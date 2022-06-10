use std::collections::HashMap;

use anyhow::{Context as AnyhowContext, Result};
use itertools::Itertools;

use crate::ast::ast_fold::*;
use crate::error::{Error, Reason};
use crate::{ast::*, Context, Declaration};

/// Runs type analysis on a query, using context.
///
/// Will determine type for each function call, variable or literal.
/// Will throw error on incorrect function argument type.
pub fn resolve_types(nodes: Vec<Node>, context: Context) -> Result<(Vec<Node>, Context)> {
    let mut resolver = TypeResolver::new(context);

    resolver.validate_function_defs()?;

    let nodes = resolver.fold_nodes(nodes)?;

    Ok((nodes, resolver.context))
}

pub struct TypeResolver {
    pub context: Context,
}

impl TypeResolver {
    fn new(context: Context) -> Self {
        TypeResolver { context }
    }

    fn validate_function_defs(&mut self) -> Result<()> {
        let function_defs: Vec<_> = (self.context.declarations.0.iter())
            .enumerate()
            .filter(|(_, (decl, _))| matches!(decl, Declaration::Function(_)))
            .map(|(id, _)| id)
            .collect();

        for id in function_defs {
            let mut func_def = self.context.declarations.take(id).into_function().unwrap();

            func_def.body = Box::new(self.fold_node(*func_def.body)?);

            let expected = func_def.return_ty.unwrap_or(Ty::Infer);

            let assumed = validate_type(&func_def.body, &expected, || Some(func_def.name.clone()))?;

            func_def.return_ty = Some(assumed);

            let decl = Declaration::Function(func_def);
            self.context.declarations.replace(id, decl);
        }

        Ok(())
    }
}

impl AstFold for TypeResolver {
    fn fold_node(&mut self, mut node: Node) -> Result<Node> {
        if node.ty.is_some() {
            return Ok(node);
        }

        let ty = match node.item {
            Item::Literal(ref literal) => match literal {
                Literal::Null => Ty::Infer,
                Literal::Integer(_) => TyLit::Integer.into(),
                Literal::Float(_) => TyLit::Float.into(),
                Literal::Boolean(_) => TyLit::Boolean.into(),
                Literal::String(_) => TyLit::String.into(),
                Literal::Date(_) => TyLit::Date.into(),
                Literal::Time(_) => TyLit::Time.into(),
                Literal::Timestamp(_) => TyLit::Timestamp.into(),
            },

            Item::Assign(_) | Item::NamedArg(_) => {
                // assume type of inner expr

                node.item = self.fold_item(node.item)?;

                if let Item::Assign(ne) | Item::NamedArg(ne) = &node.item {
                    ne.expr.ty.clone().unwrap()
                } else {
                    unreachable!()
                }
            }

            Item::Ident(_) => {
                // assume type of referenced declaration

                let id = node.declared_at.unwrap();
                match self.context.declarations.get(id) {
                    Declaration::Expression(_) => {
                        let expr = self
                            .context
                            .declarations
                            .take(id)
                            .into_expression()
                            .unwrap();
                        let (expr, ty) = self.resolve_type(*expr)?;

                        self.context.declarations.replace_expr(id, expr);
                        ty
                    }
                    Declaration::ExternRef { .. } => Ty::Literal(TyLit::Column),
                    Declaration::Function(func_def) => {
                        let expected = type_of_func_def(func_def);

                        let func_call = FuncCall::default();

                        validate_func_call(&func_call, &expected)?
                    }
                    Declaration::Table(_) => Ty::Literal(TyLit::Table),
                }
            }
            Item::FuncCall(mut func_call) => {
                // resolve types for each of the args
                func_call.args = self.fold_nodes(func_call.args)?;
                func_call.named_args = func_call
                    .named_args
                    .into_iter()
                    .map(|(name, node)| self.fold_node(*node).map(|n| (name, Box::new(n))))
                    .try_collect()?;

                let id = node.declared_at.unwrap();
                let func_def = (self.context.declarations.get(id).as_function())
                    .context("expected function definition?")?;
                let expected_ty = type_of_func_def(func_def);

                let res_ty = validate_func_call(&func_call, &expected_ty)?;

                node.item = Item::FuncCall(func_call);
                res_ty
            }

            Item::Pipeline(_) => {
                node.item = self.fold_item(node.item)?;

                

                Ty::Infer
            }

            Item::SString(_) => Ty::Infer, // TODO
            Item::FString(_) => TyLit::String.into(),
            Item::Interval(_) => Ty::Infer, // TODO
            Item::Range(_) => Ty::Infer,

            _ => {
                // pass trough
                node.item = self.fold_item(node.item)?;
                Ty::Infer
            }
        };

        node.ty = Some(ty);
        Ok(node)
    }
}

impl TypeResolver {
    /// Utility function for folding a node and cloning its resulting type
    fn resolve_type(&mut self, node: Node) -> Result<(Node, Ty)> {
        let node = self.fold_node(node)?;
        let ty = node.ty.clone().unwrap();
        Ok((node, ty))
    }
}

fn validate_func_call(call: &FuncCall, expected: &TyFunc) -> Result<Ty, Error> {
    // validate named args

    for (name, found) in &call.named_args {
        if let Some(expected) = expected.named.get(name) {
            validate_type(found, expected, || Some(format!("argument `{name}`")))?;
        } else {
            return Err(Error::new(Reason::Unexpected {
                found: format!("argument named `{name}`"),
            })
            .with_span(found.span));
        }
    }

    // validate positional args
    let expected_len = expected.args.len();
    let passed_len = call.args.len();

    for index in 0..usize::min(expected_len, passed_len) {
        validate_type(&call.args[index], &expected.args[index], || None)?;
    }

    if passed_len < expected_len {
        // not enough args: yield a curry

        return Ok(Ty::Function(TyFunc {
            args: expected.args[passed_len..].to_vec(),
            named: HashMap::new(),
            return_ty: expected.return_ty.clone(),
        }))
    } 
    
    if passed_len > expected_len {
        // too many args: try evaluating the return value
        let next_call = FuncCall {
            args: call.args[expected_len..].to_vec(),
            ..Default::default()
        };

        return if let Ty::Function(next_func) = expected.return_ty.as_ref() {
            validate_func_call(&next_call, next_func)
        } else {
            Err(too_many_arguments(call, expected_len, passed_len))
        }
    }

    // exactly arg match
    Ok(*expected.return_ty.clone())    
}

fn too_many_arguments(call: &FuncCall, expected_len: usize, passed_len: usize) -> Error {
    let err = Error::new(Reason::Expected {
        who: Some(call.name.clone()),
        expected: format!("{} arguments", expected_len),
        found: format!("{}", passed_len),
    });
    if passed_len >= 2 {
        err.with_help(format!(
            "If you are calling a function, you may want to add parentheses `{} [{:?} {:?}]`",
            call.name, call.args[0], call.args[1]
        ))
    } else {
        err
    }
}

/// Validates that found node has expected type. Returns assumed type of the node.
fn validate_type<F>(found: &Node, expected: &Ty, who: F) -> Result<Ty, Error>
where
    F: FnOnce() -> Option<String>,
{
    let found_ty = found.ty.clone().unwrap();

    let infer = matches!(found_ty, Ty::Infer) || matches!(expected, Ty::Infer);

    if !(found_ty <= *expected) && !infer {
        return Err(Error::new(Reason::Expected {
            who: who(),
            expected: format!("type `{}`", expected),
            found: format!("type `{}`", found_ty),
        })
        .with_span(found.span));
    }

    Ok(if let Ty::Infer = expected {
        found_ty
    } else {
        expected.clone()
    })
}

fn type_of_func_def(def: &FuncDef) -> TyFunc {
    TyFunc {
        args: def
            .positional_params
            .iter()
            .map(|a| a.1.clone().unwrap_or(Ty::Infer))
            .collect(),
        named: def
            .named_params
            .iter()
            .map(|a| {
                (
                    a.0.item.as_named_arg().unwrap().name.clone(),
                    a.1.clone().unwrap_or(Ty::Infer),
                )
            })
            .collect(),
        return_ty: Box::new(def.return_ty.clone().unwrap_or(Ty::Infer)),
    }
}
