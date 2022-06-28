fn main() {}

#[cfg(test)]
mod tests {
    use chrono::{DateTime, Utc};
    use insta::{assert_snapshot, glob};
    use postgres::{
        types::{FromSql, Type},
        Row,
    };
    use rusqlite::{types::ValueRef, Connection};
    use std::{fs, path::Path, time::SystemTime};

    #[test]
    fn test() {
        // for each of the queries
        glob!("queries/**/*.prql", |path| {
            // read
            let prql = fs::read_to_string(path).unwrap();

            if prql.contains("skip_test") {
                return;
            }

            // compile
            let sql = prql_compiler::compile(&prql).unwrap();

            // save both csv files as same snapshot
            assert_snapshot!("", sqlite(&sql));
            assert_snapshot!("", postgres(&sql));
        });
    }

    fn sqlite(sql: &str) -> String {
        let path = Path::new("./chinook.db");
        let conn = Connection::open(path).unwrap();

        let mut statement = conn.prepare(sql).unwrap();

        let csv_header = statement.column_names().join("\t");
        let column_count = statement.column_count();

        let csv_rows = statement
            .query_map([], |row| {
                Ok((0..column_count)
                    .map(|i| match row.get_ref_unwrap(i) {
                        ValueRef::Null => "".to_string(),
                        ValueRef::Integer(i) => i.to_string(),
                        ValueRef::Real(r) => r.to_string(),
                        ValueRef::Text(t) => String::from_utf8_lossy(t).to_string(),
                        ValueRef::Blob(_) => unimplemented!(),
                    })
                    .collect::<Vec<_>>()
                    .join("\t"))
            })
            .unwrap()
            .into_iter()
            .take(100) // truncate to 100 rows
            .map(|r| r.unwrap())
            .collect::<Vec<String>>()
            .join("\n");

        csv_header + "\n" + &csv_rows
    }

    fn postgres(sql: &str) -> String {
        use postgres::{Client, NoTls};

        let host = "localhost"; // change this to 'postgres' to run in docker compose
        let mut client = Client::connect(&format!("host={} user=postgres", host), NoTls).unwrap();

        let statement = client.prepare(sql).unwrap();

        let csv_header = statement
            .columns()
            .iter()
            .map(|c| c.name())
            .take(100) // truncate to 100 rows
            .collect::<Vec<_>>()
            .join("\t");

        let rows = client.query(&statement, &[]).unwrap();

        fn get<'a, T: ToString + FromSql<'a>>(row: &'a Row, idx: usize) -> String {
            row.get::<usize, Option<T>>(idx)
                .map(|v| v.to_string())
                .unwrap_or_default()
        }

        let mut csv_rows = vec![csv_header];
        for row in rows.into_iter().take(100) {
            csv_rows.push(
                (0..row.len())
                    .map(|i| match row.columns()[i].type_() {
                        &Type::BOOL => get::<bool>(&row, i),
                        &Type::INT2 => get::<i16>(&row, i),
                        &Type::INT4 => get::<i32>(&row, i),
                        &Type::INT8 => get::<i64>(&row, i),
                        &Type::TEXT | &Type::VARCHAR => get::<String>(&row, i),
                        &Type::JSON | &Type::JSONB => get::<String>(&row, i),
                        &Type::FLOAT4 => get::<f32>(&row, i),
                        &Type::FLOAT8 => get::<f32>(&row, i),
                        &Type::TIMESTAMPTZ | &Type::TIMESTAMP => get::<Timestamp>(&row, i),
                        t => unimplemented!("postgres type {t}"),
                    })
                    .collect::<Vec<_>>()
                    .join("\t"),
            );
        }

        csv_rows.join("\n")
    }

    struct Timestamp(SystemTime);
    impl<'a> FromSql<'a> for Timestamp {
        fn from_sql(
            ty: &Type,
            raw: &'a [u8],
        ) -> Result<Self, Box<dyn std::error::Error + Sync + Send>> {
            SystemTime::from_sql(ty, raw).map(Timestamp)
        }

        fn accepts(ty: &Type) -> bool {
            SystemTime::accepts(ty)
        }
    }
    impl ToString for Timestamp {
        fn to_string(&self) -> String {
            let dt = DateTime::<Utc>::from(self.0);
            dt.format("%Y-%m-%d %H:%M:%S").to_string()
        }
    }
}
