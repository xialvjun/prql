
Database chinook.db was downloaded from https://www.sqlitetutorial.net/sqlite-sample-database/

I've renamed column names to snake_case, so Postgres does not struggle with them.

Could be compressed:

 rw-r--r-- 1 aljaz aljaz 864K nov 29  2015 chinook.db
-rw-r--r-- 1 aljaz aljaz 326K nov 29  2015 chinook.db.gz
-rw-r--r-- 1 aljaz aljaz 1,1M jun 23 15:56 chinook.sql
-rw-r--r-- 1 aljaz aljaz 296K jun 23 16:15 chinook.zip

## SQLite

    docker build . -f sqlite.dockerfile -t prql-test-sqlite

    docker run -it --rm prql-test-sqlite 