#!/usr/bin/env bash
# Shared configuration for the TPC-H DuckDB-engine benchmark kit.
# Override any value via environment, e.g.  SF=1 ./04_load.sh
#
#   SF         TPC-H scale factor                         (default 10)
#   DATA_DIR   where .tbl files are generated/loaded from (default /git/tpch/sf<SF>)
#   SCHEMA     DuckDB schema populated via duckdb_query_udf (default bench)
#   TPCH_SQL   MariaDB-dialect query file (source of the 22 queries)
#   MARIADB    mariadb client command

SF="${SF:-10}"
DATA_DIR="${DATA_DIR:-/git/tpch/sf${SF}}"
SCHEMA="${SCHEMA:-bench}"
TPCH_SQL="${TPCH_SQL:-/tpch.sql}"
MARIADB="${MARIADB:-mariadb}"

TABLES=(region nation supplier customer part partsupp orders lineitem)

# Run one statement on the embedded DuckDB through MariaDB's duckdb_query_udf.
# Single quotes in $1 are escaped so SQL string/identifier literals survive.
# Prints the UDF result text (callers discard it when not needed).
duck() {
  local esc
  esc=$(printf '%s' "$1" | sed "s/'/''/g")
  "$MARIADB" -N -e "SELECT duckdb_query_udf('$esc')"
}
