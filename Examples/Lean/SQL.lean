/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
-- Dialect with some SQL commands for example purposes.
import Strata

#dialect
dialect SQL;

op create (name : Ident, c : CommaSepBy Ident) : Command =>
  "CREATE " name "(" c ")" ";\n";

op drop (name : Ident) : Command =>
  "DROP " name ";\n";

category Columns;
op colStar : Columns => "*";
op colList (c : CommaSepBy Ident) : Columns => c;

op select (col : Columns, table : Ident) : Command =>
  "SELECT " col " FROM " table ";\n";
#end

#print SQL

def example1 := #strata
program SQL;
CREATE NewTable (Key, Value);
SELECT Name, Address FROM Customers;
SELECT * FROM Addresses;
#end

#print example1

#eval IO.println example1

#eval IO.println example1.ppDialect!

set_option trace.Strata.generator true

#strata_gen SQL

#print Command
#print Columns
#check Columns.colStar

#eval example1.toIon
