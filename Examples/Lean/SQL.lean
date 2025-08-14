/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Very rough dialect with some SQL commands for example purposes.
import Strata

#dialect
dialect SQL;

op create (name : Ident, c : CommaSepBy Ident) : Command =>
  "CREATE " name "(" c ")" ";\n";

category Columns;
op colStar : Columns => "*";
op colList (c : CommaSepBy Ident) : Columns => c;
op select (col : Columns, table : Ident) : Command =>
  "SELECT " col " FROM " table ";\n";
#end

def example1 := #strata
program SQL;
CREATE NewTable (Key, Value);
SELECT Name, Address FROM Customers;
#end

#eval example1

#eval IO.println example1

#eval IO.println example1.ppDialect!

#eval example1.toIon

namespace SQL
set_option trace.Strata.generator true

#strata_gen SQL

#check Columns.colStar

end SQL
