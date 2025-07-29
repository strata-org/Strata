/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

-- This module serves as the root of the `Strata` library.

/- DDM -/
import Strata.DDM.Integration.Lean
import Strata.DDM.Ion
import Strata.DDM.Example

/- Dialect Library -/
import Strata.DL.SMT.SMT
import Strata.DL.Lambda.Lambda
import Strata.DL.Imperative.Imperative

/- Boogie -/
import Strata.Languages.Boogie.Examples.Examples
import Strata.Languages.Boogie.StatementSemantics

/- CSimp -/
import Strata.Languages.C_Simp.Examples.Examples

/- Code Transforms -/
import Strata.Transform.Examples
