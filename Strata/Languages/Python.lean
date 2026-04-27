/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

-- Aggregator: re-exports Python language submodules
public import Strata.Languages.Python.CorePrelude -- shake: keep
public import Strata.Languages.Python.FunctionSignatures -- shake: keep
public import Strata.Languages.Python.PythonToCore -- shake: keep
public import Strata.Languages.Python.PythonDialect -- shake: keep
public import Strata.Languages.Python.PythonToLaurel -- shake: keep
public import Strata.Languages.Python.PyFactory -- shake: keep
