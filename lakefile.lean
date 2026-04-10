/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Lake
open Lake DSL
open System (FilePath)

package «Strata» where
  version := v!"0.1.0"
require plausible from git
  "https://github.com/leanprover-community/plausible.git" @ "bump_to_v4.27.0"

/-- Compile the C FFI code (ffi/statistics.c) into a static library. -/
extern_lib «strata_ffi» pkg := do
  let srcJob ← inputTextFile (pkg.dir / "ffi" / "statistics.c")
  let includeDir ← getLeanIncludeDir
  let oJob ← buildO (pkg.irDir / "ffi" / "statistics.o") srcJob
    (weakArgs := #["-I", includeDir.toString])
  let name := nameToStaticLib "strata_ffi"
  buildStaticLib (pkg.staticLibDir / name) #[oJob]

@[default_target]
lean_lib «Strata»

@[default_target]
lean_exe «strata» where
  root := `StrataMain

lean_lib «StrataExamples» where
  globs := #[.submodules `Examples.Lean]

lean_lib «StrataTest» where
  globs := #[.submodules `StrataTest]

@[default_target]
lean_exe «StrataToCBMC»

@[default_target]
lean_exe «StrataCoreToGoto»

lean_exe «DiffTestCore»

lean_exe «TestProfile»
