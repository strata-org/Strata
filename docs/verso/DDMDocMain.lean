/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import DDMDoc
open Verso.Genre.Manual (Config manualMain)

def config : Config where
  emitTeX := false
  emitHtmlSingle := true
  emitHtmlMulti := false
  htmlDepth := 2

def main := manualMain (%doc DDMDoc) (config := config)
