/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import LangSemDoc
open Verso.Genre.Manual (RenderConfig manualMain)

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .immediately
  emitHtmlMulti := .no
  htmlDepth := 2

def main := manualMain (%doc LangSemDoc) (config := config)
