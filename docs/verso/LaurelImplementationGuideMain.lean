/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import LaurelImplementationGuide
open Verso.Genre.Manual (RenderConfig manualMain)

def config : RenderConfig where
  emitTeX := false
  -- Multi-page output so the sidebar navigation is nested.
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2

def main := manualMain (%doc LaurelImplementationGuide) (config := config)
