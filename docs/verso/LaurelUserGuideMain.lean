/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import LaurelUserGuide
open Verso.Genre.Manual (RenderConfig manualMain)

def config : RenderConfig where
  emitTeX := false
  -- Multi-page output so the sidebar navigation is nested: each top-level
  -- section becomes its own page and its subsections show in the sidebar.
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2

def main := manualMain (%doc LaurelUserGuide) (config := config)
