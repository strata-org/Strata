/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.StatementType

namespace Core

section DuplicateBlockLabelsTests

open Std (ToFormat Format format)
open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax

/-- info: error: [label_outer :
{
  label_inner :
  {
    init (x : int) := #1
  }
  label_inner :
  {
    init (y : int) := #2
  }
}]: Duplicate label 'label_inner' within block 'label_outer'. All labels within a single block must be distinct. -/
#guard_msgs in
#eval do
  let stmts : List Statement := [
    .block "label_outer" [
      .block "label_inner" [
        Statement.init "x" t[int] (some eb[#1]) .empty
      ] .empty,
      .block "label_inner" [  -- Duplicate label at same level
        Statement.init "y" t[int] (some eb[#2]) .empty
      ] .empty
    ] .empty
  ]
  let ans ← typeCheck LContext.default TEnv.default Program.init none stmts
  return format ans

/--
info: ok: {
  label_outer :
  {
    label_inner1 :
    {
      init (x : int) := #1
    }
    label_inner2 :
    {
      init (y : int) := #2
    }
  }
}
-/
#guard_msgs in
#eval do
  let stmts : List Statement := [
    .block "label_outer" [
      .block "label_inner1" [
        Statement.init "x" t[int] (some eb[#1]) .empty
      ] .empty,
      .block "label_inner2" [  -- Different label, should be OK
        Statement.init "y" t[int] (some eb[#2]) .empty
      ] .empty
    ] .empty
  ]
  let ans ← typeCheck LContext.default TEnv.default Program.init none stmts
  return format ans.fst

/--
info: ok: {
  label_outer :
  {
    label_inner :
    {
      label_inner :
      {
        init (x : int) := #1
      }
    }
  }
}
-/
#guard_msgs in
#eval do
  let stmts : List Statement := [
    .block "label_outer" [
      .block "label_inner" [
        .block "label_inner" [  -- Same label but nested, should be OK
          Statement.init "x" t[int] (some eb[#1]) .empty
        ] .empty
      ] .empty
    ] .empty
  ]
  let ans ← typeCheck LContext.default TEnv.default Program.init none stmts
  return format ans.fst

/-- info: error: [label_outer :
{
  label_a :
  {
    init (x : int) := #1
  }
  label_a :
  {
    init (y : int) := #2
  }
  label_b :
  {
    init (z : int) := #3
  }
  label_b :
  {
    init (w : int) := #4
  }
}]: Duplicate label 'label_a' within block 'label_outer'. All labels within a single block must be distinct. -/
#guard_msgs in
#eval do
  let stmts : List Statement := [
    .block "label_outer" [
      .block "label_a" [
        Statement.init "x" t[int] (some eb[#1]) .empty
      ] .empty,
      .block "label_a" [  -- First duplicate
        Statement.init "y" t[int] (some eb[#2]) .empty
      ] .empty,
      .block "label_b" [
        Statement.init "z" t[int] (some eb[#3]) .empty
      ] .empty,
      .block "label_b" [  -- Second duplicate
        Statement.init "w" t[int] (some eb[#4]) .empty
      ] .empty
    ] .empty
  ]
  let ans ← typeCheck LContext.default TEnv.default Program.init none stmts
  return format ans

end DuplicateBlockLabelsTests

end Core
