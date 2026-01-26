/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.Op

/-!
Tests for SMT Op abbreviations.

The #genOpAbbrevs macro in Strata/DL/SMT/Op.lean generates abbreviations like
Op.not for Op.core Op.Core.not. These tests verify the abbreviations exist and
have the expected types.
-/

namespace StrataTest.DL.SMT.OpTests

open Strata.SMT

-- Verify that the generated abbreviations exist and have the correct types
#check (Op.not : Op)
#check (Op.and : Op)
#check (Op.or : Op)
#check (Op.eq : Op)
#check (Op.ite : Op)
#check (Op.implies : Op)
#check (Op.distinct : Op)
#check (Op.uf : UF → Op)
#check (Op.neg : Op)
#check (Op.sub : Op)
#check (Op.add : Op)
#check (Op.mul : Op)
#check (Op.div : Op)
#check (Op.mod : Op)
#check (Op.abs : Op)
#check (Op.le : Op)
#check (Op.lt : Op)
#check (Op.ge : Op)
#check (Op.gt : Op)
#check (Op.bvneg : Op)
#check (Op.bvadd : Op)
#check (Op.bvsub : Op)
#check (Op.bvmul : Op)
#check (Op.bvnot : Op)
#check (Op.bvand : Op)
#check (Op.bvor : Op)
#check (Op.bvxor : Op)
#check (Op.bvshl : Op)
#check (Op.bvlshr : Op)
#check (Op.bvashr : Op)
#check (Op.bvslt : Op)
#check (Op.bvsle : Op)
#check (Op.bvult : Op)
#check (Op.bvsge : Op)
#check (Op.bvsgt : Op)
#check (Op.bvule : Op)
#check (Op.bvugt : Op)
#check (Op.bvuge : Op)
#check (Op.bvudiv : Op)
#check (Op.bvurem : Op)
#check (Op.bvsdiv : Op)
#check (Op.bvsrem : Op)
#check (Op.bvnego : Op)
#check (Op.bvsaddo : Op)
#check (Op.bvssubo : Op)
#check (Op.bvsmulo : Op)
#check (Op.bvconcat : Op)
#check (Op.zero_extend : Nat → Op)
#check (Op.str_length : Op)
#check (Op.str_concat : Op)
#check (Op.str_lt : Op)
#check (Op.str_le : Op)
#check (Op.str_at : Op)
#check (Op.str_substr : Op)
#check (Op.str_prefixof : Op)
#check (Op.str_suffixof : Op)
#check (Op.str_contains : Op)
#check (Op.str_indexof : Op)
#check (Op.str_replace : Op)
#check (Op.str_replace_all : Op)
#check (Op.str_to_re : Op)
#check (Op.str_in_re : Op)
#check (Op.re_none : Op)
#check (Op.re_all : Op)
#check (Op.re_allchar : Op)
#check (Op.re_concat : Op)
#check (Op.re_union : Op)
#check (Op.re_inter : Op)
#check (Op.re_star : Op)
#check (Op.str_replace_re : Op)
#check (Op.str_replace_re_all : Op)
#check (Op.re_comp : Op)
#check (Op.re_diff : Op)
#check (Op.re_plus : Op)
#check (Op.re_opt : Op)
#check (Op.re_range : Op)
#check (Op.re_loop : Nat → Nat → Op)
#check (Op.re_index : Nat → Op)

end StrataTest.DL.SMT.OpTests
