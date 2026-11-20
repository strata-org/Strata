/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Cli.VerifyOptions

/-! # The cvc5 flags of `verify`

`--cvc5-full-saturate-quant`, `--cvc5-retry-full-saturate-quant` and `--cvc5-retry-timeout`, parsed
by `parseVerifyOptions`, set their `VerifyOptions` fields; a non-numeric retry timeout is refused
(`parseCvc5RetryTimeout`). -/

meta section

open Strata.Cli

/-- The options these flags parse to, from the default options. -/
private def optionsOf (flags : List (String × Option String)) : IO Core.VerifyOptions :=
  parseVerifyOptions (flags.foldl (fun acc (k, v) => ParsedFlags.insert acc k v) {})

/-- info: false false 0 -/
#guard_msgs in
#eval do
  let o ← optionsOf []
  IO.println s!"{o.cvc5FullSaturateQuant} {o.cvc5RetryFullSaturateQuant} {o.cvc5RetryTimeout}"

/-- info: true false 0 -/
#guard_msgs in
#eval do
  let o ← optionsOf [("cvc5-full-saturate-quant", none)]
  IO.println s!"{o.cvc5FullSaturateQuant} {o.cvc5RetryFullSaturateQuant} {o.cvc5RetryTimeout}"

/-- info: false true 3 -/
#guard_msgs in
#eval do
  let o ← optionsOf [("cvc5-retry-full-saturate-quant", none), ("cvc5-retry-timeout", some "3")]
  IO.println s!"{o.cvc5FullSaturateQuant} {o.cvc5RetryFullSaturateQuant} {o.cvc5RetryTimeout}"

-- The retry timeout: absent keeps the base, a number is taken, anything else is refused.
#guard (parseCvc5RetryTimeout none 7).toOption == some 7
#guard (parseCvc5RetryTimeout (some "3") 0).toOption == some 3
#guard (match parseCvc5RetryTimeout (some "x") 0 with
  | .error msg => msg == "Invalid cvc5 retry timeout: 'x'"
  | .ok _ => false)

end
