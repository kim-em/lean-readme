/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

import LeanReadme.Check
import LeanReadme.Extract
import LeanReadme.Report
meta import LeanReadme.Check

set_option linter.missingDocs true
set_option doc.verso true

open LeanReadme

-- The bare environment has `Nat` available.
/-- info: ok -/
#guard_msgs in
#eval show IO Unit from do
  unsafe Lean.enableInitializersExecution
  let st ← initialState ("does-not-exist" : System.FilePath)
  if st.env.contains `Nat then IO.println "ok" else IO.println "missing Nat"

/-- Runs the README text through extraction + checking, printing pass/fail and diagnostics. -/
def checkSource (src : String) : IO Unit := do
  let src := src.crlfToLf
  let st ← initialState ("does-not-exist" : System.FilePath)
  let inputCtx := Lean.Parser.mkInputContext src "README.md" (normalizeLineEndings := false)
  match extract src with
  | .error _ => IO.println "extract error"
  | .ok blocks =>
    let mut st := st
    let mut anyFail := false
    for blk in blocks do
      let (st', outcome) ← checkBlock inputCtx blk st
      st := st'
      if outcome.failed then anyFail := true
      for d in outcome.messages do IO.print d.rendered
    IO.println (if anyFail then "FAIL" else "OK")

-- A recall block checks a displayed theorem against an imported declaration.
/-- info: OK -/
#guard_msgs in
#eval show IO Unit from do
  unsafe Lean.enableInitializersExecution
  checkSource "```lean recall\ntheorem Nat.add_comm (n m : Nat) : n + m = m + n\n```\n"

-- A recall block rejects a displayed theorem whose type has drifted.
/-- info: README.md:2:0: error: type mismatch for recalled declaration 'Nat.add_comm'
  ∀ (n m : Nat), n + m = n + m
is not definitionally equal to
  ∀ (n m : Nat), n + m = m + n
FAIL -/
#guard_msgs in
#eval show IO Unit from do
  unsafe Lean.enableInitializersExecution
  checkSource "```lean recall\ntheorem Nat.add_comm (n m : Nat) : n + m = n + m\n```\n"

-- A recall block does not accept a declaration introduced by the README itself.
/-- info: README.md:5:0: error: recalled declaration 'localTheorem' is not imported
FAIL -/
#guard_msgs in
#eval show IO Unit from do
  unsafe Lean.enableInitializersExecution
  checkSource "```lean\ntheorem localTheorem : True := trivial\n```\n\
```lean recall\ntheorem localTheorem : True\n```\n"

-- A clean block passes.
/-- info: OK -/
#guard_msgs in
#eval show IO Unit from do
  unsafe Lean.enableInitializersExecution
  checkSource "```lean\ndef a := 1\n```\n"

-- An unexpected error fails and is reported at the README position.
/-- info: README.md:2:15: error: Type mismatch
  true
has type
  Bool
but is expected to have type
  Nat
FAIL -/
#guard_msgs in
#eval show IO Unit from do
  unsafe Lean.enableInitializersExecution
  checkSource "```lean\ndef b : Nat := true\n```\n"

-- A block marked `error` that errors passes, silently.
/-- info: OK -/
#guard_msgs in
#eval show IO Unit from do
  unsafe Lean.enableInitializersExecution
  checkSource "```lean error\ndef c : Nat := true\n```\n"

-- A block marked `error` that does NOT error fails.
/-- info: README.md:1:0: error: expected an error, but the block elaborated cleanly
FAIL -/
#guard_msgs in
#eval show IO Unit from do
  unsafe Lean.enableInitializersExecution
  checkSource "```lean error\ndef d := 1\n```\n"

-- nocheck is skipped entirely.
/-- info: OK -/
#guard_msgs in
#eval show IO Unit from do
  unsafe Lean.enableInitializersExecution
  checkSource "```lean nocheck\nthis is not lean\n```\n"

-- A term block elaborates a bare expression.
/-- info: OK -/
#guard_msgs in
#eval show IO Unit from do
  unsafe Lean.enableInitializersExecution
  checkSource "```lean term\n(1 : Nat) + 1\n```\n"

-- A block marked `warning` that warns passes, silently.
/-- info: OK -/
#guard_msgs in
#eval show IO Unit from do
  unsafe Lean.enableInitializersExecution
  checkSource "```lean warning\nset_option linter.unusedVariables true in\ndef e (x : Nat) := 0\n```\n"

-- An unmarked block that warns fails and prints the warning diagnostic.
/-- info: README.md:3:7: warning: Variable name `x` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
FAIL -/
#guard_msgs in
#eval show IO Unit from do
  unsafe Lean.enableInitializersExecution
  checkSource "```lean\nset_option linter.unusedVariables true in\ndef f (x : Nat) := 0\n```\n"

-- A block marked `warning` that does NOT warn fails.
/-- info: README.md:1:0: error: expected a warning, but the block elaborated cleanly
FAIL -/
#guard_msgs in
#eval show IO Unit from do
  unsafe Lean.enableInitializersExecution
  checkSource "```lean warning\ndef g := 1\n```\n"

-- A term block whose contents fail to elaborate fails, reported at the real README position.
/-- info: README.md:2:0: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  HAdd Nat Bool ?m.5

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
FAIL -/
#guard_msgs in
#eval show IO Unit from do
  unsafe Lean.enableInitializersExecution
  checkSource "```lean term\n(1 : Nat) + true\n```\n"

-- A multi-line, indented term block reports the error at the real README line and column.
/-- info: README.md:5:4: error: Application type mismatch: The argument
  true
has type
  Bool
but is expected to have type
  Nat
in the application
  if true = true then 0 else true
FAIL -/
#guard_msgs in
#eval show IO Unit from do
  unsafe Lean.enableInitializersExecution
  checkSource "```lean term\nif true then\n    (0 : Nat)\n  else\n    true\n```\n"
