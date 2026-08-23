/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

-- Both imports are required: `import` lets ordinary definitions reference `extract`; `meta import` provides the compiled symbols the interpreter needs for `#eval`.
import LeanReadme.Extract
meta import LeanReadme.Extract

set_option linter.missingDocs true
set_option doc.verso true

open LeanReadme

/-- Renders a block as {lit}`start..stop flags` for compact assertions. -/
def blockSummary (s : String) (b : Block) : String :=
  let content := ({ str := s, startPos := b.startByte, stopPos := b.stopByte : Substring.Raw }).toString
  let f := b.flags
  let tags := [("term", f.term), ("error", f.expectError),
               ("warning", f.expectWarning), ("nocheck", f.noCheck), ("recall", f.recall)]
              |>.filterMap (fun (n, on) => if on then some n else none)
  s!"L{b.fenceLine} [{String.intercalate "," tags}] {repr content}"

def report (s : String) : IO Unit :=
  match extract s with
  | .error (.unterminated ln) => IO.println s!"unterminated fence at line {ln}"
  | .ok bs => for b in bs do IO.println (blockSummary s b)

-- A single plain lean block yields its inner text.
/-- info: L1 [] "def x := 1\n" -/
#guard_msgs in
#eval report "```lean\ndef x := 1\n```\n"

-- Info string flags are parsed; `lean` must be first.
/-- info: L1 [term,error] "1 + true\n" -/
#guard_msgs in
#eval report "```lean term error\n1 + true\n```\n"

-- Recall blocks are recognized separately from ordinary command blocks.
/-- info: L1 [recall] "theorem Nat.add_comm (n m : Nat) : n + m = m + n\n" -/
#guard_msgs in
#eval report "```lean recall\ntheorem Nat.add_comm (n m : Nat) : n + m = m + n\n```\n"

-- Non-lean fences are skipped, including their bodies.
/-- info: L4 [] "def y := 2\n" -/
#guard_msgs in
#eval report "```python\nprint(1)\n```\n```lean\ndef y := 2\n```\n"

-- An empty lean block has start == stop.
/-- info: L1 [] "" -/
#guard_msgs in
#eval report "```lean\n```\n"

-- A longer closing fence than opening still closes (>= count).
/-- info: L1 [] "x\n" -/
#guard_msgs in
#eval report "```lean\nx\n`````\n"

-- An unterminated fence is an error naming the opening line.
/-- info: unterminated fence at line 2 -/
#guard_msgs in
#eval report "intro\n```lean\nx\n"
