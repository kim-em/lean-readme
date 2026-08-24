/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

import Lean.Data.Position

set_option linter.missingDocs true
set_option doc.verso true

public section

namespace LeanReadme

/-- Recognized info-string flags on a {lit}`lean` code fence. -/
structure Flags where
  /-- Whether the block is elaborated as a {lit}`term` rather than as commands. -/
  term : Bool := false
  /-- Whether the block is expected to produce an error. -/
  expectError : Bool := false
  /-- Whether the block is expected to produce a warning. -/
  expectWarning : Bool := false
  /-- Whether the block is left unchecked. -/
  noCheck : Bool := false
  /-- Whether displayed theorem declarations are checked against imported declarations. -/
  recall : Bool := false
deriving Repr, Inhabited

/-- A Lean code block, delimited by byte offsets into the source. -/
structure Block where
  /-- The byte offset where the block's content begins. -/
  startByte : String.Pos.Raw
  /-- The byte offset just past the block's content. -/
  stopByte : String.Pos.Raw
  /-- The flags parsed from the fence's info string. -/
  flags : Flags
  /-- The 1-based line number of the opening fence. -/
  fenceLine : Nat
deriving Repr, Inhabited

/-- Extraction failures. -/
inductive ExtractError where
  /-- A code fence opened on the given line but was never closed. -/
  | unterminated (fenceLine : Nat)
deriving Repr

/-- Count of leading backticks in a trimmed line, else 0. -/
private def backtickRun (line : String.Slice) : Nat :=
  line.takeWhile '`' |>.positions.length

/-- Parses the words after {lit}`lean` in an info string into {name}`Flags`. Unknown words are ignored. -/
private def parseFlags (words : Array String.Slice) : Flags := Id.run do
  let mut f : Flags := {}
  for w in words do
    match w.copy with
    | "term" => f := { f with term := true }
    | "error" => f := { f with expectError := true }
    | "warning" => f := { f with expectWarning := true }
    | "nocheck" => f := { f with noCheck := true }
    | "recall" => f := { f with recall := true }
    | _ => pure ()
  return f

open Lean in
private def lineWithoutTrailingNewline (fm : FileMap) (l : Nat)
    (l_valid : l < fm.positions.size - 1) : String.Slice :=
  let lineStart := fm.positions[l]
  let nextLineStart := fm.positions[l + 1]
  let endPos := if l + 1 < fm.positions.size - 1 then nextLineStart - '\n' else nextLineStart
  fm.source.slice! (fm.source.pos! lineStart) (fm.source.pos! endPos)

/--
Extracts Lean code blocks from LF-normalized Markdown as byte ranges.

A fence opens on a line whose first non-space run is three or more backticks; the remainder is the
info string. The block closes on the next line that is only a run of at least as many backticks.
Fences whose first info-string word is not {lit}`lean` are skipped, body included.
-/
def extract (source : String) : Except ExtractError (Array Block) := Id.run do
  -- Build a FileMap so line boundaries are available as direct array lookups.
  -- positions[k] is the byte start of line k+1 (1-based); the last entry is the
  -- end-of-file position. Lines are 0-indexed here; line i spans
  -- [positions[i], positions[i+1]).
  let fmap := Lean.FileMap.ofString source
  let positions := fmap.positions
  let numLines := positions.size - 1  -- number of iterable lines
  let mut blocks : Array Block := #[]

  let mut i := 0
  while h : i < numLines do
    -- Extract the content of line i, stripping the trailing '\n' when present.
    -- For i + 1 < numLines the byte at positions[i+1] - 1 is always '\n'
    -- (FileMap pushes the position right after each newline). For the final
    -- trailing segment the end position carries no newline to strip.
    let nextStart := positions[i + 1]
    let line : String.Slice := lineWithoutTrailingNewline fmap i (by grind)
    let trimmed := line.trimAsciiStart
    let ticks := backtickRun trimmed
    if ticks ≥ 3 then
      -- Opening fence: info string follows the backtick run.
      let info := trimmed.drop ticks |>.trimAscii
      let words := info.split " " |>.filter (!·.isEmpty)
      let isLean := words.first?.getD ↑"" == ↑"lean"
      let openLine := i + 1  -- 1-based line number of the opening fence
      -- Content starts at the byte that begins the line after the opening fence.
      let contentStartByte : String.Pos.Raw := nextStart
      -- Scan forward for the closing fence.
      let mut j := i + 1
      let mut closed := false
      let mut contentStopByte : String.Pos.Raw := contentStartByte
      while h : j < numLines && !closed do
        let ls := positions[j]'(by grind)
        let l : String.Slice := lineWithoutTrailingNewline fmap j (by grind)
        let t := l.trimAsciiStart
        let tt := backtickRun t
        if tt ≥ ticks && (t.trimAscii).all (· == '`') then
          -- Closing fence found: content ends at the byte start of this line.
          closed := true
          contentStopByte := ls
        else
          j := j + 1
      if !closed then
        return .error (.unterminated openLine)
      if isLean then
        blocks := blocks.push {
          startByte := contentStartByte
          stopByte := contentStopByte
          flags := parseFlags (words.toArray.drop 1)
          fenceLine := openLine
        }
      -- Resume scanning from the line after the closing fence.
      i := j + 1
    else
      i := i + 1
  return .ok blocks
