# lean-readme

This is a tool for checking code samples in README.md files for
projects written in Lean. It does so by elaborating Lean code blocks
in the file, from top to bottom. An optional prefix file can be used
to add imports and declarations prior to the check.

`lean-readme` is an experimental internal project, made public for
experimentation. It is not an official Lean FRO product and the code
remains experimental.

## Installation

Add `lean-readme` as a Lake dependency in `lakefile.toml`:

```toml
[[require]]
name = "lean-readme"
git = "https://github.com/leanprover/lean-readme"
rev = "main"
```

## Usage

```
lake exe lean-readme [--prefix PATH] [FILE...]
```

With no arguments, `lean-readme` searches the working directory for a
README file (`README.md`, `README.markdown`, or `README`,
case-insensitive). File arguments are checked in order, in independent
states.

`--prefix PATH` sets the prefix file (default: `.lean-readme/Prefix.lean`).

The exit code is:
 * `0` when all blocks pass
 * `1` when any block fails
 * `2` for a usage error.

## Fence conventions

A Lean code block opens on a line whose first non-space characters are
three or more backticks followed by an info string beginning with
`lean`. Optional flags follow `lean` in the info string:

| Flag | Meaning |
|---|---|
| `term` | Check the block as a single term rather than a sequence of commands |
| `error` | Expect at least one error |
| `warning` | Expect at least one warning |
| `nocheck` | Skip the block |
| `recall [name]` | Check displayed `theorem` declarations against imported declarations |

Blocks without any flag are checked as commands. Unrecognized flags
are ignored. Unexpected errors or warnings cause the check to fail, as
does the absence of expected errors or warnings.

Imports at the start of checked command blocks are collected before checking and
loaded together as the README's module header. Checking resumes after each
block's imports, so commands later in the same block are not skipped.

In a `lean recall` block, each top-level `theorem` declaration is checked
against the imported declaration resolved by its name. A fully qualified target
after `recall` selects the declaration without changing the displayed theorem:

````markdown
```lean recall Nat.add_comm
theorem add_comm (n m : Nat) : n + m = m + n
```
````

The displayed and imported types must be definitionally equal. When a target is
given, the displayed signature is elaborated in the target's namespace.

## Prefix file

`.lean-readme/Prefix.lean` is an ordinary Lean source file. Every
definition and import in it is in scope for all code blocks in the
file. For example, this prefix imports `Mathlib`:

```lean nocheck
module

import Mathlib
```

## Example

This code block is checked:

```lean
def greeting : String := "hello"
```
