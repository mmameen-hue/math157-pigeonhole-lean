# Math 157 Final Project — Formalizing the Pigeonhole Principle in Lean

---

## Overview

This project formalizes the Pigeonhole Principle in Lean 4 using Mathlib. The main
theorem states that for every natural number `n`, there is no injective function
from a finite set of size `n+1` into a finite set of size `n`. Finite sets are
represented using Lean's built-in `Fin` type, and injectivity is expressed with
Mathlib's `Function.Injective`.

---

## How to Compile

This file requires a standard Mathlib4 project.

**Option 1 — New project:**
```bash
lake new PigeonholeProject math
cd PigeonholeProject
lake exe cache get
# copy PigeonholePrinciple.lean into PigeonholeProject/
lake build
```

**Option 2 — Existing project:**  
Add the following to `lakefile.lean`:
```
require mathlib from git "https://github.com/leanprover-community/mathlib4"
```
Then run `lake exe cache get` and `lake build`.

The file compiles with no `sorry`s and no errors. Lean 4 / Mathlib version:
`v4.x` (latest stable; tested on Lean 4.31.0-rc1 via live.lean-lang.org).

---

## Scope Changes

My original proposal planned to also prove several supporting results from scratch
(e.g., facts about finite cardinalities). After exploring Mathlib more carefully,
I found that these intermediate results are already available as library theorems
(`Fintype.card_le_of_injective`, `Fintype.card_fin`). Rather than re-deriving
them, I chose to focus on understanding the formal proof structure and organizing
the file clearly, which aligns better with the learning goals stated in my proposal.
This change was discussed in the Week 8 progress report.

---

## AI Disclosure

Claude (Anthropic) assisted with initial file structure and helped diagnose a
Lean error in an earlier draft (the `succ_not_le_self` application was replaced
by `omega` after debugging). All mathematical reasoning, proof organization, and
final code are my own work developed through working through each step in the
Lean infoview.

---

## Key Mathlib Dependencies

| Mathlib lemma | Role in this project |
|---|---|
| `Fintype.card_fin` | `card(Fin n) = n` |
| `Fintype.card_le_of_injective` | injection implies cardinality inequality |
| `omega` | closes linear arithmetic goals like `n+1 ≤ n → False` |
