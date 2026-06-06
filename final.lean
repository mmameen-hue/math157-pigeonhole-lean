-- PigeonholePrinciple.lean
-- Math 157 Final Project — Code Component
--
-- SETUP: This file requires a standard Mathlib4 project.
-- To compile, create a project with:
--   lake new PigeonholeProject math
-- or add to an existing lakefile.lean:
--   require mathlib from git "https://github.com/leanprover-community/mathlib4"
-- Then run: lake exe cache get
-- Place this file in the project source directory and run: lake build
--
-- AI DISCLOSURE: Claude (Anthropic) assisted with initial structure and
-- debugging. All proof logic and mathematical organization are my own work,
-- developed through understanding each step independently.

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic

/-!
# Formalizing the Pigeonhole Principle in Lean

The Pigeonhole Principle is a foundational theorem in combinatorics: if n+1
objects are placed into n boxes, at least one box must contain more than one
object. In formal terms, this means there cannot exist an injective (one-to-one)
function from a set of size n+1 into a set of size n.

In this file we formalize that statement using Lean's `Fin` type to represent
finite sets. `Fin k` is the type whose elements are the natural numbers
{0, 1, ..., k-1}, so it serves as a canonical set of exactly k elements.
Injectivity is expressed with Mathlib's `Function.Injective`, which asserts
that distinct inputs always map to distinct outputs.

The proof strategy is:
  1. Assume for contradiction that an injection f : Fin (n+1) → Fin n exists.
  2. Any injection between finite types forces the domain's cardinality to be
     at most the codomain's cardinality (via `Fintype.card_le_of_injective`).
  3. The cardinality of `Fin k` is exactly k (via `Fintype.card_fin`).
  4. This yields the impossible inequality n+1 ≤ n, closed by `omega`.
-/

-- ============================================================
-- Section 1: Named helper lemmas
-- ============================================================

-- `card_fin_eq` restates the Mathlib fact that the cardinality of `Fin n`
-- is exactly n. We give it a short name to keep later proofs readable.
-- This is a thin wrapper around `Fintype.card_fin`.
lemma card_fin_eq (n : ℕ) : Fintype.card (Fin n) = n :=
  Fintype.card_fin n

-- `injective_card_le` expresses the key consequence of injectivity for
-- finite types: if f : α → β is injective and both types are finite, then
-- |α| ≤ |β|. This is exactly `Fintype.card_le_of_injective` from Mathlib.
-- Naming it here makes the dependency explicit and the main proof cleaner.
lemma injective_card_le {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Injective f) :
    Fintype.card α ≤ Fintype.card β :=
  Fintype.card_le_of_injective f hf

-- ============================================================
-- Section 2: The Pigeonhole Principle (main theorem)
-- ============================================================

-- `pigeonhole` is the main result: for every natural number n, there is no
-- injective function from Fin (n+1) to Fin n.
--
-- Proof:
--   Suppose such f exists. By `injective_card_le`, card(Fin (n+1)) ≤ card(Fin n).
--   Rewriting via `card_fin_eq` on both sides gives n+1 ≤ n.
--   The tactic `omega` closes this as a contradiction in linear arithmetic.
theorem pigeonhole (n : ℕ) :
    ¬ ∃ f : Fin (n + 1) → Fin n, Function.Injective f := by
  -- Destructure the existential hypothesis into the function and its injectivity proof.
  rintro ⟨f, hf⟩
  -- Derive that the cardinality of the domain is at most that of the codomain.
  have hcard : Fintype.card (Fin (n + 1)) ≤ Fintype.card (Fin n) :=
    injective_card_le f hf
  -- Replace both cardinalities with concrete natural numbers using card_fin_eq.
  rw [card_fin_eq, card_fin_eq] at hcard
  -- Now hcard : n + 1 ≤ n, which omega immediately refutes.
  omega

-- ============================================================
-- Section 3: Concrete instantiations as sanity checks
-- ============================================================

-- Specializing at n = 2: no injection from Fin 3 into Fin 2.
-- This is the simplest non-trivial case and confirms the general theorem
-- behaves correctly at a concrete value.
theorem pigeonhole_three_into_two :
    ¬ ∃ f : Fin 3 → Fin 2, Function.Injective f :=
  pigeonhole 2

-- Specializing at n = 3: no injection from Fin 4 into Fin 3.
-- The "four pigeons, three holes" version that is often used in textbooks
-- as the motivating example for the principle.
theorem pigeonhole_four_into_three :
    ¬ ∃ f : Fin 4 → Fin 3, Function.Injective f :=
  pigeonhole 3

-- ============================================================
-- Section 4: A self-contained alternate proof
-- ============================================================

-- `pigeonhole'` proves the same statement without using our named helpers,
-- relying only on Mathlib lemmas directly. The `simp` call handles both
-- the cardinality rewrites and the arithmetic in one step.
-- Comparing this with `pigeonhole` illustrates how named intermediate lemmas
-- improve readability even when they do not add logical content.
theorem pigeonhole' (n : ℕ) :
    ¬ ∃ f : Fin (n + 1) → Fin n, Function.Injective f := by
  rintro ⟨f, hf⟩
  have h := Fintype.card_le_of_injective f hf
  simp [Fintype.card_fin] at h

-- ============================================================
-- Section 5: A variant stated without existential quantifier
-- ============================================================

-- `pigeonhole_direct` avoids the existential entirely: given any concrete
-- function f : Fin (n+1) → Fin n, it cannot be injective.
-- This form is sometimes easier to apply when you already have a specific
-- function in hand rather than a hypothesis that one exists.
theorem pigeonhole_direct (n : ℕ) (f : Fin (n + 1) → Fin n) :
    ¬ Function.Injective f := by
  -- Use the existential version: package f into an existential and apply pigeonhole.
  intro hf
  exact pigeonhole n ⟨f, hf⟩