# Task: check that a Lean 4 statement says exactly what a mathematical theorem says

You are reviewing a formalization. Your only job is to decide whether the **Lean statement** below
is logically equivalent to the **mathematical theorem** below. Do **not** try to prove or disprove the
theorem, and do not assess the proof: the Lean proof has been machine-checked (no `sorry`, only the
standard axioms `propext`, `Classical.choice`, `Quot.sound`). The only remaining risk is that the
formal statement does not mean what the mathematical statement means. Be skeptical and precise.

## 1. The mathematical theorem

Let `n ≥ 2` and `P = [0,p₁]×…×[0,pₙ]` with `pᵢ ≥ 0` (a closed box in Euclidean `n`-space). For
`A, B ≥ 0` the `A × B` *rectangle* is `{x₀ + s·A·u + r·B·v : s, r ∈ [0, 1]}` for some point `x₀` and some
orthonormal pair `u, v ∈ ℝⁿ`; it *fits into* `P` if `x₀, u, v` can be chosen so that it lies in `P`
(equivalently: some isometry of `ℝⁿ`, reflections allowed, maps the rectangle `[0,A]×[0,B]×{0}×…×{0}`
into `P`). For `S ⊆ {1,…,n}` let `‖p_S‖² = Σ_{i∈S} pᵢ²` and `x₊ = max(x, 0)`.

**Carver's criterion** (plane). Let `X ≥ Y ≥ 0` be the sides of a planar rectangle and `a ≥ b ≥ 0` the
sides of another. The `a × b` rectangle fits into the `X × Y` rectangle iff
(i) `a ≤ X` and `b ≤ Y`, or
(ii) `a > X`, `b ≤ Y` and `((X+Y)/(a+b))² + ((X−Y)/(a−b))² ≥ 2`.
`Carver(a, b; X, Y)` denotes this condition after sorting both pairs in decreasing order.

**Theorem.** Let `n ≥ 2`, `pᵢ ≥ 0`, `A, B ≥ 0`. The `A × B` rectangle fits into `P` if and only if there
are indices `k ≠ l` and a partition `S ⊔ T = {1,…,n} ∖ {k, l}` such that
`Carver(a′, b′; p_k, p_l)`, where `a′ = √(A² − ‖p_S‖²)₊` and `b′ = √(B² − ‖p_T‖²)₊`.

## 2. The Lean 4 statement (code verbatim, docstrings shortened; Lean 4 + Mathlib, indices are `0, …, n−1`)

```lean
namespace RectInNBox

variable {n m : ℕ}

/-- Euclidean space `ℝⁿ`. -/
abbrev En (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The closed box `∏ᵢ [0, qᵢ]` in `ℝⁿ` with edges along the coordinate axes. -/
def boxN (q : Fin n → ℝ) : Set (En n) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ q i}

/-- The vector of edges `q : Fin m → ℝ` extended by zeros to `Fin n` (`m ≤ n`). -/
noncomputable def pad (h : m ≤ n) (q : Fin m → ℝ) : Fin n → ℝ :=
  Function.extend (Fin.castLE h) q 0

/-- The box with edges `q` fits into the box with edges `p`. -/
def FitsN (p q : Fin n → ℝ) : Prop := ∃ f : En n ≃ᵢ En n, f '' boxN q ⊆ boxN p

/-- Carver's criterion for sorted sides (`X ≥ Y` — the box, `a ≥ b` — the rectangle). -/
def CarverS (a b X Y : ℝ) : Prop :=
  (a ≤ X ∧ b ≤ Y) ∨
    (X < a ∧ b ≤ Y ∧ 2 ≤ ((X + Y) / (a + b)) ^ 2 + ((X - Y) / (a - b)) ^ 2)

/-- Carver's criterion after sorting both pairs in decreasing order. -/
def Carver (a b X Y : ℝ) : Prop := CarverS (max a b) (min a b) (max X Y) (min X Y)

open Finset Real in
theorem fitsN_rect_iff_explicit (h : 2 ≤ n) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    FitsN p (pad h ![A, B]) ↔
      ∃ k l : Fin n, k ≠ l ∧ ∃ S T : Finset (Fin n), Disjoint S T ∧ S ∪ T = univ \ {k, l} ∧
        Carver (√(A ^ 2 - ∑ i ∈ S, p i ^ 2)) (√(B ^ 2 - ∑ i ∈ T, p i ^ 2)) (p k) (p l)
```

Notes on Lean/Mathlib notation, for reference:
* `EuclideanSpace ℝ (Fin n)` is `ℝⁿ` with the Euclidean distance; `x i` is the `i`-th coordinate.
* `En n ≃ᵢ En n` is the type of isometric bijections of `ℝⁿ` onto itself (`IsometryEquiv`).
* `f '' S` is the image of the set `S` under `f`; `⊆` is set inclusion.
* `![A, B] : Fin 2 → ℝ` is the vector `(A, B)`. `Fin.castLE h : Fin m → Fin n` is the inclusion
  `i ↦ i`; `Function.extend g q 0` equals `q j` at `g j` and `0` outside the range of `g`.
* `Finset (Fin n)` is a finite set of indices, `univ` is the set of all indices,
  `Disjoint S T` means `S ∩ T = ∅`, `∑ i ∈ S, f i` is a finite sum.
* `√t` is `Real.sqrt t`, defined for all reals and equal to `0` for `t < 0`.
* Division by zero is defined in Lean: `x / 0 = 0`.

## 3. What to check (answer every item)

1. Does `boxN q` coincide with `[0,q₀]×…×[0,q_{n−1}]` (closed, axis-parallel, one corner at the origin)?
2. Does `FitsN p q` coincide with "the box `q` fits into the box `p`" (any isometry, reflections
   allowed)? Is quantifying over isometric **bijections** the same as over all isometries of `ℝⁿ`?
3. Is `boxN (pad h ![A, B])` exactly the rectangle `[0,A]×[0,B]×{0}×…×{0}`, so that
   `FitsN p (pad h ![A, B])` means "the `A × B` rectangle fits into `P`"?
4. Do `CarverS` / `Carver` coincide with Carver's criterion as stated in §1, including the sorting,
   and can the convention `x / 0 = 0` change the answer in branch (ii)?
5. Does the right-hand side coincide with the condition of the theorem: the partition
   (`Disjoint S T ∧ S ∪ T = univ \ {k, l}`), the positive part (via `√t = 0` for `t < 0`), and the
   order of the arguments of `Carver`?
6. Do the hypotheses `h`, `hp`, `hA`, `hB` match `n ≥ 2`, `pᵢ ≥ 0`, `A, B ≥ 0`, with nothing added or
   missing, and without making the statement vacuous?
7. Is there any other way in which the Lean statement is weaker, stronger, or vacuous compared with
   the mathematical theorem (e.g. an implicit coercion, an off-by-one index, a definition that is
   trivially true or false)?

## 4. Required answer format

```
VERDICT: EQUIVALENT | NOT EQUIVALENT | UNSURE
1: OK | PROBLEM — <one or two sentences>
2: OK | PROBLEM — ...
3: OK | PROBLEM — ...
4: OK | PROBLEM — ...
5: OK | PROBLEM — ...
6: OK | PROBLEM — ...
7: OK | PROBLEM — ...
DETAILS: <any explanation; for every PROBLEM give a concrete input (numbers) on which the two
statements differ, or say explicitly that you could not find one>
```

Do not answer `NOT EQUIVALENT` without a concrete distinguishing example or a precise logical reason.
If you are not sure about a Lean/Mathlib detail, say so and answer `UNSURE` rather than guessing.
