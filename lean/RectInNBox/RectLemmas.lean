import RectInNBox.RectSuff
import RectInNBox.RectV

/-!
# Lemmas R and V (Section 5) for the relaxed problem

We work with a solution `(x, y)` of the relaxed problem (`RectW`): `‖x‖² ≥ A²`, `‖y‖² ≥ B²`,
`⟨x, y⟩ = 0`, `|xᵢ| + |yᵢ| ≤ pᵢ`. Relation to the notation of the paper (Section 4.3): the axis `i` with its
"local" width `rᵢ = |xᵢ| + |yᵢ|` (that is, `p′ᵢ` of Section 4.3) is active; `tᵢ = (|xᵢ| − |yᵢ|)/rᵢ`,
`Pᵢ = rᵢ²`, the side of an axis is the sign of `xᵢ yᵢ`, an axis is mixed if `xᵢ yᵢ ≠ 0`,
`D = 2 ∑ |xᵢ yᵢ|`. Hence no passage to the box `p′` with active axes is needed: all steps preserve `rᵢ`, and
so `|xᵢ| + |yᵢ| ≤ pᵢ` as well.

* `lemmaR_noMixed` — Lemma R: under the sign condition the axes can be "rounded" (no mixed axes);
  `condII_of_signs`, `condII_of_signs'` — (II) (via Lemma C) for both sign variants.
* `lemmaV` — Lemma V: if `i ≠ j` are mixed axes of side `+`, `k` of side `−`, and not
  `tᵢ = tⱼ ∧ tᵢ t_k ≤ 0`, then there is a solution with a smaller `∑ |xᵢ yᵢ|`.
-/

namespace RectInNBox

open Finset

variable {n : ℕ}

/-! ## Lemma R -/

/-- **Lemma R** (Section 5). If the axes of side `+` (`xᵢyᵢ > 0`) have `|yᵢ| ≤ |xᵢ|` (that is, `t ≥ 0`) and
the axes of side `−` have `|xᵢ| ≤ |yᵢ|` (`t ≤ 0`), then the rounding `x′ = p·[yᵢ = 0 ∨ xᵢyᵢ > 0]`,
`y′ = p − x′` is a solution without mixed axes. -/
theorem lemmaR_noMixed (p : Fin n → ℝ) {A B : ℝ} {x y : Fin n → ℝ}
    (hx : A ^ 2 ≤ ∑ i, x i ^ 2) (hy : B ^ 2 ≤ ∑ i, y i ^ 2) (hxy : ∑ i, x i * y i = 0)
    (hw : ∀ i, |x i| + |y i| ≤ p i)
    (hpos : ∀ i, 0 < x i * y i → |y i| ≤ |x i|) (hneg : ∀ i, x i * y i < 0 → |x i| ≤ |y i|) :
    ∃ x' y' : Fin n → ℝ, A ^ 2 ≤ ∑ i, x' i ^ 2 ∧ B ^ 2 ≤ ∑ i, y' i ^ 2 ∧
      ∑ i, x' i * y' i = 0 ∧ (∀ i, |x' i| + |y' i| ≤ p i) ∧ ∀ i, x' i * y' i = 0 := by
  classical
  have hp : ∀ i, 0 ≤ p i := fun i => le_trans (by positivity) (hw i)
  set x' : Fin n → ℝ := fun i => if y i = 0 ∨ 0 < x i * y i then p i else 0 with hx'
  set y' : Fin n → ℝ := fun i => if y i = 0 ∨ 0 < x i * y i then 0 else p i with hy'
  have key : ∀ i, x i * y i ≤ x' i ^ 2 - x i ^ 2 ∧ -(x i * y i) ≤ y' i ^ 2 - y i ^ 2 := by
    intro i
    have ha := abs_nonneg (x i)
    have hb := abs_nonneg (y i)
    have hab : |x i * y i| = |x i| * |y i| := abs_mul _ _
    have hx2 : x i ^ 2 = |x i| ^ 2 := (sq_abs _).symm
    have hy2 : y i ^ 2 = |y i| ^ 2 := (sq_abs _).symm
    have hle := le_abs_self (x i * y i)
    have hle' := neg_abs_le (x i * y i)
    have hwi := hw i
    have hp2 : (|x i| + |y i|) ^ 2 ≤ p i ^ 2 := by nlinarith
    by_cases hq : y i = 0 ∨ 0 < x i * y i
    · simp only [hx', hy', hq, ↓reduceIte]
      refine ⟨by nlinarith, ?_⟩
      rcases hq with h0 | h0
      · simp [h0]
      · have := hpos i h0
        rw [abs_of_pos h0] at hab
        nlinarith
    · simp only [hx', hy', hq, ↓reduceIte]
      push Not at hq
      obtain ⟨hy0, hxy0⟩ := hq
      refine ⟨?_, by nlinarith⟩
      rcases hxy0.lt_or_eq with h0 | h0
      · have := hneg i h0
        rw [abs_of_neg h0] at hab
        nlinarith
      · have : x i = 0 := by
          rcases mul_eq_zero.1 h0 with h | h
          · exact h
          · exact absurd h hy0
        simp [this]
  have hsum : ∀ (f g : Fin n → ℝ), (∀ i, f i ≤ g i) → ∑ i, f i ≤ ∑ i, g i :=
    fun f g h => Finset.sum_le_sum fun i _ => h i
  have hnm : ∀ i, x' i * y' i = 0 := by
    intro i
    by_cases hq : y i = 0 ∨ 0 < x i * y i
    · simp [hx', hy', hq]
    · simp [hx', hy', hq]
  refine ⟨x', y', ?_, ?_, ?_, fun i => ?_, hnm⟩
  · have h1 := hsum _ _ fun i => (key i).1
    rw [Finset.sum_sub_distrib, hxy] at h1
    linarith
  · have h1 := hsum _ _ fun i => (key i).2
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, hxy] at h1
    linarith
  · simp only [hnm, Finset.sum_const_zero]
  · by_cases hq : y i = 0 ∨ 0 < x i * y i
    · simp [hx', hy', hq, abs_of_nonneg (hp i)]
    · simp [hx', hy', hq, abs_of_nonneg (hp i)]

/-- Lemma R ⇒ (II) (via Lemma C). -/
theorem condII_of_signs (h : 2 ≤ n) (p : Fin n → ℝ) {A B : ℝ} {x y : Fin n → ℝ}
    (hx : A ^ 2 ≤ ∑ i, x i ^ 2) (hy : B ^ 2 ≤ ∑ i, y i ^ 2) (hxy : ∑ i, x i * y i = 0)
    (hw : ∀ i, |x i| + |y i| ≤ p i)
    (hpos : ∀ i, 0 < x i * y i → |y i| ≤ |x i|) (hneg : ∀ i, x i * y i < 0 → |x i| ≤ |y i|) :
    CondII p A B := by
  obtain ⟨x', y', hx', hy', hxy', hw', h0⟩ := lemmaR_noMixed p hx hy hxy hw hpos hneg
  exact condII_of_mixed_subset p hx' hy' hxy' hw' (k := ⟨0, by omega⟩) (l := ⟨1, by omega⟩)
    (by simp [Fin.ext_iff]) fun i _ _ => h0 i

/-- Lemma R "the other way round" (sides swapped): reduces to `condII_of_signs` for `(x, −y)`. -/
theorem condII_of_signs' (h : 2 ≤ n) (p : Fin n → ℝ) {A B : ℝ} {x y : Fin n → ℝ}
    (hx : A ^ 2 ≤ ∑ i, x i ^ 2) (hy : B ^ 2 ≤ ∑ i, y i ^ 2) (hxy : ∑ i, x i * y i = 0)
    (hw : ∀ i, |x i| + |y i| ≤ p i)
    (hpos : ∀ i, 0 < x i * y i → |x i| ≤ |y i|) (hneg : ∀ i, x i * y i < 0 → |y i| ≤ |x i|) :
    CondII p A B := by
  refine condII_of_signs h p (y := fun i => -y i) hx (by simpa [neg_sq] using hy)
    (by simp [hxy]) (by simpa using hw) (fun i hi => ?_) (fun i hi => ?_)
  · simp only [mul_neg, neg_pos] at hi
    simpa using hneg i hi
  · simp only [mul_neg, neg_lt_zero] at hi
    simpa using hpos i hi

/-! ## Lemma V -/

/-- The parameter of an axis `t = (|a| − |b|)/(|a| + |b|)` (Section 4.3). -/
noncomputable def tt (a b : ℝ) : ℝ := (|a| - |b|) / (|a| + |b|)

/-- The new value of `x` on an axis with parameter `T` (the sign and the width `|a| + |b|` are kept). -/
noncomputable def rx (a b T : ℝ) : ℝ := a / |a| * ((|a| + |b|) * (1 + T) / 2)

/-- The new value of `y` on an axis with parameter `T`. -/
noncomputable def ry (a b T : ℝ) : ℝ := b / |b| * ((|a| + |b|) * (1 - T) / 2)

/-- Recomputing one mixed axis when `t ↦ T`. -/
lemma row_facts {a b T : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hT : |T| ≤ 1) :
    |tt a b| < 1 ∧
    rx a b T ^ 2 - a ^ 2 = (|a| + |b|) ^ 2 * ((1 + T) ^ 2 - (1 + tt a b) ^ 2) / 4 ∧
    ry a b T ^ 2 - b ^ 2 = (|a| + |b|) ^ 2 * ((1 - T) ^ 2 - (1 - tt a b) ^ 2) / 4 ∧
    rx a b T * ry a b T - a * b =
      (a * b / (|a| * |b|)) * ((|a| + |b|) ^ 2 * (tt a b ^ 2 - T ^ 2) / 4) ∧
    |rx a b T * ry a b T| - |a * b| = (|a| + |b|) ^ 2 * (tt a b ^ 2 - T ^ 2) / 4 ∧
    |rx a b T| + |ry a b T| = |a| + |b| := by
  have hα : 0 < |a| := abs_pos.2 ha
  have hβ : 0 < |b| := abs_pos.2 hb
  have hr : 0 < |a| + |b| := by linarith
  have hαne := hα.ne'
  have hβne := hβ.ne'
  have hrne := hr.ne'
  have hu2 : (a / |a|) ^ 2 = 1 := by rw [div_pow, sq_abs, div_self (pow_ne_zero 2 ha)]
  have hw2 : (b / |b|) ^ 2 = 1 := by rw [div_pow, sq_abs, div_self (pow_ne_zero 2 hb)]
  have hua : abs (a / |a|) = 1 := by rw [abs_div, abs_abs, div_self hαne]
  have hwb : abs (b / |b|) = 1 := by rw [abs_div, abs_abs, div_self hβne]
  obtain ⟨hT1, hT2⟩ := abs_le.1 hT
  have eα : |a| = (|a| + |b|) * (1 + tt a b) / 2 := by unfold tt; field_simp; ring
  have eβ : |b| = (|a| + |b|) * (1 - tt a b) / 2 := by unfold tt; field_simp; ring
  have ea : a = a / |a| * ((|a| + |b|) * (1 + tt a b) / 2) := by
    rw [← eα]; field_simp
  have eb : b = b / |b| * ((|a| + |b|) * (1 - tt a b) / 2) := by
    rw [← eβ]; field_simp
  have habsx : |rx a b T| = (|a| + |b|) * (1 + T) / 2 := by
    unfold rx; rw [abs_mul, hua, one_mul, abs_of_nonneg (by nlinarith)]
  have habsy : |ry a b T| = (|a| + |b|) * (1 - T) / 2 := by
    unfold ry; rw [abs_mul, hwb, one_mul, abs_of_nonneg (by nlinarith)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold tt
    rw [abs_lt, lt_div_iff₀ hr, div_lt_iff₀ hr]
    constructor <;> linarith
  · have e : (a / |a| * ((|a| + |b|) * (1 + T) / 2)) ^ 2 -
        (a / |a| * ((|a| + |b|) * (1 + tt a b) / 2)) ^ 2 =
        (|a| + |b|) ^ 2 * ((1 + T) ^ 2 - (1 + tt a b) ^ 2) / 4 := by
      linear_combination ((|a| + |b|) ^ 2 * ((1 + T) ^ 2 - (1 + tt a b) ^ 2) / 4) * hu2
    rw [← ea] at e
    exact e
  · have e : (b / |b| * ((|a| + |b|) * (1 - T) / 2)) ^ 2 -
        (b / |b| * ((|a| + |b|) * (1 - tt a b) / 2)) ^ 2 =
        (|a| + |b|) ^ 2 * ((1 - T) ^ 2 - (1 - tt a b) ^ 2) / 4 := by
      linear_combination ((|a| + |b|) ^ 2 * ((1 - T) ^ 2 - (1 - tt a b) ^ 2) / 4) * hw2
    rw [← eb] at e
    exact e
  · have e : (a / |a| * ((|a| + |b|) * (1 + T) / 2)) * (b / |b| * ((|a| + |b|) * (1 - T) / 2)) -
        (a / |a| * ((|a| + |b|) * (1 + tt a b) / 2)) *
          (b / |b| * ((|a| + |b|) * (1 - tt a b) / 2)) =
        (a * b / (|a| * |b|)) * ((|a| + |b|) ^ 2 * (tt a b ^ 2 - T ^ 2) / 4) := by
      field_simp
      ring
    rw [← ea, ← eb] at e
    exact e
  · rw [abs_mul, abs_mul, habsx, habsy]
    have := congrArg₂ (· * ·) eα eβ
    linear_combination (-1 : ℝ) * this
  · rw [habsx, habsy]; ring

/-- The difference of sums when the functions agree outside three distinct points. -/
lemma sum_eq_add_three {f g : Fin n → ℝ} {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (h : ∀ m, m ≠ i → m ≠ j → m ≠ k → f m = g m) :
    ∑ m, f m = ∑ m, g m + (f i - g i) + (f j - g j) + (f k - g k) := by
  classical
  have e : ∑ m, (f m - g m) = ∑ m ∈ {i, j, k}, (f m - g m) := by
    refine (Finset.sum_subset (subset_univ _) fun m _ hm => ?_).symm
    simp only [mem_insert, mem_singleton, not_or] at hm
    rw [h m hm.1 hm.2.1 hm.2.2, sub_self]
  rw [Finset.sum_insert (by simp [hij, hik]), Finset.sum_insert (by simp [hjk]),
    Finset.sum_singleton, Finset.sum_sub_distrib] at e
  linarith

/-- **Lemma V** (Section 5). Let `i ≠ j` be mixed axes of side `+`, `k` a mixed axis
of side `−`, and suppose `tᵢ = tⱼ ∧ tᵢ t_k ≤ 0` fails (cases (a) `tᵢ ≠ tⱼ` and (b)
`tᵢ = tⱼ`, `tᵢ t_k > 0`). Then there is a solution of the relaxed problem with a strictly smaller
`∑ |xᵢ yᵢ|` (that is, `D`). -/
theorem lemmaV (p : Fin n → ℝ) {A B : ℝ} {x y : Fin n → ℝ}
    (hx : A ^ 2 ≤ ∑ i, x i ^ 2) (hy : B ^ 2 ≤ ∑ i, y i ^ 2) (hxy : ∑ i, x i * y i = 0)
    (hw : ∀ i, |x i| + |y i| ≤ p i) {i j k : Fin n} (hij : i ≠ j)
    (hi : 0 < x i * y i) (hj : 0 < x j * y j) (hk : x k * y k < 0)
    (hnot : ¬ (tt (x i) (y i) = tt (x j) (y j) ∧ tt (x i) (y i) * tt (x k) (y k) ≤ 0)) :
    ∃ x' y' : Fin n → ℝ, A ^ 2 ≤ ∑ m, x' m ^ 2 ∧ B ^ 2 ≤ ∑ m, y' m ^ 2 ∧
      ∑ m, x' m * y' m = 0 ∧ (∀ m, |x' m| + |y' m| ≤ p m) ∧
      ∑ m, |x' m * y' m| < ∑ m, |x m * y m| := by
  classical
  have hik : i ≠ k := by rintro rfl; linarith
  have hjk : j ≠ k := by rintro rfl; linarith
  have nz : ∀ m, x m * y m ≠ 0 → x m ≠ 0 ∧ y m ≠ 0 := fun m h => mul_ne_zero_iff.1 h
  obtain ⟨hxi, hyi⟩ := nz i hi.ne'
  obtain ⟨hxj, hyj⟩ := nz j hj.ne'
  obtain ⟨hxk, hyk⟩ := nz k hk.ne
  have hPi : 0 < (|x i| + |y i|) ^ 2 := by have := abs_pos.2 hxi; positivity
  have hPj : 0 < (|x j| + |y j|) ^ 2 := by have := abs_pos.2 hxj; positivity
  have hPk : 0 < (|x k| + |y k|) ^ 2 := by have := abs_pos.2 hxk; positivity
  obtain ⟨hti, -⟩ := row_facts (T := 0) hxi hyi (by simp)
  obtain ⟨htj, -⟩ := row_facts (T := 0) hxj hyj (by simp)
  obtain ⟨htk, -⟩ := row_facts (T := 0) hxk hyk (by simp)
  obtain ⟨X, Y, s, hX, hY, hs, hlt, E1, E2⟩ := lemmaV_core hPi hPj hPk hti htj htk hnot
  obtain ⟨-, Rxi, Ryi, Pxyi, Pabsi, Wi⟩ := row_facts hxi hyi hX
  obtain ⟨-, Rxj, Ryj, Pxyj, Pabsj, Wj⟩ := row_facts hxj hyj hY
  obtain ⟨-, Rxk, Ryk, Pxyk, Pabsk, Wk⟩ := row_facts hxk hyk hs
  have ei : x i * y i / (|x i| * |y i|) = 1 := by
    rw [← abs_mul, abs_of_pos hi, div_self hi.ne']
  have ej : x j * y j / (|x j| * |y j|) = 1 := by
    rw [← abs_mul, abs_of_pos hj, div_self hj.ne']
  have ek : x k * y k / (|x k| * |y k|) = -1 := by
    rw [← abs_mul, abs_of_neg hk, div_neg, div_self hk.ne]
  rw [ei] at Pxyi
  rw [ej] at Pxyj
  rw [ek] at Pxyk
  set x' : Fin n → ℝ := fun m => if m = i then rx (x i) (y i) X else if m = j then
    rx (x j) (y j) Y else if m = k then rx (x k) (y k) s else x m with hx'
  set y' : Fin n → ℝ := fun m => if m = i then ry (x i) (y i) X else if m = j then
    ry (x j) (y j) Y else if m = k then ry (x k) (y k) s else y m with hy'
  have x'i : x' i = rx (x i) (y i) X := by simp [hx']
  have x'j : x' j = rx (x j) (y j) Y := by simp [hx', hij.symm]
  have x'k : x' k = rx (x k) (y k) s := by simp [hx', hik.symm, hjk.symm]
  have y'i : y' i = ry (x i) (y i) X := by simp [hy']
  have y'j : y' j = ry (x j) (y j) Y := by simp [hy', hij.symm]
  have y'k : y' k = ry (x k) (y k) s := by simp [hy', hik.symm, hjk.symm]
  have x'o : ∀ m, m ≠ i → m ≠ j → m ≠ k → x' m = x m := fun m h1 h2 h3 => by
    simp [hx', h1, h2, h3]
  have y'o : ∀ m, m ≠ i → m ≠ j → m ≠ k → y' m = y m := fun m h1 h2 h3 => by
    simp [hy', h1, h2, h3]
  have S1 := sum_eq_add_three (f := fun m => x' m ^ 2) (g := fun m => x m ^ 2) hij hik hjk
    fun m h1 h2 h3 => by simp only [x'o m h1 h2 h3]
  have S2 := sum_eq_add_three (f := fun m => y' m ^ 2) (g := fun m => y m ^ 2) hij hik hjk
    fun m h1 h2 h3 => by simp only [y'o m h1 h2 h3]
  have S3 := sum_eq_add_three (f := fun m => x' m * y' m) (g := fun m => x m * y m) hij hik hjk
    fun m h1 h2 h3 => by simp only [x'o m h1 h2 h3, y'o m h1 h2 h3]
  have S4 := sum_eq_add_three (f := fun m => |x' m * y' m|) (g := fun m => |x m * y m|)
    hij hik hjk fun m h1 h2 h3 => by simp only [x'o m h1 h2 h3, y'o m h1 h2 h3]
  simp only [x'i, x'j, x'k, y'i, y'j, y'k] at S1 S2 S3 S4
  rw [Rxi, Rxj, Rxk] at S1
  rw [Ryi, Ryj, Ryk] at S2
  rw [Pxyi, Pxyj, Pxyk] at S3
  rw [Pabsi, Pabsj, Pabsk] at S4
  have hpos : 0 < (|x k| + |y k|) ^ 2 * (s ^ 2 - tt (x k) (y k) ^ 2) :=
    mul_pos hPk (by linarith)
  refine ⟨x', y', ?_, ?_, ?_, fun m => ?_, ?_⟩
  · have key : ∑ m, x' m ^ 2 =
        ∑ m, x m ^ 2 + (|x k| + |y k|) ^ 2 * (s ^ 2 - tt (x k) (y k) ^ 2) / 2 := by
      rw [S1]; linear_combination (1 / 2 : ℝ) * E1 + (1 / 4 : ℝ) * E2
    rw [key]; linarith
  · have key : ∑ m, y' m ^ 2 =
        ∑ m, y m ^ 2 + (|x k| + |y k|) ^ 2 * (s ^ 2 - tt (x k) (y k) ^ 2) / 2 := by
      rw [S2]; linear_combination (-1 / 2 : ℝ) * E1 + (1 / 4 : ℝ) * E2
    rw [key]; linarith
  · rw [S3, hxy]
    linear_combination (-1 / 4 : ℝ) * E2
  · by_cases h1 : m = i
    · subst h1; rw [x'i, y'i, Wi]; exact hw _
    · by_cases h2 : m = j
      · subst h2; rw [x'j, y'j, Wj]; exact hw _
      · by_cases h3 : m = k
        · subst h3; rw [x'k, y'k, Wk]; exact hw _
        · rw [x'o m h1 h2 h3, y'o m h1 h2 h3]; exact hw m
  · have key : ∑ m, |x' m * y' m| =
        ∑ m, |x m * y m| - (|x k| + |y k|) ^ 2 * (s ^ 2 - tt (x k) (y k) ^ 2) / 2 := by
      rw [S4]; linear_combination (-1 / 4 : ℝ) * E2
    rw [key]; linarith

end RectInNBox
