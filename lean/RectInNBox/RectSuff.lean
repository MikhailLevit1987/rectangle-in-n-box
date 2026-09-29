import RectInNBox.Widths

/-!
# A rectangle in an `n`-box: definitions, the relaxed form, sufficiency, Lemma C

References are to the paper (`paper/rectangle-in-n-box-en.pdf`).

* `CondII p A B` — condition **(II)** of Section 2. "The rectangle `a′ × b′` fits into the 2-box
  `(p_k, p_l)`" is written literally as `FitsN ![p k, p l] ![a′, b′]` (in `ℝ²`). The positive part `(·)₊`
  under the root is not needed: in Mathlib `√x = 0` for `x ≤ 0`.
* `CondI p A B` — condition **(I)**.
* `RectW p A B` — the relaxed form of (1) (Section 4.2) in the variables `x = A u`, `y = B v`:
  `‖x‖² ≥ A²`, `‖y‖² ≥ B²`, `⟨x, y⟩ = 0`, `|xᵢ| + |yᵢ| ≤ pᵢ`.

Results of the file:
* `fitsN_rect_iff_rectW` — `FitsN p (pad h ![A, B]) ↔ RectW p A B` (formula (1) + Section 4.2);
* `fits2_iff_rectW` — the same in `ℝ²` without `pad`;
* `rectW_of_condII` — sufficiency: (II) ⇒ fits (Section 3);
* `condII_of_mixed_subset` — Lemma C (Section 5) in the form: if all "mixed" axes
  (`xᵢ yᵢ ≠ 0`) lie in `{k, l}`, `k ≠ l`, then (II);
* `condII_of_condI` — (I) ⇒ (II) (Section 7).
-/

namespace RectInNBox

open Finset

variable {n : ℕ}

/-! ## Definitions -/

/-- The relaxed form of (1) (Section 4.2) in the variables `x = A u`, `y = B v`. -/
def RectW (p : Fin n → ℝ) (A B : ℝ) : Prop :=
  ∃ x y : Fin n → ℝ, A ^ 2 ≤ ∑ i, x i ^ 2 ∧ B ^ 2 ≤ ∑ i, y i ^ 2 ∧ ∑ i, x i * y i = 0 ∧
    ∀ i, |x i| + |y i| ≤ p i

/-- **Condition (II)** (Section 2): there are `k ≠ l` and a partition `S ⊔ T = [n] ∖ {k, l}` such that
the rectangle `a′ × b′`, `a′ = √(A² − ‖p_S‖²)₊`, `b′ = √(B² − ‖p_T‖²)₊`, fits into
the 2-box `(p_k, p_l)`. -/
def CondII (p : Fin n → ℝ) (A B : ℝ) : Prop :=
  ∃ k l : Fin n, k ≠ l ∧ ∃ S T : Finset (Fin n), Disjoint S T ∧ S ∪ T = univ \ {k, l} ∧
    FitsN ![p k, p l] ![√(A ^ 2 - ∑ i ∈ S, p i ^ 2), √(B ^ 2 - ∑ i ∈ T, p i ^ 2)]

/-- **Condition (I)** (Section 2): disjoint `S, T` with `A ≤ ‖p_S‖`, `B ≤ ‖p_T‖`
(squared; for `A, B ≥ 0` this is the same). -/
def CondI (p : Fin n → ℝ) (A B : ℝ) : Prop :=
  ∃ S T : Finset (Fin n), Disjoint S T ∧ A ^ 2 ≤ ∑ i ∈ S, p i ^ 2 ∧ B ^ 2 ≤ ∑ i ∈ T, p i ^ 2

/-! ## Auxiliary facts -/

lemma pad_refl {m : ℕ} (q : Fin m → ℝ) : pad le_rfl q = q := by
  funext i
  simpa using pad_castLE (le_refl m) q i

/-- `a ≤ s + (√(a − s)₊)²`. -/
lemma le_add_sq_sqrt_sub (a s : ℝ) : a ≤ s + √(a - s) ^ 2 := by
  rw [Real.sq_sqrt']
  have := le_max_left (a - s) 0
  linarith

/-- `(√c₊)² ≤ t` if `c ≤ t` and `0 ≤ t`. -/
lemma sq_sqrt_le_of {c t : ℝ} (h : c ≤ t) (ht : 0 ≤ t) : √c ^ 2 ≤ t := by
  rw [Real.sq_sqrt']
  exact max_le h ht

/-- In `ℝⁿ`, `n ≥ 2`: every vector has an orthogonal unit vector. -/
lemma exists_unit_perp (h : 2 ≤ n) (w : Fin n → ℝ) :
    ∃ u : Fin n → ℝ, ∑ i, u i ^ 2 = 1 ∧ ∑ i, u i * w i = 0 := by
  classical
  set i₀ : Fin n := ⟨0, by omega⟩
  set i₁ : Fin n := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  by_cases hw : w i₀ = 0 ∧ w i₁ = 0
  · refine ⟨fun i => if i = i₀ then 1 else 0, ?_, ?_⟩
    · simp [ite_pow]
    · simp [hw.1]
  · have hr2 : 0 < w i₀ ^ 2 + w i₁ ^ 2 := by
      by_contra hc
      push Not at hc
      apply hw
      constructor <;> nlinarith [sq_nonneg (w i₀), sq_nonneg (w i₁)]
    set r := √(w i₀ ^ 2 + w i₁ ^ 2)
    have hr : 0 < r := Real.sqrt_pos.2 hr2
    have hrr : r ^ 2 = w i₀ ^ 2 + w i₁ ^ 2 := Real.sq_sqrt hr2.le
    refine ⟨fun i => if i = i₀ then -w i₁ / r else if i = i₁ then w i₀ / r else 0, ?_, ?_⟩
    · rw [Finset.sum_eq_add i₀ i₁ h01 ?_ (by simp) (by simp)]
      · simp only [h01.symm, ↓reduceIte, div_pow, neg_div, neg_sq]
        rw [← add_div, add_comm, ← hrr]
        exact div_self (pow_pos hr 2).ne'
      · intro c _ hc; simp [hc.1, hc.2]
    · rw [Finset.sum_eq_add i₀ i₁ h01 ?_ (by simp) (by simp)]
      · simp only [h01.symm, ↓reduceIte]
        ring
      · intro c _ hc; simp [hc.1, hc.2]

/-- Normalization `x ↦ x / ‖x‖`. -/
lemma normalize_props (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 ≠ 0) :
    (∑ i, (x i / √(∑ j, x j ^ 2)) ^ 2 = 1) ∧
    ∀ c, 0 ≤ c → c ^ 2 ≤ ∑ j, x j ^ 2 → ∀ i, c * |x i / √(∑ j, x j ^ 2)| ≤ |x i| := by
  have hpos : 0 < ∑ j, x j ^ 2 :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => sq_nonneg (x j)) (Ne.symm hx)
  have hN : 0 < √(∑ j, x j ^ 2) := Real.sqrt_pos.2 hpos
  refine ⟨?_, fun c hc hc2 i => ?_⟩
  · simp only [div_pow, ← Finset.sum_div, Real.sq_sqrt hpos.le]
    exact div_self hx
  · have hcN : c ≤ √(∑ j, x j ^ 2) := Real.le_sqrt_of_sq_le hc2
    rw [abs_div, abs_of_pos hN, mul_div_assoc', div_le_iff₀ hN]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hcN (abs_nonneg _)

/-! ## The relaxed form -/

/-- Formula (1) ⇔ the relaxed form `RectW` (Section 4.2: shrink `u`, `v` to unit vectors). -/
theorem rect_iff_rectW (h : 2 ≤ n) (p : Fin n → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∃ u v : Fin n → ℝ, (∑ i, u i ^ 2 = 1) ∧ (∑ i, v i ^ 2 = 1) ∧ (∑ i, u i * v i = 0) ∧
      ∀ i, A * |u i| + B * |v i| ≤ p i) ↔ RectW p A B := by
  constructor
  · rintro ⟨u, v, hu, hv, huv, hw⟩
    refine ⟨fun i => A * u i, fun i => B * v i, ?_, ?_, ?_, fun i => ?_⟩
    · simp only [mul_pow, ← Finset.mul_sum, hu, mul_one, le_refl]
    · simp only [mul_pow, ← Finset.mul_sum, hv, mul_one, le_refl]
    · have : ∀ i, A * u i * (B * v i) = (A * B) * (u i * v i) := fun i => by ring
      simp only [this, ← Finset.mul_sum, huv, mul_zero]
    · simpa [abs_mul, abs_of_nonneg hA, abs_of_nonneg hB] using hw i
  · rintro ⟨x, y, hx, hy, hxy, hw⟩
    -- assembling from the given `u`, `v`
    have key : ∀ u v : Fin n → ℝ, ∑ i, u i ^ 2 = 1 → ∑ i, v i ^ 2 = 1 → ∑ i, u i * v i = 0 →
        (∀ i, A * |u i| ≤ |x i|) → (∀ i, B * |v i| ≤ |y i|) →
        ∃ u v : Fin n → ℝ, (∑ i, u i ^ 2 = 1) ∧ (∑ i, v i ^ 2 = 1) ∧ (∑ i, u i * v i = 0) ∧
          ∀ i, A * |u i| + B * |v i| ≤ p i :=
      fun u v hu hv huv hAu hBv =>
        ⟨u, v, hu, hv, huv, fun i => by linarith [hAu i, hBv i, hw i]⟩
    have zero_of : ∀ {c : ℝ} (z : Fin n → ℝ), 0 ≤ c → c ^ 2 ≤ ∑ i, z i ^ 2 →
        ∑ i, z i ^ 2 = 0 → c = 0 := by
      intro c z hc h1 h2
      rw [h2] at h1
      nlinarith
    by_cases hx0 : ∑ i, x i ^ 2 = 0 <;> by_cases hy0 : ∑ i, y i ^ 2 = 0
    · -- `A = B = 0`
      have hA0 := zero_of x hA hx hx0
      have hB0 := zero_of y hB hy hy0
      obtain ⟨u, hu, -⟩ := exists_unit_perp h (0 : Fin n → ℝ)
      obtain ⟨v, hv, hvu⟩ := exists_unit_perp h u
      refine key u v hu hv (by simpa [mul_comm] using hvu) (fun i => ?_) (fun i => ?_)
      · simp [hA0]
      · simp [hB0]
    · -- `A = 0`
      have hA0 := zero_of x hA hx hx0
      obtain ⟨hv1, hv2⟩ := normalize_props y hy0
      obtain ⟨u, hu, huv⟩ := exists_unit_perp h (fun i => y i / √(∑ j, y j ^ 2))
      exact key u _ hu hv1 huv (fun i => by simp [hA0]) (hv2 B hB hy)
    · -- `B = 0`
      have hB0 := zero_of y hB hy hy0
      obtain ⟨hu1, hu2⟩ := normalize_props x hx0
      obtain ⟨v, hv, hvu⟩ := exists_unit_perp h (fun i => x i / √(∑ j, x j ^ 2))
      exact key _ v hu1 hv (by simpa [mul_comm] using hvu) (hu2 A hA hx) (fun i => by simp [hB0])
    · obtain ⟨hu1, hu2⟩ := normalize_props x hx0
      obtain ⟨hv1, hv2⟩ := normalize_props y hy0
      refine key _ _ hu1 hv1 ?_ (hu2 A hA hx) (hv2 B hB hy)
      have : ∀ i, x i / √(∑ j, x j ^ 2) * (y i / √(∑ j, y j ^ 2)) =
          (x i * y i) / (√(∑ j, x j ^ 2) * √(∑ j, y j ^ 2)) := fun i => by ring
      simp only [this, ← Finset.sum_div, hxy, zero_div]

/-- **Formula (1) in the relaxed form:** the rectangle `A × B` fits into the `n`-box `p`
⇔ `RectW p A B`. -/
theorem fitsN_rect_iff_rectW (h : 2 ≤ n) (p : Fin n → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    FitsN p (pad h ![A, B]) ↔ RectW p A B :=
  (fitsN_rect_iff h p hA hB).trans (rect_iff_rectW h p hA hB)

/-- The plane case: a rectangle `a × b` in the 2-box `(X, Y)`. -/
theorem fits2_iff_rectW (X Y : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    FitsN ![X, Y] ![a, b] ↔ RectW ![X, Y] a b := by
  have := fitsN_rect_iff_rectW (le_refl 2) ![X, Y] ha hb
  rwa [pad_refl] at this

/-! ## Sufficiency (Section 3) -/

/-- **Sufficiency** (Section 3): (II) ⇒ the relaxed form of (1). In the relaxed form
`λ = μ = 1` suffice: `x = p_S + (x′ on the axes k, l)`, `y = p_T + (y′ on the axes k, l)`. -/
theorem rectW_of_condII (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) {A B : ℝ} (hII : CondII p A B) :
    RectW p A B := by
  classical
  obtain ⟨k, l, hkl, S, T, hST, hU, hfit⟩ := hII
  rw [fits2_iff_rectW _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)] at hfit
  obtain ⟨x', y', hx', hy', hxy', hw'⟩ := hfit
  simp only [Fin.sum_univ_two] at hx' hy' hxy'
  have hw0 := hw' 0
  have hw1 := hw' 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hw0 hw1
  have hS : ∀ i ∈ S, i ≠ k ∧ i ≠ l := by
    intro i hi
    have : i ∈ univ \ {k, l} := hU ▸ mem_union_left T hi
    simpa using this
  have hT : ∀ i ∈ T, i ≠ k ∧ i ≠ l := by
    intro i hi
    have : i ∈ univ \ {k, l} := hU ▸ mem_union_right S hi
    simpa using this
  have hSorT : ∀ i, i ≠ k → i ≠ l → i ∈ S ∨ i ∈ T := by
    intro i hik hil
    have : i ∈ univ \ {k, l} := by simp [hik, hil]
    rw [← hU] at this
    exact mem_union.1 this
  set x : Fin n → ℝ := fun i =>
    if i ∈ S then p i else if i = k then x' 0 else if i = l then x' 1 else 0 with hxdef
  set y : Fin n → ℝ := fun i =>
    if i ∈ T then p i else if i = k then y' 0 else if i = l then y' 1 else 0 with hydef
  have px2 : ∀ i, x i ^ 2 = (if i ∈ S then p i ^ 2 else 0) + (if i = k then x' 0 ^ 2 else 0) +
      (if i = l then x' 1 ^ 2 else 0) := by
    intro i
    by_cases hiS : i ∈ S
    · simp [x, hiS, (hS i hiS).1, (hS i hiS).2]
    · by_cases hik : i = k
      · subst hik; simp [x, hiS, hkl]
      · by_cases hil : i = l
        · subst hil; simp [x, hiS, hik]
        · simp [x, hiS, hik, hil]
  have py2 : ∀ i, y i ^ 2 = (if i ∈ T then p i ^ 2 else 0) + (if i = k then y' 0 ^ 2 else 0) +
      (if i = l then y' 1 ^ 2 else 0) := by
    intro i
    by_cases hiT : i ∈ T
    · simp [y, hiT, (hT i hiT).1, (hT i hiT).2]
    · by_cases hik : i = k
      · subst hik; simp [y, hiT, hkl]
      · by_cases hil : i = l
        · subst hil; simp [y, hiT, hik]
        · simp [y, hiT, hik, hil]
  have pxy : ∀ i, x i * y i = (if i = k then x' 0 * y' 0 else 0) +
      (if i = l then x' 1 * y' 1 else 0) := by
    intro i
    by_cases hiS : i ∈ S
    · have hiT : i ∉ T := Finset.disjoint_left.1 hST hiS
      simp [x, y, hiS, hiT, (hS i hiS).1, (hS i hiS).2]
    · by_cases hiT : i ∈ T
      · simp [x, y, hiS, hiT, (hT i hiT).1, (hT i hiT).2]
      · by_cases hik : i = k
        · subst hik
          have hkS : i ∉ S := hiS
          simp [x, y, hiS, hiT, hkl]
        · by_cases hil : i = l
          · subst hil; simp [x, y, hiS, hiT, hik]
          · simp [x, y, hiS, hiT, hik, hil]
  refine ⟨x, y, ?_, ?_, ?_, fun i => ?_⟩
  · rw [Finset.sum_congr rfl fun i _ => px2 i]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_mem, univ_inter, Finset.sum_ite_eq',
      mem_univ, ite_true]
    have := le_add_sq_sqrt_sub (A ^ 2) (∑ i ∈ S, p i ^ 2)
    linarith
  · rw [Finset.sum_congr rfl fun i _ => py2 i]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_mem, univ_inter, Finset.sum_ite_eq',
      mem_univ, ite_true]
    have := le_add_sq_sqrt_sub (B ^ 2) (∑ i ∈ T, p i ^ 2)
    linarith
  · rw [Finset.sum_congr rfl fun i _ => pxy i]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', mem_univ, ite_true]
    exact hxy'
  · by_cases hiS : i ∈ S
    · have hiT : i ∉ T := Finset.disjoint_left.1 hST hiS
      simp [x, y, hiS, hiT, (hS i hiS).1, (hS i hiS).2, abs_of_nonneg (hp i)]
    · by_cases hiT : i ∈ T
      · simp [x, y, hiS, hiT, (hT i hiT).1, (hT i hiT).2, abs_of_nonneg (hp i)]
      · by_cases hik : i = k
        · subst hik; simpa [x, y, hiS, hiT] using hw0
        · by_cases hil : i = l
          · subst hil; simpa [x, y, hiS, hiT, hik] using hw1
          · exact absurd (hSorT i hik hil) (by simp [hiS, hiT])

/-! ## Lemma C (Section 5) -/

/-- **Lemma C** (Section 5), in the form: if all mixed axes of a solution of the relaxed problem
(`xᵢ yᵢ ≠ 0`) lie among `{k, l}`, `k ≠ l`, then (II) holds. Covers both cases of
the paper ("no mixed axes" and "two mixed axes"): `S = {i ∉ {k,l} : yᵢ = 0}`, `T` — the rest. -/
theorem condII_of_mixed_subset (p : Fin n → ℝ) {A B : ℝ} {x y : Fin n → ℝ}
    (hx : A ^ 2 ≤ ∑ i, x i ^ 2) (hy : B ^ 2 ≤ ∑ i, y i ^ 2) (hxy : ∑ i, x i * y i = 0)
    (hw : ∀ i, |x i| + |y i| ≤ p i) {k l : Fin n} (hkl : k ≠ l)
    (hmix : ∀ i, i ≠ k → i ≠ l → x i * y i = 0) : CondII p A B := by
  classical
  set R : Finset (Fin n) := univ \ {k, l} with hR
  set S := R.filter (fun i => y i = 0)
  set T := R.filter (fun i => ¬ y i = 0)
  have hmemR : ∀ i ∈ R, i ≠ k ∧ i ≠ l := fun i hi => by simpa [R] using hi
  refine ⟨k, l, hkl, S, T, disjoint_filter_filter_not _ _ _, filter_union_filter_not_eq _ _, ?_⟩
  rw [fits2_iff_rectW _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  -- splitting the sums over `{k, l}` and `R = S ⊔ T`
  have split : ∀ f : Fin n → ℝ, ∑ i, f i = f k + f l + (∑ i ∈ S, f i + ∑ i ∈ T, f i) := by
    intro f
    rw [← Finset.sum_sdiff (subset_univ {k, l}), Finset.sum_pair hkl,
      ← Finset.sum_filter_add_sum_filter_not R (fun i => y i = 0)]
    ring
  have hxT : ∀ i ∈ T, x i = 0 := by
    intro i hi
    obtain ⟨hiR, hyi⟩ := Finset.mem_filter.1 hi
    have := hmix i (hmemR i hiR).1 (hmemR i hiR).2
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd h hyi
  have hyS : ∀ i ∈ S, y i = 0 := fun i hi => (Finset.mem_filter.1 hi).2
  have hp2 : ∀ (z : Fin n → ℝ), (∀ i, |z i| ≤ p i) → ∀ i, z i ^ 2 ≤ p i ^ 2 := by
    intro z hz i
    have h1 := hz i
    have h0 : 0 ≤ |z i| := abs_nonneg _
    rw [← sq_abs (z i)]
    nlinarith
  have hxp := hp2 x (fun i => by linarith [hw i, abs_nonneg (y i)])
  have hyp := hp2 y (fun i => by linarith [hw i, abs_nonneg (x i)])
  refine ⟨![x k, x l], ![y k, y l], ?_, ?_, ?_, ?_⟩
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have e := split (fun i => x i ^ 2)
    have hT0 : ∑ i ∈ T, x i ^ 2 = 0 := Finset.sum_eq_zero fun i hi => by simp [hxT i hi]
    have hSle : ∑ i ∈ S, x i ^ 2 ≤ ∑ i ∈ S, p i ^ 2 := Finset.sum_le_sum fun i _ => hxp i
    apply sq_sqrt_le_of
    · linarith
    · positivity
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have e := split (fun i => y i ^ 2)
    have hS0 : ∑ i ∈ S, y i ^ 2 = 0 := Finset.sum_eq_zero fun i hi => by simp [hyS i hi]
    have hTle : ∑ i ∈ T, y i ^ 2 ≤ ∑ i ∈ T, p i ^ 2 := Finset.sum_le_sum fun i _ => hyp i
    apply sq_sqrt_le_of
    · linarith
    · positivity
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have e := split (fun i => x i * y i)
    have hS0 : ∑ i ∈ S, x i * y i = 0 := Finset.sum_eq_zero fun i hi => by simp [hyS i hi]
    have hT0 : ∑ i ∈ T, x i * y i = 0 := Finset.sum_eq_zero fun i hi => by simp [hxT i hi]
    linarith
  · intro i
    fin_cases i
    · simpa using hw k
    · simpa using hw l

/-! ## (I) ⇒ (II) (Section 7) -/

/-- From (I): a solution of the relaxed problem without mixed axes, `x = p_S`, `y = p_T`. -/
lemma rectW_of_condI (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) {A B : ℝ} (hI : CondI p A B) :
    ∃ x y : Fin n → ℝ, A ^ 2 ≤ ∑ i, x i ^ 2 ∧ B ^ 2 ≤ ∑ i, y i ^ 2 ∧ ∑ i, x i * y i = 0 ∧
      (∀ i, |x i| + |y i| ≤ p i) ∧ ∀ i, x i * y i = 0 := by
  classical
  obtain ⟨S, T, hST, hS, hT⟩ := hI
  have hxy0 : ∀ i, (if i ∈ S then p i else 0) * (if i ∈ T then p i else 0) = 0 := by
    intro i
    by_cases hiS : i ∈ S
    · simp [hiS, Finset.disjoint_left.1 hST hiS]
    · simp [hiS]
  refine ⟨fun i => if i ∈ S then p i else 0, fun i => if i ∈ T then p i else 0, ?_, ?_, ?_,
    fun i => ?_, hxy0⟩
  · simpa [ite_pow, Finset.sum_ite_mem] using hS
  · simpa [ite_pow, Finset.sum_ite_mem] using hT
  · simp only [hxy0, Finset.sum_const_zero]
  · by_cases hiS : i ∈ S
    · simp [hiS, Finset.disjoint_left.1 hST hiS, abs_of_nonneg (hp i)]
    · by_cases hiT : i ∈ T
      · simp [hiS, hiT, abs_of_nonneg (hp i)]
      · simp [hiS, hiT, hp i]

/-- **Section 7: (I) ⇒ (II).** -/
theorem condII_of_condI (h : 2 ≤ n) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) {A B : ℝ}
    (hI : CondI p A B) : CondII p A B := by
  obtain ⟨x, y, hx, hy, hxy, hw, h0⟩ := rectW_of_condI p hp hI
  refine condII_of_mixed_subset p hx hy hxy hw (k := ⟨0, by omega⟩) (l := ⟨1, by omega⟩)
    (by simp [Fin.ext_iff]) fun i _ _ => h0 i

end RectInNBox
