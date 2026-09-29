import RectInNBox.RectLemmas

/-!
# The theorem on a rectangle in an `n`-box

The proof follows the paper, Sections 2–7.

**Main theorem** `fitsN_rect_iff_condII`: for `n ≥ 2`, `p ≥ 0`, `A, B ≥ 0`
`FitsN p (pad h ![A, B]) ↔ CondII p A B`.

Necessity (Section 6): on the compact set of solutions of the relaxed problem (`feasSet`) take a minimizer of
`Φ(x, y) = ∑ |xᵢ yᵢ|` (this is `D/2`). By Lemma V all mixed axes of one side of the minimizer
have a common `t`, and the `t` of sides `+` and `−` have different signs (if some side has ≥ 2 mixed
axes); then Lemma R applies. Otherwise there are at most two mixed axes, one on each side, and
Lemma C applies.
-/

namespace RectInNBox

open Finset

variable {n : ℕ}

/-- The set of solutions of the relaxed problem (Section 4.2) in `ℝⁿ × ℝⁿ`. -/
def feasSet (p : Fin n → ℝ) (A B : ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {z | A ^ 2 ≤ ∑ i, z.1 i ^ 2 ∧ B ^ 2 ≤ ∑ i, z.2 i ^ 2 ∧ ∑ i, z.1 i * z.2 i = 0 ∧
    ∀ i, |z.1 i| + |z.2 i| ≤ p i}

lemma isCompact_feasSet (p : Fin n → ℝ) (A B : ℝ) : IsCompact (feasSet p A B) := by
  have hsub : feasSet p A B ⊆ Set.Icc (-p) p ×ˢ Set.Icc (-p) p := by
    rintro ⟨x, y⟩ ⟨-, -, -, hw⟩
    have hx : ∀ i, |x i| ≤ p i := fun i => by linarith [hw i, abs_nonneg (y i)]
    have hy : ∀ i, |y i| ≤ p i := fun i => by linarith [hw i, abs_nonneg (x i)]
    refine ⟨⟨fun i => ?_, fun i => ?_⟩, ⟨fun i => ?_, fun i => ?_⟩⟩
    · simpa using (abs_le.1 (hx i)).1
    · exact (abs_le.1 (hx i)).2
    · simpa using (abs_le.1 (hy i)).1
    · exact (abs_le.1 (hy i)).2
  refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_ hsub
  have e : feasSet p A B = {z : (Fin n → ℝ) × (Fin n → ℝ) | A ^ 2 ≤ ∑ i, z.1 i ^ 2} ∩
      ({z | B ^ 2 ≤ ∑ i, z.2 i ^ 2} ∩ ({z | ∑ i, z.1 i * z.2 i = 0} ∩
        ⋂ i, {z | |z.1 i| + |z.2 i| ≤ p i})) := by
    ext z; simp [feasSet]
  rw [e]
  refine (isClosed_le continuous_const (by fun_prop)).inter
    ((isClosed_le continuous_const (by fun_prop)).inter
      ((isClosed_eq (by fun_prop) continuous_const).inter
        (isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const)))

lemma abs_le_of_tt_nonneg {a b : ℝ} (h : 0 ≤ tt a b) : |b| ≤ |a| := by
  by_contra hc
  push Not at hc
  have : tt a b < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith [abs_nonneg a])
  linarith

lemma abs_le_of_tt_nonpos {a b : ℝ} (h : tt a b ≤ 0) : |a| ≤ |b| := by
  by_contra hc
  push Not at hc
  have : 0 < tt a b := div_pos (by linarith) (by linarith [abs_nonneg b])
  linarith

/-- Case analysis of Section 6, items 1 and 3: side `+` has two mixed axes; the conclusions
of Lemma V (`Hp`, `Hm`) give the sign conditions of Lemma R. -/
lemma condII_of_structure (h : 2 ≤ n) (p : Fin n → ℝ) {A B : ℝ} {x y : Fin n → ℝ}
    (hx : A ^ 2 ≤ ∑ i, x i ^ 2) (hy : B ^ 2 ≤ ∑ i, y i ^ 2) (hxy : ∑ i, x i * y i = 0)
    (hw : ∀ i, |x i| + |y i| ≤ p i)
    (Hp : ∀ i j k, i ≠ j → 0 < x i * y i → 0 < x j * y j → x k * y k < 0 →
      tt (x i) (y i) = tt (x j) (y j) ∧ tt (x i) (y i) * tt (x k) (y k) ≤ 0)
    (Hm : ∀ i j k, i ≠ j → x i * y i < 0 → x j * y j < 0 → 0 < x k * y k →
      tt (x i) (y i) = tt (x j) (y j))
    {i j : Fin n} (hij : i ≠ j) (hi : 0 < x i * y i) (hj : 0 < x j * y j) : CondII p A B := by
  -- side `−` has a mixed axis too (orthogonality, Section 4.4)
  obtain ⟨k0, hk0⟩ : ∃ k, x k * y k < 0 := by
    by_contra hc
    push Not at hc
    have := (Finset.sum_eq_zero_iff_of_nonneg fun m _ => hc m).1 hxy i (mem_univ _)
    linarith
  have hP : ∀ m, 0 < x m * y m → tt (x m) (y m) = tt (x i) (y i) := by
    intro m hm
    by_cases hmi : m = i
    · rw [hmi]
    · exact (Hp i m k0 (Ne.symm hmi) hi hm hk0).1.symm
  have hN : ∀ m, x m * y m < 0 → tt (x m) (y m) = tt (x k0) (y k0) := by
    intro m hm
    by_cases hmk : m = k0
    · rw [hmk]
    · exact Hm m k0 i hmk hm hk0 hi
  have hτs := (Hp i j k0 hij hi hj hk0).2
  set τ := tt (x i) (y i)
  set s := tt (x k0) (y k0)
  by_cases hcase : 0 ≤ τ ∧ s ≤ 0
  · refine condII_of_signs h p hx hy hxy hw (fun m hm => ?_) (fun m hm => ?_)
    · exact abs_le_of_tt_nonneg (by rw [hP m hm]; exact hcase.1)
    · exact abs_le_of_tt_nonpos (by rw [hN m hm]; exact hcase.2)
  · have hcase' : τ ≤ 0 ∧ 0 ≤ s := by
      by_cases h0 : 0 ≤ τ
      · have hs : 0 < s := by
          by_contra hs; push Not at hs; exact hcase ⟨h0, hs⟩
        exact ⟨by nlinarith, hs.le⟩
      · push Not at h0
        exact ⟨h0.le, by nlinarith⟩
    refine condII_of_signs' h p hx hy hxy hw (fun m hm => ?_) (fun m hm => ?_)
    · exact abs_le_of_tt_nonpos (by rw [hP m hm]; exact hcase'.1)
    · exact abs_le_of_tt_nonneg (by rw [hN m hm]; exact hcase'.2)

/-- **Necessity** (Section 6): the relaxed problem is solvable ⇒ (II). -/
theorem condII_of_rectW (h : 2 ≤ n) (p : Fin n → ℝ) {A B : ℝ} (hR : RectW p A B) :
    CondII p A B := by
  classical
  obtain ⟨x0, y0, h1, h2, h3, h4⟩ := hR
  have hcont : Continuous fun z : (Fin n → ℝ) × (Fin n → ℝ) => ∑ i, |z.1 i * z.2 i| := by
    fun_prop
  obtain ⟨⟨x, y⟩, ⟨hx, hy, hxy, hw⟩, hmin⟩ :=
    (isCompact_feasSet p A B).exists_isMinOn ⟨(x0, y0), h1, h2, h3, h4⟩ hcont.continuousOn
  -- the conclusions of Lemma V for the minimizer
  have Hp : ∀ i j k, i ≠ j → 0 < x i * y i → 0 < x j * y j → x k * y k < 0 →
      tt (x i) (y i) = tt (x j) (y j) ∧ tt (x i) (y i) * tt (x k) (y k) ≤ 0 := by
    intro i j k hij hi hj hk
    by_contra hnot
    obtain ⟨x', y', h1', h2', h3', h4', hlt⟩ := lemmaV p hx hy hxy hw hij hi hj hk hnot
    have := hmin (show (x', y') ∈ feasSet p A B from ⟨h1', h2', h3', h4'⟩)
    simp only [Set.mem_ofPred_eq] at this
    linarith
  have ttneg : ∀ m, tt (x m) (-y m) = tt (x m) (y m) := fun m => by simp [tt, abs_neg]
  have Hm : ∀ i j k, i ≠ j → x i * y i < 0 → x j * y j < 0 → 0 < x k * y k →
      tt (x i) (y i) = tt (x j) (y j) ∧ tt (x i) (y i) * tt (x k) (y k) ≤ 0 := by
    intro i j k hij hi hj hk
    by_contra hnot
    rw [← ttneg i, ← ttneg j, ← ttneg k] at hnot
    obtain ⟨x', y', h1', h2', h3', h4', hlt⟩ := lemmaV p (y := fun m => -y m) hx
      (by simpa [neg_sq] using hy) (by simp [hxy]) (by simpa using hw) hij
      (by simpa using hi) (by simpa using hj) (by simpa using hk) hnot
    have := hmin (show (x', y') ∈ feasSet p A B from ⟨h1', h2', h3', h4'⟩)
    simp only [Set.mem_ofPred_eq] at this
    simp only [mul_neg, abs_neg] at hlt
    linarith
  by_cases hA : ∃ i j, i ≠ j ∧ 0 < x i * y i ∧ 0 < x j * y j
  · obtain ⟨i, j, hij, hi, hj⟩ := hA
    exact condII_of_structure h p hx hy hxy hw Hp (fun i j k a b c d => (Hm i j k a b c d).1)
      hij hi hj
  by_cases hB : ∃ i j, i ≠ j ∧ x i * y i < 0 ∧ x j * y j < 0
  · -- the same for `(x, −y)`: the sides are swapped
    obtain ⟨i, j, hij, hi, hj⟩ := hB
    refine condII_of_structure h p (y := fun m => -y m) hx (by simpa [neg_sq] using hy)
      (by simp [hxy]) (by simpa using hw) (fun a b c h1 h2 h3 h4 => ?_)
      (fun a b c h1 h2 h3 h4 => ?_) hij (by simpa using hi) (by simpa using hj)
    · simp only [ttneg]
      simp only [mul_neg, neg_pos, neg_lt_zero] at h2 h3 h4
      exact Hm a b c h1 h2 h3 h4
    · simp only [ttneg]
      simp only [mul_neg, neg_pos, neg_lt_zero] at h2 h3 h4
      exact (Hp a b c h1 h2 h3 h4).1
  -- at most one mixed axis on each side: Lemma C
  push Not at hA hB
  set M := univ.filter (fun m => x m * y m ≠ 0)
  have hMcard : M.card ≤ 2 := by
    have hsplit : M ⊆ univ.filter (fun m => 0 < x m * y m) ∪
        univ.filter (fun m => x m * y m < 0) := by
      intro m hm
      simp only [M, mem_filter, mem_univ, true_and] at hm
      rcases hm.lt_or_gt with h' | h'
      · exact mem_union_right _ (by simp [h'])
      · exact mem_union_left _ (by simp [h'])
    have c1 : (univ.filter (fun m => 0 < x m * y m)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [mem_filter, mem_univ, true_and] at ha hb
      by_contra hab
      exact absurd hb (not_lt.2 (hA a b hab ha))
    have c2 : (univ.filter (fun m => x m * y m < 0)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [mem_filter, mem_univ, true_and] at ha hb
      by_contra hab
      exact absurd hb (not_lt.2 (hB a b hab ha))
    calc M.card ≤ _ := card_le_card hsplit
      _ ≤ _ := card_union_le _ _
      _ ≤ 2 := by omega
  obtain ⟨t, hMt, htcard⟩ := Finset.exists_superset_card_eq hMcard (by simpa using h)
  obtain ⟨k, l, hkl, rfl⟩ := Finset.card_eq_two.1 htcard
  refine condII_of_mixed_subset p hx hy hxy hw hkl fun m hmk hml => ?_
  by_contra hne
  have hne' : x m * y m ≠ 0 := hne
  have : m ∈ ({k, l} : Finset (Fin n)) := hMt (by
    simp only [M, mem_filter, mem_univ, true_and]; exact hne')
  simp only [mem_insert, mem_singleton] at this
  rcases this with h' | h'
  · exact hmk h'
  · exact hml h'

/-- **The theorem on a rectangle in an `n`-box** (the paper, Section 2).
For `n ≥ 2`, `p ≥ 0`, `A, B ≥ 0`: the rectangle `A × B` (the box `(A, B, 0, …, 0)`)
fits into the box `p` ⇔ **(II)**. -/
theorem fitsN_rect_iff_condII (h : 2 ≤ n) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) : FitsN p (pad h ![A, B]) ↔ CondII p A B := by
  rw [fitsN_rect_iff_rectW h p hA hB]
  exact ⟨condII_of_rectW h p, rectW_of_condII p hp⟩

/-- (I) is a sufficient condition (Section 7). -/
theorem fitsN_rect_of_condI (h : 2 ≤ n) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hI : CondI p A B) : FitsN p (pad h ![A, B]) :=
  (fitsN_rect_iff_condII h p hp hA hB).2 (condII_of_condI h p hp hI)

end RectInNBox
