import RectInNBox.RectMain
import RectInNBox.Strip

/-!
# The explicit plane criterion (Carver) and the explicit form of the main theorem

* `Rot2 a b X Y` — the rectangle `a × b` rotated by the angle with `(cos θ, sin θ) = (c, d)`, `c, d ≥ 0`,
  has widths `a c + b d ≤ X`, `a d + b c ≤ Y`;
* `fits2_iff_rot2` — `FitsN ![X, Y] ![a, b] ↔ Rot2 a b X Y` (from `fitsN_rect_iff`);
* `CarverS` — Carver's criterion (the paper, Section 2) for sorted sides
  (`X ≥ Y`, `a ≥ b`), with division; `Carver` — the same after sorting by `max`/`min`;
* `CarverPolyS`, `CarverPoly` — the same condition without division: instead of
  `((X+Y)/(a+b))² + ((X−Y)/(a−b))² ≥ 2` it reads `(a²−b²)² ≤ (a²+b²)(X²+Y²) − 4abXY`;
* `fits2_iff_carver` — the plane criterion (in Carver's form with division, as in the literature);
  `carver_iff_carverPoly` — the equivalent form without division, on which the proof rests;
* `fitsN_rect_iff_explicit` — the main theorem with `Carver` instead of `FitsN` in `ℝ²`.

The proof of the plane criterion uses Lemma 1 on a strip (`Strip.lean`: `strip_exists` — sufficiency,
`strip_min` — necessity): for `a > X` the optimal position touches the strip of width `X`, and
it remains to compare `stripH a b X` with `Y` — pure algebra (`carver_T_le_iff`).
-/

namespace RectInNBox

open Finset Real

variable {n : ℕ}

/-! ## Definitions -/

/-- The rectangle `a × b` with direction `(c, d)` (`c, d ≥ 0`, `c² + d² = 1`) has widths
`a c + b d ≤ X` along the first axis and `a d + b c ≤ Y` along the second. -/
def Rot2 (a b X Y : ℝ) : Prop :=
  ∃ c d : ℝ, 0 ≤ c ∧ 0 ≤ d ∧ c ^ 2 + d ^ 2 = 1 ∧ a * c + b * d ≤ X ∧ a * d + b * c ≤ Y

/-- **Carver's criterion** for sorted sides (`X ≥ Y` — the box, `a ≥ b` — the rectangle),
verbatim as in the paper (Section 2): (i) `a ≤ X ∧ b ≤ Y`, or (ii) `a > X`, `b ≤ Y` and
`((X+Y)/(a+b))² + ((X−Y)/(a−b))² ≥ 2`.
It is assumed that `a ≥ b ≥ 0`, `X ≥ Y ≥ 0`; the definition itself does not check this — the order is ensured by
`Carver` (sorting by `max`/`min`), nonnegativity by the hypotheses of the theorems. Under these conditions branch (ii)
has `a > X ≥ Y ≥ b ≥ 0`, so `a ± b > 0` and there is no division by zero. -/
def CarverS (a b X Y : ℝ) : Prop :=
  (a ≤ X ∧ b ≤ Y) ∨
    (X < a ∧ b ≤ Y ∧ 2 ≤ ((X + Y) / (a + b)) ^ 2 + ((X - Y) / (a - b)) ^ 2)

/-- **Carver(a, b; X, Y)**: Carver's criterion after sorting both pairs in decreasing order. -/
def Carver (a b X Y : ℝ) : Prop := CarverS (max a b) (min a b) (max X Y) (min X Y)

/-- Carver's criterion without division (sorted sides). -/
def CarverPolyS (a b X Y : ℝ) : Prop :=
  (a ≤ X ∧ b ≤ Y) ∨
    (X < a ∧ b ≤ Y ∧ (a ^ 2 - b ^ 2) ^ 2 ≤ (a ^ 2 + b ^ 2) * (X ^ 2 + Y ^ 2) - 4 * a * b * X * Y)

/-- Carver's criterion without division, after sorting. -/
def CarverPoly (a b X Y : ℝ) : Prop := CarverPolyS (max a b) (min a b) (max X Y) (min X Y)

/-! ## `FitsN` in `ℝ²` ⇔ `Rot2` -/

lemma fits2_iff_rot2 (X Y : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    FitsN ![X, Y] ![a, b] ↔ Rot2 a b X Y := by
  have e := fitsN_rect_iff (le_refl 2) ![X, Y] ha hb
  rw [pad_refl] at e
  rw [e]
  simp only [Fin.sum_univ_two, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨u, v, hu, hv, huv, h0, h1⟩
    have hsq : (u 0 * v 0) ^ 2 = (u 1 * v 1) ^ 2 := by
      rw [show u 0 * v 0 = -(u 1 * v 1) by linarith]; ring
    have e0 : v 0 ^ 2 = u 1 ^ 2 := by
      linear_combination hsq - v 0 ^ 2 * hu + u 1 ^ 2 * hv
    have e1 : v 1 ^ 2 = u 0 ^ 2 := by
      linear_combination -hsq - v 1 ^ 2 * hu + u 0 ^ 2 * hv
    rw [(sq_eq_sq_iff_abs_eq_abs _ _).1 e0] at h0
    rw [(sq_eq_sq_iff_abs_eq_abs _ _).1 e1] at h1
    exact ⟨|u 0|, |u 1|, abs_nonneg _, abs_nonneg _, by rw [sq_abs, sq_abs]; exact hu, h0,
      by linarith⟩
  · rintro ⟨c, d, hc, hd, hcd, h0, h1⟩
    refine ⟨![c, d], ![d, -c], ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hcd
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; linear_combination hcd
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; ring
    · simp only [Matrix.cons_val_zero, abs_of_nonneg hc, abs_of_nonneg hd]
      exact h0
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, abs_neg, abs_of_nonneg hc,
        abs_of_nonneg hd]
      linarith

/-! ## Symmetries of `Rot2` -/

lemma rot2_swap_ab {a b X Y : ℝ} (h : Rot2 a b X Y) : Rot2 b a X Y := by
  obtain ⟨c, d, hc, hd, hcd, h0, h1⟩ := h
  exact ⟨d, c, hd, hc, by linarith, by linarith, by linarith⟩

lemma rot2_swap_XY {a b X Y : ℝ} (h : Rot2 a b X Y) : Rot2 a b Y X := by
  obtain ⟨c, d, hc, hd, hcd, h0, h1⟩ := h
  exact ⟨d, c, hd, hc, by linarith, by linarith, by linarith⟩

lemma rot2_sort (a b X Y : ℝ) :
    Rot2 a b X Y ↔ Rot2 (max a b) (min a b) (max X Y) (min X Y) := by
  have hab : Rot2 a b X Y ↔ Rot2 b a X Y := ⟨rot2_swap_ab, rot2_swap_ab⟩
  have hXY : ∀ a b, Rot2 a b X Y ↔ Rot2 a b Y X := fun _ _ => ⟨rot2_swap_XY, rot2_swap_XY⟩
  rcases le_total b a with h1 | h1 <;> rcases le_total Y X with h2 | h2
  · rw [max_eq_left h1, min_eq_right h1, max_eq_left h2, min_eq_right h2]
  · rw [max_eq_left h1, min_eq_right h1, max_eq_right h2, min_eq_left h2, hXY]
  · rw [max_eq_right h1, min_eq_left h1, max_eq_left h2, min_eq_right h2, hab]
  · rw [max_eq_right h1, min_eq_left h1, max_eq_right h2, min_eq_left h2, hab, hXY]

/-! ## Algebra -/

/-- The form with division ⇔ the form without division (for `a + b > 0`, `a − b > 0`). -/
lemma carver_div_iff {a b X Y : ℝ} (hs : 0 < a + b) (ht : 0 < a - b) :
    2 ≤ ((X + Y) / (a + b)) ^ 2 + ((X - Y) / (a - b)) ^ 2 ↔
      (a ^ 2 - b ^ 2) ^ 2 ≤ (a ^ 2 + b ^ 2) * (X ^ 2 + Y ^ 2) - 4 * a * b * X * Y := by
  rw [div_pow, div_pow, div_add_div _ _ (pow_pos hs 2).ne' (pow_pos ht 2).ne',
    le_div_iff₀ (mul_pos (pow_pos hs 2) (pow_pos ht 2))]
  have e : (X + Y) ^ 2 * (a - b) ^ 2 + (a + b) ^ 2 * (X - Y) ^ 2 - 2 * ((a + b) ^ 2 * (a - b) ^ 2) =
      2 * ((a ^ 2 + b ^ 2) * (X ^ 2 + Y ^ 2) - 4 * a * b * X * Y - (a ^ 2 - b ^ 2) ^ 2) := by ring
  constructor <;> intro h <;> linarith

lemma carverS_iff_polyS {a b X Y : ℝ} (hb : 0 ≤ b) (hYX : Y ≤ X) :
    CarverS a b X Y ↔ CarverPolyS a b X Y := by
  unfold CarverS CarverPolyS
  exact or_congr Iff.rfl (and_congr_right fun h1 => and_congr_right fun h2 =>
    carver_div_iff (by linarith) (by linarith))

/-- Carver's condition without division (in case (ii)) implies `2abX ≤ Y(a²+b²)`. -/
lemma carver_aux {a b X Y : ℝ} (hb : 0 ≤ b) (hbY : b ≤ Y) (hYX : Y ≤ X) (hXa : X < a)
    (hK : (a ^ 2 - b ^ 2) ^ 2 ≤ (a ^ 2 + b ^ 2) * (X ^ 2 + Y ^ 2) - 4 * a * b * X * Y) :
    2 * a * b * X ≤ Y * (a ^ 2 + b ^ 2) := by
  have ha : 0 < a := by linarith
  have hN : 0 < a ^ 2 + b ^ 2 := by positivity
  by_contra hlt
  push Not at hlt
  have hb0 : 0 < b := by
    rcases eq_or_lt_of_le hb with h | h
    · subst h; nlinarith [mul_nonneg (hb.trans hbY) hN.le]
    · exact h
  -- `a² + b² < 2aX`
  have h2aX : a ^ 2 + b ^ 2 < 2 * a * X := by
    have : b * (a ^ 2 + b ^ 2) < b * (2 * a * X) := by
      nlinarith [mul_le_mul_of_nonneg_right hbY hN.le]
    exact lt_of_mul_lt_mul_left this hb0.le
  set F := (a ^ 2 + b ^ 2) * X - a * (3 * b ^ 2 - a ^ 2) with hF
  have hF0 : 0 < F := by
    have hprod : 0 ≤ (3 * a ^ 2 - b ^ 2) * (a ^ 2 - b ^ 2) :=
      mul_nonneg (by nlinarith) (by nlinarith)
    have h1 := mul_lt_mul_of_pos_left h2aX hN
    have h2 : 0 < 2 * a * F := by rw [hF]; nlinarith
    by_contra h3
    push Not at h3
    nlinarith [mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 2 * a)]
  set G := (a ^ 2 + b ^ 2) * (Y + b) - 4 * a * b * X with hG
  have hG0 : G ≤ 0 := by
    rw [hG]; nlinarith [mul_le_mul_of_nonneg_left hbY hN.le]
  have e : (a ^ 2 + b ^ 2) * (X ^ 2 + Y ^ 2) - 4 * a * b * X * Y - (a ^ 2 - b ^ 2) ^ 2 =
      (X - a) * F + (Y - b) * G := by rw [hF, hG]; ring
  have h1 : (X - a) * F < 0 := mul_neg_of_neg_of_pos (by linarith) hF0
  have h2 : (Y - b) * G ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hG0
  linarith

/-- The key comparison: for `a > X ≥ Y ≥ b ≥ 0` the extent `T` of Lemma 1 (`stripH` for `a > X`)
is at most `Y` ⇔ Carver's condition without division. -/
lemma carver_T_le_iff {a b X Y : ℝ} (hb : 0 ≤ b) (hbY : b ≤ Y) (hYX : Y ≤ X) (hXa : X < a) :
    (2 * a * b * X + (a ^ 2 - b ^ 2) * √(a ^ 2 + b ^ 2 - X ^ 2)) / (a ^ 2 + b ^ 2) ≤ Y ↔
      (a ^ 2 - b ^ 2) ^ 2 ≤ (a ^ 2 + b ^ 2) * (X ^ 2 + Y ^ 2) - 4 * a * b * X * Y := by
  have hY : 0 ≤ Y := hb.trans hbY
  have hX : 0 ≤ X := hY.trans hYX
  have ha : 0 < a := by linarith
  have hN : 0 < a ^ 2 + b ^ 2 := by positivity
  have hD : 0 ≤ a ^ 2 - b ^ 2 := by nlinarith
  rw [div_le_iff₀ hN]
  set R := √(a ^ 2 + b ^ 2 - X ^ 2) with hRdef
  have hR0 : 0 ≤ R := sqrt_nonneg _
  have hR2 : R ^ 2 = a ^ 2 + b ^ 2 - X ^ 2 := sq_sqrt (by nlinarith)
  have hDR : 0 ≤ (a ^ 2 - b ^ 2) * R := mul_nonneg hD hR0
  have key : (a ^ 2 + b ^ 2) *
      ((a ^ 2 + b ^ 2) * (X ^ 2 + Y ^ 2) - 4 * a * b * X * Y - (a ^ 2 - b ^ 2) ^ 2) =
      (Y * (a ^ 2 + b ^ 2) - 2 * a * b * X) ^ 2 - ((a ^ 2 - b ^ 2) * R) ^ 2 := by
    linear_combination (a ^ 2 - b ^ 2) ^ 2 * hR2
  constructor
  · intro h
    have h1 : (a ^ 2 - b ^ 2) * R ≤ Y * (a ^ 2 + b ^ 2) - 2 * a * b * X := by linarith
    have h2 := pow_le_pow_left₀ hDR h1 2
    have h3 : 0 ≤ (a ^ 2 + b ^ 2) *
        ((a ^ 2 + b ^ 2) * (X ^ 2 + Y ^ 2) - 4 * a * b * X * Y - (a ^ 2 - b ^ 2) ^ 2) := by
      rw [key]; linarith
    by_contra h4
    push Not at h4
    nlinarith
  · intro hK
    have hM : 0 ≤ Y * (a ^ 2 + b ^ 2) - 2 * a * b * X := by
      linarith [carver_aux hb hbY hYX hXa hK]
    have h3 : 0 ≤ (a ^ 2 + b ^ 2) *
        ((a ^ 2 + b ^ 2) * (X ^ 2 + Y ^ 2) - 4 * a * b * X * Y - (a ^ 2 - b ^ 2) ^ 2) :=
      mul_nonneg hN.le (by linarith)
    have h1 : ((a ^ 2 - b ^ 2) * R) ^ 2 ≤ (Y * (a ^ 2 + b ^ 2) - 2 * a * b * X) ^ 2 := by
      linarith
    have h2 := (sq_le_sq₀ hDR hM).1 h1
    linarith

/-! ## The plane criterion -/

/-- The sorted case: `Rot2 ⇔ CarverPolyS`. -/
lemma rot2_iff_carverPolyS {a b X Y : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (hY : 0 ≤ Y) (hYX : Y ≤ X) :
    Rot2 a b X Y ↔ CarverPolyS a b X Y := by
  have hX : 0 ≤ X := hY.trans hYX
  have ha : 0 ≤ a := hb.trans hab
  constructor
  · rintro ⟨c, d, hc, hd, hcd, h0, h1⟩
    have hcd1 : 1 ≤ c + d := by nlinarith [mul_nonneg hc hd]
    have hbY : b ≤ Y := by
      nlinarith [mul_le_mul_of_nonneg_right hab hd, mul_nonneg hb (by linarith : (0 : ℝ) ≤ c + d - 1)]
    rcases le_or_gt a X with haX | haX
    · exact Or.inl ⟨haX, hbY⟩
    refine Or.inr ⟨haX, hbY, ?_⟩
    obtain ⟨-, hH⟩ := strip_min ha hb hX hc hd hcd h0
    simp only [stripH] at hH
    simp only [max_eq_left hab, min_eq_right hab, not_le.2 haX, ↓reduceIte] at hH
    rcases min_le_iff.1 (hH.trans h1) with h | h
    · linarith
    · exact (carver_T_le_iff hb hbY hYX haX).1 h
  · rintro (⟨haX, hbY⟩ | ⟨haX, hbY, hK⟩)
    · exact ⟨1, 0, by norm_num, le_refl _, by norm_num, by linarith, by linarith⟩
    have hT := (carver_T_le_iff hb hbY hYX haX).2 hK
    have hOK : stripOK a b X := by
      unfold stripOK; rw [min_eq_right hab]; linarith
    obtain ⟨c, d, hc, hd, hcd, h0, h1⟩ := strip_exists ha hb hX hOK
    refine ⟨c, d, hc, hd, hcd, h0, h1.trans ?_⟩
    simp only [stripH]
    simp only [max_eq_left hab, min_eq_right hab, not_le.2 haX, ↓reduceIte]
    exact min_le_of_right_le hT

/-- Carver's forms with and without division agree. -/
lemma carver_iff_carverPoly {a b X Y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Carver a b X Y ↔ CarverPoly a b X Y :=
  carverS_iff_polyS (le_min ha hb) min_le_max

/-- **Carver's plane criterion**: the rectangle `a × b` fits into the rectangle `X × Y`
⇔ `Carver a b X Y` (the paper, Section 2). -/
theorem fits2_iff_carver {X Y a b : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    FitsN ![X, Y] ![a, b] ↔ Carver a b X Y := by
  rw [carver_iff_carverPoly ha hb, fits2_iff_rot2 X Y ha hb, rot2_sort, CarverPoly]
  exact rot2_iff_carverPolyS (le_min ha hb) min_le_max (le_min hX hY) min_le_max

/-! ## The main theorem in explicit form -/

/-- **Theorem (explicit form).** The rectangle `A × B` fits into the `n`-box `p` ⇔ there are
`k ≠ l` and a partition `S ⊔ T = [n] ∖ {k, l}` for which Carver's criterion
`Carver(√(A² − ‖p_S‖²)₊, √(B² − ‖p_T‖²)₊; p_k, p_l)` holds. -/
theorem fitsN_rect_iff_explicit (h : 2 ≤ n) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    FitsN p (pad h ![A, B]) ↔
      ∃ k l : Fin n, k ≠ l ∧ ∃ S T : Finset (Fin n), Disjoint S T ∧ S ∪ T = univ \ {k, l} ∧
        Carver (√(A ^ 2 - ∑ i ∈ S, p i ^ 2)) (√(B ^ 2 - ∑ i ∈ T, p i ^ 2)) (p k) (p l) := by
  rw [fitsN_rect_iff_condII h p hp hA hB, CondII]
  exact exists_congr fun k => exists_congr fun l => and_congr_right fun _ =>
    exists_congr fun S => exists_congr fun T => and_congr_right fun _ => and_congr_right fun _ =>
      fits2_iff_carver (hp k) (hp l) (sqrt_nonneg _) (sqrt_nonneg _)

end RectInNBox
