import Mathlib

/-!
# Lemma 1 (strip): a rectangle in a strip

A `u × v` rectangle is put into the strip `{0 ≤ x ≤ s}` of the plane; `(c, d) = (cos θ, sin θ)` is
the direction of its side `u`. Then its extent across the strip is `u c + v d` and its extent along
the strip is `u d + v c`.

* `strip_exists` — if `min u v ≤ s` (`stripOK`), some direction gives extent across `≤ s` and extent
  along `≤ stripH u v s` (explicit formula);
* `strip_min` — conversely, any direction with extent across `≤ s` has extent along `≥ stripH u v s`.

These lemmas are taken verbatim from the three-dimensional formalization
(`box-in-box`, files `Statement.lean` and `ZeroEntry.lean`); here they give Carver's plane criterion
(`RectCarver.lean`).
-/

namespace RectInNBox

open Real

/-- A `u × v` rectangle can be put into a strip of width `s`: its shorter side is not wider than
the strip. -/
def stripOK (u v s : ℝ) : Prop := min u v ≤ s

/-- The least extent along a strip of width `s` of a `u × v` rectangle placed in the strip
(the formula of Lemma 1; meaningful when `stripOK u v s`). With `x = max u v`, `y = min u v`. -/
noncomputable def stripH (u v s : ℝ) : ℝ :=
  let x := max u v
  let y := min u v
  if x ≤ s then y
  else min x ((2 * x * y * s + (x ^ 2 - y ^ 2) * √(x ^ 2 + y ^ 2 - s ^ 2)) / (x ^ 2 + y ^ 2))

/-- Lemma 1 (strip) for `y ≤ x`: the rotation `(c, d) = (cos θ, sin θ)` puts the `x × y` rectangle
into the strip of width `s` (`x c + y d ≤ s`), and its extent along the strip (`x d + y c`) is at most
`stripH`. For `x > s` the angle is explicit:
`c = (x s − y √(x²+y²−s²))/(x²+y²)`, `d = (y s + x √(x²+y²−s²))/(x²+y²)`. -/
lemma strip_aux {x y s : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hs : 0 ≤ s) (hys : y ≤ s) :
    ∃ c d : ℝ, 0 ≤ c ∧ 0 ≤ d ∧ c ^ 2 + d ^ 2 = 1 ∧ x * c + y * d ≤ s ∧
      x * d + y * c ≤ (if x ≤ s then y
        else min x ((2 * x * y * s + (x ^ 2 - y ^ 2) * √(x ^ 2 + y ^ 2 - s ^ 2)) / (x ^ 2 + y ^ 2))) := by
  split_ifs with hxs
  · exact ⟨1, 0, by norm_num, le_refl _, by norm_num, by simpa using hxs, by simp⟩
  push Not at hxs
  set T := (2 * x * y * s + (x ^ 2 - y ^ 2) * √(x ^ 2 + y ^ 2 - s ^ 2)) / (x ^ 2 + y ^ 2) with hT
  rcases le_total x T with hxT | hTx
  · -- lying on its side: height `y`, extent `x` along the strip
    rw [min_eq_left hxT]
    exact ⟨0, 1, le_refl _, by norm_num, by norm_num, by simpa using hys, by simp⟩
  rw [min_eq_right hTx]
  have hx : 0 < x := lt_of_le_of_lt hs hxs
  have hr : 0 < x ^ 2 + y ^ 2 := by positivity
  set R := √(x ^ 2 + y ^ 2 - s ^ 2) with hRdef
  have hR0 : 0 ≤ R := sqrt_nonneg _
  have hR2 : R ^ 2 = x ^ 2 + y ^ 2 - s ^ 2 := sq_sqrt (by nlinarith)
  have hyR : y * R ≤ x * s := by
    by_contra hlt
    push Not at hlt
    have := mul_self_lt_mul_self (by positivity) hlt
    nlinarith [mul_nonneg hr.le (sq_nonneg y), mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hy hys 2) hr.le]
  refine ⟨(x * s - y * R) / (x ^ 2 + y ^ 2), (y * s + x * R) / (x ^ 2 + y ^ 2),
    div_nonneg (by linarith) hr.le, div_nonneg (by positivity) hr.le, ?_, ?_, ?_⟩
  · rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (by positivity)]
    linear_combination (x ^ 2 + y ^ 2) * hR2
  · rw [mul_div_assoc', mul_div_assoc', ← add_div, div_le_iff₀ hr]
    nlinarith
  · rw [hT, mul_div_assoc', mul_div_assoc', ← add_div]
    exact le_of_eq (by ring)

/-- Lemma 1 (strip), general form. -/
lemma strip_exists {u v s : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 ≤ s) (h : stripOK u v s) :
    ∃ c d : ℝ, 0 ≤ c ∧ 0 ≤ d ∧ c ^ 2 + d ^ 2 = 1 ∧ u * c + v * d ≤ s ∧
      u * d + v * c ≤ stripH u v s := by
  unfold stripOK at h
  simp only [stripH]
  rcases le_total v u with huv | huv
  · rw [max_eq_left huv, min_eq_right huv] at *
    exact strip_aux hv huv hs h
  · rw [max_eq_right huv, min_eq_left huv] at *
    obtain ⟨c, d, hc, hd, h1, h2, h3⟩ := strip_aux hu huv hs h
    exact ⟨d, c, hd, hc, by linarith, by linarith, by linarith⟩

/-- Core of minimality: a point `(A, E)` of the circle of radius `r = √(x²+y²)` with
`y ≤ A ≤ s`, `E ≥ 0` lies above the chord between `(y, x)` and `(s, R)`, `R = √(r² − s²)`; hence
`B = (2xyA + (x²−y²)E)/r² ≥ min(x, T)`, where `T` is the value of `B` at `A = s`. -/
lemma chord_core {x y s A E B R : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hx : 0 < x) (hs : 0 ≤ s)
    (hyA : y ≤ A) (hAs : A ≤ s) (hE0 : 0 ≤ E) (hR0 : 0 ≤ R)
    (hAE : A ^ 2 + E ^ 2 = x ^ 2 + y ^ 2) (hBid : (x ^ 2 + y ^ 2) * B = 2 * x * y * A + (x ^ 2 - y ^ 2) * E)
    (hR2 : R ^ 2 = x ^ 2 + y ^ 2 - s ^ 2) :
    min x ((2 * x * y * s + (x ^ 2 - y ^ 2) * R) / (x ^ 2 + y ^ 2)) ≤ B := by
  obtain ⟨r2, hr2⟩ : ∃ r2, r2 = x ^ 2 + y ^ 2 := ⟨_, rfl⟩
  rw [← hr2] at hAE hBid hR2 ⊢
  have hr : 0 < r2 := by rw [hr2]; positivity
  obtain ⟨T, hT⟩ : ∃ T, T = (2 * x * y * s + (x ^ 2 - y ^ 2) * R) / r2 := ⟨_, rfl⟩
  rw [← hT]
  have hTr : T * r2 = 2 * x * y * s + (x ^ 2 - y ^ 2) * R := by rw [hT]; exact div_mul_cancel₀ _ hr.ne'
  have hxy2 : 0 ≤ x ^ 2 - y ^ 2 := by nlinarith
  have hA0 : 0 ≤ A := le_trans hy hyA
  -- `E ≥ R` because `A ≤ s`
  have hER : R ≤ E := by
    refine (sq_le_sq₀ hR0 hE0).1 ?_
    nlinarith [mul_le_mul hAs hAs hA0 hs]
  obtain ⟨a, ha⟩ : ∃ a, a = s - A := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = A - y := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hb0 : 0 ≤ b := by rw [hb]; linarith
  rcases eq_or_lt_of_le (add_nonneg ha0 hb0) with hD | hD
  · -- `A = s`: then `B ≥ T`
    have hAs' : A = s := by linarith
    refine le_trans (min_le_right _ _) ?_
    have h1 : T * r2 ≤ B * r2 := by
      rw [hTr, mul_comm B, hBid, hAs']
      linarith [mul_le_mul_of_nonneg_left hER hxy2]
    exact le_of_mul_le_mul_right h1 hr
  -- the chord: `(a+b) E ≥ a x + b R`
  obtain ⟨D, hDdef⟩ : ∃ D, D = a + b := ⟨_, rfl⟩
  rw [← hDdef] at hD
  have hDA : D * A = a * y + b * s := by rw [hDdef, ha, hb]; ring
  have hCS0 : 0 ≤ y * s + x * R := add_nonneg (mul_nonneg hy hs) (mul_nonneg hx.le hR0)
  have hCS : y * s + x * R ≤ r2 := by
    have e : r2 ^ 2 - (y * s + x * R) ^ 2 = (y * R - x * s) ^ 2 := by
      linear_combination (-(x ^ 2 + y ^ 2)) * hR2 + (r2 - x ^ 2 - y ^ 2 + x ^ 2 + y ^ 2) * hr2
    exact (sq_le_sq₀ hCS0 hr.le).1 (by linarith [e, sq_nonneg (y * R - x * s)])
  have hL : (a * x + b * R) ^ 2 ≤ (D * E) ^ 2 := by
    have hab : 0 ≤ 2 * (a * b) := by positivity
    have e2 : (a * y + b * s) ^ 2 + (a * x + b * R) ^ 2 = (a ^ 2 + b ^ 2) * r2 + 2 * (a * b) * (y * s + x * R) := by
      linear_combination b ^ 2 * hR2 - a ^ 2 * hr2
    have e3 : D ^ 2 * r2 = (a ^ 2 + b ^ 2) * r2 + 2 * (a * b) * r2 := by rw [hDdef]; ring
    have hDE : (D * E) ^ 2 = D ^ 2 * r2 - (D * A) ^ 2 := by
      have : E ^ 2 = r2 - A ^ 2 := by linarith
      rw [mul_pow, mul_pow, this]; ring
    rw [hDE, hDA]
    linarith [mul_le_mul_of_nonneg_left hCS hab]
  have hchord : a * x + b * R ≤ D * E :=
    (sq_le_sq₀ (add_nonneg (mul_nonneg ha0 hx.le) (mul_nonneg hb0 hR0))
      (mul_nonneg hD.le hE0)).1 hL
  have hm1 : min x T ≤ x := min_le_left _ _
  have hm2 : min x T ≤ T := min_le_right _ _
  have key : (a * x + b * T) * r2 ≤ D * B * r2 := by
    have e1 : D * B * r2 = 2 * x * y * (D * A) + (x ^ 2 - y ^ 2) * (D * E) := by
      rw [mul_assoc, mul_comm B, hBid]; ring
    have e2 : (a * x + b * T) * r2 = a * x * r2 + b * (T * r2) := by ring
    have e4 : a * x * r2 = a * (2 * x * y * y + (x ^ 2 - y ^ 2) * x) := by rw [hr2]; ring
    rw [e1, e2, hTr, hDA, e4]
    nlinarith [mul_le_mul_of_nonneg_left hchord hxy2]
  have key' : a * x + b * T ≤ D * B := le_of_mul_le_mul_right key hr
  have : D * min x T ≤ D * B := by
    have e : D * min x T = a * min x T + b * min x T := by rw [hDdef]; ring
    linarith [mul_le_mul_of_nonneg_left hm1 ha0, mul_le_mul_of_nonneg_left hm2 hb0]
  exact le_of_mul_le_mul_left this hD

/-- Lemma 1, minimality, for `y ≤ x`. -/
lemma strip_min_aux {x y s c d : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hs : 0 ≤ s)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c ^ 2 + d ^ 2 = 1) (h : x * c + y * d ≤ s) :
    y ≤ s ∧ (if x ≤ s then y
        else min x ((2 * x * y * s + (x ^ 2 - y ^ 2) * √(x ^ 2 + y ^ 2 - s ^ 2)) / (x ^ 2 + y ^ 2)))
      ≤ x * d + y * c := by
  have hcd1 : 1 ≤ c + d := by nlinarith [mul_nonneg hc hd]
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg d]
  have hyA : y ≤ x * c + y * d := by nlinarith [mul_le_mul_of_nonneg_right hyx hc]
  refine ⟨le_trans hyA h, ?_⟩
  split_ifs with hxs
  · nlinarith [mul_le_mul_of_nonneg_right hyx hd]
  push Not at hxs
  have hx : 0 < x := lt_of_le_of_lt hs hxs
  have hA0 : 0 ≤ x * c + y * d := le_trans hy hyA
  have hAE : (x * c + y * d) ^ 2 + (x * d - y * c) ^ 2 = x ^ 2 + y ^ 2 := by
    linear_combination (x ^ 2 + y ^ 2) * hcd
  -- `E ≥ 0`: otherwise `A ≥ x > s`
  have hE0 : 0 ≤ x * d - y * c := by
    by_contra hneg
    push Not at hneg
    have h1 : y * c - x * d ≤ y := by nlinarith [mul_nonneg hx.le hd, mul_le_mul_of_nonneg_left hc1 hy]
    have h1' : 0 ≤ y * c - x * d := by linarith
    have h2 : x ^ 2 ≤ (x * c + y * d) ^ 2 := by nlinarith [mul_le_mul h1 h1 h1' hy]
    have h3 : x ≤ x * c + y * d := (sq_le_sq₀ hx.le hA0).1 h2
    linarith
  exact chord_core hy hyx hx hs hyA h hE0 (sqrt_nonneg _) hAE (by ring)
    (sq_sqrt (by nlinarith))

/-- Lemma 1, minimality: if the `u × v` rectangle with direction `(c, d)` stands in the strip of
width `s`, then `stripOK` holds and its extent along the strip is at least `stripH`. -/
lemma strip_min {u v s c d : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 ≤ s)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hcd : c ^ 2 + d ^ 2 = 1) (h : u * c + v * d ≤ s) :
    stripOK u v s ∧ stripH u v s ≤ u * d + v * c := by
  unfold stripOK
  simp only [stripH]
  rcases le_total v u with huv | huv
  · rw [max_eq_left huv, min_eq_right huv]
    exact strip_min_aux hv huv hs hc hd hcd h
  · rw [max_eq_right huv, min_eq_left huv]
    have := strip_min_aux hu huv hs hd hc (by linarith) (by linarith)
    exact ⟨this.1, by linarith [this.2]⟩

end RectInNBox
