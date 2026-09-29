import Mathlib

/-!
# Lemma V (Section 5), the real core: moving along the curve "line ∩ ellipse"

The paper, Section 5, Lemma V. Three mixed axes `i, j` (one side) and `k`
(the other side) with weights `Pᵢ, Pⱼ, P_k > 0` and parameters `tᵢ, tⱼ, s₀ ∈ (−1, 1)`. We look for new
`X, Y, s ∈ [−1, 1]` preserving
`PᵢX + PⱼY + P_k s = Pᵢtᵢ + Pⱼtⱼ + P_k s₀` (that is, `L`) and
`PᵢX² + PⱼY² − P_k s² = Pᵢtᵢ² + Pⱼtⱼ² − P_k s₀²` (that is, `Def₊ − Def₋`),
with `s² > s₀²` strictly (that is, `D` strictly decreases).

Instead of the implicit function theorem, an explicit solution: the line `PᵢX + PⱼY = λ(s)` is parametrized by
`X = τ + Pⱼθ`, `Y = τ − Pᵢθ`, `τ = λ/(Pᵢ+Pⱼ)`, and then `PᵢX² + PⱼY² = (Pᵢ+Pⱼ)τ² + PᵢPⱼ(Pᵢ+Pⱼ)θ²`,
whence `θ(s) = σ·√(h(s)/(PᵢPⱼ(Pᵢ+Pⱼ)))`, `h(s) = μ(s) − (Pᵢ+Pⱼ)τ(s)²`. The functions `X(s)`, `Y(s)`
are continuous and equal `(tᵢ, tⱼ)` at `s = s₀`; it only remains to get `h(s) ≥ 0` for `s` slightly farther from zero:
in case (a) `tᵢ ≠ tⱼ` this is `h(s₀) > 0` and continuity, in case (b) `tᵢ = tⱼ`, `tᵢ s₀ > 0` —
an explicit expansion of `h` at `s₀`.
-/

namespace RectInNBox

open Filter Topology

/-- The core of Lemma V for `s₀ ≥ 0` (moving to the right). -/
lemma lemmaV_core_nonneg {Pi Pj Pk ti tj s0 : ℝ} (hPi : 0 < Pi) (hPj : 0 < Pj) (hPk : 0 < Pk)
    (hti : |ti| < 1) (htj : |tj| < 1) (hs0 : |s0| < 1) (hs0n : 0 ≤ s0)
    (hnot : ¬ (ti = tj ∧ ti * s0 ≤ 0)) :
    ∃ X Y s : ℝ, |X| ≤ 1 ∧ |Y| ≤ 1 ∧ |s| ≤ 1 ∧ s0 ^ 2 < s ^ 2 ∧
      Pi * X + Pj * Y + Pk * s = Pi * ti + Pj * tj + Pk * s0 ∧
      Pi * X ^ 2 + Pj * Y ^ 2 - Pk * s ^ 2 = Pi * ti ^ 2 + Pj * tj ^ 2 - Pk * s0 ^ 2 := by
  have hQ : 0 < Pi + Pj := by linarith
  have hc : 0 < Pi * Pj * (Pi + Pj) := by positivity
  obtain ⟨σ, hσ2, hσθ⟩ : ∃ σ : ℝ, σ ^ 2 = 1 ∧ σ * |(ti - tj) / (Pi + Pj)| = (ti - tj) / (Pi + Pj) := by
    by_cases h : 0 ≤ (ti - tj) / (Pi + Pj)
    · exact ⟨1, by norm_num, by rw [abs_of_nonneg h, one_mul]⟩
    · exact ⟨-1, by norm_num, by rw [abs_of_neg (not_le.1 h)]; ring⟩
  -- τ, h, θ, X, Y
  obtain ⟨τ, hτd⟩ : ∃ τ : ℝ → ℝ,
      τ = fun s => (Pi * ti + Pj * tj + Pk * s0 - Pk * s) / (Pi + Pj) := ⟨_, rfl⟩
  have hτc : Continuous τ := by rw [hτd]; fun_prop
  have hτ : ∀ s, (Pi + Pj) * τ s = Pi * ti + Pj * tj + Pk * s0 - Pk * s := fun s => by
    rw [hτd]; exact mul_div_cancel₀ _ hQ.ne'
  obtain ⟨hf, hfd⟩ : ∃ hf : ℝ → ℝ,
      hf = fun s => Pi * ti ^ 2 + Pj * tj ^ 2 - Pk * s0 ^ 2 + Pk * s ^ 2 - (Pi + Pj) * τ s ^ 2 :=
    ⟨_, rfl⟩
  have hfc : Continuous hf := by rw [hfd]; fun_prop
  have hf_eq : ∀ s, hf s = Pi * ti ^ 2 + Pj * tj ^ 2 - Pk * s0 ^ 2 + Pk * s ^ 2 -
      (Pi + Pj) * τ s ^ 2 := fun s => by rw [hfd]
  obtain ⟨θ, hθd⟩ : ∃ θ : ℝ → ℝ, θ = fun s => σ * √(hf s / (Pi * Pj * (Pi + Pj))) := ⟨_, rfl⟩
  have hθc : Continuous θ := by rw [hθd]; fun_prop
  have hθ2 : ∀ s, 0 ≤ hf s → Pi * Pj * (Pi + Pj) * θ s ^ 2 = hf s := by
    intro s hs
    rw [hθd]
    simp only
    rw [mul_pow, hσ2, one_mul, Real.sq_sqrt (div_nonneg hs hc.le)]
    field_simp
  set X : ℝ → ℝ := fun s => τ s + Pj * θ s with hXd
  set Y : ℝ → ℝ := fun s => τ s - Pi * θ s with hYd
  have hXc : Continuous X := by fun_prop
  have hYc : Continuous Y := by fun_prop
  -- values at `s₀`
  have hτ0 : τ s0 = (Pi * ti + Pj * tj) / (Pi + Pj) := by
    rw [hτd]; simp only; ring_nf
  have hf0 : hf s0 = Pi * Pj * (Pi + Pj) * ((ti - tj) / (Pi + Pj)) ^ 2 := by
    rw [hf_eq, hτ0]
    field_simp
    ring
  have hθ0 : θ s0 = (ti - tj) / (Pi + Pj) := by
    rw [hθd]
    simp only
    rw [hf0, mul_div_cancel_left₀ _ hc.ne', Real.sqrt_sq_eq_abs, hσθ]
  have hX0 : X s0 = ti := by
    simp only [hXd, hθ0, hτ0]
    field_simp
    ring
  have hY0 : Y s0 = tj := by
    simp only [hYd, hθ0, hτ0]
    field_simp
    ring
  -- a neighbourhood where everything stays in `(−1, 1)`
  have ev1 : ∀ᶠ s in 𝓝 s0, |X s| < 1 ∧ |Y s| < 1 ∧ |s| < 1 := by
    have e1 : ∀ᶠ s in 𝓝 s0, |X s| < 1 :=
      hXc.abs.continuousAt.eventually_lt continuousAt_const (by rwa [hX0])
    have e2 : ∀ᶠ s in 𝓝 s0, |Y s| < 1 :=
      hYc.abs.continuousAt.eventually_lt continuousAt_const (by rwa [hY0])
    have e3 : ∀ᶠ s in 𝓝 s0, |s| < 1 :=
      continuous_abs.continuousAt.eventually_lt continuousAt_const hs0
    exact e1.and (e2.and e3)
  -- `h(s) ≥ 0` for `s` slightly to the right of `s₀`
  have ev2 : ∀ᶠ s in 𝓝[>] s0, 0 ≤ hf s := by
    by_cases htij : ti = tj
    · -- case (b): tangency, `tᵢ = tⱼ`, `tᵢ s₀ > 0`
      have hpos : 0 < ti * s0 := lt_of_not_ge fun h => hnot ⟨htij, h⟩
      have hs0p : 0 < s0 := by
        rcases hs0n.lt_or_eq with h | h
        · exact h
        · rw [← h, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
      have htip : 0 < ti := pos_of_mul_pos_left hpos hs0n
      have hδ : 0 < (Pi + Pj) * (s0 + ti) / Pk := by positivity
      filter_upwards [Ioo_mem_nhdsGT (show s0 < s0 + (Pi + Pj) * (s0 + ti) / Pk by linarith)]
        with s hs
      obtain ⟨hs1, hs2⟩ := hs
      have he0 : 0 < s - s0 := by linarith
      have heP : (s - s0) * Pk < (Pi + Pj) * (s0 + ti) := by
        have : s - s0 < (Pi + Pj) * (s0 + ti) / Pk := by linarith
        rwa [lt_div_iff₀ hPk] at this
      have hτs : (Pi + Pj) * τ s = (Pi + Pj) * ti - Pk * (s - s0) := by
        linear_combination hτ s - Pj * htij
      -- `(Pᵢ+Pⱼ)·h(s)` in terms of `e = s − s₀`
      have hexp : (Pi + Pj) * hf s = 2 * Pk * (s - s0) * (Pi + Pj) * (s0 + ti) +
          (s - s0) ^ 2 * (Pk * (Pi + Pj) - Pk ^ 2) := by
        rw [hf_eq, ← htij]
        linear_combination (-((Pi + Pj) * τ s + ((Pi + Pj) * ti - Pk * (s - s0)))) * hτs
      have h1 : 0 < (s - s0) * Pk := by positivity
      have h2 : ((s - s0) * Pk) * ((s - s0) * Pk) < ((s - s0) * Pk) * ((Pi + Pj) * (s0 + ti)) :=
        mul_lt_mul_of_pos_left heP h1
      have h3 : (Pi + Pj) * 0 ≤ (Pi + Pj) * hf s := by
        rw [hexp]; nlinarith [sq_nonneg (s - s0), mul_pos hPk hQ]
      exact le_of_mul_le_mul_left h3 hQ
    · -- case (a): `tᵢ ≠ tⱼ`, `h(s₀) > 0`
      have hpos : 0 < hf s0 := by
        rw [hf0]
        have : (ti - tj) / (Pi + Pj) ≠ 0 := div_ne_zero (sub_ne_zero.2 htij) hQ.ne'
        positivity
      have : ∀ᶠ s in 𝓝 s0, 0 < hf s := hfc.continuousAt.eventually (lt_mem_nhds hpos)
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun s hs => hs.le
  have ev3 : ∀ᶠ s in 𝓝[>] s0, s0 < s := self_mem_nhdsWithin
  obtain ⟨s, ⟨hXs, hYs, hss⟩, hfs, hs⟩ := ((ev1.filter_mono nhdsWithin_le_nhds).and (ev2.and ev3)).exists
  refine ⟨X s, Y s, s, hXs.le, hYs.le, hss.le, by nlinarith, ?_, ?_⟩
  · simp only [hXd, hYd]
    linear_combination hτ s
  · simp only [hXd, hYd]
    linear_combination hθ2 s hfs + hf_eq s

/-- **The core of Lemma V** (Section 5, cases (a) and (b)): unless `tᵢ = tⱼ ∧ tᵢ s₀ ≤ 0`, the triple
`(tᵢ, tⱼ, s₀)` can be moved inside `[−1, 1]³` preserving `L` and `Def₊ − Def₋` and strictly
increasing `s²`. The case `s₀ < 0` reduces to `s₀ ≥ 0` by changing the signs of all three parameters. -/
theorem lemmaV_core {Pi Pj Pk ti tj s0 : ℝ} (hPi : 0 < Pi) (hPj : 0 < Pj) (hPk : 0 < Pk)
    (hti : |ti| < 1) (htj : |tj| < 1) (hs0 : |s0| < 1)
    (hnot : ¬ (ti = tj ∧ ti * s0 ≤ 0)) :
    ∃ X Y s : ℝ, |X| ≤ 1 ∧ |Y| ≤ 1 ∧ |s| ≤ 1 ∧ s0 ^ 2 < s ^ 2 ∧
      Pi * X + Pj * Y + Pk * s = Pi * ti + Pj * tj + Pk * s0 ∧
      Pi * X ^ 2 + Pj * Y ^ 2 - Pk * s ^ 2 = Pi * ti ^ 2 + Pj * tj ^ 2 - Pk * s0 ^ 2 := by
  rcases le_or_gt 0 s0 with hs0n | hs0n
  · exact lemmaV_core_nonneg hPi hPj hPk hti htj hs0 hs0n hnot
  · have hnot' : ¬ (-ti = -tj ∧ -ti * -s0 ≤ 0) := by
      rw [neg_inj, neg_mul_neg]; exact hnot
    obtain ⟨X, Y, s, hX, hY, hs, hlt, h1, h2⟩ := lemmaV_core_nonneg hPi hPj hPk
      (by rwa [abs_neg]) (by rwa [abs_neg]) (by rwa [abs_neg]) (by linarith) hnot'
    refine ⟨-X, -Y, -s, by rwa [abs_neg], by rwa [abs_neg], by rwa [abs_neg], ?_, ?_, ?_⟩
    · simpa [neg_sq] using hlt
    · linear_combination -h1
    · simpa [neg_sq] using h2

end RectInNBox
