import RectInNBox.Reduction

/-!
# Reduction to widths in any dimension; the statement

The `n`-dimensional version of `fits_iff_widths` from the three-dimensional formalization
(`box-in-box`, `Statement.lean`), and its special case — a rectangle in an `n`-box (formula (1) of
the paper, Section 4.1).

**Choice of definitions.** A box always lives in the ambient `ℝⁿ` and is given by its vector of edges
`q : Fin n → ℝ`: `boxN q = ∏ᵢ [0, qᵢ]`. A box of lower dimension `m ≤ n` (for instance a
rectangle, `m = 2`) is `boxN (pad h q)`, where `pad h q : Fin n → ℝ` extends
`q : Fin m → ℝ` by zeros: `(q₀, …, q_{m-1}, 0, …, 0)`. Then "a `k`-box in an `n`-box" is
literally a special case of `FitsN`, and no separate embedding `ℝᵐ → ℝⁿ` is needed.
**Trusted definitions:** only `boxN`, `pad` and `FitsN` have to be checked by eye.
-/

namespace RectInNBox

open Matrix WithLp

variable {n m : ℕ}

/-- Euclidean space `ℝⁿ`. -/
abbrev En (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The closed box `∏ᵢ [0, qᵢ]` in `ℝⁿ` with edges along the coordinate axes. -/
def boxN (q : Fin n → ℝ) : Set (En n) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ q i}

/-- The vector of edges `q : Fin m → ℝ` extended by zeros to `Fin n` (`m ≤ n`):
`pad h q = (q₀, …, q_{m-1}, 0, …, 0)`. -/
noncomputable def pad (h : m ≤ n) (q : Fin m → ℝ) : Fin n → ℝ :=
  Function.extend (Fin.castLE h) q 0

/-- **Statement.** The box with edges `q` fits into the box with edges `p`: some isometry of
`ℝⁿ` (any rigid motion, reflections included) maps the first box into the second. -/
def FitsN (p q : Fin n → ℝ) : Prop := ∃ f : En n ≃ᵢ En n, f '' boxN q ⊆ boxN p

/-! ## `pad` -/

lemma pad_castLE (h : m ≤ n) (q : Fin m → ℝ) (j : Fin m) : pad h q (Fin.castLE h j) = q j :=
  (Fin.castLE_injective h).extend_apply _ _ _

lemma pad_nonneg (h : m ≤ n) {q : Fin m → ℝ} (hq : ∀ j, 0 ≤ q j) (i : Fin n) : 0 ≤ pad h q i := by
  by_cases hi : ∃ j, Fin.castLE h j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [pad_castLE]; exact hq j
  · rw [pad, Function.extend_apply' _ _ _ hi]; rfl

/-- A sum against a zero-padded vector is a sum over the original coordinates. -/
lemma sum_pad_mul (h : m ≤ n) (q : Fin m → ℝ) (c : Fin n → ℝ) :
    ∑ j, pad h q j * c j = ∑ j, q j * c (Fin.castLE h j) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
  · intro i hi
    rw [pad, Function.extend_apply' _ _ _ (by rintro ⟨j, rfl⟩; exact hi ⟨j, rfl⟩)]
    simp
  · intro j; rw [pad_castLE]

/-! ## Rigid motions -/

/-- An orthogonal matrix preserves the dot square. -/
lemma dot_mulVec_self_of_orthN {R : Matrix (Fin n) (Fin n) ℝ} (hR : Rᵀ * R = 1)
    (v : Fin n → ℝ) : (R *ᵥ v) ⬝ᵥ (R *ᵥ v) = v ⬝ᵥ v := by
  calc (R *ᵥ v) ⬝ᵥ (R *ᵥ v) = ((R *ᵥ v) ᵥ* R) ⬝ᵥ v := dotProduct_mulVec _ _ _
    _ = (Rᵀ *ᵥ (R *ᵥ v)) ⬝ᵥ v := by rw [mulVec_transpose]
    _ = v ⬝ᵥ v := by rw [mulVec_mulVec, hR, one_mulVec]

/-- The motion `x ↦ R x + t` of `ℝⁿ` for an orthogonal `R`. -/
noncomputable def motionN (R : Matrix (Fin n) (Fin n) ℝ) (hR : R ∈ orthogonalGroup (Fin n) ℝ)
    (t : Fin n → ℝ) : En n ≃ᵢ En n where
  toFun x := toLp 2 (R *ᵥ ofLp x + t)
  invFun y := toLp 2 (Rᵀ *ᵥ (ofLp y - t))
  left_inv x := by
    have h : Rᵀ * R = 1 := (mem_orthogonalGroup_iff' (Fin n) ℝ).1 hR
    simp [mulVec_mulVec, h]
  right_inv y := by
    have h : R * Rᵀ = 1 := (mem_orthogonalGroup_iff (Fin n) ℝ).1 hR
    simp [mulVec_mulVec, h]
  isometry_toFun := by
    have h : Rᵀ * R = 1 := (mem_orthogonalGroup_iff' (Fin n) ℝ).1 hR
    refine Isometry.of_dist_eq fun x y => ?_
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    congr 1
    have key := dot_mulVec_self_of_orthN h (ofLp x - ofLp y)
    simp only [dotProduct, mulVec_sub] at key
    simp only [Pi.add_apply, Real.dist_eq, sq_abs]
    convert key using 2 with i _ i _
    · simp [Pi.sub_apply, sq]
    · simp [sq]

lemma mem_boxN_iff (q : Fin n → ℝ) (X : En n) :
    X ∈ boxN q ↔ ofLp X ∈ Set.Icc (0 : Fin n → ℝ) q := by
  simp [boxN, Set.mem_Icc, Pi.le_def, forall_and]

/-! ## Widths -/

/-- **Reduction to widths in `ℝⁿ`.** `FitsN p q` ⇔ there is an orthogonal matrix `R`
with `∑ⱼ qⱼ |Rᵢⱼ| ≤ pᵢ` for all `i`. (Mazur–Ulam + `exists_translate_mem_box_iff`.) -/
theorem fitsN_iff_widths (p q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i) :
    FitsN p q ↔ ∃ R ∈ orthogonalGroup (Fin n) ℝ, ∀ i, ∑ j, q j * |R i j| ≤ p i := by
  have hq' : (0 : Fin n → ℝ) ≤ q := fun i => hq i
  constructor
  · rintro ⟨f, hf⟩
    set L := f.toRealLinearIsometryEquiv
    set b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    set R := LinearMap.toMatrix b b (L : En n →ₗ[ℝ] En n)
    have hRmem : R ∈ orthogonalGroup (Fin n) ℝ :=
      L.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin n) ℝ)
        (EuclideanSpace.basisFun (Fin n) ℝ)
    have hL : ∀ x : Fin n → ℝ, ofLp (L (toLp 2 x)) = R *ᵥ x := by
      intro x
      have : toEuclideanLin R = (L : En n →ₗ[ℝ] En n) := by
        rw [toEuclideanLin_eq_toLin_orthonormal, Matrix.toLin_toMatrix]
      rw [← LinearIsometryEquiv.coe_toLinearEquiv, ← LinearEquiv.coe_toLinearMap]
      change ofLp ((L : En n →ₗ[ℝ] En n) (toLp 2 x)) = _
      rw [← this, toLpLin_apply]
    refine ⟨R, hRmem, (exists_translate_mem_box_iff R q p hq').1 ⟨ofLp (f 0), fun x hx => ?_⟩⟩
    have hX : toLp 2 x ∈ boxN q := (mem_boxN_iff q _).2 (by simpa using hx)
    have := (mem_boxN_iff p _).1 (hf ⟨_, hX, rfl⟩)
    have e : f (toLp 2 x) = L (toLp 2 x) + f 0 := by
      rw [IsometryEquiv.toRealLinearIsometryEquiv_apply]; abel
    rw [e, ofLp_add, hL] at this
    exact this
  · rintro ⟨R, hR, hw⟩
    obtain ⟨t, ht⟩ := (exists_translate_mem_box_iff R q p hq').2 hw
    refine ⟨motionN R hR t, ?_⟩
    rintro _ ⟨X, hX, rfl⟩
    rw [mem_boxN_iff]
    exact ht _ ((mem_boxN_iff q X).1 hX)

/-- Widths for an `m`-box in an `n`-box: only the first `m` columns of `R` take part. -/
theorem fitsN_pad_iff_widths (h : m ≤ n) (p : Fin n → ℝ) (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j) :
    FitsN p (pad h q) ↔ ∃ R ∈ orthogonalGroup (Fin n) ℝ,
      ∀ i, ∑ j, q j * |R i (Fin.castLE h j)| ≤ p i := by
  rw [fitsN_iff_widths p _ (pad_nonneg h hq)]
  simp only [sum_pad_mul]

/-! ## The rectangle: formula (1) -/

/-- **Formula (1)** (the paper, Section 4.1). The rectangle `A × B`
(the box `(A, B, 0, …, 0)`) fits into the `n`-box `p` ⇔ there are orthonormal
`u, v ∈ ℝⁿ` with `A|uᵢ| + B|vᵢ| ≤ pᵢ` for all `i`. -/
theorem fitsN_rect_iff (h : 2 ≤ n) (p : Fin n → ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    FitsN p (pad h ![A, B]) ↔ ∃ u v : Fin n → ℝ,
      (∑ i, u i ^ 2 = 1) ∧ (∑ i, v i ^ 2 = 1) ∧ (∑ i, u i * v i = 0) ∧
      ∀ i, A * |u i| + B * |v i| ≤ p i := by
  have hq : ∀ j, 0 ≤ (![A, B] : Fin 2 → ℝ) j := by
    intro j; fin_cases j <;> simp [hA, hB]
  rw [fitsN_pad_iff_widths h p _ hq]
  set a : Fin n := Fin.castLE h 0 with ha
  set b : Fin n := Fin.castLE h 1 with hb
  have hab : a ≠ b := fun e => absurd (Fin.castLE_injective h e) (by decide)
  constructor
  · rintro ⟨R, hR, hw⟩
    have hR' : Rᵀ * R = 1 := (mem_orthogonalGroup_iff' (Fin n) ℝ).1 hR
    have hcol : ∀ j k, ∑ i, R i j * R i k = if j = k then 1 else 0 := by
      intro j k
      have := congrFun (congrFun hR' j) k
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    refine ⟨fun i => R i a, fun i => R i b, ?_, ?_, ?_, fun i => ?_⟩
    · simpa [sq] using hcol a a
    · simpa [sq] using hcol b b
    · simpa [hab] using hcol a b
    · simpa [Fin.sum_univ_two, ← ha, ← hb] using hw i
  · rintro ⟨u, v, hu, hv, huv, hw⟩
    classical
    -- the family: `u` at `a`, `v` at `b`, zeros elsewhere
    set w : Fin n → En n := fun k => if k = a then toLp 2 u else if k = b then toLp 2 v else 0
    have hwa : w a = toLp 2 u := by simp [w]
    have hwb : w b = toLp 2 v := by simp [w, hab.symm]
    have inner_eq : ∀ x y : Fin n → ℝ, inner ℝ (toLp 2 x : En n) (toLp 2 y) = ∑ i, x i * y i := by
      intro x y
      simp [PiLp.inner_apply, mul_comm]
    have hon : Orthonormal ℝ (({a, b} : Set (Fin n)).domRestrict w) := by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
        simp only [Set.domRestrict_apply, hwa, hwb, inner_eq] <;>
        simp [hab, hab.symm, ← sq, hu, hv, huv, mul_comm]
    obtain ⟨β, hβ⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
    set R := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix β
    have hRij : ∀ i j, R i j = β j i := by
      intro i j
      simp [R, Module.Basis.toMatrix_apply]
    refine ⟨R, (EuclideanSpace.basisFun (Fin n) ℝ).toMatrix_orthonormalBasis_mem_orthogonal β,
      fun i => ?_⟩
    have ea : R i a = u i := by rw [hRij, hβ a (by simp), hwa]
    have eb : R i b = v i := by rw [hRij, hβ b (by simp), hwb]
    simpa [Fin.sum_univ_two, ← ha, ← hb, ea, eb] using hw i

end RectInNBox
