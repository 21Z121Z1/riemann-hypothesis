import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianForm
section
noncomputable def UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm :
    {g : ℕ} → Matrix (Fin g) (Fin g) ℂ → (Fin g → ℂ) → (Fin g → ℂ) → ℂ :=
    fun {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) ↦ z ⬝ᵥ Hm.mulVec (Star.star w)

noncomputable def UpperTheory.Reformulated.B.HermitianFormImEqSum.hv :
    {n : ℕ} → Matrix (Fin n) (Fin n) ℂ → (Fin n → ℂ) → (Fin n → ℂ) → ℂ :=
    fun {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) ↦ Star.star y ⬝ᵥ M.mulVec x

private theorem UpperTheory.Reformulated.B.HermitianFormImEqSum.ext_span {V : Type} [AddCommGroup V] [Module ℝ V]
    (f h : V → ℝ) (S : Set V) (hS : Submodule.span ℝ S = ⊤)
    (fa : ∀ x y, f (x + y) = f x + f y) (fs : ∀ (c : ℝ) x, f (c • x) = c * f x)
    (ha : ∀ x y, h (x + y) = h x + h y) (hs : ∀ (c : ℝ) x, h (c • x) = c * h x)
    (H : ∀ a ∈ S, f a = h a) (x : V) : f x = h x := by
  have hx : x ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem a ha => exact H a ha
  | zero =>
    have h1 := fs 0 0
    have h2 := hs 0 0
    simp only [zero_smul, zero_mul] at h1 h2
    rw [h1, h2]
  | add a b _ _ h1 h2 => rw [fa, ha, h1, h2]
  | smul c a _ h1 => rw [fs, hs, h1]

private theorem UpperTheory.Reformulated.B.HermitianFormImEqSum.re_hermitian_combination_nonpos (c : ℝ) (a b : ℂ) : (a * (c • b)).re = c * (a * b).re := by
  rw [mul_smul_comm, Complex.smul_re, smul_eq_mul]

theorem UpperTheory.Reformulated.B.HermitianFormImEqSum.bil_eq :
    ∀ {P : Type} [inst : Fintype P] [DecidableEq P] {n g : ℕ} (R : (P → Fin n → ℂ) ≃ₗ[ℝ] Fin g → ℂ)
      (Hm : Matrix (Fin g) (Fin g) ℂ) (M : P → Matrix (Fin n) (Fin n) ℂ) (s : P → ℂ) (r : P → ℝ) (S : Set (P → Fin n → ℂ)),
      Submodule.span ℝ S = ⊤ →
        (∀ a ∈ S,
            ∀ b ∈ S,
              (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm ((R : (P → Fin n → ℂ) → Fin g → ℂ) a) ((R : (P → Fin n → ℂ) → Fin g → ℂ) b)).im =
                ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (a v) (b v)).re) →
          ∀ (x y : P → Fin n → ℂ),
            (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm ((R : (P → Fin n → ℂ) → Fin g → ℂ) x) ((R : (P → Fin n → ℂ) → Fin g → ℂ) y)).im =
              ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (x v) (y v)).re := by
  intro P _ _ n g R Hm M s r S hS H x y
  have step : ∀ a ∈ S, ∀ y : P → Fin n → ℂ,
      (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm (R a) (R y)).im =
        ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (a v) (y v)).re := by
    intro a ha y
    refine UpperTheory.Reformulated.B.HermitianFormImEqSum.ext_span (fun y => (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm (R a) (R y)).im)
      (fun y => ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (a v) (y v)).re)
      S hS ?_ ?_ ?_ ?_ (H a ha) y
    · intro u w
      simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm, map_add, star_add, Matrix.mulVec_add, dotProduct_add,
        Complex.add_im]
    · intro c u
      simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm, map_smul, star_smul, star_trivial, Matrix.mulVec_smul,
        dotProduct_smul, Complex.smul_im, smul_eq_mul]
    · intro u w
      simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hv, Pi.add_apply, star_add, add_dotProduct, mul_add,
        Complex.add_re, Finset.sum_add_distrib]
    · intro c u
      simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hv, Pi.smul_apply, star_smul, star_trivial, smul_dotProduct,
        UpperTheory.Reformulated.B.HermitianFormImEqSum.re_hermitian_combination_nonpos, Finset.mul_sum, mul_left_comm c]
  refine UpperTheory.Reformulated.B.HermitianFormImEqSum.ext_span (fun x => (UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm Hm (R x) (R y)).im)
    (fun x => ∑ v : P, r v * (-s v * Complex.I * UpperTheory.Reformulated.B.HermitianFormImEqSum.hv (M v) (x v) (y v)).re)
    S hS ?_ ?_ ?_ ?_ (fun a ha => step a ha y) x
  · intro u w
    simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm, map_add, add_dotProduct, Complex.add_im]
  · intro c u
    simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hermForm, map_smul, smul_dotProduct, Complex.smul_im, smul_eq_mul]
  · intro u w
    simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hv, Pi.add_apply, Matrix.mulVec_add, dotProduct_add, mul_add,
      Complex.add_re, Finset.sum_add_distrib]
  · intro c u
    simp only [UpperTheory.Reformulated.B.HermitianFormImEqSum.hv, Pi.smul_apply, Matrix.mulVec_smul, dotProduct_smul,
      UpperTheory.Reformulated.B.HermitianFormImEqSum.re_hermitian_combination_nonpos, Finset.mul_sum, mul_left_comm c]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianPositiveSymplectic
section
private theorem exists_ker {n g : ℕ} (f : (Fin n → ℂ) →ₗ[ℝ] (Fin g → ℂ))
    (U : Submodule ℂ (Fin g → ℂ)) (hU : ∀ y, f y ∈ U)
    (hI : ∀ y, f y = 0 → f (Complex.I • y) = 0) :
    ∃ K : Submodule ℂ (Fin n → ℂ), (∀ y, y ∈ K ↔ f y = 0) ∧
      n ≤ Module.finrank ℂ K + Module.finrank ℂ U := by
  let K : Submodule ℂ (Fin n → ℂ) :=
    { carrier := {y | f y = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun z y hy => by
        simp only [Set.mem_setOf_eq] at hy ⊢
        have hz : z • y = z.re • y + z.im • (Complex.I • y) := by
          ext i
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
          conv_lhs => rw [← Complex.re_add_im z]
          ring
        rw [hz, map_add, map_smul, map_smul, hy, hI y hy, smul_zero, smul_zero, add_zero] }
  refine ⟨K, fun y => Iff.rfl, ?_⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : LinearMap.ker f = K.restrictScalars ℝ := by
    ext y
    rfl
  have h3 : LinearMap.range f ≤ U.restrictScalars ℝ := by
    rintro _ ⟨y, rfl⟩
    exact hU y
  have h4 := Submodule.finrank_mono h3
  have h5 : Module.finrank ℝ (U.restrictScalars ℝ) = 2 * Module.finrank ℂ U :=
    finrank_real_of_complex U
  have h6 : Module.finrank ℝ (K.restrictScalars ℝ) = 2 * Module.finrank ℂ K :=
    finrank_real_of_complex K
  have h7 : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [finrank_real_of_complex]; simp
  rw [h2, h6, h7] at h1
  omega

theorem UpperTheory.hermitian_positive_symplectic :
    ∀ {g j j' : ℕ} (p : (Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ)) (H : Matrix (Fin g) (Fin g) ℂ)
        (S : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (c : ℝ) (U U' : Submodule ℂ (Fin g → ℂ)),
        (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (dotProduct z (H.mulVec (star z))).re) →
        IsUnit S.det → 0 < c →
        (∀ y y', (dotProduct (p y) (H.mulVec (star (p y')))).im =
          2 * (Complex.I * (c : ℂ) * dotProduct (star y') (S.mulVec y)).re) →
        Module.finrank ℂ U = j' → Module.finrank ℂ U' = j →
        (∀ y, p y - Complex.I • p (Complex.I • y) ∈ U) →
        (∀ y, p y + Complex.I • p (Complex.I • y) ∈ U') →
        ∃ K K' : Submodule ℂ (Fin (j + j') → ℂ),
          j ≤ Module.finrank ℂ K ∧ j' ≤ Module.finrank ℂ K' ∧
          (∀ y ∈ K, p y - Complex.I • p (Complex.I • y) = 0) ∧
          (∀ y ∈ K', p y + Complex.I • p (Complex.I • y) = 0) ∧
          (∀ y ∈ K, y ≠ 0 → 0 < (dotProduct (star y) (S.mulVec y)).re) ∧
          (∀ y ∈ K', y ≠ 0 → (dotProduct (star y) (S.mulVec y)).re < 0) ∧
          ∀ y ∈ K, ∀ y' ∈ K', dotProduct (star y') (S.mulVec y) = 0 := by
  intro g j j' p H S c U U' hH hS hc hp hU hU' hA hB
  let Q : (Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
    { toFun := fun y => Complex.I • p (Complex.I • y)
      map_add' := fun a b => by rw [smul_add, map_add, smul_add]
      map_smul' := fun r a => by
        rw [smul_comm Complex.I r a, map_smul, smul_comm Complex.I r]; rfl }
  have hII : ∀ {m : ℕ} (v : Fin m → ℂ), Complex.I • Complex.I • v = -v := by
    intro m v
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  have eA : ∀ y, p y - Complex.I • p (Complex.I • y) = 0 →
      p (Complex.I • y) = -(Complex.I • p y) := by
    intro y hy
    rw [sub_eq_zero.mp hy, hII, neg_neg]
  have eB : ∀ y, p y + Complex.I • p (Complex.I • y) = 0 →
      p (Complex.I • y) = Complex.I • p y := by
    intro y hy
    rw [eq_neg_of_add_eq_zero_left hy, smul_neg, hII, neg_neg]
  obtain ⟨K, hK, dK⟩ := exists_ker (p - Q) U hA (by
    intro y hy
    change p (Complex.I • y) - Complex.I • p (Complex.I • Complex.I • y) = 0
    rw [hII, map_neg, eA y hy, smul_neg, sub_self])
  obtain ⟨K', hK', dK'⟩ := exists_ker (p + Q) U' hB (by
    intro y hy
    change p (Complex.I • y) + Complex.I • p (Complex.I • Complex.I • y) = 0
    rw [hII, map_neg, eB y hy, smul_neg, add_neg_cancel])
  have hp' : ∀ y y', (dotProduct (p y) (H.mulVec (star (p y')))).im =
      -(2 * c * (dotProduct (star y') (S.mulVec y)).im) := by
    intro y y'
    rw [hp]
    simp
    ring
  have hinj : ∀ y, y ≠ 0 → p y ≠ 0 := by
    intro y hy h0
    apply hy
    have hz : ∀ y', (dotProduct (star y') (S.mulVec y)).im = 0 := by
      intro y'
      have h := hp' y y'
      rw [h0, zero_dotProduct, Complex.zero_im] at h
      have : c * (dotProduct (star y') (S.mulVec y)).im = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hc.ne'
    have hSy : S.mulVec y = 0 := by
      ext i
      have h1 := hz (Pi.single i 1)
      have h2 := hz (Pi.single i Complex.I)
      simp [← Pi.single_star] at h1 h2
      apply Complex.ext <;> simp [h1, h2]
    exact Matrix.eq_zero_of_mulVec_eq_zero hS.ne_zero hSy
  refine ⟨K, K', by omega, by omega, fun y hy => (hK y).mp hy, fun y hy => (hK' y).mp hy,
    ?_, ?_, ?_⟩
  · intro y hy h0
    have h1 := hH _ (hinj y h0)
    have h2 := hp' (Complex.I • y) y
    rw [eA y ((hK y).mp hy)] at h2
    simp [Matrix.mulVec_smul] at h2
    by_contra hn
    have := mul_nonneg hc.le (neg_nonneg.mpr (not_lt.mp hn))
    linarith
  · intro y hy h0
    have h1 := hH _ (hinj y h0)
    have h2 := hp' (Complex.I • y) y
    rw [eB y ((hK' y).mp hy)] at h2
    simp [Matrix.mulVec_smul] at h2
    by_contra hn
    have := mul_nonneg hc.le (not_lt.mp hn)
    linarith
  · intro y hy y' hy'
    have e1 := eA y ((hK y).mp hy)
    have e2 := eB y' ((hK' y').mp hy')
    have h1 := hp' y y'
    have h2 := hp' (Complex.I • y) y'
    have h3 := hp' y (Complex.I • y')
    have h4 := hp' (Complex.I • y) (Complex.I • y')
    rw [e1] at h2 h4
    rw [e2] at h3 h4
    simp [Matrix.mulVec_smul, Matrix.mulVec_neg] at h2 h3 h4
    have r1 : c * (dotProduct (star y') (S.mulVec y)).re = 0 := by linarith
    have r2 : c * (dotProduct (star y') (S.mulVec y)).im = 0 := by linarith
    exact Complex.ext ((mul_eq_zero.mp r1).resolve_left hc.ne')
      ((mul_eq_zero.mp r2).resolve_left hc.ne')
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HermitianProjectionEq
section
theorem UpperTheory.hermitian_projection_eq :
    ∀ {S : Type} [CommRing S] {n r : ℕ}
        (g P m : Matrix (Fin n) (Fin n) S) (X Y : Matrix (Fin n) (Fin r) S)
        (B C : Matrix (Fin r) (Fin r) S) (Xd Yd : Matrix (Fin r) (Fin n) S) (d e : Fin r → S),
        Xd * X = 0 → Yd * Y = 0 → Xd * Y = 1 → Yd * X = 1 →
        B.BlockTriangular id → g * X = X * B → Xd * g = C * Xd →
        (∀ i, d i = B i i) → (∀ i, IsUnit (d i)) →
        P = 1 - X * Yd - Y * Xd →
        m = (X * Matrix.diagonal d) * Yd + (Y * Matrix.diagonal e) * Xd + P * g * P →
        IsUnit m.det →
        (∃ B' : Matrix (Fin r) (Fin r) S, B'.BlockTriangular id ∧ (∀ i, B' i i = 1) ∧
            m⁻¹ * g * X = X * B') ∧
          ∀ z : Fin n → S, Xd.mulVec z = 0 →
            ∃ a : Fin r → S, (m⁻¹ * g - 1).mulVec z = X.mulVec a := by
  intro S _ n r g P m X Y B C Xd Yd d e hXdX hYdY hXdY hYdX hB hgX hXdg hd hu hP hm hdet
  have hmm : m⁻¹ * m = 1 := Matrix.nonsing_inv_mul m hdet
  obtain ⟨f, hf⟩ : ∃ f : Fin r → S, ∀ i, f i * d i = 1 :=
    ⟨fun i => (((hu i).unit⁻¹ : Sˣ) : S), fun i => (hu i).val_inv_mul⟩
  have hDF : Matrix.diagonal d * Matrix.diagonal f = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hf i
  have hPX : P * X = 0 := by
    rw [hP, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, hYdX, hXdX,
      Matrix.mul_one, Matrix.mul_zero, sub_self, sub_zero]
  have hmX : m * X = X * Matrix.diagonal d := by
    rw [hm, Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc _ Yd, Matrix.mul_assoc _ Xd, hYdX, hXdX,
      Matrix.mul_assoc _ P, hPX, Matrix.mul_one, Matrix.mul_zero, Matrix.mul_zero, add_zero,
      add_zero]
  have hinvX : m⁻¹ * X = X * Matrix.diagonal f := by
    calc m⁻¹ * X = m⁻¹ * (X * (Matrix.diagonal d * Matrix.diagonal f)) := by
          rw [hDF, Matrix.mul_one]
      _ = (m⁻¹ * m) * (X * Matrix.diagonal f) := by
          rw [← Matrix.mul_assoc X, ← hmX, Matrix.mul_assoc m, Matrix.mul_assoc m⁻¹]
      _ = X * Matrix.diagonal f := by rw [hmm, Matrix.one_mul]
  have hPgX : P * g * X = 0 := by
    rw [Matrix.mul_assoc, hgX, ← Matrix.mul_assoc, hPX, Matrix.zero_mul]
  have hPg : P * g = g - X * (Yd * g) - Y * C * Xd := by
    rw [hP, sub_mul, sub_mul, Matrix.one_mul, Matrix.mul_assoc X, Matrix.mul_assoc Y, hXdg,
      Matrix.mul_assoc Y]
  have hPgP : P * g * P = P * g - P * g * Y * Xd := by
    have h0 : P * g * P = P * g * (1 - X * Yd - Y * Xd) := by rw [← hP]
    rw [h0, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc _ X, hPgX,
      Matrix.zero_mul, sub_zero, ← Matrix.mul_assoc _ Y]
  have hid : g - m = X * (Yd * g - Matrix.diagonal d * Yd)
      + (Y * C - Y * Matrix.diagonal e + P * g * Y) * Xd := by
    rw [hm, hPgP, hPg]
    simp only [Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  refine ⟨⟨Matrix.diagonal f * B, ?_, ?_, ?_⟩, ?_⟩
  · intro i j hij
    rw [Matrix.diagonal_mul, hB hij, mul_zero]
  · intro i
    rw [Matrix.diagonal_mul, ← hd i]
    exact hf i
  · rw [Matrix.mul_assoc, hgX, ← Matrix.mul_assoc, hinvX, Matrix.mul_assoc]
  · intro z hz
    refine ⟨(Matrix.diagonal f * (Yd * g - Matrix.diagonal d * Yd)).mulVec z, ?_⟩
    have h1 : m⁻¹ * g - 1 = (X * Matrix.diagonal f) * (Yd * g - Matrix.diagonal d * Yd)
        + m⁻¹ * (Y * C - Y * Matrix.diagonal e + P * g * Y) * Xd := by
      calc m⁻¹ * g - 1 = m⁻¹ * (g - m) := by rw [Matrix.mul_sub, hmm]
        _ = _ := by
          rw [hid, Matrix.mul_add, ← Matrix.mul_assoc, hinvX, ← Matrix.mul_assoc]
    rw [h1, Matrix.add_mulVec, ← Matrix.mulVec_mulVec z _ Xd, hz, Matrix.mulVec_zero, add_zero,
      Matrix.mul_assoc X, Matrix.mulVec_mulVec]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HilbertNinety
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

theorem UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.h90 :
    ∀ (K Ω : Type) [inst : Field K] [NumberField K] [inst_2 : Field Ω] [inst_3 : Algebra K Ω] [IsAlgClosure K Ω]
      (f : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω → Ω),
      IsLocallyConstant f →
        (∀ (g : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω), f g ≠ (0 : Ω)) →
          (∀ (g h : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω), f (g * h) = f g * (g : Ω → Ω) (f h)) →
            ∃ (β : Ω), β ≠ (0 : Ω) ∧ ∀ (g : UpperTheory.Reformulated.B.HilbertNinetyCapelliIdentities.G K Ω), (g : Ω → Ω) β = f g * β := by
  intro K Ω _ _ _ _ _ f hlc h0 hc
  classical
  have h1 : f 1 = 1 := by
    have h := hc 1 1
    rw [mul_one, AlgEquiv.one_apply] at h
    exact (mul_eq_left₀ (h0 1)).1 h.symm
  have hU : f ⁻¹' {1} ∈ nhds (1 : Gal(Ω/K)) :=
    (hlc {1}).mem_nhds h1
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 hU
  have hH : ∀ (g h : Gal(Ω/K)), h ∈ L.fixingSubgroup → f (g * h) = f g := by
    intro g h hh
    have : f h = 1 := hLU hh
    rw [hc, this, map_one, mul_one]
  have hopen : IsOpen (L.fixingSubgroup : Set Gal(Ω/K)) := L.fixingSubgroup_isOpen
  haveI : Finite (Gal(Ω/K) ⧸ L.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  letI : Fintype (Gal(Ω/K) ⧸ L.fixingSubgroup) := Fintype.ofFinite _
  let χ : (Gal(Ω/K) ⧸ L.fixingSubgroup) → (L →* Ω) := fun q =>
    ((q.out : Gal(Ω/K)) : Ω →* Ω).comp (L.val : L →* Ω)
  have hχ : ∀ q (x : L), χ q x = (q.out : Gal(Ω/K)) (x : Ω) := fun q x => rfl
  have hinj : Function.Injective χ := by
    intro p q hpq
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q, QuotientGroup.eq,
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h := DFunLike.congr_fun hpq ⟨x, hx⟩
    rw [hχ, hχ] at h
    rw [AlgEquiv.mul_apply]
    change p.out.symm (q.out x) = x
    rw [AlgEquiv.symm_apply_eq]
    exact h.symm
  have hli := (linearIndependent_monoidHom L Ω).comp χ hinj
  have hex : ∃ x : L, ∑ q, f q.out * χ q x ≠ 0 := by
    by_contra hne
    push Not at hne
    have := Fintype.linearIndependent_iff.1 hli (fun q => f q.out) (by
      funext x
      simpa [Finset.sum_apply] using hne x) (QuotientGroup.mk 1)
    exact h0 _ this
  obtain ⟨x, hx⟩ := hex
  have key : ∀ g : Gal(Ω/K),
      f g * g (∑ q, f q.out * χ q x) = ∑ q, f q.out * χ q x := by
    intro g
    rw [map_sum, Finset.mul_sum]
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => ?_
    have hq : g • q = QuotientGroup.mk (g * q.out) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul L.fixingSubgroup (g * q.out)
    have hfix : (h : Gal(Ω/K)) (x : Ω) = x :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 h.2 x x.2
    rw [MulAction.toPerm_apply, hq, hχ, hχ, hh, hH _ _ h.2, hc, AlgEquiv.mul_apply, hfix,
      AlgEquiv.mul_apply, map_mul, mul_assoc]
  refine ⟨(∑ q, f q.out * χ q x)⁻¹, inv_ne_zero hx, fun g => ?_⟩
  have hk := key g
  generalize (∑ q, f q.out * χ q x) = b at hx hk
  have hg : g b ≠ 0 := (map_ne_zero g).2 hx
  rw [map_inv₀]
  field_simp
  rw [mul_comm]
  exact hk.symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HomWProd
section
noncomputable def UpperTheory.Reformulated.B.Qi22.wsum.{v} :
    {ι : Type v} → (ι → ℤ) → (ι →₀ ℕ) → ℤ :=
    fun {ι : Type v} (w : ι → ℤ) (n : ι →₀ ℕ) ↦ n.sum fun (x : ι) (k : ℕ) ↦ (↑k : ℤ) * w x

noncomputable def UpperTheory.Reformulated.B.Qi22.HomW.{u, v} :
    {K : Type u} → [NormedField K] → {ι : Type v} → (ι → ℤ) → ℤ → MvPowerSeries ι K → Prop :=
    fun {K : Type u} [NormedField K] {ι : Type v} (w : ι → ℤ) (c : ℤ) (f : MvPowerSeries ι K) ↦
      ∀ (n : ι →₀ ℕ), (MvPowerSeries.coeff n : MvPowerSeries ι K → K) f ≠ (0 : K) → UpperTheory.Reformulated.B.Qi22.wsum w n = c

private theorem UpperTheory.Reformulated.B.Qi22.wsum_add {ι : Type*} (w : ι → ℤ) (a b : ι →₀ ℕ) :
    UpperTheory.Reformulated.B.Qi22.wsum w (a + b) = UpperTheory.Reformulated.B.Qi22.wsum w a + UpperTheory.Reformulated.B.Qi22.wsum w b := by
  unfold UpperTheory.Reformulated.B.Qi22.wsum
  apply Finsupp.sum_add_index'
  · intro x; simp
  · intro x p q; push_cast; ring

private theorem UpperTheory.Reformulated.B.Qi22.homW_one {K : Type*} [NormedField K] {ι : Type*} (w : ι → ℤ) :
    UpperTheory.Reformulated.B.Qi22.HomW w 0 (1 : MvPowerSeries ι K) := by
  classical
  intro n hn
  have h0 : n = 0 := by
    by_contra h
    exact hn (by rw [MvPowerSeries.coeff_one, if_neg h])
  subst h0
  simp [UpperTheory.Reformulated.B.Qi22.wsum]

private theorem UpperTheory.Reformulated.B.Qi22.homW_mul {K : Type*} [NormedField K] {ι : Type*} {w : ι → ℤ}
    {c d : ℤ} {f g : MvPowerSeries ι K} (hf : UpperTheory.Reformulated.B.Qi22.HomW w c f)
    (hg : UpperTheory.Reformulated.B.Qi22.HomW w d g) : UpperTheory.Reformulated.B.Qi22.HomW w (c + d) (f * g) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_mul] at hn
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hsum : p.1 + p.2 = n := by simpa using hp
  rw [← hsum, UpperTheory.Reformulated.B.Qi22.wsum_add, hf p.1 (left_ne_zero_of_mul hne),
    hg p.2 (right_ne_zero_of_mul hne)]

theorem UpperTheory.Reformulated.B.Qi22.homW_prod.{u, v, w} :
    ∀ {K : Type u} [inst : NormedField K] {ι : Type v} {w : ι → ℤ} {α : Type w} (s : Finset α) (c : α → ℤ)
      (F : α → MvPowerSeries ι K),
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qi22.HomW w (c i) (F i)) → UpperTheory.Reformulated.B.Qi22.HomW w (∑ i ∈ s, c i) (∏ i ∈ s, F i) := by
  intro K inst ι w α s c F
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using UpperTheory.Reformulated.B.Qi22.homW_one (K := K) w
  | insert a s ha ih =>
    intro h
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact UpperTheory.Reformulated.B.Qi22.homW_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HsSum
section
noncomputable def UpperTheory.Reformulated.B.Qh70.Hs :
    {L V ι : Type} →
      [inst : Field L] →
        [inst_1 : Algebra ℂ L] →
          [inst_2 : AddCommGroup V] → [_root_.Module L V] → Subalgebra ℂ L → Finset ι → (ι → V) → V → Prop :=
    fun {L V ι : Type} [Field L] [Algebra ℂ L] [AddCommGroup V] [_root_.Module L V] (B : Subalgebra ℂ L) (P : Finset ι)
        (g : ι → V) (w : V) ↦
      ∃ (c : ι → L), (∀ (S : ι), c S ∈ B) ∧ w = ∑ S ∈ P, c S • g S

theorem UpperTheory.Reformulated.B.Qh70.Hs_sum :
    ∀ {L V ι : Type} [inst : Field L] [inst_1 : Algebra ℂ L] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module L V]
      {B : Subalgebra ℂ L} {P : Finset ι} {g : ι → V} {α : Type} (s : Finset α) (f : α → V),
      (∀ a ∈ s, UpperTheory.Reformulated.B.Qh70.Hs B P g (f a)) → UpperTheory.Reformulated.B.Qh70.Hs B P g (∑ a ∈ s, f a) := by
  intro L V ι _ _ _ _ B P g α s f h
  refine Finset.sum_induction f (UpperTheory.Reformulated.B.Qh70.Hs B P g) ?_ ?_ h
  · rintro a b ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    refine ⟨fun S => c S + d S, fun S => B.add_mem (hc S) (hd S), ?_⟩
    simp only [add_smul, Finset.sum_add_distrib]
  · exact ⟨fun _ => 0, fun _ => B.zero_mem, by simp⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImagOfSq
section
theorem UpperTheory.Reformulated.B.Qh67.imag_of_sq :
    ∀ {c : ℂ} {d : ℕ},
    (0 : ℕ) < d → c ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) c = -c ∧ c ≠ (0 : ℂ) := by
  intro c d hd h
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have h1 : c.re * c.re - c.im * c.im = -(d : ℝ) := by
    have := congrArg Complex.re h
    simpa [pow_two] using this
  have h2 : c.re * c.im + c.im * c.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two] using this
  have h3 : c.re * c.im = 0 := by linarith [mul_comm c.re c.im]
  have hre : c.re = 0 := by
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact h4
    · rw [h4] at h1
      nlinarith [mul_self_nonneg c.re]
  refine ⟨?_, ?_⟩
  · apply Complex.ext
    · simp [hre]
    · simp
  · rintro rfl
    simp at h1
    omega
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsAlt
section
theorem UpperTheory.Reformulated.B.ConjEqNegOfSqEqNegNat₂.main :
    ∀ {d : ℕ}, (0 : ℕ) < d → ∀ {z : ℂ}, z ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  intro d hd z hz
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    have h := congrArg Complex.re hz
    simpa [pow_two] using h
  have him : z.re * z.im + z.im * z.re = 0 := by
    have h := congrArg Complex.im hz
    simpa [pow_two] using h
  have hprod : z.re * z.im = 0 := by linarith
  have hre0 : z.re = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact h
    · rw [h] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [hre0]
  · simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisSide
section
theorem UpperTheory.Reformulated.B.DYlb8.main :
    ∀ {n : ℕ} {S : Finset (Fin n)}, (∀ (a b : Fin n), b ≤ a → a ∈ S → b ∈ S) → ∀ (a : Fin n), a ∈ S ↔ (↑a : ℕ) < S.card := by
  intro n S h a
  constructor
  · intro ha
    have hsub : Finset.Iic a ⊆ S := fun b hb => h a b (Finset.mem_Iic.mp hb) ha
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega
  · intro hlt
    by_contra ha
    have hsub : S ⊆ Finset.Iio a :=
      fun b hb => Finset.mem_Iio.mpr (lt_of_not_ge fun hab => ha (h b a hab hb))
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    omega
end

