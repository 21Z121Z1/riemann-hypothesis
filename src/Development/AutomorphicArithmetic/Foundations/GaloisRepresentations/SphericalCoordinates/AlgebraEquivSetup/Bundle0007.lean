import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRealGen
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma traceCM_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (z : E) :
    Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z

private lemma conj_conj' {E : Type} [Field E] [NumberField E] [IsCMField E] (z : E) :
    IsCMField.complexConj E (IsCMField.complexConj E z) = z :=
  IsCMField.complexConj_apply_apply E z

private lemma inCodiff_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E)
    (hbar : ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) {y : E} (hy : InCodiff y) :
    InCodiff (IsCMField.complexConj E y) := by
  intro x
  obtain ⟨m, hm⟩ := hy (bar.symm x)
  refine ⟨m, ?_⟩
  have h : IsCMField.complexConj E y * (x : E) =
      IsCMField.complexConj E (y * ((bar.symm x : 𝓞 E) : E)) := by
    rw [map_mul, ← hbar, RingEquiv.apply_symm_apply]
  rw [h, traceCM_conj, hm]

private lemma inCodiff_mul {E : Type} [Field E] [NumberField E] {y : E} (hy : InCodiff y) (a : 𝓞 E) :
    InCodiff (y * (a : E)) := by
  intro x
  obtain ⟨m, hm⟩ := hy (a * x)
  refine ⟨m, ?_⟩
  rw [mul_assoc, ← hm]
  push_cast
  rfl

private lemma inCodiff_add {E : Type} [Field E] [NumberField E] {y z : E} (hy : InCodiff y) (hz : InCodiff z) :
    InCodiff (y + z) := by
  intro x
  obtain ⟨m, hm⟩ := hy x
  obtain ⟨n, hn⟩ := hz x
  refine ⟨m + n, ?_⟩
  rw [add_mul, map_add, hm, hn]
  push_cast
  rfl

theorem UpperTheory.Gal.W2.Seed.pRealGen :
    CodiffGen → CodiffUnit → RealGen := by
  intro hgen hunit E _ _ _ bar hbar M hM ε hε
  obtain ⟨y, hy⟩ := hgen E M hM
  by_cases hy0 : y = 0
  · subst hy0
    exact ⟨0, map_zero _, hy⟩
  obtain ⟨hyc, e, he, hegen⟩ := hy
  have hcy : InCodiff (IsCMField.complexConj E y) := inCodiff_conj bar hbar hyc
  obtain ⟨x0, hx0⟩ := hegen _ hcy
  have hx0' : (e : E) * y = IsCMField.complexConj E y * ((bar x0 : 𝓞 E) : E) := by
    have h := congrArg (IsCMField.complexConj E) hx0
    rw [map_mul, map_mul, conj_conj', map_natCast] at h
    rw [hbar, h]
  have hnorm : x0 * bar x0 = (e : 𝓞 E) ^ 2 := by
    apply RingOfIntegers.ext
    have h1 : y * ((e : E) ^ 2) = y * ((x0 : E) * ((bar x0 : 𝓞 E) : E)) := by
      calc y * ((e : E) ^ 2) = (e : E) * ((e : E) * y) := by ring
        _ = (e : E) * IsCMField.complexConj E y * ((bar x0 : 𝓞 E) : E) := by rw [hx0']; ring
        _ = y * (x0 : E) * ((bar x0 : 𝓞 E) : E) := by rw [hx0]
        _ = _ := by ring
    have h2 := mul_left_cancel₀ hy0 h1
    push_cast
    exact h2.symm
  set t : E := y * (ε : E) + IsCMField.complexConj E (y * (ε : E)) with ht
  refine ⟨t, ?_, ?_⟩
  · rw [ht, map_add, conj_conj', add_comm]
  · apply hunit E M hM y t ⟨hyc, e, he, hegen⟩
      (inCodiff_add (inCodiff_mul hyc ε) (inCodiff_conj bar hbar (inCodiff_mul hyc ε)))
    intro P hP hMP
    have heP : (e : 𝓞 E) ∉ P := by
      intro heP
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr he
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one]
      have h3 : ((a * e + b * M : ℤ) : 𝓞 E) = 1 := by rw [hab]; simp
      rw [← h3]
      push_cast
      exact P.add_mem (P.mul_mem_left _ heP) (P.mul_mem_left _ hMP)
    have hx0P : x0 ∉ P := by
      intro h
      apply heP
      have h4 : (e : 𝓞 E) ^ 2 ∈ P := hnorm ▸ P.mul_mem_right _ h
      exact hP.isPrime.mem_of_pow_mem 2 h4
    obtain ⟨h1, h2⟩ := hε P hP hMP
    refine ⟨e, e * ε + x0 * bar ε, heP, ?_, ?_⟩
    · intro hu
      rcases hP.isPrime.mem_or_mem h2 with hεP | hεP
      · apply hx0P
        have h5 : x0 = (e * ε + x0 * bar ε) - (e - x0) * ε - x0 * (ε + bar ε - 1) := by ring
        rw [h5]
        exact P.sub_mem (P.sub_mem hu (P.mul_mem_left _ hεP)) (P.mul_mem_left _ h1)
      · apply heP
        have h5 : (e : 𝓞 E) = (e * ε + x0 * bar ε) - e * (ε + bar ε - 1) + (e - x0) * bar ε := by ring
        rw [h5]
        exact P.add_mem (P.sub_mem hu (P.mul_mem_left _ h1)) (P.mul_mem_left _ hεP)
    · rw [ht, map_mul, ← hbar]
      push_cast
      linear_combination ((bar ε : 𝓞 E) : E) * hx0
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRealIso
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma realForm_eq_zero {E : Type} [Field E] [NumberField E] {P : Type} [Fintype P] (g : P → (E →+* ℂ))
    (hg : Function.Injective (Sum.elim g (fun p => ComplexEmbedding.conjugate (g p))))
    (u v : P → ℝ) (h : ∀ x : 𝓞 E, ∑ p, (u p * (g p (x : E)).re + v p * (g p (x : E)).im) = 0) :
    ∀ p, u p = 0 ∧ v p = 0 := by
  classical
  let σ : P ⊕ P → (E →* ℂ) := fun k =>
    (Sum.elim g (fun p => ComplexEmbedding.conjugate (g p)) k).toMonoidHom
  have hσ : Function.Injective σ := by
    intro k l hkl
    apply hg
    ext x
    exact DFunLike.congr_fun hkl x
  have hli : LinearIndependent ℂ (fun k => (σ k : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp σ hσ
  have hE : ∀ x : E, ∑ p, (u p * (g p x).re + v p * (g p x).im) = 0 := by
    intro x
    obtain ⟨d, hd, hdx⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset E)
    obtain ⟨w, hw⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp
      (hdx x (Finset.mem_singleton_self x))
    have h1 := h w
    have hw' : (w : E) = (d : E) * x := by
      rw [← zsmul_eq_mul, ← hw]
    rw [hw'] at h1
    simp only [map_mul, map_intCast, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, zero_mul, sub_zero, add_zero] at h1
    have h3 : (d : ℝ) * ∑ p, (u p * (g p x).re + v p * (g p x).im) = 0 := by
      rw [Finset.mul_sum, ← h1]
      exact Finset.sum_congr rfl fun p _ => by ring
    rcases mul_eq_zero.mp h3 with h2 | h2
    · exact absurd (Int.cast_eq_zero.mp h2) hd
    · exact h2
  let c : P ⊕ P → ℂ := Sum.elim (fun p => ((u p : ℂ) - Complex.I * v p) / 2)
    (fun p => ((u p : ℂ) + Complex.I * v p) / 2)
  have hterm : ∀ p (x : E), ((u p : ℂ) - Complex.I * v p) / 2 * g p x +
      ((u p : ℂ) + Complex.I * v p) / 2 * ComplexEmbedding.conjugate (g p) x =
      ((u p * (g p x).re + v p * (g p x).im : ℝ) : ℂ) := by
    intro p x
    rw [ComplexEmbedding.conjugate_coe_eq]
    apply Complex.ext <;> simp <;> ring
  have hsum : ∑ k, c k • (σ k : E → ℂ) = 0 := by
    funext x
    rw [Finset.sum_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    calc _ = ∑ p, ((u p * (g p x).re + v p * (g p x).im : ℝ) : ℂ) :=
          Finset.sum_congr rfl fun p _ => hterm p x
      _ = 0 := by rw [← Complex.ofReal_sum, hE x, Complex.ofReal_zero]
  have hc := (Fintype.linearIndependent_iff.mp hli) c hsum
  intro p
  have h1 : ((u p : ℂ) - Complex.I * v p) / 2 = 0 := hc (Sum.inl p)
  have h1' : (u p : ℂ) - Complex.I * v p = 0 := by
    rcases div_eq_zero_iff.mp h1 with h | h
    · exact h
    · norm_num at h
  constructor
  · have h4 := congrArg Complex.re h1'
    simpa using h4
  · have h4 := congrArg Complex.im h1'
    simpa using h4

theorem UpperTheory.Gal.W2.Seed.pRealIso :
    TraceType → RealIso := by
  intro hT E _ _ _ A n
  classical
  obtain ⟨-, -, hpl, him⟩ := hT E A
  have hcardPhi : Fintype.card (Phi A) = Fintype.card (InfinitePlace E) := by
    refine Fintype.card_congr (Equiv.ofBijective (fun τ : Phi A => InfinitePlace.mk τ.1) ⟨?_, ?_⟩)
    · intro a b hab
      exact (hpl (InfinitePlace.mk a.1)).unique rfl hab.symm
    · intro v
      obtain ⟨τ, hτ, -⟩ := hpl v
      exact ⟨τ, hτ⟩
  have hrank : 2 * Fintype.card (InfinitePlace E) = Module.finrank ℚ E := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank E
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero E]
    rw [IsTotallyComplex.nrRealPlaces_eq_zero E] at h1
    omega
  let b := NumberField.RingOfIntegers.basis E
  let bZ := Pi.basis (fun _ : Fin n => b)
  let b1 := Algebra.TensorProduct.basis ℝ bZ
  let F : (Fin n → 𝓞 E) →ₗ[ℤ] (Phi A × Fin n → ℂ) :=
    LinearMap.pi (fun p : Phi A × Fin n =>
      ((p.1.1.comp (algebraMap (𝓞 E) E)).toIntAlgHom.toLinearMap) ∘ₗ LinearMap.proj p.2)
  let L : ℝ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℝ] (Phi A × Fin n → ℂ) := b1.constr ℝ (fun k => F (bZ k))
  have hL : ∀ x, L (1 ⊗ₜ x) = F x := by
    have hcomp : (L.restrictScalars ℤ) ∘ₗ TensorProduct.mk ℤ ℝ (Fin n → 𝓞 E) 1 = F := by
      refine bZ.ext fun k => ?_
      have hk : ((L.restrictScalars ℤ) ∘ₗ TensorProduct.mk ℤ ℝ (Fin n → 𝓞 E) 1) (bZ k) =
          L (b1 k) := by
        rw [Algebra.TensorProduct.basis_apply]
        rfl
      rw [hk, Module.Basis.constr_basis]
    intro x
    exact LinearMap.congr_fun hcomp x
  have dec : ∀ (φ : Module.Dual ℝ (Phi A × Fin n → ℂ)) p (w : ℂ),
      φ (Pi.single p w) = w.re * φ (Pi.single p 1) + w.im * φ (Pi.single p Complex.I) := by
    intro φ p w
    have hw : (Pi.single p w : Phi A × Fin n → ℂ) =
        w.re • (Pi.single p (1 : ℂ) : Phi A × Fin n → ℂ) +
          w.im • (Pi.single p Complex.I : Phi A × Fin n → ℂ) := by
      ext q
      by_cases hq : q = p
      · subst hq
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
        apply Complex.ext <;> simp
      · simp [Pi.single_apply, hq]
    rw [hw, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hg : Function.Injective
      (Sum.elim (fun τ : Phi A => τ.1) (fun τ : Phi A => ComplexEmbedding.conjugate τ.1)) := by
    have hcross : ∀ a b : Phi A, a.1 ≠ ComplexEmbedding.conjugate b.1 := by
      intro a b h
      have h2 := RingHom.congr_fun h (A.ω : E)
      rw [ComplexEmbedding.conjugate_coe_eq, a.2, b.2] at h2
      have h3 := congrArg Complex.im h2
      rw [Complex.conj_im] at h3
      exact him (by linarith)
    rintro (a | a) (b | b) h
    · exact congrArg _ (Subtype.ext h)
    · exact absurd h (hcross a b)
    · exact absurd h.symm (hcross b a)
    · simp only [Sum.elim_inr] at h
      have h' : (a.1 : E →+* ℂ) = b.1 := by
        ext x
        have hx := RingHom.congr_fun h x
        rw [ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq] at hx
        simpa using congrArg (starRingEnd ℂ) hx
      exact congrArg _ (Subtype.ext h')
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
    have hvan : ∀ y, φ (L y) = 0 := by
      intro y
      have hm : φ (L y) ∈ (LinearMap.range L).map φ := ⟨L y, ⟨y, rfl⟩, rfl⟩
      rw [hφ] at hm
      exact (Submodule.mem_bot ℝ).mp hm
    have huv : ∀ i : Fin n, ∀ τ : Phi A,
        φ (Pi.single (τ, i) 1) = 0 ∧ φ (Pi.single (τ, i) Complex.I) = 0 := by
      intro i
      refine realForm_eq_zero (fun τ : Phi A => τ.1) hg _ _ fun x => ?_
      have h1 := hvan (1 ⊗ₜ Pi.single i x)
      rw [hL] at h1
      have hFx : F (Pi.single i x) = ∑ τ : Phi A, Pi.single (τ, i) (τ.1 (x : E)) := by
        ext ⟨τ', i'⟩
        rw [Finset.sum_apply]
        by_cases hi : i' = i
        · subst hi
          rw [Finset.sum_eq_single τ']
          · simp [F]
          · intro τ _ hτ
            simp [Pi.single_apply, hτ]
          · simp
        · simp [F, Pi.single_apply, hi]
      rw [hFx, map_sum] at h1
      rw [← h1]
      exact Finset.sum_congr rfl fun τ _ => by rw [dec φ (τ, i) (τ.1 (x : E))]; ring
    apply hφ0
    refine LinearMap.ext fun z => ?_
    rw [LinearMap.zero_apply, ← Finset.univ_sum_single z, map_sum]
    refine Finset.sum_eq_zero fun p _ => ?_
    obtain ⟨τ, i⟩ := p
    rw [dec, (huv i τ).1, (huv i τ).2]
    simp
  have hdim : Module.finrank ℝ (ℝ ⊗[ℤ] (Fin n → 𝓞 E)) =
      Module.finrank ℝ (Phi A × Fin n → ℂ) := by
    rw [Module.finrank_eq_card_basis b1,
      Module.finrank_eq_card_basis (Pi.basis fun _ : Phi A × Fin n => Complex.basisOneI)]
    simp only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Fintype.card_fin, Fintype.card_prod]
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, ← hrank, hcardPhi]
    ring
  refine ⟨LinearEquiv.ofBijective L
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩, ?_⟩
  intro x τ i
  show L (1 ⊗ₜ x) (τ, i) = _
  rw [hL]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepAdj
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pRepAdj :
    RepAdj := by
  intro E _ _ _ A n rep hrep x a b
  obtain ⟨β, h1, h2⟩ := hrep
  have key : ∀ z w, LinearMap.BilinForm.baseChange ℚ (A.EF n) z w =
      Algebra.trace ℚ E (A.δ * ∑ i, (A.hd n i : E) * β z i * IsCMField.complexConj E (β w i)) := by
    have hσq : ∀ (q : ℚ) (b : E), IsCMField.complexConj E (q • b) = q • IsCMField.complexConj E b := by
      intro q b
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      simp
    have hEF : ∀ v u : Fin n → 𝓞 E, ((A.EF n v u : ℤ) : ℚ) =
        Algebra.trace ℚ E (A.δ * ∑ i, (A.hd n i : E) * v i * IsCMField.complexConj E (u i)) := by
      intro v u
      simp only [Arith.EF, LinearMap.mk₂_apply, A.trd_spec]
      push_cast
      simp only [A.bar_eq]
    intro z w
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp [ha, hb, add_mul, Finset.sum_add_distrib, mul_add]
    | tmul q v =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp [ha, hb, mul_add, Finset.sum_add_distrib]
      | tmul r u =>
        rw [LinearMap.BilinForm.baseChange_tmul]
        have e1 : q ⊗ₜ[ℤ] v = q • ((1:ℚ) ⊗ₜ[ℤ] v) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have e2 : r ⊗ₜ[ℤ] u = r • ((1:ℚ) ⊗ₜ[ℤ] u) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [e1, e2, map_smul, map_smul]
        simp only [Pi.smul_apply, h1, hσq]
        have hS : ∑ x, (A.hd n x : E) * q • (v x : E) * r • IsCMField.complexConj E (u x : E) =
            (q * r) • ∑ x, (A.hd n x : E) * v x * IsCMField.complexConj E (u x : E) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [Algebra.smul_def, map_mul]
          ring
        rw [hS, mul_smul_comm, map_smul, ← hEF, zsmul_eq_mul, smul_eq_mul]
        ring
  have hreal : ∀ i, IsCMField.complexConj E (A.hd n i : E) = A.hd n i := by
    intro i
    have hc : IsCMField.complexConj E (A.c : E) = A.c := by
      rw [← A.bar_eq, A.c_real]
    simp only [Arith.hd, Arith.dg]
    split_ifs <;> simp [hc]
  have hc0 : (A.c : E) ≠ 0 := by
    intro h
    have := A.c_neg
    rw [h, map_zero] at this
    simp at this
  have hne : ∀ i, (A.hd n i : E) ≠ 0 := by
    intro i
    simp only [Arith.hd, Arith.dg]
    split_ifs <;> simp [hc0]
  rw [key, key, h2, h2]
  congr 2
  generalize β a = p
  generalize β b = s
  have hD : ∀ d : Fin n → E, (∀ m, d m ≠ 0) → (diagonal d)⁻¹ = diagonal (fun m => (d m)⁻¹) := by
    intro d hd
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext m
    exact inv_mul_cancel₀ (hd m)
  have hx : ∀ j, (MulOpposite.unop ((hermStar (A.H n) (by
      simp only [Arith.H, Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => hne i)) x) *ᵥ s) j =
      (A.hd n j : E)⁻¹ * ∑ k, IsCMField.complexConj E (x k j) * A.hd n k * s k := by
    intro j
    simp only [hermStar, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op, Arith.H]
    rw [Matrix.diagonal_map (map_zero _)]
    simp only [Function.comp_def, RingHom.coe_coe, hreal]
    rw [hD _ hne, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
    rw [show ∀ d : Fin n → E, diagonal d *ᵥ s = fun m => d m * s m from fun d => funext (Matrix.mulVec_diagonal d s)]
    simp only [Matrix.mulVec, dotProduct, transpose_apply, map_apply, RingHom.coe_coe]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [hx]
  simp only [map_mul, map_inv₀, map_sum, hreal, IsCMField.complexConj_apply_apply, Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have := hne j
  field_simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepLaws
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma beta_baseChange {E : Type} [Field E] [NumberField E] {n : ℕ}
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E))
    (hβ : ∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E)) (b : 𝓞 E)
    (z : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) :
    β ((DistribMulAction.toLinearMap ℤ (Fin n → 𝓞 E) b).baseChange ℚ z) = (b : E) • β z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul q v =>
    have h1 : ∀ w : Fin n → 𝓞 E, q ⊗ₜ[ℤ] w = q • ((1 : ℚ) ⊗ₜ[ℤ] w) := by
      intro w
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h2 : (DistribMulAction.toLinearMap ℤ (Fin n → 𝓞 E) b).baseChange ℚ (q ⊗ₜ[ℤ] v)
        = q ⊗ₜ[ℤ] (b • v) := by
      rw [LinearMap.baseChange_tmul]
      rfl
    rw [h2, h1 (b • v), h1 v, map_smul, map_smul]
    funext i
    simp only [Pi.smul_apply, hβ]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingOfIntegers.coe_eq_algebraMap, Rat.smul_def, mul_left_comm, Algebra.smul_def]

theorem UpperTheory.Gal.W2.Seed.pRepLaws :
    RepLaws := by
  rintro E _ _ _ A n rep ⟨β, hβ, hr⟩
  have hβ1 : ∀ v : Fin n → 𝓞 E, β (1 ⊗ₜ v) = fun i => (v i : E) := fun v => funext (hβ v)
  have hsc : ∀ c : 𝓞 E, rep (algebraMap E (Matrix (Fin n) (Fin n) E) c)
      = (DistribMulAction.toLinearMap ℤ (Fin n → 𝓞 E) c).baseChange ℚ := by
    intro c
    refine LinearMap.ext fun z => β.injective ?_
    rw [hr, beta_baseChange β hβ c z, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  refine ⟨?_, ?_, hsc, ?_⟩
  · intro x y hxy
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    obtain ⟨z, rfl⟩ := β.surjective w
    simp only [Matrix.toLin'_apply]
    rw [← hr, ← hr, hxy]
  · intro M
    constructor
    · rintro ⟨x, rfl⟩ b
      rw [← hsc, ← map_mul, ← map_mul, Algebra.commutes]
    · intro hM
      let F0 : (Fin n → E) →ₗ[ℚ] (Fin n → E) := β.toLinearMap ∘ₗ M ∘ₗ β.symm.toLinearMap
      have hF0 : ∀ (b : 𝓞 E) w, F0 ((b : E) • w) = (b : E) • F0 w := by
        intro b w
        obtain ⟨z, rfl⟩ := β.surjective w
        have h := congrArg (fun N => β (N z)) (hM b)
        simp only [Module.End.mul_apply] at h
        rw [beta_baseChange β hβ] at h
        simp only [F0, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        rw [← beta_baseChange β hβ, LinearEquiv.symm_apply_apply, h]
      have hF : ∀ (e : E) w, F0 (e • w) = e • F0 w := by
        intro e w
        obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
        have hd0 : (algebraMap (𝓞 E) E d) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
        apply smul_right_injective (Fin n → E) hd0
        change algebraMap (𝓞 E) E d • F0 _ = algebraMap (𝓞 E) E d • _
        rw [smul_smul, mul_div_cancel₀ _ hd0]
        have h2 := hF0 d ((algebraMap (𝓞 E) E b / algebraMap (𝓞 E) E d) • w)
        have h3 := hF0 b w
        change F0 (algebraMap (𝓞 E) E d • _) = algebraMap (𝓞 E) E d • _ at h2
        change F0 (algebraMap (𝓞 E) E b • _) = algebraMap (𝓞 E) E b • _ at h3
        rw [← h2, smul_smul, mul_div_cancel₀ _ hd0, h3]
      let F : (Fin n → E) →ₗ[E] (Fin n → E) :=
        { toFun := F0, map_add' := F0.map_add, map_smul' := hF }
      refine ⟨Matrix.toLin'.symm F, ?_⟩
      refine LinearMap.ext fun z => β.injective ?_
      rw [hr]
      have hx : (Matrix.toLin'.symm F) *ᵥ β z = F (β z) := by
        rw [← Matrix.toLin'_apply, LinearEquiv.apply_symm_apply]
      rw [hx]
      simp [F, F0]
  · intro x v
    apply β.injective
    rw [hr, hβ1, hβ1]
    funext i
    exact (RingHom.map_mulVec (algebraMap (𝓞 E) E) x v i).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSetupBasic
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pSetupBasic :
    SetupBasic := by
  intro E _ _ _ A n p _ S
  have key : ∀ v : InfinitePlace E, sigPosH (S.G.gram_herm v) = 1 ↔ v = InfinitePlace.mk A.τ₀ := by
    intro v
    show sigPos (A.herm n) v.embedding = 1 ↔ _
    have h := S.sig v.embedding
    rw [InfinitePlace.mk_embedding] at h
    constructor
    · intro h1
      by_contra hne
      have h0 := (h.2 hne).1
      omega
    · intro hv
      exact (h.1 hv).1
  refine ⟨?_, (key _).2 rfl, fun h => ?_⟩
  · exact Fintype.card_eq_one_iff.2 ⟨⟨InfinitePlace.mk A.τ₀, (key _).2 rfl⟩,
      fun w => Subtype.ext ((key w.1).1 w.2)⟩
  · have h2 : 2 * 1 < Module.finrank ℚ E := by simpa using h
    exact ⟨Or.inl h2, Or.inl h2⟩
end

