import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle0002
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.DedekindDomain.Instances
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.CardOfIsFiniteLength
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.FiniteStability

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LengthQuotientSpanEqFinsumValuation
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M
open scoped nonZeroDivisors

private theorem length_quotient_eq_norm_valuation {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {D : Type} [CommRing D] [Algebra O D] [Module.Finite O D] [Module.Free O D] (a : D) :
    Module.length O (D ⧸ Ideal.span {a}) = IsDiscreteValuationRing.addVal O (Algebra.norm O a) := by
  classical
  let b := Module.Free.chooseBasis O D
  let f : D →ₗ[O] D := Algebra.lmul O D a
  let Φ := LinearMap.toMatrix b b f
  have hdet : Algebra.norm O a = Φ.det := by
    rw [Algebra.norm_apply, LinearMap.det_toMatrix]
  have hmul : Φ.mulVecLin = b.equivFun.toLinearMap ∘ₗ f ∘ₗ b.equivFun.symm.toLinearMap := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := b.equivFun.surjective y
    simp only [Matrix.mulVecLin_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply]
    simp only [Module.Basis.equivFun_apply]
    exact LinearMap.toMatrix_mulVec_repr b b f x
  have hI : (Ideal.span {a}).restrictScalars O = LinearMap.range f := by
    ext x
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton', LinearMap.mem_range, f,
      Algebra.coe_lmul_eq_mul]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm _ _⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm _ _⟩
  have hmap : (LinearMap.range f).map b.equivFun.toLinearMap = LinearMap.range Φ.mulVecLin := by
    rw [hmul, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, ← LinearMap.range_eq_map]
  let e : (D ⧸ Ideal.span {a}) ≃ₗ[O] KStar.Selmer.H2 Φ :=
    (Submodule.Quotient.restrictScalarsEquiv O (Ideal.span {a})).symm.trans
      ((Submodule.quotEquivOfEq _ _ hI).trans (Submodule.Quotient.equiv _ _ b.equivFun hmap))
  rw [e.length_eq, hdet]
  exact KStar.Selmer.length_cokernel_eq_addVal_det Φ

private theorem algHom_finite_domain_injective {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [FaithfulSMul O K]
    {D : Type} [CommRing D] [IsDomain D] [Algebra O D] [Module.Finite O D] (σ : D →ₐ[O] K) :
    Function.Injective σ := by
  have : Algebra.IsIntegral O D := Algebra.IsIntegral.of_finite O D
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hker : (RingHom.ker σ).comap (algebraMap O D) = ⊥ := by
    ext c
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, Ideal.mem_bot]
    exact ⟨fun h => (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).1 h,
      fun h => by simp [h]⟩
  have hmem : x ∈ RingHom.ker σ := hx
  rw [Ideal.eq_bot_of_comap_eq_bot hker] at hmem
  exact hmem

attribute [local instance] FractionRing.liftAlgebra in
private theorem algebra_norm_eq_prod_embeddings {O : Type} [CommRing O] [IsDomain O] [CharZero O]
    {K : Type} [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
    {D : Type} [CommRing D] [IsDomain D] [Algebra O D] [Module.Finite O D] [FaithfulSMul O D] [Module.Free O D]
    (a : D) : ∃ _ : Fintype (D →ₐ[O] K), algebraMap O K (Algebra.norm O a) = ∏ σ : D →ₐ[O] K, σ a := by
  classical
  have : IsScalarTower O (FractionRing O) K := FractionRing.isScalarTower_liftAlgebra O K
  let M := Algebra.algebraMapSubmonoid D O⁰
  let L := Localization M
  have hM : M ≤ D⁰ := by
    rintro _ ⟨m, hm, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O D)).2 (nonZeroDivisors.ne_zero hm))
  have : IsDomain L := IsLocalization.isDomain_localization hM
  have hF : IsField L := by
    have : Module.Finite (FractionRing O) L := Module.Finite.of_isLocalization O D O⁰
    exact isField_of_isIntegral_of_isField' (Field.toIsField (FractionRing O))
  letI : Field L := hF.toField
  letI : Algebra (FractionRing O) L := localizationAlgebra O⁰ D
  have : Module.Finite (FractionRing O) L := Module.Finite.of_isLocalization O D O⁰
  have hN : Algebra.norm (FractionRing O) (algebraMap D L a) =
      algebraMap O (FractionRing O) (Algebra.norm O a) :=
    Algebra.norm_localization O O⁰ a
  have hE := Algebra.norm_eq_prod_embeddings (FractionRing O) K (algebraMap D L a)
  let r : (L →ₐ[FractionRing O] K) → (D →ₐ[O] K) := fun τ =>
    (τ.restrictScalars O).comp (IsScalarTower.toAlgHom O D L)
  have hinj : Function.Injective r := by
    intro τ₁ τ₂ h
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext M
    ext d
    exact DFunLike.congr_fun h d
  have hsurj : Function.Surjective r := by
    intro σ
    have hu : ∀ y : M, IsUnit ((σ : D →+* K) y) := by
      rintro ⟨_, m, hm, rfl⟩
      rw [AlgHom.coe_toRingHom, AlgHom.commutes]
      exact isUnit_iff_ne_zero.2
        ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective O K)).2 (nonZeroDivisors.ne_zero hm))
    let τ₀ : L →+* K := IsLocalization.lift hu
    have hc : τ₀.comp (algebraMap (FractionRing O) L) = algebraMap (FractionRing O) K := by
      apply IsLocalization.ringHom_ext O⁰
      ext c
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply O D L, IsLocalization.lift_eq]
      simp
    refine ⟨{ τ₀ with commutes' := fun x => DFunLike.congr_fun hc x }, ?_⟩
    ext d
    simp [r, τ₀, IsLocalization.lift_eq]
  letI inst : Fintype (D →ₐ[O] K) := Fintype.ofSurjective r hsurj
  refine ⟨inst, ?_⟩
  rw [IsScalarTower.algebraMap_apply O (FractionRing O) K, ← hN, hE]
  exact Fintype.prod_bijective r ⟨hinj, hsurj⟩ _ _ (fun τ => rfl)

theorem UpperTheory.V.Alg.M.length_quotient_span_eq_finsum_valuation :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v →
    ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra O D] [Module.Finite O D] [FaithfulSMul O D] (a : D), a ≠ 0 →
      Finite (D →ₐ[O] K) ∧ Module.length O (D ⧸ Ideal.span {a}) ≠ ⊤ ∧
      (((Module.length O (D ⧸ Ideal.span {a})).toNat : ℕ) : ℝ) = ∑ᶠ σ : D →ₐ[O] K, v (σ a) := by
  intro O _ _ _ _ _ K _ _ _ _ v hv D _ _ _ _ _ a ha
  classical
  have : Module.Free O D := inferInstance
  obtain ⟨hF, hN⟩ := algebra_norm_eq_prod_embeddings (O := O) (K := K) a
  have hn : Algebra.norm O a ≠ 0 := Algebra.norm_ne_zero_iff.2 ha
  have hσ : ∀ σ : D →ₐ[O] K, σ a ≠ 0 := fun σ h => ha (algHom_finite_domain_injective σ (h.trans (map_zero _).symm))
  have h1 : v 1 = 0 := by
    have := hv.mul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    linarith
  have hp : ∀ s : Finset (D →ₐ[O] K), v (∏ σ ∈ s, σ a) = ∑ σ ∈ s, v (σ a) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h1
    | insert τ s hτ ih =>
      rw [Finset.prod_insert hτ, Finset.sum_insert hτ,
        hv.mul _ _ (hσ τ) (Finset.prod_ne_zero_iff.2 fun σ _ => hσ σ), ih]
  rw [length_quotient_eq_norm_valuation]
  refine ⟨inferInstance, fun h => hn (IsDiscreteValuationRing.addVal_eq_top_iff.1 h), ?_⟩
  rw [← hv.base _ hn, hN, hp, finsum_eq_sum_of_fintype]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Mprime
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem der_satSq {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] (x : A →ₐ[O] O)
    (D : A →ₗ[O] O) (hD : D ∈ PtDer x O) (f : A) (hf : f ∈ satSq x) : D f = 0 := by
  obtain ⟨c, hc, hcf⟩ := hf
  have hD' : ∀ f g, D (f * g) = x f • D g + x g • D f := hD
  have key : ∀ g ∈ RingHom.ker x ^ 2, D g = 0 := by
    intro g hg
    rw [sq] at hg
    refine Submodule.mul_induction_on hg ?_ ?_
    · intro a ha b hb
      have ha' : x a = 0 := ha
      have hb' : x b = 0 := hb
      rw [hD', ha', hb']; simp
    · intro a b ha hb
      rw [map_add, ha, hb, add_zero]
  have := key _ hcf
  rw [map_smul, smul_eq_mul] at this
  exact (mul_eq_zero.1 this).resolve_left hc

private theorem len_le_of_inj {O : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)]
    {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (hN : Module.length O N ≠ ⊤) (ψ : M → N) (hψ : Function.Injective ψ) :
    Module.length O M ≤ Module.length O N := by
  obtain ⟨hfN, n, hn, hcn⟩ := Formalism.MainNotions.V.Pf.V2.card_of_isFiniteLength (Module.length_ne_top_iff.1 hN)
  have hfM : Finite M := Finite.of_injective ψ hψ
  have hM : IsFiniteLength O M := isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩
  obtain ⟨_, m, hm, hcm⟩ := Formalism.MainNotions.V.Pf.V2.card_of_isFiniteLength hM
  have hle := Nat.card_le_card_of_injective ψ hψ
  rw [hcm, hcn] at hle
  have h1 : 1 < Nat.card (ResidueField O) := Finite.one_lt_card
  rw [hm, hn]
  exact_mod_cast (Nat.pow_le_pow_iff_right h1).1 hle

theorem UpperTheory.V.Alg.M.mprime_holds :
    LemmaM' := by
  intro O _ _ _ _ A X _ _ _ _ 𝒜 _ x j hx ι F hF c hc M _ _ D hD hDF hlift
  by_cases htop : cotLen x 𝒜 j F = ⊤
  · rw [htop]; exact le_top
  have hsat : ∀ μ, satSq x ≤ LinearMap.ker (D μ) := by
    intro μ f hf
    obtain ⟨D', hD', -, h⟩ := hlift μ
    rw [LinearMap.mem_ker, h, der_satSq x D' hD' f hf, map_zero]
  have hspan : ∀ μ, (cotSpan x F).comap (cotLat x 𝒜 j).subtype ≤
      LinearMap.ker (((satSq x).liftQ (D μ) (hsat μ)) ∘ₗ (cotLat x 𝒜 j).subtype) := by
    intro μ
    rw [LinearMap.ker_comp]
    refine Submodule.comap_mono ?_
    rw [cotSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hDF μ i
  let ψ : M → ((cotLat x 𝒜 j ⧸ (cotSpan x F).comap (cotLat x 𝒜 j).subtype) →ₗ[O] O ⧸ Ideal.span {c}) :=
    fun μ => Submodule.liftQ _ _ (hspan μ)
  have hψ : Function.Injective ψ := by
    intro μ ν h
    apply hD
    have hj : ∀ f ∈ 𝒜 j, D μ f = D ν f := fun f hf =>
      LinearMap.congr_fun h (Submodule.Quotient.mk ⟨(satSq x).mkQ f, f, ⟨hf, hx f hf⟩, rfl⟩)
    have hi : ∀ μ i, i ≠ j → ∀ f ∈ 𝒜 i, D μ f = 0 := by
      intro μ i hi f hf
      obtain ⟨D', -, hw, h⟩ := hlift μ
      rw [h, hw i hi f hf, map_zero]
    refine LinearMap.ext fun f => ?_
    induction f using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => rw [map_zero, map_zero]
    | @homogeneous i m =>
      by_cases hij : i = j
      · subst hij; exact hj _ m.2
      · rw [hi μ i hij _ m.2, hi ν i hij _ m.2]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hc hp
  have hQ : Module.length O ((O ⧸ maximalIdeal O) →ₗ[O] (O ⧸ Ideal.span {c})) ≤ 1 := by
    rw [Ideal.span_singleton_eq_span_singleton.2 hk]
    exact Formalism.MainNotions.V.Pf.V2.length_hom_residue_le p hp.maximalIdeal_eq hp.ne_zero k
  have hle := Formalism.MainNotions.V.Pf.V2.length_hom_le hQ (Module.length_ne_top_iff.1 htop)
  exact (len_le_of_inj (ne_top_of_le_ne_top htop hle) ψ hψ).trans hle
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.NegWeightLe
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem UpperTheory.V.Alg.M.neg_weight_le {τ : Type} (wt : τ → ℤ) (ν : τ →₀ ℕ) :
    -Finsupp.weight wt ν ≤ ((Finsupp.weight (negW wt) ν : ℕ) : ℤ) := by
  simp only [Finsupp.weight_apply, Finsupp.sum]
  push_cast
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hi : -wt i ≤ ((negW wt i : ℕ) : ℤ) := by
    simp only [negW]
    exact Int.self_le_toNat _
  have hc : (0 : ℤ) ≤ (ν i : ℤ) := Int.natCast_nonneg _
  simp only [nsmul_eq_mul, smul_eq_mul]
  push_cast
  nlinarith

theorem UpperTheory.V.Alg.M.fil_holds :
    ∀ (E τ : Type) [CommRing E] (wt : τ → ℤ) (a b : ℕ) (g h : MvPowerSeries τ E), g ∈ fil E wt a → h ∈ fil E wt b →
      g * h ∈ fil E wt (a + b) ∧ ∀ j : ℤ, g ∈ wtPart E wt j → g ∈ fil E wt (-j).toNat := by
  intro E τ _ wt a b g h hg hh
  classical
  refine ⟨?_, ?_⟩
  · intro ν hν
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hw : Finsupp.weight (negW wt) p.1 + Finsupp.weight (negW wt) p.2 =
        Finsupp.weight (negW wt) ν := by
      rw [← hp, map_add]
    by_cases h1 : Finsupp.weight (negW wt) p.1 < a
    · rw [hg p.1 h1, zero_mul]
    · rw [hh p.2 (by omega), mul_zero]
  · intro j hj ν hν
    by_contra hne
    have hwj : Finsupp.weight wt ν = j := by
      by_contra h'
      exact hne (hj ν h')
    have key := neg_weight_le wt ν
    rw [hwj] at key
    omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.NsPoint
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M
open scoped TensorProduct

private theorem ns_point (K R : Type) [Field K] [IsAlgClosed K] [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (Q : Ideal R) (hQ : Q.IsPrime) (x : R) (hx : x ∉ Q) :
    ∃ ψ : R →ₐ[K] K, (∀ y ∈ Q, ψ y = 0) ∧ ψ x ≠ 0 := by
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  have hj : Q.jacobson = Q := IsJacobsonRing.out inferInstance hQ.isRadical
  rw [← hj, Ideal.jacobson, Ideal.mem_sInf] at hx
  push Not at hx
  obtain ⟨M, ⟨hQM, hM⟩, hxM⟩ := hx
  letI : Field (R ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite K (R ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ M)
  haveI : Algebra.IsAlgebraic K (R ⧸ M) := Algebra.IsAlgebraic.of_finite K _
  let e : (R ⧸ M) →ₐ[K] K := IsAlgClosed.lift
  refine ⟨e.comp (Ideal.Quotient.mkₐ K M), fun y hy => ?_, ?_⟩
  · have : Ideal.Quotient.mk M y = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hQM hy)
    simp [this]
  · have : Ideal.Quotient.mk M x ≠ 0 := fun h => hxM (Ideal.Quotient.eq_zero_iff_mem.1 h)
    simpa using this

private theorem ns_prime (B A K : Type) [CommRing B] [CommRing A] [Field K] [Algebra B A] [Algebra B K]
    (P : Ideal A) [P.IsPrime] (hP : ∀ b, algebraMap B A b ∈ P ↔ algebraMap B K b = 0) :
    ∃ Q : Ideal (K ⊗[B] A), Q.IsPrime ∧ ∀ a : A, (1 : K) ⊗ₜ[B] a ∈ Q ↔ a ∈ P := by
  let p : Ideal B := P.under B
  haveI : p.IsPrime := inferInstance
  have h1 : p ≤ RingHom.ker (algebraMap B K) := fun b hb => (hP b).1 hb
  have h2 : p.primeCompl ≤ (IsUnit.submonoid K).comap (algebraMap B K) := fun b hb =>
    (isUnit_iff_ne_zero.2 (fun h => hb ((hP b).2 h)) : IsUnit (algebraMap B K b))
  have h1' : p ≤ RingHom.ker (algebraMap B P.ResidueField) := fun b hb => by
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply B A, Ideal.algebraMap_residueField_eq_zero]
    exact hb
  have h2' : p.primeCompl ≤ (IsUnit.submonoid P.ResidueField).comap (algebraMap B P.ResidueField) :=
    fun b hb => (isUnit_iff_ne_zero.2 (fun h => hb (by
      rw [IsScalarTower.algebraMap_apply B A, Ideal.algebraMap_residueField_eq_zero] at h
      exact h)) : IsUnit (algebraMap B P.ResidueField b))
  letI aK : Algebra p.ResidueField K := (Ideal.ResidueField.lift p _ h1 h2).toAlgebra
  letI aL : Algebra p.ResidueField P.ResidueField := (Ideal.ResidueField.lift p _ h1' h2').toAlgebra
  haveI : IsScalarTower B p.ResidueField K := IsScalarTower.of_algebraMap_eq fun b =>
    (Ideal.ResidueField.lift_algebraMap p _ h1 h2 b).symm
  haveI : IsScalarTower B p.ResidueField P.ResidueField := IsScalarTower.of_algebraMap_eq fun b =>
    (Ideal.ResidueField.lift_algebraMap p _ h1' h2' b).symm
  let T := K ⊗[p.ResidueField] P.ResidueField
  haveI : Nontrivial T := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
    p.ResidueField K P.ResidueField (RingHom.injective _) (RingHom.injective _)
  obtain ⟨N, hN⟩ := Ideal.exists_maximal T
  let i1 : K →ₐ[B] T := (Algebra.TensorProduct.includeLeft (S := B))
  let j : P.ResidueField →ₐ[p.ResidueField] T := Algebra.TensorProduct.includeRight
  let i2 : A →ₐ[B] T := (j.restrictScalars B).comp (IsScalarTower.toAlgHom B A P.ResidueField)
  let φ : K ⊗[B] A →ₐ[B] T := Algebra.TensorProduct.lift i1 i2 (fun _ _ => Commute.all _ _)
  refine ⟨N.comap φ, Ideal.comap_isPrime _ _, fun a => ?_⟩
  have hφ : φ ((1 : K) ⊗ₜ[B] a) = j (algebraMap A P.ResidueField a) := by
    simp [φ, i2]
  rw [Ideal.mem_comap, hφ]
  constructor
  · intro h
    by_contra ha
    have hu : IsUnit (algebraMap A P.ResidueField a) :=
      isUnit_iff_ne_zero.2 (fun h => ha (Ideal.algebraMap_residueField_eq_zero.1 h))
    exact hN.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hu.map j))
  · intro h
    rw [Ideal.algebraMap_residueField_eq_zero.2 h, map_zero]
    exact N.zero_mem

theorem UpperTheory.V.Alg.M.ns_holds :
    ∀ (O B A K : Type) [CommRing O] [CommRing B] [CommRing A] [Field K] [IsAlgClosed K] [Algebra O B] [Algebra B A]
      [Algebra O A] [IsScalarTower O B A] [Algebra O K] [Algebra.FiniteType B A] (σ : B →ₐ[O] K) (J : Ideal A) (f : A),
      (∀ b, σ b = 0 → algebraMap B A b ∈ J) → (∀ (b : B) (n : ℕ), σ b ≠ 0 → algebraMap B A b * f ^ n ∉ J) →
      ∃ ξ : A →ₐ[O] K, (∀ b, ξ (algebraMap B A b) = σ b) ∧ (∀ g ∈ J, ξ g = 0) ∧ ξ f ≠ 0 := by
  intro O B A K _ _ _ _ _ _ _ _ _ _ _ σ J f h0 h1
  let S : Submonoid A :=
    { carrier := {a | ∃ (b : B) (n : ℕ), σ b ≠ 0 ∧ a = algebraMap B A b * f ^ n}
      one_mem' := ⟨1, 0, by simp, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨b, n, hb, rfl⟩ ⟨c, m, hc, rfl⟩
        exact ⟨b * c, n + m, by simp [hb, hc], by rw [map_mul]; ring⟩ }
  have hd : Disjoint (J : Set A) (S : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ha ⟨b, n, hb, rfl⟩
    exact h1 b n hb ha
  obtain ⟨P, hP, hJP, hPS⟩ := Ideal.exists_le_prime_disjoint J S hd
  rw [Set.disjoint_left] at hPS
  letI : Algebra B K := σ.toRingHom.toAlgebra
  have hσ : ∀ b, algebraMap B K b = σ b := fun _ => rfl
  haveI : IsScalarTower O B K := IsScalarTower.of_algebraMap_eq fun o => by
    rw [hσ, AlgHom.commutes]
  obtain ⟨Q, hQ, hQP⟩ := ns_prime B A K P (fun b => by
    rw [hσ]
    constructor
    · intro hb
      by_contra hne
      exact hPS hb ⟨b, 0, hne, by simp⟩
    · intro hb
      exact hJP (h0 b hb))
  have hf : f ∉ P := fun h => hPS h ⟨1, 1, by simp, by simp⟩
  obtain ⟨ψ, hψ0, hψ1⟩ := ns_point K (K ⊗[B] A) Q hQ ((1 : K) ⊗ₜ[B] f) (fun h => hf ((hQP f).1 h))
  let ξ : A →ₐ[B] K := (ψ.restrictScalars B).comp Algebra.TensorProduct.includeRight
  refine ⟨ξ.restrictScalars O, fun b => ?_, fun g hg => ?_, hψ1⟩
  · exact (ξ.commutes b).trans (hσ b)
  · exact hψ0 _ ((hQP g).2 (hJP hg))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.NzCoeffMul
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem nz_coeff_mul {τ E : Type} [CommRing E] (i : τ) (f g : MvPowerSeries τ E)
    (hf : MvPowerSeries.constantCoeff f = 0) (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) = 0 := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd := congrArg Finsupp.degree h
  rw [map_add, Finsupp.degree_single] at hd
  by_cases h1 : Finsupp.degree p.1 = 0
  · rw [(Finsupp.degree_eq_zero_iff _).1 h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_mul]
  · have h2 : Finsupp.degree p.2 = 0 := by omega
    rw [(Finsupp.degree_eq_zero_iff _).1 h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg, mul_zero]

private theorem nz_comp {O A τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O) (wt : τ → ℤ)
    (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (h : IsChart0 𝒜 x wt φ) (i : τ) :
    ∃ f ∈ 𝒜 (wt i), MvPowerSeries.coeff (Finsupp.single i 1) (φ f) ≠ 0 := by
  classical
  obtain ⟨f, hf, -⟩ := h.onto i
  rw [← DirectSum.sum_support_decompose 𝒜 f, map_sum, map_sum] at hf
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hf
  have hm := (DirectSum.decompose 𝒜 f j).2
  have hw : wt i = j := by
    by_contra hne
    exact hj (h.graded j _ hm _ (by simpa [Finsupp.weight_single] using hne))
  exact ⟨_, hw ▸ hm, hj⟩

theorem UpperTheory.V.Alg.M.nz_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
    1 ≤ Nat.card {i // wt i = -1} → 1 ≤ Nat.card {i // wt i = 1} → SpansCot x 𝒜 (-1) Q.F →
    ∀ a ∈ 𝒜 0, ∃ a' ∈ 𝒜 0, a' - a ∈ Q.ideal ∧ x a' = x a ∧ φ a' ≠ 0 := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q τ _ wt φ hφ hn hp hS a ha
  by_cases h0 : φ a = 0
  swap
  · exact ⟨a, ha, by simp, rfl, h0⟩
  obtain ⟨⟨i, hi⟩⟩ := (Nat.card_pos_iff.1 hn).1
  obtain ⟨⟨i', hi'⟩⟩ := (Nat.card_pos_iff.1 hp).1
  obtain ⟨f, hf, hf0⟩ := nz_comp 𝒜 x wt φ hφ i
  obtain ⟨g, hg, hg0⟩ := nz_comp 𝒜 x wt φ hφ i'
  rw [hi] at hf
  rw [hi'] at hg
  have hg1 : φ g ≠ 0 := fun h => hg0 (by rw [h, map_zero])
  have hinj : ∀ c : O, c ≠ 0 → ∀ y : FractionRing O, c • y = 0 → y = 0 := fun c hc y hy => by
    rw [Algebra.smul_def] at hy
    exact (mul_eq_zero.1 hy).resolve_left fun h => hc (IsFractionRing.injective O _ (h.trans (map_zero _).symm))
  have hF : ∃ k, φ (Q.F k) ≠ 0 := by
    by_contra hall
    push Not at hall
    let L : A →ₗ[O] FractionRing O :=
      ((MvPowerSeries.coeff (Finsupp.single i 1)).restrictScalars O) ∘ₗ φ.toLinearMap
    have hL : ∀ y, L y = MvPowerSeries.coeff (Finsupp.single i 1) (φ y) := fun _ => rfl
    have hsq : ∀ y ∈ RingHom.ker x ^ 2, L y = 0 := by
      intro y hy
      rw [sq] at hy
      refine Submodule.mul_induction_on hy (fun u hu v hv => ?_) (fun u v hu hv => by rw [map_add, hu, hv, add_zero])
      have hu' : x u = 0 := hu
      have hv' : x v = 0 := hv
      rw [hL, map_mul]
      exact nz_coeff_mul _ _ _ (by rw [hφ.const, hu', map_zero]) (by rw [hφ.const, hv', map_zero])
    have hk : satSq x ≤ LinearMap.ker L := by
      rintro y ⟨c, hc, hy⟩
      have := hsq _ hy
      rw [map_smul] at this
      exact hinj c hc _ this
    have hsp : cotSpan x Q.F ≤ LinearMap.ker ((satSq x).liftQ L hk) := by
      rw [cotSpan, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      show L (Q.F k) = 0
      rw [hL, hall k, map_zero]
    obtain ⟨c, hc, hcf⟩ := hS ((satSq x).mkQ f) ⟨f, ⟨hf, hW.fixed (-1) (by norm_num) f hf⟩, rfl⟩
    have := hsp hcf
    rw [LinearMap.mem_ker, map_smul] at this
    exact hf0 (hinj c hc _ this)
  obtain ⟨k, hk⟩ := hF
  have hm : g * Q.F k ∈ 𝒜 0 := by simpa using SetLike.GradedMul.mul_mem hg (Q.hF k)
  refine ⟨a + g * Q.F k, add_mem ha hm, ?_, ?_, ?_⟩
  · rw [add_sub_cancel_left]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · rw [map_add, map_mul, hW.fixed 1 one_ne_zero g hg, zero_mul, add_zero]
  · rw [map_add, h0, zero_add, map_mul]
    exact mul_ne_zero hg1 hk
end

