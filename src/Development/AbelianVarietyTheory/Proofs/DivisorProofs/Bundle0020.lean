import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAdjoinBaseChangeImage
section
open TensorProduct

namespace GlobalTheory

theorem etale_adjoin_baseChange_image (R S B : Type) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B] (A₀ : Subalgebra R S)
    (B₀ : Type) [CommRing B₀] [Algebra A₀ B₀] [Algebra.Etale A₀ B₀] (e : B ≃ₐ[S] S ⊗[A₀] B₀)
    (S' : Subalgebra R S) (h : A₀ ≤ S') :
    ∃ (_ : Algebra S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))))
      (_ : IsScalarTower R S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))))),
      Algebra.Etale S' ↥(Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))) := by
  set C := Algebra.adjoin R ((algebraMap S B) '' (S' : Set S) ∪
        Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))) with hC
  letI : Algebra A₀ S' := (Subalgebra.inclusion h).toRingHom.toAlgebra
  let ι : S' →ₐ[A₀] S :=
    { toRingHom := S'.val.toRingHom
      commutes' := fun _ => rfl }
  let Φ : S' ⊗[A₀] B₀ →ₐ[A₀] S ⊗[A₀] B₀ := Algebra.TensorProduct.map ι (AlgHom.id A₀ B₀)
  let Ψ : S' ⊗[A₀] B₀ →+* B := (e.symm : S ⊗[A₀] B₀ →+* B).comp Φ.toRingHom
  haveI : Module.Flat A₀ B₀ := inferInstance
  have hΦ : Function.Injective Φ := by
    have hl : (Φ.toLinearMap : S' ⊗[A₀] B₀ →ₗ[A₀] S ⊗[A₀] B₀) = LinearMap.rTensor B₀ ι.toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      rfl
    have : Function.Injective (LinearMap.rTensor B₀ ι.toLinearMap) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (fun a b hab => Subtype.ext hab)
    rw [← hl] at this
    exact this
  have hΨ : Function.Injective Ψ := e.symm.injective.comp hΦ
  have htmul : ∀ (s : S') (b : B₀), Ψ (s ⊗ₜ b) = algebraMap S B s * e.symm (1 ⊗ₜ b) := by
    intro s b
    have : ((s : S) ⊗ₜ[A₀] b : S ⊗[A₀] B₀) = algebraMap S (S ⊗[A₀] B₀) s * (1 ⊗ₜ b) := by
      simp [Algebra.TensorProduct.algebraMap_apply]
    show e.symm ((s : S) ⊗ₜ[A₀] b) = _
    rw [this, map_mul, AlgEquiv.commutes]
  have h1 : e.symm ((1 : S) ⊗ₜ[A₀] (1 : B₀)) = 1 := by
    rw [← Algebra.TensorProduct.one_def, map_one]
  have hsub : ∀ x, Ψ x ∈ C := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s b =>
      rw [htmul]
      exact C.mul_mem (Algebra.subset_adjoin (Or.inl ⟨s, s.2, rfl⟩))
        (Algebra.subset_adjoin (Or.inr ⟨b, rfl⟩))
    | add x y hx hy => rw [map_add]; exact C.add_mem hx hy
  have hsurj : (C : Set B) ⊆ Set.range Ψ := by
    have := Algebra.adjoin_eq_ring_closure (R := R)
      ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b)))
    intro y hy
    have hy' : y ∈ (C.toSubring) := hy
    rw [hC, this] at hy'
    have hle : Subring.closure (Set.range (algebraMap R B) ∪
        ((algebraMap S B) '' (S' : Set S) ∪ Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))))
        ≤ Ψ.range := by
      rw [Subring.closure_le]
      rintro z (⟨r, rfl⟩ | ⟨s, hs, rfl⟩ | ⟨b, rfl⟩)
      · refine ⟨(algebraMap R S' r) ⊗ₜ 1, ?_⟩
        rw [htmul, h1, mul_one, IsScalarTower.algebraMap_apply R S B]
        rfl
      · refine ⟨(⟨s, hs⟩ : S') ⊗ₜ 1, ?_⟩
        rw [htmul, h1, mul_one]
      · refine ⟨1 ⊗ₜ b, ?_⟩
        rw [htmul]; simp
    exact hle hy'
  let f : S' ⊗[A₀] B₀ →+* C := Ψ.codRestrict C.toSubring hsub
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => hΨ (congrArg Subtype.val hxy), ?_⟩
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hsurj hy
    exact ⟨x, rfl⟩
  let eqv : S' ⊗[A₀] B₀ ≃+* C := RingEquiv.ofBijective f hf
  letI alg : Algebra S' C := (f.comp (algebraMap S' (S' ⊗[A₀] B₀))).toAlgebra
  have tower : IsScalarTower R S' C := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    apply Subtype.ext
    show algebraMap R B r = Ψ (algebraMap S' (S' ⊗[A₀] B₀) (algebraMap R S' r))
    rw [Algebra.TensorProduct.algebraMap_apply, htmul, h1, mul_one,
      IsScalarTower.algebraMap_apply R S B]
    rfl
  refine ⟨alg, tower, ?_⟩
  let eA : S' ⊗[A₀] B₀ ≃ₐ[S'] C := AlgEquiv.ofRingEquiv (f := eqv) (fun _ => rfl)
  haveI : Algebra.Etale S' (S' ⊗[A₀] B₀) := Algebra.Etale.baseChange A₀ B₀ S'
  exact Algebra.Etale.of_equiv eA

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFibreEmbeddingsCard
section
open scoped TensorProduct

namespace GlobalTheory.EtaleFibre

theorem finrank_baseChange_field (A M L : Type*) [CommRing A] [IsDomain A] [AddCommGroup M]
    [Module A M] [Module.Finite A M] [Module.Flat A M] [Field L] [Algebra A L] :
    Module.finrank L (L ⊗[A] M) = Module.finrank A M := by
  have h := Module.rankAtStalk_baseChange (R := A) (M := M) (S := L) (⊥ : PrimeSpectrum L)
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq,
    Ideal.finrank_fiber_eq_finrank] at h
  exact h

theorem card_algHom (A B L : Type*) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Algebra.Etale A B] [Field L] [IsSepClosed L] [Algebra A L] :
    Finite (B →ₐ[A] L) ∧ Nat.card (B →ₐ[A] L) = Module.finrank A B := by
  have : IsArtinianRing (L ⊗[A] B) := .of_finite L _
  have := Fintype.ofFinite (PrimeSpectrum (L ⊗[A] B))
  have e : (B →ₐ[A] L) ≃ PrimeSpectrum (L ⊗[A] B) :=
    (AlgHom.liftEquiv A L B L).trans
      (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum L (L ⊗[A] B))
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, ← finrank_baseChange_field A B L,
    (Algebra.FormallyEtale.equivPiOfIsSepClosed L (L ⊗[A] B)).toLinearEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

theorem encard_points_eq_finrank : ∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] (f : A →+* B), f.Finite → f.Etale → ∀ φ : A →+* ℂ, {ψ : B →+* ℂ | ψ.comp f = φ}.encard = (letI := f.toAlgebra; Module.finrank A B : ℕ) := by
  intro A B _ _ _ f hf he φ
  letI := f.toAlgebra
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hf
  haveI : Algebra.Etale A B := he
  obtain ⟨hfin, hcard⟩ := card_algHom A B ℂ
  let e : {ψ : B →+* ℂ | ψ.comp f = φ} ≃ (B →ₐ[A] ℂ) :=
    { toFun := fun ψ => { ψ.1 with commutes' := fun a => RingHom.congr_fun ψ.2 a }
      invFun := fun ψ => ⟨ψ.toRingHom, RingHom.ext fun a => ψ.commutes a⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs : {ψ : B →+* ℂ | ψ.comp f = φ}.Finite := Finite.of_equiv _ e.symm
  rw [← hs.cast_ncard_eq, ← Nat.card_coe_set_eq, Nat.card_congr e, hcard]

end GlobalTheory.EtaleFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFractionFieldOfEtaleHeightOne
section
open IsLocalRing

namespace GlobalTheory

theorem etale_fractionField_of_etale_height_one :
    ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A]
      [Algebra R A], ¬ IsField R →
      (∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
        Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) →
      Algebra.Etale (Localization.AtPrime (⊥ : Ideal R))
        (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) A) := by
  intro R A _ _ _ _ _ _ hR h

  have hm : maximalIdeal R ≠ ⊥ := fun hm => hR ((isField_iff_maximalIdeal_eq).mpr hm)
  obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨P, hPmin, -⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem _).mpr hxm)
  haveI hP : P.IsPrime := hPmin.1.1
  have hxP : x ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hPmin.1.2
  have hPne : P ≠ ⊥ := fun e => hx0 (by simpa [e] using hxP)
  haveI : (Ideal.span {x}).IsPrincipal := ⟨⟨x, rfl⟩⟩
  have h1 : P.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hPmin)
    (Order.one_le_iff_ne_zero.mpr (fun e => hPne (Ideal.height_eq_zero_iff_eq_bot.mp e)))
  haveI := h P h1
  set K := Localization.AtPrime (⊥ : Ideal R)
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap R K y) := by
    intro y
    have hy : (y : R) ∈ (⊥ : Ideal R).primeCompl := by
      intro hb
      have hb' : (y : R) = 0 := Ideal.mem_bot.mp hb
      exact y.2 (by rw [hb']; exact P.zero_mem)
    exact IsLocalization.map_units K (⟨y, hy⟩ : (⊥ : Ideal R).primeCompl)
  letI : Algebra (Localization.AtPrime P) K :=
    (IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) hunit).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime P) K :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      change _ = IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) hunit _
      rw [IsLocalization.lift_eq])
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime P) K K A)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomToFieldFactorsAlgClosedSubfield
section
open IsLocalRing

open scoped TensorProduct

namespace GlobalTheory

theorem etale_hom_to_field_lands_in_algClosed_subfield
    (A B K L : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    [Algebra.Etale A B] [Field K] [IsAlgClosed K] [Field L]
    (α : A →+* K) (ι : K →+* L) (β : B →+* L) :
    (∀ a ∈ maximalIdeal A, α a = 0) → β.comp (algebraMap A B) = ι.comp α →
      ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = α ∧ ι.comp ψ = β := by
  intro _ hβ
  letI : Algebra A K := α.toAlgebra
  letI : Algebra K L := ι.toAlgebra
  letI : Algebra A L := (ι.comp α).toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g : B →ₐ[A] L :=
    { β with
      commutes' := fun a => congrArg (fun f : A →+* L => f a) hβ }
  let f : K ⊗[A] B →ₐ[K] L :=
    Algebra.TensorProduct.lift (Algebra.ofId K L) g (fun _ _ => Commute.all _ _)
  haveI : Module.Finite K (K ⊗[A] B) := Algebra.FormallyUnramified.finite_of_free K (K ⊗[A] B)
  haveI : Algebra.IsIntegral K (K ⊗[A] B) := Algebra.IsIntegral.of_finite K _
  haveI : Algebra.IsIntegral K f.range :=
    Algebra.IsIntegral.of_surjective f.rangeRestrict (AlgHom.rangeRestrict_surjective f)
  have hsurj : Function.Surjective (algebraMap K f.range) := by
    intro y
    have hy : IsIntegral K (y : L) := (Algebra.IsIntegral.isIntegral y).map f.range.val
    obtain ⟨k, hk⟩ := minpoly.mem_range_of_degree_eq_one K (y : L)
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hy))
    exact ⟨k, Subtype.ext hk⟩
  let e : K ≃+* f.range :=
    RingEquiv.ofBijective (algebraMap K f.range) ⟨(algebraMap K f.range).injective, hsurj⟩
  let ψ : B →+* K :=
    e.symm.toRingHom.comp (f.rangeRestrict.toRingHom.comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B).toRingHom)
  have hι : ∀ x, ι (ψ x) = β x := by
    intro x
    have h1 : (algebraMap K f.range (ψ x) : L) = ι (ψ x) := rfl
    have h2 : algebraMap K f.range (ψ x) = f.rangeRestrict (1 ⊗ₜ x) := by
      simp only [ψ, e, RingHom.comp_apply]
      exact (RingEquiv.ofBijective (algebraMap K f.range) _).apply_symm_apply _
    rw [← h1, h2]
    simp [f, g]
  refine ⟨ψ, ?_, ?_⟩
  · ext a
    apply ι.injective
    rw [RingHom.comp_apply, hι]
    exact congrArg (fun f : A →+* L => f a) hβ
  · ext x
    exact hι x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosureTensorOfEtaleOfIsIntegral
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem exists_one_tmul_eq_of_isIntegral_smooth_fractionField
    (R K B : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    (x : K ⊗[R] B) (hx : IsIntegral R x) : ∃ b : B, x = (1 : K) ⊗ₜ[R] b := by
  let e := Algebra.TensorProduct.comm R K B
  have h1 : IsIntegral R (e x) := hx.map e.toAlgHom
  have h2 : IsIntegral B (e x) := h1.tower_top
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := R) (S := B) (B := K)).2 ⟨e x, h2⟩
  have hy' : (TensorProduct.toIntegralClosure R B K y : B ⊗[R] K) = e x := congrArg Subtype.val hy
  have key : ∀ y : B ⊗[R] integralClosure R K, ∃ b : B,
      (TensorProduct.toIntegralClosure R B K y : B ⊗[R] K) = b ⊗ₜ[R] (1 : K) := by
    intro y
    induction y with
    | zero => exact ⟨0, by simp⟩
    | tmul b c =>
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 c.2
      refine ⟨r • b, ?_⟩
      rw [TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]
      rfl
    | add u v hu hv =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hv
      exact ⟨a + b, by rw [map_add, Subalgebra.coe_add, ha, hb, TensorProduct.add_tmul]⟩
  obtain ⟨b, hb⟩ := key y
  refine ⟨b, e.injective ?_⟩
  rw [← hy', hb]
  simp [e]

theorem etale_integralClosure_tensor_of_etale_of_isIntegral :
    ∀ (S₁ K₁ T : Type) [CommRing S₁] [IsDomain S₁] [IsIntegrallyClosed S₁] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [CommRing T] [Algebra S₁ T],
    Algebra.Etale S₁ T → Algebra.IsIntegral S₁ T →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[S₁] T)) := by
  intro S₁ K₁ T _ _ _ _ _ _ _ _ hE hI
  let i : T →ₐ[S₁] K₁ ⊗[S₁] T := Algebra.TensorProduct.includeRight
  have hi : Function.Injective i :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective S₁ K₁)
  have hint : ∀ t : T, i t ∈ integralClosure S₁ (K₁ ⊗[S₁] T) := fun t =>
    (Algebra.IsIntegral.isIntegral (R := S₁) t).map i
  let φ : T →ₐ[S₁] integralClosure S₁ (K₁ ⊗[S₁] T) := i.codRestrict _ hint
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      exact hi (congrArg Subtype.val hab)
    · rintro ⟨x, hx⟩
      obtain ⟨b, hb⟩ := exists_one_tmul_eq_of_isIntegral_smooth_fractionField S₁ K₁ T x hx
      exact ⟨b, Subtype.ext hb.symm⟩
  exact Algebra.Etale.of_equiv (AlgEquiv.ofBijective φ hφ)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalRingOfLocalization
section
open IsLocalRing

namespace GlobalTheory

theorem exists_finitePresentation_isLocalization_of_localization (A B E : Type) [CommRing A]
    [CommRing B] [CommRing E] [Algebra A B] (M : Submonoid A) [IsLocalization M B] [Algebra B E]
    [Algebra.FinitePresentation B E] :
    ∃ (D : Type) (_ : CommRing D) (_ : Algebra A D) (_ : Algebra.FinitePresentation A D)
      (φ : D →+* E), φ.comp (algebraMap A D) = (algebraMap B E).comp (algebraMap A B) ∧
      @IsLocalization D _ (Algebra.algebraMapSubmonoid D M) E _ φ.toAlgebra := by
  classical
  obtain ⟨n, f, hf, hK⟩ := ‹Algebra.FinitePresentation B E›
  letI : Algebra (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) B) :=
    MvPolynomial.algebraMvPolynomial
  haveI hL : IsLocalization (M.map (MvPolynomial.C (σ := Fin n))) (MvPolynomial (Fin n) B) :=
    MvPolynomial.isLocalization M B
  obtain ⟨s, hs⟩ := hK
  choose p hp using fun g : (s : Set (MvPolynomial (Fin n) B)) =>
    IsLocalization.surj (M.map (MvPolynomial.C (σ := Fin n))) (g : MvPolynomial (Fin n) B)
  let J₀ : Ideal (MvPolynomial (Fin n) A) := Ideal.span (Set.range fun g => (p g).1)
  have hJ : J₀.map (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) B)) =
      RingHom.ker f := by
    have hs' : Ideal.span (s : Set (MvPolynomial (Fin n) B)) = RingHom.ker f := hs
    rw [Ideal.map_span, ← hs']
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      rw [← hp g]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span g.2)
    · rw [Ideal.span_le]
      intro g hg
      rw [SetLike.mem_coe, ← Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units _ (p ⟨g, hg⟩).2),
        hp ⟨g, hg⟩]
      exact Ideal.subset_span ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
  have hJfg : J₀.FG := Submodule.fg_span (Set.finite_range _)
  let D := MvPolynomial (Fin n) A ⧸ J₀
  haveI : Algebra.FinitePresentation A D := Algebra.FinitePresentation.quotient hJfg
  let Dl := MvPolynomial (Fin n) B ⧸ J₀.map (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) B))
  haveI hDl : IsLocalization (Algebra.algebraMapSubmonoid D (M.map (MvPolynomial.C (σ := Fin n)))) Dl :=
    inferInstance
  let e : Dl ≃+* E := (Ideal.quotEquivOfEq hJ).trans (Ideal.quotientKerAlgEquivOfSurjective hf).toRingEquiv
  let φ : D →+* E := e.toRingHom.comp (algebraMap D Dl)
  refine ⟨D, inferInstance, inferInstance, inferInstance, φ, ?_, ?_⟩
  · ext a
    change e (Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) B)
      (MvPolynomial.C a))) = algebraMap B E (algebraMap A B a)
    have he : ∀ x, e (Ideal.Quotient.mk _ x) = f x := fun x => rfl
    rw [he, MvPolynomial.algebraMap_def, MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq, f.commutes]
  · letI : Algebra D E := φ.toAlgebra
    let e' : Dl ≃ₐ[D] E := AlgEquiv.ofRingEquiv (f := e) (fun x => rfl)
    have hsub : Algebra.algebraMapSubmonoid D (M.map (MvPolynomial.C (σ := Fin n))) =
        Algebra.algebraMapSubmonoid D M := by
      ext x
      simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    haveI := IsLocalization.isLocalization_of_algEquiv
      (Algebra.algebraMapSubmonoid D (M.map (MvPolynomial.C (σ := Fin n)))) e'
    rwa [hsub] at this

theorem exists_etale_atPrime_algEquiv_of_isEtaleAt (R D : Type) [CommRing R] [CommRing D]
    [Algebra R D] [Algebra.FinitePresentation R D] (P' : Ideal D) [P'.IsPrime]
    [Algebra.IsEtaleAt R P'] :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A)
      (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P') := by
  obtain ⟨f, hfP, hfet⟩ := Algebra.exists_etale_of_isEtaleAt (R := R) P'
  let A' := Localization.Away f
  have hdisj : Disjoint (Submonoid.powers f : Set D) P' :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hfP
  let q' : Ideal A' := P'.map (algebraMap D A')
  haveI hq' : q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) A' P' ‹_› hdisj
  have hcomap : q'.comap (algebraMap D A') = P' :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) A' ‹_› hdisj
  haveI h1 : IsLocalization.AtPrime (Localization.AtPrime q') (q'.comap (algebraMap D A')) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers f)
      (Localization.AtPrime q') q'
  haveI h2 : IsLocalization P'.primeCompl (Localization.AtPrime q') := by
    have h1' : IsLocalization (q'.comap (algebraMap D A')).primeCompl (Localization.AtPrime q') := h1
    have hsub : (q'.comap (algebraMap D A')).primeCompl = P'.primeCompl := by
      ext x
      simp only [Ideal.mem_primeCompl_iff, hcomap]
    rwa [hsub] at h1'
  let e : Localization.AtPrime q' ≃ₐ[D] Localization.AtPrime P' :=
    IsLocalization.algEquiv P'.primeCompl _ _
  exact ⟨A', inferInstance, inferInstance, hfet, q', hq', ⟨e.restrictScalars R⟩⟩

theorem essEtale_atPrime_of_etale_over_atPrime : ∀ (R A E : Type) [CommRing R] [CommRing A] [CommRing E] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime] [Algebra (Localization.AtPrime q) E] [Algebra.Etale (Localization.AtPrime q) E] [Algebra R E] [IsScalarTower R (Localization.AtPrime q) E] (P : Ideal E) [P.IsPrime], (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P)) := by
  intro R A E _ _ _ _ _ q _ _ _ _ _ P _
  obtain ⟨D, _, _, _, φ, hφ, hloc⟩ :=
    exists_finitePresentation_isLocalization_of_localization A (Localization.AtPrime q) E q.primeCompl
  letI : Algebra R D := ((algebraMap A D).comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FinitePresentation R D := Algebra.FinitePresentation.trans R A D
  letI : Algebra D E := φ.toAlgebra
  haveI : IsScalarTower R D E := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime q) E,
      IsScalarTower.algebraMap_eq R A (Localization.AtPrime q), ← RingHom.comp_assoc, ← hφ]
    rfl
  let EP := Localization.AtPrime P
  haveI : IsScalarTower D E EP := inferInstance
  haveI : IsScalarTower R D EP := inferInstance
  haveI hEP : IsLocalization.AtPrime EP (P.comap (algebraMap D E)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid D q.primeCompl) EP P
  let P' := P.comap (algebraMap D E)
  let eP : Localization.AtPrime P' ≃ₐ[D] EP := IsLocalization.algEquiv P'.primeCompl _ _
  haveI : Algebra.FormallyEtale R A := inferInstance
  haveI : Algebra.FormallyEtale A (Localization.AtPrime q) :=
    Algebra.FormallyEtale.of_isLocalization q.primeCompl
  haveI : Algebra.FormallyEtale R (Localization.AtPrime q) :=
    Algebra.FormallyEtale.comp R A (Localization.AtPrime q)
  haveI : Algebra.FormallyEtale R E := Algebra.FormallyEtale.comp R (Localization.AtPrime q) E
  haveI : Algebra.FormallyEtale E EP := Algebra.FormallyEtale.of_isLocalization P.primeCompl
  haveI : Algebra.FormallyEtale R EP := Algebra.FormallyEtale.comp R E EP
  haveI : Algebra.IsEtaleAt R P' := Algebra.FormallyEtale.of_equiv (eP.restrictScalars R).symm
  obtain ⟨A', i1, i2, i3, q', i4, ⟨e⟩⟩ := exists_etale_atPrime_algEquiv_of_isEtaleAt R D P'
  exact ⟨A', i1, i2, i3, q', i4, ⟨e.trans (eP.restrictScalars R)⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeOfHeightOne
section
open IsLocalRing

namespace GlobalTheory

theorem etale_localization_atPrime_of_height_one :
    ∀ (R A : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [Algebra R A]
      (p : Ideal R) [p.IsPrime],
      (∀ (P : Ideal R) [P.IsPrime], P.height = 1 →
        Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) A)) →
      ∀ (q : Ideal (Localization.AtPrime p)) [q.IsPrime], q.height = 1 →
        Algebra.Etale (Localization.AtPrime q)
          (TensorProduct (Localization.AtPrime p) (Localization.AtPrime q)
            (TensorProduct R (Localization.AtPrime p) A)) := by
  intro R A _ _ _ _ _ p _ H q _ hq
  set P : Ideal R := q.comap (algebraMap R (Localization.AtPrime p)) with hPdef
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hP : P.height = 1 := by
    rw [← hq, ← IsLocalization.height_comap p.primeCompl q]
  haveI := H P hP
  haveI : IsLocalization.AtPrime (Localization.AtPrime q) P :=
    IsLocalization.isLocalization_atPrime_localization_atPrime p.primeCompl q
  let e : Localization.AtPrime P ≃ₐ[R] Localization.AtPrime q :=
    IsLocalization.algEquiv P.primeCompl _ _
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime q) := e.toRingHom.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime P) (Localization.AtPrime q) :=
    IsScalarTower.of_algebraMap_eq (fun r => (e.commutes r).symm)
  haveI : Algebra.Etale (Localization.AtPrime q)
      (TensorProduct (Localization.AtPrime P) (Localization.AtPrime q)
        (TensorProduct R (Localization.AtPrime P) A)) :=
    Algebra.Etale.baseChange _ _ _
  let e1 := Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime P)
    (Localization.AtPrime q) (Localization.AtPrime q) A
  let e2 := Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime p)
    (Localization.AtPrime q) (Localization.AtPrime q) A
  exact Algebra.Etale.of_equiv (e1.trans e2.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleUniquePrimeLeMapMaximal
section
namespace GlobalTheory

theorem etale_prime_le_map_of_unique (B A : Type) [CommRing B] [CommRing A] [Algebra B A]
    [Algebra.Etale B A] (P : Ideal B) (hP : P.IsMaximal) (Q : Ideal A)
    (hQ : ∀ Q' : Ideal A, Q'.IsPrime → P.map (algebraMap B A) ≤ Q' → Q' = Q) :
    Q ≤ P.map (algebraMap B A) := by
  set I := P.map (algebraMap B A) with hI
  by_cases htop : I = ⊤
  · rw [htop]; exact le_top

  have hrad : I.radical = Q := by
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop
    have hMQ : M = Q := hQ M hM.isPrime hIM
    rw [Ideal.radical_eq_sInf]
    apply le_antisymm
    · exact sInf_le ⟨hMQ ▸ hIM, hMQ ▸ hM.isPrime⟩
    · refine le_sInf ?_
      rintro J ⟨hJ1, hJ2⟩
      exact (hQ J hJ2 hJ1).ge

  haveI := hP
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  haveI : Algebra.FormallyUnramified B (A ⧸ I) :=
    Algebra.FormallyUnramified.comp B A (A ⧸ I)
  haveI : Algebra.FormallyUnramified (B ⧸ P) (A ⧸ I) :=
    Algebra.FormallyUnramified.of_restrictScalars B (B ⧸ P) (A ⧸ I)
  haveI : Algebra.EssFiniteType B (A ⧸ I) := Algebra.EssFiniteType.comp B A (A ⧸ I)
  haveI : Algebra.EssFiniteType (B ⧸ P) (A ⧸ I) := Algebra.EssFiniteType.of_comp B (B ⧸ P) (A ⧸ I)
  haveI : IsReduced (A ⧸ I) := Algebra.FormallyUnramified.isReduced_of_field (B ⧸ P) (A ⧸ I)
  intro x hx
  rw [← hrad] at hx
  obtain ⟨n, hn⟩ := hx
  have h0 : (Ideal.Quotient.mk I x) ^ n = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn
  have : Ideal.Quotient.mk I x = 0 := IsReduced.eq_zero _ ⟨n, h0⟩
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

end GlobalTheory
end

