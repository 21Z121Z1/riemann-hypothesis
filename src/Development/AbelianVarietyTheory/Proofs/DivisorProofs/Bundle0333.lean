import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0310
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomFactorThroughSplitInjection
section
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory

theorem bialgHom_factor_through_split :
    ∀ (O : Type) [CommRing O] (A B D : Type) [CommRing A] [CommRing B] [CommRing D] [Bialgebra O A] [Bialgebra O B] [Bialgebra O D] (j : B →ₐc[O] A) (ρ : A →ₗ[O] B) (f : D →ₐc[O] A), (∀ b, ρ (j b) = b) → (∀ d, f d ∈ Set.range j) → ∃ g : D →ₐc[O] B, ∀ d, j (g d) = f d := by
  intro O _ A B D _ _ _ _ _ _ j ρ f hρ hf
  have hjinj : Function.Injective j := fun x y h => by
    have := congrArg ρ h; rwa [hρ, hρ] at this
  have hjg : ∀ d, j (ρ (f d)) = f d := fun d => by
    obtain ⟨b, hb⟩ := hf d; rw [← hb, hρ]
  have hmapinj : Function.Injective (TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A)) := by
    have hid : (TensorProduct.map ρ ρ).comp (TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A)) = LinearMap.id := by
      apply TensorProduct.ext'
      intro x y
      simp [hρ]
    intro x y h
    have := congrArg (TensorProduct.map ρ ρ) h
    simpa [← LinearMap.comp_apply, hid] using this
  let gl : D →ₗ[O] B := ρ ∘ₗ (f : D →ₗ[O] A)
  have hgl : ∀ d, j (gl d) = f d := hjg
  have hcomp : (j : B →ₗ[O] A) ∘ₗ gl = (f : D →ₗ[O] A) := LinearMap.ext hgl
  refine ⟨{ gl with
    counit_comp := ?_
    map_comp_comul := ?_
    map_one' := ?_
    map_mul' := ?_ }, hgl⟩
  · ext d
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [← CoalgHomClass.counit_comp_apply j, hgl, CoalgHomClass.counit_comp_apply]
  · ext d
    apply hmapinj
    show TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A) (TensorProduct.map gl gl (comul d)) =
      TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A) (comul (gl d))
    rw [CoalgHomClass.map_comp_comul_apply j, hgl, ← LinearMap.comp_apply, ← TensorProduct.map_comp, hcomp,
      CoalgHomClass.map_comp_comul_apply f]
  · apply hjinj
    show j (gl 1) = j 1
    rw [hgl, map_one, map_one]
  · intro x y
    apply hjinj
    show j (gl (x * y)) = j (gl x * gl y)
    rw [hgl, map_mul, map_mul, hgl, hgl]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLocallyConstantComapAlgClosureTensorOfH
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory

open IsLocalRing

theorem locallyConstant_eq_of_specializes {Y Λ : Type*} [TopologicalSpace Y]
    (φ : LocallyConstant Y Λ) {y y' : Y} (h : y ⤳ y') : φ y = φ y' :=
  h.mem_open (φ.isLocallyConstant.isOpen_fiber (φ y')) rfl

theorem mem_iff_of_specializes_of_isClopen {Y : Type*} [TopologicalSpace Y] {V : Set Y}
    (hV : IsClopen V) {y y' : Y} (h : y ⤳ y') : y ∈ V ↔ y' ∈ V :=
  ⟨fun hy ↦ h.mem_closed hV.1 hy, fun hy ↦ h.mem_open hV.2 hy⟩

theorem bijective_locallyConstant_comap_of_specializes_of_isClopen {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (Λ : Type*) (f : C(X, Y))
    (h1 : ∀ y : Y, ∃ x : X, y ⤳ f x)
    (h2 : ∀ U : Set X, IsClopen U → ∃ V : Set Y, IsClopen V ∧ f ⁻¹' V = U) :
    Function.Bijective (fun φ : LocallyConstant Y Λ ↦ φ.comap f) := by
  choose g hg using h1
  refine ⟨fun φ ψ hφψ ↦ ?_, fun ψ ↦ ?_⟩
  · ext y
    have h : (φ.comap f) (g y) = (ψ.comap f) (g y) := by
      rw [show φ.comap f = ψ.comap f from hφψ]
    rw [locallyConstant_eq_of_specializes φ (hg y), locallyConstant_eq_of_specializes ψ (hg y)]
    simpa using h
  · have key : ∀ l : Λ, ∃ V : Set Y, IsClopen V ∧ f ⁻¹' V = {x | ψ x = l} ∧
        (fun y ↦ ψ (g y)) ⁻¹' {l} = V := by
      intro l
      obtain ⟨V, hV, hVU⟩ := h2 _ (ψ.isLocallyConstant.isClopen_fiber l)
      refine ⟨V, hV, hVU, ?_⟩
      ext y
      show ψ (g y) = l ↔ y ∈ V
      rw [mem_iff_of_specializes_of_isClopen hV (hg y)]
      change ψ (g y) = l ↔ g y ∈ f ⁻¹' V
      rw [hVU]
      rfl
    refine ⟨⟨fun y ↦ ψ (g y), IsLocallyConstant.iff_isOpen_fiber.2 fun l ↦ ?_⟩, ?_⟩
    · obtain ⟨V, hV, -, hV'⟩ := key l
      rw [hV']
      exact hV.2
    · ext x
      obtain ⟨V, -, hVU, hV'⟩ := key (ψ x)
      have hx : x ∈ f ⁻¹' V := by rw [hVU]; rfl
      rw [← hV'] at hx
      exact hx

theorem map_maximalIdeal_le_of_isIntegral (A B : Type*) [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (M : Ideal B) [M.IsMaximal] :
    (maximalIdeal A).map (algebraMap A B) ≤ M := by
  rw [Ideal.map_le_iff_le_comap]
  have : (M.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  exact (IsLocalRing.eq_maximalIdeal this).ge

theorem exists_isIdempotentElem_lift_quotient_of_isIntegral (A B : Type) [CommRing A]
    [HenselianLocalRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    {c : B ⧸ (maximalIdeal A).map (algebraMap A B)} (hc : IsIdempotentElem c) :
    ∃ e : B, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = c := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hb : b * b - b ∈ (maximalIdeal A).map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc.eq, sub_self]
  have hb' : b * b - b ∈ Submodule.span B (algebraMap A B '' (maximalIdeal A : Set A)) := hb
  obtain ⟨n, r, s, hs⟩ := Submodule.mem_span_set'.1 hb'
  choose a ha hsa using fun i ↦ (s i).2
  set B₀ := Algebra.adjoin A (insert b (Set.range r)) with hB₀
  haveI : Module.Finite A B₀ := Algebra.finite_adjoin_of_finite_of_isIntegral
    ((Set.finite_range r).insert b) fun x _ ↦ Algebra.IsIntegral.isIntegral x
  let b₀ : B₀ := ⟨b, Algebra.subset_adjoin (Set.mem_insert _ _)⟩
  let r₀ : Fin n → B₀ := fun i ↦ ⟨r i, Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i, rfl⟩)⟩
  have hsum : b₀ * b₀ - b₀ = ∑ i, r₀ i * algebraMap A B₀ (a i) := by
    apply Subtype.ext
    show b * b - b = B₀.val (∑ i, r₀ i * algebraMap A B₀ (a i))
    rw [map_sum, ← hs]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, AlgHom.commutes, hsa i, smul_eq_mul]
    rfl
  have hb₀ : b₀ * b₀ - b₀ ∈ (maximalIdeal A).map (algebraMap A B₀) := by
    rw [hsum]
    exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (ha i))
  obtain ⟨e₀, ⟨he₀, he₀b⟩, -⟩ := existsUnique_idempotent_lift_quotient A (S := B₀)
    (c := Ideal.Quotient.mk _ b₀) (by
      show Ideal.Quotient.mk _ b₀ * Ideal.Quotient.mk _ b₀ = Ideal.Quotient.mk _ b₀
      rw [← map_mul, Ideal.Quotient.eq]
      exact hb₀)
  refine ⟨(e₀ : B), he₀.map B₀.val, ?_⟩
  have h := Ideal.mem_map_of_mem (B₀.val : B₀ →+* B) (Ideal.Quotient.eq.1 he₀b)
  rw [Ideal.map_map, AlgHom.comp_algebraMap] at h
  rw [Ideal.Quotient.eq]
  simpa using h

theorem bijective_locallyConstant_comap_algebraicClosure_tensor : ∀ (Λ : Type) (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)] (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B], Function.Bijective (fun φ : LocallyConstant (PrimeSpectrum B) Λ => φ.comap ⟨PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B).toRingHom, PrimeSpectrum.continuous_comap _⟩) := by
  intro Λ A _ _ _ _ B _ _ _
  let k := ResidueField A
  let Ω := AlgebraicClosure k
  let I : Ideal B := (maximalIdeal A).map (algebraMap A B)
  let ιk : B →ₐ[A] k ⊗[A] B := Algebra.TensorProduct.includeRight
  let μ : k ⊗[A] B →+* Ω ⊗[A] B :=
    (Algebra.TensorProduct.map (Algebra.ofId k Ω) (AlgHom.id A B)).toRingHom
  have hμ : IsHomeomorph (PrimeSpectrum.comap μ) :=
    PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable (R := A) (K := k)
      (S := B) Ω
  have hIk : ∀ x ∈ I, ιk x = 0 := by
    intro x hx
    have hle : I ≤ RingHom.ker ιk := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker]
      show ιk (algebraMap A B a) = 0
      rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply,
        show algebraMap A k a = 0 from (IsLocalRing.residue_eq_zero_iff a).2 ha, zero_tmul]
    exact hle hx
  let e' : B ⧸ I →+* k ⊗[A] B := Ideal.Quotient.lift I ιk.toRingHom hIk
  have he'mk : ∀ b : B, e' (Ideal.Quotient.mk I b) = ιk b := fun b ↦ rfl
  let σ : k →ₐ[A] B ⧸ I := Ideal.Quotient.liftₐ (maximalIdeal A) (Algebra.ofId A (B ⧸ I))
    fun a ha ↦ by
      rw [Algebra.ofId_apply]
      show Ideal.Quotient.mk I (algebraMap A B a) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
  let τ : k ⊗[A] B →ₐ[A] B ⧸ I :=
    Algebra.TensorProduct.lift σ (Ideal.Quotient.mkₐ A I) fun _ _ ↦ Commute.all _ _
  have hτ : ∀ q, τ (e' q) = q := by
    intro q
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [he'mk]
    show τ ((1 : k) ⊗ₜ[A] b) = _
    simp [τ]
  have he' : Function.Bijective e' := by
    refine ⟨Function.LeftInverse.injective hτ, fun y ↦ ?_⟩
    obtain ⟨b, rfl⟩ := includeRight_residueField_surjective A B y
    exact ⟨Ideal.Quotient.mk I b, rfl⟩
  let ρ : B ⧸ I →+* Ω ⊗[A] B := μ.comp e'
  have hρ : IsHomeomorph (PrimeSpectrum.comap ρ) := by
    rw [PrimeSpectrum.comap_comp]
    exact (PrimeSpectrum.isHomeomorph_comap_of_bijective he').comp hμ
  have hfac : ∀ x : PrimeSpectrum (Ω ⊗[A] B),
      PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom x =
        PrimeSpectrum.comap (Ideal.Quotient.mk I) (PrimeSpectrum.comap ρ x) := by
    intro x
    have : (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom =
        ρ.comp (Ideal.Quotient.mk I) := by
      ext b
      show (1 : Ω) ⊗ₜ[A] b = μ ((1 : k) ⊗ₜ[A] b)
      simp [μ]
    rw [this]
    rfl
  apply bijective_locallyConstant_comap_of_specializes_of_isClopen
  · intro y
    obtain ⟨M, hM, hyM⟩ := Ideal.exists_le_maximal y.asIdeal y.isPrime.ne_top
    have hIM : I ≤ M := map_maximalIdeal_le_of_isIntegral A B M
    haveI := hM.isPrime
    let P : PrimeSpectrum (B ⧸ I) := ⟨M.map (Ideal.Quotient.mk I),
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])⟩
    have hPM : (PrimeSpectrum.comap (Ideal.Quotient.mk I) P).asIdeal = M := by
      show (M.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = M
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.2 hIM]
    obtain ⟨x, hx⟩ := hρ.surjective P
    refine ⟨x, ?_⟩
    rw [← PrimeSpectrum.le_iff_specializes, ← PrimeSpectrum.asIdeal_le_asIdeal]
    show y.asIdeal ≤ (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom x).asIdeal
    rw [hfac, hx, hPM]
    exact hyM
  · intro U hU
    have hU' : IsClopen (PrimeSpectrum.comap ρ '' U) :=
      ⟨hρ.isClosedMap U hU.1, hρ.isOpenMap U hU.2⟩
    set c := PrimeSpectrum.isIdempotentElemEquivClopens.symm ⟨_, hU'⟩ with hc
    obtain ⟨e, he, hec⟩ := exists_isIdempotentElem_lift_quotient_of_isIntegral A B c.2
    have hU'c : (PrimeSpectrum.basicOpen (Ideal.Quotient.mk I e) : Set (PrimeSpectrum (B ⧸ I))) =
        PrimeSpectrum.comap ρ '' U := by
      rw [hec]
      exact congrArg SetLike.coe (PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm _)
    refine ⟨PrimeSpectrum.basicOpen e, ?_, ?_⟩
    · have := (PrimeSpectrum.isIdempotentElemEquivClopens ⟨e, he⟩).isClopen
      rwa [PrimeSpectrum.coe_isIdempotentElemEquivClopens_apply] at this
    · ext x
      change PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] Ω ⊗[A] B).toRingHom x ∈
        PrimeSpectrum.basicOpen e ↔ x ∈ U
      rw [hfac, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
        ← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, hU'c, hρ.injective.mem_set_image]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveMultiplicativeGroupSectionsUnits
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.GmSec

def gammaIso : yoneda.obj (Spec (CommRingCat.of (MvPolynomial Unit (ULift ℤ)))) ≅ Scheme.Γ ⋙ forget CommRingCat :=
  NatIso.ofComponents (fun U => Equiv.toIso
    ((AffineSpace.toSpecMvPolyIntEquiv Unit (X := U.unop)).trans (Equiv.funUnique Unit _))) (by
      intro U V f
      ext g
      rfl)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in

theorem _root_.GlobalTheory.EtC.GmSec.isSheaf_gamma :
    Presieve.IsSheaf Scheme.etaleTopology.{0} (Scheme.Γ ⋙ forget CommRingCat) :=
  Presieve.isSheaf_iso _ _root_.GlobalTheory.EtC.GmSec.gammaIso
    (Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))

abbrev uval {V : Scheme.{0}} (t : ((Scheme.Γ ⋙ unitsF) ⋙ forget (ModuleCat.{1} (ULift.{1} ℤ))).obj (op V)) : Γ(V, ⊤)ˣ :=
  Additive.toMul (ULift.down (α := Additive Γ(V, ⊤)ˣ) t)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
private lemma gmSec_uval_map_eq_units_map {U V : Scheme.{0}} (g : V ⟶ U)
    (t : ((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
      forget (ModuleCat.{1} (ULift.{1} ℤ))).obj (op U)) :
    _root_.GlobalTheory.EtC.GmSec.uval (((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
        forget (ModuleCat.{1} (ULift.{1} ℤ))).map g.op t) =
      Units.map (Scheme.Γ.map g.op).hom.toMonoidHom (_root_.GlobalTheory.EtC.GmSec.uval t) :=
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
private lemma gmSec_eq_of_uval_eq {U : Scheme.{0}}
    (s s' : ((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
      forget (ModuleCat.{1} (ULift.{1} ℤ))).obj (op U))
    (h : _root_.GlobalTheory.EtC.GmSec.uval s = _root_.GlobalTheory.EtC.GmSec.uval s') : s = s' := by
  cases s; cases s'; congr 1

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in
private theorem isSheaf_etaleTopology_units :
    Presieve.IsSheaf Scheme.etaleTopology.{0}
      ((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙ forget (ModuleCat.{1} (ULift.{1} ℤ))) := by
  intro U S hS x hx
  have hG := _root_.GlobalTheory.EtC.GmSec.isSheaf_gamma S hS
  let a : Presieve.FamilyOfElements (Scheme.Γ ⋙ forget CommRingCat) S.arrows :=
    fun V f hf => ((_root_.GlobalTheory.EtC.GmSec.uval (x f hf) : Γ(V, ⊤)ˣ) : Γ(V, ⊤))
  let b : Presieve.FamilyOfElements (Scheme.Γ ⋙ forget CommRingCat) S.arrows :=
    fun V f hf => (((_root_.GlobalTheory.EtC.GmSec.uval (x f hf))⁻¹ : Γ(V, ⊤)ˣ) : Γ(V, ⊤))
  have ha : a.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    exact congrArg (fun t => ((_root_.GlobalTheory.EtC.GmSec.uval t : Γ(Z, ⊤)ˣ) : Γ(Z, ⊤)))
      (hx g₁ g₂ h₁ h₂ w)
  have hb : b.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    have := congrArg (fun t => (((_root_.GlobalTheory.EtC.GmSec.uval t)⁻¹ : Γ(Z, ⊤)ˣ) : Γ(Z, ⊤)))
      (hx g₁ g₂ h₁ h₂ w)
    simp only [gmSec_uval_map_eq_units_map, ← map_inv] at this
    exact this
  have hA := hG.isAmalgamation ha
  have hB := hG.isAmalgamation hb
  set A := hG.amalgamate a ha
  set B := hG.amalgamate b hb
  have hAB : A * B = 1 := by
    refine hG.isSeparatedFor.ext fun V f hf => ?_
    change (Scheme.Γ.map f.op).hom (A * B) = (Scheme.Γ.map f.op).hom 1
    rw [map_mul, map_one]
    change (Scheme.Γ ⋙ forget CommRingCat).map f.op A *
      (Scheme.Γ ⋙ forget CommRingCat).map f.op B = 1
    rw [hA f hf, hB f hf]
    exact (_root_.GlobalTheory.EtC.GmSec.uval (x f hf)).mul_inv
  have hBA : B * A = 1 := by rw [mul_comm, hAB]
  let u : Γ(U, ⊤)ˣ := ⟨A, B, hAB, hBA⟩
  refine ⟨⟨Additive.ofMul u⟩, fun V f hf => gmSec_eq_of_uval_eq _ _ (Units.ext (hA f hf)),
    fun t ht => gmSec_eq_of_uval_eq _ _ (Units.ext ?_)⟩
  refine hG.isSeparatedFor.ext fun V f hf => ?_
  change ((_root_.GlobalTheory.EtC.GmSec.uval (((Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) ⋙
      forget (ModuleCat.{1} (ULift.{1} ℤ))).map f.op t) : Γ(V, ⊤)ˣ) : Γ(V, ⊤)) =
    (Scheme.Γ ⋙ forget CommRingCat).map f.op A
  rw [ht f hf, hA f hf]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct in

theorem _root_.GlobalTheory.EtC.GmSec.gm_sec_bijective :
    ∀ U : Scheme.{0},
      Function.Bijective
        (_root_.GlobalTheory.EtC.ofRings.sec _root_.GlobalTheory.EtC.unitsF U) := by
  intro U
  have hP : Presheaf.IsSheaf Scheme.etaleTopology (Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).mpr
      ((isSheaf_iff_isSheaf_of_type _ _).mpr isSheaf_etaleTopology_units)
  haveI := isIso_toSheafify Scheme.etaleTopology hP
  delta _root_.GlobalTheory.EtC.ofRings.sec
  exact ConcreteCategory.bijective_of_isIso
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ _root_.GlobalTheory.EtC.unitsF)).app (op U))

end GlobalTheory.EtC.GmSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BinaryFormSplits
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem exists_fin_enum_multiset {α : Type} : ∀ (n : ℕ) (M : Multiset α), Multiset.card M = n →
    ∃ u : Fin n → α, Multiset.map u Finset.univ.val = M := by
  classical
  intro n
  induction n with
  | zero =>
    intro M hM
    refine ⟨Fin.elim0, ?_⟩
    rw [Multiset.card_eq_zero] at hM
    subst hM; simp
  | succ n ih =>
    intro M hM
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card M)
    obtain ⟨u, hu⟩ := ih (M.erase a) (by rw [Multiset.card_erase_of_mem ha, hM]; rfl)
    refine ⟨Fin.cons a u, ?_⟩
    rw [Fin.univ_val_map, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← Multiset.cons_coe, ← Fin.univ_val_map, hu, Multiset.cons_erase ha]

theorem homogenize_multiset_prod_X_sub_C {E : Type} [Field E] (R : Multiset E) :
    Polynomial.homogenize (R.map fun a => Polynomial.X - Polynomial.C a).prod (Multiset.card R)
      = (R.map fun a => MvPolynomial.X 0 - MvPolynomial.C a * MvPolynomial.X 1).prod := by
  induction R using Multiset.induction_on with
  | empty => simp
  | cons a R ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm,
      Polynomial.homogenize_mul _ _ (m := 1) (n := Multiset.card R) ?_ ?_, ih]
    · simp [Multiset.map_cons]
    · exact Polynomial.natDegree_X_sub_C_le a
    · rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]

theorem binary_form_splits : ∀ (F : Type) [Field F] (m : ℕ) (p : Fin (m + 1) → F), p ≠ 0 →
    ∃ (E : Type) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E) (c : E)
      (s t : Fin m → E), c ≠ 0 ∧ (∀ j, ![s j, t j] ≠ 0) ∧
      ∀ (A : Type) [CommRing A] [Algebra E A] (x y : A),
        ∑ i : Fin (m + 1), algebraMap E A (algebraMap F E (p i)) * y ^ (i : ℕ) * x ^ (m - i) =
          algebraMap E A c * ∏ j, (algebraMap E A (s j) * x + algebraMap E A (t j) * y) := by
  intro F _ m p hp
  classical
  set q : F[X] := ∑ i : Fin (m + 1), Polynomial.C (p i) * Polynomial.X ^ (i : ℕ) with hq_def
  have hcoeff : ∀ i : Fin (m + 1), q.coeff i = p i := by
    intro i
    simp only [hq_def, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg]
      exact fun h => hj (Fin.ext h.symm)
    · simp
  have hq0 : q ≠ 0 := by
    intro h; apply hp; funext i; rw [← hcoeff i, h]; simp
  have hdeg : q.natDegree ≤ m := by
    rw [hq_def]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro i _
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp i.2)
  let E := q.SplittingField
  set Q : E[X] := q.map (algebraMap F E) with hQ_def
  have hsplit : Q.Splits := Polynomial.SplittingField.splits q
  have hQ0 : Q ≠ 0 := Polynomial.map_ne_zero hq0
  have hQdeg : Q.natDegree = q.natDegree := Polynomial.natDegree_map _
  set d := Q.natDegree with hd
  have hdm : d ≤ m := hQdeg ▸ hdeg
  have hcard : Multiset.card Q.roots = d := hsplit.natDegree_eq_card_roots.symm
  let M : Multiset (E × E) := Q.roots.map (fun r => (-r, 1)) + Multiset.replicate (m - d) (1, 0)
  have hM : Multiset.card M = m := by simp [M, hcard]; omega
  obtain ⟨u, hu⟩ := exists_fin_enum_multiset m M hM
  refine ⟨E, inferInstance, inferInstance, inferInstance, Q.leadingCoeff, fun j => (u j).1,
    fun j => (u j).2, ?_, ?_, ?_⟩
  · exact Polynomial.leadingCoeff_ne_zero.mpr hQ0
  · intro j
    have hj : u j ∈ M := by rw [← hu]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val j)
    simp only [M, Multiset.mem_add, Multiset.mem_map, Multiset.mem_replicate] at hj
    intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    rcases hj with ⟨r, _, hr⟩ | ⟨_, hr⟩
    · rw [← hr] at h1; simp at h1
    · rw [hr] at h0; simp at h0
  · intro A _ _ x y
    have hform : Polynomial.homogenize Q m = ∑ i : Fin (m + 1),
        MvPolynomial.C (algebraMap F E (p i)) * (MvPolynomial.X 0 ^ (i : ℕ) *
          MvPolynomial.X 1 ^ (m - i)) := by
      rw [hQ_def, congrArg (Polynomial.map (algebraMap F E)) hq_def, Polynomial.map_sum, Polynomial.homogenize_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.homogenize_C_mul, Polynomial.homogenize_X_pow (Nat.lt_succ_iff.mp i.2)]
    have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (hcard.trans hd)
    have hP := homogenize_multiset_prod_X_sub_C Q.roots
    rw [hcard] at hP
    have key : Polynomial.homogenize Q m = MvPolynomial.C Q.leadingCoeff *
        ((Q.roots.map fun a => MvPolynomial.X 0 - MvPolynomial.C a * MvPolynomial.X 1).prod *
          MvPolynomial.X 1 ^ (m - d)) := by
      calc Polynomial.homogenize Q m
          = Polynomial.homogenize (Polynomial.C Q.leadingCoeff *
              ((Q.roots.map fun a => Polynomial.X - Polynomial.C a).prod * 1)) (d + (m - d)) := by
            rw [mul_one, hfac, Nat.add_sub_cancel' hdm]
        _ = _ := by
            rw [Polynomial.homogenize_C_mul, Polynomial.homogenize_mul _ _ ?_ ?_, hP,
              Polynomial.homogenize_one]
            · rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hcard]
            · simp
    have h1 := congrArg (MvPolynomial.aeval (R := E) (σ := Fin 2) ![y, x]) (hform.symm.trans key)
    simp only [map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      map_multiset_prod, Multiset.map_map, Function.comp_def, map_sub, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h1
    have hprod : ∏ j, (algebraMap E A (u j).1 * x + algebraMap E A (u j).2 * y) =
        (M.map fun st => algebraMap E A st.1 * x + algebraMap E A st.2 * y).prod := by
      rw [← hu, Multiset.map_map]; rfl
    simp only [mul_assoc] at h1 ⊢
    rw [h1, hprod]
    simp only [M, Multiset.map_add, Multiset.prod_add, Multiset.map_map, Function.comp_def,
      Multiset.map_replicate, Multiset.prod_replicate]
    congr 2
    · congr 1
      refine Multiset.map_congr rfl fun r _ => ?_
      simp only [map_neg, map_one]
      ring
    · simp

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsBasic
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem chains_basic : ∀ (R : Type) [CommRing R] , (∀ E : Spc, ((chains R).obj E).IsStrictlyLE 0) ∧ (∀ {E E' : Spc} (f : E ⟶ E') (p : ℕ), ((chains R).map f).f (-(p : ℤ)) ≫ (chainsXIso R E' p).hom = (chainsXIso R E p).hom ≫ (free R).map (f.app (op (SimplexCategory.mk p)))) ∧ ∀ (E : Spc) (p : ℕ), (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ≫ (chainsXIso R E p).hom = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) := by
  intro R _
  refine ⟨fun E => (CochainComplex.isStrictlyLE_iff _ 0).2 (fun i hi => CupSpec.isZero_chains E i hi), fun {E E'} f p => ?_, fun E p => ?_⟩
  · rw [← cancel_epi (chainsXIso R E p).inv, ← Category.assoc, CupSpec.chains_map, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  · rw [← Category.assoc, CupSpec.chains_d, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterTrivialMatrixLatticeOpenCompactBasisStatement
section
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterTrivialMatrixLattice_open_compact_basis : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 → (∀ s : k, s ≠ 0 → IsOpen (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ∧ IsCompact (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k))) ∧ ∀ W ∈ 𝓝 (0 : Matrix (Fin n) (Fin d) k), ∃ s : k, s ≠ 0 ∧ (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ⊆ W := by
  first | exact @GlobalTheory.LinSchurLatt.latt_open_compact_basis | exact GlobalTheory.LinSchurLatt.latt_open_compact_basis | (intros; apply GlobalTheory.LinSchurLatt.latt_open_compact_basis <;> assumption)
end

