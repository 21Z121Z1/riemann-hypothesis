import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3063
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3088
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalizationModelFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NormCover

open GlobalTheory.BplusDescent

theorem genericPoint_mem {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : (U : Set X).Nonempty) :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)

theorem isFinite_fromNormalization_fieldPt {X : Scheme.{0}} [IsIntegral X] [GlobalTheory.IsNormalScheme X]
    [IsLocallyNoetherian X] {L : Type} [Field L] [CharZero L]
    (ψ : X.presheaf.stalk (genericPoint X) ⟶ .of L) (hψ : ψ.hom.Finite) :
    IsFinite (fieldPt ψ).fromNormalization := by
  refine ⟨fun U hU => ?_⟩
  by_cases hne : (U : Set X).Nonempty
  · have hη := genericPoint_mem hne
    haveI : Nonempty U := hne.to_subtype
    letI : Algebra Γ(X, U) Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) :=
      ((fieldPt ψ).fromNormalization.app U).hom.toAlgebra
    letI : Algebra Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) L :=
      (normFun ψ hη).hom.toAlgebra
    letI : Algebra Γ(X, U) L := (X.presheaf.germ U _ hη ≫ ψ).hom.toAlgebra
    letI : Algebra X.functionField L := ψ.hom.toAlgebra
    haveI : IsScalarTower Γ(X, U) Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) L :=
      .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom (app_normFun ψ hη)).symm
    haveI := functionField_isFractionRing_of_isAffineOpen X U hU
    haveI : IsScalarTower Γ(X, U) X.functionField L := .of_algebraMap_eq' rfl
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    haveI : FiniteDimensional X.functionField L := hψ
    haveI : CharZero X.functionField := ψ.hom.charZero
    haveI : IsIntegralClosure Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) Γ(X, U) L :=
      ⟨(normFun_spec ψ hη hU).1, fun {x} => ((normFun_spec ψ hη hU).2 x).symm⟩
    exact IsIntegralClosure.finite Γ(X, U) X.functionField L _
  · haveI : Subsingleton Γ((fieldPt ψ).normalization, (fieldPt ψ).fromNormalization ⁻¹ᵁ U) := by
      refine subsingleton_of_forall_eq 0 fun s => ?_
      rw [← basicOpen_eq_bot_iff]
      exact eq_bot_iff.2 fun z hz => (hne ⟨_, ((fieldPt ψ).normalization.basicOpen_le s hz :)⟩).elim
    letI := ((fieldPt ψ).fromNormalization.app U).hom.toAlgebra
    change Module.Finite _ _
    infer_instance

end GlobalTheory.NormCover

namespace GlobalTheory.NormCover

open GlobalTheory.BplusDescent

theorem exists_normalization_model : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω]
    (M : RatModel k Ω) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra k Ω'] [IsScalarTower k Ω Ω']
    [FiniteDimensional Ω Ω'], Geo.Tor.IsNormalScheme M.Z → ∃ (M' : RatModel k Ω') (π : M'.Z ⟶ M.Z),
      Geo.Tor.IsNormalScheme M'.Z ∧ IsFinite π ∧ M'.pt ≫ π = spMap (algebraMap Ω Ω') ≫ M.pt := by
  intro k Ω _ _ _ _ _ M Ω' _ _ _ _ _ hN
  haveI : GlobalTheory.IsNormalScheme M.Z := GlobalTheory.IsNormalScheme.of_pred hN
  haveI := M.lft
  haveI := M.sep
  haveI := M.qc
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap Ω Ω').injective
  let ρ : M.Z.presheaf.stalk (genericPoint M.Z) ⟶ .of Ω :=
    M.Z.presheaf.stalkSpecializes (M.pt_specializes (IsLocalRing.closedPoint Ω) (genericPoint M.Z)) ≫
      Scheme.stalkClosedPointTo M.pt
  have hρ : fieldPt ρ = M.pt := by
    simp only [fieldPt, ρ, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk M.pt
  let ψ : M.Z.presheaf.stalk (genericPoint M.Z) ⟶ .of Ω' := ρ ≫ CommRingCat.ofHom (algebraMap Ω Ω')
  have hψ : fieldPt ψ = spMap (algebraMap Ω Ω') ≫ M.pt := by
    rw [← hρ]
    simp only [fieldPt, ψ, Spec.map_comp, Category.assoc]
  have hρs : Function.Surjective ρ.hom := by
    intro x
    obtain ⟨U, f, hU, rfl⟩ := M.onto x
    have hη := genericPoint_mem hU
    refine ⟨M.Z.presheaf.germ U _ hη f, ?_⟩
    have key : ∀ (g : Sp Ω ⟶ M.Z) (_ : fieldPt ρ = g) (e : ⊤ ≤ g ⁻¹ᵁ U),
        g.appLE U ⊤ e ≫ (Scheme.ΓSpecIso (.of Ω)).hom = M.Z.presheaf.germ U _ hη ≫ ρ := by
      rintro _ rfl e
      exact fieldPt_appLE ρ hη
    have e := M.top_le_preimage_pt hU
    rw [valF, dif_pos e]
    exact (congrArg (fun g => g.hom f) (key M.pt hρ e)).symm
  have hψfin : ψ.hom.Finite :=
    RingHom.Finite.comp (RingHom.finite_algebraMap.2 inferInstance) (RingHom.Finite.of_surjective ρ.hom hρs)
  haveI hfin : IsFinite (fieldPt ψ).fromNormalization := isFinite_fromNormalization_fieldPt ψ hψfin

  have hgen : Set.range (fieldPt ψ).toNormalization = {genericPoint (fieldPt ψ).normalization} := by
    have hc : ∀ w : Sp Ω', w = IsLocalRing.closedPoint Ω' := fun w =>
      Subsingleton.elim (α := PrimeSpectrum Ω') _ _
    have hr : Set.range (fieldPt ψ).toNormalization = {(fieldPt ψ).toNormalization (IsLocalRing.closedPoint Ω')} := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        rw [hc w]
        rfl
      · rintro rfl
        exact ⟨_, rfl⟩
    have hd : closure (Set.range (fieldPt ψ).toNormalization) = Set.univ := (fieldPt ψ).toNormalization.denseRange.closure_range
    rw [hr] at hd ⊢
    have hg : IsGenericPoint ((fieldPt ψ).toNormalization (IsLocalRing.closedPoint Ω')) ⊤ := hd
    rw [hg.eq (genericPoint_spec (fieldPt ψ).normalization)]
  have hpts : (fieldPt ψ).toNormalization ≫ (fieldPt ψ).fromNormalization ≫ M.s = spMap (algebraMap k Ω') := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hψ, Category.assoc, M.pt_s, spMap, spMap,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have honto : ∀ x : Ω', ∃ (U : (fieldPt ψ).normalization.Opens) (f : Γ((fieldPt ψ).normalization, U)), (U : Set (fieldPt ψ).normalization).Nonempty ∧
      valF (fieldPt ψ).toNormalization U f = x := by
    intro x
    obtain ⟨U, hU, hηU, -⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint M.Z) (U := ⊤) trivial
    haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
    letI : Algebra Γ(M.Z, U) Ω' := (M.Z.presheaf.germ U _ hηU ≫ ψ).hom.toAlgebra
    letI : Algebra M.Z.functionField Ω' := ψ.hom.toAlgebra
    haveI := functionField_isFractionRing_of_isAffineOpen M.Z U hU
    haveI : IsScalarTower Γ(M.Z, U) M.Z.functionField Ω' := .of_algebraMap_eq' rfl
    haveI : FiniteDimensional M.Z.functionField Ω' := hψfin
    obtain ⟨⟨a, ha⟩, hax⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors Γ(M.Z, U)) x
      (Algebra.IsIntegral.isIntegral (R := M.Z.functionField) x)
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hηV : genericPoint M.Z ∈ M.Z.basicOpen a := by
      refine genericPoint_mem ?_
      rw [Set.nonempty_iff_ne_empty]
      exact fun h => ha0 ((basicOpen_eq_bot_iff a).1 (SetLike.coe_injective h))
    have hV : IsAffineOpen (M.Z.basicOpen a) := hU.basicOpen a
    let r := M.Z.presheaf.map (homOfLE (M.Z.basicOpen_le a)).op
    letI : Algebra Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) := r.hom.toAlgebra
    letI : Algebra Γ(M.Z, M.Z.basicOpen a) Ω' := (M.Z.presheaf.germ _ _ hηV ≫ ψ).hom.toAlgebra
    haveI : IsScalarTower Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) Ω' := .of_algebraMap_eq' (by
      have e : r ≫ M.Z.presheaf.germ _ _ hηV = M.Z.presheaf.germ U _ hηU := TopCat.Presheaf.germ_res _ _ _ _
      change (M.Z.presheaf.germ U _ hηU ≫ ψ).hom = (r ≫ M.Z.presheaf.germ _ _ hηV ≫ ψ).hom
      simp only [← e, Category.assoc])
    have hunit : IsUnit (r.hom a) := M.Z.toRingedSpace.isUnit_res_basicOpen a
    have hxV : IsIntegral Γ(M.Z, M.Z.basicOpen a) x := by
      have h1 : IsIntegral Γ(M.Z, M.Z.basicOpen a) (algebraMap Γ(M.Z, U) Ω' a * x) := by
        have := hax.tower_top (A := Γ(M.Z, M.Z.basicOpen a))
        rwa [Submonoid.smul_def, Algebra.smul_def] at this
      have h2 : x = algebraMap Γ(M.Z, M.Z.basicOpen a) Ω' (↑hunit.unit⁻¹ : Γ(M.Z, M.Z.basicOpen a)) *
          (algebraMap Γ(M.Z, U) Ω' a * x) := by
        rw [IsScalarTower.algebraMap_apply Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) Ω' a, ← _root_.mul_assoc, ← map_mul]
        have : (↑hunit.unit⁻¹ : Γ(M.Z, M.Z.basicOpen a)) * algebraMap Γ(M.Z, U) Γ(M.Z, M.Z.basicOpen a) a = 1 :=
          hunit.val_inv_mul
        rw [this, map_one, _root_.one_mul]
      rw [h2]
      exact isIntegral_algebraMap.mul h1
    obtain ⟨c, hc⟩ := ((normFun_spec ψ hηV hV).2 x).2 hxV
    have hW : ⊤ ≤ (fieldPt ψ).toNormalization ⁻¹ᵁ ((fieldPt ψ).fromNormalization ⁻¹ᵁ M.Z.basicOpen a) := by
      intro w _
      show (fieldPt ψ).fromNormalization ((fieldPt ψ).toNormalization w) ∈ M.Z.basicOpen a
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization, fieldPt_apply]
      exact hηV
    refine ⟨(fieldPt ψ).fromNormalization ⁻¹ᵁ M.Z.basicOpen a, c,
      ⟨_, hW (x := IsLocalRing.closedPoint Ω') trivial⟩, ?_⟩
    rw [valF, dif_pos hW]
    exact hc
  let M' : RatModel k Ω' :=
    { Z := (fieldPt ψ).normalization
      s := (fieldPt ψ).fromNormalization ≫ M.s
      sep := inferInstance
      lft := inferInstance
      qc := inferInstance
      pt := (fieldPt ψ).toNormalization
      pt_s := hpts
      gen := hgen
      onto := honto }
  refine ⟨M', (fieldPt ψ).fromNormalization, (GlobalTheory.IsNormalScheme.normalization_of_isIntegral (fieldPt ψ)).pred _, hfin, ?_⟩
  exact (Scheme.Hom.toNormalization_fromNormalization (fieldPt ψ)).trans hψ

end GlobalTheory.NormCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceWeightedOverPlace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair

theorem isTranscendenceBasis_one_tmul {k K F W ι : Type} [Field k] [Field K] [Field F] [Field W]
    [Algebra k K] [Algebra k F] [Algebra K W] [Algebra (K ⊗[k] F) W]
    [IsScalarTower K (K ⊗[k] F) W] [IsFractionRing (K ⊗[k] F) W] {x : ι → F}
    (hx : IsTranscendenceBasis k x) :
    IsTranscendenceBasis K fun i => algebraMap (K ⊗[k] F) W (1 ⊗ₜ x i) := by
  let ψ : K ⊗[k] F →ₐ[K] W := IsScalarTower.toAlgHom K (K ⊗[k] F) W
  have hψ : Function.Injective ψ := IsFractionRing.injective (K ⊗[k] F) W
  have hy : AlgebraicIndependent K fun i => ψ (1 ⊗ₜ x i) := by
    rw [algebraicIndependent_iff_injective_aeval]
    have h1 : Function.Injective
        (Algebra.TensorProduct.map (AlgHom.id K K) (MvPolynomial.aeval (R := k) x)) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := K)
        (MvPolynomial.aeval (R := k) x).toLinearMap
        (algebraicIndependent_iff_injective_aeval.1 hx.1)
    have e : (MvPolynomial.aeval (R := K) fun i => ψ (1 ⊗ₜ x i)) =
        (ψ.comp (Algebra.TensorProduct.map (AlgHom.id K K) (MvPolynomial.aeval (R := k) x))).comp
          (MvPolynomial.algebraTensorAlgEquiv (σ := ι) k K).symm.toAlgHom := by
      ext i
      simp
    rw [e]
    exact (hψ.comp h1).comp (MvPolynomial.algebraTensorAlgEquiv (σ := ι) k K).symm.injective
  change IsTranscendenceBasis K fun i => ψ (1 ⊗ₜ x i)
  rw [hy.isTranscendenceBasis_iff_isAlgebraic, ← IntermediateField.isAlgebraic_adjoin_iff_top]
  let E := IntermediateField.adjoin K (Set.range fun i => ψ (1 ⊗ₜ x i))
  let φ : F →+* W := (ψ : K ⊗[k] F →+* W).comp
    (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := F)).toRingHom
  have hm : ∀ a ∈ Algebra.adjoin k (Set.range x), φ a ∈ E := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      exact IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
    | algebraMap r =>
      have : φ (algebraMap k F r) = algebraMap K W (algebraMap k K r) := by
        rw [← ψ.commutes]
        change ψ (1 ⊗ₜ algebraMap k F r) = ψ (algebraMap k K r ⊗ₜ 1)
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          TensorProduct.smul_tmul]
      rw [this]
      exact E.algebraMap_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let g : Algebra.adjoin k (Set.range x) →+* E :=
    (φ.comp (Algebra.adjoin k (Set.range x)).val.toRingHom).codRestrict E fun a => hm a a.2
  have hg : Function.Injective g := fun a b h =>
    Subtype.ext (φ.injective (congrArg Subtype.val h))
  have hT : ∀ a, ψ a ∈ algebraicClosure E W := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | tmul l f =>
      have : l ⊗ₜ[k] f = algebraMap K _ l * ((1 : K) ⊗ₜ[k] f) := by simp
      rw [this, map_mul, ψ.commutes]
      refine mul_mem ((algebraicClosure E W).algebraMap_mem (algebraMap K E l)) ?_
      rw [mem_algebraicClosure_iff]
      exact (hx.isAlgebraic.isAlgebraic f).ringHom_of_comp_eq g φ hg rfl
  refine ⟨fun z => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := K ⊗[k] F) z
  exact mem_algebraicClosure_iff.1 (div_mem (hT a) (hT b))

theorem trBasis_append_tmul {k K F W : Type} [Field k] [Field K] [Field F] [Field W]
    [Algebra k K] [Algebra k F] [Algebra k W] [Algebra (K ⊗[k] F) W]
    [IsScalarTower k (K ⊗[k] F) W] [IsFractionRing (K ⊗[k] F) W] {n m : ℕ} {x : Fin n → K}
    {y : Fin m → F} (hx : TrBasis (algebraMap k K) x) (hy : TrBasis (algebraMap k F) y) :
    TrBasis (algebraMap k W) (Fin.append (fun i => algebraMap (K ⊗[k] F) W (1 ⊗ₜ y i))
      (fun i => algebraMap (K ⊗[k] F) W (x i ⊗ₜ 1))) := by
  have key : ∀ {A : Type} [Field A] [inst : Algebra k A] {l : ℕ} (u : Fin l → A),
      TrBasis (algebraMap k A) u ↔ IsTranscendenceBasis k u := by
    intro A _ inst l u
    have e : (algebraMap k A).toAlgebra = inst := Algebra.algebra_ext _ _ fun _ => rfl
    unfold TrBasis
    rw [e]
  rw [key] at hx hy ⊢
  letI : Algebra K W := ((algebraMap (K ⊗[k] F) W).comp (algebraMap K (K ⊗[k] F))).toAlgebra
  haveI : IsScalarTower K (K ⊗[k] F) W := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower k K W := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply k (K ⊗[k] F) W,
      IsScalarTower.algebraMap_apply k K (K ⊗[k] F), ← IsScalarTower.algebraMap_apply]
  have h := hx.sumElim_comp (isTranscendenceBasis_one_tmul (K := K) (W := W) hy)
  rw [← isTranscendenceBasis_equiv finSumFinEquiv]
  convert h using 1
  funext i
  rcases i with i | i
  · simp
  · simp
    rfl

theorem Place.le_ord_iff_div_mem {k K : Type} [Field k] [Field K] {c : k →+* K} (V : Place c)
    {f t : K} (hf : f ≠ 0) (ht : t ≠ 0) : V.ord t ≤ V.ord f ↔ f / t ∈ V.ring := by
  rw [← V.ord_nonneg_iff (div_ne_zero hf ht), div_eq_mul_inv, V.ord_mul hf (inv_ne_zero ht),
    V.ord_inv]
  omega

theorem exists_place_weighted_over_place : ∀ {K κ κ' L : Type} [Field K] [Field κ] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (n k k' : ℕ) (x : Fin n → K) (τ' : Fin k' → κ') (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ'),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ') τ' → (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ a, algebraMap ℂ K a ∈ R) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) →
  ∀ (E : Place (algebraMap ℂ K)), E.Contains R → (∀ r : R, (r : K) ≠ 0 → (π r = 0 ↔ 0 < E.ord r)) →
  ∀ M : ℕ, 1 ≤ k → 1 ≤ M → ∃ V : Place (algebraMap ℂ L),
    (∀ r : R, algebraMap (K ⊗[ℂ] κ') L ((r : K) ⊗ₜ 1) ∈ V.ring) ∧
    (∀ b : κ', b ≠ 0 → V.ord (algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ b)) = 0) ∧
    (∀ g : K, g ≠ 0 → V.ord (algebraMap (K ⊗[ℂ] κ') L (g ⊗ₜ 1)) = M * E.ord g) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), ∑ i, ρ (π (a i)) * b i ≠ 0 →
      (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ≠ 0 ∧ V.ord ((fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b) = 0) ∧
    (∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ'), (fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b ≠ 0 →
      ∑ i, π (a i) ⊗ₜ[ℂ] b i ∈ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M → (M : ℤ) ≤ V.ord ((fun (l : ℕ) (a : Fin l → R) (b : Fin l → κ') => ∑ i, algebraMap (K ⊗[ℂ] κ') L ((a i : K) ⊗ₜ b i)) l a b)) ∧
    V.formOrd (dForm (algebraMap ℂ L) (Fin.append (fun i => algebraMap (K ⊗[ℂ] κ') L (1 ⊗ₜ τ' i))
      (fun i => algebraMap (K ⊗[ℂ] κ') L (x i ⊗ₜ 1)))) + 1 ≤ M * (E.formOrd (dForm (algebraMap ℂ K) x) + 1) + k := by
  intro K κ κ' L _ _ _ _ _ _ _ _ _ _ _ n k k' x τ' R π ρ hx hτ hO hz hc hR hπ E hER hE M hk hM
  obtain ⟨Q, hQ, z, hm, hdim, hEQ, hg, hb, hu, hJ, y, q, hy, hq, hform⟩ :=
    GlobalTheory.T.exists_regular_localModel_graph_of_place (L := L) n k k' x τ' R π ρ hx hτ hO hz hc hR hπ E hER hE
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hw := trBasis_append_tmul (W := L) hx hτ
  let σ : Equiv.Perm (Fin (k + 1 + 1)) := Equiv.swap 0 1
  let wt : Fin (k + 1 + 1) → ℕ := fun i => if i = 1 then M else 1
  obtain ⟨V, hVQ, hV0, hVz, hVd, hVf⟩ := GlobalTheory.T.exists_weighted_monomial_valuation_of_parameters (algebraMap ℂ L) Q hQ (k + 1) (k' + n)
    (z ∘ σ) wt (by rw [σ.surjective.range_comp]; exact hm) hdim (by simp [wt])
    (fun i => by simp only [wt]; split_ifs <;> omega) ⟨_, hw⟩
  have hz0 : V.ord (z 0) = M := by simpa [σ, wt] using hVz 1
  have hz0' : (z 0 : L) ≠ 0 := by
    intro h
    rw [h, Place.ord, map_zero, WithZero.log_zero] at hz0
    omega
  have hne : ∀ p : Q, IsUnit p → (p : L) ≠ 0 := fun p hp => (hp.map Q.subtype).ne_zero
  have hmul : ∀ (p : Q) (a : ℤ), IsUnit p → V.ord ((p : L) * (z 0 : L) ^ a) = M * a := by
    intro p a hp
    rw [V.ord_mul (hne p hp) (zpow_ne_zero _ hz0'), hV0 p hp, V.ord_zpow, hz0]
    ring
  refine ⟨V, fun r => hVQ _ (hEQ _ (hER _ r.2)), fun b hb0 => ?_, fun g hg0 => ?_,
    fun l a b h => ?_, fun l a b h0 h => ?_, ?_⟩
  · obtain ⟨p, hp, e⟩ := hb b hb0
    rw [← e, hV0 p hp]
  · obtain ⟨p, hp, e⟩ := hg g hg0
    rw [e, hmul p _ hp]
  · obtain ⟨p, hp, e⟩ := hu l a b h
    rw [← e]
    exact ⟨hne p hp, hV0 p hp⟩
  · obtain ⟨p, e, hp⟩ := hJ M l a b h
    rw [← e] at h0 ⊢
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hp
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ht
    rw [← hz0, V.le_ord_iff_div_mem h0 hz0']
    push_cast
    rw [add_div, mul_div_cancel_right₀ _ hz0']
    refine add_mem ?_ (hVQ _ u.2)
    by_cases hs0 : (s : L) = 0
    · rw [hs0, zero_div]
      exact zero_mem _
    · rw [← V.le_ord_iff_div_mem hs0 hz0', hz0]
      exact hVd M s hs0 hs
  · have hd : dForm (algebraMap ℂ L) (fun i => (y i : L)) ≠ 0 := by
      intro h
      have h1 := (isFreeGen_dForm_of_trBasis _ hw).1 (a₁ := 1) (a₂ := 0)
        (by simp only [hform, h, smul_zero])
      exact one_ne_zero h1
    have hs : ∑ i, (wt i : ℤ) = M + (k + 1) := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      have : ∀ i : Fin k, wt i.succ.succ = 1 := fun i =>
        if_neg (fun h => Fin.succ_ne_zero i (Fin.succ_injective _ h))
      simp [this, wt]
      ring
    have h1 := hVf y hy
    rw [hform, V.formOrd_smul hw hd (mul_ne_zero (hne q hq) (zpow_ne_zero _ hz0')), hmul q _ hq]
    rw [hs] at h1
    push_cast
    linarith

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackFrameSpanningFlag
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

namespace GlobalTheory.FlagCell

open GlobalTheory.Twist (resM resM_resM resM_smul app_resM sec_ext_of_cover exists_sec_of_cover)
open GlobalTheory.LB (exists_fun_of_cover)

theorem pullCol_res {B Y : Scheme.{0}} (π : Y ⟶ B) {E : B.Modules} {U : B.Opens} {m : ℕ}
    (e : Fin m → Γ(E, U)) {V V' : Y.Opens} (hV : V ≤ π ⁻¹ᵁ U) (h : V' ≤ V)
    (M : Matrix (Fin m) (Fin m) Γ(Y, V)) (j : Fin m) :
    resM _ h (pullCol π e hV M j) = pullCol π e (h.trans hV) (M.map (resG Y h)) j := by
  simp only [pullCol, map_sum, resM_smul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact congrArg (resG Y h (M l j) • ·) (QCoh.res_pullbackSections π E hV h (e l))

theorem Spans.res {X : Scheme.{0}} {F : X.Modules} {m : ℕ} {fl : Vert.Flag F m} {V V' : X.Opens}
    {v : Fin m → Γ(F, V)} (hs : Spans fl V v) (h : V' ≤ V) :
    Spans fl V' fun j => resM F h (v j) := fun l => by
  obtain ⟨s, hfr, hv⟩ := hs l
  exact ⟨fun j => resM _ h (s j), hfr.res h, fun j => by rw [app_resM, hv]⟩

def IsCellCoord {B Y : Scheme.{0}} (π : Y ⟶ B) {ι : Type} {r : ι → ℕ} {E : ι → B.Modules}
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) {U : B.Opens}
    (eU : ∀ a, Fin (r a) → Γ(E a, U)) (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U)
    (n : (Σ a, Low (r a)) → Γ(Y, V)) : Prop :=
  ∀ a, Spans (fl a) V (pullCol π (eU a) hV (uniR fun s => n ⟨a, s⟩))

theorem IsCellCoord.res {B Y : Scheme.{0}} {π : Y ⟶ B} {ι : Type} {r : ι → ℕ} {E : ι → B.Modules}
    {fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)} {U : B.Opens}
    {eU : ∀ a, Fin (r a) → Γ(E a, U)} {V V' : Y.Opens} {hV : V ≤ π ⁻¹ᵁ U}
    {n : (Σ a, Low (r a)) → Γ(Y, V)} (hn : IsCellCoord π fl eU V hV n) (h : V' ≤ V) :
    IsCellCoord π fl eU V' (h.trans hV) fun s => resG Y h (n s) := fun a => by
  have e : (fun j => resM _ h (pullCol π (eU a) hV (uniR fun s => n ⟨a, s⟩) j)) =
      pullCol π (eU a) (h.trans hV) (uniR fun s => resG Y h (n ⟨a, s⟩)) :=
    funext fun j => by rw [pullCol_res, map_uniR]
  exact e ▸ (hn a).res h

theorem exists_cellLocus : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (r : ι → ℕ) (E : ι → B.Modules) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, IsVB (E a) (r a)) → ∀ (U : B.Opens) (eU : ∀ a, Fin (r a) → Γ(E a, U)), (∀ a, IsFrame (eU a)) → ∃ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U) (n : (Σ a, Low (r a)) → Γ(Y, W)), (∀ a, Spans (fl a) W (pullCol π (eU a) hW (uniR fun s => n ⟨a, s⟩))) ∧ ∀ (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U) (n' : (Σ a, Low (r a)) → Γ(Y, V)), (∀ a, Spans (fl a) V (pullCol π (eU a) hV (uniR fun s => n' ⟨a, s⟩))) → ∃ hVW : V ≤ W, ∀ s, Y.presheaf.map (homOfLE hVW).op (n s) = n' s := by
  intro B Y π ι r E fl hE U eU heU
  have uniq : ∀ (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U) (n₁ n₂ : (Σ a, Low (r a)) → Γ(Y, V)),
      IsCellCoord π fl eU V hV n₁ → IsCellCoord π fl eU V hV n₂ → n₁ = n₂ := by
    intro V hV n₁ n₂ h₁ h₂
    funext ⟨a, s⟩
    exact congrFun (GlobalTheory.T.pullback_unipotent_frame_unique Y B π (E a) (r a) (hE a) U (eU a) (heU a) (fl a) V hV _ _
      (h₁ a) (h₂ a)) s
  let K := {V : Y.Opens // ∃ (hV : V ≤ π ⁻¹ᵁ U) (n : (Σ a, Low (r a)) → Γ(Y, V)),
    IsCellCoord π fl eU V hV n}
  choose hK nK gK using fun k : K => k.2
  have hWk : ∀ k : K, k.1 ≤ ⨆ k : K, k.1 := fun k => le_iSup (fun k : K => k.1) k
  have hW : (⨆ k : K, k.1) ≤ π ⁻¹ᵁ U := iSup_le hK
  have compat : ∀ (k l : K) s, resG Y (inf_le_left : k.1 ⊓ l.1 ≤ k.1) (nK k s) =
      resG Y (inf_le_right : k.1 ⊓ l.1 ≤ l.1) (nK l s) := fun k l s =>
    congrFun (uniq _ (inf_le_left.trans (hK k)) _ _ ((gK k).res inf_le_left)
      ((gK l).res inf_le_right)) s
  choose N hN using fun s => exists_fun_of_cover (fun k : K => k.1) hWk le_rfl
    (fun k => nK k s) fun k l => compat k l s
  have resN : ∀ k : K, (fun s => resG Y (hWk k) (N s)) = nK k := fun k => funext fun s => hN s k
  have good : IsCellCoord π fl eU (⨆ k : K, k.1) hW N := by
    intro a l
    have hv : ∀ k : K, pullCol π (eU a) (hK k) (uniR fun s => nK k ⟨a, s⟩) =
        fun j => resM _ (hWk k) (pullCol π (eU a) hW (uniR fun s => N ⟨a, s⟩) j) := by
      intro k; funext j; rw [pullCol_res, map_uniR, ← resN k]
    choose sK hsK hιK using fun k : K => gK k a l
    have compS : ∀ (k k' : K) j, resM _ (inf_le_left : k.1 ⊓ k'.1 ≤ k.1) (sK k j) =
        resM _ (inf_le_right : k.1 ⊓ k'.1 ≤ k'.1) (sK k' j) := by
      intro k k' j
      apply QCoh.injective_app_of_mono ((fl a).ι l)
      rw [app_resM, app_resM, hιK, hιK]
      simp only [hv, resM_resM]
    choose t ht using fun j => exists_sec_of_cover (F := (fl a).F l) (fun k : K => k.1) hWk le_rfl
      (fun k => sK k j) fun k k' => compS k k' j
    refine ⟨t, ?_, fun j => ?_⟩
    · refine isFrame_of_forall_exists fun V' h y hy => ?_
      obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show y ∈ ⨆ k : K, k.1 from h hy)
      refine ⟨V' ⊓ k.1, inf_le_left, ⟨hy, hk⟩, ?_⟩
      have e : (fun j => resM _ ((inf_le_left : V' ⊓ k.1 ≤ V').trans h) (t j)) =
          fun j => resM _ (inf_le_right : V' ⊓ k.1 ≤ k.1) (sK k j) := by
        funext j; rw [← ht j k, resM_resM]
      rw [e]
      exact hsK k _ inf_le_right
    · refine sec_ext_of_cover (fun k : K => k.1) hWk le_rfl fun k => ?_
      rw [← app_resM, ht, hιK]
      simp only [hv]
  refine ⟨⨆ k : K, k.1, hW, N, good, fun V hV n' hn' => ⟨hWk ⟨V, hV, n', hn'⟩, fun s => ?_⟩⟩
  exact (hN s _).trans (congrFun (uniq V hV _ _ (gK ⟨V, hV, n', hn'⟩) hn') s)

end GlobalTheory.FlagCell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReductionPointsAbelianSchemeValuationRingStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reduction_points_abelianScheme_valuationRing : ∀ (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [IsAlgClosed Ω] [Algebra U Ω] [IsFractionRing U Ω] [Field k] [IsAlgClosed k] (h : U →+* k) (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ u : Sp U ⟶ S, ∃ r : (Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G) →* (Over.mk (spMap h ≫ u) ⟶ G), (∀ (P : Over.mk u ⟶ G) y y₀, y.left = spMap (algebraMap U Ω) ≫ P.left → y₀.left = spMap h ≫ P.left → r y = y₀) ∧ (∀ (f : G ⟶ G) y, r (y ≫ f) = r y ≫ f) ∧ (∀ n : ℕ, IsUnit (n : U) → Set.BijOn r {y | y ^ n = 1} {y | y ^ n = 1}) ∧ ∀ (Lb : LB G.left), Lb.IsLB → ∀ n : ℕ, IsUnit (n : U) → ∀ y y' (c : Uˣ), y ^ n = 1 → y' ^ n = 1 → Out.WeilIs G Lb n y y' (unitOn (Units.map (algebraMap U Ω : U →* Ω) c)) → Out.WeilIs G Lb n (r y) (r y') (unitOn (Units.map (h : U →* k) c)) := by
  first | exact @GlobalTheory.ValReduction.reduction_points | exact GlobalTheory.ValReduction.reduction_points | (intros; apply GlobalTheory.ValReduction.reduction_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomMatrixLiftOfOrderActionExponentialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_matrix_lift_of_orderAction_exponential : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ) (O : Type) [Ring O] (act : O → (G ⟶ G)), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsExp y e → ∃ ρ' : O →+* Matrix (Fin g) (Fin g) ℂ, ∀ a z, e (ρ' a *ᵥ z) = e z ≫ act a := by
  first | exact @GlobalTheory.ExpLin.exists_ringHom_matrix_lift | exact GlobalTheory.ExpLin.exists_ringHom_matrix_lift | (intros; apply GlobalTheory.ExpLin.exists_ringHom_matrix_lift <;> assumption)
end

