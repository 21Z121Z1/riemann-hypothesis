import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0098
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2792
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsSecNeObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2348
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2808
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2553
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2816
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2836
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2817
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsAtOfCodimLeOneOverCompleteDVRs
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CodimOneExtend

theorem extAt_of_flat {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X XK XV XF : Scheme.{0}} {p : X ⟶ Sp R} {J : XK ⟶ X} {q : XK ⟶ Sp K}
    (H : IsPullback J q p (spMap (algebraMap R K))) (φ : XV ⟶ X) [Flat φ] (A : XF ⟶ XV)
    (hA : ∀ U, Function.Injective (A.app U).hom) (B : XF ⟶ XK) (w : B ≫ J = A ≫ φ) (W : X.Opens)
    (f : Γ(XK, J ⁻¹ᵁ W)) (s : Γ(XV, φ ⁻¹ᵁ W)) (h₂ : A ⁻¹ᵁ φ ⁻¹ᵁ W ≤ B ⁻¹ᵁ J ⁻¹ᵁ W)
    (hs : (A.appLE _ _ le_rfl).hom s = (B.appLE _ _ h₂).hom f) (v : XV) (hv : φ v ∈ W) :
    GenericExtend.ExtAt J W f (φ v) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hvU, hUW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hv W.isOpen
  have hUW : U ≤ W := hUW
  obtain ⟨a, ha, b, hb⟩ := loc_surj (nonZeroDivisors R) H hU (resG XK (J.preimage_mono hUW) f)
  have hb' : ∀ z, J z ∈ U → gs (𝟙 XK) z (J ⁻¹ᵁ U) ((J.app U).hom b) =
      cst (J ≫ p) z a * gs (𝟙 XK) z (J ⁻¹ᵁ W) f := fun z hz ↦ by
    rw [gs_pull (𝟙 XK) J z U hz, Category.id_comp, hb z hz, gs_res (𝟙 XK) z _ hz]
  have hw : ∀ t, J (B t) = φ (A t) := fun t ↦ by
    rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
  have e : (φ.app U).hom b = constFn (φ ≫ p) _ a * resG XV (φ.preimage_mono hUW) s := by
    refine hA _ (fn_ext fun t ht ↦ ?_)
    have ht' : J (B t) ∈ U := by rw [hw]; exact ht
    have k := congrArg (B.stalkMap t).hom (hb' (B t) ht')
    rw [map_mul, ← gs_stalkMap B t _ ht', ← gs_stalkMap B t _ (hUW ht'), H1.cst_stalkMap, gs_pull B J t U ht',
      w] at k
    have k' := congrArg (gs (𝟙 XF) t _) hs
    rw [gs_appLE A _ _ _ (𝟙 XF) t (hUW ht), gs_appLE B _ _ _ (𝟙 XF) t (hUW ht), Category.id_comp,
      Category.id_comp] at k'
    rw [gs_pull (𝟙 XF) A t _ ht, gs_pull (𝟙 XF) A t _ ht, Category.id_comp, gs_mul A t _ ht,
      gs_pull A φ t U ht, gs_constFn _ _ A t ht, gs_res A t _ ht, k, k', reassoc_of% w]
  have hd : cst p (φ v) a ∣ gs (𝟙 X) (φ v) U b := by
    refine dvd_descend φ v ?_
    have k := congrArg (gs (𝟙 XV) v _) e
    rw [gs_pull (𝟙 XV) φ v U hvU, gs_mul (𝟙 XV) v _ hvU, gs_constFn _ _ (𝟙 XV) v hvU, Category.id_comp,
      Category.id_comp] at k
    rw [← gs_stalkMap φ v U hvU, H1.cst_stalkMap, k]
    exact dvd_mul_right _ _
  obtain ⟨t, ht⟩ := hd
  obtain ⟨U', hU', c, rfl⟩ := X.presheaf.exists_germ_eq t
  have hm : φ v ∈ U ⊓ U' := ⟨hvU, hU'⟩
  have e₁ : gs (𝟙 X) (φ v) (U ⊓ U') (resG X inf_le_left b) =
      gs (𝟙 X) (φ v) (U ⊓ U') (constFn p (U ⊓ U') a * resG X inf_le_right c) := by
    rw [gs_res (𝟙 X) (φ v) _ hm, gs_mul (𝟙 X) (φ v) _ hm, gs_res (𝟙 X) (φ v) _ hm, gs_constFn p _ (𝟙 X) (φ v) hm,
      Category.id_comp, ht, gs_eq (𝟙 X) (φ v) U' hU']
    rfl
  rw [gs_eq (𝟙 X) (φ v) _ hm, gs_eq (𝟙 X) (φ v) _ hm] at e₁
  obtain ⟨O, hO, i₁, i₂, e'⟩ := X.presheaf.germ_eq (φ v) hm hm _ _ e₁
  have le : O ≤ U ⊓ U' := i₁.le
  refine ⟨O, le.trans (inf_le_left.trans hUW), resG X (le.trans inf_le_right) c, hO, fn_ext fun z hz ↦ ?_⟩
  have hz' : J z ∈ U ⊓ U' := le hz
  have k := (gs_res J z le hz _).symm.trans ((congrArg (gs J z O) e').trans (gs_res J z le hz _))
  have k' : gs J z (U ⊓ U') (resG X inf_le_left b) =
      gs J z (U ⊓ U') (constFn p (U ⊓ U') a * resG X inf_le_right c) := k
  rw [gs_res J z _ hz', gs_mul J z _ hz', gs_res J z _ hz', gs_constFn p _ J z hz'] at k'
  have k₂ := hb' z hz'.1
  rw [gs_pull (𝟙 XK) J z U hz'.1, Category.id_comp, k'] at k₂
  have hu : IsUnit (cst (J ≫ p) z a) := by
    rw [H.w, cst_comp]
    refine IsUnit.of_mul_eq_one (cst q z (algebraMap R K a)⁻¹) ?_
    rw [← H1.cst_mul, mul_inv_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha), H1.cst_one]
  rw [gs_appLE J _ _ _ (𝟙 XK) z hz, Category.id_comp, gs_res J z _ hz, gs_res (𝟙 XK) z _ hz]
  exact hu.mul_left_cancel k₂

theorem exists_cDvr_flat (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CharZero R] (𝔭 : Ideal R) [𝔭.IsPrime] (h : 𝔭.height = 1) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V), GlobalTheory.LN.CDvr V ∧ ∃ φ : R →+* V,
      Function.Injective φ ∧ φ.Flat ∧ (IsLocalRing.maximalIdeal V).comap φ = 𝔭 := by
  have := ((GlobalTheory.normal_domain_height_one.{0, 0, 0} R (FractionRing R)).1 𝔭 h).1
  have hi : Function.Injective (algebraMap R (Localization.AtPrime 𝔭)) :=
    IsLocalization.injective _ 𝔭.primeCompl_le_nonZeroDivisors
  have : CharZero (Localization.AtPrime 𝔭) := charZero_of_injective_algebraMap hi
  obtain ⟨V, _, _, _, hV, j, hj, hl⟩ :=
    GlobalTheory.DvrCompletion.exists_cDvr_of_isDiscreteValuationRing (Localization.AtPrime 𝔭)
  refine ⟨V, _, _, _, hV, j.comp (algebraMap R _), hj.comp hi, ?_, ?_⟩
  · refine RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance) ?_
    let _ := j.toAlgebra
    have : FaithfulSMul (Localization.AtPrime 𝔭) V := (faithfulSMul_iff_algebraMap_injective _ _).2 hj
    exact (inferInstance : Module.Flat (Localization.AtPrime 𝔭) V)
  · rw [← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap]
    exact Localization.AtPrime.under_maximalIdeal

theorem exists_map_fractionRing {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V)
    (hφ : Function.Injective φ) : ∃ φK : FractionRing R →+* FractionRing V,
      φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ :=
  ⟨IsLocalization.map (M := nonZeroDivisors R) (T := nonZeroDivisors V) (FractionRing V) φ
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφ), IsLocalization.map_comp _⟩

theorem extAt_of_coheight_le_one : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (W : (Over.mk χ ⊗ G).left.Opens) (f : Γ((Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⊗ G).left, ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)), (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V) (φK : FractionRing R →+* FractionRing V) (h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ), φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ → ∃ s : Γ((Over.mk (spMap φ ≫ χ) ⊗ G).left, ((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W), ∀ (O : (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⊗ G).left.Opens) (h₁ : O ≤ ((Over.homMk (spMap (algebraMap V (FractionRing V))) rfl : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ)) ▷ G).left ⁻¹ᵁ (((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)) (h₂ : O ≤ ((Over.homMk (spMap φK) h : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) ▷ G).left ⁻¹ᵁ (((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)), (((Over.homMk (spMap (algebraMap V (FractionRing V))) rfl : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ)) ▷ G).left.appLE _ O h₁).hom s = (((Over.homMk (spMap φK) h : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) ▷ G).left.appLE _ O h₂).hom f) → ∀ y ∈ W, Order.coheight y ≤ 1 → y ∉ Set.range ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left → GlobalTheory.GenericExtend.ExtAt ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left W f y := by
  intro S G _ hG R _ _ _ _ _ χ W f hf y hy h1 hr
  have := hG.smooth
  have fl : ∀ T : Over S, Flat (fst T G).left := fun T ↦
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback T.hom G.hom).flip inferInstance
  have := fl (Over.mk χ)
  have H := ThetaRuleCompare.isPullback_whisker (A := G)
    (Over.homMk (spMap (algebraMap R (FractionRing R))) rfl :
      Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ)
  let x : PrimeSpectrum R := (fst (Over.mk χ) G).left y
  have hx1 : Order.coheight ((fst (Over.mk χ) G).left y) ≤ 1 := GenericExtend.coheight_apply_le_one _ h1
  have hx0 : x.asIdeal ≠ ⊥ := fun h0 ↦ hr (by
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback H y (⊥ : PrimeSpectrum (FractionRing R)) (by
      refine PrimeSpectrum.ext (h0.trans ?_)
      exact (Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))).symm)
    exact ⟨z, hz⟩)
  have hx : x.asIdeal.height = 1 := by
    refine le_antisymm ?_ (ENat.one_le_iff_ne_zero.2 fun h0 ↦ hx0 (Ideal.height_eq_zero_iff_eq_bot.1 h0))
    exact (idealHeight_eq_coheight (CommRingCat.of R) x).trans_le hx1
  obtain ⟨V, _, _, _, hV, φ, hφ, hfl, hc⟩ := exists_cDvr_flat R x.asIdeal hx
  obtain ⟨φK, hK⟩ := exists_map_fractionRing φ hφ
  have hK' : spMap φK ≫ spMap (algebraMap R (FractionRing R)) =
      spMap (algebraMap V (FractionRing V)) ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hK]
  obtain ⟨s, hs⟩ := hf V hV φ φK (by rw [reassoc_of% hK']) hK
  have HV := ThetaRuleCompare.isPullback_whisker (A := G)
    (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ)
  have HF := ThetaRuleCompare.isPullback_whisker (A := G)
    (Over.homMk (spMap (algebraMap V (FractionRing V))) rfl :
      Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ))
  have hφf : Flat (spMap φ) := Flat.SpecMap_iff.2 hfl
  have := MorphismProperty.of_isPullback (P := @Flat) HV.flip hφf
  have := fl (Over.mk (spMap φ ≫ χ))
  obtain ⟨v, rfl, -⟩ := Scheme.exists_preimage_of_isPullback HV y (IsLocalRing.closedPoint V)
    (PrimeSpectrum.ext hc.symm)
  have w : ((Over.homMk (spMap φK) (by simp only [Over.mk_hom]; rw [reassoc_of% hK']) :
      Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶
        Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) ▷ G).left ≫
      ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl :
        Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left =
      ((Over.homMk (spMap (algebraMap V (FractionRing V))) rfl :
        Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ)) ▷ G).left ≫
      ((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ G).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← comp_whiskerRight, ← comp_whiskerRight]
    congr 2
    exact Over.OverMorphism.ext hK'
  have hA := Exist.CubicalExtension.app_injective_generic HF
  have h₂ := congrArg (· ⁻¹ᵁ W) w
  simp only [Scheme.Hom.comp_preimage] at h₂
  exact extAt_of_flat H _ _ hA _ w W f s h₂.ge (hs _ le_rfl h₂.ge) v hy

end GlobalTheory.CodimOneExtend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreConstOfSpecialisationInvariant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory

theorem fibre_exists_finite_generizing {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] [T0Space Z] (q : Y → Z)
    (hq : Continuous q) (z : Z) :
    ∃ T : Set Y, T.Finite ∧ (∀ e ∈ T, q e = z) ∧ ∀ w, q w = z → ∃ e ∈ T, e ⤳ w := by
  have hfin : (irreducibleComponents (q ⁻¹' {z})).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have key : ∀ C : irreducibleComponents (q ⁻¹' {z}),
      ∃ e : Y, q e = z ∧ ∀ c ∈ C.1, e ⤳ (c : Y) := by
    intro C
    have hC : IsIrreducible C.1 := C.2.1
    have hCi : IsIrreducible (((↑) : q ⁻¹' {z} → Y) '' C.1) :=
      hC.image _ continuous_subtype_val.continuousOn
    have hgen := hCi.isGenericPoint_genericPoint_closure
    refine ⟨hCi.genericPoint, ?_, ?_⟩
    · obtain ⟨c, hc⟩ := hC.nonempty
      have hcz : q c = z := c.2
      have h1 : hCi.genericPoint ⤳ (c : Y) := hgen.specializes (subset_closure ⟨c, hc, rfl⟩)
      have h2 : hCi.genericPoint ∈ closure (((↑) : q ⁻¹' {z} → Y) '' C.1) := hgen.mem
      have h3 : closure (((↑) : q ⁻¹' {z} → Y) '' C.1) ⊆ q ⁻¹' closure {z} :=
        (closure_mono (by rintro _ ⟨d, -, rfl⟩; exact d.2)).trans (hq.closure_preimage_subset _)
      have h4 : z ⤳ q hCi.genericPoint := specializes_iff_mem_closure.2 (h3 h2)
      have h5 : q hCi.genericPoint ⤳ z := by
        have := h1.map hq
        rwa [hcz] at this
      exact (h5.antisymm h4).eq
    · intro c hc
      exact hgen.specializes (subset_closure ⟨c, hc, rfl⟩)
  choose f hf using key
  haveI : Finite (irreducibleComponents (q ⁻¹' {z})) := hfin.to_subtype
  refine ⟨Set.range f, Set.finite_range f, ?_, ?_⟩
  · rintro _ ⟨C, rfl⟩
    exact (hf C).1
  · intro w hw
    let w' : q ⁻¹' {z} := ⟨w, hw⟩
    refine ⟨f ⟨_, irreducibleComponent_mem_irreducibleComponents w'⟩, ⟨_, rfl⟩, ?_⟩
    exact (hf _).2 w' mem_irreducibleComponent

theorem fibre_const_of_specializes_invariant : ∀ (Y Z : Type) [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] [T0Space Z] (q : Y → Z), Continuous q → ∀ z : Z, _root_.IsPreconnected (q ⁻¹' {z}) → ∀ P : Y → Prop, (∀ a b, q a = z → q b = z → a ⤳ b → (P a ↔ P b)) → ∀ a b, q a = z → q b = z → P a → P b := by
  intro Y Z _ _ _ _ _ q hq z hpc P hP a b ha hb hPa
  obtain ⟨T, hTf, hTz, hTs⟩ := fibre_exists_finite_generizing q hq z
  by_contra hPb
  have closed : ∀ R : Y → Prop, IsClosed (⋃ e ∈ {e ∈ T | R e}, closure ({e} : Set Y)) :=
    fun R => (hTf.subset (fun _ h => h.1)).isClosed_biUnion (fun _ _ => isClosed_closure)
  have mem : ∀ (R : Y → Prop) (e w : Y), e ∈ T → R e → e ⤳ w →
      w ∈ ⋃ e ∈ {e ∈ T | R e}, closure ({e} : Set Y) := by
    intro R e w he hR hs
    exact Set.mem_biUnion ⟨he, hR⟩ (specializes_iff_mem_closure.1 hs)
  have mem' : ∀ (R : Y → Prop) (w : Y), w ∈ ⋃ e ∈ {e ∈ T | R e}, closure ({e} : Set Y) →
      ∃ e, e ∈ T ∧ R e ∧ e ⤳ w := by
    intro R w hw
    obtain ⟨e, ⟨he, hR⟩, hc⟩ := Set.mem_iUnion₂.1 hw
    exact ⟨e, he, hR, specializes_iff_mem_closure.2 hc⟩
  obtain ⟨w, hwS, hwt, hwt'⟩ := isPreconnected_closed_iff.1 hpc _ _ (closed P) (closed (fun e => ¬ P e))
    (by
      intro w hw
      obtain ⟨e, he, hs⟩ := hTs w hw
      by_cases h : P e
      · exact Or.inl (mem P e w he h hs)
      · exact Or.inr (mem _ e w he h hs))
    (by
      obtain ⟨e, he, hs⟩ := hTs a ha
      exact ⟨a, ha, mem P e a he ((hP e a (hTz e he) ha hs).2 hPa) hs⟩)
    (by
      obtain ⟨e, he, hs⟩ := hTs b hb
      exact ⟨b, hb, mem (fun e => ¬ P e) e b he (fun h => hPb ((hP e b (hTz e he) hb hs).1 h)) hs⟩)
  have hwz : q w = z := hwS
  obtain ⟨e₁, h₁, hP₁, hs₁⟩ := mem' P w hwt
  obtain ⟨e₂, h₂, hP₂, hs₂⟩ := mem' _ w hwt'
  exact hP₂ ((hP e₂ w (hTz e₂ h₂) hwz hs₂).2 ((hP e₁ w (hTz e₁ h₁) hwz hs₁).1 hP₁))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatKernelSymmetricBirigidifiedBundle
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerFlatP

theorem flat_of_finite_rep : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (B : Over (Sp R)) [GrpObj B],
    IsAbelianScheme B → ∀ N : LB B.left, N.IsLB → Out.RelAmple B N → ∀ M : LB B.left, M.IsLB →
    ∀ (H : Over (Sp R)) (j : H ⟶ B), IsClosedImmersion j.left → IsFinite H.hom →
    (∀ (T : Over (Sp R)) (x : T ⟶ B), GlobalTheory.MemKL B M x ↔ ∃ z : T ⟶ H, z ≫ j = x) → Flat H.hom := by
  intro R _ _ B _ hB N hN hamp M hM H j hj hfin hrep
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  refine GlobalTheory.T.flat_of_isFinite_of_flat_at_maximal R H hfin (fun m _ => ?_)
  set f := spMap (algebraMap R (Localization.AtPrime m)) with hf
  have hB' : IsAbelianScheme ((Over.pullback f).obj B) := GlobalTheory.isAbelianScheme_pullback_obj f B hB
  haveI := hB'.comm
  have hpb := IsPullback.of_hasPullback B.hom f
  obtain ⟨hP, -, -, -⟩ := GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ B N hB hN hamp
    (Localization.AtPrime m) f _ _ _ hpb
  have hML : (M.pull (pullback.fst B.hom f)).IsLB := pull_isLB hM _
  have hrep' := GlobalTheory.T.memKernelOfLineBundle_baseChange_representable _ _ f B M hM H j hrep
  have hth := GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy GlobalTheory.T.abelianScheme_laws_unconditional.1 _ ((Over.pullback f).obj B) hB' hP _ hML
  have hcl : IsClosedImmersion ((Over.pullback f).map j).left := by
    have e : ((Over.pullback f).map j).left =
        pullback.map H.hom f B.hom f j.left (𝟙 _) (𝟙 _) (by simp [Over.w j]) (by simp) := by
      first
      | rfl
      | (apply pullback.hom_ext <;> simp [Over.pullback_map_left])
      | (simp only [Over.pullback_map_left]; apply pullback.hom_ext <;> simp)
    rw [e]
    haveI : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
      ⟨fun _ _ hf hg => by haveI := hf; haveI := hg; infer_instance⟩
    exact MorphismProperty.pullback_map (P := @IsClosedImmersion) hj (inferInstance : IsClosedImmersion (𝟙 _)) (Over.w j).symm (by simp)
  have hfin' : IsFinite ((Over.pullback f).obj H).hom := by
    first
    | exact MorphismProperty.pullback_snd (P := @IsFinite) _ _ hfin
    | (haveI := hfin; exact (inferInstance : IsFinite (pullback.snd H.hom f)))
  exact GlobalTheory.T.lineBundleKernel_flat_of_finite_noetherian_local hG (Localization.AtPrime m) ((Over.pullback f).obj B) hB' hP _ hML hth _ _ hcl hrep' hfin'

theorem exists_closed_rep : ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B], IsAbelianScheme B →
    ∀ N : LB B.left, N.IsLB → Out.RelAmple B N → ∀ M : LB B.left, M.IsLB →
    ∃ (H : Over (Sp R)) (j : H ⟶ B), IsClosedImmersion j.left ∧
      ∀ (T : Over (Sp R)) (x : T ⟶ B), GlobalTheory.MemKL B M x ↔ ∃ z : T ⟶ H, z ≫ j = x := by
  intro R _ B _ hB N hN hamp M hM
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hP : IsProjBy B.hom := GlobalTheory.WtTower.isProjBy_of_relAmple B hN hamp
  obtain ⟨h0, -, h2⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B M hM
  obtain ⟨H, j, hj, hrep⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hG R B hB hP M (AbLaw.pw M 0) hM h0
  refine ⟨H, j, hj, fun T x => ?_⟩
  rw [← GlobalTheory.UU.inK_iff_memKL, h2 _ rfl T x]
  exact hrep T x

private theorem isFinite_of_closedImmersion_factor_through_finite {S : Scheme.{0}} {H F G : Over S} (j : H ⟶ G) (i : F ⟶ G)
    (m : H ⟶ F) (hm : m ≫ i = j) (hj : IsClosedImmersion j.left) (hF : IsFinite F.hom) : IsFinite H.hom := by
  haveI : IsSeparated (i.left ≫ G.hom) := by rw [Over.w i]; infer_instance
  haveI : IsSeparated i.left := IsSeparated.of_comp i.left G.hom
  haveI : IsClosedImmersion (m.left ≫ i.left) := by rw [← Over.comp_left, hm]; exact hj
  haveI : IsClosedImmersion m.left := IsClosedImmersion.of_comp m.left i.left
  rw [← Over.w m]; infer_instance

end GlobalTheory.KerFlatP

namespace GlobalTheory

open GlobalTheory.KerFlatP in

theorem kernel_finiteFlat : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G2 G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → Out.RelAmple G (P.pull (lift (𝟙 G) (𝟙 G)).left) → ∃ (H : Over (Sp R)) (i : H ⟶ G), IsClosedImmersion i.left ∧ IsFinite H.hom ∧ Flat H.hom ∧ ∀ (T : Over (Sp R)) (x : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) ↔ ∃ y : T ⟶ H, y ≫ i = x := by
  intro R _ _ G _ hG P hP h1 h2 hsym hamp
  have hL : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  obtain ⟨HL, _, iL, -, -, hfinL, -, hrepL⟩ := GlobalTheory.kernel_finiteFlat_subgroup R G hG _ hL hamp
  have hGG : IsAbelianScheme (G ⊗ G) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor G G hG hG
  haveI : IsProper G.hom := hG.proper
  haveI : IsProper (G ⊗ G).hom := by
    show IsProper (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  have hL1 := pull_isLB hL (fst G G).left
  have hL2 := pull_isLB hL (snd G G).left
  have hN := GlobalTheory.CechPic.isLB_tens hL1 hL2
  have hNamp : Out.RelAmple (G ⊗ G) (GlobalTheory.CechPic.tens _ _) :=
    GlobalTheory.MumProd.SumPol.relAmple_prod G G hL hL hN
      (by rw [GlobalTheory.CechPic.cls_tens hL1 hL2 hN, GlobalTheory.CechPic.cls_pull hL _ hL1, GlobalTheory.CechPic.cls_pull hL _ hL2])
      hamp hamp

  obtain ⟨K, k, hk, hrepK⟩ := exists_closed_rep R (G ⊗ G) hGG _ hN hNamp P hP

  have hmemK : GlobalTheory.MemKL (G ⊗ G) P (lift (k ≫ fst G G) (k ≫ snd G G)) := by
    rw [lift_comp_fst_snd]; exact (hrepK K k).2 ⟨𝟙 K, Category.id_comp _⟩
  obtain ⟨ha, hb⟩ := GlobalTheory.T.trivial_evaluations_of_mem_kernel_symmetric_pair R G hG P hP h1 h2 hsym K _ _ hmemK
  obtain ⟨za, hza⟩ := (hrepL K _).1 (GlobalTheory.T.mem_kernel_diagonal_restriction_of_symmetric_trivial R G hG P hP h1 h2 hsym K _ ha)
  obtain ⟨zb, hzb⟩ := (hrepL K _).1 (GlobalTheory.T.mem_kernel_diagonal_restriction_of_symmetric_trivial R G hG P hP h1 h2 hsym K _ hb)
  have hfinHL2 : IsFinite (HL ⊗ HL).hom := by
    haveI := hfinL
    show IsFinite (pullback.fst HL.hom HL.hom ≫ HL.hom)
    infer_instance
  have hfinK : IsFinite K.hom := by
    refine isFinite_of_closedImmersion_factor_through_finite k (lift (fst HL HL ≫ iL) (snd HL HL ≫ iL)) (lift za zb) ?_ hk hfinHL2
    apply CartesianMonoidalCategory.hom_ext <;> simp [hza, hzb]
  have hflatK : Flat K.hom := flat_of_finite_rep R (G ⊗ G) hGG _ hN hNamp P hP K k hk hfinK hrepK

  set e : G ⟶ G ⊗ G := lift (𝟙 G) (1 : G ⟶ G) with he
  have hxe : ∀ {T : Over (Sp R)} (x : T ⟶ G), x ≫ e = lift x (1 : T ⟶ G) := by
    intro T x
    apply CartesianMonoidalCategory.hom_ext <;> simp [e]
  let H : Over (Sp R) := Over.mk (pullback.snd k.left e.left ≫ G.hom)
  let i : H ⟶ G := Over.homMk (pullback.snd k.left e.left) rfl
  haveI := hk
  have hi : IsClosedImmersion i.left := by
    show IsClosedImmersion (pullback.snd k.left e.left)
    infer_instance
  have hwK : pullback.fst k.left e.left ≫ K.hom = H.hom := by
    show _ = pullback.snd k.left e.left ≫ G.hom
    rw [← Over.w k, pullback.condition_assoc, Over.w e]
  let s : H ⟶ K := Over.homMk (pullback.fst k.left e.left) hwK
  have hs : s ≫ k = i ≫ e :=
    Over.OverMorphism.ext (by rw [Over.comp_left, Over.comp_left]; exact pullback.condition)
  have hmemH : ∀ (T : Over (Sp R)) (x : T ⟶ G),
      (∃ t : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) ↔ ∃ y : T ⟶ H, y ≫ i = x := by
    intro T x
    constructor
    · intro htr
      obtain ⟨z, hz⟩ := (hrepK T _).1 (GlobalTheory.T.mem_kernel_lift_one_of_axis_trivial_bundle R G hG P hP h1 h2 hsym T x htr)
      have hz' : z.left ≫ k.left = x.left ≫ e.left := by
        rw [← Over.comp_left, hz, ← hxe, Over.comp_left]
      refine ⟨Over.homMk (pullback.lift z.left x.left hz') ?_, ?_⟩
      · show pullback.lift z.left x.left hz' ≫ pullback.snd k.left e.left ≫ G.hom = T.hom
        rw [pullback.lift_snd_assoc, Over.w x]
      · exact Over.OverMorphism.ext (by rw [Over.comp_left]; exact pullback.lift_snd _ _ _)
    · rintro ⟨y, rfl⟩
      have hm : GlobalTheory.MemKL (G ⊗ G) P (lift (y ≫ i) (1 : T ⟶ G)) := by
        refine (hrepK T _).2 ⟨y ≫ s, ?_⟩
        rw [Category.assoc, hs, ← Category.assoc, hxe]
      exact (GlobalTheory.T.trivial_evaluations_of_mem_kernel_symmetric_pair R G hG P hP h1 h2 hsym T _ _ hm).1

  have hLi : GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) i :=
    GlobalTheory.T.mem_kernel_diagonal_restriction_of_symmetric_trivial R G hG P hP h1 h2 hsym H i ((hmemH H i).2 ⟨𝟙 H, Category.id_comp _⟩)
  obtain ⟨zH, hzH⟩ := (hrepL H i).1 hLi
  have hfinH : IsFinite H.hom := isFinite_of_closedImmersion_factor_through_finite i iL zH hzH hi hfinL

  obtain ⟨r, hr⟩ := (hmemH K (k ≫ fst G G)).1 ha
  have hsr : s ≫ r = 𝟙 H := by
    haveI : Mono i.left := by
      show Mono (pullback.snd k.left e.left)
      infer_instance
    have h3 : s ≫ r ≫ i = 𝟙 H ≫ i := by
      rw [hr, ← Category.assoc, hs, Category.assoc]; simp [e]
    apply Over.OverMorphism.ext
    exact (cancel_mono i.left).1 (by simpa [Over.comp_left] using congrArg CommaMorphism.left h3)
  exact ⟨H, i, hi, hfinH, GlobalTheory.T.flat_of_finite_retract_of_finite_flat R H K s r hsr hfinH hfinK hflatK, hmemH⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIntegerRingActionsPrincipallyPolarisedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_integerRing_actions_principallyPolarised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K)), letI := H.starRing; Set.Finite {act : 𝓞 E → (P.A ⟶ P.A) | ∃ ρ : P.OAct (𝓞 E), ∀ a, ρ.act a = act a} := by
  first | exact @GlobalTheory.UMin.FinAct.finite_oActs | exact GlobalTheory.UMin.FinAct.finite_oActs | (intros; apply GlobalTheory.UMin.FinAct.finite_oActs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsBalancedFormsUptoAutStatement
section
open GlobalTheory.PolFan GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_minimiser_systems_balanced_forms_upto_aut : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N → ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)), ∃ S : Finset ((Fin n → ZMod N) → Y), ∀ b ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b x x) → ∃ e : Y ≃ₗ[O] Y, ∀ μ : (Fin n → ZMod N) → Y, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → pull e.toLinearMap b (μ cl) (μ cl) ≤ pull e.toLinearMap b α α) → μ ∈ S := by
  first | exact @GlobalTheory.Poinc.MinSysTypeBal.finite_minimiser_systems_upTo_aut | exact GlobalTheory.Poinc.MinSysTypeBal.finite_minimiser_systems_upTo_aut | (intros; apply GlobalTheory.Poinc.MinSysTypeBal.finite_minimiser_systems_upTo_aut <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMorphismValuativeLiftingNormalDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory

theorem finite_lift_fractionField (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (Z P : Scheme.{0}) (p : Z ⟶ P) (ξ₀ : Sp R ⟶ P) (y : Sp (FractionRing R) ⟶ Z)
    (hp : IsFinite p) (hy : y ≫ p = jK R ≫ ξ₀) :
    ∃ ξ : Sp R ⟶ Z, jK R ≫ ξ = y ∧ ξ ≫ p = ξ₀ := by
  first
  | exact @_root_.GlobalTheory.RetractionLiftSection.lift_finite
  | exact _root_.GlobalTheory.RetractionLiftSection.lift_finite
  | (apply _root_.GlobalTheory.RetractionLiftSection.lift_finite <;> assumption)
  | (intros; apply _root_.GlobalTheory.RetractionLiftSection.lift_finite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RetractionLiftSection.lift_finite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RetractionLiftSection.lift_finite ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOverProjectiveSpaceProjectiveAmpleTwistStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_over_projectiveSpace_projective_ample_twist : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] (n k : ℕ) (Z : Scheme.{0}) (p : Z ⟶ PSpace o n), 1 ≤ k → IsFinite p → IsProjOver (p ≫ PSpace.str o n) ∧ (lbPow ((ProjSpace.O1 o n).pull p) k).IsLB ∧ IsAmpleLB (lbPow ((ProjSpace.O1 o n).pull p) k) ∧ ∀ (Y : Scheme.{0}) (h : Y ⟶ Z), LBIso ((lbPow ((ProjSpace.O1 o n).pull p) k).pull h) (lbPow ((ProjSpace.O1 o n).pull (h ≫ p)) k) := by
  first | exact @GlobalTheory.FiniteOverPSpace.isProjOver_and_isAmpleLB | exact GlobalTheory.FiniteOverPSpace.isProjOver_and_isAmpleLB | (intros; apply GlobalTheory.FiniteOverPSpace.isProjOver_and_isAmpleLB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartPowEqOneLocalStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_part_pow_eq_one_local : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X} {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q) {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left} (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (h : aH P' x0 hu hg.1 ^ q = 1) (S : Type) [CommRing S] [hS : IsLocalRing S] (y : Sp S ⟶ (torsion G' q).left), (∃ s : Sp (IsLocalRing.ResidueField S) ⟶ (Hs P' x0 hu).left, s ≫ (jH P' x0 hu hg.1 h).left = spMap (IsLocalRing.residue S) ≫ y) → ∃ s : Sp S ⟶ (Hs P' x0 hu).left, s ≫ (jH P' x0 hu hg.1 h).left = y := by
  first | exact @GlobalTheory.FinPartAt.lift_of_residue | exact GlobalTheory.FinPartAt.lift_of_residue | (intros; apply GlobalTheory.FinPartAt.lift_of_residue <;> assumption)
end
end

