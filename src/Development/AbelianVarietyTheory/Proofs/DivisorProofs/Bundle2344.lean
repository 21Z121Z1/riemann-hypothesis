import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpMapClosedPointOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2220
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0050
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfArcsAndGoodReductionPoints
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
open GlobalTheory.ArcIntegral

namespace GlobalTheory.ArcIntegralMixed

theorem exists_denominator {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A] (ϖ : A)
    (hϖ : Irreducible ϖ) (S : Type) [CommRing S] [Algebra (PowerSeries A) S]
    [IsLocalization.Away (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A) S] (v : S)
    (hv : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
      [IsFractionRing R K] (ρ : PowerSeries A →+* R) (ψ : S →+* K),
      ψ.comp (algebraMap (PowerSeries A) S) = (algebraMap R K).comp ρ → IsUnit (ρ PowerSeries.X) →
      ψ v ∈ (algebraMap R K).range) :
    ∃ s t : PowerSeries A, ¬ PowerSeries.C ϖ ∣ t ∧ v * algebraMap _ S t = algebraMap _ S s := by
  obtain ⟨hp, hdvr⟩ := GlobalTheory.T.isDiscreteValuationRing_localization_powerSeries_uniformiser A ϖ hϖ
  obtain ⟨R, _, _, _, _, _⟩ : ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : Algebra (PowerSeries A) R), IsLocalization.AtPrime R (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}) :=
    ⟨_, _, _, hdvr, _, inferInstance⟩
  let K := FractionRing R
  have hρ : Function.Injective (algebraMap (PowerSeries A) R) :=
    IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}))
  let f : PowerSeries A →+* K := (algebraMap R K).comp (algebraMap (PowerSeries A) R)
  have hf : Function.Injective f := (IsFractionRing.injective R K).comp hρ
  have hC : Function.Injective (f.comp (PowerSeries.C (R := A))) := hf.comp PowerSeries.C_injective
  haveI : CharZero K := (RingHom.charZero_iff hC).1 inferInstance
  have h0 : (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A) ≠ 0 :=
    mul_ne_zero (fun h => hϖ.ne_zero (PowerSeries.C_injective (h.trans (map_zero _).symm))) PowerSeries.X_ne_zero
  have hu : IsUnit (f (PowerSeries.C ϖ * PowerSeries.X)) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ hf).2 h0)
  obtain ⟨ψ, hψ⟩ := exists_away_lift (S := S) _ f hu
  have hψi : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, m⟩, ha⟩ :=
      IsLocalization.surj (Submonoid.powers (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A)) x
    have ha0 : a = 0 := hf (by
      have := congrArg ψ ha
      rw [map_mul, hx, zero_mul, hψ] at this
      rw [← this, map_zero])
    rw [ha0, map_zero] at ha
    exact (IsLocalization.map_units S m).mul_left_eq_zero.1 ha
  have hX : (PowerSeries.X : PowerSeries A) ∈ (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).primeCompl := by
    intro hm
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hm
    have := congrArg (PowerSeries.coeff 1) hq
    rw [PowerSeries.coeff_one_X, PowerSeries.coeff_C_mul] at this
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one _ this.symm)
  obtain ⟨r, hr⟩ := hv R K (algebraMap _ R) ψ (RingHom.ext hψ) (IsLocalization.map_units R ⟨_, hX⟩)
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj (Ideal.span {(PowerSeries.C ϖ : PowerSeries A)}).primeCompl r
  refine ⟨s, t, fun hd => t.2 (Ideal.mem_span_singleton.2 hd), hψi ?_⟩
  rw [map_mul, hψ, hψ, ← hr]
  exact (map_mul (algebraMap R K) _ _).symm.trans (congrArg (algebraMap R K) hst)

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ g : A →+* B, f = spMap g :=
  ⟨(Spec.preimage f).hom, (Spec.map_preimage f).symm⟩

theorem spMap_injective {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem integral_of_arcs_of_good : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype), Y.N3 → Y.N4 → Y.SplitFibres → IsOpenImmersion Y.j → ∀ (U₀ W₀ : Y.X.Opens) (f₀ : Γ(Y.X, W₀)), (∀ x ∈ U₀, x ∈ Set.range Y.j → x ∈ W₀) → (∀ (a : ArcIn D l V.subtype ℂ (c.F.val.toRingHom.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X), Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (c.F.val.toRingHom.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ U₀ → ∀ h : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ⁻¹ᵁ W₀, ev (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) W₀ h f₀ ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range) → (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (y : Sp K ⟶ Xo.XF c), ⊤ ≤ z ⁻¹ᵁ U₀ → y ≫ Y.j = spMap (algebraMap R K) ≫ z → Set.range z ⊆ abLocus Y.t.G → ∀ h : ⊤ ≤ (spMap (algebraMap R K) ≫ z) ⁻¹ᵁ W₀, ev (spMap (algebraMap R K) ≫ z) W₀ h f₀ ∈ (algebraMap R K).range) → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (y : Sp K ⟶ Xo.XF c), Countable R → ⊤ ≤ z ⁻¹ᵁ U₀ → y ≫ Y.j = spMap (algebraMap R K) ≫ z → ∀ h : ⊤ ≤ (spMap (algebraMap R K) ≫ z) ⁻¹ᵁ W₀, ev (spMap (algebraMap R K) ≫ z) W₀ h f₀ ∈ (algebraMap R K).range := by
  intro E _ _ _ H Dw l Xo c V Y h3 h4 hS hj U₀ W₀ f₀ hUW harc hgood R K _ _ _ _ _ _ _ z y hcount hU hy h
  by_cases hab : Set.range z ⊆ abLocus Y.t.G
  · exact hgood R K z y hU hy hab h
  have hzW : ∀ {A : Type} [CommRing A] (w : Sp A ⟶ Y.X), Set.range w ⊆ Set.range Y.j → ⊤ ≤ w ⁻¹ᵁ U₀ →
      ⊤ ≤ w ⁻¹ᵁ W₀ := fun w hr hu x hx => hUW _ (hu hx) (hr ⟨x, rfl⟩)
  obtain ⟨io, hio⟩ := exists_spMap (y ≫ pullback.snd _ _)
  obtain ⟨b₀, hover⟩ := exists_spMap (z ≫ Y.s)
  have hcomp : (algebraMap R K).comp b₀ = io.comp V.subtype := spMap_injective (by
    rw [← sp_comp, ← sp_comp, ← hover, ← hio, ← Category.assoc, ← hy, Model.j, ← Y.jQ_over]
    simp only [Category.assoc, pullback.condition])
  have hgen : Set.range (spMap (algebraMap R K) ≫ z) ⊆ Set.range Y.j := by
    rw [← hy]; rintro _ ⟨x, rfl⟩; exact ⟨y x, (Scheme.Hom.comp_apply _ _ _).symm⟩
  have hch : CharZero R := (RingHom.charZero_iff (IsFractionRing.injective R K)).2 inferInstance
  obtain ⟨T, i, hi, hil, hcard⟩ := GlobalTheory.CountableCompletion.exists_cdvr_mk_le_continuum R hcount
  have hiF : Function.Injective ((algebraMap T.V T.Fr).comp i) := (IsFractionRing.injective T.V T.Fr).comp hi
  obtain ⟨iK, hiK⟩ := exists_frac_lift (K := K) _ hiF
  let y' : Sp T.V ⟶ Y.X := spMap i ≫ z
  let b : V →+* T.V := i.comp b₀
  let io' : c.F →+* T.Fr := iK.comp io
  have hbio : (algebraMap T.V T.Fr).comp b = io'.comp V.subtype := by
    simp only [b, io']
    rw [← RingHom.comp_assoc, ← hiK, RingHom.comp_assoc, hcomp, RingHom.comp_assoc]
  have hy' : y' ≫ Y.s = spMap b := by
    simp only [y', Category.assoc]; rw [hover, sp_comp]
  let zT : Sp T.Fr ⟶ Xo.XF c := spMap iK ≫ y
  have hzT : zT ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' := by
    simp only [y', zT]
    rw [Category.assoc, hy, ← Category.assoc, sp_comp, hiK, ← sp_comp, Category.assoc]
  have hzT' : zT ≫ pullback.snd _ _ = spMap io' := by
    simp only [zT, io']
    rw [Category.assoc, hio, sp_comp]
  clear_value zT
  have hbad : ¬ Set.range y' ⊆ abLocus Y.t.G := fun hy => hab (by
    rintro _ ⟨x, rfl⟩
    rcases point_cases R K x with ⟨p, rfl⟩ | rfl
    · exact range_j_subset Y (hgen ⟨p, by rw [Scheme.Hom.comp_apply]⟩)
    · have e : spMap i (IsLocalRing.closedPoint T.V) = IsLocalRing.closedPoint R := spMap_closedPoint i
      have := hy ⟨IsLocalRing.closedPoint T.V, rfl⟩
      change (spMap i ≫ z) (IsLocalRing.closedPoint T.V) ∈ _ at this
      erw [Scheme.Hom.comp_apply, e] at this; exact this)
  obtain ⟨T', g, ϖ, a, hg, hgf, hϖ, hA⟩ := GlobalTheory.T.exists_arcData_of_badReduction_finiteExtension E H Dw l Xo c V Y h3 hS T io' b y' zT hbio hy' hzT' hzT hbad
  have hcpl : IsAdicComplete (Ideal.span {ϖ}) T'.V := hϖ.maximalIdeal_eq ▸ T'.cpl
  obtain ⟨χ₀, hχ, hsp⟩ := h4 T'.V (g.comp b) ϖ a (Or.inr ⟨inferInstance, hϖ, hcpl⟩)
  obtain ⟨hover₀, hab₀, hopen, hW⟩ := (hχ χ₀).1 rfl
  obtain ⟨W⟩ := (Y.hasArcData_iff a _ _ _ χ₀).1 hW
  obtain ⟨-, -, evu, hevC, hevX, -⟩ := GlobalTheory.UniformiserEval.dvr_admissibleBase_and_powerSeries_evalUniformiser T'.V ϖ hϖ T'.cpl
  have hgF : Function.Injective ((algebraMap T'.V T'.Fr).comp g) := (IsFractionRing.injective T'.V T'.Fr).comp hg
  obtain ⟨gF, hgF'⟩ := exists_frac_lift (K := T.Fr) _ hgF
  have hχy : spMap evu ≫ χ₀ = spMap g ≫ y' := hsp hϖ (spMap g ≫ y') evu (by rw [Category.assoc, hy', sp_comp]) (by
      rintro _ ⟨x, rfl⟩
      have e : Out.jK T'.V ≫ spMap g ≫ y' = spMap gF ≫ zT ≫ Y.j := by
        rw [hzT, ← Category.assoc, ← Category.assoc, sp_comp, ← hgF', ← sp_comp]
        rfl
      exact ⟨zT (spMap gF x), by rw [e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]⟩) hA hevC hevX
  have hχz : spMap evu ≫ χ₀ = spMap g ≫ spMap i ≫ z := hχy
  haveI hgl : IsLocalHom g := RingHom.IsIntegral.isLocalHom hgf.to_isIntegral hg
  have hχU : ⊤ ≤ χ₀ ⁻¹ᵁ U₀ := by
    have hc : χ₀ (IsLocalRing.closedPoint (PowerSeries T'.V)) ∈ U₀ := by
      rw [← spMap_closedPoint_of_surjective evu (fun x => ⟨PowerSeries.C x, hevC x⟩)]
      change (spMap evu ≫ χ₀) (IsLocalRing.closedPoint T'.V) ∈ U₀
      rw [hχz]
      exact hU (Set.mem_univ ((spMap g ≫ spMap i) (IsLocalRing.closedPoint T'.V)))
    exact ((IsLocalRing.closed_point_mem_iff (U := χ₀ ⁻¹ᵁ U₀)).1 hc).ge

  let S := Localization.Away (PowerSeries.C ϖ * PowerSeries.X : PowerSeries T'.V)
  let ι : PowerSeries T'.V →+* S := algebraMap _ _
  have huX : IsUnit (ι (PowerSeries.C ϖ * PowerSeries.X)) := IsLocalization.Away.algebraMap_isUnit _
  have hSj : Set.range (spMap ι ≫ χ₀) ⊆ Set.range Y.j := by
    rintro _ ⟨x, rfl⟩
    exact hopen (spMap ι x) fun hx => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _
      (show ι (PowerSeries.C ϖ * PowerSeries.X) ∈ x.asIdeal from hx) huX)
  have hSW : ⊤ ≤ (spMap ι ≫ χ₀) ⁻¹ᵁ W₀ := hzW _ hSj (le_preimage_comp _ hχU)

  have hcard' : Cardinal.mk T'.Fr ≤ Cardinal.continuum := by
    rw [show Cardinal.mk T'.Fr = Cardinal.mk T'.V from IsFractionRing.cardinalMk T'.V T'.Fr]
    exact mk_le_continuum_of_finite g hgf hcard
  obtain ⟨κ, hκ⟩ := @GlobalTheory.ComplexEmbedding.exists_embedding_of_mk_le_continuum c.F T'.Fr _ _ _
    (gF.comp io').toAlgebra hcard' c.F.val.toRingHom
  let κ₀ : T'.V →+* ℂ := κ.comp (algebraMap T'.V T'.Fr)
  have hκ₀ : Function.Injective κ₀ := κ.injective.comp (IsFractionRing.injective T'.V T'.Fr)
  have hb' : c.F.val.toRingHom.comp V.subtype = κ₀.comp (g.comp b) := by
    rw [← hκ]
    change κ.comp (gF.comp (io'.comp V.subtype)) = κ.comp (((algebraMap T'.V T'.Fr).comp g).comp b)
    rw [← hbio, ← hgF']; rfl
  obtain ⟨h1, h2, -, hL4, hL5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨⟨a₁, p, hp⟩, hbc⟩ := GlobalTheory.ArcQBC.baseChanges h1 h2 hL4.unifBaseChange hL5 E H Dw l Xo c _ _ Y T'.V ℂ
    (g.comp b) a κ₀ hκ₀ _ hb'
  obtain ⟨hW₁, -⟩ := hbc a₁ p hp
  obtain ⟨W₁, -⟩ := hW₁ χ₀ W
  have hϖ0 : κ₀ ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hκ₀ (h0.trans (map_zero _).symm))
  have hXu : IsUnit ((HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map κ₀) (PowerSeries.C ϖ * PowerSeries.X)) := by
    rw [map_mul]
    refine IsUnit.mul ?_ (isUnit_map_X κ₀)
    rw [RingHom.comp_apply, PowerSeries.map_C]
    exact ((IsUnit.mk0 _ hϖ0).map _).map _
  obtain ⟨ιC, hιC'⟩ := exists_away_lift (S := S) _ _ hXu
  have hιC : ∀ s, ιC (ι s) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map κ₀ s) :=
    fun s => (hιC' s).trans (RingHom.comp_apply _ _ _)
  have hpt : spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ spMap (PowerSeries.map κ₀) ≫ χ₀ = spMap ιC ≫ spMap ι ≫ χ₀ := by
    rw [← Category.assoc, ← Category.assoc (spMap ιC), sp_comp, sp_comp,
      show ιC.comp ι = (HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map κ₀) from RingHom.ext hιC]
  have hLh : ⊤ ≤ (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ spMap (PowerSeries.map κ₀) ≫ χ₀) ⁻¹ᵁ W₀ := by
    rw [hpt]; exact le_preimage_comp _ hSW
  have hres := harc a₁ (spMap (PowerSeries.map κ₀) ≫ χ₀) ((Y.hasArcData_iff _ _ _ _ _).2 ⟨W₁⟩) (by
      rw [Category.assoc, hover₀, sp_comp, sp_comp, sp_comp, hb']
      exact congrArg spMap (RingHom.ext fun x => PowerSeries.map_C κ₀ _)) (fun x hx => by
      refine hopen (spMap (PowerSeries.map κ₀) x) fun hm => ?_
      have hm' : PowerSeries.map κ₀ (PowerSeries.C ϖ * PowerSeries.X) ∈ x.asIdeal := hm
      rw [map_mul, PowerSeries.map_C, PowerSeries.map_X] at hm'
      exact hx ((Ideal.unit_mul_mem_iff_mem _ ((IsUnit.mk0 _ hϖ0).map _)).1 hm'))
    (le_preimage_comp _ hχU) hLh
  rw [ev_factor ιC (spMap ι ≫ χ₀) _ hpt W₀ hSW hLh f₀] at hres

  have hden := exists_denominator ϖ hϖ S (ev (spMap ι ≫ χ₀) W₀ hSW f₀) (by
    intro R' K' _ _ _ _ _ _ _ ρ ψ hψ hρ
    have e : spMap (algebraMap R' K') ≫ spMap ρ ≫ χ₀ = spMap ψ ≫ spMap ι ≫ χ₀ := by
      rw [← Category.assoc, ← Category.assoc (spMap ψ), sp_comp, sp_comp, ← hψ]
    have hW' : ⊤ ≤ (spMap (algebraMap R' K') ≫ spMap ρ ≫ χ₀) ⁻¹ᵁ W₀ := by
      rw [e]; exact le_preimage_comp _ hSW
    rw [← ev_factor ψ (spMap ι ≫ χ₀) _ e W₀ hSW hW' f₀]
    refine hgood R' K' (spMap ρ ≫ χ₀) (spMap ψ ≫ IsOpenImmersion.lift Y.j (spMap ι ≫ χ₀) hSj)
      (le_preimage_comp _ hχU) (by rw [Category.assoc, IsOpenImmersion.lift_fac, e]) ?_ hW'
    rintro _ ⟨x, rfl⟩
    exact (hab₀ (spMap ρ x)).2 fun hx => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _
      (show ρ PowerSeries.X ∈ x.asIdeal from hx) hρ))
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_powerSeries_of_no_pole_away_uniformizer_X T'.V ϖ hϖ κ₀ hκ₀ S ιC hιC _ hres hden

  have hϖu : IsUnit ((algebraMap T'.V T'.Fr).comp evu (PowerSeries.C ϖ * PowerSeries.X)) := by
    rw [RingHom.comp_apply, map_mul evu, hevC, hevX]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective T'.V T'.Fr)).2
      (mul_ne_zero hϖ.ne_zero hϖ.ne_zero))
  obtain ⟨φS, hφS⟩ := exists_away_lift (S := S) _ _ hϖu
  have hgi : Function.Injective ((algebraMap T'.V T'.Fr).comp (g.comp i)) :=
    (IsFractionRing.injective T'.V T'.Fr).comp (hg.comp hi)
  obtain ⟨la, hla⟩ := exists_frac_lift (K := K) _ hgi
  have hpt2 : spMap la ≫ spMap (algebraMap R K) ≫ z = spMap φS ≫ spMap ι ≫ χ₀ := by
    have e1 : spMap la ≫ spMap (algebraMap R K) ≫ z = spMap ((algebraMap T'.V T'.Fr).comp (g.comp i)) ≫ z := by
      rw [← Category.assoc, sp_comp, hla]
    have e2 : spMap φS ≫ spMap ι ≫ χ₀ = spMap ((algebraMap T'.V T'.Fr).comp (g.comp i)) ≫ z := by
      rw [← Category.assoc, sp_comp, show φS.comp ι = (algebraMap T'.V T'.Fr).comp evu from RingHom.ext hφS,
        ← sp_comp, Category.assoc, hχz, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp]
    rw [e1, e2]
  have hval : la (ev (spMap (algebraMap R K) ≫ z) W₀ h f₀) = algebraMap T'.V T'.Fr (evu s) := by
    rw [← ev_factor la (spMap (algebraMap R K) ≫ z) _ rfl W₀ h (le_preimage_comp _ h),
      GlobalTheory.FlagMod.ev_congr hpt2 W₀ _ (le_preimage_comp _ hSW), ev_factor φS _ _ rfl W₀ hSW, hs, hφS]
    rfl
  haveI : IsLocalHom (g.comp i) := inferInstance
  exact mem_range_of_map (g.comp i) la (fun r => RingHom.congr_fun hla r) _ ⟨evu s, hval.symm⟩

end GlobalTheory.ArcIntegralMixed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InteriorLevelActionEqRestrictionLevelMoveInv
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelMoveRestr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_frPt_ptF {K : Type} [Field K] [Algebra c.F K] (t : Sp K ⟶ Xo.XF c)
    (ht : t ≫ pullback.snd _ _ = spMap (algebraMap c.F K)) : ∃ y : FrPt Xo c K, ptF y = t := by
  obtain ⟨y, hy⟩ := GlobalTheory.FlagTan.exists_frPt (Xo := Xo) (c := c) (S := K) (t ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, sOf, ← Spec.map_comp]; rfl)
  refine ⟨y, pullback.hom_ext ?_ ?_⟩
  · simp only [ptF, pullback.lift_fst]; exact hy
  · simp only [ptF, pullback.lift_snd]; exact ht.symm

theorem restr_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ γ : Γ, (ρ γ).hom ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c (ι γ)⁻¹ := by
  intro E _ _ _ H Dw l Xo c TF Z hpq hA Γ _ ι ρ hρ γ
  haveI : IsSeparated Xo.s := Formalism.L2.Pj.sepX Xo
  haveI : IsReduced (Xo.XF c) := GlobalTheory.TransitionUnique.isReduced_XF Xo c
  refine ext_of_fromSpecResidueField_eq _ _ (pullback.snd _ _) Set.univ dense_univ (fun x _ => ?_) ?_
  · let t : Spec ((V₀ TF.Y Z).residueField x) ⟶ Sp c.F :=
      (V₀ TF.Y Z).fromSpecResidueField x ≫ i₀ TF.Y Z ≫ pullback.snd _ _
    letI : Algebra c.F ((V₀ TF.Y Z).residueField x) := (Spec.preimage t).hom.toAlgebra
    obtain ⟨y, hy⟩ := exists_frPt_ptF (K := (V₀ TF.Y Z).residueField x)
      ((V₀ TF.Y Z).fromSpecResidueField x ≫ i₀ TF.Y Z) (by
        rw [Category.assoc]
        exact (Spec.map_preimage t).symm)
    have h1 := hρ.2 γ ((V₀ TF.Y Z).residueField x) y ((V₀ TF.Y Z).fromSpecResidueField x) hy.symm
    rw [h1, GlobalTheory.CompLevelStab.ptF_move hpq hA Xo c, hy, Category.assoc]
  · have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
    have h0 := hρ.1 γ
    rw [GlobalTheory.CompLevelStab.j₀_s₀, hid, Category.comp_id] at h0
    rw [Category.assoc, Category.assoc, GlobalTheory.CompLevelStab.mvF_snd]
    exact h0

end GlobalTheory.LevelMoveRestr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleComponentsClopenPartition
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

open TopologicalSpace

namespace GlobalTheory.CompPart

theorem isIrreducible_generizations {Z : Scheme.{0}} (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x)) (x : Z) :
    IsIrreducible {y : Z | y ⤳ x} := by
  haveI := hd x
  rw [← Scheme.range_fromSpecStalk, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ (Spec (Z.presheaf.stalk x))).image _
    (Z.fromSpecStalk x).continuous.continuousOn

theorem eq_closure_generizations {Z : Scheme.{0}} (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x))
    {C : Set Z} (hC : C ∈ irreducibleComponents Z) {x : Z} (hx : x ∈ C) :
    C = closure {y : Z | y ⤳ x} := by
  have hcl : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 hcl
  have hηx : η ⤳ x := by
    rw [specializes_iff_mem_closure, hη.def]; exact hx
  have hsub : C ⊆ closure {y : Z | y ⤳ x} := by
    rw [← hη.def]
    exact closure_mono (Set.singleton_subset_iff.2 hηx)
  exact hsub.antisymm (hC.2 (isIrreducible_generizations hd x).closure hsub)

theorem existsUnique_mem {Z : Scheme.{0}} (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x)) (x : Z) :
    ∃! C : irreducibleComponents Z, x ∈ (C : Set Z) :=
  ⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, mem_irreducibleComponent, fun C hC =>
    Subtype.ext ((eq_closure_generizations hd C.2 hC).trans
      (eq_closure_generizations hd (irreducibleComponent_mem_irreducibleComponents x)
        mem_irreducibleComponent).symm)⟩

theorem isOpen_of_mem {Z : Scheme.{0}} [NoetherianSpace Z] (hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x))
    {C : Set Z} (hC : C ∈ irreducibleComponents Z) : IsOpen C := by
  have hfin : (irreducibleComponents Z).Finite := NoetherianSpace.finite_irreducibleComponents
  have hcompl : Cᶜ = ⋃ D ∈ {D ∈ irreducibleComponents Z | D ≠ C}, D := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hy
      exact ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y,
        fun h => hy (h ▸ mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
    · rintro ⟨D, ⟨hD, hne⟩, hyD⟩ hyC
      exact hne (congrArg Subtype.val ((existsUnique_mem hd y).unique (y₁ := ⟨D, hD⟩) (y₂ := ⟨C, hC⟩) hyD hyC))
  rw [← isClosed_compl_iff, hcompl]
  exact (hfin.subset fun D hD => hD.1).isClosed_biUnion fun D hD =>
    isClosed_of_mem_irreducibleComponents D hD.1

end GlobalTheory.CompPart

theorem GlobalTheory.irreducibleComponents_clopen_partition : ∀ (n : ℕ) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)),
    IsProjOver z → GlobalTheory.IsNormalScheme Z → ∃ (ι : Type) (_ : Fintype ι) (W : ι → Set Z),
      (∀ c, IsClopen (W c)) ∧ (∀ c, IsIrreducible (W c)) ∧ ∀ x, ∃! c, x ∈ W c := by
  intro n Z z hz hN
  haveI : IsNoetherianRing (cycAway n) :=
    is_noetherian_subring_closure _ (Set.toFinite _)
  haveI : AlgebraicGeometry.IsNoetherian Z := GlobalTheory.isNoetherian_of_isProjOver hz
  have hd : ∀ x : Z, IsDomain (Z.presheaf.stalk x) := fun x => hN.isDomain_stalk x
  have hfin : (irreducibleComponents Z).Finite := NoetherianSpace.finite_irreducibleComponents
  exact ⟨irreducibleComponents Z, hfin.fintype, fun C => (C : Set Z),
    fun C => ⟨isClosed_of_mem_irreducibleComponents _ C.2, GlobalTheory.CompPart.isOpen_of_mem hd C.2⟩,
    fun C => C.2.1, GlobalTheory.CompPart.existsUnique_mem hd⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageAddInfPreimageSubGrpScheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SumAffine

theorem isIso_shear {C : Type*} [Category C] [CartesianMonoidalCategory C] (A T : C) [GrpObj A]
    (b : T ⟶ A) : IsIso (lift (fst A T * (snd A T ≫ b)) (snd A T)) := by
  refine ⟨lift (fst A T * (snd A T ≫ b⁻¹)) (snd A T), ?_, ?_⟩
  · ext
    · simp [MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]
    · simp
  · ext
    · simp [MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]
    · simp

theorem isAffineOpen_preimage_translate (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (V : A.left.Opens) (hV : IsAffineOpen V) (T : Over (Sp R)) [IsAffine T.left] (b : T ⟶ A) :
    IsAffineOpen ((fst A T * (snd A T ≫ b)).left ⁻¹ᵁ V) := by
  haveI : IsAffine (Sp R) := by unfold Sp; infer_instance
  haveI : IsAffineHom T.hom := inferInstance
  haveI : IsAffineHom (fst A T).left := by
    change IsAffineHom (pullback.fst A.hom T.hom)
    exact isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback A.hom T.hom).flip inferInstance
  haveI := isIso_shear A T b
  have h : fst A T * (snd A T ≫ b) = lift (fst A T * (snd A T ≫ b)) (snd A T) ≫ fst A T := by simp
  haveI : IsAffineHom (fst A T * (snd A T ≫ b)).left := by
    rw [h, Over.comp_left]
    haveI : IsIso (lift (fst A T * (snd A T ≫ b)) (snd A T)).left :=
      inferInstanceAs (IsIso ((Over.forget (Sp R)).map (lift (fst A T * (snd A T ≫ b)) (snd A T))))
    infer_instance
  exact hV.preimage _

theorem isAffineOpen_preimage_add_inf_preimage_sub (R : Type) [CommRing R] (A : Over (Sp R))
    [GrpObj A] [IsSeparated A.hom] (V : A.left.Opens) (hV : IsAffineOpen V) (T : Over (Sp R))
    [IsAffine T.left] (a : T ⟶ A) :
    IsAffineOpen ((fst A T * (snd A T ≫ a)).left ⁻¹ᵁ V ⊓
      (fst A T * (snd A T ≫ a)⁻¹).left ⁻¹ᵁ V) := by
  have h1 := isAffineOpen_preimage_translate R A V hV T a
  have h2 := isAffineOpen_preimage_translate R A V hV T a⁻¹
  rw [GrpObj.comp_inv] at h2
  haveI : IsSeparated (snd A T).left := by
    change IsSeparated (pullback.snd A.hom T.hom)
    infer_instance
  haveI : (A ⊗ T).left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from (snd A T).left]
    infer_instance
  exact h1.inf h2

end GlobalTheory.SumAffine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

variable {S : Scheme.{0}}

def pullTop {X Y : Scheme.{0}} (f : X ⟶ Y) : Γ(Y, ⊤)ˣ →* Γ(X, ⊤)ˣ := Units.map f.appTop.hom

def pmap {A A' : Over S} (q : A ⟶ A') (T : Over S) : A ⊗ T ⟶ A' ⊗ T := lift (fst A T ≫ q) (snd A T)

def actMap {A N : Over S} [GrpObj A] (i : N ⟶ A) (T : Over S) : A ⊗ (N ⊗ T) ⟶ A ⊗ T :=
  lift (fst A (N ⊗ T) * (snd A (N ⊗ T) ≫ fst N T ≫ i)) (snd A (N ⊗ T) ≫ snd N T)

def prMap (A N T : Over S) : A ⊗ (N ⊗ T) ⟶ A ⊗ T := lift (fst A (N ⊗ T)) (snd A (N ⊗ T) ≫ snd N T)

def IsCharacter {N T : Over S} [GrpObj N] (χ : Γ((N ⊗ T).left, ⊤)ˣ) : Prop :=
  pullTop (lift (fst N (N ⊗ T) * (snd N (N ⊗ T) ≫ fst N T)) (snd N (N ⊗ T) ≫ snd N T)).left χ =
    pullTop (lift (fst N (N ⊗ T)) (snd N (N ⊗ T) ≫ snd N T)).left χ * pullTop (snd N (N ⊗ T)).left χ

def IsPullGen {X Y : Scheme.{0}} (p : X ⟶ Y) (M : LB Y) (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ) : Prop :=
  ∀ (k l : M.ι) (W : X.Opens) (h₁ : W ≤ p ⁻¹ᵁ M.U k) (h₂ : W ≤ p ⁻¹ᵁ M.U l) (h₃ : W ≤ p ⁻¹ᵁ (M.U k ⊓ M.U l)),
    res h₁ (e k) = res h₃ (pullU p _ (M.g k l)) * res h₂ (e l)

def IsEquivGen {A A' N T : Over S} [GrpObj A] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ)
    (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ) : Prop :=
  IsPullGen (pmap q T).left M e ∧
    ∀ (k : M.ι) (W : (A ⊗ (N ⊗ T)).left.Opens)
      (h₁ : W ≤ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k))
      (h₂ : W ≤ (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k)),
      res h₁ (pullU (actMap i T).left _ (e k)) =
        res le_top (pullTop (snd A (N ⊗ T)).left χ) * res h₂ (pullU (prMap A N T).left _ (e k))

end GlobalTheory.CharKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIso
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

theorem isDual_of_iso (S : Scheme.{0}) (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B']
    (P : LB (A ⊗ B).left) (P' : LB (A ⊗ B').left) (h : IsDual A B' P') (hP : P.IsLB) (x : B ⟶ B') (hx : IsIso x)
    (hm : IsMonHom x) (e : LBIso P (ev P' (fst A B) (snd A B ≫ x))) : IsDual A B P := by
  have c : cls P hP = cls _ (pull_isLB h.isLB (lift (fst A B) (snd A B ≫ x)).left) :=
    (cls_eq_iff _ _).2 e
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ B), evc hP a t = evc h.isLB a (t ≫ x) := by
    intro Y a t
    rw [evc, c, cls_ev h.isLB, pull_evc, lift_fst, lift_snd_assoc]
  have iso : ∀ (T : Over S) (M : LB (A ⊗ T).left) (hM : M.IsLB) (w : T ⟶ B),
      LBIso M (ev P (fst A T) (snd A T ≫ w)) ↔ LBIso M (ev P' (fst A T) (snd A T ≫ w ≫ x)) := by
    intro T M hM w
    rw [← cls_eq_iff hM (pull_isLB hP _), ← cls_eq_iff hM (pull_isLB h.isLB _), cls_ev hP, cls_ev h.isLB, key,
      Category.assoc]
  refine ⟨hP, (isAdditive_iff hP).2 fun Y a a' t ↦ ?_, (triv_ev_iff hP _ _).2 ?_, fun T M hM hM' ↦ ?_⟩
  · rw [key, key, key]
    exact (isAdditive_iff h.isLB).1 h.additive Y a a' (t ≫ x)
  · rw [key, MonObj.one_comp]
    exact (triv_ev_iff h.isLB _ _).1 h.zero
  · obtain ⟨z, hz, hu⟩ := h.univ T M hM hM'
    refine ⟨z ≫ inv x, (iso T M hM _).2 ?_, fun w hw ↦ ?_⟩
    · rwa [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    · rw [← hu _ ((iso T M hM w).1 hw), Category.assoc, IsIso.hom_inv_id, Category.comp_id]

theorem transport : ∀ (S : Scheme.{0}) (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B'] (P : LB (A ⊗ B).left) (P' : LB (A ⊗ B').left), IsDual A B' P' → P.IsLB → ∀ x : B ⟶ B', IsIso x → IsMonHom x → LBIso P (ev P' (fst A B) (snd A B ≫ x)) → IsDual A B P :=
  fun S A B B' _ _ _ P P' h hP x hx hm e ↦ isDual_of_iso S A B B' P P' h hP x hx hm e

end GlobalTheory.AbDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGeneratorTopFormsOfFormallyUnramifiedStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFreeGenerator_topForms_of_formallyUnramified : ∀ {k A B : Type} [CommRing k] [CommRing A] [CommRing B] (α : k →+* A) (β : k →+* B) (ψ : A →+* B) (h : ψ.comp α = β) (n : ℕ), (letI := ψ.toAlgebra; Algebra.FormallyUnramified A B) → ∀ ω : Forms α n, IsFreeGen A ω → (∃ ω' : Forms β n, IsFreeGen B ω') → IsFreeGen B (TopForm.formMap n ψ h ω) := by
  first | exact @GlobalTheory.TopForm.isFreeGen_formMap_of_formallyUnramified | exact GlobalTheory.TopForm.isFreeGen_formMap_of_formallyUnramified | (intros; apply GlobalTheory.TopForm.isFreeGen_formMap_of_formallyUnramified <;> assumption)
end

