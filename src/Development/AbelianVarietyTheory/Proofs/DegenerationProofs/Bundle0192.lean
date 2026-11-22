import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0186
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoeffRecoveryByTorsionAverages
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0091
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0191

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcFamilyFourthConditionInvertiblePushforward
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.LN.ArcClause

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem exists_lift (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) {K : Type} [Field K] (z : Sp K ⟶ Y.X)
    (h : Set.range z ⊆ Set.range Y.j) : ∃ y : Sp K ⟶ Xo.XF c, y ≫ Y.j = z := by
  obtain ⟨g, hg⟩ : ∃ g : V →+* K, z ≫ Y.s = spMap g := ⟨(Spec.preimage (z ≫ Y.s)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨x, hx⟩ := h ⟨(default : PrimeSpectrum K), rfl⟩
  have e : Y.j ≫ Y.s = (Y.jQ ≫ pullback.snd _ _) ≫ spMap V.subtype := by
    rw [Model.j, Category.assoc, pullback.condition, Category.assoc]
  obtain ⟨q, e1⟩ : ∃ q : PrimeSpectrum c.F, PrimeSpectrum.comap g default = PrimeSpectrum.comap V.subtype q := by
    have e2 : (z ≫ Y.s) (default : PrimeSpectrum K) = (Y.j ≫ Y.s) x := congrArg Y.s hx.symm
    rw [hg, e] at e2
    exact ⟨_, e2⟩
  have hinj : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun v hv => ?_
    have h1 : v ∈ (PrimeSpectrum.comap g default).asIdeal := by
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hv]; exact zero_mem _
    rw [e1, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h1
    rw [Ideal.eq_bot_of_prime q.asIdeal] at h1
    exact Subtype.ext h1
  let g' : c.F →+* K := IsFractionRing.lift hinj
  have hg' : spMap g' ≫ spMap V.subtype = spMap g := by
    rw [← Spec.map_comp]
    congr 1
    ext v
    exact IsFractionRing.lift_algebraMap hinj v
  let z' : Sp K ⟶ pullback Y.s (spMap V.subtype) := pullback.lift z (spMap g') (hg.trans hg'.symm)
  have hz' : z' ≫ pullback.fst _ _ = z := pullback.lift_fst _ _ _
  have : IsPreimmersion (spMap V.subtype) := IsPreimmersion.of_isLocalization (nonZeroDivisors V) (S := c.F)
  have h1 : IsPreimmersion (pullback.fst Y.s (spMap V.subtype)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip this
  have := Y.jQ_open
  have hr : Set.range z' ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    refine ⟨x, (pullback.fst Y.s (spMap V.subtype)).isEmbedding.injective ?_⟩
    have e3 : (z' ≫ pullback.fst Y.s (spMap V.subtype)) (default : PrimeSpectrum K) = z (default : PrimeSpectrum K) := by
      rw [hz']
    exact hx.trans e3.symm
  refine ⟨IsOpenImmersion.lift Y.jQ z' hr, ?_⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hz']

theorem not_mem_generic {R R' : Type} [CommRing R] [CommRing R'] [IsDomain R'] (f : R →+* R') {r : R} (hr : f r ≠ 0)
    (p : PrimeSpectrum (FractionRing R')) : r ∉ ((jK R' ≫ spMap f) p).asIdeal := by
  intro h
  have h1 : algebraMap R' (FractionRing R') (f r) ∈ PrimeSpectrum.asIdeal p := h
  rw [Ideal.eq_bot_of_prime (PrimeSpectrum.asIdeal p)] at h1
  exact hr (IsFractionRing.injective R' (FractionRing R') (h1.trans (map_zero _).symm))

theorem arc_clause : DVR.TwistBaseChangeStatement → Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → Ega → USt → PelSt → HomExtSt → ArcFamSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → Amp Y → Y.N4 := by
  intro hT h1 h2 h3 h4 h5 h6 hE hU hP hX hF E _ _ _ H D l Xo c W₀ Y p hN hA O' _ _ _ b ϖ a hB
  obtain ⟨m, Z, π, t, mt, hodd, hunit, hfin, hsurj, hAF⟩ := hA
  have hm : IsUnit (m : O') := by simpa using hunit.map b
  obtain ⟨R₁, _, _, g, y₁, hg, hgf, hR, hTD, hθ, hf⟩ := hF E H D l Xo c W₀ Y O' b ϖ a hB m hodd hm
  let gam : FractionRing (PowerSeries O') →+* FractionRing R₁ :=
    IsFractionRing.lift (g := (algebraMap R₁ (FractionRing R₁)).comp g) ((IsFractionRing.injective R₁ _).comp hg)
  have hgam : ∀ r, gam (algebraMap (PowerSeries O') _ r) = algebraMap R₁ _ (g r) := fun r =>
    IsFractionRing.lift_algebraMap _ r
  obtain ⟨y, hy, hTy⟩ := GlobalTheory.T.arcGenericPoint_descends_to_powerSeries h1 h2 h3 h4 h5 h6 E H D l Xo c W₀ Y O' b a ϖ hB R₁ g y₁ gam hgam hgf hR hTD
  have hys : y ≫ Y.j ≫ Y.s = jK _ ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b := by
    have := hTy.1
    rwa [show spMap (RingHom.id (PowerSeries O')) = 𝟙 _ from Spec.map_id _, Category.id_comp] at this
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.arc_generic_point_extends_powerSeries h1 h2 E H D l Xo c W₀ Y O' b a ϖ hB m Z π t mt hfin hsurj hAF R₁ g y₁ gam hgam hgf hR
    y hy hys hθ hf
  obtain ⟨c1, c2, c3⟩ := GlobalTheory.T.arc_abelianLocus_and_moduli_of_traitData h1 h2 E H D l Xo c W₀ Y O' b a ϖ hB y χ hχ hTy
  have c4 := GlobalTheory.T.extendedArc_uAdicUniformisation_of_arcData h1 h2 h3 h4 h5 h6 hE hU hP hX E H D l Xo c W₀ Y O' b a ϖ hB hN.2.2.1 y χ hχ hTy
  have hϖ : ϖ ≠ 0 := by
    rcases hB with ⟨-, rfl⟩ | ⟨-, h, -⟩
    exacts [one_ne_zero, h.ne_zero]
  refine ⟨χ, fun χ' => ⟨fun h => h ▸ ⟨c1, c2, c3, c4⟩, fun ⟨d1, _, d3, d4⟩ => ?_⟩, fun hirr y' ev hs hr hd hC hXv => ?_⟩
  · have hpid : IsPrincipalIdealRing O' ∧ IsLocalRing O' := by
      rcases hB with ⟨h, -⟩ | ⟨h, -⟩
      · letI := h.toField
        exact ⟨inferInstance, inferInstance⟩
      · exact ⟨inferInstance, inferInstance⟩
    obtain ⟨_, _⟩ := hpid
    have : CharZero (PowerSeries O') := charZero_of_injective_ringHom (f := PowerSeries.C (R := O')) PowerSeries.C_injective
    obtain ⟨y', hy'⟩ := exists_lift (c.V W₀) Y (jK (PowerSeries O') ≫ χ') (by
      rintro _ ⟨q, rfl⟩
      refine d3 _ ?_
      have := not_mem_generic (RingHom.id (PowerSeries O')) (r := PowerSeries.C ϖ * PowerSeries.X)
        (mul_ne_zero (fun h => hϖ (PowerSeries.C_injective (h.trans (map_zero _).symm))) PowerSeries.X_ne_zero) q
      exact this)
    exact GlobalTheory.T.model_points_eq_of_same_degeneration_data h1 h2 h3 h4 h5 E H D l Xo c W₀ Y O' b a (PowerSeries O') (Ideal.span {PowerSeries.X})
      (PowerSeries.C (R := O')) PowerSeries.X ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
      (fun h => PowerSeries.X_prime.not_unit (Ideal.span_singleton_eq_top.1 h)) PowerSeries.C_injective
      χ' χ y' y hy' hχ.symm d1 c1 d4 c4
  · rcases hB with ⟨-, rfl⟩ | ⟨hdvr, -, hc⟩
    · exact absurd isUnit_one hirr.not_isUnit
    have hc' : IsAdicComplete (IsLocalRing.maximalIdeal O') O' := by
      rwa [hirr.maximalIdeal_eq]
    have hrg : Set.range (jK O' ≫ spMap ev ≫ χ) ⊆ Set.range Y.j := by
      rintro _ ⟨q, rfl⟩
      refine c3 _ ?_
      have := not_mem_generic ev (r := PowerSeries.C ϖ * PowerSeries.X)
        (by rw [map_mul, hC, hXv]; exact mul_ne_zero hϖ hϖ) q
      exact this
    have c5 := GlobalTheory.T.arcData_specialise_at_uniformiser h1 h2 hT h4.unifBaseChange h5 E H D l Xo c _ _ Y O' b ϖ a hirr hc' ev hC hXv χ c1 hrg c4
    obtain ⟨z, hz⟩ := exists_lift (c.V W₀) Y _ hrg
    obtain ⟨z', hz'⟩ := exists_lift (c.V W₀) Y _ hr
    have hid : spMap (RingHom.id O') = 𝟙 _ := Spec.map_id _
    have hev : spMap ev ≫ spMap (PowerSeries.C (R := O')) = spMap (RingHom.id O') := by
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact hC x
    refine GlobalTheory.T.model_points_eq_of_same_degeneration_data h1 h2 h3 h4 h5 E H D l Xo c W₀ Y O' b a O' (Ideal.span {ϖ}) (RingHom.id O') ϖ
      ⟨inferInstance, inferInstance, inferInstance, hc⟩
      (fun h => hirr.not_isUnit (Ideal.span_singleton_eq_top.1 h)) Function.injective_id
      _ y' z z' hz hz' ?_ ?_ c5 hd
    · rw [Category.assoc, c1, ← Category.assoc, hev]
    · rw [hid, Category.id_comp, hs]

end GlobalTheory.LN.ArcClause
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleOfThickenings
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBAlgLocal

open GlobalTheory.MorAlg GlobalTheory.LBAlg

theorem exists_veryAmpleBy_of_isPullback {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} {f' : X' ⟶ Spec (CommRingCat.of R')} {φ : X' ⟶ X} (g : R →+* R')
    (h : IsPullback φ f' f (Spec.map (CommRingCat.ofHom g))) {H : LB X} (hH : H.IsLB) {m : ℕ}
    {σ : Fin (m + 1) → LB.Sec H} (hσ : VeryAmpleBy f H σ) :
    ∃ σ' : Fin (m + 1) → LB.Sec (H.pull φ), VeryAmpleBy f' (H.pull φ) σ' := by
  obtain ⟨σ₀, w₀, hw₀, c₀⟩ := exists_isPull φ hH σ
  refine ⟨σ₀, GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R X f H m σ hH hσ _ g _ _ φ h.w ?_ _ w₀ _
    (pull_isLB hH _) hw₀ c₀⟩
  have e : pullback.lift φ f' h.w = h.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
    · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  rw [e]
  infer_instance

theorem exists_lineBundle_of_thickenings : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (B : Over (Spec (CommRingCat.of R))) (b : ∀ e, (Y e).left ⟶ B.left), IsProjBy B.hom → Flat B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∃ M : LB B.left, M.IsLB ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  intro R _ _ _ I hI hcomp Y β hβ B b hB hfl hb hc N v hN
  obtain ⟨H, hH, m, σ, hσ⟩ := id hB
  have hL : ∀ e, (H.pull (b e)).IsLB := fun e => pull_isLB hH _
  choose σ' hva using fun e =>
    exists_veryAmpleBy_of_isPullback (Ideal.Quotient.mk (I ^ (e + 1))) (hb e) hH hσ
  have hI' : I ^ (0 + 1) ≠ ⊤ := by simpa using hI
  have : Nontrivial (R ⧸ I ^ (0 + 1)) := Ideal.Quotient.nontrivial_iff.2 hI'
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (R ⧸ I ^ (0 + 1))
  let _ := Ideal.Quotient.field 𝔪
  have hπ := IsPullback.of_hasPullback (Y 0).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔪)))
  generalize pullback.snd (Y 0).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔪))) = f₀ at hπ
  generalize pullback.fst (Y 0).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔪))) = π at hπ
  obtain ⟨σ₀, hσ₀⟩ := exists_veryAmpleBy_of_isPullback (Ideal.Quotient.mk 𝔪) hπ (hL 0) (hva 0)
  obtain ⟨t₁, ht₁⟩ := GlobalTheory.AbLaw.serre_h1Zero_and_sections_polynomial.1 _ _ _ _ _ _ (pull_isLB (hL 0) π) hσ₀ ((N 0).pull π) (pull_isLB (hN 0).1 π)
  obtain ⟨t₂, ht₂⟩ := GlobalTheory.TwistGen.twist_generated _ _ _ _ _ _ (hL 0) (hva 0) (N 0) (hN 0).1
  obtain ⟨t, h₁, h₂⟩ : ∃ t, t₁ ≤ t ∧ t₂ ≤ t := ⟨max t₁ t₂, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨n, u, hu⟩ := ht₂ t h₂
  have hT : ∀ e, (tw (N e) (H.pull (b e)) t).IsLB := fun e => isLB_tw (hN e).1 (hL e) t
  have hv' : ∀ e, LBIso (tw (N e) (H.pull (b e)) t) ((tw (N (e + 1)) (H.pull (b (e + 1))) t).pull (β e)) :=
    fun e => LBIso.trans (hT e) (isLB_tw (pull_isLB (hN (e + 1)).1 _) (hL e) t) (pull_isLB (hT (e + 1)) _)
      (lbIso_tw_congr (hL e) t ⟨v e, (hN e).2⟩)
      (LBIso.chartPull (chartPullTw (Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullSame H _ _ _ (β e) fun _ => (hc e).symm) t) (Geo.Tor.chartPullPull _ _ _ rfl)
        (lbIso_self (hT (e + 1))))
  choose v' hv' using hv'
  have hflY : ∀ e, Flat (Y e).hom := fun e => MorphismProperty.of_isPullback (P := @Flat) (hb e) hfl
  have hP : ∀ e, IsProjBy (Y e).hom := fun e => ⟨_, hL e, m, σ' e, hva e⟩
  obtain ⟨w₀, hw₀⟩ : LBIso (tw ((N 0).pull π) ((H.pull (b 0)).pull π) t) ((tw (N 0) (H.pull (b 0)) t).pull π) :=
    LBIso.chartPull (chartPullTw (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl) t)
      (Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_self (hT 0))
  choose s hs0 hs using fun j => GlobalTheory.SecLifts.exists_compatible_sections_local R I hI Y β hβ hflY hP
    (fun e => tw (N e) (H.pull (b e)) t) v' (fun e => ⟨hT e, hv' e⟩) _ (Ideal.Quotient.mk 𝔪)
    Ideal.Quotient.mk_surjective _ π f₀ hπ _ w₀ (isLB_tw (pull_isLB (hN 0).1 π) (pull_isLB (hL 0) π) t) hw₀
    (ht₁ t h₁) (u j)
  obtain ⟨M, hM, hNM⟩ := GlobalTheory.GenSystem.exists_lb_of_generated_system R I hI hcomp Y β hβ B b hB hfl hb hc
    (fun e => tw (N e) (H.pull (b e)) t) v' (fun e => ⟨hT e, hv' e⟩) n (fun e j => s j e) (fun e j => hs j e)
    (by simpa only [hs0] using hu)
  have hM' : (tw M H (-t)).IsLB := isLB_tw hM hH _
  refine ⟨tw M H (-t), hM', fun e => ?_⟩
  have hO' : (tw (M.pull (b e)) (H.pull (b e)) (-t)).IsLB := isLB_tw (pull_isLB hM _) (hL e) _
  exact LBIso.trans (hN e).1 hO' (pull_isLB hM' _)
    (LBIso.trans (hN e).1 (isLB_tw (hT e) (hL e) _) hO' (lbIso_tw_tw (hN e).1 (hL e) t)
      (lbIso_tw_congr (hL e) (-t) (hNM e)))
    (LBIso.chartPull (chartPullTw (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl) (-t))
      (Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_self hM'))

end GlobalTheory.LBAlgLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPointUnitValuePrimitiveIntegralFami
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.UnitValue
open GlobalTheory.TorusExt GlobalTheory.UT.WeightValue GlobalTheory.UT.CoefBasic

theorem not_all_ne_zero {F : Type} [Field F] [IsAlgClosed F] [CharZero F] {v : AddValuation F (WithTop ℚ)} {X : Type}
    [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {n : ℕ} (hn : 2 ≤ n) (hvn : v (n : F) = 0) {a : X → F}
    (ha : NullV v a) (h0 : ∀ χ, 0 ≤ v (a χ)) {α : X} (hα : v (a α) = 0)
    (H : ∀ t : Multiplicative X →* Fˣ, (∃ k, t ^ n ^ k = 1) →
      ∃ S, SumV v (fun χ => (t (Multiplicative.ofAdd χ)).val * a χ) S ∧ v S ≠ 0) : False := by
  classical
  choose! S hS hS0 using H
  have hroot : ∀ (t : Multiplicative X →* Fˣ) (k : ℕ), t ^ n ^ k = 1 → ∀ χ, v (t χ).val = 0 ∧ v ((t χ)⁻¹).val = 0 := by
    intro t k ht χ
    have e : t χ ^ n ^ k = 1 := by rw [← MonoidHom.pow_apply, ht, MonoidHom.one_apply]
    have hN : 0 < n ^ k := pow_pos (by omega) k
    exact ⟨GlobalTheory.TorsRecov.val_eq_zero_of_pow v _ _ hN (by rw [← Units.val_pow_eq_pow_val, e, Units.val_one]),
      GlobalTheory.TorsRecov.val_eq_zero_of_pow v _ _ hN (by rw [← Units.val_pow_eq_pow_val, inv_pow, e, inv_one, Units.val_one])⟩
  have hpos : ∀ (t : Multiplicative X →* Fˣ) (k : ℕ), t ^ n ^ k = 1 → 0 < v (S t) := fun t k ht =>
    lt_of_le_of_ne (le_of_sumV (q := 0) (hS t ⟨k, ht⟩) fun χ => by
      rw [v.map_mul, (hroot t k ht _).1, zero_add]; exact h0 χ) (hS0 t ⟨k, ht⟩).symm
  obtain ⟨k, hk⟩ := GlobalTheory.coeff_recovery_by_torsion_averages F v X n hn hvn a ha S hS (fun _ => α)
    (fun _ => ⟨0, by simp⟩) (a α) (Or.inl ⟨α, fun _ => ⟨0, by simp⟩, rfl⟩) 1
  have h1 := hk k le_rfl
  have hN : 0 < n ^ k := pow_pos (by omega) k
  haveI : Finite {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1} :=
    Nat.finite_of_card_ne_zero (by
      rw [GlobalTheory.TorsRecov.card_tors F X _ hN]; exact pow_ne_zero _ hN.ne')
  letI := Fintype.ofFinite {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1}
  rw [finsum_eq_sum_of_fintype] at h1
  have h2 : 0 < v (((n : F) ^ (k * Module.finrank ℤ X))⁻¹ * ∑ t : {t : Multiplicative X →* Fˣ // t ^ n ^ k = 1},
      ((t.1 (Multiplicative.ofAdd α))⁻¹).val * S t.1) := by
    rw [v.map_mul, GlobalTheory.TorsRecov.val_inv_pow v _ _ hvn, zero_add]
    refine v.map_lt_sum WithTop.zero_ne_top fun t _ => ?_
    rw [v.map_mul, (hroot t.1 k t.2 _).2, zero_add]
    exact hpos t.1 k t.2
  have h3 := v.map_lt_add (lt_of_lt_of_le (by exact_mod_cast (zero_lt_one : (0 : ℚ) < 1)) h1) h2
  rw [sub_add_cancel, hα] at h3
  exact lt_irrefl _ h3

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} {hϖ : Irreducible ϖ}
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} {hv : ValOver ϖ F v}

theorem exists_frm_zero (k : ℕ) (g : GtPtF D.toPre F) : ∃ w : Frm D.toPre F k g.b, w.IsGen ∧ GenV hϖ hv w 0 := by
  obtain ⟨w, hw⟩ := (coef_basic V D.toPre F k g).1
  obtain ⟨r, φ₀, hφ, t₀, ht₀, x, hx, e⟩ := CoefVal.exists_genV_frm (hϖ := hϖ) (hv := hv) hw
  have hx0 : x ≠ 0 := v.ne_top_iff.1 (by rw [hx]; exact WithTop.coe_ne_top)
  obtain ⟨w', hw', e'⟩ := TorsionValue.exists_frm_scale w hw (inv_ne_zero hx0)
  refine ⟨w', hw', φ₀, hφ, t₀, ht₀, 1, v.map_one, fun z J hJ => ?_⟩
  rw [e' z J hJ, e z J hJ, ← _root_.mul_assoc, cst_eq, cst_eq, cst_eq, ← map_mul, inv_mul_cancel₀ hx0]

theorem exists_frm_cast {k : ℕ} {b b' : TF (R := V) F ⟶ D.toPre.P.A} (hb : b' = b) (w : Frm D.toPre F k b) (hw : w.IsGen)
    (h0 : GenV hϖ hv w 0) : ∃ w' : Frm D.toPre F k b', w'.IsGen ∧ GenV hϖ hv w' 0 ∧
      ∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J = val w (𝟙 _) z J := by
  subst hb
  exact ⟨w, hw, h0, fun _ _ _ => rfl⟩

end

attribute [local instance] gtGroup in

theorem exists_unit_value : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ k n : ℕ, 4 ≤ k → n.Prime → IsUnit (n : V) → ∀ (t : SecA A F k) (s : Fam D.toPre F k) (α : D.toPre.X), U.ExpandsF F k w₀ t s → IntGe D v s 0 → (∀ q : ℚ, 0 < q → ¬ VGe D F v k α (s.s α) q) → ∃ (j : ℕ) (x : TFK (R := V) F ⟶ A.A), 2 ≤ j ∧ FromGt U.toUnifPre (n ^ j) x ∧ ∀ e (c : F), IsTorsFrame A ρ (n ^ j) x e → ValAt t x e c → v c = 0 := by
  intro hL hT hVR hTW hUU V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN k n hk hn hnV t s α hts hint hprim
  by_contra hcon
  have hk1 : 1 ≤ k := by omega
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  have : CharZero (FractionRing V) := IsFractionRing.charZero V
  have : CharZero F := (algebraMap (FractionRing V) F).charZero_iff (algebraMap (FractionRing V) F).injective |>.1 this
  obtain ⟨i, g, o, ho, hgo, hg⟩ := GlobalTheory.T.exists_torsion_point_primitive_component_valuation_zero hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv k n hk hn hnV s α
    (hint α) hprim
  have hgi : n ^ i • g = 0 := ((isNsmul_iff_eq _ _ _).1 hgo).symm.trans ((isZero_iff_eq _).1 ho)
  obtain ⟨w, hw, hw0⟩ := exists_frm_zero (hϖ := hϖ) (hv := hv) k g
  have hB := D.tau_bimult
  have hgV : ∀ χ, GenV hϖ hv (g.s χ) 0 := fun χ => by
    have e := CoefVal.gtV_qk (hϖ := hϖ) (hv := hv) hVR hQ (Nat.one_le_pow i n hn.pos)
      (qkMk hB 0 g (hgi.trans (map_zero _).symm)) χ
    simpa only [qkMk_y, qkMk_g, bOf_zero_left hϖ hQ, Int.cast_zero, zero_div] using e
  have hvn : v (n : F) = 0 := by
    have e := GC.v_alg_unit hv hnV.unit
    rwa [IsUnit.unit_spec, map_natCast, map_natCast] at e
  refine not_all_ne_zero (v := v) (a := coef s g w) (α := α) hn.two_le hvn
    (((CoefVal.main hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv g).2.2.2.2.2.2 k hk1 w s hw).1)
    (fun χ => by simpa using CoefVal.le_v_coef hw (hint χ) (hgV χ) hw0) (hg w hw hw0) ?_
  rintro τ ⟨m, hm⟩
  have hj : 1 ≤ n ^ (i + m + 2) := Nat.one_le_pow _ n hn.pos
  let p : QkPt D.toPre F (n ^ (i + m + 2)) := qkMk hB 0 (g + torusPt D.toPre F (Additive.ofMul τ)) (by
    have e₁ : n ^ (i + m + 2) • g = 0 := by rw [add_assoc, pow_add, mul_comm, mul_smul, hgi, smul_zero]
    have e₂ : τ ^ n ^ (i + m + 2) = 1 := by
      rw [show i + m + 2 = m + (i + 2) by ring, pow_add, pow_mul, hm, one_pow]
    rw [smul_add, e₁, ← map_nsmul, ← ofMul_pow, e₂, ofMul_one, map_zero, map_zero, add_zero])
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V (maximalIdeal V) hA D A G hG U F _ hj
  have hx : QkToAkU U.toUnifPre F _ p (f p) := (hf p _).2 rfl
  have hex : ∃ e c, IsTorsFrame A ρ (n ^ (i + m + 2)) (f p) e ∧ ValAt t (f p) e c ∧ v c ≠ 0 := by
    by_contra h
    refine hcon ⟨i + m + 2, f p, by omega, ⟨p, rfl, hx⟩, fun e c he hc => ?_⟩
    by_contra h'
    exact h ⟨e, c, he, hc, h'⟩
  obtain ⟨e, c, he, hc, hc0⟩ := hex
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ := GlobalTheory.T.section_value_at_torsionPoint_eq_sum_terms hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN _ hj p _ hx e he
  have hv₁ : GenV hϖ hv w₁ 0 := by
    have e0 : ((Q p.y : ℚ) / ((n ^ (i + m + 2) : ℕ) : ℚ) ^ 2) = 0 := by
      rw [show p.y = 0 from rfl, QForm.Q_zero hϖ D hQ]; simp
    rwa [e0] at hv₁
  obtain ⟨w₂, hw₂, hwv⟩ := exists_pow k (line_exp k) w₁ hw₁
  have hw₂0 : GenV hϖ hv w₂ 0 := genV_pow k (line_exp k) hv₁ fun z J _ => hwv _ _ z J
  have hS : SumV v (coef s p.g w₂) c := hsum k hk1 w₂ ⟨hw₂, fun z J _ => hwv _ _ z J⟩ t s c hts hc
  have hb : p.g.b = g.b := by
    show (g + torusPt D.toPre F (Additive.ofMul τ)).b = g.b
    rw [add_b, torusPt_b, _root_.mul_one]
  obtain ⟨w', hw', hw'0, hww⟩ := exists_frm_cast hb w hw hw0
  obtain ⟨u, hu, huv, huc⟩ := ((coef_basic V D.toPre F k p.g).2.2 w₂ hw₂).2.2.1 w' hw'
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hu)
  have r0 : r = 0 := by
    have := CoefVal.sep D
    exact CoefVal.genV_unique D.toPre.P.isLB (genV_smul hw₂0 hr.symm huv) hw'0
  have hu0 : v u = 0 := by rw [← hr, r0]; rfl
  have htr := ((coef_basic V D.toPre F k g).2.2 w hw).2.2.2 τ _ p.g w'
    ((isTor_iff _ _).2 (isTorusPtF_torusPt τ)) ((isAdd_iff_eq _ _ _).2 rfl) hww s
  refine ⟨u * c, ?_, by rwa [v.map_mul, hu0, zero_add]⟩
  have := sumV_mul hS hu0
  simpa only [← huc, htr] using this

end GlobalTheory.OneBasis.UnitValue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusTorsionPointStandardAlternatingFormStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_torsionPoint_standardAlternatingForm : LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → (∀ a b, x (a + b) = x a * x b) → (∀ z : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, z ^ (S.r * S.N) = 1 → ∃ a, z = x a) → ∀ t ∈ S.perp l.yy.ker, ∃ (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), pk.y = 0 ∧ IsTor τ pk.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk (x t) ∧ ∀ (a : S.Gam) (α : u.D.toPre.X), l.yy a = QuotientAddGroup.mk α → (τ (Multiplicative.ofAdd α)).val = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ t a).val))) := by
  first | exact @GlobalTheory.ZH.PerpCharacter.exists_torus_point_eStd | exact GlobalTheory.ZH.PerpCharacter.exists_torus_point_eStd | (intros; apply GlobalTheory.ZH.PerpCharacter.exists_torus_point_eStd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralFamilyValuesTorsionTorusExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis

theorem integral_value_at_torsion : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → ∀ (x : TFK (R := V) F ⟶ A.A) e (t : SecA A F k) (s : Fam D.toPre F k) (c : F), FromGt U.toUnifPre n x → IsTorsFrame A ρ n x e → U.ExpandsF F k w₀ t s → IntGe D v s 0 → ValAt t x e c → 0 ≤ v c := by
  intro hL hT hVR hTW hUU V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN n k hn hk x e t s c hp he hts hs hc
  obtain ⟨p, hy, hx⟩ := hp
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ :=
    GlobalTheory.T.section_value_at_torsionPoint_eq_sum_terms hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN n hn p x hx e he
  have hv₁ : GenV hϖ hv w₁ 0 := by
    have e0 : ((Q p.y : ℚ) / (n : ℚ) ^ 2) = 0 := by rw [hy, QForm.Q_zero hϖ D hQ]; simp
    rwa [e0] at hv₁
  obtain ⟨w, hw, hwv⟩ := WeightValue.exists_pow k (WeightValue.line_exp k) w₁ hw₁
  have hw0 : GenV hϖ hv w 0 := WeightValue.genV_pow k (WeightValue.line_exp k) hv₁ fun z J _ => hwv _ _ z J
  have hS : SumV v (coef s p.g w) c := hsum k hk w ⟨hw, fun z J _ => hwv _ _ z J⟩ t s c hts hc
  have hg := CoefVal.gtV_qk (hϖ := hϖ) (hv := hv) hVR hQ hn p
  refine WeightValue.le_of_sumV (q := 0) hS fun β => ?_
  have h := CoefVal.le_v_coef hw (hs β) (hg β) hw0
  have b0 : QForm.bOf D.toPre Q p.y β = 0 := by
    rw [hy, QForm.bOf, zero_add, QForm.Q_zero hϖ D hQ]; ring
  simpa [b0] using h

end GlobalTheory.OneBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemThetaPointsOfClosureCosetConditionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_thetaPoints_of_closure_coset_condition : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (n j : ℕ) (ρ z : K) (v : D.La → K), n.Prime → Odd n → 2 ≤ j → Compat H ((n ^ j) ^ 2) z ρ → (∀ G, VanishC D (n ^ j) G → MvPolynomial.eval₂ (cf z ρ) v G = 0) → (∀ x, ∃ h, v (x + n ^ (j - 1) • h) ≠ 0) → ∃ o : Full D K, o.ρ = ρ ∧ (o.I.ζ ((n ^ j) ^ 2) : K) = z ∧ o.Theta (n ^ j) v := by
  first | exact @GlobalTheory.Ex.ClosurePoint.exists_full_of_closure_of_cosets | exact GlobalTheory.Ex.ClosurePoint.exists_full_of_closure_of_cosets | (intros; apply GlobalTheory.Ex.ClosurePoint.exists_full_of_closure_of_cosets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelUniformisationOfAbelianLocusDirectImage
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory

theorem isAdmissibleCompleteLocalDomainPrime_maximalIdeal (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (h₁ : IsNoetherianRing R) (h₂ : IsIntegrallyClosed R) (h₃ : IsAdicComplete (IsLocalRing.maximalIdeal R) R) :
    admitted R (IsLocalRing.maximalIdeal R) := by
  refine ⟨⟨h₁, inferInstance, h₂, h₃⟩, h₃, inferInstance, (IsLocalRing.maximalIdeal.isMaximal R).isPrime, ?_⟩
  let _ : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  infer_instance

theorem model_uniformisation_of_clauses : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Ega → USt → PelSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → Y.N3 := by
  intro hL hL2 hL3 hL4 hL5 hE hU hP E _ _ _ H D l Xo c W₀ Y p hN R _ _ _ _ hR₁ hR₂ hR₃ ξ t ht hne hsp
  obtain ⟨-, hpol, hloc⟩ := T.generic_point_mem_moduli_of_meets_abelian_locus hL hL2 E H D l Xo c W₀ Y p hN R ξ t ht hne
  have hθ : ThetaNZ t.G t.PP.L := T.fibrewise_nonvanishing_of_invertible_pushforward E H Y.X Y.t hN.2.2.1 R ξ t ht
  have hadm : admitted R (IsLocalRing.maximalIdeal R) := isAdmissibleCompleteLocalDomainPrime_maximalIdeal R hR₁ hR₂ hR₃
  let _ : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  have hpid : IsPrincipalIdealRing (R ⧸ IsLocalRing.maximalIdeal R) := inferInstance
  have hsplit : SplitOver t.G (IsLocalRing.maximalIdeal R) := hsp
  obtain ⟨P, hP'⟩ := T.exists_uniformisation_complete_local_normal_prime hL hL2 hL3 hL4 hL5 hE hU hP E H R _ hadm hpid t hpol hsplit hθ
  have hopen : IsOpen (abLocus t.G) := by
    obtain ⟨U, hU', -⟩ := hN.2.2.2.1
    rw [← hloc, ← hU']
    exact U.isOpen.preimage ξ.continuous
  refine ⟨P, ?_, hP'⟩
  rw [hloc]
  exact T.pelTrivialisation_isUnit_on_abelianLocus hL hL2 hL3 hL4 hL5 E H R _ hadm t P hP' hopen

end GlobalTheory
end

