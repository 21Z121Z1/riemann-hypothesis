import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfInvertibleLinearChange
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1595
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0109
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0094
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0104
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0051
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0093
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlacesOfCondition

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismToProjSpaceEqLinearProjectionComp
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.SpanVA

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj toProj_str toProj_preimage_chart O1 coord coord_f chart pullRatio secRatio_on
  pullRatio_toProj_on appLE_resG appLE_appLE appLE_of_eq)

theorem lin_f {R : Type} [CommRing R] {m N : ℕ} (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) (j : Fin (m + 1))
    (i : Fin (N + 1)) :
    (lin a j).f i = ∑ n, GlobalTheory.AbLaw.cst (PSpace.str R N) (chart R N i) (a j n) * GlobalTheory.ProjSpace.ratio R N i n := by
  refine (GlobalTheory.LinChange.sum_f (H := O1 R N) _ i).trans (Finset.sum_congr rfl fun n _ => ?_)
  refine (GlobalTheory.LB.smul_f (L := O1 R N) _ _ i).trans ?_
  rw [GlobalTheory.LinChange.resG_cst]
  exact congrArg (_ * ·) (coord_f R N n i)

end GlobalTheory.SpanVA

theorem GlobalTheory.SpanVA.toProj_eq_liftDom_proj : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (m N : ℕ) (s : Fin (m + 1) → LB.Sec H) (t : Fin (N + 1) → LB.Sec H) (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R), H.IsLB → ∀ (hs : ⨆ i, nonzeroLocus (s i) = ⊤) (ht : ⨆ j, nonzeroLocus (t j) = ⊤) (hst : ∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) (h : GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ GlobalTheory.SpanVA.dom a = ⊤), GlobalTheory.ProjSpace.toProj f s hs = GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h ≫ GlobalTheory.SpanVA.proj a := by
  intro R _ X f H m N s t a _ hs ht hst h
  have hg : GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h ≫ (GlobalTheory.SpanVA.dom a).ι ≫ PSpace.str R N = f := by
    rw [← Category.assoc, GlobalTheory.SpanVA.liftDom_fac, GlobalTheory.ProjSpace.toProj_str]
  have e := GlobalTheory.ProjSpace.toProj_eq_comp_of_locally (f := (GlobalTheory.SpanVA.dom a).ι ≫ PSpace.str R N)
    (GlobalTheory.SpanVA.iSup_nonzeroLocus_secPull_lin a) (GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h)
    (t := s) hs ?_
  · rw [hg] at e
    exact e
  intro z
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (ht.ge (Set.mem_univ z))
  obtain ⟨l, hl⟩ := GlobalTheory.exists_chart_of_mem_nonzeroLocus hi
  have hW : nonzeroLocus (t i) ⊓ H.U l ≤ GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N i :=
    inf_le_left.trans (GlobalTheory.ProjSpace.toProj_preimage_chart f t ht i).ge
  have hk : nonzeroLocus (t i) ⊓ H.U l ≤ GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h ⁻¹ᵁ
      ((GlobalTheory.ProjSpace.O1 R N).pull (GlobalTheory.SpanVA.dom a).ι).U (fun _ => i) := by
    refine hW.trans (le_of_eq ?_)
    erw [GlobalTheory.Cartier.pull_U]
    rw [← Scheme.Hom.comp_preimage, GlobalTheory.SpanVA.liftDom_fac]
    rfl
  refine ⟨nonzeroLocus (t i) ⊓ H.U l, ⟨hi, hl⟩, fun _ => i, hk, l, inf_le_right, ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X inf_le_right ((t i).f l),
    fun j => ?_⟩
  have key : ((GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h).appLE _ _ hk).hom
      ((GlobalTheory.Cartier.secPull (GlobalTheory.SpanVA.lin a j) (GlobalTheory.SpanVA.dom a).ι).f (fun _ => i)) =
      ((GlobalTheory.ProjSpace.toProj f t ht).appLE (GlobalTheory.ProjSpace.chart R N i) _ hW).hom ((GlobalTheory.SpanVA.lin a j).f i) := by
    show ((GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h).appLE _ _ hk).hom
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG _ _ (((GlobalTheory.SpanVA.dom a).ι.app _).hom ((GlobalTheory.SpanVA.lin a j).f i))) = _
    rw [GlobalTheory.ProjSpace.appLE_resG, Scheme.Hom.app_eq_appLE, GlobalTheory.ProjSpace.appLE_appLE]
    exact congrArg (fun ψ => ψ.hom ((GlobalTheory.SpanVA.lin a j).f i))
      (GlobalTheory.ProjSpace.appLE_of_eq (GlobalTheory.SpanVA.liftDom_fac a _ h) (GlobalTheory.ProjSpace.chart R N i) _ _ hW)
  rw [key, GlobalTheory.SpanVA.lin_f, map_sum, hst j, GlobalTheory.LinChange.sum_f, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [GlobalTheory.LB.smul_f, map_mul, map_mul, GlobalTheory.LinChange.resG_cst, GlobalTheory.LinChange.resG_cst]
  erw [GlobalTheory.LinChange.appLE_cst (PSpace.str R N) (GlobalTheory.ProjSpace.toProj f t ht) hW (a j n)]
  rw [GlobalTheory.ProjSpace.toProj_str]
  change _ = _ * (_ * GlobalTheory.ProjSpace.pullRatio (GlobalTheory.ProjSpace.toProj f t ht) _ i hW n)
  rw [GlobalTheory.ProjSpace.pullRatio_toProj_on, GlobalTheory.ProjSpace.secRatio_on (t i) (t n) l inf_le_left inf_le_right]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismToProjSpacePreimageNonzeroLocusLinearFor
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

noncomputable section

namespace GlobalTheory.SpanVA

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj O1 coord)

theorem comb_f {R : Type} [CommRing R] {X : Scheme.{0}} {H : LB X} {n : ℕ} (g : X ⟶ Sp R) (c : Fin n → R)
    (t : Fin n → H.Sec) (k : H.ι) :
    (∑ j, GlobalTheory.AbLaw.cst g ⊤ (c j) • t j).f k = ∑ j, GlobalTheory.AbLaw.cst g (H.U k) (c j) * (t j).f k := by
  rw [GlobalTheory.LinChange.sum_f]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.LB.smul_f, GlobalTheory.LinChange.resG_cst]

theorem secPull_comb_f {R : Type} [CommRing R] {X Y : Scheme.{0}} {L : LB X} {n : ℕ} (p : X ⟶ Sp R)
    (c : Fin n → R) (t : Fin n → L.Sec) (φ : Y ⟶ X) (q : (L.pull φ).ι) :
    (GlobalTheory.Cartier.secPull (∑ j, GlobalTheory.AbLaw.cst p ⊤ (c j) • t j) φ).f q =
      ∑ j, GlobalTheory.AbLaw.cst (φ ≫ p) ((L.pull φ).U q) (c j) * (GlobalTheory.Cartier.secPull (t j) φ).f q := by
  have hc : ∀ (U : X.Opens) (r : R),
      (φ.app U).hom (GlobalTheory.AbLaw.cst p U r) = GlobalTheory.AbLaw.cst (φ ≫ p) (φ ⁻¹ᵁ U) r := fun U r => by
    rw [Scheme.Hom.app_eq_appLE]
    exact GlobalTheory.LinChange.appLE_cst p φ le_rfl r
  dsimp only [GlobalTheory.Cartier.secPull]
  rw [comb_f, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, hc, GlobalTheory.LinChange.resG_cst]

end GlobalTheory.SpanVA

open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus) in

theorem GlobalTheory.SpanVA.toProj_preimage_nonzeroLocus_lin : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (m N : ℕ) (s : Fin (m + 1) → LB.Sec H) (t : Fin (N + 1) → LB.Sec H) (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R), H.IsLB → ∀ (ht : ⨆ j, nonzeroLocus (t j) = ⊤), (∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) → ∀ i, GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ nonzeroLocus (GlobalTheory.SpanVA.lin a i) = nonzeroLocus (s i) := by
  intro R _ X f H m N s t a hH ht hst i
  rw [← GlobalTheory.Cartier.nonzeroLocus_secPull]
  refine GlobalTheory.Cartier.SecMaps.nonzeroLocus_eq (pull_isLB (GlobalTheory.ProjSpace.O1_isLB R N) _) hH
    (w := GlobalTheory.ProjSpace.toProjIso f t ht) ?_
  rintro ⟨k, q⟩
  have hc := fun j => GlobalTheory.ProjSpace.secMaps_toProjIso f t ht j (k, q)
  change resG X _ ((s i).f k) = _ * resG X _ ((GlobalTheory.Cartier.secPull (GlobalTheory.SpanVA.lin a i) (GlobalTheory.ProjSpace.toProj f t ht)).f q)
  rw [GlobalTheory.SpanVA.lin]
  rw [hst i, GlobalTheory.SpanVA.comb_f, GlobalTheory.SpanVA.secPull_comb_f, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, GlobalTheory.LinChange.resG_cst, GlobalTheory.LinChange.resG_cst, hc j, GlobalTheory.ProjSpace.toProj_str]
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSectionReadingEqMovedFrameReading
section
set_option autoImplicit false

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

noncomputable section

namespace GlobalTheory.GeoLevel

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

set_option maxHeartbeats 800000 in

theorem exists_isometry_of_move_deriv {g : ℕ} {σ' : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty)
    {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ) {i : Fin F.n} {P P' : (F.Di i).La →+ (Fin g → ℂ)}
    (p : IsPeriod (F.Di i) ty P) (p' : IsPeriod (F.Di i) ty P') (hu : F.u i P ≫ ρ = F.u i P')
    (hd : ∀ j, ∃ v, IsDerivAt0 (fun z => (F.ex i P z).left) (Pi.single j 1) v ∧
      IsDerivAt0 (fun z => (F.ex i P' z).left) (Pi.single j 1) (v ≫ ν.φ)) :
    ∃ gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i).La, (∀ a b, (F.Di i).EF (gam a) (gam b) = (F.Di i).EF a b) ∧
      (∀ a, P' (gam a) = P a) ∧ ∀ z, (F.ex i P' z).left = (F.ex i P z).left ≫ ν.φ := by
  obtain ⟨gam, h, hiso, hh, hex⟩ := exists_isometry_of_sabMap F ν p p' hu
  have hcol : ∀ j, h.toLinearMap (Pi.single j 1) = Pi.single j 1 := by
    intro j
    obtain ⟨v, hv, d1⟩ := hd j
    have d0 := FibreDeriv.isDerivAt0_comp hv ν.φ
    simp only [← hex] at d0
    have d2 := (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F _ P' p') h.toLinearMap _ _).1 d0
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P' p'
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  have hid : h.toLinearMap = LinearMap.id := by
    refine (Pi.basisFun ℂ (Fin g)).ext fun j => ?_
    rw [Pi.basisFun_apply, hcol, LinearMap.id_apply]
  have hz : ∀ z, h z = z := fun z => LinearMap.congr_fun hid z
  exact ⟨gam, hiso, fun a => by rw [hh, hz], fun z => by rw [← hex, hz]⟩

set_option maxHeartbeats 1600000 in

theorem evR_normUn_move {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)}
    {M : ModelsOf F r} {k : Fin F.n} (T : ThetaData e F M k) {un : (M.X k).dom → FrPt Xo c (CAt σ)}
    (hun : IsNormUn T un) (x x' : (M.X k).dom) (A : Matrix (Fin r) (Fin r) E)
    (hA : A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E))
    (hper : ∀ a, ∃ a', (M.φ k a' : Fin r → E) = A *ᵥ (M.φ k a : Fin r → E) ∧ T.Pf x'.1 a' = T.Pf x.1 a)
    {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ) (hρ : ρ ≫ Xo.s = Xo.s)
    (hx : (un x').x = (un x).x ≫ ρ) (hu : ∀ τ i, (un x').u τ i = (un x).u τ i ≫ ν.φ)
    {w : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hw : Dom w n) {f f' : Rul Xo c} (hf : f ∈ sec Xo c w n)
    (hff : ∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') :
    evR Xo c f' (un x) = evR Xo c f (un x') := by
  obtain ⟨κ, hκ, hy⟩ := hun x
  obtain ⟨κ', hκ', hy'⟩ := hun x'
  have hb : T.co.symm x.1 ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm x.1) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact x.2
  have hb' : T.co.symm x'.1 ∈ T.co ⁻¹' (M.X k).dom := by
    show T.co (T.co.symm x'.1) ∈ (M.X k).dom
    rw [T.co.apply_symm_apply]; exact x'.2
  have p := T.isPer _ hb
  have p' := T.isPer _ hb'
  obtain ⟨gam, hiso, hP, hex⟩ := exists_isometry_of_move_deriv F ν p p'
    ((congrArg (· ≫ ρ) hy.1).symm.trans (hx.symm.trans hy'.1)) (fun j => by
      obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective j
      exact ⟨_, hy.2.1 τ i, hu τ i ▸ hy'.2.1 τ i⟩)
  have hgam : ∀ a, (M.φ k (gam a) : Fin r → E) = A *ᵥ (M.φ k a : Fin r → E) := fun a => by
    obtain ⟨a', h1, h2⟩ := hper a
    have h3 : gam a = a' := p'.2.1 (by rw [hP, T.co.apply_symm_apply, T.co.apply_symm_apply, h2])
    rw [h3, h1]
  obtain ⟨y', hmv⟩ := (GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν hρ (CAt σ) (un x)).1
  obtain ⟨t₀, ht⟩ := exists_frBor_gen (un x') y' (hmv.1.trans hx.symm)
    (funext fun τ => funext fun i => (hmv.2.1 τ i).trans (hu τ i).symm)
  have hC : (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) (M.X k).ξ0 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : Formalism.L2.PjFree.relab c σ (e j).1 (M.X k).ξ0 ≠ 0 := (map_ne_zero _).2 (M.X k).ξ0_ne
    positivity
  have d1 := (T.norm _ hb).1.ne_zero
  have d2 := (T.norm _ hb').1.ne_zero
  have k1 : κ ≠ 0 := fun h0 => mul_ne_zero hC d1 (by rw [← hκ, h0]; simp)
  have k2 : κ' ≠ 0 := fun h0 => mul_ne_zero hC d2 (by rw [← hκ', h0]; simp)
  have hth := GlobalTheory.T.thetaSection_sq_multiplier_along_isometry_move E H Dw l Xo c σ g e F r M k T _ hb _ hb' κ κ' (un x) (un x') y' gam A ρ ν _ k1 k2 hy hy'
    hiso hgam hA hP hex hmv ht
  have ht2 : Formalism.L2.PjFree.toC (t₀ : CAt σ) ^ 2 = 1 := by
    rw [hκ, hκ'] at hth
    refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero hC d2) d1) ?_
    refine hth.trans ?_
    ring
  have hred : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
  rw [hff _ _ hmv, (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 (CAt σ) hred w n f hf _ _ _ ht,
    wchar_ex_sign Dw _ ht2 (fun _ => rfl) w n hw.2, one_mul]

theorem exists_isMatch_of_models (D : Datum H) {X X' : Data E r} (φ : D.La ≃ₗ[𝓞 E] X.Λ) (φ' : D.La ≃ₗ[𝓞 E] X'.Λ)
    (hΨ : X.Ψ = X'.Ψ) (hp : X.p0 = X'.p0) (hG : X'.Gm = X.Gm) (hξ : X'.ξ0 = X.ξ0)
    (ef : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (ef' : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X'.ξ0 * herm X'.Gm (φ' a : Fin r → E) (φ' b))) :
    ∃ δ : GL (Fin r) E, IsMatch X X' δ ∧
      ∀ a, (φ' a : Fin r → E) = (δ : Matrix (Fin r) (Fin r) E) *ᵥ (φ a : Fin r → E) := by
  have hs : ∀ (Y : Data E r) (ψ : D.La ≃ₗ[𝓞 E] Y.Λ), Function.Injective (Y.Λ.subtype ∘ₗ ψ.toLinearMap) ∧
      Submodule.span E (Set.range (Y.Λ.subtype ∘ₗ ψ.toLinearMap)) = ⊤ := fun Y ψ => by
    refine ⟨Subtype.val_injective.comp ψ.injective, ?_⟩
    rw [← Y.Λ_span]
    congr 1
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (ψ a).2
    · intro hv
      exact ⟨ψ.symm ⟨v, hv⟩, congrArg Subtype.val (ψ.apply_symm_apply _)⟩
  have hc : cc (-X.ξ0) = -(-X.ξ0) := by
    have := X.ξ0_im
    unfold cc at this ⊢
    rw [map_neg, this]
  rw [hG, hξ] at ef'
  obtain ⟨δ, h1, h2⟩ := GlobalTheory.IsoExt.exists_unitary_of_isometry E H D D r (-X.ξ0) X.Gm
    (X.Λ.subtype ∘ₗ φ.toLinearMap) (X'.Λ.subtype ∘ₗ φ'.toLinearMap) (LinearEquiv.refl _ _) hc
    ⟨(hs X φ).1, (hs X φ).2, X.Gm_herm, X.Gm_det, ef⟩ ⟨(hs X' φ').1, (hs X' φ').2, X.Gm_herm, X.Gm_det, ef'⟩
    (fun _ _ => rfl)
  have h3 : ∀ a, (φ' a : Fin r → E) = (δ : Matrix (Fin r) (Fin r) E) *ᵥ (φ a : Fin r → E) := h2
  refine ⟨δ, ⟨hΨ, hp, hξ.symm, fun u v => by rw [hG, h1], fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩, h3⟩
  · have := h3 (φ.symm ⟨v, hv⟩)
    rw [φ.apply_symm_apply] at this
    exact this ▸ (φ' _).2
  · have := h3 (φ'.symm ⟨_, hv⟩)
    rw [φ'.apply_symm_apply] at this
    have e := congrArg (fun u => ((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ u) this
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at e
    rw [e]
    exact (φ _).2

end

set_option maxHeartbeats 3200000 in

theorem rdU_move_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (φD : Dw.La →ₗ[𝓞 E] (Fin r → E)), Function.Injective φD → Submodule.span E (Set.range φD) = ⊤ → (∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φD x) (φD y))) → (∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ (U.X k).ξ0).im < 0) → ∀ (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U.X k) δ), ((δ : Matrix (Fin r) (Fin r) E).det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ (δ : Matrix (Fin r) (Fin r) E).det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → MoveMatch U U k k h ρ ν → ∀ w n, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n, (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f' k x = Formalism.L2.PjFree.rdU U f k (lact δ (castFr h.psi x)) := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU k φD hinj hsp hEF hneg δ h hdet ρ ν hρ hmm w n hw f hf f' hf' hff x hx
  obtain ⟨g, e, F, ik, φ, ⟨hef, hpin⟩, hnorm⟩ := exists_pinned_of_isUnf hU
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨M, hM, hξ, hMG⟩ := GlobalTheory.ModelsExist.exists_modelsOf GlobalTheory.QNorm.hasseNormSt E H Dw l Xo _ _ _ F r
    (U.X k).ξ0 (U.X k).Gm φD (U.X k).ξ0_im hneg ⟨hinj, hsp, (U.X k).Gm_herm, (U.X k).Gm_det, hEF⟩
  have T : ∀ k, ThetaData e F M k := fun k => (GlobalTheory.T.nonempty_thetaData_flagDomainModels E H Dw l Xo c σ g e F r M hσ hM hξ k).some
  choose un hun using fun k => GlobalTheory.T.exists_normalisedFramedPoint_on_each_component hT E H Dw l Xo c σ g e F r M k (T k)
  have hok : FramesOK e F M un :=
    ⟨fun k => GlobalTheory.T.normalised_points_satisfy_single_frame hT E H Dw l Xo c σ g e F r M k (T k) (un k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_triangularFrame_weightRule hT E H Dw l Xo c σ g e F r M un k (T k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_arithmeticGroup_invariant_sign hT E H Dw l Xo c σ g e F r M un k (T k) hσ hM hξ (hun k),
      fun a n han f hf k => GlobalTheory.T.differentiableOn_readings_normalised_theta_points hB hT E H Dw l Xo c σ g e F r M un k (T k) (hun k) a n han f hf⟩
  have hU₀ := isUnf_built hB E H Dw l Xo c σ g e F r M un hσ hM hξ hok
  obtain ⟨δ₀, h₀, hφ⟩ := exists_isMatch_of_models (F.Di (ik k)) (φ k) (M.φ (ik k))
    (Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hM.type (ik k)).2 τ).symm)
    ((hU.2.1 k).1.trans (hM.type (ik k)).1.symm) (hMG _).1 (hMG _).2 (hef k) (hM.ef _)
  have hPf : ∀ (y : Frame (U.X k).Ψ r) a j, (T (ik k)).Pf (lact δ₀ (castFr h₀.psi y)) a j =
      Formalism.L2.PjFree.perFr (U.X k) y (φ k a : Fin r → E) (Formalism.L2.PjFree.relab c σ (e j).1) (e j).2 := fun y a j => by
    rw [(T (ik k)).per, hφ]
    exact GlobalTheory.T.period_coordinates_frame_rational_isometry E r _ _ δ₀ h₀ y _ _ _
  have key : ∀ y : (U.X k).dom, (un (ik k) ⟨_, h₀.mem_dom y.2⟩).x = (U.un k y).x ∧
      (un (ik k) ⟨_, h₀.mem_dom y.2⟩).u = (U.un k y).u ∧
      (IsUnitFr (U.X k) y.1 → ∃ P : (F.Di (ik k)).La →+ (Fin g → ℂ),
        IsPeriod (F.Di (ik k)) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P ∧ (U.un k y).x = F.u (ik k) P ∧
        NormPin F (ik k) P (U.un k y) ∧ NormPin F (ik k) P (un (ik k) ⟨_, h₀.mem_dom y.2⟩)) := fun y => by
    obtain ⟨P, a1, a2, a3, a4⟩ := hpin k y
    obtain ⟨P', b1, -, b3, b4, b5⟩ := hok.1 (ik k) ⟨_, h₀.mem_dom y.2⟩
    obtain rfl : P' = P := AddMonoidHom.ext fun v => funext fun j =>
      (b1 v j).trans (((T (ik k)).per _ v j).symm.trans ((hPf y.1 v j).trans (a1 v j).symm))
    refine ⟨b3.trans a3.symm, funext fun τ => funext fun i =>
      ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ _ a2).2.1 _).unique (b4 τ i) (a4 τ i), fun hy =>
      ⟨P', a2, a3, hnorm k y P' a1 hy, b5 fun τ i => (congrArg norm (h₀.dmin_eq y.1 τ i)).trans (hy _ i)⟩⟩
  obtain ⟨ν₁, hν₁, hid⟩ := (GlobalTheory.MoveCalc.frMove_calculus E H Dw l Xo c).1
  have hmm₀ : MoveMatch U (unfOf e F M un) k (ik k) h₀ (𝟙 _) ν₁ := fun y y' hy =>
    ⟨hy.1.trans ((Category.comp_id _).trans (key y).1.symm), (funext fun τ => funext fun i =>
      (hy.2.1 τ i).trans ((congrArg _ hν₁).trans (Category.comp_id _))).trans (key y).2.1.symm⟩
  obtain ⟨ε, -, hε⟩ := GlobalTheory.T.exists_const_mul_reading_of_moved_section_at_frame E H Dw l Xo c σ r U (unfOf e F M un) hσ hU hU₀ k (ik k) δ₀ h₀ (𝟙 _) ν₁
    (Category.id_comp _) hmm₀ (fun y y' t hy hmv hb => by
      obtain ⟨P, p, a1, a2, a3⟩ := (key y).2.2 hy
      exact cabs_gen_eq_one_of_normPin E H Dw l Xo c σ _ g _ F _ _ P P _ ν₁ _ _ y' t p p a1
        ((key y).1.trans a1) a2 a3 hmv hb) n
  have hself : ∀ (f₀ : Rul Xo c) (y y' : FrPt Xo c (CAt σ)), FrMove (𝟙 _) ν₁ y y' →
      evR Xo c f₀ y = evR Xo c f₀ y' := fun f₀ y y' hy => by
    rw [(GlobalTheory.exists_unique_frMove E H Dw l Xo c _ ν₁ (Category.id_comp _) (CAt σ) y).2 y y' ν₁ rfl (hid _ y) hy]
  have hx' := h.mem_dom hx
  rw [hε w hw f' hf' f' hf' (hself f') x hx, hε w hw f hf f hf (hself f) _ hx']
  refine congrArg (ε * ·) ?_
  refine (rdU_of_mem (unfOf e F M un) f' (ik k) (h₀.mem_dom hx)).trans
    (Eq.trans (congrArg Formalism.L2.PjFree.toC ?_) (rdU_of_mem (unfOf e F M un) f (ik k) (h₀.mem_dom hx')).symm)
  obtain ⟨y', hmv⟩ := (GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν hρ (CAt σ) (U.un k ⟨x, hx⟩)).1
  obtain ⟨m1, m2⟩ := hmm ⟨x, hx⟩ y' hmv
  obtain ⟨k1, k2, -⟩ := key ⟨x, hx⟩
  obtain ⟨k3, k4, -⟩ := key ⟨_, hx'⟩
  refine evR_normUn_move (T (ik k)) (hun (ik k)) ⟨_, h₀.mem_dom hx⟩ ⟨_, h₀.mem_dom hx'⟩
    ((δ₀ * δ * δ₀⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) ?_ (fun a => ?_) ν hρ ?_ (fun τ i => ?_) hw hf hff
  · have : ((δ₀ * δ * δ₀⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).det = (δ : Matrix (Fin r) (Fin r) E).det := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj]
    rw [this]
    exact hdet
  · obtain ⟨a', ha'⟩ := (φ k).surjective ⟨_, (h.lat _).1 (φ k a).2⟩
    have ha : (φ k a' : Fin r → E) = (δ : Matrix (Fin r) (Fin r) E) *ᵥ (φ k a : Fin r → E) := congrArg Subtype.val ha'
    refine ⟨a', ?_, funext fun j => ?_⟩
    · rw [hφ, hφ, ha, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Matrix.mul_assoc, Units.inv_mul,
        Matrix.mul_one, Units.val_mul]
    · refine (hPf _ a' j).trans (Eq.trans ?_ (hPf _ a j).symm)
      rw [ha]
      exact GlobalTheory.T.period_coordinates_frame_rational_isometry E r _ _ δ h x _ _ _
  · exact k3.trans (m1.symm.trans (hmv.1.trans (congrArg (· ≫ ρ) k1.symm)))
  · exact (congrFun (congrFun (k4.trans m2.symm) τ) i).trans
      ((hmv.2.1 τ i).trans (congrArg (· ≫ ν.φ) (congrFun (congrFun k2.symm τ) i)))

end GlobalTheory.GeoLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyCartierOfLocallyPrincipal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

namespace GlobalTheory.CompHS

theorem nonempty_cartier_of_locally_principal : ∀ (Y : Scheme.{0}) (I : Y.IdealSheafData),
    (∀ y : Y, ∃ (W : Y.affineOpens) (a : Γ(Y, W.1)), y ∈ W.1 ∧ a ∈ nonZeroDivisors Γ(Y, W.1) ∧
      I.ideal W = Ideal.span {a}) → Nonempty (Cartier I) := by
  intro Y I h
  obtain ⟨D, hD⟩ := GlobalTheory.EffCartierData.exists_idealSheaf_eq (I := I) h
  refine ⟨{ P := D.lb, isLB := D.isLB_lb, t := D.canonical, reg := fun i y hi => ?_, cut := ?_ }⟩
  · exact GlobalTheory.Cartier.isRegularFn_iff_germ.1 (D.regular i) y hi
  · refine ideal_ext_stalk fun y => ?_
    obtain ⟨i, hi⟩ := D.exists_mem y
    rw [stalkId_cutIdeal D.isLB_lb _ i y hi, ← hD, D.stalkId_idealSheaf i y hi, Set.range_const]
    rfl

end GlobalTheory.CompHS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicThetaSumSchroedingerRationalPairInvariStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_adelicThetaSum_schroedinger_rationalPair_invariant : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] (Φ : (κ → AF F) → ℂ),
    ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w : (κ → AF F) × (κ → AF F),
      ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (γ + w) Φ)‖ = ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)‖ := by
  first | exact @GlobalTheory.ThetaRatInv.norm_thetaSum_schr_ratPair_add | exact GlobalTheory.ThetaRatInv.norm_thetaSum_schr_ratPair_add | (intros; apply GlobalTheory.ThetaRatInv.norm_thetaSum_schr_ratPair_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormChartLineBundleBaseChangeFieldExtensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ProjField
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normChartLineBundle_baseChange_field_extension : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ N₀ : LB A.left, N₀.IsLB → NormChart A N₀ → NormChart ((Over.pullback (spMap (algebraMap K Ω))).obj A) (N₀.pull (pullback.fst A.hom (spMap (algebraMap K Ω)))) := by
  first | exact @GlobalTheory.ProjField.normChart_baseChange | exact GlobalTheory.ProjField.normChart_baseChange | (intros; apply GlobalTheory.ProjField.normChart_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedImageHeightUniqueFrame
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

namespace GlobalTheory.ImageHeightFrame

theorem isImageHeight_unique : Quoted → ∀ (F : Type) [Field F] [NumberField F] (V Ω : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] [Field Ω] [Algebra F Ω] (Nm : (F →+* ℂ) → V → ℝ) (W : Submodule (𝓞 F) V) (ev : V →ₗ[F] Ω) (D : ℕ) (h h' : ℝ), IsTotallyComplex F → CompHt.IsImageHeight Nm W ev D h → CompHt.IsImageHeight Nm W ev D h' → h = h' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh hh' => ImageHeightUnique.isImageHeight_unique hh hh'

end GlobalTheory.ImageHeightFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfValuesMulOfValuesStatement
section
open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ofValues_mul_ofValues' : ∀ {n : ℕ} (α β : V n → V n → ℂ), ofValues α * ofValues β = ofValuesTwo (wedge α β) := by
  first | exact @GlobalTheory.SecForm.ofValues_mul_ofValues | exact GlobalTheory.SecForm.ofValues_mul_ofValues | (intros; apply GlobalTheory.SecForm.ofValues_mul_ofValues <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointLinearFunctionalCmStatement
section
open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit Classical
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_linear_functional_cm : ∀ {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (φ : E →+* C), ∃ (m : ℕ) (u : Fin m → P.T) (ℓ : Fin m → (P.T →ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] 𝓞 E)) (e : ℤ_[p] ⊗[ℤ] 𝓞 E), (∀ j a t, ℓ j (P.actT a t) = (1 ⊗ₜ a) * ℓ j t) ∧ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (embO P.integers φ) e = 1 ∧ ∀ t, tensorAction P.actT e t = ∑ j, tensorAction P.actT (ℓ j t) (u j) := by
  first | exact @GlobalTheory.TateLocFree.exists_place_decomp | exact GlobalTheory.TateLocFree.exists_place_decomp | (intros; apply GlobalTheory.TateLocFree.exists_place_decomp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointTraceDualStatement
section
open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit Classical
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_trace_dual : ∀ {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (φ : E →+* C) (d : C), d ≠ 0 → (∀ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E) (s : C), (∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then s else 0) → v s ≤ v d) → ∀ (m : ℕ) (u : Fin m → P.T) (ℓ : Fin m → (P.T →ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] 𝓞 E)) (e : ℤ_[p] ⊗[ℤ] 𝓞 E), (∀ j a t, ℓ j (P.actT a t) = (1 ⊗ₜ a) * ℓ j t) → ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (embO P.integers φ) e = 1 → (∀ t, tensorAction P.actT e t = ∑ j, tensorAction P.actT (ℓ j t) (u j)) → ∀ w : P.V, w ∈ P.eigV (embO P.integers φ) → d • w ∈ P.latT → w ∈ P.latTQuot (σ := fun ψ : E →+* C => embO P.integers ψ) (isSplitting_embO P.integers) φ := by
  first | exact @GlobalTheory.EigGlue.mem_latTQuot_of_smul_mem_latT | exact GlobalTheory.EigGlue.mem_latTQuot_of_smul_mem_latT | (intros; apply GlobalTheory.EigGlue.mem_latTQuot_of_smul_mem_latT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransferEigensystemPartsThreeLevelsOfMultEqStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transfer_eigensystem_parts_three_levels_of_mult_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ s : ℕ, A.fam.Ok s → GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → GoodStable A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.TrCopy.TRLev R F SF := by
  first | exact @GlobalTheory.TrLevMult.trLev_of_multEq | exact GlobalTheory.TrLevMult.trLev_of_multEq | (intros; apply GlobalTheory.TrLevMult.trLev_of_multEq <;> assumption)
end

