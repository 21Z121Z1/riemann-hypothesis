import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3295
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0020
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3306
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelRuleSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3302
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchSecOfUnf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusFlagUnitWeightBundlesNef
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3308

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringMeasureReductionBound
section
section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
namespace GlobalTheory.CovTop.MeasRd
theorem covering_measure_reduction : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Meas := by
  intro h
  have h2 := _root_.GlobalTheory.T.normalized_covolume_eq_one h
  refine Closed.imp (Closed.and (GlobalTheory.T.log_ratio_upper_bound h2) (_root_.GlobalTheory.T.covolume_lower_bound_of_cover h)) ?_
  intro _ Fm _ _ hh
  obtain ⟨⟨K1, hK1, a, ha⟩, ⟨K2, hK2, b, hb⟩⟩ := hh
  refine ⟨(K1 + K2) / 2, by positivity, max a b, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨hr, hu⟩ := ha x hx ((le_max_left _ _).trans hle) ι p hp i
  have hl := hb x hx ((le_max_right _ _).trans hle) ι p hp i
  exact measAt_of p i (GlobalTheory.T.exact_at_of_one_measure p hp.1 (h2 _) i) hr hK1 hK2 hu hl
end GlobalTheory.CovTop.MeasRd
end
end

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_measure_reduction_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Meas := by
  first | exact @_root_.GlobalTheory.CovTop.MeasRd.covering_measure_reduction | exact _root_.GlobalTheory.CovTop.MeasRd.covering_measure_reduction | (intros; apply _root_.GlobalTheory.CovTop.MeasRd.covering_measure_reduction <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.DefectBoundOfConnected
section
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CovTop.DefCore
theorem defect_bound_of_connected : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ M : ℝ, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A : ℝ), RowsT p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm) - C₀ * unitE p ≤ muCore p i := by
  intro _hP
  refine ⟨0, 0, le_rfl, ?_⟩
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A hp hi hg hw hh hF
  obtain ⟨hdef, hfin, hne, hdict⟩ := GlobalTheory.T.deformation_case_finite_components p i PP A 0 hp hi hg hw hh hF
  obtain ⟨G, _, _, lev, χ, hact, hfree, hsl⟩ := GlobalTheory.T.exists_finite_group_level p i PP A 0 hp hi hg hw hh hF
  have hflat := GlobalTheory.T.flat_exists_at_last_index p i PP A 0 hp hi hg hw hh hF
  have h := (GlobalTheory.T.eigenlattice_slope_lower_bound_definite_case D _ _ _ _ _ _ (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) G lev χ
    (wtA (p.κ i)) (p.κ i).n _ hdef hfin hne hdict hact hfree hw.dom hg.2.2.2 hflat).2
  unfold Gk at hsl
  linarith
theorem twice_defect_bound_le_mu : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Lifts fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → GramAt p i → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm) - C * unitE p ≤ muCore p i := by
  intro hP
  obtain ⟨M1, C1, hC1, h1⟩ := _root_.GlobalTheory.CovTop.DefCore.defect_bound_of_connected hP
  obtain ⟨M2, C2, hC2, h2⟩ := _root_.GlobalTheory.T.two_defBound_sub_unitError_le_muCore hP
  have hW : WtN := GlobalTheory.CovTop.WtShape.wtN
  have hH1 : HostN M1 := GlobalTheory.CovTop.Sizes.hostN M1
  have hH2 : HostN M2 := GlobalTheory.CovTop.Sizes.hostN M2
  unfold Lifts WtN HostN at *
  refine Closed.imp ((hW.and hH1).and hH2) ?_
  rintro eps Fm CH - ⟨⟨⟨Cw, -, xw, hw⟩, ⟨A1, -, x1, ha1⟩⟩, ⟨A2, -, x2, ha2⟩⟩
  refine ⟨max C1 C2, le_max_of_le_left hC1, max (max xw x1) x2, fun x hx hle ι p hp i hi hg => ?_⟩
  have hle1 : xw ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have hle2 : x1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle
  have hle3 : x2 ≤ x := le_trans (le_max_right _ _) hle
  have w := hw x hx hle1 ι p hp i
  have a1 := ha1 x hx hle2 ι p hp i
  have a2 := ha2 x hx hle3 ι p hp i
  have hu := unitE_nonneg p i _ _ _ w a1
  by_cases hF : FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c
  · have := h1 p i _ _ hp hi hg w a1 hF
    nlinarith [le_max_left C1 C2]
  · have := h2 p i _ _ hp hi hg w a2 hF
    nlinarith [le_max_right C1 C2]
end GlobalTheory.CovTop.DefCore
end
end

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.defect_bound_le_half_mu : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Lifts fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → GramAt p i → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm) - C * unitE p ≤ muCore p i := by
  first | exact @_root_.GlobalTheory.CovTop.DefCore.twice_defect_bound_le_mu | exact _root_.GlobalTheory.CovTop.DefCore.twice_defect_bound_le_mu | (intros; apply _root_.GlobalTheory.CovTop.DefCore.twice_defect_bound_le_mu <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.DetLineExistsHorizontalSection
section
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.DetLine
open ReciprocityTheory.ChartRestriction.G.PullbackSections.AnFrameC ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows GlobalTheory.DetLine.GoodTransport
namespace GlobalTheory.DetLine.PeriodFlat
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}
section Linear
variable {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} {Hm : Matrix (Fin g) (Fin g) ℂ}
end Linear
section Fibre
variable {Xo : Moduli D l} {σ : KA l →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n)
variable {Fu i} {P : (Fu.Di i).La →+ (Fin g₀ → ℂ)}
end Fibre
section Model
variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {U : (Xo.XF c).Opens} {τ : E →+* ℂ}
end Model
end GlobalTheory.DetLine.PeriodFlat
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit in
theorem GlobalTheory.DetLine.PeriodFlat.detLine_exists_horizontal_section : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.CanonicalExtensionRankOne → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H), ∃ (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1), (V : Set (Xo.XF c)) = Z ∧ sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsHorizontal sig := by
  intro hp _ E _ _ _ H Dw l Xo c r U x hL Z τ
  obtain ⟨Y, -⟩ := hp.p1 E H Dw hL.pos l Xo c
  obtain ⟨V, hV, hirr⟩ := GlobalTheory.GeomIrrComp.exists_open_irreducibleSpace_baseChange E H Dw l Xo c hL.geo Z
  have hc : IsClosed (V : Set (Xo.XF c)) := hV ▸ isClosed_of_mem_irreducibleComponents _ Z.2
  have hG : GeometricallyConnected (V.ι ≫ toF Xo c) :=
    ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.2 fun K _ _ => by
      have := hirr K (algebraMap c.F K)
      exact (inferInstance : ConnectedSpace ↑(pullback (V.ι ≫ toF Xo c) (spMap (algebraMap c.F K))))⟩
  obtain ⟨-, σ, -, -, hf, -, hY⟩ := detLineTrivial_of_toroidal hp.p1 E H Dw l Xo c V hc hG τ.1 τ.2
  obtain ⟨σb, hs, hz, hres, -⟩ := hY _ _ Y (GlobalTheory.FlatRow.isNormal_genFibre Y)
  refine ⟨Y, V, fun R _ _ a => σb R a.x a.v a.w, hV, fun R R' _ _ j j' a a' f M N h => ?_,
    fun R _ j a => hz R j _ _ _ (PeriodFlat.frY_framed a), PeriodFlat.isHorizontal_of_isFlatAt hc hres hz hf⟩
  rw [mul_comm, mul_comm _ N.det]
  exact (sec_chg hs (PeriodFlat.frY_framed a) (PeriodFlat.frY_framed a') ⟨h.2.1, h.2.2⟩).symm
end
end

section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detLine_period_flat : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.CanonicalExtensionRankOne → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H), ∃ (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1), (V : Set (Xo.XF c)) = Z ∧ sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsHorizontal sig := by
  first | exact @_root_.GlobalTheory.DetLine.PeriodFlat.detLine_exists_horizontal_section | exact _root_.GlobalTheory.DetLine.PeriodFlat.detLine_exists_horizontal_section | (intros; apply _root_.GlobalTheory.DetLine.PeriodFlat.detLine_exists_horizontal_section <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsArchimedeanSectionWithDenominator
section
section
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
open GlobalTheory.FlatDenom
noncomputable section
namespace GlobalTheory.FlatDenom
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
open GlobalTheory.DetLine GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal in
theorem exists_horizontal_section_flat_model (hp : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hpos : 1 ≤ Dw.p + Dw.q) (hgeo : FnAlgClosed Xo c) (Z : Comp Xo c)
    (τ : Psi H) : ∃ (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1),
      (V : Set (Xo.XF c)) = Z ∧ sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig ∧
        GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.IsHorizontal sig := by
  obtain ⟨Y, -⟩ := hp.p1 E H Dw hpos l Xo c
  obtain ⟨V, hV, hirr⟩ := GlobalTheory.GeomIrrComp.exists_open_irreducibleSpace_baseChange E H Dw l Xo c hgeo Z
  have hc : IsClosed (V : Set (Xo.XF c)) := hV ▸ isClosed_of_mem_irreducibleComponents _ Z.2
  have hG : GeometricallyConnected (V.ι ≫ toF Xo c) :=
    ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.2 fun K _ _ => by
      have := hirr K (algebraMap c.F K)
      exact (inferInstance : ConnectedSpace ↑(pullback (V.ι ≫ toF Xo c) (spMap (algebraMap c.F K))))⟩
  obtain ⟨-, σ, -, -, hf, -, hY⟩ := detLineTrivial_of_toroidal hp.p1 E H Dw l Xo c V hc hG τ.1 τ.2
  obtain ⟨σb, hs, hz, hres, -⟩ := hY _ _ Y (GlobalTheory.FlatRow.isNormal_genFibre Y)
  refine ⟨Y, V, fun R _ _ a => σb R a.x a.v a.w, hV, fun R R' _ _ j j' a a' f M N h => ?_,
    fun R _ j a => hz R j _ _ _ (PeriodFlat.frY_framed a), PeriodFlat.isHorizontal_of_isFlatAt hc hres hz hf⟩
  rw [mul_comm, mul_comm _ N.det]
  exact (sec_chg hs (PeriodFlat.frY_framed a) (PeriodFlat.frY_framed a') ⟨h.2.1, h.2.2⟩).symm
variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}
theorem exists_archimedean_section_of_unramified (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1)
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hgeo : FnAlgClosed Xo c) (x : ℝ) (Z : Comp Xo c) (τ : Psi H) :
    ∃ (s : ArchSec U x Z (flatWt Dw τ)) (m : ℕ), 0 < m ∧
      ∀ la, ∀ v ∈ valOn Z la, 0 ≤ v ((m : c.F) • s.sig) ∧ 0 ≤ v ((m : c.F) • s.inv) := by
  obtain ⟨Y, V, sig, hV, hs, hnv, hh⟩ := _root_.GlobalTheory.FlatDenom.exists_horizontal_section_flat_model hP hpq hgeo Z τ
  obtain ⟨f, g, hf, hg, hfi, hgi, hfg, hR⟩ := GlobalTheory.BdryUnit.ReadDet.exists_reads E H Dw l Xo c Y Z V τ sig hV hs hnv
  choose b hb hb' using fun σ => const_length (U _) x (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) hgeo hV hnv hh hR
  exact ⟨⟨f, g, hf, hg, hfi, hgi, hfg, b, hb, hb'⟩, archSec_denom hpq hA _ fun T io y₀ h0 hZ =>
    _root_.GlobalTheory.BdryUnitVal.boundary_unit_at_integral_points hP E H Dw l Xo c Y Z V τ sig f hV hs hnv hR T io y₀ h0 hZ⟩
end GlobalTheory.FlatDenom
open Formalism.BasicNotions GlobalTheory.CovTop in
theorem GlobalTheory.FlatDenom.exists_archimedean_section_with_denominator : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H), ∃ (s : GlobalTheory.FlatCore.ArchSec Y.U (xiR D) Z (GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ)) (m : ℕ), 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s.sig) ∧ 0 ≤ v ((m : Y.d.c₂.F) • s.inv) := by
  intro hP D T j Y e o hG _ Z τ
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  have h1 : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q := (hG.unf Y.d.c₂.F.val.toRingHom rfl).1
  exact _root_.GlobalTheory.FlatDenom.exists_archimedean_section_of_unramified hP (by omega) hG.lev.2 hG.unf hG.geo _ Z τ
namespace GlobalTheory.FlatDenom
section Powers
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)
  (Z : Comp Xo c)
variable {U x Z} {la la' : GlobalTheory.AllWt.Weight Dw}
end Powers
end GlobalTheory.FlatDenom
open Formalism.BasicNotions GlobalTheory.CovTop in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.FlatDenom.unit_pow_clears_denominator_flat_model : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (n : ℤ) (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H) (s i : Rul Y.d.Xo₂ Y.d.c₂), (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C)) → ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • i) := by
  intro hP D T j Y e o hY hE n Z τ s i ⟨hs, hi, hIs, hIi, hsi, hb⟩
  have h₁ : HasBddSec Y.U (xiR D) Z (flatWt (T.Q.Dw j) τ) := _root_.GlobalTheory.FlatDenom.exists_archimedean_section_with_denominator hP D T j Y e o hY hE Z τ
  obtain ⟨s₀, m₀, hm₀, h₀⟩ := h₁.zsmul n
  generalize n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ = la at *
  have hw : wtOf (T.Q.Dw j) la 0 + wtOf (T.Q.Dw j) (-la) 0 = 0 := by
    rw [← GlobalTheory.FlatLine.wtOf_add', add_neg_cancel, GlobalTheory.AllWt.wtOf_zero]
  have hg : s * s₀.inv ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 := by
    have h := GlobalTheory.AllWt.mul_mem_secZ hs s₀.inv_mem
    have h0 : Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) la 0) + -GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0 = 0 :=
      add_neg_cancel _
    rwa [h0] at h
  have hh : i * s₀.sig ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 := by
    have h := GlobalTheory.AllWt.mul_mem_secZ hi s₀.sig_mem
    have h0 : -Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) la 0) + GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0 = 0 :=
      neg_add_cancel _
    rwa [h0] at h
  have hIg : GlobalTheory.FlatLine.idem Z * (s * s₀.inv) = s * s₀.inv := by rw [← mul_assoc, hIs]
  have hIh : GlobalTheory.FlatLine.idem Z * (i * s₀.sig) = i * s₀.sig := by rw [← mul_assoc, hIi]
  have hgh : s * s₀.inv * (i * s₀.sig) = GlobalTheory.FlatLine.idem Z := by
    calc s * s₀.inv * (i * s₀.sig) = (s * i) * (s₀.sig * s₀.inv) := by ring
      _ = _ := by rw [hsi, s₀.mul_inv, GlobalTheory.FlatLine.idem_mul_idem]
  have hbd : ∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z,
      GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 (s * s₀.inv) z ≤ C ∧
        GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 (i * s₀.sig) z ≤ C := by
    intro σ hσ
    obtain ⟨C, hC⟩ := hb σ hσ
    have hgo : Formalism.L2.Pj.goodOf Y.d.c₂ σ = σ := if_pos hσ
    have hN : ∀ σ'' (_ : Formalism.L2.Pj.goodOf Y.d.c₂ σ = σ''), ∀ z ∈ framesOn (Y.U σ'') Z,
        GlobalTheory.AllWt.homN (Y.U σ'') (xiR D) (wtOf (T.Q.Dw j) la 0) s₀.sig z = s₀.cInf σ ∧
        GlobalTheory.AllWt.homN (Y.U σ'') (xiR D) (wtOf (T.Q.Dw j) (-la) 0) s₀.inv z = (s₀.cInf σ)⁻¹ := by
      rintro _ rfl z hz
      exact ⟨homN_sig s₀ hz, homN_inv s₀ hz⟩
    have hpos := s₀.cInf_pos σ
    refine ⟨max (C * (s₀.cInf σ)⁻¹) (C * s₀.cInf σ), fun z hz => ?_⟩
    have hd : z.2 ∈ ((Y.U σ).X z.1).dom := hz.1
    obtain ⟨h1, h2⟩ := hN σ hgo z hz
    obtain ⟨c1, c2⟩ := hC z hz
    have hev : Even (-(wtOf (T.Q.Dw j) la 0)).2 := by
      simpa using (GlobalTheory.AllWt.even_wtOf (Dw := T.Q.Dw j) la 0).neg
    have e1 := GlobalTheory.AllWt.homN_mul (Y.U σ) (xiR D) (GlobalTheory.AllWt.even_wtOf la 0) (GlobalTheory.AllWt.even_wtOf (-la) 0)
      s s₀.inv z hd
    rw [hw, h2] at e1
    have e2 := GlobalTheory.AllWt.homN_mul (Y.U σ) (xiR D) hev (GlobalTheory.AllWt.even_wtOf la 0) i s₀.sig z hd
    rw [neg_add_cancel, h1] at e2
    constructor
    · rw [e1]; exact (mul_le_mul_of_nonneg_right c1 (inv_pos.2 hpos).le).trans (le_max_left _ _)
    · rw [e2]; exact (mul_le_mul_of_nonneg_right c2 hpos.le).trans (le_max_right _ _)
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.CovTop.koecher_principle_unit_constant hP D T j Y e o hY hE Z _ _ hg hh hIg hIh hgh hbd
  have hsa : s = a • s₀.sig := by
    calc s = s * GlobalTheory.FlatLine.idem Z := by rw [mul_comm, hIs]
      _ = (s * s₀.inv) * s₀.sig := by rw [← s₀.mul_inv]; ring
      _ = a • s₀.sig := by rw [ha, smul_mul_assoc, s₀.idem_sig]
  by_cases ha0 : a = 0
  · refine ⟨1, one_pos, fun w v hv => ?_⟩
    exfalso
    have h1 := GlobalTheory.FlatLine.val_idem hv
    rw [← hsi, hsa, ha0, zero_smul, zero_mul, (GlobalTheory.FlatLine.isVal_valOn hv).zero] at h1
    exact EReal.top_ne_zero h1
  have hia : i = a⁻¹ • s₀.inv := by
    calc i = i * GlobalTheory.FlatLine.idem Z := by rw [mul_comm, hIi]
      _ = i * (a • s₀.sig * a⁻¹ • s₀.inv) := by rw [GlobalTheory.FlatLine.smul_mul_inv_smul ha0, s₀.mul_inv]
      _ = (s * i) * a⁻¹ • s₀.inv := by rw [← hsa]; ring
      _ = a⁻¹ • s₀.inv := by rw [hsi, mul_smul_comm, s₀.idem_inv]
  obtain ⟨n₁, hn₁, k₁⟩ := exists_nat_vAdd ha0
  obtain ⟨n₂, hn₂, k₂⟩ := exists_nat_vAdd (inv_ne_zero ha0)
  have hnat : ∀ (k : ℕ), 0 < k → ∀ w, 0 ≤ vAdd w (k : Y.d.c₂.F) := fun k hk w => by
    have := Formalism.L2.Pj.vAdd_int_nonneg w (a := (k : 𝓞 Y.d.c₂.F)) (by
      have : (k : Y.d.c₂.F) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
      simpa using this)
    simpa using this
  have key : ∀ (b : Y.d.c₂.F) (k k' : ℕ) (f : Rul Y.d.Xo₂ Y.d.c₂), b ≠ 0 → 0 < k → 0 < k' → ∀ w, ∀ v ∈ valOn Z w,
      0 ≤ vAdd w ((k : Y.d.c₂.F) * b) → 0 ≤ v ((m₀ : Y.d.c₂.F) • f) →
      0 ≤ v (((k' * k * m₀ : ℕ) : Y.d.c₂.F) • b • f) := fun b k k' f hb hk hk' w v hv h1 h2 => by
    have hV := GlobalTheory.FlatLine.isVal_valOn hv
    have e1 : ((k' * k * m₀ : ℕ) : Y.d.c₂.F) • b • f = (k' : Y.d.c₂.F) • ((k : Y.d.c₂.F) * b) • (m₀ : Y.d.c₂.F) • f := by
      simp only [smul_smul]
      congr 1
      push_cast
      ring
    rw [e1, hV.smul _ _ (Nat.cast_ne_zero.2 hk'.ne'), hV.smul _ _ (mul_ne_zero (Nat.cast_ne_zero.2 hk.ne') hb)]
    exact add_nonneg (EReal.coe_nonneg.2 (by exact_mod_cast hnat k' hk' w))
      (add_nonneg (EReal.coe_nonneg.2 (by exact_mod_cast h1)) h2)
  refine ⟨n₂ * n₁ * m₀, Nat.mul_pos (Nat.mul_pos hn₂ hn₁) hm₀, fun w v hv => ⟨?_, ?_⟩⟩
  · rw [hsa]
    exact key a n₁ n₂ _ ha0 hn₁ hn₂ w v hv (k₁ w) (h₀ w v hv).1
  · rw [hia, mul_comm n₂]
    exact key a⁻¹ n₂ n₁ _ (inv_ne_zero ha0) hn₂ hn₁ w v hv (k₂ w) (h₀ w v hv).2
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IsNefHodgeBundleUnitWeight
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NefUnit
open GlobalTheory.FlagMod (FlagCover Frames ev ev_res ev_spMap ext_ev tau tau_le spMap_ev ev_tau le_preimage_comp le_preimage_mono
  vec tanPull tanPull_actR tanPull_vec tan_ext_left ev_pull_g)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
open GlobalTheory.Toroidal (gen genι genStr)
open GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm (epsAt IsEigBasisAt IsCombAt IsFrame chi compactOf toF)
open GlobalTheory.DetLine (FrY RuleY SecY NzY)
section Glue
variable {W : Scheme.{0}}
end Glue
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y)
theorem isNef_hodgeBundle_unitWeight : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ τ : Psi H, letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.unitWt τ 1)) ∧ IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.unitWt τ (-1))) := by
  intro hP _ E _ _ _ H Dw l Xo c TF Z hF τ
  letI := algebraΓOfHom (str₀ TF.X Z)
  have hp := (VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF).2.1
  exact ⟨(isGenerated_unitWt hP.p1 TF Z hF τ 1).isNef_of_isProjOver hp,
    (isGenerated_unitWt hP.p1 TF Z hF τ (-1)).isNef_of_isProjOver hp⟩
end GlobalTheory.NefUnit
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeBundle_unitWeight_nef : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ τ : Psi H, letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.unitWt τ 1)) ∧ IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.unitWt τ (-1))) := by
  first | exact @_root_.GlobalTheory.NefUnit.isNef_hodgeBundle_unitWeight | exact _root_.GlobalTheory.NefUnit.isNef_hodgeBundle_unitWeight | (intros; apply _root_.GlobalTheory.NefUnit.isNef_hodgeBundle_unitWeight <;> assumption)
end
end

