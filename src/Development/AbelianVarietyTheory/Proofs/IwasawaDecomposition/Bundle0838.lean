import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0837
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnChoiceCloudBoundLeExplicit
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0288
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0010
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0337
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0493
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0836
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0746
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0797
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1015
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0991
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0796
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0852
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0739
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0824
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0738
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0737
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0811
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0721
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0832

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientDutyInputsAllStatesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_duty_inputs_all_states : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → GlobalTheory.NRows.HypothesesX → AllSt fun _ _ _ _ _ _ x => ∀ l : LC hL x, GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → Nonempty (GlobalTheory.NRows.Inputs hL D') := by
  first | exact @GlobalTheory.PtInputsX.inputs_at_third | exact GlobalTheory.PtInputsX.inputs_at_third | (intros; apply GlobalTheory.PtInputsX.inputs_at_third <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnChoiceCloudBoundLeExplicitParametersStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnChoice_cloudBound_le_cG : StepW Pinned fun K B f T w => ∀ Z : w.Lt, ∃ c : ℕ, (∀ u, Formalism.L2.G.CloudBound (w.D Z) u c) ∧ ∀ L : SizeData₂ (w.D Z), L.sc = K.s → Val K.C K.cD K.ch L → (c : ℝ) ≤ G.cG L := by
  first | exact @GlobalTheory.Mem.Top.Bl.cloudBound_step | exact GlobalTheory.Mem.Top.Bl.cloudBound_step | (intros; apply GlobalTheory.Mem.Top.Bl.cloudBound_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DepthZeroEigenSpanAdmissibleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_zero_eigen_span_admissible : (HtCard → PrN → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c => PairedCharacterCondition.tieChi (D := w.D Z) ∧ ∃ Q : PairedCharacterCondition.Pend (w.D Z), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) := by
  first | exact @GlobalTheory.HeightCounting.Up.PendLayer.main | exact GlobalTheory.HeightCounting.Up.PendLayer.main | (intros; apply GlobalTheory.HeightCounting.Up.PendLayer.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtendedColumnDataAllClausesButPlacesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extendedColumnData_all_clauses_but_places : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∃ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' ∧ ExtN z z') := by
  first | exact @GlobalTheory.Mem.R3.Rw.ExtBuild.exists_ext_build | exact GlobalTheory.Mem.R3.Rw.ExtBuild.exists_ext_build | (intros; apply GlobalTheory.Mem.R3.Rw.ExtBuild.exists_ext_build <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantSmoothRefinementPolyFan
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

theorem resolution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → ∃ φ' : InvFun (𝓞 E), IsPolFan H.bar q φ' ∧ NoSelfInt H.bar q φ' ∧ IsTwInv H φ' ∧ Subordinate H.bar q φ' φ := by
  intro E _ _ _ H q φ lab hD hP hT hL hS
  suffices key : ∀ n : ℕ, ∀ φ lab : InvFun (𝓞 E), maxMult H.bar q φ = n → IsPolyFan H.bar q φ → IsTwInv H φ →
      IsTwInv H lab → SimpLab H.bar q φ lab → ∃ φ' : InvFun (𝓞 E), IsPolFan H.bar q φ' ∧ NoSelfInt H.bar q φ' ∧
        IsTwInv H φ' ∧ Subordinate H.bar q φ' φ by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (GlobalTheory.T.maxSimplicialCellMultiplicity_lt_top_of_isPolyFan E H q φ hP).ne
    exact key n φ lab hn.symm hP hT hL hS
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro φ lab hn hP hT hL hS
    by_cases h2 : 2 ≤ maxMult H.bar q φ
    · obtain ⟨φ', lab', hP', hT', hL', hS', hsub, hlt⟩ :=
        GlobalTheory.T.exists_starSubdivision_lowers_maxCellMultiplicity E H q φ lab hD hP hT hL hS (hn ▸ ENat.coe_lt_top n) h2
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (hlt.trans_le le_top).ne
      have hkn : k < n := by
        rw [← hk, hn] at hlt; exact_mod_cast hlt
      obtain ⟨φ'', h1, h2, h3, h4⟩ := ih k hkn φ' lab' hk.symm hP' hT' hL' hS'
      exact ⟨φ'', h1, h2, h3, h4.trans hsub⟩
    · have hle : maxMult H.bar q φ ≤ 1 := by
        rw [hn] at h2 ⊢
        have : ¬ 2 ≤ n := fun h => h2 (by exact_mod_cast h)
        exact_mod_cast (show n ≤ 1 by omega)
      obtain ⟨h1, h2⟩ := GlobalTheory.T.isSmoothAdmissibleFan_of_cellMult_one_CMField E H q φ lab hD hP hS hle
      exact ⟨φ, h1, h2, hT, Subordinate.refl φ⟩

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRiemannFormPeriodChartGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_riemannForm_periodChart_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ x₀ : GlobalTheory.CxPts (genStr T.Z) σ, ∃ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g) (d : ℝ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ IsExpChart ch₀ ex ∧ x₀ ∈ ch₀.source ∧ ch₀ x₀ = 0 ∧ Fintype.card ((Σ τ : E →+* ℂ, Fin (Dw.mult τ))) = g ∧ 0 < d ∧ (∀ x ∈ ch₀.source, Inner x ↔ ∀ i : Fin a, ch₀ x (Fin.castLE ha i) ≠ 0) ∧ ∀ x ∈ ch₀.source, Inner x → ((((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹).IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹) u u).re) ∧ (∀ v w : Fin g → ℂ, ex x v = 1 → ex x w = 1 → ∃ m : ℤ, (hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹) v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex x v = 1 → ex x w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm (((d : ℝ) : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B (ch₀ x))⁻¹) v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil T.Z.t.cub k (ex x ((k : ℂ)⁻¹ • v)) (ex x ((k : ℂ)⁻¹ • w)) (unitOn ζ)) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.PerChart.exists_riemann_period_chart | exact GlobalTheory.ShFam.Hor.LogCh.PerChart.exists_riemann_period_chart | (intros; apply GlobalTheory.ShFam.Hor.LogCh.PerChart.exists_riemann_period_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodCuspidalParameterLocalSide
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.HeightCounting.Up.ParCopy

set_option maxHeartbeats 4000000 in

theorem parIn_of_nTrue {hL : GlobalTheory.Published.LocalLanglandsGL} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : NTrue hL D' cf' C' tp') (rep' : D'.what₂.FT → NG.FinTyp D'.host.E D'.R.r)
    (hrep : HEq nt.rep rep') :
    ∃ Rw : RowSide D', HEq Rw.locR nt.A.row.locR ∧ Nonempty (ParIn hL D' cf' rep' Rw) := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp pack
  obtain ⟨hcf, -⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  subst hcf
  have hr : rep = rep' := eq_of_heq hrep
  subst hr
  let T : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut := { A.wdT with }
  let Rw : RowSide (withLoc L) := { A.row with }
  refine ⟨Rw, HEq.rfl, ⟨{ T := T, lab := A.lab, chr := { A.chr with }, cg := { cg with }, A := { A.au with }, au := au, row := row }⟩⟩

set_option maxHeartbeats 4000000 in

theorem mtInput_of_nTrue {hL : GlobalTheory.Published.LocalLanglandsGL} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : NTrue hL D' cf' C' tp') (M' : MtFam D') (hM : HEq (mtL nt.L nt.M) M') :
    ∃ tup Q, MtInput D' M' tup Q := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  have hm : mtL L M = M' := eq_of_heq hM
  subst hm
  exact ⟨tp.tup, C.Q, { mt with }⟩

set_option maxHeartbeats 4000000 in

theorem final (hN : PrN) (hL : GlobalTheory.Published.LocalLanglandsGL) {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : NTrue hL D' cf' C' tp') (Rw0 : RowSide D') (h0 : HEq Rw0.locR nt.A.row.locR)
    (hLift : LiftAll D' Rw0) (hLoc : ∀ σ, RowLoc D' Rw0 σ) (hEFK : SphericalInertData.HypEFK D') (hCM : SphericalInertData.HypCM D')
    (hDef : ∀ j, 1 ≤ j → j ≤ D'.R.m → (D'.sp.V j).IsDefinite) (Rw : RowSide D') (hRw : HEq Rw.locR nt.A.row.locR) :
    GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D' Rw := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  have e0 : Rw0.locR = A.row.locR := eq_of_heq h0
  have e1 : Rw.locR = A.row.locR := eq_of_heq hRw
  have hpar : ParIn hL D cf rep A.row := ⟨A.wdT, A.lab, A.chr, cg, A.au, au, row⟩
  have hLaws := GlobalTheory.T.parameter_laws_empty hN hL D cf rep A.row A.bare hpar
  have hconds := GlobalTheory.T.base_change_of_hypotheses hN.bc hN.what₂.bern hN.ds hN.gen hN.std hL D A.wdT A.au cg au
  have hLift' : LiftAll D A.row := by
    intro j h1 h2 σ hσ
    obtain ⟨π, μ, hl⟩ := hLift j h1 h2 σ hσ
    refine ⟨π, μ, ⟨hl.csd, hl.unr, hl.sph, fun w hw => ?_, hl.eta, hl.inf⟩⟩
    have := hl.loc w hw
    rw [e0] at this
    exact this
  have hLoc' : ∀ σ, RowLoc D A.row σ := by
    intro σ w hw hk
    have := hLoc σ w hw hk
    rw [e0] at this
    exact this
  have hG := GlobalTheory.T.good_row_cusp_param D A.row hLaws hconds hEFK hCM hDef hLift' hLoc'
  intro j h1 h2 σ hσ hg
  obtain ⟨π, hπ⟩ := hG j h1 h2 σ hσ hg
  refine ⟨π, hπ.1, hπ.2.1, fun w hw => ?_, hπ.2.2.2⟩
  rw [e1]
  exact hπ.2.2.1 w hw

end GlobalTheory.HeightCounting.Up.ParCopy

namespace GlobalTheory.HeightCounting.Up

open GlobalTheory.HeightCounting.Up.ParCopy in

theorem goodRowCuspParam_atMem : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL (fun _ _ _ _ w Z _ _ _ _ _ c =>
    ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw) := by
  intro hN hL
  have hlift := GlobalTheory.T.lift_all_of_inputs hN hL
  have hloc := GlobalTheory.T.row_local_all hN hL
  have hsz := GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices
  refine EvG.imp ((hlift.inter hloc).inter hsz) fun K _ _ _ _ H => ?_
  refine large₂.imp ((H.1.1.inter H.1.2).inter H.2) fun B f T _ h => ?_
  intro hKP w Z Wt p0 t nch n xd c hE _ hpin Rw hRw
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨e⟩ := hE
  have e' : NMore (D := (w.st Z).toD7) c.row t.r.z.geo xd := e
  obtain ⟨Rw0, hRw0, ⟨hpar⟩⟩ := parIn_of_nTrue c.a.nt _ c.row.rep_eq
  obtain ⟨tup, Q, hmt⟩ := mtInput_of_nTrue c.a.nt c.a.all.gal.mt c.a.mt_eq
  have hLift := h1 hKP w hpin Z Wt t.hX t.r.z p0 t.r.Y t.r.intersectionNumber_baseChange t.exAt t.inGeo t.grp t.grpAt Rw0 hpar _ tup Q e'.ad hmt
  have hLoc := h2 hKP w hpin Z Wt t.hX t.r.z p0 t.r.Y t.r.intersectionNumber_baseChange t.exAt t.inGeo t.grp t.grpAt Rw0 hpar
  obtain ⟨-, -, -, hEFK, hCM, hDef, -⟩ := h3 hKP T w Z
  exact final hN hL c.a.nt Rw0 hRw0 hLift hLoc hEFK hCM hDef Rw hRw

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricPointClassFormMassEqCovolume
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.BaseVolume

theorem mass_openPart_eq_covol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 (ptsIn X.str (σ.comp e.toRingHom) (openPart j)) = ENNReal.ofReal (GlobalTheory.TrueCx.covol (U.X k)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL
  have hj' : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right _ _
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by have := (hU.2.1 k).1; omega
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_componentUniformisation_boundedDomain_complexPoints E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL
  have himg := GlobalTheory.T.uniformisation_image_boundedDomain_eq_openPart E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hfib := GlobalTheory.T.componentUniformisation_fibre_arithmeticGroup_related E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hinv := GlobalTheory.T.componentUniformisation_arithmeticGroup_invariant E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hdens := GlobalTheory.T.chernTopPart_hodgeMetric_uniformisation_image E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hnull := GlobalTheory.T.uniformisation_null_sets_to_pointClass_null E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  obtain ⟨FD, hFD⟩ := GlobalTheory.BoundedFundDomain.exists_isFD E (Dw.p + Dw.q) Dw.p (U.X k) hj' (U.X k).Ψ (Equiv.refl _) hp
  obtain ⟨hlt, hcov⟩ := GlobalTheory.FlagFibre.covol_eq_muD E (Dw.p + Dw.q) Dw.p (U.X k) hj' (U.X k).Ψ (Equiv.refl _) hp FD hFD
  obtain ⟨hFm, hFsub, hFcov, hFbad⟩ := hFD
  set μD := muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hμD
  set Bad := {v | v ∈ FD ∧ ∃ γ ∈ gammaU (U.X k) hj' (Equiv.refl (U.X k).Ψ), flat (moebI γ (unflat v)) ∈ FD ∧
    moebI γ (unflat v) ≠ unflat v} with hBad
  set B' := toMeasurable μD Bad with hB'
  have hB'0 : μD B' = 0 := by rw [hB', measure_toMeasurable]; exact hFbad
  have hfu : ∀ v : (U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ, flat (unflat v) = v := fun v => rfl
  have hinj : Set.InjOn ψ (FD \ B') := by
    intro v hv w hw hvw
    obtain ⟨γ, hγ, hγe⟩ := hfib v (hFsub hv.1) w (hFsub hw.1) hvw
    have hnb : v ∉ Bad := fun h => hv.2 (subset_toMeasurable _ _ h)
    have h1 : moebI γ (unflat v) = unflat v := by
      by_contra hne
      exact hnb ⟨hv.1, γ, hγ, by rw [hγe, hfu]; exact hw.1, hne⟩
    rw [← hfu v, ← hfu w, ← hγe, h1]
  have hD := hdens (FD \ B') (Set.diff_subset.trans hFsub) (hFm.diff (measurableSet_toMeasurable _ _)) hinj
  have hN := hnull (FD ∩ B') (Set.inter_subset_left.trans hFsub) (measure_mono_null Set.inter_subset_right hB'0)
  have hmF : μD (FD \ B') = μD FD := measure_diff_null hB'0
  have hsub : ψ '' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) ⊆ ψ '' (FD \ B') ∪ ψ '' (FD ∩ B') := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨γ, hγ, hγF⟩ := hFcov (unflat v) hv
    rw [← Set.image_union, Set.diff_union_inter, ← hinv γ hγ v hv]
    exact Set.mem_image_of_mem _ hγF
  have hsup : ψ '' (FD \ B') ⊆ ψ '' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) :=
    Set.image_mono (Set.diff_subset.trans hFsub)
  rw [← himg, hcov, ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hlt.ne, ← hmF, ← hD]
  refine le_antisymm ?_ (measure_mono hsup)
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ = _ := by rw [hN, add_zero]

end GlobalTheory.BaseVolume
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MotiveBoundOfSeries
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

theorem mvB_of_classicalTheorems : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, MvB hL := by
  intro hP hS hL
  refine StepW.trans (StepW.and (GlobalTheory.T.same_galois_extension_state hP hS hL) (GlobalTheory.T.carried_state_lift_listing hP hS hL)) (StepW.of_all fun K B' f' T' w' _ _ h => ?_)
  obtain ⟨h, h'⟩ := h
  intro B f T w hE hf hSt hpx hsel hJ hδ P x l P' hExt x' l' hG
  obtain ⟨x₁, ⟨l₁⟩, hC₁, hL₁⟩ := h B f T w hE hf hSt hpx hsel hJ hδ P x l P' hExt x' l' hG
  obtain ⟨x₂, hl₂, hC₂, hL₂⟩ := h' P' x₁ (Dof x) l₁ hC₁
  exact ⟨x₂, hl₂, hC₂, fun c hc => hL₂ c (hL₁ c hc)⟩

end GlobalTheory.HeightCounting.Up
end

