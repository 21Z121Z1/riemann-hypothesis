import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsOfRepresentationTheoryOfHyp
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0067
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0132
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0170
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0039
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0040
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0042
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0156
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0043
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0613
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0079
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0152
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3217
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0118
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0015
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0168
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0146
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0828
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0133
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0850
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0159
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GalRead

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BundlePackEqAdelicData
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.PtRowsAt
section General
open NumberField IsDedekindDomain MeasureTheory
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult
  Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe
section Args
open GlobalTheory.Mem.Top.Bl
variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0}
end Args
set_option maxHeartbeats 1000000 in
theorem see_join_alt (h5 : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
    {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts}
    {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX} (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex)
    (P : SPack D fun u => (Rc.T.cols.forms u).to0) (S : SRest P) (S0 : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (hS : S0 = S.toRealSpectralMatching Rc)
    (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S0) (c : ℝ) (hH : Holds x.R x.F) (hP : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y))
    (h : Placed x.R.toRealDat x.F.lv2 x.Y.eE P S y.tS c) :
    _root_.Formalism.IndefR.IndefiniteRealisationExtends (_root_.GlobalTheory.Mem.R3.realisationOfInput y) ∧ Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin Rc S0 (_root_.GlobalTheory.Mem.R3.realisationOfInput y)) := by
  subst hS
  have hSch : SchurAll D := fun V _ S θ M J χ μ 𝓕 =>
    (GlobalTheory.MultFinite.hcFinite_and_schurMult h5.2.2.2.1 h5.2.2.2.2 D θ V S M J χ μ 𝓕).2
  have hL := (GlobalTheory.T.rowLattices_metrics_agree_of_realGroupTheorems h5 D _ _ _ _ x.A3 _ x.R x.F x.cG ex.p0 x.Y x.Z x.pins hH).1
  exact ⟨(_root_.GlobalTheory.Mem.JPin.seeEx_joinPin_alt _ _ _ _ _ _ _ _ _ x Rc P S y c hH h.1 h.2.1 h.2.2).1,
    (_root_.GlobalTheory.T.join_subspace_real_data_exists_alt _ _ _ _ _ _ _ _ _ x Rc P S y c 1 hSch hP hH hH.ok hH.sep hL
      (rowConditions_at_companion_from_readings _ _ _ _ _ _ _ _ _ x).2.1 h.1 h.2.1 h.2.2).1⟩
end General
section Wit
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} {q : Bl.WPt p.s K} {c : ℝ} {b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c}
theorem bundle_P_eq_divisionPair_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : b.P = R3.divisionPairOfAdelicFormsFaceColumnsData w.x := congrArg _root_.GlobalTheory.Mem.Top.Bl.RealPackage.P w.y.eq
theorem dcPtG_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : DcPtG b.P := by
  rw [_root_.GlobalTheory.Fam.PtRowsAt.bundle_P_eq_divisionPair_of_bWit w]
  exact (GlobalTheory.Mem.R3.rowConditions_at_companion_from_readings _ _ _ _ _ _ _ _ _ w.x).2.2.1
theorem realPins_of_bWit' (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation b.B.Q := (_root_.GlobalTheory.T.characters_match_bundle_alt q b w).2.2.2.2.2.1
theorem framesEx_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx b.B.Q := by
  letI := b.B.alg
  exact _root_.GlobalTheory.FramesAtReal.framesEx_of_realisation_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b.B.Q (_root_.GlobalTheory.Fam.PtRowsAt.realPins_of_bWit' w)
theorem prim_links_and_typesSep3_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : Formalism.IndefR.Links.PrimRows3 b.B.Q.Rl b.B.Q.F ∧ b.P.A3.fam3.TypesSep3 := by
  have h : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => Formalism.IndefR.Links.PrimRows3 r.B.Q.Rl r.B.Q.F ∧ r.P.A3.fam3.TypesSep3) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput w.y.y) :=
    ⟨w.y.intersectionNumber_baseChange.prim, w.y.intersectionNumber_baseChange.sep⟩
  rw [← w.y.eq] at h
  exact h
theorem exAt_of_bWit (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : b.B.Q.Rl.toRealDat.ExAt := by
  have h : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => r.B.Q.Rl.toRealDat.ExAt) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput w.y.y) := exAt_of_args w.a w.x w.ax
  rw [← w.y.eq] at h
  exact h
set_option maxHeartbeats 1000000 in
theorem seeEx_and_joinSI_nonempty_of_bWit (h5 : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) :
    _root_.Formalism.IndefR.IndefiniteRealisationExtends b.B.Q ∧ Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin b.R b.S b.B.Q) := by
  obtain ⟨sP, sS, hP, hS, e⟩ := w.s
  have hpin : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => _root_.Formalism.IndefR.IndefiniteRealisationNormalisation r.B.Q) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) := _root_.GlobalTheory.Fam.PtRowsAt.realPins_of_bWit' w
  rw [w.y.eq] at hpin
  have h0 := placed_of_args w.a w.x w.ax q.saturationAtWeightedPoint.P q.saturationAtWeightedPoint.S q.saturationAtWeightedPoint.t q.saturationAtWeightedPoint.c ⟨q.saturationAtWeightedPoint.see, q.saturationAtWeightedPoint.ev, q.saturationAtWeightedPoint.rowJ⟩
  have ht : w.y.y.tS = q.saturationAtWeightedPoint.t := eq_of_heq w.pt.1
  have hF : (fun u => (b.R.T.cols.forms u).to0) = fun u => (q.x.col.C.forms u).to0 :=
    congrArg (fun C : type_of% q.x.col.C => fun u => (C.forms u).to0) w.recPin.s.cols
  have h1 := Placed.of_heq hF hP hS h0
  rw [← ht] at h1
  have h : (fun r : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => _root_.Formalism.IndefR.IndefiniteRealisationExtends r.B.Q ∧ Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin b.R b.S r.B.Q)) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput w.y.y) :=
    _root_.GlobalTheory.Fam.PtRowsAt.see_join_alt h5 w.x b.R sP sS b.S e w.y.y q.saturationAtWeightedPoint.c w.y.intersectionNumber_baseChange hpin h1
  rw [← w.y.eq] at h
  exact h
end Wit
theorem good_linked_ptR_of_cuspRapidDecay : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ _ _ _ b => _root_.GlobalTheory.Fam.BundlePointConditions b) := by
  intro h1 h2 h3 h4 h5 hL p
  obtain ⟨Cl₀, hnc⟩ := GlobalTheory.Core.Rk.HdNc.hd_nc
  refine (_root_.GlobalTheory.T.exists_constants_for_parameters_scale_bundle hL p (fun _ _ => 0) (fun _ _ => max 1801 Cl₀) (fun _ _ => 0)).imp ?_
  rintro κ K β c b - - ⟨q, b', ⟨w⟩, he⟩ ⟨C', Cl, Cg, CT, -, hCl, -, hHD, -, -, hB, hrS⟩
  have key : ∀ s t : (Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c), s = t →
      (Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin t.2.2.R t.2.2.S t.2.2.B.Q) ∧ DcPtG t.2.2.P ∧ _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx t.2.2.B.Q ∧
        _root_.Formalism.IndefR.IndefiniteRealisationExtends t.2.2.B.Q ∧ t.2.2.B.Q.Rl.toRealDat.ExAt ∧
        (Formalism.IndefR.Links.PrimRows3 t.2.2.B.Q.Rl t.2.2.B.Q.F ∧ t.2.2.P.A3.fam3.TypesSep3)) →
      (Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin s.2.2.R s.2.2.S s.2.2.B.Q) ∧ DcPtG s.2.2.P ∧ _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx s.2.2.B.Q ∧
        _root_.Formalism.IndefR.IndefiniteRealisationExtends s.2.2.B.Q ∧ s.2.2.B.Q.Rl.toRealDat.ExAt ∧
        (Formalism.IndefR.Links.PrimRows3 s.2.2.B.Q.Rl s.2.2.B.Q.F ∧ s.2.2.P.A3.fam3.TypesSep3)) := by
    rintro _ _ rfl h
    exact h
  have hsj := _root_.GlobalTheory.Fam.PtRowsAt.seeEx_and_joinSI_nonempty_of_bWit ⟨h1, h2, h3, h4, h5⟩ w
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := key ⟨β.D, β.O, b⟩ ⟨q.w.D q.Z, q.O, b'⟩ he
    ⟨hsj.2, _root_.GlobalTheory.Fam.PtRowsAt.dcPtG_of_bWit w, _root_.GlobalTheory.Fam.PtRowsAt.framesEx_of_bWit w, hsj.1, _root_.GlobalTheory.Fam.PtRowsAt.exAt_of_bWit w, _root_.GlobalTheory.Fam.PtRowsAt.prim_links_and_typesSep3_of_bWit w⟩
  exact ⟨a1, a2, a3, a4, a5, a6,
    GlobalTheory.Core.Rk.finX_of_gap _ b.S.toSTies (gapHyp_of_hd ((le_max_left _ _).trans hCl) hHD),
    hnc _ _ _ _ _ _ _ _ _ ((le_max_right _ _).trans hCl) hHD b.S.X,
    GlobalTheory.Core.Rk.GapOfNodes.harishChandraNodesFarApart_of_cubic_node_gap _ hB, hrS⟩
end GlobalTheory.Fam.PtRowsAt
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DatExists
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam
theorem QuadraticExtensionData.dat_exists : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∃ C : ℕ → ℂ, (∀ j, j < B.R.m → C j ≠ 0) ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∃ s ζ ρ, J.Dat C s ζ ρ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr hoT
  obtain ⟨C, hC0, hC⟩ := _root_.GlobalTheory.T.true_geometry_row_pair_relation_alt_alt W hW u a ha hTr hoT
  refine ⟨C, hC0, fun t J hR => ?_⟩
  obtain ⟨e₀, he₀, hAe⟩ := _root_.GlobalTheory.T.true_geometry_twist_quadratic_level_alt W hW u a ha hTr t J hR
  obtain ⟨p, q, hA, hB, ⟨c0, hc0, h0⟩, hstep, hD⟩ := _root_.GlobalTheory.T.true_geometry_row_pair_property_alt W hW u a ha hTr hoT t J hR
  set Af : ∀ j, J.Ch j → ℂ := fun j α => p j α * (J.A.chr (j + 1) (J.A.xr j (J.ι j α)) : ℂ) with hAf
  set Bf : ∀ j, J.Ch (j + 1) → ℂ := fun j γ => q j γ * ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ))⁻¹ with hBf
  let k : ℕ → ℂ := fun j => if h : j + 1 < B.R.m then (hstep j h).choose else 1
  have hk : ∀ j, ∃ n : ℕ, 0 < n ∧ k j ^ n = 1 := fun j => by
    by_cases h : j + 1 < B.R.m
    · simp only [k, dif_pos h]; exact (hstep j h).choose_spec.1
    · simp only [k, dif_neg h]; exact ⟨1, one_pos, by simp⟩
  let cc : ℕ → ℂ := fun j => c0 * ∏ i ∈ Finset.range j, k i
  have hcc : ∀ j, ∃ n : ℕ, 0 < n ∧ cc j ^ n = 1 := fun j =>
    datRoot_mul hc0 (datRoot_prod _ _ fun i _ => hk i)
  let s : ∀ j, J.Ch j → ℂ := chartRescale B.R.m cc Bf
  have hs0 : ∀ α, s 0 α = 1 := fun _ => rfl
  have hsS : ∀ j γ, j < B.R.m → s (j + 1) γ = cc j * Bf j γ := fun j γ h => by
    show (if j < B.R.m then cc j * Bf j γ else 1) = _
    rw [if_pos h]
  have hsA : ∀ j, j < B.R.m → ∀ α, s j α * Af j α = cc j := by
    intro j
    induction j with
    | zero => intro _ α; rw [hs0, one_mul]; simp [cc, Af, h0 α]
    | succ j ih =>
      intro hj γ
      rw [hsS j γ (by omega)]
      have hk' : k j = (hstep j hj).choose := by simp only [k, dif_pos hj]
      have := (hstep j hj).choose_spec.2 γ
      calc cc j * Bf j γ * Af (j + 1) γ = cc j * (Bf j γ * Af (j + 1) γ) := by ring
        _ = cc j * k j := by rw [hk', ← this]
        _ = cc (j + 1) := by simp only [cc, Finset.prod_range_succ]; ring
  have hsroot : ∀ j α, ∃ n : ℕ, 0 < n ∧ s j α ^ n = 1 := by
    intro j
    cases j with
    | zero => intro α; exact ⟨1, one_pos, by rw [hs0, one_pow]⟩
    | succ j =>
      intro γ
      by_cases h : j < B.R.m
      · rw [hsS j γ h]; exact datRoot_mul (hcc j) (hB j h γ)
      · refine ⟨1, one_pos, ?_⟩
        show (if j < B.R.m then cc j * Bf j γ else 1) ^ 1 = 1
        rw [if_neg h, one_pow]
  refine ⟨s, fun j α γ => s j α * (s (j + 1) γ)⁻¹ * (p j α * q j γ), fun _ => 1, hsroot, hs0,
    fun _ => ⟨1, one_pos, one_pow 1⟩, fun j hj α γ => ⟨?_, ?_⟩⟩
  · have h1 := hD e₀ he₀ j hj α γ _ _ (hC t J hR e₀ he₀ j hj α γ)
    have h2 := isRatDatum_const_mul h1 (s j α * (s (j + 1) γ)⁻¹ * J.wt j α)
    rw [← hAe] at h2
    have hdQ : J.dQ s j α γ = (s j α * (s (j + 1) γ)⁻¹ * J.wt j α) • aconv (List.ofFn fun i => (J.E i).dL j (α i) (γ i)) := by
      simp only [_root_.GlobalTheory.Fam.QuadraticExtensionData.dQ, smul_smul]
    rw [hdQ, comb_smul_coef]
    convert h2 using 2
    rename_i z
    beta_reduce
    rw [_root_.GlobalTheory.T.true_geometry_twist_quadratic_value_alt W hW u a ha hTr t J hR j hj α γ z]
    ring
  · have hjm : j < B.R.m := by omega
    have hSA := hsA j hjm α
    have hBn : Bf j γ ≠ 0 := datRoot_ne_zero (hB j hjm γ)
    have hcn : cc j ≠ 0 := datRoot_ne_zero (hcc j)
    beta_reduce
    rw [hsS j γ hjm]
    have hx : ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ)) ≠ 0 := by
      exact Circle.coe_ne_zero _
    calc s j α * (cc j * Bf j γ)⁻¹ * (p j α * q j γ) * (J.A.chr (j + 1) (J.A.xr j (J.ι j α)) : ℂ) *
          ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ))⁻¹
        = (s j α * Af j α) * Bf j γ * (cc j * Bf j γ)⁻¹ := by simp only [hAf, hBf]; ring
      _ = 1 := by rw [hSA]; exact mul_inv_cancel₀ (mul_ne_zero hcn hBn)
end GlobalTheory.Fam
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DegLieCore
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FlatCore
namespace GlobalTheory.DefCoreLie
end GlobalTheory.DefCoreLie
namespace GlobalTheory.DefCoreLie
theorem degLie_core_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → ∀ (Z : Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) (P : PtData Z) (τ : Psi p.T.Q.H), P.degLie τ.1 = -flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hm hG hW hN hF Z P τ
  obtain ⟨hDC, -, -, -⟩ := _root_.GlobalTheory.T.finite_nonempty_components_and_dict_mem_dom p i PP A M hR hm hG hW hN hF
  have hJ : LawsJ p.T := p.fw.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.succ_pos _, hm.le⟩
  have hL : Laws (p.T.U ((i : ℕ) + 1)) (xiR D) := GlobalTheory.LawsCore.laws_core D p.T hJ _ hj hF
  obtain ⟨_, χ, hχ, hOm, -, hH⟩ := GlobalTheory.T.logPeriod_eq_kroneckerCharacter_logPeriod_of_host D L p.T.Q hJ.pins.1 p.Del p.h0
  have hFr := frameDeg_def GlobalTheory.T.cmObject_definite_lieEigenLattice_degree_difference D.host.E p.T.Q.H hH χ hχ _ _ _ _ _ _ _ hL hDC.q
  obtain ⟨s⟩ := GlobalTheory.FlatLine.Definite.nonempty_flatSec (p.T.U ((i : ℕ) + 1)) (xiR D) hDC.q hDC.p hDC.good hDC.unf hDC.geo Z τ
  have h := (hFr Z τ (ArchSec.ofConst s.toFrame) s.toFrame.rho_vw fun w v hv => by
      have h1 := s.toFrame.val_eq hv
      rw [Pi.zero_apply, zero_add] at h1
      exact h1).2
  rw [(GlobalTheory.T.degree_dualDetLie_eq_neg_flatSection_degree _ _ _ _ _ _ _ _ _ hDC Z P).1 τ s, s.deg_eq_toFrame, flatDegVal, ← hOm, ← h]
  rfl
end GlobalTheory.DefCoreLie
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsCuspWithThetaJetValueLe
section
set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace GlobalTheory.ThetaJetsT
theorem exists_cusp_with_theta_jet_value_le_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ f ∈ AllWt.cuspOn Y.U Z (Formalism.L2.Pj.wtZ (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i))), evI y' f ≠ 0 ∧ (vV T.V (evI y' f) : ℝ) ≤ cst * φT := by
  intro h1 h2 h3 h4
  have hA := _root_.GlobalTheory.T.theta_jet_value_bound_char_zero' h1 h2 h3 h4
  have hC := _root_.GlobalTheory.T.theta_cusp_value_formula_at_weight h1 h2 h3 h4
  unfold _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition Formalism.MainNotions.Closed at hA hC ⊢
  obtain ⟨ε1, hε1, hA⟩ := hA
  obtain ⟨ε2, hε2, hC⟩ := hC
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun eps he hle => ?_⟩
  obtain ⟨K1, hK1⟩ := hA eps he (hle.trans (min_le_left _ _))
  obtain ⟨K2, hK2⟩ := hC eps he (hle.trans (min_le_right _ _))
  refine ⟨⟨max K1.pre K2.pre, fun l => max (K1.t l) (K2.t l), fun l => max (K1.mid l) (K2.mid l),
    fun l => max (K1.last l) (K2.last l)⟩, fun Fm CH hF hL => ?_⟩
  have hL1 : Fm.Large K1 CH := ⟨fun c hc => (le_max_left _ _).trans (hL.1 c hc), trivial,
    fun c hc => (le_max_left _ _).trans (hL.2.2.1 c hc), fun c hc => (le_max_left _ _).trans (hL.2.2.2 c hc)⟩
  have hL2 : Fm.Large K2 CH := ⟨fun c hc => (le_max_right _ _).trans (hL.1 c hc), trivial,
    fun c hc => (le_max_right _ _).trans (hL.2.2.1 c hc), fun c hc => (le_max_right _ _).trans (hL.2.2.2 c hc)⟩
  obtain ⟨C1, hC1, hE1⟩ := hK1 Fm CH hF hL1
  obtain ⟨C2, -, hE2⟩ := hK2 Fm CH hF hL2
  refine ⟨C1, hC1, ?_⟩
  obtain ⟨x1, hx1⟩ := hE1.and hE2
  refine ⟨x1, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hAi, hCi⟩ := hx1 x hx hle ι p hp
  have hA' := hAi i hi Y hY
  have hC' := hCi i hi Y hY
  intro Z TF la hla cst hJ y hy T io y' g φT hg hφ hpt
  have hch : CharZero (IsLocalRing.ResidueField T.V) := GlobalTheory.UnifTrait.charZero_residue_of_map T.V
    (Spec.map (CommRingCat.ofHom g) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z ≫ TF.X.π ≫ TF.Y.s)
  obtain ⟨st, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond _ _ _ _ Y.d.Xo₂ Y.d.c₂
  obtain rfl := GlobalTheory.PowGerm.starSt _ _ st hnab.1
  obtain ⟨T', io', y'', r, C, P, hch', hr, hC0, hP, hφ', hsc⟩ := GlobalTheory.T.exists_extension_truncatedFrame_chart_residue_charZero _ _ _ _ Y.d.Xo₂ Y.d.c₂ T io y' hch φT hφ
  obtain ⟨f, hf, hne, hle⟩ := hA' la hla cst hJ nab hnab T' io' y'' C P (r * φT) hch' hC0 hP hφ'
  have hs := hsc nab hnab _ _ 1 1 f hf
  simp only [map_one, one_mul, mul_one] at hs
  obtain ⟨f', hf', hev⟩ := hC' Z TF la hla nab hnab f hf y T io y' g hpt
  have hne' : evI y' f ≠ 0 := by
    intro h0
    rw [h0, nval_zero, nval_of_ne hne] at hs
    exact EReal.coe_ne_top _ hs
  refine ⟨f', hf', hev ▸ hne', ?_⟩
  rw [hev]
  rw [nval_of_ne hne, nval_of_ne hne', EReal.coe_eq_coe_iff] at hs
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hφ0 := hφ.nonneg
  rw [Nat.cast_one, div_one] at hs
  rw [← hs, div_le_iff₀ hr']
  nlinarith
end GlobalTheory.ThetaJetsT
end
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_jet_cusp_value_bound_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → ∀ y ∈ (U₀ TF.X Z : Set (Y₀ TF.X Z))ᶜ, ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V) (φT : ℝ), IsLocalHom g → GlobalTheory.SlopeRec.HasPhi y' φT → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ f ∈ AllWt.cuspOn Y.U Z (Formalism.L2.Pj.wtZ (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i))), evI y' f ≠ 0 ∧ (vV T.V (evI y' f) : ℝ) ≤ cst * φT := by
  first | exact @_root_.GlobalTheory.ThetaJetsT.exists_cusp_with_theta_jet_value_le_alt | exact _root_.GlobalTheory.ThetaJetsT.exists_cusp_with_theta_jet_value_le_alt | (intros; apply _root_.GlobalTheory.ThetaJetsT.exists_cusp_with_theta_jet_value_le_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrameAtOfLayerStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameAt_of_tup_eq_mu_at_members : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c => ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s k, t.r.Y.tup s = (w.st Z).toD7.nd.mu i → GlobalTheory.CenLocAt.FrameAt t.r.Y t.r.z.cG k (ad.PV k) s := by
  first | exact @_root_.GlobalTheory.CenLocAt.frameAt_of_layer_alt | exact _root_.GlobalTheory.CenLocAt.frameAt_of_layer_alt | (intros; apply _root_.GlobalTheory.CenLocAt.frameAt_of_layer_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalSide
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.TwInputs
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}
structure GalSideAlt (D : D7) : Type 1 where
  wd : GlobalTheory.RowTie.WDTie D.nd D.naut
  lab : GlobalTheory.HeightCounting.LabTrue D wd
  cf : CharFrame D
  chr : GlobalTheory.HeightCounting.CharSide D cf
  triple : _root_.GlobalTheory.Triple.IsGaloisTriple D
  lam : GlobalTheory.LamTie.LamDat D
  lamOk : lam.Ok
  lamTie : GlobalTheory.LamTie.IsLamTie D.ntw lam
  rank : 100 ≤ D.R.r
  primes : ∀ k, 2 * D.R.r ≤ D.host.g k
section Abstract
end Abstract
end GlobalTheory.TwInputs
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkSat
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Formalism.L2.Host Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.HeightCounting (CharSide)
open GlobalTheory.GalOfCusp GlobalTheory.TripleGal GlobalTheory.Triple
open GlobalTheory.TypeLeaf (FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
open GlobalTheory.JumpDictionaryFoundation (exists_embOver embOver_true_apply)
section Twist
variable {D : D7} {C₀ : CharFrame D} (S : CharSide D C₀) {n : ℕ} (π : D.naut.CG n) {ξ : HChar D.host.E} (hξ : ξ.IsUnitary)
variable {π}
end Twist
section Chars
variable {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m)
end Chars
section Triple
variable {D : D7} {T : WDTie D.nd D.naut} {C₀ C : CharFrame D} (S : CharSide D C₀)
  {art : Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om} {i : D.ntw.Tw} {s : D.ntw.Sig i}
  {ρ : Reading D.ntw i (D.ntw.side i s)} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))} {ν : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* (D.ntw.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.Zbar (D.ntw.l i) →+* FbAt D w}
theorem hkSat_of_isTripleWith (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) :
    HkSat D.naut i s (ρ.ι.toRingHom.comp ρ.κ) (twBy S π (mu_unitary C (D.ntw.l i) (jIdx s))) := by
  intro P hP hs k hk
  obtain ⟨x, h1, h2⟩ := h.hecke k P hk hs hP
  refine ⟨x, h1.symm, h2.trans ?_⟩
  have hμ := mu_unr C (jIdx s) (fun k hk => hP (D.ntw.placesOver_subset_exceptional i k hk)) fun hp => hP (D.ntw.primes_subset_exceptional i hp)
  rw [(twBy_unr S (mu_unitary C (D.ntw.l i) (jIdx s)) (h.unr_of_notMem hP) hμ.inv).2, heckeVal, satake, Multiset.map_map]
  have e1 : ((k : ℂ) * ((D.R.r : ℂ) - k)) / 2 = ((k * (D.R.r - k) / 2 : ℕ) : ℂ) := by
    have := congrArg (Nat.cast : ℕ → ℂ) (two_mul_half D.R hk)
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hk] at this
    rw [← this]
    push_cast
    ring
  have e2 : -((D.R.r : ℂ) + D.R.t) / 2 = -((D.R.nV / 2 : ℕ) : ℂ) := by
    have := congrArg (Nat.cast : ℕ → ℂ) (two_mul_nV_half D.R)
    rw [Nat.cast_mul, Nat.cast_add] at this
    rw [← this]
    push_cast
    ring
  rw [e1, e2, Complex.cpow_neg, Complex.cpow_natCast, Complex.cpow_natCast]
  congr 2
  refine Multiset.map_congr rfl fun a _ => ?_
  simp [mul_comm]
end Triple
end GlobalTheory.TripleLocal
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleOfSideB
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TripInhab
open GlobalTheory.Triple GlobalTheory.EigTie
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf GalE)
open GlobalTheory.TwistAbove (twGL)
variable {D : D7} {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om}
end GlobalTheory.TripInhab
namespace GlobalTheory.TripInhab
open GlobalTheory.Triple GlobalTheory.EigTie
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf GalE)
open GlobalTheory.TwistAbove (twGL)
theorem isTriple_of_sideB_alt : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ Sb : Finset (PlE D.host), (∀ i, Sb ⊆ D.ntw.S0 i) → (∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm) → ChiTOk D cf → GrpSide D → CharSide D cf → ValLL0 D cf → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → EigTrue D cf Rw Sb eig → EigOcc D S θ hL Sb eig → RowParam D Rw → _root_.GlobalTheory.EigTie.ResTiedAlt D Rw → _root_.GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GaloisRepsAlt D → D.nexp.sig_all → _root_.GlobalTheory.Triple.IsGaloisTriple D := by
  intro hCheb hArt D cf Rw low Pq S hL eig θ Bs Sb hSb hks hT hG hCS hV hroot hstar hET hEO hRP hRT hGR hall
  obtain ⟨art, ha⟩ := hArt D.host.E D.nd.Om
  refine ⟨cf, art, ha, fun i hi b => ?_,
    fun i _ s => GlobalTheory.T.twistTriple_eigenvector_in_good_part D cf Rw low Pq S hL eig θ Bs Sb hSb hks hEO i s, hall⟩
  obtain ⟨ρ, w, red, hind, hres⟩ := hRT.exists_reading hstar hi b
  have hc : IsChars cf art ρ := GlobalTheory.T.firstTwistCharacters_eq_ladic_characters_allReadings hCheb hArt D cf Rw low Pq S hL eig θ Bs hT hG hCS hV hroot art ha i b ρ
  refine ⟨ρ, hc, fun s hs => ?_⟩
  subst hs
  obtain ⟨hocc, hgood, hspec⟩ := Bs.rhoS i s
  obtain ⟨π, hpar⟩ := hRP _ (D.ntw.jS_range i s).1 (D.ntw.jS_range i s).2 _ hocc hgood
  obtain ⟨r, hr⟩ := hGR π hpar.1.csd hpar.1.ralg (D.ntw.l i) ρ.ι
  obtain ⟨ν, n, hν⟩ := exists_shift ha hV ρ
  have hR1 := hspec π hpar.1.csd hpar.1.ralg hpar.2 ρ.κ ρ.ι ρ.κ_alg (fun x => ρ.read x)
  have hR2 := _root_.GlobalTheory.TripInhab.isRepOf_twGL_of_isGal ha hCS ρ hr hν
  obtain ⟨A, hA⟩ := GlobalTheory.HeightCounting.FitRho.conj_of_isRepOf D ρ.ι _ _ (GlobalTheory.ChebSplitDense.chebSplit_nd hCheb D) _ _ hR1 hR2
  have hhk := GlobalTheory.TwInputs.HEig.hEig_eq_heckeVal D cf Rw low Pq S hL eig θ Bs Sb hSb hET i s ρ π hpar
  refine _root_.GlobalTheory.Triple.isTripleAt_of_conj_alt hgood hocc hpar.1 hr ⟨n, hν⟩ A (fun g => ?_) hhk hind
    (hres.2.2 _ π r hgood ⟨_, (D.ntw.jS_range i s).1, (D.ntw.jS_range i s).2, hocc⟩ hpar hr)
  have := congrArg (fun M : GL (Fin D.R.r) (Qbar (D.ntw.l i)) => (M : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.ntw.l i)))) (hA g)
  simp only [Units.val_mul, GlobalTheory.TwistAbove.twGL_val, Matrix.mul_smul, Matrix.smul_mul] at this
  rw [Units.val_mul, Units.val_mul]
  exact this
end GlobalTheory.TripInhab
end
end
end

