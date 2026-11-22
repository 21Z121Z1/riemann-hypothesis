import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0084
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2140
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0578
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0098
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0081
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0566
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0080
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0085
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0101
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0077
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0181
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0065
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0066
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0100
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0032
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0039
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0029
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0082

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IntTie
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField
open Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
namespace GlobalTheory.BigTop.Fun.IntTie
end GlobalTheory.BigTop.Fun.IntTie
open GlobalTheory.BigTop.Fun.IntTie in
theorem GlobalTheory.BigTop.Fun.int_tie_alt (hS : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint)
    (hd : Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps)
    (hB : BotSmall) (hN : BotNe) : _root_.GlobalTheory.BigTop.Fun.LeafIntegrality @Comparison₂ := by
  have hQ := _root_.GlobalTheory.T.forallLeaves_fitted_of_gBig _ hS hd (gBig_dep (gBig_and hB hN))
  refine _root_.GlobalTheory.BigTop.Fun.LeafConditions.mono hQ ?_
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d C CH _ hd
  refine ⟨hd, fun hq => ?_⟩
  obtain ⟨h1, h2, ⟨-, -, hsmall⟩, hne⟩ := hq
  change 1 ≤ CF at h1
  change CF ≤ C at h2
  obtain ⟨a, ha⟩ := hd.2
  have hsq := ha.sq
  obtain ⟨S, del, -, -, hNI, hdl⟩ := hsq.int
  obtain ⟨δ, t0, hP⟩ := hsq.norms
  choose P P' hb hz hz' using hP
  have hI := hNI δ t0 D.what₂.LL D.what₂.embLL (Sq D) P P' d.zA d.zA'
    (fun ij => hsmall δ t0 _ (P ij) (P' ij) _ ij.1 ij.2 _ (hb ij))
    (fun ij => hne δ t0 _ (P ij) (P' ij) ij.1 ij.2 (hb ij))
    (fun ij => ⟨hz ij, hz' ij⟩)
  rw [← hdl] at hI
  show NonArchimedeanDefectBound d.dl d.zA d.zA' (d.O.bDel C p.Z.b)
  refine integralNormBound_mono hI ?_
  clear hQ hne hsmall hb hz hz' hNI
  have eN : (d.O.N : ℝ) = (GlobalTheory.ChiGrid.bigN D : ℝ) := by
    have := D.R.m_add_three_le_k
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    norm_cast
    show D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 5) + 1) = D.R.k + D.R.m * (D.R.t + (GlobalTheory.ChiGrid.sLen D) + 1)
    unfold GlobalTheory.ChiGrid.sLen
    rw [hr]
    congr 3
    omega
  have eB : d.O.Bw = (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) := hsq.weight
  have eS : d.O.cS = Real.log (GlobalTheory.FunObj.SqNum.levQ d.G.pl) := by
    rw [GlobalTheory.FunObj.SqNum.log_levQ]
    rfl
  have ef : (d.O.f : ℝ) = D.R.f := rfl
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) * Real.log ((D.R.f : ℝ) * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ))) +
      D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) * (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) * Real.log p.Z.b +
      D.R.f * (2 * (GlobalTheory.ChiGrid.bigN D : ℝ)) ^ 2 * (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) *
        Real.log (GlobalTheory.FunObj.SqNum.levQ d.G.pl) := ⟨_, rfl⟩
  have e1 : d.O.bDel C p.Z.b = C * X := by
    unfold FunData.bDel
    rw [eN, eB, eS, ef, hX]
    ring
  have e2 : GlobalTheory.NormSum.intBound CF D.R.f (GlobalTheory.ChiGrid.bigN D) (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) (Real.log p.Z.b)
      (GlobalTheory.FunObj.SqNum.levQ d.G.pl) = CF * X := by
    unfold GlobalTheory.NormSum.intBound
    rw [hX]
    ring
  have h0 := hI.2.1 ∅
  rw [Finset.sum_empty] at h0
  change 0 ≤ GlobalTheory.NormSum.intBound CF D.R.f (GlobalTheory.ChiGrid.bigN D) (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) (Real.log p.Z.b)
      (GlobalTheory.FunObj.SqNum.levQ d.G.pl) at h0
  change GlobalTheory.NormSum.intBound CF D.R.f (GlobalTheory.ChiGrid.bigN D) (GlobalTheory.FunObj.SqNum.maxWt D 1 : ℝ) (Real.log p.Z.b)
      (GlobalTheory.FunObj.SqNum.levQ d.G.pl) ≤ _
  rw [e1, e2]
  rw [e2] at h0
  have hX0 : 0 ≤ X := (mul_nonneg_iff_of_pos_left (by linarith)).1 h0
  exact mul_le_mul_of_nonneg_right h2 hX0
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KapStStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inRange_kapAt_of_smallAt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → KapAt p j P w := by
  first | exact @_root_.GlobalTheory.FrameOf.kapSt_alt | exact _root_.GlobalTheory.FrameOf.kapSt_alt | (intros; apply _root_.GlobalTheory.FrameOf.kapSt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LabelsOkStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_place_block_decomposition_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ Q : (blk p j (p.R.mu w)).Pl, IsSplitAt (labOf p j (p.R.mu w) Q) ∧
      (labOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) = (plOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) ∧
      Ideal.absNorm (labOf p j (p.R.mu w) Q).asIdeal = (blk p j (p.R.mu w)).q Q ∧
      (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (labOf p j (p.R.mu w) Q).asIdeal ↔ ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (plOf p j (p.R.mu w) Q).asIdeal) := by
  first | exact @_root_.GlobalTheory.FrameLab.labels_ok_alt | exact _root_.GlobalTheory.FrameLab.labels_ok_alt | (intros; apply _root_.GlobalTheory.FrameLab.labels_ok_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticesFramesBasePointsExist
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem level_prime_not_mem_under_Pg_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) :
    ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ (PP.under (𝓞 D.host.F)).asIdeal := by
  intro PP hPP hmem
  obtain ⟨k, hk⟩ := (W.Q.charW.base.lev.Pg PP).1 hPP
  have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.under (𝓞 D.host.K)).asIdeal := by
    have := (W.Q.Rl.C.P).pb_over k
    rw [← show PP.under (𝓞 D.host.K) = _ from hk] at this
    exact this
  have h2 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h1
    simpa using this
  have h3 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal := hmem
    simpa using this
  have hc : IsCoprime (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.E) :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.mem u).A.T_prime (D.host.g_prime k)).2 (D.T_ne_g u k))
  obtain ⟨a, b, hab⟩ := hc
  exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ PP.asIdeal.add_mem (PP.asIdeal.mul_mem_left _ h3) (PP.asIdeal.mul_mem_left _ h2)))
theorem lattices_frames_basePoints_exist_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀))) (o : TDat (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = PP.under (𝓞 D.host.F)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (_root_.GlobalTheory.Fam.pk_z W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∃ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (b : ∀ j, GA D (Yc D j)) (dT : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) (M : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀) (β₀ : ∀ j ρ h i, GlobalTheory.FinPl.Frame (o.p i) (y.bes j ρ h).V₀ (Fin (D.sp.X j).rank ⊕ Fin 1)), ShapeOff { v with N := N, dT := dT, RamAd := o.Ram } { o with M := M, β₀ := β₀ } ∧ (∀ j, b j ∈ GfC (Yc D j) ∧ GlobalTheory.FinPl.CombAt (· ∈ v.tP) (dT j)) ∧ (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j) ∧ ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) → GlobalTheory.FinPl.Moves (Yc D j) (b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) (N j) P) ∧ ∀ PP h, Nonempty (LocY (l PP h) y N (_root_.GlobalTheory.Fam.pk_z W).βY b (bas PP h)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hT0 hτ hNT hζ hLT hgP htP hPre hLZ hbas
  have hPg : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ (PP.under (𝓞 D.host.F)).asIdeal :=
    _root_.GlobalTheory.Fam.level_prime_not_mem_under_Pg_alt W u
  have hdisj : Disjoint v.gP v.tP := Finset.disjoint_left.2 fun p hp hp' => by
    obtain ⟨PP, hPP, rfl⟩ := (hgP p).1 hp
    exact hPg PP hPP ((htP _).1 hp')
  have hU := _root_.GlobalTheory.levelPrime_not_mem_places_alt W u hW hPg
  have hA : ∀ PP h, ∃ (FY : FYFam (l PP h)) (sc : ℕ → (l PP h).k), IsNormalFr (l PP h) y FY sc :=
    fun PP h => GlobalTheory.T.exists_normalFrames_rationalDecompositions_over_local a y (l PP h) _ hTau hT0 (hU PP h)
  choose FY sc hFY using hA
  obtain ⟨N, dT, M, β₀, hShape, hdT, hSD, hInt⟩ :=
    _root_.GlobalTheory.T.local_component_measure_identity_alt_bis W u hW a y m b₀ k ι v o l bas hIs hTau hT0 hτ hNT hζ hLT hgP htP hdisj hPre hLZ hbas FY sc hFY
  obtain ⟨b, hbG, hbM, hbF⟩ :=
    _root_.GlobalTheory.T.local_component_measure_identity_alt_alt W u hW a y m b₀ k ι v o l bas hIs hTau hT0 hτ hNT hζ hLT hgP htP hdisj hPre hLZ hbas FY N hSD hInt
  refine ⟨N, b, dT, M, β₀, hShape, fun j => ⟨hbG j, hdT j⟩, fun j hj => ⟨hSD j hj, hbM j hj⟩, fun PP h => ⟨?_⟩⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hFY PP h
  exact { FY := FY PP h, sc := sc PP h, sc_unit := h1, sc_step := h2, hz_unit := h3, bes := h4, jac := h5, tau := h6,
          latY := hInt PP h, frame := hbF PP h }
end GlobalTheory.Fam
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevUIffInLevG
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FamTrace
theorem levU_iff_inLevG_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → ((y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U ↔ _root_.GlobalTheory.FamTrace.InLevelGroup a κ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat row col hc κ hκ y hy
  constructor
  · intro h
    exact ⟨_root_.GlobalTheory.T.true_geometry_lattice_forward_alt W hA u a ha hat row col hc κ hκ y hy h, _root_.GlobalTheory.T.true_geometry_lattice_image_alt W hA u a ha hat row col hc κ hκ y hy h, _root_.GlobalTheory.T.true_geometry_lattice_kernel_alt W hA u a ha hat row col hc κ hκ y hy h⟩
  · intro h
    refine ((_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U_eq _).2 ⟨y.2, fun v => ?_⟩
    by_cases hv : (((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal)
    · exact _root_.GlobalTheory.T.true_geometry_lattice_index_alt W hA u a ha hat row col hc κ hκ y hy h v hv
    · by_cases hb : v ∈ Formalism.L2.Forms.badG (I.rec7 l Z)
      · exact _root_.GlobalTheory.T.true_geometry_lattice_measure_alt W hA u a ha hat row col hc κ hκ y hy h v hb
      · exact _root_.GlobalTheory.T.true_geometry_lattice_volume_alt W hA u a ha hat row col hc κ hκ y hy h v hb hv
end GlobalTheory.FamTrace
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelSqYBoundAtRecStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leafLevelSq_and_leafYBound : _root_.GlobalTheory.BigOn.ForallRecordObjects fun Fm x _ i p _ O => LeafLevelSq O (Res (R2 p)) (Fm.D x i).R.f ∧ LeafYBound O := by
  first | exact @_root_.GlobalTheory.BigOn.levelSq_yBound_atRec_alt | exact _root_.GlobalTheory.BigOn.levelSq_yBound_atRec_alt | (intros; apply _root_.GlobalTheory.BigOn.levelSq_yBound_atRec_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Link
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Top.link_alt_alt_alt : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (hLamP : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.Rows.RowsHoldLam3 (selP Fm hc x hx h i).1)
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (zL : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, ∃ xr : ℝ, ∀ x (hx : Fm.x1 < x) (h : (sel Fm (d3_a hc)).1 ≤ x), xr ≤ x →
      ∀ (i : Fm.Ix x) (k : Fin (Fm.D x i).R.m),
        Function.Surjective (Formalism.L2.DIV.lPrj (Fm.D x i) (selP Fm (d3_a hc) x hx h i).1.A3.A (selP Fm (d3_a hc) x hx h i).1.P0
          (selP Fm (d3_a hc) x hx h i).1.ψ0 ((selP Fm (d3_a hc) x hx h i).1.A3.fam3.toSub2 (selP Fm (d3_a hc) x hx h i).1.Zs) k
          (selP Fm (d3_a hc) x hx h i).1.A3.A.μ0).mulVec), Closed (D3 3 𝒜) fun Fm _ => SmallLevelRankEq Fm := by
  intro 𝒜 sel selS selP selDH selC selB hPA hLamP hDivG zL
  have hDivR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3 (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps
        (selP Fm hc x hx h i).1.ψs (selP Fm hc x hx h i).1.Zs (selP Fm hc x hx h i).1.S0 (selP Fm hc x hx h i).1.S1 (Fm.ex x hx i).p0 (selP Fm hc x hx h i).1.C (selP Fm hc x hx h i).1.NuC (selP Fm hc x hx h i).1.I :=
    fun Fm hc x hx h i => (hDivG Fm hc x hx h i).toRows (_root_.Formalism.IndefR.LevelRealisationRankEquality.tup_all_used_of_realisation (selB Fm hc x hx h i).Q)
  have hZ : Closed (D3 3 𝒜) fun Fm _ => SmallLevelRankEq Fm :=
    closed_of_mem (zL.imp fun Fm _ _ h hc => by
      obtain ⟨xr, h⟩ := h hc
      exact _root_.Formalism.L2.N.RankZeroOfLevelThree.rank_zero_of_row_conditions_alt Fm (max (sel Fm (d3_a hc)).1 xr)
        (fun x hx h0 i => ((sel Fm (d3_a hc)).2 x hx (le_trans (le_max_left _ _) h0) i).T)
        (fun x hx h0 i => (selP Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i).1)
        (fun x hx h0 i => (selP Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i).2)
        (fun x hx h0 i => hLamP Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i)
        (fun x hx h0 i => hDivR Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i)
        (fun x hx h0 i => _root_.Formalism.L2.Top4.selP_condition_zero_of_primAll hPA Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i)
        (fun x hx h0 i => ⟨_, (selP Fm (d3_a hc) x hx (le_trans (le_max_left _ _) h0) i).1.tied.div.tup.mu0,
          h x hx (le_trans (le_max_left _ _) h0) (le_trans (le_max_right _ _) h0) i⟩))
  exact hZ
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkAltAltBis
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Top.link_alt_alt_bis : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (hWu : Formalism.L2.SG.Pf.WuDecayOfGap)
    (hRF : Formalism.L2.SG.RowsDef.RowsFinDim)
    (hTF : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3)
    (c30 : List ℝ → Formalism.MainNotions.S.CountingConstants)
    (hc30 : ∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A)
    (sTy : Formalism.L2.SG.RowsPos.TypeP)
    (sNG : Formalism.L2.SG.RowsPos.RowNGP)
    (sM : Formalism.L2.SG.RowsPos.RowMainEqP)
    (sLp : Formalism.L2.SG.ThmSOwn.LoopRowS 3 (D3 3 𝒜) (fun Fm hc => ⟨(sel Fm (d3_a hc)).1, fun x hx h i => (selS Fm (d3_a hc) x hx h i).toSTies⟩))
    (sO : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, Formalism.L2.SG.ThmSOwn.TheoremSSelected Fm 3
      ⟨(sel Fm (d3_a hc)).1, fun x hx h i => (selS Fm (d3_a hc) x hx h i).toSTies⟩)
    (h30 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.S.CountE.CountAllPointsClass Formalism.L2.SG.ThmSOwn.PLevT' Fm (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb)
    (hInstR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.VolSigIndep (Fm.D x i) ∧ Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassItemsAt (Fm.D x i) ((Fm.D x i).sp.Y 0).rank), Closed (D3 3 𝒜) fun Fm _ => TuSize Fm → LinkS Fm 3 := by
  intro 𝒜 sel selS hWu hRF hTF c30 hc30 sTy sNG sM sLp sO h30 hInstR
  have hC0 : (3 : ℝ) ≤ 3 := le_refl _
  have hC0' : (0 : ℝ) < 3 := by norm_num
  have hCe : Real.exp 1 ≤ 3 := le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hC0
  have sRes : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.S.ResidEv Fm := Formalism.L2.SG.ResidEvFree.residEv_closed_free (D3 3 𝒜)
  let ssel : Formalism.L2.SG.ThmSOwn.SSel (D3 3 𝒜) :=
    fun Fm hc => ⟨(sel Fm (d3_a hc)).1, fun x hx h i => (selS Fm (d3_a hc) x hx h i).toSTies⟩
  have lS := Formalism.L2.SG.ThmSOwn.theoremS_transport_link_zero (C0 := 3) (D3 3 𝒜) ssel hWu hRF
    (fun Fm hc x hx h i => (selS Fm (d3_a hc) x hx h i).locTied)
    (fun Fm hc x hx h i => Formalism.L2.SG.ThmSOwn.instTie_of_record (selS Fm (d3_a hc) x hx h i).inst
      (Formalism.MainNotions.RT.volTie_of_realTied _ ((sel Fm (d3_a hc)).2 x hx h i).T.theta.real) (hInstR Fm (d3_a hc) x hx h i).1
      (hInstR Fm (d3_a hc) x hx h i).2 (Fm.ties x i).cdScale_tie)
    (fun Fm hc x hx h i => Formalism.L2.SG.ThmSOwn.one_le_qqI_of_inst (selS Fm (d3_a hc) x hx h i).inst)
    hTF c30 (by linarith) hc30 sRes sTy sNG sM sLp sO h30
  exact lS
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkEta
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
theorem GlobalTheory.Top.closed_linkEta_of_duty : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm), Closed (D3 3 𝒜) fun Fm _ => LinkEta Fm := by
  intro 𝒜 sel _
  refine Closed.of_class fun Fm _ hc => ?_
  obtain ⟨x0, hx0⟩ := _root_.Formalism.L2.Top3.tied_families_of_choice_alt (sel Fm (d3_a hc))
  refine Formalism.L2.linkEta_closed Fm ⟨max x0 (Fm.x1 + 1), fun x hx i => ?_⟩
  have h1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hx)
  obtain ⟨T⟩ := hx0 x h1 ((le_max_left _ _).trans hx) i
  exact ⟨T.n.gal.mt, T.n.cover, T.n.gal.hecke⟩
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkEx
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Top.designExists_of_tuSize_aux4n_litThin : ∀ (𝒜 : FamClass)
    (cT : ℝ → ℝ → ℝ)
    (hEx : MinkDiv → DesignChoices (WithTw 𝒜) 3 cT)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm)
    (hTu : Closed (WithTw (WithSm (WithChN 𝒜))) fun {eps} Fm _ => cT eps Fm.CYL ≤ Fm.CTu → TuSize Fm)
    (hn4 : Closed (WithTw (WithSm (WithChN 𝒜))) fun Fm _ => ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
      StandardLattice.ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev)
    (hLit : LitThin), DesignExists (WithTw (WithSm (WithChN 𝒜))) 3 := by
  intro 𝒜 cT hEx sel hduty hTu hn4 hLit
  have hC0 : (3 : ℝ) ≤ 3 := le_refl _
  have hC0' : (0 : ℝ) < 3 := by norm_num
  have hCe : Real.exp 1 ≤ 3 := le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hC0
  have hRec : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → _root_.Formalism.L2.SecondLayerFamilyClass Fm := fun Fm hc =>
    _root_.Formalism.L2.Top3.layerTwoFamilyClass_of_linked_aligned (sel Fm hc) (_root_.Formalism.L2.Top3.linkedFamiliesAligned_of_duty (sel Fm hc) (hduty Fm hc))
  have hsub : ∀ {eps : ℝ} (Fm : FamP eps), WithTw (WithSm (WithChN 𝒜)) Fm → 𝒜 Fm := fun _ hc => hc.1.1.1
  have hProv : Closed (WithTw (WithSm (WithChN 𝒜))) fun Fm _ => ChosenProviso Fm 3 :=
    (hn4.and (Pk.Closed.sub _root_.Formalism.MainNotions.Ext.Lw.second_chern_linked_closed_rank_ties fun Fm hc => (hRec Fm (hsub Fm hc)).c2s)).imp
      fun Fm _ _ h => Formalism.MainNotions.StandardLattice.HarishChandraReduction.chosenProviso_min Fm 3 hCe h.1 h.2
  have hE' : DesignExists (WithTw (WithSm (WithChN 𝒜))) 3 :=
    designExists_of_choices (designChoices_upN (hEx minkowski_bound_rat)) hTu hProv
      (chosenThin_closed (WithTw (WithSm (WithChN 𝒜))) hLit)
  exact hE'
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkG
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Top.closed_linkG_of_duty : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm), Closed (D3 3 𝒜) fun Fm _ => LinkG Fm := by
  intro 𝒜 sel hduty
  have hRec : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → _root_.Formalism.L2.SecondLayerFamilyClass Fm := fun Fm hc =>
    _root_.Formalism.L2.Top3.layerTwoFamilyClass_of_linked_aligned (sel Fm hc) (_root_.Formalism.L2.Top3.linkedFamiliesAligned_of_duty (sel Fm hc) (hduty Fm hc))
  have hG2 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.G.Adm2F Fm :=
    Closed.of_class fun Fm _ hc => admissible_tops_mertens Fm (topsF_of_chosenE Fm hc.2.1.choose_spec)
  have hGt : Closed (D3 3 𝒜) fun Fm _ => Formalism.L2.G.GroupCompatibilityFamily Fm :=
    Closed.of_class fun Fm _ hc => _root_.Formalism.L2.group_compatibility_of_second_layer_family Fm (hRec Fm (d3_a hc))
  have lG := Formalism.L2.G.linkG_concrete5 (D3 3 𝒜) hGt hG2
  exact lG
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRows
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
namespace GlobalTheory.BigOn
theorem links2_of_rows_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D)
    (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz),
    p.PointConditions' → SingleIndexPlacesAreTwisted p → Links2 p := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hr hw
  obtain ⟨hU, hB, hR⟩ := _root_.GlobalTheory.T.l_unif_base_links_rank_of_pt_split D L hT Gi Gl Kc Y cX ex Csz p hr
  obtain ⟨hBar, hPin, hPh⟩ := _root_.GlobalTheory.T.bar_tie_om_pins_phase_tie_of_pt_split D L hT Gi Gl Kc Y cX ex Csz p hr
  exact ⟨GlobalTheory.T.char_R2_of_exAt_of_singleIndexPlacesTwisted D L hT Gi Gl Kc Y cX ex Csz p hr.exAt hw, hr.ok.ok2, hU, hB, hR, hBar, hPin, hPh⟩
end GlobalTheory.BigOn
end
end

