import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2155
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0084
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2156
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0097
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0106
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0096
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0580
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0571
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0562
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0070
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0091
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0182
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0065
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0955
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0039
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0089
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0054
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0069
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0578
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2158
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IntTieStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leafIntegrality_of_logDeriv_bound : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → BotSmall → BotNe → _root_.GlobalTheory.BigTop.Fun.LeafIntegrality @Comparison₂ := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.int_tie_alt | exact _root_.GlobalTheory.BigTop.Fun.int_tie_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.int_tie_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KerEqOfFormula
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
theorem ker_mulVecLin_eq_U_of_formulaAt {p : PtAt ex Csz} (hp : p.PointConditions') (hD : 0 < (Df p).dQ p.P.A3.fam3.base3.μ0)
    (hPq : Function.Surjective ((Df p).Pq p.P.A3.fam3.base3.μ0).mulVec)
    {CF : ℝ} (d : FunIn p CF) (a : SlopeTestRemainingChoices p d.G d.W d.n) (h : TieAt d a)
    (hI : ∀ u, (∀ i, psiK a.ch i u = 0) → u = 0) (hC : ∀ i j t, a.ch.c i j t ≠ 0)
    (hF : ∃ κ ze, FormulaAt a.ch κ ze) :
    LinearMap.ker (d.V p.P.A3.fam3.base3.μ0).mulVecLin = (Df p).U p.P.A3.fam3.base3.μ0 := by
  obtain ⟨κ, ze, hz, hf⟩ := hF
  have hc : cTot a.ch p.P.A3.fam3.base3.μ0 ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => hC i j _
  have hze : D.what₂.embLL (ze p.P.A3.fam3.base3.μ0) ≠ 0 := by
    obtain ⟨n, hn, e⟩ := hz p.P.A3.fam3.base3.μ0
    refine (map_ne_zero _).2 fun z => ?_
    rw [z, zero_pow hn.ne'] at e
    exact zero_ne_one e
  have hinj := (_root_.GlobalTheory.T.iC_iota_mulVec_eq_iC p hp).1
  have key : ∀ y, p.R.Th p.P.A3.fam3.base3.μ0 (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y)) = 0 ↔
      ((Df p).Pq p.P.A3.fam3.base3.μ0).mulVec y = 0 := by
    intro y
    have e := _root_.GlobalTheory.T.theta_j_ev0_eq_ic_pq p hp p.P.A3.fam3.base3.μ0 y
    change p.R.Th p.P.A3.fam3.base3.μ0 (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y)) = _ at e
    rw [e]
    constructor
    · intro h0
      have h1 := hinj (h0.trans (map_zero _).symm)
      funext i
      exact p.P.A3.fam3.base3.v0.embedding.injective (by simpa [cpt] using congrFun h1 i)
    · intro h0
      rw [h0]
      have : cpt p.P.A3.fam3.base3.v0.embedding (0 : Fin ((Df p).dQ p.P.A3.fam3.base3.μ0) → D.what₂.LL) = 0 := by
        funext i; simp [cpt]
      rw [this, map_zero]
      rfl
  have hκ : κ ≠ 0 := by
    obtain ⟨y, hy⟩ := hPq (Pi.single ⟨0, hD⟩ 1)
    have hne : p.R.Th p.P.A3.fam3.base3.μ0 (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y)) ≠ 0 := fun h0 => by
      have h2 := congrFun ((key y).1 h0) ⟨0, hD⟩
      rw [hy] at h2
      simp at h2
    obtain ⟨i, hi⟩ : ∃ i, psiK a.ch i (p.R.Th p.P.A3.fam3.base3.μ0
        (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y))) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hne (hI _ hall)
    exact FormulaAt.ne_zero ⟨hz, hf⟩ hc (_root_.GlobalTheory.T.eV0_mem_goodF' p hp _ y) hi
  ext y
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, DefSide.U]
  rw [← key y]
  constructor
  · intro h0
    apply hI
    intro i
    have e := hf p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y) (_root_.GlobalTheory.T.eV0_mem_goodF' p hp _ y) i
    have hs := h.sums p.P.A3.fam3.base3.μ0 (Or.inl rfl) y i
    have hv : vK a.ch p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y) i = 0 :=
      hs.symm.trans (by rw [h0]; exact map_zero _)
    have e2 := e.trans (by rw [hv, mul_zero])
    exact ((mul_eq_zero.1 e2).resolve_left (mul_ne_zero hze hc))
  · intro h0
    funext i
    have e := hf p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y) (_root_.GlobalTheory.T.eV0_mem_goodF' p hp _ y) i
    have hs := h.sums p.P.A3.fam3.base3.μ0 (Or.inl rfl) y i
    have hz0 : psiK a.ch i (p.R.Th p.P.A3.fam3.base3.μ0
        (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y))) = 0 := by
      rw [h0]; exact psiK_zero _ _
    rw [hz0, mul_zero, ← hs] at e
    have h3 := (mul_eq_zero.1 e.symm).resolve_left hκ
    exact D.what₂.embLL.injective (by rw [h3]; exact (map_zero _).symm)
theorem leafKernel_of_linK_injK_constK_formula2K : _root_.GlobalTheory.BigTop.Fun.BundleCondition → _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → LinK → InjK → ConstK → Formula2K → _root_.GlobalTheory.BigTop.Fun.LeafKernel @Comparison₂ := by
  intro hB hS _ hI hC hF
  obtain ⟨CF0, hA⟩ := hS.atPt (hI.and (hC.and hF))
  refine ⟨CF0, fun CF hCF => (hA CF hCF).imp fun Fm CH _ e _ => ⟨0, fun C _ => _root_.GlobalTheory.BigTop.Fun.evPt_mono e fun x hx i p hp b d hd => ?_⟩⟩
  obtain ⟨-, a, ha⟩ := hd
  obtain ⟨q1, q2, q3⟩ := b d.G d.W d.n a ha.ok
  obtain ⟨wf, R0, hR⟩ := hB p hp
  have h0 : 0 < (p.S false).D := hR ▸ R0.D_pos
  have v : d.O.vmu p.P.A3.fam3.base3.μ0 = d.V p.P.A3.fam3.base3.μ0 := by
    show (1 : _)⁻¹ • _ = _
    rw [inv_one]
    exact one_smul _ _
  show LinearMap.ker (d.O.vmu _).mulVecLin = _
  rw [v]
  exact _root_.GlobalTheory.BigTop.Fun.ker_mulVecLin_eq_U_of_formulaAt hp h0 (wf.Pq_surj _) d a ha q1 (fun i j t => (q2 i j t).2) (q3 ha.ok.field)
end GlobalTheory.BigTop.Fun
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticesFramesBasePointsExistStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_vector_relation_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀))) (o : TDat (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (_root_.GlobalTheory.Fam.pk_z W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, p = PP.under (𝓞 D.host.F)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (_root_.GlobalTheory.Fam.pk_z W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∃ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (b : ∀ j, GA D (Yc D j)) (dT : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) (M : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀) (β₀ : ∀ j ρ h i, GlobalTheory.FinPl.Frame (o.p i) (y.bes j ρ h).V₀ (Fin (D.sp.X j).rank ⊕ Fin 1)), ShapeOff { v with N := N, dT := dT, RamAd := o.Ram } { o with M := M, β₀ := β₀ } ∧ (∀ j, b j ∈ GfC (Yc D j) ∧ GlobalTheory.FinPl.CombAt (· ∈ v.tP) (dT j)) ∧ (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j) ∧ ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) → GlobalTheory.FinPl.Moves (Yc D j) (b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) (N j) P) ∧ ∀ PP h, Nonempty (LocY (l PP h) y N (_root_.GlobalTheory.Fam.pk_z W).βY b (bas PP h)) := by
  first | exact @_root_.GlobalTheory.Fam.lattices_frames_basePoints_exist_alt | exact _root_.GlobalTheory.Fam.lattices_frames_basePoints_exist_alt | (intros; apply _root_.GlobalTheory.Fam.lattices_frames_basePoints_exist_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevUIffInLevGStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_final_identity_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → ((y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U ↔ _root_.GlobalTheory.FamTrace.InLevelGroup a κ) := by
  first | exact @_root_.GlobalTheory.FamTrace.levU_iff_inLevG_alt | exact _root_.GlobalTheory.FamTrace.levU_iff_inLevG_alt | (intros; apply _root_.GlobalTheory.FamTrace.levU_iff_inLevG_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelEqUpInf
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped Pointwise in
theorem GlobalTheory.LevProd.level_eq_up_inf_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) g, g ∈ J.A.U j (J.ι j α) ↔ g ∈ _root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj ∧ ∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hT' j hj t J hJ α g
  have hle : ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ (α' : J'.Ch j),
      _root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α ≤ _root_.GlobalTheory.LevProd.relaxedLevelSubgroup J' j hj α' := by
    intro t J hJ α t' J' hJ' α' x hx
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨_root_.GlobalTheory.T.true_geometry_lattice_index_value_alt W hW u a ha hT' j hj t J hJ α t' J' hJ' α' x hx, ?_⟩, ?_⟩
    · exact (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2
    · exact (Subgroup.mem_pi _).2 fun i _ => _root_.GlobalTheory.T.true_geometry_lattice_index_step_alt W hW u a ha hT' j hj t J hJ α t' J' hJ' x hx i
  have hUp : _root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj = _root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α := by
    have hex : ∃ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.Reads ∧ Nonempty (J.Ch j) := ⟨t, J, hJ, ⟨α⟩⟩
    unfold _root_.GlobalTheory.LevProd.upperLevelSubgroup
    rw [dif_pos hex]
    exact le_antisymm (hle _ _ hex.choose_spec.choose_spec.1 _ _ _ hJ α) (hle _ _ hJ α _ _ hex.choose_spec.choose_spec.1 _)
  rw [hUp]
  have hN : (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J)).Normal := by
    unfold GlobalTheory.FinPl.grpAt GlobalTheory.FinPl.congGrp; exact MonoidHom.normal_ker _
  constructor
  · intro hg
    have hf := _root_.GlobalTheory.T.true_geometry_lattice_measure_value_alt W hW u a ha hT' j hj t J hJ α g hg
    refine ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left hg, ?_⟩, ?_⟩, hf⟩
    · exact ((hJ.is.U j (by omega) _ g).1 hg).1
    · exact (Subgroup.mem_pi _).2 fun i _ => _root_.GlobalTheory.T.true_geometry_lattice_measure_step_alt W hW u a ha hT' j hj t J hJ α i (hf i)
  · rintro ⟨hr, hH⟩
    have hs := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hr).1).1
    have : g ∈ ((J.A.U j (J.ι j α) : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) * (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J) : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)))) := by
      rw [← Subgroup.mul_normal]; exact hs
    obtain ⟨x, hx, n, hn, rfl⟩ := this
    have hn' : n ∈ J.A.U j (J.ι j α) := by
      refine _root_.GlobalTheory.T.true_geometry_lattice_conjugate_alt W hW u a ha hT' j hj t J hJ α n hn fun i => ?_
      have h1 := _root_.GlobalTheory.T.true_geometry_lattice_measure_value_alt W hW u a ha hT' j hj t J hJ α x hx i
      have h2 := hH i
      rw [map_mul, Pi.mul_apply] at h2
      simpa using (Subgroup.mul_mem_cancel_left _ h1).1 h2
    exact mul_mem hx hn'
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftPrincipal
section
set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TieLift
theorem lift_principal_alt : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ g0 : G0 (R2 p).Pg (Fm.D x i).R.r,
    ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc (Fm.D x i) j) ((R2 p).βW j) ((R2 p).datWp j (R2 p).triv) g0 κ' :=
  _root_.GlobalTheory.BigOn.Exp.TwistConditions.of_forall fun Fm x hx i p hr hm w hw j g0 =>
    GlobalTheory.GalLift.Transl.lifts (R2 p) j (_root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hr hm.1).1.lev g0
end GlobalTheory.TieLift
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkIrr
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Top.Irr
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.ConcNWeight Formalism.L2.GlobalTheoryTheory.AllJoin
end
section
open Formalism.BasicNotions Formalism.MainNotions
end
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
theorem closed_linkIRR_of_join_count : GlobalTheory.GLq.Green → ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (cIc : ℝ)
    (hcI : 0 < cIc)
    (irrC : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i),
      Formalism.MainNotions.ArithmeticCylinders.LabelCountGoodInjective A ∧ Formalism.L2.GlobalTheoryTheory.AllJoin.AllJoinA A ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.CountAllRows A (Formalism.L2.GlobalTheoryTheory.ConcN.epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f)), Closed (D3 3 𝒜) fun Fm _ => LinkIRR Fm := by
  intro hG 𝒜 sel cIc hcI irrC
  have irr : Closed (D3 3 𝒜) fun {eps} Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i),
      Formalism.MainNotions.ArithmeticCylinders.LabelCountGoodInjective A ∧ Formalism.L2.GlobalTheoryTheory.AllJoin.AllJoinA A ∧ Formalism.MainNotions.ArithmeticCylinders.admLq (Fm.D x i) ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.CountAllRows A (Formalism.L2.GlobalTheoryTheory.ConcN.epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f) ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.SizesRec (Fm.D x i) x Fm.ez 6 :=
    closed_of_mem (irrC.imp fun Fm _ _ H hc => by
      obtain ⟨x0, H⟩ := H
      refine ⟨max (max x0 (sel Fm (d3_a hc)).1) (max (Fm.x1 + 1) 4), fun x hx i => ?_⟩
      have h1 : Fm.x1 < x := by have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx; linarith
      have hs : (sel Fm (d3_a hc)).1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
      obtain ⟨A, a, b, c⟩ := H x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx) i
      exact ⟨A, a, b, GlobalTheory.Top.Lq.admissibleLabelWeights_of_greenCuspidalParametrisation hG _ _ ((sel Fm (d3_a hc)).2 x h1 hs i).T.n.types, c,
        sizesRec_at Fm h1 (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) i le_rfl⟩)
  exact (irr.and (closed_eps_le_one _)).imp fun Fm _ he ⟨h, h1⟩ =>
      linkIRR_of_join_ex _ 6 cIc he h1 hcI Fm h
end GlobalTheory.Top.Irr
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRowsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.links2_of_single_index_twisted : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.PointConditions' → SingleIndexPlacesAreTwisted p → Links2 p := by
  first | exact @_root_.GlobalTheory.BigOn.links2_of_rows_alt | exact _root_.GlobalTheory.BigOn.links2_of_rows_alt | (intros; apply _root_.GlobalTheory.BigOn.links2_of_rows_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainOfAltAlt
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
noncomputable section
namespace GlobalTheory.TheoremBQD
open MvPolynomial
theorem main_of_alt (hc : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (C : ℝ) (Qp : MvPolynomial (Fin 3) ℕ), 2080 ≤ C → (∀ f r t : ℕ, 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal Qp f r t) → EmbeddingTypeJumps.GlobalIndexAwayFromTypes r ρ → EmbeddingTypeJumps.admG1 r → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.admG3 r ρ → EmbeddingTypeJumps.admG4 r → EmbeddingTypeJumps.admG5 r → EmbeddingTypeJumps.admG6 r → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.KillingTwistedPlaces ρ → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → (∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.TameGeneratorConditions i) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → EmbeddingTypeJumps.Conclusion0 D ∧ EmbeddingTypeJumps.Conclusion1 D ∧ EmbeddingTypeJumps.Conclusion2 ρ large₂ C Qp) : ∃ (constantFirstHub : ℝ) (Q : MvPolynomial (Fin 3) ℕ), Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → EmbeddingTypeJumps.Conclusion2 X.ρ L constantFirstHub Q := by
  refine ⟨2080, polyB, ?_⟩
  intro hP D L P nch HW F Cm X C₂ hS
  have hb : (0 : ℝ) ≤ L.sc.b := (Real.exp_pos _).le
  have hX := _root_.GlobalTheory.T.split_bound_of_params_alt hP.font hP.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 hS.canon P
    (by have := hS.big; linarith) le_rfl (by simpa using hb) (hS.facts.admJ L hS.par) hS.par67 hS.facts.toCore.admA
    hS.facts.Conclusion1.1 hS.facts.Conclusion1.2.2 hS.facts.Conclusion2.1 hS.facts.Conclusion2.2.2 hS.facts.rhoBar hS.facts.large.2.1
    hS.facts.large.2.2 hS.facts.nct hS.facts.trip hS.facts.same hS.facts.block hS.facts.muUnr hS.facts.depthG
  have hSet := _root_.GlobalTheory.T.set_pt_of_setup_not_twisted hP D L P nch HW F Cm X C₂ hS
  have hpt : ∀ i, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, SetPt i (X.r i) (X.ρ i) π := fun i hi π hπ =>
    hSet i (GlobalTheory.AtQDTypes.l_not_mem_gset i hi.1.1) π hπ
  obtain ⟨ep, hep⟩ := (_root_.GlobalTheory.JumpStatement.holds_all_alt D L (hS.facts.admJ L hS.par)).1
  have hJ := _root_.GlobalTheory.T.hodgeJumpParameters_of_setup hP D L P nch HW F Cm X C₂ hS ep hep
  have hSt := GlobalTheory.T.lengthBound_of_rowConditions_and_dualityTheorems hP.artin hP.bk hP.tate hP.euler D (GlobalTheory.DesignUnconditional.main D hS.facts.large.2.2)
  have hN5 : EmbeddingTypeJumps.GlobalIndexAwayFromTypes X.r X.ρ := fun i π dc lenRow e' cB hA =>
    hSt.1 i (X.r i) (X.ρ i) π dc lenRow e' cB (hX.1 i) hA
  have hKill : EmbeddingTypeJumps.KillingTwistedPlaces X.ρ := by
    intro i hl htw _ π hπ
    have hk := hS.kill i htw
    have h2 := UpperTheory.KStar.nuL_eq_zero_of_qd D _ hl
    refine ⟨?_, ?_⟩
    · have := (hk.1 π hπ).2
      simpa [h2, TwistedPlaces.epsL, EmbeddingTypeJumps.epsL, one_div] using this
    · simpa [TwistedPlaces.epsL, EmbeddingTypeJumps.epsL, one_div, EmbeddingTypeJumps.vZeta] using hk.2
  refine (hc hP.artin hP.bk hP.tate hP.euler D HW F Cm X.r X.ρ L ep 2080 polyB le_rfl polyB_val hN5
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).1)
    (fun i hi π hπ => (hpt i hi π hπ).2.1)
    (fun i hi π hπ => (hpt i hi π hπ).2.2.1)
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).2.2.2.1)
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).2.2.2.2.1)
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).2.2.2.2.2.2.1)
    (fun i hi π hπ => by
      obtain ⟨-, -, -, -, -, -, -, -, hc1, hs1, hd1, he1, -⟩ := hpt i hi π hπ
      exact ⟨hc1, hs1, hd1, he1⟩)
    hKill hJ hX.2.2.1
    (fun i hi => by obtain ⟨π, hπ⟩ := exists_good hi; exact (hpt i hi π hπ).2.2.2.2.2.1)
    hS.par67).2.2
theorem main_alt_alt : ∃ (constantFirstHub : ℝ) (Q : MvPolynomial (Fin 3) ℕ), Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → EmbeddingTypeJumps.Conclusion2 X.ρ L constantFirstHub Q :=
  _root_.GlobalTheory.TheoremBQD.main_of_alt GlobalTheory.T.twistedPlace_selmerLengthBound_of_localDuality
end GlobalTheory.TheoremBQD
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedDatumEqStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_data_chain_step_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (o' : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) o' ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (· ∈ v.gP) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) ∧ (((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0 → comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) ≠ 0) ∧ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)) = κ • comb f.c.ψ _ _ (v.eG j) (comb f.c.ψ _ _ o' ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j))) := by
  first | exact @_root_.GlobalTheory.MidDatum.moved_datum_eq_alt | exact _root_.GlobalTheory.MidDatum.moved_datum_eq_alt | (intros; apply _root_.GlobalTheory.MidDatum.moved_datum_eq_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OneSqTieStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneSq_of_log_derivative_bound_and_oneSqSt : _root_.GlobalTheory.BigTop.Fun.SettingAtPoint → (Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → (_root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted @Comparison₂) fun p _ d _ _ => ThA d.G p.P.A3.A.μ0 p.R.mu) → OneSqSt → _root_.GlobalTheory.BigTop.Fun.LeafUniqueSquareRoot @Comparison₂ := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.oneSq_of_log_derivative_bound_thA | exact _root_.GlobalTheory.BigTop.Fun.oneSq_of_log_derivative_bound_thA | (intros; apply _root_.GlobalTheory.BigTop.Fun.oneSq_of_log_derivative_bound_thA <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PageSt
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn
namespace GlobalTheory.BigOn.PageNumbers
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L}
end GlobalTheory.BigOn.PageNumbers
namespace GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem pageSt_alt : _root_.GlobalTheory.BigOn.PageStatement := by
  refine (GlobalTheory.T.indexBoundParameterRequirements_eventually_family.and _root_.GlobalTheory.T.leafLevelSq_and_leafYBound).imp fun Fm CH _ H => ?_
  obtain ⟨⟨xs, hxs⟩, ⟨c1, hc1⟩⟩ := H
  refine ⟨max c1 1, fun c hc hB => ?_⟩
  obtain ⟨x2, hx2⟩ := hc1 c ((le_max_left _ _).trans hc) hB
  refine ⟨max (max xs x2) (3 * c.C), fun x hx hle i p hp hm r O hr => ?_⟩
  have hxs' : xs ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hle)
  have hx2' : x2 ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hle)
  have hxC : 3 * c.C ≤ x := (le_max_right _ _).trans hle
  have hR := hxs x hx hxs' i
  obtain ⟨hSq, hY⟩ := hx2 x hx hx2' i p hp hm r O hr
  have hE : ∀ C CH', ErrorConstantMatchesDefinition ((R2 p).num (F2 p) C CH') O C := fun C CH' => (GlobalTheory.BigOn.Check.twoRunDatum_boundUnit_at_indefinitePoint p (Fm.parT x hx i) r O hr C CH').1
  have hb : O.b = (Fm.L x i).sc.b := (GlobalTheory.BigOn.Check.twoRunDatum_boundUnit_at_indefinitePoint p (Fm.parT x hx i) r O hr 0 0).2
  obtain ⟨st, hd⟩ := hr.1.depth
  letI := st
  letI := hostAlg (Fm.D x i)
  have hd' : GlobalTheory.RunDepth.RunTie p.T.toCore (Fm.ex x hx i).errX (Fm.parT x hx i) (Fm.ex x hx i).kap_def ({ O with de2 := (Fm.L x i).de2 } : Obj p c)
      (fun j : Fin (Fm.D x i).R.m => (j : ℕ) + 1) := { hd with }
  have hN : GlobalTheory.IndexAssembly.NumTie (Fm.parT x hx i) (Fm.ex x hx i).kap_def ({ O with de2 := (Fm.L x i).de2 } : Obj p c) :=
    ⟨hr.1.rr_eq, hr.1.realisedChain_torus_eq, hr.1.Nc_eq,
      hr.1.DF_eq.trans (congrArg (fun n : ℕ => (n : ℝ)) (PageNumbers.sup_fin_eq_topDeg _ _)), rfl, hr.1.pde_eq⟩
  have hx3 : 3 * c.C ≤ (Fm.L x i).sc.x := by rw [Fm.L_x x i hx]; exact hxC
  have hC : Formalism.L2.Indef.Tree.OnPage.ConstC c := (le_max_right _ _).trans hc
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.IndexAssembly.numericLeaves hd' hN hR hC hB hx3
  refine ⟨h1, h2, h3, h4, hSq, hY, hb, ?_, hE⟩
  have hx0 : 0 < (Fm.L x i).sc.x := by linarith [(Fm.L x i).sc.one_lt_alt]
  have e1 := Real.rpow_pos_of_pos hx0 (Fm.L x i).sc.eps
  have e2 := Real.rpow_pos_of_pos hx0 (-(Fm.L x i).sc.eps)
  change 0 ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps * (((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b *
    (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps + (Fm.L x i).Nc)
  have hb0 : 0 < (Fm.L x i).sc.b := Real.exp_pos _
  unfold SizeData₂.Nc budgetNc rankBudget bSize
  positivity
end GlobalTheory.BigOn
end
end
end

