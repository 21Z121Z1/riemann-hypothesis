import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0341
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0144
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0343
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentEVMemLevel
section
noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

namespace GlobalTheory.MiTop

theorem descent_eV_mem_level : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), BotHyp W → LevHyp W → (∀ t F, (cxW W).Θ t ((cxW W).jR t (W.Q.F.eV (cxW W).zs t F)) ∈ (cxW W).EEl true) := by
  intro D L hT Gi Gl Kc Yd cX ex W hB hLv t F
  obtain ⟨-, -, -, hC, -⟩ := hB.hyp
  obtain ⟨⟨s, hs⟩, hRZ, gE, hU, hG, h2, hl0, hl1⟩ := hLv
  have hK := RealDat3.kFormR_of (R := W.Q.Rl) (F := W.Q.F) hC.models
  have hJ := RealDat3.jIsoR_of (R := W.Q.Rl) (F := W.Q.F) hC.models
  have hDn := Formalism.IndefR.CxPass.descent_of_types hs hK hJ hRZ hU hG h2 hl0 hl1 true
  have hE := Formalism.IndefR.Links.EvTie.evTie_real ⟨s, hs⟩ W.Q.Rl W.Q.F
  have hV : (cxW W).jR t (W.Q.F.eV (cxW W).zs t F) ∈ (cxW W).V0C W.Q.F.cv true t :=
    Submodule.subset_span ⟨_, hE.1 t F, rfl⟩
  exact hDn t (Submodule.mem_map_of_mem hV)

end GlobalTheory.MiTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentTopSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.TopVac

section Fam

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)

theorem isWeil_top (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : ∃ χS χT, IsWeilDatumO (pk W).ψ (Yc D (j + 1)) D.sp.X' χS χT
    (omT (pk W) W.P.A3.A.μ0 j h) := by
  have hω := W.Q.charW.base.chain.ωX W.P.A3.A.μ0
  have key : ∀ n (e : D.R.m - 1 = n), IsWeilDatumO (pk W).ψ (Yc D n) D.sp.X'
      (Lift.chrStep ((pk W).toLevCh.mu W.P.A3.A.μ0) (pk W).eta D.R.m).1
      (Lift.chrStep ((pk W).toLevCh.mu W.P.A3.A.μ0) (pk W).eta D.R.m).2
      (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((pk W).ωX W.P.A3.A.μ0) e) := by
    intro n e
    subst e
    exact hω
  exact ⟨_, _, key _ (GlobalTheory.Fam.idx_top h)⟩

end Fam

theorem moved_vacuum : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ j (h : j + 2 * 0 + 2 = D.R.m) d₀, IsDG W (j + 1) (pk W).MX (pk W).ΛX (pk W).βX (vacT (pk W) j h) d₀ → IsSelfDualC (Yc D (j + 1)) ((pk W).ΛY (j + 1)) ∧ IsSelfDualC D.sp.X' (pk W).ΛX ∧ ∃ M : GlobalTheory.FinPl.Lat (Yc D (j + 1)), IsSelfDualC (Yc D (j + 1)) M ∧ (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((pk W).ΛY (j + 1)) M P) ∧ GlobalTheory.FinPl.Vac f.c.ψ (Yc D (j + 1)) D.sp.X' M f.g.LT (fun _ => True) (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk _ v hv hVT j h d₀ hd₀
  have hLev := hPk.bot.hyp.2.2.2.1.lev
  have sdY : IsSelfDualC (Yc D (j + 1)) ((pk W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY (j + 1) (by omega))
  have sdX : IsSelfDualC D.sp.X' (pk W).ΛX := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hLev.βX
  obtain ⟨M, hM, hmov⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D _ _ sdY).1 (f.g.b (j + 1))
  obtain ⟨χS, χT, hWe⟩ := isWeil_top W j h
  have sdT : IsSelfDualC D.sp.X' f.g.LT := hVT.bT.2 ▸ hv.sdT
  refine ⟨sdY, sdX, M, hM, hmov, ?_⟩
  exact GlobalTheory.VacMove.vac_of_moves D (pk W).ψ _ _ χS χT _ hWe _ _ sdY sdX _ _ ⟨hd₀.2.1.2.theta, hd₀.2.1.2.lat⟩ _ _ M f.g.LT hM sdT
    (hmov _) (hVT.movesT _)

end GlobalTheory.TopVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightFunProperties
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP
variable {D : D7} (A : HSp D) (L : Lat A) (a : GL (Fin A.rank) (AE D))

theorem hgtL_eq_prod (hL : IsSelfDualC A L) (ha : IsMaj A a) (g : GA D A) : hgtL A L a g = (∏ w, hgtArch D.sp.cm.sig (dblSp A).gram w (Formalism.UG.bc (compInf _ _ w) a)
      (ioH _ D.sp.cm.sig (gram_hdbl A) (projArch D.sp.cm.sig A.gram w g, 1))) *
      ∏ᶠ v, hgtFin D.sp.cm.sig (dblSp A).gram L v (ioH _ D.sp.cm.sig (gram_hdbl A) (proj D.sp.cm.sig A.gram v g, 1)) := by
  haveI : Submodule.IsLattice D.host.E L := hL.1
  have hI := GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A L a hL ha
  rw [hgtL, hI.hgtAd_eq (isCMExt_host D)]
  simp only [io, proj_ioH, projArch_ioH, map_one]

theorem isOpen_openOff (hL : IsSelfDualC A L) (Sf : Finset (FinPl D)) : IsOpen (openOff A L Sf) := by
  haveI : Submodule.IsLattice D.host.E L := hL.1
  let H : Subgroup (GA D A) := ⨅ (v) (_ : v ∉ Sf), (stabLoc D.sp.cm.sig A.gram L v).comap (proj D.sp.cm.sig A.gram v)
  have hH : (H : Set (GA D A)) = openOff A L Sf := by
    ext g
    simp [H, openOff, Subgroup.mem_iInf, Subgroup.mem_comap]
  rw [← hH]
  refine Subgroup.isOpen_mono (H₁ := levelOpen D.sp.cm.sig A.gram L) (fun g hg => ?_) (isOpen_levelOpen _ _ _)
  simp only [H, Subgroup.mem_iInf, Subgroup.mem_comap]
  exact fun v _ => (mem_levelOpen.1 hg) v

theorem continuous_hgtL (hL : IsSelfDualC A L) (ha : IsMaj A a) : Continuous (hgtL A L a) := by
  haveI : Submodule.IsLattice D.host.E L := hL.1
  haveI := t2Space_adeleRing' (F := D.host.F)
  have hI := GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A L a hL ha
  show Continuous fun g => hgtAd D.sp.cm.sig (dblSp A).gram L a (io A (g, 1))
  exact (hI.continuous_hgtH continuous_absE (isCompact_KAd (isCMExt_host D))).comp
    ((continuous_io A).comp (continuous_id.prodMk continuous_const))

theorem hgtL_le_one (hL : IsSelfDualC A L) (ha : IsMaj A a) (g : GA D A) : hgtL A L a g ≤ 1 := by
  rw [hgtL_eq_prod A L a hL ha g]
  refine mul_le_one' (Finset.prod_le_one' fun w _ => ?_) ?_
  · have := GlobalTheory.T.doublingHeightAtRealPlace_le_one D A a ha w (projArch D.sp.cm.sig A.gram w g)
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW] using this
  · by_cases hf : (Function.mulSupport fun v => hgtFin D.sp.cm.sig (dblSp A).gram L v
        (ioH _ D.sp.cm.sig (gram_hdbl A) (proj D.sp.cm.sig A.gram v g, 1))).Finite
    · rw [finprod_eq_prod _ hf]
      exact Finset.prod_le_one' fun v _ => GlobalTheory.T.siegelHeightFinitePlace_doublingEmbedding_le_one D A L hL v _
    · rw [finprod_of_infinite_mulSupport hf]

theorem hgtL_eq_prod_off (hL : IsSelfDualC A L) (ha : IsMaj A a) (Sf : Finset (FinPl D)) (g : GA D A)
    (hg : g ∈ openOff A L Sf) : (hgtL A L a g : ℝ) = (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW A a w (projArch D.sp.cm.sig A.gram w g)) *
      ∏ v ∈ Sf, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v (proj D.sp.cm.sig A.gram v g) := by
  haveI : Submodule.IsLattice D.host.E L := hL.1
  rw [hgtL_eq_prod A L a hL ha g]
  have hsub : (Function.mulSupport fun v => hgtFin D.sp.cm.sig (dblSp A).gram L v
      (ioH _ D.sp.cm.sig (gram_hdbl A) (proj D.sp.cm.sig A.gram v g, 1))) ⊆ (Sf : Set (FinPl D)) := by
    intro v hv
    by_contra hvS
    exact hv (hgtH_of_mem (continuous_absEv v) (isCompact_KFin v)
      ((ioH_mem_KFin (gram_hdbl A)).2 ⟨hg v hvS, one_mem _⟩))
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  push_cast
  rfl

theorem hgtL_props : ∀ (D : D7) (A : HSp D) (L : Lat A) (a : GL (Fin A.rank) (AE D)), IsSelfDualC A L → IsMaj A a → Continuous (hgtL A L a) ∧ (∀ g, 0 < hgtL A L a g ∧ hgtL A L a g ≤ 1) ∧ ∀ (Sf : Finset (FinPl D)), IsOpen (openOff A L Sf) ∧ ∀ g ∈ openOff A L Sf, (hgtL A L a g : ℝ) = (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW A a w (projArch D.sp.cm.sig A.gram w g)) * ∏ v ∈ Sf, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v (proj D.sp.cm.sig A.gram v g) := by
  intro D A L a hL ha
  exact ⟨continuous_hgtL A L a hL ha, fun g => ⟨hgtH_pos _, hgtL_le_one A L a hL ha g⟩,
    fun Sf => ⟨isOpen_openOff A L hL Sf, fun g hg => hgtL_eq_prod_off A L a hL ha Sf g hg⟩⟩

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSmulOfUnitaryEquivariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.BranchMultOne

def blkMat (N n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => if hi : i.1 < n then (if hj : j.1 < n then h ⟨i.1, hi⟩ ⟨j.1, hj⟩ else 0)
    else (if j.1 < n then 0 else 1)

def blkPoly (N n : ℕ) (v : Fin N × Fin N) : MvPolynomial (Fin n × Fin n) ℂ :=
  if hi : v.1.1 < n then (if hj : v.2.1 < n then MvPolynomial.X (⟨v.1.1, hi⟩, ⟨v.2.1, hj⟩) else 0)
    else (if v.2.1 < n then 0 else 1)

theorem eval_blkPoly (N n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) (v : Fin N × Fin N) :
    MvPolynomial.eval (fun x : Fin n × Fin n => h x.1 x.2) (blkPoly N n v) = blkMat N n h v.1 v.2 := by
  simp only [blkPoly, blkMat, Matrix.of_apply]
  split_ifs <;> simp_all

theorem isBlock_blkMat {N n : ℕ} (hN : N = n + 1) (h : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.BranchFormula.IsBlock hN (blkMat N n h) h 1 := by
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩ <;>
    simp [blkMat, Formalism.L2.Col.Br.iC, Formalism.L2.Col.Br.iL]

theorem eq_blkMat_of_isBlock {N n : ℕ} (hN : N = n + 1) {kt : Matrix (Fin N) (Fin N) ℂ}
    {k : Matrix (Fin n) (Fin n) ℂ} (H : GlobalTheory.BranchFormula.IsBlock hN kt k 1) : kt = blkMat N n k := by
  ext i j
  simp only [blkMat, Matrix.of_apply]
  by_cases hi : i.1 < n <;> by_cases hj : j.1 < n
  · rw [dif_pos hi, dif_pos hj]
    have := H.1 ⟨i.1, hi⟩ ⟨j.1, hj⟩
    simpa [Formalism.L2.Col.Br.iC] using this
  · rw [dif_pos hi, dif_neg hj]
    have ej : j = Formalism.L2.Col.Br.iL hN := Fin.ext (by simp [Formalism.L2.Col.Br.iL]; omega)
    have := (H.2.1 ⟨i.1, hi⟩).1
    rw [ej]
    simpa [Formalism.L2.Col.Br.iC] using this
  · rw [dif_neg hi, if_pos hj]
    have ei : i = Formalism.L2.Col.Br.iL hN := Fin.ext (by simp [Formalism.L2.Col.Br.iL]; omega)
    have := (H.2.1 ⟨j.1, hj⟩).2
    rw [ei]
    simpa [Formalism.L2.Col.Br.iC] using this
  · rw [dif_neg hi, if_neg hj]
    have ei : i = Formalism.L2.Col.Br.iL hN := Fin.ext (by simp [Formalism.L2.Col.Br.iL]; omega)
    have ej : j = Formalism.L2.Col.Br.iL hN := Fin.ext (by simp [Formalism.L2.Col.Br.iL]; omega)
    rw [ei, ej]
    exact H.2.2

theorem pow_toNat_eq (x : ℂ) (hx : x ≠ 0) (c m : ℤ) (hc : 0 ≤ c + m) :
    x ^ (c + m).toNat = x ^ m * x ^ c := by
  rw [← zpow_natCast, Int.toNat_of_nonneg hc, zpow_add₀ hx, mul_comm]

theorem det_eval_mvPolynomialX (n : ℕ) (h : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial.eval (fun x : Fin n × Fin n => h x.1 x.2) (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det = h.det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.mvPolynomialX]

theorem det_ne_zero_of_unitary {n : ℕ} {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    u.det ≠ 0 := by
  have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 hu)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact right_ne_zero_of_mul_eq_one h

end GlobalTheory.BranchMultOne

namespace GlobalTheory.BranchMultOne

open Formalism.BasicNotions

theorem unitary_to_all {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n)
    (u : delSq ℂ N lam →ₗ[ℂ] delSq ℂ n sg)
    (E : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ)
    (hE : ∀ f : delSq ℂ N lam, E f.1 = (u f).1)
    (hu : ∀ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ kt : Matrix (Fin N) (Fin N) ℂ, GlobalTheory.BranchFormula.IsBlock hN kt k 1 →
      ∀ f f' : delSq ℂ N lam, f'.1 = Formalism.GradedWeylDivisibility.rowAct ℂ kt f.1 →
        k.det ^ lam.detShift • (u f').1 = k.det ^ sg.detShift • Formalism.GradedWeylDivisibility.rowAct ℂ k (u f).1)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : g.det ≠ 0) (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ∈ delSq ℂ N lam) :
    g.det ^ lam.detShift • E (Formalism.GradedWeylDivisibility.rowAct ℂ (blkMat N n g) f) =
      g.det ^ sg.detShift • Formalism.GradedWeylDivisibility.rowAct ℂ g (E f) := by
  set a := lam.detShift
  set b := sg.detShift
  set m : ℤ := |a| + |b|
  have ha : 0 ≤ a + m := by
    have := neg_abs_le a; have := abs_nonneg b; omega
  have hb : 0 ≤ b + m := by
    have := neg_abs_le b; have := abs_nonneg a; omega
  have poly : ∀ g' : Matrix (Fin n) (Fin n) ℂ,
      g'.det ^ (a + m).toNat • E (Formalism.GradedWeylDivisibility.rowAct ℂ (blkMat N n g') f) =
        g'.det ^ (b + m).toNat • Formalism.GradedWeylDivisibility.rowAct ℂ g' (E f) := by
    intro g'
    rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_
    obtain ⟨P₁, hP₁⟩ := GlobalTheory.Branching.exists_poly_rowAct_coef N N f (l ∘ₗ E)
    obtain ⟨P₂, hP₂⟩ := GlobalTheory.Branching.exists_poly_rowAct_coef n n (E f) l
    let D := (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det
    let Q := D ^ (a + m).toNat * MvPolynomial.bind₁ (blkPoly N n) P₁ - D ^ (b + m).toNat * P₂
    have hQ : ∀ h : Matrix (Fin n) (Fin n) ℂ, MvPolynomial.eval (fun x => h x.1 x.2) Q =
        l (h.det ^ (a + m).toNat • E (Formalism.GradedWeylDivisibility.rowAct ℂ (blkMat N n h) f) -
          h.det ^ (b + m).toNat • Formalism.GradedWeylDivisibility.rowAct ℂ h (E f)) := by
      intro h
      have hbind : MvPolynomial.eval (fun x : Fin n × Fin n => h x.1 x.2) (MvPolynomial.bind₁ (blkPoly N n) P₁) =
          MvPolynomial.eval (fun v => MvPolynomial.eval (fun x : Fin n × Fin n => h x.1 x.2) (blkPoly N n v)) P₁ :=
        MvPolynomial.eval₂Hom_bind₁ _ _ _ P₁
      simp only [Q, D, map_sub, map_mul, map_pow, det_eval_mvPolynomialX, map_smul, smul_eq_mul, hbind, eval_blkPoly]
      rw [← hP₁ (blkMat N n h), ← hP₂ h]
      rfl
    have Q0 : Q = 0 := by
      refine GlobalTheory.Branching.eq_zero_of_vanish_unitaryGroup n Q fun v hv => ?_
      rw [hQ]
      have hv0 := det_ne_zero_of_unitary hv
      have key := hu v hv (blkMat N n v) (isBlock_blkMat hN v) ⟨f, hf⟩
        ⟨Formalism.GradedWeylDivisibility.rowAct ℂ (blkMat N n v) f, GlobalTheory.ValueSpaceCoordinates.rowAct_mem_delSq lam _ f hf⟩ rfl
      rw [← hE, ← hE] at key
      rw [pow_toNat_eq _ hv0 a m ha, pow_toNat_eq _ hv0 b m hb, mul_smul, mul_smul, ← smul_sub]
      simp only at key
      rw [key, sub_self, smul_zero, map_zero]
    have := hQ g'
    rw [Q0, map_zero] at this
    exact this.symm
  have h := poly g
  rw [pow_toNat_eq _ hg a m ha, pow_toNat_eq _ hg b m hb, mul_smul, mul_smul] at h
  exact smul_right_injective _ (zpow_ne_zero m hg) h

end GlobalTheory.BranchMultOne

namespace GlobalTheory.BranchMultOne

theorem eq_smul_of_unitary_equivariant : ∀ (N n : ℕ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n), Formalism.L2.Col.Br.Interlace hN lam sg → ∀ t t₀ : delSq ℂ N lam →ₗ[ℂ] delSq ℂ n sg, (∀ s, s = t ∨ s = t₀ → ∀ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ kt : Matrix (Fin N) (Fin N) ℂ, GlobalTheory.BranchFormula.IsBlock hN kt k 1 → ∀ f f' : delSq ℂ N lam, f'.1 = Formalism.GradedWeylDivisibility.rowAct ℂ kt f.1 → k.det ^ lam.detShift • (s f').1 = k.det ^ sg.detShift • Formalism.GradedWeylDivisibility.rowAct ℂ k (s f).1) → t₀ ≠ 0 → ∃ c : ℂ, t = c • t₀ := by
  intro N n hN lam sg hI t t₀ H h0
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (delSq ℂ N lam)
  let π := (delSq ℂ N lam).linearProjOfIsCompl C hC
  let E : (delSq ℂ N lam →ₗ[ℂ] delSq ℂ n sg) → MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    fun u => (delSq ℂ n sg).subtype ∘ₗ u ∘ₗ π
  have hE : ∀ u (f : delSq ℂ N lam), E u f.1 = (u f).1 := fun u f => by
    show (u (π f.1)).1 = (u f).1
    exact congrArg (fun x => (u x).1) (Submodule.linearProjOfIsCompl_apply_left hC f)
  have hN' : Formalism.BasicNotions.nablaSq ℂ N lam = delSq ℂ N lam := Formalism.L2.Col.nablaSq_eq_delSq ℂ lam
  have hn' : Formalism.BasicNotions.nablaSq ℂ n sg = delSq ℂ n sg := Formalism.L2.Col.nablaSq_eq_delSq ℂ sg
  have key : ∀ s, s = E t ∨ s = E t₀ → (∀ f ∈ Formalism.BasicNotions.nablaSq ℂ N lam, s f ∈ Formalism.BasicNotions.nablaSq ℂ n sg) ∧
      ∀ (g : GL (Fin n) ℂ), ∀ f ∈ Formalism.BasicNotions.nablaSq ℂ N lam,
        s (Formalism.BasicNotions.sqAct ℂ N lam (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm g) f) = Formalism.BasicNotions.sqAct ℂ n sg g (s f) := by
    intro s hs
    obtain ⟨u, hu, rfl⟩ : ∃ u, (u = t ∨ u = t₀) ∧ s = E u := by
      rcases hs with hs | hs
      · exact ⟨t, Or.inl rfl, hs⟩
      · exact ⟨t₀, Or.inr rfl, hs⟩
    refine ⟨fun f hf => ?_, fun g f hf => ?_⟩
    · rw [hN'] at hf
      rw [hn', hE u ⟨f, hf⟩]
      exact (u _).2
    · rw [hN'] at hf
      have hb := (GlobalTheory.BranchFormula.isBlock_embGL ℂ hN g).transpose
      have hdet : (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm g : Matrix (Fin N) (Fin N) ℂ).det =
          (g : Matrix (Fin n) (Fin n) ℂ).det := by
        rw [(GlobalTheory.BranchFormula.isBlock_embGL ℂ hN g).det, mul_one]
      have hg0 : (g : Matrix (Fin n) (Fin n) ℂ).transpose.det ≠ 0 := by
        rw [Matrix.det_transpose]
        have := (Matrix.GeneralLinearGroup.det g).ne_zero
        rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
      have main := unitary_to_all hN lam sg u (E u) (hE u) (H u hu) _ hg0 f hf
      rw [← eq_blkMat_of_isBlock hN hb, Matrix.det_transpose] at main
      simp only [Formalism.BasicNotions.sqAct, Formalism.BasicNotions.detPow, map_smul, Units.val_zpow_eq_zpow_val,
        Matrix.GeneralLinearGroup.val_det_apply, hdet]
      exact main
  have hne : ∃ f ∈ Formalism.BasicNotions.nablaSq ℂ N lam, E t₀ f ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply h0
    refine LinearMap.ext fun f => Subtype.ext ?_
    have := hc f.1 (by rw [hN']; exact f.2)
    rw [hE] at this
    simpa using this
  obtain ⟨c, hc⟩ := GlobalTheory.Branching.equivariant_map_eq_smul n N hN.symm lam sg
    ((GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.interlace_iff hN lam sg).1 hI) (E t) (E t₀) key hne
  refine ⟨c, LinearMap.ext fun f => Subtype.ext ?_⟩
  have := hc f.1 (by rw [hN']; exact f.2)
  rw [hE, hE] at this
  simpa using this

end GlobalTheory.BranchMultOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBoxFinitePosProductHaarUnitaryGroups
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem haar_box_prod_finite_pos : ∀ (ι : Type) [Fintype ι] (p q : ι → ℕ) (m : ∀ i, Measure (UpqT (p i) (q i))), (∀ i, (m i).IsHaarMeasure) → ∃ B : ∀ i, Set (UpqT (p i) (q i)), (∀ i, MeasurableSet (B i)) ∧ ∏ i, m i (B i) ≠ 0 ∧ ∏ i, m i (B i) ≠ ⊤ := by
  intro ι _ p q m hm
  have hK : ∀ i, ∃ K : Set (UpqT (p i) (q i)), IsCompact K ∧ K ∈ nhds (1 : UpqT (p i) (q i)) :=
    fun i => exists_compact_mem_nhds 1
  choose K hKc hKn using hK
  refine ⟨fun i => interior (K i), fun i => isOpen_interior.measurableSet, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro i _
    exact (isOpen_interior.measure_pos (m i) ⟨1, mem_interior_iff_mem_nhds.mpr (hKn i)⟩).ne'
  · apply ENNReal.prod_ne_top
    intro i _
    exact (lt_of_le_of_lt (measure_mono interior_subset) (hKc i).measure_lt_top).ne

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdelicConjSelfDualDoublingCompactStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelic_conj_selfDual_doublingCompact : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' → ∃ k ∈ GfC A, ∀ (a : GL (Fin A.rank) (AE D)) (x : GA D (dblSp A)), x ∈ KAd D.sp.cm.sig (dblSp A).gram L' a ↔ (io A (k, k))⁻¹ * x * io A (k, k) ∈ KAd D.sp.cm.sig (dblSp A).gram L a := by
  first | exact @GlobalTheory.Core.Rk.LatMove.exists_conj_KAd_of_selfDual | exact GlobalTheory.Core.Rk.LatMove.exists_conj_KAd_of_selfDual | (intros; apply GlobalTheory.Core.Rk.LatMove.exists_conj_KAd_of_selfDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHaarAdelicUnitaryProductRealFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdelicHaarProd

theorem haar_prod : ∀ (D : D7) (V : HSp D) (μf : Measure (GfC V)), μf.IsHaarMeasure → ∃ (μR : Measure (GA D V)) (μi : Measure (GinfC V)), μR.IsHaarMeasure ∧ ∀ (S : Set (GinfC V)) (E : Set (GfC V)), μR {h | ∃ a ∈ S, ∃ k ∈ E, h = (a : GA D V) * k} = μi S * μf E := by
  intro D V μf hμf
  obtain ⟨hLC, hSC, hT2, hB, hTG, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hi := GlobalTheory.AdelicSplit.isClosed_GinfC' V
  have hf := GlobalTheory.AdelicSplit.isClosed_GfC' V
  haveI : LocallyCompactSpace (GinfC V) := hi.locallyCompactSpace
  haveI : LocallyCompactSpace (GfC V) := hf.locallyCompactSpace
  let e := GlobalTheory.AdelicSplit.splitEquiv V
  let μi : Measure (GinfC V) := Measure.haar
  haveI : SFinite μf := inferInstance
  refine ⟨Measure.map e (μi.prod μf), μi, ContinuousMulEquiv.isHaarMeasure_map _ e, fun S E => ?_⟩
  have hset : {h : GA D V | ∃ a ∈ S, ∃ k ∈ E, h = (a : GA D V) * k} = e '' (S ×ˢ E) := by
    ext h
    constructor
    · rintro ⟨a, ha, k, hk, rfl⟩
      exact ⟨(a, k), ⟨ha, hk⟩, rfl⟩
    · rintro ⟨p, ⟨ha, hk⟩, rfl⟩
      exact ⟨p.1, ha, p.2, hk, rfl⟩
  rw [hset]
  rw [show (Measure.map e (μi.prod μf)) = Measure.map (e.toHomeomorph.toMeasurableEquiv) (μi.prod μf) from rfl]
  rw [MeasurableEquiv.map_apply]
  rw [show (e.toHomeomorph.toMeasurableEquiv) ⁻¹' (e '' (S ×ˢ E)) = S ×ˢ E from e.toEquiv.preimage_image _]
  exact Measure.prod_prod S E

end GlobalTheory.AdelicHaarProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalMatrixOfMemPeriodLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.LamPre

theorem exists_mat_of_mem_lamC : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), ∀ x ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N', ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' ∧ embH (tauE D) δ (toHom S T hS hT γ) = x ∧ ∃ v, GlobalTheory.AdTh.IsFinOf S T γ v := by
  intro D S T a b hS hT δ N N' x hx
  obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 hx
  refine ⟨(LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm, ?_, ?_, ?_⟩
  · have e : toHom S T hS hT ((LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm) = y := by
      unfold toHom
      rw [show ((LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm).reindex (finCongr hT) (finCongr hS)
          = LinearMap.toMatrix' y from by ext i j; simp, Matrix.toLin'_toMatrix']
    rw [e]; exact hy
  · have e : toHom S T hS hT ((LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm) = y := by
      unfold toHom
      rw [show ((LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm).reindex (finCongr hT) (finCongr hS)
          = LinearMap.toMatrix' y from by ext i j; simp, Matrix.toLin'_toMatrix']
    rw [e]
  · exact ⟨GlobalTheory.VacUnique.finRat S T _, GlobalTheory.VacUnique.finRat_inf S T _, GlobalTheory.VacUnique.finRat_fin S T _⟩

end GlobalTheory.AdForm.LamPre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceGeometryExtensionCosetOrbitRepsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlaceGeometryExtension_cosetOrbitReps : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (PP : Formalism.L2.DIV.Pl D.host.E) (G : QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle), c.Is → ∀ (δ : G.kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → G.kˣ →* ℂˣ), (∀ j, IsUnram (η j)) → (∀ j, j ≤ G.s + 1 → (ofSplit G.q).IsComp (χ j)⁻¹ (η (j + 1) * δ)) → ∀ A, (G.T δ hδ η).IsRepSystem A G.ψk G.ν → ∀ M : ℕ, (G.T δ hδ η).Adapted A (box _ (G.ϖ ^ M)⁻¹) (box _ (G.ϖ ^ M)) → ∀ (C : Type) [Fintype C] (cs : C → XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) → G.k), (∀ y y', SameOrb ((G.T δ hδ η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ M)) (Submodule.Quotient.mk (cs y)) (Submodule.Quotient.mk (cs y')) → y = y') → (∀ z ∈ box (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1)) (G.ϖ ^ M)⁻¹, ∃ y, SameOrb ((G.T δ hδ η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ M)) (Submodule.Quotient.mk (cs y)) (Submodule.Quotient.mk z)) → ∃ E : QExt G χ, E.δ = δ ∧ E.η = η ∧ E.A = A ∧ E.M = M ∧ (∃ e : C ≃ E.Ch (G.s + 1), ∀ y, E.cos (e y) = Submodule.Quotient.mk (cs y)) ∧ ∀ j, G.s + 1 + 1 < j → Nonempty (Unique (E.Ch j)) := by
  first | exact @GlobalTheory.QTw.CosExt.exists_qExt_cos | exact GlobalTheory.QTw.CosExt.exists_qExt_cos | (intros; apply GlobalTheory.QTw.CosExt.exists_qExt_cos <;> assumption)
end

