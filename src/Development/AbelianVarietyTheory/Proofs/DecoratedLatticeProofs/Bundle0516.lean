import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastTwoStepsDoubleLiftPeriodEqIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0417
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0405
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0507
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeHyperbolicLineIdealsAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormCoprimeOfSup
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0352
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0500
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0506
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0494

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDoubleThetaLiftIntegrableLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastDbl

variable {D : D7}

theorem ker_smul {A S X : HSp D} (oma : Om A S) (omX : Om S X) (a : ℂ) (C : WO A S → WO S X → ℂ) (h₀ : GA D A)
    (h₁ : GA D S) (h₂ : GA D X) :
    GlobalTheory.SeeSmallPf.ker oma omX (a • C) h₀ h₁ h₂ = a * GlobalTheory.SeeSmallPf.ker oma omX C h₀ h₁ h₂ := by
  unfold GlobalTheory.SeeSmallPf.ker
  have e1 : (fun v => oma (h₀, h₁) (fun u => (a • C) u v) 0) = a • fun v => oma (h₀, h₁) (fun u => C u v) 0 := by
    funext v
    have e : (fun u => (a • C) u v) = a • fun u => C u v := by
      funext u; simp only [Pi.smul_apply]
    rw [e, map_smul]; simp only [Pi.smul_apply]
  rw [e1, map_smul]; simp only [Pi.smul_apply, smul_eq_mul]

theorem biLift_smul {A S X : HSp D} (oma : Om A S) (omX : Om S X) (vA : Vol A) (vS : Vol S) (φ : GA D A → ℂ) (a : ℂ)
    (C : WO A S → WO S X → ℂ) (h₂ : GA D X) :
    biLift oma omX vA vS φ (a • C) h₂ = a * biLift oma omX vA vS φ C h₂ := by
  rw [GlobalTheory.SeeSmallPf.biLift_eq, GlobalTheory.SeeSmallPf.biLift_eq]
  have e : ∀ h₀ h₁, φ h₀ * GlobalTheory.SeeSmallPf.ker oma omX (a • C) h₀ h₁ h₂ =
      a * (φ h₀ * GlobalTheory.SeeSmallPf.ker oma omX C h₀ h₁ h₂) := fun h₀ h₁ => by rw [ker_smul]; ring
  simp only [e, integral_const_mul]

theorem theta_smul {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (a : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (a • f) where
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U, hUo, fun u hu hi => ?_⟩
    have e : heisO ψ S T u (a • f) = a • heisO ψ S T u f := by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, hU u hu hi]
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := (contDiff_const.mul (hf.smooth k L hL hfin w))

theorem sum_fin {G M : Type} [AddCommMonoid M] (s : Finset G) (F : G → M) :
    ∑ g ∈ s, F g = ∑ i : Fin s.card, F (s.equivFin.symm i) := by
  rw [← Finset.sum_coe_sort s F]
  exact (Equiv.sum_comp s.equivFin.symm (fun x => F x)).symm

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c), c.Is → t.Is → WeilOK (t := t) v → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (Y : WO (c.V (j + 1)) c.T → ℂ), IsThetaFunO c.ψ _ _ Y → ∀ φ, IsContAut (c.X j) φ → (∀ X : WO (c.V j) (c.V (j + 1)) → ℂ, IsThetaFunO c.ψ _ _ X → ∀ f, IsContAut c.T f → IntegrableOn (fun h' => f h' * c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) X Y) ((c.oT (j + 1 + 1) h).emb (h', 1))) c.volT.𝓕 c.volT.μ) ∧ ∀ (G : Type) (s : Finset G) (a : G → ℂ) (X : G → WO (c.V j) (c.V (j + 1)) → ℂ), (∀ g, IsThetaFunO c.ψ _ _ (X g)) → ∑ g ∈ s, a g • c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (X g) Y) = c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (∑ g ∈ s, a g • X g) Y) := by
  intro D c v t hc ht hW j h Y hY φ hφ
  obtain ⟨χA, χz, χS', χT, omz, omT, omz'', hχV, hWa, hWz, hWX, hWT, hWTb, hWz''⟩ := hW.last j h
  have hB : BiAct D := GlobalTheory.SeeSaw.biAct_all D
  have hA : CoCpt (c.X j) := (hc.x j (by omega)).cpt
  have hS : CoCpt (c.X (j + 1)) := (hc.x (j + 1) (by omega)).cpt
  have hτ := (hW.tau j h).2
  obtain ⟨-, -, hthS, -⟩ := GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO D c.ψ (c.V (j + 1)) (c.X (j + 1)) c.T (c.jac j 0 h).d hc.std
  have hY' : IsThetaFunO c.ψ (c.X (j + 1)) c.T (fun w => Y ((c.jac j 0 h).d.ext0 c.T w)) := (hthS Y).2 hY
  have hC : ∀ Z : WO (c.V j) (c.V (j + 1)) → ℂ, IsThetaFunO c.ψ _ _ Z →
      IsBiTheta c.ψ (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1)) (c.lst j h (v.τ j h) (t.sBF j 0 h) Z Y) := by
    intro Z hZ
    have hZ' : IsThetaFunO c.ψ (c.B j 0 h).V (c.J j 0 h).W Z := hZ
    obtain ⟨hΞ, -⟩ := GlobalTheory.LastRed.val_zero (t.sBF j 0 h) hZ'
    exact GlobalTheory.LastRed.lastBi_biTheta D c.ψ (c.bes j 0 h).V₀ (c.X j) (c.bes j 0 h).L (c.X (j + 1)) (c.X (j + 1 + 1)) c.T c.Lz
      (c.bes j 0 h).o (c.oT (j + 1 + 1) h) (v.τ j h) hτ (flatBF (t.sBF j 0 h) Z) _ hΞ hY'
  refine ⟨fun X hX f hf => GlobalTheory.SeeSmallPf.outer hB hWa hWX (hC X hX) hA hS hc.cpt (c.x j).vol (c.x (j + 1)).vol c.volT
    (c.oT (j + 1 + 1) h) hφ hf, fun G s a X hX => ?_⟩
  have hsum : ∀ (Z : G → WO (c.V j) (c.V (j + 1)) → ℂ), c.lst j h (v.τ j h) (t.sBF j 0 h) (∑ g ∈ s, a g • Z g) Y =
      ∑ g ∈ s, a g • c.lst j h (v.τ j h) (t.sBF j 0 h) (Z g) Y := by
    intro Z
    funext u w
    simp only [Comm.lst, GlobalTheory.FinPl.lastBi, OrthDec.boxT, GlobalTheory.LastRed.flatBF_rankZero, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun g _ => by ring
  have hsm : ∀ (b : ℂ) (Z : WO (c.V j) (c.V (j + 1)) → ℂ), c.lst j h (v.τ j h) (t.sBF j 0 h) (b • Z) Y =
      b • c.lst j h (v.τ j h) (t.sBF j 0 h) Z Y := by
    intro b Z
    funext u w
    simp only [Comm.lst, GlobalTheory.FinPl.lastBi, OrthDec.boxT, GlobalTheory.LastRed.flatBF_rankZero, Pi.smul_apply, smul_eq_mul]
    ring
  funext h₂
  rw [hsum, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have e1 : ∀ g, a g * c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (X g) Y) h₂ =
      c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (a g • X g) Y) h₂ := fun g => by
    rw [hsm]; exact (biLift_smul _ _ _ _ _ _ _ _).symm
  simp only [e1]
  rw [sum_fin s, sum_fin s]
  have e2 : (∑ i : Fin s.card, a (s.equivFin.symm i) • c.lst j h (v.τ j h) (t.sBF j 0 h) (X (s.equivFin.symm i)) Y) =
      ∑ i : Fin s.card, c.lst j h (v.τ j h) (t.sBF j 0 h) (a (s.equivFin.symm i) • X (s.equivFin.symm i)) Y :=
    Finset.sum_congr rfl fun i _ => (hsm _ _).symm
  rw [e2]
  exact (GlobalTheory.SeeSmallPf.biLift_sum hB hWa hWX hA hS (c.x j).vol (c.x (j + 1)).vol hφ
    (fun i => c.lst j h (v.τ j h) (t.sBF j 0 h) (a (s.equivFin.symm i) • X (s.equivFin.symm i)) Y)
    (fun i => hC _ (theta_smul _ (hX _))) h₂).symm

end GlobalTheory.LastDbl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemColGroupIff
section
noncomputable section

namespace GlobalTheory.SeeSaw.LevMem

section Columns

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.LevRead GlobalTheory.Mem.Col2.TC.GLev0 Matrix
open scoped TensorProduct

section Pts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def IsInt (m : GL (Fin n) (AfE F E)) : Prop := (∀ i j, m.1 i j ∈ RInt F E) ∧ ∀ i j, (m⁻¹).1 i j ∈ RInt F E

theorem isInt_of {m : GL (Fin n) (AfE F E)} (h : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔ ∀ i, (m.1 *ᵥ z) i ∈ RInt F E) :
    IsInt m := by
  have h1 : ∀ j i, (Pi.single j 1 : Fin n → AfE F E) i ∈ RInt F E := fun j i => by
    rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  refine ⟨fun i j => by simpa using (h _).1 (h1 j) i, fun i j => ?_⟩
  have := (h ((m⁻¹).1 *ᵥ Pi.single j 1)).2 (by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    exact h1 j) i
  simpa using this

def LastOne (P : HeightOneSpectrum (𝓞 E)) (m : GL (Fin n) (AfE F E)) : Prop :=
  ∀ r : Fin n, r.1 + 1 = n → ∀ j, HasRes P (adAt F P (m.1 r j)) (if j = r then 1 else 0)

variable [StarRing E] {hc : CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

end Pts

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

end Columns

section LocalField

open ValuativeRel IsLocalRing Matrix GlobalTheory.LatPair
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos Reduces)

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

end LocalField

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos)
open GlobalTheory.SymBridge

section Adelic

variable {D : D7}

theorem mem_latHat_iff {n : ℕ} {L : Set (Fin n → D.host.E)} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D n)
    (z : Fin n → Af D.host.F ⊗[D.host.F] D.host.E) : z ∈ latHat D.host.F D.host.E L ↔ ∀ i, z i ∈ intAE D := by
  constructor
  · intro h i
    induction h using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨a, ha, ⟨x i, (hL x).1 hx i⟩, rfl⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | neg y _ hy => exact neg_mem hy
  · intro h
    rw [← Finset.univ_sum_single z]
    refine sum_mem fun i _ => ?_
    have hi := h i
    generalize z i = c at hi
    induction hi using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), (hL _).2 fun j => ?_, funext fun j => ?_⟩
      · rw [Pi.single_apply]
        split_ifs
        exacts [x.isIntegral_coe, isIntegral_zero]
      · rw [Pi.single_apply, Pi.single_apply]
        split_ifs
        exacts [rfl, (TensorProduct.tmul_zero _ _).symm]
    | zero => rw [Pi.single_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Pi.single_add]; exact add_mem hy hz
    | neg y _ hy => rw [Pi.single_neg]; exact neg_mem hy

set_option maxHeartbeats 1000000 in

theorem moves_iff {V : HSp D} {L : GlobalTheory.FinPl.Lat V} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D V.rank) {κ : GA D V} {n : ℕ} (hn : V.rank = n)
    {y : GL (Fin n) (EF D)} (hy : finM V hn κ = y.1) :
    GlobalTheory.FinPl.Moves V κ L L (fun _ => True) ↔ IsInt (F := D.host.F) (E := D.host.E) y := by
  subst hn
  have h1 : ∀ a : Fin V.rank → AE D, (∀ i, a i ∈ GlobalTheory.FinPl.idAt D fun _ => True) →
      (a ∈ GlobalTheory.FinPl.latV V L (fun _ => True) ↔ ∀ i, toEAf D (a i) ∈ Formalism.L2.DIV.RInt D.host.F D.host.E) := fun a ha =>
    (GlobalTheory.FinPl.KOpen.mem_latV_iff V L _ a ha).trans ((mem_latHat_iff hL _).trans
      (forall_congr' fun i => GlobalTheory.IdemSupport.mem_intAE_iff _))
  have h2 : ∀ (a : Fin V.rank → AE D) i, toEAf D ((mt V κ *ᵥ a) i) = (y.1 *ᵥ fun j => toEAf D (a j)) i := fun a i => by
    rw [← hy]
    exact RingHom.map_mulVec (toEAf D) _ a i
  constructor
  · intro h
    refine isInt_of fun z => ?_
    let sw := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E)
    choose a ha ha' using fun i => GlobalTheory.KStabBridge.exists_fin_lift (D := D) (sw.symm (z i))
    have hz : ∀ i, toEAf D (a i) = z i := fun i => (congrArg sw (ha' i)).trans (sw.apply_symm_apply _)
    have hi : ∀ i, a i ∈ GlobalTheory.FinPl.idAt D fun _ => True := fun i =>
      Submodule.mem_inf.2 ⟨ha i, (Submodule.mem_iInf _).2 fun u => absurd trivial u.2⟩
    have := h a hi
    rw [h1 a hi, h1 _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ κ hi)] at this
    simp only [h2, hz] at this
    exact this
  · intro h a ha
    rw [h1 a ha, h1 _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ κ ha)]
    simp only [h2]
    refine ⟨PtExist.mulVec_int h.1, fun h' i => ?_⟩
    have := PtExist.mulVec_int h.2 h' i
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

section Split

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : Formalism.L2.DIV.Pl D.host.E}

end Split

variable {u : D.what₂.Word} {a : XPart D u}

def ColAt {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (H : GX a ζ₀ PP) (κ : GA D (D.sp.X 0)) : Prop :=
  H.mat0 κ ∈ colGroup H.k D.R.k (Fin D.R.t)

end Adelic

end GlobalTheory.SeeSaw.LevMem

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralAdelesSplitPlacesIffHalves
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPl.SplitHalves

variable {D : D7}

theorem sum_idem {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → SplitPt D k} {I : List ι} {P : Pl D → Prop} [DecidableEq ι] (hP : Places p I P) :
    ∑ i ∈ I.toFinset, GlobalTheory.FinPlLoc.idem D (· = (p i).v) = GlobalTheory.FinPlLoc.idem D P := by
  classical
  rw [← sub_eq_zero]
  apply GlobalTheory.FinPlLoc.eq_zero_of_comp
  · rw [map_sub, map_sum]
    simp only [GlobalTheory.FinPlLoc.idem, GlobalTheory.FinPlLoc.infPart_pair, Finset.sum_const_zero, sub_zero]
  · intro w
    rw [map_sub, map_sum]
    simp only [GlobalTheory.FinPlLoc.compAt_idem]
    by_cases hw : P w
    · obtain ⟨j, rfl⟩ := (hP.mem w).1 hw
      rw [Finset.sum_eq_single j (fun i _ hij => if_neg (fun h => hij (hP.inj h.symm)))
        (fun hj => absurd (List.mem_toFinset.2 (hP.all j)) hj), if_pos rfl, if_pos hw, sub_self]
    · rw [Finset.sum_eq_zero (fun i _ => if_neg (fun h => hw ((hP.mem w).2 ⟨i, h⟩))), if_neg hw, sub_self]

theorem mem_intAt_iff_halves : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ a : AE D, a ∈ intAt D P ↔ a ∈ idAt D P ∧ ∀ i, (p i).pr a ∈ 𝒪[k] ∧ (p i).pr (cA D a) ∈ 𝒪[k] := by
  intro D k _ _ _ _ ι p I P hP a
  classical
  have hsec1 : ∀ i, (p i).sec 1 ∈ intAt D (· = (p i).v) := fun i => by
    simpa using (GlobalTheory.Core.Mi.LatMatch.mul_sec_mem_intAt_iff (p i) 1 1).2 (by simp)
  have hcsec1 : ∀ i, cA D ((p i).sec 1) ∈ intAt D (· = (p i).v) := fun i => by
    simpa using (GlobalTheory.Core.Mi.LatMatch.mul_cA_sec_mem_intAt_iff (p i) 1 1).2 (by simp)
  constructor
  · intro h
    have hr := (GlobalTheory.IwaIdeals.mem_intAt_iff.1 h).2
    refine ⟨h.1, fun i => ⟨?_, ?_⟩⟩
    · have h1 : a * (p i).sec 1 ∈ intAt D (· = (p i).v) := GlobalTheory.IwaIdeals.mem_intAt_iff.2
        ⟨Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.sec_mem_idAt _ _),
          mul_mem hr (GlobalTheory.IwaIdeals.mem_intAt_iff.1 (hsec1 i)).2⟩
      simpa using (GlobalTheory.Core.Mi.LatMatch.mul_sec_mem_intAt_iff (p i) a 1).1 h1
    · have h1 : a * cA D ((p i).sec 1) ∈ intAt D (· = (p i).v) := GlobalTheory.IwaIdeals.mem_intAt_iff.2
        ⟨Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.csec_mem_idAt (p := p i) 1),
          mul_mem hr (GlobalTheory.IwaIdeals.mem_intAt_iff.1 (hcsec1 i)).2⟩
      simpa using (GlobalTheory.Core.Mi.LatMatch.mul_cA_sec_mem_intAt_iff (p i) a 1).1 h1
  · rintro ⟨hid, hh⟩
    refine ⟨hid, ?_⟩
    have ha : a = ∑ i ∈ I.toFinset, (a * (p i).sec 1 + a * cA D ((p i).sec 1)) := by
      conv_lhs => rw [← (GlobalTheory.FinPlLoc.mem_idAt_iff P a).1 hid, ← sum_idem hP, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      set ε := GlobalTheory.FinPlLoc.idem D (· = (p i).v)
      have h1 : ε * a ∈ idAt D (· = (p i).v) := Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
      have h2 := (GlobalTheory.FinPl.FrameLat.idem_iff (p i) _).1 h1
      have he : ε * (p i).sec 1 = (p i).sec 1 :=
        (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.FrameLat.sec_mem_idAt _ _)
      have hce : ε * cA D ((p i).sec 1) = cA D ((p i).sec 1) :=
        (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.FrameLat.csec_mem_idAt (p := p i) 1)
      rw [GlobalTheory.FinPl.FrameLat.sec_one] at he hce ⊢
      calc ε * a = ((p i).e + cA D (p i).e) * (ε * a) := h2.symm
        _ = (ε * (p i).e) * a + (ε * cA D (p i).e) * a := by
          rw [add_mul, mul_left_comm, ← mul_assoc, mul_left_comm (cA D (p i).e), ← mul_assoc]
        _ = a * (p i).e + a * cA D (p i).e := by rw [he, hce, mul_comm (p i).e, mul_comm (cA D (p i).e)]
    rw [ha, map_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [map_add]
    exact add_mem ((GlobalTheory.Core.Mi.LatMatch.mul_sec_mem_intAt_iff (p i) a 1).2 (by simpa using (hh i).1)).2
      ((GlobalTheory.Core.Mi.LatMatch.mul_cA_sec_mem_intAt_iff (p i) a 1).2 (by simpa using (hh i).2)).2

end GlobalTheory.FinPl.SplitHalves

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSecondModelStabilizerIffCarriesRowLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.KsetAt

theorem mem_Kset_iff_moves : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (v : GlobalTheory.FinPl.Pl D) (κ : GA D (D.sp.Y 0)), κ ∈ grpAt (D.sp.Y 0) (· = v) → ((iotaX X h κ).2 ∈ X.B.I.Kset ↔ Moves (D.sp.Y 0) κ (latS D) (latS D) (· = v)) := by
  intro D X h v κ hκ
  have hlat : Submodule.IsLattice D.host.E (latS D) :=
    GlobalTheory.StdFrames.isLattice_crdLat (D.sp.Y 0) (D.sp.Y 0).standardTuple_isLattice
  obtain ⟨β, hβ⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E _ (latS D) hlat
  have h1 := ((GlobalTheory.SeeConjReadIota.read_iota X h β hβ κ).2.1)
  have h2 := GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_of_fg (D.sp.Y 0) β (latS D) hβ hlat.fg κ
  have h3 : κ ∈ GlobalTheory.AdelicU.levelOpen D.sp.cm.sig (D.sp.Y 0).gram (latS D) ↔
      Moves (D.sp.Y 0) κ (latS D) (latS D) (· = v) :=
    ⟨fun hk => GlobalTheory.FinPl.KOpen.moves_of_levelOpen (D.sp.Y 0) (latS D) hlat.fg (· = v) hk,
     fun hm => GlobalTheory.FinPl.KOpen.levelOpen_of_inK (D.sp.Y 0) (latS D) hlat.fg (· = v) ⟨hκ, hm⟩⟩
  exact h1.trans (h2.trans (GlobalTheory.AdelicU.mem_levelOpen.symm.trans h3))

end GlobalTheory.Core.Mi.KsetAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedDatumEqFiniteDatumRepresentativePair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.TwMovedVal

set_option maxHeartbeats 1600000 in

theorem moves_rep_tw : ∀ {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch : ℕ → Type} (A : TwDat I l Z u a Ch), A.Is → ∀ (j : ℕ) (hj : j ≤ B.R.m) (c : (I.stp u a j).Cl) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), finM _ (rankN (I.rec7 l Z) j hj) g = ((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1.1 → Moves _ (rankN (I.rec7 l Z) j hj) g ((I.stp u a j).rep c).1.1.deco.1.N := by
  intro B X I l Z u a Ch A hA j hj c g hg
  have h1 := ((hA.reads j hj).pt c).lat
  have h2 := ((hA.base j hj (A.chOf j c)).1).lat
  rw [extTo_deco] at h1 h2
  rw [(hA.base j hj (A.chOf j c)).2] at h2
  have hinv : finM _ (rankN (I.rec7 l Z) j hj) g⁻¹ = ((((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1)⁻¹ : GL _ _).1 := by
    have e1 : finM _ (rankN (I.rec7 l Z) j hj) g⁻¹ * ((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1.1 = 1 := by
      rw [← hg, ← GlobalTheory.RepLattice.finM_mul', inv_mul_cancel, GlobalTheory.RepLattice.finM_one']
    rw [← Matrix.mul_one (finM _ _ g⁻¹), ← Units.mul_inv (((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1), ← Matrix.mul_assoc, e1,
      Matrix.one_mul]
  intro x
  rw [hinv]
  exact GlobalTheory.RepLattice.mem_iff_of_carries _ _ _ ((I.stp u a j).rep c).1.1.deco.2.lat h1 h2 x

set_option maxHeartbeats 1600000 in

theorem moved_datum_val_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ p : ℂ, (∀ z, Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) = p * A.xi i hi α γ z) → ∀ (c : {c // A.chOf i c = α}) (c' : {c // A.chOf (i + 1) c = γ}), Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (A.h i α c) ((I.stp u a i).rep c.1).1.1.deco.1.N ∧ Moves _ (rankN (I.rec7 l Z) (i + 1) hi) (A.h (i + 1) γ c') ((I.stp u a (i + 1)).rep c'.1).1.1.deco.1.N ∧ ∀ z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E, Φ (actO _ _ (A.h i α c)⁻¹ (A.h (i + 1) γ c')⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) = p * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) z)) := by
  intro B X I hOk hP l Z u a Ch A hA i hi α γ Φ hΦ p hΦv c c'
  obtain ⟨c, rfl⟩ := c
  obtain ⟨c', rfl⟩ := c'
  obtain ⟨hg, hy⟩ := hA.h i (Nat.le_of_succ_le hi) (A.chOf i c) ⟨c, rfl⟩
  obtain ⟨hg', hy'⟩ := hA.h (i + 1) hi (A.chOf (i + 1) c') ⟨c', rfl⟩
  refine ⟨moves_rep_tw A hA i _ c _ hy, moves_rep_tw A hA (i + 1) hi c' _ hy', fun z => ?_⟩
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.T.chartBasePair_datum_rational_approx_eq_twisted I hOk hP l Z u a Ch A hA i hi c c' _ _ hg hg' hy hy'
  obtain ⟨-, k, hk0, hkinv, -⟩ := hΦ
  obtain ⟨γ₀, v, hv, hvh, he⟩ := GlobalTheory.AdForm.exists_rat_half_approx _ _ A.e _ hA.idem (M * k) (Nat.mul_pos hM0 hk0)
    (actO _ _ (A.h i (A.chOf i c) ⟨c, rfl⟩)⁻¹ (A.h (i + 1) (A.chOf (i + 1) c') ⟨c', rfl⟩)⁻¹ (z.map fun r => incA (I.rec7 l Z) r))
  have hx : actO _ _ (A.h i (A.chOf i c) ⟨c, rfl⟩)⁻¹ (A.h (i + 1) (A.chOf (i + 1) c') ⟨c', rfl⟩)⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) =
      A.e • actO _ _ (A.h i (A.chOf i c) ⟨c, rfl⟩)⁻¹ (A.h (i + 1) (A.chOf (i + 1) c') ⟨c', rfl⟩)⁻¹ (z.map fun r => incA (I.rec7 l Z) r) := by
    have : (z.map fun r => A.e * incA (I.rec7 l Z) r) = A.e • (z.map fun r => incA (I.rec7 l Z) r) := by
      ext a b; rfl
    simp only [actO, this, Matrix.mul_smul, Matrix.smul_mul]
  have half : ∀ (n : ℕ) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), IsHalf A.e v → IsHalf A.e (n • v) :=
    fun n v h a b => by
      simp only [Matrix.smul_apply, nsmul_eq_mul]
      rw [mul_left_comm, h a b]
  have e1 : Φ (γ₀.map fun r => A.e * incA (I.rec7 l Z) r) =
      Φ (actO _ _ (A.h i (A.chOf i c) ⟨c, rfl⟩)⁻¹ (A.h (i + 1) (A.chOf (i + 1) c') ⟨c', rfl⟩)⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) := by
    rw [he, ← hx, mul_nsmul]
    exact hkinv _ (nsmul_mem hv M) (half M v hvh) _
  rw [← e1, hΦv]
  congr 1
  refine hM z γ₀ (k • v) (nsmul_mem hv k) (half k v hvh) ?_
  rw [he, ← hx, mul_nsmul']

end GlobalTheory.AdForm.TwMovedVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OffBaseGramTermSumInvariantRationalFlagUnipotentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.offBaseGram_termSum_invariant_rationalFlagUnipotent : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), IsBase W x₀ → ∀ γ ∈ GQ V, γ ∈ flagN d → ∀ Φ : WO V W → ℂ, IsThetaFunO ψ V W Φ → ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS (om (γ, 1) Φ) x.1 = ∑' x : {x : Matrix (Fin W.rank) (Fin ρ) D.host.E // gramQ W x ≠ gramQ W x₀}, term ψ d W vS Φ x.1 := by
  first | exact @GlobalTheory.Unf.tsum_offBase_invariant | exact GlobalTheory.Unf.tsum_offBase_invariant | (intros; apply GlobalTheory.Unf.tsum_offBase_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawLastStageCharsUnramifiedAtLevelPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

namespace GlobalTheory.LastStep

theorem chars_unram : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (t : Tup c), t.UnrOn (· ∈ v.tP) → t.UnrK (· ∈ v.tP) → ∀ (χz χS' χT : (AE D)ˣ →* Circle), IsWeilDatumO c.ψ _ _ χS' (χT * χz⁻¹) (t.kom (j + 1)) → IsWeilDatumO c.ψ _ _ χS' χT (t.omT j h) → ∀ x, x ∈ v.tP → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS' x ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT x := by
  intro D c v k _ _ _ _ ι o hS j h t hU hK χz χS' χT h1 h2 x hx
  obtain ⟨i, rfl⟩ := (hS.pre.tP x).1 hx
  have hpos : ∀ n, 0 < (c.X n).rank := fun n => by
    apply Nat.pos_of_ne_zero
    intro h0
    have P := o.Q n i
    revert P
    rw [h0]
    intro P
    exact P.fn_ne (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])
  have hV : 0 < (c.V (j + 1)).rank := by
    have := (c.jac j 0 h).d.rank_add
    have := hpos (j + 1)
    omega
  obtain ⟨χS₃, χT₃, hW₃, hu₃⟩ := hK (j + 1) (by omega)
  obtain ⟨χS₂, χT₂, hW₂, hu₂⟩ := hU.top j h
  refine ⟨?_, ?_⟩
  · exact (GlobalTheory.T.weilRepresentation_determines_charUnramified_splitPlace D k (o.p i) c.ψ _ _ χS₃ χT₃ χS' (χT * χz⁻¹) (t.kom (j + 1)) hW₃ h1).2 (hpos _) (hu₃ _ ((hS.pre.tP _).2 ⟨i, rfl⟩)).1
  · exact (GlobalTheory.T.weilRepresentation_determines_charUnramified_splitPlace D k (o.p i) c.ψ _ _ χS₂ χT₂ χS' χT (t.omT j h) hW₂ h2).1 hV (hu₂ _ ((hS.pre.tP _).2 ⟨i, rfl⟩)).2

end GlobalTheory.LastStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualCoreComponentGluedAlongPairStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualCore_component_gluedAlongPair : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M : Lat S) (μ : D.host.E) (T : ℕ) (q : GlobalTheory.LatPair.Unif k), IsSumFrame o ζ β β₀ → IsSelfDualC S M → μ ≠ 0 → LineAt (vecB o ζ) μ M p.v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → valuation k (p.pr (incA D (T : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k) → ∃ P : GlobalTheory.LatPair.Pair k n, GluedW β₀ M q (p.pr (incA D μ)) P := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.exists_gluedW | exact GlobalTheory.Core.Mi.LatMatch.exists_gluedW | (intros; apply GlobalTheory.Core.Mi.LatMatch.exists_gluedW <;> assumption)
end

