import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOfHeisDer
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0293
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0232
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqIntegralFactorQuotient

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodPositionSplitLinesReadCompletionsAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocCongr

variable {D : D7}

theorem mul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {z : Fin S.rank → AE D} (hz : z ∈ latV S L P) :
    (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) ∈ latA S L P := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (0 : Fin S.rank → AE D) i) = 0 := by
      funext i; simp
    rw [this]; exact zero_mem _
  | add z z' _ _ hz hz' =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (z + z') i) =
        (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) + (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z' i) := by
      funext i; simp [mul_add]
    rw [this]; exact add_mem hz hz'
  | neg z _ hz =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (-z) i) =
        -(fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) := by
      funext i; simp
    rw [this]; exact neg_mem hz

theorem latA_le_of_latV_le {S : HSp D} {L L' : Lat S} {P : Pl D → Prop} (h : latV S L P ≤ latV S L' P) :
    latA S L P ≤ latA S L' P := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro y ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩
  have hz : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) ∈ latV S L P :=
    AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
  have hm := mul_mem_latA (L := L') ha (h hz)
  have key : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) =
      fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
    funext i
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [SetLike.mem_coe, key]
  exact hm

theorem latA_congr {S : HSp D} {L L' : Lat S} {P : Pl D → Prop} (h : latV S L P = latV S L' P) :
    latA S L P = latA S L' P :=
  le_antisymm (latA_le_of_latV_le h.le) (latA_le_of_latV_le h.ge)

theorem latO_congr {S T : HSp D} {LS LS' : Lat S} {LT LT' : Lat T} (hS : IsSelfDualC S LS) (hS' : IsSelfDualC S LS')
    (hT : IsSelfDualC T LT) (hT' : IsSelfDualC T LT') {P : Pl D → Prop} (eS : latV S LS P = latV S LS' P)
    (eT : latV T LT P = latV T LT' P) :
    latO S T (LS : Set _) (LT : Set _) P = latO S T (LS' : Set _) (LT' : Set _) P := by
  ext u
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT, GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS' LT' hS' hT', eS,
    latA_congr eT]

theorem monoAt_congr {S S₀ : HSp D} {ρ : ℕ} {d : HypDec S S₀ ρ} {L L' : Lat S} {L₀ L₀' : Lat S₀} {v : Pl D}
    (e : latV S L (· = v) = latV S L' (· = v)) (e₀ : latV S₀ L₀ (· = v) = latV S₀ L₀' (· = v)) (H : MonoAt d L L₀ v) :
    MonoAt d L' L₀' v := by
  unfold MonoAt at H ⊢
  rw [← e, ← e₀]
  exact H

theorem orthAt_congr {S A B : HSp D} {o : OrthDec S A B} {L L' : Lat S} {LA : Lat A} {LB : Lat B} {v : Pl D}
    (e : latV S L (· = v) = latV S L' (· = v)) (H : OrthAt o L LA LB v) : OrthAt o L' LA LB v := by
  unfold OrthAt at H ⊢
  rw [← e]
  exact H

theorem primAt_congr {ψ : AddChar (AF D.host.F) ℂ} {S S₀ : HSp D} {ρ : ℕ} {d : HypDec S S₀ ρ} {L L' : Lat S} {v : Pl D}
    (e : latV S L (· = v) = latV S L' (· = v)) (H : PrimAt ψ d L v) : PrimAt ψ d L' v := by
  unfold PrimAt at H ⊢
  rw [← e]
  exact H

theorem colsAt_congr {V V₀ W : HSp D} {ρ : ℕ} {d : HypDec V V₀ ρ} {x : Mx D W.rank ρ} {LV LV' : Lat V} {LW LW' : Lat W}
    {v : Pl D} (e : latV V LV (· = v) = latV V LV' (· = v)) (eW : latV W LW (· = v) = latV W LW' (· = v))
    (H : ColsAt d x LV LW v) : ColsAt d x LV' LW' v := by
  unfold ColsAt at H ⊢
  rw [← e, ← latA_congr eW]
  exact H

end GlobalTheory.LocCongr

namespace GlobalTheory.LocCongr

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem goodBF_congr {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} {LV LV' : Lat B.V} {LV₀ LV₀' : Lat B.V₀} {LW LW' : Lat J.W}
    {LW₀ : Lat J.W₀} {v : Pl D} (sV : IsSelfDualC B.V LV') (sV₀ : IsSelfDualC B.V₀ LV₀') (sW : IsSelfDualC J.W LW')
    (eV : latV B.V LV (· = v) = latV B.V LV' (· = v)) (eV₀ : latV B.V₀ LV₀ (· = v) = latV B.V₀ LV₀' (· = v))
    (eW : latV J.W LW (· = v) = latV J.W LW' (· = v)) (H : GoodBF ψ B J LV LV₀ LW LW₀ v) :
    GoodBF ψ B J LV' LV₀' LW' LW₀ v where
  tame := H.tame
  sdV := sV
  sdV₀ := sV₀
  sdW := sW
  sdW₀ := H.sdW₀
  monoV := monoAt_congr eV eV₀ H.monoV
  monoW := monoAt_congr eW rfl H.monoW
  prim := primAt_congr eV H.prim
  cols := colsAt_congr eV eW H.cols
  last := by
    rw [← latO_congr H.sdV₀ sV₀ H.sdW sW eV₀ eW]
    exact H.last

theorem adaptFB_congr {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} {LV LV' : Lat J.W} {LV₀ : Lat J.W₀}
    {LW LW' : Lat B.V} {LW₀ LW₀' : Lat B.V₀} {v : Pl D} (sV : IsSelfDualC J.W LV') (sW : IsSelfDualC B.V LW')
    (sW₀ : IsSelfDualC B.V₀ LW₀') (eV : latV J.W LV (· = v) = latV J.W LV' (· = v))
    (eW : latV B.V LW (· = v) = latV B.V LW' (· = v)) (eW₀ : latV B.V₀ LW₀ (· = v) = latV B.V₀ LW₀' (· = v))
    (H : AdaptFB ψ J B LV LV₀ LW LW₀ v) : AdaptFB ψ J B LV' LV₀ LW' LW₀' v where
  tame := H.tame
  sdV := sV
  sdV₀ := H.sdV₀
  sdW := sW
  sdW₀ := sW₀
  monoV := monoAt_congr eV rfl H.monoV
  monoW := monoAt_congr eW eW₀ H.monoW
  prim := primAt_congr eV H.prim
  cols := colsAt_congr eV eW H.cols

theorem goodAt_splitAt_congr : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀)
    (x : Pl D), (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j) ∧ IsSelfDualC (c.V j) (N j) ∧
      latV (c.V j) (N j) (· = x) = latV (c.V j) (v.N j) (· = x)) →
    (∀ j ρ h, IsSelfDualC _ (o.M j ρ h) ∧ IsSelfDualC _ (M j ρ h) ∧ latV _ (M j ρ h) (· = x) = latV _ (o.M j ρ h) (· = x)) →
    (GoodAt v o x → GoodAt { v with N := N } { o with M := M } x) ∧
      (SplitAt v o x → SplitAt { v with N := N } { o with M := M } x) := by
  intro D c v k _ _ _ _ ι o N M x hN hM
  refine ⟨fun hg => ⟨fun j ρ h => ?_, fun j σ h => ?_⟩, fun hs => ⟨fun j ρ h => ?_, fun j h => ?_⟩⟩
  · have h0 := hN j (by omega)
    have h1 := hN (j + 1) (by omega)
    exact goodBF_congr h0.2.1 (hM j ρ h).2.1 h1.2.1 h0.2.2.symm (hM j ρ h).2.2.symm h1.2.2.symm (hg.bf j ρ h)
  · have h1 := hN (j + 1) (by omega)
    have h2 := hN (j + 1 + 1) (by omega)
    exact adaptFB_congr h1.2.1 h2.2.1 (hM (j + 1 + 1) σ (idx_step h)).2.1 h1.2.2.symm h2.2.2.symm
      (hM (j + 1 + 1) σ (idx_step h)).2.2.symm (hg.fb j σ h)
  · obtain ⟨LL, hLL, hO⟩ := hs.core j ρ h
    exact ⟨LL, hLL, orthAt_congr (hM j ρ h).2.2.symm hO⟩
  · obtain ⟨LL, LZ, h1, h2, h3, h4, h5⟩ := hs.top j h
    exact ⟨LL, LZ, h1, h2, orthAt_congr (hM j 0 h).2.2.symm h3, h4, h5⟩

end GlobalTheory.LocCongr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtDOmT
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.ZcDer

open GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift (dOmT)

theorem conjAt_rel {D : D7} (V : HSp D) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    gramAt D V τ * Formalism.L2.Theta.conjAt V τ Z = -(Zᴴ * gramAt D V τ) ∧
      (Formalism.L2.Theta.conjAt V τ Z)ᴴ * gramAt D V τ = -(gramAt D V τ * Z) := by
  have h1 : gramAt D V τ * Formalism.L2.Theta.conjAt V τ Z = -(Zᴴ * gramAt D V τ) := by
    unfold Formalism.L2.Theta.conjAt
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ), Matrix.one_mul]
  refine ⟨h1, ?_⟩
  have h2 := congrArg Matrix.conjTranspose h1
  rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, GlobalTheory.SmoothForms.RealPts.gramAt_herm] at h2

theorem re_mem {D : D7} (V : HSp D) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    (1 / 2 : ℂ) • (Z + Formalism.L2.Theta.conjAt V τ Z) ∈ lieAt V τ := by
  obtain ⟨a, b⟩ := conjAt_rel V τ Z
  show _ + _ = _
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.conjTranspose_add, Matrix.add_mul,
    Matrix.mul_add, a, b]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this, ← smul_add]
  simp

theorem im_mem {D : D7} (V : HSp D) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    (1 / (2 * Complex.I)) • (Z - Formalism.L2.Theta.conjAt V τ Z) ∈ lieAt V τ := by
  obtain ⟨a, b⟩ := conjAt_rel V τ Z
  show _ + _ = _
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.conjTranspose_sub, Matrix.sub_mul,
    Matrix.mul_sub, a, b]
  have : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by simp
  rw [this, sub_neg_eq_add, sub_neg_eq_add, add_comm (Zᴴ * gramAt D V τ), neg_smul, neg_add_cancel]

theorem hasDerivAt_dOmT {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : WRep S T} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT om)
    {τ : D.what₂.Tau} {X : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hX : X ∈ lieAt T τ) :
    (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (dOmT θ om τ X f)) ∧
    (∀ f, IsThetaFunO ψ S T f → ∀ g h w,
      HasDerivAt (fun t : ℝ => om (g, h * oneP θ T τ X t) f w) (om (g, h) (dOmT θ om τ X f) w) 0) ∧
    (∀ f, IsThetaFunO ψ S T f → ∀ w,
      HasDerivAt (fun t : ℝ => om (1, oneP θ T τ X t) f w) (dOmT θ om τ X f w) 0) := by
  obtain ⟨ht, hd⟩ := GlobalTheory.Chain.LiftReg.tame_dOmT hθ hω hX
  have h2 : ∀ f, IsThetaFunO ψ S T f → ∀ g h w,
      HasDerivAt (fun t : ℝ => om (g, h * oneP θ T τ X t) f w) (om (g, h) (dOmT θ om τ X f) w) 0 := by
    intro f hf g h w
    have := hd f hf (g, h) w
    simp only [Prod.mk_mul_mk, mul_one] at this
    exact this
  refine ⟨fun f hf => ht.theta hf, h2, fun f hf w => ?_⟩
  have := h2 f hf 1 1 w
  simp only [one_mul, Prod.mk_one_one, map_one, Module.End.one_apply] at this
  exact this

theorem dOmT_add {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : WRep S T} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT om)
    {τ : D.what₂.Tau} {X : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hX : X ∈ lieAt T τ) {f f' : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') :
    dOmT θ om τ X (f + f') = dOmT θ om τ X f + dOmT θ om τ X f' := by
  obtain ⟨-, -, hD⟩ := hasDerivAt_dOmT hθ hω hX
  funext w
  have h1 := (hD f hf w).add (hD f' hf' w)
  have h2 := hD (f + f') ((GlobalTheory.RealWeil.thetaSub ψ S T).add_mem hf hf') w
  have e : (fun t : ℝ => om (1, oneP θ T τ X t) (f + f') w) =
      fun t => om (1, oneP θ T τ X t) f w + om (1, oneP θ T τ X t) f' w := by
    funext t
    simp only [map_add, Pi.add_apply]
  rw [e] at h2
  exact h2.unique h1

theorem dOmT_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : WRep S T} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT om)
    {τ : D.what₂.Tau} {X : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hX : X ∈ lieAt T τ) (c : ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    dOmT θ om τ X (c • f) = c • dOmT θ om τ X f := by
  obtain ⟨-, -, hD⟩ := hasDerivAt_dOmT hθ hω hX
  funext w
  have h1 := (hD f hf w).const_mul c
  have h2 := hD (c • f) ((GlobalTheory.RealWeil.thetaSub ψ S T).smul_mem c hf) w
  have e : (fun t : ℝ => om (1, oneP θ T τ X t) (c • f) w) = fun t => c * om (1, oneP θ T τ X t) f w := by
    funext t
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [e] at h2
  exact h2.unique h1

end GlobalTheory.Core.Rk.ZcDer

open GlobalTheory.Core.Rk.ZcDer in

theorem GlobalTheory.Core.Rk.ZcDer.rderC_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (τ : D.what₂.Tau) (Z : Matrix (Fin T.rank) (Fin T.rank) ℂ), ∃ Dz : (WO S T → ℂ) → (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Dz f)) ∧ (∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → Dz (f + f') = Dz f + Dz f') ∧ (∀ (c : ℂ) f, IsThetaFunO ψ S T f → Dz (c • f) = c • Dz f) ∧ ∀ f, IsThetaFunO ψ S T f → ∀ g w, RderC θ T τ Z (fun h => om (g, h) f w) = fun h => om (g, h) (Dz f) w := by
  intro D ψ θ S T χS χT om hθ hω τ Z
  have hX := GlobalTheory.Core.Rk.ZcDer.re_mem T τ Z
  have hY := GlobalTheory.Core.Rk.ZcDer.im_mem T τ Z
  obtain ⟨tX, dX, -⟩ := hasDerivAt_dOmT hθ hω hX
  obtain ⟨tY, dY, -⟩ := hasDerivAt_dOmT hθ hω hY
  refine ⟨fun f => GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT θ om τ ((1 / 2 : ℂ) • (Z + Formalism.L2.Theta.conjAt T τ Z)) f +
      Complex.I • GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT θ om τ ((1 / (2 * Complex.I)) • (Z - Formalism.L2.Theta.conjAt T τ Z)) f,
    fun f hf => ?_, fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf g w => ?_⟩
  · exact (GlobalTheory.RealWeil.thetaSub ψ S T).add_mem (tX f hf) ((GlobalTheory.RealWeil.thetaSub ψ S T).smul_mem _ (tY f hf))
  · beta_reduce
    rw [dOmT_add hθ hω hX hf hf', dOmT_add hθ hω hY hf hf', smul_add Complex.I]
    abel
  · beta_reduce
    rw [dOmT_smul hθ hω hX c hf, dOmT_smul hθ hω hY c hf, smul_add c, smul_comm Complex.I c]
  · funext h
    simp only [Formalism.L2.Theta.RderC, Formalism.L2.Theta.Rder, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_smul]
    rw [(dX f hf g h w).deriv, (dY f hf g h w).deriv]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeParametersOfElementFromOneNonzeroValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.ChainOnto.parOfVal_of_parts : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D → LevFacts D → ParOfVal D := by
  intro hP D hM hL c hc j hj s hs x w B hv hf
  obtain ⟨e, he⟩ := GlobalTheory.T.stageCuspFormValue_mem_fullSphericalHecke_eigenpart hP D hM hL c hc j hj s hs x w B hv hf
  exact (GlobalTheory.T.thetaChain_eigenPart_has_heckeParameters hP D c hc j hj s hs x e he).2 w B hv hf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombAwayFromPlaceKeepsVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.QVal GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.VacAway

variable {D : D7}

def combL (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := comb ψ S T c
  map_add' f g := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring

theorem comb_single_one (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (y : WO S T) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single y 1) f = heisO ψ S T y f := by
  unfold comb
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]

theorem vac_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q₀ : QStep S) (c₁ : WO S.B.V S.J.W →₀ ℂ) (c₂ : WO S.J.W S.B'.V →₀ ℂ), IsFinComb c₁ → IsFinComb c₂ → Q₀.Away c₁ → Q₀.Away c₂ → ∀ f₁ f₂, IsThetaFunO ψ _ _ f₁ → IsThetaFunO ψ _ _ f₂ → Q₀.Vac f₁ f₂ → Q₀.Vac (comb ψ _ _ c₁ f₁) (comb ψ _ _ c₂ f₂) := by
  intro D ψ hψ σ S Q₀ c₁ c₂ hc₁ hc₂ ha₁ ha₂ f₁ f₂ _ _ hv
  obtain ⟨hee, hec, -⟩ := Q₀.q.split
  have hce : cA D Q₀.q.e * Q₀.q.e = 0 := by rw [mul_comm, hec]
  have hcc : cA D Q₀.q.e * cA D Q₀.q.e = cA D Q₀.q.e := by rw [← map_mul, hee]
  have hreal : cA D (Q₀.q.e + cA D Q₀.q.e) = Q₀.q.e + cA D Q₀.q.e := by
    rw [map_add, Formalism.L2.Theta.cA_cA, add_comm]
  have hidem : (Q₀.q.e + cA D Q₀.q.e) * (Q₀.q.e + cA D Q₀.q.e) = Q₀.q.e + cA D Q₀.q.e := by
    rw [add_mul, mul_add, mul_add, hee, hec, hce, hcc, add_zero, zero_add]
  have horth : (Q₀.q.e + cA D Q₀.q.e) * (1 - (Q₀.q.e + cA D Q₀.q.e)) = 0 := by
    rw [mul_sub, mul_one, hidem, sub_self]
  have comm : ∀ {A B : HSp D} (c : WO A B →₀ ℂ), Q₀.Away c → ∀ (f : WO A B → ℂ) (y : WO A B),
      IsHalf (Q₀.q.e + cA D Q₀.q.e) y → comb ψ A B c (heisO ψ A B y f) = heisO ψ A B y (comb ψ A B c f) := by
    intro A B c ha f y hy
    have h := (GlobalTheory.HeisComb.main D ψ A B).2.1 (Finsupp.single y 1) c (fun x hx u hu => by
      have hxy : x = y := Finset.mem_singleton.1 (Finsupp.support_single_subset hx)
      subst hxy
      exact GlobalTheory.HeisComb.symplO_half A B _ _ x u hreal horth hy (ha u hu)) f
    rw [comb_single_one, comb_single_one] at h
    exact h.symm
  obtain ⟨⟨T₁, O₁, hT₁, hO₁, rfl⟩, ⟨T₂, O₂, hT₂, hO₂, rfl⟩⟩ := hv
  refine ⟨⟨combL ψ _ _ c₁ ∘ₗ T₁, O₁, ?_, hO₁, rfl⟩, ⟨combL ψ _ _ c₂ ∘ₗ T₂, O₂, ?_, hO₂, rfl⟩⟩
  · exact (GlobalTheory.LocModU.localModel_uniq_transport_exist D Q₀.k (ofSplit Q₀.q) _ _ _ _ Q₀.F.G₀ Q₀.F.G₁ ψ hψ).2.1 T₁ hT₁
      (combL ψ _ _ c₁) (fun f hf => (GlobalTheory.HeisComb.main D ψ _ _).2.2.1 c₁ f hf hc₁ hψ)
      (fun f _ y hy => comm c₁ ha₁ f y hy)
  · exact (GlobalTheory.LocModU.localModel_uniq_transport_exist D Q₀.k (ofSplit Q₀.q) _ _ _ _ Q₀.F.G₁ Q₀.F.G₂ ψ hψ).2.1 T₂ hT₂
      (combL ψ _ _ c₂) (fun f hf => (GlobalTheory.HeisComb.main D ψ _ _).2.2.1 c₂ f hf hc₂ hψ)
      (fun f _ y hy => comm c₂ ha₂ f y hy)

end GlobalTheory.VacAway

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacuaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (P P' : Pl D → Prop), (∀ p, P p → ¬ P' p) → (∀ e e' : WO S T →₀ ℂ, CombAt P e → CombAt P' e' → ∀ f, comb ψ S T e (comb ψ S T e' f) = comb ψ S T e' (comb ψ S T e f)) ∧ (∀ e : WO S T →₀ ℂ, CombAt P e → IsFinComb e ∧ ∀ LS LT f, Vac ψ S T LS LT P' f → Vac ψ S T LS LT P' (comb ψ S T e f)) ∧ (∀ χS χT (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ e : WO S T →₀ ℂ, CombAt P e → ∀ g ∈ grpOff S P, ∀ h ∈ grpOff T P, ∀ f, IsThetaFunO ψ S T f → om (g, h) (comb ψ S T e f) = comb ψ S T e (om (g, h) f)) ∧ (∀ e e' : WO S T →₀ ℂ, CombAt (fun p => P p ∨ P' p) e → CombAt (fun p => P p ∨ P' p) e' → ∃ e'', CombAt (fun p => P p ∨ P' p) e'' ∧ ∀ f, comb ψ S T e'' f = comb ψ S T e (comb ψ S T e' f)) ∧ ∀ LS LT f, IsSelfDualC S LS → IsSelfDualC T LT → (Vac ψ S T LS LT (fun p => P p ∨ P' p) f ↔ Vac ψ S T LS LT P f ∧ Vac ψ S T LS LT P' f) := by
  first | exact @GlobalTheory.DisjComb.main | exact GlobalTheory.DisjComb.main | (intros; apply GlobalTheory.DisjComb.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionLeClosureIsotropicHalves
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HalfGen

variable {D : D7}

theorem list_sum_pair {ι : Type} (l : List ι) (α : ι → Af D.host.F) :
    (l.map fun i => pairA D.host.F 0 (α i) ⊗ₜ[D.host.F] (1 : D.host.E)).sum =
      pairA D.host.F 0 (l.map α).sum ⊗ₜ[D.host.F] (1 : D.host.E) := by
  induction l with
  | nil => simp [GlobalTheory.FinPlLoc.pairA_zero]
  | cons a l ih => simp [List.map_cons, List.sum_cons, ih, GlobalTheory.FinPlLoc.pairA_add, TensorProduct.add_tmul]

theorem sum_splitIdem_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} {p : ι → SplitPt D k} {I : List ι} {P : Pl D → Prop} (h : Places p I P) :
    (I.map fun i => (p i).e + cA D (p i).e).sum = GlobalTheory.FinPlLoc.idem D P := by
  classical
  choose ε hε hεe using fun i => (p i).above
  choose α hαe hα1 hα0 using hε
  have hterm : ∀ i, (p i).e + cA D (p i).e = pairA D.host.F 0 (α i) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    intro i
    rw [hεe i, hαe i]
    rfl
  rw [List.map_congr_left (fun i _ => hterm i), list_sum_pair]
  unfold GlobalTheory.FinPlLoc.idem
  congr 2
  refine RestrictedProduct.ext _ _ fun w => ?_
  show evalV D.host.F w (I.map α).sum = evalV D.host.F w (GlobalTheory.FinPlLoc.ePl D P)
  rw [GlobalTheory.FinPlLoc.evalV_ePl, map_list_sum, List.map_map, ← List.sum_toFinset _ h.nodup]
  by_cases hw : P w
  · rw [if_pos hw]
    obtain ⟨j, rfl⟩ := (h.mem w).1 hw
    have hj : ∀ i, evalV D.host.F (p j).v (α i) = if i = j then 1 else 0 := by
      intro i
      split_ifs with hij
      · subst hij; exact hα1 i
      · exact hα0 i _ fun hv => hij (h.inj hv.symm)
    simp only [Function.comp_apply, hj]
    rw [Finset.sum_ite_eq' , if_pos (List.mem_toFinset.2 (h.all j))]
  · rw [if_neg hw]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact hα0 i w fun hv => hw ((h.mem w).2 ⟨i, hv⟩)

theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, hsum⟩ := he
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hε, ?_⟩
  · rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, h2]
  · rw [GlobalTheory.DualPairCheck.cA_cA, add_comm, hsum]

theorem smul_mem_halves {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : Pl D → Prop} {e : AE D} (he : IsSplitIdem D e) {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    e • u ∈ {x | x ∈ latO S T LS LT P ∧ ∃ e, IsSplitIdem D e ∧ IsHalf e x} := by
  have hee : e * e = e := he.1
  refine ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT P e ?_ u hu, e, he, ?_⟩
  · exact GlobalTheory.AdIdem.idempotent_mem_intAE D (finPart D e) (by rw [← map_mul, hee])
  · rw [GlobalTheory.SplitScalar.isHalf_iff, smul_smul, hee]

theorem entry_mem_idAt {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : Pl D → Prop} {u : WO S T} (hu : u ∈ latO S T LS LT P) : ∀ i j, u i j ∈ idAt D P := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, -, hα, a, -, s, -, t, -, rfl⟩ := hy
    exact fun i j => GlobalTheory.FinPlLoc.pair_mem_idAt P α hα _
  | zero => exact fun i j => zero_mem _
  | add y z _ _ hy hz => exact fun i j => add_mem (hy i j) (hz i j)
  | neg y _ hy => exact fun i j => neg_mem (hy i j)

theorem latO_le_closure_halves : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)), ∀ u ∈ latO S T LS LT P, u ∈ AddSubgroup.closure {x | x ∈ latO S T LS LT P ∧ ∃ e, IsSplitIdem D e ∧ IsHalf e x} := by
  intro D k _ _ _ _ ι p I P h S T LS LT u hu
  have hsum := sum_splitIdem_eq h
  have hu' : GlobalTheory.FinPlLoc.idem D P • u = u := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (GlobalTheory.FinPlLoc.mem_idAt_iff P _).1 (entry_mem_idAt hu i j)
  have hdec : u = (I.map fun i => (p i).e • u + cA D (p i).e • u).sum := by
    conv_lhs => rw [← hu', ← hsum, List.sum_smul, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply, add_smul]
  rw [hdec]
  refine AddSubgroup.list_sum_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact add_mem (AddSubgroup.subset_closure (smul_mem_halves (p i).split hu))
    (AddSubgroup.subset_closure (smul_mem_halves (isSplitIdem_cA (p i).split) hu))

end GlobalTheory.HalfGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqIntegralFactorQuotientStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_quotient_eq_integral_factor_quotient : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (G G₁ G₂ R K₁ K₂ : Subgroup H), IsClosed (G : Set H) → IsClosed (G₁ : Set H) → IsClosed (G₂ : Set H) → IsClosed (R : Set H) → G₁ ≤ G → G₂ ≤ G → (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) → (∃ e : (G₁ × G₂) ≃ₜ G, ∀ p, (e p : H) = p.1 * p.2) → (∀ a ∈ G₁, ∀ b ∈ G₂, a * b ∈ R → a ∈ R ∧ b ∈ R) → K₁ ≤ G₁ → K₂ ≤ G₂ → IsCompact (K₁ : Set H) → IsCompact (K₂ : Set H) → IsOpen ((K₁.subgroupOf G₁ : Subgroup G₁) : Set G₁) → IsOpen ((K₂.subgroupOf G₂ : Subgroup G₂) : Set G₂) → ∀ (ρ : Measure (R.subgroupOf G)) (μ : Measure G) (ρ₁ : Measure (R.subgroupOf G₁)) (μ₁ : Measure G₁), ρ.IsHaarMeasure → μ.IsHaarMeasure → ρ₁.IsHaarMeasure → μ₁.IsHaarMeasure → ρ.IsInvInvariant → μ₁ {g | g.1 ∈ K₁} = 1 → ρ₁ {g | g.1.1 ∈ K₁} = 1 → ∀ (f : H → ℂ) (z : ℂ), (∀ r ∈ R, r ∈ G → ∀ g ∈ G, f (r * g) = f g) → (∀ k ∈ K₂, ∀ g ∈ G, f (g * k) = f g) → (∀ g ∈ G, f g ≠ 0 → ∃ r ∈ R, r ∈ G ∧ ∃ x ∈ G₁, ∃ k ∈ K₂, g = r * x * k) → IsQuotIntL1 ρ₁ μ₁ (fun x => f x.1) z → IsQuotIntL1 ρ μ (fun g => f g.1) (((μ.real {g | ∃ a ∈ K₁, ∃ b ∈ K₂, g.1 = a * b} / ρ.real {g | ∃ a ∈ K₁, ∃ b ∈ K₂, g.1.1 = a * b} : ℝ) : ℂ) * z) := by
  first | exact @GlobalTheory.CollapseFactor.collapse_factor | exact GlobalTheory.CollapseFactor.collapse_factor | (intros; apply GlobalTheory.CollapseFactor.collapse_factor <;> assumption)
end

