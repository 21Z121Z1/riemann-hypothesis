import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0150
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingReindex
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0312
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0152
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0318
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0385
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.RowsFinC
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeRightTranslateLowerBoun
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0188
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0321
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0355
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0377
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0386
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0387

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletionLatticeInfOrthEqOrthPart
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.OrthLoc

variable {D : D7}

theorem localForm_add_left (Z : LocDat D) (p : PlF D) (x y z : Vp D p) :
    LocFacts₂ Z.M p (x + y) z = LocFacts₂ Z.M p x z + LocFacts₂ Z.M p y z := by
  simp only [LocFacts₂, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem localForm_smul_left (Z : LocDat D) (p : PlF D) (c : (D.s.atP p).Ep) (x z : Vp D p) :
    LocFacts₂ Z.M p (c • x) z = c * LocFacts₂ Z.M p x z := by
  simp only [LocFacts₂, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

def orthP (Z : LocDat D) (p : PlF D) (U : Submodule D.host.E (VS D).V) :
    Submodule (D.s.atP p).Ep (Vp D p) where
  carrier := {v | ∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0}
  zero_mem' := by intro u _; simp [LocFacts₂]
  add_mem' := by intro a b ha hb u hu; rw [localForm_add_left, ha u hu, hb u hu, add_zero]
  smul_mem' := by intro c a ha u hu; rw [localForm_smul_left, ha u hu, mul_zero]

theorem span_orth_le (Z : LocDat D) (p : PlF D) (U : Submodule D.host.E (VS D).V) :
    Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (orth (VS D) U : Set (VS D).V)) ≤ orthP Z p U := by
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩ u hu
  have ha' : (VS D).hT u a = 0 := by
    have ha2 : a ∈ orth (VS D) U := ha
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at ha2
    exact ha2 u hu
  rw [baseChangeAt_form Z.M p (Z.hcj p)]
  simp [brS, ha']

theorem mem_localLattice_inf_orthogonal : ∀ (D : D7) (Z : LocDat D) (U : Submodule D.host.E (VS D).V),
    (∀ x : (VS D).V, ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b) →
    (∀ (p : PlF D) (v : Vp D p), v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) →
      (∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) → v = 0) →
    ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → ∀ (p : PlF D) (t : Vp D p), t ∈ lattice₂ D Z.M p Λ →
      (∀ u ∈ U, LocFacts₂ Z.M p t (baseChange₂ D p u) = 0) → t ∈ lattice₂ D Z.M p (Λ ⊓ toO (VS D) (orth (VS D) U)) := by
  intro D Z U hdec huniq Λ hΛ p t ht horth
  have hsat := Formalism.L2.SG.Pf.locSatC_holds D Z p Λ (orth (VS D) U) hΛ.fg
  have hmem : t ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) (orth (VS D) U)) : Set (Vp D p)) := by
    rw [hsat]
    refine ⟨ht, ?_⟩
    have htop : Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (orth (VS D) U : Set (VS D).V)) ⊔
        Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) = ⊤ := by
      rw [eq_top_iff, ← span_baseChange_eq_top (D := D) p, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := hdec x
      rw [map_add]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨a, ha, rfl⟩) (Submodule.subset_span ⟨b, hb, rfl⟩)
    have ht' : t ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (orth (VS D) U : Set (VS D).V)) ⊔
        Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) := htop ▸ Submodule.mem_top
    obtain ⟨α, hα, β, hβ, hαβ⟩ := Submodule.mem_sup.1 ht'
    have hβ0 : β = 0 := by
      apply huniq p β hβ
      have e : β = t - α := by rw [← hαβ]; abel
      have hto : t ∈ orthP Z p U := horth
      have h2 := (orthP Z p U).sub_mem hto (span_orth_le Z p U hα)
      rw [← e] at h2
      exact h2
    rw [← hαβ, hβ0, add_zero]
    exact hα
  exact hmem

end GlobalTheory.Unfold.OrthLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOneScalarPairSymmetric
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalSymm

open Formalism.L2.SG.NGCut

theorem scal_symm : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ t t' : TauC Y u u', t.G ≠ 0 → t'.G ≠ 0 → (Y.tO u u').s0 t t' = 1 → (Y.tO u u').scal t t' → (Y.tO u u').s0 t' t = 1 ∧ (Y.tO u u').scal t' t := by
  intro D X Y u u' t t' hG hG' hs hsc
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hGv : ∀ t : TauC Y u u', t.G ≠ 0 → Gval (lf D (X.Fu u)) t.frame ≠ 0 := fun t h =>
    (Formalism.L2.SG.Pf.SatGram.gterm_G Y t) ▸ h
  have hlat : ∀ t : TauC Y u u', Submodule.IsLattice D.host.E t.lam := fun t =>
    ((Y.rowsOK u).1 t.lam t.mem).2.1.1
  have hLF : ∀ t : TauC Y u u', IsLift t.lam (lf D (X.Fu u)) := fun t =>
    ((Y.rowsOK u).1 t.lam t.mem).2.1.2.2.1
  have hLt : ∀ t : TauC Y u u', IsLift t.lam t.frame := fun t => t.rep.2.2.2.2.1
  obtain ⟨⟨hlam, hlam'⟩, -, hIS⟩ := (show Formalism.L2.SG.TermOp.scalT t t' from hsc)
  have h1' : Formalism.L2.SG.TermOp.s0T t t' = 1 := hs
  unfold Formalism.L2.SG.TermOp.s0T at h1'
  rw [if_pos ⟨hlam, hlam'⟩] at h1'
  have hth := (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t.frame t'.frame _ (hLF t) (hLt t)
    (hGv t hG)).1 h1'
  have hL' : IsLift t.lam t'.frame := by rw [hlam]; exact hLt t'
  have hsym := CorankRelation.Th_symm D.R.k hdim t.lam (hlat t) _ t.frame t'.frame (t'.lin * t.lin⁻¹) (hLF t) (hLt t) hL'
    (hGv t hG) (hGv t' hG') (CorankRelation.frame_mem_iff t t') hth
  have hinv : (t'.lin * t.lin⁻¹)⁻¹ = t.lin * t'.lin⁻¹ := by group
  rw [hinv] at hsym
  have hs' : s0 t.lam (lf D (X.Fu u)) t'.frame t.frame (t.lin * t'.lin⁻¹) D.R.k = 1 :=
    (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam (hlat t) _ t'.frame t.frame _ (hLF t) hL' (hGv t' hG')).2 hsym
  have hback : ∀ y : (VS D).V, (t'.lin * t.lin⁻¹) ((t.lin * t'.lin⁻¹) y) = y := fun y => by
    show t'.lin (t.lin.symm (t.lin (t'.lin.symm y))) = y
    simp
  refine ⟨?_, ?_⟩
  · show Formalism.L2.SG.TermOp.s0T t' t = 1
    unfold Formalism.L2.SG.TermOp.s0T
    rw [if_pos ⟨hlam.symm, hlam'.symm⟩, ← hlam]
    exact hs'
  · show Formalism.L2.SG.TermOp.scalT t' t
    refine ⟨⟨hlam.symm, hlam'.symm⟩, ?_, ?_⟩
    · rw [← hlam]; exact hs'
    · rw [← hlam]
      intro y2 hy2 y1 hy1 y2'' hy2'' y1' hy1' hd hd' al al'
      have hd1 : y1 - y2 ∈ Xsp (lf D (X.Fu u)) := by
        have := (Xsp (lf D (X.Fu u))).neg_mem hd
        simpa using this
      have hd2 : y2'' - (t'.lin * t.lin⁻¹) y1' ∈ Xsp t'.frame := by
        have h := (CorankRelation.frame_mem_iff t t' _).1 hd'
        rw [map_sub, hback] at h
        have := (Xsp t'.frame).neg_mem h
        simpa using this
      exact (hIS y1 hy1 y2 hy2 y1' hy1' y2'' hy2'' hd1 hd2 al al').symm

end GlobalTheory.ScalSymm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepPointBoundCuspidalIsometricIntertwinerFamily
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.DeepFamilyGap

theorem one_mem_NA (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) : (1 : I.GA) ∈ I.NA W := by
  unfold AutInst.NA
  refine ⟨fun v => ?_, ?_⟩
  · have hdet : IsUnit (I.P v).det := by
      first
      | exact (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
      | exact I.P_unit v
    have hg : I.P v * uMat ((1 : I.GA).1 v) * (I.P v)⁻¹ = 1 := by
      rw [show uMat ((1 : I.GA).1 v) = 1 from rfl, mul_one]
      exact Matrix.mul_nonsing_inv _ hdet
    rw [hg]
    unfold AutInst.InUnipRad
    simp
    intro x _
    unfold Formalism.UG.hform
    simp
  · have hf : I.fmat (1 : I.GA).2 = 1 := by
      first
      | rfl
      | simp
      | exact map_one _
    rw [hf]
    unfold AutInst.InUnipRad
    simp
    intro x _
    unfold Formalism.UG.hform
    simp

theorem self_mem_omega (I : AutInst) (x : I.GA) (W : Submodule I.E (Fin I.n → I.E)) {ρ : ℝ} (h : 0 ≤ ρ) :
    x ∈ omega I x W ρ := by
  refine ⟨rfl, fun _ => 0, fun _ => 0, fun v => ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (I.ε v)).zero_mem,
    (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (I.ε v)).zero_mem⟩, ?_, fun v => by simp, fun s t => ⟨1, ?_, fun v => ?_⟩⟩
  · simpa [GlobalTheory.SobolevBound.hs_eq_trace] using h
  · exact one_mem_NA I W
  · rw [smul_zero, smul_zero, NormedSpace.exp_zero, mul_one, mul_one]
    exact one_mul _

theorem beP_nonneg (n : ℕ) (b : ℝ) (P : ℕ) : 0 ≤ beP n b P := by
  unfold beP
  positivity

theorem monotone₂ (n : ℕ) (b : ℝ) {P Q : ℕ} (h : P ≤ Q) : beP n b P ≤ beP n b Q := by
  unfold beP
  have : (P : ℝ) ≤ Q := by exact_mod_cast h
  linarith

theorem iterate (B : RowsAut) (b ρ M β : ℝ) (P₀ : ℕ) (D : ℕ)
    (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ) (x : B.I.GA)
    (W : Submodule B.I.E (Fin B.I.n → B.I.E)) (hg : 1 ≤ B.g) (hW : B.I.IsIsot W)
    (hcov : ∀ ν : B.I.Ginf, ((ν, 1) : B.I.GA) ∈ B.I.NA W → ∃ γ ∈ B.I.GFset, ∃ k ∈ B.I.Kg B.g,
      ∃ y ∈ omega B.I x W ρ, ((ν, 1) : B.I.GA) * x = γ * y * (1, k))
    (hS : ∀ P, StepBoundAt B b P) (hR : ∀ i, IsReps B (T i) (Fr i))
    (hC : ∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (hβ : beP B.I.n b P₀ ≤ β)
    (h0 : ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P₀, ‖vv B Fr u y‖ ≤ M * ‖u‖) :
    ∀ k P : ℕ, P + k = P₀ → ∀ y ∈ omega B.I x W ρ, ∀ u ∈ VP B P,
      ‖vv B Fr u y‖ ≤ (2 * ρ * Real.sqrt B.I.f * β) ^ k * M * ‖u‖ := by
  have hβ0 : 0 ≤ β := le_trans (beP_nonneg _ _ _) hβ
  have hc0 : 0 ≤ 2 * ρ * Real.sqrt B.I.f * β :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hρ) (Real.sqrt_nonneg _)) hβ0
  intro k
  induction k with
  | zero =>
    intro P hP y hy u hu
    have hPP : P = P₀ := by simpa using hP
    subst hPP
    simpa using h0 y hy u hu
  | succ k ih =>
    intro P hP y hy u hu
    have hP' : (P + 1) + k = P₀ := by omega
    have hM' : 0 ≤ (2 * ρ * Real.sqrt B.I.f * β) ^ k * M := mul_nonneg (pow_nonneg hc0 _) hM
    have key := GlobalTheory.DeepStep.step_bound B b ρ ((2 * ρ * Real.sqrt B.I.f * β) ^ k * M) P D T Fr x W hg hW
      hcov (hS P) hR hC hM' (ih (P + 1) hP') y hy u hu
    have hle : beP B.I.n b P ≤ β := le_trans (monotone₂ _ _ (by omega : P ≤ P₀)) hβ
    calc ‖vv B Fr u y‖
        ≤ 2 * ρ * Real.sqrt B.I.f * beP B.I.n b P * ((2 * ρ * Real.sqrt B.I.f * β) ^ k * M) * ‖u‖ := key
      _ ≤ 2 * ρ * Real.sqrt B.I.f * β * ((2 * ρ * Real.sqrt B.I.f * β) ^ k * M) * ‖u‖ := by
          gcongr
      _ = (2 * ρ * Real.sqrt B.I.f * β) ^ (k + 1) * M * ‖u‖ := by ring

theorem mult_le {n τ t : ℝ} (hn : 1 ≤ n) (hτ : 0 < τ) (hτ1 : τ < 1 / 2) (ht : τ / 2 ≤ t) :
    1 + 4 * Real.sqrt n / t ^ 2 ≤ 17 * Real.sqrt n / τ ^ 2 := by
  have hs : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hn
  have ht0 : 0 < t := by linarith
  have hτt : τ ^ 2 ≤ 4 * t ^ 2 := by nlinarith
  have h1 : 4 * Real.sqrt n / t ^ 2 ≤ 16 * Real.sqrt n / τ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : 1 ≤ Real.sqrt n / τ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h3 : 17 * Real.sqrt n / τ ^ 2 = 16 * Real.sqrt n / τ ^ 2 + Real.sqrt n / τ ^ 2 := by ring
  linarith

theorem deep_bound_family : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ) (c : InfinitePlace B.I.F → ℝ) (x : B.I.GA) (D : ℕ) (T : Fin D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund)) (Fr : Fin D → B.Hs → B.I.GA → ℂ), 8 ≤ n₀ → 1 ≤ q → CountHyp B Cg n₀ d p q b → (∀ v, IsGauge (B.I.ε v) (c v)) → least B.I x < tauStar B q b → (∀ i, IsReps B (T i) (Fr i)) → (∀ i u, ‖T i u‖ = ‖u‖) → (∀ i u, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (T i u))) → ‖vv B Fr (B.tens B.w) x‖ ^ 2 ≤ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * Real.sqrt B.I.f * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ (16 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal := by
  intro B Cg n₀ d p q b c x D T Fr hn₀ hq hCH hc hτ hR hiso hcusp
  obtain ⟨hDS, -, hn₀n, hq2, -, -, hb2, -, -, hg, -⟩ := id hCH
  obtain ⟨-, hrd, hf, -, -, -, hrk, -, -, -, -, htau, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg n₀ d p q b hn₀ hCH
  obtain ⟨htau2, hb19⟩ := htau hq
  have hn8 : 8 ≤ B.I.n := le_trans hn₀ hn₀n
  have hn1 : 1 ≤ B.I.n := by omega
  have hτpos : 0 < least B.I x :=
    ((GlobalTheory.CountSteps.steps B.I x 1 one_pos).2.2.2.2.2.2.2.2 hn1).1
  have hτhalf : least B.I x < 1 / 2 := lt_trans hτ htau2
  have hτ1 : tau1 B.I x = least B.I x := min_eq_right hτhalf.le
  obtain ⟨W, hW, hcov⟩ := GlobalTheory.DeepCover.unipotent_orbit_cover B.I x B.g q hg hn1
    (fun v => (hrk v).le) hτhalf
  have hτX : least B.I x ≤ ((B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b)⁻¹ ^ (11 * q) := hτ.le
  have hex := GlobalTheory.deep_region_exponents B.I.n B.I.f q B.I.rd B.g b (least B.I x) hn8 hf hq hq2 hrd hb2
    (by exact_mod_cast hg) hτpos hτX
  have hrho : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) ≤ Real.log 2 := hex.1
  have hρ0 : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh
    have hg0 : (1 : ℝ) ≤ B.g := by exact_mod_cast hg
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (Real.sqrt_nonneg _)) (by linarith)) (by linarith)) (Real.rpow_nonneg (by linarith) _))
      (by norm_num)
  have hS : ∀ P, StepBoundAt B b P := GlobalTheory.T.discreteSeries_stepBound_of_countingHypotheses B Cg n₀ d p q b hn₀ hCH
  have hβ : beP B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + B.I.n ^ 2 * B.I.f) =
      GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) := rfl
  have hβ0 : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) := by
    rw [← hβ]; exact beP_nonneg _ _ _
  have hβle : beP B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) ≤
      GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) := by
    rw [← hβ]; exact monotone₂ _ _ (Nat.le_add_right _ _)
  have hc0 : 0 < ∏ v, c v := Finset.prod_pos fun v _ => GlobalTheory.SobolevBound.gauge_pos (hc v)
  have hN : B.I.n ^ 2 * B.I.f = GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B := rfl
  have hK0 : 0 ≤ (6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _)
      (Real.exp_pos _).le) (pow_nonneg (by positivity) _)) (Nat.cast_nonneg _)) hc0.le)
      ENNReal.toReal_nonneg
  have h0 : ∀ y ∈ omega B.I x W (GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x)),
      ∀ u ∈ VP B (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B), ‖vv B Fr u y‖ ≤
        Real.sqrt ((6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal) * ‖u‖ := by
    intro y hy u hu
    have hs := GlobalTheory.SobolevBound.sobolev_bound B b c (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) D T Fr hn8 hg hb19 hc hS
      hR hiso y u hu
    rw [hβ, hN] at hs
    have ht : least B.I x / 2 ≤ tau1 B.I y := by
      rw [← hτ1]; exact GlobalTheory.OmegaLeast.half_truncatedLeastLatticeSize_le_unipotentNeighbourhood B.I x W _ hn1 hrho y hy
    have hm := mult_le (n := (B.I.n : ℝ)) (by exact_mod_cast hn1) hτpos hτhalf ht
    have hle : ‖vv B Fr u y‖ ^ 2 ≤ ((6 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B)) ^ GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * Real.exp B.I.f * (17 * Real.sqrt B.I.n / least B.I x ^ 2) ^ (2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) * (D : ℝ) * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal) * ‖u‖ ^ 2 := by
      refine hs.trans ?_
      gcongr
    have := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hK0, Real.sqrt_sq (norm_nonneg _)] at this
  have key := GlobalTheory.DeepFamilyGap.iterate B b (GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x)) _ _
    (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) D T Fr x W hg hW hcov hS hR hcusp hρ0 (Real.sqrt_nonneg _) hβle h0
    (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) 0 (by simp) x (self_mem_omega B.I x W hρ0) (B.tens B.w)
    (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.tens_w_mem B hDS 0).1
  rw [(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.tens_w_mem B hDS 0).2, mul_one] at key
  have hA0 : 0 ≤ 2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * Real.sqrt B.I.f *
      GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B + GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hρ0) (Real.sqrt_nonneg _)) hβ0
  have hsq := pow_le_pow_left₀ (norm_nonneg _) key 2
  rw [mul_pow, ← pow_mul, Real.sq_sqrt hK0] at hsq
  refine hsq.trans (le_of_eq ?_)
  rw [show 8 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B * 2 = 16 * q * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B by ring]
  ring

end GlobalTheory.DeepFamilyGap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCountingOfFiniteAndBounds
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CountSum

theorem countHyp_mono {B : RowsAut} {Cg : ℝ} {n₀ n₁ : ℕ} {d : InfinitePlace B.I.F → ℝ} {p q : ℕ} {b : ℝ}
    (h : CountHyp B Cg n₀ d p q b) (hn : n₁ ≤ n₀) : CountHyp B Cg n₁ d p q b :=
  ⟨h.1, h.2.1, hn.trans h.2.2.1, h.2.2.2⟩

theorem countingTheorem_of_finite_of_bounds :
    (∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ →
      CountHyp B Cg n₀ d p q b → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re)) →
    GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Deep.PtBound →
    GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate → GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.FarModerate → GlobalTheory.IndefiniteRowSideFullHecke.RareFlags.FlagRare →
    GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.DeepBound → GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem := by
  intro hfinC hflag hpt hnear hfar hrare hdeep Cg
  by_cases hC : 0 ≤ Cg
  swap
  · exact ⟨8, fun B d p q b h => absurd (GlobalTheory.Dec.countHyp_numerics B Cg 8 d p q b le_rfl h).1 hC⟩
  obtain ⟨n₁, hn₁⟩ := hnear Cg hC
  obtain ⟨n₂, hn₂⟩ := hfar Cg hC
  obtain ⟨n₃, hn₃⟩ := hrare
  obtain ⟨n₄, hn₄⟩ := hdeep Cg hC
  refine ⟨8 + n₁ + n₂ + n₃ + n₄ + ⌈Real.exp 15⌉₊, fun B d p q b H => ?_⟩
  have hfin := hfinC B Cg _ d p q b (by omega) H
  refine ⟨hfin, ?_⟩
  obtain ⟨-, -, hf1, -, hpq, h2q, hrk, hmin, hd, -, -, hts, h, -, hgap, -, h32, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg _ d p q b (by omega) H
  have H1 := countHyp_mono H (n₁ := n₁) (by omega)
  have H2 := countHyp_mono H (n₁ := n₂) (by omega)
  have H4 := countHyp_mono H (n₁ := n₄) (by omega)
  obtain ⟨hDS, hsig, hn, hq2, hrd, hlf, -, -, -, hg, -, hpr, h4, hsp, -⟩ := H
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have e := GlobalTheory.T.definiteUnitaryGroup_count_eq_mainTerm B d p ⟨hDS, hsig, by omega, hg, hpr, h4, hsp⟩ hfin
    rw [← e, sub_self, abs_zero]
    positivity
  have hn1 : 1 ≤ B.I.n := by omega
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  have : BorelSpace B.I.GA := inferInstance
  obtain ⟨-, -, hphe1, him, hre, -, hloc⟩ := hpt B d p q h hDS hsig hgap (by rw [hmin]; exact h120)
  obtain ⟨-, hv0, hvT, -⟩ := hflag B.I B.μf B.fund B.fund_spec p q hsig h2q 1 (fun _ => 1) le_rfl
    (fun _ => le_rfl) (by simpa using Nat.succ_le_of_lt hq) ∅ MeasurableSet.empty (Set.empty_subset _)
  obtain ⟨hc, hle, hint⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hDS hloc
  have hI : Integrable (ph B d) (muInf B.I) := by
    have h0 := hint 0 le_rfl (fun v => Or.inr (by
      have h1 := h32 v
      rw [hrk v] at h1 ⊢
      have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 (by exact_mod_cast hq)
      have hqn : (q : ℝ) < B.I.n := by exact_mod_cast (by omega : q < B.I.n)
      have hn0 : (0 : ℝ) < B.I.n := by exact_mod_cast hn1
      have := mul_lt_mul_of_pos_left hqn (mul_pos hs hn0)
      nlinarith))
    simp only [zero_mul, Real.exp_zero, mul_one] at h0
    exact h0.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hle)
  obtain ⟨-, -, ⟨T, hT⟩, -⟩ := GlobalTheory.GlobProj.globalProj_holds B d hDS hI
  obtain ⟨-, Fc, -, -, -, hexp, hKi, hD, -⟩ := GlobalTheory.T.kernelB' B d h hDS hn1 hloc h32 hfin T hT
  obtain ⟨hsum, -⟩ := GlobalTheory.T.automorphicKernel_convergence_properties B d h hDS hn1 hloc h32
  obtain ⟨hmeas, hsplit⟩ := GlobalTheory.NearMeas.nearAbs_measurable_and_split B d hDS
  have hcl : Continuous (least B.I) := (GlobalTheory.LeastVar.least_variation_continuity B.I hn1).2.1
  set μ := (B.I.muA B.μf).restrict B.fund with hμ
  have : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ]; exact hvT⟩
  have hM : MeasurableSet {x | tauStar B q b ≤ least B.I x} :=
    (isClosed_le continuous_const hcl).measurableSet
  have hvol : 0 < B.I.vol B.μf B.fund := ENNReal.toReal_pos hv0.ne' hvT.ne
  have hc0 : 0 ≤ (∏ v, d v) * (B.e 1).re := mul_nonneg hd.le hre
  have hmain : mainTerm B d = (∏ v, d v) * (B.e 1).re * B.I.vol B.μf B.fund := by
    unfold mainTerm AutInst.Dstar; ring
  have hm0 : 0 ≤ mainTerm B d := hmain ▸ mul_nonneg hc0 hvol.le
  have e1 : {x | tauStar B q b ≤ least B.I x} ∩ B.fund = {x | x ∈ B.fund ∧ tauStar B q b ≤ least B.I x} :=
    Set.inter_comm _ _
  have e2 : {x | tauStar B q b ≤ least B.I x}ᶜ ∩ B.fund = GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b := by
    ext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet, and_comm]
  have key := GlobalTheory.abs_integral_sub_const_mul_le_of_split B.I.GA μ {x | tauStar B q b ≤ least B.I x}
    (fun x => (kern B.I (phe B d) x x).re) (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d)
    ((∏ v, d v) * (B.e 1).re) (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound B d)
    (Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) * mainTerm B d)
    ((B.D : ℝ) * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) hM hKi.re
    (fun x => by
      simp only [hexp, Complex.re_sum]
      refine Finset.sum_nonneg fun i _ => ?_
      rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
      exact Complex.normSq_nonneg _)
    hmeas hc0 (mul_nonneg (Real.exp_pos _).le hm0) (mul_nonneg (Real.exp_pos _).le hm0) (by positivity)
    (fun x _ => by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hsplit x (hsum x x).1)
      refine le_trans (le_of_eq ?_) (Complex.abs_re_le_norm _)
      rw [Complex.sub_re, hphe1, Complex.re_ofReal_mul])
    (by rw [hμ, Measure.restrict_restrict hM, e1]; exact hn₁ B d p q b hq H1)
    (by rw [hμ, Measure.restrict_restrict hM, e1]; exact hn₂ B d p q b hq H2)
    (by rw [hμ, Measure.restrict_restrict hM.compl, e2]; exact hn₄ B d p q b hq H4)
  have hKD : ∫ x, (kern B.I (phe B d) x x).re ∂μ = (B.D : ℝ) := by
    have := integral_re hKi
    rw [hD] at this
    simpa using this
  have hU : (μ Set.univ).toReal = B.I.vol B.μf B.fund := by
    rw [hμ, Measure.restrict_apply_univ]; rfl
  have hP : (μ {x | tauStar B q b ≤ least B.I x}ᶜ).toReal ≤
      Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log B.I.n)) * B.I.vol B.μf B.fund := by
    have h1 := hn₃ B p q hsig (by omega) hq2 hrd hlf
    unfold prob at h1
    rw [div_le_iff₀ hvol] at h1
    refine le_trans ?_ h1
    rw [hμ, Measure.restrict_apply hM.compl]
    refine ENNReal.toReal_mono ((measure_mono Set.inter_subset_right).trans_lt hvT).ne
      (measure_mono (Set.inter_subset_inter_left _ fun x hx => ?_))
    have hx' : ¬ tauStar B q b ≤ least B.I x := hx
    exact lt_trans (not_le.1 hx') (hts hq).1
  rw [hKD, hU, ← hmain] at key
  have hP' := mul_le_mul_of_nonneg_left hP hc0
  have hne : Real.exp 15 ≤ (B.I.n : ℝ) := Nat.ceil_le.1 (by omega)
  have fin := GlobalTheory.abs_sub_le_exp_neg_sixteenth_mul (B.D : ℝ) (mainTerm B d) B.I.n B.I.f (by positivity) hm0 hne
    (by exact_mod_cast hf1) (by
      refine key.trans ?_
      unfold GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound
      simp only [neg_mul]
      rw [hmain] at *
      nlinarith [hP'])
  simpa only [neg_mul] using fin

end GlobalTheory.CountSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LevelCharacterUnipotentPartOfAdmissibilityWitnesStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacter_unipotentPart_of_admissibilityWitness : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ (t : TauC Y u u') (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)), AdmWit t.lam (gS D) (lf D (X.Fu u)) t.frame ξ → chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.pt) = (Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))))⁻¹ := by
  first | exact @GlobalTheory.AdmWitChar.chiN_kOf_eq_inv_psiInf_sgUp | exact GlobalTheory.AdmWitChar.chiN_kOf_eq_inv_psiInf_sgUp | (intros; apply GlobalTheory.AdmWitChar.chiN_kOf_eq_inv_psiInf_sgUp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRatioStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.MassAtRecord

theorem massRatio_at_record : ∀ D : D7, UnitaryVolumeMass.stMassRatio D := fun D => by
  letI := D.host.cmStar
  exact fun j hj V V' _ _ _ _ _ _ _ _ f f' L L' hs hs' ho ho' =>
    GlobalTheory.T.siegel_massRatio_unimodular_definite D.host.E D.sp.cm.cmUnram j hj V V' f f' L L' hs hs' ho ho'

end GlobalTheory.MassAtRecord
end

