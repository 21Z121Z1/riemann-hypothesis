import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0417
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0116
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0053
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0428
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0174
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0425
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0327
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0270
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0426
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0427

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMatrixMemUnipotentStabilizerFrameGram
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

noncomputable section

open scoped Classical

namespace GlobalTheory.FrameStab

open Formalism.L2.SG.RealObj

variable {n m r : ℕ}

def colMat (f : Fin m → Fin n → ℂ) : Matrix (Fin n) (Fin m) ℂ := Matrix.of fun i a => f a i

theorem isMatOn_iff (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin m → Fin n → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.LoopAct.IsMatOn g f M ↔ g * colMat f = colMat f * M := by
  constructor
  · intro h
    ext i b
    have := congrFun (h b) i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, colMat, Matrix.of_apply, this, mul_comm]
  · intro h b
    ext i
    have := congrFun (congrFun h i) b
    simp only [Matrix.mul_apply, colMat, Matrix.of_apply] at this
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, this, mul_comm]

theorem zhat_eq (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (G : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.L2.SG.RealObj.Zhat ε f f' G = (colMat f)ᴴ * Formalism.REAL.Jm ε * G * colMat f' := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc]
  ext a b
  simp only [Formalism.L2.SG.RealObj.Zhat, Formalism.L2.SG.HidaSetting.hJ, Matrix.mul_apply, Matrix.mulVec, dotProduct, colMat,
    Matrix.of_apply, Matrix.conjTranspose_apply, Pi.star_apply]

theorem conjTranspose_mul_zhat_mul {ε : Fin n → Bool} {f f' : Fin (r + 1) → Fin n → ℂ}
    {Y G Gi : Matrix (Fin n) (Fin n) ℂ} {P M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hY : Yᴴ * Formalism.REAL.Jm ε * Y = Formalism.REAL.Jm ε) (hG : G * Gi = 1)
    (hP : GlobalTheory.LoopAct.IsMatOn Y f P) (hM : GlobalTheory.LoopAct.IsMatOn (Gi * Y * G) f' M) :
    Pᴴ * (Formalism.L2.SG.RealObj.Zhat ε f f' G * M) = Formalism.L2.SG.RealObj.Zhat ε f f' G := by
  rw [isMatOn_iff] at hP hM
  rw [zhat_eq]
  calc Pᴴ * ((colMat f)ᴴ * Formalism.REAL.Jm ε * G * colMat f' * M)
      = (colMat f * P)ᴴ * Formalism.REAL.Jm ε * G * (colMat f' * M) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (Y * colMat f)ᴴ * Formalism.REAL.Jm ε * G * (Gi * Y * G * colMat f') := by rw [hP, hM]
    _ = (colMat f)ᴴ * (Yᴴ * Formalism.REAL.Jm ε * ((G * Gi) * Y)) * G * colMat f' := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (colMat f)ᴴ * Formalism.REAL.Jm ε * G * colMat f' := by
        rw [hG, Matrix.one_mul, hY]

theorem isLoUni_conjTranspose {N : ℕ} {P : Matrix (Fin N) (Fin N) ℂ} (h : Formalism.MainNotions.S.IsUpUni P) :
    Formalism.MainNotions.S.IsLoUni Pᴴ := by
  intro i j
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [Matrix.conjTranspose_apply, (h j i).1 hij, star_zero]
  · rw [Matrix.conjTranspose_apply, (h j i).2 hij.symm, star_one]

theorem mem_stabU_of_conjTranspose_mul {N : ℕ} {Z P M : Matrix (Fin N) (Fin N) ℂ} (hZ : IsUnit Z.det)
    (hP : Formalism.MainNotions.S.IsUpUni P) (hM : Formalism.MainNotions.S.IsUpUni M) (h : Pᴴ * (Z * M) = Z) :
    M ∈ GlobalTheory.LoopV.stabU Z := by
  refine ⟨hM, ?_⟩
  have e : Pᴴ * (Z * M * Z⁻¹) = 1 := by
    rw [← Matrix.mul_assoc, h, Matrix.mul_nonsing_inv _ hZ]
  rw [← Matrix.inv_eq_right_inv e]
  exact (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv (isLoUni_conjTranspose hP)).1

end GlobalTheory.FrameStab

namespace GlobalTheory.FrameStab

variable {n r : ℕ}

theorem exists_coeff_of_mem_spanLt {e : Fin r → Fin n → ℂ} {k : ℕ} {x : Fin n → ℂ}
    (hx : x ∈ Formalism.L2.SG.HidaSetting.spanLt e k) :
    ∃ c : Fin r → ℂ, (∀ b : Fin r, ¬ b.1 < k → c b = 0) ∧ x = ∑ b, c b • e b := by
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).1 hx
  refine ⟨l, fun b hb => ?_, ?_⟩
  · exact (Finsupp.mem_supported' ℂ l).1 hl b hb
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; exact zero_smul _ _

theorem exists_isUpUni_isMatOn {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.L2.SG.HidaSetting.InS e z Y) :
    ∃ P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, Formalism.MainNotions.S.IsUpUni P ∧
      GlobalTheory.LoopAct.IsMatOn Y (Formalism.L2.SG.RealObj.fam e z) P := by
  choose ca hca0 hcae using fun a : Fin r => exists_coeff_of_mem_spanLt (h.1 a)
  obtain ⟨cz, -, hcz⟩ := exists_coeff_of_mem_spanLt h.2
  let Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := fun i j =>
    Fin.lastCases (motive := fun _ => ℂ) 0
      (fun c : Fin r => Fin.lastCases (motive := fun _ => ℂ) (cz c) (fun a : Fin r => ca a c) j) i
  have hQl : ∀ j, Q (Fin.last r) j = 0 := fun j => by simp [Q]
  have hQcl : ∀ c, Q (Fin.castSucc c) (Fin.last r) = cz c := fun c => by simp [Q]
  have hQcc : ∀ c a, Q (Fin.castSucc c) (Fin.castSucc a) = ca a c := fun c a => by simp [Q]
  refine ⟨1 + Q, fun i j => ?_, fun b => ?_⟩
  · refine Fin.lastCases ?_ (fun c => ?_) i
    · refine ⟨fun hj => ?_, fun hj => ?_⟩
      · rw [Matrix.add_apply, hQl, Matrix.one_apply_ne (ne_of_lt hj).symm, add_zero]
      · rw [Matrix.add_apply, hQl, hj, Matrix.one_apply_eq, add_zero]
    · refine Fin.lastCases ?_ (fun a => ?_) j
      · exact ⟨fun hj => absurd hj (not_lt.2 (Fin.castSucc_lt_last c).le),
          fun hj => absurd hj (Fin.castSucc_lt_last c).ne⟩
      · refine ⟨fun hj => ?_, fun hj => ?_⟩
        · rw [Matrix.add_apply, hQcc, Matrix.one_apply_ne (ne_of_lt hj).symm, zero_add]
          exact hca0 a c (not_lt.2 (Fin.castSucc_lt_castSucc_iff.1 hj).le)
        · rw [Matrix.add_apply, hQcc, hj, Matrix.one_apply_eq, Fin.castSucc_inj.1 hj]
          rw [hca0 a a (lt_irrefl _), add_zero]
  · rw [Fin.sum_univ_castSucc]
    simp only [Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc, Fin.snoc_last, Matrix.add_apply, add_smul,
      Finset.sum_add_distrib, hQl, zero_smul, add_zero]
    refine Fin.lastCases ?_ (fun a => ?_) b
    · simp only [Fin.snoc_last, hQcl, Matrix.one_apply_eq, one_smul,
        Matrix.one_apply_ne (Fin.castSucc_lt_last _).ne, zero_smul, Finset.sum_const_zero, zero_add]
      rw [← hcz, Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
    · simp only [Fin.snoc_castSucc, hQcc, Matrix.one_apply_ne (Fin.castSucc_lt_last _).ne', zero_smul,
        add_zero]
      have e1 : ∑ x : Fin r, (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (Fin.castSucc x) (Fin.castSucc a) • e x
          = e a := by
        simp only [Matrix.one_apply, Fin.castSucc_inj, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [e1, ← hcae a, Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]

end GlobalTheory.FrameStab

namespace GlobalTheory.FrameStab

theorem frameMat_mem_stabU : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ y : X.B.I.Ginf) (v : NumberField.InfinitePlace X.B.I.F) (M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), y ∈ Formalism.L2.SG.RealObj.StInf X u u' γ → IsUpUni M → GlobalTheory.LoopAct.IsMatOn (uMat ((γ⁻¹ * y * γ) v)) (Formalism.L2.SG.RealObj.frm X u' 1 v) M → IsUnit (Formalism.L2.SG.RealObj.ZX X u u' 1 γ v).det → M ∈ GlobalTheory.LoopV.stabU (Formalism.L2.SG.RealObj.ZX X u u' 1 γ v) := by
  intro D X u u' γ y v M hy hMu hM hZ
  obtain ⟨P, hPu, hP⟩ := exists_isUpUni_isMatOn ((hy.1 v).1)
  have hf : Formalism.L2.SG.RealObj.frm X u 1 v = Formalism.L2.SG.RealObj.fam
      (fun a => Formalism.L2.SG.HidaSetting.rv X.B.I v (X.eR a)) (Formalism.L2.SG.HidaSetting.rv X.B.I v (X.zR u)) := by
    funext a
    simp [Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc]
  rw [← hf] at hP
  have hY : (uMat (y v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat (y v) = Formalism.REAL.Jm (X.B.I.ε v) := (y v).2
  have hG : uMat (γ v) * uMat (γ⁻¹ v) = 1 := by
    show uMat ((γ * γ⁻¹) v) = 1
    rw [mul_inv_cancel]
    rfl
  exact mem_stabU_of_conjTranspose_mul hZ hPu hMu (conjTranspose_mul_zhat_mul hY hG hP hM)

end GlobalTheory.FrameStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapNearPlaceParameterHalfNoncompactGap
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapNear

theorem gap_near : ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → m₀ ≤ D.R.m → ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r → GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2) := by
  intro Cn
  refine ⟨max Cn 1000, fun D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl hm₀ τ lam' hl => ?_⟩
  have hdim := dimS_eq D.R
  have hrr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hmk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hnR : (D.R.r : ℝ) = 2 * D.R.rS + D.R.k + 1 := by rw [← hdim]; push_cast; ring
  have hmC : Cn ≤ (D.R.m : ℝ) := le_trans (le_max_left _ _) hm₀
  have hm1000 : (1000 : ℝ) ≤ D.R.m := le_trans (le_max_right _ _) hm₀
  have hkr : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : D.R.k ≤ D.R.r)
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : D.R.m ≤ D.R.r)
  have hr1000 : (1000 : ℝ) ≤ D.R.r := le_trans hm1000 hmr
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _

  have hsize : Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r ≤ (D.R.r : ℝ) ^ 19 / 2 := by
    have h1 : Cn * D.R.k * (D.R.m : ℝ) ^ 3 ≤ (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 := by
      have := mul_le_mul_of_nonneg_right hmC (show (0 : ℝ) ≤ D.R.k * (D.R.m : ℝ) ^ 3 by positivity)
      linarith [show Cn * D.R.k * (D.R.m : ℝ) ^ 3 = Cn * (D.R.k * (D.R.m : ℝ) ^ 3) by ring,
        show (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 = (D.R.m : ℝ) * (D.R.k * (D.R.m : ℝ) ^ 3) by ring]
    have h2 : (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 5 := by
      have e : (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 = D.R.k * (D.R.m : ℝ) ^ 4 := by ring
      have e' : (D.R.r : ℝ) ^ 5 = D.R.r * (D.R.r : ℝ) ^ 4 := by ring
      rw [e, e']
      exact mul_le_mul hkr (pow_le_pow_left₀ (by positivity) hmr 4) (by positivity) (by positivity)
    have h3 : (D.R.r : ℝ) ≤ (D.R.r : ℝ) ^ 5 := le_self_pow₀ (by linarith) (by norm_num)
    have h4 : (4 : ℝ) ≤ (D.R.r : ℝ) ^ 14 := le_trans (by norm_num) (le_trans hr1000 (le_self_pow₀ (by linarith) (by norm_num)))
    have h5 : 4 * (D.R.r : ℝ) ^ 5 ≤ (D.R.r : ℝ) ^ 19 := by
      have := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ (D.R.r : ℝ) ^ 5 by positivity)
      linarith [show (D.R.r : ℝ) ^ 5 * (D.R.r : ℝ) ^ 14 = (D.R.r : ℝ) ^ 19 by ring]
    linarith

  have hf : 1 ≤ D.R.f := by
    have := D.R.m_le_f
    unfold Ranks.f Ranks.n
    omega
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hG0 := Formalism.MainNotions.BridgeLemma.szh_gap hZ.1 τ
  have hG : (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have hf' : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast hf)
    have h5 : (1 : ℝ) ≤ Cl * ((D.R.f : ℝ) ^ 5 * large₂.sc.L) :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_mul_of_one_le_of_one_le hf' hL)
    have h6 := mul_le_mul_of_nonneg_left h5 (show (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 by positivity)
    have h7 : (D.R.r : ℝ) ^ 19 * (Cl * ((D.R.f : ℝ) ^ 5 * large₂.sc.L)) =
      Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by ring
    linarith
  refine ⟨fun a b hne => ?_, ?_⟩
  · have hab : a ≠ b := fun e => hne (e ▸ rfl)
    have g := hG0 a b hne
    change _ ≤ |lamD D τ a - lamD D τ b| at g
    have hpair : |lam' a - lamD D τ a| + |lam' b - lamD D τ b| ≤ l1dist lam' (lamD D τ) := by
      unfold l1dist
      rw [← Finset.sum_pair (f := fun i => |lam' i - lamD D τ i|) hab]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => abs_nonneg _)
    have tri : |lamD D τ a - lamD D τ b| ≤ |lam' a - lam' b| + |lam' a - lamD D τ a| + |lam' b - lamD D τ b| := by
      rw [abs_le]
      constructor <;>
      linarith [le_abs_self (lam' a - lam' b), neg_abs_le (lam' a - lam' b), le_abs_self (lam' a - lamD D τ a),
        neg_abs_le (lam' a - lamD D τ a), le_abs_self (lam' b - lamD D τ b), neg_abs_le (lam' b - lamD D τ b)]
    linarith
  · have hok := (GlobalTheory.SizeNum.gapOK D.R.k D.R.rS D.R.r hnR (by omega) hr1000).1
    exact GlobalTheory.NumFam.gapOK_mono D.R.k D.R.rS (by linarith [show (0:ℝ) ≤ (D.R.r : ℝ) ^ 19 by positivity]) hok

end GlobalTheory.GapNear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianVolumeDependsOnlyOnFieldSignature
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.VolInvariant

theorem hform_eq {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J y x = star y ⬝ᵥ (J *ᵥ x) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem eq_or_conj {E : Type} [Field E] [CharZero E] [StarRing E] (φ ψ : E →+* ℂ)
    (hψ : ∀ a, ψ (star a) = starRingEnd ℂ (ψ a)) (h : ∀ a, star a = a → φ a = ψ a) :
    φ = ψ ∨ φ = (starRingEnd ℂ).comp ψ := by
  by_cases hall : ∀ a : E, star a = a
  · left; ext a; exact h a (hall a)
  push Not at hall
  obtain ⟨b, hb⟩ := hall
  set θ := b - star b with hθ
  have hθ0 : θ ≠ 0 := sub_ne_zero.2 hb.symm
  have hs : star θ = -θ := by simp [hθ]
  have hsq : φ θ ^ 2 = ψ θ ^ 2 := by
    rw [← map_pow, ← map_pow]; apply h; rw [star_pow, hs]; ring
  have h2 : star (2 : E) = 2 := star_ofNat 2
  have dec : ∀ a : E, ∃ u w : E, star u = u ∧ star w = w ∧ a = u + θ * w := by
    intro a
    refine ⟨(a + star a) / 2, (a - star a) / (2 * θ), ?_, ?_, ?_⟩
    · rw [star_div₀, star_add, star_star, h2, add_comm]
    · rw [star_div₀, star_sub, star_star, star_mul', h2, hs]; field_simp; ring
    · field_simp; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h1 | h1
  · left; ext a
    obtain ⟨u, w, hu, hw, rfl⟩ := dec a
    simp only [map_add, map_mul, h u hu, h w hw, h1]
  · right; ext a
    obtain ⟨u, w, hu, hw, rfl⟩ := dec a
    rw [RingHom.comp_apply, ← hψ, star_add, star_mul', hu, hw, hs]
    simp only [map_add, map_mul, map_neg, h u hu, h w hw, h1]

theorem hasSignature_all (I : AutInst) {p q : ℕ} (h : HasSig I p q) (φ : I.E →+* ℂ) :
    Formalism.UG.HasSignature (I.J.map φ) p q := by
  set v : InfinitePlace I.F := InfinitePlace.mk (φ.comp (algebraMap I.F I.E)) with hv
  have hc := I.cm.cmUnram.2.1
  have hag : ∀ a, star a = a → φ a = I.φ v a := by
    intro a ha
    obtain ⟨c, rfl⟩ := (I.cm.fixed a).1 ha
    rw [I.φ_over]
    rcases InfinitePlace.embedding_mk_eq (φ.comp (algebraMap I.F I.E)) with h1 | h1
    · rw [hv, h1]; rfl
    · rw [hv, h1, ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hc, ha]
  rw [← (h v).1, ← (h v).2]
  rcases eq_or_conj φ (I.φ v) (hc _) hag with h1 | h1
  · have e0 : I.J.map φ = I.J.map (I.φ v) := congrArg (fun ψ : I.E →+* ℂ => I.J.map ψ) h1
    rw [e0]
    exact GlobalTheory.AutInhab.hasSignature_inst I v
  · refine GlobalTheory.AutInhab.hasSignature_of_frame (P := (I.P v).map (starRingEnd ℂ)) ?_ ?_
    · exact (I.P_unit v).map (starRingEnd ℂ).mapMatrix
    · have := congrArg (fun M => Matrix.map M (starRingEnd ℂ)) (I.P_spec v)
      simp only [Matrix.map_mul] at this
      have e1 : I.J.map φ = (I.J.map (I.φ v)).map (starRingEnd ℂ) := by
        ext i j; conv_lhs => rw [h1]
        rfl
      have e2 : ((I.P v).map (starRingEnd ℂ))ᴴ = ((I.P v)ᴴ).map (starRingEnd ℂ) := by
        ext i j; rfl
      rw [e1, e2, this]
      ext i j
      simp only [Formalism.REAL.Jm, Matrix.map_apply, Matrix.diagonal_apply]
      split_ifs <;> simp

section Transport

variable {E E' : Type} [Field E] [NumberField E] [StarRing E] [Field E'] [NumberField E'] [StarRing E'] {n : ℕ}

theorem exists_image (e : E' ≃+* E) (he : ∀ y, e (star y) = star (e y)) (J : Matrix (Fin n) (Fin n) E)
    (J' : Matrix (Fin n) (Fin n) E') (A : GL (Fin n) E)
    (hA : (A : Matrix (Fin n) (Fin n) E)ᴴ * J * (A : Matrix (Fin n) (Fin n) E) = J'.map e)
    (L : Submodule (𝓞 E') (Fin n → E')) (hL : Submodule.IsLattice E' L)
    (hd : ∀ x, x ∈ L ↔ ∀ y ∈ L, star y ⬝ᵥ (J' *ᵥ x) ∈ (algebraMap (𝓞 E') E').range) :
    ∃ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Λ ∧
      (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) ∧
      ∀ y : Fin n → E', y ∈ L ↔ (A : Matrix (Fin n) (Fin n) E) *ᵥ (fun i => e (y i)) ∈ Λ := by
  let σ : 𝓞 E' →+* 𝓞 E := (RingOfIntegers.mapRingEquiv e : 𝓞 E' ≃+* 𝓞 E)
  haveI : RingHomSurjective σ := ⟨(RingOfIntegers.mapRingEquiv e).surjective⟩
  haveI : RingHomSurjective (e : E' →+* E) := ⟨e.surjective⟩
  let g : (Fin n → E') →ₛₗ[(e : E' →+* E)] (Fin n → E) :=
    { toFun := fun y => (A : Matrix (Fin n) (Fin n) E) *ᵥ (fun i => e (y i))
      map_add' := fun x y => by
        rw [← Matrix.mulVec_add]; congr 1; ext i; simp
      map_smul' := fun c x => by
        rw [← Matrix.mulVec_smul]; congr 1; ext i; simp }
  let f : (Fin n → E') →ₛₗ[σ] (Fin n → E) :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun c x => g.map_smulₛₗ (c : E') x }
  have hf : ∀ y, f y = (A : Matrix (Fin n) (Fin n) E) *ᵥ (fun i => e (y i)) := fun _ => rfl
  have hinj : Function.Injective f := by
    intro x y hxy
    have := congrArg (fun z => ((A⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ z) hxy
    simp only [hf, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
    ext i; exact e.injective (congrFun this i)
  have hsurj : Function.Surjective f := by
    intro x
    refine ⟨fun i => e.symm ((((A⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x) i), ?_⟩
    simp only [hf, RingEquiv.apply_symm_apply]
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hform : ∀ x y, star (f y) ⬝ᵥ (J *ᵥ f x) = e (star y ⬝ᵥ (J' *ᵥ x)) := by
    intro x y
    rw [hf, hf, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA]
    simp [dotProduct, Matrix.mulVec, he]
  have hint : ∀ a : E', e a ∈ (algebraMap (𝓞 E) E).range ↔ a ∈ (algebraMap (𝓞 E') E').range := by
    intro a
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨(RingOfIntegers.mapRingEquiv e).symm c, e.injective ?_⟩
      rw [← hc]
      exact e.apply_symm_apply _
    · rintro ⟨c, rfl⟩
      exact ⟨σ c, rfl⟩
  have hmem : ∀ y, y ∈ L ↔ f y ∈ L.map f := fun y =>
    ⟨fun h => ⟨y, h, rfl⟩, fun ⟨z, hz, h⟩ => hinj h ▸ hz⟩
  refine ⟨L.map f, ⟨hL.fg.map f, ?_⟩, ?_, hmem⟩
  · have : ((L.map f : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = g '' (L : Set (Fin n → E')) := rfl
    rw [this, ← Submodule.map_span, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact hsurj
  · intro x
    obtain ⟨x, rfl⟩ := hsurj x
    rw [← hmem, hd]
    constructor
    · rintro h _ ⟨y, hy, rfl⟩
      rw [hform, hint]; exact h y hy
    · intro h y hy
      rw [← hint, ← hform]; exact h _ ⟨y, hy, rfl⟩

theorem exists_isometry (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) (e : E' ≃+* E) (he : ∀ y, e (star y) = star (e y)) {n' : ℕ}
    (hn : n' = n) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin n') (Fin n') E')
    (hJ : Jᴴ = J) (hJ' : J'ᴴ = J') (hdet : J.det ≠ 0) (hdet' : J'.det ≠ 0)
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (hd : ∀ x, x ∈ L ↔ ∀ y ∈ L, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range)
    (L' : Submodule (𝓞 E') (Fin n' → E')) (hL' : Submodule.IsLattice E' L')
    (hd' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', star y ⬝ᵥ (J' *ᵥ x) ∈ (algebraMap (𝓞 E') E').range)
    {p q : ℕ} (hs : ∀ φ : E →+* ℂ, Formalism.UG.HasSignature (J.map φ) p q)
    (hs' : ∀ φ : E' →+* ℂ, Formalism.UG.HasSignature (J'.map φ) p q) :
    ∃ (A : Matrix (Fin n) (Fin n') E) (Λ : Submodule (𝓞 E) (Fin n → E)), Aᴴ * J * A = J'.map e ∧
      Submodule.IsLattice E Λ ∧
      (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) ∧
      ∀ y : Fin n' → E', y ∈ L' ↔ A *ᵥ (fun i => e (y i)) ∈ Λ := by
  subst hn
  obtain ⟨Λ₁, h1, h2, -⟩ := exists_image e he (J'.map e) J' 1 (by simp) L' hL' hd'
  have hh : (J'.map e)ᴴ = J'.map e := by
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← he, ← Matrix.conjTranspose_apply, hJ']
  have hde : (J'.map e).det ≠ 0 := by
    have := RingHom.map_det (e : E' →+* E) J'
    rw [RingHom.mapMatrix_apply] at this
    have h3 : (J'.map e).det = e J'.det := this.symm
    rw [h3]
    exact (map_ne_zero e).2 hdet'
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.hermitian_spaces_same_signature_isometric E hE _ J (J'.map e) hJ hh hdet hde ⟨L, hL, hd⟩ ⟨Λ₁, h1, h2⟩
    fun φ => ⟨p, q, hs φ, hs' (φ.comp (e : E' →+* E))⟩
  obtain ⟨Λ, h3, h4, h5⟩ := exists_image e he J J' γ hγ L' hL' hd'
  exact ⟨γ, Λ, hγ, h3, h4, h5⟩

end Transport

theorem rank_eq (I : AutInst) {p q : ℕ} (h : HasSig I p q) : I.n = p + q := by
  obtain ⟨φ⟩ : Nonempty (I.E →+* ℂ) := inferInstance
  simpa using (Formalism.UG.P.sig_data _ p q (hasSignature_all I h φ)).1

theorem volumeInvariant : VolumeInvariant := by
  rintro I I' p q ⟨e, he⟩ h h' c μf _ _ c' μf' _ _ hc hc'
  have hn : I'.n = I.n := (rank_eq I' h').trans (rank_eq I h).symm
  obtain ⟨A, Λ, hA, hΛ, hd, hmem⟩ := exists_isometry I.cm.cmUnram e he hn I.J I'.J I.J_herm I'.J_herm
    I.J_det I'.J_det I.L ⟨I.L_fg, I.L_span⟩ (by simpa only [hform_eq] using I.L_dual)
    I'.L ⟨I'.L_fg, I'.L_span⟩ (by simpa only [hform_eq] using I'.L_dual)
    (hasSignature_all I h) (hasSignature_all I' h')
  obtain ⟨xf, hx⟩ := GlobalTheory.T.exists_finiteAdelicPoint_lattice_eq_selfDual I Λ hΛ (by simpa only [hform_eq] using hd)
  exact GlobalTheory.T.gaugeVolume_eq_of_semilinear_isometry_genus I I' e A xf he hn hA (hx ▸ hmem) c μf c' μf' hc hc'

end GlobalTheory.VolInvariant
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableCellOrbitalIntegralRankOneKFinite
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellOrbIntG

open GlobalTheory.CellOrbInt

theorem orbInt_integrable : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), GapAtLeast L.ε L.lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → L.κN ≠ ⊤ → CellData L μG γ μR νR ν → (∀ᵐ p ∂ν, Matrix.of p.1.1 ∈ UWset k r L.z ∧ Matrix.of p.1.2 ∈ Nset k r ∧ Matrix.of p.2.1 ∈ UWset k r L.z' ∧ Matrix.of p.2.2 ∈ Nset k r) ∧ ∀ b : ℝ, 0 ≤ b → b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 → Integrable (pairMaj γ b) ν → ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' → ∀ (ξ : L.Wp) (ξ' : L.Wq), Integrable (besselIntg L (coefF L v v' ξ ξ') γ) ν := by
  intro H k r L h μG γ μR νR ν hgap hok _ hC
  obtain ⟨hγ, -, -, -, hR, hQ, -⟩ := hC
  have hae := ae_quot L hR hQ
  refine ⟨hae, fun b _ hb hint v v' hv hv' ξ ξ' => ?_⟩
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have hsm := H.1.1.2.2.1 k r L.ε L.lam L.Hs L.σ L.hlam hσ v' hv'
  obtain ⟨C, Ws, -, hdec⟩ := H.1.1.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hok v hv
  have hd := hdec v' hsm
  generalize C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) L.σ W v'‖).sum = A at hd
  have hF : ContinuousOn (coefF L v v' ξ ξ') (UH (Hpk k r)) := by
    have e : coefF L v v' ξ ξ' = fun g => ⟪v, L.σ g v'⟫_ℂ • (innerSL ℂ ξ').smulRight ξ :=
      funext (coefF_eq L v v' ξ ξ')
    rw [e]
    exact (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ v')).smul continuousOn_const
  haveI : BorelSpace (PairSp k r) := Prod.borelSpace
  have hm : AEStronglyMeasurable (besselIntg L (coefF L v v' ξ ξ') γ) ν := by
    have := (contOn_intg L hγ hF).aestronglyMeasurable (μ := ν) (meas_pairSet L)
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at this
  refine (hint.const_mul (|A| * ‖(innerSL ℂ ξ').smulRight ξ‖)).mono' hm ?_
  filter_upwards [hae] with p hp
  refine (norm_intg_le L γ _ hp).trans ?_
  have hx := point_mem L hγ hp
  unfold pairMaj
  set x := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1
  have h1 : 1 ≤ Formalism.FourierDecayAlt.B.gN x := PI.PolynomialProperness.GN.gN_ge_one hx
  have h2 : Formalism.FourierDecayAlt.B.gN x ^ (1 - Formalism.FourierDecayAlt.ThreeDimData.aOf r h) ≤ Formalism.FourierDecayAlt.B.gN x ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have h3 : ‖⟪v, L.σ x v'⟫_ℂ‖ ≤ |A| * Formalism.FourierDecayAlt.B.gN x ^ (-b) :=
    (hd x hx).trans ((mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg A)))
  rw [coefF_eq, norm_smul, mul_right_comm]
  exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)

end GlobalTheory.CellOrbIntG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralStabiliserCovolumeLeIndexWeightStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralStabiliser_covolume_le_indexWeight : GlobalTheory.TypeAsm.CovTC := by
  first | exact @GlobalTheory.TypeAsm.covTC_holds | exact GlobalTheory.TypeAsm.covTC_holds | (intros; apply GlobalTheory.TypeAsm.covTC_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentCovolumeFiniteBoundedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotent_covolume_finite_bounded : GlobalTheory.TypeAsm.CovNC := by
  first | exact @GlobalTheory.TypeAsm.covNC_holds | exact GlobalTheory.TypeAsm.covNC_holds | (intros; apply GlobalTheory.TypeAsm.covNC_holds <;> assumption)
end

