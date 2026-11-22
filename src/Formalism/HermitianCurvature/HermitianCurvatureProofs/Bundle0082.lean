import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0070
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0076
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactlySupportedBanachModel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSizesOfHypotheses
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BudgetTopConvergence
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0056
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeakToStrongSmoothnessReal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopCellsOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0026

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableEquivOps
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.QuantumDeterminants.WeylGroupFacts

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section aux

variable {k r : ℕ}

def pOf (a b c d : B.Mat k r) : B.SS k r :=
  ((Matrix.of.symm a, Matrix.of.symm b), (Matrix.of.symm c, Matrix.of.symm d))

theorem level_zero_iff (g : B.Mat k r) : g ∈ Q.Glev k r 0 ↔ g ∈ B.GV k r := by
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

theorem mat_inv_one : (1 : B.Mat k r)⁻¹ = 1 := by
  simp

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem rho_pOf (D : B.RealPlaceData k r Wp Wq) (a b c d : B.Mat k r) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    B.rho D (pOf a b c d) F = fun x => (D.π a).comp ((F (a⁻¹ * b⁻¹ * x * d * c)).comp (D.π' c⁻¹)) := by
  funext x
  simp [B.rho, B.sgs, pOf]

end aux

theorem equivariant_operators_holds : EquivOps := by
  intro hE k r Wp Wq _ _ _ _ _ D O P hDom hloc hsmul hsm hcomm J hJ
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  have hext : ∀ g₀ ∈ B.GV k r, g₀ ∈ O → ∃ (f : B.Mat k r → (Wq →L[ℂ] Wp)) (U : Set (B.Mat k r)),
      B.CkOn ⊤ (B.GV k r) f ∧ HasCompactSupport f ∧ tsupport f ⊆ O ∧ IsOpen U ∧ g₀ ∈ U ∧
        ∀ x ∈ U, x ∈ B.GV k r → f x = J x :=
    fun g₀ hg hO => hE k r (Wq →L[ℂ] Wp) O J hDom.1 hS g₀ hg hO
  have one_N : (1 : B.Mat k r) ∈ Q.Nlev k r 0 := ⟨mem_n_one, (level_zero_iff _).2 uh_one⟩
  have one_S : ∀ z, (1 : B.Mat k r) ∈ Q.Slev k r z 0 :=
    fun z => ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, 1, one_N, by simp⟩
  have hπ1 : D.π 1 = 1 := D.π_rep.1
  have hπ'1 : D.π' 1 = 1 := D.π'_rep.1
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro g₀ hg₀
    have hgG := (level_zero_iff g₀).1 hg₀.1
    obtain ⟨f, U, hf, _, hfO, hUo, hgU, hfJ⟩ := hext g₀ hgG hg₀.2
    obtain ⟨U', F, hU', hgU', hF, hFe⟩ := hsm f hf hfO g₀ hg₀
    refine ⟨U ∩ U', F, hUo.inter hU', ⟨hgU, hgU'⟩, hF.mono Set.inter_subset_right, ?_⟩
    intro x hx hxG
    rw [← hFe x hx.2 hxG]
    exact hloc U J f hUo (fun y hy hyG => (hfJ y hy hyG).symm) x hx.1 ((level_zero_iff x).1 hxG)
  ·
    intro g hg n hn
    have hgG := (level_zero_iff g).1 hg.1
    have hnN : n ∈ Formalism.QuantumDeterminants.Nset k r := hn.1
    have hnG : n ∈ B.GV k r := hnN.1
    have hng : n * g ∈ O := by
      have := hDom.2 g hg n ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z, n, hn, by simp⟩ 1 (one_S D.z')
      simpa using this
    have hngG : n * g ∈ B.GV k r := uh_mul hnG hgG
    obtain ⟨f1, U1, hf1, hf1c, hf1O, hU1, hngU1, hf1J⟩ := hext (n * g) hngG hng
    have hp : D.inSS (pOf 1 n⁻¹ 1 1) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [pOf, Equiv.apply_symm_apply]
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z
      · exact mem_n_inv hnN
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z'
      · exact mem_n_one
    have hrho : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.rho D (pOf 1 n⁻¹ 1 1) F = fun x => F (n * x) := by
      intro F
      rw [rho_pOf]
      funext x
      rw [Matrix.nonsing_inv_nonsing_inv n (isUnit_of_uh hnG), mat_inv_one, hπ1, hπ'1]
      ext v
      simp
    have hc := hcomm f1 hf1 hf1c hf1O _ hp g hg.2 hgG
    rw [hrho, hrho] at hc
    beta_reduce at hc
    have e1 : P f1 (n * g) = P J (n * g) := hloc U1 f1 J hU1 hf1J (n * g) hngU1 hngG
    have hV : IsOpen ((fun x : B.Mat k r => n * x) ⁻¹' U1 ∩ O) :=
      (hU1.preimage (continuous_const.matrix_mul continuous_id)).inter hDom.1
    have e2 : P (fun x => f1 (n * x)) g = P (Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd n • J) g := by
      refine hloc _ _ _ hV ?_ g ⟨hngU1, hg.2⟩ hgG
      intro x hx hxG
      rw [hf1J (n * x) hx.1 (uh_mul hnG hxG), Pi.smul_apply]
      exact hL x ⟨(level_zero_iff x).2 hxG, hx.2⟩ n hn
    rw [← e1, ← hc, e2, hsmul _ J g hgG]
  ·
    intro g hg n hn
    have hgG := (level_zero_iff g).1 hg.1
    have hnN : n ∈ Formalism.QuantumDeterminants.Nset k r := hn.1
    have hnG : n ∈ B.GV k r := hnN.1
    have hgn : g * n ∈ O := by
      have := hDom.2 g hg 1 (one_S D.z) n ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z', n, hn, by simp⟩
      simpa using this
    have hgnG : g * n ∈ B.GV k r := uh_mul hgG hnG
    obtain ⟨f1, U1, hf1, hf1c, hf1O, hU1, hgnU1, hf1J⟩ := hext (g * n) hgnG hgn
    have hp : D.inSS (pOf 1 1 1 n) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [pOf, Equiv.apply_symm_apply]
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z
      · exact mem_n_one
      · exact Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r D.z'
      · exact hnN
    have hrho : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.rho D (pOf 1 1 1 n) F = fun x => F (x * n) := by
      intro F
      rw [rho_pOf]
      funext x
      rw [mat_inv_one, hπ1, hπ'1]
      ext v
      simp
    have hc := hcomm f1 hf1 hf1c hf1O _ hp g hg.2 hgG
    rw [hrho, hrho] at hc
    beta_reduce at hc
    have e1 : P f1 (g * n) = P J (g * n) := hloc U1 f1 J hU1 hf1J (g * n) hgnU1 hgnG
    have hV : IsOpen ((fun x : B.Mat k r => x * n) ⁻¹' U1 ∩ O) :=
      (hU1.preimage (continuous_id.matrix_mul continuous_const)).inter hDom.1
    have e2 : P (fun x => f1 (x * n)) g = P (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd n • J) g := by
      refine hloc _ _ _ hV ?_ g ⟨hgnU1, hg.2⟩ hgG
      intro x hx hxG
      rw [hf1J (x * n) hx.1 (uh_mul hxG hnG), Pi.smul_apply]
      exact hR x ⟨(level_zero_iff x).2 hxG, hx.2⟩ n hn
    rw [← e1, ← hc, e2, hsmul _ J g hgG]
  ·
    intro g hg h hh h' hh'
    have hgG := (level_zero_iff g).1 hg.1
    have hhG : h ∈ B.GV k r := hh.1
    have hh'G : h' ∈ B.GV k r := hh'.1
    have hu := isUnit_of_uh hhG
    have hu' := isUnit_of_uh hh'G
    have hhg : h * g * h' ∈ O := by
      have := hDom.2 g hg h ⟨h, hh, 1, one_N, by simp⟩ h' ⟨h', hh', 1, one_N, by simp⟩
      simpa using this
    have hhgG : h * g * h' ∈ B.GV k r := uh_mul (uh_mul hhG hgG) hh'G
    obtain ⟨f1, U1, hf1, hf1c, hf1O, hU1, hhgU1, hf1J⟩ := hext (h * g * h') hhgG hhg
    have hp : D.inSS (pOf h⁻¹ 1 h' 1) := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [pOf, Equiv.apply_symm_apply]
      · exact uw_inv hh
      · exact mem_n_one
      · exact hh'
      · exact mem_n_one
    have hrho : ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.rho D (pOf h⁻¹ 1 h' 1) F =
        fun x => (D.π h⁻¹).comp ((F (h * x * h')).comp (D.π' h'⁻¹)) := by
      intro F
      rw [rho_pOf]
      funext x
      rw [Matrix.nonsing_inv_nonsing_inv h hu, mat_inv_one]
      simp [Matrix.mul_assoc]

    have eL : (D.π h⁻¹).comp (D.π h) = 1 := by
      rw [← D.π_rep.2 _ (uw_inv hh) _ hh, Matrix.nonsing_inv_mul h hu, hπ1]
    have eL' : (D.π h).comp (D.π h⁻¹) = 1 := by
      rw [← D.π_rep.2 _ hh _ (uw_inv hh), Matrix.mul_nonsing_inv h hu, hπ1]
    have eR : (D.π' h').comp (D.π' h'⁻¹) = 1 := by
      rw [← D.π'_rep.2 _ hh' _ (uw_inv hh'), Matrix.mul_nonsing_inv h' hu', hπ'1]
    have eR' : (D.π' h'⁻¹).comp (D.π' h') = 1 := by
      rw [← D.π'_rep.2 _ (uw_inv hh') _ hh', Matrix.nonsing_inv_mul h' hu', hπ'1]
    have eLv : ∀ w, D.π h⁻¹ (D.π h w) = w := fun w => by simpa using congrArg (fun L => L w) eL
    have eL'v : ∀ w, D.π h (D.π h⁻¹ w) = w := fun w => by simpa using congrArg (fun L => L w) eL'
    have eRv : ∀ w, D.π' h' (D.π' h'⁻¹ w) = w := fun w => by simpa using congrArg (fun L => L w) eR
    have eR'v : ∀ w, D.π' h'⁻¹ (D.π' h' w) = w := fun w => by simpa using congrArg (fun L => L w) eR'
    have hc := hcomm f1 hf1 hf1c hf1O _ hp g hg.2 hgG
    rw [hrho, hrho] at hc
    have e1 : P f1 (h * g * h') = P J (h * g * h') := hloc U1 f1 J hU1 hf1J _ hhgU1 hhgG
    have hV : IsOpen ((fun x : B.Mat k r => h * x * h') ⁻¹' U1 ∩ O) :=
      (hU1.preimage ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)).inter hDom.1
    have e2 : P (fun x => (D.π h⁻¹).comp ((f1 (h * x * h')).comp (D.π' h'⁻¹))) g = P J g := by
      refine hloc _ _ _ hV ?_ g ⟨hhgU1, hg.2⟩ hgG
      intro x hx hxG
      rw [hf1J _ hx.1 (uh_mul (uh_mul hhG hxG) hh'G), hU x ⟨(level_zero_iff x).2 hxG, hx.2⟩ h hh h' hh']
      ext v
      simp [eLv, eRv]
    rw [e2] at hc
    beta_reduce at hc
    rw [e1] at hc

    rw [hc]
    ext v
    simp [eL'v, eR'v]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRStepALevel
section
open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.CapelliExpansionLemmas

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem base_index_ne_first_index (l : Fin r) (j : Fin (mdim k r l.succ)) : v0 k l j ≠ e0 k l := by
  unfold v0 e0
  intro h
  simp [Fin.ext_iff] at h

section Level
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ} {l : Fin r}
  {D : Set (Mx k r)}

variable (E l) in

def borderedMinorImage (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) {m : ℕ} (f b : Fin m → Fin (mdim k r l.succ)) (u : ℂ) :
    Module.End ℂ (sfData E l.succ (ho1 l hD)).V :=
  bTee E l hD u * mB E l.succ (ho1 l hD) f b (u - 1) -
    ∑ w : Fin m, ∑ x : Fin m, ((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ)) : ℂ) •
      (scaledRowVectorOperator E l hD z (f w) * mB E l.succ (ho1 l hD) (f ∘ skip1 w) (b ∘ skip1 x) (u - 2) *
        (xv k r z' l.succ (b x) • 1))

variable (R : Rules) (hz : inWb k r z) (hz' : inWb k r z') (hD : IsDom k r z z' l.castSucc D) {J : Mx k r → E}
  (hJ : SmoothLev k r l.castSucc D J) (hl : LeftEq k r z l.castSucc D J) (hr : RightEq k r z' l.castSucc D J)

include hz hz' hl hr in
theorem evaluation_bordered_minor_first {m : ℕ} (f b : Fin m → Fin (mdim k r l.succ)) (u : ℂ) :
    IntJ (rho E R.w l hD.1) (VLeft z l.castSucc hD.1) (J0 hD.1 hJ)
      (qminor (E0 E l.castSucc hD.1) (bE (e0 k l) (v0 k l ∘ f)) (bE (e0 k l) (v0 k l ∘ b)) u)
      (borderedMinorImage E l hD.1 z z' f b u) := by
  rw [quantum_minor_border_expansion_first _ (e0 k l) (v0 k l ∘ f) (v0 k l ∘ b) (level_generators_gl_relations R.gl l.castSucc hD.1) (fun _ => base_index_ne_first_index l _)
    (fun _ => base_index_ne_first_index l _) u]
  have hJ0 := restricted_function_mem_left_space hD hJ hl
  refine IntJ.sub (((int_Tee R.w R.ep R.rt hD u).mul (int_minor R.w R.ep R.q hD f b (u - 1))).toJ hJ0)
    (IntJ.sum _ fun w _ => IntJ.sum _ fun x _ => IntJ.intMul ?_ _)
  exact ((int_we R.w R.ep R.rl hz hD (f w)).mul
    (int_minor R.w R.ep R.q hD (f ∘ skip1 w) (b ∘ skip1 x) (u - 2))).mulJ
    (intJ_eig hJ0 (eig_ex R.rr hz' hD.1 hJ hr (b x)))

include hz hz' hl hr in

theorem quantum_minor_point_evaluation {m : ℕ} (f b : Fin m → Fin (mdim k r l.succ)) (u : ℂ) {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Mx k r}
    (hg : g ∈ Glev k r l.succ) (hgD : g ∈ Dc1 l D c) :
    qminorOp (EH k r) (posL k r l.castSucc ∘ bE (e0 k l) (v0 k l ∘ f)) (posL k r l.castSucc ∘ bE (e0 k l) (v0 k l ∘ b))
        u J (w1 k r l (c l) * g) =
      evP (ho1 l hD.1) (rho E R.w l hD.1 (J0 hD.1 hJ)) c g (borderedMinorImage E l hD.1 z z' f b u) := stp_evalPt R.w hD.1 hJ (evaluation_bordered_minor_first R hz hz' hD hJ hl hr f b u) hc hg hgD

end Level

section Comb

theorem sign_antisymmetric {m : ℕ} {a b : Fin m} (h : a ≠ b) : sg2 a b = -sg2 b a := by
  unfold sg2
  have hne : (a : ℕ) ≠ b := fun h' => h (Fin.ext h')
  split_ifs <;> first | omega | ring

private theorem skip1_val_eq_ite {n : ℕ} (a : Fin n) (b : Fin (n - 1)) :
    ((skip1 a b : Fin n) : ℕ) = if (b : ℕ) < a then (b : ℕ) else b + 1 := by
  unfold skip1
  split_ifs <;> rfl

private theorem skip2_val_eq_ite {n : ℕ} (a b : Fin n) (j : Fin (n - 2)) :
    ((skip2 a b j : Fin n) : ℕ) = if (j : ℕ) < a then (j : ℕ) else if (j : ℕ) + 1 < b then j + 1 else j + 2 := by
  unfold skip2
  split_ifs <;> rfl

private theorem skip1_eq_succAbove {t : ℕ} (s : Fin (t + 1)) (w : Fin t) : skip1 s w = s.succAbove w := by
  apply Fin.ext
  rw [skip1_val_eq_ite]
  by_cases h : (w : ℕ) < s
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt s w (by rw [Fin.lt_def, Fin.coe_castSucc]; exact h)]
    simp
  · rw [if_neg h, Fin.succAbove_of_le_castSucc s w (by rw [Fin.le_def, Fin.coe_castSucc]; omega)]
    simp

private theorem skip1_skip1_val_eq_skip2_min_max {t : ℕ} (s : Fin (t + 1)) (w : Fin t) (j : Fin (t + 1 - 2)) :
    ((skip1 s (skip1 w j) : Fin (t + 1)) : ℕ) = (skip2 (min (skip1 s w) s) (max (skip1 s w) s) j : ℕ) := by
  have hmin : ((min (skip1 s w) s : Fin (t + 1)) : ℕ) = min ((skip1 s w : Fin (t + 1)) : ℕ) (s : ℕ) := by
    rcases _root_.le_total (skip1 s w) s with h | h
    · rw [_root_.min_eq_left h, _root_.min_eq_left (Fin.le_def.mp h)]
    · rw [_root_.min_eq_right h, _root_.min_eq_right (Fin.le_def.mp h)]
  have hmax : ((max (skip1 s w) s : Fin (t + 1)) : ℕ) = max ((skip1 s w : Fin (t + 1)) : ℕ) (s : ℕ) := by
    rcases _root_.le_total (skip1 s w) s with h | h
    · rw [_root_.max_eq_right h, _root_.max_eq_right (Fin.le_def.mp h)]
    · rw [_root_.max_eq_left h, _root_.max_eq_left (Fin.le_def.mp h)]
  have hj := j.isLt
  have hw := w.isLt
  have hs := s.isLt
  rw [skip2_val_eq_ite, hmin, hmax, skip1_val_eq_ite s (skip1 w j), skip1_val_eq_ite s w, skip1_val_eq_ite w j]
  simp only [Nat.min_def, Nat.max_def]
  split_ifs <;> omega

end Comb

section Alg
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {l : Fin r} {D : Set (Mx k r)}
  (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)

theorem aY_comm_bTee (t : Fin (mdim k r l.succ)) (u : ℂ) :
    mulB E l.succ (ho1 l hD) (aY z l.succ t) * bTee E l hD u = bTee E l hD u * mulB E l.succ (ho1 l hD) (aY z l.succ t) := by
  have h := P_mulB_of (E := E) (ho1 l hD) l (sf_aY z t) 0 (fun c _ g => by
    rw [zero_mul]; exact pOp_const l _ c)
  rw [zero_smul, add_zero] at h
  unfold bTee
  rw [mul_add, add_mul, h, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

theorem capelli_key_first_term :
    (∑ s : Fin (mdim k r l.succ), ∑ t : Fin (mdim k r l.succ),
      ((((-1 : ℤ) ^ ((s : ℕ) + (t : ℕ)) : ℤ) : ℂ) * xbv k r z' l.succ s) •
        (mulB E l.succ (ho1 l hD) (aY z l.succ t) *
          (bTee E l hD (uC k r l.castSucc Y) * mB E l.succ (ho1 l hD) (skip1 s) (skip1 t) (uC k r l.castSucc Y - 1)))) =
      -(bTee E l hD (uC k r l.castSucc Y) * tB E l.succ (ho1 l hD) z z' Y 1 0) := by
  rw [stp_uC_succ, ← mul_neg, ← signed_expansion_block10, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← mul_assoc, aY_comm_bTee, mul_assoc, mul_smul_comm]

end Alg

section Comb2

theorem comb {M : Type*} [AddCommGroup M] [Module ℂ M] {t : ℕ} (β α' : Fin (t + 1) → ℂ)
    (Θ : Fin (t + 1) → Fin (t + 1) → (Fin (t + 1 - 2) → Fin (t + 1)) → (Fin (t + 1 - 2) → Fin (t + 1)) → M) :
    (∑ s : Fin (t + 1), ∑ T : Fin (t + 1), ∑ w : Fin t, ∑ x : Fin t,
      (((sg2 s (skip1 s w) * sg2 T (skip1 T x) : ℤ) : ℂ) * β s * α' (skip1 T x)) •
        Θ (skip1 s w) T (skip1 s ∘ skip1 w) (skip1 T ∘ skip1 x)) =
      -∑ w : Fin (t + 1), ∑ w' : Fin (t + 1), ∑ x : Fin (t + 1), ∑ x' : Fin (t + 1),
        if w ≠ w' ∧ x ≠ x' then (((sg2 w w' * sg2 x x' : ℤ) : ℂ) * (α' x' * β w')) •
          Θ w x (skip2 (min w w') (max w w')) (skip2 (min x x') (max x x')) else 0 := by
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => arg 1; arg 2; ext w'; rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [ite_and]
  rw [Fin.sum_univ_succAbove _ s]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, Finset.sum_const_zero, zero_add, Fin.succAbove_ne,
    not_false_eq_true]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_succAbove _ T]
  simp only [not_true_eq_false, ↓reduceIte, zero_add]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hTj : ¬T = T.succAbove j := (Fin.succAbove_ne T j).symm
  rw [if_pos hTj, ← skip1_eq_succAbove s i, ← skip1_eq_succAbove T j]
  have h1 : (skip1 s ∘ skip1 i : Fin (t + 1 - 2) → Fin (t + 1)) = skip2 (min (skip1 s i) s) (max (skip1 s i) s) :=
    funext fun k => Fin.ext (skip1_skip1_val_eq_skip2_min_max s i k)
  have h2 : (skip1 T ∘ skip1 j : Fin (t + 1 - 2) → Fin (t + 1)) = skip2 (min T (skip1 T j)) (max T (skip1 T j)) := by
    rw [_root_.min_comm, _root_.max_comm]
    exact funext fun k => Fin.ext (skip1_skip1_val_eq_skip2_min_max T j k)
  have hne : s ≠ skip1 s i := by
    rw [skip1_eq_succAbove s i]
    exact (Fin.succAbove_ne s i).symm
  rw [h1, h2, sign_antisymmetric hne, ← neg_smul]
  congr 1
  push_cast
  ring

theorem sign_skip_eq_power_at_level (L : Fin (r + 1)) (s : Fin (mdim k r L)) (w : Fin (mdim k r L - 1)) :
    sg2 s (skip1 s w) = (-1) ^ ((s : ℕ) + (w : ℕ)) := by
  unfold sg2 skip1
  by_cases hw : (w : ℕ) < s
  · simp [hw]
  · have h2 : ¬ ((w : ℕ) + 1 < s) := by omega
    simp only [hw, h2, ↓reduceIte, Fin.val_mk]
    ring

end Comb2

section Alg2
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {l : Fin r} {D : Set (Mx k r)}
  (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)

theorem capelli_key_second_term (s t : Fin (mdim k r l.succ)) (w x : Fin (mdim k r l.succ - 1)) (u : ℂ) :
    ((((-1 : ℤ) ^ ((s : ℕ) + (t : ℕ)) : ℤ) : ℂ) * xbv k r z' l.succ s) •
      (mulB E l.succ (ho1 l hD) (aY z l.succ t) *
        (((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ)) : ℂ) •
          (scaledRowVectorOperator E l hD z (skip1 s w) * mB E l.succ (ho1 l hD) (skip1 s ∘ skip1 w) (skip1 t ∘ skip1 x) u *
            (xv k r z' l.succ (skip1 t x) • 1)))) =
      mulB E l.succ (ho1 l hD) (aCi k l) *
        ((((sg2 s (skip1 s w) * sg2 t (skip1 t x) : ℤ) : ℂ) * xbv k r z' l.succ s * xv k r z' l.succ (skip1 t x)) •
          (mulB E l.succ (ho1 l hD) (aYb z l.succ (skip1 s w)) *
            (mulB E l.succ (ho1 l hD) (aY z l.succ t) * mB E l.succ (ho1 l hD) (skip1 s ∘ skip1 w) (skip1 t ∘ skip1 x) u))) := by
  unfold scaledRowVectorOperator
  rw [sign_skip_eq_power_at_level, sign_skip_eq_power_at_level]
  have c1 : mulB E l.succ (ho1 l hD) (aY z l.succ t) * mulB E l.succ (ho1 l hD) (aCi k l) = mulB E l.succ (ho1 l hD) (aCi k l) * mulB E l.succ (ho1 l hD) (aY z l.succ t) :=
    (mulB_comm (E := E) (ho1 l hD) (sf_aY z t) (sf_aCi l)).eq
  have c2 : mulB E l.succ (ho1 l hD) (aY z l.succ t) * mulB E l.succ (ho1 l hD) (aYb z l.succ (skip1 s w)) =
      mulB E l.succ (ho1 l hD) (aYb z l.succ (skip1 s w)) * mulB E l.succ (ho1 l hD) (aY z l.succ t) :=
    (mulB_comm (E := E) (ho1 l hD) (sf_aY z t) (sf_aYb z (skip1 s w))).eq
  simp only [mul_smul_comm, smul_mul_assoc, smul_smul, mul_one, mul_assoc]
  rw [← mul_assoc (mulB E l.succ (ho1 l hD) (aY z l.succ t)) (mulB E l.succ (ho1 l hD) (aCi k l)), c1, mul_assoc,
    ← mul_assoc (mulB E l.succ (ho1 l hD) (aY z l.succ t)) (mulB E l.succ (ho1 l hD) (aYb z l.succ (skip1 s w))), c2, mul_assoc]
  congr 1
  push_cast
  ring

theorem capelli_key_second_identity :
    (∑ s : Fin (mdim k r l.succ), ∑ t : Fin (mdim k r l.succ),
      ((((-1 : ℤ) ^ ((s : ℕ) + (t : ℕ)) : ℤ) : ℂ) * xbv k r z' l.succ s) •
        (mulB E l.succ (ho1 l hD) (aY z l.succ t) *
          ∑ w : Fin (mdim k r l.succ - 1), ∑ x : Fin (mdim k r l.succ - 1),
            ((((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ)) : ℂ) •
              (scaledRowVectorOperator E l hD z (skip1 s w) *
                mB E l.succ (ho1 l hD) (skip1 s ∘ skip1 w) (skip1 t ∘ skip1 x) (uC k r l.castSucc Y - 2) *
                (xv k r z' l.succ (skip1 t x) • 1)))) =
      mulB E l.succ (ho1 l hD) (aCi k l) * tB E l.succ (ho1 l hD) z z' Y 1 1 := by
  calc _ = mulB E l.succ (ho1 l hD) (aCi k l) * (∑ s : Fin (mdim k r l.succ), ∑ t : Fin (mdim k r l.succ), ∑ w : Fin (mdim k r l.succ - 1),
          ∑ x : Fin (mdim k r l.succ - 1),
          ((((sg2 s (skip1 s w) * sg2 t (skip1 t x) : ℤ) : ℂ) * xbv k r z' l.succ s *
            xv k r z' l.succ (skip1 t x)) •
            (mulB E l.succ (ho1 l hD) (aYb z l.succ (skip1 s w)) *
              (mulB E l.succ (ho1 l hD) (aY z l.succ t) * mB E l.succ (ho1 l hD) (skip1 s ∘ skip1 w) (skip1 t ∘ skip1 x) (uC k r l.castSucc Y - 2))))) := by
        simp only [Finset.mul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ =>
          Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ => ?_
        exact capelli_key_second_term hD z z' s t w x _
    _ = mulB E l.succ (ho1 l hD) (aCi k l) * -(∑ w : Fin (mdim k r l.succ), ∑ w' : Fin (mdim k r l.succ), ∑ x : Fin (mdim k r l.succ),
          ∑ x' : Fin (mdim k r l.succ),
          if w ≠ w' ∧ x ≠ x' then (((sg2 w w' * sg2 x x' : ℤ) : ℂ) * (xv k r z' l.succ x' * xbv k r z' l.succ w')) •
            (mulB E l.succ (ho1 l hD) (aYb z l.succ w) * (mulB E l.succ (ho1 l hD) (aY z l.succ x) *
              mB E l.succ (ho1 l hD) (skip2 (min w w') (max w w')) (skip2 (min x x') (max x x')) (uC k r l.castSucc Y - 2))) else 0) := by
        exact congrArg (fun S => mulB E l.succ (ho1 l hD) (aCi k l) * S)
          (comb (fun s => xbv k r z' l.succ s) (fun x => xv k r z' l.succ x)
            (fun w x f b => mulB E l.succ (ho1 l hD) (aYb z l.succ w) * (mulB E l.succ (ho1 l hD) (aY z l.succ x) *
              mB E l.succ (ho1 l hD) f b (uC k r l.castSucc Y - 2))))
    _ = mulB E l.succ (ho1 l hD) (aCi k l) * tB E l.succ (ho1 l hD) z z' Y 1 1 := by
        rw [stp_uC_succ2, signed_double_expansion_block11, neg_neg]

end Alg2

end Formalism.FourierDecayAlt.P.CutMP.CapelliExpansionLemmas
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivativeBoundInBanachSpace
section
namespace Formalism.FourierDecayAlt.P

theorem coordinate_sizes_in_norm : Formalism.FourierDecayAlt.U.SliceCoordinateSizes :=
  coordinate_sizes_of_parts slice_membership block3_apply_embedding aux_statement_17 hat_z_on_slice level_determinant_z

theorem norm_decay_in_coordinates : Formalism.FourierDecayAlt.U.CoordinateDecay :=
  norm_decay_of_coordinate_sizes coordinate_sizes_in_norm

theorem phi_pointwise_bound : Formalism.FourierDecayAlt.U.PointwiseIntegralBound :=
  phi_bound_of_parts slice_membership derivative_cost_bound norm_decay_in_coordinates weight_integrability

theorem theorem_u : Formalism.FourierDecayAlt.U.TheoremU :=
  theorem_u_of_parts phi_pointwise_bound phi_support_determinant weak_to_strong_smoothness

theorem phi_support_level_function : Formalism.FourierDecayAlt.U.PhiSuppG :=
  phi_support_level_of_parts level_function_slice level_determinant_z hat_z_on_slice

theorem corollary_u2_germ_hypothesis : Formalism.FourierDecayAlt.U.GermExpansionHypothesis :=
  corollary_u2_of_parts theorem_u corollary_u1_truncated_alt star_projection budget_second_corollary
    thresholds_second_corollary phi_support_level_function

theorem derivative_bound_in_banach_space : Formalism.FourierDecayAlt.U.UseDerivBound :=
  derivative_bound_use_of_parts corollary_u2_germ_hypothesis compactly_supported_banach_model compactly_supported_monotone seminorm_of_form
    seminorm_completion derivative_bound_of_decay derivative_bound_composition

theorem germ_expansion_applies : Formalism.FourierDecayAlt.U.UseGerm :=
  germ_expansion_of_parts germ_rate det_weyl_matrix corollary_u2_germ_hypothesis derivative_bound_of_decay
    power_matching scale_matching

theorem germ_expansion_top_level : Formalism.FourierDecayAlt.U.UseGermTop :=
  germ_top_level_of_parts germ_rate det_weyl_matrix top_cells derivative_bound_of_decay

theorem germ_expansion_top_count : Formalism.FourierDecayAlt.U.UseGermTopCount :=
  germ_top_count_of_parts germ_expansion_top_level budget_top_convergence

theorem germ_expansion_in_form_space : Formalism.FourierDecayAlt.U.GermInForm :=
  germ_in_form_of_parts germ_rate det_weyl_matrix derivative_bound_in_banach_space scale_matching

end Formalism.FourierDecayAlt.P
end

