import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FormalDegreeBessel.StatementG
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0032
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0025
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0004
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiCentreEigenfunctionDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0147
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0160
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRadicalNormalFormPairOfFlags
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0153
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0156
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0157
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0158
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBlockAntidiagonalScaledPairingMatrix
section
open Matrix

namespace GlobalTheory.Amp.BlockFrame

theorem blockAnti_scaled_pairing : ∀ {K : Type} [Field K] {j r : ℕ} (hj : j ≤ r) (w : Formalism.MainNotions.S.Loc.Pt K j),
    ∃ β : Fin r → ℕ, Monotone β ∧ (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) ∧
      ∀ (σ : K →+* ℂ) (sgn : Fin j → ℤˣ) (ρ : ℝ), 0 < ρ →
      GlobalTheory.Amp.BlockAnti (fun a : Fin j => β (Fin.castLE hj a))
        (Matrix.of fun a b : Fin j => (((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) *
          σ (w.mat b a * ((sgn a : ℤ) : K))) := by
  intro K _ j r hj w
  obtain ⟨τ, γ, t, ht⟩ := GlobalTheory.HL.BlockStab.exists_monomial (E := K) w.blocks
  rw [w.size] at ht

  have hγN : ∀ a, a < j → γ a < (Finset.range j).sup γ + 1 := fun a ha =>
    Nat.lt_succ_of_le (Finset.le_sup (f := γ) (Finset.mem_range.mpr ha))
  refine ⟨fun a => if (a : ℕ) < j then γ a else (Finset.range j).sup γ + 1, ?_, ?_, ?_⟩
  · intro a b hab
    have hab' : (a : ℕ) ≤ b := hab
    dsimp only
    split_ifs with h1 h2 h2
    · exact ((ht a h1).2.2.2 b h2).2.1 hab'
    · exact (hγN a h1).le
    · omega
    · exact le_rfl
  · intro a b hb
    have hb' : ¬ ((b : ℕ) < j) := by omega
    dsimp only
    rw [if_neg hb']
    by_cases ha : (a : ℕ) < j
    · rw [if_pos ha]
      exact ⟨fun h => absurd h (hγN a ha).ne, fun h => absurd h (by omega)⟩
    · rw [if_neg ha]
      exact ⟨fun _ => by omega, fun _ => rfl⟩
  · intro σ sgn ρ hρ
    simp only [Fin.val_castLE, Fin.is_lt, if_true]

    have hent : ∀ a b : Fin j, w.mat b a = if (a : ℕ) = τ b then (t (γ b) : K) else 0 :=
      fun a b => ((ht b b.isLt).2.2.2 a a.isLt).2.2.2
    have key : ∀ a b : Fin j,
        (((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) * σ (w.mat b a * ((sgn a : ℤ) : K)) ≠ 0 →
          (a : ℕ) = τ b := by
      intro a b h
      by_contra hne
      apply h
      rw [hent a b, if_neg hne, zero_mul, map_zero, mul_zero]
    have hs : ∀ a : Fin j, ‖σ ((sgn a : ℤ) : K)‖ = 1 := fun a => by
      rcases Int.units_eq_one_or (sgn a) with h | h <;> simp [h]
    have hsK : ∀ a : Fin j, ((sgn a : ℤ) : K) ≠ 0 := fun a => by
      rcases Int.units_eq_one_or (sgn a) with h | h <;> simp [h]

    have hZ : (Matrix.of fun a b : Fin j => (((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) *
          σ (w.mat b a * ((sgn a : ℤ) : K))) =
        Matrix.diagonal (fun a : Fin j => (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ)) *
          (Matrix.diagonal (fun a : Fin j => ((sgn a : ℤ) : K)) * w.matᵀ).map σ *
          Matrix.diagonal (fun a : Fin j => (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ)) := by
      ext a b
      simp only [Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply,
        Matrix.transpose_apply, Complex.ofReal_mul, map_mul]
      ring
    have hd : ∀ a : Fin j, (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) ≠ 0 := fun a =>
      Complex.ofReal_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ hρ.ne'))
    unfold GlobalTheory.Amp.BlockAnti
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b hab
      exact ((ht a a.isLt).2.2.2 b b.isLt).2.1 hab
    · rw [hZ, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
        show ((Matrix.diagonal (fun a : Fin j => ((sgn a : ℤ) : K)) * w.matᵀ).map σ).det =
          σ (Matrix.diagonal (fun a : Fin j => ((sgn a : ℤ) : K)) * w.matᵀ).det from
          (RingHom.map_det σ _).symm,
        Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose]
      have hP : ∏ a : Fin j, (((ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun a _ => hd a
      refine mul_ne_zero (mul_ne_zero hP ?_) hP
      exact (map_ne_zero σ).mpr (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun a _ => hsK a)
        (GlobalTheory.SgLoc.PtAlg.isUnit_det w).ne_zero)
    · intro a b h
      have e := key a b h
      show γ a = γ b
      rw [e]
      exact (ht b b.isLt).2.2.1
    · intro a b a' b' h1 h2 hγ
      have hγ' : γ a = γ a' := hγ
      have e1 := key a b h1
      have e2 := key a' b' h2
      have hb : (b : ℕ) = τ a := by rw [e1, (ht b b.isLt).2.1]
      have hb' : (b' : ℕ) = τ a' := by rw [e2, (ht b' b'.isLt).2.1]
      have hsum : (a : ℕ) + τ a = a' + τ a' := ((ht a a.isLt).2.2.2 a' a'.isLt).2.2.1 hγ'
      refine ⟨?_, ?_, ?_⟩
      · have hγb : γ b = γ a := by rw [hb]; exact (ht a a.isLt).2.2.1
        have hγb' : γ b' = γ a := by rw [hb', hγ']; exact (ht a' a'.isLt).2.2.1
        have hw1 : w.mat b a = (t (γ a) : K) := by rw [hent a b, if_pos e1, hγb]
        have hw2 : w.mat b' a' = (t (γ a) : K) := by rw [hent a' b', if_pos e2, hγb']
        have ha := a.isLt
        have hb2 := b.isLt
        have ha' := a'.isLt
        have hb2' := b'.isLt
        have hexp : (r - b.val) + (r - a.val) = (r - b'.val) + (r - a'.val) := by omega
        have hc : ((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) =
            (ρ ^ (r - b'.val))⁻¹ * (ρ ^ (r - a'.val))⁻¹ := by
          rw [← mul_inv, ← mul_inv, ← pow_add, ← pow_add, hexp]
        simp only [Matrix.of_apply]
        rw [hw1, hw2, hc, norm_mul, norm_mul, map_mul, map_mul, norm_mul, norm_mul, hs a, hs a']
      · intro haa
        subst haa
        exact Fin.ext (hb.trans hb'.symm)
      · intro hlt
        have hlt' : (a : ℕ) < a' := hlt
        exact Fin.lt_def.mpr (by omega)

end GlobalTheory.Amp.BlockFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDerivPhiConj
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.PhiConjDeriv

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma analyticAt_Phi (lam : Fin n → ℝ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ Omega n) :
    AnalyticAt ℂ (Phi lam) z := by
  have h := GlobalTheory.PhiEigenfun.analytic_Phi lam (1 : Matrix (Fin n) (Fin n) ℂ) 1 z (by simpa using hz)
  simpa using h

lemma fderiv_Phi_single (lam : Fin n → ℝ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ Omega n) {a b : Fin n}
    (hab : a < b) : fderiv ℂ (Phi lam) z (z * Matrix.single a b 1) = 0 := by
  have hne : a ≠ b := ne_of_lt hab
  have hγ : HasDerivAt (fun t : ℂ => z + t • (z * Matrix.single a b 1)) (z * Matrix.single a b 1) 0 := by
    have h0 := ((hasDerivAt_id' (0 : ℂ)).smul_const (z * Matrix.single a b 1)).const_add z
    rwa [one_smul] at h0
  have hP : HasFDerivAt (Phi lam) (fderiv ℂ (Phi lam) z) (z + (0 : ℂ) • (z * Matrix.single a b 1)) := by
    rw [zero_smul, add_zero]
    exact (analyticAt_Phi lam hz).differentiableAt.hasFDerivAt
  have h1 := hP.comp_hasDerivAt (0 : ℂ) hγ
  have hc : ∀ᶠ t : ℂ in nhds 0, 1 + t ≠ 0 := by
    have hca : ContinuousAt (fun t : ℂ => 1 + t) 0 := (continuous_const.add continuous_id).continuousAt
    exact hca.eventually_ne (by norm_num)
  have hev : (fun t : ℂ => Phi lam (z + t • (z * Matrix.single a b 1))) =ᶠ[nhds 0] fun _ => Phi lam z := by
    filter_upwards [hc] with t ht
    have hm := GlobalTheory.PhiEigenfun.Phi_mul_single lam hz hab.le ht
    rw [if_neg hne, one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul] at hm
    exact hm
  have h2 : HasDerivAt (fun t : ℂ => Phi lam (z + t • (z * Matrix.single a b 1))) 0 0 :=
    (hasDerivAt_const (0 : ℂ) (Phi lam z)).congr_of_eventuallyEq hev
  exact h1.unique h2

def sgn (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

lemma star_entry {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) (a b : Fin n) :
    star (Y a b) = -(sgn ε b * sgn ε a) * Y b a := by
  have h' : Yᴴ * Jm ε + Jm ε * Y = 0 := h
  have h1 := congrFun (congrFun h' b) a
  simp only [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply] at h1
  unfold sgn
  rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
    rcases Bool.eq_false_or_eq_true (ε b) with hb | hb <;>
    simp only [ha, hb, if_true, if_false, Bool.false_eq_true] at h1 ⊢ <;>
    first | linear_combination h1 | linear_combination -h1

lemma inG_conj {ε : Fin n → Bool} {k X : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (hX : inG ε X) :
    inG ε (k⁻¹ * X * k) := by
  obtain ⟨hu, hJ⟩ := hk
  have hkk : kᴴ * k = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hu
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hkk
  have hJ' : Jm ε * kᴴ = kᴴ * Jm ε := by
    have h2 := congrArg Matrix.conjTranspose hJ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTranspose] at h2
    exact h2
  have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  show (k⁻¹ * X * k)ᴴ * Jm ε + Jm ε * (k⁻¹ * X * k) = 0
  rw [hinv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc kᴴ * (Xᴴ * k) * Jm ε + Jm ε * (kᴴ * X * k)
      = kᴴ * Xᴴ * (k * Jm ε) + Jm ε * kᴴ * X * k := by simp only [Matrix.mul_assoc]
    _ = kᴴ * (Xᴴ * Jm ε + Jm ε * X) * k := by
        rw [hJ, hJ']; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX', Matrix.mul_zero, Matrix.zero_mul]

theorem exists_deriv_Phi_conj : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), ∃ l : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ → ℂ, (∀ c d z, d < c → l c d z = 0) ∧ (∀ c d, ContinuousOn (l c d) (Omega n)) ∧ ∀ k ∈ Kset ε, ∀ g ∈ UJset ε, k⁻¹ * g * k ∈ Omega n → ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → HasDerivAt (fun t : ℝ => Phi lam ((k⁻¹ * (g * NormedSpace.exp ((t : ℂ) • X)) * k).map star)) (∑ c, ∑ d, (k⁻¹ * X * k) c d * l c d (k⁻¹ * g * k)) 0 := by
  intro n ε lam
  refine ⟨fun c d z => if d < c then 0 else
    -(sgn ε c * sgn ε d) * star (fderiv ℂ (Phi lam) z (z * Matrix.single d c 1)), ?_, ?_, ?_⟩
  · intro c d z hdc
    simp only [hdc, if_true]
  · intro c d
    by_cases hdc : d < c
    · simp only [hdc, if_true]
      exact continuousOn_const
    · simp only [hdc, if_false]
      have hA : AnalyticOnNhd ℂ (Phi lam) (Omega n) := fun z hz => analyticAt_Phi lam hz
      have hF : ContinuousOn (fderiv ℂ (Phi lam)) (Omega n) := hA.fderiv.continuousOn
      have hv : ContinuousOn (fun z : Matrix (Fin n) (Fin n) ℂ => z * Matrix.single d c 1) (Omega n) :=
        (continuous_id.matrix_mul continuous_const).continuousOn
      exact continuousOn_const.mul (hF.clm_apply hv).star
  · intro k hk g hg hw X hX
    have hkk : kᴴ * k = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hk.1
    have hkk' : k * kᴴ = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hk.1
    have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv hkk
    have hYG : inG ε (k⁻¹ * X * k) := inG_conj hk hX

    let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
      LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℂ k⁻¹).comp (LinearMap.mulRight ℂ k))
    have hL : ∀ M, L M = k⁻¹ * (M * k) := fun M => rfl
    have hcurve : HasDerivAt (fun s : ℂ => k⁻¹ * (g * NormedSpace.exp (s • X)) * k)
        ((k⁻¹ * g * k) * (k⁻¹ * X * k)) 0 := by
      have h0 := L.hasFDerivAt.comp_hasDerivAt (0 : ℂ) (GlobalTheory.PhiEigenfun.hasDerivAt_curve g X)
      have hLgX : L (g * X) = (k⁻¹ * g * k) * (k⁻¹ * X * k) := by
        rw [hL, hinv]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc k kᴴ (X * k), hkk', Matrix.one_mul]
      refine (h0.congr_deriv hLgX).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      exact Matrix.mul_assoc _ _ _
    have hP : HasFDerivAt (Phi lam) (fderiv ℂ (Phi lam) (k⁻¹ * g * k))
        (k⁻¹ * (g * NormedSpace.exp ((0 : ℂ) • X)) * k) := by
      rw [zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
      exact (analyticAt_Phi lam hw).differentiableAt.hasFDerivAt
    have hφ := hP.comp_hasDerivAt (0 : ℂ) hcurve
    have hφ' : HasDerivAt (fun s : ℂ => Phi lam (k⁻¹ * (g * NormedSpace.exp (s • X)) * k))
        (fderiv ℂ (Phi lam) (k⁻¹ * g * k) ((k⁻¹ * g * k) * (k⁻¹ * X * k))) ((0 : ℝ) : ℂ) := by
      rw [Complex.ofReal_zero]
      exact hφ
    have hst := hφ'.comp_ofReal.star

    have hexp : ∀ (w Y : Matrix (Fin n) (Fin n) ℂ), fderiv ℂ (Phi lam) w (w * Y) =
        ∑ c, ∑ d, Y c d * fderiv ℂ (Phi lam) w (w * Matrix.single c d 1) := by
      intro w Y
      conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
      simp only [Matrix.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      have hs : Matrix.single c d (Y c d) = Y c d • Matrix.single c d (1 : ℂ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [hs, Matrix.mul_smul, map_smul, smul_eq_mul]
    have hD0 : ∀ c d : Fin n, d < c → fderiv ℂ (Phi lam) (k⁻¹ * g * k) ((k⁻¹ * g * k) * Matrix.single d c 1) = 0 :=
      fun c d h => fderiv_Phi_single lam hw h
    have hfun : (fun t : ℝ => Phi lam ((k⁻¹ * (g * NormedSpace.exp ((t : ℂ) • X)) * k).map star)) =
        fun t : ℝ => star (Phi lam (k⁻¹ * (g * NormedSpace.exp ((t : ℂ) • X)) * k)) := by
      funext t
      exact GlobalTheory.Dec.FormF.Phi_star lam _
    rw [hfun]
    refine hst.congr_deriv ?_
    rw [hexp, star_sum]
    simp only [star_sum, star_mul', star_entry hYG]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    split_ifs with h
    · rw [hD0 _ _ h]
      simp
    · ring

end GlobalTheory.PhiConjDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalLieCoordinates
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas Formalism.REAL

noncomputable section

namespace GlobalTheory.NilCovSec

open GlobalTheory.NilCov

variable {n : ℕ}

def jInv (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := Jm ε * Xᴴ * Jm ε

variable (ε : Fin n → Bool)

theorem jInv_sub (X Y : Matrix (Fin n) (Fin n) ℂ) : jInv ε (X - Y) = jInv ε X - jInv ε Y := by
  simp only [jInv, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]

theorem jInv_smul (a : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : jInv ε (a • X) = a • jInv ε X := by
  simp [jInv, conjTranspose_smul]

theorem jInv_jInv_mul (X : Matrix (Fin n) (Fin n) ℂ) : jInv ε (jInv ε X * X) = jInv ε X * X := by
  simp only [jInv, conjTranspose_mul, Jm_conjTranspose, conjTranspose_conjTranspose, Matrix.mul_assoc,
    Jm_mul_self, Matrix.mul_one]

theorem continuous_jInv : Continuous (jInv ε) := by
  exact (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const

def iter (Y : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Nat.rec Y (fun _ X => Y - (1 / 2 : ℝ) • (jInv ε X * X)) k

theorem continuous_iter (k : ℕ) : Continuous fun Y => iter ε Y k := by
  induction k with
  | zero => exact continuous_id
  | succ k ih =>
    exact continuous_id.sub ((((continuous_jInv ε).comp ih).matrix_mul ih).const_smul (1 / 2 : ℝ))

variable {ε} {A : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}

theorem iter_mem (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (hle : ∀ c, A (c + 1) ≤ A c) (hinv : ∀ c, ∀ X ∈ A c, Jm ε * Xᴴ * Jm ε ∈ A c)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ A 0) (k : ℕ) : iter ε Y k ∈ A 0 := by
  induction k with
  | zero => exact hY
  | succ k ih =>
    exact (A 0).sub_mem hY ((A 0).smul_mem _ (hle 0 (hmul 0 _ (hinv 0 _ ih) _ ih).1))

theorem iter_sub_mem (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (hle : ∀ c, A (c + 1) ≤ A c) (hinv : ∀ c, ∀ X ∈ A c, Jm ε * Xᴴ * Jm ε ∈ A c)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ A 0) (k : ℕ) : iter ε Y (k + 1) - iter ε Y k ∈ A k := by
  have hm := iter_mem hmul hle hinv hY
  induction k with
  | zero => exact (A 0).sub_mem (hm 1) (hm 0)
  | succ k ih =>
    have e : iter ε Y (k + 1 + 1) - iter ε Y (k + 1) =
        (-(1 / 2) : ℝ) • (jInv ε (iter ε Y (k + 1) - iter ε Y k) * iter ε Y (k + 1) +
          jInv ε (iter ε Y k) * (iter ε Y (k + 1) - iter ε Y k)) := by
      have e1 : iter ε Y (k + 1 + 1) =
        Y - (1 / 2 : ℝ) • (jInv ε (iter ε Y (k + 1)) * iter ε Y (k + 1)) := rfl
      have e2 : iter ε Y (k + 1) = Y - (1 / 2 : ℝ) • (jInv ε (iter ε Y k) * iter ε Y k) := rfl
      rw [e1]
      generalize iter ε Y (k + 1) = P at e2 ⊢
      generalize iter ε Y k = Q at e2 ⊢
      rw [jInv_sub, Matrix.sub_mul, Matrix.mul_sub]
      nth_rewrite 3 [e2]
      module
    rw [e]
    exact (A _).smul_mem _ ((A _).add_mem (hmul k _ (hinv k _ ih) _ (hm _)).1
      (hmul k _ ih _ (hinv 0 _ (hm _))).2)

theorem one_add_mul_of_fixed {X Y : Matrix (Fin n) (Fin n) ℂ} (hY : jInv ε Y = -Y)
    (h : X = Y - (1 / 2 : ℝ) • (jInv ε X * X)) : (1 + jInv ε X) * (1 + X) = 1 := by
  have h2 : jInv ε X = -Y - (1 / 2 : ℝ) • (jInv ε X * X) := by
    conv_lhs => rw [h]
    rw [jInv_sub, jInv_smul, jInv_jInv_mul, hY]
  have h3 : X + jInv ε X + jInv ε X * X = 0 := by
    generalize jInv ε X * X = P at h h2 ⊢
    rw [h2, h]
    module
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]
  calc 1 + X + (jInv ε X + jInv ε X * X) = 1 + (X + jInv ε X + jInv ε X * X) := by abel
    _ = 1 := by rw [h3, add_zero]

theorem inUJ_of_one_add_mul {X : Matrix (Fin n) (Fin n) ℂ} (h : (1 + jInv ε X) * (1 + X) = 1) :
    (1 + X)ᴴ * Jm ε * (1 + X) = Jm ε := by
  have e : (1 + X)ᴴ * Jm ε = Jm ε * (1 + jInv ε X) := by
    rw [conjTranspose_add, conjTranspose_one, Matrix.add_mul, Matrix.mul_add, jInv, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]
  rw [e, Matrix.mul_assoc, h, Matrix.mul_one]

theorem exists_continuous_section (n d m : ℕ) (ε : Fin n → Bool)
    (A : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hA : A m = ⊥) (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (hle : ∀ c, A (c + 1) ≤ A c)
    (hinv : ∀ c, ∀ X ∈ A c, Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε ∈ A c)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hG : ∀ i, E i ∈ A 0 ∧ Formalism.REAL.inG ε (E i)) :
    ∃ σ : (Fin d → ℝ) → Formalism.REAL.UJ ε, Continuous σ ∧ ∀ x, uMat (σ x) - 1 ∈ A 0 ∧
      ∀ i, (((uMat (σ x) - 1) * (E i)ᴴ).trace).re = x i := by
  let Y : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun x => ∑ i, x i • E i
  have hYc : Continuous Y := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_apply i).smul continuous_const
  have hY0 : ∀ x, Y x ∈ A 0 := fun x =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hG i).1
  have hYθ : ∀ x, jInv ε (Y x) = -Y x := fun x => by
    simp only [jInv, Y, conjTranspose_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := jInv_smul ε (x i) (E i)
    unfold jInv at this
    rw [this, inv_eq_neg_of_inG (hG i).2, smul_neg]
  let X : (Fin d → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun x => iter ε (Y x) m
  have hXc : Continuous X := (continuous_iter ε m).comp hYc
  have hfix : ∀ x, X x = Y x - (1 / 2 : ℝ) • (jInv ε (X x) * X x) := fun x => by
    have h := iter_sub_mem hmul hle hinv (hY0 x) m
    rw [hA, Submodule.mem_bot, sub_eq_zero] at h
    exact h.symm
  have h1 : ∀ x, (1 + jInv ε (X x)) * (1 + X x) = 1 := fun x => one_add_mul_of_fixed (hYθ x) (hfix x)
  let u : (Fin d → ℝ) → (Matrix (Fin n) (Fin n) ℂ)ˣ := fun x =>
    ⟨1 + X x, 1 + jInv ε (X x), mul_eq_one_comm.1 (h1 x), h1 x⟩
  have huc : Continuous u := Units.continuous_iff.2
    ⟨continuous_const.add hXc, continuous_const.add ((continuous_jInv ε).comp hXc)⟩
  have hu : ∀ x, u x ∈ UJ ε := fun x => inUJ_of_one_add_mul (h1 x)
  refine ⟨fun x => ⟨u x, hu x⟩, huc.subtype_mk hu, fun x => ?_⟩
  have e : uMat (⟨u x, hu x⟩ : UJ ε) - 1 = X x := by
    change 1 + X x - 1 = X x
    abel
  rw [e]
  refine ⟨iter_mem hmul hle hinv (hY0 x) m, fun i => ?_⟩
  have h0 : ipL (E i) (jInv ε (X x) * X x) = 0 := by
    have h := ipL_inv (hG i).2 (jInv ε (X x) * X x)
    have h' : ipL (E i) (jInv ε (jInv ε (X x) * X x)) = -ipL (E i) (jInv ε (X x) * X x) := h
    rw [jInv_jInv_mul] at h'
    linarith
  rw [← ipL_apply, hfix x, map_sub, map_smul, h0, smul_zero, sub_zero]
  simp only [Y, map_sum, map_smul, ipL_apply, hE, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

end GlobalTheory.NilCovSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRadicalNormalFormPairOfFlagsStatement
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_radical_normalForm_pair_of_flags : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (p : Point ℂ (r + 1)), TwoFl k r z z' g₀ → ZhatO k r z z' g₀ = ptMat p → ∃ p₁ p₀ : PPar k r, pOf k r p₀ *ᵥ z' = z' ∧ IsNormal k r (fun a => blockIdx p.1 a.val) (pOf k r p₁ * g₀ * (pOf k r p₀)⁻¹) ∧ Zr k r (pOf k r p₁ * g₀ * (pOf k r p₀)⁻¹) = Zr k r g₀ ∧ ∀ a : Fin r, blockIdx p.1 a.val ≠ blockIdx p.1 r := by
  first | exact @GlobalTheory.Amp.NormalEx.normal_form | exact GlobalTheory.Amp.NormalEx.normal_form | (intros; apply GlobalTheory.Amp.NormalEx.normal_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSymmInvariantKernelHermitianFramesStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symm_invariant_kernel_hermitian_frames : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ Λ, P Λ ↔ (S.IsTerm d Λ ∧ S.InFF β (j + 1) βJ d Λ)) → ∃ m : Submodule L.O S.V → Submodule L.O S.V → ℝ, (∀ h ∈ S.St, ∀ x y, P x → P y → m (h • x) (h • y) = m x y) ∧ ∀ x, P x → {y | P y ∧ m x y ≠ 0}.Finite ∧ (∀ y, P y → 0 ≤ m x y ∧ m x y = m y x) ∧ |(∑ᶠ y : {y // P y}, m x y) - 1| ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) ∧ ‖∑ᶠ y : {y // P y}, (m x y : ℂ) * S.om d y‖ ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  first | exact @GlobalTheory.HL.exists_symm_invariant_kernel | exact GlobalTheory.HL.exists_symm_invariant_kernel | (intros; apply GlobalTheory.HL.exists_symm_invariant_kernel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryTorusScaleBesselCharacterStatement
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryTorus_scale_besselCharacter : ∀ (k r : ℕ) (c : ℂ), c ≠ 0 → ∃ t ∈ GG k r, (∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r) ∧ (∀ z, inWb k r z → t *ᵥ z = z ∧ (∀ h ∈ UWset k r z, t * h = h * t) ∧ ∀ n ∈ Nset k r, psi k r z cStd n = psi k r z c (t * n * t⁻¹)) ∧ ∀ a : Fin (r + 1), ∃ s : ℂ, s ≠ 0 ∧ ‖s‖ ≤ max (‖c‖ / 2) (2 / ‖c‖) ^ r ∧ ‖s‖⁻¹ ≤ max (‖c‖ / 2) (2 / ‖c‖) ^ r ∧ ∀ z, inWb k r z → t⁻¹ *ᵥ fvec k r z a = s • fvec k r z a := by
  first | exact @GlobalTheory.TorusScale.exists_torus_scale | exact GlobalTheory.TorusScale.exists_torus_scale | (intros; apply GlobalTheory.TorusScale.exists_torus_scale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedVectorDifferentiableStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_orbit_and_decay_of_decay : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : H), IsURepOn (UJset ε) σ → SmoothOnG ε α → HasCompactSupport (fun g : UJ ε => α (umat g)) → (∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) w⟫_ℂ ∂(muG ε) = ⟪u, w⟫_ℂ) → ∃ L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] H, ∀ X, inG ε X → HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) w) (L X) 0 ∧ ∀ (c : ℝ) (v : H), 0 ≤ c → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) w⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) (L X)⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) := by
  first | exact @GlobalTheory.GardingVec.fixed_vector_differentiable | exact GlobalTheory.GardingVec.fixed_vector_differentiable | (intros; apply GlobalTheory.GardingVec.fixed_vector_differentiable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGramNumberNormalizedInvarianceStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagGramNumberNormalized_invariance : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ γ : Mat k r, inWb k r z → inWb k r z' → γ ∈ GG k r → ∀ x ∈ GG k r, (∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), Yj k r hj z z' γ (x * κ) = Yj k r hj z z' γ x) ∧ (∀ n₁ ∈ Nset k r, ∀ n₂ ∈ Nset k r, Yj k r hj z z' (n₁ * γ * n₂) x = Yj k r hj z z' γ (n₂ * x)) ∧ ∀ ρ ∈ Rset k r γ, Yj k r hj z z' γ (ρ * x) = Yj k r hj z z' γ x := by
  first | exact @GlobalTheory.Amp.YjInv.yj_invariant | exact GlobalTheory.Amp.YjInv.yj_invariant | (intros; apply GlobalTheory.Amp.YjInv.yj_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeProportionalStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_degree_proportional : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS), cdScaleTie D → GoodW D τ w w' θ W → ∃ κ : ℝ, 0 < κ ∧ ∀ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A → ∀ v : A.H, v ≠ 0 → A.deg = κ * PI.BesselPeriodGGP.fdegH W.μG A.σ v ∧ 0 < A.deg := by
  first | exact @GlobalTheory.DegreeTie.deg_eq_mul_fdegH | exact GlobalTheory.DegreeTie.deg_eq_mul_fdegH | (intros; apply GlobalTheory.DegreeTie.deg_eq_mul_fdegH <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasDerivAtCompletedTensorOrbitSmoothAverageStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_completedTensorOrbit_smoothAverage : ∀ (B : RowsAut) (F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ) (E : gInf B) (w : B.Hs), IsURep B.σs → ContDiff ℝ ∞ F → HasCompactSupport F → ∃ F' : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F' ∧ HasCompactSupport F' ∧ HasDerivAt (orbit B E (∫ g, F (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I))) (∫ g, F' (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I)) 0 := by
  first | exact @GlobalTheory.AverageDeriv.hasDerivAt_orbit_average | exact GlobalTheory.AverageDeriv.hasDerivAt_orbit_average | (intros; apply GlobalTheory.AverageDeriv.hasDerivAt_orbit_average <;> assumption)
end

