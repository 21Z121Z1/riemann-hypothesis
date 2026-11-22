import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0033
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0036
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0013
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0011
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0014
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0009
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0001
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0007
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirrorDecomposition.HpkRowEsI

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupCayleyBound
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.RatioMoment

theorem iterate_bound {X M ι : Type} [MeasurableSpace X] [NormedAddCommGroup M] [Fintype ι] (μ : Measure X)
    (κ : X → ℝ) (f : M → X → ℝ) (T : ι → ι → M → M) (L : ℕ → M → Prop) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hκ : AEMeasurable κ μ) (hf : ∀ w, AEMeasurable (f w) μ) (hf0 : ∀ w x, 0 ≤ f w x)
    (hpt : ∀ᵐ x ∂μ, ∀ w, κ x ^ 2 * f w x ≤ ∑ c, ∑ e, f (T c e w) x)
    (hL : ∀ j w, L j w → ∀ c e, L (j + 2) (T c e w))
    (hs : ∀ j w, j ≤ N → L j w → ∑ c, ∑ e, ‖T c e w‖ ^ 2 ≤ B ^ 2 * ‖w‖ ^ 2)
    (h0 : ∀ w, ∫⁻ x, ENNReal.ofReal (1 * f w x) ∂μ ≤ ENNReal.ofReal (‖w‖ ^ 2)) :
    ∀ q j, j + 2 * q ≤ N → ∀ w, L j w →
      ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * q) * f w x) ∂μ ≤ ENNReal.ofReal (B ^ (2 * q) * ‖w‖ ^ 2) := by
  intro q
  induction q with
  | zero =>
    intro j _ w _
    simpa using h0 w
  | succ q ih =>
    intro j hj w hw
    have hN : j ≤ N := by omega
    have hpos : ∀ x, 0 ≤ κ x ^ (2 * q) := fun x => (even_two_mul q).pow_nonneg _
    have hm : ∀ v, AEMeasurable (fun x => ENNReal.ofReal (κ x ^ (2 * q) * f v x)) μ :=
      fun v => ENNReal.measurable_ofReal.comp_aemeasurable ((hκ.pow_const _).mul (hf v))
    calc ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * (q + 1)) * f w x) ∂μ
        ≤ ∫⁻ x, ∑ c, ∑ e, ENNReal.ofReal (κ x ^ (2 * q) * f (T c e w) x) ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [hpt] with x hx
          have h1 : κ x ^ (2 * (q + 1)) * f w x ≤ ∑ c, ∑ e, κ x ^ (2 * q) * f (T c e w) x := by
            calc κ x ^ (2 * (q + 1)) * f w x = κ x ^ (2 * q) * (κ x ^ 2 * f w x) := by ring
              _ ≤ κ x ^ (2 * q) * ∑ c, ∑ e, f (T c e w) x := mul_le_mul_of_nonneg_left (hx w) (hpos x)
              _ = ∑ c, ∑ e, κ x ^ (2 * q) * f (T c e w) x := by simp_rw [Finset.mul_sum]
          calc ENNReal.ofReal (κ x ^ (2 * (q + 1)) * f w x)
              ≤ ENNReal.ofReal (∑ c, ∑ e, κ x ^ (2 * q) * f (T c e w) x) := ENNReal.ofReal_le_ofReal h1
            _ = ∑ c, ∑ e, ENNReal.ofReal (κ x ^ (2 * q) * f (T c e w) x) := by
              rw [ENNReal.ofReal_sum_of_nonneg
                (fun c _ => Finset.sum_nonneg (fun e _ => mul_nonneg (hpos x) (hf0 _ x)))]
              refine Finset.sum_congr rfl (fun c _ => ?_)
              exact ENNReal.ofReal_sum_of_nonneg (fun e _ => mul_nonneg (hpos x) (hf0 _ x))
      _ = ∑ c, ∑ e, ∫⁻ x, ENNReal.ofReal (κ x ^ (2 * q) * f (T c e w) x) ∂μ := by
          rw [lintegral_finsetSum' _ (fun c _ => Finset.aemeasurable_fun_sum _ (fun e _ => hm _))]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          exact lintegral_finsetSum' _ (fun e _ => hm _)
      _ ≤ ∑ c, ∑ e, ENNReal.ofReal (B ^ (2 * q) * ‖T c e w‖ ^ 2) := by
          gcongr with c _ e _
          exact ih (j + 2) (by omega) _ (hL j w hw c e)
      _ = ENNReal.ofReal (B ^ (2 * q) * ∑ c, ∑ e, ‖T c e w‖ ^ 2) := by
          simp_rw [Finset.mul_sum]
          rw [ENNReal.ofReal_sum_of_nonneg (fun c _ => Finset.sum_nonneg
            (fun e _ => mul_nonneg (pow_nonneg hB _) (sq_nonneg _)))]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => mul_nonneg (pow_nonneg hB _) (sq_nonneg _))]
      _ ≤ ENNReal.ofReal (B ^ (2 * (q + 1)) * ‖w‖ ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          calc B ^ (2 * q) * ∑ c, ∑ e, ‖T c e w‖ ^ 2 ≤ B ^ (2 * q) * (B ^ 2 * ‖w‖ ^ 2) :=
                mul_le_mul_of_nonneg_left (hs j w hN hw) (pow_nonneg hB _)
            _ = B ^ (2 * (q + 1)) * ‖w‖ ^ 2 := by ring

theorem ratio_moment : HypsG → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), SetupG lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ ν, n1 ν ≤ q0 → ∀ (j q : ℕ), j + 2 * q ≤ 4 * (2 * r + k + 1) ^ 2 → ∀ (a : Fin r) (w : (R ν).smSub), Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc) ^ (2 * q) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ 2) ^ (2 * q) * ‖w‖ ^ 2) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hn j q hjq a w hw
  have h0all := (Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hn).1
  obtain ⟨hnum, hfam, hside, hsf⟩ := hS
  have hk : 1 ≤ k := hnum.1
  have hDG := hfam ν hn
  obtain ⟨hE1, hGl⟩ := hE ν hn
  have hMod := Gp91.GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hk hDG Q (E ν) hQ hE1
  obtain ⟨hBeL, hdg, -⟩ := hsf ν hn
  have hKF : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨hae, -, hlen, hmeas⟩ :=
    Gp91.GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hKF k r _ _ (R ν) Wp z π u μW μN μG νq hDG hside
  have hν : ∀ i, |((ν i : ℤ) : ℝ)| ≤ q0 := by
    intro i
    have h1 : (ν i).natAbs ≤ n1 ν :=
      Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : ((ν i).natAbs : ℝ) ≤ q0 := by exact_mod_cast h1.trans hn
    rwa [Nat.cast_natAbs, Int.cast_abs] at h2
  obtain ⟨-, -, -, -, -, hlo, hhi, hbd, -, hga, hgap, -, hq0ga, hq0h, hbv⟩ := hnum
  have i0 : k - 1 < 2 * r + k + 1 := by omega
  have i1 : k < 2 * r + k + 1 := by omega
  have hbvq : 100 * ((q0 : ℝ) + 1) ≤ bv := by
    have e1 : k - (k - 1) = 1 := by omega
    have e2 : ¬ k < k - 1 := by omega
    have hne : PI.BesselPeriodGGP.eps48 k r ⟨k - 1, i0⟩ ≠ PI.BesselPeriodGGP.eps48 k r ⟨k, i1⟩ := by
      simp [PI.BesselPeriodGGP.eps48, e1, e2]
    have g1 := hgap _ _ hne
    have a1 := hhi ⟨k - 1, i0⟩ (show k ≤ k - 1 + 1 by omega)
    have a2 := hhi ⟨k, i1⟩ (show k ≤ k + 1 by omega)
    have : |lam ⟨k - 1, i0⟩ - lam ⟨k, i1⟩| ≤ bv := by
      rw [abs_le]; constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
    have hq0h' : 100 * ((q0 : ℝ) + 1) ≤ h := by exact_mod_cast hq0h
    linarith
  have hbvb : bv ≤ b := by
    have a1 := hhi ⟨k - 1, i0⟩ (show k ≤ k - 1 + 1 by omega)
    have := hbd ⟨k - 1, i0⟩
    rw [abs_le] at this
    linarith [a1.2]
  have hShape : BranchingSupport.Shape (PI.BesselPeriodGGP.eps48 k r) k
      (fun i => lam i + ((ν i : ℤ) : ℝ)) bv := by
    obtain ⟨h', hgap', hgok'⟩ := hDG.gap
    have hmuA := hDG.hc.1
    have hh' : 2 ≤ h' := by
      have := hgok'.2.1
      have : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1))
      nlinarith
    have hq0 : ((q0 : ℝ)) ≤ bv / 100 := by linarith
    refine ⟨hk, by omega, ?_, ?_, ?_, hbv⟩
    · intro x c hxc
      have hpos : ∀ y y' : Fin (2 * r + k + 1), y < y' →
          0 < (lam y + ((ν y : ℤ) : ℝ)) - (lam y' + ((ν y' : ℤ) : ℝ)) :=
        fun y y' hyy => sub_pos.2 (hmuA hyy)
      have hdiff : ∀ y y' : Fin (2 * r + k + 1), y < y' →
          PI.BesselPeriodGGP.eps48 k r y ≠ PI.BesselPeriodGGP.eps48 k r y' →
          2 ≤ (lam y + ((ν y : ℤ) : ℝ)) - (lam y' + ((ν y' : ℤ) : ℝ)) := by
        intro y y' hyy hne
        have g := hgap' y y' hne
        rw [abs_of_pos (hpos y y' hyy)] at g
        linarith
      by_cases hε : PI.BesselPeriodGGP.eps48 k r x = PI.BesselPeriodGGP.eps48 k r c
      · have hxc' : (x : ℕ) < c := hxc
        have nx := hν x
        have nc := hν c
        rw [abs_le] at nx nc
        by_cases hc : (c : ℕ) + 1 < k
        · have := hga x c hxc hc
          have hq0ga' : 100 * ((q0 : ℝ) + 1) ≤ ga := by exact_mod_cast hq0ga
          linarith
        · by_cases hc' : (c : ℕ) = k - 1
          · have l1 := hlo x (by omega)
            have l2 := hhi c (by omega)
            linarith [l1.1, l2.2]
          · have hb' : (c : ℕ) - 1 < 2 * r + k + 1 := by omega
            let y : Fin (2 * r + k + 1) := ⟨c - 1, hb'⟩
            have hyc : y < c := by show (c : ℕ) - 1 < c; omega
            have hεy : PI.BesselPeriodGGP.eps48 k r y ≠ PI.BesselPeriodGGP.eps48 k r c := by
              have n1' : ¬ ((c : ℕ) - 1 < k - 1) := by omega
              have n2' : ¬ ((c : ℕ) < k - 1) := by omega
              simp only [PI.BesselPeriodGGP.eps48, y, n1', n2', if_false]
              rcases Nat.mod_two_eq_zero_or_one ((c : ℕ) - (k - 1)) with h0 | h1
              · have : ((c : ℕ) - 1 - (k - 1)) % 2 = 1 := by omega
                simp [h0, this]
              · have : ((c : ℕ) - 1 - (k - 1)) % 2 = 0 := by omega
                simp [h1, this]
            have hxy : x < y := by
              have hle : (x : ℕ) ≤ (c : ℕ) - 1 := by omega
              rcases Nat.lt_or_ge (x : ℕ) ((c : ℕ) - 1) with hlt | hge
              · exact hlt
              · exfalso
                have hxeq : x = y := Fin.ext (by show (x : ℕ) = (c : ℕ) - 1; omega)
                exact hεy (hxeq ▸ hε)
            have d1 := hpos x y hxy
            have d2 := hdiff y c hyc hεy
            linarith
      · exact hdiff x c hxc hε
    · intro x hx
      have hx' : (x : ℕ) < k - 1 := by omega
      refine ⟨by simp [PI.BesselPeriodGGP.eps48, hx'], ?_, ?_⟩ <;>
      · have l1 := hlo x hx
        have nx := hν x
        rw [abs_le] at nx
        linarith [l1.1, l1.2]
    · intro x hx
      have l1 := hhi x hx
      have nx := hν x
      rw [abs_le] at nx
      constructor <;> linarith [l1.1, l1.2]
  refine iterate_bound νq
    (fun x => lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc)
    (fun (w : ↥(R ν).smSub) x => dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)
    (fun c e w => E ν c e w)
    (fun j w => Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun i => lam i + ((ν i : ℤ) : ℝ)) j w)
    (4 * (2 * r + k + 1) ^ 2) (b ^ 2) (sq_nonneg b) ?_ ?_ ?_ ?_ ?_ ?_ ?_ q j hjq w hw
  · exact (hlen a.succ).div (hlen a.castSucc)
  · intro v
    exact (((hmeas (l ν) hBeL.1 v v.2).norm).aemeasurable.pow_const 2).const_mul (dg ν)
  · intro v x
    exact mul_nonneg hdg.le (sq_nonneg _)
  · filter_upwards [hae] with x hx
    intro v
    have h1 := Gp91.GlobalTheory.T.bessel_cayley_side_bound hKF k r _ _ (R ν) Wp z π u μW μN μG νq (l ν) Q (E ν) hDG hside
      hBeL.1 hQ hE1 (Matrix.of x) hx a v
    have h2 := mul_le_mul_of_nonneg_left h1 hdg.le
    simp only [Finset.mul_sum] at h2
    beta_reduce
    calc _ = dg ν * ((lenA k r z (Matrix.of x) a.succ / lenA k r z (Matrix.of x) a.castSucc) ^ 2 *
          ‖l ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) := by ring
      _ ≤ _ := h2
  · intro j' v hv c e
    exact _root_.GlobalTheory.lev_E_add_two _ _ _ _ _ j' v hGl hMod.2.1 hv c e
  · intro j' v hj' hv
    have := _root_.GlobalTheory.T.unitaryGlModule_level_sum_norm_sq_le _ _ _ _ _ k j' bv b v hMod hShape hbvb hj' hv
    calc _ ≤ b ^ 4 * ‖v‖ ^ 2 := this
      _ = (b ^ 2) ^ 2 * ‖v‖ ^ 2 := by ring
  · intro v
    exact h0all v v.2

end GlobalTheory.RatioMoment
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupMomentGrowthStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.lowering_scalar_sq_mul_degree_ratio_le : HypsG → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), SetupG lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + 1 ≤ q0 → ∀ io pr ep, TensH dualM (Formalism.QuantumDeterminants.Hpk k r) (R ν) (fun s => R (ν - Pi.single s 1)) io pr ep → NzOn (R ν) (l ν) → ∀ (s : Fin (2 * r + k + 1)) (κ₀ : ℂ), (∀ v ∈ (R ν).sm, l (ν - Pi.single s 1) (∑ c, pr s c (tm (R ν) (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v c)) = κ₀ • l ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν - Pi.single s 1) ≤ Formalism.QuantumDeterminants.Tz k r z * b ^ 4 := by
  first | exact @GlobalTheory.DualStepBound.dual_step_bound | exact GlobalTheory.DualStepBound.dual_step_bound | (intros; apply GlobalTheory.DualStepBound.dual_step_bound <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorMomentTransferStatement
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.tensor_moment_transfer : HypsG → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (Bm : R.H → Wp) (BI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → Function.Injective muI → TensRaw ρ R RI io pr → SideG k r z π u μW μN μG νq → IsBes R z π Bm → (∀ I, IsIsoB (RI I) z π νq (BI I) ∨ β I = 0) → (∀ I, ∀ y ∈ (RI I).sm, Bm (ev Γ R om (fun c => io I c y)) = β I • BI I y) → ∀ I, IsIsoB (RI I) z π νq (BI I) → ∀ y ∈ (RI I).sm, ∀ (a : ι → ℂ), ∀ w ∈ R.sm, ∫ x, ⟪BI I ((RI I).σ (Matrix.of x) y), Formalism.QuantumDeterminants.herm Γ (ρ (Matrix.of x) *ᵥ a) om • Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = β I * ⟪y, ∑ c, pr I c (tm R a w c)⟫_ℂ := by
  first | exact @GlobalTheory.BesselPairing.pairing | exact GlobalTheory.BesselPairing.pairing | (intros; apply GlobalTheory.BesselPairing.pairing <;> assumption)
end Gp91
end

-- bundled from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorWeightedBesselGap
section
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselPieri

theorem gg_mul {k r : ℕ} {a b : Mx k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [ha', hb']

theorem one_gg (k r : ℕ) : (1 : Mx k r) ∈ GG k r := by
  show (1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
  simp

theorem one_N (k r : ℕ) : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.Nset k r :=
  ⟨one_gg k r, fun _ _ _ => Matrix.one_apply, fun _ _ _ _ _ => Matrix.one_apply⟩

theorem one_UW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.UWset k r z :=
  ⟨one_gg k r, fun _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩

theorem herm_iso {ι : Type} [Fintype ι] [DecidableEq ι] {Γ A : Matrix ι ι ℂ} (hA : Aᴴ * Γ * A = Γ) (x y : ι → ℂ) :
    Formalism.QuantumDeterminants.herm Γ (A *ᵥ x) (A *ᵥ y) = Formalism.QuantumDeterminants.herm Γ x y := by
  unfold Formalism.QuantumDeterminants.herm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hA]

theorem coef_inv {k r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : Mx k r → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ}
    {d : ℕ} (hρ : IsFRep ρ Γ d) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {om om' : ι → ℂ}
    (h1 : ∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z, ρ g *ᵥ om = om) (h2 : ∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z', ρ g *ᵥ om' = om')
    {γ : Mx k r} (hγ : γ ∈ GG k r) (p : B.SS k r) (hp : D.inSS p) :
    Formalism.QuantumDeterminants.herm Γ (ρ (B.sgs p γ) *ᵥ om') om = Formalism.QuantumDeterminants.herm Γ (ρ γ *ᵥ om') om := by
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  obtain ⟨-, -, -, hmul, hiso, -⟩ := hρ
  have hi := PI.MirrorSection₂.uw_inv hh
  have ni := PI.MirrorSection₂.n_inv hn
  have ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GG k r := gg_mul hi.1 ni.1
  have e1 := h1 _ ⟨_, hi, _, ni, rfl⟩
  have e2 : ρ (Matrix.of p.2.1) *ᵥ om' = om' := h2 _ ⟨_, hh', 1, one_N k r, (Matrix.mul_one _).symm⟩
  have e3 : ρ (Matrix.of p.2.2) *ᵥ om' = om' := h2 _ ⟨1, one_UW k r _, _, hn', (Matrix.one_mul _).symm⟩
  unfold B.sgs
  rw [hmul _ (gg_mul (gg_mul ha hγ) hn'.1) _ hh'.1, hmul _ (gg_mul ha hγ) _ hn'.1, hmul _ ha _ hγ,
    ← mulVec_mulVec, e2, ← mulVec_mulVec, e3, ← mulVec_mulVec]
  conv_lhs => rw [← e1]
  exact herm_iso (hiso _ ha) _ _

theorem pieri_bessel : HypsG → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (om om' : ι → ℂ) (l : R.H → Wp) (l' : R.H → Wq) (lI : ∀ I, (RI I).H → Wp) (lI' : ∀ I, (RI I).H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ) (FI : κ → Mx k r → (Wq →L[ℂ] Wp)) (sI τ : κ → ℂ), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → (∀ I, (RI I).IsDG ε (muI I) ∧ Formalism.QuantumDeterminants.GapAtLeast ε (muI I) h) → GapOK k r h → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z, ρ g *ᵥ om = om) → (∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z', ρ g *ᵥ om' = om') → (∀ I, IsBeL (RI I) D.z D.π D.μW D.μN (lI I) ∧ IsBeL (RI I) D.z' D.π' D.μW' D.μN (lI' I)) → IsCoef R l l' F s → (∀ I, ((¬ NzOn (RI I) (lI I) ∨ ¬ NzOn (RI I) (lI' I)) ∧ τ I = 0) ∨ (IsCoef (RI I) (lI I) (lI' I) (FI I) (sI I) ∧ sI I ≠ 0 ∧ ∃ κ₀ κ₁ : ℂ, (∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ • l v) ∧ (∀ v ∈ R.sm, lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ • l' v) ∧ τ I = (ep I : ℂ) * κ₁ * star κ₀ * s / sI I)) → ∀ γ ∈ JF.Om k r D.z D.z', Formalism.QuantumDeterminants.herm Γ (ρ γ *ᵥ om') om • B.JF D F γ = ∑ I, τ I • B.JF D (FI I) γ := by
  intro H k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI h Wp _ _ _ _ Wq _ _ _ _ D om om' l l' lI lI' F s FI sI τ
    hR _ hRI hgap hρ hT h1 h2 hBe hF hτ γ hγ
  have hγG : γ ∈ GG k r := hγ.1
  obtain ⟨Ft, st, hFt, hsum, hz, hst⟩ := GlobalTheory.T.tensor_weighted_bessel_sum H.1.2.2.1 k r ι κ ρ Γ d R RI io pr ep ε mu muI Wp Wq om om'
    l l' lI lI' F s hR (fun I => (hRI I).1) hρ hT hF
  obtain ⟨hloc, hfac, hfin, -⟩ := GlobalTheory.T.besselFunction_locality_invariantFactor_finiteSum k r Wp Wq D γ hγG
  have hOO := fun I => GlobalTheory.T.bessel_orbital_integral_integrable_and_eq_smul H k r ε (muI I) h (RI I) Wp Wq D (lI I) (lI' I) (hRI I).1 (hRI I).2 hgap
    (hBe I).1 (hBe I).2
  choose OO hOO using hOO
  rw [← hfac (fun g => Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ om') om) F (fun p hp => coef_inv hρ D h1 h2 hγG p hp),
    (hloc _ (fun g => ∑ I, Ft I g) hsum).1, hfin κ Ft (fun I => (hOO I _ _ (hFt I) γ hγ).1)]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [(hOO I _ _ (hFt I) γ hγ).2]
  rcases hτ I with ⟨hn, h0⟩ | ⟨hc, hs, κ₀, κ₁, a0, a1, ht⟩
  · rw [hz I hn, h0, zero_smul, zero_smul]
  · rw [(hOO I _ _ hc γ hγ).2, hst I κ₀ κ₁ a0 a1, ht, smul_smul, div_mul_cancel₀ _ hs]

end GlobalTheory.BesselPieri
end Gp91
end

