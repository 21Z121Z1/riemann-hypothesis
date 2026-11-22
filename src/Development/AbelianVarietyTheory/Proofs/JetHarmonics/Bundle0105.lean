import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0099
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0087
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0094
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0085
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0078
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0088
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0058
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0016
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValLeOfMemSpan
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0100

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupCayleyMoment
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomentStep

theorem lintegral_le_of_le_sum {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) (f : Ω → ℝ)
    (g : ι → ι → Ω → ℝ) (C : ℝ) (N : ι → ι → ℝ) (hC : 0 ≤ C) (hg0 : ∀ d s x, 0 ≤ g d s x)
    (hm : ∀ d s, AEMeasurable (g d s) ν) (hpt : ∀ᵐ x ∂ν, f x ≤ C * ∑ d, ∑ s, g d s x)
    (hN : ∀ d s, 0 ≤ N d s) (hint : ∀ d s, ∫⁻ x, ENNReal.ofReal (g d s x) ∂ν ≤ ENNReal.ofReal (N d s)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂ν ≤ ENNReal.ofReal (C * ∑ d, ∑ s, N d s) := by
  calc ∫⁻ x, ENNReal.ofReal (f x) ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal C * ∑ d, ∑ s, ENNReal.ofReal (g d s x) ∂ν := by
        refine lintegral_mono_ae (hpt.mono fun x hx => ?_)
        refine (ENNReal.ofReal_le_ofReal hx).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_sum_of_nonneg fun d _ => Finset.sum_nonneg fun s _ => hg0 d s x]
        congr 1
        exact Finset.sum_congr rfl fun d _ => ENNReal.ofReal_sum_of_nonneg fun s _ => hg0 d s x
    _ = ENNReal.ofReal C * ∑ d, ∑ s, ∫⁻ x, ENNReal.ofReal (g d s x) ∂ν := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finset_sum' _ fun d _ => Finset.aemeasurable_fun_sum _ fun s _ => (hm d s).ennreal_ofReal]
        congr 1
        exact Finset.sum_congr rfl fun d _ => lintegral_finset_sum' _ fun s _ => (hm d s).ennreal_ofReal
    _ ≤ ENNReal.ofReal C * ∑ d, ∑ s, ENNReal.ofReal (N d s) := by
        gcongr with d _ s _
        exact hint d s
    _ = _ := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_sum_of_nonneg fun d _ => Finset.sum_nonneg fun s _ => hN d s]
        congr 1
        exact (Finset.sum_congr rfl fun d _ => ENNReal.ofReal_sum_of_nonneg fun s _ => hN d s).symm

theorem norm_sum_smul_sq_le {V ι : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [Fintype ι] (c : ι → ℂ)
    (v : ι → V) : ‖∑ s, c s • v s‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ s, ‖c s‖ ^ 2 * ‖v s‖ ^ 2 := by
  have h1 : ‖∑ s, c s • v s‖ ≤ ∑ s, ‖c s‖ * ‖v s‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun s _ => norm_smul _ _))
  have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun s => ‖c s‖ * ‖v s‖)
  simp only [mul_pow, Finset.card_univ] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem pointwise_le {V ι : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [Fintype ι] (L D A : ℝ) (q : ℕ)
    (a β : ι → ℂ) (Ds : ι → ℝ) (v : V) (y : ι → ι → V) (hD : 0 ≤ D) (hL : ∑ d, ‖a d‖ ^ 2 = L ^ 2)
    (he : ∀ d, a d • v = ∑ s, β s • y d s) (hβ : ∀ s, ‖β s‖ ^ 2 * D ≤ A * Ds s) :
    L ^ (2 * (q + 1)) * (D * ‖v‖ ^ 2) ≤
      ((Fintype.card ι : ℝ) * A) * ∑ d, ∑ s, L ^ (2 * q) * (Ds s * ‖y d s‖ ^ 2) := by
  have hP : 0 ≤ L ^ (2 * q) := by rw [pow_mul]; positivity
  have e1 : L ^ (2 * (q + 1)) * (D * ‖v‖ ^ 2) = ∑ d, L ^ (2 * q) * (D * ‖a d • v‖ ^ 2) := by
    rw [mul_add, pow_add, mul_one, ← hL, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [norm_smul]; ring
  rw [e1, Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [he d]
  calc L ^ (2 * q) * (D * ‖∑ s, β s • y d s‖ ^ 2)
      ≤ L ^ (2 * q) * (D * ((Fintype.card ι : ℝ) * ∑ s, ‖β s‖ ^ 2 * ‖y d s‖ ^ 2)) := by
        gcongr
        exact norm_sum_smul_sq_le β (y d)
    _ = ∑ s, (Fintype.card ι : ℝ) * L ^ (2 * q) * ‖y d s‖ ^ 2 * (‖β s‖ ^ 2 * D) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
    _ ≤ ∑ s, (Fintype.card ι : ℝ) * L ^ (2 * q) * ‖y d s‖ ^ 2 * (A * Ds s) := by
        exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hβ s) (by positivity)
    _ = _ := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring

theorem lOneNorm_sub_single_one_le {n : ℕ} (ν : Fin n → ℤ) (s : Fin n) : n1 (ν - Pi.single s 1) ≤ n1 ν + 1 := by
  have h1 : ∑ i, ((Pi.single s 1 : Fin n → ℤ) i).natAbs = 1 := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  unfold n1
  rw [← h1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_sub_le _ _

theorem param_sub_single {n : ℕ} (lam : Fin n → ℝ) (ν : Fin n → ℤ) (s : Fin n) :
    (fun a => lam a + (((ν - Pi.single s 1) : Fin n → ℤ) a : ℝ)) =
      (fun a => lam a + (ν a : ℝ)) - Pi.single s 1 := by
  funext a
  by_cases h : a = s
  · subst h; simp; ring
  · simp [h]

set_option maxHeartbeats 1000000 in

theorem moment_step : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ ν, n1 ν + 1 ≤ q0 → ∀ (j q : ℕ) (MM : ℝ), j ≤ 4 * (2 * r + k + 1) ^ 2 → 0 ≤ MM → (∀ (s : Fin (2 * r + k + 1)) (y : (R (ν - Pi.single s 1)).smSub), Lev (PI.BesselPeriodGGP.eps48 k r) (E (ν - Pi.single s 1)) (fun a => lam a + (((ν - Pi.single s 1) : Fin (2 * r + k + 1) → ℤ) a : ℝ)) (j + 2) y → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * q) * (dg (ν - Pi.single s 1) * ‖l (ν - Pi.single s 1) ((R (ν - Pi.single s 1)).σ (Matrix.of x) y)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (MM * ‖y‖ ^ 2)) → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * (q + 1)) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) * MM * ‖w‖ ^ 2) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg Q E hS hQ hE ν hν j q MM hj hMM hind w hw
  have hK : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨hNum, hFam, hG, hSide⟩ := id hS
  have hν0 : n1 ν ≤ q0 := by omega
  have hνs : ∀ s, n1 (ν - Pi.single s 1) ≤ q0 := fun s => (lOneNorm_sub_single_one_le ν s).trans hν
  have hDS := hFam ν hν0
  have hDSs := fun s => hFam _ (hνs s)
  obtain ⟨hBe, hdg, -⟩ := hSide ν hν0
  have hBes := fun s => (hSide _ (hνs s)).1
  have hdgs := fun s => (hSide _ (hνs s)).2.1
  obtain ⟨hae, -, hmL, hml⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ (R ν) Wp z π u μW μN μG νq hDS hG
  by_cases hnz : NzOn (R ν) (l ν)
  swap
  · have : ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * (q + 1)) *
        (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = 0 := by
      rw [← lintegral_zero (μ := νq)]
      refine lintegral_congr_ae (hae.mono fun x hx => ?_)
      have : l ν ((R ν).σ (Matrix.of x) w) = 0 := by
        by_contra hne
        exact hnz ⟨_, Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_translate hDS.2 w.2 hx, hne⟩
      simp [this]
    rw [this]
    exact bot_le
  obtain ⟨io, pr, ep, hT⟩ := (GlobalTheory.T.pieri_tensor_decomposition hH k r lam u b bv ga h q0 R hNum hFam ν).2 hν
  have hF := GlobalTheory.isFRep_dualM k r
  have hkap := fun s => GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hH k r _ _ dualM (Formalism.QuantumDeterminants.Hpk k r) 1 (R ν)
    (fun s => R (ν - Pi.single s 1)) io pr ep _ _ _ Wp z π u μW μN μG νq
    (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) (l ν) hDS hDSs hF hT hG
    (fun s hs => (GlobalTheory.FlagFix.fixes_wedge_and_form k r z hG.1 s hs).2) hBe hnz s
    (l (ν - Pi.single s 1)) (hBes s)
  choose κ hκ using fun s => (hkap s).1
  have hdual := fun s => (hkap s).2 (κ s) (hκ s)
  have hA : ∀ s, ‖(ep s : ℂ) * star (κ s)‖ ^ 2 * dg ν ≤
      (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * dg (ν - Pi.single s 1) := by
    intro s
    have h1 := GlobalTheory.T.lowering_scalar_sq_mul_degree_ratio_le hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν io pr ep hT hnz s
      (κ s) (hκ s)
    rw [div_le_iff₀ (hdgs s)] at h1
    have h2 : ‖(ep s : ℂ) * star (κ s)‖ = ‖κ s‖ := by
      rcases hT.ep_sq s with h | h <;> simp [h]
    rwa [h2]
  obtain ⟨io', pr', hAlg, hpr⟩ := GlobalTheory.T.dual_tensor_cayley_weighted hK k r _ _ (R ν) hDS (fun s => R (ν - Pi.single s 1)) _ io pr ep Q
    (E ν) (fun s => E (ν - Pi.single s 1)) hDSs hT hQ (hE ν hν0).1 (fun s => (hE _ (hνs s)).1)
  have hMod := GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ (R ν) hNum.1 hDS Q (E ν) hQ (hE ν hν0).1
  have hMods : ∀ s, IsMod (PI.BesselPeriodGGP.eps48 k r) (E (ν - Pi.single s 1))
      ((fun a => lam a + (ν a : ℝ)) - Pi.single s 1) := fun s => by
    rw [← param_sub_single]
    exact GlobalTheory.T.cayley_endomorphisms_modular hH k r _ _ _ hNum.1 (hDSs s) Q _ hQ (hE _ (hνs s)).1
  have hShape := ((GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum).2 ν hν0).2.1
  have hlev := GlobalTheory.T.unitaryGl_projection_level_sum_sq_le _ _ _ (E ν) (fun s => (R (ν - Pi.single s 1)).smSub) (fun s => E (ν - Pi.single s 1))
    io' pr' _ k j bv w hMod hMods hAlg hShape hj hw
  have hexp : 2 * r + k + 1 + 1 - k = 2 * r + 2 := by omega
  rw [hexp] at hlev
  have hy : ∀ d s, ((pr' s (Pi.single d w) : (R (ν - Pi.single s 1)).smSub) : (R (ν - Pi.single s 1)).H) =
      ∑ c, pr s c (tm (R ν) (fun c => Q d c) w c) := by
    intro d s
    rw [hpr]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [Finset.sum_eq_single d]
    · simp [tm]
    · intro e _ he; simp [he]
    · simp
  have hA0 : 0 ≤ Formalism.QuantumDeterminants.Tz k r z * b ^ 4 := mul_nonneg hG.2.1.le (by positivity)
  have key := lintegral_le_of_le_sum νq
    (fun x => lenA k r z (Matrix.of x) 0 ^ (2 * (q + 1)) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2))
    (fun d s x => lenA k r z (Matrix.of x) 0 ^ (2 * q) * (dg (ν - Pi.single s 1) *
      ‖l (ν - Pi.single s 1) ((R (ν - Pi.single s 1)).σ (Matrix.of x)
        (pr' s (Pi.single d w) : (R (ν - Pi.single s 1)).smSub))‖ ^ 2))
    ((Fintype.card (Fin (2 * r + k + 1)) : ℝ) * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4))
    (fun d s => MM * ‖pr' s (Pi.single d w)‖ ^ 2) (by positivity)
    (fun d s x => mul_nonneg (by rw [pow_mul]; positivity) (mul_nonneg (hdgs s).le (by positivity)))
    (fun d s => ((hmL 0).pow_const _).mul
      ((((GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r _ _ _ Wp z π u μW μN μG νq (hDSs s) hG).2.2.2 _ (hBes s).1 _
        (pr' s (Pi.single d w)).2).norm.aemeasurable.pow_const _).const_mul _))
    (hae.mono fun x hx => by
      refine pointwise_le _ _ _ q
        (fun d => Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (dualM (Matrix.of x) *ᵥ (fun c => Q d c))
          (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)))
        (fun s => (ep s : ℂ) * star (κ s)) _ _ _ hdg.le ?_ (fun d => ?_) hA
      · rw [GlobalTheory.T.sum_norm_sq_herm_translates_orthonormal k r _ dualM _ Q 1 _ hF hQ.2 _ hx]
        exact (GlobalTheory.TensLen.lengths k r z hG.1 hG.2.1 _ hx).2.1
      · simp only [hy]
        exact GlobalTheory.T.tensor_bessel_transfer hK k r _ _ dualM (Formalism.QuantumDeterminants.Hpk k r) 1 (R ν) (fun s => R (ν - Pi.single s 1)) io pr _ _ _
          Wp _ (l ν) (fun s => l (ν - Pi.single s 1)) _ hDS hDSs hT.raw hBe.1.1 hBe.1.2.1 hdual _ w w.2 _ hx)
    (fun d s => by positivity)
    (fun d s => hind s _ (by rw [param_sub_single]; exact (hlev d).1 s))
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hsum : ∑ d, ∑ s, MM * ‖pr' s (Pi.single d w)‖ ^ 2 ≤
      ∑ _d : Fin (2 * r + k + 1), MM * ((6 * bv) ^ (2 * (2 * r + 2)) * ‖w‖ ^ 2) := by
    refine Finset.sum_le_sum fun d _ => ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hlev d).2 hMM
  refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.MomentStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralWeierstrassChartXyUnitSeries
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.ChartXY

variable {q : ℕ} [Fact q.Prime]

def IntLt (n : ℕ) (f : ℂ_[q]⟦X⟧) : Prop := ∀ m < n, ‖coeff m f‖ ≤ 1

lemma IntLt.add {n : ℕ} {f g : ℂ_[q]⟦X⟧} (hf : IntLt n f) (hg : IntLt n g) : IntLt n (f + g) := by
  intro m hm
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf m hm) (hg m hm))

lemma IntLt.mul {n : ℕ} {f g : ℂ_[q]⟦X⟧} (hf : IntLt n f) (hg : IntLt n g) : IntLt n (f * g) := by
  intro m hm
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  rintro ⟨i, j⟩ hij
  replace hij : i + j = m := by simpa using hij
  simp only
  rw [norm_mul]
  exact mul_le_one₀ (hf i (by omega)) (norm_nonneg _) (hg j (by omega))

lemma IntLt.mul_succ {n : ℕ} {f g : ℂ_[q]⟦X⟧} (hf : IntLt n f) (hg : IntLt n g)
    (hf0 : constantCoeff f = 0) (hg0 : constantCoeff g = 0) : IntLt (n + 1) (f * g) := by
  intro m hm
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  rintro ⟨i, j⟩ hij
  replace hij : i + j = m := by simpa using hij
  simp only
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [hf0]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [hg0]
  rw [norm_mul]
  exact mul_le_one₀ (hf i (by omega)) (norm_nonneg _) (hg j (by omega))

lemma intLt_C {n : ℕ} {a : ℂ_[q]} (ha : ‖a‖ ≤ 1) : IntLt n (C a : ℂ_[q]⟦X⟧) := by
  intro m _
  rw [coeff_C]
  split_ifs
  · exact ha
  · simp

lemma bd_iff {f : ℂ_[q]⟦X⟧} : Bd 1 f ↔ ∀ n, IntLt n f :=
  ⟨fun h _ m _ => h m, fun h m => h (m + 1) m (Nat.lt_succ_self m)⟩

lemma bd_w {U W : ℂ_[q]⟦X⟧} {a₁ a₂ a₃ a₄ a₆ : ℂ_[q]} (h₁ : ‖a₁‖ ≤ 1) (h₂ : ‖a₂‖ ≤ 1) (h₃ : ‖a₃‖ ≤ 1)
    (h₄ : ‖a₄‖ ≤ 1) (h₆ : ‖a₆‖ ≤ 1) (hU : Bd 1 U) (hU0 : constantCoeff U = 0) (hW0 : constantCoeff W = 0)
    (h : W = U * U * U + W * (C a₁ * U + C a₂ * U * U + C a₃ * W + C a₄ * U * W + C a₆ * W * W)) : Bd 1 W := by
  rw [bd_iff] at hU ⊢
  intro n
  induction n with
  | zero => intro m hm; omega
  | succ n ih =>
    rw [h]
    refine (((hU _).mul (hU _)).mul (hU _)).add (IntLt.mul_succ ih ?_ hW0 (by simp [hU0, hW0]))
    exact (((((intLt_C h₁).mul (hU _)).add (((intLt_C h₂).mul (hU _)).mul (hU _))).add
      ((intLt_C h₃).mul ih)).add (((intLt_C h₄).mul (hU _)).mul ih)).add (((intLt_C h₆).mul ih).mul ih)

section Hat
variable (ι : ℂ ≃+* ℂ_[q]) {ℓ : ℂ_[q]⟦X⟧} (hℓ : constantCoeff ℓ = 0)
include hℓ

lemma hat_add {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) :
    hat ι ℓ (fun z => F z + G z) = hat ι ℓ F + hat ι ℓ G :=
  ((GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hℓ).1 F G hF hG).1

lemma hat_mul {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) :
    hat ι ℓ (fun z => F z * G z) = hat ι ℓ F * hat ι ℓ G :=
  ((GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hℓ).1 F G hF hG).2.1

lemma hat_congr {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0)
    (h : ∀ᶠ z in 𝓝[≠] (0 : ℂ), F z = G z) : hat ι ℓ F = hat ι ℓ G :=
  ((GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hℓ).1 F G hF hG).2.2.1 h

lemma hat_const (c : ℂ) : hat ι ℓ (fun _ => c) = C (ι c) :=
  (GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hℓ).2.1 c

lemma hat_pow {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (n : ℕ) :
    hat ι ℓ (fun z => F z ^ n) = hat ι ℓ F ^ n := by
  induction n with
  | zero => simpa using hat_const ι hℓ 1
  | succ n ih =>
    simp only [pow_succ]
    rw [hat_mul ι hℓ (F := fun z => F z ^ n) (hF.fun_pow n) hF, ih]

lemma hat_sum (s : Finset ℕ) {F : ℕ → ℂ → ℂ} (hF : ∀ i, AnalyticAt ℂ (F i) 0) :
    hat ι ℓ (fun z => ∑ i ∈ s, F i z) = ∑ i ∈ s, hat ι ℓ (F i) := by
  induction s using Finset.induction_on with
  | empty => simpa using hat_const ι hℓ 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [hat_add ι hℓ (G := fun z => ∑ i ∈ s, F i z) (hF a)
      (Finset.analyticAt_fun_sum s fun i _ => hF i), ih]

end Hat

noncomputable def homog (D : Polynomial ℂ) (j : ℕ) (u w : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (j + 1), D.coeff i * (u z ^ i * w z ^ (j - i))

lemma homog_analytic (D : Polynomial ℂ) (j : ℕ) {u w : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hw : AnalyticAt ℂ w 0) :
    AnalyticAt ℂ (homog D j u w) 0 := by
  unfold homog
  exact Finset.analyticAt_fun_sum _ fun i _ => by fun_prop

lemma homog_eq {D : Polynomial ℂ} {j : ℕ} (hD : D.natDegree ≤ j) {u w : ℂ → ℂ} {z x : ℂ} (h : x * w z = u z) :
    homog D j u w z = D.eval x * w z ^ j := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hD), Finset.sum_mul, homog]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  rw [← h, Nat.add_sub_cancel_left]
  ring

lemma hat_homog (ι : ℂ ≃+* ℂ_[q]) {ℓ : ℂ_[q]⟦X⟧} (hℓ : constantCoeff ℓ = 0) (D : Polynomial ℂ) (j : ℕ)
    {u w : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hw : AnalyticAt ℂ w 0) {v ys : ℂ_[q]⟦X⟧}
    (hU : hat ι ℓ u = X * v) (hW : hat ι ℓ w * ys = X ^ 3) :
    hat ι ℓ (homog D j u w) * ys ^ j =
      X ^ j * ∑ i ∈ Finset.range (j + 1), C (ι (D.coeff i)) * X ^ (2 * (j - i)) * (v * ys) ^ i := by
  have := hat_sum ι hℓ (Finset.range (j + 1)) (F := fun i z => D.coeff i * (u z ^ i * w z ^ (j - i)))
    (fun i => by fun_prop)
  unfold homog
  rw [this, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  rw [hat_mul ι hℓ (F := fun _ => D.coeff i) (G := fun z => u z ^ i * w z ^ (i + m - i)) (by fun_prop) (by fun_prop),
    hat_mul ι hℓ (F := fun z => u z ^ i) (G := fun z => w z ^ (i + m - i)) (by fun_prop) (by fun_prop),
    hat_pow ι hℓ hu, hat_pow ι hℓ hw, hat_const ι hℓ, hU, Nat.add_sub_cancel_left]
  calc _ = C (ι (D.coeff i)) * X ^ i * (v * ys) ^ i * (hat ι ℓ w * ys) ^ m := by ring
    _ = _ := by rw [hW]; ring

theorem chart_xy : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧), M.Chart ℓ → coeff 1 ℓ ≠ 0 ∧ ∃ v xs ys : ℂ_[q]⟦X⟧, Bd 1 v ∧ Bd 1 xs ∧ Bd 1 ys ∧ ‖constantCoeff v‖ = 1 ∧ ‖constantCoeff xs‖ = 1 ∧ ‖constantCoeff ys‖ = 1 ∧ hat M.ι ℓ M.u = X * v ∧ hat M.ι ℓ M.w * ys = -X ^ 3 ∧ xs = -v * ys ∧ ∀ (F : ℂ → ℂ) (A B : Polynomial ℂ) (k : ℕ), AnalyticAt ℂ F 0 → A.natDegree ≤ k → B.natDegree ≤ k → ∀ G : ℂ → ℂ, AnalyticAt ℂ G 0 → ∀ (D : Polynomial ℂ) (j : ℕ), D.natDegree ≤ j → (∀ᶠ z in 𝓝[≠] (0 : ℂ), F z * D.eval (M.x z) = G z * (A.eval (M.x z) + B.eval (M.x z) * M.y z)) → hat M.ι ℓ F * X ^ (2 * k + 3) * (∑ i ∈ Finset.range (j + 1), C (M.ι (D.coeff i)) * X ^ (2 * (j - i)) * xs ^ i) = hat M.ι ℓ G * X ^ (2 * j) * ∑ i ∈ Finset.range (k + 1), (C (M.ι (A.coeff i)) * X ^ (2 * (k - i) + 3) * xs ^ i + C (M.ι (B.coeff i)) * X ^ (2 * (k - i)) * xs ^ i * ys) := by
  rintro q _ M ℓ ⟨hok, hℓ, hU, hU1⟩
  obtain ⟨-, -, -, -, hu0, hw0, -, -, hs⟩ := GlobalTheory.MomOne.uw_elliptic_flow q M hok
  obtain ⟨hu, hw, -, -, hxy, heq⟩ := hs 0 (Or.inl (zero_mem _))
  obtain ⟨-, h₁, h₂, h₃, h₄, h₆, -⟩ := hok
  obtain ⟨-, -, -, hc0, hder, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι ℓ hℓ
  obtain ⟨hring, -, hinv, -⟩ := GlobalTheory.MomOne.sup_norm_laws q
  have hU0 : constantCoeff (hat M.ι ℓ M.u) = 0 := by rw [hc0, hu0, map_zero]
  have hW0 : constantCoeff (hat M.ι ℓ M.w) = 0 := by rw [hc0, hw0, map_zero]
  refine ⟨?_, ?_⟩
  · intro h0
    have := congrArg (coeff 0) (hder M.u hu)
    rw [coeff_derivative, coeff_zero_eq_constantCoeff_apply, map_mul, ← coeff_zero_eq_constantCoeff_apply,
      coeff_derivative] at this
    simp only [zero_add, h0, Nat.cast_zero, mul_one, zero_mul] at this
    rw [this] at hU1
    simp at hU1
  obtain ⟨v, hv⟩ := X_dvd_iff.mpr hU0
  have hvc : ∀ n, coeff n v = coeff (n + 1) (hat M.ι ℓ M.u) := fun n => by rw [hv, coeff_succ_X_mul]
  have hvB : Bd 1 v := fun n => by rw [hvc]; exact hU _
  have hv0 : ‖constantCoeff v‖ = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hvc]; exact hU1
  have hv0' : constantCoeff v ≠ 0 := by
    intro h; rw [h] at hv0; simp at hv0
  have hvi : v * v⁻¹ = 1 := PowerSeries.mul_inv_cancel v hv0'
  have hviB : Bd 1 v⁻¹ := hinv v _ hvB hv0 hvi
  have hWeq : hat M.ι ℓ M.w = hat M.ι ℓ M.u * hat M.ι ℓ M.u * hat M.ι ℓ M.u + hat M.ι ℓ M.w *
      (C M.W.a₁ * hat M.ι ℓ M.u + C M.W.a₂ * hat M.ι ℓ M.u * hat M.ι ℓ M.u + C M.W.a₃ * hat M.ι ℓ M.w
        + C M.W.a₄ * hat M.ι ℓ M.u * hat M.ι ℓ M.w + C M.W.a₆ * hat M.ι ℓ M.w * hat M.ι ℓ M.w) := by
    have hc : ∀ a : ℂ_[q], C a = hat M.ι ℓ (fun _ => M.ι.symm a) := fun a => by
      rw [hat_const M.ι hℓ, RingEquiv.apply_symm_apply]
    simp only [hc]
    simp (disch := fun_prop) only [← hat_mul M.ι hℓ, ← hat_add M.ι hℓ]
    refine hat_congr M.ι hℓ hw (by fun_prop) ?_
    filter_upwards [nhdsWithin_le_nhds heq] with z hz
    linear_combination hz.1
  have hWB : Bd 1 (hat M.ι ℓ M.w) := bd_w h₁ h₂ h₃ h₄ h₆ hU hU0 hW0 hWeq
  set Q := C M.W.a₁ * hat M.ι ℓ M.u + C M.W.a₂ * hat M.ι ℓ M.u * hat M.ι ℓ M.u + C M.W.a₃ * hat M.ι ℓ M.w
        + C M.W.a₄ * hat M.ι ℓ M.u * hat M.ι ℓ M.w + C M.W.a₆ * hat M.ι ℓ M.w * hat M.ι ℓ M.w with hQ
  have hQ0 : constantCoeff Q = 0 := by simp [hQ, hU0, hW0]
  have hQB : Bd 1 Q := by
    rw [bd_iff] at hU hWB ⊢
    intro n
    exact (((((intLt_C h₁).mul (hU _)).add (((intLt_C h₂).mul (hU _)).mul (hU _))).add
      ((intLt_C h₃).mul (hWB _))).add (((intLt_C h₄).mul (hU _)).mul (hWB _))).add
      (((intLt_C h₆).mul (hWB _)).mul (hWB _))
  set ys := (C 1 + C (-1) * Q) * (v⁻¹ * v⁻¹ * v⁻¹) with hys
  have hysB : Bd 1 ys := by
    rw [bd_iff] at hQB hviB ⊢
    intro n
    exact ((intLt_C (by simp)).add ((intLt_C (by simp)).mul (hQB _))).mul
      (((hviB _).mul (hviB _)).mul (hviB _))
  have hys0 : ‖constantCoeff ys‖ = 1 := by
    simp [hys, hQ0, hv0]
  have hWys : hat M.ι ℓ M.w * ys = X ^ 3 := by
    have h1 : hat M.ι ℓ M.w * (1 - Q) = (X * v) ^ 3 := by
      rw [← hv]; linear_combination hWeq
    calc hat M.ι ℓ M.w * ys = hat M.ι ℓ M.w * (1 - Q) * v⁻¹ ^ 3 := by
          rw [hys, map_neg, map_one]; ring
      _ = X ^ 3 * (v * v⁻¹) ^ 3 := by rw [h1]; ring
      _ = X ^ 3 := by rw [hvi]; ring
  refine ⟨v, v * ys, -ys, hvB, ?_, fun n => by simpa using hysB n, hv0, ?_, by simpa using hys0, hv,
    by rw [mul_neg, hWys], by ring, ?_⟩
  · rw [bd_iff] at hvB hysB ⊢
    exact fun n => (hvB n).mul (hysB n)
  · rw [map_mul, norm_mul, hv0, hys0, mul_one]
  intro F A B k hF hA hB G hG D j hD h
  clear_value ys Q
  clear hs heq hder hring hinv
  have hAa := homog_analytic A k hu hw
  have hBa := homog_analytic B k hu hw
  have hDa := homog_analytic D j hu hw
  have key : hat M.ι ℓ F * hat M.ι ℓ (homog D j M.u M.w) * hat M.ι ℓ M.w ^ (k + 1)
      + hat M.ι ℓ G * hat M.ι ℓ M.w ^ j * hat M.ι ℓ (homog B k M.u M.w)
      = hat M.ι ℓ G * hat M.ι ℓ M.w ^ j * (hat M.ι ℓ (homog A k M.u M.w) * hat M.ι ℓ M.w) := by
    rw [← hat_pow M.ι hℓ hw, ← hat_pow M.ι hℓ hw]
    simp (disch := fun_prop) only [← hat_mul M.ι hℓ, ← hat_add M.ι hℓ]
    refine hat_congr M.ι hℓ (by fun_prop) (by fun_prop) ?_
    filter_upwards [h, hxy] with z hz ⟨_, _, hx, hy⟩
    rw [homog_eq hA hx, homog_eq hB hx, homog_eq hD hx]
    linear_combination M.w z ^ (j + k + 1) * hz
      + G z * M.w z ^ j * (B.eval (M.x z)) * M.w z ^ k * hy
  have eA := hat_homog M.ι hℓ A k hu hw hv hWys
  have eB := hat_homog M.ι hℓ B k hu hw hv hWys
  have eD := hat_homog M.ι hℓ D j hu hw hv hWys
  have hsum : ∑ i ∈ Finset.range (k + 1), (C (M.ι (A.coeff i)) * X ^ (2 * (k - i) + 3) * (v * ys) ^ i
      + C (M.ι (B.coeff i)) * X ^ (2 * (k - i)) * (v * ys) ^ i * -ys) =
      (∑ i ∈ Finset.range (k + 1), C (M.ι (A.coeff i)) * X ^ (2 * (k - i)) * (v * ys) ^ i) * X ^ 3
      - (∑ i ∈ Finset.range (k + 1), C (M.ι (B.coeff i)) * X ^ (2 * (k - i)) * (v * ys) ^ i) * ys := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  set SA := ∑ i ∈ Finset.range (k + 1), C (M.ι (A.coeff i)) * X ^ (2 * (k - i)) * (v * ys) ^ i
  set SB := ∑ i ∈ Finset.range (k + 1), C (M.ι (B.coeff i)) * X ^ (2 * (k - i)) * (v * ys) ^ i
  set SD := ∑ i ∈ Finset.range (j + 1), C (M.ι (D.coeff i)) * X ^ (2 * (j - i)) * (v * ys) ^ i
  have hX : (X : ℂ_[q]⟦X⟧) ^ (j + k) ≠ 0 := pow_ne_zero _ X_ne_zero
  apply mul_left_cancel₀ hX
  have key2 : hat M.ι ℓ F * (hat M.ι ℓ (homog D j M.u M.w) * ys ^ j) * (hat M.ι ℓ M.w * ys) ^ (k + 1)
      + hat M.ι ℓ G * (hat M.ι ℓ M.w * ys) ^ j * (hat M.ι ℓ (homog B k M.u M.w) * ys ^ k) * ys
      = hat M.ι ℓ G * (hat M.ι ℓ M.w * ys) ^ j * ((hat M.ι ℓ (homog A k M.u M.w) * ys ^ k)
        * (hat M.ι ℓ M.w * ys)) := by
    linear_combination ys ^ (j + k + 1) * key
  rw [eA, eB, eD, hWys] at key2
  linear_combination key2

end GlobalTheory.MomOne.ChartXY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumProdConstMul
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory GlobalTheory.FamGerm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DepthBound

theorem sum_prod_const_mul {k Λ : Type} [CommRing k] [Fintype Λ] {n : ℕ} (S : Finset (Fin n))
    (P : MvPolynomial (Λ × Fin n) k) (mu mu' : Fin n → (Λ →₀ ℕ) → k) (c : Fin n → k)
    (h : ∀ b ∈ S, ∀ mo, mu b mo = c b * mu' b mo) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b ∈ S, mu b (colM mo b) =
      (∏ b ∈ S, c b) * ∑ mo ∈ P.support, P.coeff mo * ∏ b ∈ S, mu' b (colM mo b) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun mo _ => ?_
  rw [Finset.prod_congr rfl fun b hb => h b hb _, Finset.prod_mul_distrib]
  ring

end GlobalTheory.DepthBound
end
end

