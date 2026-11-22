import Formalism.SharpRestriction.CuspSpanNormBounds.RatioInvLeFrameFactor
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0013
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.NatSmulMulEq
import Formalism.FlagUnipotentLattices.Bundle0010
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0012
import Formalism.SharpRestriction.CuspSpanNormBounds.ExpansionFromLemmaB
import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0005

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BlockExponentKappaIdentity
section
open MeasureTheory Matrix Finset

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

section Weight

variable {k r : ℕ} {κ τ : ℝ}

def Wbig (k r : ℕ) (κ τ : ℝ) : ℝ := ∏ a : Fin (r + 1), tF r κ τ a ^ (4 * (2 * (r - a.val) + k - 1))

def frameBlockSum (g : ℕ → ℕ → ℕ) : ℕ → List (ℂ × ℕ) → ℕ
  | _, [] => 0
  | acc, (_, s) :: bs => g acc s + frameBlockSum g (acc + s) bs

def frGN (k r acc s : ℕ) : ℕ := 2 * s * (Ml k r (acc + s) + s - 3)

def frGE (r acc s : ℕ) : ℕ := 2 * (r + 1 - (acc + s)) + (s - 1)

def frTri (d : ℕ) : ℕ := ∑ j ∈ range d, (d - j)

theorem ptWeightFrom_scale (hκ : 0 < κ) (hτ : 0 < τ) (T T' : ℝ) (acc : ℕ) (bs : List (ℂ × ℕ)) :
    ptWeightFrom k r (τ ^ 2 * T) (τ ^ 2 * T') acc (scaleBlocks κ τ r acc bs) =
      τ ^ frameBlockSum (fun a s => 2 * frGN k r a s) acc bs *
        κ ^ frameBlockSum (fun a s => frGE r a s * frGN k r a s) acc bs * ptWeightFrom k r T T' acc bs := by
  induction bs generalizing acc with
  | nil => simp [ptWeightFrom, scaleBlocks, frameBlockSum]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [scaleBlocks, ptWeightFrom, frameBlockSum]
    rw [ih (acc + s)]
    by_cases h : s = 1 ∧ acc + 1 = r + 1
    · rw [if_pos h, if_pos h]
      obtain ⟨rfl, h2⟩ := h
      have e1 : 2 * (r + 1 - (acc + 1)) + (1 - 1) = 0 := by omega
      have e2 : frGE r acc 1 = 0 := by unfold frGE; omega
      have e3 : 2 * frGN k r acc 1 = 4 * (k - 1) := by unfold frGN Ml; omega
      have hbase : Complex.normSq (((τ ^ 2 * κ ^ 0 : ℝ) : ℂ) * t) - τ ^ 2 * T * (τ ^ 2 * T') =
          τ ^ 4 * (Complex.normSq t - T * T') := by
        rw [Complex.normSq_mul, Complex.normSq_ofReal]; ring
      rw [e1, hbase, e2, e3, mul_pow]
      ring
    · rw [if_neg h, if_neg h, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      unfold frGE frGN
      ring

theorem sum_pos_blocks (f : ℕ → ℕ → ℕ) (acc : ℕ) (bs : List (ℂ × ℕ)) :
    ∑ p ∈ range (bs.map Prod.snd).sum, f (acc + p) (p - frStart bs p) =
      frameBlockSum (fun a s => ∑ i ∈ range s, f (a + i) i) acc bs := by
  induction bs generalizing acc with
  | nil => simp [frameBlockSum]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_range_add, frameBlockSum, ← ih (acc + s)]
    congr 1
    · refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : p < s := Finset.mem_range.mp hp
      simp only [frStart, if_pos hp', Nat.sub_zero]
    · refine Finset.sum_congr rfl fun p _ => ?_
      simp only [frStart]
      rw [if_neg (show ¬ (s + p < s) by omega), show s + p - s = p by omega,
        show acc + (s + p) = acc + s + p by omega,
        show s + p - (s + frStart bs p) = p - frStart bs p by omega]

theorem sum_rootPat_diff (γ : Point ℂ (r + 1)) :
    ∑ p ∈ rootPat γ, (p.2.val - p.1.val) = frameBlockSum (fun a s => ∑ i ∈ range s, frTri i) 0 γ.1 := by
  have h1 := sum_rootPat (fun a b => b - a) γ
  have h2 := sum_pos_blocks (fun _ d => frTri d) 0 γ.1
  rw [γ.2.2] at h2
  rw [h1, ← h2]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_Ico_eq_sum_range]
  unfold frTri
  refine Finset.sum_congr rfl fun j hj => ?_
  have := Finset.mem_range.mp hj
  have := frStart_le γ.1 b
  omega

theorem Wbig_eq : Wbig k r κ τ = τ ^ (∑ a ∈ range (r + 1), 4 * (2 * (r - a) + k - 1)) *
    κ ^ (∑ a ∈ range (r + 1), (r - a) * (4 * (2 * (r - a) + k - 1))) := by
  unfold Wbig
  rw [Fin.prod_univ_eq_prod_range (fun a => tF r κ τ a ^ (4 * (2 * (r - a) + k - 1)))]
  simp_rw [tF, mul_pow, ← pow_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]

theorem alphaPt_sq_mul (hκ : 0 < κ) (hτ : 0 < τ) (γ : Point ℂ (r + 1)) :
    alphaPt κ τ γ ^ 2 * κ ^ (4 * ∑ p ∈ rootPat γ, (p.2.val - p.1.val)) = κ ^ (2 * (rootPat γ).card) := by
  have h1 : ∀ p ∈ rootPat γ,
      (tF r κ τ p.2.val / tF r κ τ p.1.val) ^ 2 * κ ^ (2 * (p.2.val - p.1.val)) = 1 := by
    intro p hp
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2.1
    have hlt' : p.1.val < p.2.val := hlt
    have hle : p.2.val ≤ r := Nat.lt_succ_iff.mp p.2.isLt
    have e : tF r κ τ p.1.val = tF r κ τ p.2.val * κ ^ (p.2.val - p.1.val) := by
      unfold tF; rw [mul_assoc, ← pow_add]; congr 2; omega
    have h2 := tF_pos (r := r) hκ hτ p.2.val
    have h3 : 0 < κ ^ (p.2.val - p.1.val) := pow_pos hκ _
    have h4 : tF r κ τ p.2.val / (tF r κ τ p.2.val * κ ^ (p.2.val - p.1.val)) * κ ^ (p.2.val - p.1.val) = 1 := by
      field_simp
    rw [e, pow_mul', ← mul_pow, h4, one_pow]
  set P := ∏ p ∈ rootPat γ, (tF r κ τ p.2.val / tF r κ τ p.1.val) ^ 2 with hP
  set S := ∑ p ∈ rootPat γ, (p.2.val - p.1.val) with hS
  have hPS : P * κ ^ (2 * S) = 1 := by
    rw [hS, Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum, hP, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one h1
  unfold alphaPt
  rw [← hP, show (κ ^ (rootPat γ).card * P) ^ 2 * κ ^ (4 * S) =
    κ ^ (2 * (rootPat γ).card) * (P * κ ^ (2 * S)) ^ 2 by ring, hPS]
  ring

theorem frTri_succ (d : ℕ) : frTri (d + 1) = frTri d + (d + 1) := by
  unfold frTri
  rw [Finset.sum_range_succ']
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by omega

theorem two_mul_frTri (d : ℕ) : 2 * frTri d = d * (d + 1) := by
  induction d with
  | zero => simp [frTri]
  | succ n ih => rw [frTri_succ, mul_add, ih]; ring

theorem block_exponent_tau_identity (m k' s' : ℕ) :
    2 * (2 * (s' + 1) * (2 * m + k' + s')) = ∑ i ∈ range (s' + 1), 4 * (2 * (m + i) + k') := by
  induction s' with
  | zero => simp only [zero_add, add_zero, Finset.sum_range_one]; ring
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; ring

theorem block_exponent_kappa_identity (m k' s' : ℕ) :
    (2 * m + s') * (2 * (s' + 1) * (2 * m + k' + s')) + 4 * ∑ i ∈ range (s' + 1), frTri i =
      ∑ i ∈ range (s' + 1), (m + i) * (4 * (2 * (m + i) + k')) := by
  induction s' with
  | zero =>
    simp only [zero_add, add_zero, Finset.sum_range_one, frTri, Finset.range_zero, Finset.sum_empty, mul_zero]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ frTri (n + 1),
      Finset.sum_range_succ (fun i => (m + i) * (4 * (2 * (m + i) + k'))) (n + 1), ← ih]
    have h := two_mul_frTri (n + 1)
    nlinarith [h]

theorem blk_tau (hk : 1 ≤ k) (a s : ℕ) (h : a + s ≤ r + 1) :
    2 * frGN k r a s = ∑ i ∈ range s, 4 * (2 * (r - (a + i)) + k - 1) := by
  rcases s with _ | s'
  · simp [frGN]
  obtain ⟨m, hm⟩ : ∃ m, m = r + 1 - (a + (s' + 1)) := ⟨_, rfl⟩
  have hN : frGN k r a (s' + 1) = 2 * (s' + 1) * (2 * m + (k - 1) + s') := by
    unfold frGN Ml; congr 1; omega
  rw [hN, block_exponent_tau_identity m (k - 1) s',
    ← Finset.sum_range_reflect (fun i => 4 * (2 * (r - (a + i)) + k - 1)) (s' + 1)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.mp hi
  try dsimp only
  omega

theorem blk_kappa (hk : 1 ≤ k) (a s : ℕ) (h : a + s ≤ r + 1) :
    frGE r a s * frGN k r a s + 4 * ∑ i ∈ range s, frTri i =
      ∑ i ∈ range s, (r - (a + i)) * (4 * (2 * (r - (a + i)) + k - 1)) := by
  rcases s with _ | s'
  · simp [frGN]
  obtain ⟨m, hm⟩ : ∃ m, m = r + 1 - (a + (s' + 1)) := ⟨_, rfl⟩
  have hN : frGN k r a (s' + 1) = 2 * (s' + 1) * (2 * m + (k - 1) + s') := by
    unfold frGN Ml; congr 1; omega
  have hE : frGE r a (s' + 1) = 2 * m + s' := by unfold frGE; omega
  rw [hN, hE, block_exponent_kappa_identity m (k - 1) s',
    ← Finset.sum_range_reflect (fun i => (r - (a + i)) * (4 * (2 * (r - (a + i)) + k - 1))) (s' + 1)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.mp hi
  try dsimp only
  have e1 : r - (a + (s' + 1 - 1 - i)) = m + i := by omega
  have e2 : 2 * (m + i) + k - 1 = 2 * (m + i) + (k - 1) := by omega
  rw [e1, e2]

theorem frame_block_sum_congr {g₁ g₂ : ℕ → ℕ → ℕ} {R : ℕ} (h : ∀ a s, a + s ≤ R → g₁ a s = g₂ a s) (acc : ℕ)
    (bs : List (ℂ × ℕ)) (hb : acc + (bs.map Prod.snd).sum ≤ R) : frameBlockSum g₁ acc bs = frameBlockSum g₂ acc bs := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at hb
    simp only [frameBlockSum]
    rw [h acc s (by omega), ih (acc + s) (by omega)]

theorem frame_block_sum_add (g₁ g₂ : ℕ → ℕ → ℕ) (acc : ℕ) (bs : List (ℂ × ℕ)) :
    frameBlockSum (fun a s => g₁ a s + g₂ a s) acc bs = frameBlockSum g₁ acc bs + frameBlockSum g₂ acc bs := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [frameBlockSum]
    rw [ih (acc + s)]; ring

theorem frame_block_sum_mul (c : ℕ) (g : ℕ → ℕ → ℕ) (acc : ℕ) (bs : List (ℂ × ℕ)) :
    frameBlockSum (fun a s => c * g a s) acc bs = c * frameBlockSum g acc bs := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [frameBlockSum]
    rw [ih (acc + s)]; ring

theorem ptWeight_ptTr (hk : 1 ≤ k) (hκ : 0 < κ) (hτ : 0 < τ) (T T' : ℝ) (γ : Point ℂ (r + 1)) :
    ptWeight k r (τ ^ 2 * T) (τ ^ 2 * T') (ptTr κ τ hκ hτ γ) * κ ^ (2 * (rootPat γ).card) =
      Wbig k r κ τ * alphaPt κ τ γ ^ 2 * ptWeight k r T T' γ := by
  have hsum : 0 + (γ.1.map Prod.snd).sum ≤ r + 1 := by rw [γ.2.2]; omega
  have hU := sum_pos_blocks (fun p _ => 4 * (2 * (r - p) + k - 1)) 0 γ.1
  have hV := sum_pos_blocks (fun p _ => (r - p) * (4 * (2 * (r - p) + k - 1))) 0 γ.1
  rw [γ.2.2] at hU hV
  simp only [zero_add] at hU hV
  have hA : frameBlockSum (fun a s => 2 * frGN k r a s) 0 γ.1 = ∑ a ∈ range (r + 1), 4 * (2 * (r - a) + k - 1) := by
    rw [hU]
    refine frame_block_sum_congr ?_ 0 γ.1 hsum
    intro a s h; exact blk_tau hk a s h
  have hB : frameBlockSum (fun a s => frGE r a s * frGN k r a s) 0 γ.1 + 4 * ∑ p ∈ rootPat γ, (p.2.val - p.1.val) =
      ∑ a ∈ range (r + 1), (r - a) * (4 * (2 * (r - a) + k - 1)) := by
    rw [hV, sum_rootPat_diff, ← frame_block_sum_mul, ← frame_block_sum_add]
    refine frame_block_sum_congr ?_ 0 γ.1 hsum
    intro a s h; exact blk_kappa hk a s h
  have hα := alphaPt_sq_mul hκ hτ γ
  unfold ptWeight
  rw [ptTr_val, ptWeightFrom_scale hκ hτ, Wbig_eq, hA, ← hB, ← hα, pow_add]
  ring

end Weight

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BridgeVolRatio
section
noncomputable section

namespace Formalism.MainNotions.BridgeVolRatio

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.MainNotions.BridgeDeepQ
open scoped ENNReal TensorProduct

def GaugeVolumeBoundVar (X : CData) (C0 : ℝ) : Prop :=
  X.I.vol X.μf X.fund / ((X.μf X.I.Kset).toReal * X.I.gaugeU) ≤ cn_Y X ^ (C0 * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ))

theorem one_le_rd (I : AutInst) : 1 ≤ I.rd := by
  unfold AutInst.rd
  have hd : (1 : ℝ) ≤ |(NumberField.discr I.E : ℝ)| := by
    have h0 : NumberField.discr I.E ≠ 0 := NumberField.discr_ne_zero I.E
    have : (1 : ℤ) ≤ |NumberField.discr I.E| := Int.one_le_abs h0
    exact_mod_cast this
  exact Real.one_le_rpow hd (by positivity)

theorem one_le_f (I : AutInst) : 1 ≤ I.f := Module.finrank_pos

theorem kg_pos_fin (X : CData) (hH : X.μf.IsHaarMeasure) {g : ℕ} (hg : 1 ≤ g) :
    0 < X.μf (X.I.Kg g) ∧ X.μf X.I.Kset < ∞ := by
  have hopen : IsOpen (X.I.Kg g) := X.I.topf_open g hg
  have hne : (X.I.Kg g).Nonempty := ⟨1, by
    refine ⟨?_, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
    · show ((1 : X.I.Gf) : GL (Fin X.I.n) (X.I.E ⊗[X.I.F] Af X.I.F)) ∈ Formalism.UG.stabGL X.I.Lf
      rw [OneMemClass.coe_one]
      exact (Formalism.UG.stabGL X.I.Lf).one_mem
    · simp [AutInst.fmat]⟩
  refine ⟨hopen.measure_pos X.μf hne, ?_⟩
  exact (PI.WAU.Cpt.isCompact_Kset X.I).measure_lt_top

theorem kg_sub (I : AutInst) (g : ℕ) : I.Kg g ⊆ I.Kset := fun _ hx => hx.1

theorem vol_ratio_of_gauge_volume (hGD : ∀ (n : ℕ) (ε : Fin n → Bool), Gauge.GaugeDens ε) {C0 : ℝ} (X : CData) {n₀ : ℕ} {A : ℝ}
    (hn₀ : 1 ≤ n₀) (hX : X.HypB n₀ A) (hV : GaugeVolumeBoundVar X C0) : VolRatio X (C0 + 2) := by
  obtain ⟨hset, hcount, -⟩ := hX
  have hH : X.μf.IsHaarMeasure := hcount.2.2.2.1
  have hn : 1 ≤ X.I.n := le_trans hn₀ hset.1
  have hb : (2 : ℝ) ≤ X.b := hset.2.2.1
  have hg : 1 ≤ X.g := hset.2.2.2.2.2.2.2.1
  obtain ⟨hpos, hfin⟩ := kg_pos_fin X hH hg
  have hKg_fin : X.μf (X.I.Kg X.g) < ∞ := lt_of_le_of_lt (measure_mono (kg_sub X.I X.g)) hfin
  have hK_pos : 0 < X.μf X.I.Kset := lt_of_lt_of_le hpos (measure_mono (kg_sub X.I X.g))
  set μK := (X.μf X.I.Kset).toReal with hμK
  set μKg := (X.μf (X.I.Kg X.g)).toReal with hμKg
  have hμK0 : 0 < μK := ENNReal.toReal_pos hK_pos.ne' hfin.ne
  have hμKg0 : 0 < μKg := ENNReal.toReal_pos hpos.ne' hKg_fin.ne
  have hU : 0 < X.I.gaugeU := Finset.prod_pos fun v _ => (hGD _ (X.I.ε v)).2

  have hidx : μK ≤ ((X.g : ℝ) ^ (2 * X.I.n ^ 2 * X.I.f)) * μKg := by
    have h := Formalism.MainNotions.BridgeLevelGen.levelIdx X.I X.μf hg
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hKg_fin.ne) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h2
    simpa [hμK, hμKg] using h2
  have hvolK : (μKg / μK)⁻¹ ≤ (X.g : ℝ) ^ (2 * X.I.n ^ 2 * X.I.f) := by
    rw [inv_div, div_le_iff₀ hμKg0]; exact hidx
  have hlev := Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts.volLevel C0 X.I.n X.I.f X.I.rd (X.g : ℝ) X.b
    (X.I.vol X.μf X.fund / (μK * X.I.gaugeU)) (μKg / μK) hn (one_le_f X.I) (one_le_rd X.I)
    (by exact_mod_cast hg) hb (div_pos hμKg0 hμK0) hV hvolK
  refine ⟨mul_pos hμKg0 hU, ?_⟩
  have e : X.I.vol X.μf X.fund / X.I.volKg X.μf X.g =
      X.I.vol X.μf X.fund / (μK * X.I.gaugeU) / (μKg / μK) := by
    unfold AutInst.volKg
    rw [← hμKg]
    field_simp
  rw [e]
  exact hlev

end Formalism.MainNotions.BridgeVolRatio

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.FrameFactorGe
section
open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

variable {r : ℕ} {κ τ : ℝ}

theorem frame_factor_ge (hκ : 0 < κ) (hτ : 0 < τ) (A A₁ : (Fin r → ℂ) × ℂ → ENNReal) (K F : ℝ) (hK : 0 < K)
    (hF : 0 ≤ F)
    (h1 : ∀ p, A₁ (sBig r κ τ p) ≤ ENNReal.ofReal (K * F) * A p)
    (h2 : ∀ p, ENNReal.ofReal K * A p ≤ ENNReal.ofReal F * A₁ (sBig r κ τ p))
    (hint : ∫⁻ p, A₁ p = ENNReal.ofReal K * ∫⁻ p, A p) (h0 : ∫⁻ p, A p ≠ 0) (htop : ∫⁻ p, A p ≠ ⊤) :
    jacBig r κ τ ≤ F ∧ 1 ≤ jacBig r κ τ * F := by
  have hJ := jacBig_pos (r := r) hκ hτ
  have hS := lintegral_sBig (r := r) hκ hτ A₁
  set I := ∫⁻ p, A p
  set I₁ := ∫⁻ p, A₁ (sBig r κ τ p)
  have e : ENNReal.ofReal (jacBig r κ τ) * I₁ = ENNReal.ofReal K * I := by rw [← hS, hint]
  have a1 : I₁ ≤ ENNReal.ofReal (K * F) * I := by
    calc I₁ ≤ ∫⁻ p, ENNReal.ofReal (K * F) * A p := lintegral_mono h1
      _ = ENNReal.ofReal (K * F) * I := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have a2 : ENNReal.ofReal K * I ≤ ENNReal.ofReal F * I₁ := by
    calc ENNReal.ofReal K * I = ∫⁻ p, ENNReal.ofReal K * A p := (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ p, ENNReal.ofReal F * A₁ (sBig r κ τ p) := lintegral_mono h2
      _ = ENNReal.ofReal F * I₁ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  constructor
  ·
    have b : ENNReal.ofReal (jacBig r κ τ * K) * I ≤ ENNReal.ofReal (F * K) * I := by
      calc ENNReal.ofReal (jacBig r κ τ * K) * I = ENNReal.ofReal (jacBig r κ τ) * (ENNReal.ofReal K * I) := by
            rw [ENNReal.ofReal_mul hJ.le, mul_assoc]
        _ ≤ ENNReal.ofReal (jacBig r κ τ) * (ENNReal.ofReal F * I₁) := by gcongr
        _ = ENNReal.ofReal F * (ENNReal.ofReal K * I) := by rw [mul_left_comm, e]
        _ = ENNReal.ofReal (F * K) * I := by rw [ENNReal.ofReal_mul hF, mul_assoc]
    have c := (ENNReal.mul_le_mul_iff_left h0 htop).mp b
    rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg hF hK.le)] at c
    nlinarith
  · have b : ENNReal.ofReal K * I ≤ ENNReal.ofReal (jacBig r κ τ * K * F) * I := by
      calc ENNReal.ofReal K * I = ENNReal.ofReal (jacBig r κ τ) * I₁ := e.symm
        _ ≤ ENNReal.ofReal (jacBig r κ τ) * (ENNReal.ofReal (K * F) * I) := by gcongr
        _ = ENNReal.ofReal (jacBig r κ τ * K * F) * I := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hJ.le, mul_assoc (jacBig r κ τ)]
    have c := (ENNReal.mul_le_mul_iff_left h0 htop).mp b
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at c
    nlinarith

theorem jacBig_one (τ : ℝ) : jacBig r 1 τ = τ ^ (4 * (r + 1)) := by
  unfold jacBig tF
  simp only [one_pow, mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, ← pow_add]; ring_nf

theorem cf_ge_two (hτ : 1 < τ) (Cf : ℝ) (A A₁ : (Fin r → ℂ) × ℂ → ENNReal) (K : ℝ) (hK : 0 < K)
    (h1 : ∀ p, A₁ (sBig r 1 τ p) ≤
      ENNReal.ofReal (K * (max τ τ⁻¹ ^ (Cf * ((2 * r + 2 : ℕ) : ℝ)))) * A p)
    (h2 : ∀ p, ENNReal.ofReal K * A p ≤
      ENNReal.ofReal (max τ τ⁻¹ ^ (Cf * ((2 * r + 2 : ℕ) : ℝ))) * A₁ (sBig r 1 τ p))
    (hint : ∫⁻ p, A₁ p = ENNReal.ofReal K * ∫⁻ p, A p) (h0 : ∫⁻ p, A p ≠ 0) (htop : ∫⁻ p, A p ≠ ⊤) :
    2 ≤ Cf := by
  have hτ0 : 0 < τ := by linarith
  have hmax : max τ τ⁻¹ = τ := max_eq_left (by
    have : τ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hτ
    linarith)
  rw [hmax] at h1 h2
  have hF : 0 ≤ τ ^ (Cf * ((2 * r + 2 : ℕ) : ℝ)) := Real.rpow_nonneg hτ0.le _
  have := (frame_factor_ge one_pos hτ0 A A₁ K _ hK hF h1 h2 hint h0 htop).1
  rw [jacBig_one, ← Real.rpow_natCast] at this
  have h := (Real.rpow_le_rpow_left_iff hτ).mp this
  push_cast at h
  have hr : (0 : ℝ) < 2 * r + 2 := by positivity
  nlinarith

theorem frames_ineqs {pw pw₁ s K ρ F : ℝ} (X : ENNReal) (hs : 0 ≤ s) (hK : 0 ≤ K) (hρ : 0 < ρ)
    (h1 : ρ ≤ F) (h2 : ρ⁻¹ ≤ F) (he : pw₁ * s = K * ρ * pw) :
    ENNReal.ofReal pw₁ * (ENNReal.ofReal s * X) ≤ ENNReal.ofReal (K * F) * (ENNReal.ofReal pw * X) ∧
      ENNReal.ofReal K * (ENNReal.ofReal pw * X) ≤ ENNReal.ofReal F * (ENNReal.ofReal pw₁ * (ENNReal.ofReal s * X)) := by
  have hF : 0 < F := lt_of_lt_of_le hρ h1
  rw [← mul_assoc (ENNReal.ofReal pw₁), ← ENNReal.ofReal_mul' hs, he]
  by_cases hp : pw ≤ 0
  · have h0 : K * ρ * pw ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hK hρ.le) hp
    rw [ENNReal.ofReal_of_nonpos h0, ENNReal.ofReal_of_nonpos hp]
    simp
  · push Not at hp
    constructor
    · rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hK hF.le)]
      gcongr ENNReal.ofReal ?_ * _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hK) hp.le
    · rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_mul hF.le]
      gcongr ENNReal.ofReal ?_ * _
      have : 1 ≤ F * ρ := by
        have := mul_le_mul_of_nonneg_right h2 hρ.le
        rwa [inv_mul_cancel₀ hρ.ne'] at this
      nlinarith [mul_nonneg hK hp.le]

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.KfinOfMemLowKSub
section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.MainNotions.DoubleDerivativeSmoothness

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄

section Smooth

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem finset_sup_kstable {n : ℕ} (ε : Fin n → Bool) (τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (s : Finset (Submodule ℂ H)) (hs : ∀ S ∈ s, FiniteDimensional ℂ S ∧ IsKStableOn ε τ S) :
    FiniteDimensional ℂ ↥(s.sup (id : Submodule ℂ H → Submodule ℂ H)) ∧
      IsKStableOn ε τ (s.sup (id : Submodule ℂ H → Submodule ℂ H)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, ?_⟩
    · show FiniteDimensional ℂ ↥(⊥ : Submodule ℂ H)
      infer_instance
    · intro g _ v hv
      simp only [Finset.sup_empty, Submodule.mem_bot] at hv
      simp [hv]
  | insert a s ha ih =>
    have hA := hs a (Finset.mem_insert_self a s)
    have hS := ih (fun S hS' => hs S (Finset.mem_insert_of_mem hS'))
    rw [Finset.sup_insert]
    have := hA.1
    have := hS.1
    refine ⟨?_, ?_⟩
    · simp only [id]
      infer_instance
    · intro g hg v hv
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add]
      exact Submodule.add_mem_sup (hA.2 g hg x hx) (hS.2 g hg y hy)

theorem kfin_of_mem_lowKSub {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ}
    {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {w : H} (hw : w ∈ lowKSub ε lam τ) :
    ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ w ∈ S ∧ IsKStableOn ε τ S := by
  obtain ⟨s, hsS, hws⟩ := Submodule.mem_sSup_iff_exists_finset.1 hw
  have h := finset_sup_kstable ε τ s (fun S hS => ⟨(hsS hS).1, (hsS hS).2.1⟩)
  refine ⟨s.sup (id : Submodule ℂ H → Submodule ℂ H), h.1, ?_, h.2⟩
  rw [Finset.sup_eq_iSup]
  exact hws

theorem kfinHpk_of_lowUnitH {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mx k r → (H →L[ℂ] H)} {w : H} (hw : IsLowUnitH k r ε lam σ w) : IsKFinHpk (k := k) (r := r) σ w := by
  obtain ⟨P, hP, -, hmem⟩ := hw
  obtain ⟨S, hfd, hwS, hst⟩ := kfin_of_mem_lowKSub hmem
  exact ⟨S, hfd, hwS, Formalism.MainNotions.LowestKTypeMultiplicity.kstable_Hpk hP hst⟩

theorem zero_mem_smoothVecs (σ : Mx k r → (H →L[ℂ] H)) : (0 : H) ∈ smoothVecs (k := k) (r := r) σ := by
  intro g₀ _
  refine ⟨Set.univ, fun _ => (0 : H), isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => ?_⟩
  simp

def smoothSub (σ : Mx k r → (H →L[ℂ] H)) : Submodule ℂ H where
  carrier := smoothVecs (k := k) (r := r) σ
  add_mem' := fun h1 h2 => Formalism.MainNotions.LeviCoordinates.smooth_vectors_add h1 h2
  zero_mem' := zero_mem_smoothVecs σ
  smul_mem' := fun c _ h => Formalism.MainNotions.LeviCoordinates.smooth_vectors_smul c h

theorem ddSmooth_of [CompleteSpace H] (hKS : Formalism.MainNotions.DiscreteSeriesInnerProducts.KFinSmooth) {ε : Fin (2 * r + k + 1) → Bool}
    {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mx k r → (H →L[ℂ] H)} {w0 : H} (hσ : IsDSHpk k r ε lam σ)
    (hw0 : IsLowUnitH k r ε lam σ w0) : DDSmoothAt σ w0 := by
  have hw : w0 ∈ smoothVecs (k := k) (r := r) σ := hKS k r ε lam H σ hσ w0 (kfinHpk_of_lowUnitH hw0)
  have hle : DDsp σ w0 ≤ smoothSub σ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    exact Formalism.MainNotions.LeviCoordinates.smooth_vectors_translate_unitary (fun _ ha _ hb => Formalism.MainNotions.LeviCoordinates.discrete_series_map_mul hσ ha hb) hw hg
  intro u hu
  exact hle hu

end Smooth

end Formalism.MainNotions.DoubleDerivativeSmoothness
end
end

