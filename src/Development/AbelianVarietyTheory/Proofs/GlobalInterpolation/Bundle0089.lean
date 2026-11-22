import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0033
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0038
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0079
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0073
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0062
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0081
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0064
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DiscOneScaleRatioIdealRingAlgebraicUnit
section
noncomputable section

namespace GlobalTheory.MomDelta

section Scale

open GlobalTheory.MomOne

def scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : PeriodPair :=
  ⟨c * L.ω₁, c * L.ω₂, LinearIndependent.pair_iff.2 fun s t h => by
    have h' : s • L.ω₁ + t • L.ω₂ = 0 := by
      apply mul_left_cancel₀ hc
      simp only [Complex.real_smul] at h ⊢
      linear_combination h
    exact LinearIndependent.pair_iff.1 L.indep s t h'⟩

theorem mem_scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    c * z ∈ (scalePair L c hc).lattice ↔ z ∈ L.lattice := by
  rw [PeriodPair.mem_lattice, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    refine ⟨m, n, mul_left_cancel₀ hc ?_⟩
    simp only [scalePair] at h
    linear_combination h
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp only [scalePair]; ring⟩

theorem G_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (k : ℕ) :
    L.G k = c ^ k * (scalePair L c hc).G k := by
  let e : (L.lattice : Set ℂ) ≃ ((scalePair L c hc).lattice : Set ℂ) :=
    (Equiv.mulLeft₀ c hc).subtypeEquiv fun w => by
      simpa using (mem_scalePair L c hc w).symm
  have h2 : ∀ P : PeriodPair, P.G k = ∑' w : (P.lattice : Set ℂ), ((w : ℂ) ^ k)⁻¹ := fun _ => rfl
  rw [h2, h2, ← e.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun w => ?_
  have : ((e w : ((scalePair L c hc).lattice : Set ℂ)) : ℂ) = c * w := rfl
  rw [this, mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hc), one_mul]

theorem g₂_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : (scalePair L c hc).g₂ = L.g₂ / c ^ 4 := by
  simp only [PeriodPair.g₂, G_scale L c hc 4]
  field_simp

theorem g₃_scale (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : (scalePair L c hc).g₃ = L.g₃ / c ^ 6 := by
  simp only [PeriodPair.g₃, G_scale L c hc 6]
  field_simp

variable {q : ℕ} [Fact q.Prime]

theorem ok_scale (M : Mdl q) (hM : M.Ok) (c : ℂ) (hc : c ≠ 0) :
    (Mdl.mk M.ι (scalePair M.L c hc) (M.c / c) M.W).Ok := by
  obtain ⟨h0, h1, h2, h3, h4, h6, hΔ, hg2, hg3⟩ := hM
  refine ⟨div_ne_zero h0 hc, h1, h2, h3, h4, h6, hΔ, ?_, ?_⟩
  · have : (scalePair M.L c hc).g₂ / (M.c / c) ^ 4 = M.L.g₂ / M.c ^ 4 := by
      rw [g₂_scale]; field_simp
    show M.W.c₄ / 12 = M.ι _
    rw [this]; exact hg2
  · have : (scalePair M.L c hc).g₃ / (M.c / c) ^ 6 = M.L.g₃ / M.c ^ 6 := by
      rw [g₃_scale]; field_simp
    show M.W.c₆ / 216 = M.ι _
    rw [this]; exact hg3

theorem norm_disc_ring (ι : ℂ ≃+* ℂ_[q]) {d : ℕ} (hd : d.Prime) (h16 : d % 16 = 7) (L' : PeriodPair) (N : ℕ)
    (hq : q ≠ 2) (hN : Nat.Coprime N (2 * q)) (hN0 : N ≠ 0)
    (h1 : ∀ z, InOK d z → (N : ℂ) * z ∈ L'.lattice) (h2 : ∀ x ∈ L'.lattice, InOK d x) :
    ‖ι (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2)‖ = ‖ι (discr d)‖ := by
  have hc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hL := Basic.isOK_okPair d hd.pos
  obtain ⟨M, hMι, hML, hOk, -⟩ := exists_model d q ι _ hd h16 hL
  have hIs : IsOK d M.L := hML ▸ hL
  subst hMι
  have hk := GlobalTheory.T.norm_discriminant_superlattice_odd_index_eq q (Mdl.mk M.ι (scalePair M.L N hc) (M.c / N) M.W) L' N hq (ok_scale M hOk N hc) hN
    (fun z hz => by
      have e : z = (N : ℂ) * (z / N) := by field_simp
      have hz' : (N : ℂ) * (z / N) ∈ (scalePair M.L N hc).lattice := by rw [← e]; exact hz
      rw [e]
      exact h1 _ ((hIs _).1 ((mem_scalePair M.L N hc _).1 hz')))
    (fun x hx => (mem_scalePair M.L N hc x).2 ((hIs x).2 (h2 x hx)))
  have e : (scalePair M.L N hc).g₂ ^ 3 - 27 * (scalePair M.L N hc).g₃ ^ 2
      = (M.L.g₂ ^ 3 - 27 * M.L.g₃ ^ 2) / (N : ℂ) ^ 12 := by
    rw [g₂_scale, g₃_scale]; field_simp
  have hnorm : ‖M.ι (N : ℂ)‖ = 1 := by
    rw [map_natCast]
    exact Basic.norm_nat_eq_one (Nat.Coprime.symm (Nat.coprime_mul_iff_right.1 hN).2)
  refine hk.trans ?_
  show ‖M.ι ((scalePair M.L N hc).g₂ ^ 3 - 27 * (scalePair M.L N hc).g₃ ^ 2)‖ = _
  rw [e, map_div₀, norm_div, map_pow, norm_pow, hnorm, one_pow, div_one, (Basic.discr_eq hIs).1]

end Scale

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem delta_ratio : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    δ₀ ^ 12 = GlobalTheory.MomOne.discr D.host.d → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → Nat.Coprime (Ideal.absNorm cc) q →
    δ / δ₀ ∈ Qbar ∧ ∀ ι : ℂ ≃+* ℂ_[q], ‖ι (δ / δ₀)‖ = 1 := by
  intro D cc δ δ₀ hcc hδ hδ₀ q _ hq hNq
  obtain ⟨hdp, h16, hOK, -, hlam⟩ := GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts D
  obtain ⟨hne, hcop⟩ := hcc
  have hN0 : Ideal.absNorm cc ≠ 0 := fun h => hne (Ideal.absNorm_eq_zero_iff.1 h)
  have hN2 : Nat.Coprime (Ideal.absNorm cc) (2 * q) :=
    Nat.coprime_mul_iff_right.2 ⟨(Nat.coprime_mul_iff_right.1 hcop).1, hNq⟩
  obtain ⟨L', hL'⟩ := Formalism.L2.PairingIndexBounds.Rec.exists_pp D cc hne
  have hmem : ((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) ∈ cc := Ideal.absNorm_mem cc
  have hΔ : Formalism.MainNotions.TaylorLogMetric.discr (Formalism.MainNotions.TaylorLogMetric.lamOf D cc 1) = L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 := by
    have h4 := Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L' hL' 2 (by norm_num)
    have h6 := Formalism.L2.PairingIndexBounds.Rec.eisG_eq_G _ L' hL' 3 (by norm_num)
    unfold Formalism.MainNotions.TaylorLogMetric.discr Formalism.MainNotions.TaylorLogMetric.g2 Formalism.MainNotions.TaylorLogMetric.g3
    rw [h4, h6]
    simp [PeriodPair.g₂, PeriodPair.g₃]
  have h1 : ∀ z, GlobalTheory.MomOne.InOK D.host.d z → ((Ideal.absNorm cc : ℕ) : ℂ) * z ∈ L'.lattice := by
    intro z hz
    obtain ⟨x, rfl⟩ := (hOK z).1 hz
    refine (hL' _).1 ((hlam cc 1 hne).2 _ |>.2 ⟨((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) * x, cc.mul_mem_right x hmem, ?_⟩)
    simp
  have h2 : ∀ x ∈ L'.lattice, GlobalTheory.MomOne.InOK D.host.d x := by
    intro x hx
    obtain ⟨c, -, rfl⟩ := ((hlam cc 1 hne).2 x).1 ((hL' x).2 hx)
    exact (hOK _).2 ⟨c, by simp⟩
  have hne₀ : GlobalTheory.MomOne.discr D.host.d ≠ 0 :=
    (GlobalTheory.MomOne.Basic.discr_eq (GlobalTheory.MomOne.Basic.isOK_okPair _ hdp.pos)).2
  have hδ₀0 : δ₀ ≠ 0 := by
    rintro rfl
    exact hne₀ (by rw [← hδ₀]; simp)
  have key : ∀ ι : ℂ ≃+* ℂ_[q], ‖ι (δ / δ₀)‖ = 1 := by
    intro ι
    have h := norm_disc_ring ι hdp h16 L' _ hq hN2 hN0 h1 h2
    have hδ' : δ ^ 12 = L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 := by rw [← hΔ]; exact hδ
    rw [← hδ', ← hδ₀, map_pow, map_pow, norm_pow, norm_pow] at h
    have hι₀ : ‖ι δ₀‖ ≠ 0 := by simpa using hδ₀0
    have h12 : ‖ι (δ / δ₀)‖ ^ 12 = 1 := by
      rw [map_div₀, norm_div, div_pow, h, div_self (pow_ne_zero _ hι₀)]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h12
  obtain ⟨ι⟩ := GlobalTheory.MomOne.Basic.nonempty_iso q
  exact ⟨GlobalTheory.MomOne.mem_algebraicClosure_of_norm_le q ι _ 1 fun ι' _ => (key ι').le, key⟩

end GlobalTheory.MomDelta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualWeylHighestWeightSpaceLineFieldStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_highestWeight_space_line_field : ∀ (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ f ∈ dualWeyl k N N ν, IsWeightedHomogeneous (rowW N N) f ν → ∃ c : k, f = c • hw k le_rfl ν := by
  first | exact @GlobalTheory.Alc.hw_line_field | exact GlobalTheory.Alc.hw_line_field | (intros; apply GlobalTheory.Alc.hw_line_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsHcParamOfCode
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem exists_hcParam_of_code (R : Ranks) (D h : ℕ) (hD : 1 ≤ D) (hh : ((R.t : ℚ) + 3) / 2 ≤ h)
    (U0 UL B : ℤ) (h0 : ((R.k - 2 : ℕ) : ℚ) * (4 * (D : ℚ)) ≤ U0) (hL : UL < 0) (hB : -B ≤ UL)
    (w : Fin (R.k - 2) → Bool) :
    ∃ p : HCParam R, (∀ i : Fin (R.k - 1), p.v i = ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (D : ℚ))) ∧
      (∀ hk : 0 < R.k, p.u ⟨0, hk⟩ = U0 + 1 / 2 ∧ p.u ⟨R.k - 1, by omega⟩ = UL + 1 / 2) ∧
      (∀ (l : ℕ) (hl : l < R.k - 2), p.u ⟨l + 1, by omega⟩ =
        ((R.k - 2 - l : ℕ) : ℚ) * (4 * (D : ℚ)) - 1 / 2 - (if w ⟨l, hl⟩ then (D : ℚ) else 0)) ∧
      ∀ j : Fin R.m, p.b j = B + (j.1 : ℚ) * (2 * h) ∧ p.e j = p.b j + h := by
  have hk5 : 5 ≤ R.k := by have := R.two_le_m; have := R.m_add_three_le_k; omega
  have hD' : (1 : ℚ) ≤ D := by exact_mod_cast hD
  let u : Fin R.k → ℚ := fun i =>
    if i.1 = 0 then U0 + 1 / 2 else
      if hi : i.1 - 1 < R.k - 2 then
        ((R.k - 2 - (i.1 - 1) : ℕ) : ℚ) * (4 * (D : ℚ)) - 1 / 2 - (if w ⟨i.1 - 1, hi⟩ then (D : ℚ) else 0)
      else UL + 1 / 2
  have u0 : ∀ hk : 0 < R.k, u ⟨0, hk⟩ = U0 + 1 / 2 := fun hk => by simp [u]
  have uL : ∀ hk : R.k - 1 < R.k, u ⟨R.k - 1, hk⟩ = UL + 1 / 2 := fun hk => by
    have h1 : ¬ (R.k - 1 = 0) := by omega
    have h2 : ¬ (R.k - 1 - 1 < R.k - 2) := by omega
    simp only [u, h1, h2, if_false, dite_false]
  have um : ∀ (l : ℕ) (hl : l < R.k - 2) (hk : l + 1 < R.k), u ⟨l + 1, hk⟩ =
      ((R.k - 2 - l : ℕ) : ℚ) * (4 * (D : ℚ)) - 1 / 2 - (if w ⟨l, hl⟩ then (D : ℚ) else 0) := fun l hl hk => by
    simp only [u, Nat.add_one_ne_zero, Nat.add_sub_cancel, hl, if_false, dite_true]
  have hLq : (UL : ℚ) ≤ -1 := by exact_mod_cast (by omega : UL ≤ -1)
  have hBq : -(B : ℚ) ≤ UL := by exact_mod_cast hB
  refine ⟨⟨u, fun i => ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (D : ℚ)), fun j => B + (j.1 : ℚ) * (2 * h),
    fun j => B + (j.1 : ℚ) * (2 * h) + h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun i => rfl, fun hk => ⟨u0 hk, uL _⟩, fun l hl => um l hl _, fun j => ⟨rfl, rfl⟩⟩
  · rintro ⟨i, hi⟩
    rcases i with _ | l
    · rw [u0]; simp only [Nat.sub_zero]; linarith
    · have hl : l < R.k - 2 := by omega
      rw [um l hl]
      have : R.k - 2 - l = (R.k - 2 - (l + 1)) + 1 := by omega
      rw [this]; push_cast
      split_ifs <;> linarith
  · rintro ⟨l, hi⟩
    by_cases hl : l < R.k - 2
    · rw [um l hl]
      split_ifs <;> linarith
    · have e1 : l + 1 = R.k - 1 := by omega
      have e2 : R.k - 2 - l = 0 := by omega
      have : u ⟨l + 1, by omega⟩ = UL + 1 / 2 := by
        rw [← uL (by omega)]; congr 2
      simp only [this, e2]
      push_cast; linarith
  · intro hk hm
    rw [uL]; simp only [Nat.cast_zero]; linarith
  · intro j; linarith
  · intro j hj; push_cast; linarith
  · intro j; exact ⟨B + j.1 * (2 * h) + h, by push_cast; ring⟩
  · rintro ⟨i, hi⟩
    rcases i with _ | l
    · exact ⟨U0, u0 _⟩
    · by_cases hl : l < R.k - 2
      · rw [um l hl]
        split_ifs
        · exact ⟨((R.k - 2 - l : ℕ) : ℤ) * (4 * D) - 1 - D, by push_cast; ring⟩
        · exact ⟨((R.k - 2 - l : ℕ) : ℤ) * (4 * D) - 1, by push_cast; ring⟩
      · have e1 : l + 1 = R.k - 1 := by omega
        refine ⟨UL, ?_⟩
        rw [← uL (by omega)]; congr 2
  · intro i; exact ⟨((R.k - 2 - i.1 : ℕ) : ℤ) * (4 * D), by push_cast; ring⟩
  · intro j; exact ⟨B + j.1 * (2 * h), by push_cast; ring⟩

theorem hc_sizes (eps cD ch : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hcD : 0 ≤ cD) (hch : 402 ≤ ch) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R →
      1 ≤ Delv s cD ∧ ((R.t : ℚ) + 3) / 2 ≤ (⌈s.x ^ ch⌉₊ : ℕ) ∧
      (R.k : ℝ) * (4 * (Delv s cD : ℝ)) ≤ s.a ∧ (R.k : ℝ) ≤ s.b' / s.x ∧ 0 < s.b' ∧ 0 < s.b ∧ 0 < s.w'' R.n := by
  obtain ⟨x1, H1⟩ := GlobalTheory.T.scale_polynomial_quantities_comparison eps (cD + 6) 1 h0 one_pos
  obtain ⟨x2, H2⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps h0 h1
  refine ⟨max 8 (max x1 x2), fun s R he hx hR => ?_⟩
  have hx8 : 8 ≤ s.x := le_trans (le_max_left _ _) hx
  have hx1 : x1 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : x2 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨-, -, hS, -⟩ := H1 s he hx1
  obtain ⟨-, -, hr, hkr, -, -, -, -, -, -, -, -, -, ht, -⟩ := H2 s R he hx2 hR
  have hxp : 0 < s.x := by linarith
  have hx1' : 1 ≤ s.x := by linarith
  rw [Real.rpow_one] at hS
  have hb : 0 < s.b := Real.exp_pos _
  have hX : 1 ≤ s.X' := Real.one_le_exp (Real.rpow_nonneg hxp.le _)
  have hXp : 0 < s.X' := by linarith
  have hk : (R.k : ℝ) ≤ s.x ^ (5 : ℝ) := le_trans (by exact_mod_cast hkr) hr
  have hD1 : 1 ≤ s.x ^ cD := Real.one_le_rpow hx1' hcD
  have h5 : 1 ≤ s.x ^ (5 : ℝ) := Real.one_le_rpow hx1' (by norm_num)
  have hsplit : s.x ^ (cD + 6) = s.x ^ cD * s.x ^ (5 : ℝ) * s.x := by
    rw [show cD + 6 = cD + 5 + 1 by ring, Real.rpow_add hxp, Real.rpow_add hxp, Real.rpow_one]
  have hDle : (Delv s cD : ℝ) ≤ 2 * s.x ^ cD := by
    have := Nat.ceil_lt_add_one (show 0 ≤ s.x ^ cD by linarith)
    unfold Delv; linarith
  have hb' : 0 < s.b' := div_pos (mul_pos hxp hb) hXp
  have hn : (0 : ℝ) < R.n := by unfold Ranks.n; positivity
  refine ⟨?_, ?_, ?_, ?_, hb', hb, div_pos hb' (mul_pos hxp hn)⟩
  · exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by linarith)).ne'
  · have h401 : 1 ≤ s.x ^ (401 : ℝ) := Real.one_le_rpow hx1' (by norm_num)
    have h402 : s.x ^ (401 : ℝ) * s.x ≤ s.x ^ ch := by
      rw [← Real.rpow_add_one hxp.ne']
      exact Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
    have hc := Nat.le_ceil (s.x ^ ch)
    have : ((R.t : ℝ) + 3) / 2 ≤ (⌈s.x ^ ch⌉₊ : ℕ) := by nlinarith
    have h' : ((((R.t : ℚ) + 3) / 2 : ℚ) : ℝ) ≤ (((⌈s.x ^ ch⌉₊ : ℕ) : ℚ) : ℝ) := by push_cast; exact this
    exact_mod_cast h'
  · have hP : 0 ≤ s.x ^ cD * s.x ^ (5 : ℝ) := by positivity
    have e1 : (R.k : ℝ) * (4 * (Delv s cD : ℝ)) ≤ s.x ^ (5 : ℝ) * (4 * (2 * s.x ^ cD)) := by gcongr
    have e2 : s.x ^ (cD + 6) ≤ s.x ^ (cD + 6) * s.X' := le_mul_of_one_le_right (by positivity) hX
    have e3 : s.b ≤ s.a := le_mul_of_one_le_left hb.le hx1'
    have e4 : s.x ^ cD * s.x ^ (5 : ℝ) * 8 ≤ s.x ^ cD * s.x ^ (5 : ℝ) * s.x := by gcongr
    linarith
  · have e : s.b' / s.x = s.b / s.X' := by
      unfold Scale.b' Scale.a; field_simp
    rw [e, le_div_iff₀ hXp]
    refine le_trans ?_ hS
    gcongr
    exact le_trans hk (Real.rpow_le_rpow_of_exponent_le hx1' (by linarith))

theorem exists_hc_family : ∀ eps cD ch C8 : ℝ, 0 < eps → eps < 1 / 52 → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (H : Host R) (aT bT : H.TT → ℤ), s.eps = eps → x0 ≤ s.x → RankVal s R → HostVal s C8 H → (∀ t, s.a ≤ (aT t : ℝ) ∧ s.b' ≤ (bT t : ℝ)) → ∀ (Tau : Type) [Fintype Tau] (eTau : Tau ≃ R.Psi), ∃ hcw : (Fin (R.k - 2) → Bool) → Tau → HCParam R, (∀ w, HCVal s cD ch H (fun τ => (eTau τ : R.GG)) (hcw w) bT) ∧ (∀ w w' τ, (hcw w τ).v = (hcw w' τ).v ∧ (hcw w τ).b = (hcw w' τ).b ∧ (hcw w τ).e = (hcw w' τ).e ∧ ∀ h : 0 < R.k, (hcw w τ).u ⟨0, h⟩ = (hcw w' τ).u ⟨0, h⟩ ∧ (hcw w τ).u ⟨R.k - 1, by omega⟩ = (hcw w' τ).u ⟨R.k - 1, by omega⟩) ∧ (∀ w τ (l : ℕ) (h : l < R.k - 2), (hcw w τ).u ⟨l + 1, by omega⟩ = (hcw w τ).v ⟨l, by omega⟩ - 1 / 2 - (if w ⟨l, h⟩ then (Delv s cD : ℚ) else 0)) ∧ ∀ w τ (t : H.TT) (h : 0 < R.k), (eTau τ : R.GG) = R.tau1 t → (hcw w τ).u ⟨0, h⟩ = (aT t : ℚ) + ((R.k : ℚ) - 1) / 2 ∧ (hcw w τ).u ⟨R.k - 1, by omega⟩ = -(bT t : ℚ) - ((R.k : ℚ) - 1) / 2 := by
  intro eps cD ch C8 he0 he1 hcD hch
  obtain ⟨x0, Hs⟩ := hc_sizes eps cD ch he0 he1 hcD hch
  refine ⟨x0, fun s R H aT bT he hx hR hH hab Tau _ eTau => ?_⟩
  classical
  obtain ⟨hD, hh, hka, hkb, hb', hb, hw⟩ := Hs s R he hx hR
  have hk5 : 5 ≤ R.k := by have := R.two_le_m; have := R.m_add_three_le_k; omega
  obtain ⟨κ, hκ⟩ := R.k_even
  have hκq : (R.k : ℚ) = 2 * κ := by rw [hκ]; push_cast; ring
  obtain ⟨-, hthP, hdisj, -, hcard⟩ := factTopsThick R H
  have hinj : ∀ t t' : H.TT, R.tau1 t = R.tau1 t' → t = t' := fun t t' h =>
    Subtype.ext (R.iota_bijective.1 (congrArg Prod.snd h))
  have htop : ∀ g, g ∈ H.topPlaces ↔ ∃ t : H.TT, g = R.tau1 t := fun g => by
    unfold Host.topPlaces
    rw [Finset.mem_image]
    exact ⟨fun ⟨t, ht, e⟩ => ⟨⟨t, ht⟩, e.symm⟩, fun ⟨t, e⟩ => ⟨t.1, t.2, e.symm⟩⟩
  have hne : H.thickPlaces.Nonempty := by
    rw [← Finset.card_pos, hcard]
    have h1 := hH.2.2.1
    have hxp : 0 < s.x := by linarith [s.one_lt_alt]
    have hn : (0 : ℝ) < R.n := by unfold Ranks.n; positivity
    have : (0 : ℝ) < H.T2.card := lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hxp _) hn) h1
    exact_mod_cast this
  obtain ⟨g0, hg0⟩ := hne
  let τ0 : Tau := eTau.symm ⟨g0, hthP g0 hg0⟩
  have hτ0 : (eTau τ0 : R.GG) = g0 := by simp [τ0]
  let base : Tau → ℤ := fun τ =>
    if h : ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t then bT h.choose + ⌊s.b' / s.x⌋
    else if (eTau τ : R.GG) ∈ H.thickPlaces then ⌈s.b⌉ else ⌈s.w'' R.n⌉
  obtain ⟨sh, hsh, hMU⟩ := UpperTheory.Mu.exists_shift H eTau base τ0
  let ε : ℤ := (sh : ℤ)
  have hε : 0 ≤ ε ∧ ε < (NumberField.Units.torsionOrder H.E : ℤ) :=
    ⟨Int.natCast_nonneg _, Int.ofNat_lt.2 hsh⟩
  let b1 : Tau → ℤ := fun τ => base τ + if τ = τ0 then ε else 0
  let U0 : Tau → ℤ := fun τ =>
    if h : ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t then aT h.choose + κ - 1
    else ((R.k - 2 : ℕ) : ℤ) * (4 * Delv s cD) + R.k * (4 * Delv s cD)
  let UL : Tau → ℤ := fun τ =>
    if h : ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t then -bT h.choose - κ else -1
  have hT : ∀ τ (t : H.TT), (eTau τ : R.GG) = R.tau1 t →
      b1 τ = bT t + ⌊s.b' / s.x⌋ ∧ U0 τ = aT t + κ - 1 ∧ UL τ = -bT t - κ := fun τ t ht => by
    have h : ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t := ⟨t, ht⟩
    have hc : h.choose = t := hinj _ _ (h.choose_spec.symm.trans ht)
    have hτ : τ ≠ τ0 := by
      rintro rfl
      exact Finset.disjoint_left.1 hdisj ((htop _).2 h) (hτ0 ▸ hg0)
    simp only [b1, base, U0, UL, dif_pos h, hc, if_neg hτ, add_zero, and_self]
  have hN : ∀ τ, (¬ ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t) →
      1 ≤ b1 τ ∧ U0 τ = ((R.k - 2 : ℕ) : ℤ) * (4 * Delv s cD) + R.k * (4 * Delv s cD) ∧ UL τ = -1 := fun τ h => by
    have c1 : 0 < ⌈s.b⌉ := Int.ceil_pos.2 hb
    have c2 : 0 < ⌈s.w'' R.n⌉ := Int.ceil_pos.2 hw
    simp only [b1, base, U0, UL, dif_neg h, and_self, and_true]
    split_ifs <;> omega
  have hcond : ∀ τ, ((R.k - 2 : ℕ) : ℚ) * (4 * (Delv s cD : ℚ)) ≤ U0 τ ∧ UL τ < 0 ∧ -b1 τ ≤ UL τ := fun τ => by
    by_cases h : ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t
    · obtain ⟨t, ht⟩ := h
      obtain ⟨e1, e2, e3⟩ := hT τ t ht
      have a1 : (R.k : ℤ) * (4 * (Delv s cD : ℤ)) ≤ aT t := by
        have := hka.trans (hab t).1
        exact_mod_cast this
      have a2 : 0 < bT t := by
        have := hb'.trans_le (hab t).2
        exact_mod_cast this
      have a3 : (R.k : ℤ) ≤ ⌊s.b' / s.x⌋ := Int.le_floor.2 (by exact_mod_cast hkb)
      rw [e1, e2, e3]
      refine ⟨?_, by omega, by omega⟩
      have a4 : ((R.k - 2 : ℕ) : ℤ) * (4 * (Delv s cD : ℤ)) ≤ (R.k : ℤ) * (4 * (Delv s cD : ℤ)) := by
        gcongr; omega
      have : ((R.k - 2 : ℕ) : ℤ) * (4 * (Delv s cD : ℤ)) ≤ aT t + κ - 1 := by omega
      exact_mod_cast this
    · obtain ⟨e1, e2, e3⟩ := hN τ h
      rw [e2, e3]
      refine ⟨?_, by omega, by omega⟩
      push_cast
      have : (0 : ℚ) ≤ (R.k : ℚ) * (4 * (Delv s cD : ℚ)) := by positivity
      linarith
  choose p hv hu hm hbe using fun (w : Fin (R.k - 2) → Bool) (τ : Tau) =>
    exists_hcParam_of_code R (Delv s cD) ⌈s.x ^ ch⌉₊ hD hh (U0 τ) (UL τ) (b1 τ)
      (hcond τ).1 (hcond τ).2.1 (hcond τ).2.2 w
  have hh0 : (h0v s ch : ℚ) = 2 * (⌈s.x ^ ch⌉₊ : ℕ) := by unfold h0v; push_cast; ring
  refine ⟨p, fun w => ⟨fun τ i => hv w τ i, fun τ hk hτ => ?_, ⟨b1, fun τ j => ?_, fun τ t ht => (hT τ t ht).1,
    fun τ hτ => ?_, fun τ hτ => ?_⟩, fun j => ?_⟩, fun w w' τ => ⟨?_, ?_, ?_, fun h => ?_⟩, fun w τ l h => ?_,
    fun w τ t h ht => ?_⟩
  · obtain ⟨-, e2, e3⟩ := hN τ (fun h => hτ ((htop _).2 h))
    rw [(hu w τ hk).1, (hu w τ hk).2, e2, e3]
    constructor
    · push_cast; ring
    · norm_num
  · rw [(hbe w τ j).2, (hbe w τ j).1, hh0]
    constructor <;> ring
  · have h : ¬ ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t := fun h =>
      Finset.disjoint_left.1 hdisj ((htop _).2 h) hτ
    have hτ' : (eTau τ : R.GG) ∈ H.thickPlaces := hτ
    simp only [b1, base, dif_neg h, if_pos hτ']
    split_ifs <;> omega
  · have h : ¬ ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t := fun h => hτ.2.1 ((htop _).2 h)
    have hτ' : (eTau τ : R.GG) ∉ H.thickPlaces := hτ.2.2
    have hτ1 : τ ≠ τ0 := by
      rintro rfl
      exact hτ' (hτ0 ▸ hg0)
    simp only [b1, base, dif_neg h, if_neg hτ', if_neg hτ1, add_zero]
  · refine UpperTheory.Mu.muq_of_parallel H eTau hMU (j.1 * (2 * (⌈s.x ^ ch⌉₊ : ℕ)) + (⌈s.x ^ ch⌉₊ : ℕ)) (fun τ => ?_)
    rw [(hbe w τ j).2, (hbe w τ j).1]
    change _ = ((b1 τ : ℤ) : ℚ) + _
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
    ring
  · funext i; rw [hv, hv]
  · funext j; rw [(hbe w τ j).1, (hbe w' τ j).1]
  · funext j; rw [(hbe w τ j).2, (hbe w' τ j).2, (hbe w τ j).1, (hbe w' τ j).1]
  · rw [(hu w τ h).1, (hu w τ h).2, (hu w' τ h).1, (hu w' τ h).2]; exact ⟨rfl, rfl⟩
  · rw [hm w τ l h, hv]
  · obtain ⟨-, e2, e3⟩ := hT τ t ht
    rw [(hu w τ h).1, (hu w τ h).2, e2, e3, hκq]
    constructor <;> (push_cast; ring)

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLatticeVectorApproxAllFinitePlacesStatement
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_vector_approx_all_finitePlaces : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → ∀ (T : ℕ), T ≠ 0 → ∀ (y : ∀ v : HeightOneSpectrum (𝓞 F), Fin k → E ⊗[F] v.adicCompletion F), (∀ v, y v ∈ locLat v Λ) → ∃ x ∈ Λ, ∀ v : HeightOneSpectrum (𝓞 F), ∃ z ∈ locLat v Λ, y v = (fun i => inclE (F := F) (v.adicCompletion F) (x i)) + T • z := by
  first | exact @GlobalTheory.OverCompare.exists_lattice_approx_all | exact GlobalTheory.OverCompare.exists_lattice_approx_all | (intros; apply GlobalTheory.OverCompare.exists_lattice_approx_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceRowWeightRatioAndLastCloudLeTwiceFStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicitChoice_rowWeight_ratio_and_lastCloud_le_twice_first : SzRow (fun C D L => (∀ j j' τ τ', 1 ≤ j → j ≤ D.R.m → 1 ≤ j' → j' ≤ D.R.m → wj D j τ ≤ L.sc.X'' D.R.n * wj D j' τ') ∧ (∀ τ (hm : 0 < D.R.m), (D.hc τ).b ⟨D.R.m - 1, by omega⟩ ≤ 2 * (D.hc τ).b ⟨0, hm⟩)) := by
  first | exact @GlobalTheory.EX.szRow_size_ratio | exact GlobalTheory.EX.szRow_size_ratio | (intros; apply GlobalTheory.EX.szRow_size_ratio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteQuotDivLatMulLatHomAt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT

theorem finite_quot_divLat_mulLat_homAt :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (cA c : ℕ), Submodule.IsLattice E N → Submodule.IsLattice E N' → 0 < cA → 0 < c → Finite (↥(divLat cA (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) :=
  GlobalTheory.finite_divLat_quot_mulLat_homAt

end GlobalTheory.MomT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodLiftsLatticeMapMemSetupGoodLifts
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomGood

theorem inOK_iff_mem_OK (d : ℕ) (z : ℂ) : GlobalTheory.MomOne.InOK d z ↔ z ∈ JMB.OK d := Iff.rfl

theorem lamA_eq_lamC {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (x : ℂ) : JMB.lamA lam x = lamC lam x := rfl

theorem main : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N₀ n : ℕ), S.d = D.host.d → (∀ x, e x ∈ S.La ↔ x ∈ La D (tor0 D cc δ) L L') → ∀ y ∈ GlobalTheory.MomT.goodLifts D (tor0 D cc δ) lam N₀ n L L', e y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ JMB.OK S.d, ‖JMB.lamA lam ((starRingEnd ℂ) κ)‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧ ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (p : ℂ) ^ n) • x} := by
  intro D cc δ N N' L L' g S e p _ lam N₀ n hd hLa y hy
  obtain ⟨-, -, hOK, hconj, -⟩ := GlobalTheory.MomDict.main D
  unfold GlobalTheory.MomT.goodLifts at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨κ, hκ, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨D.host.φ₀ ((κ : D.host.K) : D.host.E), ?_, ?_, e x, (hLa x).2 hx, ?_⟩
    · rw [hd]
      exact (inOK_iff_mem_OK _ _).1 ((hOK _).2 ⟨κ, rfl⟩)
    · rw [lamA_eq_lamC, ← hconj]
      exact hκ
    · exact map_smul e _ x
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

end GlobalTheory.MomGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocCharEqZpowMul
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

namespace GlobalTheory.LocCharVal

theorem isUnit_redP {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (b : E)
    (hb : P.valuation E b = 1) : IsUnit (redP P b) := by
  have h1 : Formalism.L2.Col.IntAt P b := (GlobalTheory.CharVal.intAt_iff _).2 hb.le
  have h2 : Formalism.L2.Col.IntAt P b⁻¹ := (GlobalTheory.CharVal.intAt_iff _).2 (by rw [map_inv₀, hb]; simp)
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have h3 := reduction_mul h1 h2
  rw [mul_inv_cancel₀ hb0] at h3
  have h4 : redP P (1 : E) = 1 := by simpa using reduction_coe P 1
  rw [h4] at h3
  exact IsUnit.of_mul_eq_one _ h3.symm

theorem locChar_eq_zpow_mul : ∀ (E K : Type) [Field E] [NumberField E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E), P.valuation E (q : E) = WithZero.exp (-1 : ℤ) → a ≠ 0 → ∃ (z : ℤ) (ζ : Kˣ), IsOfFinOrder ζ ∧ LocE.locChar q cq χ a = cq ^ z * (ζ : K) := by
  intro E K _ _ _ P q cq χ a hq ha
  have hv : P.valuation E a ≠ 0 := by simpa using ha
  have hex : ∃ z : ℤ, IsUnit (redP P (a / (q : E) ^ z)) := by
    refine ⟨-WithZero.log (P.valuation E a), isUnit_redP P _ ?_⟩
    rw [map_div₀, map_zpow₀, hq, ← WithZero.exp_zsmul]
    simp [WithZero.exp_log hv, hv]
  have hu : IsUnit (redP P (a / (q : E) ^ LocE.vP P q a)) := Classical.epsilon_spec hex
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  refine ⟨LocE.vP P q a, χ hu.unit, MonoidHom.isOfFinOrder χ (isOfFinOrder_of_finite _), ?_⟩
  unfold LocE.locChar LocE.unitV
  rw [dif_pos hu]

end GlobalTheory.LocCharVal
end

