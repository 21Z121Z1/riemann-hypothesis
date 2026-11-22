import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0087
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassSamePartOneFactorLe
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

private theorem pow_card_pow_natDegree_eq_self_of_mem_aroots {g : ℕ} [Fact g.Prime] {P : (ZMod g)[X]} (hP : Irreducible P)
    {x : AlgebraicClosure (ZMod g)} (hx : x ∈ P.aroots (AlgebraicClosure (ZMod g))) :
    x ^ (g ^ P.natDegree) = x := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have : Fact (Irreducible P) := ⟨hP⟩
  have hxr : aeval x P = 0 := (Polynomial.mem_aroots.mp hx).2
  have : Module.Finite (ZMod g) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP0).finite
  have : Finite (AdjoinRoot P) := Module.finite_of_finite (ZMod g)
  let _ : Fintype (AdjoinRoot P) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot P) = g ^ P.natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, (AdjoinRoot.powerBasis hP0).finrank,
      AdjoinRoot.powerBasis_dim]
  have h := FiniteField.pow_card (AdjoinRoot.root P)
  rw [hcard] at h
  have hxr' : P.eval₂ (algebraMap (ZMod g) (AlgebraicClosure (ZMod g))) x = 0 := by
    rwa [aeval_def] at hxr
  have h' := congrArg (AdjoinRoot.lift (algebraMap (ZMod g) (AlgebraicClosure (ZMod g))) x hxr') h
  rwa [map_pow, AdjoinRoot.lift_root] at h'

theorem dvd_of_samePart_roots {g : ℕ} [Fact g.Prime] {P : (ZMod g)[X]} (hP : Irreducible P) (h0 : P.coeff 0 ≠ 0)
    {l : ℕ} (hl : l.Prime) {x y : AlgebraicClosure (ZMod g)} (hx : x ∈ P.aroots (AlgebraicClosure (ZMod g)))
    (hy : y ∈ P.aroots (AlgebraicClosure (ZMod g))) (hxy : x ≠ y) (hs : SamePart l x y) :
    2 ≤ P.natDegree ∧ l ∣ g ^ P.natDegree - 1 := by
  have hcard : (P.aroots (AlgebraicClosure (ZMod g))).card = P.natDegree :=
    IsAlgClosed.card_aroots_eq_natDegree
  have h2 : 2 ≤ P.natDegree := by
    rw [← hcard]
    have hsub : ({x, y} : Finset (AlgebraicClosure (ZMod g))) ⊆
        (P.aroots (AlgebraicClosure (ZMod g))).toFinset := by
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [Multiset.mem_toFinset]
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    calc 2 = ({x, y} : Finset (AlgebraicClosure (ZMod g))).card := (Finset.card_pair hxy).symm
      _ ≤ (P.aroots (AlgebraicClosure (ZMod g))).toFinset.card := Finset.card_le_card hsub
      _ ≤ (P.aroots (AlgebraicClosure (ZMod g))).card := Multiset.toFinset_card_le _
  refine ⟨h2, ?_⟩
  have hgp : g.Prime := Fact.out
  have hx0 := root_ne_zero h0 hx
  have hy0 := root_ne_zero h0 hy
  have hM0 : g ^ P.natDegree - 1 ≠ 0 := by
    have : 2 ≤ g ^ P.natDegree := le_trans hgp.two_le (Nat.le_self_pow (by omega) g)
    omega
  have hpow : ∀ z ∈ P.aroots (AlgebraicClosure (ZMod g)), z ≠ 0 → z ^ (g ^ P.natDegree - 1) = 1 := by
    intro z hz hz0
    have h := pow_card_pow_natDegree_eq_self_of_mem_aroots hP hz
    have hg1 : 1 ≤ g ^ P.natDegree := Nat.one_le_pow _ _ hgp.pos
    apply mul_left_cancel₀ hz0
    rw [← pow_succ', Nat.sub_add_cancel hg1, h, mul_one]
  by_contra hnd
  have hcop : (g ^ P.natDegree - 1).Coprime l :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).mpr hnd)
  obtain ⟨a, ha⟩ := (samePart_iff_of_ne_zero hl hx0 hy0).mp hs
  exact hxy (eq_of_pow_eq hcop (hpow x hx hx0) (hpow y hy hy0) hM0 ha)

theorem card_primeFactors_pow_sub_one_le {g d : ℕ} (hg : 2 ≤ g) (hd : 1 ≤ d) :
    ((g ^ d - 1).primeFactors.card : ℝ) ≤ d * Real.logb 2 g := by
  have hgd : 2 ≤ g ^ d := le_trans hg (Nat.le_self_pow (by omega) g)
  have hn0 : 0 < g ^ d - 1 := by omega
  have h2k : 2 ^ (g ^ d - 1).primeFactors.card ≤ g ^ d := by
    calc 2 ^ (g ^ d - 1).primeFactors.card ≤ ∏ p ∈ (g ^ d - 1).primeFactors, p :=
          Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ g ^ d - 1 := Nat.le_of_dvd hn0 (Nat.prod_primeFactors_dvd _)
      _ ≤ g ^ d := Nat.sub_le _ _
  have hreal : (2 : ℝ) ^ (((g ^ d - 1).primeFactors.card : ℕ) : ℝ) ≤ (g : ℝ) ^ d := by
    rw [Real.rpow_natCast]
    exact_mod_cast h2k
  have hgpos : (0 : ℝ) < (g : ℝ) ^ d := pow_pos (by exact_mod_cast (by omega : 0 < g)) d
  have := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hgpos).mpr hreal
  rwa [Real.logb_pow] at this

theorem sum_mul_pow_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 8) (N : ℕ) :
    ∑ d ∈ Finset.Icc 2 N, (d : ℝ) * u ^ d ≤ 6 * u ^ 2 := by
  have hIcc : Finset.Icc 2 N = Finset.Ico 2 (N + 1) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  calc ∑ k ∈ Finset.range (N + 1 - 2), ((2 + k : ℕ) : ℝ) * u ^ (2 + k)
      ≤ ∑ k ∈ Finset.range (N + 1 - 2), 3 * u ^ 2 * (1 / 2 : ℝ) ^ k := by
        apply Finset.sum_le_sum
        intro k _
        have hk : ((2 + k : ℕ) : ℝ) ≤ 3 * 4 ^ k := by
          have h1 : k < 4 ^ k := Nat.lt_pow_self (by norm_num)
          have h2 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
          exact_mod_cast (by omega : 2 + k ≤ 3 * 4 ^ k)
        have hu : u ^ k ≤ (1 / 8 : ℝ) ^ k := pow_le_pow_left₀ h0 h1 k
        calc ((2 + k : ℕ) : ℝ) * u ^ (2 + k) = ((2 + k : ℕ) : ℝ) * u ^ k * u ^ 2 := by ring
          _ ≤ (3 * 4 ^ k) * (1 / 8 : ℝ) ^ k * u ^ 2 := by gcongr
          _ = 3 * u ^ 2 * (1 / 2 : ℝ) ^ k := by
            rw [show (1 / 2 : ℝ) = 4 * (1 / 8) by norm_num, mul_pow]
            ring
    _ = 3 * u ^ 2 * ∑ k ∈ Finset.range (N + 1 - 2), (1 / 2 : ℝ) ^ k := by rw [Finset.mul_sum]
    _ ≤ 3 * u ^ 2 * 2 := by
        gcongr
        exact sum_geometric_two_le _
    _ = 6 * u ^ 2 := by ring

theorem mass_samePart_one_factor : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 2 ^ 12 ≤ g → (mass g N fun f => ∃ l : ℕ, l.Prime ∧ ¬ BB g N l ∧ ∃ P : (ZMod g)[X], P.Monic ∧ Irreducible P ∧ P ∣ f ∧ ∃ x ∈ P.aroots (AlgebraicClosure (ZMod g)), ∃ y ∈ P.aroots (AlgebraicClosure (ZMod g)), x ≠ y ∧ SamePart l x y) ≤ 12 * Real.logb 2 g / Real.sqrt g := by
  intro g _ N hg
  have hg2 : 2 ≤ g := le_trans (by norm_num) hg
  obtain ⟨-, -, hunion, -⟩ := GlobalTheory.T.squarefreeLabelTorusMass_union_bounds g N
  obtain ⟨S, hS⟩ : ∃ S : ℕ → ℕ → Finset (ZMod g)[X], S = fun d l => (sqSet g d).filter fun P =>
      Irreducible P ∧ ∃ x ∈ P.aroots (AlgebraicClosure (ZMod g)),
        ∃ y ∈ P.aroots (AlgebraicClosure (ZMod g)), x ≠ y ∧ SamePart l x y := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℕ → Finset ℕ,
      L = fun d => (g ^ d - 1).primeFactors.filter fun l => ¬ BB g N l := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (g : ℝ) ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
  have hgpos : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hr0 : 0 < r := hr ▸ Real.rpow_pos_of_pos hgpos _
  have hr4 : r ^ 4 = g := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hgpos.le]
    norm_num
  have hr8 : 8 ≤ r := by
    by_contra h
    have h1 : r ^ 4 < 8 ^ 4 := pow_lt_pow_left₀ (lt_of_not_ge h) hr0.le (by norm_num)
    have h2' : 4096 ≤ g := by simpa using hg
    have h2 : (4096 : ℝ) ≤ (g : ℝ) := by exact_mod_cast h2'
    norm_num at h1
    linarith
  have hlog : 0 ≤ Real.logb 2 g :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ g))
  have hstep3 : ∀ d ∈ Finset.Icc 2 N, ∀ l ∈ L d, mass g N (fun f => ∃ P ∈ S d l, P ∣ f) ≤
      (g : ℝ) ^ ((3 * d : ℝ) / 4) * (((g ^ d - 1 : ℕ) : ℝ))⁻¹ := by
    intro d hd l hl
    rw [Finset.mem_Icc] at hd
    simp only [hL, Finset.mem_filter, Nat.mem_primeFactors] at hl
    calc mass g N (fun f => ∃ P ∈ S d l, P ∣ f)
        ≤ ∑ P ∈ S d l, mass g N (fun f => P ∣ f) :=
          hunion _ (S d l) _ (fun P f => P ∣ f) (fun f _ hf => hf)
      _ ≤ ∑ P ∈ S d l, (((g ^ d - 1 : ℕ) : ℝ))⁻¹ := by
          apply Finset.sum_le_sum
          intro P hP
          simp only [hS, Finset.mem_filter] at hP
          have h1 := (GlobalTheory.T.squarefreeLabelTorusMass_divisor_bound g).2 N d P hP.1
          rw [torusCard_irreducible hP.2.1, (mem_sqSet.mp hP.1).2.1] at h1
          exact h1
      _ = ((S d l).card : ℝ) * (((g ^ d - 1 : ℕ) : ℝ))⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (g : ℝ) ^ ((3 * d : ℝ) / 4) * (((g ^ d - 1 : ℕ) : ℝ))⁻¹ := by
          gcongr
          have := GlobalTheory.T.card_irreducible_samePrimeToPart_roots_le g N d l hd.1 hd.2 hl.1.1 hl.2
          rw [hS]
          exact this
  have hstep2 : ∀ d ∈ Finset.Icc 2 N, mass g N (fun f => ∃ l ∈ L d, ∃ P ∈ S d l, P ∣ f) ≤
      ((d : ℝ) * Real.logb 2 g) * ((g : ℝ) ^ ((3 * d : ℝ) / 4) * (((g ^ d - 1 : ℕ) : ℝ))⁻¹) := by
    intro d hd
    have hd' := Finset.mem_Icc.mp hd
    calc mass g N (fun f => ∃ l ∈ L d, ∃ P ∈ S d l, P ∣ f)
        ≤ ∑ l ∈ L d, mass g N (fun f => ∃ P ∈ S d l, P ∣ f) :=
          hunion _ (L d) _ (fun l f => ∃ P ∈ S d l, P ∣ f) (fun f _ hf => hf)
      _ ≤ ∑ l ∈ L d, (g : ℝ) ^ ((3 * d : ℝ) / 4) * (((g ^ d - 1 : ℕ) : ℝ))⁻¹ :=
          Finset.sum_le_sum (hstep3 d hd)
      _ = ((L d).card : ℝ) * ((g : ℝ) ^ ((3 * d : ℝ) / 4) * (((g ^ d - 1 : ℕ) : ℝ))⁻¹) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((d : ℝ) * Real.logb 2 g) * ((g : ℝ) ^ ((3 * d : ℝ) / 4) * (((g ^ d - 1 : ℕ) : ℝ))⁻¹) := by
          gcongr
          calc ((L d).card : ℝ) ≤ ((g ^ d - 1).primeFactors.card : ℝ) := by
                exact_mod_cast Finset.card_le_card (by rw [hL]; exact Finset.filter_subset _ _)
            _ ≤ d * Real.logb 2 g := card_primeFactors_pow_sub_one_le hg2 (by omega)
  have hstep1 : (mass g N fun f => ∃ l : ℕ, l.Prime ∧ ¬ BB g N l ∧ ∃ P : (ZMod g)[X], P.Monic ∧
      Irreducible P ∧ P ∣ f ∧ ∃ x ∈ P.aroots (AlgebraicClosure (ZMod g)),
        ∃ y ∈ P.aroots (AlgebraicClosure (ZMod g)), x ≠ y ∧ SamePart l x y) ≤
      ∑ d ∈ Finset.Icc 2 N, mass g N (fun f => ∃ l ∈ L d, ∃ P ∈ S d l, P ∣ f) := by
    apply hunion
    rintro f hf ⟨l, hl, hBB, P, hPm, hPi, hPf, x, hx, y, hy, hxy, hs⟩
    have hfm := mem_sqSet.mp hf
    have hP0 : P.coeff 0 ≠ 0 := by
      intro h0
      exact hfm.2.2.2 (Polynomial.X_dvd_iff.mp (dvd_trans (Polynomial.X_dvd_iff.mpr h0) hPf))
    obtain ⟨hd2, hldvd⟩ := dvd_of_samePart_roots hPi hP0 hl hx hy hxy hs
    have hdN : P.natDegree ≤ N := hfm.2.1 ▸ Polynomial.natDegree_le_of_dvd hPf hfm.1.ne_zero
    refine ⟨P.natDegree, Finset.mem_Icc.mpr ⟨hd2, hdN⟩, l, ?_, P, ?_, hPf⟩
    · simp only [hL, Finset.mem_filter, Nat.mem_primeFactors]
      refine ⟨⟨hl, hldvd, ?_⟩, hBB⟩
      have : 2 ≤ g ^ P.natDegree := le_trans hg2 (Nat.le_self_pow (by omega) g)
      omega
    · simp only [hS, Finset.mem_filter]
      exact ⟨mem_sqSet.mpr ⟨hPm, rfl, hPi.squarefree, hP0⟩, hPi, x, hx, y, hy, hxy, hs⟩
  have hE : ∀ d ∈ Finset.Icc 2 N,
      (g : ℝ) ^ ((3 * d : ℝ) / 4) * (((g ^ d - 1 : ℕ) : ℝ))⁻¹ ≤ 2 * r⁻¹ ^ d := by
    intro d hd
    have hd' := Finset.mem_Icc.mp hd
    have h1 : (g : ℝ) ^ ((3 * d : ℝ) / 4) = (r ^ d) ^ 3 := by
      rw [hr, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hgpos.le]
      congr 1
      push_cast
      ring
    have h2 : (((g ^ d - 1 : ℕ) : ℝ)) = (r ^ d) ^ 4 - 1 := by
      have : 1 ≤ g ^ d := Nat.one_le_pow _ _ (by omega)
      rw [Nat.cast_sub this, Nat.cast_pow, Nat.cast_one, ← hr4, ← pow_mul, ← pow_mul, mul_comm]
    have hR : 8 ≤ r ^ d := le_trans hr8 (le_self_pow₀ (by linarith) (by omega))
    rw [h1, h2, inv_pow]
    generalize r ^ d = R at hR ⊢
    have h4 : (8 : ℝ) ^ 4 ≤ R ^ 4 := pow_le_pow_left₀ (by norm_num) hR 4
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  calc _ ≤ ∑ d ∈ Finset.Icc 2 N, mass g N (fun f => ∃ l ∈ L d, ∃ P ∈ S d l, P ∣ f) := hstep1
    _ ≤ ∑ d ∈ Finset.Icc 2 N, ((d : ℝ) * Real.logb 2 g) *
          ((g : ℝ) ^ ((3 * d : ℝ) / 4) * (((g ^ d - 1 : ℕ) : ℝ))⁻¹) := Finset.sum_le_sum hstep2
    _ ≤ ∑ d ∈ Finset.Icc 2 N, 2 * Real.logb 2 g * ((d : ℝ) * r⁻¹ ^ d) := by
        apply Finset.sum_le_sum
        intro d hd
        calc ((d : ℝ) * Real.logb 2 g) * ((g : ℝ) ^ ((3 * d : ℝ) / 4) * (((g ^ d - 1 : ℕ) : ℝ))⁻¹)
            ≤ ((d : ℝ) * Real.logb 2 g) * (2 * r⁻¹ ^ d) :=
              mul_le_mul_of_nonneg_left (hE d hd) (mul_nonneg (Nat.cast_nonneg _) hlog)
          _ = 2 * Real.logb 2 g * ((d : ℝ) * r⁻¹ ^ d) := by ring
    _ = 2 * Real.logb 2 g * ∑ d ∈ Finset.Icc 2 N, (d : ℝ) * r⁻¹ ^ d := by rw [Finset.mul_sum]
    _ ≤ 2 * Real.logb 2 g * (6 * r⁻¹ ^ 2) := by
        gcongr
        refine sum_mul_pow_le (inv_nonneg.mpr hr0.le) ?_ N
        rw [one_div]
        exact inv_anti₀ (by norm_num) hr8
    _ = 12 * Real.logb 2 g / Real.sqrt g := by
        have hsq : Real.sqrt g = r ^ 2 := by
          rw [← hr4, show r ^ 4 = (r ^ 2) ^ 2 by ring]
          exact Real.sqrt_sq (by positivity)
        rw [hsq]
        field_simp
        ring

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPeriodicCotEqQExpansionFourier
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.CotQExp

theorem hasSum_pi_cot (w : ℂ) (hw : 0 < w.im) :
    HasSum (fun m : ℕ => -2 * π * Complex.I * cexp (2 * π * Complex.I * w) ^ (m + 1))
      (π * Complex.cot (π * w) + π * Complex.I) := by
  have h : (π : ℂ) * Complex.cot (π * w) =
      π * Complex.I - 2 * π * Complex.I * ∑' n : ℕ, cexp (2 * π * Complex.I * w) ^ n :=
    pi_mul_cot_pi_q_exp (⟨w, hw⟩ : ℍ)
  have hq : ‖cexp (2 * π * Complex.I * w)‖ < 1 :=
    UpperHalfPlane.norm_exp_two_pi_I_lt_one (⟨w, hw⟩ : ℍ)
  have hs : Summable fun n : ℕ => cexp (2 * π * Complex.I * w) ^ n :=
    summable_geometric_of_norm_lt_one hq
  have hs1 : Summable fun n : ℕ => cexp (2 * π * Complex.I * w) ^ (n + 1) :=
    (summable_nat_add_iff 1).2 hs
  have h2 := hs1.hasSum.mul_left (-2 * π * Complex.I)
  have e : (π : ℂ) * Complex.cot (π * w) + π * Complex.I =
      -2 * π * Complex.I * ∑' n : ℕ, cexp (2 * π * Complex.I * w) ^ (n + 1) := by
    rw [h, hs.tsum_eq_zero_add]
    ring
  rw [e]
  exact h2

theorem sum_cot_eq_qexp : ∀ (L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 0 < L → 0 < z.im → hat φ 0 = 0 →
    ∑ r ∈ Finset.range L, φ r * (π / L * Complex.cot (π * ((z + r) / L))) =
      -2 * π * Complex.I / L *
        ∑' m : ℕ, hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L) := by
  intro L φ z hL hz h0
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hsum0 : ∑ r ∈ Finset.range L, φ r = 0 := by
    simpa [hat] using h0
  have him : ∀ r : ℕ, 0 < ((z + r) / L : ℂ).im := by
    intro r
    rw [Complex.div_natCast_im]
    simpa using div_pos hz hLr
  have hs := hasSum_sum (s := Finset.range L)
    (fun r _ => (hasSum_pi_cot _ (him r)).mul_left (φ r / L))
  rw [← tsum_mul_left]
  have e1 : ∑ r ∈ Finset.range L, φ r * (π / L * Complex.cot (π * ((z + r) / L))) =
      ∑ r ∈ Finset.range L, φ r / L * (π * Complex.cot (π * ((z + r) / L)) + π * Complex.I) := by
    have : ∑ r ∈ Finset.range L, φ r / L * (π * Complex.cot (π * ((z + r) / L)) + π * Complex.I)
        = ∑ r ∈ Finset.range L, φ r * (π / L * Complex.cot (π * ((z + r) / L)))
          + (∑ r ∈ Finset.range L, φ r) * (π * Complex.I / L) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    rw [this, hsum0, zero_mul, add_zero]
  rw [e1, ← hs.tsum_eq]
  refine tsum_congr fun m => ?_
  rw [hat, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Complex.exp_nat_mul, mul_assoc (φ r), ← Complex.exp_add]
  have e2 : ((m + 1 : ℕ) : ℂ) * (2 * π * Complex.I * ((z + r) / L)) =
      2 * π * Complex.I * (r * (((m + 1 : ℕ) : ℤ) : ℂ)) / L
        + 2 * π * Complex.I * (m + 1 : ℕ) * z / L := by
    push_cast
    ring
  rw [e2]
  ring

end GlobalTheory.CotQExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumSlashHeckeRepLowerLevelEqPowMulHeckeV
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem qExpansionFunction_coeffHeckeVOperator_eq_tsum (l : ℕ) (hl : 0 < l) (a : ℕ → ℂ) (τ : ℍ) :
    qs (Vo l a) τ = ∑' m : ℕ, a m * cexp (2 * π * Complex.I * m * ((l : ℂ) * τ)) := by
  unfold qs Vo
  have hinj : Function.Injective (fun m : ℕ => l * m) := fun x y h => by
    simpa [hl.ne'] using h
  rw [← hinj.tsum_eq]
  · congr 1; ext m
    simp only [dvd_mul_right, if_true, Nat.mul_div_cancel_left m hl]
    congr 2; push_cast; ring
  · intro n hn
    by_cases h : l ∣ n
    · obtain ⟨m, rfl⟩ := h; exact ⟨m, rfl⟩
    · simp [Function.mem_support, h] at hn

theorem adjU_sum (k N l : ℕ) (ε : DirichletCharacter ℂ N) (h : ℕ → ℂ) (hk : 1 ≤ k) (hl : 0 < l)
    (hf : MF k N (ch ε) h) (τ : ℍ) :
    ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ = (l : ℂ) ^ k * qs (Vo l h) τ := by
  have hlC : (0 : ℝ) < l := by exact_mod_cast hl
  let τ' : ℍ := ⟨(l : ℂ) * τ, by simpa using mul_pos hlC τ.im_pos⟩
  have hτ' : (τ' : ℂ) = (l : ℂ) * τ := rfl
  have key : ∀ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ = (l : ℂ) ^ (k - 1) * qs h τ' := by
    intro j
    let γ : SL(2, ℤ) := ⟨!![1, 0; (N * (j : ℕ) : ℤ), 1], by simp [Matrix.det_fin_two]⟩
    have hγ := hf.2 γ (by simp [γ]) τ'
    have hpt : ((γ • τ' : ℍ) : ℂ) = ((l : ℂ) * τ) / (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) := by
      rw [coe_specialLinearGroup_apply]; simp [γ, hτ']; ring
    have hden : ((((N * (j : ℕ) : ℤ)) : ℂ) * (τ' : ℂ) + 1) = (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) := by
      rw [hτ']; push_cast; ring
    have hne : (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp at this
      rcases this with h1 | h1
      · have h2 : N * l * (j : ℕ) = 0 := by rcases h1 with (h1 | h1) | h1 <;> simp [h1]
        simp [h2] at h0
      · exact (τ.im_pos.ne' h1)
    have hγ' : qs h (γ • τ') = (((N * l * (j : ℕ) : ℕ) : ℂ) * τ + 1) ^ k * qs h τ' := by
      rw [← hden, hγ]; simp [γ, ch]
    have harg : ((l : ℂ) * τ / ((N : ℂ) * l * ((j : ℕ) : ℂ) * τ + 1)) = ((γ • τ' : ℍ) : ℂ) := by
      rw [hpt]; push_cast; ring
    unfold slz repL
    simp [Matrix.det_fin_two]
    rw [harg, ofComplex_apply, hγ']
    push_cast at hne ⊢
    field_simp
  simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [qExpansionFunction_coeffHeckeVOperator_eq_tsum l hl h τ]
  have hp : (l : ℂ) * (l : ℂ) ^ (k - 1) = (l : ℂ) ^ k := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  rw [← mul_assoc, hp]
  rfl
end GlobalTheory.EisM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableCardDivisorsSqDivOneAddRpow
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.DivSq

theorem four_factors {n x y : ℕ} (hx : x ∣ n) (hy : y ∣ n) (hn : n ≠ 0) :
    ∃ a b c e : ℕ, a * b * c * e = n ∧ a * b = x ∧ a * c = y := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hn (by simpa using hx)
  obtain ⟨e, he⟩ := Nat.lcm_dvd hx hy
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_left x y
  obtain ⟨c, hc⟩ := Nat.gcd_dvd_right x y
  refine ⟨Nat.gcd x y, b, c, e, ?_, hb.symm, hc.symm⟩
  have hg : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hx0)
  have h1 := Nat.gcd_mul_lcm x y
  have h2 : Nat.gcd x y * b * c = Nat.lcm x y := by
    apply Nat.eq_of_mul_eq_mul_left hg
    rw [h1]
    calc Nat.gcd x y * (Nat.gcd x y * b * c) = (Nat.gcd x y * b) * (Nat.gcd x y * c) := by ring
      _ = x * y := by rw [← hb, ← hc]
  rw [h2, ← he]

theorem inv_rpow_natCast_mul (p : ℝ) (a b : ℕ) :
    ((((a * b : ℕ)) : ℝ) ^ p)⁻¹ = ((a : ℝ) ^ p)⁻¹ * ((b : ℝ) ^ p)⁻¹ := by
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity), mul_inv]

theorem sum_range_le_pow (p : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ p
      ≤ (∑ n ∈ Finset.range N, ((n : ℝ) ^ p)⁻¹) ^ 4 := by
  classical
  set I := Finset.range N with hI
  let φ : ℕ × ℕ × ℕ × ℕ → (Σ _ : ℕ, ℕ × ℕ) :=
    fun q => ⟨q.1 * q.2.1 * q.2.2.1 * q.2.2.2, q.1 * q.2.1, q.1 * q.2.2.1⟩
  let w : (Σ _ : ℕ, ℕ × ℕ) → ℝ := fun s => ((s.1 : ℝ) ^ p)⁻¹
  have hw : ∀ s, 0 ≤ w s := fun s => by simp only [w]; positivity
  have h1 : ∑ n ∈ I, ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ p
      = ∑ s ∈ I.sigma (fun n => n.divisors ×ˢ n.divisors), w s := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [w, Finset.sum_const, Finset.card_product, nsmul_eq_mul]
    push_cast
    ring
  have h2 : I.sigma (fun n => n.divisors ×ˢ n.divisors) ⊆ (I ×ˢ I ×ˢ I ×ˢ I).image φ := by
    rintro ⟨n, x, y⟩ hs
    simp only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisors, hI, Finset.mem_range] at hs
    obtain ⟨hnN, ⟨hx, hn⟩, hy, -⟩ := hs
    obtain ⟨a, b, c, e, rfl, rfl, rfl⟩ := four_factors hx hy hn
    have key : ∀ d, d ∣ a * b * c * e → d ∈ I := fun d hd => by
      rw [hI, Finset.mem_range]
      exact lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) hnN
    refine Finset.mem_image.2 ⟨(a, b, c, e), ?_, rfl⟩
    simp only [Finset.mem_product]
    exact ⟨key _ ⟨b * c * e, by ring⟩, key _ ⟨a * c * e, by ring⟩, key _ ⟨a * b * e, by ring⟩,
      key _ ⟨a * b * c, by ring⟩⟩
  have h3 : ∑ s ∈ (I ×ˢ I ×ˢ I ×ˢ I).image φ, w s ≤ ∑ q ∈ I ×ˢ I ×ˢ I ×ˢ I, w (φ q) :=
    Finset.sum_image_le_of_nonneg (fun s _ => hw s)
  have h4 : ∑ q ∈ I ×ˢ I ×ˢ I ×ˢ I, w (φ q) = (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) ^ 4 := by
    have : (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) ^ 4 = (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) *
      ((∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) * ((∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) * (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹))) := by
      ring
    rw [this]
    rw [Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_product, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_product, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [w, φ]
    rw [inv_rpow_natCast_mul, inv_rpow_natCast_mul, inv_rpow_natCast_mul]
    ring
  rw [h1, ← h4]
  exact (Finset.sum_le_sum_of_subset_of_nonneg h2 fun s _ _ => hw s).trans h3

theorem summable_card_divisors_sq_div_rpow :
    ∀ s : ℝ, 0 < s → Summable fun n : ℕ => ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ (1 + s) := by
  intro s hs
  have hz : Summable fun n : ℕ => ((n : ℝ) ^ (1 + s))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  refine summable_of_sum_range_le (c := (∑' n : ℕ, ((n : ℝ) ^ (1 + s))⁻¹) ^ 4)
    (fun n => by positivity) fun N => ?_
  refine (sum_range_le_pow (1 + s) N).trans ?_
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => by positivity)
    (hz.sum_le_tsum _ fun n _ => by positivity) 4

end GlobalTheory.DivSq
end

