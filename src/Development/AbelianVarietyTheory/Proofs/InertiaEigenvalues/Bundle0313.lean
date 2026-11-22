import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0097
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0109
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0101
import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0296
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0298
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0289
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0263
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0261
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCongruenceFiltrationGaloisRep
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory

theorem congrFilt_le_all_eq_zero (l : ℕ) [hl : Fact l.Prime] (x : ℝ) (hx0 : 0 ≤ x)
    (h : ∀ k : ℕ, x ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) : x = 0 := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  by_contra hne
  have hpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hne)
  have hinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hpos hinv
  have h1 : (l : ℝ) ^ (-((k : ℤ) + 2)) ≤ (l : ℝ) ^ (-(k : ℤ)) :=
    zpow_le_zpow_right₀ hl1.le (by omega)
  have h2 : (l : ℝ) ^ (-(k : ℤ)) = ((l : ℝ)⁻¹) ^ k := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  linarith [h k]

theorem congrFiltration : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]), (∀ i j, Continuous fun g => (ρ g : Matrix n n ℚ_[l]) i j) → ∃ N : ℕ → Subgroup ↥(GK K), (∀ k g, g ∈ N k ↔ ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) ∧ Antitone N ∧ (∀ k, IsOpen (N k : Set ↥(GK K))) ∧ (∀ k g, g ∈ N k → g ^ l ∈ N (k + 1)) ∧ (∀ k g, g ∈ N 0 → g ^ l ∈ N (k + 1) → g ∈ N k) ∧ ∀ g, (∀ k, g ∈ N k) → ρ g = 1 := by
  intro l _ n _ _ K ρ hcont
  obtain ⟨Γ, hΓ⟩ := GlobalTheory.T.exists_congruenceSubgroups_GL_padic l n
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
  have hmem : ∀ k g, g ∈ (Γ k).comap ρ ↔ ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) := by
    intro k g
    rw [Subgroup.mem_comap, hΓ]
  refine ⟨fun k => (Γ k).comap ρ, hmem, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab g hg
    rw [hmem] at hg ⊢
    intro i j
    have hab' : (a : ℤ) ≤ b := by exact_mod_cast hab
    exact le_trans (hg i j) (zpow_le_zpow_right₀ hl1 (by omega))
  · intro k
    have hset : (((Γ k).comap ρ : Subgroup ↥(GK K)) : Set ↥(GK K)) =
        ⋂ i, ⋂ j, (fun g => ((ρ g : Matrix n n ℚ_[l]) - 1) i j) ⁻¹'
          Metric.closedBall (0 : ℚ_[l]) ((l : ℝ) ^ (-((k : ℤ) + 2))) := by
      ext g
      simp only [SetLike.mem_coe, hmem, Set.mem_iInter, Set.mem_preimage, mem_closedBall_zero_iff]
    rw [hset]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    have hc : Continuous fun g => ((ρ g : Matrix n n ℚ_[l]) - 1) i j := by
      simp only [Matrix.sub_apply]
      exact (hcont i j).sub continuous_const
    exact (IsUltrametricDist.isOpen_closedBall (0 : ℚ_[l])
      (zpow_pos (by linarith) _).ne').preimage hc
  · intro k g hg
    rw [hmem] at hg ⊢
    have := GlobalTheory.T.norm_pow_prime_sub_one_le_of_norm_sub_one_le l n (ρ g : Matrix n n ℚ_[l]) k hg
    simpa [map_pow, Units.val_pow_eq_pow_val] using this
  · intro k g h0 hk
    rw [hmem] at h0 hk ⊢
    have h0' : ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-2 : ℤ) := by
      simpa using h0
    have hk' : ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) ^ l - 1) i j‖ ≤ (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) := by
      simpa [map_pow, Units.val_pow_eq_pow_val] using hk
    exact GlobalTheory.T.norm_sub_one_le_of_norm_pow_prime_sub_one_le l n _ k h0' hk'
  · intro g hg
    apply Units.ext
    ext i j
    have hz : ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ = 0 :=
      congrFilt_le_all_eq_zero l _ (norm_nonneg _) fun k => (hmem k g).1 (hg k) i j
    rw [norm_eq_zero, Matrix.sub_apply, sub_eq_zero] at hz
    simpa using hz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicFrobeniusTwistedValueEqPowMul
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

theorem cycVal_add {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ)
    (lam lam' : ℕ → ↥(K0 K)) (d d' : ↥(K0 K)) :
    cycVal P K s e (fun a => lam a + lam' a) (d + d') =
      cycVal P K s e lam d + cycVal P K s e lam' d' := by
  unfold cycVal
  simp only [map_add]
  push_cast
  simp only [add_mul, Finset.sum_add_distrib, mul_add]
  ring

theorem cycVal_neg {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ)
    (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)) :
    cycVal P K s e (fun a => -lam a) (-d) = -cycVal P K s e lam d := by
  unfold cycVal
  simp only [map_neg]
  push_cast
  simp only [neg_mul, Finset.sum_neg_distrib, mul_neg]
  ring

theorem cycVal_zero {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ) :
    cycVal P K s e (fun _ => 0) 0 = 0 := by
  simp [cycVal]

theorem exists_cycVal_eq_pow_mul (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e : ℕ)
    (hs : 1 ≤ s) (α : Om l) (hα : α ∈ Ks K s) (hn : ‖α‖ ≤ 1) :
    ∃ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) ∧ ‖(d : Om l)‖ ≤ 1 ∧
      d - (l : ↥(K0 K)) ^ e * frK P K d = (frK P K ^ s) (∑ a ∈ primeTo l s, lam a) ∧
      cycVal P K s e lam d = (l : Om l) ^ ((e + 1) * (s - 1)) * α := by
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hsum := GlobalTheory.ExpImage.Values.sum_zeta P
  have hgeom : ∑ r ∈ Finset.range l, P.ζQ 1 ^ r = 0 := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), hsum]
    simp
  have hpow : P.ζQ 1 ^ l = 1 := by
    have h := geom_sum_mul (P.ζQ 1) l
    rw [hgeom, zero_mul] at h
    exact (sub_eq_zero.mp h.symm)
  have h0 : P.ζQ 0 = 1 := by
    have h := GlobalTheory.ExpImage.Values.zeta_pow P 0 1
    simpa [hpow] using h.symm
  have h1 : P.ζQ 1 ≠ 1 := by
    intro h
    rw [h] at hsum
    have hc : ((l - 1 : ℕ) : Om l) = -1 := by simpa using hsum
    have hz : ((l : ℕ) : Om l) = 0 := by
      push_cast [Nat.cast_sub hl1.le] at hc
      linear_combination hc
    exact (Nat.cast_ne_zero.mpr (by omega : l ≠ 0)) hz
  have hchain : ∀ j, P.ζQ (j + 1) ^ l = P.ζQ j := fun j => by
    simpa using GlobalTheory.ExpImage.Values.zeta_pow P j 1
  have hmem := GlobalTheory.T.cyclotomicLevel_integers_mem_closure_levels l K P.ζQ h0 h1 hchain s hs α hα hn
  clear hα hn
  induction hmem using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, n, c, hj, hjs, hn', hc, hc1, rfl⟩ := hx
    exact GlobalTheory.T.exists_cyclotomicFrobeniusTwistedValue_eq l P K s e j n hj hjs hn' c hc hc1
  | zero =>
    refine ⟨fun _ => 0, 0, fun _ => by simp, by simp, by simp, ?_⟩
    rw [cycVal_zero, mul_zero]
  | add x y _ _ ihx ihy =>
    obtain ⟨lam, d, hlam, hd, hfr, hv⟩ := ihx
    obtain ⟨lam', d', hlam', hd', hfr', hv'⟩ := ihy
    refine ⟨fun a => lam a + lam' a, d + d', fun a => ?_, ?_, ?_, ?_⟩
    · push_cast
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hlam a) (hlam' a))
    · push_cast
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hd hd')
    · simp only [map_add, Finset.sum_add_distrib]
      rw [← hfr, ← hfr']
      ring
    · rw [cycVal_add, hv, hv']
      ring
  | neg x _ ih =>
    obtain ⟨lam, d, hlam, hd, hfr, hv⟩ := ih
    refine ⟨fun a => -lam a, -d, fun a => by simpa using hlam a, by simpa using hd, ?_, ?_⟩
    · simp only [map_neg, Finset.sum_neg_distrib]
      rw [← hfr]
      ring
    · rw [cycVal_neg, hv]
      ring

end GlobalTheory.ExpImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamElementOfCocycleRecursion
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.ExpImage.Sum

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem frob_π₁ : WittVector.frobenius AI.π₁ = AI.μ := by
  rw [LocAinf.π₁, LocAinf.μ, map_sub, map_one, WittVector.frobenius_eq_map_frobenius,
    WittVector.map_teichmuller]
  congr 2
  exact (frobeniusEquiv (OCb l) l).apply_symm_apply AI.ε

theorem act_μ {K : FinExt l} {h : GQ l} (hh : h ∈ Hinf K) : AI.actW h AI.μ = AI.μ := by
  have h1 : P.χQ h = 1 :=
    ((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K h (Hinf_le_fix hh)).2.mp hh
  have h2 := GlobalTheory.T.cyclotomic_action_on_root_tower l P AI h 1 (by rw [h1]; simp) 0
  have h3 : AI.actT h AI.ε = AI.ε := by simpa [LocAinf.εroot] using h2
  rw [LocAinf.μ, map_sub, map_one, LocAinf.actW, WittVector.map_teichmuller]
  congr 2

theorem step_dR (T : LocTied l P AI) {g : GQ l} {U : ℤ_[l]} {k : ℕ} {β r : Ainf l} {u : P.R.BdR}
    (hu : io AI AI.π₁ * u = 1) (h : Step AI g U AI.π₁ k β r) :
    qB P (U : ℚ_[l]) * P.actQdR g (io AI β * u ^ k) - io AI β * u ^ k = io AI r * u ^ k := by
  have e := congrArg (io AI) h
  simp only [map_sub, map_mul, map_pow, io_act, io_zl AI T] at e
  have h1 : io AI AI.π₁ ^ k * u ^ k = 1 := by rw [← mul_pow, hu, one_pow]
  have h2 : P.actQdR g (io AI AI.π₁) ^ k * P.actQdR g u ^ k = 1 := by
    rw [← mul_pow, ← map_mul, hu, map_one, one_pow]
  rw [map_mul, map_pow]
  linear_combination (u ^ k * P.actQdR g u ^ k) * e
    - (qB P (U : ℚ_[l]) * P.actQdR g (io AI β) * P.actQdR g u ^ k) * h1
    + (io AI β * u ^ k + io AI r * u ^ k) * h2

theorem limit (T : LocTied l P AI) {M : ℕ} (hM : 1 ≤ M) (g : GQ l) (U : ℤ_[l]) (b v : P.R.BdR)
    (S E : ℕ → P.R.BdR)
    (hb : ∀ n : ℕ, ∃ R₀ : ℕ, ∀ R ≥ R₀, b - S R ∈ Lat AI M n)
    (hE : ∀ n : ℕ, ∃ R₀ : ℕ, ∀ R ≥ R₀, E R ∈ Lat AI M n)
    (hS : ∀ R, ∃ z : ℤ_[l], v + (qB P (U : ℚ_[l]) * P.actQdR g (S R) - S R) = qB P (z : ℚ_[l]) - E R) :
    NearZ P M (v + (qB P (U : ℚ_[l]) * P.actQdR g b - b)) := by
  refine GlobalTheory.T.padicInt_add_fil_closed_in_deRhamPeriodRing l P AI T M hM _ fun n => ?_
  obtain ⟨R₀, h₀⟩ := hb n
  obtain ⟨R₁, h₁⟩ := hE n
  obtain ⟨z, hz⟩ := hS (max R₀ R₁)
  have a := h₀ _ (le_max_left R₀ R₁)
  have a' := h₁ _ (le_max_right R₀ R₁)
  refine ⟨z, ?_⟩
  have := add_mem (sub_mem a (qB_mul_mem_Lat AI T U (act_mem_Lat AI g a))) a'
  convert this using 1
  rw [map_sub]
  linear_combination -hz

theorem telescope (g : GQ l) (U : ℤ_[l]) (s : ℕ) (B H : ℕ → P.R.BdR)
    (h : ∀ k, ∃ z : ℤ_[l], qB P (U : ℚ_[l]) * P.actQdR g (B k) - B k =
      H k - (l : P.R.BdR) ^ s * H (k + 1) + qB P (z : ℚ_[l])) (R : ℕ) :
    ∃ z : ℤ_[l], -H 0 + (qB P (U : ℚ_[l]) *
        P.actQdR g (∑ k ∈ Finset.range R, (l : P.R.BdR) ^ (s * k) * B k) -
        ∑ k ∈ Finset.range R, (l : P.R.BdR) ^ (s * k) * B k) =
      qB P (z : ℚ_[l]) - (l : P.R.BdR) ^ (s * R) * H R := by
  induction R with
  | zero => exact ⟨0, by simp⟩
  | succ R ih =>
    obtain ⟨z, hz⟩ := ih
    obtain ⟨w, hw⟩ := h R
    refine ⟨z + (l : ℤ_[l]) ^ (s * R) * w, ?_⟩
    rw [Finset.sum_range_succ, map_add, map_mul, map_pow, map_natCast]
    rw [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast,
      map_add, map_mul, map_pow, map_natCast, mul_add s R 1, pow_add, mul_one]
    linear_combination hz + (l : P.R.BdR) ^ (s * R) * hw

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (g : GQ l) (U : ℤ_[l]) (M : ℕ), 1 ≤ M → ∀ y : Ainf l, Solv AI K s g U (y - WittVector.frobenius y) → ∃ b ∈ FilB P 0, (∀ h ∈ Hinf K, NearZ P M (P.actQdR h b - b)) ∧ NearZ P M (io AI y + (qB P (U : ℚ_[l]) * P.actQdR g b - b)) := by
  intro l _ P AI T K s hs g U M hM y ⟨p, q, hq0, hp, hstep⟩
  have asw := (GlobalTheory.ArtinSchreierWitt.main l).2.2
  choose β hβ using fun k : ℕ => asw (AI.ξ ^ (k + 1)) (p k)
  have hη' : ∀ k : ℕ, ∃ η : Ainf l, WittVector.frobenius η - AI.ξ ^ k * η = q k ∧ (k = 0 → η = -y) := by
    intro k
    rcases k with _ | k
    · exact ⟨-y, by rw [hq0, map_neg]; ring, fun _ => rfl⟩
    · obtain ⟨η, h⟩ := asw (AI.ξ ^ (k + 1)) (q (k + 1))
      exact ⟨η, h, fun h => absurd h (Nat.succ_ne_zero k)⟩
  choose η hη hη0 using hη'
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.T.exists_inv_io_pi_alt l P AI T
  have small := GlobalTheory.T.prime_pow_mul_inv_pow_mem_ainfFilLattice l P AI s hs u hu0 hu M
  obtain ⟨b, hb0, hb⟩ := GlobalTheory.T.exists_series_limit_Lat_alt l P AI M
    (fun k => (l : P.R.BdR) ^ (s * k) * (io AI (β k) * u ^ (k + 1)))
    (fun k => by
      have h1 : (l : P.R.BdR) ^ (s * k) * io AI (β k) ∈ FilB P 0 := by
        simpa using io_mem AI (((l : ℕ) : Ainf l) ^ (s * k) * β k)
      have h2 : u ^ (k + 1) ∈ FilB P 0 := by simpa using FilB_pow hu0 (k + 1)
      rw [← mul_assoc]
      exact FilB_zero_mul h1 h2)
    (fun n => by
      obtain ⟨k₀, h⟩ := small n
      exact ⟨k₀, fun k hk => by rw [← mul_assoc]; exact h k hk _⟩)
  have h1 : ∀ k, io AI AI.π₁ ^ k * u ^ k = 1 := fun k => by rw [← mul_pow, hu, one_pow]
  refine ⟨b, hb0, fun h hh => ?_, ?_⟩
  · have key : ∀ k, ∃ z : ℤ_[l], qB P ((1 : ℤ_[l]) : ℚ_[l]) * P.actQdR h (io AI (β k) * u ^ (k + 1)) -
        io AI (β k) * u ^ (k + 1) = (0 : P.R.BdR) - (l : P.R.BdR) ^ s * 0 + qB P (z : ℚ_[l]) := by
      intro k
      obtain ⟨z, hz⟩ := GlobalTheory.T.exists_ainfCocycleRecursion_of_frobenius_twist l P AI h 1 (k + 1) (β k) 0 (by
        rw [hβ]
        unfold Step
        rw [hp k h hh, act_μ AI hh]
        simp [mul_comm])
      refine ⟨z, ?_⟩
      rw [step_dR AI T hu hz, zero_add, map_mul, map_pow, io_zl AI T, mul_assoc, h1]
      ring
    have := limit AI T hM h 1 b 0 _ (fun _ => 0) hb (fun n => ⟨0, fun _ _ => zero_mem _⟩)
      (fun R => by
        simpa using telescope h 1 s (fun k => io AI (β k) * u ^ (k + 1)) (fun _ => 0) key R)
    simpa using this
  · have key : ∀ k, ∃ z : ℤ_[l], qB P (U : ℚ_[l]) * P.actQdR g (io AI (β k) * u ^ (k + 1)) -
        io AI (β k) * u ^ (k + 1) = io AI (η k) * u ^ k -
          (l : P.R.BdR) ^ s * (io AI (η (k + 1)) * u ^ (k + 1)) + qB P (z : ℚ_[l]) := by
      intro k
      obtain ⟨z, hz⟩ := GlobalTheory.T.exists_ainfCocycleRecursion_of_frobenius_twist l P AI g U (k + 1) (β k)
        (AI.π₁ * η k - ((l : ℕ) : Ainf l) ^ s * η (k + 1)) (by
        rw [hβ]
        convert hstep k using 1
        rw [← hη k, ← hη (k + 1), map_sub, map_mul, map_mul, map_pow, map_natCast, frob_π₁, AI.μ_eq]
        ring)
      refine ⟨z, ?_⟩
      rw [step_dR AI T hu hz]
      simp only [map_add, map_sub, map_mul, map_pow, map_natCast, io_zl AI T]
      linear_combination (io AI (η k) * u ^ k) * hu + qB P (z : ℚ_[l]) * h1 (k + 1)
    refine limit AI T hM g U b _ _ (fun R => (l : P.R.BdR) ^ (s * R) * (io AI (η R) * u ^ R)) hb
      (fun n => ?_) (fun R => ?_)
    · obtain ⟨k₀, h⟩ := small n
      refine ⟨k₀, fun R hR => ?_⟩
      convert h R hR (η R * AI.π₁) using 1
      rw [map_mul]
      linear_combination (-(l : P.R.BdR) ^ (s * R) * (io AI (η R) * u ^ R)) * hu
    · have := telescope g U s (fun k => io AI (β k) * u ^ (k + 1)) (fun k => io AI (η k) * u ^ k) key R
      simpa only [hη0 0 rfl, map_neg, pow_zero, mul_one, neg_neg] using this

end GlobalTheory.ExpImage.Sum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqOfExhaustive
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.FilCount

theorem exists_eq_of_exhaustive {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    (D : Submodule k M) [FiniteDimensional k D] (F : ℤ → Submodule k M) (hF : Antitone F)
    (hle : ∀ a, F a ≤ D) (hex : ∀ x ∈ D, ∃ a, x ∈ F a) : ∃ b : ℤ, ∀ a ≤ b, F a = D := by
  obtain ⟨s, hs⟩ : D.FG := (Submodule.fg_iff_finiteDimensional D).2 inferInstance
  have hsD : ∀ x ∈ s, x ∈ D := fun x hx => hs ▸ Submodule.subset_span hx
  choose! f hf using hex
  obtain ⟨b, hb⟩ := (s.image f).bddBelow
  refine ⟨b, fun a ha => le_antisymm (hle a) ?_⟩
  rw [← hs, Submodule.span_le]
  intro x hx
  have hbx : b ≤ f x := hb (Finset.mem_coe.2 (Finset.mem_image_of_mem f hx))
  exact hF (ha.trans hbx) (hf x (hsD x hx))

theorem telescope (d : ℤ → ℤ) (c : ℤ) (b : ℤ) (hb : ∀ a ≤ b, d a = c) (J : Finset ℤ)
    (hJ : ∀ a, a ∉ J → d a - d (a + 1) = 0) :
    c - d 0 = ∑ a ∈ J.filter (· < 0), (d a - d (a + 1)) := by
  have tel : ∀ n : ℕ, ∑ a ∈ Finset.Ico (-(n : ℤ)) 0, (d a - d (a + 1)) = d (-n) - d 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : Finset.Ico (-((n + 1 : ℕ) : ℤ)) 0
          = insert (-((n + 1 : ℕ) : ℤ)) (Finset.Ico (-(n : ℤ)) 0) := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_insert]
        push_cast
        omega
      rw [e, Finset.sum_insert (by simp only [Finset.mem_Ico]; push_cast; omega), ih]
      have e2 : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by push_cast; ring
      rw [e2]; ring
  obtain ⟨m, hm⟩ := J.bddBelow
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, -(n : ℤ) ≤ m ∧ -(n : ℤ) ≤ b :=
    ⟨m.natAbs + b.natAbs, by omega, by omega⟩
  rw [← hb _ hn2, ← tel n]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx
    exact Finset.mem_Ico.2 ⟨hn1.trans (hm (Finset.mem_coe.2 hx.1)), hx.2⟩
  · intro x hx hx'
    refine hJ x fun h => hx' (Finset.mem_filter.2 ⟨h, (Finset.mem_Ico.1 hx).2⟩)

section

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem tmul_mem_filV (a : ℤ) (v : V) (b : BdR) (hb : b ∈ PD.Fil a) :
    v ⊗ₜ[Qp] b ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨v ⊗ₜ[Qp] ⟨b, hb⟩, rfl⟩

theorem filV_antitone : Antitone (FilV PD (LL := LL) (V := V)) := by
  have hA : Antitone PD.Fil := antitone_int_of_succ_le PD.Fil_anti
  rintro a b hab _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul v c => exact tmul_mem_filV PD a v c.1 (hA hab c.2)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem filV_exhaustive (x : V ⊗[Qp] BdR) : ∃ a, x ∈ FilV PD (LL := LL) (V := V) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v c =>
    obtain ⟨a, ha⟩ := PD.Fil_exh c
    exact ⟨a, tmul_mem_filV PD a v c ha⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (filV_antitone PD (min_le_left a b) ha)
      (filV_antitone PD (min_le_right a b) hb)⟩

theorem codim_fil_zero (ρ : Representation LL G V) [FiniteDimensional LL ↥(DdR PD ρ)]
    (τ : K →ₐ[Qp] LL) (J : Finset ℤ) (hJ : ∀ a, a ∉ J → multV PD ρ τ a = 0) :
    (Module.finrank LL ↥(DdRE PD ρ τ) : ℤ) - Module.finrank LL ↥(FildR PD ρ τ 0)
      = ∑ a ∈ J.filter (· < 0), multV PD ρ τ a := by
  have : FiniteDimensional LL ↥(DdRE PD ρ τ) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left
  obtain ⟨b, hb⟩ := exists_eq_of_exhaustive (DdRE PD ρ τ) (FildR PD ρ τ)
    (fun a b hab => inf_le_inf_left _ (filV_antitone PD hab)) (fun a => inf_le_left)
    (fun x hx => (filV_exhaustive PD (LL := LL) x).imp fun a ha => ⟨hx, ha⟩)
  exact telescope (fun a => (Module.finrank LL ↥(FildR PD ρ τ a) : ℤ)) _ b
    (fun a ha => by rw [hb a ha]) J hJ

end

theorem fil_count : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
      [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)
      (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (J : Finset ℤ), (∀ a, a ∉ J → multV (P.PD K) ρ τ a = 0) →
      (Module.finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) : ℤ) - Module.finrank ↥LL.1 ↥(FildR (P.PD K) ρ τ 0)
        = ∑ a ∈ J.filter (· < 0), multV (P.PD K) ρ τ a := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ τ J hJ
  have := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ).1
  exact codim_fil_zero (P.PD K) ρ τ J hJ

end GlobalTheory.Per.FilCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionBlockPeriodMatrixSemistable
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem extPeriodMatrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (K : FinExt l) (ρ : ↥(GK K) →* GL (a ⊕ b) ↥(MaximalUnramifiedExtension l)) (ρ₁ : ↥(GK K) →* GL a ↥(MaximalUnramifiedExtension l)) (ρ₂ : ↥(GK K) →* GL b ↥(MaximalUnramifiedExtension l)) (c : ↥(GK K) → Matrix a b ↥(MaximalUnramifiedExtension l)), (∀ g, (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)) = Matrix.fromBlocks (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)) (c g) 0 (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l))) → ∀ (Q₁ : GL a (Bst P)) (Q₂ : GL b (Bst P)), (∀ g : ↥(GK K), (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₁ : Matrix a a (Bst P)).map (actSt P (g : GQ l)) = Q₁) → (∀ g : ↥(GK K), (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₂ : Matrix b b (Bst P)).map (actSt P (g : GQ l)) = Q₂) → ∀ v : a × b → Bst P, (∀ g : ↥(GK K), (fun i => ks P (extCoc ρ₂ c g i)) = ((homRep ρ₁ ρ₂ g : Matrix (a × b) (a × b) ↥(MaximalUnramifiedExtension l)).map (ks P)).mulVec (fun i => actSt P (g : GQ l) (v i)) - v) → ∃ Q : GL (a ⊕ b) (Bst P), ∀ g : ↥(GK K), (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix (a ⊕ b) (a ⊕ b) (Bst P)).map (actSt P (g : GQ l)) = Q := by
  intro l _ P a b _ _ _ _ K ρ ρ₁ ρ₂ c hρ Q₁ Q₂ h₁ h₂ v hv
  let β : Matrix a b (Bst P) := Matrix.of fun i j => v (i, j)
  have hvβ : v = vecM β := rfl
  let Qm : Matrix (a ⊕ b) (a ⊕ b) (Bst P) :=
    Matrix.fromBlocks (Q₁ : Matrix a a (Bst P)) (-(β * (Q₂ : Matrix b b (Bst P)))) 0 (Q₂ : Matrix b b (Bst P))
  let Qi : Matrix (a ⊕ b) (a ⊕ b) (Bst P) :=
    Matrix.fromBlocks ((Q₁⁻¹ : GL a (Bst P)) : Matrix a a (Bst P)) (((Q₁⁻¹ : GL a (Bst P)) : Matrix a a (Bst P)) * β) 0
      ((Q₂⁻¹ : GL b (Bst P)) : Matrix b b (Bst P))
  have hQ : Qm * Qi = 1 := by
    simp only [Qm, Qi, Matrix.fromBlocks_multiply, Units.mul_inv, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      ← Matrix.mul_assoc, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_assoc β, Units.mul_inv, Matrix.mul_one,
      add_neg_cancel, Matrix.fromBlocks_one]
  have hQ' : Qi * Qm = 1 := by
    simp only [Qm, Qi, Matrix.fromBlocks_multiply, Units.inv_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.mul_neg, ← Matrix.mul_assoc, neg_add_cancel, neg_zero, Matrix.fromBlocks_one]
  refine ⟨⟨Qm, Qi, hQ, hQ'⟩, fun g => ?_⟩
  set σ : Bst P →+* Bst P := (actSt P (g : GQ l)).toRingHom with hσ
  have hσc : ⇑(actSt P (g : GQ l)) = ⇑σ := rfl
  have hc : ((c g * (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l))).map (ks P)) =
      (ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * β.map σ * (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) - β := by
    apply vecM_injective
    have h := hv g
    rw [homRep_apply, hvβ] at h
    have e1 : (fun i => actSt P (g : GQ l) (vecM β i)) = vecM (β.map σ) := rfl
    rw [e1, homUnit_mulVec] at h
    exact h
  have hR : (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQ2 : (Q₂ : Matrix b b (Bst P)).map σ =
      (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q₂ : Matrix b b (Bst P)) := by
    calc (Q₂ : Matrix b b (Bst P)).map σ
        = ((((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) * (ρ₂ g : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P)) *
            (Q₂ : Matrix b b (Bst P)).map σ := by rw [hR, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc]; exact congrArg _ (h₂ g)
  have hC : (c g).map (ks P) * (Q₂ : Matrix b b (Bst P)).map σ =
      ((ρ₁ g : Matrix a a ↥(MaximalUnramifiedExtension l)).map (ks P) * β.map σ * (((ρ₂ g)⁻¹ : GL b ↥(MaximalUnramifiedExtension l)) : Matrix b b ↥(MaximalUnramifiedExtension l)).map (ks P) - β) *
        (Q₂ : Matrix b b (Bst P)) := by
    rw [hQ2, ← hc, Matrix.map_mul, Matrix.mul_assoc]
  show (ρ g : Matrix (a ⊕ b) (a ⊕ b) ↥(MaximalUnramifiedExtension l)).map (ks P) * Qm.map σ = Qm
  rw [hρ g]
  simp only [Qm, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.map_zero _ (map_zero _), Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add]
  have e1 := h₁ g
  have e2 := h₂ g
  rw [hσc] at e1 e2
  rw [e1, e2]
  congr 1
  rw [Matrix.map_neg _ (map_neg σ), Matrix.map_mul, hC, hQ2]
  simp only [Matrix.sub_mul, Matrix.mul_neg, Matrix.mul_assoc]
  abel

end GlobalTheory.PMon
end
end

