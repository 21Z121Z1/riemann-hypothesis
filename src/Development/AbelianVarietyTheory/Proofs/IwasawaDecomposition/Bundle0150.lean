import Mathlib
import Formalism.GL3MeanSquares.Bundle0001
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.CyclotomicNorms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanSqCardPrimeFactorsOutPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0124
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0137
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0139
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0038
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
import Formalism.LocalRingCardinality.DataCD
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0026
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0138
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0140
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplicativeWeightPrimeSum
section
open Finset ArithmeticFunction

namespace GlobalTheory.Mem.An

open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2

theorem squarefree_prod_primeFactors_filter (m : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Squarefree (∏ p ∈ m.primeFactors.filter P, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro p hp q hq hpq
    have hp' := Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1
    have hq' := Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hq).1
    exact Nat.coprime_iff_isRelPrime.1 ((Nat.coprime_primes hp' hq').2 hpq)
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).prime.squarefree

theorem inPart_dvd_modulus (m₀ m : ℕ) : inPart m₀ m ∣ m₀ := by
  unfold inPart
  refine Finset.prod_primes_dvd _ ?_ ?_
  · intro p hp
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).prime
  · intro p hp
    exact (Finset.mem_filter.1 hp).2.1

theorem outPart_coprime_modulus (m₀ m : ℕ) : Nat.Coprime (outPart m₀ m) m₀ := by
  unfold outPart
  refine Nat.Coprime.prod_left ?_
  intro p hp
  exact (Nat.Prime.coprime_iff_not_dvd
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1)).2 (Finset.mem_filter.1 hp).2.1

theorem outPart_le_self (m₀ m : ℕ) (hm : 0 < m) : outPart m₀ m ≤ m := by
  refine Nat.le_of_dvd hm ?_
  have h := GlobalTheory.inPart_mul_outPart_mul_sq m₀ m hm
  exact ((Dvd.intro_left _ rfl).mul_right _).trans (dvd_of_eq h)

theorem abs_sum_jacobiSym_le_outPart (m₀ a₀ m : ℕ) (S : Finset ℕ) (h8 : 8 ∣ m₀) (hm : 0 < m)
    (hS : ∀ q ∈ S, q % 4 = 3 ∧ q ≡ a₀ [MOD m₀] ∧ Nat.Coprime m q) :
    |∑ q ∈ S, (jacobiSym (m : ℤ) q : ℝ)| ≤ |∑ q ∈ S, (jacobiSym (q : ℤ) (outPart m₀ m) : ℝ)| := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨q₀, hq₀⟩
  · simp
  have hodd : ∀ q ∈ S, Odd q := fun q hq => by
    have := (hS q hq).1
    rw [Nat.odd_iff]; omega
  have hs : Odd (outPart m₀ m) := by
    have h2 : Nat.Coprime (outPart m₀ m) 2 :=
      (outPart_coprime_modulus m₀ m).coprime_dvd_right (Dvd.dvd.trans (by norm_num) h8)
    exact Nat.coprime_two_right.1 h2
  have key : ∀ q ∈ S, jacobiSym (m : ℤ) q =
      (jacobiSym (inPart m₀ m : ℤ) q₀ * (-1) ^ (outPart m₀ m / 2)) * jacobiSym (q : ℤ) (outPart m₀ m) := by
    intro q hq
    obtain ⟨h4, hc, hcop⟩ := hS q hq
    rw [GlobalTheory.jacobiInOut m₀ m q hm hcop,
      GlobalTheory.jacobiSym_const_on_class m₀ (inPart m₀ m) q q₀ h8 (inPart_dvd_modulus m₀ m)
        (squarefree_prod_primeFactors_filter _ _) (hodd q hq) (hodd q₀ hq₀) (hc.trans (hS q₀ hq₀).2.1.symm),
      jacobiSym.quadratic_reciprocity hs (hodd q hq), mul_comm (outPart m₀ m / 2), pow_mul,
      Odd.neg_one_pow (show Odd (q / 2) by rw [Nat.odd_iff]; omega), mul_assoc]
  rw [Finset.sum_congr rfl (fun q hq => by rw [key q hq, Int.cast_mul]), ← Finset.mul_sum, abs_mul]
  refine mul_le_of_le_one_left (abs_nonneg _) ?_
  push_cast
  rw [abs_mul, abs_neg_one_pow, mul_one]
  rcases jacobiSym.trichotomy (inPart m₀ m : ℤ) q₀ with h | h | h <;> simp [h]

theorem rpow_lt_of_mem_PP {x X : ℝ} {m₀ a₀ q : ℕ} (hx : Real.exp 1600 ≤ x) (h8 : 8 ≤ m₀) (hX : 0 < X)
    (h1 : (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X) (hq : q ∈ PP m₀ a₀ X) :
    x ^ (400 : ℝ) < q := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : 1600 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hm : 2 ≤ Real.log m₀ := by
    have h2 : Real.log 8 ≤ Real.log m₀ := Real.log_le_log (by norm_num) (by exact_mod_cast h8)
    have h3 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have hq1 : Real.sqrt X < q := by
    have := (Finset.mem_Ioc.1 (Finset.mem_filter.1 hq).1).1
    exact (Nat.floor_lt (Real.sqrt_nonneg X)).1 this
  refine lt_of_le_of_lt ?_ hq1
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hx0 _) (Real.sqrt_pos.2 hX), Real.log_rpow hx0,
    Real.log_sqrt hX.le]
  have h4 : Real.log x ^ 2 * 2 ≤ Real.log x ^ 2 * Real.log m₀ :=
    mul_le_mul_of_nonneg_left hm (sq_nonneg _)
  nlinarith

theorem meanSq_primes_residue_le : GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x₀ C : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ m₀ a₀ : ℕ, 8 ∣ m₀ → 0 < m₀ → Nat.Coprime a₀ m₀ → a₀ % 4 = 3 → (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (eps / 5) ∨ x ^ (400 : ℝ) < p) → ∀ X : ℝ, 0 < X → (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (eps / 6) ≤ Real.log X → ∀ κ : ℕ → ℂ, κ 1 = 1 → (∀ m n, κ (m * n) = κ m * κ n) → (∀ n, ‖κ n‖ ≤ 1) → (∑ p ∈ Formalism.HermitianLattices.GL2PrimeSums.PP m₀ a₀ X, ‖Formalism.HermitianLattices.GL2PrimeSums.sqSum x κ p‖ ^ 2) / (Formalism.HermitianLattices.GL2PrimeSums.PP m₀ a₀ X).card ≤ C * x * Real.log x := by
  intro hTZ hPage hZ eps he he'
  obtain ⟨x₁, C', c', hC', hc', hmu⟩ := GlobalTheory.T.squarefree_prime_sum_exceptional hTZ hPage hZ eps he he'
  obtain ⟨x₂, hcard⟩ := card_primes_residue_ge_rpow hTZ eps he he'
  obtain ⟨x₃, C, hcore⟩ :=
    GlobalTheory.meanSq_core sum_vonMangoldt_le_two_mul eps he (by linarith) C' c' hC' hc'
  refine ⟨max (max x₁ x₂) (max x₃ (Real.exp 1600)), C, ?_⟩
  intro x hx m₀ a₀ h8 hm hcop ha hpr X hX h1 h2 κ hκ1 hκm hκb
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx4
  have h8' : 8 ≤ m₀ := Nat.le_of_dvd hm h8
  obtain ⟨nStar, hn⟩ := hmu x hx1 m₀ a₀ h8 hm hcop X hX h1 h2
  have hc := hcard x hx2 m₀ a₀ (by omega) hcop X hX h1 h2
  have hpos : (0 : ℝ) < (PP m₀ a₀ X).card := lt_of_lt_of_le (Real.rpow_pos_of_pos hX _) hc
  have hmem : ∀ q ∈ PP m₀ a₀ X, q.Prime ∧ q % 4 = 3 ∧ x ^ (400 : ℝ) < q := by
    intro q hq
    have h := (Finset.mem_filter.1 hq).2
    refine ⟨h.1, ?_, rpow_lt_of_mem_PP hx4 h8' hX h1 hq⟩
    have h4 : q ≡ a₀ [MOD 4] := h.2.of_dvd (Dvd.dvd.trans (by norm_num) h8)
    exact (show q % 4 = a₀ % 4 from h4).trans ha
  refine hcore x hx3 m₀ (PP m₀ a₀ X) κ nStar h8 hm hpr
    (Finset.card_pos.1 (by exact_mod_cast hpos)) hmem hκ1 hκm hκb ?_
  intro n n' hn1 hn2 _ _ hne1 hne2
  have hz : (0 : ℝ) ≤ x ^ (400 : ℝ) := (Real.rpow_pos_of_pos hx0 _).le
  obtain ⟨hn1a, hn1b⟩ := Finset.mem_Icc.1 hn1
  obtain ⟨hn2a, hn2b⟩ := Finset.mem_Icc.1 hn2
  have hn1c : (n : ℝ) ≤ x ^ (400 : ℝ) := (Nat.le_floor_iff hz).1 hn1b
  have hn2c : (n' : ℝ) ≤ x ^ (400 : ℝ) := (Nat.le_floor_iff hz).1 hn2b
  have hnn : 0 < n * n' := Nat.mul_pos hn1a hn2a
  have hsq : Squarefree (outPart m₀ (n * n')) := squarefree_prod_primeFactors_filter _ _
  have hs1 : 1 < outPart m₀ (n * n') := by
    have := hsq.ne_zero
    omega
  have hsle : (outPart m₀ (n * n') : ℝ) ≤ x ^ (800 : ℝ) := by
    have h3 : (outPart m₀ (n * n') : ℝ) ≤ (n : ℝ) * n' := by exact_mod_cast outPart_le_self m₀ _ hnn
    have h4 : x ^ (800 : ℝ) = x ^ (400 : ℝ) * x ^ (400 : ℝ) := by
      rw [← Real.rpow_add hx0]; norm_num
    rw [h4]
    exact h3.trans (mul_le_mul hn1c hn2c (Nat.cast_nonneg _) hz)
  refine le_trans ?_ (hn _ hs1 hsq (outPart_coprime_modulus _ _) hsle hne2)
  rw [abs_div, abs_div]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
  refine abs_sum_jacobiSym_le_outPart m₀ a₀ (n * n') _ h8 hnn ?_
  intro q hq
  obtain ⟨hp, h4, hlt⟩ := hmem q hq
  refine ⟨h4, (Finset.mem_filter.1 hq).2.2, ?_⟩
  have hl : ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ x ^ (400 : ℝ) → Nat.Coprime k q := fun k hk hk' =>
    (Nat.coprime_of_lt_prime (by omega) (by exact_mod_cast hk'.trans_lt hlt) hp).symm
  exact Nat.Coprime.mul_left (hl n hn1a hn1c) (hl n' hn2a hn2c)

end GlobalTheory.Mem.An
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPrimesShortIntervalLowerStatement
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_primes_short_interval_lower : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → ∃ C₀ Cr cr c : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < c ∧ ∀ d M : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 1 ≤ M → ∀ X h : ℝ, (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ C₀ ≤ X → h ≤ 1 → Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr (4 * (d : ℝ) * (M : ℝ) ^ 2) X ≤ h / 100 → (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3) → c * h * (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ (-6 : ℝ) * X / Real.log X ≤ ((normPrimes d M X (X * (1 + h))).card : ℝ) := by
  first | exact @GlobalTheory.Mem.NormPrimes.normPrimes_short_interval | exact GlobalTheory.Mem.NormPrimes.normPrimes_short_interval | (intros; apply GlobalTheory.Mem.NormPrimes.normPrimes_short_interval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotInjectiveTwoPrimesEqualNormCofiniteStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_injective_two_primes_equal_norm_cofinite : ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ∀ f : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} × Bool → HeightOneSpectrum (𝓞 F), Function.Injective f → (∀ x, Ideal.absNorm (f x).asIdeal = Ideal.absNorm x.1.1.asIdeal) → False := by
  first | exact @GlobalTheory.Mem.ZetaPole.not_injective_double_primes | exact GlobalTheory.Mem.ZetaPole.not_injective_double_primes | (intros; apply GlobalTheory.Mem.ZetaPole.not_injective_double_primes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaLebUnique
section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.OmegaLebUnique

theorem omegaLeb_unique :
    ∀ (P Q : ℕ) (l l' : Measure (lieU P Q)), IsOmegaLeb l → IsOmegaLeb l' → l = l' :=
  fun _ _ _ _ h h' => GlobalTheory.CompactDualUnique.isOmegaLeb_unique h h'

end GlobalTheory.OmegaLebUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.ChiIdeal

open GlobalTheory.Mem.Chr.DetOrd

section General

variable {L : Type} [Field L] [NumberField L]

theorem frac_of_mul_eq_one {A B : Submodule (𝓞 L) L} (h : A * B = 1) :
    IsFractional (𝓞 L)⁰ A ∧ ∃ k : Lˣ, (k : L) ∈ A := by
  refine ⟨FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit (IsUnit.of_mul_eq_one B h)), ?_⟩
  have hA : A ≠ ⊥ := by
    rintro rfl
    rw [Submodule.bot_mul] at h
    have : (1 : L) ∈ (⊥ : Submodule (𝓞 L) L) := h ▸ Submodule.one_le.1 le_rfl
    exact one_ne_zero ((Submodule.mem_bot _).1 this)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff A).1 hA
  exact ⟨Units.mk0 x hx0, hx⟩

theorem ordF_le_iff (w : HeightOneSpectrum (𝓞 L)) (a b : Lˣ) :
    ordF w a ≤ ordF w b ↔ w.valuation L (b : L) ≤ w.valuation L (a : L) := by
  have ha : w.valuation L (a : L) ≠ 0 := by simp
  have hb : w.valuation L (b : L) ≠ 0 := by simp
  unfold ordF
  rw [neg_le_neg_iff, WithZero.log_le_log hb ha]

theorem exists_gen {A : Submodule (𝓞 L) L} (h : IsFractional (𝓞 L)⁰ A) (k0 : Lˣ) (hk0 : (k0 : L) ∈ A)
    (w : HeightOneSpectrum (𝓞 L)) :
    ∃ a : Lˣ, (a : L) ∈ A ∧ ordF w a = ordSub w A ∧ ∀ x ∈ A, w.valuation L x ≤ w.valuation L (a : L) := by
  obtain ⟨⟨a, ha, e⟩, hl⟩ := isLeast_ordSub h k0 hk0 w
  refine ⟨a, ha, e, fun x hx => ?_⟩
  by_cases h0 : x = 0
  · simp [h0]
  · have h1 := hl ⟨Units.mk0 x h0, hx, rfl⟩
    rw [← e, ordF_le_iff] at h1
    exact h1

theorem ordSub_mul {A B : Submodule (𝓞 L) L} (hA : IsFractional (𝓞 L)⁰ A) (a0 : Lˣ) (ha0 : (a0 : L) ∈ A)
    (hB : IsFractional (𝓞 L)⁰ B) (b0 : Lˣ) (hb0 : (b0 : L) ∈ B) (w : HeightOneSpectrum (𝓞 L)) :
    ordSub w (A * B) = ordSub w A + ordSub w B := by
  obtain ⟨a, ha, ea, hla⟩ := exists_gen hA a0 ha0 w
  obtain ⟨b, hb, eb, hlb⟩ := exists_gen hB b0 hb0 w
  rw [← ea, ← eb, ← ordF_mul']
  refine IsLeast.csInf_eq ⟨⟨a * b, Submodule.mul_mem_mul ha hb, rfl⟩, ?_⟩
  rintro n ⟨k, hk, rfl⟩
  rw [ordF_le_iff]
  refine Submodule.mul_induction_on (C := fun x => w.valuation L x ≤ w.valuation L ((a * b : Lˣ) : L)) hk
    (fun x hx y hy => ?_) (fun x y hx hy => ?_)
  · rw [Units.val_mul, map_mul, map_mul]
    exact mul_le_mul' (hla x hx) (hlb y hy)
  · exact Valuation.map_add_le _ hx hy

theorem ordSub_one (w : HeightOneSpectrum (𝓞 L)) : ordSub w (1 : Submodule (𝓞 L) L) = 0 := by
  have h := ordSub_span_singleton w (1 : Lˣ)
  rw [Units.val_one, ← Submodule.one_eq_span] at h
  rw [h]
  simp [ordF]

theorem ordF_conj {c : L ≃+* L} {w w' : HeightOneSpectrum (𝓞 L)} (h : ConjPl c w w') (k k' : Lˣ)
    (e : (k' : L) = c k) : ordF w' k' = ordF w k := by
  unfold ordF
  rw [e, h]

theorem ordSub_conj {c : L ≃+* L} {w w' : HeightOneSpectrum (𝓞 L)} (h : ConjPl c w w') {A B : Submodule (𝓞 L) L}
    (hB : ∀ x, x ∈ B ↔ c x ∈ A) : ordSub w' A = ordSub w B := by
  unfold ordSub
  congr 1
  ext n
  constructor
  · rintro ⟨k, hk, rfl⟩
    have h0 : c.symm k ≠ 0 := by simp
    refine ⟨Units.mk0 _ h0, (hB _).2 (by simpa using hk), (ordF_conj h _ _ (by simp)).symm⟩
  · rintro ⟨k, hk, rfl⟩
    have h0 : c k ≠ 0 := by simp
    exact ⟨Units.mk0 _ h0, (hB _).1 hk, ordF_conj h _ _ rfl⟩

theorem ordSub_conj_eq_neg {c : L ≃+* L} {w w' : HeightOneSpectrum (𝓞 L)} (h : ConjPl c w w')
    {A B : Submodule (𝓞 L) L} (hB : ∀ x, x ∈ B ↔ c x ∈ A) (h1 : A * B = 1) : ordSub w' A = -ordSub w A := by
  obtain ⟨fA, a, ha⟩ := frac_of_mul_eq_one h1
  obtain ⟨fB, b, hb⟩ := frac_of_mul_eq_one ((mul_comm B A).trans h1)
  have h2 := ordSub_mul fA a ha fB b hb w
  rw [h1, ordSub_one, ← ordSub_conj h hB] at h2
  omega

variable {F : Type} [Field F] [NumberField F] [Algebra F L]

theorem prod_val_above (χ : HChar L) (hu : ∀ v, χ.UnrAt v) (ht : χ.TrivOn F)
    (hr : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (v : HeightOneSpectrum (𝓞 F)) : ∏ P ∈ aboveF (L := L) F v, χ.val P = 1 := by
  have h := ht.1 v (unif v)
  rw [HChar.resFin, MonoidHom.finset_prod_apply] at h
  rw [← h]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hP' : P.under (𝓞 F) = v := by simpa [aboveF] using hP
  rw [MonoidHom.comp_apply, GlobalTheory.HeckeProduct.locK_unr χ (hu P), hr, hP', ordF_unif_self, zpow_one]

theorem finprod_val_eq_one (χ : HChar L) (hv : ∀ v, ∏ P ∈ aboveF (L := L) F v, χ.val P = 1)
    (n : HeightOneSpectrum (𝓞 L) → ℤ) (hf : {w | n w ≠ 0}.Finite)
    (hn : ∀ w w', w'.under (𝓞 F) = w.under (𝓞 F) → n w' = n w) : ∏ᶠ w, χ.val w ^ n w = 1 := by
  classical
  have hm : ∀ (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 L)),
      P ∈ aboveF (L := L) F v ↔ P.under (𝓞 F) = v := fun v P => by simp [aboveF]
  rw [finprod_eq_prod_of_mulSupport_subset _
    (s := (hf.toFinset.image fun w => w.under (𝓞 F)).biUnion (aboveF (L := L) F)), Finset.prod_biUnion]
  · refine Finset.prod_eq_one fun v hv' => ?_
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hv'
    rw [Finset.prod_congr rfl (fun P hP => by rw [hn w P ((hm _ _).1 hP)]), Finset.prod_zpow, hv, one_zpow]
  · intro v _ v' _ hne
    refine Finset.disjoint_left.2 fun P h1 h2 => hne (((hm _ _).1 h1).symm.trans ((hm _ _).1 h2))
  · intro w hw
    have : n w ≠ 0 := fun h0 => hw (by simp [h0])
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
    exact ⟨_, Finset.mem_image.2 ⟨w, hf.mem_toFinset.2 this, rfl⟩, (hm _ _).2 rfl⟩

theorem finprod_val_add (χ : HChar L) (n m : HeightOneSpectrum (𝓞 L) → ℤ) (hn : {w | n w ≠ 0}.Finite)
    (hm : {w | m w ≠ 0}.Finite) :
    ∏ᶠ w, χ.val w ^ (n w + m w) = (∏ᶠ w, χ.val w ^ n w) * ∏ᶠ w, χ.val w ^ m w := by
  simp only [zpow_add]
  exact finprod_mul_distrib (hn.subset fun w hw h0 => hw (by simp [h0])) (hm.subset fun w hw h0 => hw (by simp [h0]))

theorem finprod_val_congr (χ : HChar L) (hv : ∀ v, ∏ P ∈ aboveF (L := L) F v, χ.val P = 1)
    (n m : HeightOneSpectrum (𝓞 L) → ℤ) (hn : {w | n w ≠ 0}.Finite) (hm : {w | m w ≠ 0}.Finite)
    (h : ∀ w w', w'.under (𝓞 F) = w.under (𝓞 F) → n w' - m w' = n w - m w) :
    ∏ᶠ w, χ.val w ^ n w = ∏ᶠ w, χ.val w ^ m w := by
  have hd : {w | n w - m w ≠ 0}.Finite := (hn.union hm).subset fun w hw => by
    by_contra h0
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at h0
    exact hw (by rw [h0.1, h0.2, sub_self])
  have h1 := finprod_val_add χ _ m hd hm
  rw [finprod_val_eq_one χ hv _ hd h, one_mul] at h1
  simpa using h1

theorem finite_toNat {n : HeightOneSpectrum (𝓞 L) → ℤ} (hn : {w | n w ≠ 0}.Finite) :
    {w | ((n w).toNat : ℤ) ≠ 0}.Finite :=
  hn.subset fun w hw h0 => hw (by simp [h0])

end General

theorem phase_sq_eq {a u : ℂ} (ha : a ≠ 0) (h : u * starRingEnd ℂ a = a) :
    (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = u := by
  have hc : starRingEnd ℂ a ≠ 0 := by simpa using ha
  rw [zpow_ofNat, div_pow, ← Complex.mul_conj', div_eq_iff (mul_ne_zero ha hc)]
  linear_combination (-a) * h

theorem exists_mul_conj_eq {L : Type} [Field L] (c : L →+* L) (hc : ∀ x, c (c x) = x) (hne : ∃ a, c a ≠ a)
    (z : L) (hz : z * c z = 1) : ∃ k : Lˣ, z * c (k : L) = k := by
  by_cases h : 1 + z = 0
  · obtain ⟨a, ha⟩ := hne
    refine ⟨Units.mk0 (a - c a) (sub_ne_zero.2 ha.symm), ?_⟩
    have hz1 : z = -1 := by linear_combination h
    rw [Units.val_mk0, map_sub, hc, hz1]
    ring
  · refine ⟨Units.mk0 (1 + z) h, ?_⟩
    rw [Units.val_mk0, map_add, map_one]
    linear_combination hz

theorem isChi_chiId : ∀ (D : D7) (χ : HChar D.host.E), IsChiPsi D.host χ → Formalism.MainNotions.TaylorLogMetric.IsChi D (chiId χ) := by
  intro D χ hχ
  obtain ⟨c, hc, hcm, hr, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have hv := prod_val_above χ hχ.unr hχ.triv hr
  have hpl := fun w w' => (under_eq_iff_conjPl c hcm.rank hcm.ne w w').1
  refine ⟨?_, ?_⟩
  · rintro A B ⟨A', hA', hA⟩ ⟨B', hB', hB⟩
    obtain ⟨fA, a, ha⟩ := frac_of_mul_eq_one hA
    obtain ⟨fB, b, hb⟩ := frac_of_mul_eq_one hB
    have nA := ordSub_finite fA a ha
    have nB := ordSub_finite fB b hb
    have nAB : {w | ordSub w A + ordSub w B ≠ 0}.Finite := (nA.union nB).subset fun w hw => by
      by_contra h0
      simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at h0
      exact hw (by rw [h0.1, h0.2, add_zero])
    unfold chiId
    rw [← Units.val_mul]
    congr 1
    simp only [← zpow_natCast, ordSub_mul fA a ha fB b hb]
    rw [← finprod_val_add χ _ _ (finite_toNat nA) (finite_toNat nB)]
    refine finprod_val_congr χ hv _ _ (finite_toNat nAB) ((nA.union nB).subset fun w hw => ?_) fun w w' h => ?_
    · by_contra h0
      simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at h0
      exact hw (by simp [h0.1, h0.2])
    · rcases hpl w w' h with rfl | h
      · rfl
      · rw [ordSub_conj_eq_neg h (fun x => (hA' x).trans (by rw [← hc]; rfl)) hA,
          ordSub_conj_eq_neg h (fun x => (hB' x).trans (by rw [← hc]; rfl)) hB]
        omega
  · letI := D.host.cmStar
    intro z
    have hcmf : IsCMField D.host.E := D.host.isCMField_hostE
    have hcc : ∀ x, IsCMField.complexConj D.host.E x = D.host.conj x := fun x => bridge_star_holds D.R D.host x
    have hinv : ∀ x, c (c x) = x := fun x => by
      rw [hc, hc, ← hcc, ← hcc, IsCMField.complexConj_apply_apply]
    have hz : (z : D.host.E) * c (z : D.host.E) = 1 := by
      rw [hc, ← bridge_star_holds D.R D.host]
      exact z.2.2
    obtain ⟨k, hk⟩ := exists_mul_conj_eq (c : D.host.E →+* D.host.E) hinv
      (by by_contra hn; push Not at hn; exact hcm.ne (AlgEquiv.ext hn)) z hz
    have hk' : (z : D.host.E) * c (k : D.host.E) = k := hk
    have z0 : (z : D.host.E) ≠ 0 := left_ne_zero_of_mul_eq_one hz
    have k0 : c (k : D.host.E) ≠ 0 := by simp
    have hu : Units.mk0 _ z0 * Units.mk0 _ k0 = k := Units.ext hk'
    have e1 := chiId_span_singleton χ (Units.mk0 _ z0)
    rw [Units.val_mk0] at e1
    have e2 : ∏ᶠ w, χ.val w ^ (ordF w (Units.mk0 _ z0)).toNat = ∏ᶠ w, χ.val w ^ ordF w k := by
      simp only [← zpow_natCast]
      refine finprod_val_congr χ hv _ _ (finite_toNat (ordF_finite _)) (ordF_finite _) fun w w' h => ?_
      rcases hpl w w' h with rfl | h
      · rfl
      · have a1 := ordF_mul' w (Units.mk0 _ z0) (Units.mk0 _ k0)
        have a2 := ordF_mul' w' (Units.mk0 _ z0) (Units.mk0 _ k0)
        have a3 := ordF_conj h k (Units.mk0 _ k0) rfl
        have a4 := ordF_conj h (Units.mk0 _ k0) k (hinv _).symm
        rw [hu] at a1 a2
        omega
    have e3 := GlobalTheory.HeckeProduct.productRule χ ∅ (fun v _ => hχ.unr v) k
    simp only [Finset.prod_empty, mul_one, Finset.notMem_empty, not_false_eq_true, finprod_true] at e3
    rw [mul_comm, mul_eq_one_iff_eq_inv] at e3
    rw [e1, e2, e3, Units.val_inv_eq_inv_val, hχ.inf k, ← Finset.prod_inv_distrib]
    refine (Fintype.prod_equiv D.eTau _ _ fun τ => ?_).symm
    congr 1
    refine (phase_sq_eq ((map_ne_zero _).2 k.ne_zero) ?_).symm
    have hcj : embPsi D.host (D.eTau τ) (D.host.conj (k : D.host.E)) =
        starRingEnd ℂ (embPsi D.host (D.eTau τ) (k : D.host.E)) := Formalism.HC.HostAx.conjE_apply _ _ _
    rw [← hcj, ← hc]
    exact (map_mul (embPsi D.host (D.eTau τ)) _ _).symm.trans (congrArg _ hk')

end GlobalTheory.Mem.ChiIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationSquaresAgreeAtEachThickeningStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_squares_agree_at_each_thickening : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I →
    ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G)
    (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen →
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      eSec G (r z) ∈ U.LG.L.U jL → eSec G (r z) ∈ U'.LG.L.U jL' →
      gm r z _ (U.LG.rig.s (fun _ => jL)) ^ 2 =
        gv wL (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') * gm r z _ (U'.LG.rig.s (fun _ => jL')) ^ 2) →
    ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom →
    (U'.gt e).q ≫ β.hom = (U.gt e).q →
    ∃ v : LB.Iso ((LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).pull
        (fstG I e D'.toPre.P.A).left)
      ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull
        (β.hom.left ≫ (fstG I e D.toPre.P.A).left)), v.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
      (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
      (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
      gw v (r ≫ (U'.gt e).q.left) z (fun _ => jM) (fun _ => fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 =
        gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG I e G).left) z (fun _ => jL) (fun _ => jL') := by
  first | exact @GlobalTheory.polarisation_squares_agree_at_level | exact GlobalTheory.polarisation_squares_agree_at_level | (intros; apply GlobalTheory.polarisation_squares_agree_at_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeLevelStructureDataRanksModPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeLevelStructureData_ranks_mod_prime : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → (∀ P c, Module.finrank (Res P.1) (A.lv P c) = n) ∧ ∀ P c, Module.finrank (Res P.1) (A.lk P c) = n := by
  first | exact @GlobalTheory.Mem.Col2.LRank.ranks | exact GlobalTheory.Mem.Col2.LRank.ranks | (intros; apply GlobalTheory.Mem.Col2.LRank.ranks <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Psi0TruncatedExplicitFormulaStatement
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_psi0_add_zsum_le_of_isPrimitive : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u → ‖GlobalTheoryTheory.psi0 χ u + zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (q * u * T) ^ 2 / T + Real.log (q * u) + zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)) := by
  first | exact @GlobalTheory.Mem.An.ExplUsed.explicit_formula_used | exact GlobalTheory.Mem.An.ExplUsed.explicit_formula_used | (intros; apply GlobalTheory.Mem.An.ExplUsed.explicit_formula_used <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameAtOfLocalizationEqStatement
section
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sameAt_of_localization_eq : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (Q : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E A → Submodule.IsLattice E B → localization₂ Q.asIdeal A = localization₂ Q.asIdeal B → SameAt Q A B := by
  first | exact @GlobalTheory.sameAt_of_localized_eq | exact GlobalTheory.sameAt_of_localized_eq | (intros; apply GlobalTheory.sameAt_of_localized_eq <;> assumption)
end

