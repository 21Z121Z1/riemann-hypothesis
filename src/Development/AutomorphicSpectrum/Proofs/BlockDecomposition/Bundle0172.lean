import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
import GroundTheory.PAdicHodge.BStPeriod
import GroundTheory.PAdicHodge.KerTheta
import GroundTheory.PAdicHodge.TiltValuation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0164
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0167
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0151

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicPairUnitaryTransitive
section
open HeckeCharacterZeroLocus.SiegelWeilU
open scoped Matrix

namespace GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry

open GlobalTheory.CompanionTheory.SW.QuasiRefl

section Form

variable {A : Type} [CommRing A] {N : ℕ} {τ : A →+* A} {H : Matrix (Fin N) (Fin N) A}

theorem hform_add_fst (x x' y : Fin N → A) :
    hform τ H (x + x') y = hform τ H x y + hform τ H x' y := by
  have h : (τ ∘ (x + x')) = τ ∘ x + τ ∘ x' := by
    funext i
    simp
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, h, add_dotProduct]

theorem hform_add_snd (x y y' : Fin N → A) :
    hform τ H x (y + y') = hform τ H x y + hform τ H x y' := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, Matrix.mulVec_add, dotProduct_add]

theorem hform_sub_fst (x x' y : Fin N → A) :
    hform τ H (x - x') y = hform τ H x y - hform τ H x' y := by
  have h : (τ ∘ (x - x')) = τ ∘ x - τ ∘ x' := by
    funext i
    simp
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, h, sub_dotProduct]

theorem hform_sub_snd (x y y' : Fin N → A) :
    hform τ H x (y - y') = hform τ H x y - hform τ H x y' := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, Matrix.mulVec_sub, dotProduct_sub]

theorem hform_unitary {g : GL (Fin N) A} (hg : g ∈ UJ τ H) (x y : Fin N → A) :
    hform τ H ((g : Matrix (Fin N) (Fin N) A) *ᵥ x) ((g : Matrix (Fin N) (Fin N) A) *ᵥ y) =
      hform τ H x y := by
  rw [hform_mulVec']
  have hg' : cT τ (g : Matrix (Fin N) (Fin N) A) * H * (g : Matrix (Fin N) (Fin N) A) = H := hg
  rw [hg']

theorem carry (hτ : ∀ y, τ (τ y) = y)
    (hcar : ∀ p β : A, IsUnit β → τ β = β → ∃ ε z : A, ε * τ ε = 1 ∧ (β - τ ε * p) * z = 1)
    (hH : ∀ i j, τ (H j i) = H i j) (x y : Fin N → A)
    (hxy : hform τ H x x = hform τ H y y) (hβ : IsUnit (hform τ H x x)) :
    ∃ g ∈ UJ τ H, (g : Matrix (Fin N) (Fin N) A) *ᵥ x = y ∧
      ∀ z, hform τ H x z = 0 → hform τ H y z = 0 → (g : Matrix (Fin N) (Fin N) A) *ᵥ z = z := by
  have hfix : τ (hform τ H x x) = hform τ H x x := hform_conj_symm hτ hH x x
  obtain ⟨ε, z, hε, hz⟩ := hcar (hform τ H y x) (hform τ H x x) hβ hfix
  exact exists_unitary_carry A τ hτ N H hH x y ε hxy hβ hε ⟨⟨_, z, hz, (mul_comm z _).trans hz⟩, rfl⟩

theorem exists_hyperbolic_partner (hτ : ∀ y, τ (τ y) = y) (h2 : IsUnit (2 : A))
    {Hi : Matrix (Fin N) (Fin N) A} (hHi : H * Hi = 1) (hH : ∀ i j, τ (H j i) = H i j)
    (y a : Fin N → A) (hyy : hform τ H y y = 0) (hay : ∑ k, a k * y k = 1) :
    ∃ y₁ : Fin N → A, hform τ H y₁ y₁ = 0 ∧ hform τ H y y₁ = 1 := by
  have hyw : hform τ H y (Hi *ᵥ (τ ∘ a)) = 1 := by
    rw [hform_eq_dot, Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec]
    have h : (τ ∘ y) ⬝ᵥ (τ ∘ a) = τ (∑ k, a k * y k) := by
      simp only [dotProduct, Function.comp_apply, map_sum, map_mul]
      exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
    rw [h, hay, map_one]
  have hwy : hform τ H (Hi *ᵥ (τ ∘ a)) y = 1 := by
    rw [← hform_conj_symm hτ hH y (Hi *ᵥ (τ ∘ a)), hyw, map_one]
  have hww : τ (hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a))) =
      hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a)) := hform_conj_symm hτ hH _ _
  have ht2 : 2 * (↑h2.unit⁻¹ : A) = 1 := h2.mul_val_inv
  have hτt : τ (↑h2.unit⁻¹ : A) = ↑h2.unit⁻¹ := by
    have h1 : τ (↑h2.unit⁻¹ : A) * 2 = 1 := by
      have h := congrArg τ ht2
      rw [map_mul, map_one, map_ofNat] at h
      rw [mul_comm]
      exact h
    calc τ (↑h2.unit⁻¹ : A) = τ (↑h2.unit⁻¹ : A) * (2 * ↑h2.unit⁻¹) := by rw [ht2, mul_one]
      _ = (τ (↑h2.unit⁻¹ : A) * 2) * ↑h2.unit⁻¹ := by ring
      _ = ↑h2.unit⁻¹ := by rw [h1, one_mul]
  have hτc : τ ((↑h2.unit⁻¹ : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a))) =
      (↑h2.unit⁻¹ : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a)) := by
    rw [map_mul, hτt, hww]
  refine ⟨Hi *ᵥ (τ ∘ a) - ((↑h2.unit⁻¹ : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a))) • y, ?_, ?_⟩
  · rw [hform_sub_left, hform_sub_right, hform_sub_right, hyy, hwy, hyw, hτc]
    linear_combination (-1 : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a)) * ht2
  · rw [hform_sub_right, hyw, hyy, mul_zero, sub_zero]

end Form

theorem exists_unitary_carry_primitive :
    ∀ (A : Type) [CommRing A] (τ : A →+* A), (∀ y, τ (τ y) = y) → IsUnit (2 : A) →
    (∀ p β : A, IsUnit β → τ β = β → ∃ ε z : A, ε * τ ε = 1 ∧ (β - τ ε * p) * z = 1) →
    ∀ (N : ℕ) (H Hi : Matrix (Fin N) (Fin N) A), H * Hi = 1 → (∀ i j, τ (H j i) = H i j) →
    ∀ e f y a : Fin N → A, hform τ H e e = 0 → hform τ H f f = 0 → hform τ H e f = 1 →
    hform τ H y y = 0 → ∑ k, a k * y k = 1 →
    ∃ g ∈ UJ τ H, (g : Matrix (Fin N) (Fin N) A) *ᵥ e = y := by
  intro A _ τ hτ h2 hcar N H Hi hHi hH e f y a hee hff hef hyy hay
  obtain ⟨y₁, hy₁, hyy₁⟩ := exists_hyperbolic_partner hτ h2 hHi hH y a hyy hay
  have hfe : hform τ H f e = 1 := by rw [← hform_conj_symm hτ hH e f, hef, map_one]
  have hy₁y : hform τ H y₁ y = 1 := by rw [← hform_conj_symm hτ hH y y₁, hyy₁, map_one]
  have hx1 : hform τ H (e + f) (e + f) = 2 := by
    rw [hform_add_fst, hform_add_snd, hform_add_snd, hee, hef, hfe, hff]
    norm_num
  have hy1 : hform τ H (y + y₁) (y + y₁) = 2 := by
    rw [hform_add_fst, hform_add_snd, hform_add_snd, hyy, hyy₁, hy₁y, hy₁]
    norm_num
  obtain ⟨g₁, hg₁, hg₁x, -⟩ := carry hτ hcar hH (e + f) (y + y₁) (by rw [hx1, hy1]) (by rw [hx1]; exact h2)
  have hvv : hform τ H ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) = -2 := by
    rw [hform_unitary hg₁, hform_sub_fst, hform_sub_snd, hform_sub_snd, hee, hef, hfe, hff]
    ring
  have hyy' : hform τ H (y - y₁) (y - y₁) = -2 := by
    rw [hform_sub_fst, hform_sub_snd, hform_sub_snd, hyy, hyy₁, hy₁y, hy₁]
    ring
  have h2' : IsUnit (-2 : A) := h2.neg
  obtain ⟨g₂, hg₂, hg₂v, hfix⟩ := carry hτ hcar hH ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) (y - y₁)
    (by rw [hvv, hyy']) (by rw [hvv]; exact h2')
  have hperp1 : hform τ H ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) (y + y₁) = 0 := by
    rw [← hg₁x, hform_unitary hg₁, hform_sub_fst, hform_add_snd, hform_add_snd, hee, hef, hfe, hff]
    ring
  have hperp2 : hform τ H (y - y₁) (y + y₁) = 0 := by
    rw [hform_sub_fst, hform_add_snd, hform_add_snd, hyy, hyy₁, hy₁y, hy₁]
    ring
  have hfix' := hfix (y + y₁) hperp1 hperp2
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_⟩
  have hsum : ((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ (e + f) = y + y₁ := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg₁x, hfix']
  have hdiff : ((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ (e - f) = y - y₁ := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg₂v]
  have key : (2 : A) • (((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ e) = (2 : A) • y := by
    have h : ((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ ((e + f) + (e - f)) = (y + y₁) + (y - y₁) := by
      rw [Matrix.mulVec_add, hsum, hdiff]
    have he : (e + f) + (e - f) = (2 : A) • e := by
      rw [two_smul]
      abel
    have hy : (y + y₁) + (y - y₁) = (2 : A) • y := by
      rw [two_smul]
      abel
    rw [he, Matrix.mulVec_smul, hy] at h
    exact h
  have h3 := congrArg (fun z => (↑h2.unit⁻¹ : A) • z) key
  simp only [smul_smul, h2.val_inv_mul, one_smul] at h3
  exact h3

end GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentSumInjective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.FixInj

variable {l : ℕ} [Fact l.Prime]

theorem coeff_zero_eq_zero_of_mem (A : PAlg l) :
    ∀ (n : ℕ) (d : ℤ) (x : A.W), ¬ ((l : ℤ) ^ n ∣ d) →
      (d : A.W) * x ∈ Ideal.span {(l : A.W) ^ n} → x.coeff 0 = 0 := by
  intro n
  induction n with
  | zero => intro d x h; exact absurd (by simp) h
  | succ n ih =>
    intro d x hd hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
    by_cases hl : (l : ℤ) ∣ d
    · obtain ⟨d', rfl⟩ := hl
      refine ih d' x (fun h => hd ?_) ?_
      · rw [pow_succ']; exact mul_dvd_mul_left _ h
      · refine Ideal.mem_span_singleton'.2 ⟨y, ?_⟩
        have h0 : (l : A.W) * (y * (l : A.W) ^ n - (d' : A.W) * x) = 0 := by
          push_cast at hy
          linear_combination hy
        exact sub_eq_zero.1 (A.l_mul_eq_zero h0)
    · have hc : (d : A.A) * x.coeff 0 = 0 := by
        have h1 := congrArg (WittVector.constantCoeff : A.W →+* A.A) hy
        rw [map_mul, map_mul, map_pow, map_natCast, map_intCast, A.natCast_l,
          zero_pow (Nat.succ_ne_zero n), mul_zero, WittVector.constantCoeff_apply] at h1
        exact h1.symm
      have hcop : IsCoprime d (l : ℤ) :=
        (((Nat.prime_iff_prime_int.1 (Fact.out : l.Prime)).coprime_iff_not_dvd).2 hl).symm
      obtain ⟨u, v, huv⟩ := hcop
      have h2 : (u : A.A) * (d : A.A) + (v : A.A) * (l : A.A) = 1 := by
        have := congrArg (Int.cast : ℤ → A.A) huv
        push_cast at this
        exact this
      rw [A.natCast_l, mul_zero, add_zero] at h2
      calc x.coeff 0 = ((u : A.A) * (d : A.A)) * x.coeff 0 := by rw [h2, one_mul]
        _ = (u : A.A) * ((d : A.A) * x.coeff 0) := mul_assoc _ _ _
        _ = 0 := by rw [hc, mul_zero]

theorem idemSum_mul_teichmuller (A : PAlg l) (n : ℕ) [NeZero (l ^ n)] (e : ZMod (l ^ n) → A.A)
    (he : CompleteOrthogonalIdempotents e) (a : ZMod (l ^ n)) (z : A.A) :
    A.idemSum n e * Ideal.Quotient.mk (Ideal.span {(l : A.W) ^ n})
        (WittVector.teichmuller l (e a * z)) =
      (a.val : A.Wn n) * Ideal.Quotient.mk (Ideal.span {(l : A.W) ^ n})
        (WittVector.teichmuller l (e a * z)) := by
  have hterm : ∀ c : ZMod (l ^ n),
      Ideal.Quotient.mk (Ideal.span {(l : A.W) ^ n}) (WittVector.teichmuller l (e c)) *
        Ideal.Quotient.mk (Ideal.span {(l : A.W) ^ n}) (WittVector.teichmuller l (e a * z)) =
      Ideal.Quotient.mk (Ideal.span {(l : A.W) ^ n})
        (WittVector.teichmuller l (e c * (e a * z))) := by
    intro c
    rw [← map_mul, ← map_mul]
  unfold PAlg.idemSum
  rw [Finset.sum_mul, Finset.sum_eq_single a]
  · rw [mul_assoc, hterm, ← mul_assoc, he.idem a]
  · intro c _ hc
    rw [mul_assoc, hterm, ← mul_assoc, he.ortho hc, zero_mul, WittVector.teichmuller_zero, map_zero,
      mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem mul_eq_zero_of_ne (A : PAlg l) (n : ℕ) [NeZero (l ^ n)] (e e' : ZMod (l ^ n) → A.A)
    (he : CompleteOrthogonalIdempotents e) (he' : CompleteOrthogonalIdempotents e')
    (hs : A.idemSum n e = A.idemSum n e') {a b : ZMod (l ^ n)} (hab : a ≠ b) :
    e a * e' b = 0 := by
  have h1 := idemSum_mul_teichmuller A n e he a (e' b)
  have h2 := idemSum_mul_teichmuller A n e' he' b (e a)
  rw [mul_comm (e' b) (e a)] at h2
  rw [hs, h2] at h1
  have hmem : (((a.val : ℤ) - (b.val : ℤ) : ℤ) : A.W) *
      WittVector.teichmuller l (e a * e' b) ∈ Ideal.span {(l : A.W) ^ n} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_intCast]
    push_cast
    exact (sub_mul _ _ _).trans (sub_eq_zero.2 h1.symm)
  have hnd : ¬ ((l : ℤ) ^ n ∣ ((a.val : ℤ) - (b.val : ℤ))) := by
    intro h
    apply hab
    have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((a.val : ℤ) - (b.val : ℤ)) (l ^ n)).2
      (by exact_mod_cast h)
    push_cast at h3
    simpa [sub_eq_zero] using h3
  have := coeff_zero_eq_zero_of_mem A n _ _ hnd hmem
  rwa [WittVector.teichmuller_coeff_zero] at this

theorem idem_unique : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) (e e' : ZMod (l ^ n) → A.A), (haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩; CompleteOrthogonalIdempotents e ∧ CompleteOrthogonalIdempotents e') → A.idemSum n e = A.idemSum n e' → e = e' := by
  intro l _ A n e e' h hs
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨he, he'⟩ : CompleteOrthogonalIdempotents e ∧ CompleteOrthogonalIdempotents e' := h
  funext a
  have h1 : e a = e a * e' a := by
    calc e a = e a * ∑ b, e' b := by rw [he'.complete, mul_one]
      _ = ∑ b, e a * e' b := Finset.mul_sum _ _ _
      _ = e a * e' a := Finset.sum_eq_single a
          (fun b _ hb => mul_eq_zero_of_ne A n e e' he he' hs (Ne.symm hb))
          (fun h => absurd (Finset.mem_univ a) h)
  have h2 : e' a = e a * e' a := by
    calc e' a = (∑ b, e b) * e' a := by rw [he.complete, one_mul]
      _ = ∑ b, e b * e' a := Finset.sum_mul _ _ _
      _ = e a * e' a := Finset.sum_eq_single a
          (fun b _ hb => mul_eq_zero_of_ne A n e e' he he' hs hb)
          (fun h => absurd (Finset.mem_univ a) h)
  exact h1.trans h2.symm

end GlobalTheory.CompanionTheory.FixInj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRingAdicCompletePrimeRegular
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.TiltCompl

variable {l : ℕ} [Fact l.Prime]

theorem norm_pFlat_pos : 0 < ‖pFlat l‖ := by
  rw [preTilt_norm_def, coe_untilt_pFlat]
  exact norm_pos_iff.2 natCast_p_ne_zero_cp

theorem norm_pFlat_lt_one : ‖pFlat l‖ < 1 := by
  rw [preTilt_norm_def, coe_untilt_pFlat]
  exact IsPerfectoidField.norm_natCast_lt_one

theorem smodEq_iff (n : ℕ) (x y : Ob l) :
    x ≡ y [SMOD (Ideal.span {pFlat l} ^ n • ⊤ : Ideal (Ob l))] ↔ ‖x - y‖ ≤ ‖pFlat l‖ ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, preTilt_dvd_iff_norm_le, norm_pow]

theorem complete_tf : ∀ {l : ℕ} [Fact l.Prime],
    IsAdicComplete (Ideal.span {pFlat l}) (Ob l) ∧ pFlat l ∈ nonZeroDivisors (Ob l) := by
  intro l _
  have h0 : 0 < ‖pFlat l‖ := norm_pFlat_pos
  have h1 : ‖pFlat l‖ < 1 := norm_pFlat_lt_one
  have hlim : Filter.Tendsto (fun n : ℕ => ‖pFlat l‖ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1
  refine ⟨{ haus' := fun x hx => ?_, prec' := fun f hf => ?_ }, ?_⟩
  · have hb : ∀ n : ℕ, ‖x‖ ≤ ‖pFlat l‖ ^ n := fun n => by
      simpa using (smodEq_iff n x 0).1 (hx n)
    have : ‖x‖ ≤ 0 := ge_of_tendsto' hlim hb
    exact norm_le_zero_iff.1 this
  · have hb : ∀ {m n : ℕ}, m ≤ n → ‖f m - f n‖ ≤ ‖pFlat l‖ ^ m := fun h =>
      (smodEq_iff _ _ _).1 (hf h)
    have hc : CauchySeq f := by
      refine cauchySeq_of_le_geometric ‖pFlat l‖ 1 h1 fun n => ?_
      rw [dist_eq_norm, one_mul]
      exact hb n.le_succ
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨L, fun n => (smodEq_iff _ _ _).2 ?_⟩
    have ht : Filter.Tendsto (fun m => ‖f n - f m‖) Filter.atTop (nhds ‖f n - L‖) :=
      (tendsto_const_nhds.sub hL).norm
    refine le_of_tendsto ht ?_
    filter_upwards [Filter.eventually_ge_atTop n] with m hm using hb hm
  · exact mem_nonZeroDivisors_iff_left.2 fun x hx => by
      have := congrArg norm hx
      rw [norm_mul, norm_zero] at this
      exact norm_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h0.ne')

end GlobalTheory.CompanionTheory.TiltCompl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRingFacts
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.TiltFacts

variable (l : ℕ) [Fact l.Prime]

theorem isDomain_ob : IsDomain (CrystallineSemistableComparison.Ob l) :=
  IsPerfectoidField.isDomain_preTilt (K := ℂ_[l]) l

theorem norm_pFlat_eq : ‖(pFlat l : PreTilt (normInteger ℂ_[l]) l)‖ = ‖(l : ℂ_[l])‖ := by
  rw [preTilt_norm_def, coe_untilt_pFlat]

theorem norm_pFlat_pos : 0 < ‖(pFlat l : PreTilt (normInteger ℂ_[l]) l)‖ := by
  rw [norm_pFlat_eq]
  exact norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

theorem norm_pFlat_lt_one : ‖(pFlat l : PreTilt (normInteger ℂ_[l]) l)‖ < 1 := by
  rw [norm_pFlat_eq]
  exact IsPerfectoidField.norm_natCast_lt_one

theorem rt_pow (k : ℕ) : CrystallineSemistableComparison.D.rt l k ^ l ^ k = pFlat l := by
  have h := (iterateFrobeniusEquiv (CrystallineSemistableComparison.Ob l) l k).apply_symm_apply (pFlat l)
  rwa [iterateFrobeniusEquiv_def] at h

theorem exists_dvd_pFlat_pow (a : CrystallineSemistableComparison.Ob l) (ha : a ≠ 0) : ∃ M : ℕ, a ∣ pFlat l ^ M := by
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 ha) (norm_pFlat_lt_one l)
  refine ⟨M, preTilt_dvd_iff_norm_le.2 ?_⟩
  rw [norm_pow]
  exact hM.le

theorem exists_rt_dvd (a : CrystallineSemistableComparison.Ob l) (ha : ¬ IsUnit a) : ∃ k : ℕ, CrystallineSemistableComparison.D.rt l k ∣ a := by
  have hlt : ‖a‖ < 1 := by
    refine lt_of_le_of_ne (preTilt_norm_le_one a) fun h => ha ?_
    exact (IsPerfectoidField.isUnit_iff_norm_untilt l).2 (by rwa [preTilt_norm_def] at h)
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pFlat_pos l) hlt
  have hnl : n ≤ l ^ n := (Nat.lt_pow_self hl).le
  refine ⟨n, preTilt_dvd_iff_norm_le.2 ?_⟩
  have h1 : ‖a‖ ^ l ^ n ≤ ‖CrystallineSemistableComparison.D.rt l n‖ ^ l ^ n := by
    rw [← norm_pow (CrystallineSemistableComparison.D.rt l n), rt_pow]
    exact (pow_le_pow_of_le_one (norm_nonneg _) hlt.le hnl).trans hn.le
  exact le_of_pow_le_pow_left₀ (pow_ne_zero _ (by omega)) (norm_nonneg _) h1

theorem obFacts : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.ObFacts l := by
  intro l _
  haveI := isDomain_ob l
  refine ⟨inferInstance, ?_, exists_dvd_pFlat_pow l, exists_rt_dvd l⟩
  refine (ValuationRing.iff_dvd_total).2 ⟨fun a b => ?_⟩
  rcases le_total ‖a‖ ‖b‖ with h | h
  · exact Or.inr (preTilt_dvd_iff_norm_le.2 h)
  · exact Or.inl (preTilt_dvd_iff_norm_le.2 h)

end GlobalTheory.CompanionTheory.TiltFacts
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationTopEqBot
section
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatNil

theorem isDPMorphism_ι {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)
    (hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) :
    IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γB f ξ) (Lat.ι f ξ l M) := by
  refine ⟨Ideal.map_comap_le, ?_⟩
  intro n a ha
  exact (Lat.ι_γ f ξ l M hc ha).symm

theorem dividedPowerFiltration_eq_bot : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ hc : Lat.DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ), pdP (Lat.γ f ξ l M hc) m = ⊥ := by
  intro W B _ _ _ f ξ l M m h hc
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  have h1 : Lat.ι f ξ l M x ∈ pdP (Lat.γB f ξ) m := dividedPowerFiltration_map (isDPMorphism_ι f ξ l M hc) m hx
  rw [GlobalTheory.T.divided_power_filtration_span_pow f ξ m, h.nil, Ideal.mem_span_singleton, zero_dvd_iff] at h1
  exact Lat.ι_injective f ξ l M (by rw [h1, map_zero])

end GlobalTheory.CompanionTheory.LatNil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalIdempotentsOfPowPrimeEqSelf
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.FrobFixed

open Polynomial in

theorem sum_one_sub_pow {l : ℕ} [Fact l.Prime] [NeZero l] :
    ∑ c : ZMod l, (1 - (X - C c) ^ (l - 1) : (ZMod l)[X]) = 1 := by
  have hl : l.Prime := Fact.out
  have hl1 : l - 1 ≠ 0 := by
    have := hl.two_le
    omega
  rw [← sub_eq_zero]
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Finset.univ (fun a _ => ?_) ?_
  · have key : ∀ c : ZMod l, (1 - (a - c) ^ (l - 1) : ZMod l) = if a = c then 1 else 0 := fun c => by
      split_ifs with h
      · rw [h, sub_self, zero_pow hl1, sub_zero]
      · rw [ZMod.pow_card_sub_one_eq_one (sub_ne_zero.2 h), sub_self]
    simp only [eval_sub, eval_finset_sum, eval_one, eval_pow, eval_X, eval_C, key]
    simp
  · have hdeg : ∀ c : ZMod l, natDegree (1 - (X - C c) ^ (l - 1) : (ZMod l)[X]) ≤ l - 1 := fun c => by
      refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
      refine natDegree_pow_le.trans ?_
      rw [natDegree_X_sub_C, mul_one]
    have h1 : natDegree (∑ c : ZMod l, (1 - (X - C c) ^ (l - 1) : (ZMod l)[X]) - 1) ≤ l - 1 := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
      exact natDegree_sum_le_of_forall_le _ _ fun c _ => hdeg c
    rw [Finset.card_univ, ZMod.card]
    have := hl.two_le
    omega

theorem exists_idempotents {R : Type*} [CommRing R] {l : ℕ} [Fact l.Prime] [NeZero l]
    (hR : (l : R) = 0) (x : R) (hx : x ^ l = x) :
    ∃ e : ZMod l → R, CompleteOrthogonalIdempotents e ∧ ∀ c, e c * (x - (c.val : R)) = 0 := by
  rcases subsingleton_or_nontrivial R with h | h
  · exact ⟨0, ⟨⟨fun _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩,
      Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  have hl : l.Prime := Fact.out
  have hl1 : l - 1 ≠ 0 := by
    have := hl.two_le
    omega
  haveI : CharP R l := (CharP.charP_iff_prime_eq_zero hl).2 hR
  letI : Algebra (ZMod l) R := ZMod.algebra R l
  have hφ : ∀ c : ZMod l, (c.val : R) = algebraMap (ZMod l) R c := fun c => by
    rw [← map_natCast (algebraMap (ZMod l) R), ZMod.natCast_zmod_val]
  have hpow : ∀ c : ZMod l, (x - algebraMap (ZMod l) R c) ^ l = x - algebraMap (ZMod l) R c := fun c => by
    rw [sub_pow_char, hx, ← map_pow, ZMod.pow_card]
  obtain ⟨e, he⟩ : ∃ e : ZMod l → R, ∀ c, e c = 1 - (x - algebraMap (ZMod l) R c) ^ (l - 1) := ⟨_, fun _ => rfl⟩
  have hann : ∀ c, e c * (x - algebraMap (ZMod l) R c) = 0 := fun c => by
    have h1 : (x - algebraMap (ZMod l) R c) ^ (l - 1) * (x - algebraMap (ZMod l) R c)
        = x - algebraMap (ZMod l) R c := by
      rw [← pow_succ, Nat.sub_add_cancel hl.one_le, hpow]
    rw [he, sub_mul, one_mul, h1, sub_self]
  have hlin : ∀ c d, e c * (x - algebraMap (ZMod l) R d) = e c * algebraMap (ZMod l) R (c - d) := fun c d => by
    have h1 : x - algebraMap (ZMod l) R d
        = (x - algebraMap (ZMod l) R c) + algebraMap (ZMod l) R (c - d) := by
      rw [map_sub]; ring
    rw [h1, mul_add, hann, zero_add]
  have hmul : ∀ c d k, e c * (x - algebraMap (ZMod l) R d) ^ k
      = e c * algebraMap (ZMod l) R ((c - d) ^ k) := fun c d k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_right_comm, hlin, mul_assoc, ← map_mul, pow_succ']
  refine ⟨e, ⟨⟨fun c => ?_, fun c d hcd => ?_⟩, ?_⟩, fun c => by rw [hφ, hann]⟩
  · change e c * e c = e c
    have h1 : e c * e c = e c * (1 - (x - algebraMap (ZMod l) R c) ^ (l - 1)) := congrArg (e c * ·) (he c)
    rw [h1, mul_sub, mul_one, hmul, sub_self, zero_pow hl1, map_zero, mul_zero, sub_zero]
  · change e c * e d = 0
    rw [he d, mul_sub, mul_one, hmul, ZMod.pow_card_sub_one_eq_one (sub_ne_zero.2 hcd), map_one, mul_one,
      sub_self]
  · have h1 := congrArg (Polynomial.aeval x) (sum_one_sub_pow (l := l))
    simp only [map_sum, map_sub, map_one, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun c _ => he c

theorem fix_one : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (x : A.A), x ^ l = x → ∃ e : ZMod l → A.A, (haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩; CompleteOrthogonalIdempotents e ∧ ∀ c, e c * (x - (c.val : A.A)) = 0) := by
  intro l _ A x hx
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  exact exists_idempotents A.natCast_l x hx

end GlobalTheory.CompanionTheory.FrobFixed
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarMultiplicationShiftsFiltrationStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_multiplication_shifts_filtration : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens) (i : ℕ) (a : A), a ∈ pdP γ i → ∀ r : ℤ,
    (smO γ q l s 𝒱).LeC a (sFil _ (r - i)) (sFil _ r) := by
  first | exact @GlobalTheory.CompanionTheory.LecShift.leC_shift | exact GlobalTheory.CompanionTheory.LecShift.leC_shift | (intros; apply GlobalTheory.CompanionTheory.LecShift.leC_shift <;> assumption)
end

