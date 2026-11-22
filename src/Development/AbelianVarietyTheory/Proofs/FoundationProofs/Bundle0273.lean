import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0261
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0262
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0251
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormCmPrimeInertPrimeSign
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

namespace GlobalTheory.InertResidue

theorem card_of_involution {k : Type} [Field k] [Finite k] {q : ℕ} [Fact q.Prime] [CharP k q] (s : k →+* k)
    (hs : ∀ x, s (s x) = x) {r : k} {m : ℤ} (hr : r ^ 2 = m) (hsr : s r = -r) (hne : -r ≠ r) :
    (∃ f, Odd f ∧ Nat.card k = q ^ (2 * f)) ∧ ¬ IsSquare (m : ZMod q) := by
  letI : Algebra (ZMod q) k := ZMod.algebra k q
  haveI := Fintype.ofFinite k
  let σ : k ≃ₐ[ZMod q] k :=
    { toFun := s, invFun := s, left_inv := hs, right_inv := hs, map_mul' := map_mul s, map_add' := map_add s,
      commutes' := fun c => RingHom.congr_fun (Subsingleton.elim (s.comp (algebraMap (ZMod q) k)) _) c }
  have hσ : ∀ x, σ x = s x := fun _ => rfl
  constructor
  · obtain ⟨⟨j, hj⟩, e⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod q) k).2 σ
    set φ := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod q) k with hφ
    change φ ^ j = σ at e
    have ho : orderOf φ = Module.finrank (ZMod q) k := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod q) k
    have h2 : φ ^ (2 * j) = 1 := by
      rw [two_mul, pow_add, e]; ext x; exact hs x
    have hsq : (φ r) ^ 2 = r ^ 2 := by rw [← map_pow, hr, map_intCast]
    have hev : ∀ i, (φ ^ (2 * i)) r = r := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih =>
        rw [mul_add, pow_add, AlgEquiv.mul_apply, mul_one, sq, AlgEquiv.mul_apply]
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
        · rw [h, h, ih]
        · rw [h, map_neg, h, neg_neg, ih]
    have hodd : Odd j := by
      rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
      · exact absurd (by rw [← hsr, ← hσ, ← e, hev]) hne
      · exact ⟨i, rfl⟩
    refine ⟨j, hodd, ?_⟩
    have hd := orderOf_dvd_of_pow_eq_one h2
    rw [ho] at hd
    have hn : Module.finrank (ZMod q) k = 2 * j := by
      obtain ⟨c, hc⟩ := hd
      have hj0 := hodd.pos
      rcases c with _ | _ | c
      · omega
      · omega
      · nlinarith [Nat.zero_le (Module.finrank (ZMod q) k * c)]
    rw [Module.natCard_eq_pow_finrank (K := ZMod q), hn, Nat.card_zmod]
  · rintro ⟨c, hc⟩
    have h1 : r ^ 2 = (algebraMap (ZMod q) k c) ^ 2 := by rw [hr, sq, ← map_mul, ← hc, map_intCast]
    apply hne
    rw [← hsr, ← hσ]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h] <;> simp

theorem exists_root (D : D7) (n : ℕ) (b : D.host.E) (hb : b ^ 2 = -(n : D.host.E)) :
    ∃ r : 𝓞 D.host.E, r ^ 2 = ((-(n : ℤ) : ℤ) : 𝓞 D.host.E) ∧ D.host.conj • r = -r := by
  have hint : IsIntegral ℤ b := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hb]
    exact (isIntegral_natCast n).neg
  have hconj : D.host.conj b = -b := by
    apply D.host.φ₀.injective
    have h1 : D.host.φ₀ (D.host.conj b) = starRingEnd ℂ (D.host.φ₀ b) :=
      D.host.conjE_apply D.host.φ₀ b
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have h2 : (D.host.φ₀ b) ^ 2 = (Complex.I * (Real.sqrt n : ℂ)) ^ 2 := by
      rw [← map_pow, hb, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
        Real.sq_sqrt hn0]
      simp
    rw [h1, map_neg]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h <;> rw [h] <;> simp
  refine ⟨⟨b, hint⟩, RingOfIntegers.ext ?_, RingOfIntegers.ext hconj⟩
  have : (((-(n : ℤ) : ℤ) : 𝓞 D.host.E) : D.host.E) = ((-(n : ℤ) : ℤ) : D.host.E) :=
    map_intCast (algebraMap (𝓞 D.host.E) D.host.E) _
  rw [this]
  push_cast
  exact hb

theorem two_not_mem (D : D7) {P : Ideal (𝓞 D.host.E)} (hP : P.IsPrime) (hsP : ∀ x ∈ P, D.host.conj • x ∈ P) :
    (2 : 𝓞 D.host.E) ∉ P := by
  intro h2
  have hw : D.host.conj • (Formalism.L2.Pj.w0E D) = 1 - Formalism.L2.Pj.w0E D := by
    rw [← Formalism.L2.Pj.conj_w0E D]
    exact RingOfIntegers.ext (Formalism.L2.Pj.barE_eq_conj D (Formalism.L2.Pj.w0E D)).symm
  have hsq := Formalism.L2.Pj.w0E_sq D
  obtain ⟨k, hk⟩ : ∃ k, Formalism.L2.Pj.mE D = 2 * k := by
    have h1 := D.host.hyp.2.2.2.1
    have h3 := Formalism.L2.Pj.mE_spec D
    exact ⟨Formalism.L2.Pj.mE D / 2, by omega⟩
  rw [hk] at hsq
  push_cast at hsq
  set w := Formalism.L2.Pj.w0E D
  have hm : w * (1 - w) ∈ P := by
    have : w * (1 - w) = k * 2 := by linear_combination -hsq
    rw [this]; exact P.mul_mem_left _ h2
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one]
  rcases hP.mem_or_mem hm with h | h
  · have h' := hsP _ h
    rw [hw] at h'
    simpa using P.add_mem h h'
  · have h' := hsP _ h
    rw [smul_sub, smul_one, hw] at h'
    simpa using P.add_mem h h'

theorem card_of_root (D : D7) {P : Ideal (𝓞 D.host.E)} (hP : P.IsMaximal) (hfix : D.host.conj • P = P) {q : ℕ}
    (hq : q.Prime) (hqP : (q : 𝓞 D.host.E) ∈ P) (n : ℕ) (hc : Nat.Coprime q n) (b : D.host.E)
    (hb : b ^ 2 = -(n : D.host.E)) :
    (∃ f, Odd f ∧ Ideal.absNorm P = q ^ (2 * f)) ∧ ¬ IsSquare (-(n : ZMod q)) := by
  have hsP : ∀ x ∈ P, D.host.conj • x ∈ P := fun x hx => by
    rw [← hfix]; exact Ideal.smul_mem_pointwise_smul _ _ _ hx
  obtain ⟨r, hr, hsr⟩ := exists_root D n b hb
  haveI := Fact.mk hq
  letI := Ideal.Quotient.field P
  haveI : Finite (𝓞 D.host.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P
    (Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _))
  haveI : CharP (𝓞 D.host.E ⧸ P) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]; exact hqP)
  let c := MulSemiringAction.toRingHom _ (𝓞 D.host.E) D.host.conj
  let s : 𝓞 D.host.E ⧸ P →+* 𝓞 D.host.E ⧸ P := Ideal.quotientMap P c hsP
  have hs : ∀ x, s (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (D.host.conj • x) := fun _ => rfl
  have h := card_of_involution (q := q) s (r := Ideal.Quotient.mk P r) (m := -(n : ℤ))
    (fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [hs, hs, smul_smul, VacInt.conj_mul_self, one_smul])
    (by rw [← map_pow, hr, map_intCast]) (by rw [hs, hsr, map_neg])
    (fun h => by
      rw [← map_neg, Ideal.Quotient.eq] at h
      have h2 : 2 * r ∈ P := by
        have := P.neg_mem h
        convert this using 1
        ring
      have h3 := (hP.isPrime.mem_or_mem h2).resolve_left (two_not_mem D hP.isPrime hsP)
      have hnP : (n : 𝓞 D.host.E) ∈ P := by
        have := P.neg_mem (hr ▸ P.pow_mem_of_mem h3 2 two_pos)
        simpa using this
      obtain ⟨u, v, huv⟩ : IsCoprime (q : 𝓞 D.host.E) (n : 𝓞 D.host.E) := hc.cast
      exact hP.ne_top ((Ideal.eq_top_iff_one P).2
        (huv ▸ P.add_mem (P.mul_mem_left u hqP) (P.mul_mem_left v hnP))))
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  push_cast at h
  exact h

theorem exists_prime (D : D7) {P : Ideal (𝓞 D.host.E)} (hP : P.IsMaximal) :
    ∃ q n : ℕ, q.Prime ∧ (q : 𝓞 D.host.E) ∈ P ∧ Ideal.absNorm P = q ^ n := by
  letI := Ideal.Quotient.field P
  haveI : Finite (𝓞 D.host.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P
    (Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _))
  haveI := Fintype.ofFinite (𝓞 D.host.E ⧸ P)
  obtain ⟨q, hc, n, hq, hn⟩ := FiniteField.card' (𝓞 D.host.E ⧸ P)
  refine ⟨q, n, hq, ?_, ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ q
  · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hn]

theorem norm_prime : ∀ (D : D7) (P : Ideal (𝓞 D.host.E)), P.IsMaximal → Ev D (Ideal.absNorm P) ∧ (D.host.conj • P = P → sgn D (Ideal.absNorm P) = -1 ∧ ∃ q f : ℕ, q.Prime ∧ InertQ D q ∧ q ≠ 2 ∧ (q : 𝓞 D.host.E) ∈ P ∧ Odd f ∧ Ideal.absNorm P = q ^ (2 * f) ∧ (q ≠ D.host.d → ¬ IsSquare (-(D.host.d : ZMod q)))) ∧ (D.host.conj • P ≠ P → sgn D (Ideal.absNorm P) = 1 ∧ ∀ q : ℕ, q.Prime → (q : 𝓞 D.host.E) ∈ P → ¬ InertQ D q) := by
  intro D P hP
  obtain ⟨q, n, hq, hqP, hn⟩ := exists_prime D hP
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  by_cases hfix : D.host.conj • P = P
  · have hin : InertQ D q := by
      by_contra h
      exact VacInt.conj_smul_ne D hq h P hP.isPrime hqP hfix
    obtain ⟨hq₁, hd, hq8, hd16, -⟩ := D.host.hyp
    have hd' : q ≠ D.host.d → _ := fun h => card_of_root D hP hfix hq hqP D.host.d
      ((Nat.coprime_primes hq hd).2 h) (D.host.sqd)
      (D.host.sqd_sq)
    obtain ⟨f, hf, hN⟩ : ∃ f, Odd f ∧ Ideal.absNorm P = q ^ (2 * f) := by
      by_cases h : q = D.host.d
      · exfalso
        haveI := hP.isPrime
        haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := by
          refine ⟨Ideal.IsMaximal.eq_of_le
            (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hq).irreducible)
            (Ideal.IsPrime.ne_top inferInstance) ?_⟩
          rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
          exact hqP
        exact D.host.der.decompConj q hq (h ▸ Dvd.intro_left _ rfl) P (MulAction.mem_stabilizer_iff.2 hfix)
      · exact (hd' h).1
    refine ⟨?_, fun _ => ⟨?_, q, f, hq, hin, ?_, hqP, hf, hN, fun h => (hd' h).2⟩, fun h => absurd hfix h⟩
    · intro p _ _
      rw [hN, Nat.factorization_pow]
      simp [Nat.even_mul]
    · have hf0 : 2 * f ≠ 0 := by have := hf.pos; omega
      rw [hN, sgn, hlf, Nat.primeFactors_prime_pow hf0 hq, Finset.filter_singleton, if_pos hin,
        Finset.sum_singleton, Nat.factorization_pow_self hq, Nat.mul_div_cancel_left _ two_pos, hf.neg_one_pow]
    · rintro rfl
      exact two_not_mem D hP.isPrime
        (fun x hx => by rw [← hfix]; exact Ideal.smul_mem_pointwise_smul _ _ _ hx) (by exact_mod_cast hqP)
  · have hall : ∀ p : ℕ, (p : 𝓞 D.host.E) ∈ P → ¬ InertQ D p := fun p hp h => hfix (h P hP.isPrime hP0 hp)
    have h0 : ∀ p : ℕ, InertQ D p → (Ideal.absNorm P).factorization p = 0 := fun p hp => by
      rw [hn, hq.factorization_pow, Finsupp.single_eq_of_ne]
      rintro rfl
      exact hall _ hqP hp
    refine ⟨fun p _ hp => by rw [h0 p hp]; exact Even.zero, fun h => absurd h hfix, fun _ => ⟨?_, fun p _ hp => hall p hp⟩⟩
    rw [← sgn_one (D := D)]
    exact sgn_congr fun p _ hp => by rw [h0 p hp]; simp

end GlobalTheory.InertResidue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdelicHermitianCharacterPairingPropertiesStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicHermitianCharacterPairing_properties : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ ψ : AE D → ℂ, IsPsi D cc δ ψ → ∀ (N N' : ℕ), (∀ u ζ η, gamA ψ (actA D N N' u ζ) (actA D N N' u η) = gamA ψ ζ η) ∧ (∀ ζ : XA D N N', gamA ψ ζ ζ = 1) ∧ (∀ (r : 𝓞 D.host.E) (ζ η : XA D N N'), gamA ψ (r • ζ) η = gamA ψ ζ (sgO D r • η)) ∧ (∀ ζ η ξ : XA D N N', gamA ψ (ζ + η) ξ = gamA ψ ζ ξ * gamA ψ η ξ) ∧ (∀ ζ η ξ : XA D N N', gamA ψ ζ (η + ξ) = gamA ψ ζ η * gamA ψ ζ ξ) := by
  first | exact @GlobalTheory.FinWeil.gamA_alg | exact GlobalTheory.FinWeil.gamA_alg | (intros; apply GlobalTheory.FinWeil.gamA_alg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleAtOfIrreducibleTameStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_point_additive_form : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧ ∀ (N N' : ℕ) (z y : Matrix (Fin N') (Fin N) D.host.E), ee (-(Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y)).im) = psi0 D cc δ (∑ i, ∑ j, z i j * D.host.conj (y i j)) ∧ pt D (tor0 D cc δ) δ (z + y) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ y ∧ ∀ F, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ y) F) = psi0 D cc δ (∑ i, ∑ j, (w : D.host.E) * z i j * D.host.conj (y i j)) • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z + y)) F := by
  first | exact @GlobalTheory.FinWeil.WdCocycle.wd_cocycle | exact GlobalTheory.FinWeil.WdCocycle.wd_cocycle | (intros; apply GlobalTheory.FinWeil.WdCocycle.wd_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorTorsionTranslateEvenThetaStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicTaylor_torsionTranslate_evenTheta : ∀ Λ : AddSubgroup ℂ, IsLat Λ → (∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (sgStar Λ))) → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (GL3Theta.th0 Λ t₀)) ∧ ∀ ω ∈ Λ, ∃ κ ∈ Qbar, κ ≠ 0 ∧ ∀ z, U1 Λ (x + ω) (GL3Theta.th0 Λ t₀) z = κ * U1 Λ x (GL3Theta.th0 Λ t₀) z := by
  first | exact @GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt | exact GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt | (intros; apply GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AugSpanOneMemOfOrthogonalThree
section
open scoped Matrix

namespace GlobalTheory.AugCore

variable {K : Type} [Field K] {Γ : Type} [Group Γ] {m : ℕ}

abbrev augSpan (S : Γ →* Matrix (Fin m) (Fin m) K) : Submodule K (Matrix (Fin m) (Fin m) K) :=
  Submodule.span K (Set.range fun g => S g - 1)

def Stable (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)) : Prop :=
  ∀ g, ∀ v ∈ P, S g *ᵥ v ∈ P

theorem mul_mem_augSpan (S : Γ →* Matrix (Fin m) (Fin m) K) {A C : Matrix (Fin m) (Fin m) K}
    (hA : A ∈ augSpan S) (hC : C ∈ augSpan S) : A * C ∈ augSpan S := by
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    induction hC using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, rfl⟩ := hy
      have e : (S g - 1) * (S h - 1) = (S (g * h) - 1) - (S g - 1) - (S h - 1) := by
        rw [map_mul]; noncomm_ring
      rw [e]
      exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩)
        (Submodule.subset_span ⟨_, rfl⟩)) (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul a y _ hy => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ a hy
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ a hx

theorem augSpan_preserves (S : Γ →* Matrix (Fin m) (Fin m) K) {P : Submodule K (Fin m → K)}
    (hP : Stable S P) {T : Matrix (Fin m) (Fin m) K} (hT : T ∈ augSpan S) :
    ∀ v ∈ P, T *ᵥ v ∈ P := by
  induction hT using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    intro v hv
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact P.sub_mem (hP g v hv) hv
  | zero => intro v _; rw [Matrix.zero_mulVec]; exact P.zero_mem
  | add x y _ _ hx hy => intro v hv; rw [Matrix.add_mulVec]; exact P.add_mem (hx v hv) (hy v hv)
  | smul a x _ hx => intro v hv; rw [Matrix.smul_mulVec]; exact P.smul_mem a (hx v hv)

def Good (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)) : Prop :=
  ∃ T ∈ augSpan S, ∀ v ∈ P, T *ᵥ v = v

theorem good_sup (S : Γ →* Matrix (Fin m) (Fin m) K) {L P : Submodule K (Fin m → K)}
    (hL : Stable S L) (hP : Stable S P) (gL : Good S L) (gP : Good S P) : Good S (L ⊔ P) := by
  obtain ⟨T₁, h₁, e₁⟩ := gL
  obtain ⟨T₂, h₂, e₂⟩ := gP
  refine ⟨T₁ + T₂ - T₁ * T₂, Submodule.sub_mem _ (Submodule.add_mem _ h₁ h₂)
    (mul_mem_augSpan S h₁ h₂), ?_⟩
  intro v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  have hTa : T₂ *ᵥ a ∈ L := augSpan_preserves S hL h₂ a ha
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_add,
    e₁ a ha, e₂ b hb, e₁ _ hTa]
  abel

theorem good_bot (S : Γ →* Matrix (Fin m) (Fin m) K) : Good S ⊥ :=
  ⟨0, Submodule.zero_mem _, fun v hv => by
    rw [(Submodule.mem_bot K).mp hv, Matrix.mulVec_zero]⟩

theorem stable_inf (S : Γ →* Matrix (Fin m) (Fin m) K) {L P : Submodule K (Fin m → K)}
    (hL : Stable S L) (hP : Stable S P) : Stable S (L ⊓ P) :=
  fun g v hv => ⟨hL g v hv.1, hP g v hv.2⟩

theorem stable_orthogonal (S : Γ →* Matrix (Fin m) (Fin m) K)
    (B : LinearMap.BilinForm K (Fin m → K))
    (hinv : ∀ g v w, B (S g *ᵥ v) (S g *ᵥ w) = B v w) {Q : Submodule K (Fin m → K)}
    (hQ : Stable S Q) : Stable S (B.orthogonal Q) := by
  intro g v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
  intro n hn
  have e : S g *ᵥ (S g⁻¹ *ᵥ n) = n := by
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
  have := hv _ (hQ g⁻¹ n hn)
  rw [← e, hinv]
  exact this

end GlobalTheory.AugCore

namespace GlobalTheory.AugCore

variable {K : Type} [Field K] {Γ : Type} [Group Γ]

theorem inf_orthogonal_eq_bot (S : Γ →* Matrix (Fin 3) (Fin 3) K)
    (B : LinearMap.BilinForm K (Fin 3 → K)) (hB : B.Nondegenerate)
    (hiso : ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0)
    {Q : Submodule K (Fin 3 → K)} (hQ : Stable S Q) (hQo : Stable S (B.orthogonal Q)) :
    Q ⊓ B.orthogonal Q = ⊥ := by
  set Z := Q ⊓ B.orthogonal Q with hZ
  have hZs : Stable S Z := stable_inf S hQ hQo
  have hZle : Z ≤ B.orthogonal Z := by
    intro z hz
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hz.2) n hn.1
  have h3 : Module.finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
  have hfo : Module.finrank K (B.orthogonal Z) = 3 - Module.finrank K Z := by
    rw [LinearMap.BilinForm.finrank_orthogonal hB, h3]
  have hmono := Submodule.finrank_mono hZle
  by_contra hne
  obtain ⟨y, hyZ, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hsp : (K ∙ y) ≤ Z := (Submodule.span_singleton_le_iff_mem y Z).mpr hyZ
  have h1 : Module.finrank K (K ∙ y) = 1 := finrank_span_singleton hy0
  have hspm := Submodule.finrank_mono hsp
  have hZ1 : Module.finrank K Z = 1 := by omega
  have heq : (K ∙ y) = Z := Submodule.eq_of_le_of_finrank_eq hsp (by rw [h1, hZ1])
  apply hiso y hy0
  · intro g
    have : S g *ᵥ y ∈ (K ∙ y) := by rw [heq]; exact hZs g y hyZ
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
    exact ⟨c, hc.symm⟩
  · exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hyZ.2) y hyZ.1

theorem sup_orthogonal_eq_top (S : Γ →* Matrix (Fin 3) (Fin 3) K)
    (B : LinearMap.BilinForm K (Fin 3 → K)) (hB : B.Nondegenerate)
    (hiso : ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0)
    {Q : Submodule K (Fin 3 → K)} (hQ : Stable S Q) (hQo : Stable S (B.orthogonal Q)) :
    Q ⊔ B.orthogonal Q = ⊤ := by
  have h3 : Module.finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
  have key := Submodule.finrank_sup_add_finrank_inf_eq Q (B.orthogonal Q)
  rw [inf_orthogonal_eq_bot S B hB hiso hQ hQo, finrank_bot,
    LinearMap.BilinForm.finrank_orthogonal hB, h3] at key
  have hle := Submodule.finrank_le Q
  rw [h3] at hle
  apply Submodule.eq_top_of_finrank_eq
  rw [h3]; omega

theorem good_of_stable (S : Γ →* Matrix (Fin 3) (Fin 3) K) [IsAlgClosed K]
    (B : LinearMap.BilinForm K (Fin 3 → K)) (hB : B.Nondegenerate)
    (hinv : ∀ g v w, B (S g *ᵥ v) (S g *ᵥ w) = B v w)
    (hfix : ∀ v : Fin 3 → K, (∀ g, S g *ᵥ v = v) → v = 0)
    (hiso : ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0) :
    ∀ n, ∀ P : Submodule K (Fin 3 → K), Stable S P → Module.finrank K P = n → Good S P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hP hn
  by_cases hirr : ∀ Q : Submodule K (Fin 3 → K), Q ≤ P → Stable S Q → Q = ⊥ ∨ Q = P
  · by_cases hbot : P = ⊥
    · rw [hbot]; exact good_bot S
    · have hnt : ∃ g, ∃ v ∈ P, S g *ᵥ v ≠ v := by
        by_contra hc
        push_neg at hc
        apply hbot
        rw [Submodule.eq_bot_iff]
        intro v hv
        exact hfix v (fun g => hc g v hv)
      exact GlobalTheory.T.exists_augmentationSpan_eq_id_on_irreducible S P hP hirr hnt
  · push_neg at hirr
    obtain ⟨Q, hQP, hQs, hQ0, hQne⟩ := hirr
    have hQo : Stable S (B.orthogonal Q) := stable_orthogonal S B hinv hQs
    set R := P ⊓ B.orthogonal Q with hR
    have hRs : Stable S R := stable_inf S hP hQo
    have htop := sup_orthogonal_eq_top S B hB hiso hQs hQo
    have hinf := inf_orthogonal_eq_bot S B hB hiso hQs hQo
    have hQR : Q ⊔ R = P := by
      apply le_antisymm (sup_le hQP inf_le_left)
      intro v hv
      have hvt : v ∈ Q ⊔ B.orthogonal Q := by rw [htop]; trivial
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hvt
      have hbP : b ∈ P := by
        have := P.sub_mem hv (hQP ha)
        simpa using this
      exact Submodule.mem_sup.mpr ⟨a, ha, b, ⟨hbP, hb⟩, rfl⟩
    have hQlt : Module.finrank K Q < n := by
      rw [← hn]; exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hQP hQne)
    have hRne : R ≠ P := by
      intro hRP
      apply hQ0
      rw [eq_bot_iff, ← hinf]
      intro x hx
      have : x ∈ R := by rw [hRP]; exact hQP hx
      exact ⟨hx, this.2⟩
    have hRlt : Module.finrank K R < n := by
      rw [← hn]; exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left hRne)
    have g := good_sup S hQs hRs (ih _ hQlt Q hQs rfl) (ih _ hRlt R hRs rfl)
    rwa [hQR] at g

end GlobalTheory.AugCore

theorem GlobalTheory.augSpan_one_mem_of_orthogonal_three : ∀ {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ] (S : Γ →* Matrix (Fin 3) (Fin 3) K) (B : LinearMap.BilinForm K (Fin 3 → K)), B.Nondegenerate → B.IsSymm → (∀ g v w, B (S g *ᵥ v) (S g *ᵥ w) = B v w) → (∀ v : Fin 3 → K, (∀ g, S g *ᵥ v = v) → v = 0) → (∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0) → (1 : Matrix (Fin 3) (Fin 3) K) ∈ Submodule.span K (Set.range fun g => S g - 1) := by
  intro K _ _ _ Γ _ S B hB _ hinv hfix hiso
  obtain ⟨T, hT, hTv⟩ := GlobalTheory.AugCore.good_of_stable S B hB hinv hfix hiso _ ⊤
    (fun _ _ _ => trivial) rfl
  have e : T = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec]
    exact hTv v trivial
  exact (congrArg (· ∈ Submodule.span K (Set.range fun g => S g - 1)) e).mp hT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardParitySignLengthOfEqStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattices_neighbour_chain : ∀ (D : D7) (n : ℕ) (L₀ L : Lat D n), SD D L₀ → SD D L → L₀ ≠ L → ∃ (P : Ideal (𝓞 D.host.E)) (q : ℕ) (x : Fin n → D.host.E), P.IsMaximal ∧ q.Prime ∧ (q : 𝓞 D.host.E) ∈ P ∧ x ∈ L₀ ∧ NbD D P L x ∧ lenQ D L₀ (nbr D L x) + 1 = lenQ D L₀ L := by
  first | exact @GlobalTheory.NearerNeighbour.exists_nearer | exact GlobalTheory.NearerNeighbour.exists_nearer | (intros; apply GlobalTheory.NearerNeighbour.exists_nearer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactSpaceUpqTZeroRight
section
open Formalism.BasicNotions MeasureTheory Filter Topology

namespace GlobalTheory

theorem compactSpace_UpqT_zero_right : ∀ N : ℕ, CompactSpace (UpqT N 0) :=
  fun N => (GlobalTheory.compactSpace_UpqT_definite N).1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedStandardAdelicLatticePropertiesStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedStandardAdelicLattice_properties : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ z : Matrix (Fin N') (Fin N) D.host.E, z.map (inc D) ∈ latA D cc N N' ↔ pt D (tor0 D cc δ) δ z ∈ La0 D (tor0 D cc δ) N N') ∧ (∀ x ∈ La0 D (tor0 D cc δ) N N', ∃ z, x = pt D (tor0 D cc δ) δ z) ∧ (∀ (ζ : XA D N N') (m : ℕ), 0 < m → ∃ z : Matrix (Fin N') (Fin N) D.host.E, ∃ a ∈ latA D cc N N', z.map (inc D) = ζ + m • a) ∧ (∀ ζ : XA D N N', ∃ m : ℕ, 0 < m ∧ m • ζ ∈ latA D cc N N') ∧ (∃ m : ℕ, 0 < m ∧ ∀ y ∈ IhE D cc, (m : AE D) * y ∈ OhE D) ∧ (∃ m : ℕ, 0 < m ∧ ∀ s ∈ OhE D, (m : AE D) * s ∈ IhE D cc) := by
  first | exact @GlobalTheory.CompletedLattice.completed_lattice | exact GlobalTheory.CompletedLattice.completed_lattice | (intros; apply GlobalTheory.CompletedLattice.completed_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjInvolutiveAndExistsHalfIdempotent
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.NormSum.HalfIdempotent

theorem conj_involutive_and_exists_half_idempotent : ∀ (D : D7), (∀ y : AE D, sgA D (sgA D y) = y) ∧ ∃ ε ∈ OhE D, ε * ε = ε ∧ ε * sgA D ε = 0 ∧ ∀ q : ℕ, q.Prime → (InertQ D q → ZeroAt D q (ε + sgA D ε)) ∧ (¬ InertQ D q → ZeroAt D q (1 - (ε + sgA D ε))) :=
  fun D => ⟨GlobalTheory.NormSum.VacMove.sgA_sgA D, GlobalTheory.NormSum.VacMove.exists_half_idem D⟩

end GlobalTheory.NormSum.HalfIdempotent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalValueModPrimePowUniqueOddWeightStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w : ℕ), Odd w → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ φ' : HahnSeries ℚ Ω,
  IsThB X A N l n b φ → IsThB X A N l n b φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X A N l _ hj hl2 hlN hN
  exact GlobalTheory.isThB_coeff_cong Ω ε X A N l hj hl2 hlN (by omega)
end

