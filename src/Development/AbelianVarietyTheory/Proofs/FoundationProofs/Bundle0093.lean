import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0089
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0077

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CyclotomicCharacterFrobV
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem rootOfUnity_eq_one_of_val {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    {m : ℕ} (hm : ¬ v (m : K) < 1) {η : K} (hη : η ^ m = 1) (h1 : v (η - 1) < 1) : η = 1 := by
  by_contra hne
  apply hm
  have hv : v η = 1 := by
    have := v.map_one_add_of_lt h1
    simpa using this
  have hi : ∀ i : ℕ, v (1 - η ^ i) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : 1 - η ^ (i + 1) = (1 - η ^ i) + -(η ^ i * (η - 1)) := by ring
      rw [e]
      refine v.map_add_lt ih ?_
      rw [v.map_neg, map_mul, map_pow, hv, one_pow, one_mul]
      exact h1
  have hs : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := mul_geom_sum η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  have e : (m : K) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  exact v.map_sum_lt one_ne_zero fun i _ => hi i

theorem not_val_lt_one_of_coprime {K : Type*} [Field K] (V : ValuationSubring K) {m q : ℕ} (h : Nat.Coprime m q)
    (hq : V.valuation (q : K) < 1) : ¬ V.valuation (m : K) < 1 := by
  intro hm
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  have e : (1 : K) = (a : K) * m + (b : K) * q := by
    have := congrArg (Int.cast : ℤ → K) hab
    push_cast at this
    exact this.symm
  have hz : ∀ (c : ℤ) (x : K), V.valuation x < 1 → V.valuation ((c : K) * x) < 1 := by
    intro c x hx
    rw [map_mul]
    have hc : V.valuation (c : K) ≤ 1 := (V.valuation_le_one_iff _).mpr (intCast_mem V c)
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hx
  have := V.valuation.map_add_lt (hz a _ hm) (hz b _ hq)
  rw [← e, map_one] at this
  exact lt_irrefl _ this

theorem FrobV.apply_rootOfUnity {Ω : Type} [Field Ω] [Algebra ℚ Ω] {V : ValuationSubring Ω} {q : ℕ}
    {s : Ω ≃ₐ[ℚ] Ω} (hs : FrobV V q s) {m : ℕ} (hm0 : m ≠ 0) (hm : Nat.Coprime m q) {ζ : Ω} (hζ : ζ ^ m = 1) :
    s ζ = ζ ^ q := by
  have hq : V.valuation (q : Ω) < 1 := V.mem_nonunits_iff.mp hs.1
  have hv : V.valuation ζ = 1 := by
    have := congrArg V.valuation hζ
    rw [map_pow, map_one] at this
    exact (pow_eq_one_iff_left hm0).mp this
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hv
  have hV : ζ ∈ V := (V.valuation_le_one_iff _).mp hv.le
  have h := (hs.2 ζ hV).2.2
  have hq0 : ζ ^ q ≠ 0 := pow_ne_zero _ hζ0
  have key : s ζ / ζ ^ q = 1 := by
    refine rootOfUnity_eq_one_of_val V.valuation (not_val_lt_one_of_coprime V hm hq) ?_ ?_
    · rw [div_pow, ← map_pow, hζ, map_one, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, div_one]
    · rw [div_sub_one hq0, map_div₀, map_pow, hv, one_pow, div_one]
      exact h
  exact (div_eq_one_iff_eq hq0).mp key

theorem cyclotomicCharacter_frobV : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l q : ℕ) [Fact l.Prime],
    q.Prime → q ≠ l → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s →
      (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) = q := by
  intro Ω _ _ _ l q hl hq hql V s hs
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, NeZero ((l ^ i : ℕ) : Ω) := fun i => ⟨by exact_mod_cast pow_ne_zero i hl.out.ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [cyclotomicCharacter.toZModPow, map_natCast]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have ht' : (t : Ω) ^ (l ^ n) = 1 := (mem_rootsOfUnity' _ _).mp ht
  have hc : Nat.Coprime (l ^ n) q := ((Nat.coprime_primes hl.out hq).mpr hql.symm).pow_left n
  have := hs.apply_rootOfUnity (pow_ne_zero n hl.out.ne_zero) hc ht'
  rw [ZMod.val_natCast, ← pow_eq_pow_mod q ht']
  exact this

end GlobalTheory.KZ.ES
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraPotentialSubmoduleAndBaseChange
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ

theorem pot_triv_lin : ∀ (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)), (∀ F G, F ∈ Pot R w Γ → G ∈ Pot R w Γ → F + G ∈ Pot R w Γ) ∧ (0 ∈ Pot R w Γ) ∧ (∀ (c : R) F, F ∈ Pot R w Γ → c • F ∈ Pot R w Γ) ∧ (∀ F G, F ∈ Triv R w Γ → G ∈ Triv R w Γ → F + G ∈ Triv R w Γ) ∧ (∀ (c : R) F, F ∈ Triv R w Γ → c • F ∈ Triv R w Γ) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) F, F ∈ Pot R w Γ → (fun z => MvPolynomial.map f (F z)) ∈ Pot S w Γ) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) F, F ∈ Triv R w Γ → (fun z => MvPolynomial.map f (F z)) ∈ Triv S w Γ) := by
  intro R _ w Γ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    refine ⟨fun z => (hF z).add (hG z), fun γ hγ => ?_⟩
    obtain ⟨p, hp⟩ := hF' γ hγ
    obtain ⟨q, hq⟩ := hG' γ hγ
    refine ⟨p + q, fun z hz => ?_⟩
    simp only [Pi.add_apply, map_add]
    rw [← hp z hz, ← hq z hz]; abel
  · refine ⟨fun z => MvPolynomial.isHomogeneous_zero _ _ _, fun γ _ => ⟨0, fun z _ => ?_⟩⟩
    simp
  · rintro c F ⟨hF, hF'⟩
    refine ⟨fun z => ?_, fun γ hγ => ?_⟩
    · simp only [Pi.smul_apply, MvPolynomial.smul_eq_C_mul]
      simpa using (MvPolynomial.isHomogeneous_C (Fin 2) c).mul (hF z)
    · obtain ⟨p, hp⟩ := hF' γ hγ
      refine ⟨c • p, fun z hz => ?_⟩
      simp only [Pi.smul_apply, map_smul]
      rw [← hp z hz, smul_sub]
  · rintro F G ⟨ψ, p, hψ, hp⟩ ⟨ψ', p', hψ', hp'⟩
    refine ⟨ψ + ψ', p + p', fun γ hγ z hz => ?_, fun z hz => ?_⟩
    · simp only [Pi.add_apply, map_add, hψ γ hγ z hz, hψ' γ hγ z hz]
    · simp only [Pi.add_apply, hp z hz, hp' z hz]; abel
  · rintro c F ⟨ψ, p, hψ, hp⟩
    refine ⟨c • ψ, c • p, fun γ hγ z hz => ?_, fun z hz => ?_⟩
    · simp only [Pi.smul_apply, map_smul, hψ γ hγ z hz]
    · simp only [Pi.smul_apply, hp z hz, smul_add]
  · rintro S _ f F ⟨hF, hF'⟩
    refine ⟨fun z => (hF z).map f, fun γ hγ => ?_⟩
    obtain ⟨p, hp⟩ := hF' γ hγ
    refine ⟨MvPolynomial.map f p, fun z hz => ?_⟩
    rw [← (polySlash_laws R).2.2.2.2.1 S f, ← map_sub, hp z hz]
  · rintro S _ f F ⟨ψ, p, hψ, hp⟩
    refine ⟨fun z => MvPolynomial.map f (ψ z), MvPolynomial.map f p, fun γ hγ z hz => ?_, fun z hz => ?_⟩
    · simp only
      rw [← (polySlash_laws R).2.2.2.2.1 S f, hψ γ hγ z hz]
    · simp only [hp z hz, map_add]

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinAlgebraicPowerSeriesCoeffClosure
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.AlgPowerSeries

theorem mem_range_map_iff {L : Type} [CommRing L] (B : Subring L) (f : PowerSeries L) :
    f ∈ (PowerSeries.map B.subtype).range ↔ ∀ k, PowerSeries.coeff k f ∈ B := by
  constructor
  · rintro ⟨g, rfl⟩ k
    rw [PowerSeries.coeff_map]; exact (PowerSeries.coeff k g).2
  · intro h
    refine ⟨PowerSeries.mk fun k => ⟨PowerSeries.coeff k f, h k⟩, ?_⟩
    ext k; simp [PowerSeries.coeff_map]

theorem exists_finset_coeff_mem_closure :
    ∀ (L : Type) [Field L] [CharZero L] (A : Subring L) (b : PowerSeries L)
      (Q : Polynomial (PowerSeries L)), Q ≠ 0 →
      (∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ A) → Q.eval b = 0 →
      ∃ S : Finset L, ∀ k, PowerSeries.coeff k b ∈ Subring.closure ((A : Set L) ∪ S) := by
  classical
  intro L _ _ A b Q hQ hA hb
  obtain ⟨RA, hRAdef⟩ : ∃ RA : Subring (PowerSeries L), RA = (PowerSeries.map A.subtype).range :=
    ⟨_, rfl⟩
  have hex : ∃ d, ∃ R : Polynomial (PowerSeries L), R ≠ 0 ∧ (∀ i, R.coeff i ∈ RA) ∧
      R.eval b = 0 ∧ R.natDegree = d :=
    ⟨Q.natDegree, Q, hQ, fun i => hRAdef ▸ (mem_range_map_iff A _).2 (hA i), hb, rfl⟩
  obtain ⟨R, hR0, hRA', hRb, hRd⟩ := Nat.find_spec hex
  have hmin : ∀ R' : Polynomial (PowerSeries L), R' ≠ 0 → (∀ i, R'.coeff i ∈ RA) →
      R'.natDegree < R.natDegree → R'.eval b ≠ 0 := by
    intro R' h0 hc hlt he
    exact Nat.find_min hex (by omega) ⟨R', h0, hc, he, rfl⟩
  have hdeg : R.natDegree ≠ 0 := by
    intro h
    rw [Polynomial.eq_C_of_natDegree_eq_zero h, Polynomial.eval_C] at hRb
    apply hR0; rw [Polynomial.eq_C_of_natDegree_eq_zero h, hRb, map_zero]
  obtain ⟨D, hD⟩ : ∃ D, D = Polynomial.derivative R := ⟨_, rfl⟩
  have hD0 : D ≠ 0 := by
    haveI : IsAddTorsionFree (PowerSeries L) := IsAddTorsionFree.of_isTorsionFree L _
    intro h; rw [hD] at h; exact hdeg (Polynomial.natDegree_eq_zero_of_derivative_eq_zero h)
  have hDc : ∀ i, D.coeff i ∈ RA := by
    intro i; rw [hD, Polynomial.coeff_derivative]
    exact RA.mul_mem (hRA' _) (RA.add_mem (natCast_mem RA _) RA.one_mem)
  have hDb : D.eval b ≠ 0 :=
    hmin D hD0 hDc (hD ▸ Polynomial.natDegree_derivative_lt hdeg)
  obtain ⟨F, hF⟩ : ∃ F, F = D.eval b := ⟨_, rfl⟩
  have hex2 : ∃ m, PowerSeries.coeff m F ≠ 0 := by
    by_contra h; push_neg at h; exact hDb (hF ▸ PowerSeries.ext fun k => by simpa using h k)
  obtain ⟨m, hc, hlow⟩ : ∃ m, PowerSeries.coeff m F ≠ 0 ∧ ∀ i < m, PowerSeries.coeff i F = 0 :=
    ⟨Nat.find hex2, Nat.find_spec hex2, fun i hi => not_not.mp (Nat.find_min hex2 hi)⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = PowerSeries.coeff m F := ⟨_, rfl⟩
  rw [← hcdef] at hc
  refine ⟨insert c⁻¹ ((Finset.range (m+1)).image fun i => PowerSeries.coeff i b), ?_⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = Subring.closure ((A : Set L) ∪
      ↑(insert c⁻¹ ((Finset.range (m+1)).image fun i => PowerSeries.coeff i b))) := ⟨_, rfl⟩
  rw [← hBdef]
  have hAB : ∀ x ∈ A, x ∈ B := fun x hx => hBdef ▸ Subring.subset_closure (Or.inl hx)
  have hcB : c⁻¹ ∈ B := hBdef ▸ Subring.subset_closure (Or.inr (by simp))
  have hbB : ∀ i ≤ m, PowerSeries.coeff i b ∈ B := fun i hi =>
    hBdef ▸ Subring.subset_closure (Or.inr (by simp; exact Or.inr ⟨i, by omega, rfl⟩))
  obtain ⟨RB, hRBdef⟩ : ∃ RB : Subring (PowerSeries L), RB = (PowerSeries.map B.subtype).range :=
    ⟨_, rfl⟩
  have hRARB : ∀ f ∈ RA, f ∈ RB := fun f hf => by
    rw [hRBdef]; rw [hRAdef] at hf
    exact (mem_range_map_iff B f).2 fun k => hAB _ ((mem_range_map_iff A f).1 hf k)
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  rcases le_or_gt n m with hnm | hmn
  · exact hbB n hnm
  obtain ⟨u, hu⟩ : ∃ u : PowerSeries L,
      u = PowerSeries.mk fun k => if k < n then PowerSeries.coeff k b else 0 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : PowerSeries L,
      v = PowerSeries.mk fun k => PowerSeries.coeff (n + k) b := ⟨_, rfl⟩
  have hbuv : b = u + PowerSeries.X ^ n * v := by
    ext k
    rw [map_add, PowerSeries.coeff_X_pow_mul', hu, hv]
    simp only [PowerSeries.coeff_mk]
    by_cases h1 : k < n
    · rw [if_pos h1, if_neg (by omega), add_zero]
    · rw [if_neg h1, if_pos (by omega), zero_add, show n + (k - n) = k by omega]
  have huB : u ∈ RB := by
    rw [hRBdef]
    refine (mem_range_map_iff B u).2 fun k => ?_
    rw [hu, PowerSeries.coeff_mk]; split_ifs with h
    · exact ih k h
    · exact B.zero_mem
  have hRu : R.eval u ∈ RB := by
    rw [Polynomial.eval_eq_sum_range]
    exact RB.sum_mem fun i _ => RB.mul_mem (hRARB _ (hRA' i)) (RB.pow_mem huB _)
  have hdvd : PowerSeries.X ^ n ∣ F - D.eval u := by
    have h1 := Polynomial.sub_dvd_eval_sub b u D
    have h2 : b - u = PowerSeries.X ^ n * v := by rw [hbuv]; ring
    rw [h2, ← hF] at h1
    exact (dvd_mul_right _ _).trans h1
  obtain ⟨w, hw⟩ := hdvd
  obtain ⟨k, hk⟩ := R.binomExpansion u (PowerSeries.X ^ n * v)
  rw [← hbuv, hRb, ← hD] at hk
  have hDu : D.eval u = F - PowerSeries.X ^ n * w := by rw [← hw]; ring
  rw [hDu] at hk
  have key : 0 = R.eval u + PowerSeries.X ^ n * (F * v) +
      PowerSeries.X ^ (n + n) * (k * v ^ 2 - w * v) := by
    rw [hk]; ring
  have hc2 := congrArg (PowerSeries.coeff (n + m)) key
  rw [map_zero, map_add, map_add, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
    if_pos (by omega), if_neg (by omega), add_zero, Nat.add_sub_cancel_left] at hc2
  have hFv : PowerSeries.coeff m (F * v) = c * PowerSeries.coeff n b := by
    rw [PowerSeries.coeff_mul, Finset.sum_eq_single (m, 0)]
    · rw [← hcdef, hv, PowerSeries.coeff_mk, add_zero]
    · rintro ⟨i, j⟩ hij hne
      have hij' : i + j = m := by simpa using hij
      have him : i < m := by
        rcases Nat.lt_or_ge i m with h | h
        · exact h
        · exfalso; apply hne; simp only [Prod.mk.injEq]; omega
      rw [hlow i him, zero_mul]
    · intro h; exfalso; exact h (by simp)
  have hcn : c * PowerSeries.coeff n b ∈ B := by
    have e : c * PowerSeries.coeff n b = - PowerSeries.coeff (n + m) (R.eval u) := by
      linear_combination -hc2 - hFv
    rw [e]
    rw [hRBdef] at hRu
    exact B.neg_mem ((mem_range_map_iff B _).1 hRu _)
  have e2 : PowerSeries.coeff n b = c⁻¹ * (c * PowerSeries.coeff n b) := by
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [e2]; exact B.mul_mem hcB hcn

end GlobalTheory.AlgPowerSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinPieceUnitSetLevelSuccEqStatement
section
open GlobalTheory.KummerEisensteinGalois
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisensteinPiece_unitSet_level_succ_eq : ∀ (p : ℕ) [Fact p.Prime] (N n m k : ℕ) (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) (w w' v v' : ℤ × ℤ) (ζ : K) (X : Finset (GL (Fin 2) (ZMod (p ^ n)))), IsPrimitiveRoot ζ (N * p ^ (n + 1)) → 0 < N → ¬ p ∣ N → 1 ≤ m → m ≤ n → 3 ≤ k → ¬ (p : ℤ) ∣ c → ¬ (p : ℤ) ∣ d → (p : ℤ) * v.1 ≡ w.1 [ZMOD N] → (p : ℤ) * v.2 ≡ w.2 [ZMOD N] → (p : ℤ) * v'.1 ≡ w'.1 [ZMOD N] → (p : ℤ) * v'.2 ≡ w'.2 [ZMOD N] → (∀ γ ∈ X, ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0).val ∧ ¬ p ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0).val) → ∀ r : ℕ, pieceT N p (n + 1) m k ψ c d v v' ζ (Finset.univ.filter fun γ => Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ ∈ X) r = vp p (pieceT N p n m k ψ c d w w' (ζ ^ p) X) r := by
  first | exact @GlobalTheory.KummerEisensteinGalois.pieceT_unitSet_level_succ | exact GlobalTheory.KummerEisensteinGalois.pieceT_unitSet_level_succ | (intros; apply GlobalTheory.KummerEisensteinGalois.pieceT_unitSet_level_succ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfBettiKummerRelationPadicZero
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB

theorem gamma_le_gamma_of_dvd {K M : ℕ} (h : K ∣ M) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma M) :
    δ ∈ CongruenceSubgroup.Gamma K := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [map_intCast, map_one] using congrArg (ZMod.castHom h (ZMod K)) h1
  · simpa using congrArg (ZMod.castHom h (ZMod K)) h2
  · simpa using congrArg (ZMod.castHom h (ZMod K)) h3
  · simpa only [map_intCast, map_one] using congrArg (ZMod.castHom h (ZMod K)) h4

theorem mem_gam_of_mem_gamma {N l : ℕ} {δ : SL(2, ℤ)} (hN : δ ∈ CongruenceSubgroup.Gamma N)
    (hl : δ ∈ CongruenceSubgroup.Gamma l) : δ ∈ Gam N l := by
  rw [CongruenceSubgroup.Gamma_mem] at hN hl
  refine ⟨?_, ?_⟩
  · exact (CongruenceSubgroup.Gamma1_mem N δ).2 ⟨hN.1, hN.2.2.2, hN.2.2.1⟩
  · exact CongruenceSubgroup.Gamma0_mem.2 hl.2.2.1

theorem cls_pow_eq_zero {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (n : ℕ) (g : X.Kˣ) : X.cls l n (g ^ (l ^ n)) = 0 := by
  unfold Tower.cls
  rw [Submodule.Quotient.mk_eq_zero]
  have h : ((1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul (g ^ (l ^ n)) : X.Kl l) =
      ((l : ℤ_[l]) ^ n) • ((1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul g : X.Kl l) := by
    rw [ofMul_pow, TensorProduct.tmul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [h]
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n) Submodule.mem_top

theorem eq_zero_of_btZ_zero : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l : ℕ) [Fact l.Prime], 0 < N → ∀ b : X.Fn l, BtZ X N l b 0 → b = 0 := by
  intro Ω _ _ _ ε X hε hj N l hl hN b hb
  funext u
  apply AdicCompletion.ext
  intro n
  obtain ⟨χ, ⟨f, a, c, M₁, hM₁, hev, ⟨ha, hc, hc0, hroot⟩, hinv⟩, M₂, hM₂, hχ⟩ := hb n u
  have hlpos : 0 < l := hl.out.pos
  obtain ⟨g, hg⟩ := kummer_root_mem ε X hε hj (l ^ n) (pow_pos hlpos n) f a c (M₁ * M₂ * N * l)
    (by positivity) ha hc hc0 hroot (by
      intro γ hγ
      have h1 : γ ∈ CongruenceSubgroup.Gamma M₁ := gamma_le_gamma_of_dvd ⟨M₂ * N * l, by ring⟩ hγ
      have h2 : γ ∈ CongruenceSubgroup.Gamma M₂ := gamma_le_gamma_of_dvd ⟨M₁ * N * l, by ring⟩ hγ
      have h3 : γ ∈ CongruenceSubgroup.Gamma N := gamma_le_gamma_of_dvd ⟨M₁ * M₂ * l, by ring⟩ hγ
      have h4 : γ ∈ CongruenceSubgroup.Gamma l := gamma_le_gamma_of_dvd ⟨M₁ * M₂ * N, by ring⟩ hγ
      have h0 : χ γ = 0 := by
        have := hχ ⟨γ, mem_gam_of_mem_gamma h3 h4⟩ h2
        simpa using this.symm
      refine Filter.Germ.coe_eq.2 (Filter.eventually_of_mem (Filter.self_mem_codiscreteWithin Hs) fun z hz => ?_)
      have := hinv γ h1 z hz
      rw [h0] at this
      simpa using this)
  have : AdicCompletion.eval (idl l) (X.Kl l) n (b u) = 0 := by
    rw [hev, hg, cls_pow_eq_zero]
  exact this

end GlobalTheory.KZ.BettiB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvNormOpEqNrm
section
open GlobalTheory.Col PowerSeries

namespace GlobalTheory.Col

theorem ev_normOp_eq_nrm (R : Type) [CommRing R] (p m : ℕ) [hp : Fact p.Prime] (hm : 1 ≤ m)
    (hR : IsAdicComplete (Ideal.span {(p : R)}) R) (h : PowerSeries R) :
    ev R p m (normOp p h) = nrm p m hm (ev R p (m + 1) h) := by
  obtain ⟨b, hb⟩ := GlobalTheory.Col.exists_basis_one_add_X_pow R p hR
  letI iA : Algebra (PowerSeries R) (PowerSeries R) := (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
  letI iM : Module (PowerSeries R) (PowerSeries R) := @Algebra.toModule _ _ _ _ iA
  letI iS : SMul (PowerSeries R) (PowerSeries R) := iM.toSMul
  have F1 : ∀ x : PowerSeries R, ∑ i, phi (R := R) p hp.out.pos (b.repr x i) * (1 + X) ^ (i : ℕ) = x := by
    intro x
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb i]; rfl
  have F3 : ∀ (d : Fin p → PowerSeries R) (i : Fin p),
      b.repr (∑ j, phi (R := R) p hp.out.pos (d j) * (1 + X) ^ (j : ℕ)) i = d i := by
    intro d i
    have h1 : (∑ j, phi (R := R) p hp.out.pos (d j) * (1 + X) ^ (j : ℕ)) = b.equivFun.symm d := by
      rw [Module.Basis.equivFun_symm_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hb j]; rfl
    rw [h1, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have F2 : ∀ (a x : PowerSeries R) (i : Fin p),
      b.repr (phi (R := R) p hp.out.pos a * x) i = a * b.repr x i := by
    intro a x i
    have : phi (R := R) p hp.out.pos a * x = a • x := rfl
    rw [this, LinearEquiv.map_smul]; rfl

  letI iU : Algebra (lev R p m) (lev R p (m + 1)) := (up (R := R) p m hm).toAlgebra
  have hup : ∀ a : PowerSeries R, up (R := R) p m hm (ev R p m a) = ev R p (m + 1) (phi (R := R) p hp.out.pos a) :=
    fun a => rfl
  have hsm : ∀ (a : PowerSeries R) (y : PowerSeries R),
      ev R p (m + 1) (phi (R := R) p hp.out.pos a * y) = (ev R p m a) • ev R p (m + 1) y := by
    intro a y
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, hup, map_mul]
  let v : Fin p → lev R p (m + 1) := fun i => ev R p (m + 1) ((1 + X) ^ (i : ℕ))
  have hli : LinearIndependent (lev R p m) v := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    choose d hd using fun i => Ideal.Quotient.mk_surjective (g i)
    have hx : ev R p (m + 1) (∑ j, phi (R := R) p hp.out.pos (d j) * (1 + X) ^ (j : ℕ)) = 0 := by
      rw [← hg, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hsm, ← hd j]
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hx)
    rw [← phi_cyc (R := R) p m hm, mul_comm] at ha
    have := F3 d i
    rw [← ha, F2] at this
    rw [← hd i, ← this, map_mul]
    have h0 : ev R p m (cyc R p m) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rw [h0, zero_mul]
  have hsp : ⊤ ≤ Submodule.span (lev R p m) (Set.range v) := by
    intro z _
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    show ev R p (m + 1) y ∈ _
    rw [← F1 y, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' : Module.Basis (Fin p) (lev R p m) (lev R p (m + 1)) := Module.Basis.mk hli hsp
  have G : ∀ (y : PowerSeries R) (i : Fin p), b'.repr (ev R p (m + 1) y) i = ev R p m (b.repr y i) := by
    intro y i
    have e1 : ev R p (m + 1) y = b'.equivFun.symm (fun i => ev R p m (b.repr y i)) := by
      rw [Module.Basis.equivFun_symm_apply]
      conv_lhs => rw [← F1 y]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Module.Basis.mk_apply, hsm]
    rw [e1, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  unfold nrm normOp
  rw [Algebra.norm_eq_matrix_det b', Algebra.norm_eq_matrix_det b, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.mk_apply, ← map_mul, G, hb]

end GlobalTheory.Col
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgClosureAutomorphismRestrictingLocal
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.CuspDown

theorem exists_restrict : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ IsInt p (j x)) → ∀ g : Gal p Ωl, ∃ s : Ω ≃ₐ[ℚ] Ω, Stab A s ∧ ∀ x, g (j x) = j (s x) := by
  intro Ω _ _ _ p _ A Ωl _ _ hC j hA g
  haveI : CharZero Ωl := GlobalTheory.K5.Basic.charZero_of_isClo hC
  letI : Algebra Ω Ωl := j.toAlgebra
  haveI : IsScalarTower ℚ Ω Ωl := IsScalarTower.of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ Ωl), eq_ratCast (algebraMap ℚ Ω), map_ratCast]
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let gq : Ωl ≃ₐ[ℚ] Ωl := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun x => by
    simp only [eq_ratCast, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.coe_toEquiv, AlgEquiv.coe_ringEquiv]
    exact map_ratCast g x)
  have hc : ∀ x, g (j x) = j (gq.restrictNormal Ω x) := fun x => by
    have := AlgEquiv.restrictNormal_commutes gq Ω x
    rw [RingHom.algebraMap_toAlgebra] at this
    rw [this]; rfl
  refine ⟨gq.restrictNormal Ω, fun x => ?_, hc⟩
  rw [hA, hA, ← hc]
  constructor
  · intro h
    have := GlobalTheory.K5.Basic.isInt_gal g.symm h
    rwa [AlgEquiv.symm_apply_apply] at this
  · exact GlobalTheory.K5.Basic.isInt_gal g

end GlobalTheory.CuspDown
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCharacterAverageEigenvectorCompactSubgroupStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_character_average_eigenvector_compact_subgroup : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ → ∀ w : V, ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ j ∈ R, j ∈ H) ∧ IsEig π H θ (∑ j ∈ R, (θ j)⁻¹ • π j w) := by
  first | exact @GlobalTheory.PsType.avg_eig | exact GlobalTheory.PsType.avg_eig | (intros; apply GlobalTheory.PsType.avg_eig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCocycleExtensionOfNegCentralElementStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocycle_extension_of_neg_central_element : ∀ (G : Type) [Group G] (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (ρ : G → V →ₗ[R] V), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → IsUnit (2 : R) → ∀ (S : Submodule R V), (∀ g, ∀ v ∈ S, ρ g v ∈ S) → ∀ (Δ : Subgroup G), Δ.Normal → (∀ δ ∈ Δ, ∀ v, ρ δ v = v) → ∀ c : G, (∀ v ∈ S, ρ c v = -v) → (∀ g, c * g * c⁻¹ * g⁻¹ ∈ Δ) → ∀ φ : G → V, (∀ δ ∈ Δ, φ δ ∈ S) → (∀ δ ∈ Δ, ∀ δ' ∈ Δ, φ (δ * δ') = φ δ + φ δ') → (∀ g, ∀ δ ∈ Δ, ρ g (φ (g * δ * g⁻¹)) = φ δ) → ∃ z : G → V, (∀ g, z g ∈ S) ∧ (∀ g h, z (g * h) = ρ h (z g) + z h) ∧ ∀ δ ∈ Δ, z δ = φ δ := by
  first | exact @GlobalTheory.KZ.H3.exists_cocycle_extension_of_neg_action | exact GlobalTheory.KZ.H3.exists_cocycle_extension_of_neg_action | (intros; apply GlobalTheory.KZ.H3.exists_cocycle_extension_of_neg_action <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetPrimesMemValuationSubringOverStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_primes_mem_valuationSubring_over : ∀ {F : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] (s : Finset F), ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F, ((q : ℕ) : F) ∈ V.nonunits → ∀ x ∈ s, x ∈ V := by
  first | exact @GlobalTheory.exists_finset_primes_forall_mem_valuationSubring | exact GlobalTheory.exists_finset_primes_forall_mem_valuationSubring | (intros; apply GlobalTheory.exists_finset_primes_forall_mem_valuationSubring <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormalDeformationPowerSeriesSolutionStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formal_deformation_powerSeries_solution : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (I : Type) [Fintype I] (V : Submodule k A) (D P₀ : Ideal A) (Q : I → Ideal A) (f₀ : A), 2 ≤ N → P₀.IsMaximal → (FiniteDimensional k V ∧ (∀ v ∈ V, v ∈ D) ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, Q i ≠ P₀) ∧ (∀ i, ¬ D ≤ Q i) ∧ ¬ D ≤ P₀ ∧ f₀ ∈ V ∧ f₀ ≠ 0 ∧ Ideal.span {f₀} = P₀ * D * ∏ i, Q i ^ N ∧ (∀ u : A, ∃ v ∈ V, u - v ∈ P₀ * ∏ i, Q i ^ (N - 1))) → ∃ (ξ : A →ₐ[k] PowerSeries k) (Δ : I → ℕ → A →ₗ[k] PowerSeries k) (m : ℕ) (v : Fin m → A) (y : Fin m → PowerSeries k),
  Function.Injective ξ ∧ (∀ i, Δ i 0 1 = 1) ∧ (∀ i, (∀ l, ∀ u w : A, Δ i l (u * w) = ∑ p ∈ Finset.range (l + 1), l.choose p • (Δ i p u * Δ i (l - p) w))) ∧ (∀ i, ∃ π : A, Δ i 1 π = 1) ∧
  (∀ j, v j ∈ V) ∧ LinearIndependent k v ∧ (∃ j, IsUnit (y j)) ∧ ∑ j, y j * ξ (v j) = 0 ∧ (∀ i, ∀ l < N, ∑ j, y j * Δ i l (v j) = 0) ∧
  (∀ i i', i ≠ i' → ∃ u : A, IsUnit (Δ i 0 u - Δ i' 0 u)) ∧ (∀ i, ∃ u : A, IsUnit (Δ i 0 u - ξ u)) ∧ (∀ i, ∃ u ∈ D, IsUnit (Δ i 0 u)) ∧ (∃ u ∈ D, IsUnit (ξ u)) := by
  first | exact @GlobalTheory.FormalDeform.formal_deformation | exact GlobalTheory.FormalDeform.formal_deformation | (intros; apply GlobalTheory.FormalDeform.formal_deformation <;> assumption)
end

