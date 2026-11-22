import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0615
import GroundTheory.Brauer.BaseChangeCSA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0624
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0625
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LazardOneVariableExistsWittLift
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.LazardOne

theorem choose_pow_mul_add_modEq_one (p : ℕ) [hp : Fact p.Prime] :
    ∀ (s A B : ℕ), B < p ^ s → (p ^ s * A + B).choose B ≡ 1 [MOD p] := by
  intro s
  induction s with
  | zero =>
    intro A B hB
    have : B = 0 := by simpa using hB
    subst this
    simp [Nat.ModEq]
  | succ s ih =>
    intro A B hB
    have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (p ^ (s + 1) * A + B) B p _
    have e0 : p ^ (s + 1) * A + B = B + p * (p ^ s * A) := by ring
    rw [e0, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hp.out.pos, Nat.choose_self,
      one_mul] at h
    have hB' : B / p < p ^ s := by
      rw [Nat.div_lt_iff_lt_mul hp.out.pos, ← pow_succ]; exact hB
    have := ih A (B / p) hB'
    rw [add_comm (p ^ s * A)] at this
    rw [e0]; exact h.trans this

theorem not_dvd_choose_pow_mul_add (p : ℕ) [hp : Fact p.Prime] (s A B : ℕ) (hB : B < p ^ s) :
    ¬ p ∣ (p ^ s * A + B).choose B := by
  intro hd
  have h0 := (Nat.modEq_zero_iff_dvd.2 hd).symm.trans (choose_pow_mul_add_modEq_one p s A B hB)
  exact hp.out.not_dvd_one (Nat.modEq_zero_iff_dvd.1 h0.symm)

variable (p : ℕ) [hp : Fact p.Prime] {k : Type} [Field k] [CharP k p]

theorem eq_zero_of_eq_zero (N : ℕ) (c : ℕ → k)
    (hsym : ∀ i, i ≤ N → c i = c (N - i))
    (hrel : ∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N →
      c (i + j) * ((i + j).choose i : k) = c i * ((j + l).choose j : k))
    (s K : ℕ) (hN : N = p ^ s * K) (hK2 : 2 ≤ K)
    (hK : ∀ u, 0 < u → u < K → ¬ p ∣ u ∨ ¬ p ∣ (K - u))
    (h0 : c (p ^ s) = 0) : ∀ n, 0 < n → n < N → c n = 0 := by
  have hA : ∀ i n, c i = 0 → 0 < i → i < n → n < N → ¬ p ∣ n.choose i → c n = 0 := by
    intro i n hi hi0 hin hnN hd
    have h := hrel i (n - i) (N - n) hi0 (by omega) (by omega) (by omega)
    rw [show i + (n - i) = n by omega, hi, zero_mul] at h
    have hne : ((n.choose i : ℕ) : k) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff k p]; exact hd
    exact (mul_eq_zero.1 h).resolve_right hne
  have hq : 0 < p ^ s := pow_pos hp.out.pos s
  have hb1 : ∀ u, 0 < u → u < K → ¬ p ∣ u → c (p ^ s * u) = 0 := by
    intro u hu huK hpu
    rcases Nat.lt_or_ge 1 u with h1 | h1
    · refine hA (p ^ s) (p ^ s * u) h0 hq (lt_mul_of_one_lt_right hq h1) ?_
        (GlobalTheory.Honda.Lazard.not_dvd_choose_pow_mul hp.out u hpu s)
      rw [hN]; exact Nat.mul_lt_mul_of_pos_left huK hq
    · have : u = 1 := by omega
      subst this; simpa using h0
  have hb : ∀ u, 0 < u → u < K → c (p ^ s * u) = 0 := by
    intro u hu huK
    rcases hK u hu huK with h | h
    · exact hb1 u hu huK h
    · have h' := hb1 (K - u) (by omega) (by omega) h
      have hle : p ^ s * (K - u) ≤ N := by rw [hN]; exact Nat.mul_le_mul_left _ (by omega)
      rw [hsym _ hle] at h'
      rwa [show N - p ^ s * (K - u) = p ^ s * u by
        rw [hN, ← Nat.mul_sub]; congr 1; omega] at h'
  intro n hn hnN
  obtain ⟨u, v, hvlt, rfl⟩ : ∃ u v, v < p ^ s ∧ n = p ^ s * u + v :=
    ⟨n / p ^ s, n % p ^ s, Nat.mod_lt _ hq, (Nat.div_add_mod n (p ^ s)).symm⟩
  have huK : u < K := by
    apply Nat.lt_of_mul_lt_mul_left (a := p ^ s)
    rw [← hN]; omega
  rcases Nat.eq_zero_or_pos v with hv | hv
  · subst hv
    rw [add_zero] at hn ⊢
    rcases Nat.eq_zero_or_pos u with hu | hu
    · subst hu; simp at hn
    · exact hb u hu huK
  · have hK1 : c (p ^ s * (K - 1)) = 0 := hb (K - 1) (by omega) (by omega)
    have e1 : p ^ s * K = p ^ s * (K - 1) + p ^ s := by
      rw [← Nat.mul_succ]; congr 1; omega
    have hNv : N - v = p ^ s * (K - 1) + (p ^ s - v) := by omega
    have hpos : 0 < p ^ s * (K - 1) := Nat.mul_pos hq (by omega)
    have hcNv : c (N - v) = 0 := by
      rw [hNv]
      refine hA (p ^ s * (K - 1)) _ hK1 hpos (by omega) (by omega) ?_
      rw [Nat.choose_symm_add]
      exact not_dvd_choose_pow_mul_add p s (K - 1) (p ^ s - v) (by omega)
    have hcv : c v = 0 := by rw [hsym v (by omega), hcNv]
    rcases Nat.eq_zero_or_pos u with hu | hu
    · subst hu; simpa using hcv
    · have hsu : 0 < p ^ s * u := Nat.mul_pos hq hu
      exact hA v _ hcv hv (by omega) hnN (not_dvd_choose_pow_mul_add p s u v hvlt)

theorem exists_scalar (N : ℕ) (a : ℕ → k)
    (hsym : ∀ i, i ≤ N → a i = a (N - i))
    (hrel : ∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N →
      a (i + j) * ((i + j).choose i : k) = a i * ((j + l).choose j : k))
    (g : ℕ) (hg : 0 < g) (hdiv : ∀ i, 0 < i → i < N → g ∣ N.choose i)
    (s K : ℕ) (hN : N = p ^ s * K) (hK2 : 2 ≤ K)
    (hK : ∀ u, 0 < u → u < K → ¬ p ∣ u ∨ ¬ p ∣ (K - u))
    (hb : ((N.choose (p ^ s) / g : ℕ) : k) ≠ 0) :
    ∃ z : k, ∀ i, 0 < i → i < N → a i = z * ((N.choose i / g : ℕ) : k) := by
  set b : ℕ → k := fun i => ((N.choose i / g : ℕ) : k) with hbdef
  have hbsym : ∀ i, i ≤ N → b (N - i) = b i := by
    intro i hi; simp only [hbdef, Nat.choose_symm hi]
  have hbrel : ∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N →
      b (i + j) * ((i + j).choose i : k) = b i * ((j + l).choose j : k) := by
    intro i j l hi hj hl hs
    obtain ⟨x, hx⟩ := hdiv (i + j) (by omega) (by omega)
    obtain ⟨y, hy⟩ := hdiv i hi (by omega)
    have hm := Nat.choose_mul (n := N) (k := i + j) (s := i) (by omega)
    rw [show N - i = j + l by omega, show i + j - i = j by omega, hx, hy, mul_assoc, mul_assoc] at hm
    have hm' := Nat.eq_of_mul_eq_mul_left hg hm
    simp only [hbdef, hx, hy, Nat.mul_div_cancel_left _ hg]
    rw [← Nat.cast_mul, ← Nat.cast_mul, hm']
  refine ⟨a (p ^ s) / b (p ^ s), ?_⟩
  have key := eq_zero_of_eq_zero p N (fun i => a i - a (p ^ s) / b (p ^ s) * b i) ?_ ?_ s K hN hK2 hK ?_
  · intro i hi hiN
    exact sub_eq_zero.1 (key i hi hiN)
  · intro i hi
    rw [hsym i hi, hbsym i hi]
  · intro i j l hi hj hl hs
    rw [sub_mul, sub_mul, hrel i j l hi hj hl hs, mul_assoc, mul_assoc, hbrel i j l hi hj hl hs]
  · rw [div_mul_cancel₀ _ hb, sub_self]

theorem exists_lift : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : ℕ)
    (a : ℕ → k), 2 ≤ N → (∀ i, i ≤ N → a i = a (N - i)) →
    (∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N →
      a (i + j) * ((i + j).choose i : k) = a i * ((j + l).choose j : k)) →
    ∃ t : Fr p k, ∀ i, 0 < i → i < N → ∃ w : WittVector p k,
      t * (N.choose i : Fr p k) = algebraMap (WittVector p k) (Fr p k) w ∧
      WittVector.constantCoeff w = a i := by
  intro p _ k _ _ _ N a hN2 hsym hrel
  have hp : p.Prime := Fact.out
  obtain ⟨g, hg, hg1, hdiv, z, hz⟩ : ∃ g, 0 < g ∧ (g = 1 ∨ g = p) ∧
      (∀ i, 0 < i → i < N → g ∣ N.choose i) ∧
      ∃ z : k, ∀ i, 0 < i → i < N → a i = z * ((N.choose i / g : ℕ) : k) := by
    obtain ⟨r, m, hm, hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : N ≠ 0) p hp.one_lt.ne'
    by_cases hm1 : m = 1
    · subst hm1
      rw [mul_one] at hNe
      have hr : 0 < r := by
        rcases Nat.eq_zero_or_pos r with h | h
        · subst h; simp at hNe; omega
        · exact h
      have hdv : ∀ i, 0 < i → i < N → p ∣ N.choose i := by
        intro i hi hiN; rw [hNe] at hiN ⊢; exact hp.dvd_choose_pow (by omega) (by omega)
      refine ⟨p, hp.pos, Or.inr rfl, hdv, ?_⟩
      obtain ⟨c, hc, hch⟩ := GlobalTheory.Honda.Lazard.choose_prime_pow_pred hp r hr
      refine exists_scalar p N a hsym hrel p hp.pos hdv (r - 1) p ?_ hp.two_le ?_ ?_
      · rw [hNe, ← pow_succ]; congr 1; omega
      · intro u hu hup; left; exact fun h => absurd (Nat.le_of_dvd hu h) (by omega)
      · rw [hNe, hch, Nat.mul_div_cancel_left _ hp.pos, Ne, CharP.cast_eq_zero_iff k p]; exact hc
    · have hm0 : m ≠ 0 := by rintro rfl; simp at hNe; omega
      have hm2 : 2 ≤ m := by omega
      refine ⟨1, one_pos, Or.inl rfl, fun _ _ _ => one_dvd _, ?_⟩
      refine exists_scalar p N a hsym hrel 1 one_pos (fun _ _ _ => one_dvd _) r m hNe hm2 ?_ ?_
      · intro u hu huK
        by_contra h
        push_neg at h
        have := Nat.dvd_add h.2 h.1
        rw [Nat.sub_add_cancel huK.le] at this
        exact hm this
      · rw [Nat.div_one, hNe, Ne, CharP.cast_eq_zero_iff k p]
        exact GlobalTheory.Honda.Lazard.not_dvd_choose_pow_mul hp m hm r
  have hgW : ((g : ℕ) : WittVector p k) ≠ 0 := by
    rcases hg1 with h | h
    · subst h; simp
    · rw [h]
      intro h0
      have := congrArg (fun x : WittVector p k => x.coeff 1) h0
      simp only [WittVector.coeff_p_one, WittVector.zero_coeff] at this
      exact one_ne_zero this
  have hgF : ((g : ℕ) : Fr p k) ≠ 0 := by
    rw [← map_natCast (algebraMap (WittVector p k) (Fr p k)), Ne,
      map_eq_zero_iff _ (IsFractionRing.injective (WittVector p k) (Fr p k))]
    exact hgW
  refine ⟨algebraMap (WittVector p k) (Fr p k) (WittVector.teichmuller p z) / (g : Fr p k), ?_⟩
  intro i hi hiN
  obtain ⟨q, hq⟩ := hdiv i hi hiN
  refine ⟨WittVector.teichmuller p z * (q : WittVector p k), ?_, ?_⟩
  · rw [hq, Nat.cast_mul, map_mul, map_natCast]
    field_simp
  · rw [hz i hi hiN, hq, Nat.mul_div_cancel_left _ hg, map_mul, map_natCast,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

end GlobalTheory.LazardOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyEqOfAevalOfLinearIndependent
section
open scoped TensorProduct
open Polynomial

namespace GlobalTheory.SkNoFactor

theorem minpoly_eq_of_aeval_of_linearIndependent {L A : Type} [Field L] [Ring A] [Algebra L A]
    (p : L[X]) (y : A) (hm : p.Monic) (hy : aeval y p = 0)
    (hind : ∀ c : Fin p.natDegree → L, ∑ j, c j • y ^ (j : ℕ) = 0 → c = 0) : minpoly L y = p := by
  have hi : IsIntegral L y := ⟨p, hm, by rwa [← aeval_def]⟩
  have hdvd : minpoly L y ∣ p := minpoly.dvd L y hy
  have hle : p.natDegree ≤ (minpoly L y).natDegree := by
    by_contra hlt
    push_neg at hlt
    have hsum := aeval_eq_sum_range' hlt y
    rw [minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly L y).coeff i • y ^ i)] at hsum
    have hc := hind (fun i => (minpoly L y).coeff i) hsum.symm
    apply minpoly.ne_zero hi
    ext i
    rw [coeff_zero]
    by_cases h : i < p.natDegree
    · exact congrFun hc ⟨i, h⟩
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hi) hdvd hle
  rw [this, hm.leadingCoeff, C_1, one_mul]

theorem minpoly_one_tmul {F B : Type} [Field F] [Ring B] [Algebra F B] [FiniteDimensional F B]
    (K : Type) [Field K] [Algebra F K] (y : B) :
    minpoly K ((1 : K) ⊗ₜ[F] y) = (minpoly F y).map (algebraMap F K) := by
  set z : K ⊗[F] B := (1 : K) ⊗ₜ[F] y with hz
  have hzi : IsIntegral K z := IsIntegral.of_finite K z
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  have hzr : z = Algebra.TensorProduct.includeRight y := rfl
  have hdvd : minpoly K z ∣ (minpoly F y).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hzr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := GlobalTheory.CentSep.natDegree_minpoly_le_baseChange K y hzi
  have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzi) hdvd
    (by rw [natDegree_map]; exact hge)
  rw [this, ((minpoly.monic hyi).map _).leadingCoeff, C_1, one_mul]

theorem exists_unit_conj_baseChange : ∀ (S F B : Type) [Field S] [CharZero S] [Field F] [Algebra ℚ F]
    [FiniteDimensional ℚ F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B]
    [FiniteDimensional F B] (n : ℕ), Module.finrank F B = n ^ 2 → ∀ (x₀ : B) (x : S ⊗[ℚ] B),
    (minpoly F x₀).Separable → (minpoly F x₀).natDegree = n →
    (∑ i ∈ Finset.range (n + 1), ((1 : S) ⊗ₜ[ℚ] algebraMap F B ((minpoly F x₀).coeff i)) * x ^ i = 0) →
    (∀ c : Fin n → S ⊗[ℚ] F, ∑ j, Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom ℚ F B) (c j) *
      x ^ (j : ℕ) = 0 → c = 0) →
    ∃ g : (S ⊗[ℚ] B)ˣ, (g : S ⊗[ℚ] B) * ((1 : S) ⊗ₜ[ℚ] x₀) = x * g := by
  intro S F B _ _ _ _ _ _ _ _ _ _ _ _ n hn x₀ x hsep hdeg hP hind
  classical
  obtain ⟨ι, _, L, _, _, _, Φ, ψ, hΦ1, hΦ2⟩ := GlobalTheory.T.tensor_rat_algebra_decomp_factorwise S F B
  have hcomp : ∀ i, ∃ u : (L i ⊗[F] B)ˣ, (u : L i ⊗[F] B) * ((1 : L i) ⊗ₜ[F] x₀) = Φ x i * u := by
    intro i
    haveI : Infinite (L i) := Infinite.of_injective (Nat.cast : ℕ → L i) Nat.cast_injective
    have hn' : Module.finrank (L i) (L i ⊗[F] B) = n ^ 2 := by rw [Module.finrank_baseChange, hn]
    have h0 : minpoly (L i) ((1 : L i) ⊗ₜ[F] x₀) = (minpoly F x₀).map (algebraMap F (L i)) :=
      minpoly_one_tmul (L i) x₀
    have hmonic : ((minpoly F x₀).map (algebraMap F (L i))).Monic :=
      (minpoly.monic (IsIntegral.of_finite F x₀)).map _
    have hdegm : ((minpoly F x₀).map (algebraMap F (L i))).natDegree = n := by rw [natDegree_map, hdeg]
    have hcoef : ∀ c : F, Φ ((1 : S) ⊗ₜ[ℚ] algebraMap F B c) i =
        algebraMap (L i) (L i ⊗[F] B) (algebraMap F (L i) c) := by
      intro c
      rw [hΦ1]
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
        ← Algebra.TensorProduct.one_def]
    have hy : aeval (Φ x i) ((minpoly F x₀).map (algebraMap F (L i))) = 0 := by
      have := congrArg (fun w => Φ w i) hP
      simp only [map_sum, map_mul, map_pow, map_zero, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply,
        Pi.zero_apply, hcoef] at this
      rw [aeval_eq_sum_range' (n := n + 1) (by rw [hdegm]; omega), ← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coeff_map, Algebra.smul_def]
    have hli : ∀ c : Fin ((minpoly F x₀).map (algebraMap F (L i))).natDegree → L i,
        ∑ j, c j • Φ x i ^ (j : ℕ) = 0 → c = 0 := by
      rw [hdegm]
      intro c hc
      have hz := hind (fun j => ψ.symm (Pi.single i (c j))) (by
        apply Φ.injective
        rw [map_zero]
        funext k
        simp only [map_sum, map_mul, map_pow, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, hΦ2,
          RingEquiv.apply_symm_apply, Pi.zero_apply]
        by_cases hk : k = i
        · subst hk
          simpa [Pi.single_eq_same, Algebra.smul_def] using hc
        · simp [Pi.single_eq_of_ne hk])
      funext j
      have := congrArg (fun w => ψ (w j) i) hz
      simpa using this
    have hmin : minpoly (L i) (Φ x i) = minpoly (L i) ((1 : L i) ⊗ₜ[F] x₀) := by
      rw [h0]; exact minpoly_eq_of_aeval_of_linearIndependent _ _ hmonic hy hli
    exact GlobalTheory.LKInv.exists_unit_conj_of_minpoly_eq (L i) (L i ⊗[F] B) n hn' _ _
      (by rw [h0]; exact hsep.map) (by rw [h0, hdegm]) hmin
  choose u hu using hcomp
  let v : ((i : ι) → L i ⊗[F] B)ˣ := MulEquiv.piUnits.symm u
  refine ⟨Units.map Φ.symm.toMonoidHom v, ?_⟩
  apply Φ.injective
  rw [map_mul, map_mul]
  funext i
  simp [v, hΦ1, hu i]

end GlobalTheory.SkNoFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesReductionModPrimeRules
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.RedRules

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (σ : Type)

theorem inj : Function.Injective (algebraMap (WittVector p k) (Fr p k)) :=
  IsFractionRing.injective _ _

theorem coeff_smul' (r : WittVector p k) (f : MvPowerSeries σ (Fr p k)) (α : σ →₀ ℕ) :
    coeff α (r • f) = algebraMap _ (Fr p k) r * coeff α f := by
  change r • coeff α f = _
  rw [Algebra.smul_def]

theorem intBy_one_iff (f : MvPowerSeries σ (Fr p k)) :
    f ∈ intBy p k σ 1 ↔ ∃ g, Red p f g := by
  constructor
  · intro hf
    choose w hw using hf
    refine ⟨fun α => WittVector.constantCoeff (w α), fun α => ⟨w α, ?_, rfl⟩⟩
    rw [hw α, one_mul]
  · rintro ⟨g, hg⟩ α
    obtain ⟨w, hw, -⟩ := hg α
    exact ⟨w, by rw [one_mul, hw]⟩

theorem red_unique (f : MvPowerSeries σ (Fr p k)) (g g' : MvPowerSeries σ k)
    (h : Red p f g) (h' : Red p f g') : g = g' := by
  ext α
  obtain ⟨w, hw, hg⟩ := h α
  obtain ⟨w', hw', hg'⟩ := h' α
  have : w = w' := inj p k (hw.symm.trans hw')
  rw [← hg, ← hg', this]

theorem red_lift (g : MvPowerSeries σ k) : Red p (Katz.lift p g) g := fun α =>
  ⟨WittVector.teichmuller p (coeff α g), coeff_lift p g α, by
    rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩

theorem red_add_sub (f f' : MvPowerSeries σ (Fr p k)) (g g' : MvPowerSeries σ k)
    (h : Red p f g) (h' : Red p f' g') : Red p (f + f') (g + g') ∧ Red p (f - f') (g - g') := by
  constructor
  · intro α
    obtain ⟨w, hw, hg⟩ := h α
    obtain ⟨w', hw', hg'⟩ := h' α
    exact ⟨w + w', by rw [map_add, map_add, hw, hw'], by rw [map_add, map_add, hg, hg']⟩
  · intro α
    obtain ⟨w, hw, hg⟩ := h α
    obtain ⟨w', hw', hg'⟩ := h' α
    exact ⟨w - w', by rw [map_sub, map_sub, hw, hw'], by rw [map_sub, map_sub, hg, hg']⟩

theorem red_smul (r : WittVector p k) (f : MvPowerSeries σ (Fr p k)) (g : MvPowerSeries σ k)
    (h : Red p f g) : Red p (r • f) (WittVector.constantCoeff r • g) := by
  intro α
  obtain ⟨w, hw, hg⟩ := h α
  refine ⟨r * w, ?_, ?_⟩
  · rw [coeff_smul', hw, map_mul]
  · rw [map_mul, hg, MvPowerSeries.coeff_smul]

theorem constantCoeff_p_mul (v : WittVector p k) :
    WittVector.constantCoeff ((p : WittVector p k) * v) = 0 := by
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem exists_p_mul [PerfectRing k p] (w : WittVector p k) (hw : WittVector.constantCoeff w = 0) :
    ∃ v, w = (p : WittVector p k) * v := by
  by_cases h0 : w = 0
  · exact ⟨0, by rw [h0, mul_zero]⟩
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul w h0
  cases m with
  | zero =>
    rw [pow_zero, one_mul, WittVector.constantCoeff_apply] at hw
    exact absurd hw hb
  | succ m => exact ⟨(p : WittVector p k) ^ m * b, by rw [pow_succ, mul_comm _ (p : WittVector p k), mul_assoc]⟩

theorem intBy_p_iff [PerfectRing k p] (f : MvPowerSeries σ (Fr p k)) :
    f ∈ intBy p k σ p ↔ Red p f 0 := by
  constructor
  · intro hf α
    obtain ⟨v, hv⟩ := hf α
    exact ⟨_, hv, by rw [constantCoeff_p_mul, map_zero]⟩
  · intro hf α
    obtain ⟨w, hw, h0⟩ := hf α
    rw [map_zero] at h0
    obtain ⟨v, rfl⟩ := exists_p_mul p k w h0
    exact ⟨v, hw⟩

theorem intBy_iff (c : WittVector p k) (f : MvPowerSeries σ (Fr p k)) :
    f ∈ intBy p k σ c ↔ ∃ g ∈ intBy p k σ 1, f = c • g := by
  constructor
  · intro hf
    choose w hw using hf
    refine ⟨(fun α => algebraMap _ (Fr p k) (w α) : MvPowerSeries σ (Fr p k)), fun α => ⟨w α, by rw [one_mul]; rfl⟩, ?_⟩
    ext α
    rw [hw α, map_mul]
    exact (coeff_smul' p k σ c (fun α => algebraMap _ (Fr p k) (w α)) α).symm
  · rintro ⟨g, hg, rfl⟩ α
    obtain ⟨w, hw⟩ := hg α
    exact ⟨w, by rw [coeff_smul', hw, one_mul, map_mul]⟩

end GlobalTheory.Katz.RedRules

open GlobalTheory.Katz.RedRules in
theorem GlobalTheory.Katz.red_rules : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ : Type), (∀ (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ 1 ↔ ∃ g, Red p f g) ∧ (∀ (f : MvPowerSeries (σ) (Fr p k)) g g', Red p f g → Red p f g' → g = g') ∧ (∀ g : MvPowerSeries σ k, Red p (Katz.lift p g) g) ∧ (∀ (f f' : MvPowerSeries (σ) (Fr p k)) g g', Red p f g → Red p f' g' → Red p (f + f') (g + g') ∧ Red p (f - f') (g - g')) ∧ (∀ (r : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)) g, Red p f g → Red p (r • f) (WittVector.constantCoeff r • g)) ∧ (∀ f : MvPowerSeries (σ) (Fr p k), f ∈ intBy p k σ p ↔ Red p f 0) ∧ (∀ (c : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ c ↔ ∃ g ∈ intBy p k σ 1, f = c • g) := by
  intro p _ k _ _ _ σ
  exact ⟨intBy_one_iff p k σ, red_unique p k σ, red_lift p k σ, red_add_sub p k σ, red_smul p k σ,
    intBy_p_iff p k σ, intBy_iff p k σ⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyStructureSheafCohomologyModelOfQuasiIsoStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_structureSheafCohomologyModel_of_quasiIso : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (K C : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ C), (∀ (S : Type) [CommRing S] [Algebra R S], QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R S)).mapHomologicalComplex _).map φ)) → Model s C → Nonempty (Model s K) := by
  first | exact @GlobalTheory.AbCoh.nonempty_model_of_quasiIso | exact GlobalTheory.AbCoh.nonempty_model_of_quasiIso | (intros; apply GlobalTheory.AbCoh.nonempty_model_of_quasiIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

variable {p : ℕ} [Fact p.Prime]

theorem projective_La_int (D : Datum p) :
    letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
    Module.Projective (𝓞 D.F) D.La := by
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  haveI := D.freeLa
  haveI := D.finLa
  have htor : Submodule.torsion (𝓞 D.F) D.La = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have ha0 : (a : 𝓞 D.F) ≠ 0 := nonZeroDivisors.ne_zero a.2
    have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) ha0 (Ideal.mem_span_singleton_self (a : 𝓞 D.F))
      (Algebra.IsIntegral.isIntegral (R := ℤ) (a : 𝓞 D.F))
    obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at he
    obtain ⟨d, hd⟩ := he
    have h1 : e • x = 0 := by
      have : (algebraMap ℤ (𝓞 D.F) e) • x = e • x := by
        rw [algebraMap_smul]
      rw [← this, ← hd, mul_smul]
      change d • (a • x) = 0
      rw [hax, smul_zero]
    rcases smul_eq_zero.1 h1 with h | h
    · exact absurd h he0
    · exact (Submodule.mem_bot _).2 h
  haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.of_restrictScalars_finite ℤ (𝓞 D.F) D.La
  have : Module.Flat (𝓞 D.F) D.La := (IsDedekindDomain.flat_iff_torsion_eq_bot).2 htor
  have := Module.finitePresentation_of_finite (𝓞 D.F) D.La
  exact Module.Flat.projective_of_finitePresentation

end GlobalTheory.UPel.HT.EtLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderSurjectsMatrixAlgebraModPrimePowerStatement
section
open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.order_surjects_matrix_algebra_mod_prime_power : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal →
    (p : 𝓞 D.F) ∈ w0 →
    ∃ φ : D.O →ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⧸ w0 ^ r), Function.Surjective φ ∧
      ∀ b, φ b = 0 → b ∈ (w0 ^ r) • (⊤ : Submodule (𝓞 D.F) D.O) := by
  first | (exact @GlobalTheory.UPel.HT.MatRed.exists_matRed) | (exact GlobalTheory.UPel.HT.MatRed.exists_matRed) | (intros; apply GlobalTheory.UPel.HT.MatRed.exists_matRed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerPullbackSectionExistsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_pullback_section_exists : ∀ {X Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (g : X ⟶ Z₂) (a : ℤ) (α : LB.Gen (LB.div (powPull M g a) (powPull L f a))), α.IsGen → L.IsLB → M.IsLB → ∀ σ : LB.Sec (powPull M g a), ∃ s : LB.Sec (powPull L f a), ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι), (X.presheaf.map (homOfLE (inf_le_left : LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤ LB.wchart M (fun _ : Fin 1 => g) p.1)).op).hom (σ.f p.1) = (show Γ(X, LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2) from (α.s p).val) * (X.presheaf.map (homOfLE (inf_le_right : LB.wchart M (fun _ : Fin 1 => g) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤ LB.wchart L (fun _ : Fin 1 => f) p.2)).op).hom (s.f p.2) := by
  first | exact @GlobalTheory.HomFixMat.divSec_exists | exact GlobalTheory.HomFixMat.divSec_exists | (intros; apply GlobalTheory.HomFixMat.divSec_exists <;> assumption)
end

