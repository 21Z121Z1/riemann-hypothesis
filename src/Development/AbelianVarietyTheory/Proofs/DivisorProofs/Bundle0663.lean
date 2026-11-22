import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharpolyMemVirtualCharactersGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0379
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0567
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0637
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0639
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHasPAdicPowerSeriesValueOfDiffCoeffs
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.ValEx

theorem nat_bound (p N m : ℕ) (hp : 2 ≤ p) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ a v : ℕ, M ≤ a → p ^ v ≤ a → N * (m + v) ≤ a := by
  set T := 2 * N + m + 1 with hT
  have hT2 : T < 2 ^ T := Nat.lt_two_pow_self
  have hA : ∀ v, 2 * T ≤ v → N * (m + v) ≤ 2 ^ v := by
    intro v hv
    induction v, hv using Nat.le_induction with
    | base =>
      have hNT : N ≤ T := by omega
      have h1 : N * (m + 2 * T) ≤ T * T := by nlinarith [Nat.mul_le_mul_right m hNT]
      have h2 : T * T ≤ 2 ^ T * 2 ^ T := Nat.mul_le_mul hT2.le hT2.le
      calc N * (m + 2 * T) ≤ T * T := h1
        _ ≤ 2 ^ T * 2 ^ T := h2
        _ = 2 ^ (2 * T) := by rw [← pow_add, two_mul]
    | succ v hv ih =>
      have h3 : N ≤ 2 ^ v := by
        have : 2 ^ T ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      rw [pow_succ]; nlinarith
  refine ⟨N * (m + 2 * T) + 1, by omega, fun a v ha hv => ?_⟩
  by_cases hvK : 2 * T ≤ v
  · calc N * (m + v) ≤ 2 ^ v := hA v hvK
      _ ≤ p ^ v := Nat.pow_le_pow_left hp v
      _ ≤ a := hv
  · have : N * (m + v) ≤ N * (m + 2 * T) := Nat.mul_le_mul_left _ (by omega)
    omega

def img (B : Type) {Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] (p m : ℕ) : AddSubgroup Q where
  carrier := {x | ∃ b : B, x = algebraMap B Q ((p : B) ^ m * b)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by rw [mul_add, map_add]⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, by rw [mul_neg, map_neg]⟩

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type} [Fintype σ] [DecidableEq σ]

def box (σ : Type) [Fintype σ] (n : ℕ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => n

def psum (z : σ → B) (f : MvPowerSeries σ Q) (n : ℕ) : Q :=
  MvPolynomial.eval (fun i => algebraMap B Q (z i)) (trunc' Q (box σ n) f)

theorem psum_eq (z : σ → B) (f : MvPowerSeries σ Q) (n : ℕ) :
    psum z f n = ∑ α ∈ Finset.Iic (box σ n),
      coeff α f * algebraMap B Q (α.prod fun i e => z i ^ e) := by
  simp only [psum, trunc', truncFinset_apply, map_sum, MvPolynomial.eval_monomial]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_finsuppProd]
  simp [map_pow]

theorem exists_lt_of_not_mem_box {n : ℕ} {α : σ →₀ ℕ} (h : α ∉ Finset.Iic (box σ n)) :
    ∃ i, n < α i := by
  simpa [box, Finset.mem_Iic, Finsupp.le_def] using h

theorem box_mono {n n' : ℕ} (h : n ≤ n') : Finset.Iic (box σ n) ⊆ Finset.Iic (box σ n') :=
  Finset.Iic_subset_Iic.2 (Finsupp.le_def.2 fun i => by simpa [box] using h)

theorem term_mem (p : ℕ) [hp : Fact p.Prime] (hunit : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B))
    (z : σ → B) (hz : ∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) (f : MvPowerSeries σ Q)
    (hf : DIn (⊤ : Ideal B) f) (m : ℕ) :
    ∃ M : ℕ, ∀ (α : σ →₀ ℕ) (i : σ), M ≤ α i →
      coeff α f * algebraMap B Q (α.prod fun i e => z i ^ e) ∈ img B p m := by
  choose Nf hNf using hz
  set N := ∑ i, Nf i
  have hN : ∀ i, (p : B) ∣ z i ^ N := fun i => (hNf i).trans
    (pow_dvd_pow _ (Finset.single_le_sum (fun j _ => Nat.zero_le (Nf j)) (Finset.mem_univ i)))
  obtain ⟨M, hM1, hM⟩ := nat_bound p N m hp.out.two_le
  refine ⟨M, fun α i hi => ?_⟩
  have ha0 : α i ≠ 0 := by omega
  obtain ⟨v, u, hu, hau⟩ := Nat.exists_eq_pow_mul_and_not_dvd ha0 p hp.out.ne_one
  have hcop : Nat.Coprime u p := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hu)
  obtain ⟨U, hU⟩ := hunit u hcop
  have hle : N * (m + v) ≤ α i := hM (α i) v hi (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) ⟨u, hau⟩)
  have hdz : (p : B) ^ (m + v) ∣ z i ^ (α i) :=
    (pow_dvd_pow_of_dvd (hN i) (m + v)).trans (by rw [← pow_mul]; exact pow_dvd_pow _ hle)
  have hprod : z i ^ (α i) ∣ α.prod fun j e => z j ^ e := by
    have hi' : i ∈ α.support := Finsupp.mem_support_iff.2 ha0
    unfold Finsupp.prod
    exact Finset.dvd_prod_of_mem (fun j => z j ^ α j) hi'
  obtain ⟨r, hr⟩ := hdz.trans hprod
  obtain ⟨b, -, hb⟩ := hf α i
  refine ⟨b * ↑U⁻¹ * r, ?_⟩
  rw [hr]
  rw [hau] at hb
  have hUU : (u : Q) * algebraMap B Q (↑U⁻¹ : B) = 1 := by
    rw [← map_natCast (algebraMap B Q), ← map_mul, ← hU, Units.mul_inv, map_one]
  simp only [map_mul, map_pow, map_natCast]
  push_cast at hb
  linear_combination ((p : Q) ^ m * algebraMap B Q (↑U⁻¹ : B) * algebraMap B Q r) * hb -
    (coeff α f * (p : Q) ^ (m + v) * algebraMap B Q r) * hUU

theorem cauchy (p : ℕ) [Fact p.Prime] (hunit : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B))
    (z : σ → B) (hz : ∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) (f : MvPowerSeries σ Q)
    (hf : DIn (⊤ : Ideal B) f) (m : ℕ) :
    ∃ M : ℕ, ∀ n n' : ℕ, M ≤ n → n ≤ n' → psum z f n' - psum z f n ∈ img B p m := by
  obtain ⟨M, hM⟩ := term_mem p hunit z hz f hf m
  refine ⟨M, fun n n' hn hnn' => ?_⟩
  rw [psum_eq, psum_eq, ← Finset.sum_sdiff (box_mono hnn'), add_sub_cancel_right]
  refine AddSubgroup.sum_mem _ fun α hα => ?_
  obtain ⟨i, hi⟩ := exists_lt_of_not_mem_box (Finset.mem_sdiff.1 hα).2
  exact hM α i (by omega)

end GlobalTheory.QLog.ValEx

namespace GlobalTheory.QLog

open ValEx in

theorem existsUnique_hasVal_of_dIn : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ]
    [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) →
    ∀ f : MvPowerSeries σ Q, DIn (⊤ : Ideal B) f → ∃! q : Q, HasVal p z f q := by
  intro p _ B O Q _ _ _ _ θ hF σ _ _ z hz f hf
  haveI := hF.complete
  have hI : ∀ (k : ℕ) (x : B), x ∈ ((Ideal.span {(p : B)}) ^ k • ⊤ : Submodule B B) ↔
      ∃ e, x = (p : B) ^ k * e := by
    intro k x
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨e, he⟩; exact ⟨e, by rw [← he, mul_comm]⟩
    · rintro ⟨e, he⟩; exact ⟨e, by rw [he, mul_comm]⟩
  choose M hM using cauchy p hF.unit_coprime z hz f hf
  set K : ℕ → ℕ := fun m => ∑ k ∈ Finset.range (m + 1), M k with hK
  have hMK : ∀ m, M m ≤ K m := fun m =>
    Finset.single_le_sum (fun k _ => Nat.zero_le (M k)) (Finset.mem_range.2 (Nat.lt_succ_self m))
  have hKmono : Monotone K := fun a b hab =>
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hab))
  have h0 : ∀ n, psum z f (K n) - psum z f (K 0) ∈ img B p 0 := fun n =>
    hM 0 (K 0) (K n) (hMK 0) (hKmono (Nat.zero_le n))
  choose b hb using h0
  have hcau : ∀ {k n : ℕ}, k ≤ n →
      b k ≡ b n [SMOD ((Ideal.span {(p : B)}) ^ k • ⊤ : Submodule B B)] := by
    intro k n hkn
    rw [SModEq.sub_mem, hI]
    obtain ⟨e, he⟩ := hM k (K k) (K n) (hMK k) (hKmono hkn)
    refine ⟨-e, hF.inj ?_⟩
    have hbk := hb k
    have hbn := hb n
    simp only [pow_zero, one_mul, map_sub, map_mul, map_neg, map_pow, map_natCast] at hbk hbn he ⊢
    linear_combination hbn - hbk - he
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' b hcau
  have huniq : ∀ q1 q2, HasVal p z f q1 → HasVal p z f q2 → q1 = q2 := by
    intro q1 q2 h1 h2
    have hd : ∀ m, ∃ e : B, q1 - q2 = algebraMap B Q ((p : B) ^ m * e) := by
      intro m
      obtain ⟨N1, hN1⟩ := h1 m
      obtain ⟨N2, hN2⟩ := h2 m
      obtain ⟨e1, he1⟩ := hN1 (max N1 N2) (le_max_left _ _)
      obtain ⟨e2, he2⟩ := hN2 (max N1 N2) (le_max_right _ _)
      exact ⟨e1 - e2, by rw [mul_sub, map_sub, ← he1, ← he2]; ring⟩
    obtain ⟨c, hc⟩ := hd 0
    have hc0 : c = 0 := by
      refine IsHausdorff.haus' (I := Ideal.span {(p : B)}) c fun n => ?_
      rw [SModEq.sub_mem, sub_zero, hI]
      obtain ⟨e, he⟩ := hd n
      exact ⟨e, hF.inj (by rw [← he, hc, pow_zero, one_mul])⟩
    rw [← sub_eq_zero, hc, hc0, mul_zero, map_zero]
  have hq : HasVal p z f (psum z f (K 0) + algebraMap B Q L) := fun m => ⟨K m, fun N' hN' => by
    obtain ⟨e1, he1⟩ := (hI m _).1 (SModEq.sub_mem.1 (hL m))
    obtain ⟨e2, he2⟩ := hM m (K m) N' (hMK m) hN'
    have hbm := hb m
    have he1' := congrArg (algebraMap B Q) he1
    refine ⟨-e1 - e2, ?_⟩
    change psum z f (K 0) + algebraMap B Q L - psum z f N' = _
    simp only [pow_zero, one_mul, map_sub, map_mul, map_neg, map_pow, map_natCast] at hbm he1' he2 ⊢
    linear_combination -hbm - he1' - he2⟩
  exact ⟨_, hq, fun q' hq' => huniq _ _ hq' hq⟩

end GlobalTheory.QLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueOfCompatible
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Limits

theorem smod_pow_iff {R : Type} [CommRing R] (a x y : R) (m : ℕ) :
    x ≡ y [SMOD (Ideal.span {a} ^ m • ⊤ : Submodule R R)] ↔ a ^ m ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem eval_eq_of_le {O σ : Type} [CommRing O] (A : ℕ → Type) [∀ n, CommRing (A n)]
    [∀ n, Algebra O (A n)] (r : ∀ n, A (n + 1) →ₐ[O] A n) (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n)
    (hr : ∀ n f, r n (E (n + 1) f) = E n f) {n k : ℕ} (hnk : n ≤ k) (x y : MvPowerSeries σ O)
    (h : E k x = E k y) : E n x = E n y := by
  induction k, hnk using Nat.le_induction with
  | base => exact h
  | succ k _ ih => exact ih (by rw [← hr k x, ← hr k y, h])

theorem exists_unique_of_compatible : ∀ (p : ℕ) (O σ : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] [Fintype σ] (A : ℕ → Type) [∀ n, CommRing (A n)] [∀ n, Algebra O (A n)] [∀ n, IsHausdorff (Ideal.span {(p : A n)}) (A n)] (r : ∀ n, A (n + 1) →ₐ[O] A n) (y : ∀ n, σ → A n) (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n), (∀ n, IsEval p (y n) (E n)) → (∀ n f, r n (E (n + 1) f) = E n f) → (∀ m N : ℕ, ∃ n, ∀ f, E n f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → (∀ f, (∀ n, E n f = 0) → f = 0) ∧ ((∀ n, Function.Surjective (E n)) → ∀ a : ∀ n, A n, (∀ n, r n (a (n + 1)) = a n) → ∃ f, ∀ n, E n f = a n) := by
  intro p O σ _ _ _ A _ _ _ r y E hev hr hker
  have hausO : IsHausdorff (Ideal.span {(p : O)}) O := inferInstance
  have precO : IsPrecomplete (Ideal.span {(p : O)}) O := inferInstance
  have hle : ∀ {n k : ℕ}, n ≤ k → ∀ x y, E k x = E k y → E n x = E n y :=
    fun hnk => eval_eq_of_le A r E hr hnk
  refine ⟨fun f hf => ?_, fun hsurj a ha => ?_⟩
  · ext α
    refine hausO.haus _ fun m => (smod_pow_iff _ _ _ _).2 ?_
    obtain ⟨n, hn⟩ := hker m (α.degree + 1)
    simpa using hn f (hf n) α (Nat.lt_succ_self _)
  · choose nk hnk using fun m => hker m m
    choose g hg using fun n => hsurj n (a n)
    set ν : ℕ → ℕ := fun m => m + ∑ j ∈ Finset.range (m + 1), nk j with hν
    have hνmono : Monotone ν := fun m m' hmm' => by
      simp only [hν]
      exact Nat.add_le_add hmm' (Finset.sum_le_sum_of_subset
        (Finset.range_mono (Nat.succ_le_succ hmm')))
    have hνk : ∀ m, nk m ≤ ν m := fun m => by
      simp only [hν]
      exact le_add_left (Finset.single_le_sum (f := nk) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 (Nat.lt_succ_self m)))
    have hνm : ∀ m, m ≤ ν m := fun m => by simp only [hν]; exact Nat.le_add_right _ _

    have hga : ∀ n k, n ≤ k → E n (g k) = a n := by
      intro n k hnk
      induction k, hnk using Nat.le_induction with
      | base => exact hg n
      | succ k hk ih =>
        rw [← ih]
        refine hle hk _ _ ?_
        rw [← hr k, hg (k + 1), ha k, hg k]

    have hKν : ∀ m k, ν m ≤ k → ∀ x, E k x = 0 → ∀ α : σ →₀ ℕ, α.degree < m →
        (p : O) ^ m ∣ coeff α x := by
      intro m k hk x hx α hα
      refine hnk m x ?_ α hα
      have := hle ((hνk m).trans hk) x 0 (by rw [hx, map_zero])
      rwa [map_zero] at this
    set h : ℕ → MvPowerSeries σ O := fun m => g (ν m) with hh
    have hD : ∀ m m', m ≤ m' → ∀ α : σ →₀ ℕ, α.degree < m →
        (p : O) ^ m ∣ coeff α (h m') - coeff α (h m) := by
      intro m m' hmm' α hα
      rw [← map_sub]
      refine hKν m (ν m) le_rfl _ ?_ α hα
      rw [map_sub, hh, hga _ _ (hνmono hmm'), hga _ _ le_rfl, sub_self]
    have hL : ∀ α : σ →₀ ℕ, ∃ L : O, ∀ j, (p : O) ^ j ∣ coeff α (h (j + (α.degree + 1))) - L := by
      intro α
      obtain ⟨L, hL⟩ := precO.prec (f := fun j => coeff α (h (j + (α.degree + 1)))) (by
        intro j j' hjj'
        rw [smod_pow_iff]
        have := hD (j + (α.degree + 1)) (j' + (α.degree + 1)) (by omega) α (by omega)
        rw [← neg_sub, dvd_neg]
        exact (pow_dvd_pow _ (by omega)).trans this)
      exact ⟨L, fun j => (smod_pow_iff _ _ _ _).1 (hL j)⟩
    choose L hLs using hL
    let f : MvPowerSeries σ O := fun α => L α
    have hf : ∀ m M (α : σ →₀ ℕ), m ≤ M → α.degree < M →
        (p : O) ^ m ∣ coeff α f - coeff α (h M) := by
      intro m M α hmM hα
      have h1 := hLs α M
      have h2 := hD M (M + (α.degree + 1)) (by omega) α hα
      have : coeff α f - coeff α (h M) =
          (coeff α (h (M + (α.degree + 1))) - coeff α (h M)) -
            (coeff α (h (M + (α.degree + 1))) - L α) := by
        show L α - _ = _; ring
      rw [this]
      exact (pow_dvd_pow _ hmM).trans (dvd_sub h2 h1)
    refine ⟨f, fun n => ?_⟩
    rw [← sub_eq_zero]
    refine IsHausdorff.haus (I := Ideal.span {(p : A n)}) inferInstance _ fun m => ?_
    rw [smod_pow_iff, sub_zero]
    obtain ⟨N₀, hN₀⟩ := (hev n).2 m
    set M := max (max m N₀) n with hM
    have hEM : E n (h M) = a n := hga _ _ ((le_max_right _ _).trans (hνm M))
    have hdiv : ∀ α : σ →₀ ℕ, α.degree < N₀ → (p : O) ^ m ∣ coeff α (f - h M) := by
      intro α hα
      rw [map_sub]
      exact hf m M α (by omega) (by omega)
    let Q : MvPowerSeries σ O := fun α =>
      if hα : α.degree < N₀ then Classical.choose (hdiv α hα) else 0
    have hR : ∀ α : σ →₀ ℕ, α.degree < N₀ →
        coeff α (f - h M - (p : O) ^ m • Q) = 0 := by
      intro α hα
      rw [map_sub, coeff_smul]
      show coeff α (f - h M) - (p : O) ^ m * (if hα : α.degree < N₀ then _ else 0) = 0
      rw [dif_pos hα, ← Classical.choose_spec (hdiv α hα), sub_self]
    have hsplit : E n f - a n = (p : A n) ^ m * E n Q + E n (f - h M - (p : O) ^ m • Q) := by
      rw [map_sub, map_sub, map_smul, hEM, Algebra.smul_def, map_pow, map_natCast]
      ring
    rw [hsplit]
    exact dvd_add (dvd_mul_right _ _) (hN₀ _ hR)

end GlobalTheory.Limits
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterShintaniPsiLift
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem shLift_eq_of_exists {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ}
    (δ : GL (Fin n) F') (h : ∃ γ, IsNorm s δ γ) (f : GL (Fin n) F → ℂ) :
    shLift s f δ = f h.choose := by
  unfold shLift
  rw [dif_pos h]

theorem exists_virt_psi_lift : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ k n : ℕ, ∃ X ∈ Virt ℂ ℂ (GHat F F' n), (∀ g, X (inl g) = psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) n g) ∧ ∀ δ, X (inl δ * inr s) = shLift s (psiG (rootSum (pullθ ι θ) k) n) δ := by
  intro F F' _ _ _ _ s hp hs ι θ hθ k
  haveI : Finite F := Finite.of_injective (algebraMap F F') (algebraMap F F').injective
  haveI : FiniteDimensional F F' := Module.Finite.of_finite
  have hcard : Nat.card (F' ≃ₐ[F] F') = Module.finrank F F' := by
    exact IsGalois.card_aut_eq_finrank F F'
  have hgen : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s := by
    haveI : Fact (Module.finrank F F').Prime := ⟨hp⟩
    rw [zpowers_eq_top_of_prime_card hcard hs]; intro t; trivial
  have hlift1 : ∀ (m : ℕ) (δ : GL (Fin m) F'), shLift s (fun _ : GL (Fin m) F => (1 : ℂ)) δ = 1 := by
    intro m δ
    exact shLift_eq_of_exists s δ (GlobalTheory.T.every_element_is_norm F F' s hgen m δ) _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hZ : ∀ a : Fin n, ∃ Z ∈ Virt ℂ ℂ (GHat F F' n),
      (∀ δ, Z (inl δ) = hc a (n - a)
        (psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) a) (fun _ => 1) n δ) ∧
      ∀ δ, Z (inl δ * inr s) = hcTw (s : F' →+* F') a (n - a)
        (shLift s (psiG (rootSum (pullθ ι θ) k) a)) (fun _ => 1) n δ := by
    intro a
    obtain ⟨Xa, hXa, h1, h2⟩ := ih a a.2
    obtain ⟨Z, hZv, hZe⟩ := GlobalTheory.T.exists_virtualCharacter_twistedHarishChandraInductionGL F F' a (n - a) n (by omega) Xa hXa
    refine ⟨Z, hZv, fun δ => ?_, fun δ => ?_⟩
    · have e := hZe 1 δ
      simp only [map_one, mul_one] at e
      have e2 : (fun d => Xa (inl d)) = psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) a :=
        funext h1
      rw [e2] at e
      exact e
    · rw [hZe s δ]
      have e2 : (fun d => Xa (inl d * inr s)) = shLift s (psiG (rootSum (pullθ ι θ) k) a) := funext h2
      rw [e2]
  choose Z hZv hZ1 hZ2 using hZ
  obtain ⟨A, hA, hA1, hA2⟩ := GlobalTheory.T.exists_tensorInduction_virtualCharacter_prime (GL (Fin n) F') (F' ≃ₐ[F] F') (galAct F F' n) s
    (by rw [hcard]; exact hp) hs (fun x => rootSum θ k (Matrix.charpoly (x : Matrix (Fin n) (Fin n) F')))
    (GlobalTheory.T.rootPowerSum_charpoly_mem_virtualCharacters_GL F' θ hθ n k)
  refine ⟨A - ∑ a : Fin n, Z a, sub_mem hA (sum_mem fun a _ => hZv a), fun g => ?_, fun δ => ?_⟩
  · simp only [Pi.sub_apply, Finset.sum_apply, hA1, hZ1]
    rw [GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F' _ n g]
    rw [Fin.sum_univ_eq_sum_range (fun a => hc a (n - a)
        (psiG (fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F'))) a) (fun _ => 1) n g) n]
    congr 1
    unfold chG
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [galAct_apply, ← Matrix.charpoly_map]
    congr 2
  · simp only [Pi.sub_apply, Finset.sum_apply, hA2, hZ2]
    have hex := GlobalTheory.T.every_element_is_norm F F' s hgen n δ
    rw [shLift_eq_of_exists s δ hex, GlobalTheory.T.primitiveFunctionCharpolyGL_harishChandra_recursion F _ n, ← shLift_eq_of_exists s δ hex (chG _ n),
      GlobalTheory.T.shintaniLift_charpoly_rootPowerSum_eq_norm F F' s hgen ι θ k n δ]
    rw [Fin.sum_univ_eq_sum_range (fun a => hcTw (s : F' →+* F') a (n - a)
        (shLift s (psiG (rootSum (pullθ ι θ) k) a)) (fun _ => 1) n δ) n]
    congr 1
    · unfold chG nrm
      rw [hcard]
    · refine Finset.sum_congr rfl fun a ha => ?_
      have han : n = a + (n - a) := by have := Finset.mem_range.1 ha; omega
      rw [← shLift_eq_of_exists s δ hex (hc a (n - a) (psiG (rootSum (pullθ ι θ) k) a) (fun _ => 1) n),
        GlobalTheory.T.shintaniLift_harishChandraInduction_eq_twisted F F' s hgen a (n - a) n han _ _
          ((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 a (fun _ => 1) (fun _ => 1)).2.2 _).1 (fun _ _ => rfl)]
      congr 1
      funext x
      exact (hlift1 _ x).symm

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroOnSubsetApplyCoe
section
namespace GlobalTheory.OTY.TwEst

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

def wt (A : WeightedAtlas n Y ι La) (E : La) (β : ι → Y → ℂ) (z : Y → V n) (y : Y) : ℝ :=
  -Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap (jdet A z) y)

def quot (A : WeightedAtlas n Y ι La) (h β : ι → Y → ℂ) (y : Y) : ℂ :=
  h (A.pick y) y / β (A.pick y) y

open scoped Classical in

def ext0 {Y : Type*} (U : Set Y) (f : U → ℂ) (y : Y) : ℂ :=
  if hy : y ∈ U then f ⟨y, hy⟩ else 0

theorem extendByZeroOnSubset_apply_coe {Y : Type*} (U : Set Y) (f : U → ℂ) (y : U) : ext0 U f y = f y := by
  simp [ext0, y.2]

end

end GlobalTheory.OTY.TwEst

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.nz_facts {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    (L Λ : La) (s : Fin n → ι → Y → ℂ) (τ : ι → Y → ℂ) (C : ℝ) (hC0 : 0 < C)
    (hsq : ∀ y, A.sqn L s y ≤ 1) (hC : ∀ y, A.nsq Λ τ y ≤ C * A.sqn L s y) (y : Y) (hy : y ∈ nz A τ) :
    y ∉ A.zeroSet s ∧ psi A L s y ≤ 0 ∧
      -psi A L s y ≤ (n : ℝ) * (-Real.log (A.nsq Λ τ y)) + (n : ℝ) * Real.log C := by
  have hτy : τ (A.pick y) y ≠ 0 := hy
  have hτ0 : 0 < A.nsq Λ τ y := by
    unfold WeightedAtlas.nsq
    exact mul_pos (pow_pos (norm_pos_iff.mpr hτy) 2) (Real.exp_pos _)
  have hs0 : 0 < A.sqn L s y := by
    by_contra hle
    push_neg at hle
    have := hC y
    nlinarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have hz' : ∀ k, s k (A.pick y) y = 0 := hz
    have : A.sqn L s y = 0 := by
      unfold WeightedAtlas.sqn WeightedAtlas.nsq
      simp [hz']
    linarith
  · unfold psi
    have := Real.log_nonpos hs0.le (hsq y)
    nlinarith
  · unfold psi
    have h1 : Real.log (A.nsq Λ τ y) ≤ Real.log C + Real.log (A.sqn L s y) := by
      rw [← Real.log_mul hC0.ne' hs0.ne']
      exact Real.log_le_log hτ0 (hC y)
    have := mul_le_mul_of_nonneg_left h1 hn
    nlinarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivGlobalOneFormEqSumWedgeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorDeriv_globalOneForm_eq_sum_wedge : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ w : Glob1 F, ∃ (n : ℕ) (u v : Fin n → Glob1 F), ClRel F w u v := by
  first | exact @GlobalTheory.AbCoh.dOne_glob_eq_wsum | exact GlobalTheory.AbCoh.dOne_glob_eq_wsum | (intros; apply GlobalTheory.AbCoh.dOne_glob_eq_wsum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorSquareEquivOfBaseChangeFieldStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorSquare_equiv_of_baseChange_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (M N M' N' : Type) [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] [AddCommGroup M'] [Module L M'] [AddCommGroup N'] [Module L N'] (c : M →ₗ[K] M →ₗ[K] N) (c' : M' →ₗ[L] M' →ₗ[L] N') (e₁ : L ⊗[K] M ≃ₗ[L] M') (e₂ : L ⊗[K] N ≃ₗ[L] N'), (∀ a b, e₂ (1 ⊗ₜ c a b) = c' (e₁ (1 ⊗ₜ a)) (e₁ (1 ⊗ₜ b))) → (∃ e : ⋀[L]^2 M' ≃ₗ[L] N', ∀ a b, e (exteriorPower.ιMulti L 2 ![a, b]) = c' a b) → ∃ e : ⋀[K]^2 M ≃ₗ[K] N, ∀ a b, e (exteriorPower.ιMulti K 2 ![a, b]) = c a b := by
  first | exact @GlobalTheory.AbCoh.exteriorSquare_equiv_of_baseChange | exact GlobalTheory.AbCoh.exteriorSquare_equiv_of_baseChange | (intros; apply GlobalTheory.AbCoh.exteriorSquare_equiv_of_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStableStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockHarmonics_graded_compactStable : ∀ (p q r s : ℕ) (S : Set (Pol p q r s)), (S = harm1 p q r s ∨ S = harm2 p q r s ∨ S = jointHarm p q r s) → (Submodule.span ℂ S : Set (Pol p q r s)) = S ∧ KStable (fockAct1 p q r s) (Submodule.span ℂ S) ∧ KStable (fockAct2 p q r s) (Submodule.span ℂ S) ∧ ∀ P ∈ S, ∀ d : ℕ, homogeneousComponent d P ∈ S := by
  first | exact @GlobalTheory.FockAlg.harm_graded_stable | exact GlobalTheory.FockAlg.harm_graded_stable | (intros; apply GlobalTheory.FockAlg.harm_graded_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoContinuationOfFunctionalEquationStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation : GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo := by
  first | exact @GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe | exact GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe | (intros; apply GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe <;> assumption)
end

