import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0221
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0118
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0133
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0070

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsRangeOfMonicRoot
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem qAll_isBoundedAtImInfty {p : ℂ → Prop} {N : ℕ} {f : ℍ → ℂ} (hN : 0 < N) (h : QAll p N f) :
    UpperHalfPlane.IsBoundedAtImInfty f := by
  obtain ⟨a, ha, -⟩ := h
  exact (GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty N f a hN ha).2

theorem isBoundedAtImInfty_of_monic_root {n : ℕ} {h : ℍ → ℂ} {s : Fin n → ℍ → ℂ}
    (hs : ∀ j, UpperHalfPlane.IsBoundedAtImInfty (s j))
    (hrel : ∀ τ, h τ ^ n + ∑ j, s j τ * h τ ^ (j : ℕ) = 0) : UpperHalfPlane.IsBoundedAtImInfty h := by
  have hb : ∀ τ, ‖h τ‖ ≤ 1 + ∑ j, ‖s j τ‖ := fun τ => GlobalTheory.T.norm_root_le_one_add_sum_norm_coeff n (fun j => s j τ) (h τ) (hrel τ)
  have hsum : (fun τ => 1 + ∑ j, ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := by
    refine Asymptotics.IsBigO.add (Asymptotics.isBigO_refl _ _) ?_
    convert Asymptotics.IsBigO.sum (A := fun j τ => ‖s j τ‖) (s := Finset.univ) (fun j _ => (hs j).norm_left) using 1
    ext τ; simp [Finset.sum_apply]
  refine Asymptotics.IsBigO.trans (Asymptotics.isBigO_of_le _ fun τ => ?_) hsum
  refine (hb τ).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (by positivity)]

end GlobalTheory.FN

namespace GlobalTheory.FN

theorem qAll_range_of_monic_root : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (N n : ℕ) (h : ℍ → ℂ) (s : Fin n → ℍ → ℂ), 0 < N → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → (∀ τ : ℍ, h ((N : ℝ) +ᵥ τ) = h τ) → (∀ j, QAll (· ∈ ε.range) N (s j)) → (∀ τ, h τ ^ n + ∑ j, s j τ * h τ ^ (j : ℕ) = 0) → QAll (· ∈ ε.range) N h := by
  intro Ω _ _ ε N n h s hN hh hper hs hrel
  obtain ⟨b, hb⟩ := GlobalTheory.T.hasQExpansion_of_periodic_bounded_holomorphic N h hN hh hper
    (isBoundedAtImInfty_of_monic_root (fun j => qAll_isBoundedAtImInfty hN (hs j)) hrel)
  choose a ha hain using hs
  let p : ℕ → ℍ → ℂ := fun i => if hi : i < n then s ⟨i, hi⟩ else fun _ => 1
  let c : ℕ → ℕ → ℂ := fun i => if hi : i < n then a ⟨i, hi⟩ else fun k => if k = 0 then 1 else 0
  have hp : ∀ i, HasQ N (p i) (c i) := by
    intro i
    by_cases hi : i < n
    · simpa [p, c, hi] using ha ⟨i, hi⟩
    · simpa [p, c, hi] using HasQ.const N 1
  have hrel' : ∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * h τ ^ i = 0 := by
    intro τ
    rw [Finset.sum_range_succ, Finset.sum_range, add_comm, ← hrel τ]
    simp [p]
  have hQ := GlobalTheory.T.polynomial_relation_passes_to_qExpansions N n h b p c hN hb hp hrel'
  set Q := ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (c i)) with hQdef
  have hcoeff : ∀ i, Q.coeff i = if i < n + 1 then PowerSeries.mk (c i) else 0 := by
    intro i
    rw [hQdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) i (fun j => PowerSeries.mk (c j))]
    simp
  have hcn : PowerSeries.mk (c n) = 1 := by
    ext k
    simp [c, PowerSeries.coeff_one]
  have hQ0 : Q ≠ 0 := by
    intro h0
    have := hcoeff n
    rw [h0, if_pos (Nat.lt_succ_self n), hcn] at this
    simp at this
  have hcr : ∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ ε.range := by
    intro i k
    rw [hcoeff i]
    split_ifs with hi
    · rw [PowerSeries.coeff_mk]
      by_cases hin : i < n
      · simpa [c, hin] using hain ⟨i, hin⟩ k
      · simp only [c, hin, dite_false]
        split_ifs
        · exact ⟨1, map_one ε⟩
        · exact ⟨0, map_zero ε⟩
    · simp only [map_zero]
      exact ⟨0, map_zero ε⟩
  have key := GlobalTheory.T.coeff_mem_range_of_isRoot_of_coeff_mem_range Ω ε (PowerSeries.mk b) Q hQ0 hcr hQ
  exact ⟨b, hb, fun k => by simpa using key k⟩

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffsMemFinitelyGenerated
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

def clearCoeff (n M w : ℕ) (c : Fin n → Polynomial ℂ) (i : ℕ) (τ : ℍ) : ℂ :=
  if h : i < n then
    DD τ ^ (w * (n - i)) * ∑ k ∈ Finset.range (M + 1), (c ⟨i, h⟩).coeff k * (E₄ τ ^ (3 * k) * DD τ ^ (M - k))
  else DD τ ^ M

theorem dd_pow_mul_eval_jT (p : Polynomial ℂ) (M : ℕ) (hp : p.natDegree ≤ M) (τ : ℍ) :
    DD τ ^ M * p.eval (jT τ) =
      ∑ k ∈ Finset.range (M + 1), p.coeff k * (E₄ τ ^ (3 * k) * DD τ ^ (M - k)) := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hD := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ
  have hsplit : DD τ ^ M = DD τ ^ (M - k) * DD τ ^ k := by rw [← pow_add, Nat.sub_add_cancel hk']
  rw [hsplit]
  simp only [ReciprocityTheory.ChartRestriction.L1.jT, ReciprocityTheory.ChartRestriction.L1.AA]
  rw [div_pow, pow_mul]
  field_simp

theorem sum_clearCoeff_eq_zero (n M w : ℕ) (c : Fin n → Polynomial ℂ) (hM : ∀ i, (c i).natDegree ≤ M)
    (f : ℍ → ℂ) (h : ∀ τ, f τ ^ n + ∑ i, (c i).eval (jT τ) * f τ ^ (i : ℕ) = 0) (τ : ℍ) :
    ∑ i ∈ Finset.range (n + 1), clearCoeff n M w c i τ * (DD τ ^ w * f τ) ^ i = 0 := by
  have key : ∑ i ∈ Finset.range (n + 1), clearCoeff n M w c i τ * (DD τ ^ w * f τ) ^ i =
      DD τ ^ (w * n + M) * (f τ ^ n + ∑ i, (c i).eval (jT τ) * f τ ^ (i : ℕ)) := by
    rw [Finset.sum_range_succ, Finset.sum_range (fun i => clearCoeff n M w c i τ * (DD τ ^ w * f τ) ^ i),
      mul_add, Finset.mul_sum, add_comm]
    congr 1
    · simp only [clearCoeff, lt_irrefl, dite_false]
      rw [mul_pow, ← pow_mul, pow_add]
      ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [clearCoeff, Fin.is_lt, dite_true, Fin.eta]
      rw [← dd_pow_mul_eval_jT _ M (hM i), mul_pow, ← pow_mul]
      have e : w * (n - i) + M + w * i = w * n + M := by
        rw [add_right_comm, ← mul_add, Nat.sub_add_cancel i.isLt.le]
      rw [← e, pow_add, pow_add]
      ring
  rw [key, h τ, mul_zero]

theorem qall_clearCoeff (R : Subring ℂ) (N : ℕ) (hN : 0 < N) (n M w : ℕ) (c : Fin n → Polynomial ℂ)
    (hc : ∀ (i : Fin n) (k : ℕ), k ≤ M → (c i).coeff k ∈ R) (i : ℕ) :
    QAll (· ∈ R) N (clearCoeff n M w c i) := by
  obtain ⟨hcst, -, -, hmul, hpow, hsum⟩ := GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed R N hN
  have hDD : QAll (· ∈ R) N DD := ((GlobalTheory.T.eisenstein_delta_qExpansion_integrality N hN DD (Or.inr (Or.inr rfl))).2.1) R
  have hE : QAll (· ∈ R) N ⇑E₄ := ((GlobalTheory.T.eisenstein_delta_qExpansion_integrality N hN ⇑E₄ (Or.inl rfl)).2.1) R
  by_cases h : i < n
  · have hf : clearCoeff n M w c i = fun τ => DD τ ^ (w * (n - i)) *
        ∑ k ∈ Finset.range (M + 1), (c ⟨i, h⟩).coeff k * (E₄ τ ^ (3 * k) * DD τ ^ (M - k)) := by
      funext τ; simp [clearCoeff, h]
    rw [hf]
    refine hmul _ _ (hpow _ _ hDD) ?_
    refine (hsum ℕ (Finset.range (M + 1)) _ fun k hk => ?_).1
    exact hmul _ _ (hcst _ (hc _ k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))))
      (hmul _ _ (hpow _ _ hE) (hpow _ _ hDD))
  · have hf : clearCoeff n M w c i = fun τ => DD τ ^ M := by funext τ; simp [clearCoeff, h]
    rw [hf]
    exact hpow _ _ hDD

theorem powerSeries_map_mk {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (g : ℕ → Ω) :
    PowerSeries.map ε (PowerSeries.mk g) = PowerSeries.mk fun k => ε (g k) := by
  ext k; simp [PowerSeries.coeff_map]

theorem qcoeff_finitelyGenerated : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (N w : ℕ) (f : ℍ → ℂ) (a : ℕ → Ω),
    0 < N → Lv ε.range N w f → HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (a n)) →
      ∃ S : Finset Ω, ∀ k, a k ∈ Subring.closure (S : Set Ω) := by
  intro Ω _ ε N w f a hN hLv hF
  classical
  haveI : CharZero Ω := ε.charZero
  obtain ⟨n, c, hc, hrel⟩ := GlobalTheory.T.integral_over_jInvariant_of_hasSomeLevelOver ε.range f ⟨N, w, hN, hLv⟩
  set M := ∑ i, (c i).natDegree with hMdef
  have hM : ∀ i, (c i).natDegree ≤ M := fun i =>
    Finset.single_le_sum (f := fun i => (c i).natDegree) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hpre : ∀ (i : Fin n) (k : ℕ), ∃ x : Ω, ε x = (c i).coeff k := fun i k => RingHom.mem_range.1 (hc i k)
  choose e he using hpre
  set S₀ : Finset Ω := Finset.univ.image (fun p : Fin n × Fin (M + 1) => e p.1 p.2) with hS₀
  set A : Subring Ω := Subring.closure (S₀ : Set Ω) with hA
  set R : Subring ℂ := A.map ε with hR
  have hcR : ∀ (i : Fin n) (k : ℕ), k ≤ M → (c i).coeff k ∈ R := fun i k hk =>
    Subring.mem_map.2 ⟨e i k, Subring.subset_closure (Finset.mem_coe.2 (Finset.mem_image.2
      ⟨(i, ⟨k, Nat.lt_succ_of_le hk⟩), Finset.mem_univ _, rfl⟩)), he i k⟩
  have hP : ∀ i, QAll (· ∈ R) N (clearCoeff n M w c i) := qall_clearCoeff R N hN n M w c hcR
  choose c' hc'Q hc'R using hP
  have hser := GlobalTheory.T.polynomial_relation_passes_to_qExpansions N n (fun τ => DD τ ^ w * f τ) (fun k => ε (a k)) (clearCoeff n M w c) c' hN hF hc'Q
    (sum_clearCoeff_eq_zero n M w c hM f hrel)
  have hpre2 : ∀ i k, ∃ x ∈ A, ε x = c' i k := fun i k => Subring.mem_map.1 (hc'R i k)
  choose d hdA hd using hpre2
  set Q : Polynomial (PowerSeries Ω) :=
    ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (d i)) with hQdef
  have hmap : PowerSeries.map ε (Q.eval (PowerSeries.mk a)) =
      (∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (c' i))).eval
        (PowerSeries.mk fun k => ε (a k)) := by
    simp only [hQdef, Polynomial.eval_finset_sum, Polynomial.eval_monomial, map_sum, map_mul, map_pow,
      powerSeries_map_mk, hd]
  rw [hser] at hmap
  have hQ : Q.eval (PowerSeries.mk a) = 0 := by
    ext k
    have := congrArg (PowerSeries.coeff k) hmap
    simpa [PowerSeries.coeff_map] using this
  have hcoef : ∀ i, Q.coeff i = if i ∈ Finset.range (n + 1) then PowerSeries.mk (d i) else 0 := fun i => by
    simp only [hQdef, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
    exact Finset.sum_ite_eq' _ _ _
  have hQne : Q ≠ 0 := by
    intro h0
    have hn := hcoef n
    rw [h0, Polynomial.coeff_zero, if_pos (Finset.self_mem_range_succ n)] at hn
    have hc0 : c' n = 0 := funext fun k => by
      have h1 := congrArg (PowerSeries.coeff k) hn
      rw [PowerSeries.coeff_mk, map_zero] at h1
      rw [← hd n k, ← h1, map_zero]; rfl
    have hq := hc'Q n
    have hPn : clearCoeff n M w c n = fun τ => DD τ ^ M := by funext τ; simp [clearCoeff]
    rw [hPn, hc0] at hq
    have hz : HasQ N (fun _ : ℍ => (0 : ℂ)) (0 : ℕ → ℂ) := fun τ => by simpa using hasSum_zero
    have := (GlobalTheory.T.hasQExpansionOfLevel_coeff_and_function_unique).2 N _ _ 0 hq hz
    exact pow_ne_zero M (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero UpperHalfPlane.I) (congrFun this UpperHalfPlane.I)
  have hcA : ∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ A := fun i k => by
    rw [hcoef i]
    split_ifs
    · rw [PowerSeries.coeff_mk]; exact hdA i k
    · simp
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.eisenstein_algebraic_powerSeries_coeff_closure Ω A (PowerSeries.mk a) Q hQne hcA hQ
  refine ⟨S₀ ∪ S₁, fun k => ?_⟩
  have hk := hS₁ k
  rw [PowerSeries.coeff_mk] at hk
  refine (Subring.closure_le.2 ?_) hk
  rintro x (hx | hx)
  · exact Subring.closure_mono (by simp [Finset.coe_union]) hx
  · exact Subring.subset_closure (by simp [hx])

end GlobalTheory.FN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassDivisorBound
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem mass_true_le_one (g : ℕ) [Fact g.Prime] (N : ℕ) : (mass g N fun _ => True) ≤ 1 := by
  refine (GlobalTheory.T.mass_degType_le_card_cycleType_div g N (fun _ => True)).trans (le_of_eq ?_)
  rw [Finset.filter_true, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hN : (N.factorial : ℝ) ≠ 0 := by positivity
  exact div_self hN

theorem mass_dvd_le (g : ℕ) [Fact g.Prime] (N a : ℕ) (h : (ZMod g)[X]) (hh : h ∈ sqSet g a) :
    (mass g N fun f => h ∣ f) ≤ ((torusCard g h : ℝ))⁻¹ * mass g (N - a) fun _ => True := by
  obtain ⟨hmon, hdeg, -, -⟩ := mem_sqSet.1 hh
  have hh0 : h ≠ 0 := hmon.ne_zero
  unfold mass
  set S := (sqSet g N).filter fun f => h ∣ f with hS
  have hfac : ∀ f ∈ S, h * (f /ₘ h) = f := by
    intro f hf
    have hd : h ∣ f := (Finset.mem_filter.1 hf).2
    have e := Polynomial.modByMonic_add_div f h
    rwa [(Polynomial.modByMonic_eq_zero_iff_dvd hmon).2 hd, zero_add] at e
  have hmem : ∀ f ∈ S, f /ₘ h ∈ sqSet g (N - a) := by
    intro f hf
    obtain ⟨fmon, fdeg, fsq, fc0⟩ := mem_sqSet.1 (Finset.mem_filter.1 hf).1
    have e := hfac f hf
    have umon : (f /ₘ h).Monic := hmon.of_mul_monic_left (by rw [e]; exact fmon)
    refine mem_sqSet.2 ⟨umon, ?_, ?_, ?_⟩
    · have hd := hmon.natDegree_mul umon
      rw [e, fdeg, hdeg] at hd
      omega
    · exact Squarefree.of_mul_right (by rw [e]; exact fsq)
    · intro hz
      apply fc0
      rw [← e, Polynomial.mul_coeff_zero, hz, mul_zero]
  have hinj : Set.InjOn (fun f => f /ₘ h) (S : Set (ZMod g)[X]) := by
    intro f hf f' hf' hq
    rw [← hfac f hf, ← hfac f' hf']
    exact congrArg (h * ·) hq
  have hterm : ∀ f ∈ S, ((torusCard g f : ℝ))⁻¹ =
      ((torusCard g h : ℝ))⁻¹ * ((torusCard g (f /ₘ h) : ℝ))⁻¹ := by
    intro f hf
    have e := hfac f hf
    have hu0 : f /ₘ h ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at e
      exact (mem_sqSet.1 (Finset.mem_filter.1 hf).1).1.ne_zero e.symm
    conv_lhs => rw [← e]
    rw [torusCard_mul hh0 hu0, Nat.cast_mul, mul_inv]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
  rw [← Finset.sum_image (f := fun u => ((torusCard g u : ℝ))⁻¹) hinj, Finset.filter_true]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => inv_nonneg.2 (Nat.cast_nonneg _))
  intro u hu
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hu
  exact hmem f hf

theorem divisor_bound : ∀ (g : ℕ) [Fact g.Prime], (∀ N : ℕ, (mass g N fun _ => True) ≤ 1) ∧
    ∀ (N a : ℕ), ∀ h ∈ sqSet g a, (mass g N fun f => h ∣ f) ≤ ((torusCard g h : ℝ))⁻¹ := by
  intro g _
  refine ⟨mass_true_le_one g, fun N a h hh => ?_⟩
  refine (mass_dvd_le g N a h hh).trans ?_
  exact mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg _)) (mass_true_le_one g _)

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassHasDivisorOfDegreeLe
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

open Polynomial Classical in
private lemma exists_le_degType_sum_eq_of_hasDiv {g : ℕ} [Fact g.Prime] {N a : ℕ}
    {f : (ZMod g)[X]} (hf : f ∈ _root_.GlobalTheory.BadShare.sqSet g N) (hd : _root_.GlobalTheory.BadShare.HasDiv g a f) :
    ∃ ν ≤ _root_.GlobalTheory.BadShare.degType g f, ν.sum = a := by
  unfold _root_.GlobalTheory.BadShare.HasDiv at hd
  obtain ⟨h, hdvd, hdeg⟩ := hd
  obtain ⟨hmon, -, hsq, hc0⟩ := (_root_.GlobalTheory.BadShare.mem_sqSet).mp hf
  have hf0 : f ≠ 0 := hmon.ne_zero
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hf0 (zero_dvd_iff.mp hdvd)
  have hlc : h.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hh0
  obtain ⟨u, hu⟩ : ∃ u : (ZMod g)[X], u = h * C h.leadingCoeff⁻¹ := ⟨_, rfl⟩
  have hudvd : u ∣ f := by
    refine dvd_trans ⟨C h.leadingCoeff, ?_⟩ hdvd
    rw [hu, mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, mul_one]
  have humon : u.Monic := hu ▸ monic_mul_leadingCoeff_inv hh0
  have hudeg : u.natDegree = a := by rw [hu, natDegree_mul_C (inv_ne_zero hlc), hdeg]
  have husq : Squarefree u := hsq.squarefree_of_dvd hudvd
  have huc0 : u.coeff 0 ≠ 0 := by
    intro h0
    apply hc0
    obtain ⟨k, hk⟩ := hudvd
    rw [hk, mul_coeff_zero, h0, zero_mul]
  have hmem : u ∈ _root_.GlobalTheory.BadShare.sqSet g a :=
    (_root_.GlobalTheory.BadShare.mem_sqSet).mpr ⟨humon, hudeg, husq, huc0⟩
  obtain ⟨k, hk⟩ := hudvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    exact hf0 hk
  refine ⟨_root_.GlobalTheory.BadShare.degType g u, ?_,
    ((_root_.GlobalTheory.BadShare.torusCard_bounds_mul g).1 a u hmem).2.2.1⟩
  rw [hk, ((_root_.GlobalTheory.BadShare.torusCard_bounds_mul g).2.1 u k humon.ne_zero hk0).1]
  exact Multiset.le_add_right _ _

open Polynomial Classical in
private lemma exists_subset_map_eq_of_le_map {β γ : Type} (f : β → γ) (s : Finset β) :
    ∀ ν : Multiset γ, ν ≤ s.val.map f → ∃ t ⊆ s, t.val.map f = ν := by
  induction s using Finset.cons_induction with
  | empty =>
    intro ν h
    rw [Finset.empty_val, Multiset.map_zero, Multiset.le_zero] at h
    exact ⟨∅, Finset.empty_subset _, by rw [h]; rfl⟩
  | cons a s ha ih =>
    intro ν h
    rw [Finset.cons_val, Multiset.map_cons] at h
    by_cases hm : f a ∈ ν
    · obtain ⟨t, ht, htν⟩ := ih (ν.erase (f a))
        (by rw [← Multiset.cons_le_cons_iff (f a), Multiset.cons_erase hm]; exact h)
      refine ⟨Finset.cons a t (fun hat => ha (ht hat)), fun x hx => ?_, ?_⟩
      · rw [Finset.mem_cons] at hx ⊢
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (ht hx)
      · rw [Finset.cons_val, Multiset.map_cons, htν, Multiset.cons_erase hm]
    · obtain ⟨t, ht, htν⟩ := ih ν ((Multiset.le_cons_of_notMem hm).mp h)
      exact ⟨t, fun x hx => Finset.mem_cons.mpr (Or.inr (ht hx)), htν⟩

open Polynomial Classical in
private lemma exists_invariant_finset_card_of_le_cycleType {n : ℕ} (σ : Equiv.Perm (Fin n)) (ν : Multiset ℕ)
    (hν : ν ≤ σ.partition.parts) : ∃ S : Finset (Fin n), S.card = ν.sum ∧ S.map σ.toEmbedding = S := by
  rw [Equiv.Perm.parts_partition] at hν
  have h1 : ν.filter (2 ≤ ·) ≤ σ.cycleType := by
    refine (Multiset.filter_le_filter _ hν).trans (le_of_eq ?_)
    rw [Multiset.filter_add, Multiset.filter_eq_self.mpr (fun x hx => Equiv.Perm.two_le_of_mem_cycleType hx),
      Multiset.filter_eq_nil.mpr (fun x hx => by rw [Multiset.eq_of_mem_replicate hx]; norm_num), add_zero]
  have h2 : ν.filter (fun x => ¬ 2 ≤ x) ≤ Multiset.replicate (Fintype.card (Fin n) - σ.support.card) 1 := by
    refine (Multiset.filter_le_filter _ hν).trans (le_of_eq ?_)
    rw [Multiset.filter_add, Multiset.filter_eq_nil.mpr (fun x hx => not_not.mpr (Equiv.Perm.two_le_of_mem_cycleType hx)),
      Multiset.filter_eq_self.mpr (fun x hx => by rw [Multiset.eq_of_mem_replicate hx]; norm_num), zero_add]
  have hν2 : ν.filter (fun x => ¬ 2 ≤ x) = Multiset.replicate (Multiset.card (ν.filter (fun x => ¬ 2 ≤ x))) 1 :=
    Multiset.eq_replicate_of_mem fun b hb => Multiset.eq_of_mem_replicate (Multiset.mem_of_le h2 hb)
  have hk := Multiset.card_le_card h2
  rw [Multiset.card_replicate] at hk
  rw [Equiv.Perm.cycleType_def] at h1
  obtain ⟨C, hC, hCν⟩ := exists_subset_map_eq_of_le_map _ _ _ h1
  have hcompl : (σ.support)ᶜ.card = Fintype.card (Fin n) - σ.support.card := Finset.card_compl _
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq (hcompl ▸ hk)
  have hCσ : ∀ c ∈ C, ∀ x ∈ c.support, σ x = c x := fun c hc x hx =>
    ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp (hC hc)).2 x hx).symm
  have hS1 : ∀ x ∈ C.biUnion (fun c => c.support), σ x ∈ C.biUnion (fun c => c.support) ∧ σ x ≠ x := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hx
    rw [hCσ c hc x hxc]
    exact ⟨Finset.mem_biUnion.mpr ⟨c, hc, Equiv.Perm.apply_mem_support.mpr hxc⟩, Equiv.Perm.mem_support.mp hxc⟩
  have hT' : ∀ x ∈ T, σ x = x := fun x hx => Equiv.Perm.notMem_support.mp (Finset.mem_compl.mp (hT hx))
  have hdisj : Disjoint (C.biUnion (fun c => c.support)) T := by
    rw [Finset.disjoint_left]
    intro x hx hxT
    exact (hS1 x hx).2 (hT' x hxT)
  have hcard1 : (C.biUnion (fun c => c.support)).card = (ν.filter (2 ≤ ·)).sum := by
    rw [Finset.card_biUnion, ← hCν, Finset.sum_eq_multiset_sum]
    · rfl
    · intro c hc e he hce
      exact (Equiv.Perm.cycleFactorsFinset_pairwise_disjoint σ (hC hc) (hC he) hce).disjoint_support
  refine ⟨C.biUnion (fun c => c.support) ∪ T, ?_, ?_⟩
  · have hs2 : (ν.filter (fun x => ¬ 2 ≤ x)).sum = Multiset.card (ν.filter (fun x => ¬ 2 ≤ x)) := by
      conv_lhs => rw [hν2]
      rw [Multiset.sum_replicate, smul_eq_mul, mul_one]
    rw [Finset.card_union_of_disjoint hdisj, hcard1, hTc, ← hs2, ← Multiset.sum_add, Multiset.filter_add_not]
  · refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) (by rw [Finset.card_map])
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ (hS1 x hx).1
    · simp only [Equiv.toEmbedding_apply]
      rw [hT' x hx]
      exact Finset.mem_union_right _ hx

open Polynomial Classical in

theorem _root_.GlobalTheory.BadShare.mass_hasDiv_le : ∀ (g : ℕ) [Fact g.Prime], ∀ N a : ℕ, 0 < a → a < N →
    _root_.GlobalTheory.BadShare.mass g N (_root_.GlobalTheory.BadShare.HasDiv g a) ≤ 7 / 8 := by
  intro g _ N a ha haN
  have hmono := (_root_.GlobalTheory.BadShare.mass_union_bounds g N).1
  refine (hmono _ (fun f => (fun μ : Multiset ℕ => ∃ ν ≤ μ, ν.sum = a) (_root_.GlobalTheory.BadShare.degType g f))
    (fun f hf hd => exists_le_degType_sum_eq_of_hasDiv hf hd)).trans ?_
  refine (_root_.GlobalTheory.BadShare.mass_degType_le_cycleType g N (fun μ => ∃ ν ≤ μ, ν.sum = a)).trans ?_
  have h := _root_.GlobalTheory.StableSubset.card_exists_stable_subset_le N a ha haN
  have hc := Finset.card_le_card (s := Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∃ ν ≤ σ.partition.parts, ν.sum = a)
    (t := Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∃ A : Finset (Fin N), A.card = a ∧ A.map σ.toEmbedding = A)
    (fun σ hσ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      obtain ⟨ν, hν, rfl⟩ := hσ
      exact exists_invariant_finset_card_of_le_cycleType σ ν hν)
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  rw [div_le_iff₀ hf]
  have h' := (Nat.cast_le (α := ℝ)).mpr h
  have hc' := (Nat.cast_le (α := ℝ)).mpr hc
  push_cast at h' hc'
  linarith

end GlobalTheory.BadShare
end

