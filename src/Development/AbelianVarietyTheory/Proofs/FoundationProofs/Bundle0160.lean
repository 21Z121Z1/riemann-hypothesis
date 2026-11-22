import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0144
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenLangRatFunc
section
open GlobalTheory.NeedB Polynomial

noncomputable section

namespace GlobalTheory
namespace TsenLang

variable {k : Type} [Field k]

def genSub (n s : ℕ) (j : Fin n) : (MvPolynomial (Fin n × Fin (s + 1)) k)[X] :=
  ∑ t : Fin (s + 1), Polynomial.monomial (t : ℕ) (MvPolynomial.X (j, t))

def genEval (n s : ℕ) (g : MvPolynomial (Fin n) k[X]) : (MvPolynomial (Fin n × Fin (s + 1)) k)[X] :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom MvPolynomial.C) (genSub n s) g

theorem map_genEval (n s : ℕ) (φ : MvPolynomial (Fin n × Fin (s + 1)) k →+* k)
    (hφ : ∀ a, φ (MvPolynomial.C a) = a) (g : MvPolynomial (Fin n) k[X]) :
    (genEval n s g).map φ = MvPolynomial.eval (fun j => (genSub n s j).map φ) g := by
  unfold genEval
  rw [← Polynomial.coe_mapRingHom, MvPolynomial.hom_eval₂, Polynomial.mapRingHom_comp]
  have h : φ.comp (MvPolynomial.C : k →+* MvPolynomial (Fin n × Fin (s + 1)) k) = RingHom.id k :=
    RingHom.ext hφ
  rw [h, Polynomial.mapRingHom_id]
  rfl

theorem natDegree_genSub_le (n s : ℕ) (j : Fin n) : (genSub (k := k) n s j).natDegree ≤ s := by
  unfold genSub
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro t _
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp t.2)

theorem natDegree_genEval_le (n s d m : ℕ) (g : MvPolynomial (Fin n) k[X])
    (hg : ∀ μ, g.coeff μ ≠ 0 → μ.degree = d ∧ (g.coeff μ).natDegree ≤ m) :
    (genEval n s g).natDegree ≤ d * s + m := by
  unfold genEval
  rw [MvPolynomial.eval₂_eq']
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro μ hμ
  obtain ⟨h1, h2⟩ := hg μ (MvPolynomial.mem_support_iff.mp hμ)
  refine (Polynomial.natDegree_mul_le).trans ?_
  have hA : (Polynomial.mapRingHom (MvPolynomial.C : k →+* MvPolynomial (Fin n × Fin (s + 1)) k)
      (g.coeff μ)).natDegree ≤ m := (Polynomial.natDegree_map_le).trans h2
  have hB : (∏ j, genSub (k := k) n s j ^ μ j).natDegree ≤ d * s := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc ∑ j, (genSub (k := k) n s j ^ μ j).natDegree ≤ ∑ j, μ j * s :=
          Finset.sum_le_sum fun j _ =>
            (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left _ (natDegree_genSub_le n s j))
      _ = (∑ j, μ j) * s := by rw [Finset.sum_mul]
      _ = d * s := by rw [← h1, Finsupp.degree_eq_sum]
  omega

theorem genSub_map_constantCoeff (n s : ℕ) (j : Fin n) :
    (genSub (k := k) n s j).map MvPolynomial.constantCoeff = 0 := by
  simp [genSub, Polynomial.map_sum]

theorem coeff_genSub_map_eval (n s : ℕ) (c : Fin n × Fin (s + 1) → k) (j : Fin n) (t : Fin (s + 1)) :
    ((genSub (k := k) n s j).map (MvPolynomial.eval c)).coeff t = c (j, t) := by
  simp [genSub, Polynomial.map_sum, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Fin.val_inj]

theorem constantCoeff_coeff_genEval (n s d : ℕ) (hd : 0 < d) (g : MvPolynomial (Fin n) k[X])
    (hg : ∀ μ, g.coeff μ ≠ 0 → μ.degree = d) (e : ℕ) :
    MvPolynomial.constantCoeff ((genEval n s g).coeff e) = 0 := by
  have h := map_genEval (k := k) n s MvPolynomial.constantCoeff (fun a => by simp) g
  have h2 : (fun j => (genSub (k := k) n s j).map MvPolynomial.constantCoeff) = 0 := by
    funext j; exact genSub_map_constantCoeff n s j
  rw [h2, MvPolynomial.eval_zero] at h
  have h3 : MvPolynomial.constantCoeff g = 0 := by
    by_contra hne
    have := hg 0 (by rwa [← MvPolynomial.constantCoeff_eq])
    simp at this; omega
  rw [h3] at h
  have := congrArg (fun p => Polynomial.coeff p e) h
  simpa [Polynomial.coeff_map] using this

theorem exists_ne_zero_polynomial_common_zero [IsAlgClosed k] (n r d m : ℕ)
    (g : Fin r → MvPolynomial (Fin n) k[X])
    (hg : ∀ i μ, (g i).coeff μ ≠ 0 → μ.degree = d ∧ ((g i).coeff μ).natDegree ≤ m)
    (hd : 0 < d) (hn : r * d < n) :
    ∃ x : Fin n → k[X], x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (g i) = 0 := by
  classical
  set s := r * (m + 1) with hs
  set E := d * s + m + 1 with hE
  let F : Fin r × Fin E → MvPolynomial (Fin n × Fin (s + 1)) k :=
    fun p => (genEval n s (g p.1)).coeff p.2
  let e1 : Fin (r * E) ≃ Fin r × Fin E := finProdFinEquiv.symm
  let e2 : Fin (n * (s + 1)) ≃ Fin n × Fin (s + 1) := finProdFinEquiv.symm
  let F' : Fin (r * E) → MvPolynomial (Fin (n * (s + 1))) k :=
    fun q => MvPolynomial.rename e2.symm (F (e1 q))
  have hF' : ∀ q, MvPolynomial.constantCoeff (F' q) = 0 := by
    intro q
    simp only [F', MvPolynomial.constantCoeff_rename, F]
    exact constantCoeff_coeff_genEval n s d hd _ (fun μ h => (hg _ μ h).1) _
  have hlt : r * E < n * (s + 1) := by
    have h1 : r * d + 1 ≤ n := hn
    have h2 : (r * d + 1) * (s + 1) ≤ n * (s + 1) := Nat.mul_le_mul_right _ h1
    have h3 : r * E < (r * d + 1) * (s + 1) := by
      rw [hE, hs]; ring_nf; nlinarith
    omega
  obtain ⟨c, hc0, hc⟩ := exists_ne_zero_common_zero_of_constantCoeff_eq_zero k _ _ F' hF' hlt
  set c' : Fin n × Fin (s + 1) → k := c ∘ e2.symm with hc'
  refine ⟨fun j => (genSub n s j).map (MvPolynomial.eval c'), ?_, ?_⟩
  · intro h0
    obtain ⟨q, hq⟩ : ∃ q, c q ≠ 0 := by
      by_contra hh; push_neg at hh; exact hc0 (funext hh)
    have := congrArg (fun x : Fin n → k[X] => (x (e2 q).1).coeff (e2 q).2) h0
    simp only [coeff_genSub_map_eval, Pi.zero_apply, Polynomial.coeff_zero] at this
    apply hq
    simpa [hc'] using this
  · intro i
    rw [← map_genEval n s (MvPolynomial.eval c') (fun a => by simp)]
    ext e
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    by_cases he : e < E
    · have := hc (e1.symm (i, ⟨e, he⟩))
      simpa [F', F, MvPolynomial.eval_rename, hc'] using this
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt, map_zero]
      have := natDegree_genEval_le n s d m (g i) (hg i)
      omega

end TsenLang

open TsenLang in

theorem tsenLang_ratFunc :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (n r d : ℕ) (f : Fin r → MvPolynomial (Fin n) (RatFunc k)),
      (∀ i, (f i).IsHomogeneous d) → 0 < d → r * d < n →
        ∃ x : Fin n → RatFunc k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  intro k _ _ n r d f hf hd hn
  classical
  let S : Finset (RatFunc k) := Finset.univ.biUnion fun i => (f i).support.image fun μ => (f i).coeff μ
  obtain ⟨⟨b, hb⟩, hbS⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors k[X]) S
  let numer : RatFunc k → k[X] := fun a =>
    if h : IsLocalization.IsInteger k[X] (b • a) then (RingHom.mem_rangeS.mp h).choose else 0
  have hnumer : ∀ a ∈ S, algebraMap k[X] (RatFunc k) (numer a) = b • a := by
    intro a ha
    have h := hbS a ha
    simp only [numer, dif_pos h]
    exact (RingHom.mem_rangeS.mp h).choose_spec
  let g : Fin r → MvPolynomial (Fin n) k[X] := fun i =>
    ∑ μ ∈ (f i).support, MvPolynomial.monomial μ (numer ((f i).coeff μ))
  have hgc : ∀ i μ, (g i).coeff μ = if μ ∈ (f i).support then numer ((f i).coeff μ) else 0 := by
    intro i μ
    simp only [g, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
  have hgmap : ∀ i, MvPolynomial.map (algebraMap k[X] (RatFunc k)) (g i) =
      MvPolynomial.C (algebraMap k[X] (RatFunc k) b) * f i := by
    intro i
    ext μ
    rw [MvPolynomial.coeff_map, hgc, MvPolynomial.coeff_C_mul]
    split_ifs with hμ
    · rw [hnumer _ (by simp only [S, Finset.mem_biUnion, Finset.mem_image]; exact ⟨i, Finset.mem_univ _, μ, hμ, rfl⟩),
        Algebra.smul_def]
    · rw [MvPolynomial.notMem_support_iff.mp hμ]; simp
  let m : ℕ := Finset.univ.sup fun i => (g i).support.sup fun μ => ((g i).coeff μ).natDegree
  have hg : ∀ i μ, (g i).coeff μ ≠ 0 → μ.degree = d ∧ ((g i).coeff μ).natDegree ≤ m := by
    intro i μ hμ
    refine ⟨?_, ?_⟩
    · have hmem : μ ∈ (f i).support := by
        by_contra h; rw [hgc, if_neg h] at hμ; exact hμ rfl
      have := hf i (MvPolynomial.mem_support_iff.mp hmem)
      rwa [Finsupp.degree_eq_weight_one]
    · exact le_trans (Finset.le_sup (f := fun μ => ((g i).coeff μ).natDegree)
          (MvPolynomial.mem_support_iff.mpr hμ))
        (Finset.le_sup (f := fun i => (g i).support.sup fun μ => ((g i).coeff μ).natDegree)
          (Finset.mem_univ i))
  obtain ⟨y, hy0, hy⟩ := exists_ne_zero_polynomial_common_zero n r d m g hg hd hn
  have hinj : Function.Injective (algebraMap k[X] (RatFunc k)) := IsFractionRing.injective k[X] (RatFunc k)
  have hb0 : algebraMap k[X] (RatFunc k) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  refine ⟨fun j => algebraMap k[X] (RatFunc k) (y j), ?_, ?_⟩
  · intro h
    apply hy0
    funext j
    have := congrFun h j
    exact hinj (by simpa using this)
  · intro i
    have h1 : algebraMap k[X] (RatFunc k) (MvPolynomial.eval y (g i)) =
        MvPolynomial.eval (fun j => algebraMap k[X] (RatFunc k) (y j))
          (MvPolynomial.map (algebraMap k[X] (RatFunc k)) (g i)) := by
      rw [MvPolynomial.eval_map]
      first
        | (simp only [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.hom_eval₂]; rfl)
        | exact MvPolynomial.eval₂_comp_left _ _ _ _
        | simp [MvPolynomial.eval₂_comp_left]
    rw [hy i, map_zero, hgmap, map_mul, MvPolynomial.eval_C] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hb0

example : ∀ (k : Type) [Field k] [IsAlgClosed k] (n r d : ℕ) (f : Fin r → MvPolynomial (Fin n) (RatFunc k)),
  (∀ i, (f i).IsHomogeneous d) → 0 < d → r * d < n → ∃ x : Fin n → RatFunc k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 :=
  tsenLang_ratFunc

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoStepRecursionLocalEulerFactors
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.LocSer

theorem step (x y : ℂ) (c : ℕ → ℂ) (h1 : c 1 = x + y) (h0 : c 0 = 1)
    (hr : ∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r) :
    ∀ r, c (r + 1) = y * c r + x ^ (r + 1) := by
  intro r
  induction r with
  | zero => rw [h1, h0]; ring
  | succ n ih => rw [hr n, ih]; ring

theorem bound (x y z : ℂ) (c : ℕ → ℂ) (h0 : c 0 = 1)
    (hs : ∀ r, c (r + 1) = y * c r + x ^ (r + 1)) :
    ∀ r : ℕ, ‖c r * z ^ r‖ ≤ ((r : ℝ) + 1) * (max ‖x * z‖ ‖y * z‖) ^ r := by
  intro r
  induction r with
  | zero => simp [h0]
  | succ n ih =>
    have e : c (n + 1) * z ^ (n + 1) = (y * z) * (c n * z ^ n) + (x * z) ^ (n + 1) := by
      rw [hs n]; ring
    rw [e]
    set ρ := max ‖x * z‖ ‖y * z‖
    have hx : ‖x * z‖ ≤ ρ := le_max_left _ _
    have hy : ‖y * z‖ ≤ ρ := le_max_right _ _
    have hρ : 0 ≤ ρ := le_trans (norm_nonneg _) hx
    calc ‖(y * z) * (c n * z ^ n) + (x * z) ^ (n + 1)‖
        ≤ ‖y * z‖ * ‖c n * z ^ n‖ + ‖x * z‖ ^ (n + 1) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_pow]
      _ ≤ ρ * (((n : ℝ) + 1) * ρ ^ n) + ρ ^ (n + 1) := by
          gcongr
      _ = (((n + 1 : ℕ) : ℝ) + 1) * ρ ^ (n + 1) := by push_cast; ring

theorem summ1 (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun r : ℕ => ((r : ℝ) + 1) * ρ ^ r) := by
  have hn : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have a := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have b := summable_geometric_of_lt_one h0 h1
  exact (a.add b).congr (fun r => by ring)

theorem summ2 (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun r : ℕ => ((r : ℝ) + 1) ^ 2 * ρ ^ r) := by
  have hn : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have a := summable_pow_mul_geometric_of_norm_lt_one 2 hn
  have a1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have b := summable_geometric_of_lt_one h0 h1
  exact ((a.add (a1.mul_left 2)).add b).congr (fun r => by ring)

theorem part1 (x y z : ℂ) (c : ℕ → ℂ) (h0 : c 0 = 1)
    (hs : ∀ r, c (r + 1) = y * c r + x ^ (r + 1))
    (hx : ‖x * z‖ < 1) (hy : ‖y * z‖ < 1) :
    Summable (fun r => c r * z ^ r) ∧ (∑' r, c r * z ^ r) * ((1 - x * z) * (1 - y * z)) = 1 := by
  set ρ := max ‖x * z‖ ‖y * z‖
  have hρ1 : ρ < 1 := max_lt hx hy
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (le_max_left _ _)
  have hS : Summable (fun r => c r * z ^ r) :=
    Summable.of_norm_bounded (summ1 ρ hρ0 hρ1) (bound x y z c h0 hs)
  refine ⟨hS, ?_⟩
  have hG := tsum_geometric_of_norm_lt_one hx
  have hGs := summable_geometric_of_norm_lt_one hx
  have hne : (1 : ℂ) - x * z ≠ 0 := by
    intro h
    have : x * z = 1 := by linear_combination -h
    rw [this, norm_one] at hx; exact lt_irrefl _ hx
  have hG' : (∑' n : ℕ, (x * z) ^ n) * (1 - x * z) = 1 := by
    rw [hG]; exact inv_mul_cancel₀ hne
  have e1 := hS.tsum_eq_zero_add
  have e2 : ∀ r : ℕ, c (r + 1) * z ^ (r + 1) = (y * z) * (c r * z ^ r) + (x * z) * (x * z) ^ r := by
    intro r; rw [hs r]; ring
  simp_rw [e2] at e1
  rw [Summable.tsum_add (hS.mul_left _) (hGs.mul_left _), tsum_mul_left, tsum_mul_left, h0] at e1
  simp only [pow_zero, mul_one] at e1
  linear_combination (1 - x * z) * e1 + (x * z) * hG'

theorem part2 (x y : ℂ) (c : ℕ → ℂ) (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T < 1) (hx : ‖x‖ ^ 2 * T < 1)
    (hy : ‖y‖ ^ 2 * T < 1) (h0 : c 0 = 1) (hs : ∀ r, c (r + 1) = y * c r + x ^ (r + 1)) :
    (∑' r : ℕ, ‖c r‖ ^ 2 * T ^ r) * ((1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2)
      = 1 - ‖x * y‖ ^ 2 * T ^ 2 := by
  have hnx : 0 ≤ ‖x‖ := norm_nonneg _
  have hny : 0 ≤ ‖y‖ := norm_nonneg _
  have hnT : ‖(T : ℂ)‖ = T := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0]
  have hxy : ‖y‖ * (‖x‖ * T) < 1 := by
    have hp := mul_lt_mul'' hx hy (by positivity) (by positivity)
    have e : (‖y‖ * (‖x‖ * T)) ^ 2 = (‖x‖ ^ 2 * T) * (‖y‖ ^ 2 * T) := by ring
    have : (‖y‖ * (‖x‖ * T)) ^ 2 < 1 := by rw [e]; linarith
    nlinarith [mul_nonneg hny (mul_nonneg hnx hT0)]

  set m := max ‖x‖ ‖y‖ with hm
  have hσ : m ^ 2 * T < 1 := by
    rcases max_choice ‖x‖ ‖y‖ with h | h <;> rw [hm, h] <;> assumption
  have hb : ∀ r : ℕ, ‖c r‖ ≤ ((r : ℝ) + 1) * m ^ r := by
    intro r; have := bound x y 1 c h0 hs r; simpa using this
  have hU : Summable (fun r : ℕ => ‖c r‖ ^ 2 * T ^ r) := by
    refine Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_)
      (summ2 (m ^ 2 * T) (by positivity) hσ)
    calc ‖c r‖ ^ 2 * T ^ r ≤ (((r : ℝ) + 1) * m ^ r) ^ 2 * T ^ r := by
          gcongr; exact hb r
      _ = ((r : ℝ) + 1) ^ 2 * (m ^ 2 * T) ^ r := by ring
  have hf : ∀ r : ℕ, c r * conj (c r) * (T : ℂ) ^ r = ((‖c r‖ ^ 2 * T ^ r : ℝ) : ℂ) := by
    intro r; push_cast; rw [Complex.mul_conj']
  have hVs : Summable (fun r : ℕ => c r * conj (c r) * (T : ℂ) ^ r) := by
    have := (Complex.summable_ofReal).mpr hU
    exact this.congr (fun r => (hf r).symm)
  have hVdef : ((∑' r : ℕ, ‖c r‖ ^ 2 * T ^ r : ℝ) : ℂ) = ∑' r : ℕ, c r * conj (c r) * (T : ℂ) ^ r := by
    rw [Complex.ofReal_tsum]; congr 1; funext r; exact (hf r).symm

  have hW : Summable (fun r => c r * (conj x * T) ^ r) ∧
      (∑' r, c r * (conj x * T) ^ r) * ((1 - x * (conj x * T)) * (1 - y * (conj x * T))) = 1 := by
    refine part1 x y (conj x * T) c h0 hs ?_ ?_
    · rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; nlinarith
    · rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; exact hxy
  have hW' : Summable (fun r => conj (c r) * (x * T) ^ r) ∧
      (∑' r, conj (c r) * (x * T) ^ r) * ((1 - conj x * (x * T)) * (1 - conj y * (x * T))) = 1 := by
    refine part1 (conj x) (conj y) (x * T) (fun r => conj (c r)) (by simp [h0]) ?_ ?_ ?_
    · intro r
      show conj (c (r + 1)) = conj y * conj (c r) + conj x ^ (r + 1)
      rw [hs r]; simp only [map_add, map_mul, map_pow]
    · rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; nlinarith
    · rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; linarith [hxy]
  have hGn : ‖x * conj x * (T : ℂ)‖ < 1 := by
    rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; nlinarith
  have hGs := summable_geometric_of_norm_lt_one hGn
  have hG : (∑' n : ℕ, (x * conj x * (T : ℂ)) ^ n) * (1 - x * conj x * T) = 1 := by
    rw [tsum_geometric_of_norm_lt_one hGn]
    refine inv_mul_cancel₀ ?_
    intro h
    have : x * conj x * (T : ℂ) = 1 := by linear_combination -h
    rw [this, norm_one] at hGn; exact lt_irrefl _ hGn
  have e1 := hVs.tsum_eq_zero_add
  have e2 : ∀ r : ℕ, c (r + 1) * conj (c (r + 1)) * (T : ℂ) ^ (r + 1) =
      (T : ℂ) * (y * conj y * (c r * conj (c r) * (T : ℂ) ^ r) + y * conj x * (c r * (conj x * T) ^ r)
        + x * conj y * (conj (c r) * (x * T) ^ r) + x * conj x * (x * conj x * T) ^ r) := by
    intro r; rw [hs r]; simp only [map_add, map_mul, map_pow]; ring
  simp_rw [e2] at e1
  rw [tsum_mul_left, Summable.tsum_add (((hVs.mul_left _).add (hW.1.mul_left _)).add (hW'.1.mul_left _))
    (hGs.mul_left _), Summable.tsum_add ((hVs.mul_left _).add (hW.1.mul_left _)) (hW'.1.mul_left _),
    Summable.tsum_add (hVs.mul_left _) (hW.1.mul_left _)] at e1
  simp only [tsum_mul_left, h0, map_one, pow_zero, mul_one] at e1
  have hW2 := hW.2
  have hW'2 := hW'.2
  set V := ∑' r : ℕ, c r * conj (c r) * (T : ℂ) ^ r
  set W := ∑' r, c r * (conj x * T) ^ r
  set W' := ∑' r, conj (c r) * (x * T) ^ r
  set G := ∑' n : ℕ, (x * conj x * (T : ℂ)) ^ n
  have key : V * ((1 - x * conj x * T) * (1 - y * conj y * T) * ((1 - x * conj y * T) * (1 - conj x * y * T)))
      = 1 - x * conj x * (y * conj y) * T ^ 2 := by
    linear_combination ((1 - x * conj x * T) * (1 - x * conj y * T) * (1 - conj x * y * T)) * e1
      + (T * y * conj x * (1 - x * conj y * T)) * hW2 + (T * x * conj y * (1 - conj x * y * T)) * hW'2
      + (x * conj x * T * (1 - x * conj y * T) * (1 - conj x * y * T)) * hG
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, hVdef]
  push_cast
  have hx2 : ((‖x‖ : ℂ)) ^ 2 = x * conj x := (Complex.mul_conj' x).symm
  have hy2 : ((‖y‖ : ℂ)) ^ 2 = y * conj y := (Complex.mul_conj' y).symm
  have hxy2 : ((‖x * y‖ : ℂ)) ^ 2 = x * y * conj (x * y) := (Complex.mul_conj' _).symm
  have hn2 : ((‖1 - x * conj y * T‖ : ℂ)) ^ 2 = (1 - x * conj y * T) * conj (1 - x * conj y * T) :=
    (Complex.mul_conj' _).symm
  rw [hx2, hy2, hxy2, hn2]
  simp only [map_mul, map_sub, map_one, Complex.conj_conj, Complex.conj_ofReal]
  linear_combination key

theorem twoStep_eulerFactors : ∀ (x y : ℂ) (c : ℕ → ℂ) (T : ℝ), 0 ≤ T → T < 1 → ‖x‖ ^ 2 * T < 1 → ‖y‖ ^ 2 * T < 1 → c 0 = 1 → c 1 = x + y → (∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r) → (∑' r : ℕ, c r * (T : ℂ) ^ r) * ((1 - x * T) * (1 - y * T)) = 1 ∧ (∑' r : ℕ, ‖c r‖ ^ 2 * T ^ r) * ((1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2) = 1 - ‖x * y‖ ^ 2 * T ^ 2 := by
  intro x y c T hT0 hT1 hx hy h0 h1 hr
  have hs := step x y c h1 h0 hr
  have hnT : ‖(T : ℂ)‖ = T := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0]
  have hsq : ∀ u : ℂ, ‖u‖ ^ 2 * T < 1 → ‖u * (T : ℂ)‖ < 1 := by
    intro u hu
    rw [norm_mul, hnT]
    have hn : 0 ≤ ‖u‖ * T := mul_nonneg (norm_nonneg _) hT0
    have : (‖u‖ * T) ^ 2 ≤ ‖u‖ ^ 2 * T := by
      have : (‖u‖ * T) ^ 2 = (‖u‖ ^ 2 * T) * T := by ring
      rw [this]
      exact mul_le_of_le_one_right (mul_nonneg (sq_nonneg _) hT0) hT1.le
    nlinarith
  exact ⟨(part1 x y T c h0 hs (hsq x hx) (hsq y hy)).2, part2 x y c T hT0 hT1 hx hy h0 hs⟩

end GlobalTheory.LocSer
end

