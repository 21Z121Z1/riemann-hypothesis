import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0074
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0075
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0046
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0006

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelChartPoly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RelChartPoly

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

theorem chartMonomial_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ e k ∈ relSecM R y e := by
  classical
  have h := monomial_mem_relSecM R y (b := e) (fun q : Σ k, ι k => if q.2 = c q.1 then e q.1 else 0)
    (fun k => by simp)
  convert h using 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp [pow_ite]

theorem coord_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) [DecidableEq K] :
    y p ∈ relSecM R y (Pi.single p.1 1) := by
  have h := chartMonomial_mem R y (Function.update c p.1 p.2) (Pi.single p.1 1)
  convert h using 1
  rw [Finset.prod_eq_single p.1]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

theorem generator_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Σ k, ι k) :
    y p / y ⟨p.1, c p.1⟩ * ∏ k, y ⟨k, c k⟩ ∈ relSecM R y (fun _ => 1) := by
  classical
  by_cases h0 : y ⟨p.1, c p.1⟩ = 0
  · simp [h0]
  have hW : ∏ k, y ⟨k, c k⟩ = (∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 (1 : ℕ) : K → ℕ) k) *
      ∏ k, y ⟨k, c k⟩ ^ (if k = p.1 then 0 else 1) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_add]
    by_cases hk : k = p.1
    · subst hk; simp
    · simp [hk]
  have h1 : ∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 (1 : ℕ) : K → ℕ) k = y ⟨p.1, c p.1⟩ := by
    rw [Finset.prod_eq_single p.1]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have hmem := mul_mem_relSecM R y (coord_mem R y c p)
    (chartMonomial_mem R y c (fun k => if k = p.1 then 0 else 1))
  have hb : (Pi.single p.1 1 + fun k => if k = p.1 then 0 else 1 : K → ℕ) = fun _ => 1 := by
    funext k
    by_cases hk : k = p.1
    · subst hk; simp
    · simp [hk]
  rw [hb] at hmem
  rw [hW, h1, ← mul_assoc, div_mul_cancel₀ _ h0]
  exact hmem

end RelChartPoly

theorem RelChartPoly.proof : RelChartPoly.Statement := by
  intro K _ ι _ Ω _ R y c σ hσ
  have hW : ∀ M : ℕ, (∏ k, y ⟨k, c k⟩) ^ M ∈ relSecM R y (fun _ => M) := by
    intro M
    rw [← Finset.prod_pow]
    exact RelChartPoly.chartMonomial_mem R y c (fun _ => M)
  have hmul : ∀ {a b : ℕ} {x x' : Ω}, x ∈ relSecM R y (fun _ => a) → x' ∈ relSecM R y (fun _ => b) →
      x * x' ∈ relSecM R y (fun _ => a + b) := fun hx hx' => mul_mem_relSecM R y hx hx'
  induction hσ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨1, by simpa using RelChartPoly.generator_mem R y c p⟩
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [pow_zero, mul_one, Algebra.algebraMap_eq_smul_one]
    refine Submodule.smul_mem _ r ?_
    simpa using hW 0
  | add x x' _ _ hx hx' =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hx'
    refine ⟨N + M, ?_⟩
    rw [add_mul]
    refine add_mem ?_ ?_
    · have := hmul hN (hW M)
      convert this using 1
      ring
    · have := hmul hM (hW N)
      rw [add_comm N M]
      convert this using 1
      ring
  | mul x x' _ _ hx hx' =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hx'
    refine ⟨N + M, ?_⟩
    have := hmul hN hM
    convert this using 1
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelTorsionBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace RelTorsionBound

attribute [local instance] MvPolynomial.weightedGradedAlgebra

section Lemmas

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def blockWeight : (Σ k, ι k) → (K → ℕ) := fun p => Pi.single p.1 1

theorem weight_blockWeight (μ : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockWeight (ι := ι)) μ = fun k => ∑ i, μ ⟨k, i⟩ := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma,
    Finset.sum_eq_single k]
  · simp [blockWeight]
  · intro k' _ hk
    simp [blockWeight, Ne.symm hk]
  · simp

omit [DecidableEq K] in

theorem aeval_monomial_one (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (μ : (Σ k, ι k) →₀ ℕ) :
    aeval y (monomial μ (1 : R)) = ∏ p, y p ^ μ p := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  simp

theorem relSecM_le_map (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (b : K → ℕ) :
    relSecM R y b ≤ (weightedHomogeneousSubmodule R (blockWeight (ι := ι)) b).map (aeval y).toLinearMap := by
  rw [relSecM, Submodule.span_le]
  rintro _ ⟨μ, hμ, rfl⟩
  refine ⟨monomial (Finsupp.equivFunOnFinite.symm μ) 1, ?_, ?_⟩
  · refine (mem_weightedHomogeneousSubmodule _ _ _ _).2 (isWeightedHomogeneous_monomial _ _ _ ?_)
    rw [weight_blockWeight]
    funext k
    simpa using hμ k
  · simp [aeval_monomial_one]

omit [Fintype K] [DecidableEq K] in

theorem exists_chart_le (N : ℕ) (μ : (Σ k, ι k) → ℕ)
    (h : ∀ k, Fintype.card (ι k) * N < ∑ i, μ ⟨k, i⟩) : ∃ c : ∀ k, ι k, ∀ k, N ≤ μ ⟨k, c k⟩ := by
  have hk : ∀ k, ∃ i, N ≤ μ ⟨k, i⟩ := by
    intro k
    by_contra hn
    simp only [not_exists, not_le] at hn
    have hle := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (hn i).le
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
    exact absurd (h k) (not_lt.2 hle)
  exact ⟨fun k => (hk k).choose, fun k => (hk k).choose_spec⟩

omit [Fintype K] [DecidableEq K] in
open Classical in

theorem sum_chart (c : ∀ k, ι k) (N : ℕ) (k : K) : ∑ i, (if c k = i then N else 0) = N := by
  rw [Finset.sum_ite_eq]
  simp

omit [DecidableEq K] in
open Classical in

theorem prod_chart (z : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (N : ℕ) :
    ∏ p : Σ k, ι k, z p ^ (if c p.1 = p.2 then N else 0) = (∏ k, z ⟨k, c k⟩) ^ N := by
  rw [Fintype.prod_sigma, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_eq_single (c k)]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

omit [DecidableEq K] in

theorem chart_pow_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (N : ℕ) :
    (∏ k, y ⟨k, c k⟩) ^ N ∈ relSecM R y (fun _ => N) := by
  classical
  rw [← prod_chart]
  exact monomial_mem_relSecM R y _ fun k => sum_chart c N k

omit [DecidableEq K] in

theorem exists_chart_factor (N : ℕ) (μ : (Σ k, ι k) → ℕ) (c : ∀ k, ι k) (hc : ∀ k, N ≤ μ ⟨k, c k⟩) :
    ∃ ν : (Σ k, ι k) → ℕ, (∀ k, ∑ i, ν ⟨k, i⟩ + N = ∑ i, μ ⟨k, i⟩) ∧
      ∀ z : (Σ k, ι k) → Ω, ∏ p, z p ^ μ p = (∏ p, z p ^ ν p) * (∏ k, z ⟨k, c k⟩) ^ N := by
  classical
  have hsplit : ∀ p : Σ k, ι k,
      μ p = (μ p - if c p.1 = p.2 then N else 0) + if c p.1 = p.2 then N else 0 := by
    intro p
    split_ifs with h
    · have hp : N ≤ μ p := by
        have := hc p.1
        rw [h] at this
        exact this
      omega
    · omega
  refine ⟨fun p => μ p - if c p.1 = p.2 then N else 0, fun k => ?_, fun z => ?_⟩
  · have hs : ∑ i, μ ⟨k, i⟩ = ∑ i, ((μ ⟨k, i⟩ - if c k = i then N else 0) + if c k = i then N else 0) :=
      Finset.sum_congr rfl fun i _ => hsplit ⟨k, i⟩
    rw [hs, Finset.sum_add_distrib, sum_chart]
  · rw [← prod_chart z c N, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_add, ← hsplit p]

omit [∀ k, Fintype (ι k)] in
open Classical in

theorem comp_mul (R : Type*) [CommRing R] {d : K → ℕ} (m : K → ℕ) {G : MvPolynomial (Σ k, ι k) R}
    (hG : G ∈ weightedHomogeneousSubmodule R (blockWeight (ι := ι)) d) (A : MvPolynomial (Σ k, ι k) R) :
    weightedHomogeneousComponent blockWeight m (A * G) =
      if d ≤ m then weightedHomogeneousComponent blockWeight (m - d) A * G else 0 := by
  have h := DirectSum.coe_decompose_mul_of_right_mem
    (𝒜 := weightedHomogeneousSubmodule R (blockWeight (ι := ι))) (a := A) m hG
  rw [← decompose'_apply R blockWeight, ← decompose'_apply R blockWeight]
  exact h

def KilledAt (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (k0 : K) (c : ∀ k, ι k) (d : K → ℕ)
    (N : ℕ) (v : Ω) : Prop :=
  ∃ a : K → ℕ, a + Pi.single k0 1 = d + (fun _ => N) ∧
    ∃ g ∈ relSecM R y a, (∏ k, y ⟨k, c k⟩) ^ N * v = y ⟨k0, c0 k0⟩ * g

theorem KilledAt.mono {R : Subalgebra ℤ Ω} {y : (Σ k, ι k) → Ω} {c0 : ∀ k, ι k} {k0 : K} {c : ∀ k, ι k}
    {d : K → ℕ} {N N' : ℕ} {v : Ω} (h : KilledAt R y c0 k0 c d N v) (hN : N ≤ N') :
    KilledAt R y c0 k0 c d N' v := by
  obtain ⟨a, ha, g, hg, hgv⟩ := h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine ⟨(fun _ => m) + a, ?_, (∏ k, y ⟨k, c k⟩) ^ m * g, mul_mem_relSecM R y (chart_pow_mem R y c m) hg, ?_⟩
  · funext k
    have := congrFun ha k
    simp only [Pi.add_apply] at this ⊢
    omega
  · linear_combination (∏ k, y ⟨k, c k⟩) ^ m * hgv

def TorsionForm (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (k0 : K) (d : K → ℕ) (N : ℕ)
    (G : MvPolynomial (Σ k, ι k) R) : Prop :=
  G ∈ weightedHomogeneousSubmodule R (blockWeight (ι := ι)) d ∧
    ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → KilledAt R y c0 k0 c d N (aeval y G)

theorem TorsionForm.mono {R : Subalgebra ℤ Ω} {y : (Σ k, ι k) → Ω} {c0 : ∀ k, ι k} {k0 : K} {d : K → ℕ}
    {N N' : ℕ} {G : MvPolynomial (Σ k, ι k) R} (h : TorsionForm R y c0 k0 d N G) (hN : N ≤ N') :
    TorsionForm R y c0 k0 d N' G :=
  ⟨h.1, fun c hc => (h.2 c hc).mono hN⟩

theorem aeval_mul_mem (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k) (k0 : K) {d a b : K → ℕ}
    {N : ℕ} (hN : 1 ≤ N) {G : MvPolynomial (Σ k, ι k) R} (hG : TorsionForm R y c0 k0 d N G)
    (ha : ∀ k, Fintype.card (ι k) * N < a k) (hab : a + d = b + Pi.single k0 1)
    {A : MvPolynomial (Σ k, ι k) R} (hA : A ∈ weightedHomogeneousSubmodule R (blockWeight (ι := ι)) a) :
    aeval y (A * G) ∈ (relSecM R y b).map (LinearMap.mulLeft R (y ⟨k0, c0 k0⟩)) := by
  rw [A.as_sum, Finset.sum_mul, map_sum]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have hwμ : Finsupp.weight blockWeight μ = a := hA (mem_support_iff.1 hμ)
  rw [weight_blockWeight] at hwμ
  obtain ⟨c, hc⟩ := exists_chart_le N μ fun k => by rw [congrFun hwμ k]; exact ha k
  obtain ⟨ν, hν, hfac⟩ := exists_chart_factor (Ω := Ω) N μ c hc
  have hval : aeval y (monomial μ (coeff μ A) * G) = algebraMap R Ω (coeff μ A) *
      ((∏ p, y p ^ ν p) * ((∏ k, y ⟨k, c k⟩) ^ N * aeval y G)) := by
    rw [show monomial μ (coeff μ A) = C (coeff μ A) * monomial μ 1 by rw [C_mul_monomial, mul_one],
      map_mul, map_mul, aeval_C, aeval_monomial_one, hfac y]
    ring
  by_cases hgood : ∀ k, y ⟨k, c k⟩ ≠ 0
  · obtain ⟨a', ha', g, hg, hgv⟩ := hG.2 c hgood
    have hdeg : (fun k => ∑ i, ν ⟨k, i⟩) + a' = b := by
      funext k
      have h1 := hν k
      have h2 := congrFun hwμ k
      have h3 := congrFun ha' k
      have h4 := congrFun hab k
      simp only [Pi.add_apply] at h3 h4 ⊢
      omega
    have hmem := mul_mem_relSecM R y (monomial_mem_relSecM R y ν fun k => rfl) hg
    rw [hdeg] at hmem
    refine ⟨coeff μ A • ((∏ p, y p ^ ν p) * g), Submodule.smul_mem _ _ hmem, ?_⟩
    rw [hval, hgv, LinearMap.mulLeft_apply, Algebra.smul_def]
    ring
  · simp only [not_forall, not_not] at hgood
    obtain ⟨k, hk⟩ := hgood
    have hprod : ∏ k, y ⟨k, c k⟩ = 0 := Finset.prod_eq_zero (Finset.mem_univ k) hk
    rw [hval, hprod, zero_pow (by omega), zero_mul, mul_zero, mul_zero]
    exact Submodule.zero_mem _

end Lemmas

theorem proof : RelTorsionBound.Statement := by
  intro K _ _ ι _ Ω _ R hR y c0 hc0 k0
  classical
  have := hR
  let s : Set (MvPolynomial (Σ k, ι k) R) := {G | ∃ d N, TorsionForm R y c0 k0 d N G}
  obtain ⟨t, hts, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset s).1 (IsNoetherian.noetherian (R := MvPolynomial (Σ k, ι k) R) _)
  have hs : ∀ G ∈ s, ∃ d N, TorsionForm R y c0 k0 d N G := fun G h => h
  choose! dG NG hdN using hs
  set N₀ := t.sup NG + 1 with hN₀
  have hT : ∀ G ∈ t, TorsionForm R y c0 k0 (dG G) N₀ G := fun G hG =>
    (hdN G (hts hG)).mono (by have := Finset.le_sup (f := NG) hG; omega)
  refine ⟨∑ k, (Fintype.card (ι k) * N₀ + 1) + ∑ G ∈ t, ∑ k, dG G k, fun b hb f hf hyp => ?_⟩
  obtain ⟨F, hF, rfl⟩ := relSecM_le_map R y _ hf
  choose! D g hg hgf using hyp
  have hFs : F ∈ s := by
    refine ⟨b + Pi.single k0 1, Finset.univ.sup D, hF, fun c hc => ?_⟩
    refine KilledAt.mono ⟨b + fun _ => D c, ?_, g c, hg c hc, hgf c hc⟩ (Finset.le_sup (Finset.mem_univ c))
    funext k
    simp only [Pi.add_apply]
    omega
  have hFt : F ∈ Submodule.span (MvPolynomial (Σ k, ι k) R) (t : Set (MvPolynomial (Σ k, ι k) R)) :=
    hspan ▸ Submodule.subset_span hFs
  obtain ⟨A, -, hA⟩ := Submodule.mem_span_finset.1 hFt
  have hFsum : F = ∑ G ∈ t, weightedHomogeneousComponent blockWeight (b + Pi.single k0 1) (A G * G) := by
    have h1 : weightedHomogeneousComponent blockWeight (b + Pi.single k0 1) F = F :=
      IsWeightedHomogeneous.weightedHomogeneousComponent_same ((mem_weightedHomogeneousSubmodule _ _ _ _).1 hF)
    rw [← h1]
    conv_lhs => rw [← hA]
    rw [map_sum]
    simp only [smul_eq_mul]
  suffices h : aeval y F ∈ (relSecM R y b).map (LinearMap.mulLeft R (y ⟨k0, c0 k0⟩)) by
    obtain ⟨g', hg', hgx⟩ := h
    exact ⟨g', hg', by simpa using hgx.symm⟩
  rw [hFsum, map_sum]
  refine Submodule.sum_mem _ fun G hG => ?_
  rw [comp_mul _ _ (hT G hG).1]
  split_ifs with hle
  · refine aeval_mul_mem R y c0 k0 (by omega) (hT G hG) (fun k => ?_) (tsub_add_cancel_of_le hle)
      (weightedHomogeneousComponent_mem _ _ _)
    have h1 : Fintype.card (ι k) * N₀ + 1 ≤ ∑ k, (Fintype.card (ι k) * N₀ + 1) :=
      Finset.single_le_sum (f := fun k => Fintype.card (ι k) * N₀ + 1) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k)
    have h2 : dG G k ≤ ∑ k, dG G k :=
      Finset.single_le_sum (f := fun k => dG G k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have h3 : ∑ k, dG G k ≤ ∑ G ∈ t, ∑ k, dG G k :=
      Finset.single_le_sum (f := fun G => ∑ k, dG G k) (fun _ _ => Nat.zero_le _) hG
    have h4 := hb k
    have h5 := hle k
    simp only [Pi.sub_apply, Pi.add_apply] at h5 ⊢
    omega
  · simp

end RelTorsionBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftDegreePolynomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ShiftDegreePolynomial

def toMultilinear {K : Type} {n : ℕ} (f : (Fin n → K → ℤ) → ℤ)
    (hadd : ∀ (bs : Fin n → K → ℤ) (j : Fin n) (x y : K → ℤ),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y)) :
    MultilinearMap ℤ (fun _ : Fin n => K → ℤ) ℤ where
  toFun := f
  map_update_add' := by
    intro inst m i x y
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    exact hadd m i x y
  map_update_smul' := by
    intro inst m i c x
    obtain rfl : inst = instDecidableEqFin n := Subsingleton.elim _ _
    exact (AddMonoidHom.mk' (fun x => f (Function.update m i x)) (hadd m i)).map_zsmul c x

theorem expand {K : Type} {n : ℕ} (f : (Fin n → K → ℤ) → ℤ)
    (hadd : ∀ (bs : Fin n → K → ℤ) (j : Fin n) (x y : K → ℤ),
      f (Function.update bs j (x + y)) = f (Function.update bs j x) + f (Function.update bs j y))
    (q : ℤ) (a b : K → ℤ) :
    f (fun _ => q • a + b) =
      ∑ s : Finset (Fin n), q ^ s.card * f (s.piecewise (fun _ => a) (fun _ => b)) := by
  have h1 := (toMultilinear f hadd).map_add_univ (fun _ => q • a) (fun _ => b)
  refine h1.trans (Finset.sum_congr rfl fun s _ => ?_)
  have h2 := (toMultilinear f hadd).map_piecewise_smul (fun _ => q)
    (s.piecewise (fun _ => a) (fun _ => b)) s
  have h3 : s.piecewise (fun i => q • s.piecewise (fun _ => a) (fun _ => b) i)
      (s.piecewise (fun _ => a) (fun _ => b)) = s.piecewise (fun _ => q • a) (fun _ => b) := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [h3, Finset.prod_const, smul_eq_mul] at h2
  exact h2

theorem genericFibre {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {D : ℕ} (hP : IsArithVar P (D + 1)) :
    GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime (P.map (MvPolynomial.map (Int.castRingHom ℚ))) ∧
      ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸ P.map (MvPolynomial.map (Int.castRingHom ℚ))) =
        ((D + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have : P.IsPrime := hPp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ P → m = 0 := by
    intro m hm
    have h1 : m ∈ P.comap (C : ℤ →+* MRing ι) := hm
    rw [show P.comap (C : ℤ →+* MRing ι) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hchar
  have hq : ReciprocityTheory.AnForm.R.extQ P = P.map (MvPolynomial.map (Int.castRingHom ℚ)) := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff]
    refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · rw [hq, hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · rw [hdim] at hform
    refine GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq _ _ ?_
    rw [hform]
    push_cast
    ring

theorem proof (h : MixedNumberPolynomial.Statement.{0}) : ShiftDegreePolynomial.Statement := by
  classical
  intro K _ ι _ P D a b hP
  obtain ⟨hprime, hdimq⟩ := genericFibre hP
  set Q := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hQ
  have hadd := (h ℚ K ι Q D hprime hdimq).2
  let f : (Fin D → K → ℤ) → ℤ := fun bs => GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ Q bs
  let c : Finset (Fin D) → ℤ := fun s => f (s.piecewise (fun _ => a) (fun _ => b))
  refine ⟨∑ s : Finset (Fin D), Polynomial.C (c s : ℝ) * Polynomial.X ^ s.card, ?_, ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s _ => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    simpa using Finset.card_le_univ s
  · rw [Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single Finset.univ]
    · simp [c, f, genDeg, hQ]
    · intro s _ hs
      rw [if_neg]
      intro hD
      apply hs
      rw [← Finset.card_eq_iff_eq_univ, Fintype.card_fin]
      exact hD.symm
    · intro hu
      exact absurd (Finset.mem_univ _) hu
  · intro q
    have hexp := expand f hadd (q : ℤ) a b
    have hg : genDeg P D ((q : ℤ) • a + b) = f (fun _ => (q : ℤ) • a + b) := rfl
    rw [hg, hexp, Polynomial.eval_finsetSum]
    push_cast
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [c, mul_comm]

end ShiftDegreePolynomial

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKoszulCechExact
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KoszulCech

noncomputable section

def KoszulCechExact.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (α : K → ℤ) (R : ℕ)
    (z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0),
    (∀ I : KH.Cell K ι 0, ∃ u : Fin R → LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V),
      (∀ j, u j ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-α)) ∧ ∑ j, u j * z j I = 1) →
    ∀ (c : K → ℤ) (n : ℕ),
      (∀ φ ∈ kosPart S ι V R α c 0 n, ∃ ψ ∈ kosPart S ι V R α c 1 n, kosD z 0 n ψ = φ) ∧
      (∀ p : ℕ, ∀ φ ∈ kosPart S ι V R α c (p + 1) n, kosD z p n φ = 0 →
        ∃ ψ ∈ kosPart S ι V R α c (p + 2) n, kosD z (p + 1) n ψ = φ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

