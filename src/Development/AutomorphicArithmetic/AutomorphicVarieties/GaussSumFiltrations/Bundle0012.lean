import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0011
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.DualLatticeIndexEqDiscrPowMulDetPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.FinSupp

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertQExpPadicCongruencePowPrimePow
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.QPow

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {p : ℕ} [Fact p.Prime] {ι : Qbar p ≃+* ℂ}

theorem norm_p (ι : Qbar p ≃+* ℂ) : ‖ι.symm (p : ℂ)‖ = (p : ℝ)⁻¹ := by
  rw [map_natCast]
  have h : ‖(algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]))‖ = ‖(p : ℚ_[p])‖ :=
    PadicAlgCl.norm_extends p _
  rw [map_natCast, Padic.norm_p] at h
  exact h

private theorem hasQ_const (c : ℂ) :
    HasQ (F := F) (fun _ : Hn F => c) (({0} : Set F).indicator fun _ => c) := by
  classical
  refine ⟨⟨1, one_pos, fun ξ hξ => ?_⟩, fun z => ?_⟩
  · have h0 : ξ = 0 := by
      by_contra hne
      exact hξ (by simp [Set.indicator_apply, hne])
    subst h0
    refine ⟨Or.inl rfl, ?_⟩
    rw [mul_zero]
    exact isIntegral_zero
  · have h := hasSum_single
      (f := fun ξ : F => (({0} : Set F).indicator (fun _ => c) ξ) * ez ξ z) 0
      (fun b hb => by simp [Set.indicator_apply, hb])
    convert h using 1
    simp [Set.indicator_apply, ez, reAt]

theorem small_const {r : ℝ} {g : Hn F → ℂ} (h : Small ι r g) (c : ℂ) :
    Small (F := F) ι ‖ι.symm c‖ (fun _ : Hn F => c) := by
  classical
  refine ⟨_, hasQ_const c, fun ξ => ?_⟩
  by_cases hξ : ξ = 0
  · simp [Set.indicator_apply, hξ]
  · simp [Set.indicator_apply, hξ]

theorem small_mono {r s : ℝ} {g : Hn F → ℂ} (h : Small ι r g) (hrs : r ≤ s) : Small ι s g := by
  obtain ⟨a, ha, hb⟩ := h
  exact ⟨a, ha, fun ξ => (hb ξ).trans hrs⟩

private theorem hasQ_add {f g : Hn F → ℂ} {a b : F → ℂ} (hf : HasQ f a) (hg : HasQ g b) :
    HasQ (f + g) (a + b) := by
  obtain ⟨⟨D, hD, hDa⟩, ha⟩ := hf
  obtain ⟨⟨E, hE, hEb⟩, hb⟩ := hg
  refine ⟨⟨D * E, Nat.mul_pos hD hE, fun ξ hξ => ?_⟩, fun z => ?_⟩
  · by_cases h0 : a ξ = 0
    · have hb0 : b ξ ≠ 0 := by
        intro hb0
        apply hξ
        simp [h0, hb0]
      obtain ⟨h1, h2⟩ := hEb ξ hb0
      refine ⟨h1, ?_⟩
      have h3 := (isIntegral_natCast (R := ℤ) (B := F) D).mul h2
      have e : ((D * E : ℕ) : F) * ξ = (D : F) * ((E : F) * ξ) := by
        push_cast
        ring
      rw [e]
      exact h3
    · obtain ⟨h1, h2⟩ := hDa ξ h0
      refine ⟨h1, ?_⟩
      have h3 := (isIntegral_natCast (R := ℤ) (B := F) E).mul h2
      have e : ((D * E : ℕ) : F) * ξ = (E : F) * ((D : F) * ξ) := by
        push_cast
        ring
      rw [e]
      exact h3
  · have h := (ha z).add (hb z)
    simp only [Pi.add_apply, add_mul]
    exact h

theorem small_add {r s : ℝ} {f g : Hn F → ℂ} (hf : Small ι r f) (hg : Small ι s g) : Small ι (max r s) (f + g) := by
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hg
  refine ⟨a + b, hasQ_add ha hb, fun ξ => ?_⟩
  rw [Pi.add_apply, map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (ha' ξ) (hb' ξ))

theorem small_mul {r s : ℝ} {f g : Hn F → ℂ} (hf : Small ι r f) (hg : Small ι s g) : Small ι (r * s) (f * g) := by
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hg
  have hr : 0 ≤ r := (norm_nonneg _).trans (ha' 0)
  have hs : 0 ≤ s := (norm_nonneg _).trans (hb' 0)
  obtain ⟨c, hc, hc'⟩ := hasQ_mul F f g a b ha hb
  refine ⟨c, hc, fun ξ => ?_⟩
  obtain ⟨t, ht⟩ := hc' ξ
  rw [ht, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr hs) fun η _ => ?_
  rw [map_mul, norm_mul]
  exact mul_le_mul (ha' η) (hb' (ξ - η)) (norm_nonneg _) hr

theorem small_nonneg {r : ℝ} {f : Hn F → ℂ} (hf : Small ι r f) : 0 ≤ r := by
  obtain ⟨a, -, hb⟩ := hf
  exact (norm_nonneg _).trans (hb 0)

theorem small_zero {r : ℝ} {f : Hn F → ℂ} (hf : Small ι r f) : Small ι r (0 : Hn F → ℂ) := by
  refine ⟨0, ⟨⟨1, one_pos, fun ξ hξ => (hξ rfl).elim⟩, fun z => ?_⟩, fun ξ => ?_⟩
  · simpa using (hasSum_zero : HasSum (fun _ : F => (0 : ℂ)) 0)
  · simpa using small_nonneg hf

theorem pow_sub_one {r : ℝ} {f : Hn F → ℂ} (h : Small ι r (f - 1)) (hr : r ≤ 1) :
    ∀ m : ℕ, Small ι r (f ^ m - 1) := by
  have hr0 := small_nonneg h
  intro m
  induction m with
  | zero => simpa using small_zero h
  | succ m ih =>
    have e : f ^ (m + 1) - 1 = (f ^ m - 1) * (f - 1) + ((f ^ m - 1) + (f - 1)) := by ring
    rw [e]
    have h1 := small_add (small_mul ih h) (small_add ih h)
    refine small_mono h1 ?_
    rw [max_self]
    exact max_le (mul_le_of_le_one_left hr0 hr) le_rfl

theorem sum_small {r : ℝ} {f : Hn F → ℂ} (h : Small ι r (f - 1)) (hr : r ≤ (p : ℝ)⁻¹) :
    ∀ n : ℕ, Small ι (p : ℝ)⁻¹ (∑ i ∈ Finset.range n, (f ^ i - 1)) := by
  have hp1 : (p : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  have hs : Small ι (p : ℝ)⁻¹ (f - 1) := small_mono h hr
  intro n
  induction n with
  | zero => simpa using small_zero hs
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 := small_add ih (pow_sub_one hs hp1 n)
    rwa [max_self] at h1

theorem pow_p {r : ℝ} {f : Hn F → ℂ} (h : Small ι r (f - 1)) (hr : r ≤ (p : ℝ)⁻¹) :
    Small ι (r * (p : ℝ)⁻¹) (f ^ p - 1) := by
  have key : ∀ x : ℂ, x ^ p - 1 =
      (x - 1) * ∑ i ∈ Finset.range p, (x ^ i - 1) + (p : ℂ) * (x - 1) := by
    intro x
    have hg := geom_sum_mul x p
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    linear_combination (-1 : ℂ) * hg
  have e : f ^ p - 1 = (f - 1) * ∑ i ∈ Finset.range p, (f ^ i - 1) +
      (fun _ : Hn F => (p : ℂ)) * (f - 1) := by
    funext z
    simp only [Pi.sub_apply, Pi.pow_apply, Pi.one_apply, Pi.mul_apply, Pi.add_apply,
      Finset.sum_apply]
    exact key (f z)
  rw [e]
  have h1 := small_mul h (sum_small h hr p)
  have h2 := small_mul (small_const h (p : ℂ)) h
  rw [norm_p ι] at h2
  refine small_mono (small_add h1 h2) ?_
  rw [mul_comm (p : ℝ)⁻¹ r, max_self]

theorem main : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ)
    (f : Hn F → ℂ), Small ι (p : ℝ)⁻¹ (f - 1) → ∀ N m : ℕ,
      Small ι ((p : ℝ)⁻¹ ^ (N + 1)) (f ^ (p ^ N * m) - 1) := by
  intro F _ _ _ p _ ι f h N m
  have hp0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hp1 : (p : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  have step : ∀ n : ℕ, Small ι ((p : ℝ)⁻¹ ^ (n + 1)) (f ^ (p ^ n) - 1) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      have h1 := pow_p ih (pow_le_of_le_one hp0 hp1 (Nat.succ_ne_zero n))
      rw [← pow_mul, ← pow_succ, ← pow_succ] at h1
      exact h1
  have h2 := pow_sub_one (step N) (pow_le_one₀ hp0 hp1) m
  rwa [← pow_mul] at h2

end GlobalTheory.QPow

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertQExp_padicCongruence_pow_prime_pow : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (f : Hn F → ℂ), Small ι (p : ℝ)⁻¹ (f - 1) → ∀ N m : ℕ, Small ι ((p : ℝ)⁻¹ ^ (N + 1)) (f ^ (p ^ N * m) - 1) := by
  first | exact @GlobalTheory.QPow.main | exact GlobalTheory.QPow.main | (intros; apply GlobalTheory.QPow.main <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertThetaSeriesPeriodicInversionFormula
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem thetaSeries_periodic_slash_frickeMatrix : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ (a b : F) (c : Fˣ) (T : Finset (κ → F)) (Φ : (κ → F) → ℂ), a ≠ 0 → b ≠ 0 → aL κ a ≤ aL κ b → IsReps (aL κ a) (aL κ b) T → (∀ x, Φ x ≠ 0 → x ∈ aL κ b) → (∀ x, ∀ l ∈ aL κ a, Φ (x + l) = Φ x) → sl0 k (toInf (wm c)) (th G Φ) = th G (wT G k t a c T Φ) := by
  classical
  intro F _ _ _ κ _ _ G hG t ht k hk a b c T Φ ha hb hab hT hsupp hper
  have hdec : ∀ x, Φ x = ∑ x₀ ∈ T, Φ x₀ * (if x - x₀ ∈ aL κ a then (1:ℂ) else 0) := by
    intro x
    have e2 : ∀ x₀ ∈ T, Φ x₀ * (if x - x₀ ∈ aL κ a then (1:ℂ) else 0) = Φ x * (if x - x₀ ∈ aL κ a then (1:ℂ) else 0) := by
      intro x₀ _
      split_ifs with h
      · have := hper x₀ (x - x₀) h
        rw [show x₀ + (x - x₀) = x by abel] at this
        rw [this]
      · simp
    rw [Finset.sum_congr rfl e2, ← Finset.mul_sum]
    by_cases h0 : Φ x = 0
    · simp [h0]
    · obtain ⟨y, ⟨hyT, hy⟩, huniq⟩ := hT.2 x (hsupp x h0)
      rw [Finset.sum_eq_single y]
      · simp [hy]
      · intro x₀ hx₀ hne
        rw [if_neg]
        intro hm
        exact hne (huniq x₀ ⟨hx₀, hm⟩)
      · intro h
        exact absurd hyT h
  have hW : ∀ y, wT G k t a c T Φ y = ∑ x₀ ∈ T, Φ x₀ * wT G k t a c {x₀} (fun _ => 1) y := by
    intro y
    simp only [wT, Finset.sum_singleton, one_mul]
    split_ifs
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x₀ _ => by ring)
    · simp
  have hsumL : ∀ x₀ ∈ T, ∀ z : Hn F, Summable fun x => (if x - x₀ ∈ aL κ a then (1:ℂ) else 0) * ez (QF G x) z := by
    intro x₀ hx₀ z
    refine (_root_.GlobalTheory.T.thetaSeries_holomorphic_qExpansion_of_bounded_coeff F κ G hG b _ 1 ?_ ?_).1 z
    · intro x hx
      have hm : x - x₀ ∈ aL κ a := by
        by_contra hm
        exact hx (if_neg hm)
      have := (aL κ b).add_mem (hab hm) (hT.1 x₀ hx₀)
      simpa using this
    · intro x
      split_ifs <;> simp
  have hsumR : ∀ (x₀ : κ → F) (z : Hn F), Summable fun y => wT G k t a c {x₀} (fun _ => (1:ℂ)) y * ez (QF G y) z := by
    intro x₀ z
    obtain ⟨-, ⟨N, hN, hN2⟩, -⟩ := _root_.GlobalTheory.T.dualLattice_index_eq_discr_pow_mul_det_pow F κ G hG
    have hc : (c : F) ≠ 0 := c.ne_zero
    have hNF : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
    refine (_root_.GlobalTheory.T.thetaSeries_holomorphic_qExpansion_of_bounded_coeff F κ G hG ((c:F) / ((N:F) * a)) _ ‖wC k t a (c:F)‖ ?_ ?_).1 z
    · intro y hy
      have hd : (a / c) • y ∈ dualL F G := by
        by_contra hd
        exact hy (by simp [wT, hd])
      have hw := (hN2 _ hd).1
      refine AddSubgroup.mem_map.2 ⟨_, hw, ?_⟩
      simp only [DistribMulAction.toAddMonoidHom_apply]
      rw [smul_smul, smul_smul]
      rw [show (c:F) / ((N:F) * a) * (N:F) * (a / c) = 1 by field_simp, one_smul]
    · intro y
      simp only [wT, Finset.sum_singleton, one_mul]
      split_ifs
      · simp [et, Complex.norm_exp]
      · simp
  have thL : ∀ z, th G Φ z = ∑ x₀ ∈ T, Φ x₀ * th G (fun x => if x - x₀ ∈ aL κ a then (1:ℂ) else 0) z := by
    intro z
    simp only [th]
    have e : ∀ x, Φ x * ez (QF G x) z = ∑ x₀ ∈ T, Φ x₀ * ((if x - x₀ ∈ aL κ a then (1:ℂ) else 0) * ez (QF G x) z) := by
      intro x
      rw [hdec x, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [tsum_congr e, Summable.tsum_finsetSum (fun x₀ hx₀ => (hsumL x₀ hx₀ z).mul_left (Φ x₀))]
    exact Finset.sum_congr rfl (fun x₀ _ => tsum_mul_left)
  have thR : ∀ z, th G (wT G k t a c T Φ) z = ∑ x₀ ∈ T, Φ x₀ * th G (wT G k t a c {x₀} (fun _ => (1:ℂ))) z := by
    intro z
    simp only [th]
    have e : ∀ y, wT G k t a c T Φ y * ez (QF G y) z = ∑ x₀ ∈ T, Φ x₀ * (wT G k t a c {x₀} (fun _ => (1:ℂ)) y * ez (QF G y) z) := by
      intro y
      rw [hW y, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [tsum_congr e, Summable.tsum_finsetSum (fun x₀ _ => (hsumR x₀ z).mul_left (Φ x₀))]
    exact Finset.sum_congr rfl (fun x₀ _ => tsum_mul_left)
  funext z
  rw [thR z]
  simp only [sl0]
  rw [thL, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x₀ _ => ?_)
  have := congrFun (_root_.GlobalTheory.T.hilbertThetaSeries_coset_inversion_formula F κ G hG t ht k hk a c x₀ ha) z
  simp only [sl0] at this
  rw [← this]
  ring

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertThetaSeries_periodic_inversion_formula : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ (a b : F) (c : Fˣ) (T : Finset (κ → F)) (Φ : (κ → F) → ℂ), a ≠ 0 → b ≠ 0 → aL κ a ≤ aL κ b → IsReps (aL κ a) (aL κ b) T → (∀ x, Φ x ≠ 0 → x ∈ aL κ b) → (∀ x, ∀ l ∈ aL κ a, Φ (x + l) = Φ x) → sl0 k (toInf (wm c)) (th G Φ) = th G (wT G k t a c T Φ) := by
  first | exact @GlobalTheory.HilbertThetaSeries.thetaSeries_periodic_slash_frickeMatrix | exact GlobalTheory.HilbertThetaSeries.thetaSeries_periodic_slash_frickeMatrix | (intros; apply GlobalTheory.HilbertThetaSeries.thetaSeries_periodic_slash_frickeMatrix <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.SystemCuspInfinityComponentCongrOne
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.CuspOne

theorem pow_sub_one_small (p : ℕ) [Fact p.Prime] (r : ℚ) (hr : ‖(r : ℚ_[p])‖ = 1) (k : ℕ) (hk : p - 1 ∣ k) :
    ‖((r : ℚ_[p]) ^ k - 1)‖ ≤ (p : ℝ)⁻¹ := by
  set x : ℤ_[p] := ⟨(r : ℚ_[p]), hr.le⟩ with hx
  have hxu : ‖x‖ = 1 := hr
  have h1 : PadicInt.toZMod x ≠ 0 := by
    intro h0
    have : x ∈ IsLocalRing.maximalIdeal ℤ_[p] := by rw [← PadicInt.ker_toZMod]; exact h0
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at this
    linarith
  obtain ⟨m, rfl⟩ := hk
  have h2 : PadicInt.toZMod (x ^ ((p - 1) * m) - 1) = 0 := by
    rw [map_sub, map_pow, map_one, pow_mul, ZMod.pow_card_sub_one_eq_one h1, one_pow, sub_self]
  have h3 : x ^ ((p - 1) * m) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[p] := by rw [← PadicInt.ker_toZMod]; exact h2
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at h3
  have h4 : ‖x ^ ((p - 1) * m) - 1‖ ≤ (p : ℝ) ^ (-1 : ℤ) :=
    (PadicInt.norm_le_pow_iff_norm_lt_pow_add_one _ (-1)).2 (by simpa using h3)
  have h5 : ((x ^ ((p - 1) * m) - 1 : ℤ_[p]) : ℚ_[p]) = (r : ℚ_[p]) ^ ((p - 1) * m) - 1 := by
    push_cast; rfl
  rw [← h5, ← PadicInt.norm_def]
  simpa using h4

theorem norm_qbar_rat (p : ℕ) [Fact p.Prime] (q : ℚ) : ‖((q : ℚ) : Qbar p)‖ = ‖(q : ℚ_[p])‖ := by
  have : ((q : ℚ) : Qbar p) = algebraMap ℚ_[p] (Qbar p) (q : ℚ_[p]) := by simp
  rw [this]
  exact PadicAlgCl.norm_extends p _

theorem toFin_aff {F : Type} [Field F] [NumberField F] (ξ : Fˣ) :
    toFin (aff ξ 0) = aff (Units.map (algebraMap F (Af F)).toMonoidHom ξ) 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toFin, aff]

theorem aff_mul {R : Type} [CommRing R] (a b : Rˣ) : aff (a * b) 0 = aff a 0 * aff b 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

theorem det_aff {R : Type} [CommRing R] (a : Rˣ) : (aff a 0).val.det = a := by
  simp [aff, Matrix.det_fin_two]

theorem weightSlash_hilbertAffine_apply {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (ξ : Fˣ) (g : Hn F → ℂ) :
    sl0 k (toInf (aff ξ 0)) g = fun z => g (act (toInf (aff ξ 0)) z) := by
  funext z
  simp [sl0, toInf, cmp, aff, UpperHalfPlane.denom]

theorem cusp_inf_one : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ (k : ℕ), p - 1 ∣ k → ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∀ (y y' z : (Af F)ˣ) (f : Hn F → ℂ), AtP p δ y' → (∀ γ, InG p δ γ → Small ι (p : ℝ)⁻¹ (sl0 k (toInf γ) f - 1)) → ∀ (γ : GL (Fin 2) F) (u : GL (Fin 2) (Af F)), TP γ.val.det → u ∈ KLev F 2 1 → toFin γ * aff y 0 = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y' 0 * u → Ψ (aff y 0) = sl k (toInf γ) (((absF y' ^ ((k : ℝ) / 2) : ℝ) : ℂ) • f) → Small ι (p : ℝ)⁻¹ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0) - 1) := by
  intro F _ _ _ p _ ι hp2 δ hδ k hk Ψ _ y y' z f hy' hf γ u hγ hu hmat hΨ
  have hpp : p.Prime := Fact.out
  have hkev : Even k := by
    have ho : Odd p := hpp.odd_of_ne_two hp2
    have : Even (p - 1) := Nat.Odd.sub_odd ho odd_one
    exact even_iff_two_dvd.2 ((even_iff_two_dvd.1 this).trans hk)
  have R := fun (g : Hn F → ℂ) => GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash F k g
  have hrhom : ∀ v (x : F), rhom x v = reAt v x := (R f).1
  obtain ⟨-, hdel⟩ := GlobalTheory.T.exists_different_generator_totallyPositive_translate F p hpp
  obtain ⟨ξ, hξTP, hξy⟩ := hdel δ hδ y
  set ξa : (Af F)ˣ := Units.map (algebraMap F (Af F)).toMonoidHom ξ with hξa
  set γ₁ : GL (Fin 2) F := γ * (aff ξ 0)⁻¹ with hγ₁
  have hγeq : γ = γ₁ * aff ξ 0 := by simp [γ₁]
  have hmat₁ : toFin γ₁ * aff (ξa * y) 0 = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y' 0 * u := by
    rw [← hmat, aff_mul, hγ₁, map_mul, map_inv, toFin_aff]
    simp only [← hξa, mul_assoc, inv_mul_cancel_left]
  have hdet₁ : γ₁.val.det = γ.val.det / ξ := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hγ₁, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, det_aff, div_eq_mul_inv]
  have hTP₁ : TP γ₁.val.det := fun v => by
    have h1 : γ.val.det = γ₁.val.det * ξ := by rw [hdet₁, div_mul_cancel₀ _ ξ.ne_zero]
    have h2 := hγ v
    rw [h1, ← hrhom, map_mul, Pi.mul_apply, hrhom, hrhom] at h2
    exact (mul_pos_iff_of_pos_right (hξTP v)).1 h2
  obtain ⟨-, -, hgp⟩ := GlobalTheory.T.exists_inG_scalar_mul_and_abs_norm_det_mul_absF_eq F p δ hδ
  obtain ⟨η, r, hInG, hr0, hrn, hnorm⟩ := hgp (ξa * y) y' z γ₁ u hξy hy' hTP₁ hu hmat₁
  set γ₂ : GL (Fin 2) F := Matrix.GeneralLinearGroup.scalar (Fin 2) η * γ₁ with hγ₂
  set G : Hn F → ℂ := sl0 k (toInf γ₂) f with hGdef
  have hG := hf γ₂ hInG
  have hPos₁ : Pos (toInf γ₁) := ((R f).2.1 γ₁).1.2 hTP₁
  have hPosξ : Pos (toInf (aff ξ 0)) := ((R f).2.1 _).1.2 (by rw [det_aff]; exact hξTP)
  set c' : ℂ := ((absF y' ^ ((k : ℝ) / 2) : ℝ) : ℂ) with hc'
  set Nd : ℝ := |((Algebra.norm ℚ γ₂.val.det : ℚ) : ℝ)| with hNd
  set Nξ : ℝ := |((Algebra.norm ℚ (aff ξ 0).val.det : ℚ) : ℝ)| with hNξ
  have e1 : sl k (toInf γ) (c' • f) = sl k (toInf (aff ξ 0)) (sl k (toInf γ₁) (c' • f)) := by
    rw [hγeq, map_mul]
    exact (GlobalTheory.HilbertThetaSeries.SlashCocycle.slash_cocycle F k _ _ _ hPos₁ hPosξ).2.2.2.1
  have e2 : sl k (toInf γ₁) (c' • f) = sl k (toInf γ₂) (c' • f) := by
    have h := ((R (c' • f)).2.2.1 hkev (Units.map (rhom (F := F)).toMonoidHom η) (toInf γ₁) hPos₁).2
    rw [← (R f).2.2.2.1 η, ← map_mul] at h
    exact h.symm
  have e3 : sl k (toInf γ₂) (c' • f) = ((Nd ^ ((k : ℝ) / 2) : ℝ) : ℂ) • (c' • G) := by
    rw [((R (c' • f)).2.1 γ₂).2, (GlobalTheory.HilbertThetaSeries.slash_add_smul_pow F k 1 (toInf γ₂) f f c').2.1]
  have e4 : sl k (toInf (aff ξ 0)) (((Nd ^ ((k : ℝ) / 2) : ℝ) : ℂ) • (c' • G)) =
      (((Nd ^ ((k : ℝ) / 2) : ℝ) : ℂ) * c' * ((Nξ ^ ((k : ℝ) / 2) : ℝ) : ℂ)) • sl0 k (toInf (aff ξ 0)) G := by
    rw [smul_smul, (GlobalTheory.HilbertThetaSeries.slash_add_smul_pow F k 1 (toInf (aff ξ 0)) G G _).2.2.2.2.1, ((R G).2.1 (aff ξ 0)).2, smul_smul]

  obtain ⟨hA0, hAmul, -, hAprod⟩ := UpperTheory.V.Sd.Hm.absf F
  have hNξ' : Nξ * absF ξa = 1 := by
    rw [hNξ, det_aff, ← ((R f).2.2.2.2 (ξ : F)).1, Finset.abs_prod]
    exact hAprod ξ
  have hreal : Nd ^ ((k : ℝ) / 2) * absF y' ^ ((k : ℝ) / 2) * Nξ ^ ((k : ℝ) / 2) =
      ((r : ℝ) ^ k) * absF y ^ ((k : ℝ) / 2) := by
    have h0 : Nd * absF y' * Nξ = (r : ℝ) ^ 2 * absF y := by
      rw [hNd, hnorm, hAmul]
      calc (r : ℝ) ^ 2 * (absF ξa * absF y) * Nξ = (r : ℝ) ^ 2 * absF y * (Nξ * absF ξa) := by ring
        _ = _ := by rw [hNξ', mul_one]
    have hNd0 : 0 ≤ Nd := abs_nonneg _
    have hNξ0 : 0 ≤ Nξ := abs_nonneg _
    have hy'0 : 0 ≤ absF y' := (hA0 y').le
    rw [← Real.mul_rpow hNd0 hy'0, ← Real.mul_rpow (mul_nonneg hNd0 hy'0) hNξ0, h0,
      Real.mul_rpow (sq_nonneg _) (hA0 y).le, ← Real.rpow_natCast ((r : ℝ)) 2, ← Real.rpow_mul (by exact_mod_cast hr0.le)]
    congr 1
    rw [← Real.rpow_natCast]
    congr 1
    push_cast; ring
  have hy0 : ((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (hA0 y) _).ne'
  set H : Hn F → ℂ := sl0 k (toInf (aff ξ 0)) G with hHdef
  set c : ℂ := ((r : ℚ) : ℂ) ^ k with hcdef
  have key : (((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ * (((Nd ^ ((k : ℝ) / 2) : ℝ) : ℂ) * c' * ((Nξ ^ ((k : ℝ) / 2) : ℝ) : ℂ)) = c := by
    rw [hc', inv_mul_eq_iff_eq_mul₀ hy0]
    have := congrArg (fun x : ℝ => (x : ℂ)) hreal
    push_cast at this ⊢
    rw [this, hcdef]
    ring
  have hΨ' : (((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0) = c • H := by
    rw [hΨ, e1, e2, e3, e4, smul_smul, key]
  rw [hΨ']

  obtain ⟨a, ha, hb⟩ := hG
  have S1 : Small ι (p : ℝ)⁻¹ (H - 1) := by
    have hq := GlobalTheory.T.hasQExpansion_affineTranslate_coeff F k (G - 1) a ξ 0 hξTP ha
    have hH1 : sl0 k (toInf (aff ξ 0)) (G - 1) = H - 1 := by
      rw [hHdef, weightSlash_hilbertAffine_apply, weightSlash_hilbertAffine_apply]; funext w; simp
    rw [hH1] at hq
    refine ⟨_, hq, fun x => ?_⟩
    simpa [et] using hb (x / ξ)
  have Q := GlobalTheory.T.hilbertQExp_padicBound_algebra_properties F p ι
  have hc : ‖ι.symm c‖ = 1 := by
    rw [hcdef, map_pow, map_ratCast, norm_pow, norm_qbar_rat, hrn, one_pow]
  have hc1 : ‖ι.symm (c - 1)‖ ≤ (p : ℝ)⁻¹ := by
    have : ι.symm (c - 1) = (((r ^ k - 1 : ℚ)) : Qbar p) := by
      rw [hcdef, map_sub, map_pow, map_ratCast, map_one]; push_cast; rfl
    rw [this, norm_qbar_rat]
    have h := pow_sub_one_small p r hrn k hk
    push_cast
    exact h
  have hS2 := (Q _ _ (H - 1) (H - 1) c S1 S1).2.2.1
  have hS3 := (Q _ _ (H - 1) (H - 1) (c - 1) S1 S1).2.2.2.2.2
  have hsum := (Q _ _ _ _ 0 hS2 hS3).1
  have heq : c • H - 1 = c • (H - 1) + fun _ => c - 1 := by
    funext w; simp; ring
  rw [heq]
  exact (Q _ _ _ _ 0 hsum S1).2.2.2.1 (by rw [hc, one_mul]; exact max_le le_rfl hc1)

end GlobalTheory.HilbertThetaSeries.CuspOne

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.system_cusp_infinity_component_congr_one : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ (k : ℕ), p - 1 ∣ k → ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∀ (y y' z : (Af F)ˣ) (f : Hn F → ℂ), AtP p δ y' → (∀ γ, InG p δ γ → Small ι (p : ℝ)⁻¹ (sl0 k (toInf γ) f - 1)) → ∀ (γ : GL (Fin 2) F) (u : GL (Fin 2) (Af F)), TP γ.val.det → u ∈ KLev F 2 1 → toFin γ * aff y 0 = Matrix.GeneralLinearGroup.scalar (Fin 2) z * aff y' 0 * u → Ψ (aff y 0) = sl k (toInf γ) (((absF y' ^ ((k : ℝ) / 2) : ℝ) : ℂ) • f) → Small ι (p : ℝ)⁻¹ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0) - 1) := by
  first | exact @GlobalTheory.HilbertThetaSeries.CuspOne.cusp_inf_one | exact GlobalTheory.HilbertThetaSeries.CuspOne.cusp_inf_one | (intros; apply GlobalTheory.HilbertThetaSeries.CuspOne.cusp_inf_one <;> assumption)
end

