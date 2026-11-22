import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0032
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSublatticeDegree

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConductor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace Conductor

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def invMon (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ : K → ℕ) : Ω := ∏ k, (y ⟨k, c k⟩ ^ δ k)⁻¹

theorem invMon_add (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ ε : K → ℕ) :
    invMon y c (δ + ε) = invMon y c δ * invMon y c ε := by
  rw [invMon, invMon, invMon, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add, mul_inv]

theorem invMon_sum {β : Type} (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (s : Finset β) (δ : β → K → ℕ) :
    ∏ b ∈ s, invMon y c (δ b) = invMon y c (∑ b ∈ s, δ b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [invMon]
  | insert b s hb ih => rw [Finset.prod_insert hb, Finset.sum_insert hb, ih, invMon_add]

theorem prod_zpow_eq_invMon (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (-(δ k : ℤ)) = invMon y c δ := by
  simp [invMon, zpow_neg, zpow_natCast]

theorem form_mul_invMon_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {δ : K → ℕ} {g : MRing ι}
    (hg : IsMultiHomog g δ) : aeval y g * invMon y c δ ∈ chartRingZ y c := by
  rw [← prod_zpow_eq_invMon, NmSectionsRationalProof.aeval_mul_prod_zpow y c hg, chartRingZ,
    Algebra.adjoin_range_eq_range_aeval]
  exact ⟨g, rfl⟩

theorem isFractionRing_chartRingZ (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : IsFractionRing (chartRingZ y c) Ω := by
  refine IsFractionRing.of_field (chartRingZ y c) Ω fun z => ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hbir z
  have hP : invMon y c d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => inv_ne_zero (pow_ne_zero _ (hc k))
  refine ⟨⟨_, form_mul_invMon_mem y c hg⟩, ⟨_, form_mul_invMon_mem y c hh⟩, ?_⟩
  change z = aeval y g * _ / (aeval y h * _)
  rw [hgh, mul_assoc, mul_div_assoc, div_self (mul_ne_zero hh0 hP), mul_one]

theorem exists_chart_conductor (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (δ : K → ℕ) (F : MRing ι), IsMultiHomog F δ ∧ aeval y F ≠ 0 ∧
      ∀ x ∈ integralClosure (chartRingZ y c) Ω, aeval y F * invMon y c δ * x ∈ chartRingZ y c := by
  classical
  set A := chartRingZ y c
  have := isFractionRing_chartRingZ y hbir c hc
  have : Algebra.FiniteType ℤ A := .adjoin_of_finite (Set.finite_range _)
  have hfin : Module.Finite A (integralClosure A Ω) := Model.FiniteIntegralClosure.proof A Ω Ω
  obtain ⟨s, hs⟩ := hfin.fg_top
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
    (s.image fun z : integralClosure A Ω => (z : Ω))
  have key : ∀ z : integralClosure A Ω, ((b : A) : Ω) * (z : Ω) ∈ A := by
    intro z
    have hz : z ∈ Submodule.span A (s : Set (integralClosure A Ω)) := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨u, hu⟩ := hb _ (Finset.mem_image_of_mem _ hw)
      have : (u : Ω) = ((b : A) : Ω) * (w : Ω) := by rw [Algebra.smul_def] at hu; exact hu
      rw [← this]; exact u.2
    | zero => simp
    | add w v _ _ hw hv => rw [Subalgebra.coe_add, mul_add]; exact add_mem hw hv
    | smul r w _ hw =>
      rw [Subalgebra.coe_smul, Algebra.smul_def, mul_left_comm]
      exact mul_mem r.2 hw
  have hb0 : ((b : A) : Ω) ≠ 0 := by
    intro h
    exact nonZeroDivisors.coe_ne_zero b (Subtype.ext h)
  obtain ⟨δ, e, he, hv⟩ := SectionBounded.exists_form_of_mem_chartRingZ y c hc (b : A).2
  have hm : (∏ k, y ⟨k, c k⟩ ^ δ k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hbv : aeval y e * invMon y c δ = ((b : A) : Ω) := by
    rw [hv, invMon, Finset.prod_inv_distrib, mul_assoc, mul_inv_cancel₀ hm, mul_one]
  refine ⟨δ, e, he, by rw [hv]; exact mul_ne_zero hb0 hm, fun x hx => ?_⟩
  rw [hbv]
  exact key ⟨x, hx⟩

theorem homog_prod {β : Type} (s : Finset β) (F : β → MRing ι) (δ : β → K → ℕ)
    (h : ∀ b ∈ s, IsMultiHomog (F b) (δ b)) : IsMultiHomog (∏ b ∈ s, F b) (∑ b ∈ s, δ b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (SectionBounded.homog_one (ι := ι))
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    exact SectionBounded.homog_mul (h b (Finset.mem_insert_self b s))
      (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))

end Conductor

theorem Conductor.proof (hS : SecEq.Statement) : KH.CondStatement := by
  classical
  intro K _ ι _ Ω _ y a ha hy hbir
  obtain ⟨τ₀, hτ₀⟩ := hS K ι Ω y a ha hy
  let C := {c : ∀ k, ι k // ∀ k, y ⟨k, c k⟩ ≠ 0}
  choose δ F hF hF0 hcond using fun c : C => Conductor.exists_chart_conductor y hbir c.1 c.2
  choose i0 hi0 using hy
  set Δ : K → ℕ := ∑ c : C, δ c
  set k' : ℕ := τ₀ + ∑ κ, Δ κ
  have hΔ : ∀ κ, Δ κ ≤ k' * a κ := fun κ =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ κ)).trans
      ((Nat.le_add_left _ _).trans (Nat.le_mul_of_pos_right _ (ha κ)))
  set e : K → ℕ := fun κ => k' * a κ - Δ κ
  set Φ : MRing ι := (∏ c : C, F c) * SectionBounded.chartMon i0 e
  have hΦ : IsMultiHomog Φ (fun κ => k' * a κ) :=
    SectionBounded.homog_congr (SectionBounded.homog_mul
      (Conductor.homog_prod Finset.univ F δ fun c _ => hF c) (SectionBounded.homog_chartMon i0 e))
      fun κ => by simp only [Pi.add_apply, e]; exact Nat.add_sub_cancel' (hΔ κ)
  have hM : aeval y (SectionBounded.chartMon i0 e) ≠ 0 := by
    rw [SectionBounded.aeval_chartMon]
    exact Finset.prod_ne_zero_iff.mpr fun κ _ => pow_ne_zero _ (hi0 κ)
  have hΦ0 : aeval y Φ ≠ 0 := by
    rw [map_mul, map_prod]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun c _ => hF0 c) hM
  refine ⟨k', Φ, hΦ, hΦ0, fun τ s hs => ?_⟩
  rw [← hτ₀ (τ + k') (by omega)]
  intro c' hc'
  set c : C := ⟨c', hc'⟩
  have hx := hs c' hc'
  have hτ : (fun κ => τ * a κ) + Δ + e = fun κ => (τ + k') * a κ := by
    funext κ
    simp only [Pi.add_apply, e]
    rw [add_assoc, Nat.add_sub_cancel' (hΔ κ)]
    ring
  have hexp : ∀ n : K → ℕ, (∏ κ, y ⟨κ, c' κ⟩ ^ (-((n κ : ℕ) : ℤ))) = Conductor.invMon y c' n :=
    Conductor.prod_zpow_eq_invMon y c'
  beta_reduce at hx ⊢
  have e1 : ∀ κ, -((τ : ℤ) * (a κ : ℤ)) = -(((τ * a κ : ℕ)) : ℤ) := fun κ => by push_cast; ring
  have e2 : ∀ κ, -(((τ + k' : ℕ) : ℤ) * (a κ : ℤ)) = -((((τ + k') * a κ : ℕ)) : ℤ) := fun κ => by push_cast; ring
  simp only [e1] at hx
  simp only [e2]
  rw [hexp (fun κ => τ * a κ)] at hx
  rw [hexp (fun κ => (τ + k') * a κ), ← hτ, Conductor.invMon_add, Conductor.invMon_add,
    ← Conductor.invMon_sum y c' Finset.univ δ]
  have hsplit : aeval y Φ * s * (Conductor.invMon y c' (fun κ => τ * a κ) *
      (∏ b : C, Conductor.invMon y c' (δ b)) * Conductor.invMon y c' e) =
      (∏ b ∈ Finset.univ.erase c, aeval y (F b) * Conductor.invMon y c' (δ b)) *
        (aeval y (SectionBounded.chartMon i0 e) * Conductor.invMon y c' e) *
        (aeval y (F c) * Conductor.invMon y c' (δ c) * (s * Conductor.invMon y c' (fun κ => τ * a κ))) := by
    rw [map_mul, map_prod]
    rw [← Finset.mul_prod_erase Finset.univ (fun b => aeval y (F b)) (Finset.mem_univ c),
      ← Finset.mul_prod_erase Finset.univ (fun b => Conductor.invMon y c' (δ b)) (Finset.mem_univ c),
      Finset.prod_mul_distrib]
    ring
  rw [hsplit]
  refine mul_mem (mul_mem (prod_mem fun b _ => Conductor.form_mul_invMon_mem y c' (hF b))
    (Conductor.form_mul_invMon_mem y c' (SectionBounded.homog_chartMon i0 e))) ?_
  exact hcond c _ hx

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology MeasureTheory

noncomputable section

namespace ConstantShift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

theorem sheetDensity_add_const (P : Ideal (MRing ι)) {e : ℕ} {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ j, ∃ c : ℝ, ∀ z ∈ mcPts P, φ' j z = φ j z + c)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ' g y w = sheetDensity P Ψ φ g y w := by
  unfold sheetDensity
  split_ifs with hγ
  · congr 1
    have hH : ∀ k, cxHessian (fun y' => φ' k (hγ.choose y')) y =
        cxHessian (fun y' => φ k (hγ.choose y')) y := by
      intro k
      obtain ⟨c, hc⟩ := h k
      have h1 : (fun y' => φ' k (hγ.choose y')) =ᶠ[𝓝 y] fun y' => φ k (hγ.choose y') + c := by
        filter_upwards [hγ.choose_spec.2] with y' hy'
        exact hc _ hy'.2.1
      have h2 : fderiv ℝ (fun y' => φ' k (hγ.choose y')) =ᶠ[𝓝 y]
          fderiv ℝ (fun y' => φ k (hγ.choose y')) := by
        filter_upwards [h1.eventuallyEq_nhds] with x hx
        rw [hx.fderiv_eq, fderiv_add_const]
      unfold cxHessian
      rw [h2.fderiv_eq]
    simp only [maDensity, hH]
  · rfl

omit [∀ k, Fintype (ι k)] in

theorem ptsIntegral_add_const (P : Ideal (MRing ι)) {e : ℕ} {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ j, ∃ c : ℝ, ∀ z ∈ mcPts P, φ' j z = φ j z + c) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ' g = ptsIntegral P φ g := by
  unfold ptsIntegral
  split_ifs
  · simp only [ptsIntegralAt, sheetDensity_add_const P h]
  · rfl

omit [∀ k, Fintype (ι k)] in

theorem ptsIntegral_const (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (r : ℝ) :
    ptsIntegral P φ (fun _ => r) = r * ptsIntegral P φ (fun _ => 1) := by
  have hs : ∀ Ψ y w, sheetDensity P Ψ φ (fun _ => r) y w = r * sheetDensity P Ψ φ (fun _ => 1) y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs <;> simp
  unfold ptsIntegral
  split_ifs
  · simp only [ptsIntegralAt, hs]
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum_mem]
  · simp

theorem proof : ConstantShift.Statement := by
  intro K _ ι _ I P D A η hI hP hA
  have hS : IsSmoothHerm (HermLine.constShift A η) := isSmoothHerm_constShift hA η
  set g := geomDeg P A D with hg
  let L : ℕ → Fin (D + 1) → HermLine ι := fun n i =>
    if (i : ℕ) < n then HermLine.constShift A η else A
  have hLs : ∀ n i, IsSmoothHerm (L n i) := by
    intro n i
    dsimp only [L]
    split_ifs
    exacts [hS, hA]
  have hLpot : ∀ n i, ∃ c : ℝ, ∀ z ∈ mcPts P, Real.log ((L n i).h z) = Real.log (A.h z) + c := by
    intro n i
    dsimp only [L]
    split_ifs
    · refine ⟨-η, fun z hz => ?_⟩
      rw [constShift_h, Real.log_mul (A.pos z hz.1).ne' (Real.exp_pos _).ne', Real.log_exp]
    · exact ⟨0, fun z _ => by rw [add_zero]⟩
  have step : ∀ n, n < D + 1 → I P (D + 1) (L (n + 1)) = I P (D + 1) (L n) - η * g := by
    intro n hn
    set j : Fin (D + 1) := ⟨n, hn⟩ with hj
    set σ : Equiv.Perm (Fin (D + 1)) := Equiv.swap j (Fin.last D) with hσ
    set M : Fin D → HermLine ι := Fin.init (L n ∘ σ) with hMdef
    have hσl : σ (Fin.last D) = j := Equiv.swap_apply_right _ _
    have hne : ∀ i : Fin D, σ (Fin.castSucc i) ≠ j := by
      intro i h'
      rw [← hσl] at h'
      exact (Fin.castSucc_lt_last i).ne (σ.injective h')
    have hM : Fin.init (L (n + 1) ∘ σ) = M := by
      funext i
      have hv : ((σ (Fin.castSucc i) : Fin (D + 1)) : ℕ) ≠ n := fun h' => hne i (Fin.ext h')
      have hiff : ((σ (Fin.castSucc i) : Fin (D + 1)) : ℕ) < n + 1 ↔
          ((σ (Fin.castSucc i) : Fin (D + 1)) : ℕ) < n := by omega
      simp only [hMdef, Fin.init, Function.comp, L, hiff]
    have e0 : L n ∘ σ = Fin.snoc M A := by
      have h0 := Fin.snoc_init_self (q := L n ∘ σ)
      have hl : (L n ∘ σ) (Fin.last D) = A := by
        simp only [Function.comp, hσl, hj, L, lt_irrefl, if_false]
      rw [hl] at h0
      exact h0.symm
    have e1 : L (n + 1) ∘ σ = Fin.snoc M (HermLine.constShift A η) := by
      have h0 := Fin.snoc_init_self (q := L (n + 1) ∘ σ)
      have hl : (L (n + 1) ∘ σ) (Fin.last D) = HermLine.constShift A η := by
        simp only [Function.comp, hσl, hj, L, lt_add_one, if_true]
      rw [hl, hM] at h0
      exact h0.symm
    have hMs : ∀ i, IsSmoothHerm (M i) := fun i => hLs n _
    have hmc : I P (D + 1) (Fin.snoc M (HermLine.constShift A η)) =
        I P (D + 1) (Fin.snoc M A) - ptsIntegral P (pot M) (fun _ => η) :=
      metricChange K ι I hI P D M A (fun _ => η) (fun _ _ _ => rfl) hP hMs hA contDiffOn_const
    have hint : ptsIntegral P (pot M) (fun _ => η) = η * g := by
      rw [ptsIntegral_const, hg, geomDeg]
      congr 1
      exact ptsIntegral_add_const P (fun i => hLpot n _) _
    rw [← hI.1 P (D + 1) (L (n + 1)) σ hP (hLs (n + 1)), ← hI.1 P (D + 1) (L n) σ hP (hLs n), e0, e1,
      hmc, hint]
  have hall : ∀ n, n ≤ D + 1 → I P (D + 1) (L n) = I P (D + 1) (L 0) - n * η * g := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [step n (by omega), ih (by omega)]
      push_cast
      ring
  have hL0 : L 0 = fun _ => A := by
    funext i
    simp [L]
  have hLD : L (D + 1) = fun _ => HermLine.constShift A η := by
    funext i
    simp [L, i.isLt]
  have := hall (D + 1) le_rfl
  rw [hL0, hLD] at this
  rw [this]
  push_cast
  ring

end ConstantShift

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEuclideanSections
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

namespace EuclideanSections

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [∀ k, Fintype (ι k)] in

theorem mul_mem_chartLat {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n j : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a j) : s * t ∈ chartLat y a (n + j) := by
  intro c hc
  have h : ∏ k, y ⟨k, c k⟩ ^ (-(((n + j : ℕ) : ℤ) * a k)) =
      (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    push_cast
    ring
  rw [h, show s * t * ((∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) by ring]
  exact mul_mem (hs c hc) (ht c hc)

theorem isBoundedH_mono {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : HermLine ι} {τ : ℕ} {s : Ω}
    {c c' : ℝ} (hs : IsBoundedH P y A τ c s) (hc : c ≤ c') : IsBoundedH P y A τ c' s := by
  intro dg dh g h z hg hh hd he hz
  refine (hs dg dh g h z hg hh hd he hz).trans ?_
  have h0 : 0 ≤ A.h z ^ τ := pow_nonneg (A.pos z hz.1).le τ
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (norm_nonneg (eval z (map (Int.castRingHom ℂ) h)))) h0

theorem eventually_shift_le (D m : ℕ) (b E δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, n ≤ N → N ≤ n + m →
      b * ((N : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) + E * ((N : ℝ) + 1) ^ D ≤
        (b + δ) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hF0 : 0 < F := by positivity
  have hlin : ∀ c : ℝ, (fun n : ℕ => (n : ℝ) + c) ~[atTop] fun n : ℕ => (n : ℝ) := fun c =>
    IsEquivalent.refl.add_isLittleO ((isLittleO_const_id_atTop c).comp_tendsto tendsto_natCast_atTop_atTop)
  have hu : (fun n : ℕ => ((n : ℝ) + m) ^ (D + 1) - (n : ℝ) ^ (D + 1)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := (hlin m).pow (D + 1)
  have hv : (fun n : ℕ => ((n : ℝ) + (m + 1)) ^ D) =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) :=
    ((hlin (m + 1)).pow D).isBigO.trans_isLittleO
      ((isLittleO_pow_pow_atTop_of_lt (Nat.lt_succ_self D)).comp_tendsto tendsto_natCast_atTop_atTop)
  set c₁ := δ / (2 * (|b| + 1)) with hc₁
  set c₂ := δ / (2 * F * (|E| + 1)) with hc₂
  have hc₁0 : 0 < c₁ := by positivity
  have hc₂0 : 0 < c₂ := by positivity
  have hbc : |b| * c₁ ≤ δ / 2 := by
    rw [hc₁, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg b]
  have hEc : F * (|E| * c₂) ≤ δ / 2 := by
    rw [hc₂, mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg E]
  filter_upwards [hu.def hc₁0, hv.def hc₂0] with n h1 h2
  intro N hnN hNn
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hN1 : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hN2 : (N : ℝ) ≤ n + m := by exact_mod_cast hNn
  have hw : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1) := by positivity
  have hpow : (N : ℝ) ^ (D + 1) ≤ ((n : ℝ) + m) ^ (D + 1) := pow_le_pow_left₀ (by positivity) hN2 _
  have hpow' : (n : ℝ) ^ (D + 1) ≤ (N : ℝ) ^ (D + 1) := pow_le_pow_left₀ hn0 hN1 _
  have hv' : ((N : ℝ) + 1) ^ D ≤ ((n : ℝ) + (m + 1)) ^ D := pow_le_pow_left₀ (by positivity) (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw, abs_of_nonneg (by linarith)] at h1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw, abs_of_nonneg (by positivity)] at h2
  have hb : b * (N : ℝ) ^ (D + 1) ≤
      b * (n : ℝ) ^ (D + 1) + |b| * (((n : ℝ) + m) ^ (D + 1) - (n : ℝ) ^ (D + 1)) := by
    rcases le_total 0 b with hb | hb
    · rw [abs_of_nonneg hb]; nlinarith
    · nlinarith [abs_nonneg b, mul_le_mul_of_nonpos_left hpow' hb]
  have hE : E * ((N : ℝ) + 1) ^ D ≤ |E| * ((n : ℝ) + (m + 1)) ^ D :=
    (mul_le_mul_of_nonneg_right (le_abs_self E) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hv' (abs_nonneg E))
  have hb2 : |b| * (((n : ℝ) + m) ^ (D + 1) - (n : ℝ) ^ (D + 1)) ≤ δ / 2 * (n : ℝ) ^ (D + 1) :=
    (mul_le_mul_of_nonneg_left h1 (abs_nonneg b)).trans
      (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hbc hw)
  have hE2 : |E| * F * ((n : ℝ) + (m + 1)) ^ D ≤ δ / 2 * (n : ℝ) ^ (D + 1) := by
    have := mul_le_mul_of_nonneg_left h2 (mul_nonneg (abs_nonneg E) hF0.le)
    nlinarith [mul_le_mul_of_nonneg_right hEc hw]
  have key : b * (N : ℝ) ^ (D + 1) + F * (E * ((N : ℝ) + 1) ^ D) ≤ (b + δ) * (n : ℝ) ^ (D + 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hE hF0.le]
  rw [show b * ((N : ℝ) ^ (D + 1) / F) + E * ((N : ℝ) + 1) ^ D =
      (b * (N : ℝ) ^ (D + 1) + F * (E * ((N : ℝ) + 1) ^ D)) / F by field_simp, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right key hF0.le

end EuclideanSections

open EuclideanSections in

theorem EuclideanSections.proof (hP : EuclideanSectionsPower.Statement) (hS : SmallSectionsNonzero.Statement)
    (hL : SublatticeDegree.Statement) (hG : SuccessiveMinimaSpan.Statement) : EuclideanSections.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 II hD hII har hb hA hconj
  obtain ⟨r, φ, hinj, hdisc, hlat, hsup, hcon, ⟨Cr, hr⟩, m, hm, hdeg⟩ :=
    hP K ι Ω y D A P0 II hD hII har hb hA hconj
  obtain ⟨C, hC⟩ := hG K ι Ω y D A P0 hD har hb hA
  refine ⟨r, φ, hinj, hdisc, hlat, hsup, ⟨Cr, hr⟩, fun ε hε => ?_⟩
  set C₁ := max C 1 with hC₁
  have hC₁1 : (1 : ℝ) ≤ C₁ := le_max_right _ _
  have hlog : 0 ≤ Real.log C₁ := Real.log_nonneg hC₁1
  set I := II K ι (mCoordIdeal y) (D + 1) (fun _ => A) with hI
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 (hdeg (ε / 2) (half_pos hε))
  filter_upwards [eventually_shift_le D m (I + ε / 2) (Cr * Real.log C₁) (ε / 2) (half_pos hε),
    eventually_ge_atTop (m * Q)] with n hn hnQ
  intro _ _
  have hqQ : Q ≤ n / m + 1 := Nat.le_succ_of_le ((Nat.le_div_iff_mul_le hm).2 (by rw [mul_comm]; exact hnQ))
  have hnN : n ≤ m * (n / m + 1) := (Nat.lt_mul_div_succ n hm).le
  have hNn : m * (n / m + 1) ≤ n + m := by
    have := Nat.mul_div_le n m
    rw [mul_add, mul_one]
    omega
  suffices main : ∀ N : ℕ, n ≤ N → N ≤ n + m →
      -Real.log (ZLattice.covolume (imageLattice (φ N))) ≤
        (I + ε / 2) * ((N : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) →
      -Real.log (ZLattice.covolume (imageLattice (φ n))) ≤
        (I + ε) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) from
    main _ hnN hNn (hQ (n / m + 1) hqQ)
  intro N hnN hNn h1
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnN
  obtain ⟨t, ht, ht0, hts⟩ := hS K ι Ω y D A P0 har hb hA j

  let ψ : chartLat y A.a n →+ chartLat y A.a (n + j) :=
    { toFun := fun s => ⟨(s : Ω) * t, mul_mem_chartLat s.2 ht⟩
      map_zero' := by ext; simp
      map_add' := fun s s' => by ext; simp [add_mul] }
  have hψ : Function.Injective ψ := fun s s' h =>
    Subtype.ext (mul_right_cancel₀ ht0 (congrArg Subtype.val h))
  have hψn : ∀ s, ‖φ (n + j) (ψ s)‖ ≤ ‖φ n s‖ := fun s => hcon n j s ⟨t, ht⟩ (ψ s) hts rfl

  have hclos : AddSubgroup.closure
      {s : chartLat y A.a (n + j) | IsBoundedH (mCoordIdeal y) y A (n + j) C₁ (s : Ω)} = ⊤ := by
    rw [AddSubgroup.eq_top_iff']
    intro x
    have hx : (x : Ω) ∈ AddSubgroup.closure
        {s | s ∈ chartLat y A.a (n + j) ∧ IsBoundedH (mCoordIdeal y) y A (n + j) C s} := by
      rw [hC (n + j)]; exact x.2
    have key : ∀ z (hz : z ∈ AddSubgroup.closure
        {s | s ∈ chartLat y A.a (n + j) ∧ IsBoundedH (mCoordIdeal y) y A (n + j) C s}),
        ∃ hz' : z ∈ chartLat y A.a (n + j), (⟨z, hz'⟩ : chartLat y A.a (n + j)) ∈ AddSubgroup.closure
          {s : chartLat y A.a (n + j) | IsBoundedH (mCoordIdeal y) y A (n + j) C₁ (s : Ω)} := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem z hz => exact ⟨hz.1, AddSubgroup.subset_closure (isBoundedH_mono hz.2 (le_max_left _ _))⟩
      | zero => exact ⟨zero_mem _, zero_mem _⟩
      | add z w _ _ hz hw =>
        obtain ⟨hz', hz''⟩ := hz
        obtain ⟨hw', hw''⟩ := hw
        exact ⟨add_mem hz' hw', add_mem hz'' hw''⟩
      | neg z _ hz =>
        obtain ⟨hz', hz''⟩ := hz
        exact ⟨neg_mem hz', neg_mem hz''⟩
    obtain ⟨_, hx'⟩ := key x hx
    exact hx'
  have hbound : ∀ s ∈ {s : chartLat y A.a (n + j) | IsBoundedH (mCoordIdeal y) y A (n + j) C₁ (s : Ω)},
      ‖φ (n + j) s‖ ≤ C₁ := fun s hs => hsup (n + j) C₁ s (by linarith) hs
  have h2 := hL (chartLat y A.a (n + j)) (chartLat y A.a n) (r (n + j)) (r n) (φ (n + j)) (φ n) ψ _ C₁
    (hinj _) (hinj _) hψ hψn hclos hbound hC₁1
  have h3 : (r (n + j) : ℝ) * Real.log C₁ ≤ Cr * Real.log C₁ * (((n + j : ℕ) : ℝ) + 1) ^ D := by
    have := mul_le_mul_of_nonneg_right (hr (n + j)) hlog
    linarith
  have h4 := hn (n + j) (Nat.le_add_right n j) hNn
  have h5 : I + ε / 2 + ε / 2 = I + ε := by ring
  rw [h5] at h4
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

