import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0064

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryRightDerivConjInvariantAverageEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KAvgDeriv

open MeasureTheory Filter Topology GlobalTheory.KFourier

variable {n : ℕ}

theorem toMK_expK_real {ε : Fin n → Bool} {X : Mx n} (hX : inK ε X) (t : ℝ) :
    toMK (expK ε X t) = NormedSpace.exp (t • X) := by
  rw [toMK_expK hX t, Complex.coe_smul]

theorem toMK_mem_UJ {ε : Fin n → Bool} (k : KG ε) : toMK k ∈ UJset ε := K_le_UJ (toMK_mem_K k)

theorem integral_conj_swap {ε : Fin n → Bool} (e : KG ε → ℂ) (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k)
    (φ : Mx n → ℂ) (g : Mx n) (κ : KG ε) :
    ∫ k, e k * φ (g * toMK κ * toMK k) ∂(muK ε) = ∫ k, e k * φ (g * toMK k * toMK κ) ∂(muK ε) := by
  have h1 := integral_mul_left_eq_self (μ := muK ε) (fun k => e k * φ (g * toMK κ * toMK k)) κ⁻¹
  have h2 := integral_mul_right_eq_self (μ := muK ε) (fun k => e (κ⁻¹ * k) * φ (g * toMK k)) κ
  have ea : ∀ k, g * toMK κ * toMK (κ⁻¹ * k) = g * toMK k := fun k => by
    rw [mul_assoc, ← toMK_mul, mul_inv_cancel_left]
  have eb : ∀ k, e (κ⁻¹ * (k * κ)) = e k := fun k => by
    have := he κ⁻¹ k
    rwa [inv_inv, mul_assoc] at this
  calc ∫ k, e k * φ (g * toMK κ * toMK k) ∂(muK ε)
      = ∫ k, e (κ⁻¹ * k) * φ (g * toMK κ * toMK (κ⁻¹ * k)) ∂(muK ε) := h1.symm
    _ = ∫ k, e (κ⁻¹ * k) * φ (g * toMK k) ∂(muK ε) := by simp only [ea]
    _ = ∫ k, e (κ⁻¹ * (k * κ)) * φ (g * toMK (k * κ)) ∂(muK ε) := h2.symm
    _ = _ := by simp only [eb, toMK_mul, mul_assoc]

variable {ε : Fin n → Bool} {F : List (Mx n) → Mx n → ℂ}

theorem measurable_fam (hD : IsDerFam ε F) {f : Mx n → ℂ} (hf : ContinuousOn f (UJset ε))
    (hF0 : ∀ g ∈ UJset ε, F [] g = f g) :
    ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ a ∈ UJset ε, ∀ b ∈ UJset ε,
      Measurable fun k : KG ε => F l (a * toMK k * b) := by
  intro l
  induction l with
  | nil =>
    intro _ a ha b hb
    have hm : ∀ k : KG ε, a * toMK k * b ∈ UJset ε := fun k => mul_mem_UJ (mul_mem_UJ ha (toMK_mem_UJ k)) hb
    have e1 : (fun k : KG ε => F [] (a * toMK k * b)) = fun k => f (a * toMK k * b) :=
      funext fun k => hF0 _ (hm k)
    rw [e1]
    exact (hf.comp_continuous ((continuous_const.mul (continuous_toMK ε)).mul continuous_const) hm).measurable
  | cons X l ih =>
    intro hl a ha b hb
    have hX : X ∈ lieSet ε := hl X List.mem_cons_self
    have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
    let s : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
    have hs0 : Tendsto s atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun m => by simp only [Set.mem_compl_iff, Set.mem_singleton_iff, s]; positivity⟩
    have hmeas : ∀ m : ℕ, Measurable fun k : KG ε =>
        (s m)⁻¹ • (F l (a * toMK k * (b * NormedSpace.exp (s m • X))) - F l (a * toMK k * b)) := fun m => by
      have := ((ih hl' a ha _ (mul_mem_UJ hb (exp_mem_UJ hX (s m)))).sub (ih hl' a ha b hb)).const_smul (s m)⁻¹
      exact this
    refine measurable_of_tendsto_metrizable hmeas (tendsto_pi_nhds.2 fun k => ?_)
    have hg : a * toMK k * b ∈ UJset ε := mul_mem_UJ (mul_mem_UJ ha (toMK_mem_UJ k)) hb
    have hd := (hasDerivAt_iff_tendsto_slope.1 (hD l hl' X hX _ hg)).comp hs0
    refine hd.congr fun m => ?_
    simp only [Function.comp_apply, slope_def_module, sub_zero, zero_smul, NormedSpace.exp_zero, mul_one,
      mul_assoc]

theorem hasDerivAt_avg (hD : IsDerFam ε F) {N : ℕ} (hG : FamGrowth ε N F) {f : Mx n → ℂ}
    (hf : ContinuousOn f (UJset ε)) (hF0 : ∀ g ∈ UJset ε, F [] g = f g) {e : KG ε → ℂ} (hec : Continuous e)
    (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k) {l : List (Mx n)} (hl : ∀ Y ∈ l, Y ∈ lieSet ε) {X : Mx n}
    (hX : inK ε X) {g : Mx n} (hg : g ∈ UJset ε) :
    HasDerivAt (fun t : ℝ => ∫ k, e k * F l (g * toMK (expK ε X t) * toMK k) ∂(muK ε))
      (∫ k, e k * F (X :: l) (g * toMK k) ∂(muK ε)) 0 := by
  have hXl : X ∈ lieSet ε := hX.1
  have hl' : ∀ Y ∈ X :: l, Y ∈ lieSet ε := by
    intro Y hY
    rcases List.mem_cons.1 hY with rfl | h
    exacts [hXl, hl Y h]
  have hre : (fun t : ℝ => ∫ k, e k * F l (g * toMK (expK ε X t) * toMK k) ∂(muK ε)) =
      fun t => ∫ k, e k * F l (g * toMK k * NormedSpace.exp (t • X)) ∂(muK ε) := by
    funext t
    rw [integral_conj_swap e he, toMK_expK_real hX]
  rw [hre]
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hec.continuousOn
  obtain ⟨C, hC⟩ := hG (X :: l) hl'
  obtain ⟨C0, hC0⟩ := hG l hl
  have hmem : ∀ (k : KG ε) (s : ℝ), g * toMK k * NormedSpace.exp (s • X) ∈ UJset ε := fun k s =>
    mul_mem_UJ (mul_mem_UJ hg (toMK_mem_UJ k)) (exp_mem_UJ hXl s)
  have hhs : ∀ (k : KG ε) (s : ℝ), hs (g * toMK k * NormedSpace.exp (s • X)) = hs g := fun k s => by
    rw [← toMK_expK_real hX, mul_assoc, ← toMK_mul]
    exact ((hermitian_small_ball n ε).2 _ _ (toMK_mem_K _)).1
  have hem : Measurable e := hec.measurable
  have hbd : ∀ (l' : List (Mx n)) (C' : ℝ), (∀ h ∈ UJset ε, ‖F l' h‖ ≤ C' * (1 + hs h) ^ N) →
      ∀ (k : KG ε) (s : ℝ), ‖e k * F l' (g * toMK k * NormedSpace.exp (s • X))‖ ≤ M * (C' * (1 + hs g) ^ N) :=
    fun l' C' hC' k s => by
      rw [norm_mul]
      refine mul_le_mul (hM k trivial) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hM k trivial))
      rw [← hhs k s]
      exact hC' _ (hmem k s)
  have hmeasF : ∀ t : ℝ, AEStronglyMeasurable (fun k => e k * F l (g * toMK k * NormedSpace.exp (t • X))) (muK ε) :=
    fun t => (hem.mul (measurable_fam hD hf hF0 l hl g hg _ (exp_mem_UJ hXl t))).aestronglyMeasurable
  have hmeasF' : AEStronglyMeasurable (fun k => e k * F (X :: l) (g * toMK k * NormedSpace.exp ((0 : ℝ) • X)))
      (muK ε) := (hem.mul (measurable_fam hD hf hF0 (X :: l) hl' g hg _ (exp_mem_UJ hXl 0))).aestronglyMeasurable
  have hint : Integrable (fun k => e k * F l (g * toMK k * NormedSpace.exp ((0 : ℝ) • X))) (muK ε) :=
    Integrable.mono' (integrable_const (M * (C0 * (1 + hs g) ^ N))) (hmeasF 0) (ae_of_all _ fun k => hbd l C0 hC0 k 0)
  have hdif : ∀ (k : KG ε) (s : ℝ), HasDerivAt (fun t : ℝ => e k * F l (g * toMK k * NormedSpace.exp (t • X)))
      (e k * F (X :: l) (g * toMK k * NormedSpace.exp (s • X))) s := fun k s => by
    have h1 := hD l hl X hXl _ (hmem k s)
    have h2 : HasDerivAt (fun t : ℝ => F l (g * toMK k * NormedSpace.exp (s • X) * NormedSpace.exp ((t - s) • X)))
        (F (X :: l) (g * toMK k * NormedSpace.exp (s • X))) s :=
      HasDerivAt.comp_sub_const (f := fun t : ℝ => F l (g * toMK k * NormedSpace.exp (s • X) * NormedSpace.exp (t • X)))
        s s (by rw [sub_self]; exact h1)
    have e2 : (fun t : ℝ => F l (g * toMK k * NormedSpace.exp (s • X) * NormedSpace.exp ((t - s) • X))) =
        fun t => F l (g * toMK k * NormedSpace.exp (t • X)) := by
      funext t
      rw [mul_assoc (g * toMK k), ← exp_add_smul, add_sub_cancel]
    rw [e2] at h2
    exact h2.const_mul (e k)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muK ε) (x₀ := (0 : ℝ))
    (F := fun t k => e k * F l (g * toMK k * NormedSpace.exp (t • X)))
    (F' := fun t k => e k * F (X :: l) (g * toMK k * NormedSpace.exp (t • X)))
    (bound := fun _ => M * (C * (1 + hs g) ^ N)) (s := Set.univ) Filter.univ_mem (Eventually.of_forall hmeasF) hint hmeasF'
    (ae_of_all _ fun k t _ => hbd (X :: l) C hC k t) (integrable_const _) (ae_of_all _ fun k s _ => hdif k s)
  have e3 : (fun k => e k * F (X :: l) (g * toMK k * NormedSpace.exp ((0 : ℝ) • X))) =
      fun k => e k * F (X :: l) (g * toMK k) := by
    funext k
    rw [zero_smul, NormedSpace.exp_zero, mul_one]
  simpa only [e3] using key.2

theorem rder_avgK_all (hD : IsDerFam ε F) {N : ℕ} (hG : FamGrowth ε N F) {f : Mx n → ℂ}
    (hf : ContinuousOn f (UJset ε)) (hF0 : ∀ g ∈ UJset ε, F [] g = f g) {e : KG ε → ℂ} (hec : Continuous e)
    (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k) {y : Mx n} (hy : y ∈ UJset ε) :
    ∀ u : List (Mx n), (∀ X ∈ u, inK ε X) → ∀ k' : KG ε,
      rder ε u (avgK ε e f y) k' = ∫ k, e k * F u (y * toMK k' * toMK k) ∂(muK ε) := by
  intro u
  induction u with
  | nil =>
    intro _ k'
    rw [rder_nil]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    simp only
    rw [hF0 _ (mul_mem_UJ (mul_mem_UJ hy (toMK_mem_UJ k')) (toMK_mem_UJ k))]
  | cons X l ih =>
    intro hu k'
    have hX : inK ε X := hu X List.mem_cons_self
    have hlK : ∀ Y ∈ l, inK ε Y := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    have hl : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => (hlK Y hY).1
    rw [rder_cons]
    have e1 : (fun t : ℝ => rder ε l (avgK ε e f y) (k' * expK ε X t)) =
        fun t => ∫ k, e k * F l (y * toMK k' * toMK (expK ε X t) * toMK k) ∂(muK ε) := by
      funext t
      rw [ih hlK, toMK_mul, mul_assoc y]
    rw [e1]
    exact (hasDerivAt_avg hD hG hf hF0 hec he hl hX (mul_mem_UJ hy (toMK_mem_UJ k'))).deriv

theorem rder_avgK_one (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ) (hD : IsDerFam ε F)
    (hG : FamGrowth ε N F) (f : Mx n → ℂ) (hf : ContinuousOn f (UJset ε)) (hF0 : ∀ g ∈ UJset ε, F [] g = f g)
    (e : KG ε → ℂ) (hec : Continuous e) (he : ∀ a k : KG ε, e (a * k * a⁻¹) = e k) (u : List (Mx n))
    (hu : ∀ X ∈ u, inK ε X) (y : Mx n) (hy : y ∈ UJset ε) :
    GlobalTheory.KFourier.rder ε u (GlobalTheory.KFourier.avgK ε e f y) 1 = ∫ k, e k * F u (y * toMK k) ∂(muK ε) := by
  rw [rder_avgK_all hD hG hf hF0 hec he hy u hu 1, toMK_one, mul_one]

end GlobalTheory.KAvgDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContDiffMatrixRightInvariantDerivative
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open Matrix

variable {n : ℕ}

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_exp_entry_real (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  have h2 : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)) i j) (X i j) 0 :=
    L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) = fun t : ℝ => (NormedSpace.exp (t • X)) i j := by
    funext t; rw [Complex.coe_smul]
  rw [e]; exact h2

theorem coord_mul_expK_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (c : Fin n × Fin n × Bool) (k : KG ε) : coord ε c (k * expK ε X 0) = coord ε c k := by
  simp [coord, toMK_mul, toMK_expK hX, NormedSpace.exp_zero]

theorem mono_mul_expK_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (s : List (Fin n × Fin n × Bool)) (k : KG ε) : mono ε s (k * expK ε X 0) = mono ε s k := by
  simp only [mono, coord_mul_expK_zero hX]

theorem hasDerivAt_coord {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (c : Fin n × Fin n × Bool) : ∃ ψ ∈ polyV ε 1, ∀ k : KG ε,
      HasDerivAt (fun t : ℝ => coord ε c (k * expK ε X t)) (ψ k) 0 := by
  obtain ⟨a, b, f⟩ := c
  have hent : ∀ k : KG ε, HasDerivAt (fun t : ℝ => (toMK (k * expK ε X t)) a b)
      (∑ l, toMK k a l * X l b) 0 := by
    intro k
    have e : (fun t : ℝ => (toMK (k * expK ε X t)) a b) =
        fun t : ℝ => ∑ l, toMK k a l * (NormedSpace.exp ((t : ℂ) • X)) l b := by
      funext t; simp only [toMK_mul, toMK_expK hX, Matrix.mul_apply]
    rw [e]
    exact HasDerivAt.fun_sum fun l _ => (hasDerivAt_exp_entry_real X l b).const_mul _
  cases f
  · refine ⟨∑ l, star (X l b) • coord ε (a, l, false), ?_, fun k => ?_⟩
    · exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (coord_mem ε _)
    · have h := (hent k).star
      have e1 : (fun t : ℝ => coord ε (a, b, false) (k * expK ε X t)) =
          fun t => star ((toMK (k * expK ε X t)) a b) := by
        funext t; simp [coord]
      rw [e1]
      have hv : (∑ l, star (X l b) • coord ε (a, l, false)) k = star (∑ l, toMK k a l * X l b) := by
        rw [Finset.sum_apply, star_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, coord, Bool.false_eq_true, if_false, star_mul']
        exact mul_comm _ _
      rw [hv]; exact h
  · refine ⟨∑ l, X l b • coord ε (a, l, true), ?_, fun k => ?_⟩
    · exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (coord_mem ε _)
    · have e1 : (fun t : ℝ => coord ε (a, b, true) (k * expK ε X t)) =
          fun t => (toMK (k * expK ε X t)) a b := by
        funext t; simp [coord]
      rw [e1]
      have hv : (∑ l, X l b • coord ε (a, l, true)) k = ∑ l, toMK k a l * X l b := by
        rw [Finset.sum_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, coord, if_true]
        exact mul_comm _ _
      rw [hv]; exact hent k

theorem hasDerivAt_mono {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (s : List (Fin n × Fin n × Bool)) : ∀ d, s.length ≤ d → ∃ ψ ∈ polyV ε d, ∀ k : KG ε,
      HasDerivAt (fun t : ℝ => mono ε s (k * expK ε X t)) (ψ k) 0 := by
  induction s with
  | nil =>
    intro d _
    refine ⟨0, Submodule.zero_mem _, fun k => ?_⟩
    simpa [mono] using hasDerivAt_const (0 : ℝ) (1 : ℂ)
  | cons c s ih =>
    intro d hd
    simp only [List.length_cons] at hd
    obtain ⟨ψc, hψc, hc⟩ := hasDerivAt_coord hX c
    obtain ⟨ψs, hψs, hs⟩ := ih (d - 1) (by omega)
    refine ⟨ψc * mono ε s + coord ε c * ψs, ?_, fun k => ?_⟩
    · have hle : 1 + (d - 1) ≤ d := by omega
      exact add_mem (polyV_mono ε hle (mul_mem hψc (mono_mem (by omega))))
        (polyV_mono ε hle (mul_mem (coord_mem ε c) hψs))
    · have h := (hc k).mul (hs k)
      have e : (fun t : ℝ => mono ε (c :: s) (k * expK ε X t)) =
          fun t => coord ε c (k * expK ε X t) * mono ε s (k * expK ε X t) := by
        funext t; simp [mono]
      rw [e]
      rw [coord_mul_expK_zero hX, mono_mul_expK_zero hX] at h
      exact h

theorem hasDerivAt_of_mem {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) {d : ℕ}
    {φ : KG ε → ℂ} (hφ : φ ∈ polyV ε d) : ∃ ψ ∈ polyV ε d, ∀ k : KG ε,
      HasDerivAt (fun t : ℝ => φ (k * expK ε X t)) (ψ k) 0 := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact hasDerivAt_mono hX s d hs
  | zero =>
    exact ⟨0, Submodule.zero_mem _, fun k => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add x y _ _ hx hy =>
    obtain ⟨ψ₁, h₁, d₁⟩ := hx
    obtain ⟨ψ₂, h₂, d₂⟩ := hy
    exact ⟨ψ₁ + ψ₂, add_mem h₁ h₂, fun k => (d₁ k).add (d₂ k)⟩
  | smul a x _ hx =>
    obtain ⟨ψ, h, dψ⟩ := hx
    exact ⟨a • ψ, Submodule.smul_mem _ a h, fun k => by simpa using (dψ k).const_mul a⟩

theorem rder_mem_and_hasDerivAt (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ) (hφ : φ ∈ polyV ε d)
    (X : Mx n) (hX : inK ε X) : rder ε [X] φ ∈ polyV ε d ∧
      ∀ k : KG ε, HasDerivAt (fun t : ℝ => φ (k * expK ε X t)) (rder ε [X] φ k) 0 := by
  obtain ⟨ψ, hψ, hd⟩ := hasDerivAt_of_mem hX hφ
  have e : rder ε [X] φ = ψ := by
    funext k
    rw [rder_cons, rder_nil]
    exact (hd k).deriv
  rw [e]
  exact ⟨hψ, hd⟩

end GlobalTheory.KFourier

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.EqZeroOfOrthogonalCompactUnitaryPolyFun
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory Matrix Formalism.REAL

variable {n : ℕ}

def polyAlg (ε : Fin n → Bool) : StarSubalgebra ℂ C(KG ε, ℂ) where
  carrier := {f | ∃ d, ⇑f ∈ polyV ε d}
  mul_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by simpa using mul_mem ha hb⟩
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨max a b, by simpa using add_mem (polyV_mono ε (le_max_left a b) ha) (polyV_mono ε (le_max_right a b) hb)⟩
  algebraMap_mem' := by
    intro c
    refine ⟨0, ?_⟩
    convert const_mem ε 0 c using 1
    funext k; simp [Algebra.algebraMap_eq_smul_one]
  star_mem' := by
    rintro f ⟨a, ha⟩
    refine ⟨a, ?_⟩
    convert star_mem ha using 1
    funext k; rfl

theorem toMK_injective (ε : Fin n → Bool) : Function.Injective (fun k : KG ε => toMK k) := by
  intro a b h
  have h1 : ((a : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) = ((b : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) := Units.ext h
  exact Subtype.ext (Subtype.ext h1)

theorem polyAlg_separatesPoints (ε : Fin n → Bool) : (polyAlg ε).SeparatesPoints := by
  intro x y hxy
  have hne : toMK x ≠ toMK y := fun h => hxy (toMK_injective ε h)
  obtain ⟨i, j, hij⟩ : ∃ i j, toMK x i j ≠ toMK y i j := by
    by_contra hc
    push_neg at hc
    exact hne (Matrix.ext hc)
  refine ⟨_, ⟨⟨coord ε (i, j, true), continuous_coord ε _⟩, ⟨1, show coord ε (i, j, true) ∈ polyV ε 1 from coord_mem ε _⟩, rfl⟩, ?_⟩
  simpa [coord] using hij

theorem polyAlg_dense (ε : Fin n → Bool) : (polyAlg ε).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ (polyAlg_separatesPoints ε)

theorem integrable_cont (ε : Fin n → Bool) (F : C(KG ε, ℂ)) : Integrable F (muK ε) :=
  F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem continuous_integral_cont (ε : Fin n → Bool) :
    Continuous fun F : C(KG ε, ℂ) => ∫ k, F k ∂(muK ε) := by
  refine (LipschitzWith.of_dist_le_mul fun F G => ?_).continuous (K := 1)
  rw [dist_eq_norm, ← integral_sub (integrable_cont ε F) (integrable_cont ε G)]
  have h := norm_integral_le_of_norm_le_const (μ := muK ε) (C := ‖F - G‖)
    (Filter.Eventually.of_forall fun k => by
      simpa using ContinuousMap.norm_coe_le_norm (F - G) k)
  simpa [probReal_univ, dist_eq_norm] using h

theorem eq_zero_of_orth_poly : ∀ {n : ℕ} (ε : Fin n → Bool) (h : KG ε → ℂ), Continuous h → (∀ d, ∀ q ∈ GlobalTheory.KFourier.polyV ε d, ∫ k, star (q k) * h k ∂(muK ε) = 0) → h = 0 := by
  intro n ε h hc horth
  let H : C(KG ε, ℂ) := ⟨h, hc⟩
  let Φ : C(KG ε, ℂ) → ℂ := fun F => ∫ k, star (F k) * h k ∂(muK ε)
  have hΦ : Continuous Φ := by
    have : Continuous fun F : C(KG ε, ℂ) => star F * H := (continuous_star).mul continuous_const
    exact (continuous_integral_cont ε).comp this
  have hclosed : IsClosed {F : C(KG ε, ℂ) | Φ F = 0} := isClosed_eq hΦ continuous_const
  have hsub : ((polyAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) ⊆ {F | Φ F = 0} := by
    rintro F ⟨d, hd⟩
    exact horth d _ hd
  have hcl : closure ((polyAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) = Set.univ := by
    have := polyAlg_dense ε
    rw [← StarSubalgebra.topologicalClosure_coe, this]
    rfl
  have hH : Φ H = 0 := by
    have : H ∈ closure ((polyAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) := by rw [hcl]; trivial
    exact hclosed.closure_subset_iff.mpr hsub this

  have hint : ∫ k, (Complex.normSq (h k) : ℂ) ∂(muK ε) = 0 := by
    have e : (fun k => (Complex.normSq (h k) : ℂ)) = fun k => star (h k) * h k := by
      funext k; rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [e]; exact hH
  have hint' : ∫ k, Complex.normSq (h k) ∂(muK ε) = 0 := by
    rw [integral_complex_ofReal] at hint
    exact_mod_cast hint
  have hnn : 0 ≤ᵐ[muK ε] fun k => Complex.normSq (h k) := Filter.Eventually.of_forall fun k => Complex.normSq_nonneg _
  have hcn : Continuous fun k => Complex.normSq (h k) := Complex.continuous_normSq.comp hc
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn
    (hcn.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp hint'
  have hz : (fun k => Complex.normSq (h k)) = fun _ => 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) hcn continuous_const).mp hae
  funext k
  have := congrFun hz k
  simpa using this

end GlobalTheory.KFourier

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsMapsOfRelationsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maps_of_relations_alt : GlobalTheory.Published.HarishChandraModules → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (d : ℕ) (w : Fin d → H), (∀ a, IsKFin ε σ (w a)) →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (τ : Ltr ε → Module.End ℂ M) (m₀ : M),
    (∀ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), (∀ a, ∑ i, c i • wordV σ (u i) (w a) = 0) →
      ∑ i, c i • wordE τ (u i) m₀ = 0) →
    ∃ T : Fin d → (H →ₗ[ℂ] M), (∀ a v, IsKFin ε σ v → ∀ x, T a (ltrV σ x v) = τ x (T a v)) ∧ ∑ a, T a (w a) = m₀ ∧
      ∀ a v, IsKFin ε σ v → ∃ (m : ℕ) (c : Fin m → ℂ) (u : Fin m → List (Ltr ε)), T a v = ∑ i, c i • wordE τ (u i) m₀ := by
  first | exact @GlobalTheory.TypeSum.CoefClos.exists_maps_of_relations | exact GlobalTheory.TypeSum.CoefClos.exists_maps_of_relations | (intros; apply GlobalTheory.TypeSum.CoefClos.exists_maps_of_relations <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSobolevContinuousFormOfModerateGrowthMapStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sobolevContinuous_form_of_moderateGrowthMap : GlobalTheory.Published.CasselmanWallach → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ →
    ∀ (N : ℕ) (T : H →ₗ[ℂ] (Mx n → ℂ)),
    (∀ v, IsKFin ε σ v → ∃ C : ℝ, ∀ g ∈ UJset ε, ‖T v g‖ ≤ C * (1 + Formalism.REAL.hs g) ^ N) →
    (∀ v, IsKFin ε σ v → ∀ k ∈ Kset ε, ∀ g ∈ UJset ε, T (σ k v) g = T v (g * k)) →
    (∀ v, IsKFin ε σ v → ∀ X ∈ lieSet ε, ∀ g ∈ UJset ε,
      HasDerivAt (fun t : ℝ => T v (g * NormedSpace.exp (t • X))) (T (dRep σ X v) g) 0) →
    ∃ L : H →ₗ[ℂ] ℂ, Sobolev₂ (lieSet ε) σ L ∧ ∀ v, IsKFin ε σ v → ∀ y ∈ UJset ε, T v y = L (σ y v) := by
  first | exact @GlobalTheory.TypeSum.GrowthForm.exists_form | exact GlobalTheory.TypeSum.GrowthForm.exists_form | (intros; apply GlobalTheory.TypeSum.GrowthForm.exists_form <;> assumption)
end

