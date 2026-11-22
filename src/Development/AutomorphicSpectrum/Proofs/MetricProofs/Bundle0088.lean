import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0062
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0013
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0081
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0029
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0007
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumAndCuspWeightBounds

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartSectionNotMemComponents
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
open ReciprocityTheory.AnForm.R (conePts)
open GroundTheory.Heights₂.Heights (chartLift chartLift_segre_apply)

namespace SecNotIn

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def chartMono (i : (k : K) → ι k) : MRingOver ℂ ι := ∏ k, X ⟨k, i k⟩

theorem eval_chartMono (i : (k : K) → ι k) (x : (Σ k, ι k) → ℂ) : eval x (chartMono i) = segre x i := by
  simp [chartMono, segre]

theorem eval_scale_eq_zero {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q)
    (c : K → ℂ) {x : (Σ k, ι k) → ℂ} (hx : ∀ f ∈ Q, eval x f = 0) :
    ∀ f ∈ Q, eval (fun q => c q.1 * x q) f = 0 := by
  obtain ⟨S, hS, rfl⟩ := hQ
  have hle : Ideal.span S ≤ RingHom.ker (eval (fun q : Σ k, ι k => c q.1 * x q)) := by
    rw [Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    have h := ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog ha c x
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have h' : eval (fun q : Σ k, ι k => c q.1 * x q) f = (∏ k, c k ^ a k) * eval x f := h
    rw [h', hx f (Ideal.subset_span hf), mul_zero]
  exact fun f hf => hle hf

theorem mem_of_eval_eq_zero {Q : Ideal (MRingOver ℂ ι)} (hQp : Q.IsPrime) {i : (k : K) → ι k}
    (hw : chartMono i ∉ Q) {g : MRingOver ℂ ι}
    (h : ∀ x : (Σ k, ι k) → ℂ, (∀ f ∈ Q, eval x f = 0) → segre x i ≠ 0 → eval x g = 0) : g ∈ Q := by
  have hrad : g * chartMono i ∈ Q.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), mem_vanishingIdeal_iff]
    intro x hx
    have hae : ∀ p : MvPolynomial (Σ k, ι k) ℂ, aeval x p = eval x p := fun _ => rfl
    rw [hae, map_mul, eval_chartMono]
    by_cases h0 : segre x i = 0
    · rw [h0, mul_zero]
    · rw [h x (fun f hf => by have := hx f hf; rwa [hae] at this) h0, zero_mul]
  rw [hQp.radical] at hrad
  exact (hQp.mem_or_mem hrad).resolve_right hw

def normAt (i : (k : K) → ι k) (x : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => (x ⟨q.1, i q.1⟩)⁻¹ * x q

theorem entry_ne_zero {i : (k : K) → ι k} {x : (Σ k, ι k) → ℂ} (h : segre x i ≠ 0) (k : K) :
    x ⟨k, i k⟩ ≠ 0 := fun h0 => h (Finset.prod_eq_zero (Finset.mem_univ k) h0)

theorem segre_normAt (i i' : (k : K) → ι k) (x : (Σ k, ι k) → ℂ) :
    segre (normAt i x) i' = segre x i' / segre x i := by
  simp only [segre, normAt, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rw [div_eq_mul_inv, mul_comm]

theorem normAt_mem {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q)
    {i : (k : K) → ι k} {x : (Σ k, ι k) → ℂ} (hx : ∀ f ∈ Q, eval x f = 0) (h : segre x i ≠ 0) :
    normAt i x ∈ conePts Q :=
  ⟨fun k => ⟨i k, mul_ne_zero (inv_ne_zero (entry_ne_zero h k)) (entry_ne_zero h k)⟩,
    eval_scale_eq_zero hQ (fun k => (x ⟨k, i k⟩)⁻¹) hx⟩

theorem normAt_mem_chartSet {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q)
    {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) {i : (k : K) → ι k} {x : (Σ k, ι k) → ℂ}
    (hx : ∀ f ∈ Q, eval x f = 0) (h : segre x i ≠ 0) :
    (fun a => segre x (σ a) / segre x i) ∈ chartSet (conePts Q) σ i :=
  ⟨normAt i x, normAt_mem hQ hx h, by rw [segre_normAt, div_self h],
    funext fun a => (segre_normAt i (σ a) x).symm⟩

theorem exists_homogenise {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (f : MvPolynomial (Fin m) ℂ) :
    ∃ (F : MRingOver ℂ ι) (D : ℕ), ∀ x : (Σ k, ι k) → ℂ, segre x i ≠ 0 →
      eval x F = segre x i ^ D * eval (fun a => segre x (σ a) / segre x i) f := by
  induction f using MvPolynomial.induction_on with
  | C c => exact ⟨C c, 0, fun x _ => by simp⟩
  | add f g hf hg =>
    obtain ⟨F, D, hF⟩ := hf
    obtain ⟨G, E, hG⟩ := hg
    refine ⟨F * chartMono i ^ E + G * chartMono i ^ D, D + E, fun x hx => ?_⟩
    simp only [map_add, map_mul, map_pow, eval_chartMono, hF x hx, hG x hx]
    ring
  | mul_X f a hf =>
    obtain ⟨F, D, hF⟩ := hf
    refine ⟨F * chartMono (σ a), D + 1, fun x hx => ?_⟩
    simp only [map_mul, eval_chartMono, hF x hx, eval_X]
    field_simp
    ring

theorem chartIdeal_isPrime {Q : Ideal (MRingOver ℂ ι)} (hQp : Q.IsPrime)
    (hQh : IsMultiHomogIdeal Q) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    {i : (k : K) → ι k} (hw : chartMono i ∉ Q) (hne : chartIdeal (conePts Q) σ i ≠ ⊤) :
    (chartIdeal (conePts Q) σ i).IsPrime := by
  have back : ∀ (f : MvPolynomial (Fin m) ℂ) (F : MRingOver ℂ ι) (D : ℕ),
      (∀ x : (Σ k, ι k) → ℂ, segre x i ≠ 0 →
        eval x F = segre x i ^ D * eval (fun a => segre x (σ a) / segre x i) f) →
      F ∈ Q → f ∈ chartIdeal (conePts Q) σ i := by
    intro f F D hF hFQ
    rw [chartIdeal, mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have h0 : segre z i ≠ 0 := by rw [hz1]; exact one_ne_zero
    have h := hF z h0
    rw [hz.2 F hFQ, hz1] at h
    simpa using h.symm
  refine ⟨hne, fun {f g} hfg => ?_⟩
  obtain ⟨F, D, hF⟩ := exists_homogenise σ i f
  obtain ⟨G, E, hG⟩ := exists_homogenise σ i g
  have hFG : F * G ∈ Q := mem_of_eval_eq_zero hQp hw fun x hx h0 => by
    have h1 : eval (fun a => segre x (σ a) / segre x i) (f * g) = 0 :=
      (mem_vanishingIdeal_iff.1 hfg) _ (normAt_mem_chartSet hQh σ hx h0)
    rw [map_mul] at h1
    rw [map_mul, hF x h0, hG x h0]
    linear_combination (segre x i ^ D * segre x i ^ E) * h1
  rcases hQp.mem_or_mem hFG with h | h
  · exact Or.inl (back f F D hF h)
  · exact Or.inr (back g G E hG h)

theorem eval_chartSection [DecidableEq K] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (x : Fin m → ℂ) (s : MRingOver ℂ ι) : eval x (chartSection σ i s) = eval (chartLift σ i x) s := by
  induction s using MvPolynomial.induction_on with
  | C c => simp [chartSection]
  | add f g hf hg =>
    simp only [chartSection, map_add] at hf hg ⊢
    rw [hf, hg]
  | mul_X f q hf =>
    simp only [chartSection, map_mul, aeval_X, eval_X] at hf ⊢
    rw [hf]
    rfl

end SecNotIn

open SecNotIn in

theorem chartSection_notMem_component : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsMultiHomog s a → s ∉ Q →
    ∀ J ∈ chartComponents (conePts Q) σ i, chartSection σ i s ∉ J := by
  intro K _ _ ι _ Q e m σ i s a hQ hs hsQ J hJ hmem
  obtain ⟨-, ⟨hQp, hQh, -⟩, -⟩ := hQ
  have hJmin := mem_chartComponents.1 hJ
  have hprimeJ : J.IsPrime := hJmin.1.1
  have hne : chartIdeal (conePts Q) σ i ≠ ⊤ := fun h =>
    hprimeJ.ne_top (top_le_iff.1 (h ▸ hJmin.1.2))
  have hw : chartMono i ∉ Q := by
    intro hwQ
    apply hne
    rw [Ideal.eq_top_iff_one, chartIdeal, mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have h0 := hz.2 _ hwQ
    rw [eval_chartMono, hz1] at h0
    exact absurd h0 one_ne_zero
  have hprime := chartIdeal_isPrime hQp hQh σ hw hne
  have hJI : J ≤ chartIdeal (conePts Q) σ i := hJmin.2 ⟨hprime, le_rfl⟩ hJmin.1.2
  have hI := hJI hmem
  apply hsQ
  refine mem_of_eval_eq_zero hQp hw fun x hx h0 => ?_
  have hz1 : segre (normAt i x) i = 1 := by rw [segre_normAt, div_self h0]
  have hpt : (fun a => segre (normAt i x) (σ a)) ∈ chartSet (conePts Q) σ i :=
    ⟨normAt i x, normAt_mem hQh hx h0, hz1, rfl⟩
  have h1 : eval (fun a => segre (normAt i x) (σ a)) (chartSection σ i s) = 0 :=
    (mem_vanishingIdeal_iff.1 hI) _ hpt
  have hlift : chartLift σ i (fun a => segre (normAt i x) (σ a)) = normAt i x := by
    funext ⟨k, j⟩
    rw [chartLift_segre_apply σ i _ hz1]
    have : normAt i x ⟨k, i k⟩ = 1 := inv_mul_cancel₀ (entry_ne_zero h0 k)
    rw [this, inv_one, mul_one]
  rw [eval_chartSection, hlift] at h1
  have hsc : eval (normAt i x) s = (∏ k, ((x ⟨k, i k⟩)⁻¹) ^ a k) * eval x s :=
    ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog (fun d hd k => hs d hd k)
      (fun k => (x ⟨k, i k⟩)⁻¹) x
  rw [hsc] at h1
  refine (mul_eq_zero.1 h1).resolve_left ?_
  exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (entry_ne_zero h0 k))

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartWSaturatedAndContinuousSection
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.NoMonodromy

variable {a g : ℕ}

theorem map_mulVec_real (M : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    M.map (fun x : ℤ => (x : ℝ)) *ᵥ (fun k => (v k : ℝ)) = fun k => ((M *ᵥ v) k : ℝ) := by
  funext k
  simp [mulVec, dotProduct]

theorem ker_each (B : Fin a → Matrix (Fin g) (Fin g) ℤ)
    (hB : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℤ)
    (hv : (∑ j, B j) *ᵥ v = 0) (j : Fin a) : B j *ᵥ v = 0 := by
  set r : Fin g → ℝ := fun k => (v k : ℝ) with hr
  have hsum : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℝ)) := by
    ext p q
    simp [Matrix.sum_apply]
  have h1 : (∑ j, (B j).map (fun x : ℤ => (x : ℝ))) *ᵥ r = 0 := by
    rw [← hsum, hr, map_mulVec_real, hv]
    funext k
    simp
  have h0 : r ⬝ᵥ ((∑ j, (B j).map (fun x : ℤ => (x : ℝ))) *ᵥ r) = 0 := by
    rw [h1]; simp
  rw [Matrix.sum_mulVec, dotProduct_sum] at h0
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ r ⬝ᵥ ((B i).map (fun x : ℤ => (x : ℝ)) *ᵥ r) := by
    intro i _
    simpa using (hB i).dotProduct_mulVec_nonneg r
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 j (Finset.mem_univ j)
  have h3 : (B j).map (fun x : ℤ => (x : ℝ)) *ᵥ r = 0 :=
    ((hB j).dotProduct_mulVec_zero_iff r).1 (by simpa using h2)
  rw [hr, map_mulVec_real] at h3
  funext k
  have := congrFun h3 k
  simpa using this

theorem vec_eq_sum (t : Fin g → ℂ) : t = ∑ i, t i • cst (Pi.single i 1 : Fin g → ℤ) := by
  funext k
  simp [cst, Finset.sum_apply, Pi.single_apply]

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.NoMonodromy

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

open NoMonodromy

theorem noMonodromy_lattice : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ), IsChart L bas A T0 B c ρ → (∀ (x : Λ) (k : ℤ), k ≠ 0 → k • x ∈ chartW bas B → x ∈ chartW bas B) ∧ (∀ x ∈ chartW bas B, ContinuousAt (chartS bas A T0 x) 0 ∧ ∀ w ∈ logCover L.a_le, chartS bas A T0 x (expCover a w) = L.P w x) ∧ Function.Injective (chartPer bas A T0 B) ∧ Submodule.span ℂ (Set.range (chartPer bas A T0 B)) = ⊤ := by
  intro n a g Λ _ L bas A T0 B c ρ h
  have hmem : ∀ x, x ∈ chartW bas B ↔ (∑ j, B j) *ᵥ vCo bas x = 0 := fun x => by
    rw [chartW, LinearMap.mem_ker]
    rfl
  have h0ball : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hA0 : ContinuousAt A 0 := h.A_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0ball)
  have hT0 : ContinuousAt T0 0 := h.T_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0ball)
  have hunit : IsUnit ((A 0)ᵀ).det := Ne.isUnit (by rw [det_transpose]; exact h.A_det)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x k hk hx
    rw [hmem] at hx ⊢
    rw [map_zsmul, Matrix.mulVec_smul] at hx
    exact (smul_eq_zero.1 hx).resolve_left hk
  · intro x hx
    have hxv := (hmem x).1 hx
    refine ⟨?_, fun w hw => ?_⟩
    · have hcts : Continuous (fun p : Matrix (Fin g) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ =>
          p.1ᵀ *ᵥ (cst (uCo bas x) + p.2 *ᵥ cst (vCo bas x))) :=
        (continuous_fst.matrix_transpose).matrix_mulVec
          (continuous_const.add (continuous_snd.matrix_mulVec continuous_const))
      exact ContinuousAt.comp (f := fun z => (A z, T0 z)) hcts.continuousAt (hA0.prodMk hT0)
    · rw [h.per w hw x]
      simp only [chartS, tauAt]
      have hz : (∑ j, (w (Fin.castLE L.a_le j) / (2 * Real.pi * Complex.I)) •
          (B j).map (fun x : ℤ => (x : ℂ))) *ᵥ cst (vCo bas x) = 0 := by
        rw [Matrix.sum_mulVec]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [Matrix.smul_mulVec, cst_mulVec, ker_each B h.B_psd _ hxv j, cst_zero, smul_zero]
      rw [Matrix.add_mulVec, hz, add_zero]
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hxv := (hmem _).1 x.2
    set u := uCo bas (x : Λ) with hu
    set v := vCo bas (x : Λ) with hv
    have hS : (A 0)ᵀ *ᵥ (cst u + T0 0 *ᵥ cst v) = 0 := hx
    have hy : cst u + T0 0 *ᵥ cst v = 0 := by
      have := congrArg (fun y => ((A 0)ᵀ)⁻¹ *ᵥ y) hS
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit] using this
    set r : Fin g → ℝ := fun k => (v k : ℝ) with hr
    have him : ((T0 0).map Complex.im) *ᵥ r = 0 := by
      funext i
      have h1 := congrArg Complex.im (congrFun hy i)
      simpa [cst, mulVec, dotProduct, hr] using h1
    have hlow := GlobalTheory.CompanionTheory.ChartBlockLower.im_lower_on_kernel n a g L.a_le (Metric.ball 0 ρ) T0 B c
      Metric.isOpen_ball (h.T_cont.mono (Metric.ball_subset_ball h.ρ_le)) h.B_psd h.c_pos h.im_lower 0
      (Metric.mem_ball_self h.ρ_pos) 0 (fun j hj => absurd rfl hj) (fun _ _ => rfl) r
      (fun j _ => by
        rw [hr, map_mulVec_real, ker_each B h.B_psd _ hxv j]
        funext k
        simp)
    simp only [Pi.zero_apply, zero_div, zero_smul, Finset.sum_const_zero, add_zero] at hlow
    rw [him, dotProduct_zero] at hlow
    have hrr : r ⬝ᵥ r ≤ 0 := by
      by_contra hcon
      exact absurd hlow (not_le.2 (mul_pos h.c_pos (not_le.1 hcon)))
    have hr0 : r = 0 := by
      refine dotProduct_self_eq_zero.1 (le_antisymm hrr ?_)
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hv0 : v = 0 := by
      funext k
      have := congrFun hr0 k
      simpa [hr] using this
    have hu0 : u = 0 := by
      rw [hv0, cst_zero, mulVec_zero, add_zero] at hy
      funext k
      have := congrFun hy k
      simpa [cst] using this
    refine Subtype.ext (eq_of_coords bas ?_ ?_)
    · rw [← hu, hu0]; simp
    · rw [← hv, hv0]; simp
  · rw [eq_top_iff]
    intro y _
    set t : Fin g → ℂ := ((A 0)ᵀ)⁻¹ *ᵥ y with ht
    have hyt : y = (A 0)ᵀ *ᵥ t := by
      rw [ht, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
    have hper : ∀ i, (A 0)ᵀ *ᵥ cst (Pi.single i 1 : Fin g → ℤ) ∈
        Submodule.span ℂ (Set.range (chartPer bas A T0 B)) := by
      intro i
      refine Submodule.subset_span ⟨⟨mk bas (Pi.single i 1) 0, ?_⟩, ?_⟩
      · rw [hmem, vCo_mk]; simp
      · change chartS bas A T0 (mk bas (Pi.single i 1) 0) 0 = _
        simp only [chartS, uCo_mk, vCo_mk, cst_zero, mulVec_zero, add_zero]
    rw [hyt, vec_eq_sum t, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ _ (hper i)

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CoordinateRatioValueAtPointStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinate_ratio_value_at_point : ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] (y' : (Σ k, ι' k) → Ω) (z : (Σ k, ι' k) → ℂ) (k : K') (c : ι' k), z ∈ mcPts (mCoordIdeal y') → z ⟨k, c⟩ ≠ 0 → y' ⟨k, c⟩ ≠ 0 ∧ ∀ i : ι' k, IsValueAt y' (y' ⟨k, i⟩ / y' ⟨k, c⟩) z ((z ⟨k, c⟩)⁻¹ * z ⟨k, i⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.isValueAt_coord_ratio | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.isValueAt_coord_ratio | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.isValueAt_coord_ratio <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspSubmodulesLocallyFinite
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cusp_submodules_locally_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ), IsOpen U → IsHolFam U R → IsCMFam σ → (∀ t ∈ U, (R t).HasRank σ m) → ∀ t₀ ∈ U, ∃ (ε : ℝ) (F : Finset (Submodule (𝓞 E) Λ)), 0 < ε ∧ ∀ t ∈ U ∩ Metric.ball t₀ ε, (∀ I ∈ F, (R t).IsCusp I) ∧ ∀ I, (R t).IsCusp I → (R t).nz σ I ≤ 1 → I ∈ F := by
  first | exact @LevelTowerAlt.cusps_locally_finite_family | exact LevelTowerAlt.cusps_locally_finite_family
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryTwistMinorOtherStepsStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elementary_twist_minor_other_steps : ∀ (N j : ℕ) (a b ca cb : Fin N), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (i : Fin N), i ≠ a → ∀ I, minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j i) = minorIJ h I (stepCols N j i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TransvOther.minorIJ_other_step | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TransvOther.minorIJ_other_step | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TransvOther.minorIJ_other_step <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryTwistMinorScalarStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elementary_twist_minor_scalar : ∀ (N j : ℕ) (a b ca cb : Fin N), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (h B : Matrix (Fin N) (Fin N) ℂ) (t t' μ : ℂ), h.det ≠ 0 → IsBlockDiag j B → B.BlockTriangular id → (∀ I, minorIJ (h * B * (1 + Matrix.single cb ca t')) I (stepCols N j a) = μ * minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j a)) → μ = (∏ c ∈ (stepCols N j a).erase ca, B c c) * (B ca ca + t' * B ca cb) ∧ μ * t = (∏ c ∈ (stepCols N j a).erase ca, B c c) * (t' * B cb cb) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Plane.param_relation | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Plane.param_relation | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Plane.param_relation <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBaseChartAtGoodPointStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_chart_at_good_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (F : FrameData ι Ψ N M.Ω M.blk) (x₀ : Rb.X), M.GoodAt F (mCoordIdeal (Rb.lift x₀ x₀)) → ∃ (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ), x₀ ∈ (Rb.A.chart kb).source ∧ Rb.A.chart kb x₀ ∈ V ∧ IsBaseChart M Rb F kb V bl := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.BaseLift.exists_baseChart | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.BaseLift.exists_baseChart | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.BaseLift.exists_baseChart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBlockDiagFrameChangeStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_block_diag_frame_change : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι k) → ℂ), z ∈ mcPts (mCoordIdeal y) → M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z)) → ∃ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ, IsBlockDiag j (h τ) ∧ (h τ).det ≠ 0) ∧ ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M.blk z) p.2 ⟨k, m⟩ (h p.1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.exists_flags_good | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.exists_flags_good | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.exists_flags_good <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFamilyInIdealOfIsOFamily
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem oFamily_of_image : ∀ (E : Type) [Field E] [NumberField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (W I : Submodule (𝓞 E) Λ) (per : W →+ (Fin g → ℂ)) (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (r : ℕ) (v : Fin r → Fin g → ℂ), I ≤ W → Function.Injective per → (∀ (c : 𝓞 E) (x : W), per (c • x) = ρ c (per x)) → IsOFamily ρ (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) v → ∃ y : Fin r → W, (∀ a, (y a : Λ) ∈ I) ∧ (∀ a, per (y a) = v a) ∧ LinearIndependent (𝓞 E) (fun a => (y a : Λ)) ∧ (oSpan ρ v).relIndex (AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x}) = (Submodule.span (𝓞 E) (Set.range fun a => (y a : Λ))).toAddSubgroup.relIndex I.toAddSubgroup := by
  intro E _ _ g Λ _ _ W I per ρ r v hIW hinj hact hO
  classical
  set J : Submodule (𝓞 E) W := I.comap W.subtype with hJ
  have hS : AddSubgroup.closure {p | ∃ x : W, (x : Λ) ∈ I ∧ p = per x} = J.toAddSubgroup.map per := by
    apply le_antisymm
    · rw [AddSubgroup.closure_le]
      rintro p ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro p ⟨x, hx, rfl⟩
      exact AddSubgroup.subset_closure ⟨x, hx, rfl⟩
  rw [hS] at hO ⊢
  obtain ⟨hmem, hind, hfin⟩ := hO
  choose y hyJ hyv using fun a => (hmem a)
  have hyI : ∀ a, ((y a : W) : Λ) ∈ I := fun a => hyJ a
  have hsum : ∀ c : Fin r → 𝓞 E, per (∑ i, c i • y i) = ∑ i, ρ (c i) (v i) := by
    intro c
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hact, hyv]
  refine ⟨y, hyI, hyv, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h0 : ∑ i, c i • y i = 0 := by
      apply Subtype.ext
      simpa using hc
    have := hind c (by rw [← hsum, h0, map_zero])
    exact congrFun this i
  · set P : Submodule (𝓞 E) W := Submodule.span (𝓞 E) (Set.range y) with hP
    have hspan : oSpan ρ v = P.toAddSubgroup.map per := by
      apply le_antisymm
      · rw [oSpan, AddSubgroup.closure_le]
        rintro p ⟨a, i, rfl⟩
        refine ⟨a • y i, ?_, ?_⟩
        · exact P.smul_mem a (Submodule.subset_span ⟨i, rfl⟩)
        · simp only [hact, hyv]
      · rintro p ⟨x, hx, rfl⟩
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hx
        show per _ ∈ _
        rw [hsum]
        exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨c i, i, rfl⟩
    have hPΛ : (Submodule.span (𝓞 E) (Set.range fun a => (y a : Λ))).toAddSubgroup
        = P.toAddSubgroup.map W.subtype.toAddMonoidHom := by
      have : Submodule.span (𝓞 E) (Set.range fun a => (y a : Λ)) = P.map W.subtype := by
        rw [hP, Submodule.map_span, ← Set.range_comp]
        rfl
      rw [this]
      ext x
      simp
    have hIΛ : I.toAddSubgroup = J.toAddSubgroup.map W.subtype.toAddMonoidHom := by
      ext x
      constructor
      · intro hx
        exact ⟨⟨x, hIW hx⟩, hx, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact hz
    rw [hspan, hPΛ, hIΛ, AddSubgroup.relIndex_map_map_of_injective _ _ hinj,
      AddSubgroup.relIndex_map_map_of_injective _ _ W.injective_subtype]

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumAndCuspWeightBoundsStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_minimum_and_cusp_weight_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ), IsCMFam σ → R.HasRank σ m → 1 ≤ m → 0 < R.lam1 ∧ (∀ v : Λ, v ≠ 0 → R.lam1 ≤ Real.sqrt (R.normSq v)) ∧ (∀ I, R.IsCusp I → -Real.log (R.nz σ I) ≤ R.cuspW σ ∧ Module.finrank (𝓞 E) I ≤ m) ∧ 0 ≤ R.cuspW σ ∧ R.cuspW σ ≤ Fintype.card Ψ * m * (2 * max 0 (Real.log (1 / R.lam1)) + Real.log (2 * Fintype.card Ψ * m * (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.cuspW_le | exact GlobalTheory.CompanionTheory.Ar.Cusp.cuspW_le | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.cuspW_le <;> assumption)
end

