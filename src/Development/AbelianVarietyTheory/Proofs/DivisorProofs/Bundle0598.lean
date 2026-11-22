import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0286
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0195
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0586
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0313
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0474
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0588
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0046

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalPhaseFrameSmallAngles
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

namespace GlobalTheory.RiemConst

lemma exp_I_arg_exp_I (t : ℝ) :
    Complex.exp (Complex.I * ((Complex.exp (Complex.I * (t : ℂ))).arg : ℂ)) =
      Complex.exp (Complex.I * (t : ℂ)) := by
  have h := Complex.norm_mul_exp_arg_mul_I (Complex.exp (Complex.I * (t : ℂ)))
  have h1 : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I t
  rw [h1] at h
  simpa [mul_comm] using h

lemma exp_I_neg_sum {n : ℕ} (f : Fin n → ℝ) :
    Complex.exp (Complex.I * ((-∑ k, f k : ℝ) : ℂ)) =
      (∏ k, Complex.exp (Complex.I * (f k : ℂ)))⁻¹ := by
  push_cast
  rw [mul_neg, Complex.exp_neg, Finset.mul_sum, Complex.exp_sum]

theorem phaseFrame_small_angles : ∀ (E : Type) [Field E] (Ψ : Finset (E →+* ℂ)) (r : ℕ) (δ : ℝ), 0 < δ → ∃ η : ℝ, 0 < η ∧ ∀ θ : Ψ → Fin (r - 1) → ℝ, (∀ τ (a : Fin r), ‖phaseFrame θ τ a a - 1‖ < η) → ∃ θ' : Ψ → Fin (r - 1) → ℝ, ‖θ'‖ < δ ∧ phaseFrame θ' = phaseFrame θ := by
  intro E _ Ψ r δ hδ
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.mp
    (Complex.continuousAt_arg (Complex.one_mem_slitPlane)) δ hδ
  refine ⟨η, hη, fun θ hθ => ?_⟩
  refine ⟨fun τ k => (Complex.exp (Complex.I * (θ τ k : ℂ))).arg, ?_, ?_⟩
  · rw [pi_norm_lt_iff hδ]
    intro τ
    rw [pi_norm_lt_iff hδ]
    intro k
    have hk := hθ τ (Fin.castLE (Nat.sub_le r 1) k)
    have hentry : phaseFrame θ τ (Fin.castLE (Nat.sub_le r 1) k) (Fin.castLE (Nat.sub_le r 1) k)
        = Complex.exp (Complex.I * (θ τ k : ℂ)) := by
      simp only [phaseFrame, Matrix.diagonal_apply_eq, angles, Fin.coe_castLE, k.isLt, dif_pos]
    rw [hentry] at hk
    have := hcont (x := Complex.exp (Complex.I * (θ τ k : ℂ))) (by rwa [dist_eq_norm])
    rw [Complex.arg_one, Real.dist_eq, sub_zero] at this
    simpa [Real.norm_eq_abs] using this
  · funext τ
    simp only [phaseFrame]
    congr 1
    funext a
    unfold angles
    split_ifs with h
    · exact exp_I_arg_exp_I _
    · rw [exp_I_neg_sum, exp_I_neg_sum]
      congr 1
      exact Finset.prod_congr rfl fun k _ => exp_I_arg_exp_I _

end GlobalTheory.RiemConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnHilbertEisensteinWeightTwoSeries
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.QHolo

variable {F : Type} [Field F] [NumberField F]

theorem isOpen_upperHalf : IsOpen (upperHalf F) := by
  have : upperHalf F = ⋂ τ : Emb F, (fun z : Emb F → ℂ => (z τ).im) ⁻¹' Set.Ioi 0 := by
    ext z; simp [upperHalf]
  rw [this]
  exact isOpen_iInter_of_finite fun τ => isOpen_Ioi.preimage (by fun_prop)

theorem qClass_two (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (c : Quotient (qRel 𝔞 𝔟)) : qClass 𝔞 𝔟 2 z c =
    ((|(Algebra.norm ℚ c.out.1.1 : ℝ)| / nrm 𝔞 : ℝ) : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * I * ∑ τ, (τ (c.out.1.1 * c.out.1.2) : ℂ) * z τ) := by
  simp [qClass, qTerm, qPow]

theorem differentiable_qClass (𝔞 𝔟 : Frac F) (c : Quotient (qRel 𝔞 𝔟)) :
    Differentiable ℂ (fun z => qClass 𝔞 𝔟 2 z c) := by
  simp only [qClass_two]
  fun_prop

theorem norm_qClass (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (c : Quotient (qRel 𝔞 𝔟)) : ‖qClass 𝔞 𝔟 2 z c‖ =
    |(Algebra.norm ℚ c.out.1.1 : ℝ)| / nrm 𝔞 *
      Real.exp (-(2 * Real.pi) * ∑ τ, τ (c.out.1.1 * c.out.1.2) * (z τ).im) := by
  rw [qClass_two, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (abs_nonneg _) (by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _))]
  congr 2
  simp [Complex.mul_re, Complex.mul_im, Complex.re_sum, Complex.im_sum, Finset.mul_sum]

theorem summable_of_fiber {α β : Type} (g : α → β) (f : α → ℝ) (B : β → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hB : Summable B) (hfib : ∀ (b : β) (s : Finset α), (∀ a ∈ s, g a = b) → ∑ a ∈ s, f a ≤ B b) :
    Summable f := by
  classical
  have hB0 : ∀ b, 0 ≤ B b := fun b => by simpa using hfib b ∅ (by simp)
  refine summable_of_sum_le hf (c := ∑' b, B b) fun u => ?_
  rw [← Finset.sum_fiberwise_of_maps_to (s := u) (t := u.image g) (g := g)
    (fun x hx => Finset.mem_image_of_mem g hx)]
  calc ∑ b ∈ u.image g, ∑ a ∈ u with g a = b, f a ≤ ∑ b ∈ u.image g, B b :=
        Finset.sum_le_sum fun b _ => hfib b _ fun a ha => (Finset.mem_filter.1 ha).2
    _ ≤ ∑' b, B b := hB.sum_le_tsum _ fun b _ => hB0 b

theorem card_fiber_le [IsTotallyReal F] (𝔞 𝔟 : Frac F) (ξ : F) (s : Finset (Quotient (qRel 𝔞 𝔟)))
    (hs : ∀ c ∈ s, c.out.1.1 * c.out.1.2 = ξ) :
    (s.card : ℝ) ≤ |(Algebra.norm ℚ ξ : ℝ)| / (nrm 𝔞 * nrm 𝔟) := GlobalTheory.T.card_hilbertEisensteinFourierFiber_le_norm F 𝔞 𝔟 ξ s hs

theorem abs_norm_le [IsTotallyReal F] (𝔞 𝔟 : Frac F) (p : QPair 𝔞 𝔟) :
    |(Algebra.norm ℚ p.1.1 : ℝ)| ≤ |(Algebra.norm ℚ (p.1.1 * p.1.2) : ℝ)| / nrm 𝔟 := GlobalTheory.T.abs_norm_le_abs_norm_mul_div_absNorm_of_eisensteinIndexPair F 𝔞 𝔟 p

theorem summable_exp_trace [IsTotallyReal F] (L : FractionalIdeal (𝓞 F)⁰ F) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} => Real.exp (-δ * ∑ τ : Emb F, τ x.1)) :=
  GlobalTheory.T.summable_exp_neg_trace_totallyPositive_fractionalIdeal F L δ hδ

theorem norm_sq_exp_le [IsTotallyReal F] {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, ∀ x : F, (∀ τ : Emb F, 0 < τ x) →
    |(Algebra.norm ℚ x : ℝ)| ^ 2 * Real.exp (-δ * ∑ τ : Emb F, τ x) ≤ C * Real.exp (-(δ / 2) * ∑ τ : Emb F, τ x) :=
  GlobalTheory.T.norm_sq_mul_exp_neg_trace_le' F δ hδ

theorem summable_key [IsTotallyReal F] (𝔞 𝔟 : Frac F) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun c : Quotient (qRel 𝔞 𝔟) =>
      |(Algebra.norm ℚ c.out.1.1 : ℝ)| * Real.exp (-δ * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2))) := by
  have hna : 0 ≤ nrm 𝔞 := by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _
  have hnb : 0 ≤ nrm 𝔟 := by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _
  let β := {x : F // x ∈ ((𝔞 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟) ∧ ∀ τ : Emb F, 0 < τ x}
  let g : Quotient (qRel 𝔞 𝔟) → β := fun c =>
    ⟨c.out.1.1 * c.out.1.2, FractionalIdeal.mul_mem_mul c.out.2.1 c.out.2.2.1, c.out.2.2.2⟩
  let B : β → ℝ := fun x => |(Algebra.norm ℚ x.1 : ℝ)| / (nrm 𝔞 * nrm 𝔟) *
    (|(Algebra.norm ℚ x.1 : ℝ)| / nrm 𝔟 * Real.exp (-δ * ∑ τ : Emb F, τ x.1))
  obtain ⟨C, hC⟩ := norm_sq_exp_le (F := F) hδ
  have hB : Summable B := by
    refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_)
      ((summable_exp_trace (F := F) ((𝔞 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟) (half_pos hδ)).mul_left
        ((nrm 𝔞 * nrm 𝔟 * nrm 𝔟)⁻¹ * C))
    have h := hC x.1 x.2.2
    have : B x = (nrm 𝔞 * nrm 𝔟 * nrm 𝔟)⁻¹ *
        (|(Algebra.norm ℚ x.1 : ℝ)| ^ 2 * Real.exp (-δ * ∑ τ : Emb F, τ x.1)) := by
      simp only [B]; field_simp
    rw [this]
    have h2 := mul_le_mul_of_nonneg_left h (show 0 ≤ (nrm 𝔞 * nrm 𝔟 * nrm 𝔟)⁻¹ by positivity)
    linarith
  refine summable_of_fiber g _ B (fun c => by positivity) hB fun b s hs => ?_
  have hξ : ∀ c ∈ s, c.out.1.1 * c.out.1.2 = b.1 := fun c hc => by rw [← hs c hc]
  calc ∑ c ∈ s, |(Algebra.norm ℚ c.out.1.1 : ℝ)| * Real.exp (-δ * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2))
      ≤ ∑ c ∈ s, |(Algebra.norm ℚ b.1 : ℝ)| / nrm 𝔟 * Real.exp (-δ * ∑ τ : Emb F, τ b.1) := by
        refine Finset.sum_le_sum fun c hc => ?_
        rw [← hξ c hc]
        exact mul_le_mul_of_nonneg_right (abs_norm_le 𝔞 𝔟 c.out) (Real.exp_pos _).le
    _ = (s.card : ℝ) * (|(Algebra.norm ℚ b.1 : ℝ)| / nrm 𝔟 * Real.exp (-δ * ∑ τ : Emb F, τ b.1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ B b := mul_le_mul_of_nonneg_right (card_fiber_le 𝔞 𝔟 b.1 s hξ) (by positivity)

theorem exists_im_bound {y : Emb F → ℂ} (hy : y ∈ upperHalf F) :
    ∃ ε > 0, ∀ v ∈ Metric.ball y ε, ∀ τ, ε ≤ (v τ).im := by
  obtain ⟨ε, hε, hle⟩ : ∃ ε > 0, ∀ τ, 2 * ε ≤ (y τ).im := by
    rcases isEmpty_or_nonempty (Emb F) with h | h
    · exact ⟨1, one_pos, fun τ => isEmptyElim τ⟩
    · obtain ⟨τ₀, hτ₀⟩ := Finite.exists_min (fun τ => (y τ).im)
      exact ⟨(y τ₀).im / 2, half_pos (hy τ₀), fun τ => by linarith [hτ₀ τ]⟩
  refine ⟨ε, hε, fun v hv τ => ?_⟩
  have h1 : dist (v τ) (y τ) < ε := (dist_le_pi_dist v y τ).trans_lt (Metric.mem_ball.1 hv)
  have h2 : |(v τ).im - (y τ).im| < ε := by
    rw [Complex.dist_eq] at h1
    exact (by simpa using Complex.abs_im_le_norm (v τ - y τ) : |(v τ).im - (y τ).im| ≤ ‖v τ - y τ‖).trans_lt h1
  linarith [hle τ, (abs_lt.1 h2).1]

theorem qholo : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    DifferentiableOn ℂ (fun z => ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z c) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by
  intro F _ _ _ 𝔞 𝔟
  refine ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.differentiableOn_tsum_loc isOpen_upperHalf
    (fun c z => qClass 𝔞 𝔟 2 z c) (fun c => (differentiable_qClass 𝔞 𝔟 c).differentiableOn) ?_
  intro y hy
  obtain ⟨ε, hε, hv⟩ := exists_im_bound hy
  refine ⟨ε, hε, fun c => (nrm 𝔞)⁻¹ * (|(Algebra.norm ℚ c.out.1.1 : ℝ)| *
      Real.exp (-(2 * Real.pi * ε) * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2))),
    (summable_key 𝔞 𝔟 (by positivity)).mul_left _, fun c v hvb => ?_⟩
  rw [norm_qClass, div_eq_inv_mul, mul_assoc]
  have hn : 0 ≤ (nrm 𝔞)⁻¹ := inv_nonneg.2 (by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _)
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) hn
  refine Real.exp_le_exp.2 ?_
  have hpos := c.out.2.2.2
  have : ε * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2) ≤ ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2) * (v τ).im := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ _ => by nlinarith [hpos τ, hv v hvb τ]
  have hπ := Real.pi_pos
  nlinarith

end GlobalTheory.QHolo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrAlphaDeterminantValuation
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.ShiftLam

theorem ιMulti_sum_smul {K V : Type} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (z : Fin n → V) :
    exteriorPower.ιMulti K n (fun i => ∑ j, M i j • z j) = M.det • exteriorPower.ιMulti K n z := by
  have hA : (exteriorPower.ιMulti K n).compLinearMap (Fintype.linearCombination K z) =
      (Matrix.detRowAlternating : (Fin n → K) [⋀^Fin n]→ₗ[K] K).smulRight
        (exteriorPower.ιMulti K n z) := by
    refine (Pi.basisFun K (Fin n)).ext_alternating fun u hu => ?_
    let s : Equiv.Perm (Fin n) := Equiv.ofBijective u (Finite.injective_iff_bijective.1 hu)
    have e : (fun i => Pi.basisFun K (Fin n) (u i)) = (fun i => Pi.basisFun K (Fin n) i) ∘ s := rfl
    rw [e, AlternatingMap.map_perm, AlternatingMap.map_perm]
    congr 1
    have e1 : (Matrix.detRowAlternating : (Fin n → K) [⋀^Fin n]→ₗ[K] K)
        (fun i => Pi.basisFun K (Fin n) i) = 1 := by
      change Matrix.det (Matrix.of fun i => Pi.basisFun K (Fin n) i) = 1
      rw [show (Matrix.of fun i => Pi.basisFun K (Fin n) i) = 1 from by
        ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one]
    rw [AlternatingMap.smulRight_apply, e1, one_smul, AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    simp
  exact AlternatingMap.congr_fun hA M

theorem val_le_of_image_subset {C O W : Type} [Field C] [CommRing O] [Algebra O C]
    [AddCommGroup W] [Module C W] [Module O W] [IsScalarTower O C W]
    (v : Valuation C NNReal) (hv : v.Integers O) {e : W} (he : e ≠ 0) {μ l : C}
    (H : (fun w => l • w) '' (Submodule.span O {e} : Set W) ⊆
      (fun w => μ • w) '' (Submodule.span O {e} : Set W)) :
    v l ≤ v μ := by
  obtain ⟨w, hw, hwe⟩ := H ⟨e, Submodule.subset_span rfl, rfl⟩
  obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hw
  have hmu : μ * algebraMap O C o = l := by
    apply smul_left_injective C he
    simp only [mul_smul, algebraMap_smul]
    exact hwe
  rw [← hmu, map_mul]
  exact mul_le_of_le_one_right (by positivity) (hv.map_le_one o)

end GlobalTheory.ShiftLam

namespace GlobalTheory.ShiftLam

theorem ringHom_eq_of_apply_gen {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (α : Λ)
    (hα : Algebra.adjoin ℤ_[p] {α} = ⊤) (σ τ : Λ →+* O) (he : σ α = τ α) : σ = τ := by
  let S : Subalgebra ℤ_[p] Λ :=
    { σ.eqLocus τ with
      algebraMap_mem' := fun r => by
        show σ (algebraMap ℤ_[p] Λ r) = τ (algebraMap ℤ_[p] Λ r)
        have h1 := GlobalTheory.T.padic_ring_hom_eq_canonical p O (σ.comp (algebraMap ℤ_[p] Λ))
        have h2 := GlobalTheory.T.padic_ring_hom_eq_canonical p O (τ.comp (algebraMap ℤ_[p] Λ))
        exact (RingHom.congr_fun h1 r).trans (RingHom.congr_fun h2 r).symm }
  have hle : Algebra.adjoin ℤ_[p] {α} ≤ S := Algebra.adjoin_le (by simpa [S] using he)
  ext x
  have hx : x ∈ Algebra.adjoin ℤ_[p] {α} := hα ▸ Algebra.mem_top
  exact hle hx

end GlobalTheory.ShiftLam

theorem GlobalTheory.DetInv.isShift_of_iota_image : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (α : Λ), Algebra.adjoin ℤ_[p] {α} = ⊤ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (τ : Λ →+* O) ι (lam : C), IsIota C D τ N ι → ι '' (detLattice C (actT D) τ N : Set (detLine C (actT D) τ N)) = (fun w => lam • w) '' (detLattice C (actH D) τ N : Set (detLine C (actH D) τ N)) → IsShift C v D τ (v lam * (∏ᶠ σ : {σ : Λ →+* O // σ ≠ τ}, v (algebraMap O C (τ α) - algebraMap O C (σ.1 α)) ^ D.lieRank σ.1)⁻¹) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ α hα N h hh D τ ι lam hι hlat
  unfold IsShift
  intro a b x g m k hx hgx hm hkm
  obtain ⟨ha, hab, hy⟩ := GlobalTheory.T.dvr_determinant_frame_rank p C v O hv ε hε Λ N h hh D τ a b x _ _ hx hgx hkm
  subst hab
  choose y hy using hy
  obtain ⟨X, hX1, hX2, -, hXdet⟩ := GlobalTheory.T.dvr_determinant_product_orders p C v O hv ε hε Λ a b h D τ _ _ hgx hkm
  have hmem : ∀ j, m j ∈ eig C (actH D) τ := fun j => by
    have : m j ∈ filQuot C D τ := hm.2 ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this.1
  let z : Fin (a + b) → eig C (actH D) τ := Fin.append y (fun j => ⟨m j, hmem j⟩)
  have hz1 : ∀ i, z (Fin.castAdd b i) = y i := fun i => Fin.append_left _ _ _
  have hz2 : ∀ j, (z (Fin.natAdd a j) : Fin h → C) = m j := fun j => by
    simp [z, Fin.append_right]
  obtain ⟨c, hc, hcz⟩ := GlobalTheory.T.dvr_alpha_determinant_order p C v O hv ε hε Λ α hα a b h hh D τ z
    (by convert hx using 1; funext i; rw [hz1, hy]) (by convert hm using 1; funext j; exact hz2 j)
  let M : Matrix (Fin (a + b)) (Fin (a + b)) C :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 k)
  have hM : M.det = g.det * k.det := by
    simp only [M, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  let Y : Fin (a + b) → eig C (actH D) τ := fun i => ∑ j, M i j • z j
  have hY1 : ∀ i, Y (Fin.castAdd b i) = ∑ j, g i j • y j := fun i => by
    simp [Y, M, Fin.sum_univ_add, hz1]
  have hY2 : ∀ i, Y (Fin.natAdd a i) = ∑ j, k i j • z (Fin.natAdd a j) := fun i => by
    simp [Y, M, Fin.sum_univ_add]
  have hιX : ι (exteriorPower.ιMulti C (a + b) X) = exteriorPower.ιMulti C (a + b) Y := by
    apply hι
    · intro i hi
      rw [← ha] at hi
      obtain ⟨i', rfl⟩ : ∃ i' : Fin a, Fin.castAdd b i' = i := ⟨⟨i, hi⟩, rfl⟩
      rw [hX1, hY1]
      simp [hy]
    · intro i hi
      rw [← ha] at hi
      obtain ⟨i', rfl⟩ : ∃ i' : Fin b, Fin.natAdd a i' = i :=
        ⟨⟨i - a, by omega⟩, Fin.ext (by simp; omega)⟩
      rw [hX2, hY2]
      simp [hz2]
  have hYz : exteriorPower.ιMulti C (a + b) Y =
      (g.det * k.det) • exteriorPower.ιMulti C (a + b) z := by
    rw [← hM]; exact GlobalTheory.ShiftLam.ιMulti_sum_smul M z
  have himg : ι '' (detLattice C (actT D) τ (a + b) : Set (detLine C (actT D) τ (a + b))) =
      (fun w => (g.det * k.det) • w) ''
        (Submodule.span O {exteriorPower.ιMulti C (a + b) z} : Set (detLine C (actH D) τ (a + b))) := by
    rw [hXdet]
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hu
      refine ⟨o • exteriorPower.ιMulti C (a + b) z,
        Submodule.smul_mem _ _ (Submodule.subset_span rfl), ?_⟩
      show _ = ι _
      rw [LinearMap.map_smul_of_tower, hιX, hYz, smul_comm]
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hu
      refine ⟨o • exteriorPower.ιMulti C (a + b) X,
        Submodule.smul_mem _ _ (Submodule.subset_span rfl), ?_⟩
      show ι _ = _
      rw [LinearMap.map_smul_of_tower, hιX, hYz, smul_comm]
  obtain ⟨hind, hsup, hrk⟩ := (GlobalTheory.T.sandwich_datum_eigen_multiplicity p C v O hv ε hε Λ (a + b) h hh D).2
  obtain ⟨e, -, -, he, hdet⟩ := GlobalTheory.T.exists_basis_quotient_lattice_eigen C v O Λ h (a + b) hv (actH D) τ hind hsup (hrk τ)
  have hfin : (fun w => (g.det * k.det * c) • w) ''
      (Submodule.span O {exteriorPower.ιMulti C (a + b) e} : Set (detLine C (actH D) τ (a + b))) =
      (fun w => lam • w) ''
      (Submodule.span O {exteriorPower.ιMulti C (a + b) e} : Set (detLine C (actH D) τ (a + b))) := by
    rw [← hdet, ← hlat, himg, hcz, Set.image_image]
    simp only [smul_smul]
  have hval : v (g.det * k.det * c) = v lam :=
    le_antisymm (GlobalTheory.ShiftLam.val_le_of_image_subset v hv he hfin.subset)
      (GlobalTheory.ShiftLam.val_le_of_image_subset v hv he hfin.symm.subset)
  have hc0 : v c ≠ 0 := by
    rw [hc]
    refine finprod_induction (fun t : NNReal => t ≠ 0) one_ne_zero (fun s t => mul_ne_zero) ?_
    intro σ
    refine pow_ne_zero _ ((Valuation.ne_zero_iff v).2 (sub_ne_zero.2 fun hst => σ.2 ?_))
    exact GlobalTheory.ShiftLam.ringHom_eq_of_apply_gen α hα σ.1 τ (hv.hom_inj hst).symm
  rw [← hc, ← hval, map_mul, map_mul, mul_inv_cancel_right₀ hc0]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqUnitOfPullbackEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

theorem eq_unit_of_pullback_eq : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∀ (T : Scheme.{0}) (t : T ⟶ S)
    (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → φ' ≫ u.left = φ' ≫ v.left →
    ∀ τ : T, ∀ x : A.left, A.hom x = t τ → (u * v⁻¹).left x = (η[B]).left (t τ) := by
  intro S A B _ _ _ _ u v _ _ _ _ T t A' _ φ' hp he τ x hx
  have hw : φ' ≫ A.hom = A'.hom ≫ t := hp.1.w
  let P : Over.mk (A'.hom ≫ t) ⟶ A := Over.homMk φ' (by simpa using hw)
  have hPu : P ≫ u = P ≫ v := by
    ext1; simpa [P] using he
  have h1 : P ≫ (u * v⁻¹) = 1 := by
    rw [comp_mul, GrpObj.comp_inv, hPu, mul_inv_cancel]
  have h2 : φ' ≫ (u * v⁻¹).left = A'.hom ≫ t ≫ (η[B]).left := by
    have := congrArg CommaMorphism.left h1
    simpa [P, Hom.one_def] using this
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x τ hx
  have hf : (hp.1.isoPullback.inv ≫ φ') z = x := by rw [hp.1.isoPullback_inv_fst]; exact hz1
  have hs : (hp.1.isoPullback.inv ≫ A'.hom) z = τ := by rw [hp.1.isoPullback_inv_snd]; exact hz2
  rw [Scheme.Hom.comp_apply] at hf hs
  rw [← hf, ← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hs]

end GlobalTheory.EndLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingToHenselisationInjectiveOfNbhdStatement
section
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleNbhdLocalRingToHenselisation_injective_of_nbhd : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R), Function.Injective (Hens.of i) := by
  first | exact @GlobalTheory.Henselisation.Hens.of_injective_of_nbhd | exact GlobalTheory.Henselisation.Hens.of_injective_of_nbhd | (intros; apply GlobalTheory.Henselisation.Hens.of_injective_of_nbhd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSurjectiveSectionOfSHStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_of_etale_surjective_of_SH : ∀ (A : Type) [CommRing A], SH A → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of A)), Etale f → Surjective f → ∃ s : Spec (CommRingCat.of A) ⟶ Y, s ≫ f = 𝟙 _ := by
  first | exact @GlobalTheory.EtC.etale_surjective_section_of_SH | exact GlobalTheory.EtC.etale_surjective_section_of_SH | (intros; apply GlobalTheory.EtC.etale_surjective_section_of_SH <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicOfRationalValuationStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraic_of_rational_valuation : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ q : ℚ, ∃ c : ℂ, c ≠ 0 ∧ Sz l lam (-(q : ℝ)) c ∧ Sz l lam q c⁻¹ := by
  first | exact @GlobalTheory.QFam.exists_sz_scale | exact GlobalTheory.QFam.exists_sz_scale | (intros; apply GlobalTheory.QFam.exists_sz_scale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteLocalGeomDomainStatement
section
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_local_geomDomain' : ∀ (k k' : Type) [Field k] [CommRing k'] [IsDomain k'] [Algebra k k'], Module.Finite k k' → ∃ (C : Type) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C) (_ : Algebra k C), IsAdicComplete (maximalIdeal C) C ∧ Nonempty (k' →ₐ[k] ResidueField C) ∧ ∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] C) := by
  first | exact @GlobalTheory.SepRing.exists_complete_local_geomDomain | exact GlobalTheory.SepRing.exists_complete_local_geomDomain | (intros; apply GlobalTheory.SepRing.exists_complete_local_geomDomain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexLinearOfPureTypesFiniteIndex
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem exists_complex_linear_of_pure_types_of_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P') (Φ : D.La ≃ₗ[𝓞 E] D'.La) (N : ℕ), 0 < N → (∀ v : D.La, N • v ∈ lat hP H.rt0 ⊔ lat hP (-H.rt0)) → (∀ a ∈ lat hP H.rt0, Φ a ∈ lat hP' H.rt0) → (∀ a ∈ lat hP (-H.rt0), Φ a ∈ lat hP' (-H.rt0)) → ∃ L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' (Φ a) = L (P a) := by
  intro E _ _ _ H D D' g ty P P' hP hP' Φ N hN hsp h₁ h₂
  obtain ⟨r, hr⟩ := exists_real_extension_of_lattice P hP.2.1 hP.2.2.1 hP.2.2.2.1
    (P'.comp Φ.toLinearMap.toAddMonoidHom)
  have hr' : ∀ a, r (P a) = P' (Φ a) := hr
  have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  have hre : H.rt0.re = 0 ∧ H.rt0.im ≠ 0 := by
    have e₁ := congrArg Complex.re H.sqrt_neg_disc_sq
    have e₂ := congrArg Complex.im H.sqrt_neg_disc_sq
    simp [pow_two] at e₁ e₂
    have him : H.rt0.im ≠ 0 := fun h => by
      rw [h] at e₁; nlinarith [mul_self_nonneg H.rt0.re]
    refine ⟨?_, him⟩
    have : H.rt0.re * H.rt0.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right him
  have hρ : H.rt0 = (H.rt0.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre.1]
  have key : ∀ (ρ : ℂ) (a : D.La), a ∈ lat hP ρ → Φ a ∈ lat hP' ρ → r (ρ • P a) = ρ • r (P a) := by
    intro ρ a ha ha'
    rw [← period_rt_smul hP ha, hr', hr', map_smul, period_rt_smul hP' ha']
  have hPN : ∀ a, r (H.rt0 • P (N • a)) = H.rt0 • r (P (N • a)) := by
    intro a
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hsp a)
    rw [← hxy]
    have k₁ := key _ x hx (h₁ x hx)
    have k₂ := key _ y hy (h₂ y hy)
    rw [neg_smul, neg_smul, map_neg, neg_inj] at k₂
    rw [map_add, smul_add, map_add, map_add, smul_add, k₁, k₂]
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hP0 : ∀ a, r (H.rt0 • P a) = H.rt0 • r (P a) := by
    intro a
    have h := hPN a
    rw [map_nsmul, smul_comm H.rt0 N, map_nsmul, map_nsmul, smul_comm H.rt0 N,
      ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h
    exact smul_right_injective _ hNc h
  have h0 : ∀ v, r (H.rt0 • v) = H.rt0 • r v := by
    intro v
    have hv : v ∈ Submodule.span ℝ (Set.range P) := by rw [hP.2.2.2.1]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hP0 a
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]
    | smul c x _ hx => rw [smul_comm, r.map_smul, r.map_smul, hx, smul_comm]
  have hI : ∀ v, r (Complex.I • v) = Complex.I • r v := by
    intro v
    have := h0 v
    rw [hρ, mul_smul, mul_smul, Complex.coe_smul, Complex.coe_smul, map_smul] at this
    exact smul_right_injective _ hre.2 this
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    { toFun := r
      map_add' := r.map_add
      map_smul' := fun c v => by
        rw [RingHom.id_apply, ← Complex.re_add_im c, add_smul, add_smul, mul_smul, mul_smul, Complex.coe_smul,
          Complex.coe_smul, Complex.coe_smul, Complex.coe_smul, map_add, map_smul, map_smul, hI] }
  have hsurj : Function.Surjective L := by
    show Function.Surjective r
    rw [← LinearMap.range_eq_top, ← top_le_iff, ← hP'.2.2.2.1, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨P (Φ.symm a), by rw [hr', Φ.apply_symm_apply]⟩
  exact ⟨LinearEquiv.ofBijective L ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩, fun a => (hr' a).symm⟩

end GlobalTheory.CompRat
end

