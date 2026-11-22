import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0203
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KRegConv
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem kReg_conv : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) (k k' : Mat n → (E.V →L[ℂ] E.V)), KReg k → KReg k' → KReg (conv μ E k k') := by
  intro hL n _ _ μ _ E k k' hk hk'
  obtain ⟨hsub, -, -, -, hcG, -, -⟩ := hL n
  obtain ⟨hkc, R, hR⟩ := hk
  obtain ⟨hkc', R', hR'⟩ := hk'
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hval : ∀ y : G n, y.val ∈ GLs n := fun y => by
    have : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    exact this.ne_zero
  have hmul : ∀ a ∈ GLs n, ∀ b ∈ GLs n, a * b ∈ GLs n := fun a ha b hb => by
    change (a * b).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero ha hb
  refine ⟨?_, R + R', fun x hx hlt => ?_⟩
  · have hcv : Continuous (fun y : G n => y.val) := Units.continuous_val
    have hci : Continuous (fun y : G n => (y⁻¹ : G n).val) := hcv.comp continuous_inv
    have h1 : ContinuousOn (fun p : Mat n × G n => k p.2.val) (GLs n ×ˢ Set.univ) :=
      hkc.comp (hcv.comp continuous_snd).continuousOn (fun p _ => hval p.2)
    have h2 : ContinuousOn (fun p : Mat n × G n => k' ((p.2⁻¹ : G n).val * p.1)) (GLs n ×ˢ Set.univ) :=
      hkc'.comp ((hci.comp continuous_snd).mul continuous_fst).continuousOn
        (fun p hp => hmul _ (hval _) _ hp.1)
    have h3 : ContinuousOn (Function.uncurry fun (x : Mat n) (y : G n) => k y.val * k' ((y⁻¹ : G n).val * x))
        (GLs n ×ˢ Set.univ) := h1.clm_comp h2
    exact continuousOn_integral_of_compact_support (hcG R) h3 (fun x y _ hy => by
      have : R < lg y.val := not_le.1 hy
      simp [hR _ (hval y) this])
  · have hz : ∀ y : G n, k y.val * k' ((y⁻¹ : G n).val * x) = 0 := fun y => by
      by_cases hy : R < lg y.val
      · simp [hR _ (hval y) hy]
      · have hm : (y⁻¹ : G n).val * x ∈ GLs n := hmul _ (hval _) _ hx
        have hle := hsub _ (hval y) _ hm
        have he : y.val * ((y⁻¹ : G n).val * x) = x := by
          rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
        rw [he] at hle
        have : R' < lg ((y⁻¹ : G n).val * x) := by linarith [not_lt.1 hy]
        rw [hR' _ hm this, mul_zero]
    change ∫ y : G n, k y.val * k' ((y⁻¹ : G n).val * x) ∂μ = 0
    rw [show (fun y : G n => k y.val * k' ((y⁻¹ : G n).val * x)) = fun _ => 0 from funext hz, integral_zero]

end GlobalTheory.CompanionTheory.WaveMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelActionEquivariant
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem act_kReg_section : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (E : KMod n) (κ : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), KReg κ →
    ContinuousOn f (GLs n) →
    (∀ y ∈ GLs n, ∀ k₁ : Matrix.unitaryGroup (Fin n) ℂ, κ (k₁.1 * y) = E.ρ k₁ * κ y) →
    ContinuousOn (act μ E κ f) (GLs n) ∧
      ∀ x ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, act μ E κ f (x * k₂.1) = E.ρ k₂⁻¹ (act μ E κ f x) := by
  intro hL n _ _ μ _ E κ f hκ hf hleft
  obtain ⟨-, -, -, -, hcG, -, -⟩ := hL n
  obtain ⟨hkc, R, hR⟩ := hκ
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hval : ∀ y : G n, y.val ∈ GLs n := fun y => by
    have : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    exact this.ne_zero
  have hmul : ∀ a ∈ GLs n, ∀ b ∈ GLs n, a * b ∈ GLs n := fun a ha b hb => by
    change (a * b).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero ha hb
  refine ⟨?_, fun x _ k₂ => ?_⟩
  · have hcv : Continuous (fun y : G n => y.val) := Units.continuous_val
    have h1 : ContinuousOn (fun p : Mat n × G n => κ p.2.val) (GLs n ×ˢ Set.univ) :=
      hkc.comp (hcv.comp continuous_snd).continuousOn (fun p _ => hval p.2)
    have h2 : ContinuousOn (fun p : Mat n × G n => f (p.1 * p.2.val)) (GLs n ×ˢ Set.univ) :=
      hf.comp (continuous_fst.mul (hcv.comp continuous_snd)).continuousOn
        (fun p hp => hmul _ hp.1 _ (hval _))
    have h3 : ContinuousOn (Function.uncurry fun (x : Mat n) (y : G n) => κ y.val (f (x * y.val)))
        (GLs n ×ˢ Set.univ) := h1.clm_apply h2
    exact continuousOn_integral_of_compact_support (hcG R) h3 (fun x y _ hy => by
      have : R < lg y.val := not_le.1 hy
      simp [hR _ (hval y) this])
  · have hk : k₂.1 * (k₂⁻¹).1 = 1 := congrArg Subtype.val (mul_inv_cancel k₂)
    have hk' : (k₂⁻¹).1 * k₂.1 = 1 := congrArg Subtype.val (inv_mul_cancel k₂)
    let g : G n := ⟨(k₂⁻¹).1, k₂.1, hk', hk⟩
    change ∫ y : G n, κ y.val (f (x * k₂.1 * y.val)) ∂μ = E.ρ k₂⁻¹ (∫ y : G n, κ y.val (f (x * y.val)) ∂μ)
    rw [← integral_mul_left_eq_self (fun y : G n => κ y.val (f (x * k₂.1 * y.val))) g]
    have hpt : ∀ y : G n, κ (g * y).val (f (x * k₂.1 * (g * y).val)) =
        E.ρ k₂⁻¹ (κ y.val (f (x * y.val))) := fun y => by
      have e1 : (g * y).val = (k₂⁻¹).1 * y.val := rfl
      have e2 : x * k₂.1 * ((k₂⁻¹).1 * y.val) = x * y.val := by
        rw [mul_assoc, ← mul_assoc k₂.1, hk, one_mul]
      rw [e1, e2, hleft _ (hval y) k₂⁻¹]
      rfl
    simp_rw [hpt]
    exact (E.ρ k₂⁻¹).integral_comp_comm'
      (AddMonoidHomClass.isometry_of_norm (E.ρ k₂⁻¹) (E.iso _)).antilipschitz _

end GlobalTheory.CompanionTheory.WaveMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelAdjointRegular
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem continuousOn_inv_GLs {n : ℕ} : ContinuousOn (fun y : Mat n => y⁻¹) (GLs n) := by
  have h : (fun y : Mat n => y⁻¹) = fun y => (y.det)⁻¹ • y.adjugate := by
    funext y
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact ((continuous_id.matrix_det).continuousOn.inv₀ (fun y hy => hy)).smul
    (continuous_id.matrix_adjugate).continuousOn

theorem unitary_matrix_inv {n : ℕ} (k : Matrix.unitaryGroup (Fin n) ℂ) :
    (k.1 : Mat n)⁻¹ = (k⁻¹).1 := by
  apply Matrix.inv_eq_left_inv
  have := congrArg Subtype.val (inv_mul_cancel k)
  simpa using this

theorem adjoint_rho_inv {n : ℕ} (E : KMod n) [CompleteSpace E.V] (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ContinuousLinearMap.adjoint (E.ρ k⁻¹) = E.ρ k := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  let f : E.V →ₗᵢ[ℂ] E.V := ⟨(E.ρ k : E.V →L[ℂ] E.V).toLinearMap, E.iso k⟩
  have h1 : E.ρ k (E.ρ k⁻¹ y) = y := by
    have : E.ρ k * E.ρ k⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg (fun T : E.V →L[ℂ] E.V => T y) this
  have h2 := f.inner_map_map x (E.ρ k⁻¹ y)
  have h3 : f (E.ρ k⁻¹ y) = y := h1
  rw [h3] at h2
  exact h2

theorem adjoint_kernel_reg : LgFacts → ∀ (n : ℕ) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)), KReg k → (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) → (haveI := FiniteDimensional.complete ℂ E.V; KReg (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) ∧ ∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, ContinuousLinearMap.adjoint (k (k₁.1 * y * k₂.1)⁻¹) = E.ρ k₁ * ContinuousLinearMap.adjoint (k y⁻¹) * E.ρ k₂) := by
  intro hL n E k hk heq
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨hc, R, hR⟩ := hk
  refine ⟨⟨?_, R, ?_⟩, ?_⟩
  · have hinv : ContinuousOn (fun y : Mat n => k y⁻¹) (GLs n) :=
      hc.comp continuousOn_inv_GLs (fun y hy => inv_mem_GLs hy)
    exact (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E.V) (F := E.V)).continuous.comp_continuousOn hinv
  · intro y hy hlt
    have h1 : lg y⁻¹ = lg y := (hL n).2.1 y hy
    have h2 : k y⁻¹ = 0 := hR _ (inv_mem_GLs hy) (by rw [h1]; exact hlt)
    simp [h2]
  · intro y hy k₁ k₂
    have h1 : ((k₁.1 : Mat n) * y * k₂.1)⁻¹ = (k₂⁻¹).1 * y⁻¹ * (k₁⁻¹).1 := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, unitary_matrix_inv, unitary_matrix_inv, mul_assoc]
    rw [h1, heq _ (inv_mem_GLs hy)]
    have h2 : ContinuousLinearMap.adjoint (E.ρ k₂⁻¹ * k y⁻¹ * E.ρ k₁⁻¹)
        = ContinuousLinearMap.adjoint (E.ρ k₁⁻¹) * ContinuousLinearMap.adjoint (k y⁻¹)
          * ContinuousLinearMap.adjoint (E.ρ k₂⁻¹) := by
      simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp]
      rfl
    rw [h2, adjoint_rho_inv, adjoint_rho_inv]

end GlobalTheory.CompanionTheory.WaveMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelMultiplierLinear
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem conv_eq_sum_of_kernels : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) {ι ι' : Type} [Fintype ι] [Fintype ι'] (c : ι → ℂ) (c' : ι' → ℂ) (ks : ι → Mat n → (E.V →L[ℂ] E.V)) (ks' : ι' → Mat n → (E.V →L[ℂ] E.V)) (k k' : Mat n → (E.V →L[ℂ] E.V)), (∀ i, KReg (ks i)) → (∀ j, KReg (ks' j)) → (∀ y ∈ GLs n, k y = ∑ i, c i • ks i y) → (∀ y ∈ GLs n, k' y = ∑ j, c' j • ks' j y) → ∀ x ∈ GLs n, conv μ E k k' x = ∑ i, ∑ j, (c i * c' j) • conv μ E (ks i) (ks' j) x := by
  intro hL n _ _ μ _ E ι ι' _ _ c c' ks ks' k k' hks hks' hk hk' x hx
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hval : ∀ y : G n, y.val ∈ GLs n := fun y => by
    have := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    exact this.ne_zero
  have hcv : Continuous (fun y : G n => y.val) := Units.continuous_val
  have hcinv : Continuous (fun y : G n => (y⁻¹ : G n).val) := Units.continuous_val.comp continuous_inv
  have hmem : ∀ y : G n, (y⁻¹ : G n).val * x ∈ GLs n := by
    intro y
    have h1 : ((y⁻¹ : G n).val).det ≠ 0 := hval _
    change ((y⁻¹ : G n).val * x).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero h1 hx
  have hint : ∀ i j, Integrable (fun y : G n => ks i y.val * ks' j ((y⁻¹ : G n).val * x)) μ := by
    intro i j
    obtain ⟨hc, R, hR⟩ := hks i
    have hcont : Continuous (fun y : G n => ks i y.val * ks' j ((y⁻¹ : G n).val * x)) := by
      have h1 : Continuous (fun y : G n => ks i y.val) := hc.comp_continuous hcv hval
      have h2 : Continuous (fun y : G n => ks' j ((y⁻¹ : G n).val * x)) :=
        (hks' j).1.comp_continuous (hcinv.mul continuous_const) hmem
      exact h1.mul h2
    have hsupp : HasCompactSupport (fun y : G n => ks i y.val * ks' j ((y⁻¹ : G n).val * x)) := by
      refine HasCompactSupport.intro ((hL n).2.2.2.2.1 R) ?_
      intro y hy
      have hy' : R < lg y.val := not_le.1 hy
      simp [hR y.val (hval y) hy']
    exact hcont.integrable_of_hasCompactSupport hsupp
  have hpt : (fun y : G n => k y.val * k' ((y⁻¹ : G n).val * x))
      = fun y : G n => ∑ i, ∑ j, (c i * c' j) • (ks i y.val * ks' j ((y⁻¹ : G n).val * x)) := by
    funext y
    rw [hk y.val (hval y), hk' _ (hmem y), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm]
  have hi : ∀ i ∈ (Finset.univ : Finset ι), Integrable
      (fun y : G n => ∑ j, (c i * c' j) • (ks i y.val * ks' j ((y⁻¹ : G n).val * x))) μ :=
    fun i _ => integrable_finset_sum _ fun j _ => (hint i j).smul (c i * c' j)
  unfold conv
  rw [hpt, integral_finset_sum _ hi]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hj : ∀ j ∈ (Finset.univ : Finset ι'), Integrable
      (fun y : G n => (c i * c' j) • (ks i y.val * ks' j ((y⁻¹ : G n).val * x))) μ :=
    fun j _ => (hint i j).smul (c i * c' j)
  rw [integral_finset_sum _ hj]
  exact Finset.sum_congr rfl fun j _ => integral_smul (c i * c' j) _

end GlobalTheory.CompanionTheory.WaveMult
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LTLTInv
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveCp
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp

section LeftTranslation

variable {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem LT_coeFn (x : G n) (u : Lp V 2 μ) :
    (LT μ x u : G n → V) =ᵐ[μ] fun g => u (x⁻¹ * g) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_mul_left μ x⁻¹)

theorem LT_LT_inv (x : G n) (u : Lp V 2 μ) : LT μ x (LT μ x⁻¹ u) = u := by
  apply Lp.ext
  have h1 := LT_coeFn μ x (LT μ x⁻¹ u)
  have h2 := LT_coeFn μ x⁻¹ u
  have h3 := (measurePreserving_mul_left μ x⁻¹).quasiMeasurePreserving.ae_eq_comp h2
  filter_upwards [h1, h3] with g e1 e3
  rw [e1]
  have e3' : (LT μ x⁻¹ u : G n → V) (x⁻¹ * g) = u (x⁻¹⁻¹ * (x⁻¹ * g)) := e3
  rw [e3']
  simp

theorem LT_inner (x : G n) (u v : Lp V 2 μ) : ⟪LT μ x u, LT μ x v⟫_ℂ = ⟪u, v⟫_ℂ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun g : G n => x⁻¹ * g)
    (measurePreserving_mul_left μ x⁻¹)).inner_map_map u v

theorem LT_facts (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) :
    (LT μ x : Lp V 2 μ →L[ℂ] Lp V 2 μ) * LT μ x⁻¹ = 1 ∧
    (∀ u v : Lp V 2 μ, ⟪LT μ x u, v⟫_ℂ = ⟪u, LT μ x⁻¹ v⟫_ℂ) ∧
    ∀ f : Mat n → V, MemLp (fun y : G n => f y.val) 2 μ → LT μ x (toL μ f) = toL μ (transl x f) := by
  refine ⟨?_, fun u v => ?_, fun f hf => ?_⟩
  · ext1 u
    exact LT_LT_inv μ x u
  · conv_lhs => rw [← LT_LT_inv μ x v]
    exact LT_inner μ x u _
  · have hfun : (fun y : G n => transl x f y.val) = (fun y : G n => f y.val) ∘ fun g : G n => x⁻¹ * g := by
      funext y
      simp [transl, Units.val_mul]
    have hm : MemLp (fun y : G n => transl x f y.val) 2 μ := by
      rw [hfun]
      exact hf.comp_measurePreserving (measurePreserving_mul_left μ x⁻¹)
    apply Lp.ext
    have h1 := LT_coeFn μ x (toL μ f)
    have h2 : (toL μ f : G n → V) =ᵐ[μ] fun g => f g.val := toL_coe hf
    have h3 := (measurePreserving_mul_left μ x⁻¹).quasiMeasurePreserving.ae_eq_comp h2
    have h4 : (toL μ (transl x f) : G n → V) =ᵐ[μ] fun g => transl x f g.val := toL_coe hm
    filter_upwards [h1, h3, h4] with g e1 e3 e4
    rw [e1, e4]
    have e3' : (toL μ f : G n → V) (x⁻¹ * g) = f (x⁻¹ * g).val := e3
    rw [e3']
    simp [transl, Units.val_mul]

end LeftTranslation

end GlobalTheory.CompanionTheory.WaveCp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateRightDerivative
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobGL.LeftTr

variable {n : ℕ}

theorem isOpen_gls (n : ℕ) : IsOpen (GLs n) := by
  have h : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage h

def lmul (x : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x)

def rmul (x : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ x)

theorem lmul_apply (x y : Mat n) : lmul x y = x * y := rfl

theorem mul_mem_gls {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem contDiffOn_along {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (A : E →L[ℝ] E) :
    ContDiffOn ℝ ∞ (fun g => fderiv ℝ f g (A g)) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply A.contDiff.contDiffOn

theorem contDiffOn_Rd {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) :
    ContDiffOn ℝ ∞ (Rd X f) (GLs n) :=
  contDiffOn_along (isOpen_gls n) hf (rmul X)

theorem contDiffOn_Rw {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (w : List (Idx n)) : ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact contDiffOn_Rd ih (bs p)

theorem Rw_left (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V)
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (x : Mat n) (hx : x ∈ GLs n) :
    ContDiffOn ℝ ∞ (fun y => f (x * y)) (GLs n) ∧
      ∀ (w : List (Idx n)), ∀ y ∈ GLs n, Rw w (fun y => f (x * y)) y = Rw w f (x * y) := by
  have hmaps : Set.MapsTo (fun y : Mat n => x * y) (GLs n) (GLs n) :=
    fun y hy => mul_mem_gls hx hy
  refine ⟨hf.comp (lmul x).contDiff.contDiffOn hmaps, fun w => ?_⟩
  induction w with
  | nil => intro y _; rfl
  | cons p w ih =>
    intro y hy
    have hev : Rw w (fun y => f (x * y)) =ᶠ[nhds y] (Rw w f) ∘ (lmul x) :=
      Filter.eventually_of_mem ((isOpen_gls n).mem_nhds hy) ih
    have hd : DifferentiableAt ℝ (Rw w f) (lmul x y) :=
      ((contDiffOn_Rw hf w).contDiffAt ((isOpen_gls n).mem_nhds (mul_mem_gls hx hy))).differentiableAt
        (by simp)
    have hc : HasFDerivAt ((Rw w f) ∘ (lmul x))
        ((fderiv ℝ (Rw w f) (lmul x y)).comp (lmul x)) y :=
      hd.hasFDerivAt.comp y (lmul x).hasFDerivAt
    change fderiv ℝ (Rw w (fun y => f (x * y))) y (y * bs p) =
      fderiv ℝ (Rw w f) (x * y) (x * y * bs p)
    rw [hev.fderiv_eq, hc.fderiv]
    simp only [ContinuousLinearMap.comp_apply, lmul_apply, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.SobGL.LeftTr
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionCompact
section
noncomputable section

open Matrix Finset

namespace GlobalTheory.CompanionTheory.LgBound

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lgCpt : PositivityTheory.RgBcC.VC.LgCpt := by
  intro n R
  haveI : ProperSpace (Mat n) := FiniteDimensional.proper ℂ _
  let f : G n → ℝ := fun y => 1 + ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2)
  have hinv : ∀ y : G n, (y.val)⁻¹ = (y⁻¹).val := fun y => (Matrix.coe_units_inv y).symm
  have hc1 : Continuous fun y : G n => y.val := Units.continuous_val
  have hc2 : Continuous fun y : G n => (y⁻¹).val := Units.continuous_val.comp continuous_inv
  have hfc : Continuous f := by
    refine continuous_const.add (continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_)
    exact ((hc1.matrix_elem a b).norm.pow 2).add ((hc2.matrix_elem a b).norm.pow 2)
  have hsum : ∀ y : G n, 0 ≤ ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) := fun y =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
  have hfpos : ∀ y, 0 < f y := fun y => by
    have := hsum y
    show 0 < 1 + _
    linarith
  have hS : {y : G n | lg y.val ≤ R} = f ⁻¹' Set.Iic (Real.exp R) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic, lg, hinv]
    exact Real.log_le_iff_le_exp (hfpos y)
  rw [hS]
  have hclosed : IsClosed (f ⁻¹' Set.Iic (Real.exp R)) := isClosed_Iic.preimage hfc

  set r : ℝ := Real.exp R with hr
  have hr0 : 0 ≤ r + 1 := by positivity
  have hterm : ∀ y : G n, f y ≤ r → ∀ a b, ‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2 ≤ r := by
    intro y hy a b
    have h1 : ‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2 ≤ ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) :=
      Finset.single_le_sum (f := fun b => ‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2)
        (fun b _ => by positivity) (Finset.mem_univ b)
    have h2 : ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) ≤ ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) :=
      Finset.single_le_sum (f := fun a => ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2))
        (fun a _ => Finset.sum_nonneg fun b _ => by positivity) (Finset.mem_univ a)
    have h3 : 1 + ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) ≤ r := hy
    linarith
  have hle : ∀ t : ℝ, 0 ≤ t → t ^ 2 ≤ r → t ≤ r + 1 := by
    intro t ht h
    nlinarith [sq_nonneg (t - 1)]
  have hb1 : ∀ y : G n, f y ≤ r → ‖y.val‖ ≤ r + 1 := by
    intro y hy
    refine (Matrix.norm_le_iff hr0).2 fun a b => hle _ (norm_nonneg _) ?_
    have := hterm y hy a b
    have h2 : 0 ≤ ‖(y⁻¹).val a b‖ ^ 2 := by positivity
    linarith
  have hb2 : ∀ y : G n, f y ≤ r → ‖(y⁻¹).val‖ ≤ r + 1 := by
    intro y hy
    refine (Matrix.norm_le_iff hr0).2 fun a b => hle _ (norm_nonneg _) ?_
    have := hterm y hy a b
    have h2 : 0 ≤ ‖y.val a b‖ ^ 2 := by positivity
    linarith
  have hball : IsCompact (Metric.closedBall (0 : Mat n) (r + 1)) := isCompact_closedBall _ _
  have hK : IsCompact ((fun p : Mat n × Mat n => (p.1, MulOpposite.op p.2)) ''
      (Metric.closedBall (0 : Mat n) (r + 1) ×ˢ Metric.closedBall (0 : Mat n) (r + 1))) :=
    (hball.prod hball).image (continuous_fst.prodMk (MulOpposite.continuous_op.comp continuous_snd))
  have hpre := (Units.isClosedEmbedding_embedProduct (α := Mat n)).isCompact_preimage hK
  refine hpre.of_isClosed_subset hclosed ?_
  intro y hy
  refine ⟨(y.val, (y⁻¹).val), ⟨?_, ?_⟩, rfl⟩
  · simpa using hb1 y hy
  · simpa using hb2 y hy

end GlobalTheory.CompanionTheory.LgBound
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothMonotoneCutoffExists
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SmoothCut

theorem exists_smooth_antitone_cut :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, deriv χ x ≤ 0) ∧ (∀ x, 0 ≤ χ x) ∧
      (∀ x, x ≤ 0 → χ x = 1) ∧ ∀ x, 1 ≤ x → χ x = 0 := by
  have hanti : Antitone (fun x : ℝ => Real.smoothTransition (1 - x)) := fun a b hab =>
    Real.smoothTransition.monotone (by linarith)
  refine ⟨fun x => Real.smoothTransition (1 - x),
    Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id), ?_,
    fun x => Real.smoothTransition.nonneg _,
    fun x hx => Real.smoothTransition.one_of_one_le (by linarith),
    fun x hx => Real.smoothTransition.zero_of_nonpos (by linarith)⟩
  intro x
  have hneg : Monotone (fun x : ℝ => -Real.smoothTransition (1 - x)) := fun a b hab =>
    neg_le_neg (hanti hab)
  have h := hneg.deriv_nonneg (x := x)
  rw [deriv.fun_neg] at h
  linarith

end GlobalTheory.CompanionTheory.SmoothCut
end

