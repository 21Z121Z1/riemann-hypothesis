import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.Bundle0014
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.TwistedTraces.Bundle0002
import Development.AutomorphicArithmetic.TwistedTraces.Bundle0004
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableCartan

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.CuspDecayArchConvFinAvg
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

theorem UpperTheory.cuspDecay_archConv_finAvg :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
        (ν : Measure (ArchUnits K n)) [ν.IsHaarMeasure] (β : ArchMatrix K n → ℝ)
        (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β) (hβc : HasCompactSupport β)
        (hβu : tsupport β ⊆ Set.range (Units.val : ArchUnits K n → ArchMatrix K n))
        (U : Subgroup (AdelicGLn.integralFiniteGL K n)) (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
        (g : CC K n), CuspDecay μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) := by
  intro K _ _ n μ _ ν _ β hβ hβc hβu U hU g N'
  obtain ⟨Sg, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := K) n
  obtain ⟨f, hf⟩ : ∃ f, f = archConv ν hβ.continuous hβc hβu (finAvg U hU g) := ⟨_, rfl⟩
  rw [← hf]
  obtain ⟨C₀, N₀, hC₀⟩ := exists_norm_rconv_le_siegel_basic μ f hω ht
  obtain ⟨Ch, hCh0, hCh⟩ := exists_height_le_normOne (K := K) (n := n) hω
  obtain ⟨e, he⟩ : ∃ e, e = 2 * Fintype.card (InfinitePlace K) := ⟨_, rfl⟩
  rw [← he] at hCh
  obtain ⟨C₁, hC₁⟩ := exists_norm_rconv_le_decay μ ν hβ hβc hβu U hU g hω hωB ht (n * e * N')
  rw [← hf] at hC₁
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = (max 1 t⁻¹) ^ n := ⟨_, rfl⟩
  have hτ1 : 1 ≤ τ := hτdef ▸ one_le_pow₀ (le_max_left _ _)
  obtain ⟨D, hDdef⟩ : ∃ D, D = max (Ch * τ ^ e) 1 := ⟨_, rfl⟩
  have hD1 : 1 ≤ D := hDdef ▸ le_max_right _ _
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  obtain ⟨B, hBdef⟩ : ∃ B, B = max C₀ 0 + max C₁ 0 := ⟨_, rfl⟩
  have hC₀B : C₀ ≤ B := hBdef ▸ (le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _))
  have hC₁B : C₁ ≤ B := hBdef ▸ (le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _))
  have hB0 : 0 ≤ B := hBdef ▸ add_nonneg (le_max_right _ _) (le_max_right _ _)
  refine ⟨B * D ^ N', fun φ hφ x => ?_⟩
  have hq1 : 1 ≤ qht x := le_ciInf fun γ => one_le_height _
  have hq0 : 0 < qht x := zero_lt_one.trans_le hq1
  have hqN : 0 < qht x ^ N' := pow_pos hq0 _
  obtain ⟨γ, hγ⟩ := hsieg (x : AdelicGLn.AdelicGL K n)
  have hγ1 : AdelicGLn.diagonal K n γ ∈ normOneGL K n := rationalGL_le_normOneGL ⟨γ, rfl⟩
  obtain ⟨γ₁, hγ₁⟩ : ∃ γ₁ : normOneGL K n, γ₁ = ⟨AdelicGLn.diagonal K n γ, hγ1⟩ := ⟨_, rfl⟩
  have hγΓ : γ₁ ∈ Gam K n := ⟨γ, by rw [hγ₁]; rfl⟩
  have hqle : qht x ≤ AutomorphicForm.height ((γ₁ * x : G1 K n) : AdelicGLn.AdelicGL K n) := by
    refine ciInf_le ⟨0, ?_⟩ (⟨γ₁, hγΓ⟩ : Gam K n)
    rintro _ ⟨δ, rfl⟩
    exact (height_pos _).le
  rw [← rconv_mul_left (Gam K n) μ f φ hγΓ x]
  obtain ⟨b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hx⟩ := hγ
  have hx' : ((γ₁ * x : normOneGL K n) : AdelicGLn.AdelicGL K n) =
      b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk := by
    rw [hγ₁]; exact hx

  have hheight : ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin n, i < j → ρ i / ρ j ≤ R) → qht x ≤ D * R ^ e := by
    intro R hR1 hR
    have hall : ∀ i j : Fin n, ρ i / ρ j ≤ τ * R := fun i j => by
      rw [hτdef]; exact siegel_div_le_mul ht hρ hs hR1 hR i j
    have h1 := hCh b hb ρ hρ kk hkk _ (γ₁ * x).2 hx' (τ * R)
      (one_le_mul_of_one_le_of_one_le hτ1 hR1) hall
    calc qht x ≤ _ := hqle
      _ ≤ Ch * (τ * R) ^ e := h1
      _ = Ch * τ ^ e * R ^ e := by rw [mul_pow]; ring
      _ ≤ D * R ^ e := mul_le_mul_of_nonneg_right (hDdef ▸ le_max_left _ _)
          (pow_nonneg (zero_le_one.trans hR1) _)

  have hsmall : (∀ i j : Fin n, i < j → ρ i / ρ j ≤ 1) →
      ‖rconv (Gam K n) μ f φ (γ₁ * x)‖ ≤ B * D ^ N' * (qht x ^ N')⁻¹ * ‖φ‖ := by
    intro hall
    have h := hC₀ φ b hb ρ hρ hs kk hkk (γ₁ * x) hx' 1 le_rfl hall
    rw [one_pow, Real.sqrt_one, mul_one] at h
    have hqD : qht x ≤ D := by simpa using hheight 1 le_rfl hall
    have h1 : 1 ≤ D ^ N' * (qht x ^ N')⁻¹ := by
      rw [le_mul_inv_iff₀ hqN, one_mul]
      exact pow_le_pow_left₀ hq0.le hqD _
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    calc C₀ ≤ B := hC₀B
      _ ≤ B * (D ^ N' * (qht x ^ N')⁻¹) := le_mul_of_one_le_right hB0 h1
      _ = B * D ^ N' * (qht x ^ N')⁻¹ := by ring
  by_cases hn : 2 ≤ n
  · obtain ⟨r, hr, hrn, hratio⟩ := exists_le_max_pow hn ρ hρ
    obtain ⟨α, hαdef⟩ : ∃ α, α = ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩ := ⟨_, rfl⟩
    rw [← hαdef] at hratio
    rcases le_or_gt α 1 with hα1 | hα1
    · exact hsmall fun i j hij => (hratio i j hij).trans (by rw [max_eq_left hα1, one_pow])
    · have hM : max 1 α = α := max_eq_right hα1.le
      have hαn1 : 1 ≤ α ^ n := one_le_pow₀ hα1.le
      have hlt : (⟨r - 1, by omega⟩ : Fin n) < ⟨r, hrn⟩ := by
        rw [Fin.mk_lt_mk]; omega
      have h := hC₁ φ hφ b hb ρ hρ hs kk hkk (γ₁ * x) hx' α hα1.le
        ⟨_, _, hlt, hαdef.le⟩
      have hqA : qht x ≤ D * α ^ (n * e) := by
        have := hheight (α ^ n) hαn1 fun i j hij => (hratio i j hij).trans (by rw [hM])
        rwa [← pow_mul] at this
      have hAN : 0 < α ^ (n * e * N') := pow_pos (zero_lt_one.trans hα1) _
      have h1 : (α ^ (n * e * N'))⁻¹ ≤ D ^ N' * (qht x ^ N')⁻¹ := by
        rw [le_mul_inv_iff₀ hqN, inv_mul_le_iff₀ hAN, pow_mul α (n * e) N', ← mul_pow]
        refine pow_le_pow_left₀ hq0.le ?_ _
        linarith [mul_comm (α ^ (n * e)) D]
      refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      calc C₁ * (α ^ (n * e * N'))⁻¹ ≤ B * (D ^ N' * (qht x ^ N')⁻¹) :=
            mul_le_mul hC₁B h1 (inv_nonneg.2 hAN.le) hB0
        _ = B * D ^ N' * (qht x ^ N')⁻¹ := by ring
  · refine hsmall fun i j hij => ?_
    have : (i : ℕ) < j := hij
    omega
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.CuspDecayFinsetSum
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

private theorem rconv_add_fun {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] (a b : CC K n) (φ : L2 μ) (x : G1 K n) :
    rconv (Gam K n) μ (a + b : CC K n) φ x =
      rconv (Gam K n) μ a φ x + rconv (Gam K n) μ b φ x := by
  unfold rconv
  rw [← integral_add (integrable_rconv (Gam K n) μ a φ x) (integrable_rconv (Gam K n) μ b φ x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply, add_mul]

private theorem cuspDecay_zero {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] : CuspDecay μ (0 : CC K n) := fun _ =>
  ⟨0, fun φ _ x => by simp [rconv]⟩

private theorem cuspDecay_add {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n))
    [μ.IsHaarMeasure] {a b : CC K n} (ha : CuspDecay μ a) (hb : CuspDecay μ b) :
    CuspDecay μ (a + b) := fun N' => by
  obtain ⟨C₁, h₁⟩ := ha N'
  obtain ⟨C₂, h₂⟩ := hb N'
  refine ⟨C₁ + C₂, fun φ hφ x => ?_⟩
  rw [rconv_add_fun, add_mul, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (h₁ φ hφ x) (h₂ φ hφ x))

theorem UpperTheory.cuspDecay_finset_sum :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
        (ι : Type) [Fintype ι] (f : ι → CC K n), (∀ i, CuspDecay μ (f i)) → CuspDecay μ (∑ i, f i) := by
  intro K _ _ n μ _ ι _ f hf
  exact Finset.sum_induction f (CuspDecay μ) (fun _ _ => cuspDecay_add μ) (cuspDecay_zero μ)
    (fun i _ => hf i)
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.CuspDecayOfRankZero
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

theorem UpperTheory.cuspDecay_of_rank_zero :
    ∀ (K : Type) [Field K] [NumberField K] (μ : Measure (G1 K 0)) [μ.IsHaarMeasure] (a : CC K 0), CuspDecay μ a := by
  intro K _ _ μ _ a N'
  haveI : Subsingleton (AdelicGLn.AdelicGL K 0) :=
    ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
  haveI : Subsingleton (G1 K 0) := ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  obtain ⟨Ω₀, hΩ₁, hΩ₁B, t, ht, hsieg⟩ := exists_siegelSet (K := K) 0
  obtain ⟨C₀, N, hC₀⟩ := exists_norm_rconv_le_siegel_basic μ a hΩ₁ ht
  have hq : 1 ≤ qht (1 : G1 K 0) := le_ciInf fun _ => AutomorphicForm.one_le_height _
  have hqN : qht (1 : G1 K 0) ^ N' ≠ 0 := (pow_pos (by linarith) N').ne'
  refine ⟨max C₀ 0 * qht (1 : G1 K 0) ^ N', fun φ _ x => ?_⟩
  obtain ⟨γ, hγ⟩ := hsieg (x : AdelicGLn.AdelicGL K 0)
  obtain ⟨b, hb, a', ⟨ρ, hρ, hs, rfl⟩, kk, hkk, -⟩ := hγ
  have h := hC₀ φ b hb ρ hρ hs kk hkk x (Subsingleton.elim _ _) 1 le_rfl (fun i => i.elim0)
  rw [one_pow, Real.sqrt_one, mul_one] at h
  rw [Subsingleton.elim x 1] at h ⊢
  rw [mul_inv_cancel_right₀ hqN]
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.ExistsContDiffArchMatrixExtensionOfSmooth
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

private theorem UpperTheory.exists_smooth_bump_units {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] (h : IsExpLieAlgebra (⊤ : Subgroup 𝔸ˣ) (⊤ : Submodule ℝ 𝔸))
    (κ : (⊤ : Subgroup 𝔸ˣ) → ℝ) (hs : h.IsSmoothFun (fun A => (κ A : ℂ)))
    (hc : HasCompactSupport κ) :
    ∃ β : 𝔸 → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β ∧ HasCompactSupport β ∧
      tsupport β ⊆ Set.range (Units.val : 𝔸ˣ → 𝔸) ∧
      ∀ A : (⊤ : Subgroup 𝔸ˣ), β ((A : 𝔸ˣ) : 𝔸) = κ A := by
  classical
  let ι : (⊤ : Subgroup 𝔸ˣ) → 𝔸 := fun A => ((A : 𝔸ˣ) : 𝔸)
  have hemb : Topology.IsOpenEmbedding ι :=
    Units.isOpenEmbedding_val.comp (IsOpen.isOpenEmbedding_subtypeVal (by simp))
  have hinj := hemb.injective
  let β : 𝔸 → ℝ := Function.extend ι κ 0
  have hβ : ∀ A, β (ι A) = κ A := fun A => hinj.extend_apply _ _ A
  have hβ0 : ∀ x, x ∉ Set.range ι → β x = 0 := fun x hx =>
    Function.extend_apply' _ _ _ (by simpa using hx)
  have hCc : IsCompact (ι '' tsupport κ) := IsCompact.image hc hemb.continuous
  have hCcl := hCc.isClosed
  have hsupp : Function.support β ⊆ ι '' tsupport κ := by
    intro x hx
    by_cases hr : x ∈ Set.range ι
    · obtain ⟨A, rfl⟩ := hr
      refine ⟨A, subset_tsupport _ ?_, rfl⟩
      rw [Function.mem_support, ← hβ]
      exact hx
    · exact absurd (hβ0 x hr) hx
  have hts : tsupport β ⊆ ι '' tsupport κ := closure_minimal hsupp hCcl
  refine ⟨β, ?_, hCc.of_isClosed_subset (isClosed_tsupport β) hts, ?_, hβ⟩
  · rw [contDiff_iff_contDiffAt]
    intro X
    by_cases hX : X ∈ ι '' tsupport κ
    · obtain ⟨g, -, rfl⟩ := hX
      let e := expPartialHomeomorph ℝ 𝔸
      have hF := (h.isSmoothFun_iff.1 hs) g
      have hF' : ContDiff ℝ ∞ fun Y : (⊤ : Submodule ℝ 𝔸) => κ (g * h.expG Y) :=
        Complex.reCLM.contDiff.comp hF
      let gi : 𝔸 := (((g : 𝔸ˣ)⁻¹ : 𝔸ˣ) : 𝔸)
      have hm : ContDiff ℝ ∞ (fun x : 𝔸 => gi * x) := contDiff_const.mul contDiff_id
      have h1 : gi * ι g = 1 := Units.inv_mul _
      have hn : e.target ∈ nhds (gi * ι g) := by
        rw [h1]; exact e.open_target.mem_nhds (one_mem_expPartialHomeomorph_target ℝ _)
      have hl : ContDiffAt ℝ ∞
          (fun x => subspaceProj (⊤ : Submodule ℝ 𝔸) (e.symm (gi * x))) (ι g) :=
        (subspaceProj (⊤ : Submodule ℝ 𝔸)).contDiff.contDiffAt.comp _
          (((contDiffOn_expPartialHomeomorph_symm ℝ _).contDiffAt hn).comp _ hm.contDiffAt)
      refine (hF'.contDiffAt.comp _ hl).congr_of_eventuallyEq ?_
      filter_upwards [hm.continuous.continuousAt.preimage_mem_nhds hn] with x hx
      have hexp : NormedSpace.exp (e.symm (gi * x)) = gi * x := e.right_inv hx
      have key : ι (g * h.expG (subspaceProj (⊤ : Submodule ℝ 𝔸) (e.symm (gi * x)))) = x := by
        simp only [ι, Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]
        rw [subspaceProj_of_mem Submodule.mem_top, hexp, ← mul_assoc]
        simp [gi]
      rw [Function.comp_apply, ← hβ, key]
    · have hz : β =ᶠ[nhds X] fun _ => (0 : ℝ) := by
        filter_upwards [hCcl.isOpen_compl.mem_nhds hX] with x hx
        by_contra hne
        exact hx (hsupp hne)
      exact contDiffAt_const.congr_of_eventuallyEq hz
  · intro x hx
    obtain ⟨A, -, rfl⟩ := hts hx
    exact ⟨(A : 𝔸ˣ), rfl⟩

theorem UpperTheory.exists_contDiff_archMatrix_extension_of_smooth :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (κ : archGroup K n → ℝ),
        (isExpLieAlgebra K n).IsSmoothFun (fun A => (κ A : ℂ)) → HasCompactSupport κ →
        ∃ β : ArchMatrix K n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β ∧ HasCompactSupport β ∧
          tsupport β ⊆ Set.range (Units.val : ArchUnits K n → ArchMatrix K n) ∧
          ∀ A : archGroup K n, β ((A : ArchUnits K n) : ArchMatrix K n) = κ A := by
  intro K _ _ n κ hs hc
  exact UpperTheory.exists_smooth_bump_units (isExpLieAlgebra K n) κ hs hc
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.ExistsFiniteBasisLeftInvariantCompactSupport
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

theorem UpperTheory.exists_finite_basis_leftInvariant_compactSupport :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (V : Subgroup G),
        IsOpen (V : Set G) → IsCompact (V : Set G) → ∀ S : Set G, IsCompact S →
        ∃ (m : ℕ) (b : Fin m → G) (e : Fin m → CompactlySupportedContinuousMap G ℂ),
          (∀ j, ∀ v ∈ V, ∀ h, e j (v * h) = e j h) ∧
          ∀ f : G → ℂ, (∀ v ∈ V, ∀ h, f (v * h) = f h) → (∀ h, h ∉ S → f h = 0) →
            ∀ h, f h = ∑ j, e j h * f (b j) := by
  intro G _ _ _ _ V hVo hVc S hS
  classical
  have hVcl : IsClosed (V : Set G) := Subgroup.isClosed_of_isOpen V hVo

  let W : G → Set G := fun b => {h | b * h⁻¹ ∈ V}
  have hWpre : ∀ b, W b = (fun h : G => b * h⁻¹) ⁻¹' (V : Set G) := fun b => rfl
  have hcont : ∀ b : G, Continuous (fun h : G => b * h⁻¹) := fun b =>
    continuous_const.mul continuous_inv
  have hWo : ∀ b, IsOpen (W b) := fun b => by
    rw [hWpre]; exact hVo.preimage (hcont b)
  have hWcl : ∀ b, IsClosed (W b) := fun b => by
    rw [hWpre]; exact hVcl.preimage (hcont b)
  have hWself : ∀ b, b ∈ W b := fun b => by
    show b * b⁻¹ ∈ V
    simpa using V.one_mem
  have hWK : ∀ b, W b ⊆ (fun v : G => v⁻¹ * b) '' (V : Set G) := fun b h hh =>
    ⟨b * h⁻¹, hh, by group⟩
  have hKc : ∀ b, IsCompact ((fun v : G => v⁻¹ * b) '' (V : Set G)) := fun b =>
    hVc.image (continuous_inv.mul continuous_const)
  have hWinv : ∀ b, ∀ v ∈ V, ∀ h, v * h ∈ W b ↔ h ∈ W b := fun b v hv h => by
    show b * (v * h)⁻¹ ∈ V ↔ b * h⁻¹ ∈ V
    have : b * (v * h)⁻¹ = b * h⁻¹ * v⁻¹ := by group
    rw [this]
    exact V.mul_mem_cancel_right (V.inv_mem hv)

  let E : G → CompactlySupportedContinuousMap G ℂ := fun b =>
    { toFun := (W b).indicator (fun _ => (1 : ℂ))
      continuous_toFun := (IsClopen.continuous_indicator ⟨hWcl b, hWo b⟩ continuous_const)
      hasCompactSupport' := by
        refine HasCompactSupport.intro (hKc b) (fun x hx => ?_)
        exact Set.indicator_of_notMem (fun hxW => hx (hWK b hxW)) _ }
  have hE : ∀ b h, E b h = (W b).indicator (fun _ => (1 : ℂ)) h := fun _ _ => rfl

  let q : G → Quotient (QuotientGroup.rightRel V) := fun h => Quotient.mk _ h
  have hq : ∀ x y : G, q x = q y ↔ x ∈ W y := fun x y => by
    show Quotient.mk _ x = Quotient.mk _ y ↔ y * x⁻¹ ∈ V
    rw [Quotient.eq]
    exact QuotientGroup.rightRel_apply
  obtain ⟨t, -, ht⟩ := hS.elim_nhds_subcover W (fun x _ => (hWo x).mem_nhds (hWself x))
  let T : Finset (Quotient (QuotientGroup.rightRel V)) := t.image q
  let ε := T.equivFin
  let b : Fin T.card → G := fun j => (ε.symm j).1.out
  have hqb : ∀ j, q (b j) = (ε.symm j).1 := fun j => Quotient.out_eq _
  refine ⟨T.card, b, fun j => E (b j), ?_, ?_⟩
  · intro j v hv h
    rw [hE, hE]
    by_cases hh : h ∈ W (b j)
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem ((hWinv _ v hv h).2 hh)]
    · rw [Set.indicator_of_notMem hh,
        Set.indicator_of_notMem (fun h' => hh ((hWinv _ v hv h).1 h'))]
  · intro f hfV hfS h
    have hfW : ∀ c x, x ∈ W c → f x = f c := fun c x hx => by
      have := hfV (c * x⁻¹) hx x
      simpa using this.symm
    by_cases hT : q h ∈ T
    · let j0 : Fin T.card := ε ⟨q h, hT⟩
      have hj0 : q (b j0) = q h := by
        rw [hqb]; simp [j0]
      have hmem : h ∈ W (b j0) := (hq _ _).1 hj0.symm
      rw [Finset.sum_eq_single j0]
      · rw [hE, Set.indicator_of_mem hmem, one_mul]
        exact hfW _ _ hmem
      · intro j _ hj
        have hnot : h ∉ W (b j) := fun hm => by
          apply hj
          have h1 : (ε.symm j).1 = q h := by rw [← hqb]; exact ((hq _ _).2 hm).symm
          have h2 : ε.symm j = ⟨q h, hT⟩ := Subtype.ext h1
          simp [j0, ← h2]
        rw [hE, Set.indicator_of_notMem hnot, zero_mul]
      · intro hj; exact absurd (Finset.mem_univ _) hj
    · have hhS : h ∉ S := fun hs => by
        have := ht hs
        simp only [Set.mem_iUnion] at this
        obtain ⟨x, hx, hxW⟩ := this
        exact hT (Finset.mem_image.2 ⟨x, hx, ((hq _ _).2 hxW).symm⟩)
      rw [hfS h hhS]
      symm
      refine Finset.sum_eq_zero (fun j _ => ?_)
      have hnot : h ∉ W (b j) := fun hm => hT (by
        rw [(hq _ _).2 hm, hqb]; exact (ε.symm j).2)
      rw [hE, Set.indicator_of_notMem hnot, zero_mul]
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.ExistsSignedBasisLieSubalgebraExpCompact
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.exists_signed_basis_lieSubalgebra_exp_compact :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), ∃ B : LinearMap.BilinForm ℝ (isExpLieAlgebra K n).lieSubalgebra, (∀ X Y, B X Y = trForm K n X Y) ∧ (∀ X Y, B X Y = B Y X) ∧ ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra) (ε : Fin d → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) ∧ (∀ i j, B (b i) (b j) = if i = j then ε i else 0) ∧ ∀ i, ε i = -1 → ∀ t : ℝ, (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (b i)) ∈ archCompact K n := by
  intro K _ _ n
  have hmk : ∀ X Y : (isExpLieAlgebra K n).lieSubalgebra, trForm K n X Y =
      Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K)
        (Matrix.trace (mat (X : ArchMatrix K n) * mat (Y : ArchMatrix K n))) := fun _ _ => rfl
  let B : LinearMap.BilinForm ℝ (isExpLieAlgebra K n).lieSubalgebra :=
    LinearMap.mk₂ ℝ (fun X Y => trForm K n X Y)
      (fun X₁ X₂ Y => by
        simp only [hmk, mat_coe_add, Matrix.add_mul, Matrix.trace_add, map_add])
      (fun r X Y => by
        simp only [hmk, mat_coe_smul, Matrix.smul_mul, Matrix.trace_smul, map_smul])
      (fun X Y₁ Y₂ => by
        simp only [hmk, mat_coe_add, Matrix.mul_add, Matrix.trace_add, map_add])
      (fun r X Y => by
        simp only [hmk, mat_coe_smul, Matrix.mul_smul, Matrix.trace_smul, map_smul])
  have hB : ∀ X Y, B X Y = trForm K n X Y := fun _ _ => rfl
  have hsymm : ∀ X Y, B X Y = B Y X := by
    intro X Y
    rw [hB, hB, hmk, hmk, Matrix.trace_mul_comm]
  obtain ⟨h1, h2, h3⟩ := UpperTheory.trForm_definite_on_archSkew_archHerm K n
  haveI : FiniteDimensional ℝ (isExpLieAlgebra K n).lieSubalgebra :=
    FiniteDimensional.finiteDimensional_submodule (isExpLieAlgebra K n).lieSubalgebra.toSubmodule
  obtain ⟨d, b, ε, hε, horth, hk⟩ := UpperTheory.exists_signed_orthonormal_basis_of_isCompl _ B (archSkew K n) (archHerm K n)
    isCompl_archSkew_archHerm hsymm h1 h2 h3
  refine ⟨B, hB, hsymm, d, b, ε, hε, horth, fun i hi t => expG_mem_archCompact_of_skew _ ?_⟩
  have h := hk i hi
  rw [mem_archSkew] at h
  show Matrix.conjTranspose (t • mat (b i : ArchMatrix K n)) = -(t • mat (b i : ArchMatrix K n))
  rw [Matrix.conjTranspose_smul, star_trivial, h, smul_neg]
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.ExistsSumConvRealSmoothT
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

private noncomputable def mkL {K : Type} [Field K] [NumberField K] {n : ℕ} (L : ℂ →L[ℝ] ℂ) (f : TI K n) : TI K n :=
  ⟨⟨fun g => L (f g), L.continuous.comp f.continuous⟩, f.hasCompactSupport.comp_left (map_zero L)⟩

private theorem smoothT_mkL {K : Type} [Field K] [NumberField K] {n : ℕ} (L : ℂ →L[ℝ] ℂ) {f : TI K n}
    (hf : SmoothT f) : SmoothT (mkL L f) := by
  let _ := (isExpLieAlgebra K n).chartedSpace
  exact L.contDiff.comp_contMDiff hf

private noncomputable def reL : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM

private noncomputable def imL : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM

private theorem conv_split {K : Type} [Field K] [NumberField K] {n : ℕ}
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (a b : TI K n) (x : archGroup K n) :
    conv ν (mkL reL a) b x + conv ν (mkL imL a) (Complex.I • b) x = ∫ y, a y * b (y⁻¹ * x) ∂ν := by
  have hb : Continuous fun y : archGroup K n => b (y⁻¹ * x) := by fun_prop
  have i1 : Integrable (fun y => mkL reL a y * b (y⁻¹ * x)) ν :=
    ((mkL reL a).continuous.mul hb).integrable_of_hasCompactSupport
      (mkL reL a).hasCompactSupport.mul_right
  have i2 : Integrable (fun y => mkL imL a y * (Complex.I • b) (y⁻¹ * x)) ν :=
    ((mkL imL a).continuous.mul ((Complex.I • b).continuous.comp (by fun_prop))).integrable_of_hasCompactSupport
      (mkL imL a).hasCompactSupport.mul_right
  rw [conv_apply, conv_apply, ← integral_add i1 i2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ((a y).re : ℂ) * b (y⁻¹ * x) + ((a y).im : ℂ) * (Complex.I * b (y⁻¹ * x)) = a y * b (y⁻¹ * x)
  have hz : ((a y).re : ℂ) + ((a y).im : ℂ) * Complex.I = a y := Complex.re_add_im _
  calc _ = (((a y).re : ℂ) + ((a y).im : ℂ) * Complex.I) * b (y⁻¹ * x) := by ring
    _ = _ := by rw [hz]

theorem UpperTheory.exists_sum_conv_real_smoothT :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
        (F : TI K n), SmoothT F → ∃ (ι : Type) (_ : Fintype ι) (κ γ : ι → TI K n),
          (∀ i, SmoothT (κ i) ∧ ∀ g, (κ i g).im = 0) ∧ F = ∑ i, conv ν (κ i) (γ i) := by
  intro K _ _ n ν _ F hF
  obtain ⟨N, φ, ψ, h, e⟩ := dixmierMalliavin (isExpLieAlgebra K n) ν (fun g => F g) hF F.hasCompactSupport
  let _ := (isExpLieAlgebra K n).chartedSpace
  let a : Fin N → TI K n := fun i => ⟨⟨φ i, (h i).1.continuous⟩, (h i).2.1⟩
  let b : Fin N → TI K n := fun i => ⟨⟨ψ i, (h i).2.2.1.continuous⟩, (h i).2.2.2⟩
  have has : ∀ i, SmoothT (a i) := fun i => (h i).1
  refine ⟨Fin N × Bool, inferInstance,
    fun p => if p.2 then mkL imL (a p.1) else mkL reL (a p.1),
    fun p => if p.2 then Complex.I • b p.1 else b p.1, ?_, ?_⟩
  · rintro ⟨i, _ | _⟩
    · exact ⟨smoothT_mkL _ (has i), fun g => by simp [mkL, reL]⟩
    · exact ⟨smoothT_mkL _ (has i), fun g => by simp [mkL, imL]⟩
  · ext x
    have ex : F x = ∑ i, groupConv ν (φ i) (ψ i) x := by
      have := congrFun e x
      simpa [Finset.sum_apply] using this
    rw [ex, CompactlySupportedContinuousMap.sum_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool]
    simp only [if_true, Bool.false_eq_true, if_false]
    rw [add_comm, conv_split]
    rfl
end

