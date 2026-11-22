import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0022
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0020

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensGen
section
noncomputable section

namespace PI.AprimeInfW.GenericDensity

open scoped RealInnerProductSpace FourierTransform
open MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {V W ι : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V]
  [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] [Fintype ι] [DecidableEq ι]

private theorem exists_linearMap_inner_eq_and_det_eq_gram_det (β : W → W → ℝ)
    (hL : ∀ x x' y, β (x + x') y = β x y + β x' y) (hR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hcL : ∀ y, Continuous fun x => β x y) (hcR : ∀ x, Continuous fun y => β x y)
    (b : OrthonormalBasis ι ℝ W) :
    ∃ A : W →ₗ[ℝ] W, (∀ x y, β x y = ⟪x, A y⟫) ∧
      LinearMap.det A = (Matrix.of fun i j => β (b i) (b j)).det := by
  have sL : ∀ (r : ℝ) x y, β (r • x) y = r * β x y := fun r x y =>
    map_real_smul (AddMonoidHom.mk' (fun x => β x y) (fun x x' => hL x x' y)) (hcL y) r x
  have sR : ∀ (r : ℝ) x y, β x (r • y) = r * β x y := fun r x y =>
    map_real_smul (AddMonoidHom.mk' (fun y => β x y) (fun y y' => hR x y y')) (hcR x) r y
  let A : W →ₗ[ℝ] W :=
    { toFun := fun y => ∑ i, β (b i) y • b i
      map_add' := fun y y' => by simp only [hR, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r y => by simp only [sR, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hA : ∀ x y, β x y = ⟪x, A y⟫ := by
    intro x y
    have h1 : β x y = ∑ i, ⟪b i, x⟫ * β (b i) y := by
      conv_lhs => rw [← b.sum_repr' x]
      change (AddMonoidHom.mk' (fun x => β x y) (fun x x' => hL x x' y)) (∑ i, ⟪b i, x⟫ • b i) = _
      rw [map_sum]
      simp [sL]
    have h2 : ⟪x, A y⟫ = ∑ i, β (b i) y * ⟪x, b i⟫ := by
      simp [A, inner_sum, inner_smul_right]
    rw [h1, h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm, mul_comm]
  refine ⟨A, hA, ?_⟩
  rw [← LinearMap.det_toMatrix b.toBasis]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.of_apply, hA]
  simp [OrthonormalBasis.repr_apply_apply]

private theorem integral_fourier_map_eq_neg_of_integrable (μ : Measure V) (χ : V → V → ℂ) (hμ : SelfDual μ χ) (e : V ≃ₜ W)
    (he : ∀ x y, e (x + y) = e x + e y) (β : W → W → ℝ)
    (hχ : ∀ x y, χ (e.symm x) (e.symm y) = ((𝐞 (β x y) : Circle) : ℂ))
    (Φ : W → ℂ) (hΦc : Continuous Φ) (hΦs : HasCompactSupport Φ)
    (hint : Integrable (fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂(μ.map e)) (μ.map e))
    (z : W) :
    ∫ y, (∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂(μ.map e)) * ((𝐞 (β y z) : Circle) : ℂ) ∂(μ.map e)
      = Φ (-z) := by
  have hme : MeasurableEmbedding e := e.measurableEmbedding
  have hmap : ∀ g : W → ℂ, ∫ w, g w ∂(μ.map e) = ∫ x, g (e x) ∂μ := fun g => hme.integral_map g
  have hχ' : ∀ x y, χ x y = ((𝐞 (β (e x) (e y)) : Circle) : ℂ) := fun x y => by
    simpa using hχ (e x) (e y)
  set F := fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂(μ.map e) with hFdef
  have hF : ∀ y, ∫ x, (Φ ∘ e) x * χ x y ∂μ = F (e y) := by
    intro y
    simp only [hFdef, hmap, Function.comp_apply, hχ']
  have hint' : Integrable (fun y => ∫ x, (Φ ∘ e) x * χ x y ∂μ) μ := by
    simp only [hF]
    exact hme.integrable_map_iff.mp hint
  have key := hμ.2 (Φ ∘ e) (hΦc.comp e.continuous) (hΦs.comp_homeomorph e) hint' (e.symm z)
  have hneg : e (-(e.symm z)) = -z := by
    have := map_neg (AddMonoidHom.mk' e he) (e.symm z)
    simpa using this
  simp only [hF, hχ', Homeomorph.apply_symm_apply, Function.comp_apply, hneg] at key
  rw [hmap]
  simp only [hFdef, hmap]
  exact key

private theorem false_of_degenerate_of_fourier_inversion (ν : Measure W) [ν.IsAddHaarMeasure] (β : W → W → ℝ)
    (hL : ∀ x x' y, β (x + x') y = β x y + β x' y) (hcL : ∀ y, Continuous fun x => β x y)
    (k : W) (hk : k ≠ 0) (hk0 : ∀ y, β k y = 0)
    (hP : ∀ Φ : W → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable (fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν) ν → ∀ z : W,
      ∫ y, (∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν) * ((𝐞 (β y z) : Circle) : ℂ) ∂ν = Φ (-z)) :
    False := by
  have hkpos : 0 < ‖k‖ := norm_pos_iff.mpr hk
  let bump : ContDiffBump (0 : W) := ⟨‖k‖ / 2, ‖k‖, by positivity, by linarith⟩
  let ψ : W → ℂ := fun x => ((bump x : ℝ) : ℂ)
  have hψc : Continuous ψ := Complex.continuous_ofReal.comp bump.continuous
  have hψs : HasCompactSupport ψ := bump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hψs' : HasCompactSupport (fun x => ψ (x + k)) := hψs.comp_homeomorph (Homeomorph.addRight k)
  let Φ : W → ℂ := fun x => ψ x - ψ (x + k)
  have hΦc : Continuous Φ := hψc.sub (hψc.comp (continuous_add_right k))
  have hΦs : HasCompactSupport Φ := hψs.sub hψs'
  have hzero : ∀ y, ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν = 0 := by
    intro y
    let g : W → ℂ := fun x => ψ x * ((𝐞 (β x y) : Circle) : ℂ)
    have hgc : Continuous g := by
      have := hcL y
      fun_prop
    have hg : Integrable g ν := hgc.integrable_of_hasCompactSupport hψs.mul_right
    have heq : (fun x => Φ x * ((𝐞 (β x y) : Circle) : ℂ)) = fun x => g x - g (x + k) := by
      funext x
      simp only [Φ, g, hL, hk0, add_zero]
      ring
    rw [heq, integral_sub hg (hg.comp_add_right k), integral_add_right_eq_self, sub_self]
  have hint : Integrable (fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν) ν := by
    simp only [hzero]
    exact integrable_zero _ _ _
  have key := hP Φ hΦc hΦs hint 0
  simp only [hzero, zero_mul, integral_zero, neg_zero] at key
  have h0 : bump 0 = 1 := bump.one_of_mem_closedBall (by simp; positivity)
  have h1 : bump k = 0 := by
    apply Function.notMem_support.mp
    rw [bump.support_eq]
    simp
    exact le_rfl
  simp [Φ, ψ, h0, h1] at key

private theorem measure_eq_sqrt_abs_det_smul_volume_of_inversion (ν : Measure W) [ν.IsAddHaarMeasure] (A : W →ₗ[ℝ] W)
    (hdet : LinearMap.det A ≠ 0)
    (hP : ∀ Φ : W → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable (fun y => ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν) ν → ∀ z : W,
      ∫ y, (∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν) * ((𝐞 ⟪A y, z⟫ : Circle) : ℂ) ∂ν = Φ (-z)) :
    ν = ENNReal.ofReal (Real.sqrt |LinearMap.det A|) • volume := by
  set s := ν.addHaarScalarFactor volume with hsdef
  have hs : 0 < s := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν volume
  have hν : ν = (s : ENNReal) • volume := by
    rw [← ENNReal.smul_def]
    exact Measure.isAddLeftInvariant_eq_smul ν volume
  let bump : ContDiffBump (0 : W) := ⟨1, 2, one_pos, one_lt_two⟩
  have h0 : bump 0 = 1 := bump.one_of_mem_closedBall (by simp; exact bump.rIn_pos.le)
  let Φ : W → ℂ := fun x => ((bump x : ℝ) : ℂ)
  have hΦs : HasCompactSupport Φ := bump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hΦd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ :=
    Complex.ofRealCLM.contDiff.comp (bump.contDiff (n := ⊤))
  let S : SchwartzMap W ℂ := hΦs.toSchwartzMap hΦd
  have hSΦ : (S : W → ℂ) = Φ := rfl
  let g : W → ℂ := 𝓕⁻ Φ
  have hgS : g = ⇑(𝓕⁻ S : SchwartzMap W ℂ) := by rw [SchwartzMap.fourierInv_coe, hSΦ]
  have hgi : Integrable g := by rw [hgS]; exact (𝓕⁻ S : SchwartzMap W ℂ).integrable
  have hgg : ∫ v, g v = 1 := by
    have h1 : 𝓕⁻ g 0 = ∫ v, g v := by simp [Real.fourierInv_eq]
    have h2 : 𝓕⁻ g 0 = Φ 0 := by
      rw [Real.fourierInv_eq_fourier_neg, hgS, ← SchwartzMap.fourier_coe,
        FourierInvPair.fourier_fourierInv_eq, hSΦ, neg_zero]
    rw [← h1, h2]
    simp [Φ, h0]
  have hAc : Continuous A := A.continuous_of_finiteDimensional
  have hAm : AEMeasurable A volume := hAc.measurable.aemeasurable
  have hmapA : (volume : Measure W).map A = ENNReal.ofReal |(LinearMap.det A)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet
  have hgim : Integrable g ((volume : Measure W).map A) := by
    rw [hmapA]
    exact hgi.smul_measure ENNReal.ofReal_ne_top
  have hgA : Integrable (fun y => g (A y)) volume :=
    (integrable_map_measure hgim.aestronglyMeasurable hAm).mp hgim
  have hinner : ∀ y, ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν = (s : ℝ) • g (A y) := by
    intro y
    show _ = (s : ℝ) • 𝓕⁻ Φ (A y)
    rw [hν, integral_smul_measure, ENNReal.coe_toReal, Real.fourierInv_eq]
    congr 1
    congr 1
    funext x
    rw [Circle.smul_def, smul_eq_mul, mul_comm]
  have hint : Integrable (fun y => ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν) ν := by
    simp only [hinner]
    rw [hν]
    exact (hgA.smul (s : ℝ)).smul_measure ENNReal.coe_ne_top
  have hcomp : ∫ y, g (A y) = (ENNReal.ofReal |(LinearMap.det A)⁻¹|).toReal • (1 : ℂ) := by
    rw [← integral_map hAm hgim.aestronglyMeasurable, hmapA, integral_smul_measure, hgg]
  have key := hP Φ hΦd.continuous hΦs hint 0
  simp only [hinner, inner_zero_right, AddChar.map_zero_eq_one, Circle.coe_one, mul_one] at key
  rw [hν, integral_smul_measure, integral_smul, hcomp, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (abs_nonneg _)] at key
  have hreal : (s : ℝ) * ((s : ℝ) * |(LinearMap.det A)⁻¹|) = 1 := by
    have h2 : Φ (-0) = 1 := by simp [Φ, h0]
    rw [h2] at key
    have := congrArg Complex.re key
    simp only [Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one] at this
    exact this
  have hdpos : 0 < |LinearMap.det A| := abs_pos.mpr hdet
  have hsq : (s : ℝ) ^ 2 = |LinearMap.det A| := by
    rw [abs_inv] at hreal
    field_simp at hreal
    nlinarith [hreal]
  rw [hν]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, ← hsq, Real.sqrt_sq s.coe_nonneg]

theorem dens_generic (μ : Measure V) (χ : V → V → ℂ) (hμ : SelfDual μ χ) (e : V ≃ₜ W)
    (he : ∀ x y, e (x + y) = e x + e y) (β : W → W → ℝ)
    (hχ : ∀ x y, χ (e.symm x) (e.symm y) = ((𝐞 (β x y) : Circle) : ℂ))
    (hL : ∀ x x' y, β (x + x') y = β x y + β x' y) (hR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hcL : ∀ y, Continuous fun x => β x y) (hcR : ∀ x, Continuous fun y => β x y)
    (hS : ∀ x y, β x y = β y x) (b : OrthonormalBasis ι ℝ W) :
    μ.map e = ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j => β (b i) (b j)).det|) • volume := by
  obtain ⟨A, hA, hdet⟩ := exists_linearMap_inner_eq_and_det_eq_gram_det β hL hR hcL hcR b
  have hP := fun Φ hc hs hi z => integral_fourier_map_eq_neg_of_integrable μ χ hμ e he β hχ Φ hc hs hi z
  haveI : μ.IsAddHaarMeasure := hμ.1
  haveI : (μ.map e).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μ (AddMonoidHom.mk' e he) e.continuous e.surjective
      e.isClosedEmbedding.tendsto_cocompact
  by_cases hd : (Matrix.of fun i j => β (b i) (b j)).det = 0
  · exfalso
    rw [← hdet] at hd
    obtain ⟨k, hkker, hk⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hd)
    have hk0 : ∀ y, β k y = 0 := fun y => by
      rw [hS, hA, LinearMap.mem_ker.mp hkker, inner_zero_right]
    exact false_of_degenerate_of_fourier_inversion (μ.map e) β hL hcL k hk hk0 hP
  · rw [← hdet] at hd ⊢
    apply measure_eq_sqrt_abs_det_smul_volume_of_inversion (μ.map e) A hd
    intro Φ hc hs hi z
    have hβ' : ∀ y z, ⟪A y, z⟫ = β y z := fun y z => by rw [hS, hA, real_inner_comm]
    simp only [← hA, hβ'] at hi ⊢
    exact hP Φ hc hs hi z

end PI.AprimeInfW.GenericDensity
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GrpHaarW
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

def UstdSub {n : ℕ} (ε : Fin n → Bool) (S : Finset (Fin n)) : Subgroup (Formalism.REAL.UJ ε) where
  carrier := {g | InStd S g}
  one_mem' := by
    intro i _ j
    show (1 : Matrix (Fin n) (Fin n) ℂ) j i = _
    rw [Matrix.one_apply]
  mul_mem' := by
    intro g h hg hh i hi j
    have e : (((g * h : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
        ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
          ((h : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := rfl
    show (((g * h : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) j i = _
    rw [e, Matrix.mul_apply]
    simp_rw [hh i hi]
    simp [hg i hi j]
  inv_mem' := by
    intro g hg i hi j
    have e : ((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) = ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ))⁻¹ := rfl
    have h1 : (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
        ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1 := Units.inv_mul _
    have h2 := congrFun (congrFun h1 j) i
    rw [Matrix.mul_apply] at h2
    simp_rw [hg i hi] at h2
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.one_apply] at h2
    show ((((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ) j i = _
    rw [e, h2]

def BlockHaarV : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (S : Finset (Fin n)) (k : ℕ), S.card = k →
    (∀ i ∈ S, ε i = true) → Formalism.MainNotions.S.Gauge.GaugeDens ε →
    ∃ (β : Type) (_ : Fintype β) (L₁ : EuclideanSpace ℝ β →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)
      (P₁ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ β) (ν : Measure (UstdSub ε S)) (r : ℝ)
      (e : EuclideanSpace ℝ β → ℝ) (hmem : ∀ y, expU ε (L₁ y) ∈ UstdSub ε S),
      (∀ z, P₁ (L₁ z) = z) ∧ (∀ M, InBlock ε S M → L₁ (P₁ M) = M) ∧ (∀ z, InBlock ε S (L₁ z)) ∧
      (∀ z, frob (L₁ z) = ‖z‖ ^ 2) ∧
      ν.IsMulLeftInvariant ∧ IsFiniteMeasure ν ∧ ν Set.univ ≠ 0 ∧ 0 < r ∧ Measurable e ∧ (∀ z, 0 ≤ e z) ∧
      ContinuousAt e 0 ∧ 0 < e 0 ∧ (ν Set.univ).toReal / e 0 = Formalism.MainNotions.S.UnitaryVolumeMass.volU k ∧
      Continuous (fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) ∧
      Set.InjOn (fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) (ball 0 r) ∧
      ∀ A ⊆ ball (0 : EuclideanSpace ℝ β) r, MeasurableSet A →
        ν ((fun y => (⟨expU ε (L₁ y), hmem y⟩ : UstdSub ε S)) '' A) = ∫⁻ y in A, ENNReal.ofReal (e y)

theorem grpHaarH_of (hBH : BlockHaarV) : GrpHaarH := by
  intro D X u' hb c S ι η _ _ L L₁ ctx hS
  obtain ⟨⟨ψ', hT, μinf, νinf, fibInf, hP⟩, hc, hL, hB⟩ := ctx
  have hgd : ∀ v, Formalism.MainNotions.S.Gauge.GaugeDens (X.B.I.ε v) := hP.2.2.2.1
  choose β hβ L1 P1 ν r e hmem h1 h2 h3 h4 hνL hνF hν0 hr hem hen hec he0 hrat hcont hinj hdens using
    fun v => hBH X.B.I.n (X.B.I.ε v) (S v) D.R.k (hc.1 v).1 (hc.1 v).2 (hgd v)
  letI : ∀ v, Fintype (β v) := hβ
  have hUJ : ∀ v, SecondCountableTopology (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => Formalism.REAL.instSecondCountableUJ _ _
  have : ∀ v, SecondCountableTopology (UstdSub (X.B.I.ε v) (S v)) := fun v =>
    TopologicalSpace.Subtype.secondCountableTopology ((UstdSub (X.B.I.ε v) (S v) : Set (Formalism.REAL.UJ (X.B.I.ε v))))
  have : ∀ v, OpensMeasurableSpace (UstdSub (X.B.I.ε v) (S v)) := fun v => inferInstance
  have : OpensMeasurableSpace (∀ v, UstdSub (X.B.I.ε v) (S v)) := Pi.opensMeasurableSpace
  have : ∀ v, IsFiniteMeasure (ν v) := hνF
  have : ∀ v, (ν v).IsMulLeftInvariant := hνL
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have : SecondCountableTopology (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    PI.AprimeInfT.secondCountable_HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J
  obtain ⟨hTyb, hTyn⟩ := coord_facts L₁ (fun v M => InBlock (X.B.I.ε v) (S v) M) L1 P1 h1 h2 h3 h4
    (fun y v => hB.1 y v) (fun y => hB.2.1 y) (fun M hM => hB.2.2 M hM)
  set Ty : EuclideanSpace ℝ η →ₗ[ℝ] (∀ v, EuclideanSpace ℝ (β v)) :=
    LinearMap.pi fun v => (P1 v).comp ((LinearMap.proj v).comp L₁) with hTyd
  have hTym := PI.AprimeInfG.measurePreserving_of_normSq Ty hTyb hTyn
  let Tye : EuclideanSpace ℝ η ≃ᵐ (∀ v, EuclideanSpace ℝ (β v)) :=
    (LinearEquiv.ofBijective Ty hTyb).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hTye : MeasurePreserving Tye volume (Measure.pi fun _ => volume) := hTym
  have hTyv : ∀ y v, L1 v (Ty y v) = L₁ y v := fun y v => h2 v _ (hB.1 y v)

  let ψf : (∀ v, UstdSub (X.B.I.ε v) (S v)) →
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') :=
    fun g => ⟨X.toInf hb (c * (fun v => ((g v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) * c⁻¹),
      (hc.2 _).2 fun v => (g v).2⟩
  let ψm : (∀ v, UstdSub (X.B.I.ε v) (S v)) →ₙ*
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') :=
    { toFun := ψf
      map_mul' := fun g h => by
        apply Subtype.ext
        show toInfHom X hb _ = toInfHom X hb _ * toInfHom X hb _
        rw [← map_mul]
        congr 1
        have : (fun v => (((g * h) v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) =
            (fun v => ((g v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) *
              (fun v => ((h v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) := funext fun v => rfl
        rw [this]
        group }
  have hψc : Continuous ψm := by
    apply Continuous.subtype_mk
    exact (MassDataMassesW.continuous_toInf X hb).comp ((continuous_const.mul (continuous_pi fun v =>
      continuous_subtype_val.comp (continuous_apply v))).mul continuous_const)
  have hψi : Function.Injective ψm := by
    intro g h he
    have e1 := toInf_injective X hb (congrArg Subtype.val he)
    have e2 : (fun v => ((g v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) =
        (fun v => ((h v : UstdSub (X.B.I.ε v) (S v)) : Formalism.REAL.UJ (X.B.I.ε v))) := by simpa using e1
    funext v
    exact Subtype.ext (congrFun e2 v)
  have hψs : Function.Surjective ψm := by
    intro hh
    obtain ⟨s, hs⟩ := PI.AprimeInfU.toInf_surjective X hb MassDataMassesW.splitIso_holds
      (hh : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)
    have hmemS : X.toInf hb (c * (c⁻¹ * s * c) * c⁻¹) ∈
        MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u') := by
      rw [show c * (c⁻¹ * s * c) * c⁻¹ = s by group, hs]
      exact hh.2
    have hstd := (hc.2 _).1 hmemS
    refine ⟨fun v => ⟨(c⁻¹ * s * c) v, hstd v⟩, Subtype.ext ?_⟩
    show X.toInf hb (c * (c⁻¹ * s * c) * c⁻¹) = hh
    rw [show c * (c⁻¹ * s * c) * c⁻¹ = s by group, hs]

  let Φ : ∀ v, EuclideanSpace ℝ (β v) → UstdSub (X.B.I.ε v) (S v) :=
    fun v z => ⟨expU (X.B.I.ε v) (L1 v z), hmem v z⟩
  have hχ : ∀ y, (⟨chiOf X hb c L₁ y, hS y⟩ :
      MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u')) =
      ψm (fun v => Φ v (Ty y v)) := by
    intro y
    apply Subtype.ext
    show chiOf X hb c L₁ y = X.toInf hb (c * (fun v => expU (X.B.I.ε v) (L1 v (Ty y v))) * c⁻¹)
    unfold chiOf
    simp_rw [hTyv]
  set rr := (insert 1 (Finset.univ.image r)).min' ⟨1, Finset.mem_insert_self _ _⟩ with hrr
  have hrr0 : 0 < rr := by
    have hm := Finset.min'_mem (insert 1 (Finset.univ.image r)) ⟨1, Finset.mem_insert_self _ _⟩
    rcases Finset.mem_insert.1 hm with e' | e'
    · rw [hrr, e']; norm_num
    · obtain ⟨v, -, hv⟩ := Finset.mem_image.1 e'
      rw [hrr, ← hv]; exact hr v
  have hrrv : ∀ v, rr ≤ r v := fun v =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem r (Finset.mem_univ v)))
  have hTyle : ∀ y v, ‖Ty y v‖ ≤ ‖y‖ := by
    intro y v
    have : ‖Ty y v‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [← hTyn y]
      exact Finset.single_le_sum (f := fun v => ‖Ty y v‖ ^ 2) (fun v _ => sq_nonneg _) (Finset.mem_univ v)
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  have hT0 : ∀ v, Ty 0 v = 0 := fun v => by simp
  have hνu : (Measure.pi ν).map ψm Set.univ = ∏ v, ν v Set.univ := by
    rw [Measure.map_apply hψc.measurable MeasurableSet.univ, Set.preimage_univ, Measure.pi_univ]
  refine ⟨(Measure.pi ν).map ψm, rr, fun y => ∏ v, e v (Ty y v),
    isMulLeftInvariant_map ψm hψc.measurable hψs, inferInstance, ?_, ?_, hrr0, ?_, ?_, ?_, ?_⟩
  · rw [hνu]
    exact Finset.prod_ne_zero_iff.2 fun v _ => hν0 v
  · rw [hνu]
    exact ENNReal.prod_ne_top fun v _ => measure_ne_top _ _
  · refine tendsto_finsetProd _ fun v _ => ?_
    have hv : ContinuousAt (fun y : EuclideanSpace ℝ η => Ty y v) 0 :=
      ((continuous_apply v).comp Ty.continuous_of_finiteDimensional).continuousAt
    have hd : ContinuousAt (e v) (Ty 0 v) := by rw [hT0 v]; exact hec v
    have hdv := ContinuousAt.comp (f := fun y : EuclideanSpace ℝ η => Ty y v) hd hv
    exact hdv
  · simp only [hT0]
    exact Finset.prod_pos fun v _ => he0 v
  · rw [hνu, ENNReal.toReal_prod]
    simp only [hT0]
    rw [← Finset.prod_div_distrib]
    simp only [hrat, Finset.prod_const, Finset.card_univ]
  · intro s hs hsr
    have hB' : Ty '' ball 0 s ⊆ Set.univ.pi fun v => ball 0 (r v) := by
      rintro _ ⟨y, hy, rfl⟩ v -
      exact mem_ball_zero_iff.2 (((hTyle y v).trans_lt (mem_ball_zero_iff.1 hy)).trans_le (hsr.trans (hrrv v)))
    have hΦc : Continuous (fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) :=
      continuous_pi fun v => (hcont v).comp (continuous_apply v)
    have hΦi : Set.InjOn (fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v))
        (Set.univ.pi fun v => ball 0 (r v)) := by
      intro z hz z' hz' he'
      funext v
      exact hinj v (hz v (Set.mem_univ v)) (hz' v (Set.mem_univ v)) (congr_fun he' v)
    have hTA : MeasurableSet (Tye '' ball 0 s) := Tye.measurableSet_image.2 measurableSet_ball
    have hAi : MeasurableSet ((fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) '' (Tye '' ball 0 s)) :=
      hTA.image_of_continuousOn_injOn hΦc.continuousOn (hΦi.mono hB')
    have himg : (fun y => (⟨chiOf X hb c L₁ y, hS y⟩ :
        MulAction.stabilizer (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (Y0 X u'))) '' ball 0 s =
        ψm '' ((fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) '' (Tye '' ball 0 s)) := by
      rw [Set.image_image, Set.image_image]
      exact Set.image_congr fun y _ => hχ y
    have hmeasH : MeasurableSet (ψm '' ((fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) ''
        (Tye '' ball 0 s))) := by
      have e3 : ψm '' ((fun z : ∀ v, EuclideanSpace ℝ (β v) => fun v => Φ v (z v)) '' (Tye '' ball 0 s)) =
          (fun y => ψm (fun v => Φ v (Ty y v))) '' ball 0 s := by
        rw [Set.image_image, Set.image_image]
        rfl
      rw [e3]
      refine measurableSet_ball.image_of_continuousOn_injOn ?_ ?_
      · exact (hψc.comp (hΦc.comp Ty.continuous_of_finiteDimensional)).continuousOn
      · intro y hy y' hy' he'
        have e4 := hψi he'
        have e5 : Ty y = Ty y' := hΦi (hB' ⟨y, hy, rfl⟩) (hB' ⟨y', hy', rfl⟩) e4
        exact hTyb.1 e5
    rw [himg, Measure.map_apply hψc.measurable hmeasH, hψi.preimage_image,
      PI.AprimeInfG.pi_chart_dens ν (fun _ => volume) Φ (fun v => (hcont v).measurable) (fun v => ball 0 (r v))
        (fun v => measurableSet_ball) hinj e hem hdens (Tye '' ball 0 s) hB' hTA hAi,
      ← hTye.setLIntegral_comp_emb Tye.measurableEmbedding]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_prod_of_nonneg fun v _ => hen v _]
    rfl

end PI.AprimeInfW
end
end

