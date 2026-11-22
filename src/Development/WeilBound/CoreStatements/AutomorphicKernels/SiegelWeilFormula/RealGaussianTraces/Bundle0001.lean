import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.SecondCountableTens
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Integr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0001
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCJ

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.EqOfBox
section
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

open Topology in
theorem eq_of_box {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X)
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] (B : Set X) (hB : IsOpen B) (g1 g2 : X → ℂ)
    (h1 : ContinuousOn g1 B) (h2 : ContinuousOn g2 B) (t : X) (ht : t ∈ B)
    (hbox : ∀ U ∈ 𝓝 t, ∃ S, IsCompact S ∧ S ⊆ U ∧ S ⊆ B ∧ S ∈ 𝓝 t ∧ ∫ x in S, g1 x ∂ν = ∫ x in S, g2 x ∂ν) :
    g1 t = g2 t := by
  by_contra hne
  set c := g1 t - g2 t with hc
  have hc0 : c ≠ 0 := sub_ne_zero.mpr hne
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  have hcont : ContinuousAt (fun x => g1 x - g2 x) t := (h1.sub h2).continuousAt (hB.mem_nhds ht)
  have hU : {x | ‖(g1 x - g2 x) - c‖ < ‖c‖ / 2} ∈ 𝓝 t := by
    have := hcont.eventually (Metric.ball_mem_nhds c (by positivity : (0 : ℝ) < ‖c‖ / 2))
    filter_upwards [this] with x hx
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  obtain ⟨S, hSc, hSU, hSB, hSt, hint⟩ := hbox _ hU
  have hSfin : ν S < ⊤ := hSc.measure_lt_top
  have hSpos : 0 < ν S := Measure.measure_pos_of_mem_nhds (μ := ν) hSt
  have hSr : 0 < ν.real S := ENNReal.toReal_pos hSpos.ne' hSfin.ne
  have hi1 : IntegrableOn g1 S ν := (h1.mono hSB).integrableOn_compact hSc
  have hi2 : IntegrableOn g2 S ν := (h2.mono hSB).integrableOn_compact hSc
  have hi12 : IntegrableOn (fun x => g1 x - g2 x) S ν := hi1.sub hi2
  have hic : IntegrableOn (fun _ : X => c) S ν := integrableOn_const hSfin.ne
  have h0 : ∫ x in S, (g1 x - g2 x - c) ∂ν = -(ν.real S • c) := by
    rw [integral_sub hi12 hic, integral_sub hi1 hi2, hint, sub_self, setIntegral_const, zero_sub]
  have hle : ‖∫ x in S, (g1 x - g2 x - c) ∂ν‖ ≤ ‖c‖ / 2 * ν.real S :=
    norm_setIntegral_le_of_norm_le_const hSfin (fun x hx => (hSU hx).le)
  rw [h0, norm_neg, norm_smul, Real.norm_of_nonneg hSr.le] at hle
  nlinarith

end PositivityTheory.SiegelWeilFormula.GReal
end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.ExistsSchwartzPolyGauss
section
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal ComplexOrder

private theorem hasTemperateGrowth_evX_comp_clm {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {M n : ℕ}
    (L : W →L[ℝ] (Fin M → Fin n → ℂ)) (k : Fin M × Fin n × Bool) :
    Function.HasTemperateGrowth
      (fun w => if k.2.2 = true then star (L w k.1 k.2.1) else L w k.1 k.2.1) := by
  obtain ⟨a, i, b⟩ := k
  let ℓ : W →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin M => Fin n → ℂ) a).comp L)
  have hℓ : ∀ w, ℓ w = L w a i := fun w => rfl
  cases b
  · have h : (fun w => if false = true then star (L w a i) else L w a i) = ⇑ℓ := by
      funext w
      simp [hℓ]
    rw [h]
    exact ℓ.hasTemperateGrowth
  · have h : (fun w => if true = true then star (L w a i) else L w a i) =
        ⇑(Complex.conjCLE.toContinuousLinearMap.comp ℓ) := by
      funext w
      simp [hℓ]
    rw [h]
    exact (Complex.conjCLE.toContinuousLinearMap.comp ℓ).hasTemperateGrowth

theorem hasTemperateGrowth_evX {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {M n : ℕ}
    (L : W →L[ℝ] (Fin M → Fin n → ℂ)) (P : PX M n) :
    Function.HasTemperateGrowth (fun w => evX P (L w)) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : (fun w => evX (MvPolynomial.C a : PX M n) (L w)) = fun _ => a := by
      funext w
      simp [evX]
    rw [h]
    exact Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have h : (fun w => evX (p + q : PX M n) (L w)) =
        (fun w => evX p (L w)) + (fun w => evX q (L w)) := by
      funext w
      simp [evX]
    rw [h]
    exact hp.add hq
  | mul_X p k hp =>
    have h : (fun w => evX (p * MvPolynomial.X k : PX M n) (L w)) =
        (fun w => evX p (L w)) *
          (fun w => if k.2.2 = true then star (L w k.1 k.2.1) else L w k.1 k.2.1) := by
      funext w
      simp [evX]
    rw [h]
    exact hp.mul (hasTemperateGrowth_evX_comp_clm L k)

private theorem exists_schwartz_prod_gs {ι : Type} [Fintype ι] {M n : ℕ} (c : ι → ℝ)
    (hc : ∀ i, 0 < c i) :
    ∃ g : SchwartzMap (ι → Fin M → Fin n → ℂ) ℂ, ∀ x, g x = ∏ i, gs (c i) (x i) := by
  let pr : ι → Fin M → Fin n → ((ι → Fin M → Fin n → ℂ) →L[ℝ] ℂ) := fun i a j =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin M => Fin n → ℂ) a).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => Fin M → Fin n → ℂ) i))
  have hpr : ∀ i a j x, pr i a j x = x i a j := fun _ _ _ _ => rfl
  let re3 : ι → Fin M → Fin n → ((ι → Fin M → Fin n → ℂ) →L[ℝ] ℝ) := fun i a j =>
    Complex.reCLM.comp (pr i a j)
  let im3 : ι → Fin M → Fin n → ((ι → Fin M → Fin n → ℂ) →L[ℝ] ℝ) := fun i a j =>
    Complex.imCLM.comp (pr i a j)
  have hre : ∀ i a j x, re3 i a j x = (x i a j).re := fun _ _ _ _ => rfl
  have him : ∀ i a j x, im3 i a j x = (x i a j).im := fun _ _ _ _ => rfl
  let B : (ι → Fin M → Fin n → ℂ) →L[ℝ] (ι → Fin M → Fin n → ℂ) →L[ℝ] ℝ :=
    ∑ i, ∑ a, ∑ j, (-c i) • ((re3 i a j).smulRight (re3 i a j) + (im3 i a j).smulRight (im3 i a j))
  have hB : ∀ x, B x x = -∑ i, c i * ∑ a, ∑ j, ‖x i a j‖ ^ 2 := by
    intro x
    simp only [B, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply, hre, him, smul_eq_mul]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hneg : ∀ x, x ≠ 0 → B x x < 0 := by
    intro x hx
    rw [hB, neg_lt_zero]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hi
    obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
    apply Finset.sum_pos' (fun i _ => mul_nonneg (hc i).le (by positivity)) ⟨i, Finset.mem_univ _, ?_⟩
    apply mul_pos (hc i)
    apply Finset.sum_pos' (fun _ _ => by positivity) ⟨a, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos' (fun _ _ => by positivity) ⟨j, Finset.mem_univ _, ?_⟩
    exact pow_pos (norm_pos_iff.mpr (by simpa using hj)) 2
  obtain ⟨g, hg⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_exp_diag B hneg
  refine ⟨g, fun x => ?_⟩
  rw [hg, hB, Complex.ofReal_exp]
  simp only [gs]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_neg_distrib]

theorem exists_schwartz_polyGauss {ι : Type} [Fintype ι] {M n : ℕ} (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (P : ι → PX M n) :
    ∃ f : SchwartzMap (ι → Fin M → Fin n → ℂ) ℂ, ∀ x, f x = ∏ i, (evX (P i) (x i) * gs (c i) (x i)) := by
  obtain ⟨g, hg⟩ := exists_schwartz_prod_gs (M := M) (n := n) c hc
  have hbase : ∀ i, Function.HasTemperateGrowth
      (fun x : ι → Fin M → Fin n → ℂ => evX (P i) (x i)) := fun i =>
    hasTemperateGrowth_evX (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => Fin M → Fin n → ℂ) i) (P i)
  have hp : Function.HasTemperateGrowth
      (fun x : ι → Fin M → Fin n → ℂ => ∏ i, evX (P i) (x i)) := by
    have := Finset.prod_induction (s := Finset.univ)
      (fun i => fun x : ι → Fin M → Fin n → ℂ => evX (P i) (x i))
      (fun f : (ι → Fin M → Fin n → ℂ) → ℂ => f.HasTemperateGrowth) (fun _ _ h1 h2 => h1.mul h2)
      (Function.HasTemperateGrowth.const 1) (fun i _ => hbase i)
    have h : (∏ i, fun x : ι → Fin M → Fin n → ℂ => evX (P i) (x i)) =
        fun x => ∏ i, evX (P i) (x i) := by
      funext x
      simp [Finset.prod_apply]
    rw [h] at this
    exact this
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x => ∏ i, evX (P i) (x i)) g, fun x => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply hp, hg, smul_eq_mul, Finset.prod_mul_distrib]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in
theorem isSchwartzInf_comp {ι : Type} [Fintype ι] {M n : ℕ}
    (e0 : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ+ (ι → Fin M → Fin n → ℂ))
    (f : SchwartzMap (ι → Fin M → Fin n → ℂ) ℂ) : IsSchwartzInf (fun X => f (e0 X)) := by
  intro N e he hes
  let A : (Fin N → ℝ) ≃+ (ι → Fin M → Fin n → ℂ) := e.symm.trans e0.toAddEquiv
  have hA : Continuous A := e0.continuous.comp hes
  have hAs : Continuous A.symm := he.comp e0.symm.continuous
  let L := A.toRealLinearEquiv hA hAs
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f, fun x => ?_⟩
  rfl

end PositivityTheory.SiegelWeilFormula.GReal
end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.TraceAdd
section
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GReal

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula.Gen
open scoped TensorProduct Matrix NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (y : E) : σ (σ y) = y := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2, hCM.2.2.2, star_star]

theorem sig_nt (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) : ∃ x, σ x ≠ x := by
  by_contra h
  push Not at h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hc := hCM.2.1.isComplex (InfinitePlace.mk τ)
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff] at hc
  apply hc
  ext x
  simp only [ComplexEmbedding.conjugate_coe_eq]
  have := hCM.2.2.2 τ x
  rw [h x] at this
  exact this.symm

theorem trace_add (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (z : Ainf F ⊗[F] E) :
    algebraMap (Ainf F) (Ainf F ⊗[F] E) (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) = z + sigR (Ainf F) σ z := by
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; omega)
  exact Formalism.L2.Fam.ThC.alg_trace_gen σ
    (PI.OmLocU.SdB.trace_eq_add σ (sig_sig σ hCM) (sig_nt σ hCM) hCM.2.2.1) z

end PositivityTheory.SiegelWeilFormula.GReal
end
end

