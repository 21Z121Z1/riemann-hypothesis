import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0038
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralSelfDualEqAdelicFourier
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0053

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdeleHaarProductDecompositionStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adele_haar_product_decomposition : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] (m : Measure (ι → AF F)) (μ₁ : Measure (ι → Ainf F)) (μ₂ : Measure (ι → Af F)), m.IsAddHaarMeasure → μ₁.IsAddHaarMeasure → μ₂.IsAddHaarMeasure → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ m.map (fun y : ι → AF F => ((fun i => (y i).1, fun i => (y i).2) : (ι → Ainf F) × (ι → Af F))) = c • μ₁.prod μ₂ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM.map_split_eq_smul_prod | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM.map_split_eq_smul_prod | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM.map_split_eq_smul_prod <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanFrameKTypeDecomposition
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal NNReal Topology

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.DilU

open GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Dil

section H
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

def mulHomeo (t : R) (ht : IsUnit t) : R ≃ₜ R where
  toFun y := t * y
  invFun y := (ht.unit⁻¹ : Rˣ) * y
  left_inv y := by
    change ((ht.unit⁻¹ : Rˣ) : R) * (t * y) = y
    rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
  right_inv y := by
    change t * (((ht.unit⁻¹ : Rˣ) : R) * y) = y
    rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

def mulPiU (ι : Type) (t : R) (ht : IsUnit t) : (ι → R) ≃ᵐ (ι → R) :=
  MeasurableEquiv.piCongrRight fun _ => (mulHomeo R t ht).toMeasurableEquiv

theorem map_mulPiU {ι : Type} [Fintype ι] (lam : Measure R) [SigmaFinite lam] (t : R) (ht : IsUnit t)
    (c : ℝ≥0) (h : lam.map (fun y => t * y) = c • lam) :
    (Measure.pi fun _ : ι => lam).map (mulPiU R ι t ht) =
      (c ^ Fintype.card ι) • Measure.pi fun _ : ι => lam :=
  pi_map_scale lam (fun y => t * y) (continuous_const.mul continuous_id).measurable c h

omit [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R]
  [T2Space R] [MeasurableSpace R] [BorelSpace R] in
theorem half_trace_tmul (σ : E →ₐ[F] E) (hσ : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (s : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (s ⊗ₜ[F] (1 : E)) = s := by
  have e : s ⊗ₜ[F] (1 : E) = algebraMap R (R ⊗[F] E) s := by
    simp [Algebra.TensorProduct.algebraMap_apply]
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← (map_ofNat (algebraMap F R) 2), ← map_mul]
    norm_num
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have hc : Fintype.card (Fin (Module.finrank F E)) = 2 := by
    rw [Fintype.card_fin, hσ.2.2.1]
  rw [e, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R (Module.finBasis F E)), hc,
    two_nsmul, ← two_mul, ← mul_assoc, h2, one_mul]

theorem coordHerm_map_unit (σ : E →ₐ[F] E) (hσ : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) [lam.IsAddHaarMeasure] (t : R) (ht : IsUnit t) (c : ℝ≥0)
    (h : lam.map (fun y => t * y) = c • lam) (τ : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ 1 → HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ 1) (hτm : Measurable τ)
    (hτ : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i j =
      algebraMap R (R ⊗[F] E) t * (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i j) :
    (coordHerm R σ b lam 1).map τ = c • coordHerm R σ b lam 1 := by
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, -, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ R d b lam ‹_›
  haveI := hK
  haveI := hH 1
  set φ : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ 1 → (Fin 1 → R) × ({p : Fin 1 × Fin 1 // p.1 < p.2} → R ⊗[F] E) :=
    fun S => ((fun i : Fin 1 => algebraMap F R (1 / 2) *
          Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i i)),
        (fun p : {p : Fin 1 × Fin 1 // p.1 < p.2} => (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) p.1.1 p.1.2))
    with hφ
  set Q : Measure ({p : Fin 1 × Fin 1 // p.1 < p.2} → R ⊗[F] E) := Measure.pi fun _ => coordK R b lam with hQ
  set P := (Measure.pi fun _ : Fin 1 => lam).prod Q with hP
  have hν : coordHerm R σ b lam 1 = Measure.comap φ P := rfl
  have hemp : ∀ p : {p : Fin 1 × Fin 1 // p.1 < p.2}, False := fun p =>
    absurd p.2 (by rw [Subsingleton.elim p.1.1 p.1.2]; exact lt_irrefl _)
  have hcond : Function.Injective φ ∧ ∀ s, MeasurableSet s → NullMeasurableSet (φ '' s) P := by
    by_contra hc
    have h0 : coordHerm R σ b lam 1 = 0 := by
      rw [hν, Measure.comap, dif_neg hc]
    have := isOpen_univ.measure_pos (coordHerm R σ b lam 1) Set.univ_nonempty
    simp [h0] at this
  have hs : Function.Surjective φ := by
    rintro ⟨y, w⟩
    refine ⟨hermScal R σ (y 0), Prod.ext ?_ ?_⟩
    · funext i
      rw [Subsingleton.elim i 0]
      exact half_trace_tmul R σ hσ (y 0)
    · funext p
      exact (hemp p).elim
  have hD : P.map ((mulPiU R (Fin 1) t ht).prodCongr (MeasurableEquiv.refl _)) = c • P := by
    have e := Measure.map_prod_map (Measure.pi fun _ : Fin 1 => lam) Q (mulPiU R (Fin 1) t ht).measurable
      (measurable_id)
    rw [map_mulPiU R lam t ht c h, Measure.map_id] at e
    simp only [Fintype.card_fin, pow_one] at e
    rw [Measure.prod_smul_left] at e
    exact e.symm
  rw [hν]
  refine map_comap_scale φ P τ hτm _ c hs hcond.1 hcond.2 ?_ hD
  intro S
  refine Prod.ext ?_ ?_
  · funext i
    change algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) _ =
      t * (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) _)
    rw [hτ, ← Algebra.smul_def t, map_smul, smul_eq_mul]
    ring
  · funext p
    exact (hemp p).elim

end H

theorem coordHerm_map_ainf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ t : Ainf F, IsUnit t → ∀ c : ℝ≥0, lam.map (fun y => t * y) = c • lam → ∀ τ : HermR (Ainf F) σ 1 → HermR (Ainf F) σ 1, Measurable τ → (∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j = algebraMap (Ainf F) (Ainf F ⊗[F] E) t * (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)) i j) → (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam 1).map τ = c • GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b lam 1 := by
  intro F E _ _ _ _ _ σ hσ d b lam hlam t ht c h τ hτm hτ
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  exact coordHerm_map_unit (Ainf F) σ hσ b lam t ht c h τ hτm hτ

end GlobalTheory.CompanionTheory.SW.DilU
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIntegrableOfIsSchwartzBruhat
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiInt

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.FouCoord GroundTheory.Automorphic.GJMatrix
open scoped NNReal

theorem continuous_integrable_of_isSchwartzBruhat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (dx : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), dx.IsAddHaarMeasure → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ, IsSchwartzBruhat Φ → Continuous Φ ∧ Integrable Φ dx := by
  intro F E _ _ _ _ _ σ hCM M dx hdx Φ hΦ
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  obtain ⟨h1, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := h1
  haveI := hBor 1 M
  have hf := (isSchwartzBruhat_iff b Φ).1 hΦ
  let e := crd (AF F) b M
  have hcomp : (Φ ∘ e.symm) ∘ e = Φ := by
    funext X
    simp
  have hcont : Continuous Φ := by
    have h : Continuous ((Φ ∘ e.symm) ∘ e) :=
      (continuous_of_mem_schwartzBruhatPi hf).comp e.continuous
    rwa [hcomp] at h
  refine ⟨hcont, ?_⟩
  haveI : LocallyCompactSpace (Fin 1 → Fin M → AF F ⊗[F] E) :=
    e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Fin 1 → Fin M → AF F ⊗[F] E) :=
    e.toHomeomorph.secondCountableTopology
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, dx = c • mu0 e := ⟨_, Measure.isAddLeftInvariant_eq_smul dx (mu0 e)⟩
  have hI : Integrable Φ (mu0 e) := by
    rw [mu0, (measurableEmbedding_symm e).integrable_map_iff]
    exact integrable_of_mem_schwartzBruhatPi hf
  rw [hc]
  exact hI.smul_measure_nnreal

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoordinateMeasureScalingTensor
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.HaarScale

theorem unit_mul_map_haar : ∀ (F : Type) [Field F] [NumberField F] (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → ∀ (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ t : Ainf F, IsUnit t → lam.map (fun y => t * y) = (∏ w, ‖e t w‖₊)⁻¹ • lam := by
  intro F _ _ e he lam hlam t ht
  classical
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hc : Continuous e := he.continuous
  let h : Ainf F ≃ₜ (InfinitePlace F → ℝ) := he.homeomorph e
  have hcs : Continuous e.symm := by
    have : (e.symm : (InfinitePlace F → ℝ) → Ainf F) = h.symm := by
      funext y
      have h1 : e (h.symm y) = y := h.apply_symm_apply y
      exact e.symm_apply_eq.2 h1.symm
    rw [this]; exact h.symm.continuous
  have hm : Measurable e := hc.measurable
  have hms : Measurable e.symm := hcs.measurable
  have hmul : Measurable (fun y : Ainf F => t * y) := by
    have : (fun y : Ainf F => t * y) = fun y => e.symm (e t * e y) := by
      funext y; simp
    rw [this]
    exact hcs.measurable.comp (hm.const_mul _)
  obtain ⟨D, hD⟩ : ∃ D : InfinitePlace F → ℝ, D = e t := ⟨_, rfl⟩
  have hDu : IsUnit D := hD ▸ ht.map e
  have hD0 : ∀ w, D w ≠ 0 := fun w => by
    obtain ⟨u, hu⟩ := hDu
    have h1 : D w * (u⁻¹ : (InfinitePlace F → ℝ)ˣ).1 w = 1 := by
      have := congrFun (u.mul_inv) w
      rw [hu] at this
      simpa using this
    exact left_ne_zero_of_mul_eq_one h1
  haveI hμ : (lam.map e).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map lam e.toAddEquiv hc hcs
  let L : (InfinitePlace F → ℝ) →ₗ[ℝ] (InfinitePlace F → ℝ) := Matrix.toLin' (Matrix.diagonal D)
  have hL : ∀ x, L x = D * x := fun x => by
    funext w
    simp [L, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  have hdet : LinearMap.det L = ∏ w, D w := by
    simp [L, LinearMap.det_toLin', Matrix.det_diagonal]
  have hdet0 : LinearMap.det L ≠ 0 := by
    rw [hdet]; exact Finset.prod_ne_zero_iff.2 fun w _ => hD0 w
  have hscale := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := lam.map e) hdet0
  have hconst : ENNReal.ofReal |(LinearMap.det L)⁻¹| = (((∏ w, ‖e t w‖₊)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    have : |(LinearMap.det L)⁻¹| = (((∏ w, ‖e t w‖₊)⁻¹ : ℝ≥0) : ℝ) := by
      rw [hdet, abs_inv, Finset.abs_prod]
      push_cast
      simp [hD]
    rw [this, ENNReal.ofReal_coe_nnreal]
  have key : (lam.map (fun y => t * y)).map e = (∏ w, ‖e t w‖₊)⁻¹ • lam.map e := by
    rw [Measure.map_map hm hmul, ENNReal.smul_def, ← hconst, ← hscale,
      Measure.map_map L.continuous_of_finiteDimensional.measurable hm]
    congr 1
    funext y
    simp [hL, hD]
  have back : ∀ ν : Measure (Ainf F), (ν.map e).map e.symm = ν := fun ν => by
    rw [Measure.map_map hms hm]
    have : (e.symm ∘ e : Ainf F → Ainf F) = id := by funext y; simp
    rw [this, Measure.map_id]
  rw [← back (lam.map fun y => t * y), key, Measure.map_smul, back]

end GlobalTheory.CompanionTheory.HaarScale
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.EulerFactorStandardMeasureIdentity
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct

private theorem abs_finset_prod_sub_one_le {κ : Type} (f : κ → ℝ) (s : Finset κ) :
    |(∏ v ∈ s, f v) - 1| ≤ (∏ v ∈ s, (1 + |f v - 1|)) - 1 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 : |f a| ≤ 1 + |f a - 1| := by
      have := abs_sub_abs_le_abs_sub (f a) 1
      rw [abs_one] at this
      linarith
    have hfa : f a * (∏ v ∈ s, f v) - 1 = f a * ((∏ v ∈ s, f v) - 1) + (f a - 1) := by ring
    rw [hfa]
    calc |f a * ((∏ v ∈ s, f v) - 1) + (f a - 1)|
        ≤ |f a| * |(∏ v ∈ s, f v) - 1| + |f a - 1| := by
          rw [← abs_mul]
          exact abs_add_le _ _
      _ ≤ (1 + |f a - 1|) * ((∏ v ∈ s, (1 + |f v - 1|)) - 1) + |f a - 1| := by
          gcongr
      _ = (1 + |f a - 1|) * (∏ v ∈ s, (1 + |f v - 1|)) - 1 := by ring

theorem abs_tprod_sub_one_le {κ : Type} (f : κ → ℝ)
    (hs : Summable (fun v => |f v - 1|)) :
    |(∏' v, f v) - 1| ≤ Real.exp (∑' v, |f v - 1|) - 1 := by
  have hm : Multipliable f := by
    have h := multipliable_one_add_of_summable (f := fun v => f v - 1)
      (by simpa only [Real.norm_eq_abs] using hs)
    simpa only [add_sub_cancel] using h
  have ht : Filter.Tendsto (fun s : Finset κ => ∏ v ∈ s, f v) Filter.atTop
      (nhds (∏' v, f v)) := hm.hasProd
  have hb : ∀ s : Finset κ, |(∏ v ∈ s, f v) - 1| ≤ Real.exp (∑' v, |f v - 1|) - 1 := by
    intro s
    refine (abs_finset_prod_sub_one_le f s).trans ?_
    gcongr ?_ - 1
    calc ∏ v ∈ s, (1 + |f v - 1|) ≤ ∏ v ∈ s, Real.exp (|f v - 1|) := by
          apply Finset.prod_le_prod
          · intro i _
            positivity
          · intro i _
            have := Real.add_one_le_exp (|f i - 1|)
            linarith
      _ = Real.exp (∑ v ∈ s, |f v - 1|) := (Real.exp_sum s _).symm
      _ ≤ Real.exp (∑' v, |f v - 1|) :=
          Real.exp_le_exp.mpr (hs.sum_le_tsum s (fun i _ => abs_nonneg _))
  exact le_of_tendsto' ((continuous_abs.tendsto _).comp (ht.sub_const 1)) hb

theorem tendsto_tprod_compl_one {ι : Type} (f : ι → ℝ)
    (hs : Summable (fun v => |f v - 1|)) :
    Filter.Tendsto (fun S : Finset ι => ∏' v : {v // v ∉ S}, f v) Filter.atTop (nhds 1) := by
  have hb : ∀ S : Finset ι, ‖(∏' v : {v // v ∉ S}, f v) - 1‖ ≤
      Real.exp (∑' v : {v // v ∉ S}, |f v - 1|) - 1 := by
    intro S
    rw [Real.norm_eq_abs]
    exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct.abs_tprod_sub_one_le (fun v : {v // v ∉ S} => f v) (hs.subtype _)
  have hlim : Filter.Tendsto (fun S : Finset ι => Real.exp (∑' v : {v // v ∉ S}, |f v - 1|) - 1)
      Filter.atTop (nhds 0) := by
    have h := ((Real.continuous_exp.tendsto 0).comp
      (tendsto_tsum_compl_atTop_zero (fun v => |f v - 1|))).sub_const 1
    simpa [Function.comp_def, Real.exp_zero] using h
  have h0 := squeeze_zero_norm hb hlim
  simpa using h0.add_const 1

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.TailProduct
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAdelicHaarCovolumeOneStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_haar_covolume_one : ∀ (F : Type) [Field F] [NumberField F], ∃ db : Measure (AF F), IsCovolOne db := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.exists_isCovolOne | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.exists_isCovolOne | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.exists_isCovolOne <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianMeasureScalingTransform
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal NNReal Topology

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Dil

section U
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

def mulPiU (ι : Type) (u : Rˣ) : (ι → R) ≃ᵐ (ι → R) :=
  MeasurableEquiv.piCongrRight fun _ =>
    { toEquiv := Units.mulLeft u
      measurable_toFun := (continuous_const.mul continuous_id).measurable
      measurable_invFun := (continuous_const.mul continuous_id).measurable }

theorem mulPiU_apply (ι : Type) (u : Rˣ) (x : ι → R) (i : ι) :
    mulPiU R ι u x i = (u : R) * x i := rfl

theorem map_mulPiU {ι : Type} [Fintype ι] (lam : Measure R) [SigmaFinite lam] (u : Rˣ) (c : ℝ≥0)
    (h : lam.map (fun y => (u : R) * y) = c • lam) :
    (Measure.pi fun _ : ι => lam).map (mulPiU R ι u) =
      (c ^ Fintype.card ι) • Measure.pi fun _ : ι => lam :=
  pi_map_scale lam (fun y => (u : R) * y) (continuous_const.mul continuous_id).measurable c h

theorem coordK_map_unit (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) [SigmaFinite lam] (u : Rˣ) (c : ℝ≥0)
    (h : lam.map (fun y => (u : R) * y) = c • lam) :
    (GlobalTheory.CompanionTheory.SW.coordK R b lam).map (fun y => algebraMap R (R ⊗[F] E) (u : R) * y) =
      (c ^ d) • GlobalTheory.CompanionTheory.SW.coordK R b lam := by
  obtain ⟨hr, -, -, -, -, -, hh, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hb := hh d b
  have hemb : MeasurableEmbedding (fun (y : R ⊗[F] E) (k : Fin d) =>
      (Algebra.TensorProduct.basis R b).repr y k) :=
    hb.homeomorph.toMeasurableEquiv.measurableEmbedding
  have := map_mulPiU (ι := Fin d) R lam u c h
  rw [Fintype.card_fin] at this
  refine map_comap_scale _ _ _ ?_ (mulPiU R (Fin d) u) _ hb.surjective hb.injective
    (fun s hs => (hemb.measurableSet_image' hs).nullMeasurableSet) ?_ this
  · exact (continuous_const.mul continuous_id).measurable
  · intro y
    funext k
    rw [mulPiU_apply, ← Algebra.smul_def, map_smul]
    rfl

end U

theorem coordW_map_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ t : Ainf F, IsUnit t → ∀ c : ℝ≥0, lam.map (fun y => t * y) = c • lam → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam 1 M).map (fun X p i => algebraMap (Ainf F) (Ainf F ⊗[F] E) t * X p i) = (c ^ (d * M)) • GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam 1 M := by
  intro F E _ _ _ _ _ σ hσ M d b lam hlam t ht c h
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Ainf F) d b lam hlam
  haveI := hK
  obtain ⟨u, rfl⟩ := ht
  set f : Ainf F ⊗[F] E → Ainf F ⊗[F] E := fun y => algebraMap (Ainf F) (Ainf F ⊗[F] E) (u : Ainf F) * y with hf
  have hfm : Measurable f := (continuous_const.mul continuous_id).measurable
  have hk := coordK_map_unit (Ainf F) σ hσ b lam u c h
  have hk1 := pi_map_scale (ι := Fin M) (GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) f hfm _ hk
  have hk2 := pi_map_scale (ι := Fin 1) (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam)
    (fun x i => f (x i)) (measurable_pi_iff.2 fun i => hfm.comp (measurable_pi_apply i)) _ hk1
  simp only [Fintype.card_fin, pow_one, ← pow_mul] at hk2
  exact hk2

end GlobalTheory.CompanionTheory.SW.Dil
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MeasurableProjInf
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler

open GlobalTheory.CompanionTheory.SW

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem measurable_projInf [Module.Finite F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) :
    Measurable (HeckeCharacterZeroLocus.SiegelWeilU.projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) := by
  have e := TopK.coordHomeo (E := E) (AF F) b
  have : SecondCountableTopology (AF F ⊗[F] E) := e.secondCountableTopology
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  have hc : Continuous (HeckeCharacterZeroLocus.SiegelWeilU.projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) :=
    MeasProj.continuous_mapTup b (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) MeasProj.continuous_fstA
  refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun i => ?_
  exact (((continuous_apply i).comp (continuous_apply a)).comp hc).measurable

theorem measurable_projV [Module.Finite F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) :
    Measurable (fun X : Fin n → Fin M → AF F ⊗[F] E =>
      HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X)) := by
  have e := TopK.coordHomeo (E := E) (AF F) b
  have : SecondCountableTopology (AF F ⊗[F] E) := e.secondCountableTopology
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have h1 : Continuous (HeckeCharacterZeroLocus.SiegelWeilU.projFin : (Fin n → Fin M → AF F ⊗[F] E) → _) :=
    MeasProj.continuous_mapTup b (HeckeCharacterZeroLocus.SiegelWeilU.sndA F) MeasProj.continuous_sndA
  have h2 : Continuous (HeckeCharacterZeroLocus.SiegelWeilU.projV v : (Fin n → Fin M → Af F ⊗[F] E) → _) :=
    MeasProj.continuous_mapTup b (HeckeCharacterZeroLocus.SiegelWeilU.evalV F v) (MeasProj.continuous_evalV v)
  refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun i => ?_
  exact (((continuous_apply i).comp (continuous_apply a)).comp (h2.comp h1)).measurable

theorem measurableSet_box [Module.Finite F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hA : ∀ v, MeasurableSet (A v)) (hS : ∀ v, v ∉ S → A v = HeckeCharacterZeroLocus.SiegelWeilU.latV b v) :
    MeasurableSet {X : Fin n → Fin M → AF F ⊗[F] E |
      ∀ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin X) ∈ A v} := by
  have e := TopK.coordHomeo (E := E) (AF F) b
  have : SecondCountableTopology (AF F ⊗[F] E) := e.secondCountableTopology
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  rw [EulerBox.box_eq b S A hS]
  exact (MeasProj.isOpen_intOff b S).measurableSet.inter
    (Finset.measurableSet_biInter S fun v _ => measurable_projV b n M v (hA v))

end SlopeTestRemainingChoices

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Euler
end
end

