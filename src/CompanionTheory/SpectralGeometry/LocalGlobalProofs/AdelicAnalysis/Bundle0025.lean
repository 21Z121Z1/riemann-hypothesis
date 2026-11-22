import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0018
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianRankOneHomeomorphBase
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.HermOne

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem sig_sig (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, h⟩ := hcm
  let τ : E →+* ℂ := (inferInstance : Nonempty (E →+* ℂ)).some
  apply τ.injective
  rw [h τ, h τ, star_star]

theorem exists_sig_ne (hcm : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  obtain ⟨-, htc, -, h⟩ := hcm
  let τ : E →+* ℂ := (inferInstance : Nonempty (E →+* ℂ)).some
  have hc : (InfinitePlace.mk τ).IsComplex := htc.isComplex _
  rw [InfinitePlace.isComplex_mk_iff] at hc
  by_contra hall
  push_neg at hall
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := h τ x
  rw [hall x] at this
  simpa using this.symm

theorem trace_sig (hcm : IsCMExt F E σ) (y : E) :
    Algebra.trace F E (σ y) = Algebra.trace F E y := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let e : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext (sig_sig hcm)) (AlgHom.ext (sig_sig hcm))
  have h : (e.toLinearEquiv).conj (Algebra.lmul F E y) = Algebra.lmul F E (σ y) := by
    ext z
    have h1 : e.toLinearEquiv.symm z = σ z := rfl
    have h2 : ∀ w, e.toLinearEquiv w = σ w := fun _ => rfl
    have h3 : ∀ w, e w = σ w := fun _ => rfl
    have h4 : ∀ w, e.symm w = σ w := fun _ => rfl
    simp [LinearEquiv.conj_apply, h1, h2, h3, h4, sig_sig hcm]
  rw [Algebra.trace_apply, Algebra.trace_apply]
  show LinearMap.trace F E (Algebra.lmul F E (σ y)) = LinearMap.trace F E (Algebra.lmul F E y)
  rw [← h, LinearMap.trace_conj']

theorem add_sig_eq_trace (hcm : IsCMExt F E σ) (y : E) :
    y + σ y = algebraMap F E (Algebra.trace F E y) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hfr : Module.finrank F E = 2 := hcm.2.2.1
  obtain ⟨x, hx⟩ := exists_sig_ne hcm
  set θ : E := x - σ x with hθ
  have hθ0 : θ ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hσθ : σ θ = -θ := by simp [hθ, sig_sig hcm]
  have htr : Algebra.trace F E θ = 0 := by
    have h := trace_sig hcm θ
    rw [hσθ, map_neg] at h
    have h2 : (2 : F) * Algebra.trace F E θ = 0 := by linear_combination -h
    simpa using h2
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hσs : ∀ (c : F) (w : E), σ (c • w) = c • σ w := fun c w => by simp [Algebra.smul_def]
    have h2 := congrArg σ hst
    rw [map_add, hσs, hσs, map_one, hσθ, map_zero] at h2
    have h3 : (2 * t) • θ = 0 := by
      have : (2 * t) • θ = (s • (1 : E) + t • θ) - (s • (1 : E) + t • -θ) := by
        simp only [smul_neg, mul_smul, two_smul]
        abel
      rw [this, hst, h2, sub_zero]
    have ht : t = 0 := by simpa [hθ0] using h3
    refine ⟨?_, ht⟩
    simpa [ht] using hst
  let bb : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hfr])
  have hbb : ∀ i, bb i = ![(1 : E), θ] i := fun i => by
    simp [bb]
  have hmaps : (LinearMap.id + σ.toLinearMap : E →ₗ[F] E) =
      (Algebra.linearMap F E) ∘ₗ Algebra.trace F E := by
    refine bb.ext fun i => ?_
    fin_cases i
    · have h1 : Algebra.trace F E (1 : E) = 2 := by
        have := Algebra.trace_algebraMap (R := F) (S := E) (1 : F)
        simpa [hfr] using this
      simp [hbb, h1]
      rw [map_ofNat]
      norm_num
    · simp [hbb, htr, hσθ]
  simpa using LinearMap.congr_fun hmaps y

end Field

section Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (R : Type) [CommRing R] [Algebra F R]

theorem trace_tmul (r : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] e) = r * algebraMap F R (Algebra.trace F E e) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h1 : r ⊗ₜ[F] e = r • ((1 : R) ⊗ₜ[F] e) := by simp [TensorProduct.smul_tmul']
  have h2 : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = (Algebra.lmul F E e).baseChange R := by
    ext z
    simp
  rw [h1, map_smul, smul_eq_mul, Algebra.trace_apply, Algebra.trace_apply]
  show r * LinearMap.trace R _ (Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e)) = _
  rw [h2, LinearMap.trace_baseChange]

theorem add_sigR_eq_trace (hcm : IsCMExt F E σ) (z : R ⊗[F] E) :
    z + sigR R σ z = (Algebra.trace R (R ⊗[F] E) z) ⊗ₜ[F] (1 : E) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    have h1 : sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := by simp [sigR]
    rw [h1, ← TensorProduct.tmul_add, add_sig_eq_trace hcm, trace_tmul,
      Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.smul_def, mul_comm]
  | add a c ha hc =>
    rw [map_add, map_add, TensorProduct.add_tmul, ← ha, ← hc]
    abel

end Ring

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} (R : Type) [CommRing R] [Algebra F R]

def tH (σ : E →ₐ[F] E) (S : HermR R σ 1) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0)

theorem tH_hermScal (hcm : IsCMExt F E σ) (r : R) : tH R σ (hermScal R σ r) = r := by
  have h1 : Algebra.trace F E (1 : E) = 2 := by
    have := Algebra.trace_algebraMap (R := F) (S := E) (1 : F)
    simpa [hcm.2.2.1] using this
  have h2 : algebraMap F R (1 / 2) * algebraMap F R 2 = 1 := by
    rw [← map_mul]
    norm_num
  show algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] (1 : E)) = r
  rw [trace_tmul, h1]
  linear_combination r * h2

theorem hermScal_tH (hcm : IsCMExt F E σ) (S : HermR R σ 1) : hermScal R σ (tH R σ S) = S := by
  apply Subtype.ext
  ext i j
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  set z : R ⊗[F] E := (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 with hz
  have hfix : sigR R σ z = z := S.2 0 0
  have hs := add_sigR_eq_trace R hcm z
  rw [hfix] at hs
  show (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) z) ⊗ₜ[F] (1 : E) = z
  rw [← Algebra.smul_def, ← TensorProduct.smul_tmul', ← hs, ← two_smul F z, smul_smul]
  norm_num

variable [TopologicalSpace R] [IsTopologicalRing R]

def hermHomeo (hcm : IsCMExt F E σ) : HermR R σ 1 ≃ₜ R :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  { toFun := tH R σ
    invFun := hermScal R σ
    left_inv := hermScal_tH R hcm
    right_inv := tH_hermScal R hcm
    continuous_toFun := continuous_const.mul
      ((IsModuleTopology.continuous_of_linearMap (R := R) (Algebra.trace R (R ⊗[F] E))).comp
        ((continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val)))
    continuous_invFun := Continuous.subtype_mk (continuous_pi fun _ => continuous_pi fun _ =>
      IsModuleTopology.continuous_of_linearMap (R := R) (Algebra.linearMap R (R ⊗[F] E))) _ }

variable [MeasurableSpace R] [BorelSpace R]

theorem map_coordHerm (hcm : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    [SigmaFinite lam] : (coordHerm R σ b lam 1).map (hermHomeo R hcm) = lam := by
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  haveI hT : IsEmpty {p : Fin 1 × Fin 1 // p.1 < p.2} :=
    ⟨fun p => by
      have h := p.2
      rw [Subsingleton.elim p.1.1 p.1.2] at h
      exact lt_irrefl _ h⟩
  let ψ : R → (Fin 1 → R) × ({p : Fin 1 × Fin 1 // p.1 < p.2} → R ⊗[F] E) :=
    fun r => (fun _ => r, fun p => hT.elim p)
  have hψ : MeasurableEmbedding ψ := by
    refine MeasurableEmbedding.of_measurable_inverse (g := fun q => q.1 0) ?_ ?_ ?_ ?_
    · refine Measurable.prodMk (measurable_pi_lambda _ fun _ => measurable_id) ?_
      exact measurable_pi_lambda _ fun p => hT.elim p
    · have : Set.range ψ = Set.univ := by
        ext q
        simp only [Set.mem_range, Set.mem_univ, iff_true]
        refine ⟨q.1 0, Prod.ext ?_ (Subsingleton.elim _ _)⟩
        funext i
        obtain rfl : i = 0 := Subsingleton.elim _ _
        rfl
      rw [this]
      exact MeasurableSet.univ
    · exact (measurable_pi_apply 0).comp measurable_fst
    · intro r
      rfl
  ext s hs
  have hfun : (fun S : HermR R σ 1 =>
      ((fun i : Fin 1 => algebraMap F R (1 / 2) *
          Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i i)),
        (fun p : {p : Fin 1 × Fin 1 // p.1 < p.2} =>
          (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) p.1.1 p.1.2))) = ψ ∘ hermHomeo R hcm := by
    funext S
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rfl
  have hemb : MeasurableEmbedding (ψ ∘ hermHomeo R hcm) :=
    hψ.comp (hermHomeo R hcm).measurableEmbedding
  have hpi : Measure.pi (fun _ : {p : Fin 1 × Fin 1 // p.1 < p.2} => coordK R b lam) =
      Measure.dirac (fun p => hT.elim p) := Measure.pi_of_empty _ _
  have himg : (ψ ∘ hermHomeo R hcm) '' (hermHomeo R hcm ⁻¹' s) =
      ((fun a : Fin 1 → R => a 0) ⁻¹' s) ×ˢ Set.univ := by
    ext q
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact ⟨hS, Set.mem_univ _⟩
    · rintro ⟨hq, -⟩
      refine ⟨(hermHomeo R hcm).symm (q.1 0), ?_, ?_⟩
      · simpa using hq
      · refine Prod.ext ?_ (Subsingleton.elim _ _)
        funext i
        obtain rfl : i = 0 := Subsingleton.elim _ _
        simp [ψ]
  rw [Measure.map_apply (hermHomeo R hcm).measurable hs, coordHerm, hfun, hemb.comap_apply, hpi, himg,
    Measure.prod_prod, measure_univ, mul_one]
  exact (measurePreserving_funUnique lam (Fin 1)).measure_preimage hs.nullMeasurableSet

end Main

end GlobalTheory.CompanionTheory.SW.BB.HermOne
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicAndBlockOneNondegenerate
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BlockForm

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem blockOne_zero_zero {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    blockOne t A 0 0 = t := rfl

theorem blockOne_zero_succ {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K)
    (j : Fin M) : blockOne t A 0 j.succ = 0 := rfl

theorem blockOne_succ_zero {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K)
    (i : Fin M) : blockOne t A i.succ 0 = 0 := rfl

theorem blockOne_succ_succ {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K)
    (i j : Fin M) : blockOne t A i.succ j.succ = A i j := rfl

theorem det_blockOne {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by
  have h0 : (blockOne t A).submatrix Fin.succ Fin.succ = A := by
    ext i j
    exact blockOne_succ_succ t A i j
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [blockOne_zero_zero, blockOne_zero_succ, h0]

theorem hypJ_zero_zero {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    hypJ A 0 0 = 0 := rfl

theorem hypJ_zero_one {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    hypJ A 0 1 = 1 := by
  rw [← Fin.succ_zero_eq_one]; rfl

theorem hypJ_zero_succ_succ {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (j : Fin M) : hypJ A 0 j.succ.succ = 0 := rfl

theorem hypJ_one_zero {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    hypJ A 1 0 = 1 := by
  rw [← Fin.succ_zero_eq_one]; rfl

theorem hypJ_one_one {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    hypJ A 1 1 = 0 := by
  rw [← Fin.succ_zero_eq_one]; rfl

theorem hypJ_one_succ_succ {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (j : Fin M) : hypJ A 1 j.succ.succ = 0 := by
  rw [← Fin.succ_zero_eq_one]; rfl

theorem hypJ_succ_succ_zero {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (i : Fin M) : hypJ A i.succ.succ 0 = 0 := rfl

theorem hypJ_succ_succ_one {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (i : Fin M) : hypJ A i.succ.succ 1 = 0 := by
  rw [← Fin.succ_zero_eq_one]; rfl

theorem hypJ_succ_succ_succ_succ {K : Type} [Zero K] [One K] {M : ℕ}
    (A : Matrix (Fin M) (Fin M) K) (i j : Fin M) : hypJ A i.succ.succ j.succ.succ = A i j := rfl

theorem det_hypJ {K : Type} [CommRing K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    (hypJ A).det = -A.det := by
  have h1 : (hypJ A).submatrix Fin.succ (Fin.succAbove 1) = blockOne 1 A := by
    rw [← Fin.succ_zero_eq_one]
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · rfl
    · rfl
    · rfl
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [hypJ_zero_zero, hypJ_zero_one, hypJ_zero_succ_succ, h1, det_blockOne]

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem isHermND_hypJ (σ : E →ₐ[F] E) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) : IsHermND σ (hypJ J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [hypJ_zero_zero]
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [hypJ_zero_one, hypJ_one_zero]
        · simp [hypJ_zero_succ_succ, hypJ_succ_succ_zero]
    · refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [hypJ_zero_one, hypJ_one_zero]
        · refine Fin.cases ?_ (fun j => ?_) j
          · simp [hypJ_one_one]
          · simp [hypJ_one_succ_succ, hypJ_succ_succ_one]
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [hypJ_zero_succ_succ, hypJ_succ_succ_zero]
        · refine Fin.cases ?_ (fun j => ?_) j
          · simp [hypJ_one_succ_succ, hypJ_succ_succ_one]
          · rw [hypJ_succ_succ_succ_succ, hypJ_succ_succ_succ_succ]
            exact hJ.1 i j
  · rw [det_hypJ]
    exact neg_ne_zero.mpr hJ.2

theorem isHermND_blockOne (σ : E →ₐ[F] E) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) {t : F} (ht : t ≠ 0) : IsHermND σ (blockOne (algebraMap F E t) J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [blockOne_zero_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · rw [blockOne_succ_succ, blockOne_succ_succ]
      exact hJ.1 i j
  · rw [det_blockOne]
    exact mul_ne_zero ((map_ne_zero (algebraMap F E)).mpr ht) hJ.2

theorem blockForms_isHermND : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHermND σ (hypJ J) ∧
      ∀ t : F, t ≠ 0 → IsHermND σ (blockOne (algebraMap F E t) J) :=
  fun _ _ _ _ _ _ _ σ _ _ _ hJ => ⟨isHermND_hypJ σ hJ, fun _ ht => isHermND_blockOne σ hJ ht⟩

end GlobalTheory.CompanionTheory.SW.BlockForm
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IntegralAlmostAllPlacesStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_almost_all_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), (∀ x : E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) x) k ∈ v.adicCompletionIntegers F) ∧ ∀ x : F, x ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v (algebraMap F (Fv F v) x) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units | exact GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units | (intros; apply GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeStableAlmostEverywhereStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stable_almost_everywhere : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ g : Matrix (Fin n) (Fin n) E, g.det ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), rmul (Fv F v) X (g.map (inclR (Fv F v))) ∈ latV b v ↔ X ∈ latV b v) ∧ (∀ g : GL (Fin M) E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), actTup (Fv F v) (bc (inclR (Fv F v)) g) X ∈ latV b v ↔ X ∈ latV b v) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ X : (Fin n → Fin M → Fv F v ⊗[F] E), consTup X ∈ latV b v ↔ X ∈ latV b v := by
  first | exact @GlobalTheory.CompanionTheory.SW.LatRat.latV_rational | exact GlobalTheory.CompanionTheory.SW.LatRat.latV_rational | (intros; apply GlobalTheory.CompanionTheory.SW.LatRat.latV_rational <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalUnitsContinuousSquareRoot
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem exists_sqrt_near_unit : ∀ (R : Type) [CommRing R] [TopologicalSpace R], IsLocR R → ∀ x : Rˣ,
    ∃ (B₀ : Set R) (a : R → Rˣ), IsOpen B₀ ∧ (x : R) ∈ B₀ ∧ ContinuousOn a B₀ ∧
      (∀ y, y ∉ B₀ → a y = 1) ∧ (∀ y ∈ B₀, y = ((a y : Rˣ) : R) ^ 2 * (x : R)) ∧ a (x : R) = 1 := by
  classical
  intro R _ _ hR x
  obtain ⟨htr, -, -, -, -, -, hval, U, -, hq⟩ := hR

  let h : R ≃ₜ R :=
    { toFun := fun y => y * (x : R)
      invFun := fun y => y * ((x⁻¹ : Rˣ) : R)
      left_inv := fun y => by simp [mul_assoc]
      right_inv := fun y => by simp [mul_assoc]
      continuous_toFun := continuous_id.mul continuous_const
      continuous_invFun := continuous_id.mul continuous_const }
  let f : U → R := fun u => (((u : Rˣ) ^ 2 : Rˣ) : R) * (x : R)
  have hf : IsOpenEmbedding f :=
    h.isOpenEmbedding.comp (hval.comp hq)
  have hf1 : f 1 = (x : R) := by simp [f]
  let a : R → Rˣ := fun y => if y ∈ Set.range f then ((Function.invFun f y : U) : Rˣ) else 1
  have haf : ∀ u : U, a (f u) = (u : Rˣ) := by
    intro u
    have : Function.invFun f (f u) = u := Function.leftInverse_invFun hf.injective u
    simp only [a, Set.mem_range_self, if_true, this]
  refine ⟨Set.range f, a, hf.isOpen_range, ⟨1, hf1⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    apply ContinuousAt.continuousWithinAt
    rw [← hf.continuousAt_iff]
    have : a ∘ f = fun u : U => (u : Rˣ) := funext haf
    rw [this]
    exact continuous_subtype_val.continuousAt
  · intro y hy
    simp only [a, if_neg hy]
  · rintro _ ⟨u, rfl⟩
    rw [haf]
    simp [f]
  · have := haf 1
    rw [hf1] at this
    simpa using this

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PoissonSummationGaussianStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poisson_summation_gaussian : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (Z : Matrix κ κ ℂ), Z.IsSymm → (Z.map Complex.im).PosDef → ∀ (g : Matrix κ κ ℝ), g.det ≠ 0 → ∀ a : κ → ℝ, let f : (κ → ℝ) → ℂ := fun x => Complex.exp ((Real.pi : ℂ) * Complex.I * ((fun i => (x i : ℂ)) ⬝ᵥ (Z *ᵥ fun i => (x i : ℂ)))); let fh : (κ → ℝ) → ℂ := fun y => ∫ x, f x * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x ⬝ᵥ y : ℝ) : ℂ)); Summable (fun n : κ → ℤ => ‖f (a + g *ᵥ fun i => (n i : ℝ))‖) ∧ Summable (fun n : κ → ℤ => ‖fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ))‖) ∧ ∑' n : κ → ℤ, f (a + g *ᵥ fun i => (n i : ℝ)) = ((|g.det|⁻¹ : ℝ) : ℂ) * ∑' n : κ → ℤ, fh ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((a ⬝ᵥ ((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.PoiLat.poisson_shifted_lattice | exact GlobalTheory.CompanionTheory.SW.Core.PoiLat.poisson_shifted_lattice | (intros; apply GlobalTheory.CompanionTheory.SW.Core.PoiLat.poisson_shifted_lattice <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankZeroGramFiberMeasureStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_zero_gram_fiber_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ m, IsGramFib R σ J 0 (coordW R b lam 0 M) (coordHerm R σ b lam 0) m → ∀ S, m S = Measure.dirac (fun a => a.elim0) := by
  first | exact @GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_gram_zero | exact GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_gram_zero | (intros; apply GlobalTheory.CompanionTheory.SW.GramEmpty.fibre_gram_zero <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ReductionToSiegelDomainStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_to_siegel_domain : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∃ (s : Finset SL(2, F)) (κ t : ℝ), 0 < κ ∧ 0 < t ∧ ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∃ r ∈ s, ∃ k : SL(2, F), (∀ i j, ∃ z : 𝓞 F, (z : F) = k i j) ∧ (∀ w, t ≤ (mob ρ (r * k) τ w).im) ∧ ∀ v w, κ * (mob ρ (r * k) τ w).im ≤ (mob ρ (r * k) τ v).im := by
  first | exact @GlobalTheory.CompanionTheory.SW.Red.reduction | exact GlobalTheory.CompanionTheory.SW.Red.reduction | (intros; apply GlobalTheory.CompanionTheory.SW.Red.reduction <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ScalarHermitianTraceAndUnit
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB.ScalTrace

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem hermScal_entry {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (R : Type) [CommRing R] [Algebra F R] (s : R) :
    (hermScal R σ s : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 = algebraMap R (R ⊗[F] E) s := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem trace_det : ∀ (F E : Type) [Field F] [Field E] [Algebra F E], (1 / 2 : F) ≠ 0 → Module.finrank F E = 2 → ∀ (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (β : F), algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((hermScal R σ (algebraMap F R β) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) = algebraMap F R β ∧ (β ≠ 0 → IsUnit ((hermScal R σ (algebraMap F R β) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))).det) := by
  intro F E _ _ _ h2 hf σ R _ _ β
  have hfin : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hf
  have hent := hermScal_entry σ R (algebraMap F R β)
  refine ⟨?_, fun hβ => ?_⟩
  · rw [hent, Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b) (algebraMap F R β)]
    have h20 : (2 : F) ≠ 0 := by
      intro h
      apply h2
      simp [h]
    have hhalf : algebraMap F R (1 / 2) * algebraMap F R 2 = 1 := by
      rw [← map_mul, one_div, inv_mul_cancel₀ h20, map_one]
    rw [Fintype.card_fin, nsmul_eq_mul]
    have h2R : ((2 : ℕ) : R) = algebraMap F R 2 := by
      rw [map_ofNat]
      norm_num
    rw [h2R, ← mul_assoc, hhalf, one_mul]
  · rw [Matrix.det_fin_one, hent]
    exact ((isUnit_iff_ne_zero.2 hβ).map (algebraMap F R)).map (algebraMap R (R ⊗[F] E))

end GlobalTheory.CompanionTheory.SW.BB.ScalTrace
end
end

