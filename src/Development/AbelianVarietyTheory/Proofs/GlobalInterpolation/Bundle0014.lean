import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0010
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0011
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdditiveCharConductorExistsStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_char_conductor_exists : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (v.adicCompletion F) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → (∃ t, ψ t ≠ 1) → ∃ n : ℤ, ∀ t : v.adicCompletion F, (∀ s ∈ v.adicCompletionIntegers F, ψ (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp n := by
  first | exact @GlobalTheory.CharConductor.exists_conductor_exponent | exact GlobalTheory.CharConductor.exists_conductor_exponent | (intros; apply GlobalTheory.CharConductor.exists_conductor_exponent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContDensityOnEqFibreMass
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem eq_zero_of_setIntegral_compact_eq_zero {K : Type} [MetricSpace K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsFiniteMeasureOnCompacts ν]
    [ν.IsOpenPosMeasure] {B : Set K} (hB : IsOpen B) {h : K → ℂ} (hc : ContinuousOn h B)
    (hz : ∀ S : Set K, IsCompact S → S ⊆ B → ∫ b in S, h b ∂ν = 0) {t : K} (ht : t ∈ B) :
    h t = 0 := by
  by_contra hne
  have hpos : 0 < ‖h t‖ := norm_pos_iff.2 hne
  have hca : ContinuousAt h t := hc.continuousAt (hB.mem_nhds ht)
  obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.1 hca (‖h t‖ / 2) (half_pos hpos)
  obtain ⟨δ, hδ, hδB⟩ := Metric.isOpen_iff.1 hB t ht
  have hρ0 : 0 < min (ε / 2) (δ / 2) := lt_min (half_pos hε) (half_pos hδ)
  have hmemS : ∀ b ∈ Metric.closedBall t (min (ε / 2) (δ / 2)), dist b t < ε ∧ dist b t < δ := by
    intro b hb
    have hb' := Metric.mem_closedBall.1 hb
    constructor
    · linarith [min_le_left (ε / 2) (δ / 2)]
    · linarith [min_le_right (ε / 2) (δ / 2)]
  have hSc := isCompact_closedBall t (min (ε / 2) (δ / 2))
  have hSB : Metric.closedBall t (min (ε / 2) (δ / 2)) ⊆ B := fun b hb =>
    hδB (Metric.mem_ball.2 (hmemS b hb).2)
  have hνS : 0 < ν (Metric.closedBall t (min (ε / 2) (δ / 2))) :=
    Metric.measure_closedBall_pos ν t hρ0
  have hνSf : ν (Metric.closedBall t (min (ε / 2) (δ / 2))) < ⊤ := hSc.measure_lt_top
  have hIh : IntegrableOn h (Metric.closedBall t (min (ε / 2) (δ / 2))) ν :=
    (hc.mono hSB).integrableOn_compact hSc
  have hIc : IntegrableOn (fun _ => h t) (Metric.closedBall t (min (ε / 2) (δ / 2))) ν :=
    integrableOn_const hνSf.ne
  have key := integral_sub hIh hIc
  rw [hz _ hSc hSB, setIntegral_const, zero_sub] at key
  have hbound := norm_setIntegral_le_of_norm_le_const hνSf (f := fun b => h b - h t)
    (C := ‖h t‖ / 2) (fun b hb => by rw [← dist_eq_norm]; exact (hball (hmemS b hb).1).le)
  rw [key, norm_neg, norm_smul, Real.norm_of_nonneg measureReal_nonneg] at hbound
  have hreal : 0 < ν.real (Metric.closedBall t (min (ε / 2) (δ / 2))) := by
    rw [measureReal_def]; exact ENNReal.toReal_pos hνS.ne' hνSf.ne
  nlinarith [mul_pos hreal hpos]

theorem contDensityOn_eq_fibre_mass : ∀ (K V : Type) [NormedField K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [TopologicalSpace V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → ∀ (fib : K → Measure V), IsFibreFamily μ q id Set.univ ν {t | t ≠ 0} fib → ∀ (L : Set V), IsCompact L → IsOpen L → ∀ g : K → ℂ, IsContDensityOn μ q id ν {t | t ≠ 0} (L.indicator 1) g → ∀ t : K, t ≠ 0 → g t = (((fib t L).toReal : ℝ) : ℂ) := by
  intro K V _ _ _ _ _ _ _ _ μ ν _ q hq fib hfib L hLc hLo g hg t ht
  obtain ⟨hf1, hf2, hf3⟩ := hfib
  obtain ⟨hgc, hgS⟩ := hg
  have hLm : MeasurableSet L := hLo.measurableSet
  have hBo : IsOpen {t : K | t ≠ 0} := isOpen_ne
  have hφc : Continuous (L.indicator (1 : V → ℝ)) :=
    IsClopen.continuous_indicator ⟨hLc.isClosed, hLo⟩ continuous_const
  have hφs : HasCompactSupport (L.indicator (1 : V → ℝ)) :=
    HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  obtain ⟨hint, hcont⟩ := hf3 _ hφc hφs (Set.subset_univ _)
  have hm_eq : (fun b => ∫ v, L.indicator (1 : V → ℝ) v ∂(fib b)) = fun b => (fib b L).toReal := by
    funext b; rw [integral_indicator_one hLm]; rfl
  have hmc : ContinuousOn (fun b => (fib b L).toReal) {t : K | t ≠ 0} := by
    rw [← hm_eq]; exact hcont
  have hfin : ∀ b ∈ {t : K | t ≠ 0}, fib b L < ⊤ := by
    intro b hb
    have hi := hint b hb
    rw [integrable_indicator_iff hLm] at hi
    exact ((integrableOn_const_iff (C := (1 : ℝ))).1 hi).resolve_left (by simp)
  have hmcC : ContinuousOn (fun b => (((fib b L).toReal : ℝ) : ℂ)) {t : K | t ≠ 0} :=
    Complex.continuous_ofReal.comp_continuousOn hmc
  have key : ∀ S : Set K, IsCompact S → S ⊆ {t : K | t ≠ 0} →
      ∫ b in S, (g b - (((fib b L).toReal : ℝ) : ℂ)) ∂ν = 0 := by
    intro S hS hSB
    have hSm : MeasurableSet S := hS.measurableSet
    rw [integral_sub ((hgc.mono hSB).integrableOn_compact hS)
      ((hmcC.mono hSB).integrableOn_compact hS), sub_eq_zero, ← hgS S hS hSB, Set.image_id]
    have hind : L.indicator (1 : V → ℂ) = L.indicator (fun _ => (1 : ℂ)) := rfl
    rw [hind, integral_indicator_const _ hLm, integral_complex_ofReal, Complex.real_smul, mul_one]
    congr 1
    have haem : AEMeasurable (fun b => fib b L) (ν.restrict S) :=
      ((hmc.mono hSB).aemeasurable hSm).ennreal_ofReal.congr
        ((ae_restrict_mem hSm).mono fun b hb => ENNReal.ofReal_toReal (hfin b (hSB hb)).ne)
    rw [integral_toReal haem ((ae_restrict_mem hSm).mono fun b hb => hfin b (hSB hb)),
      measureReal_def, Measure.restrict_apply hLm]
    congr 1
    have hTm : MeasurableSet (L ∩ q ⁻¹' S) := hLm.inter (hq.measurable hSm)
    have h2 := hf2 ((L ∩ q ⁻¹' S).indicator 1) (measurable_one.indicator hTm)
    rw [Measure.restrict_univ, lintegral_indicator_one hTm] at h2
    rw [h2, ← lintegral_indicator hSm]
    refine lintegral_congr fun b => ?_
    rw [lintegral_indicator_one hTm]
    by_cases hb : b ∈ S
    · rw [Set.indicator_of_mem hb]
      refine measure_inter_conull (measure_mono_null (Set.compl_subset_compl.2 ?_) (hf1 b))
      intro v hv
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, id] at hv
      simp only [Set.mem_preimage, hv.1, hb]
    · rw [Set.indicator_of_notMem hb]
      refine measure_mono_null (fun v hv => ?_) (hf1 b)
      simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        id, Set.mem_univ, and_true]
      intro hqv
      exact hb (hqv ▸ hv.2)
  exact sub_eq_zero.1 (eq_zero_of_setIntegral_compact_eq_zero ν hBo (hgc.sub hmcC) key
    (show t ∈ {t : K | t ≠ 0} from ht))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
section
open Complex
open UpperHalfPlane hiding I
open scoped Real

noncomputable section

namespace GlobalTheory.ThetaWeberRoad

def tpFactor (τ : ℍ) (z : ℂ) (n : ℕ) : ℂ :=
  (1 - cexp (2 * π * I * ((n : ℂ) + 1) * (τ : ℂ))) *
    (1 + cexp (π * I * (2 * (n : ℂ) + 1) * (τ : ℂ) + 2 * π * I * z)) *
    (1 + cexp (π * I * (2 * (n : ℂ) + 1) * (τ : ℂ) - 2 * π * I * z))

def TripleProduct : Prop := ∀ (τ : ℍ) (z : ℂ), HasProd (tpFactor τ z) (jacobiTheta₂ z τ)

def oddTheta (τ : ℍ) (z : ℂ) : ℂ :=
  cexp (π * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2)) * jacobiTheta₂ (z + ((τ : ℂ) + 1) / 2) τ

theorem differentiable_oddTheta (τ : ℍ) : Differentiable ℂ (oddTheta τ) := by
  intro z
  have hexp : DifferentiableAt ℂ
      (fun w : ℂ => cexp (π * I * (τ : ℂ) / 4 + π * I * (w + 1 / 2))) z := by
    fun_prop
  have hshift : DifferentiableAt ℂ (fun w : ℂ => w + ((τ : ℂ) + 1) / 2) z :=
    differentiableAt_id.add_const _
  have htheta : DifferentiableAt ℂ
      (fun w : ℂ => jacobiTheta₂ (w + ((τ : ℂ) + 1) / 2) τ) z := by
    have h0 : DifferentiableAt ℂ (fun w : ℂ => jacobiTheta₂ w τ) (z + ((τ : ℂ) + 1) / 2) :=
      differentiableAt_jacobiTheta₂_fst _ τ.2
    exact h0.comp z hshift
  exact hexp.mul htheta

end GlobalTheory.ThetaWeberRoad
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBruhatFunctionOfClosedEmbedding
section
open MeasureTheory Topology
open scoped ENNReal

namespace GlobalTheory

theorem exists_bruhat_function_closedEmbedding
    (T T' : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T]
    [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [MeasurableSpace T'] [BorelSpace T']
    (j : T' →* T) (hj : IsClosedEmbedding j) (m' : Measure T') [m'.IsHaarMeasure]
    [m'.IsInvInvariant] :
    ∃ b : T → ℝ≥0∞, Measurable b ∧ ∀ t, ∫⁻ s, b (j s * t) ∂m' = 1 := by
  classical
  let H : Subgroup T := j.range
  have hH : IsClosed (H : Set T) := by
    simpa [H, MonoidHom.coe_range] using hj.isClosed_range
  let e : T' ≃* H := MonoidHom.ofInjective hj.injective
  have he : Continuous e := hj.continuous.subtype_mk _
  have hes : Continuous e.symm := by
    rw [hj.isEmbedding.isInducing.continuous_iff]
    have : (fun x : H => j (e.symm x)) = fun x : H => (x : T) := by
      funext x
      exact MonoidHom.apply_ofInjective_symm hj.injective x
    rw [Function.comp_def, this]
    exact continuous_subtype_val
  have : (Measure.map e m').IsHaarMeasure := e.isHaarMeasure_map m' he hes
  obtain ⟨φ, hφ, hint, -⟩ := exists_bruhat_function_closed_subgroup T H hH (Measure.map e m')
  refine ⟨fun x => φ x⁻¹, hφ.comp measurable_inv, fun t => ?_⟩
  show ∫⁻ s, φ (j s * t)⁻¹ ∂m' = 1
  have h1 := hint t⁻¹
  have hm : Measurable (fun h : H => φ (t⁻¹ * (h : T))) :=
    hφ.comp (continuous_const.mul continuous_subtype_val).measurable
  rw [lintegral_map hm he.measurable] at h1
  have h2 : ∀ s : T', ((e s : H) : T) = j s := fun s => rfl
  simp only [h2] at h1
  have h3 : ∀ s : T', (j s * t)⁻¹ = t⁻¹ * j s⁻¹ := fun s => by
    rw [mul_inv_rev, map_inv]
  simp only [h3]
  rw [lintegral_inv_eq_self (fun s => φ (t⁻¹ * j s))]
  exact h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarOfInvariantRadonOnCosetsStatement
section
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_haar_of_invariantRadonOnCosets : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)], IsClosed (H : Set G) → ∀ (ν : Measure H) [ν.IsHaarMeasure] (μ : Measure (G ⧸ H)), IsInvariantRadon H μ → ∃! dg : Measure G, dg.IsHaarMeasure ∧ QuotientFormula H dg ν μ := by
  first | exact @GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon | exact GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon | (intros; apply GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibOfZero
section
noncomputable section

namespace GlobalTheory.QuadFibre

open MeasureTheory
open scoped Pointwise

def IsSqrtOn {K : Type} [NormedField K] (U : Set K) (s : K → K) : Prop :=
  IsOpen U ∧ IsCompact U ∧ (1 : K) ∈ U ∧ (∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) ∧ (∀ a ∈ U, a⁻¹ ∈ U) ∧
    (∀ a ∈ U, ‖a‖ = 1) ∧ Continuous s ∧ ∀ a ∈ U, s a ^ 2 = a

open Classical in

def fibOf {K V : Type} [NormedField K] [MeasurableSpace K] [AddCommGroup V] [Module K V]
    [MeasurableSpace V] (μ : Measure V) (ν : Measure K) (q : V → K) (U : Set K) (s : K → K)
    (t : K) : Measure V :=
  if t = 0 then 0 else
    (ν (t • U))⁻¹ • Measure.map (fun x => s (t / q x) • x) (μ.restrict (q ⁻¹' (t • U)))

theorem fibOf_zero {K V : Type} [NormedField K] [MeasurableSpace K] [AddCommGroup V] [Module K V]
    [MeasurableSpace V] (μ : Measure V) (ν : Measure K) (q : V → K) (U : Set K) (s : K → K) :
    fibOf μ ν q U s 0 = 0 := by simp [fibOf]

theorem fibOf_ne {K V : Type} [NormedField K] [MeasurableSpace K] [AddCommGroup V] [Module K V]
    [MeasurableSpace V] (μ : Measure V) (ν : Measure K) (q : V → K) (U : Set K) (s : K → K)
    {t : K} (ht : t ≠ 0) : fibOf μ ν q U s t =
      (ν (t • U))⁻¹ • Measure.map (fun x => s (t / q x) • x) (μ.restrict (q ⁻¹' (t • U))) := by
  simp [fibOf, ht]

end GlobalTheory.QuadFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.HermLineZeros

section Ring

variable {A : Type} [CommRing A] {M : ℕ}

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {A : Type} [CommRing A] {M : ℕ} in
theorem _root_.GlobalTheory.HermLineZeros.hform_expand (s : A →+* A) (J : Matrix (Fin M) (Fin M) A)
    (x y : Fin M → A) (c : A) :
    _root_.Formalism.UG.hform s J (x + c • y) (x + c • y) =
      _root_.Formalism.UG.hform s J x x + c * _root_.Formalism.UG.hform s J x y + s c * _root_.Formalism.UG.hform s J y x
        + s c * c * _root_.Formalism.UG.hform s J y y := by
  unfold _root_.Formalism.UG.hform
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
  ring

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {A : Type} [CommRing A] {M : ℕ} in
theorem _root_.GlobalTheory.HermLineZeros.hform_single (s : A →+* A) (J : Matrix (Fin M) (Fin M) A)
    (i j : Fin M) :
    _root_.Formalism.UG.hform s J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [_root_.Formalism.UG.hform, Pi.single_apply, apply_ite s]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.HermLineZeros.conj_invol (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.HermLineZeros.exists_conj_ne (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) : ∃ d, σ d ≠ d := by
  by_contra! hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hreal : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx := h.2.2.2 τ x
    rw [hσ x] at hx
    simpa [ComplexEmbedding.conjugate_coe_eq] using hx.symm
  have hcx := (h.2.1).isComplex (InfinitePlace.mk τ)
  rw [InfinitePlace.isComplex_mk_iff] at hcx
  exact hcx hreal

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.HermLineZeros.exists_of_fixed (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (e : E) (he : σ e = e) :
    ∃ f, algebraMap F E f = e := by
  obtain ⟨d, hd⟩ := _root_.GlobalTheory.HermLineZeros.exists_conj_ne h
  let S : Subalgebra F E := AlgHom.equalizer σ (AlgHom.id F E)
  have hS : S ≠ ⊤ := by
    intro hS
    have hdS : d ∈ S := hS ▸ Algebra.mem_top
    exact hd hdS
  have hle : Module.finrank F S ≤ 2 :=
    h.2.2.1 ▸ Submodule.finrank_le (Subalgebra.toSubmodule S)
  have hne : Module.finrank F S ≠ 2 := by
    intro h2
    apply hS
    apply Subalgebra.toSubmodule.injective
    rw [Algebra.top_toSubmodule]
    exact Submodule.eq_top_of_finrank_eq (h2.trans h.2.2.1.symm)
  have hpos : 0 < Module.finrank F S := Module.finrank_pos
  have hbot : S = ⊥ := Subalgebra.finrank_eq_one_iff.mp (by omega)
  have heS : e ∈ S := he
  rw [hbot] at heS
  exact Algebra.mem_bot.mp heS

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
private theorem hE_self_conj_fixed (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J) (v : Fin M → E) :
    σ (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J v v) = _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J v v := by
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE _root_.Formalism.UG.hform
  rw [map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [AlgHom.coe_toRingHom, map_mul, _root_.GlobalTheory.HermLineZeros.conj_invol h, hJ.1]
  ring

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
theorem _root_.GlobalTheory.HermLineZeros.exists_anisotropic (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {M : ℕ} (hM : 1 ≤ M)
    {J : Matrix (Fin M) (Fin M) E} (hJ : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J) :
    ∃ (y : Fin M → E) (a : F), a ≠ 0 ∧ _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J y y = algebraMap F E a := by
  suffices hv : ∃ v, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE σ J v v ≠ 0 by
    obtain ⟨v, hv⟩ := hv
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.HermLineZeros.exists_of_fixed h _ (hE_self_conj_fixed h hJ v)
    refine ⟨v, a, ?_, ha.symm⟩
    rintro rfl
    exact hv (by rw [← ha, map_zero])
  by_cases hd : ∃ i, J i i ≠ 0
  · obtain ⟨i, hi⟩ := hd
    exact ⟨Pi.single i 1, by rwa [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, _root_.GlobalTheory.HermLineZeros.hform_single]⟩
  push_neg at hd
  let i₀ : Fin M := ⟨0, hM⟩
  obtain ⟨j, hj⟩ : ∃ j, J i₀ j ≠ 0 := by
    by_contra! hrow
    exact hJ.2 (Matrix.det_eq_zero_of_row_eq_zero i₀ hrow)
  refine ⟨Pi.single i₀ 1 + (J i₀ j)⁻¹ • Pi.single j 1, ?_⟩
  have hji : J j i₀ = σ (J i₀ j) := (hJ.1 j i₀).symm
  rw [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, _root_.GlobalTheory.HermLineZeros.hform_expand, _root_.GlobalTheory.HermLineZeros.hform_single,
    _root_.GlobalTheory.HermLineZeros.hform_single, _root_.GlobalTheory.HermLineZeros.hform_single,
    _root_.GlobalTheory.HermLineZeros.hform_single, hd, hd, hji]
  simp only [AlgHom.coe_toRingHom, RingHom.coe_coe]
  rw [inv_mul_cancel₀ hj, ← map_mul, inv_mul_cancel₀ hj, map_one]
  norm_num

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in

theorem _root_.GlobalTheory.HermLineZeros.finite_zeros_on_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K], ∃ y : Fin M → K ⊗[F] E, ∀ x : Fin M → K ⊗[F] E, {t : K | _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR K σ J (x + t • y) = 0}.Finite := by
  intro F E _ _ _ _ _ σ h M hM J hJ K _ _
  obtain ⟨y₀, a, ha, hy⟩ := _root_.GlobalTheory.HermLineZeros.exists_anisotropic h hM hJ
  let φ : E →ₐ[F] K ⊗[F] E := Algebra.TensorProduct.includeRight
  let S := _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR K σ
  let JR := _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (F := F) K J
  set y : Fin M → K ⊗[F] E := fun i => φ (y₀ i)
  refine ⟨y, fun x => ?_⟩
  have hSc : ∀ t : K, S (algebraMap K (K ⊗[F] E) t) = algebraMap K (K ⊗[F] E) t := fun t => by
    simp [S, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply]
  have hSφ : ∀ e : E, S (φ e) = φ (σ e) := fun e => by simp [S, φ, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  have hyy : _root_.Formalism.UG.hform S JR y y = algebraMap K (K ⊗[F] E) (algebraMap F K a) := by
    rw [← IsScalarTower.algebraMap_apply, ← φ.commutes, ← hy]
    simp only [_root_.Formalism.UG.hform, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, map_sum, map_mul, y, hSφ, JR, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.map_apply, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
    rfl
  have htr : Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR y y)
      = Module.finrank K (K ⊗[F] E) • algebraMap F K a := by
    rw [hyy, Algebra.trace_algebraMap]
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have hfr : Module.finrank K (K ⊗[F] E) ≠ 0 := by
    rw [Module.finrank_baseChange, h.2.2.1]; norm_num
  set α := algebraMap F K (1 / 2) * Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR y y) with hα
  set β := algebraMap F K (1 / 2) * Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR x y + _root_.Formalism.UG.hform S JR y x)
  set γ := algebraMap F K (1 / 2) * Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR x x)
  have hα0 : α ≠ 0 := by
    rw [hα, htr]
    refine mul_ne_zero ?_ (smul_ne_zero hfr ?_)
    · rw [Ne, map_eq_zero_iff _ (algebraMap F K).injective]; norm_num
    · rw [Ne, map_eq_zero_iff _ (algebraMap F K).injective]; exact ha
  let p : Polynomial K := Polynomial.C α * Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X + Polynomial.C γ
  have hp : p ≠ 0 := by
    intro hp
    have := congrArg (Polynomial.coeff · 2) hp
    simp [p, Polynomial.coeff_X, Polynomial.coeff_C] at this
    exact hα0 this
  refine (Polynomial.finite_setOf_isRoot hp).subset fun t ht => ?_
  simp only [Set.mem_setOf_eq] at ht ⊢
  rw [Polynomial.IsRoot.def, ← ht]
  have hsmul : t • y = algebraMap K (K ⊗[F] E) t • y := by
    funext i; simp [Algebra.smul_def]
  have hexp := _root_.GlobalTheory.HermLineZeros.hform_expand S JR x y (algebraMap K (K ⊗[F] E) t)
  rw [hSc] at hexp
  have hq : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR K σ J (x + t • y) = algebraMap F K (1 / 2) *
      Algebra.trace K (K ⊗[F] E) (_root_.Formalism.UG.hform S JR (x + algebraMap K (K ⊗[F] E) t • y)
        (x + algebraMap K (K ⊗[F] E) t • y)) := by
    rw [← hsmul]; rfl
  have htc : ∀ z, Algebra.trace K (K ⊗[F] E) (algebraMap K (K ⊗[F] E) t * z)
      = t * Algebra.trace K (K ⊗[F] E) z := fun z => by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [hq, hexp, mul_assoc (algebraMap K (K ⊗[F] E) t), map_add, map_add, map_add, htc, htc, htc, htc]
  simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, α, β, γ, map_add]
  ring

end GlobalTheory.HermLineZeros
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LintegralComplexEqLintegralSqrtMulExpStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_complex_eq_polar_sqrt : ∀ (ε c : ℝ), (ε = 1 ∨ ε = -1) → ∀ g : ℂ → ENNReal, Measurable g → g 0 = 0 → ∫⁻ z, g z = ∫⁻ t : ℝ, ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, (2 : ENNReal)⁻¹ * g ((Real.sqrt (ε * (t - c)) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  first | exact @GlobalTheory.lintegral_complex_eq_lintegral_sqrt_mul_exp | exact GlobalTheory.lintegral_complex_eq_lintegral_sqrt_mul_exp | (intros; apply GlobalTheory.lintegral_complex_eq_lintegral_sqrt_mul_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemOfFiniteDimensionalSpanRightTranslatesStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_finiteDimensional_span_rightTranslates' : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] (R : Subalgebra ℂ (K → ℂ)), (∀ p ∈ R, Continuous p) → (∀ p ∈ R, star p ∈ R) → (∀ x y : K, x ≠ y → ∃ p ∈ R, p x ≠ p y) → (∀ p ∈ R, ∃ (m : ℕ) (a b : Fin m → K → ℂ), (∀ i, a i ∈ R ∧ Continuous (b i)) ∧ ∀ x k, p (x⁻¹ * k) = ∑ i, a i x * b i k) → ∀ f : K → ℂ, Continuous f → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x : K => f (x * k))) → f ∈ R := by
  first | exact @GlobalTheory.UnitaryBC.mem_of_finiteDimensional_span_rightTranslates | exact GlobalTheory.UnitaryBC.mem_of_finiteDimensional_span_rightTranslates | (intros; apply GlobalTheory.UnitaryBC.mem_of_finiteDimensional_span_rightTranslates <;> assumption)
end

