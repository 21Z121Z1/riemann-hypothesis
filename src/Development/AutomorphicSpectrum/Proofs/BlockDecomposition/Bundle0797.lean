import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0788
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0023
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0033
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0008
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0038
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0113
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0084
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0789
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0792
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentExtendByUnitVector
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree

variable {K : Type} [CommRing K] {M n : ℕ}

theorem sum_vec_zero (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) (g : Fin (n + 1) → K) :
    (∑ a, g a • (vec α c X : Fin (n + 1) → Fin (M + 1) → K) a) 0
      = g 0 * α + ∑ j : Fin n, g j.succ * c j := by
  rw [Finset.sum_apply, Fin.sum_univ_succ]
  simp [vec]

theorem sum_vec_succ (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) (g : Fin (n + 1) → K)
    (i : Fin M) :
    (∑ a, g a • (vec α c X : Fin (n + 1) → Fin (M + 1) → K) a) i.succ
      = (∑ j : Fin n, g j.succ • X j) i := by
  rw [Finset.sum_apply, Fin.sum_univ_succ, Finset.sum_apply]
  simp [vec]

theorem linearIndependent_vec_iff (K : Type) [CommRing K] (M n : ℕ) (α : K) (hα : IsUnit α)
    (c : Fin n → K) (X : Fin n → Fin M → K) :
    LinearIndependent K (vec α c X : Fin (n + 1) → Fin (M + 1) → K) ↔ LinearIndependent K X := by
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  constructor
  · intro h w hw j
    obtain ⟨β, hβ⟩ := hα.exists_left_inv
    have key := h (Fin.cons (-(∑ j : Fin n, w j * c j) * β) w) (by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [sum_vec_zero]
        simp only [Fin.cons_zero, Fin.cons_succ, Pi.zero_apply]
        rw [mul_assoc, hβ]
        ring
      · rw [sum_vec_succ]
        simp only [Fin.cons_succ, Pi.zero_apply]
        rw [hw]
        rfl) j.succ
    simpa using key
  · intro h w hw
    have hs : ∀ j : Fin n, w j.succ = 0 := by
      refine h (fun j => w j.succ) ?_
      funext i
      have := congrFun hw i.succ
      rwa [sum_vec_succ] at this
    have h0 : w 0 = 0 := by
      have := congrFun hw 0
      rw [sum_vec_zero] at this
      simp only [hs, zero_mul, Finset.sum_const_zero, add_zero, Pi.zero_apply] at this
      exact (hα.mul_left_eq_zero).1 this
    intro a
    refine Fin.cases h0 hs a

end GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureExtensionByOne
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF.ToOld

theorem linearIndependent_of_isUnit_gram {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E)
    (h : IsUnit (gramR R σ J X).det) : LinearIndependent (R ⊗[F] E) X := by
  rw [Fintype.linearIndependent_iff]
  intro w hw
  have hj : ∀ j, ∑ b, w b * X b j = 0 := fun j => by
    have := congrFun hw j
    simpa [Finset.sum_apply] using this
  have hmul : (gramR R σ J X).mulVec w = 0 := by
    funext a
    show ∑ b, hform (sigR R σ) (JR R J) (X a) (X b) * w b = 0
    simp only [hform, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : ∑ b, sigR R σ (X a i) * JR R J i j * X b j * w b =
        sigR R σ (X a i) * JR R J i j * ∑ b, w b * X b j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [this, hj j, mul_zero]
  have h1 := congrArg (Matrix.mulVec (gramR R σ J X)⁻¹) hmul
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
  exact fun i => congrFun h1 i

open Classical in

theorem isFibreFamily_restrict {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure V) (f : V → Y) (ι : X → Y) (U W : Set V) (ν : Measure X)
    (B : Set X) (fib : X → Measure V) (hUW : U ⊆ W) (hU : MeasurableSet U)
    (hUB : ∀ v b, f v = ι b → (v ∈ U ↔ b ∈ B))
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι W ν Set.univ fib) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B (fun b => if b ∈ B then fib b else 0) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hs ht => ?_⟩
  · by_cases hb : b ∈ B
    · simp only [hb, if_true]
      refine measure_mono_null (Set.compl_subset_compl.2 fun v hv => ⟨hv.1, ?_⟩) (h1 b)
      exact (hUB v b hv.1).2 hb
    · simp [hb]
  · have key := h2 (U.indicator φ) (hφ.indicator hU)
    rw [lintegral_indicator hU, Measure.restrict_restrict hU, Set.inter_eq_left.2 hUW] at key
    rw [key]
    refine lintegral_congr fun b => ?_
    have hae : ∀ᵐ v ∂(fib b), f v = ι b := by
      have : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {ι b} ∩ W := mem_ae_iff.2 (h1 b)
      filter_upwards [this] with v hv using hv.1
    by_cases hb : b ∈ B
    · simp only [hb, if_true]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with v hv
      exact Set.indicator_of_mem ((hUB v b hv).2 hb) φ
    · simp only [hb, if_false, lintegral_zero_measure]
      refine (lintegral_congr_ae (g := fun _ => 0) ?_).trans lintegral_zero
      filter_upwards [hae] with v hv
      exact Set.indicator_of_notMem (fun hvU => hb ((hUB v b hv).1 hvU)) φ
  · obtain ⟨k1, k2⟩ := h3 φ hc hs (ht.trans hUW)
    refine ⟨fun b hb => ?_, ?_⟩
    · simpa only [hb, if_true] using k1 b (Set.mem_univ b)
    · exact (k2.mono (Set.subset_univ B)).congr fun b hb => by simp only [hb, if_true]

theorem stageData_of_stageDataF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∃ m₀ : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E), StageData σ J t n b lam m₁ m₀ s B₀ a κ₁ cm := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨iTR, iLC, iSC, iT2, -⟩ := id D.hR
  haveI := iTR; haveI := iLC; haveI := iSC; haveI := iT2
  obtain ⟨kTR, kLC, kSC, kT2, -, -, -, kB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI := kTR; haveI := kLC; haveI := kSC; haveI := kT2
  haveI := kB n M
  obtain ⟨-, -, -, -, hg⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R n
  obtain ⟨g, gc, hgg⟩ := hg M J D.hJ
  have hopen : IsOpen (Unt σ R n) := by
    have hu : IsOpen {x : R ⊗[F] E | IsUnit x} := by
      have := (GlobalTheory.T.units_open_embedding_local_tensor F E σ D.hCM R D.hR).isOpen_range
      convert this using 1
      ext x
      simp [IsUnit]
    have hc : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      continuous_subtype_val.matrix_det
    exact hu.preimage hc
  have hset : {X | IsUnit (gramR R σ J X).det} = g ⁻¹' (Unt σ R n) := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Unt, hgg X]
  have hmeas : MeasurableSet {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} := by
    rw [hset]
    exact (hopen.preimage gc).measurableSet
  have hfam := isFibreFamily_restrict (coordW R b lam n M) (gramR R σ J) Subtype.val
    {X | IsUnit (gramR R σ J X).det} {X | LinearIndependent (R ⊗[F] E) X} (coordHerm R σ b lam n)
    {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} m'
    (fun X hX => linearIndependent_of_isUnit_gram R σ J X hX) hmeas
    (fun X S hX => by simp only [Set.mem_setOf_eq, hX]) D.hm'
  exact ⟨_, { hCM := D.hCM, hJ := D.hJ, ht := D.ht, hR := D.hR, hlam := D.hlam, hm₁ := D.hm₁, hm' := hfam,
              hs := D.hs, hsec := D.hsec, hcpt := D.hcpt, hB₀ := D.hB₀, htB := D.htB, hac := D.hac,
              hoff := D.hoff, hsq := D.hsq, ha1 := D.ha1, hκc := D.hκc, hκ1 := D.hκ1, hscale := D.hscale,
              hcmc := D.hcmc, hmod := D.hmod }⟩

end GlobalTheory.CompanionTheory.SW.StageF.ToOld
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureOrthogonalSum
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageF

theorem isSFiniteKernel_of_compact_open {α β : Type} [MeasurableSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [BorelSpace β] [T2Space β] (κ : ProbabilityTheory.Kernel α β)
    {K : ℕ → Set β} (hK : ∀ k, IsCompact (K k)) {U : Set β} (hU : (⋃ k, K k) = U)
    (hc : ∀ a, κ a Uᶜ = 0) (hf : ∀ a k, κ a (K k) < ⊤) : ProbabilityTheory.IsSFiniteKernel κ := by
  let C : ℕ → Set β := disjointed K
  have hCm : ∀ k, MeasurableSet (C k) := fun k =>
    MeasurableSet.disjointed (fun i => (hK i).measurableSet) k
  have hCd : Pairwise (Function.onFun Disjoint C) := disjoint_disjointed _
  have hCu : ⋃ k, C k = U := by
    simp only [C, iUnion_disjointed]
    exact hU
  have hk : ∀ k, ProbabilityTheory.IsSFiniteKernel (ProbabilityTheory.Kernel.restrict κ (hCm k)) := fun k =>
    isSFiniteKernel_of_forall_univ_lt_top _ (fun a => by
      rw [ProbabilityTheory.Kernel.restrict_apply]
      simpa using (measure_mono (disjointed_subset _ k)).trans_lt (hf a k))
  have hsum : κ = ProbabilityTheory.Kernel.sum fun k => ProbabilityTheory.Kernel.restrict κ (hCm k) := by
    ext a s hs
    rw [ProbabilityTheory.Kernel.sum_apply]
    simp only [ProbabilityTheory.Kernel.restrict_apply]
    rw [← Measure.restrict_iUnion hCd hCm, hCu,
      Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 (hc a))]
  rw [hsum]
  infer_instance

theorem gramFibFree_basic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N n : ℕ) (J₂ : Matrix (Fin N) (Fin N) E), IsHermND σ J₂ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m : HermR R σ n → Measure (Fin n → Fin N → R ⊗[F] E), IsGramFibFree R σ J₂ n (coordW R b lam n N) (coordHerm R σ b lam n) m → (∀ S, SFinite (m S)) ∧ (∃ κ : ProbabilityTheory.Kernel (HermR R σ n) (Fin n → Fin N → R ⊗[F] E), ProbabilityTheory.IsSFiniteKernel κ ∧ ∀ S, κ S = m S) ∧ (∀ (C : Set (Fin n → Fin N → R ⊗[F] E)) (D : Set (HermR R σ n)), IsCompact C → C ⊆ {X | LinearIndependent (R ⊗[F] E) X} → IsCompact D → ∃ c : ℝ≥0, ∀ S ∈ D, m S C ≤ c) ∧ ∀ S : HermR R σ n, ∀ᵐ X ∂(m S), gramR R σ J₂ X = (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) ∧ LinearIndependent (R ⊗[F] E) X := by
  intro F E _ _ _ _ _ σ hCM N n J₂ hJ R _ _ _ _ _ hR d b lam hlam m hm
  obtain ⟨iTR, iLC, iSC, iT2, -⟩ := id hR
  haveI := iTR; haveI := iLC; haveI := iSC; haveI := iT2
  obtain ⟨kTR, kLC, kSC, kT2, -, -, -, kB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := kTR; haveI := kLC; haveI := kSC; haveI := kT2
  haveI := kB n N
  obtain ⟨hLC, hSC, hT2, hB, -⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hCM R n
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB
  have hU : IsOpen {X : Fin n → Fin N → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    GlobalTheory.T.linearly_independent_frames_open F E σ hCM R hR n N
  obtain ⟨h1, -, h3⟩ := hm
  have hbf : GlobalTheory.CompanionTheory.SW.FibreFam.BumpFamily {X : Fin n → Fin N → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}
      (Set.univ : Set (HermR R σ n)) m :=
    ⟨fun S hS => absurd (Set.mem_univ S) hS, h3⟩
  have hUc : ∀ S, m S {X : Fin n → Fin N → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}ᶜ = 0 := fun S =>
    measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_right) (h1 S)
  have hmeas : ∀ A : Set (Fin n → Fin N → R ⊗[F] E), MeasurableSet A → Measurable fun S => m S A :=
    fun A hA => hbf.measurable_apply isOpen_univ hU hUc hA
  let κ : ProbabilityTheory.Kernel (HermR R σ n) (Fin n → Fin N → R ⊗[F] E) :=
    ⟨m, Measure.measurable_of_measurable_coe _ hmeas⟩
  obtain ⟨K, W, hK, -, -, hKU, -, -, hKun, -⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.exists_exhaustion hU
  haveI hκ : ProbabilityTheory.IsSFiniteKernel κ :=
    isSFiniteKernel_of_compact_open κ hK hKun hUc
      (fun S k => hbf.lt_top hU (hK k) (hKU k) S)
  refine ⟨fun S => (inferInstance : SFinite (κ S)), ⟨κ, hκ, fun _ => rfl⟩, ?_, fun S => ?_⟩
  · intro C D hC hCU hD
    obtain ⟨φ, hc, hcs, hs, h0, -, hone⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.exists_bump hC hU hCU
    obtain ⟨hi, hco⟩ := h3 φ hc hcs hs
    obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn (hco.mono (Set.subset_univ D))
    refine ⟨M.toNNReal, fun S hS => ?_⟩
    calc m S C ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂(m S) :=
          GlobalTheory.CompanionTheory.SW.FibreFam.le_lintegral_bump _ hC h0 hone
      _ = ENNReal.ofReal (∫ v, φ v ∂(m S)) :=
          (ofReal_integral_eq_lintegral_ofReal (hi S (Set.mem_univ S))
            (Filter.Eventually.of_forall h0)).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM S hS))
      _ = (M.toNNReal : ℝ≥0∞) := rfl
  · have : ∀ᵐ X ∂(m S), X ∈ gramR R σ J₂ ⁻¹' {((S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E))} ∩
        {X : Fin n → Fin N → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
      mem_ae_iff.2 (h1 S)
    filter_upwards [this] with X hX
    exact ⟨hX.1, hX.2⟩

end GlobalTheory.CompanionTheory.SW.StageF
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibrationDisintegration
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv

theorem isFibreFamily_map_homeo {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [MeasurableSpace X] (μ : Measure V) (ν : Measure X) (f : V → Y) (ι : X → Y)
    (e : V ≃ₜ V) (hf : ∀ v, f (e v) = f v) (U : Set V) (hU : e ⁻¹' U = U) (hμ : μ.map e = μ)
    (B : Set X) (fib : X → Measure V) (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B fib) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B (fun b => (fib b).map e) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  refine ⟨?_, ?_, ?_⟩
  · intro b
    have hset : e ⁻¹' (f ⁻¹' {ι b} ∩ U)ᶜ = (f ⁻¹' {ι b} ∩ U)ᶜ := by
      rw [Set.preimage_compl, Set.preimage_inter, hU]
      congr 2
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hf]
    show ((fib b).map e) _ = 0
    rw [hemb.map_apply, hset]
    exact h1 b
  · intro φ hφ
    have hr : μ.restrict U = (μ.restrict U).map e := by
      have := hemb.restrict_map μ U
      rw [hμ, hU] at this
      exact this
    rw [hr, hemb.lintegral_map, h2 (fun v => φ (e v)) (hφ.comp e.measurable)]
    refine lintegral_congr fun b => ?_
    simp only [hemb.lintegral_map]
  · intro φ hφ hcs hts
    have hts' : tsupport (φ ∘ e) ⊆ U := by
      rw [tsupport_comp_eq_preimage, ← hU]
      exact Set.preimage_mono hts
    obtain ⟨hi, hcont⟩ := h3 (φ ∘ e) (hφ.comp e.continuous)
      (hcs.comp_isClosedEmbedding e.isClosedEmbedding) hts'
    refine ⟨fun b hb => ?_, ?_⟩
    · rw [hemb.integrable_map_iff]
      exact hi b hb
    · have : (fun b => ∫ v, φ v ∂((fib b).map e)) = fun b => ∫ v, (φ ∘ e) v ∂(fib b) := by
        funext b
        exact hemb.integral_map φ
      rw [this]
      exact hcont

theorem linearIndependent_mulVec {K : Type} [CommRing K] {M n : ℕ} (g : GL (Fin M) K) (X : Fin n → Fin M → K)
    (hX : LinearIndependent K X) :
    LinearIndependent K (fun a => (g : Matrix (Fin M) (Fin M) K).mulVec (X a)) := by
  have hinj : Function.Injective (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) K)) := by
    intro x y hxy
    have h2 := congrArg (((g⁻¹ : GL (Fin M) K) : Matrix (Fin M) (Fin M) K).mulVec) hxy
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h2
    exact h2
  exact hX.map' (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) K)) (LinearMap.ker_eq_bot.2 hinj)

theorem map_actW_fibre_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree R σ J n μ ν m → ∀ (h : HA R σ J) (S : HermR R σ n), (m S).map (actW R σ J h) = m S := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm h S
  have hR' := hR
  obtain ⟨_, _, _, _, -, -, -, -⟩ := hR'
  obtain ⟨_, _, _, _, -, -, -, hbor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  have hbor' := hbor n M
  obtain ⟨_, _, _, _, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  obtain ⟨g, hgc, hgf⟩ := hlift M J hJ
  obtain ⟨_, -, -, -, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hσ M J hJ R
  obtain ⟨hcont, hone, hmul, hgr⟩ := hact n
  have hcg : ∀ k : HA R σ J, Continuous (actW R σ J k : (Fin n → Fin M → R ⊗[F] E) → _) := fun k =>
    hcont.comp (Continuous.prodMk_right k)
  let e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := actW R σ J h
      invFun := actW R σ J h⁻¹
      left_inv := fun X => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun X => by rw [← hmul, mul_inv_cancel, hone]
      continuous_toFun := hcg h
      continuous_invFun := hcg h⁻¹ }
  let W : Set (Fin n → Fin M → R ⊗[F] E) := {X | LinearIndependent (R ⊗[F] E) X}
  have hWo : IsOpen W := GlobalTheory.T.linearly_independent_frames_open F E σ hσ R hR n M
  have hfree : ∀ (k : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), X ∈ W → actW R σ J k X ∈ W :=
    fun k X hX => linearIndependent_mulVec (HA.mat R σ J k) X hX
  have hU : e ⁻¹' W = W := by
    ext X
    refine ⟨fun hX => ?_, hfree h X⟩
    have h2 : actW R σ J h⁻¹ (actW R σ J h X) ∈ W := hfree h⁻¹ _ hX
    have h3 : actW R σ J h⁻¹ (actW R σ J h X) = X := by rw [← hmul, inv_mul_cancel, hone]
    rw [h3] at h2
    exact h2
  have hμm : μ.map e = μ := GlobalTheory.T.unitary_action_preserves_haar_local F E σ hσ M J hJ R hR n μ hμ h
  have ht := isFibreFamily_map_homeo μ ν (gramR R σ J) Subtype.val e (fun X => hgr h X) W hU hμm
    Set.univ m hm
  have hm0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (g ⁻¹' Set.univ ∩ W) ν Set.univ m := by
    rw [Set.preimage_univ, Set.univ_inter]
    exact hm
  have ht0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (g ⁻¹' Set.univ ∩ W) ν Set.univ
      (fun b => (m b).map e) := by
    rw [Set.preimage_univ, Set.univ_inter]
    exact ht
  exact GlobalTheory.T.measurable_embedding_of_injective_proper _ _ _ μ ν (gramR R σ J) g Subtype.val Subtype.val_injective hgc hgf W hWo Set.univ Set.univ
    isOpen_univ isOpen_univ subset_rfl m (fun b => (m b).map e) hm0 ht0 S (Set.mem_univ S)

end GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemProdSpanInf
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.Slices

variable {A B : Type}

theorem span_eval_eq_top (W : Submodule ℂ (B → ℂ)) [FiniteDimensional ℂ W] :
    Submodule.span ℂ (Set.range fun y : B =>
      ((LinearMap.proj y : (B → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype : Module.Dual ℂ W)) = ⊤ := by
  set E := Submodule.span ℂ (Set.range fun y : B =>
      ((LinearMap.proj y : (B → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype : Module.Dual ℂ W)) with hE
  have hbot : E.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    have : (w : B → ℂ) = 0 := by
      funext y
      exact hw _ (Submodule.subset_span ⟨y, rfl⟩)
    exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
  have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := E)
  rw [hbot] at h
  rw [← h]
  simp

theorem mem_prodSpan_inf_left (U S : Submodule ℂ (A → ℂ)) (V : Submodule ℂ (B → ℂ))
    (G : A × B → ℂ) (hG : G ∈ prodSpan U V) (hS : ∀ y, (fun x => G (x, y)) ∈ S) :
    G ∈ prodSpan (U ⊓ S) V := by
  obtain ⟨n, f, g, hsum⟩ := Submodule.mem_span_set'.1 hG
  choose a ha b hb hg using fun i => (g i).2
  let W : Submodule ℂ (B → ℂ) := Submodule.span ℂ (Set.range b)
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
  have hWV : W ≤ V := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i)
  let bw : Fin n → W := fun i => ⟨b i, Submodule.subset_span ⟨i, rfl⟩⟩
  let T : A → W := fun x => ∑ i, (f i * a i x) • bw i
  have hG' : ∀ x y, G (x, y) = ∑ i, f i * a i x * b i y := by
    intro x y
    rw [← hsum]
    simp only [Finset.sum_apply, Pi.smul_apply, hg, smul_eq_mul, mul_assoc]
  have hT : ∀ x y, (T x : B → ℂ) y = G (x, y) := by
    intro x y
    rw [hG']
    simp [T, bw]
  have hφS : ∀ φ : Module.Dual ℂ W, (fun x => φ (T x)) ∈ S := by
    intro φ
    have hφ : φ ∈ Submodule.span ℂ (Set.range fun y : B =>
        ((LinearMap.proj y : (B → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype : Module.Dual ℂ W)) := by
      rw [span_eval_eq_top]; trivial
    induction hφ using Submodule.span_induction with
    | mem φ h =>
      obtain ⟨y, rfl⟩ := h
      simpa [hT] using hS y
    | zero => exact S.zero_mem
    | add φ ψ _ _ h₁ h₂ => exact S.add_mem h₁ h₂
    | smul r φ _ h => exact S.smul_mem r h
  have hφU : ∀ φ : Module.Dual ℂ W, (fun x => φ (T x)) ∈ U := by
    intro φ
    have : (fun x => φ (T x)) = ∑ i, (f i * φ (bw i)) • a i := by
      funext x
      simp only [T, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    exact U.sum_mem fun i _ => U.smul_mem _ (ha i)
  let c := Module.finBasis ℂ W
  have hdec : G = ∑ j, fun p : A × B => c.coord j (T p.1) * (c j : B → ℂ) p.2 := by
    funext ⟨x, y⟩
    rw [← hT, Finset.sum_apply]
    have h := congrArg (fun w : W => (w : B → ℂ) y) (c.sum_repr (T x))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h
    simpa [Module.Basis.coord_apply] using h.symm
  rw [hdec]
  exact Submodule.sum_mem _ fun j _ => Submodule.subset_span
    ⟨_, ⟨hφU (c.coord j), hφS (c.coord j)⟩, _, hWV (c j).2, rfl⟩

theorem swap_mem_prodSpan (U : Submodule ℂ (A → ℂ)) (V : Submodule ℂ (B → ℂ))
    (G : A × B → ℂ) (hG : G ∈ prodSpan U V) : (fun p : B × A => G p.swap) ∈ prodSpan V U := by
  induction hG using Submodule.span_induction with
  | mem F h =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    exact Submodule.subset_span ⟨b, hb, a, ha, by funext p; simp [mul_comm]⟩
  | zero => exact Submodule.zero_mem _
  | add F F' _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul r F _ h => exact Submodule.smul_mem _ r h

theorem mem_prodSpan_inf_of_slices : ∀ {A B : Type} (U₁ S₁ : Submodule ℂ (A → ℂ))
    (U₂ S₂ : Submodule ℂ (B → ℂ)) (G : A × B → ℂ), G ∈ prodSpan U₁ U₂ →
    (∀ y, (fun x => G (x, y)) ∈ S₁) → (∀ x, (fun y => G (x, y)) ∈ S₂) →
    G ∈ prodSpan (U₁ ⊓ S₁) (U₂ ⊓ S₂) := by
  intro A B U₁ S₁ U₂ S₂ G hG h₁ h₂
  have hL := mem_prodSpan_inf_left U₁ S₁ U₂ G hG h₁
  have hR := mem_prodSpan_inf_left U₂ S₂ (U₁ ⊓ S₁) (fun p : B × A => G p.swap)
    (swap_mem_prodSpan _ _ G hL) (fun x => h₂ x)
  simpa using swap_mem_prodSpan _ _ _ hR

end GlobalTheory.CompanionTheory.LimV.Slices

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureIntegralPointsNonzeroStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_measure_integral_points_nonzero : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀, ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → nuT hn I μ x₀ {z | IntOff S z.1 ∧ IntOff S z.2} ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.nuT_intOff_ne_zero | exact GlobalTheory.CompanionTheory.ColumnSplitting.nuT_intOff_ne_zero | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.nuT_intOff_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaTotalStatement
section
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_theta_total : WeilCont → FockTranslateSchwartzMajorant → FockTotal → OneTotal := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.OneRow.oneTotal | exact GlobalTheory.CompanionTheory.ThTot.OneRow.oneTotal | (intros; apply GlobalTheory.CompanionTheory.ThTot.OneRow.oneTotal <;> assumption)
end

