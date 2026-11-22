import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0143
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0156
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0138
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0081
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0152
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0151
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0144
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueCocycle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0153

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTruncatedFourierTendstoZeroEtale
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.PlancherelZero

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem continuous_char (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous ψ := by
  rw [continuous_iff_continuousAt]
  intro x
  refine (continuousAt_const (y := ψ x)).congr ?_
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with z hz
  have h1 : ψ (z - x) = 1 := hψ.1 _ (by simpa [dist_eq_norm] using hz)
  calc ψ x = ψ x * ψ (z - x) := by rw [h1, mul_one]
    _ = ψ z := by rw [← AddChar.map_add_eq_mul]; congr 1; abel

theorem kerK_eq (A : Et F E) (ψ : AddChar F ℂ) :
    A.kerK ψ = fun x y => ψ (Algebra.traceForm F A.K x y) := by
  funext x y; simp [Et.kerK, Et.psiK, Algebra.traceForm_apply]

theorem continuous_kerK (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (y : A.K) :
    Continuous fun x => A.kerK ψ x y := by
  have hl : Continuous ((Algebra.trace F A.K).comp (LinearMap.mulRight F y)) :=
    IsModuleTopology.continuous_of_linearMap _
  exact ((continuous_char ψ hψ).comp hl).congr (fun x => by simp [Et.kerK, Et.psiK])

theorem integrable_mul_kerK (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μ : Measure A.K)
    [IsFiniteMeasureOnCompacts μ] {f : A.K → ℂ} (hf : IsTest f) (y : A.K) :
    Integrable (fun x => f x * A.kerK ψ x y) μ :=
  (hf.1.continuous.mul (continuous_kerK A ψ hψ y)).integrable_of_hasCompactSupport hf.2.mul_right

theorem fourB_sub (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μ : Measure A.K)
    [IsFiniteMeasureOnCompacts μ] {f g : A.K → ℂ} (hf : IsTest f) (hg : IsTest g) (y : A.K) :
    fourB μ (A.kerK ψ) (f - g) y = fourB μ (A.kerK ψ) f y - fourB μ (A.kerK ψ) g y := by
  unfold fourB
  rw [← integral_sub (integrable_mul_kerK A ψ hψ μ hf y) (integrable_mul_kerK A ψ hψ μ hg y)]
  congr 1; funext x; simp [sub_mul]

theorem lintegral_sq_eq_ofReal {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {g : X → ℂ} (hg : IsTest g) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hc : Continuous fun x => ‖g x‖ ^ 2 := (hg.1.continuous.norm).pow 2
  have hs : HasCompactSupport ((fun z : ℂ => ‖z‖ ^ 2) ∘ g) := hg.2.comp_left (by simp)
  rw [ofReal_integral_eq_lintegral_ofReal (hc.integrable_of_hasCompactSupport hs)
    (ae_of_all _ fun x => by simp only [Pi.zero_apply]; positivity)]
  congr 1; funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

variable [Unram F E]

theorem isTest_fourB (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μK : Measure A.K)
    (hsd : SelfDual μK (A.kerK ψ)) {f : A.K → ℂ} (hf : IsTest f) : IsTest (fourB μK (A.kerK ψ) f) := by
  obtain ⟨-, -, hnd, -⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  rw [kerK_eq A ψ]
  exact (GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm (R := F) (S := A.K)) hnd).2 μK hsd.1 f hf

theorem plancherel (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μK : Measure A.K)
    (hsd : SelfDual μK (A.kerK ψ)) {f : A.K → ℂ} (hf : IsTest f) :
    ∫⁻ y, ‖fourB μK (A.kerK ψ) f y‖ₑ ^ 2 ∂μK = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μK := by
  haveI := hsd.1
  obtain ⟨-, -, hnd, -⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hB := kerK_eq A ψ
  have hP := (GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm (R := F) (S := A.K)) hnd μK
    hsd.1).2 (hB ▸ hsd) f hf
  rw [lintegral_sq_eq_ofReal μK (isTest_fourB A ψ hψ μK hsd hf), lintegral_sq_eq_ofReal μK hf, hB, hP]

end GlobalTheory.PlancherelZero

namespace GlobalTheory.PlancherelZero

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def box (A : Et F E) (c : F) : Set A.K := {z | c • z ∈ A.OK}

theorem isOpen_box (A : Et F E) (hO : IsOpen A.OK) (c : F) : IsOpen (box A c) :=
  hO.preimage (continuous_const_smul c)

theorem isClosed_box (A : Et F E) (hO : IsClosed A.OK) (c : F) : IsClosed (box A c) :=
  hO.preimage (continuous_const_smul c)

theorem isCompact_box (A : Et F E) (hO : IsCompact A.OK) {c : F} (hc : c ≠ 0) : IsCompact (box A c) :=
  (Homeomorph.isCompact_preimage (Homeomorph.smulOfNeZero c hc)).2 hO

theorem isTest_indicator_box (A : Et F E) {u : A.K → ℂ} (hu : IsLocallyConstant u) (hOo : IsOpen A.OK)
    (hOc : IsClosed A.OK) (hOk : IsCompact A.OK) {c : F} (hc : c ≠ 0) : IsTest ((box A c).indicator u) := by
  refine ⟨?_, HasCompactSupport.intro' (isCompact_box A hOk hc) (isClosed_box A hOc c)
    fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ box A c
  · filter_upwards [(isOpen_box A hOo c).mem_nhds hx, (IsLocallyConstant.iff_eventually_eq u).1 hu x] with y hy h
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx, h]
  · filter_upwards [(isClosed_box A hOc c).isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem fourB_indicator_box (A : Et F E) (ψ : AddChar F ℂ) (μ : Measure A.K) (u : A.K → ℂ) (c : F)
    (hM : MeasurableSet (box A c)) (y : A.K) :
    fourB μ (A.kerK ψ) ((box A c).indicator u) y = ∫ z in box A c, u z * A.psiK ψ (-((-y) * z)) ∂μ := by
  unfold fourB
  have h : ∀ x, (box A c).indicator u x * A.kerK ψ x y = (box A c).indicator (fun x => u x * A.kerK ψ x y) x :=
    fun x => by by_cases hx : x ∈ box A c <;> simp [hx]
  simp_rw [h]
  rw [integral_indicator hM]
  congr 1; funext z
  rw [Et.kerK, neg_mul, neg_neg, mul_comm z y]

end GlobalTheory.PlancherelZero

namespace GlobalTheory.PlancherelZero

theorem eq_zero_of_tendsto_fourier : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ (u : A.K → ℂ), IsLocallyConstant u → ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK < ⊤ → (∀ a : A.K, IsUnit a → Tendsto (fun c : F => ∫ z in {z : A.K | c • z ∈ A.OK}, u z * A.psiK ψ (-(a * z)) ∂μK) (𝓝[≠] 0) (𝓝 0)) → u = 0 := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd u hu hT hlim
  haveI := hsd.1
  obtain ⟨-, -, -, -, -, -, -, -, hnull, hOo, hOk, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hOc : IsClosed A.OK := by
    have hRo : IsOpen ((R.toAddSubgroup : AddSubgroup A.K) : Set A.K) := by rw [← hR] at hOo; exact hOo
    rw [← hR]; exact R.toAddSubgroup.isClosed_of_isOpen hRo
  have h0 : (0 : A.K) ∈ A.OK := by rw [← hR]; exact R.zero_mem
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one F
  have hpow : Tendsto (fun n : ℕ => ϖ ^ n) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hϖ1
  have hne : ∀ n : ℕ, ϖ ^ n ≠ 0 := fun n => pow_ne_zero n (norm_pos_iff.1 hϖ0)
  have hpow' : Tendsto (fun n : ℕ => ϖ ^ n) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hpow, Eventually.of_forall hne⟩
  set M : ℕ → Set A.K := fun n => box A (ϖ ^ n) with hMdef
  have hMm : ∀ n, MeasurableSet (M n) := fun n => (isOpen_box A hOo _).measurableSet
  set g : ℕ → A.K → ℂ := fun n => (M n).indicator u with hgdef
  have hg : ∀ n, IsTest (g n) := fun n => isTest_indicator_box A hu hOo hOc hOk (hne n)
  have hTc : ∀ n, Continuous (fourB μK (A.kerK ψ) (g n)) := fun n =>
    (isTest_fourB A ψ hψ μK hsd (hg n)).1.continuous
  have huc : Continuous u := hu.continuous
  have hum : Measurable fun z => ‖u z‖ₑ ^ 2 := (huc.measurable.enorm).pow_const 2
  set b : ℕ → ENNReal := fun n => ∫⁻ z, (M n)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) z ∂μK with hbdef
  have hev : ∀ z : A.K, ∀ᶠ n in atTop, z ∈ M n := by
    intro z
    have ht : Tendsto (fun n : ℕ => ϖ ^ n • z) atTop (𝓝 0) := by
      simpa using hpow.smul_const z
    exact ht (hOo.mem_nhds h0)
  have hb : Tendsto b atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := μK)
      (F := fun n z => (M n)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) z) (f := fun _ => 0) (fun z => ‖u z‖ₑ ^ 2)
      (fun n => hum.indicator (hMm n).compl) (fun n => ae_of_all _ fun z => Set.indicator_le_self _ _ z) hT.ne
      (ae_of_all _ fun z => tendsto_const_nhds.congr'
        ((hev z).mono fun n hn => (Set.indicator_of_notMem (fun h : z ∈ (M n)ᶜ => h hn) _).symm))
    simpa using this
  have hlimF : ∀ y : A.K, IsUnit y → Tendsto (fun n => fourB μK (A.kerK ψ) (g n) y) atTop (𝓝 0) := by
    intro y hy
    exact ((hlim (-y) hy.neg).comp hpow').congr fun n => (fourB_indicator_box A ψ μK u _ (hMm n) y).symm
  have hae : ∀ᵐ y ∂μK, IsUnit y := ae_iff.2 (hnull μK hsd.1)
  have key : ∀ N, ∫⁻ x, ‖g N x‖ₑ ^ 2 ∂μK ≤ b N := by
    intro N
    rw [← plancherel A ψ hψ μK hsd (hg N)]
    have hFd : ∀ n, ∫⁻ y, ‖fourB μK (A.kerK ψ) (g N) y - fourB μK (A.kerK ψ) (g n) y‖ₑ ^ 2 ∂μK
        = ∫⁻ x, ‖g N x - g n x‖ₑ ^ 2 ∂μK := by
      intro n
      have := plancherel A ψ hψ μK hsd (f := g N - g n) ⟨(hg N).1.sub (hg n).1, (hg N).2.sub (hg n).2⟩
      simp only [Pi.sub_apply] at this
      rw [← this]
      congr 1; funext y
      rw [fourB_sub A ψ hψ μK (hg N) (hg n) y]
    have hpt : ∀ n x, ‖g N x - g n x‖ₑ ^ 2 ≤
        (M N)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x + (M n)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x := by
      intro n x
      by_cases h1 : x ∈ M N <;> by_cases h2 : x ∈ M n <;> simp [g, h1, h2]
    have hle : ∀ n, ∫⁻ x, ‖g N x - g n x‖ₑ ^ 2 ∂μK ≤ b N + b n := by
      intro n
      calc _ ≤ ∫⁻ x, ((M N)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x + (M n)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x) ∂μK :=
            lintegral_mono (hpt n)
        _ = b N + b n := lintegral_add_left (hum.indicator (hMm N).compl) _
    have hliminf : ∀ᵐ y ∂μK,
        liminf (fun n => ‖fourB μK (A.kerK ψ) (g N) y - fourB μK (A.kerK ψ) (g n) y‖ₑ ^ 2) atTop
          = ‖fourB μK (A.kerK ψ) (g N) y‖ₑ ^ 2 := by
      filter_upwards [hae] with y hy
      have ht := ((ENNReal.continuous_pow 2).tendsto _).comp
        ((continuous_enorm.tendsto _).comp ((tendsto_const_nhds (x := fourB μK (A.kerK ψ) (g N) y)).sub (hlimF y hy)))
      simpa [Function.comp_def] using ht.liminf_eq
    calc ∫⁻ y, ‖fourB μK (A.kerK ψ) (g N) y‖ₑ ^ 2 ∂μK
        = ∫⁻ y, liminf (fun n => ‖fourB μK (A.kerK ψ) (g N) y - fourB μK (A.kerK ψ) (g n) y‖ₑ ^ 2) atTop ∂μK :=
          lintegral_congr_ae (hliminf.mono fun y h => h.symm)
      _ ≤ liminf (fun n => ∫⁻ y, ‖fourB μK (A.kerK ψ) (g N) y - fourB μK (A.kerK ψ) (g n) y‖ₑ ^ 2 ∂μK) atTop :=
          lintegral_liminf_le' fun n => ((((hTc N).sub (hTc n)).measurable.enorm).pow_const 2).aemeasurable
      _ = liminf (fun n => ∫⁻ x, ‖g N x - g n x‖ₑ ^ 2 ∂μK) atTop := by simp_rw [hFd]
      _ ≤ liminf (fun n => b N + b n) atTop := liminf_le_liminf (Eventually.of_forall hle)
      _ = b N := by
          have : Tendsto (fun n => b N + b n) atTop (𝓝 (b N + 0)) := tendsto_const_nhds.add hb
          simpa using this.liminf_eq
  have hsplit : ∀ N, ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK = ∫⁻ x, ‖g N x‖ₑ ^ 2 ∂μK + b N := by
    intro N
    calc ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK
        = ∫⁻ x, (‖g N x‖ₑ ^ 2 + (M N)ᶜ.indicator (fun z => ‖u z‖ₑ ^ 2) x) ∂μK := by
          congr 1; funext x
          by_cases h : x ∈ M N <;> simp [g, h]
      _ = ∫⁻ x, ‖g N x‖ₑ ^ 2 ∂μK + b N := lintegral_add_right _ (hum.indicator (hMm N).compl)
  have hT0 : ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK = 0 := by
    refine le_antisymm ?_ (by simp)
    have h2 : Tendsto (fun N => b N + b N) atTop (𝓝 0) := by simpa using hb.add hb
    exact ge_of_tendsto' h2 fun N => (hsplit N).trans_le (add_le_add (key N) le_rfl)
  have hae0 : u =ᵐ[μK] 0 := by
    filter_upwards [(lintegral_eq_zero_iff hum).1 hT0] with z hz
    simpa using hz
  exact (Continuous.ae_eq_iff_eq μK huc continuous_const).1 hae0

end GlobalTheory.PlancherelZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyTestFunctionMulInverseUnitEq
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem eventually_isUnit_and_tendsto_inverse_normed (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] (R : Type) [NormedCommRing R] [NormedAlgebra F R] [Module.Finite F R] :
    (∀ᶠ w in 𝓝 (1 : R), IsUnit w) ∧ Tendsto Ring.inverse (𝓝 (1 : R)) (𝓝 1) := by
  have : CompleteSpace R := FiniteDimensional.complete F R
  refine ⟨Units.isOpen.mem_nhds isUnit_one, ?_⟩
  have h := (NormedRing.inverse_continuousAt (1 : Rˣ)).tendsto
  simpa using h

theorem eventually_isUnit_and_tendsto_inverse (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] (R : Type) [CommRing R] [Algebra F R] [Module.Finite F R]
    [τ : TopologicalSpace R] [IsModuleTopology F R] :
    (∀ᶠ w in 𝓝 (1 : R), IsUnit w) ∧ Tendsto Ring.inverse (𝓝 (1 : R)) (𝓝 1) := by
  classical
  have hτ : τ = moduleTopology F R := eq_moduleTopology F R
  let b := Module.finBasis F R
  let : NormedRing (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedRing
  let : NormedAlgebra F (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedAlgebra
  let N : NormedCommRing R := NormedCommRing.induced R _ (Algebra.leftMulMatrix b)
    (Algebra.leftMulMatrix_injective b)
  let A : @NormedAlgebra F R _ N.toNormedRing.toSeminormedRing :=
    NormedAlgebra.induced F R _ (Algebra.leftMulMatrix b)
  have key := @eventually_isUnit_and_tendsto_inverse_normed F _ _ R N A ‹_›
  have hN : N.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      = moduleTopology F R :=
    @finiteNormedAlgebra_eq_moduleTopology F _ _ R N A ‹_›
  rw [hτ, ← hN]
  exact key

theorem eventually_testFn_mul_inverse_eq : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (φ' : A.K × A.K → ℂ), IsTest φ' → ∀ a : A.K, IsUnit a → ∀ᶠ s in 𝓝 a, ∀ t : A.K, IsUnit t → φ' (s * Ring.inverse t, t) = φ' (a * Ring.inverse t, t) := by
  intro F E _ _ _ _ hU A φ' hφ a ha
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : CompleteSpace F := inferInstance
  obtain ⟨hunit, hinv⟩ := eventually_isUnit_and_tendsto_inverse F A.K
  have hC : IsCompact (tsupport φ') := hφ.2
  have H1 : ∀ᶠ w in 𝓝 (1 : A.K), ∀ q ∈ tsupport φ', φ' (q.1 * w, q.2) = φ' q := by
    refine hC.eventually_forall_of_forall_eventually fun p _ => ?_
    have hc : Tendsto (fun z : A.K × (A.K × A.K) => (z.2.1 * z.1, z.2.2)) (𝓝 (1, p)) (𝓝 p) := by
      have : Continuous (fun z : A.K × (A.K × A.K) => (z.2.1 * z.1, z.2.2)) := by fun_prop
      simpa using this.tendsto (1, p)
    have hl : ∀ᶠ q in 𝓝 p, φ' q = φ' p := hφ.1.eventually_eq p
    have h2 : Tendsto (fun z : A.K × (A.K × A.K) => z.2) (𝓝 (1, p)) (𝓝 p) := continuous_snd.tendsto _
    filter_upwards [hc.eventually hl, h2.eventually hl] with z hz1 hz2
    exact hz1.trans hz2.symm
  have H2 : ∀ᶠ w in 𝓝 (1 : A.K), ∀ q : A.K × A.K, φ' (q.1 * w, q.2) = φ' q := by
    filter_upwards [hunit, hinv.eventually H1, H1] with w hw hw' h1 q
    by_cases hq : q ∈ tsupport φ'
    · exact h1 q hq
    by_cases hq' : (q.1 * w, q.2) ∈ tsupport φ'
    · have := hw' _ hq'
      simp only [mul_assoc, Ring.mul_inverse_cancel w hw, mul_one] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hq, image_eq_zero_of_notMem_tsupport hq']
  have hT : Tendsto (fun s : A.K => Ring.inverse a * s) (𝓝 a) (𝓝 1) := by
    have : Continuous (fun s : A.K => Ring.inverse a * s) := by fun_prop
    simpa [Ring.inverse_mul_cancel a ha] using this.tendsto a
  filter_upwards [hT.eventually H2] with s hs t _
  have := hs (a * Ring.inverse t, t)
  have e : a * Ring.inverse t * (Ring.inverse a * s) = s * Ring.inverse t := by
    calc a * Ring.inverse t * (Ring.inverse a * s) = (a * Ring.inverse a) * s * Ring.inverse t := by ring
      _ = s * Ring.inverse t := by rw [Ring.mul_inverse_cancel a ha, one_mul]
  simpa [e] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEmbOfFixed
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.Letters

theorem exists_emb_of_fixed {F E L : Type} [Field F] [Field E] [Field L] [Algebra F E] [Algebra F L]
    [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : Function.Bijective σ)
    (hfix : ∀ x, σ x = x → ∃ c : F, algebraMap F E c = x) (e : E →ₐ[F] L) :
    ∃ emb : ZMod (Module.finrank F E) → (E →ₐ[F] L),
      Function.Bijective emb ∧ ∀ i, (emb (i + 1)).comp σ = emb i := by
  classical
  let g : E ≃ₐ[F] E := AlgEquiv.ofBijective σ hσ
  have hbot : IntermediateField.fixedField (Subgroup.zpowers g) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    exact IntermediateField.mem_bot.2 (hfix x (hx g (Subgroup.mem_zpowers g)))
  have hord : orderOf g = Module.finrank F E := by
    have h := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers g)
    rw [hbot, IntermediateField.finrank_bot', Nat.card_zpowers] at h
    exact h.symm
  haveI : NeZero (Module.finrank F E) := ⟨Module.finrank_pos.ne'⟩
  let emb : ZMod (Module.finrank F E) → (E →ₐ[F] L) := fun i =>
    e.comp (g⁻¹ ^ i.val : E ≃ₐ[F] E).toAlgHom
  have hord' : orderOf g⁻¹ = Module.finrank F E := by rw [orderOf_inv, hord]
  have hinj : Function.Injective emb := by
    intro i j h
    have h1 : (g⁻¹ ^ i.val : E ≃ₐ[F] E) = g⁻¹ ^ j.val :=
      AlgEquiv.ext fun x => e.injective (DFunLike.congr_fun h x)
    rw [pow_eq_pow_iff_modEq, hord', ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val] at h1
    exact h1
  refine ⟨emb, ?_, fun i => ?_⟩
  · refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_zmod]
    exact card_algHom_le_finrank F E L
  · have h1 : (g⁻¹ ^ (i + 1).val : E ≃ₐ[F] E) = g⁻¹ ^ (i.val + 1) := by
      rw [pow_eq_pow_iff_modEq, hord', ← ZMod.natCast_eq_natCast_iff]
      simp
    have h2 : (g⁻¹ ^ (i + 1).val : E ≃ₐ[F] E) * g = g⁻¹ ^ i.val := by
      rw [h1, pow_succ, inv_mul_cancel_right]
    exact AlgHom.ext fun x => congrArg e (DFunLike.congr_fun h2 x)

variable {l : ℕ} [Fact l.Prime]

theorem sigma_fixed (P : LocPrime l) (K : FinExt l) (x : ↥(K0 K)) (hx : (P.PD K).σ x = x) :
    ∃ c : ℚ_[l], algebraMap ℚ_[l] ↥(K0 K) c = x := by
  haveI : Nontrivial P.R.B := by
    refine ⟨⟨(P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h, map_zero]
    exact zero_mem _
  obtain ⟨c, hc⟩ := (P.PD K).fund (algebraMap ↥(K0 K) P.R.B x) (by rw [(P.PD K).φ_K₀, hx]) (by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR,
      Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (P.PD K).one_mem)
  refine ⟨c, (algebraMap ↥(K0 K) P.R.B).injective ?_⟩
  rw [← IsScalarTower.algebraMap_apply, hc]

end GlobalTheory.HWL.Letters

namespace GlobalTheory.HWL

theorem exists_letters : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∃ emb : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1), Function.Bijective emb ∧ ∀ i, (emb (i + 1)).comp (P.PD K).σ = emb i := by
  intro l _ P K s LL h
  haveI := (P.PD K).finK₀
  have hle : K0 K ≤ LL.1 := fun x hx =>
    h.2.2.2 (Ks K s).val ⟨x, (le_sup_left : K0 K ≤ Ks K s) hx⟩
  exact Letters.exists_emb_of_fixed _ (P.PD K).σ_bij (Letters.sigma_fixed P K)
    (IntermediateField.inclusion hle)

end GlobalTheory.HWL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPowMovesPadicRootOfUnityStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_pow_moves_padic_rootOfUnity : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}, FiniteDimensional ℚ_[p] K →
    ∀ k : ℕ, 0 < k → ∃ (σ : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 ∧ (σ ^ k) ζ ≠ ζ := by
  first | exact @GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity | exact GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity | (intros; apply GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLtCommutatorMemOfNeTopStatement
section
open GlobalTheory.BI GlobalTheory.BrauerZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gt_commutator_mem_of_ne_whole : ∀ {G : Type} [Group G] [Finite G] [Group.IsNilpotent G] (K : Subgroup G), K ≠ ⊤ → ∃ A : Subgroup G, K < A ∧ ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ K := by
  first | exact @GlobalTheory.exists_lt_commutator_mem_of_ne_top | exact GlobalTheory.exists_lt_commutator_mem_of_ne_top | (intros; apply GlobalTheory.exists_lt_commutator_mem_of_ne_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenCompactAnnihilatorScaledIntegersKStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openCompact_annihilator_scaled_integersK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ c : F, c ≠ 0 → ∃ D : AddSubgroup A.K, (D : Set A.K) = {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1} ∧ IsOpen (D : Set A.K) ∧ IsCompact (D : Set A.K) := by
  first | exact @GlobalTheory.JR.DualScaledIntegers.exists_open_compact_annihilator | exact GlobalTheory.JR.DualScaledIntegers.exists_open_compact_annihilator | (intros; apply GlobalTheory.JR.DualScaledIntegers.exists_open_compact_annihilator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualHaarHyperbolicKernelPsiKStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_haar_hyperbolicKernelPsiK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ x : A.Kˣ, ∃ ν : Measure A.K, SelfDual ν (Hyp.kx A ψ x) := by
  first | exact @GlobalTheory.JR.Hyp.selfDual_kx_exists | exact GlobalTheory.JR.Hyp.selfDual_kx_exists | (intros; apply GlobalTheory.JR.Hyp.selfDual_kx_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTotallyPositiveApproxAtFinitePlacesStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_totallyPositive_approx_at_finite_places : ∀ (F : Type) [Field F] [NumberField F] (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (t : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → F) (M : ℕ), ∃ a : F, (∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ))) ∧ ∀ φ : F →+* ℝ, 0 < φ a := by
  first | exact @GlobalTheory.FinPlaceApproxPos.approxpos_target | exact GlobalTheory.FinPlaceApproxPos.approxpos_target | (intros; apply GlobalTheory.FinPlaceApproxPos.approxpos_target <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueCocycleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_cocycle_alt : ∀ (l : ℕ) [Fact l.Prime] (G M : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [T2Space M] (a : G → (M →+ M)), (∀ x, a 1 x = x) → (∀ g h x, a (g * h) x = a g (a h x)) → Continuous (fun p : G × M => a p.1 p.2) → ∀ T : AddSubgroup M, IsCompact (T : Set M) → (∀ g, ∀ t ∈ T, a g t ∈ T) → (∀ U ∈ nhds (0 : M), ∃ k : ℕ, ∀ t ∈ T, l ^ k • t ∈ U) → ∀ (lam : G →* Multiplicative ℤ_[l]) (g₀ : G), Continuous lam → lam g₀ = Multiplicative.ofAdd 1 → ∀ b z : M, (∀ h, lam h = 1 → a h z = z ∧ a h b - b ∈ T) → z - (a g₀ b - b) ∈ T → ∃! c : G → M, Continuous c ∧ (∀ g, c g ∈ T) ∧ (∀ g h, c (g * h) = c g + a g (c h)) ∧ (∀ h, lam h = 1 → c h = -(a h b - b)) ∧ ∀ g, lam g = Multiplicative.ofAdd 1 → c g = z - (a g b - b) := by
  first | exact @GlobalTheory.HlCoc.exists_unique_cocycle | exact GlobalTheory.HlCoc.exists_unique_cocycle | (intros; apply GlobalTheory.HlCoc.exists_unique_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitLat
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL

noncomputable def unitLat (G : Type) [Group G] [TopologicalSpace G] (Qp LL O : Type) [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] (hO : Function.Injective (algebraMap O LL)) : LocLat G Qp LL O where
  V := LL
  ρ := Representation.trivial LL G LL
  cont := fun x => by simpa using continuous_const
  L :=
    { T := Submodule.span O {1}
      fg := Submodule.fg_span_singleton _
      free := Module.Free.of_equiv
        ((LinearEquiv.ofInjective (LinearMap.toSpanSingleton O LL 1)
          (fun a b h => hO (by simpa [Algebra.smul_def] using h))).trans
          (LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range O LL 1).symm))
      span := by
        rw [Submodule.span_span_of_tower, eq_top_iff]
        intro x _
        exact Submodule.mem_span_singleton.2 ⟨x, by simp⟩
      stable := fun g x hx => by simpa using hx }

theorem exists_unitLat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), ∃ one : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), (∀ g x, one.ρ g x = x) ∧ ∃ e : one.V, e ≠ 0 ∧ one.L.T = Submodule.span ↥(OL LL) {e} := by
  intro l _ K LL
  have hO : Function.Injective (algebraMap (↥(OL LL)) ↥LL.1) :=
    Subtype.val_injective
  refine ⟨unitLat (↥(GK K)) ℚ_[l] ↥LL.1 ↥(OL LL) hO, fun _ _ => rfl, (1 : ↥LL.1), ?_, rfl⟩
  show (1 : ↥LL.1) ≠ 0
  exact one_ne_zero

end GlobalTheory.HWL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCardTorsionLevelFractionRingQuotStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_card_torsionLevel_fractionRingQuot : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    {ϖ : O}, Irreducible ϖ → ∀ {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) → ∀ n : ℕ,
    Finite (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) ∧
      Nat.card (GlobalTheory.ShapeNeg.Lev M (ϖ ^ n)) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  first | exact @GlobalTheory.ShapeNeg.levKO_card | exact GlobalTheory.ShapeNeg.levKO_card | (intros; apply GlobalTheory.ShapeNeg.levKO_card <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1H2LocalStatement
section
open Formalism.GaloisCohomology ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_H1_H2_local : LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (GK l K) M), 0 < r → ContAction rho → Finite (H1 rho) ∧ Finite (H2 rho) := by
  first | exact @GlobalTheory.finite_H1_H2_of_localTateDuality | exact GlobalTheory.finite_H1_H2_of_localTateDuality | (intros; apply GlobalTheory.finite_H1_H2_of_localTateDuality <;> assumption)
end

