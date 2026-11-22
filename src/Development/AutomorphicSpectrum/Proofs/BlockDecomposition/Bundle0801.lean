import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0797
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0788
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0113
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0084
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderVolumeAlmostAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0798
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0608
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0034
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0789
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0786
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0796
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0794
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0795
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0265
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0423
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0497
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0434
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0496
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0527
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureOrthogonalSumStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fibre_measure_orthogonal_sum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N n : ℕ) (J₂ : Matrix (Fin N) (Fin N) E), IsHermND σ J₂ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m : HermR R σ n → Measure (Fin n → Fin N → R ⊗[F] E), IsGramFibFree R σ J₂ n (coordW R b lam n N) (coordHerm R σ b lam n) m → (∀ S, SFinite (m S)) ∧ (∃ κ : ProbabilityTheory.Kernel (HermR R σ n) (Fin n → Fin N → R ⊗[F] E), ProbabilityTheory.IsSFiniteKernel κ ∧ ∀ S, κ S = m S) ∧ (∀ (C : Set (Fin n → Fin N → R ⊗[F] E)) (D : Set (HermR R σ n)), IsCompact C → C ⊆ {X | LinearIndependent (R ⊗[F] E) X} → IsCompact D → ∃ c : ℝ≥0, ∀ S ∈ D, m S C ≤ c) ∧ ∀ S : HermR R σ n, ∀ᵐ X ∂(m S), gramR R σ J₂ X = (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) ∧ LinearIndependent (R ⊗[F] E) X := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.gramFibFree_basic | exact GlobalTheory.CompanionTheory.SW.StageF.gramFibFree_basic | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.gramFibFree_basic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibrationDisintegrationStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_gram_fibration_disintegration : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree R σ J n μ ν m → ∀ (h : HA R σ J) (S : HermR R σ n), (m S).map (actW R σ J h) = m S := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv.map_actW_fibre_free | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv.map_actW_fibre_free | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv.map_actW_fibre_free <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderVolumeAlmostAllStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_order_volume_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) E), IsHermND σ J → 3 ≤ N → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) → ∀ lam : Measure (Fv F v), IsStdV v lam → ∀ m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin N → Fv F v ⊗[F] E), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 N) (coordHerm (Fv F v) σ b lam 1) m → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (c : O), ¬ IsUnit c → IsUnit (c : Fv F v ⊗[F] E) → ∀ B : Set (Fin 1 → Fin N → Fv F v ⊗[F] E), MeasurableSet B → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) ((fun (X : Fin 1 → Fin N → Fv F v ⊗[F] E) a i => (c : Fv F v ⊗[F] E) * X a i) '' B) ≤ ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) B := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit.fibre_zero_image_le | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit.fibre_zero_image_le | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit.fibre_zero_image_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalRankOneVolumeBound
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.DilPush

theorem push_dil : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (c : ℝ≥0), MeasurableSet P → (∀ S : Set (Fv F v), MeasurableSet S → coordW (Fv F v) b lam 1 M (P ∩ (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) ⁻¹' S) ≤ (c : ℝ≥0∞) * lam S) → ∀ (u : (Fv F v ⊗[F] E)ˣ) (S : Set (Fv F v)), MeasurableSet S → coordW (Fv F v) b lam 1 M ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' P ∩ (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) ⁻¹' S) ≤ ((c * ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ ^ (M - 1) : ℝ≥0) : ℝ≥0∞) * lam S := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM d b v lam hlam P c hP hbound u S hS
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  haveI := hlam.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  set Q : (Fin 1 → Fin M → Fv F v ⊗[F] E) → Fv F v := fun X => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) with hQ
  set D : (Fin 1 → Fin M → Fv F v ⊗[F] E) → (Fin 1 → Fin M → Fv F v ⊗[F] E) := fun X p k => (u : Fv F v ⊗[F] E) * X p k with hD
  set n : Fv F v := Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) with hn
  have hn0 : n ≠ 0 := (u.isUnit.map (Algebra.norm (Fv F v))).ne_zero
  have hdil : ∀ X, Q (D X) = n * Q X := fun X => GlobalTheory.T.trace_gram_unit_scaling F E σ hσ M J hJ v u X
  set S' : Set (Fv F v) := (fun t => n * t) ⁻¹' S with hS'def
  have hmul : Measurable (fun t : Fv F v => n * t) := (continuous_const_mul n).measurable
  have hS' : MeasurableSet S' := hmul hS
  have hset : D '' P ∩ Q ⁻¹' S = D '' (P ∩ Q ⁻¹' S') := by
    ext Y
    constructor
    · rintro ⟨⟨X, hX, rfl⟩, hY⟩
      refine ⟨X, ⟨hX, ?_⟩, rfl⟩
      show n * Q X ∈ S
      rw [← hdil]
      exact hY
    · rintro ⟨X, ⟨hX, hXS⟩, rfl⟩
      refine ⟨⟨X, hX, rfl⟩, ?_⟩
      show Q (D X) ∈ S
      rw [hdil]
      exact hXS
  have hQc : Continuous Q := by
    have h1 : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) :=
      PI.VolStabSW.SdUniqW.continuous_trace_tens (F := F) (E := E) (Fv F v)
    have h2 : Continuous fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => gramR (Fv F v) σ J X 0 0 :=
      (continuous_apply_apply 0 0).comp (PI.VolStabS.continuous_gramR (Fv F v) σ J)
    exact continuous_const.mul (h1.comp h2)
  have hQm : Measurable Q := hQc.measurable
  have hlamS : lam S' = (‖n‖₊ : ℝ≥0∞)⁻¹ * lam S := by
    have h := GlobalTheory.CompanionTheory.SW.ProdFormula.map_mul_left_finite v n hn0 lam hlam.1
    have h2 := congrArg (fun μ : Measure (Fv F v) => μ S) h
    simp only [Measure.smul_apply] at h2
    rw [Measure.map_apply hmul hS] at h2
    rw [hS'def, h2, ENNReal.smul_def, smul_eq_mul]
    simp [ENNReal.coe_inv (nnnorm_ne_zero_iff.2 hn0)]
  rw [hset, GlobalTheory.T.unit_scaling_rank_one_volume F E σ hσ M d b v lam hlam u _ (hP.inter (hQm hS'))]
  set a : ℝ≥0∞ := (‖n‖₊ : ℝ≥0∞) with ha
  have ha0 : a ≠ 0 := by simpa [ha] using hn0
  have hat : a ≠ ⊤ := ENNReal.coe_ne_top
  have hpow : a ^ M = a ^ (M - 1) * a := by rw [← pow_succ, Nat.sub_add_cancel hM]
  have haa : a * a⁻¹ = 1 := ENNReal.mul_inv_cancel ha0 hat
  calc a ^ M * coordW (Fv F v) b lam 1 M (P ∩ Q ⁻¹' S')
      ≤ a ^ M * ((c : ℝ≥0∞) * lam S') := by gcongr; exact hbound S' hS'
    _ = (c : ℝ≥0∞) * a ^ (M - 1) * (a * a⁻¹) * lam S := by rw [hlamS, hpow]; ring
    _ = ((c * ‖n‖₊ ^ (M - 1) : ℝ≥0) : ℝ≥0∞) * lam S := by rw [haa, ha]; push_cast; ring

end GlobalTheory.CompanionTheory.WeilSiegel.DilPush
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemProdSpanInfStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_prodSpan_inf : ∀ {A B : Type} (U₁ S₁ : Submodule ℂ (A → ℂ)) (U₂ S₂ : Submodule ℂ (B → ℂ)) (G : A × B → ℂ), G ∈ prodSpan U₁ U₂ → (∀ y, (fun x => G (x, y)) ∈ S₁) → (∀ x, (fun y => G (x, y)) ∈ S₂) → G ∈ prodSpan (U₁ ⊓ S₁) (U₂ ⊓ S₂) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.Slices.mem_prodSpan_inf_of_slices | exact GlobalTheory.CompanionTheory.LimV.Slices.mem_prodSpan_inf_of_slices | (intros; apply GlobalTheory.CompanionTheory.LimV.Slices.mem_prodSpan_inf_of_slices <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalOfNonIsomorphic
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDisc.Orth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

def fixS (V : Submodule ℂ (Sm E N)) (L : Subgroup (GL (Fin N) (Af E))) : Submodule ℂ (Sm E N) where
  carrier := {x | x ∈ V ∧ ∀ u ∈ L, finRep E N u x = x}
  add_mem' := fun {x y} hx hy => ⟨V.add_mem hx.1 hy.1, fun u hu => by rw [map_add, hx.2 u hu, hy.2 u hu]⟩
  zero_mem' := ⟨V.zero_mem, fun u _ => map_zero _⟩
  smul_mem' := fun c x hx => ⟨V.smul_mem c hx.1, fun u hu => by rw [map_smul, hx.2 u hu]⟩

theorem mem_l2_of_discrete (μ : Measure (GA E N)) [μ.IsHaarMeasure] {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {x : Sm E N}
    (hx : x ∈ V) : x ∈ squareIntegrableSmoothSubmoduleGL μ := mem_l2Sub_of_isAutForm μ (hV.aut x hx) (hV.sqInt x hx)

theorem cont_of_mem {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {x : Sm E N} (hx : x ∈ V) : Continuous x.1 :=
  ContAut.continuous_of_isOpen_stab E N x (hV.aut x hx).level

theorem eq_zero_of_l2Map_eq_zero_of_isDiscrete (μ : Measure (GA E N)) [μ.IsHaarMeasure] {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {x : Sm E N}
    (hx : x ∈ V) (h0 : l2Map μ x = 0) : x = 0 := by
  by_contra hne
  have := re_l2Form_pos μ (mem_l2_of_discrete μ hV hx) (cont_of_mem hV hx) hne
  simp [l2Form, h0] at this

def stabS (x : Sm E N) : Subgroup (GL (Fin N) (Af E)) where
  carrier := {k | finRep E N k x = x}
  mul_mem' := fun {a b} ha hb => by
    change finRep E N (a * b) x = x
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by
    change finRep E N 1 x = x
    rw [map_one, Module.End.one_apply]
  inv_mem' := fun {a} ha => by
    change finRep E N a⁻¹ x = x
    have h : finRep E N a⁻¹ (finRep E N a x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [ha] at h

theorem exists_repr (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {V V' : Submodule ℂ (Sm E N)}
    (hV : IsDiscrete V) (hV' : IsDiscrete V') {x : Sm E N} (hx : x ∈ V) :
    ∃ y ∈ V', ∀ z ∈ V', ⟪l2Map μ z, l2Map μ x⟫_ℂ = ⟪l2Map μ z, l2Map μ y⟫_ℂ := by
  obtain ⟨L, hLS, hLo, hLc⟩ := GlobalTheory.T.exists_open_compact_subgroup_le E N (stabS x) (hV.aut x hx).level
  have hunit : ∀ (k : Kinf E N) {W W' : Submodule ℂ (Sm E N)}, IsDiscrete W → IsDiscrete W' → ∀ a ∈ W, ∀ b ∈ W',
      ⟪l2Map μ (cptRep E N k a), l2Map μ (cptRep E N k b)⟫_ℂ = ⟪l2Map μ a, l2Map μ b⟫_ℂ :=
    fun k _ _ h h' a ha b hb => (GlobalTheory.T.right_translate_isometry E N μ _ a b (mem_l2_of_discrete μ h ha) (mem_l2_of_discrete μ h' hb)).2
  letI : MeasurableSpace (Kinf E N) := borel _
  haveI : BorelSpace (Kinf E N) := ⟨rfl⟩
  haveI : CompactSpace (Kinf E N) := GlobalTheory.KinfCompactness.compactSpace_Kinf E N
  have key := GlobalTheory.T.representation_unitary_average (Measure.haar : Measure (Kinf E N)) (cptRep E N) (l2Map μ) (fixS V L) (fixS V' L)
    (fun g : GA E N => (LinearMap.proj g).comp (Sm E N).subtype)
    (fun k a ha b hb => hunit k hV' hV a ha.1 b hb.1)
    (fun k a ha b hb => hunit k hV' hV' a ha.1 b hb.1)
    (fun a ha => by
      obtain ⟨A, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_finite_dim_compact_stable E N V hV L a ha.1 ha.2
      exact ⟨A, h1, h2, fun b hb => h3 b hb, h4, h5⟩)
    (fun a ha => by
      obtain ⟨A, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_finite_dim_compact_stable E N V' hV' L a ha.1 ha.2
      exact ⟨A, h1, h2, fun b hb => h3 b hb, h4, h5⟩)
    (fun W hW => by
      haveI := GlobalTheory.CompanionTheory.AdmDiscFin.admissible_discrete_spaces E N L W hLo hW V' hV'
      refine Submodule.finiteDimensional_of_le (Submodule.span_mono (t := {φ | φ ∈ V' ∧ TypeB L W φ}) ?_)
      rintro a ⟨ha, hW'⟩
      exact ⟨ha.1, fun u hu g => congrFun (congrArg Subtype.val (ha.2 u hu)) g, hW'⟩)
  have hfx : ∀ u ∈ L, finRep E N u x = x := fun u hu => hLS hu
  obtain ⟨y, hy, hyz⟩ := key x ⟨hx, hfx⟩
  refine ⟨y, hy.1, fun z hz => ?_⟩
  obtain ⟨z', hz', hfix, e⟩ := GlobalTheory.T.exists_invariant_projection E N μ V' hV' L hLc z hz
  rw [e x (mem_l2_of_discrete μ hV hx) hfx, e y (mem_l2_of_discrete μ hV' hy.1) hy.2]
  exact hyz z' ⟨hz', hfix⟩

theorem exists_adj (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (o : Op E N) :
    ∃ o' : Op E N, ∀ {V W : Submodule ℂ (Sm E N)}, IsDiscrete V → IsDiscrete W → ∀ x ∈ V, ∀ y ∈ W,
      ⟪l2Map μ x, l2Map μ (act o y)⟫_ℂ = ⟪l2Map μ (act o' x), l2Map μ y⟫_ℂ := by
  cases o with
  | fin k =>
    refine ⟨.fin k⁻¹, fun {V W} hV hW x hx y hy => ?_⟩
    have h := (GlobalTheory.T.right_translate_isometry E N μ (finGL E N k) (act (.fin k⁻¹) x) y (mem_l2_of_discrete μ hV (hV.stable _ x hx)) (mem_l2_of_discrete μ hW hy)).2
    rw [← h]
    congr 2
    change x = finRep E N k (finRep E N k⁻¹ x)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  | cpt k =>
    refine ⟨.cpt k⁻¹, fun {V W} hV hW x hx y hy => ?_⟩
    have h := (GlobalTheory.T.right_translate_isometry E N μ (infGL E N (Unitary.toUnits k)) (act (.cpt k⁻¹) x) y (mem_l2_of_discrete μ hV (hV.stable _ x hx)) (mem_l2_of_discrete μ hW hy)).2
    rw [← h]
    congr 2
    change x = cptRep E N k (cptRep E N k⁻¹ x)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  | lie X =>
    refine ⟨.lie (-X), fun {V W} hV hW x hx y hy => ?_⟩
    have hxX := hV.stable (.lie X) x hx
    have hyX := hW.stable (.lie X) y hy
    have h := GlobalTheory.T.lie_skew_adjoint_l2' E N μ X x y (cont_of_mem hV hx) (cont_of_mem hW hy) (cont_of_mem hV hxX) (cont_of_mem hW hyX)
      (mem_l2_of_discrete μ hV hx) (mem_l2_of_discrete μ hW hy) (mem_l2_of_discrete μ hV hxX) (mem_l2_of_discrete μ hW hyX)
    have e : act (.lie (-X)) x = - lie E N X x := by
      change lie E N (-X) x = _
      rw [map_neg]; rfl
    rw [e, map_neg, inner_neg_left]
    exact h

theorem isoV_of_ne (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {V V' : Submodule ℂ (Sm E N)}
    (hV : IsDiscrete V) (hV' : IsDiscrete V') {x₀ y₀ : Sm E N} (hx₀ : x₀ ∈ V) (hy₀ : y₀ ∈ V')
    (hne : ⟪l2Map μ y₀, l2Map μ x₀⟫_ℂ ≠ 0) : IsoV V V' := by
  have uniq : ∀ a ∈ V', ∀ b ∈ V', (∀ z ∈ V', ⟪l2Map μ z, l2Map μ a⟫_ℂ = ⟪l2Map μ z, l2Map μ b⟫_ℂ) → a = b := by
    intro a ha b hb h
    have h1 := h (a - b) (V'.sub_mem ha hb)
    rw [← sub_eq_zero, ← inner_sub_right, ← map_sub, inner_self_eq_zero] at h1
    exact sub_eq_zero.1 (eq_zero_of_l2Map_eq_zero_of_isDiscrete μ hV' (V'.sub_mem ha hb) h1)
  choose T hTm hT using fun x : V => exists_repr μ hV hV' x.2
  let Tl : V →ₗ[ℂ] V' :=
    { toFun := fun x => ⟨T x, hTm x⟩
      map_add' := fun x y => Subtype.ext (uniq _ (hTm _) _ (V'.add_mem (hTm x) (hTm y)) fun z hz => by
        rw [← hT _ z hz]
        simp only [Submodule.coe_add, map_add, inner_add_right]
        rw [← hT x z hz, ← hT y z hz])
      map_smul' := fun c x => Subtype.ext (uniq _ (hTm _) _ (V'.smul_mem c (hTm x)) fun z hz => by
        rw [← hT _ z hz]
        simp only [Submodule.coe_smul, map_smul, inner_smul_right, RingHom.id_apply]
        rw [← hT x z hz]) }
  have hTl : ∀ x : V, (Tl x).1 = T x := fun _ => rfl
  have eqv : ∀ (o : Op E N) (x y : V), y.1 = act o x.1 → (Tl y).1 = act o (Tl x).1 := by
    intro o x y hxy
    obtain ⟨o', ho'⟩ := exists_adj μ o
    refine uniq _ (hTm y) _ (hV'.stable o _ (hTm x)) fun z hz => ?_
    rw [hTl, ← hT y z hz, hxy, ho' hV' hV z hz _ x.2, ho' hV' hV' z hz _ (hTm x),
      hT x _ (hV'.stable o' z hz)]
  have hnz : Tl ≠ 0 := by
    intro h0
    apply hne
    have h1 : T ⟨x₀, hx₀⟩ = 0 := congrArg Subtype.val (LinearMap.congr_fun h0 ⟨x₀, hx₀⟩)
    rw [hT ⟨x₀, hx₀⟩ y₀ hy₀, h1, map_zero, inner_zero_right]
  have hker : LinearMap.ker Tl = ⊥ := by
    have hst : IsStable ((LinearMap.ker Tl).map V.subtype) := by
      rintro o _ ⟨x, hx, rfl⟩
      refine ⟨⟨_, hV.stable o _ x.2⟩, ?_, rfl⟩
      refine Subtype.ext ?_
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hx
      rw [eqv o x _ rfl, hx]
      simp
    rcases hV.irred _ (Submodule.map_subtype_le _ _) hst with h | h
    · exact Submodule.map_injective_of_injective V.injective_subtype (by rwa [Submodule.map_bot])
    · exfalso
      refine hnz (LinearMap.ext fun x => ?_)
      have : x.1 ∈ (LinearMap.ker Tl).map V.subtype := by rw [h]; exact x.2
      obtain ⟨x', hx', e⟩ := this
      obtain rfl : x' = x := Subtype.ext e
      exact hx'
  have hran : LinearMap.range Tl = ⊤ := by
    have hst : IsStable ((LinearMap.range Tl).map V'.subtype) := by
      rintro o _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨Tl ⟨_, hV.stable o _ x.2⟩, ⟨_, rfl⟩, eqv o x _ rfl⟩
    rcases hV'.irred _ (Submodule.map_subtype_le _ _) hst with h | h
    · exfalso
      have h1 : LinearMap.range Tl = ⊥ :=
        Submodule.map_injective_of_injective V'.injective_subtype (by rwa [Submodule.map_bot])
      exact hnz (LinearMap.range_eq_bot.1 h1)
    · rw [eq_top_iff]
      intro y _
      have : y.1 ∈ (LinearMap.range Tl).map V'.subtype := by rw [h]; exact y.2
      obtain ⟨y', hy', e⟩ := this
      obtain rfl : y' = y := Subtype.ext e
      exact hy'
  refine ⟨LinearEquiv.ofBijective Tl ⟨LinearMap.ker_eq_bot.1 hker, LinearMap.range_eq_top.1 hran⟩, ?_⟩
  intro o x y hxy
  exact eqv o x y hxy

end GlobalTheory.CompanionTheory.FinDisc.Orth

open GlobalTheory.CompanionTheory.FinDisc.Orth in

theorem GlobalTheory.CompanionTheory.FinDisc.integral_eq_zero_of_not_isoV :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ →
  ∀ V V' : Submodule ℂ (Sm E N), IsDiscrete V → IsDiscrete V' → ¬ IsoV V V' →
    ∀ φ ∈ V, ∀ ψ ∈ V', ∫ x in F, φ.1 x * (starRingEnd ℂ) (ψ.1 x) ∂μ = 0 := by
  intro E _ _ _ N mG bG μ _ F hF V V' hV hV' hno φ hφ ψ hψ
  obtain rfl : mG = borel _ := bG.measurable_eq
  haveI := GlobalTheory.T.haar_right_invariant E N μ
  rw [GlobalTheory.T.integral_eq_l2_inner E N μ F hF φ ψ (mem_l2_of_discrete μ hV hφ) (mem_l2_of_discrete μ hV' hψ)]
  by_contra hne
  exact hno (isoV_of_ne μ hV hV' hφ hψ hne)

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairRestriction
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV

namespace GlobalTheory.CompanionTheory.EGlue.Restrict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem pairSpace_le_prodSpan (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    pairSpace U₁ U₂ ≤ prodSpan (U₁.map (Sm E a).subtype) (U₂.map (Sm E b).subtype) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩
  exact Submodule.subset_span ⟨φ₁.1, ⟨φ₁, h₁, rfl⟩, φ₂.1, ⟨φ₂, h₂, rfl⟩, rfl⟩

theorem prodSpan_le_pairSpace (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    prodSpan (U₁.map (Sm E a).subtype) (U₂.map (Sm E b).subtype) ≤ pairSpace U₁ U₂ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨φ₁, h₁, rfl⟩, _, ⟨φ₂, h₂, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨φ₁, h₁, φ₂, h₂, rfl⟩

theorem slice_mem (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (F : H E a b → ℂ)
    (hF : F ∈ pairSpace U₁ U₂) (m₁ : GA E a) :
    (fun y => F (m₁, y)) ∈ U₂.map (Sm E b).subtype := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, -, φ₂, h₂, rfl⟩ := h
    exact ⟨φ₁.1 m₁ • φ₂, U₂.smul_mem _ h₂, by funext y; simp⟩
  | zero => exact Submodule.zero_mem _
  | add F F' _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul r F _ h => exact Submodule.smul_mem _ r h

end GlobalTheory.CompanionTheory.EGlue.Restrict

namespace GlobalTheory.CompanionTheory.EGlue

theorem pairRestrict_holds : PairRestrict := by
  intro E _ _ _ a b U₁ U₂ U₂' F hF hs
  have hS₂ : ∀ m₁, (fun y => F (m₁, y)) ∈ U₂'.map (Sm E b).subtype := by
    intro m₁
    obtain ⟨φ, -, hφ⟩ := Restrict.slice_mem U₁ U₂ F hF m₁
    exact ⟨φ, hs m₁ φ hφ, hφ⟩
  have h := GlobalTheory.CompanionTheory.LimV.Slices.mem_prodSpan_inf_of_slices (U₁.map (Sm E a).subtype) ⊤
    (U₂.map (Sm E b).subtype) (U₂'.map (Sm E b).subtype) F
    (Restrict.pairSpace_le_prodSpan U₁ U₂ hF) (fun _ => Submodule.mem_top) hS₂
  refine Restrict.prodSpan_le_pairSpace U₁ U₂' ?_
  refine Submodule.span_mono ?_ h
  rintro _ ⟨p, hp, q, hq, rfl⟩
  exact ⟨p, hp.1, q, hq.2, rfl⟩

end GlobalTheory.CompanionTheory.EGlue

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSpaceCarriesFlatStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_space_carries_flat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (e₁ : GA E a → ℂ) (e₂ : GA E b → ℂ) (U₁ U₁' : Submodule ℂ (Sm E a)) (U₂ U₂' : Submodule ℂ (Sm E b)) (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E))) (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) (F : H E a b → ℂ), FlatFn e₁ → FlatFn e₂ → Carries e₁ U₁ U₁' → Carries e₂ U₂ U₂' → F ∈ pairSpace U₁ U₂ → TypeH K₁ K₂ W₁ W₂ F → (fun x => e₁ x.1 * e₂ x.2 * F x) ∈ (pairSpace U₁' U₂' ⊓ typeHF (K₁ ⊓ KO E a) (K₂ ⊓ KO E b) W₁ W₂ : Submodule ℂ (H E a b → ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.pair_carry | exact GlobalTheory.CompanionTheory.LimV.pair_carry | (intros; apply GlobalTheory.CompanionTheory.LimV.pair_carry <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
section
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

noncomputable section

namespace GlobalTheory.CompanionTheory.Godement

open GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.PolesModel

theorem cosetConv_of_continuous_law : ∀ (D : D7) (n : ℕ) (χ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ →
    (∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g,
      φ (p * g) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2) * φ g) →
    (n : ℝ) / 2 < s₁.re → ∀ g : G D n, CosetConv (P D n) (GF D n) φ g := by
  intro D n χ s₁ φ hcont hlaw hs g
  obtain ⟨H, φ₀, -, -, hH, hsec, hne⟩ :=
    GlobalTheory.StdUnn.PolesModel.hypotheses_hold D n 0 (s₁.re : ℂ)
  have hconv0 := GlobalTheory.StdUnn.PolesModel.cosetConv_stdSec hH hsec
    (s := (s₁.re : ℂ)) (by simpa using hs) g
  have hstd : GlobalTheory.StdUnn.stdSec H φ₀ (s₁.re : ℂ) (s₁.re : ℂ) = φ₀ := by
    funext x
    simp [GlobalTheory.StdUnn.stdSec, GlobalTheory.Doubling.npow]
  rw [hstd] at hconv0
  have hK : IsCompact (↑(GlobalTheory.StdUnn.K D n) : Set (G D n)) :=
    GlobalTheory.StdUnn.HeightExists.isCompact_K
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 1 (GlobalTheory.StdUnn.K D n).one_mem)
  obtain ⟨k₀, -, hk₀⟩ := hK.exists_isMinOn ⟨1, (GlobalTheory.StdUnn.K D n).one_mem⟩
    hsec.2.1.norm.continuousOn
  have hc : 0 < ‖φ₀ k₀‖ := norm_pos_iff.mpr (hne k₀)
  have hχ : ∀ u : Circle, ‖(u : ℂ)‖ = 1 := fun u => by
    first
      | exact Circle.norm_coe u
      | exact mem_sphere_zero_iff_norm.mp u.2
      | simp [Circle.abs_coe]
  have key : ∀ x, ‖φ x‖ ≤ C / ‖φ₀ k₀‖ * ‖φ₀ x‖ := by
    intro x
    obtain ⟨p, hp, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n x
    obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hp
    rw [hlaw p hp a ha k, hsec.1 p hp a ha k]
    have hu : IsUnit (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a)) :=
      (Group.isUnit _).map _
    have hr : (0 : ℝ) < (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a) : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hu.ne_zero)
    have hRR : ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
          ((s₁.re : ℂ) + (n : ℂ) / 2)‖ =
        ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
          (s₁ + (n : ℂ) / 2)‖ := by
      simp only [GlobalTheory.Doubling.npow]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_cpow_eq_rpow_re_of_pos hr]
      congr 1 <;> simp
    have hb : ‖φ k‖ ≤ C / ‖φ₀ k₀‖ * ‖φ₀ k‖ := by
      refine le_trans (hC k hk) ?_
      calc C = C / ‖φ₀ k₀‖ * ‖φ₀ k₀‖ := (div_mul_cancel₀ C hc.ne').symm
        _ ≤ C / ‖φ₀ k₀‖ * ‖φ₀ k‖ :=
          mul_le_mul_of_nonneg_left (isMinOn_iff.mp hk₀ k hk) (div_nonneg hC0 hc.le)
    simp only [norm_mul, hχ, hRR]
    calc 1 * ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
            (s₁ + (n : ℂ) / 2)‖ * ‖φ k‖
        ≤ 1 * ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
            (s₁ + (n : ℂ) / 2)‖ * (C / ‖φ₀ k₀‖ * ‖φ₀ k‖) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C / ‖φ₀ k₀‖ * (1 * ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D
            (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2)‖ * ‖φ₀ k‖) := by ring
  unfold GlobalTheory.Eis.CosetConv at hconv0 ⊢
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    (hconv0.mul_left (C / ‖φ₀ k₀‖))
  simp only [GlobalTheory.Eis.term]
  exact key _

end GlobalTheory.CompanionTheory.Godement

end
end

