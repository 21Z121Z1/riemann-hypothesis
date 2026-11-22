import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0038
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0033
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0031
import Formalism.GL3MeanSquares.Bundle0001
import Formalism.GL3MeanSquares.HookFormulaTorsion.GlobalBoundRefinements
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedIntertwinerDecompOfQuadraticKernel

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRayClassLFunctionRealZeroFarFromOneStatement
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rayClassLFunction_real_zero_far_from_one : ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (β : ℝ), χ * χ = 1 → 3 / 4 ≤ β → 𝓕.F χ β = 0 → c / 𝓕.B ^ A ≤ 1 - β := by
  first | exact @GlobalTheory.Hk.LFam.real_zero_far_from_one | exact GlobalTheory.Hk.LFam.real_zero_far_from_one | (intros; apply GlobalTheory.Hk.LFam.real_zero_far_from_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRepPatchTwistStatement
section
open Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rep_agreeing_on_kernels : ∀ (Γ k : Type) [Group Γ] [Field k] (n : ℕ) (ρ₀ ρ' : Γ →* GL (Fin n) k) (η₀ η : Γ →* ℤˣ) (P : GL (Fin n) k) (s : Γ), η₀ s = 1 → η s = -1 → (∀ g, η₀ g = 1 → η g = 1 → ρ' g = P⁻¹ * ρ₀ g * P) → (∀ Y : Matrix (Fin n) (Fin n) k, (∀ g, η₀ g = 1 → η g = 1 → ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * Y = Y * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) → ((ρ₀ s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * Y = Y * ((ρ₀ s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) → ∃ ρ : Γ →* GL (Fin n) k, (∀ g, η₀ g = 1 → ρ g = ρ₀ g) ∧ ∀ g, η g = 1 → ρ g = P * ρ' g * P⁻¹ := by
  first | exact @GlobalTheory.exists_rep_patch_twist | exact GlobalTheory.exists_rep_patch_twist | (intros; apply GlobalTheory.exists_rep_patch_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsResidueEqZeroIff
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.ResidueBoxVolume

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in

theorem _root_.GlobalTheory.ResidueBoxVolume.exists_residue_eq_zero_iff {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    (∃ y : v.adicCompletionIntegers F, x = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧
      IsLocalRing.residue (v.adicCompletionIntegers F) y = 0) ↔ Valued.v x < 1 := by
  constructor
  · rintro ⟨y, rfl, hy⟩
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hy
    exact lt_of_le_of_ne ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).1 y.2) hy
  · intro hx
    refine ⟨⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).2 hx.le⟩, rfl, ?_⟩
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hx.ne

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
theorem _root_.GlobalTheory.ResidueBoxVolume.isOpen_val_lt_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen {x : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v | Valued.v x < 1} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [Valued.mem_nhds]
  refine ⟨1, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have hy' : y = (y - x) + x := by ring
  rw [hy']
  exact Valuation.map_add_lt _ (by simpa using hy) hx

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {V : Type}
  [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι] in
private theorem mem_residue_box_singleton_iff (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))
    (s : ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F)) (x : V) :
    (∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({s} : Set _)) ↔
    ∀ i, ∃ y : v.adicCompletionIntegers F, e x i = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧
      IsLocalRing.residue (v.adicCompletionIntegers F) y = s i := by
  simp only [Set.mem_singleton_iff, funext_iff]
  constructor
  · rintro ⟨y, h1, h2⟩ i
    exact ⟨y i, h1 i, h2 i⟩
  · intro h
    choose y hy1 hy2 using h
    exact ⟨y, hy1, hy2⟩

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
private theorem exists_residue_eq_iff_exists_residue_sub_eq_zero {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)
    (c : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) (t : v.adicCompletionIntegers F)
    (ht : IsLocalRing.residue (v.adicCompletionIntegers F) t = c) :
    (∃ y : v.adicCompletionIntegers F, a = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧
      IsLocalRing.residue (v.adicCompletionIntegers F) y = c) ↔
    ∃ y : v.adicCompletionIntegers F, a - t = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧
      IsLocalRing.residue (v.adicCompletionIntegers F) y = 0 := by
  constructor
  · rintro ⟨y, rfl, hy⟩
    exact ⟨y - t, rfl, by rw [map_sub, hy, ht, sub_self]⟩
  · rintro ⟨y, hy, hy0⟩
    refine ⟨y + t, ?_, by rw [map_add, hy0, ht, zero_add]⟩
    show a = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) + (t : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)
    rw [← hy]
    ring

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {V : Type}
  [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι] in
private theorem exists_residueBox_eq_preimage_add_lemma_2 (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))
    (s : ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :
    ∃ w : V, {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({s} : Set _)} =
      (fun x => x + w) ⁻¹' {x | ∃ y : ι → v.adicCompletionIntegers F,
        (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
        (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({0} : Set _)} := by
  choose t ht using fun i => IsLocalRing.residue_surjective (s i)
  refine ⟨-e.symm (fun i => (t i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)), ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_residue_box_singleton_iff, Pi.zero_apply,
    map_add, map_neg, map_sub, ContinuousLinearEquiv.apply_symm_apply, Pi.add_apply,
    Pi.neg_apply, Pi.sub_apply, ← sub_eq_add_neg]
  exact forall_congr' fun i => exists_residue_eq_iff_exists_residue_sub_eq_zero v _ _ _ (ht i)

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {V : Type}
  [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι] in
private theorem measurableSet_residue_box_zero (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) :
    MeasurableSet {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({0} : Set _)} := by
  have h : {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({0} : Set _)} =
      ⋂ i, (fun x => e x i) ⁻¹' {a : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v | Valued.v a < 1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, mem_residue_box_singleton_iff,
      Pi.zero_apply, _root_.GlobalTheory.ResidueBoxVolume.exists_residue_eq_zero_iff]
  rw [h]
  exact (isOpen_iInter_of_finite fun i =>
    (_root_.GlobalTheory.ResidueBoxVolume.isOpen_val_lt_one v).preimage ((continuous_apply i).comp e.continuous)).measurableSet

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {V : Type}
  [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι] in
private theorem measure_residueBox_lemma (μ : Measure V) [μ.IsAddHaarMeasure]
    (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))
    (S : Set (ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F))) :
    μ {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ S} =
    S.ncard * μ {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({0} : Set _)} := by
  classical
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    _root_.GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have hS : S.Finite := S.toFinite
  have hunion : {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ S} =
      ⋃ s ∈ hS.toFinset, {x | ∃ y : ι → v.adicCompletionIntegers F,
        (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
        (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({s} : Set _)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.Finite.mem_toFinset, Set.mem_singleton_iff,
      exists_prop]
    constructor
    · rintro ⟨y, h1, h2⟩
      exact ⟨_, h2, y, h1, rfl⟩
    · rintro ⟨s, hs, y, h1, rfl⟩
      exact ⟨y, h1, hs⟩
  rw [hunion, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl fun s _ => ?_, Finset.sum_const, nsmul_eq_mul,
      Set.ncard_eq_toFinset_card S hS]
    obtain ⟨w, hw⟩ := exists_residueBox_eq_preimage_add_lemma_2 e s
    rw [hw, measure_preimage_add_right]
  · intro s _ s' _ hss'
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨y, h1, h2⟩ ⟨y', h1', h2'⟩
    apply hss'
    have hyy : y = y' := funext fun i => Subtype.ext ((h1 i).symm.trans (h1' i))
    subst hyy
    rw [Set.mem_singleton_iff] at h2 h2'
    rw [← h2, ← h2']
  · intro s _
    obtain ⟨w, hw⟩ := exists_residueBox_eq_preimage_add_lemma_2 e s
    rw [hw]
    exact (measurableSet_residue_box_zero e).preimage (continuous_add_right w).measurable

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in

theorem _root_.GlobalTheory.ResidueBoxVolume.measureReal_residueBox (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (V : Type) [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ι : Type) [Fintype ι] (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) (S : Set (ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F))) :
    μ.real {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧ (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ S} * (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) : ℝ) ^ Fintype.card ι = (S.ncard : ℝ) * μ.real {x | ∀ i, e x i ∈ v.adicCompletionIntegers F} := by
  have hB : {x | ∀ i, e x i ∈ v.adicCompletionIntegers F} =
      {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
        (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ Set.univ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, and_true]
    constructor
    · intro h
      exact ⟨fun i => ⟨e x i, h i⟩, fun i => rfl⟩
    · rintro ⟨y, hy⟩ i
      rw [hy i]
      exact (y i).2
  rw [hB, measureReal_def, measureReal_def, measure_residueBox_lemma μ e Set.univ, measure_residueBox_lemma μ e S,
    Set.ncard_univ, Nat.card_fun, Nat.card_eq_fintype_card (α := ι), ENNReal.toReal_mul,
    ENNReal.toReal_mul]
  simp only [Nat.cast_pow, ENNReal.toReal_natCast, ENNReal.toReal_pow]
  ring

end GlobalTheory.ResidueBoxVolume
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteQuadraticCharactersInAdjointStatement
section
open Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_quadratic_characters_in_adjoint' : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (r : Γ →* GL (Fin n) k), Set.Finite {χ : Γ →* ℤˣ | ∃ X : Matrix (Fin n) (Fin n) k, X ≠ 0 ∧ ∀ g, ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = ((χ g : ℤ) : k) • (X * ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))} := by
  first | exact @GlobalTheory.finite_quadratic_characters_in_adjoint | exact GlobalTheory.finite_quadratic_characters_in_adjoint | (intros; apply GlobalTheory.finite_quadratic_characters_in_adjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldIffNoResidualRoot
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.QuadFieldCriterion
open Polynomial IsLocalRing

theorem exists_root_of_residual {O : Type*} [CommRing O] [IsLocalRing O]
    [HenselianRing O (maximalIdeal O)] (t n : O) (hd : IsUnit (t ^ 2 - 4 * n))
    (r : ResidueField O) (hr : r ^ 2 - residue O t * r + residue O n = 0) :
    ∃ s : O, s ^ 2 - t * s + n = 0 := by
  obtain ⟨r₀, rfl⟩ := residue_surjective r
  have hmon : (X ^ 2 - C t * X + C n : O[X]).Monic := by monicity!
  have h0 : r₀ ^ 2 - t * r₀ + n ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff]; simpa using hr
  obtain ⟨s, hs, -⟩ := HenselianRing.is_henselian (I := maximalIdeal O) _ hmon r₀
    (by simpa using h0) (by
      have h1 : IsUnit (residue O (t ^ 2 - 4 * n)) := hd.map _
      have h2 : residue O (t ^ 2 - 4 * n) = (residue O (2 * r₀ - t)) ^ 2 := by
        simp only [map_sub, map_pow, map_mul, map_ofNat]
        linear_combination (-4) * hr
      rw [h2, isUnit_pow_iff two_ne_zero] at h1
      have h3 : eval r₀ (derivative (X ^ 2 - C t * X + C n : O[X])) = 2 * r₀ - t := by
        simp; norm_num
      rw [h3]
      exact h1)
  exact ⟨s, by simpa using hs⟩

theorem exists_root_of_fraction {O K : Type*} [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    [Field K] [Algebra O K] [IsFractionRing O K] (t n : O) (x : K)
    (hx : x ^ 2 - algebraMap O K t * x + algebraMap O K n = 0) :
    ∃ s : O, s ^ 2 - t * s + n = 0 := by
  have hmon : (X ^ 2 - C t * X + C n : O[X]).Monic := by monicity!
  have hi : IsIntegral O x := ⟨_, hmon, by simpa using hx⟩
  obtain ⟨s, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  refine ⟨s, IsFractionRing.injective O K ?_⟩
  simpa using hx

theorem isField_iff_no_root {K A : Type*} [Field K] [CommRing A] [Algebra K A] (w : A) (t n : K)
    (hw : w ^ 2 - algebraMap K A t * w + algebraMap K A n = 0)
    (hspan : ∀ z : A, ∃ a b : K, z = algebraMap K A a + algebraMap K A b * w)
    (hind : ∀ a b : K, algebraMap K A a + algebraMap K A b * w = 0 → a = 0 ∧ b = 0) :
    IsField A ↔ ¬ ∃ x : K, x ^ 2 - t * x + n = 0 := by
  constructor
  · rintro hF ⟨x, hx⟩
    letI := hF.toField
    have hx' : algebraMap K A x ^ 2 - algebraMap K A t * algebraMap K A x + algebraMap K A n = 0 := by
      simpa using congrArg (algebraMap K A) hx
    have hprod : (algebraMap K A (-x) + algebraMap K A 1 * w) *
        (algebraMap K A (x - t) + algebraMap K A 1 * w) = 0 := by
      simp only [map_neg, map_sub, map_one]
      linear_combination hw - hx'
    rcases mul_eq_zero.mp hprod with h | h
    · exact one_ne_zero (hind _ _ h).2
    · exact one_ne_zero (hind _ _ h).2
  · intro hno
    refine ⟨⟨1, 0, fun h => one_ne_zero (hind 1 0 (by simpa using h)).1⟩, mul_comm, ?_⟩
    intro z hz
    obtain ⟨a, b, rfl⟩ := hspan z
    have hN : a ^ 2 + t * a * b + n * b ^ 2 ≠ 0 := by
      intro hN
      by_cases hb : b = 0
      · subst hb
        have : a = 0 := by simpa using hN
        subst this
        simp at hz
      · exact hno ⟨-a / b, by field_simp; linear_combination hN⟩
    refine ⟨algebraMap K A (a ^ 2 + t * a * b + n * b ^ 2)⁻¹ *
      (algebraMap K A a + algebraMap K A b * (algebraMap K A t - w)), ?_⟩
    have h1 : algebraMap K A (a ^ 2 + t * a * b + n * b ^ 2)⁻¹ *
        algebraMap K A (a ^ 2 + t * a * b + n * b ^ 2) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hN, map_one]
    rw [← h1]
    simp only [map_add, map_mul, map_pow]
    linear_combination (- algebraMap K A (a ^ 2 + t * a * b + n * b ^ 2)⁻¹ *
      algebraMap K A b ^ 2) * hw

theorem isField_iff_no_residual_root : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (A : Type) [CommRing A] [Algebra (Fv F v) A] (w : A) (t n : v.adicCompletionIntegers F), IsUnit (t ^ 2 - 4 * n) → w ^ 2 - algebraMap (Fv F v) A t * w + algebraMap (Fv F v) A n = 0 → (∀ z : A, ∃ a b : Fv F v, z = algebraMap (Fv F v) A a + algebraMap (Fv F v) A b * w) → (∀ a b : Fv F v, algebraMap (Fv F v) A a + algebraMap (Fv F v) A b * w = 0 → a = 0 ∧ b = 0) → (IsField A ↔ ¬ ∃ r : IsLocalRing.ResidueField (v.adicCompletionIntegers F), r ^ 2 - IsLocalRing.residue (v.adicCompletionIntegers F) t * r + IsLocalRing.residue (v.adicCompletionIntegers F) n = 0) := by
  intro F _ _ v A _ _ w t n hd hw hspan hind
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  rw [isField_iff_no_root w _ _ hw hspan hind]
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨s, hs⟩ := exists_root_of_fraction (K := Fv F v) t n x hx
    exact ⟨residue _ s, by simpa using congrArg (residue _) hs⟩
  · rintro ⟨r, hr⟩
    obtain ⟨s, hs⟩ := exists_root_of_residual t n hd r hr
    exact ⟨(s : Fv F v), by
      simpa using congrArg (algebraMap (v.adicCompletionIntegers F) (Fv F v)) hs⟩

end GlobalTheory.QuadFieldCriterion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiProductOfThetaWeber
section
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber

namespace GlobalTheory.ThetaWeberRoad

theorem jacobiProduct_of_thetaWeber {τ : UpperHalfPlane} (hTW : ThetaWeber τ)
    (hw : weberF τ * weberF₁ τ * weberF₂ τ = ((Real.sqrt 2 : ℝ) : ℂ)) : JacobiProduct τ := by
  obtain ⟨h1, h2, h3⟩ := hTW
  unfold JacobiProduct
  rw [h1, h2, h3]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  linear_combination (ModularForm.eta (τ : ℂ)) ^ 3 *
    (weberF τ * weberF₁ τ * weberF₂ τ + ((Real.sqrt 2 : ℝ) : ℂ)) * hw +
    ModularForm.eta (τ : ℂ) ^ 3 * hs

theorem thetaWeberStatement_of (hTL : Formalism.L2.Th1.F.ThetaLine) (hSB : Formalism.L2.Th1.F.SgStarBasic)
    (hSA : Formalism.L2.Th1.F.SgStarAdd) : ThetaWeberStatement := by
  have hTW := GlobalTheory.T.thetaConstEqEtaWeberSq_of_tripleProduct GlobalTheory.T.jacobiTripleProduct_twoVariableTheta
  have hJ : ∀ τ : UpperHalfPlane, JacobiProduct τ := fun τ ↦
    jacobiProduct_of_thetaWeber (hTW τ) (GlobalTheory.T.weberFunction_product_eq_sqrt_two τ)
  have hH := GlobalTheory.T.halfPeriodDiffThetaFourth_of_sigmaStar_addition hSA (GlobalTheory.T.gaussianOddJacobiTheta_eq_deriv_mul_sgStar hTL hSB) (GlobalTheory.T.hasDerivAt_oddJacobiTheta_zero_eta_cube GlobalTheory.T.jacobiTripleProduct_twoVariableTheta) hJ
  intro τ
  exact ⟨hH τ, hJ τ, hTW τ, GlobalTheory.T.weberFunctionsRootsOfCubic_of_halfPeriodDiff τ (hH τ) (hJ τ) (hTW τ)⟩

end GlobalTheory.ThetaWeberRoad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimesAPIntervalOfPrimesRel
section
open Finset Formalism.HermitianLattices.GL2PrimeSums

namespace GlobalTheory.Lin

open Finset in

theorem _root_.GlobalTheory.Lin.primesAPInterval_of_primesRel (h : _root_.GlobalTheory.Lin.PrimesRel) :
    ∃ C₀ Cr cr c : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < c ∧ _root_.Formalism.HermitianLattices.GL2PrimeSums.PrimesAPInterval C₀ Cr cr c := by
  unfold _root_.GlobalTheory.Lin.PrimesRel at h
  obtain ⟨c₁, c₂, c₃, CA, cS, hc₁, hc₁8, hc₂, hc₃, hCA, hcS, hmain⟩ := h
  set cr := min c₃ (Real.sqrt c₃) with hcr
  have hcr0 : 0 < cr := lt_min hc₃ (Real.sqrt_pos.mpr hc₃)
  have hdata : _root_.Formalism.HermitianLattices.GlobalBoundRefinements.PrimeCountAsymptoticInProgressions c₂ CA cr cS := by
    unfold _root_.Formalism.HermitianLattices.GlobalBoundRefinements.PrimeCountAsymptoticInProgressions
    intro m a hm ha
    haveI : NeZero m := ⟨by omega⟩
    obtain ⟨huniq, hgap, hcount⟩ := hmain m hm
    have hm1 : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
    have hlogm : 0 < Real.log m := Real.log_pos hm1
    have hlog4m : Real.log m ≤ Real.log (4 * m) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog3 : 1 < Real.log m := by
      rw [Real.lt_log_iff_exp_lt (by positivity)]
      have : (3 : ℝ) ≤ m := by exact_mod_cast hm
      linarith [Real.exp_one_lt_d9]

    have hterm : ∃ (θ : ℤ) (β : ℝ), θ ∈ ({-1, 0, 1} : Set ℤ) ∧
        (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cS / ((4 * (m : ℝ)) ^ 2 * Real.log (4 * m)) ≤ 1 - β) ∧
        _root_.GlobalTheory.Lin.ExcData c₁ m a θ β := by
      by_cases hex : ∃ (χ : DirichletCharacter ℂ m) (β : ℝ), _root_.GlobalTheory.Lin.IsExc c₁ χ β
      · obtain ⟨χ, β, hχ⟩ := hex
        have hunit : IsUnit (a : ZMod m) := (ZMod.isUnit_iff_coprime a m).mpr ha
        have hsq : χ (a : ZMod m) ^ 2 = 1 := by
          rw [← MulChar.pow_apply' χ (by norm_num), hχ.1, MulChar.one_apply hunit]
        obtain ⟨θ, hθ, hθmem⟩ : ∃ θ : ℤ, χ (a : ZMod m) = θ ∧ θ ∈ ({-1, 0, 1} : Set ℤ) := by
          have hsq' : χ (a : ZMod m) * χ (a : ZMod m) = 1 := by rw [← pow_two]; exact hsq
          rcases mul_self_eq_one_iff.mp hsq' with h1 | h1
          · exact ⟨1, by simp [h1], by simp⟩
          · exact ⟨-1, by simp [h1], by simp⟩
        refine ⟨θ, β, hθmem, fun _ => ⟨?_, hχ.2.2.1, ?_⟩, Or.inr ⟨χ, hχ, hθ⟩⟩
        · have h1 := hχ.2.1
          have : c₁ / Real.log m ≤ 1 / 2 := by
            rw [div_le_iff₀ hlogm]
            linarith
          linarith
        · refine le_trans ?_ (hgap χ β hχ)
          apply div_le_div_of_nonneg_left hcS.le (by positivity)
          have : (m : ℝ) ^ 2 ≤ (4 * m) ^ 2 := by
            apply pow_le_pow_left₀ (by positivity)
            linarith
          exact mul_le_mul this hlog4m hlogm.le (by positivity)
      · refine ⟨0, 1 / 2, by simp, fun h0 => absurd rfl h0, Or.inl ⟨rfl, fun χ β hχ => hex ⟨χ, β, hχ⟩⟩⟩
    obtain ⟨θ, β, hθmem, hβ, hdat⟩ := hterm
    refine ⟨θ, β, fun _ => 0, hθmem, hβ,
      fun _ => ⟨le_rfl, mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))⟩, ?_⟩
    intro Y hY
    have hY1 : (m : ℝ) ^ c₂ ≤ Y := by
      refine le_trans ?_ hY
      exact Real.rpow_le_rpow (by positivity) (by linarith) hc₂.le
    have hb := hcount a θ β ha hdat Y hY1
    have hY1' : 1 ≤ Y := le_trans (Real.one_le_rpow (by linarith) hc₂.le) hY1
    have hL : 0 ≤ Real.log Y := Real.log_nonneg hY1'
    have hpos : 0 < CA * (Real.exp (-c₃ * Real.log Y / Real.log m) +
        Real.exp (-√(c₃ * Real.log Y))) := by
      positivity
    have hE : 0 ≤ _root_.Formalism.HermitianLattices.GL2PrimeSums.Emain θ β Y :=
      (mul_nonneg_iff_of_pos_left hpos).mp ((abs_nonneg _).trans hb)
    have h1 : Real.exp (-c₃ * Real.log Y / Real.log m) ≤
        Real.exp (-cr * Real.log Y / Real.log (4 * m)) := by
      rw [Real.exp_le_exp, neg_mul, neg_mul, neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right (min_le_left _ _) hL)
        hlogm hlog4m
    have h2 : Real.exp (-√(c₃ * Real.log Y)) ≤ Real.exp (-cr * √(Real.log Y)) := by
      rw [Real.exp_le_exp, neg_mul, neg_le_neg_iff, Real.sqrt_mul hc₃.le]
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)
    simp only [add_zero]
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ hE)
    unfold _root_.Formalism.HermitianLattices.GL2PrimeSums.rhoErr
    rw [mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 hCA.le) (mul_le_mul_of_nonneg_left h2 hCA.le)
  obtain ⟨C₀', c, hC₀', hc, hint⟩ := _root_.Formalism.HermitianLattices.GlobalBoundRefinements.shortIntervalImpliesProgressions_statement _root_.Formalism.HermitianLattices.GlobalBoundRefinements.shortIntervalLowerBound c₂ CA cr cS hc₂ hCA hcr0 hcS hdata
  exact ⟨C₀', CA, cr, c, hC₀', hCA, hcr0, hc, hint⟩

end GlobalTheory.Lin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistedIntertwinerDecompOfQuadraticKernelStatement
section
open Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedIntertwiner_decomp_of_quadraticKernel' : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (σ σ' : Γ →* GL (Fin n) k) (S : Subgroup Γ) (χ η : Γ →* ℤˣ) (X : Matrix (Fin n) (Fin n) k), (∀ g ∈ S, η g = 1 → ((σ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = ((χ g : ℤ) : k) • (X * ((σ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → ∃ X₁ X₂ : Matrix (Fin n) (Fin n) k, X = X₁ + X₂ ∧ (∀ g ∈ S, ((σ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X₁ = ((χ g : ℤ) : k) • (X₁ * ((σ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) ∧ (∀ g ∈ S, ((σ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X₂ = (((χ * η) g : ℤ) : k) • (X₂ * ((σ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) := by
  first | exact @GlobalTheory.twistedIntertwiner_decomp_of_quadraticKernel | exact GlobalTheory.twistedIntertwiner_decomp_of_quadraticKernel | (intros; apply GlobalTheory.twistedIntertwiner_decomp_of_quadraticKernel <;> assumption)
end

