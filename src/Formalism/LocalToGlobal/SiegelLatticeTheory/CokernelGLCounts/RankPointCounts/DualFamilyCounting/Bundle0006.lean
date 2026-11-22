import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0005
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0017
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0011
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoAF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0010
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TensTop

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSBoxVolSk
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.BoxVolSk

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes Formalism.L2.SG.LocVol
  NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def GramMeas : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (a : ℕ) (T : Matrix (Fin a) (Fin a) E),
    MeasurableSet {x : Fin a → Fin n → Af F ⊗[F] E | gramR (Af F) σ J x ≠ T.map (inclR (Af F))} ∧
    (∀ y : Fin a → Fin n → AF F ⊗[F] E, gramR (AF F) σ J y = T.map (inclR (AF F)) →
      gramR (Af F) σ J (projFin y) = T.map (inclR (Af F))) ∧
    (∀ x : Fin a → Fin n → Af F ⊗[F] E, gramR (Af F) σ J x = T.map (inclR (Af F)) →
      ∀ v, gramR (Fv F v) σ J (projV v x) = T.map (inclR (Fv F v)))

def PosTest : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (a : ℕ)
    (μ : Measure (Fin a → Fin n → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ a))
    (fib : HermR (Ainf F) σ a → Measure (Fin a → Fin n → Ainf F ⊗[F] E)) (t : HermR (Ainf F) σ a),
    IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val {X | LinearIndependent (Ainf F ⊗[F] E) X} ν Set.univ fib →
    fib t ≠ 0 →
    ∃ Φ : (Fin a → Fin n → Ainf F ⊗[F] E) → ℝ, Continuous Φ ∧ HasCompactSupport Φ ∧ (∀ x, 0 ≤ Φ x) ∧
      Integrable Φ (fib t) ∧ 0 < ∫ x, Φ x ∂(fib t)

def FinInt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n a d : ℕ) (b : Module.Basis (Fin d) F E) (x : Fin a → Fin n → Af F ⊗[F] E),
    ∀ᶠ v in Filter.cofinite, projV v x ∈ latV b v

def BoxMeas : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n a : ℕ) (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin n → Fv F v ⊗[F] E)),
    (∀ v, MeasurableSet (C v)) → MeasurableSet {x : Fin a → Fin n → Af F ⊗[F] E | ∀ v, projV v x ∈ C v}

theorem BoxVolSk_tprod_ofReal {ι : Type} (r : ι → ℝ) (hm : Multipliable (fun i => (r i : ℂ))) :
    ∏' i, (r i : ℂ) = ((∏' i, r i : ℝ) : ℂ) := by
  obtain ⟨L, hL⟩ := hm
  have hclosed : IsClosed (Set.range ((↑) : ℝ → ℂ)) := Complex.isometry_ofReal.isClosedEmbedding.isClosed_range
  have hmem : L ∈ Set.range ((↑) : ℝ → ℂ) :=
    hclosed.mem_of_tendsto hL (Filter.Eventually.of_forall fun s => ⟨∏ i ∈ s, r i, by rw [Complex.ofReal_prod]⟩)
  obtain ⟨l, rfl⟩ := hmem
  have hr : HasProd r l :=
    (Complex.isometry_ofReal.isEmbedding.isInducing.hasProd_iff (g := Complex.ofRealHom) (f := r) (a := l)).mp hL
  rw [hL.tprod_eq, hr.tprod_eq]

end Formalism.L2.SG.Pf.NcS.BoxVolSk
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXBoxSteps
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.BoxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open Formalism.L2.SG.Pf.NcX.BoxVolSk
open scoped TensorProduct

theorem box_measurable_holds : BoxMeas := by
  intro F E _ _ _ _ _ n a C hC
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  have e : {x : Fin a → Fin n → Af F ⊗[F] E | ∀ v, projV v x ∈ C v} = ⋂ v, projV v ⁻¹' C v := by
    ext x; simp
  rw [e]
  exact MeasurableSet.iInter fun v =>
    (PI.VolStabW.TopoMeas.continuous_projV b v).measurable (hC v)

theorem gram_measurable_holds : GramMeas := by
  intro F E _ _ _ _ _ σ n J a T
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine ⟨?_, fun y hy => ?_, fun x hx v => ?_⟩
  · have : T2Space (Af F ⊗[F] E) := PI.VolStabW.RestrProdG.t2_tensor_product (Af F)
    have : T2Space (Matrix (Fin a) (Fin a) (Af F ⊗[F] E)) :=
      inferInstanceAs (T2Space (Fin a → Fin a → Af F ⊗[F] E))
    exact (isClosed_singleton.preimage
      (PI.VolStabW.continuous_gramR (Af F) σ J)).isOpen_compl.measurableSet
  · funext i j
    have h := congrArg (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E))
      (congrFun (congrFun hy i) j)
    rw [PI.VolStabW.RestrProdG.map_gramR, Matrix.map_apply,
      PI.VolStabW.RestrProdG.map_inclR] at h
    rw [Matrix.map_apply]
    exact h
  · funext i j
    have h := congrArg (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E))
      (congrFun (congrFun hx i) j)
    rw [PI.VolStabW.RestrProdG.map_gramR, Matrix.map_apply,
      PI.VolStabW.RestrProdG.map_inclR] at h
    rw [Matrix.map_apply]
    exact h

theorem positivity_test_holds : PosTest := by
  intro F E _ _ _ _ _ σ n J a μ ν fib t hfib hne
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  set V := Fin a → Fin n → Ainf F ⊗[F] E
  set U : Set V := {X | LinearIndependent (Ainf F ⊗[F] E) X} with hUdef
  have hUo : IsOpen U := PI.VolStabW.TensAllW.isOpen_linIndep b (Ainf F)
    (PI.VolStabW.isOpen_units_Ainf F) (PI.VolStabW.lip_ainf F)
  have : LocallyCompactSpace (Ainf F ⊗[F] E) := PI.AdicCompletionValuation.locallyCompactSpace_tens (Ainf F)
  have : T2Space (Ainf F ⊗[F] E) := PI.VolStabW.RestrProdG.t2_tensor_product (Ainf F)
  have : SecondCountableTopology (Ainf F ⊗[F] E) := PI.VolStabW.secondCountable_tens (Ainf F)

  have hcU : fib t Uᶜ = 0 := measure_mono_null
    (Set.compl_subset_compl.2 Set.inter_subset_right) (hfib.1 t)
  have hUpos : 0 < fib t U := by
    rcases eq_or_ne (fib t U) 0 with h | h
    · exfalso; apply hne
      rw [← Measure.measure_univ_eq_zero]
      have := measure_union_null h hcU
      rwa [Set.union_compl_self] at this
    · exact pos_iff_ne_zero.2 h

  have : LocallyCompactSpace U := hUo.locallyCompactSpace
  have : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hUeq : U = ⋃ m, Subtype.val '' compactCovering U m := by
    ext x; constructor
    · intro hx
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 ((iUnion_compactCovering U).symm ▸ Set.mem_univ (⟨x, hx⟩ : U))
      exact Set.mem_iUnion.2 ⟨m, ⟨⟨x, hx⟩, hm, rfl⟩⟩
    · intro hx
      obtain ⟨m, y, _, rfl⟩ := Set.mem_iUnion.1 hx
      exact y.2
  obtain ⟨m, hm⟩ : ∃ m, 0 < fib t (Subtype.val '' compactCovering U m) := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have : fib t U = 0 := by
      rw [hUeq]
      exact measure_iUnion_null fun m => nonpos_iff_eq_zero.1 (hcon m)
    exact hUpos.ne' this
  set K : Set V := Subtype.val '' compactCovering U m
  have hK : IsCompact K := (isCompact_compactCovering U m).image continuous_subtype_val
  have hKU : K ⊆ U := by rintro _ ⟨y, _, rfl⟩; exact y.2
  obtain ⟨f, hf1, hfc, hfU, hf01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hUo hKU
  have hint : Integrable f (fib t) :=
    ((hfib.2.2 f f.continuous hfc hfU).1 t (Set.mem_univ _))
  refine ⟨f, f.continuous, hfc, fun x => (hf01 x).1, hint, ?_⟩
  rw [integral_pos_iff_support_of_nonneg (fun x => (hf01 x).1) hint]
  refine lt_of_lt_of_le hm (measure_mono fun x hx => ?_)
  rw [Function.mem_support, hf1 hx]
  exact one_ne_zero

end Formalism.L2.SG.Pf.NcX.BoxSteps
end
end

