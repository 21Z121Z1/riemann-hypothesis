import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.EqSmulOfSub
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.AlgebraMapIntMemIntAd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.Bundle0006

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.KGauge
section
noncomputable section

namespace PI.IwaMeasEx.Gauge

open MeasureTheory Topology Filter Set
open scoped ENNReal NNReal Pointwise
open Formalism.MainNotions.S

section Riem

variable {n : ℕ}

abbrev MatR (n : ℕ) : Type := EuclideanSpace ℝ (Fin n × Fin n × Bool)

def realifyM (X : Matrix (Fin n) (Fin n) ℂ) : MatR n :=
  WithLp.toLp 2 (fun p => if p.2.2 then (X p.1 p.2.1).im else (X p.1 p.2.1).re)

def toMat (x : MatR n) : Matrix (Fin n) (Fin n) ℂ := fun i j => ⟨x.ofLp (i, j, false), x.ofLp (i, j, true)⟩

def expU (x : MatR n) : (Matrix (Fin n) (Fin n) ℂ)ˣ := (Matrix.isUnit_exp (toMat x)).unit

variable {ε : Fin n → Bool}

def lieOf (H : Subgroup (Formalism.REAL.UJ ε)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | ∀ t : ℝ, ∃ h ∈ H, uMat h = NormedSpace.exp ((t : ℂ) • X)}

def lieSp (H : Subgroup (Formalism.REAL.UJ ε)) : Submodule ℝ (MatR n) :=
  Submodule.span ℝ (realifyM '' lieOf H)

def conjInv (H : Subgroup (Formalism.REAL.UJ ε)) (y : Formalism.REAL.UJ ε) : Subgroup (Formalism.REAL.UJ ε) :=
  H.map (MulAut.conj y⁻¹).toMonoidHom

def expSetY (H : Subgroup (Formalism.REAL.UJ ε)) (y : Formalism.REAL.UJ ε) (T : Set (lieSp (conjInv H y))) :
    Set (Formalism.REAL.UJ ε) :=
  {g | ∃ x ∈ T, uMat g = uMat y * NormedSpace.exp (toMat (x : MatR n)) * uMat y⁻¹}

structure IsRiem (H : Subgroup (Formalism.REAL.UJ ε)) (y : Formalism.REAL.UJ ε) (R : Measure (Formalism.REAL.UJ ε)) : Prop where
  sfin : SigmaFinite R
  ne : R ≠ 0
  supp : R (H : Set (Formalism.REAL.UJ ε))ᶜ = 0
  cpt : ∀ s : Set (Formalism.REAL.UJ ε), IsCompact s → R s ≠ ⊤
  inv : ∀ h ∈ H, R.map (fun x => h * x) = R
  dens : ∀ S : Set (lieSp (conjInv H y)), MeasurableSet S → Bornology.IsBounded S →
    0 < (volume : Measure (lieSp (conjInv H y))) S → (volume : Measure (lieSp (conjInv H y))) (frontier S) = 0 →
    Tendsto (fun r : ℝ => R (expSetY H y (r • S)) / (volume : Measure (lieSp (conjInv H y))) (r • S)) (𝓝[>] 0) (𝓝 1)

def RiemHaar : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Subgroup (Formalism.REAL.UJ ε)) (y : Formalism.REAL.UJ ε), IsClosed (H : Set (Formalism.REAL.UJ ε)) →
    ∃ R, IsRiem H y R

end Riem

end PI.IwaMeasEx.Gauge

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.PseudoMetrizableAEf
section
noncomputable section

namespace PI.IwaMeasEx.MH

open MeasureTheory Measure Topology Set Filter
open scoped ENNReal NNReal TensorProduct
open Formalism.MainNotions.S Formalism.L2.S.S7.GLOne

section Gen

variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
  [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

theorem char_eq_of_map' (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) {c : ℝ≥0} (hc : c ≠ 0)
    (h : μ.map φ = c • μ) : addEquivAddHaarChar φ = c⁻¹ := by
  have hreg : μ.Regular := inferInstance
  have h1 := MeasureTheory.addEquivAddHaarChar_smul_map μ φ
  rw [h, smul_smul] at h1
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : A)
  have hpos : 0 < μ K := MeasureTheory.Measure.measure_pos_of_mem_nhds μ hKn
  have hfin : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have h2 := congrArg (fun ν : Measure A => ν K) h1
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  have h3 : μ K * ((addEquivAddHaarChar φ * c : ℝ≥0) : ℝ≥0∞) = μ K * 1 := by
    rw [mul_one, mul_comm]
    exact_mod_cast h2
  have h4 : ((addEquivAddHaarChar φ * c : ℝ≥0) : ℝ≥0∞) = 1 := (ENNReal.mul_right_inj hpos.ne' hfin).1 h3
  have h5 : addEquivAddHaarChar φ * c = 1 := by exact_mod_cast h4
  exact eq_inv_of_mul_eq_one_left h5

theorem char_eq_one_of_map (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) (h : μ.map φ = μ) :
    addEquivAddHaarChar φ = 1 := by
  have h1 : μ.map φ = (1 : ℝ≥0) • μ := by rw [one_smul]; exact h
  simpa using char_eq_of_map' μ φ one_ne_zero h1

def piE {ι : Type*} [Fintype ι] (φ : ι → A ≃ₜ+ A) : (ι → A) ≃ₜ+ (ι → A) where
  toFun x i := φ i (x i)
  invFun x i := (φ i).symm (x i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp
  map_add' x y := by funext i; simp
  continuous_toFun := continuous_pi fun i => (φ i).continuous.comp (continuous_apply i)
  continuous_invFun := continuous_pi fun i => (φ i).symm.continuous.comp (continuous_apply i)

theorem char_pi {ι : Type} [Fintype ι] [DecidableEq ι] (φ : ι → A ≃ₜ+ A) :
    addEquivAddHaarChar (piE φ) = ∏ i, addEquivAddHaarChar (φ i) := by
  classical
  set μ : Measure A := Measure.addHaar with hμ
  set c : ι → ℝ≥0 := fun i => addEquivAddHaarChar (φ i) with hcdef
  have hc0 : ∀ i, c i ≠ 0 := fun i => (addEquivAddHaarChar_pos (φ i)).ne'
  have hmap : ∀ i, μ.map (φ i) = (c i)⁻¹ • μ := by
    intro i
    have h1 := addEquivAddHaarChar_smul_map μ (φ i)
    calc μ.map (φ i) = (c i)⁻¹ • (c i • μ.map (φ i)) := by
          rw [smul_smul, inv_mul_cancel₀ (hc0 i), one_smul]
      _ = (c i)⁻¹ • μ := by rw [h1]
  haveI : ∀ i, SigmaFinite (μ.map (φ i)) := fun i => by rw [hmap i]; infer_instance
  have hbox : ∀ d : ι → ℝ≥0, Measure.pi (fun i => d i • μ) = (∏ i, d i) • Measure.pi (fun _ : ι => μ) := by
    intro d
    refine (Measure.pi_eq (μ := fun i => d i • μ) (μ' := (∏ i, d i) • Measure.pi (fun _ : ι => μ)) fun s hs => ?_)
    rw [Measure.smul_apply, Measure.pi_pi]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    rw [Finset.prod_mul_distrib, ENNReal.coe_finset_prod]
  have hpm : (Measure.pi (fun _ : ι => μ)).map (piE φ) = (∏ i, (c i)⁻¹) • Measure.pi (fun _ : ι => μ) := by
    have h2 : ⇑(piE φ) = fun x i => φ i (x i) := rfl
    rw [h2, Measure.pi_map_pi (f := fun i => (φ i : A → A)) (fun i => (φ i).continuous.measurable.aemeasurable)]
    simp only [hmap]
    exact hbox _
  have h3 := char_eq_of_map' (Measure.pi fun _ : ι => μ) (piE φ)
    (Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (hc0 i)) hpm
  rw [h3, Finset.prod_inv_distrib, inv_inv]

end Gen

section AEf

variable (I : AutInst)

attribute [local instance] AfT.tAf Nrm.topRing Nrm.t2 Nrm.mAf Nrm.borel_mAf MFI.locallyCompact_AEf

theorem sigmaCompact_AEf : SigmaCompactSpace (AEf I) := by
  refine ⟨⟨fun N => (fun x => (((AfT.isUnit_natCast I (N + 1) (by omega)).unit⁻¹ : (AEf I)ˣ) : AEf I) * x) ''
    ((IntAf I.F I.E : Subring (AEf I)) : Set (AEf I)), fun N => (Nrm.isCompact_IntAf I).image
      (continuous_const.mul continuous_id), ?_⟩⟩
  refine Set.eq_univ_of_forall fun t => ?_
  obtain ⟨N, hN, hmem⟩ := AfT.exists_nat_mul_mem I t
  refine Set.mem_iUnion.2 ⟨N - 1, (N : AEf I) * t, hmem, ?_⟩
  have e : ((N - 1 + 1 : ℕ) : AEf I) = N := by congr 1; omega
  show (((AfT.isUnit_natCast I (N - 1 + 1) (by omega)).unit⁻¹ : (AEf I)ˣ) : AEf I) * ((N : AEf I) * t) = t
  rw [← mul_assoc]
  have h2 : (((AfT.isUnit_natCast I (N - 1 + 1) (by omega)).unit⁻¹ : (AEf I)ˣ) : AEf I) * (N : AEf I) = 1 := by
    rw [← e]; exact (AfT.isUnit_natCast I (N - 1 + 1) (by omega)).val_inv_mul
  rw [h2, one_mul]

theorem pseudoMetrizable_AEf : TopologicalSpace.PseudoMetrizableSpace (AEf I) := by
  letI : UniformSpace (AEf I) := IsTopologicalAddGroup.rightUniformSpace (AEf I)
  haveI : IsUniformAddGroup (AEf I) := isUniformAddGroup_of_addCommGroup
  haveI : (𝓝 (0 : AEf I)).IsCountablyGenerated := (AfT.hasBasis_nhds_zero_tAf I).isCountablyGenerated
  haveI : (uniformity (AEf I)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  exact UniformSpace.pseudoMetrizableSpace

theorem secondCountable_AEf : SecondCountableTopology (AEf I) := by
  haveI := sigmaCompact_AEf I
  haveI := pseudoMetrizable_AEf I
  letI := TopologicalSpace.pseudoMetrizableSpacePseudoMetric (AEf I)
  infer_instance

end AEf

end PI.IwaMeasEx.MH

end
end

