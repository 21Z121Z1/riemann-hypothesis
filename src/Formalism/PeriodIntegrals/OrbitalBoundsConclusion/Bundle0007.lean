import Mathlib
import Formalism.PeriodIntegrals.Bundle0006
import Formalism.PeriodIntegrals.Bundle0014
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeArea.ImConjMulCombo
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.Bundle0001
import Formalism.PeriodIntegrals.Bundle0011
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CommutingMultiplicity.Bundle0001
import Formalism.PeriodIntegrals.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CubeFormalIdentities.IsExpIntegralParallelogramOfNe
import Formalism.PeriodIntegrals.SameFormAllLevels
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TraceFormEquality.FormEqImage
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiltrationLength.FiltLenFMain
import Formalism.PeriodIntegrals.Bundle0004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagGramNonnegativity.Gval
import Formalism.PeriodIntegrals.JointBlockShapes.MinusPart
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.BlockDiagonalPreservesDegree
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralSpanAlgebra.IntegralSpan
import Formalism.PeriodIntegrals.Bundle0015
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KernelSplitting.IsIntegralHalf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalPrimitiveFrame.StepsTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalPrimitiveFrame.DiffLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalPrimitiveFrame.Bundle0001

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AreaLat
section
theorem area_lattice_formula : PI.AreaLat := PI.AreaLatWork.areaLat
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BeDiagZp
section
theorem diagonal_zp_identity : PI.BeDiagZp.Target :=
  PI.BeDiagZp.beDiagZp_of PI.BeDiagZp.simeq_equivalence_additive PI.BeDiagZp.power_series_diagonal_linear PI.BeDiagZp.OpsW.substOps_holds
    PI.BeDiagZp.IdentW.ident_holds PI.BeDiagZp.cont_holds PI.BeDiagZp.intSubst_holds
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CommMult
section
theorem commutant_multiplicity_one : PI.UMultOne.CommutantMult :=
  PI.UnitaryGroupMassFormula.CommMult.commMult_of PI.UnitaryGroupMassFormula.CommMult.schurStep PI.UnitaryGroupMassFormula.CommMult.injStep PI.UnitaryGroupMassFormula.CommMult.avStep
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CubeRelationOfParallelogram
section
theorem cube_relation_of_parallelogram : PI.FglGram.CubeRelationOfParallelogram := PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.cubeRelationOfParallelogram
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvFormEq
section
theorem division_form_eq : PI.Dv.SameFormAllLevels := by
  intro K _ σ G _ _ T P0 hM EE _ _ ρE M M' h
  have h1 : M.form 1 = M'.form 1 := by
    rw [PI.Dv.HermitianFormEquivalence.form_one_eq M P0 hM, PI.Dv.HermitianFormEquivalence.form_one_eq M' P0 hM, h]
  refine ⟨h1, fun P => ?_⟩
  rw [PI.Dv.HermitianFormEquivalence.form_eq_image M, PI.Dv.HermitianFormEquivalence.form_eq_image M', h1]
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FglPtW
section
theorem formal_group_add_generation : PI.FglPtW.AddGen := PI.FglPtW.Wk.addGen_thm

theorem formal_group_mul_generation : PI.FglPtW.MulGen := PI.FglPtW.Wk.mulGen_thm

private theorem cc_subst_lemma {K : Type*} [CommRing K] {σ : Type*} {a : MvPowerSeries σ K}
    (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries K) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = PowerSeries.constantCoeff f := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [map_pow, ha, zero_pow hd]

private theorem powerSeries_subst_zero_of_constantCoeff_eq_zero' {K : Type*} [CommRing K] {σ : Type*} {f : PowerSeries K}
    (hf : PowerSeries.constantCoeff f = 0) : PowerSeries.subst (0 : MvPowerSeries σ K) f = 0 := by
  ext e
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
  rw [finsum_eq_single _ 0]
  · simp [hf]
  · intro d hd
    simp [zero_pow hd]

private theorem subst_subst_eq_of_subst_eq_X {K : Type*} [CommRing K] {l ex : PowerSeries K}
    (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.subst ex l = PowerSeries.X)
    {σ : Type*} {u : MvPowerSeries σ K} (hu : MvPowerSeries.constantCoeff u = 0) :
    PowerSeries.subst (PowerSeries.subst u ex) l = u := by
  have hexS : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have huS : PowerSeries.HasSubst u := PowerSeries.HasSubst.of_constantCoeff_zero hu
  rw [← PowerSeries.subst_comp_subst_apply hexS huS, hl, PowerSeries.subst_X huS]

theorem formal_group_lin_generation : PI.FglPtW.LinGen := by
  intro K _ S l ex hex hl hadd ι _ c hc σ a ha
  classical
  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have h := cc_subst_lemma (σ := Unit) (a := ex) hex l
    rw [hl] at h
    exact h.symm.trans PowerSeries.constantCoeff_X
  have hcc : ∀ j, MvPowerSeries.constantCoeff (MvPowerSeries.C (c j) * PowerSeries.subst (a j) l) = 0 := by
    intro j
    rw [map_mul, cc_subst_lemma (ha j).2, hl0, mul_zero]
  have key : ∀ s : Finset ι, PI.FglPtW.PtOver S (PowerSeries.subst
      (∑ j ∈ s, MvPowerSeries.C (c j) * PowerSeries.subst (a j) l) ex) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, powerSeries_subst_zero_of_constantCoeff_eq_zero' hex]
      exact ⟨fun n => by simp [S.zero_mem], by simp⟩
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have hw : MvPowerSeries.constantCoeff
          (∑ j ∈ s, MvPowerSeries.C (c j) * PowerSeries.subst (a j) l) = 0 := by
        rw [map_sum]
        exact Finset.sum_eq_zero fun j _ => hcc j
      have hy := PI.FglPtW.Wk.mulGen_thm K S l ex hex hl (c i) (hc i) σ (a i) (ha i)
      have h := PI.FglPtW.Wk.addGen_thm K S l ex hex hl hadd σ _ _ hy ih
      rwa [subst_subst_eq_of_subst_eq_X hex hl (hcc i), subst_subst_eq_of_subst_eq_X hex hl hw] at h
  exact key Finset.univ
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FiltLenF
section
theorem filtration_length_bound : PI.FiltLenF := PI.FiltrationLength.filtLenF_main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FlagGramNonneg
section
theorem flag_gram_nonneg : PI.FlagGramNonneg := PI.UnitaryGroupMassFormula.FlagGramNonneg.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FockRaiseLow
section
theorem gradedOscillatorProperty : FockH1Action.H1 :=
  FockRL.gradedOscillatorProperty_of FockRL.blockDiagonalPreservesDegree
    (FockRL.pcStep_of FockRaiseLowGrade.raisingLoweringSplit)
    (FockRL.adjStep_of FockRaiseLowGrade.raisingLoweringSplit FockRaiseLowInner.fischerConjLinearLeft
      FockRaiseLowInner.fischerLinearRight FockRaiseLowInner.fischerXAdjoint)
    FockRL.kroneckerProperties
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GelfSpan
section
theorem gelfand_integral_span : PI.UMultOne.IntSpan := PI.UMultOne.GelfSpanWork.intSpan'
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerSplit
section
theorem kernel_split_of_jacobi : PI.KerIso.SplitOfJacobi := by
  intro K E _ _ _ _ _ cj d p s hd hs hcj hp hJ
  by_cases h2 : p = 2
  · subst h2
    exact PI.UnitaryGroupMassFormula.KerSplit.splitsAt_two cj d s hd hs hcj
  · exact PI.UnitaryGroupMassFormula.KerSplit.splitsAt_odd cj d p s hs hcj hp h2 (hJ.resolve_left h2)
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocFramePrim
section
theorem locFramePrim : PI.LocFramePrim.Statement :=
  PI.LocFramePrimWork.Steps_top PI.LocFramePrimWork.localDifferentPowerSpan PI.LocFramePrimWork.dualFunctionalsExist
    PI.LocFramePrimWork.primitiveOfDualFunctionals
end

