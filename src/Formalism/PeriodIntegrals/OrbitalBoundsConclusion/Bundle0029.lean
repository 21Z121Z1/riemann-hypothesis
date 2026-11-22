import Formalism.PeriodIntegrals.Bundle0027
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.AdelClassFinOfSvReal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.SuccessiveVectorReal
import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.Bundle0028
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0027
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0025
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionGramMatrices.DvProjGramOf
import Formalism.PeriodIntegrals.Bundle0022
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.CapelliOps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.Bundle0004
import Formalism.PeriodIntegrals.LocGlobIncl
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGlobalInclusion.SmulMemIdealSmul
import Formalism.HermitianCurvature.StatementQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GeneralLinearLevel.ElementaryGeneratorsLevelGroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.StabilizerSplittingOfParts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.NilpotentOrthogonalComplement
import Formalism.HermitianCurvature.StatementU
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Expand

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdelClassFin
section
theorem adelic_class_set_finite : PI.AdelClassFin.AdelClassFin :=
  PIW.AdelClassFin.adelClassFin_of_svReal PIW.AdelClassFin.successive_vector_real
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvProjGram
section
theorem projection_gram_det : PI.Dv.gram_det_kernel_base_level := PI.Dv.ProjGramW.dvProjGram_of projection_sandwich division_index_calc
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HookBound
section
theorem hook_length_bound : PI.HookBound := PI.HookSteps.hookBound_of PI.HookSteps.Cap.capelli_determinant_identity
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LatCountG
section
theorem lattice_count_all : PI.LatCountG.LatCountAll :=
  PI.UnitaryGroupMassFormula.LCG.latCountAll_of_idx PI.UnitaryGroupMassFormula.LCG.determinant_index_formula PI.UnitaryGroupMassFormula.LCG.lattice_indexOf
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocGlobIncl
section
namespace PI

theorem local_global_inclusion' : PI.LocGlobIncl := PI.LocGlobInclWork.main

end PI
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnEabGl
section
private lemma single_one_mul_single_one {n : ℕ} (p q s t : Fin n) :
    Matrix.single p q (1 : ℂ) * Matrix.single s t 1 = if q = s then Matrix.single p t 1 else 0 := by
  split_ifs with h
  · subst h
    rw [Matrix.single_mul_single_same, mul_one]
  · exact Matrix.single_mul_single_of_ne (h := h) ..

private lemma posL_eq_posL_iff (k r : ℕ) (i : Fin (r + 1)) (x y : Fin (Formalism.FourierDecayAlt.Q.mdim k r i)) :
    Formalism.FourierDecayAlt.Q.posL k r i x = Formalism.FourierDecayAlt.Q.posL k r i y ↔ x = y := by
  constructor
  · intro h
    have h' := congrArg Fin.val h
    simp only [Formalism.FourierDecayAlt.Q.posL] at h'
    exact Fin.ext (by omega)
  · rintro rfl
    rfl

theorem qnEabGl : Formalism.FourierDecayAlt.Q.EabGlLev := by
  intro E _ _ k r i D a b c d f _ hf g hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hL : Formalism.FourierDecayAlt.Q.EabGlW.LocExt (Formalism.FourierDecayAlt.Q.Glev k r i) f F U := ⟨hU, hF, hfF⟩
  have good : ∀ x y : Fin (Formalism.FourierDecayAlt.Q.mdim k r i), Formalism.FourierDecayAlt.Q.EabGlW.Good k r i
      (Matrix.single (Formalism.FourierDecayAlt.Q.posL k r i x) (Formalism.FourierDecayAlt.Q.posL k r i y) (1 : ℂ)) :=
    fun x y => Formalism.FourierDecayAlt.Q.EabGlW.hpart_mem (Formalism.FourierDecayAlt.Q.EabGlW.inV_single x y)
  have good0 : Formalism.FourierDecayAlt.Q.EabGlW.Good k r i (0 : Formalism.FourierDecayAlt.Q.Mx k r) :=
    Formalism.FourierDecayAlt.Q.EabGlW.hpart_mem Formalism.FourierDecayAlt.Q.EabGlW.inV_zero
  have goodIf : ∀ (P : Prop) [Decidable P] (x y : Fin (Formalism.FourierDecayAlt.Q.mdim k r i)),
      Formalism.FourierDecayAlt.Q.EabGlW.Good k r i (if P then
        Matrix.single (Formalism.FourierDecayAlt.Q.posL k r i x) (Formalism.FourierDecayAlt.Q.posL k r i y) (1 : ℂ) else 0) := by
    intro P _ x y
    split_ifs
    · exact good x y
    · exact good0
  have hcomm := Formalism.FourierDecayAlt.Q.EabGlW.ec_comm (good a b) (good c d) hL hgU hg.1
  rw [single_one_mul_single_one, single_one_mul_single_one] at hcomm
  simp only [posL_eq_posL_iff] at hcomm
  rw [Formalism.FourierDecayAlt.Q.EabGlW.ec_sub (goodIf _ a d) (goodIf _ c b) hL hgU hg.1] at hcomm
  change _ = _ at hcomm
  refine hcomm.trans ?_
  congr 1
  · split_ifs
    · rfl
    · exact Formalism.FourierDecayAlt.Q.EabGlW.ec_zero f g
  · split_ifs
    · rfl
    · exact Formalism.FourierDecayAlt.Q.EabGlW.ec_zero f g
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.StabSplit
section
theorem stabSplit : Formalism.FourierDecayAlt.C2.C1ii :=
  PI.StabSplit.stabilizer_splitting_of_parts PI.StabSplit.fixed_point_subgroup PI.StabSplit.stabilizer_subgroup_flag PI.StabSplit.unipotent_nilpotent_radical
    PI.StabSplit.nilpotent_orthogonal_complement
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UsCompose
section
theorem differential_operator_compose : Formalism.FourierDecayAlt.U.ComposeDD :=
  PI.UnitaryGroupMassFormula.UsCompose.composeDD_of (fun _ X q => PI.UnitaryGroupMassFormula.UsCompose.degDP X q)
    (fun k j ρ => PI.UnitaryGroupMassFormula.UsCompose.degD k j ρ) PI.UnitaryGroupMassFormula.UsCompose.expand
end

