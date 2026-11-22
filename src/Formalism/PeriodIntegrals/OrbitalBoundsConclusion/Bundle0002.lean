import Mathlib
import Formalism.PeriodIntegrals.ArtSch
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationGluing.ValbLeOfCoeffEqZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArtinSchreierRoots.ExistsRootOC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmallArtinSchreier.ExistsAsOfValLtOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittCoefficients.CoeffEqOfSubMem
import Formalism.PeriodIntegrals.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicCompactDensity.ExistsNatLocal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BiadditiveCubes.ConstantCoeffLogEqZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMTraceSurjective.IsTrMulConjOfMem
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterExtension.UnitsComplexExistsZpow
import Formalism.PeriodIntegrals.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalRank.DetOneSubPNe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDifferentGenerators.DiffExistsMain
import Formalism.PeriodIntegrals.SameFormAllLevels
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalKernels.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingPermutations.CjEq

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASGlue
section
theorem tiltSurjectiveOfParts : PI.ArtSch.TiltGlue := PI.ArtSch.Glue.tiltGlue
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASRoot
section
theorem rootModP_holds : PI.ArtSch.RootModP := by
  intro l _ c b
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨z, hz⟩ := PI.ArtSch.RootWork.exists_root_OC l c' b'
  refine ⟨Ideal.Quotient.mk _ z, ?_⟩
  rw [← map_pow, ← map_mul, ← map_sub, ← map_sub, hz, map_zero]
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASSmall
section
theorem smallSurjective : PI.ArtSch.TiltSmall := PI.UnitaryGroupMassFormula.ASSmall.tiltSmall
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ASWitt
section
theorem witt_lift : PI.ArtSch.WittLift := PI.ArtSch.WittLiftWork.wittLift
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdCpctDen
section
theorem compactBounded : PI.AdCpctDen := PI.adCpctDen
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BiaddOfCube
section
theorem biadditiveOfCube_holds : PI.BiaddOfCube.Target := by
  intro p _ l ex ph hex h hC
  have hxz : PI.BiaddOfCube.add l ex (PI.BiaddOfCube.Xv (p := p) 0 : MvPowerSeries (Fin 3) ℂ_[p])
      (PI.BiaddOfCube.Xv 2) = PI.BiaddOfCube.add l ex (PI.BiaddOfCube.Xv 2) (PI.BiaddOfCube.Xv 0) :=
    PI.BiaddOfCubeWork.add_comm' l ex _ _
  have has := PI.BiaddOfCubeWork.add_assoc' hex h
    (PI.BiaddOfCube.Xv (p := p) 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.BiaddOfCube.Xv 1) (PI.BiaddOfCube.Xv 2)
    (PI.BiaddOfCubeWork.cc_Xv 0) (PI.BiaddOfCubeWork.cc_Xv 1) (PI.BiaddOfCubeWork.cc_Xv 2)
  constructor
  · refine PI.BiaddOfCubeWork.simeq_of_sub_eq ?_ hC
    simp only [PI.BiaddOfCube.be, hxz]
    ring
  · refine PI.BiaddOfCubeWork.simeq_of_sub_eq ?_ hC
    simp only [PI.BiaddOfCube.be, hxz, ← has]
    ring
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CMTraceOnto
section
theorem traceSurjective_holds : PI.CMTraceOnto := by
  intro K _ _ _ hK a ha

  have hfix : PI.CMT.conj a = a := by
    apply NumberField.RingOfIntegers.ext
    rw [PI.CMT.coe_conj, ha]
  obtain ⟨x, hx⟩ := PI.CMT.isTr_mul_fixed hfix (PI.CMT.isTr_one hK.2.2)
  refine ⟨x, PI.CMT.conj x, PI.CMT.coe_conj x, ?_⟩
  rw [hx, mul_one]
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharExtend
section
namespace PI

theorem character_extension_exists : PI.CharExtend := PI.CharExtendWork.charExtend_main

end PI
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiagRank
section
theorem diagonal_rank_bound : PI.DiagRank := PI.UnitaryGroupMassFormula.DiagRank.diagRank
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiffGenLoc
section
theorem diffExists {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) : PI.DiffGenLoc.DiffExists v :=
  PI.DiffGenLoc.UnitaryGroupMassFormula.diffExists_main v
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvRatKer
section
theorem rational_kernel_division : PI.Dv.Conclusion8 := by
  intro K _ σ G _ _ T P0 hM1 EE _ _ ρE M hR
  have hF := PI.Dv.RK.eG_mem T P0 (PI.Dv.RK.tau_eps_ne T P0 hM1)
  exact ⟨PI.Dv.RK.rat_ker M P0 hF hR, PI.Dv.RK.form_eq M P0 hF⟩
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EmbPerm
section
theorem embedding_permutation : PI.EmbPerm := PI.EmbPermWork.main
end

