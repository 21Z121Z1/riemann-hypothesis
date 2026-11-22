import Mathlib
import Formalism.PeriodIntegrals.Bundle0020
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BlockEigenvalues.PhiUZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugationInvariance.SecondRowsBlockDiagMul
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.AnisoPeel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.IsoPeel
import Formalism.PeriodIntegrals.Bundle0014
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicFiniteOrder.Assembly
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0012
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0010
import Formalism.PeriodIntegrals.Bundle0015
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalHaarSubgroup.MemOrdR
import Formalism.PeriodIntegrals.Bundle0006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.Assembly
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.Bundle0001
import Formalism.PeriodIntegrals.Bundle0021
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalResidueCharacter.ResCharEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientIntegralBound.QuotientLIntegralLeMultiplicityLIntegral
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuarticIndependence.QmIndep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuantumMinorLemma.Imports
import Formalism.PeriodIntegrals.Bundle0009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.Bundle0005
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.Bundle0004

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DatumBlockEigen
section
theorem datum_block_eigenvalues : PI.DatumBlockEigen := PI.DatumBlockEigen.Main.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DatumConjInv
section
theorem datum_conjugation_invariant : PI.DatumConjInv := PI.DatumConjInvWork.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DensInert
section
theorem density_exact_inert : Formalism.L2.SG.DensExact.DensExactInert :=
  DensInertW.densExactInert_of DensInertW.hermitianDiagonalization DensInertW.repCountCongruenceInvariant
    DensInertW.anisotropic_valuation_peel DensInertW.isotropic_valuation_peel DensInertW.quadraticDifferenceArith
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FinOrdAd
section
theorem finite_order_adelic : PI.FinOrdAd :=
  PI.finOrdAd_of unit_kronecker power_bounded_integral tensor_compact_dense positive_definite_form
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IdealLattice
section
theorem ideal_lattice_basis : PI.IdealLattice :=
  PI.IdealLatticeWork.idealLattice_of PI.IdealLatticeWork.okArea PI.IdealLatticeWork.idealBasis
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocHaarRR
section
theorem local_haar_real_real : PI.LocHaarRR.Target := PI.LocHaarRRW.target
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocalEnd
section
theorem local_endomorphism_homeomorph : PI.LocalEndHomeo :=
  PI.LocalEndW.localEndHomeo_of_three PI.LocalEndW.henselRoot PI.LocalEndW.intOfHensel PI.LocalEndW.valOfInt
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PinHostLoc
section
theorem prime_quotient_unit : PI.PinHostLoc.Target := by
  intro F E _ _ _ _ _ sig p A g hg hne i hin hnot
  have hres := PI.PinHostLoc.UnitaryGroupMassFormula.resChar_eq p (hg i) hin
  have hi0 : ((g i : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (hg i).ne_zero
  refine ⟨?_, ?_⟩
  · rw [hres]
    exact PI.PinHostLoc.UnitaryGroupMassFormula.irr A (hg i).ne_zero hin hnot
  · obtain ⟨j, hgij, hj⟩ : ∃ j : Fin 2, g i ≠ g j ∧
        ((g 0 : ℕ) : F) * ((g 1 : ℕ) : F) / ((g i : ℕ) : F) = ((g j : ℕ) : F) := by
      rcases (show i = 0 ∨ i = 1 by fin_cases i <;> simp) with rfl | rfl
      · exact ⟨1, hne, mul_div_cancel_left₀ _ hi0⟩
      · exact ⟨0, hne.symm, mul_div_cancel_right₀ _ hi0⟩
    have hjp : ((g j : ℕ) : NumberField.RingOfIntegers F) ∉ p.asIdeal := by
      intro hjin
      have hcop : IsCoprime ((g i : ℕ) : ℤ) ((g j : ℕ) : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hg i) (hg j)).mpr hgij)
      obtain ⟨a, b, hab⟩ := hcop
      have h1 : (1 : NumberField.RingOfIntegers F) ∈ p.asIdeal := by
        have h2 := congrArg (Int.cast : ℤ → NumberField.RingOfIntegers F) hab
        push_cast at h2
        rw [← h2]
        exact p.asIdeal.add_mem (p.asIdeal.mul_mem_left _ hin) (p.asIdeal.mul_mem_left _ hjin)
      exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    obtain ⟨u, hu, hu'⟩ := PI.PinHostLoc.UnitaryGroupMassFormula.unit A hjp
    exact ⟨u, hu, by rw [hu', hj]⟩
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PoincareSeriesFinite
section
theorem poincareSeries_finite (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] : Formalism.L2.SG.PoincareSeriesSquareIntegrable.PoincareSeriesFinite G μ :=
  PI.PoincareSeriesFinite.UnitaryGroupMassFormula.poincareSeriesFinite G μ
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmIndep
section
theorem rtt_independence' : PI.RTTIndependence := PI.QmIndepW.qmIndep
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmLemD
section
theorem quantum_minor_D : PI.LemmaD := PI.QmLemDWork.main
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Residue
section
open PI.Residue in
theorem dedekind_residue_bound : PI.ResidueBound :=
  residueBound_of zetaLePow zetaRLe
    (heckeLower_of
      (classLower_of (countIntegral_of boxVolume) shellVolume (unfold_of unitPreserving)
        (hitBound_of boxVolume) idealSetSum)
      classSum)
    optimise
end

