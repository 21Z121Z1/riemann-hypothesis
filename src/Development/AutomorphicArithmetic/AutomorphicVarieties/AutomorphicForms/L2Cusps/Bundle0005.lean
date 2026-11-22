import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.GrpEqMemArchCompact
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0002

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.KFinTr
section
open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem UpperTheory.V.KernelIndexFullLattice.kFinTr_holds :
    UpperTheory.V.KernelIndexFullLattice.KFinTr := by
  intro E _ _ _ a μ _ _ μ₁ _ hp v h
  have hi : Function.Injective (cmp hp) := (cmp hp).injective
  refine ⟨?_, ?_⟩
  · convert h.1 using 1
    ext k
    have e := cmpEquiv_holds E a μ μ₁ hp (finGL E a k) v
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, e, hi.eq_iff, Fb.finEmb_eq]
  · have := h.2
    have hle : (Submodule.span ℂ (Set.range fun k : archCompact E a => archRepT μ₁ (k : archGroup E a) v)).map
        (cmp hp).toLinearMap ≤ Submodule.span ℂ
        (Set.range fun k : Kinf E a => R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (cmp hp v)) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨k, rfl⟩
      obtain ⟨y, hy⟩ := (Cm.grpEq E a).surjective (k : archGroup E a)
      have hu : y.val ∈ Matrix.unitaryGroup (Fin a) (Cinf E) := (Cm.grpEq_mem_archCompact y).1 (hy ▸ k.2)
      refine Submodule.subset_span ⟨⟨y.val, hu⟩, ?_⟩
      have ey : Unitary.toUnits (⟨y.val, hu⟩ : Kinf E a) = y := Units.ext rfl
      have e := cmpEquiv_holds E a μ μ₁ hp (infGL E a y) v
      simp only [ey]
      rw [e, ← Cm.infEmb_grpEq, hy, archRepT_apply, retract_infEmb]
      rfl
    have := Submodule.finiteDimensional_of_le hle
    exact (Submodule.equivMapOfInjective (cmp hp).toLinearMap hi _).symm.finiteDimensional
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.RangeLe
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem UpperTheory.V.KernelIndexFullLattice.rangeLe_holds :
    UpperTheory.V.KernelIndexFullLattice.RangeLe := by
  intro E _ _ _ a μ _ μ₁ _ hp v
  have hv : v ∈ ((centralCuspForms E a).map (cuspVecL μ₁)).topologicalClosure := by
    rw [UpperTheory.V.KernelIndexFullLattice.dense_holds E a μ₁]; trivial
  have hcl : IsClosed (UpperTheory.V.KernelIndexFullLattice.cmp hp ⁻¹' (L2cusp μ : Set (L2 (latticeGL E a) μ))) :=
    (Submodule.isClosed_topologicalClosure _).preimage (UpperTheory.V.KernelIndexFullLattice.cmp hp).continuous
  refine closure_minimal ?_ hcl hv
  rintro _ ⟨φ, hφ, rfl⟩
  have hc : Continuous φ.1 := φ.2.1.continuous
  have hl : IsLeftInvariant φ.1 := φ.2.1.isLeftInvariant
  refine Submodule.le_topologicalClosure _ ⟨φ.1, mem_cuspCont.2 ⟨hc, fun γ g => hl γ g, fun t g => ?_,
    UpperTheory.isCuspidal_of_constantTerm_eq_zero E a φ.1 hl hc φ.2.2⟩, UpperTheory.V.KernelIndexFullLattice.cmpForm_holds E a μ μ₁ hp φ hφ⟩
  rw [splitCentre_comm, UpperTheory.V.KernelIndexFullLattice.splitEq_holds]
  exact apply_mul_centralSection_of_mem hφ _ _
end

