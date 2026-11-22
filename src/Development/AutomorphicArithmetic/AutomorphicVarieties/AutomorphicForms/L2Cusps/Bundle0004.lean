import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0002

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.CmpEquiv
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem UpperTheory.V.KernelIndexFullLattice.cmpEquiv_holds :
    UpperTheory.V.KernelIndexFullLattice.CmpEquiv := by
  intro E _ _ _ a μ _ _ μ₁ _ hp g v
  rw [l2DiscreteQuotient_ext_iff_lift_ae_eq]
  have h1 := UpperTheory.V.KernelIndexFullLattice.liftCmp_holds E a μ μ₁ hp v _ (Filter.EventuallyEq.refl _ _)
  have h2 := (MeasureTheory.measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h1
  have h3 : (toLp μ₁ (cuspRepT μ₁ (retractOne g) v) : RightCosetSpace (UpperTheory.V.KernelIndexFullLattice.Γ1 E a) → ℂ)
      =ᵐ[RightCosetSpace.quotientMeasure (UpperTheory.V.KernelIndexFullLattice.Γ1 E a) μ₁] fun x =>
        (toLp μ₁ v : RightCosetSpace (UpperTheory.V.KernelIndexFullLattice.Γ1 E a) → ℂ)
          (RightCosetSpace.rightMul (UpperTheory.V.KernelIndexFullLattice.Γ1 E a) (retractOne g) x) := by
    rw [toLp_cuspRepT]
    exact RightCosetSpace.coeFn_rightTranslate _ μ₁ (retractOne g) (toLp μ₁ v)
  have h4 := UpperTheory.V.KernelIndexFullLattice.liftCmp_holds E a μ μ₁ hp _ _ h3
  filter_upwards [lift_R g (UpperTheory.V.KernelIndexFullLattice.cmp hp v), h2, h4] with x hx1 hx2 hx4
  rw [hx1, hx4, hx2, RightCosetSpace.rightMul_mk, retractOne_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.CmpForm
section
open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem UpperTheory.V.KernelIndexFullLattice.cmpForm_holds :
    UpperTheory.V.KernelIndexFullLattice.CmpForm := by
  intro E _ _ _ a μ _ μ₁ _ hp φ hφ
  have h := UpperTheory.V.KernelIndexFullLattice.liftCmp_holds E a μ μ₁ hp (cuspVecL μ₁ φ) (cuspQuot φ.2.1.isLeftInvariant)
    (by rw [toLp_cuspVecL]; exact coeFn_cuspToL2 μ₁ φ)
  refine h.trans (Filter.Eventually.of_forall fun g => ?_)
  show cuspQuot φ.2.1.isLeftInvariant (RightCosetSpace.mk _ (retractOne g)) = φ.1 g
  rw [cuspQuot_mk, coe_retractOne, ← map_inv]
  exact apply_mul_centralSection_of_mem hφ _ _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.ContMem
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem UpperTheory.V.KernelIndexFullLattice.contMem_holds :
    UpperTheory.V.KernelIndexFullLattice.ContMem := by
  intro E _ _ _ a μ _ μ₁ _ hp φ hφ h
  obtain ⟨hc, hl, hz, hcu⟩ := mem_cuspCont.1 hφ
  have hL : IsLeftInvariant φ := fun γ g => hl γ g
  have hcusp : AutomorphicForm.IsCuspidal φ := UpperTheory.constantTerm_eq_zero_of_isCuspidal E a φ hL hc hcu
  have hr : ∀ g : GA E a, φ (retractOne g : UpperTheory.V.KernelIndexFullLattice.G1 E a) = φ g := fun g => by
    obtain ⟨t, ht⟩ := UpperTheory.V.KernelIndexFullLattice.exists_split (E := E) (a := a) UpperTheory.V.KernelIndexFullLattice.splitEq_holds
      (Reduction.detModule E a g)
    have h1 := hz t (retractOne g : UpperTheory.V.KernelIndexFullLattice.G1 E a)
    rw [← h1, splitCentre_comm, coe_retractOne, ← ht, inv_mul_cancel_right]
  have hΦ : cuspQuot hL ∘ UpperTheory.V.KernelIndexFullLattice.quotMap E a = descend (latticeGL E a) φ :=
    funext fun q => hr q.out
  have hm : MemLp (cuspQuot hL) 2 (RightCosetSpace.quotientMeasure (UpperTheory.V.KernelIndexFullLattice.Γ1 E a) μ₁) := by
    have hs := (continuous_cuspQuot hL hc).aestronglyMeasurable
      (μ := Measure.map (UpperTheory.V.KernelIndexFullLattice.quotMap E a) (quotMeasure (latticeGL E a) μ))
    rw [← hp.map_eq, memLp_map_measure_iff hs hp.measurable.aemeasurable, hΦ]
    exact h.2
  have hv : hm.toLp _ ∈ cuspidalL2 μ₁ := by
    intro r h0 h1
    filter_upwards [ae_ctFun_congr μ₁ r (MemLp.coeFn_toLp hm)] with y hy
    rw [constantTermL2, hy]
    exact hcusp r h0 h1 y
  refine ⟨⟨hm.toLp _, hv⟩, l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ?_⟩
  have h2 := UpperTheory.V.KernelIndexFullLattice.liftCmp_holds E a μ μ₁ hp ⟨hm.toLp _, hv⟩ (cuspQuot hL) (MemLp.coeFn_toLp hm)
  refine h2.trans (Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun g => ?_) h.lift_toL2_ae_eq.symm)
  exact hr g
end

