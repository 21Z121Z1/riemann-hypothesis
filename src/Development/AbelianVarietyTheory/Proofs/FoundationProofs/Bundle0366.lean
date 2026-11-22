import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanRhoKInfU
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

noncomputable section

namespace GlobalTheory.RealSpan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]

theorem exists_cEmb_pi (σ : ι → (E →+* ℂ)) (hσ : Function.Injective (fun τ => InfinitePlace.mk (σ τ)))
    (g : ι → GL (Fin n) ℂ) (hg : ∀ τ, (g τ : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ y : infU E n, (MonoidHom.pi fun τ => cEmb (E := E) (n := n) (σ τ)) y.1 = g := by
  classical
  let J : Subgroup (ι → GL (Fin n) ℂ) :=
    ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (σ τ)).comp (infU E n).subtype).range
  let Hs : ι → Subgroup (GL (Fin n) ℂ) := fun _ => (GlobalTheory.Branching.unitaryIncl n).range
  have hle : Subgroup.pi Set.univ Hs ≤ J := by
    rw [Subgroup.pi_le_iff]
    intro τ
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n (σ τ)
    let x := e.symm u
    have hx := Subgroup.mem_inf.1 x.2
    refine ⟨⟨x.1, hx.1⟩, ?_⟩
    funext τ'
    by_cases h : τ' = τ
    · subst h
      change cEmb (σ τ') x.1 = _
      rw [← he, e.apply_symm_apply]
      simp
    · have hne : InfinitePlace.mk (σ τ') ≠ InfinitePlace.mk (σ τ) := fun e' => h (hσ e')
      have h5 : x.1 ∈ (cEmb (E := E) (n := n) (σ τ')).ker :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 (σ τ')) hne
      change cEmb (σ τ') x.1 = _
      rw [MonoidHom.mem_ker.1 h5]
      simp [h]
  obtain ⟨y, hy⟩ : g ∈ J := hle fun τ _ => ⟨⟨(g τ).val, hg τ⟩, Units.ext rfl⟩
  exact ⟨y, hy⟩

theorem span_rhoK_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ι : Type) [Fintype ι]
    (σ : ι → (E →+* ℂ)) (lam : ι → DomWeight n), Function.Injective (fun τ => InfinitePlace.mk (σ τ)) →
    FiniteDimensional ℂ (Formalism.L2.DIV.VV ℂ lam) ∧ Submodule.span ℂ (Set.range ((Formalism.L2.DIV.rhoK (K := ℂ) lam).comp
      ((MonoidHom.pi fun τ => cEmb (E := E) (n := n) (σ τ)).comp (infU E n).subtype))) = ⊤ := by
  intro E _ _ _ n ι _ σ lam hσ
  haveI : ∀ τ, Finite (Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW) := fun _ => (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  haveI hfd : FiniteDimensional ℂ (Formalism.L2.DIV.VV ℂ lam) := Module.Finite.of_basis (Formalism.L2.DIV.bVV ℂ lam)
  refine ⟨hfd, ?_⟩
  rcases subsingleton_or_nontrivial (Formalism.L2.DIV.VV ℂ lam) with hs | hs
  · haveI : Subsingleton (Module.End ℂ (Formalism.L2.DIV.VV ℂ lam)) := inferInstance
    exact Subsingleton.elim _ _
  · exact GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ _ ((CuspRep.isIrreducible_iff _).2 ⟨inferInstance,
      fun U hU => GlobalTheory.CoefIrred.vv_irreducible_unitary ι n lam U fun g hg x hx => by
        obtain ⟨y, hy⟩ := exists_cEmb_pi (E := E) σ hσ g hg
        have := hU y x hx
        simpa [hy] using this⟩)

end GlobalTheory.RealSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeightModuleFiniteContinuous
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.WtCont

theorem continuous_functional_dwAct (n : ℕ) (f : MvPolynomial (Fin n × Fin n) ℂ) :
    ∀ ψ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] ℂ,
      Continuous fun g : GL (Fin n) ℂ => ψ (Formalism.UG.dwAct ℂ n n g f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro ψ
    have e : ∀ g : GL (Fin n) ℂ, Formalism.UG.dwAct ℂ n n g (C a) = C a := fun g => by
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    simp_rw [e]
    exact continuous_const
  | add p q hp hq => intro ψ; simp only [map_add]; exact (hp ψ).add (hq ψ)
  | mul_X p v hp =>
    intro ψ
    have e : ∀ g : GL (Fin n) ℂ, ψ (Formalism.UG.dwAct ℂ n n g (p * X v)) =
        ∑ b : Fin n, (((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) v.1 b) *
          (ψ.comp (LinearMap.mulRight ℂ (X (b, v.2)))) (Formalism.UG.dwAct ℂ n n g p) := by
      intro g
      simp only [map_mul, Formalism.UG.dwAct, Formalism.GradedWeylDivisibility.rowAct, aeval_X, Finset.mul_sum, map_sum, LinearMap.comp_apply,
        LinearMap.mulRight_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← smul_eq_C_mul, mul_smul_comm, map_smul, smul_eq_mul]
    simp_rw [e]
    refine continuous_finset_sum _ fun b _ => ?_
    refine Continuous.mul ?_ (hp _)
    exact ((Units.continuous_coe_inv).matrix_elem v.1 b)

theorem continuous_dual_dualWeylRep (n : ℕ) (ν : Fin n → ℕ) (x : Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν)
    (φ : Module.Dual ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν)) :
    Continuous fun g : GL (Fin n) ℂ => φ (Formalism.UG.dualWeylRep ℂ n n ν g x) := by
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend φ
  have e : ∀ g : GL (Fin n) ℂ, φ (Formalism.UG.dualWeylRep ℂ n n ν g x) = ψ (Formalism.UG.dwAct ℂ n n g x) := fun g => by
    rw [← hψ, LinearMap.comp_apply, Submodule.subtype_apply, Formalism.UG.dualWeylRep_apply]
  simp_rw [e]
  exact continuous_functional_dwAct n _ ψ

theorem continuous_det_units (n : ℕ) : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) ℂ → ℂˣ) := by
  rw [Units.continuous_iff]
  constructor
  · simp only [Function.comp_def, Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.continuous_val.matrix_det
  · have e : ∀ g : GL (Fin n) ℂ, ((Matrix.GeneralLinearGroup.det g)⁻¹ : ℂˣ) = Matrix.GeneralLinearGroup.det g⁻¹ :=
      fun g => (map_inv _ g).symm
    simp only [Function.comp_def, e, Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.continuous_coe_inv.matrix_det

theorem grp_tprod' (n : ℕ) {ι : Type} [DecidableEq ι] (mu : ι → ℕ → ℕ) (h : ι → GL (Fin n) ℂ)
    (x : ∀ τ, Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ))) :
    grp ℂ n mu h (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ (fun τ => Formalism.UG.dualWeylRep ℂ n n _ (h τ) (x τ)) := by
  simp [grp, Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep, PiTensorProduct.mapMonoidHom, PiTensorProduct.map_tprod]

theorem finite_continuous_wtOp : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ), (∀ τ, FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)))) ∧ FiniteDimensional ℂ (NablaT ℂ n mu) ∧ ∀ (u : NablaT ℂ n mu) (ℓ : Module.Dual ℂ (NablaT ℂ n mu)), Continuous fun g : ι → GL (Fin n) ℂ => ℓ (wtOp ℂ n mu sh g u) := by
  intro n ι _ _ mu sh
  haveI hfin : ∀ τ, FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ))) :=
    fun τ => GlobalTheory.NablaFin.dualWeyl_finite ℂ n _
  refine ⟨hfin, GlobalTheory.NablaFin.nablaT_finite ℂ n ι mu, ?_⟩
  have hd : Continuous fun g : ι → GL (Fin n) ℂ =>
      ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : ℂˣ) : ℂ) := by
    refine Units.continuous_val.comp (continuous_finset_prod _ fun τ _ => ?_)
    exact ((continuous_det_units n).comp (continuous_apply τ)).zpow _
  intro u ℓ
  induction u using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    let b := fun τ => Module.finBasis ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)))
    let M := ℓ.compMultilinearMap (PiTensorProduct.tprod ℂ)
    have e : ∀ g : ι → GL (Fin n) ℂ, ℓ (wtOp ℂ n mu sh g (c • PiTensorProduct.tprod ℂ x)) =
        c * (((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : ℂˣ) : ℂ) *
          ∑ p : ∀ τ, Fin (Module.finrank ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ)))),
            (∏ τ, (b τ).repr (Formalism.UG.dualWeylRep ℂ n n _ (g τ) (x τ)) (p τ)) * M (fun τ => b τ (p τ))) := by
      intro g
      rw [map_smul, map_smul, smul_eq_mul, wtOp_apply, map_smul, smul_eq_mul, grp_tprod']
      congr 2
      have h1 : (fun τ => Formalism.UG.dualWeylRep ℂ n n _ (g τ) (x τ)) = fun τ =>
          ∑ i, (b τ).repr (Formalism.UG.dualWeylRep ℂ n n _ (g τ) (x τ)) i • b τ i :=
        funext fun τ => ((b τ).sum_repr _).symm
      change M _ = _
      rw [h1, MultilinearMap.map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [MultilinearMap.map_smul_univ, smul_eq_mul]
    simp_rw [e]
    refine continuous_const.mul (hd.mul (continuous_finset_sum _ fun p _ => ?_))
    refine Continuous.mul (continuous_finset_prod _ fun τ _ => ?_) continuous_const
    exact (continuous_dual_dualWeylRep n _ (x τ) ((b τ).coord (p τ))).comp (continuous_apply τ)
  | add a a' ha ha' =>
    simp only [map_add]
    exact ha.add ha'

end GlobalTheory.WtCont
end
end

