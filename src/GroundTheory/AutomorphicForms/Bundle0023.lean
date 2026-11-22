import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.Uniqueness
import GroundTheory.AutomorphicForms.GL2Classical.Smooth

-- bundled from GroundTheory.AutomorphicForms.ArchimedeanWhittaker
section
namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix
open scoped Matrix.Norms.L2Operator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def toTopRep (σ : UnitaryRep (GL (Fin 2) ℝ) H) : UnitaryRep FiltrationCocycleLiftCriterion H where
  toHom := σ.toHom.comp FiltrationCocycleLiftCriterion.subtype
  continuous_orbit' v := (σ.continuous_orbit v).comp continuous_subtype_val

@[simp] theorem toTopRep_apply (σ : UnitaryRep (GL (Fin 2) ℝ) H) (g : FiltrationCocycleLiftCriterion) :
    toTopRep σ g = σ (g : GL (Fin 2) ℝ) := rfl

noncomputable def upperUnipotent (x : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1] (by simp)

abbrev SmoothVectorsGL2 (σ : UnitaryRep (GL (Fin 2) ℝ) H) : Type _ :=
  hGL2.SmoothFrechet (πσ (toTopRep σ))

noncomputable abbrev whittakerFunctionals (σ : UnitaryRep (GL (Fin 2) ℝ) H) (ψ : ℝ → ℂ) :
    Submodule ℂ (SmoothVectorsGL2 σ →L[ℂ] ℂ) :=
  whitSpace (toTopRep σ) ψ

end GroundTheory.Automorphic.ArchWhittaker
end

-- bundled from GroundTheory.AutomorphicForms.GL2Classical
section
open NumberField Matrix CongruenceSubgroup
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Manifold

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem liftEquiv_spec_of_mdifferentiable
    (f : SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (hhol : MDiff (f : ℍ → ℂ)) :
    IsLeftInvariant (liftEquiv N k f : AdelicGL ℚ 2 → ℂ) ∧
      IsSmooth (liftEquiv N k f : AdelicGL ℚ 2 → ℂ) ∧ IsKFinite (liftEquiv N k f : AdelicGL ℚ 2 → ℂ) :=
  ⟨(liftEquiv N k f).2.isLeftInvariant,
    isSmooth_adelicLift (fun γ hγ => SlashInvariantForm.slash_action_eqn f γ hγ) hhol,
    (liftEquiv N k f).2.isKFinite⟩

theorem liftEquiv_cuspForm_spec (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    IsLeftInvariant (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) ∧
      IsSmooth (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) ∧
      IsKFinite (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) ∧
      HasModerateGrowth (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) ∧
      IsCuspidal (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) := by
  obtain ⟨h1, h2, h3⟩ := liftEquiv_spec_of_mdifferentiable f.toSlashInvariantForm f.holo'
  exact ⟨h1, h2, h3, hasModerateGrowth_liftEquiv_cuspForm f, isCuspidal_liftEquiv_cuspForm f⟩

theorem mem_cuspForms_of_isZFinite (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hZ : IsZFinite (⟨(liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ),
      (liftEquiv_cuspForm_spec f).2.1.1⟩ : archSmooth ℚ 2)) :
    (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) ∈ cuspForms ℚ 2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := liftEquiv_cuspForm_spec f
  exact ⟨⟨h1, h2, h3, hZ, h4⟩, h5⟩

end GL2Classical

end

end GroundTheory.Automorphic
end

