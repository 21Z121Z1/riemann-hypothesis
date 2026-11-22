import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace BigA

open Complex Matrix ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate

theorem projPerp_self {N : ℕ} (g0 : Fin N → ℂ) (h : g0 ≠ 0) : projPerp g0 *ᵥ g0 = 0 := by
  have hs : (sqNorm g0 : ℂ) ≠ 0 := by
    exact_mod_cast (sqNorm_pos h).ne'
  have e : star g0 ⬝ᵥ g0 = (sqNorm g0 : ℂ) := by
    simp [sqNorm, dotProduct, Complex.normSq_eq_conj_mul_self]
  funext i
  simp only [projPerp, sub_mulVec, one_mulVec, smul_mulVec, Pi.sub_apply, Pi.smul_apply,
    Pi.zero_apply, smul_eq_mul]
  rw [show (vecMulVec g0 (star g0) *ᵥ g0) i = g0 i * (star g0 ⬝ᵥ g0) by
    simp [vecMulVec, mulVec, dotProduct, Finset.mul_sum, mul_assoc], e]
  field_simp
  ring

end BigA

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DescentStatementPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DescPf

open scoped TensorProduct
open Module

variable {F F' V : Type} [Field F] [Field F'] [Algebra F F'] [AddCommGroup V] [Module F V]

theorem indep_iff {ι : Type} (v : ι → V) :
    LinearIndependent F v ↔ LinearIndependent F' (fun i => (1 : F') ⊗ₜ[F] v i) := by
  constructor
  · intro hv
    exact Module.Flat.linearIndependent_one_tmul hv
  · intro h
    have h' : LinearIndependent F (fun i => (1 : F') ⊗ₜ[F] v i) :=
      h.restrict_scalars' F
    exact LinearIndependent.of_comp (TensorProduct.mk F F' V 1) h'

end ReciprocityTheory.ChartRestriction.G.AR.Up.DescPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

