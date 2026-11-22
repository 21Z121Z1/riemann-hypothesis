import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PrimitiveExpansionThetaPullbackHeisenbergTransla
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PrimitiveExpansionThetaPullbackHeisenbergTranslaStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_expansion_thetaPullback_heisenbergTranslates : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ (m : ℕ), Odd m → IsUnit (m : V) → ∀ x t c s, x ^ (m ^ 2) = 1 → ThC A ρ m th x t c → U.ExpandsF F (m ^ 2) w₀ t s → Prim D Q v s := by
  first | exact @GlobalTheory.UT.PrimPull.main | exact GlobalTheory.UT.PrimPull.main | (intros; apply GlobalTheory.UT.PrimPull.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTermsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_value_at_torsionPoint_eq_sum_terms : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (n : ℕ), 1 ≤ n → ∀ (p : QkPt D.toPre F n) x, QkToAkU U.toUnifPre F n p x → ∀ e, IsTorsFrame A ρ n x e → ∃ w₁ : Frm D.toPre F 1 p.g.b, w₁.IsGen ∧ GenV hϖ hv w₁ ((Q p.y : ℚ) / (n : ℚ) ^ 2) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ w : Frm D.toPre F k p.g.b, (w.IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J = val w₁ (𝟙 _) z J ^ k) → ∀ (t : SecA A F k) s (c : F), U.ExpandsF F k w₀ t s → (∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J = @id ((TFK (R := V) F).left.presheaf.stalk z) (cst (R := V) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val) → SumV v (coef s p.g w) c := by
  first | exact @GlobalTheory.UT.TorsionValue.value_at_torsion | exact GlobalTheory.UT.TorsionValue.value_at_torsion | (intros; apply GlobalTheory.UT.TorsionValue.value_at_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SubsingletonIffUnitThetaConst
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT
open GlobalTheory.TorusExt

attribute [local instance] gtGroup

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  (hB : D.TauBimult) {k : ℕ}

def qkMul (j : ℕ) (p : QkPt D F k) : QkPt D F k :=
  qkMk hB (j • p.y) (j • p.g) (by rw [smul_comm, qk_nsmul hB, map_nsmul])

theorem map_qkMul {M : Type} [Group M] (f : QkPt D F k → M)
    (hf : ∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') (p : QkPt D F k) (j : ℕ) :
    f (qkMul hB j p) = f p ^ j := by
  have add : ∀ i j : ℕ, f (qkMul hB (i + j) p) = f (qkMul hB i p) * f (qkMul hB j p) := fun i j => by
    refine hf _ _ _ ?_
    have e : qkMul hB (i + j) p = qkAdd hB (qkMul hB i p) (qkMul hB j p) :=
      qk_ext (add_smul i j p.y) (add_nsmul p.g i j)
    rw [e]
    exact qkAdd_qkAdd hB _ _
  induction j with
  | zero =>
    have h := add 0 0
    rw [pow_zero]
    exact left_eq_mul.1 h
  | succ j ih =>
    have e : qkMul hB 1 p = p := qk_ext (one_nsmul _) (one_nsmul _)
    rw [add, ih, e, pow_succ]

theorem equiv_qkMul_self (p : QkPt D F k) : QkPt.Equiv D F (qkMul hB 0 p) (qkMul hB k p) := by
  refine (equiv_iff hB _ _).2 ⟨p.y, ?_, ?_⟩
  · show k • p.y = 0 • p.y + k • p.y
    rw [zero_nsmul, zero_add]
  · show k • p.g = 0 • p.g + iota hB F p.y
    rw [zero_nsmul, zero_add, qk_nsmul hB]

end

end GlobalTheory.UT
end
end

