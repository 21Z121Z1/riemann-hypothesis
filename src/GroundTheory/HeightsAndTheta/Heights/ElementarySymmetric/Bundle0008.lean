import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Statements
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.Inhabitants
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqCech
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqBundle
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0008

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.DivisionDimOneQuot
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

def DivisionDimOneQuot.Statement : Prop :=
  ∀ (T : ℕ) (X : EmbDatum 1) (Z : ZeroDatum X), 1 ≤ T →
    ∀ F ∈ topSections X.A X.L₂ X.L (1 + T), IsFil X.A Z.s F (T - 1) →
      ∃ h ∈ topSections X.A X.L₂ X.L (1 + 1), F = Z.s 0 ^ (T - 1) * h

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.DivisionNearS
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

def DivisionNearS.Statement : Prop :=
  ∀ (D T : ℕ) (X : EmbDatum D) (Z : ZeroDatum X) (φA : TwistWeight X.A X.L₂ X.L D), 1 ≤ D → D ≤ T →
    ∀ F ∈ Vnat X.A X.L₂ X.L φA.φ (fsWeight X.e) T, IsFil X.A Z.s F (T - D) →
      ∀ t : ℝ, t < (T : ℝ) - 1 →
        skodaNormSq X.A Z.s (fun a x => φA.φ a x + ((T : ℝ) - 1 - t) * fsWeight X.e a x) (t + 1) F
          < ⊤

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PGradedCech
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

theorem GradedCech.proof : GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech.proof

end GroundTheory.Heights₂.Heights.Swarm
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PTwistFiniteNe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

theorem TwistFiniteNe.proof (hT1 : Kleiman.TwistFinite.Statement.{0, 0}) : TwistFiniteNe.Statement :=
  (TwistFinite.equiv_ne LineBundle.proof).mp hT1

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StRestrLenEuler
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def RestrLenEuler.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (qq : Ideal (Poly k N)), (∀ f ∈ qq, ∀ d : ℕ, homogeneousComponent d f ∈ qq) →
    primeOf (S := k) x ≤ qq → ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ),
      ∀ᶠ c : ℤ in atTop,
        restrLen qq (((twistSys k x 0).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c)) =
          pieceChar k qq 0 L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StSubsetDiffConst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

def subsetDiff (n : ℕ) (f : (Fin (n + 1) → ℕ) → ℤ → ℚ) (m : ℕ) (c : ℤ) : ℚ :=
  ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) *
    f (Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m) c

def SubsetDiffConst.Statement : Prop :=
  ∀ (n : ℕ) (f : (Fin (n + 1) → ℕ) → ℤ → ℚ), IsNumPolyLT (n + 1) (n + 1) f →
    (∀ (m m' : ℕ) (c c' : ℤ), subsetDiff n f m c = subsetDiff n f m' c') ∧
      (IsNumPolyLT (n + 1) n f → ∀ (m : ℕ) (c : ℤ), subsetDiff n f m c = 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StVarIntGraphCompact
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open GroundTheory.Heights₂.Heights (varInt SmoothNear euclPot contDiff_euclPot)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
open scoped ContDiff

def VarIntGraphCompact.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) (F : (Fin (n + 1) → ℂ) → ℝ)
    (Φ : Fin e → (Fin (n + 1) → ℂ) → ℝ),
    J.IsPrime → SmoothNear (zeroSet (graphIdeal J p)) F → HasCompactSupport F →
    (∀ k, SmoothNear (zeroSet (graphIdeal J p)) (Φ k)) →
      varInt (graphIdeal J p) e F Φ = varInt J e (fun x => F (graphPt p x)) (fun k x => Φ k (graphPt p x))

end GroundTheory.Heights₂.Heights.Targets
end
end

