import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0420
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionRigid

variable {S : Scheme.{0}}

lemma comp_mulN {G : Over S} [GrpObj G] {T : Over S} (x : T ⟶ G) (N : ℕ) : x ≫ mulN G N = x ^ N := by
  induction N with
  | zero =>
    rw [pow_zero, mulN, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  | succ n ih => rw [pow_succ, mulN, ← Category.assoc, comp_lift, ih, Category.comp_id, Hom.mul_def]

def tLift {G : Over S} [GrpObj G] {N : ℕ} {T : Over S} (x : T ⟶ G) (hx : x ^ N = 1) : T ⟶ torsion G N :=
  pullback.lift x (toUnit T) (by rw [comp_mulN, hx, Hom.one_def])

lemma tLift_ι {G : Over S} [GrpObj G] {N : ℕ} {T : Over S} (x : T ⟶ G) (hx : x ^ N = 1) :
    tLift x hx ≫ torsion.ι G N = x :=
  pullback.lift_fst _ _ _

lemma ι_pow (G : Over S) [GrpObj G] (N : ℕ) : torsion.ι G N ^ N = 1 := by
  rw [← comp_mulN, Hom.one_def]
  refine (pullback.condition (f := mulN G N) (g := η[G])).trans ?_
  congr 1
  exact toUnit_unique _ _

instance mono_ι (G : Over S) [GrpObj G] (N : ℕ) : Mono (torsion.ι G N) := by
  have : Mono η[G] := ⟨fun _ _ _ => toUnit_unique _ _⟩
  exact inferInstanceAs (Mono (pullback.fst _ _))

end GlobalTheory.TorsionRigid

namespace GlobalTheory.TorsionRigid

end GlobalTheory.TorsionRigid
