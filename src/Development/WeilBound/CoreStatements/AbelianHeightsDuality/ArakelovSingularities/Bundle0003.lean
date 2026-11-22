import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1024
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.Bundle0001
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.ExistsTwistMap
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace LBIso IsProjOver)
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace

namespace GlobalTheory.Amb

theorem exists_twist_map {k : Type} [CommRing k] {X : Scheme.{0}} {n : ℕ} (e : X ⟶ PSpace k n) [IsClosedImmersion e]
    (M : LB X) (hM : M.IsLB) :
    ∃ (t r : ℕ) (g : X ⟶ PSpace k r), g ≫ PSpace.str k r = e ≫ PSpace.str k n ∧
      cls ((O1 k r).pull g) (LB.isLB_pull (O1_isLB k r) g) =
        cls M hM + (t : ℤ) • cls ((O1 k n).pull e) (LB.isLB_pull (O1_isLB k n) e) := by
  have hO : ((O1 k n).pull e).IsLB := LB.isLB_pull (O1_isLB k n) e
  obtain ⟨t₀, ht⟩ := GlobalTheory.TwistGen.twist_generated k X (e ≫ PSpace.str k n) ((O1 k n).pull e) n _ hO
    (veryAmpleBy_secPull_coord e) M hM
  obtain ⟨r, u, hu⟩ := ht (t₀.toNat : ℤ) (Int.self_le_toNat t₀)
  refine ⟨t₀.toNat, r, toProj (e ≫ PSpace.str k n) u hu, toProj_str _ _ _, ?_⟩
  have hT : (tw M ((O1 k n).pull e) (t₀.toNat : ℤ)).IsLB := LB.isLB_div hM (isLB_pw hO _)
  rw [(cls_eq_iff _ hT).2 (lbIso_pullback_O1_toProj _ u hu)]
  refine (cls_div hM (isLB_pw hO _) hT).trans ?_
  rw [GlobalTheory.EffBound.cls_pw hO, neg_smul, sub_neg_eq_add]

end GlobalTheory.Amb
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.TopologicalKrullDimOfPolyCovered
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Amb

variable {k : Type} [CommRing k]

theorem polyCovered_pSpace [IsDomain k] (N : ℕ) : PolyCovered (PSpace.str k N) N :=
  polyCovered_pSpace' N

theorem polyCovered_pullback [IsDomain k] {X Y : Scheme.{0}} (f : X ⟶ Sp k) (g : Y ⟶ Sp k) (a b : ℕ) (hf : PolyCovered f a)
    (hg : PolyCovered g b) : PolyCovered (pullback.fst f g ≫ f) (a + b) :=
  polyCovered_pullback' f g a b hf hg

theorem isIntegral_of_polyCovered [IsDomain k] {X : Scheme.{0}} (f : X ⟶ Sp k) (d : ℕ) (h : PolyCovered f d) :
    IsIntegral X :=
  isIntegral_of_polyCovered' f d h

theorem topologicalKrullDim_of_polyCovered [IsDomain k] [IsNoetherianRing k] (hk : ringKrullDim k = 1)
    {X : Scheme.{0}} (f : X ⟶ Sp k) (d : ℕ) (h : PolyCovered f d) : topologicalKrullDim X = (d + 1 : ℕ) :=
  topologicalKrullDim_of_polyCovered' hk f d h

theorem ringKrullDim_eq_one [IsDomain k] [CharZero k] (hf : Module.Finite ℤ k) : ringKrullDim k = 1 :=
  ringKrullDim_eq_one' hf

end GlobalTheory.Amb
end
end

