import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData

-- bundled from Formalism.SharpRestriction.SmoothDesignExistence.EvSplit
section
noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions

def EvL {eps : ℝ} (Fm : FamP eps) (P : ∀ x, Fm.x1 < x → Fm.Ix x → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), P x hx i

theorem EvL.and {eps : ℝ} {Fm : FamP eps} {P Q : ∀ x, Fm.x1 < x → Fm.Ix x → Prop} (hP : EvL Fm P) (hQ : EvL Fm Q) :
    EvL Fm fun x hx i => P x hx i ∧ Q x hx i := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨b, hb⟩ := hQ
  exact ⟨max a b, fun x hx h1 i =>
    ⟨ha x (le_trans (le_max_left _ _) hx) h1 i, hb x (le_trans (le_max_right _ _) hx) h1 i⟩⟩

theorem EvL.mono {eps : ℝ} {Fm : FamP eps} {P Q : ∀ x, Fm.x1 < x → Fm.Ix x → Prop} (hP : EvL Fm P)
    (h : ∀ x hx i, P x hx i → Q x hx i) : EvL Fm Q := by
  obtain ⟨a, ha⟩ := hP
  exact ⟨a, fun x hx h1 i => h x h1 i (ha x hx h1 i)⟩

theorem EvD.toL {eps : ℝ} {Fm : FamP eps} {P : D7 → Prop} (h : EvD Fm P) : EvL Fm fun x _ i => P (Fm.D x i) := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun x hx _ i => ha x hx i⟩

end Formalism.MainNotions.Pk

end
end

-- bundled from Formalism.SharpRestriction.SmoothDesignExistence.PlaceDegreeData
section
noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions

structure CountingHypotheses : Prop where

  p30 : PlaceDegreeData.UniformExportStatement
  admOne : ∀ D : D7, PlaceDegreeData.adm1 D
  local_admissible_second : ∀ D : D7, PlaceDegreeData.adm2 D
  local_admissible_third : ∀ D : D7, PlaceDegreeData.adm3 D
  siegelMassRatioAlt : Formalism.HermitianLatticesTheory.SiegelMassRatio
  admFive : ∀ D : D7, PlaceDegreeData.adm5 D
  local_admissible_sixth : ∀ D : D7, PlaceDegreeData.adm6 D
  residueConstantBound : ∃ Cres : ℝ, ∀ D : D7, PlaceDegreeData.adm7 D Cres
  admEight : ∀ D : D7, PlaceDegreeData.adm8 D

end Formalism.MainNotions.Pk

end
end

