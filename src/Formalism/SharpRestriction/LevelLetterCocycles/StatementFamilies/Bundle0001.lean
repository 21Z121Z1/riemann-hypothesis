import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.ParConsts
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ArcLiftingSetup
section
noncomputable section

namespace Formalism.MainNotions.ArcLiftingSetup

open Formalism.BasicNotions

abbrev LayF (Dm : Formalism.MainNotions.DFamP) : Type 1 :=
  ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52) (x : ℝ) (i : (Dm ε h0 h1).Ix x),
    Σ HW : Formalism.BasicNotions.HWOf ((Dm ε h0 h1).D x i).loc,
      Σ F : Formalism.BasicNotions.FonOf ((Dm ε h0 h1).D x i).loc ((Dm ε h0 h1).D x i).locA HW,
        Formalism.BasicNotions.CmpOf ((Dm ε h0 h1).D x i).loc ((Dm ε h0 h1).D x i).locA HW F

def OrbitValuationBound (Dm : Formalism.MainNotions.DFamP) (L : LayF Dm) : Prop :=
  ∃ C₀ : ℝ, ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52), ∃ x0 : ℝ, ∀ C : ℝ, C₀ ≤ C → ∀ x : ℝ, x0 ≤ x →
    ∀ i : (Dm ε h0 h1).Ix x, aux₃ ((Dm ε h0 h1).D x i) (L ε h0 h1 x i).1 (L ε h0 h1 x i).2.1 C

def AdmF (Dm : Formalism.MainNotions.DFamP) (L : LayF Dm) : Prop :=
  ∃ CR CA CB CK Ckap : ℝ, ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52), ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
    ∀ i : (Dm ε h0 h1).Ix x,
      admitted ((Dm ε h0 h1).D x i) (L ε h0 h1 x i).1 (L ε h0 h1 x i).2.1 (L ε h0 h1 x i).2.2 CR CA CB CK Ckap

def KudlaFamilyStatement (Dm : Formalism.MainNotions.DFamP) (L : LayF Dm) : Prop := AdmF Dm L → OrbitValuationBound Dm L

end Formalism.MainNotions.ArcLiftingSetup

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ExportFamilies
section
noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions

def FamilyThinScalesBound {eps : ℝ} (Fm : FamP eps) (C : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, aux₃ (Fm.L x i) C

def OrbitValuationBound {eps : ℝ} (Fm : FamP eps) : Prop := ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, aux₃ (Fm.L x i) C

def AdmFC {eps : ℝ} (Fm : FamP eps) (C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), admitted (Fm.L x i) (Fm.params x hx i) C

def AdmF {eps : ℝ} (Fm : FamP eps) : Prop := ∃ C : ℝ, AdmFC Fm C

def KudlaFamilyStatement {eps : ℝ} (Fm : FamP eps) : Prop := AdmF Fm → OrbitValuationBound Fm

def UniformExportStatement (eps : ℝ) : Prop := ∀ Ca : ℝ, ∃ C : ℝ, ∀ Fm : FamP eps, AdmFC Fm Ca → FamilyThinScalesBound Fm C

theorem stmtF_of_stmtU {eps : ℝ} (h : UniformExportStatement eps) (Fm : FamP eps) : KudlaFamilyStatement Fm := by
  rintro ⟨Ca, hA⟩
  obtain ⟨C, hC⟩ := h Ca
  obtain ⟨x0, h0⟩ := hC Fm hA
  exact ⟨C, x0, h0⟩

end Formalism.MainNotions.TwistedPlaces

namespace Formalism.MainNotions.ExportFamilies

open Formalism.BasicNotions Formalism.MainNotions

abbrev FamilyThinScalesBound {eps : ℝ} (Fm : FamP eps) (C : ℝ) : Prop := TwistedPlaces.FamilyThinScalesBound Fm C

abbrev OrbitValuationBound {eps : ℝ} (Fm : FamP eps) : Prop := TwistedPlaces.OrbitValuationBound Fm

abbrev AdmFC {eps : ℝ} (Fm : FamP eps) (C : ℝ) : Prop := TwistedPlaces.AdmFC Fm C

abbrev AdmF {eps : ℝ} (Fm : FamP eps) : Prop := TwistedPlaces.AdmF Fm

abbrev KudlaFamilyStatement {eps : ℝ} (Fm : FamP eps) : Prop := TwistedPlaces.KudlaFamilyStatement Fm

abbrev UniformExportStatement (eps : ℝ) : Prop := TwistedPlaces.UniformExportStatement eps

theorem stmtF_of_stmtU {eps : ℝ} (h : UniformExportStatement eps) (Fm : FamP eps) : KudlaFamilyStatement Fm := TwistedPlaces.stmtF_of_stmtU h Fm

end Formalism.MainNotions.ExportFamilies

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.SumRepresentations
section
noncomputable section

namespace Formalism.MainNotions.SumRepresentations

open Formalism.BasicNotions Formalism.MainNotions

def ConclusionF1 {eps : ℝ} (Fm : FamP eps) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Conclusion1 (Fm.D x i)

def ConclusionF2 {eps : ℝ} (Fm : FamP eps) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Conclusion2 (Fm.D x i)

def AdmAF {eps : ℝ} (Fm : FamP eps) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, AdmAt (Fm.D x i)

def AdmF {eps : ℝ} (Fm : FamP eps) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, admitted (Fm.D x i)

def KudlaFamilyStatement {eps : ℝ} (Fm : FamP eps) : Prop := (AdmAF Fm → ConclusionF1 Fm) ∧ (AdmF Fm → ConclusionF2 Fm)

end Formalism.MainNotions.SumRepresentations

end
end

