import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.ArchBaseChangeOfHyp
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.FieldNOf
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.CauchyLoc

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.DescOffT
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.Desc

open PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def ExtExp (σ : Submodule ℂ (UA E n → ℂ)) (w : Pl E) (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (β : Fin (n / 2) → ℂˣ) : Prop :=
  ∃ τ : SmIrr (UL n w), IsCompU σ w τ ∧ ∃ y ∈ fixed τ.ρ (iwU n w b), y ≠ 0 ∧ ∀ l : Fin (n / 2) → ℤ, Cone l →
    levOp τ.ρ (KL n w) (iwU n w b) (fU n w b ϖ l) LinearMap.id y =
      ((((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹ * dlt n w l * pw β l) • y

def IsExtOf (π : CuspSub E n) (w : Pl E) (β : Fin (n / 2) → ℂˣ) : Prop :=
  (∀ i j : Fin (n / 2), i ≤ j → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖) ∧ (∀ i, 1 ≤ ‖(β i : ℂ)‖) ∧
    ∃ B, (CG.mk π).HasSat w B ∧ ∀ α : Fin (n / 2) → ℂˣ, GlobalTheory.LGrp.bcParam n α = B → GlobalTheory.LGrp.WeylConjU α β

def DescOffT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) →
  ∀ Z : Finset (Pl E), ∃ T : Finset (Pl E), Disjoint T Z ∧ (∀ w ∈ T, ¬ IsSplitAt w) ∧
    ∃ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ ∧
      (∀ φ : E →+* ℂ, ∃ lam, HasWeightAt σ φ lam ∧ π.HasInfChar φ (infOfWeight lam)) ∧
      (∀ w, IsSplitAt w → ∀ τ, π.IsLocComp w τ → Comp σ w τ) ∧
      (∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU σ w) ∧
      ∀ w ∈ T, ∀ (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ), IsWitt n w b → IsUnifAt ϖ → ∃ β, IsExtOf π w β ∧ ExtExp σ w b ϖ β

def RunExpT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
  ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ → ∀ (T : Finset (Pl E)) (β : ∀ w : Pl E, Fin (n / 2) → ℂˣ)
    (b : ∀ w : Pl E, GLw n w) (ϖ : ∀ w : Pl E, (w.adicCompletion E)ˣ), (∀ w ∈ T, ¬ IsSplitAt w ∧ IsWitt n w (b w) ∧
      IsUnifAt (ϖ w) ∧ (∀ i j : Fin (n / 2), i ≤ j → ‖(β w j : ℂ)‖ ≤ ‖(β w i : ℂ)‖) ∧ (∀ i, 1 ≤ ‖(β w i : ℂ)‖) ∧
      ExtExp σ w (b w) (ϖ w) (β w)) →
    ∃ D : Pre E n, PositivityTheory.Rg.BcB.One.Base σ D ∧ (∀ w, IsSplitAt w → D.SplitAt σ w) ∧ D.ThetaStable ∧
      (∀ w ∈ T, ∀ α, GlobalTheory.LGrp.WeylConjU α (β w) → D.Sat w (GlobalTheory.LGrp.bcParam n α)) ∧
      ∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU σ w → PositivityTheory.Rg.BcB.One.InertAt σ D w

end PositivityTheory.Rg.BcB.Desc

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.DescentOfLocalGlobalInputs
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.Desc

open PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def Temp (π : CG E n) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, π.HasSat w B ∧ ∀ z ∈ B, ‖(z : ℂ)‖ = 1

def TempOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → Temp (CG.mk π)

def RTemp : Prop := GlobalTheory.Published.GaloisRepOfPolarizedPair → GlobalTheory.Published.LocalLanglandsGL → GlobalTheory.Published.JacquetShalikaRigidity → TempOf

def SplitCore : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CG E n, π.IsUnitary → Temp π →
  ∀ (J : Type) [Fintype J] (a : J → ℕ) (P : ∀ j, CG E (a j)), (∀ j, 1 ≤ a j) → (∀ j, (P j).IsUnitary) →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w →
      ∃ b : J → Multiset ℂˣ, (∀ j, (P j).HasSat w (b j)) ∧ π.HasSat w (∑ j, b j)) →
    ∃ j, (⟨a j, P j⟩ : Σ m, CG E m) = ⟨n, π⟩

def RSplitCore : Prop := PositivityTheory.RgJS.RSU → GlobalTheory.Published.JacquetShalikaBound → SplitCore

def SplitAll : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsUnitary → Temp (CG.mk π) → ∀ D : Pre E n, D.Reg → SplitLike D π →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B

def RSplitAll : Prop := SplitCore → Rig.StrSat → Strings → SplitAll

def UnitOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  GlobalTheory.ContraPair.DualIsConj π → (CG.mk π).IsUnitary

def RunDesc2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) →
    (∃ σ, WeakDesc σ π) ∨ ∃ D : Pre E n, D.Reg ∧ SplitLike D π ∧ ¬ IsOne D π

end PositivityTheory.Rg.BcB.Desc

end
end

