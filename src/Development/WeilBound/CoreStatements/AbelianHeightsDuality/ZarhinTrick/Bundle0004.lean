import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.PolQuasiInverse

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.IsLBZb
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

section Bundle

variable (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ) {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S)

def pA (i : Fin 4) : (Over.pullback s).obj (G4 (A ⊗ B)) ⟶ (Over.pullback s).obj A :=
  (Over.pullback s).map (prj (A ⊗ B) i ≫ fst A B)

def pM (i : Fin 4) : (Over.pullback s).obj (G4 (A ⊗ B)) ⟶ (Over.pullback s).obj A :=
  (Over.pullback s).map (prj (A ⊗ B) i ≫ snd A B ≫ mu)

def phiL : Fin 4 × Fin 4 → (((Over.pullback s).obj (G4 (A ⊗ B))).left ⟶ ((Over.pullback s).obj A).left)
  | (0, i) => (pA s i).left
  | (1, i) => (pA s i)⁻¹.left
  | (2, i) => (pM mu s i).left
  | (3, i) => (pM mu s i)⁻¹.left

def phiP (ij : Fin 4 × Fin 4) : ((Over.pullback s).obj (G4 (A ⊗ B))).left ⟶ (A ⊗ B).left :=
  (toBase (G4 (A ⊗ B)) s (𝟙 _) ≫ lift (prj (A ⊗ B) ij.1 ≫ fst A B) (prj (A ⊗ B) ij.2 ≫ snd A B)).left

def zb (P : LB (A ⊗ B).left) (L : LB ((Over.pullback s).obj A).left) :
    LB ((Over.pullback s).obj (G4 (A ⊗ B))).left :=
  tens (LB.LinComb L (phiL mu s) fun _ => 1) (LB.LinComb P (phiP s) fun ij => α ij.1 ij.2)

theorem isLB_zb {P : LB (A ⊗ B).left} (hP : P.IsLB) {L : LB ((Over.pullback s).obj A).left} (hL : L.IsLB) :
    (zb mu α s P L).IsLB :=
  isLB_tens (LB.isLB_linComb hL _ _) (LB.isLB_linComb hP _ _)

end Bundle

end PositivityTheory.PrwZar
end
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.OneCompPrj
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

omit [GrpObj A] [GrpObj B] in

theorem one_comp_prj {G : Over S} [GrpObj G] {Y : Over S} (i : Fin 4) : (1 : Y ⟶ G4 G) ≫ prj G i = 1 := by
  fin_cases i <;> simp [prj]

theorem zc_rigid {P : LB (A ⊗ B).left} (hD : IsDual A B P) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu]
    (α : Matrix (Fin 4) (Fin 4) ℤ) :
    pull (lift (1 : G4 (A ⊗ B) ⟶ G4 (A ⊗ B)) (𝟙 _)).left (zc hD.isLB l mu α) = 0 ∧
      pull (lift (𝟙 _) (1 : G4 (A ⊗ B) ⟶ G4 (A ⊗ B))).left (zc hD.isLB l mu α) = 0 := by
  have e1 : ∀ {Y : Over S} (t : Y ⟶ B), evc hD.isLB (1 : Y ⟶ A) t = 0 :=
    fun t => IsAdditive.evc_one hD.isLB hD.additive t
  have e2 : ∀ {Y : Over S} (a : Y ⟶ A), evc hD.isLB a (1 : Y ⟶ B) = 0 :=
    fun a => evc_one_right hD.isLB hD.zero a
  have o1 : ∀ {Y : Over S} (i : Fin 4) (f : A ⊗ B ⟶ A) [IsMonHom f],
      (1 : Y ⟶ G4 (A ⊗ B)) ≫ prj _ i ≫ f = 1 := by
    intro Y i f _; rw [← Category.assoc, one_comp_prj, MonObj.one_comp]
  have o2 : ∀ {Y : Over S} (i : Fin 4) (f : A ⊗ B ⟶ B) [IsMonHom f],
      (1 : Y ⟶ G4 (A ⊗ B)) ≫ prj _ i ≫ f = 1 := by
    intro Y i f _; rw [← Category.assoc, one_comp_prj, MonObj.one_comp]
  constructor <;>
  · simp only [zc, zcPair, map_add, map_sum, map_nsmul, map_zsmul, pull_evc, lift_fst_assoc, lift_snd_assoc,
      Category.id_comp, o1, o2, e1, e2, smul_zero, add_zero, zero_add, Finset.sum_const_zero]

end PositivityTheory.PrwZar
end
end

