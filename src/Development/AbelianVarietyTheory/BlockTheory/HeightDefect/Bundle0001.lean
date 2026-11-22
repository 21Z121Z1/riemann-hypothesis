import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CanonicalPsiNormOne
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CanonicalPsiTorsionNorm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Can

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

def canφ (k : ℕ) : Fin 8 → ((A ⊗ A).left ⟶ A.left) :=
  ![(padd A (fst A A ^ k) (snd A A ^ k)).left, (fst A A ^ k).left, (snd A A ^ k).left, (pzero A (A ⊗ A)).left,
    (padd A (fst A A) (snd A A)).left, (fst A A).left, (snd A A).left, (pzero A (A ⊗ A)).left]

def canε (k : ℕ) : Fin 8 → ℤ := ![1, -1, -1, 1, -(k : ℤ) ^ 2, (k : ℤ) ^ 2, (k : ℤ) ^ 2, -(k : ℤ) ^ 2]

example (k : ℕ) : ∑ i, canε k i = 0 := by simp [canε, Fin.sum_univ_succ]

def IsCanIso (L : LB A.left) (k : ℕ) (u : LB.Gen (LB.LinComb L (canφ A k) (canε k))) : Prop :=
  u.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (Out.zero2 A)) (LB.oneGen L)

def IsDiagPull (L : LB A.left) (f : A ⟶ A) : Prop :=
  ∃ u : LB.Gen (LB.LinComb L (K := Fin 4)
      ![(padd A (𝟙 A) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left] ![1, -2, -1, 2]),
    u.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (eSec A)) (LB.oneGen L)

end Can

section Out

variable {R : Type} [CommRing R] [IsDomain R]

def TauPowCan (D : Out.DegPre R) (k : ℕ) : Prop :=
  (∃ u, IsCanIso D.P.A D.P.L k u) ∧
    ∀ u, IsCanIso D.P.A D.P.L k u → ∀ y y' : D.X,
      LB.Gen.Corr D.P.L _ _ _ _ (Out.GeneratorPullback.powGen D.P.L _ _ (D.tau y y') (k ^ 2))
        (LB.pullGen D.P.L _ _ u (D.pt2 y y'))

def PsiNormOne (D : Out.DegPre R) (σ : FractionRing R →+* ℂ) : Prop :=
  ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ D.P.A.left)
    (he : eSec A ≫ φ = spMap (σ.comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A),
    IsGrpPullback A D.P.A (spMap (σ.comp (algebraMap R (FractionRing R)))) φ →
    ∀ (u : HolUnif A (D.P.L.pull φ) D.P.g) (Hm : Matrix (Fin D.P.g) (Fin D.P.g) ℂ) (χ : u.Λ → ℂ),
      u.IsAH Hm χ → u.IsRig (rigPullOf φ (spMap (σ.comp (algebraMap R (FractionRing R)))) he D.P.L D.rig) →
      ∀ (y : D.X) (z : Fin D.P.g → ℂ), (u.ex z).left ≫ φ = spMap σ ≫ D.xK y →
        ∀ j : PUnit → D.P.L.ι, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (D.P.L.pull φ).U j →
          ‖valAt' (X := (Out.TK R).left) (spMap σ) _ ((D.psi y).s j).val * u.fr j z‖ =
            Real.exp (-(Real.pi / 2) * (z ⬝ᵥ Hm.mulVec (star z)).re)

end Out

def TorsionTau : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
    letI := H.starRing
    ∀ (K₁ : Type) [Field K₁] [NumberField K₁] (P : Out.PolAV (Sp (𝓞 K₁)))
      (rig : LB.Gen (P.L.pull (eSec P.A))) (oa : P.OAct (𝓞 E))
      (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] [Module (𝓞 E) Y]
      (c₀ : Y → (𝟙_ (Over (Sp (𝓞 K₁))) ⟶ P.A)) (k : ℕ),
      rig.IsGen → IsDiagPull P.A P.L (oa.act H.w0) →
      (∀ y y', c₀ (y + y') = padd P.A (c₀ y) (c₀ y')) →
      (∀ (a : 𝓞 E) y, c₀ (a • y) = c₀ y ≫ oa.act a) →
      1 ≤ k → (∀ y, c₀ y ^ k = 1) →
      ∃ (K₂ : Type) (_ : Field K₂) (_ : NumberField K₂) (_ : Algebra K₁ K₂)
        (D₀ : Out.DegPre (𝓞 K₂)) (_ : Module (𝓞 E) D₀.X) (oa₀ : D₀.OAct (𝓞 E))
        (φ : D₀.P.A.left ⟶ P.A.left)
        (he : eSec D₀.P.A ≫ φ = spMap (algebraMap (𝓞 K₁) (𝓞 K₂)) ≫ eSec P.A)
        (w : LB.Iso D₀.P.L (P.L.pull φ)) (e : Y ≃ₗ[𝓞 E] D₀.X),

        (IsGrpPullback D₀.P.A P.A (spMap (algebraMap (𝓞 K₁) (𝓞 K₂))) φ ∧ w.IsGen ∧
          LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D₀.P.A) (fun _ => 1)) D₀.rig
            (rigPullOf φ (spMap (algebraMap (𝓞 K₁) (𝓞 K₂))) he P.L rig) ∧
          (∀ a, (oa₀.onB.act a).left ≫ φ = φ ≫ (oa.act a).left) ∧
          (∀ y, (D₀.c (e y)).left ≫ φ = spMap (algebraMap (𝓞 K₁) (𝓞 K₂)) ≫ (c₀ y).left)) ∧
        D₀.TauBimult ∧ TauPowCan D₀ k ∧
        TraceFormTwistIso D₀ oa₀ H.w0 ∧ D₀.PsiEven ∧
        (∀ y, PsiUnitOn D₀ y Set.univ) ∧
        ∀ σ : FractionRing (𝓞 K₂) →+* ℂ, PsiNormOne D₀ σ

end GlobalTheory.IndefiniteRowSideFullHecke.CanonicalPsiTorsionNorm
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.HeightDefect.CanonicalTauPower
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CanonicalTauPower

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

def IsBaseChange {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')
    (P' : Out.PolAV (Sp R')) (rig' : LB.Gen (P'.L.pull (eSec P'.A)))
    (P : Out.PolAV (Sp R)) (rig : LB.Gen (P.L.pull (eSec P.A)))
    (φ : P'.A.left ⟶ P.A.left) (w : LB.Iso P'.L (P.L.pull φ)) : Prop :=
  IsGrpPullback P'.A P.A (spMap f) φ ∧ w.IsGen ∧
    ∃ he : eSec P'.A ≫ φ = spMap f ≫ eSec P.A,
      LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec P'.A) (fun _ => 1)) rig'
        (rigPullOf φ (spMap f) he P.L rig)

def IsDiagPull {S : Scheme.{0}} (P : Out.PolAV S) (f : P.A ⟶ P.A) : Prop :=
  ∃ u : LB.Gen (LB.LinComb P.L (K := Fin 4)
      ![(padd P.A (𝟙 _) f).left, 𝟙 P.A.left, f.left, (toUnit P.A ≫ η[P.A]).left] ![1, -2, -1, 2]),
    u.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ u (eSec P.A)) (LB.oneGen P.L)

def canφ {S : Scheme.{0}} (P : Out.PolAV S) (k : ℕ) : Fin 8 → ((P.A ⊗ P.A).left ⟶ P.A.left) :=
  ![(padd P.A (fst P.A P.A) (snd P.A P.A)).left, (fst P.A P.A).left, (snd P.A P.A).left,
    (toUnit (P.A ⊗ P.A) ≫ η[P.A]).left,
    (padd P.A (fst P.A P.A ^ k) (snd P.A P.A ^ k)).left, (fst P.A P.A ^ k : P.A ⊗ P.A ⟶ P.A).left,
    (snd P.A P.A ^ k : P.A ⊗ P.A ⟶ P.A).left, (toUnit (P.A ⊗ P.A) ≫ η[P.A]).left]

def canε (k : ℕ) : Fin 8 → ℤ :=
  ![(k : ℤ) ^ 2, -(k : ℤ) ^ 2, -(k : ℤ) ^ 2, (k : ℤ) ^ 2, -1, 1, 1, -1]

section Data

variable {R : Type} [CommRing R] [IsDomain R]

def TauPowCan (D : Out.DegPre R) (k : ℕ) : Prop :=
  ∃ u : LB.Gen (LB.LinComb D.P.L (canφ D.P k) (canε k)), u.IsGen ∧
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (Out.zero2 D.P.A)) (LB.oneGen D.P.L) ∧
    ∀ y y' : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (Out.GeneratorPullback.powGen D.P.L _ _ (D.tau y y') (k ^ 2))
        (LB.pullGen D.P.L _ _ u (D.pt2 y y')))
      (LB.oneGen D.P.L)

def TauSymm (D : Out.DegPre R) : Prop :=
  ∀ y y' : D.X, LB.Gen.Corr D.P.L _ _ _ _ (D.tau y y') (D.tau y' y)

def PsiNormOne (D : Out.DegPre R) (s : FractionRing R →+* ℂ) : Prop :=
  ∀ (P' : Out.PolAV (Sp ℂ)) (rig' : LB.Gen (P'.L.pull (eSec P'.A))) (φ : P'.A.left ⟶ D.P.A.left)
    (w : LB.Iso P'.L (D.P.L.pull φ)), rig'.IsGen →
    IsBaseChange (s.comp (algebraMap R (FractionRing R))) P' rig' D.P D.rig φ w →
    ∀ (u : HolUnif P'.A P'.L P'.g) (Hm : Matrix (Fin P'.g) (Fin P'.g) ℂ) (χ : u.Λ → ℂ),
      u.IsAH Hm χ → u.IsRig rig' →
      ∀ (y : D.X) (z : Fin P'.g → ℂ), (u.ex z).left ≫ φ = spMap s ≫ D.xK y →
        ∀ (j : D.P.L.ι) (i : P'.L.ι),
          ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.div (D.P.L.pull φ) P'.L).U (fun _ => j, i) →
          ‖valF (F := ℂ) (spMap s) _ ((D.psi y).s (fun _ => j)).val *
              valF (F := ℂ) (u.ex z).left _ (w.s (fun _ => j, i)).val * u.fr i z‖ ^ 2 =
            Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)

end Data

def TorsionTrivialisation : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
    letI := H.starRing
    ∀ (K₁ : Type) [Field K₁] [NumberField K₁] (P : Out.PolAV (Sp (𝓞 K₁)))
      (rig : LB.Gen (P.L.pull (eSec P.A))) (act : P.OAct (𝓞 E))
      (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
      (c : Y → (𝟙_ (Over (Sp (𝓞 K₁))) ⟶ P.A)) (k : ℕ),
      rig.IsGen → IsDiagPull P (act.act H.w0) →
      (∀ y y', c (y + y') = padd P.A (c y) (c y')) →
      (∀ (a : 𝓞 E) y, c (a • y) = c y ≫ act.act a) →
      1 ≤ k → (∀ y, c y ^ k = 1) →
      ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K₁ K')
        (D : Out.DegPre (𝓞 K')) (_ : Module (𝓞 E) D.X) (oa : D.OAct (𝓞 E)) (e : Y ≃ₗ[𝓞 E] D.X)
        (φ : D.P.A.left ⟶ P.A.left) (w : LB.Iso D.P.L (P.L.pull φ)),
        IsBaseChange (algebraMap (𝓞 K₁) (𝓞 K')) D.P D.rig P rig φ w ∧
        (∀ a, (oa.onB.act a).left ≫ φ = φ ≫ (act.act a).left) ∧
        (∀ y, (D.c (e y)).left ≫ φ = spMap (algebraMap (𝓞 K₁) (𝓞 K')) ≫ (c y).left) ∧
        TauSymm D ∧ D.TauBimult ∧ TauPowCan D k ∧
        TraceFormTwistIso D oa H.w0 ∧ D.PsiEven ∧
        (∀ y, PsiUnitOn D y Set.univ) ∧
        ∀ s : FractionRing (𝓞 K') →+* ℂ, PsiNormOne D s

example (k : ℕ) : ∑ i, canε k i = 0 := by
  simp [canε, Fin.sum_univ_succ]

example (S : Scheme.{0}) : IsDiagPull (Out.Inh.zeroPolAV S) (𝟙 _) :=
  ⟨⟨fun _ => 1⟩, by
    intro i j; erw [Out.Inh.linComb_triv_g, _root_.one_mul]; dsimp only; repeat erw [map_one], by
    intro j j' _ _ _; dsimp only [LB.pullGen, LB.oneGen]; repeat erw [map_one]⟩

end GlobalTheory.IndefiniteRowSideFullHecke.CanonicalTauPower
end
end

