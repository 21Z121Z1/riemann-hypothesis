import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001

-- bundled from Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.CubicalPullbackLaw
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.IndefiniteRowSideFullHecke.CubicalPullbackLaw

def IsRigPull {S S' : Scheme.{0}} {B' : Over S'} {B : Over S} [GrpObj B'] [IsCommMonObj B']
    [GrpObj B] [IsCommMonObj B] (p : S' ⟶ S) (F : B'.left ⟶ B.left) (L' : RigLB B') (L : RigLB B) : Prop :=
  ∃ he : eSec B' ≫ F = (show (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left from p) ≫ eSec B,
  ∃ w : LB.Iso L'.L (L.L.pull F), w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec B') (fun _ => 1)) L'.rig
      (rigPullOf F p he L.L L.rig)

def Identifies {S S' : Scheme.{0}} (p : S' ⟶ S) (E : SplitExt S) (E' : SplitExt S')
    (φ : E'.B ≅ (Over.pullback p).obj E.B) (ψ : E'.X ≃+ E.X) : Prop :=
  haveI := E.isAbelian.comm
  haveI := E'.isAbelian.comm
  IsMonHom φ.hom ∧
    ∀ χ : E'.X, IsRigPull p (φ.hom.left ≫ pullback.fst E.B.hom p) (E'.O χ) (E.O (ψ χ))

def IsBaseChange {S S' : Scheme.{0}} (p : S' ⟶ S) (E : SplitExt S) (E' : SplitExt S') : Prop :=
  ∃ (φ : E'.B ≅ (Over.pullback p).obj E.B) (ψ : E'.X ≃+ E.X), Identifies p E E' φ ψ

def GtBaseChangeLaw : Prop :=
  ∀ {S S' : Scheme.{0}} (p : S' ⟶ S) (E : SplitExt S) (G : Over S) [GrpObj G],
    E.IsGt G → ∃ E' : SplitExt S', IsBaseChange p E E' ∧ E'.IsGt ((Over.pullback p).obj G)

def CubicalPullLaw : Prop :=
  ∀ {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) (L : RigLB G) (c : CubicalStr G L),
    ∃ (hL : (L.L.pull m.F).IsLB) (hr : (m.rigPull L.L L.rig).IsGen)
      (c' : CubicalStr G' (m.rigLB L hL hr)),
      c'.t = m.thetaPull L.L c.t ∧ m.IsPullCubical c' c ∧
        (L.IsSymmetric → (m.rigLB L hL hr).IsSymmetric)

def Laws : Prop := GtBaseChangeLaw ∧ CubicalPullLaw

def GtPresentationBaseChangeLaw : Prop :=
  ∀ {S S' : Scheme.{0}} (p : S' ⟶ S) (E : SplitExt S) (G : Over S) [GrpObj G] (D : E.GtDatum G),
    ∃ (E' : SplitExt S') (φ : E'.B ≅ (Over.pullback p).obj E.B) (ψ : E'.X ≃+ E.X)
      (D' : E'.GtDatum ((Over.pullback p).obj G))
      (τ : (splitTorus S' E'.X).left ⟶ (splitTorus S E.X).left),
      Identifies p E E' φ ψ ∧
      D'.q ≫ φ.hom = (Over.pullback p).map D.q ∧
      τ ≫ (splitTorus S E.X).hom = (splitTorus S' E'.X).hom ≫ p ∧
      (∀ χ : E'.X, Units.map τ.appTop.hom.toMonoidHom (charUnit S E.X (ψ χ)) =
        charUnit S' E'.X χ) ∧
      D'.i.left ≫ pullback.fst G.hom p = τ ≫ D.i.left

theorem CubicalPullLaw.ofHom (h : CubicalPullLaw) : CubicalPullOfHomSt.{0} := by
  intro S G' G _ _ _ _ f _ L c
  obtain ⟨hL, hr, c', hc, _⟩ := h (CubeMap.ofHom f) L c
  exact ⟨hL, hr, c', hc⟩

end GlobalTheory.IndefiniteRowSideFullHecke.CubicalPullbackLaw

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.LevelStructureForms
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms

open ReciprocityTheory.ChartRestriction.G.Out

def stdForm {g : ℕ} (a b : Fin g ⊕ Fin g → ℤ) : ℤ :=
  ∑ i : Fin g, (a (Sum.inl i) * b (Sum.inr i) - a (Sum.inr i) * b (Sum.inl i))

def reduce {g : ℕ} (k : ℕ) (a : Fin g ⊕ Fin g → ℤ) : Fin g ⊕ Fin g → ZMod k :=
  fun j => (a j : ZMod k)

variable {S : Scheme.{0}}

def mulBy (A : Over S) [GrpObj A] (k : ℕ) : A ⟶ A := (𝟙 A) ^ k

abbrev constOver (S : Scheme.{0}) (I : Type) : Over S := ∐ fun _ : I => 𝟙_ (Over S)

structure Level (P : PolAV S) (k : ℕ) (ζ : Γ(S, ⊤)ˣ) where

  hom : Multiplicative (Fin P.g ⊕ Fin P.g → ZMod k) →* (𝟙_ (Over S) ⟶ P.A)

  isKer : IsPullback
    (Sigma.desc fun v : Fin P.g ⊕ Fin P.g → ZMod k => hom (Multiplicative.ofAdd v) :
      constOver S (Fin P.g ⊕ Fin P.g → ZMod k) ⟶ P.A)
    (toUnit _) (mulBy P.A k) η[P.A]

  pairing : ∀ a b : Fin P.g ⊕ Fin P.g → ℤ,
    WeilIs P.A P.L (k : ℤ) (T := 𝟙_ (Over S))
      (hom (Multiplicative.ofAdd (reduce k a))) (hom (Multiplicative.ofAdd (reduce k b)))
      (ζ ^ stdForm a b : Γ(S, ⊤)ˣ)

namespace Level

variable {P : PolAV S} {k : ℕ} {ζ : Γ(S, ⊤)ˣ}

def pt (ℓ : Level P k ζ) (v : Fin P.g ⊕ Fin P.g → ZMod k) : 𝟙_ (Over S) ⟶ P.A :=
  ℓ.hom (Multiplicative.ofAdd v)

def ptOver (ℓ : Level P k ζ) (T : Over S) (v : Fin P.g ⊕ Fin P.g → ZMod k) : T ⟶ P.A :=
  toUnit T ≫ ℓ.pt v

def ptKer (ℓ : Level P k ζ) (v : Fin P.g ⊕ Fin P.g → ZMod k) :
    𝟙_ (Over S) ⟶ pullback (mulBy P.A k) η[P.A] :=
  Sigma.ι (fun _ : Fin P.g ⊕ Fin P.g → ZMod k => 𝟙_ (Over S)) v ≫ ℓ.isKer.isoPullback.hom

example (ℓ : Level P k ζ) (v : Fin P.g ⊕ Fin P.g → ZMod k) :
    ℓ.ptKer v ≫ pullback.fst _ _ = ℓ.pt v := by
  simp [ptKer, pt]

end Level

example {g : ℕ} (i : Fin g) :
    stdForm (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr i) 1) = 1 := by
  simp [stdForm, Pi.single_apply]

example {g : ℕ} (a b : Fin g ⊕ Fin g → ℤ) : stdForm b a = -stdForm a b := by
  simp only [stdForm, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms
end
end

