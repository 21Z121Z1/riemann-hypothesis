import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Imports

-- bundled from Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.MultiplicationEtaleTorsion
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationEtaleTorsion

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

variable {S : Scheme.{0}}

def translDiffPow (A : Over S) [GrpObj A] (L : LB A.left) (N : ℕ) {T : Over S} (x : T ⟶ A) :
    LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 2) ![(translPt A x).left, (snd T A).left] ![(N : ℤ), -(N : ℤ)]

def MemK (A : Over S) [GrpObj A] (L : LB A.left) (N : ℕ) {T : Over S} (x : T ⟶ A) : Prop :=
  ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
    ∃ c : LB.Gen ((translDiffPow A L N x).pull ((fst T A).left ⁻¹ᵁ V).ι), c.IsGen

def mulPullDiff (A : Over S) [GrpObj A] (L : LB A.left) (n : ℕ) : LB A.left :=
  LB.LinComb L (K := Fin 2) ![(mulN A n).left, 𝟙 A.left] ![1, -((n : ℤ) ^ 2)]

def KPowEqTorsion : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (N : ℕ), 1 ≤ N →
    ∀ (T : Over S) (x : T ⟶ P.A), MemK P.A P.L N x ↔ x ^ N = 1

def MulPullIso : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ),
    ∃ c : LB.Gen (mulPullDiff P.A P.L n), c.IsGen

def MulFiniteFlatOnto : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n →
    IsFinite (mulN P.A n).left ∧ Flat (mulN P.A n).left ∧ Surjective (mulN P.A n).left

def MulEtale : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n →
    IsUnit (n : Γ(S, ⊤)) →
    (IsFinite (mulN P.A n).left ∧ Etale (mulN P.A n).left ∧ Surjective (mulN P.A n).left ∧
      ∀ a : P.A.left, (mulN P.A n).left.finrank a = n ^ (2 * P.g)) ∧
    (IsFinite (torsion P.A n).hom ∧ Etale (torsion P.A n).hom ∧
      ∀ s : S, (torsion P.A n).hom.finrank s = n ^ (2 * P.g))

def TorsionCard : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S), (n : K) ≠ 0 →
      Nat.card {y : Over.mk s ⟶ P.A // y ^ n = 1} = n ^ (2 * P.g)

def MulMorphism : Prop := MulFiniteFlatOnto ∧ MulEtale ∧ TorsionCard

def Laws : Prop := KPowEqTorsion ∧ MulPullIso ∧ MulMorphism

theorem comp_mulN (A : Over S) [GrpObj A] {T : Over S} (x : T ⟶ A) (n : ℕ) :
    x ≫ mulN A n = x ^ n := by
  induction n with
  | zero => simp [mulN, Hom.one_def]
  | succ n ih => rw [pow_succ, ← ih]; simp [mulN, Hom.mul_def, comp_lift_assoc]

example (A : Over S) [GrpObj A] (L : LB A.left) {T : Over S} (x : T ⟶ A) :
    translDiffPow A L 1 x = translDiff A L x := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationEtaleTorsion
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.RigidityTranslation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.RigidityTranslation

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

def rigidifiedBundle {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A)))
    (hrig : rig.IsGen) : RigLB P.A :=
  ⟨P.L, rig, P.isLB, hrig⟩

def Cube : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S)
    (rig : LB.Gen (P.L.pull (eSec P.A))) (hrig : rig.IsGen),
    Nonempty (CubicalStr P.A (rigidifiedBundle P rig hrig)) ∧
      Subsingleton (CubicalStr P.A (rigidifiedBundle P rig hrig))

def translate {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S} (x : T ⟶ A) : T ⊗ A ⟶ A :=
  lift (fst T A ≫ x) (snd T A) ≫ μ[A]

def squareBundle {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {T : Over S}
    (x y : T ⟶ A) : LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 4)
    ![(translate A (lift x y ≫ μ[A])).left, (snd T A).left, (translate A x).left,
      (translate A y).left]
    ![1, 1, -1, -1]

def Square : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (T : Over S) (x y : T ⟶ P.A),
    ∃ N : LB T.left, N.IsLB ∧
      ∃ u : LB.Iso (N.pull (fst T P.A).left) (squareBundle P.A P.L x y), u.IsGen

def Rigidity : Prop :=
  ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B],
    IsAbelianScheme A → IsAbelianScheme B →
      ∀ f : A ⟶ B, η[A] ≫ f = η[B] → IsMonHom f

def GlobalFunctions : Prop :=
  ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A],
    IsAbelianScheme A → Function.Bijective (A.hom.appTop).hom

def Laws : Prop := Cube ∧ Square ∧ Rigidity ∧ GlobalFunctions

example {S : Scheme.{0}} (A : Over S) [GrpObj A] (T : Over S) :
    translate A (toUnit T ≫ η[A]) = snd T A := by
  have h : fst T A ≫ toUnit T = toUnit (T ⊗ A) := toUnit_unique _ _
  unfold translate
  rw [← Category.assoc, h, MonObj.lift_comp_one_left]

example {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {T : Over S} (x : T ⟶ A) :
    translDiff A L x =
      LB.LinComb L (K := Fin 2) ![(translate A x).left, (snd T A).left] ![1, -1] := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.RigidityTranslation
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.WeilPairing
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilPairingLaws

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

def tors {S : Scheme.{0}} (P : PolAV S) (T : Over S) (k : ℕ) : Subgroup (T ⟶ P.A) where
  carrier := {x | x ^ k = 1}
  one_mem' := one_pow k
  mul_mem' := by
    intro x y hx hy
    haveI := P.isAb.comm
    have hc : Commute x y := mul_comm x y
    have hx' : x ^ k = 1 := hx
    have hy' : y ^ k = 1 := hy
    show (x * y) ^ k = 1
    rw [hc.mul_pow, hx', hy', _root_.mul_one]
  inv_mem' := by
    intro x hx
    have hx' : x ^ k = 1 := hx
    show x⁻¹ ^ k = 1
    rw [inv_pow, hx', inv_one]

def unitSpec {K : Type} [CommRing K] (u : Kˣ) : Γ(Spec (CommRingCat.of K), ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom u

def WeilExistsUnique : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ) (T : Over S)
    (x y : T ⟶ P.A), x ∈ tors P T k → y ∈ tors P T k →
    ∃! c : Γ(T.left, ⊤)ˣ, WeilIs P.A P.L (k : ℤ) x y c

def WeilMulLeft : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ) (T : Over S)
    (x x' y : T ⟶ P.A), x ∈ tors P T k → x' ∈ tors P T k → y ∈ tors P T k →
    ∀ c c' : Γ(T.left, ⊤)ˣ, WeilIs P.A P.L (k : ℤ) x y c → WeilIs P.A P.L (k : ℤ) x' y c' →
      WeilIs P.A P.L (k : ℤ) (x * x') y (c * c')

def WeilAlternating : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ) (T : Over S)
    (x : T ⟶ P.A), x ∈ tors P T k → WeilIs P.A P.L (k : ℤ) x x 1

def WeilLevelChange : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k l : ℕ) (T : Over S),
    IsUnit ((k * l : ℕ) : Γ(T.left, ⊤)) →
    ∀ (x y : T ⟶ P.A), x ∈ tors P T (k * l) → y ∈ tors P T k →
    ∀ c : Γ(T.left, ⊤)ˣ,
      WeilIs P.A P.L ((k * l : ℕ) : ℤ) x y c ↔ WeilIs P.A P.L (k : ℤ) (x ^ l) y c

def WeilLaws : Prop :=
  WeilExistsUnique ∧ WeilMulLeft ∧ WeilAlternating ∧ WeilLevelChange

def WeilNondegenerate : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (k : ℕ),
    (k : K) ≠ 0 →
    ∀ x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A, x ∈ tors P _ k →
      (∀ y : baseOver (Spec (CommRingCat.of K)) ⟶ P.A, y ∈ tors P _ k →
        WeilIs P.A P.L (k : ℤ) x y 1) →
      x = 1

def WeilCharacters : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (N : ℕ),
    (N : K) ≠ 0 →
    ∀ χ : tors P (baseOver (Spec (CommRingCat.of K))) N →* Kˣ,
      ∃! b : tors P (baseOver (Spec (CommRingCat.of K))) N,
        ∀ x : tors P (baseOver (Spec (CommRingCat.of K))) N,
          WeilIs P.A P.L (N : ℤ) x.1 b.1 (unitSpec (χ x))

def WeilAll : Prop := WeilLaws ∧ WeilNondegenerate ∧ WeilCharacters

example {S : Scheme.{0}} (P : PolAV S) (T : Over S) (x : T ⟶ P.A) : x ∈ tors P T 0 := pow_zero x

example {S : Scheme.{0}} (P : PolAV S) (T : Over S) (x y : T ⟶ P.A) :
    x * y = lift x y ≫ μ[P.A] ∧ (1 : T ⟶ P.A) = toUnit T ≫ η[P.A] := ⟨rfl, rfl⟩

example {K : Type} [CommRing K] : Function.Injective (unitSpec (K := K)) :=
  Units.map_injective (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.injective

end GlobalTheory.IndefiniteRowSideFullHecke.WeilPairingLaws
end
end

