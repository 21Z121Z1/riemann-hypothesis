import Mathlib
import Formalism.FormalDegreeBessel.StatementDS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.DegreeProportionalWords
section
open Finset
open scoped ENNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DegreeProportionalWords

open Formalism.QuantumDeterminants

def gam (n : ℕ) (H H' : ℝ) : ℝ := 2 * (n : ℝ) ^ ((3 : ℝ) / 2) * H * H'

def TermCount : Prop :=
  ∀ (n l : ℕ) (H H' : ℝ) (τ : Finset (Fin n) → ℂ) (ρ : Finset (Fin n) → ℝ),
    0 ≤ H → 0 ≤ H' →
    (∀ I : Finset (Fin n), I.card = l → ‖τ I‖ ≤ (H * H') ^ l) →
    (∀ I : Finset (Fin n), I.card = l → 0 < ρ I ∧ ρ I ≤ (Real.exp 1 * n) ^ l) →
    ∑ I ∈ powersetCard l (univ : Finset (Fin n)), ‖τ I * ((Real.sqrt (ρ I) : ℝ) : ℂ)‖ ≤ gam n H H' ^ l

def TermCountNorm : Prop :=
  ∀ (V : Type) [SeminormedAddCommGroup V] [NormedSpace ℂ V]
    (n l : ℕ) (H H' : ℝ) (τ : Finset (Fin n) → ℂ) (ρ : Finset (Fin n) → ℝ) (v : V) (w : Finset (Fin n) → V),
    0 ≤ H → 0 ≤ H' →
    (∀ I : Finset (Fin n), I.card = l → ‖τ I‖ ≤ (H * H') ^ l) →
    (∀ I : Finset (Fin n), I.card = l → 0 < ρ I ∧ ρ I ≤ (Real.exp 1 * n) ^ l) →
    (∀ I : Finset (Fin n), I.card = l → ‖w I‖ ≤ Real.sqrt (ρ I) * ‖v‖) →
    ‖∑ I ∈ powersetCard l (univ : Finset (Fin n)), τ I • w I‖ ≤ gam n H H' ^ l * ‖v‖

def IsGauge {A : Type} [AddCommGroup A] (N : A → ℝ) : Prop :=
  N 0 = 0 ∧ ∀ x y, N (x + y) ≤ N x + N y

def l1 {A : Type} (a : A →₀ ℂ) : ℝ := ∑ ν ∈ a.support, ‖a ν‖

def comb {A V : Type} [AddCommGroup A] [AddCommGroup V] [Module ℂ V] (j : A → V) (μ : A) (a : A →₀ ℂ) : V :=
  ∑ ν ∈ a.support, a ν • j (μ + ν)

def Expands {A V : Type} [AddCommGroup A] [AddCommGroup V] [Module ℂ V] (N M : A → ℝ) (j : A → V) (μ : A)
    (x : V) (s t B : ℝ) : Prop :=
  ∃ a : A →₀ ℂ, x = comb j μ a ∧ (∀ ν ∈ a.support, N ν ≤ s ∧ M ν ≤ t) ∧ l1 a ≤ B

def OneStep {A V ι : Type} [AddCommGroup A] [AddCommGroup V] [Module ℂ V] (N M : A → ℝ) (j : A → V)
    (D : ι → Module.End ℂ V) (w : ι → ℕ) (lam : A) (R Γ : ℝ) : Prop :=
  ∀ (i : ι) (μ : A), N (μ - lam) ≤ R → Expands N M j μ (D i (j μ)) (w i) 1 (Γ ^ w i)

def wordOp {V ι : Type} [AddCommGroup V] [Module ℂ V] (D : ι → Module.End ℂ V) (L : List ι) : Module.End ℂ V :=
  (L.map D).prod

def wordWt {ι : Type} (w : ι → ℕ) (L : List ι) : ℕ := (L.map w).sum

def Iteration : Prop :=
  ∀ (A V ι : Type) [AddCommGroup A] [AddCommGroup V] [Module ℂ V] (N M : A → ℝ) (j : A → V)
    (D : ι → Module.End ℂ V) (w : ι → ℕ) (lam : A) (R Γ : ℝ),
    IsGauge N → IsGauge M → 0 ≤ Γ → OneStep N M j D w lam R Γ →
    ∀ (L : List ι) (μ : A), N (μ - lam) + (wordWt w L : ℝ) ≤ R →
      Expands N M j μ (wordOp D L (j μ)) (wordWt w L) L.length (Γ ^ wordWt w L)

def IterationSum : Prop :=
  ∀ (A V ι : Type) [AddCommGroup A] [AddCommGroup V] [Module ℂ V] (N M : A → ℝ) (j : A → V)
    (D : ι → Module.End ℂ V) (w : ι → ℕ) (lam : A) (R Γ : ℝ),
    IsGauge N → IsGauge M → 0 ≤ Γ → OneStep N M j D w lam R Γ →
    ∀ (L : List ι) (μ : A) (c : A →₀ ℂ), (∀ ν ∈ c.support, N (μ + ν - lam) + (wordWt w L : ℝ) ≤ R) →
      ∃ c' : A →₀ ℂ, wordOp D L (comb j μ c) = comb j μ c' ∧
        (∀ ν' ∈ c'.support, ∃ ν ∈ c.support, N (ν' - ν) ≤ (wordWt w L : ℝ) ∧ M (ν' - ν) ≤ (L.length : ℝ)) ∧
        l1 c' ≤ Γ ^ wordWt w L * l1 c

def IterationGauge : Prop :=
  ∀ (A V ι : Type) [AddCommGroup A] [AddCommGroup V] [Module ℂ V] (N M : A → ℝ) (j : A → V)
    (D : ι → Module.End ℂ V) (w : ι → ℕ) (lam : A) (R Γ : ℝ) (p : V → ℝ≥0∞) (K : ℝ≥0∞),
    IsGauge N → IsGauge M → 0 ≤ Γ → OneStep N M j D w lam R Γ →
    (∀ x y, p (x + y) ≤ p x + p y) → (∀ (c : ℂ) (x : V), p (c • x) = ‖c‖ₑ * p x) →
    (∀ κ : A, N (κ - lam) ≤ R → p (j κ) ≤ K) →
    ∀ (L : List ι) (μ : A), N (μ - lam) + (wordWt w L : ℝ) ≤ R →
      p (wordOp D L (j μ)) ≤ ENNReal.ofReal (Γ ^ wordWt w L) * K

def RegInt {n : ℕ} (μ : Fin n → ℝ) : Prop :=
  Function.Injective μ ∧ ∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ)

def GapTwo {n : ℕ} (μ : Fin n → ℝ) : Prop := ∀ a b, a ≠ b → 2 ≤ |μ a - μ b|

def eSet {n : ℕ} (I : Finset (Fin n)) : Fin n → ℝ := fun a => if a ∈ I then 1 else 0

def StepSize : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ) (s : Fin n), RegInt μ →
    (Function.Injective (μ + Pi.single s 1) →
      1 / (n : ℝ) ≤ fdegHC (μ + Pi.single s 1) / fdegHC μ ∧ fdegHC (μ + Pi.single s 1) / fdegHC μ ≤ n) ∧
    (Function.Injective (μ - Pi.single s 1) →
      1 / (n : ℝ) ≤ fdegHC (μ - Pi.single s 1) / fdegHC μ ∧ fdegHC (μ - Pi.single s 1) / fdegHC μ ≤ n)

def GapStepSize : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ) (s : Fin n), GapTwo μ →
    (GapTwo (μ + Pi.single s 1) →
      1 / (4 * (n : ℝ) ^ 2) ≤ fdegHC (μ + Pi.single s 1) / fdegHC μ ∧
        fdegHC (μ + Pi.single s 1) / fdegHC μ ≤ Real.exp 1 * n) ∧
    (GapTwo (μ - Pi.single s 1) →
      1 / (4 * (n : ℝ) ^ 2) ≤ fdegHC (μ - Pi.single s 1) / fdegHC μ ∧
        fdegHC (μ - Pi.single s 1) / fdegHC μ ≤ Real.exp 1 * n)

def GapSubsetSize : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ) (I : Finset (Fin n)),
    ((∀ J ⊆ I, GapTwo (μ + eSet J)) →
      (1 / (4 * (n : ℝ) ^ 2)) ^ I.card ≤ fdegHC (μ + eSet I) / fdegHC μ ∧
        fdegHC (μ + eSet I) / fdegHC μ ≤ (Real.exp 1 * n) ^ I.card) ∧
    ((∀ J ⊆ I, GapTwo (μ - eSet J)) →
      (1 / (4 * (n : ℝ) ^ 2)) ^ I.card ≤ fdegHC (μ - eSet I) / fdegHC μ ∧
        fdegHC (μ - eSet I) / fdegHC μ ≤ (Real.exp 1 * n) ^ I.card)

def StepIn {n : ℕ} (Q : Set (Fin n → ℝ)) (μ ν : Fin n → ℝ) : Prop :=
  μ ∈ Q ∧ ν ∈ Q ∧ ∃ s : Fin n, ν = μ + Pi.single s 1 ∨ ν = μ - Pi.single s 1

def DegreeProportional : Prop :=
  ∀ (n : ℕ) (P Q : Set (Fin n → ℝ)) (d : (Fin n → ℝ) → ℝ),
    (∀ μ ∈ Q, RegInt μ) → (∀ μ ∈ Q, 0 < d μ) →
    (∀ μ ∈ Q, ∀ s : Fin n, μ + Pi.single s 1 ∈ Q →
      d (μ + Pi.single s 1) / d μ = ∏ t ∈ univ.erase s, (μ s + 1 - μ t) / (μ s - μ t)) →
    P ⊆ Q → (∀ μ ∈ P, ∀ ν ∈ P, Relation.ReflTransGen (StepIn Q) μ ν) →
    ∃ c : ℝ, 0 < c ∧ ∀ μ ∈ P, d μ = c * fdegHC μ

def Statement : Prop :=
  TermCount ∧ TermCountNorm ∧ Iteration ∧ IterationSum ∧ IterationGauge ∧
    StepSize ∧ GapStepSize ∧ GapSubsetSize ∧ DegreeProportional

example {n : ℕ} (s : Fin n) : eSet {s} = Pi.single s 1 := by
  funext a
  by_cases h : a = s <;> simp [eSet, h]

example : OneStep (A := ℤ) (V := ℂˣ → ℂ) (ι := Unit) (fun k => |(k : ℝ)|) (fun k => |(k : ℝ)|)
    (fun k x => ((x ^ k : ℂˣ) : ℂ)) (fun _ => LinearMap.mulLeft ℂ (fun x : ℂˣ => (x : ℂ))) (fun _ => 1) 0 5 1 := by
  intro i μ _
  refine ⟨Finsupp.single 1 1, ?_, ?_, ?_⟩
  · funext x
    simp [comb, Finsupp.support_single_ne_zero, zpow_add₀, mul_comm]
  · intro ν hν
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, mem_singleton] at hν
    simp [hν]
  · simp [l1, Finsupp.support_single_ne_zero]

end GlobalTheory.IndefiniteRowSideFullHecke.DegreeProportionalWords
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.TwistedPoints
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistedPoints

attribute [local instance] Over.cartesianMonoidalCategory

def constFun {A : Type} [CommRing A] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of A)) (U : Y.Opens) (a : A) :
    Γ(Y, U) :=
  rs (le_top : U ≤ ⊤) (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))

def IsSecBasis {A : Type} [CommRing A] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of A)) (N : LB Y)
    {n : ℕ} (s : Fin n → LB.Sec N) : Prop :=
  ∀ t : LB.Sec N, ∃! a : Fin n → A, ∀ j : N.ι, t.f j = ∑ i, constFun p (N.U j) (a i) * (s i).f j

abbrev powLB {X : Scheme.{0}} (L : LB X) (n : ℕ) : LB X :=
  LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (n : ℤ))

def nonvanishing {X : Scheme.{0}} {N : LB X} (s : LB.Sec N) : X.Opens :=
  ⨆ j, X.basicOpen (s.f j)

def IsAmple {X : Scheme.{0}} (L : LB X) : Prop :=
  CompactSpace X ∧
    ∀ x : X, ∃ (n : ℕ) (s : LB.Sec (powLB L n)), 1 ≤ n ∧ x ∈ nonvanishing s ∧ IsAffineOpen (nonvanishing s)

section Group

variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]

def IsAbelianOfDim (g : ℕ) : Prop :=
  SmoothOfRelativeDimension g B.hom ∧ IsProper B.hom ∧ GeometricallyConnected B.hom

def IsSymmetric (L : LB B.left) : Prop :=
  ∃ t : LB.Iso (L.pull (GrpObj.inv (X := B)).left) L, t.IsGen

def HasTrivialKernel (L : LB B.left) : Prop :=
  ∀ (T : Over S) (x : T ⟶ B),
    (∃ t : LB.Gen (cubeLB B (T := T ⊗ B) ![fst T B ≫ x, snd T B] L), t.IsGen) → x = pzero B T

abbrev TwIdx : Type := PUnit.{1} ⊕ ULift.{0} (Finset (Fin 2))

def twPts (c : 𝟙_ (Over S) ⟶ B) : Fin 2 → (B ⟶ B) := ![toUnit B ≫ c, 𝟙 B]

def twMap (c : 𝟙_ (Over S) ⟶ B) : TwIdx → (B.left ⟶ B.left) :=
  Sum.elim (fun _ => 𝟙 B.left) (fun I => (psum B (twPts B c) I.down).left)

def twExp (k : ℕ) : TwIdx → ℤ :=
  Sum.elim (fun _ => (k : ℤ)) (fun I => (-1) ^ (2 - I.down.card))

abbrev twLB (M : LB B.left) (c : 𝟙_ (Over S) ⟶ B) (k : ℕ) : LB B.left :=
  LB.LinComb M (twMap B c) (twExp k)

end Group

def HasStableBasis {R : Type} [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B]
    (M : LB B.left) (c : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) (k n : ℕ) : Prop :=
  ∃ s : Fin n → LB.Sec (twLB B M c k),
    IsSecBasis B.hom (twLB B M c k) s ∧
    ∀ (R' : Type) [CommRing R'] (f : R →+* R') (B' : Scheme.{0}) (h : B' ⟶ B.left)
      (p : B' ⟶ Spec (CommRingCat.of R')),
      IsPullback h p B.hom (Spec.map (CommRingCat.ofHom f)) →
      IsSecBasis p (LB.LinComb M (fun i => h ≫ twMap B c i) (twExp k))
        (fun i => pullSec M (twMap B c) (twExp k) (s i) h)

def TwistedSectionsBaseChange : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (g : ℕ) (M : RigLB B),
    IsAbelianOfDim B g → IsSymmetric B M.L → IsAmple M.L → HasTrivialKernel B M.L →
    ∀ (c : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) (k : ℕ), 1 ≤ k → HasStableBasis B M.L c k (k ^ g)

example {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (M : LB B.left) (c : 𝟙_ (Over S) ⟶ B) (k : ℕ) :
    LB.LinComb M (fun I => twMap B c (Sum.inr I)) (fun I => twExp k (Sum.inr I)) = cubeLB B (twPts B c) M := rfl

example {R : Type} [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B]
    (M : LB B.left) (c : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ B) (k n : ℕ) (H : HasStableBasis B M c k n)
    (R' : Type) [CommRing R'] (f : R →+* R') (B' : Scheme.{0}) (h : B' ⟶ B.left)
    (p : B' ⟶ Spec (CommRingCat.of R')) (sq : IsPullback h p B.hom (Spec.map (CommRingCat.ofHom f)))
    (t : LB.Sec (LB.LinComb M (fun i => h ≫ twMap B c i) (twExp k))) :
    ∃ (s : Fin n → LB.Sec (twLB B M c k)) (a : Fin n → R'), ∀ j,
      t.f j = ∑ i, constFun p _ (a i) * (pullSec M (twMap B c) (twExp k) (s i) h).f j := by
  obtain ⟨s, -, hs⟩ := H
  obtain ⟨a, ha, -⟩ := hs R' f B' h p sq t
  exact ⟨s, a, ha⟩

end GlobalTheory.IndefiniteRowSideFullHecke.TwistedPoints
end
end

