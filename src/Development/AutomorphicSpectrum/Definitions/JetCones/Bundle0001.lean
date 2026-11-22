import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraCentre.ConstantCoeffRhoOneCanonMonomial
import Formalism.PeriodIntegrals.Bundle0015
import Formalism.PeriodIntegrals.Bundle0022
import Formalism.RealPlaceAnalysis.Bundle0001
import Formalism.RealPlaceAnalysis.Bundle0002
import Formalism.RealPlaceAnalysis.Bundle0003

-- bundled from Development.AutomorphicSpectrum.Definitions.JetCones.KTypePosCone
section
open GroundTheory.Automorphic.HarishChandra Finset

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.CompanionTheory.DS

abbrev Pr (n : ℕ) := Fin n × Fin n

abbrev Coch (n : ℕ) (X : Type) := Finset (Pr n) → X

variable {n : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]

def sgn (S : Finset (Pr n)) (α : Pr n) : ℂ := (-1) ^ (S.filter fun β => toLex β < toLex α).card

def wedge (α : Pr n) : Module.End ℂ (Coch n X) :=
  LinearMap.pi fun S => if α ∈ S then sgn S α • LinearMap.proj (S.erase α) else 0

def contr (α : Pr n) : Module.End ℂ (Coch n X) :=
  LinearMap.pi fun S => if α ∈ S then 0 else sgn S α • LinearMap.proj (insert α S)

def ptw (T : Module.End ℂ X) : Module.End ℂ (Coch n X) := T.compLeft (Finset (Pr n))

def dC (Φ : Finset (Pr n)) (x : Pr n → Module.End ℂ X) : Module.End ℂ (Coch n X) :=
  ∑ α ∈ Φ, wedge α * ptw (x α) -
    ∑ α ∈ Φ, ∑ β ∈ Φ.filter (fun β => α.2 = β.1), wedge α * wedge β * contr (α.1, β.2)

def Supp (c Φ : Finset (Pr n)) (f : Coch n X) : Prop := ∀ S, f S ≠ 0 → c ⊆ S ∧ S ⊆ Φ

def Deg (j : ℕ) (f : Coch n X) : Prop := ∀ S, f S ≠ 0 → S.card = j

def Exact (Φ : Finset (Pr n)) (x : Pr n → Module.End ℂ X) (j : ℕ) (f : Coch n X) : Prop :=
  ∃ η : Coch n X, (∀ S, η S ≠ 0 → S ⊆ Φ ∧ S.card + 1 = j) ∧ dC Φ x η = f

def Acyc (Φ : Finset (Pr n)) (x : Pr n → Module.End ℂ X) : Prop :=
  ∀ j < Φ.card, ∀ f : Coch n X, Supp ∅ Φ f → Deg j f → dC Φ x f = 0 → Exact Φ x j f

def UpClosed (Φ : Finset (Pr n)) : Prop :=
  (∀ α ∈ Φ, α.1 < α.2) ∧ ∀ α ∈ Φ, ∀ β ∈ Φ, α.2 = β.1 → (α.1, β.2) ∈ Φ

def TopPart (c Φ : Finset (Pr n)) : Prop :=
  c ⊆ Φ ∧ ∀ α ∈ Φ, ∀ β ∈ Φ, α.2 = β.1 → (α.1, β.2) ∈ c → α ∈ c ∨ β ∈ c

def NRel (Φ : Finset (Pr n)) (x : Pr n → Module.End ℂ X) : Prop :=
  ∀ α ∈ Φ, ∀ β ∈ Φ, x α * x β - x β * x α =
    (if α.2 = β.1 then x (α.1, β.2) else 0) - (if β.2 = α.1 then x (β.1, α.2) else 0)

def wtS (S : Finset (Pr n)) : Fin n → ℝ :=
  fun k => ∑ α ∈ S, ((if k = α.1 then 1 else 0) - (if k = α.2 then 1 else 0))

def tEv (w : Fin n → ℝ) : FreeAlgebra ℂ (Fin n) →ₐ[ℂ] U n :=
  FreeAlgebra.lift ℂ fun a => e (a, a) + algebraMap ℂ (U n) (w a : ℂ)

def evT (μ : Fin n → ℝ) : FreeAlgebra ℂ (Fin n) →ₐ[ℂ] ℂ := FreeAlgebra.lift ℂ fun a => (μ a : ℂ)

def rIdeal (Φ : Finset (Pr n)) : Submodule ℂ (U n) :=
  Submodule.span ℂ {y | ∃ α ∈ Φ, ∃ u : U n, y = e α * u}

def eOp (φ : U n →ₐ[ℂ] Module.End ℂ X) : Pr n → Module.End ℂ X := fun α => φ (e α)

def IsWt (φ : U n →ₐ[ℂ] Module.End ℂ X) (μ : Fin n → ℝ) (v : X) : Prop :=
  ∀ a, φ (e (a, a)) v = (μ a : ℂ) • v

def IsWtC (φ : U n →ₐ[ℂ] Module.End ℂ X) (ν : Fin n → ℝ) (f : Coch n X) : Prop :=
  ∀ S, IsWt φ (ν + wtS S) (f S)

def twist {m : ℕ} (φ : U n →ₐ[ℂ] Module.End ℂ X) (A : Pr n → Matrix (Fin m) (Fin m) ℂ) :
    Pr n → Module.End ℂ (Fin m → X) := fun α =>
  LinearMap.pi fun i => φ (e α) ∘ₗ LinearMap.proj i - ∑ k, A α i k • LinearMap.proj k

def trC {m : ℕ} (φ : U n →ₐ[ℂ] Module.End ℂ X) (ψ : Finset (Pr n) → Fin m → U n) (f : Coch n (Fin m → X)) :
    Coch n X := fun S => ∑ i, φ (ψ S i) (f S i)

def posAll (n : ℕ) : Finset (Pr n) := univ.filter fun α => α.1 < α.2

def posC (ε : Fin n → Bool) : Finset (Pr n) := univ.filter fun α => α.1 < α.2 ∧ ε α.1 = ε α.2

def posN (ε : Fin n → Bool) : Finset (Pr n) := univ.filter fun α => α.1 < α.2 ∧ ε α.1 ≠ ε α.2

def casK (ε : Fin n → Bool) : U n :=
  ∑ α ∈ univ.filter (fun α : Pr n => ε α.1 = ε α.2), e α * e (α.2, α.1)

def casG (n : ℕ) : U n := ∑ α : Pr n, e α * e (α.2, α.1)

def CommK (ε : Fin n → Bool) (u : U n) : Prop := ∀ a b, ε a = ε b → e (a, b) * u = u * e (a, b)

def KStab (ε : Fin n → Bool) (φ : U n →ₐ[ℂ] Module.End ℂ X) (S : Submodule ℂ X) : Prop :=
  ∀ a b, ε a = ε b → ∀ v ∈ S, φ (e (a, b)) v ∈ S

def IsHW (ε : Fin n → Bool) (φ : U n →ₐ[ℂ] Module.End ℂ X) (μ : Fin n → ℝ) (v : X) : Prop :=
  IsWt φ μ v ∧ ∀ α ∈ posC ε, φ (e α) v = 0

def InPosCone (δ : Fin n → ℝ) : Prop :=
  ∃ c : Pr n → ℕ, δ = ∑ α ∈ posAll n, (c α : ℝ) • wtS {α}

section Unitary

open scoped InnerProductSpace

variable {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

def IsStar (ε : Fin n → Bool) (φ : U n →ₐ[ℂ] Module.End ℂ Y) : Prop :=
  ∀ a b, ∀ v w : Y, ⟪φ (e (a, b)) v, w⟫_ℂ = (if ε a = ε b then 1 else -1) * ⟪v, φ (e (b, a)) w⟫_ℂ

def IsUGK (ε : Fin n → Bool) (φ : U n →ₐ[ℂ] Module.End ℂ Y) : Prop :=
  IsStar ε φ ∧ ∀ v : Y, ∃ S : Submodule ℂ Y, FiniteDimensional ℂ S ∧ v ∈ S ∧ KStab ε φ S

def IsLowest (ε : Fin n → Bool) (φ : U n →ₐ[ℂ] Module.End ℂ Y) (Λ : Fin n → ℝ) : Prop :=
  ∀ (μ : Fin n → ℝ) (w : Y), w ≠ 0 → IsHW ε φ μ w → PI.UpqRep.vNormSq ε Λ ≤ PI.UpqRep.vNormSq ε μ

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def smV (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Set H :=
  PI.PhMeasCore.smoothVecs (PI.UpqRep.Jm ε) σ

def IsDerived (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H)
    (φ : U n →ₐ[ℂ] Module.End ℂ V) : Prop :=
  (∀ v ∈ V, v ∈ smV ε σ) ∧ ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (v : V),
    (φ (UniversalEnvelopingAlgebra.ι ℂ Z) v : H) = PI.DSInfCharCap.dsigC ε σ Z v

def IsGKOf (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H)
    (φ : U n →ₐ[ℂ] Module.End ℂ V) : Prop :=
  IsDerived ε σ V φ ∧ ∀ v : H, v ∈ V ↔ v ∈ smV ε σ ∧ PI.UpqRep.IsKFin ε σ v

end Unitary

def DSUnique : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    PI.UpqRep.IsHCParam lam → PI.UpqRep.IsDS ε lam σ → PI.UpqRep.IsDS ε lam σ' → PI.UpqRep.IsEquiv ε σ' σ

def KTypePosCone : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), PI.UpqRep.IsHCParam lam → PI.UpqRep.IsDS ε lam σ →
    ∀ (ν : Fin n → ℝ) (S : Submodule ℂ H), PI.UpqRep.IsKTypeOf ε σ ν S → InPosCone (ν - PI.UpqRep.lowK ε lam)

end GlobalTheory.CompanionTheory.DS
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.JetCones.SymCapRev
section
open scoped InnerProductSpace
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.AlgRepEndIrreducible

def symCap {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (x : Fin n → ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
    (((Equiv.Perm.sign σ * Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) •
      (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (x k) (σ k) (τ k)).prod

def symCapRev {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (x : Fin n → ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
    (((Equiv.Perm.sign σ * Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) •
      (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (x k) (σ k) (τ k)).reverse.prod

def TensRule {A : Type*} [Ring A] {n : ℕ} (θ β : Fin n → Fin n → A) : Prop :=
  ∀ a b c d : Fin n, θ a b * β c d - β c d * θ a b =
    (if b = c then β a d else 0) - (if d = a then β c b else 0)

def KRel {A : Type*} [Ring A] {n : ℕ} (ε : Fin n → Bool) (D : Fin n → Fin n → A) : Prop :=
  ∀ a b c d : Fin n, ε a = ε b → ε c = ε d → D a b * D c d - D c d * D a b =
    (if b = c then D a d else 0) - (if d = a then D c b else 0)

def KAdj {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (D : Fin n → Fin n → Module.End ℂ V) : Prop :=
  ∀ a b : Fin n, ε a = ε b → ∀ x y : V, ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ

def CAR {A : Type*} [Ring A] {n : ℕ} (ε : Fin n → Bool) (p m : Fin n → Fin n → A) : Prop :=
  (∀ a b, ε a = ε b → p a b = 0 ∧ m a b = 0) ∧
  (∀ a b c d, m a b * p c d + p c d * m a b = if a = c ∧ b = d ∧ ε a ≠ ε b then 1 else 0) ∧
  (∀ a b c d, p a b * p c d + p c d * p a b = 0) ∧
  (∀ a b c d, m a b * m c d + m c d * m a b = 0)

def kap {A : Type*} [Ring A] {n : ℕ} (p m : Fin n → Fin n → A) (a b : Fin n) : A :=
  ∑ d, p a d * m b d - ∑ c, p c b * m c a

def num {A : Type*} [Ring A] {n : ℕ} (p m : Fin n → Fin n → A) : A :=
  ∑ a, ∑ b, p a b * m a b

def ncCard {n : ℕ} (ε : Fin n → Bool) : ℕ :=
  (univ.filter fun x : Fin n × Fin n => x.1 < x.2 ∧ ε x.1 ≠ ε x.2).card

def Base {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} (ε : Fin n → Bool)
    (E p m : Fin n → Fin n → Module.End ℂ W) : Prop :=
  Formalism.REAL.GlRel E ∧ (∀ a b x y, ⟪E a b x, y⟫_ℂ = ⟪x, E b a y⟫_ℂ) ∧ CAR ε p m ∧
  (∀ a b x y, ⟪p a b x, y⟫_ℂ = ⟪x, m a b y⟫_ℂ) ∧
  ∀ a b c d, Commute (E a b) (p c d) ∧ Commute (E a b) (m c d)

def Vac {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (E p m : Fin n → Fin n → Module.End ℂ W) (ν : Fin n → ℝ) (w : W) : Prop :=
  w ≠ 0 ∧ Formalism.REAL.IsWeight E ν w ∧ ∀ a b, a < b → E a b w = 0 ∧ p a b w = 0 ∧ m b a w = 0

def WtBd {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ W) (ν : Fin n → ℝ) : Prop :=
  ∀ (φ : Fin n → ℝ) (v : W), v ≠ 0 → Formalism.REAL.IsWeight E φ v →
    ∀ (w : Equiv.Perm (Fin n)) (x : Fin n → ℝ), Antitone x →
      PI.UpqRep.dot x (φ ∘ w) ≤ PI.UpqRep.dot x ν

def WigMod {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} (ε : Fin n → Bool)
    (E p m : Fin n → Fin n → Module.End ℂ W) (ν : Fin n → ℝ) : Prop :=
  Base ε E p m ∧ (∃ w, Vac E p m ν w) ∧ WtBd E ν ∧
  ∀ (u : ℂ) (v : W), Formalism.REAL.qdet E u v = (∏ k : Fin n, (u - ((k : ℕ) : ℂ) + (ν k : ℂ))) • v

def KMap {W X : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] {n : ℕ}
    (ε : Fin n → Bool) (D : Fin n → Fin n → Module.End ℂ W) (E : Fin n → Fin n → Module.End ℂ X)
    (ω : W →ₗ[ℂ] X) : Prop :=
  ∀ a b, ε a = ε b → ∀ w, ω (D a b w) = E a b (ω w)

def IsDer {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (j : X →ₗᵢ[ℂ] H) (E : Fin n → Fin n → Module.End ℂ X) : Prop :=
  Set.range j = PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ ∧
  ∀ a b x, j (E a b x) = PI.DSInfCharCap.dsigC ε σ (PI.DSInfCharCap.unitM (a, b)) (j x)

end GlobalTheory.CompanionTheory.AlgRepEndIrreducible

end
end

