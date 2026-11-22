import Formalism.RealPlaceAnalysis.Bundle0001

-- bundled from Formalism.RealPlaceAnalysis.FockPairGl
section
open MvPolynomial

noncomputable section

namespace Formalism.REAL

def fockF {σ : Type*} (f g : MvPolynomial σ ℂ) : ℂ :=
  ∑ m ∈ f.support, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ)

def sgnv {M n' : ℕ} (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i : Fin M) (a : Fin n') : Bool :=
  ε i == ε' a

def bop {M n' : ℕ} (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i : Fin M) (a : Fin n') :
    Module.End ℂ (MvPolynomial (Fin M × Fin n') ℂ) :=
  if sgnv ε ε' i a then (pderiv (i, a)).toLinearMap
  else LinearMap.mulLeft ℂ (X (i, a))

def bpl {M n' : ℕ} (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i : Fin M) (a : Fin n') :
    Module.End ℂ (MvPolynomial (Fin M × Fin n') ℂ) :=
  if sgnv ε ε' i a then LinearMap.mulLeft ℂ (X (i, a))
  else -(pderiv (i, a)).toLinearMap

def Eg {M n' : ℕ} (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i j : Fin M) :
    Module.End ℂ (MvPolynomial (Fin M × Fin n') ℂ) :=
  ∑ a, bpl ε ε' i a * bop ε ε' j a

def Eg' {M n' : ℕ} (ε : Fin M → Bool) (ε' : Fin n' → Bool) (a b : Fin n') :
    Module.End ℂ (MvPolynomial (Fin M × Fin n') ℂ) :=
  -∑ i, bpl ε ε' i b * bop ε ε' i a

def NN {M n' : ℕ} (ε : Fin M → Bool) (ε' : Fin n' → Bool) :
    Module.End ℂ (MvPolynomial (Fin M × Fin n') ℂ) :=
  ∑ i, Eg ε ε' i i

def CCR : Prop :=
  ∀ (M n' : ℕ) (ε : Fin M → Bool) (ε' : Fin n' → Bool) (i j : Fin M) (a b : Fin n'),
    bop ε ε' i a * bpl ε ε' j b - bpl ε ε' j b * bop ε ε' i a = (if i = j ∧ a = b then 1 else 0) ∧
    bop ε ε' i a * bop ε ε' j b = bop ε ε' j b * bop ε ε' i a ∧
    bpl ε ε' i a * bpl ε ε' j b = bpl ε ε' j b * bpl ε ε' i a

def FockPairGl : Prop :=
  ∀ (M n' : ℕ) (ε : Fin M → Bool) (ε' : Fin n' → Bool),
    GlRel (Eg ε ε') ∧ GlRel (Eg' ε ε') ∧
    ∀ (i j : Fin M) (a b : Fin n'), Eg ε ε' i j * Eg' ε ε' a b = Eg' ε ε' a b * Eg ε ε' i j

def FockAdj : Prop :=
  ∀ (M n' : ℕ) (ε : Fin M → Bool) (ε' : Fin n' → Bool) (f g : MvPolynomial (Fin M × Fin n') ℂ),
    (∀ (i : Fin M) (a : Fin n'), fockF (bop ε ε' i a f) g =
      (if sgnv ε ε' i a then 1 else -1) * fockF f (bpl ε ε' i a g)) ∧
    (∀ i j : Fin M, fockF (Eg ε ε' i j f) g = (sgn ε i j : ℂ) * fockF f (Eg ε ε' j i g)) ∧
    (∀ a b : Fin n', fockF (Eg' ε ε' a b f) g = (sgn ε' a b : ℂ) * fockF f (Eg' ε ε' b a g))

def FockCas : Prop :=
  ∀ (M n' : ℕ) (ε : Fin M → Bool) (ε' : Fin n' → Bool),
    NN ε ε' = -∑ a, Eg' ε ε' a a ∧
    Cas (Eg ε ε') - (M : ℂ) • NN ε ε' = Cas (Eg' ε ε') - (n' : ℂ) • NN ε ε'

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.LminorPos
section
open Matrix

noncomputable section

namespace Formalism.REAL

def lminor {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) (i : Fin (n + 1)) : ℂ :=
  (Matrix.of fun a b : Fin i => x (Fin.castLE (Nat.lt_succ_iff.mp i.isLt) a)
    (Fin.castLE (Nat.lt_succ_iff.mp i.isLt) b)).det

def LminorPos : Prop :=
  ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ), Yᴴ = Y → ∀ i : Fin (n + 1),
    (lminor (NormedSpace.exp Y) i).im = 0 ∧ 0 < (lminor (NormedSpace.exp Y) i).re

def DecayPhi : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (g : ℝ) (Y : Matrix (Fin n) (Fin n) ℂ),
    StrictAnti lam →
    (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) →
    Yᴴ = Y → (∀ a b : Fin n, ε a = ε b → Y a b = 0) →
    ∏ i : Fin n, (if h : 0 < (i : ℕ) then
        ((lminor (NormedSpace.exp Y) ⟨i, by omega⟩).re) ^
          (-(lam ⟨(i : ℕ) - 1, by omega⟩ - lam i + 1))
      else 1) ≤
      Real.exp (-(g / 8) * min (hs Y) (Real.sqrt (hs Y) / Real.sqrt n))

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.SmoothOnG
section
open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.REAL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def cpart1 {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Z - Jm ε * Zᴴ * Jm ε)

def cpart2 {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / (2 * Complex.I)) • (Z + Jm ε * Zᴴ * Jm ε)

def SmoothOnG {n : ℕ} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∀ g₀, inUJ ε g₀ → ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, inUJ ε g → f g = F g

def Rd {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0

def Ec {n : ℕ} (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => Rd (cpart1 ε Z) f g + Complex.I * Rd (cpart2 ε Z) f g

def Eab {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  Ec ε (Matrix.single a b 1) f

def CpartMem : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ),
    inG ε (cpart1 ε Z) ∧ inG ε (cpart2 ε Z) ∧ Z = cpart1 ε Z + Complex.I • cpart2 ε Z ∧
    (inG ε Z → cpart1 ε Z = Z ∧ cpart2 ε Z = 0)

def RdExt : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (f F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (U : Set (Matrix (Fin n) (Fin n) ℂ)) (g X : Matrix (Fin n) (Fin n) ℂ),
    IsOpen U → g ∈ U → inUJ ε g → ContDiffOn ℝ ∞ F U → (∀ h ∈ U, inUJ ε h → f h = F h) →
    inG ε X → Rd X f g = fderiv ℝ F g (g * X)

def RdSmooth : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (X : Matrix (Fin n) (Fin n) ℂ),
    SmoothOnG ε f → inG ε X → SmoothOnG ε (Rd X f)

def RdLin : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (f f' : Matrix (Fin n) (Fin n) ℂ → ℂ) (X Y : Matrix (Fin n) (Fin n) ℂ)
    (r : ℝ) (c : ℂ) (g : Matrix (Fin n) (Fin n) ℂ),
    SmoothOnG ε f → SmoothOnG ε f' → inG ε X → inG ε Y → inUJ ε g →
    Rd (X + Y) f g = Rd X f g + Rd Y f g ∧ Rd ((r : ℂ) • X) f g = (r : ℂ) * Rd X f g ∧
    Rd X (fun h => f h + c * f' h) g = Rd X f g + c * Rd X f' g

def RdBracket : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (X Y g : Matrix (Fin n) (Fin n) ℂ),
    SmoothOnG ε f → inG ε X → inG ε Y → inUJ ε g →
    Rd X (Rd Y f) g - Rd Y (Rd X f) g = Rd (X * Y - Y * X) f g

def EabGl : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (a b c d : Fin n)
    (g : Matrix (Fin n) (Fin n) ℂ), SmoothOnG ε f → inUJ ε g →
    Eab ε a b (Eab ε c d f) g - Eab ε c d (Eab ε a b f) g =
      (if b = c then Eab ε a d f g else 0) - (if d = a then Eab ε c b f g else 0)

def RdLeft : Prop :=
  ∀ (n : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (X h g : Matrix (Fin n) (Fin n) ℂ),
    Rd X (fun x => f (h * x)) g = Rd X f (h * g)

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.StatementB
section
open Finset

noncomputable section

namespace Formalism.REAL

def epow {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : ℕ → Fin n → Fin n → A
  | 0 => fun a b => if a = b then 1 else 0
  | k + 1 => fun a b => ∑ c, epow E k a c * E c b

def etr {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) : A :=
  ∑ a, epow E k a a

def IsHW {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (ν : Fin n → ℂ) (v : V) : Prop :=
  (∀ a, E a a v = ν a • v) ∧ ∀ a b, a < b → E a b v = 0

def lsh {n : ℕ} (ν : Fin n → ℂ) : Fin n → ℂ := fun a => ν a + ((n : ℂ) - 1 - (a : ℂ))

def Amat {n : ℕ} (l : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if a = b then l a else if a < b then -1 else 0

def Dfac {n : ℕ} (l : Fin n → ℂ) (s : Fin n) : ℂ :=
  ∏ a ∈ univ.erase s, (l s - l a - 1) / (l s - l a)

def vand {n : ℕ} (l : Fin n → ℂ) : ℂ :=
  ∏ a, ∏ b ∈ univ.filter (fun b => a < b), (l a - l b)

def EpowCov : Prop :=
  ∀ (A : Type) [Ring A] (n : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (k : ℕ) (a b c d : Fin n),
      E c d * epow E k a b - epow E k a b * E c d =
        (if d = a then epow E k c b else 0) - (if b = c then epow E k a d else 0)

def EtrCentral : Prop :=
  ∀ (A : Type) [Ring A] (n : ℕ) (E : Fin n → Fin n → A), GlRel E →
    ∀ (k : ℕ) (c d : Fin n), etr E k * E c d = E c d * etr E k

def UpperKill : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ (k : ℕ) (a b : Fin n), a < b → epow E k a b v = 0

def HWDiag : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ (k : ℕ) (a : Fin n),
      epow E (k + 1) a a v =
        lsh ν a • epow E k a a v - ∑ b ∈ univ.filter (fun b => a < b), epow E k b b v

def DiagChar : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ a : Fin n,
      ∑ i ∈ range (n + 1),
        (∏ s : Fin n, (Polynomial.X - Polynomial.C (lsh ν s))).coeff i • epow E i a a v = 0

def PPGen : Prop :=
  ∀ (n : ℕ) (l : Fin n → ℂ) (u : ℂ), (∀ a, u ≠ l a) →
    ∑ a, ∑ b, ((u • (1 : Matrix (Fin n) (Fin n) ℂ) - Amat l)⁻¹) a b =
      1 - ∏ a, (u - l a - 1) / (u - l a)

def DsVand : Prop :=
  ∀ (n : ℕ) (l : Fin n → ℂ), Function.Injective l →
    ∀ s, Dfac l s = vand (l - Pi.single s 1) / vand l

def DsSum : Prop :=
  ∀ (n : ℕ) (l : Fin n → ℂ), Function.Injective l → ∑ s, Dfac l s = (n : ℂ)

def TrPowHW : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v → Function.Injective (lsh ν) →
    ∀ k : ℕ, etr E k v = (∑ s, Dfac (lsh ν) s * lsh ν s ^ k) • v

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.StatementD
section
open Finset

noncomputable section

namespace Formalism.REAL

def rhoS (n : ℕ) : Fin n → ℝ := fun a => ((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ)

def OperatorMatrixNormSqBound : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (n : ℕ) (A p t : ℝ)
    (W' : H) (x z : Fin n → H) (R : Fin n → Fin n → H →L[ℂ] H),
    0 < A → 0 ≤ p → 0 ≤ t → p ≤ ‖W'‖ →
    (∀ a, z a = ∑ b, R a b (x b)) → (∀ a b, ‖R a b‖ ≤ 2 * (n : ℝ)) →
    A / 2 * ‖W'‖ ^ 2 ≤ ∑ a, ‖z a‖ ^ 2 →
    ∑ b, ‖x b‖ ^ 2 ≤ t * p →
    p ≤ 8 * (n : ℝ) ^ 4 * t / A

def DomCas : Prop :=
  ∀ (n : ℕ) (lam mu : Fin n → ℝ) (c : Fin n → Fin n → ℝ),
    Antitone lam → Antitone mu → (∀ a b, 0 ≤ c a b) →
    lam - mu = ∑ a, ∑ b, (if a < b then c a b • root a b else 0) →
    nsq (mu + rhoS n) ≤ nsq (lam + rhoS n)

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.StatementKT
section
open scoped InnerProductSpace
open Finset

noncomputable section

namespace Formalism.REAL

def KRel {A : Type*} [Ring A] {n : ℕ} (ε : Fin n → Bool) (F : Fin n → Fin n → A) : Prop :=
  ∀ a b c d : Fin n, ε a = ε b → ε c = ε d →
    F a b * F c d - F c d * F a b = (if b = c then F a d else 0) - (if d = a then F c b else 0)

def KUnit {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) : Prop :=
  ∀ a b : Fin n, ε a = ε b → ∀ x y : V, ⟪F a b x, y⟫_ℂ = ⟪x, F b a y⟫_ℂ

def KStable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) : Prop :=
  ∀ a b : Fin n, ε a = ε b → ∀ x ∈ S, F a b x ∈ S

def kSpan {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) : Submodule ℂ V :=
  sInf {S : Submodule ℂ V | x ∈ S ∧ KStable ε F S}

def ew {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (F : Fin n → Fin n → Module.End ℂ V) : List (Fin n × Fin n) → Module.End ℂ V
  | [] => 1
  | p :: w => F p.1 p.2 * ew F w

def lowSpan {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) : Submodule ℂ V :=
  Submodule.span ℂ {y | ∃ w : List (Fin n × Fin n),
    (∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) ∧ y = ew F w x}

def isoPart {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Fin n → ℝ)) (S : Submodule ℂ V) : Submodule ℂ V :=
  ⨆ (y : V) (_ : y ∈ S ∧ ∃ μ ∈ T, KHighest ε F μ y), kSpan ε F y

def ckv {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) : ℝ := nsq (μ + rhoC ε) - nsq (rhoC ε)

def negT {A : Type*} [Ring A] {n : ℕ} (F : Fin n → Fin n → A) : Fin n → Fin n → A :=
  fun a b => -F b a

theorem glRel_kRel {A : Type*} [Ring A] {n : ℕ} (ε : Fin n → Bool) (F : Fin n → Fin n → A)
    (h : GlRel F) : KRel ε F := by
  unfold GlRel at h
  intro a b c d _ _
  exact h a b c d

theorem isUnitary_kUnit {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (h : IsUnitary ε F) : KUnit ε F := by
  unfold IsUnitary at h
  intro a b hab x y
  simpa [sgn, hab] using h a b x y

def KNegT : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V),
    (KRel ε F → KRel ε (negT F)) ∧ (KUnit ε F → KUnit ε (negT F)) ∧
    ∀ (ν : Fin n → ℝ) (x : V),
      (IsWeight F ν x ∧ ∀ a b, a < b → ε a = ε b → F b a x = 0) ↔ KHighest ε (negT F) (-ν) x

def KWtOrth : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (μ ν : Fin n → ℝ) (x y : V),
    KUnit ε F → IsWeight F μ x → IsWeight F ν y → μ ≠ ν → ⟪x, y⟫_ℂ = 0

def KLow : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (x : V),
    KRel ε F → KHighest ε F μ x →
    kSpan ε F x = lowSpan ε F x ∧
    ∀ y ∈ lowSpan ε F x, IsWeight F μ y → ∃ c : ℂ, y = c • x

def KCasSpan : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (x : V),
    KRel ε F → KHighest ε F μ x →
    ∀ y ∈ kSpan ε F x, CasK ε F y = ((ckv ε μ : ℝ) : ℂ) • y

def KOrth : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (μ ν : Fin n → ℝ) (x y : V),
    KRel ε F → KUnit ε F → KHighest ε F μ x → KHighest ε F ν y → μ ≠ ν →
    ∀ x' ∈ kSpan ε F x, ∀ y' ∈ kSpan ε F y, ⟪x', y'⟫_ℂ = 0

def KHiUniq : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (μ ν : Fin n → ℝ) (x y : V),
    KRel ε F → KUnit ε F → KHighest ε F μ x → y ∈ kSpan ε F x → KHighest ε F ν y →
    y = 0 ∨ (ν = μ ∧ ∃ c : ℂ, y = c • x)

def KFormUniq : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (x : V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
    KRel ε F → KUnit ε F → KHighest ε F μ x →
    (∀ a b, ε a = ε b → ∀ y ∈ kSpan ε F x, ∀ z ∈ kSpan ε F x, H (F a b y) z = H y (F b a z)) →
    ∀ y ∈ kSpan ε F x, ∀ z ∈ kSpan ε F x, H y z * ((‖x‖ ^ 2 : ℝ) : ℂ) = H x x * ⟪y, z⟫_ℂ

def KCommScalar : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (x : V) (T : Module.End ℂ V),
    KRel ε F → KUnit ε F → KHighest ε F μ x →
    (∀ y ∈ kSpan ε F x, T y ∈ kSpan ε F x) →
    (∀ a b, ε a = ε b → ∀ y ∈ kSpan ε F x, T (F a b y) = F a b (T y)) →
    ∃ c : ℂ, ∀ y ∈ kSpan ε F x, T y = c • y

def KHiExist : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V),
    FiniteDimensional ℂ S → KRel ε F → KUnit ε F → KStable ε F S → S ≠ ⊥ →
    ∃ x ∈ S, x ≠ 0 ∧ ∃ μ : Fin n → ℝ, KHighest ε F μ x

def KIrr : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (x : V),
    FiniteDimensional ℂ (kSpan ε F x) → KRel ε F → KUnit ε F → KHighest ε F μ x →
    ∀ S : Submodule ℂ V, S ≤ kSpan ε F x → KStable ε F S → S = ⊥ ∨ S = kSpan ε F x

def KDecomp : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V),
    FiniteDimensional ℂ S → KRel ε F → KUnit ε F → KStable ε F S →
    ∃ (m : ℕ) (x : Fin m → V) (μ : Fin m → Fin n → ℝ),
      (∀ i, x i ∈ S ∧ x i ≠ 0 ∧ KHighest ε F (μ i) (x i)) ∧
      (∀ i i', i ≠ i' → ∀ y ∈ kSpan ε F (x i), ∀ z ∈ kSpan ε F (x i'), ⟪y, z⟫_ℂ = 0) ∧
      (⨆ i, kSpan ε F (x i)) = S

def KIsoSplit : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (T : Set (Fin n → ℝ)),
    FiniteDimensional ℂ S → KRel ε F → KUnit ε F → KStable ε F S →
    (∀ y ∈ isoPart ε F T S, ∀ z ∈ isoPart ε F Tᶜ S, ⟪y, z⟫_ℂ = 0) ∧
    isoPart ε F T S ⊔ isoPart ε F Tᶜ S = S

def KWtBound : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (μ ν : Fin n → ℝ) (x y : V),
    KRel ε F → KUnit ε F → KHighest ε F μ x → y ∈ kSpan ε F x → y ≠ 0 → IsWeight F ν y →
    nsq ν ≤ ckv ε μ

def KCasBound : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (R : ℝ),
    FiniteDimensional ℂ S → KRel ε F → KUnit ε F → KStable ε F S → 0 ≤ R →
    (∀ (μ : Fin n → ℝ) (y : V), y ∈ S → y ≠ 0 → IsWeight F μ y → ∀ a, |μ a| ≤ R) →
    ∀ y ∈ S, (⟪y, CasK ε F y⟫_ℂ).re ≤ (n : ℝ) * (R + n) ^ 2 * ‖y‖ ^ 2

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.UJLocCompact
section
noncomputable section

namespace Formalism.REAL

def UJEmb : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    Topology.IsClosedEmbedding (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
      Matrix (Fin n) (Fin n) ℂ)) ∧
    Set.range (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) =
      {g | inUJ ε g}

def UJLocCompact : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), LocallyCompactSpace (UJ ε)

end Formalism.REAL
end
end

