import Formalism.LogFactorialIndices.Bundle0001
import Formalism.IncomingBounds.Bundle0001

-- bundled from Formalism.IncomingBounds.IndexLastStep
section
noncomputable section

namespace Formalism.IncomingBounds

open Module

def IndexLastStep : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (ϖ : O), Irreducible ϖ →
    ∀ (e : ℤ) (M Θ : Submodule O X), Formalism.LatticeIndexTer.IsLat O K X M → Formalism.LatticeIndexTer.IsLat O K X Θ →
      ∀ W : Submodule K X,
        Formalism.LatticeIndexTer.idx O X (M ⊓ W.restrictScalars O) (Θ ⊓ W.restrictScalars O) ≤
          e * (finrank K W : ℤ) +
            ((Formalism.LatticeIndexTer.qlen O X
              (M.map ((((algebraMap O K ϖ) ^ e) • LinearMap.id : X →ₗ[K] X).restrictScalars O) ⊔ Θ)
              Θ).toNat : ℤ)

end Formalism.IncomingBounds
end
end

-- bundled from Formalism.IncomingBounds.LevelTail
section
noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

def chSol (d : ℕ) (l h : ℝ) (p : ZMod d → ℝ) (a : ZMod d) : ℝ :=
  ∑' k : ℕ, (h - p (a + ((k + 1 : ℕ) : ZMod d))) / l ^ (k + 1)

def CHRecursion : Prop :=
  ∀ (d : ℕ) [NeZero d] (l : ℝ), 1 < l → ∀ (h : ℝ) (p x : ZMod d → ℝ),
    (∀ a : ZMod d, x a + (h - p a) = l * x (a - 1)) ↔ ∀ a : ZMod d, x a = chSol d l h p a

def CHValue : Prop :=
  ∀ (d : ℕ) [NeZero d] (l : ℕ), 2 ≤ l → 2 ≤ d → Even d →
    ∀ (r j j' rh : ℕ), rh ≤ j' → j + j' ≤ r →
      (∀ a : ZMod d, Even a.val →
        chSol d l ((r : ℝ) - rh) (fun b => if Even b.val then (r : ℝ) - j' else (j' : ℝ)) a =
            ((r : ℝ) - j' - rh) * gam l + ((j' : ℝ) - rh) * rho l ∧
          chSol d l ((r : ℝ) - rh) (fun b => if Even b.val then (r : ℝ) - j' else (j' : ℝ)) a ≤
            ((r - j' - j : ℕ) : ℝ) * gam l + ((j + j' : ℕ) : ℝ) / ((l : ℝ) - 1)) ∧
      ∀ a : ZMod d,
        chSol d l ((r : ℝ) - rh) (fun _ => (r : ℝ) - j') a = ((j' : ℝ) - rh) / ((l : ℝ) - 1) ∧
          ((j' : ℝ) - rh) / ((l : ℝ) - 1) ≤ ((j + j' : ℕ) : ℝ) / ((l : ℝ) - 1)

def NewtonWindow : Prop :=
  ∀ (R : Type) [CommRing R] (I : AddSubgroup R) (D : ℕ) (a : ℕ → R) (y0 : ℕ),
    (∀ t ≤ D, (∑ s ∈ Finset.range (D + 1), a s * ((Nat.choose (y0 + t) s : ℕ) : R)) ∈ I) →
      ∀ y : ℕ, (∑ s ∈ Finset.range (D + 1), a s * ((Nat.choose y s : ℕ) : R)) ∈ I

def capNat (n0 y : ℕ) : ℕ := ∏ a ∈ Finset.range n0, (y + a).factorial / a.factorial

def CapVal : Prop :=
  ∀ l : ℕ, l.Prime → ∀ n0 n y : ℕ, n0 ≤ n →
    (padicValNat l (capNat n0 y) : ℝ) ≤ (n0 : ℝ) * y / ((l : ℝ) - 1) + n * (Real.logb l n + 1)

def uFac (l x : ℕ) : ℚ := (-1) ^ x * ((l * x).factorial : ℚ) / ((l : ℚ) ^ x * (x.factorial : ℚ))

def FactSplit : Prop :=
  ∀ l : ℕ, 2 ≤ l → ∀ i x : ℕ,
    (((l ^ i * x).factorial : ℕ) : ℚ) =
      (-1) ^ ((∑ s ∈ Finset.range i, l ^ s) * x) * (l : ℚ) ^ ((∑ s ∈ Finset.range i, l ^ s) * x) *
        (x.factorial : ℚ) * ∏ s ∈ Finset.range i, uFac l (l ^ s * x)

def WeightIdentities : Prop :=
  ∀ l : ℕ, 2 ≤ l → ∀ i : ℕ, 1 ≤ i →
    (-(1 + ((l : ℝ) ^ i - l) * rho l) + (l : ℝ) ^ i * (rho l + ((l : ℝ) ^ i)⁻¹ / 2) +
        (rho l + 1 / 2) = 1 / ((l : ℝ) - 1)) ∧
      (∀ B : ℝ, ((l : ℝ) ^ i * B) * (rho l + ((l : ℝ) ^ i)⁻¹ / 2) + B * (rho l + 1 / 2) =
        B * ((1 + ((l : ℝ) ^ i - l) * rho l) + 1 / ((l : ℝ) - 1))) ∧
      (((l : ℝ) ^ i - 1) / ((l : ℝ) - 1) - (1 + ((l : ℝ) ^ i - l) * rho l) + 1 / ((l : ℝ) - 1) =
        ((l : ℝ) ^ i + 1) * gam l - 1) ∧
      0 ≤ ((l : ℝ) ^ i + 1) * gam l - 1

def ContentShift : Prop :=
  ∀ (l d : ℕ) [NeZero d], 3 ≤ l → 2 ≤ d → Even d → ∀ (th : ℝ) (D' E : ZMod d → ℝ),
    0 ≤ th → 0 ≤ D' → 0 ≤ E → (∀ a, E a ≤ 2 * th * D' a) →
      Fnum l d D' ≤ Fnum l d (D' + E) + 6 * th * (∑ a : ZMod d, D' a) / l

def LevelTail : Prop :=
  ∀ (l d : ℕ) [NeZero d], 2 ≤ l → ∀ (D : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ), IsFlow l d D x →
    ∀ i0 : ℕ,
      (∑ a : ZMod d, ∑ i ∈ (oddLevels d).filter (fun i => i0 ≤ i), x a i) ≤
        (∑ a : ZMod d, D a) / (l : ℝ) ^ i0

end Formalism.IncomingBounds
end
end

-- bundled from Formalism.IncomingBounds.StatementThmP
section
noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

abbrev PVar (n0 : ℕ) := (Fin n0 × Fin n0) ⊕ (Fin n0 × Fin n0)

variable {C : Type} [Field C]

def detL (C : Type) [Field C] (n0 : ℕ) : MvPolynomial (PVar n0) C :=
  Matrix.det (Matrix.of fun b c : Fin n0 => MvPolynomial.X (Sum.inl (b, c)))

def detR (C : Type) [Field C] (n0 : ℕ) : MvPolynomial (PVar n0) C :=
  Matrix.det (Matrix.of fun b c : Fin n0 => MvPolynomial.X (Sum.inr (b, c)))

def mfact {σ : Type} (m : σ →₀ ℕ) : ℕ := m.prod fun _ k => k.factorial

def jetAt0 {σ : Type} (P : MvPolynomial σ C) (g : MvPowerSeries σ C) : C :=
  ∑ m ∈ P.support, MvPolynomial.coeff m P * (mfact m : C) * MvPowerSeries.coeff m g

def mvExp {σ : Type} (h : MvPowerSeries σ C) : MvPowerSeries σ C :=
  fun m => ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (h ^ k) / (k.factorial : C)

def expE (l i : ℕ) : ℕ := 1 + l * ∑ t ∈ Finset.range ((i - 1) / 2), (l ^ 2) ^ t

def hP (C : Type) [Field C] (l i n0 : ℕ) (h1 : MvPowerSeries (PVar n0) C) :
    MvPowerSeries (PVar n0) C :=
  -((l : C) ^ (expE l i))⁻¹ • (∑ b : Fin n0, ∑ c : Fin n0,
      MvPowerSeries.X (Sum.inl (b, c)) ^ (l ^ i) * MvPowerSeries.X (Sum.inr (b, c))) + h1

def LamP (C : Type) [Field C] (l i n0 : ℕ) (h1 : MvPowerSeries (PVar n0) C) (y : ℕ) : C :=
  jetAt0 (detL C n0 ^ (l ^ i * y) * detR C n0 ^ y) (mvExp (hP C l i n0 h1))

def degL {n0 : ℕ} (m : PVar n0 →₀ ℕ) : ℕ := ∑ b : Fin n0, ∑ c : Fin n0, m (Sum.inl (b, c))

def degR {n0 : ℕ} (m : PVar n0 →₀ ℕ) : ℕ := ∑ b : Fin n0, ∑ c : Fin n0, m (Sum.inr (b, c))

def WeightCond (v : AddValuation C (WithTop ℝ)) (l i n0 : ℕ) (h1 : MvPowerSeries (PVar n0) C) :
    Prop :=
  ∀ m : PVar n0 →₀ ℕ,
    (((1 / ((l : ℝ) - 1)) : ℝ) : WithTop ℝ) ≤
      v (MvPowerSeries.coeff m h1) +
        (((degL m : ℝ) * (rho l + ((l : ℝ) ^ i)⁻¹ / 2 - ((l : ℝ) ^ i)⁻¹ / 8) +
          (degR m : ℝ) * (rho l + 1 / 2 - ((l : ℝ) ^ i)⁻¹ / 8) : ℝ) : WithTop ℝ)

def diffOp {σ : Type} (P Q : MvPolynomial σ C) : MvPolynomial σ C :=
  ∑ m ∈ P.support, ∑ a ∈ Q.support,
    if m ≤ a then
      MvPolynomial.monomial (a - m)
        (MvPolynomial.coeff m P * MvPolynomial.coeff a Q * ((mfact a : C) / (mfact (a - m) : C)))
    else 0

def CayleyId : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (n0 s : ℕ),
    diffOp (detL C n0) (detL C n0 ^ (s + 1)) =
      ((∏ a ∈ Finset.range n0, ((s : C) + 1 + a))) • detL C n0 ^ s

def ThmP : Prop :=
  ∃ C0 : ℝ, ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → (∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) →
    ∀ (i : ℕ), Odd i → ∀ (n n0 : ℕ), 1 ≤ n → n0 ≤ n →
    ∀ h1 : MvPowerSeries (PVar n0) C, MvPowerSeries.constantCoeff h1 = 0 →
      WeightCond v l i n0 h1 →
      ∀ Y0 : ℕ, ∃ y : ℕ, Y0 ≤ y ∧
        (y : ℝ) < Y0 + C0 * (n : ℝ) ^ 2 * (l : ℝ) ^ i * Real.log ((n : ℝ) * (l : ℝ) ^ i) ∧
        v (LamP C l i n0 h1 y) ≤
          ((((n0 : ℝ) * y * (((l : ℝ) ^ i + 1) * gam l - 1) + n * (Real.logb l n + 1)) : ℝ) :
            WithTop ℝ)

def ThmPFromCayley : Prop := CayleyId → ThmP

end Formalism.IncomingBounds
end
end

