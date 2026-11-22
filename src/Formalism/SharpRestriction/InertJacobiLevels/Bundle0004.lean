import Formalism.LocalRingCardinality.Bundle0006
import Formalism.SharpRestriction.InertJacobiLevels.SizeDataAt
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0002

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.ExtraH
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.DV NumberField

def logOmV (D : D7) (dl : ℝ) : ℝ := Real.eulerMascheroniConstant + Real.log (Real.pi / D.host.v) - dl

def LaV (D : D7) (sc : Scale) : ℝ := Real.log (sc.a * D.host.rdE)

def LprimeV (D : D7) (sc : Scale) : ℝ :=
  Real.log (sc.b * D.host.rdE * ((D.host.g 0 : ℝ) * D.host.g 1) * D.R.nV)

def kerPlaceV (D : D7) (dl : ℝ) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) : ℝ :=
  (∑ i ∈ Finset.range (D.R.N (j - 1)), phF (nuRow D u j τ i)) -
    (∑ i ∈ Finset.range (D.R.N (j - 1)), nuRow D u j τ i) * logOmV D dl

def SZbKV (D : D7) (sc : Scale) (dl C : ℝ) (u : D.what₂.Word) (j : ℕ) : ℝ :=
  (∑ ρ : D.what₂.Tau, kerPlaceV D dl u j ρ) +
    C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * LaV D sc +
    C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2 * sc.L

def InertJacobiLowerValue (D : D7) (sc : Scale) (C : ℝ) (j : ℕ) : ℝ :=
  (∑ ρ : D.what₂.Tau, logHook (D.R.sigW j).1 (aPlus D j ρ)) -
    C * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * LprimeV D sc

def SZbPV (D : D7) (sc : Scale) (aT : D.host.TT → ℤ) (η Sc C : ℝ) (u : D.what₂.Word) : ℝ :=
  -(∑ t : D.host.TT, (aT t : ℝ) * Real.log ((D.mem u).A.T : ℝ)) +
    C * ((D.host.TT.card : ℝ) * sc.b' * (D.R.N D.R.m : ℝ) +
      (D.R.f : ℝ) * ((D.R.m : ℝ) * η + Sc) * (D.R.N D.R.m : ℝ) +
      (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2) * LaV D sc

def hVal (D : D7) (sc : Scale) (aT : D.host.TT → ℤ) (η Sc dl C : ℝ) (u : D.what₂.Word) : ℝ :=
  SZbPV D sc aT η Sc C u + (∑ j ∈ SizeData₂.lifts D, SZbKV D sc dl C u j) - ∑ j ∈ SizeData₂.lifts D, InertJacobiLowerValue D sc C j

theorem hExpl_eq (D : D7) (L : SizeData₂ D) (X : DivX D) (C : ℝ) (u : D.what₂.Word) (_h0 : D.what₂.Drows = 0)
    (hk : ∀ e, X.kapR e = 1) : hExpl6 D L X C u = hVal D L.sc L.aT L.etaSz L.Sc L.logDerivativeAtOne C u := by
  have h2 : meanE D (fun e => Real.log (X.kapR e)) = 0 := by
    unfold meanE
    simp [hk]
  unfold hExpl6
  rw [h2, sub_zero]
  rfl

theorem h_eq_of (D : D7) (L : SizeData₂ D) (X : DivX D) (C : ℝ) (h0 : D.what₂.Drows = 0) (hk : ∀ e, X.kapR e = 1)
    (hh : ∀ u, D.div.h u = hVal D L.sc L.aT L.etaSz L.Sc L.logDerivativeAtOne C u) :
    ∀ u, D.div.h u = hExpl6 D L X C u := fun u => (hh u).trans (hExpl_eq D L X C u h0 hk).symm

end Formalism.MainNotions.Inhab

end
end

-- bundled from Formalism.SharpRestriction.InertJacobiLevels.PrimeSupply
section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField

def dlogQ (d : ℕ) (hd : d.Prime) : ℝ :=
  haveI : Fact d.Prime := ⟨hd⟩
  haveI : NeZero d := ⟨hd.ne_zero⟩
  (deriv (DirichletCharacter.LFunction
      ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ d)) 1 /
    DirichletCharacter.LFunction
      ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ d) 1).re

theorem dlogL_one (D : D7) : dlogL D 1 = dlogQ D.host.d D.host.hyp.2.1 := rfl

def ProgAt (C : ℝ) : Prop :=
  ∀ (M : ℕ) (a : ℤ) (X : ℝ), 0 < M → IsCoprime a (M : ℤ) → (M : ℝ) ^ C ≤ X → 3 ≤ X →
    ∃ p : ℕ, ∃ hp : p.Prime, X < p ∧ (p : ℝ) ≤ X ^ 2 ∧ (p : ℤ) ≡ a [ZMOD (M : ℤ)] ∧
      |dlogQ p hp| ≤ C * Real.log p

def ProgPrimes : Prop := ∃ C : ℝ, 1 ≤ C ∧ ProgAt C

def ProgSmall : Prop :=
  ∀ ε A : ℝ, 0 < ε → 0 < A → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ M : ℕ, 3 ≤ M →
    Real.log M ≤ A * x ^ (ε / 5) * Real.log x ^ 2 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ≡ 1 [MOD M] ∧ q ≡ 1 [MOD M] ∧
      Real.log p < x ^ (ε / 3) ∧ Real.log q < x ^ (ε / 3)

def ProgTwo : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 3 ≤ M → ∃ p p' : ℕ, p ≠ p' ∧ p.Prime ∧ p'.Prime ∧ p ≡ 1 [MOD M] ∧ p' ≡ 1 [MOD M] ∧
    Real.log p ≤ C * Real.log M ^ 2 ∧ Real.log p' ≤ C * Real.log M ^ 2

def RayAt (C : ℝ) : Prop :=
  ∀ (d M : ℕ) (h X : ℝ) (S : Finset ℕ), d.Prime → d % 4 = 3 → 0 < M → 0 < h → h ≤ 1 →
    C * (Real.log ((d : ℝ) * M) + Real.log (1 / h) + 1) ^ 2 ≤ Real.log X → 0 < X →
    (S.card : ℝ) ≤ X ^ ((4 : ℝ) / 5) →
    ∃ (u v : ℤ) (T : ℕ), T ∉ S ∧ T.Prime ∧ X ≤ T ∧ (T : ℝ) ≤ X * (1 + h) ∧
      (T : ℤ) = (1 + M * u) ^ 2 + d * (M * v) ^ 2

def RayWindow : Prop := ∃ C : ℝ, 1 ≤ C ∧ RayAt C

def PrimeSupply : Prop := ProgPrimes ∧ RayWindow

structure QDGood (x eps : ℝ) (q d : ℕ) : Prop where
  hyp : HostHyp q d
  q_lo : Real.exp (x ^ (eps / 5) / 2) < q
  q_hi : (q : ℝ) ≤ Real.exp (x ^ (eps / 5))
  d_lo : Real.exp (x ^ (eps / 5) * Real.log x ^ 2 / 2) < d
  d_hi : (d : ℝ) ≤ Real.exp (x ^ (eps / 5) * Real.log x ^ 2)
  split : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ x ^ (eps / 5) → jacobiSym (-(d : ℤ)) p = 1
  dlog : |dlogQ d hyp.2.1| ≤ x ^ eps

end Formalism.MainNotions.Inhab

end
end

