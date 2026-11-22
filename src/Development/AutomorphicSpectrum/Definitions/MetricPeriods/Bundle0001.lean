import Mathlib

-- bundled from Development.AutomorphicSpectrum.Definitions.MetricPeriods.EtaCut
section
namespace GlobalTheory.CompanionTheory.Ar.ThA

open scoped Matrix ComplexConjugate

noncomputable section

abbrev Low (n : ℕ) : Type := {p : Fin n × Fin n // p.2 < p.1}

def lowU {n : ℕ} (z : Low n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if h : b < a then z ⟨(a, b), h⟩ else if a = b then 1 else 0

def lmin {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin (n + 1)) : ℂ :=
  (M.submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.isLt))).det

def gramA {n : ℕ} (A x y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  xᵀ * A * y.map conj

def Jp (n p : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a : Fin n => if (a : ℕ) < p then 1 else -1

def sqn {n : ℕ} (z : Low n → ℂ) : ℝ := ∑ e, ‖z e‖ ^ 2

def densA {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : Low n → ℂ) : ℝ :=
  ∏ i : Fin n, ‖lmin (gramA A (lowU z) (lowU z)) i.castSucc‖ ^ (-2 : ℤ)

def etaCut {W : Type} [NormedAddCommGroup W] (χ : ℝ → ℝ) (r0 δ : ℝ) (v : W) : ℝ :=
  χ (‖v‖ ^ 2 / r0 ^ 2) * Real.log ((‖v‖ ^ 2 / r0 ^ 2 + δ) / 2)

def IsCut (χ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) ∧ (∀ t, t ≤ 1 / 4 → χ t = 1) ∧
    (∀ t, 97 / 100 ≤ t → χ t = 0) ∧ (∀ t, |deriv χ t| ≤ 3) ∧ ∀ t, |deriv (deriv χ) t| ≤ 30

end

end GlobalTheory.CompanionTheory.Ar.ThA
end

-- bundled from Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open Matrix
open scoped ComplexOrder

def gramOf {N : ℕ} (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  gᴴ * diagonal (fun i => (hd i : ℂ)) * g

def gramHead {N : ℕ} (hd : Fin N → ℝ) (k : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) :
    Matrix {a : Fin N // (a : ℕ) < k} {a : Fin N // (a : ℕ) < k} ℂ :=
  (gramOf hd g).submatrix Subtype.val Subtype.val

def gramLog {N : ℕ} (hd : Fin N → ℝ) (k : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (1 / 2) * Real.log ‖(gramHead hd k g).det‖

def sigForm (N j : ℕ) : Fin N → ℝ := fun a => if (a : ℕ) < N - j then -1 else 1

def InFlagDomain (N j : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsUnit g.det ∧ (-gramHead (sigForm N j) (N - j) g).PosDef

def stepPot (N j : ℕ) (i : Fin N) (g : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  if (i : ℕ) + 1 ≤ j then gramLog (sigForm N j) (N - j + ((i : ℕ) + 1)) g - gramLog (sigForm N j) (N - j) g
  else gramLog (sigForm N j) N g - gramLog (sigForm N j) (N - j) g + gramLog (sigForm N j) ((i : ℕ) + 1 - j) g

def herm2 (G : Matrix (Fin 2) (Fin 2) ℂ) (u w : Fin 2 → ℂ) : ℂ := star u ⬝ᵥ (G *ᵥ w)

def xiPot (G : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) : ℝ :=
  -Real.log (herm2 G ![1, a] ![1, a]).re + (1 / 2) * Real.log G.det.re

def logSin (G : Matrix (Fin 2) (Fin 2) ℂ) (a₀ a₁ : ℂ) : ℝ :=
  (1 / 2) * Real.log (1 - ‖herm2 G ![1, a₀] ![1, a₁]‖ ^ 2 /
    ((herm2 G ![1, a₀] ![1, a₀]).re * (herm2 G ![1, a₁] ![1, a₁]).re))

theorem inFlagDomain_one (N : ℕ) : InFlagDomain N N 1 := by
  refine ⟨by simp, ?_⟩
  haveI : IsEmpty {a : Fin N // (a : ℕ) < N - N} := ⟨fun a => by have := a.2; omega⟩
  refine ⟨by ext i; exact isEmptyElim i, fun x hx => ?_⟩
  exact absurd (by ext i; exact isEmptyElim i) hx

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial

def formPoly {σ : Type} [Fintype σ] (n : ℕ) (a : (Fin n → σ) → ℝ) : MvPolynomial σ ℝ :=
  ∑ w : Fin n → σ, C (a w) * ∏ j, X (w j)

variable {Ψ : Type} {N : ℕ}

def gapX (p : Ψ × Fin N) : MvPolynomial (Ψ × Fin N) ℝ :=
  X p - if h : (p.2 : ℕ) + 1 < N then X (p.1, ⟨(p.2 : ℕ) + 1, h⟩) else 0

def gap (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N) : ℝ := eval lam (gapX p)

def Dominant (lam : Ψ × Fin N → ℝ) : Prop := ∀ p : Ψ × Fin N, (p.2 : ℕ) + 1 < N → 0 ≤ gap lam p

def toWt : MvPolynomial (Ψ × Fin N) ℝ →ₐ[ℝ] MvPolynomial (Ψ × Fin N) ℝ := aeval gapX

def toWtS : MvPolynomial (Option (Ψ × Fin N)) ℝ →ₐ[ℝ] MvPolynomial (Option (Ψ × Fin N)) ℝ :=
  aeval fun o : Option (Ψ × Fin N) => o.elim (X none) fun p => rename some (gapX p)

def gapS (lam : Ψ × Fin N → ℝ) (s : ℝ) : Option (Ψ × Fin N) → ℝ := fun o => o.elim s (gap lam)

def xiCoef [DecidableEq Ψ] (τ : Ψ) (a : Fin N) (p : Ψ × Fin N) : ℤ :=
  if p.1 = τ then
    (if (p.2 : ℕ) + 1 = a then 1 else 0) + (if (p.2 : ℕ) = a + 1 then 1 else 0) - (if p.2 = a then 2 else 0)
  else 0

def linePoly {σ : Type} (c : σ → ℝ) (e : σ → ℤ) (Q : MvPolynomial σ ℝ) : Polynomial ℝ :=
  aeval (fun a => Polynomial.C (c a) - Polynomial.C ((e a : ℝ) / 2) * Polynomial.X) Q

def rhoWt (Ψ : Type) (N : ℕ) : Ψ × Fin N → ℝ := fun p => -((p.2 : ℕ) : ℝ)

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.MetricPeriods.RegularFormsIsBundleProjectiveCover
section
open NumberField IsDedekindDomain
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Deg

variable (K : Type) [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]

def rkL (M : Submodule (𝓞 K) V) : ℕ := Module.finrank K (Submodule.span K (M : Set V))

def IsFull (M : Submodule (𝓞 K) V) (x : Fin (rkL K M) → V) : Prop :=
  (∀ a, x a ∈ M) ∧ LinearIndependent K x

def degAt (M : Submodule (𝓞 K) V) (ip : (K →+* ℂ) → V → V → ℂ) {n : ℕ} (x : Fin n → V) : ℝ :=
  (Real.log (((Submodule.span (𝓞 K) (Set.range x)).toAddSubgroup.relIndex M.toAddSubgroup : ℕ) : ℝ) -
    ∑ σ : K →+* ℂ, Real.log ‖(Matrix.of fun a b => ip σ (x a) (x b)).det‖ / 2) / (Module.finrank ℚ K : ℝ)

def degL (M : Submodule (𝓞 K) V) (ip : (K →+* ℂ) → V → V → ℂ) : ℝ :=
  degAt K M ip (Classical.epsilon (IsFull K M))

def IsHermOn (W : Submodule K V) (ip : (K →+* ℂ) → V → V → ℂ) : Prop :=
  ∀ σ : K →+* ℂ,
    (∀ f ∈ W, ∀ f' ∈ W, ∀ g ∈ W, ip σ (f + f') g = ip σ f g + ip σ f' g) ∧
    (∀ (a : K), ∀ f ∈ W, ∀ g ∈ W, ip σ (a • f) g = σ a * ip σ f g) ∧
    (∀ f ∈ W, ∀ g ∈ W, ip σ g f = (starRingEnd ℂ) (ip σ f g)) ∧
    ∀ (n : ℕ) (x : Fin n → V), (∀ a, x a ∈ W) → LinearIndependent K x →
      (Matrix.of fun a b => ip σ (x a) (x b)).PosDef

variable (V) in

structure PtNorms where

  Pt : HeightOneSpectrum (𝓞 K) → Type

  nrm : ∀ v, Pt v → V → ℝ
  nonneg : ∀ v y f, 0 ≤ nrm v y f
  add_le : ∀ v y f g, nrm v y (f + g) ≤ max (nrm v y f) (nrm v y g)
  smul : ∀ v y (a : K) f, nrm v y (a • f) = FinitePlace.mk v a * nrm v y f

variable {K}

def PtNorms.supLat [IsScalarTower (𝓞 K) K V] (P : PtNorms K V) (W : Submodule K V) : Submodule (𝓞 K) V where
  carrier := {f | f ∈ W ∧ ∀ v y, P.nrm v y f ≤ 1}
  add_mem' := fun {f g} hf hg =>
    ⟨W.add_mem hf.1 hg.1, fun v y => (P.add_le v y f g).trans (max_le (hf.2 v y) (hg.2 v y))⟩
  zero_mem' := ⟨W.zero_mem, fun v y => by
    have h := P.smul v y 0 0
    rw [zero_smul, map_zero, zero_mul] at h
    rw [h]; exact zero_le_one⟩
  smul_mem' := fun a f hf => by
    have e : a • f = (algebraMap (𝓞 K) K a) • f := (algebraMap_smul K a f).symm
    refine ⟨by rw [e]; exact W.smul_mem _ hf.1, fun v y => ?_⟩
    rw [e, P.smul]
    have h1 : FinitePlace.mk v (algebraMap (𝓞 K) K a) ≤ 1 := by
      rw [FinitePlace.mk_apply]; exact FinitePlace.norm_le_one K v a
    exact mul_le_one₀ h1 (P.nonneg v y f) (hf.2 v y)

end GlobalTheory.CompanionTheory.Ar.Deg
end
end

