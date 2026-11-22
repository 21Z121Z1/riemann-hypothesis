import Mathlib
import Formalism.LocalRingCardinality.DataCoeff
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.ProductThetaMem
import Formalism.PeriodIntegrals.Bundle0016

-- bundled from Formalism.PeriodIntegrals.GTBranch
section
noncomputable section

namespace PI

open Formalism.BasicNotions MvPolynomial

def blkHom (R : Type) [CommRing R] (n : ℕ) :
    Matrix (Fin n) (Fin n) R →* Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R where
  toFun A := Matrix.fromBlocks A 0 0 1
  map_one' := Matrix.fromBlocks_one
  map_mul' A B := by simp [Matrix.fromBlocks_multiply]

def embGL (R : Type) [CommRing R] (n N : ℕ) (h : n + 1 = N) : GL (Fin n) R →* GL (Fin N) R :=
  Units.map (((Matrix.reindexAlgEquiv R R (finSumFinEquiv.trans (finCongr h))).toAlgHom.toRingHom.toMonoidHom).comp
    (blkHom R n))

def Interlace {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : Prop :=
  ∀ i : Fin n, sg.w i ≤ lam.w ⟨i.1, by omega⟩ ∧ lam.w ⟨i.1 + 1, by omega⟩ ≤ sg.w i

def GTBranch : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N),
    (∀ (mu : DomWeight n) (φ φ' : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ),
      (∀ ψ ∈ ({φ, φ'} : Set _), (∀ s ∈ nablaSq ℂ n mu, ψ s ∈ nablaSq ℂ N lam) ∧
        ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu,
          ψ (sqAct ℂ n mu g s) = sqAct ℂ N lam (embGL ℂ n N h g) (ψ s)) →
      (∃ s ∈ nablaSq ℂ n mu, φ' s ≠ 0) →
      Interlace h lam mu ∧ ∃ c : ℂ, ∀ s ∈ nablaSq ℂ n mu, φ s = c • φ' s) ∧
    nablaSq ℂ N lam = ⨆ (mu : DomWeight n) (_ : Interlace h lam mu)
      (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)
      (_ : (∀ s ∈ nablaSq ℂ n mu, φ s ∈ nablaSq ℂ N lam) ∧
        ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu,
          φ (sqAct ℂ n mu g s) = sqAct ℂ N lam (embGL ℂ n N h g) (φ s)), (nablaSq ℂ n mu).map φ

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.HwIrred
section
noncomputable section

namespace PI

open Formalism.BasicNotions MvPolynomial

def HwIrred : Prop :=
  ∀ (N : ℕ) (lam : DomWeight N), nablaSq ℂ N lam = delSq ℂ N lam ∧
    (∀ U : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ), U ≤ nablaSq ℂ N lam →
      (∀ (g : GL (Fin N) ℂ), ∀ f ∈ U, sqAct ℂ N lam g f ∈ U) → U = ⊥ ∨ U = nablaSq ℂ N lam) ∧
    ∀ f ∈ nablaSq ℂ N lam,
      (∀ g : GL (Fin N) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) → sqAct ℂ N lam g f = f) →
      ∃ c : ℂ, f = c • extremal ℂ N lam

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.KerTens
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace PI.KerTens

open Formalism.L2.Th1.H (Sesq matH alphaQ)

def hOne (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n] : Matrix n n ℂ :=
  ((Formalism.L2.Th1.F.area L : ℝ) : ℂ)⁻¹ • (1 : Matrix n n ℂ)

def tensPow {n : Type} (θ : (n → ℂ) → ℂ) (N N' : ℕ) (z : n → Fin N' → Fin N → ℂ) : ℂ :=
  ∏ i : Fin N', ∏ j : Fin N, θ fun τ => z τ i j

def powLat {n : Type} (ΛM : AddSubgroup (n → ℂ)) (N N' : ℕ) : AddSubgroup (n → Fin N' → Fin N → ℂ) where
  carrier := {z | ∀ i j, (fun τ => z τ i j) ∈ ΛM}
  zero_mem' := fun _ _ => ΛM.zero_mem
  add_mem' := fun hx hy i j => ΛM.add_mem (hx i j) (hy i j)
  neg_mem' := fun hx i j => ΛM.neg_mem (hx i j)

def formV (A : ℝ) (n : Type) [Fintype n] (N N' : ℕ) : Sesq (n → Fin N' → Fin N → ℂ) :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun z w => (∑ τ, ∑ i, ∑ j, z τ i j * conj (w τ i j)) / (A : ℂ))
    (by intro a b c; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← mul_div_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)
    (by intro a b c; simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, ← mul_div_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)

def TensSpans : Prop :=
  ∀ (c : ℝ) (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n] (ΛM : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ),
    (∀ F ∈ Formalism.L2.Th1.H.Th (matH (hOne L n)) (alphaQ c (matH (hOne L n))) ΛM, ∃ a : ℂ, F = a • θ) →
    ∀ (N N' : ℕ), ∀ F ∈ Formalism.L2.Th1.H.Th (formV (Formalism.L2.Th1.F.area L) n N N')
      (alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N')) (powLat ΛM N N'), ∃ a : ℂ, F = a • tensPow θ N N'

end PI.KerTens
end
end

-- bundled from Formalism.PeriodIntegrals.SchurFock
section
noncomputable section

namespace PI

open Formalism.BasicNotions MvPolynomial

def SchurFock : Prop :=
  ∀ (N : ℕ) (lam : DomWeight N), ∀ s ∈ nablaSq ℂ N lam,
    (∀ x ∈ Matrix.unitaryGroup (Fin N) ℂ, ‖MvPolynomial.eval (fun v : Fin N × Fin N => x v.1 v.2) s‖ ≤ 1) →
    (normFock lam s s).re ≤ (Module.finrank ℂ (delSq ℂ N lam) : ℝ)

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.WeylForU
section
noncomputable section

namespace PI

open PI.UpqRep Formalism.BasicNotions

def WeylForU : Prop :=
  ∀ (N : ℕ) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
    IsURepOn (Kset (allPos N)) σ → IsKTypeOf (allPos N) σ Λ S →
    (Module.finrank ℂ S : ℝ) =
      (∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b => a < b), (Λ a - Λ b + ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) /
      ∏ i ∈ Finset.range N, (i.factorial : ℝ)

def NablaDim : Prop :=
  ∀ (n : ℕ) (nu : Fin n → ℕ), Antitone nu →
    (Module.finrank ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n nu) : ℚ) =
      ∏ i : Fin n, ∏ j : Fin n,
        if i < j then ((nu i : ℚ) - (nu j : ℚ) + (j : ℚ) - (i : ℚ)) / ((j : ℚ) - (i : ℚ)) else 1

def ModelIso : Prop :=
  ∀ (N : ℕ) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
    IsURepOn (Kset (allPos N)) σ → IsKTypeOf (allPos N) σ Λ S →
    ∃ lam : DomWeight N, (∀ a, Λ a = ((lam.w a : ℤ) : ℝ)) ∧
      Module.finrank ℂ S = Module.finrank ℂ (nablaSq ℂ N lam)

def PolyCoef : Prop :=
  ∀ (N : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
    IsURepOn (Kset (allPos N)) σ → FiniteDimensional ℂ S → IsKStableOn (allPos N) σ S →
    ∀ v ∈ S, ∀ w : H, ∃ (k : ℕ) (P : MvPolynomial (Fin N × Fin N) ℂ), ∀ g ∈ Kset (allPos N),
      inner ℂ w (σ g v) * g.det ^ k = MvPolynomial.eval (fun ij => g ij.1 ij.2) P

end PI
end
end

