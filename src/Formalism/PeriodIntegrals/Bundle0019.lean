import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.PeriodIntegrals.Bundle0016
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairGen

-- bundled from Formalism.PeriodIntegrals.LocJacTyp
section
noncomputable section

namespace PI.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def sdE (ι : Type) [Fintype ι] : Measure (ι → Fv F v ⊗[F] E) :=
  if h : ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ
      (fun x y => psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i)))
  then h.choose else 0

end Meas

section Frames

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def OEv : Set (Fv F v ⊗[F] E) :=
  SetLike.coe (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ))

def sc (x : Fv F v) : Fv F v ⊗[F] E := x ⊗ₜ[F] (1 : E)

def IsDiffVal (d : Fv F v) : Prop :=
  d ≠ 0 ∧ (∀ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) ≤ Valued.v d) ∧
    ∃ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) = Valued.v d

def dV : Fv F v := if h : ∃ d, IsDiffVal v d then h.choose else 1

def alp (r : ℕ) (a : Fin (r + 1)) : Fv F v := if (a : ℕ) < r then (dV v)⁻¹ ^ (r - (a : ℕ)) else 1

def locZ {r : ℕ} (z : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) (i j : Fin (r + 1)) : Fv F v ⊗[F] E :=
  sc (E := E) v (alp v r i * alp v r j) * z (i, j)

end Frames

section Sets

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def ZZOrd (r : ℕ) : Set (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :=
  {z | ∀ i j, locZ v z i j ∈ OEv (E := E) v}

def ZZTyp (g r : ℕ) (TF TF' : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) :
    Set (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E) :=
  {z | ∀ i j, (locZ v z i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v ∧
    ((locZ v z i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹ +
        sigR (Fv F v) σ ((locZ v z j i - TF j i) * sc (E := E) v (g : Fv F v)⁻¹) -
        (TF' i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v}

def PPOrd (r : ℕ) (l : Fin (r + 1)) : Set (Fv F v ⊗[F] E) :=
  {c | sc (E := E) v (alp v r l ^ 2) * c ∈ OEv (E := E) v}

def PPTyp (g r T T' : ℕ) (l : Fin (r + 1)) : Set (Fv F v ⊗[F] E) :=
  if (l : ℕ) < r then
    {c | sc (E := E) v (alp v r l ^ 2 * (g : Fv F v)⁻¹) * c ∈ OEv (E := E) v ∧
      sc (E := E) v (alp v r l ^ 2 * ((g : Fv F v)⁻¹) ^ 2) * (c + sigR (Fv F v) σ c) ∈ OEv (E := E) v}
  else
    {c | sc (E := E) v (g : Fv F v)⁻¹ * (c + (T : Fv F v ⊗[F] E)) ∈ OEv (E := E) v ∧
      sc (E := E) v (((g : Fv F v)⁻¹) ^ 2) * (c + sigR (Fv F v) σ c + (T : Fv F v ⊗[F] E) + (T' : Fv F v ⊗[F] E))
        ∈ OEv (E := E) v}

abbrev UIdx (r : ℕ) : Type := {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2}

def UO (r : ℕ) : Set (UIdx r → Fv F v ⊗[F] E) :=
  {x | ∀ p, sc (E := E) v ((alp v r p.1.1)⁻¹ * alp v r p.1.2) * x p ∈ OEv (E := E) v}

def localVolumeOrdinary (r : ℕ) : Set ((UIdx r → Fv F v ⊗[F] E) × (UIdx r → Fv F v ⊗[F] E)) :=
  UO v r ×ˢ UO v r

def deepCongruenceVolume (g r : ℕ) : Set ((UIdx r → Fv F v ⊗[F] E) × (UIdx r → Fv F v ⊗[F] E)) :=
  {p | p.1 ∈ UO v r ∧ p.2 ∈ UO v r ∧ ∀ q,
    sc (E := E) v ((alp v r q.1.1)⁻¹ * alp v r q.1.2 * (g : Fv F v)⁻¹) * (p.1 q - p.2 q) ∈ OEv (E := E) v}

def volS {r : ℕ} (S : Set (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E)) : ℝ :=
  (sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) S).toReal

def volC (S : Set (Fv F v ⊗[F] E)) : ℝ :=
  (sdE (E := E) ψ v Unit ((fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' S)).toReal

def volU {r : ℕ} (S : Set ((UIdx r → Fv F v ⊗[F] E) × (UIdx r → Fv F v ⊗[F] E))) : ℝ :=
  (((sdE (E := E) ψ v (UIdx r)).prod (sdE (E := E) ψ v (UIdx r))) S).toReal

def absV (x : Fv F v) : ℝ :=
  if h : Valued.v x = 0 then 0
  else ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (Multiplicative.toAdd (WithZero.unzero h))

def jacS (typed : Prop) (g r : ℕ) : ℝ :=
  ∏ l : Fin r, ((absV v ((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)), alp v r i ^ 2) *
    (if typed then ((g : Fv F v)⁻¹) ^ ((l : ℕ) + 1) else 1))) ^ 2) ^ 2

end Sets

section Stmt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))

def LocJacTyp : Prop :=
  ∀ (typed : Prop) (g r T T' : ℕ) (TF TF' : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)),
    Module.finrank F E = 2 → σ ≠ AlgHom.id F E → typed → 0 < g →
    (∃ x : Fv F v ⊗[F] E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1) →
    TF ∈ HermR (Fv F v) σ (r + 1) → TF' ∈ HermR (Fv F v) σ (r + 1) →
    (∀ i j, (TF' i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v) →
    (g : ℤ) ∣ ((T : ℤ) - T') →
    volS (E := E) ψ v (ZZTyp σ v g r TF TF') * jacS v typed g r =
      volU (E := E) ψ v (deepCongruenceVolume v g r) * ∏ l : Fin (r + 1), volC (E := E) ψ v (PPTyp σ v g r T T' l)

end Stmt

end PI.LocJacTyp
end
end

-- bundled from Formalism.PeriodIntegrals.NormPullG
section
namespace PI

def NormPullG : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ (ψ : (T → I → J → ℂ) ≃ₗ[ℂ] (T → I → J → ℂ)), (∀ z w, HfG A (ψ z) (ψ w) = HfG A z w) →
    ∀ La₁ La₂ : AddSubgroup (T → I → J → ℂ), GoodLat s A La₁ → (∀ z, z ∈ La₂ ↔ ψ z ∈ La₁) →
      ∀ F ∈ ThSpG s A La₁, (fun z => F (ψ z)) ∈ ThSpG s A La₂ ∧ normSqG A La₂ (fun z => F (ψ z)) = normSqG A La₁ F

end PI
end

-- bundled from Formalism.PeriodIntegrals.NormTransG
section
namespace PI

def NormTransG : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ La' : AddSubgroup (T → I → J → ℂ), GoodLat s A La' → ∀ F ∈ ThSpG s A La', ∀ x : T → I → J → ℂ,
      normSqG A La' (UG A x F) = normSqG A La' F

end PI
end

-- bundled from Formalism.PeriodIntegrals.OmFibreUniq
section
noncomputable section

namespace PI.OmFibreUniq

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

abbrev TupV (n a : ℕ) : Type := Fin a → Fin n → Fv F v ⊗[F] E

def dX (a : ℕ) : Measure (TupV (E := E) v n a) :=
  if h : ∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ then h.choose else 0

def dT (a : ℕ) : Measure (HermR (Fv F v) σ a) :=
  if h : ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν then h.choose else 0

def IndepV (a : ℕ) : Set (TupV (E := E) v n a) := {X | LinearIndependent (Fv F v ⊗[F] E) X}

def IsOm (a : ℕ) (fib : HermR (Fv F v) σ a → Measure (TupV (E := E) v n a)) : Prop :=
  IsFibreFamily (dX σ J ψ v a) (gramR (Fv F v) σ J) Subtype.val (IndepV (E := E) (n := n) v a)
    (dT σ ψ v a) Set.univ fib

def IsStdChar (ψ : AddChar (AF F) ℂ) : Prop :=
  ∀ x : Ainf F, psiInf F ψ x =
    Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : NumberField.InfinitePlace F, (NumberField.InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))

def StdHyp : Prop := IsCMExt F E σ ∧ IsHermND σ J ∧ IsCharAF F ψ ∧ IsStdChar ψ

def OmUnique (a : ℕ) : Prop :=
  StdHyp σ J ψ → (∃ fib, IsOm σ J ψ v a fib) ∧ ∀ fib fib', IsOm σ J ψ v a fib → IsOm σ J ψ v a fib' → fib = fib'

end Meas

end PI.OmFibreUniq
end
end

-- bundled from Formalism.PeriodIntegrals.SelfDualBridge
section
noncomputable section

namespace PI.SelfDualBridge

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Classical

def SelfDualHaarExists : Prop :=
  ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [T2Space K],
    ¬ DiscreteTopology K →
  ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [TopologicalSpace V]
    [IsModuleTopology K V] [MeasurableSpace V] [BorelSpace V]
    (χ : AddChar K ℂ), Continuous χ → (∀ x, ‖χ x‖ = 1) → (∃ x, χ x ≠ 1) →
    ∀ B : V →ₗ[K] V →ₗ[K] K, (∀ x, (∀ y, B x y = 0) → x = 0) →
      ∃ μ : Measure V, SelfDual μ (fun x y => χ (B x y))

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def IsStdChar (ψ : AddChar (AF F) ℂ) : Prop :=
  ∀ x : Ainf F, psiInf F ψ x =
    Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : NumberField.InfinitePlace F, (NumberField.InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))

def StdHyp : Prop := IsCMExt F E σ ∧ IsHermND σ J ∧ IsCharAF F ψ ∧ IsStdChar ψ

def SdExists (a : ℕ) (ι : Type) [Fintype ι] : Prop :=
  StdHyp σ J ψ → (∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ) ∧ (∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν) ∧
  ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ
      (fun x y => psiV F ψ v (∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i)))

end Meas

end PI.SelfDualBridge
end
end

-- bundled from Formalism.PeriodIntegrals.SqPair
section
noncomputable section
open NumberField Matrix

namespace PI.SqPair

open Formalism.L2.PairingIndexBounds.Eq.SqG

def PLocal (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ)
    (L' L'' : Submodule (𝓞 E) (Fin N → E)) (n : 𝓞 E) (p : ℕ) : Prop :=
  ∃ e : Matrix (Fin N) (Fin N) E,
    (∀ y ∈ L', e *ᵥ y ∈ L') ∧ (∀ y ∈ L'', e *ᵥ y ∈ L'') ∧
    ∀ M ∈ ({e * e - e, eᴴ * e, (1 - e)ᴴ * (1 - e)} : Set (Matrix (Fin N) (Fin N) E)),
      ∀ y, (y ∈ L' ∨ y ∈ L'') →
        ∃ s : ℤ, ¬ (p : ℤ) ∣ s ∧ ∃ m, m ∈ L' ∧ m ∈ L'' ∧ (s : E) • (M *ᵥ y) = (n : E) • m

def PLocalAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ (N : ℕ) (L' L'' : Submodule (𝓞 E) (Fin N → E)), Even N → IsSDG E N L' → IsSDG E N L'' →
      ∀ n : 𝓞 E, n ≠ 0 → ∀ p : ℕ, p.Prime → PLocal E N L' L'' n p

def LocCartanPair : Prop :=
  ∀ (R : Type) [CommRing R] (σ : R ≃+* R), (∀ x, σ (σ x) = x) →
    ∀ (R₀ : Subring R), (∀ x, x ∈ R₀ ↔ σ x = x) →
    ∀ [IsDomain R₀] [IsDiscreteValuationRing R₀] [HenselianLocalRing R₀]
      [Finite (IsLocalRing.ResidueField R₀)],
    (∃ θ : R, IsUnit (θ - σ θ)) →
    ∀ ϖ : R₀, Irreducible ϖ →
    ∀ (N : ℕ), Even N → ∀ (k : ℕ) (h : Matrix (Fin N) (Fin N) R),
      (h.map σ)ᵀ * h = ((ϖ : R) ^ (2 * k)) • (1 : Matrix (Fin N) (Fin N) R) →
      ∃ e f : Matrix (Fin N) (Fin N) R, e * e = e ∧ (e.map σ)ᵀ = 1 - e ∧ e * h = h * f

end PI.SqPair
end
end

-- bundled from Formalism.PeriodIntegrals.StdCharTR
section
noncomputable section

open MeasureTheory NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PI.StdCharTR

def Target : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ ∧
    ∀ x : Ainf F, psiInf F ψ x =
      Complex.exp (2 * Real.pi * Complex.I *
        ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))

end PI.StdCharTR
end
end

-- bundled from Formalism.PeriodIntegrals.ThGExist
section
namespace PI

def ThGExist : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ La' : AddSubgroup (T → I → J → ℂ), GoodLat s A La' →
      ∃ G ∈ ThSpG s A La', G ≠ 0

end PI
end

-- bundled from Formalism.PeriodIntegrals.WPhDefs
section
namespace PI

namespace WPhDefs

section W

variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]

noncomputable def qG (s A : ℝ) (x : T → I → J → ℂ) : ℝ := s * (HfG A x x).re

noncomputable def wPhG (s A : ℝ) (p : ℕ) (x : T → I → J → ℂ) : ℂ :=
  if p = 2 then Complex.exp ((Real.pi : ℂ) * Complex.I * (qG s A x : ℂ))
  else Classical.epsilon (fun c : ℂ => ∃ (k : ℕ) (m : ℤ), (p : ℝ) ^ k * qG s A x = (m : ℝ) ∧ c = (-1 : ℂ) ^ m)

noncomputable def WopG (s A : ℝ) (p : ℕ) (x : T → I → J → ℂ) (G : (T → I → J → ℂ) → ℂ) : (T → I → J → ℂ) → ℂ :=
  fun z => wPhG s A p x * UG A x G z

noncomputable def kapG (A : ℝ) (x y : T → I → J → ℂ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((HfG A x y).im : ℂ))

def QIntLat (s A : ℝ) (La' : AddSubgroup (T → I → J → ℂ)) : Prop :=
  ∀ x ∈ La', (∃ m : ℤ, qG s A x = m) ∧ (x ≠ 0 → 1 ≤ qG s A x)

end W

end WPhDefs

end PI
end

