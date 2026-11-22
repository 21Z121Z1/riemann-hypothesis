import Formalism.PeriodIntegrals.Bundle0006
import Mathlib
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.Bundle0002
import Formalism.PeriodIntegrals.Bundle0011
import Formalism.PeriodIntegrals.Bundle0008
import Formalism.PeriodIntegrals.Bundle0001
import Formalism.PeriodIntegrals.Bundle0004

-- bundled from Formalism.PeriodIntegrals.AreaLat
section
open Classical

namespace PI

def AreaLat : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 →
    area (lat2 w₁ w₂) = |((starRingEnd ℂ) w₁ * w₂).im| ∧
    ∀ a ∈ lat2 w₁ w₂, ∀ b ∈ lat2 w₁ w₂, ∃ n : ℤ, ((starRingEnd ℂ) a * b).im = n * ((starRingEnd ℂ) w₁ * w₂).im

end PI
end

-- bundled from Formalism.PeriodIntegrals.BallQuotLen
section
namespace PI

open Formalism.MainNotions.Gaps.EtaleWeightGaps

def BallQuotLen : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [IsReduced A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A]
    (ϖ : O), Irreducible ϖ → Module.Finite O ↥(As O A) → ∀ [∀ ζ : Pts O A, IsDVRAt ζ],
    ∀ (V : Type) [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower K A V] [Module O V]
      [IsScalarTower O A V] (e : V), IsGen A e → ∀ (c : Pts O A → ℤ) (m : Pts O A → ℕ),
      Module.length O (↥(ballO ϖ e (fun ζ => c ζ + m ζ)) ⧸
          (ballO ϖ e c).comap (ballO ϖ e (fun ζ => c ζ + m ζ)).subtype) =
        ((∑ᶠ ζ : Pts O A, m ζ * fdeg ζ : ℕ) : ℕ∞)

end PI
end

-- bundled from Formalism.PeriodIntegrals.DSExist
section
noncomputable section

namespace PI

open PI.UpqRep

def DSExist : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), IsHCParam lam →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.DiscrNe
section
open Classical

namespace PI

def DiscrNe : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 → discr (lat2 w₁ w₂) ≠ 0

end PI
end

-- bundled from Formalism.PeriodIntegrals.EagonNorthcottSpec
section
noncomputable section

namespace PI

open EagonNorthcott in

def EagonNorthcottSpec.{u} : Prop :=
  ∀ (D a : ℕ) (n : ℕ → ℕ) (e : Fin (n 0) → Fin D → ℕ) (C : ∀ j, Matrix (Fin (n j)) (Fin (n (j + 1))) (Fin D → ℤ)),
    Resolves (MvPolynomial.X : Fin D → MvPolynomial (Fin D) ℤ) a e C →
      ∀ (R : Type u) [CommRing R] (x : Fin D → R),
        RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x) → Resolves x a e C

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.EagonNorthcottZ
section
noncomputable section

namespace PI

open EagonNorthcott in

def EagonNorthcottZ : Prop :=
  ∀ D a : ℕ, ∃ (n : ℕ → ℕ) (e : Fin (n 0) → Fin D → ℕ) (C : ∀ j, Matrix (Fin (n j)) (Fin (n (j + 1))) (Fin D → ℤ)),
    Shape D a n e C ∧ Resolves (MvPolynomial.X : Fin D → MvPolynomial (Fin D) ℤ) a e C

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.EfRankSum
section
namespace PI

open Formalism.MainNotions.Gaps.EtaleWeightGaps

def EfRankSum : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [IsReduced A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A]
    (ϖ : O), Irreducible ϖ → Module.Finite O ↥(As O A) → ∀ [∀ ζ : Pts O A, IsDVRAt ζ],
    Finite (Pts O A) ∧ (∑ᶠ ζ : Pts O A, ep ϖ ζ * fdeg ζ) = Module.finrank K A

end PI
end

-- bundled from Formalism.PeriodIntegrals.FinOrdAd
section
noncomputable section

namespace PI

open NumberField IsDedekindDomain TensorProduct Matrix ComplexOrder

section UnitaryGroups

variable {A : Type} [CommRing A] {ι : Type} [Fintype ι] [DecidableEq ι]

def cT (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ

def IsHerm (σ : A →+* A) (J : Matrix ι ι A) : Prop := cT σ J = J

def hform (σ : A →+* A) (J : Matrix ι ι A) (x y : ι → A) : A :=
  ∑ i, ∑ j, σ (x i) * J i j * y j

theorem cT_mul (σ : A →+* A) {m p q : Type} [Fintype p] (M : Matrix m p A) (N : Matrix p q A) :
    cT σ (M * N) = cT σ N * cT σ M := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one (σ : A →+* A) : cT σ (1 : Matrix ι ι A) = 1 := by
  simp [cT]

def UJ (σ : A →+* A) (J : Matrix ι ι A) : Subgroup (GL ι A) where
  carrier := {g | cT σ (g : Matrix ι ι A) * J * (g : Matrix ι ι A) = J}
  one_mem' := by simp [cT_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    calc cT σ ((a : Matrix ι ι A) * (b : Matrix ι ι A)) * J * ((a : Matrix ι ι A) * (b : Matrix ι ι A))
        = cT σ (b : Matrix ι ι A) * (cT σ (a : Matrix ι ι A) * J * (a : Matrix ι ι A)) *
            (b : Matrix ι ι A) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    calc cT σ ((g⁻¹ : GL ι A) : Matrix ι ι A) * J * ((g⁻¹ : GL ι A) : Matrix ι ι A)
        = cT σ ((g⁻¹ : GL ι A) : Matrix ι ι A) * (cT σ (g : Matrix ι ι A) * J * (g : Matrix ι ι A))
            * ((g⁻¹ : GL ι A) : Matrix ι ι A) := by rw [hg]
      _ = cT σ ((g : Matrix ι ι A) * ((g⁻¹ : GL ι A) : Matrix ι ι A)) * J
            * ((g : Matrix ι ι A) * ((g⁻¹ : GL ι A) : Matrix ι ι A)) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]

def bc {B : Type} [CommRing B] (φ : A →+* B) : GL ι A →* GL ι B :=
  Units.map (RingHom.mapMatrix φ).toMonoidHom

end UnitaryGroups

section Points

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {ι : Type} [Fintype ι] [DecidableEq ι]

def sigR (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] : E ⊗[F] R →+* E ⊗[F] R :=
  (Algebra.TensorProduct.map σ (AlgHom.id F R)).toRingHom

def inclE (R : Type) [CommRing R] [Algebra F R] : E →+* E ⊗[F] R :=
  Algebra.TensorProduct.includeLeftRingHom

def UPts (σ : E →ₐ[F] E) (J : Matrix ι ι E) (R : Type) [CommRing R] [Algebra F R] :
    Subgroup (GL ι (E ⊗[F] R)) := UJ (sigR σ R) (J.map (inclE (F := F) R))

def IsDef (σ : E →ₐ[F] E) (J : Matrix ι ι E) : Prop :=
  ∀ ι' : F →+* ℝ,
    (∀ x : ι → E, x ≠ 0 → ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x ∧ 0 < ι' a) ∨
    (∀ x : ι → E, x ≠ 0 → ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x ∧ ι' a < 0)

@[reducible] def tensTop (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (E ⊗[F] R) :=
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  moduleTopology R (E ⊗[F] R)

end Points

def FinOrdAd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
  (∀ φ : F →+* ℂ, ∃ r : F →+* ℝ, ∀ x, φ x = (r x : ℂ)) →
  ∀ (σ : E →ₐ[F] E) (k : ℕ) (J : Matrix (Fin k) (Fin k) E), IsHerm (σ : E →+* E) J → IsDef σ J →
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  ∀ U : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
    U ≤ UPts σ J (FiniteAdeleRing (𝓞 F) F) →
    IsCompact (U : Set (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) →
  ∀ y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F),
  ∀ γ ∈ UJ (σ : E →+* E) J,
    bc (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) γ ∈ U.map (MulAut.conj y).toMonoidHom →
    IsOfFinOrder γ

def DefPosDef : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
  (∀ φ : F →+* ℂ, ∃ r : F →+* ℝ, ∀ x, φ x = (r x : ℂ)) →
  ∀ (σ : E →ₐ[F] E) (k : ℕ) (J : Matrix (Fin k) (Fin k) E), 0 < k → IsHerm (σ : E →+* E) J → IsDef σ J →
    (∀ (φ : E →+* ℂ) (x : E), φ (σ x) = (starRingEnd ℂ) (φ x)) ∧
    (∀ φ : E →+* ℂ, (J.map φ).PosDef ∨ (-(J.map φ)).PosDef)

def TensCpctDen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  ∀ C : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F), IsCompact C →
    ∃ N : ℕ, 0 < N ∧ ∀ e : E, inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) e ∈ C → IsIntegral ℤ ((N : E) * e)

def CpctIntCharpoly : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ),
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  ∀ K : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
    IsCompact (K : Set (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) →
  ∀ γ : GL (Fin k) E, bc (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) γ ∈ K →
    ∀ i, IsIntegral ℤ ((γ : Matrix (Fin k) (Fin k) E).charpoly.coeff i)

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.HCFdeg
section
noncomputable section

namespace PI

open PI.UpqRep

def HCFdeg : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ →
      IsFdeg (muG ε) σ (c * fdegHC lam)

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.HCMult
section
noncomputable section

namespace PI

open PI.UpqRep

def HCMult : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S →
      FiniteDimensional ℂ (eqImg (fun k : KG ε => σ (toMK k)) S)

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.HeisMul
section
namespace PI

def HeisMul : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (A : ℝ) (x y : T → I → J → ℂ) (G : (T → I → J → ℂ) → ℂ),
    UG A x (UG A y G) =
      fun z => Complex.exp (-((Real.pi : ℂ) * Complex.I) * ((HfG A x y).im : ℂ)) * UG A (x + y) G z

end PI
end

-- bundled from Formalism.PeriodIntegrals.HeisNorm
section
namespace PI

def HeisNorm : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (A : ℝ) (x z : T → I → J → ℂ) (G : (T → I → J → ℂ) → ℂ),
    ‖UG A x G z‖ ^ 2 * Real.exp (-Real.pi * (HfG A z z).re) =
      ‖G (z + x)‖ ^ 2 * Real.exp (-Real.pi * (HfG A (z + x) (z + x)).re)

end PI
end

