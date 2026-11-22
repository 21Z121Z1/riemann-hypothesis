import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.Bundle0003

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.CardKill
section
open scoped TensorProduct
open GlobalTheory.TateLimit

theorem UpperTheory.V.K.cardKill :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] [Finite X] (c : ℕ) (Y : Submodule ℤ_[l] X), (∀ y ∈ Y, (l : ℤ_[l]) ^ c • y = 0) → Nat.card Y ≤ Nat.card (X ⧸ lpow l X 1) ^ c := by
  intro l _ X _ _ _ c Y hY
  refine le_trans ?_ (UpperTheory.V.K.cardQuotPow l X c)
  let f : X →ₗ[ℤ_[l]] X := LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ c)
  have hr : lpow l X c = LinearMap.range f := rfl
  have hYk : Y ≤ LinearMap.ker f := fun y hy => hY y hy
  have h1 : Nat.card Y ≤ Nat.card (LinearMap.ker f) :=
    Nat.card_le_card_of_injective (Submodule.inclusion hYk) (Submodule.inclusion_injective hYk)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h3 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  have h4 : Nat.card (X ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  rw [hr]
  refine h1.trans (le_of_eq (Nat.eq_of_mul_eq_mul_left hpos ?_))
  rw [h4] at h2
  rw [← h3, h2, mul_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.TensCard
section
open scoped TensorProduct
open GlobalTheory.TateLimit

theorem UpperTheory.V.K.tensCard :
    ∀ (l : ℕ) [Fact l.Prime] (H : Type) [AddCommGroup H] [Finite (AddCommGroup.torsion H)] (Y : Submodule ℤ_[l] (ℤ_[l] ⊗[ℤ] H)) [Finite Y], Nat.card Y ≤ Nat.card (AddCommGroup.torsion H) := by
  intro l _ H _ _ Y _
  have hT : AddMonoid.IsTorsion (AddCommGroup.torsion H) := fun t => isOfFinAddOrder_of_finite t
  have key : ∀ y : Y, ∃ t : AddCommGroup.torsion H,
      ((1 : ℤ_[l]) ⊗ₜ[ℤ] (t : H) : ℤ_[l] ⊗[ℤ] H) = (y : ℤ_[l] ⊗[ℤ] H) := by
    intro y
    have hy : IsOfFinAddOrder (y : ℤ_[l] ⊗[ℤ] H) := by
      obtain ⟨n, hn, hny⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (isOfFinAddOrder_of_finite y)
      refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
      have := congrArg Y.subtype hny
      rw [map_nsmul, map_zero] at this
      exact this
    obtain ⟨z, hz⟩ := UpperTheory.V.K.tensTors l H _ hy
    obtain ⟨t, rfl⟩ := UpperTheory.V.K.tensSurj l _ hT z
    refine ⟨t, ?_⟩
    rw [← hz, LinearMap.lTensor_tmul]
    rfl
  choose f hf using key
  refine Nat.card_le_card_of_injective f ?_
  intro a b hab
  apply Subtype.ext
  rw [← hf a, ← hf b, hab]
end

