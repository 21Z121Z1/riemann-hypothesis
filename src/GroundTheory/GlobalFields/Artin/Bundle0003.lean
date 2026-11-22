import Mathlib
import GroundTheory.GlobalFields.Artin.Bundle0001
import GroundTheory.GlobalFields.Artin.PlacesGalois
import GroundTheory.GlobalFields.Artin.Bundle0002

-- bundled from GroundTheory.GlobalFields.Artin.GammaInduction
section
set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise
open NumberField NumberField.InfinitePlace IntermediateField Module GroundTheory.LocalField _root_.Complex

namespace GroundTheory.Global.Artin

section IndFun

variable {Γ Δ : Type*} [Group Γ] [Group Δ] [Fintype Γ] [Fintype Δ]

theorem indFun_mulEquiv (e : Γ ≃* Δ) {ψ : Γ → ℂ} (hψ : IsClassFun ψ) :
    indFun e.toMonoidHom ψ = ψ ∘ e.symm := by
  classical
  funext s
  rw [indFun_apply]
  have h1 : ∀ t : Δ, (∑ h : Γ, if e.toMonoidHom h = t⁻¹ * s * t then ψ h else 0) =
      ψ (e.symm s) := by
    intro t
    rw [Finset.sum_eq_single (e.symm (t⁻¹ * s * t))]
    · rw [if_pos (by simp), map_mul, map_mul, map_inv]
      have := hψ (e.symm s) (e.symm t)⁻¹
      rwa [inv_inv] at this
    · intro h _ hh
      rw [if_neg]
      intro h'
      apply hh
      rw [← h']
      simp
    · simp
  simp_rw [h1]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Function.comp_apply]
  have : (Fintype.card Δ : ℂ) = Nat.card Γ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_congr e.toEquiv]
  rw [this, inv_mul_cancel_left₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne')]

end IndFun

section Stabilizer

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

end Stabilizer

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))

section Conj

end Conj

section Mackey

variable (w : InfinitePlace L)

end Mackey

section Character

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ Gal(L/fixedField H) V)

def charOnSubgroup (h : H) : ℂ :=
  ρ.character (fixedFieldMulEquiv H h)

omit [IsGalois K L] in
open Classical in

theorem character_ind_restrictScalarsHom :
    (ρ.ind (AlgEquiv.restrictScalarsHom K)).character = indFun H.subtype (charOnSubgroup H ρ) := by
  rw [character_ind]
  have hφ : (AlgEquiv.restrictScalarsHom K : Gal(L/fixedField H) →* Gal(L/K)) =
      H.subtype.comp (fixedFieldMulEquiv H).symm.toMonoidHom := MonoidHom.ext fun _ ↦ rfl
  rw [hφ, ← indFun_indFun, indFun_mulEquiv (fixedFieldMulEquiv H).symm
    (isCharacter_character ρ).isClassFun]
  rfl

end Character

section Gamma

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ Gal(L/fixedField H) V)

end Gamma

end GroundTheory.Global.Artin
end
end

-- bundled from GroundTheory.GlobalFields.Artin.InductionFrobenius
section
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField IsDedekindDomain
open scoped Pointwise

namespace GroundTheory.Global.Artin

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem zpowers_arithFrob_eq_top (w : HeightOneSpectrum (𝓞 L)) {φ : Gal(L/K)}
    (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal) :
    Subgroup.zpowers ((⟨φ, hφ.mem_stabilizer⟩ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
      MulAction.stabilizer Gal(L/K) w.asIdeal ⧸
        (w.asIdeal.inertia Gal(L/K)).subgroupOf (MulAction.stabilizer Gal(L/K) w.asIdeal)) =
      ⊤ := by
  classical
  set Q := w.asIdeal with hQ
  set P := Q.under (𝓞 K) with hP
  have : Q.IsMaximal := w.isMaximal
  have : P.IsMaximal := by rw [hP]; infer_instance
  let _ : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  let _ : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q
  have : Finite (𝓞 K ⧸ P) := hφ.finite_quotient
  have := Fintype.ofFinite (𝓞 K ⧸ P)
  have : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q w.ne_bot
  set e := Ideal.Quotient.stabilizerHom Q P Gal(L/K)
  have hfrob : e ⟨φ, hφ.mem_stabilizer⟩ =
      FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 K ⧸ P) (𝓞 L ⧸ Q) := by
    ext y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    change Ideal.Quotient.mk Q (φ • y) = Ideal.Quotient.mk Q y ^ Fintype.card (𝓞 K ⧸ P)
    rw [← Nat.card_eq_fintype_card]
    exact hφ.mk_apply y
  rw [eq_top_iff]
  rintro c -
  induction c using QuotientGroup.induction_on with | H d => ?_
  obtain ⟨n, hn⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (𝓞 K ⧸ P) (𝓞 L ⧸ Q)).2 (e d)
  refine Subgroup.mem_zpowers_iff.2 ⟨(n.1 : ℤ), ?_⟩
  have hk : ((⟨φ, hφ.mem_stabilizer⟩ : MulAction.stabilizer Gal(L/K) Q) ^ n.1)⁻¹ * d ∈ e.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hfrob, ← hn, inv_mul_cancel]
  rw [Ideal.Quotient.ker_stabilizerHom, ← Ideal.coe_mem_inertia] at hk
  rw [zpow_natCast, ← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  exact hk

end GroundTheory.Global.Artin
end
end

