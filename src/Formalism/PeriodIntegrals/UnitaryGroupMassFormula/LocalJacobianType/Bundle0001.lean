import Mathlib
import Formalism.PeriodIntegrals.Bundle0019

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Development
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct Classical

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))

def Obox (ι : Type) : Set (ι → Fv F v ⊗[F] E) := Set.univ.pi fun _ => OEv (E := E) v

def SplitHyp : Prop :=
  Module.finrank F E = 2 ∧ σ ≠ AlgHom.id F E ∧ ∃ x : Fv F v ⊗[F] E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1

def SdNorm : Prop :=
  (∀ (ι : Type) [Fintype ι] [Nonempty ι], sdE (E := E) ψ v ι = 0) ∨
  ∃ m : ℝ, 0 < m ∧ ∀ (ι : Type) [Fintype ι], (sdE (E := E) ψ v ι).IsAddHaarMeasure ∧
    (sdE (E := E) ψ v ι (Obox (E := E) v ι)).toReal = m ^ Fintype.card ι

def VolZZ : Prop :=
  ∀ (g r : ℕ) (TF TF' : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E)) (m : ℝ),
    SplitHyp σ v → 0 < g → TF ∈ HermR (Fv F v) σ (r + 1) → TF' ∈ HermR (Fv F v) σ (r + 1) →
    (∀ i j, (TF' i j - TF i j) * sc (E := E) v (g : Fv F v)⁻¹ ∈ OEv (E := E) v) →
    ∀ μ : Measure (Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E), μ.IsAddHaarMeasure →
      (μ (Obox (E := E) v _)).toReal = m ^ ((r + 1) * (r + 1)) →
      (μ (ZZTyp σ v g r TF TF')).toReal =
        m ^ ((r + 1) * (r + 1)) * absV v (g : Fv F v) ^ (3 * ((r + 1) * (r + 1))) *
          ∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((absV v (alp v r i) * absV v (alp v r j)) ^ 2)⁻¹

def VolU : Prop :=
  ∀ (g r : ℕ) (m : ℝ), SplitHyp σ v → 0 < g →
    ∀ μ : Measure (UIdx r → Fv F v ⊗[F] E), μ.IsAddHaarMeasure →
      (μ (Obox (E := E) v _)).toReal = m ^ Fintype.card (UIdx r) →
      ((μ.prod μ) (deepCongruenceVolume (E := E) v g r)).toReal =
        ∏ q : UIdx r, (m ^ 2 * absV v (g : Fv F v) ^ 2 *
          (absV v (alp v r q.1.1) / absV v (alp v r q.1.2)) ^ 4)

def VolPP : Prop :=
  ∀ (g r T T' : ℕ) (m : ℝ), SplitHyp σ v → 0 < g → (g : ℤ) ∣ ((T : ℤ) - T') →
    ∀ μ : Measure (Unit → Fv F v ⊗[F] E), μ.IsAddHaarMeasure →
      (μ (Obox (E := E) v Unit)).toReal = m →
      ∀ l : Fin (r + 1),
        (μ ((fun c : Unit → Fv F v ⊗[F] E => c ()) ⁻¹' PPTyp σ v g r T T' l)).toReal =
          m * absV v (g : Fv F v) ^ 3 * (absV v (alp v r l) ^ 4)⁻¹

def Arith : Prop :=
  ∀ (typed : Prop) (g r : ℕ) (m : ℝ), typed → 0 < g →
    m ^ ((r + 1) * (r + 1)) * absV v (g : Fv F v) ^ (3 * ((r + 1) * (r + 1))) *
        (∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((absV v (alp v r i) * absV v (alp v r j)) ^ 2)⁻¹) *
        jacS v typed g r =
      (∏ q : UIdx r, (m ^ 2 * absV v (g : Fv F v) ^ 2 *
          (absV v (alp v r q.1.1) / absV v (alp v r q.1.2)) ^ 4)) *
        ∏ l : Fin (r + 1), (m * absV v (g : Fv F v) ^ 3 * (absV v (alp v r l) ^ 4)⁻¹)

end Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))

theorem locJacTyp_of (h0 : SdNorm (E := E) ψ v) (hZ : VolZZ σ v) (hU : VolU σ v)
    (hP : VolPP σ v) (hA : Arith (F := F) v) : PI.LocJacTyp.LocJacTyp σ ψ v := by
  intro typed g r T T' TF TF' hfin hσ ht hg hsplit hTF hTF' hdiff hT
  have hS : SplitHyp σ v := ⟨hfin, hσ, hsplit⟩
  rcases h0 with h0 | ⟨m, -, h0⟩
  · have h1 : sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) = 0 := h0 _
    have h2 : sdE (E := E) ψ v Unit = 0 := h0 _
    have h3 : ∏ l : Fin (r + 1), volC (E := E) ψ v (PPTyp σ v g r T T' l) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ 0) (by simp [volC, h2])
    simp [volS, h1, h3]
  · obtain ⟨hZH, hZv⟩ := h0 (Fin (r + 1) × Fin (r + 1))
    obtain ⟨hUH, hUv⟩ := h0 (UIdx r)
    obtain ⟨hCH, hCv⟩ := h0 Unit
    have hZv' : (sdE (E := E) ψ v (Fin (r + 1) × Fin (r + 1)) (Obox (E := E) v _)).toReal =
        m ^ ((r + 1) * (r + 1)) := by rw [hZv]; simp [Fintype.card_prod]
    have hCv' : (sdE (E := E) ψ v Unit (Obox (E := E) v Unit)).toReal = m := by rw [hCv]; simp
    have eZ := hZ g r TF TF' m hS hg hTF hTF' hdiff _ hZH hZv'
    have eU := hU g r m hS hg _ hUH hUv
    have eP := hP g r T T' m hS hg hT _ hCH hCv'
    unfold volS volU volC
    rw [eZ, eU]
    simp only [eP]
    exact hA typed g r m ht hg

end PI.UnitaryGroupMassFormula.LocJacTyp
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitAbs
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem q_pos : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero h

theorem absV_zero : absV v (0 : Fv F v) = 0 := by
  unfold absV
  simp

theorem absV_pos {x : Fv F v} (hx : x ≠ 0) : 0 < absV v x := by
  have h : Valued.v x ≠ 0 := by simpa using hx
  unfold absV
  rw [dif_neg h]
  exact zpow_pos (q_pos v) _

theorem absV_ne_zero {x : Fv F v} (hx : x ≠ 0) : absV v x ≠ 0 := (absV_pos v hx).ne'

theorem absV_mul (x y : Fv F v) : absV v (x * y) = absV v x * absV v y := by
  by_cases hx : x = 0
  · simp [hx, absV_zero]
  by_cases hy : y = 0
  · simp [hy, absV_zero]
  have h1 : Valued.v x ≠ 0 := by simpa using hx
  have h2 : Valued.v y ≠ 0 := by simpa using hy
  have h3 : Valued.v (x * y) ≠ 0 := by simpa using mul_ne_zero hx hy
  unfold absV
  rw [dif_neg h1, dif_neg h2, dif_neg h3, ← zpow_add₀ (q_pos v).ne', ← toAdd_mul]
  congr 2
  apply WithZero.coe_injective
  rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, WithZero.coe_unzero, map_mul]

theorem absV_one : absV v (1 : Fv F v) = 1 := by
  have h : Valued.v (1 : Fv F v) ≠ 0 := by simp
  unfold absV
  rw [dif_neg h]
  have h1 : WithZero.unzero h = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, map_one, WithZero.coe_one]
  rw [h1, toAdd_one, zpow_zero]

theorem absV_inv (x : Fv F v) : absV v x⁻¹ = (absV v x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx, absV_zero]
  have h := absV_mul v x x⁻¹
  rw [mul_inv_cancel₀ hx, absV_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem absV_pow (x : Fv F v) (n : ℕ) : absV v (x ^ n) = absV v x ^ n := by
  induction n with
  | zero => simp [absV_one]
  | succ n ih => rw [pow_succ, absV_mul, ih, pow_succ]

theorem absV_div (x y : Fv F v) : absV v (x / y) = absV v x / absV v y := by
  rw [div_eq_mul_inv, absV_mul, absV_inv, div_eq_mul_inv]

theorem dV_ne_zero : dV v ≠ 0 := by
  unfold dV
  split_ifs with h
  · exact h.choose_spec.1
  · exact one_ne_zero

theorem alp_ne_zero (r : ℕ) (a : Fin (r + 1)) : alp v r a ≠ 0 := by
  unfold alp
  split_ifs
  · exact pow_ne_zero _ (inv_ne_zero (dV_ne_zero v))
  · exact one_ne_zero

theorem alp_last (r : ℕ) : alp v r (Fin.last r) = 1 := by
  unfold alp
  simp

theorem natCast_ne_zero {g : ℕ} (hg : 0 < g) : (g : Fv F v) ≠ 0 := by
  intro h0
  have h1 : algebraMap F (Fv F v) (g : F) = algebraMap F (Fv F v) 0 := by
    rw [map_natCast, map_zero]
    exact h0
  exact (Nat.cast_ne_zero.2 hg.ne') ((algebraMap F (Fv F v)).injective h1)

end PI.UnitaryGroupMassFormula.LocJacTyp
end
end

