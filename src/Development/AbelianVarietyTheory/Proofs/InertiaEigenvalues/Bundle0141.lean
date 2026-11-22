import Mathlib
import GroundTheory.LocalFields.UnramifiedNormSurj
import GroundTheory.LocalFields.UnramifiedGalois
import Formalism.LocalToGlobal.NormalizedHeckeFactors.ExpDefs

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticUniformizerTraceNorm
section
open ValuativeRel

namespace GlobalTheory

open GroundTheory.LocalField IsLocalRing in

theorem unramified_quadratic_uniformizer_trace_norm : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L], GroundTheory.LocalField.ramificationIndex K L = 1 → Module.finrank K L = 2 → ∃ ϖ : K, ϖ ≠ 0 ∧ ϖ ≤ᵥ 1 ∧ ¬ (1 : K) ≤ᵥ ϖ ∧ (¬ ∃ y : L, Algebra.norm K y = ϖ) ∧ (∀ y : L, y ≤ᵥ 1 → (∃ z : L, z ≤ᵥ 1 ∧ y = algebraMap K L ϖ * z) ∨ ∃ z : L, z ≤ᵥ 1 ∧ y * z = 1) ∧ (∀ s : K, s ≤ᵥ 1 → ∃ z : L, z ≤ᵥ 1 ∧ Algebra.trace K L z = s) ∧ ∀ s : K, s ≤ᵥ 1 → 1 ≤ᵥ s → ∃ w : L, w ≤ᵥ 1 ∧ Algebra.norm K w = s := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ he h2
  haveI : IsUnramified K L := ⟨he⟩
  have memK : ∀ x : K, x ∈ 𝒪[K] ↔ x ≤ᵥ 1 := fun x ↦ by
    rw [Valuation.mem_integer_iff, ← map_one (ValuativeRel.valuation K), ← Valuation.vle_iff_le]
  have memL : ∀ x : L, x ∈ 𝒪[L] ↔ x ≤ᵥ 1 := fun x ↦ by
    rw [Valuation.mem_integer_iff, ← map_one (ValuativeRel.valuation L), ← Valuation.vle_iff_le]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  refine ⟨(ϖ : K), hϖ0, (memK _).1 ϖ.2, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro h1
    have hv : ValuativeRel.valuation K (ϖ : K) = 1 :=
      le_antisymm ((Valuation.vle_iff_le _).1 ((memK _).1 ϖ.2) |>.trans_eq (map_one _))
        ((map_one (ValuativeRel.valuation K)).symm.trans_le ((Valuation.vle_iff_le _).1 h1))
    exact hϖ.not_isUnit ((Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 hv)
  ·
    rintro ⟨y, hy⟩
    have h := ord_norm (K := K) y
    rw [hy, ord_uniformizer hϖ, IsUnramified.residueDegree_eq_finrank K L, h2] at h
    omega
  ·
    intro y hy
    have hπ := irreducible_algebraMap_of_isUnramified (L := L) hϖ
    set y' : 𝒪[L] := ⟨y, (memL y).2 hy⟩
    by_cases hu : IsUnit y'
    · right
      refine ⟨((hu.unit⁻¹ : 𝒪[L]ˣ) : 𝒪[L]), (memL _).1 (hu.unit⁻¹ : 𝒪[L]ˣ).1.2, ?_⟩
      have h := hu.unit.mul_inv
      rw [IsUnit.unit_spec] at h
      have := congrArg (fun u : 𝒪[L] ↦ (u : L)) h
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
      exact this
    · left
      have hm : y' ∈ maximalIdeal 𝒪[L] := (mem_maximalIdeal y').2 hu
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
      obtain ⟨c, hc⟩ := hm
      refine ⟨(c : L), (memL _).1 c.2, ?_⟩
      have := congrArg (fun u : 𝒪[L] ↦ (u : L)) hc
      simp only [y', MulMemClass.coe_mul, coe_algebraMap_integer] at this
      exact this
  ·
    intro s hs
    obtain ⟨a, ha⟩ := trace_integer_surjective (K := K) (L := L) ⟨s, (memK s).2 hs⟩
    refine ⟨(a : L), (memL _).1 a.2, ?_⟩
    rw [← coe_trace_integer, ha]
  ·
    intro s hs1 hs2
    set s' : 𝒪[K] := ⟨s, (memK s).2 hs1⟩
    have hv : ValuativeRel.valuation K s = 1 :=
      le_antisymm ((Valuation.vle_iff_le _).1 hs1 |>.trans_eq (map_one _))
        ((map_one (ValuativeRel.valuation K)).symm.trans_le ((Valuation.vle_iff_le _).1 hs2))
    have hu : IsUnit s' := (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 hv
    obtain ⟨w, hw⟩ := normIntegerUnits_surjective (K := K) (L := L) hu.unit
    refine ⟨((w : 𝒪[L]) : L), (memL _).1 (w : 𝒪[L]).2, ?_⟩
    have := congrArg (fun u : 𝒪[K]ˣ ↦ ((u : 𝒪[K]) : K)) hw
    simp only [coe_normIntegerUnits_eq, IsUnit.unit_spec] at this
    rw [← coe_norm_integer]
    exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UupEqOneOfLeOne
section
noncomputable section

namespace GlobalTheory.MeetsGen

def pU {K G : Type} [Field K] [Group G] (U : Subgroup G) [Fintype U] (f : U → K) : MonoidAlgebra K G :=
  ∑ u : U, MonoidAlgebra.single (u : G) ((Fintype.card U : K)⁻¹ * f u)

def cU {K G : Type} [Field K] [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (f : U → K) : MonoidAlgebra K G :=
  ∑ g : G, MonoidAlgebra.single g (1 : K) * pU U f * MonoidAlgebra.single g⁻¹ (1 : K)

def uElt {K G : Type} [Field K] [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (f : U → K) (e : MonoidAlgebra K G) :
    MonoidAlgebra K G :=
  cU U f * e + (1 - e)

theorem uup_eq_one_of_le_one {ι : Type} [Fintype ι] (p : ι → ℕ) (r : ℕ) (hr : r ≤ 1) (u : Formalism.L2.NX.GProd p r)
    (hu : u ∈ Formalism.L2.NX.Uup p r) : u = 1 := by
  funext x
  apply Units.ext
  ext a c
  have ha : a = c := Fin.ext (by have := a.2; have := c.2; omega)
  subst ha
  simp only [Pi.one_apply, Units.val_one, Matrix.one_apply_eq]
  exact ((Formalism.L2.NX.mem_Uup).1 hu x).2 a

theorem map_uElt {E L G : Type} [Field E] [Field L] [Group G] [Fintype G] (j : E →+* L) (U : Subgroup G) [Fintype U]
    (f : U → E) (e : MonoidAlgebra E G) :
    MonoidAlgebra.mapRingHom G j (uElt U f e) = uElt U (fun u => j (f u)) (MonoidAlgebra.mapRingHom G j e) := by
  simp only [uElt, cU, pU, map_add, map_mul, map_sub, map_one, map_sum, MonoidAlgebra.mapRingHom_single, map_inv₀,
    map_natCast]

theorem eq_sum_of_uElt_mul {K G : Type} [Field K] [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (f : U → K)
    (e v : MonoidAlgebra K G) (hI : e * e = e) (hC : ∀ a, e * a = a * e) (hv : uElt U f e * v = 1) :
    e = ∑ g : G, MonoidAlgebra.single g (1 : K) * pU U f * (MonoidAlgebra.single g⁻¹ (1 : K) * e * v) := by
  have h1 : e * uElt U f e = cU U f * e := by
    simp only [uElt]
    rw [mul_add, mul_sub, mul_one, hI, sub_self, add_zero, ← mul_assoc, hC (cU U f), mul_assoc, hI]
  calc e = e * (uElt U f e * v) := by rw [hv, mul_one]
    _ = cU U f * e * v := by rw [← mul_assoc, h1]
    _ = _ := by
      simp only [cU, Finset.sum_mul]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [mul_assoc]

end GlobalTheory.MeetsGen

end
end

