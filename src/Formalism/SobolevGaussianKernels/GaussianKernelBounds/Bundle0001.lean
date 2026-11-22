import Mathlib
import Formalism.SobolevGaussianKernels.Bundle0001

-- bundled from Formalism.SobolevGaussianKernels.GaussianKernelBounds.EichlerEquivalenceHolds
section
set_option linter.unusedSimpArgs false

namespace Formalism.SL.P

open Formalism.SL.IwahoriBlocks
theorem eichler_isometry_holds : Formalism.SL.IwahoriBlocks.EichIsom := by
  intro E _ _ V _ _ h x u s hH hxx hux hs v w
  have hxu : h x u = 0 := by rw [hH, hux, star_zero]
  have hxw : h x w = star (h w x) := hH w x
  have huw : h u w = star (h w u) := hH w u
  have hxv : h x v = star (h v x) := hH v x
  have huv : h u v = star (h v u) := hH v u
  simp only [eich, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.map_smul,
    LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hxx, hux, hxu, hxw, huw, starRingEnd_apply, star_add, star_sub, star_mul', star_star, mul_zero, add_zero, sub_zero]
  rw [← hs]
  ring

theorem eichler_move_holds : Formalism.SL.IwahoriBlocks.EichMove := by
  intro E _ _ V _ _ h x x' u s hH hux hux' v hv
  have hx'u : h x' u = 0 := by rw [hH, hux', star_zero]
  simp only [eich, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.map_smul,
    LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hv, hx'u, mul_zero, add_zero, sub_zero, zero_smul, zero_mul, smul_zero]
  module

theorem eichler_composition_holds : Formalism.SL.IwahoriBlocks.EichComp := by
  intro E _ _ V _ _ h x a b s t hH hxx hax hbx v
  have hxa : h x a = 0 := by rw [hH, hax, star_zero]
  simp only [eich, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hxx, hax, hbx, hxa, mul_zero, zero_mul, add_zero, sub_zero, zero_smul, smul_zero]
  module

theorem eichler_inverse_holds : Formalism.SL.IwahoriBlocks.EichInv := by
  have hc := eichler_composition_holds
  intro E _ _ V _ _ h x u s hH hxx hux hs v
  have hnx : h (-u) x = 0 := by simp [hux]
  refine ⟨?_, ?_⟩
  · rw [hc E V h x (-u) u (star s) s hH hxx hnx hux]
    have : star s + s + h u (-u) = 0 := by
      rw [map_neg, ← hs]; ring
    have h2 : star s + s + -(h u) u = 0 := by rw [← hs]; ring
    simp [eich, h2]
  · rw [hc E V h x u (-u) s (star s) hH hxx hux hnx]
    have : s + star s + h (-u) u = 0 := by
      rw [LinearMap.map_neg, LinearMap.neg_apply, ← hs]; ring
    have h2 : s + star s + -(h u) u = 0 := by rw [← hs]; ring
    simp [eich, h2]

theorem eichler_integrality_holds : Formalism.SL.IwahoriBlocks.EichInt := by
  intro E _ _ V _ _ h O abelian₂ x x' u s hH hO hint hu hb hsx hx'x hux hux' v hv hvx'
  have hx'u : h x' u = 0 := by rw [hH, hux', star_zero]
  have hvx : h v x = h v (x + x') := by simp [hvx']
  have key : eich h x u s (eich h x' u s v) = v + h v u • (x + x') - (h v x + h v u * h x' x) • (u + s • x) := by
    simp only [eich, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.map_smul,
      LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hvx', hx'u, mul_zero, add_zero, sub_zero, zero_smul, zero_mul, smul_zero]
    module
  rw [key]
  have hvu := hint v hv u hu
  have hk : h v x + h v u * h x' x ∈ O := O.add_mem (hvx ▸ hint v hv _ hb) (O.mul_mem hvu hx'x)
  exact abelian₂.sub_mem (abelian₂.add_mem hv (hO _ hvu _ hb)) (hO _ hk _ (abelian₂.add_mem hu hsx))

end Formalism.SL.P
end

-- bundled from Formalism.SobolevGaussianKernels.GaussianKernelBounds.HasDerivAtSphereChartLast
section
namespace Formalism.SL.P

open MeasureTheory Formalism.SL.SB
open scoped ContDiff

namespace SphereChartDerivatives

variable {n : ℕ}

def sn (t : ℝ) (y : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) y t

@[simp] lemma sn_last (t : ℝ) (y : Fin n → ℝ) : sn t y (Fin.last n) = t := by simp [sn]
@[simp] lemma sn_cast (t : ℝ) (y : Fin n → ℝ) (k : Fin n) : sn t y (Fin.castSucc k) = y k := by
  simp [sn]

noncomputable def snocL (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi (fun j => if h : j = Fin.last n then 0
    else ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (j.castPred h))

lemma sum_split (f : Finset (Fin (n + 1)) → ℝ) :
    ∑ α : Finset (Fin (n + 1)), f α =
      ∑ β : Finset (Fin n), f (β.map Fin.castSuccEmb) +
        ∑ β : Finset (Fin n), f (insert (Fin.last n) (β.map Fin.castSuccEmb)) := by
  have hnot : Fin.last n ∉ (Finset.univ : Finset (Fin n)).map Fin.castSuccEmb := by
    simp [Fin.castSucc_ne_last]
  have hu : (Finset.univ : Finset (Finset (Fin (n + 1)))) =
      (insert (Fin.last n) ((Finset.univ : Finset (Fin n)).map Fin.castSuccEmb)).powerset := by
    rw [← Finset.cons_eq_insert _ _ hnot, ← Fin.univ_castSuccEmb, Finset.powerset_univ]
  rw [hu, Finset.sum_powerset_insert hnot]
  have key : ∀ h : Finset (Fin (n + 1)) → ℝ,
      ∑ t ∈ ((Finset.univ : Finset (Fin n)).map Fin.castSuccEmb).powerset, h t =
        ∑ β : Finset (Fin n), h (β.map Fin.castSuccEmb) := by
    intro h
    symm
    apply Finset.sum_nbij' (fun β => β.map Fin.castSuccEmb)
      (fun α => Finset.univ.filter (fun k => Fin.castSucc k ∈ α))
    · intro β _
      simp [Finset.map_subset_map]
    · intro α _
      simp
    · intro β _
      ext k
      simp
    · intro α hα
      rw [Finset.mem_powerset] at hα
      ext x
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.coe_castSuccEmb]
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact hk
      · intro hx
        obtain ⟨k, -, rfl⟩ := Finset.mem_map.1 (hα hx)
        exact ⟨k, hx, rfl⟩
    · intro β _
      rfl
  rw [key, key (fun t => f (insert (Fin.last n) t))]

noncomputable def SS {m : ℕ} (δ : ℝ) (g : (Fin m → ℝ) → ℂ) (y : Fin m → ℝ) : ℝ :=
  ∑ α : Finset (Fin m), δ ^ (2 * α.card) * ‖mixed α g y‖ ^ 2

end SphereChartDerivatives

end Formalism.SL.P
end

-- bundled from Formalism.SobolevGaussianKernels.GaussianKernelBounds.LfProd
section
namespace Formalism.SL.P

open scoped NumberField nonZeroDivisors
open NumberField InfinitePlace Finset

theorem primes_over_holds : Formalism.SL.LF.PrimesOver := by
  intro K _ _ p hp
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hqmax : q.IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hq0 : q ≠ ⊥ := by
    simp only [q, ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hset : {P : Ideal (𝓞 K) | P.IsPrime ∧ ((p : ℤ) : 𝓞 K) ∈ P} = q.primesOver (𝓞 K) := by
    ext P
    simp only [Set.mem_ofPred_eq, Ideal.primesOver]
    constructor
    · rintro ⟨hP, hpP⟩
      refine ⟨hP, ⟨?_⟩⟩
      refine hqmax.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P
      simpa using hpP
    · rintro ⟨hP, hlo⟩
      refine ⟨hP, ?_⟩
      have hmem : (p : ℤ) ∈ P.under ℤ := by
        rw [← hlo.over]
        exact Ideal.subset_span (Set.mem_singleton _)
      have : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P := hmem
      simpa using this
  rw [hset, ← IsDedekindDomain.coe_primesOverFinset hq0 (𝓞 K)]
  refine ⟨Finset.finite_toSet _, ?_⟩
  rw [Set.ncard_coe_finset]
  exact Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hq0

end Formalism.SL.P
end

