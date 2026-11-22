import Formalism.CharacterColumnKernels.Bundle0004
import Formalism.CharacterColumnKernels.IdempotentNormalForms.Bundle0003
import Formalism.CharacterColumnKernels.Bundle0003
import Formalism.CharacterColumnKernels.IdempotentNormalForms.GlobalConcreteOf
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthQuotSmulRangeFree

-- bundled from Formalism.CharacterColumnKernels.IdempotentNormalForms.SmulEqZeroIffCrit
section
open Classical

noncomputable section

namespace Formalism.NG

namespace IdempotentCriticalLength

variable {O Λ : Type*} [CommRing O] [IsLocalRing O] [Ring Λ] [Algebra O Λ]

lemma jac_smul {V : Type*} [AddCommGroup V] [Module Λ V] [IsSimpleModule Λ V]
    {a : Λ} (ha : a ∈ Ring.jacobson Λ) (w : V) : a • w = 0 :=
  Module.mem_annihilator.mp (IsSemisimpleModule.jacobson_le_annihilator (R := Λ) (M := V) ha) w

def Crit (O : Type*) [CommRing O] [IsLocalRing O] [Algebra O Λ] (ε x : Λ) : Prop :=
  ∀ y : Λ, ∀ c : O, ε * (y * x) * ε - algebraMap O Λ c * ε ∈ Ring.jacobson Λ →
    c ∈ IsLocalRing.maximalIdeal O

lemma smul_eq_zero_iff_crit {V : Type*} [AddCommGroup V] [Module Λ V] [IsSimpleModule Λ V]
    {ε : Λ} (hii : ∀ x : Λ, ∃ c : O, ε * x * ε - algebraMap O Λ c * ε ∈ Ring.jacobson Λ)
    (hiii : ∀ c ∈ IsLocalRing.maximalIdeal O, algebraMap O Λ c ∈ Ring.jacobson Λ)
    {v : V} (hv0 : v ≠ 0) (hv : ε • v = v) (x : Λ) :
    x • v = 0 ↔ Crit O ε x := by
  have e2 : ∀ c : O, (algebraMap O Λ c * ε) • v = algebraMap O Λ c • v := by
    intro c; rw [mul_smul, hv]
  constructor
  · intro hx y c hc
    have h1 := jac_smul hc v
    have e1 : (ε * (y * x) * ε) • v = 0 := by
      rw [mul_smul, hv, mul_smul, mul_smul, hx, smul_zero, smul_zero]
    rw [sub_smul, e1, e2, zero_sub, neg_eq_zero] at h1
    by_contra hcm
    have hu : IsUnit c := by
      by_contra hu'
      exact hcm hu'
    exact hv0 (((hu.map (algebraMap O Λ)).smul_eq_zero).mp h1)
  · intro hc
    by_contra hx
    obtain ⟨y, hy⟩ := (IsSimpleModule.toSpanSingleton_surjective Λ hx) v
    rw [LinearMap.toSpanSingleton_apply] at hy
    obtain ⟨c, hc'⟩ := hii (y * x)
    have h1 := jac_smul hc' v
    have e1 : (ε * (y * x) * ε) • v = v := by
      rw [mul_smul, hv, mul_smul, mul_smul, hy, hv]
    rw [sub_smul, e1, e2, sub_eq_zero, jac_smul (hiii c (hc y c hc')) v] at h1
    exact hv0 h1

lemma nonempty_equiv {V W : Type*} [AddCommGroup V] [Module Λ V] [IsSimpleModule Λ V]
    [AddCommGroup W] [Module Λ W] [IsSimpleModule Λ W] {ε : Λ} (hε : IsIdempotentElem ε)
    (hii : ∀ x : Λ, ∃ c : O, ε * x * ε - algebraMap O Λ c * ε ∈ Ring.jacobson Λ)
    (hiii : ∀ c ∈ IsLocalRing.maximalIdeal O, algebraMap O Λ c ∈ Ring.jacobson Λ)
    (hV : ∃ t : V, ε • t ≠ 0) (hW : ∃ s : W, ε • s ≠ 0) : Nonempty (V ≃ₗ[Λ] W) := by
  obtain ⟨t, ht⟩ := hV
  obtain ⟨s, hs⟩ := hW
  have hv : ε • (ε • t) = ε • t := by rw [← mul_smul, hε.eq]
  have hu : ε • (ε • s) = ε • s := by rw [← mul_smul, hε.eq]
  have hker : LinearMap.ker (LinearMap.toSpanSingleton Λ V (ε • t)) =
      LinearMap.ker (LinearMap.toSpanSingleton Λ W (ε • s)) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    rw [smul_eq_zero_iff_crit hii hiii ht hv, smul_eq_zero_iff_crit hii hiii hs hu]
  exact ⟨(LinearMap.quotKerEquivOfSurjective _
      (IsSimpleModule.toSpanSingleton_surjective Λ ht)).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans
      (LinearMap.quotKerEquivOfSurjective _ (IsSimpleModule.toSpanSingleton_surjective Λ hs)))⟩

end IdempotentCriticalLength

namespace IdempotentCriticalLengthFinite

variable {O Λ : Type*} [CommRing O] [IsLocalRing O] [Ring Λ] [Algebra O Λ]

end IdempotentCriticalLengthFinite

end Formalism.NG
end
end

-- bundled from Formalism.CharacterColumnKernels.IdempotentNormalForms.SumIteLe
section
open Finset

noncomputable section

namespace Formalism.NG

lemma sum_ite_le (t : ℕ) (vhE : ℕ∞) (Sha : ℕ → ℕ∞) :
    ∑ i ∈ range t, (if i + 1 = 1 then vhE else Sha (i + 1 - 1)) ≤
      vhE + ∑ e ∈ Ioo 0 t, Sha e := by
  rcases t with _ | n
  · simp
  · have hs : Ioo 0 (n + 1) = (range n).map ⟨(· + 1), add_left_injective 1⟩ := by
      ext e
      simp only [mem_Ioo, mem_map, mem_range, Function.Embedding.coeFn_mk]
      constructor
      · intro h
        exact ⟨e - 1, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨by omega, by omega⟩
    rw [hs, Finset.sum_map, Finset.sum_range_succ', add_comm]
    refine add_le_add (le_of_eq (if_pos rfl)) (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    show (if i + 1 + 1 = 1 then vhE else Sha (i + 1 + 1 - 1)) = Sha (i + 1)
    exact (if_neg (by omega)).trans (congrArg Sha (by omega))

theorem nGlobal : StatNGlobal := by
  intro O _ _ _ X X' T T' Z p q b hT hZ d _ _ R' m g _ _ _ P hdet hφ π' ρπ hρπ t bl hbl ρk hsurj
    hblk hcard ℓ what₂ cols Q lenRow e' j vδ h0 s Sha vhE cB deg H0 vζ eO h0b hcb
  classical
  have hG := globalConcrete O X X' T T' Z p q b hT hZ d R' m g P hdet hφ π' ρπ hρπ (Fin (t + 1)) bl
    hbl ρk hsurj hblk hcard
  refine hG.trans ((Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans ?_)
  rw [Fin.sum_univ_succ]
  have hsucc : ∑ c : Fin t, Module.length O (LinearMap.ker (relMap O (KO O) (bigRect (ρk c.succ) P))) ≤
      ∑ c : Fin t, ((if (c : ℕ) + 1 = 1 then vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ)
          else Sha ((c : ℕ) + 1 - 1)) +
        (eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
          (cols.card : ℕ∞) * H0 + ∑ z ∈ Q, vζ z)) := by
    refine Finset.sum_le_sum fun c _ => ?_
    have h := hcb c.succ (Fin.succ_ne_zero c)
    rw [Fin.val_succ] at h
    refine h.trans (le_of_eq ?_)
    ring
  have hite : ∑ c : Fin t, (if (c : ℕ) + 1 = 1 then vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ)
      else Sha ((c : ℕ) + 1 - 1)) ≤
      (vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ)) + ∑ e ∈ Ioo 0 t, Sha e :=
    (Fin.sum_univ_eq_sum_range (fun i => if i + 1 = 1 then vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ)
      else Sha (i + 1 - 1)) t).le.trans (sum_ite_le t _ Sha)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    at hsucc
  refine (add_le_add h0b (hsucc.trans (add_le_add hite le_rfl))).trans (le_of_eq ?_)
  simp only [Finset.sum_add_distrib]
  ring

theorem etaBound : LocalSubalgebraEtaBound := by
  intro O _ _ _ X _ T _ hsep V _ _ _ _ _ act hsum L hL hspan hLT Z Zg hZg a A haL hacomm haG haB
    B hB
  refine (congBoundGood O X T hsep V act hsum L hL hspan hLT Z Zg hZg a A haL hacomm haG
    haB).trans ?_
  refine sum_le_sum fun x hx => ?_
  gcongr
  exact hB x hx

end Formalism.NG
end
end

