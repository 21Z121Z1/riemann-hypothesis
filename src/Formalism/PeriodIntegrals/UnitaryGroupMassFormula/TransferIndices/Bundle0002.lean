import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.DvTransferIdxOf
import Formalism.PeriodIntegrals.Bundle0028

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.FinsumEqLogNorm
section
noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped WithZero

private theorem log_nonpos_of_le_one (m : ℤᵐ⁰) (h : m ≤ 1) : WithZero.log m ≤ 0 := by
  rcases eq_or_ne m 0 with h0 | h0
  · rw [h0, WithZero.log_zero]
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero] at h
    exact WithZero.exp_le_exp.mp h

theorem volume_nonneg : VNonneg := by
  intro K _ _ w x
  unfold vAdd
  have h := log_nonpos_of_le_one (w.valuation K (algebraMap (𝓞 K) K x)) (w.valuation_le_one x)
  omega

theorem mem_of_vAdd_ne {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)
    (h : vAdd w (algebraMap (𝓞 K) K x) ≠ 0) : x ∈ w.asIdeal := by
  by_contra hx
  apply h
  have h1 : w.valuation K (algebraMap (𝓞 K) K x) = 1 :=
    le_antisymm (w.valuation_le_one x) (not_lt.mp fun hlt => hx ((w.valuation_lt_one_iff_mem x).mp hlt))
  unfold vAdd
  rw [h1, WithZero.log_one, neg_zero]

theorem volume_finite' : VFin := by
  intro K _ _ x hx
  have hI : Ideal.span {x} ≠ (0 : Ideal (𝓞 K)) := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  refine (Ideal.finite_factors hI).subset ?_
  intro w hw
  exact Ideal.dvd_span_singleton.mpr (mem_of_vAdd_ne w x hw)

theorem unzero_toAdd (m : ℤᵐ⁰) (h : m ≠ 0) : Multiplicative.toAdd (WithZero.unzero h) = WithZero.log m := by
  obtain ⟨a, rfl⟩ := WithZero.ne_zero_iff_exists.mp h
  first
  | rfl
  | simp [WithZero.log]
  | simp

theorem norm_embedding_eq {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    ‖FinitePlace.embedding v x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(vAdd v x)) := by
  have hv : v.valuation K x ≠ 0 := by simpa using hx
  have he : Valued.v (FinitePlace.embedding v x) = v.valuation K x := by
    first
    | exact v.valuedAdicCompletion_eq_valuation' x
    | exact v.valuedAdicCompletion_eq_valuation x
    | rfl
  rw [FinitePlace.norm_def, he, WithZeroMulInt.toNNReal_neg_apply _ hv, unzero_toAdd _ hv]
  simp [vAdd]

theorem log_norm_embedding {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    Real.log ‖FinitePlace.embedding v x‖ = -((vAdd v x : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)) := by
  rw [norm_embedding_eq v x hx, Real.log_zpow]
  push_cast
  ring

theorem finsum_eq_log_norm {K : Type} [Field K] [NumberField K] (x : 𝓞 K) (hx : x ≠ 0) :
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw K w * (vAdd w (algebraMap (𝓞 K) K x) : ℝ) =
      Real.log |((Algebra.norm ℤ x : ℤ) : ℝ)| / (Module.finrank ℚ K : ℝ) := by
  classical
  have hxK : algebraMap (𝓞 K) K x ≠ 0 := by
    first
    | simpa using hx
    | exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr hx
  have hf : ∀ w : HeightOneSpectrum (𝓞 K), lw K w * (vAdd w (algebraMap (𝓞 K) K x) : ℝ) =
      -Real.log ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ / (Module.finrank ℚ K : ℝ) := by
    intro w
    rw [log_norm_embedding w _ hxK]
    unfold lw
    ring
  have hfin := volume_finite' K x hx
  have hsub : ∀ w, w ∉ hfin.toFinset → ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ = 1 := by
    intro w hw
    have h0 : vAdd w (algebraMap (𝓞 K) K x) = 0 := by
      rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hw
      exact hw
    rw [norm_embedding_eq w _ hxK, h0, neg_zero, zpow_zero]
  have hne : ∀ w ∈ hfin.toFinset, ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ ≠ 0 :=
    fun w _ => norm_ne_zero_iff.mpr ((map_ne_zero _).mpr hxK)
  have hprod : ∏ᶠ w : HeightOneSpectrum (𝓞 K), ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ =
      ∏ w ∈ hfin.toFinset, ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ := by
    refine finprod_eq_prod_of_mulSupport_subset _ ?_
    intro w hw
    rw [Finset.mem_coe]
    by_contra hws
    exact hw (hsub w hws)
  have PF : ∏ᶠ w : FinitePlace K, w (algebraMap (𝓞 K) K x) = (|((Algebra.norm ℤ x : ℤ) : ℝ)|)⁻¹ := by
    have h := FinitePlace.prod_eq_inv_abs_norm_int hx
    first
    | exact h
    | (rw [Int.cast_abs] at h; exact h)
    | (push_cast at h; exact h)
    | (convert h using 3; simp)
  have PF' : ∏ᶠ w : HeightOneSpectrum (𝓞 K), ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ =
      (|((Algebra.norm ℤ x : ℤ) : ℝ)|)⁻¹ := by
    rw [← PF]
    first
    | exact finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm
    | exact finprod_eq_of_bijective (FinitePlace.equivHeightOneSpectrum (K := K)).symm (Equiv.bijective _)
        (fun _ => rfl)
    | exact (finprod_eq_of_bijective (FinitePlace.equivHeightOneSpectrum (K := K)).symm (Equiv.bijective _)
        (fun _ => rfl)).symm
  rw [finsum_congr hf, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_]
  · rw [← Finset.sum_div, Finset.sum_neg_distrib,
      ← Real.log_prod hne,
      ← hprod, PF', Real.log_inv, neg_neg]
  · intro w hw
    rw [Finset.mem_coe]
    by_contra hws
    apply hw
    show -Real.log ‖FinitePlace.embedding w (algebraMap (𝓞 K) K x)‖ / (Module.finrank ℚ K : ℝ) = 0
    rw [hsub w hws, Real.log_one, neg_zero, zero_div]

theorem abs_norm_le {K : Type} [Field K] [NumberField K] (x : 𝓞 K) (B : ℝ) (hB : 0 ≤ B)
    (hσ : ∀ σ : K →+* ℂ, ‖σ (algebraMap (𝓞 K) K x)‖ ≤ B) :
    |((Algebra.norm ℤ x : ℤ) : ℝ)| ≤ B ^ Module.finrank ℚ K := by
  have h1 : |((Algebra.norm ℤ x : ℤ) : ℝ)| =
      ∏ w : InfinitePlace K, w (algebraMap (𝓞 K) K x) ^ w.mult := by
    rw [InfinitePlace.prod_eq_abs_norm, ← Algebra.coe_norm_int]
    first
    | simp
    | norm_cast
  rw [h1, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun w _ => pow_nonneg (AbsoluteValue.nonneg _ _) _) (fun w _ => ?_)
  refine pow_le_pow_left₀ (AbsoluteValue.nonneg _ _) ?_ _
  rw [← InfinitePlace.norm_embedding_eq]
  exact hσ _

theorem volume_sum_le : VSumLe := by
  intro K _ _ x B hx hB hσ
  rw [finsum_eq_log_norm x hx]
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hN : (0 : ℝ) < |((Algebra.norm ℤ x : ℤ) : ℝ)| := by
    rw [abs_pos, Int.cast_ne_zero, Ne, Algebra.norm_eq_zero_iff]
    exact hx
  rw [div_le_iff₀ hd, mul_comm, ← Real.log_pow]
  exact Real.log_le_log hN (abs_norm_le x B hB.le hσ)

end PI.Dv.TIW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.IdxNonnegOfLe
section
noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem idx_self (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) V) : idxAt w M M = 0 := sub_self _

theorem idx_anti (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) : idxAt w M N = -idxAt w N M :=
  (neg_sub _ _).symm

theorem one_notMem_w (w : HeightOneSpectrum (𝓞 K)) : (1 : 𝓞 K) ∉ w.asIdeal :=
  fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

theorem idx_chain (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (M N P : Submodule (𝓞 K) V) (hM : M.FG) (hN : N.FG)
    (hP : P.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V))
    (h2 : Submodule.span K (P : Set V) = Submodule.span K (N : Set V)) :
    idxAt w M P = idxAt w M N + idxAt w N P :=
  (hI K V w M N hM hN h1).2.1 P hP h2

theorem idx_nonneg_of_le (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (hN : N.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V)) (hle : N ≤ M) :
    0 ≤ idxAt w M N := by
  have := (hI K V w M N hM hN h1).2.2.2.1 0 (fun x hx => ⟨1, one_notMem_w w, by
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul, one_smul]; exact hle hx⟩)
  simpa using this

theorem idx_le_nat (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (hN : N.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V)) (n : ℕ) (hn : 0 < n)
    (hle : N ≤ M) (hsm : ∀ x ∈ M, ((n : ℕ) : 𝓞 K) • x ∈ N) :
    idxAt w M N ≤ (Formalism.HN.rkK M : ℤ) * vAdd w ((n : ℕ) : K) :=
  (hI K V w M N hM hN h1).2.2.2.2.2 n hn hle hsm

theorem idx_map (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {V' : Type} [AddCommGroup V'] [Module K V']
    [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (φ : V →ₗ[K] V') (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (hN : N.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V))
    (hker : M ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = N ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K)) :
    idxAt w M N = idxAt w (M.map (φ.restrictScalars (𝓞 K))) (N.map (φ.restrictScalars (𝓞 K))) := by
  have := (hI K V w M N hM hN h1).2.2.1 V' φ
  rw [hker, idx_self, zero_add] at this
  exact this

theorem idx_map_inj (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {V' : Type} [AddCommGroup V'] [Module K V']
    [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (φ : V →ₗ[K] V') (M N : Submodule (𝓞 K) V) (hM : M.FG)
    (hN : N.FG) (h1 : Submodule.span K (M : Set V) = Submodule.span K (N : Set V))
    (hinjM : ∀ x ∈ M, φ x = 0 → x = 0) (hinjN : ∀ x ∈ N, φ x = 0 → x = 0) :
    idxAt w M N = idxAt w (M.map (φ.restrictScalars (𝓞 K))) (N.map (φ.restrictScalars (𝓞 K))) := by
  refine idx_map hI w φ M N hM hN h1 ?_
  have hb : ∀ P : Submodule (𝓞 K) V, (∀ x ∈ P, φ x = 0 → x = 0) →
      P ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = ⊥ := by
    intro P hP
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    exact (Submodule.mem_bot _).mpr (hP x hx1 hx2)
  rw [hb M hinjM, hb N hinjN]

theorem span_pi_eq {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Submodule (𝓞 K) V) :
    Submodule.span K ((Submodule.pi Set.univ M : Submodule (𝓞 K) (ι → V)) : Set (ι → V)) =
      Submodule.pi Set.univ (fun i => Submodule.span K (M i : Set V)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx i _
    exact Submodule.subset_span (hx i (Set.mem_univ i))
  · rw [← Submodule.iSup_map_single]
    refine iSup_le fun i => ?_
    rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
    intro m hm
    rw [SetLike.mem_coe, Submodule.mem_comap]
    apply Submodule.subset_span
    intro j _
    by_cases h : j = i
    · subst h; simpa using hm
    · simp [h]

theorem idx_pi (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {ι : Type} [Fintype ι] [DecidableEq ι]
    (M N : ι → Submodule (𝓞 K) V) (hM : ∀ i, (M i).FG) (hN : ∀ i, (N i).FG)
    (hsp : ∀ i, Submodule.span K (M i : Set V) = Submodule.span K (N i : Set V)) :
    idxAt w (Submodule.pi Set.univ M) (Submodule.pi Set.univ N) = ∑ i, idxAt w (M i) (N i) := by
  have key : ∀ s : Finset ι, idxAt w (Submodule.pi Set.univ fun i => if i ∈ s then M i else ⊥)
      (Submodule.pi Set.univ fun i => if i ∈ s then N i else ⊥) = ∑ i ∈ s, idxAt w (M i) (N i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [idx_self]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, ← ih]
      have fg : ∀ P : ι → Submodule (𝓞 K) V, (∀ i, (P i).FG) →
          (Submodule.pi Set.univ fun i => if i ∈ insert a s then P i else ⊥).FG := fun P hP =>
        Submodule.fg_pi fun i => by split_ifs; exacts [hP i, Submodule.fg_bot]
      have sp : Submodule.span K ((Submodule.pi Set.univ fun i => if i ∈ insert a s then M i else ⊥ :
          Submodule (𝓞 K) (ι → V)) : Set (ι → V)) =
          Submodule.span K ((Submodule.pi Set.univ fun i => if i ∈ insert a s then N i else ⊥ :
          Submodule (𝓞 K) (ι → V)) : Set (ι → V)) := by
        rw [span_pi_eq, span_pi_eq]
        congr 1; funext i; split_ifs
        · exact hsp i
        · simp
      have hc := (hI K (ι → V) w _ _ (fg M hM) (fg N hN) sp).2.2.1 V (LinearMap.proj a)
      have hker : ∀ P : ι → Submodule (𝓞 K) V,
          (Submodule.pi Set.univ fun i => if i ∈ insert a s then P i else ⊥) ⊓
            (LinearMap.ker (LinearMap.proj a : (ι → V) →ₗ[K] V)).restrictScalars (𝓞 K) =
          Submodule.pi Set.univ fun i => if i ∈ s then P i else ⊥ := by
        intro P
        ext x
        simp only [Submodule.mem_inf, Submodule.mem_pi, Set.mem_univ, true_implies,
          Submodule.restrictScalars_mem, LinearMap.mem_ker, LinearMap.proj_apply]
        constructor
        · rintro ⟨h1, h2⟩ i
          by_cases hi : i = a
          · subst hi; simp [ha, h2]
          · have := h1 i; simpa [Finset.mem_insert, hi] using this
        · intro h
          refine ⟨fun i => ?_, ?_⟩
          · by_cases hi : i = a
            · subst hi; have := h i; simp only [ha, if_false, Submodule.mem_bot] at this; simp [this]
            · have := h i; simpa [Finset.mem_insert, hi] using this
          · have := h a; simpa [ha] using this
      have hmap : ∀ P : ι → Submodule (𝓞 K) V,
          (Submodule.pi Set.univ fun i => if i ∈ insert a s then P i else ⊥).map
            ((LinearMap.proj a : (ι → V) →ₗ[K] V).restrictScalars (𝓞 K)) = P a := by
        intro P
        ext m
        simp only [Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, true_implies,
          LinearMap.coe_restrictScalars, LinearMap.proj_apply]
        constructor
        · rintro ⟨x, hx, rfl⟩; have := hx a; simpa using this
        · intro hm
          refine ⟨Pi.single a m, fun i => ?_, by simp⟩
          by_cases hi : i = a
          · subst hi; simpa using hm
          · simp [hi]
      rw [hc, hker, hker, hmap, hmap, add_comm]
  simpa using key Finset.univ

end Gen

end PI.Dv.TIW
end
end

