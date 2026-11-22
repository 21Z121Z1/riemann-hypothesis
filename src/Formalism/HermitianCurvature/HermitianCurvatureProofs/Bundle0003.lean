import Mathlib
import Formalism.PeriodIntegrals.UpqRep
import Formalism.HermitianCurvature.Bundle0001
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0001

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJmuHC
section
namespace Formalism.FourierDecayAlt.P.CutBP.JmuHC

open Finset

theorem prod_one_add_inv_le (D : Finset ℕ) (h0 : 0 ∉ D) : ∏ d ∈ D, (1 + 1 / (d : ℝ)) ≤ D.card + 1 := by
  induction D using Finset.induction_on_max with
  | empty => simp
  | insert m D hlt ih =>
    have hm : m ∉ D := fun h => lt_irrefl _ (hlt m h)
    have h0' : 0 ∉ D := fun h => h0 (mem_insert_of_mem h)
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun e => h0 (e ▸ mem_insert_self m D)
    have hcard : D.card + 1 ≤ m := by
      have hsub : D ⊆ (range m).erase 0 := fun x hx =>
        mem_erase.2 ⟨fun e => h0' (e ▸ hx), mem_range.2 (hlt x hx)⟩
      have := card_le_card hsub
      rw [card_erase_of_mem (mem_range.2 hm0), card_range] at this
      omega
    rw [prod_insert hm, card_insert_of_notMem hm]
    have ih' := ih h0'
    have hP : 0 ≤ ∏ d ∈ D, (1 + 1 / (d : ℝ)) := prod_nonneg fun d _ => by positivity
    have hc : ((D.card : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast hcard
    have hc0 : (0 : ℝ) < (D.card : ℝ) + 1 := by positivity
    have h1 : 1 + 1 / (m : ℝ) ≤ 1 + 1 / ((D.card : ℝ) + 1) := by
      have := one_div_le_one_div_of_le hc0 hc
      linarith
    calc (1 + 1 / (m : ℝ)) * ∏ d ∈ D, (1 + 1 / (d : ℝ))
        ≤ (1 + 1 / ((D.card : ℝ) + 1)) * ((D.card : ℝ) + 1) :=
          mul_le_mul h1 ih' hP (by positivity)
      _ = ((D.card + 1 : ℕ) : ℝ) + 1 := by
          push_cast
          field_simp

variable {n : ℕ}

theorem prod_ratio_le (x : Fin n → ℝ) (hinj : Function.Injective x) (hint : ∀ a b, ∃ m : ℤ, x a - x b = m)
    (s : Fin n) (T : Finset (Fin n)) (hs : s ∉ T) :
    ∏ t ∈ T, |x s + 1 - x t| / |x s - x t| ≤ n := by
  classical
  have hne : ∀ t ∈ T, x s ≠ x t := fun t ht e => hs (hinj e ▸ ht)
  rw [← prod_filter_mul_prod_filter_not T (fun t => x t < x s)]

  have hlow : ∏ t ∈ T.filter (fun t => ¬ x t < x s), |x s + 1 - x t| / |x s - x t| ≤ 1 := by
    apply prod_le_one (fun t _ => by positivity)
    intro t ht
    obtain ⟨ht, hlt⟩ := mem_filter.1 ht
    have hgt : x s < x t := lt_of_le_of_ne (not_lt.1 hlt) (hne t ht)
    obtain ⟨m, hmv⟩ := hint t s
    have hm1 : (1 : ℝ) ≤ x t - x s := by
      rw [hmv]
      have : (0 : ℤ) < m := by exact_mod_cast (hmv ▸ sub_pos.2 hgt)
      exact_mod_cast this
    rw [div_le_one (abs_pos.2 (sub_ne_zero.2 (hne t ht)))]
    rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)]
    linarith

  set Tp := T.filter (fun t => x t < x s) with hTp
  let dN : Fin n → ℕ := fun t => (⌊x s - x t⌋).toNat
  have hdN : ∀ t ∈ Tp, ((dN t : ℕ) : ℝ) = x s - x t ∧ 1 ≤ x s - x t := by
    intro t ht
    obtain ⟨-, hlt⟩ := mem_filter.1 ht
    obtain ⟨m, hmv⟩ := hint s t
    have hm0 : (0 : ℤ) < m := by exact_mod_cast (hmv ▸ sub_pos.2 hlt)
    refine ⟨?_, ?_⟩
    · simp only [dN, hmv, Int.floor_intCast]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hm0.le]
    · rw [hmv]; exact_mod_cast hm0
  have hinjOn : Set.InjOn dN Tp := by
    intro t ht t' ht' e
    have h1 := (hdN t ht).1
    have h2 := (hdN t' ht').1
    apply hinj
    have : x s - x t = x s - x t' := by rw [← h1, ← h2, e]
    linarith
  have hup : ∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t| = ∏ d ∈ Tp.image dN, (1 + 1 / (d : ℝ)) := by
    rw [prod_image hinjOn]
    refine prod_congr rfl fun t ht => ?_
    obtain ⟨h1, h2⟩ := hdN t ht
    rw [h1, abs_of_pos (by linarith), abs_of_pos (by linarith)]
    field_simp
    ring
  have hD0 : 0 ∉ Tp.image dN := by
    intro h
    obtain ⟨t, ht, e⟩ := mem_image.1 h
    have h1 := hdN t ht
    rw [e] at h1
    simp at h1
    linarith [h1.1, h1.2]
  have hbound := prod_one_add_inv_le (Tp.image dN) hD0
  rw [card_image_of_injOn hinjOn] at hbound
  have hTcard : Tp.card + 1 ≤ n := by
    have h1 : Tp.card ≤ T.card := card_le_card (filter_subset _ _)
    have h2 : T.card < n := by
      have := card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨subset_univ T, fun e => hs (e ▸ mem_univ s)⟩)
      simpa using this
    omega
  have hupnn : 0 ≤ ∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t| := prod_nonneg fun t _ => by positivity
  calc (∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t|) *
        ∏ t ∈ T.filter (fun t => ¬ x t < x s), |x s + 1 - x t| / |x s - x t|
      ≤ (∏ t ∈ Tp, |x s + 1 - x t| / |x s - x t|) * 1 := mul_le_mul_of_nonneg_left hlow hupnn
    _ ≤ (n : ℝ) := by
        rw [mul_one, hup]
        refine hbound.trans ?_
        exact_mod_cast hTcard

def numHC (x : Fin n → ℝ) : ℝ := ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), |x a - x b|

theorem sq_prod_lt (g : Fin n → Fin n → ℝ) (hg : ∀ a b, g a b = g b a) :
    (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), g a b) ^ 2 = ∏ a : Fin n, ∏ b ∈ univ.erase a, g a b := by
  have h1 : ∀ a : Fin n, ∏ b ∈ univ.erase a, g a b =
      (∏ b ∈ univ.filter (fun b : Fin n => a < b), g a b) * ∏ b ∈ univ.filter (fun b : Fin n => b < a), g a b := by
    intro a
    rw [← prod_union]
    · congr 1
      ext b
      simp only [mem_erase, mem_univ, and_true, mem_union, mem_filter, true_and]
      constructor
      · intro h; rcases lt_or_gt_of_ne h with h | h <;> [exact Or.inr h; exact Or.inl h]
      · rintro (h | h) <;> [exact ne_of_gt h; exact ne_of_lt h]
    · rw [disjoint_filter]
      intro b _ h1 h2
      exact lt_asymm h1 h2
  rw [prod_congr rfl (fun a _ => h1 a), prod_mul_distrib, sq]
  congr 1
  have hB : ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => b < a), g a b =
      ∏ b : Fin n, ∏ a ∈ univ.filter (fun a : Fin n => b < a), g a b :=
    prod_comm' (by intro a b; simp)
  rw [hB]
  exact prod_congr rfl fun b _ => prod_congr rfl fun a _ => hg b a

theorem numHC_addI_le (x : Fin n → ℝ) (hinj : Function.Injective x) (hint : ∀ a b, ∃ m : ℤ, x a - x b = m)
    (I : Finset (Fin n)) :
    numHC (fun i => x i + if i ∈ I then 1 else 0) ≤ (n : ℝ) ^ I.card * numHC x := by
  classical
  set y : Fin n → ℝ := fun i => x i + if i ∈ I then 1 else 0 with hydef
  set f : Fin n → Fin n → ℝ := fun a b => |y a - y b| / |x a - x b| with hf
  have hx0 : ∀ a b, a ≠ b → |x a - x b| ≠ 0 := fun a b h =>
    abs_ne_zero.2 (sub_ne_zero.2 fun e => h (hinj e))
  have hfs : ∀ a b, f a b = f b a := fun a b => by simp only [hf, abs_sub_comm]
  have hy : ∀ a b, a ≠ b → |y a - y b| = f a b * |x a - x b| := fun a b h => by
    simp only [hf]; rw [div_mul_cancel₀ _ (hx0 a b h)]
  have hf1 : ∀ a b, a ≠ b → (a ∈ I ↔ b ∈ I) → f a b = 1 := by
    intro a b h hab
    simp only [hf, hydef]
    have : (x a + if a ∈ I then 1 else 0) - (x b + if b ∈ I then 1 else 0) = x a - x b := by
      by_cases ha : a ∈ I
      · rw [if_pos ha, if_pos (hab.1 ha)]; ring
      · rw [if_neg ha, if_neg (fun hb => ha (hab.2 hb))]; ring
    rw [this, div_self (hx0 a b h)]
  have hsqy : numHC y ^ 2 = ∏ a : Fin n, ∏ b ∈ univ.erase a, |y a - y b| :=
    sq_prod_lt _ fun a b => abs_sub_comm _ _
  have hsqx : numHC x ^ 2 = ∏ a : Fin n, ∏ b ∈ univ.erase a, |x a - x b| :=
    sq_prod_lt _ fun a b => abs_sub_comm _ _
  have hsplit : ∏ a : Fin n, ∏ b ∈ univ.erase a, |y a - y b| =
      (∏ a : Fin n, ∏ b ∈ univ.erase a, f a b) * numHC x ^ 2 := by
    rw [hsqx, ← prod_mul_distrib]
    refine prod_congr rfl fun a _ => ?_
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun b hb => hy a b (ne_of_mem_erase hb).symm
  set Pr := ∏ s ∈ I, ∏ t ∈ univ \ I, f s t with hPr
  have hff : ∏ a : Fin n, ∏ b ∈ univ.erase a, f a b = Pr ^ 2 := by
    have hin : ∀ a ∈ I, ∏ b ∈ univ.erase a, f a b = ∏ b ∈ univ \ I, f a b := by
      intro a ha
      symm
      apply prod_subset
      · intro b hb
        rw [mem_sdiff] at hb
        exact mem_erase.2 ⟨fun e => hb.2 (e ▸ ha), mem_univ b⟩
      · intro b hb hb'
        have hba : b ≠ a := ne_of_mem_erase hb
        have hbI : b ∈ I := by
          by_contra h
          exact hb' (mem_sdiff.2 ⟨mem_univ b, h⟩)
        exact hf1 a b hba.symm ⟨fun _ => hbI, fun _ => ha⟩
    have hout : ∀ a ∉ I, ∏ b ∈ univ.erase a, f a b = ∏ b ∈ I, f a b := by
      intro a ha
      symm
      apply prod_subset
      · intro b hb
        exact mem_erase.2 ⟨fun e => ha (e ▸ hb), mem_univ b⟩
      · intro b hb hb'
        have hba : b ≠ a := ne_of_mem_erase hb
        exact hf1 a b hba.symm ⟨fun h => absurd h ha, fun h => absurd h hb'⟩
    rw [← prod_filter_mul_prod_filter_not univ (fun a => a ∈ I)]
    have e1 : univ.filter (fun a : Fin n => a ∈ I) = I := by ext a; simp
    have e2 : univ.filter (fun a : Fin n => a ∉ I) = univ \ I := by ext a; simp
    rw [e1, e2, prod_congr rfl hin, prod_congr rfl (fun a ha => hout a (mem_sdiff.1 ha).2)]
    have hC : ∏ a ∈ univ \ I, ∏ b ∈ I, f a b = ∏ b ∈ I, ∏ a ∈ univ \ I, f a b := prod_comm
    rw [hC, sq]
    congr 1
    exact prod_congr rfl fun s _ => prod_congr rfl fun t _ => hfs t s
  have hP0 : 0 ≤ Pr := prod_nonneg fun s _ => prod_nonneg fun t _ => by positivity
  have hPn : Pr ≤ (n : ℝ) ^ I.card := by
    rw [← prod_const]
    refine prod_le_prod (fun s _ => prod_nonneg fun t _ => by positivity) fun s hs => ?_
    have e : ∏ t ∈ univ \ I, f s t = ∏ t ∈ univ \ I, |x s + 1 - x t| / |x s - x t| := by
      refine prod_congr rfl fun t ht => ?_
      have htI : t ∉ I := (mem_sdiff.1 ht).2
      simp only [hf, hydef, if_pos hs, if_neg htI]
      congr 1
      ring_nf
    rw [e]
    exact prod_ratio_le x hinj hint s (univ \ I) (fun h => (mem_sdiff.1 h).2 hs)
  have hny : 0 ≤ numHC y := prod_nonneg fun a _ => prod_nonneg fun b _ => abs_nonneg _
  have hnx : 0 ≤ numHC x := prod_nonneg fun a _ => prod_nonneg fun b _ => abs_nonneg _
  have hsq : numHC y ^ 2 ≤ ((n : ℝ) ^ I.card * numHC x) ^ 2 := by
    rw [hsqy, hsplit, hff, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hP0 hPn 2) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ hny (by positivity) two_ne_zero).1 hsq

theorem fdegHC_addI_le (x : Fin n → ℝ) (hinj : Function.Injective x) (hint : ∀ a b, ∃ m : ℤ, x a - x b = m)
    (I : Finset (Fin n)) :
    PI.UpqRep.fdegHC (fun i => x i + if i ∈ I then 1 else 0) ≤ (n : ℝ) ^ I.card * PI.UpqRep.fdegHC x := by
  unfold PI.UpqRep.fdegHC
  have hD : 0 ≤ ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) :=
    prod_nonneg fun a _ => prod_nonneg fun b hb => by
      have := (mem_filter.1 hb).2
      have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast this
      linarith
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right (numHC_addI_le x hinj hint I) hD

end Formalism.FourierDecayAlt.P.CutBP.JmuHC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DualVolumePowerIdentity
section
namespace Formalism.FourierDecayAlt.P

open Finset Real

namespace Easy

theorem dual_volume_power_identity (ι : Type) [Fintype ι] (c : ι → ℝ) (g rd : ℝ) (r i : ℕ) (hg : 0 < g) (hrd : 0 < rd) :
    (∏ v, c v * (2 * π / g) ^ ((2 * i : ℤ) - 3 - 2 * r)) /
        (g * rd ^ ((2 * r : ℤ) + 3 - 2 * i)) ^ (-(Fintype.card ι : ℤ)) =
      (∏ v, c v) * (2 * π / rd) ^ (((2 * i : ℤ) - 3 - 2 * r) * Fintype.card ι) *
        g ^ (((2 * r + 2 : ℤ) - 2 * ((i : ℤ) - 1)) * Fintype.card ι) := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  set e : ℤ := (2 * i : ℤ) - 3 - 2 * r with he
  set f : ℤ := (Fintype.card ι : ℤ) with hf
  have h1 : (2 * r : ℤ) + 3 - 2 * i = -e := by rw [he]; ring
  have h2 : ((2 * r + 2 : ℤ) - 2 * ((i : ℤ) - 1)) = -e + 1 := by rw [he]; ring
  rw [h1, h2, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← zpow_natCast, ← hf]
  have hg0 : g ≠ 0 := hg.ne'
  have hrd0 : rd ≠ 0 := hrd.ne'
  have hpi0 : (2 * π) ≠ 0 := hpi.ne'
  generalize 2 * π = A at hpi0 ⊢
  have k1 : ((A / g) ^ e) ^ f = A ^ (e * f) / g ^ (e * f) := by
    rw [← zpow_mul, div_zpow]
  have k2 : (g * rd ^ (-e)) ^ (-f) = (g ^ f)⁻¹ * rd ^ (e * f) := by
    rw [mul_zpow, ← zpow_mul, zpow_neg, show (-e * -f) = e * f by ring]
  have k3 : (A / rd) ^ (e * f) = A ^ (e * f) / rd ^ (e * f) := div_zpow _ _ _
  have k4 : g ^ ((-e + 1) * f) = (g ^ (e * f))⁻¹ * g ^ f := by
    rw [show ((-e + 1) * f) = -(e * f) + f by ring, zpow_add₀ hg0, zpow_neg]
  rw [k1, k2, k3, k4]
  have : g ^ (e * f) ≠ 0 := zpow_ne_zero _ hg0
  have : g ^ f ≠ 0 := zpow_ne_zero _ hg0
  have : rd ^ (e * f) ≠ 0 := zpow_ne_zero _ hrd0
  field_simp

end Easy

theorem dual_size_identity : Formalism.FourierDecayAlt.DualSizeIdentity := by
  intro ι _ c g rd r i hg hrd
  exact Easy.dual_volume_power_identity ι c g rd r i hg hrd

theorem omega_norm_formula : Formalism.FourierDecayAlt.OmNorm := by
  intro V _ _ ip hadd hsmul hconj z x T T' Dr hT hzz hxx
  have hadd2 : ∀ w x y, ip w (x + y) = ip w x + ip w y := by
    intro w x y
    rw [hconj (x + y) w, hadd, map_add, ← hconj, ← hconj]
  have hsmul2 : ∀ (s : ℂ) w y, ip w (s • y) = starRingEnd ℂ s * ip w y := by
    intro s w y
    rw [hconj (s • y) w, hsmul, map_mul, ← hconj]
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  set ζ := ip x z with hζ
  have hzx : ip z x = starRingEnd ℂ ζ := hconj x z
  constructor
  · rw [hsmul, hadd, hsmul, hzz]
    field_simp
    ring
  · rw [hsmul, hsmul2, hadd, hadd2, hadd2, hsmul, hsmul, hsmul2, hsmul2, hxx, hzz, hzx, ← hζ]
    apply Complex.ext
    · simp [Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
      field_simp
      ring
    · simp [Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
      field_simp
      ring

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtPrim
section
open Set Filter Topology MeasureTheory intervalIntegral Metric

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {ω : ℂ → ℂ →L[ℝ] ℝ} {S : Set ℂ} {w₀ : ℂ}

def seg (w₀ x : ℂ) (t : ℝ) : ℂ := w₀ + (t : ℂ) * (x - w₀)

theorem seg_mem (hc : Convex ℝ S) (hw₀ : w₀ ∈ S) {x : ℂ} (hx : x ∈ S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    seg w₀ x t ∈ S := by
  have h := hc.add_smul_sub_mem hw₀ hx ht
  simpa [seg, Complex.real_smul] using h

theorem seg_one (w₀ x : ℂ) : seg w₀ x 1 = x := by
  simp [seg]

theorem continuous_seg : Continuous fun p : ℂ × ℝ => seg w₀ p.1 p.2 := by
  unfold seg
  fun_prop

theorem hasDerivAt_seg (x : ℂ) (t : ℝ) : HasDerivAt (fun s : ℝ => seg w₀ x s) (x - w₀) t := by
  have h := ((hasDerivAt_id t).ofReal_comp.mul_const (x - w₀)).const_add w₀
  simpa [seg] using h

theorem hasFDerivAt_seg (x : ℂ) (t : ℝ) :
    HasFDerivAt (fun y : ℂ => seg w₀ y t) ((t : ℂ) • ContinuousLinearMap.id ℝ ℂ) x := by
  have h := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const w₀).const_smul (t : ℂ)
  have h2 := h.const_add w₀
  have hf : (fun y : ℂ => seg w₀ y t) = fun y => w₀ + ((t : ℂ) • fun x => id x - w₀) y := by
    funext y
    simp [seg, smul_eq_mul]
  rw [hf]
  exact h2

theorem prim_eq (ω : ℂ → ℂ →L[ℝ] ℝ) (w₀ w : ℂ) :
    prim ω w₀ w = ∫ t in (0 : ℝ)..1, ω (seg w₀ w t) (w - w₀) := rfl

theorem hasFDerivAt_prim (hS : IsOpen S) (hc : Convex ℝ S) (hw₀ : w₀ ∈ S) (hω : ContDiffOn ℝ 1 ω S)
    (hsym : ∀ p ∈ S, ∀ h k : ℂ, fderiv ℝ ω p h k = fderiv ℝ ω p k h) {w : ℂ} (hw : w ∈ S) :
    HasFDerivAt (prim ω w₀) (ω w) w := by
  have hdiff : ∀ p ∈ S, HasFDerivAt ω (fderiv ℝ ω p) p := fun p hp =>
    (((hω.differentiableOn one_ne_zero) p hp).differentiableAt (hS.mem_nhds hp)).hasFDerivAt
  have hcontω : ContinuousOn ω S := hω.continuousOn
  have hcontD : ContinuousOn (fderiv ℝ ω) S := hω.continuousOn_fderiv_of_isOpen hS le_rfl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hS w hw
  set δ' := δ / 2 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hcb : closedBall w δ' ⊆ S := (closedBall_subset_ball (by linarith)).trans hball
  set K := (fun p : ℂ × ℝ => seg w₀ p.1 p.2) '' (closedBall w δ' ×ˢ Icc (0 : ℝ) 1) with hK
  have hKc : IsCompact K := ((isCompact_closedBall w δ').prod isCompact_Icc).image continuous_seg
  have hKS : K ⊆ S := by
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact seg_mem hc hw₀ (hcb hx) ht
  have hmemK : ∀ x ∈ closedBall w δ', ∀ t ∈ Icc (0 : ℝ) 1, seg w₀ x t ∈ K := fun x hx t ht =>
    ⟨(x, t), ⟨hx, ht⟩, rfl⟩
  obtain ⟨M₁, hM₁⟩ := hKc.exists_bound_of_continuousOn (hcontω.mono hKS)
  obtain ⟨M₂, hM₂⟩ := hKc.exists_bound_of_continuousOn (hcontD.mono hKS)
  set F' : ℂ → ℝ → (ℂ →L[ℝ] ℝ) := fun x t => ω (seg w₀ x t) + t • (fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)
    with hF'
  have hFd : ∀ x ∈ closedBall w δ', ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt (fun y => ω (seg w₀ y t) (y - w₀)) (F' x t) x := by
    intro x hx t ht
    have hs := hmemK x hx t ht
    have hc1 : HasFDerivAt (fun y => ω (seg w₀ y t)) ((fderiv ℝ ω (seg w₀ x t)).comp ((t : ℂ) • ContinuousLinearMap.id ℝ ℂ)) x :=
      (hdiff _ (hKS hs)).comp x (hasFDerivAt_seg x t)
    have hu : HasFDerivAt (fun y : ℂ => y - w₀) (ContinuousLinearMap.id ℝ ℂ) x := (hasFDerivAt_id x).sub_const w₀
    have h := hc1.clm_apply hu
    refine h.congr_fderiv ?_
    ext h'
    simp only [hF', ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply]
    rw [show ((t : ℂ) • h' : ℂ) = (t : ℝ) • h' from by rw [Complex.real_smul]; rfl, map_smul]
    simp
  have hseg_cont : ∀ x ∈ closedBall w δ', ContinuousOn (fun t : ℝ => seg w₀ x t) (Icc 0 1) := fun x _ =>
    (continuous_seg.comp (Continuous.prodMk continuous_const continuous_id)).continuousOn
  have hωseg : ∀ x ∈ closedBall w δ', ContinuousOn (fun t : ℝ => ω (seg w₀ x t)) (Icc 0 1) := fun x hx =>
    hcontω.comp (hseg_cont x hx) fun t ht => hKS (hmemK x hx t ht)
  have hDseg : ∀ x ∈ closedBall w δ', ContinuousOn (fun t : ℝ => fderiv ℝ ω (seg w₀ x t)) (Icc 0 1) := fun x hx =>
    hcontD.comp (hseg_cont x hx) fun t ht => hKS (hmemK x hx t ht)
  have hF'cont : ∀ x ∈ closedBall w δ', ContinuousOn (F' x) (Icc 0 1) := by
    intro x hx
    refine (hωseg x hx).add (ContinuousOn.smul continuousOn_id ?_)
    exact ((ContinuousLinearMap.flipₗᵢ ℝ ℂ ℂ ℝ).continuous.comp_continuousOn (hDseg x hx)).clm_apply continuousOn_const
  have hIoc : Set.uIoc (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  have hwc : w ∈ closedBall w δ' := mem_closedBall_self hδ'0.le
  have hLeib := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun y t => ω (seg w₀ y t) (y - w₀)) (F' := F') (x₀ := w) (a := 0) (b := 1)
    (bound := fun _ => M₁ + M₂ * (δ' + ‖w - w₀‖)) (s := ball w δ') (ball_mem_nhds w hδ'0) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · have hint : ∫ t in (0 : ℝ)..1, F' w t = ω w := by
      have hEq : EqOn (F' w) (fun t => ω (seg w₀ w t) + t • fderiv ℝ ω (seg w₀ w t) (w - w₀)) (uIcc 0 1) := by
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        have hs := hKS (hmemK w hwc t ht)
        simp only [hF']
        congr 2
        ext h'
        simp only [ContinuousLinearMap.flip_apply]
        exact hsym _ hs h' (w - w₀)
      rw [intervalIntegral.integral_congr hEq]
      have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => s • ω (seg w₀ w s))
          (ω (seg w₀ w t) + t • fderiv ℝ ω (seg w₀ w t) (w - w₀)) t := by
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        have hs := hKS (hmemK w hwc t ht)
        have h1 := (hdiff _ hs).comp_hasDerivAt t (hasDerivAt_seg (w₀ := w₀) w t)
        have h2 := (hasDerivAt_id t).smul h1
        refine h2.congr_deriv ?_
        simp only [id, one_smul]
        abel
      have hcd : ContinuousOn (fun t => ω (seg w₀ w t) + t • fderiv ℝ ω (seg w₀ w t) (w - w₀)) (uIcc 0 1) := by
        rw [uIcc_of_le zero_le_one]
        exact (hωseg w hwc).add (continuousOn_id.smul ((hDseg w hwc).clm_apply continuousOn_const))
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcd.intervalIntegrable)]
      simp [seg_one]
    rw [← hint]
    exact hLeib
  · filter_upwards [ball_mem_nhds w hδ'0] with x hx
    have hxc : x ∈ closedBall w δ' := ball_subset_closedBall hx
    rw [hIoc]
    exact (((hωseg x hxc).clm_apply continuousOn_const).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (hωseg w hwc).clm_apply continuousOn_const
  · rw [hIoc]
    exact ((hF'cont w hwc).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · refine Eventually.of_forall fun t ht x hx => ?_
    rw [hIoc] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    have hxc : x ∈ closedBall w δ' := ball_subset_closedBall hx
    have hs := hmemK x hxc t ht'
    have h1 : ‖ω (seg w₀ x t)‖ ≤ M₁ := hM₁ _ hs
    have h2 : ‖fderiv ℝ ω (seg w₀ x t)‖ ≤ M₂ := hM₂ _ hs
    have h3 : ‖x - w₀‖ ≤ δ' + ‖w - w₀‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub x w w₀
      have hxw : ‖x - w‖ ≤ δ' := by rw [← dist_eq_norm]; exact mem_closedBall.mp hxc
      linarith
    have hM₂0 : 0 ≤ M₂ := le_trans (norm_nonneg _) h2
    simp only [hF']
    calc ‖ω (seg w₀ x t) + t • (fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖
        ≤ ‖ω (seg w₀ x t)‖ + ‖t • (fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖ := norm_add_le _ _
      _ ≤ M₁ + M₂ * (δ' + ‖w - w₀‖) := by
        refine add_le_add h1 ?_
        rw [norm_smul]
        have hf : ‖(fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖ ≤ M₂ * (δ' + ‖w - w₀‖) := by
          refine ((fderiv ℝ ω (seg w₀ x t)).flip.le_opNorm (x - w₀)).trans ?_
          rw [ContinuousLinearMap.opNorm_flip]
          exact mul_le_mul h2 h3 (norm_nonneg _) hM₂0
        have ht1 : ‖t‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg ht'.1]; exact ht'.2
        calc ‖t‖ * ‖(fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖ ≤ 1 * (M₂ * (δ' + ‖w - w₀‖)) :=
              mul_le_mul ht1 hf (norm_nonneg _) zero_le_one
          _ = M₂ * (δ' + ‖w - w₀‖) := one_mul _
  · refine Eventually.of_forall fun t ht x hx => ?_
    rw [hIoc] at ht
    exact hFd x (ball_subset_closedBall hx) t (Ioc_subset_Icc_self ht)

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

