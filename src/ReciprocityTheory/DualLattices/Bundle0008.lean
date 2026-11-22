import Mathlib
import ReciprocityTheory.DualLattices.Bundle0001

-- bundled from ReciprocityTheory.DualLattices.QExpansionMonoWCoeffZero
section
namespace ReciprocityTheory.PGsh

open UpperHalfPlane hiding I
open Complex ModularForm ModularFormClass MatrixGroups EisensteinSeries

def monoIdx (w : ℕ) : Finset ℕ :=
  (Finset.range (w + 1)).filter fun a => 4 * a ≤ w ∧ 6 ∣ w - 4 * a

def monoB (w a : ℕ) : ℕ := (w - 4 * a) / 6

theorem monoIdx_wt {w a : ℕ} (h : a ∈ monoIdx w) : 4 * a + 6 * monoB w a = w := by
  simp only [monoIdx, Finset.mem_filter, Finset.mem_range] at h
  obtain ⟨_, h1, h2⟩ := h
  unfold monoB
  omega

noncomputable def monoW (w a : ℕ) : ModularForm 𝒮ℒ (w : ℤ) :=
  if h : 4 * a + 6 * monoB w a = w then
    ModularForm.mcast (by omega) ((E₄.pow a).mul (E₆.pow (monoB w a)))
  else 0

theorem coe_monoW {w a : ℕ} (h : a ∈ monoIdx w) :
    (⇑(monoW w a) : ℍ → ℂ) = (⇑E₄) ^ a * (⇑E₆) ^ monoB w a := by
  simp [monoW, monoIdx_wt h]

theorem qExpansion_monoW {w a : ℕ} (h : a ∈ monoIdx w) :
    qExpansion 1 (monoW w a) =
      PowerSeries.map (Int.castRingHom ℂ) (e4Z ^ a * e6Z ^ monoB w a) := by
  simp only [monoW, monoIdx_wt h, dite_true, ModularForm.qExpansion_mcast]
  rw [ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, qExpansion_E₄_eq,
    qExpansion_E₆_eq, map_mul, map_pow, map_pow]

theorem qExpansion_monoW_coeff_zero {w a : ℕ} (h : a ∈ monoIdx w) :
    (qExpansion 1 (monoW w a)).coeff 0 = 1 := by
  have h4 : PowerSeries.constantCoeff e4Z = 1 := by simp [e4Z]
  have h6 : PowerSeries.constantCoeff e6Z = 1 := by simp [e6Z]
  rw [qExpansion_monoW h, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_mul, map_pow, map_pow, h4, h6]
  simp

theorem monoIdx_nonempty {w : ℕ} (he : Even w) (h2 : w ≠ 2) : ∃ a, a ∈ monoIdx w := by
  obtain ⟨m, rfl⟩ := he
  simp only [monoIdx, Finset.mem_filter, Finset.mem_range]
  by_cases h : m % 2 = 0
  · exact ⟨(m + m) / 4, by omega, by omega, ⟨0, by omega⟩⟩
  · exact ⟨(m + m - 6) / 4, by omega, by omega, ⟨1, by omega⟩⟩

noncomputable def monoSpanF (w : ℕ) : Submodule ℂ (ℍ → ℂ) :=
  Submodule.span ℂ (Set.range fun a : monoIdx w => (⇑(monoW w a) : ℍ → ℂ))

theorem mono_mem_monoSpanF {w a : ℕ} (h : a ∈ monoIdx w) : (⇑(monoW w a) : ℍ → ℂ) ∈ monoSpanF w :=
  Submodule.subset_span ⟨⟨a, h⟩, rfl⟩

theorem mulDisc_mem {w : ℕ} (hw : 12 ≤ w) {φ : ℍ → ℂ} (hφ : φ ∈ monoSpanF (w - 12)) :
    (ModularForm.discriminant : ℍ → ℂ) * φ ∈ monoSpanF w := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, ha⟩, rfl⟩ := hx
    have hwt := monoIdx_wt ha
    have ha3 : a + 3 ∈ monoIdx w := by
      simp only [monoIdx, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, by omega, ⟨monoB (w - 12) a, by omega⟩⟩
    have ha0 : a ∈ monoIdx w := by
      simp only [monoIdx, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, by omega, ⟨monoB (w - 12) a + 2, by omega⟩⟩
    have hb3 : monoB w (a + 3) = monoB (w - 12) a := by
      have := monoIdx_wt ha3; omega
    have hb0 : monoB w a = monoB (w - 12) a + 2 := by
      have := monoIdx_wt ha0; omega
    have heq : (ModularForm.discriminant : ℍ → ℂ) * ⇑(monoW (w - 12) a) =
        (1728 : ℂ)⁻¹ • ((⇑(monoW w (a + 3)) : ℍ → ℂ) - ⇑(monoW w a)) := by
      rw [coe_monoW ha, coe_monoW ha3, coe_monoW ha0, hb3, hb0]
      funext z
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
      ring
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (mono_mem_monoSpanF ha3)
      (mono_mem_monoSpanF ha0))
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem coe_mem_monoSpanF (w : ℕ) (f : ModularForm 𝒮ℒ (w : ℤ)) : (⇑f : ℍ → ℂ) ∈ monoSpanF w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  rcases Nat.even_or_odd w with he | ho
  · by_cases h2 : w = 2
    · subst h2
      have : f = 0 := rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero f
      subst this
      simp
    obtain ⟨a, ha⟩ := monoIdx_nonempty he h2
    set g := f - (qExpansion 1 f).coeff 0 • monoW w a with hg
    have hgc : (qExpansion 1 g).coeff 0 = 0 :=
      (ModularForm.isCuspForm_iff_coeffZero_eq_zero g).mp
        (ModularForm.sub_smul_isCuspForm f _ (qExpansion_monoW_coeff_zero ha))
    have hfg : (⇑f : ℍ → ℂ) = ⇑g + (qExpansion 1 f).coeff 0 • ⇑(monoW w a) := by
      rw [hg]; simp
    rw [hfg]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (mono_mem_monoSpanF ha))
    by_cases h12 : w < 12
    · have h0 : ModularForm.toCuspForm g hgc = 0 :=
        rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by omega)) _
      have : (⇑g : ℍ → ℂ) = 0 := by
        funext z
        have := congrArg (fun F : CuspForm 𝒮ℒ (w : ℤ) => F z) h0
        simpa using this
      rw [this]; exact Submodule.zero_mem _
    · replace h12 : 12 ≤ w := by omega
      set h := CuspForm.discriminantEquiv (ModularForm.toCuspForm g hgc) with hh
      have hmem := ih (w - 12) (by omega) (ModularForm.mcast (by omega) h)
      have hgd : (⇑g : ℍ → ℂ) = (ModularForm.discriminant : ℍ → ℂ) * ⇑h := by
        have := ModularForm.discriminant_mul_discriminantEquiv (ModularForm.toCuspForm g hgc)
        rw [hh, this]; rfl
      rw [hgd]
      exact mulDisc_mem h12 hmem
  · have : f = 0 := ModularForm.levelOne_odd_weight_eq_zero (by exact_mod_cast ho.natCast) f
    subst this
    simp

noncomputable def coeLin (k : ℤ) : ModularForm 𝒮ℒ k →ₗ[ℂ] (ℍ → ℂ) where
  toFun f := ⇑f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end ReciprocityTheory.PGsh
end

-- bundled from ReciprocityTheory.DualLattices.SumInvMulTrace
section
namespace ReciprocityTheory.PGsh

open Finset

private lemma sum_inv_mul_trace (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F]
    [inst : Algebra (ZMod p) F] :
    ∑ a : F, a⁻¹ * algebraMap (ZMod p) F (Algebra.trace (ZMod p) F a) = -1 := by
  classical
  simp_rw [_root_.trace_eq_sum_automorphisms, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ 1)]
  have h1 : ∑ a : F, a⁻¹ * (1 : F ≃ₐ[ZMod p] F) a = -1 := by
    have : ∀ a : F, a⁻¹ * (1 : F ≃ₐ[ZMod p] F) a = 1 - if a = 0 then 1 else 0 := by
      intro a
      by_cases h : a = 0
      · simp [h]
      · simp [h]
    simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, nsmul_eq_mul, mul_one,
      FiniteField.cast_card_eq_zero, zero_sub]
  have h2 : ∀ σ : F ≃ₐ[ZMod p] F, σ ≠ 1 → ∑ a : F, a⁻¹ * σ a = 0 := by
    intro σ hσ
    obtain ⟨b, hb⟩ : ∃ b, σ b ≠ b := by
      by_contra h
      push Not at h
      exact hσ (AlgEquiv.ext h)
    have hb0 : b ≠ 0 := by
      rintro rfl
      simp at hb
    have key : ∑ a : F, (b⁻¹ * σ b) * (a⁻¹ * σ a) = ∑ a : F, a⁻¹ * σ a := by
      refine Fintype.sum_equiv (Equiv.mulLeft₀ b hb0) _ _ (fun a => ?_)
      simp only [Equiv.mulLeft₀_apply, map_mul, mul_inv]
      ring
    rw [← Finset.mul_sum] at key
    have hne : b⁻¹ * σ b ≠ 1 := fun h => hb ((inv_mul_eq_one₀ hb0).mp h).symm
    have : (b⁻¹ * σ b - 1) * ∑ a : F, a⁻¹ * σ a = 0 := by
      rw [sub_mul, key, one_mul, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  rw [h1, Finset.sum_eq_zero (fun σ hσ => h2 σ (Finset.ne_of_mem_erase hσ)), add_zero]

theorem gaussCongruence : GaussCongruenceStatement := by
  intro p _ F _ _ _ O _ _ m _ ι ω ζ hF hζ hω
  let _ : Algebra (ZMod p) F := ZMod.algebra F p
  show ∃ y ∈ m, (∑ a : F, ω⁻¹ a * ζ ^ (Algebra.trace (ZMod p) F a).val) = (ζ - 1) * (y - 1)
  obtain ⟨c, rfl⟩ : ∃ c, ζ = 1 + c := ⟨ζ - 1, by ring⟩
  simp only [add_sub_cancel_left]
  have : CharP (O ⧸ m) p := charP_of_injective_ringHom ι.injective p

  have hc : c ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h : (Ideal.Quotient.mk m c) ^ p = 0 := by
      have e : Ideal.Quotient.mk m c = Ideal.Quotient.mk m (1 + c) - 1 := by
        rw [map_add, map_one]; ring
      rw [e, sub_pow_char, one_pow, ← map_pow, hζ, map_one, sub_self]
    exact pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.mp h

  have hbin : ∀ n : ℕ, ∃ r : O, (1 + c) ^ n = 1 + (n : O) * c + c ^ 2 * r := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨r, hr⟩ := ih
      exact ⟨n + r + c * r, by rw [pow_succ, hr]; push_cast; ring⟩
  choose r hr using hbin

  obtain ⟨b, hb0, hb1⟩ : ∃ b : F, b ≠ 0 ∧ b ≠ 1 := by
    classical
    by_contra h
    push Not at h
    apply hF
    have h1 : (Finset.univ : Finset F) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [h x hx]
    have h2 := Finset.card_le_card h1
    have h3 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    have h4 := Fintype.one_lt_card (α := F)
    rw [Finset.card_univ] at h2
    omega
  have hω1 : ω ≠ 1 := by
    intro h
    have e := hω b
    have e1 := MulChar.one_apply_coe (R' := O) (Units.mk0 b hb0)
    rw [Units.val_mk0] at e1
    rw [h, e1, map_one] at e
    exact hb1 (ι.injective (e.symm.trans ι.map_one.symm))
  have hsum0 : ∑ a : F, ω⁻¹ a = 0 := MulChar.sum_eq_zero_of_ne_one (inv_ne_one.mpr hω1)
  set t : F → ℕ := fun a => (Algebra.trace (ZMod p) F a).val with ht
  refine ⟨1 + ∑ a : F, ω⁻¹ a * (t a : O) + c * ∑ a : F, ω⁻¹ a * r (t a), ?_, ?_⟩
  · refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ hc)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, map_one, map_sum]
    have e : ∀ a : F, Ideal.Quotient.mk m (ω⁻¹ a * (t a : O)) =
        ι (a⁻¹ * algebraMap (ZMod p) F (Algebra.trace (ZMod p) F a)) := by
      intro a
      rw [map_mul, map_mul, MulChar.inv_apply', hω, map_natCast, ← map_natCast ι, ht,
        ZMod.natCast_val]
      rfl
    simp_rw [e]
    rw [← map_sum, sum_inv_mul_trace p F, map_neg, map_one, add_neg_cancel]
  · calc ∑ a : F, ω⁻¹ a * (1 + c) ^ t a
        = ∑ a : F, (ω⁻¹ a + c * (ω⁻¹ a * (t a : O) + c * (ω⁻¹ a * r (t a)))) :=
          Finset.sum_congr rfl fun a _ => by rw [hr]; ring
      _ = ∑ a : F, ω⁻¹ a + c * (∑ a : F, ω⁻¹ a * (t a : O) + c * ∑ a : F, ω⁻¹ a * r (t a)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = _ := by rw [hsum0]; ring

end ReciprocityTheory.PGsh
end

-- bundled from ReciprocityTheory.DualLattices.TransposeMulSelf
section
namespace ReciprocityTheory.PGsh

open Matrix

section

variable {K : Type} [Field K] {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

private noncomputable def invPerm (e : G ≃ AddChar G K) : Equiv.Perm G :=
  Function.Involutive.toPerm (fun h => e.symm (e h)⁻¹) (fun h => by simp)

private lemma invPerm_apply (e : G ≃ AddChar G K) (h : G) :
    invPerm e h = e.symm (e h)⁻¹ := rfl

private lemma transpose_mul_self (e : G ≃ AddChar G K) :
    (Matrix.of fun g h : G => e h g)ᵀ * (Matrix.of fun g h : G => e h g) =
      (Fintype.card G : K) • (invPerm e).permMatrix K := by
  ext g h
  have key : ∀ x, e g x * e h x = (e g * e h) x := fun x => (AddChar.mul_apply _ _ _).symm
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, smul_eq_mul, key]
  by_cases hgh : e g * e h = 1
  · have h1 : invPerm e g = h := by
      rw [invPerm_apply, inv_eq_of_mul_eq_one_right hgh, Equiv.symm_apply_apply]
    rw [if_pos h1, hgh]
    simp
  · have h1 : ¬ invPerm e g = h := by
      intro h1
      apply hgh
      rw [invPerm_apply] at h1
      rw [← h1, Equiv.apply_symm_apply, mul_inv_cancel]
    rw [if_neg h1, AddChar.sum_eq_zero_of_ne_one hgh, mul_zero]

private lemma det_sq (e : G ≃ AddChar G K) :
    (Matrix.of fun g h : G => e h g).det ^ 2 =
      (Fintype.card G : K) ^ Fintype.card G * (Equiv.Perm.sign (invPerm e) : K) := by
  have h := congrArg Matrix.det (transpose_mul_self e)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_permutation] at h
  rw [sq]
  exact h

end

theorem charTable : CharTableStatement := by
  intro K _ G _ _ _ e
  rw [det_sq e]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (invPerm e)) with h | h <;> rw [h]
  · left; simp
  · right; simp

end ReciprocityTheory.PGsh
end

-- bundled from ReciprocityTheory.DualLattices.VDetEqOneOfIntegral
section
namespace ReciprocityTheory.PGsh

open Matrix

section

variable {K : Type} [Field K] (v : Valuation K NNReal) {ι : Type} [Fintype ι] [DecidableEq ι]

def IsIntegralMat (U : Matrix ι ι K) : Prop := ∀ i j, v (U i j) ≤ 1

def IsIntegralVec (c : ι → K) : Prop := ∀ j, v (c j) ≤ 1

variable {v}

theorem IsIntegralMat.det_le_one {U : Matrix ι ι K} (hU : IsIntegralMat v U) : v U.det ≤ 1 := by
  rw [Matrix.det_apply']
  refine v.map_sum_le fun σ _ => ?_
  rw [map_mul, map_prod]
  have hs : v ((Equiv.Perm.sign σ : ℤ) : K) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
  rw [hs, one_mul]
  exact Finset.prod_le_one (fun _ _ => zero_le) fun i _ => hU _ _

private theorem nnreal_mul_le_one {a b : NNReal} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 := by
  simpa using mul_le_mul ha hb (zero_le) zero_le_one

theorem IsIntegralMat.mulVec {U : Matrix ι ι K} {c : ι → K} (hU : IsIntegralMat v U)
    (hc : IsIntegralVec v c) : IsIntegralVec v (U *ᵥ c) := by
  intro i
  show v (∑ j, U i j * c j) ≤ 1
  exact v.map_sum_le fun j _ => by rw [map_mul]; exact _root_.ReciprocityTheory.PGsh.nnreal_mul_le_one (hU i j) (hc j)

theorem IsIntegralMat.mul {U V : Matrix ι ι K} (hU : IsIntegralMat v U)
    (hV : IsIntegralMat v V) : IsIntegralMat v (U * V) := by
  intro i j
  rw [Matrix.mul_apply]
  exact v.map_sum_le fun k _ => by rw [map_mul]; exact _root_.ReciprocityTheory.PGsh.nnreal_mul_le_one (hU i k) (hV k j)

theorem isIntegralVec_single (j : ι) : IsIntegralVec v (Pi.single j (1 : K)) := by
  intro k
  by_cases hk : k = j
  · subst hk; simp
  · simp [hk]

end

structure Lat {K : Type} [Field K] (v : Valuation K NNReal) (ι : Type) [Fintype ι]
    [DecidableEq ι] where

  B : Matrix ι ι K
  det_ne : B.det ≠ 0

namespace Lat

variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]

def pts (L : Lat v ι) : Set (ι → K) := {x | ∃ c, IsIntegralVec v c ∧ x = L.B *ᵥ c}

def std (v : Valuation K NNReal) (ι : Type) [Fintype ι] [DecidableEq ι] : Lat v ι :=
  ⟨1, by simp⟩

def mulRight (L : Lat v ι) (U : Matrix ι ι K) (hU : U.det ≠ 0) : Lat v ι :=
  ⟨L.B * U, by rw [Matrix.det_mul]; exact mul_ne_zero L.det_ne hU⟩

theorem isUnit_det (L : Lat v ι) : IsUnit L.B.det :=
  isUnit_iff_ne_zero.mpr L.det_ne

theorem pts_subset_iff (L' L : Lat v ι) :
    L'.pts ⊆ L.pts ↔ IsIntegralMat v (L.B⁻¹ * L'.B) := by
  constructor
  · intro h i j
    obtain ⟨c, hc, hx⟩ := h ⟨Pi.single j 1, ReciprocityTheory.PGsh.isIntegralVec_single j, rfl⟩
    have hM : (L.B⁻¹ * L'.B) *ᵥ Pi.single j 1 = c := by
      rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_det L), Matrix.one_mulVec]
    have e := congrFun hM i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply] at e
    rw [e]
    exact hc i
  · intro hM x ⟨c, hc, hx⟩
    refine ⟨(L.B⁻¹ * L'.B) *ᵥ c, hM.mulVec hc, ?_⟩
    rw [hx, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_det L),
      Matrix.one_mul]

theorem v_det_eq_one_of_integral {U V : Matrix ι ι K} (hU : IsIntegralMat v U)
    (hV : IsIntegralMat v V) (hUV : U * V = 1) : v U.det = 1 := by
  refine le_antisymm hU.det_le_one ?_
  calc (1 : NNReal) = v U.det * v V.det := by
        rw [← map_mul, ← Matrix.det_mul, hUV, Matrix.det_one, map_one]
    _ ≤ v U.det * 1 := mul_le_mul_of_nonneg_left hV.det_le_one (zero_le)
    _ = v U.det := mul_one _

private theorem valuation_lat_det_ne_zero (L : ReciprocityTheory.PGsh.Lat v ι) : v L.B.det ≠ 0 :=
  (Valuation.ne_zero_iff v).mpr L.det_ne

private theorem valuation_det_inv_mul_eq_div (L' L : ReciprocityTheory.PGsh.Lat v ι) :
    v (L.B⁻¹ * L'.B).det = v L'.B.det / v L.B.det := by
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_mul, map_inv₀,
    div_eq_inv_mul]

theorem v_det_eq_of_pts_eq {L₁ L₂ : Lat v ι} (h : L₁.pts = L₂.pts) :
    v L₁.B.det = v L₂.B.det := by
  have h₁ := (pts_subset_iff L₁ L₂).mp h.subset
  have h₂ := (pts_subset_iff L₂ L₁).mp h.symm.subset
  have hMN : (L₂.B⁻¹ * L₁.B) * (L₁.B⁻¹ * L₂.B) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc L₁.B,
      Matrix.mul_nonsing_inv _ (isUnit_det L₁), Matrix.one_mul,
      Matrix.nonsing_inv_mul _ (isUnit_det L₂)]
  have := v_det_eq_one_of_integral h₁ h₂ hMN
  rw [valuation_det_inv_mul_eq_div] at this
  exact (div_eq_one_iff_eq (valuation_lat_det_ne_zero L₂)).mp this

noncomputable def dual (L : Lat v ι) : Lat v ι :=
  ⟨(L.Bᵀ)⁻¹, by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Matrix.det_transpose]
    exact inv_ne_zero L.det_ne⟩

end Lat

section colen

variable {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def colen (L' L : Lat v ι) : NNReal := v L'.B.det / v L.B.det

theorem colen_eq_v_det (L' L : Lat v ι) : colen L' L = v (L.B⁻¹ * L'.B).det := by
  rw [_root_.ReciprocityTheory.PGsh.Lat.valuation_det_inv_mul_eq_div]
  rfl

theorem colen_congr {L₁' L₂' L₁ L₂ : Lat v ι} (h' : L₁'.pts = L₂'.pts) (h : L₁.pts = L₂.pts) :
    colen L₁' L₁ = colen L₂' L₂ := by
  unfold colen
  rw [ReciprocityTheory.PGsh.Lat.v_det_eq_of_pts_eq h', ReciprocityTheory.PGsh.Lat.v_det_eq_of_pts_eq h]

theorem colen_le_one {L' L : Lat v ι} (h : L'.pts ⊆ L.pts) : colen L' L ≤ 1 := by
  rw [colen_eq_v_det]
  exact ((ReciprocityTheory.PGsh.Lat.pts_subset_iff L' L).mp h).det_le_one

theorem colen_trans (L'' L' L : Lat v ι) : colen L'' L = colen L'' L' * colen L' L := by
  unfold colen
  rw [div_mul_div_comm, mul_comm (v L''.B.det),
    mul_div_mul_left _ _ (_root_.ReciprocityTheory.PGsh.Lat.valuation_lat_det_ne_zero L')]

theorem colen_self (L : Lat v ι) : colen L L = 1 :=
  div_self (_root_.ReciprocityTheory.PGsh.Lat.valuation_lat_det_ne_zero L)

theorem colen_pos (L' L : Lat v ι) : 0 < colen L' L :=
  pos_iff_ne_zero.mpr
    (div_ne_zero (_root_.ReciprocityTheory.PGsh.Lat.valuation_lat_det_ne_zero L') (_root_.ReciprocityTheory.PGsh.Lat.valuation_lat_det_ne_zero L))

theorem colen_eq_one_iff (hZ : ColengthZeroStatement) {L' L : Lat v ι} (h : L'.pts ⊆ L.pts) :
    colen L' L = 1 ↔ L'.pts = L.pts := by
  constructor
  · intro h1
    have hM := (ReciprocityTheory.PGsh.Lat.pts_subset_iff L' L).mp h
    rw [colen_eq_v_det] at h1
    have hInv := hZ K v ι _ hM h1
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (ReciprocityTheory.PGsh.Lat.isUnit_det L)] at hInv
    exact Set.Subset.antisymm h ((ReciprocityTheory.PGsh.Lat.pts_subset_iff L L').mpr hInv)
  · intro he
    rw [colen_congr he rfl, colen_self]

private theorem valuation_det_dual_eq_inv {K : Type} [Field K] {v : Valuation K NNReal} {ι : Type} [Fintype ι] [DecidableEq ι] (L : Lat v ι) :
    v L.dual.B.det = (v L.B.det)⁻¹ := by
  show v ((L.Bᵀ)⁻¹).det = _
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', Matrix.det_transpose, map_inv₀]

theorem colen_dual (L' L : Lat v ι) : colen L.dual L'.dual = colen L' L := by
  unfold colen
  rw [valuation_det_dual_eq_inv, valuation_det_dual_eq_inv, inv_div_inv]

theorem dual_subset {L' L : Lat v ι} (h : L'.pts ⊆ L.pts) : L.dual.pts ⊆ L'.dual.pts := by
  have hM := (ReciprocityTheory.PGsh.Lat.pts_subset_iff L' L).mp h
  rw [ReciprocityTheory.PGsh.Lat.pts_subset_iff]
  show IsIntegralMat v (((L'.Bᵀ)⁻¹)⁻¹ * (L.Bᵀ)⁻¹)
  rw [Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_transpose]; exact ReciprocityTheory.PGsh.Lat.isUnit_det L'),
    ← Matrix.transpose_nonsing_inv, ← Matrix.transpose_mul]
  intro i j
  exact hM j i

end colen

end ReciprocityTheory.PGsh
end

