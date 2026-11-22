import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ImaginaryQuadraticClassBound.Development

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ImaginaryQuadraticClassBound.ClassNum
section
open NumberField NumberField.InfinitePlace
open scoped nonZeroDivisors

namespace PI.RayBoundIQW

section Lattice

variable {R : Type*} [CommRing R]

def HData (I : Ideal R) (e1 e2 : R) (a c b : ℕ) : Prop :=
  0 < a ∧ 0 < c ∧ b < a ∧ ((a : ℤ) : R) * e1 ∈ I ∧ ((b : ℤ) : R) * e1 + ((c : ℤ) : R) * e2 ∈ I ∧
    (∀ n : ℕ, 0 < n → n < a → ((n : ℤ) : R) * e1 ∉ I) ∧
    (∀ n : ℕ, 0 < n → n < c → ∀ x : ℤ, (x : R) * e1 + ((n : ℤ) : R) * e2 ∉ I)

theorem HData.minA {I : Ideal R} {e1 e2 : R} {a c b : ℕ} (hP : HData I e1 e2 a c b)
    (x : ℤ) (hx : (x : R) * e1 ∈ I) (h1 : -(a : ℤ) < x) (h2 : x < a) : x = 0 := by
  obtain ⟨-, -, -, -, -, hamin, -⟩ := hP
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine hamin (-x).toNat (by omega) (by omega) ?_
    have e : ((((-x).toNat : ℕ) : ℤ) : R) = -(x : R) := by
      rw [Int.toNat_of_nonneg (by omega)]; push_cast; ring
    rw [e]
    convert I.neg_mem hx using 1; ring
  · refine hamin x.toNat (by omega) (by omega) ?_
    rwa [Int.toNat_of_nonneg hpos.le]

theorem HData.minC {I : Ideal R} {e1 e2 : R} {a c b : ℕ} (hP : HData I e1 e2 a c b)
    (x y : ℤ) (hx : (x : R) * e1 + (y : R) * e2 ∈ I) (h1 : -(c : ℤ) < y) (h2 : y < c) :
    y = 0 := by
  obtain ⟨-, -, -, -, -, -, hcmin⟩ := hP
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine hcmin (-y).toNat (by omega) (by omega) (-x) ?_
    have e : ((((-y).toNat : ℕ) : ℤ) : R) = -(y : R) := by
      rw [Int.toNat_of_nonneg (by omega)]; push_cast; ring
    rw [e]
    convert I.neg_mem hx using 1; push_cast; ring
  · refine hcmin y.toNat (by omega) (by omega) x ?_
    rwa [Int.toNat_of_nonneg hpos.le]

theorem HData.le {I J : Ideal R} {e1 e2 : R} {a c b : ℕ}
    (hspan : ∀ z : R, ∃ x y : ℤ, z = (x : R) * e1 + (y : R) * e2)
    (hP : HData I e1 e2 a c b) (haJ : ((a : ℤ) : R) * e1 ∈ J)
    (hbJ : ((b : ℤ) : R) * e1 + ((c : ℤ) : R) * e2 ∈ J) : I ≤ J := by
  intro z hz
  obtain ⟨x, y, rfl⟩ := hspan z
  have hc0 : (0 : ℤ) < c := by exact_mod_cast hP.2.1
  have ha0 : (0 : ℤ) < a := by exact_mod_cast hP.1
  obtain ⟨q, r, hr0, hrc, rfl⟩ : ∃ q r : ℤ, 0 ≤ r ∧ r < c ∧ y = c * q + r :=
    ⟨y / c, y % c, Int.emod_nonneg _ hc0.ne', Int.emod_lt_of_pos _ hc0,
      (Int.mul_ediv_add_emod y c).symm⟩
  have hz1 : ((x - q * b : ℤ) : R) * e1 + (r : R) * e2 ∈ I := by
    have := I.sub_mem hz (I.mul_mem_left (q : R) hP.2.2.2.2.1)
    convert this using 1; push_cast; ring
  have hr : r = 0 := hP.minC _ _ hz1 (by omega) hrc
  subst hr
  obtain ⟨q', t, ht0, hta, hs⟩ : ∃ q' t : ℤ, 0 ≤ t ∧ t < a ∧ x - q * b = a * q' + t :=
    ⟨(x - q * b) / a, (x - q * b) % a, Int.emod_nonneg _ ha0.ne', Int.emod_lt_of_pos _ ha0,
      (Int.mul_ediv_add_emod _ _).symm⟩
  have hz2 : (t : R) * e1 ∈ I := by
    have := I.sub_mem hz1 (I.mul_mem_left (q' : R) hP.2.2.2.1)
    convert this using 1; rw [hs]; push_cast; ring
  have ht : t = 0 := hP.minA _ hz2 (by omega) hta
  subst ht
  have hx : x = a * q' + q * b := by linarith
  subst hx
  have := J.add_mem (J.mul_mem_left (q' : R) haJ) (J.mul_mem_left (q : R) hbJ)
  convert this using 1; push_cast; ring

end Lattice

end PI.RayBoundIQW
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ImaginaryQuadraticClassBound.GenCoprime
section
open NumberField
open scoped nonZeroDivisors

namespace PI.RayBoundIQW

variable {K0 : Type} [Field K0] [NumberField K0] (qq : Ideal (𝓞 K0))

abbrev PrimeTo := {I : Ideal (𝓞 K0) // I ≠ ⊥ ∧ I ⊔ qq = ⊤}

noncomputable def cls (J : PrimeTo qq) : ClassGroup (𝓞 K0) :=
  ClassGroup.mk0 ⟨J.1, mem_nonZeroDivisors_of_ne_zero J.2.1⟩

noncomputable def base (c : ClassGroup (𝓞 K0)) : PrimeTo qq := by
  classical
  exact if h : ∃ I : PrimeTo qq, cls qq I = c then h.choose else ⟨⊤, top_ne_bot, top_sup_eq _⟩

theorem cls_base (J : PrimeTo qq) : cls qq (base qq (cls qq J)) = cls qq J := by
  classical
  have h : ∃ I : PrimeTo qq, cls qq I = cls qq J := ⟨J, rfl⟩
  unfold base
  rw [dif_pos h]
  exact h.choose_spec

theorem principal (J : PrimeTo qq) : ∃ m : 𝓞 K0,
    Ideal.span {m} = J.1 * (base qq (cls qq J)).1 ^ (classNumber K0 - 1) := by
  set B := base qq (cls qq J) with hB
  have hJ0 : J.1 ∈ (Ideal (𝓞 K0))⁰ := mem_nonZeroDivisors_of_ne_zero J.2.1
  have hB0 : B.1 ∈ (Ideal (𝓞 K0))⁰ := mem_nonZeroDivisors_of_ne_zero B.2.1
  have hP0 : J.1 * B.1 ^ (classNumber K0 - 1) ∈ (Ideal (𝓞 K0))⁰ :=
    ((⟨J.1, hJ0⟩ : (Ideal (𝓞 K0))⁰) * (⟨B.1, hB0⟩ : (Ideal (𝓞 K0))⁰) ^ (classNumber K0 - 1)).2
  have hone : ClassGroup.mk0 ⟨J.1 * B.1 ^ (classNumber K0 - 1), hP0⟩ = 1 := by
    have e : (⟨J.1 * B.1 ^ (classNumber K0 - 1), hP0⟩ : (Ideal (𝓞 K0))⁰) =
        (⟨J.1, hJ0⟩ : (Ideal (𝓞 K0))⁰) * (⟨B.1, hB0⟩ : (Ideal (𝓞 K0))⁰) ^ (classNumber K0 - 1) := by
      apply Subtype.ext
      simp
    rw [e, map_mul, map_pow]
    have h1 : ClassGroup.mk0 (⟨B.1, hB0⟩ : (Ideal (𝓞 K0))⁰) = cls qq J := cls_base qq J
    have h2 : ClassGroup.mk0 (⟨J.1, hJ0⟩ : (Ideal (𝓞 K0))⁰) = cls qq J := rfl
    rw [h1, h2, ← pow_succ']
    have hpos : 0 < classNumber K0 := classNumber_pos K0
    rw [Nat.sub_add_cancel hpos]
    exact pow_card_eq_one
  have hpr := (ClassGroup.mk0_eq_one_iff hP0).mp hone
  exact ⟨Submodule.IsPrincipal.generator _, Submodule.IsPrincipal.span_singleton_generator _⟩

noncomputable def gen (J : PrimeTo qq) : 𝓞 K0 := (principal qq J).choose

theorem gen_spec (J : PrimeTo qq) :
    Ideal.span {gen qq J} = J.1 * (base qq (cls qq J)).1 ^ (classNumber K0 - 1) :=
  (principal qq J).choose_spec

theorem gen_ne_zero (J : PrimeTo qq) : gen qq J ≠ 0 := by
  intro h
  have e := gen_spec qq J
  rw [h, Ideal.span_singleton_eq_bot.mpr rfl] at e
  have hJ : J.1 ≠ 0 := J.2.1
  have hB : (base qq (cls qq J)).1 ^ (classNumber K0 - 1) ≠ 0 :=
    pow_ne_zero _ (base qq (cls qq J)).2.1
  exact mul_ne_zero hJ hB (by rw [← e]; rfl)

theorem gen_coprime (J : PrimeTo qq) : Ideal.span {gen qq J} ⊔ qq = ⊤ := by
  rw [gen_spec, ← Ideal.isCoprime_iff_sup_eq]
  exact IsCoprime.mul_left (Ideal.isCoprime_iff_sup_eq.mpr J.2.2)
    (IsCoprime.pow_left (Ideal.isCoprime_iff_sup_eq.mpr (base qq (cls qq J)).2.2))

noncomputable def inv (J : PrimeTo qq) : ClassGroup (𝓞 K0) × (𝓞 K0 ⧸ qq) :=
  (cls qq J, Ideal.Quotient.mk qq (gen qq J))

theorem key (hre : IsEmpty (K0 →+* ℝ)) (J J' : PrimeTo qq) (h : inv qq J = inv qq J') :
    rayRel K0 qq J J' := by
  have hc : cls qq J = cls qq J' := congrArg Prod.fst h
  have hr : Ideal.Quotient.mk qq (gen qq J) = Ideal.Quotient.mk qq (gen qq J') :=
    congrArg Prod.snd h
  have hJ := gen_spec qq J
  have hJ' := gen_spec qq J'
  rw [← hc] at hJ'
  have hdiff : gen qq J - gen qq J' ∈ qq := Ideal.Quotient.eq.mp hr
  have hmul : Ideal.span {gen qq J'} * J.1 = Ideal.span {gen qq J} * J'.1 := by
    rw [hJ, hJ']; ring
  obtain ⟨t, q, hq, htq⟩ := Ideal.mem_span_singleton_sup.mp
    ((gen_coprime qq J).symm ▸ Submodule.mem_top : (1 : 𝓞 K0) ∈ Ideal.span {gen qq J} ⊔ qq)
  by_cases ht : t = 0
  · have htop : qq = ⊤ := by
      rw [Ideal.eq_top_iff_one]; rw [ht, zero_mul, zero_add] at htq; exact htq ▸ hq
    refine ⟨gen qq J', gen qq J, gen_ne_zero qq J', gen_ne_zero qq J, ?_, ?_, ?_, hmul⟩
    · exact (mul_one (gen qq J' - 1)) ▸ qq.mul_mem_left _ ((Ideal.eq_top_iff_one qq).mp htop)
    · exact (mul_one (gen qq J - 1)) ▸ qq.mul_mem_left _ ((Ideal.eq_top_iff_one qq).mp htop)
    · intro σ; exact isEmptyElim σ
  · refine ⟨t * gen qq J', t * gen qq J, mul_ne_zero ht (gen_ne_zero qq J'),
      mul_ne_zero ht (gen_ne_zero qq J), ?_, ?_, ?_, ?_⟩
    · have e : t * gen qq J' - 1 = (-t) * (gen qq J - gen qq J') + -q := by
        linear_combination htq
      rw [e]; exact qq.add_mem (qq.mul_mem_left _ hdiff) (qq.neg_mem hq)
    · have e : t * gen qq J - 1 = -q := by linear_combination htq
      rw [e]; exact qq.neg_mem hq
    · intro σ; exact isEmptyElim σ
    · rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
        mul_assoc, mul_assoc, hmul]

end PI.RayBoundIQW
end

