import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0116
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0119
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0072
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0011
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0124
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0125
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0126

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIdempotentFrobeniusOrbitUnramified
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.UnrIdem

theorem exists_idem (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime)
    (hd : ¬ (l : ℤ) ∣ NumberField.discr E) (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hlP : (l : 𝓞 E) ∈ P) :
    ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (l : 𝓞 E) * y) ∧ ε - 1 ∈ P ∧ ∀ x ∈ P, ∃ y, ε * x = (l : 𝓞 E) * y := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hun : Algebra.IsUnramifiedAt ℤ P :=
    (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hp).mp hd P hP (by simpa using hlP)
  have hov : P.LiesOver (Ideal.span {(l : ℤ)}) :=
    (Ideal.liesOver_span_iff hP.ne_top hp).mpr (by simpa using hlP)
  have hmap : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 E)) = Ideal.span {(l : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hl0 : (l : 𝓞 E) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hne : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := by
    rw [hmap]; simpa using hl.ne_zero
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hl0 (by simpa using hlP)
  have := hP.isMaximal hP0
  obtain ⟨Q, h₁, h₂⟩ := Ideal.eq_prime_pow_mul_coprime hne P
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ hne,
    Ideal.ramificationIdx_eq_one P ℤ, pow_one, hmap] at h₂
  obtain ⟨p, hpP, q, hqQ, hpq⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp h₁)
  have key : ∀ x ∈ P, ∃ y, q * x = (l : 𝓞 E) * y := by
    intro x hx
    have : x * q ∈ Ideal.span {(l : 𝓞 E)} := h₂ ▸ Ideal.mul_mem_mul hx hqQ
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp this
    exact ⟨y, by rw [mul_comm, hy]⟩
  have hq1 : q - 1 ∈ P := by
    have : q - 1 = -p := by rw [← hpq]; ring
    rw [this]; exact P.neg_mem hpP
  refine ⟨q, ?_, hq1, key⟩
  obtain ⟨y, hy⟩ := key _ hq1
  exact ⟨y, by rw [← hy]; ring⟩

variable {C : Type} [Field C] {V : VF C}

theorem ge_int {x : C} (hx : IsIntegral ℤ x) : V.Ge 0 x := by
  have h1 : IsIntegral (Valuation.integer (V.v : Valuation C (Multiplicative (WithTop ℝ)ᵒᵈ))) x := hx.tower_top
  exact (Valuation.integer.integers (V.v : Valuation C (Multiplicative (WithTop ℝ)ᵒᵈ))).mem_of_integral h1

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := V.v.map_lt_add ha hb

theorem mm_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at ha
  rw [V.v.map_mul]
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left (by simpa using ha))

def ker (V : VF C) {R : Type} [CommRing R] (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) : Ideal R where
  carrier := {x | V.MM (f x)}
  add_mem' := fun {a b} ha hb => by
    show V.MM (f (a + b))
    rw [map_add]; exact mm_add ha hb
  zero_mem' := by
    show V.MM (f 0)
    simp [VF.MM]
  smul_mem' := fun c x hx => by
    show V.MM (f (c * x))
    rw [map_mul]; exact mm_mul (hf c) hx

theorem ker_isPrime {R : Type} [CommRing R] (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) : (ker V f hf).IsPrime := by
  refine ⟨(Ideal.ne_top_iff_one _).mpr ?_, fun {a b} hab => ?_⟩
  · show ¬ V.MM (f 1)
    simp [VF.MM]
  · change V.MM (f (a * b)) at hab
    show V.MM (f a) ∨ V.MM (f b)
    have ha := hf a
    have hb := hf b
    unfold VF.MM VF.Ge at *
    rw [map_mul, V.v.map_mul] at hab
    by_contra hc
    push Not at hc
    exact absurd hab (not_lt.mpr (add_nonpos hc.1 hc.2))

end GlobalTheory.UnrIdem

open GlobalTheory.UnrIdem in
theorem GlobalTheory.exists_idempotent_of_unramified_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (d : ℕ) [NeZero d] (tau : ZMod d → (E →+* ℂ)), FrobOrd V io ι tau → ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (V.l : 𝓞 E) * y) ∧ (∀ a, V.MM (emA3 io ι (tau a) ε - 1)) ∧ ∀ x : 𝓞 E, (∀ a, V.MM (emA3 io ι (tau a) x)) → ∃ y, ε * x = (V.l : 𝓞 E) * y := by
  intro E _ _ _ H lv c T io C _ _ V ι _ hd d _ tau hF
  have hint : ∀ τ x, V.Ge 0 (emA3 io ι τ x) := fun τ x =>
    ge_int ((RingOfIntegers.isIntegral x).map (emA3 io ι τ).toIntAlgHom)
  have hstep : ∀ x s, V.MM (emA3 io ι (tau s) x) → V.MM (emA3 io ι (tau (s + 1)) x) := by
    intro x s hs
    have h1 := hF s x
    have h2 : V.MM (emA3 io ι (tau s) x ^ V.l) := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero V.l_prime.ne_zero
      rw [hk, pow_succ]
      exact mm_mul ((hint _ _).pow k) hs
    simpa using mm_add h1 h2
  have hall : ∀ x, V.MM (emA3 io ι (tau 0) x) → ∀ a, V.MM (emA3 io ι (tau a) x) := by
    intro x h0 a
    have : ∀ n : ℕ, V.MM (emA3 io ι (tau (n : ZMod d)) x) := by
      intro n
      induction n with
      | zero => simpa using h0
      | succ n ih => push_cast; exact hstep x _ ih
    simpa using this a.val
  have hP := ker_isPrime (V := V) (emA3 io ι (tau 0)) (hint _)
  obtain ⟨ε, h1, h2, h3⟩ := exists_idem E V.l V.l_prime hd (ker V (emA3 io ι (tau 0)) (hint _)) (by
    show V.MM (emA3 io ι (tau 0) (V.l : 𝓞 E))
    rw [map_natCast]
    unfold VF.MM
    rw [V.v_l]
    exact zero_lt_one)
  refine ⟨ε, h1, fun a => ?_, fun x hx => h3 x (hx 0)⟩
  have := hall _ h2 a
  rwa [map_sub, map_one] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMatrixStandardToHyperbolicInertPlace
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.InertHyperbolic

theorem exists_norm_eq_neg_one (K : Type) [Field K] (l : ℕ) (hl : l.Prime) (h2 : l ≠ 2) [CharP K l]
    (t : K) (ht : t ≠ 0) (htl : t ^ l = -t) : ∃ a b : ℤ, (a : K) ^ 2 - (b : K) ^ 2 * t ^ 2 = -1 := by
  haveI : Fact l.Prime := ⟨hl⟩
  have hd : (t ^ 2) ^ l = t ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul, htl]; ring
  have hmem : t ^ 2 ∈ (⊥ : Subfield K) := (Subfield.mem_bot_iff_pow_eq_self K l).2 hd
  obtain ⟨d, hdd⟩ := (mem_bot_iff_intCast l K).1 hmem
  have hd0 : (d : ZMod l) ≠ 0 := by
    intro h
    have := congrArg (ZMod.castHom (dvd_refl l) K) h
    rw [map_intCast, map_zero, hdd] at this
    exact ht (pow_eq_zero_iff (two_ne_zero) |>.1 this)
  have hodd : Fintype.card (ZMod l) % 2 = 1 := by
    rw [ZMod.card]; exact Nat.odd_iff.1 (hl.odd_of_ne_two h2)
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := ZMod l)
    (f := Polynomial.X ^ 2 + Polynomial.C 1) (g := Polynomial.C (-(d : ZMod l)) * Polynomial.X ^ 2)
    (Polynomial.degree_X_pow_add_C (by norm_num) 1)
    (Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.2 hd0)) hodd
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective b
  refine ⟨a, b, ?_⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C] at hab
  have := congrArg (ZMod.castHom (dvd_refl l) K) hab
  simp only [map_add, map_mul, map_pow, map_neg, map_one, map_intCast, map_zero] at this
  rw [hdd] at this
  linear_combination this

variable {C : Type} [Field C] {V : VF C}

theorem mm_iff {x : C} : V.MM x ↔ ∃ c : ℝ, 0 < c ∧ V.Ge c x := by
  unfold VF.MM VF.Ge
  induction V.v x using WithTop.recTopCoe with
  | top => exact ⟨fun _ => ⟨1, one_pos, le_top⟩, fun _ => by simp⟩
  | coe t =>
    constructor
    · intro h
      exact ⟨t, by exact_mod_cast h, le_rfl⟩
    · rintro ⟨c, hc, h⟩
      have : c ≤ t := by exact_mod_cast h
      exact_mod_cast hc.trans_le this

theorem mm_or {x y : C} (h : V.MM (x * y)) : V.MM x ∨ V.MM y := by
  unfold VF.MM at *
  by_contra hn
  push Not at hn
  rw [V.v.map_mul] at h
  exact absurd h (not_lt.2 (add_nonpos hn.1 hn.2))

theorem not_mm_one : ¬ V.MM (1 : C) := by simp [VF.MM]

def maxId (V : VF C) : Ideal V.RR where
  carrier := {x | V.MM (x : C)}
  add_mem' := by
    intro a b ha hb
    exact V.v.map_lt_add ha hb
  zero_mem' := by simp [VF.MM]
  smul_mem' := by
    intro c x hx
    obtain ⟨e, he, h⟩ := mm_iff.1 hx
    exact mm_iff.2 ⟨e, he, VF.Ge.mul_int c.2 h⟩

theorem maxId_prime (V : VF C) : (maxId V).IsPrime :=
  ⟨fun h => not_mm_one (V := V) ((Ideal.eq_top_iff_one _).1 h), fun h => mm_or h⟩

theorem exists_residue (V : VF C) :
    ∃ (K : Type) (_ : Field K) (φ : V.RR →+* K), ∀ x, φ x = 0 ↔ V.MM (x : C) := by
  haveI := maxId_prime V
  refine ⟨FractionRing (V.RR ⧸ maxId V), inferInstance,
    (algebraMap (V.RR ⧸ maxId V) _).comp (Ideal.Quotient.mk _), fun x => ?_⟩
  rw [RingHom.comp_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  rfl

theorem mm_l : V.MM (V.l : C) := mm_iff.2 ⟨1, one_pos, VF.ge_l⟩

theorem exists_norm_congr (h2 : V.l ≠ 2) (t : C) (ht : V.v t = 0) (htl : V.MM (t ^ V.l + t)) :
    ∃ a b : ℤ, V.MM ((a : C) ^ 2 - (b : C) ^ 2 * t ^ 2 + 1) := by
  obtain ⟨K, _, φ, hφ⟩ := exists_residue V
  haveI : Fact V.l.Prime := ⟨V.l_prime⟩
  haveI : CharP K V.l := by
    rw [CharP.charP_iff_prime_eq_zero V.l_prime, ← map_natCast φ, hφ]
    simpa using mm_l
  let T : V.RR := ⟨t, by show V.Ge 0 t; simp [VF.Ge, ht]⟩
  have h1 : φ T ≠ 0 := by
    rw [Ne, hφ]; simp [T, VF.MM, ht]
  have h3 : φ T ^ V.l = -φ T := by
    rw [← add_eq_zero_iff_eq_neg, ← map_pow, ← map_add, hφ]
    simpa [T] using htl
  obtain ⟨a, b, hab⟩ := exists_norm_eq_neg_one K V.l V.l_prime h2 (φ T) h1 h3
  refine ⟨a, b, ?_⟩
  have : φ ((a : V.RR) ^ 2 - (b : V.RR) ^ 2 * T ^ 2 + 1) = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_intCast, map_one, hab]; ring
  rw [hφ] at this
  simpa [T] using this

theorem ge_pow_sub_one {s : C} {w : ℝ} (hw : 0 ≤ w) (h : V.Ge w (s - 1)) (i : ℕ) : V.Ge w (s ^ i - 1) := by
  have hs : V.Ge 0 s := by simpa using (h.mono hw).add VF.Ge.one
  rw [← geom_sum_mul]
  exact VF.Ge.mul_int (VF.Ge.sum fun j _ => hs.pow j) h

theorem ge_pow_l_pow {s : C} {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (h : V.Ge c (s - 1)) (k : ℕ) :
    V.Ge ((k + 1) * c) (s ^ V.l ^ k - 1) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ, pow_mul, ← geom_sum_mul]
    have h1 : V.Ge c (∑ i ∈ Finset.range V.l, (s ^ V.l ^ k) ^ i) := by
      have : ∑ i ∈ Finset.range V.l, (s ^ V.l ^ k) ^ i
          = (V.l : C) + ∑ i ∈ Finset.range V.l, ((s ^ V.l ^ k) ^ i - 1) := by
        simp [Finset.sum_sub_distrib]
      rw [this]
      refine (VF.ge_l.mono hc1).add (VF.Ge.sum fun i _ => ?_)
      rw [← pow_mul]; exact ge_pow_sub_one hc.le h _
    refine (h1.mul ih).mono (le_of_eq ?_)
    push_cast; ring

theorem exists_odd_pow (h2 : V.l ≠ 2) {s : C} (h : V.MM (s - 1)) (N : ℕ) :
    ∃ m : ℕ, V.Ge N (s ^ (2 * m + 1) - 1) := by
  obtain ⟨e, he, h⟩ := mm_iff.1 h
  have hc : 0 < min e 1 := lt_min he one_pos
  obtain ⟨k, hk⟩ := exists_nat_ge ((N : ℝ) / min e 1)
  obtain ⟨m, hm⟩ := (V.l_prime.odd_of_ne_two h2).pow (n := k)
  refine ⟨m, ?_⟩
  rw [← hm]
  refine (ge_pow_l_pow hc (min_le_right _ _) (h.mono (min_le_left _ _)) k).mono ?_
  rw [div_le_iff₀ hc] at hk
  nlinarith

theorem ge_inv {s : C} (hs : ¬ V.MM s) : V.Ge 0 s⁻¹ := by
  unfold VF.MM at hs
  unfold VF.Ge
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have h : V.v s + V.v s⁻¹ = 0 := by rw [← V.v.map_mul, mul_inv_cancel₀ hs0, V.v.map_one]
  have : V.v s + V.v s⁻¹ ≤ 0 + V.v s⁻¹ := by gcongr; exact not_lt.1 hs
  rw [h, zero_add] at this
  exact this

theorem ge_half (h2 : V.l ≠ 2) : V.Ge 0 (2 : C)⁻¹ := by
  refine ge_inv fun h => not_mm_one (V := V) ?_
  obtain ⟨m, hm⟩ := V.l_prime.odd_of_ne_two h2
  obtain ⟨e, he, h⟩ := mm_iff.1 h
  have : (1 : C) = V.l - m * 2 := by rw [hm]; push_cast; ring
  rw [this]
  exact mm_iff.2 ⟨min e 1, lt_min he one_pos, (VF.ge_l.mono (min_le_right _ _)).sub
    ((VF.Ge.mul_int (VF.ge_natCast m) h).mono (min_le_left _ _))⟩

theorem exists_half [CharZero C] (h2 : V.l ≠ 2) (N : ℕ) : ∃ m : ℕ, V.Ge N ((2 : C)⁻¹ - m) := by
  obtain ⟨m, hm⟩ := (V.l_prime.odd_of_ne_two h2).pow (n := N)
  refine ⟨m + 1, ?_⟩
  have hp : V.Ge N ((V.l : C) ^ N) := by
    clear hm
    induction N with
    | zero => simpa using VF.Ge.one
    | succ n ih => rw [pow_succ]; push_cast; exact ih.mul VF.ge_l
  have : (2 : C)⁻¹ - (m + 1 : ℕ) = -(2⁻¹ * (V.l : C) ^ N) := by
    rw [← Nat.cast_pow, hm]; push_cast; ring
  rw [this]
  exact (VF.Ge.mul_int (ge_half h2) hp).neg

theorem exists_pair [IsAlgClosed C] (h2 : V.l ≠ 2) (O : Type) [CommRing O] [StarRing O]
    (em : ZMod 2 → (O →+* C)) (hint : ∀ a x, V.Ge 0 (em a x))
    (hfr : ∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) (hsep : ∃ x, V.v (em 0 x - em 1 x) = 0)
    (hst : ∀ a x, em a (star x) = em (a + 1) x) :
    ∃ z : ZMod 2 → C, (∀ a, z (a + 1) * z a = -1) ∧ (∀ a, V.Ge 0 (z a)) ∧
      ∀ N : ℕ, ∃ y : O, ∀ a, V.Ge N (z a - em a y) := by
  obtain ⟨x, hx⟩ := hsep
  have e11 : (1 : ZMod 2) + 1 = 0 := rfl
  have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  set t := em 0 x - em 1 x with htdef
  have d0 : em 0 (x - star x) = t := by rw [map_sub, hst, zero_add]
  have d1 : em 1 (x - star x) = -t := by rw [map_sub, hst, e11, htdef]; ring
  have htl : V.MM (t ^ V.l + t) := by
    have := hfr 0 (x - star x)
    rw [zero_add, d0, d1] at this
    unfold VF.MM at this ⊢
    rw [← V.v.map_neg]
    convert this using 2; ring
  obtain ⟨a, b, hab⟩ := exists_norm_congr h2 t hx htl
  set w : O := a + b * (x - star x) with hw
  have w0 : em 0 w = a + b * t := by rw [hw, map_add, map_mul, d0]; simp
  have w1 : em 1 w = a - b * t := by rw [hw, map_add, map_mul, d1]; simp [sub_eq_add_neg]
  set u : C := -((a : C) ^ 2 - (b : C) ^ 2 * t ^ 2) with hu
  have hwu : ∀ c, em (c + 1) w * em c w = -u := by
    intro c
    rcases hcases c with rfl | rfl
    · rw [zero_add, w0, w1, hu]; ring
    · rw [e11, w0, w1, hu]; ring
  obtain ⟨s, hsu, hs1⟩ : ∃ s : C, s ^ 2 = u ∧ V.MM (s - 1) := by
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq u (n := 2) two_pos
    have : V.MM ((s - 1) * (-s - 1)) := by
      convert hab using 1
      linear_combination -hs - hu
    rcases mm_or this with h | h
    · exact ⟨s, hs, h⟩
    · exact ⟨-s, by rw [neg_sq, hs], h⟩
  have hns : ¬ V.MM s := by
    intro h
    apply not_mm_one (V := V)
    have := V.v.map_lt_add h (show 0 < V.v (-(s - 1)) by rw [V.v.map_neg]; exact hs1)
    simpa [VF.MM] using this
  have hs0 : s ≠ 0 := by rintro rfl; exact hns (by simp [VF.MM])
  refine ⟨fun c => em c w * s⁻¹, fun c => ?_, fun c => VF.Ge.mul_int (hint c w) (ge_inv hns), fun N => ?_⟩
  · have := hwu c
    field_simp
    linear_combination this + hsu
  · obtain ⟨m, hm⟩ := exists_odd_pow h2 hs1 N
    refine ⟨w * (-(star w * w)) ^ m, fun c => ?_⟩
    have : em c w * s⁻¹ - em c (w * (-(star w * w)) ^ m) = -(em c w * s⁻¹ * (s ^ (2 * m + 1) - 1)) := by
      rw [map_mul, map_pow, map_neg, map_mul, hst, hwu, neg_neg, ← hsu, ← pow_mul]
      field_simp
      ring
    simp only
    rw [this]
    exact (VF.Ge.mul_int (VF.Ge.mul_int (hint c w) (ge_inv hns)) hm).neg

theorem main : ∀ (C : Type) [Field C] [CharZero C] [IsAlgClosed C] (V : VF C), V.l ≠ 2 → (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → ∀ (O : Type) [CommRing O] [StarRing O] (em : ZMod 2 → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → (∃ x, V.v (em 0 x - em 1 x) = 0) → (∀ a x, em a (star x) = em (a + 1) x) → ∃ gm : ZMod 2 → Matrix (Fin 2) (Fin 2) C, (∀ N : ℕ, ∃ M : Matrix (Fin 2) (Fin 2) O, ∀ a r s, V.Ge N (gm a r s - em a (M r s))) ∧ ∀ a (s s' : Fin 2), ∑ r, gm (a + 1) r s * gm a r s' = if s = s' then 0 else 1 := by
  intro C _ _ _ V h2 _ O _ _ em hint hfr hsep hst
  obtain ⟨z, hz, hz0, hzN⟩ := exists_pair h2 O em hint hfr hsep hst
  refine ⟨fun a => !![1, 2⁻¹; z a, -(z a * 2⁻¹)], fun N => ?_, fun a s s' => ?_⟩
  · obtain ⟨y, hy⟩ := hzN N
    obtain ⟨m, hm⟩ := exists_half h2 N
    refine ⟨!![1, m; y, -(y * m)], fun a r s => ?_⟩
    fin_cases r <;> fin_cases s
    · simpa using VF.Ge.zero _
    · simpa using hm
    · simpa using hy a
    · have := ((VF.Ge.mul_int (hz0 a) hm).add (VF.Ge.mul_int (VF.ge_natCast m) (hy a))).neg
      convert this using 1
      simp; ring
  · have := hz a
    fin_cases s <;> fin_cases s' <;> simp [Fin.sum_univ_two]
    · linear_combination this
    · linear_combination (-2⁻¹) * this
    · linear_combination (-2⁻¹) * this
    · linear_combination (4⁻¹) * this

end GlobalTheory.InertHyperbolic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPlaceUOfFrobeniusOrbit
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.OrbitPlace

open ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs in

theorem mem_emb_of_congr_pow (A : Type) [CommRing A] (p : ℕ) [Fact p.Prime] (O : Type)
    [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O] (hp : ¬ IsUnit (p : O))
    (e : ℤ_[p] ⊗[ℤ] A) (he : e * e = e) (σ σ' : A →+* O)
    (h : ∀ x, σ' x - σ x ^ p ∈ IsLocalRing.maximalIdeal O) (hσ : σ ∈ Emb (O := O) e) :
    σ' ∈ Emb (O := O) e := by
  obtain ⟨s, x, hx⟩ := GlobalTheory.CharDepth.padicTensor_eq_mul_add A p e
  have hp0 : IsLocalRing.residue O (p : O) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 hp
  have key : ∀ ρ : A →+* O,
      IsLocalRing.residue O (tauExt ρ e) = IsLocalRing.residue O (ρ x) := by
    intro ρ
    have h1 : tauExt (p := p) ρ ((1 : ℤ_[p]) ⊗ₜ[ℤ] x) = ρ x := by simp [tauExt]
    rw [hx, map_add, map_mul, map_natCast, h1, map_add, map_mul, hp0, zero_mul, zero_add]
  have h1 : IsLocalRing.residue O (σ x) = 1 := by
    have : tauExt σ e = 1 := hσ
    rw [← key, this, map_one]
  have h2 : IsLocalRing.residue O (tauExt σ' e) = 1 := by
    have := (IsLocalRing.residue_eq_zero_iff _).2 (h x)
    rw [map_sub, map_pow, h1, one_pow, sub_eq_zero] at this
    rw [key, this]
  have hu : IsUnit (tauExt σ' e) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, h2]
    exact one_ne_zero
  have hid : tauExt σ' e * tauExt σ' e = tauExt σ' e * 1 := by rw [← map_mul, he, mul_one]
  exact hu.mul_left_cancel hid

theorem exists_placeU_of_frobenius_orbit : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [IsLocalRing O] [Algebra ℤ_[p] O], ¬ IsUnit (p : O) → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (d : ℕ) [NeZero d] (τ : ZMod d → (𝓞 E →+* O)), Function.Injective τ → (∀ s x, τ (s + 1) x - τ s x ^ p ∈ IsLocalRing.maximalIdeal O) → ∃ (w : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.PlaceU p (𝓞 E)) (_ : w.n = d) (t : Fin w.n ≃ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e), (∀ j : Fin w.n, ((t j : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e) : 𝓞 E →+* O) = τ ((j.val : ℕ) : ZMod d)) ∧ ∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)), IsUnit (Matrix.det (Matrix.of fun i j => ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt ((t j : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e) : 𝓞 E →+* O) (b i : ℤ_[p] ⊗[ℤ] 𝓞 E))) := by
  intro E _ _ p hpp C _ _ _ v O _ _ hv _ _ hp hd d _ τ hτ hfr
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  obtain ⟨w, hw⟩ := GlobalTheory.exists_placeU_mem_emb p (𝓞 E) O (τ 0)
  have hsep := GlobalTheory.ringOfIntegers_hom_eq_of_congr_maximalIdeal E p hpp.out hd C v O hv hp
  have hmem : ∀ k : ℕ, τ (k : ZMod d) ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e := by
    intro k
    induction k with
    | zero => simpa using hw
    | succ k ih =>
      rw [Nat.cast_succ]
      exact mem_emb_of_congr_pow _ p O hp w.e w.idem _ _ (hfr _) ih
  have hpow : ∀ (k : ℕ) x, IsLocalRing.residue O (τ (k : ZMod d) x) =
      IsLocalRing.residue O (τ 0 x) ^ (p ^ k) := by
    intro k x
    induction k with
    | zero => simp
    | succ k ih =>
      have := (IsLocalRing.residue_eq_zero_iff _).2 (hfr (k : ZMod d) x)
      rw [map_sub, map_pow, sub_eq_zero] at this
      rw [Nat.cast_succ, this, ih, ← pow_mul, pow_succ]
  have hsurj : ∀ σ ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e, ∃ s, τ s = σ := by
    intro σ hσ
    obtain ⟨i, hi⟩ := GlobalTheory.EmbFrob.exists_frobenius_pow p (𝓞 E) C v O hv hp w (τ 0) σ hw hσ
    refine ⟨(i : ZMod d), hsep _ _ fun x => ?_⟩
    have h1 : σ x - τ 0 x ^ (p ^ i) ∈ IsLocalRing.maximalIdeal O := by
      intro hu
      exact (hi x).ne (hv.one_of_isUnit hu)
    have := (IsLocalRing.residue_eq_zero_iff _).2 h1
    rw [map_sub, map_pow, sub_eq_zero] at this
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hpow, this, sub_self]
  have hmem' : ∀ s : ZMod d, τ s ∈ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e := by
    intro s
    have := hmem s.val
    rwa [ZMod.natCast_zmod_val] at this
  have hbij : Function.Bijective
      (fun s : ZMod d => (⟨τ s, hmem' s⟩ : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e)) :=
    ⟨fun a b h => hτ (congrArg Subtype.val h), fun σ => by
      obtain ⟨s, hs⟩ := hsurj σ.1 σ.2
      exact ⟨s, Subtype.ext hs⟩⟩
  obtain ⟨⟨t₀⟩, -⟩ := GlobalTheory.EmbCount.card_emb E p C v O hv w.e w.idem
  have hn : w.n = d := by
    have h1 := Nat.card_congr (t₀.trans (Equiv.ofBijective _ hbij).symm)
    rw [Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    exact h1
  have hcast : Function.Bijective (fun j : Fin w.n => ((j.val : ℕ) : ZMod d)) := by
    refine ⟨fun a b h => ?_, fun s => ⟨⟨s.val, hn ▸ ZMod.val_lt s⟩, ZMod.natCast_zmod_val s⟩⟩
    have h' := congrArg ZMod.val h
    simp only [ZMod.val_natCast] at h'
    rw [Nat.mod_eq_of_lt (hn ▸ a.2), Nat.mod_eq_of_lt (hn ▸ b.2)] at h'
    exact Fin.ext h'
  let t : Fin w.n ≃ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := O) w.e :=
    (Equiv.ofBijective _ hcast).trans (Equiv.ofBijective _ hbij)
  refine ⟨w, hn, t, fun j => rfl, ?_⟩
  exact GlobalTheory.tau_basis_unit_determinant.exists_basis_isUnit_det p (𝓞 E) O w (fun j => (t j).1) (fun j => (t j).2)
    (fun j j' h => t.injective (Subtype.ext (hsep _ _ h)))

end GlobalTheory.OrbitPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicConnectionValueBaseChangeFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicConnectionValue_baseChange_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S S' : Type) [CommRing S] [Algebra c.F S] [Field S'] [Algebra c.F S'] (ψ : S →ₐ[c.F] S') (y : FrPt Xo c S) (y' : FrPt Xo c S'), FrMap ψ y y' → ∀ (h : ptO Xo y'.x ⟶ ptO Xo y.x), h.left = spMap ψ.toRingHom → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (N : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), (∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) → ψ (∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b)) = ∑ m ∈ P.support, algebraMap c.F S' (P.coeff m) * ∏ b, nab y' ((N : ℤ) ^ 2) (F' b) (colOf m b) := by
  first | exact @GlobalTheory.harmonicValue_baseChange_field | exact GlobalTheory.harmonicValue_baseChange_field | (intros; apply GlobalTheory.harmonicValue_baseChange_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeValueLePlanBlocksStatement
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPrime_value_le_planBlocks : ∀ (P : RF.Par) (l : ℕ) (C1 : ℝ), ParOK P → 5 ≤ l → ∀ (Pk : RF.PkgInert P l C1) (p : ∀ z, Plan l P.d (RF.alongOrb P z Pk.W)),
  (∀ z ∈ Pk.Z, ∀ a i, i0 P.k l ≤ i → (p z).y a i = 0) →
  (∀ z ∈ Pk.Z, ∀ a i, (p z).y a i ≠ 0 → (RF.GlobalTheory.bi (RF.bg a) a i ((p z).y a i)).Attains (Pk.R.X z) (Pk.R.F z) (RF.blockBd l (P.k - 1) P.m i ((p z).y a i))) →
  Pk.ν ≤ (∑ z ∈ Pk.Z, (p z).bound (P.k - 1) P.m) + Pk.rest / ((l : ℝ) - 1) := by
  first | exact @GlobalTheory.PlanValue.val_le_plan | exact GlobalTheory.PlanValue.val_le_plan | (intros; apply GlobalTheory.PlanValue.val_le_plan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LargePrimePackagesDepthNonposStatement
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.largePrime_packages_depth_nonpos : ZeroBd := by
  first | exact @GlobalTheory.GoodDepth.zeroBd | exact GlobalTheory.GoodDepth.zeroBd | (intros; apply GlobalTheory.GoodDepth.zeroBd <;> assumption)
end

