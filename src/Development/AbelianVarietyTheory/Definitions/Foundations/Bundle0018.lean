import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0017
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.ExistsEqSubOfMemCob
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

namespace GlobalTheory.LambdaValuationPowers

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def lamv (l : ℕ) [Fact l.Prime] (m : ℕ) (s : G ℚ Ω) : Qbar l :=
  algebraMap ℚ_[l] (Qbar l) ((((cycZ (F := ℚ) (Ω := Ω) l s : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) - 1) / (l : Qbar l) ^ m

def HTCoAt (A : ValuationSubring Ω) (j : Ω →+* Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₀ : ℕ)
    (y : (ZMod (l ^ m))ˣ) (h : Qbar l) : Prop :=
  ∃ (q : ℕ) (o : Fin q → Qbar l) (w : Fin q → Ω), (∀ i, ‖o i‖ ≤ 1 ∧ ‖j (w i)‖ ≤ 1) ∧
    ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 →
      Cg (m - c₀) (Z m s y) (h * lamv l m s + ∑ i, o i * (j (s (w i)) - j (w i)))

theorem natCast_ne_zero : (l : Qbar l) ≠ 0 := by
  have : CharZero (Qbar l) := charZero_of_injective_algebraMap (algebraMap ℚ_[l] (Qbar l)).injective
  exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero

theorem norm_natCast_lt_one : ‖(l : Qbar l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem pow_mul_lamv (m : ℕ) (s : G ℚ Ω) :
    (l : Qbar l) ^ m * lamv l m s = algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
  rw [lamv, mul_div_cancel₀ _ (pow_ne_zero m natCast_ne_zero), map_sub, map_one]

@[simp] theorem lamv_one (m : ℕ) : lamv l m (1 : G ℚ Ω) = 0 := by
  simp [lamv]

theorem lamv_mul (m : ℕ) (s t : G ℚ Ω) :
    lamv l m (s * t) = lamv l m s + lamv l m t + (l : Qbar l) ^ m * lamv l m s * lamv l m t := by
  apply mul_left_cancel₀ (pow_ne_zero m (natCast_ne_zero (l := l)))
  have hs := pow_mul_lamv (l := l) m s
  have ht := pow_mul_lamv (l := l) m t
  rw [pow_mul_lamv, map_mul, Units.val_mul, PadicInt.coe_mul, map_mul]
  linear_combination (-(algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l t : ℤ_[l]ˣ) : ℤ_[l]))) * hs -
    ((l : Qbar l) ^ m * lamv l m s + 1) * ht

theorem exists_lamv_eq {m : ℕ} {s : G ℚ Ω} (hs : cycMod ℚ Ω l m s = 1) :
    ∃ a : ℤ_[l], ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ m * a ∧ lamv l m s = algebraMap ℤ_[l] (Qbar l) a := by
  have h1 : PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    simpa [cycMod] using congrArg Units.val hs
  have h2 : ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈ RingHom.ker (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)) := by
    rw [RingHom.mem_ker, map_sub, h1, map_one, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h2
  obtain ⟨a, ha⟩ := h2
  have h3 : ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ m * a := by rw [← ha]; ring
  refine ⟨a, h3, mul_left_cancel₀ (pow_ne_zero m (natCast_ne_zero (l := l))) ?_⟩
  rw [pow_mul_lamv, h3, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l)]
  simp

theorem norm_le_one_of_mem {c : Coef l} {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] a := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨a, ha⟩ : c.O)).map c.O.val
  have hq : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  change spectralValue (minpoly ℚ_[l] a) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

theorem norm_lamv_le_one {m : ℕ} {s : G ℚ Ω} (hs : cycMod ℚ Ω l m s = 1) : ‖lamv l m s‖ ≤ 1 := by
  obtain ⟨a, -, ha⟩ := exists_lamv_eq hs
  rw [ha, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), norm_algebraMap']
  exact a.2

def cob (c : Coef l) (A : ValuationSubring Ω) (j : Ω →+* Qbar l) : Submodule c.O (G ℚ Ω → Qbar l) :=
  Submodule.span c.O {f | ∃ w ∈ A, f = fun s : G ℚ Ω => j (s w) - j w}

section Cob

variable {c : Coef l} {A : ValuationSubring Ω} {j : Ω →+* Qbar l}

theorem sub_mem_cob {w : Ω} (hw : w ∈ A) : (fun s : G ℚ Ω => j (s w) - j w) ∈ cob c A j :=
  Submodule.subset_span ⟨w, hw, rfl⟩

theorem mem_cob_iff {f : G ℚ Ω → Qbar l} : f ∈ cob c A j ↔ ∃ (q : ℕ) (o : Fin q → Qbar l) (w : Fin q → Ω),
    (∀ i, o i ∈ c.O ∧ w i ∈ A) ∧ ∀ s, f s = ∑ i, o i * (j (s (w i)) - j (w i)) := by
  constructor
  · intro hf
    obtain ⟨q, o, g, hg⟩ := Submodule.mem_span_set'.1 hf
    choose w hw hgw using fun i => (g i).2
    refine ⟨q, fun i => o i, w, fun i => ⟨(o i).2, hw i⟩, fun s => ?_⟩
    rw [← hg, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hgw i]; rfl
  · rintro ⟨q, o, w, h, hf⟩
    have e : f = ∑ i, (⟨o i, (h i).1⟩ : c.O) • fun s : G ℚ Ω => j (s (w i)) - j (w i) := by
      funext s; rw [hf s, Finset.sum_apply]; rfl
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (sub_mem_cob (h i).2)

theorem mul_mem_cob {f : G ℚ Ω → Qbar l} (hf : f ∈ cob c A j) {a : Qbar l} (ha : a ∈ c.O) :
    (fun s => a * f s) ∈ cob c A j :=
  (cob c A j).smul_mem ⟨a, ha⟩ hf

theorem apply_one_of_mem_cob {f : G ℚ Ω → Qbar l} (hf : f ∈ cob c A j) : f 1 = 0 := by
  obtain ⟨q, o, w, -, h⟩ := mem_cob_iff.1 hf
  simp [h]

theorem exists_eq_sub_of_mem_cob (hj : ReciprocityTheory.Neutral.Cmp.Compat l A j) {f : G ℚ Ω → Qbar l} (hf : f ∈ cob c A j) :
    ∃ x : Qbar l, ‖x‖ ≤ 1 ∧ ∀ (σ : Qbar l ≃+* Qbar l) (s : G ℚ Ω), (∀ w, j (s w) = σ (j w)) → (∀ a ∈ c.O, σ a = a) →
      f s = σ x - x := by
  obtain ⟨q, o, w, h, hf⟩ := mem_cob_iff.1 hf
  refine ⟨∑ i, o i * j (w i), ?_, fun σ s hs hσ => ?_⟩
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (norm_le_one_of_mem (h i).1) (norm_nonneg _) ((hj _).1 (h i).2)
  · rw [hf s, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hσ _ (h i).1, hs]
    ring

end Cob

def HTCoIn (c : Coef l) (A : ValuationSubring Ω) (j : Ω →+* Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l)
    (m c₀ : ℕ) (y : (ZMod (l ^ m))ˣ) (h : Qbar l) : Prop :=
  ReciprocityTheory.Neutral.Cmp.Compat l A j ∧ ∃ f ∈ cob c A j, ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 →
    Cg (m - c₀) (Z m s y) (h * lamv l m s + f s)

section Co

variable {c : Coef l} {A : ValuationSubring Ω} {j : Ω →+* Qbar l} {Z Z' : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l}
  {m c₀ : ℕ} {y : (ZMod (l ^ m))ˣ} {h h' : Qbar l}

namespace HTCoIn

theorem compat (H : HTCoIn c A j Z m c₀ y h) : ReciprocityTheory.Neutral.Cmp.Compat l A j := H.1

theorem mono (H : HTCoIn c A j Z m c₀ y h) {c₁ : ℕ} (hc : c₀ ≤ c₁) : HTCoIn c A j Z m c₁ y h := by
  obtain ⟨hj, f, hf, H⟩ := H
  refine ⟨hj, f, hf, fun s hs hm => (H s hs hm).trans ?_⟩
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) norm_natCast_lt_one.le (by omega)

theorem add (H : HTCoIn c A j Z m c₀ y h) (H' : HTCoIn c A j Z' m c₀ y h') :
    HTCoIn c A j (fun r s x => Z r s x + Z' r s x) m c₀ y (h + h') := by
  obtain ⟨hj, f, hf, H⟩ := H
  obtain ⟨-, f', hf', H'⟩ := H'
  refine ⟨hj, f + f', add_mem hf hf', fun s hs hm => ?_⟩
  have e : Z m s y + Z' m s y - ((h + h') * lamv l m s + (f + f') s) =
      (Z m s y - (h * lamv l m s + f s)) + (Z' m s y - (h' * lamv l m s + f' s)) := by
    rw [Pi.add_apply]; ring
  unfold Cg
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (H s hs hm) (H' s hs hm))

theorem mul_left (H : HTCoIn c A j Z m c₀ y h) {a : Qbar l} (ha : a ∈ c.O) :
    HTCoIn c A j (fun r s x => a * Z r s x) m c₀ y (a * h) := by
  obtain ⟨hj, f, hf, H⟩ := H
  refine ⟨hj, _, mul_mem_cob hf ha, fun s hs hm => ?_⟩
  have e : a * Z m s y - (a * h * lamv l m s + a * f s) = a * (Z m s y - (h * lamv l m s + f s)) := by ring
  unfold Cg
  rw [e, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_mem ha)).trans (H s hs hm)

theorem sub (H : HTCoIn c A j Z m c₀ y h) (H' : HTCoIn c A j Z' m c₀ y h') :
    HTCoIn c A j (fun r s x => Z r s x - Z' r s x) m c₀ y (h - h') := by
  simpa [sub_eq_add_neg] using H.add (H'.mul_left (c.O.neg_mem c.O.one_mem))

theorem congr (H : HTCoIn c A j Z m c₀ y h) {y' : (ZMod (l ^ m))ˣ} {g : G ℚ Ω → Qbar l} (hg : g ∈ cob c A j)
    (hZ : ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → Cg (m - c₀) (Z' m s y') (Z m s y + g s)) (hh : Cg (m - c₀) h h') :
    HTCoIn c A j Z' m c₀ y' h' := by
  obtain ⟨hj, f, hf, H⟩ := H
  refine ⟨hj, f + g, add_mem hf hg, fun s hs hm => ?_⟩
  have e : Z' m s y' - (h' * lamv l m s + (f + g) s) =
      (Z' m s y' - (Z m s y + g s)) + ((Z m s y - (h * lamv l m s + f s)) + (h - h') * lamv l m s) := by
    rw [Pi.add_apply]; ring
  unfold Cg
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hZ s hs hm) ?_)
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (H s hs hm) ?_)
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (norm_lamv_le_one hm)).trans hh

theorem cg_one (H : HTCoIn c A j Z m c₀ y h) : Cg (m - c₀) (Z m 1 y) 0 := by
  obtain ⟨-, f, hf, H⟩ := H
  simpa [apply_one_of_mem_cob hf] using H 1 (one_mem _) (map_one _)

end HTCoIn

theorem htCoIn_lamv (hj : ReciprocityTheory.Neutral.Cmp.Compat l A j) {f : G ℚ Ω → Qbar l} (hf : f ∈ cob c A j) (m c₀ : ℕ)
    (y : (ZMod (l ^ m))ˣ) (h : Qbar l) : HTCoIn c A j (fun r s _ => h * lamv l r s + f s) m c₀ y h :=
  ⟨hj, f, hf, fun _ _ _ => by simp [Cg]⟩

end Co

example [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (w : Ω) (hw : w ∈ A) :
    ∃ j : Ω →+* Qbar l, ∀ (m : ℕ) (y : (ZMod (l ^ m))ˣ),
      HTCoIn c A j (fun r s _ => lamv l r s + (j (s w) - j w)) m 0 y 1 := by
  obtain ⟨j, hj⟩ := ReciprocityTheory.Neutral.Cmp.exists_compat (p := l) ℚ A hA
  exact ⟨j, fun m y => by simpa using htCoIn_lamv hj (sub_mem_cob (c := c) hw) m 0 y 1⟩

example (c : Coef l) (A : ValuationSubring Ω) (j : Ω →+* Qbar l) {m c₀ : ℕ} (hm : c₀ < m) (y : (ZMod (l ^ m))ˣ) (h : Qbar l) :
    ¬ HTCoIn c A j (fun _ _ _ => 1) m c₀ y h := by
  intro H
  have h1 := H.cg_one
  rw [Cg, sub_zero, norm_one, norm_pow] at h1
  exact absurd (pow_lt_one₀ (norm_nonneg _) norm_natCast_lt_one (by omega)) (not_lt.2 h1)

example (c : Coef l) (j : Ω →+* Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₀ : ℕ) (y : (ZMod (l ^ m))ˣ)
    (h : Qbar l) : ¬ HTCoIn c ⊤ j Z m c₀ y h := by
  intro H
  have h1 := (H.compat ((l : Ω)⁻¹)).1 trivial
  rw [map_inv₀, map_natCast, norm_inv, inv_le_one₀ (norm_pos_iff.2 natCast_ne_zero)] at h1
  exact absurd norm_natCast_lt_one (not_lt.2 h1)

end GlobalTheory.LambdaValuationPowers
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.IwSys2
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def Layer2 (c : Coef l) (A : ValuationSubring Ω) (ν : G ℚ Ω → (Qbar l)ˣ) (r : ℕ)
    (z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) : Prop :=
  (∀ s x, z s x ∈ c.O) ∧ ∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, ∀ x,
    z (s * t) x = z s x + (ν s : Qbar l) * z t (x * (cycMod ℚ Ω l r s)⁻¹)

def IwSys2 (c : Coef l) (A : ValuationSubring Ω) (ν : G ℚ Ω → (Qbar l)ˣ) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) :
    Prop :=
  (∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, ν (s * t) = ν s * ν t) ∧ (∀ r, Layer2 c A ν r (Z r)) ∧
    ∀ r s (x : (ZMod (l ^ r))ˣ),
      Z r s x = ∑ x' ∈ (Finset.univ.filter fun x' : (ZMod (l ^ (r + 1)))ˣ =>
        Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom x' = x), Z (r + 1) s x'

end GlobalTheory.KZ

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.KumValUnique
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 PowerSeries

namespace GlobalTheory.Col

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def KumVal (n : ℕ) (ζ u : Ω) (s : G ℚ Ω) (k : ZMod (l ^ n)) : Prop :=
  ∃ v : Ω, v ^ (l ^ n) = u ∧ s v = ζ ^ k.val * v

def KumPres (A : ValuationSubring Ω) (n r : ℕ) (ζ : Ω) (Z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) {ι : Type} [Fintype ι]
    (u : ι → Ω) (o : ι → Qbar l) : Prop :=
  IsPrimitiveRoot ζ (l ^ n) ∧ n ≤ r ∧ (∀ i, u i ∈ A ∧ u i ≠ 0 ∧ (u i)⁻¹ ∈ A) ∧ (∀ i, ‖o i‖ ≤ 1) ∧
    ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l r s = 1 → s ζ = ζ →
      ∃ k : ι → ZMod (l ^ n), (∀ i, KumVal n ζ (u i) s (k i)) ∧ Cg n (Z s 1) (∑ i, o i * ((k i).val : Qbar l))

theorem kumVal_unique {n : ℕ} {ζ u : Ω} {s : G ℚ Ω} {k k' : ZMod (l ^ n)} (hζ : IsPrimitiveRoot ζ (l ^ n)) (hs : s ζ = ζ)
    (hu : u ≠ 0) (hk : KumVal n ζ u s k) (hk' : KumVal n ζ u s k') : k = k' := by
  obtain ⟨v, hv, hsv⟩ := hk
  obtain ⟨w, hw, hsw⟩ := hk'
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  have hv0 : v ≠ 0 := by rintro rfl; exact hu (by rw [← hv, zero_pow hpos.ne'])
  have hw0 : w ≠ 0 := by rintro rfl; exact hu (by rw [← hw, zero_pow hpos.ne'])
  have h1 : (w / v) ^ (l ^ n) = 1 := by rw [div_pow, hv, hw, div_self hu]
  obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one h1
  have hwv : w = ζ ^ j * v := by rw [hj]; field_simp
  have e1 : s w = ζ ^ k.val * w := by
    rw [hwv, map_mul, map_pow, hs, hsv]; ring
  have e2 : ζ ^ k.val = ζ ^ k'.val := by
    have := e1.symm.trans hsw
    exact mul_right_cancel₀ hw0 this
  exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt k) (ZMod.val_lt k') e2)

theorem kumVal_one (n : ℕ) (ζ : Ω) (s : G ℚ Ω) : KumVal (l := l) n ζ 1 s 0 :=
  ⟨1, one_pow _, by simp⟩

theorem kumPres_empty (A : ValuationSubring Ω) {n r : ℕ} {ζ : Ω} (hζ : IsPrimitiveRoot ζ (l ^ n)) (hnr : n ≤ r)
    (Z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (hZ : ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l r s = 1 → Z s 1 = 0) :
    KumPres A n r ζ Z (ι := Empty) (fun i => i.elim) (fun i => i.elim) := by
  refine ⟨hζ, hnr, fun i => i.elim, fun i => i.elim, fun s hs hc _ => ⟨fun i => i.elim, fun i => i.elim, ?_⟩⟩
  rw [Cg, hZ s hs hc, Finset.sum_eq_zero (fun i _ => i.elim), sub_zero, norm_zero]
  exact norm_nonneg _

example (A : ValuationSubring Ω) {n r : ℕ} {ζ : Ω} (Z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (o : Unit → Qbar l) :
    ¬ KumPres A n r ζ Z (fun _ : Unit => (0 : Ω)) o :=
  fun h => (h.2.2.1 ()).2.1 rfl

example (A : ValuationSubring Ω) {r : ℕ} (Z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) {ι : Type} [Fintype ι] (u : ι → Ω)
    (o : ι → Qbar l) : ¬ KumPres A 1 r (1 : Ω) Z u o := by
  rintro ⟨h, -⟩
  have := h.eq_orderOf
  rw [orderOf_one, pow_one] at this
  exact (Fact.out : l.Prime).one_lt.ne this.symm

theorem fix_of_cycMod [∀ i, HasEnoughRootsOfUnity Ω (l ^ i)] {n r : ℕ} (hnr : n ≤ r) {s : G ℚ Ω}
    (hs : cycMod ℚ Ω l r s = 1) {t : Ω} (ht : t ^ (l ^ n) = 1) : s t = t := by
  have ht' : t ^ (l ^ r) = 1 := by
    obtain ⟨d, hd⟩ := pow_dvd_pow l hnr
    rw [hd, pow_mul, ht, one_pow]
  have h1 := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) t ht'
  have h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val.toZModPow r = 1 := by
    have := congrArg Units.val hs
    simpa [cycMod, cycZ] using this
  rw [h2, ZMod.val_one_eq_one_mod] at h1
  have h3 : t ^ (1 % l ^ r) = t := by
    rcases Nat.lt_or_ge 1 (l ^ r) with h | h
    · rw [Nat.mod_eq_of_lt h, pow_one]
    · have e : l ^ r = 1 := le_antisymm h (Nat.one_le_pow _ _ (Fact.out : l.Prime).pos)
      rw [e, Nat.mod_self, pow_zero]
      rw [e, pow_one] at ht'
      exact ht'.symm
  exact h1.trans h3

end GlobalTheory.Col
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.LiftSL
section
noncomputable section

open scoped MatrixGroups Matrix
open Filter
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ ReciprocityTheory.Gal

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def liftK (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (a : X.Kl l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Kl l)))) : X.Khat l :=
  Classical.epsilon fun b : X.Khat l => AdicCompletion.eval (idl l) (X.Kl l) n b = a

open Classical in

def clsK (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (w : X.K) : X.Khat l :=
  if h : w ≠ 0 then liftK X l n (X.cls l n (Units.mk0 w h)) else 0

def liftSL (M : ℕ) (g : SL(2, ZMod M)) : SL(2, ℤ) :=
  Classical.epsilon fun γ : SL(2, ℤ) => Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ = g

open Classical in

def clsB (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n r N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ))
    (σ : Ω ≃ₐ[ℚ] Ω) : X.Fn l :=
  let M : ℕ := l ^ (r + n) * N
  haveI : NeZero M := ⟨Nat.mul_ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (NeZero.ne N)⟩
  let f : X.Fn l := fun u => (u 0) ^ (k - 2) • clsK X l n (wk4 X l n r N x c d σ)
  ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ Finset.univ.filter (fun γ : SL(2, ZMod M) =>
      γ ∈ (Gam N l).map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)))),
    X.act l ((g r₀ * liftSL M γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) f

def repC (l : ℕ) [Fact l.Prime] (r : ℕ) (x : (ZMod (l ^ r))ˣ) : Ω ≃ₐ[ℚ] Ω :=
  Classical.epsilon fun s : Ω ≃ₐ[ℚ] Ω => cycMod (F := ℚ) (Ω := Ω) l r s = x

def Yk4 (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : GlobalTheory.Ord2.R2 Ω l)
    (n r N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ) : Fin 2 → Qbar l :=
  GlobalTheory.Ord2.mat W (repC l r y) *ᵥ
    pr (clsB X l n r N x c d k g ((repC l r y)⁻¹ * s * repC l r (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)))

def Zk4 (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : GlobalTheory.Ord2.R2 Ω l)
    (N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (r : ℕ) (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ) : Qbar l :=
  limUnder atTop fun n : ℕ => Yk4 X l pr W n r N x c d k g s y 1

def chik4 (l : ℕ) [Fact l.Prime] (e : ℕ) (ψ : ZMod l → Qbar l) (r : ℕ) (y : (ZMod (l ^ r))ˣ) : Qbar l :=
  ((((y : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * ψ (((y : ZMod (l ^ r)).val : ℕ) : ZMod l)

def yk4 (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : GlobalTheory.Ord2.R2 Ω l)
    (N : ℕ) [NeZero N] (x : ZMod N) (c d k e : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (s : Ω ≃ₐ[ℚ] Ω) : Fin 2 → Qbar l :=
  limUnder atTop fun r : ℕ => GlobalTheory.KA.spec (chik4 l e ψ r) (Yk4 X l pr W r r N x c d k g) s

def nuk4 {l : ℕ} [Fact l.Prime] (W : GlobalTheory.Ord2.R2 Ω l) (A : ValuationSubring Ω) : (Ω ≃ₐ[ℚ] Ω) →* (Qbar l)ˣ :=
  Classical.epsilon fun ν : (Ω ≃ₐ[ℚ] Ω) →* (Qbar l)ˣ => ∀ s ∈ Dec (F := ℚ) A, (ν s : Qbar l) = GlobalTheory.Ord2.mat W s 1 1

end GlobalTheory.K4
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.ZetaSysUOfHalves
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.KZ

def ZetaSysUr : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
      ∃ (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl), Sys W c y S' ∧ NzAt W A y

theorem zetaUr_of_sys (h : ZetaSysUr) : ZetaUr := fun l _ Ω _ _ _ ι e S A W g hN hS => es_of_sys (h l Ω ι e S A W g hN hS)

def GlobU (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) → R2 Ω l → Coef l →
    (G ℚ Ω →* (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
      ∃ (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl) (ν : G ℚ Ω →* (Qbar l)ˣ)
        (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l),
        Sys W c y S' ∧ IwSys c A ν Z ∧ SpLink A e χ Z y ∧ Pin e A W c ν χ Z

def LocU (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) → R2 Ω l → Coef l →
    (G ℚ Ω →* (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
      ∀ (c : Coef l) (y : G ℚ Ω → Fin 2 → Qbar l) (S' : Finset Pl) (ν : G ℚ Ω →* (Qbar l)ˣ)
        (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l),
        Sys W c y S' → IwSys c A ν Z → SpLink A e χ Z y → Pin e A W c ν χ Z → NzAt W A y

theorem zetaSysU_of_halves (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) →
    R2 Ω l → Coef l → (G ℚ Ω →* (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop)
    (hG : GlobU Pin) (hL : LocU Pin) : ZetaSysUr := by
  intro l _ Ω _ _ _ ι e S A W g hN hS
  obtain ⟨c, y, S', ν, χ, Z, h1, h2, h3, h4⟩ := hG l Ω ι e S A W g hN hS
  exact ⟨c, y, S', h1, hL l Ω ι e S A W g hN hS c y S' ν χ Z h1 h2 h3 h4⟩

theorem zetaUr_of_halves (Pin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime], ℕ → (ValuationSubring Ω) →
    R2 Ω l → Coef l → (G ℚ Ω →* (Qbar l)ˣ) → (∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) → (∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) → Prop)
    (hG : GlobU Pin) (hL : LocU Pin) : ZetaUr :=
  zetaUr_of_sys (zetaSysU_of_halves Pin hG hL)

end GlobalTheory.KZ

end
end

