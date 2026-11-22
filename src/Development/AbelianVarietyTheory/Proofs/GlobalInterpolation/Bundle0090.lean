import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalBasisSnocOfLocalBasis
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.LocBasisSnoc

variable {E : Type} [Field E] {n : ℕ}

def blk (A : Matrix (Fin n) (Fin n) E) (c : E) : Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases c (fun _ => 0) j)
    (fun i' => Fin.lastCases 0 (fun j' => A i' j') j) i

theorem blk_mulVec_castSucc (A : Matrix (Fin n) (Fin n) E) (c : E) (x : Fin (n + 1) → E) (i : Fin n) :
    (blk A c *ᵥ x) i.castSucc = (A *ᵥ Fin.init x) i := by
  simp [blk, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.init]

theorem blk_mulVec_last (A : Matrix (Fin n) (Fin n) E) (c : E) (x : Fin (n + 1) → E) :
    (blk A c *ᵥ x) (Fin.last n) = c * x (Fin.last n) := by
  simp [blk, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

theorem blk_mulVec_ext {P Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E} (h : ∀ x, P *ᵥ x = Q *ᵥ x) : P = Q :=
  Matrix.ext_of_mulVec_single fun j => h _

theorem blk_mul (A A' : Matrix (Fin n) (Fin n) E) (c c' : E) :
    blk A c * blk A' c' = blk (A * A') (c * c') := by
  refine blk_mulVec_ext fun x => ?_
  rw [← Matrix.mulVec_mulVec]
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [blk_mulVec_last, blk_mulVec_last, blk_mulVec_last, mul_assoc]
  · rw [blk_mulVec_castSucc, blk_mulVec_castSucc, ← Matrix.mulVec_mulVec]
    congr 2
    funext k
    exact blk_mulVec_castSucc _ _ _ _

theorem blk_one : blk (1 : Matrix (Fin n) (Fin n) E) 1 = 1 := by
  refine blk_mulVec_ext fun x => ?_
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [blk_mulVec_last, one_mul, Matrix.one_mulVec]
  · rw [blk_mulVec_castSucc, Matrix.one_mulVec, Matrix.one_mulVec]
    rfl

end GlobalTheory.LocBasisSnoc

open GlobalTheory.LocBasisSnoc in

theorem GlobalTheory.isLocBasis_snoc : ∀ {E : Type} [Field E] [NumberField E] {N n : ℕ} (hN : N = n + 1) (t : E), t ≠ 0 → ∀ (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin n → E)), (∀ x, x ∈ L ↔ iniH hN x ∈ L' ∧ t * x (Br.iL hN) ∈ (1 : Submodule (𝓞 E) E)) → ∀ (p : ℕ) (B' : GL (Fin n) E), p.Prime → IsLocBasis p (L' : Set (Fin n → E)) B' → ∃ B : GL (Fin N) E, (∀ x, iniH hN ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) = (B' : Matrix (Fin n) (Fin n) E) *ᵥ iniH hN x) ∧ (∀ x, t * ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) (Br.iL hN) = x (Br.iL hN)) ∧ IsLocBasis p (L : Set (Fin N → E)) B := by
  intro E _ _ N n hN t ht L L' hL p B' hp hB'
  subst hN
  let B : GL (Fin (n + 1)) E :=
    ⟨blk (B' : Matrix (Fin n) (Fin n) E) t⁻¹, blk ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) t,
      by rw [blk_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, inv_mul_cancel₀ ht, blk_one],
      by rw [blk_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_inv_cancel₀ ht, blk_one]⟩
  have hini : ∀ y : Fin (n + 1) → E, iniH rfl y = Fin.init y := fun y => rfl
  have hlast : (Br.iL (rfl : n + 1 = n + 1)) = Fin.last n := rfl
  refine ⟨B, fun x => ?_, fun x => ?_, ?_⟩
  · rw [hini, hini]
    funext i
    exact blk_mulVec_castSucc _ _ _ _
  · rw [hlast]
    show t * (blk _ t⁻¹ *ᵥ x) (Fin.last n) = _
    rw [blk_mulVec_last, ← mul_assoc, mul_inv_cancel₀ ht, one_mul]
  · intro x
    have hinv : ((B⁻¹ : GL (Fin (n + 1)) E) : Matrix _ _ E) = blk ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) t := rfl
    rw [hinv]
    set R := (algebraMap (𝓞 E) E).range
    have hR : ∀ (s : ℕ) {y : E}, y ∈ R → (s : E) * y ∈ R := fun s y hy => R.mul_mem (natCast_mem R s) hy
    have key : ∀ s : ℕ, (∀ a, (s : E) * (blk ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) t *ᵥ x) a ∈ R) ↔
        (∀ a, (s : E) * (((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ Fin.init x) a ∈ R) ∧
          (s : E) * (t * x (Fin.last n)) ∈ R := by
      intro s
      constructor
      · intro h
        refine ⟨fun a => ?_, ?_⟩
        · have := h a.castSucc
          rwa [blk_mulVec_castSucc] at this
        · have := h (Fin.last n)
          rwa [blk_mulVec_last] at this
      · rintro ⟨h1, h2⟩ a
        refine Fin.lastCases ?_ (fun i => ?_) a
        · rw [blk_mulVec_last]; exact h2
        · rw [blk_mulVec_castSucc]; exact h1 i
    have memL : ∀ s : ℕ, (s : E) • x ∈ L ↔ (s : E) • Fin.init x ∈ L' ∧ (s : E) * (t * x (Fin.last n)) ∈ R := by
      intro s
      rw [hL, hini, hlast, Submodule.mem_one]
      have e : t * ((s : E) • x) (Fin.last n) = (s : E) * (t * x (Fin.last n)) := by
        rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]
      rw [e]
      rfl
    have hnd : ∀ a b : ℕ, ¬ p ∣ a → ¬ p ∣ b → ¬ p ∣ a * b := fun a b ha hb h =>
      (hp.dvd_mul.mp h).elim ha hb
    have hB := hB' (Fin.init x)
    constructor
    · rintro ⟨s, hs, hx⟩
      obtain ⟨h1, h2⟩ := (memL s).mp hx
      obtain ⟨s', hs', h3⟩ := hB.mp ⟨s, hs, h1⟩
      refine ⟨s * s', hnd _ _ hs hs', (key _).mpr ⟨fun a => ?_, ?_⟩⟩
      · rw [Nat.cast_mul, mul_assoc]; exact hR s (h3 a)
      · rw [Nat.cast_mul, mul_comm (s : E), mul_assoc]; exact hR s' h2
    · rintro ⟨s, hs, h⟩
      obtain ⟨h1, h2⟩ := (key s).mp h
      obtain ⟨s', hs', h3⟩ := hB.mpr ⟨s, hs, h1⟩
      refine ⟨s * s', hnd _ _ hs hs', (memL _).mpr ⟨?_, ?_⟩⟩
      · rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul]
        exact nsmul_mem h3 s
      · rw [Nat.cast_mul, mul_comm (s : E), mul_assoc]; exact hR s' h2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowLocKMulInf
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

noncomputable section

namespace GlobalTheory.TamePow

open Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

theorem locK_eq_one_of_tame (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt v) (y : Lˣ)
    (h2 : v.valuation L (y : L) = 1) (h1 : v.valuation L ((y : L) - 1) ≤ WithZero.exp (-1 : ℤ)) :
    χ.locK v y = 1 := by
  have hval : ∀ k : L, Valued.v (algebraMap L (v.adicCompletion L) k) = v.valuation L k := fun k =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
  refine h (atFin v y) ((hval _).trans h2) ?_
  have : ((atFin v y : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1 =
      algebraMap L (v.adicCompletion L) ((y : L) - 1) := by
    rw [map_sub, map_one]; rfl
  rw [this, hval]
  simpa using h1

theorem exists_pow_sub_one_mem (v : HeightOneSpectrum (𝓞 L)) :
    ∃ m : ℕ, 0 < m ∧ ∀ r : 𝓞 L, r ∉ v.asIdeal → r ^ m - 1 ∈ v.asIdeal := by
  have hfin : Finite (𝓞 L ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have hmax := v.isMaximal
  refine ⟨Nat.card (𝓞 L ⧸ v.asIdeal)ˣ, Nat.card_pos, fun r hr => ?_⟩
  let _ := Ideal.Quotient.field v.asIdeal
  have h0 : Ideal.Quotient.mk v.asIdeal r ≠ 0 := fun h => hr (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have h1 := congrArg Units.val (pow_card_eq_one' (x := Units.mk0 _ h0))
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]
  rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h1

theorem exists_pow_locK (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt v) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : Lˣ, v.valuation L (u : L) = 1 → χ.locK v u ^ m = 1 := by
  obtain ⟨m, hm, H⟩ := exists_pow_sub_one_mem v
  refine ⟨m, hm, fun u hu => ?_⟩
  obtain ⟨r, s, hs, hrs⟩ := (intAt_iff (P := v) (u : L)).2 hu.le
  have hs1 : v.valuation L (algebraMap (𝓞 L) L s) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hs
  have hr1 : v.valuation L (algebraMap (𝓞 L) L r) = 1 := by
    rw [← hrs, map_mul, hs1, hu, one_mul]
  have hr : r ∉ v.asIdeal := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).1 hr1
  have hmem : r ^ m - s ^ m ∈ v.asIdeal := by
    have := v.asIdeal.sub_mem (H r hr) (H s hs)
    rwa [sub_sub_sub_cancel_right] at this
  have hle : v.valuation L (algebraMap (𝓞 L) L (r ^ m - s ^ m)) ≤ WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    simpa using (v.intValuation_le_pow_iff_mem (r ^ m - s ^ m) 1).2 (by simpa using hmem)
  rw [← map_pow]
  refine locK_eq_one_of_tame χ h _ (by simp [hu]) ?_
  have e : algebraMap (𝓞 L) L (r ^ m - s ^ m) = (algebraMap (𝓞 L) L s) ^ m * (((u ^ m : Lˣ) : L) - 1) := by
    rw [map_sub, map_pow, map_pow, ← hrs, Units.val_pow_eq_pow_val]; ring
  rwa [e, map_mul, map_pow, hs1, one_pow, one_mul] at hle

theorem exists_gen (P : HeightOneSpectrum (𝓞 L)) : ∃ (h : ℕ) (a : Lˣ), 0 < h ∧
    P.valuation L (a : L) = WithZero.exp (-(h : ℤ)) ∧
    ∀ Q : HeightOneSpectrum (𝓞 L), Q ≠ P → Q.valuation L (a : L) = 1 := by
  have hP : P.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 L)) := mem_nonZeroDivisors_of_ne_zero P.ne_bot
  have h1 : ClassGroup.mk0 (⟨P.asIdeal, hP⟩ ^ Nat.card (ClassGroup (𝓞 L))) = 1 := by
    rw [map_pow, pow_card_eq_one']
  obtain ⟨a, ha⟩ := (ClassGroup.mk0_eq_one_iff (pow_mem hP _)).1 h1
  have ha' : P.asIdeal ^ Nat.card (ClassGroup (𝓞 L)) = Ideal.span {a} := ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact pow_ne_zero _ P.ne_bot (by simpa using ha')
  refine ⟨Nat.card (ClassGroup (𝓞 L)), Units.mk0 (algebraMap (𝓞 L) L a) (by simpa using ha0), Nat.card_pos, ?_, ?_⟩
  · rw [Units.val_mk0, HeightOneSpectrum.valuation_of_algebraMap, P.intValuation_if_neg ha0, ← ha',
      Associates.mk_pow, Associates.count_pow (by simpa using P.ne_bot) P.associates_irreducible,
      Associates.count_self P.associates_irreducible, mul_one]
  · intro Q hQ
    rw [Units.val_mk0, HeightOneSpectrum.valuation_eq_one_iff_notMem]
    intro hm
    have h2 : P.asIdeal ^ Nat.card (ClassGroup (𝓞 L)) ≤ Q.asIdeal := by
      rw [ha', Ideal.span_singleton_le_iff_mem]; exact hm
    have h3 := Q.isPrime.le_of_pow_le h2
    exact hQ (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h3).symm)

theorem exists_pow_locK_mul_inf : ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (S : Finset (HeightOneSpectrum (𝓞 E))), χ.ProductRule → (∀ v, v ∉ S → χ.UnrAt v) → (∀ v, χ.TameAt v) → ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ), ∃ (M : ℕ) (z : Eˣ), 0 < M ∧ P.valuation E (z : E) = P.valuation E (k : E) ^ M ∧ (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E (z : E) = 1) ∧ χ.locK P k ^ M * χ.inf z = 1 := by
  intro E _ _ χ S hpr hunr htame P k
  classical
  obtain ⟨h, a, hh, haP, haQ⟩ := exists_gen P
  choose m hm hmu using fun v => exists_pow_locK χ (htame v)
  set M' := ∏ v ∈ insert P S, m v with hM'
  have hkill : ∀ v ∈ insert P S, ∀ u : Eˣ, v.valuation E (u : E) = 1 → χ.locK v (u ^ M') = 1 := by
    intro v hv u hu
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m hv
    rw [map_pow, hM', hc, pow_mul, hmu v u hu, one_pow]
  have hk0 : P.valuation E (k : E) ≠ 0 := by simp
  set z0 : Eˣ := a ^ ordF P k with hz0
  have hz0P : P.valuation E (z0 : E) = P.valuation E (k : E) ^ h := by
    rw [hz0, Units.val_zpow_eq_zpow_val, map_zpow₀, haP, ← WithZero.exp_log hk0, ← WithZero.exp_zsmul,
      ← WithZero.exp_nsmul, ordF]
    congr 1
    simp only [smul_eq_mul, nsmul_eq_mul]
    ring
  have hz0Q : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E (z0 : E) = 1 := fun Q hQ => by
    rw [hz0, Units.val_zpow_eq_zpow_val, map_zpow₀, haQ Q hQ, one_zpow]
  have hzQ : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E ((z0 ^ M' : Eˣ) : E) = 1 := fun Q hQ => by
    rw [Units.val_pow_eq_pow_val, map_pow, hz0Q Q hQ, one_pow]
  refine ⟨h * M', z0 ^ M', Nat.mul_pos hh (Finset.prod_pos fun v _ => hm v), ?_, hzQ, ?_⟩
  · rw [Units.val_pow_eq_pow_val, map_pow, hz0P, pow_mul]
  · have H := hpr (insert P S) (fun v hv => hunr v fun h => hv (Finset.mem_insert_of_mem h)) (z0 ^ M')
    have e1 : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ insert P S), χ.val v ^ ordF v (z0 ^ M')) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun v => ?_
      by_cases hv : v ∈ insert P S
      · rw [finprod_eq_if, if_neg (not_not.2 hv)]
      rw [finprod_eq_if, if_pos hv]
      have : v ≠ P := fun h => hv (h ▸ Finset.mem_insert_self _ _)
      rw [ordF, hzQ v this, WithZero.log_one, neg_zero, zpow_zero]
    have e2 : ∏ v ∈ insert P S, χ.locK v (z0 ^ M') = χ.locK P (z0 ^ M') :=
      Finset.prod_eq_single P (fun v hv hne => hkill v hv z0 (hz0Q v hne))
        (fun h => absurd (Finset.mem_insert_self _ _) h)
    have e3 : χ.locK P (z0 ^ M') = χ.locK P k ^ (h * M') := by
      have := hkill P (Finset.mem_insert_self _ _) (z0 / k ^ h) (by
        rw [Units.val_div_eq_div_val, map_div₀, hz0P, Units.val_pow_eq_pow_val, map_pow, div_self (pow_ne_zero _ hk0)])
      rwa [div_pow, map_div, div_eq_one, ← pow_mul, map_pow (χ.locK P) k] at this
    rw [e1, e2, e3, mul_one, mul_comm] at H
    exact H

end GlobalTheory.TamePow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowPrincipal
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

namespace GlobalTheory.NormOneIdeal

theorem star_integer_smul {E : Type} [Field E] [NumberField E] [StarRing E] (a : 𝓞 E) :
    ∃ b : 𝓞 E, (b : E) = star (a : E) := by
  refine ⟨⟨star (a : E), ?_⟩, rfl⟩
  have h : IsIntegral ℤ (a : E) := a.isIntegral_coe
  exact h.map (starRingEnd E).toIntAlgHom

theorem star_mem_mul {E : Type} [Field E] [NumberField E] [StarRing E]
    {A B C D : Submodule (𝓞 E) E} (h1 : ∀ x ∈ A, star x ∈ C) (h2 : ∀ x ∈ B, star x ∈ D) :
    ∀ x ∈ A * B, star x ∈ C * D := by
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro m hm n hn
    rw [star_mul']
    exact Submodule.mul_mem_mul (h1 m hm) (h2 n hn)
  · intro a b ha hb
    rw [star_add]
    exact add_mem ha hb

theorem star_mem_span {E : Type} [Field E] [NumberField E] [StarRing E] (z x : E)
    (hx : x ∈ Submodule.span (𝓞 E) {z}) : star x ∈ Submodule.span (𝓞 E) {star z} := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨b, hb⟩ := star_integer_smul a
  refine Submodule.mem_span_singleton.2 ⟨b, ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def, star_mul']
  exact congrArg (· * star z) hb

theorem star_mem_pow {E : Type} [Field E] [NumberField E] [StarRing E]
    {A C : Submodule (𝓞 E) E} (h1 : ∀ x ∈ A, star x ∈ C) (n : ℕ) :
    ∀ x ∈ A ^ n, star x ∈ C ^ n := by
  induction n with
  | zero =>
    intro x hx
    rw [pow_zero, Submodule.one_eq_span] at hx ⊢
    simpa using star_mem_span 1 x hx
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact star_mem_mul ih h1

theorem exists_pow_principal {E : Type} [Field E] [NumberField E]
    (I : (Submodule (𝓞 E) E)ˣ) :
    ∃ (h : ℕ) (z : E), 0 < h ∧ (I : Submodule (𝓞 E) E) ^ h = Submodule.span (𝓞 E) {z} := by
  let e := FractionalIdeal.unitsMulEquivSubmodule (S := nonZeroDivisors (𝓞 E)) (P := E)
  let F := e.symm I
  have hF : ClassGroup.mk E (F ^ Fintype.card (ClassGroup (𝓞 E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  obtain ⟨z, hz⟩ := ClassGroup.mk_eq_one_iff.1 hF
  refine ⟨Fintype.card (ClassGroup (𝓞 E)), z, Fintype.card_pos, ?_⟩
  rw [← hz]
  have : e (F ^ Fintype.card (ClassGroup (𝓞 E))) = I ^ Fintype.card (ClassGroup (𝓞 E)) := by
    rw [map_pow, MulEquiv.apply_symm_apply]
  rw [← Units.val_pow_eq_pow_val, ← this]
  rfl

theorem pow_eq_span_norm_one : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (I J : Submodule (𝓞 E) E), (∀ x, x ∈ J ↔ star x ∈ I) → I * J = 1 → (∀ (n : ℕ) (x : E), x ∈ J ^ n ↔ star x ∈ I ^ n) ∧ ∃ (h : ℕ) (y : E), 0 < h ∧ star y * y = 1 ∧ Submodule.span (𝓞 E) {y} = I ^ h := by
  intro E _ _ _ I J hJ hIJ
  have h1 : ∀ (n : ℕ) (x : E), x ∈ J ^ n ↔ star x ∈ I ^ n := by
    intro n x
    refine ⟨star_mem_pow (fun x hx => (hJ x).1 hx) n x, fun hx => ?_⟩
    have := star_mem_pow (A := I) (C := J) (fun x hx => (hJ _).2 (by rwa [star_star])) n _ hx
    rwa [star_star] at this
  refine ⟨h1, ?_⟩
  obtain ⟨h, z, hh, hz⟩ := exists_pow_principal (E := E) ⟨I, J, hIJ, by rw [mul_comm, hIJ]⟩
  change I ^ h = _ at hz
  have hJh : J ^ h = Submodule.span (𝓞 E) {star z} := by
    ext x
    rw [h1, hz]
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · simpa using star_mem_span _ _ hx
    · simpa using star_mem_span _ _ hx
  have hm : I ^ h * J ^ h = 1 := by rw [← mul_pow, hIJ, one_pow]
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [hz] at hm
    simp only [Submodule.span_zero_singleton, Submodule.bot_mul] at hm
    have : (1 : E) ∈ (⊥ : Submodule (𝓞 E) E) := by
      rw [hm, Submodule.one_eq_span]
      exact Submodule.mem_span_singleton_self _
    simp at this
  have hs0 : star z ≠ 0 := star_ne_zero.2 hz0
  have hinv : Submodule.span (𝓞 E) {(star z)⁻¹} = I ^ h := by
    calc Submodule.span (𝓞 E) {(star z)⁻¹}
        = I ^ h * J ^ h * Submodule.span (𝓞 E) {(star z)⁻¹} := by rw [hm, one_mul]
      _ = I ^ h := by
        rw [mul_assoc, hJh, Submodule.span_mul_span, Set.singleton_mul_singleton,
          mul_inv_cancel₀ hs0, ← Submodule.one_eq_span, mul_one]
  refine ⟨h + h, z * (star z)⁻¹, by omega, ?_, ?_⟩
  · rw [star_mul', star_inv₀, star_star]
    field_simp
  · rw [pow_add]
    nth_rewrite 1 [hz]
    rw [← hinv, Submodule.span_mul_span, Set.singleton_mul_singleton]

end GlobalTheory.NormOneIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRepsSupOfFiniteQuot
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory

theorem exists_reps_sup_of_finite_quot (E : Type) [Field E] (H : Type) [AddCommGroup H]
    [Module (𝓞 E) H] (Z₁ Z₀ : Submodule (𝓞 E) H) (C : AddSubgroup H)
    (hfin : Finite (↥Z₁ ⧸ Z₀.comap Z₁.subtype)) :
    ∃ R : Finset H, (∀ x ∈ R, x ∈ Z₁) ∧
      (∀ x ∈ R, ∀ y ∈ R, x - y ∈ Z₀.toAddSubgroup ⊔ C → x = y) ∧
      ∀ y ∈ Z₁, ∃ x ∈ R, y - x ∈ Z₀.toAddSubgroup ⊔ C := by
  classical
  letI := Fintype.ofFinite (↥Z₁ ⧸ Z₀.comap Z₁.subtype)
  set Z : AddSubgroup H := Z₀.toAddSubgroup ⊔ C with hZ
  let s : (↥Z₁ ⧸ Z₀.comap Z₁.subtype) → ↥Z₁ :=
    Function.surjInv (Submodule.Quotient.mk_surjective (Z₀.comap Z₁.subtype))
  have hs : ∀ z, Submodule.Quotient.mk (s z) = z := fun z =>
    Function.surjInv_eq (Submodule.Quotient.mk_surjective (Z₀.comap Z₁.subtype)) z
  let T : Finset (H ⧸ Z) := Finset.univ.image fun z => QuotientAddGroup.mk (s z : H)
  have hsurj : (Z₁ : Set H).SurjOn (QuotientAddGroup.mk : H → H ⧸ Z) T := by
    intro t ht
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
    exact ⟨s z, (s z).2, rfl⟩
  obtain ⟨R, hR, hinj, him⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn _ _ hsurj
  refine ⟨R, fun x hx => hR hx, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hinj hx hy (QuotientAddGroup.eq_iff_sub_mem.2 hxy)
  · intro y hy
    have h1 : (⟨y, hy⟩ : ↥Z₁) - s (Submodule.Quotient.mk ⟨y, hy⟩) ∈ Z₀.comap Z₁.subtype :=
      (Submodule.Quotient.eq _).1 (hs _).symm
    have h2 : y - (s (Submodule.Quotient.mk ⟨y, hy⟩) : H) ∈ Z :=
      AddSubgroup.mem_sup_left (by simpa using h1)
    have h3 : (QuotientAddGroup.mk y : H ⧸ Z) ∈ T :=
      Finset.mem_image.2 ⟨_, Finset.mem_univ _, (QuotientAddGroup.eq_iff_sub_mem.2 h2).symm⟩
    rw [← him] at h3
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.1 h3
    exact ⟨x, hx, QuotientAddGroup.eq_iff_sub_mem.1 hxy.symm⟩

theorem latSum_eq_sum_sum_reps : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (H : Type) [AddCommGroup H] [Module (𝓞 E) H] (Z₁ Z₀ : Submodule (𝓞 E) H) (C : AddSubgroup H) (J : Finset H), Z₀ ≤ Z₁ → C ≤ Z₁.toAddSubgroup → Finite (↥Z₁ ⧸ Z₀.comap Z₁.subtype) → IsReps Z₀.toAddSubgroup C J → ∃ R : Finset H, (∀ x ∈ R, x ∈ Z₁) ∧ ∀ (M : Type) [AddCommMonoid M] (f : H → M), (∀ x ∈ Z₁, ∀ y ∈ Z₀, f (x + y) = f x) → latSum Z₁ Z₀ f = ∑ x ∈ R, ∑ j ∈ J, f (x + j) := by
  intro E _ _ _ H _ _ Z₁ Z₀ C J h01 hC hfin hJ
  classical
  obtain ⟨R, hR, hRinj, hRsurj⟩ := exists_reps_sup_of_finite_quot E H Z₁ Z₀ C hfin
  obtain ⟨hJC, hJinj, hJsurj⟩ := hJ
  refine ⟨R, hR, ?_⟩
  intro M _ f hf
  letI := Fintype.ofFinite (↥Z₁ ⧸ Z₀.comap Z₁.subtype)
  have hmem : ∀ p ∈ R ×ˢ J, p.1 + p.2 ∈ Z₁ := fun p hp =>
    Z₁.add_mem (hR _ (Finset.mem_product.1 hp).1) (hC (hJC _ (Finset.mem_product.1 hp).2))
  unfold latSum
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_product']
  symm
  refine Finset.sum_bij
    (fun p hp => (Submodule.Quotient.mk ⟨p.1 + p.2, hmem p hp⟩ : ↥Z₁ ⧸ Z₀.comap Z₁.subtype))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · rintro ⟨x, j⟩ hp ⟨x', j'⟩ hp' h
    obtain ⟨hx, hj⟩ := Finset.mem_product.1 hp
    obtain ⟨hx', hj'⟩ := Finset.mem_product.1 hp'
    have h1 : x + j - (x' + j') ∈ Z₀ := by
      simpa using (Submodule.Quotient.eq _).1 h
    have h2 : x = x' := by
      refine hRinj x hx x' hx' ?_
      have : x - x' = (x + j - (x' + j')) + (j' - j) := by abel
      rw [this]
      exact AddSubgroup.add_mem_sup h1 (C.sub_mem (hJC _ hj') (hJC _ hj))
    subst h2
    have h3 : j = j' := by
      refine hJinj j hj j' hj' ?_
      have : j - j' = x + j - (x + j') := by abel
      rw [this]
      exact h1
    rw [h3]
  · intro z _
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨x, hx, hyx⟩ := hRsurj y hy
    obtain ⟨a, ha, c, hc, hac⟩ := AddSubgroup.mem_sup.1 hyx
    obtain ⟨j, hj, hcj⟩ := hJsurj c hc
    refine ⟨(x, j), Finset.mem_product.2 ⟨hx, hj⟩, (Submodule.Quotient.eq _).2 ?_⟩
    have h1 : x + j - y = -(a + (c - j)) := by
      have : y = x + (a + c) := by rw [hac]; abel
      rw [this]; abel
    have h2 : x + j - y ∈ Z₀ := by
      rw [h1]
      exact Z₀.neg_mem (Z₀.add_mem ha hcj)
    simpa using h2
  · intro p hp
    set w := Function.surjInv (Submodule.Quotient.mk_surjective (Z₀.comap Z₁.subtype))
      (Submodule.Quotient.mk ⟨p.1 + p.2, hmem p hp⟩) with hw
    have h0 : Submodule.Quotient.mk w =
        (Submodule.Quotient.mk ⟨p.1 + p.2, hmem p hp⟩ : ↥Z₁ ⧸ Z₀.comap Z₁.subtype) :=
      Function.surjInv_eq _ _
    have h1 : (w : H) - (p.1 + p.2) ∈ Z₀ := by
      simpa using (Submodule.Quotient.eq _).1 h0
    have h2 := hf _ (hmem p hp) _ h1
    rw [← h2]
    congr 1
    abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentCompanion
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.MomentCompanion

theorem companion_gen {E : Type} [Field E] [NumberField E] [StarRing E] {b : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (ϖ : 𝓞 E) (d : DecoSet E b ST SG)
    (hST : ∀ P : ST, ϖ ∈ P.1.asIdeal) (hcop : IsCoprime ϖ (cO E ϖ)) :
    ∃ N'' : Submodule (𝓞 E) (Sp E b), IsSdLat N'' ∧ (∀ y ∈ d.1.N, (ϖ : E) • y ∈ N'') ∧
      (∀ y ∈ N'', star (ϖ : E) • y ∈ d.1.N) ∧
      ∀ (P : ST) (y : Sp E b), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d.1.at P.1 ∧ d.1.f P y = 0 := by
  have hd := d.2
  have hIN : Ideal.span {ϖ} • d.1.N ≤ d.1.L := by
    rw [Submodule.smul_le]
    intro r hr y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    exact hd.smul_N_mem_L (fun P => Ideal.mul_mem_left _ _ (hST P)) hy
  obtain ⟨h1, h2⟩ := glue_unimodular (I := Ideal.span {ϖ}) (J := Ideal.span {cO E ϖ})
    (fun p hp => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hp
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    (fun p hp => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hp
      rw [map_mul, cO_cO]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    (by
      obtain ⟨u, v, huv⟩ := hcop
      exact ⟨u * ϖ, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), v * cO E ϖ,
        Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), huv⟩)
    hd.uni hd.L_lattice hd.L_le_N hIN
  have hbar : ∀ x ∈ d.1.L ⊔ Ideal.span {ϖ} • dual (hStd E b) d.1.L, cO E ϖ • x ∈ d.1.L := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ hy) ?_
    refine Submodule.smul_induction_on hz (fun r hr u hu => ?_) (fun u v hu hv => ?_)
    · rw [smul_comm]
      exact hIN (Submodule.smul_mem_smul hr (conj_smul_dual_mem hd.uni hIN
        (by rw [cO_cO]; exact Ideal.mem_span_singleton_self _) hu))
    · rw [smul_add]
      exact Submodule.add_mem _ hu hv
  refine ⟨_, ⟨h1, h2⟩, fun y hy => ?_, fun y hy => ?_, fun P y => ?_⟩
  · have : ϖ • y ∈ d.1.L := hd.smul_N_mem_L hST hy
    rw [← algebraMap_smul E ϖ y] at this
    exact Submodule.mem_sup_left this
  · have := hd.L_le_N (hbar y hy)
    rw [← algebraMap_smul E (cO E ϖ) y, algebraMap_cO] at this
    exact this
  · have hn : cO E ϖ ∉ P.1.asIdeal := by
      intro h
      obtain ⟨u, v, huv⟩ := hcop
      exact one_notMem P.1 (huv ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hST P)) (Ideal.mul_mem_left _ _ h))
    rw [← hd.mem_locP_L P y]
    exact ⟨fun h => localization_le_of_smul_mem hn hbar h, fun h => localization_le_of_smul_mem (one_notMem P.1) (fun x hx => by
      rw [one_smul]; exact Submodule.mem_sup_left hx) h⟩

theorem companion : ∀ (X : Fields) (b : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (d : DecoSet X.E b (divs ϖ) SG), X.Ok → ϖ ≠ 0 → IsCoprime ϖ (X.conjO ϖ) → (∀ P ∈ divs ϖ, ϖ ∉ P.asIdeal ^ 2) → ∃ N'' : Submodule (𝓞 X.E) (Sp X.E b), IsSdLat N'' ∧ (∀ y ∈ d.1.N, (ϖ : X.E) • y ∈ N'') ∧ (∀ y ∈ N'', star (ϖ : X.E) • y ∈ d.1.N) ∧ ∀ (P : ↥(divs ϖ)) (y : Sp X.E b), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d.1.at P.1 ∧ d.1.f P y = 0 :=
  fun _ _ _ ϖ d _ h0 hcop _ => companion_gen ϖ d (fun P => (mem_divs h0 P.1).1 P.2) hcop

end GlobalTheory.MomT.MomentCompanion
end

