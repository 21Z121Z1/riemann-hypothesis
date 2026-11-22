import Formalism.FormalGroupWitt.Statement

-- bundled from Formalism.FormalGroupWitt.FormalGroupWittProofs.AdditiveLawExample
section
noncomputable section

namespace Formalism.FG.FormalGroupSubstitution

open MvPowerSeries

theorem subst_X_add_X {σ τ : Type*} [Finite σ] {R : Type*} [CommRing R]
    (a : σ → MvPowerSeries τ R) (h : ∀ s, constantCoeff (a s) = 0) (p q : σ) :
    subst a (X p + X q : MvPowerSeries σ R) = a p + a q := by
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero h
  rw [subst_add ha, subst_X ha, subst_X ha]

theorem subst_X' {σ τ : Type*} [Finite σ] {R : Type*} [CommRing R]
    (a : σ → MvPowerSeries τ R) (h : ∀ s, constantCoeff (a s) = 0) (p : σ) :
    subst a (X p : MvPowerSeries σ R) = a p :=
  subst_X (hasSubst_of_constantCoeff_zero h) p

theorem atXv_X (j : Fin 2) :
    Formalism.FG.atXv (MvPowerSeries.X j : MvPowerSeries (Fin 2) ℤ) = Formalism.FG.vX j := by
  unfold Formalism.FG.atXv
  exact subst_X' _ (fun s => by simp) j

theorem atYv_X (j : Fin 2) :
    Formalism.FG.atYv (MvPowerSeries.X j : MvPowerSeries (Fin 2) ℤ) = Formalism.FG.vY j := by
  unfold Formalism.FG.atYv
  exact subst_X' _ (fun s => by simp) j

end Formalism.FG.FormalGroupSubstitution

namespace Formalism.FG

open MvPowerSeries Formalism.FG.FormalGroupSubstitution

theorem additive_law_example : Formalism.FG.AddLawExample := by
  unfold AddLawExample
  have hF : ∀ i : Fin 2, constantCoeff
      (vX i + vY i : MvPowerSeries (Fin 2 × Fin 2) ℤ) = 0 := fun i => by simp
  refine ⟨⟨hF, ?_, ?_, ?_, ?_⟩, ?_, ⟨fun i => by simp, ?_⟩, ⟨hF, ⟨fun j => by simp, ?_⟩, ?_⟩⟩
  · intro i x
    obtain ⟨a, b⟩ := x
    fin_cases a <;> fin_cases b <;> fin_cases i <;> simp [coeff_X, Finsupp.single_eq_single_iff]
  · intro i
    rw [subst_X_add_X _ (fun s => by split_ifs <;> simp)]
    simp
  · intro i
    rw [subst_X_add_X _ (fun s => by split_ifs <;> simp)]
    simp
  · intro i
    have hin : ∀ j : Fin 2, subst (fun y : Fin 2 × Fin 2 => (v3 (Fin.castSucc y.1) y.2 :
        MvPowerSeries (Fin 3 × Fin 2) ℤ)) (vX j + vY j : MvPowerSeries (Fin 2 × Fin 2) ℤ) =
        v3 0 j + v3 1 j := fun j => by
      rw [subst_X_add_X _ (fun s => by simp)]
      rfl
    have hin' : ∀ j : Fin 2, subst (fun y : Fin 2 × Fin 2 => (v3 y.1.succ y.2 :
        MvPowerSeries (Fin 3 × Fin 2) ℤ)) (vX j + vY j : MvPowerSeries (Fin 2 × Fin 2) ℤ) =
        v3 1 j + v3 2 j := fun j => by
      rw [subst_X_add_X _ (fun s => by simp)]
      rfl
    simp only [hin, hin']
    rw [subst_X_add_X _ (fun s => by split_ifs <;> simp),
      subst_X_add_X _ (fun s => by split_ifs <;> simp)]
    simp only [show ((1 : Fin 2) = 0) = False from by decide,
      if_true, if_false]
    rw [add_assoc]
  · intro i
    rw [subst_X_add_X _ (fun s => by simp)]
    rw [show Fin.rev (0 : Fin 2) = 1 from rfl, show Fin.rev (1 : Fin 2) = 0 from rfl, add_comm]
  · intro i
    rw [subst_X' _ hF]
    rw [subst_X_add_X _ (fun s => by split_ifs <;> simp [atXv_X, atYv_X])]
    simp [atXv_X, atYv_X]
  · intro j i
    simp [coeff_X, Finsupp.single_eq_single_iff]
  · intro j
    rw [subst_X' _ hF, atXv_X, atYv_X]

theorem not_a_law_example : Formalism.FG.NotLawExample := by
  unfold NotLawExample
  intro h
  have h2 := h.2.1 0 ((1 : Fin 2), (0 : Fin 1))
  dsimp only at h2
  rw [two_mul] at h2
  simp [coeff_X, Finsupp.single_eq_single_iff] at h2

end Formalism.FG
end
end

-- bundled from Formalism.FormalGroupWitt.FormalGroupWittProofs.ShiftFE
section
noncomputable section

universe u

namespace Formalism.FG
namespace ShiftFEAux

open MvPowerSeries

variable {K : Type*} [Field K] {l m : ℕ}

lemma pow_inj (hl : 2 ≤ l) {a b : ℕ} (h : (l ^ 2) ^ a = (l ^ 2) ^ b) : a = b :=
  Nat.pow_right_injective (le_trans hl (Nat.le_self_pow two_ne_zero l)) h

lemma eq_zero_of_pow_eq_one (hl : 2 ≤ l) {a : ℕ} (h : (l ^ 2) ^ a = 1) : a = 0 :=
  pow_inj hl (h.trans (pow_zero _).symm)

lemma coeff_shiftLog (j : ZMod m) (n : ZMod m →₀ ℕ) :
    coeff n (shiftLog K l m j) = ∑ e ∈ Finset.range (n.degree + 1),
      if n = Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0 := by
  rw [coeff_apply]; rfl

lemma coeff_shiftLog_single (hl : 2 ≤ l) (j : ZMod m) (e : ℕ) :
    coeff (Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e)) (shiftLog K l m j) =
      ((l : K) ^ e)⁻¹ := by
  rw [coeff_shiftLog, Finsupp.degree_single]
  rw [Finset.sum_eq_single e]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    have := congrArg Finsupp.degree h
    simp only [Finsupp.degree_single] at this
    exact hb (pow_inj hl this).symm
  · intro he
    exfalso; apply he
    rw [Finset.mem_range]
    have : e < (l ^ 2) ^ e := Nat.lt_pow_self (by nlinarith)
    omega

lemma coeff_shiftLog_zero (j : ZMod m) (n : ZMod m →₀ ℕ)
    (h : ∀ e : ℕ, n ≠ Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e)) :
    coeff n (shiftLog K l m j) = 0 := by
  rw [coeff_shiftLog]
  exact Finset.sum_eq_zero fun e _ => if_neg (h e)

lemma map_shiftLog (σ : K →+* K) (k : ZMod m) :
    map σ (shiftLog K l m k) = shiftLog K l m k := by
  ext n
  rw [coeff_map, coeff_shiftLog, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp [map_inv₀]

lemma idMod2 (hl : 2 ≤ l) : IsIdMod2 (shiftLog K l m) := by
  refine ⟨fun j => ?_, fun j i => ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply]
    apply coeff_shiftLog_zero
    intro e h
    have := congrArg Finsupp.degree h
    simp only [Finsupp.degree_single] at this
    have hpos : 0 < (l ^ 2) ^ e := by positivity
    have h0 : (0 : ZMod m →₀ ℕ).degree = 0 := by simp [Finsupp.degree]
    omega
  · by_cases hij : i = j
    · subst hij
      have := coeff_shiftLog_single (K := K) hl i 0
      simpa using this
    · rw [if_neg hij]
      apply coeff_shiftLog_zero
      intro e h
      have hd := congrArg Finsupp.degree h
      simp only [Finsupp.degree_single] at hd
      have he := eq_zero_of_pow_eq_one hl hd.symm
      subst he
      apply hij
      simpa using (Finsupp.single_left_inj one_ne_zero).mp h

lemma main [CharZero K] (hl : l.Prime) [NeZero m] (σ : K →+* K) (j : ZMod m) :
    shiftLog K l m j - (l : K)⁻¹ • ∑ k, shiftMat K m j k •
        MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero)
          (MvPowerSeries.map σ (shiftLog K l m k)) = MvPowerSeries.X j := by
  have hl2 : 2 ≤ l := hl.two_le
  have hsum : ∑ k, shiftMat K m j k •
        MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero)
          (MvPowerSeries.map σ (shiftLog K l m k)) =
      MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero) (shiftLog K l m (j - 1)) := by
    simp [shiftMat, map_shiftLog]
  rw [hsum]
  ext n
  simp only [map_sub, map_smul, smul_eq_mul, coeff_X]
  by_cases hA : ∃ e : ℕ, n = Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e)
  · obtain ⟨e, rfl⟩ := hA
    rw [coeff_shiftLog_single hl2]
    obtain _ | e := e
    · simp only [Nat.cast_zero, sub_zero, pow_zero, inv_one, if_true]
      rw [coeff_expand_of_not_dvd (i := j)]
      · ring
      · rw [Finsupp.single_eq_same, Nat.dvd_one]
        intro h
        nlinarith
    · have hne : Finsupp.single (j - ((e + 1 : ℕ) : ZMod m)) ((l ^ 2) ^ (e + 1)) ≠
          Finsupp.single j 1 := by
        intro h
        have hd := congrArg Finsupp.degree h
        simp only [Finsupp.degree_single] at hd
        exact absurd (eq_zero_of_pow_eq_one hl2 hd) (Nat.succ_ne_zero e)
      rw [if_neg hne]
      have hn : Finsupp.single (j - ((e + 1 : ℕ) : ZMod m)) ((l ^ 2) ^ (e + 1)) =
          (l ^ 2) • Finsupp.single ((j - 1) - (e : ZMod m)) ((l ^ 2) ^ e) := by
        rw [Finsupp.smul_single, smul_eq_mul, ← pow_succ']
        congr 1
        push_cast
        ring
      rw [hn, coeff_expand_smul, coeff_shiftLog_single hl2]
      ring
  · push Not at hA
    rw [coeff_shiftLog_zero j n hA, if_neg (by simpa using hA 0)]
    suffices h : coeff n (MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero)
        (shiftLog K l m (j - 1))) = 0 by rw [h]; ring
    by_cases hd : ∀ i, l ^ 2 ∣ n i
    · have hn : n = (l ^ 2) • Finsupp.mapRange (fun x => x / l ^ 2) (Nat.zero_div _) n := by
        ext i
        simp [Nat.mul_div_cancel' (hd i)]
      rw [hn, coeff_expand_smul]
      apply coeff_shiftLog_zero
      intro e he
      apply hA (e + 1)
      rw [hn, he, Finsupp.smul_single, smul_eq_mul, ← pow_succ']
      congr 1
      push_cast
      ring
    · push Not at hd
      obtain ⟨i, hi⟩ := hd
      exact coeff_expand_of_not_dvd _ _ _ hi

end ShiftFEAux

open ShiftFEAux in
theorem shift_functional_equation : Formalism.FG.ShiftFunEq.{u} := by
  intro K _ _ l hl m _ σ
  exact ⟨idMod2 hl.two_le, fun j => main hl σ j⟩

end Formalism.FG
end
end

-- bundled from Formalism.FormalGroupWitt.FormalGroupWittProofs.WittTeichmullerRoot
section
noncomputable section

namespace Formalism.FG.WittVectorsCharZero

theorem zlToW_injective (l : ℕ) [Fact l.Prime] : Function.Injective (zlToW l) := by
  intro a b h
  have h1 := WittVector.map_injective _ (algebraMap (ZMod l) (AlgebraicClosure (ZMod l))).injective h
  exact (WittVector.equiv l).symm.injective h1

theorem neZero_cast (l : ℕ) [Fact l.Prime] (d : ℕ) (hd : 1 ≤ d) :
    NeZero (((l ^ d - 1 : ℕ) : ZMod l)) := by
  constructor
  have hl : 1 ≤ l ^ d := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
  rw [Nat.cast_sub hl, Nat.cast_pow, ZMod.natCast_self, zero_pow (by omega), Nat.cast_one, zero_sub]
  exact neg_ne_zero.mpr one_ne_zero

end Formalism.FG.WittVectorsCharZero

namespace Formalism.FG

open Formalism.FG.WittVectorsCharZero

theorem witt_char_zero : Formalism.FG.WittCharZero := by
  intro l _
  refine ⟨fun m n h => ?_⟩
  have h1 : ((m : ℤ_[l])) = (n : ℤ_[l]) :=
    zlToW_injective l (by rw [map_natCast, map_natCast]; exact h)
  exact_mod_cast h1

theorem witt_teichmuller_root : Formalism.FG.WittTeichRoot := by
  intro l _ d hd
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hNpos : 0 < l ^ d - 1 := by
    have : l ≤ l ^ d := Nat.le_self_pow (by omega) l
    omega
  haveI : NeZero (((l ^ d - 1 : ℕ) : ZMod l)) := neZero_cast l d hd
  haveI : NeZero (((l ^ d - 1 : ℕ) : AlgebraicClosure (ZMod l))) := by
    have h := NeZero.of_injective (f := algebraMap (ZMod l) (AlgebraicClosure (ZMod l)))
      (a := (((l ^ d - 1 : ℕ) : ZMod l))) (algebraMap (ZMod l) (AlgebraicClosure (ZMod l))).injective
    rw [map_natCast] at h
    exact h
  have hdeg : (Polynomial.cyclotomic (l ^ d - 1) (AlgebraicClosure (ZMod l))).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr hNpos).ne'
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root _ hdeg
  have hprim : IsPrimitiveRoot μ (l ^ d - 1) := Polynomial.isRoot_cyclotomic_iff.mp hμ
  refine ⟨WittVector.teichmuller l μ, hprim.map_of_injective ?_⟩
  intro a b h
  have h2 := congrArg (fun w => WittVector.coeff w 0) h
  simpa [WittVector.teichmuller_coeff_zero] using h2

end Formalism.FG
end
end

