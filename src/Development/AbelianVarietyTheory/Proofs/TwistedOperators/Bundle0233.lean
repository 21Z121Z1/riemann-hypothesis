import Mathlib
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0081
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HyperbolicPairChangeOfBasis
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

namespace GlobalTheory.IsotropicPartner

open scoped ComplexOrder

def hf {n : ℕ} (d : Fin n → ℂ) (x y : Fin n → ℂ) : ℂ := ∑ i, star (x i) * d i * y i

lemma hf_symm {n : ℕ} (d : Fin n → ℂ) (hd : ∀ i, star (d i) = d i) (x y : Fin n → ℂ) :
    hf d y x = star (hf d x y) := by
  simp only [hf, star_sum, star_mul', star_star, hd]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma hf_sub {n : ℕ} (d : Fin n → ℂ) (x y u w : Fin n → ℂ) (a b : ℂ) :
    hf d x (fun i => y i - a * u i - b * w i) = hf d x y - a * hf d x u - b * hf d x w := by
  simp only [hf, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem exists_adapted_basis (n : ℕ) (ε : Fin n → Bool) (e : Fin n → ℂ) (he : e ≠ 0)
    (hiso : star e ⬝ᵥ (Jm ε *ᵥ e) = 0) :
    ∃ (P : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (c : ℂ), IsUnit P ∧ p ≠ q ∧
      P *ᵥ Pi.single p 1 = e ∧ P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ e) ∧
      ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
        (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0 := by
  set d : Fin n → ℂ := fun a => if ε a then 1 else -1 with hd_def
  have hJ : Jm ε = diagonal d := rfl
  have hd : ∀ i, star (d i) = d i := by intro i; simp only [d]; split_ifs <;> simp
  have hd2 : ∀ i, d i * d i = 1 := by intro i; simp only [d]; split_ifs <;> norm_num
  set s : ℂ := ∑ i, star (e i) * e i with hs_def
  have hs : s ≠ 0 := by
    have := (dotProduct_star_self_eq_zero (v := e)).not.mpr he
    exact fun h0 => this h0
  set c : ℂ := s⁻¹ with hc_def
  set e' : Fin n → ℂ := fun i => c * (d i * e i) with he'_def
  have hee : hf d e e = 0 := by
    simpa [hJ, hf, dotProduct, mulVec_diagonal, mul_assoc] using hiso
  have hee' : hf d e e' = 1 := by
    have : hf d e e' = c * s := by
      simp only [hf, e', s, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by linear_combination (c * star (e i) * e i) * hd2 i
    rw [this, hc_def, inv_mul_cancel₀ hs]
  have he'e' : hf d e' e' = 0 := by
    have : hf d e' e' = star c * c * hf d e e := by
      simp only [hf, e', Finset.mul_sum, star_mul', hd]
      exact Finset.sum_congr rfl fun i _ => by
        linear_combination (star c * c * star (e i) * d i * e i) * hd2 i
    rw [this, hee, mul_zero]
  have he'e : hf d e' e = 1 := by rw [hf_symm d hd, hee', star_one]
  obtain ⟨p, hp⟩ : ∃ p, e p ≠ 0 := by
    by_contra h; push_neg at h; exact he (funext h)
  set f : Fin n → ℂ := fun i => e' i - (e' p / e p) * e i with hf_def
  obtain ⟨q, hq⟩ : ∃ q, f q ≠ 0 := by
    by_contra h; push_neg at h
    have : hf d e e' = (e' p / e p) * hf d e e := by
      simp only [hf, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := h i; simp only [f] at this
      linear_combination (star (e i) * d i) * this
    rw [hee', hee, mul_zero] at this; exact one_ne_zero this
  have hpq : p ≠ q := by
    rintro rfl; apply hq; simp only [f]; field_simp; ring
  let pr : (Fin n → ℂ) → (Fin n → ℂ) := fun y i => y i - hf d e' y * e i - hf d e y * e' i
  have hpre : ∀ y, hf d e (pr y) = 0 := by
    intro y; simp only [pr]; rw [hf_sub, hee, hee']; ring
  have hpre' : ∀ y, hf d e' (pr y) = 0 := by
    intro y; simp only [pr]; rw [hf_sub, he'e, he'e']; ring
  have hpre_l : ∀ y, hf d (pr y) e = 0 := by intro y; rw [hf_symm d hd, hpre, star_zero]
  have hpre'_l : ∀ y, hf d (pr y) e' = 0 := by intro y; rw [hf_symm d hd, hpre', star_zero]
  let col : Fin n → Fin n → ℂ := fun j => if j = p then e else if j = q then e' else pr (Pi.single j 1)
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => col j i
  have hPcol : ∀ j, P *ᵥ Pi.single j 1 = col j := by
    intro j; ext i; simp [P, mulVec_single_one]
  have hgram : ∀ a b, (Pᴴ * Jm ε * P) a b = hf d (col a) (col b) := by
    intro a b
    rw [hJ, Matrix.mul_apply]; simp only [Matrix.mul_diagonal]
    simp [hf, P, Matrix.conjTranspose_apply]
  have hcolp : col p = e := by simp [col]
  have hcolq : col q = e' := by simp [col, hpq.symm]
  have hcolr : ∀ r, r ≠ p → r ≠ q → col r = pr (Pi.single r 1) := by
    intro r h1 h2; simp [col, h1, h2]
  have hGram : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      hf d (col a) (col b) = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0 := by
    intro a b hab
    rcases eq_or_ne a p with rfl | hap
    · rcases eq_or_ne b a with rfl | hba
      · simp [hcolp, hee, hpq]
      rcases eq_or_ne b q with rfl | hbq
      · simp [hcolp, hcolq, hee']
      · simp [hcolp, hcolr b hba hbq, hpre, hba, hbq]
    rcases eq_or_ne a q with rfl | haq
    · rcases eq_or_ne b p with rfl | hbp
      · simp [hcolp, hcolq, he'e]
      rcases eq_or_ne b a with rfl | hbq
      · simp [hcolq, he'e', hap]
      · simp [hcolq, hcolr b hbp hbq, hpre', hbp, hbq]
    · rcases hab with h | h | rfl | rfl
      · exact absurd h hap
      · exact absurd h haq
      · simp [hcolp, hcolr a hap haq, hpre_l, hap, haq]
      · simp [hcolq, hcolr a hap haq, hpre'_l, hap, haq]
  have key : ∀ x v, hf d x (P *ᵥ v) = ∑ j, v j * hf d x (col j) := by
    intro x v
    simp only [hf, mulVec, dotProduct, P, of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hecol : ∀ j, hf d e (col j) = if j = q then 1 else 0 := by
    intro j
    rcases eq_or_ne j p with rfl | hjp
    · simp [hcolp, hee, hpq]
    rcases eq_or_ne j q with rfl | hjq
    · simp [hcolq, hee']
    · simp [hcolr j hjp hjq, hpre, hjq]
  have he'col : ∀ j, hf d e' (col j) = if j = p then 1 else 0 := by
    intro j
    rcases eq_or_ne j p with rfl | hjp
    · simp [hcolp, he'e]
    rcases eq_or_ne j q with rfl | hjq
    · simp [hcolq, he'e', hjp]
    · simp [hcolr j hjp hjq, hpre', hjp]
  have hsingle : ∀ x j, hf d x (Pi.single j 1) = star (x j) * d j := by
    intro x j; simp [hf, Pi.single_apply]
  have h0 : ∀ x, hf d x 0 = 0 := by intro x; simp [hf]
  have hker : ∀ v, P *ᵥ v = 0 → v = 0 := by
    intro v hv
    have hvq : v q = 0 := by
      have := key e v
      rw [hv, h0] at this
      simp only [hecol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      exact this.symm
    have hvp : v p = 0 := by
      have := key e' v
      rw [hv, h0] at this
      simp only [he'col, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      exact this.symm
    have hPv : P *ᵥ v = pr v := by
      ext i
      have hterm : ∀ j, col j i * v j = pr (Pi.single j 1) i * v j := by
        intro j
        rcases eq_or_ne j p with rfl | hjp
        · simp [hvp]
        rcases eq_or_ne j q with rfl | hjq
        · simp [hvq]
        rw [hcolr j hjp hjq]
      simp only [mulVec, dotProduct, P, of_apply]
      rw [Finset.sum_congr rfl fun j _ => hterm j]
      simp only [pr, hsingle]
      have h1 : ∑ j, (Pi.single j (1:ℂ) : Fin n → ℂ) i * v j = v i := by simp [Pi.single_apply]
      simp only [sub_mul, Finset.sum_sub_distrib, h1]
      rw [sub_sub, sub_sub]
      congr 1
      simp only [hf, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hPv] at hv
    have hvi : ∀ i, v i = hf d e' v * e i + hf d e v * e' i := by
      intro i; have := congrFun hv i; simp only [pr, Pi.zero_apply] at this
      linear_combination this
    have hp0 : hf d e' v * e p + hf d e v * e' p = 0 := by rw [← hvi p, hvp]
    have hq0 : hf d e' v * e q + hf d e v * e' q = 0 := by rw [← hvi q, hvq]
    have hβ : hf d e v = 0 := by
      have : hf d e v * f q = 0 := by
        simp only [f]; field_simp; linear_combination e p * hq0 - e q * hp0
      exact (mul_eq_zero.mp this).resolve_right hq
    have hα : hf d e' v = 0 := by
      rw [hβ, zero_mul, add_zero] at hp0; exact (mul_eq_zero.mp hp0).resolve_right hp
    ext i; rw [hvi, hα, hβ]; simp
  have hunit : IsUnit P := by
    refine (Matrix.mulVec_injective_iff_isUnit).mp fun v w h => ?_
    have := hker (v - w) (by rw [Matrix.mulVec_sub, h, sub_self])
    exact sub_eq_zero.mp this
  refine ⟨P, p, q, c, hunit, hpq, by rw [hPcol, hcolp], ?_, fun a b hab => by rw [hgram]; exact hGram a b hab⟩
  rw [hPcol, hcolq]; ext i; simp [e', hJ, mulVec_diagonal]

end GlobalTheory.IsotropicPartner
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HyperbolicPairInFirstFlagSpace
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)

noncomputable section

namespace GlobalTheory.UnipRadUnit

variable {n : ℕ}

def RadCond (ε : Fin n → Bool) (e : Fin n → ℂ) (Y : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Y *ᵥ e = 0 ∧ (∀ y, star e ⬝ᵥ (Jm ε *ᵥ y) = 0 → ∃ c : ℂ, Y *ᵥ y = c • e) ∧
    ∀ y, star e ⬝ᵥ (Jm ε *ᵥ (Y *ᵥ y)) = 0

theorem RadCond.add {ε : Fin n → Bool} {e : Fin n → ℂ} {Y Y' : Matrix (Fin n) (Fin n) ℂ}
    (h : RadCond ε e Y) (h' : RadCond ε e Y') : RadCond ε e (Y + Y') := by
  refine ⟨by rw [add_mulVec, h.1, h'.1, add_zero], fun y hy => ?_, fun y => ?_⟩
  · obtain ⟨c, hc⟩ := h.2.1 y hy
    obtain ⟨c', hc'⟩ := h'.2.1 y hy
    exact ⟨c + c', by rw [add_mulVec, hc, hc', add_smul]⟩
  · rw [add_mulVec, mulVec_add, dotProduct_add, h.2.2, h'.2.2, add_zero]

theorem RadCond.smul {ε : Fin n → Bool} {e : Fin n → ℂ} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : RadCond ε e Y) (s : ℂ) : RadCond ε e (s • Y) := by
  refine ⟨by rw [Matrix.smul_mulVec, h.1, smul_zero], fun y hy => ?_, fun y => ?_⟩
  · obtain ⟨c, hc⟩ := h.2.1 y hy
    exact ⟨s * c, by rw [Matrix.smul_mulVec, hc, smul_smul]⟩
  · rw [Matrix.smul_mulVec, mulVec_smul, dotProduct_smul, h.2.2, smul_zero]

theorem RadCond.neg {ε : Fin n → Bool} {e : Fin n → ℂ} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : RadCond ε e Y) : RadCond ε e (-Y) := by
  simpa using h.smul (-1)

theorem RadCond.sub {ε : Fin n → Bool} {e : Fin n → ℂ} {Y Y' : Matrix (Fin n) (Fin n) ℂ}
    (h : RadCond ε e Y) (h' : RadCond ε e Y') : RadCond ε e (Y - Y') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

theorem RadCond.pow_three {ε : Fin n → Bool} {e : Fin n → ℂ} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : RadCond ε e Y) : Y ^ 3 = 0 := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  obtain ⟨c, hc⟩ := h.2.1 (Y *ᵥ Pi.single i 1) (h.2.2 _)
  rw [zero_mulVec, pow_succ, pow_two, ← mulVec_mulVec, ← mulVec_mulVec, hc, mulVec_smul, h.1, smul_zero]

theorem RadCond.exp_mulVec {ε : Fin n → Bool} {e : Fin n → ℂ} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : RadCond ε e Y) (y : Fin n → ℂ) (hy : star e ⬝ᵥ (Jm ε *ᵥ y) = 0) :
    NormedSpace.exp Y *ᵥ y = y + Y *ᵥ y := by
  have h3 := h.pow_three
  have hexp : NormedSpace.exp Y = ∑ k ∈ Finset.range 3, ((k.factorial : ℂ)⁻¹) • Y ^ k := by
    rw [NormedSpace.exp_eq_tsum ℂ]
    refine tsum_eq_sum fun k hk => ?_
    simp only [Finset.mem_range, not_lt] at hk
    rw [← Nat.add_sub_cancel' hk, pow_add, h3, zero_mul, smul_zero]
  obtain ⟨c, hc⟩ := h.2.1 y hy
  have h2 : Y *ᵥ (Y *ᵥ y) = 0 := by rw [hc, mulVec_smul, h.1, smul_zero]
  rw [hexp]
  simp [Finset.sum_range_succ, add_mulVec, Matrix.smul_mulVec, pow_two, ← mulVec_mulVec, h2]

theorem expG_mem_flagN {ε : Fin n → Bool} {a : ℕ} {j : Fin a → ℕ}
    {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)} (h : 0 < a) (hW : IsIsoFlag ε j W) (hj : j ⟨0, h⟩ = 1)
    {e : Fin n → ℂ} (he : e ∈ W ⟨1, Nat.succ_lt_succ h⟩) (he0 : e ≠ 0)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ lieSet ε) (hR : RadCond ε e Y) (t : ℝ) :
    expG ε Y t ∈ flagN ε W := by
  obtain ⟨hW0, hmono, hrank, hiso⟩ := hW
  have hrank1 : Module.finrank ℂ (W ⟨1, Nat.succ_lt_succ h⟩) = 1 := by
    have h1 := hrank ⟨0, h⟩
    have hc : (⟨0, h⟩ : Fin a).castSucc = 0 := Fin.ext rfl
    rw [hc, hW0, finrank_bot, hj, zero_add] at h1
    exact h1
  have hspan : ∀ y ∈ W ⟨1, Nat.succ_lt_succ h⟩, ∃ d : ℂ, y = d • e := by
    intro y hy
    have he0' : (⟨e, he⟩ : W ⟨1, Nat.succ_lt_succ h⟩) ≠ 0 := fun h0 => he0 (congrArg Subtype.val h0)
    obtain ⟨d, hd⟩ := (finrank_eq_one_iff_of_nonzero' _ he0').mp hrank1 ⟨y, hy⟩
    exact ⟨d, (congrArg Subtype.val hd).symm⟩
  have hlast : W ⟨1, Nat.succ_lt_succ h⟩ ≤ W (Fin.last a) := hmono (Fin.le_last _)
  have hperp : ∀ y ∈ W (Fin.last a), star e ⬝ᵥ (Jm ε *ᵥ y) = 0 := fun y hy => hiso e (hlast he) y hy
  have hRZ := hR.smul (t : ℂ)
  have hexp : uMat (expG ε Y t) = NormedSpace.exp ((t : ℂ) • Y) := toM_expG ε Y t hY
  have key : ∀ y, star e ⬝ᵥ (Jm ε *ᵥ y) = 0 → ∃ c : ℂ, uMat (expG ε Y t) *ᵥ y - y = c • e := by
    intro y hy
    rw [hexp, hRZ.exp_mulVec y hy, add_sub_cancel_left]
    exact hRZ.2.1 y hy
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · have hy' := hperp y (hmono (Fin.le_last _) hy)
    rcases Nat.eq_zero_or_pos i.val with hi | hi
    · have hi' : i.succ = ⟨1, Nat.succ_lt_succ h⟩ := Fin.ext (by simp [hi])
      rw [hi'] at hy
      obtain ⟨d, rfl⟩ := hspan y hy
      rw [hexp, hRZ.exp_mulVec _ hy', add_sub_cancel_left, mulVec_smul, hRZ.1, smul_zero]
      exact zero_mem _
    · obtain ⟨c, hc⟩ := key y hy'
      rw [hc]
      have hle : (⟨1, Nat.succ_lt_succ h⟩ : Fin (a + 1)) ≤ i.castSucc := by
        rw [Fin.le_def]; simp; omega
      exact hmono hle (Submodule.smul_mem _ c he)
  · obtain ⟨c, hc⟩ := key y (hy e (hlast he))
    rw [hc]
    exact hlast (Submodule.smul_mem _ c he)

def theta (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  -(Jm ε * Zᴴ * Jm ε)

theorem Jm_Jm_mul (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * M) = M := by
  rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]

theorem re_mem (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (2⁻¹ : ℂ) • (Z + theta ε Z) ∈ lieSet ε := by
  show ((2⁻¹ : ℂ) • (Z + theta ε Z))ᴴ * Jm ε + Jm ε * ((2⁻¹ : ℂ) • (Z + theta ε Z)) = 0
  simp only [theta, conjTranspose_smul, conjTranspose_add, conjTranspose_neg, conjTranspose_mul,
    Jm_conjTranspose, conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one, Jm_Jm_mul]
  simp

theorem im_mem (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    (Complex.I / 2) • (theta ε Z - Z) ∈ lieSet ε := by
  show ((Complex.I / 2) • (theta ε Z - Z))ᴴ * Jm ε + Jm ε * ((Complex.I / 2) • (theta ε Z - Z)) = 0
  simp only [theta, conjTranspose_smul, conjTranspose_sub, conjTranspose_neg, conjTranspose_mul,
    Jm_conjTranspose, conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one, Jm_Jm_mul]
  simp
  module

theorem decomp {ε : Fin n → Bool} {a : ℕ} {j : Fin a → ℕ}
    {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)} (h : 0 < a) (hW : IsIsoFlag ε j W) (hj : j ⟨0, h⟩ = 1)
    {e : Fin n → ℂ} (he : e ∈ W ⟨1, Nat.succ_lt_succ h⟩) (he0 : e ≠ 0)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : RadCond ε e Z) (hθ : RadCond ε e (theta ε Z)) :
    ∃ X X' : Matrix (Fin n) (Fin n) ℂ, X ∈ lieSet ε ∧ X' ∈ lieSet ε ∧ (∀ t, expG ε X t ∈ flagN ε W) ∧
      (∀ t, expG ε X' t ∈ flagN ε W) ∧ Z = X + Complex.I • X' := by
  refine ⟨(2⁻¹ : ℂ) • (Z + theta ε Z), (Complex.I / 2) • (theta ε Z - Z), re_mem ε Z, im_mem ε Z,
    expG_mem_flagN h hW hj he he0 (re_mem ε Z) ((hZ.add hθ).smul _),
    expG_mem_flagN h hW hj he he0 (im_mem ε Z) ((hθ.sub hZ).smul _), ?_⟩
  rw [smul_smul, show Complex.I * (Complex.I / 2) = -2⁻¹ by rw [← mul_div_assoc, Complex.I_mul_I]; ring]
  module

theorem vecMulVec_mulVec' (x φ y : Fin n → ℂ) : vecMulVec x φ *ᵥ y = (φ ⬝ᵥ y) • x := by
  rw [vecMulVec_mulVec, op_smul_eq_smul]

theorem theta_vecMulVec (ε : Fin n → Bool) (x φ : Fin n → ℂ) :
    theta ε (vecMulVec x φ) = -vecMulVec (Jm ε *ᵥ star φ) (star x ᵥ* Jm ε) := by
  rw [theta, conjTranspose_vecMulVec, mul_vecMulVec, vecMulVec_mul]

theorem radCond_col {ε : Fin n → Bool} {e : Fin n → ℂ} (hfe : star e ⬝ᵥ (Jm ε *ᵥ e) = 0)
    (φ : Fin n → ℂ) (hφ : φ ⬝ᵥ e = 0) : RadCond ε e (vecMulVec e φ) := by
  refine ⟨by rw [vecMulVec_mulVec', hφ, zero_smul], fun y _ => ⟨φ ⬝ᵥ y, vecMulVec_mulVec' _ _ _⟩,
    fun y => ?_⟩
  rw [vecMulVec_mulVec', mulVec_smul, dotProduct_smul, hfe, smul_zero]

theorem radCond_row {ε : Fin n → Bool} {e : Fin n → ℂ} (hfe : star e ⬝ᵥ (Jm ε *ᵥ e) = 0)
    (x : Fin n → ℂ) (hx : star e ⬝ᵥ (Jm ε *ᵥ x) = 0) :
    RadCond ε e (vecMulVec x (star e ᵥ* Jm ε)) := by
  refine ⟨by rw [vecMulVec_mulVec', ← dotProduct_mulVec, hfe, zero_smul], fun y hy => ⟨0, ?_⟩, fun y => ?_⟩
  · rw [vecMulVec_mulVec', ← dotProduct_mulVec, hy, zero_smul, zero_smul]
  · rw [vecMulVec_mulVec', mulVec_smul, dotProduct_smul, hx, smul_zero]

theorem single_eq_vecMulVec (p b : Fin n) :
    Matrix.single p b (1 : ℂ) = vecMulVec (Pi.single p 1) (Pi.single b 1) := by
  ext i k
  rcases eq_or_ne p i with rfl | hi
  · rcases eq_or_ne b k with rfl | hk
    · simp [vecMulVec_apply, Matrix.single_apply]
    · simp [vecMulVec_apply, Matrix.single_apply, hk, hk.symm]
  · simp [vecMulVec_apply, Matrix.single_apply, hi, hi.symm]

theorem matrixUnits_mem_radical : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a) (h : 0 < a), IsIsoFlag ε j W → j ⟨0, h⟩ = 1 → ∀ (P : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) (c : ℂ), IsUnit P → p ≠ q → P *ᵥ Pi.single p 1 ∈ W ⟨1, Nat.succ_lt_succ h⟩ → P *ᵥ Pi.single q 1 = c • (Jm ε *ᵥ (P *ᵥ Pi.single p 1)) → (∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) → (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0) → (∀ b, b ≠ p → ∃ X X' : Matrix (Fin n) (Fin n) ℂ, X ∈ lieSet ε ∧ X' ∈ lieSet ε ∧ (∀ t, expG ε X t ∈ flagN ε W) ∧ (∀ t, expG ε X' t ∈ flagN ε W) ∧ P * Matrix.single p b 1 * P⁻¹ = X + Complex.I • X') ∧ ∀ b, b ≠ q → ∃ X X' : Matrix (Fin n) (Fin n) ℂ, X ∈ lieSet ε ∧ X' ∈ lieSet ε ∧ (∀ t, expG ε X t ∈ flagN ε W) ∧ (∀ t, expG ε X' t ∈ flagN ε W) ∧ P * Matrix.single b q 1 * P⁻¹ = X + Complex.I • X' := by
  intro n ε a j W h hW hj P p q c hP hpq hp hq hG
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPP' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  set e := P *ᵥ Pi.single p 1 with he_def
  have hPe : P⁻¹ *ᵥ e = Pi.single p 1 := by rw [he_def, mulVec_mulVec, hPP, one_mulVec]
  have he0 : e ≠ 0 := by
    intro h0
    have h1 := congrFun hPe p
    rw [h0, mulVec_zero] at h1
    simp at h1
  have hGp : ∀ k, (Pᴴ * Jm ε * P) p k = if k = q then 1 else 0 := by
    intro k
    rw [hG p k (Or.inl rfl)]
    by_cases hk : k = q <;> simp [hk, hpq]
  have hf : ∀ y, star e ⬝ᵥ (Jm ε *ᵥ y) = (P⁻¹ *ᵥ y) q := by
    intro y
    have hy : y = P *ᵥ (P⁻¹ *ᵥ y) := by rw [mulVec_mulVec, hPP', one_mulVec]
    conv_lhs => rw [hy]
    rw [he_def, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
    generalize P⁻¹ *ᵥ y = v
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, hGp]
  have hfe : star e ⬝ᵥ (Jm ε *ᵥ e) = 0 := by
    rw [hf, hPe]; simp [hpq.symm]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · have hZ : P * Matrix.single p b 1 * P⁻¹ = vecMulVec e (Pi.single b 1 ᵥ* P⁻¹) := by
      rw [single_eq_vecMulVec, mul_vecMulVec, vecMulVec_mul]
    have hre : (Pi.single b 1 ᵥ* P⁻¹) ⬝ᵥ e = 0 := by
      rw [← dotProduct_mulVec, hPe]; simp [hb]
    have h1 := radCond_col hfe _ hre
    have h2 : RadCond ε e (theta ε (vecMulVec e (Pi.single b 1 ᵥ* P⁻¹))) := by
      rw [theta_vecMulVec]
      refine (radCond_row hfe _ ?_).neg
      rw [mulVec_mulVec, Jm_mul_self, one_mulVec, star_dotProduct, star_star, hre, star_zero]
    rw [hZ]
    exact decomp h hW hj hp he0 h1 h2
  · have hZ : P * Matrix.single b q 1 * P⁻¹ = vecMulVec (P *ᵥ Pi.single b 1) (Pi.single q 1 ᵥ* P⁻¹) := by
      rw [single_eq_vecMulVec, mul_vecMulVec, vecMulVec_mul]
    have hs : Pi.single q 1 ᵥ* P⁻¹ = star e ᵥ* Jm ε := by
      funext k
      have h1 := hf (Pi.single k 1)
      rw [dotProduct_mulVec] at h1
      simpa [Matrix.mulVec, Matrix.vecMul, dotProduct, Pi.single_apply] using h1.symm
    have hv : star e ⬝ᵥ (Jm ε *ᵥ (P *ᵥ Pi.single b 1)) = 0 := by
      rw [hf, mulVec_mulVec, hPP, one_mulVec]; simp [hb]
    have h1 := radCond_row hfe _ hv
    have h2 : RadCond ε e (theta ε (vecMulVec (P *ᵥ Pi.single b 1) (star e ᵥ* Jm ε))) := by
      rw [theta_vecMulVec, star_vecMul, Jm_conjTranspose, star_star, mulVec_mulVec, Jm_mul_self, one_mulVec]
      refine (radCond_col hfe _ ?_).neg
      rw [← dotProduct_mulVec, star_dotProduct, star_mulVec, Jm_conjTranspose, ← dotProduct_mulVec, hv,
        star_zero]
    rw [hZ, hs]
    exact decomp h hW hj hp he0 h1 h2

end GlobalTheory.UnipRadUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionInStagesRestriction
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem restr_mem_indFun_stage : ∀ {n a b : ℕ} {ε : Fin n → Bool} {W : Flag n a} {W' : Flag n b} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (τ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U)) (s' : Fin b → ℂ) (y : Fin b → ℝ), (∀ x t, IsSplit ε W' x t → t ∈ leviOne ε W → pairing (fun _ => 1) s' x = pairing (fun _ => 1) (fun l => Complex.I * y l) x) → ∀ {F : UJ ε → U}, F ∈ indFun ⊤ (fun _ => 1) W' τ s' → ∀ g, restr (leviOne ε W) F g ∈ indFun (leviOne ε W) (fun _ => 1) W' τ (fun l => Complex.I * y l) := by
  intro n a b ε W W' U _ _ τ s' y hs F hF g
  rw [mem_indFun_top] at hF
  obtain ⟨hc, hlaw⟩ := hF
  refine ⟨?_, fun g' hg' => restr_of_not_mem F g hg', ?_⟩
  · exact ((hc.comp (continuous_mul_const g)).continuousOn).congr fun m hm => restr_of_mem F g hm
  · intro u hu m hm x t ht h1 h2 h3 g' hg'
    have hM : u * m * t * g' ∈ leviOne ε W :=
      (leviOne ε W).mul_mem ((leviOne ε W).mul_mem ((leviOne ε W).mul_mem h1 h2) h3) hg'
    rw [restr_of_mem F g hM, restr_of_mem F g hg', mul_assoc (u * m * t) g' g, hlaw u hu m hm x t ht]
    congr 2
    have e : ∀ s r : Fin b → ℂ, pairing (fun _ => 1) (s + r) x =
        pairing (fun _ => 1) s x + pairing (fun _ => 1) r x := by
      intro s r
      simp only [pairing, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
    rw [e, e, hs x t ht h3]

end GlobalTheory.RealInd.Stages
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerNonzeroOnGeneratingSetStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_nonzero_on_generating_set : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (UJset ε) ρ → IsIrredOn (UJset ε) ρ → IsURepOn (UJset ε) π → ∀ (T : H →ₗ[ℂ] V) (Y₀ : Set H) (y₀ a₀ : H), y₀ ∈ Y₀ → T y₀ ≠ 0 → (∀ y ∈ Y₀, ∀ g ∈ UJset ε, ⟪a₀, ρ g y⟫_ℂ = ⟪T y₀, π g (T y)⟫_ℂ) → ∃ B : H →L[ℂ] V, B ≠ 0 ∧ ∀ g ∈ UJset ε, ∀ x, B (ρ g x) = π g (B x) := by
  first | exact @GlobalTheory.GraphIntertwiner.exists_intertwiner | exact GlobalTheory.GraphIntertwiner.exists_intertwiner | (intros; apply GlobalTheory.GraphIntertwiner.exists_intertwiner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemAtConjOfOtherPrimeOverSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

namespace GlobalTheory.ConjSplitIdem

theorem isIdemAt_cA_of_ne : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)), w ≠ w' → w.under (𝓞 D.host.F) = v → w'.under (𝓞 D.host.F) = v → ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → Formalism.L2.NTheta.IsIdemAt (cA D ε) w' := by
  intro D v w w' hne hw hw' ε hε
  rcases GlobalTheory.GridPlaces.eq_or_eq_conjP (P := w) (Q := w') (by rw [hw, hw']) with h | h
  · exact absurd h.symm hne
  · subst h
    exact GlobalTheory.MovedIdem.isIdemAt_conj hε (fun x => Iff.rfl)

end GlobalTheory.ConjSplitIdem
end

