import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0112
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0150
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0171
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0157
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0174

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBMemKummerInvariantSet
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.StabGal
theorem klm_sl_gal_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l M : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) (ζ : Ω) (d : ℤ) (γ γ'' : SL(2, ℤ)), 0 < M → IsPrimitiveRoot ζ M → s ζ = ζ ^ d → ((en γ 0 0 : ZMod M) = en γ'' 0 0 ∧ (en γ 0 1 : ZMod M) = d * en γ'' 0 1 ∧ (d : ZMod M) * en γ 1 0 = en γ'' 1 0 ∧ (en γ 1 1 : ZMod M) = en γ'' 1 1) → ∀ y ∈ X.Lev l M, X.klm l (X.sl (ofSL γ)).toRingEquiv (X.klm l (X.gal s) y) = X.klm l (X.gal s) (X.klm l (X.sl (ofSL γ'')).toRingEquiv y) := by
  intro Ω _ _ ε X l M _ s ζ d γ γ'' hM hζ hsd hcong y hy
  refine Submodule.span_induction (p := fun y _ => X.klm l (X.sl (ofSL γ)).toRingEquiv (X.klm l (X.gal s) y) =
      X.klm l (X.gal s) (X.klm l (X.sl (ofSL γ'')).toRingEquiv y)) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨f, hf, rfl⟩
    have hr := X.recip M (f : X.K) hM hf ζ hζ s d hsd γ'' γ hcong
    simp only [Tower.klm, LinearMap.baseChange_tmul]
    congr 1
    apply Additive.toMul.injective
    apply Units.ext
    simp [hr]
  · simp
  · intro x y _ _ hx hy; simp [hx, hy]
  · intro a x _ hx; simp [hx]

theorem galB_mem_Pol : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω), (∀ a ∈ X.A l, X.kmap l (X.gal s) a ∈ X.A l) → ∀ b ∈ X.Pol l w, X.galB l s b ∈ X.Pol l w := by
  intro Ω _ _ ε X l w _ s hA b hb
  obtain ⟨c, hcA, hc⟩ := hb
  refine ⟨fun i => ((cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) ^ (w - (i : ℕ))) • X.kmap l (X.gal s) (c i),
    fun i => Submodule.smul_mem _ _ (hA _ (hcA i)), fun u => ?_⟩
  show X.kmap l (X.gal s) (b ![u 0, (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1]) = _
  rw [hc]
  simp only [map_sum, map_smul, Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ring

theorem eval_Pol_rep : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (b : X.Fn l), b ∈ X.Pol l w → ∀ n : ℕ, ∃ y : Fin (w + 1) → X.Kl l, ∀ x : Fin 2 → ℤ_[l], ∃ Y ∈ Submodule.span ℤ_[l] (Set.range y), AdicCompletion.eval (idl l) (X.Kl l) n (b x) = Submodule.Quotient.mk Y := by
  intro Ω _ _ ε X l w _ b hb n
  obtain ⟨c, _, hc⟩ := hb
  choose y hy using fun i => Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (c i))
  refine ⟨y, fun x => ⟨∑ i : Fin (w + 1), (x 0 ^ (i : ℕ) * x 1 ^ (w - (i : ℕ))) • y i,
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩⟩
  rw [hc, map_sum]
  simp only [map_smul]
  change _ = Submodule.mkQ _ _
  rw [map_sum]
  simp only [map_smul, Submodule.mkQ_apply, hy]

theorem eval_Pol_congr : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (b : X.Fn l), b ∈ X.Pol l w → ∀ (n : ℕ) (u v : Fin 2 → ℤ_[l]), (∀ i, PadicInt.toZModPow n (u i) = PadicInt.toZModPow n (v i)) → AdicCompletion.eval (idl l) (X.Kl l) n (b u) = AdicCompletion.eval (idl l) (X.Kl l) n (b v) := by
  intro Ω _ _ ε X l w _ b hb n u v huv
  obtain ⟨c, _, hc⟩ := hb
  rw [← sub_eq_zero, ← map_sub, hc, hc, ← Finset.sum_sub_distrib, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← sub_smul, map_smul]
  have hmem : (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ)) - v 0 ^ (i : ℕ) * v 1 ^ (w - (i : ℕ))) ∈ (idl l) ^ n := by
    rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_mul, map_mul, map_pow,
      map_pow, map_pow, map_pow, huv 0, huv 1, sub_self]
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (c i))
  rw [← hz, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hmem Submodule.mem_top

theorem twist_congr : ∀ (l n M : ℕ) [Fact l.Prime], l ^ n ∣ M → ∀ (γ γ'' : SL(2, ℤ)) (d : ℤ) (χ : ℤ_[l]), ((en γ 0 0 : ZMod M) = en γ'' 0 0 ∧ (en γ 0 1 : ZMod M) = d * en γ'' 0 1 ∧ (d : ZMod M) * en γ 1 0 = en γ'' 1 0 ∧ (en γ 1 1 : ZMod M) = en γ'' 1 1) → (d : ZMod (l ^ n)) = PadicInt.toZModPow n χ → ∀ (u : Fin 2 → ℤ_[l]) (i : Fin 2), PadicInt.toZModPow n ((![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1] : Fin 2 → ℤ_[l]) i) = PadicInt.toZModPow n ((mZl l (γ'' : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![u 0, χ * u 1]) i) := by
  intro l n M _ hlnM γ γ'' d χ hc hd u i
  obtain ⟨h00, h01, h10, h11⟩ := hc
  have cast : ∀ k : ℤ, ZMod.castHom hlnM (ZMod (l ^ n)) (k : ZMod M) = (k : ZMod (l ^ n)) := fun k => map_intCast _ k
  have e00 := congrArg (ZMod.castHom hlnM (ZMod (l ^ n))) h00
  have e01 := congrArg (ZMod.castHom hlnM (ZMod (l ^ n))) h01
  have e10 := congrArg (ZMod.castHom hlnM (ZMod (l ^ n))) h10
  have e11 := congrArg (ZMod.castHom hlnM (ZMod (l ^ n))) h11
  simp only [map_mul, cast] at e00 e01 e10 e11
  simp only [en] at e00 e01 e10 e11
  rw [hd] at e01 e10
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mZl, Matrix.map_apply, map_add, map_mul, map_intCast]
  · rw [← e00, e01]; ring
  · rw [← e10, ← e11]; ring

theorem toGQ_SL (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  have h : 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by simp
  unfold toGQ
  rw [dif_pos h]
  ext i j
  simp [ofSL]

theorem inv_galB {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (N l w : ℕ) [Fact l.Prime] (hN : 0 < N) (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) (hb : b ∈ X.BSet N l w)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) = X.galB l s b := by
  obtain ⟨hpol, hinv⟩ := hb
  funext u
  apply AdicCompletion.ext
  intro n
  obtain ⟨y, hy⟩ := eval_Pol_rep X l w b hpol n
  obtain ⟨M, hM, hdiv, hlev⟩ := GlobalTheory.T.exists_common_level_span_multiple X l (N * l * l ^ n) y
    (Nat.mul_pos (Nat.mul_pos hN (Nat.Prime.pos Fact.out)) (pow_pos (Nat.Prime.pos Fact.out) n))
  have hNM : N ∣ M := Dvd.dvd.trans ⟨l * l ^ n, by ring⟩ hdiv
  have hlM : l ∣ M := Dvd.dvd.trans ⟨N * l ^ n, by ring⟩ hdiv
  have hlnM : l ^ n ∣ M := Dvd.dvd.trans ⟨N * l, by ring⟩ hdiv
  obtain ⟨γ'', hγ'', ζ, hζ, d, hsd, hcong, hdχ⟩ := GlobalTheory.T.exists_conj_level_elem_exponent_shimura (Ω := Ω) N l n M hM hNM hlM hlnM s γ hγ
  have hspan : Submodule.span ℤ_[l] (Set.range y) ≤ X.Lev l M :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hlev i)
  set χ : ℤ_[l] := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hχ
  set v : Fin 2 → ℤ_[l] := ![u 0, χ * u 1] with hv
  have h1 := eval_Pol_congr X l w b hpol n _ _ (twist_congr l n M hlnM γ γ'' d χ hcong hdχ u)
  obtain ⟨Y, hY, hYe⟩ := hy (mZl l (γ'' : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v)
  have hinv' : AdicCompletion.eval (idl l) (X.Kl l) n (X.act l (γ'' : Matrix (Fin 2) (Fin 2) ℤ) b v) =
      AdicCompletion.eval (idl l) (X.Kl l) n (b v) := by rw [hinv γ'' hγ'']
  have hc := klm_sl_gal_comm X l M s ζ d γ γ'' hM hζ hsd hcong Y (hspan hY)
  show (X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (X.kmap l (X.gal s) (b ![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1]))).val n =
    (X.kmap l (X.gal s) (b v)).val n
  rw [toGQ_SL]
  change (X.klm l (X.sl (ofSL γ)).toRingEquiv).reduceModIdeal ((idl l)^n)
      ((X.klm l (X.gal s)).reduceModIdeal ((idl l)^n) (AdicCompletion.eval (idl l) (X.Kl l) n (b _))) =
    (X.klm l (X.gal s)).reduceModIdeal ((idl l)^n) (AdicCompletion.eval (idl l) (X.Kl l) n (b v))
  rw [h1, hYe, ← hinv']
  change _ = (X.klm l (X.gal s)).reduceModIdeal ((idl l)^n)
    ((X.klm l (X.sl (toGQ (γ'' : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv).reduceModIdeal ((idl l)^n)
      (AdicCompletion.eval (idl l) (X.Kl l) n (b (mZl l (γ'' : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v))))
  rw [toGQ_SL, hYe]
  simp only [LinearMap.reduceModIdeal_apply]
  rw [hc]

theorem galB_mem_B : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.galB l s b ∈ X.B N l w := by
  intro Ω _ _ _ ε X hε hj N l w _ _ hN _ _ s b hb
  have hA := (GlobalTheory.T.modular_function_tower_integrality ε X hε hj l).2 s
  have hN0 : 0 < N := by omega
  have himg : X.galB l s '' X.BSet N l w ⊆ X.BSet N l w := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨galB_mem_Pol X l w s hA c hc.1, fun γ hγ => inv_galB X N l w hN0 s c hc γ hγ⟩
  exact Submodule.span_mono himg (Submodule.apply_mem_span_image_of_mem_span (X.galB l s) hb)

end GlobalTheory.KZ.StabGal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodSquarefreeLabelTuplesWeightGe
section
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

variable (g : ℕ) [Fact g.Prime]

def tupleMass {ι : Type} [Fintype ι] (N : ℕ) (P : (ι → (ZMod g)[X]) → Prop) : ℝ :=
  ∑ F ∈ Fintype.piFinset fun _ : ι => sqSet g N, if P F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0

variable {g} {ι : Type} [Fintype ι] {N : ℕ}

theorem tupleWeight_nonneg (F : ι → (ZMod g)[X]) : 0 ≤ ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
  exact Finset.prod_nonneg fun v _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem tupleMass_le_add {P Q R : (ι → (ZMod g)[X]) → Prop}
    (h : ∀ F, (∀ v, F v ∈ sqSet g N) → P F → Q F ∨ R F) :
    tupleMass g N P ≤ tupleMass g N Q + tupleMass g N R := by
  unfold tupleMass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun F hF => ?_
  have hw := tupleWeight_nonneg F
  have hmem : ∀ v, F v ∈ sqSet g N := fun v => Fintype.mem_piFinset.mp hF v
  by_cases hP : P F
  · rw [if_pos hP]
    rcases h F hmem hP with hQ | hR
    · rw [if_pos hQ]; split_ifs <;> linarith
    · rw [if_pos hR]; split_ifs <;> linarith
  · rw [if_neg hP]; split_ifs <;> linarith

theorem tupleMass_exists_le {κ : Type} (s : Finset κ) (Q : κ → (ι → (ZMod g)[X]) → Prop) :
    tupleMass g N (fun F => ∃ i ∈ s, Q i F) ≤ ∑ i ∈ s, tupleMass g N (Q i) := by
  unfold tupleMass
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun F _ => ?_
  have hz : ∀ j ∈ s, 0 ≤ (if Q j F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0) := fun j _ => by
    split_ifs
    · exact tupleWeight_nonneg F
    · exact le_rfl
  split_ifs with h
  · obtain ⟨i, hi, hQ⟩ := h
    calc ∏ v, ((torusCard g (F v) : ℝ))⁻¹ = (if Q i F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0) := by rw [if_pos hQ]
      _ ≤ ∑ j ∈ s, if Q j F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0 :=
        Finset.single_le_sum (f := fun j => if Q j F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0) hz hi
  · exact Finset.sum_nonneg hz

theorem tupleMass_forall (A : ι → (ZMod g)[X] → Prop) :
    tupleMass g N (fun F => ∀ v, A v (F v)) = ∏ v, mass g N (A v) := by
  unfold tupleMass mass
  simp_rw [Finset.sum_filter]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  split_ifs with h
  · exact Finset.prod_congr rfl fun v _ => (if_pos (h v)).symm
  · push Not at h
    obtain ⟨v, hv⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)).symm

theorem tupleMass_single_le (h1 : (mass g N fun _ => True) ≤ 1) (v : ι) (A : (ZMod g)[X] → Prop) :
    tupleMass g N (fun F : ι → (ZMod g)[X] => A (F v)) ≤ mass g N A := by
  have hm : ∀ B : (ZMod g)[X] → Prop, 0 ≤ mass g N B := fun B => by
    unfold mass
    exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  have key : tupleMass g N (fun F : ι → (ZMod g)[X] => A (F v)) =
      tupleMass g N (fun F => ∀ w, (if w = v then A else fun _ => True) (F w)) := by
    unfold tupleMass
    refine Finset.sum_congr rfl fun F _ => ?_
    have hiff : A (F v) ↔ ∀ w, (if w = v then A else fun _ => True) (F w) :=
      ⟨fun h w => by by_cases hw : w = v <;> simp_all, fun h => by simpa using h v⟩
    by_cases h : A (F v)
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (mt hiff.mpr h)]
  rw [key, tupleMass_forall, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), if_pos rfl]
  have hrest : ∏ w ∈ Finset.univ.erase v, mass g N (if w = v then A else fun _ => True) ≤ 1 := by
    apply Finset.prod_le_one
    · exact fun w _ => hm _
    · intro w hw
      rw [if_neg (Finset.ne_of_mem_erase hw)]
      exact h1
  calc mass g N A * _ ≤ mass g N A * 1 := mul_le_mul_of_nonneg_left hrest (hm A)
    _ = _ := mul_one _

theorem goodSet_weight_ge : ∀ (g : ℕ) [Fact g.Prime], ∀ (N m q d : ℕ) (ι : Type) [Fintype ι] (ch : ι → Fin m → (ZMod g)ˣ), 100000 ≤ N → 2 ^ 12 ≤ g → (q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1) → 1 - (badBound g (Fintype.card ι) m N ((min q d : ℕ) : ℝ) - (Fintype.card ι : ℝ) / g) ≤ ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
  intro g _ N m q d ι _ ch hN hg hqd
  have hm : ∀ B : (ZMod g)[X] → Prop, 0 ≤ mass g N B := fun B => by
    unfold mass
    exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  have h1 : (mass g N fun _ => True) ≤ 1 := (GlobalTheory.T.squarefreeLabelTorusMass_divisor_bound g).1 N
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (Fact.out : g.Prime).pos
  have hg4 : (4096 : ℝ) ≤ g := by exact_mod_cast hg
  have hN' : (100000 : ℝ) ≤ N := by exact_mod_cast hN
  have hall : 1 - 2 * (Fintype.card ι : ℝ) / g ≤ tupleMass g N (fun _ : ι → (ZMod g)[X] => True) := by
    have e := tupleMass_forall (g := g) (N := N) (fun (_ : ι) (_ : (ZMod g)[X]) => True)
    simp only [implies_true] at e
    rw [e]
    have h2 : 0 ≤ 1 - 2 / (g : ℝ) := by
      rw [sub_nonneg, div_le_one hg0]; linarith
    have h3 : (-2 : ℝ) ≤ -2 / g := by
      rw [le_div_iff₀ hg0]; nlinarith
    calc 1 - 2 * (Fintype.card ι : ℝ) / g = 1 + (Fintype.card ι : ℝ) * (-2 / g) := by ring
      _ ≤ (1 + (-2 / (g : ℝ))) ^ Fintype.card ι := one_add_mul_le_pow h3 _
      _ = ∏ _v : ι, (1 - 2 / (g : ℝ)) := by rw [Finset.prod_const, Finset.card_univ]; ring
      _ ≤ ∏ _v : ι, mass g N (fun _ => True) :=
        Finset.prod_le_prod (fun _ _ => h2) (fun _ _ => GlobalTheory.T.one_sub_two_div_le_squarefreeLabelMass g N)
  have hsq : ∀ f ∈ sqSet g N, (f.Monic ∧ f.natDegree = N ∧ f.coeff 0 ≠ 0) ∧ Squarefree f := by
    intro f hf
    unfold sqSet at hf
    rw [Finset.mem_filter, Finset.mem_image] at hf
    obtain ⟨⟨c, -, rfl⟩, hsf, hc0⟩ := hf
    have hdeg := degree_sum_fin_lt c
    refine ⟨⟨monic_X_pow_add hdeg, ?_, hc0⟩, hsf⟩
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  have hE1 : tupleMass g N (fun F : ι → (ZMod g)[X] => ∃ v ∈ Finset.univ, ¬ RootsApart g N (F v)) ≤
      (Fintype.card ι : ℝ) * (23 * Real.log g / Real.sqrt g) := by
    calc _ ≤ ∑ v ∈ Finset.univ, tupleMass g N (fun F : ι → (ZMod g)[X] => ¬ RootsApart g N (F v)) :=
          tupleMass_exists_le (Finset.univ : Finset ι) (fun (v : ι) (F : ι → (ZMod g)[X]) => ¬ RootsApart g N (F v))
      _ ≤ ∑ _v ∈ (Finset.univ : Finset ι), (23 * Real.log g / Real.sqrt g) :=
          Finset.sum_le_sum fun v _ => (tupleMass_single_le h1 v _).trans (GlobalTheory.T.squarefreeLabelTorusMass_rootsNotDistinct_le g N hg)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hE2 : ∀ c : ι → Fin m → (ZMod g)ˣ,
      tupleMass g N (fun F : ι → (ZMod g)[X] =>
        ∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (c p.1 p.2) (F p.1)) ≤
      (Fintype.card ι : ℝ) * m * (1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1)) := by
    intro c
    calc _ ≤ ∑ p ∈ (Finset.univ : Finset (ι × Fin m)),
            tupleMass g N (fun F : ι → (ZMod g)[X] => ¬ RootsAvoid g (c p.1 p.2) (F p.1)) :=
          tupleMass_exists_le (Finset.univ : Finset (ι × Fin m))
            (fun (p : ι × Fin m) (F : ι → (ZMod g)[X]) => ¬ RootsAvoid g (c p.1 p.2) (F p.1))
      _ ≤ ∑ _p ∈ (Finset.univ : Finset (ι × Fin m)),
            (1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1)) :=
          Finset.sum_le_sum fun p _ => (tupleMass_single_le h1 p.1 _).trans (GlobalTheory.T.mass_not_rootsAvoid_le' g N q d _ hqd)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have hE4 : tupleMass g N (fun F : ι → (ZMod g)[X] => ∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ≤
      (N : ℝ) / 2 * (7 / 8) ^ Fintype.card ι := by
    calc _ ≤ ∑ a ∈ Finset.Icc 1 (N / 2), tupleMass g N (fun F : ι → (ZMod g)[X] => ∀ v, HasDiv g a (F v)) :=
          tupleMass_exists_le (Finset.Icc 1 (N / 2)) (fun (a : ℕ) (F : ι → (ZMod g)[X]) => ∀ v, HasDiv g a (F v))
      _ = ∑ a ∈ Finset.Icc 1 (N / 2), ∏ _v : ι, mass g N (HasDiv g a) :=
          Finset.sum_congr rfl fun a _ => tupleMass_forall (fun _ => HasDiv g a)
      _ ≤ ∑ _a ∈ Finset.Icc 1 (N / 2), ((7 : ℝ) / 8) ^ Fintype.card ι := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [Finset.mem_Icc] at ha
          calc ∏ _v : ι, mass g N (HasDiv g a) ≤ ∏ _v : ι, ((7 : ℝ) / 8) :=
                Finset.prod_le_prod (fun _ _ => hm _) (fun _ _ => GlobalTheory.T.squarefreeLabelTorusMass_hasDivisorOfDegree_le g N a (by omega) (by omega))
            _ = _ := by rw [Finset.prod_const, Finset.card_univ]
      _ = ((N / 2 : ℕ) : ℝ) * (7 / 8) ^ Fintype.card ι := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
      _ ≤ _ := mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)
  have hL : (1 : ℝ) ≤ 10 * Real.log N := by
    have : (1 : ℝ) ≤ Real.log N :=
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log N := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    linarith
  have hE5 : tupleMass g N (fun F : ι → (ZMod g)[X] => ∀ v, ¬ HasPrimeFactor g N (F v)) ≤
      Real.exp (-((Fintype.card ι : ℝ) / (10 * Real.log N))) := by
    calc _ = ∏ _v : ι, mass g N (fun f => ¬ HasPrimeFactor g N f) :=
          tupleMass_forall (fun _ f => ¬ HasPrimeFactor g N f)
      _ ≤ ∏ _v : ι, (1 - 1 / (10 * Real.log N)) :=
          Finset.prod_le_prod (fun _ _ => hm _) (fun _ _ => GlobalTheory.T.squarefreeLabelTorusMass_no_large_prime_factor_le g N hN)
      _ = (1 + (-(1 / (10 * Real.log N)))) ^ Fintype.card ι := by
          rw [Finset.prod_const, Finset.card_univ]; ring
      _ ≤ (Real.exp (-(1 / (10 * Real.log N)))) ^ Fintype.card ι := by
          refine pow_le_pow_left₀ ?_ ?_ _
          · have : 1 / (10 * Real.log N) ≤ 1 := by rw [div_le_one (by linarith)]; exact hL
            linarith
          · linarith [Real.add_one_le_exp (-(1 / (10 * Real.log N)))]
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hsplit : ∀ F : ι → (ZMod g)[X], (∀ v, F v ∈ sqSet g N) → True →
      Good g N ch F ∨
      ((∃ v ∈ Finset.univ, ¬ RootsApart g N (F v)) ∨
      ((∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (ch p.1 p.2) (F p.1)) ∨
      ((∃ p ∈ (Finset.univ : Finset (ι × Fin m)),
          ¬ RootsAvoid g ((fun v j => (ch v j)⁻¹) p.1 p.2) (F p.1)) ∨
      ((∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ∨
      (∀ v, ¬ HasPrimeFactor g N (F v)))))) := by
    intro F hF _
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨hG, h1', h2', h3', h4', h5'⟩ := hcon
    apply hG
    have hA : ∀ v, RootsApart g N (F v) := fun v =>
      Classical.byContradiction fun h => h1' ⟨v, Finset.mem_univ _, h⟩
    have hB : ∀ v j, RootsAvoid g (ch v j) (F v) := fun v j =>
      Classical.byContradiction fun h => h2' ⟨(v, j), Finset.mem_univ _, h⟩
    have hC : ∀ v j, RootsAvoid g (ch v j)⁻¹ (F v) := fun v j =>
      Classical.byContradiction fun h => h3' ⟨(v, j), Finset.mem_univ _, h⟩
    have hD : ∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ v, ¬ HasDiv g a (F v) := fun a ha1 ha2 => by
      by_contra h
      push Not at h
      exact h4' ⟨a, Finset.mem_Icc.mpr ⟨ha1, by omega⟩, h⟩
    have hE : ∃ v, HasPrimeFactor g N (F v) := by
      by_contra h
      push Not at h
      exact h5' h
    unfold Good Formalism.CyclotomicNorms.IsGood
    exact ⟨⟨fun v => (hsq _ (hF v)).1, fun v => (hsq _ (hF v)).2,
        fun l hl hl' v => hA v l hl hl', fun l hl hlg v j => hB v j l hl hlg, hD, hE⟩,
      ⟨fun v => (hsq _ (hF v)).1, fun v => (hsq _ (hF v)).2,
        fun l hl hl' v => hA v l hl hl', fun l hl hlg v j => hC v j l hl hlg, hD, hE⟩⟩
  have hor : ∀ {P Q : (ι → (ZMod g)[X]) → Prop},
      tupleMass g N (fun F => P F ∨ Q F) ≤ tupleMass g N P + tupleMass g N Q :=
    fun {_ _} => tupleMass_le_add fun _ _ h => h
  have hgood : tupleMass g N (Good g N ch) = ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
    unfold tupleMass goodSet
    rw [Finset.sum_filter]
  have s0 := tupleMass_le_add hsplit
  have s1 := hor (P := fun F => (∃ v ∈ Finset.univ, ¬ RootsApart g N (F v)))
    (Q := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (ch p.1 p.2) (F p.1)) ∨ ((∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g ((fun v j => (ch v j)⁻¹) p.1 p.2) (F p.1)) ∨ ((∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ∨ (∀ v, ¬ HasPrimeFactor g N (F v)))))
  have s2 := hor (P := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (ch p.1 p.2) (F p.1)))
    (Q := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g ((fun v j => (ch v j)⁻¹) p.1 p.2) (F p.1)) ∨ ((∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ∨ (∀ v, ¬ HasPrimeFactor g N (F v))))
  have s3 := hor (P := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g ((fun v j => (ch v j)⁻¹) p.1 p.2) (F p.1)))
    (Q := fun F => (∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ∨ (∀ v, ¬ HasPrimeFactor g N (F v)))
  have s4 := hor (P := fun F => (∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)))
    (Q := fun F => (∀ v, ¬ HasPrimeFactor g N (F v)))
  beta_reduce at s0 s1 s2 s3 s4
  have b2 := hE2 ch
  have b3 := hE2 (fun v j => (ch v j)⁻¹)
  have hb4 := s4.trans (add_le_add hE4 hE5)
  have hb3 := s3.trans (add_le_add b3 hb4)
  have hb2 := s2.trans (add_le_add b2 hb3)
  have hb1 := s1.trans (add_le_add hE1 hb2)
  have hb0 := s0.trans (add_le_add le_rfl hb1)
  rw [← hgood]
  unfold badBound
  rw [Real.rpow_natCast]
  ring_nf at hall hb0 ⊢
  linarith only [hall, hb0]

end GlobalTheory.BadShare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterSlashSumIndepRepsStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacterSlashSum_indep_reps : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (Δ : Set M2) (ι κ : Type) [Fintype ι] [Fintype κ] (β : ι → M2) (β' : κ → M2) (f : ℍ → ℂ), 1 ≤ k → N ∣ L → (∀ δ ∈ Δ, 0 < δ.det ∧ (N : ℤ) ∣ δ 1 0) → LRep L Δ β → LRep L Δ β' → Inv k L (ch ε) f → hsum k (ch ε) β f = hsum k (ch ε) β' f := by
  first | exact @GlobalTheory.EisM.RepInd.hsum_indep | exact GlobalTheory.EisM.RepInd.hsum_indep | (intros; apply GlobalTheory.EisM.RepInd.hsum_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeSumPotentialsCocycleEqStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeSum_potentials_cocycle_eq : ∀ (N l w : ℕ) (α : Matrix (Fin 2) (Fin 2) ℤ) (ι : Type) [Fintype ι] (δ : ι → Matrix (Fin 2) (Fin 2) ℤ), 0 < N → 0 < l → 0 < α.det → GlobalTheory.HeckeFamilyMatrices.IsDCReps (GlobalTheory.HeckeFamilyMatrices.Lev N l) α δ → ∀ F ∈ Pot ℂ w (Gam N l), (∑ i, opP ℂ (δ i) F) ∈ Pot ℂ w (Gam N l) ∧ cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (∑ i, opP ℂ (δ i) F) = GlobalTheory.HeckeFamilyMatrices.hk (GlobalTheory.HeckeFamilyMatrices.Lev N l) w δ (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  first | exact @GlobalTheory.KZ.DictHk.dict_hk | exact GlobalTheory.KZ.DictHk.dict_hk | (intros; apply GlobalTheory.KZ.DictHk.dict_hk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralCoprimeSumUnfoldToUnitStripStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_coprime_sum_unfold_to_unitStrip : ∀ (L : ℕ) (ρ : ℍ → ℝ) (Ψ : ℍ → ℂ) (W : ℤ × ℤ → ℍ → ℂ), Wt L ρ → IntegrableOn Ψ strip → AEStronglyMeasurable Ψ → (∀ γ : SL(2, ℤ), (L : ℤ) ∣ γ 1 0 → ∀ τ, Ψ (γ • τ) = W (γ 1 0, γ 1 1) τ) → ∫ τ : ℍ, (ρ τ : ℂ) * ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}, W x.1 τ = ∫ τ in strip, Ψ τ := by
  first | exact @GlobalTheory.EisM.unfold_strip | exact GlobalTheory.EisM.unfold_strip | (intros; apply GlobalTheory.EisM.unfold_strip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCarryCoboundaryTwistCochain
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.NeedB.TwistCochain

theorem pow_mod_of_pow_eq_one' {Ω : Type} [Field Ω] {N : ℕ} {ζ : Ω} (hN : ζ ^ N = 1) (n : ℕ) :
    ζ ^ (n % N) = ζ ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n N, pow_add, pow_mul, hN, one_pow, one_mul]

theorem twist_cochain : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∀ w : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant w → (∀ g h, (w g : Ω) * g (w h) * α ^ (kum (N := N) ζ β (g * h)).val =
    α ^ ((kum (N := N) ζ β g).val + (kum (N := N) ζ β h).val) * w (g * h)) →
  ∃ v : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant v ∧
    ∀ g h, (v g : Ω) * g (v h) = ζ ^ (kum (N := N) ζ α g * kum (N := N) ζ β h).val * v (g * h) := by
  intro K Ω _ _ _ _ N ζ hN hζ hζfix a b α β ha hb hα hβ w hw hcoc
  haveI : NeZero N := ⟨hN.ne'⟩
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hα
    exact ha ((algebraMap K Ω).injective (by rw [← hα, map_zero]))
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hβ
    exact hb ((algebraMap K Ω).injective (by rw [← hβ, map_zero]))
  obtain ⟨-, hgα, -, -⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ α hN hζ hζfix hα0 ⟨a, hα.symm⟩
  obtain ⟨hylc, -, -, -⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ β hN hζ hζfix hβ0 ⟨b, hβ.symm⟩
  refine ⟨fun g => Units.mk0 α hα0 ^ (kum (N := N) ζ β g).val * (w g)⁻¹, ?_, ?_⟩
  · exact IsLocallyConstant.comp₂ hylc hw (fun (i : ZMod N) (u : Ωˣ) => Units.mk0 α hα0 ^ i.val * u⁻¹)
  · intro g h
    have hwg : (w g : Ω) ≠ 0 := (w g).ne_zero
    have hwh : g (w h : Ω) ≠ 0 := by simpa using (w h).ne_zero
    have hwgh : (w (g * h) : Ω) ≠ 0 := (w (g * h)).ne_zero
    have hz : ζ ^ (kum (N := N) ζ α g * kum (N := N) ζ β h).val =
        (ζ ^ (kum (N := N) ζ α g).val) ^ (kum (N := N) ζ β h).val := by
      rw [ZMod.val_mul, pow_mod_of_pow_eq_one' hζ.pow_eq_one, pow_mul]
    have hc := hcoc g h
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, map_mul, map_pow, Units.val_inv_eq_inv_val,
      map_inv₀, hgα g, hz]
    rw [pow_add] at hc
    field_simp
    rw [mul_pow]
    linear_combination -(ζ ^ (kum (N := N) ζ α g).val) ^ (kum (N := N) ζ β h).val * hc

end GlobalTheory.NeedB.TwistCochain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCarryCocycleCoboundaryOfNormsStatement
section
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_carry_cocycle_coboundary_of_norms : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  (∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 → ∃ x : L, Algebra.norm K x = c) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∃ w : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant w ∧ ∀ g h, (w g : Ω) * g (w h) * α ^ (kum (N := N) ζ β (g * h)).val =
    α ^ ((kum (N := N) ζ β g).val + (kum (N := N) ζ β h).val) * w (g * h) := by
  first | exact @GlobalTheory.NeedB.NormCob.carry_coboundary | exact GlobalTheory.NeedB.NormCob.carry_coboundary | (intros; apply GlobalTheory.NeedB.NormCob.carry_coboundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeFunctionDivisibleFirstSubstitutionStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeFunctionDivisibleFirst_substitution : ∀ (N l : ℕ) (ν : DirichletCharacter ℂ N) (φ : ZMod l → ℂ) (a b c d : ℤ),
    (N : ℤ) * a * d - l * b * c = 1 → 0 < N → 0 < l → ∀ y : ℤ × ℤ,
    (if (N : ℤ) ∣ y.1 then latF l (ch ν) φ (y.1 / N * (N * d) - y.2 * (l * c), -(y.1 / N * b) + y.2 * a) else 0) =
      latF (N * l) (fun _ => 1) (fun z => ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) z) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) z)) y := by
  first | exact @GlobalTheory.latF_rows_subst | exact GlobalTheory.latF_rows_subst | (intros; apply GlobalTheory.latF_rows_subst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TsenTheoremStatement
section
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsen_theorem : GlobalTheory.NeedB.Tsen := by
  first | exact @GlobalTheory.NeedB.tsen | exact GlobalTheory.NeedB.tsen | (intros; apply GlobalTheory.NeedB.tsen <;> assumption)
end

