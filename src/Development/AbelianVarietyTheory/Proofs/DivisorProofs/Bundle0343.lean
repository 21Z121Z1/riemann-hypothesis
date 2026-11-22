import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0316
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFlipSheafComplexPairing
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

noncomputable section
namespace GlobalTheory.EtC.SwapTransfer

variable {R : Type} [CommRing R]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.SwapTransfer.negOnePow_sq' (n m : ℤ) :
    (n.negOnePow : ℤ) * ((m.negOnePow : ℤ) * (n.negOnePow : ℤ)) = m.negOnePow := by
  rw [mul_left_comm, ← Units.val_mul, Int.units_mul_self, Units.val_one, mul_one]

def flipPair {I J K : Cx R} (μ : Pair I J K) : Pair J I K where
  mul U t s w h := (((s * t).negOnePow : ℤ) • μ.mul U s t w (by omega)).flip
  nat g t s w h b a := by
    simp only [LinearMap.flip_apply, LinearMap.smul_apply, Sec.res, map_zsmul]
    rw [← Sec.res, μ.nat]
  leibniz U t s w h b a := by
    simp only [LinearMap.flip_apply, LinearMap.smul_apply, Sec.map, map_zsmul]
    rw [← Sec.map, μ.leibniz]
    have h1 : (s * (t + 1)).negOnePow = (s * t).negOnePow * s.negOnePow := by
      rw [mul_add, mul_one, Int.negOnePow_add]
    have h2 : ((s + 1) * t).negOnePow = (s * t).negOnePow * t.negOnePow := by
      rw [add_mul, one_mul, Int.negOnePow_add]
    rw [h1, h2]
    simp only [Units.smul_def, smul_add, smul_smul, Units.val_mul]
    rw [negOnePow_sq']
    exact add_comm _ _

def swIdx {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w}) : {p : ℤ × ℤ // p.1 + p.2 = w} :=
  ⟨(p.1.2, p.1.1), by have := p.2; simp only at this ⊢; omega⟩

def swapT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens J I U w := by
  classical
  exact DirectSum.toModule _ _ _ fun p =>
    ((p.1.1 * p.1.2).negOnePow : ℤ) • ((DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (J.X q.1.1) U ⊗[ULift.{1} R] Sec (I.X q.1.2) U) (swIdx p)) ∘ₗ
      (TensorProduct.comm (ULift.{1} R) (Sec (I.X p.1.1) U) (Sec (J.X p.1.2) U)).toLinearMap)

end GlobalTheory.EtC.SwapTransfer

namespace GlobalTheory.EtC

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem flipPair_mul_eq_negOnePow_smul_mul {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    (_root_.GlobalTheory.EtC.SwapTransfer.flipPair μ).mul U t s w (by omega) b a = (s * t).negOnePow • μ.mul U s t w h a b := by
  rw [Units.smul_def]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem koszulSwap_lof_tmul_lemma_5 (I J : _root_.GlobalTheory.EtC.Cx R) (U : Scheme.{0}) {w s t : ℤ} (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    _root_.GlobalTheory.EtC.SwapTransfer.swapT I J U w
        (DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
          ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      (s * t).negOnePow • DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (J.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (I.X q.1.2) U)
          ⟨(t, s), by omega⟩ (b ⊗ₜ a) := by
  unfold _root_.GlobalTheory.EtC.SwapTransfer.swapT
  erw [DirectSum.toModule_lof]
  rw [Units.smul_def]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem lift_lof_tmul {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) (U : Scheme.{0}) {w s t : ℤ} (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    μ.lift U w
        (DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
          ⟨(s, t), h⟩ (a ⊗ₜ b)) = μ.mul U s t w h a b := by
  unfold _root_.GlobalTheory.EtC.Pair.lift
  erw [DirectSum.toModule_lof]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem lift_comp_swapT_eq_flipPair_lift {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) (U : Scheme.{0}) (w : ℤ) :
    μ.lift U w ∘ₗ _root_.GlobalTheory.EtC.SwapTransfer.swapT J I U w =
      (_root_.GlobalTheory.EtC.SwapTransfer.flipPair μ).lift U w := by
  unfold _root_.GlobalTheory.EtC.Tens
  apply DirectSum.linearMap_ext
  rintro ⟨⟨t, s⟩, h⟩
  apply TensorProduct.ext'
  intro b a
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, koszulSwap_lof_tmul_lemma_5, map_zsmul_unit, lift_lof_tmul, lift_lof_tmul, Units.smul_def, mul_comm t s]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem swapT_comp_swapT (I J : _root_.GlobalTheory.EtC.Cx R) (U : Scheme.{0}) (w : ℤ) :
    _root_.GlobalTheory.EtC.SwapTransfer.swapT J I U w ∘ₗ _root_.GlobalTheory.EtC.SwapTransfer.swapT I J U w = LinearMap.id := by
  unfold _root_.GlobalTheory.EtC.Tens
  apply DirectSum.linearMap_ext
  rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'
  intro a b
  rw [LinearMap.comp_apply, LinearMap.comp_apply, koszulSwap_lof_tmul_lemma_5, map_zsmul_unit, koszulSwap_lof_tmul_lemma_5, smul_smul, mul_comm t s, Int.units_mul_self, one_smul]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem tensorRestrict_lof_tmul_lemma_7 (I J : _root_.GlobalTheory.EtC.Cx R) {V U : Scheme.{0}} (g : V ⟶ U) {w s t : ℤ} (h : s + t = w)
    (a : _root_.GlobalTheory.EtC.Sec (I.X s) U) (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    _root_.GlobalTheory.EtC.Tens.res g w
        (DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
          ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
          _root_.GlobalTheory.EtC.Sec (I.X q.1.1) V ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) V)
          ⟨(s, t), h⟩ (_root_.GlobalTheory.EtC.Sec.res g a ⊗ₜ _root_.GlobalTheory.EtC.Sec.res g b) := by
  unfold _root_.GlobalTheory.EtC.Tens.res
  erw [DirectSum.lmap_lof]
  rfl

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem res_comp_swapT (I J : _root_.GlobalTheory.EtC.Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    _root_.GlobalTheory.EtC.Tens.res g w ∘ₗ _root_.GlobalTheory.EtC.SwapTransfer.swapT I J U w =
      _root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w ∘ₗ _root_.GlobalTheory.EtC.Tens.res g w := by
  unfold _root_.GlobalTheory.EtC.Tens
  apply DirectSum.linearMap_ext
  rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'
  intro a b
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, koszulSwap_lof_tmul_lemma_5, map_zsmul_unit, tensorRestrict_lof_tmul_lemma_7, tensorRestrict_lof_tmul_lemma_7, koszulSwap_lof_tmul_lemma_5]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in

theorem _root_.GlobalTheory.EtC.Pair.exists_isFlip (R : Type) [CommRing R]
    {I J K : _root_.GlobalTheory.EtC.Cx R} (μ : _root_.GlobalTheory.EtC.Pair I J K) :
    ∃ ν : _root_.GlobalTheory.EtC.Pair J I K, μ.IsFlip ν ∧ ν.IsFlip μ ∧
      (μ.IsTensor → ν.IsTensor) := by
  refine ⟨_root_.GlobalTheory.EtC.SwapTransfer.flipPair μ, ?_, ?_, ?_⟩
  · intro U s t w h a b
    exact flipPair_mul_eq_negOnePow_smul_mul μ U s t w h a b
  · intro U t s w h b a
    rw [flipPair_mul_eq_negOnePow_smul_mul μ U s t w (by omega) a b, smul_smul, mul_comm t s, Int.units_mul_self, one_smul]
  · rintro ⟨hsurj, hinj⟩
    refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
    · obtain ⟨S, hS, hP⟩ := hsurj U w y
      refine ⟨S, hS, fun V g hg => ?_⟩
      obtain ⟨x, hx⟩ := hP V g hg
      refine ⟨_root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w x, ?_⟩
      rw [← lift_comp_swapT_eq_flipPair_lift, LinearMap.comp_apply, ← LinearMap.comp_apply (_root_.GlobalTheory.EtC.SwapTransfer.swapT J I V w), swapT_comp_swapT, LinearMap.id_apply]
      exact hx
    · have hx' : μ.lift U w (_root_.GlobalTheory.EtC.SwapTransfer.swapT J I U w x) = 0 := by
        rw [← LinearMap.comp_apply, lift_comp_swapT_eq_flipPair_lift]
        exact hx
      obtain ⟨S, hS, hP⟩ := hinj U w _ hx'
      refine ⟨S, hS, fun V g hg => ?_⟩
      have hV := congrArg (_root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w) (hP V g hg)
      rw [← LinearMap.comp_apply (_root_.GlobalTheory.EtC.Tens.res g w), res_comp_swapT, LinearMap.comp_apply,
        ← LinearMap.comp_apply (_root_.GlobalTheory.EtC.SwapTransfer.swapT I J V w), swapT_comp_swapT, LinearMap.id_apply, map_zero] at hV
      exact hV

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsManyBoundedByPow
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.PolesOfT

open Polynomial

variable {k F : Type} [Field k] [Field F] [Algebra k F]

abbrev Mx (t : F) (v : Place k F) : WithZero (Multiplicative ℤ) := max 1 (v.1 t)

theorem one_le_Mx (t : F) (v : Place k F) : 1 ≤ Mx t v := le_max_left _ _

theorem val_aeval_le (t : F) (p : k[X]) (v : Place k F) :
    v.1 (aeval t p) ≤ Mx t v ^ p.natDegree := by
  rw [aeval_eq_sum_range]
  refine v.1.map_sum_le fun i hi => ?_
  rw [Algebra.smul_def, map_mul, map_pow]
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hc : v.1 (algebraMap k F (p.coeff i)) ≤ 1 := by
    by_cases h : p.coeff i = 0
    · simp [h]
    · exact (v.2.2 _ h).le
  calc v.1 (algebraMap k F (p.coeff i)) * v.1 t ^ i ≤ 1 * Mx t v ^ i :=
        mul_le_mul' hc (pow_le_pow_left₀ zero_le' (le_max_right _ _) i)
    _ = Mx t v ^ i := one_mul _
    _ ≤ Mx t v ^ p.natDegree := pow_le_pow_right₀ (one_le_Mx t v) hi'

theorem val_le_of_monic (t y : F) (P : F[X]) (hP : P.Monic) (hy : P.eval y = 0) (c : ℕ)
    (v : Place k F) (hc : ∀ i < P.natDegree, v.1 (P.coeff i) ≤ Mx t v ^ c) :
    v.1 y ≤ Mx t v ^ c := by
  by_contra hlt
  push_neg at hlt
  have hM : 1 ≤ Mx t v ^ c := one_le_pow₀ (one_le_Mx t v)
  have hy1 : 1 < v.1 y := lt_of_le_of_lt hM hlt
  have hy0 : v.1 y ≠ 0 := ne_of_gt (lt_trans zero_lt_one hy1)
  rw [hP.as_sum, eval_add, eval_pow, eval_X, eval_finset_sum] at hy
  have heq := eq_neg_of_add_eq_zero_left hy
  have hlt2 : v.1 (∑ i ∈ Finset.range P.natDegree, (C (P.coeff i) * X ^ i).eval y) <
      v.1 y ^ P.natDegree := by
    refine v.1.map_sum_lt (pow_ne_zero _ hy0) fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [eval_mul, eval_C, eval_pow, eval_X, map_mul, map_pow]
    calc v.1 (P.coeff i) * v.1 y ^ i ≤ Mx t v ^ c * v.1 y ^ i := mul_le_mul' (hc i hi') le_rfl
      _ < v.1 y * v.1 y ^ i := mul_lt_mul_of_pos_right hlt (pow_pos (lt_trans zero_lt_one hy1) _)
      _ = v.1 y ^ (i + 1) := (pow_succ' _ _).symm
      _ ≤ v.1 y ^ P.natDegree := pow_le_pow_right₀ hy1.le hi'
  have h3 : v.1 (y ^ P.natDegree) = v.1 (∑ i ∈ Finset.range P.natDegree, (C (P.coeff i) * X ^ i).eval y) := by
    rw [heq, Valuation.map_neg]
  rw [map_pow] at h3
  rw [← h3] at hlt2
  exact lt_irrefl _ hlt2

end GlobalTheory.Nef.PolesOfT

namespace GlobalTheory.Nef.PolesOfT

open Polynomial

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem exists_mul_bdd (t y : F) (hy : IsAlgebraic k⟮t⟯ y) :
    ∃ q : k[X], aeval t q ≠ 0 ∧ ∃ c : ℕ, ∀ v : Place k F, v.1 (aeval t q * y) ≤ Mx t v ^ c := by
  classical
  obtain ⟨p, hp0, hpy⟩ := hy
  set A : Subalgebra k F := (aeval t : k[X] →ₐ[k] F).range with hA
  set P : F[X] := p.map (algebraMap k⟮t⟯ F) with hPdef
  have hP0 : P ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap k⟮t⟯ F).injective).mpr hp0
  have hPy : P.eval y = 0 := by rw [hPdef, eval_map, ← aeval_def]; exact hpy
  have hcoef : ∀ i, ∃ s : k[X], aeval t s ≠ 0 ∧ aeval t s * P.coeff i ∈ A := by
    intro i
    rw [hPdef, coeff_map]
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff k (p.coeff i : F)).mp (p.coeff i).2
    by_cases hs : aeval t s = 0
    · refine ⟨1, by simp, ?_⟩
      have : algebraMap k⟮t⟯ F (p.coeff i) = 0 := by
        change (p.coeff i : F) = 0
        rw [hrs, hs, div_zero]
      rw [this, mul_zero]; exact A.zero_mem
    · refine ⟨s, hs, ?_⟩
      change aeval t s * (p.coeff i : F) ∈ A
      rw [hrs, mul_div_cancel₀ _ hs]
      exact ⟨r, rfl⟩
  choose s hs0 hsA using hcoef
  set D : F := ∏ i ∈ Finset.range (P.natDegree + 1), aeval t (s i) with hD
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hs0 i
  set Q : F[X] := C D * P with hQdef
  have hQA : ∀ i, Q.coeff i ∈ A := by
    intro i
    rw [hQdef, coeff_C_mul]
    by_cases hi : i ∈ Finset.range (P.natDegree + 1)
    · rw [hD, ← Finset.prod_erase_mul _ _ hi, mul_assoc]
      refine A.mul_mem (A.prod_mem fun j _ => ⟨s j, rfl⟩) (hsA i)
    · have : P.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (by
        simp only [Finset.mem_range, not_lt] at hi; omega)
      rw [this, mul_zero]; exact A.zero_mem
  have hQ0 : Q ≠ 0 := mul_ne_zero (C_ne_zero.mpr hD0) hP0
  have hQy : Q.eval y = 0 := by rw [hQdef, eval_mul, hPy, mul_zero]
  set R : F[X] := integralNormalization Q with hRdef
  have hRmon : R.Monic := monic_integralNormalization hQ0
  have hRy : R.eval (Q.leadingCoeff * y) = 0 :=
    integralNormalization_eval₂_eq_zero (RingHom.id F) hQy (fun x hx => hx)
  have hRA : ∀ i, R.coeff i ∈ A := by
    intro i
    rw [hRdef, integralNormalization_coeff]
    split_ifs
    · exact A.one_mem
    · exact A.mul_mem (hQA i) (A.pow_mem (hQA _) _)
  choose pr hpr using hRA
  obtain ⟨q, hq⟩ := hQA Q.natDegree
  have hq' : aeval t q = Q.leadingCoeff := hq
  refine ⟨q, by rw [hq']; exact leadingCoeff_ne_zero.mpr hQ0,
    (Finset.range R.natDegree).sup fun i => (pr i).natDegree, fun v => ?_⟩
  rw [hq']
  refine val_le_of_monic t _ R hRmon hRy _ v fun i hi => ?_
  have h1 : R.coeff i = aeval t (pr i) := (hpr i).symm
  rw [h1]
  exact (val_aeval_le t (pr i) v).trans
    (pow_le_pow_right₀ (one_le_Mx t v) (Finset.le_sup (f := fun i => (pr i).natDegree) (Finset.mem_range.mpr hi)))

end GlobalTheory.Nef.PolesOfT

namespace GlobalTheory.Nef

open Polynomial PolesOfT

theorem exists_many_bounded_by_pow : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ t : F, Transcendental k t → ∃ c : ℕ, ∀ N : ℕ, ∃ (n : ℕ) (f : Fin n → F), LinearIndependent k f ∧ ((N : ℤ) - c) * Module.finrank k⟮t⟯ F ≤ n ∧ ∀ (i : Fin n) (v : Place k F), v.1 (f i) ≤ max 1 (v.1 t) ^ N := by
  intro k F _ _ _ _ _ _ t ht
  by_cases hfin : FiniteDimensional k⟮t⟯ F
  swap
  · refine ⟨0, fun N => ⟨0, Fin.elim0, linearIndependent_empty_type, ?_, fun i => i.elim0⟩⟩
    rw [Module.finrank_of_infinite_dimensional hfin]; simp
  set d := Module.finrank k⟮t⟯ F with hd
  let b := Module.finBasis k⟮t⟯ F
  have halg : ∀ j, IsAlgebraic k⟮t⟯ (b j) := fun j => Algebra.IsAlgebraic.isAlgebraic _
  choose q hq0 cj hcj using fun j => exists_mul_bdd t (b j) (halg j)
  refine ⟨Finset.univ.sup cj, fun N => ?_⟩
  set c := Finset.univ.sup cj with hc
  set L := N - c with hL
  let w : Fin d → k⟮t⟯ := fun j => aeval (IntermediateField.AdjoinSimple.gen k t) (q j)
  have hw : ∀ j, algebraMap k⟮t⟯ F (w j) = aeval t (q j) := fun j => by
    simp only [w]; rw [← aeval_algebraMap_apply, IntermediateField.AdjoinSimple.algebraMap_gen]
  have hw0 : ∀ j, w j ≠ 0 := fun j h => hq0 j (by rw [← hw j, h, map_zero])
  let y : Fin d → F := fun j => aeval t (q j) * b j
  have hyli : LinearIndependent k⟮t⟯ y := by
    have := b.linearIndependent.units_smul (fun j => Units.mk0 (w j) (hw0 j))
    convert this using 1
    funext j
    simp [y, Algebra.smul_def, hw]
  have hpowF : LinearIndependent k (fun n : ℕ => t ^ n) := by
    have h1 := (Polynomial.basisMonomials k).linearIndependent.map' (aeval t).toLinearMap
      (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp ht))
    have heq : (fun n : ℕ => t ^ n) = (aeval t).toLinearMap ∘ Polynomial.basisMonomials k := by
      funext n
      simp [Polynomial.coe_basisMonomials]
    rw [heq]
    exact h1
  have hpow : LinearIndependent k (fun i : Fin L => (IntermediateField.AdjoinSimple.gen k t) ^ (i : ℕ)) := by
    have heq : (IsScalarTower.toAlgHom k k⟮t⟯ F).toLinearMap ∘
        (fun i : Fin L => (IntermediateField.AdjoinSimple.gen k t) ^ (i : ℕ)) =
        (fun n : ℕ => t ^ n) ∘ (fun i : Fin L => (i : ℕ)) := by
      funext i
      simp
    apply LinearIndependent.of_comp (IsScalarTower.toAlgHom k k⟮t⟯ F).toLinearMap
    rw [heq]
    exact hpowF.comp _ Fin.val_injective
  have hprod := linearIndependent_smul hpow hyli
  refine ⟨L * d, fun i => (fun p : Fin L × Fin d => (IntermediateField.AdjoinSimple.gen k t) ^ (p.1 : ℕ) • y p.2)
    (finProdFinEquiv.symm i), hprod.comp _ finProdFinEquiv.symm.injective, ?_, ?_⟩
  · push_cast
    have h1 : ((N : ℤ) - c) ≤ (L : ℤ) := by omega
    exact mul_le_mul_of_nonneg_right h1 (Int.natCast_nonneg _)
  · intro i v
    dsimp only
    generalize finProdFinEquiv.symm i = p
    obtain ⟨a, j⟩ := p
    have hsm : (IntermediateField.AdjoinSimple.gen k t) ^ (a : ℕ) • y j = t ^ (a : ℕ) * (aeval t (q j) * b j) := by
      rw [Algebra.smul_def, map_pow, IntermediateField.AdjoinSimple.algebraMap_gen]
    dsimp only
    rw [hsm, map_mul, map_pow]
    have ha : (a : ℕ) + c ≤ N := by have := a.2; omega
    calc v.1 t ^ (a : ℕ) * v.1 (aeval t (q j) * b j) ≤ Mx t v ^ (a : ℕ) * Mx t v ^ c :=
          mul_le_mul' (pow_le_pow_left₀ zero_le' (le_max_right _ _) _)
            ((hcj j v).trans (pow_le_pow_right₀ (one_le_Mx t v) (Finset.le_sup (Finset.mem_univ j))))
      _ = Mx t v ^ ((a : ℕ) + c) := (pow_add _ _ _).symm
      _ ≤ max 1 (v.1 t) ^ N := pow_le_pow_right₀ (one_le_Mx t v) ha

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqZeroOfSmulEqZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.ZModFlat

open scoped TensorProduct

theorem exists_mul_eq_zero_of_smul_eq_zero (q : ℕ) [NeZero q] (M : Type 1) [AddCommGroup M]
    [Module (ULift.{1} (ZMod q)) M]
    (hdiv : ∀ d e : ℕ, d * e = q → ∀ x : M, d • x = 0 → ∃ y : M, x = e • y)
    (a : ULift.{1} (ZMod q)) (y : M) (hy : a • y = 0) :
    ∃ e : ℕ, (e : ULift.{1} (ZMod q)) * a = 0 ∧ ∃ z : M, y = e • z := by
  set n := a.down.val with hn
  have ha : a = (n : ULift.{1} (ZMod q)) := by
    apply ULift.down_injective
    rw [ULift.down_natCast, hn, ZMod.natCast_zmod_val]
  have hq : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    ext; simp
  have hgq : Nat.gcd n q ∣ q := Nat.gcd_dvd_right n q
  have hgn : Nat.gcd n q ∣ n := Nat.gcd_dvd_left n q
  refine ⟨q / Nat.gcd n q, ?_, ?_⟩
  · rw [ha, ← Nat.cast_mul]
    have : q ∣ q / Nat.gcd n q * n := by
      have h := Nat.mul_dvd_mul (dvd_refl (q / Nat.gcd n q)) hgn
      rwa [Nat.div_mul_cancel hgq] at h
    obtain ⟨m, hm⟩ := this
    rw [hm, Nat.cast_mul, hq, zero_mul]
  · apply hdiv (Nat.gcd n q) (q / Nat.gcd n q) (Nat.mul_div_cancel' hgq)
    have h1 : n • y = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), ← ha, hy]
    have h2 : q • y = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), hq, zero_smul]
    have hb : ((Nat.gcd n q : ℕ) : ℤ) = n * Nat.gcdA n q + q * Nat.gcdB n q :=
      Nat.gcd_eq_gcd_ab n q
    have h3 : ((n : ℤ) * Nat.gcdA n q) • y = 0 := by
      rw [mul_comm, mul_smul, natCast_zsmul, h1, smul_zero]
    have h4 : ((q : ℤ) * Nat.gcdB n q) • y = 0 := by
      rw [mul_comm, mul_smul, natCast_zsmul, h2, smul_zero]
    rw [← natCast_zsmul, hb, add_smul, h3, h4, add_zero]

theorem flat_of_divisibility : ∀ (q : ℕ) [NeZero q] (M : Type 1) [AddCommGroup M]
    [Module (ULift.{1} (ZMod q)) M],
    (∀ d e : ℕ, d * e = q → ∀ x : M, d • x = 0 → ∃ y : M, x = e • y) →
      Module.Flat (ULift.{1} (ZMod q)) M := by
  intro q _ M _ _ hdiv
  haveI : IsPrincipalIdealRing (ULift.{1} (ZMod q)) :=
    IsPrincipalIdealRing.of_surjective
      ((ULift.ringEquiv (R := ZMod q)).symm.toRingHom.comp (Int.castRingHom (ZMod q)))
      (by
        intro x
        obtain ⟨z, hz⟩ := ZMod.intCast_surjective x.down
        exact ⟨z, by apply ULift.down_injective; simpa using hz⟩)
  rw [Module.Flat.iff_rTensor_injective']
  intro J
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal J).principal
  let b : J := ⟨a, by rw [ha]; exact Submodule.mem_span_singleton_self a⟩
  have hall : ∀ t : J ⊗[ULift.{1} (ZMod q)] M, ∃ y : M, t = b ⊗ₜ y := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul r x =>
      have hr : (r : ULift.{1} (ZMod q)) ∈ Submodule.span (ULift.{1} (ZMod q)) {a} := ha ▸ r.2
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hr
      refine ⟨c • x, ?_⟩
      rw [← TensorProduct.smul_tmul]
      congr 1
      ext
      simp [b, ← hc]
    | add s t hs ht =>
      obtain ⟨y1, rfl⟩ := hs
      obtain ⟨y2, rfl⟩ := ht
      exact ⟨y1 + y2, (TensorProduct.tmul_add _ _ _).symm⟩
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨y, rfl⟩ := hall t
  have hy : a • y = 0 := by
    have := congrArg (TensorProduct.lid (ULift.{1} (ZMod q)) M) ht
    simpa [b] using this
  obtain ⟨e, he, z, rfl⟩ := exists_mul_eq_zero_of_smul_eq_zero q M hdiv a y hy
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q)), ← TensorProduct.smul_tmul]
  have : ((e : ULift.{1} (ZMod q))) • b = 0 := by
    ext
    simp [b, he]
  rw [this, TensorProduct.zero_tmul]

end GlobalTheory.ZModFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormMulOfHermitianModelUnitaryConjStatement
section
open GlobalTheory.UnitLemma Polynomial Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_mul_of_hermitianModel_unitary_conj : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ γ' u : Matrix (Fin n) (Fin n) K.E) (x x' : B.Aˣ) (ψ ψ' : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ → GlobalTheory.InertUnitOrb.IsModel B γ' x' ψ' → (u.map K.c)ᵀ * u = 1 → γ * u = u * γ' → B.P.Separable → ∃ v : B.Aˣ, (x' : B.A) = x * (v * B.σ v) := by
  first | exact @GlobalTheory.InertUnitOrb.class_eq_of_conj | exact GlobalTheory.InertUnitOrb.class_eq_of_conj | (intros; apply GlobalTheory.InertUnitOrb.class_eq_of_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupPeriodicStatement
section
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openSubgroup_periodic : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] {ι : Type} (L : ι → AddSubgroup X), (∀ i, IsOpen (L i : Set X)) → (∀ W ∈ 𝓝 (0 : X), ∃ i, (L i : Set X) ⊆ W) → ∀ f ∈ GlobalTheory.WeilM.SB X, ∃ i, ∀ Y, ∀ C ∈ L i, f (Y + C) = f Y := by
  first | exact @GlobalTheory.WeilM.SB.exists_periodic | exact GlobalTheory.WeilM.SB.exists_periodic | (intros; apply GlobalTheory.WeilM.SB.exists_periodic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitianStatement
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oscillatorAction_unitaryGroup_hermitian : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∀ (G : Type) [Group G] (m : G →* Matrix ι ι ℂ), (∀ g, (m g)ᴴ * H * m g = H) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => m g *ᵥ v) Ω ∧ (∀ g, m g = 1 → ∀ f, Sm ρ f → Ω g f = f) ∧ (∀ [TopologicalSpace G], Continuous m → ∀ f, Sm ρ f → Continuous fun g => Ω g f) ∧ ∀ (s : Matrix ι ι ℂ) (g : G), s * s = 1 → (H * s).PosDef → s * m g = m g * s → ∀ f, Sm ρ f → (∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (I • s *ᵥ z) = 0) → Ω g f = dP s (m g) • f := by
  first | exact @GlobalTheory.RealWeil.UnitaryOsc.exists_osc | exact GlobalTheory.RealWeil.UnitaryOsc.exists_osc | (intros; apply GlobalTheory.RealWeil.UnitaryOsc.exists_osc <;> assumption)
end

