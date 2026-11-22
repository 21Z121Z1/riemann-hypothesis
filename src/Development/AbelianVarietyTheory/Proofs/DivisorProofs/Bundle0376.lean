import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Formalism.SatakeDualWeyl.Bundle0001
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLift
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0344
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealWeight
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Formalism.UG
open scoped NNReal

noncomputable section
namespace GlobalTheory.BorelUMod

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

abbrev upPairs (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2

theorem relIndex_unipLat {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {c C : Fin n → Fin n → ℤ}
    (hc : IsWeight c) (hC : IsWeight C) (hI : IsIdealWeight c C) :
    (unipLat h.2.1 hC).relIndex (unipLat h.2.1 hc) = q ^ ∑ p ∈ upPairs n, (C p.1 p.2 - c p.1 p.2).toNat := by
  rw [Cayley.relIndex_unipLat L ϖ σ q n h c C hc hC hI]
  have h1 := relIndex_upLat_eq_sq L ϖ σ q n h c C hc.1 hC.1 hI.1
  rw [UpLatIndex.relIndex_upLat L ϖ σ q n h c C hI.1, Finset.prod_pow_eq_pow_sum, ← pow_mul, mul_comm, pow_mul] at h1
  exact (Nat.pow_left_injective two_ne_zero h1).symm

theorem v_eq_exp {x : L} (hx : x ≠ 0) : Valued.v x = WithZero.exp (-ordL x) := by
  rw [ordL_eq, neg_neg, WithZero.exp_log (by simpa using hx)]

theorem ord_rev {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (t : torusU σ n) (i : Fin n) :
    ordL (t.1 i.rev : L) = -ordL (t.1 i : L) := by
  have h := (mem_GU_iff σ n _).1 t.2 i i
  rw [← map_inv, diagHom_val, diagHom_val, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h
  have := congrArg Valued.v h
  rw [hσ] at this
  simp [ordL_eq, ← this]

theorem isWeight_ord {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (t : torusU σ n) :
    IsWeight fun i j : Fin n => ordL (t.1 i : L) - ordL (t.1 j : L) :=
  ⟨fun i j => by simp only [ord_rev hσ]; ring, fun i j k _ _ => by simp⟩

theorem conj_entry (t : Fin n → Lˣ) (u : GL (Fin n) L) (i j : Fin n) :
    ((diagHom L (Fin n) t * u * (diagHom L (Fin n) t)⁻¹).val - 1) i j = t i * (u.val - 1) i j * (t j : L)⁻¹ := by
  rw [← map_inv, Units.val_mul, Units.val_mul, diagHom_val, diagHom_val]
  by_cases h : i = j
  · subst h
    simp [mul_sub, sub_mul]
  · simp [Matrix.one_apply, h]

theorem conj_mem_iff {σ : L →+* L} [LocallyCompactSpace (GU σ n)] (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (t : torusU σ n) (u : (borelU σ n).U) :
    conjAut (borelU σ n).U ⟨(borelU σ n).s t, (borelU σ n).Q_le_normalizer ((borelU σ n).s_mem _)⟩ u ∈
      unipLat hσ (isWeight_ord hσ t) ↔ u ∈ unipLat hσ isWeight_zero := by
  rw [mem_unipLat, mem_unipLat, mem_upLat, mem_upLat]
  have e : ∀ i j, ((conjAut (borelU σ n).U
      ⟨(borelU σ n).s t, (borelU σ n).Q_le_normalizer ((borelU σ n).s_mem _)⟩ u).1.1.val - 1) i j =
      t.1 i * (u.1.1.val - 1) i j * (t.1 j : L)⁻¹ := conj_entry t.1 u.1.1
  simp only [e]
  refine and_congr (forall₃_congr fun i j _ => by simp) (forall₃_congr fun i j _ => ?_)
  rw [map_mul, map_mul, map_inv₀, v_eq_exp (t.1 i).ne_zero, v_eq_exp (t.1 j).ne_zero, mul_right_comm,
    ← WithZero.exp_neg, ← WithZero.exp_add, neg_zero, WithZero.exp_zero, neg_sub', sub_eq_add_neg]
  exact mul_le_iff_le_one_right WithZero.exp_pos

theorem exists_idealWeight {c : Fin n → Fin n → ℤ} :
    ∃ C : Fin n → Fin n → ℤ, IsWeight C ∧ IsIdealWeight c C ∧ IsIdealWeight (fun _ _ => 0) C := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ i j, |c i j| ≤ M := by
    obtain ⟨M, hM⟩ := (Set.finite_range fun p : Fin n × Fin n => (c p.1 p.2).natAbs).bddAbove
    exact ⟨M, fun i j => by
      have : (c i j).natAbs ≤ M := hM ⟨(i, j), rfl⟩
      rw [← Int.natCast_natAbs]; exact_mod_cast this⟩
  have key : ∀ d : Fin n → Fin n → ℤ, (∀ i j, |d i j| ≤ M) →
      IsIdealWeight d fun i j => (M : ℤ) * (n + i.val - j.val) := by
    intro d hd
    have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
    refine ⟨fun i j _ => ?_, fun i j k h1 _ => ?_, fun i j k _ h2 => ?_⟩
    · have h1 : (1 : ℤ) ≤ n + i.val - j.val := by have := j.2; omega
      nlinarith [abs_le.1 (hd i j)]
    · have h1 : (1 : ℤ) ≤ j.val - i.val := by have := Fin.lt_def.1 h1; omega
      nlinarith [abs_le.1 (hd i j)]
    · have h1 : (1 : ℤ) ≤ k.val - j.val := by have := Fin.lt_def.1 h2; omega
      nlinarith [abs_le.1 (hd j k)]
  refine ⟨_, ⟨fun i j => ?_, fun i j k _ _ => ?_⟩, key c hM, key _ fun _ _ => by simp⟩
  · have := i.2
    have := j.2
    simp only [Fin.val_rev]
    congr 1
    omega
  · have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
    have h1 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    nlinarith

theorem sum_upPairs (a : Fin n → ℤ) :
    ∑ p ∈ upPairs n, (a p.1 - a p.2) = ∑ i, a i * ((n : ℤ) - 1 - 2 * i.val) := by
  have h1 : ∑ p ∈ upPairs n, a p.1 = ∑ i, a i * ((n : ℤ) - 1 - i.val) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_lt_eq_Ioi, Fin.card_Ioi, nsmul_eq_mul, mul_comm]
    congr 1
    have := i.2
    omega
  have h2 : ∑ p ∈ upPairs n, a p.2 = ∑ i, a i * (i.val : ℤ) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_gt_eq_Iio, Fin.card_Iio, nsmul_eq_mul, mul_comm]
  rw [Finset.sum_sub_distrib, h1, h2, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sum_half (a : Fin n → ℤ) (ha : ∀ i, a i.rev = -a i) :
    ∑ i, a i * ((n : ℤ) - 1 - 2 * i.val) =
      2 * ∑ i : Fin (n / 2), a (Fin.castLE (Nat.div_le_self n 2) i) * ((n : ℤ) - 1 - 2 * i.val) := by
  have h1 : ∑ i : Fin (n / 2), a (Fin.castLE (Nat.div_le_self n 2) i) * ((n : ℤ) - 1 - 2 * i.val) =
      ∑ i : Fin n, if i.val < n / 2 then a i * ((n : ℤ) - 1 - 2 * i.val) else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun i _ => Fin.castLE (Nat.div_le_self n 2) i) (fun i _ => by simp)
      (fun i _ j _ e => Fin.castLE_injective _ e) (fun j hj => ⟨⟨j.val, by simpa using hj⟩, by simp, rfl⟩)
      fun i _ => rfl
  rw [two_mul]
  nth_rewrite 2 [h1]
  rw [← Equiv.sum_comp Fin.revPerm (fun i : Fin n => if i.val < n / 2 then a i * ((n : ℤ) - 1 - 2 * i.val) else 0),
    h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.2
  have hr : ((i.rev.val : ℕ) : ℤ) = n - 1 - i.val := by rw [Fin.val_rev]; omega
  simp only [Fin.revPerm_apply, ha, hr]
  split_ifs with h1 h2 h2
  · omega
  · ring
  · ring
  · have : (n : ℤ) - 1 - 2 * i.val = 0 := by omega
    simp [this]

theorem zpow_finset_sum {ι : Type} {z : ℂ} (hz : z ≠ 0) (s : Finset ι) (a : ι → ℤ) :
    z ^ ∑ i ∈ s, a i = ∏ i ∈ s, z ^ a i := by
  first
  | exact @_root_.GlobalTheory.AbelianSumIdentityFirst.main
  | exact _root_.GlobalTheory.AbelianSumIdentityFirst.main
  | (apply _root_.GlobalTheory.AbelianSumIdentityFirst.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AbelianSumIdentityFirst.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AbelianSumIdentityFirst.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AbelianSumIdentityFirst.main ..)

end GlobalTheory.BorelUMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTensorEtaleSheafComplexPairing
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.res_lof {I J : _root_.GlobalTheory.EtC.Cx R} {V U : Scheme.{0}}
    (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : _root_.GlobalTheory.EtC.Sec (I.X p.1.1) U) (b : _root_.GlobalTheory.EtC.Sec (J.X p.1.2) U) :
    _root_.GlobalTheory.EtC.Tens.res g w
      (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      _root_.GlobalTheory.EtC.Sec (I.X p.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X p.1.2) U)
        p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      _root_.GlobalTheory.EtC.Sec (I.X p.1.1) V ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X p.1.2) V) p
        (_root_.GlobalTheory.EtC.Sec.res g a ⊗ₜ _root_.GlobalTheory.EtC.Sec.res g b) := by
  unfold _root_.GlobalTheory.EtC.Tens.res
  rw [DirectSum.lmap_lof, TensorProduct.map_tmul]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.sres_id {F : _root_.GlobalTheory.EtC.Shv R} {U : Scheme.{0}}
    (a : _root_.GlobalTheory.EtC.Sec F U) : _root_.GlobalTheory.EtC.Sec.res (𝟙 U) a = a := by
  unfold _root_.GlobalTheory.EtC.Sec.res
  simp

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.sres_comp {F : _root_.GlobalTheory.EtC.Shv R} {W V U : Scheme.{0}}
    (g : W ⟶ V) (f : V ⟶ U) (a : _root_.GlobalTheory.EtC.Sec F U) :
    _root_.GlobalTheory.EtC.Sec.res (g ≫ f) a =
      _root_.GlobalTheory.EtC.Sec.res g (_root_.GlobalTheory.EtC.Sec.res f a) := by
  unfold _root_.GlobalTheory.EtC.Sec.res
  simp

def pre (I J : Cx R) (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    refine ModuleCat.hom_ext (DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_)
    simp [res_lof, sres_id]
  map_comp f g := by
    refine ModuleCat.hom_ext (DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_)
    simp [res_lof, sres_comp]

end GlobalTheory.EtC.TensEx

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.smap_res {F G : _root_.GlobalTheory.EtC.Shv R} (φ : F ⟶ G)
    {V U : Scheme.{0}} (g : V ⟶ U) (a : _root_.GlobalTheory.EtC.Sec F U) :
    _root_.GlobalTheory.EtC.Sec.res g (_root_.GlobalTheory.EtC.Sec.map φ a) =
      _root_.GlobalTheory.EtC.Sec.map φ (_root_.GlobalTheory.EtC.Sec.res g a) := by
  unfold _root_.GlobalTheory.EtC.Sec.res _root_.GlobalTheory.EtC.Sec.map
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← NatTrans.naturality]

def dT (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ fun p =>
    (DirectSum.lof (ULift.{1} R) _ (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} =>
      Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp; omega⟩ ∘ₗ
      TensorProduct.map ((I.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id) +
    ((p.1.1.negOnePow : ℤ) • (DirectSum.lof (ULift.{1} R) _ (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} =>
      Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp; omega⟩ ∘ₗ
      TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom))

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.dT_lof {I J : _root_.GlobalTheory.EtC.Cx R} (U : Scheme.{0})
    (s t w : ℤ) (h : s + t = w) (a : _root_.GlobalTheory.EtC.Sec (I.X s) U)
    (b : _root_.GlobalTheory.EtC.Sec (J.X t) U) :
    _root_.GlobalTheory.EtC.TensEx.dT I J U w (DirectSum.lof (ULift.{1} R) _
      (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      _root_.GlobalTheory.EtC.Sec (I.X p.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X p.1.2) U)
        ⟨(s, t), h⟩ (a ⊗ₜ b)) =
    DirectSum.lof (ULift.{1} R) _ (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} =>
      _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
        ⟨(s + 1, t), by simp; omega⟩
        (_root_.GlobalTheory.EtC.Sec.map (I.d s (s + 1)) a ⊗ₜ b) +
    (s.negOnePow : ℤ) • DirectSum.lof (ULift.{1} R) _ (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} =>
      _root_.GlobalTheory.EtC.Sec (I.X q.1.1) U ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X q.1.2) U)
        ⟨(s, t + 1), by simp; omega⟩
        (a ⊗ₜ _root_.GlobalTheory.EtC.Sec.map (J.d t (t + 1)) b) := by
  unfold _root_.GlobalTheory.EtC.TensEx.dT
  rw [DirectSum.toModule_lof]
  rfl

end GlobalTheory.EtC.TensEx

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

theorem smap_zero {F G : Shv R} {U : Scheme.{0}} (a : Sec F U) : Sec.map (0 : F ⟶ G) a = 0 := rfl

def D (I J : Cx R) (w : ℤ) : pre I J w ⟶ pre I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality U V g := by
    refine ModuleCat.hom_ext (DirectSum.linearMap_ext _ fun ⟨⟨s, t⟩, h⟩ => TensorProduct.ext' fun a b => ?_)
    simp only [pre, ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    erw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    rw [res_lof, dT_lof, dT_lof, map_add, map_zsmul, res_lof, res_lof, smap_res, smap_res]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
private theorem sec_map_d_map_d_eq_zero (K : _root_.GlobalTheory.EtC.Cx R) {U : Scheme.{0}}
    (i j k : ℤ) (a : _root_.GlobalTheory.EtC.Sec (K.X i) U) :
    _root_.GlobalTheory.EtC.Sec.map (K.d j k) (_root_.GlobalTheory.EtC.Sec.map (K.d i j) a) = 0 := by
  have key := congrArg (fun f : K.X i ⟶ K.X k => (f.hom.app (op U)).hom a) (K.d_comp_d i j k)
  exact key

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.D_comp (I J : _root_.GlobalTheory.EtC.Cx R) (w : ℤ) :
    _root_.GlobalTheory.EtC.TensEx.D I J w ≫
      _root_.GlobalTheory.EtC.TensEx.D I J (w + 1) = 0 := by
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (DirectSum.linearMap_ext _
    fun ⟨⟨s, t⟩, h⟩ => TensorProduct.ext' fun a b => ?_))
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  show _root_.GlobalTheory.EtC.TensEx.dT I J U.unop (w + 1) (_root_.GlobalTheory.EtC.TensEx.dT I J U.unop w
    (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      _root_.GlobalTheory.EtC.Sec (I.X p.1.1) U.unop ⊗[ULift.{1} R] _root_.GlobalTheory.EtC.Sec (J.X p.1.2) U.unop)
      ⟨(s, t), h⟩ (a ⊗ₜ b))) = 0
  rw [_root_.GlobalTheory.EtC.TensEx.dT_lof, map_add, map_zsmul, _root_.GlobalTheory.EtC.TensEx.dT_lof,
    _root_.GlobalTheory.EtC.TensEx.dT_lof, sec_map_d_map_d_eq_zero, sec_map_d_map_d_eq_zero,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, map_zero]
  simp [Int.negOnePow_succ, smul_add]

end GlobalTheory.EtC.TensEx

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

def cx (I J : Cx R) : Cx R :=
  CochainComplex.of (fun w => (presheafToSheaf Scheme.etaleTopology _).obj (pre I J w))
    (fun w => (presheafToSheaf Scheme.etaleTopology _).map (D I J w))
    (fun w => by rw [← Functor.map_comp, D_comp, Functor.map_zero])

def toS (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Sec ((cx I J).X w) U :=
  ((toSheafify Scheme.etaleTopology (pre I J w)).app (op U)).hom

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.toS_res (I J : _root_.GlobalTheory.EtC.Cx R) {V U : Scheme.{0}}
    (g : V ⟶ U) (w : ℤ) (x : _root_.GlobalTheory.EtC.Tens I J U w) :
    _root_.GlobalTheory.EtC.Sec.res g (_root_.GlobalTheory.EtC.TensEx.toS I J U w x) =
      _root_.GlobalTheory.EtC.TensEx.toS I J V w (_root_.GlobalTheory.EtC.Tens.res g w x) := by
  have key := congrArg (fun f => ModuleCat.Hom.hom f x)
    ((toSheafify Scheme.etaleTopology (_root_.GlobalTheory.EtC.TensEx.pre I J w)).naturality g.op)
  exact key.symm

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.TensEx.d_toS (I J : _root_.GlobalTheory.EtC.Cx R)
    (U : Scheme.{0}) (w : ℤ) (x : _root_.GlobalTheory.EtC.Tens I J U w) :
    _root_.GlobalTheory.EtC.Sec.map ((_root_.GlobalTheory.EtC.TensEx.cx I J).d w (w + 1))
        (_root_.GlobalTheory.EtC.TensEx.toS I J U w x) =
      _root_.GlobalTheory.EtC.TensEx.toS I J U (w + 1) (_root_.GlobalTheory.EtC.TensEx.dT I J U w x) := by
  have hd : (_root_.GlobalTheory.EtC.TensEx.cx I J).d w (w + 1) = (presheafToSheaf Scheme.etaleTopology _).map
      (_root_.GlobalTheory.EtC.TensEx.D I J w) := by
    unfold _root_.GlobalTheory.EtC.TensEx.cx
    simp
  have key := congrArg (fun f => ModuleCat.Hom.hom (f.app (op U)) x)
    (toSheafify_naturality Scheme.etaleTopology (_root_.GlobalTheory.EtC.TensEx.D I J w))
  rw [hd]
  exact key.symm

end GlobalTheory.EtC.TensEx

namespace GlobalTheory.EtC.TensEx

variable {R : Type} [CommRing R]

def pair (I J : Cx R) : Pair I J (cx I J) where
  mul U s t w h := (TensorProduct.mk (ULift.{1} R) _ _).compr₂ (toS I J U w ∘ₗ
    DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩)
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [toS_res, res_lof]
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [d_toS, dT_lof, map_add, map_zsmul, Units.smul_def]

end GlobalTheory.EtC.TensEx

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped DirectSum TensorProduct in

theorem _root_.GlobalTheory.EtC.tensor_exists :
    ∀ (R : Type) [CommRing R] (I J : _root_.GlobalTheory.EtC.Cx R),
      ∃ (K : _root_.GlobalTheory.EtC.Cx R) (τ : _root_.GlobalTheory.EtC.Pair I J K), τ.IsTensor := by
  intro R _ I J
  refine ⟨_root_.GlobalTheory.EtC.TensEx.cx I J, _root_.GlobalTheory.EtC.TensEx.pair I J, ?_⟩
  have hlift : ∀ (U : Scheme.{0}) (w : ℤ),
      (_root_.GlobalTheory.EtC.TensEx.pair I J).lift U w =
        _root_.GlobalTheory.EtC.TensEx.toS I J U w := by
    intro U w
    refine DirectSum.linearMap_ext _ fun ⟨⟨s, t⟩, h⟩ => TensorProduct.ext' fun a b => ?_
    unfold _root_.GlobalTheory.EtC.Pair.lift
    rw [LinearMap.comp_apply, LinearMap.comp_apply, DirectSum.toModule_lof, TensorProduct.lift.tmul]
    rfl
  unfold _root_.GlobalTheory.EtC.Pair.IsTensor
  simp only [hlift]
  exact ⟨fun U w y =>
      (_root_.GlobalTheory.EtC.toSheafify_loc_bij_lift R (_root_.GlobalTheory.EtC.TensEx.pre I J w)).1 U y,
    fun U w x hx =>
      (_root_.GlobalTheory.EtC.toSheafify_loc_bij_lift R (_root_.GlobalTheory.EtC.TensEx.pre I J w)).2.1 U x hx⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeMapModOfPerfectAlternating
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open Module

theorem exists_lattice_map_of_symplecticBasis {La : Type} [AddCommGroup La] {g : ℕ}
    (EF : LinearMap.BilinForm ℤ La) (hB : EF.IsAlt) (b : Basis (Fin g ⊕ Fin g) ℤ La)
    (d : Fin g → ℤ) (hb : IsSymplecticBasisOfType EF b d) (M : ℕ) (u t : Fin g → ℤ)
    (ht : ∀ i, u i * d i = 1 + (M : ℤ) * t i) :
    ∃ L : (Fin g ⊕ Fin g → ℤ) →+ La,
      (∀ a, (∃ y, L a = M • y) ↔ ∃ c, a = M • c) ∧ (∀ x, ∃ a y, x = L a + M • y) ∧
      ∀ a c, ∃ k : ℤ, EF (L a) (L c) = omegaStd a c + M * k := by
  classical
  let w : Fin g ⊕ Fin g → ℤ := Sum.elim u 1
  have hw : ∀ j, IsCoprime (w j) (M : ℤ) := by
    rintro (i | i)
    · exact ⟨d i, -t i, by simp only [w, Sum.elim_inl]; linear_combination ht i⟩
    · exact isCoprime_one_left
  let S : (Fin g ⊕ Fin g → ℤ) →ₗ[ℤ] (Fin g ⊕ Fin g → ℤ) :=
    { toFun := fun a j => w j * a j
      map_add' := fun a c => by funext j; simp [mul_add]
      map_smul' := fun r a => by funext j; simp; ring }
  let L : (Fin g ⊕ Fin g → ℤ) →+ La := (b.equivFun.symm.toLinearMap ∘ₗ S).toAddMonoidHom
  have hrepr : ∀ v j, b.repr (b.equivFun.symm v) j = v j := fun v j => by
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hL : ∀ a j, b.repr (L a) j = w j * a j := fun a j => hrepr (S a) j
  refine ⟨L, fun a => ⟨?_, ?_⟩, fun x => ?_, fun a c => ?_⟩
  · rintro ⟨y, hy⟩
    have hdiv : ∀ j, (M : ℤ) ∣ a j := by
      intro j
      have := hL a j
      rw [hy, map_nsmul] at this
      have h2 : (M : ℤ) ∣ w j * a j := ⟨b.repr y j, by rw [← this]; simp⟩
      exact (hw j).symm.dvd_of_dvd_mul_left h2
    choose c hc using hdiv
    exact ⟨c, funext fun j => by simp [hc j]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨L c, map_nsmul L M c⟩
  · refine ⟨Sum.elim (fun i => d i * b.repr x (Sum.inl i)) (fun i => b.repr x (Sum.inr i)),
      b.equivFun.symm (Sum.elim (fun i => -(t i * b.repr x (Sum.inl i))) 0), ?_⟩
    apply b.repr.injective
    ext j
    rw [map_add, Finsupp.add_apply, hL, map_nsmul, Finsupp.smul_apply]
    rcases j with i | i
    · simp only [w, Sum.elim_inl, hrepr, nsmul_eq_mul]
      linear_combination (-(b.repr x (Sum.inl i))) * ht i
    · simp [w, hrepr]
  · refine ⟨∑ i, t i * (a (Sum.inl i) * c (Sum.inr i) - a (Sum.inr i) * c (Sum.inl i)), ?_⟩
    rw [hb.apply_eq_sum hB, omegaStd, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hL, w, Sum.elim_inl, Sum.elim_inr, Pi.one_apply, one_mul]
    linear_combination (a (Sum.inl i) * c (Sum.inr i) - a (Sum.inr i) * c (Sum.inl i)) * ht i

theorem exists_lattice_map_mod_of_perfect : ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La),
  (∀ x, EF x x = 0) → Function.Injective EF → ∀ (e M : ℕ), (∀ f : La →ₗ[ℤ] ℤ, ∃ x, EF x = e • f) → M.Coprime e →
  ∃ L : (Fin (Module.finrank ℤ La / 2) ⊕ Fin (Module.finrank ℤ La / 2) → ℤ) →+ La,
    (∀ a, (∃ y, L a = M • y) ↔ ∃ c, a = M • c) ∧ (∀ x, ∃ a y, x = L a + M • y) ∧
    ∀ a c, ∃ k : ℤ, EF (L a) (L c) = omegaStd a c + M * k := by
  intro La _ _ _ EF halt hinj e M hperf hcop
  have hB : EF.IsAlt := halt
  obtain ⟨g, b, d, hb, -, -⟩ := exists_isSymplecticBasisOfType_pos hB hinj
  have hg : Module.finrank ℤ La / 2 = g := by
    rw [IsSymplecticBasisOfType.finrank_eq b, Fintype.card_fin]; omega
  rw [hg]
  have hde : ∀ i, d i ∣ (e : ℤ) := by
    intro i
    obtain ⟨x, hx⟩ := hperf (b.coord (Sum.inr i))
    have h1 := hb.apply_right x i
    rw [hx] at h1
    simp only [LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
      nsmul_eq_mul, mul_one] at h1
    exact ⟨b.repr x (Sum.inl i), by rw [h1, mul_comm]⟩
  have hc : ∀ i, IsCoprime (M : ℤ) (d i) := fun i =>
    (Nat.isCoprime_iff_coprime.2 hcop).of_isCoprime_of_dvd_right (hde i)
  choose p u hpu using hc
  exact exists_lattice_map_of_symplecticBasis EF hB b d hb M u (fun i => -p i)
    (fun i => by linear_combination hpu i)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroLinearCombinationMemCommonKernelStatement
section
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_linear_combination_mem_common_kernel : ∀ (k F ι : Type) [Field k] [Field F] [Algebra k F] (n m : ℕ) (f : Fin m → F),
  LinearIndependent k f → ∀ (S : Finset ι) (N : ι → ℕ) (ψ : ∀ v, (Fin n → F) →ₗ[k] (Fin (N v) → k)),
    ∑ v ∈ S, N v < n * m → ∃ c : Fin n → Fin m → k, (fun i => ∑ j, c i j • f j) ≠ 0 ∧
      ∀ v ∈ S, ψ v (fun i => ∑ j, c i j • f j) = 0 := by
  first | exact @GlobalTheory.exists_ne_zero_comb_mem_ker | exact GlobalTheory.exists_ne_zero_comb_mem_ker | (intros; apply GlobalTheory.exists_ne_zero_comb_mem_ker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalLocalBetweenStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_local_between_alt : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i →
    ∀ (L : Type) [Field L] [Algebra (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
      [Algebra.IsSeparable (FractionRing A) L],
    ∃ (A₁ : Type) (_ : CommRing A₁) (_ : IsDomain A₁) (_ : IsLocalRing A₁) (_ : IsNoetherianRing A₁)
      (_ : IsIntegrallyClosed A₁) (_ : Algebra.EssFiniteType ℤ A₁) (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective j ∧ Function.Injective i₁ ∧ IsLocalHom i₁ ∧ i₁.comp j = i ∧
      ∃ κ : L →+* FractionRing A₁,
        κ.comp ((algebraMap (FractionRing A) L).comp (algebraMap A (FractionRing A))) =
          (algebraMap A₁ (FractionRing A₁)).comp j := by
  first | (exact @GlobalTheory.LocAcycEmbed.exists_normal_local_between) | (exact GlobalTheory.LocAcycEmbed.exists_normal_local_between) | (intros; apply GlobalTheory.LocAcycEmbed.exists_normal_local_between  <;> assumption)
end

