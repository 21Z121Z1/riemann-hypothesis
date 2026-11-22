import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0185
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0186

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomFlatOfCompFlatOfMapMaximalIdeal
section
open TensorProduct LinearMap IsLocalRing

namespace GlobalTheory

namespace LocalFlatMax

universe u

variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]

theorem lTensor_injective_of_smul_le (I : Ideal A) [hI : I.IsMaximal]
    (h : Function.Injective (I.subtype.lTensor M))
    {F : Type u} [AddCommGroup F] [Module A F] (N : Submodule A F)
    (hN : I • (⊤ : Submodule A F) ≤ N) : Function.Injective (N.subtype.lTensor M) := by
  let p : (M →₀ A) →ₗ[A] M := Finsupp.linearCombination A id
  have hp : Function.Surjective p := Finsupp.linearCombination_id_surjective A M
  have h1 : Function.Injective ((ker p).subtype.lTensor (A ⧸ I)) :=
    lTensor_injective_of_exact_of_exact_of_rTensor_injective (exact_subtype_mkQ I)
      (Submodule.mkQ_surjective I) (exact_subtype_ker_map p) hp
      ((lTensor_inj_iff_rTensor_inj _ _).mp h)
      (Module.Flat.lTensor_preserves_injective_linearMap _ (ker p).injective_subtype)
  have htors : Module.IsTorsionBySet A (F ⧸ N) I := by
    intro x a
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    change N.mkQ (a.1 • x) = 0
    exact (Submodule.Quotient.mk_eq_zero N).mpr (hN (Submodule.smul_mem_smul a.2 trivial))
  letI : Module (A ⧸ I) (F ⧸ N) := htors.module
  haveI : IsScalarTower A (A ⧸ I) (F ⧸ N) := htors.isScalarTower
  letI : Field (A ⧸ I) := Ideal.Quotient.field I
  have h2 : Function.Injective ((ker p).subtype.lTensor (F ⧸ N)) := by
    have h3 : Function.Injective
        ((AlgebraTensorModule.lTensor (A ⧸ I) (A ⧸ I) (ker p).subtype).lTensor (F ⧸ N)) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ h1
    have : AlgebraTensorModule.lTensor (A ⧸ I) (F ⧸ N) (ker p).subtype =
        (AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) (F ⧸ N) _).toLinearMap ∘ₗ
          (AlgebraTensorModule.lTensor (A ⧸ I) (A ⧸ I) (ker p).subtype).lTensor (F ⧸ N) ∘ₗ
          (AlgebraTensorModule.cancelBaseChange A (A ⧸ I) (A ⧸ I) (F ⧸ N) _).symm.toLinearMap := by
      ext
      simp
    change Function.Injective (AlgebraTensorModule.lTensor (A ⧸ I) (F ⧸ N) (ker p).subtype)
    rw [this]
    simpa using h3
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective (exact_subtype_ker_map p) hp
    (exact_subtype_mkQ N) (Submodule.mkQ_surjective N) ((lTensor_inj_iff_rTensor_inj _ _).mp h2)
    (Module.Flat.lTensor_preserves_injective_linearMap _ N.injective_subtype)

theorem lTensor_injective_of_pow_smul_le (I : Ideal A) [hI : I.IsMaximal]
    (h : Function.Injective (I.subtype.lTensor M))
    {F : Type u} [AddCommGroup F] [Module A F] (n : ℕ) (N : Submodule A F)
    (hN : I ^ n • (⊤ : Submodule A F) ≤ N) : Function.Injective (N.subtype.lTensor M) := by
  induction n generalizing N with
  | zero => exact lTensor_injective_of_smul_le I h N (le_top.trans (by simpa using hN))
  | succ n ih =>
    let N' : Submodule A F := N ⊔ I ^ n • ⊤
    have h1 := ih N' le_sup_right
    have h2 := lTensor_injective_of_smul_le I h (N.comap N'.subtype) (by
      rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'', Submodule.map_subtype_top,
        Submodule.smul_sup, ← Submodule.mul_smul, ← pow_succ']
      exact sup_le Submodule.smul_le_right hN)
    have : N.subtype = N'.subtype ∘ₗ (N.comap N'.subtype).subtype ∘ₗ
        (Submodule.comapSubtypeEquivOfLe (le_sup_left : N ≤ N')).symm.toLinearMap := by
      ext
      rfl
    rw [this, lTensor_comp, lTensor_comp]
    exact h1.comp (h2.comp (LinearEquiv.lTensor M _).injective)

theorem relationsLift_of_lTensor_injective (K : Ideal A)
    (h : ∀ L : Ideal A, K ≤ L → Function.Injective (L.subtype.lTensor M)) :
    LocalFlat.RelationsLift K M := by
  intro F _ _ f x hx
  have hy : ∃ y : M ⊗[A] K, TensorProduct.rid A M (K.subtype.lTensor M y) =
      TensorProduct.rid A M (f.lTensor M x) := by
    refine Submodule.smul_induction_on (p := fun d => ∃ y : M ⊗[A] K,
      TensorProduct.rid A M (K.subtype.lTensor M y) = d) hx ?_ ?_
    · intro r hr m _
      exact ⟨m ⊗ₜ ⟨r, hr⟩, by simp⟩
    · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨a + b, by simp⟩
  obtain ⟨y, hy⟩ := hy
  replace hy := (TensorProduct.rid A M).injective hy
  let g : F × K →ₗ[A] A := f.coprod (-K.subtype)
  let z : M ⊗[A] (F × K) := (inl A F K).lTensor M x + (inr A F K).lTensor M y
  have hgz : g.lTensor M z = 0 := by
    simp only [z, g, map_add, ← lTensor_comp_apply, coprod_inl, coprod_inr, lTensor_neg,
      LinearMap.neg_apply, hy, add_neg_cancel]
  have hL : K ≤ range g := fun a ha => ⟨(0, ⟨-a, neg_mem ha⟩), by simp [g]⟩
  have hz : g.rangeRestrict.lTensor M z = 0 := by
    apply h _ hL
    rw [← lTensor_comp_apply, map_zero]
    exact hgz
  obtain ⟨w, hw⟩ := (lTensor_exact M (exact_subtype_ker_map g.rangeRestrict)
    g.surjective_rangeRestrict z).mp hz
  refine LocalFlat.range_lTensor_le (fst A F K ∘ₗ (ker g.rangeRestrict).subtype) _ ?_ ⟨w, ?_⟩
  · rintro ⟨⟨v, k⟩, hv⟩
    have : f v + -(k : A) = 0 := congrArg Subtype.val hv
    change f v ∈ K
    rw [add_neg_eq_zero.mp this]
    exact k.2
  · rw [lTensor_comp_apply, hw]
    simp only [z, map_add, ← lTensor_comp_apply, fst_comp_inl, fst_comp_inr, lTensor_id,
      lTensor_zero, LinearMap.zero_apply, add_zero, id_apply]

theorem flat_of_lTensor_injective [IsNoetherianRing A] (B : Type*) [CommRing B] [Algebra A B]
    [IsNoetherianRing B] [Module B M] [IsScalarTower A B M] [Module.Finite B M] (I : Ideal A)
    [I.IsMaximal] (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥)
    (h : Function.Injective (I.subtype.lTensor M)) : Module.Flat A M :=
  LocalFlat.flat_of_relationsLift B hI fun n =>
    relationsLift_of_lTensor_injective _ fun L hL =>
      lTensor_injective_of_pow_smul_le I h n L (by simpa using hL)

theorem lTensor_map_injective {O : Type*} [CommRing O] [Algebra O A] [Module O M]
    [IsScalarTower O A M] [Module.Flat O M] (J : Ideal O) :
    Function.Injective ((J.map (algebraMap O A)).subtype.lTensor M) := by
  let j : J →ₗ[O] J.map (algebraMap O A) :=
    { toFun := fun a => ⟨algebraMap O A a, Ideal.mem_map_of_mem _ a.2⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun a b => Subtype.ext (by simp [Algebra.smul_def]) }
  let t : M ⊗[O] J →ₗ[O] M ⊗[A] J.map (algebraMap O A) :=
    mapOfCompatibleSMul A O O M _ ∘ₗ j.lTensor M
  have ht : ∀ x, ∃ y, t y = x := by
    intro x
    induction x with
    | zero => exact ⟨0, map_zero _⟩
    | add a b ha hb =>
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      exact ⟨a + b, map_add _ _ _⟩
    | tmul m r =>
      obtain ⟨r, hr⟩ := r
      induction hr using Submodule.span_induction generalizing m with
      | mem r hr =>
        obtain ⟨a, ha, rfl⟩ := hr
        exact ⟨m ⊗ₜ ⟨a, ha⟩, rfl⟩
      | zero => exact ⟨0, (map_zero _).trans (tmul_zero _ _).symm⟩
      | add a b ha hb iha ihb =>
        obtain ⟨a', ha'⟩ := iha m
        obtain ⟨b', hb'⟩ := ihb m
        exact ⟨a' + b', by rw [map_add, ha', hb', ← tmul_add]; rfl⟩
      | smul c a ha iha =>
        obtain ⟨a', ha'⟩ := iha (c • m)
        exact ⟨a', by rw [ha', smul_tmul]; rfl⟩
  have hc : ∀ y, TensorProduct.rid A M ((J.map (algebraMap O A)).subtype.lTensor M (t y)) =
      TensorProduct.rid O M (J.subtype.lTensor M y) := by
    intro y
    induction y with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul m a => simp [t, j]
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := ht x
  have h0 := hc y
  rw [hx, map_zero, eq_comm, LinearEquiv.map_eq_zero_iff] at h0
  have h1 : y = 0 :=
    Module.Flat.lTensor_preserves_injective_linearMap _ J.injective_subtype
      (h0.trans (map_zero _).symm)
  rw [h1, map_zero]

end LocalFlatMax

theorem ringHom_flat_of_comp_flat_of_map_maximalIdeal :
    ∀ (O R' E : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R']
      [IsLocalRing R'] [IsNoetherianRing R'] [CommRing E] [IsLocalRing E] [IsNoetherianRing E]
      (φ' : O →+* R') (b : R' →+* E), φ'.Flat → (maximalIdeal O).map φ' = maximalIdeal R' →
      IsLocalHom b → (b.comp φ').Flat → b.Flat := by
  intro O R' E _ _ _ _ _ _ _ _ _ φ' b _ hm hb hc
  algebraize [φ', b, b.comp φ']
  refine LocalFlatMax.flat_of_lTensor_injective E (maximalIdeal R') ?_ ?_
  · have h : (maximalIdeal R').map b ≤ maximalIdeal E := ((local_hom_TFAE b).out 0 2).mp hb
    exact h.trans (maximalIdeal_le_jacobson _)
  · rw [← hm]
    exact LocalFlatMax.lTensor_map_injective (maximalIdeal O)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfUnityExpZModAdditiveCharacterProperties
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.AddCharZMod

theorem ch_eq (N : ℕ) [NeZero N] (j : ZMod N) : ch N j = ZMod.stdAddChar j := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rfl

theorem main : ∀ (N : ℕ) [NeZero N], (∀ n : ℤ, ch N (n : ZMod N) = Complex.exp (2 * Real.pi * Complex.I * n / N)) ∧ (∀ i j, ch N (i + j) = ch N i * ch N j) ∧ ch N 0 = 1 ∧ (∀ j, ch N j = 1 ↔ j = 0) ∧ (∀ (m : ℕ) j, ch N ((m : ZMod N) * j) = ch N j ^ m) ∧ (∀ j, ch N (-j) = (ch N j)⁻¹) ∧ (∀ j, ‖ch N j‖ = 1) ∧ (∀ j, IsIntegral ℤ (ch N j)) := by
  intro N _
  have hpow : ∀ (m : ℕ) (j : ZMod N), ch N ((m : ZMod N) * j) = ch N j ^ m := by
    intro m j
    rw [ch_eq, ch_eq, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have hadd : ∀ i j, ch N (i + j) = ch N i * ch N j := by
    intro i j
    rw [ch_eq, ch_eq, ch_eq]
    exact AddChar.map_add_eq_mul _ i j
  have hzero : ch N 0 = 1 := by
    rw [ch_eq]
    exact AddChar.map_zero_eq_one _
  refine ⟨fun n => ?_, hadd, hzero, fun j => ?_, hpow, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · rw [ch_eq]
    exact ZMod.stdAddChar_coe n
  · rw [ch_eq, ← (ZMod.stdAddChar (N := N)).map_zero_eq_one, ZMod.injective_stdAddChar.eq_iff]
  · have h : ch N (-j) * ch N j = 1 := by
      rw [← hadd, neg_add_cancel, hzero]
    exact eq_inv_of_mul_eq_one_left h
  · rw [ch_eq, ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  · have h : ch N j ^ N = 1 := by
      rw [← hpow, ZMod.natCast_self, zero_mul, hzero]
    refine IsIntegral.of_pow (Nat.pos_of_neZero N) ?_
    rw [h]
    exact isIntegral_one

end GlobalTheory.WpFam.AddCharZMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSumMapFrobeniusPow
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

open Polynomial SemidirectProduct in
open scoped Classical in

theorem _root_.GlobalTheory.Shin.rootSum_map_frobeniusPow : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F →+* F) (j : ℕ), (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (k : ℕ) (P : F[X]), _root_.GlobalTheory.CuspGL.rootSum θ k (P.map t) = _root_.GlobalTheory.CuspGL.rootSum θ (k * ringChar F ^ j) P := by
  intro F _ _ θ t j ht k P
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  haveI : CharP (AlgebraicClosure F) (ringChar F) :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective (ringChar F)
  haveI : ExpChar (AlgebraicClosure F) (ringChar F) := ExpChar.prime Fact.out
  unfold _root_.GlobalTheory.CuspGL.rootSum
  have hmap : (P.map t).map (algebraMap F (AlgebraicClosure F)) =
      (P.map (algebraMap F (AlgebraicClosure F))).map
        (iterateFrobenius (AlgebraicClosure F) (ringChar F) j) := by
    rw [map_map, map_map]
    congr 1
    ext x
    simp [iterateFrobenius_def, ht, map_pow]
  rw [hmap, ← roots_map_of_injective_of_card_eq_natDegree
    (iterateFrobenius (AlgebraicClosure F) (ringChar F) j).injective
    IsAlgClosed.card_roots_eq_natDegree, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun α _ => ?_
  rw [Function.comp_apply, iterateFrobenius_def, map_pow, ← pow_mul, mul_comm]

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSumMinpolyPowEqSum
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem rootSum_minpoly_pow_eq_sum : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (m l : ℕ)
    (α : AlgebraicClosure F), 0 < m → α ^ (Nat.card F ^ m - 1) = 1 →
    rootSum θ l (minpoly F α ^ (m / (minpoly F α).natDegree)) =
      ∑ a ∈ Finset.range m, θ α ^ (l * Nat.card F ^ a) := by
  intro F _ _ θ m l α hm hα
  rw [((GlobalTheory.CuspGL.torus_minpoly F θ m hm α hα).2.2 l)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_pow, ← pow_mul, mul_comm]

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSumsTwoThreeClosedFormRealNonInteger
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open Filter Topology

namespace GlobalTheory.WpFam.RowReal

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
private lemma norm_add_intCast_eq_abs_of_im_eq_zero {w : ℂ} (hw : w.im = 0) (m : ℤ) :
    ‖w + m‖ = |(m : ℝ) + w.re| := by
  have h : w + m = ((w.re + m : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hw])
  rw [h, Complex.norm_real, Real.norm_eq_abs, add_comm]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
private lemma exists_pos_le_norm_add_intCast_of_im_eq_zero {w : ℂ} (hw : w.im = 0) (hn : ∀ n : ℤ, w ≠ n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℤ, δ ≤ ‖w + m‖ := by
  have hwx : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hw])
  have hf0 : 0 < Int.fract w.re := by
    rcases (Int.fract_nonneg w.re).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hn ⌊w.re⌋
      have h2 := Int.floor_add_fract w.re
      rw [← h, add_zero] at h2
      exact Complex.ext (by simp [h2]) (by simp [hw])
  have hf1 := Int.fract_lt_one w.re
  refine ⟨min (Int.fract w.re) (1 - Int.fract w.re), lt_min hf0 (by linarith), fun m => ?_⟩
  rw [norm_add_intCast_eq_abs_of_im_eq_zero hw m]
  have hx := Int.floor_add_fract w.re
  rcases le_or_gt 0 (⌊w.re⌋ + m) with h | h
  · have h' : (0 : ℝ) ≤ ((⌊w.re⌋ + m : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    rw [abs_of_nonneg (by linarith)]
    exact (min_le_left _ _).trans (by linarith)
  · have h' : ((⌊w.re⌋ + m : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : ⌊w.re⌋ + m ≤ -1)
    push_cast at h'
    rw [abs_of_neg (by linarith)]
    exact (min_le_right _ _).trans (by linarith)

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
private lemma tsum_one_div_add_int_pow_of_real_of_continuousAt {w : ℂ} (hw : w.im = 0)
    (hn : ∀ n : ℤ, w ≠ n) {k : ℕ} (hk : 2 ≤ k) {G : ℂ → ℂ} (hG : ContinuousAt G w)
    (hEq : ∀ z : ℂ, 0 < z.im → ∑' m : ℤ, 1 / (z + m) ^ k = G z) :
    ∑' m : ℤ, 1 / (w + m) ^ k = G w := by
  obtain ⟨δ, hδ, hδm⟩ := exists_pos_le_norm_add_intCast_of_im_eq_zero hw hn
  have hsum : Summable fun m : ℤ => 2 ^ k * (1 / ‖w + m‖ ^ k) := by
    refine Summable.mul_left _ ?_
    have h := (Real.summable_one_div_int_add_rpow w.re (k : ℝ)).2
      (by exact_mod_cast (by omega : 1 < k))
    refine h.congr fun m => ?_
    rw [Real.rpow_natCast, norm_add_intCast_eq_abs_of_im_eq_zero hw m]
  have hlow : ∀ (m : ℤ) (x : ℂ), x ∈ Metric.closedBall w (δ / 2) → ‖w + m‖ / 2 ≤ ‖x + m‖ := by
    intro m x hx
    have hxw : ‖x - w‖ ≤ δ / 2 := by rw [← dist_eq_norm]; exact hx
    have h1 := hδm m
    have h2 := norm_sub_norm_le (w + m) (x + m)
    rw [show (w + (m : ℂ)) - (x + m) = -(x - w) by ring, norm_neg] at h2
    linarith
  have hcont : ContinuousOn (fun x : ℂ => ∑' m : ℤ, 1 / (x + (m : ℂ)) ^ k)
      (Metric.closedBall w (δ / 2)) := by
    refine continuousOn_tsum (fun m => ?_) hsum (fun m x hx => ?_)
    · refine ContinuousOn.div continuousOn_const (by fun_prop) (fun x hx => pow_ne_zero _ ?_)
      have h1 := hlow m x hx
      have h2 := hδm m
      exact norm_ne_zero_iff.mp (by linarith)
    · have hpos : 0 < ‖w + m‖ / 2 := by linarith [hδm m]
      rw [norm_div, norm_one, norm_pow]
      calc 1 / ‖x + m‖ ^ k ≤ 1 / (‖w + m‖ / 2) ^ k :=
            one_div_le_one_div_of_le (pow_pos hpos k) (pow_le_pow_left₀ hpos.le (hlow m x hx) k)
        _ = 2 ^ k * (1 / ‖w + m‖ ^ k) := by rw [div_pow, one_div_div, mul_one_div]
  have hcw : ContinuousAt (fun x : ℂ => ∑' m : ℤ, 1 / (x + (m : ℂ)) ^ k) w :=
    hcont.continuousAt (Metric.closedBall_mem_nhds w (by linarith))
  have hpath : Tendsto (fun ε : ℝ => w + ε * Complex.I) (𝓝[>] 0) (𝓝 w) := by
    have hc : Continuous (fun ε : ℝ => w + ε * Complex.I) := by fun_prop
    have h := hc.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_nhds_unique ((hcw.tendsto.comp hpath).congr' ?_) (hG.tendsto.comp hpath)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hEq _ (by simpa [hw] using hε)

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
private lemma tsum_one_div_add_int_sq_of_im_pos (z : ℂ) (hz : 0 < z.im) :
    ∑' m : ℤ, 1 / (z + m) ^ 2 = (2 * (Real.pi : ℂ) * Complex.I) ^ 2 *
      (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)
        / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)) ^ 2) := by
  have h := EisensteinSeries.qExpansion_identity (k := 1) le_rfl ⟨z, hz⟩
  have hq := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z, hz⟩
  simp only [UpperHalfPlane.coe_mk] at h hq
  simp only [Nat.reduceAdd, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
  rw [h, tsum_coe_mul_geometric_of_norm_lt_one hq]
  ring

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
private lemma tsum_sq_mul_geometric_of_norm_lt_one {r : ℂ} (hr : ‖r‖ < 1) :
    ∑' n : ℕ, (n : ℂ) ^ 2 * r ^ n = r * (1 + r) / (1 - r) ^ 3 := by
  have hne : 1 - r ≠ 0 := by
    intro h
    have : r = 1 := by linear_combination -h
    rw [this, norm_one] at hr
    exact lt_irrefl _ hr
  have hS : Summable fun n : ℕ => (n : ℂ) ^ 2 * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have hS1 : Summable fun n : ℕ => (n : ℂ) * r ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hG : Summable fun n : ℕ => r ^ n := summable_geometric_of_norm_lt_one hr
  have h1 := tsum_coe_mul_geometric_of_norm_lt_one hr
  have hg := tsum_geometric_of_norm_lt_one hr
  have hsplit := hS.tsum_eq_zero_add
  have hshift : (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ 2 * r ^ (n + 1))
      = fun n : ℕ => r * ((n : ℂ) ^ 2 * r ^ n) + 2 * r * ((n : ℂ) * r ^ n) + r * r ^ n := by
    funext n
    push_cast
    ring
  rw [hshift, ((hS.mul_left r).add (hS1.mul_left (2 * r))).tsum_add (hG.mul_left r),
    (hS.mul_left r).tsum_add (hS1.mul_left (2 * r)), tsum_mul_left, tsum_mul_left, tsum_mul_left,
    h1, hg] at hsplit
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, pow_zero,
    mul_one, zero_add] at hsplit
  set S := ∑' n : ℕ, (n : ℂ) ^ 2 * r ^ n
  have e1 : r / (1 - r) ^ 2 * (1 - r) ^ 2 = r := div_mul_cancel₀ _ (pow_ne_zero 2 hne)
  have e2 : (1 - r)⁻¹ * (1 - r) = 1 := inv_mul_cancel₀ hne
  rw [eq_div_iff (pow_ne_zero 3 hne)]
  linear_combination (1 - r) ^ 2 * hsplit + 2 * r * e1 + r * (1 - r) * e2

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
private lemma tsum_one_div_add_int_pow_three_of_im_pos (z : ℂ) (hz : 0 < z.im) :
    ∑' m : ℤ, 1 / (z + m) ^ 3 = -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 *
      (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)
        * (1 + Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z))
        / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)) ^ 3) := by
  have h := EisensteinSeries.qExpansion_identity (k := 2) (by norm_num) ⟨z, hz⟩
  have hq := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z, hz⟩
  simp only [UpperHalfPlane.coe_mk] at h hq
  simp only [Nat.reduceAdd, Nat.factorial_two, Nat.cast_ofNat] at h
  rw [h, tsum_sq_mul_geometric_of_norm_lt_one hq]
  ring

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in

theorem _root_.GlobalTheory.WpFam.RowReal.row_real : ∀ w : ℂ, w.im = 0 → (∀ n : ℤ, w ≠ n) → (∑' m : ℤ, 1 / (w + m) ^ 2 = (2 * (Real.pi : ℂ) * Complex.I) ^ 2 * (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) ^ 2)) ∧ ∑' m : ℤ, 1 / (w + m) ^ 3 = -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 * (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) * (1 + Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) ^ 3) := by
  intro w hw hn
  have hne : 1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) ≠ 0 := by
    intro h
    have h1 : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) = 1 := by linear_combination -h
    obtain ⟨n, hn'⟩ := Complex.exp_eq_one_iff.mp h1
    apply hn n
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ h2
    linear_combination hn'
  have hE : ContinuousAt (fun x : ℂ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x)) w := by
    fun_prop
  have hD2 : ContinuousAt
      (fun x : ℂ => (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x)) ^ 2) w := by
    fun_prop
  have hD3 : ContinuousAt
      (fun x : ℂ => (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x)) ^ 3) w := by
    fun_prop
  have hN3 : ContinuousAt (fun x : ℂ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x)
      * (1 + Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x))) w := by
    fun_prop
  constructor
  · exact tsum_one_div_add_int_pow_of_real_of_continuousAt (k := 2) hw hn le_rfl
      (continuousAt_const.mul (hE.div hD2 (pow_ne_zero 2 hne)))
      tsum_one_div_add_int_sq_of_im_pos
  · exact tsum_one_div_add_int_pow_of_real_of_continuousAt (k := 3) hw hn (by norm_num)
      (continuousAt_const.mul (hN3.div hD3 (pow_ne_zero 3 hne)))
      tsum_one_div_add_int_pow_three_of_im_pos

end GlobalTheory.WpFam.RowReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumActionsRingHoms
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory.Proof.sandwich_datum_actions_ring_homs

theorem actions_ringHom : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (h : ℕ) (D : Datum ε h Λ), (∃ ρ : Λ →+* Matrix (Fin h) (Fin h) O, ⇑ρ = actT D) ∧ (∃ ρ : Λ →+* Matrix (Fin h) (Fin h) O, ⇑ρ = actH D) := by
  intro p _ O _ _ _ ε Λ _ _ h D
  exact ⟨⟨(RingHom.mapMatrix (padicToO p O)).comp (D.ρT : Λ →+* Matrix (Fin h) (Fin h) ℤ_[p]), rfl⟩,
    ⟨(RingHom.mapMatrix (WittVector.fontaineTheta O p)).comp D.ρM, rfl⟩⟩

end GlobalTheory.Proof.sandwich_datum_actions_ring_homs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarOfBorelMovesOpenFramesStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_of_borel_moves_open_frames : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (m : GL (Fin r) E) (W : Set (Frame X.Ψ r)), IsOpen W → W.Nonempty → W ⊆ X.dom → (∀ x ∈ W, ∃ b ∈ Bor X.Ψ r, lact m x = rmul x b) → ∃ s : E, (m : Matrix (Fin r) (Fin r) E) = Matrix.scalar (Fin r) s := by
  first | exact @GlobalTheory.scalar_of_triangular_moves_open | exact GlobalTheory.scalar_of_triangular_moves_open | (intros; apply GlobalTheory.scalar_of_triangular_moves_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledKoszulTestFamilyHasDerivAtScaleStatement
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledKoszulTestFamily_hasDerivAt_scale : ∀ {n : ℕ} (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → GlobalTheory.PsCo.Pc1.Poly n) (q : GlobalTheory.PsCo.Pc1.Mode ε → ℕ → GlobalTheory.PsCo.Pc1.Poly n), ContDiff ℝ (⊤ : ℕ∞) G → GlobalTheory.PsCo.Pc1.IsKoszul ε p q → ∀ t : ℝ, 0 < t → ∀ g : GlobalTheory.PsCo.Pc1.Mat n, HasDerivAt (fun s : ℝ => GlobalTheory.PsCo.Pc1.famF ε G p s g) (((t⁻¹ : ℝ) : ℂ) * ∑ x : GlobalTheory.PsCo.Pc1.Mode ε, ∑ j ∈ Finset.range (GlobalTheory.PsCo.Pc1.nMode ε + 1), GlobalTheory.PsCo.Pc1.adBas ε (Matrix.single x.1.2 x.1.1 1) (iteratedDeriv (j + 1) (fun y => G (t * y))) (q x j) g) t := by
  first | exact @GlobalTheory.PsCo.HomotDeriv.famF_hasDerivAt | exact GlobalTheory.PsCo.HomotDeriv.famF_hasDerivAt | (intros; apply GlobalTheory.PsCo.HomotDeriv.famF_hasDerivAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerRepUnitaryStatement
section
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_rep_unitary : ∀ (n : ℕ) (w : Fin n ⊕ Fin n → ℝ) (u v : EuclideanSpace ℝ (Fin n) → ℂ),
    ∫ x, rhoFun w u x * starRingEnd ℂ (rhoFun w v x) = ∫ x, u x * starRingEnd ℂ (v x) := by
  first | exact @GlobalTheory.RealWeil.integral_rhoFun_mul_conj | exact GlobalTheory.RealWeil.integral_rhoFun_mul_conj | (intros; apply GlobalTheory.RealWeil.integral_rhoFun_mul_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormLinearPhaseSecondOrderLeStatement
section
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzSeminorm_linearPhase_second_order_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c : ℝ) (f : 𝓢(V, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) f - f + ((t : ℂ) * (2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ)) f) ≤ C * t ^ 2 := by
  first | exact @GlobalTheory.LinearPhase.seminorm_phase_sub_le | exact GlobalTheory.LinearPhase.seminorm_phase_sub_le | (intros; apply GlobalTheory.LinearPhase.seminorm_phase_sub_le <;> assumption)
end

