import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPosGramQuadFormTotallyPositiveProperness
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.TPos

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem reAt_eq (v : InfinitePlace F) (x : F) :
    reAt v x = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  unfold reAt
  have h := InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x
  rw [← h, Complex.ofReal_re]

theorem abs_reAt (v : InfinitePlace F) (x : F) : |reAt v x| = v x := by
  rw [reAt_eq, ← InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal v), Real.norm_eq_abs]

theorem reAt_QF {κ : Type} [Fintype κ] (G : Matrix κ κ ℤ) (x : κ → F) (v : InfinitePlace F) :
    reAt v (QF G x) =
      (fun i => reAt v (x i)) ⬝ᵥ (G.map (Int.cast : ℤ → ℝ)) *ᵥ (fun i => reAt v (x i)) / 2 := by
  set φ := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) with hφ
  have hx : (fun i => reAt v (x i)) = φ ∘ x := by
    funext i
    simp [reAt_eq, hφ]
  have hG : (G.map (Int.cast : ℤ → ℝ)) = (G.map (Int.cast : ℤ → F)).map φ := by
    ext i j
    simp
  rw [hx, hG, reAt_eq, ← hφ]
  unfold QF BF
  rw [map_div₀, map_ofNat, RingHom.map_dotProduct]
  congr 2
  funext i
  exact RingHom.map_mulVec φ _ x i

theorem posDef_lower {κ : Type} [Fintype κ] (M : Matrix κ κ ℝ) (hM : M.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : κ → ℝ, c * ∑ i, y i ^ 2 ≤ y ⬝ᵥ M *ᵥ y := by
  classical
  rcases isEmpty_or_nonempty κ with hκ | ⟨⟨i0⟩⟩
  · refine ⟨1, one_pos, fun y => ?_⟩
    simp [dotProduct]
  set f : (κ → ℝ) → ℝ := fun y => y ⬝ᵥ M *ᵥ y with hf
  have hfc : Continuous f := by
    simp only [hf, dotProduct, Matrix.mulVec]
    fun_prop
  have hpos : ∀ y : κ → ℝ, y ≠ 0 → 0 < f y := by
    intro y hy
    have := (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 hy
    simpa [hf] using this
  set S : Set (κ → ℝ) := {y | ∑ i, y i ^ 2 = 1} with hS
  have hSc : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_eq (by fun_prop) continuous_const
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨1, fun y hy => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs]
      have h1 : y i ^ 2 ≤ ∑ j, y j ^ 2 :=
        Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [show ∑ j, y j ^ 2 = 1 from hy] at h1
      exact (sq_le_one_iff_abs_le_one _).mp h1
  have hSn : S.Nonempty := ⟨Pi.single i0 1, by simp [hS, Pi.single_apply]⟩
  obtain ⟨y0, hy0S, hmin⟩ := hSc.exists_isMinOn hSn hfc.continuousOn
  have hy0 : y0 ≠ 0 := by
    rintro rfl
    simp [hS] at hy0S
  refine ⟨f y0, hpos y0 hy0, fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    simp
  set s := ∑ i, y i ^ 2 with hs
  have hs0 : 0 < s := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    have h1 : y i ^ 2 ≤ s :=
      Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hi' : y i ≠ 0 := by simpa using hi
    have : 0 < y i ^ 2 := by positivity
    linarith
  set t := Real.sqrt s with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr hs0
  have htt : t ^ 2 = s := Real.sq_sqrt hs0.le
  have hz : t⁻¹ • y ∈ S := by
    simp only [hS, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [← Finset.mul_sum, ← hs, inv_pow, htt, inv_mul_cancel₀ hs0.ne']
  have hfz : f (t⁻¹ • y) = (t ^ 2)⁻¹ * f y := by
    simp only [hf, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have := hmin hz
  simp only [Set.mem_setOf_eq] at this
  rw [hfz, htt] at this
  have h2 := mul_le_mul_of_nonneg_left this hs0.le
  rw [← mul_assoc, mul_inv_cancel₀ hs0.ne', one_mul] at h2
  linarith [mul_comm s (f y0)]

end GlobalTheory.TPos

open GlobalTheory.TPos in

theorem GlobalTheory.HilbertThetaSeries.qf_totPos_proper : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ]
    (G : Matrix κ κ ℤ), EvenPos G → (∀ x : κ → F, x ≠ 0 → TP (QF G x)) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ (x : κ → F) v, c * ∑ i, reAt v (x i) ^ 2 ≤ reAt v (QF G x)) ∧
      ∀ (a ξ : F), {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}.Finite := by
  intro F _ _ _ κ _ _ G hG
  have hM : (G.map (Int.cast : ℤ → ℝ)).PosDef := hG.1
  obtain ⟨c, hc, hcb⟩ := posDef_lower _ hM
  have key : ∀ (x : κ → F) v, (c / 2) * ∑ i, reAt v (x i) ^ 2 ≤ reAt v (QF G x) := by
    intro x v
    rw [reAt_QF]
    have := hcb (fun i => reAt v (x i))
    linarith
  have hinj : ∀ (v : InfinitePlace F) (y : F), reAt v y = 0 → y = 0 := by
    intro v y h
    rw [reAt_eq] at h
    exact (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v)).injective (by simpa using h)
  refine ⟨?_, ⟨c / 2, by positivity, key⟩, ?_⟩
  · intro x hx v
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    have hyi : reAt v (x i) ≠ 0 := fun h => hi (hinj v _ h)
    have h1 : reAt v (x i) ^ 2 ≤ ∑ j, reAt v (x j) ^ 2 :=
      Finset.single_le_sum (f := fun j => reAt v (x j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : 0 < reAt v (x i) ^ 2 := by positivity
    have h3 := mul_pos (half_pos hc) (lt_of_lt_of_le h2 h1)
    have := key x v
    linarith
  · intro a ξ
    by_cases ha : a = 0
    · apply (Set.finite_singleton (0 : κ → F)).subset
      rintro x ⟨hx, -⟩
      unfold aL at hx
      obtain ⟨z, -, rfl⟩ := AddSubgroup.mem_map.mp hx
      simp [ha]
    set B : ℝ := ∑ v : InfinitePlace F, Real.sqrt (reAt v ξ / (c / 2)) / v a with hB
    set T : Set F := {y : F | IsIntegral ℤ y ∧ ∀ φ : F →+* ℂ, ‖φ y‖ ≤ B} with hT
    have hTf : T.Finite := NumberField.Embeddings.finite_of_norm_le F ℂ B
    apply ((Set.Finite.pi (t := fun _ : κ => T) (fun _ => hTf)).image (fun z => a • z)).subset
    rintro x ⟨hx, hxξ⟩
    unfold aL at hx
    obtain ⟨z, hz, rfl⟩ := AddSubgroup.mem_map.mp hx
    refine ⟨z, fun i _ => ?_, rfl⟩
    unfold LL at hz
    have hzi := (AddSubgroup.mem_pi _).mp hz i (Set.mem_univ _)
    refine ⟨hzi, fun φ => ?_⟩
    rw [← NumberField.InfinitePlace.apply]
    set w := InfinitePlace.mk φ
    have hxi : (DistribMulAction.toAddMonoidHom (κ → F) a z) i = a * z i := by simp
    have hwa : 0 < w a := (InfinitePlace.pos_iff).mpr ha
    have hk := key (DistribMulAction.toAddMonoidHom (κ → F) a z) w
    rw [hxξ] at hk
    have h1 : reAt w ((DistribMulAction.toAddMonoidHom (κ → F) a z) i) ^ 2 ≤
        ∑ j, reAt w ((DistribMulAction.toAddMonoidHom (κ → F) a z) j) ^ 2 :=
      Finset.single_le_sum (f := fun j => reAt w ((DistribMulAction.toAddMonoidHom (κ → F) a z) j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : reAt w ((DistribMulAction.toAddMonoidHom (κ → F) a z) i) ^ 2 ≤ reAt w ξ / (c / 2) := by
      rw [le_div_iff₀ (half_pos hc)]
      nlinarith
    have h3 := Real.abs_le_sqrt h2
    rw [abs_reAt, hxi, map_mul] at h3
    have h4 : w (z i) ≤ Real.sqrt (reAt w ξ / (c / 2)) / w a := by
      rw [le_div_iff₀ hwa]
      linarith [mul_comm (w a) (w (z i))]
    refine h4.trans ?_
    exact Finset.single_le_sum (f := fun v : InfinitePlace F => Real.sqrt (reAt v ξ / (c / 2)) / v a)
      (fun v _ => div_nonneg (Real.sqrt_nonneg _) (apply_nonneg v a)) (Finset.mem_univ w)

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenPosGram_quadForm_totallyPositive_properness : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → (∀ x : κ → F, x ≠ 0 → TP (QF G x)) ∧ (∃ c : ℝ, 0 < c ∧ ∀ (x : κ → F) v, c * ∑ i, reAt v (x i) ^ 2 ≤ reAt v (QF G x)) ∧ ∀ (a ξ : F), {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}.Finite := by
  first | exact @GlobalTheory.HilbertThetaSeries.qf_totPos_proper | exact GlobalTheory.HilbertThetaSeries.qf_totPos_proper | (intros; apply GlobalTheory.HilbertThetaSeries.qf_totPos_proper <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsFiniteRepsScaledLatticeCardNorm
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.RepsLat

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem mem_aL_iff (a : F) (x : κ → F) :
    x ∈ aL κ a ↔ ∃ m : κ → 𝓞 F, x = fun i => a * (m i : F) := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨fun i => ⟨l i, (AddSubgroup.mem_pi _).1 hl i (Set.mem_univ _)⟩, ?_⟩
    funext i
    rfl
  · rintro ⟨m, rfl⟩
    refine ⟨fun i => (m i : F), ?_, ?_⟩
    · exact (AddSubgroup.mem_pi _).2 fun i _ => (m i).2
    · funext i
      rfl

end GlobalTheory.HilbertThetaSeries.RepsLat

namespace GlobalTheory.HilbertThetaSeries

open GlobalTheory.HilbertThetaSeries.RepsLat in

theorem exists_isReps_aL : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (a b : F),
    a ≠ 0 → b ≠ 0 → IsIntegral ℤ (a / b) → ∃ T : Finset (κ → F), IsReps (aL κ a) (aL κ b) T ∧ 0 ∈ T ∧
      aL κ a ≤ aL κ b ∧ (T.card : ℚ) = |Algebra.norm ℚ (a / b)| ^ Fintype.card κ := by
  intro F _ _ κ _ _ a b ha hb hc
  obtain ⟨c, hcF⟩ : ∃ c : 𝓞 F, (c : F) = a / b := ⟨⟨a / b, hc⟩, rfl⟩
  have hab : a = b * (c : F) := by rw [hcF]; field_simp
  have hc0 : c ≠ 0 := by
    intro h
    apply ha
    have h0 : (c : F) = 0 := by rw [h]; rfl
    rw [hcF, div_eq_zero_iff] at h0
    tauto
  let I : Ideal (𝓞 F) := Ideal.span {c}
  have hcard : Nat.card (𝓞 F ⧸ I) = (Algebra.norm ℤ c).natAbs := by
    rw [← Ideal.absNorm_span_singleton, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hne : (Algebra.norm ℤ c).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero, Algebra.norm_ne_zero_iff]
    exact hc0
  haveI : Finite (𝓞 F ⧸ I) := Nat.finite_of_card_ne_zero (hcard ▸ hne)
  letI : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  classical
  let s : 𝓞 F ⧸ I → 𝓞 F := fun q => if q = 0 then 0 else Classical.choose (Ideal.Quotient.mk_surjective q)
  have hs : ∀ q, Ideal.Quotient.mk I (s q) = q := by
    intro q
    by_cases h : q = 0
    · simp [s, h]
    · simp only [s, if_neg h]
      exact Classical.choose_spec (Ideal.Quotient.mk_surjective q)
  have hs0 : s 0 = 0 := by simp [s]
  let e : (κ → 𝓞 F ⧸ I) → (κ → F) := fun q i => b * (s (q i) : F)
  have he : Function.Injective e := by
    intro q q' h
    funext i
    have h1 := mul_left_cancel₀ hb (congrFun h i)
    have h3 : s (q i) = s (q' i) := RingOfIntegers.ext h1
    rw [← hs (q i), ← hs (q' i), h3]
  refine ⟨Finset.univ.image e, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact (mem_aL_iff b _).2 ⟨fun i => s (q i), rfl⟩
  · intro x hx
    obtain ⟨m, rfl⟩ := (mem_aL_iff b x).1 hx
    refine ⟨e (fun i => Ideal.Quotient.mk I (m i)), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have hI : ∀ i, m i - s (Ideal.Quotient.mk I (m i)) ∈ I := fun i => by
        rw [← Ideal.Quotient.eq, hs]
      choose r hr using fun i => Ideal.mem_span_singleton'.1 (hI i)
      refine (mem_aL_iff a _).2 ⟨r, ?_⟩
      funext i
      have h1 := congrArg (fun z : 𝓞 F => (z : F)) (hr i)
      simp only [map_mul, map_sub] at h1
      simp only [e, Pi.sub_apply]
      rw [hab]
      linear_combination -b * h1
    · rintro y ⟨hyT, hy⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hyT
      have hq : q = fun i => Ideal.Quotient.mk I (m i) := by
        funext i
        obtain ⟨r, hr⟩ := (mem_aL_iff a _).1 hy
        have h1 := congrFun hr i
        simp only [e, Pi.sub_apply] at h1
        have h2 : ((m i - s (q i) : 𝓞 F) : F) = ((r i * c : 𝓞 F) : F) := by
          simp only [map_mul, map_sub]
          apply mul_left_cancel₀ hb
          rw [hab] at h1
          linear_combination h1
        have h3 : m i - s (q i) ∈ I := Ideal.mem_span_singleton'.2 ⟨r i, (RingOfIntegers.ext h2).symm⟩
        rw [← hs (q i)]
        exact (Ideal.Quotient.eq.2 h3).symm
      rw [hq]
  · refine Finset.mem_image.2 ⟨0, Finset.mem_univ _, ?_⟩
    funext i
    simp [e, hs0]
  · intro x hx
    obtain ⟨m, rfl⟩ := (mem_aL_iff a x).1 hx
    refine (mem_aL_iff b _).2 ⟨fun i => c * m i, ?_⟩
    funext i
    simp only [map_mul]
    rw [hab]
    ring
  · rw [Finset.card_image_of_injective _ he, Finset.card_univ, Fintype.card_fun, ← Nat.card_eq_fintype_card,
      hcard, ← hcF, Nat.cast_pow, Nat.cast_natAbs, ← Algebra.coe_norm_int, Int.cast_abs]

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_reps_scaled_lattice_card_norm : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (a b : F), a ≠ 0 → b ≠ 0 → IsIntegral ℤ (a / b) → ∃ T : Finset (κ → F), IsReps (aL κ a) (aL κ b) T ∧ 0 ∈ T ∧ aL κ a ≤ aL κ b ∧ (T.card : ℚ) = |Algebra.norm ℚ (a / b)| ^ Fintype.card κ := by
  first | exact @GlobalTheory.HilbertThetaSeries.exists_isReps_aL | exact GlobalTheory.HilbertThetaSeries.exists_isReps_aL | (intros; apply GlobalTheory.HilbertThetaSeries.exists_isReps_aL <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EzOfComplex
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.QHol

open UpperHalfPlane hiding I

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def lin (ξ : F) : (InfinitePlace F → ℂ) →L[ℂ] ℂ :=
  ∑ v, (reAt v ξ : ℂ) • ContinuousLinearMap.proj v

theorem lin_apply (ξ : F) (z : InfinitePlace F → ℂ) : lin ξ z = ∑ v, (reAt v ξ : ℂ) * z v := by
  simp [lin]

def sm (ξ : F) : ℝ := ∑ v, reAt v ξ

theorem norm_lin_le (ξ : F) (h : ∀ v, 0 ≤ reAt v ξ) : ‖lin ξ‖ ≤ sm ξ := by
  have hs : 0 ≤ sm ξ := Finset.sum_nonneg (fun v _ => h v)
  refine ContinuousLinearMap.opNorm_le_bound _ hs (fun z => ?_)
  rw [lin_apply]
  calc ‖∑ v, (reAt v ξ : ℂ) * z v‖ ≤ ∑ v, ‖(reAt v ξ : ℂ) * z v‖ := norm_sum_le _ _
    _ ≤ ∑ v, reAt v ξ * ‖z‖ := by
      apply Finset.sum_le_sum
      intro v _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h v)]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z v) (h v)
    _ = sm ξ * ‖z‖ := by rw [sm, Finset.sum_mul]

theorem re_lin (ξ : F) (z : InfinitePlace F → ℂ) :
    (2 * Real.pi * Complex.I * lin ξ z).re = -(2 * Real.pi * ∑ v, reAt v ξ * (z v).im) := by
  rw [lin_apply]
  simp [Complex.mul_re, Complex.mul_im, Complex.im_sum, Finset.mul_sum]

theorem ez_ofComplex (ξ : F) (z : InfinitePlace F → ℂ) (hz : ∀ v, 0 < (z v).im) :
    ez ξ (fun v => ofComplex (z v)) = Complex.exp (2 * Real.pi * Complex.I * lin ξ z) := by
  simp only [ez, lin_apply]
  congr 2
  apply Finset.sum_congr rfl
  intro v _
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hz v)]

private theorem mul_exp_neg_le_exp_half (m x : ℝ) (hm : 0 < m) (hx : 0 ≤ x) :
    2 * Real.pi * x * Real.exp (-(2 * Real.pi * m * x)) ≤ (2 / m) * Real.exp (-(Real.pi * m * x)) := by
  set t := Real.pi * m * x with ht_def
  have ht : 0 ≤ t := by positivity
  have e : Real.exp (-(2 * Real.pi * m * x)) = Real.exp (-t) * Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    rw [ht_def]
    ring
  have hexp : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  have key : t * Real.exp (-t) ≤ 1 := by
    have := Real.add_one_le_exp t
    nlinarith [Real.exp_pos (-t)]
  have hx2 : 2 * Real.pi * x = (2 / m) * t := by
    rw [ht_def]
    field_simp
  rw [e, hx2]
  have hE : 0 ≤ (2 / m) * Real.exp (-t) := by positivity
  calc 2 / m * t * (Real.exp (-t) * Real.exp (-t)) = (2 / m) * Real.exp (-t) * (t * Real.exp (-t)) := by ring
    _ ≤ (2 / m) * Real.exp (-t) * 1 := mul_le_mul_of_nonneg_left key hE
    _ = (2 / m) * Real.exp (-t) := by ring

theorem hol : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f : Hn F → ℂ) (a : F → ℂ),
    HasQ f a → Hol f := by
  intro F _ _ _ f a hQ
  obtain ⟨⟨D, hD, hsupp⟩, hsum⟩ := hQ
  have hpos : ∀ ξ, a ξ ≠ 0 → ∀ v, 0 ≤ reAt v ξ := by
    intro ξ hξ v
    rcases (hsupp ξ hξ).1 with h0 | htp
    · subst h0
      simp [reAt]
    · exact (htp v).le
  have hsm : ∀ ξ, a ξ ≠ 0 → 0 ≤ sm ξ := fun ξ hξ => Finset.sum_nonneg (fun v _ => hpos ξ hξ v)
  unfold Hol
  intro z0 hz0
  have hz0' : ∀ v, 0 < (z0 v).im := hz0
  obtain ⟨m, hmz, hm⟩ : ∃ m : ℝ, (∀ v, m < (z0 v).im) ∧ 0 < m := by
    have h1 : ∀ᶠ m in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ v, m < (z0 v).im :=
      Filter.eventually_all.2 (fun v => eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (hz0' v)))
    exact (h1.and self_mem_nhdsWithin).exists
  set s : Set (InfinitePlace F → ℂ) := {z | ∀ v, m < (z v).im} with hs_def
  have hsopen : IsOpen s := by
    rw [hs_def, Set.setOf_forall]
    exact isOpen_iInter_of_finite (fun v => isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply v)))
  have hsconv : Convex ℝ s := by
    intro x hx y hy p q hp hq hpq v
    have h1 := hx v
    have h2 := hy v
    simp only [Pi.add_apply, Pi.smul_apply, Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    have e : p * (x v).im + q * (y v).im - m = p * ((x v).im - m) + q * ((y v).im - m) := by
      have : m = p * m + q * m := by rw [← add_mul, hpq, one_mul]
      linarith
    by_cases hp0 : p = 0
    · have hq1 : q = 1 := by linarith
      subst hp0 hq1
      linarith
    · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
      have := mul_pos hp' (sub_pos.2 h1)
      have := mul_nonneg hq (sub_pos.2 h2).le
      linarith
  have hz0s : z0 ∈ s := hmz
  have hpos_s : ∀ z ∈ s, ∀ v, 0 < (z v).im := fun z hz v => hm.trans (hz v)
  let g : F → (InfinitePlace F → ℂ) → ℂ := fun ξ z => a ξ * Complex.exp (2 * Real.pi * Complex.I * lin ξ z)
  let g' : F → (InfinitePlace F → ℂ) → ((InfinitePlace F → ℂ) →L[ℂ] ℂ) := fun ξ z =>
    a ξ • (Complex.exp (2 * Real.pi * Complex.I * lin ξ z) • ((2 * Real.pi * Complex.I) • lin ξ))
  let u : F → ℝ := fun ξ => ‖a ξ‖ * (2 * Real.pi * sm ξ * Real.exp (-(2 * Real.pi * m * sm ξ)))
  have hderiv : ∀ ξ z, z ∈ s → HasFDerivAt (g ξ) (g' ξ z) z := by
    intro ξ z _
    have h1 : HasFDerivAt (fun z => 2 * Real.pi * Complex.I * lin ξ z) ((2 * Real.pi * Complex.I) • lin ξ) z :=
      (lin ξ).hasFDerivAt.const_mul (2 * Real.pi * Complex.I)
    exact (h1.cexp).const_mul (a ξ)
  have hbound : ∀ ξ z, z ∈ s → ‖g' ξ z‖ ≤ u ξ := by
    intro ξ z hz
    by_cases ha : a ξ = 0
    · simp [g', u, ha]
    have hr := hpos ξ ha
    have hsum_le : m * sm ξ ≤ ∑ v, reAt v ξ * (z v).im := by
      rw [sm, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro v _
      have := hz v
      nlinarith [hr v]
    simp only [g', u, norm_smul, Complex.norm_exp, re_lin]
    have hc : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
      simp [Real.pi_pos.le]
    rw [hc]
    have hL := norm_lin_le ξ hr
    have hexp : Real.exp (-(2 * Real.pi * ∑ v, reAt v ξ * (z v).im)) ≤ Real.exp (-(2 * Real.pi * m * sm ξ)) := by
      apply Real.exp_le_exp.2
      nlinarith [Real.pi_pos]
    have hn : 0 ≤ ‖a ξ‖ := norm_nonneg _
    calc ‖a ξ‖ * (Real.exp (-(2 * Real.pi * ∑ v, reAt v ξ * (z v).im)) * (2 * Real.pi * ‖lin ξ‖))
        ≤ ‖a ξ‖ * (Real.exp (-(2 * Real.pi * m * sm ξ)) * (2 * Real.pi * sm ξ)) := by
          apply mul_le_mul_of_nonneg_left _ hn
          apply mul_le_mul hexp _ (by positivity) (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left hL (by positivity)
      _ = ‖a ξ‖ * (2 * Real.pi * sm ξ * Real.exp (-(2 * Real.pi * m * sm ξ))) := by ring
  let w : Hn F := fun _ => UpperHalfPlane.ofComplex (Complex.I * ((m / 2 : ℝ) : ℂ))
  have hw_im : ∀ v : InfinitePlace F, 0 < ((fun _ => Complex.I * ((m / 2 : ℝ) : ℂ)) v : ℂ).im := by
    intro v
    simp
    linarith
  have hnw : ∀ ξ, ‖a ξ * ez ξ w‖ = ‖a ξ‖ * Real.exp (-(Real.pi * m * sm ξ)) := by
    intro ξ
    have := ez_ofComplex ξ (fun _ => Complex.I * ((m / 2 : ℝ) : ℂ)) hw_im
    rw [norm_mul, this, Complex.norm_exp, re_lin]
    congr 2
    simp [sm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hsw : Summable (fun ξ => ‖a ξ * ez ξ w‖) := (summable_norm_iff.2 (hsum w).summable)
  have hu : Summable u := by
    refine Summable.of_nonneg_of_le (fun ξ => ?_) (fun ξ => ?_) (hsw.mul_left (2 / m))
    · by_cases ha : a ξ = 0
      · simp [u, ha]
      · have := hsm ξ ha
        positivity
    · by_cases ha : a ξ = 0
      · simp [u, ha]
      · rw [hnw ξ]
        have := mul_exp_neg_le_exp_half m (sm ξ) hm (hsm ξ ha)
        calc u ξ = ‖a ξ‖ * (2 * Real.pi * sm ξ * Real.exp (-(2 * Real.pi * m * sm ξ))) := rfl
          _ ≤ ‖a ξ‖ * ((2 / m) * Real.exp (-(Real.pi * m * sm ξ))) := mul_le_mul_of_nonneg_left this (norm_nonneg _)
          _ = 2 / m * (‖a ξ‖ * Real.exp (-(Real.pi * m * sm ξ))) := by ring
  have hf0 : Summable (fun ξ => g ξ z0) := by
    refine (hsum (fun v => UpperHalfPlane.ofComplex (z0 v))).summable.congr (fun ξ => ?_)
    simp only [g]
    rw [ez_ofComplex ξ z0 hz0']
  have hT := hasFDerivAt_tsum_of_isPreconnected hu hsopen hsconv.isPreconnected hderiv hbound hz0s hf0 hz0s
  have heq : (fun z : InfinitePlace F → ℂ => f (fun v => UpperHalfPlane.ofComplex (z v))) =ᶠ[nhds z0]
      (fun y => ∑' ξ, g ξ y) := by
    filter_upwards [hsopen.mem_nhds hz0s] with y hy
    rw [← (hsum (fun v => UpperHalfPlane.ofComplex (y v))).tsum_eq]
    apply tsum_congr
    intro ξ
    simp only [g]
    rw [ez_ofComplex ξ y (hpos_s y hy)]
  exact (hT.differentiableAt.congr_of_eventuallyEq heq).differentiableWithinAt

end GlobalTheory.HilbertThetaSeries.QHol
end
end

