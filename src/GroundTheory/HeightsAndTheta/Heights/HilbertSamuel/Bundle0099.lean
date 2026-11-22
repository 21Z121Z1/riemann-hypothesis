import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0092
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0073
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0064
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.FibreNormCharpolyFalse
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0093

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullFormsGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace PullFormsGeneric

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_mem (F : IntermediateField ℚ Ω) (w : (Σ k, ι k) → Ω) (hw : ∀ p, w p ∈ F) (f : MRing ι) :
    aeval w f ∈ F := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [aeval_C, algebraMap_int_eq, eq_intCast]; exact intCast_mem F a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p q hp => rw [map_mul, aeval_X]; exact mul_mem hp (hw q)

omit [CharZero Ω] in

theorem aeval_scale {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) (y : (Σ k, ι k) → Ω) (t : K → Ω) :
    aeval (fun p => y p * t p.1) g = aeval y g * ∏ k, t k ^ d k := by
  have h := congrArg (MvPolynomial.eval t) (ProjLine.mConeMap_eq_of_isMultiHomog y hg)
  rw [map_mul, eval_C, map_prod] at h
  simp only [map_pow, eval_X] at h
  rw [← h, mConeMap, aeval_def, aeval_def, eval₂_comp_left]
  congr 1
  · exact RingHom.ext_int _ _
  · funext p
    simp

theorem blockFnField_eq_top {y : (Σ k, ι k) → Ω} (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hB : Birational y) : blockFnField y = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hB x
  set t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
  have ht : ∏ k, t k ^ d k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (inv_ne_zero (hc k))
  have hw : ∀ p, y p * t p.1 ∈ blockFnField y := fun p =>
    IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, by simp [t, div_eq_mul_inv]⟩
  have hx : x = aeval (fun p => y p * t p.1) g / aeval (fun p => y p * t p.1) h := by
    rw [aeval_scale hg, aeval_scale hh, hgh, mul_div_mul_right _ _ ht, mul_div_cancel_right₀ _ hh0]
  rw [hx]
  exact div_mem (aeval_mem _ _ hw g) (aeval_mem _ _ hw h)

theorem trdeg_eq {y : (Σ k, ι k) → Ω} {D : ℕ} (hA : IsArithVar (mCoordIdeal y) (D + 1))
    (hB : Birational y) : Algebra.trdeg ℚ Ω = D := by
  obtain ⟨_, ⟨_, _, hrel⟩, _, hdim⟩ := hA
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hrel
  rw [CoordArithOfFnField.dim_eq y c hc] at hdim
  have h1 : (Algebra.trdeg ℤ (blockFnField y)).toENat = D := by
    generalize (Algebra.trdeg ℤ (blockFnField y)).toENat = n at hdim ⊢
    induction n using ENat.recTopCoe with
    | top =>
      exfalso
      simp only [top_add] at hdim
      norm_cast at hdim
    | coe n =>
      norm_cast at hdim ⊢
      omega
  rw [Cardinal.toENat_eq_natCast] at h1
  have hE : blockFnField y ≃ₐ[ℤ] Ω :=
    ((IntermediateField.equivOfEq (blockFnField_eq_top c hc hB)).trans
      IntermediateField.topEquiv).toRingEquiv.toIntAlgEquiv
  have h2 : Algebra.trdeg ℤ Ω = D := by rw [← hE.trdeg_eq]; convert h1
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  rw [← h2, ← trdeg_add_eq ℤ ℚ (A := Ω), trdeg_eq_zero (R := ℤ) (A := ℚ), zero_add]

omit [CharZero Ω] in

theorem exists_ne_zero {y : (Σ k, ι k) → Ω} {D : ℕ} {e : K → ℕ} {L : Fin (D + 1) → MRing ι}
    (hA : IsArithVar (mCoordIdeal y) (D + 1)) (hL : ∀ j, IsMultiHomog (L j) e)
    (hz : ∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) :
    ∃ j, aeval y (L j) ≠ 0 := by
  have hne : ¬ (⊤ : Ideal (MRing ι)) ≤ mCoordIdeal y := fun h =>
    (RingHom.ker_isPrime (mConeMap y)).ne_top (top_le_iff.mp h)
  obtain ⟨z, hzP, -⟩ := exists_mcPts_not_mem_mcPts hA hne
  obtain ⟨j, hj⟩ := hz z hzP
  refine ⟨j, fun h0 => hj (hzP.2 _ ?_)⟩
  change mConeMap y (L j) = 0
  rw [ProjLine.mConeMap_eq_of_isMultiHomog y (hL j), h0, map_zero, zero_mul]

def dehom {D : ℕ} (j₀ : Fin (D + 1)) (F : MvPolynomial (Fin (D + 1)) ℚ) : MvPolynomial {i // i ≠ j₀} ℚ :=
  bind₁ (fun i => if h : i = j₀ then 1 else X ⟨i, h⟩) F

omit [Field Ω] [CharZero Ω] in
theorem aeval_dehom {A : Type} [CommRing A] [Algebra ℚ A] {D : ℕ} (j₀ : Fin (D + 1))
    (F : MvPolynomial (Fin (D + 1)) ℚ) (u : {i // i ≠ j₀} → A) :
    aeval u (dehom j₀ F) = aeval (fun i => if h : i = j₀ then 1 else u ⟨i, h⟩) F := by
  rw [dehom, aeval_bind₁]
  refine congrArg (fun f => aeval f F) (funext fun i => ?_)
  split_ifs <;> simp

end PullFormsGeneric

open PullFormsGeneric in

theorem PullFormsGeneric.proof (hR : PullRatiosAlgebraic.Statement) : PullFormsGeneric.Statement := by
  intro K _ ι _ Ω _ _ y D e L hA hB he hL hz d F hF h0
  classical
  obtain ⟨j₀, hj₀⟩ := exists_ne_zero hA hL hz
  set a := aeval y (L j₀)
  set r : {i // i ≠ j₀} → Ω := fun i => aeval y (L i.1) / a

  have hP : pullField y L = IntermediateField.adjoin ℚ (Set.range r) := by
    have hw : ∀ i, aeval y (L i) / a ∈ IntermediateField.adjoin ℚ (Set.range r) := by
      intro i
      by_cases h : i = j₀
      · subst h; rw [div_self hj₀]; exact one_mem _
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨i, h⟩, rfl⟩
    apply le_antisymm
    · rw [pullField, IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, j, hj, rfl⟩
      rw [← div_div_div_cancel_right₀ hj₀]
      exact div_mem (hw i) (hw j)
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin _ _ ⟨i.1, j₀, hj₀, rfl⟩

  obtain ⟨_, ⟨_, _, hrel⟩, _, _⟩ := hA
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hrel
  have hrel' : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => ⟨c k, hc k⟩
  have halg : Algebra.IsAlgebraic (Algebra.adjoin ℚ (Set.range r)) Ω := by
    refine ⟨fun x => IntermediateField.isAlgebraic_adjoin_iff.mp ?_⟩
    have hle : blockFnField y ≤
        (algebraicClosure (IntermediateField.adjoin ℚ (Set.range r)) Ω).restrictScalars ℚ := by
      rw [blockFnField, IntermediateField.adjoin_le_iff]
      rintro _ ⟨p, q, hpq, rfl⟩
      refine (IntermediateField.mem_restrictScalars _).mpr (mem_algebraicClosure_iff.mpr ?_)
      have := hR K ι Ω y D e L hrel' he hL hz p q hpq
      rwa [hP] at this
    have hx := hle ((blockFnField_eq_top c hc hB).symm ▸ IntermediateField.mem_top : x ∈ blockFnField y)
    exact mem_algebraicClosure_iff.mp ((IntermediateField.mem_restrictScalars _).mp hx)

  have hcard : Cardinal.mk {i : Fin (D + 1) // i ≠ j₀} ≤ Algebra.trdeg ℚ Ω := by
    rw [trdeg_eq ⟨‹_›, ⟨‹_›, ‹_›, hrel⟩, ‹_›, ‹_›⟩ hB, Cardinal.mk_fintype]
    norm_cast
    simp [Fintype.card_subtype_compl]
  have hind : AlgebraicIndependent ℚ r :=
    (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℚ r hcard).1

  have hw : (fun i => if h : i = j₀ then (1 : Ω) else r ⟨i, h⟩) = fun i => aeval y (L i) / a := by
    funext i
    split_ifs with h
    · subst h; exact (div_self hj₀).symm
    · rfl
  have hr0 : aeval r (dehom j₀ F) = 0 := by
    rw [aeval_dehom, hw]
    have h1 := FibreNormCharpoly.aeval_mul_of_isHomogeneous hF a (fun i => aeval y (L i) / a)
    simp only [mul_div_cancel₀ _ hj₀] at h1
    rw [h0] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero _ hj₀)
  have hG : dehom j₀ F = 0 := hind.eq_zero_of_aeval_eq_zero _ hr0

  have hFX : F * X j₀ = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [map_mul, eval_X, map_zero]
    by_cases hx : x j₀ = 0
    · rw [hx, mul_zero]
    · have h1 := FibreNormCharpoly.aeval_mul_of_isHomogeneous (Ω := ℚ) hF (x j₀) (fun i => x i / x j₀)
      have h2 := aeval_dehom j₀ F (fun i => x i.1 / x j₀)
      have hw' : (fun i => if h : i = j₀ then (1 : ℚ) else x i / x j₀) = fun i => x i / x j₀ := by
        funext i
        split_ifs with h
        · subst h; exact (div_self hx).symm
        · rfl
      rw [hG, map_zero, hw'] at h2
      have e1 : eval x F = x j₀ ^ d * eval (fun i => x i / x j₀) F := by
        have hs : (fun j => x j₀ * (x j / x j₀)) = x := funext fun j => mul_div_cancel₀ _ hx
        rw [hs] at h1
        rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval]
        exact h1
      have e2 : eval (fun i => x i / x j₀) F = 0 := by
        rw [← coe_aeval_eq_eval]
        exact h2.symm
      rw [e1, e2, mul_zero, zero_mul]
  exact (mul_eq_zero.mp hFX).resolve_right (X_ne_zero _)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullSectionIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace PullSectionIntegral

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_scale_of_isMultiHomog (y : (Σ k, ι k) → Ω) (t : K → Ω) {f : MRing ι} {e : K → ℕ}
    (hf : IsMultiHomog f e) :
    aeval (fun p => t p.1 * y p) f = (∏ k, t k ^ e k) * aeval y f := by
  simp only [aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hpow : ∏ p : Σ k, ι k, t p.1 ^ d p = ∏ k, t k ^ e k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, t k ^ d ⟨k, i⟩ = t k ^ e k
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  have hsplit : ∏ p, (t p.1 * y p) ^ d p = (∏ p : Σ k, ι k, t p.1 ^ d p) * ∏ p, y p ^ d p := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p _ => mul_pow _ _ _
  rw [hsplit, hpow]
  ring

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem eval_mConeMap (y : (Σ k, ι k) → Ω) (t : K → Ω) (f : MRing ι) :
    eval t (mConeMap y f) = aeval (fun p => t p.1 * y p) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp]
    simp [mConeMap, mul_comm]

theorem aeval_scale_eq_zero {y : (Σ k, ι k) → Ω} (t : K → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    aeval (fun p => t p.1 * y p) f = 0 := by
  rw [← eval_mConeMap, show mConeMap y f = 0 from hf, map_zero]

theorem exists_sum_eq_one [CharZero Ω] (P : Ideal (MRing ι)) (y' : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (hc : ∀ k, y' ⟨k, c k⟩ = 1) (hP : ∀ f ∈ P, aeval y' f = 0) {n : ℕ} (L : Fin n → MRing ι)
    (hL : ∀ z ∈ mcPts P, ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) :
    ∃ b : Fin n → MvPolynomial (Σ k, ι k) ℚ, ∑ i, aeval y' (b i) * aeval y' (L i) = 1 := by
  classical
  set φ : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω := aeval y'
  let Lq : Fin n → MvPolynomial (Σ k, ι k) ℚ := fun i => map (algebraMap ℤ ℚ) (L i)
  have hLq : ∀ i, φ (Lq i) = aeval y' (L i) := fun i => aeval_map_algebraMap ℚ y' (L i)
  let J : Ideal (MvPolynomial (Σ k, ι k) ℚ) := RingHom.ker φ ⊔ Ideal.span (Set.range Lq)
  by_cases hJ : J = ⊤
  · have h1 : (1 : MvPolynomial (Σ k, ι k) ℚ) ∈ J := hJ ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
    obtain ⟨β, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hb
    refine ⟨β, ?_⟩
    have := congrArg φ hab
    rw [map_add, show φ a = 0 from ha, zero_add, map_sum, map_one] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hLq]
  · exfalso
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
    let := Ideal.Quotient.field m
    have : Algebra.FiniteType ℚ (MvPolynomial (Σ k, ι k) ℚ ⧸ m) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ m)
        (Ideal.Quotient.mkₐ_surjective ℚ m)
    have := finite_of_finite_type_of_isJacobsonRing ℚ (MvPolynomial (Σ k, ι k) ℚ ⧸ m)
    let ψ : (MvPolynomial (Σ k, ι k) ℚ ⧸ m) →ₐ[ℚ] ℂ := IsAlgClosed.lift
    let z : (Σ k, ι k) → ℂ := fun p => ψ (Ideal.Quotient.mk m (X p))
    have hz : ∀ g : MvPolynomial (Σ k, ι k) ℚ, ψ (Ideal.Quotient.mk m g) = aeval z g := by
      intro g
      have : (ψ.comp (Ideal.Quotient.mkₐ ℚ m)) = aeval z := by
        ext p; simp [z]
      exact congrArg (fun F => F g) this
    have hzZ : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) =
        ψ (Ideal.Quotient.mk m (map (algebraMap ℤ ℚ) f)) := by
      intro f
      rw [hz, aeval_map_algebraMap, eval_map, aeval_def, algebraMap_int_eq]
    have hker : ∀ g ∈ RingHom.ker φ, Ideal.Quotient.mk m g = 0 := fun g hg =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (hJm (Ideal.mem_sup_left hg))
    have hzP : z ∈ mcPts P := by
      refine ⟨fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩
      · have hX : (X ⟨k, c k⟩ - 1 : MvPolynomial (Σ k, ι k) ℚ) ∈ RingHom.ker φ := by
          simp [RingHom.mem_ker, φ, hc k]
        have := hker _ hX
        rw [map_sub, map_one, sub_eq_zero] at this
        simp [z, this]
      · have hφf : φ (map (algebraMap ℤ ℚ) f) = 0 := by
          rw [show φ (map (algebraMap ℤ ℚ) f) = aeval y' f from aeval_map_algebraMap ℚ y' f]
          exact hP f hf
        rw [hzZ, hker _ (RingHom.mem_ker.mpr hφf), map_zero]
    obtain ⟨j, hj⟩ := hL z hzP
    apply hj
    rw [hzZ, Ideal.Quotient.eq_zero_iff_mem.mpr (hJm (Ideal.mem_sup_right
      (Ideal.subset_span ⟨j, rfl⟩))), map_zero]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_mem_of_forall [CharZero Ω] (V : Subring Ω) (hQ : ∀ r : ℚ, algebraMap ℚ Ω r ∈ V)
    (y' : (Σ k, ι k) → Ω) (hy : ∀ p, y' p ∈ V) (b : MvPolynomial (Σ k, ι k) ℚ) : aeval y' b ∈ V := by
  induction b using MvPolynomial.induction_on with
  | C a => simpa using hQ a
  | add p q hp hq => rw [map_add]; exact V.add_mem hp hq
  | mul_X p i hp => rw [map_mul, aeval_X]; exact V.mul_mem hp (hy i)

theorem proof : PullSectionIntegral.Statement := by
  intro K _ ι _ Ω _ _ y D e L q hV _ he hL hzero τ s hs j hj
  classical
  set A := Algebra.adjoin ℚ (Set.range fun i => aeval y (L i) / aeval y (L j))
  set R := (integralClosure A Ω).toSubring
  have : IsIntegrallyClosedIn R Ω := inferInstanceAs (IsIntegrallyClosedIn (integralClosure A Ω) Ω)
  show s / aeval y (L j) ^ (q * τ) ∈ R
  by_contra hnot
  obtain ⟨V, hRV, htV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hnot
  have hAV : ∀ x ∈ A, x ∈ V := fun x hx =>
    hRV (isIntegral_algebraMap (R := A) (A := Ω) (x := ⟨x, hx⟩))
  have hQ : ∀ r : ℚ, algebraMap ℚ Ω r ∈ V.toSubring := fun r => hAV _ (A.algebraMap_mem r)

  have hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hV.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap y (X ⟨k, i⟩) = 0
    simp [mConeMap, h0]
  have hmax : ∀ k, ∃ c : ι k, ∀ i, V.valuation (y ⟨k, i⟩) ≤ V.valuation (y ⟨k, c⟩) := by
    intro k
    obtain ⟨i0, -⟩ := hrel k
    obtain ⟨c, -, hc⟩ := Finset.exists_max_image Finset.univ (fun i => V.valuation (y ⟨k, i⟩))
      ⟨i0, Finset.mem_univ _⟩
    exact ⟨c, fun i => hc i (Finset.mem_univ _)⟩
  choose c hc using hmax
  have hc0 : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    obtain ⟨i0, hi0⟩ := hrel k
    have := hc k i0
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi0 this
  have hratio : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ V := by
    intro p
    rw [← V.valuation_le_one_iff, map_div₀]
    exact div_le_one_of_le₀ (hc p.1 p.2) zero_le

  set M : Ω := ∏ k, y ⟨k, c k⟩ ^ e k
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc0 k)
  have hchart : (chartRingZ y c : Set Ω) ⊆ V := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hratio p
    | algebraMap r => simp
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  have : IsIntegrallyClosedIn V.toSubring Ω := inferInstanceAs (IsIntegrallyClosedIn V Ω)
  have hxV : s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) ∈ V.toSubring :=
    (Subring.integralClosure_le_iff (R := chartRingZ y c) (T := V.toSubring)).mpr
      (fun r => hchart r.2) (hs c hc0)
  have hprod : ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) = (M ^ (q * τ))⁻¹ := by
    rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [show -((τ : ℤ) * ((q * e k : ℕ) : ℤ)) = -((e k * (q * τ) : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast, pow_mul]
  rw [hprod] at hxV

  set t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
  have hP' : ∀ f ∈ mCoordIdeal y, aeval (fun p => t p.1 * y p) f = 0 := fun f hf =>
    aeval_scale_eq_zero t hf
  obtain ⟨b, hb⟩ := exists_sum_eq_one (mCoordIdeal y) (fun p => t p.1 * y p) c
    (fun k => inv_mul_cancel₀ (hc0 k)) hP' L hzero
  have hLt : ∀ i, aeval (fun p => t p.1 * y p) (L i) = M⁻¹ * aeval y (L i) := by
    intro i
    rw [aeval_scale_of_isMultiHomog y t (hL i)]
    simp [t, M, Finset.prod_inv_distrib, inv_pow]
  have hratio' : ∀ p : Σ k, ι k, t p.1 * y p ∈ V := fun p => by
    simpa [t, div_eq_inv_mul] using hratio p
  have hMV : M / aeval y (L j) ∈ V := by
    have hsum : M / aeval y (L j) =
        ∑ i, aeval (fun p => t p.1 * y p) (b i) * (aeval y (L i) / aeval y (L j)) := by
      have := congrArg (fun w => w * (M / aeval y (L j))) hb
      simp only [one_mul, Finset.sum_mul, hLt] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [hsum]
    refine sum_mem fun i _ => mul_mem ?_ ?_
    · exact aeval_mem_of_forall V.toSubring hQ _ (fun p => hratio' p) (b i)
    · exact hAV _ (Algebra.subset_adjoin ⟨i, rfl⟩)
  apply htV
  have hMn : M ^ (q * τ) ≠ 0 := pow_ne_zero _ hM0
  have : s / aeval y (L j) ^ (q * τ) = s * (M ^ (q * τ))⁻¹ * (M / aeval y (L j)) ^ (q * τ) := by
    rw [div_pow, mul_assoc, ← mul_div_assoc, inv_mul_cancel₀ hMn, mul_one_div]
  rw [this]
  exact mul_mem hxV (pow_mem hMV _)

end PullSectionIntegral

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

