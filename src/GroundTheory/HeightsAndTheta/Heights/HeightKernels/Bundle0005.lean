import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootsOfUnityDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RootsOfUnityDenseAlt

open Complex

theorem rootsOfUnity_infinite :
    {z : ℂ | ∃ k : ℕ, 0 < k ∧ z ^ k = 1}.Infinite := by
  have hprim : ∀ m : ℕ,
      IsPrimitiveRoot (exp (2 * Real.pi * I / ((m + 1 : ℕ) : ℂ))) (m + 1) :=
    fun m => Complex.isPrimitiveRoot_exp (m + 1) (Nat.succ_ne_zero m)
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℕ => exp (2 * Real.pi * I / ((m + 1 : ℕ) : ℂ))) ?_ ?_
  · intro a b hab
    have ha := hprim a
    have hb := hprim b
    simp only at hab
    rw [hab] at ha
    have := IsPrimitiveRoot.unique ha hb
    omega
  · intro m
    exact ⟨m + 1, Nat.succ_pos m, (hprim m).pow_eq_one⟩

end RootsOfUnityDenseAlt

theorem RootsOfUnityDense.proof : RootsOfUnityDense.Statement := by
  intro n P hP
  refine MvPolynomial.funext_set (p := P) (q := 0)
    (fun _ => {z : ℂ | ∃ k : ℕ, 0 < k ∧ z ^ k = 1})
    (fun _ => RootsOfUnityDenseAlt.rootsOfUnity_infinite) ?_
  intro x hx
  rw [map_zero]
  exact hP x fun i => hx i (Set.mem_univ i)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.RestCutBasic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KRest

open MvPolynomial

noncomputable section

theorem homogeneousComponent_mul_left {σ R : Type*} [CommRing R] {P : MvPolynomial σ R} {l : ℕ}
    (hP : P.IsHomogeneous l) (G : MvPolynomial σ R) (d : ℕ) :
    homogeneousComponent d (P * G) =
      if l ≤ d then P * homogeneousComponent (d - l) G else 0 := by
  conv_lhs => rw [← sum_homogeneousComponent G, Finset.mul_sum]
  rw [map_sum]
  have hterm : ∀ i, homogeneousComponent d (P * homogeneousComponent i G) =
      if d = l + i then P * homogeneousComponent i G else 0 := fun i =>
    homogeneousComponent_of_mem ((hP.mul (homogeneousComponent_isHomogeneous i G)))
  simp_rw [hterm]
  by_cases h : l ≤ d
  · rw [if_pos h]
    have h2 : ∀ i, (if d = l + i then P * homogeneousComponent i G else 0) =
        if d - l = i then P * homogeneousComponent i G else 0 := fun i => by
      split_ifs <;> first | rfl | (exfalso; omega)
    simp_rw [h2]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · rw [homogeneousComponent_eq_zero, mul_zero]
      simp only [Finset.mem_range] at hm
      omega
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun i _ => if_neg (by omega)

theorem prod_Ioi_eq_prod_ite {R : Type*} [CommMonoid R] {m : ℕ} (g : Fin m → Fin m → R) :
    ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, g i j =
      ∏ x : Fin m × Fin m, if x.1 < x.2 then g x.1 x.2 else 1 := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp

theorem det_rev_pow_eq_vandermondeOf {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) :
    (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ))).det = RestTerms.vandermondeOf v := by
  have h1 : (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ))).det =
      (Matrix.vandermonde (v ∘ Fin.rev)).det := by
    rw [← Matrix.det_submatrix_equiv_self Fin.revPerm
      (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ)))]
    congr 1
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.vandermonde_apply,
      Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]
    congr 1
    have := b.isLt
    omega
  rw [h1, Matrix.det_vandermonde, RestTerms.vandermondeOf, prod_Ioi_eq_prod_ite,
    prod_Ioi_eq_prod_ite]
  refine Fintype.prod_equiv ((Equiv.prodComm _ _).trans (Fin.revPerm.prodCongr Fin.revPerm)) _ _ ?_
  intro x
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
    Equiv.prodCongr_apply, Prod.map, Fin.revPerm_apply, Fin.rev_lt_rev, Function.comp_apply]

theorem sum_fin_val_mul_two (N : ℕ) : (∑ i : Fin N, (i : ℕ)) * 2 = N * (N - 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id_mul_two]

theorem sum_card_Ioi_mul_two (N : ℕ) :
    (∑ i : Fin N, (Finset.Ioi i).card) * 2 = N * (N - 1) := by
  rw [← sum_fin_val_mul_two N]
  congr 1
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  simp only [Fin.card_Ioi, Fin.revPerm_apply, Fin.val_rev]
  have := i.isLt
  omega

def psiPolyFun {σ : Type*} (ψ : ℝ →ₗ[ℚ] ℚ) (P : MvPolynomial σ ℝ) : MvPolynomial σ ℚ :=
  ∑ β ∈ P.support, monomial β (ψ (coeff β P))

theorem coeff_psiPolyFun {σ : Type*} (ψ : ℝ →ₗ[ℚ] ℚ) (P : MvPolynomial σ ℝ) (β : σ →₀ ℕ) :
    coeff β (psiPolyFun ψ P) = ψ (coeff β P) := by
  classical
  rw [psiPolyFun, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [mem_support_iff, not_not] at h
    rw [h, map_zero]

def psiPoly {σ : Type*} (ψ : ℝ →ₗ[ℚ] ℚ) : MvPolynomial σ ℝ →+ MvPolynomial σ ℚ :=
  AddMonoidHom.mk' (psiPolyFun ψ) fun P Q => by
    ext β
    simp only [coeff_psiPolyFun, coeff_add, map_add]

theorem coeff_psiPoly {σ : Type*} (ψ : ℝ →ₗ[ℚ] ℚ) (P : MvPolynomial σ ℝ) (β : σ →₀ ℕ) :
    coeff β (psiPoly ψ P) = ψ (coeff β P) :=
  coeff_psiPolyFun ψ P β

theorem psiPoly_map_mul {σ : Type*} (ψ : ℝ →ₗ[ℚ] ℚ) (A : MvPolynomial σ ℚ)
    (P : MvPolynomial σ ℝ) : psiPoly ψ (map (algebraMap ℚ ℝ) A * P) = A * psiPoly ψ P := by
  classical
  ext β
  rw [coeff_psiPoly, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map, coeff_psiPoly, ← Algebra.smul_def, ψ.map_smul, smul_eq_mul]

theorem eq_zero_of_forall_psi {t : ℝ} (h : ∀ ψ : ℝ →ₗ[ℚ] ℚ, ψ t = 0) : t = 0 :=
  (Module.forall_dual_apply_eq_zero_iff ℚ t).mp h

end

end KRest

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ShortVectors
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Metric

noncomputable section

namespace KShort

def cube (n : ℕ) (c : ℝ) : Set (EuclideanSpace ℝ (Fin n)) := {x | ∀ i, |x i| < c}

theorem cube_eq (n : ℕ) (c : ℝ) :
    cube n c = (WithLp.ofLp) ⁻¹' (Set.pi Set.univ fun _ : Fin n => Set.Ioo (-c) c) := by
  ext x; simp [cube, abs_lt]

theorem volume_cube (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    volume (cube n c) = ENNReal.ofReal ((2 * c) ^ n) := by
  rw [cube_eq, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
  simp only [sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by linarith)]
  ring_nf

theorem norm_lt_of_mem_cube {n : ℕ} (hn : 0 < n) {lam : ℝ} (hlam : 0 < lam)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ cube n (lam / √n)) : ‖x‖ < lam := by
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsq : (√(n : ℝ)) ^ 2 = n := Real.sq_sqrt (by positivity)
  have h1 : ∀ i, x i ^ 2 < (lam / √n) ^ 2 := fun i => by
    have := hx i
    have h0 : 0 ≤ |x i| := abs_nonneg _
    calc x i ^ 2 = |x i| ^ 2 := (sq_abs _).symm
      _ < (lam / √n) ^ 2 := by gcongr
  have hsum : ∑ i, x i ^ 2 < ∑ _i : Fin n, (lam / √n) ^ 2 :=
    Finset.sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun i _ => h1 i
  have hsum' : ∑ _i : Fin n, (lam / √n) ^ 2 = lam ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, div_pow, hsq, nsmul_eq_mul]
    field_simp
  rw [EuclideanSpace.norm_eq]
  rw [Real.sqrt_lt' hlam]
  simpa [Real.norm_eq_abs, sq_abs, hsum'] using hsum

theorem convex_cube (n : ℕ) (c : ℝ) : Convex ℝ (cube n c) := by
  intro x hx y hy a b ha hb hab i
  have hxi := hx i
  have hyi := hy i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  calc |a * x i + b * y i| ≤ |a * x i| + |b * y i| := abs_add_le _ _
    _ = a * |x i| + b * |y i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ < c := by
      rcases ha.lt_or_eq with ha' | ha'
      · calc a * |x i| + b * |y i| < a * c + b * c := by
              have : b * |y i| ≤ b * c := mul_le_mul_of_nonneg_left hyi.le hb
              have : a * |x i| < a * c := mul_lt_mul_of_pos_left hxi ha'
              linarith
          _ = c := by rw [← add_mul, hab, one_mul]
      · subst ha'
        simp only [zero_add] at hab
        subst hab
        simpa using hyi

end KShort

namespace KShort

variable {n : ℕ}

theorem pow_le_covolume (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] {lam : ℝ} (hlam : 0 < lam)
    (hmin : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖) :
    (lam / √n) ^ n ≤ ZLattice.covolume L := by
  set b := Module.Free.chooseBasis ℤ L
  set F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)
  have fund : IsAddFundamentalDomain L.toAddSubgroup F volume :=
    ZLattice.isAddFundamentalDomain b volume
  have hcov : ZLattice.covolume L = volume.real F :=
    ZLattice.covolume_eq_measure_fundamentalDomain L volume fund
  have hFfin : volume F ≠ ⊤ :=
    (Bornology.IsBounded.measure_lt_top (ZSpan.fundamentalDomain_isBounded _)).ne
  have hc : 0 ≤ lam / √n := by positivity
  have hle : volume (cube n (lam / √n)) ≤ volume F * 2 ^ finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    by_contra hlt
    push Not at hlt
    have : Countable L.toAddSubgroup := (inferInstance : Countable L)
    have hsymm : ∀ y ∈ cube n (lam / √n), -y ∈ cube n (lam / √n) := by
      intro y hy i
      have := hy i
      simpa [abs_neg] using this
    obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (L := L.toAddSubgroup) fund hsymm (convex_cube n _) hlt
    have h1 := norm_lt_of_mem_cube hn hlam hx
    have h2 := hmin (x : EuclideanSpace ℝ (Fin n)) x.2 (by
      intro h; apply hx0; exact Subtype.ext h)
    linarith
  rw [volume_cube n hc, finrank_euclideanSpace, Fintype.card_fin] at hle
  rw [← ENNReal.ofReal_toReal hFfin] at hle
  rw [show (2 : ENNReal) ^ n = ENNReal.ofReal (2 ^ n) by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp] at hle
  rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  rw [hcov, measureReal_def]
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  rw [mul_pow] at hle
  nlinarith

theorem exists_ne_zero (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] : ∃ v ∈ L, v ≠ 0 := by
  by_contra h
  push Not at h
  have hbot : Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin n))) = ⊥ := by
    rw [Submodule.span_eq_bot]; exact h
  rw [IsZLattice.span_top] at hbot
  have : (EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)) ∈ (⊥ : Submodule ℝ _) := by
    rw [← hbot]; trivial
  rw [Submodule.mem_bot] at this
  have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v ⟨0, hn⟩) this
  simp at this

theorem finite_ball (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] (r : ℝ) :
    {v | v ∈ L ∧ ‖v‖ ≤ r}.Finite := by
  have h := Metric.finite_isBounded_inter_isClosed (K := closedBall (0 : EuclideanSpace ℝ (Fin n)) r)
    (s := (L : Set (EuclideanSpace ℝ (Fin n)))) DiscreteTopology.isDiscrete isBounded_closedBall
    (by rw [← Submodule.coe_toAddSubgroup]; exact AddSubgroup.isClosed_of_discrete)
  refine h.subset ?_
  rintro v ⟨hv, hr⟩
  exact ⟨by simpa using hr, hv⟩

theorem exists_isLeast (hn : 0 < n) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ lam : ℝ, 0 < lam ∧ IsLeast {t | ∃ v ∈ L, v ≠ 0 ∧ t = ‖v‖} lam := by
  obtain ⟨v₀, hv₀, hv₀0⟩ := exists_ne_zero hn L
  have hfin : {v | v ∈ L ∧ ‖v‖ ≤ ‖v₀‖ ∧ v ≠ 0}.Finite :=
    (finite_ball L ‖v₀‖).subset fun v hv => ⟨hv.1, hv.2.1⟩
  have hne : hfin.toFinset.Nonempty := ⟨v₀, by simp [hv₀, hv₀0]⟩
  obtain ⟨w, hw, hwmin⟩ := hfin.toFinset.exists_min_image (fun v => ‖v‖) hne
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hw hwmin
  refine ⟨‖w‖, norm_pos_iff.2 hw.2.2, ⟨w, hw.1, hw.2.2, rfl⟩, ?_⟩
  rintro t ⟨v, hv, hv0, rfl⟩
  by_cases h : ‖v‖ ≤ ‖v₀‖
  · exact hwmin v ⟨hv, h, hv0⟩
  · push Not at h
    linarith [hw.2.1]

end KShort

namespace KShort

variable {n : ℕ}

theorem card_le (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin n))) {lam r : ℝ} (hlam : 0 < lam) (hr : lam ≤ r)
    (hmin : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖) :
    (({v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r}.ncard : ℕ) : ℝ) ≤ (3 * r / lam) ^ finrank ℝ U := by
  classical
  let _ : MeasurableSpace U := borel U
  have : BorelSpace U := ⟨rfl⟩
  set μ : Measure U := (Module.finBasis ℝ U).addHaar with hμ
  set a := finrank ℝ U with ha
  set T : Set U := {w | (w : EuclideanSpace ℝ (Fin n)) ∈ L ∧ ‖w‖ ≤ r} with hT
  have hTfin : T.Finite :=
    ((finite_ball L r).preimage Subtype.val_injective.injOn).subset fun w hw => ⟨hw.1, hw.2⟩
  have himage : Subtype.val '' T = {v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r} := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hw.1, w.2, hw.2⟩
    · rintro ⟨hL, hU, hr'⟩
      exact ⟨⟨v, hU⟩, ⟨hL, hr'⟩, rfl⟩
  rw [← himage, Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_eq_toFinset_card T hTfin]
  set s := hTfin.toFinset with hs
  have hl2 : 0 < lam / 2 := half_pos hlam
  have hdisj : Set.PairwiseDisjoint (s : Set U) fun w => ball w (lam / 2) := by
    intro w hw w' hw' hne
    apply ball_disjoint_ball
    rw [add_halves, dist_eq_norm]
    have hw1 : (w : EuclideanSpace ℝ (Fin n)) ∈ L := by
      simpa [hs, hT] using (Set.Finite.mem_toFinset hTfin).1 hw |>.1
    have hw2 : (w' : EuclideanSpace ℝ (Fin n)) ∈ L := by
      simpa [hs, hT] using (Set.Finite.mem_toFinset hTfin).1 hw' |>.1
    have hsub : ((w - w' : U) : EuclideanSpace ℝ (Fin n)) ∈ L := by
      rw [Submodule.coe_sub]; exact L.sub_mem hw1 hw2
    have hne0 : ((w - w' : U) : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
      intro h
      apply hne
      have : w - w' = 0 := Subtype.ext h
      exact sub_eq_zero.1 this
    have := hmin _ hsub hne0
    simpa using this
  have hsubset : (⋃ w ∈ s, ball w (lam / 2)) ⊆ ball (0 : U) (r + lam / 2) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨w, hw, hxw⟩ := hx
    have hwr : ‖w‖ ≤ r := ((Set.Finite.mem_toFinset hTfin).1 hw).2
    rw [mem_ball_zero_iff]
    rw [mem_ball] at hxw
    calc ‖x‖ ≤ ‖w‖ + dist x w := by
          rw [dist_eq_norm]
          calc ‖x‖ = ‖w + (x - w)‖ := by abel_nf
            _ ≤ ‖w‖ + ‖x - w‖ := norm_add_le _ _
      _ < r + lam / 2 := by linarith
  have hmeas := measure_biUnion_finset (μ := μ) hdisj fun w _ => measurableSet_ball
  have hle := measure_mono (μ := μ) hsubset
  rw [hmeas] at hle
  simp only [Measure.addHaar_ball_of_pos μ _ hl2, Finset.sum_const, nsmul_eq_mul] at hle
  rw [Measure.addHaar_ball_of_pos μ _ (by linarith : 0 < r + lam / 2)] at hle
  have hc0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hct : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [← mul_assoc] at hle
  have hle' := (ENNReal.mul_le_mul_iff_left hc0 hct).1 hle
  rw [show ((s.card : ℕ) : ENNReal) = ENNReal.ofReal (s.card : ℝ) by simp,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (pow_nonneg (by linarith) _)] at hle'
  have hpos : 0 < (lam / 2) ^ a := by positivity
  have hcard : (s.card : ℝ) ≤ ((r + lam / 2) / (lam / 2)) ^ a := by
    rw [div_pow, le_div_iff₀ hpos]; exact hle'
  refine hcard.trans (pow_le_pow_left₀ (div_nonneg (by linarith) hl2.le) ?_ a)
  rw [div_le_div_iff₀ hl2 hlam]
  nlinarith

end KShort

theorem ShortVectors.intersectionNumber_baseChange : ShortVectors.Statement := by
  intro n hn L _ _
  obtain ⟨lam, hlam, hleast⟩ := KShort.exists_isLeast hn L
  have hmin : ∀ v ∈ L, v ≠ 0 → lam ≤ ‖v‖ := fun v hv hv0 => hleast.2 ⟨v, hv, hv0, rfl⟩
  refine ⟨lam, hleast, KShort.pow_le_covolume hn L hlam hmin, ?_⟩
  intro U r hr
  have hfin : {v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r ∧ v ≠ 0}.Finite :=
    (KShort.finite_ball L r).subset fun v hv => ⟨hv.1, hv.2.2.1⟩
  refine ⟨hfin, ?_⟩
  have hcard := KShort.card_le L U hlam hr hmin
  have heq : {v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r} =
      insert 0 {v | v ∈ L ∧ v ∈ U ∧ ‖v‖ ≤ r ∧ v ≠ 0} := by
    ext v
    by_cases h : v = 0
    · subst h
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, true_or, iff_true]
      exact ⟨L.zero_mem, U.zero_mem, by simp; linarith⟩
    · simp [h]
  rw [heq, Set.ncard_insert_of_notMem (by simp) hfin] at hcard
  push_cast at hcard
  linarith

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def hermChartPot {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (y : Fin e → ℂ) : ℝ :=
  Real.log (Real.sqrt (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ
    (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ))).re)

def chartMass {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) : ℝ :=
  ∫ y : Fin e → ℂ, maDensity (fun _ : Fin e => hermChartPot M) y

def ChartMassInvariant.Statement : Prop :=
  ∀ (e : ℕ) (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef →
    chartMass M = chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)

example : (Matrix.diagonal ![(4 : ℂ), 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ).PosDef :=
  Matrix.posDef_diagonal_iff.mpr fun j => by fin_cases j <;> norm_num

example (e : ℕ) : (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ).PosDef := Matrix.PosDef.one

example (e : ℕ) (y : Fin e → ℂ) :
    hermChartPot (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) y =
      Real.log (Real.sqrt (star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)).re) := by
  simp [hermChartPot]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsInvertibleIdealIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def InvertibleIdealIndex.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : Subring L) (M : AddSubgroup L) (ι : Type) [Fintype ι]
    (a : ι → L),
    Module.Finite ℤ B →
    (∀ b ∈ B, ∀ z ∈ M, b * z ∈ M) →
    (∀ i, a i ∈ M) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * a i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i) →
      (Module.finrank ℚ L : ℝ) * Real.log (genIndex M B.toAddSubgroup) =
        (Module.finrank ℤ B : ℝ) *
          Real.log (genIndex (Submodule.span (𝓞 L) (Set.range a)).toAddSubgroup
            (1 : Submodule (𝓞 L) L).toAddSubgroup)

end

end GroundTheory.Heights₂.Heights
end

