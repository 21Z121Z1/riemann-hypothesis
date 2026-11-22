import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0002

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExtMapLiftOldOfIsWeightedHomogeneous
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace AddBlockData

variable {P : ArithVariety n} (D : AddBlockData P)

theorem extMap_comp_liftOld :
    D.extMap.comp D.liftOld.toRingHom =
      eval₂Hom (Int.castRingHom _) fun v : Coord n ↦ C (P.mkF (X v)) * X (some v.1) := by
  refine MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun v ↦ ?_)
  simp [extMap, liftOld, oldCoord, extVal]

theorem eval₂Hom_monomial_blockVal (d : Coord n →₀ ℕ) (r : ℤ) :
    eval₂Hom (Int.castRingHom (MvPolynomial (Option ι) P.FunField))
        (fun v : Coord n ↦ C (P.mkF (X v)) * X (some v.1)) (monomial d r) =
      C (P.mkF (monomial d r)) * ∏ k, X (some k) ^ (Finsupp.weight (coordDeg n) d k) := by
  rw [coe_eval₂Hom, eval₂_monomial, monomial_eq, Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow,
    weight_coordDeg_apply, Fintype.prod_sigma, Finset.prod_pow_eq_pow_sum]
  simp [mul_assoc]

theorem extMap_liftOld_of_isWeightedHomogeneous {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    D.extMap (D.liftOld f) = C (P.mkF f) * ∏ k, X (some k) ^ δ k := by
  have h : D.extMap (D.liftOld f) = eval₂Hom (Int.castRingHom (MvPolynomial (Option ι) P.FunField))
      (fun v : Coord n ↦ C (P.mkF (X v)) * X (some v.1)) f := by
    rw [← D.extMap_comp_liftOld]
    rfl
  rw [h]
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [eval₂Hom_monomial_blockVal, hf (mem_support_iff.mp hd)]

theorem evalCone_liftOld {F : Type*} [CommRing F] (w : Cone D.extSizes F) (f : MvPolynomial (Coord n) ℤ) :
    evalCone w (D.liftOld f) = evalCone (D.basePart₂ w) f := by
  simp only [evalCone, liftOld]
  rw [eval₂_rename]
  rfl

theorem liftOld_mem_extIdeal {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ P.ideal) :
    D.liftOld f ∈ D.extIdeal := by
  rw [extIdeal, RingHom.mem_ker]
  conv_lhs => rw [← sum_weightedHomogeneousComponent (coordDeg n) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
  rw [map_sum, map_sum]
  refine Finset.sum_eq_zero fun m _ ↦ ?_
  rw [D.extMap_liftOld_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous m f),
    (P.mkF_eq_zero_iff _).mpr (P.homogeneous f hf m), map_zero, zero_mul]

theorem chartMonomial_mem_of_not_isLive {c : (k : ι) → Fin (n k + 1)} (hc : ¬ P.IsLive c)
    {d : ι → ℕ} (hd : ∀ k, 1 ≤ d k) : chartMonomial c d ∈ P.ideal := by
  obtain ⟨k, hk⟩ : ∃ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∈ P.ideal := by
    simpa [ArithVariety.IsLive] using hc
  exact P.ideal.mem_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))
    (P.ideal.pow_mem_of_mem hk (d k) (hd k))

theorem IsFormSystem.cross_mem {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) (c c' : (k : ι) → Fin (n k + 1)) (j : Fin (D.size + 1)) :
    chartMonomial c' d * g c j - chartMonomial c d * g c' j ∈ P.ideal := by
  by_cases hc : P.IsLive c
  · by_cases hc' : P.IsLive c'
    · rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, hg.value c hc j, hg.value c' hc' j]
      ring
    · rw [hg.dead c' hc' j, mul_zero, sub_zero]
      exact P.ideal.mul_mem_right _ (chartMonomial_mem_of_not_isLive hc' hg.pos)
  · rw [hg.dead c hc j, mul_zero, zero_sub]
    exact P.ideal.neg_mem_iff.mpr (P.ideal.mul_mem_right _ (chartMonomial_mem_of_not_isLive hc hg.pos))

end AddBlockData

open AddBlockData in

theorem ConePoints.proof (hV : ChartVanishing.Statement) : ConePoints.Statement := by
  intro ι _ _ n P D d g hg
  have hom : ∀ c j, IsWeightedHomogeneous (coordDeg n) (g c j) (fun k ↦ (d k + D.deg k).toNat) := by
    intro c j
    obtain ⟨δ, hδ, hδk⟩ := hg.homog c j
    convert hδ using 1
    funext k
    rw [← hδk k, Int.toNat_natCast]
  have hX : ∀ i, D.extMap (X (D.newCoord i)) = C (D.elt i) * X none := fun i ↦ by
    simp [extMap, newCoord, extVal]
  have part1 : ∀ (c : (k : ι) → Fin (n k + 1)) (i j : Fin (D.size + 1)),
      D.liftOld (g c j) * X (D.newCoord i) - D.liftOld (g c i) * X (D.newCoord j) ∈ D.extIdeal := by
    intro c i j
    rw [extIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, hX, hX,
      D.extMap_liftOld_of_isWeightedHomogeneous (hom c j), D.extMap_liftOld_of_isWeightedHomogeneous (hom c i)]
    by_cases hc : P.IsLive c
    · rw [hg.value c hc j, hg.value c hc i]
      simp only [map_mul]
      ring
    · rw [hg.dead c hc j, hg.dead c hc i]
      simp
  refine ⟨part1, fun w hw ↦ ?_⟩
  set z := D.basePart₂ w with hz
  set z' := D.newPart w with hz'
  have hzP : z ∈ P.points ℂ :=
    ⟨fun k ↦ hw.1 (some k), fun f hf ↦ by
      rw [← D.evalCone_liftOld]
      exact hw.2 _ (D.liftOld_mem_extIdeal hf)⟩

  have rel : ∀ c i j, evalCone z (g c j) * z' i = evalCone z (g c i) * z' j := by
    intro c i j
    have h := hw.2 _ (part1 c i j)
    unfold evalCone at h
    rw [eval₂_sub, eval₂_mul, eval₂_mul, eval₂_X, eval₂_X] at h
    change evalCone w (D.liftOld (g c j)) * _ - evalCone w (D.liftOld (g c i)) * _ = 0 at h
    rw [evalCone_liftOld, evalCone_liftOld] at h
    rw [← sub_eq_zero]
    exact h

  have cross : ∀ c c' j, evalCone z (chartMonomial c' d) * evalCone z (g c j) =
      evalCone z (chartMonomial c d) * evalCone z (g c' j) := by
    intro c c' j
    have h := hzP.2 _ (hg.cross_mem D c c' j)
    rw [← sub_eq_zero]
    simpa [evalCone] using h

  have hne : ∀ k, ∃ i, z k i ≠ 0 := fun k ↦ Function.ne_iff.mp (hzP.1 k)
  choose c₀ hc₀ using hne
  have hm₀ : evalCone z (chartMonomial c₀ d) ≠ 0 := by
    simp only [evalCone, chartMonomial, eval₂_prod, eval₂_pow, eval₂_X]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc₀ k)
  obtain ⟨j₀, hj₀⟩ : ∃ j, evalCone z (g c₀ j) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hm₀ ((hV ι n P D d g hg z hzP c₀).mp h)
  have hz'₀ : z' j₀ ≠ 0 := by
    intro h0
    apply hw.1 none
    funext i
    have := rel c₀ i j₀
    rw [h0, mul_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hj₀
  refine ⟨hzP, z' j₀ * evalCone z (chartMonomial c₀ d) / evalCone z (g c₀ j₀),
    div_ne_zero (mul_ne_zero hz'₀ hm₀) hj₀, fun c hc j ↦ ?_⟩
  rw [eq_div_iff hc, div_mul_eq_mul_div, eq_div_iff hj₀]
  linear_combination evalCone z (chartMonomial c d) * rel c₀ j j₀ - z' j₀ * cross c c₀ j

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExtVal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ConePointsConverse.proof (hV : ChartVanishing.Statement) : ConePointsConverse.Statement := by
  intro ι _ _ n P D d g hg z hz c hm
  obtain ⟨j₀, hj₀⟩ : ∃ j, evalCone z (g c j) ≠ 0 := by
    by_contra h
    exact hm ((hV ι n P D d g hg z hz c).1 fun j ↦ by_contra fun hj ↦ h ⟨j, hj⟩)
  have hlive : P.IsLive c := by
    by_contra hl
    apply hj₀
    rw [hg.dead c hl j₀]
    simp [evalCone]

  let sub : Coord D.extSizes → MvPolynomial (Coord n) ℤ := fun v ↦ match v with
    | ⟨none, j⟩ => g c j
    | ⟨some k, i⟩ => X ⟨k, i⟩
  let Φ : MvPolynomial (Coord D.extSizes) ℤ →+* MvPolynomial (Coord n) ℤ :=
    eval₂Hom (Int.castRingHom _) sub
  set w := D.joinPt z fun j ↦ evalCone z (g c j) with hw
  have key1 : (eval₂Hom (Int.castRingHom ℂ) (fun v : Coord n ↦ z v.1 v.2)).comp Φ =
      eval₂Hom (Int.castRingHom ℂ) (fun v : Coord D.extSizes ↦ w v.1 v.2) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Φ]
    · rintro ⟨_ | k, i⟩
      · simp [Φ, sub, hw, AddBlockData.joinPt, evalCone]
      · simp [Φ, sub, hw, AddBlockData.joinPt]
  have key2 : P.mkF.comp Φ =
      (MvPolynomial.eval fun o : Option ι ↦ o.elim (P.mkF (chartMonomial c d)) fun _ ↦ 1).comp
        D.extMap := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Φ]
    · rintro ⟨_ | k, i⟩
      · simp only [RingHom.comp_apply, Φ, sub, AddBlockData.extMap, AddBlockData.extVal, coe_eval₂Hom,
          eval₂_X, eval_mul, eval_C, eval_X, Option.elim]
        exact (hg.value c hlive i).trans (mul_comm _ _)
      · simp [Φ, sub, AddBlockData.extMap, AddBlockData.extVal]
  refine ⟨?_, ?_⟩
  · rintro (_ | k)
    · intro h
      exact hj₀ (congrFun h j₀)
    · exact hz.1 k
  · intro F hF
    have h0 : P.mkF (Φ F) = 0 := by
      have := RingHom.congr_fun key2 F
      rw [RingHom.comp_apply, RingHom.comp_apply, (RingHom.mem_ker).1 hF, map_zero] at this
      exact this
    have hmem : Φ F ∈ P.ideal := (P.mkF_eq_zero_iff _).1 h0
    have h1 := RingHom.congr_fun key1 F
    have h2 : evalCone z (Φ F) = 0 := hz.2 _ hmem
    simp only [RingHom.comp_apply, coe_eval₂Hom] at h1
    simpa [evalCone, h1] using h2

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.FiniteTwistsDegreeFormOfFirst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial
open scoped ContDiff

noncomputable section

namespace SectionNorm

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}

theorem evalCone_liftOld (D : GroundTheory.Heights₂.Heights.AddBlockData P) (w : Cone D.extSizes ℂ)
    (f : MvPolynomial (Coord n) ℤ) : evalCone w (D.liftOld f) = evalCone (D.basePart₂ w) f := by
  simp only [evalCone, GroundTheory.Heights₂.Heights.AddBlockData.liftOld, eval₂_rename]
  rfl

theorem evalCone_newCoord_mul (D : GroundTheory.Heights₂.Heights.AddBlockData P) (w : Cone D.extSizes ℂ)
    (j : Fin (D.size + 1)) (f : MvPolynomial (Coord n) ℤ) :
    evalCone w (X (D.newCoord j) * D.liftOld f) = D.newPart w j * evalCone (D.basePart₂ w) f := by
  rw [← evalCone_liftOld]
  simp only [evalCone, eval₂_mul, eval₂_X]
  rfl

def lineB {D : AddBlockData P} (G : ChartForms D) (Γ : GenSystem P) (N : HermLine n)
    (hN : N.deg = D.deg) (H : HermLine D.dims) (hH : H.deg = AddBlockData.eNew)
    (hmet : ∀ w, BlockNonzero w → H.metric w = hPlus G Γ N w) : HermLine D.dims where
  deg := D.degB
  metric := hB G Γ N
  metric_pos w hw := by
    show 0 < hPlus G Γ N w / N.metric (AddBlockData.basePart₂ w)
    rw [← hmet w hw]
    exact div_pos (H.metric_pos w hw) (N.metric_pos _ fun k ↦ hw (some k))
  metric_smul c w hc hw := by
    have hw' : BlockNonzero (fun o i ↦ c o * w o i : Cone D.dims ℂ) := fun o h ↦
      hw o (funext fun i ↦ by simpa [hc o] using congrFun h i)
    show hPlus G Γ N (fun o i ↦ c o * w o i) / N.metric (AddBlockData.basePart₂ (fun o i ↦ c o * w o i)) =
      (∏ o, ‖c o‖ ^ D.degB o) * (hPlus G Γ N w / N.metric (AddBlockData.basePart₂ w))
    have hNs : N.metric (AddBlockData.basePart₂ (fun o i ↦ c o * w o i : Cone D.dims ℂ)) =
        (∏ k, ‖c (some k)‖ ^ N.deg k) * N.metric (AddBlockData.basePart₂ w) :=
      N.metric_smul (fun k ↦ c (some k)) (AddBlockData.basePart₂ w) (fun k ↦ hc _) (fun k ↦ hw _)
    have hNp : 0 < N.metric (AddBlockData.basePart₂ w) := N.metric_pos _ fun k ↦ hw (some k)
    have hp : 0 < ∏ k, ‖c (some k)‖ ^ D.deg k :=
      Finset.prod_pos fun k _ ↦ zpow_pos (norm_pos_iff.2 (hc _)) _
    rw [← hmet _ hw', ← hmet _ hw, H.metric_smul c w hc hw, hH, hNs, hN, Fintype.prod_option,
      Fintype.prod_option]
    simp only [AddBlockData.eNew, AddBlockData.degB, Option.elim, zpow_one, zpow_zero,
      Finset.prod_const_one, mul_one, zpow_neg, Finset.prod_inv_distrib]
    field_simp
  metric_smooth := by
    have hold : ContDiff ℝ ∞ (fun w : Cone D.dims ℂ ↦ (AddBlockData.basePart₂ w : Cone n ℂ)) :=
      contDiff_pi.2 fun k ↦ contDiff_pi.1 contDiff_id (some k)
    have h1 : ContDiffOn ℝ ∞ (fun w ↦ H.metric w / N.metric (AddBlockData.basePart₂ w))
        {w : Cone D.dims ℂ | BlockNonzero w} :=
      H.metric_smooth.div (N.metric_smooth.comp hold.contDiffOn fun w hw k ↦ hw (some k))
        fun w hw ↦ (N.metric_pos _ fun k ↦ hw (some k)).ne'
    refine h1.congr fun w hw ↦ ?_
    show hPlus G Γ N w / N.metric (AddBlockData.basePart₂ w) = _
    rw [hmet w hw]

theorem exists_lineB (hM : GroundTheory.Heights₂.Heights.ChartMetric.Statement) (D : AddBlockData P)
    (G : ChartForms D) (Γ : GenSystem P) (N : HermLine n) (hN : N.deg = D.deg) :
    ∃ B : HermLine D.dims, B.deg = D.degB ∧ B.metric = hB G Γ N := by
  obtain ⟨⟨H, hdeg, hmet, -⟩, -⟩ := hM ι n P (AddBlockData.toObjects D) N hN G.d G.g G.isFormSystem
    Γ.r Γ.f Γ.δ Γ.isHomogGenerators
  exact ⟨lineB G Γ N hN H hdeg hmet, rfl, rfl⟩

theorem kleimanNef_field_of_alt (h : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.SectionNorm.Statement) :
    GroundTheory.Heights₂.Heights.SectionNorm.Statement := by
  intro ι _ _ n P D N hN d g hg r G δ hG c j hnot w hw hz
  have hext : (AddBlockData.ofObjects D).ext = D.extIdeal := AddBlockEq.addBlockEquiv_extIdeal D
  have hpts : D.extPoints = conePoints (AddBlockData.ofObjects D).ext ℂ := AddBlockEq.extPoints_eq D
  have h1 := (h ι n P (AddBlockData.ofObjects D) (ChartForms.ofFormSystem hg)
    (GenSystem.ofIsHomogGenerators hG) N hN).2 c j (by rw [hext]; exact hnot) w
    (by rw [← hpts]; exact hw) hz
  rw [evalCone_newCoord_mul, evalCone_liftOld, norm_mul, div_div]
  exact h1

theorem finiteTwists_degree_form_of_first
    (hL : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n)
      (D : AddBlockData P) (G : ChartForms D) (Γ : GenSystem P) (N : HermLine n), N.deg = D.deg →
        ∃ B : HermLine D.dims, B.deg = D.degB ∧ B.metric = hB G Γ N)
    (h : GroundTheory.Heights₂.Heights.SectionNorm.Statement) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.SectionNorm.Statement := by
  intro ι _ _ n P D G Γ N hN
  refine ⟨hL ι n P D G Γ N hN, fun c j hnot w hw hz ↦ ?_⟩
  have hext : (AddBlockData.toObjects D).extIdeal = D.ext := AddBlockEq.addBlockEquiv_symm_extIdeal D
  have hpts : (AddBlockData.toObjects D).extPoints = conePoints D.ext ℂ :=
    AddBlockEq.addBlockEquiv_symm_conePoints D
  have h1 := h ι n P (AddBlockData.toObjects D) N hN G.d G.g G.isFormSystem Γ.r Γ.f Γ.δ
    Γ.isHomogGenerators c j (by rw [hext]; exact hnot) w (by rw [hpts]; exact hw) hz
  erw [evalCone_newCoord_mul, evalCone_liftOld] at h1
  rw [norm_mul, div_div] at h1
  exact h1

theorem equiv (hM : GroundTheory.Heights₂.Heights.ChartMetric.Statement) :
    GroundTheory.Heights₂.Heights.SectionNorm.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.SectionNorm.Statement :=
  ⟨finiteTwists_degree_form_of_first fun _ _ _ _ _ D G Γ N hN ↦ exists_lineB hM D G Γ N hN, kleimanNef_field_of_alt⟩

end SectionNorm

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.HilbDegreeBoundAltOfStatement
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

theorem LatticePointCount.log_error_le {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    (r : ℝ) * Real.log (2 * (1 + r * C)) ≤
      (1 + Real.log (2 * (1 + C)) / Real.log 2) * (((r : ℝ) + 1) * Real.log ((r : ℝ) + 1)) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrC : 0 ≤ (r : ℝ) * C := mul_nonneg (Nat.cast_nonneg r) hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL : Real.log 2 ≤ Real.log ((r : ℝ) + 1) := Real.log_le_log two_pos (by linarith)
  have hc : 0 ≤ Real.log (2 * (1 + C)) := Real.log_nonneg (by linarith)
  have hX0 : 0 ≤ Real.log (2 * (1 + r * C)) := Real.log_nonneg (by linarith)
  have hX : Real.log (2 * (1 + r * C)) ≤ Real.log (2 * (1 + C)) + Real.log ((r : ℝ) + 1) := by
    rw [← Real.log_mul (by linarith : (0 : ℝ) < 2 * (1 + C)).ne' (by positivity)]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hcL : Real.log (2 * (1 + C)) ≤
      Real.log (2 * (1 + C)) / Real.log 2 * Real.log ((r : ℝ) + 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hL hc
  have hK : Real.log (2 * (1 + r * C)) ≤
      (1 + Real.log (2 * (1 + C)) / Real.log 2) * Real.log ((r : ℝ) + 1) := by
    have e : (1 + Real.log (2 * (1 + C)) / Real.log 2) * Real.log ((r : ℝ) + 1) =
        Real.log ((r : ℝ) + 1) + Real.log (2 * (1 + C)) / Real.log 2 * Real.log ((r : ℝ) + 1) := by
      ring
    rw [e]
    linarith
  calc (r : ℝ) * Real.log (2 * (1 + r * C)) ≤ ((r : ℝ) + 1) * Real.log (2 * (1 + r * C)) :=
        mul_le_mul_of_nonneg_right (by linarith) hX0
    _ ≤ ((r : ℝ) + 1) * ((1 + Real.log (2 * (1 + C)) / Real.log 2) * Real.log ((r : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hK (by linarith)
    _ = (1 + Real.log (2 * (1 + C)) / Real.log 2) * (((r : ℝ) + 1) * Real.log ((r : ℝ) + 1)) := by
        ring

theorem LatticePointCount.hilbDegreeBound_alt_of_statement (hA : GroundTheory.Heights₂.Heights.LatticePointCount.Statement) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.LatticePointCount.Statement := by
  intro C hC
  refine ⟨1 + Real.log (2 * (1 + C)) / Real.log 2, ?_⟩
  intro E _ _ r b hb S hS hcl
  have hmem : ∀ x : E, x ∈ AddSubgroup.closure (Set.range b) ↔ x ∈ Submodule.span ℤ (Set.range b) :=
    fun x ↦ by rw [← Submodule.span_int_eq_addSubgroupClosure]; exact Submodule.mem_toAddSubgroup _
  have hspan : Submodule.span ℤ (S : Set E) = Submodule.span ℤ (Set.range b) :=
    Submodule.toAddSubgroup_injective (by
      rw [Submodule.span_int_eq_addSubgroupClosure, Submodule.span_int_eq_addSubgroupClosure, hcl])
  have hset : {x : E | x ∈ AddSubgroup.closure (Set.range b) ∧ ‖x‖ ≤ 1} =
      {x : E | x ∈ Submodule.span ℤ (Set.range b) ∧ ‖x‖ ≤ 1} := by
    ext x
    simp only [Set.mem_ofPred_eq, hmem]
  obtain ⟨hfin, hlog⟩ := hA E r b hb (S : Set E) C hC.le hS hspan
  have hnn : 0 ≤ gram b := by
    unfold gram
    exact (Matrix.posSemidef_gram ℝ b).det_nonneg
  have hg : -Real.log (Real.sqrt (gram b)) =
      -(1 / 2) * Real.log (Matrix.of fun i j ↦ @inner ℝ E _ (b i) (b j)).det := by
    rw [Real.log_sqrt hnn]
    unfold gram
    ring
  rw [hset]
  refine ⟨hfin, ?_⟩
  rw [hg]
  have := LatticePointCount.log_error_le hC.le r
  linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsSide
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

theorem SectionCycle.equiv :
    GroundTheory.Heights₂.Heights.SectionCycle.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.SectionCycle.Statement := by
  constructor
  · intro hA ι _ _ n P D G c j hg W
    have e : (AddBlockEq.split_model_to_place_model D).extIdeal = D.ext := AddBlockEq.addBlockEquiv_symm_extIdeal D
    have h := hA ι n P (AddBlockEq.split_model_to_place_model D) G.d G.g G.isFormSystem c j
      (by rw [e]; exact hg) W
    rw [e] at h
    exact h
  · intro hB ι _ _ n P D d g hfs c j hg W
    have e : (AddBlockEq.toIndefiniteRowSideFullHecke D).ext = D.extIdeal := AddBlockEq.addBlockEquiv_extIdeal D
    have h := hB ι n P (AddBlockEq.toIndefiniteRowSideFullHecke D) (ChartForms.ofFormSystem hfs) c j
      (by rw [e]; exact hg) W
    rw [e] at h
    exact h

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

theorem ChartVanishing.equiv :
    GroundTheory.Heights₂.Heights.ChartVanishing.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ChartVanishing.Statement := by
  constructor
  · intro h ι _ _ n P D G z hz c
    exact h ι n P (AddBlockData.toObjects D) G.d G.g G.isFormSystem z hz c
  · intro h ι _ _ n P D d g hg z hz c
    exact h ι n P (AddBlockData.ofObjects D) (ChartForms.ofFormSystem hg) z hz c

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

theorem ChartDenominatorAlt.equiv :
    GroundTheory.Heights₂.Heights.ChartDenominatorAlt.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ChartDenominatorAlt.Statement := by
  constructor
  · intro hA ι _ _ n P D G Γ
    obtain ⟨hpos, hsmooth⟩ :=
      hA ι n P (AddBlockData.toObjects D) G.d G.g G.isFormSystem Γ.r Γ.f Γ.δ Γ.isHomogGenerators
    rw [den_eq G Γ]
    exact ⟨hsmooth, hpos⟩
  · intro hB ι _ _ n P D d g h r f δ hf
    obtain ⟨hsmooth, hpos⟩ :=
      hB ι n P (AddBlockData.ofObjects D) (ChartForms.ofFormSystem h)
        (GenSystem.ofIsHomogGenerators hf)
    rw [den_ofFormSystem h hf]
    exact ⟨hpos, hsmooth⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

