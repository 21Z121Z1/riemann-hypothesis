import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ContAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.KvSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0002

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.BandHS
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.bandHS :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ → ∀ (φ : ℝ → ℂ) (a b : ℝ), Continuous φ → HasCompactSupport φ → a ≤ b →
      IsHilbertSchmidt (X ∘L M.P (Ioc a b)) ∧ hsNorm (X ∘L M.P (Ioc a b)) ^ 2 = (b - a) * ∑ i, ‖kv κ (stdOrthonormalBasis ℂ V i)‖ ^ 2 ∧
      IsHilbertSchmidt (M.F.av φ ∘L M.P (Ioc a b)) ∧
      hsNorm (M.F.av φ ∘L M.P (Ioc a b)) ^ 2 = (b - a) * (Module.finrank ℂ V * ∫ x, ‖φ x‖ ^ 2) ∧
      trace (ContinuousLinearMap.adjoint (M.F.av φ ∘L M.P (Ioc a b)) ∘L (X ∘L M.P (Ioc a b))) =
        ∫ y in a..b, ∑ i, M.cor (fun x => φ (-x)) (stdOrthonormalBasis ℂ V i) (kv κ (stdOrthonormalBasis ℂ V i)) (2 * y) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X κ hk hX φ a b h1 h2 hab
  have cU : ∀ (F : Flow H) (A : V →L[ℂ] H), Continuous fun y => F.U y ∘L A := fun F A =>
    continuous_clm_apply.2 fun e => F.cont (A e)
  let A : V →L[ℂ] H := (M.J'.toContinuousLinearEquiv : L W →L[ℂ] H) ∘L kv κ
  let A' : V →L[ℂ] H := (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) ∘L sv V fun x => φ (-x)
  have pa : ∀ u, M.P (Ioc a b) (M.J u) = M.J (cut V (Ioc a b) u) := fun u => congrArg M.J (congrArg _ (M.J.symm_apply_apply u))
  obtain ⟨s1, s2, s3⟩ := scalSpec (V := V) φ h1 h2
  have hi : Integrable φ := h1.integrable_of_hasCompactSupport h2
  have y1 : ∀ u : L V, (X ∘L M.P (Ioc a b)) (M.J u) = ∫ y in Ioc a b, (M.F.U y ∘L A) (u y) := fun u => by
    obtain ⟨i1, i2⟩ := (kvSpec κ hk).2 a b u
    rw [ContinuousLinearMap.comp_apply, pa, hX, i2]
    refine ((M.J'.toContinuousLinearEquiv : L W →L[ℂ] H).integral_comp_comm i1).symm.trans ?_
    exact integral_congr_ae (Eventually.of_forall fun y => (M.hJ' y _).symm)
  have y2 : ∀ u : L V, (M.F.av φ ∘L M.P (Ioc a b)) (M.J u) = ∫ y in Ioc a b, (M.F.rev.U y ∘L A') (u y) := fun u => by
    obtain ⟨i1, i2⟩ := (kvSpec _ s1).2 a b u
    have c := ((avSpec (shF V)).2.2.2 φ hi).2.2.2.2 M.F (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) fun t h => (M.hJ t h).symm
    have c' : ∀ v, M.F.av φ (M.J v) = M.J ((shF V).av φ v) := fun v => (DFunLike.congr_fun c v).symm
    rw [ContinuousLinearMap.comp_apply, pa, c', s2, i2]
    refine ((M.J.toContinuousLinearEquiv : L V →L[ℂ] H).integral_comp_comm i1).symm.trans ?_
    rw [s3]
    exact integral_congr_ae (Eventually.of_forall fun y => (M.hJ (-y) _).symm)
  obtain ⟨k1, k2, k3⟩ := kp M.J a b _ _ _ _ hab (cU M.F A) (cU M.F.rev A') y1 y2
  obtain ⟨k4, k5, -⟩ := kp M.J a b _ _ _ _ hab (cU M.F.rev A') (cU M.F.rev A') y2 y2
  refine ⟨k1, ?_, k4, ?_, ?_⟩
  · rw [k2]
    simp [M.F.norm, A]
  · rw [k5]
    have m2 : MemLp (fun x => φ (-x)) 2 volume :=
      (h1.comp continuous_neg).memLp_of_hasCompactSupport (h2.comp_homeomorph (Homeomorph.neg ℝ))
    have n : ∀ i, ‖(M.F.rev.U 0 ∘L A') (stdOrthonormalBasis ℂ V i)‖ ^ 2 = ∫ x, ‖φ x‖ ^ 2 := fun i => by
      show ‖M.F.rev.U 0 (M.J (sv V (fun x => φ (-x)) (stdOrthonormalBasis ℂ V i)))‖ ^ 2 = _
      rw [Flow.norm, M.J.norm_map, ((svSpec (V := V)).1 _ m2 _).2, (stdOrthonormalBasis ℂ V).orthonormal.1,
        integral_neg_eq_self fun x => ‖φ x‖ ^ 2]
      simp
    simp only [ContinuousLinearMap.comp_apply, Flow.norm] at n ⊢
    simp [n, mul_left_comm]
  · rw [k3]
    refine intervalIntegral.integral_congr fun y _ => Finset.sum_congr rfl fun i _ => ?_
    show ⟪M.F.U (-y) (M.J _), M.F.U y (M.J' _)⟫_ℂ = ⟪M.J _, M.F.U (2 * y) (M.J' _)⟫_ℂ
    rw [← (avSpec M.F).1, ContinuousLinearMap.adjoint_inner_left, ← M.F.add, two_mul]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CarLaws
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.carLaws :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ →
      (∀ t h, X (M.F.U t h) = M.F.U (-t) (X h)) ∧ M.swap.Carries (ContinuousLinearMap.adjoint X) (sharp κ) ∧
      ∀ ρ T : ℝ, (∀ t, ρ < |t| → κ t = 0) → M.P' (Ioi (T + ρ)) ∘L X ∘L (1 - M.P (Ioi T)) = 0 := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X κ hk hX
  obtain ⟨c1, c2, -⟩ := convLaws κ hk
  refine ⟨fun t h => ?_, fun v => ?_, fun ρ T hρ => ?_⟩
  · obtain ⟨u, rfl⟩ := M.J.surjective h
    rw [M.hJ, hX, hX, M.hJ', neg_neg]
    exact congrArg M.J' (DFunLike.congr_fun (c1 t) u)
  · refine ext_inner_left ℂ fun h => ?_
    obtain ⟨u, rfl⟩ := M.J.surjective h
    show ⟪M.J u, ContinuousLinearMap.adjoint X (M.J' v)⟫_ℂ = ⟪M.J u, M.J (conv (sharp κ) v)⟫_ℂ
    rw [ContinuousLinearMap.adjoint_inner_right, hX, M.J'.inner_map_map, M.J.inner_map_map, ← (convAdj κ hk).2.1,
      ContinuousLinearMap.adjoint_inner_right]
  · ext h
    obtain ⟨u, rfl⟩ := M.J.surjective h
    have e : (1 - M.P (Ioi T)) (M.J u) = M.J (cut V (Iic T) u) := by
      have h1 := (cutLaws (V := V) (Iic T) (Ioi T) measurableSet_Iic measurableSet_Ioi)
      have h2 := h1.2.2.1 (Iic_disjoint_Ioi le_rfl)
      rw [Iic_union_Ioi, h1.2.2.2.1] at h2
      have h3 : u = cut V (Iic T) u + cut V (Ioi T) u := DFunLike.congr_fun h2 u
      simp only [Sc.P, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply]
      show M.J u - M.J (cut V (Ioi T) (M.J.symm (M.J u))) = _
      rw [M.J.symm_apply_apply, ← map_sub, sub_eq_of_eq_add h3]
    show M.P' (Ioi (T + ρ)) (X ((1 - M.P (Ioi T)) (M.J u))) = 0
    rw [e, hX]
    show M.J' (cut W (Ioi (T + ρ)) (M.J'.symm (M.J' _))) = 0
    rw [M.J'.symm_apply_apply]
    have := DFunLike.congr_fun (c2 ρ T hρ) u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at this
    rw [this, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CorLim
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.corLim :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (N : W →ₗ[ℂ] V), M.IsN N → ∀ (φ : ℝ → ℂ) (e : V) (p : L W) (c : ℝ), Continuous φ → HasCompactSupport φ → Bdd p →
      Continuous (M.cor φ e p) ∧ Tendsto (fun a => ∫ s in (c - a)..(c + a), M.cor φ e p s) atTop (𝓝 (conj (∫ x, φ x) * ⟪e, N (∫ x, p x)⟫_ℂ)) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M N hN φ e p c h1 h2 hp
  have hc : ∀ a b : H, Continuous fun s => ⟪a, M.F.U s b⟫_ℂ := fun a b => continuous_const.inner (M.F.cont b)
  refine ⟨hc _ _, ?_⟩
  have t1 := (cobLaws M.F).2.2.2.2.2.2.1 (projLaws M).1 _ (M.J (sv V φ e)) c (nAll M N hN p hp)
  have t2 := corOne φ e (N (∫ x, p x)) c h1 h2
  have t3 := t1.add t2
  rw [zero_add] at t3
  refine t3.congr fun a => ?_
  have e1 : ∀ s, ⟪sv V φ e, sh V s (one V (N (∫ x, p x)))⟫_ℂ = ⟪M.J (sv V φ e), M.F.U s (M.J (one V (N (∫ x, p x))))⟫_ℂ :=
    fun s => by rw [M.hJ, M.J.inner_map_map]
  simp only [e1]
  rw [← intervalIntegral.integral_add ((hc _ _).intervalIntegrable _ _) ((hc _ _).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [Sc.cor, map_sub, inner_sub_right, sub_add_cancel]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Imports
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.flip :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (a b : ℝ), (∀ t h, X (M.F.U t h) = M.F.U (-t) (X h)) →
      IsHilbertSchmidt (M.P (Ioc a b) ∘L X) → IsHilbertSchmidt (X ∘L M.P (Ioc a b)) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X a b hX hs
  obtain ⟨-, -, -, -, pl, p0, -, -⟩ := projLaws M
  rcases le_or_gt b a with hab | hab
  · rw [Ioc_eq_empty_of_le hab, p0, ContinuousLinearMap.comp_zero]
    show hsNormSq _ < _
    rw [hsNormSq_zero]; exact ENNReal.zero_lt_top
  set d := b - a with hd
  have d0 : 0 < d := sub_pos.2 hab
  let I : ℤ → Set ℝ := fun n => Ioc (a + n * d) (a + (n + 1) * d)
  have hI : ∀ n, MeasurableSet (I n) := fun _ => measurableSet_Ioc
  have sa : ∀ s, MeasurableSet s → ContinuousLinearMap.adjoint (M.P s) = M.P s := fun s hs => (pl s s hs hs).2.1.adjoint_eq
  have pyth : ∀ x : H, ‖x‖ₑ ^ 2 = ∑' n, ‖M.P (I n) x‖ₑ ^ 2 := fun x => by
    have h1 : HasSum (fun n => M.P (I n) x) x := by
      have h0 : HasSum (fun n => M.P (I n) x) (M.J (M.J.symm x)) :=
        ((cutLim (M.J.symm x)).2 a d d0).mapL (M.J.toContinuousLinearEquiv : L V →L[ℂ] H)
      rwa [M.J.apply_symm_apply] at h0
    have h2 := (h1.mapL (innerSL ℂ x)).mapL Complex.reCLM
    have e : ∀ n, (⟪x, M.P (I n) x⟫_ℂ).re = ‖M.P (I n) x‖ ^ 2 := fun n => by
      have i1 := DFunLike.congr_fun (pl _ _ (hI n) (hI n)).1 x
      rw [inter_self, ContinuousLinearMap.comp_apply] at i1
      rw [← i1, ← ContinuousLinearMap.adjoint_inner_left, sa _ (hI n), i1, inner_self_eq_norm_sq_to_K]
      simp [← Complex.ofReal_pow]
    simp only [innerSL_apply_apply, Complex.reCLM_apply, e] at h2
    rw [inner_self_eq_norm_sq_to_K] at h2
    have h3 : HasSum (fun n => ‖M.P (I n) x‖ ^ 2) (‖x‖ ^ 2) := by simpa [← Complex.ofReal_pow] using h2
    have h4 := ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg ‖M.P (I n) x‖) h3.summable
    rw [h3.tsum_eq] at h4
    simpa [ENNReal.ofReal_pow] using h4
  have dec : ∀ Y : H →L[ℂ] H, hsNormSq Y = ∑' n, hsNormSq (M.P (I n) ∘L Y) := fun Y => by
    simp only [hsNormSq]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun m => pyth _
  have un : ∀ t, ‖M.F.U t‖ₑ ≤ 1 := fun t => by
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_le_one]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => by rw [M.F.norm, one_mul]
  have step : ∀ n : ℤ, hsNormSq (M.P (I n) ∘L X ∘L M.P (Ioc a b)) ≤ hsNormSq (M.P (I n) ∘L ContinuousLinearMap.adjoint (M.P (Ioc a b) ∘L X)) := fun n => by
    have t1 := ((pl (Ioc a b) _ measurableSet_Ioc (measurableSet_Ioc (a := a) (b := b))).2.2.2.2 (-(n * d))).1
    have pre : (fun x => x + -(n * d)) ⁻¹' Ioc a b = I n := by
      ext x
      simp only [I, mem_preimage, mem_Ioc]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    rw [pre] at t1
    have t2 : ∀ h, M.F.U (-(n * d)) (M.P (Ioc a b) h) = M.P (I n) (M.F.U (-(n * d)) h) := fun h => DFunLike.congr_fun t1 h
    have e : M.P (I n) ∘L X ∘L M.P (Ioc a b) = M.F.U (-(n * d)) ∘L (M.P (Ioc a b) ∘L X ∘L M.P (I n)) ∘L M.F.U (-(n * d)) := by
      ext h
      simp only [ContinuousLinearMap.comp_apply]
      rw [← t2, hX, t2, ← M.F.add, add_neg_cancel, M.F.zero]
    have e2 : M.P (I n) ∘L ContinuousLinearMap.adjoint (M.P (Ioc a b) ∘L X) =
        ContinuousLinearMap.adjoint (M.P (Ioc a b) ∘L X ∘L M.P (I n)) := by
      simp only [ContinuousLinearMap.adjoint_comp, sa _ (hI n), ContinuousLinearMap.comp_assoc]
    rw [e, e2, hsNormSq_adjoint]
    refine (hsNormSq_comp_left_le _ _).trans ((mul_le_of_le_one_left' (pow_le_one' (un _) _)).trans ?_)
    exact (hsNormSq_comp_right_le _ _).trans (mul_le_of_le_one_left' (pow_le_one' (un _) _))
  show hsNormSq _ < _
  rw [dec]
  refine (ENNReal.tsum_le_tsum step).trans_lt ?_
  rw [← dec]
  exact hs.adjoint
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.NEx
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.nEx :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W), Function.Surjective (1 - M.abelian₂ M.T₀ M.T₀ ∘L M.F.av wR ∘L M.abelian₂ M.T₀ M.T₀ : H →L[ℂ] H) → ∃ N : W →ₗ[ℂ] V, M.IsN N := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M hs
  obtain ⟨c0, cadd, csmul, -, csh, -, -, -⟩ := cobLaws M.F
  obtain ⟨-, -, -, -, hP, -, -, hL⟩ := projLaws M
  have hP' := (projLaws M.swap).2.2.2.2.1
  obtain ⟨o1, o2, l0, -, -, l1, l2, l3, l4⟩ := hL M.T₀ M.T₀ (by linarith)
  set T := M.T₀ with hT
  set Λ := M.abelian₂ T T with hΛ
  have mI : ∀ x : ℝ, MeasurableSet (Ioi x) := fun _ => measurableSet_Ioi
  have carry : ∀ p : L V, Tail p → M.F.Cob (M.J p - M.J (one V (∫ x, p x))) := fun p hp => by
    have := (cobLaws (shF V)).2.2.2.2.2.2.2 M.F (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) (fun t h => (M.hJ t h).symm) _
      ((cobTail p).2 hp).2
    rwa [map_sub] at this
  have ex : ∀ w, ∃ n, M.F.Cob (M.J' (one W w) - M.J (one V n)) := by
    intro w
    set h := M.F.U (T - 1) (M.J' (one W w)) with hh
    have s0 : M.P' (Ioc 0 1) (M.J' (one W w)) = M.J' (one W w) := by
      show M.J' (cut W _ (M.J'.symm (M.J' _))) = _
      rw [M.J'.symm_apply_apply, ((cutLaws (Ioc 0 1) univ measurableSet_Ioc .univ).2.2.2.2.2.2.2.1 _).2]
      exact ((svSpec (V := W)).2 w).1.mono fun x hx hn => by rw [hx, indicator_of_notMem hn]
    have s1 : M.P' (Ioc (T - 1) T) h = h := by
      have := DFunLike.congr_fun ((hP _ _ (measurableSet_Ioc (a := (0 : ℝ)) (b := 1)) .univ).2.2.2.2 (T - 1)).2 (M.J' (one W w))
      have y : (fun x : ℝ => x - (T - 1)) ⁻¹' Ioc 0 1 = Ioc (T - 1) T := by
        ext x; simp only [mem_preimage, mem_Ioc]; constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith
      rw [y] at this
      simp only [ContinuousLinearMap.comp_apply, s0] at this
      exact this.symm
    have s2 : M.P' (Ioi T) h = 0 := by
      have a : M.P' (Ioi T) ∘L M.P' (Ioc (T - 1) T) = M.P' (Ioi T ∩ Ioc (T - 1) T) := (hP' _ _ (mI T) measurableSet_Ioc).1
      have b : Ioi T ∩ Ioc (T - 1) T = ∅ := eq_empty_of_forall_notMem fun x hx => absurd hx.1 (not_lt.2 hx.2.2)
      rw [b, show M.P' ∅ = 0 from (projLaws M.swap).2.2.2.2.2.1] at a
      rw [← s1]; exact DFunLike.congr_fun a h
    have s3 : M.P (Ioi (T + 1)) h = 0 := by
      have a : M.P' (Ioi (T - 1)) ∘L M.P' (Ioc (T - 1) T) = M.P' (Ioi (T - 1) ∩ Ioc (T - 1) T) := (hP' _ _ (mI _) measurableSet_Ioc).1
      rw [inter_eq_right.2 Ioc_subset_Ioi_self] at a
      rw [← s1, ← a]
      exact DFunLike.congr_fun (hL (T + 1) (T - 1) (by linarith)).1 _
    obtain ⟨k, hk⟩ := hs (Λ h)
    set R := M.F.av wR with hR
    have hk' : k - Λ (R (Λ k)) = Λ h := hk
    have ΛΛ : ∀ x, Λ (Λ x) = Λ x := fun x => DFunLike.congr_fun l0 x
    have kΛ : Λ k = k := by
      have := congrArg Λ hk'
      rw [map_sub, ΛΛ, ΛΛ, ← hk'] at this
      exact sub_left_injective this
    rw [kΛ] at hk'
    have k1 : M.P (Ioi T) k = 0 := by rw [← kΛ]; exact DFunLike.congr_fun l2 k
    have k2 : M.P' (Ioi T) k = 0 := by rw [← kΛ]; exact DFunLike.congr_fun l4 k
    have r2 : M.P' (Ioi T) (R k) = 0 := by
      obtain ⟨i, e⟩ := ((avSpec M.F).2.2.2 _ (avSpec M.F).2.1).1 k
      rw [hR, e, ← (M.P' (Ioi T)).integral_comp_comm i]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun r => ?_)
      by_cases hr : r ≤ 0
      · have a := DFunLike.congr_fun ((hP _ _ (mI (T - r)) .univ).2.2.2.2 r).2 k
        have y : (fun x : ℝ => x - r) ⁻¹' Ioi (T - r) = Ioi T := by ext x; simp
        have b : M.P' (Ioi (T - r)) ∘L M.P' (Ioi T) = M.P' (Ioi (T - r) ∩ Ioi T) := (hP' _ _ (mI _) (mI _)).1
        rw [inter_eq_left.2 (Ioi_subset_Ioi (by linarith))] at b
        rw [y, ← b] at a
        simp only [ContinuousLinearMap.comp_apply, k2, map_zero] at a
        simp [← a]
      · simp [wR, hr]
    have dec : h = (k - R k) + M.P (Ioi T) (R k) + M.P (Ioi T) h := by
      have a : Λ h = h - M.P (Ioi T) h - M.P' (Ioi T) h := rfl
      have b : Λ (R k) = R k - M.P (Ioi T) (R k) - M.P' (Ioi T) (R k) := rfl
      rw [a, b, s2, r2, sub_zero, sub_zero] at hk'
      linear_combination (norm := module) -hk'
    have cl := fun s t hs ht => cutLaws (V := V) s t hs ht
    set u := M.J.symm k with hu
    have u1 : cut V (Iic T) u = u := by
      have a := (cl (Iic T) (Ioi T) measurableSet_Iic (mI T)).2.2.1 (Iic_disjoint_Ioi le_rfl)
      rw [Iic_union_Ioi, (cl _ _ .univ .univ).2.2.2.1] at a
      have b : u = cut V (Iic T) u + cut V (Ioi T) u := DFunLike.congr_fun a u
      have c : cut V (Ioi T) u = 0 := M.J.injective (by rw [map_zero]; exact k1)
      rw [c, add_zero] at b
      exact b.symm
    have e1 : M.P (Ioi T) (R k) = M.J (cut V (Ioi T) ((shF V).av wR u)) := by
      have := DFunLike.congr_fun (((avSpec (shF V)).2.2.2 _ (avSpec M.F).2.1).2.2.2.2 M.F
        (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) fun t h => (M.hJ t h).symm) u
      have a : M.J ((shF V).av wR u) = R (M.J u) := this
      rw [hu, M.J.apply_symm_apply] at a
      show M.J (cut V _ (M.J.symm (R k))) = _
      rw [← a, M.J.symm_apply_apply]
    set v := cut V (Ioi T) (M.J.symm h) with hv
    have e2 : M.P (Ioi T) h = M.J v := rfl
    have bv : Bdd v := by
      refine ⟨|T| + 1, ?_⟩
      have a := (cl (Ioc T (T + 1)) (Ioi (T + 1)) measurableSet_Ioc (mI _)).2.2.1 (Ioc_disjoint_Ioi le_rfl)
      rw [Ioc_union_Ioi_eq_Ioi (by linarith)] at a
      have c : cut V (Ioi (T + 1)) (M.J.symm h) = 0 := M.J.injective (by rw [map_zero]; exact s3)
      have b : v = cut V (Ioc T (T + 1)) (M.J.symm h) := by rw [hv, a, ContinuousLinearMap.add_apply, c, add_zero]
      have d := (cl (Icc (-(|T| + 1)) (|T| + 1)) (Ioc T (T + 1)) measurableSet_Icc measurableSet_Ioc).1
      have sub : Ioc T (T + 1) ⊆ Icc (-(|T| + 1)) (|T| + 1) := fun x hx =>
        ⟨by linarith [hx.1, neg_abs_le T], by linarith [hx.2, le_abs_self T]⟩
      rw [inter_eq_right.2 sub] at d
      rw [b]
      exact DFunLike.congr_fun d _
    have f1 := carry _ (resTail u T u1)
    have f2 := carry _ ((cobTail v).1 bv)
    have f3 := (cadd _ _ (cadd _ _ (cadd _ _ (csh (T - 1) (M.J' (one W w))) (resCob M.F k).1).1 f1).1 f2).1
    refine ⟨(∫ x, cut V (Ioi T) ((shF V).av wR u) x) + ∫ x, v x, ?_⟩
    convert f3 using 1
    rw [← e1, ← e2, map_add, map_add, ← hh, ← hR]
    linear_combination (norm := module) dec
  choose n hn using ex
  let b := Module.finBasis ℂ W
  refine ⟨b.constr ℂ fun i => n (b i), fun w => ?_⟩
  have e : M.J' (one W w) - M.J (one V (b.constr ℂ (fun i => n (b i)) w)) =
      ∑ i, b.repr w i • (M.J' (one W (b i)) - M.J (one V (n (b i)))) := by
    conv_lhs => rw [← b.sum_repr w]
    simp only [map_sum, map_smul, Module.Basis.constr_basis, smul_sub, Finset.sum_sub_distrib]
  rw [e]
  exact Finset.sum_induction _ _ (fun x y hx hy => (cadd x y hx hy).1) c0 fun i _ => csmul _ _ (hn _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.NInt
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.nInt :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (N : W →ₗ[ℂ] V), M.IsN N → ∀ (Y : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → M.Acts Y β β' →
      ∀ w, N (symb β' 0 w) = symb β 0 (N w) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M N hN Y β β' k1 k2 ha w
  obtain ⟨-, cadd, -, -, -, -, -, cmap⟩ := cobLaws M.F
  have hY : ∀ t h, Y (M.F.U t h) = M.F.U t (Y h) := fun t h => by
    obtain ⟨u, rfl⟩ := M.J.surjective h
    rw [M.hJ, ha.1, ha.1, M.hJ]
    exact congrArg M.J (DFunLike.congr_fun ((convLaws β k1).1 t) u)
  have h1 := cmap M.F Y hY _ (hN w)
  rw [map_sub, ha.1, ha.2] at h1
  obtain ⟨-, b1, s1⟩ := (svSpec (V := W)).2 w
  obtain ⟨-, b2, s2⟩ := (svSpec (V := V)).2 (N w)
  obtain ⟨b3, s3⟩ := (convLaws β' k2).2.2 _ b1
  obtain ⟨b4, s4⟩ := (convLaws β k1).2.2 _ b2
  have h2 := nAll M N hN _ b3
  rw [s3, s1] at h2
  have h3 := ((cobTail _).2 ((cobTail _).1 b4)).2
  rw [s4, s2] at h3
  have h4 := (cobLaws (shF V)).2.2.2.2.2.2.2 M.F (M.J.toContinuousLinearEquiv : L V →L[ℂ] H) (fun t h => (M.hJ t h).symm) _ h3
  have h5 := (cadd _ _ (cadd _ _ h1 h2).2 h4).1
  have h6 : M.F.Cob (M.J (one V (N (symb β' 0 w) - symb β 0 (N w)))) := by
    convert h5 using 1
    simp
  exact sub_eq_zero.1 ((nIso M).1 _ h6)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.OntoJ
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.ontoJ :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (D : Datum H V W), Function.Surjective D.J := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ D
  set J := D.J.toContinuousLinearMap with hJ
  set J' := D.J'.toContinuousLinearMap with hJ'
  set A := ContinuousLinearMap.adjoint J with hA
  set A' := ContinuousLinearMap.adjoint J' with hA'
  have aJ : ∀ u, A (D.J u) = u := fun u => ext_inner_left ℂ fun y => by
    rw [hA, ContinuousLinearMap.adjoint_inner_right]; exact D.J.inner_map_map _ _
  have aJ' : ∀ u, A' (D.J' u) = u := fun u => ext_inner_left ℂ fun y => by
    rw [hA', ContinuousLinearMap.adjoint_inner_right]; exact D.J'.inner_map_map _ _
  have iA : ∀ u h, ⟪D.J u, h⟫_ℂ = ⟪u, A h⟫_ℂ := fun u h => (ContinuousLinearMap.adjoint_inner_right J u h).symm
  have iA' : ∀ u h, ⟪D.J' u, h⟫_ℂ = ⟪u, A' h⟫_ℂ := fun u h => (ContinuousLinearMap.adjoint_inner_right J' u h).symm
  have shf : ∀ t u v, ⟪D.J (sh V t u), D.J' v⟫_ℂ = ⟪D.J u, D.J' (sh W t v)⟫_ℂ := fun t u v =>
    D.shift t u _ v _ (sh_ae V _ u) (sh_ae W _ v)
  have adV : ∀ t (x y : L V), ⟪sh V t x, y⟫_ℂ = ⟪x, sh V (-t) y⟫_ℂ := fun t x y => by
    have := (avSpec (shF V)).1 t
    rw [← ContinuousLinearMap.adjoint_inner_right]; exact congrArg (fun Z : L V →L[ℂ] L V => ⟪x, Z y⟫_ℂ) this
  have adW : ∀ t (x y : L W), ⟪sh W t x, y⟫_ℂ = ⟪x, sh W (-t) y⟫_ℂ := fun t x y => by
    have := (avSpec (shF W)).1 t
    rw [← ContinuousLinearMap.adjoint_inner_right]; exact congrArg (fun Z : L W →L[ℂ] L W => ⟪x, Z y⟫_ℂ) this
  have S1 : ∀ t v, A (D.J' (sh W t v)) = sh V (-t) (A (D.J' v)) := fun t v => ext_inner_left ℂ fun y => by
    rw [← iA, ← shf, iA, adV]
  have S2 : ∀ t u, A' (D.J (sh V (-t) u)) = sh W t (A' (D.J u)) := fun t u => ext_inner_left ℂ fun y => by
    rw [← iA', ← inner_conj_symm, shf, inner_conj_symm, iA', adW, neg_neg]
  let Q : H →L[ℂ] H := 1 - J ∘L A
  have Qa : ∀ h, Q h = h - D.J (A h) := fun _ => rfl
  have AQ : ∀ h, A (Q h) = 0 := fun h => by rw [Qa, map_sub, aJ, sub_self]
  have nQ : ∀ h, ‖Q h‖ ^ 2 = ‖h‖ ^ 2 - ‖A h‖ ^ 2 := fun h => by
    have h1 : ⟪D.J (A h), Q h⟫_ℂ = 0 := by rw [iA, AQ, inner_zero_right]
    have h2 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h1
    rw [Qa h, add_sub_cancel, D.J.norm_map, ← Qa] at h2
    nlinarith
  let x : L W → ℝ → H := fun v t => Q (D.J' (sh W t v))
  have Ax : ∀ v t, A (x v t) = 0 := fun v t => AQ _
  have nx : ∀ v t, ‖x v t‖ = ‖Q (D.J' v)‖ := fun v t => by
    refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [nQ, nQ, S1, D.J'.norm_map, D.J'.norm_map]
    exact congrArg₂ (fun a b : ℝ => a ^ 2 - b ^ 2) ((shF W).norm t v) ((shF V).norm _ _)
  have A'x : ∀ v t, A' (x v t) = sh W t (v - A' (D.J (A (D.J' v)))) := fun v t => by
    show A' (Q _) = _
    rw [Qa, map_sub, aJ', S1, S2, map_sub]
  have dense : ∀ (y : H) (ε : ℝ), 0 < ε → ∃ u v, ‖y - (D.J u + D.J' v)‖ < ε := by
    intro y ε hε
    have : (LinearMap.range D.J.toLinearMap ⊔ LinearMap.range D.J'.toLinearMap).topologicalClosure = ⊤ := by
      rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
      exact fun h hh => D.span h (fun u => hh _ (Submodule.mem_sup_left ⟨u, rfl⟩)) fun v => hh _ (Submodule.mem_sup_right ⟨v, rfl⟩)
    have hy : y ∈ closure ((LinearMap.range D.J.toLinearMap ⊔ LinearMap.range D.J'.toLinearMap : Submodule ℂ H) : Set H) := by
      rw [← Submodule.topologicalClosure_coe, this]; trivial
    obtain ⟨z, hz, hd⟩ := Metric.mem_closure_iff.1 hy ε hε
    obtain ⟨_, ⟨u, rfl⟩, _, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hz
    exact ⟨u, v, by rwa [dist_eq_norm] at hd⟩
  have weak : ∀ v y, Tendsto (fun t => ⟪y, x v t⟫_ℂ) atTop (𝓝 0) := by
    intro v y
    rw [Metric.tendsto_nhds]
    intro ε hε
    set c := ‖Q (D.J' v)‖ + 1 with hc
    have c0 : 0 < c := by positivity
    obtain ⟨u, w, hd⟩ := dense y (ε / 2 / c) (by positivity)
    have h1 := Metric.tendsto_nhds.1 (shNull (V := W) (v - A' (D.J (A (D.J' v)))) w).1 (ε / 2) (by positivity)
    filter_upwards [h1] with t ht
    rw [dist_zero_right] at ht ⊢
    have e : ⟪y, x v t⟫_ℂ = ⟪y - (D.J u + D.J' w), x v t⟫_ℂ + ⟪w, (shF W).U t (v - A' (D.J (A (D.J' v))))⟫_ℂ := by
      rw [inner_sub_left, inner_add_left, iA, iA', A'x, Ax, inner_zero_right, zero_add]
      exact (sub_add_cancel _ _).symm
    rw [e]
    have h2 : ‖⟪y - (D.J u + D.J' w), x v t⟫_ℂ‖ ≤ ε / 2 / c * c := by
      refine (norm_inner_le_norm _ _).trans ?_
      rw [nx]; gcongr; linarith
    rw [div_mul_cancel₀ _ c0.ne'] at h2
    linarith [norm_add_le ⟪y - (D.J u + D.J' w), x v t⟫_ℂ ⟪w, (shF W).U t (v - A' (D.J (A (D.J' v))))⟫_ℂ]
  have sup : ∀ {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [CompleteSpace X] (s : ℝ) (u : L X),
      ∀ᵐ x : ℝ, x ≤ s → cut X (Ioi s) u x = 0 := fun s u =>
    (((cutLaws (Ioi s) (Ioi s) measurableSet_Ioi measurableSet_Ioi).2.2.2.2.2.2.2.1 _).1
      (by simpa using DFunLike.congr_fun (cutLaws (Ioi s) (Ioi s) measurableSet_Ioi measurableSet_Ioi).1 u)).mono
      fun x h hx => h (by simpa using hx)
  set Λ : H →L[ℂ] H := 1 - J ∘L cut V (Ioi D.T₀) ∘L A - J' ∘L cut W (Ioi D.T₀) ∘L A' with hΛ
  have tr : IsTrunc D.J D.J' D.T₀ Λ := (truncEq D.J D.J' D.T₀ Λ fun u v =>
    D.causal D.T₀ _ _ (sup _ u) ((sup _ v).mono fun x h hx => h (by linarith))).2 rfl
  have Λx : ∀ v, Tendsto (fun t => x v t - Λ (x v t)) atTop (𝓝 0) := fun v => by
    have := (D.J'.continuous.tendsto 0).comp ((cutLim (v - A' (D.J (A (D.J' v))))).1 D.T₀)
    rw [map_zero] at this
    refine this.congr fun t => ?_
    show _ = x v t - (x v t - D.J (cut V _ (A (x v t))) - D.J' (cut W _ (A' (x v t))))
    rw [A'x, Ax]; simp
  have BJ : ∀ u, D.B (D.J u) = D.J (conv D.β u) := fun u => D.B_J u _ (convSpec _ D.β_ker u).1
  have BJ' : ∀ u, D.B (D.J' u) = D.J' (conv D.β' u) := fun u => D.B_J' u _ (convSpec _ D.β'_ker u).1
  have BQ : ∀ h, D.B (Q h) = Q (D.B h) := fun h => by
    have h1 : A (D.B (Q h)) = 0 := ext_inner_left ℂ fun y => by
      rw [← iA, ← D.B_sa.isSymmetric.apply_clm, BJ, iA, AQ, inner_zero_right, inner_zero_right]
    have h2 : D.B h = D.B (Q h) + D.J (conv D.β (A h)) := by rw [← BJ, ← map_add, Qa, sub_add_cancel]
    rw [Qa (D.B h)]
    conv_rhs => rw [h2, map_add, h1, aJ, zero_add, add_sub_cancel_right]
  have Bx : ∀ v t, D.B (x v t) = x (conv D.β' v) t := fun v t => by
    show D.B (Q _) = Q _
    rw [BQ, BJ']
    exact congrArg (fun z => Q (D.J' z)) (DFunLike.congr_fun ((convLaws _ D.β'_ker).1 t) v)
  have zero : ∀ v, Q (D.J' (conv D.β' v)) = 0 := fun v => by
    have t1 := cptNull atTop _ (x v) _ (D.compact _ Λ le_rfl tr) (fun t => (nx v t).le) (weak v)
    have t2 := ((Λ ∘L D.B).continuous.tendsto 0).comp (Λx v)
    have t3 := (t1.add t2).add (Λx (conv D.β' v))
    simp only [map_zero, add_zero] at t3
    have t4 : Tendsto (fun t => x (conv D.β' v) t) atTop (𝓝 0) := t3.congr fun t => by
      simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, map_sub, Bx]; abel
    have t5 := tendsto_zero_iff_norm_tendsto_zero.1 t4
    simp only [nx] at t5
    exact norm_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds t5)
  have QJ' : ∀ v, Q (D.J' v) = 0 := fun v =>
    (convDense _ D.β'_ker D.β'_unit).induction_on v (isClosed_eq (Q.continuous.comp D.J'.continuous) continuous_const) zero
  intro h
  refine ⟨A h, (sub_eq_zero.1 (D.span (Q h) (fun u => by rw [iA, AQ, inner_zero_right]) fun v => ?_)).symm⟩
  have e : D.J' v = D.J (A (D.J' v)) := sub_eq_zero.1 (QJ' v)
  rw [e, iA, AQ, inner_zero_right]
end

