import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0005

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.Ot0
section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem ot0 (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    (hF : FixedStatement n M) (hS : ShellStatement n M) (hL : LocalStatement n M)
    (hCut : CutoffStatement) : JacobianInterpolationStatement n M := by
  intro X g ph ph2 r j c hn hj hr hg hph hphL hph2 hph2L hbd hfin0 hJ0
  have hfin : (zeroSet n g).Finite := hfin0
  have hJ : ∀ p ∈ zeroSet n g, jac n X.z g p ≠ 0 := fun p hp => hJ0 p hp
  have hz := X.isLocalHomeomorph
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = Real.pi ^ n / (Nat.factorial (n - 1) : ℝ) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = r ^ (2 * n) := ⟨_, rfl⟩
  have hQpos : 0 < Q := by rw [hQ]; positivity
  have hRpos : 0 < R := by rw [hR]; positivity
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨Sg, hSg⟩ : ∃ Sg : ℝ, Sg = ∑ p ∈ hfin.toFinset,
      ‖c p‖ ^ 2 * Real.exp (-ph2 p - (j : ℝ) * ph p) := ⟨_, rfl⟩
  have hsum : (∑' x : {x : M // ∀ i, g i x = 0},
      ENNReal.ofReal (‖c x‖ ^ 2 * Real.exp (-ph2 x - (j : ℝ) * ph x))) = ENNReal.ofReal Sg := by
    rw [hSg, ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity), ← Finset.tsum_subtype]
    exact (Equiv.subtypeEquivRight (fun x => (hfin.mem_toFinset).symm)).tsum_eq
      (fun y => ENNReal.ofReal (‖c y.1‖ ^ 2 * Real.exp (-ph2 y.1 - (j : ℝ) * ph y.1)))
  by_cases hS0 : Sg = 0
  · have hc : ∀ p ∈ zeroSet n g, c p = 0 := by
      intro p hp
      rw [hSg] at hS0
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => by positivity)).1 hS0 p
        (hfin.mem_toFinset.2 hp)
      have h2 : ‖c p‖ ^ 2 = 0 := by
        rcases mul_eq_zero.1 h1 with h | h
        · exact h
        · exact absurd h (Real.exp_pos _).ne'
      simpa using h2
    refine ⟨fun _ => 0, fun e _ => differentiableOn_const 0, fun x hx => ?_, ?_⟩
    · simp [hc x hx]
    · simp
  have hSpos : 0 < Sg := lt_of_le_of_ne
    (by rw [hSg]; exact Finset.sum_nonneg fun p _ => by positivity) (Ne.symm hS0)
  have hN0 : ∀ p : M, ∃ N : Set M, p ∈ zeroSet n g → IsOpen N ∧ p ∈ N ∧
      ∀ τ : ℝ, 0 < τ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∫⁻ x in N ∩ shell n g ph r ε, ENNReal.ofReal (‖jac n X.z g x‖ ^ 2 *
          Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * ev n g ph r x ^ (-(n : ℝ))) ∂vol n X.z ≤
        ENNReal.ofReal ((1 + τ) * (Q * Real.log 2) * R * Real.exp (-ph2 p - (j : ℝ) * ph p)) := by
    intro p
    by_cases hp : p ∈ zeroSet n g
    · obtain ⟨N, h1, h2, h3⟩ := hS X.z g ph ph2 r j p hn hz hg hph hph2 hr hp (hJ p hp)
      rw [← hQ, ← hR] at h3
      exact ⟨N, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨Set.univ, fun h => absurd h hp⟩
  choose N hN using hN0
  obtain ⟨W, m, hLD, hWN⟩ := hL X.z g ph r N hz hg hph hr hfin hJ
    (fun p hp => ⟨(hN p hp).1, (hN p hp).2.1⟩)
  obtain ⟨χ, hχ⟩ := hCut
  have hevm : Measurable (ev n g ph r) := (continuous_weightFunction n X.z hz g ph r hg hph).measurable
  have hWm : ∀ p ∈ zeroSet n g, MeasurableSet (W p) := fun p hp => (hLD.2 p hp).1.measurableSet

  have E1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ zeroSet n g,
      ∫⁻ x in N p ∩ shell n g ph r ε, ENNReal.ofReal (‖jac n X.z g x‖ ^ 2 *
          Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * ev n g ph r x ^ (-(n : ℝ))) ∂vol n X.z ≤
        ENNReal.ofReal ((1 + 1 / 200) * (Q * Real.log 2) * R *
          Real.exp (-ph2 p - (j : ℝ) * ph p)) :=
    (eventually_all_finite hfin).2 (fun p hp => (hN p hp).2.2 (1 / 200) (by norm_num))
  have E2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ zeroSet n g, ∀ t : ℝ, 0 < t → t ≤ ε →
      ∫⁻ x in N p ∩ shell n g ph r t, ENNReal.ofReal (‖jac n X.z g x‖ ^ 2 *
          Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * ev n g ph r x ^ (-(n : ℝ))) ∂vol n X.z ≤
        ENNReal.ofReal ((1 + 1) * (Q * Real.log 2) * R * Real.exp (-ph2 p - (j : ℝ) * ph p)) := by
    refine (eventually_all_finite hfin).2 (fun p hp => ?_)
    obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 ((hN p hp).2.2 1 one_pos)
    filter_upwards [Ioo_mem_nhdsGT hu] with ε hε t ht htε
    exact hsub ⟨ht, htε.trans_lt hε.2⟩
  have E3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have E4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 / 100 :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually_lt_const (by norm_num)
  have E5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 * ε ^ 2 < m := by
    have h : Tendsto (fun ε : ℝ => 2 * ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (fun ε : ℝ => 2 * ε ^ 2) := by fun_prop
      have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    exact h.eventually_lt_const hLD.1
  have E6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (1 + ε ^ 2) ^ n < 1 + 1 / 200 := by
    have h : Tendsto (fun ε : ℝ => (1 + ε ^ 2) ^ n) (𝓝[>] 0) (𝓝 1) := by
      have hc : Continuous (fun ε : ℝ => (1 + ε ^ 2) ^ n) := by fun_prop
      have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    exact h.eventually_lt_const (by norm_num)
  obtain ⟨ε, hε1, hε2, hε0, hε100, hεm, hεn⟩ :=
    (E1.and (E2.and (E3.and (E4.and (E5.and E6))))).exists
  obtain ⟨F, hFh, hFS, hFb⟩ := hF X g ph ph2 r j c W m χ ε hn hg hph hphL hph2 hph2L hr hj hbd
    hfin hJ hLD hχ hε0 (by linarith) hεm
  refine ⟨F, hFh, fun x hx => hFS x hx, ?_⟩

  have hG : ∫⁻ x in shell n g ph r ε, ENNReal.ofReal (‖gt n X.z g c W x‖ ^ 2 *
      Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * ev n g ph r x ^ (-(n : ℝ))) ∂vol n X.z ≤
      ENNReal.ofReal ((1 + 1 / 200) * (Q * Real.log 2) * R * Sg) := by
    calc _ ≤ ∑ p ∈ hfin.toFinset, ∫⁻ x in W p, ENNReal.ofReal (‖c p‖ ^ 2) *
          ENNReal.ofReal (‖jac n X.z g x‖ ^ 2 * Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) *
            ev n g ph r x ^ (-(n : ℝ))) ∂(vol n X.z).restrict (shell n g ph r ε) := by
          refine lintegral_le_sum_setLIntegral _ _ _ (fun p hp => hWm p (hfin.mem_toFinset.1 hp)) _ _ ?_ ?_
          · intro x hx
            by_contra hno
            push_neg at hno
            apply hx
            rw [localExtension_eq_zero_off n X.z g c W (fun p hp => hno p (hfin.mem_toFinset.2 hp))]
            simp
          · intro p hp x hx
            rw [localExtension_eq_mul_jacobian n X.z g ph r c W m hLD hfin (hfin.mem_toFinset.1 hp) hx,
              ← ENNReal.ofReal_mul (sq_nonneg _)]
            apply le_of_eq
            congr 1
            rw [norm_mul]
            ring
      _ ≤ ∑ p ∈ hfin.toFinset, ENNReal.ofReal (‖c p‖ ^ 2) *
          ENNReal.ofReal ((1 + 1 / 200) * (Q * Real.log 2) * R *
            Real.exp (-ph2 p - (j : ℝ) * ph p)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp' := hfin.mem_toFinset.1 hp
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, Measure.restrict_restrict (hWm p hp')]
          gcongr
          exact (lintegral_mono_set (Set.inter_subset_inter_left _ (hWN p hp'))).trans (hε1 p hp')
      _ = ENNReal.ofReal ((1 + 1 / 200) * (Q * Real.log 2) * R * Sg) := by
          rw [hSg, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
          · refine Finset.sum_congr rfl fun p _ => ?_
            rw [← ENNReal.ofReal_mul (sq_nonneg _)]
            congr 1
            ring
          · intro p _
            positivity

  have hF0 : otNorm n X.z ph ph2 j (cutExt n X.z g ph r c W χ ε) ≤
      ENNReal.ofReal (2 * ((1 + 1) * (Q * Real.log 2) * R) * ε ^ 2 * Sg) := by
    unfold otNorm
    calc _ ≤ ∑ p ∈ hfin.toFinset, ∫⁻ x in W p ∩ {x | ev n g ph r x < ε ^ 2},
          ENNReal.ofReal (‖c p‖ ^ 2) * ENNReal.ofReal (‖jac n X.z g x‖ ^ 2 *
            Real.exp (-ph2 x - ((n : ℝ) + j) * ph x)) ∂vol n X.z := by
          refine lintegral_le_sum_setLIntegral _ _ _ (fun p hp => (hWm p (hfin.mem_toFinset.1 hp)).inter
            (measurableSet_lt hevm measurable_const)) _ _ ?_ ?_
          · intro x hx
            have hne : cutExt n X.z g ph r c W χ ε x ≠ 0 := by
              intro h0
              apply hx
              simp [h0]
            unfold cutExt at hne
            have hχne : χ (ev n g ph r x / ε ^ 2) ≠ 0 := fun h => hne (by simp [h])
            have hgne : gt n X.z g c W x ≠ 0 := fun h => hne (by simp [h])
            have hlt : ev n g ph r x < ε ^ 2 := by
              by_contra hge
              push_neg at hge
              exact hχne (hχ.2.2.1 _ ((one_le_div (by positivity)).2 hge))
            by_contra hno
            push_neg at hno
            exact hgne (localExtension_eq_zero_off n X.z g c W
              (fun p hp hxp => hno p (hfin.mem_toFinset.2 hp) ⟨hxp, hlt⟩))
          · intro p hp x hx
            rw [← ENNReal.ofReal_mul (sq_nonneg _)]
            apply ENNReal.ofReal_le_ofReal
            unfold cutExt
            rw [localExtension_eq_mul_jacobian n X.z g ph r c W m hLD hfin (hfin.mem_toFinset.1 hp) hx.1,
              norm_mul, norm_mul, Complex.norm_real]
            have h1 : ‖χ (ev n g ph r x / ε ^ 2)‖ ≤ 1 := by
              rw [Real.norm_eq_abs, abs_le]
              constructor <;> linarith [(hχ.2.2.2.1 (ev n g ph r x / ε ^ 2)).1,
                (hχ.2.2.2.1 (ev n g ph r x / ε ^ 2)).2]
            have hE := Real.exp_pos (-ph2 x - ((n : ℝ) + j) * ph x)
            have h2 : (‖χ (ev n g ph r x / ε ^ 2)‖ * (‖c p‖ * ‖jac n X.z g x‖)) ^ 2 ≤
                (‖c p‖ * ‖jac n X.z g x‖) ^ 2 := by
              rw [mul_pow]
              exact mul_le_of_le_one_left (sq_nonneg _)
                (by nlinarith [norm_nonneg (χ (ev n g ph r x / ε ^ 2))])
            calc _ ≤ (‖c p‖ * ‖jac n X.z g x‖) ^ 2 * Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) :=
                  mul_le_mul_of_nonneg_right h2 hE.le
              _ = _ := by ring
      _ ≤ ∑ p ∈ hfin.toFinset, ENNReal.ofReal (‖c p‖ ^ 2) * ENNReal.ofReal
          (2 * ((1 + 1) * (Q * Real.log 2) * R * Real.exp (-ph2 p - (j : ℝ) * ph p)) * ε ^ 2) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp' := hfin.mem_toFinset.1 hp
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          gcongr
          refine lintegral_dyadic_shell_bound (vol n X.z) (ev n g ph r) hevm (weightFunction_nonneg n g ph r) (W p)
            (hWm p hp') (fun x => ‖jac n X.z g x‖ ^ 2 * Real.exp (-ph2 x - ((n : ℝ) + j) * ph x))
            (fun x => by positivity) n hn ε _ hε0 (by linarith) (by positivity) ?_ ?_
          · refine measure_mono_null (fun x hx => ?_) (volume_singleton_eq_zero n hn X.z hz p)
            have hxS := mem_zeroSet_of_weight_nonpos n g ph r hr.ne' x hx.2
            by_contra hxp
            exact not_mem_neighborhood_of_ne n g ph r W m hLD hp' hxS hxp hx.1 ((hLD.2 x hxS).2.1)
          · intro t ht htε
            exact (lintegral_mono_set (Set.inter_subset_inter_left _ (hWN p hp'))).trans
              (hε2 p hp' t ht htε)
      _ = _ := by
          rw [hSg, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
          · refine Finset.sum_congr rfl fun p _ => ?_
            rw [← ENNReal.ofReal_mul (sq_nonneg _)]
            congr 1
            ring
          · intro p _
            positivity

  have hA0 : 0 ≤ 2 * Real.exp 1 * (1 + ε ^ 2) ^ n * 72 := by positivity
  have hxG : ENNReal.ofReal (2 * Real.exp 1 * (1 + ε ^ 2) ^ n * 72) *
      ∫⁻ x in shell n g ph r ε, ENNReal.ofReal (‖gt n X.z g c W x‖ ^ 2 *
        Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * ev n g ph r x ^ (-(n : ℝ))) ∂vol n X.z ≤
      ENNReal.ofReal (2 * Real.exp 1 * (1 + ε ^ 2) ^ n * 72 *
        ((1 + 1 / 200) * (Q * Real.log 2) * R * Sg)) := by
    rw [ENNReal.ofReal_mul hA0]
    gcongr
  have hmain := sqrt_add_sq_le_weighted _ _ _ _ (by positivity) (by positivity) hxG hF0
  have hε2' : ε ^ 2 ≤ 1 / 10000 := by nlinarith
  have hcoef : 101 / 100 * (2 * Real.exp 1 * (1 + ε ^ 2) ^ n * 72 * ((1 + 1 / 200) * Real.log 2))
      + 101 * (2 * ((1 + 1) * Real.log 2) * ε ^ 2) ≤ 280 := by
    have he := Real.exp_one_lt_d9
    have hl := Real.log_two_lt_d9
    have hu0 : 0 ≤ (1 + ε ^ 2) ^ n := by positivity
    have h1 : Real.exp 1 * (1 + ε ^ 2) ^ n ≤ 2.7182818286 * (1 + 1 / 200) :=
      mul_le_mul he.le hεn.le hu0 (by norm_num)
    have h2 : Real.exp 1 * (1 + ε ^ 2) ^ n * Real.log 2 ≤
        2.7182818286 * (1 + 1 / 200) * 0.6931471808 :=
      mul_le_mul h1 hl.le hlog.le (by norm_num)
    have h3 : Real.log 2 * ε ^ 2 ≤ 0.6931471808 * (1 / 10000) :=
      mul_le_mul hl.le hε2' (sq_nonneg _) (by norm_num)
    nlinarith
  have hconst : 0 ≤ ohsawaTakegoshiConstant n r := by unfold ohsawaTakegoshiConstant; positivity
  calc _ ≤ _ := hFb
    _ ≤ _ := hmain
    _ ≤ ENNReal.ofReal (ohsawaTakegoshiConstant n r * Sg) := by
        apply ENNReal.ofReal_le_ofReal
        have hy : 0 ≤ Q * R * Sg := by positivity
        have hot : ohsawaTakegoshiConstant n r = 280 * Q * R := by rw [hQ, hR]; unfold ohsawaTakegoshiConstant; ring
        rw [hot]
        calc _ = (101 / 100 * (2 * Real.exp 1 * (1 + ε ^ 2) ^ n * 72 * ((1 + 1 / 200) *
              Real.log 2)) + 101 * (2 * ((1 + 1) * Real.log 2) * ε ^ 2)) * (Q * R * Sg) := by ring
          _ ≤ 280 * (Q * R * Sg) := mul_le_mul_of_nonneg_right hcoef hy
          _ = _ := by ring
    _ = _ := by rw [ENNReal.ofReal_mul hconst, hsum]

end ReciprocityTheory.L2DbarEstimates.I
end

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.ShellBound
section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

theorem shellBound (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    (hP : PolarStatement n) (hCov : CovStatement n) : ShellStatement n M := by
  intro z g ph ph2 r j p hn hz hg hph hph2 hr hp hJ
  obtain ⟨e, he, hpe⟩ := exists_chart n z hz p
  obtain ⟨ρ, hρ, hbt, hinj, hsmall⟩ := sh_local n z g hg p hp hJ e he hpe
  have hcph : Continuous ph :=
    (Complex.continuous_re.comp (Smooth.continuous n z hz _ hph)).congr (fun x => by simp)
  have hcph2 : Continuous ph2 :=
    (Complex.continuous_re.comp (Smooth.continuous n z hz _ hph2)).congr (fun x => by simp)
  have hcg : ∀ i, Continuous (g i) := fun i => Smooth.continuous n z hz _ (Holo.smooth n z _ (hg i))
  have hevc : Continuous (ev n g ph r) := by
    unfold ev
    exact ((continuous_finsetSum _ fun i _ => (hcg i).norm.pow 2).mul
      (Real.continuous_exp.comp hcph.neg)).div_const _
  have hy0 : e p ∈ e.target := e.map_source hpe
  have hsp : e.symm (e p) = p := e.left_inv hpe
  have hca : ContinuousAt (fun y => ph (e.symm y)) (e p) :=
    hcph.continuousAt.comp (e.continuousAt_symm hy0)
  have hcb : ContinuousAt (fun y => ph2 (e.symm y) + (j : ℝ) * ph (e.symm y)) (e p) :=
    (hcph2.continuousAt.comp (e.continuousAt_symm hy0)).add
      (continuousAt_const.mul (hcph.continuousAt.comp (e.continuousAt_symm hy0)))
  obtain ⟨δ0, hδ0, h0⟩ := Metric.continuousAt_iff.1 hca 1 one_pos
  set ρ1 := min ρ δ0 with hρ1
  have hρ1p : 0 < ρ1 := lt_min hρ hδ0
  refine ⟨e.source ∩ e ⁻¹' ball (e p) ρ1, e.isOpen_inter_preimage isOpen_ball,
    ⟨hpe, mem_ball_self hρ1p⟩, ?_⟩
  intro τ hτ
  set θ := min (τ / 10) (1 / 4) with hθdef
  have hθ : 0 < θ := lt_min (by positivity) (by norm_num)
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousAt_iff.1 hca θ hθ
  obtain ⟨δ2, hδ2, h2⟩ := Metric.continuousAt_iff.1 hcb θ hθ
  set ρ' := min (min δ1 δ2) ρ1 with hρ'
  have hρ'p : 0 < ρ' := lt_min (lt_min hδ1 hδ2) hρ1p
  obtain ⟨κ, hκ, hκs⟩ := hsmall ρ' hρ'p
  set C0 := r ^ 2 * Real.exp (ph p + 1) with hC0
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ^ 2 * C0 < κ ^ 2 := by
    refine Filter.Eventually.and eventually_mem_nhdsWithin ?_
    apply nhdsWithin_le_nhds
    have ht : Tendsto (fun ε : ℝ => ε ^ 2 * C0) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2 * C0)) :=
      ((continuous_pow 2).mul continuous_const).tendsto 0
    rw [zero_pow two_ne_zero, zero_mul] at ht
    exact ht.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hev] with ε ⟨hε, hεκ⟩
  set G := shG n g e.symm with hGdef
  set A := (e.source ∩ e ⁻¹' ball (e p) ρ1) ∩ shell n g ph r ε with hAdef
  have hAm : MeasurableSet A := by
    refine (e.isOpen_inter_preimage isOpen_ball).measurableSet.inter ?_
    exact ((isClosed_le continuous_const hevc).inter (isClosed_le hevc continuous_const)).measurableSet
  set Fh : M → ℝ≥0∞ := fun x => ENNReal.ofReal (‖LinearMap.det (fderiv ℂ G (z x) : V n →ₗ[ℂ] V n)‖ ^ 2 *
      Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * ev n g ph r x ^ (-(n : ℝ))) with hFh
  have hFm : Measurable Fh := by
    have hd : Measurable fun x => (fderiv ℂ G (z x)).det :=
      ContinuousLinearMap.continuous_det.measurable.comp
        ((measurable_fderiv ℂ G).comp hz.continuous.measurable)
    refine Measurable.ennreal_ofReal ?_
    refine ((hd.norm.pow_const 2).mul ?_).mul (hevc.measurable.pow_const _)
    exact (Real.continuous_exp.comp ((hcph2.neg).sub (continuous_const.mul hcph))).measurable
  set a := ε ^ 2 * r ^ 2 * Real.exp (ph p - θ) / 2 with hadef
  set b := ε ^ 2 * r ^ 2 * Real.exp (ph p + θ) with hbdef
  have ha : 0 < a := by positivity
  have hba : b / a = 2 * Real.exp (2 * θ) := by
    rw [div_eq_iff ha.ne', hadef, hbdef]
    have : Real.exp (ph p + θ) = Real.exp (2 * θ) * Real.exp (ph p - θ) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  have hab : a ≤ b := by
    have : 1 ≤ b / a := by rw [hba]; nlinarith [Real.add_one_le_exp (2 * θ)]
    rwa [le_div_iff₀ ha, one_mul] at this
  set Ann := {w : V n | a ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ b} with hAnn
  have hAnnm : MeasurableSet Ann :=
    ((isClosed_le continuous_const (continuous_norm.pow 2)).inter
      (isClosed_le (continuous_norm.pow 2) continuous_const)).measurableSet
  set K := r ^ (2 * n) * Real.exp (-ph2 p - (j : ℝ) * ph p) * Real.exp θ with hK
  have hK0 : 0 ≤ K := by positivity
  set f : V n → ℝ≥0∞ := fun w => ENNReal.ofReal K *
      Ann.indicator (fun w => ENNReal.ofReal ((‖w‖ ^ 2) ^ (-(n : ℝ)))) w with hfdef
  have hfm' : Measurable fun w : V n => ENNReal.ofReal ((‖w‖ ^ 2) ^ (-(n : ℝ))) :=
    ((measurable_norm.pow_const 2).pow_const _).ennreal_ofReal
  have hfm : Measurable f := measurable_const.mul (hfm'.indicator hAnnm)
  set U' := ball (e p) ρ' with hU'
  have hU'1 : U' ⊆ ball (e p) ρ1 := ball_subset_ball (min_le_right _ _)
  have hU'ρ : U' ⊆ ball (e p) ρ := hU'1.trans (ball_subset_ball (min_le_left _ _))
  set h2f : V n → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (‖LinearMap.det (fderiv ℂ G y : V n →ₗ[ℂ] V n)‖ ^ 2) * f (G y) with hh2

  have step1 : ∫⁻ x in (e.source ∩ e ⁻¹' ball (e p) ρ1) ∩ shell n g ph r ε,
      ENNReal.ofReal (‖jac n z g x‖ ^ 2 * Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) *
        ev n g ph r x ^ (-(n : ℝ))) ∂vol n z = ∫⁻ x in A, Fh x ∂vol n z := by
    refine setLIntegral_congr_fun hAm (fun x hx => ?_)
    have hxs : x ∈ e.source := hx.1.1
    have hj := sh_jac n z g hg e he (e x) (e.map_source hxs)
    rw [e.left_inv hxs] at hj
    simp only [hFh, hj, he hxs, hGdef]

  have step2 : ∫⁻ x in A, Fh x ∂vol n z = ∫⁻ y in e.target, A.indicator Fh (e.symm y) := by
    rw [← lintegral_indicator hAm]
    exact lintegral_vol_chart n z hz e he _ (hFm.indicator hAm)
      (fun x hx => indicator_of_notMem (fun h => hx h.1.1) _)

  have step3 : ∫⁻ y in e.target, A.indicator Fh (e.symm y) ≤ ∫⁻ y in e.target, U'.indicator h2f y := by
    refine setLIntegral_mono' e.open_target.measurableSet (fun y hy => ?_)
    by_cases hA : e.symm y ∈ A
    swap
    · rw [indicator_of_notMem hA]; exact zero_le
    have hey : e (e.symm y) = y := e.right_inv hy
    have hzy : z (e.symm y) = y := chart_z_symm n z e he y hy
    have hyb : y ∈ ball (e p) ρ1 := by
      have h := hA.1.2
      simp only [mem_preimage, hey] at h
      exact h
    have hsh : ε ^ 2 / 2 ≤ ev n g ph r (e.symm y) ∧ ev n g ph r (e.symm y) ≤ ε ^ 2 := hA.2
    have hGS : ‖G y‖ ^ 2 = ∑ i, ‖g i (e.symm y)‖ ^ 2 := shG_norm_sq n g e.symm y
    set x := e.symm y with hxdef
    set S := ∑ i, ‖g i x‖ ^ 2 with hS
    have hevx : ev n g ph r x = S * Real.exp (-ph x) / r ^ 2 := rfl
    have hSev : S = ev n g ph r x * r ^ 2 * Real.exp (ph x) := by
      rw [hevx, Real.exp_neg]; field_simp
    have hevpos : 0 < ev n g ph r x := lt_of_lt_of_le (by positivity) hsh.1
    have hSpos : 0 < S := by
      rw [hSev]; exact mul_pos (mul_pos hevpos (by positivity)) (Real.exp_pos _)
    have hd0 : dist y (e p) < δ0 := lt_of_lt_of_le (mem_ball.1 hyb) (min_le_right _ _)
    have hph0 := h0 hd0
    rw [hsp, Real.dist_eq, abs_lt] at hph0
    have hSle : S ≤ ε ^ 2 * C0 := by
      rw [hSev, hC0]
      have h3 : Real.exp (ph x) ≤ Real.exp (ph p + 1) := Real.exp_le_exp.2 (by linarith)
      calc ev n g ph r x * r ^ 2 * Real.exp (ph x) ≤ ε ^ 2 * r ^ 2 * Real.exp (ph p + 1) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hsh.2 (by positivity)) h3 (by positivity)
              (by positivity)
        _ = ε ^ 2 * (r ^ 2 * Real.exp (ph p + 1)) := by ring
    have hGk : ‖G y‖ < κ := by
      have h3 : ‖G y‖ ^ 2 < κ ^ 2 := by rw [hGS]; linarith
      exact lt_of_pow_lt_pow_left₀ 2 hκ.le h3
    have hyU : y ∈ U' := hκs y (ball_subset_ball (min_le_left _ _) hyb) hGk
    have hd1 : dist y (e p) < δ1 :=
      lt_of_lt_of_le (mem_ball.1 hyU) ((min_le_left _ _).trans (min_le_left _ _))
    have hd2 : dist y (e p) < δ2 :=
      lt_of_lt_of_le (mem_ball.1 hyU) ((min_le_left _ _).trans (min_le_right _ _))
    have hph1 := h1 hd1
    have hph2' := h2 hd2
    rw [hsp, Real.dist_eq, abs_lt] at hph1 hph2'
    have hGA : G y ∈ Ann := by
      refine ⟨?_, ?_⟩ <;> rw [hGS, hSev]
      · calc a = ε ^ 2 / 2 * r ^ 2 * Real.exp (ph p - θ) := by rw [hadef]; ring
          _ ≤ ev n g ph r x * r ^ 2 * Real.exp (ph x) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hsh.1 (by positivity))
              (Real.exp_le_exp.2 (by linarith)) (by positivity) (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_right hsh.2 (by positivity))
          (Real.exp_le_exp.2 (by linarith)) (by positivity) (by positivity)
    rw [indicator_of_mem hA, indicator_of_mem hyU]
    simp only [hFh, hh2, hfdef, indicator_of_mem hGA, hzy]
    rw [← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hGS, hevx, mul_assoc, sh_val n j S r (ph x) (ph2 x) hSpos hr]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hK]
    have hexp : Real.exp (-ph2 x - (j : ℝ) * ph x) ≤
        Real.exp (-ph2 p - (j : ℝ) * ph p) * Real.exp θ := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    have hSn : 0 ≤ S ^ (-(n : ℝ)) := Real.rpow_nonneg hSpos.le _
    calc r ^ (2 * n) * Real.exp (-ph2 x - (j : ℝ) * ph x) * S ^ (-(n : ℝ)) ≤
          r ^ (2 * n) * (Real.exp (-ph2 p - (j : ℝ) * ph p) * Real.exp θ) * S ^ (-(n : ℝ)) := by
          gcongr
      _ = _ := by ring
  have step4 : ∫⁻ y in e.target, U'.indicator h2f y ≤ ∫⁻ w in G '' U', f w := by
    refine (setLIntegral_le_lintegral _ _).trans ?_
    rw [lintegral_indicator measurableSet_ball]
    rw [hCov U' G f isOpen_ball
      (((shG_contDiffOn n z g hg e he).differentiableOn (by simp)).mono (hU'ρ.trans hbt))
      (hinj.mono hU'ρ) hfm]
  have step5 : ∫⁻ w in G '' U', f w ≤ ENNReal.ofReal K *
      ENNReal.ofReal (Real.pi ^ n / (Nat.factorial (n - 1) : ℝ) * Real.log (b / a)) := by
    refine (setLIntegral_le_lintegral _ _).trans (le_of_eq ?_)
    rw [lintegral_const_mul _ (hfm'.indicator hAnnm), lintegral_indicator hAnnm, hP hn a b ha hab]
  rw [step1, step2]
  refine step3.trans (step4.trans (step5.trans ?_))
  rw [← ENNReal.ofReal_mul hK0]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hba, Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp, hK]
  have hnum := sh_num τ hτ
  rw [← hθdef] at hnum
  have hX : 0 ≤ r ^ (2 * n) * Real.exp (-ph2 p - (j : ℝ) * ph p) *
      (Real.pi ^ n / (Nat.factorial (n - 1) : ℝ)) := by positivity
  calc r ^ (2 * n) * Real.exp (-ph2 p - (j : ℝ) * ph p) * Real.exp θ *
        (Real.pi ^ n / (Nat.factorial (n - 1) : ℝ) * (Real.log 2 + 2 * θ))
      = (r ^ (2 * n) * Real.exp (-ph2 p - (j : ℝ) * ph p) *
        (Real.pi ^ n / (Nat.factorial (n - 1) : ℝ))) * (Real.exp θ * (Real.log 2 + 2 * θ)) := by ring
    _ ≤ (r ^ (2 * n) * Real.exp (-ph2 p - (j : ℝ) * ph p) *
        (Real.pi ^ n / (Nat.factorial (n - 1) : ℝ))) * ((1 + τ) * Real.log 2) :=
        mul_le_mul_of_nonneg_left hnum hX
    _ = _ := by ring

end ReciprocityTheory.L2DbarEstimates.I
end

