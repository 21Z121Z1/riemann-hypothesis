import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset
import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement

-- bundled from ReciprocityTheory.L2DbarEstimates.ChartDerivatives.CommFderivApply
section
namespace ReciprocityTheory.L2DbarEstimates

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

noncomputable section

theorem comm_fderiv_apply {n : ℕ} (g : V n → ℂ) (y : V n) (hg : ContDiffAt ℝ 2 g y) (u : V n) :
    HasFDerivAt (fun y' => fderiv ℝ g y' u)
      ((ContinuousLinearMap.apply ℝ ℂ u).comp (fderiv ℝ (fderiv ℝ g) y)) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ g) y := hg.fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ g) y := h1.differentiableAt one_ne_zero
  exact (ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt.comp y hd.hasFDerivAt

theorem comm_fderiv_wd {n : ℕ} (g : V n → ℂ) (y : V n) (hg : ContDiffAt ℝ 2 g y) (j : Fin n) (v : V n) :
    fderiv ℝ (wd n j g) y v = (fderiv ℝ (fderiv ℝ g) y v (bas n j)
      - Complex.I * fderiv ℝ (fderiv ℝ g) y v (Complex.I • bas n j)) * (2 : ℂ)⁻¹ := by
  have hA := comm_fderiv_apply g y hg (bas n j)
  have hB := comm_fderiv_apply g y hg (Complex.I • bas n j)
  have hW : HasFDerivAt (fun y' => (2 : ℂ)⁻¹ • (fderiv ℝ g y' (bas n j)
      - Complex.I • fderiv ℝ g y' (Complex.I • bas n j))) _ y := (hA.sub (hB.const_smul Complex.I)).const_smul (2 : ℂ)⁻¹
  have hfun : wd n j g = fun y' => (2 : ℂ)⁻¹ • (fderiv ℝ g y' (bas n j)
      - Complex.I • fderiv ℝ g y' (Complex.I • bas n j)) := by
    funext y'
    simp only [wd, smul_eq_mul]
    ring
  rw [hfun, hW.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

theorem comm_fderiv_wdb {n : ℕ} (g : V n → ℂ) (y : V n) (hg : ContDiffAt ℝ 2 g y) (j : Fin n) (v : V n) :
    fderiv ℝ (wdb n j g) y v = (fderiv ℝ (fderiv ℝ g) y v (bas n j)
      + Complex.I * fderiv ℝ (fderiv ℝ g) y v (Complex.I • bas n j)) * (2 : ℂ)⁻¹ := by
  have hA := comm_fderiv_apply g y hg (bas n j)
  have hB := comm_fderiv_apply g y hg (Complex.I • bas n j)
  have hW : HasFDerivAt (fun y' => (2 : ℂ)⁻¹ • (fderiv ℝ g y' (bas n j)
      + Complex.I • fderiv ℝ g y' (Complex.I • bas n j))) _ y := (hA.add (hB.const_smul Complex.I)).const_smul (2 : ℂ)⁻¹
  have hfun : wdb n j g = fun y' => (2 : ℂ)⁻¹ • (fderiv ℝ g y' (bas n j)
      + Complex.I • fderiv ℝ g y' (Complex.I • bas n j)) := by
    funext y'
    simp only [wdb, smul_eq_mul]
    ring
  rw [hfun, hW.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

theorem comm_wd_wdb {n : ℕ} (g : V n → ℂ) (y : V n) (hg : ContDiffAt ℝ 2 g y) (j k : Fin n) :
    wd n j (wdb n k g) y = wdb n k (wd n j g) y := by
  have S := hg.isSymmSndFDerivAt (by simp)
  have e1 : wd n j (wdb n k g) y = (fderiv ℝ (wdb n k g) y (bas n j)
      - Complex.I * fderiv ℝ (wdb n k g) y (Complex.I • bas n j)) / 2 := rfl
  have e2 : wdb n k (wd n j g) y = (fderiv ℝ (wd n j g) y (bas n k)
      + Complex.I * fderiv ℝ (wd n j g) y (Complex.I • bas n k)) / 2 := rfl
  rw [e1, e2, comm_fderiv_wdb g y hg k (bas n j), comm_fderiv_wdb g y hg k (Complex.I • bas n j),
    comm_fderiv_wd g y hg j (bas n k), comm_fderiv_wd g y hg j (Complex.I • bas n k),
    S (bas n k) (bas n j), S (bas n k) (Complex.I • bas n j),
    S (Complex.I • bas n k) (bas n j), S (Complex.I • bas n k) (Complex.I • bas n j)]
  ring

theorem comm_wd_wd {n : ℕ} (g : V n → ℂ) (y : V n) (hg : ContDiffAt ℝ 2 g y) (j k : Fin n) :
    wd n j (wd n k g) y = wd n k (wd n j g) y := by
  have S := hg.isSymmSndFDerivAt (by simp)
  have e1 : wd n j (wd n k g) y = (fderiv ℝ (wd n k g) y (bas n j)
      - Complex.I * fderiv ℝ (wd n k g) y (Complex.I • bas n j)) / 2 := rfl
  have e2 : wd n k (wd n j g) y = (fderiv ℝ (wd n j g) y (bas n k)
      - Complex.I * fderiv ℝ (wd n j g) y (Complex.I • bas n k)) / 2 := rfl
  rw [e1, e2, comm_fderiv_wd g y hg k (bas n j), comm_fderiv_wd g y hg k (Complex.I • bas n j),
    comm_fderiv_wd g y hg j (bas n k), comm_fderiv_wd g y hg j (Complex.I • bas n k),
    S (bas n k) (bas n j), S (bas n k) (Complex.I • bas n j),
    S (Complex.I • bas n k) (bas n j), S (Complex.I • bas n k) (Complex.I • bas n j)]
  ring

theorem comm_wdb_wdb {n : ℕ} (g : V n → ℂ) (y : V n) (hg : ContDiffAt ℝ 2 g y) (j k : Fin n) :
    wdb n j (wdb n k g) y = wdb n k (wdb n j g) y := by
  have S := hg.isSymmSndFDerivAt (by simp)
  have e1 : wdb n j (wdb n k g) y = (fderiv ℝ (wdb n k g) y (bas n j)
      + Complex.I * fderiv ℝ (wdb n k g) y (Complex.I • bas n j)) / 2 := rfl
  have e2 : wdb n k (wdb n j g) y = (fderiv ℝ (wdb n j g) y (bas n k)
      + Complex.I * fderiv ℝ (wdb n j g) y (Complex.I • bas n k)) / 2 := rfl
  rw [e1, e2, comm_fderiv_wdb g y hg k (bas n j), comm_fderiv_wdb g y hg k (Complex.I • bas n j),
    comm_fderiv_wdb g y hg j (bas n k), comm_fderiv_wdb g y hg j (Complex.I • bas n k),
    S (bas n k) (bas n j), S (bas n k) (Complex.I • bas n j),
    S (Complex.I • bas n k) (bas n j), S (Complex.I • bas n k) (Complex.I • bas n j)]
  ring

private theorem chart_symm_eventuallyEq_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (he' : IsChart n z e') (y : M)
    (hy : y ∈ e.source) (hy' : y ∈ e'.source) : (e'.symm : V n → M) =ᶠ[𝓝 (z y)] e.symm := by
  have hzy : z y = e' y := he' hy'
  have ht : z y ∈ e'.target := by rw [hzy]; exact e'.map_source hy'
  have hc : ContinuousAt e'.symm (z y) := e'.continuousAt_symm ht
  have hs : e.source ∈ 𝓝 (e'.symm (z y)) := by
    rw [hzy, e'.left_inv hy']; exact e.open_source.mem_nhds hy
  filter_upwards [e'.open_target.mem_nhds ht, hc hs] with w hw hw2
  have h1 : e (e'.symm w) = w := by
    rw [← he hw2, he' (e'.map_target hw), e'.right_inv hw]
  calc e'.symm w = e.symm (e (e'.symm w)) := (e.left_inv hw2).symm
    _ = e.symm w := by rw [h1]

private theorem d_apply_eq_wd_comp_chart_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M)
    (hy : y ∈ e.source) : d n z j f y = wd n j (f ∘ e.symm) (z y) := by
  have h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  have hg : (f ∘ (Classical.choose h).symm) =ᶠ[𝓝 (z y)] (f ∘ e.symm) :=
    (chart_symm_eventuallyEq_symm n z e _ he (Classical.choose_spec h).1 y hy
      (Classical.choose_spec h).2).fun_comp f
  simp only [d, dif_pos h, wd, hg.fderiv_eq]

private theorem db_apply_eq_wdb_comp_chart_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M)
    (hy : y ∈ e.source) : db n z j f y = wdb n j (f ∘ e.symm) (z y) := by
  have h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  have hg : (f ∘ (Classical.choose h).symm) =ᶠ[𝓝 (z y)] (f ∘ e.symm) :=
    (chart_symm_eventuallyEq_symm n z e _ he (Classical.choose_spec h).1 y hy
      (Classical.choose_spec h).2).fun_comp f
  simp only [db, dif_pos h, wdb, hg.fderiv_eq]

theorem comm_chart_setup {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ)
    (hf : Ck n z 2 f) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (x : M)
    (hx : x ∈ e.source) :
    z x ∈ e.target ∧ ContDiffAt ℝ 2 (f ∘ e.symm) (z x) ∧
      (∀ j, (d n z j f ∘ e.symm) =ᶠ[𝓝 (z x)] wd n j (f ∘ e.symm)) ∧
      (∀ j, (db n z j f ∘ e.symm) =ᶠ[𝓝 (z x)] wdb n j (f ∘ e.symm)) := by
  have h1 : z x ∈ e.target := by rw [he hx]; exact e.map_source hx
  refine ⟨h1, ?_, ?_, ?_⟩
  · have h2 := (hf e he).contDiffAt (e.open_target.mem_nhds h1)
    exact_mod_cast h2
  · intro j
    filter_upwards [e.open_target.mem_nhds h1] with w hw
    have hs : e.symm w ∈ e.source := e.map_target hw
    show d n z j f (e.symm w) = wd n j (f ∘ e.symm) w
    rw [d_apply_eq_wd_comp_chart_symm n z j f e he _ hs, he hs, e.right_inv hw]
  · intro j
    filter_upwards [e.open_target.mem_nhds h1] with w hw
    have hs : e.symm w ∈ e.source := e.map_target hw
    show db n z j f (e.symm w) = wdb n j (f ∘ e.symm) w
    rw [db_apply_eq_wdb_comp_chart_symm n z j f e he _ hs, he hs, e.right_inv hw]

private theorem wd_congr_of_eventuallyEq' (n : ℕ) (j : Fin n) {g h : V n → ℂ} {w : V n}
    (hgh : g =ᶠ[𝓝 w] h) : wd n j g w = wd n j h w := by
  simp only [wd, hgh.fderiv_eq]

private theorem wdb_congr_of_eventuallyEq (n : ℕ) (j : Fin n) {g h : V n → ℂ} {w : V n}
    (hgh : g =ᶠ[𝓝 w] h) : wdb n j g w = wdb n j h w := by
  simp only [wdb, hgh.fderiv_eq]

theorem d_db_comm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (hf : Ck n z 2 f) (j k : Fin n) (x : M) :
    d n z j (db n z k f) x = db n z k (d n z j f) x := by
  by_cases h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source
  · obtain ⟨e, he, hx⟩ := h
    obtain ⟨_, h2, h3, h4⟩ := comm_chart_setup n z f hf e he x hx
    rw [d_apply_eq_wd_comp_chart_symm n z j _ e he x hx, db_apply_eq_wdb_comp_chart_symm n z k _ e he x hx,
      wd_congr_of_eventuallyEq' n j (h4 k), wdb_congr_of_eventuallyEq n k (h3 j)]
    exact comm_wd_wdb _ _ h2 j k
  · simp [d, db, h]

theorem levi_add {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph ps : M → ℝ) (hph : CkR n z 2 ph) (hps : CkR n z 2 ps) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => ph y + ps y) x ξ = Levi n z ph x ξ + Levi n z ps x ξ := by
  have hph1 : Ck n z 1 (fun y => (ph y : ℂ)) := fun e he => (hph e he).of_le (by norm_num)
  have hps1 : Ck n z 1 (fun y => (ps y : ℂ)) := fun e he => (hps e he).of_le (by norm_num)
  have e1 : (fun y => ((ph y + ps y : ℝ) : ℂ)) = fun y => (ph y : ℂ) + (ps y : ℂ) := by
    funext y; exact Complex.ofReal_add _ _
  have h1 : ∀ k, db n z k (fun y => ((ph y + ps y : ℝ) : ℂ)) =
      fun y => db n z k (fun y => (ph y : ℂ)) y + db n z k (fun y => (ps y : ℂ)) y := by
    intro k; funext y; rw [e1]; exact db_add n z _ _ hph1 hps1 k y
  have h2 : ∀ j k, d n z j (db n z k (fun y => ((ph y + ps y : ℝ) : ℂ))) x =
      d n z j (db n z k (fun y => (ph y : ℂ))) x + d n z j (db n z k (fun y => (ps y : ℂ))) x := by
    intro j k; rw [h1 k]; exact d_add n z _ _ (Ck.db n z 1 k _ hph) (Ck.db n z 1 k _ hps) j x
  simp only [Levi, h2, add_mul, Finset.sum_add_distrib]

theorem levi_const_mul {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℝ) (ph : M → ℝ) (hph : CkR n z 2 ph) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => c * ph y) x ξ = (c : ℂ) * Levi n z ph x ξ := by
  have hph1 : Ck n z 1 (fun y => (ph y : ℂ)) := fun e he => (hph e he).of_le (by norm_num)
  have e1 : (fun y => ((c * ph y : ℝ) : ℂ)) = fun y => (c : ℂ) * (ph y : ℂ) := by
    funext y; exact Complex.ofReal_mul _ _
  have h1 : ∀ k, db n z k (fun y => ((c * ph y : ℝ) : ℂ)) =
      fun y => (c : ℂ) * db n z k (fun y => (ph y : ℂ)) y := by
    intro k; funext y; rw [e1]; exact db_const_mul n z _ _ hph1 k y
  have h2 : ∀ j k, d n z j (db n z k (fun y => ((c * ph y : ℝ) : ℂ))) x =
      (c : ℂ) * d n z j (db n z k (fun y => (ph y : ℂ))) x := by
    intro j k; rw [h1 k]; exact d_const_mul n z _ _ (Ck.db n z 1 k _ hph) j x
  simp only [Levi, h2, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  ring

theorem levi_normSq {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : M → ℂ) (hg : Holo n z g) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => ‖g y‖ ^ 2) x ξ = ((‖dDot n z g x ξ‖ ^ 2 : ℝ) : ℂ) := by
  have hs : Smooth n z g := Holo.smooth n z g hg
  have hC : ∀ k, Ck n z k g := fun k => Smooth.ck n z k g hs
  have hconj : ∀ k, Ck n z k (fun y => (starRingEnd ℂ) (g y)) := fun k => Ck.conj n z k g (hC k)
  have e0 : (fun y => ((‖g y‖ ^ 2 : ℝ) : ℂ)) = fun y => g y * (starRingEnd ℂ) (g y) := by
    funext y; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hdb : ∀ k, db n z k (fun y => ((‖g y‖ ^ 2 : ℝ) : ℂ)) =
      fun y => g y * (starRingEnd ℂ) (d n z k g y) := by
    intro k; funext y
    rw [e0, db_mul n z _ _ (hC 1) (hconj 1) k y, Holo.db_eq_zero n z g hg k y, db_conj]
    ring
  have hdb0 : ∀ j, db n z j g = fun _ => 0 := fun j => funext (Holo.db_eq_zero n z g hg j)
  have hd : ∀ j k, d n z j (db n z k (fun y => ((‖g y‖ ^ 2 : ℝ) : ℂ))) x =
      d n z j g x * (starRingEnd ℂ) (d n z k g x) := by
    intro j k
    rw [hdb k, d_mul n z _ _ (hC 1) (Ck.conj n z 1 _ (Ck.d n z 1 k g (hC _))) j x, d_conj,
      ← d_db_comm n z g (hC 2) k j x, hdb0 j, d_const]
    simp
  simp only [Levi, hd, dDot]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  simp only [map_mul]
  ring

end

end ReciprocityTheory.L2DbarEstimates
end

-- bundled from ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ExistsChartPartition
section
namespace ReciprocityTheory.L2DbarEstimates

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

noncomputable section

theorem smoothR_const {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (c : ℝ) :
    SmoothR n z (fun _ => c) := by
  exact fun _ _ => contDiffOn_const

theorem smoothR_prod {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (f : ι → M → ℝ) (hf : ∀ i ∈ s, SmoothR n z (f i)) :
    SmoothR n z (fun x => ∏ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using smoothR_const n z 1
  | @insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have h3 := SmoothR.mul n z _ _ h1 h2
    simpa [Finset.prod_insert ha] using h3

theorem smoothR_sum {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (f : ι → M → ℝ) (hf : ∀ i ∈ s, SmoothR n z (f i)) :
    SmoothR n z (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using smoothR_const n z 0
  | @insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have h3 := SmoothR.add n z _ _ h1 h2
    simpa [Finset.sum_insert ha] using h3

theorem exists_chart_bump {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (U : Set M) (hU : IsOpen U) (x : M) (hx : x ∈ U) :
    ∃ (e : OpenPartialHomeomorph M (V n)) (ψ : M → ℝ),
      IsChart n z e ∧ SmoothR n z ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ e.source ∩ U ∧
      (∀ y, 0 ≤ ψ y ∧ ψ y ≤ 1) ∧ ∀ᶠ y in 𝓝 x, ψ y = 1 := by
  have hz' : ∀ y, ∃ e : OpenPartialHomeomorph M (V n), y ∈ e.source ∧ z = e := hz
  obtain ⟨e, hxe, hze⟩ := hz' x
  have he : IsChart n z e := fun y _ => congrFun hze y
  have hO : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hU
  have hxO : e x ∈ e.target ∩ e.symm ⁻¹' U := ⟨e.map_source hxe, by simp [e.left_inv hxe, hx]⟩
  obtain ⟨r, hr, hrO⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds hxO)
  let φ : ContDiffBump (e x) := ⟨r / 2, r, by positivity, by linarith⟩
  let ψ : M → ℝ := e.source.indicator (fun y => φ (e y))
  set K := e.symm '' Metric.closedBall (e x) r with hKdef
  have hKt : Metric.closedBall (e x) r ⊆ e.target := fun w hw => (hrO hw).1
  have hKc : IsCompact K :=
    (isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn_symm.mono hKt)
  have hKs : K ⊆ e.source ∩ U := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨e.map_target (hrO hw).1, (hrO hw).2⟩
  have hsupp : Function.support ψ ⊆ K := by
    intro y hy
    rw [Function.mem_support] at hy
    by_cases hys : y ∈ e.source
    · have h1 : φ (e y) ≠ 0 := by simpa [ψ, Set.indicator_of_mem hys] using hy
      have h2 : e y ∈ Metric.ball (e x) r := by
        rw [← φ.support_eq]; exact h1
      exact ⟨e y, Metric.ball_subset_closedBall h2, e.left_inv hys⟩
    · exact absurd (by simp [ψ, Set.indicator_apply, hys]) hy
  have htsK : tsupport ψ ⊆ K := closure_minimal hsupp hKc.isClosed
  refine ⟨e, ψ, he, ?_, hKc.of_isClosed_subset (isClosed_tsupport _) htsK, htsK.trans hKs,
    fun y => ?_, ?_⟩
  · intro e' he' w hw
    refine ContDiffAt.contDiffWithinAt ?_
    by_cases hys : e'.symm w ∈ e.source
    · have hc := e'.continuousAt_symm hw
      have h1 : (fun y => (ψ y : ℂ)) ∘ e'.symm =ᶠ[𝓝 w] fun w' => ((φ w' : ℝ) : ℂ) := by
        filter_upwards [e'.open_target.mem_nhds hw, hc (e.open_source.mem_nhds hys)] with w' hw' hw2
        have h2 : e (e'.symm w') = w' := by
          rw [← congrFun hze, he' (e'.map_target hw'), e'.right_inv hw']
        have hw3 : e'.symm w' ∈ e.source := hw2
        simp only [Function.comp_apply, ψ, Set.indicator_of_mem hw3, h2]
      have h3 : ContDiff ℝ ∞ (fun w' => ((φ w' : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp φ.contDiff
      exact h3.contDiffAt.congr_of_eventuallyEq h1
    · have hc := e'.continuousAt_symm hw
      have hyK : e'.symm w ∉ K := fun h => hys (hKs h).1
      have h1 : (fun y => (ψ y : ℂ)) ∘ e'.symm =ᶠ[𝓝 w] fun _ => (0 : ℂ) := by
        filter_upwards [hc (hKc.isClosed.isOpen_compl.mem_nhds hyK)] with w' hw'
        have h2 : ψ (e'.symm w') = 0 := Function.notMem_support.mp (fun h => hw' (hsupp h))
        simp [h2]
      exact contDiffAt_const.congr_of_eventuallyEq h1
  · by_cases hys : y ∈ e.source
    · simp only [ψ, Set.indicator_of_mem hys]
      exact ⟨φ.nonneg, φ.le_one⟩
    · simp [ψ, Set.indicator_apply, hys]
  · have h1 : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e x) (r / 2)) :=
      e.isOpen_inter_preimage Metric.isOpen_ball
    filter_upwards [h1.mem_nhds ⟨hxe, Metric.mem_ball_self (by positivity)⟩] with y hy
    simp only [ψ, Set.indicator_of_mem hy.1]
    exact φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy.2)

theorem exists_chart_partition {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (K U : Set M) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (N : ℕ) (e : Fin N → OpenPartialHomeomorph M (V n)) (χ : Fin N → M → ℝ),
      (∀ i, IsChart n z (e i)) ∧ (∀ i, SmoothR n z (χ i)) ∧ (∀ i, HasCompactSupport (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆ (e i).source ∩ U) ∧ (∀ i x, 0 ≤ χ i x) ∧
      (∀ x, ∑ i, χ i x ≤ 1) ∧ (∀ x ∈ K, ∑ i, χ i x = 1) := by
  classical
  have hz' : ∀ y, ∃ e : OpenPartialHomeomorph M (V n), y ∈ e.source ∧ z = e := hz
  have H : ∀ x, ∃ (e : OpenPartialHomeomorph M (V n)) (ψ : M → ℝ), x ∈ U →
      IsChart n z e ∧ SmoothR n z ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ e.source ∩ U ∧
      (∀ y, 0 ≤ ψ y ∧ ψ y ≤ 1) ∧ ∀ᶠ y in 𝓝 x, ψ y = 1 := by
    intro x
    by_cases hx : x ∈ U
    · obtain ⟨e, ψ, h⟩ := exists_chart_bump n z hz U hU x hx
      exact ⟨e, ψ, fun _ => h⟩
    · obtain ⟨e0, -, -⟩ := hz' x
      exact ⟨e0, fun _ => 0, fun h => absurd h hx⟩
  choose e ψ hψ using H
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => {y | ψ x y = 1})
    (fun x hx => (hψ x (hKU hx)).2.2.2.2.2)
  let g : Fin t.card → M := fun i => (t.equivFin.symm i : M)
  have hgU : ∀ i, g i ∈ U := fun i => hKU (htK _ (t.equivFin.symm i).2)
  have P := fun i => hψ (g i) (hgU i)
  have h1 : ∀ j, SmoothR n z (fun y => 1 - ψ (g j) y) := by
    intro j
    have h2 := SmoothR.add n z _ _ (smoothR_const n z 1)
      (SmoothR.mul n z _ _ (smoothR_const n z (-1)) (P j).2.1)
    have h3 : (fun y => 1 - ψ (g j) y) = fun y => 1 + (-1) * ψ (g j) y := by funext y; ring
    rw [h3]; exact h2
  have hsum : ∀ y, ∑ i, ψ (g i) y * ∏ j ∈ Finset.univ.filter (fun j => j < i), (1 - ψ (g j) y) =
      1 - ∏ i, (1 - ψ (g i) y) := by
    intro y
    have h4 := Finset.prod_one_sub_ordered (Finset.univ : Finset (Fin t.card)) (fun i => ψ (g i) y)
    beta_reduce at h4
    linarith
  have hprod : ∀ y, 0 ≤ ∏ i, (1 - ψ (g i) y) :=
    fun y => Finset.prod_nonneg fun j _ => sub_nonneg.2 ((P j).2.2.2.2.1 y).2
  refine ⟨t.card, fun i => e (g i),
    fun i y => ψ (g i) y * ∏ j ∈ Finset.univ.filter (fun j => j < i), (1 - ψ (g j) y),
    fun i => (P i).1, fun i => ?_, fun i => ?_, fun i => ?_, fun i x => ?_, fun x => ?_,
    fun x hx => ?_⟩
  · exact SmoothR.mul n z _ _ (P i).2.1
      (smoothR_prod n z (Finset.univ.filter (fun j => j < i)) (fun j y => 1 - ψ (g j) y)
        (fun j _ => h1 j))
  · exact HasCompactSupport.mul_right
      (f' := fun y => ∏ j ∈ Finset.univ.filter (fun j => j < i), (1 - ψ (g j) y)) (P i).2.2.1
  · exact tsupport_mul_subset_left.trans (P i).2.2.2.1
  · exact mul_nonneg ((P i).2.2.2.2.1 x).1
      (Finset.prod_nonneg fun j _ => sub_nonneg.2 ((P j).2.2.2.2.1 x).2)
  · rw [hsum x]
    linarith [hprod x]
  · rw [hsum x]
    obtain ⟨x', hx't, hx'⟩ := Set.mem_iUnion₂.1 (hcov hx)
    have hi : g (t.equivFin ⟨x', hx't⟩) = x' := by simp [g]
    have h0 : ∏ i, (1 - ψ (g i) x) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ (t.equivFin ⟨x', hx't⟩))
      simp only [Set.mem_setOf_eq] at hx'
      rw [hi, hx', sub_self]
    rw [h0, sub_zero]

theorem exists_cutoff {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (K U : Set M) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ η : M → ℝ, SmoothR n z η ∧ HasCompactSupport η ∧ tsupport η ⊆ U ∧
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧ ∀ x ∈ K, η x = 1 := by
  obtain ⟨N, e, χ, he, hs, hc, hts, h0, h1, hK1⟩ := exists_chart_partition n z hz K U hK hU hKU
  have hS : tsupport (fun x => ∑ i, χ i x) ⊆ ⋃ i, tsupport (χ i) := by
    refine closure_minimal ?_ (isClosed_iUnion_of_finite fun i => isClosed_tsupport _)
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    exact Set.mem_iUnion.2 ⟨i, subset_tsupport _ hi⟩
  refine ⟨fun x => ∑ i, χ i x, smoothR_sum n z Finset.univ χ (fun i _ => hs i),
    (isCompact_iUnion fun i => hc i).of_isClosed_subset (isClosed_tsupport _) hS,
    hS.trans (Set.iUnion_subset fun i => (hts i).trans Set.inter_subset_right),
    fun x => ⟨Finset.sum_nonneg (fun i _ => h0 i x), h1 x⟩, hK1⟩

end

end ReciprocityTheory.L2DbarEstimates
end

-- bundled from ReciprocityTheory.L2DbarEstimates.ChartDerivatives.InhHasFDerivAtNormSq
section
namespace ReciprocityTheory.L2DbarEstimates

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

noncomputable section

theorem inh_hasFDerivAt_normSq (n : ℕ) (y : V n) :
    HasFDerivAt (fun y : V n => ((‖y‖ ^ 2 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (2 • innerSL ℝ y)) y :=
  Complex.ofRealCLM.hasFDerivAt.comp y (hasStrictFDerivAt_norm_sq y).hasFDerivAt

theorem inh_wdb_normSq (n : ℕ) (k : Fin n) :
    wdb n k (fun y : V n => ((‖y‖ ^ 2 : ℝ) : ℂ)) = fun y => y k := by
  funext y
  unfold wdb
  rw [(inh_hasFDerivAt_normSq n y).fderiv]
  have hr : ∀ v : V n, (inner ℝ y v : ℝ) = (inner ℂ y v).re := fun v => by
    simp [PiLp.inner_apply, Complex.re_sum]
  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply,
    innerSL_apply_apply, Complex.ofRealCLM_apply, bas, hr, EuclideanSpace.inner_single_right,
    inner_smul_right, nsmul_eq_mul]
  apply Complex.ext <;> simp

theorem inh_wd_coord (n : ℕ) (j k : Fin n) (y : V n) :
    wd n j (fun y : V n => y k) y = if j = k then 1 else 0 := by
  have h : (fun y : V n => y k) = ⇑((EuclideanSpace.proj k : V n →L[ℂ] ℂ).restrictScalars ℝ) := by
    funext y; simp
  unfold wd
  rw [h, ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars', bas]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk, Ne.symm hjk]

theorem inh_isChart_refl (n : ℕ) : IsChart n id (OpenPartialHomeomorph.refl (V n)) :=
  fun _ _ => rfl

theorem etaleStein_nonempty (n : ℕ) :
    InhabitedStatement n := by
  refine ⟨{ z := id
            isLocalHomeomorph := (Homeomorph.refl (V n)).isLocalHomeomorph
            e := fun y => ‖y‖ ^ 2
            smooth_e := ?_
            levi_e := ?_
            isCompact_le := ?_ }⟩
  · intro e he
    have hg : ContDiff ℝ ∞ (fun y : V n => ((‖y‖ ^ 2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_norm_sq ℂ)
    refine hg.contDiffOn.congr fun y hy => ?_
    have h1 := chart_z_symm n id e he y hy
    simp only [id] at h1
    simp [Function.comp, h1]
  · intro x ξ
    rw [levi_eq_leviV n id _ (inh_isChart_refl n) _ x (Set.mem_univ x) ξ]
    unfold leviV
    simp only [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id]
    simp_rw [inh_wdb_normSq, inh_wd_coord]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun j _ => ?_
    rw [Complex.mul_conj]
    simp [Complex.normSq_nonneg]
  · intro a
    refine Metric.isCompact_of_isClosed_isBounded
      (isClosed_le (continuous_norm.pow 2) continuous_const) ?_
    refine isBounded_iff_forall_norm_le.2 ⟨max 1 a, fun x hx => ?_⟩
    simp only [Set.mem_ofPred_eq] at hx
    by_cases h : ‖x‖ ≤ 1
    · exact le_max_of_le_left h
    · push Not at h
      exact le_max_of_le_right (by nlinarith)

end

end ReciprocityTheory.L2DbarEstimates
end

