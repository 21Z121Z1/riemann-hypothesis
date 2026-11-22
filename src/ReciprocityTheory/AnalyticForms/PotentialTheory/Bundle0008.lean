import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
import ReciprocityTheory.AnalyticForms.PotentialTheory.PushAFinsumInter

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
section
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff ComplexOrder

noncomputable section

section Chart

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem potential_contDiffAt (A : FinHolAtlas e X) (P : LocPot X) (hP : IsPotential A P)
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) :
    ContDiffAt ℝ 2 (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
  have h := hP.1 ((A.chart j).symm y) j
  have hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U ((A.chart j).symm y) ∈ 𝓝 y :=
    ((A.chart j).isOpen_inter_preimage_symm (P.isOpen_U _)).mem_nhds ⟨hy, P.mem_U _⟩
  exact (h.contDiffAt hmem).of_le (by norm_cast)

theorem locDens_cons (A : FinHolAtlas (e + 1) X) (P : LocPot X) (Φ : Fin e → LocPot X)
    (j : Fin A.n) (y : Fin (e + 1) → ℂ) :
    locDens A (Fin.cons P Φ) j y = ((e + 1).factorial : ℝ) * (2 / Real.pi) ^ (e + 1) *
      (mdisc (Fin.cons (hessC (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) y)
        (fun i => hessC (fun y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) :
          Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)).re := by
  unfold locDens maDens
  congr 3
  funext k
  refine Fin.cases ?_ (fun i => ?_) k <;> simp

theorem locDens_cons_rsmul (A : FinHolAtlas (e + 1) X) (c : ℝ) (P : LocPot X)
    (Φ : Fin e → LocPot X) (j : Fin A.n) (y : Fin (e + 1) → ℂ) :
    locDens A (Fin.cons (P.rsmul c) Φ) j y = c * locDens A (Fin.cons P Φ) j y := by
  rw [locDens_cons, locDens_cons]
  have : (fun y' => (P.rsmul c).φ ((A.chart j).symm y) ((A.chart j).symm y')) =
      fun y' => c * P.φ ((A.chart j).symm y) ((A.chart j).symm y') := rfl
  rw [this, hessC_const_mul', mdisc_cons_smul, Complex.re_ofReal_mul]
  ring

theorem locDens_cons_add (A : FinHolAtlas (e + 1) X) (P Q : LocPot X) (Φ : Fin e → LocPot X)
    (hP : IsPotential A P) (hQ : IsPotential A Q) (j : Fin A.n) {y : Fin (e + 1) → ℂ}
    (hy : y ∈ (A.chart j).target) :
    locDens A (Fin.cons (P + Q) Φ) j y =
      locDens A (Fin.cons P Φ) j y + locDens A (Fin.cons Q Φ) j y := by
  rw [locDens_cons, locDens_cons, locDens_cons]
  have : (fun y' => (P + Q).φ ((A.chart j).symm y) ((A.chart j).symm y')) =
      fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y') +
        Q.φ ((A.chart j).symm y) ((A.chart j).symm y') := rfl
  rw [this, hessC_add' _ _ _ (potential_contDiffAt A P hP j hy) (potential_contDiffAt A Q hQ j hy),
    mdisc_cons_add, Complex.add_re]
  ring

theorem locDens_nonneg (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (hψ : ∀ i, IsPsh A (Φ i)) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) : 0 ≤ locDens A Φ j y := by
  unfold locDens
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_
  exact hessC_posSemidef _ _ (potential_contDiffAt A (Φ k) (hΦ k) j hy)
    fun w => hψ k ((A.chart j).symm y) j y ⟨hy, (Φ k).mem_U _⟩ w

theorem integrableOn_weight [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X) (g : X → ℝ) (hg : MIntegrable A Φ g)
    (j : Fin A.n) :
    IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
      locDens A Φ j y) (A.chart j).target := by
  set K := (A.chart j) '' tsupport (P.χ j)
  have hKc : IsCompact K := (isClosed_tsupport _).isCompact.image_of_continuousOn
    ((A.chart j).continuousOn.mono (P.tsupport_subset j))
  have hKt : K ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩; exact (A.chart j).map_source (P.tsupport_subset j hx)
  have hχc : ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target := by
    have := (P.smooth j j).continuousOn
    rw [Set.preimage_univ, Set.inter_univ] at this
    exact this
  have h1 : IntegrableOn (fun y => P.χ j ((A.chart j).symm y) *
      (g ((A.chart j).symm y) * locDens A Φ j y)) K :=
    (hg j K hKt hKc).continuousOn_mul (hχc.mono hKt) hKc
  have h2 := h1.of_forall_sdiff_eq_zero (A.chart j).open_target.measurableSet (by
    rintro y ⟨hy, hyK⟩
    have : (A.chart j).symm y ∉ tsupport (P.χ j) := fun h =>
      hyK ⟨_, h, (A.chart j).right_inv hy⟩
    simp [image_eq_zero_of_notMem_tsupport this])
  simpa only [mul_assoc] using h2

end Chart

private theorem mdisc_comp_perm_potential {D : ℕ} (B : Fin D → Matrix (Fin D) (Fin D) ℂ) (σ : Equiv.Perm (Fin D)) :
    ReciprocityTheory.AnForm.mdisc (B ∘ σ) = ReciprocityTheory.AnForm.mdisc B := by
  classical
  unfold ReciprocityTheory.AnForm.mdisc
  congr 1
  refine Fintype.sum_equiv (Equiv.finsetCongr σ) _ _ fun S => ?_
  simp [Equiv.finsetCongr_apply, Finset.card_map, Finset.sum_map]

theorem mIntSymm : MIntSymmStatement := by
  intro e X _ A Φ σ g
  have hloc : ∀ j y, locDens A (Φ ∘ σ) j y = locDens A Φ j y := by
    intro j y
    unfold locDens maDens
    congr 2
    exact mdisc_comp_perm_potential (fun k => ReciprocityTheory.AnForm.hessC
      (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) σ
  unfold mInt integralWith
  simp only [hloc]

theorem mIntAdd : MIntAddStatement := by
  intro e X _ _ _ A P Q Φ hP hQ hΦ g hgP hgQ
  unfold mInt integralWith
  split_ifs with h
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have i1 := integrableOn_weight A h.some (Fin.cons P Φ) g hgP j
    have i2 := integrableOn_weight A h.some (Fin.cons Q Φ) g hgQ j
    rw [← integral_add i1 i2]
    refine setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    show _ = _ + _
    rw [locDens_cons_add A P Q Φ hP hQ j hy]
    ring
  · simp

theorem mIntRsmul : MIntRsmulStatement := by
  intro e X _ A c P Φ hP hΦ g
  unfold mInt integralWith
  split_ifs with h
  · simp only [locDens_cons_rsmul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  · simp

theorem mIntZsmul : MIntZsmulStatement := by
  intro e X _ A m P Φ hP hΦ g
  exact mIntRsmul A (m : ℝ) P Φ hP hΦ g

theorem mIntLinear : MIntLinearStatement := by
  intro e X _ _ _ A Φ hΦ c g g' hg hg'
  unfold mInt integralWith
  split_ifs with h
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have i1 := integrableOn_weight A h.some Φ g hg j
    have i2 := integrableOn_weight A h.some Φ g' hg' j
    rw [← integral_const_mul, ← integral_add (i1.const_mul c) i2]
    congr 1
    funext y
    ring
  · simp

theorem mIntNonneg : MIntNonnegStatement := by
  intro e X _ A Φ hΦ hψ g hg
  unfold mInt integralWith
  split_ifs with h
  · exact Finset.sum_nonneg fun j _ => setIntegral_nonneg (A.chart j).open_target.measurableSet
      fun y hy => mul_nonneg (mul_nonneg (h.some.nonneg j _) (hg _)) (locDens_nonneg A Φ hΦ hψ j hy)
  · exact le_rfl

end

end ReciprocityTheory.AnForm.M
end

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.PushBForward
section
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology

noncomputable section

theorem pushB_forward : PushForwardStatement := by
  intro e X _ _ _ A Φ hΦ q T S hT hTS hS hint hq hdet hfin g hg
  have hne := existsPartition A
  rw [mInt, dif_pos hne]
  set P := hne.some with hP
  have hSc : IsClosed S := pushA_isClosed A hS
  have hTc : ∀ x, x ∉ S → x ∈ Tᶜ := fun x hx hxT => hx (hTS hxT)
  set h : Fin A.n → X → ℝ := fun j x => P.χ j x * g x * pushDens A Φ q x with hh
  have hO : ∀ j, IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Sᶜ) :=
    fun j => (A.chart j).isOpen_inter_preimage_symm hSc.isOpen_compl
  have hloc : ∀ j, ∀ z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Sᶜ, ∃ W : Set (Fin e → ℂ),
      IsOpen W ∧ z ∈ W ∧ Set.InjOn (q ∘ (A.chart j).symm) W := by
    intro j z hz
    apply pushA_locInj (pushA_analytic A hq j hz.1 (hTc _ hz.2))
    have := hdet _ hz.2 j ((A.chart j).map_target hz.1)
    rwa [(A.chart j).right_inv hz.1] at this
  choose D hDm hDd hDU hDi using fun j => pushA_cover _ (hO j) _ (hloc j)
  have hDO : ∀ j m, D j m ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Sᶜ := by
    intro j m z hz
    rw [← hDU j]
    exact Set.mem_iUnion.2 ⟨m, hz⟩

  have hEq : ∀ j, Set.EqOn (fun z => Complex.normSq (LinearMap.det
        (fderiv ℂ (q ∘ (A.chart j).symm) z : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) *
        h j ((A.chart j).symm z))
      (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Sᶜ) := by
    intro j z hz
    have hd := pushA_dens A Φ hΦ hq j hz.1 (hTc _ hz.2)
      (hdet _ hz.2 (chartIdx A _) (Classical.choose_spec (A.cover _)))
    simp only [hh]
    rw [← hd]
    ring
  have hEqN : ∀ j, Set.EqOn (fun z => Complex.normSq (LinearMap.det
        (fderiv ℂ (q ∘ (A.chart j).symm) z : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) *
        |h j ((A.chart j).symm z)|)
      (fun y => ‖P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y‖)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Sᶜ) := by
    intro j z hz
    have h1 : Complex.normSq (LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) z :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) * h j ((A.chart j).symm z) =
        P.χ j ((A.chart j).symm z) * g ((A.chart j).symm z) * locDens A Φ j z := hEq j hz
    show Complex.normSq (LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) z :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) * |h j ((A.chart j).symm z)| =
      ‖P.χ j ((A.chart j).symm z) * g ((A.chart j).symm z) * locDens A Φ j z‖
    rw [← h1, Real.norm_eq_abs, abs_mul (Complex.normSq _) (h j ((A.chart j).symm z)),
      abs_of_nonneg (Complex.normSq_nonneg _)]
  have hdiff : ∀ j m, ∀ z ∈ D j m, DifferentiableAt ℂ (q ∘ (A.chart j).symm) z := fun j m z hz =>
    (pushA_analytic A hq j (hDO j m hz).1 (hTc _ (hDO j m hz).2)).differentiableAt
  have hintT := fun j => pushA_intOn A P Φ g hg j
  have hintO : ∀ j, IntegrableOn
      (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y)
      (⋃ m, D j m) := fun j => (hintT j).mono_set (by rw [hDU j]; exact Set.inter_subset_left)

  have hpc : ∀ j m, Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} ∩ (A.chart j).symm '' D j m, h j x) ∧
      ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} ∩ (A.chart j).symm '' D j m, h j x =
        ∫ y in D j m, P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y ∧
      ∫ y, ‖∑ᶠ x ∈ q ⁻¹' {y} ∩ (A.chart j).symm '' D j m, h j x‖ =
        ∫ y in D j m, ‖P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y‖ := by
    intro j m
    obtain ⟨hI, hJ⟩ := pushA_piece q (A.chart j).symm (hDm j m) (hdiff j m) (hDi j m) (h j)
    obtain ⟨-, hJ'⟩ := pushA_piece q (A.chart j).symm (hDm j m) (hdiff j m) (hDi j m)
      (fun x => |h j x|)
    refine ⟨hI.2 (((hintT j).mono_set fun z hz => (hDO j m hz).1).congr_fun
      ((hEq j).mono (hDO j m)).symm (hDm j m)), ?_, ?_⟩
    · rw [hJ, setIntegral_congr_fun (hDm j m) ((hEq j).mono (hDO j m))]
    · rw [funext fun y => pushA_piece_norm q (A.chart j).symm (hDi j m) (h j) y, hJ',
        setIntegral_congr_fun (hDm j m) ((hEqN j).mono (hDO j m))]

  have hEd : ∀ j, Pairwise (Function.onFun Disjoint fun m => (A.chart j).symm '' D j m) := by
    intro j m m' hmm'
    refine Set.disjoint_left.2 ?_
    rintro x ⟨z, hz, rfl⟩ ⟨z', hz', hzz⟩
    have : z' = z := by
      rw [← (A.chart j).right_inv (hDO j m' hz').1, hzz, (A.chart j).right_inv (hDO j m hz).1]
    exact Set.disjoint_left.1 (hDd j hmm') hz (this ▸ hz')
  have hEU : ∀ j, ∀ x, x ∉ S → (⋃ m, (A.chart j).symm '' D j m).indicator (h j) x = h j x := by
    intro j x hx
    by_cases hxs : x ∈ (A.chart j).source
    · have hz : A.chart j x ∈ ⋃ m, D j m := by
        rw [hDU j]
        exact ⟨(A.chart j).map_source hxs,
          show (A.chart j).symm (A.chart j x) ∈ Sᶜ by rw [(A.chart j).left_inv hxs]; exact hx⟩
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hz
      have hxU : x ∈ ⋃ m, (A.chart j).symm '' D j m :=
        Set.mem_iUnion.2 ⟨m, A.chart j x, hm, (A.chart j).left_inv hxs⟩
      exact Set.indicator_of_mem hxU _
    · have hn : x ∉ ⋃ m, (A.chart j).symm '' D j m := by
        rintro hx'
        obtain ⟨m, z, hz, rfl⟩ := Set.mem_iUnion.1 hx'
        exact hxs ((A.chart j).map_target (hDO j m hz).1)
      rw [Set.indicator_of_notMem hn]
      simp only [hh]
      rw [image_eq_zero_of_notMem_tsupport (fun h' => hxs (P.tsupport_subset j h'))]
      ring

  have hser : ∀ j y, HasSum (fun m => ∑ᶠ x ∈ q ⁻¹' {y} ∩ (A.chart j).symm '' D j m, h j x)
      (∑ᶠ x ∈ q ⁻¹' {y} \ S, h j x) := by
    intro j y
    have hset : ∀ m, q ⁻¹' {y} ∩ (A.chart j).symm '' D j m =
        (q ⁻¹' {y} \ S) ∩ (A.chart j).symm '' D j m := by
      intro m
      ext x
      constructor
      · rintro ⟨hx1, z, hz, rfl⟩
        exact ⟨⟨hx1, (hDO j m hz).2⟩, z, hz, rfl⟩
      · rintro ⟨⟨hx1, -⟩, hx2⟩
        exact ⟨hx1, hx2⟩
    simp only [hset, pushA_finsum_inter, finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    refine hasSum_sum fun x hx => ?_
    have hxS : x ∉ S := ((hfin y).mem_toFinset.1 hx).2
    rw [← hEU j x hxS]
    exact pushA_hasSum_ind _ (hEd j) (h j) x
  have hnsum : ∀ j, Summable fun m =>
      ∫ y, ‖∑ᶠ x ∈ q ⁻¹' {y} ∩ (A.chart j).symm '' D j m, h j x‖ := by
    intro j
    simp only [fun m => (hpc j m).2.2]
    exact (hasSum_integral_iUnion (hDm j) (hDd j) (hintO j).norm).summable
  have hts : ∀ j, Integrable fun y => ∑' m, ∑ᶠ x ∈ q ⁻¹' {y} ∩ (A.chart j).symm '' D j m, h j x :=
    fun j => pushA_intTsum (fun m => (hpc j m).1) (fun y => (hser j y).summable) (hnsum j)
  have hpt : ∀ y, ∑ j, ∑' m, ∑ᶠ x ∈ q ⁻¹' {y} ∩ (A.chart j).symm '' D j m, h j x =
      ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x := by
    intro y
    rw [Finset.sum_congr rfl fun j _ => (hser j y).tsum_eq, pushA_sum_finsum (hfin y)]
    refine finsum_mem_congr rfl fun x _ => ?_
    simp only [hh, ← Finset.sum_mul, P.sum_eq_one, one_mul]
  have hfun : (fun y => ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x) =
      fun y => ∑ j, ∑' m, ∑ᶠ x ∈ q ⁻¹' {y} ∩ (A.chart j).symm '' D j m, h j x :=
    funext fun y => (hpt y).symm
  rw [hfun]
  refine ⟨integrable_finsetSum _ fun j _ => hts j, ?_⟩
  rw [integral_finsetSum _ fun j _ => hts j, integralWith]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hnull : ((A.chart j).target : Set (Fin e → ℂ)) =ᵐ[volume]
      (((A.chart j).target ∩ (A.chart j).symm ⁻¹' Sᶜ : Set (Fin e → ℂ))) := by
    refine ae_eq_set.2 ⟨measure_mono_null ?_ (analyticNull A S hS hint j), ?_⟩
    · rintro z ⟨hz, hzO⟩
      have hzS : (A.chart j).symm z ∈ S := by
        by_contra hc
        exact hzO ⟨hz, hc⟩
      exact ⟨(A.chart j).symm z, ⟨hzS, (A.chart j).map_target hz⟩, (A.chart j).right_inv hz⟩
    · rw [Set.sdiff_eq_empty.2 Set.inter_subset_left]
      exact measure_empty
  rw [setIntegral_congr_set hnull, ← hDU j, integral_iUnion (hDm j) (hDd j) (hintO j),
    ← integral_tsum_of_summable_integral_norm (fun m => (hpc j m).1) (hnsum j)]
  exact tsum_congr fun m => ((hpc j m).2.1).symm

end

end ReciprocityTheory.AnForm.M
end

