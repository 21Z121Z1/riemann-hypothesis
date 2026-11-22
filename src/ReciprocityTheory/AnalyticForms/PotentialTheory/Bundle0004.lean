import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Partition
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
section
namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

theorem pa_holoSmooth {e e' : ℕ} (F : (Fin e → ℂ) → (Fin e' → ℂ)) (U : Set (Fin e → ℂ))
    (hF : AnalyticOnNhd ℂ F U) : ContDiffOn ℝ ∞ F U :=
  fun x hx => ((hF x hx).contDiffAt.restrict_scalars ℝ).contDiffWithinAt

def pa_aff {e : ℕ} (a : ℂ) (ha : a ≠ 0) (b : Fin e → ℂ) : (Fin e → ℂ) ≃ₜ (Fin e → ℂ) where
  toFun y := a • (y - b)
  invFun z := a⁻¹ • z + b
  left_inv y := by simp [smul_smul, inv_mul_cancel₀ ha]
  right_inv z := by simp [smul_smul, mul_inv_cancel₀ ha]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem pa_aff_analytic {e : ℕ} (a : ℂ) (b : Fin e → ℂ) (y : Fin e → ℂ) :
    AnalyticAt ℂ (fun y : Fin e → ℂ => a • (y - b)) y :=
  by fun_prop

theorem pa_compat_chart {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (j : Fin A.n) : IsCompatChart A (A.chart j) :=
  fun k => ⟨A.holo k j, A.holo j k⟩

theorem pa_compat_restr {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (s : Set X)
    (hs : IsOpen s) : IsCompatChart A (ψ.restrOpen s hs) := by
  intro j
  obtain ⟨h1, h2⟩ := hψ j
  refine ⟨h1.mono ?_, h2.mono ?_⟩
  · rintro x ⟨hx1, hx2⟩
    exact ⟨hx1, hx2.1⟩
  · rintro x ⟨hx1, hx2⟩
    exact ⟨hx1.1, hx2⟩

theorem pa_compat_aff {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (hψ : IsCompatChart A ψ) (a : ℂ) (ha : a ≠ 0)
    (b : Fin e → ℂ) : IsCompatChart A (ψ.transHomeomorph (pa_aff a ha b)) := by
  intro j
  obtain ⟨h1, h2⟩ := hψ j
  refine ⟨fun z hz => (pa_aff_analytic a b _).comp (h1 z hz), fun z hz => ?_⟩
  have hinv : AnalyticAt ℂ (fun z : Fin e → ℂ => a⁻¹ • z + b) z :=
    by fun_prop
  exact AnalyticAt.comp (f := fun w : Fin e → ℂ => a⁻¹ • w + b) (h2 (a⁻¹ • z + b) hz) hinv

theorem existsPartition : ExistsPartitionStatement := by
  intro e X _ _ _ A
  obtain ⟨χ, h0, h1, h2, h3⟩ := ReciprocityTheory.AnForm.exists_chart_partition A.chart A.cover
    (fun i j => pa_holoSmooth _ _ (A.holo i j))
  exact ⟨⟨χ, fun j k => (h3 j k).mono Set.inter_subset_left, h0, h2, h1⟩⟩

def AffineChartStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (j : Fin A.n) (a : ℂ)
    (b : Fin e → ℂ), a ≠ 0 →
    ∃ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ ∧
      ψ.source = (A.chart j).source ∧ ∀ x ∈ ψ.source, ψ x = a • (A.chart j x - b)

theorem affineChart : AffineChartStatement := by
  intro e X _ A j a b ha
  exact ⟨(A.chart j).transHomeomorph (pa_aff a ha b), pa_compat_aff A _ (pa_compat_chart A j) a ha b, rfl,
    fun x _ => rfl⟩

def AtlasOfCompatStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ}
    (ψ : Fin m → OpenPartialHomeomorph X (Fin e → ℂ)), (∀ i, IsCompatChart A (ψ i)) →
    (∀ x, ∃ i, x ∈ (ψ i).source) →
    ∃ B : FinHolAtlas e X, A.Compatible B ∧ (∀ i, ∃ j, B.chart j = ψ i) ∧ ∀ j, ∃ i, B.chart j = ψ i

theorem atlasOfCompat : AtlasOfCompatStatement := by
  intro e X _ A m ψ hψ hcov
  refine ⟨⟨m, ψ, hcov, ?_⟩, ⟨fun j k => (hψ k j).1, fun j k => (hψ j k).2⟩, fun i => ⟨i, rfl⟩,
    fun j => ⟨j, rfl⟩⟩
  intro j k z hz
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨l, hx⟩ := A.cover ((ψ j).symm z)
  have hev : ∀ᶠ w in nhds z, (ψ j).symm w ∈ (A.chart l).source :=
    ((ψ j).continuousAt_symm hz1).preimage_mem_nhds ((A.chart l).open_source.mem_nhds hx)
  have ha1 := (hψ k l).1 (A.chart l ((ψ j).symm z))
    ⟨(A.chart l).map_source hx, by rw [Set.mem_preimage, (A.chart l).left_inv hx]; exact hz2⟩
  have ha2 := (hψ j l).2 z ⟨hz1, hx⟩
  exact (AnalyticAt.comp (f := ⇑(A.chart l) ∘ ⇑(ψ j).symm) ha1 ha2).congr (hev.mono fun w hw => by
    simp only [Function.comp, (A.chart l).left_inv hw])

theorem regularAtlas : RegularAtlasStatement := by
  intro e X _ _ _ A
  have hloc : ∀ x : X, ∃ (j : Fin A.n) (r : ℝ), 0 < r ∧ x ∈ (A.chart j).source ∧
      Metric.ball (A.chart j x) r ⊆ (A.chart j).target := by
    intro x
    obtain ⟨j, hj⟩ := A.cover x
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp (A.chart j).open_target _ ((A.chart j).map_source hj)
    exact ⟨j, r, hr, hj, hb⟩
  choose J R hR hJ hball using hloc
  have ha : ∀ x, (((3 / R x : ℝ)) : ℂ) ≠ 0 := fun x =>
    Complex.ofReal_ne_zero.mpr (div_pos (by norm_num) (hR x)).ne'
  let ψ : X → OpenPartialHomeomorph X (Fin e → ℂ) := fun x =>
    (A.chart (J x)).transHomeomorph (pa_aff (((3 / R x : ℝ)) : ℂ) (ha x) (A.chart (J x) x))
  have hψc : ∀ x, IsCompatChart A (ψ x) := fun x =>
    pa_compat_aff A _ (pa_compat_chart A (J x)) _ (ha x) _
  let U : X → Set X := fun x => (ψ x).source ∩ (ψ x) ⁻¹' Metric.ball 0 1
  have hUo : ∀ x, IsOpen (U x) := fun x => (ψ x).isOpen_inter_preimage Metric.isOpen_ball
  have hUx : ∀ x, x ∈ U x := fun x => by
    refine ⟨hJ x, ?_⟩
    show (((3 / R x : ℝ)) : ℂ) • (A.chart (J x) x - A.chart (J x) x) ∈ Metric.ball (0 : Fin e → ℂ) 1
    simp
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo (fun x _ => Set.mem_iUnion.mpr ⟨x, hUx x⟩)
  let φ : Fin t.card → OpenPartialHomeomorph X (Fin e → ℂ) := fun i => ψ (t.equivFin.symm i)
  have hcov : ∀ x, ∃ i, x ∈ (φ i).source ∧ φ i x ∈ Metric.ball (0 : Fin e → ℂ) 1 := by
    intro x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    refine ⟨t.equivFin ⟨y, hy⟩, ?_⟩
    simp only [φ, Equiv.symm_apply_apply]
    exact hxy
  obtain ⟨B, hAB, hB1, hB2⟩ := atlasOfCompat A φ (fun i => hψc _) (fun x => (hcov x).imp fun i h => h.1)
  refine ⟨B, hAB, fun j => ?_, fun x => ?_⟩
  · obtain ⟨i, hi⟩ := hB2 j
    rw [hi]
    intro w hw
    have hw' : ‖w‖ ≤ 2 := by simpa using hw
    set y := t.equivFin.symm i
    change (((3 / R y : ℝ)) : ℂ)⁻¹ • w + A.chart (J y) y ∈ (A.chart (J y)).target
    apply hball
    have hRy := hR y
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hRy), inv_div]
    calc R y / 3 * ‖w‖ ≤ R y / 3 * 2 := by gcongr
      _ < R y := by linarith
  · obtain ⟨i, hi1, hi2⟩ := hcov x
    obtain ⟨j, hj⟩ := hB1 i
    exact ⟨j, hj ▸ hi1, hj ▸ hi2⟩

end

end ReciprocityTheory.AnForm.M
end

-- bundled from ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftB
section
namespace ReciprocityTheory.AnForm.M

open Filter Topology FinHolAtlas
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := by
  first
  | exact WithTop.coe_le_coe.2 le_top
  | exact_mod_cast (le_top : ((2 : ℕ∞) ≤ ⊤))
  | norm_num
  | simp
  | decide

theorem pshShift_local (A : FinHolAtlas e X) (Ω : LocPot X) (hΩ : IsPotential A Ω)
    (hpos : IsPosPot A Ω) (w : X → ℝ) (hw : A.Smooth w) (p : X) (j : Fin A.n)
    (hp : p ∈ (A.chart j).source) :
    ∃ r > 0, ∃ m : ℝ, Metric.closedBall (A.chart j p) r ⊆
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' Ω.U p ∧
      ∀ y ∈ Metric.closedBall (A.chart j p) r, ∀ u : Fin e → ℂ,
        m * levi (Ω.φ p ∘ (A.chart j).symm) y u ≤ levi (w ∘ (A.chart j).symm) y u := by
  classical
  set φ : (Fin e → ℂ) → ℝ := Ω.φ p ∘ (A.chart j).symm with hφdef
  set ψ : (Fin e → ℂ) → ℝ := w ∘ (A.chart j).symm with hψdef
  set S : Set (Fin e → ℂ) := (A.chart j).target ∩ (A.chart j).symm ⁻¹' Ω.U p with hSdef
  have hSo : IsOpen S := (A.chart j).isOpen_inter_preimage_symm (Ω.isOpen_U p)
  have hz0 : A.chart j p ∈ S := by
    refine ⟨(A.chart j).map_source hp, ?_⟩
    show (A.chart j).symm (A.chart j p) ∈ Ω.U p
    rw [(A.chart j).left_inv hp]
    exact Ω.mem_U p
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hSo _ hz0
  have hsub : Metric.closedBall (A.chart j p) (ε / 2) ⊆ S :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hφc : ContDiffOn ℝ 2 φ S := (hΩ.1 p j).of_le two_le_infty
  have hψc : ContDiffOn ℝ 2 ψ S :=
    ((hw j).of_le two_le_infty).mono (fun y hy => ⟨hy.1, Set.mem_univ _⟩)
  have hLφ := continuousOn_levi hSo hφc
  have hLψ := continuousOn_levi hSo hψc
  set K : Set ((Fin e → ℂ) × (Fin e → ℂ)) :=
    Metric.closedBall (A.chart j p) (ε / 2) ×ˢ Metric.sphere 0 1 with hKdef
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKS : K ⊆ S ×ˢ Set.univ := Set.prod_mono hsub (Set.subset_univ _)
  have hposK : ∀ q ∈ K, 0 < levi φ q.1 q.2 := by
    intro q hq
    refine hpos p j q.1 (hsub hq.1) q.2 ?_
    intro h0
    have h1 := hq.2
    rw [h0] at h1
    simp at h1
  have hg : ContinuousOn
      (fun q : (Fin e → ℂ) × (Fin e → ℂ) => levi ψ q.1 q.2 / levi φ q.1 q.2) K :=
    (hLψ.mono hKS).div (hLφ.mono hKS) (fun q hq => (hposK q hq).ne')
  obtain ⟨M, hM⟩ := hK.bddBelow_image hg
  refine ⟨ε / 2, by positivity, M, hsub, ?_⟩
  intro y hy u
  by_cases hu : u = 0
  · subst hu
    simp [levi_zero]
  · have ht : 0 < ‖u‖ := norm_pos_iff.2 hu
    obtain ⟨s, v, hv, rfl⟩ : ∃ s : ℝ, ∃ v ∈ Metric.sphere (0 : Fin e → ℂ) 1, u = s • v := by
      refine ⟨‖u‖, ‖u‖⁻¹ • u, ?_, ?_⟩
      · simp [norm_smul, hu, ht.ne']
      · simp [smul_smul, hu, ht.ne']
    have hq : ((y, v) : (Fin e → ℂ) × (Fin e → ℂ)) ∈ K := ⟨hy, hv⟩
    have h1 := hM ⟨(y, v), hq, rfl⟩
    have h2 := hposK _ hq
    simp only at h1 h2
    have h3 : M * levi φ y v ≤ levi ψ y v := by
      rwa [le_div_iff₀ h2] at h1
    rw [levi_smul_dir, levi_smul_dir]
    nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg s)]

theorem plurisubharmonicShift_proof : PshShiftStatement := by
  intro e X _ _ _ A Ω hΩ hpos w hw
  classical
  choose jq hjq using A.cover
  choose r hr m hsubq hlocq using fun q => pshShift_local A Ω hΩ hpos w hw q (jq q) (hjq q)
  have hVo : ∀ q, IsOpen ((A.chart (jq q)).source ∩
      A.chart (jq q) ⁻¹' Metric.ball (A.chart (jq q) q) (r q)) := fun q =>
    (A.chart (jq q)).continuousOn.isOpen_inter_preimage (A.chart (jq q)).open_source
      Metric.isOpen_ball
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun q => (A.chart (jq q)).source ∩ A.chart (jq q) ⁻¹' Metric.ball (A.chart (jq q) q) (r q))
    hVo (fun q _ => Set.mem_iUnion.2 ⟨q, hjq q, Metric.mem_ball_self (hr q)⟩)
  refine ⟨∑ q ∈ t, |m q|, ?_⟩
  intro x k y hy u
  show 0 ≤ levi ((fun z => w z + (∑ q ∈ t, |m q|) * Ω.φ x z) ∘ (A.chart k).symm) y u
  have hyk : y ∈ (A.chart k).target := hy.1
  have hzx : (A.chart k).symm y ∈ Ω.U x :=
    (show (A.chart k).symm y ∈ Set.univ ∩ Ω.U x from hy.2).2
  obtain ⟨q, hqt, hzq⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ ((A.chart k).symm y)))
  have hzq1 : (A.chart k).symm y ∈ (A.chart (jq q)).source ∩
      A.chart (jq q) ⁻¹' Metric.ball (A.chart (jq q) q) (r q) := hzq
  have hsub1 := hsubq q
  have hloc1 := hlocq q
  have hC : -m q ≤ ∑ q ∈ t, |m q| :=
    (neg_le_abs (m q)).trans (Finset.single_le_sum (fun i _ => abs_nonneg (m i)) hqt)
  generalize ∑ q ∈ t, |m q| = C at hC ⊢
  generalize jq q = jj at hzq1 hsub1 hloc1
  obtain ⟨hzj, hzb⟩ := hzq1
  have hτS : A.chart jj ((A.chart k).symm y) ∈
      (A.chart jj).target ∩ (A.chart jj).symm ⁻¹' Ω.U q :=
    hsub1 (Metric.ball_subset_closedBall hzb)
  have hzq' : (A.chart k).symm y ∈ Ω.U q := by
    have h := hτS.2
    rwa [Set.mem_preimage, (A.chart jj).left_inv hzj] at h
  have hτx : A.chart jj ((A.chart k).symm y) ∈
      (A.chart jj).target ∩ (A.chart jj).symm ⁻¹' Ω.U x := by
    refine ⟨(A.chart jj).map_source hzj, ?_⟩
    rw [Set.mem_preimage, (A.chart jj).left_inv hzj]
    exact hzx
  have hψ2 : ContDiffAt ℝ 2 (w ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) :=
    ((hw jj).contDiffAt (((A.chart jj).isOpen_inter_preimage_symm isOpen_univ).mem_nhds
      ⟨(A.chart jj).map_source hzj, Set.mem_univ _⟩)).of_le two_le_infty
  have hΦx2 : ContDiffAt ℝ 2 (Ω.φ x ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) :=
    ((hΩ.1 x jj).contDiffAt (((A.chart jj).isOpen_inter_preimage_symm (Ω.isOpen_U x)).mem_nhds
      hτx)).of_le two_le_infty
  have hΦq2 : ContDiffAt ℝ 2 (Ω.φ q ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) :=
    ((hΩ.1 q jj).contDiffAt (((A.chart jj).isOpen_inter_preimage_symm (Ω.isOpen_U q)).mem_nhds
      hτS)).of_le two_le_infty
  have hτa : AnalyticAt ℂ (A.chart jj ∘ (A.chart k).symm) y := A.holo k jj y ⟨hyk, hzj⟩
  have hf2 : ContDiffAt ℝ 2 ((fun z => w z + C * Ω.φ x z) ∘ (A.chart jj).symm)
      ((A.chart jj ∘ (A.chart k).symm) y) := hψ2.add (contDiffAt_const.mul hΦx2)
  have hev1 : (fun z => w z + C * Ω.φ x z) ∘ (A.chart k).symm =ᶠ[𝓝 y]
      ((fun z => w z + C * Ω.φ x z) ∘ (A.chart jj).symm) ∘ (A.chart jj ∘ (A.chart k).symm) := by
    refine Filter.eventuallyEq_of_mem
      (((A.chart k).isOpen_inter_preimage_symm (A.chart jj).open_source).mem_nhds ⟨hyk, hzj⟩) ?_
    intro y' hy'
    simp only [Function.comp_apply]
    rw [(A.chart jj).left_inv hy'.2]
  have hpt : (A.chart jj ∘ (A.chart k).symm) y = A.chart jj ((A.chart k).symm y) := rfl
  set v := fderiv ℂ (A.chart jj ∘ (A.chart k).symm) y u with hvdef
  have hL : levi ((fun z => w z + C * Ω.φ x z) ∘ (A.chart k).symm) y u =
      levi (w ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) v +
        C * levi (Ω.φ x ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) v := by
    rw [levi_congr hev1, levi_comp u hτa hf2, hpt]
    exact levi_add_smul C hψ2 hΦx2 v
  obtain ⟨W, hWo, hzW, G, hG, hGeq⟩ := hΩ.2 x q ((A.chart k).symm y) ⟨hzx, hzq'⟩
  have hτW : A.chart jj ((A.chart k).symm y) ∈
      (A.chart jj).target ∩ (A.chart jj).symm ⁻¹' (W ∩ Ω.U x ∩ Ω.U q) := by
    refine ⟨(A.chart jj).map_source hzj, ?_⟩
    rw [Set.mem_preimage, (A.chart jj).left_inv hzj]
    exact ⟨⟨hzW, hzx⟩, hzq'⟩
  have hN2 := ((A.chart jj).isOpen_inter_preimage_symm
    ((hWo.inter (Ω.isOpen_U x)).inter (Ω.isOpen_U q))).mem_nhds hτW
  have hGa : AnalyticAt ℂ (G ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) :=
    hG jj _ ⟨hτW.1, hτW.2.1.1⟩
  have hev2 : Ω.φ x ∘ (A.chart jj).symm =ᶠ[𝓝 (A.chart jj ((A.chart k).symm y))]
      fun y' => (Ω.φ q ∘ (A.chart jj).symm) y' + 1 * ((G ∘ (A.chart jj).symm) y').re := by
    refine Filter.eventuallyEq_of_mem hN2 ?_
    intro y' hy'
    have := hGeq _ hy'.2
    simp only [Function.comp_apply]
    linarith
  have hev3 : (fun y' => ((G ∘ (A.chart jj).symm) y').re)
      =ᶠ[𝓝 (A.chart jj ((A.chart k).symm y))]
      fun y' => (Ω.φ x ∘ (A.chart jj).symm) y' - (Ω.φ q ∘ (A.chart jj).symm) y' := by
    refine Filter.eventuallyEq_of_mem hN2 ?_
    intro y' hy'
    have := hGeq _ hy'.2
    simp only [Function.comp_apply]
    linarith
  have hRe2 : ContDiffAt ℝ 2 (fun y' => ((G ∘ (A.chart jj).symm) y').re)
      (A.chart jj ((A.chart k).symm y)) :=
    (hΦx2.sub hΦq2).congr_of_eventuallyEq hev3
  have hLx : levi (Ω.φ x ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) v =
      levi (Ω.φ q ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) v := by
    rw [levi_congr hev2, levi_add_smul 1 hΦq2 hRe2 v, levi_re_analytic hGa v]
    ring
  have hloc2 := hloc1 (A.chart jj ((A.chart k).symm y)) (Metric.ball_subset_closedBall hzb) v
  have hnn : 0 ≤ levi (Ω.φ q ∘ (A.chart jj).symm) (A.chart jj ((A.chart k).symm y)) v := by
    by_cases hv0 : v = 0
    · rw [hv0, levi_zero]
    · exact (hpos q jj _ hτS v hv0).le
  rw [hL, hLx]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ m q + C) hnn]

end

end ReciprocityTheory.AnForm.M
end

