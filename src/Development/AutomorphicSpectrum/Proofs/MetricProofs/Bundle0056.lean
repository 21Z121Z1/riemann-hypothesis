import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0046
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0048
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0036
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0019
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SpherePairLogSineMoment
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJEqSubmatrix
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0047
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothMinorOfSmoothMatrix
section
noncomputable section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.MinorSmooth

theorem contDiffOn_finsetProd {e : ℕ} {Un : Set (Fin e → ℂ)} {ι : Type} (s : Finset ι)
    (f : ι → (Fin e → ℂ) → ℂ)
    (h : ∀ i ∈ s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i) Un) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => ∏ i ∈ s, f i w) Un := by
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffOn_const : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : Fin e → ℂ => (1 : ℂ)) Un)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem contDiffOn_det {e : ℕ} {Un : Set (Fin e → ℂ)} {σ : Type} [Fintype σ] [DecidableEq σ]
    (m : (Fin e → ℂ) → Matrix σ σ ℂ)
    (h : ∀ a b, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => m w a b) Un) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => (m w).det) Un := by
  have hdet : (fun w => (m w).det) =
      fun w => ∑ τ : Equiv.Perm σ, ((Equiv.Perm.sign τ : ℤ) : ℂ) * ∏ i, m w (τ i) i := by
    funext w
    exact Matrix.det_apply' _
  rw [hdet]
  exact ContDiffOn.sum fun τ _ => contDiffOn_const.mul
    (contDiffOn_finsetProd Finset.univ (fun i w => m w (τ i) i) fun i _ => h _ _)

theorem contDiffOn_minorIJ (N e : ℕ) (Un : Set (Fin e → ℂ))
    (A : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (I J : Finset (Fin N))
    (h : ∀ r s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => A w r s) Un) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => minorIJ (A w) I J) Un := by
  by_cases hc : I.card = J.card
  · have hm : (fun w => minorIJ (A w) I J) =
        fun w => ((A w).submatrix (I.orderEmbOfFin hc) (J.orderEmbOfFin rfl)).det := by
      funext w
      rw [minorIJ, dif_pos hc]
    rw [hm]
    exact contDiffOn_det _ fun a b => h _ _
  · have hm : (fun w => minorIJ (A w) I J) = fun _ => (0 : ℂ) := by
      funext w
      rw [minorIJ, dif_neg hc]
    rw [hm]
    exact contDiffOn_const

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.MinorSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnCompositionWithAnalyticMap
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem contDiffOn_comp_of_analytic_in_charts :
    ∀ (e n : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas n X) (Un : Set (Fin e → ℂ))
      (bp : (Fin e → ℂ) → X) (W : Set X) (f : X → ℝ), IsOpen Un → ContinuousOn bp Un →
      (∀ k, AnalyticOnNhd ℂ (A.chart k ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source)) →
      (∀ w ∈ Un, bp w ∈ W) → A.SmoothOn W f →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ bp) Un := by
  intro e n X _ A Un bp W f hUn hbp hana hW hf w hw
  obtain ⟨k, hk⟩ := A.cover (bp w)
  have hV : IsOpen (Un ∩ bp ⁻¹' (A.chart k).source) :=
    hbp.isOpen_inter_preimage hUn (A.chart k).open_source
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A.chart k ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source) :=
    ((hana k).contDiffOn hV.uniqueDiffOn).restrict_scalars ℝ
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ (A.chart k).symm)
      ((A.chart k).target ∩ (A.chart k).symm ⁻¹' W) := hf k
  have h3 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((f ∘ (A.chart k).symm) ∘ (A.chart k ∘ bp))
      (Un ∩ bp ⁻¹' (A.chart k).source) := by
    refine h2.comp h1 ?_
    intro x hx
    refine ⟨(A.chart k).map_source hx.2, ?_⟩
    show (A.chart k).symm (A.chart k (bp x)) ∈ W
    rw [(A.chart k).left_inv hx.2]
    exact hW x hx.1
  have h4 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source) := by
    refine h3.congr ?_
    intro x hx
    simp only [Function.comp_apply, (A.chart k).left_inv hx.2]
  exact (h4.contDiffAt (hV.mem_nhds ⟨hw, hk⟩)).contDiffWithinAt

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedAtlasProjection
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.SncPull

theorem holoOn_comp_pr {e n : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    {A : FinHolAtlas e X} {Ab : FinHolAtlas n Z} {pr : X → Z} (hp : HoloMap A Ab pr)
    {U : Set Z} {g : Z → ℂ} (hg : Ab.HoloOn U g) : A.HoloOn (pr ⁻¹' U) (fun x => g (pr x)) := by
  intro j t ht
  obtain ⟨k, hk⟩ := Ab.cover (pr ((A.chart j).symm t))
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (pr ⁻¹' (Ab.chart k).source)) :=
    (A.chart j).isOpen_inter_preimage_symm ((Ab.chart k).open_source.preimage hp.1)
  have htO : t ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (pr ⁻¹' (Ab.chart k).source) :=
    ⟨ht.1, hk⟩
  have h1 : AnalyticAt ℂ (Ab.chart k ∘ pr ∘ (A.chart j).symm) t := hp.2 j k t htO
  have hmem : (Ab.chart k ∘ pr ∘ (A.chart j).symm) t ∈
      (Ab.chart k).target ∩ (Ab.chart k).symm ⁻¹' U := by
    refine ⟨(Ab.chart k).map_source hk, ?_⟩
    simp only [Function.comp, Set.mem_preimage, (Ab.chart k).left_inv hk]
    exact ht.2
  have h2 : AnalyticAt ℂ (g ∘ (Ab.chart k).symm) ((Ab.chart k ∘ pr ∘ (A.chart j).symm) t) :=
    hg k _ hmem
  have h3 := AnalyticAt.comp (g := g ∘ (Ab.chart k).symm)
    (f := Ab.chart k ∘ pr ∘ (A.chart j).symm) h2 h1
  refine h3.congr ?_
  filter_upwards [hO.mem_nhds htO] with t' ht'
  simp [Function.comp, (Ab.chart k).left_inv ht'.2]

theorem isSection_pull {e n : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    {A : FinHolAtlas e X} {Ab : FinHolAtlas n Z} {pr : X → Z} (hp : HoloMap A Ab pr)
    {L : LocPot Z} {s : Z → Z → ℂ} (hs : IsSection Ab L s) :
    IsSection A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) :=
  ⟨fun x => holoOn_comp_pr hp (hs.1 (pr x)), fun x x' y hy => hs.2 (pr x) (pr x') (pr y) hy⟩

theorem isSNC_pull {e n : ℕ} {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    {A : FinHolAtlas e X} {Ab : FinHolAtlas n Z} {pr : X → Z} (hp : HoloMap A Ab pr)
    {L : LocPot Z} {s : Z → Z → ℂ} {nb : ℕ} {m : Fin nb → ℕ} {W : Fin nb → Set Z}
    (hsnc : IsSNC Ab L s m W)
    (hprod : ∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e),
      IsCompatChart A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧
        ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i))) :
    IsSNC A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) m (fun k => pr ⁻¹' W k) := by
  intro x
  obtain ⟨ψb, hcb, hxb, hsub, σb, hinj, hW, u, hu, hu0, hfac⟩ := hsnc (pr x)
  obtain ⟨ψ, kb, σ, hc, hx, hpr⟩ := hprod x
  obtain ⟨ψ', hc', hsrc, hco⟩ := GlobalTheory.T.compatible_chart_product_projection e n X Z A Ab pr ψ kb σ ψb hc hcb hpr
  have hsrc' : ∀ y ∈ ψ'.source, pr y ∈ ψb.source := fun y hy => by
    rw [hsrc] at hy; exact hy.2
  refine ⟨ψ', hc', by rw [hsrc]; exact ⟨hx, hxb⟩, fun y hy => hsub (hsrc' y hy),
    fun k => (σb k).map σ, ?_, ?_, fun y => u (pr y), ?_, fun y hy => hu0 _ (hsrc' y hy), ?_⟩
  · intro k k' i hk hk'
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hk
    obtain ⟨b, hb, hab⟩ := Option.map_eq_some_iff.1 hk'
    obtain rfl := σ.injective hab
    exact hinj k k' _ ha hb
  · intro k
    ext y
    constructor
    · rintro ⟨hyW, hy⟩
      have h1 : pr y ∈ W k ∩ ψb.source := ⟨hyW, hsrc' y hy⟩
      rw [hW k] at h1
      obtain ⟨-, i, hi, h0⟩ := h1
      exact ⟨hy, σ i, by simp [hi], by rw [hco y hy]; exact h0⟩
    · rintro ⟨hy, i, hi, h0⟩
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hi
      rw [hco y hy] at h0
      have h1 : pr y ∈ W k ∩ ψb.source := by
        rw [hW k]; exact ⟨hsrc' y hy, a, ha, h0⟩
      exact ⟨h1.1, hy⟩
  · exact fun j => (holoOn_comp_pr hp hu j).mono fun t ht => ⟨ht.1, hsrc' _ ht.2⟩
  · intro y hy
    show s (pr x) (pr y) = _
    rw [hfac _ (hsrc' y hy)]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    cases h : σb k with
    | none => simp [h]
    | some i => simp [h, hco y hy]

theorem exists_adapted {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {nb : ℕ} {m : Fin nb → ℕ}
    {W : Fin nb → Set X} (hL : IsPotential A L) (hs : IsSection A L s) (hsnc : IsSNC A L s m W) :
    ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B L s := by
  choose φ S μ v hc hx hball h0 hU hμ hv hv0 hfac using GlobalTheory.T.exists_snc_adapted_chart_at_point e X A L s nb m W hsnc
  have hb := fun x => GlobalTheory.T.snc_adapted_chart_section_form e X A L s hL hs x (φ x) (S x) (μ x) (v x) (hc x) (hball x) (hU x)
    (hμ x) (hv x) (hv0 x) (hfac x)
  choose hzero M hM using fun x => And.intro (hb x).1 (hb x).2
  have hopen : ∀ x, IsOpen ((φ x).source ∩ φ x ⁻¹' Metric.ball (0 : Fin e → ℂ) 1) := fun x =>
    (φ x).continuousOn.isOpen_inter_preimage (φ x).open_source Metric.isOpen_ball
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen (fun x _ =>
    Set.mem_iUnion.2 ⟨x, hx x, by simp [h0 x]⟩)
  let E := t.equivFin
  have hcov : ∀ x, ∃ i : Fin t.card, x ∈ (φ (E.symm i).1).source ∧
      φ (E.symm i).1 x ∈ Metric.ball (0 : Fin e → ℂ) 1 := by
    intro x
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    refine ⟨E ⟨p, hp⟩, ?_⟩
    simpa using hxp
  obtain ⟨B, hAB, hB1, hB2⟩ := atlasOfCompat A (fun i : Fin t.card => φ (E.symm i).1)
    (fun i => hc _) (fun x => (hcov x).imp fun _ h => h.1)
  refine ⟨B, hAB, ?_, ?_, ∑ i : Fin t.card, |M (E.symm i).1|, ?_⟩
  · intro j
    obtain ⟨i, hi⟩ := hB2 j
    rw [hi]; exact hball _
  · intro x
    obtain ⟨i, hi, hi'⟩ := hcov x
    obtain ⟨j, hj⟩ := hB1 i
    exact ⟨j, by rw [hj]; exact hi, by rw [hj]; exact hi'⟩
  · intro j
    obtain ⟨i, hi⟩ := hB2 j
    refine ⟨S (E.symm i).1, μ (E.symm i).1, hμ _, ?_, ?_⟩
    · rw [hi]; exact hzero _
    · rw [hi]
      intro y hy hy'
      exact ((hM _ y hy hy').trans (le_abs_self _)).trans
        (Finset.single_le_sum (f := fun i : Fin t.card => |M (E.symm i).1|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ i))

theorem pullback_projection : ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] (A : FinHolAtlas e X) (Ab Bb : FinHolAtlas n Z) (pr : X → Z) (hp : HoloMap A Ab pr) (L : LocPot Z) (s : Z → Z → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set Z), IsPotential Ab L → IsSection Ab L s → IsSNC Ab L s m W → (∀ x, logNormSec L s x ≤ 0) → (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i))) → IsPotential A (L.pullback pr hp.1) ∧ IsSection A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) ∧ IsSNC A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) m (fun k => pr ⁻¹' W k) ∧ ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) := by
  intro e n X Z _ _ _ _ _ _ A Ab Bb pr hp L s nb m W hL hs hsnc _ hprod
  have hL' := ReciprocityTheory.AnForm.M.isPotentialPullback Ab A pr hp L hL
  have hs' := isSection_pull hp hs
  have hn' := isSNC_pull hp hsnc hprod
  exact ⟨hL', hs', hn', exists_adapted A _ _ hL' hs' hn'⟩

end GlobalTheory.CompanionTheory.Ar.PB.SncPull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMomentPowerStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphere_moment_power : ∀ (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (N : ℕ),
    ∫ a : ℂ, wS a * ℓ (lin3 (nS a) ^ N) =
      Real.pi * ℓ (momentPoly sphereMeasure (fun _ => 1) (dotPoly (id : S2 → S2) ^ N)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.stereo_one | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.stereo_one | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.stereo_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SpherePairLogSineMomentStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphere_pair_log_sine_moment : ∀ (ℓ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ) (Q : MvPolynomial (Fin 2) ℝ),
    ∫ p : ℂ × ℂ, logSin 1 p.1 p.2 * (wS p.1 * wS p.2 * ℓ (aeval ![lin3 (nS p.1), lin3 (nS p.2)] Q)) =
      Real.pi ^ 2 * ℓ (momentPoly (sphereMeasure.prod sphereMeasure) wwLogWeight
        (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] Q)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibN.StereoTwo.integral_eq_moment | exact GlobalTheory.CompanionTheory.Ar.PB.FibN.StereoTwo.integral_eq_moment | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibN.StereoTwo.integral_eq_moment <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.StepFactorNeZero
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem minor_ne_zero_of_support {N : ℕ} {h : Matrix (Fin N) (Fin N) ℂ} (hd : h.det ≠ 0) {I : Finset (Fin N)}
    (hs : ∀ k c, c ∈ I → k ∉ I → h k c = 0) : minorIJ h I I ≠ 0 := by
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 (isUnit_iff_ne_zero.2 hd)
  have hH : (hᴴ * (1 : Matrix (Fin N) (Fin N) ℂ) * h).PosDef := by
    rw [Matrix.mul_one]
    exact Matrix.PosDef.conjTranspose_mul_self h (Matrix.mulVec_injective_of_isUnit hu)
  have hq := SchurCalc.minor_pos hH I
  rw [SchurCalc.minor_gram (G := 1) (fun k c hc hk => Matrix.one_apply_ne (fun e => hk (e ▸ hc))) hs] at hq
  intro e
  simp [e] at hq

theorem facOf_ne_zero (N j : ℕ) (a i : Fin N) (h : Matrix (Fin N) (Fin N) ℂ) (hh : IsBlockDiag j h)
    (hd : h.det ≠ 0) : facOf N j a h i ≠ 0 := by
  unfold facOf
  split_ifs
  · exact minor_ne_zero_of_support hd (MinorCalc.support_wIdx hh)
  · exact one_ne_zero
  · exact minor_ne_zero_of_support hd (MinorCalc.support_omIdx hh)

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.StepRowsInverseNonzeroEntry
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.UnitComb

theorem coe_minorIJ {L : Type} [Field L] (V : ValuationSubring L) {N : ℕ}
    (h : Matrix (Fin N) (Fin N) V) (I J : Finset (Fin N)) :
    ((minorIJ h I J : V) : L) = minorIJ (h.map V.subtype) I J := by
  unfold minorIJ
  split_ifs with e
  · exact RingHom.map_det V.subtype _
  · rfl

theorem minorIJ_one_diag {R : Type} [CommRing R] {N : ℕ} (J : Finset (Fin N)) :
    minorIJ (1 : Matrix (Fin N) (Fin N) R) J J = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (J.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem exists_isUnit_of_sum {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} (s : Finset ι)
    (f : ι → R) (h : IsUnit (∑ a ∈ s, f a)) : ∃ a ∈ s, IsUnit (f a) := by
  by_contra hc
  push_neg at hc
  have : ∑ a ∈ s, f a ∈ IsLocalRing.maximalIdeal R :=
    Ideal.sum_mem _ fun a ha => (IsLocalRing.mem_maximalIdeal _).2 (hc a ha)
  exact (IsLocalRing.mem_maximalIdeal _).1 this h

theorem stepCols_ne_empty {N j : ℕ} (i : Fin N) (hj : j ≤ N) : stepCols N j i ≠ ∅ := by
  have hi := i.2
  by_cases c : (i : ℕ) + 1 ≤ j
  · refine Finset.Nonempty.ne_empty ⟨⟨N - j, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos c]
    omega
  · refine Finset.Nonempty.ne_empty ⟨⟨0, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg c]
    omega

theorem unit_comb : ∀ (L : Type) [Field L] (V : ValuationSubring L) (N j : ℕ) (i : Fin N) (H : Matrix (Fin N) (Fin N) L) (κ : Type) [Fintype κ] (u : κ → Finset (Fin N) → L) (u' : Finset (Fin N) → κ → L), j ≤ N → IsBlockDiag j H → (∀ a b, H a b ∈ V) → H.det ≠ 0 → (H.det)⁻¹ ∈ V → (∀ I m, u' I m ∈ V) → (∀ m I, u m I ∈ V) → (∀ I I', IsStepRows N j i I → IsStepRows N j i I' → ∑ m, u' I m * u m I' = if I = I' then 1 else 0) → ∃ m, (∑ I, u m I * minorIJ H I (stepCols N j i)) ≠ 0 ∧ (∑ I, u m I * minorIJ H I (stepCols N j i))⁻¹ ∈ V := by
  intro L _ V N j i H κ _ u u' hj hB hH hdet hinv hu' hu horth
  let Hv : Matrix (Fin N) (Fin N) V := Matrix.of fun a b => ⟨H a b, hH a b⟩
  have hHv : Hv.map V.subtype = H := by ext a b; rfl
  let uv : κ → Finset (Fin N) → V := fun m I => ⟨u m I, hu m I⟩
  let uv' : Finset (Fin N) → κ → V := fun I m => ⟨u' I m, hu' I m⟩
  have hdetc : ((Hv.det : V) : L) = H.det := by
    have := RingHom.map_det V.subtype Hv
    rw [RingHom.mapMatrix_apply, hHv] at this
    exact this
  have hunit : IsUnit Hv.det := by
    refine IsUnit.of_mul_eq_one (⟨(H.det)⁻¹, hinv⟩ : V) ?_
    apply Subtype.ext
    change ((Hv.det : V) : L) * (H.det)⁻¹ = 1
    rw [hdetc, mul_inv_cancel₀ hdet]
  have main := GlobalTheory.T.block_diagonal_minor_vanishing V N j i hj
  have hJ := stepCols_ne_empty (j := j) i hj
  have hBv : IsBlockDiag j Hv := fun a b hab => Subtype.ext (hB a b hab)
  have hstep : ∀ I, ¬ IsStepRows N j i I → minorIJ Hv I (stepCols N j i) = 0 := fun I hI =>
    (main.2.1 Hv I hBv hI).resolve_right hJ
  have hsum1 : IsUnit (∑ I', minorIJ Hv⁻¹ (stepCols N j i) I' * minorIJ Hv I' (stepCols N j i)) := by
    rw [← main.1, Matrix.nonsing_inv_mul _ hunit, minorIJ_one_diag]
    exact isUnit_one
  obtain ⟨I₀, -, hI₀⟩ := exists_isUnit_of_sum _ _ hsum1
  have hI₀' : IsUnit (minorIJ Hv I₀ (stepCols N j i)) := isUnit_of_mul_isUnit_right hI₀
  have hI₀s : IsStepRows N j i I₀ := by
    by_contra hc
    rw [hstep I₀ hc] at hI₀'
    exact not_isUnit_zero hI₀'
  have horthV : ∀ I', IsStepRows N j i I' → ∑ m, uv' I₀ m * uv m I' = if I₀ = I' then 1 else 0 := by
    intro I' hI'
    apply Subtype.ext
    have := horth I₀ I' hI₀s hI'
    split_ifs at this ⊢ with e
    · simpa [uv, uv'] using this
    · simpa [uv, uv'] using this
  let w : κ → V := fun m => ∑ I, uv m I * minorIJ Hv I (stepCols N j i)
  have hw : ∑ m, uv' I₀ m * w m = minorIJ Hv I₀ (stepCols N j i) := by
    have e1 : ∑ m, uv' I₀ m * w m =
        ∑ I, (∑ m, uv' I₀ m * uv m I) * minorIJ Hv I (stepCols N j i) := by
      simp only [w, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc]
    rw [e1, Finset.sum_eq_single I₀]
    · rw [horthV I₀ hI₀s, if_pos rfl, one_mul]
    · intro b _ hb
      by_cases hs : IsStepRows N j i b
      · rw [horthV b hs, if_neg (Ne.symm hb), zero_mul]
      · rw [hstep b hs, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [← hw] at hI₀'
  obtain ⟨m, -, hm⟩ := exists_isUnit_of_sum _ _ hI₀'
  have hwm : IsUnit (w m) := isUnit_of_mul_isUnit_right hm
  have hcoe : ((w m : V) : L) = ∑ I, u m I * minorIJ H I (stepCols N j i) := by
    simp only [w, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, coe_minorIJ, hHv]
    rfl
  refine ⟨m, ?_, ?_⟩
  · rw [← hcoe]
    intro h0
    exact hwm.ne_zero (Subtype.ext h0)
  · obtain ⟨c, hc⟩ := hwm.exists_right_inv
    have hc' : ((w m : V) : L) * (c : L) = 1 := congrArg Subtype.val hc
    rw [← hcoe, inv_eq_of_mul_eq_one_right hc']
    exact c.2

end GlobalTheory.CompanionTheory.Ar.PB.UnitComb
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SupMetricCombinationBoundStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sup_metric_combination_bound : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (R : RootModel Ψ N) (lam : Wt Ψ N) (n' : Option (Ψ × Fin N) → ℤ) (p : ℕ) [Fact p.Prime] (z : (Σ k, R.ι k) → PadicAlgCl p) (rec : Ψ × Fin N → ℝ) (θ : ℝ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (∀ j, (n' j : ℝ) = R.coef lam 0 j) → (∀ r, 0 < rec r) → (∀ r, |Real.log (supMet (R.xdeg r) z) - Real.log (rec r)| ≤ θ * Real.log p) → supMet (combLine (R.line 1) n').a z ≤ (p : ℝ) ^ (θ * l1 lam) * ∏ r, rec r ^ n' (some r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.supMet_line_le_record | exact GlobalTheory.CompanionTheory.Ar.Small.supMet_line_le_record | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.supMet_line_le_record <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoByTwoMinorGramIdentity
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem xiCoef_self {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (τ : Ψ) (a i : Fin N) :
    xiCoef τ a (τ, i) = xiCoef () a ((), i) := by
  simp [xiCoef]

theorem xiCoef_ne {Ψ : Type} [DecidableEq Ψ] {N : ℕ} {τ τ' : Ψ} (h : τ' ≠ τ) (a i : Fin N) :
    xiCoef τ a (τ', i) = 0 := by
  simp [xiCoef, h]

theorem xi_sum_potentials : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (τ : Ψ) (a b ca cb : Fin N) (Gf hf : Ψ → Matrix (Fin N) (Fin N) ℂ) (u : Ψ × Fin N → ℝ) (t : ℂ) (G₂ : Matrix (Fin 2) (Fin 2) ℂ), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j (Gf τ) → (Gf τ).PosDef → IsBlockDiag j (hf τ) → (hf τ).det ≠ 0 → (∀ r s : Fin 2, G₂ r s = minorIJ ((hf τ)ᴴ * Gf τ * hf τ) (insert (![ca, cb] r) ((stepCols N j a).erase ca)) (insert (![ca, cb] s) ((stepCols N j a).erase ca)) / minorIJ ((hf τ)ᴴ * Gf τ * hf τ) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca)) → ∑ p, (xiCoef τ a p : ℝ) * (blockPot j p.2 (Gf p.1) (if p.1 = τ then hf τ * (1 + Matrix.single cb ca t) else hf p.1) - u p) = xiPot G₂ t - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else Real.log ‖facOf N j a (hf τ) i‖) + u (τ, i)) := by
  intro Ψ _ _ N j τ a b ca cb Gf hf u t G₂ hj hb hcase hca hcb hG hGp hh hdet hG₂
  obtain ⟨G₃, -, e3, key⟩ := norm_three_steps N j a b ca cb (Gf τ) (hf τ) hj hb hcase hca hcb hG hGp hh hdet
  have hGG : G₃ = G₂ := Matrix.ext fun r s => (e3 r s).trans (hG₂ r s).symm
  subst hGG
  have hsum : ∑ p, (xiCoef τ a p : ℝ) * (blockPot j p.2 (Gf p.1) (if p.1 = τ then hf τ * (1 + Matrix.single cb ca t) else hf p.1) - u p) =
      ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * (blockPot j i (Gf τ) (hf τ * (1 + Matrix.single cb ca t)) - u (τ, i)) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
    · simp
    · intro τ' _ hne
      simp [xiCoef_ne hne]
    · simp
  rw [hsum, ← key t, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [xiCoef_self]
  simp only [facOf]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoMapPullbackEnergyStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_map_pullback_energy : ∀ (e e' : ℕ) (σ : Type) [Fintype σ] (S : AnSys e σ) (X' : Type) [TopologicalSpace X'] [CompactSpace X'] [T2Space X'] (A' : FinHolAtlas e' X') (Θ' L' : LocPot X') (s' : X' → X' → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X') (q : Fin 2 → X' → S.X) (hq : ∀ i, HoloMap A' S.A (q i)), PullbackStatement → IsPotential A' Θ' → IsPosPot A' Θ' → IsPotential A' L' → IsSection A' L' s' → IsSNC A' L' s' m W → (∀ y, logNormSec L' s' y ≤ 0) → (∀ i, S.L.pullback (q i) (hq i).1 = L') → (∀ i, (fun x y => S.s (q i x) (q i y)) = s') → ∃ C₅ C t₀ : ℝ, t₀ ≤ S.t₀ ∧ ∀ (i : Fin 2) (a : σ), IsSingWeight A' L' s' ((S.th a).pullback (q i) (hq i).1) (S.ph a ∘ q i) C₅ ∧ IsRegFamily A' Θ' L' s' ((S.th a).pullback (q i) (hq i).1) (S.ph a ∘ q i) (fun t => S.phT a t ∘ q i) C t₀ ∧ IsRegFamilyC2 A' s' (S.ph a ∘ q i) (fun t => S.phT a t ∘ q i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.SysPull.pullback_common | exact GlobalTheory.CompanionTheory.Ar.PB.SysPull.pullback_common | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.SysPull.pullback_common <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSecond
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem gramPlane_posDef : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ w ∈ Un, (Gn w).PosDef := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b ca cb hb hab hca hcb X q Un Gn ΦYn ΦWn l H bp _ hF w hw
  unfold IsFibreData at hF
  obtain ⟨-, -, -, h4, h5, -, -⟩ := hF
  obtain ⟨hbp, hH⟩ := h4 w hw
  obtain ⟨hGbd, hGpd⟩ := BM.G_pos l τ (bp w) hbp
  obtain ⟨G₂, hG₂, hG₂eq, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.norm_three_steps N j a b ca cb (BM.G l τ (bp w)) (H τ w)
    M.j_le hb hab hca hcb hGbd hGpd (hH τ).1 (hH τ).2
  have hEq : Gn w = G₂ := Matrix.ext fun r s => by rw [h5 w hw r s, hG₂eq r s]
  rw [hEq]
  exact hG₂

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

