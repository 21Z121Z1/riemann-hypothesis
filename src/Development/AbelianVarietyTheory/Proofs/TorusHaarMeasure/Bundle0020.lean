import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDriftFunctionOrthonormalHermitianFrames
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

theorem lowerSemicontinuousOn_sum_pos_mul {Y : Type*} [TopologicalSpace Y] {s : Set Y}
    (I : Finset ℕ) (e : ℕ → ℝ) (he : ∀ i, 0 < e i) (α : ℕ → Y → ℝ)
    (hα : ∀ i ∈ I, LowerSemicontinuousOn (α i) s) :
    LowerSemicontinuousOn (fun x => ∑ i ∈ I, e i * α i x) s := by
  have key : ∀ i ∈ I, LowerSemicontinuousOn (fun x => e i * α i x) s := by
    intro i hi x hx y hy
    have h1 : y / e i < α i x := by
      rw [div_lt_iff₀ (he i)]
      linarith
    filter_upwards [hα i hi x hx (y / e i) h1] with z hz
    rw [gt_iff_lt, div_lt_iff₀ (he i)] at hz
    show y < e i * α i z
    linarith
  exact lowerSemicontinuousOn_sum key

theorem exists_drift_function_orthFrames : (∀ (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → ∀ (τ0 : X.Ψ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1)) → ∃ (f : Frame X.Ψ r → ℝ) (c b : ℝ), 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ LowerSemicontinuousOn f {x | IsOrth X x} ∧ (∀ x, IsOrth X x → 0 ≤ f x) ∧ (∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∀ x, IsOrth X x → f (lact γ x) = f x) ∧ (∀ x, IsOrth X x → ∑ a ∈ S, f (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) ≤ S.card * (c * f x + b)) ∧ ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ x, IsOrth X x → f x ≤ M → ε ≤ X.la1 x) := by
  intro r X hp0 hp0r τ0 S hS hirr hU
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_subspaceHeight_gramDeterminant r X
  obtain ⟨δ, hδ, hdrift⟩ := GlobalTheory.T.weighted_height_sup_drift_orthonormal_frames r X d hd τ0 S hS hirr hU
  obtain ⟨α, hlub, hlsc⟩ := exists_isLUB_height_rpow_lowerSemicontinuousOn r X d hd δ hδ
  obtain ⟨e, c, b, he, hc0, hc1, hb, hdr⟩ := hdrift α hlub
  have hdet : ∀ x, IsOrth X x → ∀ τ : X.Ψ, (mat x τ).det ≠ 0 := fun x hx => (GlobalTheory.T.majorant_eq_sum_norm_sq_orthonormalFrame r X x hx).1
  have hr : 0 < r := lt_trans hp0 hp0r
  have hlow : ∀ x, IsOrth X x → ∀ i ≤ r, ∀ W : Submodule E (Fin r → E),
      Module.finrank E W = i → 0 < d x W ∧ d x W ^ (-δ) ≤ α i x := by
    intro x hx i hi W hW
    obtain ⟨m, hm, hmW⟩ := GlobalTheory.T.exists_pos_le_latticeHeight_at_frame r X d hd x (hdet x hx)
    exact ⟨lt_of_lt_of_le hm (hmW W), (hlub i hi x (hdet x hx)).1 ⟨W, hW, rfl⟩⟩
  have hαnn : ∀ x, IsOrth X x → ∀ i ≤ r, 0 ≤ α i x := by
    intro x hx i hi
    obtain ⟨W, hW⟩ := exists_submodule_finrank_eq_of_le (K := E) hi
    obtain ⟨hpos, hle⟩ := hlow x hx i hi W hW
    exact le_trans (Real.rpow_nonneg hpos.le _) hle
  have hterm_nn : ∀ x, IsOrth X x → ∀ i ∈ Finset.Ioo 0 r, 0 ≤ e i * α i x := fun x hx i hi =>
    mul_nonneg (he i).le (hαnn x hx i (Finset.mem_Ioo.1 hi).2.le)
  refine ⟨fun x => ∑ i ∈ Finset.Ioo 0 r, e i * α i x, c, b, hc0, hc1, hb, ?_, ?_, ?_, hdr, ?_⟩
  · exact lowerSemicontinuousOn_sum_pos_mul _ e he α fun i hi =>
      (hlsc i (Finset.mem_Ioo.1 hi).2.le).mono fun x hx => hdet x hx
  · intro x hx
    exact Finset.sum_nonneg (hterm_nn x hx)
  · intro γ hγ x hx
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [GlobalTheory.T.heightSup_invariant_under_hermitianLattice_aut r X d hd δ α hlub γ hγ x (hdet x hx) i (Finset.mem_Ioo.1 hi).2.le]
  · intro M
    have h1 : (1 : ℕ) ∈ Finset.Ioo 0 r := Finset.mem_Ioo.2 ⟨Nat.one_pos, lt_of_le_of_lt hp0 hp0r⟩
    set K : ℝ := max (M / e 1) 1 with hK
    have hKpos : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
    obtain ⟨ε, hε, hεla⟩ := GlobalTheory.T.firstMinimum_lower_of_lineHeights r X d hd hr (K ^ (-1 / δ)) (Real.rpow_pos_of_pos hKpos _)
    refine ⟨ε, hε, fun x hx hfM => hεla x hx fun W hW => ?_⟩
    obtain ⟨hpos, hle⟩ := hlow x hx 1 (Finset.mem_Ioo.1 h1).2.le W hW
    have hsingle : e 1 * α 1 x ≤ M :=
      le_trans (Finset.single_le_sum (hterm_nn x hx) h1) hfM
    have hdK : d x W ^ (-δ) ≤ K := by
      refine le_trans hle (le_trans ?_ (le_max_left _ _))
      rw [le_div_iff₀ (he 1)]
      linarith
    have hpow : K ^ (-1 / δ) ≤ (d x W ^ (-δ)) ^ (-1 / δ) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hpos _) hdK
        (div_nonpos_of_nonpos_of_nonneg (by norm_num) hδ.le)
    rwa [← Real.rpow_mul hpos.le, show -δ * (-1 / δ) = 1 by field_simp, Real.rpow_one] at hpow

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IntegralEqIntegralTsumOfLintegral
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.UnfoldComplex

theorem integral_eq_integral_tsum_of_lintegral {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ ν : Measure α) (f : α → ℂ) (g : ι → α → ℂ) (hf : Measurable f) (hg : ∀ i, Measurable (g i))
    (H : ∀ φ : ℂ → ℝ≥0∞, Measurable φ → ∫⁻ z, φ (f z) ∂μ = ∫⁻ z, ∑' i, φ (g i z) ∂ν)
    (hi : Integrable f μ) : ∫ z, f z ∂μ = ∫ z, ∑' i, g i z ∂ν := by
  have hmap : μ.map f = Measure.sum fun i => ν.map (g i) := by
    ext s hs
    have hφ : Measurable (s.indicator (1 : ℂ → ℝ≥0∞)) := measurable_one.indicator hs
    have h1 := H _ hφ
    rw [lintegral_tsum (f := fun i z => s.indicator (1 : ℂ → ℝ≥0∞) (g i z))
      fun i => (hφ.comp (hg i)).aemeasurable] at h1
    rw [Measure.sum_apply _ hs, ← lintegral_indicator_one hs, lintegral_map hφ hf, h1]
    refine tsum_congr fun i => ?_
    rw [← lintegral_indicator_one hs, lintegral_map hφ (hg i)]
  have hfin : ∑' i, ∫⁻ z, ‖g i z‖ₑ ∂ν ≠ ⊤ := by
    have h1 := H (fun w => ‖w‖ₑ) measurable_enorm
    rw [lintegral_tsum fun i => (hg i).enorm.aemeasurable] at h1
    rw [← h1]
    exact hi.2.ne
  have hid : Integrable (fun w : ℂ => w) (μ.map f) :=
    (integrable_map_measure aestronglyMeasurable_id hf.aemeasurable).mpr hi
  rw [integral_tsum (fun i => (hg i).aestronglyMeasurable) hfin]
  calc ∫ z, f z ∂μ = ∫ w, w ∂(μ.map f) := (integral_map hf.aemeasurable aestronglyMeasurable_id).symm
    _ = ∑' i, ∫ w, w ∂(ν.map (g i)) := by
        rw [hmap] at hid ⊢
        exact integral_sum_measure hid
    _ = ∑' i, ∫ z, g i z ∂ν :=
        tsum_congr fun i => integral_map (hg i).aemeasurable aestronglyMeasurable_id

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in

theorem continuous_lact {r : ℕ} {Ψ : Finset (E →+* ℂ)} (δ : GL (Fin r) E) :
    Continuous (fun y : Frame Ψ r => lact δ y) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun y : Frame Ψ r =>
    ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ : Matrix (Fin r) (Fin r) ℂ)
  have hM : Continuous fun y : Frame Ψ r => mat y τ := continuous_apply τ
  exact continuous_const.matrix_mul hM

theorem unfold_integral :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ ψ : Frame X.Ψ r → ℝ≥0∞, Measurable ψ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) → ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 = ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ h : Frame X.Ψ r → ℂ, Measurable h → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, h (rmul x b) = h x) → Integrable (fun z => h (cpt X x0 z)) (muF X x0) → ∫ z, h (cpt X x0 z) ∂muF X x0 = ∫ z in FF, ∑' γ : X.Γ, h (lact γ.1 (cpt X x0 z)) ∂muF X x0) := by
  intro H r X x0 ho FF hFF h hm hinv hint
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hc : Measurable (cpt X x0) := (FundSetPf.cont_cpt X x0).measurable
  refine integral_eq_integral_tsum_of_lintegral (muF X x0) ((muF X x0).restrict FF)
    (fun z => h (cpt X x0 z)) (fun (γ : X.Γ) z => h (lact γ.1 (cpt X x0 z))) (hm.comp hc)
    (fun γ => hm.comp ((continuous_lact γ.1).measurable.comp hc)) ?_ hint
  intro φ hφ
  exact H r X x0 ho FF hFF (fun x => φ (h x)) (hφ.comp hm)
    (fun x hx b hb => by simp only [hinv x hx b hb])

end GlobalTheory.UnfoldComplex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetBorSat
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FrameMeas

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def borSat {r : ℕ} (X : Data E r) (C : Set (Frame X.Ψ r)) : Set (Frame X.Ψ r) :=
  {y | ∃ x ∈ C, ∃ b ∈ Bor X.Ψ r, y = rmul x b}

theorem borSat_subset_dom {r : ℕ} (X : Data E r) {C : Set (Frame X.Ψ r)} (hC : C ⊆ X.dom) :
    borSat X C ⊆ X.dom := by
  rintro y ⟨x, hx, b, hb, rfl⟩
  exact OrthogonalFrameDomain.rmul_mem_dom X (hC hx) hb

theorem subset_borSat {r : ℕ} (X : Data E r) (C : Set (Frame X.Ψ r)) : C ⊆ borSat X C :=
  fun x hx => ⟨x, hx, ExtFPf.oneF X, ExtFPf.oneF_mem X, (ExtFPf.rmul_oneF X x).symm⟩

theorem rmul_mem_borSat_iff {r : ℕ} (X : Data E r) (C : Set (Frame X.Ψ r)) {y b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : rmul y b ∈ borSat X C ↔ y ∈ borSat X C := by
  constructor
  · rintro ⟨x, hx, b', hb', h⟩
    refine ⟨x, hx, rmul b' (ExtFPf.invF X b), ExtFPf.mul_mem X hb' (ExtFPf.invF_mem X hb), ?_⟩
    rw [← ExtFPf.rmul_assoc, ← h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]
  · rintro ⟨x, hx, b', hb', rfl⟩
    exact ⟨x, hx, rmul b' b, ExtFPf.mul_mem X hb' hb, ExtFPf.rmul_assoc X _ _ _⟩

theorem measurableSet_borSat {r : ℕ} (X : Data E r) {C : Set (Frame X.Ψ r)} (hK : IsCompact C)
    (hC : C ⊆ X.dom) : MeasurableSet (borSat X C) := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hK
  let T : Set (Frame X.Ψ r × C) := {p | ∀ τ : X.Ψ, ∀ a c : Fin r, c < a →
    ((mat p.2.1 τ).adjugate * ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      mat p.1 τ) a c = 0}
  have hm : ∀ τ : X.Ψ, Continuous fun y : Frame X.Ψ r => mat y τ := fun τ => continuous_apply τ
  have hT : IsClosed T := by
    simp only [T, Set.setOf_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun c =>
      isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
    exact (((((hm τ).comp (continuous_subtype_val.comp continuous_snd)).matrix_adjugate).matrix_mul
      continuous_const).matrix_mul ((hm τ).comp continuous_fst)).matrix_elem a c
  have hT' : IsClosed (Prod.fst '' T) := isClosedMap_fst_of_compactSpace T hT
  have hU : IsOpen {y : Frame X.Ψ r | ∀ τ, (mat y τ).det ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun τ => isOpen_ne_fun (hm τ).matrix_det continuous_const
  have heq : borSat X C = {y : Frame X.Ψ r | ∀ τ, (mat y τ).det ≠ 0} ∩ Prod.fst '' T := by
    ext y
    constructor
    · intro hy
      have hyd : ∀ τ, (mat y τ).det ≠ 0 := fun τ => (borSat_subset_dom X hC hy τ).1
      obtain ⟨x, hx, b, hb, h⟩ := hy
      refine ⟨hyd, (y, ⟨x, hx⟩), ?_, rfl⟩
      exact (FundSetPf.charB 1 hyd fun τ => (hC hx τ).1).mp
        ⟨b, hb, by rw [FundSetPf.lact_one]; exact h⟩
    · rintro ⟨hyd, ⟨y', x, hx⟩, hp, rfl⟩
      obtain ⟨b, hb, h⟩ := (FundSetPf.charB 1 hyd fun τ => (hC hx τ).1).mpr hp
      rw [FundSetPf.lact_one] at h
      exact ⟨x, hx, b, hb, h⟩
  rw [heq]
  exact hU.measurableSet.inter hT'.measurableSet

theorem sat_eq_preimage {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) {C : Set (Frame X.Ψ r)}
    (hC : C ⊆ X.dom) : sat X x0 C = cpt X x0 ⁻¹' borSat X C := by
  ext z
  exact ⟨fun h => h.2, fun h => ⟨borSat_subset_dom X hC h, h⟩⟩

theorem frameMeas_of_local (hI : MeasInvStatement (E := E))
    (hL : ∀ (r : ℕ) (X : Data E r) (x1 : Frame X.Ψ r), IsOrth X x1 → ∀ b1 ∈ Bor X.Ψ r,
      ∃ U ∈ 𝓝 (rmul x1 b1), ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ G : Frame X.Ψ r → ℝ≥0∞, Measurable G →
        (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
        ∫⁻ x in U, G x ≤ K * ∫⁻ z, G (cpt X x1 z) ∂muF X x1) :
    FrameMeasStatement (E := E) := by
  intro r X x0 hx0 C hK hC
  have key : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ G : Frame X.Ψ r → ℝ≥0∞, Measurable G →
      (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
      ∫⁻ x in C, G x ≤ K * ∫⁻ z, G (cpt X x0 z) ∂muF X x0 := by
    refine hK.induction_on (p := fun s => ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ G : Frame X.Ψ r → ℝ≥0∞,
      Measurable G → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
      ∫⁻ x in s, G x ≤ K * ∫⁻ z, G (cpt X x0 z) ∂muF X x0) ?_ ?_ ?_ ?_
    · exact ⟨0, ENNReal.zero_lt_top, fun G _ _ => by simp⟩
    · rintro s t hst ⟨K, hK, h⟩
      exact ⟨K, hK, fun G hG hB => (lintegral_mono_set hst).trans (h G hG hB)⟩
    · rintro s t ⟨K, hK, h⟩ ⟨K', hK', h'⟩
      refine ⟨K + K', ENNReal.add_lt_top.mpr ⟨hK, hK'⟩, fun G hG hB => ?_⟩
      rw [add_mul]
      exact (lintegral_union_le _ _ _).trans (add_le_add (h G hG hB) (h' G hG hB))
    · intro x hx
      obtain ⟨x1, hx1, b1, hb1, rfl⟩ := ortho_holds r X x (hC hx)
      obtain ⟨U, hU, K, hK, h⟩ := hL r X x1 hx1 b1 hb1
      refine ⟨U, mem_nhdsWithin_of_mem_nhds hU, K, hK, fun G hG hB => ?_⟩
      rw [hI r X x0 x1 hx0 hx1 G hG hB]
      exact h G hG hB
  obtain ⟨K, hKt, h⟩ := key
  refine ⟨K, hKt, fun G hG hB => ?_⟩
  have hS := measurableSet_borSat X hK hC
  have h1 := h ((borSat X C).indicator G) (hG.indicator hS) (by
    intro x hx b hb
    by_cases hxS : x ∈ borSat X C
    · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem ((rmul_mem_borSat_iff X C hb).mpr hxS),
        hB x hx b hb]
    · rw [Set.indicator_of_notMem hxS,
        Set.indicator_of_notMem fun h => hxS ((rmul_mem_borSat_iff X C hb).mp h)])
  have h2 : ∫⁻ x in C, (borSat X C).indicator G x = ∫⁻ x in C, G x :=
    setLIntegral_congr_fun hK.measurableSet fun x hx =>
      Set.indicator_of_mem (subset_borSat X C hx) G
  have h3 : ∫⁻ z, (borSat X C).indicator G (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z in sat X x0 C, G (cpt X x0 z) ∂muF X x0 := by
    rw [sat_eq_preimage X x0 hC,
      ← lintegral_indicator ((FundSetPf.cont_cpt X x0).measurable hS)]
    rfl
  rw [← h2, ← h3]
  exact h1

end GlobalTheory.FrameMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetSatFrames
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Unfold

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def satFrames (X : Data E r) (x0 : Frame X.Ψ r) (A : Set (V (nd X))) : Set (Frame X.Ψ r) :=
  {x | ∃ z ∈ A, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x0 z) b}

theorem measurableSet_Bor (X : Data E r) : MeasurableSet (Bor X.Ψ r) := by
  have h : Bor X.Ψ r = ⋂ τ : X.Ψ, ({b : Frame X.Ψ r | (mat b τ).det ≠ 0} ∩
      ⋂ a : Fin r, ⋂ c : Fin r, ⋂ (_ : c < a), {b : Frame X.Ψ r | b τ a c = 0}) := by
    ext b; simp [Bor]
  rw [h]
  refine MeasurableSet.iInter fun τ => MeasurableSet.inter ?_ ?_
  · have hM : Continuous fun b : Frame X.Ψ r => mat b τ := continuous_apply τ
    exact (isOpen_ne_fun hM.matrix_det continuous_const).measurableSet
  · refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun c => MeasurableSet.iInter fun _ => ?_
    exact (isClosed_eq (by fun_prop) continuous_const).measurableSet

theorem continuous_rmul (X : Data E r) :
    Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => rmul p.1 p.2 := by
  refine continuous_pi fun τ => ?_
  have hM : Continuous fun b : Frame X.Ψ r => mat b τ := continuous_apply τ
  exact (hM.comp continuous_fst).matrix_mul (hM.comp continuous_snd)

theorem continuous_lact (X : Data E r) (γ : GL (Fin r) E) :
    Continuous fun x : Frame X.Ψ r => lact γ x := by
  refine continuous_pi fun τ => ?_
  have hM : Continuous fun b : Frame X.Ψ r => mat b τ := continuous_apply τ
  exact continuous_const.matrix_mul hM

theorem rmul_right_cancel (X : Data E r) {y b b' : Frame X.Ψ r} (hy : y ∈ X.dom)
    (h : rmul y b = rmul y b') : b = b' := by
  funext τ
  have h1 : mat y τ * mat b τ = mat y τ * mat b' τ := congrFun h τ
  have hu : IsUnit (mat y τ).det := isUnit_iff_ne_zero.mpr (hy τ).1
  have := congrArg (fun M => (mat y τ)⁻¹ * M) h1
  simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hu] at this
  exact this

theorem measurableSet_satFrames (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {A : Set (V (nd X))} (hA : MeasurableSet A) (hAO : A ⊆ OmF X x0) :
    MeasurableSet (satFrames X x0 A) := by
  have h : satFrames X x0 A =
      (fun p : V (nd X) × Frame X.Ψ r => rmul (cpt X x0 p.1) p.2) '' (A ×ˢ Bor X.Ψ r) := by
    ext x
    constructor
    · rintro ⟨z, hz, b, hb, rfl⟩; exact ⟨(z, b), ⟨hz, hb⟩, rfl⟩
    · rintro ⟨⟨z, b⟩, ⟨hz, hb⟩, rfl⟩; exact ⟨z, hz, b, hb, rfl⟩
  rw [h]
  have : PolishSpace (Fin r → ℂ) := inferInstance
  have : PolishSpace (Fin r → Fin r → ℂ) := inferInstance
  have : PolishSpace (Frame X.Ψ r) := inferInstance
  have : PolishSpace (V (nd X)) := inferInstance
  refine MeasurableSet.image_of_continuousOn_injOn (hA.prod (measurableSet_Bor X)) ?_ ?_
  · exact ((continuous_rmul X).comp (((FundSetPf.cont_cpt X x0).comp continuous_fst).prodMk
      continuous_snd)).continuousOn
  · rintro ⟨z, b⟩ ⟨hz, hb⟩ ⟨z', b'⟩ ⟨-, hb'⟩ hh
    obtain rfl : z = z' := FundSetPf.cpt_uniq X ho hb hb' hh
    exact Prod.ext rfl (rmul_right_cancel X (hAO hz) hh)

theorem rmul_mem_satFrames_iff (X : Data E r) (x0 : Frame X.Ψ r) (A : Set (V (nd X)))
    (x : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    rmul x b ∈ satFrames X x0 A ↔ x ∈ satFrames X x0 A := by
  constructor
  · rintro ⟨z, hz, b', hb', h⟩
    refine ⟨z, hz, rmul b' (ExtFPf.invF X b), ExtFPf.mul_mem X hb' (ExtFPf.invF_mem X hb), ?_⟩
    rw [← ExtFPf.rmul_assoc, ← h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]
  · rintro ⟨z, hz, b', hb', rfl⟩
    exact ⟨z, hz, rmul b' b, ExtFPf.mul_mem X hb' hb, by rw [ExtFPf.rmul_assoc]⟩

theorem cpt_mem_satFrames_iff (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    (A : Set (V (nd X))) (z : V (nd X)) : cpt X x0 z ∈ satFrames X x0 A ↔ z ∈ A := by
  constructor
  · rintro ⟨z', hz', b, hb, h⟩
    rw [← ExtFPf.rmul_oneF X (cpt X x0 z)] at h
    rw [FundSetPf.cpt_uniq X ho (ExtFPf.oneF_mem X) hb h]; exact hz'
  · intro hz
    exact ⟨z, hz, ExtFPf.oneF X, ExtFPf.oneF_mem X, (ExtFPf.rmul_oneF X _).symm⟩

theorem cpt_lact (X : Data E r) (x0 : Frame X.Ψ r) (γ : GL (Fin r) E) (z : V (nd X)) :
    cpt X (lact γ x0) z = lact γ (cpt X x0 z) := (FundSetPf.lact_rmul γ _ _).symm

theorem isOrth_lact (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) : IsOrth X (lact γ x0) := fun τ => by
  rw [OntoS.gram_lact X hγ]; exact ho τ

theorem muF_lact (X : Data E r) (x0 : Frame X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    muF X (lact γ x0) = muF X x0 := by
  have h1 : OmF X (lact γ x0) = OmF X x0 := by
    ext z
    show cpt X (lact γ x0) z ∈ X.dom ↔ cpt X x0 z ∈ X.dom
    rw [cpt_lact]
    refine ⟨fun h => ?_, OntoS.dom_lact X hγ⟩
    have := OntoS.dom_lact X (X.Γ.inv_mem hγ) h
    rwa [FundSetPf.lact_inv] at this
  have h2 : densF X (lact γ x0) = densF X x0 := by
    funext z
    simp only [densF, dmin, cpt_lact, OntoS.gram_lact X hγ]
  simp only [muF, h1, h2]

theorem unique_translate (X : Data E r) {x0 : Frame X.Ψ r} {FF : Set (V (nd X))}
    (hF : IsFundSet X x0 FF) {x : Frame X.Ψ r} {γ γ' : GL (Fin r) E} (hγ : γ ∈ X.Γ) (hγ' : γ' ∈ X.Γ)
    (h : lact γ⁻¹ x ∈ satFrames X x0 FF) (h' : lact γ'⁻¹ x ∈ satFrames X x0 FF) : γ = γ' := by
  obtain ⟨z, hz, b, hb, h⟩ := h
  obtain ⟨z', hz', b', hb', h'⟩ := h'
  have hδ : γ'⁻¹ * γ ∈ X.Γ := X.Γ.mul_mem (X.Γ.inv_mem hγ') hγ
  have e1 : lact (γ'⁻¹ * γ) (rmul (cpt X x0 z) b) = rmul (cpt X x0 z') b' := by
    rw [← h, ← h', ← FundSetPf.lact_mul, mul_assoc, mul_inv_cancel, mul_one]
  have hbb := ExtFPf.mul_mem X hb (ExtFPf.invF_mem X hb')
  have e2 : cpt X x0 z' = lact (γ'⁻¹ * γ) (rmul (cpt X x0 z) (rmul b (ExtFPf.invF X b'))) := by
    rw [← ExtFPf.rmul_assoc, FundSetPf.lact_rmul, e1, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb',
      ExtFPf.rmul_oneF]
  obtain rfl : z = z' := hF.2.2.1 z hz z' hz' _ hδ _ hbb e2
  have e3 : lact (γ'⁻¹ * γ) (cpt X x0 z) = rmul (cpt X x0 z) (rmul b' (ExtFPf.invF X b)) := by
    rw [← ExtFPf.rmul_assoc, ← e1, ← FundSetPf.lact_rmul, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb,
      ExtFPf.rmul_oneF]
  have := X.Γ_free _ hδ _ (hF.2.1 hz) _ (ExtFPf.mul_mem X hb' (ExtFPf.invF_mem X hb)) e3
  exact (inv_mul_eq_one.mp this).symm

theorem lintegral_unfold (hM : MeasInvStatement (E := E)) (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r)
    (ho : IsOrth X x0) (FF : Set (V (nd X))) (hF : IsFundSet X x0 FF) (ψ : Frame X.Ψ r → ℝ≥0∞)
    (hψ : Measurable ψ) (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) :
    ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0 := by
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hS := measurableSet_satFrames X ho hF.1 hF.2.1
  have hc : Measurable (cpt X x0) := (FundSetPf.cont_cpt X x0).measurable
  let φ : X.Γ → Frame X.Ψ r → ℝ≥0∞ := fun γ =>
    ((fun x => lact (γ.1)⁻¹ x) ⁻¹' satFrames X x0 FF).indicator ψ
  have hφm : ∀ γ, Measurable (φ γ) := fun γ =>
    hψ.indicator ((continuous_lact X _).measurable hS)
  have hφB : ∀ γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ γ (rmul x b) = φ γ x := by
    intro γ x hx b hb
    simp only [φ, Set.indicator, Set.mem_preimage, FundSetPf.lact_rmul,
      rmul_mem_satFrames_iff X x0 FF _ hb, hB x hx b hb]
  have h1 : ∀ᵐ z ∂muF X x0, ψ (cpt X x0 z) = ∑' γ : X.Γ, φ γ (cpt X x0 z) := by
    filter_upwards [hF.2.2.2] with z hz
    obtain ⟨z', hz', γ, hγ, b, hb, h⟩ := hz
    have hm : lact γ⁻¹ (cpt X x0 z) ∈ satFrames X x0 FF :=
      ⟨z', hz', b, hb, by rw [h, FundSetPf.lact_inv]⟩
    rw [tsum_eq_single (⟨γ, hγ⟩ : X.Γ)]
    · exact (Set.indicator_of_mem (s := (fun x => lact γ⁻¹ x) ⁻¹' satFrames X x0 FF) hm ψ).symm
    · intro γ' hne
      refine Set.indicator_of_notMem (fun hm' => hne ?_) ψ
      exact Subtype.ext (unique_translate X hF γ'.2 hγ hm' hm)
  rw [lintegral_congr_ae h1,
    lintegral_tsum (f := fun γ z => φ γ (cpt X x0 z)) fun γ => ((hφm γ).comp hc).aemeasurable,
    lintegral_tsum (f := fun (γ : X.Γ) z => ψ (lact γ.1 (cpt X x0 z))) fun γ : X.Γ =>
      ((hψ.comp (continuous_lact X γ.1).measurable).comp hc).aemeasurable]
  refine tsum_congr fun γ => ?_
  rw [hM r X x0 (lact γ.1 x0) ho (isOrth_lact X ho γ.2) (φ γ) (hφm γ) (hφB γ), muF_lact X x0 γ.2,
    ← lintegral_indicator hF.1]
  refine lintegral_congr fun z => ?_
  simp only [φ, Set.indicator, Set.mem_preimage, cpt_lact, FundSetPf.lact_inv,
    cpt_mem_satFrames_iff X ho]

end GlobalTheory.Unfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PropDiscOfFlagDomainData
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst

namespace GlobalTheory

theorem propDisc_of_flagDomainData :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), PropDisc X :=
  fun _ _ _ _ => GlobalTheory.ClosedDiscontinuity.propDisc_and_la1GG.1

end GlobalTheory
end

