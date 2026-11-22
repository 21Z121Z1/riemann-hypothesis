import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0036

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PManifoldZerosComplementConnected
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Set

theorem ManifoldZerosComplementConnected.isPreconnected_of_local {α : Type*} [TopologicalSpace α]
    {X S : Set α} (hX : IsPreconnected X) (hSX : S ⊆ X) (hdense : ∀ x ∈ X, x ∈ closure S)
    (hloc : ∀ x ∈ X, ∃ W, IsOpen W ∧ x ∈ W ∧ IsPreconnected (W ∩ S)) : IsPreconnected S := by
  intro u v hu hv hSuv ⟨a, haS, hau⟩ ⟨b, hbS, hbv⟩
  by_contra hne
  have hne' : ∀ y ∈ S, y ∈ u → y ∈ v → False := fun y hy hyu hyv => hne ⟨y, hy, hyu, hyv⟩
  let P : Set α := {x | ∃ W, IsOpen W ∧ x ∈ W ∧ W ∩ S ⊆ u}
  let Q : Set α := {x | ∃ W, IsOpen W ∧ x ∈ W ∧ W ∩ S ⊆ v}
  have hP : IsOpen P := isOpen_iff_forall_mem_open.mpr fun x ⟨W, hW, hxW, hWS⟩ =>
    ⟨W, fun y hy => ⟨W, hW, hy, hWS⟩, hW, hxW⟩
  have hQ : IsOpen Q := isOpen_iff_forall_mem_open.mpr fun x ⟨W, hW, hxW, hWS⟩ =>
    ⟨W, fun y hy => ⟨W, hW, hy, hWS⟩, hW, hxW⟩
  have hcov : X ⊆ P ∪ Q := by
    intro x hx
    obtain ⟨W, hW, hxW, hWc⟩ := hloc x hx
    by_cases h1 : (W ∩ S ∩ u).Nonempty
    · by_cases h2 : (W ∩ S ∩ v).Nonempty
      · obtain ⟨y, hyWS, hyu, hyv⟩ := hWc u v hu hv (fun y hy => hSuv hy.2) h1 h2
        exact (hne' y hyWS.2 hyu hyv).elim
      · refine Or.inl ⟨W, hW, hxW, fun y hy => ?_⟩
        rcases hSuv hy.2 with h | h
        · exact h
        · exact absurd ⟨y, hy, h⟩ h2
    · refine Or.inr ⟨W, hW, hxW, fun y hy => ?_⟩
      rcases hSuv hy.2 with h | h
      · exact absurd ⟨y, hy, h⟩ h1
      · exact h
  obtain ⟨x, hxX, ⟨W₁, hW₁, hxW₁, hW₁u⟩, ⟨W₂, hW₂, hxW₂, hW₂v⟩⟩ :=
    hX P Q hP hQ hcov ⟨a, hSX haS, u, hu, hau, inter_subset_left⟩
      ⟨b, hSX hbS, v, hv, hbv, inter_subset_left⟩
  obtain ⟨y, ⟨hy₁, hy₂⟩, hyS⟩ := mem_closure_iff.mp (hdense x hxX) _ (hW₁.inter hW₂) ⟨hxW₁, hxW₂⟩
  exact hne' y hyS (hW₁u ⟨hy₁, hyS⟩) (hW₂v ⟨hy₂, hyS⟩)

theorem ManifoldZerosComplementConnected.isPreconnected_ball_diff_countable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : 1 < Module.rank ℝ E) (c : E) {r : ℝ} (hr : 0 < r)
    {s : Set E} (hs : s.Countable) : IsPreconnected (Metric.ball c r \ s) := by
  let e : OpenPartialHomeomorph E E := OpenPartialHomeomorph.univBall c r
  have hsrc : e.source = univ := OpenPartialHomeomorph.univBall_source c r
  have htgt : e.target = Metric.ball c r := OpenPartialHomeomorph.univBall_target c hr
  have hc : (e ⁻¹' s).Countable := hs.preimage_of_injOn (e.injOn.mono (by rw [hsrc]; exact subset_univ _))
  have hcont : ContinuousOn e univ := hsrc ▸ e.continuousOn
  have heq : e '' (e ⁻¹' s)ᶜ = Metric.ball c r \ s := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨htgt ▸ e.map_source (hsrc ▸ mem_univ v), hv⟩
    · rintro ⟨hw, hws⟩
      rw [← htgt] at hw
      exact ⟨e.symm w, by simpa [mem_compl_iff, mem_preimage, e.right_inv hw] using hws, e.right_inv hw⟩
  rw [← heq]
  exact (hc.isConnected_compl_of_one_lt_rank hE).isPreconnected.image e (hcont.mono (subset_univ _))

theorem ManifoldZerosComplementConnected.isPreconnected_inter_ne_zero_of_complex {V : Set ℂ}
    (hVo : IsOpen V) (hV : IsPreconnected V) {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ V) {z₀ : ℂ}
    (hz₀ : z₀ ∈ V) (hφz₀ : φ z₀ ≠ 0) : IsPreconnected (V ∩ {z | φ z ≠ 0}) := by
  have hev : ∀ z ∈ V, ∀ᶠ w in 𝓝[≠] z, φ w ≠ 0 := by
    intro z hz
    rcases (hφ z hz).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (hφ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hV hz h hz₀) hφz₀
    · exact h
  refine ManifoldZerosComplementConnected.isPreconnected_of_local hV inter_subset_left ?_ ?_
  · intro z hz
    have h1 : ∀ᶠ w in 𝓝[≠] z, w ∈ V ∩ {z | φ z ≠ 0} :=
      ((hev z hz).and (nhdsWithin_le_nhds (hVo.mem_nhds hz))).mono fun w hw => ⟨hw.2, hw.1⟩
    exact mem_closure_iff_frequently.mpr (h1.frequently.filter_mono nhdsWithin_le_nhds)
  · intro z hz
    obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hVo z hz
    obtain ⟨r', hr', hr'φ⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp (hev z hz))
    have hρ : 0 < min r r' := lt_min hr hr'
    refine ⟨Metric.ball z (min r r'), Metric.isOpen_ball, Metric.mem_ball_self hρ, ?_⟩
    have heq : Metric.ball z (min r r') ∩ (V ∩ {w | φ w ≠ 0}) =
        Metric.ball z (min r r') \ ({z} \ {w | φ w ≠ 0}) := by
      ext w
      simp only [mem_inter_iff, Set.mem_sdiff, mem_singleton_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨hb, -, hne⟩
        exact ⟨hb, fun h => h.2 hne⟩
      · rintro ⟨hb, hw⟩
        refine ⟨hb, hrV (Metric.ball_subset_ball (min_le_left _ _) hb), ?_⟩
        by_cases hwz : w = z
        · intro h0
          exact hw ⟨hwz, fun h => h h0⟩
        · exact hr'φ w (Metric.ball_subset_ball (min_le_right _ _) hb) hwz
    rw [heq]
    exact ManifoldZerosComplementConnected.isPreconnected_ball_diff_countable
      (by rw [Complex.rank_real_complex]; exact_mod_cast (by norm_num : (1 : ℕ) < 2)) z hρ ((countable_singleton z).mono sdiff_subset)

theorem ManifoldZerosComplementConnected.isPreconnected_convex_inter_ne_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} (hUo : IsOpen U) (hUc : Convex ℝ U)
    {f : E → ℂ} (hf : AnalyticOnNhd ℂ f U) : IsPreconnected (U ∩ {z | f z ≠ 0}) := by
  refine isPreconnected_of_forall_pair ?_
  rintro p ⟨hpU, hp⟩ q ⟨hqU, hq⟩
  let ℓ : ℂ → E := fun t => p + t • (q - p)
  have hℓc : Continuous ℓ := by fun_prop
  have hℓa : ∀ t, AnalyticAt ℂ ℓ t := fun t =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hVo : IsOpen (ℓ ⁻¹' U) := hUo.preimage hℓc
  have hVc : Convex ℝ (ℓ ⁻¹' U) := by
    intro a ha b hb s t hs ht hst
    have hmem := hUc ha hb hs ht hst
    show ℓ (s • a + t • b) ∈ U
    convert hmem using 1
    obtain rfl : t = 1 - s := by linarith
    simp only [ℓ, ← Complex.coe_smul]
    push_cast
    module
  have h0 : (0 : ℂ) ∈ ℓ ⁻¹' U := by simpa [ℓ] using hpU
  have h1 : (1 : ℂ) ∈ ℓ ⁻¹' U := by simpa [ℓ] using hqU
  refine ⟨ℓ '' (ℓ ⁻¹' U ∩ {t | f (ℓ t) ≠ 0}), ?_, ⟨0, ⟨h0, by simpa [ℓ] using hp⟩, by simp [ℓ]⟩,
    ⟨1, ⟨h1, by simpa [ℓ] using hq⟩, by simp [ℓ]⟩, ?_⟩
  · rintro _ ⟨t, ⟨htV, ht⟩, rfl⟩
    exact ⟨htV, ht⟩
  · exact (ManifoldZerosComplementConnected.isPreconnected_inter_ne_zero_of_complex hVo
      hVc.isPreconnected (φ := fun t => f (ℓ t)) (fun t ht => (hf (ℓ t) ht).comp (hℓa t)) h0
      (by simpa [ℓ] using hp)).image ℓ hℓc.continuousOn

theorem ManifoldZerosComplementConnected.proof : ManifoldZerosComplementConnected.Statement := by
  intro σ _ R h hR hreg hh ⟨x₀, hx₀R, hx₀⟩

  have chart : ∀ x ∈ R, ∃ (d : ℕ) (B : Set (Fin d → ℂ)) (W : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen B ∧ Convex ℝ B ∧ IsOpen W ∧ x ∈ W ∧ AnalyticOnNhd ℂ g B ∧ R ∩ W = g '' B := by
    intro x hx
    obtain ⟨-, d, A, O, V, g, hO, hV, hxV, hg, hAg, hRV⟩ := hreg x hx
    have hxO : A x ∈ O := by
      obtain ⟨y, hy, hgy⟩ : x ∈ g '' O := hRV ▸ ⟨hx, hxV⟩
      rw [← hgy, hAg y hy]
      exact hy
    obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO (A x) hxO
    refine ⟨d, Metric.ball (A x) ε, V ∩ A ⁻¹' Metric.ball (A x) ε, g, Metric.isOpen_ball,
      convex_ball _ _, hV.inter (Metric.isOpen_ball.preimage A.continuous),
      ⟨hxV, Metric.mem_ball_self hε⟩, hg.mono hεO, ?_⟩
    ext z
    constructor
    · rintro ⟨hzR, hzV, hzB⟩
      obtain ⟨y, hy, rfl⟩ : z ∈ g '' O := hRV ▸ ⟨hzR, hzV⟩
      have hAy : A (g y) ∈ Metric.ball (A x) ε := hzB
      rw [hAg y hy] at hAy
      exact ⟨y, hAy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      have hgy : g y ∈ R ∩ V := by rw [hRV]; exact ⟨y, hεO hy, rfl⟩
      refine ⟨hgy.1, hgy.2, ?_⟩
      show A (g y) ∈ Metric.ball (A x) ε
      rw [hAg y (hεO hy)]
      exact hy
  have chartR : ∀ {d : ℕ} {B : Set (Fin d → ℂ)} {W : Set (σ → ℂ)} {g : (Fin d → ℂ) → σ → ℂ},
      R ∩ W = g '' B → ∀ y ∈ B, g y ∈ R := by
    intro d B W g hRW y hy
    have : g y ∈ R ∩ W := by rw [hRW]; exact ⟨y, hy, rfl⟩
    exact this.1

  let T : Set (σ → ℂ) := {x | ∀ᶠ z in 𝓝 x, z ∈ R → h z = 0}
  have hTo : IsOpen T := isOpen_setOfPred_eventually_nhds
  let T₂ : Set (σ → ℂ) := {x | ∃ W, IsOpen W ∧ x ∈ W ∧ ∀ z ∈ W ∩ R, z ∉ T}
  have hT₂o : IsOpen T₂ := isOpen_iff_forall_mem_open.mpr fun x ⟨W, hW, hxW, hWT⟩ =>
    ⟨W, fun y hy => ⟨W, hW, hy, hWT⟩, hW, hxW⟩
  have hcov : R ⊆ T ∪ T₂ := by
    intro x hx
    obtain ⟨d, B, W, g, hBo, hBc, hWo, hxW, hg, hRW⟩ := chart x hx
    have hhg : AnalyticOnNhd ℂ (fun y => h (g y)) B := fun y hy =>
      (hh (g y) (chartR hRW y hy)).comp (hg y hy)
    by_cases hzero : ∃ y ∈ B, ∀ᶠ y' in 𝓝 y, h (g y') = 0
    · obtain ⟨y, hy, hev⟩ := hzero
      have hEq := hhg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hBc.isPreconnected hy hev
      left
      show ∀ᶠ z in 𝓝 x, z ∈ R → h z = 0
      filter_upwards [hWo.mem_nhds hxW] with z hzW hzR
      obtain ⟨y', hy', rfl⟩ : z ∈ g '' B := hRW ▸ ⟨hzR, hzW⟩
      exact hEq hy'
    · right
      refine ⟨W, hWo, hxW, ?_⟩
      rintro z ⟨hzW, hzR⟩ hzT
      obtain ⟨y, hy, rfl⟩ : z ∈ g '' B := hRW ▸ ⟨hzR, hzW⟩
      have hzT' : ∀ᶠ w in 𝓝 (g y), w ∈ R → h w = 0 := hzT
      refine hzero ⟨y, hy, ?_⟩
      filter_upwards [(hg y hy).continuousAt.tendsto.eventually hzT', hBo.mem_nhds hy] with y' h1 h2
      exact h1 (chartR hRW y' h2)

  have hTR : ∀ x ∈ R, ¬ ∀ᶠ z in 𝓝 x, z ∈ R → h z = 0 := by
    intro x hx hxT
    have hx₀T₂ : x₀ ∈ T₂ := by
      rcases hcov hx₀R with h1 | h1
      · exact absurd ((show ∀ᶠ z in 𝓝 x₀, z ∈ R → h z = 0 from h1).self_of_nhds hx₀R) hx₀
      · exact h1
    obtain ⟨y, hyR, hyT, W, -, hyW, hWT⟩ := hR T T₂ hTo hT₂o hcov ⟨x, hx, hxT⟩ ⟨x₀, hx₀R, hx₀T₂⟩
    exact hWT y ⟨hyW, hyR⟩ hyT
  refine ManifoldZerosComplementConnected.isPreconnected_of_local hR sdiff_subset ?_ ?_
  · intro x hx
    rw [mem_closure_iff_frequently]
    exact (Filter.not_eventually.mp (hTR x hx)).mono fun z hz => Classical.not_imp.mp hz
  · intro x hx
    obtain ⟨d, B, W, g, hBo, hBc, hWo, hxW, hg, hRW⟩ := chart x hx
    have hhg : AnalyticOnNhd ℂ (fun y => h (g y)) B := fun y hy =>
      (hh (g y) (chartR hRW y hy)).comp (hg y hy)
    refine ⟨W, hWo, hxW, ?_⟩
    have heq : W ∩ (R \ {z | h z = 0}) = g '' (B ∩ {y | h (g y) ≠ 0}) := by
      ext z
      constructor
      · rintro ⟨hzW, hzR, hz⟩
        obtain ⟨y, hy, rfl⟩ : z ∈ g '' B := hRW ▸ ⟨hzR, hzW⟩
        exact ⟨y, ⟨hy, hz⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
        have hgy : g y ∈ R ∩ W := by rw [hRW]; exact ⟨y, hy, rfl⟩
        exact ⟨hgy.2, hgy.1, hy'⟩
    rw [heq]
    exact (ManifoldZerosComplementConnected.isPreconnected_convex_inter_ne_zero hBo hBc hhg).image g
      (hg.continuousOn.mono inter_subset_left)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMassFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

open scoped ENNReal

noncomputable section

namespace MassFinite

theorem exists_frame {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)),
      ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (b i) z = ∑ j, U i j * z j := by
  classical
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 fun j => star (U i j)
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i k
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hU) i) k
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    simp [v, PiLp.inner_apply, Matrix.star_apply, mul_comm]
  refine ⟨OrthonormalBasis.mk hv (hv.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)).ge,
    fun i z => ?_⟩
  rw [OrthonormalBasis.coe_mk]
  simp [v, PiLp.inner_apply, mul_comm]

theorem eval_pullback {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (P : MvPolynomial (Fin d) ℂ)
    (x : Fin n → ℂ) : eval x (ComplexSets.pullback A P) = eval (A *ᵥ x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [ComplexSets.pullback]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    simp [ComplexSets.pullback, ComplexSets.linPoly, Matrix.mulVec, dotProduct]

theorem dim_sup_lt {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (f : MvPolynomial (Fin n) ℂ) (hf : f ∉ J) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {f})) < d := by
  have := hJ
  have hr : Ideal.Quotient.mk J f ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have h := ringKrullDim_succ_le_of_surjective
    (Ideal.Quotient.factor (le_sup_left : J ≤ J ⊔ Ideal.span {f}))
    (Ideal.Quotient.factor_surjective _) hr
    (by
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  rw [hd] at h
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {f})) = x at h ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    have h' : e + 1 ≤ (d : ℕ∞) := by exact_mod_cast h
    have he : e ≠ ⊤ := fun he => by simp [he] at h'
    exact_mod_cast (ENat.add_one_le_iff he).mp h'

theorem ball_lt_top {ι : Type*} [Fintype ι] (R : ℝ) :
    μH[((2 * Fintype.card ι : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ ι) R) < ⊤ := by
  have hfr : Module.finrank ℝ (ι × Fin 2 → ℝ) = Module.finrank ℝ (EuclideanSpace ℂ ι) := by
    rw [Module.finrank_fintype_fun_eq_card, ← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ ι),
      Complex.finrank_real_complex, finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, mul_comm]
  let e := (LinearEquiv.ofFinrankEq _ _ hfr).toContinuousLinearEquiv
  have hcard : ((2 * Fintype.card ι : ℕ) : ℝ) = ((Fintype.card (ι × Fin 2) : ℕ) : ℝ) := by
    simp [mul_comm]
  have hsub : Metric.ball (0 : EuclideanSpace ℂ ι) R ⊆ e '' (e.symm '' Metric.ball 0 R) := by
    rw [Set.image_image]
    simp
  have hb : Bornology.IsBounded (e.symm '' Metric.ball (0 : EuclideanSpace ℂ ι) R) :=
    e.symm.lipschitz.isBounded_image Metric.isBounded_ball
  rw [hcard]
  calc μH[((Fintype.card (ι × Fin 2) : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ ι) R)
      ≤ μH[((Fintype.card (ι × Fin 2) : ℕ) : ℝ)] (e '' (e.symm '' Metric.ball 0 R)) := measure_mono hsub
    _ ≤ _ := e.lipschitz.hausdorffMeasure_image_le (by positivity) _
    _ < ⊤ := by
      refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.coe_ne_top) ?_
      rw [hausdorffMeasure_pi_real]
      exact hb.measure_lt_top

theorem count_le {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (U : Matrix (Fin n) (Fin n) ℂ)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hb : ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (b i) z = ∑ j, U i j * z j)
    (I : Finset (Fin n)) (hI : I.card = d) (S : Set (EuclideanSpace ℂ (Fin n)))
    (hS : S ⊆ zeroSetEuc J) (N : ℕ)
    (hN : ∀ y, (ComplexSets.fibre J (U.submatrix (I.orderEmbOfFin hI) id) y).Finite ∧
      (ComplexSets.fibre J (U.submatrix (I.orderEmbOfFin hI) id) y).ncard ≤ N)
    (x : I → ℂ) : frameFibreCount b I S x ≤ N := by
  set e := I.orderIsoOfFin hI
  set A := U.submatrix (I.orderEmbOfFin hI) id
  let y : Fin d → ℂ := fun k => x (e k)
  have hsub : WithLp.ofLp '' {z ∈ S | frameProj b I z = x} ⊆ ComplexSets.fibre J A y := by
    rintro _ ⟨z, ⟨hzS, hzx⟩, rfl⟩
    refine ⟨fun q hq => hS hzS q hq, ?_⟩
    funext k
    have h1 := congrFun hzx (e k)
    simp only [frameProj, hb] at h1
    simp only [y, ← h1, A, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id,
      Finset.coe_orderIsoOfFin_apply, e]
  have hinj : Set.InjOn (WithLp.ofLp (p := 2)) {z ∈ S | frameProj b I z = x} :=
    (WithLp.ofLp_injective 2).injOn
  unfold frameFibreCount
  rw [← hinj.encard_image, ← (hN y).1.subset hsub |>.cast_ncard_eq]
  have h2 := Set.ncard_le_ncard hsub (hN y).1
  have h3 := (hN y).2
  exact_mod_cast h2.trans h3

theorem good_localGraph {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (U : Matrix (Fin n) (Fin n) ℂ)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hb : ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (b i) z = ∑ j, U i j * z j)
    (I₀ : Finset (Fin n)) (hI : I₀.card = d) (P : MvPolynomial (Fin d) ℂ)
    (hP : ∀ y : Fin d → ℂ, eval y P ≠ 0 →
      ∀ x ∈ ComplexSets.fibre J (U.submatrix (I₀.orderEmbOfFin hI) id) y,
        ∃ (U' : Set (Fin d → ℂ)) (V : Set (Fin n → ℂ)) (g : (Fin d → ℂ) → (Fin n → ℂ)),
          IsOpen U' ∧ y ∈ U' ∧ IsOpen V ∧ x ∈ V ∧ DifferentiableOn ℂ g U' ∧ g y = x ∧
          (∀ w ∈ U', U.submatrix (I₀.orderEmbOfFin hI) id *ᵥ g w = w) ∧
          ComplexSets.zeroSet J ∩ V = g '' U') :
    ∀ z ∈ zeroSetEuc J ∩ {z | eval (U.submatrix (I₀.orderEmbOfFin hI) id *ᵥ WithLp.ofLp z) P ≠ 0},
      ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
        (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧
          DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧
          (zeroSetEuc J ∩ {z | eval (U.submatrix (I₀.orderEmbOfFin hI) id *ᵥ WithLp.ofLp z) P ≠ 0}) ∩ V =
            g '' Ω := by
  set A := U.submatrix (I₀.orderEmbOfFin hI) id
  set e := I₀.orderIsoOfFin hI
  rintro z ⟨hzZ, hzP⟩
  obtain ⟨U', V, g, hU', -, hV, hzV, hg, -, hAg, hZV⟩ := hP _ hzP (WithLp.ofLp z) ⟨hzZ, rfl⟩
  let σ : (I₀ → ℂ) →L[ℂ] (Fin d → ℂ) := ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (e k)
  have hσ : ∀ w k, σ w k = w (e k) := fun _ _ => rfl
  let L := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm
  have hL : ∀ v, L v = WithLp.toLp 2 v := fun _ => rfl
  have hcP : Continuous fun w : Fin d → ℂ => eval w P := MvPolynomial.continuous_eval P
  have hcA : Continuous fun z' : EuclideanSpace ℂ (Fin n) => A *ᵥ WithLp.ofLp z' :=
    (Continuous.matrix_mulVec continuous_const continuous_id).comp (PiLp.continuous_ofLp 2 _)
  refine ⟨σ ⁻¹' (U' ∩ {w | eval w P ≠ 0}),
    {z' | WithLp.ofLp z' ∈ V ∧ eval (A *ᵥ WithLp.ofLp z') P ≠ 0}, fun w => L (g (σ w)),
    (hU'.inter (isOpen_ne_fun hcP continuous_const)).preimage σ.continuous,
    (hV.preimage (PiLp.continuous_ofLp 2 _)).inter (isOpen_ne_fun (hcP.comp hcA) continuous_const),
    ⟨hzV, hzP⟩, L.differentiable.comp_differentiableOn (hg.comp σ.differentiable.differentiableOn
      fun w hw => hw.1), fun w hw => ?_, ?_⟩
  · funext i
    have h1 := congrFun (hAg _ hw.1) (e.symm i)
    simp only [A, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, hσ,
      ← Finset.coe_orderIsoOfFin_apply, e, OrderIso.apply_symm_apply] at h1
    simp only [frameProj, hb, hL]
    simpa using h1
  · ext z'
    constructor
    · rintro ⟨⟨hz'Z, -⟩, hz'V, hz'P⟩
      have hmem : WithLp.ofLp z' ∈ ComplexSets.zeroSet J ∩ V := ⟨hz'Z, hz'V⟩
      rw [hZV] at hmem
      obtain ⟨w0, hw0, hgw0⟩ := hmem
      have hσw : σ (fun i => w0 (e.symm i)) = w0 := by
        funext k
        simp [hσ]
      refine ⟨fun i => w0 (e.symm i), ⟨by rw [hσw]; exact hw0, ?_⟩, ?_⟩
      · rw [Set.mem_ofPred_eq, hσw, ← hAg w0 hw0, hgw0]
        exact hz'P
      · simp only [hσw, hL, hgw0]
    · rintro ⟨w, ⟨hwU, hwP⟩, rfl⟩
      have hmem : g (σ w) ∈ ComplexSets.zeroSet J ∩ V := hZV ▸ ⟨σ w, hwU, rfl⟩
      have hA : A *ᵥ WithLp.ofLp (L (g (σ w))) = σ w := hAg _ hwU
      refine ⟨⟨fun q hq => hmem.1 q hq, ?_⟩, hmem.2, ?_⟩
      · rw [Set.mem_ofPred_eq, hA]
        exact hwP
      · rw [hA]
        exact hwP

end MassFinite

theorem MassFinite.proof (hG : ComplexSets.GenericProjectionFinite.Statement)
    (hF : ComplexSets.FibreBound.Statement) (hD : ComplexSets.DiscriminantCover.Statement)
    (hN : NullSmaller.Statement) (hL : LocalGraphMass.Statement) : MassFinite.Statement := by
  intro n d J hJ hd R
  have hdn : d ≤ n := by
    have h1 := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h1
    simpa using h1
  obtain ⟨U, hU, hUfin⟩ := (hG n d J hJ hd).2.2.2 1 (fun _ => 1)
  obtain ⟨b, hb⟩ := MassFinite.exists_frame U hU
  have hfin : ∀ (I : Finset (Fin n)) (hI : I.card = d),
      ComplexSets.IsFiniteProjection J (U.submatrix (I.orderEmbOfFin hI) id) := fun I hI => by
    simpa using hUfin 0 (I.orderEmbOfFin hI).toEmbedding
  obtain ⟨I₀, -, hI₀⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (by simpa using hdn)
  set A := U.submatrix (I₀.orderEmbOfFin hI₀) id
  obtain ⟨P, hP0, hP⟩ := hD n d J A hJ hd (hfin I₀ hI₀)
  set G := zeroSetEuc J ∩ {z | eval (A *ᵥ WithLp.ofLp z) P ≠ 0}
  have hPJ : ComplexSets.pullback A P ∉ J := fun hmem => hP0 <| (hfin I₀ hI₀).injective <| by
    rw [map_zero, ComplexSets.projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  have hbad : μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P})) = 0 :=
    hN n d _ (MassFinite.dim_sup_lt J hJ hd _ hPJ)
  have hsub : zeroSetEuc J ∩ Metric.ball 0 R ⊆
      zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P}) ∪ G ∩ Metric.ball 0 R := by
    rintro z ⟨hz, hzR⟩
    by_cases hzP : eval (A *ᵥ WithLp.ofLp z) P = 0
    · left
      intro q hq
      obtain ⟨j, hj, c, hc, rfl⟩ := Submodule.mem_sup.mp hq
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      have hzj : eval (fun i => z i) j = 0 := hz j hj
      have hpb : eval (fun i => z i) (ComplexSets.pullback A P) = 0 := by
        rw [MassFinite.eval_pullback]
        exact hzP
      simp [hzj, hpb]
    · exact Or.inr ⟨⟨hz, hzP⟩, hzR⟩
  have hgood := hL n d b I₀ G hI₀ (MassFinite.good_localGraph J U b hb I₀ hI₀ P
    (fun y hy x hx => ((hP y hy).2.2 x hx))) R
  calc μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball 0 R)
      ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P}) ∪
          G ∩ Metric.ball 0 R) := measure_mono hsub
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc (J ⊔ Ideal.span {ComplexSets.pullback A P})) +
          μH[((2 * d : ℕ) : ℝ)] (G ∩ Metric.ball 0 R) := measure_union_le _ _
    _ < ⊤ := by
      rw [hbad, zero_add]
      refine lt_of_le_of_lt hgood (ENNReal.sum_lt_top.mpr fun I hI => ENNReal.mul_lt_top ?_ ?_)
      · have hIc := (Finset.mem_powersetCard.mp hI).2
        refine lt_of_le_of_lt (iSup_le fun x => MassFinite.count_le J U b hb I hIc G
          (fun z hz => hz.1) (ComplexSets.projDegree J (U.submatrix (I.orderEmbOfFin hIc) id))
          (fun y => ?_) x) ENNReal.coe_lt_top
        have h := hF n d J _ hJ hd (hfin I hIc) y
        exact ⟨h.2.1, h.2.2⟩
      · have h := MassFinite.ball_lt_top (ι := I) R
        rwa [Fintype.card_coe, (Finset.mem_powersetCard.mp hI).2] at h

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSerreCriterion
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem isRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_le_one (B : Type*) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B] (h : ringKrullDim B ≤ 1) : IsRegularLocalRing B := by
  by_cases hf : IsField B
  · let := hf.toField
    infer_instance
  · have : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.mpr (by exact_mod_cast h)
    have hm : maximalIdeal B ≠ ⊥ := fun hm => hf (isField_iff_maximalIdeal_eq.mpr hm)
    have h3 : IsIntegrallyClosed B ∧ ∃! P : Ideal B, P ≠ ⊥ ∧ P.IsPrime :=
      ⟨inferInstance, maximalIdeal B, ⟨hm, inferInstance⟩, fun P ⟨hP, hPp⟩ =>
        IsLocalRing.eq_maximalIdeal (hPp.isMaximal_of_ne_bot hP)⟩
    have hdvr : IsDiscreteValuationRing B := ((IsDiscreteValuationRing.TFAE B hf).out 0 3).mpr h3
    infer_instance

theorem SerreCriterion.proof (hS : NormalLocalDepthTwo.Statement) (hN : SerreNormalOfRegularDepth.Statement) :
    SerreCriterion.Statement := by
  intro A _ hA
  refine ⟨fun h => ⟨fun P _ hdim => ?_, fun P _ => ?_⟩, fun h => hN A hA h.1 h.2⟩
  · obtain ⟨hd, hi⟩ := h P
    exact isRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_le_one _ (by exact_mod_cast hdim)
  · obtain ⟨hd, hi⟩ := h P
    exact hS _

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermsNoetherian
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def HolGermsNoetherian.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ), IsNoetherianRing (holGerms w)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

