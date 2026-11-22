import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalGraphMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalGraphProjectionMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Function

open scoped ENNReal

noncomputable section

namespace LocalGraphProjectionMass

variable {n : ℕ}

theorem frameFibreCount_image_repr_map (b c : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (A : Set (EuclideanSpace ℂ (Fin n))) (x : I → ℂ) :
    frameFibreCount (c.map b.repr) I (b.repr '' A) x = frameFibreCount c I A x := by
  have hP : ∀ z, frameProj (c.map b.repr) I (b.repr z) = frameProj c I z := by
    intro z
    funext i
    simp only [frameProj, OrthonormalBasis.map_apply, LinearIsometryEquiv.inner_map_map]
  have h : {y ∈ b.repr '' A | frameProj (c.map b.repr) I y = x} =
      b.repr '' {z ∈ A | frameProj c I z = x} := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      exact ⟨z, ⟨hz, by rwa [hP] at hy⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, by rw [hP]; exact hzx⟩
  simp only [frameFibreCount]
  rw [h, b.repr.injective.injOn.encard_image]

theorem mass_piece_frame (hPF : ProjectionFormula.Statement)
    (b c : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n)) {d : ℕ}
    (hd : I₀.card = d) (Ω : Set (I₀ → ℂ)) (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n))
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (hfix : ∀ w ∈ Ω, frameProj b I₀ (g w) = w)
    (M : Set (EuclideanSpace ℂ (Fin n))) (hM : MeasurableSet M) :
    μH[((2 * d : ℕ) : ℝ)] (g '' Ω ∩ M) =
      ∑ I ∈ Finset.univ.powersetCard d, ∫⁻ x : EuclideanSpace ℂ I,
        frameFibreCount c I (g '' Ω ∩ M) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) := by
  obtain ⟨m, e, Ω', F, hΩ', hF, himg⟩ := LocalGraphMass.image_repr_eq_graph b I₀ hd Ω g hΩ hg hfix
  have hT : b.repr '' (g '' Ω ∩ M) = graphPt e F '' Ω' ∩ b.repr '' M := by
    rw [Set.image_inter b.repr.injective, himg]
  have hM' : MeasurableSet (b.repr '' M) :=
    b.repr.toHomeomorph.measurableEmbedding.measurableSet_image.2 hM
  have h := hPF d m n e Ω' F hΩ' hF (c.map b.repr) _ hM'
  rw [← hT, b.repr.isometry.hausdorffMeasure_image (Or.inr b.repr.surjective)] at h
  rw [h]
  simp_rw [frameFibreCount_image_repr_map]

theorem lintegral_count_le (U : Matrix (Fin n) (Fin n) ℂ)
    (c : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (hc : ∀ i (z : EuclideanSpace ℂ (Fin n)), inner ℂ (c i) z = ∑ j, U i j * z j)
    {d : ℕ} (I : Finset (Fin n)) (hI : I.card = d) (A : Set (EuclideanSpace ℂ (Fin n))) :
    ∫⁻ x : EuclideanSpace ℂ I, frameFibreCount c I A (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) ≤
      (⨆ y : EuclideanSpace ℂ (Fin d),
          (({z | z ∈ A ∧ rowsProj U (I.orderEmbOfFin hI) z = y}.encard : ℕ∞) : ℝ≥0∞)) *
        μH[((2 * d : ℕ) : ℝ)] (rowsProj U (I.orderEmbOfFin hI) '' A) := by
  set e := I.orderIsoOfFin hI
  set s : Fin d → Fin n := ⇑(I.orderEmbOfFin hI) with hs
  let φ : EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.toEquiv.symm
  have hφ : ∀ x k, φ x k = x (e k) := fun x k => rfl
  have hrow : ∀ z k, rowsProj U s z k = inner ℂ (c (e k)) z := by
    intro z k
    rw [hc]
    simp [rowsProj, Matrix.mulVec, dotProduct, s, e, Finset.coe_orderIsoOfFin_apply]
  have hiff : ∀ x z, frameProj c I z = WithLp.ofLp x ↔ rowsProj U s z = φ x := by
    intro x z
    constructor
    · intro h
      ext k
      rw [hrow, hφ]
      exact congrFun h (e k)
    · intro h
      funext i
      have := congrArg (fun y : EuclideanSpace ℂ (Fin d) => y (e.symm i)) h
      simp only [hrow, hφ, OrderIso.apply_symm_apply] at this
      exact this
  set T := rowsProj U s '' A
  set N := ⨆ y : EuclideanSpace ℂ (Fin d), (({z | z ∈ A ∧ rowsProj U s z = y}.encard : ℕ∞) : ℝ≥0∞)
  have hle : ∀ x : EuclideanSpace ℂ I, frameFibreCount c I A (WithLp.ofLp x) ≤
      (φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T).indicator (fun _ => N) x := by
    intro x
    have hset : {z ∈ A | frameProj c I z = WithLp.ofLp x} = {z | z ∈ A ∧ rowsProj U s z = φ x} := by
      ext z
      exact and_congr Iff.rfl (hiff x z)
    by_cases hx : φ x ∈ T
    · rw [Set.indicator_of_mem (show x ∈ φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T from
        subset_toMeasurable _ T hx)]
      simp only [frameFibreCount]
      rw [hset]
      exact le_iSup (fun y => (({z | z ∈ A ∧ rowsProj U s z = y}.encard : ℕ∞) : ℝ≥0∞)) (φ x)
    · have h0 : {z ∈ A | frameProj c I z = WithLp.ofLp x} = ∅ := by
        rw [hset]
        exact Set.eq_empty_of_forall_notMem fun z hz => hx ⟨z, hz.1, hz.2⟩
      simp only [frameFibreCount]
      rw [h0]
      simp
  calc _ ≤ ∫⁻ x : EuclideanSpace ℂ I, (φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T).indicator (fun _ => N) x ∂(μH[((2 * d : ℕ) : ℝ)]) :=
        lintegral_mono hle
    _ = N * μH[((2 * d : ℕ) : ℝ)] (φ ⁻¹' toMeasurable (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) T) :=
        lintegral_indicator_const ((measurableSet_toMeasurable _ _).preimage φ.continuous.measurable) _
    _ = N * μH[((2 * d : ℕ) : ℝ)] T := by
        rw [φ.isometry.hausdorffMeasure_preimage (Or.inr φ.surjective), φ.surjective.range_eq,
          Set.inter_univ, measure_toMeasurable]

end LocalGraphProjectionMass

open LocalGraphProjectionMass in

theorem LocalGraphProjectionMass.proof (hPF : ProjectionFormula.Statement) :
    LocalGraphProjectionMass.Statement := by
  intro n d b I₀ S hd hS U hU B hB
  classical
  obtain ⟨c, hc⟩ := MassFinite.exists_frame U hU
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hS' : ∀ z : S, ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
      (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ (z : EuclideanSpace ℂ (Fin n)) ∈ V ∧
        DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧ S ∩ V = g '' Ω :=
    fun z => hS z z.2
  choose Ω V g hΩ hV hzV hg hfix hSV using hS'
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V hV
  have hmemT : ∀ z ∈ S, ∃ i ∈ T, z ∈ V i := by
    intro z hz
    have : z ∈ ⋃ i ∈ T, V i := hTU ▸ Set.mem_iUnion.2 ⟨⟨z, hz⟩, hzV _⟩
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 this
    exact ⟨i, hi, hzi⟩
  have hTne : T.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨i, hi, -⟩ := hmemT z hz
    exact ⟨i, hi⟩
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  let W : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun k => V (f k)
  have hcover : S ⊆ ⋃ k, disjointed W k := by
    intro z hz
    rw [iUnion_disjointed]
    obtain ⟨i, hi, hzi⟩ := hmemT z hz
    rw [hf] at hi
    obtain ⟨k, rfl⟩ := hi
    exact Set.mem_iUnion.2 ⟨k, hzi⟩
  have hDmeas : ∀ k, MeasurableSet (disjointed W k) :=
    MeasurableSet.disjointed fun k => (hV _).measurableSet
  have hpiece : ∀ k, S ∩ B ∩ disjointed W k = g (f k) '' Ω (f k) ∩ (B ∩ disjointed W k) := by
    intro k
    rw [← hSV (f k)]
    ext z
    constructor
    · rintro ⟨⟨hzS, hzB⟩, hzD⟩
      exact ⟨⟨hzS, disjointed_subset W k hzD⟩, hzB, hzD⟩
    · rintro ⟨⟨hzS, -⟩, hzB, hzD⟩
      exact ⟨⟨hzS, hzB⟩, hzD⟩
  have hdisj : Pairwise (Disjoint on fun k => S ∩ B ∩ disjointed W k) :=
    fun i j hij => (disjoint_disjointed W hij).mono Set.inter_subset_right Set.inter_subset_right
  let G : (Fin d → Fin n) → ℝ≥0∞ := fun s =>
    (⨆ x : EuclideanSpace ℂ (Fin d),
        (({z | z ∈ S ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) *
      μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (S ∩ B))
  calc μH[((2 * d : ℕ) : ℝ)] (S ∩ B)
      ≤ μH[((2 * d : ℕ) : ℝ)] (⋃ k, S ∩ B ∩ disjointed W k) := by
        refine measure_mono fun z hz => ?_
        obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hcover hz.1)
        exact Set.mem_iUnion.2 ⟨k, hz, hk⟩
    _ ≤ ∑' k, μH[((2 * d : ℕ) : ℝ)] (S ∩ B ∩ disjointed W k) := measure_iUnion_le _
    _ = ∑' k, ∑ I ∈ Finset.univ.powersetCard d, ∫⁻ x : EuclideanSpace ℂ I,
          frameFibreCount c I (S ∩ B ∩ disjointed W k) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) := by
        congr 1
        funext k
        rw [hpiece k]
        exact mass_piece_frame hPF b c I₀ hd _ _ (hΩ _) (hg _) (hfix _) _ (hB.inter (hDmeas k))
    _ = ∑ I ∈ Finset.univ.powersetCard d, ∑' k, ∫⁻ x : EuclideanSpace ℂ I,
          frameFibreCount c I (S ∩ B ∩ disjointed W k) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ I ∈ Finset.univ.powersetCard d, ⨆ hI : I.card = d, G (I.orderEmbOfFin hI) := by
        refine Finset.sum_le_sum fun I hI => ?_
        have hIc := (Finset.mem_powersetCard.1 hI).2
        refine le_trans ?_ (le_iSup (fun h : I.card = d => G (I.orderEmbOfFin h)) hIc)
        calc _ ≤ ∫⁻ x : EuclideanSpace ℂ I, ∑' k,
              frameFibreCount c I (S ∩ B ∩ disjointed W k) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) :=
              LocalGraphMass.tsum_lintegral_le _ _
          _ ≤ ∫⁻ x : EuclideanSpace ℂ I, frameFibreCount c I (S ∩ B) (WithLp.ofLp x)
                ∂(μH[((2 * d : ℕ) : ℝ)]) :=
              lintegral_mono fun x =>
                LocalGraphMass.tsum_frameFibreCount_le c I _ (fun k => Set.inter_subset_left) hdisj _
          _ ≤ G (I.orderEmbOfFin hIc) := lintegral_count_le U c hc I hIc (S ∩ B)
    _ = ∑ s ∈ Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s), G s := by
        refine Finset.sum_bij (fun I hI => ⇑(I.orderEmbOfFin (Finset.mem_powersetCard.1 hI).2))
          (fun I hI => Finset.mem_filter.2 ⟨Finset.mem_univ _, (I.orderEmbOfFin _).strictMono⟩)
          (fun I₁ hI₁ I₂ hI₂ h => ?_) (fun t ht => ?_) (fun I hI => ?_)
        · have := congrArg Set.range h
          rw [Finset.range_orderEmbOfFin, Finset.range_orderEmbOfFin] at this
          exact Finset.coe_inj.1 this
        · have hmono := (Finset.mem_filter.1 ht).2
          have hcard : (Finset.univ.image t).card = d := by
            rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
          refine ⟨Finset.univ.image t, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hcard⟩, ?_⟩
          exact (Finset.orderEmbOfFin_unique hcard
            (fun x => Finset.mem_image_of_mem t (Finset.mem_univ x)) hmono).symm
        · exact iSup_pos (Finset.mem_powersetCard.1 hI).2

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaximalCountUnbranched
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

namespace MaximalCountUnbranched

theorem analyticOnNhd_of_differentiableOn_pi {d : ℕ} {σ : Type} [Fintype σ] {U : Set (Fin d → ℂ)}
    {G : (Fin d → ℂ) → σ → ℂ} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) : AnalyticOnNhd ℂ G U := by
  intro y hy
  refine AnalyticAt.pi fun s => ?_
  have hs : DifferentiableOn ℂ (fun x => G x s) U := differentiableOn_pi.1 hG s
  refine analyticOnNhd_of_continuousOn_of_separately hU hs.continuousOn (fun z hz i => ?_) y hy
  have h1 : DifferentiableAt ℂ (fun x => G x s) (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hs.differentiableAt (hU.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update (𝕜 := ℂ) z (z i)).differentiableAt

theorem fibre_unique_near {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {N : ℕ} (hmaps : Set.MapsTo A Y D)
    (hopen : ∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x))
    (hle : ∀ y ∈ D, {x | x ∈ Y ∧ A x = y}.encard ≤ N)
    {z : σ → ℂ} (hz : z ∈ Y) (hzN : {x' | x' ∈ Y ∧ A x' = A z}.encard = N) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ W ∈ 𝓝 (A z), ∀ y ∈ W,
      {x' | x' ∈ Y ∧ A x' = y}.encard = N ∧ (∃ x' ∈ Y, A x' = y ∧ dist x' z < ε) ∧
      ∀ x₁ ∈ Y, ∀ x₂ ∈ Y, A x₁ = y → A x₂ = y → dist x₁ z < ε → dist x₂ z < ε → x₁ = x₂ := by
  have hSfin : {x' | x' ∈ Y ∧ A x' = A z}.Finite := Set.finite_of_encard_eq_coe hzN
  have hzS : z ∈ {x' | x' ∈ Y ∧ A x' = A z} := ⟨hz, rfl⟩
  have hsep : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ {x' | x' ∈ Y ∧ A x' = A z} ×ˢ {x' | x' ∈ Y ∧ A x' = A z},
      p.1 ≠ p.2 → 2 * ε < dist p.1 p.2 := by
    refine (eventually_all_finite (hSfin.prod hSfin)).2 fun p _ => ?_
    by_cases hp : p.1 = p.2
    · exact Eventually.of_forall fun _ h => absurd hp h
    · have hpos : 0 < dist p.1 p.2 / 2 := half_pos (dist_pos.2 hp)
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hpos)] with ε hε _
      linarith
  filter_upwards [hsep, self_mem_nhdsWithin] with ε hε hε0
  have hε0 : (0 : ℝ) < ε := hε0
  refine ⟨⋂ s ∈ {x' | x' ∈ Y ∧ A x' = A z}, A '' (Y ∩ ball s ε), (biInter_mem hSfin).2 fun s hs => ?_,
    fun y hy => ?_⟩
  · have := hopen s hs.1 (ball s ε) (ball_mem_nhds s hε0)
    rwa [hs.2] at this
  have hch : ∀ s ∈ {x' | x' ∈ Y ∧ A x' = A z}, ∃ p, p ∈ Y ∧ dist p s < ε ∧ A p = y := by
    intro s hs
    obtain ⟨p, ⟨hpY, hpb⟩, hpA⟩ := Set.mem_iInter₂.1 hy s hs
    exact ⟨p, hpY, mem_ball.1 hpb, hpA⟩
  choose! f hfY hfd hfA using hch
  have hinj : Set.InjOn f {x' | x' ∈ Y ∧ A x' = A z} := by
    intro s hs s' hs' he
    by_contra hne
    have h1 : 2 * ε < dist s s' := hε (s, s') ⟨hs, hs'⟩ hne
    have h2 : dist s s' ≤ dist (f s) s + dist (f s') s' := by
      calc dist s s' ≤ dist s (f s) + dist (f s) s' := dist_triangle _ _ _
        _ = dist (f s) s + dist (f s') s' := by rw [dist_comm s, he]
    linarith [hfd s hs, hfd s' hs']
  have hyD : y ∈ D := hfA z hzS ▸ hmaps (hfY z hzS)
  have hsub : f '' {x' | x' ∈ Y ∧ A x' = A z} ⊆ {x' | x' ∈ Y ∧ A x' = y} := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨hfY s hs, hfA s hs⟩
  have himg : (f '' {x' | x' ∈ Y ∧ A x' = A z}).encard = N := by rw [hinj.encard_image, hzN]
  have hFle := hle y hyD
  have hFeq : {x' | x' ∈ Y ∧ A x' = y}.encard = N :=
    le_antisymm hFle (himg ▸ Set.encard_le_encard hsub)
  have huniq : ∀ x₁ ∈ Y, A x₁ = y → dist x₁ z < ε → x₁ = f z := by
    intro x₁ hx₁ hA₁ hd₁
    by_contra hne
    have hnot : x₁ ∉ f '' {x' | x' ∈ Y ∧ A x' = A z} := by
      rintro ⟨s, hs, rfl⟩
      by_cases hsz : s = z
      · exact hne (hsz ▸ rfl)
      · have h1 : 2 * ε < dist s z := hε (s, z) ⟨hs, hzS⟩ hsz
        have h2 : dist s z ≤ dist (f s) s + dist (f s) z := by
          calc dist s z ≤ dist s (f s) + dist (f s) z := dist_triangle _ _ _
            _ = dist (f s) s + dist (f s) z := by rw [dist_comm s]
        linarith [hfd s hs]
    have hins : insert x₁ (f '' {x' | x' ∈ Y ∧ A x' = A z}) ⊆ {x' | x' ∈ Y ∧ A x' = y} :=
      Set.insert_subset ⟨hx₁, hA₁⟩ hsub
    have hc := Set.encard_le_encard hins
    rw [Set.encard_insert_of_notMem hnot, himg] at hc
    have hc' : ((N + 1 : ℕ) : ℕ∞) ≤ (N : ℕ∞) := by exact_mod_cast hc.trans hFle
    have : N + 1 ≤ N := by exact_mod_cast hc'
    omega
  refine ⟨hFeq, ⟨f z, hfY z hzS, hfA z hzS, hfd z hzS⟩, fun x₁ hx₁ x₂ hx₂ hA₁ hA₂ hd₁ hd₂ => ?_⟩
  rw [huniq x₁ hx₁ hA₁ hd₁, huniq x₂ hx₂ hA₂ hd₂]

theorem proof (hRE : RiemannExtensionAnalytic.Statement) : MaximalCountUnbranched.Statement := by
  intro σ _ Y d A D N _hD hmaps _hprop hopen hgen x hx hxN
  have key := fun (z : σ → ℂ) (hz : z ∈ Y) (hzN : {x' | x' ∈ Y ∧ A x' = A z}.encard = N) =>
    fibre_unique_near hmaps hopen hgen.1 hz hzN
  obtain ⟨ε, ⟨W₀, hW₀, hW₀p⟩, hε0⟩ := ((key x hx hxN).and self_mem_nhdsWithin).exists
  have hε0 : (0 : ℝ) < ε := hε0
  obtain ⟨U, g, hUo, hxU, _hUD, hg, hgnz, hgsec⟩ := hgen.2 (A x) (hmaps hx)
  have hOo : IsOpen (interior W₀ ∩ U) := isOpen_interior.inter hUo
  have hOW : ∀ y ∈ interior W₀ ∩ U, y ∈ W₀ := fun y hy => interior_subset hy.1
  have hex : ∀ y ∈ interior W₀ ∩ U, ∃ x' ∈ Y, A x' = y ∧ dist x' x < ε :=
    fun y hy => (hW₀p y (hOW y hy)).2.1
  choose! h hhY hhA hhd using hex
  have hu : ∀ y ∈ interior W₀ ∩ U, ∀ x' ∈ Y, A x' = y → dist x' x < ε → x' = h y :=
    fun y hy x' hx' hA hd =>
      (hW₀p y (hOW y hy)).2.2 x' hx' (h y) (hhY y hy) hA (hhA y hy) hd (hhd y hy)

  have hcont : ContinuousOn h (interior W₀ ∩ U) := by
    intro y₀ hy₀
    refine ContinuousAt.continuousWithinAt ?_
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro η hη
    have hzN : {x' | x' ∈ Y ∧ A x' = A (h y₀)}.encard = N := by
      rw [hhA y₀ hy₀]; exact (hW₀p y₀ (hOW y₀ hy₀)).1
    have hgap : 0 < ε - dist (h y₀) x := by linarith [hhd y₀ hy₀]
    have hsmall : ∀ᶠ e in 𝓝[>] (0 : ℝ), e < min η (ε - dist (h y₀) x) :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (lt_min hη hgap))
    obtain ⟨e, ⟨W₁, hW₁, hW₁p⟩, he⟩ := ((key (h y₀) (hhY y₀ hy₀) hzN).and hsmall).exists
    rw [hhA y₀ hy₀] at hW₁
    filter_upwards [hW₁, hOo.mem_nhds hy₀] with y hy1 hyO
    obtain ⟨x'', hx''Y, hx''A, hx''d⟩ := (hW₁p y hy1).2.1
    have hm1 := min_le_left η (ε - dist (h y₀) x)
    have hm2 := min_le_right η (ε - dist (h y₀) x)
    have hx''x : dist x'' x < ε := by
      have := dist_triangle x'' (h y₀) x
      linarith
    rw [← hu y hyO x'' hx''Y hx''A hx''x]
    linarith

  have hdiff : ∀ y₀ ∈ interior W₀ ∩ U, g y₀ ≠ 0 → DifferentiableAt ℂ h y₀ := by
    intro y₀ hy₀ hg₀
    obtain ⟨_, hsec⟩ := hgsec y₀ hy₀.2 hg₀
    obtain ⟨O₁, V₁, h₁, hO₁, _hV₁, hzV₁, han₁, hA₁, hYV₁⟩ := hsec (h y₀) (hhY y₀ hy₀) (hhA y₀ hy₀)
    have hz : h y₀ ∈ h₁ '' O₁ := hYV₁ ▸ ⟨hhY y₀ hy₀, hzV₁⟩
    obtain ⟨y₁, hy₁, hy₁e⟩ := hz
    have hy₁₀ : y₁ = y₀ := by rw [← hA₁ y₁ hy₁, hy₁e, hhA y₀ hy₀]
    rw [hy₁₀] at hy₁ hy₁e
    have hc₁ : ContinuousAt h₁ y₀ := (han₁ y₀ hy₁).continuousAt
    have hball : ball x ε ∈ 𝓝 (h₁ y₀) := by
      rw [hy₁e]; exact isOpen_ball.mem_nhds (mem_ball.2 (hhd y₀ hy₀))
    have heq : h₁ =ᶠ[𝓝 y₀] h := by
      filter_upwards [hc₁.preimage_mem_nhds hball, hO₁.mem_nhds hy₁, hOo.mem_nhds hy₀]
        with y hyb hyO₁ hyO
      have hyY : h₁ y ∈ Y := by
        have hmem : h₁ y ∈ h₁ '' O₁ := ⟨y, hyO₁, rfl⟩
        rw [← hYV₁] at hmem
        exact hmem.1
      exact hu y hyO (h₁ y) hyY (hA₁ y hyO₁) (mem_ball.1 hyb)
    exact (han₁ y₀ hy₁).differentiableAt.congr_of_eventuallyEq heq.symm

  have hgd : DifferentiableOn ℂ g (interior W₀ ∩ U) := hg.differentiableOn.mono fun y hy => hy.2
  have hgnz' : ∀ V : Set (Fin d → ℂ), IsOpen V → V ⊆ interior W₀ ∩ U → V.Nonempty → ∃ t ∈ V, g t ≠ 0 :=
    fun V hV hVO hVn => hgnz V hV (hVO.trans Set.inter_subset_right) hVn
  have hdense : interior W₀ ∩ U ⊆ closure ((interior W₀ ∩ U) ∩ {t | g t ≠ 0}) := by
    intro y hy
    rw [_root_.mem_closure_iff]
    intro o ho hyo
    obtain ⟨t, ht, hgt⟩ := hgnz' (o ∩ (interior W₀ ∩ U)) (ho.inter hOo) Set.inter_subset_right ⟨y, hyo, hy⟩
    exact ⟨t, ht.1, ht.2, hgt⟩
  have hcoord : ∀ j : σ, DifferentiableOn ℂ (fun y => h y j) (interior W₀ ∩ U) := by
    intro j
    have hdj : DifferentiableOn ℂ (fun y => h y j) ((interior W₀ ∩ U) ∩ {t | g t ≠ 0}) :=
      fun y hy => (differentiableAt_pi.1 (hdiff y hy.1 hy.2) j).differentiableWithinAt
    have hbj : ∀ τ ∈ interior W₀ ∩ U, ∃ M ∈ 𝓝 τ,
        Bornology.IsBounded ((fun y => h y j) '' (M ∩ (interior W₀ ∩ U) ∩ {t | g t ≠ 0})) := by
      intro τ _
      refine ⟨Set.univ, univ_mem, ?_⟩
      rw [isBounded_iff_forall_norm_le]
      refine ⟨‖x‖ + ε, ?_⟩
      rintro _ ⟨y, ⟨⟨_, hyO⟩, _⟩, rfl⟩
      calc ‖h y j‖ ≤ ‖h y‖ := norm_le_pi_norm (h y) j
        _ ≤ ‖x‖ + ε := norm_le_of_mem_closedBall (mem_closedBall.2 (hhd y hyO).le)
    obtain ⟨F, hF, hFe⟩ := hRE d (interior W₀ ∩ U) g (fun y => h y j) hOo hgd hgnz' hdj hbj
    have hEq : Set.EqOn F (fun y => h y j) (interior W₀ ∩ U) :=
      hFe.of_subset_closure hF.continuousOn (continuousOn_pi.1 hcont j) Set.inter_subset_left hdense
    exact hF.congr fun y hy => (hEq hy).symm
  have han : AnalyticOnNhd ℂ h (interior W₀ ∩ U) :=
    analyticOnNhd_of_differentiableOn_pi hOo (differentiableOn_pi.2 hcoord)
  refine ⟨interior W₀ ∩ U, ball x ε ∩ A ⁻¹' (interior W₀ ∩ U), h, hOo,
    isOpen_ball.inter (hOo.preimage A.continuous),
    ⟨mem_ball_self hε0, mem_interior_iff_mem_nhds.2 hW₀, hxU⟩, han, hhA, ?_⟩
  ext x'
  constructor
  · rintro ⟨hx'Y, hx'b, hx'O⟩
    exact ⟨A x', hx'O, (hu (A x') hx'O x' hx'Y rfl (mem_ball.1 hx'b)).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hhY y hy, mem_ball.2 (hhd y hy), show A (h y) ∈ interior W₀ ∩ U from (hhA y hy).symm ▸ hy⟩

end MaximalCountUnbranched

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNonIsolatedFibreCurve
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

theorem NonIsolatedFibreCurve.analyticOnNhd_of_differentiableOn {k : ℕ} {O : Set (Fin k → ℂ)}
    {g : (Fin k → ℂ) → ℂ} (hO : IsOpen O) (hg : DifferentiableOn ℂ g O) : AnalyticOnNhd ℂ g O := by
  refine analyticOnNhd_of_continuousOn_of_separately hO hg.continuousOn fun z hz i => ?_
  have h1 : DifferentiableAt ℂ g (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hg.differentiableAt (hO.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update z (z i)).differentiableAt

theorem NonIsolatedFibreCurve.proof (hComp : AnalyticGermComponents.Statement)
    (hCurve : IrreducibleGermCurve.Statement) : NonIsolatedFibreCurve.Statement := by
  intro k m U f p hU hf hp hacc
  set Z : Set (Fin k → ℂ) := {v | v ∈ U ∧ f v = f p} with hZ
  have hZan : IsAnalyticNear Z p := by
    refine ⟨U, m, fun i v => f v i - f p i, hU, hp, fun i => ?_, ?_⟩
    · exact analyticOnNhd_of_differentiableOn hU ((differentiableOn_pi.1 hf i).sub_const _)
    · ext v
      simp only [hZ, Set.mem_inter_iff, Set.mem_ofPred_eq, sub_eq_zero, funext_iff]
      tauto
  obtain ⟨n, Y, hY, W, hW, hZW⟩ := hComp (Fin k) Z p hZan ⟨hp, rfl⟩

  have hfreq : ∃ᶠ y in 𝓝 p, y ≠ p ∧ y ∈ ⋃ i, Y i := by
    have h := accPt_iff_frequently.1 hacc
    refine (h.and_eventually hW).mono fun y ⟨⟨hne, hyZ⟩, hyW⟩ => ⟨hne, ?_⟩
    have : y ∈ Z ∩ W := ⟨hyZ, hyW⟩
    rw [hZW] at this
    exact this.1
  obtain ⟨i, hi⟩ : ∃ i, AccPt p (𝓟 (Y i)) := by
    by_contra hno
    push Not at hno
    have hev : ∀ᶠ y in 𝓝 p, ∀ i, ¬ (y ≠ p ∧ y ∈ Y i) := by
      refine eventually_all.2 fun i => ?_
      have := hno i
      rw [accPt_iff_frequently, Filter.not_frequently] at this
      exact this
    obtain ⟨y, ⟨hne, hyU⟩, hy⟩ := (hfreq.and_eventually hev).exists
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hyU
    exact hy j ⟨hne, hj⟩
  obtain ⟨r, hr, γ, hγd, hγi, hγ0, hγm⟩ := hCurve (Fin k) (Y i) p (hY i).1 (hY i).2 hi

  have hcont : ContinuousAt γ 0 := (hγd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).continuousAt
  have hpre : γ ⁻¹' W ∈ 𝓝 (0 : ℂ) := hcont.preimage_mem_nhds (by rwa [hγ0])
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hpre
  have hsub : ball (0 : ℂ) (min r ε) ⊆ ball 0 r := ball_subset_ball (min_le_left _ _)
  refine ⟨min r ε, lt_min hr hε, γ, hγd.mono hsub, hγi.mono hsub, hγ0, fun τ hτ => ?_⟩
  have hτW : γ τ ∈ W := hεW (ball_subset_ball (min_le_right _ _) hτ)
  have : γ τ ∈ (⋃ j, Y j) ∩ W := ⟨Set.mem_iUnion.2 ⟨i, hγm (hsub hτ)⟩, hτW⟩
  rw [← hZW] at this
  exact this.1

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompact
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def ChartMassCompact.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    ContinuousOn f (zeroSet J) → (∀ i, SmoothNear (zeroSet J) (ψ i)) →
    (HasCompactSupport f ∨ ∃ i, HasCompactSupport (ψ i)) →
      Integrable (chartAbsDens J A f ψ)

end

end GroundTheory.Heights₂.Heights
end

