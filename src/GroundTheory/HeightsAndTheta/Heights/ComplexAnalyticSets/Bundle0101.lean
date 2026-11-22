import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0096
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0085
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0093
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntPoly
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0097
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0069
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimeGermPrimitivePresentation

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveCoordinateGraph
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

theorem isCoordinateGraphNear_of_chart {n : ℕ} {X : Set (Fin n → ℂ)} {x : Fin n → ℂ}
    (A : (Fin n → ℂ) →L[ℂ] ℂ) (O : Set ℂ) (V : Set (Fin n → ℂ)) (g : ℂ → Fin n → ℂ)
    (hO : IsOpen O) (hV : IsOpen V) (hxV : x ∈ V) (hxX : x ∈ X) (hg : AnalyticOnNhd ℂ g O)
    (hAg : ∀ y ∈ O, A (g y) = y) (hXV : X ∩ V = g '' O) : IsCoordinateGraphNear X x := by
  obtain ⟨y₀, hy₀O, hgy₀⟩ : x ∈ g '' O := hXV ▸ ⟨hxX, hxV⟩

  have hAd : ∀ y ∈ O, A (deriv g y) = 1 := by
    intro y hy
    have h1 : HasDerivAt (fun t ↦ A (g t)) (A (deriv g y)) y :=
      A.hasFDerivAt.comp_hasDerivAt y (hg y hy).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun t ↦ A (g t)) 1 y :=
      (hasDerivAt_id' y).congr_of_eventuallyEq (eventually_of_mem (hO.mem_nhds hy) hAg)
    exact h1.unique h2

  obtain ⟨i, hi⟩ : ∃ i, deriv g y₀ i ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : deriv g y₀ = 0 := funext h
    simpa [h0] using hAd y₀ hy₀O
  set φ : ℂ → ℂ := fun y ↦ g y i with hφdef
  have hφ : AnalyticOnNhd ℂ φ O := fun y hy ↦
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).analyticAt (g y)).comp (hg y hy)
  have hφd : ∀ y ∈ O, HasDerivAt φ (deriv g y i) y := fun y hy ↦
    hasDerivAt_pi.1 (hg y hy).differentiableAt.hasDerivAt i

  set U : Set ℂ := O ∩ deriv φ ⁻¹' {0}ᶜ with hUdef
  have hU : IsOpen U := hφ.deriv.continuousOn.isOpen_inter_preimage hO isOpen_compl_singleton
  have hy₀U : y₀ ∈ U := ⟨hy₀O, by simpa [(hφd y₀ hy₀O).deriv] using hi⟩
  have hs : HasStrictDerivAt φ (deriv g y₀ i) y₀ := by
    simpa [(hφd y₀ hy₀O).deriv] using (hφ y₀ hy₀O).hasStrictDerivAt
  set e := ((hs.hasStrictFDerivAt_equiv hi).toOpenPartialHomeomorph φ).restrOpen U hU with hedef
  have he : ∀ y, e y = φ y := fun _ ↦ rfl
  have hsrc : ∀ {y}, y ∈ e.source → y ∈ U := fun hy ↦ hy.2
  have hy₀e : y₀ ∈ e.source := ⟨(hs.hasStrictFDerivAt_equiv hi).mem_toOpenPartialHomeomorph_source, hy₀U⟩
  refine ⟨hxX, V ∩ A ⁻¹' e.source ∩ (fun z ↦ z i) ⁻¹' e.target,
    (hV.inter (e.open_source.preimage A.continuous)).inter (e.open_target.preimage (continuous_apply i)),
    ⟨⟨hxV, ?_⟩, ?_⟩, i, e.target, fun t ↦ g (e.symm t), e.open_target, ?_, ?_, ?_⟩
  · show A x ∈ e.source
    rw [← hgy₀, hAg y₀ hy₀O]
    exact hy₀e
  · show x i ∈ e.target
    rw [← hgy₀, show g y₀ i = e y₀ from rfl]
    exact e.map_source hy₀e
  · intro t ht
    have hyt := hsrc (e.map_target ht)
    have hder : HasDerivAt e (deriv φ (e.symm t)) (e.symm t) :=
      (hφ _ hyt.1).differentiableAt.hasDerivAt
    exact ((hg _ hyt.1).differentiableAt.comp t
      (e.hasDerivAt_symm ht hyt.2 hder).differentiableAt).differentiableWithinAt
  · intro t ht
    have h := e.right_inv ht
    rw [he] at h
    exact h
  · rintro z ⟨⟨hzV, hzA⟩, hzi⟩
    constructor
    · intro hzX
      obtain ⟨y, hyO, rfl⟩ : z ∈ g '' O := hXV ▸ ⟨hzX, hzV⟩
      have hye : y ∈ e.source := by simpa [hAg y hyO] using hzA
      refine ⟨hzi, ?_⟩
      show g (e.symm (e y)) = g y
      rw [e.left_inv hye]
    · rintro ⟨ht, hgz⟩
      have hyO := (hsrc (e.map_target ht)).1
      have : z ∈ X ∩ V := hXV ▸ ⟨_, hyO, hgz⟩
      exact this.1

theorem CurveCoordinateGraph.proof (hR : CurveRegularOffCentre.Statement) : CurveCoordinateGraph.Statement := by
  intro n I q _ hdim
  obtain ⟨N, hN, hNx⟩ := hR n I q hdim
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hN
  refine ⟨ε, hε, fun x hxZ hxb hxq ↦ ?_⟩
  obtain ⟨A, O, V, g, hO, hV, hxV, hg, hAg, hZV⟩ := hNx x ⟨hxZ, hball hxb⟩ hxq
  exact isCoordinateGraphNear_of_chart A O V g hO hV hxV hxZ hg hAg hZV

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveRegularOffCentre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem CurveRegularOffCentre.proof (hG : CurveGermComponents.Statement) (hR : CurveRegularOffFinite.Statement)
    (hF : CurveProperClosedFinite.Statement) : CurveRegularOffCentre.Statement := by
  classical
  intro n I q hdim
  obtain ⟨N, hN, hcomp⟩ := hG n I q hdim
  have hZc : ∀ J : Ideal (MvPolynomial (Fin n) ℂ), IsClosed (zeroSet J) := fun J ↦ by
    have : zeroSet J = ⋂ p ∈ J, {x : Fin n → ℂ | eval x p = 0} := by ext x; simp [zeroSet]
    rw [this]
    exact isClosed_biInter fun p _ ↦ isClosed_eq (MvPolynomial.continuous_eval p) continuous_const
  have hM : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I
  set S := {W | W ∈ I.minimalPrimes ∧ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = 1}
  have hS : S.Finite := hM.subset fun W hW ↦ hW.1
  choose! F hFfin hFchart using fun W (hW : W ∈ S) ↦ hR n W hW.1.1.1 hW.2
  have hnle : ∀ W ∈ S, ∀ W' ∈ I.minimalPrimes \ {W}, ¬ W' ≤ W := fun W hW W' hW' hle ↦
    hW'.2 (le_antisymm hle (hW.1.2 hW'.1.1 hle))
  set Bad := (⋃ W ∈ S, F W) ∪ ⋃ W ∈ S, ⋃ W' ∈ I.minimalPrimes \ {W}, zeroSet W ∩ zeroSet W'
  have hBad : Bad.Finite := (hS.biUnion hFfin).union (hS.biUnion fun W hW ↦
    hM.sdiff.biUnion fun W' hW' ↦ hF n W W' hW.1.1.1 hW.2 (hnle W hW W' hW'))
  have hN'o : IsOpen (interior N \ (Bad \ {q})) := isOpen_interior.sdiff hBad.sdiff.isClosed
  refine ⟨_, hN'o.mem_nhds ⟨mem_interior_iff_mem_nhds.2 hN, fun h ↦ h.2 rfl⟩, ?_⟩
  rintro x ⟨hxI, hxN, hxB⟩ hxq
  have hxBad : x ∉ Bad := fun h ↦ hxB ⟨h, hxq⟩
  obtain ⟨W, hWm, hWd, -, hxW⟩ := hcomp x ⟨hxI, interior_subset hxN⟩
  have hWS : W ∈ S := ⟨hWm, hWd⟩
  obtain ⟨A, O, V, g, hO, hV, hxV, hg, hAg, hWV⟩ :=
    hFchart W hWS x hxW fun h ↦ hxBad (Or.inl (Set.mem_biUnion hWS h))
  set V' := V ∩ interior N ∩ ⋂ W' ∈ I.minimalPrimes \ {W}, (zeroSet W')ᶜ
  have hV' : IsOpen V' := (hV.inter isOpen_interior).inter
    (hM.sdiff.isOpen_biInter fun W' _ ↦ (hZc W').isOpen_compl)
  have hIV' : zeroSet I ∩ V' = zeroSet W ∩ V' := by
    ext z
    refine ⟨fun ⟨hzI, hzV⟩ ↦ ⟨?_, hzV⟩, fun ⟨hzW, hzV⟩ ↦ ⟨fun p hp ↦ hzW p (hWm.1.2 hp), hzV⟩⟩
    obtain ⟨W'', hW''m, -, -, hzW''⟩ := hcomp z ⟨hzI, interior_subset hzV.1.2⟩
    by_cases h : W'' = W
    · exact h ▸ hzW''
    · exact absurd hzW'' (Set.mem_iInter₂.1 hzV.2 W'' ⟨hW''m, h⟩)
  refine ⟨A, O ∩ g ⁻¹' V', V', g, hg.continuousOn.isOpen_inter_preimage hO hV', hV',
    ⟨⟨hxV, hxN⟩, Set.mem_iInter₂.2 fun W' hW' hxW' ↦ hxBad (Or.inr (Set.mem_biUnion hWS
      (Set.mem_biUnion hW' ⟨hxW, hxW'⟩)))⟩, hg.mono Set.inter_subset_left,
    fun y hy ↦ hAg y hy.1, ?_⟩
  rw [hIV', Set.image_inter_preimage, ← hWV]
  ext z
  exact ⟨fun ⟨hzW, hzV⟩ ↦ ⟨⟨hzW, hzV.1.1⟩, hzV⟩, fun ⟨⟨hzW, _⟩, hzV⟩ ↦ ⟨hzW, hzV⟩⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveResidueDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

theorem CurveResidueDegree.proof : CurveResidueDegree.Statement := by
  intro n I q _ hdim P
  have := P.isMaximal
  let _ : Field (curveNormalisation I q ⧸ P.asIdeal) := Ideal.Quotient.field _

  have hO : Nontrivial (curveLocalRing I q) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (by decide)

  have hIq : ∀ g ∈ I, eval q g = 0 := by
    intro g hg
    by_contra hgq
    have hu := isUnit_algebraMap_curveLocalRing I q g hgq
    have h0 : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) g = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hg)
    rw [h0] at hu
    exact not_isUnit_zero hu

  let evL : Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) →+* ℂ :=
    IsLocalization.lift (M := (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl) (g := eval q)
      (fun s ↦ isUnit_iff_ne_zero.2 fun h ↦ s.2 (RingHom.mem_ker.2 h))
  have hJ : ∀ a ∈ I.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))), evL a = 0 := by
    intro a ha
    have hle : I.map (algebraMap (MvPolynomial (Fin n) ℂ)
        (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))) ≤ RingHom.ker evL := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      simp [evL, IsLocalization.lift_eq, hIq g hg]
    exact hle ha
  let ε : curveLocalRing I q →+* ℂ := Ideal.Quotient.lift _ evL hJ
  let K := curveNormalisation I q ⧸ P.asIdeal
  let π : curveLocalRing I q →+* K := algebraMap (curveLocalRing I q) K
  let ι : ℂ →+* K := π.comp ((algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)).comp C)

  have : Algebra.IsIntegral (curveLocalRing I q) (curveNormalisation I q) :=
    inferInstanceAs (Algebra.IsIntegral (curveLocalRing I q)
      ↥(integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))
  have hmax : (P.asIdeal.comap (algebraMap (curveLocalRing I q) (curveNormalisation I q))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.asIdeal
  have hmax' := Ideal.comap_isMaximal_of_surjective
    (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))))))
    Ideal.Quotient.mk_surjective (K := P.asIdeal.comap (algebraMap (curveLocalRing I q) (curveNormalisation I q)))
    (H := hmax)
  have hloc := IsLocalRing.eq_maximalIdeal hmax'
  have hker : ∀ a ∈ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ),
      π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) a) = 0 := by
    intro a ha
    rw [← Localization.AtPrime.under_maximalIdeal (I := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)),
      Ideal.under, Ideal.mem_comap, ← hloc] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 ha

  have hcomp : π = ι.comp ε := by
    refine Ideal.Quotient.ringHom_ext ?_
    refine IsLocalization.ringHom_ext (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl ?_
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
    · show π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (C c)) =
        ι (ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (C c)))
      have he : ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (C c)) = c := by
        show evL (algebraMap (MvPolynomial (Fin n) ℂ)
          (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))) (C c)) = c
        simp [evL, IsLocalization.lift_eq]
      rw [he]
      rfl
    · have h1 : (X i - C (q i) : MvPolynomial (Fin n) ℂ) ∈ RingHom.ker (eval q) := by simp
      have h2 := hker _ h1
      rw [map_sub, map_sub, sub_eq_zero] at h2
      show π (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i)) =
        ι (ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i)))
      have he : ε (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i)) = q i := by
        show evL (algebraMap (MvPolynomial (Fin n) ℂ)
          (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))) (X i)) = q i
        simp [evL, IsLocalization.lift_eq]
      rw [he]
      exact h2

  have hint : ι.IsIntegral := by
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hb : IsIntegral (curveLocalRing I q) b := Algebra.IsIntegral.isIntegral b
    obtain ⟨p, hp, he⟩ := hb.map (Ideal.Quotient.mkₐ (curveLocalRing I q) P.asIdeal)
    refine ⟨p.map ε, hp.map ε, ?_⟩
    rw [Polynomial.eval₂_map, ← hcomp]
    exact he
  have hsurj : Function.Surjective ι := (IsAlgClosed.ringHom_bijective_of_isIntegral ι hint).2
  have hπ : Function.Surjective π := fun y ↦ by
    obtain ⟨c, hc⟩ := hsurj y
    exact ⟨_, hc⟩

  rw [Module.length_eq_one_iff, isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨inferInstance, fun x hx y ↦ ?_⟩
  obtain ⟨r, hr⟩ := hπ (y * x⁻¹)
  refine ⟨r, ?_⟩
  rw [LinearMap.toSpanSingleton_apply, Algebra.smul_def]
  change π r * x = y
  rw [hr, mul_assoc, inv_mul_cancel₀ hx, mul_one]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffDominated
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace CutOffDominated

variable {n d : ℕ}

theorem chartDens_congr_zeroSet {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {f g : (Fin n → ℂ) → ℝ} (h : ∀ x ∈ zeroSet J, f x = g x) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    chartDens J A f φ = chartDens J A g φ := by
  funext y
  unfold chartDens sheetSum
  refine finsum_congr fun x => finsum_congr fun hx => ?_
  simp only [h x hx.1]

open Classical in

theorem sheetSum_eq_sum {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) :
    sheetSum J A F y =
      ∑ x ∈ hfin.toFinset, if h : ∃ s, IsSheetAt J A x s then F x h.choose else 0 :=
  finsum_mem_eq_finite_toFinset_sum _ hfin

theorem ae_eval_ne_zero {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) :
    ∀ᵐ u : ι → ℂ, eval u g ≠ 0 := by
  have hU : (⋃ r : ℕ, LogInt.polydisc ι r) = Set.univ := by
    refine Set.eq_univ_of_forall fun u => ?_
    obtain ⟨r, hr⟩ := exists_nat_ge ‖u‖
    refine Set.mem_iUnion.mpr ⟨r, Set.mem_univ_pi.mpr fun i => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_pi_norm u i).trans hr
  have h := (ae_restrict_iUnion_iff (fun r : ℕ => LogInt.polydisc ι r) (fun u => eval u g ≠ 0)).mpr
    fun r => LogInt.ae_eval_ne_zero g hg r
  rwa [hU, Measure.restrict_univ] at h

end CutOffDominated

theorem CutOffDominated.proof : CutOffDominated.Statement := by
  classical
  intro n d J A P χ f ψ hJ hdim hA hP hχm hχ01 hlim hf hψ hint
  have hfin : ∀ y, (fibre J A y).Finite := fun y =>
    (ComplexSets.FibreBound.proof n d J A hJ hdim hA y).2.1
  set g : (Fin n → ℂ) → ℝ := (zeroSet J).piecewise f 0 with hgdef
  have hg : Measurable g :=
    hf.measurable_piecewise continuousOn_const (SheetSumMeasurable.isClosed_zeroSet J).measurableSet
  have hmeas : ∀ k, Measurable (chartDens J A (fun x => χ k x * f x) ψ) := fun k => by
    rw [CutOffDominated.chartDens_congr_zeroSet (g := fun x => χ k x * g x)
      (fun x hx => by rw [hgdef, Set.piecewise_eq_of_mem _ _ _ hx])]
    exact (SheetSumMeasurable.proof n d J A _ ψ hJ hdim hA ((hχm k).mul hg) hψ).1
  refine tendsto_integral_of_dominated_convergence (chartAbsDens J A f ψ)
    (fun k => (hmeas k).aestronglyMeasurable) hint (fun k => Eventually.of_forall fun y => ?_) ?_
  · rw [Real.norm_eq_abs]
    unfold chartDens chartAbsDens
    rw [CutOffDominated.sheetSum_eq_sum _ (hfin y), CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    split_ifs with h
    · rw [mul_assoc, abs_mul, abs_of_nonneg (hχ01 k x).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (hχ01 k x).2
    · simp
  · filter_upwards [CutOffDominated.ae_eval_ne_zero P hP] with y hy
    unfold chartDens
    simp only [CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine tendsto_finsetSum _ fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    have hxl := hlim x hx.1 (by rw [show A *ᵥ x = y from hx.2]; exact hy)
    split_ifs with h
    · simpa using (hxl.mul_const (f x)).mul_const
        (ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ h.choose) y)
    · exact tendsto_const_nhds

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PEnergyDensNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

noncomputable section

theorem EnergyDensNonneg.proof : EnergyDensNonneg.Statement := by
  intro n d s y v hs
  have hV : IsOpen {z | AnalyticAt ℂ s z} := isOpen_analyticAt ℂ s
  have hC : ∀ z ∈ {z | AnalyticAt ℂ s z}, ContDiffAt ℝ 2 (euclPot ∘ s) z := fun z hz =>
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp z
      (hz.restrictScalars (𝕜 := ℝ)).contDiffAt
  refine gradDensNonneg_thm d (fun _ => euclPot ∘ s) v _ hV
    (fun _ => fun z hz => (hC z hz).contDiffWithinAt) ?_ y hs
  intro _ z hz ξ
  rw [levi_comp ξ hz ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    TubeFormComparison.levi_euclPot]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormIntLelong
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix
open scoped ContDiff

theorem FormIntLelong.proof (hCP : ConeToProjective.Statement)
    (hCh : ChowFormSectionAlgClosed.Statement) (hFS : FormIntSlice.Statement)
    (hSL : SliceFormLelong.Statement) : FormIntLelong.Statement := by
  intro n e h W u u' δ hW hg hu' hδ
  obtain ⟨F, hF⟩ := hg
  obtain ⟨ℓ, hℓW, hℓP⟩ := SectionHyperplaneAvoid.proof n W u' hW
  have ha0 : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → fsLogReg h u δ (t • x) = fsLogReg h u δ x :=
    fun t x ht => fsLogReg_smul h u δ t x ht
  have ha1 : ContDiffOn ℝ ∞ (fsLogReg h u δ) {x | x ≠ 0} := contDiffOn_fsLogReg h u hδ

  have hWc := hCP n (e + 1) h W F ℓ (fsLogReg h u δ) hW hF hℓW ha0 ha1.continuousOn

  obtain ⟨c, -, gP, hgP, -⟩ := hCh ℂ n (e + 1) W F u' hW hF hu'
  have hcyc : cycleIntegral h (divCycle W u') e (fsLogReg h u δ) =
      ∑ P ∈ (divCycle W u').support, ((divCycle W u' P : ℕ) : ℝ) *
        varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e (fsLogReg h u δ)
          (fun _ x => Real.log (h.dualNorm x)) := by
    unfold cycleIntegral
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [hCP n e h P (gP P) ℓ (fsLogReg h u δ) (DivCyclePrime.proof n W u' hW P hP) (hgP P hP)
      (hℓP P hP) ha0 ha1.continuousOn]
  rw [hcyc, hWc]

  refine (hSL n e h W F u' ℓ (fsLogReg h u δ) hW hF hu' hℓW hℓP ha0 ha1).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hFS n e h W F ℓ (fsLogReg h u δ) (fsLogReg h u' ε) hW hF hℓW ha0 ha1.continuousOn
    (fun t x ht => fsLogReg_smul h u' ε t x ht) (contDiffOn_fsLogReg h u' hε)).symm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermProjectionFunctionForm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter PrimeGermPrimitivePresentation

noncomputable section

namespace GermProjectionFunctionForm

variable {σ : Type} [Fintype σ]

theorem germPull_toGerm {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (w : σ → ℂ) (u : anFun (A w)) :
    germPull A (A.analyticAt w) rfl (toGerm (A w) u) = toGerm w (compA A w u) :=
  Subtype.ext (germPull_coe A (A.analyticAt w) rfl _ u.1 rfl)

theorem coordGerm_eq_toGerm (w : σ → ℂ) (i : σ) :
    coordGerm w i = toGerm w (mkA (fun z : σ → ℂ => z i)
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)) :=
  Subtype.ext rfl

theorem isGermCombination_of_mem {w : σ → ℂ} {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) (u : anFun w)
    (hu : toGerm w u ∈ holGermIdeal w p) (f : (σ → ℂ) → ℂ) (hf : ∀ z, u.1 z = f z) :
    IsGermCombination w p f := by
  obtain ⟨h, hh, e⟩ := exists_of_mem_holGermIdeal p hu
  exact ⟨h, hh, (Germ.coe_eq.1 e).mono fun z hz => by rw [← hf]; exact hz⟩

end GermProjectionFunctionForm

open GermProjectionFunctionForm in

theorem GermProjectionFunctionForm.proof : GermProjectionFunctionForm.Statement := by
  classical
  intro σ _ w k p d A hp ⟨hinj, hgen, hint⟩
  let Z : σ → anFun w := fun i => mkA (fun z : σ → ℂ => z i)
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w)
  have hZ : ∀ i, coordGerm w i = toGerm w (Z i) := coordGerm_eq_toGerm w
  have hpull : ∀ φ : holGerms (A w), germPull A (A.analyticAt w) rfl φ = toGerm w (compA A w (rep φ)) := by
    intro φ
    conv_lhs => rw [← toGerm_rep φ]
    exact germPull_toGerm A w (rep φ)
  refine ⟨?_, ?_, ?_⟩
  · intro h hh hcomb
    have hmem := (toGerm_mem_iff hp (compA A w (mkA h hh))).2 hcomb
    rw [← germPull_toGerm] at hmem
    have h0 := congrArg Subtype.val (hinj _ hmem)
    exact Germ.coe_eq.1 (h0.trans (Germ.coe_zero (l := 𝓝 (A w)) (M := ℂ)).symm)
  · intro i
    obtain ⟨q, hq, hqP⟩ := hint i
    refine ⟨q.natDegree, fun j => (rep (q.coeff j)).1, fun j => (rep (q.coeff j)).2, ?_⟩
    have key : q.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w i) =
        toGerm w (Z i ^ q.natDegree + ∑ j : Fin q.natDegree, compA A w (rep (q.coeff j)) * Z i ^ (j : ℕ)) := by
      conv_lhs => rw [hq.as_sum]
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_finsetSum,
        Polynomial.eval₂_mul, Polynomial.eval₂_C, map_add, map_pow, map_sum, map_mul, hpull, hZ]
      rw [Fin.sum_univ_eq_sum_range (fun j => toGerm w (compA A w (rep (q.coeff j))) * toGerm w (Z i) ^ j)]
    rw [key] at hqP
    refine isGermCombination_of_mem p _ hqP _ fun z => ?_
    simp [Z, mkA, compA, Finset.sum_apply]
  · intro g hg
    obtain ⟨F, hF⟩ := hgen (toGerm w (mkA g hg))
    let e := Finsupp.equivFunOnFinite (α := σ) (M := ℕ)
    refine ⟨F.support.image e, fun m => (rep (F.coeff (e.symm m))).1, fun m _ => (rep (F.coeff (e.symm m))).2, ?_⟩
    have key : toGerm w (mkA g hg) - MvPolynomial.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w) F =
        toGerm w (mkA g hg - ∑ m ∈ F.support, compA A w (rep (F.coeff m)) * ∏ i, Z i ^ m i) := by
      rw [MvPolynomial.eval₂_eq']
      simp only [map_sub, map_sum, map_mul, map_prod, map_pow, hpull, hZ]
    rw [key] at hF
    refine isGermCombination_of_mem p _ hF _ fun z => ?_
    rw [Finset.sum_image (fun x _ y _ h => e.injective h)]
    simp [Z, mkA, compA, Finset.sum_apply, Finset.prod_apply, e]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

