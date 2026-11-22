import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0002
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PairingExists
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalPairSumGramBound

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernDensitySheetEq
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ZDens

theorem chernDens_sheet : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (c : AlgChart p σ D) (c' : AlgChart t τ D), (∀ y ∈ c.e.source, sheet t τ y ∈ c'.e.source ∧ c'.e (sheet t τ y) = c.e y) → ∀ y ∈ c.e.source, c'.chernDens ψ (sheet t τ y) = c.chernDens (φ σ) y := by
  intro k _ _ _ _ X p t τ σ D B φ ψ hW hφ hψ c c' hm y hy
  obtain ⟨hy', he⟩ := hm y hy
  have hi := GlobalTheory.CxPts.mem_pick (φ σ).isLB y
  set i := GlobalTheory.CxPts.pick (φ σ).isLB y
  have hi' : sheet t τ y ∈ ptsIn t τ (B.U i) := hi
  rw [c'.chernDens_eq hψ hy' hi', c.chernDens_eq (hφ σ) hy hi, AlgChart.hess, AlgChart.hess, he]
  have ho := GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
  have hmem := GlobalTheory.ChartGlue.mem_over c.e hy hi
  have e : (fun v => ((ψ.φ i (c'.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)]
      fun v => (((φ σ).φ i (c.e.symm v) : ℝ) : ℂ) := by
    filter_upwards [ho.mem_nhds hmem] with v hv
    have hw := c.e.map_target hv.1
    obtain ⟨h₁, h₂⟩ := hm _ hw
    have hs : c'.e.symm v = sheet t τ (c.e.symm v) := by
      rw [← c'.e.left_inv h₁, h₂, c.e.right_inv hv.1]
    rw [hs, hW σ i _ hv.2]
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e]

end GlobalTheory.CompanionTheory.Ar.ZDens
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsFramePeriodsNoGlobal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open GlobalTheory.CompanionTheory.Ar.FramePeriods
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx

theorem exists_isFramePeriods_noGlobal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), ∀ (a b : CMType H ⊕ CMType H) (N : ℕ) (bb : Fin N → ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : SncChart (mCoordIdeal y) n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω), (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z)) → t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 → (∀ p : Cpt 𝔐.ξ, InChart 𝔐.ξ (segreCoord y) cc p → unitAt 𝔐.ξ p f → (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb p) → InFrameDomain y cc f (χ.γ t₀) → ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), HodgeMetric.IsFramePeriods 𝔐 (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) χ t₀ cc f L π ρ U := by
  intro E _ _ _ H D Xo l c Y S Ω _ _ K _ J _ y 𝔐 a b N bb n Bd χ t₀ cc f hBd ht₀ hfr hdom
  classical
  obtain ⟨a₀, π, ρ₀, ha, hρ₀, hρ₀', hπ, hgeo⟩ := GlobalTheory.T.snc_chart_local_normal_form K J Ω y _ n Bd χ t₀ cc f ht₀ hdom
  have hw : DifferentiableOn ℂ (fun u => χ.γ (HodgeMetric.recentre t₀ ρ₀ π u)) (Metric.ball 0 1) := by
    refine χ.analytic.differentiableOn.comp ?_ fun u hu => (hgeo ρ₀ hρ₀ le_rfl u hu).1
    unfold HodgeMetric.recentre
    exact (differentiable_const _ |>.add (differentiable_pi.2 fun i => by
      simpa using (differentiable_apply (π i) : Differentiable ℂ fun u : Fin n → ℂ => u (π i)).const_mul (ρ₀ : ℂ))).differentiableOn
  set w : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun u => χ.γ (HodgeMetric.recentre t₀ ρ₀ π u) with hwdef
  have htie := 𝔐.tie
  have hall := 𝔐.all
  have hex : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, ∃ z : Sp ℂ ⟶ 𝔐.X, genPt 𝔐.ξ ⤳ centre z ∧ CoordsAt 𝔐.ξ y z (w u) := fun u hu =>
    (GlobalTheory.T.complex_points_iff_centres 𝔐.X Ω 𝔐.ξ K J y htie (w u)).1 (χ.mem _ (hgeo ρ₀ hρ₀ le_rfl u hu).1)
  haveI : Nonempty (Sp ℂ ⟶ 𝔐.X) := ⟨(hex 0 (by simp)).choose⟩
  choose! p hp₀ hp using hex
  have huniq : ∀ (z z' : Sp ℂ ⟶ 𝔐.X) (w' : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w' → CoordsAt 𝔐.ξ y z' w' → z = z' := fun z z' w' h h' => by
    obtain ⟨e1, -, e3⟩ := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X Ω 𝔐.ξ K J y htie ℂ
    exact (e1 w' h.1 (e3 z w' (hall _) h).1).unique ⟨hall _, h⟩ ⟨hall _, h'⟩

  have fin : ∀ (g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (ρ₁ : ℝ)
      (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), 0 < ρ₁ → ρ₁ ≤ 1 →
      (∀ k, DifferentiableOn ℂ (U k) (Metric.ball 0 1)) → LinearIndependent ℂ (fun k => U k 0) →
      (∀ u ∈ Flat.punct n a₀ 1, ∀ z : Sp ℂ ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (w ((ρ₁ : ℂ) • u)) →
        𝔐.M.GramAt 𝔐.t.PP.L z (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) (HodgeMetric.periodGram L U u)) →
      ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (L : Flat.LogPeriods n a₀ g Λ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (U : Fin N → (Fin n → ℂ) → Fin g → ℂ), HodgeMetric.IsFramePeriods 𝔐 (fun k => ((bb k : ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b)) : 𝔐.Li)) χ t₀ cc f L π ρ U := by
    intro g Λ _ L ρ₁ U h1 h2 h3 h4 h5
    have hle : ρ₀ * ρ₁ ≤ ρ₀ := by nlinarith
    have hpos : 0 < ρ₀ * ρ₁ := mul_pos hρ₀ h1
    refine ⟨a₀, g, Λ, inferInstance, L, π, ρ₀ * ρ₁, U, hpos, by nlinarith, h3, h4, hπ, fun u hu => ?_⟩
    obtain ⟨g1, g2, g3⟩ := hgeo _ hpos hle u hu
    refine ⟨g1, g2, g3, fun hup z hz => ?_⟩
    rw [recentre_mul] at hz
    exact h5 u hup z hz
  have hb0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := by simp
  have hfr0 : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre (p 0), hall _⟩ := by
    have hd := (hgeo ρ₀ hρ₀ le_rfl 0 hb0).2.1
    obtain ⟨c1, c2⟩ := GlobalTheory.T.frame_domain_in_segre_chart 𝔐.X Ω 𝔐.ξ K J y htie (p 0) (w 0) cc f (hall _) (hp 0 hb0) hd
    exact hfr _ c1 c2
  by_cases hpq : D.p + D.q = 0
  · have hV : ∀ s, 𝔐.Vgen s = ⊥ := fun s => by
      obtain ⟨-, -, b', hb', -⟩ := 𝔐.vb s ⟨genPt 𝔐.ξ, specializes_rfl⟩ trivial
      have hr : labelRk D s = 0 := by
        rcases s with s | s <;> simp only [labelRk, Sum.elim_inl, Sum.elim_inr] <;> omega
      have : IsEmpty (Fin (labelRk D s)) := by rw [hr]; infer_instance
      have e : Set.range b' = ∅ := Set.range_eq_empty b'
      rw [e, Submodule.span_empty] at hb'
      exact hb'.symm
    have hli := hfr0.1
    haveI : Subsingleton ↥(𝔐.Vgen a ⊔ 𝔐.Vgen b) := by
      rw [hV a, hV b, sup_bot_eq]
      infer_instance
    haveI : IsEmpty (Fin N) := ⟨fun k => hli.ne_zero k (Subsingleton.elim _ _)⟩
    obtain ⟨Λ, _, ⟨L⟩⟩ := zeroPeriods n a₀ ha
    exact fin 0 Λ _ L 1 (fun _ _ => 0) one_pos le_rfl (fun k => isEmptyElim k) linearIndependent_empty_type
      fun u _ z _ => ⟨fun k => isEmptyElim k, fun k => isEmptyElim k, fun k => isEmptyElim k⟩
  have hpq' : 1 ≤ D.p + D.q := Nat.one_le_iff_ne_zero.2 hpq
  have hhol : IsHolTo (Metric.ball 0 1) p := GlobalTheory.T.holomorphic_coords_of_generic_point 𝔐.X Ω 𝔐.ξ K J y htie hall n _ w p Metric.isOpen_ball hw hp
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.holomorphic_disc_over_number_field_ring c.F 𝔐.X (𝔐.f ≫ Y.s) n p hhol
  have hint : ∀ u ∈ Flat.punct n a₀ 1, 𝔐.Interior (p u) := fun u hu => by
    have h1 := (hgeo ρ₀ hρ₀ le_rfl u hu.1).2.2
    have h2 := hBd (p u) (w u) (hp u hu.1)
    by_contra h
    exact (h1.2 hu) (h2.2 h)
  set σ : KA l →+* ℂ := τ.comp (IntermediateField.inclusion c.le).toRingHom with hσ
  have hsq : (σ (baseKA l).ρ) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, (baseKA l).ρ_sq, H.sqrt_neg_disc_sq]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hs | hs
  · obtain ⟨g, Λ, _, L, ρ₁, U, h1, h2, h3, h4, h5⟩ := core 𝔐 a b N bb n a₀ p τ hpq' hs ha hhol hτ hint (hall _) hfr0
    refine fin g Λ _ L ρ₁ U h1 h2 h3 h4 fun u hu z hz => ?_
    rw [huniq z _ _ hz (hp _ (smul_mem_ball' h1 h2 hu.1))]
    exact h5 u hu
  · have hcc : (spMap (starRingEnd ℂ) : Sp ℂ ⟶ Sp ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 _ := by
      refine (Spec.map_comp (CommRingCat.ofHom (starRingEnd ℂ)) (CommRingCat.ofHom (starRingEnd ℂ))).symm.trans ?_
      convert Spec.map_id (CommRingCat.of ℂ)
      ext x
      simp
    set p' : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X) := fun u => spMap (starRingEnd ℂ) ≫ p (star u) with hp'
    have hcoord : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, CoordsAt 𝔐.ξ y (p' u) (fun q => star (w (star u) q)) := fun u hu =>
      (GlobalTheory.T.conjugate_point_same_centre 𝔐.X Ω 𝔐.ξ K J y _ _).2 (hp _ (star_mem_ball' hu))
    have hcen : ∀ u, centre (p' u) = centre (p (star u)) := fun u => (GlobalTheory.T.conjugate_point_same_centre 𝔐.X Ω 𝔐.ξ K J y _ (w 0)).1
    have hhol' : IsHolTo (Metric.ball 0 1) p' := GlobalTheory.T.holomorphic_coords_of_generic_point 𝔐.X Ω 𝔐.ξ K J y htie hall n _ _ p' Metric.isOpen_ball
      (diffOn_star' hw) hcoord
    have hτ' : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p' u ≫ 𝔐.f ≫ Y.s =
        spMap (((starRingEnd ℂ).comp τ).comp (algebraMap (𝓞 c.F) c.F)) := fun u hu => by
      rw [hp', Category.assoc, hτ _ (star_mem_ball' hu)]
      exact (Spec.map_comp (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 c.F) c.F))) (CommRingCat.ofHom (starRingEnd ℂ))).symm
    have hint' : ∀ u ∈ Flat.punct n a₀ 1, 𝔐.Interior (p' u) := fun u hu => by
      change centre (p' u) ∈ _
      rw [hcen]
      exact hint _ (star_mem_punct' hu)
    have hs' : (((starRingEnd ℂ).comp τ).comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 := by
      change (starRingEnd ℂ) (σ (baseKA l).ρ) = H.rt0
      rw [hs, map_neg, rt0_conj_neg_ne_zero, neg_neg]
    have hfr0' : (Lat.comap (fun p => 𝔐.V a p ⊔ 𝔐.V b p) (𝔐.Vgen a ⊔ 𝔐.Vgen b).subtype).IsFrameAt bb ⟨centre (p' 0), hall _⟩ := by
      have e : (⟨centre (p' 0), hall _⟩ : Cpt 𝔐.ξ) = ⟨centre (p 0), hall _⟩ := Subtype.ext (by
        show centre (p' 0) = centre (p 0)
        rw [hcen, star_zero])
      rw [e]
      exact hfr0
    obtain ⟨g, Λ, _, L', ρ₁, U', h1, h2, h3, h4, h5⟩ := core 𝔐 a b N bb n a₀ p' _ hpq' hs' ha hhol' hτ' hint' (hall _) hfr0'
    obtain ⟨L, hL⟩ := GlobalTheory.T.exists_conjugate_log_periods n a₀ g N Λ L' U' (GlobalTheory.T.bijective_logPeriods_T n a₀ g Λ L')
    refine fin g Λ _ L ρ₁ (fun k u' => star (U' k (star u'))) h1 h2 (fun k => diffOn_star' (h3 k)) ?_ fun u hu z hz => ?_
    · refine Fintype.linearIndependent_iff.2 fun c' hc' k => ?_
      have e := congrArg star hc'
      simp only [star_sum, star_smul, star_star, star_zero] at e
      have := Fintype.linearIndependent_iff.1 h4 (fun k => star (c' k)) (by simpa [star_smul] using e) k
      simpa using this
    · rw [hL u hu, huniq z _ _ hz (hp _ (smul_mem_ball' h1 h2 hu.1))]
      have := GlobalTheory.T.gramAt_conj_point_map_conj E H D l (Xo l) c Y S Ω K J y 𝔐 _ N _ _ (h5 (star u) (star_mem_punct' hu))
      have e : spMap (starRingEnd ℂ) ≫ p' ((ρ₁ : ℂ) • star u) = p ((ρ₁ : ℂ) • u) := by
        rw [hp']
        simp only
        rw [← Category.assoc, hcc, Category.id_comp, star_smul, star_star]
        simp
      rwa [e] at this

end GlobalTheory.CompanionTheory.Ar.PB.BMx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegrableOnAndSetIntegralOfEmbeddings
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

namespace GlobalTheory.CompanionTheory.Metric

theorem measure_eq_sum_map_of_embeddings {α : Type} [Fintype α] {Y : Type} [MeasurableSpace Y]
    {Z : α → Type} [∀ a, MeasurableSpace (Z a)] {s : ∀ a, Z a → Y}
    (hs : ∀ a, MeasurableEmbedding (s a)) (hu : ∀ y, ∃! a, y ∈ Set.range (s a))
    {ν : Measure Y} {μ : ∀ a, Measure (Z a)}
    (hν : ∀ a (S : Set (Z a)), MeasurableSet S → ν (s a '' S) = μ a S) :
    ν = ∑ a, Measure.map (s a) (μ a) := by
  ext T hT
  rw [Measure.finsetSum_apply]
  have hcover : T = ⋃ a, T ∩ Set.range (s a) := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hy
      obtain ⟨a, ha, -⟩ := hu y
      exact ⟨a, hy, ha⟩
    · rintro ⟨a, hy, -⟩
      exact hy
  have hdisj : Pairwise (Function.onFun Disjoint fun a => T ∩ Set.range (s a)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro y ⟨-, hya⟩ ⟨-, hyb⟩
    obtain ⟨a', -, ha'⟩ := hu y
    exact hab ((ha' a hya).trans (ha' b hyb).symm)
  have hmeas : ∀ a, MeasurableSet (T ∩ Set.range (s a)) := fun a =>
    hT.inter (hs a).measurableSet_range
  rw [show ν T = ν (⋃ a, T ∩ Set.range (s a)) by rw [← hcover], measure_iUnion hdisj hmeas,
    tsum_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [(hs a).map_apply, ← hν a _ ((hs a).measurable hT), Set.image_preimage_eq_inter_range]

theorem integrableOn_and_setIntegral_of_embeddings :
    ∀ (α : Type) [Finite α] (Y : Type) [MeasurableSpace Y] (Z : α → Type)
      [∀ a, MeasurableSpace (Z a)] (s : ∀ a, Z a → Y), (∀ a, MeasurableEmbedding (s a)) →
      (∀ y, ∃! a, y ∈ Set.range (s a)) → ∀ (ν : Measure Y) (μ : ∀ a, Measure (Z a)),
      (∀ a (S : Set (Z a)), MeasurableSet S → ν (s a '' S) = μ a S) →
      ∀ (S : Set Y), MeasurableSet S → ∀ f : Y → ℝ,
      (IntegrableOn f S ν ↔ ∀ a, IntegrableOn (fun z => f (s a z)) (s a ⁻¹' S) (μ a)) ∧
      (IntegrableOn f S ν →
        ∫ y in S, f y ∂ν = ∑ᶠ a, ∫ z in s a ⁻¹' S, f (s a z) ∂(μ a)) := by
  intro α _ Y _ Z _ s hs hu ν μ hν S hS f
  haveI := Fintype.ofFinite α
  have hνeq := measure_eq_sum_map_of_embeddings hs hu hν
  have hres : ν.restrict S = ∑ a, (Measure.map (s a) (μ a)).restrict S := by
    ext T hT
    rw [hνeq, Measure.restrict_apply hT, Measure.finsetSum_apply, Measure.finsetSum_apply]
    simp only [Measure.restrict_apply hT]
  have hint : IntegrableOn f S ν ↔ ∀ a, IntegrableOn (fun z => f (s a z)) (s a ⁻¹' S) (μ a) := by
    rw [IntegrableOn, hres, integrable_finsetSum_measure]
    simp only [Finset.mem_univ, forall_const]
    exact forall_congr' fun a => (hs a).integrableOn_map_iff
  refine ⟨hint, fun hf => ?_⟩
  have hf' : ∀ a ∈ Finset.univ, Integrable f ((Measure.map (s a) (μ a)).restrict S) := fun a _ =>
    (hs a).integrableOn_map_iff.mpr (hint.mp hf a)
  rw [finsum_eq_sum_of_fintype, hres, integral_finsetSum_measure hf']
  exact Finset.sum_congr rfl fun a _ => (hs a).setIntegral_map _ _

end GlobalTheory.CompanionTheory.Metric
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormSheetEq
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

noncomputable section

theorem GlobalTheory.CompanionTheory.Ar.BaseZ.logNorm_sheet : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → ∀ (r : B.ι → X.functionFieldˣ) (hr : IsRatSec B r) (σ : k →+* ℂ) (y : CxPts p σ), y ∈ offSupp p σ (divOfRatSec ψ.isLB hr) → logNorm ψ r (sheet t τ y) = logNorm (φ σ) r y := by
  intro k _ X _ p t τ B φ ψ h r hr σ y hy
  have hy' : sheet t τ y ∈ offSupp t τ (divOfRatSec ψ.isLB hr) := mem_offSupp.2 (mem_offSupp.1 hy)
  have hi' := mem_pick ψ.isLB (sheet t τ y)
  set i := pick ψ.isLB (sheet t τ y)
  have hi : y ∈ ptsIn p σ (B.U i) := mem_ptsIn.2 (mem_ptsIn.1 hi')
  rw [logNorm_eq ψ hr hy' hi', logNorm_eq (φ σ) hr hy hi, h σ i y hi]
  congr 3
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetIsOpenEmbeddingRange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BaseZ.Sheet

theorem finite_ringHom (k : Type) [CommRing k] [Module.Finite ℤ k] : Finite (k →+* ℂ) := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ k).FG)
  have hroot : ∀ a : k, ∃ S : Set ℂ, S.Finite ∧ ∀ σ : k →+* ℂ, σ a ∈ S := by
    intro a
    obtain ⟨P, hm, hP⟩ := (Algebra.IsIntegral.isIntegral a : IsIntegral ℤ a)
    refine ⟨{z | (P.map (Int.castRingHom ℂ)).IsRoot z}, ?_, fun σ => ?_⟩
    · exact Polynomial.finite_setOf_isRoot (hm.map _).ne_zero
    · have h : Polynomial.eval₂ (σ.comp (algebraMap ℤ k)) (σ a) P = 0 := by
        rw [← Polynomial.hom_eval₂, hP, map_zero]
      rw [Subsingleton.elim (σ.comp (algebraMap ℤ k)) (Int.castRingHom ℂ)] at h
      simpa [Polynomial.IsRoot, Polynomial.eval_map] using h
  choose S hS hm using hroot
  have : ∀ i : s, Finite (S i) := fun i => (hS i).to_subtype
  refine Finite.of_injective (fun (σ : k →+* ℂ) (i : s) => (⟨σ i, hm i σ⟩ : S i)) fun σ₁ σ₂ h => ?_
  have hs' : ∀ i ∈ s, σ₁ i = σ₂ i := fun i hi => congrArg Subtype.val (congrFun h ⟨i, hi⟩)
  have hspan : ∀ x ∈ Submodule.span ℤ (s : Set k), σ₁ x = σ₂ x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h => exact hs' x h
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, hx, hy]
    | smul a x _ hx => simp [map_zsmul, hx]
  exact RingHom.ext fun x => hspan x (hs ▸ Submodule.mem_top)

variable {k : Type} [CommRing k] {X : Scheme.{0}}

theorem emb_apply (p : X ⟶ Sp k) {t : X ⟶ Sp ℤ} {τ : ℤ →+* ℂ} (y : CxPts t τ) (a : k) :
    emb p y a = ev t τ ⊤ (algX p ⊤ a) y :=
  (ev_algX (y := unsheet p y) mem_ptsIn_top a).symm

theorem range_sheet (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) :
    Set.range (sheet t τ : CxPts p σ → CxPts t τ) = {y | emb p y = σ} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact emb_sheet t τ z
  · intro h
    have h' : emb p y = σ := h
    subst h'
    exact ⟨unsheet p y, rfl⟩

theorem isOpen_emb_eq [Finite (k →+* ℂ)] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) :
    IsOpen {y : CxPts t τ | emb p y = σ} := by
  have hc (a : k) : Continuous fun y : CxPts t τ => emb p y a := by
    simp only [emb_apply]
    exact (Points.continuous_valR_top _).comp continuous_subtype_val
  have e : {y : CxPts t τ | emb p y = σ} =
      ⋂ σ' : {s : k →+* ℂ // s ≠ σ}, ⋃ a : k, {y | emb p y a ≠ σ'.1 a} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · rintro rfl σ'
      by_contra h
      push Not at h
      exact σ'.2 (RingHom.ext fun a => (h a).symm)
    · intro h
      by_contra he
      obtain ⟨a, ha⟩ := h ⟨_, he⟩
      exact ha rfl
  rw [e]
  exact isOpen_iInter_of_finite fun σ' => isOpen_iUnion fun a => isOpen_ne_fun (hc a) continuous_const

theorem isOpenEmbedding_and_range : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ), Topology.IsOpenEmbedding (sheet t τ : CxPts p σ → CxPts t τ) ∧ Set.range (sheet t τ : CxPts p σ → CxPts t τ) = {y | emb p y = σ} := by
  intro k _ _ X p t τ σ
  have := finite_ringHom k
  have hr := range_sheet p t τ σ
  refine ⟨⟨IsEmbedding.of_comp (continuous_subtype_val.subtype_mk _) continuous_subtype_val
    IsEmbedding.subtypeVal, ?_⟩, hr⟩
  rw [hr]
  exact isOpen_emb_eq p t τ σ

end GlobalTheory.CompanionTheory.Ar.BaseZ.Sheet
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ToZIsometric
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem toZ_isometric : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (L M : HermLB p)
    (hL : ∀ τ, (wZ L t τ).IsCInf) (hM : ∀ τ, (wZ M t τ).IsCInf), L.Isometric M →
    (toZ L t hL).Isometric (toZ M t hM) := by
  intro k _ X p t L M hL hM ⟨w, hw, h⟩
  refine ⟨w, hw, fun τ a b y ha hb => ?_⟩
  exact h (emb p y) a b (unsheet p y) ha hb

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ToZPullIsometric
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem isometric_toZ_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (t : X ⟶ Sp ℤ) (t' : Y ⟶ Sp ℤ) (π : Y ⟶ X) (hπ : π ≫ p = q) (hπ' : π ≫ t = t') (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (hL' : ∀ τ, (wZ (L.pull π hπ) t' τ).IsCInf), (toZ (L.pull π hπ) t' hL').Isometric ((toZ L t hL).pull π hπ') := by
  intro k _ X Y p q t t' π hπ hπ' L hL hL'
  refine HermLB.isometric_of_eqOn fun τ a y _ => ?_
  have key : ∀ (σ σ' : k →+* ℂ) (_ : σ = σ') (z : CxPts p σ) (z' : CxPts p σ'), z.1 = z'.1 →
      (L.φ σ).φ (a PUnit.unit) z = (L.φ σ').φ (a PUnit.unit) z' := by
    rintro σ _ rfl z z' h
    rw [Subtype.ext h]
  refine (Weight.pull_φ (wZ L t τ) π hπ' a y).trans (Eq.trans ?_ (Weight.pull_φ (L.φ (emb q y)) π hπ a (unsheet q y)).symm)
  refine key _ _ ?_ _ _ rfl
  have e : (PtsOver.map π hπ' _ y).1 ≫ p = y.1 ≫ q := by
    rw [← hπ]
    exact Category.assoc _ _ _
  show (Spec.preimage ((PtsOver.map π hπ' _ y).1 ≫ p)).hom = (Spec.preimage (y.1 ≫ q)).hom
  rw [e]

end GlobalTheory.CompanionTheory.Ar.BaseZ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.WOverRestrPow
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem WOver.pow {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {t : X ⟶ Sp ℤ} {τ : ℤ →+* ℂ}
    {B : LB X} {φ : ∀ σ : k →+* ℂ, Weight p σ B} {ψ : Weight t τ B} (h : WOver φ ψ) (m : ℕ) :
    WOver (fun σ => (φ σ).pow m) (ψ.pow m) := by
  intro σ j y hy
  refine (ψ.zpow_φ _ j _).trans (Eq.trans ?_ ((φ σ).zpow_φ _ j y).symm)
  exact congrArg _ (h σ _ y (mem_pow_iff.1 hy))

theorem WOver.restr {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {t : X ⟶ Sp ℤ} {τ : ℤ →+* ℂ}
    {B : LB X} {φ : ∀ σ : k →+* ℂ, Weight p σ B} {ψ : Weight t τ B} (h : WOver φ ψ) (i : Z ⟶ X) :
    WOver (p := i ≫ p) (t := i ≫ t) (fun σ => (φ σ).pull i rfl) (ψ.pull i rfl) := by
  intro σ j y hy
  have hm : PtsOver.map i rfl _ y ∈ ptsIn p σ (B.U (j PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => PtsOver.map i rfl _ y) (fun _ => rfl) hy PUnit.unit
  refine (ψ.pull_φ i rfl j _).trans (Eq.trans ?_ ((φ σ).pull_φ i rfl j y).symm)
  exact h σ _ _ hm

theorem wOver_restr_pow : ∀ (k : Type) [CommRing k] (X Z : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (i : Z ⟶ X) (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (τ : ℤ →+* ℂ), WOver (L.restr i).φ (((toZ L t hL).restr i).φ τ) ∧ ∀ m : ℕ, WOver ((L.restr i).pow m).φ ((((toZ L t hL).restr i).pow m).φ τ) := by
  intro k _ X Z p t i L hL τ
  have h : WOver (L.restr i).φ (((toZ L t hL).restr i).φ τ) := (wOver_wZ L t τ).restr i
  exact ⟨h, fun m => h.pow m⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
end
end

