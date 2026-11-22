import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0689
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0681
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0680
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0687
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0557
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0621
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0691
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0607
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0686
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicChartOfExpChartGenericFibre
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

open GlobalTheory.Points Filter Topology

section Transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) {X : Var F} {j : X.X ⟶ gen Z}
  (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str)

theorem isOpenEmbedding_cxOf [IsOpenImmersion j] : IsOpenEmbedding (cxOf e σ hj) := by
  have hc : Continuous (cxOf e σ hj) :=
    continuous_induced_rng.2 ((continuous_comp (C := ℂ) j).comp continuous_subtype_val)
  refine ⟨IsEmbedding.of_comp hc continuous_subtype_val
    (((isOpenEmbedding_comp (C := ℂ) j).isEmbedding).comp IsEmbedding.subtypeVal), ?_⟩
  have hr : Set.range (cxOf e σ hj) = Subtype.val ⁻¹' Set.range fun x : Sp ℂ ⟶ X.X => x ≫ j := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, rfl⟩
    · rintro ⟨x, hx⟩
      replace hx : x ≫ j = y.1 := hx
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      rw [← hj, ← Category.assoc, hx, ← Category.assoc, y.2, ← Spec.map_comp]
      rfl
  rw [hr]
  exact (isOpenEmbedding_comp (C := ℂ) j).isOpen_range.preimage continuous_subtype_val

variable [IsOpenImmersion j]

theorem le_preimage_cxOf (W : X.X.Opens) {z : CxPts X.str (σ.comp e.toRingHom)}
    (hz : z ∈ ptsIn X.str (σ.comp e.toRingHom) W) : ⊤ ≤ (cxOf e σ hj z).1 ⁻¹ᵁ (j ''ᵁ W) :=
  le_preimage_comp z.1 j (j.preimage_image_eq W).ge hz

theorem ev_eq_valAt'_cxOf (W : X.X.Opens) (g : Γ(X.X, W)) {z : CxPts X.str (σ.comp e.toRingHom)}
    (hz : z ∈ ptsIn X.str (σ.comp e.toRingHom) W) :
    ev X.str (σ.comp e.toRingHom) W g z = valAt' (cxOf e σ hj z).1 (j ''ᵁ W) ((j.appIso W).inv.hom g) := by
  have hle : W ≤ j ⁻¹ᵁ j ''ᵁ W := (j.preimage_image_eq W).ge
  change valR z.1 W g = valR (z.1 ≫ j) (j ''ᵁ W) _
  rw [← valR_appLE z.1 j hle hz, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  exact (valR_res z.1 le_rfl hz g).symm

end Transfer

open GlobalTheory.Points Filter Topology

theorem finrank_eq_of_differentiableAt {E₁ E₂ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] (Φ : OpenPartialHomeomorph E₁ E₂) {x : E₁} (hx : x ∈ Φ.source)
    (h₁ : DifferentiableAt ℂ Φ x) (h₂ : DifferentiableAt ℂ Φ.symm (Φ x)) :
    Module.finrank ℂ E₁ = Module.finrank ℂ E₂ := by
  have hl : (fderiv ℂ Φ.symm (Φ x)).comp (fderiv ℂ Φ x) = ContinuousLinearMap.id ℂ E₁ :=
    ((h₂.hasFDerivAt.comp x h₁.hasFDerivAt).congr_of_eventuallyEq
      (EventuallyEq.symm (Φ.eventually_left_inverse hx : Φ.symm ∘ Φ =ᶠ[𝓝 x] id))).unique (hasFDerivAt_id x)
  have h₁' : HasFDerivAt Φ (fderiv ℂ Φ x) (Φ.symm (Φ x)) := by
    rw [Φ.left_inv hx]
    exact h₁.hasFDerivAt
  have hr : (fderiv ℂ Φ x).comp (fderiv ℂ Φ.symm (Φ x)) = ContinuousLinearMap.id ℂ E₂ :=
    ((h₁'.comp (Φ x) h₂.hasFDerivAt).congr_of_eventuallyEq
      (EventuallyEq.symm (Φ.eventually_right_inverse' hx : Φ ∘ Φ.symm =ᶠ[𝓝 (Φ x)] id))).unique (hasFDerivAt_id (Φ x))
  exact (ContinuousLinearEquiv.equivOfInverse (fderiv ℂ Φ x) (fderiv ℂ Φ.symm (Φ x))
    (fun v => DFunLike.congr_fun hl v) (fun v => DFunLike.congr_fun hr v)).toLinearEquiv.finrank_eq

section Transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ}

theorem differentiableAt_valAt'_symm {n g : ℕ} {ch₀ : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)}
    {ex : ExpMaps Z σ g} (h : IsExpChart ch₀ ex) (U : (gen Z).Opens) (f : Γ(gen Z, U)) {b : Fin n → ℂ}
    (hb : b ∈ ch₀.target) (hU : ⊤ ≤ (ch₀.symm b).1 ⁻¹ᵁ U) :
    DifferentiableAt ℂ (fun b => valAt' (ch₀.symm b).1 U f) b :=
  (h.2.2.1 U f).2.differentiableAt ((h.2.2.1 U f).1.mem_nhds ⟨hb, hU⟩)

end Transfer

theorem exists_holoChart_of_expChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ (y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (n g : ℕ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g), IsExpChart ch₀ ex → cxOf e σ hj y ∈ ch₀.source → ch₀ (cxOf e σ hj y) = 0 → ∀ r : ℝ, 0 < r → ∃ (hn : n = X.dim) (r' : ℝ) (ch : OpenPartialHomeomorph (GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (ReciprocityTheory.L2DbarEstimates.V X.dim)), 0 < r' ∧ r' < r ∧ r' < 1 ∧ IsHoloChart ch ∧ y ∈ ch.source ∧ ch y = 0 ∧ (∀ z ∈ ch.source, (ch z).ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc X.dim 1) ∧ ∀ z ∈ ch.source, cxOf e σ hj z ∈ ch₀.source ∧ ch₀ (cxOf e σ hj z) = fun k => (r' : ℂ) * (ch z).ofLp (Fin.cast hn k) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ X j hj hji y n g ch₀ ex hex hy0 hy00 r hr
  set κ := cxOf e σ hj with hκdef
  have hκ : IsOpenEmbedding κ := isOpenEmbedding_cxOf e σ hj
  haveI : Nonempty (GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) := ⟨y⟩
  set χ := (hκ.toOpenPartialHomeomorph κ).trans ch₀ with hχdef
  have hχ : ∀ u ∈ χ.target, κ (χ.symm u) = ch₀.symm u := fun u hu => by
    have h2 : ch₀.symm u ∈ Set.range κ := by
      have := hu.2
      rwa [Set.mem_preimage, IsOpenEmbedding.toOpenPartialHomeomorph_target] at this
    rw [OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply]
    exact hκ.toOpenPartialHomeomorph_right_inv κ h2
  have hyχ : y ∈ χ.source := ⟨trivial, hy0⟩
  have hχy : χ y = 0 := hy00
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.AlgChart.exists_mem_source (p := X.str) (σ := σ.comp e.toRingHom) (D := X.dim) y
  have hn : n = X.dim := by
    set Φ := χ.symm.trans c₁.e with hΦ
    have h0 : (0 : Fin n → ℂ) ∈ Φ.source := by
      refine ⟨?_, ?_⟩
      · rw [← hχy]
        exact χ.map_source hyχ
      · show χ.symm 0 ∈ c₁.e.source
        rw [← hχy, χ.left_inv hyχ]
        exact hc₁
    have h0t : (0 : Fin n → ℂ) ∈ χ.target := h0.1
    have h1 : DifferentiableAt ℂ Φ 0 := by
      rw [differentiableAt_euclidean]
      intro a
      have hev : (fun u => Φ u a) =ᶠ[𝓝 0]
          fun u => valAt' (ch₀.symm u).1 (j ''ᵁ c₁.U) ((j.appIso c₁.U).inv.hom (c₁.x a)) := by
        filter_upwards [Φ.open_source.mem_nhds h0] with u hu
        have hs : χ.symm u ∈ c₁.e.source := hu.2
        show c₁.e (χ.symm u) a = _
        rw [c₁.apply_eq _ hs a, ev_eq_valAt'_cxOf e σ hj _ _ (c₁.source_subset hs),
          show cxOf e σ hj (χ.symm u) = ch₀.symm u from hχ u hu.1]
      refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
      refine differentiableAt_valAt'_symm hex _ _ h0t.1 ?_
      rw [← hχ 0 h0t]
      exact le_preimage_cxOf e σ hj _ (c₁.source_subset h0.2)
    have h2 : DifferentiableAt ℂ Φ.symm (Φ 0) := by
      have hB : IsOpen Φ.target := Φ.open_target
      have hΦ0 : Φ 0 ∈ Φ.target := Φ.map_source h0
      have hsub : Φ.target ⊆ c₁.e.target := fun w hw => hw.1
      have hmaps : Set.MapsTo (fun w => κ (c₁.e.symm w)) Φ.target ch₀.source := fun w hw => hw.2.2
      have hhol : IsHolTo Φ.target (fun w => (κ (c₁.e.symm w)).1) := by
        intro U f
        have hset : {b ∈ Φ.target | ⊤ ≤ (κ (c₁.e.symm b)).1 ⁻¹ᵁ U} =
            Φ.target ∩ c₁.e.symm ⁻¹' ptsIn X.str (σ.comp e.toRingHom) (j ⁻¹ᵁ U) := rfl
        refine ⟨?_, ?_⟩
        · rw [hset]
          exact (c₁.e.continuousOn_symm.mono hsub).isOpen_inter_preimage hB (isOpen_ptsIn _)
        · rw [hset]
          refine ((c₁.holo (j ⁻¹ᵁ U) ((j.app U).hom f)).mono fun w hw => ⟨hsub hw.1, hw.2⟩).congr
            fun w _ => ?_
          exact valR_comp (c₁.e.symm w).1 j U f
      rw [differentiableAt_pi]
      intro k
      have hd := (hex.2.1 k (ReciprocityTheory.L2DbarEstimates.V X.dim) Φ.target (fun w => κ (c₁.e.symm w)) hB hhol hmaps).differentiableAt
        (hB.mem_nhds hΦ0)
      exact hd
    have := finrank_eq_of_differentiableAt Φ h0 h1 h2
    simpa [finrank_euclideanSpace_fin] using this
  subst hn
  have hr1 : 0 < min r 1 := lt_min hr one_pos
  set r' : ℝ := min r 1 / 2 with hr'
  have hr'0 : 0 < r' := half_pos hr1
  have hr'r : r' < min r 1 := half_lt_self hr1
  have hr'c : (r' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr'0.ne'
  let L : (Fin X.dim → ℂ) ≃L[ℂ] ReciprocityTheory.L2DbarEstimates.V X.dim :=
    (ContinuousLinearEquiv.smulLeft (Units.mk0 ((r' : ℂ)⁻¹) (inv_ne_zero hr'c))).trans
      (EuclideanSpace.equiv (Fin X.dim) ℂ).symm
  have hL : ∀ u k, (L u).ofLp k = (r' : ℂ)⁻¹ * u k := by
    intro u k
    simp [L]
  let ch := (χ.trans (OpenPartialHomeomorph.ofSet (Metric.ball (0 : Fin X.dim → ℂ) r') Metric.isOpen_ball)).trans
    L.toHomeomorph.toOpenPartialHomeomorph
  have hchs : ∀ v, ch.symm v = χ.symm (L.symm v) := fun v => rfl
  have hch : ∀ z, ch z = L (χ z) := fun z => rfl
  have hsrc : ∀ z ∈ ch.source, z ∈ χ.source ∧ χ z ∈ Metric.ball (0 : Fin X.dim → ℂ) r' := fun z hz => hz.1
  have htgt : ∀ v ∈ ch.target, L.symm v ∈ χ.target := fun v hv => hv.2.2
  refine ⟨rfl, r', ch, hr'0, hr'r.trans_le (min_le_left _ _), hr'r.trans_le (min_le_right _ _), ?_,
    ⟨⟨hyχ, ?_⟩, trivial⟩, ?_, ?_, ?_⟩
  · intro W f v hv
    have hopen : IsOpen (ch.target ∩ ch.symm ⁻¹' ptsIn X.str (σ.comp e.toRingHom) W) :=
      ch.continuousOn_symm.isOpen_inter_preimage ch.open_target (isOpen_ptsIn W)
    refine DifferentiableAt.differentiableWithinAt ?_
    have hev : (ev X.str (σ.comp e.toRingHom) W f ∘ ch.symm) =ᶠ[𝓝 v]
        fun w => valAt' (ch₀.symm (L.symm w)).1 (j ''ᵁ W) ((j.appIso W).inv.hom f) := by
      filter_upwards [hopen.mem_nhds hv] with w hw
      rw [Function.comp_apply, ev_eq_valAt'_cxOf e σ hj W f hw.2, hchs,
        show cxOf e σ hj (χ.symm (L.symm w)) = ch₀.symm (L.symm w) from hχ _ (htgt w hw.1)]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
    have hb := htgt v hv.1
    refine (differentiableAt_valAt'_symm hex (j ''ᵁ W) _ hb.1 ?_).comp v L.symm.differentiableAt
    rw [← hχ _ hb]
    exact le_preimage_cxOf e σ hj W hv.2
  · show χ y ∈ Metric.ball 0 r'
    rw [hχy]
    exact Metric.mem_ball_self hr'0
  · rw [hch, hχy, map_zero]
  · intro z hz
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc, Set.mem_setOf_eq]
    intro k
    rw [hch, hL, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr'0.le]
    have h1 := (hsrc z hz).2
    rw [mem_ball_zero_iff] at h1
    have h2 : ‖χ z k‖ < r' := (norm_le_pi_norm (χ z) k).trans_lt h1
    calc r'⁻¹ * ‖χ z k‖ < r'⁻¹ * r' := mul_lt_mul_of_pos_left h2 (inv_pos.2 hr'0)
      _ = 1 := inv_mul_cancel₀ hr'0.ne'
  · intro z hz
    refine ⟨hz.1.1.2, ?_⟩
    funext k
    show χ z k = _
    rw [hch, hL, Fin.cast_eq_self, ← mul_assoc, mul_inv_cancel₀ hr'c, one_mul]

end GlobalTheory.LieBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSncCoordinatesComplexPointSmoothVariety
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory
namespace SncChart

theorem linearIndependent_fderiv_params (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ)
    [SmoothOfRelativeDimension n p] (c : AlgChart p σ n) (x₀ : CxPts p σ) (hx : x₀ ∈ c.e.source)
    (U : Y.affineOpens) (hy : x₀.1 (IsLocalRing.closedPoint ℂ) ∈ U.1) (m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hR : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) m
      (fun i => Y.presheaf.germ U.1 _ hy (f i))) :
    LinearIndependent ℂ (fun i => fderiv ℂ (CxPts.ev p σ U.1 (f i) ∘ c.e.symm) (c.e x₀)) := by
  rw [Fintype.linearIndependent_iff]
  intro l hl
  by_contra hne
  push_neg at hne
  have hl0 : l ≠ 0 := fun h => by obtain ⟨i, hi⟩ := hne; exact hi (congrFun h i)
  obtain ⟨δ, hc0, hlb, hne'⟩ := GlobalTheory.T.exists_complexPointDerivation_separating_params_charZero k Y p n σ inferInstance x₀ U hy m f hR l hl0
  obtain ⟨v, hv⟩ := GlobalTheory.T.pointDerivation_affineOpen_eq_fderiv_etaleChart k Y p n σ c x₀ hx U (CxPts.mem_ptsIn.2 hy) δ hc0 hlb
  apply hne'
  have := congrArg (fun F => F v) hl
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.zero_apply] at this
  simpa [hv] using this

theorem exists_chart_of_fderiv (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ)
    (c : AlgChart p σ n) (x₀ : CxPts p σ) (hx : x₀ ∈ c.e.source) (W : Y.Opens)
    (hW : x₀ ∈ CxPts.ptsIn p σ W) (a : ℕ) (g : Fin a → Γ(Y, W))
    (h0 : ∀ i, CxPts.ev p σ W (g i) x₀ = 0)
    (hli : LinearIndependent ℂ (fun i => fderiv ℂ (CxPts.ev p σ W (g i) ∘ c.e.symm) (c.e x₀))) :
    ∃ e : OpenPartialHomeomorph (CxPts p σ) (Fin n → ℂ), x₀ ∈ e.source ∧ e.source ⊆ CxPts.ptsIn p σ W ∧
      e x₀ = 0 ∧ (∀ j, HolAlong e.source fun x => e x j) ∧ IsHolTo e.target (fun z => (e.symm z).1) ∧
      ∀ x ∈ e.source, ∀ (j : Fin n) (hj : (j : ℕ) < a), e x j = CxPts.ev p σ W (g ⟨j, hj⟩) x := by
  let c' := c.restr (CxPts.ptsIn p σ W) (CxPts.isOpen_ptsIn W)
  have hx' : x₀ ∈ c'.e.source := ⟨hx, hW⟩
  let G : Fin a → ReciprocityTheory.L2DbarEstimates.V n → ℂ := fun i => CxPts.ev p σ W (g i) ∘ c.e.symm
  have hv0 : c.e x₀ ∈ c'.e.target := c'.e.map_source hx'
  have hG : ∀ i, DifferentiableOn ℂ (G i) c'.e.target := fun i =>
    (c.holo W (g i)).mono (fun v hv => ⟨hv.1, hv.2⟩)
  have hG0 : ∀ i, G i (c.e x₀) = 0 := by
    intro i
    simp only [G, Function.comp_apply, c.e.left_inv hx, h0]
  obtain ⟨ψ, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.complete_holomorphic_coordinates_independent_differentials n a (c.e x₀) c'.e.target G c'.e.open_target hv0 hG hG0 hli
  obtain ⟨hh, hs⟩ := GlobalTheory.T.etaleChart_holomorphic_coordinate_change k Y p n σ c' ψ h4 h5
  refine ⟨c'.e.trans ψ, ⟨hx', h1⟩, fun x hx => hx.1.2, h3, hh, hs, fun x hx j hj => ?_⟩
  have := h6 _ hx.2 j hj
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply] at this ⊢
  refine this.trans ?_
  simp only [G, Function.comp_apply]
  exact congrArg _ (c'.e.left_inv hx.1)

theorem exists_coords : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (D : TopologicalSpace.Closeds Y) (σ : k →+* ℂ), SmoothOfRelativeDimension n p → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal D) → ∀ x₀ : CxPts p σ, ∃ (a : ℕ) (e : OpenPartialHomeomorph (CxPts p σ) (Fin n → ℂ)), x₀ ∈ e.source ∧ e x₀ = 0 ∧ (∀ j, HolAlong e.source fun x => e x j) ∧ IsHolTo e.target (fun z => (e.symm z).1) ∧ ∀ x ∈ e.source, (x.1 (IsLocalRing.closedPoint ℂ) ∉ D ↔ ∀ j : Fin n, (j : ℕ) < a → e x j ≠ 0) := by
  intro k _ _ Y p n D σ hsm hsnc x₀
  haveI := hsm
  obtain ⟨-, U, hy, m, f, J, hR, hD⟩ := hsnc (x₀.1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := n) (p := p) (σ := σ) x₀
  have hli := linearIndependent_fderiv_params k Y p n σ c x₀ hc U hy m f hR
  let ix : Fin J.card → Fin m := fun i => (J.equivFin.symm i).1
  have hix : Function.Injective ix := fun i j h => J.equivFin.symm.injective (Subtype.ext h)
  have hxU : x₀ ∈ CxPts.ptsIn p σ U.1 := CxPts.mem_ptsIn.2 hy
  have h0 : ∀ i, CxPts.ev p σ U.1 (f (ix i)) x₀ = 0 := by
    intro i
    by_contra hne
    have hb := CxPts.mem_ptsIn.1 ((CxPts.mem_ptsIn_basicOpen hxU (f (ix i))).2 hne)
    rw [Scheme.mem_basicOpen _ _ _ hy] at hb
    have hmem : Y.presheaf.germ U.1 _ hy (f (ix i)) ∈ IsLocalRing.maximalIdeal _ := by
      rw [← hR.1]; exact Ideal.subset_span ⟨ix i, rfl⟩
    exact hmem hb
  have hli' := hli.comp ix hix
  have hcard : J.card ≤ n := by
    have := hli'.fintype_card_le_finrank
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ReciprocityTheory.L2DbarEstimates.V n) (F' := ℂ)).finrank_eq,
      Module.finrank_linearMap, Module.finrank_self, _root_.mul_one] at this
    simpa [ReciprocityTheory.L2DbarEstimates.V] using this
  obtain ⟨e, hx0, hsub, he0, hhol, hsymm, hev⟩ :=
    exists_chart_of_fderiv k Y p n σ c x₀ hc U.1 hxU J.card (fun i => f (ix i)) h0 hli'
  refine ⟨J.card, e, hx0, he0, hhol, hsymm, fun x hx => ?_⟩
  rw [GlobalTheory.T.complexPoint_mem_closed_iff_factor_vanishes k Y p σ D U m f J hD x (hsub hx)]
  constructor
  · intro h j hj he
    exact h ⟨ix ⟨j, hj⟩, (J.equivFin.symm _).2, by rw [← hev x hx j hj]; exact he⟩
  · rintro h ⟨i, hi, hi0⟩
    have ht : ix (J.equivFin ⟨i, hi⟩) = i := by simp [ix]
    have hlt : ((J.equivFin ⟨i, hi⟩ : Fin J.card) : ℕ) < n := lt_of_lt_of_le (Fin.isLt _) hcard
    refine h ⟨_, hlt⟩ (J.equivFin ⟨i, hi⟩).isLt ?_
    rw [hev x hx ⟨_, hlt⟩ (J.equivFin ⟨i, hi⟩).isLt]
    simpa [ht] using hi0

end SncChart
end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpecTensorToPullbackSectionsCompat
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory

theorem fromSpec_appLE_self_top {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) (e : ⊤ ≤ hW.fromSpec ⁻¹ᵁ W) :
    hW.fromSpec.appLE W ⊤ e = (Scheme.ΓSpecIso Γ(Y, W)).inv := by
  rw [Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  rw [show (eqToHom hW.fromSpec_preimage_self).op ≫ (homOfLE e).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id, Category.comp_id]

theorem appLE_SpecMap_comp_fromSpec_hom {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) {S : CommRingCat.{0}}
    (φ : Γ(Y, W) ⟶ S) (h : ⊤ ≤ (Spec.map φ ≫ hW.fromSpec) ⁻¹ᵁ W) :
    (Spec.map φ ≫ hW.fromSpec).appLE W ⊤ h ≫ (Scheme.ΓSpecIso S).hom = φ := by
  have e1 : (⊤ : (Spec Γ(Y, W)).Opens) ≤ hW.fromSpec ⁻¹ᵁ W := by simp
  have e2 : (⊤ : (Spec S).Opens) ≤ Spec.map φ ⁻¹ᵁ ⊤ := by simp
  have e3 : (Spec.map φ).appLE ⊤ ⊤ e2 = (Spec.map φ).appTop := (Spec.map φ).appLE_eq_app
  have e4 := Scheme.Hom.appLE_comp_appLE (Spec.map φ) hW.fromSpec W ⊤ ⊤ e1 e2
  rw [← e4, fromSpec_appLE_self_top, e3, Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

theorem appLE_SpecMap_comp_fromSpec {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) {S : CommRingCat.{0}}
    (φ : Γ(Y, W) ⟶ S) (h : ⊤ ≤ (Spec.map φ ≫ hW.fromSpec) ⁻¹ᵁ W) (c : Γ(Y, W)) :
    (Scheme.ΓSpecIso S).hom.hom (((Spec.map φ ≫ hW.fromSpec).appLE W ⊤ h).hom c) = φ.hom c := by
  rw [← CommRingCat.comp_apply, appLE_SpecMap_comp_fromSpec_hom]

theorem specTensor_to_pullback : ∀ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) {R : Type} [CommRing R] (ξ : Sp R ⟶ X) (U : X.affineOpens) (hle : ⊤ ≤ ξ ⁻¹ᵁ (U : X.Opens)) (W : Y'.affineOpens) (hW : (W : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens)), letI := (ρ.appLE U W hW).hom.toAlgebra; letI := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra; ∃ (κ : Spec (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R)) ⟶ pullback ξ ρ) (hκ : ⊤ ≤ (κ ≫ pullback.snd ξ ρ) ⁻¹ᵁ (W : Y'.Opens)), (∀ c : Γ(Y', W), (Scheme.ΓSpecIso _).hom.hom (((κ ≫ pullback.snd ξ ρ).appLE W ⊤ hκ).hom c) = c ⊗ₜ[Γ(X, U)] (1 : R)) ∧ ∀ r : R, (Scheme.ΓSpecIso _).hom.hom (κ.appTop.hom ((pullback.fst ξ ρ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = (1 : Γ(Y', W)) ⊗ₜ[Γ(X, U)] r := by
  intro X Y' ρ R _ ξ U hle W hW
  letI := (ρ.appLE U W hW).hom.toAlgebra
  letI := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra
  let incL : Γ(Y', W) →+* Γ(Y', W) ⊗[Γ(X, U)] R := Algebra.TensorProduct.includeLeftRingHom
  let incR : R →ₐ[Γ(X, U)] Γ(Y', W) ⊗[Γ(X, U)] R := Algebra.TensorProduct.includeRight
  have hξ : Spec.map (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) ≫ U.2.fromSpec = ξ := by
    rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec ξ U.2 (isAffineOpen_top _) hle,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]
  have hρ : W.2.fromSpec ≫ ρ = Spec.map (ρ.appLE U W hW) ≫ U.2.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec ρ U.2 W.2 hW).symm
  have hring : (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom) ≫ CommRingCat.ofHom incR.toRingHom =
      ρ.appLE U W hW ≫ CommRingCat.ofHom incL := by
    ext b
    exact (incR.commutes b).trans ((Algebra.TensorProduct.includeLeft (R := Γ(X, U)) (S := Γ(X, U))
      (A := Γ(Y', W)) (B := R)).commutes b).symm
  have hw : Spec.map (CommRingCat.ofHom incR.toRingHom) ≫ ξ =
      (Spec.map (CommRingCat.ofHom incL) ≫ W.2.fromSpec) ≫ ρ := by
    refine (congrArg (Spec.map (CommRingCat.ofHom incR.toRingHom) ≫ ·) hξ.symm).trans ?_
    rw [Category.assoc, hρ, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hring]
  let κ := pullback.lift _ _ hw
  have hsnd : κ ≫ pullback.snd ξ ρ = Spec.map (CommRingCat.ofHom incL) ≫ W.2.fromSpec := pullback.lift_snd _ _ _
  have hfst : κ ≫ pullback.fst ξ ρ = Spec.map (CommRingCat.ofHom incR.toRingHom) := pullback.lift_fst _ _ _
  have hκ : ⊤ ≤ (κ ≫ pullback.snd ξ ρ) ⁻¹ᵁ (W : Y'.Opens) := by
    rw [hsnd]
    intro x _
    show (Spec.map (CommRingCat.ofHom incL) ≫ W.2.fromSpec) x ∈ (W : Set Y')
    rw [Scheme.Hom.comp_apply, ← W.2.range_fromSpec]
    exact ⟨_, rfl⟩
  refine ⟨κ, hκ, fun c => ?_, fun r => ?_⟩
  · have key : ∀ (f : Spec (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R)) ⟶ Y')
        (_ : f = Spec.map (CommRingCat.ofHom incL) ≫ W.2.fromSpec) (h' : ⊤ ≤ f ⁻¹ᵁ (W : Y'.Opens)),
        (Scheme.ΓSpecIso _).hom.hom ((f.appLE W ⊤ h').hom c) = c ⊗ₜ[Γ(X, U)] (1 : R) := by
      rintro f rfl h'
      exact appLE_SpecMap_comp_fromSpec W.2 (CommRingCat.ofHom incL) h' c
    exact key _ hsnd hκ
  · rw [← CommRingCat.comp_apply (pullback.fst ξ ρ).appTop κ.appTop, ← Scheme.Hom.comp_appTop, hfst,
      ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyConnectedComponentGenericFibre
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.CompOfVar

theorem exists_var_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F), SmoothOfRelativeDimension Dw.dim (genStr Z) → ∀ (Y : Var F) (π : Y.X ⟶ gen Z), π ≫ genStr Z ≫ spMap e.toRingHom = Y.str → ∃ (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j ∧ j ≫ genStr Z ≫ spMap e.toRingHom = X.str ∧ Set.range π ⊆ Set.range j := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e hsm Y π hπ
  have hS : Smooth (genStr Z) := SmoothOfRelativeDimension.smooth Dw.dim _
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  have : CompactSpace (gen Z) := QuasiCompact.compactSpace_of_compactSpace (genStr Z)
  have : IsNoetherian (gen Z) := {}
  have hcc := fun z : gen Z => PtComp.connectedComponent_mem
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (fun W hW W' hW' => PtComp.disjoint_of_smooth (genStr Z) hS W W' hW hW') z
  let z : gen Z := π (genericPoint Y.X)
  let V : (gen Z).Opens := ⟨connectedComponent z, (hcc z).2⟩
  have hred : IsReduced (gen Z) := by
    have := GlobalTheory.isNormalScheme_of_smooth (genStr Z)
    exact GlobalTheory.IsNormalScheme.isReduced
  have : CharZero F := e.toRingHom.charZero
  have : IsIso (spMap e.toRingHom) :=
    inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  have hproj : IsProjOver (genStr Z ≫ spMap e.toRingHom) := GlobalTheory.GenFibreComp.isProjOver_comp_equiv e _
    ((GlobalTheory.ProjSpace.points_and_stability O 0).2.2.1 c.F β Z.X Z.s Z.proj)
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace (hcc z).1.1
  have : IsIntegral V.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hcl : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact isClosed_connectedComponent)
  have hp : IsProjOver (V.ι ≫ genStr Z ≫ spMap e.toRingHom) :=
    (GlobalTheory.ProjSpace.points_and_stability F 0).2.2.2.1 _ _ _ _ hcl hproj
  have hsd : SmoothOfRelativeDimension Dw.dim (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := by
    have h : SmoothOfRelativeDimension (0 + (Dw.dim + 0)) (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := inferInstance
    simpa using h
  have hr : Set.range π ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact (isPreconnected_range π.continuous).subset_connectedComponent ⟨_, rfl⟩
  let g : Y.X ⟶ V.toScheme := IsOpenImmersion.lift V.ι π hr
  have hg : g ≫ V.ι = π := IsOpenImmersion.lift_fac _ _ _
  have : Smooth (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := SmoothOfRelativeDimension.smooth Dw.dim _
  have : GlobalTheory.IsNormalScheme V.toScheme := GlobalTheory.ModifSections.isNormalScheme_of_smooth (V.ι ≫ genStr Z ≫ spMap e.toRingHom)
  have : GeometricallyConnected (V.ι ≫ genStr Z ≫ spMap e.toRingHom) := by
    refine GlobalTheory.GeomConnFn.geometricallyConnected_of_locallyOfFiniteType _ ?_
    exact GlobalTheory.T.algebraicConstants_descend_to_normalIntegralScheme F V.toScheme Y.X _ Y.str g (by rw [reassoc_of% hg, hπ])
      (GlobalTheory.T.geometricallyIntegral_algebraicConstants_mem_range F Y.X Y.str)
  obtain ⟨X, ε, -, hs⟩ := GlobalTheory.ProjVar.Var.exists_iso _ Dw.dim hp
  refine ⟨X, ε.inv ≫ V.ι, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, ← hs, Iso.inv_hom_id_assoc]
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ε.inv.surjective.range_eq, Set.image_univ]
    exact hr

end GlobalTheory.CompOfVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellsGlueLocallyClosedPluckerProduct
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

theorem GlobalTheory.FlagEmb.cells_glue : ∀ (O K : Type) [CommRing O] [IsNoetherianRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover β s V α c D → IsPlk β s V α c p0 p h → ∃ (F : Scheme.{0}) (f : F ⟶ P) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)), IsImmersion f ∧ (∀ b w, IsOpenImmersion (i b w)) ∧ (∀ b w, i b w ≫ f = h b w) ∧ ∀ x : F, ∃ b w, x ∈ Set.range (i b w) := by
  intro O K _ _ _ β X s T _ m M B _ V α c D P p0 p h hs hX hC hP
  have hLN : ∀ {Y : Scheme.{0}} (g : Y ⟶ Sp O), IsProjOver g → IsLocallyNoetherian Y := by
    intro Y g hg
    obtain ⟨N, ι, _, rfl⟩ := hg
    exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ PSpace.str O N)
  haveI : IsLocallyNoetherian X := hLN s hs
  haveI : IsLocallyNoetherian P := hLN _ hP.proj
  have hW : ∀ b w, ∃ W, IsCellOpen p0 p (V b) (D b) w W := fun b w =>
    GlobalTheory.FlagEmb.CellOpen.exists_isCellOpen O X P T m M p0 p (V b) (D b) w
  choose W hW using hW
  have hcl := fun b w => GlobalTheory.T.flagCell_isClosed_in_leadingMinor_open O K β X s T m M B V α c D P p0 p h hC hP inferInstance hs b w (W b w) (hW b w)
  choose h' hh' hci using hcl
  have hred : ∀ b, AlgebraicGeometry.IsReduced (Sp (CR m (V b))) := by
    intro b
    have hn := (GlobalTheory.FlagEmb.cell_smooth_normal X T m (V b) hX).2
    haveI := fun x => (hn x).1
    exact isReduced_of_isReduced_stalk _
  let ι := B × Pm m
  haveI : Finite (Pm m) := Pi.finite
  haveI : ∀ a : ι, IsAffine (Sp (CR m (V a.1))) := fun a => inferInstance
  haveI : ∀ a : ι, AlgebraicGeometry.IsReduced (Sp (CR m (V a.1))) := fun a => hred a.1
  obtain ⟨F, f, i, hf, hio, hcomp, hcov⟩ := GlobalTheory.MemberGlue.exists_immersion_of_closed_pieces P ι
    (fun a => Sp (CR m (V a.1))) (fun a => h a.1 a.2) (fun a => W a.1 a.2) (fun a => h' a.1 a.2) inferInstance
    (fun a => hh' a.1 a.2) (fun a => hci a.1 a.2)
    (fun a a' => GlobalTheory.FlagEmb.Overlap.range_inter_cellOpen_subset O K β X s T m M B V α c D P p0 p h hC hP a.1 a.2
      (W a.1 a.2) (hW a.1 a.2) a'.1 a'.2)
  refine ⟨F, f, fun b w => i (b, w), hf, fun b w => hio (b, w), fun b w => hcomp (b, w), fun x => ?_⟩
  obtain ⟨a, ha⟩ := hcov x
  exact ⟨a.1, a.2, ha⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FurtherPlacesGroupContainsChartLevelsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.furtherPlaces_group_contains_chart_levels : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, GlobalTheory.Mem.Col2.AdT.ChiFin I l Z (K β).lev) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∃ (W : ∀ v, v ∈ Q → Subgroup (GL (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] v.adicCompletion (I.rec7 l Z).host.F))) (ψ : (∀ v : Q, ↥(W v.1 v.2)) →* ℂˣ), (∀ v hv, W v hv ≤ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v Lb0) ∧ (∀ v hv, ∃ n : ℕ, 0 < n ∧ ∀ x, Formalism.L2.Herm.InPrinc (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) v n Lb0 x → x ∈ W v hv) ∧ (∀ β v hv, (K β).lev.Uloc v ≤ (W v hv).map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom) ∧ (∀ β v hv, ((((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom).subgroupOf (W v hv)).FiniteIndex) ∧ (∀ β (κ : (K β).lev.U) (z : ∀ v : Q, ↥(W v.1 v.2)), (∀ v : Q, reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ (z v).1 = bc (prV (E := (I.rec7 l Z).host.E) v.1) κ.1) → (∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ψ z) := by
  first | exact @GlobalTheory.Mem.Col2.TC.further_group_charts | exact GlobalTheory.Mem.Col2.TC.further_group_charts | (intros; apply GlobalTheory.Mem.Col2.TC.further_group_charts <;> assumption)
end

