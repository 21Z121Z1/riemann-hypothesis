import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PremisesOfProper
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliFiniteSurjectiveOverGenericFamily
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0581

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcOffBoundaryDescendsToModuliLocalizationStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_off_boundary_descends_to_moduli_localization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)), IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → ∀ u₀ ∈ Metric.ball (0 : ℂ) r, u₀ ≠ 0 → ∃ (R : Type) (_ : CommRing R) (xR : Sp R ⟶ Xo.X) (vR : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)) (ev : ℂ → (R →+* ℂ)) (V : Set ℂ), IsOpen V ∧ u₀ ∈ V ∧ (∀ t, DifferentiableOn ℂ (fun u => ev u t) V) ∧ ∀ u ∈ V, (y u).x = spMap (show R →+* CAt σ from ev u) ≫ xR ∧ ∀ τ i, (y u).u τ i = spMap (dualMap (show R →+* CAt σ from ev u)) ≫ vR τ i := by
  first | exact @GlobalTheory.ShFam.BdArc.arc_descends_to_moduli | exact GlobalTheory.ShFam.BdArc.arc_descends_to_moduli | (intros; apply GlobalTheory.ShFam.BdArc.arc_descends_to_moduli <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcsOnFlowLinesOfAnalyticModelOnOrbitStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcs_on_flow_lines_of_analytic_model_on_orbit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (Λ : GtAn₀ aC), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → letI := H.starRing; ∀ (gam : (Uw.F.Di (Uw.ik k)).La ≃ₗ[𝓞 E] Λ.A.La) (ξ : Module.Dual ℤ Λ.A.X), OnOrbit Uw k ξ' x Λ.A gam ξ → ξ ≠ 0 → Module.finrank (𝓞 E) Λ.A.X = 1 → (∀ v, Λ.Lifts (aC.eta v) (gam (Uw.F.t (Uw.ik k) v))) → (∀ v, Λ.Lifts (aC.etaA v) (gam (Uw.F.t (Uw.ik k) v))) → ∀ (O : Type) [CommRing O] (β : O →+* c.F), FlowTie Uw (aC.restrict β) k ξ' x := by
  first | exact @GlobalTheory.CuspFrom.flowTie_of_onOrbit | exact GlobalTheory.CuspFrom.flowTie_of_onOrbit | (intros; apply GlobalTheory.CuspFrom.flowTie_of_onOrbit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasLocalRingPoints
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.Spez

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Flags

variable {X : Scheme.{0}} {t : SAB H X} {R S : Type} [CommRing R] [CommRing S] {ty : (E →+* ℂ) → Finset ℕ}

theorem sameFlag_bc (φ : R →+* S) {x : Sp R ⟶ X} {u u' : Vecs Dw t R} (h : SameFlag ty t x u u') :
    SameFlag ty t (spMap φ ≫ x) (u.bc φ) (u'.bc φ) := fun σ j hj i hi => by
  obtain ⟨cf, h1, h2⟩ := h σ j hj i hi
  exact ⟨fun l => φ (cf l), fun l hl => by simp [h1 l hl], comb_bc φ h2⟩

theorem sameFlag_of_bc {l : Level H} {c : Coeff l} {g : c.F →+* R} {φ : R →+* S} (hφ : Function.Injective φ)
    {x : Sp R ⟶ X} {u u' : Vecs Dw t R} (hu : LocM.IsFrame t g x u) (hu' : LocM.IsFrame t g x u')
    (h : SameFlag ty t (spMap φ ≫ x) (u.bc φ) (u'.bc φ)) : SameFlag ty t x u u' := fun σ j hj i hi => by
  obtain ⟨cf, hcf, -⟩ := hu.exists_comb hu' σ i
  obtain ⟨cf', h1, h2⟩ := h σ j hj i hi
  have e := ((GlobalTheory.LocM.isFrame_bc E H Dw l c _ t _ _ _ φ _ _ hu).exists_comb
    (GlobalTheory.LocM.isFrame_bc E H Dw l c _ t _ _ _ φ _ _ hu') σ i).unique (comb_bc φ hcf) h2
  exact ⟨cf, fun m hm => hφ ((congrFun e m).trans ((h1 m hm).trans (map_zero φ).symm)), hcf⟩

end Flags

section Atl

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F} {M : Model Xo c V.subtype}
  {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ} {A : Atlas M π ty} {K : Type} [Field K]

theorem sameFlag_of_flagAt {w : Sp K ⟶ X} {u u' : Vecs Dw M.t K} (h : A.FlagAt w u) (h' : A.FlagAt w u') :
    SameFlag ty M.t (w ≫ π) u u' := by
  obtain ⟨U, rfl⟩ := h.exists_up
  obtain ⟨U', rfl⟩ := h'.exists_up
  exact (sameFlag_up_iff U U').2 fun σ j hj => (h'.initSpan_eq h σ hj).le

theorem isFrame_of_flagAt {w : Sp K ⟶ X} {u : Vecs Dw M.t K} (h : A.FlagAt w u) {a : A.ch.ι} {φ : A.ch.R a →+* K}
    (e : spMap φ ≫ A.ch.χ a = w) : LocM.IsFrame M.t (φ.comp (A.alg a)) (w ≫ π) u := by
  obtain ⟨a', φ', e', hf, -⟩ := h
  rwa [A.alg_eq e e']

end Atl

theorem ext_of_field {Y : Scheme.{0}} [Y.IsSeparated] {R K : Type} [CommRing R] [Field K] {φ : R →+* K}
    (hφ : Function.Injective φ) {x x' : Sp R ⟶ Y} (h : spMap φ ≫ x = spMap φ ≫ x') : x = x' := by
  have : IsDomain R := hφ.isDomain φ
  have : IsDominant (spMap φ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2
    (by rw [(RingHom.injective_iff_ker_eq_bot φ).1 hφ]; exact bot_le)⟩
  exact ext_of_isDominant (spMap φ) h

theorem flagAt_specialise {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'}
    {V : ValuationSubring c.F} {V' : ValuationSubring c'.F} {M : Model Xo c V.subtype} {M' : Model Xo' c' V'.subtype}
    {X X' : Scheme.{0}} {π : X ⟶ M.X} {π' : X' ⟶ M'.X} {ty ty' : (E →+* ℂ) → Finset ℕ} {A : Atlas M π ty}
    {A' : Atlas M' π' ty'} {τ : M'.X ⟶ M.X} (mu : SABMap M'.t M.t τ) (hc : c.F ≤ c'.F) (hty : ∀ σ, ty σ ⊆ ty' σ)
    {R K k : Type} [CommRing R] [Field K] [Field k] {φ : R →+* K} (hφ : Function.Injective φ) (ψ : R →+* k)
    {z₁ : Sp R ⟶ X'} {z₂ : Sp R ⟶ X} (hR : z₂ ≫ π = (z₁ ≫ π') ≫ τ) {a₁ : A'.ch.ι} {ρ₁ : A'.ch.R a₁ →+* R}
    (e₁ : spMap ρ₁ ≫ A'.ch.χ a₁ = z₁) {a₂ : A.ch.ι} {ρ₂ : A.ch.R a₂ →+* R} (e₂ : spMap ρ₂ ≫ A.ch.χ a₂ = z₂)
    (hg : ρ₂.comp (A.alg a₂) = (ρ₁.comp (A'.alg a₁)).comp (IntermediateField.inclusion hc).toRingHom)
    {u : Vecs Dw M'.t K} (h₁ : A'.FlagAt (spMap φ ≫ z₁) u)
    (h₂ : A.FlagAt (spMap φ ≫ z₂) fun σ j => u σ j ≫ mu.φ) :
    A'.FlagAt (spMap ψ ≫ z₁) ((A'.fr a₁).bc (ψ.comp ρ₁)) ∧
      A.FlagAt (spMap ψ ≫ z₂) fun σ j => (A'.fr a₁).bc (ψ.comp ρ₁) σ j ≫ mu.φ := by
  have f₁ := (A'.isFrame_bc e₁).push hc mu
  rw [← hg, ← hR] at f₁
  have f₂ := A.isFrame_bc e₂
  have bc : ∀ {S : Type} [CommRing S] (χ : R →+* S),
      Vecs.bc (Dw := Dw) (t := M.t) χ (fun σ j => (A'.fr a₁).bc ρ₁ σ j ≫ mu.φ) =
        fun σ j => (A'.fr a₁).bc (χ.comp ρ₁) σ j ≫ mu.φ := fun χ => by
    rw [← Vecs.bc_bc]
    funext σ j
    exact (Category.assoc _ _ _).symm
  have c₁ : ∀ {S : Type} [CommRing S] (χ : R →+* S), spMap (χ.comp ρ₁) ≫ A'.ch.χ a₁ = spMap χ ≫ z₁ :=
    fun χ => by rw [← spMap_comp', Category.assoc, e₁]
  have c₂ : ∀ {S : Type} [CommRing S] (χ : R →+* S), spMap (χ.comp ρ₂) ≫ A.ch.χ a₂ = spMap χ ≫ z₂ :=
    fun χ => by rw [← spMap_comp', Category.assoc, e₂]
  have key : SameFlag ty M.t (z₂ ≫ π) ((A.fr a₂).bc ρ₂) fun σ j => (A'.fr a₁).bc ρ₁ σ j ≫ mu.φ := by
    refine sameFlag_of_bc hφ f₂ f₁ ?_
    rw [Vecs.bc_bc, bc, ← Category.assoc]
    have g₁ := A'.isFrame_bc (c₁ φ)
    have g₂ := A.isFrame_bc (c₂ φ)
    have s₁ := ((sameFlag_of_flagAt h₁ (A'.flagAt_fr (c₁ φ))).push mu
      (fun σ j => ((isFrame_of_flagAt h₁ (c₁ φ)).1 σ j).1) fun σ j => (g₁.1 σ j).1).mono hty
    have hK : ((spMap φ ≫ z₁) ≫ π') ≫ τ = (spMap φ ≫ z₂) ≫ π := by simp only [Category.assoc, hR]
    rw [hK] at s₁
    exact SameFlag.trans (fun σ j => (g₂.1 σ j).1)
      (fun σ j => (g₂.exists_comb (isFrame_of_flagAt h₂ (c₂ φ)) σ j).exists)
      (sameFlag_of_flagAt (A.flagAt_fr (c₂ φ)) h₂) s₁
  have r₁ := GlobalTheory.LocM.isFrame_bc E H Dw l c _ M.t _ _ _ ψ _ _ f₁
  have r₂ := sameFlag_bc ψ key
  rw [bc, ← Category.assoc] at r₁ r₂
  rw [Vecs.bc_bc] at r₂
  exact ⟨A'.flagAt_fr (c₁ ψ), a₂, ψ.comp ρ₂, c₂ ψ, r₁, r₂⟩

theorem natTo_specialise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty) (Z : Mdl Y i₀) (R K k : Type) [CommRing R] [IsLocalRing R] [Field K] [Field k] (φ : R →+* K) (ψ : R →+* k) (z : Sp R ⟶ Z.X) (z' : Sp R ⟶ X), i.c.F ≤ Z.i.c.F → (∀ σ, ty σ ⊆ Z.ty σ) → Function.Injective φ → z (IsLocalRing.closedPoint R) ∈ Z.opn → NatTo Z A (spMap φ ≫ z) (spMap φ ≫ z') → NatTo Z A (spMap ψ ≫ z) (spMap ψ ≫ z') := by
  intro E _ _ _ H Dw Xo p W Y i₀ i X π ty A Z R K k _ _ _ _ φ ψ z z' hc hty hφ hz ⟨τ, mu, u, htr, hK, h₁, h₂⟩
  obtain ⟨b, π', r, hb, hπ₁, hπ₂, -, hj, -⟩ := id htr
  have := projProper _ _ _ (Y i).proj
  have : (Y i).X.IsSeparated := ⟨by rw [← terminal.comp_from (Y i).s]; infer_instance⟩
  have hR : z' ≫ π = (z ≫ Z.π) ≫ τ := ext_of_field hφ (by simpa only [Category.assoc] using hK)
  obtain ⟨a₁, ρ₁, e₁⟩ := (atlasOf Z).ch.exists_fac z (by rw [(atlasOf Z).cover]; exact hz)
  obtain ⟨a₂, ρ₂, e₂⟩ := A.ch.exists_fac z' (by
    obtain ⟨q, hq⟩ := hz
    rw [A.cover]
    exact ⟨r q, ((Scheme.Hom.comp_apply r _ q).symm.trans (congrArg (fun f => f q) hj.symm)).trans
      ((congrArg τ hq).trans (congrArg (fun f => f (IsLocalRing.closedPoint R)) hR.symm))⟩)
  have hs : τ ≫ (Y i).s = (Y Z.i).s ≫ spMap b := by
    rw [← hπ₁, ← hπ₂, Category.assoc, Category.assoc, pullback.condition]
  have hg : ρ₂.comp (A.alg a₂) = (ρ₁.comp ((atlasOf Z).alg a₁)).comp (IntermediateField.inclusion hc).toRingHom := by
    apply coeff_ext (W := W)
    have e : z' ≫ π ≫ (Y i).s = (z ≫ Z.π ≫ (Y Z.i).s) ≫ spMap b := by
      rw [← Category.assoc, hR, Category.assoc, hs]; simp only [Category.assoc]
    rw [← A.affineOpenChart_comp_structure_eq_spMap e₂, e, (atlasOf Z).affineOpenChart_comp_structure_eq_spMap e₁, spMap_comp']
    exact congrArg spMap (RingHom.ext fun x => congrArg (ρ₁.comp ((atlasOf Z).alg a₁)) (Subtype.ext (hb x)))
  obtain ⟨k₁, k₂⟩ := flagAt_specialise (A' := atlasOf Z) mu hc hty hφ ψ hR e₁ e₂ hg h₁ h₂
  exact ⟨τ, mu, _, htr, by simp only [Category.assoc, hR], k₁, k₂⟩

end GlobalTheory.DRFlag.Spez
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasPullbackPreservesStep
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DRFlag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem initSpan_eq_transport {Y : Scheme.{0}} {t : SAB H Y} {K : Type} [Field K] {p p' : Sp K ⟶ Y} (h : p = p')
    {m n : ℕ} (u : Fin m → TanM p t.G) (v : Fin n → TanM p t.G) (u' : Fin m → TanM p' t.G)
    (v' : Fin n → TanM p' t.G) (hu : ∀ i, (tv (u i)).left = (tv (u' i)).left)
    (hv : ∀ i, (tv (v i)).left = (tv (v' i)).left) {j : ℕ} (e : initSpan K u j = initSpan K v j) :
    initSpan K u' j = initSpan K v' j := by
  subst h
  have h1 : u = u' := funext fun i => GlobalTheory.FlagMod.tan_ext_left (hu i)
  have h2 : v = v' := funext fun i => GlobalTheory.FlagMod.tan_ext_left (hv i)
  subst h1 h2
  exact e

theorem IntStep.pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ) (X' : Scheme.{0}) (f : X' ⟶ X) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas M (f ≫ π) ty'), (∀ (K : Type) [Field K] (w : Sp K ⟶ X') (u : Vecs Dw M.t K), A'.FlagAt w u → A.FlagAt (w ≫ f) u) → IntStep A σ k → IntStep A' σ k := by
  intro E _ _ _ H Dw l Xo c V M X π ty A σ k X' f ty' A' hfl hI x
  obtain ⟨U, hU, m, b, hxU, hb⟩ := hI (f x)
  obtain ⟨_, ⟨U', hU', rfl⟩, hx, hle⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ((f ⁻¹ᵁ U : X'.Opens) : Set X') from hxU) (f ⁻¹ᵁ U).isOpen
  have hle' : U' ≤ f ⁻¹ᵁ U := fun y hy => hle hy
  have h0 : ⊤ ≤ (tau hU' ≫ f) ⁻¹ᵁ U := le_preimage_map f hle' (tau_le hU' le_rfl)
  have e0 : spMap (ev (tau hU' ≫ f) U h0) ≫ tau hU ≫ π = tau hU' ≫ f ≫ π := by
    rw [← Category.assoc]
    exact (congrArg (· ≫ π) (spMap_ev (tau hU' ≫ f) hU h0)).trans (Category.assoc _ _ _)
  refine ⟨U', hU', m, basPull (ev (tau hU' ≫ f) U h0) e0 b, hx, ?_⟩
  intro K _ w hw u hu j hj
  have hw' : ⊤ ≤ (w ≫ f) ⁻¹ᵁ U := le_preimage_map f hle' hw
  obtain ⟨U₁, hU₁⟩ := Atlas.FlagAt.exists_up (hfl K w _ hu)
  have key := hb K (w ≫ f) hw' U₁ (hU₁ ▸ hfl K w _ hu) j hj
  have e1 : spMap (ev w U' hw) ≫ tau hU' ≫ f = w ≫ f := by
    rw [← Category.assoc]
    exact congrArg (· ≫ f) (spMap_ev w hU' hw)
  have e2 : ev (w ≫ f) U hw' = (ev w U' hw).comp (ev (tau hU' ≫ f) U h0) :=
    (GlobalTheory.FlagMod.ev_congr e1.symm U hw' (le_preimage_comp _ h0)).trans (ev_spMap _ _ U h0 _)
  refine initSpan_eq_transport (Category.assoc w f π) _ _ _ _ (fun i => ?_) (fun i => ?_) key
  · exact congrFun (congrFun hU₁ σ) i
  · rw [basAt_left b, basAt_left (basPull (ev (tau hU' ≫ f) U h0) e0 b) w hw, basPull_apply, GlobalTheory.FlagMod.tanPull_left, e2, GlobalTheory.FlagMod.dualMap_comp,
      ← spMap_comp', Category.assoc]
    exact Category.assoc _ _ _

end GlobalTheory.DRFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryArcLiftNotConvergesSymmetricDomain
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open scoped CommRingCat.HomTopology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc.Leave

theorem block_of_span_le {N p : ℕ} {M M' : Matrix (Fin N) (Fin N) ℂ} (hM : M.det ≠ 0)
    (h : Submodule.span ℂ (col M' '' {a | (a : ℕ) < p}) ≤ Submodule.span ℂ (col M '' {a | (a : ℕ) < p}))
    (a b : Fin N) (ha : p ≤ a) (hb : (b : ℕ) < p) : (M⁻¹ * M') a b = 0 := by
  let L : (Fin N → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj a).comp (Matrix.mulVecLin M⁻¹)
  have hL : ∀ (P : Matrix (Fin N) (Fin N) ℂ) (d : Fin N), L (col P d) = (M⁻¹ * P) a d := fun _ _ => rfl
  have h1 : Submodule.span ℂ (col M '' {a | (a : ℕ) < p}) ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨d, hd, rfl⟩
    show L (col M d) = 0
    rw [hL, Matrix.nonsing_inv_mul _ hM.isUnit]
    exact Matrix.one_apply_ne fun e => absurd (show (d : ℕ) < p from hd) (by rw [← e]; omega)
  exact (hL M' b).symm.trans (h1 (h (Submodule.subset_span ⟨b, hb, rfl⟩)))

theorem imTop_neBot : imTop.NeBot :=
  Filter.comap_neBot fun t ht => by
    obtain ⟨a, ha⟩ := Filter.nonempty_of_mem ht
    exact ⟨a * Complex.I, by simpa using ha⟩

theorem tendsto_eTwoPi : Tendsto eTwoPi imTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : Tendsto (fun w : ℂ => Real.exp (-(2 * Real.pi * w.im))) imTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop (by positivity) tendsto_comap)
  refine h.congr fun w => ?_
  simp [eTwoPi, Complex.norm_exp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {N : ℕ} {U : Unf Xo c σ N}

theorem x_eq_of_samePos (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (x x' : (U.X k).dom)
    (h : SamePos (U.X k) x.1 x'.1) : (U.un k x).x = (U.un k x').x :=
  GlobalTheory.TrueCx.PointWell.pt_eq_of_block (U := Formalism.L2.PjFree.Unf.ofPj U) hU hσ k x x'
    (fun τ => block_of_span_le (x.2 τ).1 (h τ).ge) fun τ => block_of_span_le (x'.2 τ).1 (h τ).le

theorem isHolTo_ptC (hU : IsUnf U) (k : U.Comp) (s : Frame (U.X k).Ψ N → (U.X k).dom)
    (hs : ∀ x ∈ (U.X k).dom, (s x).1 = x) : IsHolTo (U.X k).dom fun x => GlobalTheory.TrueCx.ptC (U.un k (s x)) := by
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hun⟩ := hU
  choose P hP hP' hx _ using hun k
  let L : Frame (U.X k).Ψ N ≃L[ℂ] (Fin (Module.finrank ℂ (Frame (U.X k).Ψ N)) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp only [Module.finrank_fin_fun])
  have ho : IsOpen (U.X k).dom := ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom _
  have hB := ho.preimage L.symm.continuous
  have h1 := (F.hol (ik k) _ _ (fun b => P (s (L.symm b))) hB ⟨fun b _ => hP' _, fun a =>
    differentiableOn_pi.2 fun i => by
      simp only [hP]
      refine GlobalTheory.TrueCx.TorHolo.differentiableOn_perFr _ (fun b _ => (s _).2) (fun τ a d => ?_) _ _ _
      refine (differentiable_pi.1 (differentiable_pi.1 (differentiable_pi.1 L.symm.differentiable τ) a)
        d).differentiableOn.congr fun b hb => ?_
      rw [hs _ hb]
      rfl⟩).1
  have h2 : IsHolTo (L.symm ⁻¹' (U.X k).dom) fun b => GlobalTheory.TrueCx.ptC (U.un k (s (L.symm b))) := by
    refine GlobalTheory.TrueCx.TorHolo.isHolTo_of_fst _ _ hB _ (fun b => GlobalTheory.TrueCx.ptC_snd _) ?_
    simp only [GlobalTheory.TrueCx.ptC_fst]
    exact LocLift.isHolTo_congr h1 fun b _ => hx _
  refine LocLift.isHolTo_congr (LocLift.isHolTo_comp h2 ho L.differentiableOn fun v hv => ?_) fun v _ => ?_
  · rwa [Set.mem_preimage, L.symm_apply_apply]
  · rw [L.symm_apply_apply]

theorem lift_not_converges : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsBdArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsLift U k y T xx → ∀ x₀ ∈ (U.X k).dom, ∀ x' : ℂ → Frame (U.X k).Ψ N, Tendsto x' imTop (𝓝 x₀) → ¬ ∀ᶠ w in imTop, x' w ∈ (U.X k).dom ∧ SamePos (U.X k) (xx w) (x' w) := by
  classical
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T xx hσ hU ⟨⟨⟨hr, hψ⟩, hxs, hφ⟩, hb0, _⟩ hm hl x₀ hx₀ x' ht hev
  have := isProper_genStr Z
  have := imTop_neBot
  let s : Frame (U.X k).Ψ N → (U.X k).dom := fun v => if h : v ∈ (U.X k).dom then ⟨v, h⟩ else ⟨x₀, hx₀⟩
  have hs : ∀ v (h : v ∈ (U.X k).dom), s v = ⟨v, h⟩ := fun v h => dif_pos h
  let pt : Frame (U.X k).Ψ N → CxPts (genStr Z) σ := fun v =>
    ⟨GlobalTheory.TrueCx.ptC (U.un k (s v)) ≫ Z.jQ, by rw [Category.assoc, Z.jQ_over, GlobalTheory.TrueCx.ptC_snd]⟩
  have hc : ContinuousOn pt (U.X k).dom := GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo
    (LocLift.isHolTo_comp_hom (isHolTo_ptC hU k s fun v h => by rw [hs v h]) Z.jQ)
  have h1 : Tendsto (fun w => pt (x' w)) imTop (𝓝 (pt x₀)) :=
    (hc.continuousAt ((ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain.isOpen_dom _).mem_nhds hx₀)).tendsto.comp ht
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := Metric.mem_ball_self hr
  let q : CxPts (genStr Z) σ := ⟨spMap (ψ 0) ≫ x, by
    rw [Category.assoc, hxs, ← hφ 0 h0, ← Spec.map_comp]; rfl⟩
  have ha : ContinuousAt (fun u => spMap (ψ u) ≫ x) 0 := by
    refine ((GlobalTheory.Points.continuous_comp x).comp
      (GlobalTheory.Points.continuous_specMap (C := ℂ) (CommRingCat.of A))).continuousAt.comp
      (f := fun u => CommRingCat.ofHom (ψ u)) ?_
    refine (CommRingCat.HomTopology.isEmbedding_hom _ _).isInducing.continuousAt_iff.2 (continuousAt_pi.2 fun a => ?_)
    exact ((hψ a).differentiableAt (Metric.isOpen_ball.mem_nhds h0)).continuousAt
  have h2 : Tendsto (fun w => pt (x' w)) imTop (𝓝 q) := by
    refine tendsto_subtype_rng.2 ((ha.tendsto.comp tendsto_eTwoPi).congr' ?_)
    filter_upwards [hev, tendsto_eTwoPi.eventually (Metric.isOpen_ball.mem_nhds h0),
      (tendsto_comap (f := Complex.im)).eventually (eventually_gt_atTop T)] with w hw hb hT
    obtain ⟨hd, he, -⟩ := hl w hT
    have e1 := (hm _ hb (Complex.exp_ne_zero _)).1
    have e2 : GlobalTheory.TrueCx.ptC (U.un k (s (x' w))) = GlobalTheory.TrueCx.ptC (y (eTwoPi w)) := by
      refine pullback.hom_ext ?_ ((GlobalTheory.TrueCx.ptC_snd _).trans (GlobalTheory.TrueCx.ptC_snd _).symm)
      rw [GlobalTheory.TrueCx.ptC_fst, GlobalTheory.TrueCx.ptC_fst, hs _ hw.1]
      exact (x_eq_of_samePos hσ hU k ⟨_, hd⟩ ⟨_, hw.1⟩ hw.2).symm.trans he
    exact e1.symm.trans (congrArg (· ≫ Z.jQ) e2.symm)
  have h3 : (pt x₀).1 = q.1 := congrArg Subtype.val (tendsto_nhds_unique h1 h2)
  refine mem_genBd.1 (hb0 (IsLocalRing.closedPoint ℂ)) ⟨GlobalTheory.TrueCx.ptC (U.un k (s x₀)) (IsLocalRing.closedPoint ℂ), ?_⟩
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans
    (congrArg (fun f : Sp ℂ ⟶ gen Z => f (IsLocalRing.closedPoint ℂ)) h3)

end GlobalTheory.ShFam.BdArc.Leave
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryExtensionIndependentOfModel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.OpenReg

namespace GlobalTheory.CuspFrom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
  [Algebra c.F K]

theorem exists_genPt (Z : Model Xo c β) (φ : c.F →+* V) (hφ : (algebraMap V K).comp φ = algebraMap c.F K)
    (y : FrPt Xo c K) : ∃ χ : Sp V ⟶ gen Z, χ ≫ genStr Z = spMap φ ∧ GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap (algebraMap V K) ≫ χ := by
  haveI := isProper_genStr Z
  obtain ⟨χ, h1, h2⟩ := GlobalTheory.exists_valuativeExtension (genStr Z) (spMap φ) (GlobalTheory.AllWt.ptF y ≫ Z.jQ) (by
    rw [Category.assoc, Z.jQ_over, ← Geo.Tor.spMap_comp, hφ]
    exact pullback.lift_snd _ _ _)
  exact ⟨χ, h2, h1.symm⟩

theorem exists_genIdent (Z : Model Xo c β) {χ : Sp V ⟶ gen Z} {y : FrPt Xo c K}
    (hχ : GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap (algebraMap V K) ≫ χ) {tK : SAB H (Sp K)}
    (mK : SABMap tK Xo.univ.t (GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _)) {t : SAB H (Sp V)} (m : SABMap t Z.t (χ ≫ genι Z)) :
    ∃ (a : SABMap tK t (spMap (algebraMap V K))) (mF : SABMap tK Z.oF.t (GlobalTheory.AllWt.ptF y)),
      mF.φ ≫ Z.m0.toSABMap.φ = mK.φ ∧ mF.φ ≫ Z.m.φ = a.φ ≫ m.φ := by
  obtain ⟨mF, h1⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Z.oF.t tK (pullback.fst _ _) (GlobalTheory.AllWt.ptF y)
    Z.m0.toSABMap mK
  obtain ⟨mJ, h2⟩ := sabComp pullCubComp E H _ _ _ Z.t Z.oF.t tK (Z.jQ ≫ pullback.fst _ _) (GlobalTheory.AllWt.ptF y) Z.m mF
  have hj : GlobalTheory.AllWt.ptF y ≫ Z.jQ ≫ pullback.fst _ _ = spMap (algebraMap V K) ≫ χ ≫ genι Z := by
    rw [← Category.assoc, hχ, Category.assoc]
  obtain ⟨a, h3⟩ := sabCancel pullCubCancel E H _ _ _ Z.t t tK (χ ≫ genι Z) (spMap (algebraMap V K)) m
    (PullbackSections.sabMapCast mJ hj)
  exact ⟨a, mF, h1.symm, by rw [← h2, ← PullbackSections.sabMapCast_φ mJ hj, h3]⟩

variable {O' : Type} [CommRing O'] {β' : O' →+* c.F}

theorem mem_genBd_of_mem_genBd {Z : Model Xo c β} {Z' : Model Xo c β'} {χ : Sp V ⟶ gen Z} {χ' : Sp V ⟶ gen Z'}
    {t t' : SAB H (Sp V)} (m : SABMap t Z.t (χ ≫ genι Z)) (m' : SABMap t' Z'.t (χ' ≫ genι Z'))
    (ψ : SABMap t t' (𝟙 (Sp V))) (p : Sp V) (h : χ' p ∈ genBd Z') : χ p ∈ genBd Z := by
  rw [mem_genBd_iff, ← Scheme.Hom.comp_apply, abLocus_pullback abLocusOne Z.t.semi m.cart.1 p]
  rw [mem_genBd_iff, ← Scheme.Hom.comp_apply, abLocus_pullback abLocusOne Z'.t.semi m'.cart.1 p] at h
  have e := abLocus_pullback abLocusOne t'.semi ψ.cart.1 p
  have e0 : (𝟙 (Sp V)) p = p := rfl
  rw [e0] at e
  exact fun hp => h (e.2 hp)

section Chain

variable {Z : Model Xo c β} {Z' : Model Xo c β'} {x : Sp V ⟶ Z.X} {x' : Sp V ⟶ Z'.X} {t t' : SAB H (Sp V)}
  (m : SABMap t Z.t x) (m' : SABMap t' Z'.t x') (ψ : SABMap t t' (𝟙 (Sp V))) {φ : c.F →+* V}

theorem exists_isEigBasis_chain {τ : E →+* ℂ} {n : ℕ} {v' : Fin n → (Sp (DualNumber V) ⟶ Z'.t.G.left)}
    (h : IsEigBasis Z'.t φ x' τ v') : ∃ v : Fin n → (Sp (DualNumber V) ⟶ t.G.left),
      (∀ i, (v i ≫ ψ.φ) ≫ m'.φ = v' i) ∧ (∀ i, v i ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) ∧
        IsEigBasis Z.t φ x τ (fun i => v i ≫ m.φ) := by
  have h1 : IsEigBasis Z'.t φ (𝟙 _ ≫ x') τ v' := by rwa [Category.id_comp]
  obtain ⟨v₁, hv₁, h₁⟩ := isEigBasis_pull m' h1
  have h2 : IsEigBasis t' φ (𝟙 _ ≫ 𝟙 _) τ v₁ := by rwa [Category.id_comp]
  obtain ⟨v₂, hv₂, h₂⟩ := isEigBasis_pull ψ h2
  refine ⟨v₂, fun i => by rw [hv₂, hv₁], fun i => by rw [(h₂.1 i).1, Category.comp_id], ?_⟩
  have := isEigBasis_push m h₂
  rwa [Category.id_comp] at this

end Chain

section Frame

variable {Z : Model Xo c β} {Z' : Model Xo c β'} {χ : Sp V ⟶ gen Z} {χ' : Sp V ⟶ gen Z'} {y : FrPt Xo c K}
  {tK : SAB H (Sp K)} {mK : SABMap tK Xo.univ.t (GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _)} {t t' : SAB H (Sp V)}
  {m : SABMap t Z.t (χ ≫ genι Z)} {m' : SABMap t' Z'.t (χ' ≫ genι Z')} {ψ : SABMap t t' (𝟙 (Sp V))}
  {a : SABMap tK t (spMap (algebraMap V K))} {a' : SABMap tK t' (spMap (algebraMap V K))}
  {mF : SABMap tK Z.oF.t (GlobalTheory.AllWt.ptF y)} {mF' : SABMap tK Z'.oF.t (GlobalTheory.AllWt.ptF y)}

theorem exists_lift_frameVec (hψ : a.φ ≫ ψ.φ = a'.φ) (hF0 : mF.φ ≫ Z.m0.toSABMap.φ = mK.φ)
    (hFm : mF.φ ≫ Z.m.φ = a.φ ≫ m.φ) (hF0' : mF'.φ ≫ Z'.m0.toSABMap.φ = mK.φ) (hFm' : mF'.φ ≫ Z'.m.φ = a'.φ ≫ m'.φ)
    {v : Sp (DualNumber V) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap V (DualNumber V)))
    {u' : Sp (DualNumber K) ⟶ Xo.univ.t.G.left} (hu' : u' ≫ Xo.univ.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ y.x)
    {w' : Sp (DualNumber K) ⟶ Z'.oF.t.G.left}
    (hw1 : w' ≫ Z'.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y)
    (hw2 : w' ≫ Z'.m0.toSABMap.φ = u') (hw3 : w' ≫ Z'.m.φ = spMap (dualMap (algebraMap V K)) ≫ (v ≫ ψ.φ) ≫ m'.φ) :
    ∃ w : Sp (DualNumber K) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y ∧
      w ≫ Z.m0.toSABMap.φ = u' ∧ w ≫ Z.m.φ = spMap (dualMap (algebraMap V K)) ≫ v ≫ m.φ := by
  have hx : GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _
  obtain ⟨u, hu1, hu2⟩ := exists_lift mK (spMap (algebraMap K (DualNumber K))) u' (by rw [hu', ← hx])
  have hbase : spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap V K) =
      spMap (dualMap (algebraMap V K)) ≫ spMap (algebraMap V (DualNumber V)) := by
    rw [OpenReg.spMap_comp, OpenReg.spMap_comp, PullbackSections.dualMap_comp_alg]
  have e1 : u ≫ mF'.φ = w' := by
    apply Z'.m0.toSABMap.cart.1.hom_ext
    · rw [Category.assoc, hF0', hu2, hw2]
    · rw [Category.assoc, mF'.cart.1.w, ← Category.assoc, hu1, hw1]
  have e2 : u ≫ a.φ = spMap (dualMap (algebraMap V K)) ≫ v := by
    apply ψ.cart.1.hom_ext
    · rw [Category.assoc, hψ]
      apply m'.cart.1.hom_ext
      · rw [Category.assoc, ← hFm', ← Category.assoc, e1, hw3]
        simp only [Category.assoc]
      · rw [Category.assoc, a'.cart.1.w, ← Category.assoc, hu1, hbase]
        simp only [Category.assoc, ψ.cart.1.w, Category.comp_id, hv]
    · rw [Category.assoc, a.cart.1.w, ← Category.assoc, hu1, Category.assoc, hv, hbase]
  refine ⟨u ≫ mF.φ, ?_, ?_, ?_⟩
  · rw [Category.assoc, mF.cart.1.w, ← Category.assoc, hu1]
  · rw [Category.assoc, hF0, hu2]
  · rw [Category.assoc, hFm, ← Category.assoc, e2, Category.assoc]

end Frame

theorem bdExt_of_bdExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z' : Model Xo c β') (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K), (algebraMap V K).comp φ = algebraMap c.F K → BdExt Z' φ y → BdExt Z φ y := by
  intro E _ _ _ H Dw l Xo c O _ β Z O' _ β' Z' V K _ _ _ _ _ _ _ φ y hφ h
  obtain ⟨χ', g', e1', e2', hw', hb'⟩ := h
  obtain ⟨χ, e1, e2⟩ := exists_genPt Z φ hφ y
  obtain ⟨tK, ⟨mK⟩⟩ := GlobalTheory.ModFam.exists_sabPull (GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _) Xo.univ.t
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull (χ ≫ genι Z) Z.t
  obtain ⟨t', ⟨m'⟩⟩ := GlobalTheory.ModFam.exists_sabPull (χ' ≫ genι Z') Z'.t
  obtain ⟨a, mF, hF0, hFm⟩ := exists_genIdent Z e2 mK m
  obtain ⟨a', mF', hF0', hFm'⟩ := exists_genIdent Z' e2' mK m'
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.ModelUniqueChecks.existsUnique_map V K t t' tK a a'
  choose v hv1 hv2 hv3 using fun τ => exists_isEigBasis_chain m m' ψ (EigFrame.isEigBasis g' τ)
  refine ⟨χ, eigFrameOf (fun τ i => v τ i ≫ m.φ) hv3, e1, e2, fun τ i => ?_,
    mem_genBd_of_mem_genBd m m' ψ _ hb'⟩
  obtain ⟨w', hw1, hw2, hw3⟩ := hw' τ i
  rw [← hv1 τ i] at hw3
  exact exists_lift_frameVec hψ hF0 hFm hF0' hFm' (hv2 τ i) (y.tan τ i).1 hw1 hw2 hw3

end GlobalTheory.CuspFrom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTrivialOnSumTransvections
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem exists_mem_sum_transv_killed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (φ : X.Γ →* Multiplicative ℝ) (d : ℕ) (ξ : Fin d → Fin N → E) (α : Fin d → E), (∀ i j, herm X.Gm (ξ i) (ξ j) = 0) → (∀ j, ∃ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = transvMat X.Gm (ξ j) (α j) ∧ φ γ = 1) → ∃ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = 1 + ∑ j, α j • rk1 X.Gm (ξ j) (ξ j) ∧ φ γ = 1 := by
  intro E _ _ _ N X φ d
  induction d with
  | zero =>
    intro ξ α _ _
    refine ⟨1, ?_, map_one φ⟩
    simp
  | succ d ih =>
    intro ξ α horth hγ
    obtain ⟨γ0, h0, hφ0⟩ := ih (ξ ∘ Fin.castSucc) (α ∘ Fin.castSucc)
      (fun i j => horth _ _) (fun j => hγ _)
    obtain ⟨γl, hl, hφl⟩ := hγ (Fin.last d)
    refine ⟨γ0 * γl, ?_, by rw [map_mul, hφ0, hφl, one_mul]⟩
    have hmat : ((γ0 * γl : X.Γ) : GL (Fin N) E) = (γ0 : GL (Fin N) E) * (γl : GL (Fin N) E) := rfl
    rw [hmat, Matrix.GeneralLinearGroup.coe_mul, h0, hl, transvMat_eq, Fin.sum_univ_castSucc]
    have hz : (∑ j : Fin d, (α ∘ Fin.castSucc) j • rk1 X.Gm ((ξ ∘ Fin.castSucc) j) ((ξ ∘ Fin.castSucc) j))
        * (α (Fin.last d) • rk1 X.Gm (ξ (Fin.last d)) (ξ (Fin.last d))) = 0 := by
      rw [Finset.sum_mul]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [smul_mul_assoc, mul_smul_comm, one_add_smul_vecMulVec_mul]
      simp only [Function.comp_apply, horth, zero_smul, smul_zero]
    rw [add_mul, one_mul, mul_add, mul_one, hz, add_zero]
    simp only [Function.comp]
    abel

end GlobalTheory.UnipKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantVectorsLieBasisOfComplexArcStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_vectors_lieBasis_of_complex_arc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) (Uw : UnfWit U) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), Formalism.L2.PjFree.GoodEmb c σ → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i j, z τ i j ≠ 0 → (Uw.e j).1 = τ) → (∀ τ i, AnVec Ha (e τ i) (z τ i)) → ArcBasis W (fun τ => σ.comp (embK c τ)) e := by
  first | exact @GlobalTheory.CuspFromBasis.main | exact GlobalTheory.CuspFromBasis.main | (intros; apply GlobalTheory.CuspFromBasis.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FourierJacobiConstantTermEqZeroOfFlowLineStatement
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_constant_term_eq_zero_of_flow_line : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (x : Frame X.Ψ r) (s : X.Ψ → ℂ) (d : X.Ψ → ℝ) (T : ℝ) (g : ℤ → ℂ), X.IsSec la P → FreqNonneg X la P → X.IsIso ξ → x ∈ X.dom → (∀ τ, 0 < d τ) → (∀ m ≤ 0, g m = 0) → (∀ w : ℂ, T < w.im → X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x ∈ X.dom ∧ HasSum (fun m : ℤ => g m * ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi w ^ m) (P (X.flow ξ (fun τ => s τ + w * (d τ : ℂ)) x))) → X.fj la ξ 0 P x = 0 := by
  first | exact @GlobalTheory.CuspLimit.fj_zero_eq_zero_of_line | exact GlobalTheory.CuspLimit.fj_zero_eq_zero_of_line | (intros; apply GlobalTheory.CuspLimit.fj_zero_eq_zero_of_line <;> assumption)
end

