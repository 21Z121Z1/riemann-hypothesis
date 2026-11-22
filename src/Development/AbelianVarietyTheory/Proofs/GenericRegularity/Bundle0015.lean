import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0040
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0028
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0020
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecPowSuccAndConstTermPowSucc
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem bddSec_pow_succ_and_constTerm_pow_succ
    (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P) (m : ℕ) :
    X.IsBddSec ((m + 1) • la) (P ^ (m + 1)) ∧ ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom,
      X.fj ((m + 1) • la) ξ 0 (P ^ (m + 1)) x = X.fj la ξ 0 P x ^ (m + 1) := by
  induction m with
  | zero =>
    simp only [zero_add, one_smul, pow_one]
    exact ⟨hP, fun _ _ _ _ => trivial⟩
  | succ m ih =>
    have h := bddSec_mul_and_constTerm_mul E r X ((m + 1) • la) la (P ^ (m + 1)) P ih.1 hP
    rw [succ_nsmul la (m + 1), pow_succ P (m + 1)]
    refine ⟨h.1, fun ξ hξ x hx => ?_⟩
    rw [h.2 ξ hξ x hx, ih.2 ξ hξ x hx, pow_succ _ (m + 1)]

theorem cuspForm_of_bddSec_of_pow_succ :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
      ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (m : ℕ), X.IsBddSec la P →
        P ^ (m + 1) ∈ X.SS ((m + 1) • la) → P ∈ X.SS la := by
  intro E _ _ _ r X la P m hP hpow
  refine ⟨hP, fun ξ hξ x hx => ?_⟩
  have h := (bddSec_pow_succ_and_constTerm_pow_succ E r X la P hP m).2 ξ hξ x hx
  rw [hpow.2 ξ hξ x hx] at h
  exact pow_eq_zero_iff (Nat.succ_ne_zero m) |>.1 h.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFiniteMchartCover
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

private theorem compactSpace_model {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) : CompactSpace Y.X := by
  obtain ⟨N, i, hi, hs⟩ := Y.proj
  haveI := hi
  haveI : IsProper (PSpace.str O N) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str O N
  haveI : QuasiCompact Y.s := by rw [← hs]; infer_instance
  exact QuasiCompact.compactSpace_of_compactSpace Y.s

private theorem exists_mChart_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] [IsNoetherianRing O] {β : O →+* c.F}
    (Y : Model Xo c β) (hP : PushInvertible Y.t.G Y.t.PP.L) (x : Y.X) : ∃ M : MChart Y, x ∈ M.U := by
  obtain ⟨U, hU, hxU, hdom, ⟨θ, hθ, hne⟩, n, v₀, ρ, hlie⟩ :=
    GlobalTheory.ModelChart.exists_chart_lieBasis_matrices E H Dw l Xo c O β Y hP x
  exact ⟨⟨U, hU, hdom, θ, hθ, hne, n, v₀, ρ, hlie⟩, hxU⟩

theorem exists_finite_mchart_cover :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (β : O →+* c.F) (Y : Model Xo c β), PushInvertible Y.t.G Y.t.PP.L → ∃ (J : Type) (_ : Finite J) (M : J → MChart Y), ∀ x : Y.X, ∃ j, x ∈ (M j).U := by
  intro E _ _ _ H Dw l Xo c O _ _ β Y hP
  haveI := compactSpace_model Y
  choose M hM using exists_mChart_mem Y hP
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => ((M x).U : Set Y.X))
    (fun x => (M x).U.isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hM x⟩)
  refine ⟨t, inferInstance, fun j => M j.1, fun x => ?_⟩
  obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨⟨j, hj⟩, hx⟩

end GlobalTheory.Reg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsModelChartGenericPointComponent
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open scoped CategoryTheory.Obj

namespace GlobalTheory.GenericChart

theorem exists_sec_ne_zero_of_iso {X : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B)
    (s : A.Sec) (j : A.ι) (hj : s.f j ≠ 0) : ∃ (s' : B.Sec) (k : B.ι), s'.f k ≠ 0 := by
  obtain ⟨w, hw⟩ := LBIso.chartPull (chartPullId B) (chartPullPull A (𝟙 X) (𝟙 X) rfl) h.symm
  obtain ⟨s', hs'⟩ := sec_pull_down ((isGen_iff w).1 hw) hA hB s
  refine ⟨s', ?_⟩
  by_contra hn
  push Not at hn
  refine hj (fn_ext fun x hx => ?_)
  obtain ⟨k, hk⟩ := exists_chart hB x
  have e := hs' X (𝟙 X) x j k hx hk
  rw [hn k, gs_eq (𝟙 X) x _ hk 0, map_zero, map_zero, mul_zero, Category.comp_id] at e
  rw [e, gs_eq (𝟙 X) x _ hx 0, map_zero, map_zero]

theorem exists_secOn_of_isOpenImmersion {X₀ X : Scheme.{0}} (q : X₀ ⟶ X) [IsOpenImmersion q] (L : LB X)
    (V₀ : X₀.Opens) (V : X.Opens) (hV : V ≤ q.opensRange) (hV₀ : q ⁻¹ᵁ V ≤ V₀)
    (θ : ∀ J, Γ(X₀, V₀ ⊓ (L.pull q).U J)) (hθ : θ ∈ secOn (L.pull q) V₀) :
    ∃ θ' ∈ secOn L V, ∀ (z : X₀) (i : L.ι), q z ∈ V → z ∈ X₀.basicOpen (θ fun _ => i) →
      q z ∈ X.basicOpen (θ' i) := by
  have bij : ∀ W : X.Opens, W ≤ V → Function.Bijective (q.app W).hom := fun W hW =>
    have := q.isIso_app W (hW.trans hV)
    ConcreteCategory.bijective_of_isIso (q.app W)
  have le : ∀ i, q ⁻¹ᵁ (V ⊓ L.U i) ≤ V₀ ⊓ (L.pull q).U (fun _ => i) := fun i z hz => ⟨hV₀ hz.1, mem_pull.2 hz.2⟩
  choose θ' hθ' using fun i => (bij (V ⊓ L.U i) inf_le_left).2 (resG X₀ (le i) (θ fun _ => i))
  have val : ∀ i z, q z ∈ V ⊓ L.U i → gs q z _ (θ' i) = gs (𝟙 X₀) z _ (θ fun _ => i) := fun i z hz => by
    have e := gs_pull (𝟙 X₀) q z _ hz (θ' i)
    rw [Category.id_comp, hθ'] at e
    exact e.symm.trans (gs_res (𝟙 X₀) z (le i) hz _)
  refine ⟨θ', fun i j => (bij _ (inf_le_left.trans inf_le_left)).1 (fn_ext fun z hz => ?_), fun z i hz hb => ?_⟩
  · have hz' : q z ∈ V ⊓ L.U i ⊓ L.U j := hz
    refine (gs_pull (𝟙 X₀) q z _ hz' _).trans (Eq.trans ?_ (gs_pull (𝟙 X₀) q z _ hz' _).symm)
    have hm : (𝟙 X₀ : X₀ ⟶ X₀) z ∈ V₀ ⊓ (L.pull q).U (fun _ => i) ⊓ (L.pull q).U (fun _ => j) :=
      ⟨le i hz'.1, mem_pull.2 hz'.2⟩
    have e := congrArg (gs (𝟙 X₀) z _) (hθ (fun _ => i) (fun _ => j))
    rw [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm, gs_res _ z _ hm,
      gs_unit _ z ((L.pull q).U (fun _ => i) ⊓ (L.pull q).U (fun _ => j)) ⟨hm.1.2, hm.2⟩,
      gm_pull_g L q (𝟙 X₀) z _ _ hm.1.2 hm.2, Category.id_comp] at e
    rw [Category.id_comp, gs_res _ z _ hz', gs_mul _ z _ hz', gs_res _ z _ hz', gs_res _ z _ hz',
      gs_unit _ z (L.U i ⊓ L.U j) ⟨hz'.1.2, hz'.2⟩, val i z hz'.1, val j z ⟨hz'.1.1, hz'.2⟩]
    exact e
  · have hi : q z ∈ V ⊓ L.U i := ⟨hz, mem_pull.1 (X₀.basicOpen_le _ hb).2⟩
    show z ∈ q ⁻¹ᵁ X.basicOpen (θ' i)
    rw [Scheme.preimage_basicOpen]
    refine (congrArg (fun a => z ∈ X₀.basicOpen a) (hθ' i)).mpr ?_
    exact (X₀.basicOpen_res (θ fun _ => i) (homOfLE (le i)).op).ge ⟨hi, hb⟩

theorem exists_lift_of_isPreimmersion {X' X : Scheme.{0}} (j : X' ⟶ X) [IsPreimmersion j] {K : Type} [Field K]
    (y : Sp K ⟶ X) (ξ : X') (h : y (IsLocalRing.closedPoint K) = j ξ) : ∃ z : Sp K ⟶ X', z ≫ j = y := by
  obtain ⟨⟨p, φ⟩, hy⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
  have hp : p = j ξ := by
    rw [← h, ← hy]
    exact (X.fromSpecResidueField_apply p _).symm
  subst hp
  have : IsIso (j.residueFieldMap ξ) := by
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨(j.residueFieldMap ξ).hom.injective, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := X'.residue_surjective ξ a
    obtain ⟨b, rfl⟩ := j.stalkMap_surjective ξ a
    exact ⟨X.residue _ b, congr($(Scheme.residue_residueFieldMap j ξ).hom b)⟩
  refine ⟨Spec.map (inv (j.residueFieldMap ξ) ≫ φ) ≫ X'.fromSpecResidueField ξ, ?_⟩
  rw [← hy, Scheme.SpecToEquivOfField_symm_apply, Category.assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← Spec.map_comp,
    IsIso.hom_inv_id_assoc]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem eq_genPt_of_specializes (Z : Comp Xo c) {ξ : Xo.XF c} (h : ξ ⤳ genPt Z) : ξ = genPt Z := by
  have h1 : closure {genPt Z} = (Z : Set (Xo.XF c)) :=
    (Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2))
  have h2 : (Z : Set (Xo.XF c)) ⊆ closure {ξ} := h1 ▸ specializes_iff_closure_subset.1 h
  have h3 : closure {ξ} ⊆ (Z : Set (Xo.XF c)) := Z.2.2 isIrreducible_singleton.closure h2
  exact (h.antisymm (specializes_iff_closure_subset.2 (h1 ▸ h3))).eq

theorem exists_section (hT : Out.SecTwistSt) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Z : Comp Xo c)
    [IsNoetherianRing (𝓞 c.F)] [IsFractionRing (𝓞 c.F) c.F] :
    ∃ V : Y.X.Opens, Y.j (genPt Z) ∈ V ∧ ∃ θ ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ V),
      ∀ y ∈ V, ∃ (g : Y.t.G.left) (i : Y.t.PP.L.ι), Y.t.G.hom g = y ∧ g ∈ Y.t.G.left.basicOpen (θ i) := by
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  obtain ⟨W, hxW, hW⟩ := ModelChart.exists_open_isDomain Y.X (Y.j (genPt Z))
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := Y.X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  have hU : IsAffineOpen U := hU
  have := hW U hxU hUW
  let R : Type := Γ(Y.X, U)
  let K : Type := FractionRing R
  have b₁ : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  have b₂ : Flat (spMap (algebraMap (𝓞 c.F) c.F)) := by
    have : Module.Flat (𝓞 c.F) c.F := IsLocalization.flat c.F (nonZeroDivisors (𝓞 c.F))
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 this)
  have := Y.jQ_open
  have a₁ : IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip b₁
  have a₂ : Flat (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback _ _).flip b₂
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  have : Flat Y.j := by unfold Model.j; infer_instance

  have hgen : hU.fromSpec (⊥ : PrimeSpectrum R) = Y.j (genPt Z) := by
    obtain ⟨p, hp⟩ : Y.j (genPt Z) ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hxU
    have s₀ : (⊥ : PrimeSpectrum R) ⤳ p := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    have s₁ : hU.fromSpec (⊥ : PrimeSpectrum R) ⤳ Y.j (genPt Z) := hp ▸ s₀.map hU.fromSpec.continuous
    obtain ⟨ξ, h₁, h₂⟩ := Flat.generalizingMap Y.j s₁
    rw [← h₂, eq_genPt_of_specializes Z h₁]
  have hK : spMap (algebraMap R K) (IsLocalRing.closedPoint K) = (⊥ : PrimeSpectrum R) := by
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap R K) (IsLocalRing.maximalIdeal K) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)
  obtain ⟨z, hz⟩ := exists_lift_of_isPreimmersion Y.j (spMap (algebraMap R K) ≫ hU.fromSpec) (genPt Z)
    (by rw [← hgen, ← hK]; rfl)
  obtain ⟨t₀, ⟨m₀⟩⟩ := (ModelPoints.model_points_charts E H Dw l Xo c _ _ Y).2.1 (Sp R) hU.fromSpec
  obtain ⟨t', ⟨m₂⟩⟩ : ∃ t' : SAB H (Sp K), Nonempty (SABMap t' t₀ (spMap (algebraMap R K))) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (algebraMap R K)) t₀
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₀ m₂
  have cancel : ∀ (p : Sp K ⟶ Y.X) (_ : p = z ≫ Y.j) (n : SABMap t' Y.t p),
      Nonempty (SABMap t' Y.oF.t z) := by
    intro p hp n; subst hp
    exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n).choose⟩
  obtain ⟨m₃⟩ := cancel _ hz.symm n
  obtain ⟨b, hb⟩ := globalSections_rank_one_fibre hT amplePt Y.oF m₃
  obtain ⟨k, hk⟩ : ∃ k, b.f k ≠ 0 := by
    by_contra h0
    push Not at h0
    obtain ⟨a, -, ha⟩ := hb b
    exact zero_ne_one ((ha 0 fun i => by rw [h0, mul_zero]).trans (ha 1 fun i => by rw [h0, mul_zero]).symm)
  obtain ⟨w, hw, -⟩ := n.lin
  have iso : LBIso t'.PP.L ((Y.t.PP.L.pull m₀.φ).pull m₂.φ) := LBIso.chartPull (chartPullId _) (chartPullLinComb Y.t.PP.L m₀.φ (K := PUnit) (fun _ => m₂.φ)
    (fun _ => n.φ) (fun _ => 1) (𝟙 _) (fun _ => by rw [Category.id_comp]; exact hn.symm)) ⟨w, hw⟩
  have hL₀ := pull_isLB Y.t.PP.isLB m₀.φ
  obtain ⟨h, h0, θ, hθ, nz⟩ := SecSpread.main R t₀.G t₀.semi _ hL₀ K _ m₂.φ _ m₂.cart.1
    (exists_sec_ne_zero_of_iso t'.PP.isLB (pull_isLB hL₀ _) iso b k hk)
  have : IsOpenImmersion m₀.φ :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) m₀.cart.1.flip inferInstance
  have pre : ∀ p : Sp R, hU.fromSpec p ∈ Y.X.basicOpen h ↔ p ∈ PrimeSpectrum.basicOpen h := fun p =>
    SetLike.ext_iff.1 (hU.fromSpec_preimage_basicOpen h) p
  have sq : ∀ g, Y.t.G.hom (m₀.φ g) = hU.fromSpec (t₀.G.hom g) := fun g => congr($(m₀.cart.1.w) g)
  have rg : ∀ y ∈ Y.X.basicOpen h, ∃ p : Sp R, hU.fromSpec p = y := fun y hy => by
    show y ∈ Set.range hU.fromSpec
    rw [hU.range_fromSpec]; exact Y.X.basicOpen_le h hy
  obtain ⟨θ', hθ', nz'⟩ := exists_secOn_of_isOpenImmersion m₀.φ Y.t.PP.L _ (Y.t.G.hom ⁻¹ᵁ Y.X.basicOpen h)
    (fun g hg => by
      obtain ⟨p, hp⟩ := rg _ hg
      obtain ⟨g', h₁, -⟩ := Scheme.exists_preimage_of_isPullback m₀.cart.1 g p hp.symm
      exact ⟨g', h₁⟩)
    (fun g hg => (pre _).1 (sq g ▸ hg)) θ hθ
  refine ⟨Y.X.basicOpen h, ?_, θ', hθ', fun y hy => ?_⟩
  · rw [← hgen]
    exact (pre _).2 h0
  · obtain ⟨p, rfl⟩ := rg y hy
    obtain ⟨g, i, rfl, hg⟩ := nz p ((pre p).1 hy)
    exact ⟨m₀.φ g, i PUnit.unit, sq g, nz' g _ (show Y.t.G.hom (m₀.φ g) ∈ _ from sq g ▸ hy) hg⟩

open ModelChart in

theorem exists_chart_genPt : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Z : Comp Xo c), ∃ M : MChart Y, Y.j (genPt Z) ∈ M.U := by
  intro hT E _ _ _ H Dw l Xo c Y Z
  have := c.fin
  have : NumberField c.F := {}
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have := Y.t.semi.smooth
  obtain ⟨W, hxW, hW⟩ := exists_open_isDomain Y.X (Y.j (genPt Z))
  obtain ⟨V, hxV, θ, hθ, nz⟩ := exists_section hT Y Z
  obtain ⟨U, hU, hxU, hUW, n, v₀, hv⟩ := GlobalTheory.exists_affine_lieBasis_baseChange Y.X Y.t.G _ (W ⊓ V) ⟨hxW, hxV⟩
  have hUV : U ≤ V := hUW.trans inf_le_right
  have nz' : ∀ y ∈ U, ∃ (g : Y.t.G.left) (i : Y.t.PP.L.ι), Y.t.G.hom g = y ∧ g ∈ Y.t.G.left.basicOpen
      (resG Y.t.G.left (inf_le_inf_right _ (Y.t.G.hom.preimage_mono hUV)) (θ i)) := fun y hy => by
    obtain ⟨g, i, rfl, hg⟩ := nz y (hUV hy)
    refine ⟨g, i, rfl, ?_⟩
    show g ∈ Y.t.G.left.basicOpen (Y.t.G.left.presheaf.map (homOfLE _).op (θ i))
    rw [Scheme.basicOpen_res]
    exact ⟨⟨hy, (Y.t.G.left.basicOpen_le _ hg).2⟩, hg⟩
  obtain ⟨t₀, ⟨m₀⟩⟩ := (GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c _ _ Y).2.1 (Sp Γ(Y.X, U)) hU.fromSpec
  have c₀ : IsGrpPullback t₀.G Y.t.G (spMap (RingHom.id Γ(Y.X, U)) ≫ hU.fromSpec) m₀.φ := by
    have e : spMap (RingHom.id Γ(Y.X, U)) = 𝟙 _ := Spec.map_id _
    rw [e, Category.id_comp]
    exact m₀.cart
  obtain ⟨u, hu, hb⟩ := hv _ (RingHom.id _) t₀.G m₀.φ c₀
  simp only [spMap_dualMapR_id, Category.id_comp] at hu
  have ex : ∀ a j, ∃ r : Fin n → Γ(Y.X, U), IsLieComb r u (u j ≫ t₀.act.act a) := fun a j =>
    have := t₀.act.hom a
    (hb.2 _ (isTangent_comp_hom (hb.1 j) _)).exists
  choose r hr using ex
  refine ⟨⟨U, hU, hW U hxU (hUW.trans inf_le_left), _, res_mem_secOn _ (Y.t.G.hom.preimage_mono hUV) hθ, nz', n, v₀,
    fun a i j => r a j i, fun R' _ f t' m => ?_⟩, hxU⟩
  obtain ⟨v', hv', hb'⟩ := hv R' f t'.G m.φ m.cart
  refine ⟨v', hv', hb', fun a j => ?_⟩
  have hp := m₀.cart.1
  let F : t'.G.left ⟶ t₀.G.left := hp.lift m.φ (t'.G.hom ≫ spMap f) (by rw [m.cart.1.w, Category.assoc])
  have hF : F ≫ m₀.φ = m.φ := hp.lift_fst _ _ _
  have hw : F ≫ t₀.G.hom = t'.G.hom ≫ spMap f := hp.lift_snd _ _ _
  have hc : IsGrpPullback t'.G t₀.G (spMap f) F := m₀.cart.cancel (hF ▸ m.cart) hw
  have lies : ∀ (w' : epsR R' ⟶ t'.G) (w : epsR Γ(Y.X, U) ⟶ t₀.G),
      w'.left ≫ m.φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ w.left ≫ m₀.φ →
      w'.left ≫ F = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ w.left := fun w' w h => by
    apply hp.hom_ext
    · rw [Category.assoc, hF, h, Category.assoc]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (GlobalTheory.LieCombBaseChange.dualMap_over f).symm
  refine (GlobalTheory.lieComb_baseChange _ _ f t₀.G t'.G F hc n u _ (r a j) v' _
    (fun k => lies _ _ (by rw [hv', hu])) (hr a j)).1 (lies _ _ ?_)
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, m.act, m₀.act, ← Category.assoc, hv',
    ← Category.assoc (u j).left, hu, Category.assoc]

end GlobalTheory.GenericChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRingHomOfIsLieComb
section
noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem exists_ringHom_of_isLieComb {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G]
    [IsCommMonObj G] (a : OAct O G) {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v)
    (ρ : O → Matrix (Fin n) (Fin n) R) (h : ∀ x j, IsLieComb (fun i => ρ x i j) v (v j ≫ a.act x)) :
    ∃ ρ' : O →+* Matrix (Fin n) (Fin n) R, ∀ x, ρ' x = ρ x := by
  classical
  let B := GlobalTheory.Serre.Lie.basis a hv
  refine ⟨(LinearMap.toMatrixAlgEquiv B).toRingEquiv.toRingHom.comp
    (Module.toModuleEnd R (S := O) (GlobalTheory.Serre.Lie a)), fun x => ?_⟩
  ext i j
  have h1 : IsLieComb (fun i => ρ x i j) (fun k => (B k).hom) (v j ≫ a.act x) := by
    simpa only [B, GlobalTheory.Serre.Lie.hom_basis] using h x j
  rw [GlobalTheory.Serre.Lie.isLieComb_iff] at h1
  have h2 : x • B j = ∑ k, ρ x k j • B k := by
    apply GlobalTheory.Serre.Lie.ext
    rw [GlobalTheory.Serre.Lie.hom_act_smul, ← h1, GlobalTheory.Serre.Lie.hom_basis]
  simp [LinearMap.toMatrixAlgEquiv_apply, h2, Finsupp.finset_sum_apply, Finsupp.single_apply]

theorem MChart.exists_ringHom_rho :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
      (M : MChart Y), ∃ ρ' : 𝓞 E →+* Matrix (Fin M.n) (Fin M.n) Γ(Y.X, M.U), ∀ a, ρ' a = M.ρ a := by
  intro E _ _ _ H Dw l Xo c O _ β Y M
  obtain ⟨_, _, _, _, _, hm⟩ :=
    sabPull Out.CubePf.cubePull (spMap (RingHom.id Γ(Y.X, M.U)) ≫ M.hU.fromSpec) Y.t
  obtain ⟨t', ⟨m⟩⟩ : ∃ t' : SAB H (Sp Γ(Y.X, M.U)),
      Nonempty (SABMap t' Y.t (spMap (RingHom.id Γ(Y.X, M.U)) ≫ M.hU.fromSpec)) :=
    ⟨_, ⟨hm.choose⟩⟩
  obtain ⟨v', -, hv', hρ⟩ := M.lie _ (RingHom.id _) t' m
  exact exists_ringHom_of_isLieComb t'.act hv' M.ρ hρ

end GlobalTheory.Reg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsEigenvectorIffLieBasisCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

noncomputable section

namespace GlobalTheory.Reg.VecEig

open GlobalTheory.GrpTangent

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def comb {n : ℕ} (v : Fin n → (epsR R ⟶ G)) (c : Fin n → R) : epsR R ⟶ G :=
  ∏ i, epsScale (c i) ≫ v i

theorem isLieComb_iff_comb {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = comb v c := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    apply Over.OverMorphism.ext
    rw [hu i, Over.comp_left]
    rfl
  · rintro rfl
    refine ⟨fun i => epsScale (c i) ≫ v i, fun i => ?_, ?_⟩
    · rw [Over.comp_left]
      rfl
    · rw [List.prod_ofFn]
      rfl

theorem comp_finProd {X Y : Over (Sp R)} (g : X ⟶ Y) {κ : Type} (s : Finset κ) (u : κ → (Y ⟶ G)) :
    g ≫ ∏ i ∈ s, u i = ∏ i ∈ s, g ≫ u i := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty]
    exact Chart.comp_one' g
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, comp_mul, ih]

theorem finProd_comp {X : Over (Sp R)} (g : G ⟶ G) [IsMonHom g] {κ : Type} (s : Finset κ) (u : κ → (X ⟶ G)) :
    (∏ i ∈ s, u i) ≫ g = ∏ i ∈ s, u i ≫ g := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty]
    exact one_comp g
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, mul_comp, ih]

theorem epsScale_sum_comp {w : epsR R ⟶ G} (hw : IsTangent w) {κ : Type} (s : Finset κ) (a : κ → R) :
    epsScale (∑ i ∈ s, a i) ≫ w = ∏ i ∈ s, epsScale (a i) ≫ w := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.prod_empty]
    exact epsScale_zero_comp hw
  · intro b t hb ih
    rw [Finset.sum_insert hb, Finset.prod_insert hb, epsScale_add_comp _ _ hw, ih]

theorem epsScale_comb {n : ℕ} (v : Fin n → (epsR R ⟶ G)) (c : Fin n → R) (z : R) :
    epsScale z ≫ comb v c = comb v (z • c) := by
  unfold comb
  rw [comp_finProd]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Category.assoc, epsScale_mul, Pi.smul_apply, smul_eq_mul]

theorem comb_comp {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (g : G ⟶ G) [IsMonHom g]
    (A : Matrix (Fin n) (Fin n) R) (hA : ∀ j, v j ≫ g = comb v fun i => A i j) (c : Fin n → R) :
    comb v c ≫ g = comb v (A.mulVec c) := by
  calc comb v c ≫ g = ∏ j, (epsScale (c j) ≫ v j) ≫ g := finProd_comp g _ _
    _ = ∏ j, comb v (c j • fun i => A i j) :=
        Finset.prod_congr rfl fun j _ => by rw [Category.assoc, hA j, epsScale_comb]
    _ = ∏ j, ∏ i, epsScale (A i j * c j) ≫ v i := Finset.prod_congr rfl fun j _ => by
        unfold comb
        exact Finset.prod_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_comm (c j)]
    _ = ∏ i, ∏ j, epsScale (A i j * c j) ≫ v i := Finset.prod_comm
    _ = comb v (A.mulVec c) := by
        unfold comb
        exact Finset.prod_congr rfl fun i _ => (epsScale_sum_comp (hv i) Finset.univ fun j => A i j * c j).symm

theorem isTangent_comb {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (c : Fin n → R) :
    IsTangent (comb v c) := by
  rw [isTangent_iff]
  unfold comb
  rw [comp_finProd]
  exact Finset.prod_eq_one fun i _ => (isTangent_iff _).1 (isTangent_epsScale (c i) (hv i))

theorem comb_injective {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) : Function.Injective (comb v) := by
  intro c d h
  have hc : IsLieComb c v (comb v c) := (isLieComb_iff_comb c v (comb v c)).2 rfl
  have hd : IsLieComb d v (comb v c) := (isLieComb_iff_comb d v (comb v c)).2 h
  exact (hv.2 _ (isTangent_comb hv.1 c)).unique hc hd

theorem pt_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) {X : Over S'} {u u' : X ⟶ t'.G}
    (h : u.left ≫ m.φ = u'.left ≫ m.φ) : u = u' := by
  cases m with
  | mk cm cart base act lin =>
    apply Over.OverMorphism.ext
    refine cart.1.hom_ext h ?_
    rw [Over.w u, Over.w u']

end GlobalTheory.Reg.VecEig

open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent in

theorem GlobalTheory.Reg.isEigAt_iff_eig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ (τ : E →+* ℂ) (cv : Fin M.n → R) (w : Sp (DualNumber R) ⟶ Xo.univ.t.G.left), Λ.Vec cv w → (IsEigAt c τ w ↔ M.Eig f τ cv) := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ τ cv w hw
  obtain ⟨v', u', hv', hu', rfl⟩ := hw
  obtain ⟨v, hv0, hvb, hρ⟩ := M.lie R f Λ.t' Λ.m2
  obtain rfl : v' = v := funext fun j => pt_ext Λ.m2 ((hv' j).trans (hv0 j).symm)
  have hu := (isLieComb_iff_comb _ _ _).1 hu'
  have hA := fun a j => (isLieComb_iff_comb _ _ _).1 (hρ a j)
  unfold IsEigAt MChart.Eig
  refine forall_congr' fun a => ?_
  have : IsMonHom (Λ.t'.act.act a) := Λ.t'.act.hom a
  have e1 : (u'.left ≫ Λ.m1.φ) ≫ (Xo.univ.t.act.act a).left = (u' ≫ Λ.t'.act.act a).left ≫ Λ.m1.φ := by
    rw [Over.comp_left, Category.assoc, Category.assoc]
    exact congrArg (u'.left ≫ ·) (Λ.m1.act a).symm
  have e2 : spMap (epsMul (algebraMap c.F R (embK c τ a))) ≫ u'.left ≫ Λ.m1.φ =
      (epsScale (algebraMap c.F R (embK c τ a)) ≫ u').left ≫ Λ.m1.φ := by
    rw [Over.comp_left, Category.assoc]
    rfl
  rw [e1, e2, hu, comb_comp hvb.1 _ ((M.ρ a).map f) (hA a), epsScale_comb]
  constructor
  · intro h
    exact comb_injective hvb (pt_ext Λ.m1 h)
  · intro h
    rw [h]
end
end

