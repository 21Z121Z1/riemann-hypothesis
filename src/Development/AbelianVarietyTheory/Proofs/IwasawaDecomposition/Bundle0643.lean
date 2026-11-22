import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefSetNonemptyOfNonneg
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TangentVectorsThetaSectionArcWitnessBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0037
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0616
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0626
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0627
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleFormsArcCompare
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LocM.FJ
open GlobalTheory.Toroidal
open GlobalTheory.ArcQ (Wit LieImg)

noncomputable section

namespace GlobalTheory.ArcSubst

open GlobalTheory.ArcBaseChange GlobalTheory.ObjRebase

set_option maxHeartbeats 1600000 in

theorem lieImg_subst : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (b : O →+* A) (a₀ : ArcIn Dw l β A b) (γ γ' : levelForms H l.M' a₀.D₀.X) (h : γ ∈ admitted H l.M' a₀.D₀.X) (h' : γ' ∈ admitted H l.M' a₀.D₀.X) (χ : Sp (PowerSeries A) ⟶ Y.X) (g : PowerSeries A →+* PowerSeries A) (W : Wit Y (withForm a₀ γ h) χ) (W' : Wit Y (withForm a₀ γ' h') (spMap g ≫ χ)) (hD : Out.IsPullDeg g W.P.D.toPre W'.P.D.toPre) (bc : W'.t.G ≅ (Over.pullback (Out.specOf g)).obj W.t.G) (w₁ : LB.Iso W'.P.D.toPre.P.L (a₀.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ))), g.comp (PowerSeries.C (R := A)) = PowerSeries.C → g PowerSeries.X ∈ Ideal.span {PowerSeries.X} → Out.IsPullUnif g hD bc W.P.U W'.P.U → (∀ y, hD.xe (W'.e y) = W.e y) → W'.φ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ → HEq W'.w w₁ → Tri W.w hD.w w₁ → ∀ (ν : Out.GtPt a₀.D₀ (epsR A)) (v : epsR (PowerSeries A) ⟶ W.t.G) (v' : epsR (PowerSeries A) ⟶ W'.t.G), LieImg W ν v → v'.left ≫ bc.hom.left ≫ pullback.fst W.t.G.hom (Out.specOf g) = spMap (dualMap g) ≫ v.left → LieImg W' ν v' := by
  intro E _ _ _ H Dw l Xo c O _ β Y A _ _ _ b a₀ γ γ' h h' χ g W W' hD bc w₁ hgC hgX hU he hφ hw₁ T ν v v' hv hv'
  intro n ρ' κ' vn' hρ₁ hρ₂ hκ₁ hκ₂ hb hf x
  obtain ⟨wL, -, -, -, lev⟩ := (isPullUnif_iff_stalks _ _ _ _ _ _ _ hD _ _ _ _ bc _ _).1 hU
  obtain ⟨hm, hh, ⟨-, ht⟩, -⟩ := lev n
  obtain ⟨ho, Ht⟩ := ht (W'.e x)
  rw [he] at ho Ht
  have Hν := pmaps_pullIdIso _ _ _ (ν.isGen x)
  have hs : W'.φ ≫ 𝟙 _ = (hD.e.hom.left ≫ pullback.fst W.P.D.toPre.P.A.hom (Out.specOf g)) ≫ W.φ :=
    (Category.comp_id _).trans hφ
  have S : Sq W.w hD.w (pullIdIso a₀.D₀.P.L) W'.w := by
    intro Z r z j i i' k hj hi hi' hk
    have hj' : W'.φ (r z) ∈ a₀.D₀.P.L.U j := (congrArg (fun f => f (r z) ∈ a₀.D₀.P.L.U j) hφ).mpr hj
    have pg := (isGen_iff W'.w).1 W'.spec.2.1 Z r z j i' k k hj' hi' hk hk
    rw [← T Z r z j i k hj hi hk, ← gw_heq hφ hw₁ r z j k, pg, gm_self W'.P.D.toPre.P.isLB r z hk, inv_one, mul_one,
      gw_pullIdIso a₀.D₀.P.L (r ≫ W'.φ) z j i' hj' hi']

  have := isLocalRing_trunc A n
  have := ConstTan.isLocalRing_dual (PowerSeries A ⧸ Ideal.span {(PowerSeries.X : PowerSeries A)} ^ (n + 1))
  let I : Ideal (PowerSeries A) := Ideal.span {PowerSeries.X}
  have hI : I ^ (n + 1) ≤ (I ^ (n + 1)).comap g := Ideal.map_le_iff_le_comap.1 (by
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    exact Ideal.pow_right_mono ((Ideal.span_singleton_le_iff_mem _).2 hgX) _)
  let gb : PowerSeries A ⧸ I ^ (n + 1) →+* PowerSeries A ⧸ I ^ (n + 1) := Ideal.quotientMap _ g hI
  let ρ : DualNumber (PowerSeries A) →+* DualNumber (PowerSeries A ⧸ I ^ (n + 1)) := dualMap (Ideal.Quotient.mk _)
  let κ : DualNumber A →+* DualNumber (PowerSeries A ⧸ I ^ (n + 1)) :=
    dualMap ((Ideal.Quotient.mk _).comp (PowerSeries.C (R := A)))
  let s : Sp (DualNumber (PowerSeries A ⧸ I ^ (n + 1))) ⟶ Sp (PowerSeries A ⧸ I ^ (n + 1)) := spMap (algebraMap _ _)
  have hs₀ : s ≫ Out.thick (PowerSeries A) I n = spMap ρ ≫ (epsR (PowerSeries A)).hom :=
    ((ArcBaseChange.spMap_comp' _ _).trans (congrArg spMap (RingHom.ext fun r =>
      (dualMap_inl (Ideal.Quotient.mk (I ^ (n + 1))) r).symm : _ = ρ.comp (algebraMap _ _)))).trans
      (ArcBaseChange.spMap_comp' _ _).symm
  let vn : Sp (DualNumber (PowerSeries A ⧸ I ^ (n + 1))) ⟶ (Out.thickObj (PowerSeries A) I n W.t.G).left :=
    pullback.lift (spMap ρ ≫ v.left) s (by rw [Category.assoc, Over.w v, hs₀])
  have hx : vn ≫ (Out.fstG I n W.t.G).left = spMap ρ ≫ v.left := pullback.lift_fst _ _ _
  have G := hv n ρ κ vn (dualMap_inl _) (dualMap_eps' _) (dualMap_inl _) (dualMap_eps' _)
    (pullback.lift_snd _ _ _) hx x
  let q := spMap (dualMap gb)
  have hρ : spMap ρ' ≫ spMap (dualMap g) = q ≫ spMap ρ := by
    rw [ArcBaseChange.spMap_comp', ArcBaseChange.spMap_comp']
    refine congrArg spMap (dual_hom_ext (fun r => ?_) ?_)
    · simp only [RingHom.comp_apply, ρ, dualMap_inl, hρ₁]
      rfl
    · simp only [RingHom.comp_apply, ρ, dualMap_eps', hρ₂]
  have hκ : spMap κ' ≫ 𝟙 _ = q ≫ spMap κ := by
    rw [Category.comp_id, ArcBaseChange.spMap_comp']
    refine congrArg spMap (dual_hom_ext (fun r => ?_) ?_)
    · simp only [RingHom.comp_apply, κ, dualMap_inl, hκ₁]
      exact congrArg (fun y => TrivSqZeroExt.inl (Ideal.Quotient.mk (I ^ (n + 1)) y)) (RingHom.congr_fun hgC r).symm
    · simp only [RingHom.comp_apply, κ, dualMap_eps', hκ₂]
  have hvn : vn' ≫ hm = q ≫ vn := by
    have := thick_mono (PowerSeries A) I n
    have : Mono (Out.fstG I n W.t.G).left := inferInstanceAs (Mono (pullback.fst _ _))
    rw [← cancel_mono (Out.fstG I n W.t.G).left, Category.assoc, hh, ← Category.assoc, hf, Category.assoc]
    erw [hv']
    rw [← Category.assoc, hρ, Category.assoc, Category.assoc, hx]
  refine genRelR_baseChange hs S W.spec.2.1 W.P.D.toPre.P.isLB a₀.D₀.P.isLB ((W.P.U.gt n).t_gen _) (ν.isGen _) ho Ht Hν
    hvn hκ (fun k => ?_) G
  have e := comp_eq_of_squares hs (ho k) (g := Out.DegPre.gtφT a₀.D₀ (epsR A) ν.b x k) (g' := Out.DegPre.gtφT a₀.D₀ (epsR A) ν.b x k) (d := 𝟙 _)
    (by rw [Category.comp_id, Category.id_comp]) hvn hκ (G.1 k)
  simpa only [Category.comp_id] using e

end GlobalTheory.ArcSubst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllStepsHoldOfHasDR
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.LieMet GlobalTheory.LocM.FrameBC GlobalTheory.LocM.MapComp GlobalTheory.LocM.CommonMod

namespace GlobalTheory.LocM.StepOfFrame

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_dual {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] [Nontrivial R] {y : Sp R ⟶ X} {V : X.Opens}
    (h : ⊤ ≤ y ⁻¹ᵁ V) {n n' d : ℕ} {m : Fin n' → Γ(GlobalTheory.LieVB.omega t.G, V)} (hm : VB.IsFrame m)
    {v : Fin n → TanM y t.G} (hv : Full v) (e : Fin d ↪ Fin n) :
    ∃ a : GL (Fin n') R, ∀ (j : Fin n') (i : Fin d), (i : ℕ) ≠ j →
      ∑ l, a j l * tanEv t (isTan_tv (v (e i))) h (m l) = 0 := by
  classical
  let M : Matrix (Fin n') (Fin n) R := Matrix.of fun l i => tanEv t (isTan_tv (v i)) h (m l)
  have key : ∀ (c : Fin n → R) (l : Fin n'), tanEv t (isTan_tv (∑ i, c i • v i)) h (m l) = M.mulVec c l := fun c l => by
    rw [GlobalTheory.T.tanEv_linear_combination E H X t R y V h n _ (fun i => isTan_tv (v i)) c _ _ ((LieMet.isComb_iff v c _).2 rfl)]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hb : Function.Bijective M.mulVecLin := by
    refine ⟨fun c c' hc => ?_, fun b => ?_⟩
    · have := (GlobalTheory.T.existsUnique_tangent_of_values E H X t R y V h n' m hm (M.mulVec c)).unique ⟨_, key c⟩
        ⟨_, fun l => (key c' l).trans (congrFun hc l).symm⟩
      exact (hv _).unique rfl (tan_ext this)
    · obtain ⟨w, ⟨hw, hw'⟩, -⟩ := GlobalTheory.T.existsUnique_tangent_of_values E H X t R y V h n' m hm b
      obtain ⟨c, hc, -⟩ := hv (tanOf hw)
      refine ⟨c, funext fun l => ((key c l).symm.trans ?_).trans (hw' l)⟩
      simp only [← hc]
      rfl
  obtain rfl : n = n' := by simpa using (LinearEquiv.ofBijective _ hb).finrank_eq
  obtain ⟨u, hu⟩ : IsUnit M := Matrix.mulVec_surjective_iff_isUnit.1 hb.2
  have hd : d ≤ n := by simpa using Fintype.card_le_of_embedding e
  obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_extending_pair _ _ (Fin.castLE_injective hd) e.injective
  refine ⟨⟨(u⁻¹).1.submatrix ρ id, M.submatrix id ρ, ?_, ?_⟩, fun j i hij => ?_⟩
  · rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← hu, Units.inv_mul, Matrix.submatrix_one_equiv]
  · rw [Matrix.submatrix_mul_equiv, ← hu, Units.mul_inv, Matrix.submatrix_id_id]
  · have e₁ : ((u⁻¹).1 * M) (ρ j) (e i) = 0 := by
      rw [← hu, Units.inv_mul, Matrix.one_apply_ne]
      rw [← hρ i]
      exact fun q => hij (congrArg Fin.val (ρ.injective q)).symm
    exact e₁

theorem full_map {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {R : Type} [CommRing R] {y : Sp R ⟶ X} {y' : Sp R ⟶ X'}
    (L : TanM y t.G ≃ₗ[R] TanM y' t'.G) {n : ℕ} {v : Fin n → TanM y t.G} (hv : Full v) : Full fun i => L (v i) := fun w => by
  obtain ⟨w, rfl⟩ := L.surjective w
  refine (existsUnique_congr fun a => ?_).1 (hv w)
  rw [← L.injective.eq_iff, map_sum]
  simp only [map_smul]

theorem exists_full {X X' X₁ : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {t₁ : SAB H X₁} {τ : X' ⟶ X} {π : X₁ ⟶ X}
    (mu : SABMap t' t τ) (nu : SABMap t₁ t π) {R₀ R : Type} [CommRing R₀] [CommRing R] (ρ : R₀ →+* R) {y₀ : Sp R₀ ⟶ X'}
    {y : Sp R ⟶ X₁} (q : (spMap ρ ≫ y₀) ≫ τ = y ≫ π) {n : ℕ} {v : Fin n → (Sp (DualNumber R₀) ⟶ t'.G.left)}
    (hvt : ∀ i, IsTanAtG t' y₀ (v i)) (hvb : ∀ u, IsTanAtG t' y₀ u → ∃! cf, IsCombAtG t' y₀ v cf u) :
    ∃ v₁ : Fin n → TanM y t₁.G, Full v₁ ∧
      ∀ i, (tv (v₁ i)).left ≫ nu.φ = (spMap (Formalism.L2.Pj.dualMap ρ) ≫ v i) ≫ mu.φ := by
  have hv₀ : Full fun i => tanOf (hvt i) := fun u =>
    (existsUnique_congr fun a => LieMet.isComb_iff (fun i => tanOf (hvt i)) a u).1 (hvb _ (isTan_tv u))
  exact ⟨_, full_map ((pushE mu _ q).trans (pushE nu y rfl).symm) (full_bc ρ hv₀), fun i =>
    congrArg (fun z => (tv z).left) ((pushE nu y rfl).apply_symm_apply _)⟩

theorem sum_map_mul_eq_zero {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {n : ℕ} (a b : Fin n → R) (c : k)
    (h : ∑ l, a l * b l = 0) : ∑ l, φ (a l) * (c * φ (b l)) = 0 := by
  have := congrArg (fun s => c * φ s) h
  simp only [map_sum, map_mul, map_zero, mul_zero, Finset.mul_sum] at this
  exact (Finset.sum_congr rfl fun l _ => mul_left_comm _ _ _).trans this

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
  {i₀ : Idx H p}

theorem exists_isTrans {Z' Z : Mdl Y i₀} {f : Z'.X ⟶ Z.X} (hf : IsMap Z' Z f) (x : Z'.X) :
    ∃ (τ : (Y Z'.i).X ⟶ (Y Z.i).X) (mu : SABMap (Y Z'.i).t (Y Z.i).t τ), LocM.IsTrans Z.i Z'.i τ mu := by
  haveI : Nonempty Z'.X := ⟨x⟩
  obtain ⟨z, hz⟩ := Z'.dense.nonempty
  obtain ⟨τ, mu, -, ht, -⟩ := hf.2 (Z'.X.residueField z) (Z'.X.fromSpecResidueField z) (by
    rintro _ ⟨a, rfl⟩
    exact (Scheme.fromSpecResidueField_apply z a).symm ▸ hz)
  exact ⟨τ, mu, ht⟩

theorem isIso_incl_top (Z : Mdl Y i₀) : IsIso (Lat.top Z).N.incl :=
  Twist.isIso_of_bijective _ fun V => ⟨(Lat.top Z).N.incl_app_injective V, fun s =>
    ⟨(Lat.top Z).N.mkSec s (by rw [Lat.isTop_top V]; trivial), (Lat.top Z).N.incl_app_mkSec _ _⟩⟩

theorem holds_of_hasDR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z Z' : Mdl Y i₀), HasDR Z' → (∃ f, IsMap Z' Z f) → ∀ t ∈ allSteps (Lat.top Z), Step.Holds t Z' := by
  intro E _ _ _ H Dw Xo p W _ _ Y i₀ Z Z' hZ ⟨f, hf⟩ t ht
  obtain ⟨σ, r, hr, rfl⟩ := mem_allSteps.1 ht
  have hrt : r ∈ Z'.ty σ := by rw [hZ.1, Finset.mem_range]; omega
  refine ⟨hrt, f, hf, fun x => ?_⟩
  obtain ⟨τ, mu, htr⟩ := exists_isTrans hf x
  have hπ := comp_π_eq hf htr
  obtain ⟨U₀, hU₀, w, hx₀, hw, hfl⟩ := hZ.2 x
  obtain ⟨n, v, e, hve, hvt, hvb⟩ := hw σ
  obtain ⟨V, n', m, hxV, hm⟩ := (Lat.top Z).free (f x)
  obtain ⟨U, hU, hxU, hle⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := U₀ ⊓ f ⁻¹ᵁ V) ⟨hx₀, hxV⟩
  have h₀ : U ≤ U₀ := fun z hz => (hle hz).1
  have h₁ : U ≤ f ⁻¹ᵁ V := fun z hz => (hle hz).2
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  let ρ : Γ(Z'.X, U₀) →+* Γ(Z'.X, U) := (Z'.X.presheaf.map (homOfLE h₀).op).hom
  have hρ : spMap ρ ≫ hU₀.fromSpec = hU.fromSpec := hU₀.map_fromSpec hU (homOfLE h₀).op
  have hy : ⊤ ≤ (hU.fromSpec ≫ f) ⁻¹ᵁ V := fun z _ => by
    have := h₁ (hU.range_fromSpec.le ⟨z, rfl⟩)
    rwa [Scheme.Hom.comp_preimage]
  have q₁ : (spMap ρ ≫ hU₀.fromSpec ≫ Z'.π) ≫ τ = (hU.fromSpec ≫ f) ≫ Z.π := by
    rw [← Category.assoc (spMap ρ), hρ, Category.assoc, Category.assoc, hπ]
  obtain ⟨v₁, hv₁, hL⟩ := exists_full (R := Γ(Z'.X, U)) mu Z.tMap ρ q₁ hvt hvb
  have := isIso_incl_top Z
  obtain ⟨a, ha⟩ := exists_dual (R := Γ(Z'.X, U)) Z.t hy (hm.map_iso (Lat.top Z).N.incl) hv₁ e
  refine ⟨U, hU, V, n', m, a, hxU, h₁, hm, ?_⟩
  rintro k _ φ z hz h ⟨τ', mu', u, i, htr', hu, hi, hzu⟩ j hj
  obtain ⟨rfl, hmu⟩ := TransUniq.trans_unique E H Dw Xo p W Y _ _ τ τ' mu mu' hf.1.2.1 htr htr'
  have ept : spMap (φ.comp ρ) ≫ hU₀.fromSpec = spMap φ ≫ hU.fromSpec := by
    rw [← sp_comp, Category.assoc, hρ]
  have hw' := hfl k (φ.comp ρ) (by rw [ept]; exact range_subset_opn Z' hu)
  rw [ept] at hw'
  obtain ⟨c, -, fu, sf⟩ := flagAt_two Z' hw' hu
  obtain ⟨cf, hcf, hcomb⟩ := sf σ r hrt i hi
  obtain ⟨b, ψ, hb, -⟩ := hu
  obtain ⟨y, hy', -⟩ := exists_lift_chart Z' hb
  rw [← hmu k y _ _ _ (by rw [hy']; exact (fu.1 σ i).1.1)] at hzu
  let z' : Fin (Dw.mult σ) → (Sp (DualNumber k) ⟶ Z.t.G.left) := fun i' =>
    spMap (Formalism.L2.Pj.dualMap φ) ≫ (tv (v₁ (e i'))).left
  have hz' : ∀ i', IsTanAtG Z.t (spMap φ ≫ hU.fromSpec ≫ f) (z' i') := fun i' => isTan_map φ rfl (isTan_tv _)
  have hc₁ := comb_push mu hcomb
  have q₂ : ((spMap φ ≫ hU.fromSpec) ≫ Z'.π) ≫ τ = (spMap φ ≫ hU.fromSpec ≫ f) ≫ Z.π := by
    simp only [Category.assoc, hπ]
  have q₃ : (fun i' => w.bc (φ.comp ρ) σ i' ≫ mu.φ) = fun i' => z' i' ≫ Z.tMap.φ := funext fun i' => by
    rw [← Vecs.bc_bc, Category.assoc, hL, hve]
    exact Category.assoc _ _ _
  rw [q₂, q₃, ← hzu] at hc₁
  have hz₁ : IsTanAtG Z.t (spMap φ ≫ hU.fromSpec ≫ f) z := by rw [← Category.assoc]; exact hz
  have h' : ⊤ ≤ (spMap φ ≫ hU.fromSpec ≫ f) ⁻¹ᵁ V := by rw [← Category.assoc]; exact h
  have hc₂ := (comb_push_iff Z.tMap hz' cf hz₁).1 hc₁
  have ev : ∀ s, tanEv Z.t hz h s = ∑ i', cf i' * φ (tanEv Z.t (isTan_tv (v₁ (e i'))) hy s) :=
    fun s => by
      refine Eq.trans ?_ ((GlobalTheory.T.tanEv_linear_combination E H _ Z.t k _ V h' _ z' hz' cf z hz₁ hc₂ s).trans
        (Finset.sum_congr rfl fun i' _ => congrArg (cf i' * ·) (GlobalTheory.T.tanEv_base_change E H _ Z.t _ _ V hy _ _ k φ _ h' s)))
      congr 1
  show ∑ l, φ (a j l) * tanEv Z.t hz h ((Lat.top Z).N.incl.app V (m l)) = 0
  simp only [ev, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i' _ => ?_
  by_cases hi' : r ≤ (i' : ℕ)
  · simp [hcf i' hi']
  · exact sum_map_mul_eq_zero (R := Γ(Z'.X, U)) φ _ _ _ (ha j i' (by have : r ≤ (j : ℕ) := hj; omega))

end GlobalTheory.LocM.StepOfFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasLatticeCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atlas_lattice_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (D : LCrd M π) (σ : E →+* ℂ) (α : A.ch.ι → D.C.A), (∀ a, ⊤ ≤ A.ch.χ a ⁻¹ᵁ D.C.B (α a)) → ∃ (cv Dv : ∀ a, Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R a), IsFrVec D A σ α cv ∧ (∀ a, LeftInv (Dv a) (cv a)) ∧ ∀ (K : Type) [Field K] (a a' : A.ch.ι) (φ : A.ch.R a →+* K) (φ' : A.ch.R a' →+* K), spMap φ ≫ A.ch.χ a = spMap φ' ≫ A.ch.χ a' → ∀ e : ℕ, e ∈ ty σ ∨ e = 0 ∨ e = Dw.mult σ → initSpan K (fun i => φ ∘ cv a i) e = initSpan K (fun i => φ' ∘ cv a' i) e := by
  first | exact @GlobalTheory.GrCl.exists_isFrVec | exact GlobalTheory.GrCl.exists_isFrVec | (intros; apply GlobalTheory.GrCl.exists_isFrVec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasModelComparisonStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atlas_model_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty) (Z : Mdl Y i₀), p.Prime → (p : ℂ) ∈ W.nonunits → Geo (Y i) π → i.c.F ≤ Z.i.c.F → (∀ σ, ty σ ⊆ Z.ty σ) → LocMaps Z A → ∃ h, MapsTo Z A h := by
  first | exact @GlobalTheory.DRFlag.exists_mapsTo | exact GlobalTheory.DRFlag.exists_mapsTo | (intros; apply GlobalTheory.DRFlag.exists_mapsTo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupDivisorTrivialOnFibers
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory

theorem cechPic_sp_field_eq_zero (K : Type) [Field K] (c : GlobalTheory.CechPic.Pic (Sp K)) : c = 0 := by
  obtain ⟨L, hL, rfl⟩ := GlobalTheory.CechPic.cls_surj c
  exact (GlobalTheory.CechPic.cls_eq_zero_iff hL).2 (GlobalTheory.LB.exists_isGen_of_isLocalRing hL)

theorem pull_nsmul_cls_eq_zero_of_comap : ∀ {S S' X' : Scheme.{0}} (B : GlobalTheory.EffCartierData S') (n : ℕ) (h : S ⟶ S') (q : S ⟶ X')
    (I : X'.IdealSheafData), IsIso h → FinalTheorems.EffCartier I → I.comap q = (B.idealSheaf ^ n).comap h →
    ∀ (W : Scheme.{0}) (K : Type) [Field K] (g : W ⟶ S) (a : W ⟶ Sp K) (x0 : Sp K ⟶ X'), g ≫ q = a ≫ x0 →
    GlobalTheory.CechPic.pull (g ≫ h) (n • GlobalTheory.CechPic.cls B.lb B.isLB_lb) = 0 := by
  intro S S' X' B n h q I hh hI hc W K _ g a x0 hg
  obtain ⟨D, hD⟩ := GlobalTheory.EffCartierData.exists_idealSheaf_eq hI
  have kh : (B.nsmul n).KeepsRegular h := (B.nsmul n).keepsRegular_of_flat h
  have e1 : ((B.nsmul n).pull h kh).idealSheaf = D.idealSheaf.comap q := by
    rw [GlobalTheory.EffCartierData.idealSheaf_pull, GlobalTheory.EffCartierData.idealSheaf_nsmul, hD, hc]
  have kq : D.KeepsRegular q := (D.keepsRegular_iff_effCartier q).2
    (e1 ▸ ((B.nsmul n).pull h kh).effCartier_idealSheaf)
  have e2 : ((B.nsmul n).pull h kh).idealSheaf = (D.pull q kq).idealSheaf := by
    rw [e1, GlobalTheory.EffCartierData.idealSheaf_pull]
  have i1 := ((B.nsmul n).pull h kh).lbIso_of_idealSheaf_eq (D.pull q kq) e2
  have key : GlobalTheory.CechPic.pull h (n • GlobalTheory.CechPic.cls B.lb B.isLB_lb) =
      GlobalTheory.CechPic.pull q (GlobalTheory.CechPic.cls D.lb D.isLB_lb) := by
    rw [← GlobalTheory.CechPic.cls_lbPow B.isLB_lb n (B.isLB_lbPow n),
      ← (GlobalTheory.CechPic.cls_eq_iff (B.nsmul n).isLB_lb (B.isLB_lbPow n)).2 (B.lbIso_nsmul n),
      ← GlobalTheory.CechPic.cls_pull (B.nsmul n).isLB_lb h (pull_isLB (B.nsmul n).isLB_lb h),
      ← GlobalTheory.CechPic.cls_pull D.isLB_lb q (pull_isLB D.isLB_lb q),
      ← (GlobalTheory.CechPic.cls_eq_iff ((B.nsmul n).pull h kh).isLB_lb (pull_isLB (B.nsmul n).isLB_lb h)).2
        ((B.nsmul n).lbIso_pull h kh),
      ← (GlobalTheory.CechPic.cls_eq_iff (D.pull q kq).isLB_lb (pull_isLB D.isLB_lb q)).2 (D.lbIso_pull q kq)]
    exact (GlobalTheory.CechPic.cls_eq_iff _ _).2 i1
  rw [GlobalTheory.CechPic.pull_comp, key, ← GlobalTheory.CechPic.pull_comp, hg, GlobalTheory.CechPic.pull_comp,
    cechPic_sp_field_eq_zero K (GlobalTheory.CechPic.pull x0 _), map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellCoordinateLinearRelationStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_coordinate_linear_relation : ∀ (R : Type) [CommRing R] (m a k b N : ℕ) (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → R), a ≤ k → k ≤ b → LeftInv D c → ∀ q, ∃ (T : Type) (_ : Fintype T) (jj : T → GPm m a b) (e : T → R), ∀ w' : GPm m a b, gxi a b hk c w' q = ∑ t, (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (e t) * ∑ q', (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gell a b hk D (jj t) q') * gxi a b hk c w' q' := by
  first | exact @GlobalTheory.GrCl.CellLin.main | exact GlobalTheory.GrCl.CellLin.main | (intros; apply GlobalTheory.GrCl.CellLin.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellCoordinatePolynomialsSurjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_coordinate_polynomials_surjective : ∀ (R : Type) [CommRing R] (m a k b N : ℕ) (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → R) (w : GPm m a b), a ≤ k → k ≤ b → LeftInv D c → ∑ q, (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gell a b hk D w q) * gxi a b hk c w q = 1 ∧ Function.Surjective (MvPolynomial.eval₂Hom (MvPolynomial.C : R →+* MvPolynomial (GVar m a k b) R) (gxi a b hk c w)) := by
  first | exact @GlobalTheory.GrCl.CellGen.main | exact GlobalTheory.GrCl.CellGen.main | (intros; apply GlobalTheory.GrCl.CellGen.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellGeneratorMemConeOfSmulCombination
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem cell_gen_mem_cone_of_smul : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m m' : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin m' → LinearMap.BilinForm ℤ X)
    (i : Fin m) (k : ℕ) (a : Fin m' → ℕ), IsCell bar φ δ → IsCell bar φ γ → 0 < k → k • δ i = ∑ j, a j • γ j →
    ∀ j, 0 < a j → ∃ (k' : ℕ) (b : Fin m → ℕ), 0 < k' ∧ k' • γ j = ∑ l, b l • δ l := by
  intro O _ bar φ X _ _ _ m m' δ γ i k a hδ hγ hk he j hj
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hδ.strict

  have eδ : φ.evalZ (k • δ i) = k * φ.evalZ (δ i) := by
    have := hδ.linear (Pi.single i (k : ℝ)) fun l => by
      by_cases h : l = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    simp only [Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rw [InvFun.evalZ]
    convert this using 2
    funext x y
    simp
  have eγ : φ.evalZ (∑ j, a j • γ j) = ∑ j, (a j : ℝ) * φ.evalZ (γ j) := by
    have := hγ.linear (fun j => (a j : ℝ)) fun j => by positivity
    rw [InvFun.evalZ]
    convert this using 2
    funext x y
    simp [LinearMap.sum_apply]
  have ℓδ : (ℓ (k • δ i) : ℝ) = k * (N * φ.evalZ (δ i)) := by
    rw [map_nsmul, ← h1 i, nsmul_eq_mul]; push_cast; rfl
  have ℓγ : (ℓ (∑ j, a j • γ j) : ℝ) = ∑ j, (a j : ℝ) * ℓ (γ j) := by
    rw [map_sum]; push_cast; simp [map_nsmul]
  have key : ∑ j, (a j : ℝ) * ((ℓ (γ j) : ℝ) - N * φ.evalZ (γ j)) = 0 := by
    have e1 : (ℓ (∑ j, a j • γ j) : ℝ) = N * φ.evalZ (∑ j, a j • γ j) := by
      rw [← he, ℓδ, eδ]; ring
    rw [ℓγ, eγ, Finset.mul_sum] at e1
    simp only [mul_sub, Finset.sum_sub_distrib, e1]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => by ring
  have nn : ∀ j ∈ Finset.univ, 0 ≤ (a j : ℝ) * ((ℓ (γ j) : ℝ) - N * φ.evalZ (γ j)) := fun j _ =>
    mul_nonneg (by positivity) (sub_nonneg.2 (h2 _ (hγ.mem j) (hγ.nonneg j)))
  have z := (Finset.sum_eq_zero_iff_of_nonneg nn).1 key j (Finset.mem_univ _)
  have ha : (a j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  have heq : (N : ℝ) * φ.evalZ (γ j) = ℓ (γ j) := by
    have := (mul_eq_zero.1 z).resolve_left ha
    linarith
  exact h3 _ (hγ.mem j) (hγ.nonneg j) heq

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellGeneratorsSmulMemOtherCellCone
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem exists_smul_eq_sum_of_sum_toReal_eq {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {m m' : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin m' → LinearMap.BilinForm ℤ X)
    (c : Fin m' → ℝ) (hδ : IsCell bar φ δ) (hγ : IsCell bar φ γ) (hc : ∀ j, 0 ≤ c j)
    (hs : ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ j)) :
    ∀ i, ∃ (k : ℕ) (a : Fin m' → ℕ), 0 < k ∧ k • δ i = ∑ j, a j • γ j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict

  have hrel : ∑ i, (ℓ (δ i) : ℝ) = ∑ j, c j * (ℓ (γ j) : ℝ) := by
    have e := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim δ γ) (c := Sum.elim (fun _ => (1 : ℝ)) (fun j => -c j)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, one_smul, neg_smul, Finset.sum_neg_distrib, hs,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at e
    simp only [Sum.elim_inl, Sum.elim_inr, one_mul, neg_mul, Finset.sum_neg_distrib] at e
    linarith

  have hlinγ := (linearOn_iff φ γ).1 hγ.linear c hc
  have hlinδ := (linearOn_iff φ δ).1 hδ.linear (fun _ => 1) (fun _ => zero_le_one)
  simp only [one_smul, one_mul] at hlinδ
  rw [hs, hlinγ] at hlinδ

  have hsum : ∑ i, ((ℓ (δ i) : ℝ) - N * φ.evalZ (δ i)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hlinδ, hrel, Finset.mul_sum]
    simp only [h1]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun j _ => by ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ (ℓ (δ i) : ℝ) - N * φ.evalZ (δ i) := fun i _ =>
    sub_nonneg.2 (h2 _ (hδ.mem i) (hδ.nonneg i))
  intro i
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum i (Finset.mem_univ _)
  exact h3 _ (hδ.mem i) (hδ.nonneg i) (by linarith)

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMem
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.MixedLower

def ChartMem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l}
    (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop)
    (X : GMod Xo c) (J : X.X.IdealSheafData) (φ : InvFun (𝓞 E)) (N : ℕ) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X.X) (t : SAB H (Sp R)) (_ : SABMap t X.t ξ)
    (P : PELUnif (maximalIdeal R) t) (k : ℕ) (γ : Fin k → LinearMap.BilinForm ℤ P.D.toPre.X),
    IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom →
    ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso →
    Cn P.D.toPre.X k γ → InCone P.D.toPre γ →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ¬ (∀ p : ℕ, p.Prime → IsUnit (p : W)) →
      ∀ ϖ : W, Irreducible ϖ → ∀ f : R →+* W, IsLocalHom f → Set.range (jK W ≫ spMap f ≫ ξ) ⊆ Set.range X.j →
      ∀ be ∈ levelForms H 1 P.D.toPre.X, FormAt P.D.toPre f ϖ be →
      ∀ m : ℕ, (m : ℝ) = (comb 0 φ N φ).evalZ be → Ideal.span {ϖ ^ m} ≤ (idlAlong J ξ).map f

end GlobalTheory.MixedLower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapMulIdealSheaf
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Principalise

theorem comap_mul_idealSheaf : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) (I J : X.IdealSheafData),
    (I * J).comap f = I.comap f * J.comap f := by
  intro X X' f I J
  have h : ∀ y : X', ∃ (U : X.affineOpens) (A : X'.affineOpens), y ∈ A.1 ∧ A.1 ≤ f ⁻¹ᵁ U.1 := by
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f y)) isOpen_univ
    obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAU⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ f ⁻¹ᵁ U from hyU) (f ⁻¹ᵁ U).isOpen
    exact ⟨⟨U, hU⟩, ⟨A, hA⟩, hyA, hAU⟩
  choose U A hyA hAU using h
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top A ?_ fun y => ?_
  · exact top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyA y⟩
  · rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, comapIdealAffine _ f (U y) (A y) (hAU y),
      comapIdealAffine _ f (U y) (A y) (hAU y), comapIdealAffine _ f (U y) (A y) (hAU y),
      Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul]

end GlobalTheory.Principalise
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactNormalNoetherianOfFlagCellCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_normal_noetherian_of_flagCell_cover : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Type) [Finite T] (m : T → ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (F : Scheme.{0}) (i : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ F)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → (∀ b w, IsOpenImmersion (i b w)) → (∀ x : F, ∃ b w, x ∈ Set.range (i b w)) → CompactSpace F ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme F ∧ TopologicalSpace.NoetherianSpace F := by
  first | exact @GlobalTheory.FlagEmb.compact_normal_noetherian_of_cells | exact GlobalTheory.FlagEmb.compact_normal_noetherian_of_cells | (intros; apply GlobalTheory.FlagEmb.compact_normal_noetherian_of_cells <;> assumption)
end

