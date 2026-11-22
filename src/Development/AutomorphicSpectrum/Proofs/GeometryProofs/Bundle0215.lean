import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0212
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0106
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0005
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0131
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0208
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0213
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0169
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0111
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsClosureCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegular
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0172
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0101
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianBoundConjugateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_bound_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (h : LieMetric M y) (C : ℝ) (z : Sp ℂ ⟶ X), AbBound t h C (spMap (starRingEnd ℂ) ≫ z) → AbBound t h C z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotUnif.abBound_of_conj | exact GlobalTheory.CompanionTheory.Ar.QuotUnif.abBound_of_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotUnif.abBound_of_conj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartMapsCompatibleRight
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SlopeNorm

open GroundTheory.Heights₂.Heights

theorem core_left {V : Type} [AddCommGroup V] [Module ℂ V] (c₁ c₂ : InnerProductSpace.Core ℂ V) (W : Set V)
    (hW : Submodule.span ℂ W = ⊤) (a : V) (h : ∀ b ∈ W, c₁.inner b a = c₂.inner b a) (b : V) :
    c₁.inner b a = c₂.inner b a := by
  have hb : b ∈ Submodule.span ℂ W := hW ▸ Submodule.mem_top
  induction hb using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have e₁ := c₁.smul_left 0 a 0
    have e₂ := c₂.smul_left 0 a 0
    simp only [smul_zero, map_zero, zero_mul] at e₁ e₂
    rw [e₁, e₂]
  | add x y _ _ hx hy => rw [c₁.add_left, c₂.add_left, hx, hy]
  | smul r x _ hx => rw [c₁.smul_left, c₂.smul_left, hx]

theorem core_eq {V : Type} [AddCommGroup V] [Module ℂ V] (c₁ c₂ : InnerProductSpace.Core ℂ V) (W : Set V)
    (hW : Submodule.span ℂ W = ⊤) (h : ∀ a ∈ W, ∀ b ∈ W, c₁.inner a b = c₂.inner a b) (a b : V) :
    c₁.inner a b = c₂.inner a b := by
  refine core_left c₁ c₂ W hW b (fun x hx => ?_) a
  have e := core_left c₁ c₂ W hW x (fun y hy => h y hy x hx) b
  rw [← c₁.conj_inner_symm, ← c₂.conj_inner_symm, e]

variable {L : Type} [Field L]

theorem span_tmul (σ : L →+* ℂ) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] :
    Submodule.span ℂ (Set.range fun e : V => (1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) = ⊤ := by
  refine (Submodule.eq_top_iff'.2 fun x => ?_)
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul c e =>
    have hc : c ⊗ₜ[𝓞 L] e = ((ComplexAt.ofComplex σ).symm c : ℂ) • ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] e) := by
      rw [TensorProduct.smul_tmul', ComplexAt.complex_smul_def]
      simp
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)
  | add a b ha hb => exact Submodule.add_mem _ ha hb

theorem spComp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (d : A →+* B) (c : B →+* C) :
    spMap c ≫ spMap d = spMap (c.comp d) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

def lf {S : Scheme.{0}} {G : Over S} {R : Type} [CommRing R] {x : Sp R ⟶ S} (v : epsAt x ⟶ G) :
    Sp (DualNumber R) ⟶ G.left :=
  v.left

theorem exists_transport {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x x' : Sp R ⟶ S}
    (h : x = x') {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G x V) :
    ∃ M' : LieModel G x' V, ∀ e, lf (M'.pt e) = lf (M.pt e) := by
  subst h
  exact ⟨M, fun _ => rfl⟩

theorem exists_lift {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R] (x' : Sp R ⟶ S') {b : Sp R ⟶ S}
    (hb : x' ≫ f = b) {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G b V) :
    ∃ M' : LieModel G' x' V, ∀ e, lf (M'.pt e) ≫ φ = lf (M.pt e) := by
  subst hb
  exact (LiePull.lieModel_pullback S S' G G' f φ h R x' V).1 M

theorem exists_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R] (x' : Sp R ⟶ S')
    (v : epsAt x' ⟶ G') : ∃ u : epsAt (x' ≫ f) ⟶ G, lf v ≫ φ = lf u :=
  ⟨LiePull.tanPts h x' v, rfl⟩

theorem hodge_congr {S : Scheme.{0}} {G : Over S} [GrpObj G] (Lb : LB G.left) {z z' : Sp ℂ ⟶ S} (h : z = z')
    {v w : epsAt z ⟶ G} {v' w' : epsAt z' ⟶ G} (hv : lf v = lf v') (hw : lf w = lf w') {c : ℂ}
    (hc : HodgeIP G Lb z v w c) : HodgeIP G Lb z' v' w' c := by
  subst h
  obtain rfl : v = v' := Over.OverMorphism.ext hv
  obtain rfl : w = w' := Over.OverMorphism.ext hw
  exact hc

theorem ip_congr {S : Scheme.{0}} {G : Over S}
    (ip : ∀ z : Sp ℂ ⟶ S, (epsAt z ⟶ G) → (epsAt z ⟶ G) → ℂ) {z z' : Sp ℂ ⟶ S} (h : z = z')
    {v w : epsAt z ⟶ G} {v' w' : epsAt z' ⟶ G} (hv : lf v = lf v') (hw : lf w = lf w') :
    ip z v w = ip z' v' w' := by
  subst h
  obtain rfl : v = v' := Over.OverMorphism.ext hv
  obtain rfl : w = w' := Over.OverMorphism.ext hw
  rfl

end GlobalTheory.CompanionTheory.Ar.SlopeNorm

open GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.SlopeNorm GlobalTheory.CompanionTheory.Ar.LiePull in

theorem GlobalTheory.CompanionTheory.Ar.SlopeNorm.sqAt_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (L₁ L : Type) [Field L₁] [Field L] [NumberField L] (e₂ : L₁ →+* L) (z₁ : Sp L₁ ⟶ X) (z : Sp (𝓞 L) ⟶ X) (hz : spMap (algebraMap (𝓞 L) L) ≫ z = spMap e₂ ≫ z₁) (P₁ : AbPart t z₁) (P₂ : AbPart t (spMap e₂ ≫ z₁)) (mK2 : SABMap P₂.tK P₁.tK (spMap e₂)) (mB2 : SABMap P₂.tB P₁.tB (spMap e₂)) (c1 : mK2.φ ≫ P₁.m.φ = P₂.m.φ) (c2 : mK2.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ) (t' : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (m' : SABMap tK t' (spMap (algebraMap (𝓞 L) L))) (mP : SABMap tK P₁.tB (spMap e₂)) (w : P₂.tB.G.left ⟶ tK.G.left) (hw : w ≫ mP.φ = mB2.φ) (hw' : w ≫ tK.G.hom = P₂.tB.G.hom) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel t.G ξ Li) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (h : LieMetric M₀ y) (K₀ : ℝ) (hQ : ∀ (zc : Sp ℂ ⟶ X) (P : AbPart t zc) (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v₀ : epsAt zc ⟶ t.G) (c : ℂ), IsTanAt _ _ v → v.left ≫ P.m.φ = v₀.left → HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ K₀ * (h.ip zc v₀ v₀).re) (B B' : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t.G z B.carrier) (MB' : LieModel t'.G (𝟙 _) B'.carrier) (hB : IsFibre (fun z v w c => c = h.ip z v w) z B MB) (hB' : IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B' MB') (f : B.carrier →ₗ[𝓞 L] B'.carrier) (hf : ∀ (e : B.carrier) (v : epsAt (𝟙 (Sp L)) ⟶ P₂.tK.G), MB.Lifts (algebraMap (𝓞 L) L) P₂.m.φ e v → MB'.Lifts (algebraMap (𝓞 L) L) (P₂.e.hom.left ≫ w ≫ m'.φ) (f e) (v ≫ P₂.τ.q)) (σ : L →+* ℂ) (x : GroundTheory.Heights₂.Heights.Fibre σ B.carrier), sqAt B' σ (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x) ≤ K₀ * sqAt B σ x := by
  intro E _ _ _ H X t L₁ L _ _ _ e₂ z₁ z hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' Ω _ ξ Li _ _ M₀ K J y h K₀ hQ
    B B' MB MB' hB hB' f hf σ x
  haveI : Smooth t.G.hom := t.semi.smooth
  haveI : Smooth t'.G.hom := t'.semi.smooth
  obtain ⟨Pσ, mKσ, mBσ, d1, d2⟩ := GlobalTheory.T.abelian_part_base_change E H X t L₁ ℂ z₁ P₁ (σ.comp e₂)
  obtain ⟨Mσ, hMσ⟩ := GlobalTheory.T.lie_model_complex_base_change X t.G L z B.carrier MB σ
  obtain ⟨Mσ', hMσ'⟩ := GlobalTheory.T.lie_model_complex_base_change (Sp (𝓞 L)) t'.G L (𝟙 _) B'.carrier MB' σ
  have hb : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z = spMap (σ.comp e₂) ≫ z₁ := by
    rw [← spComp (algebraMap (𝓞 L) L) σ, ← spComp e₂ σ, Category.assoc, Category.assoc, hz]
  have hb' : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 _ = spMap σ ≫ spMap (algebraMap (𝓞 L) L) := by
    rw [Category.comp_id, spComp]
  have hb2 : spMap σ ≫ spMap e₂ = 𝟙 _ ≫ spMap (σ.comp e₂) := by
    rw [Category.id_comp, spComp]

  obtain ⟨core₁, hcore₁⟩ := h.herm _ (Fibre σ B.carrier) Mσ
  have h1 : ∀ a b, (B.metric.form σ).inner a b = h.ip _ (Mσ.pt a) (Mσ.pt b) := by
    intro a b
    rw [← hcore₁]
    refine core_eq _ _ _ (span_tmul σ _) ?_ a b
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    rw [hcore₁]
    exact hB σ e e' _ _ (hMσ e) (hMσ e')

  obtain ⟨Mz, hMz⟩ := exists_transport hb' Mσ'
  have h2 : ∀ a b, HodgeIP t'.G t'.PP.L (spMap σ ≫ spMap (algebraMap (𝓞 L) L)) (Mz.pt a) (Mz.pt b)
      ((B'.metric.form σ).inner a b) := by
    refine GlobalTheory.T.hodge_inner_product_on_span E H (Sp L) (Sp (𝓞 L)) tK t' (spMap (algebraMap (𝓞 L) L)) m' (spMap σ)
      (Fibre σ B'.carrier) Mz (B'.metric.form σ) (Set.range fun e => (1 : ComplexAt σ) ⊗ₜ[𝓞 L] e)
      ⟨0, TensorProduct.tmul_zero _ _⟩ (span_tmul σ _) ?_
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    exact hodge_congr t'.PP.L hb' (hMz _).symm (hMz _).symm (hB' σ e e' _ _ (hMσ' e) (hMσ' e'))

  obtain ⟨Mc, hMc⟩ := exists_transport hb Mσ
  obtain ⟨Mv, hMv⟩ := exists_lift Pσ.m.cart (𝟙 _) (by rw [Category.id_comp]; exact hb.symm) Mσ
  obtain ⟨Mu, hMu⟩ := exists_lift m'.cart (spMap σ) hb'.symm Mσ'
  have hv₀ : lf (Mv.pt x) ≫ Pσ.m.φ = lf (Mc.pt x) := (hMv x).trans (hMc x).symm
  have h3 := GlobalTheory.T.abelian_part_maps_compatible_left E H X t L₁ L e₂ z₁ z hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' B.carrier B'.carrier
    MB MB' f hf σ Pσ mKσ mBσ d1 d2 Mσ hMσ Mσ' hMσ' x (Mv.pt x) (Mu.pt (f.lTensor (ComplexAt σ) x)) (hMv x) (hMu _)

  have hUz : lf (Mu.pt (f.lTensor (ComplexAt σ) x)) ≫ m'.φ = lf (Mz.pt (f.lTensor (ComplexAt σ) x)) :=
    (hMu _).trans (hMz _).symm
  have a1 := ((GlobalTheory.T.hodge_inner_product_pullback_unique E H (Sp L) (Sp (𝓞 L)) tK t' (spMap (algebraMap (𝓞 L) L)) m' (spMap σ)
    (Mu.pt (f.lTensor (ComplexAt σ) x)) (Mu.pt (f.lTensor (ComplexAt σ) x))
    (Mz.pt (f.lTensor (ComplexAt σ) x)) (Mz.pt (f.lTensor (ComplexAt σ) x)) hUz hUz).1 _).2
    (h2 (f.lTensor (ComplexAt σ) x) (f.lTensor (ComplexAt σ) x))
  obtain ⟨U, hU⟩ := exists_push mP.cart (spMap σ) (Mu.pt (f.lTensor (ComplexAt σ) x))
  obtain ⟨Vv, hV⟩ := exists_push mBσ.cart (𝟙 _) (Mv.pt x ≫ Pσ.τ.q ≫ Pσ.e.hom)
  have a2 := ((GlobalTheory.T.hodge_inner_product_pullback_unique E H (Sp L) (Sp L₁) tK P₁.tB (spMap e₂) mP (spMap σ)
    (Mu.pt (f.lTensor (ComplexAt σ) x)) (Mu.pt (f.lTensor (ComplexAt σ) x)) U U hU hU).1 _).1 a1
  have hUV : lf U = lf Vv := hU.symm.trans (Eq.trans h3 hV)
  have a3 := ((GlobalTheory.T.hodge_inner_product_pullback_unique E H (Sp ℂ) (Sp L₁) Pσ.tB P₁.tB (spMap (σ.comp e₂)) mBσ (𝟙 _)
    (Mv.pt x ≫ Pσ.τ.q ≫ Pσ.e.hom) (Mv.pt x ≫ Pσ.τ.q ≫ Pσ.e.hom) Vv Vv hV hV).1 _).2
    (hodge_congr P₁.tB.PP.L hb2 hUV hUV a2)
  have h5 := hQ (spMap (σ.comp e₂) ≫ z₁) Pσ (Mv.pt x) (Mc.pt x) _ (Mv.tan x) hv₀ a3
  have h6 : h.ip _ (Mc.pt x) (Mc.pt x) = (B.metric.form σ).inner x x := by
    rw [h1]
    exact ip_congr h.ip hb.symm (hMc x) (hMc x)
  rw [h6] at h5
  exact h5
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeSpecializationValueStatement
section
open ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_specialization_value : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [NormedField 𝕜] [IsUltrametricDist 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → ∀ (A : Subring Ω) (ev : A →+* 𝕜) (a : K → ℤ), ∀ s ∈ chartLatNm y a 1, (∀ (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ k i, ∃ hb : y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A, Small.HasVal y 0 (y ⟨k, i⟩ / y ⟨k, c k⟩) z (ev ⟨_, hb⟩)) ∧ ∃ hb : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) ∈ A, Small.HasVal y 0 (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) z (ev ⟨_, hb⟩)) → ∃ w, Small.HasVal y a s z w ∧ ‖w‖ ≤ Small.supMet a z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt.exists_hasVal_norm_le_supMet | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt.exists_hasVal_norm_le_supMet | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt.exists_hasVal_norm_le_supMet <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrCoordRatioValue
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem chart_point : ∀ (X : AlgebraicGeometry.Scheme.{0}) (Ω : Type) [Field Ω] (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (A : Subring Ω) (T : CDVR) (evT : A →+* T.Fr) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ (hr : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A), (∀ k i, evT ⟨_, hr k i⟩ ∈ (algebraMap T.V T.Fr).range) → (∀ a : A, ∃ b : A, evT b ≠ 0 ∧ (b : Ω) ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩) ∧ (a : Ω) * b ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩)) → ∃ (zV : AlgebraicGeometry.Spec (CommRingCat.of T.V) ⟶ X) (h : genPt ξ ⤳ centre zV), InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre zV, h⟩ ∧ FinRd.Roots.ReadsPt ξ A T evT zV := by
  intro X Ω _ ξ K _ J _ y hall tie A T evT c hc hr hint hfrac
  classical
  have hx : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  obtain ⟨U, hU, hmem⟩ := tie.affine c hx
  have hCeq : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) =
      Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩) :=
    (TiePrimes.adjoin_eq hc).trans (Algebra.adjoin_range_eq_range_aeval ℤ _).symm

  have hgU : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, CoordMap.inChart_genPt tie.gen _ c hx specializes_rfl⟩
  let e : Γ(X, U) →+* Ω := (genMap ξ ⟨genPt ξ, specializes_rfl⟩).comp (X.presheaf.germ U _ hgU).hom
  have he : ∀ {p : X} (hp : p ∈ U) (t : Γ(X, U)), genMap ξ ⟨p, hall p⟩ (X.presheaf.germ U p hp t) = e t := by
    intro p hp t
    show _ = genMap ξ ⟨genPt ξ, specializes_rfl⟩ (X.presheaf.germ U _ hgU t)
    rw [RootHt.ArchC.genMap_germ U (hall p) hp t, RootHt.ArchC.genMap_germ U specializes_rfl hgU t]
  have hC : ∀ t, e t ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩) := fun t => by
    rw [← hCeq]
    exact (tie.ring c hx (e t)).2 fun p hp =>
      ⟨X.presheaf.germ U p.1 ((hmem p.1).2 ⟨p.2, hp⟩) t, he _ t⟩

  let S : Subring Ω := ((algebraMap T.V T.Fr).range.comap evT).map A.subtype
  have hCS : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩), a ∈ S := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      exact ⟨⟨_, hr j.1 j.2⟩, hint j.1 j.2, rfl⟩
    | algebraMap n => simpa using intCast_mem S n
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  have hAm : ∀ t, e t ∈ A := fun t => by
    obtain ⟨b, -, hb⟩ := hCS _ (hC t)
    rw [← hb]
    exact b.2
  let e' : Γ(X, U) →+* A := e.codRestrict A hAm
  let ev : Γ(X, U) →+* T.Fr := evT.comp e'
  have hev : ∀ t, ev t ∈ (algebraMap T.V T.Fr).range := fun t => by
    obtain ⟨b, hb, hb'⟩ := hCS _ (hC t)
    have : b = e' t := Subtype.ext hb'
    show evT (e' t) ∈ _
    rw [← this]
    exact hb

  obtain ⟨g, hg⟩ : ∃ g : Γ(X, U) →+* T.V, (algebraMap T.V T.Fr).comp g = ev := by
    have hι : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
    let eV : T.V ≃+* (algebraMap T.V T.Fr).range :=
      RingEquiv.ofBijective (algebraMap T.V T.Fr).rangeRestrict
        ⟨fun a b h => hι (congrArg Subtype.val h), (algebraMap T.V T.Fr).rangeRestrict_surjective⟩
    refine ⟨eV.symm.toRingHom.comp (ev.codRestrict _ hev), RingHom.ext fun t => ?_⟩
    exact congrArg Subtype.val (eV.apply_symm_apply (ev.codRestrict _ hev t))
  have h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have hcV : centre (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec : Spec (CommRingCat.of T.V) ⟶ X) ∈ U :=
    h0 (Set.mem_univ (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint T.V)))
  obtain ⟨hV, hinV⟩ := (hmem _).1 hcV
  refine ⟨_, hV, hinV, ?_⟩

  have hz : gen T (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) =
      Spec.map (CommRingCat.ofHom ev) ≫ hU.fromSpec := by
    rw [gen, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg]
  obtain ⟨hcz, hgerm⟩ := RootHt.ArchC.point_of_ringHom hU ev
  obtain ⟨hgz, hchz⟩ := (hmem _).1 hcz
  have hval : ∀ a : A, (a : Ω) ∈ regAt ξ ⟨_, hgz⟩ →
      ValAt ξ (Spec.map (CommRingCat.ofHom ev) ≫ hU.fromSpec) (a : Ω) (evT a) := by
    intro a ha
    refine RootHt.ArchC.val_of_fractions hU hcz hgz ev hgerm ha fun t₁ t₂ h => ?_
    rw [he hcz, he hcz] at h
    have h' : a * e' t₂ = e' t₁ := Subtype.ext h
    have h'' := congrArg evT h'
    rwa [map_mul] at h''
  have hreg : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩),
      a ∈ regAt ξ ⟨_, hgz⟩ := fun a ha =>
    (tie.ring c hx a).1 (hCeq ▸ ha) _ hchz
  intro a
  rw [hz]
  refine hval a ?_
  obtain ⟨b, hb0, hbC, habC⟩ := hfrac a
  obtain ⟨h', s, hs1, hs2⟩ := hval b (hreg _ hbC)
  obtain ⟨s₂, hs₂⟩ := hreg _ habC
  have hu : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' _).map_nonunit s (by
    rw [hs2]
    exact isUnit_iff_ne_zero.2 hb0)
  obtain ⟨u, rfl⟩ := hu
  have hb1 : (b : Ω) * genMap ξ ⟨_, hgz⟩ (↑u⁻¹ : X.presheaf.stalk _) = 1 := by
    rw [← hs1, ← map_mul, Units.mul_inv, map_one]
  refine ⟨s₂ * ↑u⁻¹, ?_⟩
  rw [map_mul, hs₂, _root_.mul_assoc, hb1, _root_.mul_one]

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrLieModelLattice
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
private theorem exists_unitary_diagonal_of_isHermitian {X : Scheme.{0}} (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X)
    (c : centre (FinRd.Roots.gen T zV) ⤳ centre zV) :
    X.presheaf.stalkSpecializes c ≫ Scheme.stalkClosedPointTo (FinRd.Roots.gen T zV) =
      Scheme.stalkClosedPointTo zV ≫ CommRingCat.ofHom (algebraMap T.V T.Fr) := by
  have c' := IsLocalRing.specializes_closedPoint
    ((Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) (IsLocalRing.closedPoint T.Fr))
  have e2 := Scheme.stalkClosedPointTo_comp (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) zV
  have e3 := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom (algebraMap T.V T.Fr))
  have e4 := ΓSpecIso_hom_stalkClosedPointIso_inv (CommRingCat.of T.V)
  have e4' : (stalkClosedPointIso (CommRingCat.of T.V)).inv =
      (Scheme.ΓSpecIso (CommRingCat.of T.V)).inv ≫
        (Spec (CommRingCat.of T.V)).presheaf.germ ⊤ (IsLocalRing.closedPoint _) trivial := by
    rw [← e4, Iso.inv_hom_id_assoc]
  have e6 := TopCat.Presheaf.germ_stalkSpecializes (Spec (CommRingCat.of T.V)).presheaf
    (U := ⊤) (y := IsLocalRing.closedPoint _) trivial c'
  have e5 : (Spec (CommRingCat.of T.V)).presheaf.stalkSpecializes c' ≫
      Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) =
      (stalkClosedPointIso (CommRingCat.of T.V)).hom ≫ CommRingCat.ofHom (algebraMap T.V T.Fr) := by
    rw [← Iso.inv_comp_eq, e4', Category.assoc]
    erw [reassoc_of% e6]
    erw [e3]
    rw [Iso.inv_hom_id_assoc]
  change X.presheaf.stalkSpecializes c ≫ Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ zV) = _
  rw [e2]
  erw [Scheme.Hom.stalkSpecializes_stalkMap_assoc zV _ _ c']
  rw [e5, Scheme.stalkClosedPointTo, Category.assoc]

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.complete_dvr_lie_model_lattice : ∀ (X : AlgebraicGeometry.Scheme.{0}) (G : CategoryTheory.Over X) [CategoryTheory.GrpObj G] [CategoryTheory.IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) (L₀ : Type) [AddCommGroup L₀] [Module Ω L₀] (M : LieModel G ξ L₀) (T : CDVR) (zV : AlgebraicGeometry.Spec (CommRingCat.of T.V) ⟶ X) (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel G (FinRd.Roots.gen T zV) EC) (A : Subring Ω) (evT : A →+* T.Fr), IsCptGen ξ → AlgebraicGeometry.Smooth G.hom → ∀ (h : genPt ξ ⤳ centre zV), genPt ξ ⤳ centre (FinRd.Roots.gen T zV) → FinRd.Roots.ReadsPt ξ A T evT zV → ∀ (L : Lat ξ L₀) (r : ℕ) (b e : Fin r → L₀) (Tm : Matrix (Fin r) (Fin r) Ω) (w : Fin r → EC) (hT : ∀ i j, Tm i j ∈ A), L.IsFrameAt b ⟨centre zV, h⟩ → (∀ i, b i = ∑ j, Tm i j • e j) → (∀ j, M.ValAt (FinRd.Roots.gen T zV) (e j) (MC.pt (w j))) → M.fibAt L zV MC = Submodule.span T.V (Set.range fun i => ∑ j, evT ⟨Tm i j, hT i j⟩ • w j) := by
  intro X G _ _ Ω _ ξ L₀ _ _ M T zV EC _ _ _ _ MC A evT hX _ h hz hR L r b e Tm w hT hF hb hw
  obtain ⟨-, hF2⟩ := hF
  have c : centre (FinRd.Roots.gen T zV) ⤳ centre zV :=
    zV.base.hom.map_specializes (IsLocalRing.specializes_closedPoint _)
  have hK : ∀ s, (Scheme.stalkClosedPointTo (FinRd.Roots.gen T zV)).hom
      (ConcreteCategory.hom (X.presheaf.stalkSpecializes c) s) =
      algebraMap T.V T.Fr ((Scheme.stalkClosedPointTo zV).hom s) := by
    intro s
    have := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (exists_unitary_diagonal_of_isHermitian T zV c)) s
    first
      | exact this
      | simpa only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] using this
  have hsc : ∀ {x : L₀} {y : EC}, M.ValAt (FinRd.Roots.gen T zV) x (MC.pt y) →
      ∀ s : X.presheaf.stalk (centre (FinRd.Roots.gen T zV)),
        M.ValAt (FinRd.Roots.gen T zV) (genMap ξ ⟨centre (FinRd.Roots.gen T zV), hz⟩ s • x)
          (MC.pt ((Scheme.stalkClosedPointTo (FinRd.Roots.gen T zV)).hom s • y)) := by
    intro x y hxy s
    have := LieModel.ValAt.smul hxy hz s
    rwa [← LieModel.pt_smul] at this
  have hzero : ∀ {x : L₀} {y : EC}, M.ValAt (FinRd.Roots.gen T zV) x (MC.pt y) →
      M.ValAt (FinRd.Roots.gen T zV) 0 (MC.pt 0) := by
    intro x y hxy
    have := hsc hxy 0
    rw [map_zero, zero_smul] at this
    erw [map_zero, zero_smul] at this
    exact this
  have hsum : ∀ (s : Finset (Fin r)) (f : Fin r → L₀) (g : Fin r → EC),
      M.ValAt (FinRd.Roots.gen T zV) 0 (MC.pt 0) →
      (∀ j ∈ s, M.ValAt (FinRd.Roots.gen T zV) (f j) (MC.pt (g j))) →
        M.ValAt (FinRd.Roots.gen T zV) (∑ j ∈ s, f j) (MC.pt (∑ j ∈ s, g j)) := by
    intro s f g h0 hf
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, MC.add]
      exact LieModel.ValAt.add (hf a (Finset.mem_insert_self a s))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
  have hA : ∀ (a : A) (j : Fin r),
      M.ValAt (FinRd.Roots.gen T zV) ((a : Ω) • e j) (MC.pt (evT a • w j)) := by
    intro a j
    obtain ⟨h1, s, hs1, hs2⟩ := hR a
    have := hsc (hw j) s
    rw [hs1, hs2] at this
    exact this
  have hv : ∀ i, M.ValAt (FinRd.Roots.gen T zV) (b i)
      (MC.pt (∑ j, evT ⟨Tm i j, hT i j⟩ • w j)) := by
    intro i
    rw [hb i]
    exact hsum _ _ _ (hzero (hw i)) (fun j _ => hA ⟨Tm i j, hT i j⟩ j)
  unfold LieModel.fibAt
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro w' ⟨h', x, hx, hxv⟩
    have hx' : x ∈ Submodule.span (regAt ξ ⟨centre zV, h⟩) (Set.range b) := by
      rw [← hF2]
      exact hx
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hx'
    choose s hs using fun i => RingHom.mem_range.mp (cf i).2
    have key : M.ValAt (FinRd.Roots.gen T zV) x
        (MC.pt (∑ i, algebraMap T.V T.Fr ((Scheme.stalkClosedPointTo zV).hom (s i)) •
          ∑ j, evT ⟨Tm i j, hT i j⟩ • w j)) := by
      rw [← hcf]
      refine hsum _ _ _ (hzero hxv) fun i _ => ?_
      have := hsc (hv i) (ConcreteCategory.hom (X.presheaf.stalkSpecializes c) (s i))
      rw [LieTangent.genMap_specializes ⟨centre zV, h⟩ hz c, hK, hs i] at this
      rw [Subring.smul_def]
      exact this
    have hw' := MC.inj (LieModel.ValAt.unique hX hxv key)
    rw [hw']
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨h, b i, ?_, hv i⟩
    rw [hF2]
    exact Submodule.subset_span ⟨i, rfl⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataAbelianPartBoundStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_val_at_vert_factor_eq_norm_mul_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ Or.𝔐.X) (w : (Σ k, J k) → L) (cc : (k : K) → J k) (p : ℕ), CoordsAt Or.𝔐.ξ Dc.y z w → (∀ k, w ⟨k, cc k⟩ ≠ 0) → p ∈ Dc.S → ∃ t : L, t ≠ 0 ∧ ValAt Or.𝔐.ξ z (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) * chartMono Dc.y cc (-Dc.vdeg p)) t ∧ ∀ e : L →+* ℂ, Dc.vertFactor p (fun i => e (w i)) = ‖e t‖ * ∏ k, ‖e (w ⟨k, cc k⟩)‖ ^ Dc.vdeg p k := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert.vertical_value | exact GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert.vertical_value | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert.vertical_value <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFiniteKernelNonzeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_kernel_nonzero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : SAB H (Sp k)), IsProper t.G.hom → ∀ (d : ℕ) (_ : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E), a ≠ 0 → (∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (_ : Module.Finite k A) (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left) ∧ ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left → Module.finrank k A ^ Module.finrank ℚ E = (Algebra.norm ℤ a).natAbs ^ (2 * d) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.finrank_kernel_pow_degree_eq_norm_pow | exact GlobalTheory.CompanionTheory.Ar.Flat.finrank_kernel_pow_degree_eq_norm_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.finrank_kernel_pow_degree_eq_norm_pow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormalGermLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formal_germ_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0), ∃ d, Nonempty (GermAt t x d) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.germAt_exists_of_isLocalRing | exact GlobalTheory.CompanionTheory.Ar.Conj.germAt_exists_of_isLocalRing | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.germAt_exists_of_isLocalRing <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormOffSpecializationRingStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.form_off_specialization_ring : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω), Birational y → ∀ B : Finset Ω, ∃ u : MRing ι, Small.IsFormOff (mCoordIdeal y) u ∧ ∀ (𝕜 : Type) [Field 𝕜] [CharZero 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → MvPolynomial.aeval z u ≠ 0 → ∃ (A : Subring Ω) (ev : A →+* 𝕜), (↑B : Set Ω) ⊆ A ∧ (∀ n : ℕ, n ≠ 0 → ((n : Ω))⁻¹ ∈ A) ∧ ∀ x : A, Small.HasVal y 0 (x : Ω) z (ev x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub.exists_subring_val | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub.exists_subring_val | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub.exists_subring_val <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointFactorsOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_factors_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ Y.X), GlobalTheory.CompanionTheory.Ar.genPt ξ ∈ genericPoints Y.X → ∃ y₀ : Sp Ω ⟶ Xo.XF c, ξ = y₀ ≫ Y.j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChangeGeo.exists_factor_XF_of_genericPoint | exact GlobalTheory.CompanionTheory.Ar.ChangeGeo.exists_factor_XF_of_genericPoint | (intros; apply GlobalTheory.CompanionTheory.Ar.ChangeGeo.exists_factor_XF_of_genericPoint <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelCoverStHoldsStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.LevelCoverSt_holds : GlobalTheory.CompanionTheory.Ar.XR.LevelCoverSt := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.levelCover | exact GlobalTheory.CompanionTheory.Ar.XR.levelCover | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.levelCover <;> assumption)
end

