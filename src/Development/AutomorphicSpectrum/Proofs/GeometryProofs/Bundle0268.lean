import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0267
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0006
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsThetaFrameMulUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0172
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryDiscMapEmbeddingFixed
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.ModelChart

theorem exists_bdryChart_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (X' : Scheme.{0}) (jx : X' ⟶ Y.X) (t : SAB H X') (m : SABMap t Y.t jx) (τ : c.F →+* ℂ) (n a : ℕ) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X')), a ≤ n → IsHolTo (Metric.ball 0 1) p → (∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p u ≫ jx ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F))) → (∀ u ∈ Flat.punct n a 1, ∀ x : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)), x ≫ pullback.fst _ _ = p u ≫ jx → Set.range x ⊆ Set.range Y.jQ) → ∃ (ρ : ℝ) (C : Flat.BdryChart Xo (τ.comp (IntermediateField.inclusion c.le).toRingHom) n a) (h : Sp C.R ⟶ X'), 0 < ρ ∧ ρ ≤ 1 ∧ Nonempty (SABMap C.t t h) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (C.ψ z) ≫ h = p ((ρ : ℂ) • z) := by
  intro E _ _ _ H D l Xo c Y X' jx t m τ n a p han hp hs hpt
  classical
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  let fP := pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))
  let sZ := pullback.snd jx fP
  let fZ := pullback.fst jx fP
  let j := pullback.fst sZ Y.jQ
  let g := pullback.snd sZ Y.jQ
  have := Y.jQ_open
  have hj : IsOpenImmersion j := inferInstance
  let k : pullback sZ Y.jQ ⟶ Xo.X := g ≫ pullback.fst _ _

  obtain ⟨tZ, ⟨mZ⟩⟩ := exists_sab fZ t
  obtain ⟨tU, ⟨mU⟩⟩ := exists_sab g Y.oF.t
  obtain ⟨q₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m mZ
  obtain ⟨q₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp Y.m mU
  have e₁ : g ≫ Y.jQ ≫ fP = j ≫ fZ ≫ jx := by
    have a₁ : j ≫ sZ = g ≫ Y.jQ := pullback.condition
    have a₂ : fZ ≫ jx = sZ ≫ fP := pullback.condition
    rw [a₂, ← Category.assoc g, ← a₁, Category.assoc]
  rw [e₁] at q₂
  have q₁' : SABMap tZ Y.t (fZ ≫ jx) := q₁
  obtain ⟨mj, -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel q₁' q₂
  obtain ⟨mk, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp Y.m0.toSABMap mU

  let p' : (Fin n → ℂ) → (Sp ℂ ⟶ X') := fun u => if u ∈ Metric.ball (0 : Fin n → ℂ) 1 then p u else p 0
  have hp'e : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p' u = p u := fun u hu => if_pos hu
  have hp' : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1) p' := GlobalTheory.LocLift.isHolTo_congr hp hp'e
  have hs' : ∀ u, (p' u ≫ jx) ≫ Y.s = spMap τ ≫ spMap (algebraMap (𝓞 c.F) c.F) := fun u => by
    have : p' u ≫ jx ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)) := by
      by_cases hu : u ∈ Metric.ball (0 : Fin n → ℂ) 1
      · rw [hp'e u hu]; exact hs u hu
      · simp only [p', if_neg hu]; simpa [h0] using hs 0 h0
    rw [Category.assoc, this]
    simp [spMap]
  let q : (Fin n → ℂ) → (Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    fun u => pullback.lift (p' u ≫ jx) (spMap τ) (hs' u)
  have hq : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1) q :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.holPair _ _ _ Y.s (spMap (algebraMap (𝓞 c.F) c.F)) n _ _ _ hs' Metric.isOpen_ball
      (GlobalTheory.LocLift.isHolTo_comp_hom hp' jx) (GlobalTheory.PeriodTests.isHolTo_const Metric.isOpen_ball _)
  have hc : ∀ u, p' u ≫ jx = q u ≫ fP := fun u => (pullback.lift_fst _ _ _).symm
  let y : (Fin n → ℂ) → (Sp ℂ ⟶ pullback jx fP) := fun u => pullback.lift (p' u) (q u) (hc u)
  have hy : IsHolTo (Metric.ball (0 : Fin n → ℂ) 1) y :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.holPair _ _ _ jx fP n _ _ _ hc Metric.isOpen_ball hp' hq
  have hpu : ∀ z ∈ Flat.punct n a 1, ∃ w : Sp ℂ ⟶ pullback sZ Y.jQ, w ≫ j = y z ∧
      w ≫ k ≫ Xo.s = spMap (τ.comp (IntermediateField.inclusion c.le).toRingHom) := fun z hz => by
    have hr : Set.range (q z) ⊆ Set.range Y.jQ :=
      hpt z hz (q z) ((pullback.lift_fst _ _ _).trans (by rw [hp'e z hz.1]))
    let w₀ := IsOpenImmersion.lift Y.jQ (q z) hr
    have hw₀ : w₀ ≫ Y.jQ = q z := IsOpenImmersion.lift_fac _ _ _
    have hys : y z ≫ sZ = w₀ ≫ Y.jQ := (pullback.lift_snd _ _ _).trans hw₀.symm
    refine ⟨pullback.lift (y z) w₀ hys, pullback.lift_fst _ _ _, ?_⟩
    have h₁ : pullback.lift (y z) w₀ hys ≫ k = w₀ ≫ pullback.fst _ _ := by
      simp only [k, g]; rw [pullback.lift_snd_assoc]
    rw [← Category.assoc, h₁, Category.assoc, pullback.condition, ← Category.assoc]
    have h₂ : w₀ ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) = spMap τ := by
      rw [← Y.jQ_over, ← Category.assoc, hw₀]
      exact pullback.lift_snd _ _ _
    rw [h₂]
    simp [spMap]
  obtain ⟨ρ, C, i, e, hρ, hρ1, -, ⟨mi⟩, -, -, hψ⟩ :=
    Flat.exists_bdryChart_of_hol E H D l Xo (τ.comp (IntermediateField.inclusion c.le).toRingHom) _ tZ _ j k tU n a y
      han hj ⟨mj⟩ ⟨mk⟩ hy hpu
  obtain ⟨mh, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mZ mi
  refine ⟨ρ, C, i ≫ fZ, hρ, hρ1, ⟨mh⟩, fun z hz => ?_⟩
  have hin : (ρ : ℂ) • z ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    nlinarith [norm_nonneg z]
  rw [← Category.assoc, hψ z hz, ← hp'e _ hin]
  exact pullback.lift_fst _ _ _

end GlobalTheory.CompanionTheory.Ar.ModelChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscInAffineOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_disc_in_affine_open : ∀ (X : Scheme.{0}) (W : X.Opens) (hW : IsAffineOpen W) (n : ℕ) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X)), IsHolTo (Metric.ball 0 1) p → ⊤ ≤ p 0 ⁻¹ᵁ W → ∃ (ρ : ℝ) (ψ : (Fin n → ℂ) → (Γ(X, W) →+* ℂ)), 0 < ρ ∧ ρ ≤ 1 ∧ Flat.IsHolPts (Metric.ball 0 1) ψ ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (ψ z) ≫ hW.fromSpec = p ((ρ : ℂ) • z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HolFac.exists_ringMaps_of_hol | exact GlobalTheory.CompanionTheory.Ar.HolFac.exists_ringMaps_of_hol | (intros; apply GlobalTheory.CompanionTheory.Ar.HolFac.exists_ringMaps_of_hol <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTangentVectorsAffineOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_tangent_vectors_affine_open : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (q : Cpt ξ) (N : ℕ) (b : Fin N → Li), IsCptGen ξ → (∀ k, b k ∈ M.lat q) → ∃ (W : X.Opens) (hW : IsAffineOpen W) (v : Fin N → (epsAt (R := Γ(X, W)) hW.fromSpec ⟶ G)), q.1 ∈ W ∧ (∀ k, IsTanAt G hW.fromSpec (v k)) ∧ ∀ (ψ : Γ(X, W) →+* ℂ) (z : Sp ℂ ⟶ X), spMap ψ ≫ hW.fromSpec = z → genPt ξ ⤳ centre z → ∀ k, ∃ w : epsAt z ⟶ G, M.ValAt z (b k) w ∧ w.left = spMap (dualMap ψ) ≫ (v k).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameExt.exists_affine_frame | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameExt.exists_affine_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameExt.exists_affine_frame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelLocalSubringPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameDual

theorem exists_frame_dual_sq : ∀ (S X : Scheme.{0}) (G : Over S) [GrpObj G] (Gx : Over X) [GrpObj Gx] [IsCommMonObj Gx] [Smooth Gx.hom] (φ : Gx.left ⟶ G.left) (Ω₁ : Type) [Field Ω₁] (ξ : Spec (CommRingCat.of Ω₁) ⟶ X), IsCptGen ξ → ∀ (Li : Type) [AddCommGroup Li] [Module Ω₁ Li] (M : LieModel Gx ξ Li) (F : Type) [Field F] (θ : Ω₁ →+* F) (A : Subring F) [IsLocalRing A] (z : Spec (CommRingCat.of A) ⟶ X) (h : genPt ξ ⤳ centre z), (∀ s : X.presheaf.stalk (centre z), (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s)) → ∀ (ER : Type) [AddCommGroup ER] [Module A ER] (MR : LieModel Gx z ER) (xF : Spec (CommRingCat.of F) ⟶ S) (V : Type) [AddCommGroup V] [Module F V] (MV : LieModel G xF V) (io : ER → V) (Lm : Li → V), (∀ x, (MV.pt (io x)).left = Spec.map (CommRingCat.ofHom (dualMap A.subtype)) ≫ (MR.pt x).left ≫ φ) → (∀ e, (MV.pt (Lm e)).left = Spec.map (CommRingCat.ofHom (dualMap θ)) ≫ (M.pt e).left ≫ φ) → ∀ (r : ℕ) (b : Fin r → Li) (π : Fin r → Module.Dual Ω₁ Li) (m : ℕ), (∀ i, (m : Ω₁) • b i ∈ M.lat ⟨centre z, h⟩) → (∀ i j, π i (b j) = if i = j then 1 else 0) → (∀ i, ∀ e ∈ M.lat ⟨centre z, h⟩, (m : Ω₁) * π i e ∈ regAt ξ ⟨centre z, h⟩) → ∃ (β : Fin r → ER) (g : Fin r → ER →ₗ[A] A), (∀ k, io (β k) = Lm ((m : Ω₁) • b k)) ∧ ∀ i k, ((g i (β k) : A) : F) = if k = i then (m : F) ^ 2 else 0 := by
  intro S X G _ Gx _ _ _ φ Ω₁ _ ξ hξ Li _ _ M F _ θ A _ z h hs ER _ _ MR xF V _ _ MV io Lm hio hLm r b π m hm hπ hreg
  obtain ⟨ev, hev, -, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X Gx Ω₁ ξ Li M A z h ER MR hξ inferInstance
  let β : Fin r → ER := fun k => ev ⟨(m : Ω₁) • b k, hm k⟩
  have hval : ∀ k, M.ValAt z ((m : Ω₁) • b k) (MR.pt (β k)) := fun k => (hev _ _).2 ⟨hm k, rfl⟩
  have hcomp : A.subtype.comp (Scheme.stalkClosedPointTo z).hom = θ.comp (genMap ξ ⟨centre z, h⟩) :=
    RingHom.ext fun s => hs s
  have hg : ∀ i, ∃ g : ER →ₗ[A] A, ∀ (e : Li) (x : ER) (u : A), M.ValAt z e (MR.pt x) →
      ValAt ξ z (((m : Ω₁) • π i) e) u → g x = u := fun i =>
    GlobalTheory.CompanionTheory.Ar.RootHt.exists_lieFunctional X Gx Ω₁ ξ Li M A z h ER MR ((m : Ω₁) • π i) hξ
      (fun e he => by simpa [smul_eq_mul] using hreg i e he)
  choose g hg using hg
  refine ⟨β, g, fun k => ?_, fun i k => ?_⟩
  · obtain ⟨h', v, hext, hw⟩ := hval k
    have e1 := GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameExt.spec_dual_comp (Scheme.stalkClosedPointTo z).hom A.subtype
    have e2 := GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameExt.spec_dual_comp (genMap ξ ⟨centre z, h⟩) θ
    apply MV.inj
    apply Over.OverMorphism.ext
    rw [hio, hLm, hext.2, hw]
    simp only [Category.assoc]
    rw [← Category.assoc (Spec.map (CommRingCat.ofHom (dualMap A.subtype))),
      ← Category.assoc (Spec.map (CommRingCat.ofHom (dualMap θ))), e1, e2, hcomp]
  · have hnat : ∀ n : ℕ, ValAt ξ z (n : Ω₁) (n : A) := fun n =>
      ⟨h, (n : X.presheaf.stalk (centre z)), map_natCast _ n, map_natCast _ n⟩
    have hv : ((m : Ω₁) • π i) ((m : Ω₁) • b k) = ((if k = i then m ^ 2 else 0 : ℕ) : Ω₁) := by
      by_cases e : k = i
      · subst e
        simp [hπ, smul_eq_mul, pow_two]
      · have e' : ¬ i = k := fun q => e q.symm
        simp [hπ, e, e']
    have h1 := hg i _ (β k) _ (hval k) (hv ▸ hnat _)
    rw [h1]
    by_cases e : k = i <;> simp [e]

end GlobalTheory.CompanionTheory.Ar.HodgeMetric.FrameDual
end
end

