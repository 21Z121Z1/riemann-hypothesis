import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0161
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0046
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0021
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0185
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0081
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0184
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0080
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0079
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0157
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0163
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericCoordsDescendSubfield
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.WeilBound.CoreStatements.HodgeTatePoints.Famproj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import Development.WeilBound.CoreStatements.AmpleLineBundles.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0186
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0108
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCoordsOfGenericPoint
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem exists_model_of_res (hRes : ResK.ResKStatement)
    (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)) (hp : IsProjOver s)
    (hn : Tor.IsNormalScheme P) (U : (pullback s (spMap (algebraMap (𝓞 F) F))).Opens) (hd : Dense (U : Set ((pullback s (spMap (algebraMap (𝓞 F) F)) : Scheme.{0})))) (e : ℕ)
    (hU : SmoothOfRelativeDimension e (U.ι ≫ pullback.snd s (spMap (algebraMap (𝓞 F) F))))
    (Ab : Set P) (hAb : pullback.fst s (spMap (algebraMap (𝓞 F) F)) ⁻¹' Ab = U)
    (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Sp Ω ⟶ P) (hξ₀ : IsCptGen ξ₀) :
    ∃ (N : ℕ) (x : Fin (N + 1) → Ω) (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (f : X ⟶ P)
      (bd : Ideal (MRing (fun _ : Unit => Fin (N + 1)))),
      (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ x ∧ ξ ≫ f = ξ₀ ∧
      Cmp.IsSncModel (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) e bd ∧
      ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) z w →
        (w ∈ mcPts bd ↔ f (centre z) ∉ Ab) := by
  obtain ⟨hred, hln, M, i, hi, his⟩ := GlobalTheory.T.generic_fibre_projective_embedding F P s hp hn
  obtain ⟨b, ξF, hF1, hF2, hFg⟩ := GlobalTheory.T.generic_point_generic_fibre F P s Ω ξ₀ hξ₀
  have hmem := GlobalTheory.T.generic_point_mem_dense_open _ Ω ξF U hFg hd
  have hin : ResK.IsResInput M i U e := ⟨hi, hred, hd, by rw [his]; exact hU⟩
  obtain ⟨r, X', j, f', hj, hfj, hsm, hiso, hdense, hsnc⟩ := hRes F M e _ i U hin
  letI algF : Algebra F Ω := b.toAlgebra
  letI algO : Algebra (𝓞 F) Ω := (b.comp (algebraMap (𝓞 F) F)).toAlgebra
  haveI : IsScalarTower (𝓞 F) F Ω := .of_algebraMap_eq' rfl
  have hs0 : ξ₀ ≫ s = spMap (algebraMap (𝓞 F) Ω) := by
    rw [← hF1, Category.assoc, pullback.condition, ← Category.assoc, hF2]
    show _ = Spec.map (CommRingCat.ofHom (b.comp (algebraMap (𝓞 F) F)))
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  obtain ⟨nu, u, hu⟩ := GlobalTheory.T.projective_over_coords_exist (𝓞 F) P s hp Ω ξ₀ hξ₀ hs0
  have hproj : IsProjOver (f' ≫ i ≫ PSpace.str F M) := by
    have := GlobalTheory.T.closed_in_product_projective F M r X' j hj
    rwa [← Category.assoc, ← hfj, Category.assoc] at this
  have hdom := GlobalTheory.T.smooth_scheme_stalks_domains F e X' _ hsm
  obtain ⟨ξ', h1, hξ'⟩ := GlobalTheory.T.generic_point_lift_along_iso _ X' f' U Ω ξF hiso hmem hFg hdom
  have hξs : ξ' ≫ f' ≫ i ≫ PSpace.str F M = spMap (algebraMap F Ω) := by
    rw [← Category.assoc, h1, his, hF2]
  obtain ⟨nx, x2, hx2⟩ := GlobalTheory.T.projective_over_coords_exist F X' _ hproj Ω ξ' hξ' hξs
  have hg : ξ' ≫ (f' ≫ pullback.fst _ _) = ξ₀ := by rw [← Category.assoc, h1, hF1]
  have hbase := GlobalTheory.T.every_component_in_some_chart X' P Ω ξ' ξ₀ _ (𝓞 F) _ u hu hg
  obtain ⟨n, ht⟩ := GlobalTheory.T.coords_product_refinement X' Ω ξ' F _ _ x2 u hx2 hbase
  obtain ⟨c₀, hc₀, hfrac⟩ := GlobalTheory.T.coords_generate_function_field (𝓞 F) F Ω X' ξ' _ _ ht
  obtain ⟨X, ξ, sX, htX, hirr, -, -, -⟩ := GlobalTheory.T.exists_proper_integral_model Ω (𝓞 F) _ _ c₀ hc₀ hfrac
  have hreg : ∀ (a : 𝓞 F) (p : Cpt ξ), (RingHom.id Ω) (algebraMap (𝓞 F) Ω a) ∈ regAt ξ p := by
    intro a p
    obtain ⟨c, hc⟩ := htX.cover p
    exact (htX.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ a) p hc
  have hchart : ∀ p : Cpt ξ, ∃ c, InChart ξ (fun k => (RingHom.id Ω) (u k)) c p := by
    intro p
    obtain ⟨⟨q1, q2, q3⟩, h0, hc⟩ := htX.cover p
    have hne := h0
    simp only [mul_ne_zero_iff] at hne
    refine ⟨q3, hne.2, fun c' => ?_⟩
    have := hc ⟨q1, q2, c'⟩
    have e1 : ((∏ a, x2 (q1 a)) * x2 q2 * u c') / ((∏ a, x2 (q1 a)) * x2 q2 * u q3) = u c' / u q3 := by
      field_simp [hne.1.1, hne.1.2, hne.2]
    simpa [e1] using this
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.dominates_of_coords_regular P Ω ξ₀ (𝓞 F) _ u X Ω ξ (RingHom.id Ω) hu htX.gen hirr hreg hchart
  have hf' : ξ ≫ f = ξ₀ := by
    have : ξ ≫ f = _ := hf
    rw [this]; simp
  obtain ⟨N, x, hx⟩ := GlobalTheory.T.coord_over_int_of_finite_order X Ω ξ (𝓞 F) _ _ htX
  obtain ⟨R1, R2⟩ := GlobalTheory.T.coord_charts_match_regular (𝓞 F) F Ω X X' ξ ξ' _ _ htX ht
  have hchar := GlobalTheory.T.char_zero_iff_nonzero_units F Ω X ξ _ _ htX
  have hFreg : ∀ (a : F) (p' : Cpt ξ'), algebraMap F Ω a ∈ regAt ξ' p' := by
    intro a p'
    obtain ⟨c, hc⟩ := ht.cover p'
    exact (ht.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ a) p' hc
  have hunit : ∀ (p : Cpt ξ) (p' : Cpt ξ'), regAt ξ p = regAt ξ' p' → Char0 ξ p := by
    intro p p' h
    refine (hchar p).2 fun d hd0 => ?_
    have hd1 : (algebraMap (𝓞 F) F d) ≠ 0 := by simpa using hd0
    have e1 : algebraMap (𝓞 F) Ω d = algebraMap F Ω (algebraMap (𝓞 F) F d) := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [e1]; exact (map_ne_zero _).2 hd1
    · rw [h, e1]; exact hFreg _ p'
    · rw [h, e1, ← map_inv₀]; exact hFreg _ p'
  have hPts : Pts ξ = Set.range (regAt ξ') := by
    ext R
    constructor
    · rintro ⟨p, hp0, rfl⟩
      obtain ⟨p', h⟩ := R2 p ((hchar p).1 hp0)
      exact ⟨p', h.symm⟩
    · rintro ⟨p', rfl⟩
      obtain ⟨p, h⟩ := R1 p'
      exact ⟨p, hunit p p' h, h.symm⟩
  let B : Set (Cpt ξ) := {p | Char0 ξ p ∧ f p.1 ∉ Ab}
  let T : Set X' := f'.base ⁻¹' (U : Set ((pullback s (spMap (algebraMap (𝓞 F) F)) : Scheme.{0})))ᶜ
  have hgen : ∀ (p : Cpt ξ) (p' : Cpt ξ'), regAt ξ p = regAt ξ' p' → (f p.1 ∉ Ab ↔ p'.1 ∈ T) := by
    intro p p' h
    have e1 : f p.1 = (f' ≫ pullback.fst _ _) p'.1 :=
      GlobalTheory.T.regular_rings_equal_images_equal P X X' Ω ξ₀ ξ ξ' f _ (𝓞 F) _ u hu htX.gen hξ' hf' hg p p' h
    have e2 : ((f' ≫ pullback.fst s (spMap (algebraMap (𝓞 F) F))) p'.1 ∈ Ab) ↔ f' p'.1 ∈ (U : Set ((pullback s (spMap (algebraMap (𝓞 F) F)) : Scheme.{0}))) := by
      rw [← hAb]; simp
    rw [e1, e2]; rfl
  have hBd : regAt ξ '' B = regAt ξ' '' {p | p.1 ∈ T} := by
    ext R
    constructor
    · rintro ⟨p, ⟨hp0, hp1⟩, rfl⟩
      obtain ⟨p', h⟩ := R2 p ((hchar p).1 hp0)
      exact ⟨p', (hgen p p' h).1 hp1, h.symm⟩
    · rintro ⟨p', hp', rfl⟩
      obtain ⟨p, h⟩ := R1 p'
      exact ⟨p, ⟨hunit p p' h, (hgen p p' h).2 hp'⟩, h⟩
  have hpatch := GlobalTheory.T.snc_patch_at_each_component F X' _ e T Ω ξ' hξ' hξs hsm hsnc (GlobalTheory.T.regular_ring_determines_component X' Ω ξ' F _ _ ht)
  obtain ⟨bd, hm, hc⟩ := GlobalTheory.T.exists_snc_model_of_patches Ω X ξ N x e B hx (fun p hp => hp.1) (by
    intro p hp0
    obtain ⟨p', h⟩ := R2 p ((hchar p).1 hp0)
    rw [hPts, hBd, h]
    exact hpatch p')
  refine ⟨N, x, X, ξ, f, bd, hirr, hx, hf', hm, fun z w hw => ?_⟩
  rw [hc z w hw]
  constructor
  · rintro ⟨h, -, h2⟩
    exact h2
  · intro h
    exact ⟨hirr _, GlobalTheory.T.char_zero_centre_of_complex Ω X ξ z _ htX.gen, h⟩

theorem exists_sncBase : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Spec (CommRingCat.of Ω) ⟶ Y.X), IsCptGen ξ₀ → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y.X) (bd : Ideal (MRing J)), Nonempty K ∧ (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) ∧ ξ ≫ f = ξ₀ ∧ Cmp.IsSncModel y D.dim bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ f (centre z) ∉ abLocus Y.t.G) := by
  intro hRes E _ _ _ H D l Xo c Y Ω _ _ ξ₀ hξ₀
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  haveI := Y.jQ_open
  have hsm : SmoothOfRelativeDimension D.dim (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange D.dim).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  have hU : SmoothOfRelativeDimension D.dim (Y.jQ.opensRange.ι ≫ pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
    apply GlobalTheory.T.smooth_open_immersion_range _ _ _ Y.jQ
    rw [Y.jQ_over]
    exact hsm
  obtain ⟨N, x, X, ξ, f, bd, hirr, hx, hf, hm, hc⟩ := exists_model_of_res hRes c.F Y.X Y.s Y.proj Y.normal Y.jQ.opensRange
    (by simpa using Y.jQ_dense) D.dim hU (abLocus Y.t.G) (by simpa using Y.ab_gen) Ω ξ₀ hξ₀
  exact ⟨Unit, inferInstance, fun _ => Fin (N + 1), fun _ => inferInstance, fun p => x p.2, X, ξ, f, bd, inferInstance,
    hirr, GlobalTheory.T.coords_single_block_segre X Ω ξ N x hx, hf, hm, hc⟩

end GlobalTheory.CompanionTheory.Ar.SncBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDvrThroughDiscPoint
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.Flat

section Curve

variable {R : Type} [CommRing R] {n : ℕ} {ψ : (Fin n → ℂ) → (R →+* ℂ)} {z : Fin n → ℂ}

def diagLine (z : Fin n → ℂ) (T : ℂ) : Fin n → ℂ := fun i => z i + T

theorem diagLine_zero (z : Fin n → ℂ) : diagLine z 0 = z := by
  funext i; simp [diagLine]

theorem diagLine_mem_ball (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) {T : ℂ}
    (hT : T ∈ Metric.ball (0 : ℂ) (1 - ‖z‖)) : diagLine z T ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
  rw [mem_ball_zero_iff] at hT ⊢
  rw [pi_norm_lt_iff one_pos]
  intro i
  have h₁ := norm_le_pi_norm z i
  calc ‖z i + T‖ ≤ ‖z i‖ + ‖T‖ := norm_add_le _ _
    _ < 1 := by linarith

theorem analyticOnNhd_diagLine (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) (x : R) :
    AnalyticOnNhd ℂ (fun T => ψ (diagLine z T) x) (Metric.ball (0 : ℂ) (1 - ‖z‖)) := by
  have hl : DifferentiableOn ℂ (diagLine z) (Metric.ball (0 : ℂ) (1 - ‖z‖)) :=
    (differentiable_pi.2 fun i => (differentiable_const (z i)).add differentiable_id).differentiableOn
  exact ((h.2 x).comp hl fun T hT => diagLine_mem_ball hz hT).analyticOnNhd Metric.isOpen_ball

theorem zero_mem_ball_norm (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (1 - ‖z‖) := by
  have := mem_ball_zero_iff.1 hz
  simpa using this

theorem analyticAt_diagLine (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) (x : R) :
    AnalyticAt ℂ (fun T => ψ (diagLine z T) x) 0 :=
  analyticOnNhd_diagLine h hz x 0 (zero_mem_ball_norm hz)

def taylorHom (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) : R →+* PowerSeries ℂ where
  toFun x := Formalism.L2.Th1.F.taylor0 (fun T => ψ (diagLine z T) x)
  map_one' := by
    simp only [map_one]
    rw [Formalism.L2.Th1.F.Taylor.taylor0_const, map_one]
  map_zero' := by
    simp only [map_zero]
    rw [Formalism.L2.Th1.F.Taylor.taylor0_const, map_zero]
  map_mul' x y := by
    simp only [map_mul]
    exact Formalism.L2.Th1.F.Taylor.taylor0_mul (analyticAt_diagLine h hz x) (analyticAt_diagLine h hz y)
  map_add' x y := by
    simp only [map_add]
    exact Formalism.L2.Th1.F.Taylor.taylor0_add (analyticAt_diagLine h hz x) (analyticAt_diagLine h hz y)

theorem constantCoeff_comp_taylorHom (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    (PowerSeries.constantCoeff (R := ℂ)).comp (taylorHom h hz) = ψ z := by
  ext x
  have e := Formalism.L2.Th1.F.Taylor.coeff_taylor0 (fun T => ψ (diagLine z T) x) 0
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, diagLine_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] at e
  exact e

theorem eq_zero_of_taylorHom (h : IsHolPts (Metric.ball 0 1) ψ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) {x : R}
    (hx : taylorHom h hz x = 0) {T : ℂ} (hT : T ∈ Metric.ball (0 : ℂ) (1 - ‖z‖)) : ψ (diagLine z T) x = 0 := by
  have h₀ : Formalism.L2.Th1.F.taylor0 (fun T => ψ (diagLine z T) x) = Formalism.L2.Th1.F.taylor0 (fun _ => (0 : ℂ)) := by
    rw [Formalism.L2.Th1.F.Taylor.taylor0_const, map_zero]
    exact hx
  have he := Formalism.L2.Th1.F.Taylor.taylor0_inj (analyticAt_diagLine h hz x) analyticAt_const h₀
  exact (analyticOnNhd_diagLine h hz x).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball _ _).isPreconnected (zero_mem_ball_norm hz) he hT

theorem exists_diagLine_mem_punct (a : ℕ) (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    ∃ T ∈ Metric.ball (0 : ℂ) (1 - ‖z‖), diagLine z T ∈ punct n a 1 := by
  have hinf : (Metric.ball (0 : ℂ) (1 - ‖z‖)).Infinite :=
    infinite_of_mem_nhds 0 (Metric.isOpen_ball.mem_nhds (zero_mem_ball_norm hz))
  obtain ⟨T, hT, hn⟩ := hinf.exists_notMem_finset (Finset.univ.image fun i : Fin n => -z i)
  refine ⟨T, hT, diagLine_mem_ball hz hT, fun i _ he => hn ?_⟩
  refine Finset.mem_image.2 ⟨i, Finset.mem_univ _, ?_⟩
  have : z i + T = 0 := he
  linear_combination -this

end Curve

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem range_jK_taylorHom_subset {Xo : Moduli D l} {σ : KA l →+* ℂ} {n a : ℕ} (C : Flat.BdryChart Xo σ n a)
    {z : Fin n → ℂ} (hz : z ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    Set.range (Out.jK (PowerSeries ℂ) ≫ spMap (taylorHom C.hol hz)) ⊆ Set.range C.j := by
  have := C.j_open
  rintro _ ⟨q, rfl⟩
  obtain ⟨T, hT, hp⟩ := exists_diagLine_mem_punct a hz
  obtain ⟨s⟩ : Nonempty (Sp ℂ) := inferInstance
  have hw : spMap (C.ψ (diagLine z T)) s ∈ Set.range C.j :=
    ⟨C.pt (diagLine z T) s, by rw [← (C.pt_eq _ hp).1, Scheme.Hom.comp_apply]⟩
  refine Specializes.mem_open ?_ C.j.isOpenEmbedding.isOpen_range hw
  refine (PrimeSpectrum.le_iff_specializes _ _).1 fun x hx => ?_
  have hq : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top
  rw [Scheme.Hom.comp_apply] at hx
  have h₁ : algebraMap (PowerSeries ℂ) (FractionRing (PowerSeries ℂ)) (taylorHom C.hol hz x) ∈ q.asIdeal := hx
  rw [hq, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h₁
  have h₂ : C.ψ (diagLine z T) x = 0 := eq_zero_of_taylorHom C.hol hz h₁ hT
  show C.ψ (diagLine z T) x ∈ s.asIdeal
  rw [h₂]
  exact Ideal.zero_mem _

section Pulled

open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem polAt_of_pulled {S S' X : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {K : Type} [Field K] {tK : SAB H (Sp K)} {j : Sp K ⟶ S} (mK : SABMap tK t j)
    {u : SAB H X} {x : Sp K ⟶ X} (mx : SABMap tK u x) (hp : IsProper u.G.hom) (ha : Out.RelAmple u.G u.PP.L)
    (hk : Out.KTriv u.G u.PP.L) (j' : Sp K ⟶ S') (h : j' ≫ f = j) : GlobalTheory.LN.PolAt t' j' := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull j' t'
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₂
  have cancel : ∀ (t₂ : SAB H (Sp K)) (p : Sp K ⟶ S) (_ : p = 𝟙 _ ≫ j) (_ : SABMap t₂ t p),
      Nonempty (SABMap t₂ u (𝟙 _ ≫ x)) := by
    intro t₂ p hp n
    subst hp
    exact ⟨(sabComp pullCubComp E H _ _ _ _ _ _ _ _ mx
      (sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ mK n).choose).choose⟩
  obtain ⟨m₃⟩ := cancel _ _ (h.trans (Category.id_comp _).symm) n
  have h₂ : LBIso PP'.L (t'.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (u.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull t'.PP.isLB (pullback.fst t'.G.hom j')
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 hp,
    amplePt _ _ (𝟙 _ ≫ x) _ _ m₃.φ m₃.cart _ _ u.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull u.PP.isLB _) h₂.symm h₃) ha hk⟩

end Pulled

theorem exists_curve_through_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (z : Fin n → ℂ), z ∈ Metric.ball (0 : Fin n → ℂ) 1 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : C.R →+* V) (r : V →+* ℂ) (tV : SAB H (Sp V)) (_ : SABMap tV C.t (spMap f)), GlobalTheory.LN.CDvr V ∧ Function.Surjective r ∧ RingHom.ker r = IsLocalRing.maximalIdeal V ∧ r.comp f = C.ψ z ∧ GlobalTheory.LN.PolAt tV (Out.jK V) := by
  intro E _ _ _ H D l Xo σ n a C z hz
  have := C.j_open
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (taylorHom C.hol hz)) C.t
  have hc : GlobalTheory.LN.CDvr (PowerSeries ℂ) :=
    ⟨inferInstance, by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance, algebraRat.charZero _⟩
  have hsurj : Function.Surjective (PowerSeries.constantCoeff (R := ℂ)) := fun c =>
    ⟨PowerSeries.C c, by simp⟩
  refine ⟨PowerSeries ℂ, inferInstance, inferInstance, inferInstance, taylorHom C.hol hz,
    PowerSeries.constantCoeff (R := ℂ), _, m, hc, hsurj, ?_, constantCoeff_comp_taylorHom C.hol hz, ?_⟩
  · have := RingHom.ker_isMaximal_of_surjective _ hsurj
    exact IsLocalRing.eq_maximalIdeal this
  · have hr := range_jK_taylorHom_subset C hz
    let y := IsOpenImmersion.lift C.j _ hr
    have hy : y ≫ C.j = Out.jK (PowerSeries ℂ) ≫ spMap (taylorHom C.hol hz) := IsOpenImmersion.lift_fac _ _ _
    obtain ⟨_, _, _, _, _, m₀, -⟩ := sabPull Out.CubePf.cubePull y C.tV
    obtain ⟨mK, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m₁ m₀
    obtain ⟨mx, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ C.m₂ m₀
    exact polAt_of_pulled m mK mx Xo.univ.proper Xo.univ.ample Xo.univ.ktriv (Out.jK (PowerSeries ℂ)) hy.symm

end GlobalTheory.CompanionTheory.Ar.QuotLoc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankAbPartTorusPos
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.AbPartTorus

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev torTriple (H : Host E) (K : Type) [Field K] : SAB H (Sp K) :=
  GlobalTheory.Models.Inhab.trivTriple H (splitTorus (Sp K) (𝓞 E)) (GlobalTheory.Diag.isSemiAbelian _ _) (GlobalTheory.Diag.diagAct _ _ _)

def torExt (E : Type) [Field E] [NumberField E] (K : Type) [Field K] : TorusExtension (splitTorus (Sp K) (𝓞 E)) :=
  torusExtOfIso (GlobalTheory.Diag.baseChangeIso (𝟙 (Sp K)) (𝓞 E)) (GlobalTheory.Diag.torusExtension (Sp K) (𝓞 E) (𝟙 (Sp K)))

def abPartTorus (H : Host E) (K : Type) [Field K] : GlobalTheory.CompanionTheory.Ar.AbPart (torTriple H K) (𝟙 (Sp K)) where
  tK := torTriple H K
  m := (GlobalTheory.ObjMaps.exists_sab_id (torTriple H K)).choose
  τ := torExt E K
  tB := GlobalTheory.Models.Inhab.zeroTriple H (Sp K)
  e := Iso.refl _
  e_hom := by
    let := (torExt E K).grpB
    exact ⟨toUnit_unique _ _, toUnit_unique _ _⟩
  act a := toUnit_unique _ _
  pp := ⟨⟨fun _ => 1⟩, ZJ.isGen_one_of_g_eq_one _ (ZJ.div_g_eq_one _ _ (Out.Inh.linComb_triv_g _ _) (fun _ _ => rfl))⟩

attribute [local instance] TorusExtension.addCommGroup

end GlobalTheory.CompanionTheory.Ar.AbPartTorus
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermJetLiftStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_germ_jet_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (xk : ∀ m, Sp (Jet k (Fin 1 × Fin d) m) ⟶ pullback t.G.hom x), (∀ m, xk m ≫ pullback.fst _ _ = (g.x m).left) → (∀ m, xk m ≫ pullback.snd _ _ = spMap (algebraMap k _)) → ∃ _ : IsIntegral (pullback t.G.hom x), IsNormalScheme (pullback t.G.hom x) ∧ CharP (pullback t.G.hom x).functionField p ∧ ∀ (U : (pullback t.G.hom x).Opens) (hU : ∀ m, ⊤ ≤ xk m ⁻¹ᵁ U) [Nonempty U] (f : Γ(pullback t.G.hom x, U)), ∃ F : MvPowerSeries (Fin 1 × Fin d) k, (∀ m, ((xk m).appLE U ⊤ (hU m)).hom f = toΓ _ (psJet m F)) ∧ (F = 0 → f = 0) ∧ ((∀ q, MvPowerSeries.pderiv k q F = 0) → ∃ r : (pullback t.G.hom x).functionField, r ^ p = ((pullback t.G.hom x).germToFunctionField U).hom f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FibreTaylor.fibre_taylor_expansion | exact GlobalTheory.CompanionTheory.Ar.FibreTaylor.fibre_taylor_expansion | (intros; apply GlobalTheory.CompanionTheory.Ar.FibreTaylor.fibre_taylor_expansion <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermsIsomorphicStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_germs_isomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0) (d : ℕ) (g g₂ : GermAt t x d), ∃ (φ ψ : Germ.Pt S 1 d) (lam : Germ.PS S 2 d), IsIso g.B g₂.B φ ψ lam ∧ ∀ l, IsCombAtG t x g.tg (fun j => lin φ 1 j l) (g₂.tg l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.germ_iso_main | exact GlobalTheory.CompanionTheory.Ar.Conj.germ_iso_main | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.germ_iso_main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericCoordsDescendSubfieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_coords_descend_subfield : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ Y.X) (Ω₀ : Type) [Field Ω₀] [Algebra Ω₀ Ω] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (cst : c.F →+* Ω) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (Li₀ : Type) [AddCommGroup Li₀] [Module Ω₀ Li₀] (M₀ : LieModel Y.t.G ξ₀ Li₀) (j : Li₀ →+ Li) (V₀ : CMType H ⊕ CMType H → Submodule Ω₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li) (d : ℕ), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q)) → IsCptGen ξ₀ → GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f (algebraMap Ω₀ Ω) → ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → M.IsActOf t.act.act ρ → (∀ e, (M.pt (j e)).left ≫ m.φ = spMap (dualMap (algebraMap Ω₀ Ω)) ≫ (M₀.pt e).left) → (∀ s e, e ∈ V₀ s ↔ j e ∈ eigSp ρ (cst.comp (labelEmb c s))) → IsGenericFlag (Ω' := Ω) j V₀ b d → (∀ s, (M.eigLat ρ (cst.comp (labelEmb c s))).IsFlagVBOn {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ r q} (b s)) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (𝔐 : HodgeCpt Y ∅ y') (g : 𝔐.X ⟶ X) (Fl : 𝔐.Flag) (xdeg : RootIx D → K' → ℤ) (e : RootIx D → Ω), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) ∧ 𝔐.ξ ≫ g = ξ ∧ 𝔐.f = g ≫ f ∧ genPt 𝔐.ξ₀ = genPt ξ₀ ∧ Fl.deg = d ∧ Fl.RootLines xdeg e ∧ (∀ s i, (𝔐.M.pt (Fl.b s i)).left ≫ 𝔐.m.φ = (M.pt (b s i)).left ≫ m.φ) ∧ (∀ q' : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q') → ∀ h : genPt ξ ⤳ g q'.1, regAt 𝔐.ξ q' = regAt ξ ⟨g q'.1, h⟩) ∧ ∀ q₁ q₂ : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q₁) → g q₁.1 = g q₂.1 → q₁ = q₂ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_sat_model | exact GlobalTheory.CompanionTheory.Ar.exists_sat_model | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_sat_model <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductPullbackIffStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_inner_product_pullback_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (z : Sp ℂ ⟶ S') (v' w' : epsAt z ⟶ t'.G) (v w : epsAt (z ≫ f) ⟶ t.G) (c : ℂ), v'.left ≫ m.φ = v.left → w'.left ≫ m.φ = w.left → (HodgeIP t'.G t'.PP.L z v' w' c ↔ HodgeIP t.G t.PP.L (z ≫ f) v w c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgePullBack.hodgeInnerProduct_iff_of_abelianSchemeMap | exact GlobalTheory.CompanionTheory.Ar.HodgePullBack.hodgeInnerProduct_iff_of_abelianSchemeMap | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgePullBack.hodgeInnerProduct_iff_of_abelianSchemeMap <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeFlagLatticeUpper
section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem family_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (hpq : 0 < D.p + D.q) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → HTFree 𝔐 p → (∀ s, Module.Projective (chartRing o (mseg y) s.1) (Dc s).om' ∧ ∀ σ : E →+* Ω, Module.Projective (chartRing o (mseg y) s.1) ((Dc s).omHT σ)) ∧ (∀ σ : E →+* Ω, ∃ d : Ω, ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, ∃ ds : chartRing o (mseg y) s.1, (ds : Ω) = d ∧ GeneratesDiff σ ds) ∧ ∃ κ : Ω, IsCp p κ ∧ ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, κ ∈ chartRing o (mseg y) s.1 :=
  @PositivityTheory.HtPt.Famproj.family_proj

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicUniformizationDimEqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_uniformization_dim_eq : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g d : ℕ) (u : HolUnif A L g), SmoothOfRelativeDimension d A.hom → g = d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.UnifDim.eq_relativeDimension | exact GlobalTheory.CompanionTheory.Ar.UnifDim.eq_relativeDimension | (intros; apply GlobalTheory.CompanionTheory.Ar.UnifDim.eq_relativeDimension <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrincipalBaseChangeIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem isPrincipal_iff_of_sabMap_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L L' : Type) [Field L] [Field L'] (e : L →+* L') (t : SAB H (Sp L)) (t' : SAB H (Sp L')) (_ : SABMap t' t (spMap e)), IsPrincipal t' ↔ IsPrincipal t := by
  exact @CoverDenseAlt.isPrincipal_iff_of_base_change

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFrameSpansGenericStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_frame_spans_generic : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] (zL : Sp L ⟶ X) (T : Type) [AddCommGroup T] [Module L T] (TL : LieModel G zL T) (h : genPt ξ ⤳ centre zL) (Ix : Type) [Fintype Ix] (f : Ix → Li), IsCptGen ξ → LinearIndependent Ω f → Submodule.span Ω (Set.range f) = ⊤ → M.lat ⟨centre zL, h⟩ = Submodule.span (regAt ξ ⟨centre zL, h⟩) (Set.range f) → ∃ w : Ix → T, (∀ i, M.ValAt zL (f i) (TL.pt (w i))) ∧ LinearIndependent L w ∧ Submodule.span L (Set.range w) = ⊤ ∧ ∀ (A : Set Ix) (e : Li) (u : T), e ∈ Submodule.span (regAt ξ ⟨centre zL, h⟩) (f '' A) → M.ValAt zL e (TL.pt u) → u ∈ Submodule.span L (w '' A) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_valFrame | exact GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_valFrame | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_valFrame <;> assumption)
end

