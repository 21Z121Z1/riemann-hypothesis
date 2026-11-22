import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PPshLocal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0044
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreChartBundle
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0045
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAt

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlurisubharmonicLocal
section
namespace GlobalTheory.CompanionTheory.AnForm.PshLocal

open Filter Topology ReciprocityTheory.AnForm.A

theorem isPsh_mono {n : ℕ} {V W : Set (Fin n → ℂ)} {φ : (Fin n → ℂ) → ℝ} (hWV : W ⊆ V)
    (h : IsPsh V φ) : IsPsh W φ := by
  unfold ReciprocityTheory.AnForm.A.IsPsh at h ⊢
  obtain ⟨hu, hm⟩ := h
  exact ⟨hu.mono hWV, fun z w hzw => hm z w fun ζ hζ => hWV (hzw ζ hζ)⟩

theorem isPsh_of_locally :
    ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (φ : (Fin n → ℂ) → ℝ), IsOpen U →
      (∀ z ∈ U, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ z ∈ V ∧ ReciprocityTheory.AnForm.A.IsPsh V φ) →
      ReciprocityTheory.AnForm.A.IsPsh U φ := by
  intro n U φ hU hloc
  have hloc' : ∀ p ∈ U, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ IsPsh W φ := by
    intro p hp
    obtain ⟨V, hV, hpV, hψ⟩ := hloc p hp
    exact ⟨V ∩ U, hV.inter hU, ⟨hpV, hp⟩, Set.inter_subset_right, isPsh_mono Set.inter_subset_left hψ⟩
  have hlocg : ∀ k : ℕ, ∀ p ∈ U, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧
      IsPsh W (fun x => max (φ x) (-(k : ℝ))) := by
    intro k p hp
    obtain ⟨W, hW, hpW, hWU, hψ⟩ := hloc' p hp
    exact ⟨W, hW, hpW, hWU, GroundTheory.Heights₂.Heights.NineStatements.PshLocal.isPsh_max hψ _⟩
  have husc := GroundTheory.Heights₂.Heights.NineStatements.PshLocal.usc hloc'
  unfold ReciprocityTheory.AnForm.A.IsPsh
  refine ⟨husc, ?_⟩
  intro z w hzw
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi))
  let F : ℝ → ℝ := fun θ => φ (z + circleMap 0 1 θ • w)
  let f : ℕ → ℝ → ℝ := fun k θ => max (F θ) (-(k : ℝ))
  have hcore : ∀ k : ℕ, IntervalIntegrable (f k) MeasureTheory.volume 0 (2 * Real.pi) ∧
      max (φ z) (-(k : ℝ)) ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f k θ := fun k =>
    GroundTheory.Heights₂.Heights.NineStatements.PshLocal.core hU (hlocg k) z w hzw (c := -(k : ℝ))
      (fun θ => le_max_right _ _)
  have hint : ∀ k, MeasureTheory.Integrable (f k) μ := fun k =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).mp (hcore k).1
  have hanti : ∀ θ, Antitone fun k : ℕ => f k θ := by
    intro θ
    refine antitone_nat_of_succ_le fun k => ?_
    show max (F θ) (-(((k + 1 : ℕ)) : ℝ)) ≤ max (F θ) (-(k : ℝ))
    push_cast
    exact max_le_max le_rfl (by linarith)
  have htend : ∀ θ, Tendsto (fun k : ℕ => f k θ) atTop (𝓝 (F θ)) := by
    intro θ
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈-F θ⌉₊) fun k hk => ?_
    have hc := Nat.le_ceil (-F θ)
    have hk' : ((⌈-F θ⌉₊ : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    exact max_eq_left (by linarith)
  have hlow : ∀ k : ℕ, 2 * Real.pi * φ z ≤ ∫ θ, f k θ ∂μ := by
    intro k
    have h1 := le_trans (le_max_left (φ z) (-(k : ℝ))) (hcore k).2
    rw [intervalIntegral.integral_of_le h2π] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 h2π
    rwa [← mul_assoc, mul_inv_cancel₀ hpi.ne', one_mul] at h3
  have hFmeas : MeasureTheory.AEStronglyMeasurable F μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hint k).aestronglyMeasurable)
      (Filter.Eventually.of_forall htend)
  have hGnn : ∀ (k : ℕ) θ, 0 ≤ f 0 θ - f k θ := fun k θ => sub_nonneg.mpr (hanti θ (Nat.zero_le k))
  have hFle : ∀ θ, F θ ≤ f 0 θ := fun θ => le_max_left _ _
  have hGint : MeasureTheory.Integrable (fun θ => f 0 θ - F θ) μ := by
    refine ⟨(hint 0).aestronglyMeasurable.sub hFmeas, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun θ => sub_nonneg.mpr (hFle θ))]
    have hlim : ∀ θ, Tendsto (fun k : ℕ => ENNReal.ofReal (f 0 θ - f k θ)) atTop
        (𝓝 (ENNReal.ofReal (f 0 θ - F θ))) :=
      fun θ => (ENNReal.continuous_ofReal.tendsto _).comp ((htend θ).const_sub _)
    have hterm : ∀ k : ℕ, ∫⁻ θ, ENNReal.ofReal (f 0 θ - f k θ) ∂μ ≤
        ENNReal.ofReal (∫ θ, f 0 θ ∂μ - 2 * Real.pi * φ z) := by
      intro k
      have e := MeasureTheory.ofReal_integral_eq_lintegral_ofReal (f := fun θ => f 0 θ - f k θ)
        ((hint 0).sub (hint k)) (Filter.Eventually.of_forall (hGnn k))
      rw [← e, MeasureTheory.integral_sub (hint 0) (hint k)]
      exact ENNReal.ofReal_le_ofReal (by linarith [hlow k])
    calc ∫⁻ θ, ENNReal.ofReal (f 0 θ - F θ) ∂μ
        = ∫⁻ θ, liminf (fun k : ℕ => ENNReal.ofReal (f 0 θ - f k θ)) atTop ∂μ := by
          congr 1
          funext θ
          exact ((hlim θ).liminf_eq).symm
      _ ≤ liminf (fun k : ℕ => ∫⁻ θ, ENNReal.ofReal (f 0 θ - f k θ) ∂μ) atTop :=
          MeasureTheory.lintegral_liminf_le' fun k => ((hint 0).sub (hint k)).aemeasurable.ennreal_ofReal
      _ ≤ ENNReal.ofReal (∫ θ, f 0 θ ∂μ - 2 * Real.pi * φ z) :=
          Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hterm)
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hFint : MeasureTheory.Integrable F μ :=
    ((hint 0).sub hGint).congr (Filter.Eventually.of_forall fun θ => by simp)
  have hlimI := MeasureTheory.integral_tendsto_of_tendsto_of_antitone hint hFint
    (Filter.Eventually.of_forall hanti) (Filter.Eventually.of_forall htend)
  have hge : 2 * Real.pi * φ z ≤ ∫ θ, F θ ∂μ := ge_of_tendsto' hlimI hlow
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le h2π).mpr hFint, ?_⟩
  rw [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le h2π]
  have h4 := mul_le_mul_of_nonneg_left hge (inv_nonneg.mpr h2π)
  rwa [← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul] at h4

end GlobalTheory.CompanionTheory.AnForm.PshLocal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalizationStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regAt_chart_localization : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ), InChart M.ξ x c p → (∀ a ∈ chRing o x c, a ∈ regAt M.ξ p) ∧ ∀ a : Ω, a ∈ regAt M.ξ p ↔ ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, unitAt M.ξ p v ∧ a = u / v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation | exact GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation | (intros; apply GlobalTheory.CompanionTheory.Ar.chart_regAt_localisation <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtLeIffSpecializesStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regAt_le_iff_specializes : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (p q : Cpt M.ξ), regAt M.ξ p ≤ regAt M.ξ q ↔ q.1 ⤳ p.1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.regAt_le_regAt_iff_specializes | exact GlobalTheory.CompanionTheory.Ar.regAt_le_regAt_iff_specializes | (intros; apply GlobalTheory.CompanionTheory.Ar.regAt_le_regAt_iff_specializes <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtLocalOrderFractionStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regAt_local_order_fraction : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ p : Cpt ξ, IsLocalRing (regAt ξ p)) ∧ (∀ p q : Cpt ξ, q.1 ⤳ p.1 → regAt ξ p ≤ regAt ξ q) ∧ (IsCptGen ξ → ∀ (p : Cpt ξ) (a : Ω), ∃ u ∈ regAt ξ p, ∃ v ∈ regAt ξ p, v ≠ 0 ∧ a = u / v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.regAt_local_mono_frac | exact GlobalTheory.CompanionTheory.Ar.regAt_local_mono_frac | (intros; apply GlobalTheory.CompanionTheory.Ar.regAt_local_mono_frac <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreChartBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segre_chart_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (E : Type) [AddCommGroup E] [Module Ω E] (r : ℕ) (W : ChartBundle ℤ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) r E) (L : Lat ξ E), CoordTie ℤ ξ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) → L.IsVB r ⊤ → L.IsChartOf (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) W.lat → ∀ (c : (k : K) → J k) (f : Ω) (b : Fin r → E), GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y c ≠ 0 → f ∈ chartRing ℤ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) c → f ≠ 0 → (GroundTheory.Heights₂.Heights.LowerBoundFree.IsFrameOver y W c f b ↔ ∀ p : Cpt ξ, InChart ξ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) c p → unitAt ξ p f → L.IsFrameAt b p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isFrameOver_iff_forall_isFrameAt | exact GlobalTheory.CompanionTheory.Ar.isFrameOver_iff_forall_isFrameAt | (intros; apply GlobalTheory.CompanionTheory.Ar.isFrameOver_iff_forall_isFrameAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSectionAdditive
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SqAdd

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {S : Scheme.{0}} {C B : Type} [CommRing C] [CommRing B]

theorem dualMap_comp_algebraMap (φ : C →+* B) :
    (dualMap φ).comp (algebraMap C (DualNumber C)) = (algebraMap B (DualNumber B)).comp φ := by
  refine RingHom.ext fun c => ?_
  apply TrivSqZeroExt.ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap (φ : C →+* B) :
    (TrivSqZeroExt.fstHom B B B).toRingHom.comp (dualMap φ) =
      φ.comp (TrivSqZeroExt.fstHom C C C).toRingHom := by
  refine RingHom.ext fun c => ?_
  simp [dualMap]

def epsIdeal (B : Type) [CommRing B] : Ideal (DualNumber B) :=
  RingHom.ker (TrivSqZeroExt.fstHom B B B).toRingHom

theorem epsIdeal_sq : epsIdeal B ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  have ha' : a.fst = 0 := ha
  have hb' : b.fst = 0 := hb
  rw [Ideal.mem_bot]
  apply TrivSqZeroExt.ext <;> simp [ha', hb']

def redMap (B : Type) [CommRing B] : B →+* DualNumber B ⧸ epsIdeal B :=
  (Ideal.Quotient.mk (epsIdeal B)).comp (algebraMap B (DualNumber B))

theorem mk_eq_redMap_comp :
    Ideal.Quotient.mk (epsIdeal B) = (redMap B).comp (TrivSqZeroExt.fstHom B B B).toRingHom := by
  refine RingHom.ext fun a => ?_
  change Ideal.Quotient.mk (epsIdeal B) a = Ideal.Quotient.mk (epsIdeal B) (algebraMap B (DualNumber B) a.fst)
  rw [Ideal.Quotient.eq]
  change (TrivSqZeroExt.fstHom B B B).toRingHom _ = 0
  simp [TrivSqZeroExt.algebraMap_eq_inl]

def restr (φ : C →+* B) (y : Sp C ⟶ S) :
    Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ epsAt y :=
  Over.homMk (spMap (dualMap φ)) (by
    change spMap _ ≫ spMap _ ≫ y = spMap _ ≫ spMap _ ≫ y
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    exact congrArg CommRingCat.ofHom (dualMap_comp_algebraMap φ))

theorem red_restr (G : Over S) [GrpObj G] (φ : C →+* B) (y : Sp C ⟶ S) (v : epsAt y ⟶ G) (tv : IsTanAt G y v) :
    spMap (Ideal.Quotient.mk (epsIdeal B)) ≫ (restr φ y ≫ v).left =
      spMap (Ideal.Quotient.mk (epsIdeal B)) ≫
        (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left := by
  have hred : spMap (redMap B) = spMap (Ideal.Quotient.mk (epsIdeal B)) ≫ spMap (algebraMap B (DualNumber B)) := by
    rw [← Spec.map_comp]; rfl
  have hmk : spMap (Ideal.Quotient.mk (epsIdeal B)) =
      spMap (redMap B) ≫ spMap (TrivSqZeroExt.fstHom B B B).toRingHom := by
    rw [← Spec.map_comp]
    exact congrArg (fun f => spMap f) mk_eq_redMap_comp
  have hfst : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ spMap (dualMap φ) =
      spMap φ ≫ spMap (TrivSqZeroExt.fstHom C C C).toRingHom := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => spMap f) (fst_comp_dualMap φ)
  let T : Over S := Over.mk (spMap (Ideal.Quotient.mk (epsIdeal B)) ≫
    spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y)
  let m₁ : T ⟶ Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) :=
    Over.homMk (spMap (Ideal.Quotient.mk (epsIdeal B))) rfl
  let m₂ : T ⟶ Over.mk y := Over.homMk (spMap (redMap B) ≫ spMap φ) (by
    change (spMap (redMap B) ≫ spMap φ) ≫ y = _
    rw [hred]
    simp [T])
  have c : m₁ ≫ (1 : _ ⟶ G) = m₂ ≫ (1 : _ ⟶ G) := by
    rw [MonObj.comp_one, MonObj.comp_one]
  have c' : spMap (Ideal.Quotient.mk (epsIdeal B)) ≫
      (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left =
      (spMap (redMap B) ≫ spMap φ) ≫ (1 : Over.mk y ⟶ G).left := congrArg CommaMorphism.left c
  rw [c']
  have tv' : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ v.left = (1 : Over.mk y ⟶ G).left := tv
  rw [← tv']
  change spMap (Ideal.Quotient.mk (epsIdeal B)) ≫ spMap (dualMap φ) ≫ v.left = _
  rw [hmk]
  simp only [Category.assoc]
  rw [reassoc_of% hfst]

theorem top_le_comp {X Y Z : Scheme.{0}} (p : X ⟶ Y) (k : Y ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ k ⁻¹ᵁ U) :
    ⊤ ≤ (p ≫ k) ⁻¹ᵁ U := fun z _ => by
  change k (p z) ∈ U
  exact h (show p z ∈ (⊤ : Y.Opens) from trivial)

theorem appTop_appLE {X Y Z : Scheme.{0}} (p : X ⟶ Y) (k : Y ⟶ Z) (k' : X ⟶ Z) (e : k' = p ≫ k) (U : Z.Opens)
    (h : ⊤ ≤ k ⁻¹ᵁ U) (h' : ⊤ ≤ k' ⁻¹ᵁ U) (s : Γ(Z, U)) :
    p.appTop.hom ((k.appLE U ⊤ h).hom s) = (k'.appLE U ⊤ h').hom s := by
  subst e
  have hle : (⊤ : X.Opens) ≤ p ⁻¹ᵁ (⊤ : Y.Opens) := by simp
  have hp : p.appTop = p.appLE ⊤ ⊤ hle := Scheme.Hom.app_eq_appLE ..
  have : k.appLE U ⊤ h ≫ p.appTop = (p ≫ k).appLE U ⊤ h' := by
    rw [hp]
    exact Scheme.Hom.appLE_comp_appLE ..
  rw [← this]
  rfl

theorem tan_local (G : Over S) [GrpObj G] [IsLocalRing B] (φ : C →+* B) (y : Sp C ⟶ S) (v w : epsAt y ⟶ G)
    (tv : IsTanAt G y v) (tw : IsTanAt G y w) (U : G.left.Opens) (hv : ⊤ ≤ v.left ⁻¹ᵁ U) (hw : ⊤ ≤ w.left ⁻¹ᵁ U)
    (hvw : ⊤ ≤ (v * w).left ⁻¹ᵁ U) (h1 : ⊤ ≤ (1 : epsAt y ⟶ G).left ⁻¹ᵁ U) (s : Γ(G.left, U)) :
    (spMap (dualMap φ)).appTop.hom
        (((v * w).left.appLE U ⊤ hvw).hom s + ((1 : epsAt y ⟶ G).left.appLE U ⊤ h1).hom s) =
      (spMap (dualMap φ)).appTop.hom ((v.left.appLE U ⊤ hv).hom s + (w.left.appLE U ⊤ hw).hom s) := by
  have hmul : ((restr φ y ≫ v) * (restr φ y ≫ w)).left = spMap (dualMap φ) ≫ (v * w).left :=
    congrArg CommaMorphism.left (MonObj.comp_mul (restr φ y) v w).symm
  have hone : (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left =
      spMap (dualMap φ) ≫ (1 : epsAt y ⟶ G).left :=
    congrArg CommaMorphism.left (MonObj.comp_one (restr φ y)).symm
  have hxv : ⊤ ≤ (restr φ y ≫ v).left ⁻¹ᵁ U := top_le_comp (spMap (dualMap φ)) v.left U hv
  have hxw : ⊤ ≤ (restr φ y ≫ w).left ⁻¹ᵁ U := top_le_comp (spMap (dualMap φ)) w.left U hw
  have hxvw : ⊤ ≤ ((restr φ y ≫ v) * (restr φ y ≫ w)).left ⁻¹ᵁ U := by
    rw [hmul]; exact top_le_comp _ _ U hvw
  have hx1 : ⊤ ≤ (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left ⁻¹ᵁ U := by
    rw [hone]; exact top_le_comp _ _ U h1
  have key := GlobalTheory.T.first_order_points_commute S G B (spMap φ ≫ y) (DualNumber B) (algebraMap B (DualNumber B)) (epsIdeal B)
    epsIdeal_sq (restr φ y ≫ v) (restr φ y ≫ w) (red_restr G φ y v tv) (red_restr G φ y w tw) U hxv hxw hxvw hx1 s
  rw [map_add, map_add,
    appTop_appLE (spMap (dualMap φ)) _ _ hmul U hvw hxvw s,
    appTop_appLE (spMap (dualMap φ)) _ _ hone U h1 hx1 s,
    appTop_appLE (spMap (dualMap φ)) v.left (restr φ y ≫ v).left rfl U hv hxv s,
    appTop_appLE (spMap (dualMap φ)) w.left (restr φ y ≫ w).left rfl U hw hxw s]
  exact key

theorem dualMap_fst (φ : C →+* B) (a : DualNumber C) : (dualMap φ a).fst = φ a.fst := by
  simp [dualMap]

theorem dualMap_snd (φ : C →+* B) (a : DualNumber C) : (dualMap φ a).snd = φ a.snd := by
  simp [dualMap]

theorem dual_eq_of_localization (a b : DualNumber C)
    (h : ∀ (q : Ideal C) [q.IsMaximal], dualMap (algebraMap C (Localization.AtPrime q)) a =
      dualMap (algebraMap C (Localization.AtPrime q)) b) : a = b := by
  have h0 : ∀ r r' : C, (∀ (q : Ideal C) [q.IsMaximal], algebraMap C (Localization.AtPrime q) r =
      algebraMap C (Localization.AtPrime q) r') → r = r' := by
    intro r r' hr
    rw [← sub_eq_zero]
    refine eq_zero_of_localization _ fun q hq => ?_
    rw [map_sub, hr q, sub_self]
  apply TrivSqZeroExt.ext
  · exact h0 _ _ fun q _ => by
      rw [← dualMap_fst, ← dualMap_fst, h q]
  · exact h0 _ _ fun q _ => by
      rw [← dualMap_snd, ← dualMap_snd, h q]

theorem gamma_eq_of_localization (a b : Γ(Sp (DualNumber C), ⊤))
    (h : ∀ (q : Ideal C) [q.IsMaximal], (spMap (dualMap (algebraMap C (Localization.AtPrime q)))).appTop.hom a =
      (spMap (dualMap (algebraMap C (Localization.AtPrime q)))).appTop.hom b) : a = b := by
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom :=
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).commRingCatIsoToRingEquiv.injective
  refine hinj (dual_eq_of_localization _ _ fun q _ => ?_)
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (dualMap (algebraMap C (Localization.AtPrime q))))
  have e' : ∀ c : Γ(Sp (DualNumber C), ⊤), dualMap (algebraMap C (Localization.AtPrime q))
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber (Localization.AtPrime q)))).hom
        ((spMap (dualMap (algebraMap C (Localization.AtPrime q)))).appTop.hom c) := fun c =>
    (congrArg (fun f => f.hom c) e).symm
  rw [e', e', h q]

theorem tan_mul_add : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (C : Type) [CommRing C] (y : Sp C ⟶ S)
    (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
    ∀ (U : G.left.Opens) (hv : ⊤ ≤ v.left ⁻¹ᵁ U) (hw : ⊤ ≤ w.left ⁻¹ᵁ U) (hvw : ⊤ ≤ (v * w).left ⁻¹ᵁ U)
      (h1 : ⊤ ≤ (1 : epsAt y ⟶ G).left ⁻¹ᵁ U) (s : Γ(G.left, U)),
      ((v * w).left.appLE U ⊤ hvw).hom s + ((1 : epsAt y ⟶ G).left.appLE U ⊤ h1).hom s =
        (v.left.appLE U ⊤ hv).hom s + (w.left.appLE U ⊤ hw).hom s := by
  intro S G _ C _ y v w tv tw U hv hw hvw h1 s
  exact gamma_eq_of_localization _ _ fun q _ =>
    tan_local G (algebraMap C (Localization.AtPrime q)) y v w tv tw U hv hw hvw h1 s

end GlobalTheory.CompanionTheory.Ar.SqAdd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingBaseChangeStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_embedding_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → IsSeparated G.hom → ∀ (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R') (Γ' : QFGroup R' T) (i' : Γ'.G.left ⟶ G.left), Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom φ) ≫ x) N i' → ∀ (B : Type) [CommRing B] (b : R →+* B) (j : B →+* FractionRing R) (j' : B →+* FractionRing R') (σ : T → (Spec (CommRingCat.of B) ⟶ G.left)), Function.Injective j → j.comp b = algebraMap R _ → j'.comp b = (algebraMap R' _).comp φ → (∀ t, σ t ≫ G.hom = Spec.map (CommRingCat.ofHom b) ≫ x) → (∀ t, Spec.map (CommRingCat.ofHom j) ≫ σ t = (Γ.pt t).left ≫ i) → (∀ t, Spec.map (CommRingCat.ofHom j') ≫ σ t = (Γ'.pt t).left ≫ i') → ∃ F : Γ'.G.left ⟶ Γ.G.left, F ≫ i = i' ∧ Γ'.IsBaseChange Γ φ F := by
  first | exact @GlobalTheory.CompanionTheory.Relay.torsion_embedding_base_change | exact GlobalTheory.CompanionTheory.Relay.torsion_embedding_base_change | (intros; apply GlobalTheory.CompanionTheory.Relay.torsion_embedding_base_change <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPullbackCorrespondence
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem torsionAlong_iff_pullback_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (X : Scheme.{0}) (x : Sp R ⟶ X) (G : Over X) [GrpObj G] (G₀ : Over (Sp R)) [GrpObj G₀] (ψ : G₀.left ⟶ G.left) (N : ℕ), IsGrpPullback G₀ G x ψ → (∀ i : Γ.G.left ⟶ G.left, Γ.IsTorsionAlong G x N i → ∃ i₀ : Γ.G.left ⟶ G₀.left, i₀ ≫ ψ = i ∧ Γ.IsTorsionAlong G₀ (𝟙 _) N i₀) ∧ ∀ i₀ : Γ.G.left ⟶ G₀.left, Γ.IsTorsionAlong G₀ (𝟙 _) N i₀ → Γ.IsTorsionAlong G x N (i₀ ≫ ψ) :=
  @PositivityTheory.UnitarySelfGeneration.isTorsionAlong_iff_of_isGrpPullback

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistObjMapFunctorialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_obj_map_functorial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (S' : Scheme.{0}) (s' : S' ⟶ Sp B) (o : Obj D l b s) (o' : Obj D l b s') (f : S' ⟶ S) (m : ObjMap o' o f) (g : HostAut H) (a : TwIso D g) (h : TwOK o g a) (h' : TwOK o' g a), ∃ n : ObjMap (twistObj o' g a h') (twistObj o g a h) f, n.toSABMap = twistMap m.toSABMap g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.objMap_twist | exact GlobalTheory.CompanionTheory.Ar.objMap_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.objMap_twist <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitSectionAvoidPrimeStatement
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_section_avoid_prime : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)) (f g : MRing ι) (df dg : K → ℕ), IsMultiProjPrime P → IsMultiProjPrime W → P ≤ W → IsMultiHomog f df → IsMultiHomog g dg → g ∉ P → IsUnitSec P f g → ∃ (f' g' : MRing ι) (df' dg' : K → ℕ), IsMultiHomog f' df' ∧ IsMultiHomog g' dg' ∧ (∀ k, (df' k : ℤ) - dg' k = (df k : ℤ) - dg k) ∧ f' ∉ W ∧ g' ∉ W ∧ f' * g - g' * f ∈ P ∧ IsUnitSec P f' g' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_rep_avoiding | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_rep_avoiding | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_rep_avoiding <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valAt_iff_value_at : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), genPt ξ ⤳ centre z → CoordsAt ξ y z w → ∀ (a : Ω) (v : ℂ), ValAt ξ z a v ↔ GroundTheory.Heights₂.Heights.LowerBoundFree.IsValueAt y a w v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords | exact GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationCentreRegularUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_centre_regular_unit : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → ∀ V : ValuationSubring Ω, (∀ o : O, algebraMap O Ω o ∈ V) → ∃ p : Cpt ξ, regAt ξ p ≤ V.toSubring ∧ ∀ a ∈ regAt ξ p, a ≠ 0 → a⁻¹ ∈ V → ∃ g : X.presheaf.stalk p.1, IsUnit g ∧ genMap ξ p g = a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_centre_of_isProper | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_centre_of_isProper | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_centre_of_isProper <;> assumption)
end

