import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0105
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0005
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0084
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerSeriesExpansionInDeltaUnique
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecMapCompAppLE
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetSectionGeneratorValue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

theorem aug_comp_inL (k : Type) [Field k] (B : Type) [CommRing B] [Algebra k B] (p : ℕ) :
    ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B).comp
        ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p) =
      (algebraMap k B).comp ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    have h0 : (Ideal.Quotient.mk (orig k Unit ^ (p + 1)) (MvPolynomial.C a) : Jet k Unit p) =
        algebraMap k (Jet k Unit p) a := rfl
    simp only [RingHom.comp_apply, h0, RingHom.coe_coe, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply k B (Jet B Unit p), AlgHom.commutes]
    rfl
  · intro i
    have h1 : (inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p)
        (Ideal.Quotient.mk (orig k Unit ^ (p + 1)) (MvPolynomial.X i)) = dQ B p := by
      change (MvPolynomial.aeval fun _ => dQ B p) (MvPolynomial.X i : MvPolynomial Unit k) = _
      simp
    have h2 : (jetAug : Jet B Unit p →ₐ[B] B) (dQ B p) = 0 := by
      change (MvPolynomial.aeval fun _ => (0 : B)) (MvPolynomial.X () : MvPolynomial Unit B) = _
      simp
    have h3 : (jetAug : Jet k Unit p →ₐ[k] k)
        (Ideal.Quotient.mk (orig k Unit ^ (p + 1)) (MvPolynomial.X i)) = 0 := by
      change (MvPolynomial.aeval fun _ => (0 : k)) (MvPolynomial.X i : MvPolynomial Unit k) = _
      simp
    simp only [RingHom.comp_apply, RingHom.coe_coe, h1, h2, h3, map_zero]

theorem red_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G) (B : Type) [CommRing B] [Algebra k B], homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1) → ∀ j₀ : t.PP.L.ι, ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ → ∃ τ₀ : (Jet B Unit p)ˣ, (jetAug : Jet B Unit p →ₐ[B] B) τ₀ = 1 ∧ ∀ (z : Sp (Jet B Unit p)) (J : (Sp (Jet B Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → (∀ ψ : Sp (Jet B Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀) → val τ (spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p)) z J = gm (𝟙 _) z ⊤ (unitΓ τ₀) := by
  intro E _ _ _ H X0 t k _ x p y B _ _ hy τ hτ j₀ hj₀
  have h1 : ∀ (κ : Fin 2) (q : Sp (Jet B Unit p)),
      (spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p) ≫
        (![y.left, (1 : Tm x p ⟶ t.G).left] : Fin 2 → _) κ) q ∈ t.PP.L.U j₀ := by
    intro κ q
    rw [Scheme.Hom.comp_apply]
    fin_cases κ
    · exact jet_left_mem t x j₀ hj₀ y hy _
    · exact jet_left_mem t x j₀ hj₀ 1 (by simp [Hom.one_def]) _
  have hc : spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫
        spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p) =
      spMap (algebraMap k B) ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [aug_comp_inL]
  obtain ⟨e₀, he, hall⟩ := val_eq_unit_of_red t.G.left (Sp (Jet k Unit p)) t.PP.L t.PP.isLB B p (Fin 2)
    ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1] τ
    (spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p)) j₀ h1
    (fun z' J' hG _ => by rw [hc]; exact hτ _ _ z' J' hG)
  exact ⟨e₀, he, fun z J hG hJ => hall z J hG fun κ => hJ _ (h1 κ z)⟩

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsUnitValues
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
open Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.OrArch.Ext

section General

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.setOf_forall, Set.setOf_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem continuousAt_metric (A : HermLine ι) (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContinuousAt A.h z :=
  hA.continuousOn.continuousAt (isOpen_blockNonzero.mem_nhds hz)

theorem continuous_aeval_form (g : MRing ι) : Continuous fun z : (Σ k, ι k) → ℂ => aeval z g := by
  have := MvPolynomial.continuous_eval (map (Int.castRingHom ℂ) g)
  simpa only [Small.LineModel.eval_map_eq] using this

theorem continuousAt_log_metric {σ : Type} (A : HermLine ι) (hA : IsSmoothHerm A) (c : (Σ k, ι k) → σ)
    {z : σ → ℂ} (hz : ∀ k, ∃ i, z (c ⟨k, i⟩) ≠ 0) :
    ContinuousAt (fun w : σ → ℂ => Real.log (A.h fun p => w (c p))) z := by
  have h1 : ContinuousAt (fun w : σ → ℂ => A.h fun p => w (c p)) z :=
    ContinuousAt.comp (g := A.h) (f := fun (w : σ → ℂ) p => w (c p)) (continuousAt_metric A hA hz)
      (continuous_pi fun p => continuous_apply _).continuousAt
  exact h1.log (A.pos _ hz).ne'

end General

theorem line_smooth {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : Top.RootModel Ψ N) (t : ℝ)
    (j : Option (Ψ × Fin N)) : IsSmoothHerm (M.line t j) := by
  cases j with
  | none => exact M.A_smooth
  | some r => exact M.x_smooth t r

theorem archBetween_of_off_form : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : Top.RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (t : ℝ) (lam : Top.Wt Ψ N) (s lo hi : ℝ) (f : MRing (Cmp.joinIdx M.ι R.ι)), f ∉ mCoordIdeal (Ht.joinOf M R i) → (∀ j, Ht.GenUnit (Ht.joinOf M R i) (Ht.joinDeg M R j) (u j)) → (∀ w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)), Cmp.evC w f ≠ 0 → ∀ val : Option (Ψ × Fin N) → ℂ, (∀ j, Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R j) (u j) w (val j)) → ∑ j, M.coef lam s j * (Real.log ((M.line t j).h (fun p => w (Cmp.joinInl M.ι R.ι p))) - Real.log ((R.line 1 j).h (fun p => w (Cmp.joinInr M.ι R.ι p))) - Real.log ‖val j‖) ∈ Set.Icc lo hi) → Ht.ArchBetween M R i u t lam s lo hi := by
  intro Ψ _ _ N M R i u t lam s lo hi f hf hu hb z hz val hval
  have hcl := GlobalTheory.T.complex_points_dense_nonvanishing (M.K ⊕ R.K) (Cmp.joinIdx M.ι R.ι) (mCoordIdeal (Ht.joinOf M R i)) _ f
    (GlobalTheory.T.join_model_points_project Ψ N M R i).1 hf
  have hzc := hcl (by rwa [← Small.LineModel.ptsOver_complex])
  have hne : ∀ j, val j ≠ 0 := by
    intro j
    obtain ⟨v, hv0, hv⟩ := hu j ℂ z hz
    rwa [Small.LineModel.hasVal_unique _ _ _ hz (hval j) hv]
  choose dg dh g h hg hh hd e n v using hval
  have hq : ∀ j, aeval z (g j) / aeval z (h j) = val j := fun j => by
    rw [v j, mul_div_assoc, div_self (n j), mul_one]
  let Fn : ((Σ k, Cmp.joinIdx M.ι R.ι k) → ℂ) → ℝ := fun w =>
    ∑ j, M.coef lam s j * (Real.log ((M.line t j).h fun p => w (Cmp.joinInl M.ι R.ι p)) -
      Real.log ((R.line 1 j).h fun p => w (Cmp.joinInr M.ι R.ι p)) -
        Real.log ‖aeval w (g j) / aeval w (h j)‖)
  have hcont : ContinuousAt Fn z := by
    refine tendsto_finset_sum _ fun j _ => ?_
    have h1 := continuousAt_log_metric (M.line t j) (line_smooth M t j) (Cmp.joinInl M.ι R.ι)
      (z := z) fun k => hz.1 (Sum.inl k)
    have h2 := continuousAt_log_metric (R.line 1 j) (line_smooth R 1 j) (Cmp.joinInr M.ι R.ι)
      (z := z) fun k => hz.1 (Sum.inr k)
    have h3 : ContinuousAt (fun w : (Σ k, Cmp.joinIdx M.ι R.ι k) → ℂ =>
        Real.log ‖aeval w (g j) / aeval w (h j)‖) z := by
      refine ContinuousAt.log ?_ ?_
      · exact (((continuous_aeval_form (g j)).continuousAt).div
          ((continuous_aeval_form (h j)).continuousAt) (n j)).norm
      · rw [hq j]
        exact norm_ne_zero_iff.mpr (hne j)
    exact continuousAt_const.mul ((h1.sub h2).sub h3)
  have hev : ∀ᶠ w in 𝓝[{w | w ∈ mcPts (mCoordIdeal (Ht.joinOf M R i)) ∧ Cmp.evC w f ≠ 0}] z,
      Fn w ∈ Set.Icc lo hi := by
    have hV : ∀ᶠ w in 𝓝 z, ∀ j, aeval w (h j) ≠ 0 := by
      rw [Filter.eventually_all]
      intro j
      exact (continuous_aeval_form (h j)).continuousAt.eventually_ne (n j)
    filter_upwards [nhdsWithin_le_nhds hV, self_mem_nhdsWithin] with w hw hS
    have hwp : w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)) := by
      rw [Small.LineModel.ptsOver_complex]
      exact hS.1
    exact hb w hwp hS.2 (fun j => aeval w (g j) / aeval w (h j)) fun j =>
      ⟨dg j, dh j, g j, h j, hg j, hh j, hd j, e j, hw j, (div_mul_cancel₀ _ (hw j)).symm⟩
  haveI hnb : (𝓝[{w | w ∈ mcPts (mCoordIdeal (Ht.joinOf M R i)) ∧ Cmp.evC w f ≠ 0}] z).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 hzc
  have hmem : Fn z ∈ Set.Icc lo hi :=
    isClosed_Icc.mem_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
  have hFn : Fn z = ∑ j, M.coef lam s j * (Real.log ((M.line t j).h fun p => z (Cmp.joinInl M.ι R.ι p)) -
      Real.log ((R.line 1 j).h fun p => z (Cmp.joinInr M.ι R.ι p)) - Real.log ‖val j‖) :=
    Finset.sum_congr rfl fun j _ => by rw [hq j]
  rwa [hFn] at hmem

end GlobalTheory.CompanionTheory.Ar.OrArch.Ext
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}

def gen (y : (Σ k, J k) → Ω) (a : K → ℤ) (e₀ : Ω) (c : (k : K) → J k) : Ω :=
  (∏ k, y ⟨k, c k⟩ ^ a k) * e₀

def IsCls {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} (b₀ : Fin r → E) (i : Fin r) (e : E) (t : Ω) : Prop :=
  e - t • b₀ i ∈ flagStep Ω b₀ i

def Sandwich {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
    (M : LieModel G ξ Li) (V : Lat ξ Li) {r : ℕ} (b₀ : Fin r → Li) (m : ℕ) : Prop :=
  ∀ p : Cpt ξ, ∃ (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li), (∀ i : ℕ, flagStep Ω b i = flagStep Ω b₀ i) ∧
    V.IsFrameAt b p ∧ (∀ i, (m : Ω) • b i ∈ M.lat p) ∧ (∀ i j, π i (b j) = if i = j then 1 else 0) ∧
    ∀ i, ∀ e ∈ M.lat p, (m : Ω) * π i e ∈ regAt ξ p

def gramAt {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
    {M : LieModel G ξ Li} {y : (Σ k, J k) → Ω} (h : LieMetric M y) (z : Sp ℂ ⟶ X) {n : ℕ}
    (v : Fin n → (epsAt z ⟶ G)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => h.ip z (v a) (v b)

def locRatio {L : Type} [Field L] [NumberField L] (a : K → ℤ) (w : (Σ k, J k) → L)
    (c : (k : K) → J k) (v : FinitePlace L) : ℝ :=
  ∏ k, ((⨆ i, v (w ⟨k, i⟩)) / v (w ⟨k, c k⟩)) ^ a k

end GlobalTheory.CompanionTheory.Ar.RootHt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonzeroSectionGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen

theorem exists_generic_mem_nonzeroLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (M : LB G.left), M.IsLB → ∀ t : SecMod G.hom M, t ≠ 0 → ∀ b : Sp R, b.asIdeal = ⊥ → ∃ y : G.left, G.hom y = b ∧ y ∈ Out.nonzeroLocus (M := M) t := by
  intro R _ _ _ G _ _ _ M hM t ht b hb
  haveI hI : IsIntegral (Sp R) := by unfold Sp; infer_instance
  haveI hN : IsLocallyNoetherian (Sp R) := by unfold Sp; infer_instance
  haveI hGI : GeometricallyIntegral G.hom :=
    GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres G.hom
  haveI hGR : GeometricallyReduced G.hom := inferInstance
  haveI hRed : AlgebraicGeometry.IsReduced G.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian G.hom
  have hgen : GeneralizingMap G.hom.base := Flat.generalizingMap G.hom
  have hne : ∃ y, y ∈ Out.nonzeroLocus (M := M) t := by
    by_contra hcon
    simp only [not_exists] at hcon
    apply ht
    apply SecMod.ext
    intro k
    rw [zero_f, ← basicOpen_eq_bot_iff, eq_bot_iff]
    intro y hy
    exact absurd (by unfold Out.nonzeroLocus; exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hy⟩) (hcon y)
  obtain ⟨y, hy⟩ := hne
  have hle : b.asIdeal ≤ (G.hom.base y).asIdeal := by rw [hb]; exact bot_le
  have hsp : b ⤳ G.hom.base y := (PrimeSpectrum.le_iff_specializes _ _).mp hle
  obtain ⟨y', hy'sp, hy'eq⟩ := hgen hsp
  exact ⟨y', hy'eq, hy'sp.mem_open (Out.nonzeroLocus (M := M) t).isOpen hy⟩

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalizedDegreeGramDet
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDegFree

open scoped ComplexOrder in

theorem gramDet_eq_norm {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L) (σ : L →+* ℂ)
    {n : ℕ} {e : Fin n → B.carrier} (hli : LinearIndependent (𝓞 L) e) :
    GroundTheory.Heights₂.Heights.gramDet B.metric σ e = ‖B.gramDet σ e‖ := by
  have hd : B.gramDet σ e = (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det := rfl
  have hp : 0 < (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det :=
    (Matrix.posDef_gram_of_linearIndependent (linearIndependent_fibreVec B.metric σ hli)).det_pos
  obtain ⟨h1, h2⟩ := Complex.lt_def.mp hp
  have hz : (((Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det).re : ℂ) =
      (Matrix.gram ℂ fun i => fibreVec B.metric σ (e i)).det :=
    Complex.ext (by simp) (by simpa using h2)
  rw [hd, ← hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa using h1)]
  rfl

theorem normDegree_top_eq_mean_gramDet : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (n : ℕ) (e : Fin n → B.carrier), LinearIndependent (𝓞 L) e → Submodule.span (𝓞 L) (Set.range e) = ⊤ → B.normDegree ⊤ = -(1 / 2) * mean L (fun σ => Real.log ‖B.gramDet σ e‖) := by
  intro L _ _ B n e hli hspan
  let s : Fin n → (⊤ : Submodule (𝓞 L) B.carrier) := fun i => ⟨e i, Submodule.mem_top⟩
  have hs : LinearIndependent (𝓞 L) s :=
    LinearIndependent.of_comp (⊤ : Submodule (𝓞 L) B.carrier).subtype hli
  have hcard : Fintype.card (Fin n) = B.rank ⊤ := by
    rw [Fintype.card_fin, HermitianBundle.rank, finrank_top,
      Module.finrank_eq_card_basis (Module.Basis.mk hli hspan.ge), Fintype.card_fin]
  have hsp : Submodule.span (𝓞 L) (Set.range s) = ⊤ := by
    have hmap : (Submodule.span (𝓞 L) (Set.range s)).map
        (⊤ : Submodule (𝓞 L) B.carrier).subtype = ⊤ := by
      rw [Submodule.map_span, ← Set.range_comp]
      exact hspan
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' : x ∈ (Submodule.span (𝓞 L) (Set.range s)).map
        (⊤ : Submodule (𝓞 L) B.carrier).subtype := by
      rw [hmap]
      exact Submodule.mem_top
    obtain ⟨y, hy, rfl⟩ := hx'
    exact hy
  have hone : Nat.card ((⊤ : Submodule (𝓞 L) B.carrier) ⧸ Submodule.span (𝓞 L) (Set.range s)) = 1 := by
    rw [hsp]
    exact Nat.card_unique
  have hg : ∀ σ : L →+* ℂ, GroundTheory.Heights₂.Heights.gramDet B.metric σ
      (fun i => ((s i : (⊤ : Submodule (𝓞 L) B.carrier)) : B.carrier)) = ‖B.gramDet σ e‖ :=
    fun σ => gramDet_eq_norm B σ hli
  rw [HermitianBundle.normDegree, B.degree_eq_of_linearIndependent ⊤ hs hcard,
    hone, Nat.cast_one, Real.log_one, zero_sub, mean]
  simp only [hg]
  ring

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDegFree
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerSeriesExpansionInDeltaUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_series_expansion_in_delta_unique : ∀ (X0 : Scheme.{0}) (G : Over X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (m : ℕ) (W : (pullback G.hom x).Opens) (f : Γ(Ym G x m, prZ G x m ⁻¹ᵁ W)), ∃! c : Fin (m + 1) → Γ(pullback G.hom x, W), f = ∑ i, ((prZ G x m).app W).hom (c i) * dltOn G x m _ ^ (i : ℕ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.Thick.sections_thick | exact GlobalTheory.CompanionTheory.Ar.Coc.Thick.sections_thick | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.Thick.sections_thick <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResidueHodgeLatticeAdaptedBasisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_hodge_lattice_adapted_basis : ∀ (E : Type) [Field E] [NumberField E] (C A : Type) [Field C] [CharZero C] [CommRing A] [Algebra A C]
    (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (g p q : ℕ) (ρC : 𝓞 E →+* Module.End C (Fin g → C))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HV : Submodule A ((Fin g → C) × Module.Dual C (Fin g → C)))
    (tC : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (b₁ v : Fin p → Fin g → C) (b₂ w : Fin q → Fin g → C)
    (u : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (Ap : Matrix (Fin (p + q)) (Fin (p + q)) C)
    (P : Matrix (Fin p) (Fin p) C) (Q : Matrix (Fin q) (Fin q) C) (gm : C),
    (∀ a y, (ρHC a y).1 = ρC a y.1) → (∀ a f, ρHC a (0, f) = (0, f ∘ₗ ρC (bar a))) →
    (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) →
    (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A C).range) → HT.IsFreeOn ρHC HV tC →
    IsAdapted ρHC σ b₁ b₂ u → (∀ i, v i = ∑ k, P i k • b₁ k) → (∀ i, w i = ∑ k, Q i k • b₂ k) →
    LinearIndependent C b₁ → (∀ i, HT.eigProj ρHC σ (tC i) = ∑ k, Ap i k • u k) →
    (∀ (v' : Fin p → Fin g → C) (w' : Fin q → Fin g → C)
      (u' : Fin (p + q) → (Fin g → C) × Module.Dual C (Fin g → C)) (B : Matrix (Fin (p + q)) (Fin (p + q)) C),
      LinearIndependent C v' → Submodule.span A (Set.range v') = HT.eigSub ρC σ (stdLat A C g) →
      LinearIndependent C w' → Submodule.span A (Set.range w') = HT.eigSub ρC σ' (stdLat A C g) →
      IsAdapted ρHC σ v' w' u' → LinearIndependent C (fun i => ∑ k, B i k • u' k) →
      Submodule.span A (Set.range fun i => ∑ k, B i k • u' k) = HT.eigQuot ρHC σ HV →
      ∃ ε : Aˣ, B.det = algebraMap A C ε * gm) →
    LinearIndependent C v → Submodule.span C (Set.range v) = HT.eigSp ρC σ →
    Submodule.span A (Set.range v) = HT.eigSub ρC σ (stdLat A C g) →
    LinearIndependent C w → Submodule.span C (Set.range w) = HT.eigSp ρC σ' →
    Submodule.span A (Set.range w) = HT.eigSub ρC σ' (stdLat A C g) →
    ∃ ε : Aˣ, Ap.det * Q.det = algebraMap A C ε * gm * P.det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.det_evaluated_frame | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.det_evaluated_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.det_evaluated_frame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionRatioOverlap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.InvDer
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.InvDer.JetCmp

theorem iter_sum {B J : Type} [AddCommMonoid B] (D : B →+ B) (s : Finset J) (k : ℕ) (g : J → B) :
    D^[k] (∑ j ∈ s, g j) = ∑ j ∈ s, D^[k] (g j) := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ_apply]
    rw [map_sum, ih]

theorem iter_const_mul {B : Type} [CommRing B] (D : B →+ B) (c : B) (hc : ∀ g, D (c * g) = c * D g) (k : ℕ) (g : B) :
    D^[k] (c * g) = c * D^[k] g := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ_apply]
    rw [hc, ih]

theorem jet_cmp_ring {B K : Type} [CommRing B] [Field K] (D : B →+ B)
    (hD : ∀ a b, D (a * b) = a * D b + b * D a) (e : B →+* K) (r : ℕ) (c a a' : Fin r → B) (u : B)
    (hc : ∀ j g, D (c j * g) = c j * D g) (hu : e u ≠ 0) (ha : ∀ j, a j = u * a' j) (i : ℕ)
    (h : ∀ k < i, ∑ j, e (c j) * e (D^[k] (a j)) = 0) :
    ∑ j, e (c j) * e (D^[i] (a j)) = e u * ∑ j, e (c j) * e (D^[i] (a' j)) := by
  have hval : ∀ (b : Fin r → B) (k : ℕ), e (D^[k] (∑ j, c j * b j)) = ∑ j, e (c j) * e (D^[k] (b j)) := by
    intro b k
    rw [iter_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iter_const_mul D (c j) (hc j), map_mul]
  have hΦ : ∑ j, c j * a j = u * ∑ j, c j * a' j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ha j]; ring
  have h1 : ∀ k < i, e (D^[k] (u * ∑ j, c j * a' j)) = 0 := by
    intro k hk
    rw [← hΦ, hval]; exact h k hk
  have h2 := jet_vanish_of_mul D hD e u _ hu i h1
  have h3 := jet_mul_of_vanish D hD e i u _ h2
  rw [← hΦ, hval, hval] at h3
  exact h3

theorem iter_der_res {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (v : epsAt (𝟙 (Sp R)) ⟶ G)
    (hv : IsTanAt G (𝟙 (Sp R)) v) {V V' : G.left.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (le : V' ≤ V) (k : ℕ) (g : Γ(G.left, V)) :
    (der v hv hV')^[k] ((G.left.presheaf.map (homOfLE le).op).hom g) =
      (G.left.presheaf.map (homOfLE le).op).hom ((der v hv hV)^[k] g) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply]
    rw [der_res v hv hV hV' le, ih]

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (l1 : V ≤ U) (l2 : W ≤ V) (l3 : W ≤ U) (g : Γ(X, U)) :
    (X.presheaf.map (homOfLE l2).op).hom ((X.presheaf.map (homOfLE l1).op).hom g) =
      (X.presheaf.map (homOfLE l3).op).hom g := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem jet_cmp : ∀ (R K : Type) [CommRing R] [Field K] (G : Over (Sp R)) [GrpObj G] (v₀ : epsAt (𝟙 (Sp R)) ⟶ G) (hv₀ : IsTanAt G (𝟙 (Sp R)) v₀) (y : Sp K ⟶ G.left) (V₀ V₁ : G.left.Opens) (h₀ : IsAffineOpen V₀) (h₁ : IsAffineOpen V₁) (t₀ : ⊤ ≤ y ⁻¹ᵁ V₀) (t₁ : ⊤ ≤ y ⁻¹ᵁ V₁) (t : ⊤ ≤ y ⁻¹ᵁ (V₀ ⊓ V₁)) (r : ℕ) (f : Fin r → Γ(G.left, V₀)) (f' : Fin r → Γ(G.left, V₁)) (uu : Γ(G.left, V₀ ⊓ V₁)), ev y _ t uu ≠ 0 → (∀ j, (G.left.presheaf.map (homOfLE (inf_le_left : V₀ ⊓ V₁ ≤ V₀)).op).hom (f j) = uu * (G.left.presheaf.map (homOfLE (inf_le_right : V₀ ⊓ V₁ ≤ V₁)).op).hom (f' j)) → ∀ (i : ℕ) (c : Fin r → R), (∀ k < i, ∑ j, bmap (y ≫ G.hom) (c j) * ev y V₀ t₀ ((der v₀ hv₀ h₀)^[k] (f j)) = 0) → ∑ j, bmap (y ≫ G.hom) (c j) * ev y V₀ t₀ ((der v₀ hv₀ h₀)^[i] (f j)) = ev y _ t uu * ∑ j, bmap (y ≫ G.hom) (c j) * ev y V₁ t₁ ((der v₀ hv₀ h₁)^[i] (f' j)) := by
  intro R K _ _ G _ v₀ hv₀ y V₀ V₁ h₀ h₁ t₀ t₁ t r f f' uu hu hf i c hyp
  obtain ⟨W, hWa, hWy, hWle'⟩ := exists_isAffineOpen_mem_and_subset
    (X := G.left) (x := y (default : PrimeSpectrum K)) (U := V₀ ⊓ V₁) (t (show _ ∈ (⊤ : (Sp K).Opens) from trivial))
  have hWle : W ≤ V₀ ⊓ V₁ := hWle'
  have tW : ⊤ ≤ y ⁻¹ᵁ W := by
    intro p _
    rw [Subsingleton.elim p (default : PrimeSpectrum K)]
    exact hWy
  have l0 : W ≤ V₀ := hWle.trans inf_le_left
  have l1 : W ≤ V₁ := hWle.trans inf_le_right
  have key := jet_cmp_ring (der v₀ hv₀ hWa) (der_mul v₀ hv₀ hWa) (ev y W tW) r
    (fun j => constFn G.hom W (c j))
    (fun j => (G.left.presheaf.map (homOfLE l0).op).hom (f j))
    (fun j => (G.left.presheaf.map (homOfLE l1).op).hom (f' j))
    ((G.left.presheaf.map (homOfLE hWle).op).hom uu)
    (fun j g => der_const_mul v₀ hv₀ hWa (c j) g)
    (by rw [ev_res y hWle t tW]; exact hu)
    (fun j => by
      have := congrArg (G.left.presheaf.map (homOfLE hWle).op).hom (hf j)
      rw [map_mul, res_res _ _ l0, res_res _ _ l1] at this
      exact this)
    i
    (fun k hk => by
      have := hyp k hk
      simp only [iter_der_res v₀ hv₀ h₀ hWa l0, ev_res y l0 t₀ tW, ev_const]
      exact this)
  simp only [iter_der_res v₀ hv₀ h₀ hWa l0, iter_der_res v₀ hv₀ h₁ hWa l1, ev_res y l0 t₀ tW, ev_res y l1 t₁ tW,
    ev_res y hWle t tW, ev_const] at key
  exact key

end GlobalTheory.CompanionTheory.Ar.InvDer.JetCmp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TruncatedExpansionPthPowerCoeffStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_expansion_pth_power_coeff : ∀ (A B : Type) [CommRing A] [CommRing B] (π : A →+* B) (δ : B) (p : ℕ) [Fact p.Prime], (p : B) = 0 → δ ^ (p + 1) = 0 → (∀ c c' : Fin (p + 1) → A, ∑ i, π (c i) * δ ^ (i : ℕ) = ∑ i, π (c' i) * δ ^ (i : ℕ) → c = c') → ∀ (u c₁ c₂ : Fin (p + 1) → A), u 0 = 1 → c₁ 0 = 1 → c₂ 0 = 1 → ∑ i, π (c₁ i) * δ ^ (i : ℕ) = (∑ i, π (u i) * δ ^ (i : ℕ)) ^ p * ∑ i, π (c₂ i) * δ ^ (i : ℕ) → c₁ (Fin.last p) = c₂ (Fin.last p) + u ⟨1, Nat.succ_lt_succ (Nat.Prime.pos Fact.out)⟩ ^ p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoefAlg.coeff_comparison | exact GlobalTheory.CompanionTheory.Ar.CoefAlg.coeff_comparison | (intros; apply GlobalTheory.CompanionTheory.Ar.CoefAlg.coeff_comparison <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistInverseIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_inverse_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H) (a : TwIso D g), ∃ a' : TwIso D g.symm, ∀ (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), (∀ (h : TwOK o g a) (h' : TwOK (twistObj o g a h) g.symm a'), Nonempty (ObjMap (twistObj (twistObj o g a h) g.symm a' h') o (𝟙 S))) ∧ ∀ (h : TwOK o g.symm a') (h' : TwOK (twistObj o g.symm a' h) g a), Nonempty (ObjMap (twistObj (twistObj o g.symm a' h) g a h') o (𝟙 S)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.twBack | exact GlobalTheory.CompanionTheory.Ar.twBack | (intros; apply GlobalTheory.CompanionTheory.Ar.twBack <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistModelsCommonPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_models_common_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (π' : Z ⟶ Y'.X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ Z) (x x' : Sp Ω ⟶ Xo.XF c), ξ ≫ π = x ≫ Y.j → ξ ≫ π' = x' ≫ Y'.j → x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → ∃ (t t' : SAB H Z) (tΩ : SAB H (Sp Ω)) (a : SABMap t Y.t π) (a' : SABMap t' Y'.t π') (m : SABMap tΩ t ξ) (m' : SABMap (twistSAB tΩ g) t' ξ) (u : SABMap tΩ Y.oF.t x) (u' : SABMap (twistSAB tΩ g) Y'.oF.t x'), m.φ ≫ a.φ = u.φ ≫ Y.m.φ ∧ m'.φ ≫ a'.φ = u'.φ ≫ Y'.m.φ ∧ u'.φ ≫ Y'.m0.toSABMap.φ = (twistMap u g).φ ≫ (twistMap Y.m0.toSABMap g).φ ≫ n.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwoModels.generic_fibre_twist | exact GlobalTheory.CompanionTheory.Ar.TwoModels.generic_fibre_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.TwoModels.generic_fibre_twist <;> assumption)
end

