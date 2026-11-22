import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieMultIffExistsFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0011
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0204
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0182
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0145
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0184
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0196
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0028
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0238

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPeriodRiemannLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FibreAtPeriod

section Reparam

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left}

theorem exists_reparam_isAH {g g' : ℕ} (u : HolUnif A L g') (X : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ))
    (Hm : Matrix (Fin g') (Fin g') ℂ) (Hf : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (hAH : u.IsAH Hm χ)
    (hHf : Hf.IsHermitian) (hf : ∀ x y, hermForm Hf x y = hermForm Hm (X x) (X y)) :
    ∃ (u₂ : HolUnif A L g) (χ₂ : u₂.Λ → ℂ), (∀ z, u₂.ex z = u.ex (X z)) ∧ (∀ z, z ∈ u₂.Λ ↔ X z ∈ u.Λ) ∧
      u₂.IsAH Hf χ₂ ∧ ∀ w v, u.IsDiff (X w) v → u₂.IsDiff w v := by
  have hg : g = g' := by simpa using X.finrank_eq
  subst hg
  refine ⟨GlobalTheory.holUnifReparam u X (fun _ => 1) (differentiable_const _) (fun _ => one_ne_zero),
    fun l => χ ⟨X l, l.2⟩, fun _ => rfl, fun _ => Iff.rfl, ⟨hHf, ?_, fun l => hAH.2.2.1 _, ?_⟩, ?_⟩
  · intro z hz
    have h := hAH.2.1 (X z) ((LinearEquiv.map_ne_zero_iff X).2 hz)
    have e := hf z z
    unfold hermForm at e
    rw [e]
    exact h
  · intro l i z hz
    have h := hAH.2.2.2 ⟨X l, l.2⟩ i (X z) hz
    have e1 := hf z l
    have e2 := hf l l
    unfold hermForm at e1 e2
    show u.fr i (X z) / 1 = χ ⟨X l, l.2⟩ * Complex.exp (Real.pi * (z ⬝ᵥ Hf.mulVec (star (l : Fin g → ℂ))) +
      Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hf.mulVec (star (l : Fin g → ℂ)))) * (u.fr i (X (z + l)) / 1)
    rw [div_one, div_one, map_add, h, e1, e2]
  · intro w v hv U h f
    rw [hv U h f]
    have key := X.toContinuousLinearEquiv.comp_right_fderiv
      (f := fun z => valAt' (u.ex z).left U f) (x := 0)
    have h2 := congrArg (fun T => T w) key
    simp only [map_zero] at h2
    exact h2.symm

end Reparam

theorem fibreLatVec_of_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (R : RiemLat E g (FU.Di i).La) (P : (FU.Di i).La →+ (Fin g → ℂ)) (h : Matrix (Fin g) (Fin g) ℂ), IsPeriod (FU.Di i) ty P → R.form = (FU.Di i).EF → IsUnit h.det → (∀ x, P x = h *ᵥ R.P x) → ∀ (A₀ : Type) (x : A₀ → Fin g → ℂ) (v : A₀ → (epsAt (FU.u i P) ⟶ Xo.univ.t.G)), (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (h *ᵥ x a) (v a).left) → FibreLatVec Xo.univ.t (FU.u i P) R x v := by
  intro E _ _ _ H D l Xo σ g ty FU i R P h hP hRf hdet hPh A₀ x v hd
  let hl : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := h.toLinearEquiv' (h.invertibleOfIsUnitDet hdet)
  have hla : ∀ z, hl z = h *ᵥ z := fun z => by
    show Matrix.toLin' h z = h *ᵥ z
    exact Matrix.toLin'_apply h z
  have hlP : ∀ a, hl (R.P a) = P a := fun a => by rw [hla, hPh]
  have hlP' : ∀ a, hl.symm (P a) = R.P a := fun a => by rw [← hlP, hl.symm_apply_apply]
  obtain ⟨Q, ψ, -, hQ, hQL, -⟩ := GlobalTheory.exists_polAV_pullback_of_isLocalRing E H _ Xo.univ.t Xo.univ.proper
    Xo.univ.ample Xo.univ.ktriv ℂ (FU.u i P)
  obtain ⟨u, H₂, χ, F, hAH, -, d₂, -, hF, hΛ, hE⟩ :=
    GlobalTheory.familyUnif_fibre_theta GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1.weil E H D l Xo σ g ty FU i P hP
      Q ψ hQ hQL
  obtain ⟨w, hw⟩ := hQL

  have hLB : (Xo.univ.t.PP.L.pull ψ).IsLB := LB.isLB_pull Xo.univ.t.PP.isLB ψ
  let ub : HolUnif Q.A (Xo.univ.t.PP.L.pull ψ) Q.g := GlobalTheory.ArchMetricCompare.carry u Q.isLB hLB hw
  have hAHb : ub.IsAH H₂ χ := GlobalTheory.ArchMetricCompare.carry_isAH Q.isLB hLB hw hAH
  let T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin Q.g → ℂ) := hl.trans F
  have hf : ∀ x y, hermForm R.Hm x y = hermForm H₂ (T x) (T y) := fun x y => by
    have key := GlobalTheory.KeyFam.SamePeriod.hermForm_eq_of_im H₂ F.toLinearMap R.Hm hl.symm.toLinearMap hP.2.2.2.1 (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      have h1 := hE a b
      have h2 := R.im a b
      rw [hRf] at h2
      show (hermForm H₂ (F (P a)) (F (P b))).im = (hermForm R.Hm (hl.symm (P a)) (hl.symm (P b))).im
      rw [hlP', hlP', h1]
      exact h2.symm) (hl x) (hl y)
    show _ = hermForm H₂ (F (hl x)) (F (hl y))
    simpa using key.symm
  obtain ⟨u', χ', hue, huΛ, huAH, hud⟩ := exists_reparam_isAH ub T H₂ R.Hm χ hAHb R.herm hf
  have hex : ∀ q, (u'.ex q).left ≫ ψ = (FU.ex i P (hl q)).left := fun q => by
    rw [hue]
    exact hF (hl q)

  have hB : ∀ (a : 𝓞 E) (p : Fin g → ℂ), hl (R.B a p) = fun k => ty k (a : E) * hl p k := fun a p => by
    let Da : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      { toFun := fun z k => ty k (a : E) * z k
        map_add' := fun z z' => by
          ext k
          simp [mul_add]
        map_smul' := fun c z => by
          ext k
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          ring }
    let N : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      hl.toLinearMap.comp ((R.B a).comp hl.symm.toLinearMap) - Da
    have hN : N.restrictScalars ℝ = 0 := LinearMap.ext_on hP.2.2.2.1 (by
      rintro _ ⟨y, rfl⟩
      show hl (R.B a (hl.symm (P y))) - (fun k => ty k (a : E) * P y k) = 0
      rw [hlP', ← R.act, hlP, sub_eq_zero]
      exact funext (hP.1 a y))
    have h0 : N (hl p) = 0 := congrArg (fun f => f (hl p)) hN
    have h1 : hl (R.B a (hl.symm (hl p))) - (fun k => ty k (a : E) * hl p k) = 0 := h0
    rw [hl.symm_apply_apply] at h1
    exact sub_eq_zero.1 h1
  refine ⟨Q.A, inferInstance, ψ, u', χ', hQ, huAH, fun a p => ?_, fun y y' hy => ?_, fun p => ?_, fun a => ?_⟩
  · rw [hex, hB, FU.ex_lin i P hP a (hl p), Over.comp_left, ← Category.assoc, hex]
  · exact hP.2.1 (by rw [hPh, hPh, hy])
  · rw [huΛ]
    show F (hl p) ∈ u.Λ ↔ _
    rw [hΛ]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, hl.injective (by rw [hlP, hy])⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, (hlP y).symm⟩
  · have hd' : IsDerivAt0 (fun z => (FU.ex i P z).left) (hl (x a)) (v a).left := by
      rw [hla]
      exact hd a
    obtain ⟨t, ⟨h₁, h₂⟩, -⟩ := d₂ (F (hl (x a)))
    refine ⟨t, GlobalTheory.VerticalDeriv.isDerivAt0_unique
      (Flat.PerGram.isDerivAt0_of_fibre ψ u F.toLinearMap hF h₁ h₂) hd', hud (x a) t h₂⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.FibreAtPeriod
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionsFlatAgree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.RepScalar

theorem exchange {F W : Type} [Field F] [AddCommGroup W] [Module F W] {n : ℕ} {t u : Fin n → W}
    (ht : LinearIndependent F t) (h : Submodule.span F (Set.range t) = Submodule.span F (Set.range u)) :
    LinearIndependent F u ∧ ∃ A : Matrix (Fin n) (Fin n) F, (∀ i, t i = ∑ k, A i k • u k) ∧ IsUnit A.det := by
  have hu : LinearIndependent F u := by
    rw [linearIndependent_iff_card_eq_finrank_span]
    have := linearIndependent_iff_card_eq_finrank_span.1 ht
    rw [Set.finrank, ← h]
    exact this
  refine ⟨hu, ?_⟩
  have h1 : ∀ i, ∃ c : Fin n → F, ∑ k, c k • u k = t i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun F).1 (h ▸ Submodule.subset_span ⟨i, rfl⟩)
  have h2 : ∀ i, ∃ c : Fin n → F, ∑ k, c k • t k = u i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun F).1 (h.symm ▸ Submodule.subset_span ⟨i, rfl⟩)
  choose A hA using h1
  choose B hB using h2
  have hAB : (Matrix.of A) * (Matrix.of B) = 1 := by
    ext i l
    have key : ∑ m, ((Matrix.of A * Matrix.of B) i m - (1 : Matrix (Fin n) (Fin n) F) i m) • t m = 0 := by
      have e1 : ∑ m, (Matrix.of A * Matrix.of B) i m • t m = t i := by
        conv_rhs => rw [← hA i]
        simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul, ← hB, Finset.smul_sum, smul_smul]
        exact Finset.sum_comm
      have e2 : ∑ m, (1 : Matrix (Fin n) (Fin n) F) i m • t m = t i := by
        simp [Matrix.one_apply]
      simp only [sub_smul, Finset.sum_sub_distrib, e1, e2, sub_self]
    have := Fintype.linearIndependent_iff.1 ht _ key l
    exact sub_eq_zero.1 this
  refine ⟨Matrix.of A, fun i => (hA i).symm, ?_⟩
  have := congrArg Matrix.det hAB
  rw [Matrix.det_mul, Matrix.det_one] at this
  exact IsUnit.of_mul_eq_one _ this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_value_frame (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U)
    (hβ : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) (τ : E →+* ℂ) (F : Type) [Field F]
    (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (hy : y ≫ pullback.snd _ _ = spMap βF)
    (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (n : ℕ) (b : Fin n → Z.V)
    (hb : (Z.eig τ).IsFrameAt b ⟨centre (y ≫ Y.j), h⟩) (v : Vecs y n)
    (hv : IsEigFrame Xo.univ.t.act (under y) (βF.comp (tauIn c τ)) v) :
    ∃ (v₀ : Vecs y n) (A : Matrix (Fin n) (Fin n) F),
      IsEigFrame Xo.univ.t.act (under y) (βF.comp (tauIn c τ)) v₀ ∧
      (∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b i) v' ∧ SameVec Y y (v₀ i) v') ∧
      (∀ i, IsComb (A i) v₀ (v i)) ∧ IsUnit A.det := by
  obtain ⟨W, _, _, Mu, Mz, ρ, hu, hz, hS⟩ := GlobalTheory.T.universal_lie_model_pullback E H D l Xo c O β Y F y
  obtain ⟨m, e, cf, h1, h2⟩ := GlobalTheory.T.eigen_projector_field_embedding E c.F (tauIn c τ)
  obtain ⟨u, hval, hspan⟩ := GlobalTheory.T.lie_model_action_specialize Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M F (y ≫ Y.j) h W Mz (𝓞 E) Y.t.act Z.ρ ρ c.F Z.inc βF
    (tauIn c τ) m e cf n b Z.gen Y.t.semi.smooth Z.act hz (GlobalTheory.T.constants_at_field_point E H D l Xo c O β Y U Z F βF y hβ hy h) h1
    (h2 Z.Ω Z.V Z.inc Z.ρ) hb
  choose t ht using fun i => Mu.onto _ (hv.1 i).1
  have hvt : v = fun i => Mu.pt (t i) := funext fun i => (ht i).symm
  subst hvt
  obtain ⟨hti, hts⟩ := (Test.isEigFrame_iff Mu Xo.univ.t.act ρ hu _ t).1 hv
  obtain ⟨hui, A, hA, hAu⟩ := exchange hti (hts.trans hspan.symm)
  refine ⟨fun i => Mu.pt (u i), A, (Test.isEigFrame_iff Mu Xo.univ.t.act ρ hu _ u).2 ⟨hui, hspan⟩,
    fun i => ⟨Mz.pt (u i), hval i, hS (u i)⟩, fun i => (Test.isComb_iff Mu (A i) u (t i)).2 (hA i), hAu⟩

theorem valAt_mul {X : Scheme.{0}} {Ω R : Type} [Field Ω] [CommRing R] [IsLocalRing R]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {z : Spec (CommRingCat.of R) ⟶ X} {a b : Ω} {r s : R}
    (ha : ValAt ξ z a r) (hb : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, u, hu, rfl⟩ := ha
  obtain ⟨_, w, hw, rfl⟩ := hb
  exact ⟨h, u * w, by rw [map_mul, hu, hw], map_mul _ _ _⟩

theorem valAt_eq {X : Scheme.{0}} {Ω R : Type} [Field Ω] [CommRing R] [IsLocalRing R]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ) {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r r' : R}
    (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨h1, s, hs, rfl⟩ := h
  obtain ⟨h2, s', hs', rfl⟩ := h'
  rw [hξ.inj ⟨centre z, h1⟩ (hs.trans hs'.symm)]

theorem exists_eq_smul_wedge {X : Scheme.{0}} {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Lat ξ V} {x : Cpt ξ} {p : ℕ} {f : Fin p → V}
    (hf : L.IsFrameAt f x) {α : Ω} {a : ⋀[Ω]^p V} (hα : α ≠ 0)
    (hL : L.wedge p x = Submodule.span (regAt ξ x) {α • a}) :
    ∃ g₀ : Ω, a = g₀ • exteriorPower.ιMulti Ω p f := by
  have hmem : exteriorPower.ιMulti Ω p f ∈ L.wedge p x :=
    Submodule.subset_span ⟨f, fun i => by
      rw [hf.2]; exact Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  rw [hL] at hmem
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hmem
  have hr' : ((r : Ω) * α) • a = exteriorPower.ιMulti Ω p f := by
    rw [mul_smul]; exact hr
  have hne := WedgeFrame.wedge_ne_zero f hf.1
  have h0 : (r : Ω) * α ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hr'; exact hne hr'.symm
  exact ⟨((r : Ω) * α)⁻¹, by rw [← hr', smul_smul, inv_mul_cancel₀ h0, one_smul]⟩

end GlobalTheory.CompanionTheory.Ar.Flat.RepScalar

namespace GlobalTheory.CompanionTheory.Ar.Flat

open RepScalar

theorem exists_const_of_flatOnModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ φ' : FrameFn Xo c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → Z.IsGeom → IsLineFn U τ φ → FlatOnModel Z τ φ → IsLineFn U τ φ' → FlatOnModel Z τ φ' → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ φ φ' hβ hτ hg hl hfl hl' hfl'
  obtain ⟨-, a, b, hgen, hrep⟩ := hfl
  obtain ⟨-, a', b', hgen', hrep'⟩ := hfl'
  obtain ⟨x, s, t, hx, ht, hst, ha', hb'⟩ := GlobalTheory.T.line_generator_geometric E H D l Xo c O β Y U Z τ a a' b b' hβ hg hgen hgen'
  refine ⟨x, hx, fun F _ βF y v w hf => ?_⟩
  obtain ⟨hy, hU, hv, hw⟩ := id hf
  have hpt : y (IsLocalRing.closedPoint F) ∈ U := hU ⟨_, rfl⟩
  have hsp : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := ((Z.closure _).1 hpt).map Y.j.continuous
  have hmem : (⟨centre (y ≫ Y.j), hsp⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib := ⟨Y.jQ (y (IsLocalRing.closedPoint F)), rfl⟩
  obtain ⟨h1, h2, -, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hβ hτ
  obtain ⟨U₁, hU₁, b₁, -, hb₁⟩ := h1 _ hmem
  obtain ⟨U₂, hU₂, b₂, -, hb₂⟩ := h2 _ hmem
  have f₁ := hb₁ _ hmem hU₁
  have f₂ := hb₂ _ hmem hU₂
  obtain ⟨v₀, A, hv₀, hval₁, hA, hAu⟩ := exists_value_frame Y U Z hβ.2.2 τ F βF y hy hsp D.p b₁ f₁ v hv
  obtain ⟨w₀, B, hw₀, hval₂, hB, -⟩ := exists_value_frame Y U Z hβ.2.2 (ComplexEmbedding.conjugate τ) F βF y hy hsp D.q b₂ f₂ w hw
  have hf₀ : IsFramed U τ βF y v₀ w₀ := ⟨hy, hU, hv₀, hw₀⟩
  obtain ⟨-, hb0, hco⟩ := hgen
  obtain ⟨α, κ, hα, hκ, hWa, hWb, -⟩ := hco _ hmem
  obtain ⟨ga, hga⟩ := exists_eq_smul_wedge f₁ hα hWa
  obtain ⟨gb, hgb⟩ := exists_eq_smul_wedge f₂ hκ hWb
  have hgb0 : gb ≠ 0 := by
    rintro rfl
    exact hb0 (by rw [hgb, zero_smul])
  have r1 := hrep F βF y v₀ w₀ b₁ b₂ ga gb hf₀ hga hgb hval₁ hval₂
  have r2 := hrep' F βF y v₀ w₀ b₁ b₂ (s * ga) (t * gb) hf₀ (by rw [ha', hga, smul_smul])
    (by rw [hb', hgb, smul_smul]) hval₁ hval₂
  have r3 := valAt_mul (GlobalTheory.T.constants_at_field_point E H D l Xo c O β Y U Z F βF y hβ.2.2 hy hsp x) r1
  have e : s * ga / (t * gb) = Z.inc x * (ga / gb) := by
    rw [hst]; field_simp
  rw [e] at r2
  have e2 : φ' F y v₀ w₀ = βF x * φ F y v₀ w₀ := valAt_eq Z.gen r2 r3
  have c1 := hl.chg F βF y v₀ w₀ v w A B hf₀ hf hA hB
  have c2 := hl'.chg F βF y v₀ w₀ v w A B hf₀ hf hA hB
  refine hAu.mul_left_injective ?_
  show φ' F y v w * A.det = βF x * φ F y v w * A.det
  rw [c2, e2, _root_.mul_assoc (βF x), _root_.mul_assoc (βF x), c1]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMultLabelRank
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgeCpt

theorem lieMult_label_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (s : CMType H ⊕ CMType H), LieMult 𝔐.t.act 𝔐.ξ (𝔐.emb s) (labelRk D s) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J y 𝔐 s
  letI := 𝔐.acg
  letI := 𝔐.mod
  obtain ⟨U, hU, b, hspan, hfr⟩ := 𝔐.vb s ⟨genPt 𝔐.ξ, specializes_refl _⟩ (Set.mem_univ _)
  exact (Fl.Test.lieMult_iff_exists_frame _ _ _ _).2
    ⟨_, (Fl.Test.isEigFrame_iff 𝔐.M 𝔐.t.act 𝔐.ρ 𝔐.act (𝔐.emb s) b).2
      ⟨(hfr _ (Set.mem_univ _) hU).1, hspan⟩⟩

end GlobalTheory.CompanionTheory.Ar.HodgeCpt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalGoodReductionExtends
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TrivialModel

theorem exists_model_of_rank_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp L)), IsPrincipal t → (∀ (σ : L →+* ℂ) (τ : 𝓞 E →+* ℂ), LieMult t.act (spMap σ) τ 0) → ∃ t' : SAB H (Sp (𝓞 L)), Nonempty (SABMap t t' (spMap (algebraMap (𝓞 L) L))) :=
  @PositivityTheory.Xgn.trivial_type_good_reduction

end GlobalTheory.CompanionTheory.Ar.TrivialModel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalLieMultiplicityTypeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_lie_multiplicity_type : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (F : IntermediateField ℚ ℂ) (hK : KA l ≤ F) (t : SAB H (Sp F)), IsPrincipal t → l.A = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : F →+* k) (τ : 𝓞 E →+* k), (τ H.rt = g (IntermediateField.inclusion hK (baseKA l).ρ) → LieMult t.act (spMap g) τ D.p) ∧ (τ H.rt ≠ g (IntermediateField.inclusion hK (baseKA l).ρ) → LieMult t.act (spMap g) τ D.q)) → ∀ I : TateIso D ℂ (Over.mk (spMap (algebraMap F ℂ)) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (∀ a : D.La, ∃ s : 𝟙_ (Over (Sp F)) ⟶ t.G, toUnit _ ≫ s = I.ev l.M a) → ∃ o : Obj D l (baseKA l) (spMap (IntermediateField.inclusion hK).toRingHom), o.t = t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SabModel.obj_of_sections | exact GlobalTheory.CompanionTheory.Ar.SabModel.obj_of_sections | (intros; apply GlobalTheory.CompanionTheory.Ar.SabModel.obj_of_sections <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TateIsoDatumExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.SabModel

theorem datum_tate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] (t : SAB H (Sp L)), IsPrincipal t → ∀ (σ : L →+* ℂ) (p q : ℕ), (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult t.act (spMap σ) τ p) ∧ (τ H.rt ≠ H.rt0 → LieMult t.act (spMap σ) τ q)) → ∃ D : Datum H, D.p = p ∧ D.q = q ∧ Nonempty (TateIso D ℂ (Over.mk (spMap σ) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))) :=
  @PositivityTheory.Xgn.shimura_datum_tate_isomorphism

end GlobalTheory.CompanionTheory.Ar.SabModel
end

