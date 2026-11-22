import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0188
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0185
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientDifferentialMatrix
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientLattice
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.QQuasiCompact
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericCoordsDescendSubfield
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0191
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0050
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0142
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0135
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExists
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0010

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartFactorsThroughStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_part_factors_through : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (m : SABMap t' t f) (K : Type) [Field K] (z : Sp K ⟶ S') (P : AbPart t (z ≫ f)), ∃ m' : SABMap P.tK t' z, m'.φ ≫ m.φ = P.m.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AbPartPull.exists_sabMap_tK | exact GlobalTheory.CompanionTheory.Ar.AbPartPull.exists_sabMap_tK | (intros; apply GlobalTheory.CompanionTheory.Ar.AbPartPull.exists_sabMap_tK <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientDifferentialMatrixStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_quotient_differential_matrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (P : Matrix (Fin d') (Fin d) k), Q.IsDiff g gB P → ∀ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) → linQ Qs = P := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.linQ_eq_diff | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.linQ_eq_diff | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.linQ_eq_diff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGermPowerSeriesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_quotient_germ_power_series : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∃ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) ∧ (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.ChartMap.main | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.ChartMap.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.ChartMap.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGermSubstitutionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_quotient_germ_substitution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) → ∀ (m : ℕ) (a : 𝓞 E), (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (g.B.A.act a p.2)).comp (sub1 Qs m) = (sub1 Qs m).comp (jetSubstP m fun p : Fin 1 × Fin d' => psTrunc m (gB.B.A.act a p.2)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.substitution_action_commutes | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.substitution_action_commutes | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.substitution_action_commutes <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientLatticeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_quotient_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∃ (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (_ : Module.Free ℤ Λ) (_ : Module.Finite ℤ Λ) (P : Matrix (Fin d') (Fin d) k) (j : TensorProduct ℤ k Λ →ₗ[k] (Fin d → k)), Q.IsDiff g gB P ∧ Function.Surjective P.mulVec ∧ Function.Injective j ∧ (∀ u, P.mulVec u = 0 ↔ u ∈ LinearMap.range j) ∧ (∀ a, P * rho g.B a = rho gB.B a * P) ∧ ∀ a v, j (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ) v) = (rho g.B a).mulVec (j v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieSeq.lie_seq | exact GlobalTheory.CompanionTheory.Ar.LieSeq.lie_seq | (intros; apply GlobalTheory.CompanionTheory.Ar.LieSeq.lie_seq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeModelBaseChangeSubalgebra
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem model_passes_to_subalgebra : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (A : Over (Sp V)) [GrpObj A] (A₀ : Over (Sp k)) [GrpObj A₀] (φ : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap (algebraMap k V)) φ → ∀ R : Subalgebra k V, ∃ (_ : GrpObj (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R))))) (φ₁ : A.left ⟶ pullback A₀.hom (spMap (algebraMap k R))), IsGrpPullback (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) A₀ (spMap (algebraMap k R)) (pullback.fst _ _) ∧ IsGrpPullback A (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) (spMap R.val.toRingHom) φ₁ ∧ φ₁ ≫ pullback.fst _ _ = φ := by
  intro k V _ _ _ A _ A₀ _ φ h R
  have es : spMap R.val.toRingHom ≫ spMap (algebraMap k R) = spMap (algebraMap k V) := by
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have w : φ ≫ A₀.hom = (A.hom ≫ spMap R.val.toRingHom) ≫ spMap (algebraMap k R) := by
    rw [Category.assoc, es]; exact h.1.w
  let inst : GrpObj (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) :=
    inferInstanceAs (GrpObj ((Over.pullback (spMap (algebraMap k R))).obj A₀))
  have h₁ : IsGrpPullback (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) A₀ (spMap (algebraMap k R))
      (pullback.fst _ _) := isGrpPullback_pullback A₀ (spMap (algebraMap k R))
  have hf : pullback.lift φ (A.hom ≫ spMap R.val.toRingHom) w ≫ pullback.fst _ _ = φ := pullback.lift_fst _ _ _
  refine ⟨inst, pullback.lift φ (A.hom ≫ spMap R.val.toRingHom) w, h₁, ?_, hf⟩
  exact IsGrpPullback.cancel h₁ (h.congr es.symm hf.symm) (pullback.lift_snd _ _ _)

end GlobalTheory.CompanionTheory.Ar.Approx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockMatrixGramNormal
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BlockFrame

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

theorem quotNormSq_eq_of_blockFrame : ∀ (N j : ℕ) (hj : j ≤ N) (G G' T : Matrix (Fin N) (Fin N) ℂ) (Γ : Matrix (Fin (N - j)) (Fin (N - j)) ℂ), G.PosDef → G' = Tᴴ * G * T → (∀ a a', T (headIdx hj a) (headIdx hj a') = if a = a' then 1 else 0) → (∀ k a, T (tailIdx hj k) (headIdx hj a) = 0) → (∀ k k', T (tailIdx hj k) (tailIdx hj k') = if k = k' then 1 else 0) → (∀ a k, G' (headIdx hj a) (tailIdx hj k) = 0) → (∀ k k', G' (tailIdx hj k) (tailIdx hj k') = Γ k k') → quotNormSq hj G = Γ.det.re := by
  intro N j hj G G' T Γ hG hG' hT1 hT2 hT3 hG'1 hG'2
  obtain ⟨e, hel, her⟩ : ∃ e : Fin j ⊕ Fin (N - j) ≃ Fin N,
      (∀ a, e (Sum.inl a) = headIdx hj a) ∧ ∀ k, e (Sum.inr k) = tailIdx hj k :=
    ⟨finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hj)),
      fun a => by ext; simp [headIdx],
      fun k => by ext; simp [tailIdx]⟩
  have hhinj : Function.Injective (headIdx hj) := by
    intro a a' h
    rw [← hel, ← hel] at h
    exact Sum.inl_injective (e.injective h)
  have hht : ∀ a k, headIdx hj a ≠ tailIdx hj k := by
    intro a k h
    rw [← hel, ← her] at h
    exact Sum.inl_ne_inr (e.injective h)
  have hblocks : ∀ M : Matrix (Fin N) (Fin N) ℂ, M.submatrix e e =
      Matrix.fromBlocks (M.submatrix (headIdx hj) (headIdx hj))
        (M.submatrix (headIdx hj) (tailIdx hj))
        (M.submatrix (tailIdx hj) (headIdx hj)) (M.submatrix (tailIdx hj) (tailIdx hj)) := by
    intro M
    ext (a | k) (a' | k') <;> simp [hel, her]
  have hdet : ∀ M : Matrix (Fin N) (Fin N) ℂ, M.det = (M.submatrix e e).det := fun M =>
    (Matrix.det_submatrix_equiv_self e M).symm
  have hTdet : T.det = 1 := by
    have h1 : T.submatrix (headIdx hj) (headIdx hj) = 1 := by
      ext a a'; simp [hT1, Matrix.one_apply]
    have h0 : T.submatrix (tailIdx hj) (headIdx hj) = 0 := by
      ext k a; simp [hT2]
    have h2 : T.submatrix (tailIdx hj) (tailIdx hj) = 1 := by
      ext k k'; simp [hT3, Matrix.one_apply]
    rw [hdet T, hblocks T, h1, h0, h2, Matrix.det_fromBlocks_zero₂₁]
    simp
  have hdetG : G'.det = G.det := by
    rw [hG', Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hTdet]
    simp
  have hcol : T.submatrix id (headIdx hj) =
      (1 : Matrix (Fin N) (Fin N) ℂ).submatrix id (headIdx hj) := by
    ext y a'
    obtain ⟨z, rfl⟩ := e.surjective y
    rcases z with a | k
    · simp [hel, hT1, Matrix.one_apply, hhinj.eq_iff]
    · simp [her, hT2, Matrix.one_apply, (hht a' k).symm]
  have key : ∀ M : Matrix (Fin N) (Fin N) ℂ,
      (Mᴴ * G * M).submatrix (headIdx hj) (headIdx hj) =
        (M.submatrix id (headIdx hj))ᴴ * G * M.submatrix id (headIdx hj) := by
    intro M
    first
      | rfl
      | (ext a a'; simp [Matrix.mul_apply, Matrix.conjTranspose_apply])
  have hhh : G'.submatrix (headIdx hj) (headIdx hj) = G.submatrix (headIdx hj) (headIdx hj) := by
    rw [hG', key T, hcol, ← key 1]
    simp
  have hht' : G'.submatrix (headIdx hj) (tailIdx hj) = 0 := by
    ext a k; simp [hG'1]
  have htt : G'.submatrix (tailIdx hj) (tailIdx hj) = Γ := by
    ext k k'; simp [hG'2]
  have hdetblock : G.det = (G.submatrix (headIdx hj) (headIdx hj)).det * Γ.det := by
    rw [← hdetG, hdet G', hblocks G', hht', htt, Matrix.det_fromBlocks_zero₁₂, hhh]
  have hpos : 0 < (G.submatrix (headIdx hj) (headIdx hj)).det :=
    (hG.submatrix hhinj).det_pos
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hpos
  unfold quotNormSq
  rw [hdetblock, Complex.mul_re, ← him, zero_mul, sub_zero]
  exact mul_div_cancel_left₀ _ hre.ne'

end GlobalTheory.CompanionTheory.Ar.Cusp.BlockFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeTangentCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_tangent_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (X : Scheme.{0}) (t : SAB H X) (h : Sp C.R ⟶ X) (m : SABMap C.t t h) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (N : ℕ) (b : Fin N → Li) (x : Fin N → Fin C.g → C.R) (z : Fin n → ℂ) (Hm : Matrix (Fin C.g) (Fin C.g) ℂ) (w : Fin N → (epsAt (spMap (C.ψ z) ≫ h) ⟶ t.G)), C.IsRiem z Hm → (∀ k, M.ValAt _ (b k) (w k)) → (∀ k, (w k).left = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (x k)).left ≫ m.φ) → M.GramAt t.PP.L (spMap (C.ψ z) ≫ h) b (Matrix.of fun i j => (Real.pi : ℂ) * ((fun e => C.ψ z (x j e)) ⬝ᵥ Hm *ᵥ star (fun e => C.ψ z (x i e)))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RiemGram.gramAt_of_isRiem | exact GlobalTheory.CompanionTheory.Ar.RiemGram.gramAt_of_isRiem | (intros; apply GlobalTheory.CompanionTheory.Ar.RiemGram.gramAt_of_isRiem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeLatticeComparison
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptStalk

theorem isIntegrallyClosed_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (hg : IsCptGen ξ) (q : Cpt ξ) : IsIntegrallyClosed (regAt ξ q) := by
  let e : X.presheaf.stalk q.1 ≃+* regAt ξ q :=
    RingEquiv.ofBijective (genMap ξ q).rangeRestrict
      ⟨fun x y hxy => hg.inj q (congrArg Subtype.val hxy), (genMap ξ q).rangeRestrict_surjective⟩
  haveI := (hn q.1).1
  haveI := (hn q.1).2
  exact IsIntegrallyClosed.of_equiv e

theorem asIdeal_eq_bot {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ)
    {F : Type} [Field F] [NumberField F] (s : X ⟶ Spec (CommRingCat.of (𝓞 F))) (b : 𝓞 F →+* Ω)
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom b)) {p : Cpt ξ} (hp : p ∈ genFibre ℤ ξ) :
    (s p.1).asIdeal = ⊥ := by
  letI : Algebra (𝓞 F) Ω := b.toAlgebra
  have hreg := ConstReg.regular_const X Ω ξ (𝓞 F) s hs p
  refine (Submodule.eq_bot_iff _).2 fun o ho => ?_
  by_contra h0
  have hn : Ideal.absNorm (Ideal.span {o}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact h0
  have hmem : ((Ideal.absNorm (Ideal.span {o}) : ℕ) : 𝓞 F) ∈ (s p.1).asIdeal :=
    (Ideal.span_singleton_le_iff_mem _).2 ho (Ideal.absNorm_mem _)
  have hu := hp ((Ideal.absNorm (Ideal.span {o}) : ℕ) : ℤ) (by exact_mod_cast hn)
  have hu' : unitAt ξ p (algebraMap (𝓞 F) Ω ((Ideal.absNorm (Ideal.span {o}) : ℕ) : 𝓞 F)) := by
    simpa using hu
  exact ((hreg _).2 hg).1 hu' hmem

section Eig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
  {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {f : X' ⟶ X} (m : SABMap t' t f)
  {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] {ξ : Spec (CommRingCat.of Ω₀) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
  {i : Ω₀ →+* Ω} {V V' : Type} [AddCommGroup V] [Module Ω₀ V] [AddCommGroup V'] [Module Ω V']
  {M : LieModel t.G ξ V} {M' : LieModel t'.G ξ' V'} {ρ : 𝓞 E →+* Module.End Ω₀ V}
  {ρ' : 𝓞 E →+* Module.End Ω V'} {j : V →+ V'}

include m in

theorem map_act (hact : M.IsActOf t.act.act ρ) (hact' : M'.IsActOf t'.act.act ρ')
    (hj : ∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left) (a : 𝓞 E) (e : V) :
    j (ρ a e) = ρ' a (j e) := by
  have hcanc : ∀ v w : epsAt ξ' ⟶ t'.G, v.left ≫ m.φ = w.left ≫ m.φ → v = w := by
    intro v w h
    apply Over.OverMorphism.ext
    refine m.cart.1.hom_ext h ?_
    rw [Over.w v, Over.w w]
  refine M'.inj (hcanc _ _ ?_)
  rw [hj, hact a e, hact' a (j e), Over.comp_left, Over.comp_left, Category.assoc, m.act a,
    ← Category.assoc (M'.pt (j e)).left]
  exact congrArg (· ≫ _) (hj e).symm

include m in

theorem map_mem_eigSp (hact : M.IsActOf t.act.act ρ) (hact' : M'.IsActOf t'.act.act ρ')
    (hj : ∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left)
    (hsl : ∀ (a : Ω₀) (e : V), j (a • e) = i a • j e) (σ : 𝓞 E →+* Ω₀) {e : V} (he : e ∈ eigSp ρ σ) :
    j e ∈ eigSp ρ' (i.comp σ) := by
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at he ⊢
  intro a
  rw [← map_act m hact hact' hj, he a, hsl]
  rfl

theorem eigLat_eq_pull [CharZero Ω₀] [CharZero Ω] (cst : c.F →+* Ω₀) (hg : IsCptGen ξ) (hg' : IsCptGen ξ')
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i) (hact : M.IsActOf t.act.act ρ) (hact' : M'.IsActOf t'.act.act ρ')
    (hint : ∀ q : Cpt ξ, IsIntegrallyClosed (regAt ξ q)) (hint' : ∀ q : Cpt ξ', IsIntegrallyClosed (regAt ξ' q))
    (hj : ∀ e, (M'.pt (j e)).left ≫ m.φ = spMap (dualMap i) ≫ (M.pt e).left)
    (s : CMType H ⊕ CMType H) (q : Cpt ξ') (hq : ∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q) :
    M'.eigLat ρ' ((i.comp cst).comp (labelEmb c s)) q =
      (M.eigLat ρ (cst.comp (labelEmb c s))).pull ξ' f j q := by
  obtain ⟨j₂, hj₂, hsl₂, -, -, hlat₂⟩ := GlobalTheory.T.lie_model_dominant_hodge E H X t X' t' f m Ω₀ Ω ξ ξ' i V V' M M' hg hg' hd
  have hcanc : ∀ v w : epsAt ξ' ⟶ t'.G, v.left ≫ m.φ = w.left ≫ m.φ → v = w := by
    intro v w h
    apply Over.OverMorphism.ext
    refine m.cart.1.hom_ext h ?_
    rw [Over.w v, Over.w w]
  have hjj : j₂ = j := by
    ext e
    exact M'.inj (hcanc _ _ ((hj₂ e).trans (hj e).symm))
  subst hjj
  have hlat := hlat₂
  have hsl := hsl₂
  obtain ⟨h, -, h2⟩ := RegAtDom.regAt_dominates X Ω₀ ξ X' Ω ξ' f i hd q
  have hp : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r ⟨f q.1, h⟩ := fun r hr hn =>
    hn (by
      have := h2 hg' _ (natCast_mem _ r) (by rw [map_natCast]; exact not_not.1 (hq r hr))
      exact this)
  have hsum := (SatModel.lat_eq_iSup_of_char0 c t ξ hg cst M ρ hact (fun q _ => hint q)).2 _ hp
  have hind := (SatModel.lat_eq_iSup_of_char0 c t' ξ' hg' (i.comp cst) M' ρ' hact' (fun q _ => hint' q)).1
  have hle : ∀ u, ((M.eigLat ρ (cst.comp (labelEmb c u))).pull ξ' f j₂) q ≤ M'.lat q ⊓
      (eigSp ρ' ((i.comp cst).comp (labelEmb c u))).restrictScalars (regAt ξ' q) := by
    intro u
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h', e, he, rfl⟩
    have he2 : e ∈ eigSp ρ (cst.comp (labelEmb c u)) := he.2
    have h3 : j₂ e ∈ eigSp ρ' ((i.comp cst).comp (labelEmb c u)) := by
      rw [RingHom.comp_assoc]
      exact map_mem_eigSp m hact hact' hj₂ hsl _ he2
    refine ⟨?_, h3⟩
    show j₂ e ∈ M'.lat q
    rw [hlat]
    exact Submodule.subset_span ⟨h, e, he.1, rfl⟩
  have hall : M'.lat q ≤ ⨆ u, ((M.eigLat ρ (cst.comp (labelEmb c u))).pull ξ' f j₂) q := by
    rw [hlat]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h', e, he, rfl⟩
    have he1 : e ∈ ⨆ u, M.lat.inter (eigSp ρ (cst.comp (labelEmb c u))) ⟨f q.1, h⟩ := by
      rw [← hsum]
      exact he
    refine Submodule.iSup_induction _ (motive := fun e =>
      j₂ e ∈ ⨆ u, ((M.eigLat ρ (cst.comp (labelEmb c u))).pull ξ' f j₂) q) he1 (fun u e he => ?_) ?_
      (fun x y hx hy => ?_)
    · exact Submodule.mem_iSup_of_mem u (Submodule.subset_span ⟨h, e, he, rfl⟩)
    · simp only [map_zero]
      exact zero_mem _
    · simp only [map_add]
      exact add_mem hx hy
  refine le_antisymm ?_ (hle s)
  rintro x ⟨hx1, hx2⟩
  exact FlagStep.mem_of_mem_iSup_of_indep (regAt ξ' q) hind (fun u => (hle u).trans inf_le_right) s (hall hx1) hx2

end Eig

section Labels

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)

theorem labelEmb_inl (τ : CMType H) : labelEmb c (.inl τ) = tauIn c τ.1 := rfl

theorem labelEmb_inr (τ : CMType H) : labelEmb c (.inr τ) = tauIn c (ComplexEmbedding.conjugate τ.1) := by
  refine RingHom.ext fun a => Subtype.ext ?_
  change τ.1 ((H.bar a : 𝓞 E) : E) = (ComplexEmbedding.conjugate τ.1) (a : E)
  rw [H.bar_eq, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]

end Labels

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li), CptIn.IsTie Z 𝔐 i j → ∀ p ∈ genFibre ℤ 𝔐.ξ, 𝔐.f p.1 ∈ Subtype.val '' Z.genFib ∧ 𝔐.V (.inl τ) p = (Z.eig τ.1).pull 𝔐.ξ 𝔐.f j p ∧ 𝔐.V (.inr τ) p = (Z.eig (ComplexEmbedding.conjugate τ.1)).pull 𝔐.ξ 𝔐.f j p := by
  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 τ i j hT p hp
  obtain ⟨hd, hi, -, hpt⟩ := hT
  have hg' := 𝔐.tie.gen
  have hg := Z.gen
  haveI : CharZero Z.Ω := (RingHom.charZero_iff Z.inc.injective).1 inferInstance
  haveI : CharZero Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
  have hq : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r p := fun r hr hf =>
    hf (by simpa using hp (r : ℤ) (by exact_mod_cast hr.ne_zero))
  have hcore : ∀ s, 𝔐.V s p = (Z.M.eigLat Z.ρ (Z.inc.comp (labelEmb c s))).pull 𝔐.ξ 𝔐.f j p := by
    intro s
    have h1 : 𝔐.V s p = 𝔐.M.eigLat 𝔐.ρ (𝔐.cst.comp (labelEmb c s)) p :=
      Lat.patch_of_not S _ _ fun r hr => hq r (𝔐.S_prime r hr)
    rw [h1, ← hi]
    exact eigLat_eq_pull c 𝔐.m Z.inc hg hg' hd Z.act 𝔐.act (isIntegrallyClosed_regAt Y.normal hg)
      (isIntegrallyClosed_regAt 𝔐.normal hg') hpt s p hq
  refine ⟨?_, ?_, ?_⟩
  · have hb : (Y.s (𝔐.f p.1)).asIdeal = ⊥ := by
      have := asIdeal_eq_bot hg' (𝔐.f ≫ Y.s) (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) 𝔐.cst_over hp
      rwa [Scheme.Hom.comp_apply] at this
    refine ⟨⟨𝔐.f p.1, hd.specializes p⟩, ?_, rfl⟩
    show 𝔐.f p.1 ∈ Set.range (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
    obtain ⟨w⟩ : Nonempty (Sp c.F) := inferInstance
    have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := IsFractionRing.injective _ _
    have e : Y.s (𝔐.f p.1) = spMap (algebraMap (𝓞 c.F) c.F) w := by
      refine PrimeSpectrum.ext ?_
      rw [hb]
      refine ((Submodule.eq_bot_iff _).2 fun o ho => ?_).symm
      have h1 : algebraMap (𝓞 c.F) c.F o ∈ w.asIdeal := ho
      by_contra h0
      have h2 : algebraMap (𝓞 c.F) c.F o ≠ 0 := fun e0 => h0 (hβ (by rw [e0, map_zero]))
      exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (isUnit_iff_ne_zero.2 h2))
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback _ _ e
    exact ⟨z, hz⟩
  · rw [hcore, labelEmb_inl]
    rfl
  · rw [hcore, labelEmb_inr]
    rfl

end GlobalTheory.CompanionTheory.Ar.Flat.CptStalk
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComparisonOfInputsAvoidanceStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_of_inputs_avoidance : Inputs → AvoidStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → CmpSt := by
  first | exact @GlobalTheory.CompanionTheory.Relay.comparison_of_inputs_avoidance | exact GlobalTheory.CompanionTheory.Relay.comparison_of_inputs_avoidance | (intros; apply GlobalTheory.CompanionTheory.Relay.comparison_of_inputs_avoidance <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeSecond
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BlockSumFrame

theorem isVB_comap_of_range {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E'] (A : Lat ξ E')
    (S : Submodule Ω E') (i : E →ₗ[Ω] E') (hinj : Function.Injective i) (hrange : LinearMap.range i = S) {r : ℕ}
    (h : (Lat.comap A S.subtype).IsVB r ⊤) : (Lat.comap A i).IsVB r ⊤ := by
  have hmem : ∀ x, i x ∈ S := fun x => hrange ▸ LinearMap.mem_range_self i x
  let e : E →ₗ[Ω] S := i.codRestrict S hmem
  have hei : ∀ x, ((e x : S) : E') = i x := fun x => rfl
  have he_inj : Function.Injective e := fun x y hxy => hinj (by rw [← hei, ← hei, hxy])
  have he_surj : Function.Surjective e := fun s => by
    have : (s : E') ∈ LinearMap.range i := hrange ▸ s.2
    obtain ⟨x, hx⟩ := this
    exact ⟨x, Subtype.ext hx⟩
  let eq : E ≃ₗ[Ω] S := LinearEquiv.ofBijective e ⟨he_inj, he_surj⟩
  have heq : ∀ x, ((eq x : S) : E') = i x := fun x => rfl
  intro p hp
  obtain ⟨U, hpU, b, hspan, hfr⟩ := h p hp
  refine ⟨U, hpU, fun k => eq.symm (b k), ?_, fun q hq hqU => ?_⟩
  · have : Set.range (fun k => eq.symm (b k)) = eq.symm '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, ← LinearEquiv.coe_coe, ← Submodule.map_span, hspan, Submodule.map_top, LinearEquiv.range]
  · obtain ⟨hli, hst⟩ := hfr q hq hqU
    refine ⟨hli.map' eq.symm.toLinearMap (LinearEquiv.ker _), ?_⟩
    ext x
    have h1 : x ∈ Lat.comap A i q ↔ eq x ∈ Lat.comap A S.subtype q := Iff.rfl
    rw [h1, hst]
    let eR : E ≃ₗ[regAt ξ q] S := eq.restrictScalars (regAt ξ q)
    have hrng : Set.range b = eR '' Set.range (fun k => eq.symm (b k)) := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun k => (eq.apply_symm_apply (b k)).symm)
    rw [hrng, ← LinearEquiv.coe_coe, ← Submodule.map_span]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := eR.injective hyx
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩

theorem frame_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (τ : CMType H) (cc : (k : K) → J k) (f : Ω) (b : Fin Dc.N → W τ) (h : genPt Or.𝔐.ξ ⤳ centre z), CoordsAt Or.𝔐.ξ Dc.y z w → IsFrameOver Dc.y (Dc.W τ) cc f b → InFrameDomain Dc.y cc f w → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ := by
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z w τ cc f b h hw hfr hd
  have hT : CoordTie ℤ Or.𝔐.ξ (segreCoord Dc.y) := Or.𝔐.tie
  have hrk : labelRk D (Or.bg τ) + labelRk D (Or.sm τ) = Dc.N := by
    rw [Or.rk_bg, Or.rk_sm]
    exact Nat.add_sub_cancel' Dc.j_le_N
  have hsum := GlobalTheory.T.pair_lattice_sum_comap E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 (Or.bg τ) (Or.sm τ) (Or.bg_ne_sm τ τ)
  rw [hrk] at hsum
  have hvb : (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsVB Dc.N ⊤ :=
    isVB_comap_of_range _ _ (Or.i τ) (Or.i_inj τ) (Or.i_range τ) hsum
  obtain ⟨c1, c2⟩ := GlobalTheory.T.frame_domain_in_segre_chart Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y hT z w cc f h hw hd
  exact (GlobalTheory.T.segre_chart_bundle Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y (W τ) Dc.N (Dc.W τ) _ hT hvb (Or.lat τ) cc f b hfr.1 hfr.2.1
    hfr.2.2.1).1 hfr _ c1 c2

end GlobalTheory.CompanionTheory.Ar.BlockSumFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DetLatticeFlagTensor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.det_lattice_flag_tensor : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (b₀ : Fin r → V), LinearIndependent Ω b₀ → L.IsFlagVBOn Set.univ b₀ → detLat L b₀ = Lat.tens (fun i => L.gr b₀ i) (fun _ => 1) := by
  first | exact @LevelTowerAlt.determinant_lattice_graded_tensor | exact LevelTowerAlt.determinant_lattice_graded_tensor
end

