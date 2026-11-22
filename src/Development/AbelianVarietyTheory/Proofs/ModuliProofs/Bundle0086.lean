import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0081
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0047
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeDescendsGaloisCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianScheme_descent_of_galoisCover : ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (G : Over X) [GrpObj G] (ν : Ga → (G.left ⟶ G.left)), IsGaloisCover Ga ρ π → IsQProjOver (G.hom ≫ π ≫ sY) → IsAbelianScheme G → (∀ a, IsGrpPullback G G (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → ∃ (G' : Over Y) (_ : GrpObj G') (φ : G.left ⟶ G'.left), IsAbelianScheme G' ∧ IsGrpPullback G G' π φ ∧ IsGaloisCover Ga ν φ := by
  first | exact @GlobalTheory.abelianScheme_descends_galoisCover | exact GlobalTheory.abelianScheme_descends_galoisCover | (intros; apply GlobalTheory.abelianScheme_descends_galoisCover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoveringAndSmoothnessIffOfSeparableSplitting
section
noncomputable section

namespace GlobalTheory.CoveringCompare

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke

section Fibres

def SplitOver {S : Scheme.{0}} (G : Over S) [GrpObj G] (x : S) (k : Type) [Field k] [Algebra (S.residueField x) k] :
    Prop :=
  ∃ T : SplitExt (Sp k), T.IsGt ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) k)) ≫ S.fromSpecResidueField x)).obj G)

theorem splitOver_of_torusExtension {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (x : S) (k : Type)
    [Field k] [Algebra (S.residueField x) k]
    (h : Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap (S.residueField x) k))).obj
      ((Over.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x)).obj G)))) :
    SplitOver G x k := by
  obtain ⟨T⟩ := h
  obtain ⟨i, hi, -⟩ := grpPullback_iso
    ((isGrpPullback_pullback ((Over.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x)).obj G)
      (spMap (algebraMap (S.residueField x) k))).comp (isGrpPullback_pullback G _))
    (isGrpPullback_pullback G _)
  have := hG.comm
  exact exists_splitExt_isGt_of_torusExtension _ _ ⟨torusExtOfIso i T⟩

theorem exists_finite_splitOver {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (x : S) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra (S.residueField x) k),
      FiniteDimensional (S.residueField x) k ∧ SplitOver G x k := by
  have h₀ := IsSemiAbelian.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x) G hG
  have := h₀.smooth
  obtain ⟨k, hk, T⟩ := exists_finite_torusExtension (S.residueField x) (AlgebraicClosure (S.residueField x)) _
    inferInstance h₀.quasiCompact h₀.separated (h₀.fibres _ _)
  exact ⟨k, inferInstance, inferInstance, hk, splitOver_of_torusExtension G hG x k T⟩

def SeparableSplitting : Prop :=
  ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], IsSemiAbelian G →
    ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧
      Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap k k'))).obj G))

end Fibres

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section One

variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem isChartAt_iff (Y : Model Xo c β) (x : Y.X) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ξ : Sp R ⟶ Y.X) :
    CoveringAbelianLocusSmooth.IsChartAt Y x R ξ ↔ UniformizationBase.IsUnifBase Y R ξ ∧ ξ (IsLocalRing.closedPoint R) = x :=
  ⟨fun ⟨a, b, c, d, e, f, g⟩ => ⟨⟨a, b, c, d, f, g⟩, e⟩, fun ⟨⟨a, b, c, d, f, g⟩, e⟩ => ⟨a, b, c, d, e, f, g⟩⟩

theorem covered_iff (Y : Model Xo c β) (p : ℕ) : (∀ x, UniformizationBase.CovAt Y p x) ↔ CoveringAbelianLocusSmooth.CoveredByCharts Y p := by
  refine forall_congr' fun x => ⟨?_, ?_⟩
  · rintro ⟨n, R, _, _, _, ξ, h₁, h₂⟩
    exact ⟨n, R, _, _, _, ξ, fun i => (isChartAt_iff Y x _ _).2 (h₁ i),
      fun V C _ _ _ _ _ _ _ _ => h₂ C V⟩
  · rintro ⟨n, R, _, _, _, ξ, h₁, h₂⟩
    exact ⟨n, R, _, _, _, ξ, fun i => (isChartAt_iff Y x _ _).1 (h₁ i),
      fun C V _ _ _ _ _ _ _ _ => h₂ V C⟩

theorem abLocusSmooth_iff (Y : Model Xo c β) : UniformizationBase.AbLocusSmooth Y ↔ CoveringAbelianLocusSmooth.AbLocusSmooth Y := Iff.rfl

theorem splitFibres_iff_imperfect (Y : Model Xo c β) :
    Y.SplitFibres ↔ ∀ x : Y.X, ¬ PerfectField (Y.X.residueField x) →
      ∃ (k : Type) (_ : Field k) (_ : Algebra (Y.X.residueField x) k),
        FiniteDimensional (Y.X.residueField x) k ∧ Algebra.IsSeparable (Y.X.residueField x) k ∧
          SplitOver Y.t.G x k := by
  refine ⟨fun h x _ => h x, fun h x => ?_⟩
  by_cases hx : PerfectField (Y.X.residueField x)
  · obtain ⟨k, _, _, hk, hs⟩ := exists_finite_splitOver Y.t.G Y.t.semi x
    exact ⟨k, inferInstance, inferInstance, hk, inferInstance, hs⟩
  · exact h x hx

theorem splitFibres_of_separableSplitting (h : SeparableSplitting) (Y : Model Xo c β) : Y.SplitFibres := fun x => by
  obtain ⟨k, _, _, hk, hs, T⟩ := h (Y.X.residueField x) _
    (IsSemiAbelian.pullback (show Sp (Y.X.residueField x) ⟶ Y.X from Y.X.fromSpecResidueField x) Y.t.G Y.t.semi)
  exact ⟨k, inferInstance, inferInstance, hk, hs, splitOver_of_torusExtension Y.t.G Y.t.semi x k T⟩

end One

theorem goodPrime_iff (l : Level H) (p : ℕ) : UniformizationBase.GoodPrime l p ↔ CoveringAbelianLocusSmooth.GoodPrime l p := Iff.rfl

theorem smoothnessLemma_iff : UniformizationBase.SmoothnessLemma ↔ CoveringAbelianLocusSmooth.SmoothnessLemma := Iff.rfl

def CoveringForSplitFibres : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits →
    ∀ Y : LocalSystem Xo p W, N2 Y → ∀ i : Idx H p, (Y i).SplitFibres → ∀ x : (Y i).X, UniformizationBase.CovAt (Y i) p x

theorem coveringLemma_iff_restricted : CoveringAbelianLocusSmooth.CoveringLemma ↔ CoveringForSplitFibres :=
  ⟨fun h E _ _ _ H D Xo p W hp hW Y hY i hs => (covered_iff _ p).2 (h E H D Xo p W hp hW Y hY i hs),
    fun h E _ _ _ H D Xo p W hp hW Y hY i hs => (covered_iff _ p).1 (h E H D Xo p W hp hW Y hY i hs)⟩

theorem coveringLemma_imp (h : UniformizationBase.CoveringLemma) : CoveringAbelianLocusSmooth.CoveringLemma :=
  fun E _ _ _ H D Xo p W hp hW Y hY i _ => (covered_iff _ p).1 (h E H D Xo p W hp hW Y hY i)

theorem coveringLemma_iff_of_separableSplitting (h : SeparableSplitting) :
    UniformizationBase.CoveringLemma ↔ CoveringAbelianLocusSmooth.CoveringLemma :=
  ⟨coveringLemma_imp, fun hB E _ _ _ H D Xo p W hp hW Y hY i =>
    (covered_iff _ p).2 (hB E H D Xo p W hp hW Y hY i (splitFibres_of_separableSplitting h _))⟩

theorem typings_compare :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
      (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : ℕ),
      (∀ (x : Y.X) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X),
        CoveringAbelianLocusSmooth.IsChartAt Y x R ξ ↔ UniformizationBase.IsUnifBase Y R ξ ∧ ξ (IsLocalRing.closedPoint R) = x) ∧
      ((∀ x, UniformizationBase.CovAt Y p x) ↔ CoveringAbelianLocusSmooth.CoveredByCharts Y p) ∧
      (UniformizationBase.AbLocusSmooth Y ↔ CoveringAbelianLocusSmooth.AbLocusSmooth Y) ∧ (UniformizationBase.GoodPrime l p ↔ CoveringAbelianLocusSmooth.GoodPrime l p) ∧
      (Y.SplitFibres ↔ ∀ x : Y.X, ¬ PerfectField (Y.X.residueField x) →
        ∃ (k : Type) (_ : Field k) (_ : Algebra (Y.X.residueField x) k),
          FiniteDimensional (Y.X.residueField x) k ∧ Algebra.IsSeparable (Y.X.residueField x) k ∧
            SplitOver Y.t.G x k)) ∧
    (UniformizationBase.SmoothnessLemma ↔ CoveringAbelianLocusSmooth.SmoothnessLemma) ∧
    (CoveringAbelianLocusSmooth.CoveringAndSmoothness ↔ CoveringForSplitFibres ∧ UniformizationBase.SmoothnessLemma) ∧
    (UniformizationBase.CoveringAndSmoothness → CoveringAbelianLocusSmooth.CoveringAndSmoothness) :=
  ⟨fun _ _ _ _ _ _ l _ _ _ _ _ Y p =>
      ⟨fun x R _ _ _ ξ => isChartAt_iff Y x R ξ, covered_iff Y p, abLocusSmooth_iff Y, goodPrime_iff l p,
        splitFibres_iff_imperfect Y⟩,
    smoothnessLemma_iff, and_congr coveringLemma_iff_restricted smoothnessLemma_iff.symm,
    fun h => ⟨coveringLemma_imp h.1, smoothnessLemma_iff.1 h.2⟩⟩

theorem coveringAndSmoothness_iff_of_separableSplitting (h : SeparableSplitting) :
    UniformizationBase.CoveringAndSmoothness ↔ CoveringAbelianLocusSmooth.CoveringAndSmoothness :=
  and_congr (coveringLemma_iff_of_separableSplitting h) smoothnessLemma_iff

end GlobalTheory.CoveringCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStrOfTrivTheta
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.Moduli

theorem cubicalStr_of_triv_theta : Out.Laws → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.Rigidified A M → Triv (Theta A M) → ∃ L : RigLB A, L.L = M ∧ Nonempty (CubicalStr A L) := by
  intro hL S A _ _ hA M hM hR hT
  obtain ⟨t, ht⟩ := hT
  obtain ⟨r, hr⟩ := hR
  obtain ⟨t', ht', hn⟩ := GlobalTheory.AbLaw.Cube.exists_normalised hM t ht
  exact ⟨⟨M, r, hM, hr⟩, rfl, ⟨GlobalTheory.AbLaw.Cube.cubicalOfNormalised
    (by cases hL; assumption) hA ⟨M, r, hM, hr⟩ t' ht' hn⟩⟩

end GlobalTheory.Moduli
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EpsPtScaleZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.PointUnif

section Deriv

open GlobalTheory.TangentOrigin GlobalTheory.LieEtale

variable {g g' : ℕ} {X Y : Scheme.{0}}

theorem evalPt_comp {R : Type} [CommRing R] (x : Sp R ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U) (f : Γ(Y, U)) :
    evalPt (x ≫ φ) U h f = evalPt x (φ ⁻¹ᵁ U) h ((φ.app U).hom f) := by
  have := Scheme.Hom.appLE_comp_appLE x φ U (φ ⁻¹ᵁ U) ⊤ le_rfl h
  unfold evalPt
  rw [← this, Scheme.Hom.app_eq_appLE]
  rfl

theorem valAt'_comp (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · rw [valAt'_eq_evalPt _ _ h, valAt'_eq_evalPt x (φ ⁻¹ᵁ U) h, evalPt_comp]
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U := h
    unfold valAt'
    rw [dif_neg h, dif_neg h']

theorem isHolTo_comp {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (he : IsHolTo Set.univ e) (φ : X ⟶ Y) :
    IsHolTo Set.univ fun z => e z ≫ φ := by
  intro U f
  simp only [valAt'_comp]
  exact he (φ ⁻¹ᵁ U) ((φ.app U).hom f)

theorem isHolTo_linear {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (he : IsHolTo Set.univ e)
    (F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : IsHolTo Set.univ fun z => e (F z) := by
  intro U f
  have hF : Differentiable ℂ F := F.toContinuousLinearMap.differentiable
  exact ⟨(he U f).1.preimage hF.continuous, (he U f).2.comp hF.differentiableOn fun z hz => hz⟩

theorem isDerivAt0_iff {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X} :
    IsDerivAt0 e w v ↔ spMap fstC ≫ v = e 0 ∧ ∀ (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)),
      (evalPt v U h f).snd = fderiv ℂ (fun z => valAt' (e z) U f) 0 w := Iff.rfl

theorem deriv_comp {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (h : IsDerivAt0 e w v) (φ : X ⟶ Y) : IsDerivAt0 (fun z => e z ≫ φ) w (v ≫ φ) := by
  rw [isDerivAt0_iff] at h ⊢
  refine ⟨by rw [← h.1, Category.assoc], fun U hU f => ?_⟩
  simp only [valAt'_comp]
  rw [evalPt_comp]
  exact h.2 _ _ _

theorem deriv_unique {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v v' : Sp (DualNumber ℂ) ⟶ X}
    (h : IsDerivAt0 e w v) (h' : IsDerivAt0 e w v') : v = v' := by
  rw [isDerivAt0_iff] at h h'
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (e 0 (default : PrimeSpectrum ℂ))) isOpen_univ
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := fun q _ => by
    rw [Subsingleton.elim (α := PrimeSpectrum ℂ) q default]; exact hx
  have hv : ⊤ ≤ v ⁻¹ᵁ U := (top_le_preimage_iff v U).2 (h.1 ▸ h0)
  have hv' : ⊤ ≤ v' ⁻¹ᵁ U := (top_le_preimage_iff v' U).2 (h'.1 ▸ h0)
  refine ext_evalPt hU hv hv' (RingHom.ext fun f => TrivSqZeroExt.ext ?_ ((h.2 U hv f).trans (h'.2 U hv' f).symm))
  have key : ∀ (u : Sp (DualNumber ℂ) ⟶ X) (hu : ⊤ ≤ u ⁻¹ᵁ U) (y : Sp ℂ ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      spMap fstC ≫ u = y → (evalPt u U hu f).fst = evalPt y U hy f := by
    rintro u hu y hy rfl
    exact (evalPt_spMap_comp fstC u U hu hy f).symm
  exact (key v hv _ h0 h.1).trans (key v' hv' _ h0 h'.1).symm

theorem deriv_linear {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} (he : IsHolTo Set.univ e)
    (F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) {w : Fin g' → ℂ} {v : Sp (DualNumber ℂ) ⟶ X} :
    IsDerivAt0 (fun z => e (F z)) w v ↔ IsDerivAt0 e (F w) v := by
  rw [isDerivAt0_iff, isDerivAt0_iff, map_zero]
  refine and_congr_right fun h0 => forall₃_congr fun U hU f => ?_
  have hU0 : ⊤ ≤ e 0 ⁻¹ᵁ U := h0 ▸ (top_le_preimage_iff v U).1 hU
  have hd : DifferentiableAt ℂ (fun z => valAt' (e z) U f) (F.toContinuousLinearMap 0) := by
    rw [map_zero]
    exact (he U f).2.differentiableAt ((he U f).1.mem_nhds ⟨trivial, hU0⟩)
  have := (hd.hasFDerivAt.comp 0 F.toContinuousLinearMap.hasFDerivAt).fderiv
  rw [map_zero] at this
  have e2 : fderiv ℂ (fun z => valAt' (e (F z)) U f) 0 = _ := this
  rw [e2]
  rfl

theorem deriv_smul {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)} {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ X}
    (h : IsDerivAt0 e w v) (c : ℂ) : IsDerivAt0 e (c • w) (spMap (epsScale c) ≫ v) := by
  rw [isDerivAt0_iff] at h ⊢
  have e0 : spMap fstC ≫ spMap (epsScale c) ≫ v = spMap fstC ≫ v := by
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => TrivSqZeroExt.fst_map _ r
  refine ⟨e0.trans h.1, fun U hU f => ?_⟩
  have hv : ⊤ ≤ v ⁻¹ᵁ U := (top_le_preimage_iff v U).2 (e0 ▸ (top_le_preimage_iff _ U).1 hU)
  rw [evalPt_spMap_comp _ v U hv hU, map_smul, ← h.2 U hv f]
  simp [epsScale]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S}

abbrev epsTwo (y : Sp ℂ ⟶ S) : Over S := Over.mk (spMap (algebraMap ℂ (TrivSqZeroExt ℂ (ℂ × ℂ))) ≫ y)

def toTwo (y : Sp ℂ ⟶ S) (l : ℂ →ₗ[ℂ] ℂ × ℂ) : epsTwo y ⟶ epsPt y :=
  Over.homMk (spMap (TrivSqZeroExt.map l).toRingHom) (by
    change _ ≫ _ ≫ y = _ ≫ y
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => (TrivSqZeroExt.map l).commutes r)

def ofTwo (y : Sp ℂ ⟶ S) (l : ℂ × ℂ →ₗ[ℂ] ℂ) : epsPt y ⟶ epsTwo y :=
  Over.homMk (spMap (TrivSqZeroExt.map l).toRingHom) (by
    change _ ≫ _ ≫ y = _ ≫ y
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => (TrivSqZeroExt.map l).commutes r)

theorem ofTwo_toTwo (l : ℂ →ₗ[ℂ] ℂ × ℂ) (l' : ℂ × ℂ →ₗ[ℂ] ℂ) :
    ofTwo y l' ≫ toTwo y l = epsPtScale y (l' (l 1)) := by
  refine Over.OverMorphism.ext ?_
  change spMap _ ≫ spMap _ = spMap _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun x => ?_
  have : l' (l x.snd) = l' (l 1) * x.snd := by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, _root_.mul_one]
  ext <;> simp [this, epsScale]

theorem epsPtScale_one : epsPtScale y 1 = 𝟙 _ := by
  refine Over.OverMorphism.ext ?_
  change spMap _ = 𝟙 _
  rw [← Spec.map_id]
  congr 1
  ext x <;> simp [epsScale]

theorem epsPtScale_zero {v : epsPt y ⟶ G} (hv : epsPtZero y ≫ v = 1) : epsPtScale y 0 ≫ v = 1 := by
  let s : epsPt y ⟶ Over.mk y := Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl
  have : epsPtScale y 0 = s ≫ epsPtZero y := by
    refine Over.OverMorphism.ext ?_
    change spMap _ = spMap _ ≫ spMap _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun x => ?_
    ext <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]
  rw [this, Category.assoc, hv, MonObj.comp_one]

theorem deriv_mul {e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)} {w w' : Fin g → ℂ} {v v' : epsPt y ⟶ G}
    (h0 : e 0 = (1 : Over.mk y ⟶ G).left)
    (h : IsDerivAt0 e w v.left) (h' : IsDerivAt0 e w' v'.left) : IsDerivAt0 e (w + w') (v * v').left := by
  have hv : epsPtZero y ≫ v = 1 := Over.OverMorphism.ext (h.1.trans h0)
  have hv' : epsPtZero y ≫ v' = 1 := Over.OverMorphism.ext (h'.1.trans h0)
  have hm : epsPtZero y ≫ (v * v') = 1 := by rw [MonObj.comp_mul, hv, hv', _root_.mul_one]
  have hm' : spMap fstC ≫ (v * v').left = e 0 := (congrArg (·.left) hm).trans h0.symm
  rw [isDerivAt0_iff] at h h' ⊢
  refine ⟨hm', fun U hU f => ?_⟩
  let u : epsTwo y ⟶ G := (toTwo y (LinearMap.inl ℂ ℂ ℂ) ≫ v) * (toTwo y (LinearMap.inr ℂ ℂ ℂ) ≫ v')
  have hu : ∀ l, ofTwo y l ≫ u = (epsPtScale y (l (1, 0)) ≫ v) * (epsPtScale y (l (0, 1)) ≫ v') := fun l => by
    simp only [u, MonObj.comp_mul, ← Category.assoc, ofTwo_toTwo]
    rfl
  have h1 : ofTwo y (LinearMap.fst ℂ ℂ ℂ) ≫ u = v := by
    rw [hu, LinearMap.fst_apply, LinearMap.fst_apply, epsPtScale_one, epsPtScale_zero hv', _root_.mul_one, Category.id_comp]
  have h2 : ofTwo y (LinearMap.snd ℂ ℂ ℂ) ≫ u = v' := by
    rw [hu, LinearMap.snd_apply, LinearMap.snd_apply, epsPtScale_one, epsPtScale_zero hv, _root_.one_mul, Category.id_comp]
  have h3 : ofTwo y (LinearMap.fst ℂ ℂ ℂ + LinearMap.snd ℂ ℂ ℂ) ≫ u = v * v' := by
    rw [hu]; simp [epsPtScale_one]
  have hU0 : ⊤ ≤ e 0 ⁻¹ᵁ U := hm' ▸ (top_le_preimage_iff _ U).1 hU
  have hU1 : ⊤ ≤ v.left ⁻¹ᵁ U := (top_le_preimage_iff _ U).2 (h.1 ▸ hU0)
  have hU2 : ⊤ ≤ v'.left ⁻¹ᵁ U := (top_le_preimage_iff _ U).2 (h'.1 ▸ hU0)
  have hsub : ∀ p q : PrimeSpectrum (TrivSqZeroExt ℂ (ℂ × ℂ)), p = q := by
    have k : ∀ z : PrimeSpectrum (TrivSqZeroExt ℂ (ℂ × ℂ)), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
      constructor
      · intro ha
        by_contra h0
        exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
      · intro ha
        refine z.2.mem_of_pow_mem 2 ?_
        rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
        exact z.asIdeal.zero_mem
    intro p q
    ext a
    rw [k, k]
  have hUu : ⊤ ≤ u.left ⁻¹ᵁ U := fun p _ => by
    let q : (epsPt y).left := spMap fstC (default : PrimeSpectrum ℂ)
    have hq : v.left q ∈ U := hU1 (Set.mem_univ q)
    rw [← h1] at hq
    rw [hsub p ((ofTwo y (LinearMap.fst ℂ ℂ ℂ)).left q)]
    exact hq
  have key : ∀ (l : ℂ × ℂ →ₗ[ℂ] ℂ) (x : epsPt y ⟶ G) (hx : ⊤ ≤ x.left ⁻¹ᵁ U), ofTwo y l ≫ u = x →
      (evalPt (R := DualNumber ℂ) x.left U hx f).snd =
        l (evalPt (R := TrivSqZeroExt ℂ (ℂ × ℂ)) u.left U hUu f).snd := by
    rintro l x hx rfl
    exact (congrArg TrivSqZeroExt.snd (evalPt_spMap_comp (TrivSqZeroExt.map l).toRingHom u.left U hUu hx f)).trans
      (TrivSqZeroExt.snd_map _ _)
  rw [map_add, ← h.2 U hU1 f, ← h'.2 U hU2 f, key _ _ hU h3, key _ _ hU1 h1, key _ _ hU2 h2]
  rfl

end Deriv

end GlobalTheory.PointUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfSurjectiveAppTopOfSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem eq_one_of_surjective_appTop_of_section {X S : Scheme.{0}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
    (hs : Function.Surjective p.appTop.hom) (a : Γ(X, ⊤)) (ha : o.appTop.hom a = 1) : a = 1 := by
  obtain ⟨b, rfl⟩ := hs a
  have e : o.appTop.hom (p.appTop.hom b) = b := by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, ho, Scheme.Hom.id_appTop]
    rfl
  rw [e.symm.trans ha, map_one]

theorem exists_sabMap_of_isProper_of_lbIso : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (φ : t'.G.left ⟶ t.G.left), IsProper t.G.hom → IsGrpPullback t'.G t.G f φ → LBIso t'.PP.L (t.PP.L.pull φ) → (∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left) → ∃ m : SABMap t' t f, m.φ = φ := by
  intro hG E _ _ _ H S S' t t' f φ hp gp ⟨w, hw⟩ hact
  obtain ⟨w', hw', Hr⟩ := TripleMap.exists_rigidified t.PP.isLB t'.PP.isLB w ((isGen_iff w).1 hw) (eSec t.G)
    (eSec t'.G) t'.G.hom (Over.w _) f (cubeMapOf gp).e_comm t.PP.rig t.PP.rigGen t'.PP.rig t'.PP.rigGen
  have hp' : IsProper t'.G.hom := MorphismProperty.of_isPullback gp.1 hp
  have hA := AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi
  have hA₃ := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA)
  refine ⟨⟨cubeMapOf gp, gp, rfl, hact, (isPullCubical_iff _ _ _).2 ⟨w', hw', Hr,
    TripleMap.pmaps_cubical gp t.cub t'.cub hw' fun a ha => ?_⟩⟩, rfl⟩
  let o := lift (1 : 𝟙_ (Over S') ⟶ t'.G) (lift (1 : 𝟙_ (Over S') ⟶ t'.G) (1 : 𝟙_ (Over S') ⟶ t'.G))
  have h₁ : pullU o.left ⊤ a = 1 := unit_ext fun y _ =>
    (gm_pull (𝟙 _) o.left y ⊤ trivial a).trans ((congrArg (fun q => gm q y ⊤ a) (Category.id_comp _)).trans
      ((ha y).trans (map_one _).symm))
  exact Units.ext (eq_one_of_surjective_appTop_of_section (G3 t'.G).hom o.left (Over.w o) (hG _ _ hA₃).2 a.val
    (congrArg Units.val h₁))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwayProjectiveFormsThroughPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_away_projective_forms_through_points : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (σ Hh : Type) [Finite σ] [Finite Hh] (p : Hh → σ → R) (Q : Polynomial ℚ) (d : ℕ) (P : Set (Ideal R)), DenseP P → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K) (I : Ideal (MvPolynomial σ K)), RingHom.ker x = q ∧ CutBy I Q d (fun h i => x (p h i))) → ∀ q₀ ∈ P, ∃ f : R, f ∉ q₀ ∧ (∀ e ≥ d, Module.Projective (Localization.Away f) (↥(MvPolynomial.homogeneousSubmodule σ (Localization.Away f) e) ⧸ ((vanIdeal d (fun h i => (algebraMap R (Localization.Away f)) (p h i))).restrictScalars (Localization.Away f)).comap (MvPolynomial.homogeneousSubmodule σ (Localization.Away f) e).subtype)) ∧ ∀ (K : Type) [Field K] (x : (Localization.Away f) →+* K), (vanIdeal d (fun h i => (algebraMap R (Localization.Away f)) (p h i))).map (MvPolynomial.map x) = vanIdeal d (fun h i => x ((algebraMap R (Localization.Away f)) (p h i))) := by
  first | exact @GlobalTheory.ZM.FormsFamily.exists_away_projective_vanIdeal | exact GlobalTheory.ZM.FormsFamily.exists_away_projective_vanIdeal | (intros; apply GlobalTheory.ZM.FormsFamily.exists_away_projective_vanIdeal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDiagonalCoordinatesOfDeterminantConditionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diagonal_coordinates_of_determinantCondition : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (ty : Fin P.g → (E →+* ℂ)), u.IsAH Hm χ → IsTypeFn H D.p D.q ty → DetCond D act (𝟙 (Sp ℂ)) H.rt0 → ∃ h : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ), ∀ (a : 𝓞 E) z, u.ex (h (fun i => ty i (a : E) * z i)) = u.ex (h z) ≫ act.act a := by
  first | exact @GlobalTheory.exists_diagonal_coordinates_of_detCond | exact GlobalTheory.exists_diagonal_coordinates_of_detCond | (intros; apply GlobalTheory.exists_diagonal_coordinates_of_detCond <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfRigidifiedFaithfullyFlatDescentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gen_of_rigidified_faithfullyFlat_descent : Out.GlobalFnsSt → ∀ (S S' : Scheme.{0}) (π : S' ⟶ S) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Flat π → Surjective π → QuasiCompact π → (∃ t : (N.pull (eSec A)).Gen, t.IsGen) → (∃ t : (N.pull (pullback.fst A.hom π)).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  first | exact @GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange | exact GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange | (intros; apply GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedPartialLineBundlesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_rigidified_partial_line_bundles : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (I : Type) (U : I → S.Opens) (M : I → LB X), e ≫ p = 𝟙 S → (∀ (V : S.Opens) (u : Γ(X, p ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → iSup U = ⊤ → (∀ i, ⨆ a, (M i).U a = p ⁻¹ᵁ U i) → (∀ i, ∀ (a : (M i).ι) (x : X), x ∈ (M i).U a → gm (𝟙 X) x ((M i).U a ⊓ (M i).U a) ((M i).g a a) = 1) → (∀ i, ∃ r : ((M i).pull e).Gen, r.IsGen) → (∀ i j, LBIso (M i) (M j)) → ∃ L : LB X, L.IsLB ∧ (∃ r : (L.pull e).Gen, r.IsGen) ∧ ∀ i, LBIso (M i) L := by
  first | exact @GlobalTheory.PartialBundleGlue.exists_glue | exact GlobalTheory.PartialBundleGlue.exists_glue | (intros; apply GlobalTheory.PartialBundleGlue.exists_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmoothOfRelDimOfIsUnitProperFlatStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_smoothOfRelDim_of_isUnit_proper_flat : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → SmoothOfRelativeDimension g (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → SmoothOfRelativeDimension g (pullback.snd s (spMap φ)) := by
  first | exact @GlobalTheory.SmoothNearFibre.exists_smoothOfRelativeDimension_of_isUnit | exact GlobalTheory.SmoothNearFibre.exists_smoothOfRelativeDimension_of_isUnit | (intros; apply GlobalTheory.SmoothNearFibre.exists_smoothOfRelativeDimension_of_isUnit <;> assumption)
end

