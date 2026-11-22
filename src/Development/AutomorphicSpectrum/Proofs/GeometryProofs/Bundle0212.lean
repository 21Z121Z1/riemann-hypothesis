import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0106
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0005
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HeightBoundComplexConjugate
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0209
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0090
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0101
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0050
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0056
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0116
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0020
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0111
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ExistsRingHomComplex
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.DegreeMultiplicationNorm
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0208
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0065
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIsMaximalOfIsFractionRing
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLineDegreeFormula
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0210

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianBoundConjugate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif

theorem abBound_of_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (h : LieMetric M y) (C : ℝ) (z : Sp ℂ ⟶ X), AbBound t h C (spMap (starRingEnd ℂ) ≫ z) → AbBound t h C z := by
  exact @PositivityTheory.Xgn.height_bound_complex_conjugate

end GlobalTheory.CompanionTheory.Ar.QuotUnif
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartLatticeSpecializationValue
section
open ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt

open MvPolynomial

theorem norm_le_one_of_monic_eval₂ {𝕜 : Type} [NormedField 𝕜] [IsUltrametricDist 𝕜] {R : Type} [CommRing R]
    (φ : R →+* 𝕜) (hφ : ∀ r, ‖φ r‖ ≤ 1) {f : Polynomial R} (hmon : f.Monic) {x : 𝕜}
    (hf : f.eval₂ φ x = 0) : ‖x‖ ≤ 1 := by
  by_contra! h
  rw [hmon.as_sum] at hf
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hf
  have hsum : x ^ f.natDegree = -∑ i ∈ Finset.range f.natDegree, φ (f.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_left hf
  have hpos : 0 < f.natDegree := by
    rcases Nat.eq_zero_or_pos f.natDegree with h0 | h0
    · rw [h0] at hsum
      simp at hsum
    · exact h0
  have hle : ‖∑ i ∈ Finset.range f.natDegree, φ (f.coeff i) * x ^ i‖ ≤ ‖x‖ ^ (f.natDegree - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' : i ≤ f.natDegree - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖φ (f.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (f.natDegree - 1) :=
          mul_le_mul (hφ _) (pow_le_pow_right₀ h.le hi') (by positivity) zero_le_one
      _ = ‖x‖ ^ (f.natDegree - 1) := one_mul _
  have h1 : ‖x‖ ^ f.natDegree ≤ ‖x‖ ^ (f.natDegree - 1) := by
    rw [← norm_pow, hsum, norm_neg]
    exact hle
  have h2 : ‖x‖ ^ (f.natDegree - 1) < ‖x‖ ^ f.natDegree := pow_lt_pow_right₀ h (by omega)
  linarith

section Ring

variable {Ω : Type} [Field Ω] {𝕜 : Type} [NormedField 𝕜] [IsUltrametricDist 𝕜]

def unitBall (A : Subring Ω) (ev : A →+* 𝕜) : Subring Ω where
  carrier := {x | ∃ h : x ∈ A, ‖ev ⟨x, h⟩‖ ≤ 1}
  mul_mem' := by
    rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    refine ⟨A.mul_mem ha hb, ?_⟩
    have e : (⟨a * b, A.mul_mem ha hb⟩ : A) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [e, map_mul, norm_mul]
    exact mul_le_one₀ ha1 (norm_nonneg _) hb1
  one_mem' := by
    refine ⟨A.one_mem, ?_⟩
    have e : (⟨1, A.one_mem⟩ : A) = 1 := rfl
    rw [e, map_one, norm_one]
  add_mem' := by
    rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    refine ⟨A.add_mem ha hb, ?_⟩
    have e : (⟨a + b, A.add_mem ha hb⟩ : A) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [e, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha1 hb1)
  zero_mem' := by
    refine ⟨A.zero_mem, ?_⟩
    have e : (⟨0, A.zero_mem⟩ : A) = 0 := rfl
    rw [e, map_zero, norm_zero]
    exact zero_le_one
  neg_mem' := by
    rintro a ⟨ha, ha1⟩
    refine ⟨A.neg_mem ha, ?_⟩
    have e : (⟨-a, A.neg_mem ha⟩ : A) = -⟨a, ha⟩ := rfl
    rw [e, map_neg, norm_neg]
    exact ha1

theorem norm_ev_le_one (A : Subring Ω) (ev : A →+* 𝕜) (R : Subalgebra ℤ Ω)
    (hR : ∀ x ∈ R, ∃ h : x ∈ A, ‖ev ⟨x, h⟩‖ ≤ 1) {t : Ω} (ht : t ∈ integralClosure R Ω) (hb : t ∈ A) :
    ‖ev ⟨t, hb⟩‖ ≤ 1 := by
  obtain ⟨f, hmon, hf⟩ := ht
  let ψ : R →+* A :=
    { toFun := fun r => ⟨r, (hR r r.2).1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h1 : f.eval₂ ψ ⟨t, hb⟩ = 0 := by
    apply Subtype.ext
    exact (Polynomial.hom_eval₂ f ψ A.subtype ⟨t, hb⟩).trans hf
  have h2 : f.eval₂ (ev.comp ψ) (ev ⟨t, hb⟩) = 0 := by
    rw [← Polynomial.hom_eval₂, h1, map_zero]
  exact norm_le_one_of_monic_eval₂ (ev.comp ψ) (fun r => (hR r r.2).2) hmon h2

end Ring

section Pt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {y : (Σ k, ι k) → Ω} {𝕜 : Type} [Field 𝕜] {z : (Σ k, ι k) → 𝕜}

theorem isMultiHomog_X_single [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm b
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases hb : b = k
  · subst hb
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hj (by simpa using h.symm)
    · simp
  · rw [Pi.single_eq_of_ne hb]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hb (congrArg Sigma.fst h).symm

theorem hasVal_coord [DecidableEq K] (k : K) (i : ι k) :
    Small.HasVal y (Pi.single k 1) (y ⟨k, i⟩) z (z ⟨k, i⟩) := by
  refine ⟨Pi.single k 1, 0, X ⟨k, i⟩, 1, isMultiHomog_X_single k i, ?_, fun b => ?_, by simp, by simp, by simp⟩
  · exact ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one
  · by_cases hb : b = k
    · subst hb
      simp
    · simp [Pi.single_eq_of_ne hb]

theorem hasVal_ratio_coord {k : K} (i c : ι k) (hy : y ⟨k, c⟩ ≠ 0) (hz : z ⟨k, c⟩ ≠ 0) :
    Small.HasVal y 0 (y ⟨k, i⟩ / y ⟨k, c⟩) z (z ⟨k, i⟩ / z ⟨k, c⟩) := by
  classical
  refine ⟨Pi.single k 1, Pi.single k 1, X ⟨k, i⟩, X ⟨k, c⟩, isMultiHomog_X_single k i, isMultiHomog_X_single k c,
    fun b => by simp, ?_, by simpa using hz, ?_⟩
  · simp only [aeval_X]
    field_simp
  · simp only [aeval_X]
    field_simp

theorem coord_ne_zero (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) (p : Σ k, ι k) (h : z p ≠ 0) : y p ≠ 0 := by
  intro h0
  have hm : (X p : MRing ι) ∈ mCoordIdeal y := by
    show mConeMap y (X p) = 0
    simp [mConeMap, h0]
  exact h (by simpa using hz.2 _ hm)

end Pt

theorem exists_hasVal_norm_le_supMet :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [NormedField 𝕜] [IsUltrametricDist 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → ∀ (A : Subring Ω) (ev : A →+* 𝕜) (a : K → ℤ), ∀ s ∈ chartLatNm y a 1, (∀ (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ k i, ∃ hb : y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A, Small.HasVal y 0 (y ⟨k, i⟩ / y ⟨k, c k⟩) z (ev ⟨_, hb⟩)) ∧ ∃ hb : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) ∈ A, Small.HasVal y 0 (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) z (ev ⟨_, hb⟩)) → ∃ w, Small.HasVal y a s z w ∧ ‖w‖ ≤ Small.supMet a z := by
  classical
  intro K _ ι _ Ω _ y 𝕜 _ _ z hz A ev a s hs H
  have hc : ∀ k, ∃ c : ι k, ∀ i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c⟩‖ := fun k => by
    obtain ⟨i0, -⟩ := hz.1 k
    haveI : Nonempty (ι k) := ⟨i0⟩
    exact Finite.exists_max (fun i => ‖z ⟨k, i⟩‖)
  choose c hc using hc
  have hzc : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    obtain ⟨i0, hi0⟩ := hz.1 k
    have h1 := hc k i0
    rw [h0, norm_zero] at h1
    exact hi0 (norm_le_zero_iff.1 h1)
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => coord_ne_zero hz _ (hzc k)
  obtain ⟨hr, hb, hv⟩ := H c hyc
  have hle : chartRingZ y c ≤ subalgebraOfSubring (unitBall A ev) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨k, i⟩, rfl⟩
    obtain ⟨hb', hv'⟩ := hr k i
    have e := Small.ReadFinTest.hasVal_unique hz hv' (hasVal_ratio_coord i (c k) (hyc k) (hzc k))
    refine ⟨hb', ?_⟩
    rw [e, norm_div]
    exact div_le_one_of_le₀ (hc k i) (norm_nonneg _)
  have hn : ‖ev ⟨_, hb⟩‖ ≤ 1 := norm_ev_le_one A ev _ (fun x hx => hle hx) (hs c hyc) hb
  refine ⟨ev ⟨_, hb⟩ * ∏ k, z ⟨k, c k⟩ ^ a k, ?_, ?_⟩
  · have hp : ∀ k ∈ (Finset.univ : Finset K), Small.HasVal y (a k • (Pi.single k 1 : K → ℤ)) (y ⟨k, c k⟩ ^ a k) z
        (z ⟨k, c k⟩ ^ a k) := fun k _ => hv_zpow hz (hasVal_coord k (c k)) (hyc k) (hzc k) (a k)
    have h3 := hv_mul hv (hv_prod Finset.univ hp)
    have e1 : (0 : K → ℤ) + ∑ k, a k • (Pi.single k 1 : K → ℤ) = a := by
      funext b
      simp [Finset.sum_apply, Pi.single_apply]
    have e2 : (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ a k = s := by
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      have : ∀ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) * y ⟨k, c k⟩ ^ a k = 1 := fun k => by
        rw [← zpow_add₀ (hyc k)]
        simp
      rw [Finset.prod_congr rfl fun k _ => this k, Finset.prod_const_one, mul_one]
    rw [e1, e2] at h3
    exact h3
  · have hm : Small.supMet a z = ∏ k, ‖z ⟨k, c k⟩‖ ^ a k := by
      unfold Small.supMet
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (hc k))
        (norm_le_pi_norm (fun i => z ⟨k, i⟩) (c k))]
    rw [norm_mul, norm_prod, hm]
    simp only [norm_zpow]
    exact mul_le_of_le_one_left (Finset.prod_nonneg fun k _ => by positivity) hn

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmIntegersRegularAtComponentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_integers_regular_at_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : E →+* Z.Ω), (∀ b : 𝓞 E, σ (b : E) = Z.inc (tauIn c τ b)) →
    ∀ (q : Cpt (Z.ξ₀ ≫ Y.j)) (a : 𝓞 E), σ (a : E) ∈ regAt (Z.ξ₀ ≫ Y.j) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.integers_mem_regAt | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.integers_mem_regAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.integers_mem_regAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmLieModelActionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_lie_model_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP), ∃ (M : LieModel Xo.univ.t.G (under X.y) (Fin g → X.K)) (ρ : 𝓞 E →+* Module.End X.K (Fin g → X.K)) (lam : ∀ b, PureType.lat hP (sgnRt H b) → Fin g → X.K), M.IsActOf Xo.univ.t.act.act ρ ∧ (∀ b a u, X.IsImage b a u ↔ u = M.pt (lam b a)) ∧ (∀ b (s : 𝓞 E) a, lam b (s • a) = ρ s (lam b a)) ∧ (∀ b a a', lam b (a + a') = lam b a + lam b a') ∧ (∀ b (s : X.K) a, (s : ℂ) = sgnRt H b → ρ H.rt (lam b a) = s • lam b a) ∧ ∀ b (τ : E →+* ℂ) a v, X.IsCMVec b τ a v ↔ v = M.pt (HT.eigProj ρ (X.β.comp (tauE c τ)) (lam b a)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.cm_lie_model_action | exact GlobalTheory.CompanionTheory.Relay.cm_lie_model_action | (intros; apply GlobalTheory.CompanionTheory.Relay.cm_lie_model_action <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataAbelianPartBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert

open GlobalTheory.CompanionTheory.Ar.RootHt.PullVal

section Field

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {L : Type} [Field L]

theorem centre_map (zL : Sp L ⟶ X) (e : L →+* ℂ) : centre (spMap e ≫ zL) = centre zL := by
  refine (Scheme.Hom.comp_apply (spMap e) zL _).trans ?_
  exact congrArg zL (Subsingleton.elim _ _)

theorem descend {ξ : Sp Ω ⟶ X} (hξ : IsCptGen ξ) (zL : Sp L ⟶ X) (e : L →+* ℂ) {a : Ω} {r : ℂ}
    (h : ValAt ξ (spMap e ≫ zL) a r) : ∃ t : L, ValAt ξ zL a t ∧ e t = r := by
  have hc : centre zL = centre (spMap e ≫ zL) := (centre_map zL e).symm
  have h0 := h
  obtain ⟨h', s, hs, -⟩ := h
  have h'' : genPt ξ ⤳ centre zL := hc ▸ h'
  have hv : ValAt ξ zL a (Scheme.stalkClosedPointTo zL |>.hom (X.presheaf.stalkSpecializes (specializes_of_eq hc) s)) :=
    ⟨h'', _, (genMap_stalkSpecializes ξ hc h' h'' s).trans hs, rfl⟩
  exact ⟨_, hv, ValAt.unique hξ (valAt_of_field_map ξ zL _ e rfl hv) h0⟩

theorem coords_map (ξ : Sp Ω ⟶ X) {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} {zL : Sp L ⟶ X}
    {w : (Σ k, J k) → L} (hw : CoordsAt ξ y zL w) (e : L →+* ℂ) :
    CoordsAt ξ y (spMap e ≫ zL) (fun p => e (w p)) := by
  refine ⟨fun k => (hw.1 k).imp fun c hc => hc.map e, fun k c hc => ?_⟩
  have hne : w ⟨k, c⟩ ≠ 0 := fun h0 => by simp [h0] at hc
  obtain ⟨hy, hi⟩ := hw.2 k c (isUnit_iff_ne_zero.2 hne)
  refine ⟨hy, fun i => ?_⟩
  obtain ⟨ρ, hρ, hr⟩ := hi i
  exact ⟨e ρ, valAt_of_field_map ξ zL _ e rfl hρ, by simp only [hr, map_mul]⟩

variable {ξ : Sp Ω ⟶ X} {z : Sp L ⟶ X}

theorem val_inv {a : Ω} {r : L} (h : ValAt ξ z a r) (hr : r ≠ 0) : ValAt ξ z a⁻¹ r⁻¹ := by
  obtain ⟨h1, s, rfl, rfl⟩ := h
  obtain ⟨u, rfl⟩ : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s (isUnit_iff_ne_zero.2 hr)
  refine ⟨h1, (u⁻¹ : (X.presheaf.stalk (centre z))ˣ).1, eq_inv_of_mul_eq_one_left ?_, eq_inv_of_mul_eq_one_left ?_⟩
  · rw [← map_mul, Units.inv_mul, map_one]
  · refine ((Scheme.stalkClosedPointTo z).hom.map_mul _ _).symm.trans ?_
    exact (congrArg (Scheme.stalkClosedPointTo z).hom (Units.inv_mul u)).trans (Scheme.stalkClosedPointTo z).hom.map_one

theorem val_pow (h₀ : genPt ξ ⤳ centre z) {a : Ω} {r : L} (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  induction n with
  | zero => simpa using RootHt.valAt_one h₀
  | succ n ih => simpa [pow_succ] using RootHt.valAt_mul ih h

theorem val_zpow (h₀ : genPt ξ ⤳ centre z) {a : Ω} {r : L} (h : ValAt ξ z a r) (hr : r ≠ 0) (n : ℤ) :
    ValAt ξ z (a ^ n) (r ^ n) := by
  cases n with
  | ofNat n => simpa using val_pow h₀ h n
  | negSucc n =>
    simpa [zpow_negSucc] using val_inv (val_pow h₀ h (n + 1)) (pow_ne_zero _ hr)

theorem val_prod_zpow (h₀ : genPt ξ ⤳ centre z) {K : Type} (s : Finset K) {A : K → Ω} {r : K → L} (b : K → ℤ)
    (h : ∀ k, ValAt ξ z (A k) (r k)) (hr : ∀ k, r k ≠ 0) :
    ValAt ξ z (∏ k ∈ s, A k ^ b k) (∏ k ∈ s, r k ^ b k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RootHt.valAt_one h₀
  | insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk]
    exact RootHt.valAt_mul (val_zpow h₀ (h k) (hr k) _) ih

end Field

theorem vertical_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ Or.𝔐.X) (w : (Σ k, J k) → L) (cc : (k : K) → J k) (p : ℕ), CoordsAt Or.𝔐.ξ Dc.y z w → (∀ k, w ⟨k, cc k⟩ ≠ 0) → p ∈ Dc.S → ∃ t : L, t ≠ 0 ∧ ValAt Or.𝔐.ξ z (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) * chartMono Dc.y cc (-Dc.vdeg p)) t ∧ ∀ e : L →+* ℂ, Dc.vertFactor p (fun i => e (w i)) = ‖e t‖ * ∏ k, ‖e (w ⟨k, cc k⟩)‖ ^ Dc.vdeg p k := by
  intro E _ _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or L _ _ z w cc p hw hcc hp
  classical
  obtain ⟨e₀⟩ : Nonempty (L →+* ℂ) := inferInstance
  have hT := Or.𝔐.tie
  have hξ := hT.gen
  have hwe := fun e : L →+* ℂ => coords_map Or.𝔐.ξ hw e
  have hm : ∀ e : L →+* ℂ, (fun q => e (w q)) ∈ mcPts (mCoordIdeal Dc.y) := fun e =>
    (GlobalTheory.T.complex_points_iff_centres _ _ _ K J _ hT _).2 ⟨_, Or.𝔐.all _, hwe e⟩
  have tv : ∀ (e : L →+* ℂ) (a : Ω) (r : ℂ),
      ValAt Or.𝔐.ξ (spMap e ≫ z) a r ↔ IsValueAt Dc.y a (fun q => e (w q)) r :=
    fun e a r => GlobalTheory.T.valAt_iff_value_at _ _ _ K J _ hT _ _ (Or.𝔐.all _) (hwe e) a r
  have hne := GlobalTheory.CompanionTheory.Ar.ProvConj.valAt_ne_zero (Dc.S_prime p hp).ne_zero (Dc.vertical p hp) (hm e₀) cc
    (fun k => (map_ne_zero e₀).2 (hcc k)) Dc.arith.2.1.2.1
  have hex : ∃ v, IsValueAt Dc.y (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
      chartMono Dc.y cc (-Dc.vdeg p)) (fun q => e₀ (w q)) v := by
    by_contra h
    exact hne (by rw [GroundTheory.Heights₂.Heights.LowerBoundFree.valAt, dif_neg h])
  obtain ⟨v, hv⟩ := hex
  rw [valAt_eq (hm e₀) hv] at hne
  obtain ⟨t, ht, het⟩ := descend hξ z e₀ ((tv e₀ _ _).2 hv)
  refine ⟨t, fun h0 => hne (by rw [← het, h0, map_zero]), ht, fun e => ?_⟩
  have hve := valAt_of_field_map Or.𝔐.ξ z _ e rfl ht
  have hccz : ∀ k, e (w ⟨k, cc k⟩) ≠ 0 := fun k => (map_ne_zero e).2 (hcc k)
  have hc : ∃ c : (k : K) → J k, ∀ k, (fun q => e (w q)) ⟨k, c k⟩ ≠ 0 := ⟨cc, hccz⟩
  unfold ComponentData.vertFactor
  rw [dif_pos hc]
  have hcs := hc.choose_spec
  generalize hc.choose = c at hcs ⊢
  have hcs' : ∀ k, e (w ⟨k, c k⟩) ≠ 0 := hcs
  have hy : ∀ k, Dc.y ⟨k, c k⟩ ≠ 0 := fun k => ((hwe e).2 k (c k) (isUnit_iff_ne_zero.2 (hcs' k))).1
  have hy' : ∀ k, Dc.y ⟨k, cc k⟩ ≠ 0 := fun k => ((hwe e).2 k (cc k) (isUnit_iff_ne_zero.2 (hccz k))).1
  have hr : ∀ k, ValAt Or.𝔐.ξ (spMap e ≫ z) (Dc.y ⟨k, cc k⟩ / Dc.y ⟨k, c k⟩)
      (e (w ⟨k, cc k⟩) / e (w ⟨k, c k⟩)) := fun k => by
    obtain ⟨ρ, h1, h2⟩ := ((hwe e).2 k (c k) (isUnit_iff_ne_zero.2 (hcs' k))).2 (cc k)
    have h3 : e (w ⟨k, cc k⟩) / e (w ⟨k, c k⟩) = ρ := by
      rw [div_eq_iff (hcs' k)]
      exact h2
    rw [h3]
    exact h1
  have hall := RootHt.valAt_mul hve (val_prod_zpow (Or.𝔐.all _) Finset.univ (Dc.vdeg p) hr
    (fun k => div_ne_zero (hccz k) (hcs' k)))
  have ha : MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
      chartMono Dc.y cc (-Dc.vdeg p) * ∏ k, (Dc.y ⟨k, cc k⟩ / Dc.y ⟨k, c k⟩) ^ Dc.vdeg p k =
      MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
        chartMono Dc.y c (-Dc.vdeg p) := by
    rw [_root_.mul_assoc]
    congr 1
    unfold chartMono
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.neg_apply, _root_.zpow_neg, _root_.zpow_neg, div_zpow, div_eq_mul_inv, ← _root_.mul_assoc,
      inv_mul_cancel₀ (zpow_ne_zero _ (hy' k)), _root_.one_mul]
  rw [ha] at hall
  rw [valAt_eq (hm e) ((tv e _ _).1 hall), ← norm_mul]
  have hid : e t * (∏ k, (e (w ⟨k, cc k⟩) / e (w ⟨k, c k⟩)) ^ Dc.vdeg p k) *
      zMono (fun q => e (w q)) c (Dc.vdeg p) = e t * ∏ k, e (w ⟨k, cc k⟩) ^ Dc.vdeg p k := by
    rw [_root_.mul_assoc]
    congr 1
    unfold zMono
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← mul_zpow, div_mul_cancel₀ _ (hcs' k)]
  rw [hid, norm_mul, norm_prod]
  simp only [norm_zpow]

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Vert
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpRatioUnramifiedOddPrimeStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cp_ratio_unramified_odd_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ κ w : Ω, HT.IsCp p κ → HT.IsCp p w → HT.Sandwich 𝔐 p κ → ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q → w ∈ regAt 𝔐.ξ q → ∀ t : CMType H ⊕ CMType H, 𝔐.dR t q ≤ 𝔐.HT p t q ∧ ∀ e ∈ 𝔐.HT p t q, w • e ∈ 𝔐.dR t q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.SandPt.sandwich_at_point | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.SandPt.sandwich_at_point | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.SandPt.sandwich_at_point <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFiniteKernelNonzero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CompanionTheory.Ar.Flat.finrank_kernel_pow_degree_eq_norm_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : SAB H (Sp k)), IsProper t.G.hom → ∀ (d : ℕ) (_ : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E), a ≠ 0 → (∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (_ : Module.Finite k A) (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left) ∧ ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left → Module.finrank k A ^ Module.finrank ℚ E = (Algebra.norm ℤ a).natAbs ^ (2 * d) :=
  PositivityTheory.Xgn.degree_multiplication_norm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFlatHermHodgeCptConst
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_flatHerm_hodgeCpt_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (τ : CMType H) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (A : HermLine J) (c₀ : Ω) (r : HeightOneSpectrum (𝓞 F') →₀ ℚ) (cinf : (F' →+* ℂ) → ℝ), Fl.RootLines xdeg e → A.a = ∑ i, xdeg (τ, i) → Birational y → IsConjInvariantH A → c₀ ≠ 0 → (∀ p ∈ genFibre ℤ 𝔐.ξ, (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ)) (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))).IsGenAt p (c₀ * ∏ i, e (τ, i))) → (∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ (m : ℕ) (k : ℤ), 0 < m ∧ (k : ℚ) = m * r v ∧ ∀ p : Cpt 𝔐.ξ, (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt 𝔐.ξ p) → OrderAt (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ)) (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (c₀ * ∏ i, e (τ, i)) (ψ π) m k p) → (∀ σ, 0 < cinf σ) → (∀ (σ : F' →+* ℂ) z (g h : MRing J) (dg dh : K → ℕ), PtOver y ψ σ z → IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h → ‖evC z g‖ = cinf σ * A.h z * ‖evC z h‖) → OverInt y ψ ∧ ∃ Sf : FlatHerm y ψ A, Sf.ht = ((r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) - ∑ σ : F' →+* ℂ, Real.log (cinf σ)) / (Module.finrank ℚ F' : ℝ) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 Fl xdeg e τ F' _ _ ψ A c₀ r cinf hR hA hB hC hc₀ hgen hZ hcinf hnorm
  have hN : NormalCpt 𝔐.ξ := XR.normalCpt_of_isCptGen 𝔐.tie.gen 𝔐.normal
  have hO : OverInt y ψ := overInt_of_normalCpt 𝔐.tie hN ψ
  have hD := GlobalTheory.T.hodge_cpt_flag_degree E H D l Xo c O β Y S Ω K J y 𝔐 Fl xdeg e τ hR
  rw [← hA] at hD
  refine ⟨hO, GlobalTheory.T.birational_lattice_height_formula K J Ω F' y ψ 𝔐.X 𝔐.ξ Ω _ (∏ i, e (τ, i)) c₀ A r cinf hO hB hC 𝔐.tie hN hD hc₀
    (fun p => ?_) hcinf hnorm⟩
  by_cases hp : p ∈ genFibre ℤ 𝔐.ξ
  · exact Or.inl ⟨cst_mem_regAt_of_genFibre hN ψ hp, orderAt_one_zero.2 (hgen p hp)⟩
  · obtain ⟨v, hv⟩ := exists_place_of_notMem_genFibre hN ψ hp
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F'
    obtain ⟨m, n, hm, hn, h⟩ := hZ v π hπ
    exact Or.inr ⟨v, π, m, n, hv, hπ, hm, hn, h p hv⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormalGermLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem germAt_exists_of_isLocalRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X0), ∃ d, Nonempty (GermAt t x d) :=
  GermInh.germ_local

end GlobalTheory.CompanionTheory.Ar.Conj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsMultihomogPrimeOfPlaceStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multihomog_prime_of_place : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K) (v : Place (ZMod p) K) (c : ∀ k, J k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k i, v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩)) → ∃ W : Ideal (MRing J), W.IsPrime ∧ IsMultiHomogIdeal W ∧ mCoordIdeal w ≤ W ∧ (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) ∧ Dom v w W ∧ ∀ (e : B → ℕ) (g : MRing J), IsMultiHomog g e → (g ∈ W ↔ v.valuation (aeval w g) < ∏ k, v.valuation (w ⟨k, c k⟩) ^ e k) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre.exists_centre | exact GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre.exists_centre | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoDeg.Centre.exists_centre <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLineDegreeFormulaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_line_degree_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (h : LieMetric 𝔐.M y) (x : CMType H × Fin (D.p + D.q) → HermLine J) (e : CMType H × Fin (D.p + D.q) → Ω), (∀ r, IsSmoothHerm (x r)) → Fl.RootLines (fun r => (x r).a) e → ∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ 𝔐.X), CoordsAt 𝔐.ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier) (A : FlagPair B (CMType H) D.p D.q), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ((∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inl τ)) i.val) z MB ((A.W τ).F i)) ∧ ∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inr τ)) i.val) z MB ((A.S τ).F i)) → (∀ τ (i : Fin D.p), |Ht.lineHt (x (τ, Fin.castAdd D.q i)) L w - (A.W τ).grDeg i| ≤ C) ∧ ∀ τ (i : Fin D.q), |Ht.lineHt (x (τ, Fin.natAdd D.p i)) L w + (A.S τ).grDeg i.rev| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.root_height | exact GlobalTheory.CompanionTheory.Ar.RootHt.root_height | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.root_height <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricNumberZeroFinrankStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_number_zero_finrank : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → ∀ (k : B) (c : J k), w ⟨k, c⟩ ≠ 0 → ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), ∀ (b : Fin 0 → B → ℤ) [IsLocalRing (locRing (mCoordIdeal w) W)] [Algebra (ZMod p) (locRing (mCoordIdeal w) W)], geoNum 0 W b = (Module.finrank (ZMod p) (ResidueField (locRing (mCoordIdeal w) W)) : ℤ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg.geoNum_zero_eq_finrank | exact GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg.geoNum_zero_eq_finrank | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg.geoNum_zero_eq_finrank <;> assumption)
end

