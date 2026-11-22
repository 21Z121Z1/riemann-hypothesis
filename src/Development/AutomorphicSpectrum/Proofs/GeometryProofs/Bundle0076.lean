import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelDescentGenericFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelDescentValuationFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOverDvrExtension
import Development.WeilBound.CoreStatements.IdealCycleValues.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0070
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0036
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0035
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogHermitianSumBounded
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.CancelBound

theorem log_h_scale {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h fun p => c p.1 * z p) = (∑ k, (A.a k : ℝ) * Real.log ‖c k‖) + Real.log (A.h z) := by
  have hne : ∀ k, ‖c k‖ ^ A.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  rw [A.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => hne k) (A.pos z hz).ne',
    Real.log_prod (fun k _ => hne k)]
  congr 1
  exact Finset.sum_congr rfl fun k _ => Real.log_zpow _ _

theorem continuousOn_log_h {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι)
    (hA : IsSmoothHerm A) :
    ContinuousOn (fun z => Real.log (A.h z)) {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
  ContinuousOn.log (ContDiffOn.continuousOn hA) fun z hz => (A.pos z hz).ne'

theorem log_metrics_bounded (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Type) (A : HermLine ι)
    (B : J → HermLine ι) (T : Finset J) (hA : IsSmoothHerm A) (hB : ∀ j, IsSmoothHerm (B j))
    (hdeg : A.a = -∑ j ∈ T, (B j).a) :
    ∃ C : ℝ, ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ a, z ⟨k, a⟩ ≠ 0) →
      |Real.log (A.h z) + ∑ j ∈ T, Real.log ((B j).h z)| ≤ C := by
  classical
  let f : ((Σ k, ι k) → ℂ) → ℝ := fun z => Real.log (A.h z) + ∑ j ∈ T, Real.log ((B j).h z)
  let n : K → ((Σ k, ι k) → ℂ) → ℝ := fun k z => ∑ i, ‖z ⟨k, i⟩‖
  let S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, n k z = 1}
  have hcn : ∀ k, Continuous (n k) := fun k =>
    continuous_finset_sum _ fun i _ => (continuous_apply _).norm
  have hnpos : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ k, 0 < n k z := by
    intro z hz k
    obtain ⟨i, hi⟩ := hz k
    exact Finset.sum_pos' (fun _ _ => norm_nonneg _) ⟨i, Finset.mem_univ _, norm_pos_iff.mpr hi⟩
  have hSU : S ⊆ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    intro z hz k
    by_contra hcon
    push_neg at hcon
    have h0 : n k z = 0 := Finset.sum_eq_zero fun i _ => by simp [hcon i]
    have h1 : n k z = 1 := hz k
    rw [h0] at h1
    exact zero_ne_one h1
  have hScl : IsClosed S := by
    have hS : S = ⋂ k, {z | n k z = 1} := by
      ext z
      simp [S]
    rw [hS]
    exact isClosed_iInter fun k => isClosed_eq (hcn k) continuous_const
  have hSb : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : (Σ k, ι k) → ℂ)) (r := 1)).subset ?_
    intro z hz
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    rintro ⟨k, i⟩
    calc ‖z ⟨k, i⟩‖ ≤ n k z :=
          Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
      _ = 1 := hz k
  have hScpt : IsCompact S := Metric.isCompact_of_isClosed_isBounded hScl hSb
  have hfc : ContinuousOn f S := by
    refine ContinuousOn.mono ?_ hSU
    exact (continuousOn_log_h A hA).add
      (continuousOn_finset_sum _ fun j _ => continuousOn_log_h (B j) (hB j))
  obtain ⟨C, hC⟩ := hScpt.exists_bound_of_continuousOn hfc
  refine ⟨C, fun z hz => ?_⟩
  let c : K → ℂ := fun k => (((n k z)⁻¹ : ℝ) : ℂ)
  let w : (Σ k, ι k) → ℂ := fun p => c p.1 * z p
  have hc : ∀ k, c k ≠ 0 := fun k =>
    Complex.ofReal_ne_zero.mpr (inv_ne_zero (hnpos z hz k).ne')
  have hwS : w ∈ S := by
    intro k
    have hn := (hnpos z hz k).ne'
    have hterm : ∀ i, ‖w ⟨k, i⟩‖ = (n k z)⁻¹ * ‖z ⟨k, i⟩‖ := by
      intro i
      simp only [w, c, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (inv_pos.mpr (hnpos z hz k))]
    change ∑ i, ‖w ⟨k, i⟩‖ = 1
    simp only [hterm]
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ hn
  have hdegk : ∀ k, (A.a k : ℝ) + ∑ j ∈ T, ((B j).a k : ℝ) = 0 := by
    intro k
    have hk : A.a k = -∑ j ∈ T, (B j).a k := by
      rw [hdeg]
      simp [Finset.sum_apply]
    rw [hk]
    push_cast
    ring
  have hfw : f w = f z := by
    simp only [f, w]
    rw [log_h_scale A c z hc hz,
      Finset.sum_congr rfl fun j _ => log_h_scale (B j) c z hc hz, Finset.sum_add_distrib,
      Finset.sum_comm]
    have hz0 : (∑ k, (A.a k : ℝ) * Real.log ‖c k‖) + ∑ k, ∑ j ∈ T, ((B j).a k : ℝ) * Real.log ‖c k‖ = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [← Finset.sum_mul, ← add_mul, hdegk k, zero_mul]
    linarith
  have hb := hC w hwS
  rwa [hfw, Real.norm_eq_abs] at hb

end GlobalTheory.CompanionTheory.Ar.CancelBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelDescentGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_descent_generic_fibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d → IsIntegrallyClosedIn O Ω → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra.IsAlgebraic O O'] (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'], Function.Injective (algebraMap O' Ω') → ∀ (F : Type) [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p] (ζ : O'), IsPrimitiveRoot ζ (Fintype.card F - 1) → ∀ (n : ℕ) (Sg : Type) (r s : Sg → ℕ) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O) (φ : Equiv.Perm Sg) (Df : (∀ k, J k) → LieLatticeData Ω F n Sg r s), IsPreFamily O y p w σ φ Df → ∃ (χ : Sg → F → O') (Df' : (∀ k, J k) → LieLatticeData Ω' F n Sg r s), IsLatticeFamily O' (fun v => algebraMap Ω Ω' (y v)) p (algebraMap O O' w) χ φ Df' ∧ ∀ c, mseg y c ≠ 0 → ∀ τ, (Df' c).lie τ = spanOver (chartRing O' (mseg (fun v => algebraMap Ω Ω' (y v))) c) (bcMap Ω Ω' _ '' (Df c).lie τ) ∧ (Df' c).W τ = spanOver (chartRing O' (mseg (fun v => algebraMap Ω Ω' (y v))) c) (bcMap Ω Ω' _ '' (Df c).W τ) ∧ (Df' c).om τ = spanOver (chartRing O' (mseg (fun v => algebraMap Ω Ω' (y v))) c) (bcMap Ω Ω' _ '' (Df c).om τ) ∧ (Df' c).omHT τ = spanOver (chartRing O' (mseg (fun v => algebraMap Ω Ω' (y v))) c) (bcMap Ω Ω' _ '' (Df c).omHT τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PreFamExt.main | exact GlobalTheory.CompanionTheory.Ar.Num.PreFamExt.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PreFamExt.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelDescentValuationFibreStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_descent_valuation_fibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d → IsIntegrallyClosedIn O Ω → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra.IsAlgebraic O O'] (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'], Function.Injective (algebraMap O' Ω') → ∀ (ϖ : O) (ϖ' : O'), Irreducible ϖ → Irreducible ϖ' → ∀ (r : ℕ) (B B' : ChartBundle O (segreVec y) r (Fin r → Ω)) (w w' : Module.Basis (Fin r) Ω (Fin r → Ω)) (T : LocPair J O (Fin r)), IsFlagPair ϖ y B B' w w' T.x T.x' T.f T.g → ∃ (C₁ C₁' : ChartBundle O' (segreVec (fun v => algebraMap Ω Ω' (y v))) r (Fin r → Ω')) (v v' : Module.Basis (Fin r) Ω' (Fin r → Ω')), (∀ c, segreVec y c ≠ 0 → C₁.lat c = spanOver (chartRing O' (segreVec (fun v => algebraMap Ω Ω' (y v))) c) (bcMap Ω Ω' _ '' B.lat c) ∧ C₁'.lat c = spanOver (chartRing O' (segreVec (fun v => algebraMap Ω Ω' (y v))) c) (bcMap Ω Ω' _ '' B'.lat c)) ∧ IsFlagPair ϖ' (fun v => algebraMap Ω Ω' (y v)) C₁ C₁' v v' T.x T.x' (T.map (algebraMap O O')).f (T.map (algebraMap O O')).g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FlagPairExt.flagPair_ext | exact GlobalTheory.CompanionTheory.Ar.Num.FlagPairExt.flagPair_ext | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FlagPairExt.flagPair_ext <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOverDvrExtensionStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_over_dvr_extension : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d → IsIntegrallyClosedIn O Ω → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra.IsAlgebraic O O'] (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'], Function.Injective (algebraMap O' Ω') → pointIdeal O' (fun v => algebraMap Ω Ω' (y v)) = (pointIdeal O y).map (MvPolynomial.map (algebraMap O O')) ∧ IsModelOver (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.model_baseChange_algebraic | exact GlobalTheory.CompanionTheory.Ar.Num.model_baseChange_algebraic | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.model_baseChange_algebraic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOverRamifiedExtension
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem numbers_divCycle_baseChange_dvr : ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] (ϖ : O) (ϖ' : O') (u : O'ˣ) (e : ℕ), Irreducible ϖ → Irreducible ϖ' → 0 < e → algebraMap O O' ϖ = u * ϖ' ^ e → ∀ (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MvPolynomial (Σ k, J k) O)) (d : ℕ), IsModelOver P d → IsModelOver (P.map (MvPolynomial.map (algebraMap O O'))) d → ∀ (a : K → ℕ) (f : MvPolynomial (Σ k, J k) O), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a → f ∉ P → ∀ l : List (K → ℤ), l.length = d → cycList (divCycle (P.map (MvPolynomial.map (algebraMap O O'))) (MvPolynomial.map (algebraMap O O') f)) l = e * cycList (divCycle P f) l :=
  BaseChangeColon.isModelOver_ramified_base_change

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogComponentQuotientStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multihomog_component_quotient : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)), P.IsPrime → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → ∀ (f g u₀ v₀ : MvPolynomial (Σ k, ι k) ℤ) (bf bg a : K → ℕ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f bf → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g bg → f ∉ P → u₀ * f - v₀ * g ∈ P → weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀ ∉ P → ∃ (b : K → ℕ) (v : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ (weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀) * f - v * g ∈ P := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.multihomog_component_relation | exact GlobalTheory.CompanionTheory.Ggeo.multihomog_component_relation | (intros; apply GlobalTheory.CompanionTheory.Ggeo.multihomog_component_relation <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogCoveringForms
section
open MvPolynomial

namespace GlobalTheory.CompanionTheory.TwistLine

theorem twisted_hermitian_line : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a b : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (u j) a) → (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (v j) b) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) → ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A → ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A → ∃ A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, A'.a = (fun k => A.a k + (a k : ℤ) - (b k : ℤ)) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A' ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A' ∧ ∀ z : ((Σ k, ι k) → ℂ), A'.h z = A.h z * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) / (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) :=
  @PositivityTheory.Xgn.multihomogeneous_line_bundle

end GlobalTheory.CompanionTheory.TwistLine
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogNonvanishingRatioStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multihomog_nonvanishing_ratio : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (bf bg : K → ℕ) (z : ((Σ k, ι k) → ℂ)) (q : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → q ∈ P → eval z (MvPolynomial.map (Int.castRingHom ℂ) q) ≠ 0 → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ u ∈ P ∧ v ∈ P ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0 ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.TwistLine.forms_off_vanishing_locus | exact GlobalTheory.CompanionTheory.Ggeo.TwistLine.forms_off_vanishing_locus | (intros; apply GlobalTheory.CompanionTheory.Ggeo.TwistLine.forms_off_vanishing_locus <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogRatioInduction
section
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.TwistLine

theorem finite_pairs_common_bidegree : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : (K → ℕ) → (K → ℕ) → MvPolynomial (Σ k, ι k) ℤ → MvPolynomial (Σ k, ι k) ℤ → Prop) (bf bg : K → ℕ), (∀ (a b d : K → ℕ) (u v m : MvPolynomial (Σ k, ι k) ℤ), Q a b u v → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog m d → Q (a + d) (b + d) (u * m) (v * m)) → (∀ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), Q a b u v ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0) → ∃ (A B : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), A + bf = B + bg ∧ (∀ j, Q A B (u j) (v j)) ∧ (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) ∧ (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) :=
  @PositivityTheory.Xgn.multihomogeneous_twist_finite

end GlobalTheory.CompanionTheory.Ar.TwistLine
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalAffineChartExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.normal_affine_chart_exists : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ q : Cpt ξ, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (x : Spec (CommRingCat.of R) ⟶ X) (κ : FractionRing R ≃+* Ω), IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsOpenImmersion x ∧ q.1 ∈ Set.range x ∧ (∀ y ∈ Set.range x, genPt ξ ⤳ y) ∧ spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x = ξ := by
  first | exact @PositivityTheory.HtPt.Mk.ht_lat_chart | exact PositivityTheory.HtPt.Mk.ht_lat_chart
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalCptIffNormalScheme
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem component_whole_isIntegral_and_normal : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → (∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) → IsIntegral X ∧ (Flat.NormalCpt ξ ↔ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) :=
  PositivityTheory.HtPt.Mf.xr_normal

end GlobalTheory.CompanionTheory.Ar.XR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OneMemChartLatNm
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.Diag

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
open GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

section General

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem hasVal_unique {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} {L : Type} [Field L] {z : (Σ k, ι k) → L}
    (hz : z ∈ ptsOver L (mCoordIdeal y)) {w w' : L} (h : HasVal y a s z w) (h' : HasVal y a s z w') : w = w' := by
  obtain ⟨dg, dh, g, h₁, hg, hh, hd, hy, hz0, hzw⟩ := h
  obtain ⟨dg', dh', g', h₁', hg', hh', hd', hy', hz0', hzw'⟩ := h'
  have e : dg + dh' = dg' + dh := by
    funext k
    simp only [Pi.add_apply]
    have h1 := hd k
    have h2 := hd' k
    omega
  have hh2 : IsMultiHomog (g' * h₁) (dg + dh') := by
    rw [e]
    exact GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.homog_mul hg' hh
  have hF : g * h₁' - g' * h₁ ∈ mCoordIdeal y := by
    refine GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.mem_of_aeval_eq_zero
      (GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.homog_sub (GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.homog_mul hg hh') hh2) ?_
    rw [map_sub, map_mul, map_mul, hy, hy']
    ring
  have h0 := hz.2 _ hF
  rw [map_sub, map_mul, map_mul, hzw, hzw'] at h0
  have h2 : (w - w') * ((MvPolynomial.aeval z) h₁ * (MvPolynomial.aeval z) h₁') = 0 := by
    linear_combination h0
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 (mul_ne_zero hz0 hz0')

end General

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

end GlobalTheory.CompanionTheory.Ar.Ht.Diag
end
end

