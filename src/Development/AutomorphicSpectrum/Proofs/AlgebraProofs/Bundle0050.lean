import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaBetaAdjointExact
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaBetaIsomorphismTransport
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaKernelDerivativeVanishes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0048
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0043
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalLeadingForm
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0050
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0043
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSemiampleNef
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaBetaAdjointExactStatement
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alpha_beta_adjoint_exact : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), (∀ u y, u ⬝ᵥ beta B p y = pairH B (alpha B p u) y) ∧ beta B p ∘ₗ alpha B p = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.Isotropy.beta_comp_alpha | exact GlobalTheory.CompanionTheory.Ar.Conj.Isotropy.beta_comp_alpha | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.Isotropy.beta_comp_alpha <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaBetaIsomorphismTransportStatement
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alpha_beta_isomorphism_transport : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d), IsIso B B₂ φ ψ lam → (∀ u, alpha B p (((lin φ 1).map (· ^ p)).mulVec u) = transH φ ψ lam (alpha B₂ p u)) ∧ ∀ y, beta B p (transH φ ψ lam y) = ((lin ψ 1).transpose.map (· ^ p)).mulVec (beta B₂ p y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.alpha_beta_of_isIso | exact GlobalTheory.CompanionTheory.Ar.Conj.alpha_beta_of_isIso | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.alpha_beta_of_isIso <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaKernelDerivativeVanishesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alpha_kernel_derivative_vanishes : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : Germ.FB R d O) (u : Fin d → R) (g : Germ.PS R 2 d), alpha B p u = 0 → pow1 B p = Germ.ev (n := 2) ![ptPow R d p 0, Germ.pt R d 1] g → ∀ j, MvPowerSeries.pderiv R ((0 : Fin 1), j) (∑ i, MvPowerSeries.C (u i) * Germ.ev (n := 1) ![0, Germ.pt R d 0] (MvPowerSeries.pderiv R ((0 : Fin 2), i) g)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Kill.germKill | exact GlobalTheory.CompanionTheory.Ar.Kill.germKill | (intros; apply GlobalTheory.CompanionTheory.Ar.Kill.germKill <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BetaEquivariantFrobenius
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv

theorem beta_rhoH_eq : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O]
    [StarRing O] (B : FB R d O) (a : O) (y : (Fin d → R) × (Fin d → R)),
    beta B p (rhoH B a y) = ((rho B (star a)).transpose.map (· ^ p)).mulVec (beta B p y) := by
  intro R _ p _ _ d O _ _ B a y
  refine dotProduct_eq _ _ fun u => ?_
  have hadj := (GlobalTheory.T.formal_hermitian_action_pairing R d O B).2.2 (star a) (alpha B p u) y
  rw [star_star] at hadj
  have htw := GlobalTheory.T.alpha_equivariant_frobenius R p d O B (star a) u
  rw [dotProduct_comm, dotProduct_beta, ← hadj, ← htw, ← dotProduct_beta, dotProduct_comm _ (beta B p y),
    Matrix.dotProduct_mulVec, Matrix.transpose_map, Matrix.mulVec_transpose]

end GlobalTheory.CompanionTheory.Ar.Conj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BlowUpFibreSemilocalStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blow_up_fibre_semilocal : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpFibreSemilocal.Statement.{0} := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre.main | exact GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre.main | (intros; apply GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalLeadingFormStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_stacked_exceptional_leading_form : GroundTheory.Heights₂.Heights.DualStackedExcLeadForm.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.LeadForm.dualStackedExcLeadForm | exact GlobalTheory.CompanionTheory.Ar.Giv.LeadForm.dualStackedExcLeadForm | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.LeadForm.dualStackedExcLeadForm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedGraphBihomogeneous
section
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem graph_bihomog : GroundTheory.Heights₂.Heights.DualStackedGraphBihomog.Statement :=
  GroundTheory.Heights₂.Heights.DualStackedGraphBihomog.proof

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenFlagSlopeBoundStatement
section
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_flag_slope_bound : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (O k S T : Type) [CommRing O] [StarRing O] [Field k] [Algebra k K] [Fintype S] [Fintype T] (χ : S → (O →+* k)) (d : ℕ) (D : ConjData C p O d) (ι κ : T → S) (j q : ℕ) (μ : T → ℕ → ℝ) (W L : T → ℕ → Submodule K (Fin d → K)), 2 < p → IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → Function.Bijective (Sum.elim ι κ) → (∀ τ a, χ (κ τ) a = χ (ι τ) (star a)) → 1 ≤ j → 1 ≤ q → (∀ τ, W τ 0 = ⊥) → (∀ τ, L τ 0 = ⊥) → (∀ τ, W τ j = (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ (ι τ) a)))) → (∀ τ, L τ q = (eig (fun a => Matrix.toLin' (D.ρ a)) (fun a => algebraMap k K (χ (κ τ) a)))) → GapCond p j q μ → 0 ≤ lmuNum j q μ (fun τ i => (subDeg C D.lie (W τ i) : ℝ)) (fun τ i => (subDeg C D.lie (L τ i) : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.LmuDeg.lmuNum_nonneg_of_conjData | exact GlobalTheory.CompanionTheory.Ar.Crv.LmuDeg.lmuNum_nonneg_of_conjData | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.LmuDeg.lmuNum_nonneg_of_conjData <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalDataBaseChangeStatement
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_data_base_change : ∀ (R R₂ : Type) [CommRing R] [CommRing R₂] (f : R →+* R₂) (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R₂ d O), IsMapOf f B B₂ → (∀ a, rho B₂ a = (rho B a).map f ∧ bil (B₂.ad a) 1 1 = (bil (B.ad a) 1 1).map f) ∧ bil B₂.sy 1 1 = (bil B.sy 1 1).map f ∧ ∀ p, hw B₂ p = (hw B p).map f ∧ am B₂ p = (am B p).map f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.map_mats_baseChange | exact GlobalTheory.CompanionTheory.Ar.Conj.map_mats_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.map_mats_baseChange <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalGroupActionRingHomStatement
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_group_action_ring_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ ρ : O →+* Matrix (Fin d) (Fin d) R, ∀ a, ρ a = rho B a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.rho_hom | exact GlobalTheory.CompanionTheory.Ar.Conj.rho_hom | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.rho_hom <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FunctionFieldCurveExists
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.FF

theorem places_form_curve : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [GroundTheory.FunctionField.IsFunctionField k K], ∃ C : ACurve K, IsFFCurve k C ∧ Nonempty C.I ∧ ∀ i (x : K), IsAlgebraic k x → C.v i x ≤ 1 :=
  @PositivityTheory.HtPt.Cc.inh_ff

end GlobalTheory.CompanionTheory.Ar.FF
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GeneratedLineBundleNefOnFibres
section
set_option maxSynthPendingDepth 1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

open ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights

theorem nefOnFibres_of_generatesOn :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D : ℕ)
      (a : K → ℤ) (q : ℕ) (w : Fin q → Ω), IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
      (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w → NefOnFibres (mCoordIdeal y) a := by
  classical
  intro K _ ι _ Ω _ y D a m w _ _ hw hg W hW hPW hchar hdim
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  have : W.IsPrime := hW.1
  set ℓ := charOf W with hℓdef
  have hℓ : ℓ.Prime := SemiampleNefAlt.charOf_prime hchar
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hgen : KH.GeneratedV (ZMod ℓ) (fibreIdeal ℓ y) a :=
    (GenOnFibres.proof K ι Ω y _ m w hw hg).2 ℓ hℓ
  have hpW : ((ℓ : ℕ) : MRing ι) ∈ W := by
    have h := GroundTheory.Heights₂.Heights.Inter.C_charOf_mem W
    rwa [map_natCast] at h
  set W' := W.map (NefAmpleFibreAlt.red (ι := ι) ℓ) with hW'def
  have hker := NefAmpleFibreAlt.ker_red_le (ι := ι) ℓ hpW
  have hW'proj : IsProjVarF W' 1 := by
    refine ⟨⟨Ideal.map_isPrime_of_surjective (NefAmpleFibreAlt.red_surjective ℓ) hker,
      NefAmpleFibreAlt.isMultiHomogIdeal_map _ hW.2.1, fun k => ?_⟩, ?_⟩
    · obtain ⟨i, hi⟩ := hW.2.2 k
      refine ⟨i, fun h => hi ?_⟩
      rw [← NefAmpleFibreAlt.mem_map_red_iff ℓ hpW]
      simpa [NefAmpleFibreAlt.red] using h
    · rw [NefAmpleFibreAlt.ringKrullDim_red ℓ hpW, hdim, add_comm]
  have hle : fibreIdeal ℓ y ≤ W' := Ideal.map_mono hPW
  have hI := GeoNumTarget.isFieldIntersection_intNum (K := K) (ι := ι) ℓ
  have hnef := GeneratedNefF.proof (ZMod ℓ) K ι _ (fibreIdeal ℓ y) a hI hgen W' hW'proj hle
  have hgeo := geoNumStatement ι ℓ _ hI W 1 (fun _ => a) hW hpW hW'proj
  rw [hgeo]
  convert hnef using 2
  funext j
  fin_cases j
  rfl

end GlobalTheory.CompanionTheory.Ar.Giv
end

