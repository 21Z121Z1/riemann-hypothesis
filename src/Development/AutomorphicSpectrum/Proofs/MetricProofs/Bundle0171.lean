import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0170
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightIntegrableOnFundamentalSet
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0168
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCSqsys
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncModelReindexedCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCoordsForComponent

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdjacentSwapHeightPolynomialRelationStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjacent_swap_height_polynomial_relation : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N d : ℕ) (S : AnSys (d + 1) (Ψ × Fin N)) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Re : Realis S P) (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → SqSys Re (τ, a) (xiCoef τ a) → ∀ lam : Ψ × Fin N → ℝ, eval lam (toWt (Re.PB II)) + eval (lam ∘ Equiv.swap (τ, a) (τ, b)) (toWt (Re.PB II)) = (tsgPoly (d + 1) kappa (linePoly (fun p => gap lam p + gap lam (τ, a) / 2 * (xiCoef τ a p : ℝ)) (xiCoef τ a) S.degPoly)).eval (gap lam (τ, a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.thmA_swap | exact GlobalTheory.CompanionTheory.Ar.PB.thmA_swap | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.thmA_swap <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightIntegrableOnFundamentalSetStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_weight_integrable_on_fundamental_set : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (H : Host E) (F : UnivFam E Ψ j j' n g Λ) (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (FF : Set (Fin n → ℂ)), F.IsArith Γ → F.IsFundSet Γ FF → 1 ≤ j' → 3 * j' + 1 ≤ j + j' → IntegrableOn (ballDens F.q) FF ∧ 0 < ∫ t in FF, ballDens F.q t ∧ IntegrableOn (fun t => (F.R t).cuspW F.σ * ballDens F.q t) FF ∧ ∫ t in FF, (F.R t).cuspW F.σ * ballDens F.q t ≤ Fintype.card Ψ * j' * (6 + Real.log (2 * Fintype.card Ψ * hostRd E) + Real.log (2 * Fintype.card Ψ * j' * hostRd E)) * ∫ t in FF, ballDens F.q t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.fund_set_mean_cuspW | exact GlobalTheory.CompanionTheory.Ar.Cusp.fund_set_mean_cuspW | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.fund_set_mean_cuspW <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverRealisationPullback
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_cover_realisation_pullback : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (CR : CovReal FA Cv), IsArithVar (mCoordIdeal y) (d + 2) → ∀ (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → Nonempty (SqSys CR.Re (τ, a) (xiCoef τ a)) := by
  first | exact @PositivityTheory.Xgp.t_c_sqsys | exact PositivityTheory.Xgp.t_c_sqsys
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointsIntegralProductFormulaStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_points_integral_product_formula : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ) (w : Fin (GroundTheory.Heights₂.Heights.LowerBoundFree.dimFl Ψ N) → Ψ × Fin N), 2 ≤ N → ptsIntegral (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (pot fun r => GroundTheory.Heights₂.Heights.LowerBoundFree.xLine Ψ N (w r)) (fun _ => 1) = ((GroundTheory.Heights₂.Heights.LowerBoundFree.flagInt Ψ N (∏ r, X (w r)) : ℚ) : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.borel_word | exact GlobalTheory.CompanionTheory.Ar.Giv.borel_word | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.borel_word <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameGenericRank
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX

theorem blkF_ne_inl (Ψ : Type) (p q : ℕ) {K₀ : Type} (k : K₀) (r : Ψ × Fin (p + q)) :
    blkF Ψ p q K₀ r ≠ some (.inl k) := by
  unfold blkF
  split_ifs <;> simp

theorem hasSncBoundary_reTie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (ht : CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀))) (e : ℕ), HasSncBoundary 𝔐 e → HasSncBoundary (reTie 𝔐 (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) ht) e := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ ht e hs
  obtain ⟨bd, hsnc, hiff⟩ := hs
  let bk : K₀ → NonPluckerBlocks (blkF (CMType H) D.p D.q K₀) :=
    fun k => ⟨Sum.inl k, fun r => blkF_ne_inl (CMType H) D.p D.q k r⟩
  let bx : ∀ k, J₀ k ≃ baseIdx (idx (p := D.p) (q := D.q) J₀ n) (blkF (CMType H) D.p D.q K₀) (bk k) :=
    fun k => Equiv.refl _
  have hval : ∀ (k : K₀) (a : J₀ k),
      xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀ ⟨bk k, bx k a⟩ = x₀ ⟨k, a⟩ := fun _ _ => rfl
  have hreg : ∀ q' : Cpt 𝔐.ξ, (∀ r : ℕ, Nat.Prime r → ¬ InFibre 𝔐.ξ r q') →
      ∀ h : genPt 𝔐.ξ ⤳ (𝟙 𝔐.X : 𝔐.X ⟶ 𝔐.X) q'.1, regAt 𝔐.ξ q' = regAt 𝔐.ξ ⟨(𝟙 𝔐.X : 𝔐.X ⟶ 𝔐.X) q'.1, h⟩ :=
    fun _ _ _ => rfl
  have hinj : ∀ q₁ q₂ : Cpt 𝔐.ξ, (∀ r : ℕ, Nat.Prime r → ¬ InFibre 𝔐.ξ r q₁) →
      (𝟙 𝔐.X : 𝔐.X ⟶ 𝔐.X) q₁.1 = (𝟙 𝔐.X : 𝔐.X ⟶ 𝔐.X) q₂.1 → q₁ = q₂ :=
    fun _ _ _ h => Subtype.ext h
  have hsnc' := GlobalTheory.CompanionTheory.Ar.SncRefine.isSncModel_refine 𝔐.X 𝔐.X Ω 𝔐.ξ 𝔐.ξ (𝟙 _) K₀ J₀ x₀ _ _
    (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) bk bx e bd 𝔐.all 𝔐.all 𝔐.tie ht (Category.comp_id _)
    hval hreg hinj hsnc
  unfold HasSncBoundary
  refine ⟨_, hsnc', fun z w hw => ?_⟩
  have hdown := GlobalTheory.CompanionTheory.Ar.CoordsDown.coordsAt_down 𝔐.X 𝔐.X Ω 𝔐.ξ 𝔐.ξ (𝟙 _) K₀ J₀ x₀ _ _
    (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) bk bx z w 𝔐.all 𝔐.all 𝔐.tie.gen (Category.comp_id _) hval hreg hw
  have hnd1 : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := fun k => (hw.1 k).imp fun _ h => h.ne_zero
  have hnd2 : ∀ k, ∃ i, w ⟨bk k, bx k i⟩ ≠ 0 := fun k => (hdown.1 k).imp fun _ h => h.ne_zero
  exact (GlobalTheory.CompanionTheory.Ar.EigBase.mem_mcPts_rename (fun p => (⟨bk p.1, bx p.1 p.2⟩ : Σ k, _)) bd w hnd1 hnd2).trans
    (hiff z _ hdown)

end GlobalTheory.CompanionTheory.Ar.PB.FMX
end
end

