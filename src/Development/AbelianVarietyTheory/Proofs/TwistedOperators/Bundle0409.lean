import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.StatementOfTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0333
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0394
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoSidedHeckePartnerInertPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0395
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0396
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeIdempotentUnipotentIntegralVanishSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightWittLeviLePowOfBoundedUnipo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalTranslateSumBoundedRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.LatticeTranslateSum

theorem sum_pow_le {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (N : ℕ) :
    (∑ i, f i) ^ N ≤ (Fintype.card ι : ℝ) ^ N * ∑ i, f i ^ N := by
  set k : ℝ := (Fintype.card ι : ℝ) with hk_def
  have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr Fintype.card_pos
  have hk : (0 : ℝ) < k := by linarith
  have hw : ∑ _i : ι, (1 / k) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hk_def]
    field_simp
  have h := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun _ => 1 / k) f
    (fun _ _ => by positivity) hw (fun i _ => hf i) N
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_pow] at h
  have hs : 0 ≤ ∑ i, f i ^ N := Finset.sum_nonneg fun i _ => pow_nonneg (hf i) _
  calc (∑ i, f i) ^ N = k ^ N * ((1 / k) ^ N * (∑ i, f i) ^ N) := by
        rw [← mul_assoc, ← mul_pow, mul_one_div_cancel hk.ne', one_pow, one_mul]
    _ ≤ k ^ N * (1 / k * ∑ i, f i ^ N) := mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ k ^ N * ∑ i, f i ^ N := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have : 1 / k ≤ 1 := by rw [div_le_one hk]; exact hk1
        nlinarith

theorem decay (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (hθ : IsInfFam θ)
    (S T : HSp D) (c : WO S T → ℂ)
    (hder : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (k : ℕ), ∃ C : ℝ, ∀ w : WO S T,
      ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ ^ k * ‖c w‖ ≤ C) (N : ℕ) :
    ∃ C : ℝ, ∀ w : WO S T, (1 + GlobalTheory.Unf.realSize θ w) ^ N * ‖c w‖ ≤ C := by
  classical
  choose n zs κ hκ using fun τ => GlobalTheory.T.exists_bound_matrix_by_symplecticFormHomAtRealPlace D S T τ
  choose Cf hCf using hder
  obtain ⟨τ₀⟩ := (GlobalTheory.DataRowsCounterexample.places_nonempty D).1
  let dv : (Σ τ : D.what₂.Tau, Fin (n τ)) → WO S T → ℝ := fun p w =>
    ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ p.1 (zs p.1 p.2) t) w)) 0‖
  let r : (Σ τ : D.what₂.Tau, Fin (n τ)) → ℝ := fun p => |κ p.1| / (2 * Real.pi)
  let f : WO S T → Option (Σ τ : D.what₂.Tau, Fin (n τ)) → ℝ := fun w o =>
    match o with
    | none => 1
    | some p => r p * dv p w
  have hf0 : ∀ w o, 0 ≤ f w o := by
    intro w o
    cases o with
    | none => simp [f]
    | some p => exact mul_nonneg (div_nonneg (abs_nonneg _) (by positivity)) (norm_nonneg _)
  have hdv : ∀ p w, r p * dv p w = |κ p.1| * |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T p.1 (zs p.1 p.2) (compAt θ p.1 w)| := by
    intro p w
    simp only [r, dv]
    rw [GlobalTheory.T.norm_deriv_character_symplecticPairing_realLine D ψ hψ θ hθ S T p.1 (zs p.1 p.2) w]
    field_simp
  have hsize : ∀ w, 1 + GlobalTheory.Unf.realSize θ w ≤ ∑ o, f w o := by
    intro w
    rw [Fintype.sum_option]
    simp only [f]
    refine add_le_add le_rfl ?_
    rw [Fintype.sum_sigma]
    unfold GlobalTheory.Unf.realSize
    refine Finset.sum_le_sum fun τ _ => ?_
    simp only [hdv]
    rw [← Finset.mul_sum]
    have hs : 0 ≤ ∑ l, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ (zs τ l) (compAt θ τ w)| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    exact (hκ τ (compAt θ τ w)).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hs)
  refine ⟨(Fintype.card (Option (Σ τ : D.what₂.Tau, Fin (n τ))) : ℝ) ^ N *
    (Cf τ₀ 0 0 + ∑ p, r p ^ N * Cf p.1 (zs p.1 p.2) N), fun w => ?_⟩
  have hrs : 0 ≤ GlobalTheory.Unf.realSize θ w := by
    unfold GlobalTheory.Unf.realSize
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h1 : (1 + GlobalTheory.Unf.realSize θ w) ^ N ≤ (∑ o, f w o) ^ N := pow_le_pow_left₀ (by positivity) (hsize w) N
  have h2 := sum_pow_le (f w) (hf0 w) N
  calc (1 + GlobalTheory.Unf.realSize θ w) ^ N * ‖c w‖ ≤ (∑ o, f w o) ^ N * ‖c w‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ (Fintype.card (Option (Σ τ : D.what₂.Tau, Fin (n τ))) : ℝ) ^ N * (∑ o, f w o ^ N) * ‖c w‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ ≤ _ := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Fintype.sum_option, add_mul, Finset.sum_mul]
        refine add_le_add ?_ (Finset.sum_le_sum fun p _ => ?_)
        · simp only [f, one_pow, one_mul]
          simpa using hCf τ₀ 0 0 w
        · simp only [f]
          rw [mul_pow, mul_assoc]
          exact mul_le_mul_of_nonneg_left (hCf p.1 (zs p.1 p.2) N w)
            (pow_nonneg (div_nonneg (abs_nonneg _) (by positivity)) _)

end GlobalTheory.LatticeTranslateSum

open GlobalTheory.LatticeTranslateSum in

theorem GlobalTheory.LatticeTranslateSum.sum_translates_bounded : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (c : WO S T → ℂ), (∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ w : WO S T, c w ≠ 0 → ∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO S T w u) = 1) → (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (k : ℕ), ∃ C : ℝ, ∀ w : WO S T, ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ ^ k * ‖c w‖ ≤ C) → ∃ C : ℝ, ∀ w : WO S T, Summable (fun γ : ratL T S => ‖c ((γ : WO S T) + w)‖) ∧ ∑' γ : ratL T S, ‖c ((γ : WO S T) + w)‖ ≤ C := by
  intro D ψ hψ θ hθ S T c ⟨U, hU, hUc⟩ hder
  obtain ⟨Q, hQ, hQc⟩ := GlobalTheory.T.exists_compact_finiteComponents_of_annihilator_openSubgroup D ψ hψ S T U hU
  have hbox : ∀ x, c x ≠ 0 → GlobalTheory.Unf.InBox Q x := fun x hx => hQc x (hUc x hx)
  obtain ⟨-, -, -, -, -, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨N, hN⟩ := GlobalTheory.Unf.MajLoc.summable_bound D θ hθ T.rank S.rank
  obtain ⟨b, hb, hbb⟩ := hN Q K hQ hK
  obtain ⟨C, hC⟩ := decay D ψ hψ θ hθ S T c hder N
  have hmaj : ∀ x : WO S T, ‖c x‖ ≤ max C 0 * GlobalTheory.Unf.maj θ Q N x := by
    intro x
    by_cases hx : c x = 0
    · rw [hx, norm_zero]
      refine mul_nonneg (le_max_right _ _) ?_
      unfold GlobalTheory.Unf.maj
      split_ifs
      · have hrs : 0 ≤ GlobalTheory.Unf.realSize θ x := by
          unfold GlobalTheory.Unf.realSize
          exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
        positivity
      · exact le_rfl
    · have hrs : 0 ≤ GlobalTheory.Unf.realSize θ x := by
        unfold GlobalTheory.Unf.realSize
        exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hp : 0 < (1 + GlobalTheory.Unf.realSize θ x) ^ N := by positivity
      unfold GlobalTheory.Unf.maj
      rw [if_pos (hbox x hx), ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
      exact (hC x).trans (le_max_left _ _)
  have hinj : Function.Injective (incA D) := GlobalTheory.MixModel.incA_injective
  let e0 : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ratL T S := fun ξ => ⟨rat ξ, ⟨ξ, rfl⟩⟩
  have he0 : Function.Bijective e0 := by
    refine ⟨fun ξ ξ' h => ?_, fun γ => ?_⟩
    · have h' : rat ξ = rat ξ' := congrArg Subtype.val h
      exact Matrix.map_injective hinj h'
    · obtain ⟨x, ξ, hξ⟩ := γ
      exact ⟨ξ, Subtype.ext hξ⟩
  refine ⟨max C 0 * ∑' ξ, b ξ, fun w => ?_⟩
  obtain ⟨g0, hg0, hg0K⟩ := hcov w
  let e : Matrix (Fin T.rank) (Fin S.rank) D.host.E ≃ ratL T S :=
    (Equiv.ofBijective e0 he0).trans (Equiv.addRight ⟨g0, hg0⟩)
  have hterm : ∀ ξ, ‖c (((e ξ : ratL T S) : WO S T) + w)‖ ≤ max C 0 * b ξ := by
    intro ξ
    have he : ((e ξ : ratL T S) : WO S T) + w = (g0 + w) + rat ξ := by
      show rat ξ + g0 + w = (g0 + w) + rat ξ
      abel
    rw [he]
    exact (hmaj _).trans (mul_le_mul_of_nonneg_left (hbb _ hg0K ξ) (le_max_right _ _))
  have hs : Summable (fun ξ => ‖c (((e ξ : ratL T S) : WO S T) + w)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hb.mul_left _)
  refine ⟨e.summable_iff.mp hs, ?_⟩
  rw [← e.tsum_eq, ← tsum_mul_left]
  exact hs.tsum_le_tsum hterm (hb.mul_left _)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTestVanishingStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_semisimple_test_vanishing : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestFin T U μf ff → (∀ v, (μf v).IsHaarMeasure) → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ → ∀ (Φ : WittFrame V) (u : SV (wittIndex V)) (γ : GF V), u ≠ 0 → IsRegSS γ.1.1 → rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) {u} → ∀ C : GA D V → ℂ, Continuous C → LeftInv (cent (rat V γ)) C → (∀ hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u), LeftInv (NA (IsoFlag.single hW)) C) → ∀ (dg : Measure (∀ v : T.S, GLoc D.sp.cm.sig V.gram v)) [dg.IsHaarMeasure] (dt : Measure (cent (projAt D.sp.cm.sig V.gram T.S (rat V γ)))) [dt.IsHaarMeasure], HasQuotInt (cent (projAt D.sp.cm.sig V.gram T.S (rat V γ))) dt dg (fun x => C (embAt D.sp.cm.sig V.gram T.S x) * ∏ v : T.S, ff v ((x v)⁻¹ * proj D.sp.cm.sig V.gram v (rat V γ) * x v)) 0 := by
  first | exact @GlobalTheory.TypesFactor.typesFactor_vanish | exact GlobalTheory.TypesFactor.typesFactor_vanish | (intros; apply GlobalTheory.TypesFactor.typesFactor_vanish <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzOneParameterGroupFormulaStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_one_parameter_group_formula : GlobalTheory.FunPr.Hypotheses₂ → ∀ (l : Type) [Fintype l] [DecidableEq l]
    (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ), Z ∈ LieAlgebra.Symplectic.sp l ℝ →
    ∀ T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l, T 0 = LinearMap.id → (∀ s t, T (s + t) = T s ∘ₗ T t) →
    (∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑(T t h₁) = GlobalTheory.RealWeil.rhoFun (NormedSpace.exp (t • Z) *ᵥ w) ⇑(T t h)) →
    (∀ (t : ℝ) (h : GlobalTheory.RealWeil.Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) →
    (∀ (h : GlobalTheory.RealWeil.Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) →
    ∃ a : ℂ, ∀ f : GlobalTheory.RealWeil.Sch l,
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (nhdsWithin 0 {0}ᶜ) (nhds (a • f + GlobalTheory.RealWeil.quad Z f)) := by
  first | exact @GlobalTheory.MetaplecticScalarDeriv.main | exact GlobalTheory.MetaplecticScalarDeriv.main | (intros; apply GlobalTheory.MetaplecticScalarDeriv.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SingleSplitLabMemSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpanPoly

open Polynomial

theorem coeff_heckePolyOf_le (n q : ℕ) (a : ℕ → ℂ) {i : ℕ} (hi : i ≤ n) :
    (Formalism.L2.Col.heckePolyOf n q a).coeff i = (-1) ^ i * (q : ℂ) ^ (i * (i - 1) / 2) * a i := by
  unfold Formalism.L2.Col.heckePolyOf
  rw [finset_sum_coeff, Finset.sum_eq_single i]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro b _ hb
    rw [coeff_C_mul_X_pow, if_neg (Ne.symm hb)]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

theorem heckePolyOf_eq_zero (n q : ℕ) (a : ℕ → ℂ) (h : ∀ k ≤ n, a k = 0) :
    Formalism.L2.Col.heckePolyOf n q a = 0 := by
  unfold Formalism.L2.Col.heckePolyOf
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [h k (by simpa [Nat.lt_succ_iff] using hk)]
  simp

theorem single_mem_span (nX nY q : ℕ) (hq : q ≠ 0) (c : ℂ) (hc : c ≠ 0) (B : Polynomial ℂ) (hB : B ≠ 0)
    (z : ℕ → ℕ → ℂ)
    (h : ∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf nX q (fun k => ∑ j ∈ Finset.range (nY + 1), z k j * a j) =
      (Formalism.L2.Col.heckePolyOf nY q a).comp (Polynomial.C c * Polynomial.X) * B)
    (j : Fin (nY + 1)) :
    Pi.single j (1 : ℂ) ∈ Submodule.span ℂ (Set.range fun k : Fin (nX + 1) => fun i : Fin (nY + 1) => z k i) := by
  by_contra hj
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hj inferInstance
  set a : ℕ → ℂ := fun i => if hi : i < nY + 1 then f (Pi.single ⟨i, hi⟩ 1) else 0 with ha
  have hfv : ∀ k : ℕ, f (fun i : Fin (nY + 1) => z k i) = ∑ i ∈ Finset.range (nY + 1), z k i * a i := by
    intro k
    rw [← Fin.sum_univ_eq_sum_range (fun i => z k i * a i)]
    conv_lhs => rw [show (fun i : Fin (nY + 1) => z k i) = ∑ i : Fin (nY + 1), z k i • Pi.single i (1 : ℂ) by
      ext m; simp [Finset.sum_apply, Pi.single_apply]]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := Fin.is_le i
    simp [ha, hi]
  have hzero : ∀ k ≤ nX, ∑ i ∈ Finset.range (nY + 1), z k i * a i = 0 := by
    intro k hk
    rw [← hfv k]
    have hm : f (fun i : Fin (nY + 1) => z k i) ∈ Submodule.map f (Submodule.span ℂ (Set.range fun k : Fin (nX + 1) => fun i : Fin (nY + 1) => z k i)) :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨⟨k, by omega⟩, rfl⟩)
    rw [hmap] at hm
    simpa using hm
  have h0 := h a
  rw [heckePolyOf_eq_zero _ _ _ hzero] at h0
  have hcomp : (Formalism.L2.Col.heckePolyOf nY q a).comp (Polynomial.C c * Polynomial.X) = 0 := by
    rcases mul_eq_zero.1 h0.symm with h1 | h1
    · exact h1
    · exact absurd h1 hB
  have hco := congrArg (fun p => Polynomial.coeff p j) hcomp
  simp only [comp_C_mul_X_coeff, coeff_zero] at hco
  rw [coeff_heckePolyOf_le _ _ _ (Nat.lt_succ_iff.1 j.isLt)] at hco
  have hqc : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have haj : a j = 0 := by
    simpa [hc, hqc] using hco
  apply hf
  have hjle := Fin.is_le j
  simpa [ha, hjle] using haj

end GlobalTheory.SpanPoly

namespace GlobalTheory.SpanPoly

theorem single_splitLab_mem_span : ∀ (nX nY q : ℕ), q ≠ 0 → ∀ (c : ℂ), c ≠ 0 → ∀ (B : Polynomial ℂ), B ≠ 0 → ∀ (z : ℕ → ℕ → ℂ), (∀ a : ℕ → ℂ, Formalism.L2.Col.heckePolyOf nX q (fun k => ∑ j ∈ Finset.range (nY + 1), z k j * a j) = (Formalism.L2.Col.heckePolyOf nY q a).comp (Polynomial.C c * Polynomial.X) * B) → ∀ j ≤ nY, Finsupp.single (splitLab nY j) (1 : ℂ) ∈ Submodule.span ℂ ((fun k => GlobalTheory.Hk3.splitC nY (z k)) '' Set.Iic nX) := by
  intro nX nY q hq c hc B hB z h j hj
  let φ : (Fin (nY + 1) → ℂ) →ₗ[ℂ] (List ℤ →₀ ℂ) :=
    ∑ i : Fin (nY + 1), (Finsupp.lsingle (splitLab nY i)).comp (LinearMap.proj i)
  have hφz : ∀ k, φ (fun i : Fin (nY + 1) => z k i) = GlobalTheory.Hk3.splitC nY (z k) := by
    intro k
    unfold GlobalTheory.Hk3.splitC
    rw [← Fin.sum_univ_eq_sum_range (fun i => Finsupp.single (splitLab nY i) (z k i))]
    simp [φ]
  have hφe : φ (Pi.single (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (nY + 1)) 1) = Finsupp.single (splitLab nY j) (1 : ℂ) := by
    simp only [φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Finsupp.lsingle_apply]
    rw [Finset.sum_eq_single (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (nY + 1))]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  rw [← hφe]
  have hm := Submodule.mem_map_of_mem (f := φ) (single_mem_span nX nY q hq c hc B hB z h ⟨j, Nat.lt_succ_of_le hj⟩)
  rw [Submodule.map_span] at hm
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  exact ⟨k, Set.mem_Iic.2 (Nat.lt_succ_iff.1 k.isLt), (hφz k).symm⟩

end GlobalTheory.SpanPoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumHeisenbergTranslatesLatticeVacuumNeZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_heisenbergTranslates_latticeVacuum_ne_zero : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ (R : Finset (WO S T)), (∀ y ∈ R, ∀ y' ∈ R, y ≠ y' → ∃ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True), IsHalf e u ∧ ψ (symplO S T u y) ≠ ψ (symplO S T u y')) → ∀ g : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) g → g ≠ 0 → ∀ c : WO S T → ℂ, (∃ z ∈ R, c z ≠ 0) → ∑ z ∈ R, c z • heisO ψ S T z g ≠ 0 := by
  first | exact @GlobalTheory.HeisJointEigen.sum_heisO_ne_zero | exact GlobalTheory.HeisJointEigen.sum_heisO_ne_zero | (intros; apply GlobalTheory.HeisJointEigen.sum_heisO_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIrreducibleOfCountableDimensionIrreducibleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_irreducible_of_countable_dimension_irreducible : ∀ (V U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (SV : Set (Module.End ℂ V))
    (SU : Set (Module.End ℂ U)), Module.rank ℂ V ≤ Cardinal.aleph0 → Nontrivial V →
    (∀ N : Submodule ℂ V, (∀ a ∈ SV, ∀ x ∈ N, a x ∈ N) → N = ⊥ ∨ N = ⊤) →
    (∀ N : Submodule ℂ U, (∀ b ∈ SU, ∀ x ∈ N, b x ∈ N) → N = ⊥ ∨ N = ⊤) →
    ∀ N : Submodule ℂ (V ⊗[ℂ] U), (∀ a ∈ SV, ∀ x ∈ N, LinearMap.rTensor U a x ∈ N) →
      (∀ b ∈ SU, ∀ x ∈ N, LinearMap.lTensor V b x ∈ N) → N = ⊥ ∨ N = ⊤ := by
  first | exact @GlobalTheory.TensIrr.tensor_irreducible | exact GlobalTheory.TensIrr.tensor_irreducible | (intros; apply GlobalTheory.TensIrr.tensor_irreducible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralModerateGrowthOfBoundedKernelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_moderate_growth_of_bounded_kernel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB → IsHaarFD W₁ ν₁ 𝓕₁ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Φ₀ Φ₀D, IsDatum Γ.M' ψ cB Φ₀D Φ₀ → Γ.M'.Conv om' Φ₀D →
    (∃ (C : ℝ) (k : ℕ), ∀ g h, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ₀D g h‖ ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht h : ℝ) ^ k) →
    ModInt θ ωB ν₁ 𝓕₁ Φ₀ := by
  first | exact @GlobalTheory.ModGrowth.modInt_of_bound | exact GlobalTheory.ModGrowth.modInt_of_bound | (intros; apply GlobalTheory.ModGrowth.modInt_of_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftAdjointPreservesHeckeEigenvectorsMatche
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Hk3

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Hk3.SysE.matched_keeps_eigen : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H), (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) → GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R t) h → ∀ P, GlobalTheory.Hk3.Good R t P → ∀ (cX c0 : List ℤ →₀ ℂ), GlobalTheory.Hk3.MatchE R t P cX c0 → ∀ (x : R.HE.H) (l : ℂ), h P c0 x = l • x → h P c0 (R.Th t (LinearMap.adjoint (R.Th t) x)) = l • R.Th t (LinearMap.adjoint (R.Th t) x) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t h hh hhn P hg cX c0 hM x l hx
  have injE : Function.Injective R.HE.e := hC.models.HE.1
  have hX01 := (GlobalTheory.DefiniteOps.definite_ops R F hC.lev hC.fam hC.models).1 t
  rcases hX01 with ⟨hX, hXo, hXn⟩
  have comm : ∀ y, R.Th t (hX P cX y) = h P c0 (R.Th t y) := by
    intro y
    apply injE
    exact (hM y (hX P cX y) (hXo P hg cX y)).trans (hh P hg c0 (R.Th t y)).symm
  have eX : LinearMap.adjoint (hX P cX) = hX P (dualC (Finsupp.mapRange star (star_zero ℂ) cX)) := hXn.2 P hg cX
  have cX' : Commute (hX P cX) (hX P (dualC (Finsupp.mapRange star (star_zero ℂ) cX))) := hXn.1 P P hg hg _ _
  have nX : Commute (hX P cX) (LinearMap.adjoint (hX P cX)) :=
    @Eq.subst (Module.End ℂ (R.HX t).H) (fun B => Commute (hX P cX) B) _ _ eX.symm cX'
  have eE : LinearMap.adjoint (h P c0) = h P (dualC (Finsupp.mapRange star (star_zero ℂ) c0)) := hhn.2 P hg c0
  have cE : Commute (h P c0) (h P (dualC (Finsupp.mapRange star (star_zero ℂ) c0))) := hhn.1 P P hg hg _ _
  have nE : Commute (h P c0) (LinearMap.adjoint (h P c0)) :=
    @Eq.subst (Module.End ℂ R.HE.H) (fun B => Commute (h P c0) B) _ _ eE.symm cE
  have up : hX P cX (LinearMap.adjoint (R.Th t) x) = l • LinearMap.adjoint (R.Th t) x :=
    GlobalTheory.T.eigenvector_adjoint_intertwiner_normal_operators (R.Th t) (fun _ : Unit => hX P cX) (fun _ : Unit => h P c0)
      (fun _ u => comm u) (fun _ => nX) (fun _ => nE) () l x hx
  have c1 := comm (LinearMap.adjoint (R.Th t) x)
  have c2 : R.Th t (hX P cX (LinearMap.adjoint (R.Th t) x)) = l • R.Th t (LinearMap.adjoint (R.Th t) x) := by
    exact (congrArg (R.Th t) up).trans ((R.Th t).map_smul l _)
  exact c1.symm.trans c2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeIdempotentUnipotentIntegralVanishSplitPlaceStatement
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeIdempotent_unipotentIntegral_vanish_splitPlace : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (v : T.S) (a : ℕ), 0 < a → a < V.rank →
    GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed (T.τ v) (GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (ResF v.1) V.rank a) →
    ∀ 𝔉 : IsoFlag V, InConjParabolic (parAt 𝔉 (T.frame v)) a →
    ∀ (μ : Measure (GLoc D.sp.cm.sig V.gram v.1)) [μ.IsHaarMeasure] (φ : GLoc D.sp.cm.sig V.gram v.1 → ℂ),
      φ ∈ CcLoc D.sp.cm.sig V.gram v.1 → ∀ f : GLoc D.sp.cm.sig V.gram v.1 → ℂ,
      (f = GlobalTheory.AutomorphicL2Unitary.conv μ ((T.frame v).idem μ (T.τ v)) φ ∨ f = GlobalTheory.AutomorphicL2Unitary.conv μ φ ((T.frame v).idem μ (T.τ v))) →
    ∀ (ν : Measure (NLoc 𝔉 v.1)) [ν.IsHaarMeasure] (x y : GLoc D.sp.cm.sig V.gram v.1),
      Integrable (fun n : NLoc 𝔉 v.1 => f (x * n * y)) ν ∧ ∫ n : NLoc 𝔉 v.1, f (x * n * y) ∂ν = 0 := by
  first | exact @GlobalTheory.LocConst.unip_integral_vanish | exact GlobalTheory.LocConst.unip_integral_vanish | (intros; apply GlobalTheory.LocConst.unip_integral_vanish <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightOrthogonalSumComparableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryQuotientHeight_orthogonalSum_comparable : ∀ (D : D7) (S A B : HSp D) (o : OrthDec S A B), ∃ (C : ℝ) (a : ℕ), ∀ h, quotHeight A h ≤ C * quotHeight S (o.emb (h, 1)) ^ a ∧ quotHeight S (o.emb (h, 1)) ≤ C * quotHeight A h ^ a := by
  first | exact @GlobalTheory.HtOrth.quotHeight_orthDec_cmp | exact GlobalTheory.HtOrth.quotHeight_orthDec_cmp | (intros; apply GlobalTheory.HtOrth.quotHeight_orthDec_cmp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightWittLeviLePowOfBoundedUnipoStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryQuotientHeight_wittLevi_le_pow_of_boundedUnipotent : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (C₀ : ℝ), ∃ (C : ℝ) (a : ℕ), ∀ n ∈ flagN d, height S n ≤ C₀ → ∀ h : GA D S₀, quotHeight S₀ h ≤ C * quotHeight S (n * d.emb0 h) ^ a := by
  first | exact @GlobalTheory.HtWittLow.quotHeight_le_of_height_le | exact GlobalTheory.HtWittLow.quotHeight_le_of_height_le | (intros; apply GlobalTheory.HtWittLow.quotHeight_le_of_height_le <;> assumption)
end

