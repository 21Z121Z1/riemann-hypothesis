import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0233
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0312
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0409
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0410
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainUnitVacuumOtherLatticesExists
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoreVacRe

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem reLat_sigOK (G : GridData L sc) (i : ℕ) (h : i ≤ D.R.m) (r : ReLat (G.V (.core i))) : r.sp.SigOK :=
  (G.isV (X := .core i) (by simpa [Node.InRange] using h) (by simp)).sigOK

theorem frameLat_selfDual (V : HSp D) : IsSelfDualC V (GlobalTheory.AdelicU.frameLat V) := by
  have e : GlobalTheory.AdelicU.frameLat V = GlobalTheory.PlaceModel.latFrame V := by
    ext y; rw [GlobalTheory.AdelicU.mem_frameLat, GlobalTheory.PlaceModel.mem_latFrame]
  rw [e]; exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem vacExists_reLat : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ (r : ReLat (G.V (.core i)))
    (r' : ReLat (G.V (.core (i + 1)))) (S S' : D.what₂.Tau → SPar) (M : DSModel r.sp S) (M' : DSModel r'.sp S'),
    ∃ f₀, IsVacO W.ψ W.θ r.sp r'.sp (cart M) (cart M') (GlobalTheory.AdelicU.frameLat r.sp : Set _)
      (GlobalTheory.AdelicU.frameLat r'.sp : Set _) f₀ := by
  intro D _ _ _ _ _ _ G W _ _ i hi r r' S S' M M'
  exact GlobalTheory.VacuumO.vacExists D W.ψ W.θ W.ψ_std W.θ_is r.sp r'.sp (cart M) (cart M')
    (reLat_sigOK G i hi.le r) (reLat_sigOK G (i + 1) hi r')
    (fun τ => GlobalTheory.ChainOnto.RealData.isCartanInv_cart M τ) (fun τ => GlobalTheory.ChainOnto.RealData.isCartanInv_cart M' τ)
    _ _ (frameLat_selfDual r.sp) (frameLat_selfDual r'.sp)

end GlobalTheory.CoreVacRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightComparableWittDecomposition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.HtWitt

theorem reduce (hT2 : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ n ∈ flagN d, ∃ γ ∈ GQ S, γ ∈ flagN d ∧ height S (γ * n) ≤ C) (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) :
    ∃ C₁ : ℝ, ∀ n ∈ flagN d, ∀ h : GA D S₀, ∃ n' ∈ flagN d, ∃ h' : GA D S₀, height S n' ≤ C₁ ∧
      height S₀ h' ≤ 2 * quotHeight S₀ h ∧ quotHeight S₀ h' = quotHeight S₀ h ∧
      quotHeight S (n' * d.emb0 h') = quotHeight S (n * d.emb0 h) := by
  obtain ⟨C₁, hC₁⟩ := hT2 D S S₀ ρ d
  refine ⟨C₁, fun n hn h => ?_⟩
  obtain ⟨δ, hδ, hδh⟩ := exists_height_le_two_mul_quotHeight S₀ h
  have hm : d.emb0 δ * n * (d.emb0 δ)⁻¹ ∈ flagN d := GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn δ
  obtain ⟨γ, hγ, hγN, hγC⟩ := hC₁ _ hm
  refine ⟨γ * (d.emb0 δ * n * (d.emb0 δ)⁻¹), mul_mem hγN hm, δ * h, hγC, hδh, quotHeight_left S₀ hδ h, ?_⟩
  have e : γ * (d.emb0 δ * n * (d.emb0 δ)⁻¹) * d.emb0 (δ * h) = (γ * d.emb0 δ) * (n * d.emb0 h) := by
    rw [map_mul]; group
  rw [e, quotHeight_left S (mul_mem hγ (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hδ))]

theorem main (hT1 : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ g : GA D S₀, height S (d.emb0 g) ≤ C * height S₀ g) (hT2 : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ n ∈ flagN d, ∃ γ ∈ GQ S, γ ∈ flagN d ∧ height S (γ * n) ≤ C) (hT3 : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (C₀ : ℝ), ∃ (C : ℝ) (a : ℕ), ∀ n ∈ flagN d, height S n ≤ C₀ → ∀ h : GA D S₀, quotHeight S₀ h ≤ C * quotHeight S (n * d.emb0 h) ^ a) : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ (C : ℝ) (a : ℕ), ∀ n ∈ flagN d, ∀ h, quotHeight S₀ h ≤ C * quotHeight S (n * d.emb0 h) ^ a ∧ quotHeight S (n * d.emb0 h) ≤ C * quotHeight S₀ h ^ a := by
  intro D S S₀ ρ d
  obtain ⟨C₁, hC₁⟩ := reduce hT2 D S S₀ ρ d
  obtain ⟨C₂, hC₂⟩ := hT1 D S S₀ ρ d
  obtain ⟨C₃, a₃, hC₃⟩ := hT3 D S S₀ ρ d C₁
  have hC2 : 0 ≤ C₂ := by
    have := hC₂ 1
    rw [map_one, height_one, height_one] at this
    linarith
  refine ⟨max C₃ (C₁ * C₂ * 2) , max a₃ 1, fun n hn h => ?_⟩
  obtain ⟨n', hn', h', hn'C, hh', hq0, hq⟩ := hC₁ n hn h
  have hC1 : 0 ≤ C₁ := (height_pos S n').le.trans hn'C
  have q1 : 1 ≤ quotHeight S (n * d.emb0 h) := one_le_quotHeight S _
  have q0 : 1 ≤ quotHeight S₀ h := one_le_quotHeight S₀ _
  have hM : 0 ≤ max C₃ (C₁ * C₂ * 2) := le_max_of_le_right (by positivity)
  constructor
  · have h3 := hC₃ n' hn' hn'C h'
    rw [hq0, hq] at h3
    exact h3.trans (mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ q1 (le_max_left _ _)) (by positivity) hM)
  · have hb : quotHeight S (n' * d.emb0 h') ≤ C₁ * C₂ * 2 * quotHeight S₀ h := by
      have h1 := height_mul_le S n' (d.emb0 h')
      have h2 := hC₂ h'
      have hp : 0 ≤ height S (d.emb0 h') := (height_pos S _).le
      calc quotHeight S (n' * d.emb0 h') ≤ height S n' * height S (d.emb0 h') := (quotHeight_le_height S _).trans h1
        _ ≤ C₁ * (C₂ * height S₀ h') := mul_le_mul hn'C h2 hp hC1
        _ ≤ C₁ * (C₂ * (2 * quotHeight S₀ h)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh' hC2) hC1
        _ = C₁ * C₂ * 2 * quotHeight S₀ h := by ring
    rw [hq] at hb
    refine hb.trans (mul_le_mul (le_max_right _ _) ?_ (by linarith) hM)
    calc quotHeight S₀ h = quotHeight S₀ h ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ q0 (le_max_right _ _)

end GlobalTheory.HtWitt

namespace GlobalTheory.HtWitt

theorem quotHeight_witt : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ (C : ℝ) (a : ℕ), ∀ n ∈ flagN d, ∀ h, quotHeight S₀ h ≤ C * quotHeight S (n * d.emb0 h) ^ a ∧ quotHeight S (n * d.emb0 h) ≤ C * quotHeight S₀ h ^ a :=
  main GlobalTheory.T.unitaryAdelicHeight_wittEmbedding_le_const_mul GlobalTheory.T.exists_rational_translate_flagUnipotent_height_le GlobalTheory.T.unitaryQuotientHeight_wittLevi_le_pow_of_boundedUnipotent

end GlobalTheory.HtWitt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelProjectionFactorisationStatement
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
theorem _root_.GlobalTheory.T.weil_model_projection_factorisation : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z) (ψ : AddChar (AF F) ℂ),
    M.IsGood ψ → ∀ (P : Type) [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    (N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F → Type) [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v),
    (∀ᶠ v in Filter.cofinite, pv v (M.vac v) = s v) →
    ∃ q : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] P ⊗[ℂ] GlobalTheory.SmallThetaModules.RTens s,
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        q (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v)) := by
  first | exact @GlobalTheory.PureLift.exists_pureLift | exact GlobalTheory.PureLift.exists_pureLift | (intros; apply GlobalTheory.PureLift.exists_pureLift <;> assumption)
end

