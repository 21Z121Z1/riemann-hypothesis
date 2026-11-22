import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0022
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionIntegrateEntryOfTranslation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0042
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiesOnRamOfInvariant
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumHeckeSeriesSphericalEigenfunctionStatement
section
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_hecke_series_spherical_eigenfunction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ X : ℂ, (∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1) → ∀ g : GL (Fin n) k, HasSum (fun c : {c : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k])} => X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ (g * c.1.out)) ((∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) * φ g) := by
  first | exact @GlobalTheory.HeckeShift.hasSum_hecke_shift | exact GlobalTheory.HeckeShift.hasSum_hecke_shift | (intros; apply GlobalTheory.HeckeShift.hasSum_hecke_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumHeckeSeriesSphericalIntegralInverseStatement
section
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_hecke_series_spherical_integral_inverse : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ X : ℂ, (∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X‖ < 1) → HasSum (fun c : {c : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k])} => X ^ (-ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ c.1.out) (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹) := by
  first | exact @GlobalTheory.HeckeDual.hasSum_dual | exact GlobalTheory.HeckeDual.hasSum_dual | (intros; apply GlobalTheory.HeckeDual.hasSum_dual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCoordinateShearHaarLocalFieldStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_coordinate_shear_haar_localField : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (J : Type) [Fintype J] [DecidableEq J] (S : Finset J) (g : (J → k) → (J → k)), Continuous g → (∀ y y' : J → k, (∀ j, j ∉ S → y j = y' j) → g y = g y') → (∀ (y : J → k) j, j ∉ S → g y j = 0) → ∀ F : (J → k) → ℂ, ∫ y, F (y + g y) ∂(Measure.pi fun _ => ν) = ∫ y, F y ∂(Measure.pi fun _ => ν) := by
  first | exact @GlobalTheory.CoordShear.integral_shear | exact GlobalTheory.CoordShear.integral_shear | (intros; apply GlobalTheory.CoordShear.integral_shear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantIntegralSuccPositionEqExchangeStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantIntegral_succ_position_eq_exchange : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B B₁ : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ p σ B) (_ : ∀ Ψ v, B₁ Ψ v = exUp ν p σ (B Ψ) v) (F : A) (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (Rr : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ) (_ : ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsQuotInt ν μX μG p (tInt ψ ν μ p σ B F Φ.1) (Rr Φ)) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), IsQuotInt ν μX μG (p + 1) (tInt ψ ν μ (p + 1) σ B₁ F Φ.1) (exUp ν p ρ' Rr Φ) := by
  first | exact @GlobalTheory.PosOne.RrStep.rr_step | exact GlobalTheory.PosOne.RrStep.rr_step | (intros; apply GlobalTheory.PosOne.RrStep.rr_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneIndexOfOneClassOfSupportOne
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymChain

theorem exists_affPt_of_flat_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c : ℕ} (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (h : GL (n ⊕ Fin c) k) (h0 : flat ψ ν μ Φ 1 h ≠ 0) :
    ∃ x₀ e, Φ ((h⁻¹).val * affPt 1 x₀ e) ≠ 0 := by
  by_contra hne
  simp only [not_exists, not_not] at hne
  apply h0
  funext x₀
  have key : ∀ e, om μ 1 h Φ (affPt 1 x₀ e) = 0 := fun e => by
    have h1 : Φ ((h⁻¹).val * affPt 1 x₀ e * (1 : GL (n' ⊕ Fin (c + 1)) k).val) = 0 := by
      rw [Units.val_one, Matrix.mul_one]; exact hne x₀ e
    exact mul_eq_zero_of_right _ h1
  unfold flat opE
  simp only [key, zero_mul, integral_zero, Pi.zero_apply]

theorem oneIndex_of_oneClass_of_supportOne :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
      [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t]
      [DecidableEq t], S.OneClass t ν → S.SupportOne t → S.OneIndex t ν := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ hC hS j c hjc β hβ
  have := hν.1
  obtain ⟨h, rfl, h0⟩ := hβ
  obtain ⟨r, hr, u, hu, rfl⟩ := hC j c hjc h h0
  have HL : (S.T t).Laws := Chain.ofType_laws _ _ _ _ _
  have h1 := (GlobalTheory.UnfoldedEntries.flat_ne_zero_congr (ψ := S.ψ) (ν := ν) (h₂' := 1) (h₂ := u) (by omega)
    (HL.1 j (c + 1) (by omega)) rfl
    ((DoubleCoset.eq _ _ _ _).2 ⟨r⁻¹, inv_mem hr, 1, one_mem _, by group⟩)).1 h0
  obtain ⟨x₀, e, he⟩ := exists_affPt_of_flat_ne_zero _ _ _ _ _ h1
  obtain ⟨r', hr', w, hw, rfl⟩ := hS j c hjc u hu x₀ e he
  exact (DoubleCoset.eq _ _ _ _).2 ⟨(r * r')⁻¹, inv_mem (mul_mem hr hr'), w⁻¹, inv_mem hw, by group⟩

end GlobalTheory.SymChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionEqFlatMapFourierJacobiRowStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialReduction_eq_flatMapFourierJacobiRow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ), c = 2 * ρ + 1 → ∀ (lρ : Fin c), lρ.val = ρ → ∀ (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.PartRed.red ψ ν GlobalTheory.PartRed.chL (basePt c (0 : Matrix n n' k)) (GlobalTheory.PartRed.fixSet ρ ∪ GlobalTheory.PartRed.lowSet ρ) (GlobalTheory.PartRed.transSet ρ ∪ GlobalTheory.PartRed.upSet ρ) Φ x = GlobalTheory.LocFlat.flRow ψ ν (ρ + 1) Φ (Matrix.of fun r s => Sum.elim (fun r => x (Sum.inl r) (Sum.inl s)) (fun _ => x (Sum.inr lρ) (Sum.inl s)) r) := by
  first | exact @GlobalTheory.RedFlatRow.red_eq_flRow | exact GlobalTheory.RedFlatRow.red_eq_flRow | (intros; apply GlobalTheory.RedFlatRow.red_eq_flRow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionEqZeroOfFlatMapColumnZeroStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialReduction_eq_zero_of_flatMapColumn_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ), c = 2 * ρ → ∀ Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ, (∀ x, GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ x = 0) → ∀ t, GlobalTheory.FlatFactor.red ν (GlobalTheory.FlatFactor.evAll n n' c ρ) (GlobalTheory.FlatFactor.itFree n n' c ρ) (basePt c (0 : Matrix n n' k)) (fun t => (ψ (-ch t) : ℂ) * Φ t) t = 0 := by
  first | exact @GlobalTheory.FlatRed.red_eq_zero_of_flCol | exact GlobalTheory.FlatRed.red_eq_zero_of_flCol | (intros; apply GlobalTheory.FlatRed.red_eq_zero_of_flCol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionEvaluateEntryOfMulLawStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialReduction_evaluate_entry_of_mul_law : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ I → GlobalTheory.PartRed.Kills L ψ ν w β E I → GlobalTheory.PartRed.EvalLaw L ψ ν w β E I e → GlobalTheory.PartRed.Kills L ψ ν w β (insert e E) I := by
  first | exact @GlobalTheory.PartRedEval.kills_insert_of_evalLaw | exact GlobalTheory.PartRedEval.kills_insert_of_evalLaw | (intros; apply GlobalTheory.PartRedEval.kills_insert_of_evalLaw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialReductionIntegrateEntryOfTranslationStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialReduction_integrate_entry_of_translation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (R Q : Type) [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q] (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix R Q k) →ₗ[ℂ] M) (w : Matrix R Q k →ₗ[k] k) (β : Matrix R Q k) (E I : Finset (R × Q)) (e : R × Q), e ∉ E → GlobalTheory.PartRed.Kills L ψ ν w β E I → GlobalTheory.PartRed.IntLaw L ψ ν w β E I e → GlobalTheory.PartRed.Kills L ψ ν w β E (insert e I) := by
  first | exact @GlobalTheory.PartRed.IntEntry.integrate_entry | exact GlobalTheory.PartRed.IntEntry.integrate_entry | (intros; apply GlobalTheory.PartRed.IntEntry.integrate_entry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotIntPosOne
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents app_coe)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale volR)

noncomputable section
namespace GlobalTheory.PosOneCell

section Lemmas
variable {X : Type} [TopologicalSpace X] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem app_smul (l : SB X →ₗ[ℂ] V) (z : ℂ) (f : X → ℂ) : app l (z • f) = z • app l f := by
  by_cases hz : z = 0
  · subst hz
    have : app l (0 : X → ℂ) = 0 := by
      rw [show (0 : X → ℂ) = ((0 : SB X) : X → ℂ) from rfl, app_coe, map_zero]
    rw [zero_smul, zero_smul, this]
  · by_cases hf : f ∈ SB X
    · have hzf : z • f ∈ SB X := (SB X).smul_mem z hf
      simp only [app, hf, hzf, dif_pos]
      rw [← map_smul]
      rfl
    · have hzf : z • f ∉ SB X := fun h => hf (((SB X).smul_mem_iff hz).1 h)
      simp [app, hf, hzf]

theorem app_zero (l : SB X →ₗ[ℂ] V) : app l (0 : X → ℂ) = 0 := by
  rw [show (0 : X → ℂ) = ((0 : SB X) : X → ℂ) from rfl, app_coe, map_zero]

end Lemmas

theorem quotInt_posOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (_ : 1 ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : HasConductor ψ 1) (ν : Measure k) (_ : IsUnitVol ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (m : Measure (GL n k)) [m.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (L : Level (GL (n ⊕ Fin c) k)) (_ : IsCO L.J) (_ : μG L.J = 1) (b : GL (n ⊕ Fin c) k) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ 1 σ B) (F : A) (_ : ∀ j : L.J, σ (j : GL (n ⊕ Fin c) k) F = (L.lam j : ℂ) • F) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (_ : ∀ j : L.J, om μ 1 (j : GL (n ⊕ Fin c) k) Φ.1 = (((L.lam j)⁻¹ : ℂˣ) : ℂ) • Φ.1) (h' : GL (n' ⊕ Fin (c + 1)) k) (T : Finset (GL (n ⊕ Fin c) k)) (_ : Covers 1 L.J T fun h => flat ψ ν μ Φ.1 h' h), IsQuotInt ν (rescale ν b m) μG 1 (tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1)) (∑ h ∈ T, (((m (prX (Cgrp L.J h))).toReal⁻¹ : ℝ) : ℂ) * app B (xi ψ ν μ Φ.1 L.J b h' h) (σ h F)) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c hc ψ hψ hψc ν hν μ hμ m _ μG _ L hJ hJ1 b A _ _ σ hσ B hB F hF Φ hΦ h' T hT
  haveI : ν.IsAddHaarMeasure := hν.1
  have hr := volN_stabLat (n := n) (c := c) ν b
  haveI : (rescale ν b m).IsHaarMeasure := by
    unfold rescale
    exact Measure.IsHaarMeasure.smul m (ENNReal.inv_ne_zero.2 (ENNReal.toReal_pos_iff.1 hr).2.ne)
      (ENNReal.inv_ne_top.2 (ENNReal.toReal_pos_iff.1 hr).1.ne')
  have hflat : ∀ h, tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) h = app B (flat ψ ν μ Φ.1 h' h) (σ h F) := by
    intro h
    simp only [tInt, flat]
    rw [← om_mul]
    simp
  have hSB : ∀ h, flat ψ ν μ Φ.1 h' h ∈ SB (Matrix n n' k) := fun h =>
    (GlobalTheory.RootEx.opE_SB_and_linear k n n' c 1 ψ hψ ν).1 _ (om_mem_SB μ h' h Φ.2)
  have hinv : ∀ h, ∀ j ∈ L.J, tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) (h * j) = tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) h := by
    intro h j hj
    have hΦj : om μ 1 j Φ.1 = (((L.lam ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) • Φ.1 := hΦ ⟨j, hj⟩
    have hFj : σ j F = (L.lam ⟨j, hj⟩ : ℂ) • F := hF ⟨j, hj⟩
    have e : flat ψ ν μ Φ.1 h' (h * j) = (((L.lam ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) • flat ψ ν μ Φ.1 h' h := by
      unfold flat
      rw [show om μ h' (h * j) Φ.1 = om μ h' h (om μ 1 j Φ.1) by rw [← om_mul]; simp, hΦj,
        GlobalTheory.UnfoldedEntries.om_smul, GlobalTheory.UnfoldedEntries.opE_smul]
    rw [hflat, hflat, e, PosOneCell.app_smul, map_mul, Module.End.mul_apply, hFj, map_smul, map_smul,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mul]
  have hmod : ∀ (x : GL n k), ∀ u ∈ N k n c 1, ∀ h, tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) (embX c x * u * h) =
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * ((1 : ℕ) : ℝ)) : ℝ) : ℂ) *
        tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) h := by
    intro x u hu h
    have e : flat ψ ν μ Φ.1 h' (embX c x * u * h) =
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ) •
          om μ 1 x ((ψ (-simpleSum u) : ℂ) • flat ψ ν μ Φ.1 h' h) := by
      unfold flat
      rw [show om μ h' (embX c x * u * h) Φ.1 = om μ 1 (embX c x) (om μ 1 u (om μ h' h Φ.1)) by
          rw [← om_mul, ← om_mul]; simp,
        (GlobalTheory.RootEx.opE_om_embX k n n' c 1 le_rfl hc ψ ν μ _).1,
        GlobalTheory.RootEx.opE_om_target_unipotent k n n' c 1 le_rfl hc ψ ν μ _ u hu]
    let Ψ : SB (Matrix n n' k) := ⟨flat ψ ν μ Φ.1 h' h, hSB h⟩
    let Ψ₁ : SB (Matrix n n' k) := ⟨om μ 1 x (flat ψ ν μ Φ.1 h' h), om_mem_SB μ 1 x (hSB h)⟩
    have a0 : app B (flat ψ ν μ Φ.1 h' h) = B Ψ := app_coe B Ψ
    have a1 : app B (om μ 1 x (flat ψ ν μ Φ.1 h' h)) = B Ψ₁ := app_coe B Ψ₁
    rw [hflat, hflat, e, GlobalTheory.UnfoldedEntries.om_smul, smul_smul, PosOneCell.app_smul, map_mul, map_mul,
      Module.End.mul_apply, Module.End.mul_apply, a0, a1, LinearMap.smul_apply, hB.2 x Ψ Ψ₁ _ rfl,
      hB.1 Ψ u hu, smul_eq_mul]
    have key : (ψ (-simpleSum u) : ℂ) * (ψ (simpleSum u) : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
    have hp := GlobalTheory.RootEx.OpELevi.nabs_pos (Matrix.GeneralLinearGroup.det x)
    have rp : ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ) =
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * ((1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add hp]
      congr 2
      ring
    linear_combination (B Ψ (σ h F)) * (((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ)) * key
      + (B Ψ (σ h F)) * rp
  have hcov : Covers 1 L.J T (tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1)) := by
    refine ⟨hT.1, fun h hh => hT.2 h ?_⟩
    intro h0
    apply hh
    simp only at h0
    rw [hflat, h0, PosOneCell.app_zero, LinearMap.zero_apply]
  obtain ⟨-, hiff⟩ := GlobalTheory.T.isQuotInt_cells_alt k n c 1 le_rfl hc ν (rescale ν b m) μG L.J hJ _ hinv hmod T hcov
  refine (hiff _).2 (Finset.sum_congr rfl fun h _ => ?_)
  obtain ⟨-, -, -, -, hm⟩ := (GlobalTheory.UnfoldedEntries.entries_wellDefined k ψ ν hψc hν).2.2.1 n c hc L.J hJ h
  obtain ⟨-, -, -, hresc, -⟩ := hm m inferInstance
  have hvc : volCell ν (rescale ν b m) 1 L.J h = volR ν (rescale ν b m) (Cgrp L.J h) := by
    unfold volCell volR
    refine lintegral_congr fun g => ?_
    congr 1
    ext u
    simp only [Set.mem_setOf_eq, mem_Cgrp]
    refine ⟨fun H => ⟨?_, H⟩, fun H => H.2⟩
    exact (R k n c 1).mul_mem (Subgroup.mem_sup_left (MonoidHom.mem_range.2 ⟨g, rfl⟩)) (Subgroup.mem_sup_right u.2)
  have hxi : xi ψ ν μ Φ.1 L.J b h' h = (((volNat ν b (Cgrp L.J h))⁻¹ : ℝ) : ℂ) • flat ψ ν μ Φ.1 h' h := rfl
  rw [hxi, PosOneCell.app_smul, LinearMap.smul_apply, smul_eq_mul, hflat, hvc, hresc b, hJ1, ENNReal.toReal_one]
  push_cast
  ring

end GlobalTheory.PosOneCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatCompAffineMatrixStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_comp_affine_matrix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R Q : Type) [Fintype R] [DecidableEq R] [Fintype Q] (A : GL R k) (a : Matrix R Q k) (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → (fun x => Φ (A.val * x + a)) ∈ SB (Matrix R Q k) := by
  first | exact @GlobalTheory.AffineSB.mem_SB_comp_affine | exact GlobalTheory.AffineSB.mem_SB_comp_affine | (intros; apply GlobalTheory.AffineSB.mem_SB_comp_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmulGluedLatticeFirstPositionCasesStatement
section
open GlobalTheory.LatPair ValuativeRel
open scoped Pointwise
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smul_gluedLatticeFirstPosition_cases : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (P : Pair k n) (h : GL (n ⊕ Fin 1) k), (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∈ h • gluedS q 1 P.ker P.vec → (∀ x ∈ h • gluedS q 1 P.ker P.vec, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k]) → (∃ (Λ : Submodule 𝒪[k] (n → k)) (_ : Λ.IsLattice k), h • gluedS q 1 P.ker P.vec = lastKer Λ ∨ h • gluedS q 1 P.ker P.vec = (lastPair q Λ).lat) ∨ ∃ g : GL n k, h • gluedS q 1 P.ker P.vec = embX 1 g • gluedS q 1 P.ker P.vec := by
  first | exact @GlobalTheory.GluedOrbit.smul_gluedS_cases | exact GlobalTheory.GluedOrbit.smul_gluedS_cases | (intros; apply GlobalTheory.GluedOrbit.smul_gluedS_cases <;> assumption)
end

