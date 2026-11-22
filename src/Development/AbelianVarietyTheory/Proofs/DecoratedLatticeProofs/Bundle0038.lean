import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0037
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapLawsFactorFourierJacobiSource
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumSphericalFunctionDoublingLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselStepPositionOneFiniteStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_step_position_one_finite : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (e : GL (n' ⊕ Fin (c + 1)) k →₀ ℂ) (_ : SrcComb ψ ν P ρ' Φ e) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ P σ B) (F : A) (z : GL (n' ⊕ Fin (c + 1)) k → ℂ), (∀ g ∈ e.support, IsQuotInt ν μX μG P (tInt ψ ν μ P σ B F (om μ g 1 Φ.1)) (z g)) → IsQuotInt ν μX μG 1 (tIntOne ψ ν μ P σ B F Φ.1) (comb e z) := by
  first | exact @GlobalTheory.PosOne.quotInt_one_comb | exact GlobalTheory.PosOne.quotInt_one_comb | (intros; apply GlobalTheory.PosOne.quotInt_one_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBilinearPositionMiddleVertexStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bilinear_position_middle_vertex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ) (_ : c + 1 = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ₁ μ₂ : kˣ →* ℂˣ) (_ : IsOpen (μ₁.ker : Set kˣ)) (_ : IsOpen (μ₂.ker : Set kˣ)) (m₁ : Measure (GL n₁ k)) [m₁.IsHaarMeasure] (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) [G₁.IsHaarMeasure] (m₂ : Measure (GL n₂ k)) [m₂.IsHaarMeasure] (G₂ : Measure (GL (n₂ ⊕ Fin c) k)) [G₂.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : TriPos ψ μ₁ μ₂ ρ σ T) (F : A) (ρ₁ : Representation ℂ (GL (n₁ ⊕ Fin (c + 1)) k) (SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k))) (_ : IsSrc μ₂ ρ₁), ∃ b : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ, BilPos ψ μ₁ ρ ρ₁ b ∧ (∀ Ψ (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)), IsQuotInt ν m₂ G₂ ρ (tInt ψ ν μ₂ ρ σ (T Ψ) F Φ₂.1) (b Ψ Φ₂)) ∧ ∀ Ψ (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)), IsQuotInt ν m₂ G₂ 1 (tIntOne ψ ν μ₂ ρ σ (T Ψ) F Φ₂.1) (toOne ν ρ₁ ρ (b Ψ) Φ₂) := by
  first | exact @GlobalTheory.PosOne.MidVertex.exists_bilPos_mid | exact GlobalTheory.PosOne.MidVertex.exists_bilPos_mid | (intros; apply GlobalTheory.PosOne.MidVertex.exists_bilPos_mid <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapLawsFactorFourierJacobiSourceStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMap_laws_factor_fourierJacobi_source : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ + 1 → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val ≤ ρ ∧ ¬ Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l s, r = Sum.inr l ∧ ρ < l.val ∧ q = Sum.inl s) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), Free (ρ + 1) (r, q) → (∀ i, q = Sum.inr i → ρ < i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → L Φ' = (ψ (ch (Matrix.single r q a)) : ℂ) • L Φ) → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∃ L₀ : SB (Matrix (n ⊕ Unit) n' k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow ψ ν (ρ + 1) Φ.1 → L Φ = L₀ Ψ := by
  first | exact @GlobalTheory.PartRed.flRow_factor | exact GlobalTheory.PartRed.flRow_factor | (intros; apply GlobalTheory.PartRed.flRow_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiTargetBilinearFormIntegralStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_target_bilinear_form_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : c = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (fj : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : Represents ψ ν ρ σ fj B) (_ : BilPos ψ μ (ρ + 1) σ B) (F : A) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (z : ℂ), IsQuotInt ν μX μG (ρ + 1) (tInt ψ ν μ (ρ + 1) σ B F Φ.1) z ↔ FJInt ψ ν μX μG μ ρ (fun h Ψ Φ₀ => fj Ψ (σ h F) Φ₀) Φ.1 z := by
  first | exact @GlobalTheory.PosOne.FJTarget.target_bilinear | exact GlobalTheory.PosOne.FJTarget.target_bilinear | (intros; apply GlobalTheory.PosOne.FJTarget.target_bilinear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumSphericalFunctionDoublingLengthStatement
section
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_sphericalFunction_doublingLength : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k → ∀ len : GL (Fin n) k → ℕ, (∀ e : Fin n → ℤ, Antitone e → ∀ g ∈ cell k (Fin n) ϖ e, len g = (∑ i, |e i|).toNat) → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℂ, ‖X‖ < δ → HasSum (fun c : GL (Fin n) k ⧸ KO k (Fin n) => X ^ len c.out * φ c.out) ((∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) * (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹) * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)) := by
  first | exact @GlobalTheory.DoublingLength.hasSum_doublingLength | exact GlobalTheory.DoublingLength.hasSum_doublingLength | (intros; apply GlobalTheory.DoublingLength.hasSum_doublingLength <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelReductionExtendEvaluatedIntegratedStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelReduction_extend_evaluated_integrated : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it ev' it' : Finset (m × m')), ev ⊆ ev' → it ⊆ it' → Disjoint ev' it' → GlobalTheory.FlatFactor.KerRed ν ev it β l → (∀ e ∈ ev', e ∉ ev → ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → (∀ e ∈ it', e ∉ it → ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) → GlobalTheory.FlatFactor.KerRed ν ev' it' β l := by
  first | exact @GlobalTheory.FlatFactor.KerRedStep.kerRed_extend | exact GlobalTheory.FlatFactor.KerRedStep.kerRed_extend | (intros; apply GlobalTheory.FlatFactor.KerRedStep.kerRed_extend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneDblIffSum
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

namespace GlobalTheory.PosOne

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A : Type} [AddCommGroup A] [Module ℂ A] in
private lemma isHaarMeasure_framePositiveSum_rescale (ν : Measure k)
    [ν.IsAddHaarMeasure] (b : GL (n ⊕ Fin c) k) (m : Measure (GL n k)) [m.IsHaarMeasure] :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b m).IsHaarMeasure := by
  have hpos := ENNReal.toReal_pos_iff.mp (_root_.GlobalTheory.StepData.volN_stabLat ν b)
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale
  exact Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr hpos.2.ne)
    (ENNReal.inv_ne_top.mpr hpos.1.ne')

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A : Type} [AddCommGroup A] [Module ℂ A] in
private lemma posOne_toOne_zero (ν : Measure k)
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (P : ℕ) :
    _root_.GlobalTheory.PosOne.toOne ν σ P (fun _ => 0) = fun _ => 0 := by
  have hdown : ∀ p, _root_.GlobalTheory.RootEx.exDown ν p σ (fun _ => (0 : ℂ)) = fun _ => 0 := by
    intro p
    funext v
    simp [_root_.GlobalTheory.RootEx.exDown]
  have key : ∀ m : ℕ, _root_.GlobalTheory.PosOne.toOne ν σ (m + 1) (fun _ => 0) = fun _ => 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [show m + 1 + 1 = m + 2 from rfl, _root_.GlobalTheory.PosOne.toOne_succ, hdown, ih]
  cases P with
  | zero => rfl
  | succ m => exact key m

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A : Type} [AddCommGroup A] [Module ℂ A] in
private lemma fourierJacobiAverage_app_toOne_comm {X : Type} [TopologicalSpace X]
    (ν : Measure k) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (P : ℕ)
    (B B₁ : _root_.GlobalTheory.SplitWeil.SB X →ₗ[ℂ] A →ₗ[ℂ] ℂ)
    (hB : ∀ Ψ v, B₁ Ψ v = _root_.GlobalTheory.PosOne.toOne ν σ P (B Ψ) v) (x : X → ℂ) (v : A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B₁ x v =
      _root_.GlobalTheory.PosOne.toOne ν σ P (fun w => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B x w) v := by
  by_cases hx : x ∈ _root_.GlobalTheory.SplitWeil.SB X
  · simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app, dif_pos hx]
    exact hB _ _
  · simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app, dif_neg hx, LinearMap.zero_apply]
    rw [posOne_toOne_zero]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A : Type} [AddCommGroup A] [Module ℂ A] in
private lemma fourierJacobiAverage_app_of_mem_SB {X V : Type} [TopologicalSpace X]
    [AddCommGroup V] [Module ℂ V] (B : _root_.GlobalTheory.SplitWeil.SB X →ₗ[ℂ] V) {x : X → ℂ}
    (hx : x ∈ _root_.GlobalTheory.SplitWeil.SB X) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B x = B ⟨x, hx⟩ := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app, dif_pos hx]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A : Type} [AddCommGroup A] [Module ℂ A] in
private lemma fourierJacobiAverage_app_of_not_mem_SB {X V : Type} [TopologicalSpace X]
    [AddCommGroup V] [Module ℂ V] (B : _root_.GlobalTheory.SplitWeil.SB X →ₗ[ℂ] V) {x : X → ℂ}
    (hx : x ∉ _root_.GlobalTheory.SplitWeil.SB X) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B x = 0 := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app, dif_neg hx]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A : Type} [AddCommGroup A] [Module ℂ A] in
private lemma fourierJacobiAverage_app_zero_map {X V : Type} [TopologicalSpace X]
    [AddCommGroup V] [Module ℂ V] (x : X → ℂ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (0 : _root_.GlobalTheory.SplitWeil.SB X →ₗ[ℂ] V) x = 0 := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app
  split_ifs <;> rfl

open MeasureTheory ValuativeRel Matrix in

theorem _root_.GlobalTheory.PosOne.oneDbl_iff_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ) (_ : c + 1 = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) (ν : Measure k) (_ : _root_.GlobalTheory.SplitWeil.IsUnitVol ν) (μ₁ μ₂ : kˣ →* ℂˣ) (_ : IsOpen (μ₁.ker : Set kˣ)) (_ : IsOpen (μ₂.ker : Set kˣ)) (m₁ : Measure (GL n₁ k)) [m₁.IsHaarMeasure] (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) [G₁.IsHaarMeasure] (m₂ : Measure (GL n₂ k)) [m₂.IsHaarMeasure] (G₂ : Measure (GL (n₂ ⊕ Fin c) k)) [G₂.IsHaarMeasure] (L₁ : _root_.GlobalTheory.StepData.Level (GL (n₁ ⊕ Fin (c + 1)) k)) (L₂ : _root_.GlobalTheory.StepData.Level (GL (n₂ ⊕ Fin c) k)) (_ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO L₁.J) (_ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO L₂.J) (_ : G₁ L₁.J = 1) (_ : G₂ L₂.J = 1) (b₁ : GL (n₁ ⊕ Fin (c + 1)) k) (b₂ : GL (n₂ ⊕ Fin c) k) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A) (_ : _root_.GlobalTheory.SplitWeil.IsSmoothRep σ) (T : _root_.GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k) →ₗ[ℂ] _root_.GlobalTheory.SplitWeil.SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : _root_.GlobalTheory.PosOne.TriPos ψ μ₁ μ₂ ρ σ T) (F : A) (_ : ∀ j : L₂.J, σ (j : GL (n₂ ⊕ Fin c) k) F = (L₂.lam j : ℂ) • F) (Φ₁ : _root_.GlobalTheory.SplitWeil.SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (Φ₂ : _root_.GlobalTheory.SplitWeil.SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)) (_ : ∀ j : L₁.J, _root_.GlobalTheory.SplitWeil.om μ₁ 1 (j : GL (n₁ ⊕ Fin (c + 1)) k) Φ₁.1 = (((L₁.lam j)⁻¹ : ℂˣ) : ℂ) • Φ₁.1) (_ : _root_.GlobalTheory.StepData.HasTypes μ₂ L₁ L₂ Φ₂.1) (α : GL (n₀ ⊕ Fin (c + 1 + 1)) k) (T₁ : Finset (GL (n₁ ⊕ Fin (c + 1)) k)) (T₂ : Finset (GL (n₂ ⊕ Fin c) k)) (_ : _root_.GlobalTheory.PosOne.Covers 1 L₁.J T₁ fun h => _root_.GlobalTheory.StepData.flat ψ ν μ₁ Φ₁.1 α h) (_ : ∀ γ ∈ T₁, _root_.GlobalTheory.PosOne.Covers 1 L₂.J T₂ fun h => _root_.GlobalTheory.StepData.flat ψ ν μ₂ Φ₂.1 γ h) (z : ℂ), _root_.GlobalTheory.PosOne.OneDbl ψ ν (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₁ m₁) G₁ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂) G₂ μ₁ μ₂ ρ σ T F (_root_.GlobalTheory.SplitWeil.om μ₁ α 1 Φ₁.1) Φ₂.1 z ↔ z = ∑ γ ∈ T₁, ∑ β ∈ T₂, (((m₁ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₁.J γ))).toReal⁻¹ * (m₂ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₂.J β))).toReal⁻¹ : ℝ) : ℂ) * _root_.GlobalTheory.PosOne.toOne ν σ ρ (fun v => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app T (_root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ)) (_root_.GlobalTheory.StepData.xi ψ ν μ₂ Φ₂.1 L₂.J b₂ γ β) v) (σ β F) := by
  intro k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ ψ hψ hcond ν hν μ₁ μ₂ hμ₁ hμ₂ m₁ _ G₁ _ m₂ _ G₂ _
    L₁ L₂ hL₁ hL₂ hG₁ hG₂ b₁ b₂ A _ _ σ hσ T hT F hF Φ₁ Φ₂ hΦ₁ hΦ₂ α T₁ T₂ hT₁ hT₂ z
  haveI : ν.IsAddHaarMeasure := hν.1
  have hψ1 : ψ ≠ 1 := hcond.ne_one
  have hsd : _root_.GlobalTheory.SplitWeil.IsSelfDual ψ ν :=
    _root_.GlobalTheory.SplitWeil.isSelfDual_of_isUnitVol ν hcond hν
  have hρ1 : 1 ≤ ρ := by omega
  have hρc : ρ ≤ c := by omega
  haveI : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₁ m₁).IsHaarMeasure :=
    isHaarMeasure_framePositiveSum_rescale ν b₁ m₁
  haveI : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂).IsHaarMeasure :=
    isHaarMeasure_framePositiveSum_rescale ν b₂ m₂
  obtain ⟨ρ₁, hρ₁⟩ := (_root_.GlobalTheory.PosOne.isSrc_exists_isSmoothRep k (n₁ ⊕ Fin (c + 1)) (n₂ ⊕ Fin c) μ₂ hμ₂).1
  have hρ₁s := (_root_.GlobalTheory.PosOne.isSrc_exists_isSmoothRep k (n₁ ⊕ Fin (c + 1)) (n₂ ⊕ Fin c) μ₂ hμ₂).2 ρ₁ hρ₁
  obtain ⟨b, hb, -, hbone⟩ := _root_.GlobalTheory.PosOne.MidVertex.exists_bilPos_mid k n₀ n₁ n₂ c ρ hcρ ψ hψ hψ1 ν hsd
    μ₁ μ₂ hμ₁ hμ₂ m₁ G₁ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂) G₂ A σ hσ T hT F ρ₁ hρ₁
  obtain ⟨B', hB'eq, hB'⟩ := (_root_.GlobalTheory.PosOne.toOne_isPosOne k n₁ n₀ (c + 1) ρ hρ1 (by omega)
    ψ hψ hψ1 ν _ ρ₁ hρ₁s).2 μ₁ hμ₁ b hb
  have hin : ∀ Ψ, ∃ B₁ : _root_.GlobalTheory.SplitWeil.SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ,
      (∀ Ψ' v, B₁ Ψ' v = _root_.GlobalTheory.PosOne.toOne ν σ ρ (T Ψ Ψ') v) ∧
        _root_.GlobalTheory.PosOne.BilPos ψ μ₂ 1 σ B₁ := fun Ψ =>
    (_root_.GlobalTheory.PosOne.toOne_isPosOne k n₂ n₁ c ρ hρ1 hρc ψ hψ hψ1 ν A σ hσ).2 μ₂ hμ₂ (T Ψ)
      (hT.1 Ψ)
  choose B₁ hB₁eq hB₁ using hin
  have uniq₁ := fun f => (_root_.GlobalTheory.QuotInt.quotInt_unique_exists k n₁ (c + 1) 1 le_rfl
    (by omega) ν (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₁ m₁) G₁ f).1
  have uniq₂ := fun f => (_root_.GlobalTheory.QuotInt.quotInt_unique_exists k n₂ c 1 le_rfl
    (by omega) ν (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂) G₂ f).1
  have hinteg : ∀ Ψ Φb, _root_.GlobalTheory.PosOne.tIntOne ψ ν μ₂ ρ σ (T Ψ) F Φb =
      _root_.GlobalTheory.PosOne.tInt ψ ν μ₂ 1 σ (B₁ Ψ) F Φb := by
    intro Ψ Φb
    funext h
    simp only [_root_.GlobalTheory.PosOne.tIntOne, _root_.GlobalTheory.PosOne.tInt]
    exact (fourierJacobiAverage_app_toOne_comm ν σ ρ (T Ψ) (B₁ Ψ) (hB₁eq Ψ) _ _).symm
  have hinner : ∀ h Ψ, _root_.GlobalTheory.RootEx.IsQuotInt ν (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂)
      G₂ 1 (_root_.GlobalTheory.PosOne.tInt ψ ν μ₂ 1 σ (B₁ Ψ) F (_root_.GlobalTheory.SplitWeil.om μ₂ h 1 Φ₂.1))
      (B' Ψ (ρ₁ h Φ₂)) := by
    intro h Ψ
    have := hbone Ψ (ρ₁ h Φ₂)
    rwa [hρ₁ h Φ₂, ← hB'eq Ψ, hinteg Ψ] at this
  have hF' : ∀ j : L₁.J, ρ₁ (j : GL (n₁ ⊕ Fin (c + 1)) k) Φ₂ = (L₁.lam j : ℂ) • Φ₂ := by
    intro j
    apply Subtype.ext
    rw [hρ₁, Submodule.coe_smul]
    exact hΦ₂.1 j
  have houter := _root_.GlobalTheory.PosOneCell.quotInt_posOne k n₁ n₀ (c + 1) (by omega) ψ hψ hcond ν hν
    μ₁ hμ₁ m₁ G₁ L₁ hL₁ hG₁ b₁ _ ρ₁ hρ₁s B' hB' Φ₂ hF' Φ₁ hΦ₁ α T₁ hT₁
  have hinner_sum : ∀ γ ∈ T₁, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B' (_root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ) (ρ₁ γ Φ₂) = ∑ β ∈ T₂, (((m₂ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₂.J β))).toReal⁻¹ : ℝ) : ℂ) * _root_.GlobalTheory.PosOne.toOne ν σ ρ (fun v => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app T (_root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ)) (_root_.GlobalTheory.StepData.xi ψ ν μ₂ Φ₂.1 L₂.J b₂ γ β) v) (σ β F) := by
    intro γ hγ
    by_cases hx : _root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ ∈ _root_.GlobalTheory.SplitWeil.SB _
    · rw [fourierJacobiAverage_app_of_mem_SB B' hx, fourierJacobiAverage_app_of_mem_SB T hx]
      have hi := _root_.GlobalTheory.PosOneCell.quotInt_posOne k n₂ n₁ c (by omega) ψ hψ hcond ν hν
        μ₂ hμ₂ m₂ G₂ L₂ hL₂ hG₂ b₂ A σ hσ (B₁ ⟨_, hx⟩) (hB₁ _) F hF Φ₂ hΦ₂.2 γ T₂ (hT₂ γ hγ)
      rw [uniq₂ _ _ _ (hinner γ ⟨_, hx⟩) hi]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [fourierJacobiAverage_app_toOne_comm ν σ ρ (T ⟨_, hx⟩) (B₁ ⟨_, hx⟩) (hB₁eq _)]
    · simp only [fourierJacobiAverage_app_of_not_mem_SB B' hx,
        fourierJacobiAverage_app_of_not_mem_SB T hx, fourierJacobiAverage_app_zero_map,
        LinearMap.zero_apply, posOne_toOne_zero, mul_zero,
        Finset.sum_const_zero]
  have hsum : ∀ S, _root_.GlobalTheory.RootEx.IsQuotInt ν (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₁ m₁) G₁ 1
      (_root_.GlobalTheory.PosOne.tInt ψ ν μ₁ 1 ρ₁ B' Φ₂ (_root_.GlobalTheory.SplitWeil.om μ₁ α 1 Φ₁.1)) S →
      S = ∑ γ ∈ T₁, ∑ β ∈ T₂, (((m₁ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₁.J γ))).toReal⁻¹ * (m₂ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₂.J β))).toReal⁻¹ : ℝ) : ℂ) * _root_.GlobalTheory.PosOne.toOne ν σ ρ (fun v => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app T (_root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ)) (_root_.GlobalTheory.StepData.xi ψ ν μ₂ Φ₂.1 L₂.J b₂ γ β) v) (σ β F) := by
    intro S hS
    rw [uniq₁ _ _ _ hS houter]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [hinner_sum γ hγ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    push_cast
    ring
  have hf : ∀ w : GL (n₁ ⊕ Fin (c + 1)) k → _root_.GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k) →ₗ[ℂ] ℂ,
      (∀ h Ψ, w h Ψ = B' Ψ (ρ₁ h Φ₂)) →
      (fun h => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (w h) (_root_.GlobalTheory.RootEx.opE ψ ν 1
        (_root_.GlobalTheory.SplitWeil.om μ₁ 1 h (_root_.GlobalTheory.SplitWeil.om μ₁ α 1 Φ₁.1)))) =
      _root_.GlobalTheory.PosOne.tInt ψ ν μ₁ 1 ρ₁ B' Φ₂ (_root_.GlobalTheory.SplitWeil.om μ₁ α 1 Φ₁.1) := by
    intro w hw
    funext h
    simp only [_root_.GlobalTheory.PosOne.tInt, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app]
    split_ifs
    · exact hw _ _
    · rfl
  unfold _root_.GlobalTheory.PosOne.OneDbl
  constructor
  · rintro ⟨w, hw, hz⟩
    have hwv : ∀ h Ψ, w h Ψ = B' Ψ (ρ₁ h Φ₂) := by
      intro h Ψ
      have hwh := hw h Ψ
      rw [hinteg] at hwh
      exact uniq₂ _ _ _ hwh (hinner h Ψ)
    rw [hf w hwv] at hz
    exact hsum z hz
  · intro hz
    refine ⟨fun h => B'.flip (ρ₁ h Φ₂), fun h Ψ => ?_, ?_⟩
    · rw [hinteg]
      exact hinner h Ψ
    · rw [hf _ (fun h Ψ => rfl), hz, ← hsum _ houter]
      exact houter

end GlobalTheory.PosOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatSelfAverageHeisenbergStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_self_average_heisenberg : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∃ Φ₀ : SB (n' → k), GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1 = Φ.1) ∧ ∀ Φ₀ : SB (n' → k), GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1 ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) ∧ (∀ h, opE ψ ν p (om μ 1 h (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1)) = opEFJ ψ ν p Φ₀.1 (om μ 1 h Φ.1)) ∧ ∀ (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ), app L (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1) = ∫ u, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀.1 u * L (ρ' (rowE (c + 1) p u) Φ) ∂(Measure.pi fun _ => ν) := by
  first | exact @GlobalTheory.PosOne.avg_self_and_props | exact GlobalTheory.PosOne.avg_self_and_props | (intros; apply GlobalTheory.PosOne.avg_self_and_props <;> assumption)
end

