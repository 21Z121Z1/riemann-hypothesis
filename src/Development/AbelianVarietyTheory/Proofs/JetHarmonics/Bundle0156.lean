import Mathlib
import Formalism.HermitianCurvature.Bundle0007
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0154
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0089
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0068
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0071
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0155
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AestronglyMeasurableBesselFunctionContinuousFami
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

set_option synthInstance.maxSize 2000 in

theorem besselJ_family_aestronglyMeasurable : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (α : Type) [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [SecondCountableTopology α] (μ : Measure α) [SFinite μ] (U : Set α) (γ : α → B.Mat k r) (V : Set (B.Mat k r)) (H : B.Mat k r → (Wq →L[ℂ] Wp)), IsOpen U → ContinuousOn γ U → (∀ x ∈ U, ∀ q, Bs.inSS q → B.sgs q (γ x) ∈ V) → ContinuousOn H V → AEStronglyMeasurable (fun x => B.JF Bs H (γ x)) (μ.restrict U) := by
  intro k r Wp Wq _ _ _ _ _ _ Bs α _ _ _ _ μ _ U γ V H hU hγ hV hH
  set S : Set (B.SS k r) := {p | Bs.inSS p} with hS
  have hWc := (P.weyl_subgroup_closed k r Bs.z).closed
  have hWc' := (P.weyl_subgroup_closed k r Bs.z').closed
  have hNc := (P.unipotent_radical_closed k r).closed
  have hSc : IsClosed S := by
    have e : S = (fun p : B.SS k r => (p.1.1 : B.Mat k r)) ⁻¹' (UWset k r Bs.z) ∩
        ((fun p : B.SS k r => (p.1.2 : B.Mat k r)) ⁻¹' (Nset k r) ∩
          ((fun p : B.SS k r => (p.2.1 : B.Mat k r)) ⁻¹' (UWset k r Bs.z') ∩
            (fun p : B.SS k r => (p.2.2 : B.Mat k r)) ⁻¹' (Nset k r))) := by
      ext p; rfl
    rw [e]
    exact (hWc.preimage continuous_fst.fst).inter ((hNc.preimage continuous_fst.snd).inter
      ((hWc'.preimage continuous_snd.fst).inter (hNc.preimage continuous_snd.snd)))
  have hxi : Continuous fun p : B.SS k r => B.xiTau Bs (1, 1) p :=
    (P.B7.continuous_xi Bs).comp (by fun_prop : Continuous fun p : B.SS k r => (((1 : ℝ), (1 : ℝ)), p))
  have hπ : ContinuousOn (fun p : B.SS k r => Bs.π (Matrix.of p.1.1)) S :=
    Bs.π_cont.comp (continuous_fst.fst).continuousOn (fun p hp => hp.1)
  have hinv1 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_fst.fst).continuousOn (fun p hp => hp.1.1)
  have hinv2 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_fst.snd).continuousOn (fun p hp => hp.2.1.1)
  have hinv3 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_snd.fst).continuousOn (fun p hp => hp.2.2.1.1)
  have hπ' : ContinuousOn (fun p : B.SS k r => Bs.π' (Matrix.of p.2.1 : B.Mat k r)⁻¹) S :=
    Bs.π'_cont.comp hinv3 (fun p hp => Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp.2.2.1)
  have hc4 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r)) S :=
    (continuous_snd.snd).continuousOn
  have hc5 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)) S :=
    (continuous_snd.fst).continuousOn
  have up : ∀ {β : Type} [TopologicalSpace β] {f : B.SS k r → β}, ContinuousOn f S →
      ContinuousOn (fun y : α × B.SS k r => f y.2) (U ×ˢ S) :=
    fun hf => hf.comp continuous_snd.continuousOn (fun y hy => hy.2)
  have hγ' : ContinuousOn (fun y : α × B.SS k r => γ y.1) (U ×ˢ S) :=
    hγ.comp continuous_fst.continuousOn (fun y hy => hy.1)
  have hsgs : ContinuousOn (fun y : α × B.SS k r => B.sgs y.2 (γ y.1)) (U ×ˢ S) :=
    (((((up hinv1).mul (up hinv2)).mul hγ').mul (up hc4)).mul (up hc5))
  have hFs : ContinuousOn (fun y : α × B.SS k r => H (B.sgs y.2 (γ y.1))) (U ×ˢ S) :=
    hH.comp hsgs (fun y hy => hV y.1 hy.1 y.2 hy.2)
  have hcont : ContinuousOn (fun y : α × B.SS k r => D.orbIntegrand Bs (γ y.1) H y.2) (U ×ˢ S) := by
    unfold D.orbIntegrand B.rho
    exact (up hxi.continuousOn).smul ((up hπ).clm_comp (hFs.clm_comp (up hπ')))
  have hW : SigmaFinite Bs.μW := P.Dx2.MN.sigma_of_haar Bs.haarW
  have hW' : SigmaFinite Bs.μW' := P.Dx2.MN.sigma_of_haar Bs.haarW'
  have hN : SigmaFinite Bs.μN := P.Dx2.MN.sigma_of_haar Bs.haarN
  have hsf : SFinite Bs.μSS := by unfold B.RealPlaceData.μSS; infer_instance
  have h1 := hcont.aestronglyMeasurable (μ := μ.prod Bs.μSS) (hU.measurableSet.prod hSc.measurableSet)
  have hae : ∀ᵐ p ∂Bs.μSS, p ∈ S := P.Dx2.OrbJ.ae_inSS Bs
  rw [← Measure.prod_restrict, Measure.restrict_eq_self_of_ae_mem hae] at h1
  have h2 := h1.integral_prod_right'
  have e : (fun x => B.JF Bs H (γ x)) = fun x => ∫ p, D.orbIntegrand Bs (γ x) H p ∂Bs.μSS := by
    funext x
    rw [← P.bessel_function_trivial_index k r Wp Wq Bs H (γ x)]
    rfl
  rw [e]
  exact h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingUniformConstantStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_setting_uniform_constant : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∃ c : ℝ, 0 < c ∧ ∀ (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ F s, IsCoef R l l' F s → B.normSq D F = ENNReal.ofReal (c * ‖s‖ ^ 2 / dd) := by
  first | exact @GlobalTheory.BesselNormSq.normSq_coef | exact GlobalTheory.BesselNormSq.normSq_coef | (intros; apply GlobalTheory.BesselNormSq.normSq_coef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenSumLinearCombinationStatement
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliEigenSum_linearCombination : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (ι : Type) (S : Finset ι) (co : ι → ℂ) (Fs : ι → B.Mat k r → (Wq →L[ℂ] Wp)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ x ∈ S, ∃ (d' : ℕ) (A' : ℝ), d' ≤ d ∧ A ≤ A' ∧ (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d' : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A') m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (Fs x) g = ∑ i, Fi i g)) → (∀ g ∈ B.GV k r, F g = ∑ x ∈ S, co x • Fs x g) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g) := by
  first | exact @GlobalTheory.capelli_eigenSum_linearCombination | exact GlobalTheory.capelli_eigenSum_linearCombination | (intros; apply GlobalTheory.capelli_eigenSum_linearCombination <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliProductLevelZeroPairingNormLeStatement
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliProduct_levelZeroPairing_norm_le : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (A : ℝ), B.AB k r ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ (X Z : B.Mat k r → (Wq →L[ℂ] Wp)) (c c' : ℝ), B.CkOn ⊤ (B.GV k r) X → B.CCle A (5 + w.length * (2 * r + k + 1)) X c → B.CCle A 5 Z c' → ‖B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z‖ ≤ C * c * c' := by
  first | exact @GlobalTheory.beta_capelliFold_norm_le | exact GlobalTheory.beta_capelliFold_norm_le | (intros; apply GlobalTheory.beta_capelliFold_norm_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliProductLevelZeroPairingSesquilinearStatement
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliProduct_levelZeroPairing_sesquilinear : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (A : ℝ), B.AB k r ≤ A → ∀ (a : ℂ) (X X' Z Z' : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) X → B.CkOn ⊤ (B.GV k r) X' → B.InCC A (5 + w.length * (2 * r + k + 1)) X → B.InCC A (5 + w.length * (2 * r + k + 1)) X' → B.InCC A 5 Z → B.InCC A 5 Z' → B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X + a • X') w) Z = B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z + a * B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X') w) Z ∧ B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) (Z + a • Z') = B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z + (starRingEnd ℂ) a * B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z' := by
  first | exact @GlobalTheory.beta_foldCapelli_sesquilinear | exact GlobalTheory.beta_foldCapelli_sesquilinear | (intros; apply GlobalTheory.beta_foldCapelli_sesquilinear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ContinuousOfIsPolyDeg
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF Filter Topology

namespace GlobalTheory.HatNF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open MeasureTheory Filter Topology in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma norm_opApply_le_of_polynomial_coeffs_lemma {k r : ℕ} {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ : ℕ) (A : ℝ)
    (Θ : List (_root_.Formalism.FourierDecayAlt.B.DTerm k r Wp Wq))
    (hΘ : ∀ T ∈ Θ, T.word.length ≤ o ∧ ∃ Q : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q ∧
      ∀ g, T.coef g = Q g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (B : ℝ), _root_.Formalism.FourierDecayAlt.B.CCle A o G B →
      ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, ‖_root_.Formalism.FourierDecayAlt.B.opApply Θ G g‖ ≤ C * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) := by
  induction Θ with
  | nil => exact ⟨0, le_rfl, fun G B hG g _ => by
      simp [_root_.Formalism.FourierDecayAlt.B.opApply, _root_.Formalism.FourierDecayAlt.P.B4.gN_rpow_nonneg, mul_nonneg (mul_nonneg le_rfl (_root_.Formalism.FourierDecayAlt.P.B4.cc_nonneg hG))]⟩
  | cons T Θ ih =>
    obtain ⟨C₁, hC₁0, hC₁⟩ := ih (fun S hS => hΘ S (List.mem_cons_of_mem _ hS))
    obtain ⟨hlen, Q, hQ, hcoef⟩ := hΘ T List.mem_cons_self
    obtain ⟨CQ, hCQ0, hCQ⟩ := _root_.PI.UnitaryCorollaryDerivatives.pb_nonneg (_root_.PI.UnitaryCorollaryDerivatives.pb_poly hQ) 0
    have hunit : ∀ X ∈ List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word, _root_.Formalism.FourierDecayAlt.B.unitLie k r X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
      exact _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm_unit (T.word_lie Y hY)
    set ν : ℝ := ‖((List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nz T.word).prod : ℂ)‖ with hν
    refine ⟨CQ * ν + C₁, by positivity, fun G B hG g hg => ?_⟩
    have hgpos : 0 < _root_.Formalism.FourierDecayAlt.B.gN g := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_pos hg
    have hB : 0 ≤ B := _root_.Formalism.FourierDecayAlt.P.B4.cc_nonneg hG
    have hRw : _root_.Formalism.FourierDecayAlt.B.CCle A 0 (_root_.Formalism.FourierDecayAlt.B.Rw (List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word) G) B :=
      _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_Rw hunit (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (by simpa using hlen) hG)
    have hRw' := hRw.2 [] [] (by simp) (by simp) (by simp) g hg
    simp only [_root_.Formalism.FourierDecayAlt.B.dLR, List.foldr_nil, _root_.Formalism.FourierDecayAlt.B.Rw] at hRw'
    have hword : ‖_root_.Formalism.FourierDecayAlt.B.Rw (List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word) G g‖ ≤ B * _root_.Formalism.FourierDecayAlt.B.gN g ^ (-A) := by
      rw [Real.rpow_neg hgpos.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hgpos _),
        mul_comm]
      simpa [_root_.Formalism.FourierDecayAlt.B.Rw] using hRw'
    have hQg : ‖Q g‖ ≤ CQ * _root_.Formalism.FourierDecayAlt.B.gN g ^ (κ : ℝ) := by
      have := hCQ [] (by simp) (by simp) g hg
      simpa [_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw] using this
    have hterm : ‖(T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g)‖ ≤ CQ * ν * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) := by
      rw [hcoef, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, norm_smul,
        congrFun (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_scale T.word G) g, norm_smul, ← hν, sub_eq_add_neg,
        Real.rpow_add hgpos]
      calc ‖Q g‖ * (ν * ‖_root_.Formalism.FourierDecayAlt.B.Rw (List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word) G g‖)
          ≤ (CQ * _root_.Formalism.FourierDecayAlt.B.gN g ^ (κ : ℝ)) * (ν * (B * _root_.Formalism.FourierDecayAlt.B.gN g ^ (-A))) := by
            gcongr
        _ = CQ * ν * B * (_root_.Formalism.FourierDecayAlt.B.gN g ^ (κ : ℝ) * _root_.Formalism.FourierDecayAlt.B.gN g ^ (-A)) := by ring
    have hrest := hC₁ G B hG g hg
    have hsplit : _root_.Formalism.FourierDecayAlt.B.opApply (T :: Θ) G g = (T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g) + _root_.Formalism.FourierDecayAlt.B.opApply Θ G g := by
      simp [_root_.Formalism.FourierDecayAlt.B.opApply]
    rw [hsplit]
    calc ‖(T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g) + _root_.Formalism.FourierDecayAlt.B.opApply Θ G g‖
        ≤ ‖(T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g)‖ + ‖_root_.Formalism.FourierDecayAlt.B.opApply Θ G g‖ := norm_add_le _ _
      _ ≤ CQ * ν * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) + C₁ * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) :=
          add_le_add hterm hrest
      _ = (CQ * ν + C₁) * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) := by ring

open MeasureTheory Filter Topology in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma continuousOn_opApply_of_polynomial_coeffs_lemma_2 {k r : ℕ} {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ : ℕ)
    (Θ : List (_root_.Formalism.FourierDecayAlt.B.DTerm k r Wp Wq))
    (hΘ : ∀ T ∈ Θ, T.word.length ≤ o ∧ ∃ Q : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q ∧
      ∀ g, T.coef g = Q g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
    {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) G) :
    ContinuousOn (_root_.Formalism.FourierDecayAlt.B.opApply Θ G) (_root_.Formalism.FourierDecayAlt.B.GV k r) := by
  apply _root_.Formalism.FourierDecayAlt.P.PBE.opApply_continuousOn
  intro T hT
  obtain ⟨-, Q, hQ, hcoef⟩ := hΘ T hT
  have hQc : Continuous Q := (_root_.Formalism.FourierDecayAlt.P.poly_adm (n := 0) hQ).1.continuous
  have hRw : ContinuousOn (_root_.Formalism.FourierDecayAlt.B.Rw T.word G) (_root_.Formalism.FourierDecayAlt.B.GV k r) :=
    _root_.Formalism.FourierDecayAlt.P.PBE.ckOn_continuousOn' subset_rfl (_root_.Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_Rw_top hG T.word_lie)
  have hfun : (fun g => (T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g)) =
      fun g => Q g • _root_.Formalism.FourierDecayAlt.B.Rw T.word G g := by
    funext g
    rw [hcoef]
    simp
  rw [hfun]
  exact hQc.continuousOn.smul hRw

open MeasureTheory Filter Topology in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem _root_.GlobalTheory.HatNF.vecV_cut_polyOp : ∃ c₃ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (o κ : ℕ) (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp P.k P.r Wp Wq) (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp o κ Θ → _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) F → _root_.Formalism.FourierDecayAlt.B.InCC A o F → c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A - 1 - κ → ∀ cut : ℕ → _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → ℂ, (∀ n g, cut n g = ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) → ∀ γ : _root_.Formalism.FourierDecayAlt.C.LPt, Filter.Tendsto (fun n => p.V (_root_.Formalism.FourierDecayAlt.B.opApply Θ (fun g => cut n g • F g)) γ) Filter.atTop (nhds (p.V (_root_.Formalism.FourierDecayAlt.B.opApply Θ F) γ)) := by
  obtain ⟨c₃, hc₃⟩ := _root_.Formalism.FourierDecayAlt.P.PBE.vecV_tendsto
  refine ⟨c₃, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p o κ Θ F A hΘ hF hCC hA cut hcut γ
  unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hΘ
  have hΘ' : ∀ T ∈ Θ, T.word.length ≤ o ∧ ∃ Q : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → ℂ, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q ∧
      ∀ g, T.coef g = Q g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := by
    intro T hT
    obtain ⟨hl, Q, hQ, hc, -⟩ := hΘ T hT
    exact ⟨hl, Q, hQ, hc⟩
  have hcutφ : ∀ n : ℕ, cut n = fun g => _root_.Formalism.FourierDecayAlt.P.JCx2.pdPhi (((n : ℝ) + 1)⁻¹ • g) := by
    intro n
    funext g
    rw [hcut]
    rfl
  have hψ : ∀ (n : ℕ) g, cut n g = 1 - _root_.Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := by
    intro n g
    have h : _root_.Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g = 1 - _root_.Formalism.FourierDecayAlt.P.JCx2.pdPhi (((n : ℝ) + 1)⁻¹ • g) := rfl
    rw [hcutφ, h]
    ring
  unfold _root_.Formalism.FourierDecayAlt.B.InCC at hCC
  obtain ⟨b, hb⟩ := hCC
  have hb0 : 0 ≤ b := _root_.Formalism.FourierDecayAlt.P.B4.cc_nonneg hb
  have hb1 : _root_.Formalism.FourierDecayAlt.B.CCle (A - 1) o F b := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) hb
  obtain ⟨K, hK0, hK⟩ := _root_.Formalism.FourierDecayAlt.P.JCx2.pd_cut_ccle (k := P.k) (r := P.r) (E := Wq →L[ℂ] Wp) o
  have hGn : ∀ n : ℕ, _root_.Formalism.FourierDecayAlt.B.CCle (A - 1) o (fun g => cut n g • F g) (b + K * b) := by
    intro n
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h3 := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hb1 (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1 : ℂ) (hK ((n : ℝ) + 1) hR A F b hb))
    refine _root_.Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c (_root_.Formalism.FourierDecayAlt.P.JCx2.mn_ccle_congr ?_ h3) ?_
    · intro g _
      rw [hψ n g, sub_smul, one_smul, neg_one_smul, sub_eq_add_neg]
    · rw [norm_neg, norm_one, one_mul]
      linarith [div_le_self (mul_nonneg hK0 hb0) (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1)]
  have hG0 : _root_.Formalism.FourierDecayAlt.B.CCle (A - 1) o F (b + K * b) := _root_.Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c hb1 (by nlinarith)
  obtain ⟨C, hC0, hC⟩ := norm_opApply_le_of_polynomial_coeffs_lemma o κ (A - 1) Θ hΘ'
  have hexp : (κ : ℝ) - (A - 1) = -(A - 1 - κ) := by ring
  have hckn : ∀ n : ℕ, _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) (fun g => cut n g • F g) := by
    intro n
    have h := (_root_.Formalism.FourierDecayAlt.P.JCx2.pd_cut_nice (R := (n : ℝ) + 1) (by positivity) hF).1
    rw [hcutφ n]
    exact h
  unfold _root_.Formalism.FourierDecayAlt.KB.Pl.V
  refine hc₃ P.k P.r Wp Wq p.T.base p.ν' p.m₀ γ (A - 1 - κ) hA
    (fun n => _root_.Formalism.FourierDecayAlt.B.opApply Θ (fun g => cut n g • F g)) (_root_.Formalism.FourierDecayAlt.B.opApply Θ F) (C * (b + K * b))
    (by positivity)
    (fun n => (continuousOn_opApply_of_polynomial_coeffs_lemma_2 o κ Θ hΘ' (hckn n)).mono
      (fun g hg => hg.1))
    ((continuousOn_opApply_of_polynomial_coeffs_lemma_2 o κ Θ hΘ' hF).mono (fun g hg => hg.1))
    (fun n g hg => by
      have := hC _ _ (hGn n) g hg.1
      rwa [hexp] at this)
    (fun g hg => by
      have := hC _ _ hG0 g hg.1
      rwa [hexp] at this) ?_
  intro g _
  set S : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → ℝ := fun h => ∑ i, ∑ j, Complex.normSq (h i j) with hS
  have hScont : Continuous S :=
    continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))
  have hO : IsOpen {h | S h < S g + 1} := isOpen_lt hScont continuous_const
  obtain ⟨N, hN⟩ := exists_nat_ge (S g + 1)
  apply tendsto_const_nhds.congr'
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  symm
  apply _root_.Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open Θ hO _ g (by simp)
  intro h hh
  have hSh : S h < S g + 1 := hh
  have hS0 : 0 ≤ S h := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Complex.normSq_nonneg _
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hscaled : ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • h) i j) =
      ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1)⁻¹ * S h := by
    simp only [hS, Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul,
      Complex.normSq_ofReal, Finset.mul_sum]
  have hle : ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1)⁻¹ * S h ≤ 1 := by
    rw [← mul_inv, inv_mul_le_iff₀ (by positivity)]
    nlinarith
  have hone : cut n h = 1 := by
    rw [hcut, hscaled, Real.smoothTransition.one_of_one_le (by linarith)]
    simp
  simp only [hone, one_smul]

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiftedWordContinuousOnGPos
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem liftedWord_continuousOn_GPos : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → B.CkOn ⊤ (B.GV P.k P.r) F → ContinuousOn (p.Θ.Θ w e F) (B.GPos p.T.base) := by
  intro Wp Wq _ _ _ _ _ _ P0 p Cb w e F hDD hw hF
  obtain ⟨nf, fib, o, κ, Dop, -, hIn, -, -, hEq⟩ := hDD w hw e
  have hsub : B.GPos p.T.base ⊆ C6.domL p.T.base ∅ :=
    fun g hg => ⟨hg.1, hg.2, fun l hl => by simp at hl⟩
  have hGPG : B.GPos p.T.base ⊆ B.GV P0.k P0.r := fun g hg => hg.1
  have hcont : ContinuousOn (B.opApply Dop F) (B.GPos p.T.base) := by
    apply Formalism.FourierDecayAlt.P.PBE.opApply_continuousOn
    intro T hT
    have h1 : ContinuousOn T.coef (B.GPos p.T.base) :=
      (Formalism.FourierDecayAlt.P.PBE.ckOn_continuousOn' (fun g hg => hg.1) (hIn.1 T hT).1).mono hsub
    have h2 : ContinuousOn (B.Rw T.word F) (B.GPos p.T.base) :=
      (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (Formalism.FourierDecayAlt.P.JFxG.ckOn_Rw_top hF T.word T.word_lie)).mono hGPG
    exact h1.clm_apply h2
  exact hcont.congr (fun g hg => hEq F g (hsub hg))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorSumPolynomialOperatorStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantumMinor_sum_polynomialOperator : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r m κ : ℕ) (ι : Type) [Fintype ι] (a b : ι → Fin m → Fin (2 * r + k + 1)) (u : ℂ) (co : ι → B.Mat k r → ℂ), (∀ i, U.IsPolyDeg κ (co i)) → ∃ Θ : B.DiffOp k r Wp Wq, Formalism.FourierDecayAlt.P.CutMP.PolyOp m κ Θ ∧ ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), ∀ g ∈ B.GV k r, ∀ V : Set (B.Mat k r), IsOpen V → g ∈ V → B.CkOn ⊤ (B.GV k r ∩ V) F → B.opApply Θ F g = ∑ i, co i g • qminorOp (EabH (Hpk k r)) (a i) (b i) u F g := by
  first | exact @GlobalTheory.HatNF.MinorPoly.minor_polyOp | exact GlobalTheory.HatNF.MinorPoly.minor_polyOp | (intros; apply GlobalTheory.HatNF.MinorPoly.minor_polyOp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialMultipliersSatisfyNormalFormRelations
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.MulRelActual

section pairs

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mkPair_mul_mkPair (a b c d : Module.End ℂ V) : Q.mkP a b * Q.mkP c d = Q.mkP (a * c) (d * b) := rfl
theorem mkPair_add_mkPair (a b c d : Module.End ℂ V) : Q.mkP a b + Q.mkP c d = Q.mkP (a + c) (b + d) := rfl
theorem mkPair_sub_mkPair (a b c d : Module.End ℂ V) : Q.mkP a b - Q.mkP c d = Q.mkP (a - c) (b - d) := rfl
theorem mkPair_congr {a b c d : Module.End ℂ V} (h : a = c) (h' : b = d) : Q.mkP a b = Q.mkP c d := by rw [h, h']

theorem snd_eq_of_mkPair_eq {a b c d : Module.End ℂ V} (h : Q.mkP a b = Q.mkP c d) : b = d :=
  congrArg (fun x : Q.Pr V => MulOpposite.unop (Prod.snd x)) h

theorem commute_mkP {a b w : Module.End ℂ V} (ha : Commute a w) (hb : Commute b w) :
    Commute (Q.mkP a b) (Q.mkP w w) := by
  change Q.mkP a b * Q.mkP w w = Q.mkP w w * Q.mkP a b
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair]
  exact mkPair_congr ha.eq hb.eq.symm

theorem exists_mkP (x : Q.Pr V) : ∃ a b, x = Q.mkP a b := ⟨Prod.fst x, MulOpposite.unop (Prod.snd x), rfl⟩

end pairs

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

omit [FiniteDimensional ℂ Wp] in
theorem hsVec_smul (s : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (s • A) = s • B.hsVec A := rfl

omit [FiniteDimensional ℂ Wp] in
theorem hsVec_sub (A A' : Wq →L[ℂ] Wp) : B.hsVec (A - A') = B.hsVec A - B.hsVec A' := rfl

omit [FiniteDimensional ℂ Wp] in
theorem eq_zero_of_hsVec {A : Wq →L[ℂ] Wp} (h : B.hsVec A = 0) : A = 0 := by
  have h1 : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0 := fun i => congrArg (fun v => v i) h
  apply ContinuousLinearMap.coe_injective
  apply (stdOrthonormalBasis ℂ Wq).toBasis.ext
  intro i
  simpa using h1 i

omit [FiniteDimensional ℂ Wp] in
theorem eq_of_inner {A A' : Wq →L[ℂ] Wp}
    (h : inner ℂ (B.hsVec (A - A')) (B.hsVec A) = inner ℂ (B.hsVec (A - A')) (B.hsVec A')) : A = A' := by
  have h1 : inner ℂ (B.hsVec (A - A')) (B.hsVec (A - A')) = 0 := by
    nth_rewrite 2 [hsVec_sub]
    rw [inner_sub_right, h, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_hsVec (inner_self_eq_zero.1 h1))

variable {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem radSp_ext {Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'}
    (h : ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) : Φ = Ψ := by
  apply Subtype.ext
  funext c g
  by_cases hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z'
  · exact h (c, g) hx
  · rw [Φ.2.1 (c, g) hx, Ψ.2.1 (c, g) hx]

theorem commute_of_adj {a b w : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
    {m : (Fin P.r → ℂ) → Q.Mx P.k P.r → ℂ} (hw : P5.multiplicationOperator w m)
    (hab : ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
      B.hsInner ((a Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) =
        B.hsInner ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) ((b Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)) :
    Commute a w := by
  refine LinearMap.ext fun Φ => radSp_ext fun x hx => ?_
  apply eq_of_inner
  have h1 := hab (w Φ) (a (w Φ) - w (a Φ)) x hx
  have h2 := hab Φ (a (w Φ) - w (a Φ)) x hx
  unfold B.hsInner at h1 h2
  rw [hw Φ, hsVec_smul, inner_smul_right, ← h2, ← inner_smul_right, ← hsVec_smul, ← hw (a Φ)] at h1
  exact h1

theorem commute_of_ptAdj {x : RA P Bs} (hx : PtAdj P Bs x) {w : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
    {m : (Fin P.r → ℂ) → Q.Mx P.k P.r → ℂ} (hw : P5.multiplicationOperator w m) : Commute x (Q.mkP w w) := by
  obtain ⟨a, b, rfl⟩ := exists_mkP x
  refine commute_mkP (commute_of_adj (b := b) hw hx) (commute_of_adj (b := a) hw fun Φ Ψ y hy => ?_)
  have h := hx Ψ Φ y hy
  unfold B.hsInner at h ⊢
  rw [← inner_conj_symm, ← inner_conj_symm (B.hsVec ((a Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2))]
  exact congrArg _ h.symm

end hs

theorem mulRel_actual : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → MulRel d.L (fun q => Q.mkP (W q) (W q)) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN φ W hφ hW
  have hH := (GlobalTheory.T.normalForm_actualOperators_algebraicHypotheses Wp Wq P Bs X μ L st l0 d hD hN).1
  have hK := GlobalTheory.T.radialPairConstants_pointwiseAdjoint_bounded Wp Wq P Bs X μ L st l0 d hD hN
  have hC := GlobalTheory.T.eulerDerivMultipliers_coordOps_commutation_relations Wp Wq P Bs X μ L st l0 d hD hN φ W hφ hW
  have hT := GlobalTheory.T.normalForm_entries_commutator_multiplier Wp Wq P Bs X μ L st l0 d hD hN φ W hφ hW
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩, -, hR, hQ⟩ := hN
  have hκ : ∀ q (f : M.Ty P → ℂ), Commute (d.κ f) (Q.mkP (W q) (W q)) := fun q f =>
    commute_of_ptAdj (hK f).1 (hW q)
  have hf : ∀ q, ∀ f ∈ d.L.fns, Commute f (Q.mkP (W q) (W q)) := by
    intro q f hf
    obtain ⟨ho, hfn⟩ := hC q
    rcases hf with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | hf)
    · rw [h3]; exact commute_mkP (ho l).2.2.1 (ho l).2.2.2.2.1
    · rw [h4]; exact commute_mkP (ho l).2.2.2.1 (ho l).2.2.2.2.2
    · rw [h5]; exact commute_mkP (ho l).2.2.2.2.1 (ho l).2.2.1
    · rw [h6]; exact commute_mkP (ho l).2.2.2.2.2 (ho l).2.2.2.1
    · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h7]; exact commute_mkP (hfn _) (hfn _)
      · rw [h8]; exact commute_mkP (hfn _) (hfn _)
      · rw [h9]; exact commute_mkP (hfn _) (hfn _)
      · rw [h10]; exact commute_mkP (hfn _) (hfn _)
      · rw [h11]; exact commute_mkP (hfn _) (hfn _)
      · rw [h12]; exact commute_mkP (hfn _) (hfn _)
  refine GlobalTheory.T.connection_mulRel_of_entry_relations P (RA P Bs) d hH _ fun q => ⟨hf q, fun l => ?_, fun l => ?_, hκ q, rfl, fun Y => ?_⟩
  · rw [h1, mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_add_mkPair]
    refine mkPair_congr ((hC q).1 l).1 ?_
    rw [neg_mul, ((hC q).1 l).2.1, mul_neg]; abel
  · rw [h2, mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_add_mkPair]
    refine mkPair_congr ((hC q).1 l).2.1 ?_
    rw [neg_mul, ((hC q).1 l).1, mul_neg]; abel
  · have mζ : d.L.ζb ∈ d.L.fns := Or.inr (by simp)
    have mG : d.L.GG ∈ d.L.fns := Or.inr (by simp)
    have mGi : d.L.GGi ∈ d.L.fns := Or.inr (by simp)
    have e11 : d.QQ Y 1 1 = d.L.GG * d.x Y := rfl
    have c11 : ∀ g ∈ d.L.fns, Commute (d.QQ Y 1 1) g := fun g hg => by
      rw [e11]
      exact Commute.mul_left (d.L.fns_comm _ mG _ hg) (hR.2.1 _ g (Or.inl hg))
    have c11m : Commute (d.QQ Y 1 1) (Q.mkP (W (q + 1)) (W (q + 1))) := by
      rw [e11]
      exact Commute.mul_left (hf _ _ mG) (hκ _ _)
    have cζG : Commute d.L.ζb d.L.GGi := d.L.fns_comm _ mζ _ mGi
    have key : d.L.ζb * d.L.GGi * Q.mkP (W (q + 1)) (W (q + 1)) * d.QQ Y 1 1 =
        d.QQ Y 1 1 * (Q.mkP (W (q + 1)) (W (q + 1)) * (d.L.GGi * d.L.ζb)) := by
      rw [← (((c11 _ mζ).mul_right (c11 _ mGi)).mul_right c11m).eq,
        (Commute.mul_left (hf (q + 1) _ mζ) (hf (q + 1) _ mGi)).eq, cζG.eq]
    have hY : star (Y : ℂ) = Y := Complex.conj_ofReal Y
    have q10 : d.QQ Y 1 0 = Q.mkP (X.t Y 1 0) (X.t Y 0 1) := by
      rw [← hQ]
      change Q.mkP (X.t Y 1 0) (X.t (star (Y : ℂ)) 0 1) = _
      rw [hY]
    have q11 : d.QQ Y 1 1 = Q.mkP (X.t Y 1 1) (X.t Y 1 1) := by
      rw [← hQ]
      change Q.mkP (X.t Y 1 1) (X.t (star (Y : ℂ)) 1 1) = _
      rw [hY]
    rw [q11, h9, h12] at key
    rw [q10, q11, h9, h12]
    simp only [mkPair_mul_mkPair, mkPair_sub_mkPair] at key ⊢
    refine mkPair_congr (hT q Y).1 ?_
    rw [snd_eq_of_mkPair_eq key, (hT q Y).2.2]
    abel

end GlobalTheory.HatNF.MulRelActual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TranslateCoprimeOrderNotIncreaseThetaCombNormStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_coprime_order_not_increase_theta_comb_norm : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (a m : ℕ) (c : Fin m → ℂ_[q]) (s : Fin m → ℂ) (t : ℂ) (B : ℝ), (∀ j, PrimeTo d q (s j)) → PrimeTo d q t → ¬ InOK d (t - 1 / 2) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d (s j) θ) ^ a) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d t (U1 d (s j) θ)) ^ a) := by
  first | exact @GlobalTheory.MomOne.TranslNorm.translate_bd | exact GlobalTheory.MomOne.TranslNorm.translate_bd | (intros; apply GlobalTheory.MomOne.TranslNorm.translate_bd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeilOperatorThetaTranslateShiftPrimeToQStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_theta_translate_shift_prime_to_q : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → (∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ M.At ω (M.ι (kap1 d 1 y)) y) → ∀ (t y : ℂ) (n s : ℕ), Nat.Coprime s q → InOK d ((s : ℂ) * t) → Good M.ι d n s y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ hat M.ι (C ω * logS) (W1 d y (U1 d t θ)) = shiftS (M.ι (kap1 d 1 y)) (hat M.ι (C ω * logS) (U1 d t θ)) := by
  first | exact @GlobalTheory.MomOne.TranslateLaw.main | exact GlobalTheory.MomOne.TranslateLaw.main | (intros; apply GlobalTheory.MomOne.TranslateLaw.main <;> assumption)
end

