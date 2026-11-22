import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0185
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0297
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.Bundle0007
import Formalism.HermitianCurvature.Bundle0004
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0182
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0186
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0160
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0061
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0165
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0161
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0129
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0127
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0175
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0110

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsCoefContinuousOn
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SupMeas

theorem isDS_continuousOn {k r : ℕ} {R : Rep k r} {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ}
    (h : R.IsDS ε μ) (v : R.H) : ContinuousOn (fun g => R.σ g v) (GG k r) := by
  obtain ⟨-, P, hP, -, -, ⟨-, -, hc⟩, -⟩ := h
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hmaps := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.cayley_maps hP
  have e : ∀ g : Mx k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]
  have h3 : Continuous fun g : Mx k r => P * g * P⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have := (hc v).comp h3.continuousOn hmaps
  simpa only [Function.comp_def, e] using this

theorem isCoef_continuousOn {k r : ℕ} {R : Rep k r} {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ}
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    {l : R.H → Wp} {l' : R.H → Wq} {F : Mx k r → (Wq →L[ℂ] Wp)} {s : ℂ}
    (h : R.IsDS ε μ) (hF : IsCoef R l l' F s) : ContinuousOn F (GG k r) := by
  obtain ⟨m, x, y, X, -, hF, -⟩ := hF
  refine ContinuousOn.congr ?_ hF
  exact continuousOn_finsetSum _ fun i _ =>
    (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (isDS_continuousOn h (y i))).smul continuousOn_const

theorem sup_meas : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Sup p lam q0 R l l' dg s J tau → ∀ ν, AEMeasurable fun c : Fin (P.r + 1) → ℂ => ENNReal.ofReal (TBB.Ew p (fun _ => 1) (J ν) (P.r + 1) [] (TBB.bigPt P.r c)) := by
  intro _ P Wp Wq _ _ _ _ _ _ p lam b bv ga h q0 R l l' dg s J tau _ hS ν
  apply GlobalTheory.T.aemeasurable_besselNormIntegrand_bigCell
  by_cases hν : n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)
  · exact isCoef_continuousOn (hS.fam ν hν.1) (hS.coef ν hν.1 hν.2.1 hν.2.2).1
  · rw [hS.zero ν hν]
    exact continuousOn_const

end GlobalTheory.SupMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IteratedDerivBddOfEventuallyConst
section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open MeasureTheory in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private theorem exists_smooth_bounded_derivs_eq_pow_mul_of_cutPow {e : ℕ} {φ : ℝ → ℝ} (hφ : _root_.GlobalTheory.HatNF.CutPow e φ) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ (∀ q : ℕ, ∃ c, ∀ x, ‖iteratedDeriv q h x‖ ≤ c) ∧
      ∀ x, φ x = x ^ e * h x := by
  unfold _root_.GlobalTheory.HatNF.CutPow at hφ
  obtain ⟨hφs, ⟨δ, hδ, hφ0⟩, a, R, hφR⟩ := hφ
  have hzero : ∀ x < δ, (fun y => φ y / y ^ e) =ᶠ[nhds x] fun _ => (0 : ℝ) := fun x hx =>
    (eventually_lt_nhds hx).mono fun y hy => by
      show φ y / y ^ e = 0
      rw [hφ0 y hy, zero_div]
  have hconst : ∀ x, max R δ < x → (fun y => φ y / y ^ e) =ᶠ[nhds x] fun _ => a := fun x hx =>
    (eventually_gt_nhds hx).mono fun y hy => by
      have hy0 : 0 < y := hδ.trans (lt_of_le_of_lt (_root_.le_max_right _ _) hy)
      have hy1 : φ y = a * y ^ e := hφR y ((_root_.le_max_left _ _).trans hy.le)
      simp only
      rw [hy1, mul_div_assoc, div_self (pow_ne_zero _ hy0.ne'), mul_one]
  have hsmooth : ContDiff ℝ ∞ (fun y => φ y / y ^ e) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases lt_or_ge x δ with hx | hx
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero x hx)
    · exact hφs.contDiffAt.div (contDiffAt_id.pow e) (pow_ne_zero _ (hδ.trans_le hx).ne')
  refine ⟨fun y => φ y / y ^ e, hsmooth, fun q => ?_, fun x => ?_⟩
  · obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc δ (max R δ))).exists_bound_of_continuousOn
      (hsmooth.continuous_iteratedDeriv q (WithTop.coe_le_coe.mpr le_top)).continuousOn
    refine ⟨max C (max |a| 0), fun x => ?_⟩
    rcases lt_or_ge x δ with hx | hx
    · rw [(hzero x hx).iteratedDeriv_eq, iteratedDeriv_const]
      split_ifs <;> rw [norm_zero] <;> exact (_root_.le_max_right _ _).trans (_root_.le_max_right _ _)
    rcases le_or_gt x (max R δ) with hx' | hx'
    · exact (hC x ⟨hx, hx'⟩).trans (_root_.le_max_left _ _)
    · rw [(hconst x hx').iteratedDeriv_eq, iteratedDeriv_const]
      split_ifs
      · rw [Real.norm_eq_abs]; exact (_root_.le_max_left _ _).trans (_root_.le_max_right _ _)
      · rw [norm_zero]; exact (_root_.le_max_right _ _).trans (_root_.le_max_right _ _)
  · rcases lt_or_ge x δ with hx | hx
    · show φ x = x ^ e * (φ x / x ^ e)
      rw [hφ0 x hx, zero_div, mul_zero]
    · have hx0 : x ^ e ≠ 0 := pow_ne_zero _ (hδ.trans_le hx).ne'
      show φ x = x ^ e * (φ x / x ^ e)
      rw [mul_comm, div_mul_cancel₀ (φ x) hx0]

open MeasureTheory in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private theorem ckOn_smul_of_ckOn_infinite {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {c : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ} (hc : ContDiff ℝ ∞ c) {F : _root_.Formalism.FourierDecayAlt.B.Mat k r → E} (n : ℕ∞)
    (hF : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F) : _root_.Formalism.FourierDecayAlt.B.CkOn n (_root_.Formalism.FourierDecayAlt.B.GV k r) (fun g => c g • F g) := by
  unfold _root_.Formalism.FourierDecayAlt.B.CkOn at hF ⊢
  intro g₀ hg₀
  obtain ⟨U, F', hU, hgU, hF', hEq⟩ := hF g₀ hg₀
  refine ⟨U, fun g => c g • F' g, hU, hgU, ?_, fun g hgU hg => by simp only [hEq g hgU hg]⟩
  exact (hc.contDiffOn.smul hF').of_le (WithTop.coe_le_coe.mpr le_top)

open MeasureTheory in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private theorem inCC_real_smul_comp_Gf_of_inCC {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hb : ∀ q : ℕ, ∃ c, ∀ x, ‖iteratedDeriv q h x‖ ≤ c)
    {f : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} {A : ℝ} {m : ℕ} (hf : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) f)
    (hA : _root_.Formalism.FourierDecayAlt.B.InCC A m f) :
    _root_.Formalism.FourierDecayAlt.B.InCC (A - (2 * (r : ℝ) + 2) * m) m (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k r z z' g) : ℝ) : ℂ) • f g) := by
  obtain ⟨ρ, rfl⟩ : ∃ ρ, r = 0 + ρ := ⟨r, (zero_add r).symm⟩
  have hcd : ContDiff ℝ ∞ (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hh.comp (_root_.Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf z z'))
  obtain ⟨M, hM⟩ := _root_.Formalism.FourierDecayAlt.P.AdmissibleLieWords.poly_H (_root_.Formalism.FourierDecayAlt.P.AdmissibleLieWords.gf_pd k (0 + ρ) z z') m
  obtain ⟨K, hK0, hK⟩ := _root_.PI.UnitaryCorollaryDerivatives.CRH.main (fun g => _root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) h
    (fun _ => 2 * (0 + ρ) + 2) m M (_root_.Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf z z') hh hb (fun w hw hne g hg => by
      have hp : _root_.PI.UnitaryCorollaryDerivatives.CRH.cs (fun _ => 2 * (0 + ρ) + 2) w = (2 * (0 + ρ) + 2) * w.length := by
        simp only [_root_.PI.UnitaryCorollaryDerivatives.CRH.cs, List.map_const', List.sum_replicate, smul_eq_mul]
        ring
      rw [hp]
      exact hM w hw hne g hg) m 0
  have hWB : _root_.PI.UnitaryCorollaryDerivatives.WB (fun X => _root_.PI.UnitaryCorollaryDerivatives.costP k 0 ρ X + (2 * (0 + ρ) + 2))
      (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) : ℝ) : ℂ)) (m + 0) K 0 := by
    unfold _root_.PI.UnitaryCorollaryDerivatives.WB
    intro u v hu hv huv g hg
    rw [_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_eq]
    have hadm : _root_.PI.UnitaryCorollaryDerivatives.CRH.admitted m (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v) := ⟨u, v, hu, hv, huv, rfl⟩
    have hlen : (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v).length ≤ m := by
      simp only [_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL, _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR, List.length_append, List.length_map]; omega
    have hK1 := hK _ hadm hlen g hg
    simp only [iteratedDeriv_zero] at hK1
    have hn : _root_.PI.UnitaryCorollaryDerivatives.CRH.cs (fun _ => 2 * (0 + ρ) + 2) (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v) ≤
        (List.map (fun X => _root_.PI.UnitaryCorollaryDerivatives.costP k 0 ρ X + (2 * (0 + ρ) + 2)) (u ++ v)).sum := by
      simp only [_root_.PI.UnitaryCorollaryDerivatives.CRH.cs, _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL, _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR, List.map_append, List.map_map, List.sum_append,
        List.sum_map_add, Function.comp_def, List.map_const', List.sum_replicate, smul_eq_mul,
        List.length_map]
      omega
    calc _ ≤ K * _root_.Formalism.FourierDecayAlt.B.gN g ^ _root_.PI.UnitaryCorollaryDerivatives.CRH.cs (fun _ => 2 * (0 + ρ) + 2) (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v) := hK1
      _ = K * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((_root_.PI.UnitaryCorollaryDerivatives.CRH.cs (fun _ => 2 * (0 + ρ) + 2) (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL u ++ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR v) : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg)
          (by linarith [(Nat.cast_le (α := ℝ)).mpr hn])) hK0
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := _root_.PI.UnitaryCorollaryDerivatives.cC_bound (j := 0) (ρ := ρ) (E := Wq →L[ℂ] Wp) (Q := m) (o := 0)
    (mm₀ := m) (A₀ := A) hcd hWB (w := []) (fun X hX => nomatch hX) (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨c, hc⟩ := id hA
  have hc' := hc
  unfold _root_.Formalism.FourierDecayAlt.B.InCC
  refine ⟨CΨ * c, ?_⟩
  unfold _root_.Formalism.FourierDecayAlt.B.CCle at hc ⊢
  refine ⟨ckOn_smul_of_ckOn_infinite hcd _ hf, fun u v hu hv huv g hg => ?_⟩
  have hIW : ∀ w : List (_root_.Formalism.FourierDecayAlt.B.Mat k (0 + ρ)), (∀ X ∈ w, _root_.Formalism.FourierDecayAlt.B.unitLie k (0 + ρ) X) → _root_.Formalism.FourierDecayAlt.U.unitP k 0 ρ w :=
    fun w hw X hX => ⟨⟨(hw X hX).1, fun i b hb' _ => absurd hb' (Nat.not_lt_zero _)⟩, (hw X hX).2⟩
  have hB : ‖_root_.Formalism.FourierDecayAlt.B.dLR u v (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) : ℝ) : ℂ) • f g) g‖ ≤
      CΨ * c * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((0 : ℕ) * ((0 : ℕ) : ℝ) + ((2 * (0 + ρ) + 2 : ℕ) : ℝ) * ((m + 0 : ℕ) : ℝ) - A) :=
    hCΨ f c hc' u v (hIW u hu) (hIW v hv) huv g hg
  have hpos := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_pos hg
  calc _root_.Formalism.FourierDecayAlt.B.gN g ^ (A - (2 * ((0 + ρ : ℕ) : ℝ) + 2) * m) *
        ‖_root_.Formalism.FourierDecayAlt.B.dLR u v (fun g => ((h (_root_.Formalism.QuantumDeterminants.Gf k (0 + ρ) z z' g) : ℝ) : ℂ) • f g) g‖
      ≤ _root_.Formalism.FourierDecayAlt.B.gN g ^ (A - (2 * ((0 + ρ : ℕ) : ℝ) + 2) * m) *
        (CΨ * c * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((0 : ℕ) * ((0 : ℕ) : ℝ) + ((2 * (0 + ρ) + 2 : ℕ) : ℝ) * ((m + 0 : ℕ) : ℝ) - A)) :=
        mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hpos.le _)
    _ = CΨ * c := by
        rw [mul_comm, mul_assoc, ← Real.rpow_add hpos]
        have h0 : ((0 : ℕ) * ((0 : ℕ) : ℝ) + ((2 * (0 + ρ) + 2 : ℕ) : ℝ) * ((m + 0 : ℕ) : ℝ) - A) +
            (A - (2 * ((0 + ρ : ℕ) : ℝ) + 2) * m) = 0 := by
          simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
          ring
        rw [h0, Real.rpow_zero, mul_one]

open MeasureTheory in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem _root_.GlobalTheory.HatNF.mulG_ckOn_inCC : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : _root_.Formalism.FourierDecayAlt.M.Par) (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq), ∀ (e m : ℕ) (φ : ℝ → ℝ)
    (f : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), _root_.GlobalTheory.HatNF.CutPow e φ →
    _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) f → _root_.Formalism.FourierDecayAlt.B.InCC A m f →
    _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) (_root_.GlobalTheory.HatNF.mulG Bs φ f) ∧
      _root_.Formalism.FourierDecayAlt.B.InCC (A - (2 * (P.r : ℝ) + 2) * ((e : ℝ) + m)) m (_root_.GlobalTheory.HatNF.mulG Bs φ f) := by
  intro Wp Wq _ _ _ _ _ _ P Bs e m φ f A hφ hf hA
  have hval : _root_.GlobalTheory.HatNF.mulG Bs φ f =
      fun g => ((φ (_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g) : ℝ) : ℂ) • f g := rfl
  obtain ⟨h, hh, hb, hφh⟩ := exists_smooth_bounded_derivs_eq_pow_mul_of_cutPow hφ
  have hφs : ContDiff ℝ ∞ φ := by
    unfold _root_.GlobalTheory.HatNF.CutPow at hφ
    exact hφ.1
  have hfun : _root_.GlobalTheory.HatNF.mulG Bs φ f = fun g =>
      ((_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g ^ e : ℝ) : ℂ) •
        (((h (_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g) : ℝ) : ℂ) • f g) := by
    rw [hval]
    funext g
    rw [smul_smul, ← Complex.ofReal_mul, ← hφh]
  refine ⟨?_, ?_⟩
  · rw [hval]
    exact ckOn_smul_of_ckOn_infinite (c := fun g => ((φ (_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g) : ℝ) : ℂ))
      (Complex.ofRealCLM.contDiff.comp (hφs.comp (_root_.Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z'))) ⊤ hf
  · rw [hfun]
    obtain ⟨c, hc⟩ := inCC_real_smul_comp_Gf_of_inCC Bs.z Bs.z' hh hb hf hA
    have hpd := (show (∀ F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp, _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) F →
        _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r)
          (fun g => ((_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g ^ e : ℝ) : ℂ) • F g)) ∧
      ∀ (A' : ℝ) (m' : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → Wq →L[ℂ] Wp) (b : ℝ),
        _root_.Formalism.FourierDecayAlt.B.CCle (A' + (((2 * P.r + 2) * e : ℕ) : ℝ)) m' F b →
          _root_.Formalism.FourierDecayAlt.B.CCle A' m' (fun g => ((_root_.Formalism.QuantumDeterminants.Gf P.k P.r Bs.z Bs.z' g ^ e : ℝ) : ℂ) • F g) (K * b) from
      _root_.Formalism.FourierDecayAlt.P.CutBP.pd_good_Gpow (Wp := Wp) (Wq := Wq) Bs.z Bs.z' e).2
    obtain ⟨K, -, hK⟩ := hpd (A - (2 * (P.r : ℝ) + 2) * ((e : ℝ) + m)) m
    refine ⟨K * c, hK _ c ?_⟩
    have hA' : A - (2 * (P.r : ℝ) + 2) * ((e : ℝ) + m) + (((2 * P.r + 2) * e : ℕ) : ℝ) =
        A - (2 * (P.r : ℝ) + 2) * m := by
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      ring
    rw [hA']
    exact hc

end

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormDiagonalBigCellImEqZero
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.LevelFormsReal

theorem isLocPt_ofFn {j : ℕ} (c : Fin j → ℂ) (hc : ∀ l, c l ≠ 0) :
    D.IsLocPt (List.ofFn fun l => ((1 : ℕ), c l)) j := by
  refine ⟨fun b hb => ?_, ?_⟩
  · simp only [List.mem_ofFn] at hb
    obtain ⟨l, rfl⟩ := hb
    exact ⟨by simp, hc l⟩
  · simp [D.ptSize, List.map_ofFn, Function.comp_def]

theorem ofFn_snoc {j : ℕ} (c : Fin j → ℂ) (t : ℂ) :
    (List.ofFn fun l => ((1 : ℕ), (Fin.snoc c t : Fin (j + 1) → ℂ) l))
      = (List.ofFn fun l => ((1 : ℕ), c l)) ++ [(1, t)] := by
  rw [List.ofFn_succ']
  simp

theorem integral_im_eq_zero {f : ℂ → ℂ} (hf : ∀ t, t ≠ 0 → (f t).im = 0) :
    (∫ t : ℂ, f t).im = 0 := by
  have h : f =ᵐ[volume] fun t => (((f t).re : ℝ) : ℂ) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with t ht
    exact Complex.ext (by simp) (by simp [hf t ht])
  rw [integral_congr_ae h, integral_complex_ofReal]
  simp

theorem levelZero_im_eq_zero : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CutWord P p.l0 w → (p.RR H 0 w [] []).im = 0 := by
  intro hP Wp Wq _ _ _ _ _ _ P p Cb H w hD hH hw
  have key : ∀ (n j : ℕ), j + n = P.r + 1 → ∀ c : Fin j → ℂ, (∀ l, c l ≠ 0) →
      (p.RR H j w (List.ofFn fun l => ((1 : ℕ), c l)) (List.ofFn fun l => ((1 : ℕ), c l))).im = 0 := by
    intro n
    induction n with
    | zero =>
      intro j hj c hc
      obtain rfl : j = P.r + 1 := hj
      exact (GlobalTheory.T.topDensity_bigCell_eq_prod_levelWeights_mul_topForm Wp Wq P p H w c hc).2.1
    | succ n ih =>
      intro j hj c hc
      rw [(GlobalTheory.T.levelModuleForm_eq_integral_of_compactCoeff hP Wp Wq P p Cb H w j _ hD hH hw (by omega) (isLocPt_ofFn c hc)).2]
      refine integral_im_eq_zero fun t ht => ?_
      have h := ih (j + 1) (by omega) (Fin.snoc c t) (fun l => by
        refine Fin.lastCases ?_ (fun i => ?_) l
        · simpa using ht
        · simpa using hc i)
      rw [ofFn_snoc] at h
      simp [Complex.mul_im, h]
  simpa using key (P.r + 1) 0 (by omega) (fun l => l.elim0) (fun l => l.elim0)

end GlobalTheory.LevelFormsReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordBoundCompactSupportCoefficients
section
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem polyLift_listProd {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (o κ : ℕ) (H : List (RA P Bs)) (hH : ∀ h ∈ H, PolyLift P Bs o κ h) :
    PolyLift P Bs (H.length * o) (H.length * κ) H.prod := by
  obtain ⟨h1, -, hmul⟩ := GlobalTheory.T.polyLift_one_mono_mul Wp Wq P Bs
  induction H with
  | nil => simpa using h1
  | cons a H ih =>
    have := hmul _ _ _ _ _ _ (hH a (by simp)) (ih fun h hh => hH h (by simp [hh]))
    rw [List.prod_cons, List.length_cons, Nat.succ_mul, Nat.succ_mul, add_comm _ o, add_comm _ κ]
    exact this

theorem wordBound_cptCoef : ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (w : List C.Letter), KB.CutWord P p.l0 w → ∃ (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq)), WordBound p (a P.r) w C J Θs (fun φ f => ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ KB.CptCoef p.T.base f) := by
  intro a ha Wp Wq _ _ _ _ _ _ P p w hw
  obtain ⟨X, μ, L, st, hD, hL⟩ := p.hΘ
  obtain ⟨d, hd⟩ := Formalism.FourierDecayAlt.P.normal_form_actual Wp Wq P _ _ _ _ p.hP X
  have hNF : IsNF (Bs := p.T.base) X d := hd
  have hok := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of P _ _ _ _ st p.l0 hD.1.1 p.hl.1 p.hl.2.1 hD.2.2.2.2.1 hD.2.2.2.2.2.1 w
    hw.1 hw.2
  have hl : (D.positionted w).length = w.length := by simp [D.positionted]
  obtain ⟨C, J, Ts, hC, hTs, hB⟩ := GlobalTheory.T.wordOperator_radial_pointwise_bound Wp Wq P p.T.base X μ L st p.l0 d hD hNF (Fin w.length) _ (a P.r)
    (ha Wp Wq P p.T.base X μ L st p.l0 d hD hNF) (D.positionted w) hok.1
  rw [hl] at hTs hB
  have hlift : ∀ H : List (RA P p.T.base), ∃ Θ : B.DiffOp P.k P.r Wp Wq, H ∈ Ts →
      Formalism.FourierDecayAlt.P.CutMP.PolyOp (w.length * (2 * P.r + P.k + 1))
        (w.length * (8 * (P.r + 1) * (2 * P.r + P.k + 1))) Θ ∧ TL.RadIs P p.T.base Θ H.prod.1 := by
    intro H
    by_cases hH : H ∈ Ts
    · obtain ⟨Θ, hΘ⟩ := polyLift_listProd P p.T.base _ _ H (hTs H hH).2
      rw [(hTs H hH).1] at hΘ
      exact ⟨Θ, fun _ => hΘ⟩
    · obtain ⟨Θ, -⟩ := (GlobalTheory.T.polyLift_one_mono_mul Wp Wq P p.T.base).1
      exact ⟨Θ, fun h => absurd h hH⟩
  choose lf hlf using hlift
  refine ⟨C, J, Ts.map lf, hC, ?_, ?_⟩
  · intro Θ hΘ
    obtain ⟨H, hH, rfl⟩ := List.mem_map.1 hΘ
    exact (hlf H hH).1
  · rintro φ f ⟨hφ, hf⟩ e c hc hG
    obtain ⟨hm1, hm2⟩ := GlobalTheory.T.radial_picture_smul_cutoff_G_multiplier Wp Wq P p.T.base φ f
    obtain ⟨hsl, hcpt⟩ := hm1 hφ
    obtain ⟨W, hW⟩ := mulG_exists Wp Wq P p.T.base X μ L st p.l0 d hD hNF φ hsl
    obtain ⟨⟨ε, hε, hN⟩, -⟩ := Formalism.FourierDecayAlt.P.compact_support_facts P.k P.r Wp Wq p.T.base f hf
    obtain ⟨Φ, hΦ⟩ := Formalism.FourierDecayAlt.P5.radJFExists Wp Wq P _ _ _ _ p.T.base f p.hP rfl rfl rfl rfl
      ⟨hN.2.1, ε, hε, hN.2.2⟩
    have hΦ' : Top.IsRadOf P p.T.base Φ f := hΦ
    have hrad := hL w hw _ (hcpt hf) _ (hm2 W Φ hW hΦ') e
    rw [TL.act_e1Vec] at hrad
    obtain ⟨x, hx, hg, hdd, lam, hlam, hV⟩ := GlobalTheory.T.bigCellVector_norm_eq_radialValue_norm Wp Wq P p c hc hG
    have hb := hB φ W hsl hW Φ e x hx
    rw [hg, hdd] at hb
    have hs : ((Ts.map lf).map fun Θ => ‖B.hsVec (p.V (B.opApply Θ f) (TBB.bigPt P.r c))‖).sum =
        lam * (Ts.map fun H => nv (H.prod.1 Φ) x).sum := by
      rw [List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun H hH => ?_
      exact hV _ _ ((hlf H hH).2 f hf Φ hΦ')
    rw [hV _ _ hrad, hs]
    have := mul_le_mul_of_nonneg_left hb hlam.le
    refine le_trans (le_of_eq rfl) (this.trans (le_of_eq ?_))
    ring

end GlobalTheory.HatNF
end

