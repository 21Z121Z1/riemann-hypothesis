import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0200
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0238
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0239
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.THProvA
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0240
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaximalCompactActsOnFockVectorsBySubstitution
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompact

theorem det_isUnit_of_onb {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ}
    (h : Formalism.IndefR.Datum.IsONBasis G s B p) : IsUnit B.det := by
  obtain ⟨ε, hε, hB, -⟩ := h
  have hd : (Bᴴ * G * B).det ≠ 0 := by
    rw [hB, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
    rcases hε a with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
  rw [Matrix.det_mul] at hd
  exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hd)

theorem comm_of_onb {k : ℕ} {G s B κ : Matrix (Fin k) (Fin k) ℂ} {p : ℕ}
    (h : Formalism.IndefR.Datum.IsONBasis G s B p) (hκ : IsKMat p κ) : s * (B * κ * B⁻¹) = B * κ * B⁻¹ * s := by
  have hu := det_isUnit_of_onb h
  obtain ⟨ε, hε, -, hs⟩ := h
  obtain ⟨-, hκ0⟩ := hκ
  have hBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hu
  have hiB : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hu
  have hcomm : (diagonal fun a => (ε a : ℂ)) * κ = κ * diagonal fun a => (ε a : ℂ) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : (i.val < p ↔ j.val < p)
    · have hij' : ε i = ε j := by
        rcases hε i with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩ <;> rcases hε j with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩
        · rw [hi1, hj1]
        · exact absurd (hij.mp hi2) (by omega)
        · exact absurd (hij.mpr hj2) (by omega)
        · rw [hi1, hj1]
      rw [hij', mul_comm]
    · rw [hκ0 i j hij, mul_zero, zero_mul]
  have hs' : s = B * (diagonal fun a => (ε a : ℂ)) * B⁻¹ := by
    calc s = s * (B * B⁻¹) := by rw [hBi, mul_one]
      _ = B * (diagonal fun a => (ε a : ℂ)) * B⁻¹ := by rw [← mul_assoc, hs]
  rw [hs']
  simp only [mul_assoc]
  rw [← mul_assoc B⁻¹ B, hiB, one_mul, ← mul_assoc B⁻¹ B, hiB, one_mul, ← mul_assoc _ κ, hcomm, mul_assoc κ]

theorem compAt_of_atTau {D : D7} {θ : InfFam D} {S : HSp D} {τ : D.what₂.Tau}
    {M : Matrix (Fin S.rank) (Fin S.rank) ℂ} {g : GA D S} (h : IsAtTau θ S τ M g) :
    compAt θ τ (Formalism.L2.Theta.mt S g) = M ∧ ∀ ρ, ρ ≠ τ → compAt θ ρ (Formalism.L2.Theta.mt S g) = 1 := by
  obtain ⟨-, h1, h2⟩ := h
  refine ⟨Eq.trans ?_ h1, fun ρ hρ => Eq.trans ?_ (h2 ρ hρ)⟩
  · rfl
  · rfl

theorem om_pureTensorO_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → ∀ (τ : D.what₂.Tau) κS κT, IsKMat (pS τ) κS → IsKMat (pT τ) κT → ∀ g h, IsAtTau θ S τ (BS τ * κS * (BS τ)⁻¹) g → IsAtTau θ T τ (BT τ * κT * (BT τ)⁻¹) h → ∀ c : ℂ, om (g, h) f = c • f → ∀ P, om (g, h) (pureTensorO ψ θ S T sS sT BS BT f P) = c • pureTensorO ψ θ S T sS sT BS BT f (fockSub τ (pS τ) (pT τ) κS κT P) := by
  intro D ψ θ S T χS χT om hW hθ sS BS sT BT pS pT hpS hpT hcS hcT hoS hoT f hf τ κS κT hκS hκT g h hg hh c hc P
  have hstd : IsStdChar D ψ (-1) := hW.std
  obtain ⟨hgτ, hgρ⟩ := compAt_of_atTau hg
  obtain ⟨hhτ, hhρ⟩ := compAt_of_atTau hh
  have hcomS : ∀ ρ, sS ρ * compAt θ ρ (Formalism.L2.Theta.mt S g) = compAt θ ρ (Formalism.L2.Theta.mt S g) * sS ρ := by
    intro ρ
    by_cases hρ : ρ = τ
    · subst hρ
      rw [hgτ]
      exact comm_of_onb (hoS ρ) hκS
    · rw [hgρ ρ hρ, mul_one, one_mul]
  have hcomT : ∀ ρ, sT ρ * compAt θ ρ (Formalism.L2.Theta.mt T h) = compAt θ ρ (Formalism.L2.Theta.mt T h) * sT ρ := by
    intro ρ
    by_cases hρ : ρ = τ
    · subst hρ
      rw [hhτ]
      exact comm_of_onb (hoT ρ) hκT
    · rw [hhρ ρ hρ, mul_one, one_mul]
  have key := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS
    (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt S g) * BS ρ) sT sT BT
    (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt T h) * BT ρ) g h hcomS hcomT (fun _ => rfl) (fun _ => rfl) f hf P).2
  rw [key, hc, GlobalTheory.FiniteFock.pureTensorO_smul]
  have e2 := GlobalTheory.T.fockPolynomialVector_maximalCompact_moved_bases D ψ θ S T hstd hθ sS BS sT BT pS pT hpS hpT hcS hcT hoS hoT f hf τ κS κT hκS hκT
    (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt S g) * BS ρ) (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt T h) * BT ρ) ?_ ?_ ?_ P
  · rw [e2]
  · show compAt θ τ (Formalism.L2.Theta.mt S g) * BS τ = BS τ * κS
    rw [hgτ, mul_assoc, Matrix.nonsing_inv_mul _ (det_isUnit_of_onb (hoS τ)), mul_one]
  · show compAt θ τ (Formalism.L2.Theta.mt T h) * BT τ = BT τ * κT
    rw [hhτ, mul_assoc, Matrix.nonsing_inv_mul _ (det_isUnit_of_onb (hoT τ)), mul_one]
  · intro ρ hρ
    refine ⟨?_, ?_⟩
    · show compAt θ ρ (Formalism.L2.Theta.mt S g) * BS ρ = BS ρ
      rw [hgρ ρ hρ, one_mul]
    · show compAt θ ρ (Formalism.L2.Theta.mt T h) * BT ρ = BT ρ
      rw [hhρ ρ hρ, one_mul]

end GlobalTheory.FockCompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModerateGrowthSobolevSizeRightTranslatePolyBound
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.Grow GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.Size
open scoped ENNReal NNReal

namespace GlobalTheory.Size.Translate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem wordSum_succ {ι X : Type} [Fintype ι] (A : ι → X → X) (p : X → ℝ≥0∞) (d : ℕ) (x : X) :
    wordSum A p (d + 1) x = p x + ∑ i, wordSum A p d (A i x) := by
  classical
  unfold wordSum
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · simp [wordAct_nil]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Fintype.sum_prod_type']
    symm
    refine Fintype.sum_equiv (Fin.snocEquiv fun _ => ι) _ _ fun q => ?_
    change _ = p (wordAct A (List.ofFn (fun i => (Fin.snoc (α := fun _ => ι) q.2 q.1 i : ι))) x)
    rw [List.ofFn_succ']
    simp [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, wordAct_append, wordAct_cons, wordAct_nil]

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem growthSob_sum_le {α : Type} (s : Finset α) (f : α → GA D V → ℂ) (hf : ∀ a, f a ∈ SmFun θ V) (d N : ℕ) :
    growthSob θ V d N (∑ a ∈ s, f a) ≤ ∑ a ∈ s, growthSob θ V d N (f a) := by
  classical
  induction s using Finset.induction_on
  · simpa using growthSob_smul (θ := θ) (φ := (0 : GA D V → ℂ)) (0 : ℂ) d N
  · rename_i a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (growthSob_add_le (hf a) (Submodule.sum_mem _ fun b _ => hf b) d N).trans (add_le_add le_rfl ih)

theorem growthSob_RderC_le (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hs : φ ∈ SmFun θ V) (τ : D.what₂.Tau)
    {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ} {B : ℝ≥0∞} (hB : ∀ a b, ‖Z a b‖ₑ ≤ B) (d N : ℕ) :
    growthSob θ V d N (RderC θ V τ Z φ) ≤
      (Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0∞) * (B * growthSob θ V (d + 1) N φ) := by
  rw [RderC_eq_sum_glDer hθ hs τ Z]
  have hmem : ∀ a : Fin V.rank × Fin V.rank, Z a.1 a.2 • glDer θ V (τ, a) φ ∈ SmFun θ V := fun a =>
    (SmFun θ V).smul_mem _ ((linOnSm_RderC (θ := θ) τ (Matrix.single a.1 a.2 1)).mem φ hs)
  refine (growthSob_sum_le Finset.univ _ hmem d N).trans ?_
  calc ∑ a : Fin V.rank × Fin V.rank, growthSob θ V d N (Z a.1 a.2 • glDer θ V (τ, a) φ)
      ≤ ∑ _a : Fin V.rank × Fin V.rank, B * growthSob θ V (d + 1) N φ := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [growthSob_smul]
        exact mul_le_mul' (hB a.1 a.2)
          (wordSum_letter_le (A := glDer θ V) (p := growthSize V N) d (τ, a) φ)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem growthSize_rTr_le (h : GA D V) (N : ℕ) (φ : GA D V → ℂ) :
    growthSize V N (rTr V h φ) ≤ ENNReal.ofReal (height V h) ^ N * growthSize V N φ := by
  obtain ⟨h1, -, -, hmul, -⟩ := height_laws V
  unfold growthSize
  refine iSup_le fun g => ?_
  have hgpos : 0 < height V g := lt_of_lt_of_le one_pos (h1 g)
  have hhpos : 0 < height V h := lt_of_lt_of_le one_pos (h1 h)
  have hghpos : 0 < height V (g * h) := lt_of_lt_of_le one_pos (h1 (g * h))
  have hq : 0 ≤ ‖φ (g * h)‖ / height V (g * h) ^ N := div_nonneg (norm_nonneg _) (pow_pos hghpos N).le
  have key : ‖rTr V h φ g‖ / height V g ^ N ≤ height V h ^ N * (‖φ (g * h)‖ / height V (g * h) ^ N) := by
    change ‖φ (g * h)‖ / height V g ^ N ≤ _
    rw [div_le_iff₀ (pow_pos hgpos N)]
    have hp : height V (g * h) ^ N ≤ (height V g * height V h) ^ N := pow_le_pow_left₀ hghpos.le (hmul g h) N
    calc ‖φ (g * h)‖ = ‖φ (g * h)‖ / height V (g * h) ^ N * height V (g * h) ^ N :=
          (div_mul_cancel₀ _ (pow_pos hghpos N).ne').symm
      _ ≤ ‖φ (g * h)‖ / height V (g * h) ^ N * (height V g * height V h) ^ N := mul_le_mul_of_nonneg_left hp hq
      _ = height V h ^ N * (‖φ (g * h)‖ / height V (g * h) ^ N) * height V g ^ N := by ring
  calc ENNReal.ofReal (‖rTr V h φ g‖ / height V g ^ N)
      ≤ ENNReal.ofReal (height V h ^ N * (‖φ (g * h)‖ / height V (g * h) ^ N)) := ENNReal.ofReal_le_ofReal key
    _ = ENNReal.ofReal (height V h) ^ N * ENNReal.ofReal (‖φ (g * h)‖ / height V (g * h) ^ N) := by
        rw [ENNReal.ofReal_mul (pow_pos hhpos N).le, ENNReal.ofReal_pow hhpos.le]
    _ ≤ ENNReal.ofReal (height V h) ^ N * ⨆ g', ENNReal.ofReal (‖φ g'‖ / height V g' ^ N) :=
        by gcongr; exact le_iSup (fun g' => ENNReal.ofReal (‖φ g'‖ / height V g' ^ N)) (g * h)

theorem exists_adAt_le (hθ : IsInfFam θ) (V : HSp D) : ∃ C : ℝ≥0, ∀ (h : GA D V) τ a b c d,
    ‖adAt θ h τ (Matrix.single a b 1) c d‖ₑ ≤ C * ENNReal.ofReal (height V h) ^ 2 := by
  obtain ⟨C, hC⟩ := normInf_le_height V hθ
  refine ⟨Real.toNNReal (C ^ 2), fun h τ a b c d => ?_⟩
  have hent : ∀ i j, ‖infMat D.sp.cm.sig V.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j‖ ≤
      C * height V h := by
    intro i j
    refine le_trans ?_ (hC h)
    calc ‖infMat D.sp.cm.sig V.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j‖
        ≤ ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ) h i j'‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j'‖) :=
          Finset.single_le_sum (f := fun j' => ‖infMat D.sp.cm.sig V.gram (θ τ) h i j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j'‖) (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ) h i' j'‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i' j'‖) :=
          Finset.single_le_sum (f := fun i' => ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ) h i' j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i' j'‖)) (fun _ _ => by positivity) (Finset.mem_univ i)
      _ ≤ ∑ τ', ∑ i', ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ') h i' j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ') h⁻¹ i' j'‖) :=
          Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ') h i' j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ') h⁻¹ i' j'‖)) (fun _ _ => by positivity) (Finset.mem_univ τ)
      _ = _ := rfl
  have hcomp : adAt θ h τ (Matrix.single a b 1) c d =
      infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a * infMat D.sp.cm.sig V.gram (θ τ) h b d := by
    simp [adAt, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have hx := hent c a
  have hy := hent b d
  have hx' : ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a‖ ≤ C * height V h := by
    linarith [norm_nonneg (infMat D.sp.cm.sig V.gram (θ τ) h c a)]
  have hy' : ‖infMat D.sp.cm.sig V.gram (θ τ) h b d‖ ≤ C * height V h := by
    linarith [norm_nonneg (infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ b d)]
  have hht : 0 ≤ height V h := le_trans zero_le_one ((height_laws V).1 h)
  have hreal : ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a‖ * ‖infMat D.sp.cm.sig V.gram (θ τ) h b d‖ ≤
      C ^ 2 * height V h ^ 2 := by
    calc _ ≤ (C * height V h) * (C * height V h) :=
          mul_le_mul hx' hy' (norm_nonneg _) ((norm_nonneg _).trans hx')
      _ = C ^ 2 * height V h ^ 2 := by ring
  rw [hcomp, ← ofReal_norm_eq_enorm, norm_mul]
  calc ENNReal.ofReal (‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a‖ * ‖infMat D.sp.cm.sig V.gram (θ τ) h b d‖)
      ≤ ENNReal.ofReal (C ^ 2 * height V h ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := by rw [ENNReal.ofReal_mul (sq_nonneg C), ENNReal.ofReal_pow hht]; rfl

private theorem rderC_rTr' (hθ : IsInfFam θ) (h : GA D V) {φ : GA D V → ℂ} (hs : φ ∈ SmFun θ V)
    (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ Z (rTr V h φ) = rTr V h (RderC θ V τ (adAt θ h τ Z) φ) := by
  obtain ⟨hX, hY⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  have hZ := (GlobalTheory.SmoothAutCheck.parts_sum V τ Z).symm
  set X := (1 / 2 : ℂ) • (Z + conjAt V τ Z) with hXdef
  set Y := (1 / (2 * Complex.I)) • (Z - conjAt V τ Z) with hYdef
  have hsum : adAt θ h τ Z = adAt θ h τ X + Complex.I • adAt θ h τ Y := by
    conv_lhs => rw [hZ]
    simp only [adAt, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hsum, RderC_add hθ hs, RderC_smul hθ hs,
    GlobalTheory.SmoothAutCheck.RderC_eq θ V τ (adAt_mem_lieAt hθ h hX),
    GlobalTheory.SmoothAutCheck.RderC_eq θ V τ (adAt_mem_lieAt hθ h hY)]
  change Rder θ V τ X (rTr V h φ) + Complex.I • Rder θ V τ Y (rTr V h φ) = _
  rw [Rder_rTr_adelic hθ h hX, Rder_rTr_adelic hθ h hY]
  rfl

theorem exists_growthSob_rTr_le (hθ : IsInfFam θ) (V : HSp D) (N d : ℕ) : ∃ C : ℝ≥0, ∀ h ∈ GinfC V, ∀ φ ∈ SmFun θ V,
    growthSob θ V d N (rTr V h φ) ≤ C * ENNReal.ofReal (height V h) ^ (N + 2 * d) * growthSob θ V d N φ := by
  obtain ⟨C₁, hC₁⟩ := exists_adAt_le hθ V
  induction d with
  | zero =>
    refine ⟨1, fun h _ φ _ => ?_⟩
    simpa [growthSob, wordSum_zero] using growthSize_rTr_le h N φ
  | succ d ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨1 + (Fintype.card (D.what₂.Tau × Fin V.rank × Fin V.rank) : ℝ≥0) * C *
      (Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0) * C₁, fun h hh φ hs => ?_⟩
    have hT : 1 ≤ ENNReal.ofReal (height V h) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal ((height_laws V).1 h)
    have hS0 : growthSize V N φ ≤ growthSob θ V (d + 1) N φ :=
      le_wordSum (A := glDer θ V) (p := growthSize V N) (l := []) (Nat.zero_le _) φ
    have hterm : ∀ a : D.what₂.Tau × Fin V.rank × Fin V.rank,
        growthSob θ V d N (glDer θ V a (rTr V h φ)) ≤
          C * ENNReal.ofReal (height V h) ^ (N + 2 * d) *
            ((Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0∞) *
              ((C₁ * ENNReal.ofReal (height V h) ^ 2) * growthSob θ V (d + 1) N φ)) := by
      intro a
      have e : glDer θ V a (rTr V h φ) =
          rTr V h (RderC θ V a.1 (adAt θ h a.1 (Matrix.single a.2.1 a.2.2 1)) φ) :=
        rderC_rTr' hθ h hs a.1 _
      rw [e]
      refine (hC h hh _ ((linOnSm_RderC (θ := θ) a.1 _).mem φ hs)).trans ?_
      gcongr
      exact growthSob_RderC_le hθ hs a.1 (fun b c => hC₁ h a.1 a.2.1 a.2.2 b c) d N
    have hpow : ENNReal.ofReal (height V h) ^ N ≤ ENNReal.ofReal (height V h) ^ (N + 2 * (d + 1)) :=
      pow_le_pow_right₀ hT (by omega)
    have e0 : growthSob θ V (d + 1) N (rTr V h φ) =
        growthSize V N (rTr V h φ) + ∑ a, growthSob θ V d N (glDer θ V a (rTr V h φ)) :=
      wordSum_succ _ _ _ _
    rw [e0]
    calc growthSize V N (rTr V h φ) + ∑ a, growthSob θ V d N (glDer θ V a (rTr V h φ))
        ≤ ENNReal.ofReal (height V h) ^ (N + 2 * (d + 1)) * growthSob θ V (d + 1) N φ +
          ∑ _a : D.what₂.Tau × Fin V.rank × Fin V.rank, C * ENNReal.ofReal (height V h) ^ (N + 2 * d) *
            ((Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0∞) *
              ((C₁ * ENNReal.ofReal (height V h) ^ 2) * growthSob θ V (d + 1) N φ)) :=
          add_le_add ((growthSize_rTr_le h N φ).trans (mul_le_mul' hpow hS0))
            (Finset.sum_le_sum fun a _ => hterm a)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          push_cast
          ring

theorem growthSob_rTr_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (d N : ℕ), ∃ (C : NNReal) (m : ℕ),
    ∀ h ∈ GinfC V, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V d N (rTr V h φ) ≤
      (C : ENNReal) * ENNReal.ofReal (GlobalTheory.Grow.height V h ^ m) * GlobalTheory.Size.growthSob θ V d N φ := by
  intro D θ hθ V d N
  obtain ⟨C, hC⟩ := exists_growthSob_rTr_le hθ V N d
  refine ⟨C, N + 2 * d, fun h hh φ hφ => ?_⟩
  rw [ENNReal.ofReal_pow (le_trans zero_le_one ((height_laws V).1 h))]
  exact hC h hh φ hφ

end GlobalTheory.Size.Translate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.LFun.SatBoundGL

private theorem mem_adicCompletionIntegers_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E) :
    letI := GlobalTheory.LocalData.complRel w
    x ∈ Valuation.integer (ValuativeRel.valuation (w.adicCompletion E)) ↔ x ∈ w.adicCompletionIntegers E := by
  letI := GlobalTheory.LocalData.complRel w
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [Valuation.mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers]
  simpa using h x 1

open ValuativeRel in

theorem resCard_completion {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    GlobalTheory.SplitWeil.resCard (w.adicCompletion E) = Ideal.absNorm w.asIdeal := by
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w

  let e : Valuation.integer (ValuativeRel.valuation (w.adicCompletion E)) ≃+* w.adicCompletionIntegers E :=
    { toFun := fun x => ⟨x.1, (mem_adicCompletionIntegers_iff w x.1).1 x.2⟩
      invFun := fun y => ⟨y.1, (mem_adicCompletionIntegers_iff w y.1).2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  unfold GlobalTheory.SplitWeil.resCard
  rw [Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv, Formalism.UG.P.tjcosets_card_residue w]
  rfl

theorem norm_le_of_hasSatGL : GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.SatakeTrivialBound → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (B : Multiset ℂˣ), GlobalTheory.LGrp.IsIrrSmooth ρ → GlobalTheory.LGrp.IsUnitarisable ρ → HasSatGL w ρ B → ∀ b ∈ B, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  intro hT E _ _ w n V _ _ ρ B hirr hun hsat b hb
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  obtain ⟨hsph, hvec⟩ := hsat

  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hsph
  have hG : LGrp.HasSatakeGL ρ B := GlobalTheory.LFun.SatCompare.hasSatakeGL_of_isSatVecGL hirr (hvec x hx hx0)
  obtain ⟨α, hαB, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ ρ B).mp hG
  have hR := hT (w.adicCompletion E) n V ρ α hirr.1 hirr.2 ((GlobalTheory.LGrp.isUnitarisable_iff ρ).mp hun) ?_ hα
  · rw [← hαB] at hb
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hb
    have hi := (hR i).2
    rwa [resCard_completion] at hi
  · unfold GlobalTheory.SmGL.IsSpherical
    exact (GlobalTheory.LGrp.isSpherical_iff ρ _).mp hG.2

end GlobalTheory.LFun.SatBoundGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPlaceModelLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

open GlobalTheory.SplitLinear GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove GlobalTheory.VecInv in
open GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm in

theorem om_placeModel_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsWeilDatumO ψ S T χS χT om → IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ (v : FinPl D) (e a : AE D), IsSplitIdem D e → e + cA D e = idem D (.inl v) → (a = e ∨ a = cA D e) → ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → ∀ g h, SuppAt e S g → SuppAt e T h → ∀ x y, IsDetAt e S g x → IsDetAt e T h y → ∃ r : ℝ, 0 < r ∧ ∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → om (g, h) (Tm Φ) = ((r : ℂ) * ((splitFacO χS χT x y : Circle) : ℂ)) • Tm fun t => Φ (actO S T g⁻¹ h⁻¹ t) := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ hW hB v e a he _ ha Tm hTm g h hg hh x y hx hy
  have orth : ∀ b : AE D, IsSplitIdem D b → GlobalTheory.PlaceModelSum.IsOrthSum b := fun b hb =>
    ⟨Unit, {()}, fun _ => b, fun _ _ => hb, fun _ _ _ _ h => absurd rfl h, (Finset.sum_singleton (fun _ => b) ()).symm⟩
  have ho := orth e he
  rcases ha with ha | ha
  · rw [ha] at hTm ⊢
    refine ⟨modFac S T x y, modFac_pos S T x y, fun Φ hΦ => ?_⟩
    rw [law_orth hW hB.2.2.1 hB.2.2.2.1 ho he.2.1 (base_theta hB) hB.2.2.2.2.2.lat one_ne_zero hTm hg hh hx hy Φ hΦ,
      fac, mul_comm]
  · rw [ha] at hTm ⊢
    have ho' := ho.conj
    have sc : ∀ (V : HSp D) (k : GA D V), SuppAt e V k → SuppAt (cA D e) V k := fun V k hk i j => by
      rw [GlobalTheory.SplitOnto.cA_cA, add_comm]; exact hk i j
    have dx := det_conj ho'.idem hx
    have dy := det_conj ho'.idem hy
    refine ⟨modFac S T (detAt _ ho'.idem S g) (detAt _ ho'.idem T h), modFac_pos S T _ _, fun Φ hΦ => ?_⟩
    rw [law_orth hW hB.2.2.1 hB.2.2.2.1 ho' (by rw [GlobalTheory.SplitOnto.cA_cA, mul_comm, he.2.1]) (base_theta hB)
      hB.2.2.2.2.2.lat one_ne_zero hTm (sc S g hg) (sc T h hh) (isDetAt_detAt _ ho'.idem S g)
      (isDetAt_detAt _ ho'.idem T h) Φ hΦ, fac, mul_comm, splitFacO, splitFacO,
      GlobalTheory.SplitDetCharacter.char_eq_of_mul_conj hW.resT _ _ dx, GlobalTheory.SplitDetCharacter.char_eq_of_mul_conj hW.resS _ _ dy]

end GlobalTheory.PlaceTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowerBasisCoordsIsTorusHermitianIsometryStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerBasisCoords_isTorusHermitianIsometry : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ) (P : PPol σ r) (k : Type) [CommRing k] [Algebra F k], IsIsom P k (GlobalTheory.TrUnitLat.gramOne P) 1 (GlobalTheory.TrUnitLat.coordEquiv P k) := by
  first | exact @GlobalTheory.TrUnitLat.isIsom_coordEquiv | exact GlobalTheory.TrUnitLat.isIsom_coordEquiv | (intros; apply GlobalTheory.TrUnitLat.isIsom_coordEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PseudocoefficientTraceVanishesStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudocoefficient_trace_vanishes : GlobalTheory.Published.HarishChandraCharacters → ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (δ : UJ ε →* (X →L[ℂ] X)) (f : UJ ε → ℂ), IsPseudoCoeff (ujMat ε) μ δ f → ∀ I : IndModule ε, I.a ≠ 0 → HasTrace (repOp I.rep μ f) 0 := by
  first | exact @GlobalTheory.IndTraceZero.hasTrace_indModule_eq_zero | exact GlobalTheory.IndTraceZero.hasTrace_indModule_eq_zero | (intros; apply GlobalTheory.IndTraceZero.hasTrace_indModule_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIntertwinerContractionValuesKFiniteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realIntertwinerContraction_values_kFinite : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) (aS aT : ℚ) (A : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ), SemiW M M' τ aS aT A → (∀ φ y, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) (A φ y)) ∧ ∀ φ u, ∃ b : M'.H τ, Formalism.MainNotions.S.IsKFin (M'.ε τ) (M'.σ τ) b ∧ ∀ y : M'.sm τ, ⟪u, A φ y⟫_ℂ = ⟪b, (y : M'.H τ)⟫_ℂ := by
  first | exact @GlobalTheory.Chain.RealLineKFin.kfin | exact GlobalTheory.Chain.RealLineKFin.kfin | (intros; apply GlobalTheory.Chain.RealLineKFin.kfin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceDeterminantPowerMulNeZeroExp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ConjHol

theorem detPow_mul_ne_zero_exp : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (m : D.what₂.Tau → ℤ), (∀ a b, detPow θ V m (a * b) = detPow θ V m a * detPow θ V m b) ∧ (∀ a, detPow θ V m a ≠ 0) ∧ (∀ Y : GlobalTheory.SmoothForms.LieN V, detPow θ V m (GlobalTheory.SmoothForms.expInf θ V Y) = cexp (GlobalTheory.AdSpan.ConjHol.trLin V m Y)) := by
  intro D θ hθ V m
  have R : GlobalTheory.SmoothForms.RealPoints θ V := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  have hd : ∀ a, detPow θ V m a = ∏ ρ, (infMat D.sp.cm.sig V.gram (θ ρ) a).det ^ (m ρ) := fun a => rfl
  refine ⟨fun a b => ?_, fun a => ?_, fun Y => ?_⟩
  · rw [hd, hd, hd, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [R.2.2.2.1, det_mul, mul_zpow]
  · rw [hd]
    refine Finset.prod_ne_zero_iff.2 fun ρ _ => zpow_ne_zero _ fun h0 => ?_
    have h : (infMat D.sp.cm.sig V.gram (θ ρ) a)ᴴ * gramAt D V ρ * infMat D.sp.cm.sig V.gram (θ ρ) a = gramAt D V ρ :=
      GlobalTheory.RealLift.archM_mem hθ V a ρ
    have h2 := congrArg det h
    rw [det_mul, h0, mul_zero] at h2
    exact (R.1 ρ).2.ne_zero h2.symm
  · rw [hd]
    change _ = cexp (∑ ρ, (m ρ : ℂ) * trace (Y ρ).1)
    rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [(GlobalTheory.SmoothForms.isExpFam_expInf R Y).2 ρ, Formalism.MainNotions.DIV.Inh.det_exp, Complex.exp_int_mul]

end GlobalTheory.AdSpan.ConjHol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceGroupsActUnitarilyWeaklyOnThetaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceGroups_act_unitarily_weakly_on_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → ∀ (frS : Mn S.rank) (εS : Fin S.rank → Bool) (frT : Mn T.rank) (εT : Fin T.rank → Bool) (aS aT : ℚ) (pt : LPol T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)), (∀ P, IsThetaFunO ψ S T (pt P)) → LieAt ψ θ τ ω εS frS εT frT aS aT pt → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ Θ, L2UnitaryRepresentationData (gramAt D S τ) (actSrc θ ω τ) pt (ipTh μ 𝓕) Θ ∧ L2UnitaryRepresentationData (gramAt D T τ) (actTgt θ ω τ) pt (ipTh μ 𝓕) Θ := by
  first | exact @GlobalTheory.ThetaL2InnerProduct.exists_l2_unitary_theta_of_fundamentalDomain | exact GlobalTheory.ThetaL2InnerProduct.exists_l2_unitary_theta_of_fundamentalDomain | (intros; apply GlobalTheory.ThetaL2InnerProduct.exists_l2_unitary_theta_of_fundamentalDomain <;> assumption)
end

