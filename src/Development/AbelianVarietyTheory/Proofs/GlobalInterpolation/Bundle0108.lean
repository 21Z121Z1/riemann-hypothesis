import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0100
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0098
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrivialClassShortInterval
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryLieVolumeBallSplitBasisVector
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0101
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowLStarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_b_add_Sc_add_etaSz_add_div_lt_lStar : SzRow (fun C D L => (L.sc.b' + L.Sc + L.etaSz + L.sc.b / lStar L < lStar L) ∧ (2 * L.etaSz + D.R.t + 8 * L.sc.b / lStar L + 7 < lStar L)) := by
  first | exact @GlobalTheory.EX.szRow_lStar | exact GlobalTheory.EX.szRow_lStar | (intros; apply GlobalTheory.EX.szRow_lStar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNodeGapStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_node_bounds_le_h0 : SzRow (fun C D L => (12 * L.sc.b / lStar L + 2 * D.R.t + 8 ≤ h0 L ∧ (D.R.k : ℝ) * D.R.t * L.sc.L ≤ h0 L ∧ C.P.Ch0r * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L ≤ h0 L ∧ ((D.R.N D.R.m : ℝ) * D.R.f * L.sc.L) ^ C.P.CCount ≤ h0 L ∧ 4 * (D.R.N D.R.m : ℝ) ^ 3 + 2 * D.R.t + 6 ≤ h0 L ∧ C.P.Ch0k * D.R.k * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) ≤ h0 L ∧ 2 * (Mrt D : ℝ) ^ 3 + D.R.t + 3 ≤ h0 L ∧ 120 * (D.R.r : ℝ) * (qSig D : ℝ) ^ ((3 : ℝ) / 2) ≤ h0 L ∧ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ h0 L ∧ 16 * (qSig D : ℝ) * D.R.N D.R.m ≤ h0 L)) := by
  first | exact @GlobalTheory.EX.szRow_nodeGap | exact GlobalTheory.EX.szRow_nodeGap | (intros; apply GlobalTheory.EX.szRow_nodeGap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowPpDimToLeRpowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_PP_and_dim_and_TOv_le_x_rpow_Ct : SzRow (fun C D L => ((C.T.CP * zBase L ^ C.T.eP) ≤ L.sc.x ^ L.Ct) ∧ (((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ≤ L.sc.x ^ L.Ct) ∧ (((TOv L.sc : ℕ) : ℝ) ≤ L.sc.x ^ L.Ct)) := by
  first | exact @GlobalTheory.EX.szRow_pp_dim_to_le_rpow | exact GlobalTheory.EX.szRow_pp_dim_to_le_rpow | (intros; apply GlobalTheory.EX.szRow_pp_dim_to_le_rpow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowTOLowerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_PP_pow_mul_dim_pow_div_le_TOv : SzRow (fun C D L => ((C.T.CP * zBase L ^ C.T.eP) ^ 4 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ C.T.Cp / ((D.R.m : ℝ) * L.de2) ≤ ((TOv L.sc : ℕ) : ℝ)) ∧ (((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) * D.R.k / D.R.m ≤ ((TOv L.sc : ℕ) : ℝ))) := by
  first | exact @GlobalTheory.EX.szRow_TO_lower | exact GlobalTheory.EX.szRow_TO_lower | (intros; apply GlobalTheory.EX.szRow_TO_lower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowTypePrimesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_exists_Y_bounds_host_g_mem_Icc_Y_two_mul_Y : SzRow (fun C D L => (∃ Y : ℝ, ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ Y ∧ (D.R.N D.R.m : ℝ) ^ 4 * (condE D : ℝ) ^ C.P.CY ≤ Y ^ ((1 : ℝ) / 4) ∧ Real.log Y ≤ C.P.CYL * L.sc.L ∧ ∀ i, Y ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ 2 * Y)) := by
  first | exact @GlobalTheory.EX.szRow_typePrimes | exact GlobalTheory.EX.szRow_typePrimes | (intros; apply GlobalTheory.EX.szRow_typePrimes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrivialClassShortIntervalStatement
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lam_zero_sum_shortInterval_ge : ∃ A c c' : ℝ, 0 < A ∧ 0 < c ∧ 0 < c' ∧ ∀ (𝓕 : LFam) (X h : ℝ), 1 ≤ X → Real.log 𝓕.B ≤ c * Real.sqrt (Real.log X) → Real.exp (-c * Real.sqrt (Real.log X)) ≤ h → h ≤ 1 → c' * h * X / 𝓕.B ^ A ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X * (1 + h)⌋₊, 𝓕.lam 0 n := by
  first | exact @GlobalTheory.Hk.ShortInt.trivialClass_shortInterval | exact GlobalTheory.Hk.ShortInt.trivialClass_shortInterval | (intros; apply GlobalTheory.Hk.ShortInt.trivialClass_shortInterval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryExpLieBallComparableEntryGauge
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

namespace GlobalTheory.ExpBallCompare

variable {P Q : ℕ}

theorem entry_le_l1 (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (i j) : ‖Z i j‖ ≤ l1 Z :=
  (Finset.single_le_sum (f := fun j => ‖Z i j‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, ‖Z i j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))

theorem l1_add_le (Z W : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    l1 (Z + W) ≤ l1 Z + l1 W := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => norm_add_le _ _

theorem l1_neg (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) : l1 (-Z) = l1 Z := by
  simp [l1]

theorem exists_l1_ball {S : Set (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} (hS : S ∈ 𝓝 0) :
    ∃ δ > 0, ∀ Z, l1 Z < δ → Z ∈ S := by
  have hS' : S ∈ 𝓝 (0 : (Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ) := hS
  obtain ⟨δ, hδ, h⟩ := Metric.mem_nhds_iff.1 hS'
  refine ⟨δ, hδ, fun Z hZ => h ?_⟩
  exact mem_ball_zero_iff.2 ((pi_norm_lt_iff hδ).2 fun i => (pi_norm_lt_iff hδ).2 fun j =>
    (entry_le_l1 Z i j).trans_lt hZ)

theorem exp_isLittleO (A : Type) [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] :
    (fun Z : A => NormedSpace.exp Z - 1 - Z) =o[𝓝 0] fun Z => Z := by
  have h := (hasFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := A)).isLittleO
  simpa using h

theorem eventually_l1_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ in 𝓝 0,
      l1 (NormedSpace.exp Z - 1 - Z) ≤ ε * l1 Z := by
  let : NormedRing (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℂ (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := Matrix.linftyOpNormedAlgebra
  have : CompleteSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := FiniteDimensional.complete ℂ _
  have hrow : ∀ (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i, ∑ j, ‖Z i j‖ ≤ ‖Z‖ := by
    intro Z i
    rw [Matrix.linfty_opNorm_def]
    have := Finset.le_sup (f := fun i => ∑ j, ‖Z i j‖₊) (Finset.mem_univ i)
    have h2 := NNReal.coe_le_coe.2 this
    simpa using h2
  have h1 : ∀ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, l1 Z ≤ (P + Q : ℝ) * ‖Z‖ := by
    intro Z
    have := Finset.sum_le_card_nsmul Finset.univ (fun i => ∑ j, ‖Z i j‖) ‖Z‖ fun i _ => hrow Z i
    simpa [l1] using this
  have h2 : ∀ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, ‖Z‖ ≤ l1 Z := by
    intro Z
    rw [Matrix.linfty_opNorm_def]
    have : (Finset.univ.sup fun i => ∑ j, ‖Z i j‖₊) ≤ ∑ i, ∑ j, ‖Z i j‖₊ :=
      Finset.sup_le fun i _ => Finset.single_le_sum (f := fun i => ∑ j, ‖Z i j‖₊)
        (fun _ _ => by positivity) (Finset.mem_univ i)
    have h2 := NNReal.coe_le_coe.2 this
    simpa [l1] using h2
  have hN : (0 : ℝ) < P + Q + 1 := by positivity
  have h3 := (exp_isLittleO (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)).def (div_pos hε hN)
  filter_upwards [h3] with Z hZ
  calc l1 (NormedSpace.exp Z - 1 - Z) ≤ (P + Q : ℝ) * ‖NormedSpace.exp Z - 1 - Z‖ := h1 _
    _ ≤ (P + Q + 1 : ℝ) * (ε / (P + Q + 1) * ‖Z‖) :=
      mul_le_mul (by linarith) hZ (norm_nonneg _) hN.le
    _ = ε * ‖Z‖ := by field_simp
    _ ≤ ε * l1 Z := mul_le_mul_of_nonneg_left (h2 Z) hε.le

theorem exists_l1_exp {t : ℝ} (ht : 1 < t) : ∃ δ > 0,
    ∀ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, l1 Z < δ →
      l1 (NormedSpace.exp Z - 1) ≤ t * l1 Z ∧ l1 Z ≤ t * l1 (NormedSpace.exp Z - 1) := by
  have ht0 : 0 < t := by linarith
  have hε : 0 < 1 - t⁻¹ := sub_pos.2 (inv_lt_one_of_one_lt₀ ht)
  obtain ⟨δ, hδ, h⟩ := exists_l1_ball
    ((eventually_l1_exp (P := P) (Q := Q) hε).and (eventually_l1_exp (sub_pos.2 ht)))
  refine ⟨δ, hδ, fun Z hZ => ?_⟩
  obtain ⟨h1, h2⟩ := h Z hZ
  constructor
  · have := l1_add_le (NormedSpace.exp Z - 1 - Z) Z
    rw [sub_add_cancel] at this
    linarith
  · have := l1_add_le (NormedSpace.exp Z - 1) (-(NormedSpace.exp Z - 1 - Z))
    rw [l1_neg, ← sub_eq_add_neg, sub_sub_cancel] at this
    have h3 : t⁻¹ * l1 Z ≤ l1 (NormedSpace.exp Z - 1) := by linarith
    exact (inv_mul_le_iff₀ ht0).1 h3

theorem exists_gauge_ball {S : Set (UpqT P Q)} (hS : S ∈ 𝓝 (1 : UpqT P Q)) :
    ∃ δ > 0, ∀ g, gauge g < δ → g ∈ S := by
  rw [GlobalTheory.UpqTopology.isClosedEmbedding_mat.isInducing.nhds_eq_comap] at hS
  obtain ⟨T, hT, hTS⟩ := hS
  have h1 : UpqT.mat (1 : UpqT P Q) = 1 := rfl
  have c : Continuous fun Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ => Z + 1 :=
    continuous_id.add continuous_const
  obtain ⟨δ, hδ, h⟩ := exists_l1_ball (c.continuousAt.preimage_mem_nhds (x := 0) (t := T)
    (by rw [zero_add, ← h1]; exact hT))
  refine ⟨δ, hδ, fun g hg => hTS ?_⟩
  simpa using h _ hg

theorem expBall_compare : ∀ (P Q : ℕ) (t : ℝ), 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), expBall P Q (t⁻¹ * r) ⊆ {g : UpqT P Q | gauge g < r} ∧ {g : UpqT P Q | gauge g < r} ⊆ expBall P Q (t * r) := by
  intro P Q t ht
  have ht0 : 0 < t := by linarith
  obtain ⟨δ, hδ, h⟩ := exists_l1_exp (P := P) (Q := Q) ht
  obtain ⟨η, hη, h'⟩ := exists_gauge_ball (GlobalTheory.ExpBallNhds.exp_ballU_mem_nhds P Q δ hδ)
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ hη)] with r hr
  obtain ⟨hr0, hr1⟩ := hr
  have hrδ : r < δ := hr1.trans_le (min_le_left _ _)
  have hrη : r < η := hr1.trans_le (min_le_right _ _)
  constructor
  · rintro g ⟨X, hX, hg⟩
    have hX' : l1 (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) < t⁻¹ * r := hX
    have h1 : t⁻¹ * r ≤ r := mul_le_of_le_one_left hr0.le (inv_lt_one_of_one_lt₀ ht).le
    have h2 := (h X (by linarith)).1
    have h3 := (lt_inv_mul_iff₀ ht0).1 hX'
    show l1 (UpqT.mat g - 1) < r
    rw [hg]
    linarith
  · intro g hg
    have hg' : l1 (UpqT.mat g - 1) < r := hg
    obtain ⟨X, hX, hgX⟩ := h' g (lt_trans hg hrη)
    refine ⟨X, ?_, hgX⟩
    have h2 := (h X hX).2
    rw [hgX] at hg'
    exact h2.trans_lt (mul_lt_mul_of_pos_left hg' ht0)

end GlobalTheory.ExpBallCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryLieVolumeBallSplitBasisVectorStatement
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryLie_volume_ball_split_basis_vector : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)), SignCompat e → ∀ (lam : Measure (lieU P Q)) (lam' : Measure (lieU P' Q')), IsOmegaLeb lam → IsOmegaLeb lam' → ∀ r : ℝ, lam (ballU P Q r) = (2 : ℝ≥0∞) ^ (P' + Q') * ((volume : Measure (ℝ × Sp P' Q')).prod lam') {p | tanGauge p.1 + l1 (p.2 : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) < r} := by
  first | exact @GlobalTheory.OmegaSplit.omega_split | exact GlobalTheory.OmegaSplit.omega_split | (intros; apply GlobalTheory.OmegaSplit.omega_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UopIsExtStatement
section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (v : X.A.vT) (φ : Fn X i) (Φ : M.Pt → M.Val), M.IsExt φ Φ → M.IsExt (Uop X i v φ) (fun p => ∑ᶠ p₁ ∈ {p₁ | M.Inc v p p₁}, Φ p₁) := by
  first | exact @GlobalTheory.LvT.uop_isExt | exact GlobalTheory.LvT.uop_isExt | (intros; apply GlobalTheory.LvT.uop_isExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightRequirementOfValidStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_requirement_of_valid : ∀ (C : FC) (cD ch : ℝ) (p : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), Std C → Val C cD ch p.L → p.From H a b c u0 → CanonInst p.ta.Gx → (∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) → WOK p.L.sc cD ch C.GK H a b → Formalism.MainNotions.AuxBlock8.WReq p.ta.Gx C.GK (G.aL p.L) (G.bL p.L) := by
  first | exact @GlobalTheory.EX.wreq_of_wok | exact GlobalTheory.EX.wreq_of_wok | (intros; apply GlobalTheory.EX.wreq_of_wok <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylHeisenbergOperatorCalculusRationalStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylHeisenbergOperator_calculus_rational : ∀ (X : Fields) (A : Amb X) (a b : ℕ), (∀ (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ), Wx A x (Wx A y F) = fun z => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A x y : ℂ)) * Wx A (x + y) F z) ∧ (∀ (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ), Wx A x (Wx A y F) = fun z => brkE A y x * Wx A y (Wx A x F) z) ∧ (∀ x y : HomE X.E a b, imH A x y = coc A x y - coc A y x) ∧ (∀ x y z : HomE X.E a b, coc A (x + y) z = coc A x z + coc A y z ∧ coc A x (y + z) = coc A x y + coc A x z ∧ imH A (x + y) z = imH A x z + imH A y z ∧ imH A x (y + z) = imH A x y + imH A x z) ∧ (∀ y t : HomE X.E a b, brkE A y t = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (imH A t y : ℂ))) ∧ (∀ y t : HomE X.E a b, brkE A y t = 1 ↔ ∃ n : ℤ, imH A t y = n) ∧ (∀ (x : HomE X.E a b) (F : VCx X.Tau a b → ℂ), (∀ k : ℕ, ContDiff ℂ k F) → ∀ k : ℕ, ContDiff ℂ k (Wx A x F)) ∧ (∀ (κ : Type) (T : Finset κ) (c : κ → ℂ) (F : κ → VCx X.Tau a b → ℂ), (∀ i ∈ T, ∀ k : ℕ, ContDiff ℂ k (F i)) → ∀ m, jetC A.cD (fun z => ∑ i ∈ T, c i * F i z) m = ∑ i ∈ T, c i * jetC A.cD (F i) m) := by
  first | exact @GlobalTheory.MomT.Heis.calculus | exact GlobalTheory.MomT.Heis.calculus | (intros; apply GlobalTheory.MomT.Heis.calculus <;> assumption)
end

