import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0047
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0046
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
import Formalism.PeriodIntegrals.Bundle0015
import Formalism.PeriodIntegrals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0051
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HilbertSchmidtNormSubmulInvGeOneStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSchmidt_norm_submul_inv_ge_one : Formalism.FourierDecayAlt.ThreeDimData.NormInv := by
  first | exact @GlobalTheory.BesselNorm.hilbertSchmidt_normInv | exact GlobalTheory.BesselNorm.hilbertSchmidt_normInv | (intros; apply GlobalTheory.BesselNorm.hilbertSchmidt_normInv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepDualStandardUnitaryRepStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFRep_dual_standard_unitaryRep : ∀ (k r : ℕ), IsFRep (k := k) (r := r) dualM (Formalism.QuantumDeterminants.Hpk k r) 1 := by
  first | exact @GlobalTheory.isFRep_dualM | exact GlobalTheory.isFRep_dualM | (intros; apply GlobalTheory.isFRep_dualM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotentStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent : ∀ (k r : ℕ) (μ : Measure (Formalism.QuantumDeterminants.Mt k r)), (PI.BesselPeriodGGP.IsHaarOn (GG k r) μ ↔ B.IsHaarOn (GG k r) μ) ∧ (PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ ↔ B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ) ∧ ∀ z, Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → 1 ≤ k → (PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μ ↔ B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μ) := by
  first | exact @GlobalTheory.HaarNotions.isHaarOn_iff_groups | exact GlobalTheory.HaarNotions.isHaarOn_iff_groups | (intros; apply GlobalTheory.HaarNotions.isHaarOn_iff_groups <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.KFiniteDerivativesFiniteSpan
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.UnitBoxWords

open PI.UpqRep GlobalTheory.DerivedAction

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}

def lieSubspace (k r : ℕ) : Submodule ℝ (Mx k r) where
  carrier := {X | InLieHpk k r X}
  add_mem' := fun {X Y} hX hY => by
    simp only [Set.mem_setOf_eq, InLieHpk] at *
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  zero_mem' := by simp [InLieHpk]
  smul_mem' := fun c X hX => by
    simp only [Set.mem_setOf_eq, InLieHpk] at *
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

theorem exists_box_generators (k r : ℕ) : ∃ (J : Type) (_ : Fintype J) (Z : J → Mx k r),
    (∀ j, InLieHpk k r (Z j)) ∧ ∀ Y, B.unitLie k r Y → ∃ c : J → ℝ, (∀ j, |c j| ≤ 1) ∧ Y = ∑ j, c j • Z j := by
  obtain ⟨P, hP⟩ := (lieSubspace k r).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  let n := Fin (2 * r + k + 1)
  let E : (n × n) ⊕ (n × n) → Mx k r :=
    Sum.elim (fun p => Matrix.single p.1 p.2 1) (fun p => Matrix.single p.1 p.2 Complex.I)
  refine ⟨(n × n) ⊕ (n × n), inferInstance, fun j => (P (E j)).1, fun j => (P (E j)).2, fun Y hY => ?_⟩
  let c : (n × n) ⊕ (n × n) → ℝ := Sum.elim (fun p => (Y p.1 p.2).re) (fun p => (Y p.1 p.2).im)
  refine ⟨c, ?_, ?_⟩
  · rintro (p | p)
    · exact (Complex.abs_re_le_norm _).trans (hY.2 _ _)
    · exact (Complex.abs_im_le_norm _).trans (hY.2 _ _)
  · have h1 : Y = ∑ j, c j • E j := by
      rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib, Fintype.sum_prod_type]
      conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [c, E, Sum.elim_inl, Sum.elim_inr, Matrix.smul_single, ← Matrix.single_add]
      congr 1
      simp [Complex.real_smul]
    have hYL : Y ∈ lieSubspace k r := hY.1
    have h2 : (P Y).1 = Y := by
      have := LinearMap.congr_fun hP ⟨Y, hYL⟩
      exact congrArg Subtype.val this
    calc Y = (P Y).1 := h2.symm
      _ = (P (∑ j, c j • E j)).1 := by rw [← h1]
      _ = _ := by simp [map_sum]

theorem dsig_sum_letter {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    {J : Type} [Fintype J] {Z : J → Mx k r} (hZ : ∀ j, InLieHpk k r (Z j)) (c : J → ℝ) {v : H}
    (hv : v ∈ smoothVecs (k := k) (r := r) σ) :
    dsig (k := k) (r := r) σ (∑ j, c j • Z j) v = ∑ j, (c j : ℂ) • dsig (k := k) (r := r) σ (Z j) v := by
  obtain ⟨L, hL⟩ := exists_lin hv
  have hm : (∑ j, c j • Z j) ∈ lieSubspace k r :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hZ j)
  rw [(hL _ hm).1, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, (hL _ (hZ j)).1, Complex.coe_smul]

theorem dsig_sum_vec (R : Rep k r) {X : Mx k r} (hX : InLieHpk k r X) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    {v : ι → R.H} (hv : ∀ i, v i ∈ R.sm) :
    dsig (k := k) (r := r) R.σ X (∑ i ∈ s, c i • v i) = ∑ i ∈ s, c i • dsig (k := k) (r := r) R.σ X (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dsig_zero]
  | insert a s ha ih =>
    have h1 : c a • v a ∈ R.smSub := R.smSub.smul_mem _ (hv a)
    have h2 : ∑ i ∈ s, c i • v i ∈ R.smSub := R.smSub.sum_mem fun i _ => R.smSub.smul_mem _ (hv i)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, dsig_add hX h1 h2, dsig_smul hX _ (hv a), ih]

theorem box_words_fintype (hK : PI.KFinSmooth) (R : Rep k r) (hR : R.IsDS ε mu) {x : R.H} (hx : x ∈ R.TK) (m : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (xs : ι → R.H), (∀ i, xs i ∈ R.TK) ∧ ∀ a : List (Mx k r),
      (∀ Y ∈ a, B.unitLie k r Y) → a.length ≤ m → ∃ co : ι → ℝ, (∀ i, |co i| ≤ 1) ∧
        dsigW (k := k) (r := r) R.σ a x = ∑ i, (co i : ℂ) • xs i := by
  obtain ⟨J, _, Z, hZ, hbox⟩ := exists_box_generators k r
  have h0 : InLieHpk k r (0 : Mx k r) := (lieSubspace k r).zero_mem
  induction m with
  | zero =>
    refine ⟨Unit, inferInstance, fun _ => x, fun _ => hx, fun a _ hl => ⟨fun _ => 1, by simp, ?_⟩⟩
    obtain rfl : a = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)
    simp [dsigW]
  | succ m ih =>
    obtain ⟨ι, _, xs, hxs, h⟩ := ih
    refine ⟨Unit ⊕ (J × ι), inferInstance,
      Sum.elim (fun _ => x) (fun p => dsig (k := k) (r := r) R.σ (Z p.1) (xs p.2)), ?_, ?_⟩
    · rintro (p | p)
      · exact hx
      · exact (dsig_TK hK R hR (hZ p.1) _ (hxs p.2)).2
    · intro a ha hl
      cases a with
      | nil =>
        refine ⟨Sum.elim (fun _ => 1) (fun _ => 0), ?_, ?_⟩
        · rintro (p | p) <;> simp
        · simp [dsigW, Fintype.sum_sum_type]
      | cons Y a =>
        have hY := ha Y (by simp)
        obtain ⟨co, hco, e⟩ := h a (fun Y hY => ha Y (by simp [hY])) (by simpa using hl)
        obtain ⟨c, hc, eY⟩ := hbox Y hY
        have hsm : ∀ i, xs i ∈ R.sm := fun i => (dsig_TK hK R hR h0 _ (hxs i)).1
        refine ⟨Sum.elim (fun _ => 0) (fun p => co p.2 * c p.1), ?_, ?_⟩
        · rintro (p | p)
          · simp
          · simp only [Sum.elim_inr, abs_mul]
            exact mul_le_one₀ (hco _) (abs_nonneg _) (hc _)
        · have hYL : InLieHpk k r Y := hY.1
          show dsig (k := k) (r := r) R.σ Y (dsigW (k := k) (r := r) R.σ a x) = _
          rw [e, dsig_sum_vec R hYL _ _ hsm, Fintype.sum_sum_type, Fintype.sum_prod_type_right]
          simp only [Sum.elim_inl, Sum.elim_inr, Complex.ofReal_zero, zero_smul, Finset.sum_const_zero, zero_add]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [eY, dsig_sum_letter hZ c (hsm i), Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_smul, Complex.ofReal_mul]

theorem box_words : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ x ∈ R.TK, ∀ m : ℕ, ∃ (M : ℕ) (xs : Fin M → R.H), (∀ i, xs i ∈ R.TK) ∧ ∀ a : List (Mx k r), (∀ Y ∈ a, B.unitLie k r Y) → a.length ≤ m → ∃ co : Fin M → ℝ, (∀ i, |co i| ≤ 1) ∧ PI.UpqRep.dsigW (k := k) (r := r) R.σ a x = ∑ i, (co i : ℂ) • xs i := by
  intro hK k r ε mu R hR x hx m
  obtain ⟨ι, _, xs, hxs, h⟩ := box_words_fintype hK R hR hx m
  let e := (Fintype.equivFin ι).symm
  refine ⟨_, xs ∘ e, fun i => hxs _, fun a ha hl => ?_⟩
  obtain ⟨co, hco, h'⟩ := h a ha hl
  refine ⟨co ∘ e, fun i => hco _, ?_⟩
  rw [h', ← e.sum_comp]
  rfl

end GlobalTheory.UnitBoxWords
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LintegralInvEqOfBiInvariantMatGroupStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_inv_eq_of_biInvariant_matGroup : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)), PI.IsMatGroup S → PI.IsHaarOnM S μ → PI.IsRightInvM S μ → ∀ f : PI.MtM m → ℝ≥0∞, Measurable f → ∫⁻ s, f (fun i j => (Matrix.of s)⁻¹ i j) ∂μ = ∫⁻ s, f s ∂μ := by
  first | exact @GlobalTheory.HaarInversion.lintegral_inv_eq | exact GlobalTheory.HaarInversion.lintegral_inv_eq | (intros; apply GlobalTheory.HaarInversion.lintegral_inv_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPosStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matGroupHaar_unique_finite_compact_openPos : ∀ (m : ℕ) (G : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)), PI.IsMatGroup G → PI.IsHaarOnM G μ → (∀ μ' : Measure (PI.MtM m), PI.IsHaarOnM G μ' → ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ μ' = c • μ) ∧ (∀ K : Set (PI.MtM m), IsCompact K → (∀ x ∈ K, Matrix.of x ∈ G) → μ K < ⊤) ∧ ∀ U : Set (PI.MtM m), IsOpen U → (∃ x ∈ U, Matrix.of x ∈ G) → 0 < μ U := by
  first | exact @GlobalTheory.MatHaar.haar_unique_locFinite_openPos | exact GlobalTheory.MatHaar.haar_unique_locFinite_openPos | (intros; apply GlobalTheory.MatHaar.haar_unique_locFinite_openPos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSqIntegralInnerWeightLeStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sq_integral_inner_weight_le : ∀ (Ω V : Type) [MeasurableSpace Ω] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ν : Measure Ω) (f g : Ω → V) (ph : Ω → ℂ), AEStronglyMeasurable f ν → AEStronglyMeasurable g ν → AEStronglyMeasurable ph ν → ENNReal.ofReal (‖∫ x, ⟪f x, ph x • g x⟫_ℂ ∂ν‖ ^ 2) ≤ (∫⁻ x, ENNReal.ofReal (‖ph x‖ ^ 2 * ‖f x‖ ^ 2) ∂ν) * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂ν := by
  first | exact @GlobalTheory.norm_sq_integral_inner_smul_le | exact GlobalTheory.norm_sq_integral_inner_smul_le | (intros; apply GlobalTheory.norm_sq_integral_inner_smul_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyProductBoundConstantLeStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numericalFamily_productBound_constant_le : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (T : ℝ), Num k r lam u b bv ga h q0 → 0 < T → (((2 * r + k + 1) : ℝ) ^ 2 * (T * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) * (b ^ 2) ^ (2 * r) ≤ Hsq r T b := by
  first | exact @GlobalTheory.MomNum.mom_num | exact GlobalTheory.MomNum.mom_num | (intros; apply GlobalTheory.MomNum.mom_num <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGapsStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numericalFamily_shape_gaps : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ), Num k r lam u b bv ga h q0 → (bv ≤ b ∧ (1000000 : ℝ) ≤ bv ∧ ((2 * r + k + 1) : ℝ) ≤ b ∧ 100 * (q0 : ℝ) ≤ bv ∧ GapOK k r (h / 2)) ∧ ∀ ν : Fin (2 * r + k + 1) → ℤ, n1 ν ≤ q0 → Formalism.QuantumDeterminants.IsHCParam (fun a => lam a + (ν a : ℝ)) ∧ Shape (PI.BesselPeriodGGP.eps48 k r) k (fun a => lam a + (ν a : ℝ)) bv ∧ Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (h / 2) ∧ ∀ a c, a < c → 2 ≤ (lam a + (ν a : ℝ)) - (lam c + (ν c : ℝ)) := by
  first | exact @GlobalTheory.NumFam.num_fam | exact GlobalTheory.NumFam.num_fam | (intros; apply GlobalTheory.NumFam.num_fam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PositiveRankOneProportionalStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_rank_one_proportional : ∀ (T W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] (l₀ La : T → W), (∀ v w, ContinuousLinearMap.adjoint ((innerSL ℂ (La v)).smulRight (l₀ w)) = (innerSL ℂ (La w)).smulRight (l₀ v)) → (∀ v ξ, (⟪ξ, ((innerSL ℂ (La v)).smulRight (l₀ v)) ξ⟫_ℂ).im = 0 ∧ 0 ≤ (⟪ξ, ((innerSL ℂ (La v)).smulRight (l₀ v)) ξ⟫_ℂ).re) → (∃ v, l₀ v ≠ 0) → ∃ c : ℝ, 0 ≤ c ∧ ∀ v, La v = (c : ℂ) • l₀ v := by
  first | exact @GlobalTheory.hermitian_rankOne_kernel_shape | exact GlobalTheory.hermitian_rankOne_kernel_shape | (intros; apply GlobalTheory.hermitian_rankOne_kernel_shape <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProductMomentBoundDensityMassOneStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_moment_bound_density_mass_one : ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r : ℕ) (len : Fin (r + 1) → Ω → ℝ) (Ph : Ω → ℝ) (A Rr : ℝ), (∀ a, AEMeasurable (len a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 < len a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν = 1 → 0 ≤ A → 1 ≤ Rr → (∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal (len 0 x ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (A ^ q)) → (∀ a : Fin r, ∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal ((len a.succ x / len a.castSucc x) ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * q))) → ∫⁻ x, ENNReal.ofReal ((∏ a, len a x ^ 2) * Ph x) ∂ν ≤ ENNReal.ofReal ((A * Rr ^ (2 * r)) ^ (r + 1)) := by
  first | exact @GlobalTheory.MomentHolder.product_moment_le | exact GlobalTheory.MomentHolder.product_moment_le | (intros; apply GlobalTheory.MomentHolder.product_moment_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorBlockLinearMapIntertwineStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantumMinor_block_linearMap_intertwine : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n m : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (w : Fin m → Fin n) (Pop : Fin m → Fin m → Wp → Wp), Function.Injective w → (∀ i j v, l (E (w i) (w j) v) = Pop i j (l v)) → ∀ u v, l (Formalism.REAL.qminor E w w u v) = Formalism.FourierDecayAlt.Q.qmF Pop id id u (l v) := by
  first | exact @GlobalTheory.qminor_block_intertwine | exact GlobalTheory.qminor_block_intertwine | (intros; apply GlobalTheory.qminor_block_intertwine <;> assumption)
end

