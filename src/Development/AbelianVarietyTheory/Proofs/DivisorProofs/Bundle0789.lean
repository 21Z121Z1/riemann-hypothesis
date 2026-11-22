import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0773
import GroundTheory.AutomorphicForms.ReductionSiegel
import GroundTheory.AutomorphicForms.ReductionIwasawa
import GroundTheory.AutomorphicForms.ReductionDirichlet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import GroundTheory.AutomorphicForms.GL2.GJMatrixSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0774
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelAtShortOfSixUnit
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem mem_of_pow_mem_valSubring (V : ValuationSubring ℂ) {x : ℂ} {n : ℕ} (hn : n ≠ 0) (h : x ^ n ∈ V) :
    x ∈ V := by
  rw [← V.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff_of_nonneg zero_le' hn).1 h

theorem inv_two_three_mem (V : ValuationSubring ℂ) (h : V.valuation (6 : ℂ) = 1) :
    (2 : ℂ)⁻¹ ∈ V ∧ (3 : ℂ)⁻¹ ∈ V := by
  have h6 : (6 : ℂ)⁻¹ ∈ V := by
    rw [← V.valuation_le_one_iff, map_inv₀, h, inv_one]
  have h2 : (2 : ℂ) ∈ V := by simpa using natCast_mem V 2
  have h3 : (3 : ℂ) ∈ V := by simpa using natCast_mem V 3
  constructor
  · have : (2 : ℂ)⁻¹ = 3 * 6⁻¹ := by norm_num
    rw [this]; exact mul_mem h3 h6
  · have : (3 : ℂ)⁻¹ = 2 * 6⁻¹ := by norm_num
    rw [this]; exact mul_mem h2 h6

theorem short_coeff_mem (V : ValuationSubring ℂ) (h : V.valuation (6 : ℂ) = 1) (a b j : ℂ) (hj : j ∈ V)
    (hd : -16 * (4 * a ^ 3 + 27 * b ^ 2) ∈ V)
    (he : j * (-16 * (4 * a ^ 3 + 27 * b ^ 2)) = (-48 * a) ^ 3) : a ∈ V ∧ b ∈ V := by
  obtain ⟨h2, h3⟩ := inv_two_three_mem V h
  have h1 : -48 * a ∈ V := mem_of_pow_mem_valSubring V (n := 3) (by norm_num) (he ▸ mul_mem hj hd)
  have ha : a ∈ V := by
    have : a = -(((2 : ℂ)⁻¹) ^ 4 * 3⁻¹ * (-48 * a)) := by ring
    rw [this]
    exact neg_mem (mul_mem (mul_mem (pow_mem h2 4) h3) h1)
  refine ⟨ha, mem_of_pow_mem_valSubring V (n := 2) (by norm_num) ?_⟩
  have h4 : (4 : ℂ) ∈ V := by simpa using natCast_mem V 4
  have : b ^ 2 = ((3 : ℂ)⁻¹) ^ 3 * (-(((2 : ℂ)⁻¹) ^ 4 * (-16 * (4 * a ^ 3 + 27 * b ^ 2))) - 4 * a ^ 3) := by
    ring
  rw [this]
  exact mul_mem (pow_mem h3 3) (sub_mem (neg_mem (mul_mem (pow_mem h2 4) hd)) (mul_mem h4 (pow_mem ha 3)))

theorem modelAt_short_of_six_unit :
    ∀ (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (a₄ a₆ j u D : ℂ), j ∈ V → j * (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ = (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).c₄ ^ 3 → V.valuation (6 : ℂ) = 1 → u ∈ F → u ≠ 0 → D ∈ V → V.valuation u ^ 12 * V.valuation D = V.valuation (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ → ModelAt V F ⟨0, 0, 0, a₄, a₆⟩ D := by
  intro V F a₄ a₆ j u D hj he h6 hu hu0 hD hv
  set C : VariableChange ℂ := ⟨Units.mk0 u hu0, 0, 0, 0⟩ with hC
  have hΔ : (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ = -16 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    ring
  have hc : (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).c₄ = -48 * a₄ := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  have hval : V.valuation (u⁻¹ ^ 12 * (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ) = V.valuation D := by
    have hvu : V.valuation u ≠ 0 := by simpa using hu0
    rw [map_mul, map_pow, map_inv₀, ← hv, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hvu, one_pow, one_mul]
  have hmem : u⁻¹ ^ 12 * (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ ∈ V := by
    rw [← V.valuation_le_one_iff, hval, V.valuation_le_one_iff]; exact hD
  have hab := short_coeff_mem V h6 (u⁻¹ ^ 4 * a₄) (u⁻¹ ^ 6 * a₆) j hj
    (by convert hmem using 1; rw [hΔ]; ring)
    (by rw [hΔ, hc] at he; linear_combination u⁻¹ ^ 12 * he)
  refine ⟨C, hu, zero_mem F, zero_mem F, zero_mem F, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [hC, variableChange_a₁, zero_mem]
  · simp [hC, variableChange_a₂, zero_mem]
  · simp [hC, variableChange_a₃, zero_mem]
  · simpa [hC, variableChange_a₄] using hab.1
  · simpa [hC, variableChange_a₆] using hab.2
  · rw [variableChange_Δ, ← hval]; simp [hC]

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModerateGrowthSpanHarishChandraFiniteForms
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology GroundTheory.Automorphic.Reduction
open scoped ContDiff

noncomputable section
open scoped Pointwise
namespace GlobalTheory.HCF.ModGrowth
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in
theorem norm_ringEquivComplex (w : InfinitePlace E) (hw : w.IsComplex) (x : w.Completion) :
    ‖InfinitePlace.Completion.ringEquivComplexOfIsComplex hw x‖ = ‖x‖ :=
  (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).isometry.norm_map_of_map_zero
    (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)) x

theorem norm_pInf_apply (x : Ad E) (w : InfinitePlace E) : ‖pInf E x w‖ = ‖x.1 w‖ :=
  norm_ringEquivComplex w (IsTotallyComplex.isComplex w) (x.1 w)

theorem norm_toL_mul_le (A B : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (A * B)‖ ≤ a * (‖toL A‖ * ‖toL B‖) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖(A * B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (‖toL A‖ * ‖toL B‖) fun k _ => ?_).trans_eq
    (by simp [nsmul_eq_mul]))
  refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _))
  · exact (norm_le_pi_norm (toL A i) k).trans (norm_le_pi_norm (toL A) i)
  · exact (norm_le_pi_norm (toL B k) j).trans (norm_le_pi_norm (toL B) k)

theorem height_mul_le (y z : GL (Fin a) (Cinf E)) :
    GlobalTheory.CuspRep.height (y * z) ≤ (a + 1) * (GlobalTheory.CuspRep.height y * GlobalTheory.CuspRep.height z) := by
  have h1 := norm_toL_mul_le (E := E) y.val z.val
  have h2 := norm_toL_mul_le (E := E) (z⁻¹).val (y⁻¹).val
  unfold GlobalTheory.CuspRep.height
  rw [mul_inv_rev, Units.val_mul, Units.val_mul]
  have p1 := norm_nonneg (toL y.val)
  have p2 := norm_nonneg (toL (y⁻¹).val)
  have q1 := norm_nonneg (toL z.val)
  have q2 := norm_nonneg (toL (z⁻¹).val)
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  nlinarith [mul_nonneg p1 q1, mul_nonneg p2 q2, mul_nonneg p1 q2, mul_nonneg p2 q1, mul_nonneg ha (mul_nonneg p1 q1),
    mul_nonneg ha (mul_nonneg p2 q2), mul_nonneg ha p1, mul_nonneg ha p2, mul_nonneg ha q1, mul_nonneg ha q2,
    mul_nonneg ha (mul_nonneg p1 q2), mul_nonneg ha (mul_nonneg p2 q1)]

theorem continuous_height : Continuous (GlobalTheory.CuspRep.height : GL (Fin a) (Cinf E) → ℝ) := by
  have h1 : Continuous fun y : GL (Fin a) (Cinf E) => toL y.val :=
    Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))
  have h2 : Continuous fun y : GL (Fin a) (Cinf E) => toL (y⁻¹).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp continuous_inv
  exact (continuous_const.add (continuous_norm.comp h1)).add (continuous_norm.comp h2)

theorem pFin_diag (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) :
    Matrix.GeneralLinearGroup.map (pFin E) (diagUnits a fun i => posIdele (K := E) (r i) (hr i)) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change pFin E ((diagUnits a fun i => posIdele (K := E) (r i) (hr i) : GA E a) i j) = (1 : Matrix (Fin a) (Fin a) (Af E)) i j
  rw [coe_diagUnits, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs with h
  · subst h
    exact IsDedekindDomain.FiniteAdeleRing.ext _ fun v => by
      change ((posIdele (K := E) (r i) (hr i) : GroundTheory.Global.IdeleGroup E) : AdeleRing (𝓞 E) E).2 v = _
      rw [posIdele_finite]; rfl
  · exact map_zero _

theorem height_pInf_diag (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) :
    GlobalTheory.CuspRep.height (Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a fun i => posIdele (K := E) (r i) (hr i)))
      ≤ 1 + ∑ i, (r i + (r i)⁻¹) := by
  set d : Fin a → GroundTheory.Global.IdeleGroup E := fun i => posIdele (K := E) (r i) (hr i) with hd
  have hn : ∀ i w, ‖pInf E (d i : Ad E) w‖ = r i := fun i w => by
    rw [norm_pInf_apply]; exact norm_posIdele_infinite (r i) (hr i) w
  have hn' : ∀ i w, ‖pInf E (((d i)⁻¹ : GroundTheory.Global.IdeleGroup E) : Ad E) w‖ = (r i)⁻¹ := fun i w => by
    have e : pInf E (((d i)⁻¹ : GroundTheory.Global.IdeleGroup E) : Ad E) w * pInf E (d i : Ad E) w = 1 := by
      rw [← Pi.mul_apply, ← map_mul, Units.inv_mul, map_one, Pi.one_apply]
    have := congrArg norm e
    rw [norm_mul, hn, norm_one] at this
    exact eq_inv_of_mul_eq_one_left this
  have key : ∀ (f : Fin a → GroundTheory.Global.IdeleGroup E) (s : Fin a → ℝ), (∀ i w, ‖pInf E (f i : Ad E) w‖ = s i) →
      (∀ i, 0 ≤ s i) → ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a f)).val‖ ≤ ∑ i, s i := by
    intro f s hf hs
    have h0 : 0 ≤ ∑ i, s i := Finset.sum_nonneg fun i _ => hs i
    refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
    change ‖pInf E ((diagUnits a f : GA E a) i j)‖ ≤ _
    rw [coe_diagUnits, Matrix.diagonal_apply]
    split_ifs with h
    · subst h
      refine (pi_norm_le_iff_of_nonneg h0).2 fun w => ?_
      rw [hf]
      exact Finset.single_le_sum (fun k _ => hs k) (Finset.mem_univ i)
    · rw [map_zero, norm_zero]; exact h0
  have h1 := key d r hn fun i => (hr i).le
  have h2 := key (fun i => (d i)⁻¹) (fun i => (r i)⁻¹) hn' fun i => (inv_pos.2 (hr i)).le
  have e : (Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a d))⁻¹ =
      Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a fun i => (d i)⁻¹) := by
    rw [← map_inv, ← map_inv]; rfl
  unfold GlobalTheory.CuspRep.height
  rw [e, Finset.sum_add_distrib]
  linarith

theorem span_props {L : Subgroup (GL (Fin a) (Af E))} {W : Submodule ℂ (Kinf E a → ℂ)}
    {X : Set (Module.End ℂ (Sm E a) → ℂ)} {N : ℕ} {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ (formsGL E a L W X N)) :
    (∀ l ∈ L, finRep E a l φ = φ) ∧ ∀ g, ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧
      ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ M := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    refine ⟨hx.2.1, fun g => ?_⟩
    obtain ⟨C, M, h⟩ := hx.1.growth g
    refine ⟨|C|, M, abs_nonneg _, fun y => (h y).trans (mul_le_mul_of_nonneg_right (le_abs_self C) ?_)⟩
    exact pow_nonneg (zero_le_one.trans (one_le_height y)) _
  | zero => exact ⟨fun l _ => map_zero _, fun g => ⟨0, 0, le_rfl, fun y => by simp⟩⟩
  | add x y _ _ hx hy =>
    refine ⟨fun l hl => by rw [map_add, hx.1 l hl, hy.1 l hl], fun g => ?_⟩
    obtain ⟨C1, M1, h1, e1⟩ := hx.2 g
    obtain ⟨C2, M2, h2, e2⟩ := hy.2 g
    refine ⟨C1 + C2, M1 + M2, add_nonneg h1 h2, fun z => ?_⟩
    have hz := one_le_height z
    have p1 : GlobalTheory.CuspRep.height z ^ M1 ≤ GlobalTheory.CuspRep.height z ^ (M1 + M2) := pow_le_pow_right₀ hz (by omega)
    have p2 : GlobalTheory.CuspRep.height z ^ M2 ≤ GlobalTheory.CuspRep.height z ^ (M1 + M2) := pow_le_pow_right₀ hz (by omega)
    calc ‖(x + y).1 (g * infGL E a z)‖ = ‖x.1 (g * infGL E a z) + y.1 (g * infGL E a z)‖ := rfl
      _ ≤ ‖x.1 (g * infGL E a z)‖ + ‖y.1 (g * infGL E a z)‖ := norm_add_le _ _
      _ ≤ C1 * GlobalTheory.CuspRep.height z ^ (M1 + M2) + C2 * GlobalTheory.CuspRep.height z ^ (M1 + M2) :=
        add_le_add ((e1 z).trans (mul_le_mul_of_nonneg_left p1 h1)) ((e2 z).trans (mul_le_mul_of_nonneg_left p2 h2))
      _ = (C1 + C2) * GlobalTheory.CuspRep.height z ^ (M1 + M2) := by ring
  | smul c x _ hx =>
    refine ⟨fun l hl => by rw [map_smul, hx.1 l hl], fun g => ?_⟩
    obtain ⟨C, M, h, e⟩ := hx.2 g
    refine ⟨‖c‖ * C, M, by positivity, fun z => ?_⟩
    change ‖c * x.1 (g * infGL E a z)‖ ≤ _
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (e z) (norm_nonneg c)

theorem uniform_fin {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) {φ : Sm E a}
    (hinv : ∀ l ∈ L, finRep E a l φ = φ)
    (hg : ∀ g, ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ M)
    {S : Set (GL (Fin a) (Af E))} (hS : IsCompact S) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ s ∈ S, ∀ y, ‖φ.1 (finGL E a s * infGL E a y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ M := by
  classical
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun s : GL (Fin a) (Af E) => s • (L : Set (GL (Fin a) (Af E))))
    (fun s => hL.leftCoset s) (fun s _ => Set.mem_iUnion.2 ⟨s, Set.mem_smul_set.2 ⟨1, L.one_mem, mul_one s⟩⟩)
  choose C M hC hb using fun s : GL (Fin a) (Af E) => hg (finGL E a s)
  refine ⟨∑ s ∈ t, C s, ∑ s ∈ t, M s, Finset.sum_nonneg fun s _ => hC s, fun s' hs' y => ?_⟩
  obtain ⟨s, hst, hs⟩ := Set.mem_iUnion₂.1 (ht hs')
  obtain ⟨l, hl, rfl⟩ := Set.mem_smul_set.1 hs
  have e : φ.1 (finGL E a (s • l) * infGL E a y) = φ.1 (finGL E a s * infGL E a y) := by
    have h := congrArg (fun ψ : Sm E a => ψ.1 (finGL E a s * infGL E a y)) (hinv l hl)
    refine Eq.trans ?_ h
    change φ.1 (finGL E a (s * l) * infGL E a y) = φ.1 (finGL E a s * infGL E a y * finGL E a l)
    rw [map_mul, mul_assoc, mul_assoc, infGL_comm]
  rw [e]
  have hy := one_le_height y
  refine (hb s y).trans (mul_le_mul (Finset.single_le_sum (fun s _ => hC s) hst)
    (pow_le_pow_right₀ hy (Finset.single_le_sum (fun s _ => Nat.zero_le (M s)) hst))
    (pow_nonneg (zero_le_one.trans hy) _) (Finset.sum_nonneg fun s _ => hC s))

end GlobalTheory.HCF.ModGrowth

namespace GlobalTheory.HCF.ModGrowth

theorem modGrowth_span : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ (W : Submodule ℂ (Kinf E a → ℂ))
    (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N : ℕ), ∀ φ ∈ Submodule.span ℂ (formsGL E a L W X N),
    ∀ Ω : Set (GA E a), IsCompact Ω → ∃ (C : ℝ) (N₀ : ℕ), 0 ≤ C ∧ ∀ b ∈ Ω, ∀ (r : Fin a → ℝ) (hr : ∀ i, 0 < r i),
    ∀ k ∈ (maxCompact : Subgroup (GA E a)), ∀ y : GL (Fin a) (Cinf E),
    ‖φ.1 (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k * infGL E a y)‖ ≤
      C * (∑ i, (r i + (r i)⁻¹)) ^ N₀ * height y ^ N₀ := by
  intro E _ _ _ a L hL W X N φ hφ Ω hΩ
  obtain ⟨hinv, hgr⟩ := span_props hφ
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have h1 : ∀ g : GA E 0, g = 1 := fun g => Units.ext (Matrix.ext fun i => Fin.elim0 i)
    refine ⟨‖φ.1 1‖, 0, norm_nonneg _, fun b _ r hr k _ y => ?_⟩
    rw [h1 (b * _ * k * _)]
    simp
  have hS : IsCompact ((fun p : GA E a × GA E a => Matrix.GeneralLinearGroup.map (pFin E) (p.1 * p.2)) ''
      (Ω ×ˢ ((maxCompact : Subgroup (GA E a)) : Set (GA E a)))) :=
    (hΩ.prod isCompact_maxCompact).image ((ContAut.continuous_map_pFin E a).comp (continuous_fst.mul continuous_snd))
  obtain ⟨C1, M, hC1, hb1⟩ := uniform_fin hL hinv hgr hS
  have hf : Continuous fun g : GA E a => GlobalTheory.CuspRep.height (Matrix.GeneralLinearGroup.map (pInf E) g) :=
    continuous_height.comp (ContAut.continuous_map_pInf E a)
  obtain ⟨Mb, hMb⟩ := hΩ.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨Mk, hMk⟩ := (isCompact_maxCompact (K := E) (n := a)).exists_bound_of_continuousOn hf.continuousOn
  have hB : (0 : ℝ) ≤ (a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1) := by positivity
  refine ⟨C1 * ((a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1)) ^ M, M, by positivity, fun b hb r hr k hk y => ?_⟩
  have hfin : Matrix.GeneralLinearGroup.map (pFin E) (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k *
      infGL E a y) = Matrix.GeneralLinearGroup.map (pFin E) (b * k) := by
    simp only [map_mul, pFin_diag, pFin_infGL, mul_one]
  have hinf : Matrix.GeneralLinearGroup.map (pInf E) (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k *
      infGL E a y) = Matrix.GeneralLinearGroup.map (pInf E) b *
        Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a (fun i => posIdele (K := E) (r i) (hr i))) *
        Matrix.GeneralLinearGroup.map (pInf E) k * y := by
    simp only [map_mul, pInf_infGL]
  have hx := infGL_mul_finGL (b * diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) * k * infGL E a y)
  rw [infGL_comm, hfin, hinf] at hx
  rw [← hx]
  have hs : Matrix.GeneralLinearGroup.map (pFin E) (b * k) ∈ (fun p : GA E a × GA E a =>
      Matrix.GeneralLinearGroup.map (pFin E) (p.1 * p.2)) '' (Ω ×ˢ ((maxCompact : Subgroup (GA E a)) : Set (GA E a))) :=
    ⟨(b, k), ⟨hb, hk⟩, rfl⟩
  refine (hb1 _ hs _).trans ?_

  set A := Matrix.GeneralLinearGroup.map (pInf E) b
  set D := Matrix.GeneralLinearGroup.map (pInf E) (diagUnits a (fun i => posIdele (K := E) (r i) (hr i)))
  set K := Matrix.GeneralLinearGroup.map (pInf E) k
  set s := ∑ i, (r i + (r i)⁻¹)
  have hs1 : 1 ≤ s := by
    have h0 : ∀ i, 0 ≤ r i + (r i)⁻¹ := fun i => add_nonneg (hr i).le (inv_pos.2 (hr i)).le
    have h1 : 1 ≤ r ⟨0, ha⟩ + (r ⟨0, ha⟩)⁻¹ := by
      rcases le_total (r ⟨0, ha⟩) 1 with h | h
      · linarith [(one_le_inv₀ (hr ⟨0, ha⟩)).2 h, hr ⟨0, ha⟩]
      · linarith [inv_pos.2 (hr ⟨0, ha⟩)]
    exact h1.trans (Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_univ _))
  have hA : GlobalTheory.CuspRep.height A ≤ max Mb 1 :=
    ((Real.le_norm_self _).trans (hMb b hb)).trans (le_max_left _ _)
  have hK : GlobalTheory.CuspRep.height K ≤ max Mk 1 :=
    ((Real.le_norm_self _).trans (hMk k hk)).trans (le_max_left _ _)
  have hD : GlobalTheory.CuspRep.height D ≤ 2 * s := (height_pInf_diag r hr).trans (by linarith)
  have hA1 := one_le_height A
  have hD1 := one_le_height D
  have hK1 := one_le_height K
  have hy1 := one_le_height y
  have c0 : (0 : ℝ) ≤ a + 1 := by positivity
  have e3 := height_mul_le A D
  have e2 := height_mul_le (A * D) K
  have e1 := height_mul_le (A * D * K) y
  have hAD : GlobalTheory.CuspRep.height A * GlobalTheory.CuspRep.height D ≤ max Mb 1 * (2 * s) :=
    mul_le_mul hA hD (by linarith) (by positivity)
  have hADK : GlobalTheory.CuspRep.height (A * D * K) ≤ (a + 1) * ((a + 1) * (max Mb 1 * (2 * s)) * max Mk 1) :=
    e2.trans (mul_le_mul_of_nonneg_left (mul_le_mul (e3.trans (mul_le_mul_of_nonneg_left hAD c0)) hK (by linarith)
      (by positivity)) c0)
  have hz : GlobalTheory.CuspRep.height (A * D * K * y) ≤ (a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1) * s * GlobalTheory.CuspRep.height y := by
    refine e1.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hADK (by linarith)) c0).trans_eq ?_)
    ring
  have hz0 : 0 ≤ GlobalTheory.CuspRep.height (A * D * K * y) := zero_le_one.trans (one_le_height _)
  calc C1 * GlobalTheory.CuspRep.height (A * D * K * y) ^ M
      ≤ C1 * ((a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1) * s * GlobalTheory.CuspRep.height y) ^ M :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz0 hz M) hC1
    _ = C1 * ((a + 1) ^ 3 * (max Mb 1 * 2 * max Mk 1)) ^ M * s ^ M * GlobalTheory.CuspRep.height y ^ M := by
        rw [mul_pow, mul_pow]; ring

end GlobalTheory.HCF.ModGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroSquaresModPrimeMulPermUpToSign
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem isSquare_or_isSquare_neg_of_mod_four {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3)
    {a : ZMod p} (ha : a ≠ 0) : IsSquare a ∨ IsSquare (-a) := by
  by_cases hs : IsSquare a
  · exact Or.inl hs
  · right
    have h1 : quadraticChar (ZMod p) a = -1 := (quadraticChar_neg_one_iff_not_isSquare).2 hs
    have hm1 : ¬ IsSquare (-1 : ZMod p) := by
      rw [ZMod.exists_sq_eq_neg_one_iff]; omega
    have h2 : quadraticChar (ZMod p) (-1) = -1 := (quadraticChar_neg_one_iff_not_isSquare).2 hm1
    have h4 : quadraticChar (ZMod p) (-a) = 1 := by
      rw [neg_eq_neg_one_mul, map_mul, h1, h2]; norm_num
    exact (quadraticChar_one_iff_isSquare (neg_ne_zero.2 ha)).1 h4

theorem sq_perm_mul :
    ∀ (p c : ℕ), p.Prime → p % 4 = 3 → ¬ p ∣ c → ∃ (e : Sq p ≃ Sq p) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
      ∀ k : Sq p, (p : ℤ) ∣ (((k.1 : ℕ) : ℤ) * c - ε * (((e k).1 : ℕ) : ℤ)) := by
  intro p c hp h3 hc
  haveI : Fact p.Prime := ⟨hp⟩
  have hc0 : ((c : ℕ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  obtain ⟨ε, hε, hsq⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsSquare ((ε : ZMod p) * (c : ZMod p)) := by
    rcases isSquare_or_isSquare_neg_of_mod_four h3 hc0 with h | h
    · exact ⟨1, Or.inl rfl, by simpa using h⟩
    · exact ⟨-1, Or.inr rfl, by simpa using h⟩
  set s : ZMod p := (ε : ZMod p) * (c : ZMod p) with hs
  have hε2 : (ε : ZMod p) * (ε : ZMod p) = 1 := by
    rcases hε with h | h <;> subst h <;> simp
  have hs0 : s ≠ 0 := by
    intro h0
    have : (ε : ZMod p) * s = 0 := by rw [h0, mul_zero]
    rw [hs, ← mul_assoc, hε2, one_mul] at this
    exact hc0 this
  let f : Sq p → Sq p := fun k =>
    ⟨⟨(s * ((k.1 : ℕ) : ZMod p)).val, ZMod.val_lt _⟩, by
      simp only [ZMod.natCast_val, ZMod.cast_id', id]
      exact ⟨mul_ne_zero hs0 k.2.1, hsq.mul k.2.2⟩⟩
  have hf : ∀ k, (((f k).1 : ℕ) : ZMod p) = s * ((k.1 : ℕ) : ZMod p) := by
    intro k; simp [f]
  have hinj : Function.Injective f := by
    intro k₁ k₂ h
    have h' : s * ((k₁.1 : ℕ) : ZMod p) = s * ((k₂.1 : ℕ) : ZMod p) := by
      rw [← hf, ← hf, h]
    have h'' := mul_left_cancel₀ hs0 h'
    apply Subtype.ext; apply Fin.ext
    have := congrArg ZMod.val h''
    rwa [ZMod.val_cast_of_lt k₁.1.2, ZMod.val_cast_of_lt k₂.1.2] at this
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.1 hinj
  refine ⟨Equiv.ofBijective f hbij, ε, hε, fun k => ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [Equiv.ofBijective_apply, hf, hs]
  linear_combination (-(((k.1 : ℕ) : ZMod p) * (c : ZMod p))) * hε2

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroSquaresSumEquivIcoModFour
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.SqSplit

theorem natCast_sub_eq_neg {p n : ℕ} (h : n ≤ p) : ((p - n : ℕ) : ZMod p) = -((n : ℕ) : ZMod p) := by
  rw [Nat.cast_sub h, ZMod.natCast_self, zero_sub]

theorem neg_one_not_isSquare {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) : ¬ IsSquare (-1 : ZMod p) := by
  rw [ZMod.exists_sq_eq_neg_one_iff]; omega

theorem ringChar_ne_two {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; omega

theorem isSquare_neg_of_not {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) {a : ZMod p} (ha : a ≠ 0)
    (hs : ¬ IsSquare a) : IsSquare (-a) := by
  have hc := ringChar_ne_two h3
  have h1 : quadraticChar (ZMod p) a = -1 := (quadraticChar_neg_one_iff_not_isSquare).2 hs
  have h2 : quadraticChar (ZMod p) (-1) = -1 :=
    (quadraticChar_neg_one_iff_not_isSquare).2 (neg_one_not_isSquare h3)
  have hna : -a ≠ 0 := neg_ne_zero.2 ha
  rw [← quadraticChar_one_iff_isSquare hna, neg_eq_neg_one_mul, map_mul, h1, h2]; norm_num

theorem not_both {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) {a : ZMod p} (ha : a ≠ 0)
    (h1 : IsSquare a) (h2 : IsSquare (-a)) : False := by
  apply neg_one_not_isSquare h3
  have : (-1 : ZMod p) = -a * a⁻¹ := by rw [neg_mul, mul_inv_cancel₀ ha]
  rw [this]; exact h2.mul h1.inv

end GlobalTheory.SqSplit

open GlobalTheory.SqSplit in
theorem GlobalTheory.sq_sum_equiv_Ico : ∀ (p : ℕ), p.Prime → p % 4 = 3 → ∃ e : Sq p ⊕ Sq p ≃ (Finset.Ico 1 p : Finset ℕ), ∀ k : Sq p, ((e (Sum.inl k) : ℕ) = (k.1 : ℕ)) ∧ ((e (Sum.inr k) : ℕ) = p - (k.1 : ℕ)) := by
  intro p hp h3
  haveI : Fact p.Prime := ⟨hp⟩
  have pos : ∀ k : Sq p, 1 ≤ (k.1 : ℕ) := by
    intro k
    rcases Nat.eq_zero_or_pos (k.1 : ℕ) with h | h
    · exact absurd (by rw [h]; simp) k.2.1
    · exact h
  let f : Sq p ⊕ Sq p → (Finset.Ico 1 p : Finset ℕ) := Sum.elim
    (fun k => ⟨(k.1 : ℕ), Finset.mem_Ico.2 ⟨pos k, k.1.2⟩⟩)
    (fun k => ⟨p - (k.1 : ℕ), Finset.mem_Ico.2 ⟨by have := k.1.2; omega, by have := pos k; omega⟩⟩)
  have hf : Function.Bijective f := by
    constructor
    · rintro (a | a) (b | b) hab <;> simp only [f, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at hab
      · exact congrArg Sum.inl (Subtype.ext (Fin.ext hab))
      · exfalso
        have hb := b.1.2
        have e1 : ((a.1 : ℕ) : ZMod p) = -((b.1 : ℕ) : ZMod p) := by
          rw [hab, natCast_sub_eq_neg hb.le]
        exact not_both h3 b.2.1 b.2.2 (e1 ▸ a.2.2)
      · exfalso
        have ha := a.1.2
        have e1 : ((b.1 : ℕ) : ZMod p) = -((a.1 : ℕ) : ZMod p) := by
          rw [← hab, natCast_sub_eq_neg ha.le]
        exact not_both h3 a.2.1 a.2.2 (e1 ▸ b.2.2)
      · have ha := a.1.2; have hb := b.1.2
        exact congrArg Sum.inr (Subtype.ext (Fin.ext (by omega)))
    · rintro ⟨n, hn⟩
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hn
      have hn0 : ((n : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd; exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
      by_cases hs : IsSquare ((n : ℕ) : ZMod p)
      · exact ⟨Sum.inl ⟨⟨n, h2⟩, hn0, hs⟩, rfl⟩
      · have hm : ((p - n : ℕ) : ZMod p) = -((n : ℕ) : ZMod p) := natCast_sub_eq_neg h2.le
        refine ⟨Sum.inr ⟨⟨p - n, by omega⟩, ?_, ?_⟩, ?_⟩
        · simp only; rw [hm]; exact neg_ne_zero.2 hn0
        · simp only; rw [hm]; exact isSquare_neg_of_not h3 hn0 hs
        · simp only [f, Sum.elim_inr]; apply Subtype.ext; simp only; omega
  exact ⟨Equiv.ofBijective f hf, fun k => ⟨rfl, rfl⟩⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEqOfValuedEq
section
open NumberField IsDedekindDomain Matrix GroundTheory.Global GroundTheory.Automorphic.GJMatrix GlobalTheory.HenQ
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc)
open scoped nonZeroDivisors

noncomputable section
namespace GlobalTheory.HenQ
variable {K : Type} [Field K] [NumberField K]

theorem valued_det_of_KGL {w : HeightOneSpectrum (𝓞 K)} {n : ℕ} {g : GL (Fin n) (w.adicCompletion K)}
    (hg : g ∈ GlobalTheory.LFun.KGL w n) : Valued.v g.val.det = 1 := by
  obtain ⟨g0, rfl⟩ := hg
  set O := (w.adicCompletionIntegers K).toSubring
  have hd : ∀ h : GL (Fin n) O, ((Formalism.UG.bc O.subtype h).val.det) = ((h.val.det : O) : w.adicCompletion K) := by
    intro h
    exact (RingHom.map_det O.subtype h.val).symm
  have h1 : Valued.v ((g0.val.det : O) : w.adicCompletion K) ≤ 1 := (g0.val.det).2
  have h2 : Valued.v (((g0⁻¹).val.det : O) : w.adicCompletion K) ≤ 1 := ((g0⁻¹).val.det).2
  have h3 : ((g0.val.det : O) : w.adicCompletion K) * (((g0⁻¹).val.det : O) : w.adicCompletion K) = 1 := by
    rw [← Subring.coe_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    rfl
  have h4 := congrArg Valued.v h3
  rw [map_mul, map_one] at h4
  rw [hd]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := h4.symm
    _ ≤ Valued.v ((g0.val.det : O) : w.adicCompletion K) * 1 := mul_le_mul' le_rfl h2
    _ = _ := mul_one _

end GlobalTheory.HenQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmGenerationOfDivisionStepPadicStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_generation_of_division_step_padic : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) E), (∀ i, QL μ ⊤ (e i)) → (∀ f, QL μ ⊤ f → ∃ (b : ι → O) (s : MvPowerSeries (Fin d) O) (f₁ : MvPowerSeries (Fin d) E), QL μ ⊤ f₁ ∧ f = comb b e + map (algebraMap O E) s + (p : E) • f₁) → ∀ f, QL μ ⊤ f → ∃ b : ι → O, In (⊤ : Ideal O) (f - comb b e) := by
  first | exact @GlobalTheory.QLog.Conv.generate_of_step | exact GlobalTheory.QLog.Conv.generate_of_step | (intros; apply GlobalTheory.QLog.Conv.generate_of_step <;> assumption)
end

