import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerEis
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0103
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0200
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0202
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0190

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerEisStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_slz_qs_eis_eq_smul : ∀ (j N l : ℕ) (ω : DirichletCharacter ℂ l) (ν : DirichletCharacter ℂ N) (c₁ c₂ : ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ j → 0 < N → l.Prime → ¬ l ∣ N → MF j (N * l) (fun d => ch ω d * ch ν d) (eis j c₁ (ch ω) (ch ν)) → MF j (N * l) (fun d => ch ω d * ch ν⁻¹ d) (eis j c₂ (fun x => ch ω x * hat ν x) fun _ => 1) → ∃ κ : ℂ, κ ≠ 0 ∧ slz j !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs (eis j c₁ (ch ω) (ch ν))) = κ • qs (eis j c₂ (fun x => ch ω x * hat ν x) fun _ => 1) := by
  first | exact @GlobalTheory.EisAL.atkin_lehner_eis | exact GlobalTheory.EisAL.atkin_lehner_eis | (intros; apply GlobalTheory.EisAL.atkin_lehner_eis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BadRowsShareBoundTwoPrimes
section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.ShareThm

theorem real_step (ep x w₁ w₂ W₁ W₂ D D₀ D₁ D₂ : ℝ) (h0 : 0 ≤ ep) (h1 : ep < 1) (hD : 0 ≤ D)
    (hall : |D - x| ≤ ep * x) (h₁ : |D₁ - w₁ * x| ≤ ep * (w₁ * x)) (h₂ : |D₂ - w₂ * x| ≤ ep * (w₂ * x))
    (hw₁ : w₁ ≤ W₁) (hw₂ : w₂ ≤ W₂) (hs : D ≤ D₀ + D₁ + D₂) :
    (1 - (1 + ep) / (1 - ep) * (max 0 W₁ + max 0 W₂)) * D ≤ D₀ := by
  obtain ⟨ha, hb⟩ := abs_le.mp hall
  have hc := (abs_le.mp h₁).2
  have hd := (abs_le.mp h₂).2
  have hx : 0 ≤ x := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hpos : 0 < 1 - ep := by linarith
  have hxD : x ≤ D / (1 - ep) := by
    rw [le_div_iff₀ hpos]; nlinarith
  have m₁ : w₁ ≤ max 0 W₁ := hw₁.trans (le_max_right _ _)
  have m₂ : w₂ ≤ max 0 W₂ := hw₂.trans (le_max_right _ _)
  have p₁ : 0 ≤ max 0 W₁ := le_max_left _ _
  have p₂ : 0 ≤ max 0 W₂ := le_max_left _ _
  set A := max 0 W₁
  set B := max 0 W₂
  have e₁ : D₁ + D₂ ≤ (1 + ep) * ((w₁ + w₂) * x) := by nlinarith
  have e₂ : (w₁ + w₂) * x ≤ (A + B) * (D / (1 - ep)) :=
    (mul_le_mul_of_nonneg_right (add_le_add m₁ m₂) hx).trans
      (mul_le_mul_of_nonneg_left hxD (add_nonneg p₁ p₂))
  have e₃ : D₁ + D₂ ≤ (1 + ep) * ((A + B) * (D / (1 - ep))) :=
    e₁.trans (mul_le_mul_of_nonneg_left e₂ (by linarith))
  have e₄ : (1 - (1 + ep) / (1 - ep) * (A + B)) * D = D - (1 + ep) * ((A + B) * (D / (1 - ep))) := by
    ring
  rw [e₄]; linarith

theorem abstract_step (H₁ H₂ : Type) [Group H₁] [Fintype H₁] [Group H₂] [Fintype H₂]
    (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (H₁ × H₂) M)
    (U₁ : H₁ → Prop) (U₂ : H₂ → Prop) (E₁ A₁ : H₁ → ℂ) (E₂ A₂ : H₂ → ℂ)
    (hE₁ : IsProj E₁) (hE₂ : IsProj E₂) (hA₁ : IsProj A₁) (hA₂ : IsProj A₂)
    (c₁ : ∀ a, conv A₁ a = conv a A₁) (c₂ : ∀ a, conv A₂ a = conv a A₂)
    (u₁ : ∀ γ, E₁ γ ≠ 0 → U₁ γ) (u₂ : ∀ γ, E₂ γ ≠ 0 → U₂ γ)
    (w₁ w₂ W₁ W₂ : ℝ) (hw₁ : conv (dirac - A₁) E₁ 1 = (w₁ : ℂ) * E₁ 1) (hw₂ : conv (dirac - A₂) E₂ 1 = (w₂ : ℂ) * E₂ 1)
    (hW₁ : w₁ ≤ W₁) (hW₂ : w₂ ≤ W₂) (ep c : ℝ) (h0 : 0 ≤ ep) (h1 : ep < 1)
    (hc : ∀ e : H₁ × H₂ → ℂ, IsProj e → ((∀ γ, e γ ≠ 0 → U₁ γ.1) ∨ ∀ γ, e γ ≠ 0 → U₂ γ.2) →
      |(rk ρ e : ℝ) - c * (e 1).re| ≤ ep * (c * (e 1).re)) :
    (1 - (1 + ep) / (1 - ep) * (max 0 W₁ + max 0 W₂)) * (rk ρ (tens2 E₁ E₂) : ℝ)
      ≤ (rk ρ (conv (tens2 A₁ A₂) (tens2 E₁ E₂)) : ℝ) := by
  obtain ⟨hop, hone, -, -, -, -, -⟩ := GlobalTheory.T.groupAlgebraOperator_convolution_calculus (H₁ × H₂) M ρ
  obtain ⟨-, -, has₁, hd₁, hp₁, hq₁, -⟩ := GlobalTheory.T.groupAlgebraOperator_convolution_calculus H₁ ℂ 1
  obtain ⟨-, -, has₂, hd₂, hp₂, hq₂, -⟩ := GlobalTheory.T.groupAlgebraOperator_convolution_calculus H₂ ℂ 1
  obtain ⟨-, -, tc, tp, td, ts⟩ := GlobalTheory.T.exteriorTensorProduct_convolution_calculus Unit H₁ H₂
  have P₁ : IsProj (conv (dirac - A₁) E₁) := hp₁ _ _ (hq₁ _ hA₁) hE₁ (by
    rw [(has₁ dirac A₁ E₁).2.1, (has₁ dirac A₁ E₁).2.2, (hd₁ E₁).1, (hd₁ E₁).2, c₁])
  have P₂ : IsProj (conv (dirac - A₂) E₂) := hp₂ _ _ (hq₂ _ hA₂) hE₂ (by
    rw [(has₂ dirac A₂ E₂).2.1, (has₂ dirac A₂ E₂).2.2, (hd₂ E₂).1, (hd₂ E₂).2, c₂])
  have kall := hc (tens2 E₁ E₂) (tp _ _ hE₁ hE₂) (Or.inr fun γ h => u₂ _ (right_ne_zero_of_mul h))
  have k₁ := hc (tens2 (conv (dirac - A₁) E₁) E₂) (tp _ _ P₁ hE₂) (Or.inr fun γ h => u₂ _ (right_ne_zero_of_mul h))
  have k₂ := hc (tens2 E₁ (conv (dirac - A₂) E₂)) (tp _ _ hE₁ P₂) (Or.inl fun γ h => u₁ _ (left_ne_zero_of_mul h))
  have v₁ : c * (tens2 (conv (dirac - A₁) E₁) E₂ 1).re = w₁ * (c * (tens2 E₁ E₂ 1).re) := by
    simp only [tens2, Prod.fst_one, Prod.snd_one, hw₁, mul_assoc, Complex.re_ofReal_mul]; ring
  have v₂ : c * (tens2 E₁ (conv (dirac - A₂) E₂) 1).re = w₂ * (c * (tens2 E₁ E₂ 1).re) := by
    simp only [tens2, Prod.fst_one, Prod.snd_one, hw₂]
    rw [mul_left_comm (E₁ 1), Complex.re_ofReal_mul]; ring
  rw [v₁] at k₁
  rw [v₂] at k₂
  have hs := GlobalTheory.T.finrank_range_le_sum_three_complements M (op ρ (tens2 E₁ E₂)) (op ρ (tens2 A₁ dirac)) (op ρ (tens2 dirac A₂))
  have r₀ : op ρ (tens2 A₁ dirac) * op ρ (tens2 dirac A₂) * op ρ (tens2 E₁ E₂)
      = op ρ (conv (tens2 A₁ A₂) (tens2 E₁ E₂)) := by
    rw [← (hop _ _).1, ← (hop _ _).1, tc A₁ dirac, (hd₁ A₁).2, (hd₂ A₂).1]
  have r₁ : (1 - op ρ (tens2 A₁ dirac)) * op ρ (tens2 E₁ E₂) = op ρ (tens2 (conv (dirac - A₁) E₁) E₂) := by
    rw [← hone, ← td, ← (hop _ _).2.1, ← (ts dirac A₁ dirac dirac).1, ← (hop _ _).1, tc, (hd₂ E₂).1]
  have r₂ : (1 - op ρ (tens2 dirac A₂)) * op ρ (tens2 E₁ E₂) = op ρ (tens2 E₁ (conv (dirac - A₂) E₂)) := by
    rw [← hone, ← td, ← (hop _ _).2.1, ← (ts dirac dirac dirac A₂).2, ← (hop _ _).1, tc, (hd₁ E₁).1]
  rw [r₀, r₁, r₂] at hs
  refine real_step ep _ w₁ w₂ W₁ W₂ _ _ _ _ h0 h1 (Nat.cast_nonneg _) kall k₁ k₂ hW₁ hW₂ ?_
  unfold rk
  exact_mod_cast hs

theorem level_proj (g : ℕ) [Fact g.Prime] (N : ℕ) (ι : Type) [Fintype ι] (L : ι → Lev g N) :
    IsProj (tens fun v => (L v).e) ∧ ∀ γ, (tens fun v => (L v).e) γ ≠ 0 → AllUnip γ := by
  constructor
  · refine (GlobalTheory.T.exteriorTensorProduct_convolution_calculus ι (GG g N) Unit).2.1 _ fun v => ?_
    obtain ⟨a, b, c, d, -⟩ := GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N (L v)
    exact (GlobalTheory.T.subgroupCharacterIdempotent_properties (GG g N) ℂ 1 _ _ a b c d).1
  · intro γ h v
    apply (GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N (L v)).2.2.2.2
    have h' : (L v).e (γ v) ≠ 0 := Finset.prod_ne_zero_iff.mp h v (Finset.mem_univ v)
    by_contra hn
    exact h' (by simp [Lev.e, eps, hn])

theorem bad_share : ∀ (g₁ g₂ : ℕ) [Fact g₁.Prime] [Fact g₂.Prime] (N m q d : ℕ) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂], 100000 ≤ N → PrimeOK g₁ q d → PrimeOK g₂ q d → ∀ (L₁ : ι₁ → Lev g₁ N) (L₂ : ι₂ → Lev g₂ N) (τ₁ : ι₁ → (ZMod g₁)[X] → GG g₁ N → ℂ) (τ₂ : ι₂ → (ZMod g₂)[X] → GG g₂ N → ℂ), (∀ v, IsSeries (τ₁ v)) → (∀ v, IsSeries (τ₂ v)) → ∀ (ch₁ : ι₁ → Fin m → (ZMod g₁)ˣ) (ch₂ : ι₂ → Fin m → (ZMod g₂)ˣ) (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ ((ι₁ → GG g₁ N) × (ι₂ → GG g₂ N)) M) (ep : ℝ), 0 ≤ ep → ep < 1 → CountAt ρ ep → (1 - (1 + ep) / (1 - ep) * (max 0 (badBound g₁ (Fintype.card ι₁) m N ((min q d : ℕ) : ℝ)) + max 0 (badBound g₂ (Fintype.card ι₂) m N ((min q d : ℕ) : ℝ)))) * (rk ρ (tens2 (tens fun v => (L₁ v).e) (tens fun v => (L₂ v).e)) : ℝ) ≤ (rk ρ (conv (tens2 (eGood τ₁ ch₁) (eGood τ₂ ch₂)) (tens2 (tens fun v => (L₁ v).e) (tens fun v => (L₂ v).e))) : ℝ) := by
  intro g₁ g₂ _ _ N m q d ι₁ ι₂ _ _ hN ok₁ ok₂ L₁ L₂ τ₁ τ₂ s₁ s₂ ch₁ ch₂ M _ _ _ ρ ep h0 h1 hc
  obtain ⟨c, -, hc⟩ := hc
  obtain ⟨pE₁, u₁⟩ := level_proj g₁ N ι₁ L₁
  obtain ⟨pE₂, u₂⟩ := level_proj g₂ N ι₂ L₂
  obtain ⟨pA₁, c₁⟩ := GlobalTheory.T.goodTupleProjector_isProj_central g₁ N m ι₁ τ₁ ch₁ s₁
  obtain ⟨pA₂, c₂⟩ := GlobalTheory.T.goodTupleProjector_isProj_central g₂ N m ι₂ τ₂ ch₂ s₂
  obtain ⟨w₁, hw₁, hW₁⟩ := GlobalTheory.T.badLabelTuple_weight_le_bound g₁ N m q d ι₁ L₁ τ₁ ch₁ hN ok₁ s₁
  obtain ⟨w₂, hw₂, hW₂⟩ := GlobalTheory.T.badLabelTuple_weight_le_bound g₂ N m q d ι₂ L₂ τ₂ ch₂ hN ok₂ s₂
  exact abstract_step _ _ M ρ AllUnip AllUnip _ _ _ _ pE₁ pE₂ pA₁ pA₂ c₁ c₂ u₁ u₂ w₁ w₂ _ _ hw₁ hw₂ hW₁ hW₂
    ep c h0 h1 hc

end GlobalTheory.BadShare.ShareThm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CasimirScalarOnModuleGeneratedKilledByLowerStatement
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_scalar_on_module_generated_killedByLower : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (Λ : Ix p q → ℚ) (e : V), e ∈ hwSub act Λ → KilledByLower act e → genSub act {e} = ⊤ → ∀ x, casimir act x = (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • x := by
  first | exact @GlobalTheory.CasimirLowest.casimir_on_generated | exact GlobalTheory.CasimirLowest.casimir_on_generated | (intros; apply GlobalTheory.CasimirLowest.casimir_on_generated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentredHarishChandraParameterIsParamBlattnerStatement
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centredHarishChandraParameter_isParam_blattner : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am → (∀ i, 1 ≤ ap i) → (∀ i, 1 ≤ am i) → IsParam (hcParam n ap am) ∧ blattner (hcParam n ap am) = wtK n ap am ∧ ∀ (i : Fin p) (j : Fin q), hcParam n ap am (Sum.inr j) < hcParam n ap am (Sum.inl i) := by
  first | exact @GlobalTheory.HarmonicParam.hcParam_isParam_blattner | exact GlobalTheory.HarmonicParam.hcParam_isParam_blattner | (intros; apply GlobalTheory.HarmonicParam.hcParam_isParam_blattner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinPeriodicWeightsIsModularForm
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisPer

theorem per_val {N : ℕ} [NeZero N] (a : ℤ → ℂ) (ha : ∀ x, a (x + N) = a x) (n : ℤ) :
    a n = a (((n : ZMod N).val : ℕ) : ℤ) := by
  have hp : Function.Periodic a (N : ℤ) := ha
  rw [ZMod.val_intCast]
  have := hp.int_mul (n / N) (n % N)
  simp only [Int.cast_id] at this
  rw [← this]
  congr 1
  have := Int.mul_ediv_add_emod n N
  linarith [mul_comm (N : ℤ) (n / N)]

theorem sum_range_zmod {N : ℕ} [NeZero N] (g : ZMod N → ℂ) :
    ∑ y ∈ Finset.range N, g (y : ZMod N) = ∑ z : ZMod N, g z := by
  refine Finset.sum_bij' (fun y _ => (y : ZMod N)) (fun z _ => z.val) (by simp)
    (fun z _ => by simpa using ZMod.val_lt z) (fun y hy => ZMod.val_cast_of_lt (Finset.mem_range.1 hy))
    (fun z _ => ZMod.natCast_zmod_val z) (fun _ _ => rfl)

def invF {N : ℕ} [NeZero N] (a : ℤ → ℂ) (y : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ x : ZMod N, a (x.val : ℤ) * ZMod.stdAddChar (-(x * y))

theorem hat_invF {N : ℕ} [NeZero N] (a : ℤ → ℂ) (ha : ∀ x, a (x + N) = a x) (d : ℤ) :
    hat (invF (N := N) a) d = a d := by
  unfold hat
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have e1 : ∀ y : ℕ, cexp (2 * π * Complex.I * (y * d) / N) = ZMod.stdAddChar ((y : ZMod N) * (d : ZMod N)) := by
    intro y
    have := ZMod.stdAddChar_coe (N := N) ((y : ℤ) * d)
    push_cast at this
    rw [← this]
  simp_rw [e1]
  rw [sum_range_zmod (fun z => invF a z * ZMod.stdAddChar (z * (d : ZMod N)))]
  unfold invF
  simp_rw [mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have e2 : ∀ x y : ZMod N, a (x.val : ℤ) * ZMod.stdAddChar (-(x * y)) * ZMod.stdAddChar (y * (d : ZMod N))
      = a (x.val : ℤ) * ZMod.stdAddChar (y * ((d : ZMod N) - x)) := by
    intro x y
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [e2]
  simp_rw [← Finset.mul_sum]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar N)]
  simp_rw [ZMod.card, Nat.cast_ite, Nat.cast_zero, sub_eq_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ (d : ZMod N) (fun x => a (x.val : ℤ) * (N : ℂ))]
  simp only [Finset.mem_univ, if_true]
  rw [← per_val a ha d]
  field_simp

theorem invF_twist {N : ℕ} [NeZero N] (a : ℤ → ℂ) (ha : ∀ x, a (x + N) = a x) (d : ℤ) (c : ℂ)
    (hd : IsCoprime d (N : ℤ)) (hmul : ∀ x, a (x * d) = c * a x) (y : ZMod N) :
    invF (N := N) a y = c * invF (N := N) a (y * (d : ZMod N)) := by
  obtain ⟨u, v, huv⟩ := hd
  have hu : (u : ZMod N) * (d : ZMod N) = 1 := by
    have := congrArg (fun t : ℤ => (t : ZMod N)) huv
    simpa using this
  let U : (ZMod N)ˣ := ⟨(d : ZMod N), (u : ZMod N), by rw [mul_comm]; exact hu, hu⟩
  unfold invF
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  have e : ∀ x : ZMod N, c * ((N : ℂ)⁻¹ * (a (x.val : ℤ) * ZMod.stdAddChar (-(x * (y * (d : ZMod N))))))
      = (N : ℂ)⁻¹ * (a ((x * (d : ZMod N)).val : ℤ) * ZMod.stdAddChar (-((x * (d : ZMod N)) * y))) := by
    intro x
    have h1 : a ((x * (d : ZMod N)).val : ℤ) = c * a (x.val : ℤ) := by
      rw [← hmul, per_val a ha ((x.val : ℤ) * d)]
      congr 3
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [h1]
    have h2 : -(x * (y * (d : ZMod N))) = -((x * (d : ZMod N)) * y) := by ring
    rw [h2]; ring
  exact (Fintype.sum_equiv (Units.mulRight U) _ _ e).symm

end GlobalTheory.EisPer

end

open GlobalTheory.EisPer in
theorem GlobalTheory.eis_periodic_weights : ∀ (j L₁ L₂ : ℕ) (a b χ₁ χ₂ : ℤ → ℂ), 1 ≤ j → 0 < L₁ → 0 < L₂ → a 0 = 0 → (∀ x, a (x + L₁) = a x) → (∀ x, b (x + L₂) = b x) → (∀ d : ℤ, IsCoprime d (L₁ * L₂ : ℕ) → (∀ x, a (x * d) = χ₁ d * a x) ∧ ∀ x, b (x * d) = χ₂ d * b x) → χ₁ (-1) * χ₂ (-1) = (-1) ^ j → ∃ c : ℂ, MF j (L₁ * L₂) (fun d => χ₁ d * χ₂ d) (eis j c a b) := by
  intro j L₁ L₂ a b χ₁ χ₂ hj hL₁ hL₂ ha0 ha hb hχ hpar
  haveI : NeZero L₁ := ⟨hL₁.ne'⟩
  have hhat : hat (invF (N := L₁) a) = a := funext (hat_invF a ha)
  obtain ⟨c, hc, -⟩ := GlobalTheory.T.eisenstein_latticeFunction_isModularFormCoeffSeq j L₁ L₂ b χ₁ χ₂ (invF (N := L₁) a) hj hL₁ hL₂
    (by rw [hhat]; exact ha0) hb
    (fun d hd => ⟨fun y => invF_twist a ha d (χ₁ d)
      (by
        have : IsCoprime d ((L₁ : ℤ) * (L₂ : ℤ)) := by exact_mod_cast hd
        exact this.of_mul_right_left) (hχ d hd).1 y, (hχ d hd).2⟩) hpar
  exact ⟨c, by rw [hhat] at hc; exact hc⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraDecompositionCocycleStatement
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eichlerShimura_decomposition_cocycle : ∀ (N M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → Γ ≤ CongruenceSubgroup.Gamma1 N → Odd k → 3 ≤ k → ∀ z ∈ Z1 Γ (k - 2), ∃ (f : ModularForm Γ (k : ℤ)) (h : CuspForm Γ (k : ℤ)), z - per Γ (k - 2) ⇑f - cj (per Γ (k - 2) ⇑h) ∈ B1 Γ (k - 2) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.EichlerShimura.exists_per_add_cj_per | exact GlobalTheory.HeckeFamilyMatrices.EichlerShimura.exists_per_add_cj_per | (intros; apply GlobalTheory.HeckeFamilyMatrices.EichlerShimura.exists_per_add_cj_per <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEquivariantTensorMapOfCyclicCommutingStatement
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_tensor_map_of_cyclic_commuting : ∀ (p q r s : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ V) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ V), (∀ Y Z, a₁ Y * a₂ Z = a₂ Z * a₁ Y) → ∀ (M₁ : GKMod p q) (M₂ : GKMod r s) (i₁ : M₁.V →ₗ[ℂ] V) (i₂ : M₂.V →ₗ[ℂ] V), (∀ Z x, i₁ (M₁.act Z x) = a₁ Z (i₁ x)) → (∀ Z y, i₂ (M₂.act Z y) = a₂ Z (i₂ y)) → ∀ (x₀ : M₁.V) (y₀ : M₂.V), genSub M₁.act {x₀} = ⊤ → genSub M₂.act {y₀} = ⊤ → i₁ x₀ = i₂ y₀ → ∃ I : M₁.V ⊗[ℂ] M₂.V →ₗ[ℂ] V, (∀ Z x y, a₁ Z (I (x ⊗ₜ y)) = I (M₁.act Z x ⊗ₜ y)) ∧ (∀ Z x y, a₂ Z (I (x ⊗ₜ y)) = I (x ⊗ₜ M₂.act Z y)) ∧ (∀ x, I (x ⊗ₜ y₀) = i₁ x) ∧ ∀ y, I (x₀ ⊗ₜ y) = i₂ y := by
  first | exact @GlobalTheory.FockBilin.exists_bilin | exact GlobalTheory.FockBilin.exists_bilin | (intros; apply GlobalTheory.FockBilin.exists_bilin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntertwinerMapHighestWeightVectorCompactStatement
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intertwiner_map_highestWeightVector_compact : ∀ (n : ℕ) (M M' : GKMod n 0) (Λ : Ix n 0 → ℚ) (v : M.V) (v' : M'.V), IrrGK M → IrrGK M' → IsHW M.act Λ v → IsHW M'.act Λ v' → ∃ f : M.V →ₗ[ℂ] M'.V, f v = v' ∧ ∀ Z x, f (M.act Z x) = M'.act Z (f x) := by
  first | exact @GlobalTheory.exists_intertwiner_map_highestVector | exact GlobalTheory.exists_intertwiner_map_highestVector | (intros; apply GlobalTheory.exists_intertwiner_map_highestVector <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubrepClosureAnalyticVectorsStatement
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subrep_closure_analytic_vectors : ∀ (p q : ℕ) (T : GrpData p q), Subgroup.closure (T.expt '' upq p q) = ⊤ → ∀ (πU : URep T) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (E : V →ₗ[ℂ] πU.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E x)) (E (act Y x)) 0) → (∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ, ‖E ((act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → ∃ (σ : URep T) (j : V →ₗ[ℂ] σ.H) (J : σ.H →ₗᵢ[ℂ] πU.H), Dense (Set.range j) ∧ (∀ x, J (j x) = E x) ∧ (∀ g y, J (σ.π g y) = πU.π g (J y)) ∧ (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (act Y x)) 0) := by
  first | exact @GlobalTheory.AnalyticClosure.exists_subrep_closure | exact GlobalTheory.AnalyticClosure.exists_subrep_closure | (intros; apply GlobalTheory.AnalyticClosure.exists_subrep_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockTensorIntertwinerUniqueAndRangeStatement
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_tensor_intertwiner_unique_and_range : ∀ (p q n : ℕ) (T0 : GrpData (p * n + q * 0) (p * 0 + q * n)) (T1 : GrpData p q) (T2 : GrpData n 0) (F : FockData T0 T1 T2) (M₁ : GKMod p q) (W : Submodule ℂ M₁.V) (M : GKMod n 0) (I : M₁.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (e₀ : W) (v₀ : M.V), genSub M₁.act (W : Set M₁.V) = ⊤ → KStable M₁.act W → (∀ N : Submodule ℂ M₁.V, N ≤ W → KStable M₁.act N → N = ⊥ ∨ N = W) → IrrGK M → e₀ ≠ 0 → v₀ ≠ 0 → IsGIntw F M₁ M I → (∀ io', IsKIntw F M₁ W M io' → io' (e₀ ⊗ₜ v₀) = I ((e₀ : M₁.V) ⊗ₜ v₀) → io' = I ∘ₗ TensorProduct.map W.subtype LinearMap.id) ∧ (∀ I', IsGIntw F M₁ M I' → (∀ (e : W) (v : M.V), I' ((e : M₁.V) ⊗ₜ v) = I ((e : M₁.V) ⊗ₜ v)) → I' = I) ∧ ∀ v : M.V, Set.range (fun x : M₁.V => I (x ⊗ₜ v)) = (genSub F.act1 (Set.range fun e : W => I ((e : M₁.V) ⊗ₜ v)) : Set (Pol p q n 0)) := by
  first | exact @GlobalTheory.FockUniq.intertwiner_unique_and_range | exact GlobalTheory.FockUniq.intertwiner_unique_and_range | (intros; apply GlobalTheory.FockUniq.intertwiner_unique_and_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTqSemisimpleCuspFormsGamma1Statement
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTq_semisimple_cuspForms_gamma1 : ∀ (N k q : ℕ) (σ : SL(2, ℤ)), 5 ≤ N → 3 ≤ k → q.Prime → ¬ q ∣ N → IsDiam N 1 (q : ZMod N) σ → ∀ (f : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ)) (c : ℂ) (n : ℕ), (fun F => TqF (k : ℤ) q σ F - c • F)^[n] ⇑f = 0 → TqF (k : ℤ) q σ ⇑f = c • ⇑f := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.SemisimpleLevelOne.tq_semisimple | exact GlobalTheory.HeckeFamilyMatrices.SemisimpleLevelOne.tq_semisimple | (intros; apply GlobalTheory.HeckeFamilyMatrices.SemisimpleLevelOne.tq_semisimple <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnStripUnfoldedRankinIntegrand
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem strip_integrable_rankin : ∀ (k e L N : ℕ) (ε : DirichletCharacter ℂ N) (h b : ℕ → ℂ) (s : ℝ), k = 2 * e + 1 → 1 ≤ e → 0 < s → 0 < L → N ∣ L → CF k L (ch ε) h → PolyB b → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) → IntegrableOn (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)) strip := by
  intro k e L N ε h b s hk he hs hL hNL hh hb hsum
  obtain ⟨-, hch⟩ := GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hh.1.1
  obtain ⟨-, hcb⟩ := GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb
  obtain ⟨C, hC⟩ := hh.2
  obtain ⟨C', δ, hδ, hdec⟩ := GlobalTheory.T.cuspForm_coeffSeq_exp_decay_at_every_cusp k L N ε h 1 (by omega) hL hNL hh
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_bound_norm_qs_of_one_le_im b hb
  have fcont : Continuous (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)) := by
    refine ((Complex.continuous_conj.comp hch).mul hcb).mul (Complex.continuous_ofReal.comp ?_)
    exact UpperHalfPlane.continuous_im.rpow_const (fun τ => Or.inl τ.im_pos.ne')
  have hnorm : ∀ τ : ℍ, ‖conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)‖ = ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ ((k : ℝ) + s) := by
    intro τ
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos τ.im_pos _)]
  have hsplit : strip = {τ | τ ∈ strip ∧ τ.im < 1} ∪ {τ | τ ∈ strip ∧ 1 ≤ τ.im} := by
    ext τ; simp only [Set.mem_union, Set.mem_setOf_eq]; constructor
    · intro h; rcases lt_or_ge τ.im 1 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (h | h) <;> exact h.1
  have hmre : Measurable (fun τ : ℍ => τ.re) := UpperHalfPlane.continuous_re.measurable
  have hmim : Measurable (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im.measurable
  have hmup : MeasurableSet {τ : ℍ | τ ∈ strip ∧ 1 ≤ τ.im} :=
    ((measurableSet_le measurable_const hmre).inter (measurableSet_lt hmre measurable_const)).inter
      (measurableSet_le measurable_const hmim)
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  ·
    have hg : IntegrableOn (fun τ : ℍ => (C * τ.im ^ (s + 1) + ‖qs b τ‖ ^ 2 * τ.im ^ (2 * (e : ℝ) + s)) / 2) {τ | τ ∈ strip ∧ τ.im < 1} :=
      (((GlobalTheory.T.integrableOn_im_rpow_unitStrip_below_one s hs).const_mul C).add (GlobalTheory.T.integrableOn_sq_qExpansion_unitStrip_low e b s he hs hb hsum)).div_const 2
    refine hg.mono' fcont.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
    rw [hnorm]
    have hy := τ.im_pos
    set A := ‖qs h τ‖
    set B := ‖qs b τ‖
    set y := τ.im
    have e1 : y ^ (((k : ℝ) + 1 + s) / 2) * y ^ (((k : ℝ) + 1 + s) / 2) = y ^ k * y ^ (s + 1) := by
      rw [← Real.rpow_add hy, ← Real.rpow_natCast, ← Real.rpow_add hy]; congr 1; ring
    have e2 : y ^ ((2 * (e : ℝ) + s) / 2) * y ^ ((2 * (e : ℝ) + s) / 2) = y ^ (2 * (e : ℝ) + s) := by
      rw [← Real.rpow_add hy]; congr 1; ring
    have e3 : y ^ (((k : ℝ) + 1 + s) / 2) * y ^ ((2 * (e : ℝ) + s) / 2) = y ^ ((k : ℝ) + s) := by
      rw [← Real.rpow_add hy]; congr 1; rw [hk]; push_cast; ring
    have amgm := two_mul_le_add_sq (A * y ^ (((k : ℝ) + 1 + s) / 2)) (B * y ^ ((2 * (e : ℝ) + s) / 2))
    have hCb : A ^ 2 * y ^ k ≤ C := hC τ
    have hp : 0 ≤ y ^ (s + 1) := (Real.rpow_pos_of_pos hy _).le
    have : A ^ 2 * (y ^ k * y ^ (s + 1)) ≤ C * y ^ (s + 1) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCb hp
    have h1 : 2 * (A * y ^ (((k : ℝ) + 1 + s) / 2)) * (B * y ^ ((2 * (e : ℝ) + s) / 2)) = 2 * (A * B * y ^ ((k : ℝ) + s)) := by rw [← e3]; ring
    have h2 : (A * y ^ (((k : ℝ) + 1 + s) / 2)) ^ 2 = A ^ 2 * (y ^ k * y ^ (s + 1)) := by rw [← e1]; ring
    have h3 : (B * y ^ ((2 * (e : ℝ) + s) / 2)) ^ 2 = B ^ 2 * y ^ (2 * (e : ℝ) + s) := by rw [← e2]; ring
    rw [h1, h2, h3] at amgm
    linarith
  ·
    have hg := (GlobalTheory.T.integrableOn_im_rpow_mul_exp_unitStrip_one_le ((k : ℝ) / 2 + s) (δ / 2) (by linarith)).const_mul (Real.sqrt C' * M)
    refine hg.mono' fcont.aestronglyMeasurable ((ae_restrict_iff' hmup).2 (Eventually.of_forall fun τ hτ => ?_))
    rw [hnorm]
    have hy := τ.im_pos
    have hy1 : 1 ≤ τ.im := hτ.2
    have hd := hdec τ (by linarith)
    rw [one_smul] at hd
    have hB := hM τ hy1
    set A := ‖qs h τ‖
    set B := ‖qs b τ‖
    set y := τ.im
    have hA0 : 0 ≤ A := norm_nonneg _
    have hB0 : 0 ≤ B := norm_nonneg _
    have hyk : 0 ≤ y ^ ((k : ℝ) / 2) := (Real.rpow_pos_of_pos hy _).le
    have hsq : (A * y ^ ((k : ℝ) / 2)) ^ 2 = A ^ 2 * y ^ k := by
      rw [mul_pow, ← Real.rpow_natCast (y ^ ((k : ℝ) / 2)), ← Real.rpow_mul hy.le, ← Real.rpow_natCast y k]
      congr 2; push_cast; ring
    have hAy : A * y ^ ((k : ℝ) / 2) ≤ Real.sqrt C' * Real.exp (-(δ / 2) * y) := by
      have := Real.sqrt_le_sqrt hd
      rw [← hsq, Real.sqrt_sq (mul_nonneg hA0 hyk), Real.sqrt_mul' _ (Real.exp_pos _).le] at this
      convert this using 2
      rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]; congr 1; ring
    have hsplitpow : y ^ ((k : ℝ) + s) = y ^ ((k : ℝ) / 2) * y ^ ((k : ℝ) / 2 + s) := by
      rw [← Real.rpow_add hy]; congr 1; ring
    have hr : 0 ≤ y ^ ((k : ℝ) / 2 + s) := (Real.rpow_pos_of_pos hy _).le
    calc A * B * y ^ ((k : ℝ) + s) = (A * y ^ ((k : ℝ) / 2)) * B * y ^ ((k : ℝ) / 2 + s) := by rw [hsplitpow]; ring
      _ ≤ (Real.sqrt C' * Real.exp (-(δ / 2) * y)) * M * y ^ ((k : ℝ) / 2 + s) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul hAy hB hB0 (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)) hr
      _ = Real.sqrt C' * M * (y ^ ((k : ℝ) / 2 + s) * Real.exp (-(δ / 2) * y)) := by ring

end GlobalTheory.EisM
end

