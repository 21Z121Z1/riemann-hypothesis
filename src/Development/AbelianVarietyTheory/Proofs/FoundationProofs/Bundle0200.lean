import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0560
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0083
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0193
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0196
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0053

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BadLabelTupleWeightLeBoundStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.badLabelTuple_weight_le_bound : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (m q d : ℕ) (ι : Type) [Fintype ι] (L : ι → Lev g N) (τ : ι → (ZMod g)[X] → GG g N → ℂ) (ch : ι → Fin m → (ZMod g)ˣ), 100000 ≤ N → PrimeOK g q d → (∀ v, IsSeries (τ v)) → ∃ w : ℝ, conv (dirac - eGood τ ch) (tens fun v => (L v).e) 1 = (w : ℂ) * (tens fun v => (L v).e) 1 ∧ w ≤ badBound g (Fintype.card ι) m N ((min q d : ℕ) : ℝ) := by
  first | exact @GlobalTheory.BadShare.badWeight_le | exact GlobalTheory.BadShare.badWeight_le | (intros; apply GlobalTheory.BadShare.badWeight_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CasimirScalarOnModuleGeneratedKilledByLower
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.CasimirLowest

open GlobalTheory.CasimirHighest

theorem casimir_on_vector {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) (Λ : Ix p q → ℚ) (e : V)
    (hv : e ∈ hwSub act Λ) (hk : KilledByLower act e) :
    casimir act e = (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) +
      ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • e := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv
  obtain ⟨hw, hr⟩ := hv
  have h1 := casimir_on_highest_rat (fun i j : Fin p => act (Eab (.inl i) (.inl j)))
    (fun i j => by simpa using act_Eab_comm h (.inl i) (.inl j) (.inl j) (.inl i)) e
    (fun i => Λ (.inl i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
  have h2 := casimir_on_highest_rat (fun i j : Fin q => act (Eab (.inr i) (.inr j)))
    (fun i j => by simpa using act_Eab_comm h (.inr i) (.inr j) (.inr j) (.inr i)) e
    (fun i => Λ (.inr i)) (fun i j hij => hr _ _ hij) (fun i => hw _)
  have h3 : ∀ (a : Fin p) (b : Fin q),
      act (Eab (.inl a) (.inr b)) (act (Eab (.inr b) (.inl a)) e) = 0 := by
    intro a b; rw [hk a b, map_zero]
  have h4 : ∀ (b : Fin q) (a : Fin p),
      act (Eab (.inr b) (.inl a)) (act (Eab (.inl a) (.inr b)) e) =
        ((Λ (.inr b) - Λ (.inl a) : ℚ) : ℂ) • e := by
    intro b a
    have h5 := congrArg (fun f : Module.End ℂ V => f e)
      (act_Eab_comm h (.inr b) (.inl a) (.inl a) (.inr b))
    simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply, h3, sub_zero, hw] at h5
    rw [h5, Rat.cast_sub, sub_smul]
  have h6 : ∑ b : Fin q, ∑ a : Fin p, ((Λ (.inr b) - Λ (.inl a) : ℚ) : ℂ) • e =
      ((∑ b : Fin q, ∑ a : Fin p, (Λ (.inr b) - Λ (.inl a)) : ℚ) : ℂ) • e := by
    simp only [Rat.cast_sum, Finset.sum_smul]
  simp only [casimir, LinearMap.sum_apply, LinearMap.add_apply, Module.End.mul_apply,
    Fintype.sum_sum_type, Finset.sum_add_distrib, h3, h4, Finset.sum_const_zero, zero_add]
  rw [h1, h2, h6, ← add_smul, ← add_smul, ← Rat.cast_add, ← Rat.cast_add]
  congr 2
  have e1 : ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) =
      ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - 1 - 2 * (i : ℕ)) - q * ∑ i : Fin p, Λ (Sum.inl i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ)) =
      ∑ j : Fin q, Λ (Sum.inr j) * ((q : ℚ) - 1 - 2 * (j : ℕ)) + p * ∑ j : Fin q, Λ (Sum.inr j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ b : Fin q, ∑ a : Fin p, (Λ (.inr b) - Λ (.inl a)) =
      p * ∑ j : Fin q, Λ (Sum.inr j) - q * ∑ i : Fin p, Λ (Sum.inl i) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.mul_sum]
  rw [e1, e2, e3]
  ring

theorem casimir_on_generated : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (Λ : Ix p q → ℚ) (e : V), e ∈ hwSub act Λ → KilledByLower act e → genSub act {e} = ⊤ → ∀ x, casimir act x = (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) + ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) • x := by
  intro p q V _ _ act h Λ e hv hk hg x
  have he := casimir_on_vector h Λ e hv hk
  generalize (((∑ a, Λ a ^ 2 + ∑ i : Fin p, Λ (Sum.inl i) * ((p : ℚ) - q - 1 - 2 * (i : ℕ)) +
      ∑ j : Fin q, Λ (Sum.inr j) * ((p : ℚ) + q - 1 - 2 * (j : ℕ))) : ℚ) : ℂ) = c at he ⊢
  have hc := (casimir_central_and_highest p q V act h).1
  have hle : genSub act {e} ≤ LinearMap.ker (casimir act - c • LinearMap.id) := by
    refine sInf_le ⟨?_, ?_⟩
    · rintro y rfl
      simp [he]
    · intro Z y hy
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        sub_eq_zero] at hy ⊢
      have := congrArg (fun f : Module.End ℂ V => f y) (hc Z)
      simp only [Module.End.mul_apply] at this
      rw [this, hy, map_smul]
  have hx := hle (hg ▸ Submodule.mem_top : x ∈ genSub act {e})
  simpa [sub_eq_zero] using hx

end GlobalTheory.CasimirLowest
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentredHarishChandraParameterIsParamBlattner
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.HarmonicParam

variable {p q : ℕ}

theorem card_filter_sum (P : Ix p q → Prop) [DecidablePred P] (A : Finset (Fin p)) (B : Finset (Fin q))
    (hA : ∀ i, P (Sum.inl i) ↔ i ∈ A) (hB : ∀ j, P (Sum.inr j) ↔ j ∈ B) :
    (Finset.univ.filter P).card = A.card + B.card := by
  rw [← Finset.card_disjSum]
  congr 1
  ext x
  cases x <;> simp [hA, hB]

theorem rhoNC_of_strictAnti (lam : Ix p q → ℚ) (h1 : StrictAnti fun i => lam (Sum.inl i))
    (h2 : StrictAnti fun j => lam (Sum.inr j)) (h3 : ∀ i j, lam (Sum.inr j) < lam (Sum.inl i)) :
    (∀ i : Fin p, rhoNC lam (Sum.inl i) = (q : ℚ) / 2 - ((p : ℚ) - 1 - 2 * (i.1 : ℚ)) / 2) ∧
    (∀ j : Fin q, rhoNC lam (Sum.inr j) = -(p : ℚ) / 2 - ((q : ℚ) - 1 - 2 * (j.1 : ℚ)) / 2) := by
  have h1' : ∀ i i', lam (Sum.inl i) < lam (Sum.inl i') ↔ i' < i := fun i i' => h1.lt_iff_gt
  have h2' : ∀ i i', lam (Sum.inr i) < lam (Sum.inr i') ↔ i' < i := fun i i' => h2.lt_iff_gt
  have h4 : ∀ i j, ¬ lam (Sum.inl i) < lam (Sum.inr j) := fun i j => (h3 i j).not_gt
  constructor
  · intro i
    unfold rhoNC
    rw [card_filter_sum _ ∅ Finset.univ (by simp [sameBlock]) (by simp [sameBlock, h3]),
      card_filter_sum _ ∅ ∅ (by simp [sameBlock]) (by simp [sameBlock, h4]),
      card_filter_sum _ (Finset.Ioi i) ∅ (by simp [sameBlock, h1']) (by simp [sameBlock]),
      card_filter_sum _ (Finset.Iio i) ∅ (by simp [sameBlock, h1']) (by simp [sameBlock])]
    have hi : i.1 + 1 ≤ p := i.2
    simp only [Finset.card_empty, Finset.card_univ, Fintype.card_fin, Fin.card_Ioi, Fin.card_Iio,
      Nat.sub_sub, zero_add, add_zero]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  · intro i
    unfold rhoNC
    rw [card_filter_sum _ ∅ ∅ (by simp [sameBlock, h4]) (by simp [sameBlock]),
      card_filter_sum _ Finset.univ ∅ (by simp [sameBlock, h3]) (by simp [sameBlock]),
      card_filter_sum _ ∅ (Finset.Ioi i) (by simp [sameBlock]) (by simp [sameBlock, h2']),
      card_filter_sum _ ∅ (Finset.Iio i) (by simp [sameBlock]) (by simp [sameBlock, h2'])]
    have hi : i.1 + 1 ≤ q := i.2
    simp only [Finset.card_empty, Finset.card_univ, Fintype.card_fin, Fin.card_Ioi, Fin.card_Iio,
      Nat.sub_sub, zero_add, add_zero]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring

theorem hcParam_isParam_blattner : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ),
    Antitone ap → Antitone am → (∀ i, 1 ≤ ap i) → (∀ i, 1 ≤ am i) →
    IsParam (hcParam n ap am) ∧ blattner (hcParam n ap am) = wtK n ap am ∧
    ∀ (i : Fin p) (j : Fin q), hcParam n ap am (Sum.inr j) < hcParam n ap am (Sum.inl i) := by
  intro p q n hn ap am hap ham _ _
  have hn' : (p : ℚ) + q + 1 ≤ n := by exact_mod_cast hn
  have h1 : StrictAnti fun i => hcParam n ap am (Sum.inl i) := by
    intro i j hij
    have a : (ap j : ℚ) ≤ ap i := by exact_mod_cast hap hij.le
    have b : (i.1 : ℚ) < j.1 := by exact_mod_cast hij
    simp only [hcParam]
    linarith
  have h2 : StrictAnti fun i => hcParam n ap am (Sum.inr i) := by
    intro i j hij
    have a : (am i.rev : ℚ) ≤ am j.rev := by exact_mod_cast ham (Fin.rev_le_rev.2 hij.le)
    have b : (i.1 : ℚ) < j.1 := by exact_mod_cast hij
    simp only [hcParam]
    linarith
  have h3 : ∀ (i : Fin p) (j : Fin q), hcParam n ap am (Sum.inr j) < hcParam n ap am (Sum.inl i) := by
    intro i j
    have a : (0 : ℚ) ≤ ap i := Nat.cast_nonneg _
    have b : (0 : ℚ) ≤ am j.rev := Nat.cast_nonneg _
    have c : (0 : ℚ) ≤ j.1 := Nat.cast_nonneg _
    have d : (i.1 : ℚ) + 1 ≤ p := by exact_mod_cast i.2
    simp only [hcParam]
    linarith
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, h3⟩
  · rintro (a | a) (b | b) h
    · rw [h1.injective h]
    · exact absurd h (h3 a b).ne'
    · exact absurd h (h3 b a).ne
    · rw [h2.injective h]
  · rintro (a | a) (b | b) h
    · exact h1 h
    · exact h.elim
    · exact h.elim
    · exact h2 h
  · rintro (a | a)
    · exact ⟨2 * (ap a) + 2 * (p - (a.1 + 1)) + (n - p - q + 1), by simp only [hcParam]; push_cast; ring⟩
    · exact ⟨-2 * (am a.rev) - 2 * (a.1 + 1) - (n - p - q - 1), by simp only [hcParam]; push_cast; ring⟩
  · rintro (a | a) (b | b)
    · exact ⟨ap a - ap b - a.1 + b.1, by simp only [hcParam]; push_cast; ring⟩
    · exact ⟨ap a + (p - (a.1 + 1)) + am b.rev + (b.1 + 1) + (n - p - q),
        by simp only [hcParam]; push_cast; ring⟩
    · exact ⟨-(ap b + (p - (b.1 + 1)) + am a.rev + (a.1 + 1) + (n - p - q)),
        by simp only [hcParam]; push_cast; ring⟩
    · exact ⟨am b.rev - am a.rev - a.1 + b.1, by simp only [hcParam]; push_cast; ring⟩
  · obtain ⟨r1, r2⟩ := rhoNC_of_strictAnti _ h1 h2 h3
    funext a
    rcases a with a | a
    · simp only [blattner, r1, hcParam, wtK]
      ring
    · simp only [blattner, r2, hcParam, wtK]
      ring

end GlobalTheory.HarmonicParam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormCoeffSeqExpDecayAtEveryCuspStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_coeffSeq_exp_decay_at_every_cusp : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ) (γ : SL(2, ℤ)), 1 ≤ k → 0 < L → N ∣ L → CF k L (ch ε) a → ∃ C δ : ℝ, 0 < δ ∧ ∀ τ : ℍ, 1 / 2 ≤ τ.im → ‖qs a (γ • τ)‖ ^ 2 * (γ • τ).im ^ k ≤ C * Real.exp (-δ * τ.im) := by
  first | exact @GlobalTheory.EisM.cusp_decay | exact GlobalTheory.EisM.cusp_decay | (intros; apply GlobalTheory.EisM.cusp_decay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormLseriesExtendsEntireStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_lseries_extends_entire : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → CF k L (ch ε) g → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re → LSeriesSummable g s ∧ LSeries g s = Λ s := by
  first | exact @GlobalTheory.EisM.lseries_cusp_entire | exact GlobalTheory.EisM.lseries_cusp_entire | (intros; apply GlobalTheory.EisM.lseries_cusp_entire <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DilMonomial
section
noncomputable section
namespace GlobalTheory.FockDecay
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix

def rectDiag (p q : ℕ) (f : ℕ → ℝ) : Matrix (Fin p) (Fin q) ℂ :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then ((f i : ℝ) : ℂ) else 0

def diagP (p q : ℕ) (σ : ℕ → ℝ) : Mat p q :=
  Matrix.fromBlocks 0 (rectDiag p q σ) (rectDiag p q σ)ᴴ 0

def tanhDiag (p q : ℕ) (σ : ℕ → ℝ) (t : ℝ) : Mat p q :=
  Matrix.diagonal fun a => (if a.isLeft then 1 else -1) *
    ((σ (posIx a) * Real.tanh (t * σ (posIx a)) : ℝ) : ℂ)

def hypMat (p q : ℕ) (σ : ℕ → ℝ) (t : ℝ) : Mat p q :=
  Matrix.fromBlocks (Matrix.diagonal fun i : Fin p => ((Real.cosh (t * σ i) : ℝ) : ℂ))
    (rectDiag p q fun i => Real.sinh (t * σ i)) (rectDiag p q fun i => Real.sinh (t * σ i))ᴴ
    (Matrix.diagonal fun j : Fin q => ((Real.cosh (t * σ j) : ℝ) : ℂ))

def dil {p q : ℕ} (n : ℕ) (u : Ix p q → ℝ) : Pol p q n 0 →ₗ[ℂ] Pol p q n 0 :=
  ((Real.exp ((∑ l : Ln p q n 0, u l.1) / 2) : ℝ) : ℂ) •
    (MvPolynomial.aeval fun l : Ln p q n 0 =>
      (MvPolynomial.C ((Real.exp (u l.1) : ℝ) : ℂ) * MvPolynomial.X l : Pol p q n 0)).toLinearMap

theorem diagonalElement_mem (p q : ℕ) (σ : ℕ → ℝ) : diagP p q σ ∈ pR p q := pY_mem (rectDiag p q σ)

theorem dil_monomial {p q n : ℕ} (u : Ix p q → ℝ) (α : Ln p q n 0 →₀ ℕ) (c : ℂ) :
    dil n u (MvPolynomial.monomial α c) =
      ((Real.exp (∑ l : Ln p q n 0, ((α l : ℝ) + 1 / 2) * u l.1) : ℝ) : ℂ) • MvPolynomial.monomial α c := by
  have h : Real.exp (∑ l : Ln p q n 0, ((α l : ℝ) + 1 / 2) * u l.1) =
      Real.exp ((∑ l : Ln p q n 0, u l.1) / 2) * ∏ l : Ln p q n 0, Real.exp (u l.1) ^ α l := by
    simp only [← Real.exp_nat_mul, ← Real.exp_sum, ← Real.exp_add, Finset.sum_div, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [h, Complex.ofReal_mul, mul_smul, dil, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
    MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), MvPolynomial.monomial_eq,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  congr 1
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, MvPolynomial.smul_eq_C_mul,
    MvPolynomial.algebraMap_eq, Complex.ofReal_prod, Complex.ofReal_pow]
  ring

theorem dil_dil_neg {p q n : ℕ} (u : Ix p q → ℝ) (Φ : Pol p q n 0) : dil n u (dil n (-u) Φ) = Φ := by
  induction Φ using MvPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ]
  | monomial α c =>
    rw [dil_monomial, map_smul, dil_monomial, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add,
      ← Finset.sum_add_distrib]
    simp

theorem dil_zero {p q n : ℕ} (Φ : Pol p q n 0) : dil n 0 Φ = Φ := by
  induction Φ using MvPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, hP, hQ]
  | monomial α c => rw [dil_monomial]; simp

end GlobalTheory.FockDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeFunctionIsModularFormCoeffSeqStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_latticeFunction_isModularFormCoeffSeq : ∀ (j L₁ L₂ : ℕ) (b χ₁ χ₂ : ℤ → ℂ) (φ : ZMod L₁ → ℂ), 1 ≤ j → 0 < L₁ → 0 < L₂ → hat φ 0 = 0 → (∀ x, b (x + L₂) = b x) → (∀ d : ℤ, IsCoprime d (L₁ * L₂ : ℕ) → (∀ y, φ y = χ₁ d * φ (y * d)) ∧ ∀ x, b (x * d) = χ₂ d * b x) → χ₁ (-1) * χ₂ (-1) = (-1) ^ j → ∃ c : ℂ, MF j (L₁ * L₂) (fun d => χ₁ d * χ₂ d) (eis j c (hat φ) b) ∧ ∀ τ : ℍ, lat j 0 L₁ (0, 1) (latF L₁ b φ) τ = 2 * (-2 * π * Complex.I / L₁) ^ j / (j - 1).factorial * qs (eis j c (hat φ) b) τ := by
  first | exact @GlobalTheory.EisForm.eis_latF_mf | exact GlobalTheory.EisForm.eis_latF_mf | (intros; apply GlobalTheory.EisForm.eis_latF_mf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraDecompositionCocycle
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.EichlerShimura

theorem exists_of_finrank_le {A A' V : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ A] [FiniteDimensional ℂ A']
    (Z B : Submodule ℂ V) [FiniteDimensional ℂ Z] (hBZ : B ≤ Z) (P : A → V) (Q : A' → V)
    (hPa : ∀ x y, P (x + y) = P x + P y) (hQa : ∀ x y, Q (x + y) = Q x + Q y)
    (hPs : ∀ (r : ℝ) x, P ((r : ℂ) • x) = (r : ℂ) • P x) (hQs : ∀ (r : ℝ) x, Q ((r : ℂ) • x) = (r : ℂ) • Q x)
    (hPZ : ∀ x, P x ∈ Z) (hQZ : ∀ x, Q x ∈ Z)
    (hinj : ∀ x y, P x + Q y ∈ B → x = 0 ∧ y = 0)
    (hdim : Module.finrank ℂ Z ≤ Module.finrank ℂ A + Module.finrank ℂ A' + Module.finrank ℂ B) :
    ∀ z ∈ Z, ∃ x y, z - P x - Q y ∈ B := by
  classical
  have : FiniteDimensional ℂ B := Submodule.finiteDimensional_of_le hBZ
  have hPs' : ∀ (r : ℝ) x, P (r • x) = (r : ℂ) • P x := fun r x => hPs r x
  have hQs' : ∀ (r : ℝ) x, Q (r • x) = (r : ℂ) • Q x := fun r x => hQs r x
  have hP0 : P 0 = 0 := by simpa using hPa 0 0
  have hQ0 : Q 0 = 0 := by simpa using hQa 0 0
  let Φ : (A × A') × B →ₗ[ℝ] Z :=
    { toFun := fun p => ⟨P p.1.1 + Q p.1.2 + (p.2 : V),
        Z.add_mem (Z.add_mem (hPZ _) (hQZ _)) (hBZ p.2.2)⟩
      map_add' := fun p q => by
        apply Subtype.ext
        change P (p.1.1 + q.1.1) + Q (p.1.2 + q.1.2) + ((p.2 : V) + q.2) =
          (P p.1.1 + Q p.1.2 + p.2) + (P q.1.1 + Q q.1.2 + q.2)
        rw [hPa, hQa]
        abel
      map_smul' := fun r p => by
        apply Subtype.ext
        change P (r • p.1.1) + Q (r • p.1.2) + (r : ℂ) • (p.2 : V) =
          (r : ℂ) • (P p.1.1 + Q p.1.2 + p.2)
        rw [hPs', hQs', smul_add, smul_add] }
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨x, y⟩, b⟩ h
    have h' : P x + Q y + (b : V) = 0 := congrArg Subtype.val h
    have hmem : P x + Q y ∈ B := by
      rw [eq_neg_of_add_eq_zero_left h']
      exact B.neg_mem b.2
    obtain ⟨rfl, rfl⟩ := hinj x y hmem
    have hb : b = 0 := Subtype.ext (by simpa [hP0, hQ0] using h')
    simp [hb]
  have hle : Module.finrank ℝ Z ≤ Module.finrank ℝ ((A × A') × B) := by
    have hZ : Module.finrank ℝ Z = 2 * Module.finrank ℂ Z := finrank_real_of_complex Z
    have hA : Module.finrank ℝ A = 2 * Module.finrank ℂ A := finrank_real_of_complex A
    have hA' : Module.finrank ℝ A' = 2 * Module.finrank ℂ A' := finrank_real_of_complex A'
    have hB : Module.finrank ℝ B = 2 * Module.finrank ℂ B := finrank_real_of_complex B
    rw [Module.finrank_prod, Module.finrank_prod, hZ, hA, hA', hB]
    omega
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (le_antisymm (LinearMap.finrank_le_finrank_of_injective hΦ) hle)).1 hΦ
  intro z hz
  obtain ⟨⟨⟨x, y⟩, b⟩, hp⟩ := hsurj ⟨z, hz⟩
  refine ⟨x, y, ?_⟩
  have hz' : P x + Q y + (b : V) = z := congrArg Subtype.val hp
  have : z - P x - Q y = b := by rw [← hz']; abel
  rw [this]
  exact b.2

theorem coboundaries_le_cocycles (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : B1 Γ w ≤ Z1 Γ w := by
  intro z hz
  obtain ⟨p, rfl⟩ := LinearMap.mem_range.1 hz
  have hp : (p : ℂ[X]) ∈ degreeLT ℂ (w + 1) := p.2
  refine ⟨fun γ => ?_, fun γ δ => ?_⟩
  · change slP w (mat γ) p - p ∈ degreeLT ℂ (w + 1)
    exact Submodule.sub_mem _ (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w (mat γ) 1 p hp).1 hp
  · change slP w (mat ((γ * δ : Γ) : SL(2, ℤ))) p - p =
      slP w (mat δ) (slP w (mat γ) p - p) + (slP w (mat δ) p - p)
    have hmat : mat ((γ * δ : Γ) : SL(2, ℤ)) = mat γ * mat δ := by simp [mat]
    rw [hmat, (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w (mat γ) (mat δ) p hp).2.1, map_sub]
    abel

theorem integrable_seg {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (n : ℕ) (τ : ℍ) :
    IntervalIntegrable (fun t : ℝ => (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
      (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ n * ((τ : ℂ) - Complex.I)) MeasureTheory.volume 0 1 := by
  have hd := UpperHalfPlane.mdifferentiable_iff.1 hf
  have him : ∀ t ∈ Set.uIcc (0 : ℝ) 1, 0 < (Complex.I + t * ((τ : ℂ) - Complex.I)).im := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    obtain ⟨h0, h1⟩ := ht
    have hτ := τ.im_pos
    have e : (Complex.I + t * ((τ : ℂ) - Complex.I)).im = (1 - t) + t * τ.im := by
      simp [Complex.mul_im]
      ring
    rw [e]
    rcases h1.lt_or_eq with h1 | rfl
    · nlinarith [mul_nonneg h0 hτ.le]
    · simpa using hτ
  have hpath : Continuous fun t : ℝ => Complex.I + t * ((τ : ℂ) - Complex.I) := by fun_prop
  have hc : ContinuousOn (fun t : ℝ => (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)))
      (Set.uIcc 0 1) :=
    hd.continuousOn.comp hpath.continuousOn fun t ht => him t ht
  have hpow : Continuous fun t : ℝ => (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ n := by fun_prop
  exact ((hc.mul hpow.continuousOn).mul continuousOn_const).intervalIntegrable

theorem per_add (Γ : Subgroup SL(2, ℤ)) (w : ℕ) {f g : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) : per Γ w (f + g) = per Γ w f + per Γ w g := by
  have he : ∀ τ : ℍ, eichler w (f + g) τ = eichler w f τ + eichler w g τ := by
    intro τ
    simp only [eichler, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hint : (∫ t in (0 : ℝ)..1, ((f + g) ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
          (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) =
        (∫ t in (0 : ℝ)..1, (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
          (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) +
        (∫ t in (0 : ℝ)..1, (g ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
          (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) := by
      rw [← intervalIntegral.integral_add (integrable_seg hf (w - j) τ) (integrable_seg hg (w - j) τ)]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [Function.comp_apply, Pi.add_apply]
      ring
    rw [hint, mul_add, C_add, add_mul]
  funext γ
  simp only [per, Pi.add_apply, he, map_add]

theorem cj_add {Γ : Type} (x y : Γ → ℂ[X]) : cj (x + y) = cj x + cj y := by
  funext γ
  simp [cj, Polynomial.map_add]

theorem cj_real_smul {Γ : Type} (r : ℝ) (x : Γ → ℂ[X]) : cj ((r : ℂ) • x) = (r : ℂ) • cj x := by
  funext γ
  change ((r : ℂ) • x γ).map (starRingEnd ℂ) = (r : ℂ) • (x γ).map (starRingEnd ℂ)
  rw [Polynomial.map_smul, Complex.conj_ofReal]

theorem exists_per_add_cj_per : ∀ (N M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → 0 < M →
    CongruenceSubgroup.Gamma M ≤ Γ → Γ ≤ CongruenceSubgroup.Gamma1 N → Odd k → 3 ≤ k →
    ∀ z ∈ Z1 Γ (k - 2), ∃ (f : ModularForm Γ (k : ℤ)) (h : CuspForm Γ (k : ℤ)),
      z - per Γ (k - 2) ⇑f - cj (per Γ (k - 2) ⇑h) ∈ B1 Γ (k - 2) := by
  intro N M Γ k hN hM hΓM hΓN hk hk3 z hz
  have : NeZero M := ⟨hM.ne'⟩
  have hfi : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓM
  obtain ⟨hfdM, hfdC, hcount⟩ := GlobalTheory.T.oddWeight_modular_cusp_dimension_lower_bound N M Γ k hN hM hΓM hΓN hk hk3
  obtain ⟨hfdZ, hZ⟩ := GlobalTheory.T.finrank_z1_le_of_le_gamma1_of_finiteIndex N Γ (k - 2) hN hΓN hfi
  have hB := GlobalTheory.T.finrank_b1_eq_of_gamma_le M Γ (k - 2) hM (by omega) hΓM
  have hk2 : 2 ≤ k := by omega
  have hsm := (GlobalTheory.T.eichlerShimura_conj_cocycles_coboundaries_period_smul Γ (k - 2)).2.2
  have hnegper : ∀ g : ℍ → ℂ, per Γ (k - 2) (-g) = -per Γ (k - 2) g := by
    intro g
    simpa using hsm g (-1)
  have hcjneg : ∀ x : Γ → ℂ[X], cj (-x) = -cj x := by
    intro x
    funext γ
    simp [cj, Polynomial.map_neg]
  have key := exists_of_finrank_le (A := ModularForm Γ k) (A' := CuspForm Γ k)
    (Z1 Γ (k - 2)) (B1 Γ (k - 2)) (coboundaries_le_cocycles Γ (k - 2))
    (fun f => per Γ (k - 2) ⇑f) (fun h => -cj (per Γ (k - 2) ⇑h))
    (fun x y => by
      simp only [FunLike.coe_add]
      exact per_add Γ _ (ModularFormClass.holo x) (ModularFormClass.holo y))
    (fun x y => by
      simp only [FunLike.coe_add, per_add Γ _ (ModularFormClass.holo x) (ModularFormClass.holo y), cj_add,
        neg_add])
    (fun r x => by
      simp only [FunLike.coe_smul]
      exact hsm _ _)
    (fun r x => by simp only [FunLike.coe_smul, hsm, cj_real_smul, smul_neg])
    (fun x => (GlobalTheory.T.eichlerPeriodCocycle_mem_cocycles_and_eq Γ k hk2 x).1)
    (fun y => Submodule.neg_mem _
      ((GlobalTheory.T.eichlerShimura_conj_cocycles_coboundaries_period_smul Γ (k - 2)).1 _ (GlobalTheory.T.eichlerPeriodCocycle_mem_cocycles_and_eq Γ k hk2 (ModularFormClass.modularForm y)).1))
    (fun x y hxy => by
      have hxy' : per Γ (k - 2) ⇑x - cj (per Γ (k - 2) ⇑y) ∈ B1 Γ (k - 2) := by
        simpa [sub_eq_add_neg] using hxy
      obtain ⟨f', hf'⟩ := GlobalTheory.T.cuspidal_of_eichlerPeriod_sub_conj_mem_coboundaries N Γ k hN hΓN hfi hk3 x y hxy'
      rw [← hf'] at hxy'
      obtain ⟨h1, h2⟩ := GlobalTheory.T.cuspForms_eq_zero_of_period_sub_conj_coboundary N Γ k hN hΓN hfi hk3 f' y hxy'
      refine ⟨DFunLike.coe_injective ?_, h2⟩
      rw [← hf', h1]
      simp)
    (by
      rw [hB]
      have e : k - 1 = k - 2 + 1 := by omega
      rw [e] at hcount
      rw [Nat.mul_add] at hZ
      omega)
  obtain ⟨f, h, hfh⟩ := key z hz
  refine ⟨f, -h, ?_⟩
  simpa [FunLike.coe_neg, hnegper, hcjneg, sub_eq_add_neg] using hfh

end GlobalTheory.HeckeFamilyMatrices.EichlerShimura
end

