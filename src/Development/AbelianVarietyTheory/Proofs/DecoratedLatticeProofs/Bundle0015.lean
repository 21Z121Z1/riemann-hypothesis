import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0014
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotRedOfMem
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCutoffOfAddCharTranslationInvariantFunctio
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.CharCutoff

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dot_eq_one {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) {n : Type} [Fintype n]
    (R : kˣ) {t y : n → k} (ht : t ∈ box n (c * R⁻¹)) (hy : y ∈ box n R) : ψ (t ⬝ᵥ y) = 1 := by
  apply h.eq_one
  show valuation k (∑ i, t i * y i) ≤ valuation k (c : k)
  refine Valuation.map_sum_le (valuation k) fun i _ => ?_
  have h2 : valuation k (t i * y i) ≤ valuation k (((c * R⁻¹ : kˣ) : k) * R) := by
    rw [map_mul, map_mul]
    exact mul_le_mul' (ht i trivial) (hy i trivial)
  rwa [← Units.val_mul, inv_mul_cancel_right] at h2

theorem exists_dot_ne_one {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) {n : Type} [Fintype n]
    (s : kˣ) {y : n → k} (hy : y ∉ box n s) : ∃ b ∈ box n (c * s⁻¹), ψ (b ⬝ᵥ y) ≠ 1 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, y i ∉ cball s := by
    by_contra hne
    push_neg at hne
    exact hy fun i _ => hne i
  have hcs : c * (c * s⁻¹)⁻¹ = s := by
    rw [_root_.mul_inv_rev, inv_inv, mul_comm s, mul_inv_cancel_left]
  obtain ⟨t, ht, hne⟩ := h.exists_ne_one (c * s⁻¹) (x := y i) (by rwa [hcs])
  refine ⟨Pi.single i t, fun j _ => ?_, ?_⟩
  · by_cases hj : j = i
    · subst hj; simpa using ht
    · simp [Pi.single_eq_of_ne hj, cball]
  · rwa [single_dotProduct]

theorem sum_char {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) {n : Type} [Fintype n]
    (s R : kˣ) (S : Finset (n → k)) (hS : ∀ b ∈ S, b ∈ box n (c * s⁻¹))
    (hU : ∀ a ∈ box n (c * s⁻¹), ∃! b, b ∈ S ∧ a - b ∈ box n (c * R⁻¹)) {y : n → k}
    (hy : y ∈ box n R) :
    ∑ b ∈ S, (ψ (b ⬝ᵥ y) : ℂ) = (box n s).indicator (fun _ => (1 : ℂ)) y * S.card := by
  by_cases hys : y ∈ box n s
  · rw [Set.indicator_of_mem hys, one_mul]
    rw [Finset.sum_congr rfl fun b hb => by rw [dot_eq_one h s (hS b hb) hys, Circle.coe_one]]
    simp
  · rw [Set.indicator_of_notMem hys, zero_mul]
    obtain ⟨a, ha, hne⟩ := exists_dot_ne_one h s hys
    have key := GlobalTheory.T.sum_integralScaledBoxPi_coset_reps_shift_invariant k n (c * R⁻¹) (c * s⁻¹) S hS hU (fun b => (ψ (b ⬝ᵥ y) : ℂ))
      (fun t ht z => by
        rw [add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, dot_eq_one h R ht hy,
          Circle.coe_one, mul_one]) a ha
    simp only [add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, ← Finset.mul_sum] at key
    have h3 : (ψ (a ⬝ᵥ y) : ℂ) - 1 ≠ 0 := fun h4 => hne (Circle.ext (by simpa using sub_eq_zero.mp h4))
    refine (mul_eq_zero.mp ?_).resolve_left h3
    rw [sub_mul, key, one_mul, sub_self]

theorem exists_cutoff_of_char_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (b : I₁ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) → l Φ' = l Φ) → ∀ (Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))) (s : kˣ), ∃ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x, Φ'.1 x = (box I₁ s).indicator (fun _ => (1 : ℂ)) x.2.1 * Φ.1 x) ∧ l Φ = l Φ' := by
  intro k _ _ _ _ ψ hψ h1 I₀ I₁ I₂ _ _ _ M _ _ l hl Φ s
  haveI := t2Space k
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  have hK : IsCompact ((fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => x.2.1) '' tsupport Φ.1) :=
    Φ.2.2.image (by fun_prop)
  obtain ⟨R, hsR, hKR⟩ := GlobalTheory.T.exists_integralScaledBoxPi_superset_of_isCompact k I₁ _ hK s
  have hvr : valuation k ((c * R⁻¹ : kˣ) : k) ≤ valuation k ((c * s⁻¹ : kˣ) : k) := by
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    exact mul_le_mul' le_rfl (inv_anti₀ (by simp [zero_lt_iff]) hsR)
  obtain ⟨S, hS, hU⟩ := GlobalTheory.T.exists_finset_integralScaledBoxPi_coset_reps k I₁ (c * R⁻¹) (c * s⁻¹) hvr
  have hmem : ∀ b : I₁ → k,
      (fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x) ∈
        SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) := fun b => by
    have hcont : Continuous fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => b ⬝ᵥ x.2.1 :=
      continuous_const.dotProduct (continuous_fst.comp continuous_snd)
    have h2 : IsLocallyConstant fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => (ψ (b ⬝ᵥ x.2.1) : ℂ) :=
      (IsLocallyConstant.comp_continuous hc.isLocallyConstant hcont).comp (fun z : Circle => (z : ℂ))
    exact ⟨IsLocallyConstant.mul h2 Φ.2.1, Φ.2.2.mul_left⟩
  let Φb : (I₁ → k) → SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) := fun b => ⟨_, hmem b⟩
  have hlb : ∀ b, l (Φb b) = l Φ := fun b => hl b Φ (Φb b) (fun x => rfl)
  have h0 : (0 : I₁ → k) ∈ box I₁ (c * s⁻¹) := fun i _ => by simp [cball]
  obtain ⟨b0, ⟨hb0, _⟩, _⟩ := hU 0 h0
  have hcard : (S.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨b0, hb0⟩).ne'
  refine ⟨(S.card : ℂ)⁻¹ • ∑ b ∈ S, Φb b, fun x => ?_, ?_⟩
  · simp only [Submodule.coe_smul, Submodule.coe_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    show (S.card : ℂ)⁻¹ * ∑ b ∈ S, (ψ (b ⬝ᵥ x.2.1) : ℂ) * Φ.1 x = _
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ tsupport Φ.1
    · rw [sum_char hc s R S hS hU (hKR ⟨x, hx, rfl⟩), ← mul_assoc, mul_comm ((S.card : ℂ)⁻¹),
        mul_inv_cancel_right₀ hcard]
    · rw [image_eq_zero_of_notMem_tsupport hx]; simp
  · rw [map_smul, map_sum, Finset.sum_congr rfl fun b _ => hlb b, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

end GlobalTheory.CharCutoff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedDepthOneLevelCharOfOneRowFirstBlockStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDepthOneLevel_char_of_one_row_first_block : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (r₀ : r) (h : (P.iter t μ hμ j).J), (∀ a b, a ≠ Sum.inl r₀ → (h : GL (Ix r t j) k).val a b = (1 : Matrix (Ix r t j) (Ix r t j) k) a b) → (h : GL (Ix r t j) k).val (Sum.inl r₀) (Sum.inl r₀) = 1 → ∃ g : P.J, (g : GL r k).val = (h : GL (Ix r t j) k).val.submatrix Sum.inl Sum.inl ∧ (P.iter t μ hμ j).lam h = P.lam g := by
  first | exact @GlobalTheory.StepData.iter_lam_one_row | exact GlobalTheory.StepData.iter_lam_one_row | (intros; apply GlobalTheory.StepData.iter_lam_one_row <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearWeilActionSupportAndPeriodIntegralStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearWeilAction_support_and_period_integral : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (ϖ : kˣ), valuation k (ϖ : k) < 1 → ∀ (i : ℕ)
    (μ : kˣ →* ℂˣ) (Φ : Matrix B A k → ℂ), (∀ x, Φ x ≠ 0 → IntM x) → (∀ x y, MaxM y → Φ (x + y) = Φ x) →
    ∀ (g : GL A k) (g' : GL B k), IntM (g⁻¹ : GL A k).val → IntM ((ϖ : k) ^ i • g.val) →
      IntM (g'⁻¹ : GL B k).val → IntM ((ϖ : k) ^ (i + 1) • g'.val) →
    (∀ x, om μ g g' Φ x ≠ 0 → ∀ r s, valuation k (x r s) ≤ valuation k (((ϖ ^ (i + 1))⁻¹ : kˣ) : k)) ∧
    (∀ x y, (∀ r s, valuation k (y r s) ≤ valuation k ((ϖ : k) ^ (i + 1))) → om μ g g' Φ (x + y) = om μ g g' Φ x) := by
  first | exact @GlobalTheory.StepData.om_support_period | exact GlobalTheory.StepData.om_support_period | (intros; apply GlobalTheory.StepData.om_support_period <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormIteratedDerivWeierstrassPLeOne
section
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators

noncomputable section

namespace GlobalTheory.Klein

variable {p : ℕ} [Fact p.Prime]

def intAt (ι : ℂ ≃+* ℂ_[p]) : Subring ℂ where
  carrier := {c | ‖ι c‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_mul, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

theorem mem_intAt (ι : ℂ ≃+* ℂ_[p]) (c : ℂ) : c ∈ intAt ι ↔ ‖ι c‖ ≤ 1 := Iff.rfl

theorem half_mem_intAt (ι : ℂ ≃+* ℂ_[p]) (hp : p ≠ 2) : (2⁻¹ : ℂ) ∈ intAt ι := by
  have hc : Nat.Coprime p 2 := (Nat.coprime_primes Fact.out Nat.prime_two).2 hp
  have h : ‖((2 : ℕ) : ℚ_[p])‖ = 1 := Padic.norm_natCast_eq_one_iff.2 hc
  have h2 : ‖((2 : ℕ) : ℂ_[p])‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', h]
  have h3 : ι 2 = ((2 : ℕ) : ℂ_[p]) := by
    rw [← map_natCast ι]; simp
  rw [mem_intAt, map_inv₀, norm_inv, h3, h2]; simp

theorem mem_intAt_of_sq (ι : ℂ ≃+* ℂ_[p]) {c : ℂ} (h : c ^ 2 ∈ intAt ι) : c ∈ intAt ι := by
  rw [mem_intAt, map_pow, norm_pow] at h
  rw [mem_intAt]
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

def intFun (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ) : Subring (ℂ → ℂ) :=
  Subring.closure ({fun z => L.weierstrassP z - r, L.derivWeierstrassP} ∪ {f | ∃ c ∈ intAt ι, f = fun _ => c})

theorem const_mem_intFun (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ) {c : ℂ} (hc : c ∈ intAt ι) :
    (fun _ => c) ∈ intFun ι L r :=
  Subring.subset_closure (Or.inr ⟨c, hc, rfl⟩)

theorem x_mem_intFun (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ) :
    (fun z => L.weierstrassP z - r) ∈ intFun ι L r :=
  Subring.subset_closure (Or.inl (Or.inl rfl))

theorem y_mem_intFun (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ) : L.derivWeierstrassP ∈ intFun ι L r :=
  Subring.subset_closure (Or.inl (Or.inr rfl))

theorem derivWeierstrassP_mem_intAt {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r z : ℂ} (hg : Good ι L r)
    (hz : Red ι L r z) : L.derivWeierstrassP z ∈ intAt ι := by
  obtain ⟨-, h1, h2, h3, -⟩ := hg
  obtain ⟨hz, hx⟩ := hz
  rw [← mem_intAt] at h1 h2 h3 hx
  apply mem_intAt_of_sq
  have e : L.derivWeierstrassP z ^ 2 = ((4 : ℕ) : ℂ) * (L.weierstrassP z - r) ^ 3 + 12 * r * (L.weierstrassP z - r) ^ 2
      + (12 * r ^ 2 - L.g₂) * (L.weierstrassP z - r) + (4 * r ^ 3 - L.g₂ * r - L.g₃) := by
    rw [L.derivWeierstrassP_sq z hz]; push_cast; ring
  rw [e]
  exact add_mem (add_mem (add_mem (mul_mem (natCast_mem _ 4) (pow_mem hx 3)) (mul_mem h1 (pow_mem hx 2)))
    (mul_mem h2 hx)) h3

theorem apply_mem_intAt {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r z : ℂ} (hg : Good ι L r)
    (hz : Red ι L r z) {f : ℂ → ℂ} (hf : f ∈ intFun ι L r) : f z ∈ intAt ι := by
  have : intFun ι L r ≤ (intAt ι).comap (Pi.evalRingHom (fun _ : ℂ => ℂ) z) := by
    refine Subring.closure_le.2 ?_
    rintro f ((rfl | rfl) | ⟨c, hc, rfl⟩)
    · exact hz.2
    · exact derivWeierstrassP_mem_intAt hg hz
    · exact hc
  exact this hf

theorem exists_hasDerivAt_intFun {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r : ℂ} (hg : Good ι L r)
    {f : ℂ → ℂ} (hf : f ∈ intFun ι L r) :
    ∃ g ∈ intFun ι L r, ∀ w ∉ L.lattice, HasDerivAt f (g w) w := by
  induction hf using Subring.closure_induction with
  | mem f hf =>
    rcases hf with (rfl | rfl) | ⟨c, hc, rfl⟩
    · exact ⟨_, y_mem_intFun ι L r, fun w hw => (GlobalTheory.hasDerivAt_weierstrassP L hw).sub_const r⟩
    · obtain ⟨hp, h1, h2, -, -⟩ := hg
      rw [← mem_intAt] at h1 h2
      have hx := x_mem_intFun ι L r
      refine ⟨_, add_mem (add_mem (mul_mem (const_mem_intFun ι L r (natCast_mem _ 6)) (mul_mem hx hx))
        (mul_mem (const_mem_intFun ι L r h1) hx))
        (const_mem_intFun ι L r (mul_mem h2 (half_mem_intAt ι hp))), fun w hw => ?_⟩
      convert GlobalTheory.hasDerivAt_derivWeierstrassP L hw using 1
      simp only [Pi.add_apply, Pi.mul_apply]
      push_cast; ring
    · exact ⟨0, zero_mem _, fun w _ => hasDerivAt_const w c⟩
  | zero => exact ⟨0, zero_mem _, fun w _ => hasDerivAt_const w 0⟩
  | one => exact ⟨0, zero_mem _, fun w _ => hasDerivAt_const w 1⟩
  | add f f' _ _ h h' =>
    obtain ⟨g, hg1, hg2⟩ := h
    obtain ⟨g', hg1', hg2'⟩ := h'
    exact ⟨g + g', add_mem hg1 hg1', fun w hw => (hg2 w hw).add (hg2' w hw)⟩
  | neg f _ h =>
    obtain ⟨g, hg1, hg2⟩ := h
    exact ⟨-g, neg_mem hg1, fun w hw => (hg2 w hw).neg⟩
  | mul f f' hf hf' h h' =>
    obtain ⟨g, hg1, hg2⟩ := h
    obtain ⟨g', hg1', hg2'⟩ := h'
    exact ⟨g * f' + f * g', add_mem (mul_mem hg1 hf') (mul_mem hf hg1'),
      fun w hw => (hg2 w hw).mul (hg2' w hw)⟩

theorem exists_iteratedDeriv_eq_intFun {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r : ℂ} (hg : Good ι L r) (k : ℕ) :
    ∃ f ∈ intFun ι L r, ∀ w ∉ L.lattice, iteratedDeriv (k + 1) L.weierstrassP w = f w := by
  induction k with
  | zero =>
    exact ⟨_, y_mem_intFun ι L r, fun w hw => by
      rw [zero_add, iteratedDeriv_one]; exact (GlobalTheory.hasDerivAt_weierstrassP L hw).deriv⟩
  | succ k ih =>
    obtain ⟨f, hf, hfe⟩ := ih
    obtain ⟨g, hg1, hg2⟩ := exists_hasDerivAt_intFun hg hf
    refine ⟨g, hg1, fun w hw => ?_⟩
    have he : iteratedDeriv (k + 1) L.weierstrassP =ᶠ[nhds w] f := by
      filter_upwards [GlobalTheory.eventually_notMem_periodLattice L hw] with u hu using hfe u hu
    rw [iteratedDeriv_succ, he.deriv_eq, (hg2 w hw).deriv]

theorem norm_iteratedDeriv_weierstrassP_le_one : ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ), Good ι L r → ∀ z, Red ι L r z → ∀ k : ℕ, ‖ι (iteratedDeriv (k + 1) L.weierstrassP z)‖ ≤ 1 := by
  intro p _ ι L r hg z hz k
  obtain ⟨f, hf, hfe⟩ := exists_iteratedDeriv_eq_intFun hg k
  rw [hfe z hz.1]
  exact apply_mem_intAt hg hz hf

end GlobalTheory.Klein
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricChainLastTwoStepsRootOfUnityStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricChain_last_two_steps_root_of_unity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s : ℕ) (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ), (∀ j, IsUnram (η j)) → ∀ g : GL (XIx κ t (s + 1) ⊕ Fin 0) k, g ∈ ((twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).J → ∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ (∀ h x₀ y, (twistChain s t κ δ hδ η).Psi h (g.val.toBlocks₁₁ * x₀) (g.val.toBlocks₁₁ *ᵥ y) = c * (twistChain s t κ δ hδ η).Psi h x₀ y) ∧ ∀ (ψ : AddChar k Circle) (ε : k) (w : kˣ) (y : XIx κ t (s + 1) → k) x, (twistChain s t κ δ hδ η).xiTop (box _ w) ψ ν ε (Submodule.Quotient.mk y) (x * g.val.toBlocks₁₁) = c * (twistChain s t κ δ hδ η).xiTop (box _ w) ψ ν ε (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y)) x := by
  first | exact @GlobalTheory.LevelLaw.last_steps_law | exact GlobalTheory.LevelLaw.last_steps_law | (intros; apply GlobalTheory.LevelLaw.last_steps_law <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionSetSubgroup
section
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators

namespace GlobalTheory.Klein

private theorem ultra_add_le {K : Type*} [NormedField K] [IsUltrametricDist K] {x y : K} {C : ℝ}
    (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C) : ‖x + y‖ ≤ C :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

private theorem mul_le_of {K : Type*} [NormedField K] {x y : K} {C D : ℝ}
    (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ D) : ‖x * y‖ ≤ C * D := by
  rw [norm_mul]
  exact mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)

private theorem cubic_le {K : Type*} [NormedField K] [IsUltrametricDist K] {x k₂ k₁ k₀ : K} {ρ : ℝ}
    (h2 : ‖(2 : K)‖ = 1) (hρ : 1 ≤ ρ) (hx : ‖x‖ ≤ ρ) (hk₂ : ‖k₂‖ ≤ 1) (hk₁ : ‖k₁‖ ≤ 1) (hk₀ : ‖k₀‖ ≤ 1) :
    ‖2 * 2 * (x * x * x) + k₂ * (x * x) + k₁ * x + k₀‖ ≤ ρ * ρ * ρ := by
  have h1 : 1 ≤ ρ * ρ := by nlinarith
  refine ultra_add_le (ultra_add_le (ultra_add_le ?_ ?_) ?_) ?_
  · simpa using mul_le_of (mul_le_of h2.le h2.le) (mul_le_of (mul_le_of hx hx) hx)
  · exact (mul_le_of hk₂ (mul_le_of hx hx)).trans (by nlinarith)
  · exact (mul_le_of hk₁ hx).trans (by nlinarith)
  · exact hk₀.trans (by nlinarith)

private theorem le_of_mul_self_le_mul_self' {x y : ℝ} (h : x * x ≤ y * y) (hy : 0 ≤ y) : x ≤ y :=
  (abs_le_of_sq_le_sq' (by simpa only [sq] using h) hy).2

theorem chord_norm_le_one {K : Type*} [NormedField K] [IsUltrametricDist K] {a b A B X k₂ k₁ k₀ : K}
    (h2 : ‖(2 : K)‖ = 1) (ha : 1 < ‖a‖) (hb : ‖b‖ ≤ 1) (hk₂ : ‖k₂‖ ≤ 1) (hk₁ : ‖k₁‖ ≤ 1) (hk₀ : ‖k₀‖ ≤ 1)
    (hA : A ^ 2 = 4 * a ^ 3 + k₂ * a ^ 2 + k₁ * a + k₀)
    (hB : B ^ 2 = 4 * b ^ 3 + k₂ * b ^ 2 + k₁ * b + k₀)
    (hX : 4 * (a - b) ^ 2 * X = (A - B) ^ 2 - (4 * (a + b) + k₂) * (a - b) ^ 2) : ‖X‖ ≤ 1 := by
  set ρ := ‖a‖ with hρ
  have haa : ‖a‖ ≤ ρ := le_rfl
  have hab : ‖a - b‖ = ρ := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; linarith),
      norm_neg, max_eq_left (by linarith)]
  have hA' : ‖A‖ * ‖A‖ ≤ ρ * ρ * ρ := by
    rw [← norm_mul, show A * A = 2 * 2 * (a * a * a) + k₂ * (a * a) + k₁ * a + k₀ by
      linear_combination hA]
    exact cubic_le h2 ha.le haa hk₂ hk₁ hk₀
  have hB' : ‖B‖ * ‖B‖ ≤ 1 * 1 * 1 := by
    rw [← norm_mul, show B * B = 2 * 2 * (b * b * b) + k₂ * (b * b) + k₁ * b + k₀ by
      linear_combination hB]
    exact cubic_le h2 le_rfl hb hk₂ hk₁ hk₀
  have h1 : 1 ≤ ρ * ρ := by nlinarith
  have hρρ : ρ ≤ ρ * ρ := by nlinarith
  have hA1 : ‖A‖ ≤ ρ * ρ := by
    exact le_of_mul_self_le_mul_self' (hA'.trans (by nlinarith)) (by linarith)
  have hB1 : ‖B‖ ≤ 1 := by
    exact le_of_mul_self_le_mul_self' (hB'.trans (by norm_num)) (by linarith)
  have hN : 2 * 2 * ((a - b) * (a - b)) * X =
      2 * 2 * b * (a * (a + b)) + 2 * k₂ * b * a + k₁ * (a + b) + 2 * k₀ + 2 * B * (-A) := by
    linear_combination hX + hA + hB
  have hs : ‖a + b‖ ≤ ρ := ultra_add_le haa (by linarith)
  have hn : ‖2 * 2 * b * (a * (a + b)) + 2 * k₂ * b * a + k₁ * (a + b) + 2 * k₀ + 2 * B * (-A)‖
      ≤ ρ * ρ := by
    refine ultra_add_le (ultra_add_le (ultra_add_le (ultra_add_le ?_ ?_) ?_) ?_) ?_
    · simpa using mul_le_of (mul_le_of (mul_le_of h2.le h2.le) hb) (mul_le_of haa hs)
    · exact (mul_le_of (mul_le_of (mul_le_of h2.le hk₂) hb) haa).trans (by linarith)
    · exact (mul_le_of hk₁ hs).trans (by linarith)
    · exact (mul_le_of h2.le hk₀).trans (by linarith)
    · exact (mul_le_of (mul_le_of h2.le hB1) ((norm_neg A).le.trans hA1)).trans (by linarith)
  rw [← hN, norm_mul, norm_mul, norm_mul, norm_mul, h2, hab] at hn
  by_contra hc
  push_neg at hc
  nlinarith

theorem norm_two_of_ne {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h : ‖((2 : ℕ) : ℚ_[p])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes Fact.out Nat.prime_two).2 hp
  have e : (2 : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((2 : ℕ) : ℚ_[p]) := by
    rw [map_natCast]; norm_num
  rw [e, norm_algebraMap', h]

variable {p : ℕ} [Fact p.Prime]

theorem Red.neg {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r z : ℂ} (h : Red ι L r z) : Red ι L r (-z) :=
  ⟨fun h' => h.1 (by simpa using h'), by rw [L.weierstrassP_neg]; exact h.2⟩

theorem Red.add_lattice {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r z ω : ℂ} (h : Red ι L r z)
    (hω : ω ∈ L.lattice) : Red ι L r (z + ω) :=
  ⟨fun h' => h.1 ((L.lattice.add_mem_iff_left hω).1 h'), by
    have e : L.weierstrassP (z + ω) = L.weierstrassP z := L.weierstrassP_add_coe z ⟨ω, hω⟩
    rw [e]; exact h.2⟩

theorem Red.add_of_not {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r u w : ℂ} (hg : Good ι L r)
    (hu : ¬ Red ι L r u) (hw : Red ι L r w) : Red ι L r (u + w) := by
  by_cases hL : u ∈ L.lattice
  · rw [add_comm]; exact hw.add_lattice hL
  have ha : 1 < ‖ι (L.weierstrassP u - r)‖ := not_le.1 fun h => hu ⟨hL, h⟩
  have hne : L.weierstrassP u ≠ L.weierstrassP w := fun h => by
    rw [h] at ha; exact absurd hw.2 (not_le.2 ha)
  refine ⟨fun h => hu ?_, ?_⟩
  · have := hw.neg.add_lattice h
    rwa [show -w + (u + w) = u by ring] at this
  obtain ⟨hp, hk₂, hk₁, hk₀, -⟩ := hg
  have hs := (GlobalTheory.weierstrassP_add L hL hw.1 hne).1
  have e1 := L.derivWeierstrassP_sq u hL
  have e2 := L.derivWeierstrassP_sq w hw.1
  have hd := sub_ne_zero.2 hne
  have key : ∀ x y : ℂ, y ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃ →
      ι y ^ 2 = 4 * ι (x - r) ^ 3 + ι (12 * r) * ι (x - r) ^ 2 + ι (12 * r ^ 2 - L.g₂) * ι (x - r)
        + ι (4 * r ^ 3 - L.g₂ * r - L.g₃) := fun x y h => by
    have : y ^ 2 = 4 * (x - r) ^ 3 + (12 * r) * (x - r) ^ 2 + (12 * r ^ 2 - L.g₂) * (x - r)
        + (4 * r ^ 3 - L.g₂ * r - L.g₃) := by linear_combination h
    rw [← map_pow, this, map_add, map_add, map_add, map_mul ι 4, map_mul ι (12 * r),
      map_mul ι _ (x - r), map_pow, map_pow, map_ofNat]
  refine chord_norm_le_one (norm_two_of_ne hp) ha hw.2 hk₂ hk₁ hk₀ (key _ _ e1) (key _ _ e2) ?_
  have : 4 * ((L.weierstrassP u - r) - (L.weierstrassP w - r)) ^ 2 * (L.weierstrassP (u + w) - r)
      = (L.derivWeierstrassP u - L.derivWeierstrassP w) ^ 2
        - (4 * ((L.weierstrassP u - r) + (L.weierstrassP w - r)) + 12 * r)
          * ((L.weierstrassP u - r) - (L.weierstrassP w - r)) ^ 2 := by
    rw [hs]; field_simp; ring
  have := congrArg ι this
  simpa only [map_mul, map_sub, map_add, map_pow, map_ofNat] using this

theorem not_red_addSubgroup : ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ), Good ι L r → (∀ z, Red ι L r z → Red ι L r (-z)) ∧ (∀ z, Red ι L r z → ∀ ω ∈ L.lattice, Red ι L r (z + ω)) ∧ (∀ u w, ¬ Red ι L r u → Red ι L r w → Red ι L r (u + w)) ∧ ∃ G : AddSubgroup ℂ, (∀ z, z ∈ G ↔ ¬ Red ι L r z) ∧ ∀ ω ∈ L.lattice, ω ∈ G := by
  intro p _ ι L r hg
  refine ⟨fun z h => h.neg, fun z h ω hω => h.add_lattice hω, fun u w hu hw => Red.add_of_not hg hu hw, ?_⟩
  have hneg : ∀ {z : ℂ}, ¬ Red ι L r z → ¬ Red ι L r (-z) := fun hz h => hz (by simpa using h.neg)
  refine ⟨{ carrier := {z | ¬ Red ι L r z}
            add_mem' := fun {u v} hu hv h => hu ?_
            zero_mem' := not_red_of_mem ι L r L.lattice.zero_mem
            neg_mem' := hneg }, fun z => Iff.rfl, fun ω hω => not_red_of_mem ι L r hω⟩
  have := Red.add_of_not hg (hneg hv) h
  rwa [show -v + (u + v) = u by ring] at this

end GlobalTheory.Klein
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeRowUnipotentLatticeFrameConjApplyStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootExchangeRowUnipotent_latticeFrame_conj_apply : ∀ (k : Type) [Field k] (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (ϖ : kˣ) (j c l : ℕ) (h : j + c = l) (p : ℕ) (hp : p < c) (u : XIx κ t j → k) (a b : Ix (κ ⊕ Fin l) t j), ((typeFrame ϖ (stdOrd κ t j c h)).conj.symm (rowE c (p + 1) u)).val a b = (1 : Matrix (Ix (κ ⊕ Fin l) t j) (Ix (κ ⊕ Fin l) t j) k) a b + if a = Sum.inl (Sum.inr ⟨p, by omega⟩) then Sum.elim (fun y => ((ϖ : k) ^ (p + 1))⁻¹ * u y) (fun _ => 0) (stdOrd κ t j c h b) else 0 := by
  first | exact @GlobalTheory.typeFrame_conj_symm_rowE_apply | exact GlobalTheory.typeFrame_conj_symm_rowE_apply | (intros; apply GlobalTheory.typeFrame_conj_symm_rowE_apply <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatFunctionalZeroOfFibreIntegralZero
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology

noncomputable section
namespace GlobalTheory.SplitWeil.FourierPi

theorem map_eq_zero_of_translation_invariant_of_fibre_integral_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (I₀ I₁ I₂ : Type) [Fintype I₀] [Fintype I₁] [Fintype I₂] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) →ₗ[ℂ] M), (∀ (a : I₂ → k) (Φ Φ' : SB ((I₀ → k) × (I₁ → k) × (I₂ → k))), (∀ x, Φ'.1 x = Φ.1 (x + (0, 0, a))) → l Φ' = l Φ) → ∀ Φ : SB ((I₀ → k) × (I₁ → k) × (I₂ → k)), (∀ x₀ x₁, ∫ a, Φ.1 (x₀, x₁, a) ∂(Measure.pi fun _ => ν) = 0) → l Φ = 0 := by
  intro k _ _ _ _ _ _ ν hν I₀ I₁ I₂ _ _ _ M _ _ l hl Φ hΦ
  haveI := secondCountable k
  haveI := hν

  have hU : {t : I₂ → k | ∀ g : (I₀ → k) × (I₁ → k) × (I₂ → k), Φ.1 (g + (0, 0, t)) = Φ.1 g} ∈
      𝓝 (0 : I₂ → k) := by
    have ht : Filter.Tendsto
        (fun t : I₂ → k => ((0, 0, -t) : (I₀ → k) × (I₁ → k) × (I₂ → k))) (𝓝 0) (𝓝 0) := by
      have hc : Continuous
          (fun t : I₂ → k => ((0, 0, -t) : (I₀ → k) × (I₁ → k) × (I₂ → k))) := by fun_prop
      have e : (((0 : I₀ → k), (0 : I₁ → k), -(0 : I₂ → k))) = 0 := by rw [neg_zero]; rfl
      have h := hc.tendsto 0
      rwa [e] at h
    filter_upwards [ht.eventually (GlobalTheory.SBConv.eventually_translate Φ.2)] with t h g
    have := h g
    simpa [sub_eq_add_neg] using this
  obtain ⟨r, hr⟩ := exists_box_subset hU
  have hK : IsCompact ((fun x : (I₀ → k) × (I₁ → k) × (I₂ → k) => x.2.2) '' tsupport Φ.1) :=
    Φ.2.2.isCompact.image (by fun_prop)
  obtain ⟨R, hrR, hKR⟩ := GlobalTheory.T.exists_integralScaledBoxPi_superset_of_isCompact k I₂ _ hK r
  obtain ⟨S, hSR, hS⟩ := GlobalTheory.T.exists_finset_integralScaledBoxPi_coset_reps k I₂ r R hrR
  have h0R : (0 : I₂ → k) ∈ box I₂ R := fun i _ => by simp [cball]
  have h0r : (0 : I₂ → k) ∈ box I₂ r := fun i _ => by simp [cball]
  have hSne : S.Nonempty := by
    obtain ⟨b, ⟨hb, -⟩, -⟩ := hS 0 h0R
    exact ⟨b, hb⟩

  let T : (I₂ → k) → SB ((I₀ → k) × (I₁ → k) × (I₂ → k)) := fun b =>
    ⟨fun x => Φ.1 (x + (0, 0, b)), Φ.2.1.comp_continuous (continuous_add_right _),
      Φ.2.2.comp_homeomorph (Homeomorph.addRight _)⟩
  have hT : ∀ b, l (T b) = l Φ := fun b => hl b Φ (T b) fun _ => rfl

  have hvol : (Measure.pi fun _ : I₂ => ν).real (box I₂ r) ≠ 0 := by
    rw [measureReal_def]
    exact (ENNReal.toReal_pos ((isOpen_box r).measure_ne_zero _ ⟨0, h0r⟩)
      (isCompact_box r).measure_lt_top.ne).ne'
  have hsum : ∑ b ∈ S, T b = 0 := by
    apply Subtype.ext
    funext x
    obtain ⟨x₀, x₁, a⟩ := x
    have hF1 : ∀ t ∈ box I₂ r, ∀ y, Φ.1 (x₀, x₁, y + t) = Φ.1 (x₀, x₁, y) := fun t ht y => by
      have := hr ht (x₀, x₁, y)
      simpa using this
    have hF2 : ∀ y ∉ box I₂ R, Φ.1 (x₀, x₁, y) = 0 := fun y hy =>
      image_eq_zero_of_notMem_tsupport fun hm => hy (hKR ⟨_, hm, rfl⟩)
    have hval : (∑ b ∈ S, T b).1 (x₀, x₁, a) = ∑ b ∈ S, Φ.1 (x₀, x₁, a + b) := by
      rw [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [T]
    rw [hval]
    by_cases ha : a ∈ box I₂ R
    · rw [GlobalTheory.T.sum_integralScaledBoxPi_coset_reps_shift_invariant k I₂ r R S hSR hS (fun y => Φ.1 (x₀, x₁, y)) hF1 a ha]
      have h := GlobalTheory.T.integral_box_invariant_eq_measureReal_mul_sum_reps k ν hν I₂ r R S hSR hS (fun y => Φ.1 (x₀, x₁, y)) hF1 hF2
      rw [hΦ x₀ x₁] at h
      have h' := (mul_eq_zero.mp h.symm).resolve_left (by exact_mod_cast hvol)
      simpa using h'
    · refine Finset.sum_eq_zero fun b hb => hF2 _ fun hab => ha fun i _ => ?_
      have := add_mem_cball (hab i trivial) (neg_mem_cball (hSR b hb i trivial))
      simpa using this
  have hz : (S.card : ℂ) • l Φ = 0 := by
    have h1 : l (∑ b ∈ S, T b) = (S.card : ℂ) • l Φ := by
      rw [map_sum, Finset.sum_congr rfl fun b _ => hT b, Finset.sum_const, Nat.cast_smul_eq_nsmul]
    rw [← h1, hsum, map_zero]
  exact (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast hSne.card_ne_zero)

end GlobalTheory.SplitWeil.FourierPi
end
end

