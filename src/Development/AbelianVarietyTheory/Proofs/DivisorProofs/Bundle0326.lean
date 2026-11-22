import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Formalism.SatakeDualWeyl.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0286
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGUIffAdjJ
section
open GlobalTheory.LGrp Formalism.UG

noncomputable section
namespace GlobalTheory.BorelUMod

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

def upLat (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (c : Fin n → Fin n → ℤ) :
    AddSubgroup (Matrix (Fin n) (Fin n) L) where
  carrier := {X | (∀ i j, j ≤ i → X i j = 0) ∧ ∀ i j, i < j → Valued.v (X i j) ≤ WithZero.exp (-c i j)}
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => by simp⟩
  add_mem' := fun {X Y} hX hY => ⟨fun i j h => by simp [hX.1 i j h, hY.1 i j h], fun i j h =>
    Valuation.map_add_le _ (hX.2 i j h) (hY.2 i j h)⟩
  neg_mem' := fun {X} hX => ⟨fun i j h => by simp [hX.1 i j h], fun i j h => by simpa using hX.2 i j h⟩

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.mem_upLat {c : Fin n → Fin n → ℤ}
    {X : Matrix (Fin n) (Fin n) L} :
    X ∈ _root_.GlobalTheory.BorelUMod.upLat L c ↔
      (∀ i j, j ≤ i → X i j = 0) ∧ ∀ i j, i < j → Valued.v (X i j) ≤ WithZero.exp (-c i j) :=
  Iff.rfl

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in

theorem _root_.GlobalTheory.BorelUMod.mul_mem_upLat {a b c : Fin n → Fin n → ℤ}
    (h : ∀ i j k, i < j → j < k → c i k ≤ a i j + b j k)
    {X Y : Matrix (Fin n) (Fin n) L} (hX : X ∈ _root_.GlobalTheory.BorelUMod.upLat L a)
    (hY : Y ∈ _root_.GlobalTheory.BorelUMod.upLat L b) : X * Y ∈ _root_.GlobalTheory.BorelUMod.upLat L c := by
  obtain ⟨hX0, hXv⟩ := hX
  obtain ⟨hY0, hYv⟩ := hY
  refine ⟨fun i j hji => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases le_or_gt k i with hki | hik
    · rw [hX0 i k hki, zero_mul]
    · rw [hY0 k j (hji.trans hik.le), mul_zero]
  · rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rcases le_or_gt k i with hki | hik
    · simp [hX0 i k hki]
    rcases le_or_gt j k with hjk | hkj
    · simp [hY0 k j hjk]
    rw [Valuation.map_mul]
    calc Valued.v (X i k) * Valued.v (Y k j)
        ≤ WithZero.exp (-a i k) * WithZero.exp (-b k j) := mul_le_mul' (hXv i k hik) (hYv k j hkj)
      _ = WithZero.exp (-a i k + -b k j) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (-c i j) := WithZero.exp_le_exp.2 (by linarith [h i k j hik hkj])

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.upLat_mono {c C : Fin n → Fin n → ℤ}
    (h : ∀ i j, i < j → c i j ≤ C i j) :
    _root_.GlobalTheory.BorelUMod.upLat L C ≤ _root_.GlobalTheory.BorelUMod.upLat L c :=
  fun _ hX => ⟨hX.1, fun i j hij =>
    (hX.2 i j hij).trans (WithZero.exp_le_exp.2 (neg_le_neg (h i j hij)))⟩

def adjJ (σ : L →+* L) (X : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) L := fun i j => σ (X j.rev i.rev)

def skewJ (σ : L →+* L) (n : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) L) where
  carrier := {X | adjJ σ X = -X}
  zero_mem' := by ext i j; simp [adjJ]
  add_mem' := fun {X Y} hX hY => by
    ext i j
    have h1 := congrFun (congrFun hX i) j
    have h2 := congrFun (congrFun hY i) j
    simp only [adjJ, Matrix.neg_apply] at h1 h2
    simp [adjJ, h1, h2, add_comm]
  neg_mem' := fun {X} hX => by
    ext i j
    have h1 := congrFun (congrFun hX i) j
    simp only [adjJ, Matrix.neg_apply] at h1
    simp [adjJ, h1]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.mem_skewJ {σ : L →+* L} {X : Matrix (Fin n) (Fin n) L} :
    X ∈ _root_.GlobalTheory.BorelUMod.skewJ σ n ↔ _root_.GlobalTheory.BorelUMod.adjJ σ X = -X :=
  Iff.rfl

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_mul (σ : L →+* L) (X Y : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (X * Y) =
      _root_.GlobalTheory.BorelUMod.adjJ σ Y * _root_.GlobalTheory.BorelUMod.adjJ σ X := by
  ext i j
  simp only [_root_.GlobalTheory.BorelUMod.adjJ, Matrix.mul_apply, map_sum, map_mul]
  rw [← Equiv.sum_comp Fin.revPerm]
  simp [mul_comm]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_add (σ : L →+* L) (X Y : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (X + Y) =
      _root_.GlobalTheory.BorelUMod.adjJ σ X + _root_.GlobalTheory.BorelUMod.adjJ σ Y := by
  ext i j
  simp [_root_.GlobalTheory.BorelUMod.adjJ]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_sub (σ : L →+* L) (X Y : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (X - Y) =
      _root_.GlobalTheory.BorelUMod.adjJ σ X - _root_.GlobalTheory.BorelUMod.adjJ σ Y := by
  ext i j
  simp [_root_.GlobalTheory.BorelUMod.adjJ]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_smul (σ : L →+* L) (a : L) (X : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (a • X) = σ a • _root_.GlobalTheory.BorelUMod.adjJ σ X := by
  ext i j
  simp [_root_.GlobalTheory.BorelUMod.adjJ]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_one (σ : L →+* L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [_root_.GlobalTheory.BorelUMod.adjJ]
  · have h' : j.rev ≠ i.rev := fun e => h (Fin.rev_injective e).symm
    simp [_root_.GlobalTheory.BorelUMod.adjJ, Matrix.one_apply, h, h']

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem _root_.GlobalTheory.BorelUMod.adjJ_adjJ {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x)
    (X : Matrix (Fin n) (Fin n) L) :
    _root_.GlobalTheory.BorelUMod.adjJ σ (_root_.GlobalTheory.BorelUMod.adjJ σ X) = X := by
  ext i j
  simp [_root_.GlobalTheory.BorelUMod.adjJ, hσ]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
omit [Valued L (WithZero (Multiplicative ℤ))] in

theorem _root_.GlobalTheory.BorelUMod.mem_GU_iff_adjJ (σ : L →+* L) (g : GL (Fin n) L) :
    g ∈ _root_.Formalism.UG.GU σ n ↔ (g⁻¹).val = _root_.GlobalTheory.BorelUMod.adjJ σ g.val := by
  rw [_root_.GlobalTheory.LGrp.mem_GU_iff]
  constructor
  · intro h
    ext i j
    exact h i j
  · intro h i j
    exact congrFun (congrFun h i) j

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.adjJ_mem_upLat {σ : L →+* L}
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {c : Fin n → Fin n → ℤ}
    (hc : ∀ i j, c j.rev i.rev = c i j) {X : Matrix (Fin n) (Fin n) L}
    (hX : X ∈ _root_.GlobalTheory.BorelUMod.upLat L c) :
    _root_.GlobalTheory.BorelUMod.adjJ σ X ∈ _root_.GlobalTheory.BorelUMod.upLat L c := by
  refine ⟨fun i j hji => ?_, fun i j hij => ?_⟩
  · simp [_root_.GlobalTheory.BorelUMod.adjJ, hX.1 j.rev i.rev (Fin.rev_le_rev.2 hji)]
  · simp only [_root_.GlobalTheory.BorelUMod.adjJ]
    rw [hσ, ← hc i j]
    exact hX.2 j.rev i.rev (Fin.rev_lt_rev.2 hij)

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.smul_mem_upLat {c : Fin n → Fin n → ℤ} {a : L}
    (ha : Valued.v a ≤ 1) {X : Matrix (Fin n) (Fin n) L}
    (hX : X ∈ _root_.GlobalTheory.BorelUMod.upLat L c) : a • X ∈ _root_.GlobalTheory.BorelUMod.upLat L c := by
  refine ⟨fun i j hji => by simp [hX.1 i j hji], fun i j hij => ?_⟩
  rw [Matrix.smul_apply, smul_eq_mul, Valuation.map_mul]
  calc Valued.v a * Valued.v (X i j) ≤ 1 * WithZero.exp (-c i j) := mul_le_mul' ha (hX.2 i j hij)
    _ = WithZero.exp (-c i j) := one_mul _

def IsWeight (c : Fin n → Fin n → ℤ) : Prop :=
  (∀ i j, c j.rev i.rev = c i j) ∧ ∀ i j k, i < j → j < k → c i k ≤ c i j + c j k

def IsIdealWeight (c C : Fin n → Fin n → ℤ) : Prop :=
  (∀ i j, i < j → c i j ≤ C i j) ∧ (∀ i j k, i < j → j < k → C i k ≤ c i j + C j k) ∧
    ∀ i j k, i < j → j < k → C i k ≤ C i j + c j k

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.isWeight_zero :
    _root_.GlobalTheory.BorelUMod.IsWeight (fun _ _ : Fin n => (0 : ℤ)) :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ => by simp⟩

def unipLat {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {c : Fin n → Fin n → ℤ} (hc : IsWeight c) :
    Subgroup (borelU σ n).U where
  carrier := {u | (u.1.1.val : Matrix (Fin n) (Fin n) L) - 1 ∈ upLat L c}
  one_mem' := by
    show ((1 : Matrix (Fin n) (Fin n) L)) - 1 ∈ upLat L c
    simp
  mul_mem' := fun {u w} hu hw => by
    show u.1.1.val * w.1.1.val - 1 ∈ upLat L c
    have : u.1.1.val * w.1.1.val - 1 = (u.1.1.val - 1) * (w.1.1.val - 1) + (u.1.1.val - 1) + (w.1.1.val - 1) := by
      noncomm_ring
    rw [this]
    exact add_mem (add_mem (mul_mem_upLat hc.2 hu hw) hu) hw
  inv_mem' := fun {u} hu => by
    show (u.1.1⁻¹).val - 1 ∈ upLat L c
    rw [(mem_GU_iff_adjJ σ _).1 u.1.2, ← adjJ_one σ, ← adjJ_sub]
    exact adjJ_mem_upLat hσ hc.1 hu

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in
theorem _root_.GlobalTheory.BorelUMod.mem_unipLat {σ : L →+* L}
    {hσ : ∀ x, Valued.v (σ x) = Valued.v x} {c : Fin n → Fin n → ℤ}
    {hc : _root_.GlobalTheory.BorelUMod.IsWeight c} {u : (_root_.GlobalTheory.LGrp.borelU σ n).U} :
    u ∈ _root_.GlobalTheory.BorelUMod.unipLat hσ hc ↔
      (u.1.1.val : Matrix (Fin n) (Fin n) L) - 1 ∈ _root_.GlobalTheory.BorelUMod.upLat L c :=
  Iff.rfl

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} in

theorem _root_.GlobalTheory.BorelUMod.exists_trace_one {ϖ : L} {σ : L →+* L} {q : ℕ}
    (h : _root_.Formalism.UG.IsUnramInv ϖ σ q) :
    (∃ θ : L, Valued.v θ ≤ 1 ∧ θ + σ θ = 1) ∧ ∃ d : L, Valued.v d = 1 ∧ σ d = -d := by
  obtain ⟨hinv, -, -, -, ⟨x, hx, hxu⟩, -⟩ := h
  have hx1 : Valued.v x ≤ 1 := hx
  refine ⟨?_, σ x - x, hxu, by rw [map_sub, hinv]; ring⟩
  have h2le : Valued.v (2 : L) ≤ 1 := by
    have h11 : Valued.v ((1 : L) + 1) ≤ 1 :=
      Valuation.map_add_le _ (le_of_eq (Valuation.map_one _)) (le_of_eq (Valuation.map_one _))
    rwa [one_add_one_eq_two] at h11
  rcases h2le.lt_or_eq with h2 | h2
  · have hlt : Valued.v (2 * x) < Valued.v (σ x - x) := by
      rw [hxu, Valuation.map_mul]
      calc Valued.v (2 : L) * Valued.v x ≤ Valued.v (2 : L) * 1 := mul_le_mul' le_rfl hx1
        _ = Valued.v (2 : L) := mul_one _
        _ < 1 := h2
    have ht : Valued.v (x + σ x) = 1 := by
      have e : x + σ x = (σ x - x) + 2 * x := by ring
      rw [e, Valuation.map_add_eq_of_lt_left _ hlt, hxu]
    have ht0 : x + σ x ≠ 0 := by
      intro e
      rw [e, Valuation.map_zero] at ht
      exact zero_ne_one ht
    refine ⟨x / (x + σ x), ?_, ?_⟩
    · rw [map_div₀, ht, div_one]
      exact hx1
    · rw [map_div₀, map_add, hinv, add_comm (σ x) x, ← add_div, div_self ht0]
  · refine ⟨1 / 2, ?_, ?_⟩
    · rw [map_div₀, Valuation.map_one, h2, div_one]
    · rw [map_div₀, map_one, map_ofNat]
      have h20 : (2 : L) ≠ 0 := by
        intro e
        rw [e, Valuation.map_zero] at h2
        exact zero_ne_one h2
      rw [← add_div, one_add_one_eq_two, div_self h20]

end GlobalTheory.BorelUMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanValuationSubringIff
section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix

namespace GlobalTheory.FrameModel

variable {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [Algebra O C]

def embVal (hv : v.Integers O) {Λ : Type} [CommRing Λ] (α : Λ) :
    (Λ →+* O) → v.valuationSubring :=
  fun σ => ⟨algebraMap O C (σ α), (Valuation.mem_valuationSubring_iff _ _).2 (hv.map_le_one _)⟩

theorem coe_embVal (hv : v.Integers O) {Λ : Type} [CommRing Λ] (α : Λ) (σ : Λ →+* O) :
    (embVal v hv α σ : C) = algebraMap O C (σ α) := rfl

def modelLattice {S : Type} {h N : ℕ} (Φ : (Fin h → C) ≃ₗ[C] (S → Fin N → C))
    (L : Submodule O (Fin h → O)) : Submodule v.valuationSubring (S → Fin N → C) :=
  Submodule.span v.valuationSubring ((fun t => Φ (incl C h t)) '' (L : Set (Fin h → O)))

theorem mem_span_valuationSubring_iff (hv : v.Integers O) {W : Type} [AddCommGroup W] [Module C W]
    [Module O W] [IsScalarTower O C W] [Module v.valuationSubring W]
    [IsScalarTower v.valuationSubring C W] (s : Set W) (x : W) :
    x ∈ Submodule.span v.valuationSubring s ↔ x ∈ Submodule.span O s := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx =>
      obtain ⟨o, ho⟩ := hv.exists_of_le_one ((Valuation.mem_valuationSubring_iff _ _).1 c.2)
      have : c • x = o • x := by
        rw [← algebraMap_smul C c x, ← algebraMap_smul C o x, ho]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ hx
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul o x _ hx =>
      let c : v.valuationSubring :=
        ⟨algebraMap O C o, (Valuation.mem_valuationSubring_iff _ _).2 (hv.map_le_one _)⟩
      have : o • x = c • x := by
        rw [← algebraMap_smul C c x, ← algebraMap_smul C o x]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ hx

theorem mem_modelLattice (hv : v.Integers O) {S : Type} {h N : ℕ}
    (Φ : (Fin h → C) ≃ₗ[C] (S → Fin N → C)) (L : Submodule O (Fin h → O)) (w : S → Fin N → C) :
    w ∈ modelLattice v Φ L ↔ ∃ t ∈ L, Φ (incl C h t) = w := by
  unfold modelLattice
  rw [mem_span_valuationSubring_iff v hv]
  have : (fun t => Φ (incl C h t)) '' (L : Set (Fin h → O)) =
      (L.map ((Φ.toLinearMap.restrictScalars O) ∘ₗ incl C h) : Set (S → Fin N → C)) := by
    rw [Submodule.map_coe]; rfl
  rw [this, Submodule.span_eq, Submodule.mem_map]
  rfl

theorem mem_eig_iff {Λ : Type} [CommRing Λ] {h : ℕ} (ρ : Λ → Matrix (Fin h) (Fin h) O)
    (τ : Λ →+* O) (x : Fin h → C) :
    x ∈ eig C ρ τ ↔ ∀ l, (ρ l).map (algebraMap O C) *ᵥ x = algebraMap O C (τ l) • x := by
  simp only [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]

theorem mem_eig_iff_support (hv : v.Integers O) {Λ : Type} [CommRing Λ] {h N : ℕ}
    (ρ : Λ → Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C))
    (hΦ : ∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ)
    (τ : Λ →+* O) (x : Fin h → C) : x ∈ eig C ρ τ ↔ ∀ σ, σ ≠ τ → Φ x σ = 0 := by
  rw [mem_eig_iff]
  constructor
  · intro hx σ hσ
    obtain ⟨l, hl⟩ : ∃ l, σ l ≠ τ l := by
      by_contra hc
      push Not at hc
      exact hσ (RingHom.ext hc)
    have e := hΦ l x σ
    rw [hx l, map_smul, Pi.smul_apply, ← sub_eq_zero, ← sub_smul, smul_eq_zero] at e
    rcases e with e | e
    · exact absurd (hv.hom_inj (sub_eq_zero.1 e)).symm hl
    · exact e
  · intro hx l
    apply Φ.injective
    funext σ
    rw [hΦ, map_smul, Pi.smul_apply]
    by_cases hσ : σ = τ
    · rw [hσ]
    · rw [hx σ hσ, smul_zero, smul_zero]

theorem mem_freeLattice_iff (hv : v.Integers O) {Λ : Type} [CommRing Λ] (α : Λ) {h N : ℕ}
    (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C))
    (hΦ : ∀ z, (∀ i, z i ∈ (algebraMap O C).range) ↔
      ∀ i, ∃ f : Polynomial O, ∀ σ, Φ z σ i = algebraMap O C (f.eval (σ α)))
    (w : (Λ →+* O) → Fin N → C) :
    w ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice (embVal v hv α) N ↔
      ∃ t : Fin h → O, Φ (incl C h t) = w := by
  let j : O →+* v.valuationSubring := (algebraMap O C).codRestrict v.valuationSubring
    fun o => (Valuation.mem_valuationSubring_iff _ _).2 (hv.map_le_one _)
  have hj : Function.Surjective j := fun c => by
    obtain ⟨o, ho⟩ := hv.exists_of_le_one ((Valuation.mem_valuationSubring_iff _ _).1 c.2)
    exact ⟨o, Subtype.ext ho⟩
  have key : ∀ (f : Polynomial O) (σ : Λ →+* O),
      (((f.map j).eval (embVal v hv α σ) : v.valuationSubring) : C) =
        algebraMap O C (f.eval (σ α)) := by
    intro f σ
    have : embVal v hv α σ = j (σ α) := rfl
    rw [this, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rfl
  constructor
  · intro hw
    have : ∀ i, Φ.symm w i ∈ (algebraMap O C).range := by
      rw [hΦ]
      intro i
      obtain ⟨f, hf⟩ := hw i
      obtain ⟨g, rfl⟩ := Polynomial.map_surjective j hj f
      exact ⟨g, fun σ => by rw [Φ.apply_symm_apply, hf, key]⟩
    choose t ht using this
    refine ⟨t, ?_⟩
    have : incl C h t = Φ.symm w := funext ht
    rw [this, Φ.apply_symm_apply]
  · rintro ⟨t, rfl⟩ i
    obtain ⟨f, hf⟩ := (hΦ (incl C h t)).1 (fun i => ⟨t i, rfl⟩) i
    exact ⟨f.map j, fun σ => by rw [hf, key]⟩

theorem mulVec_incl {h k : ℕ} (X : Matrix (Fin k) (Fin h) O) (t : Fin h → O) :
    X.map (algebraMap O C) *ᵥ incl C h t = incl C k (X *ᵥ t) := by
  funext i
  show _ = algebraMap O C ((X *ᵥ t) i)
  rw [RingHom.map_mulVec]
  rfl

theorem incl_injective (hv : v.Integers O) (h : ℕ) :
    Function.Injective (incl C h : (Fin h → O) → (Fin h → C)) := by
  intro u u' e
  funext i
  exact hv.hom_inj (congrFun e i)

theorem exists_smul_eq_incl (hv : v.Integers O) {h : ℕ} (y : Fin h → C) :
    ∃ (o : O) (t : Fin h → O), algebraMap O C o ≠ 0 ∧ incl C h t = algebraMap O C o • y := by
  haveI : IsDomain O := hv.hom_inj.isDomain
  haveI : IsFractionRing O C := hv.isFractionRing
  obtain ⟨o, ho⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) y
  choose t ht using ho
  refine ⟨o, t, fun e => nonZeroDivisors.coe_ne_zero o (hv.hom_inj (by rw [e, map_zero])), ?_⟩
  funext i
  show algebraMap O C (t i) = _
  rw [ht i, Pi.smul_apply, algebraMap_smul]

theorem mem_iSup_eig_iff (hv : v.Integers O) {Λ : Type} [CommRing Λ] [Finite (Λ →+* O)] {h N : ℕ}
    (ρ : Λ → Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C))
    (hΦ : ∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ)
    (τ : Λ →+* O) (x : Fin h → C) :
    x ∈ (⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ σ.1) ↔ Φ x τ = 0 := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.iSup_induction' with
    | mem σ x hx => exact (mem_eig_iff_support v hv ρ Φ hΦ σ.1 x).1 hx τ σ.2.symm
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, Pi.add_apply, hx, hy, add_zero]
  · intro hx
    letI := Fintype.ofFinite (Λ →+* O)
    have e : x = ∑ σ, Φ.symm (Pi.single σ (Φ x σ)) := by
      rw [← map_sum, Finset.univ_sum_single, Φ.symm_apply_apply]
    rw [e]
    refine sum_mem fun σ _ => ?_
    by_cases hσ : σ = τ
    · rw [hσ, hx, Pi.single_zero, map_zero]
      exact zero_mem _
    · refine Submodule.mem_iSup_of_mem (⟨σ, hσ⟩ : {σ : Λ →+* O // σ ≠ τ}) ?_
      rw [mem_eig_iff_support v hv ρ Φ hΦ]
      intro s hs
      rw [Φ.apply_symm_apply, Pi.single_eq_of_ne hs]

theorem exists_eig_apply_eq (hv : v.Integers O) {Λ : Type} [CommRing Λ] {h N : ℕ}
    (ρ : Λ → Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C))
    (hΦ : ∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ)
    (τ : Λ →+* O) (w : Fin N → C) : ∃ x ∈ eig C ρ τ, Φ x τ = w := by
  classical
  refine ⟨Φ.symm (Pi.single τ w), ?_, by rw [Φ.apply_symm_apply, Pi.single_eq_same]⟩
  rw [mem_eig_iff_support v hv ρ Φ hΦ]
  intro s hs
  rw [Φ.apply_symm_apply, Pi.single_eq_of_ne hs]

theorem eq_zero_of_apply_eq_zero (hv : v.Integers O) {Λ : Type} [CommRing Λ] {h N : ℕ}
    (ρ : Λ → Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C))
    (hΦ : ∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ)
    (τ : Λ →+* O) (x : Fin h → C) (hx : x ∈ eig C ρ τ) (h0 : Φ x τ = 0) : x = 0 := by
  apply Φ.injective
  funext σ
  rw [map_zero, Pi.zero_apply]
  by_cases hσ : σ = τ
  · rw [hσ, h0]
  · exact (mem_eig_iff_support v hv ρ Φ hΦ τ x).1 hx σ hσ

theorem mem_eigPart_iff (hv : v.Integers O) {Λ : Type} [CommRing Λ] [Finite (Λ →+* O)] {h N : ℕ}
    (ρ : Λ → Matrix (Fin h) (Fin h) O) (Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C))
    (hΦ : ∀ l z σ, Φ ((ρ l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ)
    (τ : Λ →+* O) (L : Submodule O (Fin h → O)) (x : Fin h → C) :
    x ∈ eigPart C ρ τ L ↔ x ∈ eig C ρ τ ∧ ∃ t ∈ L, Φ (incl C h t) τ = Φ x τ := by
  unfold eigPart
  rw [Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_sup]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨_, ⟨t, ht, rfl⟩, r, hr, rfl⟩
    rw [Submodule.restrictScalars_mem, mem_iSup_eig_iff v hv ρ Φ hΦ] at hr
    exact ⟨t, ht, by rw [map_add, Pi.add_apply, hr, add_zero]⟩
  · rintro ⟨t, ht, e⟩
    refine ⟨_, ⟨t, ht, rfl⟩, x - incl C h t, ?_, by abel⟩
    rw [Submodule.restrictScalars_mem, mem_iSup_eig_iff v hv ρ Φ hΦ, map_sub, Pi.sub_apply, e,
      sub_self]

end GlobalTheory.FrameModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHeckeTermDecayFourierIntegralLeStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_heckeTermDecayFourierIntegral_le : ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ (a : ℤ) (b m : ℕ), 2 ≤ a + 2 * b → ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, y ≠ 0 →
      ‖intZ σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) := by
  first | exact @GlobalTheory.HeckeTwo.TermDecay.norm_intZ_le | exact GlobalTheory.HeckeTwo.TermDecay.norm_intZ_le | (intros; apply GlobalTheory.HeckeTwo.TermDecay.norm_intZ_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdealUniquePrimeOver
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.origin_ideal_unique_prime_over : ∀ (A S : Type) [CommRing A] [IsLocalRing A] [CommRing S] [IsLocalRing S] (f : A →+* S), f.IsIntegral →
    (Polynomial.mapRingHom f).IsIntegral ∧ (GlobalTheory.KeyOriginCut.originIdeal S).IsPrime ∧
    (GlobalTheory.KeyOriginCut.originIdeal S).comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A ∧
    ∀ 𝔔 : Ideal (Polynomial S), 𝔔.IsPrime → 𝔔.comap (Polynomial.mapRingHom f) = GlobalTheory.KeyOriginCut.originIdeal A → 𝔔 = GlobalTheory.KeyOriginCut.originIdeal S := by
  first | (exact @GlobalTheory.PolyOrigin.polyOrigin) | (exact GlobalTheory.PolyOrigin.polyOrigin) | (intros; apply GlobalTheory.PolyOrigin.polyOrigin  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomUniqueAdicCompleteStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_ring_hom_unique_adic_complete : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], (∀ f : ℤ_[p] →+* O, f = padicToO p O) ∧ ∀ (h : ℕ) (f : ℤ_[p] →+* Matrix (Fin h) (Fin h) O) (c : ℤ_[p]), f c = padicToO p O c • (1 : Matrix (Fin h) (Fin h) O) := by
  first | exact @GlobalTheory.padic_ringHom_unique | exact GlobalTheory.padic_ringHom_unique | (intros; apply GlobalTheory.padic_ringHom_unique <;> assumption)
end

