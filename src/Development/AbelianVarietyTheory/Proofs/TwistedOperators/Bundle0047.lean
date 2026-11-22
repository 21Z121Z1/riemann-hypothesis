import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfPowerSpherical
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0040
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSumRowCol
import Formalism.RealPlaceAnalysis.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NabsDetEqOfActEq
section
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical GlobalTheory.LatPair GlobalTheory.StepData
open scoped Pointwise

noncomputable section
namespace GlobalTheory.IdealChain

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mem_idl {b : kˣ} {x : k} : x ∈ idl b ↔ valuation k x ≤ valuation k (b : k) := by
  have hb : valuation k (b : k) ≠ 0 := by simp
  rw [idl, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨s, rfl⟩
    change valuation k ((s : k) * b) ≤ _
    rw [map_mul]
    exact mul_le_of_le_one_left' s.2
  · intro h
    refine ⟨⟨x / b, ?_⟩, ?_⟩
    · change valuation k (x / b) ≤ 1
      rw [map_div₀]
      exact div_le_one_of_le₀ h zero_le
    · change x / b * b = x
      simp

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mem_idl_iff_int {b : kˣ} {x : k} : x ∈ idl b ↔ ((b⁻¹ : kˣ) : k) * x ∈ 𝒪[k] := by
  have hb : 0 < valuation k (b : k) := zero_lt_iff.2 (by simp)
  rw [mem_idl]
  change _ ↔ valuation k _ ≤ 1
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ hb, mul_one]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem idl_eq_iff {a b : kˣ} : idl a = idl b ↔ valuation k (a : k) = valuation k (b : k) := by
  constructor
  · intro h
    exact le_antisymm (mem_idl.1 (h ▸ mem_idl.2 le_rfl)) (mem_idl.1 (h ▸ mem_idl.2 le_rfl))
  · intro h
    ext x
    rw [mem_idl, mem_idl, h]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mem_monLat {n : Type} {c : ℕ} {L : Submodule 𝒪[k] (n → k)} {b : ℕ → kˣ} {v : n ⊕ Fin c → k} :
    v ∈ monLat c L b ↔ (fun r => v (Sum.inl r)) ∈ L ∧ ∀ i : Fin c, v (Sum.inr i) ∈ idl (b (i.val + 1)) := Iff.rfl

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem monLat_congr {n : Type} {c : ℕ} (L : Submodule 𝒪[k] (n → k)) {b b' : ℕ → kˣ}
    (h : ∀ i, 1 ≤ i → i ≤ c → idl (b i) = idl (b' i)) : monLat c L b = monLat c L b' := by
  ext v
  simp only [mem_monLat]
  exact and_congr_right' (forall_congr' fun i => by rw [h _ (by omega) i.2])

section Act
variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mem_act {g : GL ι k} {L : Submodule 𝒪[k] (ι → k)} {v : ι → k} : v ∈ act g L ↔ (g⁻¹).val *ᵥ v ∈ L := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · exact fun h => ⟨_, h, by simp⟩

theorem act_eq_smul (g : GL ι k) (L : Submodule 𝒪[k] (ι → k)) : act g L = g • L := by
  ext v
  rw [mem_act, mem_smul_iff]
  rfl

theorem isLattice_act (g : GL ι k) {L : Submodule 𝒪[k] (ι → k)} (h : L.IsLattice k) : (act g L).IsLattice k := by
  rw [act_eq_smul]
  infer_instance

theorem exists_act_stdLat {L : Submodule 𝒪[k] (ι → k)} (h : L.IsLattice k) : ∃ g : GL ι k, L = act g (stdLat k ι) := by
  obtain ⟨g, hg⟩ := exists_smul_lat (stdLat k ι) L
  exact ⟨g, by rw [act_eq_smul, hg]⟩

theorem act_stdLat_eq_iff {g : GL ι k} : act g (stdLat k ι) = stdLat k ι ↔ g ∈ KO k ι := by
  rw [mem_KO]
  constructor
  · intro h
    refine ⟨maps_stdLat_iff.1 fun y hy => ?_, maps_stdLat_iff.1 fun y hy => ?_⟩
    · rw [← h]
      exact ⟨y, hy, rfl⟩
    · rw [← h] at hy
      exact mem_act.1 hy
  · rintro ⟨h1, h2⟩
    ext v
    rw [mem_act]
    refine ⟨fun hv => ?_, fun hv => maps_stdLat_iff.2 h2 v hv⟩
    simpa using maps_stdLat_iff.2 h1 _ hv

theorem nabs_det_eq_of_act_eq {g h : GL ι k} {L : Submodule 𝒪[k] (ι → k)} (hL : L.IsLattice k)
    (e : act g L = act h L) :
    nabs k (Matrix.GeneralLinearGroup.det g) = nabs k (Matrix.GeneralLinearGroup.det h) := by
  obtain ⟨u, rfl⟩ := exists_act_stdLat hL
  have h1 : act ((h * u)⁻¹ * (g * u)) (stdLat k ι) = stdLat k ι := by
    rw [act_mul, act_mul g, e, ← act_mul h, ← act_mul, inv_mul_cancel, act_one]
  have h2 := valuation_det_of_mem_KO (act_stdLat_eq_iff.1 h1)
  rw [nabs_eq_iff]
  have : Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det h *
      Matrix.GeneralLinearGroup.det ((h * u)⁻¹ * (g * u)) := by
    simp only [map_mul, map_inv]
    rw [_root_.mul_inv_rev, mul_comm (Matrix.GeneralLinearGroup.det g)]
    group
    rw [mul_comm (Matrix.GeneralLinearGroup.det h)]
    group
  rw [this, Units.val_mul, map_mul, h2, mul_one]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype ι] [DecidableEq ι] [DecidableEq ι'] in
open Classical in
theorem sph_apply (α : kˣ) (L' : Submodule 𝒪[k] (ι' → k)) (L : Submodule 𝒪[k] (ι → k)) (x : Matrix ι ι' k) :
    sph α L' L x = if ∀ v ∈ L', (((α⁻¹ : kˣ) : k) • x) *ᵥ v ∈ L then 1 else 0 := by
  unfold sph
  refine if_congr (forall₂_congr fun v _ => ?_) rfl rfl
  rw [Matrix.smul_mulVec]
  constructor
  · rintro ⟨w, hw, e⟩
    rw [e, smul_smul]
    simpa using hw
  · exact fun h => ⟨_, h, by simp [smul_smul]⟩

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem sph_act (α : kˣ) (g' : GL ι' k) (g : GL ι k) (L' : Submodule 𝒪[k] (ι' → k)) (L : Submodule 𝒪[k] (ι → k))
    (x : Matrix ι ι' k) : sph α (act g' L') (act g L) x = sph α L' L ((g⁻¹).val * x * g'.val) := by
  classical
  rw [sph_apply, sph_apply]
  refine if_congr ?_ rfl rfl
  simp only [mem_act, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul]
  refine ⟨fun H y hy => H _ (by simpa using hy), fun H y hy => ?_⟩
  simpa using H _ hy

omit [DecidableEq ι] [DecidableEq ι'] in
open Classical in
theorem sph_stdLat (α : kˣ) (x : Matrix ι ι' k) :
    sph α (stdLat k ι') (stdLat k ι) x = if IntM (((α⁻¹ : kˣ) : k) • x) then 1 else 0 := by
  rw [sph_apply]
  exact if_congr maps_stdLat_iff rfl rfl

omit [DecidableEq ι] [DecidableEq ι'] in
theorem sph_mem_SB (α : kˣ) {L' : Submodule 𝒪[k] (ι' → k)} {L : Submodule 𝒪[k] (ι → k)} (h' : L'.IsLattice k)
    (h : L.IsLattice k) : sph α L' L ∈ SB (Matrix ι ι' k) := by
  classical
  have : sph α L' L = latInd L' (α • L) := by
    funext x
    rw [sph, latInd]
    refine if_congr (forall₂_congr fun v _ => ?_) rfl rfl
    refine Iff.trans ?_ (Submodule.mem_smul_pointwise_iff_exists _ α L).symm
    exact exists_congr fun w => and_congr_right' eq_comm
  rw [this]
  exact latInd_mem_SB _ _

theorem om_sph (μ : kˣ →* ℂˣ) (h : GL ι k) (α : kˣ) (L' : Submodule 𝒪[k] (ι' → k)) (L : Submodule 𝒪[k] (ι → k))
    (x : Matrix ι ι' k) : om μ 1 h (sph α L' L) x = (((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) *
      ((nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card ι' : ℝ) / 2) : ℝ) : ℂ) * sph α L' (act h L) x := by
  conv_rhs => rw [← act_one L', sph_act]
  simp [om, nabs_one]

end Act

section Half

theorem resCard_pos : (0 : ℝ) < resCard k := by exact_mod_cast (one_lt_resCard k).trans' one_pos

theorem isHalfPow_one : IsHalfPow k 1 := ⟨0, by simp⟩

theorem isHalfPow_mul {a b : ℝ} (ha : IsHalfPow k a) (hb : IsHalfPow k b) : IsHalfPow k (a * b) := by
  obtain ⟨e, rfl⟩ := ha
  obtain ⟨f, rfl⟩ := hb
  exact ⟨e + f, by rw [← Real.rpow_add resCard_pos]; push_cast; ring_nf⟩

theorem isHalfPow_inv {a : ℝ} (ha : IsHalfPow k a) : IsHalfPow k a⁻¹ := by
  obtain ⟨e, rfl⟩ := ha
  exact ⟨-e, by rw [← Real.rpow_neg resCard_pos.le]; push_cast; ring_nf⟩

theorem isHalfPow_pow {a : ℝ} (ha : IsHalfPow k a) (m : ℕ) : IsHalfPow k (a ^ m) := by
  induction m with
  | zero => simpa using isHalfPow_one
  | succ m ih => rw [pow_succ]; exact isHalfPow_mul ih ha

theorem exists_nabs_eq_zpow (x : kˣ) : ∃ e : ℤ, nabs k x = (resCard k : ℝ) ^ e := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have key : ∀ x : kˣ, (x : k) ∈ 𝒪[k] → ∃ e : ℤ, nabs k x = (resCard k : ℝ) ^ e := fun x hx => by
    obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨x, hx⟩ : 𝒪[k])) (fun h => x.ne_zero (congrArg Subtype.val h)) hϖ
    have hu' : (x : k) = ((u : 𝒪[k]) : k) * (ϖ : k) ^ m := by simpa using congrArg Subtype.val hu
    have hv : valuation k ((u : 𝒪[k]) : k) = 1 :=
      (Valuation.Integers.valuation_unit (Valuation.integer.integers (valuation k)) u)
    have : nabs k x = nabs k (Units.mk0 (ϖ : k) h0 ^ m) := by
      rw [nabs_eq_iff, hu', map_mul, hv, one_mul]
      simp
    refine ⟨-m, ?_⟩
    rw [this, OpELevi.nabs_pow, nabs_uniformiser hϖ rfl]
    simp
  rcases le_total (valuation k (x : k)) 1 with h | h
  · exact key x h
  · obtain ⟨e, he⟩ := key x⁻¹ (by
      change valuation k _ ≤ 1
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact inv_le_one_of_one_le₀ h)
    rw [OpELevi.nabs_inv] at he
    exact ⟨-e, by rw [_root_.zpow_neg, ← he, inv_inv]⟩

theorem isHalfPow_nabs_rpow (x : kˣ) (m : ℤ) : IsHalfPow k (nabs k x ^ ((m : ℝ) / 2)) := by
  obtain ⟨e, he⟩ := exists_nabs_eq_zpow x
  refine ⟨e * m, ?_⟩
  rw [he, ← Real.rpow_intCast, ← Real.rpow_mul resCard_pos.le]
  push_cast
  ring_nf

theorem isHalfPow_nabs (x : kˣ) : IsHalfPow k (nabs k x) := by
  simpa using isHalfPow_nabs_rpow x 2

end Half

end GlobalTheory.IdealChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpECutOmEquivariant
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx.CutRow

variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

end GlobalTheory.RootEx.CutRow

open MeasureTheory ValuativeRel Matrix in

theorem _root_.GlobalTheory.RootEx.opE_cut_om_equivariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (χ : (n' → k) → ℂ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : GL n k), ∀ u ∈ _root_.GlobalTheory.RootEx.N k n c p ⊓ _root_.GlobalTheory.RootEx.N k n c (p + 1), _root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (fun y => (∑ l : Fin c, if l.val + 1 = p then χ (fun s => y (Sum.inr l) (Sum.inl s)) else 0) * _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x * u) Φ y) = (((_root_.GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((p + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * (ψ (-_root_.GlobalTheory.RootEx.simpleSum u) : ℂ)) • _root_.GlobalTheory.SplitWeil.om μ 1 x (_root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (fun y => (∑ l : Fin c, if l.val + 1 = p then χ (fun s => y (Sum.inr l) (Sum.inl s)) else 0) * Φ y)) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp1 hpc ψ ν _ μ χ Φ x u hu
  obtain ⟨huP, huP1⟩ := Subgroup.mem_inf.mp hu
  set cut : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ := fun y =>
    ∑ l : Fin c, if l.val + 1 = p then χ (fun s => y (Sum.inr l) (Sum.inl s)) else 0 with hcut
  have hlevi : ∀ (g : GL n k) (y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      cut (((_root_.GlobalTheory.RootEx.embX c g : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * y) = cut y := by
    intro g y
    simp only [hcut, _root_.GlobalTheory.RootEx.Radical.embX_val, _root_.GlobalTheory.RootEx.OpELevi.left_inr]
  have hgen : _root_.GlobalTheory.RootEx.InN p u⁻¹ :=
    _root_.GlobalTheory.RootEx.Model.mem_N_iff.mp (inv_mem huP)
  have hunip : ∀ (x₀ : Matrix n n' k) (e : { rs // _root_.GlobalTheory.RootEx.Free (p + 1) rs } → k),
      cut (((u⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * _root_.GlobalTheory.RootEx.affPt (p + 1) x₀ e) =
        cut (_root_.GlobalTheory.RootEx.affPt (p + 1) x₀ e) := by
    intro x₀ e
    simp only [hcut]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs with hl
    · congr 1
      funext s
      rw [_root_.GlobalTheory.RootEx.TargetUnip.mul_apply_of_inN hgen, Finset.sum_eq_zero, add_zero]
      intro r _
      split_ifs with hlt
      · cases r with
        | inl i =>
          simp [_root_.GlobalTheory.RootEx.lev] at hlt
          omega
        | inr i =>
          simp [_root_.GlobalTheory.RootEx.lev] at hlt
          rw [_root_.GlobalTheory.RootEx.TargetUnip.affPt_of_not_free]
          · simp [_root_.GlobalTheory.RootEx.basePt]
          · simp [_root_.GlobalTheory.RootEx.Free]
            omega
      · rfl
    · rfl
  have hmul : _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x * u) Φ =
      _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x) (_root_.GlobalTheory.SplitWeil.om μ 1 u Φ) := by
    have h := _root_.GlobalTheory.SplitWeil.Model.om_mul μ 1 1 (_root_.GlobalTheory.RootEx.embX c x) u Φ
    rwa [one_mul] at h
  have hcomm : ∀ Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ,
      (fun y => cut y * _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x) Ψ y) =
        _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x) (fun y => cut y * Ψ y) := by
    intro Ψ
    funext y
    simp only [_root_.GlobalTheory.SplitWeil.om, Units.val_one, Matrix.mul_one, ← map_inv, hlevi]
    ring
  have hcut_unip : _root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (fun y => cut y * _root_.GlobalTheory.SplitWeil.om μ 1 u Φ y) =
      _root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (_root_.GlobalTheory.SplitWeil.om μ 1 u (fun y => cut y * Φ y)) := by
    funext x₀
    unfold _root_.GlobalTheory.RootEx.opE
    congr 1
    funext e
    simp only [_root_.GlobalTheory.SplitWeil.om, Units.val_one, Matrix.mul_one, hunip]
    ring
  rw [hmul, hcomm, (_root_.GlobalTheory.RootEx.opE_om_embX k n n' c (p + 1) (by omega) (by omega) ψ ν μ _).1 x,
    hcut_unip, _root_.GlobalTheory.RootEx.opE_om_target_unipotent k n n' c (p + 1) (by omega) (by omega) ψ ν μ _ u huP1]
  funext y
  simp only [_root_.GlobalTheory.SplitWeil.om, Pi.smul_apply, smul_eq_mul]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetAddOneSubEqSumQminor
section
open Formalism.REAL Finset

namespace GlobalTheory.CapelliDiff

theorem prod_ofFn_sub {A : Type*} [Ring A] [Algebra ℂ A] :
    ∀ (n : ℕ) (x y : Fin (n + 1) → A) (d : Fin (n + 1) → ℂ),
      (∀ k, y k = x k + algebraMap ℂ A (d k)) →
      (List.ofFn y).prod - (List.ofFn x).prod =
        ∑ k : Fin (n + 1), algebraMap ℂ A (d k) *
          (List.ofFn fun j : Fin n => if Fin.castSucc j < k then x (Fin.castSucc j) else y j.succ).prod := by
  intro n
  induction n with
  | zero =>
    intro x y d h
    simp [h 0]
  | succ n ih =>
    intro x y d h
    rw [List.ofFn_succ (f := y), List.ofFn_succ (f := x), List.prod_cons, List.prod_cons, Fin.sum_univ_succ]
    have key := ih (fun i => x i.succ) (fun i => y i.succ) (fun i => d i.succ) (fun i => h i.succ)
    have e1 : y 0 * (List.ofFn fun i : Fin (n+1) => y i.succ).prod - x 0 * (List.ofFn fun i : Fin (n+1) => x i.succ).prod
        = algebraMap ℂ A (d 0) * (List.ofFn fun i : Fin (n+1) => y i.succ).prod + x 0 * ((List.ofFn fun i : Fin (n+1) => y i.succ).prod - (List.ofFn fun i : Fin (n+1) => x i.succ).prod) := by
      rw [h 0]; noncomm_ring
    rw [e1, key, Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · congr 2
    · apply Finset.sum_congr rfl
      intro k _
      rw [List.ofFn_succ, List.prod_cons]
      have h0 : (Fin.castSucc (0 : Fin (n+1)) : Fin (n+2)) < k.succ := by simp [Fin.succ_pos]
      rw [if_pos h0, Fin.castSucc_zero, ← mul_assoc (x 0), ← Algebra.commutes, mul_assoc]
      have hl : (List.ofFn fun j : Fin n => if j.castSucc < k then x j.castSucc.succ else y j.succ.succ) =
          (List.ofFn fun i : Fin n => if i.succ.castSucc < k.succ then x i.succ.castSucc else y i.succ.succ) := by
        congr 1; funext j; simp only [← Fin.succ_castSucc, Fin.succ_lt_succ_iff]
      rw [hl]

theorem Tm_add_one {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (v : ℂ) (a b : Fin n) :
    Tm E (v + 1) a b = Tm E v a b + algebraMap ℂ A (if a = b then 1 else 0) := by
  unfold Tm
  split_ifs <;> simp [map_add]; abel

def extAt {m : ℕ} (k : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.Perm.ofSubtype ((finSuccAboveEquiv k).permCongr τ)

theorem extAt_succAbove {m : ℕ} (k : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) (j : Fin m) :
    extAt k τ (k.succAbove j) = k.succAbove (τ j) := by
  have hj : k.succAbove j = ((finSuccAboveEquiv k j : {x // x ≠ k}) : Fin (m + 1)) := by
    rw [finSuccAboveEquiv_apply]
  unfold extAt
  rw [hj, Equiv.Perm.ofSubtype_apply_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    finSuccAboveEquiv_apply]

theorem sign_extAt {m : ℕ} (k : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (extAt k τ) = Equiv.Perm.sign τ := by
  unfold extAt
  rw [Equiv.Perm.sign_ofSubtype, Equiv.Perm.sign_permCongr]

theorem sum_fix_eq {A : Type*} [AddCommMonoid A] {m : ℕ} (k : Fin (m + 1))
    (g : Equiv.Perm (Fin (m + 1)) → A) :
    ∑ σ : Equiv.Perm (Fin (m + 1)), (if σ k = k then g σ else 0) =
      ∑ τ : Equiv.Perm (Fin m), g (extAt k τ) := by
  let e : Equiv.Perm (Fin m) ≃ {f : Equiv.Perm (Fin (m + 1)) // ∀ a, ¬ (a ≠ k) → f a = a} :=
    ((finSuccAboveEquiv k).permCongr).trans (Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ≠ k))
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun f : Equiv.Perm (Fin (m + 1)) => ∀ a, ¬ (a ≠ k) → f a = a)]
  · rw [← Equiv.sum_comp e]
    rfl
  · intro σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    constructor
    · intro h a ha; rw [ha]; exact h
    · intro h; exact h k rfl

theorem qdet_add_one_sub (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (u : ℂ) :
    qdet E (u + 1) - qdet E u = ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u := by
  unfold qdet qminor
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  have step : ∀ σ : Equiv.Perm (Fin (m + 1)),
      (List.ofFn fun k : Fin (m + 1) => Tm E (u + 1 - (k : ℂ)) (id (σ k)) (id k)).prod -
        (List.ofFn fun k : Fin (m + 1) => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod =
      ∑ k : Fin (m + 1), algebraMap ℂ A (if σ k = k then 1 else 0) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod := by
    intro σ
    rw [prod_ofFn_sub m (fun k => Tm E (u - (k : ℂ)) (id (σ k)) (id k))
      (fun k => Tm E (u + 1 - (k : ℂ)) (id (σ k)) (id k)) (fun k => if σ k = k then 1 else 0)]
    · apply Finset.sum_congr rfl
      intro k _
      congr 2
      congr 1
      funext j
      by_cases hj : Fin.castSucc j < k
      · rw [if_pos hj, Fin.succAbove_of_castSucc_lt k j hj]
        simp [Fin.coe_castSucc]
      · rw [if_neg hj, Fin.succAbove_of_le_castSucc k j (not_lt.mp hj)]
        simp only [id, Fin.val_succ]
        congr 1
        push_cast; ring
    · intro k
      have : u + 1 - (k : ℂ) = (u - (k : ℂ)) + 1 := by ring
      simp only [this, Tm_add_one, id]
  simp_rw [step, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have h2 : ∀ σ : Equiv.Perm (Fin (m + 1)),
      ((Equiv.Perm.sign σ : ℤ) : A) * (algebraMap ℂ A (if σ k = k then 1 else 0) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod) =
      if σ k = k then ((Equiv.Perm.sign σ : ℤ) : A) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod else 0 := by
    intro σ
    split_ifs <;> simp
  simp_rw [h2]
  rw [sum_fix_eq k (fun σ => ((Equiv.Perm.sign σ : ℤ) : A) *
        (List.ofFn fun j : Fin m => Tm E (u - (j : ℂ)) (σ (k.succAbove j)) (k.succAbove j)).prod)]
  apply Finset.sum_congr rfl
  intro τ _
  simp only [sign_extAt, extAt_succAbove]

end GlobalTheory.CapelliDiff

theorem GlobalTheory.qdet_add_one_sub_eq_sum_qminor : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (u : ℂ), qdet E (u + 1) - qdet E u = ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u :=
  GlobalTheory.CapelliDiff.qdet_add_one_sub
end

