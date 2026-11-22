import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0006

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldTopologyNormBalls
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QLTop

theorem isOpen_integers (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    IsOpen ((𝒪[F] : Subring F) : Set F) := by
  refine AddSubgroup.isOpen_of_mem_nhds (𝒪[F] : Subring F).toAddSubgroup (g := 0) ?_
  refine (IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.mpr ⟨1, one_ne_zero, fun x hx => ?_⟩
  exact (Valuation.mem_integer_iff _ _).mpr (le_of_lt hx)

theorem nrm_le_one_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ} (h : LF O ϖ nrm q) :
    1 < q ∧ ∀ x : F, nrm x ≤ 1 ↔ x ∈ O := by
  have hq : 1 < q := by rw [h.card]; exact Finite.one_lt_card
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  refine ⟨hq, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hv : ValuativeRel.valuation F ϖ < 1 := (h.lt_one ϖ).mpr ⟨1, O.one_mem, (mul_one _).symm⟩
  have hv0 : 0 < ValuativeRel.valuation F ϖ := zero_lt_iff.mpr (by simpa using h.ne)
  have hx0 : 0 < ValuativeRel.valuation F x := zero_lt_iff.mpr (by simpa using hx)
  haveI : MulArchimedean (ValuativeRel.ValueGroupWithZero F) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  have hw : 1 < (ValuativeRel.valuation F ϖ)⁻¹ := (one_lt_inv₀ hv0).mpr hv
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℤ, (ValuativeRel.valuation F ϖ)⁻¹ ^ n < ValuativeRel.valuation F x ∧
      ValuativeRel.valuation F x ≤ (ValuativeRel.valuation F ϖ)⁻¹ ^ (n + 1) := by
    obtain ⟨a, ha⟩ := exists_pow_lt₀ hv (Units.mk0 _ hx0.ne')
    obtain ⟨b, hb⟩ := exists_pow_lt₀ hv (Units.mk0 _ (inv_pos.mpr hx0).ne')
    simp only [Units.val_mk0] at ha hb
    obtain ⟨m, hm, hmin⟩ := Int.exists_least_of_bdd
      (P := fun z : ℤ => ValuativeRel.valuation F x ≤ (ValuativeRel.valuation F ϖ)⁻¹ ^ z)
      ⟨-(a : ℤ), fun z hz => by
        have h1 : (ValuativeRel.valuation F ϖ)⁻¹ ^ (-(a : ℤ)) < (ValuativeRel.valuation F ϖ)⁻¹ ^ z := by
          refine lt_of_lt_of_le ?_ hz
          simpa using ha
        exact ((zpow_lt_zpow_iff_right₀ hw).mp h1).le⟩
      ⟨(b : ℤ), by
        rw [zpow_natCast, inv_pow]
        exact ((lt_inv_comm₀ (pow_pos hv0 b) hx0).mp hb).le⟩
    refine ⟨m - 1, ?_, by simpa using hm⟩
    by_contra hc
    have := hmin _ (not_lt.mp hc)
    omega
  rw [_root_.inv_zpow] at hn1 hn2
  have hp : ∀ m : ℤ, 0 < ValuativeRel.valuation F ϖ ^ m := fun m => zpow_pos hv0 m
  have hy : ValuativeRel.valuation F (x * ϖ ^ (n + 1)) = 1 := by
    have hle : ValuativeRel.valuation F (x * ϖ ^ (n + 1)) ≤ 1 := by
      rw [map_mul, map_zpow₀]
      rwa [← one_mul (_ ⁻¹), le_mul_inv_iff₀ (hp _)] at hn2
    by_contra hne
    obtain ⟨o, ho, he⟩ := (h.lt_one _).mp (lt_of_le_of_ne hle hne)
    rw [zpow_add_one₀ h.ne, ← mul_assoc, mul_comm ϖ o] at he
    have he' := mul_right_cancel₀ h.ne he
    rw [← he', h.O_eq, Valuation.mem_integer_iff, map_mul, map_zpow₀] at ho
    rw [← one_mul (_ ⁻¹), mul_inv_lt_iff₀ (hp _)] at hn1
    exact absurd ho (not_le.mpr hn1)
  have hn := h.nrm_unit _ hy
  rw [map_mul, map_zpow₀, h.nrm_pi, _root_.inv_zpow, mul_inv_eq_one₀ (zpow_ne_zero _ (by positivity))] at hn
  rw [map_mul, map_zpow₀] at hy
  have hy' : ValuativeRel.valuation F x = (ValuativeRel.valuation F ϖ)⁻¹ ^ (n + 1) := by
    rw [_root_.inv_zpow]; exact eq_inv_of_mul_eq_one_left hy
  rw [hn, h.O_eq, Valuation.mem_integer_iff, hy', zpow_le_one_iff_right₀ hq1, zpow_le_one_iff_right₀ hw]

theorem localField_top : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → IsOpen (O : Set F) ∧ IsCompact (O : Set F) ∧ SecondCountableTopology F ∧ Continuous (fun x : F => nrm x) ∧ (∀ e : ℤ, IsOpen {x : F | nrm x ≤ (q : ℝ) ^ e}) ∧ (∀ s ∈ nhds (0 : F), ∃ e : ℤ, {x : F | nrm x ≤ (q : ℝ) ^ e} ⊆ s) := by
  intro F _ _ _ _ O ϖ nrm q h
  obtain ⟨hq, hle⟩ := nrm_le_one_iff h
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := lt_trans one_pos hq1
  have hO : IsOpen (O : Set F) := by rw [h.O_eq]; exact isOpen_integers F
  have hball : ∀ (e : ℤ) (x : F), nrm x ≤ (q : ℝ) ^ e ↔ x * ϖ ^ e ∈ O := by
    intro e x
    rw [← hle, map_mul, map_zpow₀, h.nrm_pi, _root_.inv_zpow, ← div_eq_mul_inv, div_le_one (zpow_pos hq0 e)]
  have hopen : ∀ e : ℤ, IsOpen {x : F | nrm x ≤ (q : ℝ) ^ e} := by
    intro e
    have : {x : F | nrm x ≤ (q : ℝ) ^ e} = (fun x => x * ϖ ^ e) ⁻¹' (O : Set F) := by
      ext x; exact hball e x
    rw [this]
    exact hO.preimage (continuous_id.mul continuous_const)
  refine ⟨hO, ?_, GlobalTheory.SgLoc.Top.localField_secondCountable F, ?_, hopen, ?_⟩
  · rw [h.O_eq]
    exact IsNonarchimedeanLocalField.isCompact_closedBall F 1
  · rw [continuous_iff_continuousAt]
    intro x₀
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hq1)
    have hU : IsOpen ((fun x => x - x₀) ⁻¹' {x : F | nrm x ≤ (q : ℝ) ^ (-(n : ℤ))}) :=
      (hopen _).preimage (continuous_id.sub continuous_const)
    have hm : x₀ ∈ ((fun x => x - x₀) ⁻¹' {x : F | nrm x ≤ (q : ℝ) ^ (-(n : ℤ))}) := by
      show nrm (x₀ - x₀) ≤ _
      rw [sub_self, map_zero]; exact (zpow_pos hq0 _).le
    filter_upwards [hU.mem_nhds hm] with x hx
    have hx' : nrm (x - x₀) ≤ (q : ℝ) ^ (-(n : ℤ)) := hx
    rw [_root_.zpow_neg, zpow_natCast, ← inv_pow] at hx'
    rw [Real.dist_eq]
    exact lt_of_le_of_lt ((nrm.abs_abv_sub_le_abv_sub x x₀).trans hx') hn
  · intro s hs
    obtain ⟨γ, hγ, hs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.mp hs
    have hv : ValuativeRel.valuation F ϖ < 1 := (h.lt_one ϖ).mpr ⟨1, O.one_mem, (mul_one _).symm⟩
    haveI : MulArchimedean (ValuativeRel.ValueGroupWithZero F) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hv (Units.mk0 γ hγ)
    refine ⟨-(n : ℤ), fun x hx => hs ?_⟩
    have hx' := (hball _ x).mp hx
    rw [h.O_eq, Valuation.mem_integer_iff] at hx'
    have : x = (x * ϖ ^ (-(n : ℤ))) * ϖ ^ n := by
      rw [_root_.zpow_neg, zpow_natCast, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ h.ne), mul_one]
    show ValuativeRel.valuation F x < γ
    rw [this, map_mul, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hx') hn

end GlobalTheory.CompanionTheory.QLTop
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemBoxLatticeIffCongruence
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.QIndex.OnePlus

theorem nrm_det_one_add {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
    (hLF : LF O ϖ nrm q) {n : ℕ} {x : Matrix (Fin n) (Fin n) F}
    (hx : ∀ a b, ∃ o ∈ O, x a b = ϖ * o) : nrm (1 + x).det = 1 := by
  obtain ⟨-, hϖ, hle, hlt, -, -, -⟩ := GlobalTheory.CompanionTheory.QL.NormalisedValue.main hLF
  choose f hf hf' using hx
  let ϖ' : O := ⟨ϖ, hϖ⟩
  let y : Matrix (Fin n) (Fin n) O := fun a b => ⟨f a b, hf a b⟩
  let M : Matrix (Fin n) (Fin n) O := 1 + ϖ' • y
  have hM : O.subtype.mapMatrix M = 1 + x := by
    ext a b
    by_cases hab : a = b
    · simp [M, y, ϖ', hf', hab]
      rfl
    · simp [M, y, ϖ', hf', hab, Matrix.one_apply]
      rfl
  let π := Ideal.Quotient.mk (Ideal.span {ϖ'})
  have hπ : π ϖ' = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have hred : π.mapMatrix M = 1 := by
    simp only [M, map_add, map_one]
    have : π.mapMatrix (ϖ' • y) = 0 := by
      ext a b
      simp [hπ]
    rw [this, add_zero]
  have hdet : π M.det = 1 := by
    rw [RingHom.map_det, hred, Matrix.det_one]
  have hmem : M.det - 1 ∈ Ideal.span {ϖ'} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one]
    exact sub_eq_zero.2 hdet
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hmem
  have hcoe : (1 + x).det = (M.det : F) := by
    rw [← hM, ← RingHom.map_det]
    rfl
  have hEq : (1 + x).det = 1 + (a : F) * ϖ := by
    have h2 := congrArg (Subtype.val) ha
    have h3 : (a : F) * ϖ = (M.det : F) - 1 := by simpa [ϖ'] using h2
    rw [hcoe, h3]
    ring
  have hin : (1 + x).det ∈ O := by
    rw [hcoe]
    exact M.det.2
  refine le_antisymm ((hle _).2 hin) (not_lt.1 fun hl => ?_)
  obtain ⟨o, ho, e⟩ := (hlt _).1 hl
  have h1 : (1 : F) = ϖ * (o - a) := by
    have : (1 : F) + (a : F) * ϖ = ϖ * o := by rw [← hEq, e]
    linear_combination this
  have h2 : nrm (1 : F) < 1 := (hlt 1).2 ⟨o - a, O.sub_mem ho a.2, h1⟩
  simp at h2

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (β : Fin n → ℕ) (Q : Subgroup (GL (Fin n) F)), (∀ g, g ∈ Q ↔ (g : Matrix (Fin n) (Fin n) F).BlockTriangular β) → ∀ T : ℕ, 1 ≤ T → ∀ x : Matrix (Fin n) (Fin n) F, x ∈ boxAdd O β (fun _ _ => ϖ ^ T) ↔ ∃ p ∈ (congGL O (ϖ ^ T) n).subgroupOf Q, ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + x := by
  intro F _ _ _ _ O ϖ nrm q hLF n β Q hQ T hT x
  obtain ⟨-, hϖ, -, -, -, -, -⟩ := GlobalTheory.CompanionTheory.QL.NormalisedValue.main hLF
  constructor
  · rintro ⟨hbt, hent⟩
    have hx' : ∀ a b, ∃ o ∈ O, x a b = ϖ * o := fun a b => by
      obtain ⟨o, ho, e⟩ := hent a b
      have e' : x a b = ϖ ^ T * o := e
      have hTT : ϖ ^ T = ϖ * ϖ ^ (T - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hT]
      refine ⟨ϖ ^ (T - 1) * o, O.mul_mem (O.pow_mem hϖ _) ho, ?_⟩
      rw [e', hTT, mul_assoc]
    have hdet := nrm_det_one_add hLF hx'
    have hne : (1 + x).det ≠ 0 := fun e => by
      rw [e] at hdet
      simp at hdet
    let g : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + x) hne
    have hg : (g : Matrix (Fin n) (Fin n) F) = 1 + x := rfl
    have hint : IsInt O (g : Matrix (Fin n) (Fin n) F) := fun a b => by
      rw [hg, Matrix.add_apply]
      obtain ⟨o, ho, e⟩ := hx' a b
      refine O.add_mem ?_ (e ▸ O.mul_mem hϖ ho)
      by_cases hab : a = b
      · rw [hab, Matrix.one_apply_eq]
        exact O.one_mem
      · rw [Matrix.one_apply_ne hab]
        exact O.zero_mem
    have hgQ : g ∈ Q := by
      rw [hQ, hg]
      intro i j hij
      have hne' : i ≠ j := fun e => by
        subst e
        exact lt_irrefl _ hij
      simp [hbt hij, hne']
    refine ⟨⟨g, hgQ⟩, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨(GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff hLF n g).2 ⟨hint, hdet⟩, fun a b => ?_⟩
    obtain ⟨o, ho, e⟩ := hent a b
    refine ⟨o, ho, ?_⟩
    simpa [hg] using e
  · rintro ⟨p, hp, e⟩
    rw [Subgroup.mem_subgroupOf] at hp
    obtain ⟨-, hl⟩ := hp
    have hx : x = ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 := by
      rw [e]
      simp
    refine ⟨fun i j hij => ?_, fun a b => ?_⟩
    · have h0 := (hQ _).1 p.2 hij
      have hne' : i ≠ j := fun e => by
        subst e
        exact lt_irrefl _ hij
      simp [hx, h0, hne']
    · rw [hx]
      exact hl a b

end GlobalTheory.CompanionTheory.QL.QIndex.OnePlus
end

