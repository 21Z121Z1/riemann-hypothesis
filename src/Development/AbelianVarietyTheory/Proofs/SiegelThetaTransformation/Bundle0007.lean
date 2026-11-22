import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0002
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInnerProductSelfNonnegBounds
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.IpPos

open NumberField

variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.exists_of_mem_perSub {R : ℕ} {x : Matrix κ ι K}
    (hx : x ∈ _root_.GlobalTheory.SW.perSub K κ ι R) :
    ∃ y : Matrix κ ι K, _root_.GlobalTheory.SW.IntM y ∧ x = (R : K) • y := by
  obtain ⟨y, rfl⟩ := (_root_.GlobalTheory.SW.HaarLevel.mem_perSub R x).mp hx
  exact ⟨_root_.GlobalTheory.SW.HaarLevel.incl K κ ι y,
    (_root_.GlobalTheory.SW.HaarLevel.intM_iff _).mpr ⟨y, rfl⟩,
    (Nat.cast_smul_eq_nsmul K R _).symm⟩

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.apply_out_mk {R : ℕ} {φ : Matrix κ ι K → ℂ}
    (h : _root_.GlobalTheory.SW.HasLevel R φ) (x : Matrix κ ι K) :
    φ (QuotientAddGroup.mk (s := _root_.GlobalTheory.SW.perSub K κ ι R) x).out = φ x := by
  have hmem := QuotientAddGroup.eq.mp
    (QuotientAddGroup.out_eq' (QuotientAddGroup.mk (s := _root_.GlobalTheory.SW.perSub K κ ι R) x)).symm
  rw [← _root_.GlobalTheory.SW.HaarLevel.periodic h x _ hmem, add_neg_cancel_left]

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.intM_natCast_smul (n : ℕ) {x : Matrix κ ι K}
    (hx : _root_.GlobalTheory.SW.IntM x) : _root_.GlobalTheory.SW.IntM ((n : K) • x) := by
  intro k i
  rw [Matrix.smul_apply, smul_eq_mul]
  exact (isIntegral_natCast n).mul (hx k i)

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.hasLevel_mul {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : _root_.GlobalTheory.SW.HasLevel R φ)
    (S : ℕ) : _root_.GlobalTheory.SW.HasLevel (R * S) φ := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact _root_.GlobalTheory.SW.IpPos.intM_natCast_smul S (h.1 x hx)
  · rw [Nat.cast_mul, mul_smul]
    exact h.2 x _ (_root_.GlobalTheory.SW.IpPos.intM_natCast_smul S hy)

def classes (K κ ι : Type) [Field K] (R : ℕ) : Set (Matrix κ ι K ⧸ perSub K κ ι R) :=
  {q | IntM ((R : K) • q.out)}

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.classes_finite_card {R : ℕ} (hR : 0 < R) :
    (_root_.GlobalTheory.SW.IpPos.classes K κ ι R).Finite ∧
      (_root_.GlobalTheory.SW.IpPos.classes K κ ι R).ncard ≤
      (R ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι))) ^ 2 := by
  set L := _root_.GlobalTheory.SW.perSub K κ ι 1
  set H := (_root_.GlobalTheory.SW.perSub K κ ι (1 * (R * R))).addSubgroupOf L
  have hRK : (R : K) ≠ 0 := Nat.cast_ne_zero.mpr hR.ne'
  have hidx : H.index = (R ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι))) ^ 2 := by
    show (_root_.GlobalTheory.SW.perSub K κ ι (1 * (R * R))).relIndex L = _
    rw [_root_.GlobalTheory.SW.HaarLevel.relIndex_perSub 1 (R * R) one_pos, mul_pow, ← sq]
  let g : L →+ Matrix κ ι K ⧸ _root_.GlobalTheory.SW.perSub K κ ι R :=
    (QuotientAddGroup.mk' _).comp
      ((DistribMulAction.toAddMonoidHom (Matrix κ ι K) ((R : K)⁻¹)).comp L.subtype)
  have hker : H ≤ g.ker := by
    intro z hz
    rw [AddMonoidHom.mem_ker]
    obtain ⟨y, hy, hzy⟩ :=
      _root_.GlobalTheory.SW.IpPos.exists_of_mem_perSub (AddSubgroup.mem_addSubgroupOf.mp hz)
    simp only [g, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
      DistribMulAction.toAddMonoidHom_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, hzy, smul_smul]
    rw [show ((R : K))⁻¹ * ((1 * (R * R) : ℕ) : K) = R by push_cast; field_simp]
    exact AddSubgroup.subset_closure ⟨y, hy, rfl⟩
  let F := QuotientAddGroup.lift H g hker
  have hsub : _root_.GlobalTheory.SW.IpPos.classes K κ ι R ⊆ Set.range F := by
    intro q hq
    have hL : (R : K) • q.out ∈ L :=
      AddSubgroup.subset_closure ⟨_, hq, by rw [Nat.cast_one, one_smul]⟩
    refine ⟨QuotientAddGroup.mk ⟨_, hL⟩, ?_⟩
    simp only [F, QuotientAddGroup.lift_mk, g, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
      DistribMulAction.toAddMonoidHom_apply, QuotientAddGroup.mk'_apply, smul_smul,
      inv_mul_cancel₀ hRK, one_smul]
    exact QuotientAddGroup.out_eq' q
  have hfin : Finite (L ⧸ H) := Nat.finite_of_card_ne_zero (by
    rw [← AddSubgroup.index, hidx]; positivity)
  refine ⟨(Set.finite_range F).subset hsub, ?_⟩
  calc (_root_.GlobalTheory.SW.IpPos.classes K κ ι R).ncard ≤ (Set.range F).ncard :=
        Set.ncard_le_ncard hsub (Set.finite_range F)
    _ = Nat.card (Set.range F) := (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card (L ⧸ H) := Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
    _ = _ := hidx

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.ip_eq_sum {R : ℕ} (hR : 0 < R) {φ ψ : Matrix κ ι K → ℂ}
    (hφ : _root_.GlobalTheory.SW.HasLevel R φ) (hψ : _root_.GlobalTheory.SW.HasLevel R ψ) :
    _root_.GlobalTheory.SW.ip φ ψ =
      ((R : ℂ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)))⁻¹ *
      ∑ q ∈ (_root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hR).1.toFinset,
        φ q.out * conj (ψ q.out) := by
  have hlev : _root_.GlobalTheory.SW.HasLevel R (fun x => φ x * conj (ψ x)) := by
    refine ⟨fun x hx => hφ.1 x (left_ne_zero_of_mul hx), fun x y hy => ?_⟩
    simp only [hφ.2 x y hy, hψ.2 x y hy]
  unfold _root_.GlobalTheory.SW.ip
  rw [(_root_.GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR hlev).1]
  unfold _root_.GlobalTheory.SW.haarAt
  congr 1
  refine finsum_eq_sum_of_support_subset _ ?_
  intro q hq
  rw [Set.Finite.coe_toFinset]
  exact hφ.1 _ (left_ne_zero_of_mul hq)

end GlobalTheory.SW.IpPos

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
private lemma schwartzBruhatInnerProduct_self_eq_lemma {R : ℕ} (hR : 0 < R) {φ : Matrix κ ι K → ℂ}
    (hφ : _root_.GlobalTheory.SW.HasLevel R φ) :
    _root_.GlobalTheory.SW.ip φ φ =
      (((R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)))⁻¹ *
      ∑ q ∈ (_root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hR).1.toFinset,
        ‖φ q.out‖ ^ 2 : ℝ) := by
  rw [_root_.GlobalTheory.SW.IpPos.ip_eq_sum hR hφ hφ]
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

open Matrix Complex in
open scoped ComplexConjugate Real in

theorem _root_.GlobalTheory.SW.ip_self_nonneg_and_bounds : ∀ (K κ ι : Type) [Field K] [NumberField K]
    [Fintype κ] [Fintype ι] (R : ℕ) (φ : Matrix κ ι K → ℂ), 0 < R → _root_.GlobalTheory.SW.HasLevel R φ →
    (_root_.GlobalTheory.SW.ip φ φ).im = 0 ∧ 0 ≤ (_root_.GlobalTheory.SW.ip φ φ).re ∧
    (∀ x, ‖φ x‖ ^ 2 ≤ (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) *
      (_root_.GlobalTheory.SW.ip φ φ).re) ∧
    (∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) → (_root_.GlobalTheory.SW.ip φ φ).re ≤
      (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) * B ^ 2) ∧
    (∃ B : ℝ, ∀ x, ‖φ x‖ ≤ B) ∧ ∀ ψ, _root_.GlobalTheory.SW.IsSB ψ →
      ‖_root_.GlobalTheory.SW.ip φ ψ‖ ^ 2 ≤
        (_root_.GlobalTheory.SW.ip φ φ).re * (_root_.GlobalTheory.SW.ip ψ ψ).re := by
  intro K κ ι _ _ _ _ R φ hR hφ
  set N := Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)
  have hfc := _root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hR
  set s := hfc.1.toFinset with hs
  set Sφ := ∑ q ∈ s, ‖φ q.out‖ ^ 2 with hSφ
  have hc : (0 : ℝ) < (R : ℝ) ^ N := by positivity
  have hip : _root_.GlobalTheory.SW.ip φ φ = (((R : ℝ) ^ N)⁻¹ * Sφ : ℝ) :=
    schwartzBruhatInnerProduct_self_eq_lemma hR hφ
  have hre : (_root_.GlobalTheory.SW.ip φ φ).re = ((R : ℝ) ^ N)⁻¹ * Sφ := by
    rw [hip, Complex.ofReal_re]
  have hS0 : 0 ≤ Sφ := Finset.sum_nonneg fun _ _ => by positivity
  have hpt : ∀ x, ‖φ x‖ ^ 2 ≤ (R : ℝ) ^ N * (_root_.GlobalTheory.SW.ip φ φ).re := by
    intro x
    rw [hre, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    by_cases hx : φ x = 0
    · simpa [hx] using hS0
    · have hq : (QuotientAddGroup.mk x : Matrix κ ι K ⧸ _root_.GlobalTheory.SW.perSub K κ ι R) ∈ s := by
        rw [hs, Set.Finite.mem_toFinset]
        show _root_.GlobalTheory.SW.IntM _
        exact hφ.1 _ (by rwa [_root_.GlobalTheory.SW.IpPos.apply_out_mk hφ])
      have h := Finset.single_le_sum (f := fun q => ‖φ q.out‖ ^ 2) (fun _ _ => by positivity) hq
      simpa only [_root_.GlobalTheory.SW.IpPos.apply_out_mk hφ] using h
  refine ⟨by rw [hip, Complex.ofReal_im], by rw [hre]; positivity, hpt, fun B hB => ?_,
    ⟨√((R : ℝ) ^ N * (_root_.GlobalTheory.SW.ip φ φ).re), fun x => by
      simpa using Real.abs_le_sqrt (hpt x)⟩, fun ψ hψ => ?_⟩
  · have h1 : Sφ ≤ s.card • B ^ 2 :=
      Finset.sum_le_card_nsmul _ _ _ (fun q _ => pow_le_pow_left₀ (norm_nonneg _) (hB _) 2)
    have hcard : (s.card : ℝ) ≤ ((R : ℝ) ^ N) ^ 2 := by
      rw [hs, ← Set.ncard_eq_toFinset_card _ hfc.1]
      exact_mod_cast hfc.2
    rw [nsmul_eq_mul] at h1
    rw [hre]
    calc ((R : ℝ) ^ N)⁻¹ * Sφ ≤ ((R : ℝ) ^ N)⁻¹ * (((R : ℝ) ^ N) ^ 2 * B ^ 2) := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_right hcard (sq_nonneg B))
      _ = (R : ℝ) ^ N * B ^ 2 := by field_simp
  · obtain ⟨S, hS, hψS⟩ := hψ
    have hRS : 0 < R * S := Nat.mul_pos hR hS
    have hφ' := _root_.GlobalTheory.SW.IpPos.hasLevel_mul hφ S
    have hψ' : _root_.GlobalTheory.SW.HasLevel (R * S) ψ := by
      rw [mul_comm]; exact _root_.GlobalTheory.SW.IpPos.hasLevel_mul hψS R
    rw [_root_.GlobalTheory.SW.IpPos.ip_eq_sum hRS hφ' hψ',
      schwartzBruhatInnerProduct_self_eq_lemma hRS hφ', schwartzBruhatInnerProduct_self_eq_lemma hRS hψ',
      Complex.ofReal_re, Complex.ofReal_re, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    set t := (_root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hRS).1.toFinset
    set d : ℝ := ((R * S : ℕ) : ℝ) ^ N
    have hcs : ‖∑ q ∈ t, φ q.out * conj (ψ q.out)‖ ^ 2 ≤
        (∑ q ∈ t, ‖φ q.out‖ ^ 2) * ∑ q ∈ t, ‖ψ q.out‖ ^ 2 := by
      calc _ ≤ (∑ q ∈ t, ‖φ q.out‖ * ‖ψ q.out‖) ^ 2 := by
            gcongr
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            simp [Complex.norm_conj]
        _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    calc (d⁻¹ * ‖∑ q ∈ t, φ q.out * conj (ψ q.out)‖) ^ 2
        = d⁻¹ * d⁻¹ * ‖∑ q ∈ t, φ q.out * conj (ψ q.out)‖ ^ 2 := by ring
      _ ≤ d⁻¹ * d⁻¹ * ((∑ q ∈ t, ‖φ q.out‖ ^ 2) * ∑ q ∈ t, ‖ψ q.out‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = _ := by ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelThetaMulConjEqBlockTheta
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.ThetaProd

theorem hasLevel_mul {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ} (S : ℕ)
    {φ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) : HasLevel (S * R) φ := by
  refine ⟨fun x hx k i => ?_, fun x y hy => ?_⟩
  · have := (h.1 x hx k i).nsmul S
    simpa [mul_assoc] using this
  · have := h.2 x ((S : ℚ) • y) fun k i => by simpa using (hy k i).nsmul S
    rw [← this, smul_smul, Nat.cast_mul, mul_comm]

theorem isSB_prod {κ ι₁ ι₂ : Type} [Fintype κ] [Fintype ι₁] [Fintype ι₂]
    {φ₁ : Matrix κ ι₁ ℚ → ℂ} {φ₂ : Matrix κ ι₂ ℚ → ℂ} (h₁ : IsSB φ₁) (h₂ : IsSB φ₂) :
    IsSB (fun m : Matrix κ (ι₁ ⊕ ι₂) ℚ => φ₁ m.toCols₁ * conj (φ₂ (-m.toCols₂))) := by
  obtain ⟨R₁, hR₁, h₁⟩ := h₁
  obtain ⟨R₂, hR₂, h₂⟩ := h₂
  have g₁ := hasLevel_mul R₂ h₁
  have g₂ := hasLevel_mul R₁ h₂
  rw [mul_comm] at g₁
  refine ⟨R₁ * R₂, by positivity, fun x hx k i => ?_, fun x y hy => ?_⟩
  · have a₁ := g₁.1 _ (left_ne_zero_of_mul hx)
    have a₂ := g₂.1 _ ((map_ne_zero conj).1 (right_ne_zero_of_mul hx))
    rcases i with i | i
    · exact a₁ k i
    · have := (a₂ k i).neg
      simpa [toCols₂] using this
  · have a₁ := g₁.2 x.toCols₁ y.toCols₁ fun k i => hy k (Sum.inl i)
    have a₂ := g₂.2 (-x.toCols₂) (-y.toCols₂) fun k i => (hy k (Sum.inr i)).neg
    have e₁ : (x + ((R₁ * R₂ : ℕ) : ℚ) • y).toCols₁ =
      x.toCols₁ + ((R₁ * R₂ : ℕ) : ℚ) • y.toCols₁ := rfl
    have e₂ : -(x + ((R₁ * R₂ : ℕ) : ℚ) • y).toCols₂ =
      -x.toCols₂ + ((R₁ * R₂ : ℕ) : ℚ) • (-y.toCols₂) := by
      rw [smul_neg, ← neg_add]; rfl
    simp only [e₁, e₂, a₁, a₂]

theorem fromBlocks_mem_siegel {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {τ₁ : Matrix ι₁ ι₁ ℂ} {τ₂ : Matrix ι₂ ι₂ ℂ} (h₁ : τ₁ ∈ Siegel ι₁) (h₂ : τ₂ ∈ Siegel ι₂) :
    Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj)) ∈ Siegel (ι₁ ⊕ ι₂) := by
  refine ⟨Matrix.IsSymm.fromBlocks h₁.1 (by simp) (h₂.1.map _).neg, ?_⟩
  have e : (Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj))).map Complex.im =
      Matrix.fromBlocks (τ₁.map Complex.im) 0 0 (τ₂.map Complex.im) := by
    ext (i | i) (j | j) <;> simp
  rw [e]
  refine Matrix.posDef_iff_dotProduct_mulVec.2
    ⟨Matrix.IsHermitian.fromBlocks h₁.2.isHermitian (by simp) h₂.2.isHermitian, fun x hx => ?_⟩
  obtain ⟨u, v, rfl⟩ : ∃ u v, x = Sum.elim u v :=
    ⟨x ∘ Sum.inl, x ∘ Sum.inr, (Sum.elim_comp_inl_inr x).symm⟩
  rw [star_trivial, fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero, zero_add]
  have a := h₁.2.posSemidef.dotProduct_mulVec_nonneg u
  have b := h₂.2.posSemidef.dotProduct_mulVec_nonneg v
  rw [star_trivial] at a b
  by_cases hu : u = 0
  · have hv : v ≠ 0 := by
      rintro rfl
      apply hx
      rw [hu]
      ext (i | i) <;> rfl
    have := h₂.2.dotProduct_mulVec_pos hv
    rw [star_trivial] at this
    linarith
  · have := h₁.2.dotProduct_mulVec_pos hu
    rw [star_trivial] at this
    linarith

def colsEquiv (κ ι₁ ι₂ : Type) : Matrix κ (ι₁ ⊕ ι₂) ℚ ≃ Matrix κ ι₁ ℚ × Matrix κ ι₂ ℚ where
  toFun m := (m.toCols₁, -m.toCols₂)
  invFun p := fromCols p.1 (-p.2)
  left_inv m := by simp
  right_inv p := by simp

theorem row_exponent {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (τ₁ : Matrix ι₁ ι₁ ℂ) (τ₂ : Matrix ι₂ ι₂ ℂ) (ζ₁ : ι₁ → ℂ) (ζ₂ : ι₂ → ℂ) (v : ι₁ ⊕ ι₂ → ℚ) :
    qv v ⬝ᵥ Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj)) *ᵥ qv v +
        2 * (qv v ⬝ᵥ Sum.elim ζ₁ (star ζ₂)) =
      (qv (fun i => v (Sum.inl i)) ⬝ᵥ τ₁ *ᵥ qv (fun i => v (Sum.inl i)) +
        2 * (qv (fun i => v (Sum.inl i)) ⬝ᵥ ζ₁)) -
      conj (qv (fun i => -v (Sum.inr i)) ⬝ᵥ τ₂ *ᵥ qv (fun i => -v (Sum.inr i)) +
        2 * (qv (fun i => -v (Sum.inr i)) ⬝ᵥ ζ₂)) := by
  have h2 : conj (2 : ℂ) = 2 := map_ofNat _ 2
  simp [dotProduct, mulVec, qv, Fintype.sum_sum_type, h2]
  ring

theorem thS_mul_conj_thS : ∀ (κ ι₁ ι₂ : Type) [Fintype κ] [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] (φ₁ : Matrix κ ι₁ ℚ → ℂ) (φ₂ : Matrix κ ι₂ ℚ → ℂ), IsSB φ₁ → IsSB φ₂ → IsSB (fun m : Matrix κ (ι₁ ⊕ ι₂) ℚ => φ₁ m.toCols₁ * conj (φ₂ (-m.toCols₂))) ∧ ∀ τ₁ ∈ Siegel ι₁, ∀ τ₂ ∈ Siegel ι₂, Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj)) ∈ Siegel (ι₁ ⊕ ι₂) ∧ ∀ (ζ₁ : κ → ι₁ → ℂ) (ζ₂ : κ → ι₂ → ℂ), thS φ₁ τ₁ ζ₁ * conj (thS φ₂ τ₂ ζ₂) = thS (fun m : Matrix κ (ι₁ ⊕ ι₂) ℚ => φ₁ m.toCols₁ * conj (φ₂ (-m.toCols₂))) (Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj))) (fun k => Sum.elim (ζ₁ k) (star (ζ₂ k))) := by
  intro κ ι₁ ι₂ _ _ _ _ _ φ₁ φ₂ h₁ h₂
  refine ⟨isSB_prod h₁ h₂, fun τ₁ t₁ τ₂ t₂ => ⟨fromBlocks_mem_siegel t₁ t₂, fun ζ₁ ζ₂ => ?_⟩⟩
  have s₁ := SiegelSum.summable_norm_thetaTerm κ ι₁ φ₁ h₁ τ₁ t₁ ζ₁
  have s₂ := SiegelSum.summable_norm_thetaTerm κ ι₂ φ₂ h₂ τ₂ t₂ ζ₂
  unfold thS
  rw [Complex.conj_tsum, tsum_mul_tsum_of_summable_norm s₁
    (by simpa only [Complex.norm_conj] using s₂), ← (colsEquiv κ ι₁ ι₂).tsum_eq]
  refine tsum_congr fun m => ?_
  simp only [row_exponent, Finset.sum_sub_distrib, mul_sub, ← map_sum]
  rw [map_mul, ← Complex.exp_conj, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I,
    sub_eq_add_neg, Complex.exp_add, mul_mul_mul_comm, mul_neg, neg_mul]
  rfl

end GlobalTheory.SW.ThetaProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TsumSchwartzBruhatLevelEqSumResidueCosets
section
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.FourierJ

open Matrix Complex in
open scoped ComplexConjugate Real in
private theorem rep_eq_of_neg_rep_add_rep_eq_smul_zm {κ ι : Type} {R : ℕ} (hR : 0 < R)
    {n n' : κ → ι → Fin (R * R)} (m : κ → ι → ℤ)
    (hm : -_root_.GlobalTheory.SW.FourierJ.rep R n + _root_.GlobalTheory.SW.FourierJ.rep R n' =
      R • _root_.GlobalTheory.SW.FourierJ.zm m) : n = n' := by
    funext k i
    have hk := congrFun (congrFun hm k) i
    simp only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.neg_apply,
      Matrix.of_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul] at hk
    have hRq : (R : ℚ) ≠ 0 := by positivity
    rw [neg_add_eq_sub, ← sub_div, div_eq_iff hRq] at hk
    have hzq : ((n' k i : ℕ) : ℚ) - (n k i : ℕ) = (R : ℚ) * R * m k i := by
      linear_combination hk
    have hz : ((n' k i : ℕ) : ℤ) - (n k i : ℕ) = (R : ℤ) * R * m k i := by
      exact_mod_cast hzq
    have hb : ((n' k i : ℕ) : ℤ) < (R : ℤ) * R := by exact_mod_cast (n' k i).isLt
    have ha : ((n k i : ℕ) : ℤ) < (R : ℤ) * R := by exact_mod_cast (n k i).isLt
    have h0 : ((n' k i : ℕ) : ℤ) - (n k i : ℕ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd ⟨m k i, hz⟩
      rw [abs_lt]
      constructor <;>
        linarith [Int.natCast_nonneg (n k i : ℕ), Int.natCast_nonneg (n' k i : ℕ)]
    exact Fin.ext (by omega)

open Matrix Complex in
open scoped ComplexConjugate Real in
private theorem exists_rep_add_natCast_smul_zm_of_intM_smul {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ}
    (hR : 0 < R) (x : Matrix κ ι ℚ) (hx : _root_.GlobalTheory.SW.IntM (R • x)) :
    ∃ (n : κ → ι → Fin (R * R)) (m : κ → ι → ℤ),
      x = _root_.GlobalTheory.SW.FourierJ.rep R n + R • _root_.GlobalTheory.SW.FourierJ.zm m := by
  obtain ⟨M, hM⟩ := (_root_.GlobalTheory.SW.FourierJ.intM_iff _).mp hx
  have hRR : (0 : ℤ) < (R : ℤ) * R := by positivity
  have hRq : (R : ℚ) ≠ 0 := by positivity
  refine ⟨fun k i => ⟨(M k i % ((R : ℤ) * R)).toNat, ?_⟩, fun k i => M k i / ((R : ℤ) * R), ?_⟩
  · have h1 := Int.emod_nonneg (M k i) hRR.ne'
    have h2 := Int.emod_lt_of_pos (M k i) hRR
    have h3 : ((M k i % ((R : ℤ) * R)).toNat : ℤ) < (R : ℤ) * R := by
      rw [Int.toNat_of_nonneg h1]; exact h2
    exact_mod_cast h3
  · ext k i
    have hk := congrFun (congrFun hM k) i
    simp only [Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, Matrix.of_apply, nsmul_eq_mul] at hk
    simp only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.smul_apply,
      Matrix.of_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul]
    have h1 := Int.emod_nonneg (M k i) hRR.ne'
    have hn : (((M k i % ((R : ℤ) * R)).toNat : ℕ) : ℚ) = ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h1]
    have hq : ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) + (R : ℚ) * R * ((M k i / ((R : ℤ) * R) : ℤ) : ℚ)
        = (M k i : ℚ) := by
      have := Int.mul_ediv_add_emod (M k i) ((R : ℤ) * R)
      have h' : (R : ℚ) * R * ((M k i / ((R : ℤ) * R) : ℤ) : ℚ) +
          ((M k i % ((R : ℤ) * R) : ℤ) : ℚ) = (M k i : ℚ) := by
        exact_mod_cast this
      linear_combination h'
    have hx' : x k i = (M k i : ℚ) / R := by
      rw [eq_div_iff hRq]
      linear_combination hk
    rw [hx', hn, ← hq, add_div]
    congr 1
    rw [mul_assoc, mul_div_cancel_left₀ _ hRq]

open Matrix Complex in
open scoped ComplexConjugate Real in

theorem _root_.GlobalTheory.SW.FourierJ.tsum_level_eq_sum_cosets : ∀ (κ ι : Type) [Fintype κ] [Fintype ι]
    [DecidableEq κ]
    [DecidableEq ι] (R : ℕ) (φ F : Matrix κ ι ℚ → ℂ), 0 < R → _root_.GlobalTheory.SW.HasLevel R φ →
    Summable (fun x => φ x * F x) → ∑' x, φ x * F x =
      ∑ n : κ → ι → Fin (R * R), φ (_root_.GlobalTheory.SW.FourierJ.rep R n) *
        ∑' m : κ → ι → ℤ, F (_root_.GlobalTheory.SW.FourierJ.rep R n +
          (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zm m) := by
  intro κ ι _ _ _ _ R φ F hR hφ hsum
  have hRq : (R : ℚ) ≠ 0 := by positivity
  have hsmul : ∀ m : κ → ι → ℤ, (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zm m = R • _root_.GlobalTheory.SW.FourierJ.zm m :=
    fun m => Nat.cast_smul_eq_nsmul ℚ R _
  let e : (κ → ι → Fin (R * R)) × (κ → ι → ℤ) → Matrix κ ι ℚ := fun p =>
    _root_.GlobalTheory.SW.FourierJ.rep R p.1 + (R : ℚ) • _root_.GlobalTheory.SW.FourierJ.zm p.2
  have he : Function.Injective e := by
    rintro ⟨n, m⟩ ⟨n', m'⟩ h
    simp only [e] at h
    have hn : n = n' := by
      apply rep_eq_of_neg_rep_add_rep_eq_smul_zm hR (m - m')
      ext k i
      have hk := congrFun (congrFun h k) i
      simp only [_root_.GlobalTheory.SW.FourierJ.rep, Matrix.add_apply, Matrix.neg_apply,
        Matrix.of_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, nsmul_eq_mul, smul_eq_mul,
        Pi.sub_apply] at hk ⊢
      push_cast
      linear_combination -hk
    subst hn
    have hm : m = m' := by
      funext k i
      have hk := congrFun (congrFun h k) i
      simp only [Matrix.add_apply, Matrix.smul_apply, _root_.GlobalTheory.SW.FourierJ.zm, Matrix.of_apply,
        smul_eq_mul, add_right_inj] at hk
      exact_mod_cast mul_left_cancel₀ hRq hk
    rw [hm]
  have hsupp : Function.support (fun x => φ x * F x) ⊆ Set.range e := by
    intro x hx
    have hφx : φ x ≠ 0 := left_ne_zero_of_mul (Function.mem_support.mp hx)
    obtain ⟨n, m, hnm⟩ := exists_rep_add_natCast_smul_zm_of_intM_smul hR x (hφ.1 x hφx)
    exact ⟨(n, m), by simp only [e, hsmul]; exact hnm.symm⟩
  rw [← he.tsum_eq hsupp]
  have hs2 : Summable fun p => φ (e p) * F (e p) := hsum.comp_injective he
  rw [hs2.tsum_prod' (fun n => hs2.comp_injective (by intro m m' h; simpa using h)),
    tsum_fintype]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  simp only [e]
  rw [hφ.2 _ _ ((_root_.GlobalTheory.SW.FourierJ.intM_iff _).mpr ⟨m, rfl⟩)]

end GlobalTheory.SW.FourierJ
end

