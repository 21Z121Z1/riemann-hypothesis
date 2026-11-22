import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0237
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormsEqZeroOfPeriodSubConjCoboundary
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.Positivity

noncomputable def segPt (τ : ℍ) (t : ℝ) : ℍ :=
  ⟨Complex.I + ((Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) : ℂ) * ((τ : ℂ) - Complex.I), by
    have h0 := (Set.projIcc (0 : ℝ) 1 zero_le_one t).2.1
    have h1 := (Set.projIcc (0 : ℝ) 1 zero_le_one t).2.2
    have h2 := τ.im_pos
    simp only [Complex.add_im, Complex.I_im, Complex.mul_im, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, zero_mul, add_zero, UpperHalfPlane.coe_im]
    rcases h1.eq_or_lt with h | h
    · rw [h]; linarith
    · nlinarith [mul_nonneg h0 h2.le]⟩

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma eichler_mem_degreeLT_succ (w : ℕ) (g : ℍ → ℂ) (τ : ℍ) :
    _root_.GlobalTheory.HeckeFamilyMatrices.eichler w g τ ∈ ℂ[X]_(w + 1) := by
  rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  rw [_root_.GlobalTheory.EichlerChange.coeff_eichler, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma map_conj_mem_degreeLT {n : ℕ} {p : ℂ[X]} (hp : p ∈ ℂ[X]_n) :
    p.map (starRingEnd ℂ) ∈ ℂ[X]_n := by
  rw [Polynomial.mem_degreeLT] at hp ⊢
  rwa [Polynomial.degree_map]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma sl_denom_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
  have h := UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ
  simpa [UpperHalfPlane.denom] using h

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma eval_eq_denom_pow_mul_eval_of_slP_invariant (w : ℕ) (V : ℍ → ℂ[X]) (γ : SL(2, ℤ)) (τ : ℍ)
    (hmem : V (γ • τ) ∈ ℂ[X]_(w + 1))
    (hrel : _root_.GlobalTheory.HeckeFamilyMatrices.slP w (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) (V (γ • τ)) = V τ) :
    eval (τ : ℂ) (V τ) =
      (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ w * eval ((γ • τ : ℍ) : ℂ) (V (γ • τ)) := by
  rw [← hrel, _root_.GlobalTheory.HeckeFamilyMatrices.eval_polySlash w _ _ _ hmem (sl_denom_ne_zero γ τ)]
  congr 2
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [_root_.GlobalTheory.HeckeFamilyMatrices.mat]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma im_sl_smul_eq_im_div_normSq_denom (γ : SL(2, ℤ)) (τ : ℍ) :
    (γ • τ).im = τ.im / Complex.normSq (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) := by
  rw [ModularGroup.sl_moeb, UpperHalfPlane.im_smul_eq_div_normSq]
  simp [UpperHalfPlane.denom]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma continuous_eval_of_continuous_coeff_of_degree_le (w : ℕ) (V : ℍ → ℂ[X])
    (hmem : ∀ τ, V τ ∈ ℂ[X]_(w + 1)) (hc : ∀ n, Continuous fun τ => (V τ).coeff n) :
    Continuous fun τ : ℍ => eval (τ : ℂ) (V τ) := by
  have h : (fun τ : ℍ => eval (τ : ℂ) (V τ)) =
      fun τ => ∑ i ∈ Finset.range (w + 1), (V τ).coeff i * (τ : ℂ) ^ i := by
    funext τ
    apply eval_eq_sum_range'
    by_cases h0 : V τ = 0
    · simp [h0]
    · have := hmem τ
      rw [mem_degreeLT] at this
      exact (natDegree_lt_iff_degree_lt h0).2 this
  rw [h]
  exact continuous_finset_sum _ fun i _ => (hc i).mul (continuous_coe.pow i)

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma exists_norm_eval_le_mul_im_rpow_of_slP_invariant (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (w : ℕ)
    (V : ℍ → ℂ[X]) (hmem : ∀ τ, V τ ∈ ℂ[X]_(w + 1))
    (hc : ∀ n, Continuous fun τ => (V τ).coeff n)
    (hrel : ∀ γ ∈ Γ, ∀ τ, _root_.GlobalTheory.HeckeFamilyMatrices.slP w (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) (V (γ • τ)) = V τ)
    (hdecay : ∀ g : SL(2, ℤ), Filter.Tendsto
      (fun τ => ‖eval ((g • τ : ℍ) : ℂ) (V (g • τ))‖ * (g • τ).im ^ (-(w : ℝ) / 2))
      atImInfty (nhds 0)) :
    ∃ C, ∀ τ : ℍ, ‖eval (τ : ℂ) (V τ)‖ ≤ C * τ.im ^ ((w : ℝ) / 2) := by
  have hinv : ∀ γ ∈ Γ, ∀ τ : ℍ,
      ‖eval ((γ • τ : ℍ) : ℂ) (V (γ • τ))‖ * (γ • τ).im ^ (-(w : ℝ) / 2) =
        ‖eval (τ : ℂ) (V τ)‖ * τ.im ^ (-(w : ℝ) / 2) := by
    intro γ hγ τ
    have he := eval_eq_denom_pow_mul_eval_of_slP_invariant w V γ τ (hmem _) (hrel γ hγ τ)
    have hD := sl_denom_ne_zero γ τ
    set D := ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) with hDdef
    have hDpos : 0 < ‖D‖ := norm_pos_iff.2 hD
    have hx : (‖D‖ ^ (2 : ℕ)) ^ (-(w : ℝ) / 2) = (‖D‖ ^ w)⁻¹ := by
      rw [← Real.rpow_natCast ‖D‖ 2, ← Real.rpow_mul (norm_nonneg _),
        show ((2 : ℕ) : ℝ) * (-(w : ℝ) / 2) = -(w : ℝ) by push_cast; ring,
        Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
    rw [he, im_sl_smul_eq_im_div_normSq_denom, ← hDdef, Real.div_rpow τ.im_pos.le (Complex.normSq_nonneg _),
      Complex.normSq_eq_norm_sq, hx, norm_mul, norm_pow]
    have hw : 0 < ‖D‖ ^ w := pow_pos hDpos w
    field_simp
  obtain ⟨C, hC⟩ := ModularGroup.exists_bound_of_subgroup_invariant_of_isBigO
    (f := fun τ : ℍ => ‖eval (τ : ℂ) (V τ)‖ * τ.im ^ (-(w : ℝ) / 2))
    (((continuous_eval_of_continuous_coeff_of_degree_le w V hmem hc).norm).mul
      (UpperHalfPlane.continuous_im.rpow_const fun τ => Or.inl τ.im_pos.ne'))
    le_rfl (fun g => by simpa using (hdecay g).isBigO_one ℝ) (Γ := Γ) hinv
  refine ⟨C, fun τ => ?_⟩
  have h1 := hC τ
  rw [Real.rpow_zero, mul_one, Real.norm_of_nonneg (by positivity)] at h1
  have hpos : 0 < τ.im ^ ((w : ℝ) / 2) := Real.rpow_pos_of_pos τ.im_pos _
  calc ‖eval (τ : ℂ) (V τ)‖
      = ‖eval (τ : ℂ) (V τ)‖ * τ.im ^ (-(w : ℝ) / 2) * τ.im ^ ((w : ℝ) / 2) := by
        rw [mul_assoc, ← Real.rpow_add τ.im_pos]
        simp [neg_div]
    _ ≤ C * τ.im ^ ((w : ℝ) / 2) := mul_le_mul_of_nonneg_right h1 hpos.le

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
private lemma eq_zero_of_eichler_conj_slash_relation (Γ : Subgroup SL(2, ℤ)) (k : ℕ)
    (hΓ : Γ.FiniteIndex) (hk : 3 ≤ k)
    (f h : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ) k) (p : ℂ[X])
    (hp : p ∈ ℂ[X]_(k - 1))
    (hrel : ∀ (γ : Γ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ)
      (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ) -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ)) - p) =
      _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f τ -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h τ) - p) :
    h = 0 := by
  set V : ℍ → ℂ[X] := fun τ => _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f τ -
    map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h τ) - p with hV
  have hk1 : k - 1 = k - 2 + 1 := by omega
  have hp' : p ∈ ℂ[X]_(k - 2 + 1) := by rw [← hk1]; exact hp
  have hmem : ∀ τ, V τ ∈ ℂ[X]_(k - 2 + 1) := fun τ =>
    sub_mem (sub_mem (eichler_mem_degreeLT_succ _ _ _)
      (map_conj_mem_degreeLT (eichler_mem_degreeLT_succ _ _ _))) hp'
  have hcf : ∀ g : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ) k, ∀ n : ℕ,
      Continuous fun τ => (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) g τ).coeff n := by
    intro g n
    simp_rw [_root_.GlobalTheory.EichlerChange.coeff_eichler]
    refine continuous_const.mul (continuous_iff_continuousAt.2 fun τ => ?_)
    exact ((_root_.GlobalTheory.EichlerChange.hasDerivAt_ecoef (k - 2) g (CuspFormClass.holo g) n τ
      τ.im_pos).continuousAt).comp continuous_coe.continuousAt
  have hc : ∀ n, Continuous fun τ => (V τ).coeff n := by
    intro n
    simp only [hV, coeff_sub, coeff_map]
    exact ((hcf f n).sub (Complex.continuous_conj.comp (hcf h n))).sub continuous_const
  have hrel' : ∀ γ ∈ Γ, ∀ τ,
      _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) (V (γ • τ)) = V τ :=
    fun γ hγ τ => hrel ⟨γ, hγ⟩ τ
  have hdecay := _root_.GlobalTheory.HeckeFamilyMatrices.Decay.decay_at_cusp Γ k hΓ hk f h p hp hrel
  have hw : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  obtain ⟨C, hC⟩ := exists_norm_eval_le_mul_im_rpow_of_slP_invariant Γ (k - 2) V hmem hc hrel'
    (by rw [hw]; exact hdecay)
  obtain ⟨n, hn, -, hTn⟩ :=
    Subgroup.exists_pow_mem_of_index_ne_zero hΓ.index_ne_zero ModularGroup.T
  refine _root_.GlobalTheory.EichlerPositivity.cuspForm_eq_zero_of_periodic_of_bound Γ k hΓ hk f h p n C hn (fun τ => ?_)
    (fun τ => by rw [← hw]; exact hC τ)
  have hT : ModularGroup.T ^ n • τ = (n : ℝ) +ᵥ τ := by
    rw [← zpow_natCast, modular_T_zpow_smul]; simp
  have he := eval_eq_denom_pow_mul_eval_of_slP_invariant (k - 2) V (ModularGroup.T ^ n) τ (hmem _) (hrel' _ hTn τ)
  have h10 : ((ModularGroup.T ^ n) 1 0 : ℤ) = 0 ∧ ((ModularGroup.T ^ n) 1 1 : ℤ) = 1 := by
    rw [← zpow_natCast, ModularGroup.coe_T_zpow]; simp
  rw [h10.1, h10.2] at he
  simp only [Int.cast_zero, zero_mul, zero_add, Int.cast_one, one_pow, one_mul, hT] at he
  exact he.symm

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in

theorem _root_.GlobalTheory.HeckeFamilyMatrices.Positivity.eq_zero_of_per_sub_cj_mem : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N →
    Γ ≤ CongruenceSubgroup.Gamma1 N → Γ.FiniteIndex → 3 ≤ k → ∀ (f h : CuspForm Γ (k : ℤ)),
    _root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑f - _root_.GlobalTheory.HeckeFamilyMatrices.cj (_root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑h) ∈
      _root_.GlobalTheory.HeckeFamilyMatrices.B1 Γ (k - 2) → f = 0 ∧ h = 0 := by
  intro N Γ k _ _ hΓ hk f h hB
  unfold _root_.GlobalTheory.HeckeFamilyMatrices.B1 at hB
  obtain ⟨⟨q, hq⟩, hqe⟩ := hB
  have hcoc : ∀ γ : Γ, _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) q - q =
      _root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑f γ -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑h γ) := fun γ => by
    have := congrFun hqe γ
    simpa [_root_.GlobalTheory.HeckeFamilyMatrices.cj] using this
  have hper : ∀ g : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ) k,
      ∀ (γ : Γ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.per Γ (k - 2) ⇑g γ =
        _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ)
            (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) g (γ • τ)) -
          _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) g τ := fun g =>
    (_root_.GlobalTheory.HeckeFamilyMatrices.PerCoc.per_mem_Z1_and_eq_slP_eichler_sub Γ k (by omega) (CuspForm.toModularFormₗ g)).2
  have hmemE : ∀ (g : ℍ → ℂ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) g τ ∈ ℂ[X]_(k - 2 + 1) :=
    fun g τ => eichler_mem_degreeLT_succ _ _ _
  have hconj : ∀ p ∈ ℂ[X]_(k - 2 + 1), ∀ γ : SL(2, ℤ),
      map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) p) =
        _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) (map (starRingEnd ℂ) p) :=
    fun p hp γ =>
      (_root_.GlobalTheory.HeckeFamilyMatrices.SlPAct.polySlash_act (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ) 1 p hp).2.2.2
  have hcc : ∀ p : ℂ[X], map (starRingEnd ℂ) (map (starRingEnd ℂ) p) = p := fun p => by
    ext n; simp [coeff_map]
  have hk1 : k - 1 = k - 2 + 1 := by omega
  have rel1 : ∀ (γ : Γ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ)
      (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ) -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ)) - q) =
      _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f τ -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h τ) - q := by
    intro γ τ
    have h1 := hcoc γ
    rw [hper f γ τ, hper h γ τ, Polynomial.map_sub, hconj _ (hmemE _ _)] at h1
    rw [map_sub, map_sub]
    linear_combination -h1
  have rel2 : ∀ (γ : Γ) (τ : ℍ), _root_.GlobalTheory.HeckeFamilyMatrices.slP (k - 2) (_root_.GlobalTheory.HeckeFamilyMatrices.mat γ)
      (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ) -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ)) - -map (starRingEnd ℂ) q) =
      _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h τ -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f τ) - -map (starRingEnd ℂ) q := by
    intro γ τ
    have h2 := congrArg (map (starRingEnd ℂ)) (rel1 γ τ)
    rw [hconj _ (sub_mem (sub_mem (hmemE _ _) (map_conj_mem_degreeLT (hmemE _ _))) hq)] at h2
    simp only [Polynomial.map_sub, hcc] at h2
    have hneg : _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ) -
        map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ)) - -map (starRingEnd ℂ) q =
        -(map (starRingEnd ℂ) (_root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) f (γ • τ)) -
          _root_.GlobalTheory.HeckeFamilyMatrices.eichler (k - 2) h (γ • τ) - map (starRingEnd ℂ) q) := by ring
    rw [hneg, map_neg, h2]
    ring
  have hq' : q ∈ ℂ[X]_(k - 1) := by rw [hk1]; exact hq
  exact ⟨eq_zero_of_eichler_conj_slash_relation Γ k hΓ hk h f _
      (neg_mem (map_conj_mem_degreeLT hq')) rel2,
    eq_zero_of_eichler_conj_slash_relation Γ k hΓ hk f h q hq' rel1⟩

end GlobalTheory.HeckeFamilyMatrices.Positivity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjLevelOne
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_conj_level_one : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F : ℍ → ℂ), 0 < N →
    (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → (∃ a, HasQ N F a) →
    ∃ F' : ℍ → ℂ, (∀ γ : SL(2, ℤ), F' ∣[(w : ℤ)] γ = F') ∧ QConj g N F F' := by
  intro g w N F hN hinv ⟨a, ha⟩
  have hmf : IsMF (w : ℤ) F := GlobalTheory.QFam.isMF_of_invariant_of_hasQ N w F a hN hinv ha
  obtain ⟨s, c, hwt, hF⟩ := GlobalTheory.QFam.isMF_eq_sum_monomials w F hmf
  refine ⟨fun τ => ∑ p ∈ s, g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2), ?_, ?_⟩
  ·
    let act : Unit → SL(2, ℤ) → Unit := fun i _ => i
    have hfam : IsFam act (w : ℤ)
        (fun _ τ => ∑ p ∈ s, g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) := by
      refine IsFam.sum_fun s (f := fun p _ τ => g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) ?_
      intro p hp
      have h4 := (isFam_const_E4 Unit act).pow_fun p.1
      have h6 := (isFam_const_E6 Unit act).pow_fun p.2
      have hm := (h4.mul_fun h6).const_mul_fun (g (c p))
      have e : ((p.1 : ℕ) : ℤ) * 4 + ((p.2 : ℕ) : ℤ) * 6 = (w : ℤ) := by
        rw [← hwt p hp]; push_cast; ring
      rw [e] at hm
      exact hm
    intro γ
    exact hfam () γ
  · have hFe : F = fun τ => ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := funext hF
    rw [hFe]
    refine QConj.sum s (f := fun p τ => c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2))
      (f' := fun p τ => g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) ?_
    intro p _
    have h4 : QConj g N ⇑E₄ ⇑E₄ := eis_qConj N hN _ (Or.inl rfl) g
    have h6 : QConj g N ⇑E₆ ⇑E₆ := eis_qConj N hN _ (Or.inr (Or.inl rfl)) g
    exact QConj.mul hN (QConj.const g N (c p))
      (QConj.mul hN (QConj.pow hN p.1 h4) (QConj.pow hN p.2 h6))

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowN
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace GlobalTheory.CycDec

theorem exists_unit_infinite_order (l : ℕ) [Fact l.Prime] :
    ∃ u : ℤ_[l]ˣ, ∀ n : ℤ, n ≠ 0 → u ^ n ≠ 1 := by
  have hl : l.Prime := Fact.out
  have hu : IsUnit (1 + (l : ℤ_[l])) := by
    rw [← sub_neg_eq_add]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ fun h =>
      PadicInt.irreducible_p.not_isUnit ((IsUnit.neg_iff _).1 h)
  obtain ⟨u, hu⟩ := hu
  refine ⟨u, fun n hn h => ?_⟩
  have h1 : u ^ n.natAbs = 1 := by
    rcases Int.natAbs_eq n with e | e
    · rw [← zpow_natCast, ← e, h]
    · rw [e, zpow_neg, inv_eq_one, zpow_natCast] at h
      exact h
  have h2 : (((1 + l) ^ n.natAbs : ℕ) : ℤ_[l]) = ((1 : ℕ) : ℤ_[l]) := by
    push_cast
    rw [← hu, ← Units.val_pow_eq_pow_val, h1, Units.val_one]
  have h3 := Nat.cast_injective h2
  rw [pow_eq_one_iff] at h3
  rcases h3 with h3 | h3
  · exact hl.ne_zero (by omega)
  · exact hn (Int.natAbs_eq_zero.1 h3)

theorem exists_mem_Dec_cycZ_zpow_ne_one : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F))
    (A : ValuationSubring Ω), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → IsPlaceOver A v → ∀ n : ℤ, n ≠ 0 →
    ∃ g : G F Ω, g ∈ Dec (F := F) A ∧ cycZ F Ω l g ^ n ≠ 1 := by
  intro F Ω _ _ _ _ _ l _ v A hl hA n hn
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hv : A.valuation (l : Ω) < 1 := by
    simpa using (hA _).2 hl
  obtain ⟨u, hu⟩ := exists_unit_infinite_order l
  obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hv u
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ F Ω).fieldRange
  have : FiniteDimensional ℚ K :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ F Ω)).toLinearEquiv.finiteDimensional
  have : Finite ((Ω ≃ₐ[ℚ] Ω) ⧸ K.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ K.fixingSubgroup_isOpen
  have : K.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := K.fixingSubgroup)) σ
  let g : G F Ω := { (σ ^ N).toRingEquiv with
    commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _ ⟨x, rfl⟩ }
  have hD : σ ^ N ∈ Dec (F := ℚ) A := (Dec (F := ℚ) A).pow_mem (Ine_le_Dec A hσ) N
  have hc : cycZ F Ω l g = cycZ ℚ Ω l (σ ^ N) := rfl
  refine ⟨g, hD, ?_⟩
  rw [hc, map_pow, hσu, ← zpow_natCast, ← zpow_mul]
  exact hu _ (mul_ne_zero (by exact_mod_cast hN.ne') hn)

end GlobalTheory.CycDec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDeltaPowQExpansionIffLaurentSeries
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem laurent_exp_shift (M : ℕ) (hM : 0 < M) (w : ℕ) (k : ℤ) (τ : ℂ) :
    Complex.exp (2 * Real.pi * Complex.I * τ) ^ w *
      Complex.exp (2 * Real.pi * Complex.I * ((k - (w * M : ℕ) : ℤ) : ℂ) * τ / M) =
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * τ / M) := by
  have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

theorem laurent_qAll_int (E : Subring ℂ) (M : ℕ) (hM : 0 < M) (f : ℍ → ℂ) (c : ℕ → ℤ)
    (h : HasQ 1 f fun n => (c n : ℂ)) : QAll (· ∈ E) M f :=
  QAll.of_dvd hM (one_dvd M) E.zero_mem ⟨_, h, fun n => intCast_mem E (c n)⟩

theorem laurent_iff : ∀ (E : Subring ℂ) (M : ℕ) (φ : ℍ → ℂ), 0 < M → ((∃ w : ℕ, QAll (· ∈ E) M fun τ => DD τ ^ w * φ τ) ↔ ∃ (c : ℤ → ℂ) (n₀ : ℤ), (∀ n, c n ∈ E) ∧ (∀ n < n₀, c n = 0) ∧ ∀ τ : ℍ, HasSum (fun n : ℤ => c n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (φ τ)) := by
  intro E M φ hM
  obtain ⟨⟨cD, -, hD⟩, ⟨cI, -, hI⟩⟩ := GlobalTheory.T.modularDiscriminant_div_q_integer_qExpansions
  obtain ⟨-, -, -, hmul, hpow, -⟩ := GlobalTheory.QFam.QAllSubring.ring_closed E M hM
  have hqD := laurent_qAll_int E M hM _ cD hD
  have hqI := laurent_qAll_int E M hM _ cI hI
  have hDD0 : ∀ τ : ℍ, DD τ ≠ 0 := ReciprocityTheory.ChartRestriction.L1.DD_ne_zero
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨b, hb, hbE⟩ := hmul _ _ (hpow _ w hqI) hw
    let g : ℕ → ℤ := fun k => (k : ℤ) - ((w * M : ℕ) : ℤ)
    have hginj : Function.Injective g := fun a b h => by simpa [g] using h
    let c : ℤ → ℂ := fun n => if -((w * M : ℕ) : ℤ) ≤ n then b (n + ((w * M : ℕ) : ℤ)).toNat else 0
    refine ⟨c, -((w * M : ℕ) : ℤ), fun n => ?_, fun n hn => ?_, fun τ => ?_⟩
    · simp only [c]
      split_ifs
      · exact hbE _
      · exact E.zero_mem
    · simp only [c]
      rw [if_neg (not_le.mpr hn)]
    · rw [← hginj.hasSum_iff]
      · have h1 := (hb τ).mul_left (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)⁻¹
        have hφ : (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)⁻¹ *
            ((Complex.exp (2 * Real.pi * Complex.I * τ) / DD τ) ^ w * (DD τ ^ w * φ τ)) = φ τ := by
          rw [div_pow]
          field_simp [pow_ne_zero w (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ))),
            pow_ne_zero w (hDD0 τ)]
        rw [hφ] at h1
        have key : (fun k : ℕ => (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)⁻¹ *
            (b k * Complex.exp (2 * Real.pi * Complex.I * k * τ / M))) =
            (fun n : ℤ => c n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) ∘ g := by
          funext k
          simp only [Function.comp, g, c]
          rw [if_pos (by omega)]
          have hk : ((k : ℤ) - ((w * M : ℕ) : ℤ) + ((w * M : ℕ) : ℤ)).toNat = k := by omega
          rw [hk]
          have := laurent_exp_shift M hM w k τ
          rw [← Int.cast_natCast k, ← this]
          field_simp [pow_ne_zero w (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ)))]
        rw [key] at h1
        exact h1
      · intro n hn
        have : ¬ (-((w * M : ℕ) : ℤ) ≤ n) := fun h => hn ⟨(n + ((w * M : ℕ) : ℤ)).toNat, by
          simp only [g]; omega⟩
        simp only [c]
        rw [if_neg this, zero_mul]
  · rintro ⟨c, n₀, hcE, hc0, hs⟩
    refine ⟨(-n₀).toNat, ?_⟩
    set w := (-n₀).toNat with hw
    let g : ℕ → ℤ := fun k => (k : ℤ) - ((w * M : ℕ) : ℤ)
    have hginj : Function.Injective g := fun a b h => by simpa [g] using h
    have hwM : (w : ℤ) ≤ ((w * M : ℕ) : ℤ) := by
      have : w ≤ w * M := Nat.le_mul_of_pos_right w hM
      exact_mod_cast this
    have hq : HasQ M (fun τ => Complex.exp (2 * Real.pi * Complex.I * τ) ^ w * φ τ) fun k => c (g k) := by
      intro τ
      have h1 := (hs τ).mul_left (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w)
      rw [← hginj.hasSum_iff] at h1
      · have key : (fun i : ℤ => Complex.exp (2 * Real.pi * Complex.I * τ) ^ w *
            (c i * Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) * τ / M))) ∘ g =
            fun k : ℕ => c (g k) * Complex.exp (2 * Real.pi * Complex.I * k * τ / M) := by
          funext k
          simp only [Function.comp, g]
          rw [mul_left_comm, laurent_exp_shift M hM w k τ]
          push_cast
          rfl
        rw [key] at h1
        exact h1
      · intro n hn
        have : n < n₀ := by
          by_contra hh
          exact hn ⟨(n + ((w * M : ℕ) : ℤ)).toNat, by simp only [g]; omega⟩
        simp [hc0 n this]
    have hqE : QAll (· ∈ E) M fun τ => Complex.exp (2 * Real.pi * Complex.I * τ) ^ w * φ τ :=
      ⟨_, hq, fun k => hcE _⟩
    have h2 := hmul _ _ (hpow _ w hqD) hqE
    have key : (fun τ : ℍ => (DD τ / Complex.exp (2 * Real.pi * Complex.I * τ)) ^ w *
        (Complex.exp (2 * Real.pi * Complex.I * τ) ^ w * φ τ)) = fun τ => DD τ ^ w * φ τ := by
      funext τ
      rw [div_pow]
      field_simp [pow_ne_zero w (Complex.exp_ne_zero (2 * Real.pi * Complex.I * (τ : ℂ)))]
    rw [key] at h2
    exact h2

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegralStatement
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisInvariant_valuation_integers_eq_integral : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∃ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ IsInt p x) ∧ (∀ (g : Gal p Ω) (x : Ω), v (g x) = v x) ∧ 0 < v (p : Ω) ∧ v (p : Ω) < 1 := by
  first | exact @GlobalTheory.K5.exists_valuation_isInt | exact GlobalTheory.K5.exists_valuation_isInt | (intros; apply GlobalTheory.K5.exists_valuation_isInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHolomorphicRootUpperHalfPlaneStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_root_upperHalfPlane : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs → (∀ τ ∈ Hs, ∃ k : ℕ, analyticOrderAt h τ = ((m * k : ℕ) : ℕ∞)) → ∃ r : ℂ → ℂ, DifferentiableOn ℂ r Hs ∧ ∀ z ∈ Hs, r z ^ m = h z := by
  first | exact @GlobalTheory.KZ.H3.uhp_root | exact GlobalTheory.KZ.H3.uhp_root | (intros; apply GlobalTheory.KZ.H3.uhp_root <;> assumption)
end

