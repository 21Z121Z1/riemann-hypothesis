import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashToGLSmul
section
noncomputable section

open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

def wOld (N l : ℕ) (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![(l : ℤ), a; (N : ℤ) * l, (l : ℤ) * b]

def gaOld (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (j : ℕ) : SL(2, ℤ) :=
  ⟨!![1, (j : ℤ) + a; (N : ℤ), (N : ℤ) * j + l * b], by
    rw [Matrix.det_fin_two_of]; linear_combination h⟩

def trOld (k : ℤ) (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (G : ℍ → ℂ) : ℍ → ℂ :=
  G + ∑ j ∈ Finset.range l, G ∣[k] gaOld N l a b h j

def ChiInv (k : ℤ) (N M : ℕ) (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → G ∣[k] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • G

def CuspAll (k : ℤ) (G : ℍ → ℂ) : Prop :=
  MDiff G ∧ ∀ c : OnePoint ℝ, IsCusp c 𝒮ℒ → c.IsZeroAt G k

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices

lemma toGL_val (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) :
    ((toGL g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (Int.castRingHom ℝ).mapMatrix g := by
  unfold toGL
  rw [dif_neg hg]
  rfl

lemma toGL_det (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) :
    ((toGL g).det : ℝ) = (g.det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, toGL_val g hg, ← RingHom.map_det]
  simp

lemma toGL_mul (g h : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) (hh : h.det ≠ 0) :
    toGL (g * h) = toGL g * toGL h := by
  have hgh : (g * h).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero hg hh
  apply Units.ext
  rw [Units.val_mul, toGL_val _ hgh, toGL_val _ hg, toGL_val _ hh]
  exact map_mul (Int.castRingHom ℝ).mapMatrix g h

lemma slash_SL_eq (k : ℤ) (γ : SL(2, ℤ)) (G : ℍ → ℂ) : G ∣[k] γ = G ∣[k] toGL (mat γ) := by
  rw [ModularForm.SL_slash]
  congr 1
  apply Units.ext
  rw [toGL_val _ (by simp [mat])]
  ext i j
  simp [mat]

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices

lemma sigma_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (z : ℂ) : σ g z = z := by
  rw [σ, if_pos hg]
  rfl

lemma slash_scalar (k : ℤ) (c : ℝ) (hc : 0 < c) (G : ℍ → ℂ) :
    G ∣[k] (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc.ne')) = ((c : ℂ) ^ (k - 2)) • G := by
  ext τ
  have hdet : (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc.ne')).det.val = c ^ 2 := by
    simp [Matrix.GeneralLinearGroup.det_scalar]
  have hpos : 0 < (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc.ne')).det.val := by
    rw [hdet]; positivity
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [ModularForm.slash_apply, sigma_pos hpos, hdet, abs_of_pos (by positivity),
    UpperHalfPlane.glScalar_smul, UpperHalfPlane.denom_scalar]
  simp only [Units.val_mk0, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [← zpow_natCast, ← zpow_mul]
  have he : (c : ℂ) ^ (k - 2) = (c : ℂ) ^ (((2 : ℕ) : ℤ) * (k - 1)) * (c : ℂ) ^ (-k) := by
    rw [← zpow_add₀ hc']
    congr 1
    push_cast
    ring
  rw [he]
  ring

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices

lemma toGL_det_pos (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : 0 < g.det) : 0 < (toGL g).det.val := by
  rw [toGL_det g hg.ne']
  exact_mod_cast hg

lemma smul_slash_toGL (k : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : 0 < M.det) (c : ℂ) (G : ℍ → ℂ) :
    (c • G) ∣[k] toGL M = c • (G ∣[k] toGL M) := by
  rw [ModularForm.smul_slash, sigma_pos (toGL_det_pos M hM)]

lemma toGL_smul (c : ℕ) (hc : 0 < c) (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : g.det ≠ 0) :
    toGL ((c : ℤ) • g) = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (c : ℝ) (by positivity)) * toGL g := by
  have h1 : ((c : ℤ) • g).det ≠ 0 := by
    rw [Matrix.det_smul]
    simp [hg, hc.ne']
  apply Units.ext
  rw [Units.val_mul, toGL_val _ h1, toGL_val _ hg, Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_mul,
    Units.val_mk0, Matrix.smul_apply, smul_eq_mul]
  simp

lemma slash_toGL_smul (k : ℤ) (c : ℕ) (hc : 0 < c) (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : 0 < g.det)
    (G : ℍ → ℂ) : G ∣[k] toGL ((c : ℤ) • g) = ((c : ℂ) ^ (k - 2)) • (G ∣[k] toGL g) := by
  rw [toGL_smul c hc g hg.ne', SlashAction.slash_mul, slash_scalar k (c : ℝ) (by positivity),
    smul_slash_toGL k g hg, Complex.ofReal_natCast]

lemma ulFam_det (l : ℕ) (hl : 0 < l) (j : Fin l) : 0 < (ulFam l j).det := by
  simp [ulFam, Matrix.det_fin_two_of]
  exact_mod_cast hl

lemma ulF_add (k : ℤ) (l : ℕ) (F G : ℍ → ℂ) : UlF k l (F + G) = UlF k l F + UlF k l G := by
  simp only [UlF, hkF, SlashAction.add_slash, Finset.sum_add_distrib]

lemma ulF_smul (k : ℤ) (l : ℕ) (hl : 0 < l) (c : ℂ) (F : ℍ → ℂ) : UlF k l (c • F) = c • UlF k l F := by
  simp only [UlF, hkF, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => smul_slash_toGL k _ (ulFam_det l hl j) c F

lemma ulF_sub (k : ℤ) (l : ℕ) (hl : 0 < l) (F G : ℍ → ℂ) : UlF k l (F - G) = UlF k l F - UlF k l G := by
  have h := ulF_smul k l hl (-1) G
  rw [sub_eq_add_neg, ulF_add, sub_eq_add_neg]
  congr 1
  simpa using h

end GlobalTheory.HeckeFamilyMatrices

namespace GlobalTheory.HeckeFamilyMatrices
open CongruenceSubgroup

lemma chiInv_add {k : ℤ} {N M : ℕ} {χ : DirichletCharacter ℂ N} {F G : ℍ → ℂ} (hF : ChiInv k N M χ F)
    (hG : ChiInv k N M χ G) : ChiInv k N M χ (F + G) := by
  intro γ hγ
  rw [SlashAction.add_slash, hF γ hγ, hG γ hγ, smul_add]

lemma chiInv_smul {k : ℤ} {N M : ℕ} {χ : DirichletCharacter ℂ N} {F : ℍ → ℂ} (c : ℂ) (hF : ChiInv k N M χ F) :
    ChiInv k N M χ (c • F) := by
  intro γ hγ
  rw [ModularForm.SL_smul_slash, hF γ hγ, smul_comm]

lemma cuspAll_add {k : ℤ} {F G : ℍ → ℂ} (hF : CuspAll k F) (hG : CuspAll k G) : CuspAll k (F + G) := ⟨hF.1.add hG.1, fun c hc => (hF.2 c hc).add (hG.2 c hc)⟩

lemma cuspAll_smul {k : ℤ} {F : ℍ → ℂ} (c : ℂ) (hF : CuspAll k F) : CuspAll k (c • F) := by
  refine ⟨hF.1.const_smul c, fun p hp g hg => ?_⟩
  rw [ModularForm.smul_slash]
  exact Filter.ZeroAtFilter.smul _ (hF.2 p hp g hg)

end GlobalTheory.HeckeFamilyMatrices
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StripEvalPolynomialDecayMulImRpow
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

open Filter Topology

private lemma norm_eval_add_C_le_of_coeff_le (w : ℕ) (a z : ℂ) (p : ℂ[X]) (K e : ℝ) (hK : 0 ≤ K)
    (he : 0 ≤ e) (hp : p ∈ degreeLT ℂ (w + 1))
    (hc : ∀ j ≤ w, ‖p.coeff j‖ ≤ K * e * (1 + ‖z‖) ^ w) :
    ‖(p + C a).eval z‖ ≤ ‖a‖ + (w + 1) * (K * e * (1 + ‖z‖) ^ (2 * w)) := by
  have hdeg : p.natDegree < w + 1 := by
    by_cases h0 : p = 0
    · simp [h0]
    · exact (natDegree_lt_iff_degree_lt h0).2 (mem_degreeLT.1 hp)
  rw [eval_add, eval_C, eval_eq_sum_range' hdeg]
  have hz1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hterm : ∀ j ∈ Finset.range (w + 1),
      ‖p.coeff j * z ^ j‖ ≤ K * e * (1 + ‖z‖) ^ (2 * w) := by
    intro j hj
    have hjw : j ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [norm_mul, norm_pow]
    have h1 : ‖z‖ ^ j ≤ (1 + ‖z‖) ^ w :=
      (pow_le_pow_left₀ (norm_nonneg z) (by linarith) j).trans (pow_le_pow_right₀ hz1 hjw)
    calc ‖p.coeff j‖ * ‖z‖ ^ j ≤ (K * e * (1 + ‖z‖) ^ w) * (1 + ‖z‖) ^ w :=
          mul_le_mul (hc j hjw) h1 (by positivity) (by positivity)
      _ = K * e * (1 + ‖z‖) ^ (2 * w) := by ring
  calc ‖∑ j ∈ Finset.range (w + 1), p.coeff j * z ^ j + a‖
      ≤ ‖∑ j ∈ Finset.range (w + 1), p.coeff j * z ^ j‖ + ‖a‖ := norm_add_le _ _
    _ ≤ ∑ j ∈ Finset.range (w + 1), ‖p.coeff j * z ^ j‖ + ‖a‖ := by
        gcongr; exact norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (w + 1), K * e * (1 + ‖z‖) ^ (2 * w) + ‖a‖ := by
        gcongr with j hj; exact hterm j hj
    _ = ‖a‖ + (w + 1) * (K * e * (1 + ‖z‖) ^ (2 * w)) := by simp; ring

theorem strip_eval_decay : ∀ (w n : ℕ) (a : ℂ) (V : ℍ → ℂ[X]) (C' c : ℝ), 1 ≤ w → 0 < c →
    (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) →
    (∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - C a).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w) →
    ∀ ε > 0, ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → 0 ≤ τ.re → τ.re ≤ n →
      ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) < ε := by
  intro w n a V C' c hw hc hV hcoef ε hε
  set K := max C' 0 with hKdef
  have hK : 0 ≤ K := le_max_right _ _
  have hwpos : (0 : ℝ) < (w : ℝ) / 2 := by
    have : (1 : ℝ) ≤ w := by exact_mod_cast hw
    linarith
  have h1 : Tendsto (fun y : ℝ => ‖a‖ * y ^ (-(w : ℝ) / 2)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop hwpos).const_mul ‖a‖
    rw [mul_zero] at this
    refine this.congr' (Eventually.of_forall fun y => ?_)
    simp only [neg_div]
  have h2 : Tendsto (fun y : ℝ => (w + 1) * (K * 4 ^ w) * (y ^ (2 * w) / Real.exp (c * y)))
      atTop (𝓝 0) := by
    have := ((isLittleO_pow_exp_pos_mul_atTop (2 * w) hc).tendsto_div_nhds_zero).const_mul
      ((w + 1) * (K * 4 ^ w))
    rwa [mul_zero] at this
  have e1 := h1.eventually (gt_mem_nhds (half_pos hε))
  have e2 := h2.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨A0, hA0⟩ := eventually_atTop.1 (e1.and e2)
  refine ⟨max A0 (1 + n), fun τ hA hre hren => ?_⟩
  have hpos : 0 < τ.im := τ.im_pos
  have hy0 : A0 ≤ τ.im := le_trans (le_max_left _ _) hA
  have hyn : 1 + (n : ℝ) ≤ τ.im := le_trans (le_max_right _ _) hA
  have hy1 : 1 ≤ τ.im := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨hf1, hf2⟩ := hA0 τ.im hy0
  have hz : ‖(τ : ℂ)‖ ≤ n + τ.im := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hr : |(τ : ℂ).re| ≤ n := by
      rw [UpperHalfPlane.coe_re, abs_of_nonneg hre]; exact hren
    have hi : |(τ : ℂ).im| = τ.im := by
      rw [UpperHalfPlane.coe_im, abs_of_pos hpos]
    linarith
  have hcb : ∀ j ≤ w, ‖(V τ - C a).coeff j‖ ≤ K * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by
    intro j hj
    refine (hcoef τ hy1 j hj).trans ?_
    gcongr
    exact le_max_left _ _
  have hmem : V τ - C a ∈ degreeLT ℂ (w + 1) :=
    Submodule.sub_mem _ (hV τ)
      (mem_degreeLT.2 (lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.succ_pos w)))
  have hmain := norm_eval_add_C_le_of_coeff_le w a (τ : ℂ) (V τ - C a) K (Real.exp (-c * τ.im)) hK
    (Real.exp_pos _).le hmem hcb
  rw [sub_add_cancel] at hmain
  have hnz : 1 + ‖(τ : ℂ)‖ ≤ 2 * τ.im := by linarith
  have hpow : (1 + ‖(τ : ℂ)‖) ^ (2 * w) ≤ 4 ^ w * τ.im ^ (2 * w) := by
    calc (1 + ‖(τ : ℂ)‖) ^ (2 * w) ≤ (2 * τ.im) ^ (2 * w) :=
          pow_le_pow_left₀ (by positivity) hnz _
      _ = 4 ^ w * τ.im ^ (2 * w) := by rw [mul_pow, pow_mul]; norm_num
  have hT : (w + 1) * (K * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ (2 * w))
      ≤ (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by
    rw [neg_mul, Real.exp_neg]
    calc (w + 1) * (K * (Real.exp (c * τ.im))⁻¹ * (1 + ‖(τ : ℂ)‖) ^ (2 * w))
        ≤ (w + 1) * (K * (Real.exp (c * τ.im))⁻¹ * (4 ^ w * τ.im ^ (2 * w))) := by gcongr
      _ = (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by
        rw [div_eq_mul_inv]; ring
  have hT0 : 0 ≤ (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by positivity
  have hr0 : 0 ≤ τ.im ^ (-(w : ℝ) / 2) := Real.rpow_nonneg hpos.le _
  have hr1 : τ.im ^ (-(w : ℝ) / 2) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hy1 ?_
    have : (0 : ℝ) ≤ w := Nat.cast_nonneg w
    linarith
  calc ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2)
      ≤ (‖a‖ + (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)))
          * τ.im ^ (-(w : ℝ) / 2) := by gcongr; linarith
    _ = ‖a‖ * τ.im ^ (-(w : ℝ) / 2)
          + (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im))
            * τ.im ^ (-(w : ℝ) / 2) := by ring
    _ ≤ ‖a‖ * τ.im ^ (-(w : ℝ) / 2)
          + (w + 1) * (K * 4 ^ w) * (τ.im ^ (2 * w) / Real.exp (c * τ.im)) := by
        exact add_le_add le_rfl (mul_le_of_le_one_right hT0 hr1)
    _ < ε / 2 + ε / 2 := add_lt_add hf1 hf2
    _ = ε := add_halves ε

end GlobalTheory.HeckeFamilyMatrices
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumEqZeroAddUnits
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.NormFormGauss

theorem card_eq_sq {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ x, s (s x) = x)
    (r : k) (hr : s r - r ≠ 0) :
    Fintype.card k = (Finset.univ.filter (fun x : k => s x = x)).card ^ 2 := by
  let T : k →+ k := s.toAddMonoidHom - AddMonoidHom.id k
  have hT : ∀ x, T x = s x - x := fun x => rfl
  have h1 : Nat.card k = Nat.card (k ⧸ T.ker) * Nat.card T.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have h2 : Nat.card (k ⧸ T.ker) = Nat.card T.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange T).toEquiv
  have h3 : Nat.card T.ker = (Finset.univ.filter (fun x : k => s x = x)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [AddMonoidHom.mem_ker, hT, sub_eq_zero]
  have hθ : s (s r - r) = -(s r - r) := by rw [map_sub, hs]; ring
  have h4 : Nat.card T.range = Nat.card T.ker := by
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun u : T.ker => (⟨(s r - r) * u, ⟨r * u, ?_⟩⟩ : T.range)) ⟨?_, ?_⟩)
    · have hu : s u = u := by
        have := u.2
        rw [AddMonoidHom.mem_ker, hT, sub_eq_zero] at this
        exact this
      rw [hT, map_mul, hu]; ring
    · intro u v huv
      have := congrArg Subtype.val huv
      exact Subtype.ext (mul_left_cancel₀ hr this)
    · rintro ⟨_, t, rfl⟩
      refine ⟨⟨(s t - t) / (s r - r), ?_⟩, ?_⟩
      · rw [AddMonoidHom.mem_ker, hT, sub_eq_zero, map_div₀, hθ, map_sub, hs]
        field_simp
        ring
      · apply Subtype.ext
        simp only [hT]
        field_simp
  rw [← Nat.card_eq_fintype_card, h1, h2, h4, h3, sq]

theorem sum_norm_units {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ x, s (s x) = x)
    (r : k) (hr : s r - r ≠ 0) :
    ∃ m : ℕ, Fintype.card kˣ = m * (Finset.univ.filter (fun x : kˣ => s x = x)).card ∧
      ∀ f : k → ℂ, ∑ x : kˣ, f (x * s x) =
        m * ∑ y ∈ Finset.univ.filter (fun x : kˣ => s x = x), f y := by
  let S : kˣ →* kˣ := Units.map s.toMonoidHom
  have hS : ∀ x : kˣ, ((S x : kˣ) : k) = s x := fun x => rfl
  let N : kˣ →* kˣ := MonoidHom.id _ * S
  let D : kˣ →* kˣ := MonoidHom.id _ / S
  have hN : ∀ x : kˣ, ((N x : kˣ) : k) = x * s x := fun x => rfl
  have hD : ∀ x : kˣ, ((D x : kˣ) : k) = x / s x := fun x => by
    simp [D, hS]
  have hθ : s (s r - r) = -(s r - r) := by rw [map_sub, hs]; ring
  have hne : ∀ x : kˣ, s x ≠ 0 := fun x => by simp
  have hDk : ∀ x : kˣ, x ∈ D.ker ↔ s x = x := fun x => by
    rw [MonoidHom.mem_ker, Units.ext_iff, hD, Units.val_one, div_eq_one_iff_eq (hne x), eq_comm]
  have hker : N.ker = D.range := by
    ext x
    rw [MonoidHom.mem_ker, Units.ext_iff, hN, Units.val_one]
    constructor
    · intro hx
      by_cases h : (1 + x : k) = 0
      · refine ⟨Units.mk0 _ hr, Units.ext ?_⟩
        rw [hD, Units.val_mk0, hθ, div_neg, div_self hr]
        linear_combination -h
      · refine ⟨Units.mk0 _ h, Units.ext ?_⟩
        have h' := hne (Units.mk0 _ h)
        rw [hD, div_eq_iff h', Units.val_mk0, map_add, map_one]
        linear_combination -hx
    · rintro ⟨y, rfl⟩
      rw [hD, map_div₀, hs]
      have := hne y
      have := y.ne_zero
      field_simp
  have c1 : Nat.card kˣ = Nat.card N.range * Nat.card N.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange N).toEquiv]
  have c2 : Nat.card kˣ = Nat.card D.range * Nat.card D.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup D.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange D).toEquiv]
  have c3 : Nat.card N.range = Nat.card D.ker := by
    rw [← hker, c1, mul_comm] at c2
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos c2
  have hle : N.range ≤ D.ker := by
    rintro _ ⟨x, rfl⟩
    rw [hDk, hN, map_mul, hs, mul_comm]
  have hr' : N.range = D.ker := Subgroup.eq_of_le_of_card_ge hle c3.ge
  have c4 : Nat.card D.ker = (Finset.univ.filter (fun x : kˣ => s x = x)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp only [Finset.mem_filter, hDk]
  refine ⟨Nat.card N.ker, ?_, fun f => ?_⟩
  · rw [← Nat.card_eq_fintype_card, c1, c3, c4, mul_comm]
  · have himg : Finset.univ.image N = Finset.univ.filter (fun x : kˣ => s x = x) := by
      ext x
      simp only [Finset.mem_filter, ← hDk, ← hr', Finset.mem_image, Finset.mem_univ, true_and]
      rfl
    have := Finset.sum_comp (s := Finset.univ) (fun y : kˣ => f y) N
    simp only [hN] at this
    rw [this, ← himg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [nsmul_eq_mul]
    congr 2
    have hy' : y ∈ Set.range N := by simpa using hy
    rw [MonoidHom.card_fiber_eq_of_mem_range N hy' (⟨1, map_one N⟩ : (1 : kˣ) ∈ Set.range N),
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [MonoidHom.mem_ker]

theorem sum_eq_zero_add_units {k : Type} [Field k] [Fintype k] {M : Type} [AddCommMonoid M]
    (g : k → M) : ∑ x : k, g x = g 0 + ∑ x : kˣ, g x := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k))]
  congr 1
  symm
  refine Finset.sum_bij (fun x _ => (x : k)) ?_ ?_ ?_ ?_
  · intro a _; simp
  · intro a _ b _ h; exact Units.ext h
  · intro b hb
    exact ⟨Units.mk0 b (by simpa using hb), by simp, rfl⟩
  · intro a _; rfl

theorem gauss_field {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ x, s (s x) = x)
    (r : k) (hr : s r - r ≠ 0) (f : k → ℂ) (hadd : ∀ a b, f (a + b) = f a * f b) (h0 : f 0 = 1)
    (u : k) (hu : s u = u) (hfu : f u ≠ 1) :
    ∑ x : k, f (x * s x) = -(Real.sqrt (Fintype.card k) : ℂ) := by
  obtain ⟨m, hm, hsum⟩ := sum_norm_units s hs r hr
  have hq := card_eq_sq s hs r hr
  set q := (Finset.univ.filter (fun x : k => s x = x)).card with hqdef
  set a := (Finset.univ.filter (fun x : kˣ => s x = x)).card with hadef
  have hqa : q = 1 + a := by
    have := sum_eq_zero_add_units (fun x : k => if s x = x then (1 : ℕ) else 0)
    rw [hqdef, hadef, Finset.card_filter, Finset.card_filter, this, if_pos (map_zero s)]
  have ha : 0 < a := Finset.card_pos.2 ⟨1, by simp⟩
  have hcard : Fintype.card k = 1 + Fintype.card kˣ := by
    have := sum_eq_zero_add_units (fun _ : k => (1 : ℕ))
    simpa using this
  have hmq : m = q + 1 := by
    apply Nat.eq_of_mul_eq_mul_right ha
    rw [hm, hq, hqa] at hcard
    rw [hqa]
    nlinarith
  have hz : ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f y = 0 := by
    have h1 : ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f (u + y) =
        ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f y := by
      refine Finset.sum_equiv (Equiv.addLeft u) ?_ ?_
      · intro i; simp [hu]
      · intro i _; rfl
    simp only [hadd, ← Finset.mul_sum] at h1
    have h2 : (f u - 1) * ∑ y ∈ Finset.univ.filter (fun x : k => s x = x), f y = 0 := by
      linear_combination h1
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hfu)
  have hu1 : ∑ y ∈ Finset.univ.filter (fun x : kˣ => s x = x), f y = -1 := by
    have := sum_eq_zero_add_units (fun x : k => if s x = x then f x else 0)
    rw [← Finset.sum_filter, hz, ← Finset.sum_filter] at this
    simp only [map_zero, if_true, h0] at this
    linear_combination -this
  rw [sum_eq_zero_add_units, hsum, hu1, hq, hmq]
  push_cast
  rw [Real.sqrt_sq (Nat.cast_nonneg q)]
  simp [h0]

theorem gauss_quotient : ∀ {R : Type} [CommRing R] (σ : R →+* R) (w : R), (∀ r, σ (σ r) = r) → w + σ w = 1 → ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) → (∀ r ∈ P, σ r ∈ P) → (∃ r, σ r - r ∉ P) → ∀ χ : R → ℂ, (∀ s t, χ (s + t) = χ s * χ t) → χ 0 = 1 → (∀ r ∈ P, χ r = 1) → (∀ t, χ (σ t) = χ t) → (∃ t, χ t ≠ 1) → (∑ᶠ q : R ⧸ P, χ (w * (Quotient.out q : R) * σ (Quotient.out q : R))) = -(Real.sqrt (Nat.card (R ⧸ P)) : ℂ) := by
  intro R _ σ w hσ hw P hP hfin hst ⟨r, hr⟩ χ hadd h0 hχP hχσ ⟨t, ht⟩
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (R ⧸ P) := Fintype.ofFinite _
  let s : R ⧸ P →+* R ⧸ P := Ideal.quotientMap P σ (fun r hr => hst r hr)
  have hs : ∀ x, s (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (σ x) := fun x => rfl
  have hout : ∀ q : R ⧸ P, Ideal.Quotient.mk P (Quotient.out q) = q := fun q => Quotient.out_eq q
  have hcongr : ∀ a b : R, Ideal.Quotient.mk P a = Ideal.Quotient.mk P b → χ a = χ b := by
    intro a b h
    have h1 := hχP _ (Ideal.Quotient.eq.1 h)
    have h2 := hadd (a - b) b
    rw [h1, one_mul, sub_add_cancel] at h2
    exact h2
  let f : R ⧸ P → ℂ := fun q => χ (w * Quotient.out q)
  have hf : ∀ a : R, f (Ideal.Quotient.mk P a) = χ (w * a) := fun a =>
    hcongr _ _ (by rw [map_mul, map_mul, hout])
  have key := gauss_field s
    (fun x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [hs, hs, hσ])
    (Ideal.Quotient.mk P r)
    (by
      rw [hs, ← map_sub]
      exact fun h => hr (Ideal.Quotient.eq_zero_iff_mem.1 h))
    f
    (fun a b => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [← map_add, hf, hf, hf, mul_add, hadd])
    (by rw [← map_zero (Ideal.Quotient.mk P), hf, mul_zero, h0])
    (Ideal.Quotient.mk P (t + σ t))
    (by rw [hs, map_add σ, hσ, add_comm])
    (by
      rw [hf, mul_add, hadd, ← hχσ (w * σ t), map_mul, hσ, ← hadd, ← add_mul, hw, one_mul]
      exact ht)
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, ← key]
  refine Finset.sum_congr rfl fun q _ => ?_
  conv_rhs => rw [← hout q]
  rw [hs, ← map_mul, hf, mul_assoc]

end GlobalTheory.NormFormGauss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableRpowOfFibreCardLeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_rpow_of_fibre_card_le' : ∀ (ι : Type) (n : ℕ) (b C t : ℝ) (k : ι → Fin n → ℕ) (h : ι → ℝ), 1 < b → (n : ℝ) < t → (∀ q, 0 ≤ h q ∧ h q ≤ C * ∏ i, (b ^ k q i)⁻¹) → (∀ (m : Fin n → ℕ) (T : Finset ι), (∀ q ∈ T, k q = m) → (T.card : ℝ) ≤ C * ∏ i, b ^ (n * m i)) → Summable fun q => h q ^ t := by
  first | exact @GlobalTheory.SummCount.summable_rpow_of_fibre_card_le | exact GlobalTheory.SummCount.summable_rpow_of_fibre_card_le | (intros; apply GlobalTheory.SummCount.summable_rpow_of_fibre_card_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TensorProductNondegeneratePairingStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_product_nondegenerate_pairing : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M N : ι → Type) [∀ τ, AddCommGroup (M τ)] [∀ τ, Module ℂ (M τ)] [∀ τ, AddCommGroup (N τ)] [∀ τ, Module ℂ (N τ)] [∀ τ, FiniteDimensional ℂ (N τ)] (b : ∀ τ, M τ →ₗ[ℂ] N τ →ₗ[ℂ] ℂ), (∀ τ u, u ≠ 0 → ∃ v, b τ v u ≠ 0) → ∃ B : MultilinearMap ℂ M (Module.Dual ℂ (PiTensorProduct ℂ N)), (∀ v x, B v (PiTensorProduct.tprod ℂ x) = ∏ τ, b τ (v τ) (x τ)) ∧ ∀ u, u ≠ 0 → ∃ v, B v u ≠ 0 := by
  first | exact @GlobalTheory.tensor_pairing_separating | exact GlobalTheory.tensor_pairing_separating | (intros; apply GlobalTheory.tensor_pairing_separating <;> assumption)
end

