import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0023
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0111
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PerpSetBaseChange
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

namespace GlobalTheory.PerpBaseChange

private theorem dual_span_sum_eq_zero {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (S : Set (Module.Dual E (Fin n → E))) (u : Fin n → A)
    (hu : ∀ φ ∈ S, ∑ j, ι (φ (Pi.single j 1)) * u j = 0) :
    ∀ ψ ∈ Submodule.span E S, ∑ j, ι (ψ (Pi.single j 1)) * u j = 0 := by
  intro ψ hψ
  induction hψ using Submodule.span_induction with
  | mem x hx => exact hu x hx
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [LinearMap.add_apply, map_add, add_mul, Finset.sum_add_distrib, hx, hy, add_zero]
  | smul c x _ hx =>
    simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, mul_assoc]
    rw [← Finset.mul_sum, hx, mul_zero]

theorem mem_span_of_forms {E A : Type} [Field E] [CommRing A] (ι : E →+* A) {n : ℕ}
    (S : Set (Module.Dual E (Fin n → E))) (u : Fin n → A)
    (hu : ∀ φ ∈ S, ∑ j, ι (φ (Pi.single j 1)) * u j = 0) :
    u ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' {y | ∀ φ ∈ S, φ y = 0}) := by
  classical

  set D : Submodule E (Module.Dual E (Fin n → E)) := Submodule.span E S with hD
  set K : Submodule E (Fin n → E) := D.dualCoannihilator with hK
  have hKset : ∀ y, y ∈ K ↔ ∀ φ ∈ S, φ y = 0 := by
    intro y
    rw [hK, Submodule.mem_dualCoannihilator]
    constructor
    · intro h φ hφ
      exact h φ (Submodule.subset_span hφ)
    · intro h φ hφ
      induction hφ using Submodule.span_induction with
      | mem x hx => exact h x hx
      | zero => simp
      | add x z _ _ hx hz => simp [hx, hz]
      | smul c x _ hx => simp [hx]

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective K.subtype K.ker_subtype
  set P : (Fin n → E) →ₗ[E] (Fin n → E) := K.subtype ∘ₗ g with hP
  have hPK : ∀ y, P y ∈ K := fun y => (g y).2
  have hPid : ∀ k ∈ K, P k = k := by
    intro k hk
    have h1 := LinearMap.congr_fun hg ⟨k, hk⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at h1
    simp [hP, h1]

  have hrow : ∀ i, (LinearMap.proj i - LinearMap.proj i ∘ₗ P : Module.Dual E (Fin n → E)) ∈ D := by
    intro i
    have hmem : (LinearMap.proj i - LinearMap.proj i ∘ₗ P : Module.Dual E (Fin n → E)) ∈
        K.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro k hk
      simp [hPid k hk]
    rwa [hK, Subspace.dualCoannihilator_dualAnnihilator_eq] at hmem
  have hcoord : ∀ i, u i = ∑ j, ι (P (Pi.single j 1) i) * u j := by
    intro i
    have h0 := dual_span_sum_eq_zero ι S u hu _ (hrow i)
    simp only [LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.comp_apply, map_sub, sub_mul,
      Finset.sum_sub_distrib, sub_eq_zero] at h0
    rw [← h0]
    simp [Pi.single_apply]
  have hu' : u = ∑ j, u j • (fun i => ι (P (Pi.single j 1) i)) := by
    funext i
    rw [hcoord i]
    simp [Finset.sum_apply, mul_comm]
  rw [hu']
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨P (Pi.single j 1), ?_, rfl⟩)
  exact (hKset _).1 (hPK _)

def formRight {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (w : Fin n → E) : Module.Dual E (Fin n → E) where
  toFun y := Formalism.UG.hform σ J w y
  map_add' y z := by simp [Formalism.UG.hform, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem formRight_apply {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (w y : Fin n → E) : formRight σ J w y = Formalism.UG.hform σ J w y := rfl

private theorem hform_add_right_flag_measures {A : Type} [CommRing A] (s : A →+* A) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) A) (x y z : Fin n → A) :
    Formalism.UG.hform s J x (y + z) = Formalism.UG.hform s J x y + Formalism.UG.hform s J x z := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem hform_smul_right_flag_measures {A : Type} [CommRing A] (s : A →+* A) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) A) (c : A) (x y : Fin n → A) :
    Formalism.UG.hform s J x (c • y) = c * Formalism.UG.hform s J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem hform_add_left_flag_measures' {A : Type} [CommRing A] (s : A →+* A) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) A) (x x' y : Fin n → A) :
    Formalism.UG.hform s J (x + x') y = Formalism.UG.hform s J x y + Formalism.UG.hform s J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

private theorem hform_smul_left_flag_measures {A : Type} [CommRing A] (s : A →+* A) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) A) (c : A) (x y : Fin n → A) :
    Formalism.UG.hform s J (c • x) y = s c * Formalism.UG.hform s J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem perpSet_baseChange : ∀ (E A : Type) [Field E] [CommRing A] (σ : E →+* E) (s : A →+* A) (ι : E →+* A) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (W : Submodule E (Fin n → E)), (∀ e, s (ι e) = ι (σ e)) → perpSet s (J.map ι) (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set (Fin n → E)))) = (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' perpSet σ J W) : Set (Fin n → A)) := by
  intro E A _ _ σ s ι n J W hs
  classical

  have key : ∀ w z : Fin n → E, Formalism.UG.hform s (J.map ι) (fun i => ι (w i)) (fun i => ι (z i)) =
      ι (Formalism.UG.hform σ J w z) := by
    intro w z
    simp only [Formalism.UG.hform, Matrix.map_apply, hs, map_sum, map_mul]

  have pair : ∀ (w : Fin n → E) (y : Fin n → A), Formalism.UG.hform s (J.map ι) (fun i => ι (w i)) y =
      ∑ j, ι (formRight σ J w (Pi.single j 1)) * y j := by
    intro w y
    simp only [formRight_apply, Formalism.UG.hform, Matrix.map_apply, hs, Pi.single_apply, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sum, map_mul,
      Finset.sum_mul]
    rw [Finset.sum_comm]
  have hset : {z : Fin n → E | ∀ φ ∈ formRight σ J '' (W : Set (Fin n → E)), φ z = 0} = perpSet σ J W := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, perpSet, formRight_apply, SetLike.mem_coe]
  ext y
  constructor
  · intro hy
    rw [SetLike.mem_coe, ← hset]
    apply mem_span_of_forms ι _ y
    rintro φ ⟨w, hw, rfl⟩
    rw [← pair]
    exact hy _ (Submodule.subset_span ⟨w, hw, rfl⟩)
  · intro hy
    rw [SetLike.mem_coe] at hy
    have hgen : ∀ w ∈ W, Formalism.UG.hform s (J.map ι) (fun i => ι (w i)) y = 0 := by
      intro w hw
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨z, hz, rfl⟩ := hx
        rw [key, hz w hw, map_zero]
      | zero => simp [Formalism.UG.hform]
      | add x x' _ _ hx hx' => rw [hform_add_right_flag_measures, hx, hx', add_zero]
      | smul c x _ hx => rw [hform_smul_right_flag_measures, hx, mul_zero]
    simp only [perpSet, Set.mem_setOf_eq]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact hgen w hw
    | zero => simp [Formalism.UG.hform]
    | add x x' _ _ hx hx' => rw [hform_add_left_flag_measures', hx, hx', add_zero]
    | smul c x _ hx => rw [hform_smul_left_flag_measures, hx, mul_zero]

end GlobalTheory.PerpBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLeadMinorDecay
section
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.MinorDecay

lemma Jm_sq {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

lemma herm_of_inP {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : inP ε X) :
    X.IsHermitian := by
  obtain ⟨h1, h2⟩ := h
  unfold inG at h1
  have h3 : Xᴴ * Jm ε = X * Jm ε := by
    rw [h2]; exact eq_neg_of_add_eq_zero_left h1
  have h4 := congrArg (· * Jm ε) h3
  simp only [Matrix.mul_assoc, Jm_sq, Matrix.mul_one] at h4
  exact h4

lemma diag_of_inP {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : inP ε X)
    (a : Fin n) : X a a = 0 := by
  have h2 := congrFun (congrFun h.2 a) a
  unfold Jm at h2
  simp only [mul_diagonal, Matrix.neg_apply, diagonal_mul] at h2
  split_ifs at h2
  · linear_combination h2 / 2
  · linear_combination -h2 / 2

lemma hs_eq_trace {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    ((hs X : ℝ) : ℂ) = (X * Xᴴ).trace := by
  unfold hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.mul_conj']
  rfl

lemma conj_facts {n : ℕ} {ε : Fin n → Bool} {X k : Matrix (Fin n) (Fin n) ℂ} (h : inP ε X)
    (hk : k ∈ Kset ε) :
    inP ε (k⁻¹ * X * k) ∧ hs (k⁻¹ * X * k) = hs X ∧
      k⁻¹ * NormedSpace.exp X * k = NormedSpace.exp (k⁻¹ * X * k) := by
  obtain ⟨hu, hJ⟩ := hk
  have h1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
  have h2 : k * kᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hu
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv h1
  have hunit : IsUnit k := ⟨⟨k, kᴴ, h2, h1⟩, rfl⟩
  have hH := herm_of_inP h
  have hJ' : kᴴ * Jm ε = Jm ε * kᴴ := by
    calc kᴴ * Jm ε = kᴴ * Jm ε * (k * kᴴ) := by rw [h2, Matrix.mul_one]
      _ = kᴴ * (Jm ε * k) * kᴴ := by simp only [Matrix.mul_assoc]
      _ = (kᴴ * k) * Jm ε * kᴴ := by rw [← hJ]; simp only [Matrix.mul_assoc]
      _ = Jm ε * kᴴ := by rw [h1, Matrix.one_mul]
  have hanti : kᴴ * X * k * Jm ε = -(Jm ε * (kᴴ * X * k)) := by
    calc kᴴ * X * k * Jm ε = kᴴ * (X * Jm ε) * k := by
          simp only [Matrix.mul_assoc]; rw [hJ]
      _ = -(kᴴ * Jm ε * X * k) := by rw [h.2]; simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
      _ = _ := by rw [hJ']; simp only [Matrix.mul_assoc]
  have hYH : (kᴴ * X * k)ᴴ = kᴴ * X * k := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH.eq, Matrix.mul_assoc]
  refine ⟨?_, ?_, (Matrix.exp_conj' k X hunit).symm⟩
  · rw [hinv]
    refine ⟨?_, hanti⟩
    unfold inG
    rw [hYH, hanti, neg_add_cancel]
  · rw [hinv]
    apply Complex.ofReal_injective
    rw [hs_eq_trace, hs_eq_trace, hYH, hH.eq]
    have : kᴴ * X * k * (kᴴ * X * k) = kᴴ * (X * (k * kᴴ) * X * k) := by
      simp only [Matrix.mul_assoc]
    rw [this, h2, Matrix.mul_one, trace_mul_comm, Matrix.mul_assoc, h2, Matrix.mul_one]

lemma deriv_sum_exp {ι : Type} [Fintype ι] (w y : ι → ℝ) :
    deriv (fun t : ℝ => ∑ J, w J * Real.exp (t * y J)) =
      fun t : ℝ => ∑ J, (w J * y J) * Real.exp (t * y J) := by
  funext t
  apply HasDerivAt.deriv
  apply HasDerivAt.fun_sum
  intro J _
  have := (((hasDerivAt_id t).mul_const (y J)).exp).const_mul (w J)
  exact this.congr_deriv (by simp only [id]; ring)

lemma hs_nonneg {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs X := by
  unfold hs; positivity

lemma minor_bound {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inP ε Y)
    (R : ℝ) (hR : R = Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card
      (univ.filter fun a => ε a = false).card : ℕ) : ℝ)) * Real.sqrt (hs Y))
    (l : ℕ) (hl : l ≤ n) :
    0 < (leadMinor (NormedSpace.exp Y) l hl).re ∧ (leadMinor (NormedSpace.exp Y) l hl).im = 0 ∧
      min 1 (1 / R) * (∑ a : Fin n, ∑ b : Fin n,
        if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0) / 4
        ≤ Real.log (leadMinor (NormedSpace.exp Y) l hl).re := by
  have hH := herm_of_inP h
  obtain ⟨w, hw0, -, hw1, hw⟩ := GlobalTheory.T.leadMinor_exp_hermitian_eq_convex_exp_sum n Y hH l hl
  obtain ⟨hd1, hd2⟩ := GlobalTheory.T.deriv_leadMinor_exp_hermitian_zeroDiag n Y hH (diag_of_inP h) l hl
  have hrange := GlobalTheory.T.abs_sum_eigenvalues_noncompactPart_le n ε Y hH h
  rw [← hR] at hrange
  set y : Finset (Fin n) → ℝ := fun J => ∑ j ∈ J, hH.eigenvalues j with hy
  have hfun : (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re)
      = fun t : ℝ => ∑ J, w J * Real.exp (t * y J) := by
    funext t; rw [hw t, Complex.ofReal_re]
  rw [hfun, deriv_sum_exp] at hd1 hd2
  rw [deriv_sum_exp] at hd2
  simp only [zero_mul, Real.exp_zero, mul_one] at hd1 hd2
  have hone := hw 1
  simp only [Complex.ofReal_one, one_smul, one_mul] at hone
  rw [hone, Complex.ofReal_re, Complex.ofReal_im]
  have hpos : 0 < ∑ J, w J * Real.exp (y J) := by
    have : ∃ J, w J ≠ 0 := by
      by_contra hc
      push Not at hc
      simp [hc] at hw1
    obtain ⟨J, hJ⟩ := this
    exact Finset.sum_pos' (fun J _ => mul_nonneg (hw0 J) (Real.exp_pos _).le)
      ⟨J, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (hw0 J) hJ.symm) (Real.exp_pos _)⟩
  refine ⟨hpos, rfl, ?_⟩
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hvar : ∑ J, w J * y J ^ 2 = ∑ a : Fin n, ∑ b : Fin n,
        if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0 := by
    rw [← hd2]; refine Finset.sum_congr rfl fun J _ => by ring
  rw [← hvar]
  rcases hR0.eq_or_lt with h0 | h0
  · have hy0 : ∀ J, y J = 0 := fun J => abs_nonpos_iff.1 (by rw [h0]; exact hrange J)
    change _ ≤ Real.log (∑ J, w J * Real.exp (y J))
    simp [hy0, hw1]
  · exact GlobalTheory.T.quadratic_le_log_sum_exp_of_bounded_centred _ w y R h0 hw0 hw1 hd1 (fun J _ => hrange J)

lemma min_mul_eq (H c : ℝ) (hH : 0 ≤ H) :
    min 1 (1 / (c * Real.sqrt H)) * H = min H (Real.sqrt H / c) := by
  rw [min_mul_of_nonneg _ _ hH, one_mul]
  congr 1
  rcases hH.eq_or_lt with h0 | h0
  · simp [← h0]
  · have hs : 0 < Real.sqrt H := Real.sqrt_pos.2 h0
    have : H = Real.sqrt H * Real.sqrt H := (Real.mul_self_sqrt hH).symm
    rcases eq_or_ne c 0 with hc | hc
    · simp [hc]
    · rw [div_mul_eq_mul_div, one_mul, div_eq_div_iff (by positivity) hc]
      linear_combination c * this

theorem prod_leadMinor_decay : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (X km : Matrix (Fin n) (Fin n) ℂ), IsHCParam lam → GapAtLeast ε lam h → inP ε X → km ∈ Kset ε → (∀ (l : ℕ) (hl : l ≤ n), 0 < (leadMinor (km⁻¹ * NormedSpace.exp X * km) l hl).re ∧ (leadMinor (km⁻¹ * NormedSpace.exp X * km) l hl).im = 0) ∧ ∏ i : Fin (n - 1), (leadMinor (km⁻¹ * NormedSpace.exp X * km) (i.val + 1) (by omega)).re ^ (-(lam ⟨i.val, by omega⟩ - lam ⟨i.val + 1, by omega⟩ + 1)) ≤ Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card (univ.filter fun a => ε a = false).card : ℕ) : ℝ)))) := by
  intro n ε lam h X km hlam hgap hX hk
  obtain ⟨hY, hhs, hexp⟩ := conj_facts hX hk
  rw [hexp, ← hhs]
  set Y := km⁻¹ * X * km with hYdef
  have key := minor_bound hY _ rfl
  refine ⟨fun l hl => ⟨(key l hl).1, (key l hl).2.1⟩, ?_⟩
  have hgs := GlobalTheory.T.hs_le_weighted_sum_blockVariances_of_gap n ε lam h Y hlam.1 hgap hY
  rw [← min_mul_eq _ _ (hs_nonneg Y)]
  set c := Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card
      (univ.filter fun a => ε a = false).card : ℕ) : ℝ)) with hc
  set t := min 1 (1 / (c * Real.sqrt (hs Y))) with ht
  have ht0 : 0 ≤ t := le_min zero_le_one (by positivity)
  rw [Finset.prod_congr rfl fun i _ => Real.rpow_def_of_pos (key _ _).1 _, ← Real.exp_sum,
    Real.exp_le_exp]
  have h2 := mul_le_mul_of_nonneg_left hgs (by positivity : 0 ≤ t / 4)
  rw [Finset.mul_sum] at h2
  have h3 : -(h / 8) * (t * hs Y) = -(t / 4 * (h * hs Y / 2)) := by ring
  rw [h3, le_neg]
  refine h2.trans ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hlt : lam ⟨i.val + 1, by omega⟩ < lam ⟨i.val, by omega⟩ :=
    hlam.1 (by simp [Fin.lt_def])
  have hk := (key (i.val + 1) (by omega)).2.2
  have hs0 : 0 ≤ lam ⟨i.val, by omega⟩ - lam ⟨i.val + 1, by omega⟩ + 1 := by linarith
  have := mul_le_mul_of_nonneg_left hk hs0
  linarith

end GlobalTheory.MinorDecay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ShuffleNoDescentIffOpen
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory

theorem shuffle_first_block_upper (a n : ℕ) (σ : Equiv.Perm (Fin n))
    (h : ∀ i j : Fin n, (i : ℕ) < a → a ≤ (j : ℕ) → (σ j : ℕ) ≠ σ i + 1)
    (i : Fin n) (hi : (i : ℕ) < a) (k : ℕ) :
    ∀ j : Fin n, (σ j : ℕ) = σ i + k → (j : ℕ) < a := by
  induction k with
  | zero =>
    intro j hj
    have : σ j = σ i := Fin.ext (by simpa using hj)
    rw [σ.injective this]; exact hi
  | succ k ih =>
    intro j hj
    have hlt : (σ i : ℕ) + k < n := by have := (σ j).isLt; omega
    have h1 : ((σ (σ.symm ⟨σ i + k, hlt⟩) : Fin n) : ℕ) = σ i + k := by simp
    have h2 := ih _ h1
    by_contra hc
    exact h _ j h2 (not_lt.mp hc) (by omega)

theorem shuffle_noDescent_iff_open :
    ∀ (a b n : ℕ) (σ : Equiv.Perm (Fin n)), n = a + b → (∀ i j : Fin n, i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j) → ((∀ i j : Fin n, (i : ℕ) < a → a ≤ (j : ℕ) → (σ j : ℕ) ≠ σ i + 1) ↔ ∀ j : Fin n, (σ j : ℕ) = if (j : ℕ) < a then b + j else j - a) := by
  intro a b n σ hn hmono
  constructor
  · intro h
    have hup : ∀ i j : Fin n, (i : ℕ) < a → a ≤ (j : ℕ) → σ j < σ i := by
      intro i j hi hj
      by_contra hc
      have hc' : (σ i : ℕ) ≤ σ j := not_lt.mp hc
      have := shuffle_first_block_upper a n σ h i hi (σ j - σ i) j (by omega)
      omega
    let ρ : Fin n → Fin n := fun k =>
      ⟨if (k : ℕ) < b then a + k else k - b, by have := k.isLt; split_ifs <;> omega⟩
    have hρ : ∀ k, (ρ k : ℕ) = if (k : ℕ) < b then a + k else k - b := fun _ => rfl
    have hs : StrictMono (fun k => σ (ρ k)) := by
      intro k l hkl
      have hkl' : (k : ℕ) < l := hkl
      have hk := hρ k
      have hl := hρ l
      have hl2 := l.isLt
      show σ (ρ k) < σ (ρ l)
      by_cases h1 : (k : ℕ) < b
      · by_cases h2 : (l : ℕ) < b
        · rw [if_pos h1] at hk; rw [if_pos h2] at hl
          exact hmono _ _ (Fin.lt_def.mpr (by omega)) (Or.inr (by omega))
        · rw [if_pos h1] at hk; rw [if_neg h2] at hl
          exact hup _ _ (by omega) (by omega)
      · have h2 : ¬ (l : ℕ) < b := by omega
        rw [if_neg h1] at hk; rw [if_neg h2] at hl
        exact hmono _ _ (Fin.lt_def.mpr (by omega)) (Or.inl (by omega))
    have hid : ∀ k, σ (ρ k) = k := fun k =>
      le_antisymm (hs.dual.le_apply (x := OrderDual.toDual k)) hs.le_apply
    intro j
    have hj := j.isLt
    let k : Fin n := ⟨if (j : ℕ) < a then b + j else j - a, by split_ifs <;> omega⟩
    have hk : (k : ℕ) = if (j : ℕ) < a then b + j else j - a := rfl
    have hjk : ρ k = j := by
      apply Fin.ext
      rw [hρ, hk]
      split_ifs <;> omega
    rw [← hk, ← hid k, hjk]
  · intro h i j hi hj
    have h1 := h i
    have h2 := h j
    have := j.isLt
    rw [if_pos hi] at h1
    rw [if_neg (by omega)] at h2
    omega

end GlobalTheory
end

