import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0006
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.AnChart
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial

noncomputable section

variable {n : ℕ}

def zeroSet (K : Ideal (MvPolynomial (Fin n) ℂ)) : Set (Fin n → ℂ) :=
  {y | ∀ h ∈ K, eval y h = 0}

def evalFam {e : ℕ} (r : Fin e → MvPolynomial (Fin n) ℂ) (y : Fin n → ℂ) : Fin e → ℂ :=
  fun i => eval y (r i)

theorem exists_holo_coords (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) (e : ℕ)
    [IsRegularLocalRing (locRing K p)] (he : ringKrullDim (locRing K p) = e)
    (r : Fin e → MvPolynomial (Fin n) ℂ)
    (hr : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) =
      Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p)) :
    ∃ (U : Set (Fin n → ℂ)) (V : Set (Fin e → ℂ)) (g : (Fin e → ℂ) → (Fin n → ℂ)),
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ AnalyticOnNhd ℂ g V ∧
      Set.BijOn g V (U ∩ zeroSet K) ∧ ∀ w ∈ V, evalFam r (g w) = w := by
  classical
  obtain ⟨hen, F, hFK, -, hh, hhp, hcut⟩ := exists_jacobian_cut K p e he
  let Ψ : (Fin n → ℂ) → (Fin e → ℂ) × (Fin (n - e) → ℂ) :=
    fun y => (evalFam r y, fun k => eval y (F k))
  have hΨ : ∀ y, Ψ y = (evalFam r y, fun k => eval y (F k)) := fun y => rfl
  let Lr : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) := ContinuousLinearMap.pi fun i =>
    ∑ j, eval p (pderiv j (r i)) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j
  let LF : (Fin n → ℂ) →L[ℂ] (Fin (n - e) → ℂ) := ContinuousLinearMap.pi fun k =>
    ∑ j, eval p (pderiv j (F k)) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j
  let Lm : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) × (Fin (n - e) → ℂ) := Lr.prod LF
  have hΨd : HasFDerivAt Ψ Lm p :=
    (hasFDerivAt_pi.2 fun i => ReciprocityTheory.AnForm.hasFDerivAt_mvPolynomial_eval (r i) p).prodMk
      (hasFDerivAt_pi.2 fun k => ReciprocityTheory.AnForm.hasFDerivAt_mvPolynomial_eval (F k) p)
  have hΨan : AnalyticAt ℂ Ψ p := by
    refine AnalyticAt.prod ?_ ?_
    · rw [analyticAt_pi_iff]; intro i; exact analyticOnNhd_eval_univ (r i) p (Set.mem_univ _)
    · rw [analyticAt_pi_iff]; intro k; exact analyticOnNhd_eval_univ (F k) p (Set.mem_univ _)
  have hstrict : HasStrictFDerivAt Ψ Lm p := by
    have := hΨan.hasStrictFDerivAt; rwa [hΨd.fderiv] at this
  have hinj : Function.Injective Lm := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    refine eq_zero_of_grad K p r hr F hFK hh hhp hcut v (fun i => ?_) (fun k => ?_)
    · have := congrFun (congrArg Prod.fst hv) i; simpa [Lm, Lr] using this
    · have := congrFun (congrArg Prod.snd hv) k; simpa [Lm, LF] using this
  have hsurjL : Function.Surjective Lm := by
    have hdim : Module.finrank ℂ (Fin n → ℂ) =
        Module.finrank ℂ ((Fin e → ℂ) × (Fin (n - e) → ℂ)) := by
      simp [Module.finrank_prod]; omega
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (Lm : (Fin n → ℂ) →ₗ[ℂ] (Fin e → ℂ) × (Fin (n - e) → ℂ)))).mp hinj
  let Le := ContinuousLinearEquiv.ofBijective Lm (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurjL)
  have hLe : (Le : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) × (Fin (n - e) → ℂ)) = Lm :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hφ : HasStrictFDerivAt Ψ (Le : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) × (Fin (n - e) → ℂ)) p := by
    rw [hLe]; exact hstrict
  let Φ := hφ.toOpenPartialHomeomorph Ψ
  have hΦ : ∀ x, Φ x = Ψ x := fun x => rfl
  have hpS : p ∈ Φ.source := hφ.mem_toOpenPartialHomeomorph_source
  have hsymm : AnalyticAt ℂ Φ.symm (Φ p) :=
    Φ.analyticAt_symm' (i := Le) hpS hΨan hφ.hasFDerivAt.fderiv
  obtain ⟨s, hs, hsan⟩ := hsymm.exists_mem_nhds_analyticOnNhd
  obtain ⟨T0, hT0s, hT0o, hT0p⟩ := mem_nhds_iff.mp hs
  have hHo : IsOpen {y : Fin n → ℂ | eval y hh ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval hh) continuous_const
  set O : Set (Fin n → ℂ) := (Φ.source ∩ {y | eval y hh ≠ 0}) ∩ Φ ⁻¹' T0 with hOdef
  have hO : IsOpen O := (Φ.continuousOn.mono Set.inter_subset_left).isOpen_inter_preimage
    (Φ.open_source.inter hHo) hT0o
  set T : Set ((Fin e → ℂ) × (Fin (n - e) → ℂ)) := Φ.target ∩ Φ.symm ⁻¹' O with hTdef
  have hT : IsOpen T := Φ.continuousOn_symm.isOpen_inter_preimage Φ.open_target hO

  have hzs : ∀ y, eval y hh ≠ 0 → (∀ k, eval y (F k) = 0) → y ∈ zeroSet K := by
    intro y hy hFy k hk
    have hspan : Ideal.span (Set.range F) ≤ RingHom.ker (eval y) := by
      rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact RingHom.mem_ker.mpr (hFy i)
    have h1 := RingHom.mem_ker.mp (hspan (hcut k hk))
    rw [map_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left hy
  refine ⟨O, {w | (w, (0 : Fin (n - e) → ℂ)) ∈ T}, fun w => Φ.symm (w, 0), hO,
    ⟨⟨hpS, hhp⟩, hT0p⟩, hT.preimage (continuous_id.prodMk continuous_const), ?_, ?_, ?_⟩
  · intro w hw
    have hw1 : (w, (0 : Fin (n - e) → ℂ)) ∈ s := by
      have h2 := hw.2.2
      rw [Set.mem_preimage, Φ.right_inv hw.1] at h2
      exact hT0s h2
    have h1 : AnalyticAt ℂ (fun w : Fin e → ℂ => (w, (0 : Fin (n - e) → ℂ))) w :=
      analyticAt_id.prod analyticAt_const
    exact AnalyticAt.comp (f := fun w : Fin e → ℂ => (w, (0 : Fin (n - e) → ℂ))) (hsan _ hw1) h1
  · refine ⟨?_, ?_, ?_⟩
    · intro w hw
      refine ⟨hw.2, hzs _ hw.2.1.2 fun k => ?_⟩
      have := congrFun (congrArg Prod.snd (Φ.right_inv hw.1)) k
      rwa [hΦ, hΨ] at this
    · intro w hw w' hw' h
      have h2 : Φ (Φ.symm (w, 0)) = Φ (Φ.symm (w', 0)) := by
        simp only at h; rw [h]
      rw [Φ.right_inv hw.1, Φ.right_inv hw'.1] at h2
      exact congrArg Prod.fst h2
    · rintro y ⟨hyO, hyK⟩
      have hy : Φ y = (evalFam r y, 0) := by
        rw [hΦ, hΨ]; congr 1; funext k; exact hyK _ (hFK k)
      refine ⟨evalFam r y, ⟨?_, ?_⟩, ?_⟩
      · rw [← hy]; exact Φ.map_source hyO.1.1
      · show Φ.symm (evalFam r y, 0) ∈ O
        rw [← hy, Φ.left_inv hyO.1.1]; exact hyO
      · show Φ.symm (evalFam r y, 0) = y
        rw [← hy]; exact Φ.left_inv hyO.1.1
  · intro w hw
    have := congrArg Prod.fst (Φ.right_inv hw.1)
    rwa [hΦ, hΨ] at this

end

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def IsMultiHomogIdeal (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : Prop :=
  ∃ S : Set (MvPolynomial (Σ k, ι k) ℂ), (∀ f ∈ S, ∃ a, IsMultiHomog f a) ∧ P = Ideal.span S

def IsRelevant (W : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : Prop :=
  ∀ k, ∃ i, (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ W

def chartIdeal (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  P ⊔ Ideal.span (Set.range fun k => (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ))

abbrev chartRing (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) : Type :=
  MvPolynomial (Σ k, ι k) ℂ ⧸ chartIdeal P p

theorem eval_smul_of_isMultiHomog {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) (c : K → ℂ) (y : (Σ k, ι k) → ℂ) :
    eval (fun q => c q.1 * y q) f = (∏ k, c k ^ a k) * eval y f := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hc : ∏ q : (Σ k, ι k), c q.1 ^ d q = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  have key : ∏ q, (c q.1 * y q) ^ d q = (∏ k, c k ^ a k) * ∏ q, y q ^ d q := by
    rw [← hc, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun q _ => mul_pow _ _ _)
  linear_combination (coeff d f) * key

theorem eval_eq_zero_of_smul {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (c : K → ℂ) (y : (Σ k, ι k) → ℂ) (hy : ∀ f ∈ P, eval y f = 0) :
    ∀ f ∈ P, eval (fun q => c q.1 * y q) f = 0 := by
  obtain ⟨S, hS, rfl⟩ := hP
  intro f hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, ha⟩ := hS g hg
    rw [eval_smul_of_isMultiHomog ha, hy g (Ideal.subset_span hg), mul_zero]
  | zero => simp
  | add g h _ _ hg hh => rw [map_add, hg, hh, add_zero]
  | smul a g _ hg => rw [smul_eq_mul, map_mul, hg, mul_zero]

theorem mem_conePts_iff_chartIdeal {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    z ∈ conePts P ↔ ∀ h ∈ chartIdeal P p, eval (affCoord p z) h = 0 := by
  have haff : affCoord p z = fun q => (z ⟨q.1, p q.1⟩)⁻¹ * z q := by
    funext q
    show z q / z ⟨q.1, p q.1⟩ = _
    rw [div_eq_inv_mul]
  unfold conePts
  rw [Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, hzP⟩
    have hle : chartIdeal P p ≤ RingHom.ker (eval (affCoord p z)) := by
      refine sup_le ?_ ?_
      · intro f hf
        rw [RingHom.mem_ker, haff]
        exact eval_eq_zero_of_smul hP (fun k => (z ⟨k, p k⟩)⁻¹) z hzP f hf
      · rw [Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, eval_X, map_one]
        show z ⟨k, p k⟩ / z ⟨k, p k⟩ - 1 = 0
        rw [div_self (hz k), sub_self]
    intro h hh
    exact hle hh
  · intro hch
    refine ⟨fun k => ⟨p k, hz k⟩, ?_⟩
    have hzeq : z = fun q => z ⟨q.1, p q.1⟩ * affCoord p z q := by
      funext q
      show z q = z ⟨q.1, p q.1⟩ * (z q / z ⟨q.1, p q.1⟩)
      have := hz q.1
      field_simp
    intro f hf
    rw [hzeq]
    exact eval_eq_zero_of_smul hP (fun k => z ⟨k, p k⟩) (affCoord p z)
      (fun g hg => hch g (Ideal.mem_sup_left hg)) f hf

theorem conePts_of_chartIdeal {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (y : (Σ k, ι k) → ℂ) (hy : ∀ h ∈ chartIdeal P p, eval y h = 0) :
    y ∈ conePts P ∧ (∀ k, y ⟨k, p k⟩ = 1) ∧ affCoord p y = y := by
  have hle : Ideal.span (Set.range fun k => (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ)) ≤
      chartIdeal P p := le_sup_right
  have hleP : P ≤ chartIdeal P p := le_sup_left
  have h1 : ∀ k, y ⟨k, p k⟩ = 1 := by
    intro k
    have hmem : (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ chartIdeal P p :=
      hle (Ideal.subset_span (Set.mem_range_self k))
    have := hy _ hmem
    rw [map_sub, eval_X, map_one, sub_eq_zero] at this
    exact this
  refine ⟨?_, h1, ?_⟩
  · unfold conePts
    rw [Set.mem_setOf_eq]
    exact ⟨fun k => ⟨p k, by rw [h1 k]; exact one_ne_zero⟩, fun f hf => hy f (hleP hf)⟩
  · funext q
    show y q / y ⟨q.1, p q.1⟩ = y q
    rw [h1 q.1, div_one]

theorem exists_chart (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∃ p : (k : K) → ι k, (∀ k, z ⟨k, p k⟩ ≠ 0) ∧ ∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, p k⟩‖ := by
  have hmax : ∀ k, ∃ i, ∀ j, ‖z ⟨k, j⟩‖ ≤ ‖z ⟨k, i⟩‖ := fun k => by
    obtain ⟨i0, _⟩ := hz k
    haveI : Nonempty (ι k) := ⟨i0⟩
    exact Finite.exists_max (fun j => ‖z ⟨k, j⟩‖)
  choose p hp using hmax
  refine ⟨p, fun k => ?_, fun k i => hp k i⟩
  obtain ⟨i0, hi0⟩ := hz k
  have h1 : 0 < ‖z ⟨k, i0⟩‖ := norm_pos_iff.mpr hi0
  have h2 := hp k i0
  intro h
  rw [h, norm_zero] at h2
  linarith

theorem affCoord_eq_of_sameOrbit (p : (k : K) → ι k) {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : affCoord p z = affCoord p z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext q
  show c q.1 * z' q / (c q.1 * z' ⟨q.1, p q.1⟩) = z' q / z' ⟨q.1, p q.1⟩
  exact mul_div_mul_left (z' q) (z' ⟨q.1, p q.1⟩) (hc q.1)

theorem sameOrbit_affCoord (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    SameOrbit z (affCoord p z) := by
  refine ⟨fun k => z ⟨k, p k⟩, hz, ?_⟩
  funext q
  show z q = z ⟨q.1, p q.1⟩ * (z q / z ⟨q.1, p q.1⟩)
  have := hz q.1
  field_simp

end

end ReciprocityTheory.AnForm.R
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjectiveLineMultihomogClassify
section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial OnePoint Filter Topology

noncomputable section

def projectiveLineInvPoint (w : ℂ) : OnePoint ℂ := if w = 0 then ∞ else ((w⁻¹ : ℂ) : OnePoint ℂ)

def locRingBotEquivN {n : ℕ} (p : Fin n → ℂ) :
    locPt p ≃+* locRing (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) p :=
  (RingEquiv.quotientBot (locPt p)).symm.trans (Ideal.quotEquivOfEq Ideal.map_bot.symm)

theorem ptIdeal_isMaximal {n : ℕ} (p : Fin n → ℂ) : (ptIdeal p).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c => ⟨C c, eval_C c⟩

theorem locRing_bot_regularN {n : ℕ} (p : Fin n → ℂ) :
    IsRegularLocalRing (locRing (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) p) :=
  IsRegularLocalRing.of_ringEquiv (locRingBotEquivN p)

theorem locRing_bot_dimN {n : ℕ} (p : Fin n → ℂ) :
    ringKrullDim (locRing (⊥ : Ideal (MvPolynomial (Fin n) ℂ)) p) = n := by
  have := ptIdeal_isMaximal p
  rw [← ringKrullDim_eq_of_ringEquiv (locRingBotEquivN p),
    IsLocalization.AtPrime.ringKrullDim_eq_height (ptIdeal p) (locPt p),
    (ReciprocityTheory.CA.height_maximal_mvPolynomial_field ℂ n (ptIdeal p)).2]
  rfl

theorem sub_C_eval_mem_span {n : ℕ} (p : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) :
    f - C (eval p f) ∈ Ideal.span (Set.range fun i => X i - C (p i)) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg =>
    have : f + g - C (eval p (f + g)) = (f - C (eval p f)) + (g - C (eval p g)) := by
      simp only [map_add]; ring
    rw [this]; exact add_mem hf hg
  | mul_X f i hf =>
    have : f * X i - C (eval p (f * X i)) =
        (f - C (eval p f)) * X i + C (eval p f) * (X i - C (p i)) := by
      simp only [map_mul, eval_X]; ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))

theorem ptIdeal_eq_span {n : ℕ} (p : Fin n → ℂ) :
    ptIdeal p = Ideal.span (Set.range fun i => X i - C (p i)) := by
  apply le_antisymm
  · intro f hf
    have h0 : eval p f = 0 := hf
    simpa [h0] using sub_C_eval_mem_span p f
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    show eval p (X i - C (p i)) = 0
    simp

end

end ReciprocityTheory.AnForm.R
end

