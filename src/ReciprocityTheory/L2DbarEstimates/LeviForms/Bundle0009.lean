import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0001
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Bundle0001
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0008

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.DetUpdateColEq
section
namespace ReciprocityTheory.L2DbarEstimates.I

namespace MongeAmpereIntegrability

open MeasureTheory Filter Topology Set
open scoped ContDiff

noncomputable section

variable {n : ℕ}

theorem cdo_wd {Ω : Set (V n)} (hΩ : IsOpen Ω) {g : V n → ℂ} (hg : ContDiffOn ℝ ∞ g Ω)
    (j : Fin n) : ContDiffOn ℝ ∞ (wd n j g) Ω ∧ ContDiffOn ℝ ∞ (wdb n j g) Ω := by
  have hF : ∀ v : V n, ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y v) Ω := fun v =>
    ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).1 hg).2.clm_apply contDiffOn_const
  constructor
  · unfold wd
    exact ((hF _).sub (contDiffOn_const.mul (hF _))).div_const 2
  · unfold wdb
    exact ((hF _).add (contDiffOn_const.mul (hF _))).div_const 2

theorem wd_zero_of_eqOn {Z : Set (V n)} (hZ : IsOpen Z) {g : V n → ℂ}
    (h : ∀ w ∈ Z, g w = 0) (j : Fin n) {y : V n} (hy : y ∈ Z) :
    wd n j g y = 0 ∧ wdb n j g y = 0 := by
  have hev : g =ᶠ[𝓝 y] fun _ => (0 : ℂ) := Filter.eventually_of_mem (hZ.mem_nhds hy) fun w hw => h w hw
  have hd : fderiv ℝ g y = 0 := by
    rw [hev.fderiv_eq]; simp
  constructor <;> simp [wd, wdb, hd]

theorem cdo_ofReal {Ω : Set (V n)} {p : V n → ℝ} (hp : ContDiffOn ℝ ∞ p Ω) :
    ContDiffOn ℝ ∞ (fun w => (p w : ℂ)) Ω := Complex.ofRealCLM.contDiff.comp_contDiffOn hp

private theorem lin_lemma' {g₁ g₂ : V n → ℂ} {y : V n} (h₁ : DifferentiableAt ℝ g₁ y)
    (h₂ : DifferentiableAt ℝ g₂ y) (c : ℂ) (j : Fin n) :
    wd n j (fun w => g₁ w + c * g₂ w) y = wd n j g₁ y + c * wd n j g₂ y ∧
      wdb n j (fun w => g₁ w + c * g₂ w) y = wdb n j g₁ y + c * wdb n j g₂ y := by
  have hF : fderiv ℝ (fun w => g₁ w + c * g₂ w) y = fderiv ℝ g₁ y + c • fderiv ℝ g₂ y := by
    have H : HasFDerivAt (fun w => g₁ w + c * g₂ w) (fderiv ℝ g₁ y + c • fderiv ℝ g₂ y) y :=
      h₁.hasFDerivAt.add (h₂.hasFDerivAt.const_mul c)
    exact H.fderiv
  constructor <;>
    simp only [wd, wdb, hF, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul] <;> ring

theorem cHess_add_smul {Ω : Set (V n)} (hΩ : IsOpen Ω) {p q : V n → ℝ}
    (hp : ContDiffOn ℝ ∞ p Ω) (hq : ContDiffOn ℝ ∞ q Ω) (t : ℝ) {y : V n} (hy : y ∈ Ω) :
    cHess n (fun w => ((p w + t * q w : ℝ) : ℂ)) y =
      cHess n (fun w => (p w : ℂ)) y + (t : ℂ) • cHess n (fun w => (q w : ℂ)) y := by
  ext j k
  simp only [cHess, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hP := cdo_ofReal hp
  have hQ := cdo_ofReal hq
  have dP : ∀ v ∈ Ω, DifferentiableAt ℝ (fun w => (p w : ℂ)) v := fun v hv =>
    (hP.contDiffAt (hΩ.mem_nhds hv)).differentiableAt (by simp)
  have dQ : ∀ v ∈ Ω, DifferentiableAt ℝ (fun w => (q w : ℂ)) v := fun v hv =>
    (hQ.contDiffAt (hΩ.mem_nhds hv)).differentiableAt (by simp)
  have hfun : (fun w => ((p w + t * q w : ℝ) : ℂ)) = fun w => (p w : ℂ) + (t : ℂ) * (q w : ℂ) := by
    funext w; push_cast; ring
  rw [hfun]
  have hev : wdb n k (fun w => (p w : ℂ) + (t : ℂ) * (q w : ℂ)) =ᶠ[𝓝 y]
      fun v => wdb n k (fun w => (p w : ℂ)) v + (t : ℂ) * wdb n k (fun w => (q w : ℂ)) v := by
    filter_upwards [hΩ.mem_nhds hy] with v hv
    exact (lin_lemma' (dP v hv) (dQ v hv) _ k).2
  have e1 : wd n j (wdb n k (fun w => (p w : ℂ) + (t : ℂ) * (q w : ℂ))) y =
      wd n j (fun v => wdb n k (fun w => (p w : ℂ)) v + (t : ℂ) * wdb n k (fun w => (q w : ℂ)) v) y := by
    simp only [wd, hev.fderiv_eq]
  rw [e1]
  have dP' : DifferentiableAt ℝ (wdb n k (fun w => (p w : ℂ))) y :=
    (((cdo_wd hΩ hP k).2).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  have dQ' : DifferentiableAt ℝ (wdb n k (fun w => (q w : ℂ))) y :=
    (((cdo_wd hΩ hQ k).2).contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  exact (lin_lemma' dP' dQ' _ j).1

theorem cdo_det {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {S : Set X} {m : WithTop ℕ∞}
    (F : Fin n → Fin n → X → ℂ) (hF : ∀ i j, ContDiffOn ℝ m (F i j) S) :
    ContDiffOn ℝ m (fun w => (Matrix.of fun i j => F i j w).det) S := by
  simp only [Matrix.det_apply, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
  refine ContDiffOn.sum fun σ _ => contDiffOn_const.mul ?_
  exact contDiffOn_prod fun i _ => hF _ _

theorem cdo_adj {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {S : Set X} {m : WithTop ℕ∞}
    (F : Fin n → Fin n → X → ℂ) (hF : ∀ i j, ContDiffOn ℝ m (F i j) S) (k l : Fin n) :
    ContDiffOn ℝ m (fun w => (Matrix.of fun i j => F i j w).adjugate k l) S := by
  simp only [Matrix.adjugate_apply]
  refine cdo_det (F := fun i j w => ((Matrix.of fun i j => F i j w).updateRow l (Pi.single k 1)) i j)
    fun i j => ?_
  by_cases h : i = l
  · simp only [Matrix.updateRow_apply, h, ↓reduceIte]
    exact contDiffOn_const
  · simp only [Matrix.updateRow_apply, h, ↓reduceIte, Matrix.of_apply]
    exact hF i j

theorem cont_adj {X : Type*} [TopologicalSpace X] {S : Set X}
    (F : Fin n → Fin n → X → ℂ) (hF : ∀ i j, ContinuousOn (F i j) S) (k l : Fin n) :
    ContinuousOn (fun w => (Matrix.of fun i j => F i j w).adjugate k l) S := by
  simp only [Matrix.adjugate_apply, Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine continuousOn_finset_sum _ fun σ _ => continuousOn_const.mul ?_
  refine continuousOn_finset_prod _ fun i _ => ?_
  by_cases h : σ i = l
  · simp only [Matrix.updateRow_apply, h, ↓reduceIte]
    exact continuousOn_const
  · simp only [Matrix.updateRow_apply, h, ↓reduceIte, Matrix.of_apply]
    exact hF _ _

theorem adj_sum (M : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) (b : Fin n → ℂ) :
    ∑ j, M.adjugate k j * b j = (M.updateCol k b).det := by
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  simp [Matrix.mulVec, dotProduct]

theorem det_updateCol_eq (M : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) (b : Fin n → ℂ) :
    (M.updateCol k b).det = ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * (b (σ k) * ∏ l ∈ Finset.univ.erase k, M (σ l) l) := by
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
    Matrix.updateCol_self]
  congr 2
  exact Finset.prod_congr rfl fun l hl => Matrix.updateCol_ne (Finset.ne_of_mem_erase hl)

theorem hasDerivAt_det (A B : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (A + (s : ℂ) • B).det)
      (∑ k, ∑ j, (A + (t : ℂ) • B).adjugate k j * B j k) t := by
  have hent : ∀ i j, HasDerivAt (fun s : ℝ => (A + (s : ℂ) • B) i j) (B i j) t := by
    intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    simpa using ((hasDerivAt_id t).ofReal_comp.mul_const (B i j)).const_add (A i j)
  have hdet : HasDerivAt (fun s : ℝ => (A + (s : ℂ) • B).det)
      (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ k, (∏ l ∈ Finset.univ.erase k, (A + (t : ℂ) • B) (σ l) l) • B (σ k) k) t := by
    simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
    have hs := HasDerivAt.sum (u := Finset.univ)
      (A := fun σ (s : ℝ) => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, (A + (s : ℂ) • B) (σ i) i)
      (A' := fun σ => ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ k, (∏ l ∈ Finset.univ.erase k, (A + (t : ℂ) • B) (σ l) l) • B (σ k) k)
      (fun σ _ => by
        have h := (HasDerivAt.finset_prod (u := Finset.univ) fun k _ => hent (σ k) k).const_mul
          (((Equiv.Perm.sign σ : ℤ) : ℂ))
        simp only [Finset.prod_apply] at h
        exact h)
    rw [Finset.sum_fn] at hs
    exact hs
  convert hdet using 1
  simp_rw [adj_sum, det_updateCol_eq, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end

end MongeAmpereIntegrability

end ReciprocityTheory.L2DbarEstimates.I
end

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.TwistLevi
section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem twistLevi (n : ℕ) (M : Type u) [TopologicalSpace M]
    (hLog : LogLeviStatement n M) (hCh : ChainStatement n M) (hB : BasicStatement n M) :
    TwistLeviStatement n M := by
  intro z g ph ph2 r j ε δ hz hg hph hLph hph2 hLph2 hr hj hε hδ hbd
  set c := 1 + Real.log (1 + ε ^ 2) with hc
  have hlε := tl_lw_smoothR n z g ph r ε hg hph hε
  have hlδ := tl_lw_smoothR n z g ph r δ hg hph hδ
  have hwgt : SmoothR n z (wgt n g ph ph2 r j δ) :=
    SmoothR.add n z _ _ (SmoothR.add n z _ _ hph2 (SmoothR.mul n z _ _ (smoothR_const n z _) hph))
      (SmoothR.mul n z _ _ (smoothR_const n z _) hlδ)
  have htw : SmoothR n z (twist n g ph r ε) := by
    rw [tl_twist_eq n g ph r ε hr hε hbd]; exact SmoothR.comp n z _ (tlK_contDiff c) _ hlε
  obtain ⟨hB1, -, -, -⟩ := hB g ph ph2 r j ε δ hr hε hbd
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj

  have key : ∀ x ξ,
      tlKpp c (lw n g ph r ε x) * ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ ^ 2 +
        tlKp c (lw n g ph r ε x) * ((Levi n z (lw n g ph r ε) x ξ).re + (Levi n z ph x ξ).re) ≤
      (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re := by
    intro x ξ
    rw [tl_levi_formula n hCh z g ph ph2 r j ε δ hz hg hph hph2 hr hε hδ hbd x ξ]
    obtain ⟨hx1, he1, hk2, -⟩ := hB1 x
    have hq : tlKp c (lw n g ph r ε x) = kap n g ph r ε x / eta n g ph r ε x := rfl
    have hq0 : 0 ≤ kap n g ph r ε x / eta n g ph r ε x := by
      unfold kap; have : 0 ≤ 1 / xx n g ph r ε x := by positivity
      exact div_nonneg (by linarith) (by linarith)
    have hq2 : kap n g ph r ε x / eta n g ph r ε x ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hL2 := hLph2 x ξ
    have hL := hLph x ξ
    have hδL := (hLog z g ph r δ hz hg hph hLph hr.ne' hδ x ξ).2
    have h1 := mul_nonneg (show 0 ≤ (j : ℝ) - kap n g ph r ε x / eta n g ph r ε x by linarith) hL
    have h2 := mul_nonneg (show (0 : ℝ) ≤ n by positivity) hδL
    rw [hq]
    nlinarith
  refine ⟨hwgt, htw, ?_, ?_⟩
  · intro x ξ
    have hk := key x ξ
    have hεL := (hLog z g ph r ε hz hg hph hLph hr.ne' hε x ξ).2
    obtain ⟨hx1, he1, hk2, -⟩ := hB1 x
    have hq0 : 0 ≤ tlKp c (lw n g ph r ε x) := by
      show 0 ≤ kap n g ph r ε x / eta n g ph r ε x
      unfold kap; have : 0 ≤ 1 / xx n g ph r ε x := by positivity
      exact div_nonneg (by linarith) (by linarith)
    have := mul_nonneg hq0 hεL
    have e : tlKpp c (lw n g ph r ε x) = 1 / (xx n g ph r ε x ^ 2 * eta n g ph r ε x) +
        (kap n g ph r ε x / eta n g ph r ε x) ^ 2 := rfl
    rw [← e]
    linarith
  · intro x ξ hx
    have hk := key x ξ
    obtain ⟨hε1, hεL⟩ := hLog z g ph r ε hz hg hph hLph hr.ne' hε x ξ
    obtain ⟨hx1, he1, hk2, -⟩ := hB1 x
    set D := ‖dDot n z (fun y => (lw n g ph r ε y : ℂ)) x ξ‖ ^ 2 with hD
    set A := (Levi n z (lw n g ph r ε) x ξ).re + (Levi n z ph x ξ).re with hAdef
    have hD0 : 0 ≤ D := by positivity
    have hDA : D ≤ A := by
      have hε2 : 0 < ε ^ 2 := by positivity
      have : ε ^ 2 * D ≤ ε ^ 2 * A := hε1.trans (mul_le_mul_of_nonneg_right hx hεL)
      exact le_of_mul_le_mul_left this hε2
    have hq : tlKp c (lw n g ph r ε x) = kap n g ph r ε x / eta n g ph r ε x := rfl
    have hpp : 0 ≤ tlKpp c (lw n g ph r ε x) := by
      show 0 ≤ 1 / (xx n g ph r ε x ^ 2 * eta n g ph r ε x) + (kap n g ph r ε x / eta n g ph r ε x) ^ 2
      have : 0 ≤ 1 / (xx n g ph r ε x ^ 2 * eta n g ph r ε x) :=
        div_nonneg zero_le_one (mul_nonneg (by positivity) (by linarith))
      positivity
    have hq0 : 0 ≤ kap n g ph r ε x / eta n g ph r ε x := by
      unfold kap; have : 0 ≤ 1 / xx n g ph r ε x := by positivity
      exact div_nonneg (by linarith) (by linarith)
    rw [hq] at hk
    have h3 : kap n g ph r ε x / eta n g ph r ε x * D ≤
        (Levi n z (fun y => wgt n g ph ph2 r j δ y + twist n g ph r ε y) x ξ).re := by
      have := mul_le_mul_of_nonneg_left hDA hq0
      have := mul_nonneg hpp hD0
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ eta n g ph r ε x by linarith)
    have h5 : eta n g ph r ε x * (kap n g ph r ε x / eta n g ph r ε x * D) = kap n g ph r ε x * D := by
      field_simp
    linarith

end ReciprocityTheory.L2DbarEstimates.I
end

