import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.TaylorExpansionLocalCoordinates
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NmatZeroMemBor
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open Filter Asymptotics

namespace GlobalTheory.LeadJets

noncomputable section

theorem mem_multiLt {n a : ℕ} {α : Fin n → ℕ} : α ∈ multiLt n a ↔ ∑ k, α k < a := by
  simp [multiLt, Finset.Nat.mem_antidiagonalTuple]

def leadVal {n δ : ℕ} (s : Fin n → ℂ) (w : ℂ) (t : Fin δ → ℂ) (T a0 : ℕ)
    (cc : (Fin n → ℕ) → Fin δ → ℂ) : ℂ :=
  ∑ α ∈ multiLt n a0, ∑ k, cc α k * (∏ q, s q ^ α q) * w ^ (T - ∑ q, α q) * t k

theorem leadVal_add {n δ : ℕ} (s : Fin n → ℂ) (w : ℂ) (t : Fin δ → ℂ) {T a0 a : ℕ}
    (ha : a < a0) (ha0 : a0 ≤ T + 1) (cc dd : (Fin n → ℕ) → Fin δ → ℂ) (hw : w ≠ 0) :
    leadVal s w t T a0 (fun α k => cc α k + if ∑ q, α q = a then dd α k else 0) =
      leadVal s w t T a0 cc + ∑ α ∈ Finset.Nat.antidiagonalTuple n a,
        (w ^ T * ∑ k, dd α k * t k) * ∏ k, (s k / w) ^ α k := by
  classical
  have hfil : (multiLt n a0).filter (fun α => ∑ q, α q = a) =
      Finset.Nat.antidiagonalTuple n a := by
    ext α
    simp only [Finset.mem_filter, mem_multiLt, Finset.Nat.mem_antidiagonalTuple]
    omega
  unfold leadVal
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  rw [← hfil, Finset.sum_filter]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hlt := mem_multiLt.1 hα
  by_cases h : ∑ q, α q = a
  · simp only [if_pos h]
    have hm : (∏ q, s q ^ α q) = (∏ k, (s k / w) ^ α k) * w ^ (∑ q, α q) := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [← mul_pow, div_mul_cancel₀ _ hw]
    have hT : w ^ (∑ q, α q) * w ^ (T - ∑ q, α q) = w ^ T := by
      rw [← pow_add]; congr 1; omega
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hm]
    linear_combination (dd α k * (∏ q, (s q / w) ^ α q) * t k) * hT
  · simp [h]

theorem leadVal_diffOn {n δ : ℕ} {U : Set (V n)} {s : V n → Fin n → ℂ} {w : V n → ℂ}
    {t : V n → Fin δ → ℂ} (hs : ∀ k, DifferentiableOn ℂ (fun z => s z k) U)
    (hw : DifferentiableOn ℂ w U) (ht : ∀ k, DifferentiableOn ℂ (fun z => t z k) U)
    (T a0 : ℕ) (cc : (Fin n → ℕ) → Fin δ → ℂ) :
    DifferentiableOn ℂ (fun z => leadVal (s z) (w z) (t z) T a0 cc) U := by
  unfold leadVal
  refine DifferentiableOn.fun_sum fun α _ => DifferentiableOn.fun_sum fun k _ => ?_
  refine (((differentiableOn_const _).mul ?_).mul (hw.pow _)).mul (ht k)
  refine Finset.induction_on (motive := fun F : Finset (Fin n) =>
    DifferentiableOn ℂ (fun z => ∏ q ∈ F, s z q ^ α q) U) Finset.univ ?_ fun q F hq ih => ?_
  · simpa using differentiableOn_const (1 : ℂ)
  · simp only [Finset.prod_insert hq]
    exact ((hs q).fun_pow _).mul ih

section Step

variable {n δ m : ℕ} {U : Fin m → Set (V n)} {f w : Fin m → V n → ℂ}
  {s : Fin m → V n → Fin n → ℂ} {t : Fin m → V n → Fin δ → ℂ}

theorem step {T a0 a : ℕ} (ha : a < a0) (ha0 : a0 ≤ T + 1)
    (hU : ∀ j, IsOpen (U j)) (h0 : ∀ j, (0 : V n) ∈ U j)
    (hf : ∀ j, DifferentiableOn ℂ (f j) (U j)) (hw : ∀ j, DifferentiableOn ℂ (w j) (U j))
    (hs : ∀ j k, DifferentiableOn ℂ (fun z => s j z k) (U j))
    (ht : ∀ j k, DifferentiableOn ℂ (fun z => t j z k) (U j))
    (hw0 : ∀ j, w j 0 ≠ 0) (hs0 : ∀ j k, s j 0 k = 0)
    (hcoord : ∀ j, (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => s j z k / w j z : V n)) 0).det ≠ 0)
    (hsurj : ∀ v : Fin m → ℂ, ∃ c : Fin δ → ℂ, ∀ j, ∑ k, c k * t j 0 k = v j)
    (cc : (Fin n → ℕ) → Fin δ → ℂ)
    (hcc : ∀ j, (fun z => f j z - leadVal (s j z) (w j z) (t j z) T a0 cc) =O[𝓝 0] fun z => ‖z‖ ^ a) :
    ∃ cc' : (Fin n → ℕ) → Fin δ → ℂ, ∀ j,
      (fun z => f j z - leadVal (s j z) (w j z) (t j z) T a0 cc') =O[𝓝 0] fun z => ‖z‖ ^ (a + 1) := by
  classical
  set ζ : Fin m → V n → V n := fun j z => (WithLp.toLp 2 fun k => s j z k / w j z : V n) with hζdef
  have loc : ∀ j, ∃ U' : Set (V n), IsOpen U' ∧ (0 : V n) ∈ U' ∧ U' ⊆ U j ∧
      (∀ v ∈ U', w j v ≠ 0) ∧ DifferentiableOn ℂ (ζ j) U' ∧ ζ j 0 = 0 := by
    intro j
    refine ⟨U j ∩ w j ⁻¹' {0}ᶜ, (hw j).continuousOn.isOpen_inter_preimage (hU j)
      isOpen_compl_singleton, ⟨h0 j, hw0 j⟩, Set.inter_subset_left, fun v hv => hv.2, ?_, ?_⟩
    · refine differentiableOn_euclidean.2 fun k => ?_
      have hdiv : DifferentiableOn ℂ (fun v => s j v k * (w j v)⁻¹) (U j ∩ w j ⁻¹' {0}ᶜ) :=
        ((hs j k).mono Set.inter_subset_left).mul
          (((hw j).mono Set.inter_subset_left).inv fun v hv => hv.2)
      exact hdiv.congr fun v _ => by simp [hζdef, div_eq_mul_inv]
    · ext k
      simp [hζdef, hs0]
  have hb : ∀ j, ∃ b : (Fin n → ℕ) → ℂ,
      (fun v => (f j v - leadVal (s j v) (w j v) (t j v) T a0 cc) -
        ∑ α ∈ Finset.Nat.antidiagonalTuple n a, b α * ∏ k, ζ j v k ^ α k)
        =O[𝓝 0] fun v => ‖v‖ ^ (a + 1) := by
    intro j
    obtain ⟨U', hUo, hxU, hUt, -, hζ, hζ0⟩ := loc j
    obtain ⟨b, hb⟩ := taylor_expansion_local_coordinates (a := a)
      (fun v => f j v - leadVal (s j v) (w j v) (t j v) T a0 cc) (ζ j) U' 0 hUo hxU
      (((hf j).sub (leadVal_diffOn (hs j) (hw j) (ht j) T a0 cc)).mono hUt) hζ hζ0 (hcoord j)
      (by simpa only [sub_zero] using hcc j)
    exact ⟨b, by simpa only [sub_zero] using hb⟩
  choose bb hbb using hb
  choose dd hdd using fun α => hsurj (fun j => bb j α / w j 0 ^ T)
  refine ⟨fun α k => cc α k + if ∑ q, α q = a then dd α k else 0, fun j => ?_⟩
  obtain ⟨U', hUo, hxU, hUt, hUw, hζ, hζ0⟩ := loc j
  have hxt : U j ∈ 𝓝 (0 : V n) := (hU j).mem_nhds (h0 j)
  have hζO : (fun v => ζ j v) =O[𝓝 0] fun v => v := by
    have := (hζ.differentiableAt (hUo.mem_nhds hxU)).hasFDerivAt.isBigO_sub
    simpa only [hζ0, sub_zero] using this
  have hQ : ∀ α ∈ Finset.Nat.antidiagonalTuple n a,
      (fun v => ∏ k, ζ j v k ^ α k) =O[𝓝 0] fun v => ‖v‖ ^ a := by
    intro α hα
    have hsum := Finset.Nat.mem_antidiagonalTuple.1 hα
    refine (IsBigO.of_bound 1 (Eventually.of_forall fun v => ?_)).trans (hζO.norm_norm.pow a)
    calc ‖∏ k, ζ j v k ^ α k‖
        = ∏ k, ‖ζ j v k‖ ^ α k := by simp only [norm_prod, norm_pow]
      _ ≤ ∏ k, ‖ζ j v‖ ^ α k :=
          Finset.prod_le_prod (fun k _ => by positivity)
            (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le _ _) _)
      _ = 1 * ‖‖ζ j v‖ ^ a‖ := by
          rw [Finset.prod_pow_eq_pow_sum, hsum, one_mul, norm_pow, norm_norm]
  have hφ : ∀ α, (fun v => bb j α - w j v ^ T * ∑ k, dd α k * t j v k)
        =O[𝓝 0] fun v => ‖v‖ ^ 1 := by
    intro α
    have hd : DifferentiableAt ℂ (fun v => bb j α - w j v ^ T * ∑ k, dd α k * t j v k) 0 := by
      refine (differentiableAt_const _).sub ((((hw j).differentiableAt hxt).pow T).mul ?_)
      exact DifferentiableAt.fun_sum fun k _ => ((ht j k).differentiableAt hxt).const_mul _
    have h00 : bb j α - w j 0 ^ T * ∑ k, dd α k * t j 0 k = 0 := by
      rw [hdd α j, mul_div_cancel₀ _ (pow_ne_zero _ (hw0 j)), sub_self]
    have := hd.hasFDerivAt.isBigO_sub
    rw [h00] at this
    simp only [sub_zero] at this
    exact (this.trans (isBigO_refl _ _).norm_right).congr_right fun v => (pow_one _).symm
  have h2 : (fun v => ∑ α ∈ Finset.Nat.antidiagonalTuple n a,
      (bb j α - w j v ^ T * ∑ k, dd α k * t j v k) * ∏ k, ζ j v k ^ α k)
      =O[𝓝 0] fun v => ‖v‖ ^ (a + 1) := by
    have hterm : ∀ α ∈ Finset.Nat.antidiagonalTuple n a,
        (fun v => (bb j α - w j v ^ T * ∑ k, dd α k * t j v k) * ∏ k, ζ j v k ^ α k)
        =O[𝓝 0] fun v => ‖v‖ ^ (a + 1) :=
      fun α hα => ((hφ α).mul (hQ α hα)).congr_right fun v => by ring
    exact (IsBigO.sum hterm).congr_left fun v => Finset.sum_apply _ _ _
  refine ((hbb j).add h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [hUo.mem_nhds hxU] with v hv
  beta_reduce
  rw [leadVal_add _ _ _ ha ha0 cc dd (hUw v hv)]
  simp only [hζdef, PiLp.toLp_apply, sub_mul, Finset.sum_sub_distrib]
  ring

theorem jets {T a0 : ℕ} (ha0 : a0 ≤ T + 1)
    (hU : ∀ j, IsOpen (U j)) (h0 : ∀ j, (0 : V n) ∈ U j)
    (hf : ∀ j, DifferentiableOn ℂ (f j) (U j)) (hw : ∀ j, DifferentiableOn ℂ (w j) (U j))
    (hs : ∀ j k, DifferentiableOn ℂ (fun z => s j z k) (U j))
    (ht : ∀ j k, DifferentiableOn ℂ (fun z => t j z k) (U j))
    (hw0 : ∀ j, w j 0 ≠ 0) (hs0 : ∀ j k, s j 0 k = 0)
    (hcoord : ∀ j, (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => s j z k / w j z : V n)) 0).det ≠ 0)
    (hsurj : ∀ v : Fin m → ℂ, ∃ c : Fin δ → ℂ, ∀ j, ∑ k, c k * t j 0 k = v j) :
    ∃ cc : (Fin n → ℕ) → Fin δ → ℂ, ∀ j,
      (fun z => f j z - leadVal (s j z) (w j z) (t j z) T a0 cc) =O[𝓝 0] fun z => ‖z‖ ^ a0 := by
  have key : ∀ a ≤ a0, ∃ cc : (Fin n → ℕ) → Fin δ → ℂ, ∀ j,
      (fun z => f j z - leadVal (s j z) (w j z) (t j z) T a0 cc) =O[𝓝 0] fun z => ‖z‖ ^ a := by
    intro a
    induction a with
    | zero =>
      intro _
      refine ⟨0, fun j => ?_⟩
      have hc := (((hf j).sub (leadVal_diffOn (hs j) (hw j) (ht j) T a0 0)).differentiableAt
        ((hU j).mem_nhds (h0 j))).continuousAt
      exact (hc.tendsto.isBigO_one ℝ).congr_right fun v => (pow_zero _).symm
    | succ a ih =>
      intro ha
      obtain ⟨cc, hcc⟩ := ih (by omega)
      exact step (by omega) ha0 hU h0 hf hw hs ht hw0 hs0 hcoord hsurj cc hcc
  exact key a0 le_rfl

end Step

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mat_nmat_zero {r : ℕ} (X : Data E r) (τ : X.Ψ) : mat (nmat X 0) τ = 1 := by
  ext a b
  by_cases h1 : b < a
  · simp [mat, nmat, h1, h1.ne']
    rfl
  · simp [mat, nmat, h1, Matrix.one_apply]

theorem cpt_zero {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) : cpt X x0 0 = x0 := by
  funext τ
  show (mat x0 τ * mat (nmat X 0) τ : Matrix (Fin r) (Fin r) ℂ) = x0 τ
  rw [mat_nmat_zero, Matrix.mul_one]
  rfl

theorem rmul_nmat_zero {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) : rmul x0 (nmat X 0) = x0 :=
  cpt_zero X x0

theorem nmat_zero_mem_Bor {r : ℕ} (X : Data E r) : nmat X 0 ∈ Bor X.Ψ r := by
  intro τ
  refine ⟨by rw [mat_nmat_zero, Matrix.det_one]; exact one_ne_zero, fun a c h => ?_⟩
  have := congrFun (congrFun (mat_nmat_zero X τ) a) c
  rw [Matrix.one_apply_ne h.ne'] at this
  exact this

theorem lact_one {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show (((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rfl

theorem main : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (T a δ : ℕ), a ≤ T + 1 →
    ∀ (t : Fin δ → Frame X.Ψ r → ℂ), (∀ k, X.IsSec G (t k)) → IsValBasisM X Fl.xs t →
    ∀ f, X.IsSec (G + T • Xa.L) f →
    ∃ cc : (Fin (nd X) → ℕ) → Fin δ → ℂ, ∀ j,
      (fun z : V (nd X) => f (cpt X (Fl.xs j) z) - leadM X Fl.s Fl.w0 t T a cc (cpt X (Fl.xs j) z))
        =O[𝓝 0] fun z => ‖z‖ ^ a := by
  intro r X Xa Fl G T a δ ha t ht hb f hf
  have hs0 : ∀ j k, Fl.s k (Fl.xs j) = 0 := fun j =>
    (Fl.S_eq _ (Fl.xs_mem j)).2 ⟨j, 1, one_mem _, nmat X 0, nmat_zero_mem_Bor X, by
      rw [rmul_nmat_zero, lact_one]⟩
  exact jets (U := fun j => OmF X (Fl.xs j)) (f := fun j z => f (cpt X (Fl.xs j) z))
    (w := fun j z => Fl.w0 (cpt X (Fl.xs j) z)) (s := fun j z k => Fl.s k (cpt X (Fl.xs j) z))
    (t := fun j z k => t k (cpt X (Fl.xs j) z)) ha
    (fun j => OntoB.isOpen_OmF X _)
    (fun j => by
      show cpt X (Fl.xs j) 0 ∈ X.dom
      rw [cpt_zero]; exact Fl.xs_mem j)
    (fun j => OntoB.hol_comp X _ hf.1)
    (fun j => OntoB.hol_comp X _ Fl.weightForm_vanishes.1.1.1.1)
    (fun j k => OntoB.hol_comp X _ (Fl.s_van k).1.1.1.1)
    (fun j k => OntoB.hol_comp X _ (ht k).1)
    (fun j => by simpa only [cpt_zero] using Fl.w0_ne j)
    (fun j k => by simpa only [cpt_zero] using hs0 j k)
    Fl.coord
    (fun v => by simpa only [cpt_zero] using hb.1 v)

end

end GlobalTheory.LeadJets
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OrthonormalFramesBoundedOfDefinite
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.norm_entry_le_of_gram_eq_smul_one {r : ℕ} (G x : Matrix (Fin r) (Fin r) ℂ) (s : ℂ)
    (hs : s * s = 1) (h : xᵀ * G * x.map (starRingEnd ℂ) = s • (1 : Matrix (Fin r) (Fin r) ℂ))
    (a b : Fin r) : ‖x a b‖ ≤ 1 + ‖G⁻¹ a a‖ := by
  set y := x.map (starRingEnd ℂ) with hy
  have h1 : xᵀ * (s • (G * y)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, h, smul_smul, hs, one_smul]
  have h2 : (s • (G * y)) * xᵀ = 1 := mul_eq_one_comm.1 h1
  have h3 : G * (s • (y * xᵀ)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.smul_mul]; exact h2
  have hinv : G⁻¹ = s • (y * xᵀ) := Matrix.inv_eq_right_inv h3
  have hentry : G⁻¹ a a = s * ((∑ c, ‖x a c‖ ^ 2 : ℝ) : ℂ) := by
    rw [hinv, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
    congr 1
    push_cast
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [hy, Matrix.transpose_apply, Complex.conj_mul']
  have hsn : ‖s‖ = 1 := by
    have h4 := congrArg norm hs
    rw [norm_mul, norm_one] at h4
    nlinarith [norm_nonneg s]
  have hsum : 0 ≤ ∑ c, ‖x a c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hnorm : ‖G⁻¹ a a‖ = ∑ c, ‖x a c‖ ^ 2 := by
    rw [hentry, norm_mul, hsn, one_mul, Complex.norm_of_nonneg hsum]
  have hle : ‖x a b‖ ^ 2 ≤ ∑ c, ‖x a c‖ ^ 2 :=
    Finset.single_le_sum (f := fun c => ‖x a c‖ ^ 2) (fun c _ => sq_nonneg _) (Finset.mem_univ b)
  rw [hnorm]
  nlinarith [sq_nonneg (‖x a b‖ - 1), norm_nonneg (x a b)]

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.orthonormal_frames_bounded_of_definite :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), (X.p0 = 0 ∨ X.p0 = r) →
      ∃ R : ℝ, ∀ x, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ∀ τ a b, ‖x τ a b‖ ≤ R) := by
  intro r X hp
  refine ⟨1 + ∑ τ : X.Ψ, ∑ a : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a a‖,
    fun x hx τ a b => ?_⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at hx
  have hτ := hx τ
  obtain ⟨s, hs, hdiag⟩ : ∃ s : ℂ, s * s = 1 ∧
      Matrix.diagonal (fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ)) = s • 1 := by
    rcases hp with h | h
    · refine ⟨-1, by norm_num, ?_⟩
      ext i j
      simp [h, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, Matrix.diagonal_apply, Matrix.one_apply]
    · refine ⟨1, by norm_num, ?_⟩
      ext i j
      simp [h, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, Matrix.diagonal_apply, Matrix.one_apply]
  have key : (Matrix.of (x τ))ᵀ * X.Gm.map (τ : E →+* ℂ) * (Matrix.of (x τ)).map (starRingEnd ℂ)
      = s • 1 := by
    rw [← hdiag, ← hτ]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.gram _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hb := _root_.GlobalTheory.norm_entry_le_of_gram_eq_smul_one _ _ s hs key a b
  have h1 : ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a a‖ ≤ ∑ a' : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖ :=
    Finset.single_le_sum (f := fun a' => ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  have h2 : ∑ a' : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖ ≤
      ∑ τ' : X.Ψ, ∑ a' : Fin r, ‖((X.Gm.map (τ' : E →+* ℂ))⁻¹) a' a'‖ :=
    Finset.single_le_sum (f := fun τ' : X.Ψ => ∑ a' : Fin r, ‖((X.Gm.map (τ' : E →+* ℂ))⁻¹) a' a'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ)
  have hx' : ‖x τ a b‖ = ‖Matrix.of (x τ) a b‖ := rfl
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexSpanNeZero
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.SpanIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.SpanIndex.relIndex_span_ne_zero : (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) ≠ 0) := by
  classical
  intro r X ι _ _ w _ hw
  set V := Submodule.span E (Set.range w)
  set N := Submodule.span (𝓞 E) (Set.range w)
  set M : Submodule (𝓞 E) (Fin r → E) := X.Λ ⊓ V.restrictScalars (𝓞 E)
  have hK : X.Λ.toAddSubgroup ⊓ V.toAddSubgroup = M.toAddSubgroup := rfl
  rw [hK]
  have hMfg : M.FG := by
    haveI : IsNoetherian (𝓞 E) X.Λ := isNoetherian_of_fg_of_noetherian X.Λ X.Λ_fg
    exact Submodule.FG.of_le_of_isNoetherian inf_le_left
  haveI : Module.Finite (𝓞 E) M := Module.Finite.iff_fg.mpr hMfg
  haveI : Module.Finite ℤ (M ⧸ N.comap M.subtype) := Module.Finite.trans (𝓞 E) _
  have htors : Module.IsTorsion ℤ (M ⧸ N.comap M.subtype) := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨v, hv⟩ := x
      have hvV : v ∈ V := (Submodule.mem_inf.mp hv).2
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hvV
      obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image c)
      refine ⟨⟨y, mem_nonZeroDivisors_of_ne_zero hy0⟩, ?_⟩
      rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_comap]
      have hint : ∀ a, IsIntegral ℤ (y • c a) := fun a =>
        hy _ (Finset.mem_image_of_mem c (Finset.mem_univ a))
      have hsum : y • v = ∑ a, (⟨y • c a, hint a⟩ : 𝓞 E) • w a := by
        rw [← hc, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ext i
        change _ = ((⟨y • c a, hint a⟩ : 𝓞 E) : E) * w a i
        simp [zsmul_eq_mul, mul_assoc]
      change y • v ∈ N
      rw [hsum]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  haveI : Finite (M ⧸ N.comap M.subtype) := Module.finite_of_fg_torsion _ htors
  exact AddSubgroup.index_ne_zero_of_finite (hH := this)

end GlobalTheory.SpanIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RmulOneFrame
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ProperDiscontinuity

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def oneFrame (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Frame Ψ r :=
  fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)

omit [NumberField E] [IsCMField E] in
theorem mat_oneFrame (Ψ : Finset (E →+* ℂ)) (r : ℕ) (τ : Ψ) : mat (oneFrame Ψ r) τ = 1 := rfl

omit [NumberField E] [IsCMField E] in
theorem oneFrame_mem (Ψ : Finset (E →+* ℂ)) (r : ℕ) : oneFrame Ψ r ∈ Bor Ψ r := by
  intro τ
  refine ⟨by rw [mat_oneFrame]; simp, fun a c h => ?_⟩
  exact Matrix.one_apply_ne (ne_of_gt h)

omit [NumberField E] [IsCMField E] in
theorem rmul_oneFrame {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : Frame Ψ r) :
    rmul x (oneFrame Ψ r) = x := by
  funext τ
  show mat x τ * mat (oneFrame Ψ r) τ = _
  rw [mat_oneFrame, Matrix.mul_one]
  rfl

omit [NumberField E] [IsCMField E] in
theorem lact_one {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : Frame Ψ r) :
    lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = _
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rfl

theorem propDisc :
    (∀ (r : ℕ) (X : Data E r) (γ : GL (Fin r) E), IsUStab X.Gm X.Λ γ → ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj (lact γ (rmul x b)) τ (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ.1) v) = X.maj x τ v) → (∀ (r : ℕ) (X : Data E r) (K : Set (Frame X.Ψ r)), IsCompact K → K ⊆ X.dom → ∃ c C : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ (τ : X.Ψ) (v : Fin r → ℂ), c * ‖v‖ ^ 2 ≤ X.maj x τ v ∧ X.maj x τ v ≤ C * ‖v‖ ^ 2) → (∀ (r : ℕ) (X : Data E r) (R : ℝ), {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r), ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ R}.Finite) → (∀ (r : ℕ) (X : Data E r), PropDisc X) := by
  intro hinv hbd hfin r X x hx x' hx'
  have hO := FourierCoefficientDomain.isOpen_dom X
  obtain ⟨K, hK, hKd, hKc⟩ := local_compact_nhds (hO.mem_nhds hx)
  obtain ⟨K', hK', hKd', hKc'⟩ := local_compact_nhds (hO.mem_nhds hx')
  obtain ⟨c, C, hc, hb⟩ := hbd r X (K ∪ K') (hKc.union hKc') (Set.union_subset hKd hKd')
  refine ⟨K, hK, K', hK', (hfin r X (Real.sqrt (C / c))).subset ?_⟩
  rintro γ ⟨hγ, u, hu, u', hu', b, hbB, he⟩
  refine ⟨X.Γ_stab γ hγ, fun τ i j => ?_⟩
  set M : Matrix (Fin r) (Fin r) ℂ := (γ : Matrix (Fin r) (Fin r) E).map τ.1 with hM
  set v : Fin r → ℂ := Pi.single j 1 with hv
  have h1 := (hinv r X γ (X.Γ_stab γ hγ) u (hKd hu) _ (oneFrame_mem X.Ψ r)).2 τ v
  rw [rmul_oneFrame, he] at h1
  have h2 := (hinv r X 1 (X.Γ_stab 1 X.Γ.one_mem) u' (hKd' hu') b hbB).2 τ (M.mulVec v)
  rw [lact_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec] at h2
  have h3 := (hb u' (Or.inr hu') τ (M.mulVec v)).1
  have h4 := (hb u (Or.inl hu) τ v).2
  have hv1 : ‖v‖ = 1 := by rw [hv, Pi.norm_single, norm_one]
  rw [hv1] at h4
  have h5 : c * ‖M.mulVec v‖ ^ 2 ≤ C := by
    have : X.maj u' τ (M.mulVec v) = X.maj u τ v := h2.symm.trans h1
    linarith
  have h6 : ‖M.mulVec v‖ ≤ Real.sqrt (C / c) := by
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hc]
    linarith
  have h7 : M.mulVec v i = τ.1 ((γ : Matrix (Fin r) (Fin r) E) i j) := by
    simp [hv, hM]
  rw [← h7]
  exact (norm_le_pi_norm _ i).trans h6

end GlobalTheory.ProperDiscontinuity
end

