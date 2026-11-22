import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetInequalitiesClosedFormsStatement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfFiniteCovolume

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetFderivNeZeroOrbit
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.OrbitCoord

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in

theorem rmul_left_cancel {r : ℕ} {Ψ : Finset (E →+* ℂ)} {o a c : Frame Ψ r}
    (ho : ∀ τ, (mat o τ).det ≠ 0) (h : rmul o a = rmul o c) : a = c := by
  funext τ
  have h1 : mat o τ * mat a τ = mat o τ * mat c τ := congrFun h τ
  have hu : IsUnit (mat o τ) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (ho τ))
  exact hu.mul_left_cancel h1

theorem exists_swap {r : ℕ} (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    ∃ (U : Set (V (nd X))) (Φ : V (nd X) → V (nd X)) (bf : V (nd X) → Frame X.Ψ r),
      IsOpen U ∧ 0 ∈ U ∧ DifferentiableOn ℂ Φ U ∧ Φ 0 = 0 ∧
      ∀ z ∈ U, bf z ∈ Bor X.Ψ r ∧ rmul b (nmat X z) = rmul (nmat X (Φ z)) (bf z) := by
  have ho : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
  have hod : x0F X ∈ X.dom := IW.orth_mem_dom X _ ho
  obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hsplit, huniq⟩ := lu_holds r X (x0F X) ho
  have hcd := OntoB.cd_cpt X (rmul (x0F X) b)
  have h0 := huniq 0 (IW.zero_mem_OmF X _ ho) b hb
  rw [IW.cpt_zero] at h0
  refine ⟨cpt X (rmul (x0F X) b) ⁻¹' {x | x ∈ X.dom ∧ Δ x ≠ 0},
    fun z => zOf (cpt X (rmul (x0F X) b) z), fun z => bOf (cpt X (rmul (x0F X) b) z), ?_, ?_, ?_, ?_, ?_⟩
  · exact ((FourierCoefficientDomain.isOpen_dom X).inter
      (isOpen_ne_fun hΔ.continuous continuous_const)).preimage hcd.continuous
  · show cpt X _ 0 ∈ X.dom ∧ Δ (cpt X _ 0) ≠ 0
    rw [IW.cpt_zero]
    exact ⟨OntoS.dom_rmul X hod hb, h0.1⟩
  · exact hz.comp (hcd.differentiable (by simp)).differentiableOn fun _ h => h
  · show zOf (cpt X _ 0) = 0
    rw [IW.cpt_zero]
    exact h0.2.1
  · intro z hzU
    obtain ⟨-, h2, h3⟩ := hsplit _ hzU.1 hzU.2
    refine ⟨h2, rmul_left_cancel (fun τ => (hod τ).1) ?_⟩
    rw [← ExtFPf.rmul_assoc, ← ExtFPf.rmul_assoc]
    exact h3

theorem det_fderiv_ne_zero_orbit : (KapGGStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ), X.IsSec L w0 → (∀ k, X.IsSec L (s k)) → ∀ x ∈ X.dom, w0 x ≠ 0 → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (x) z) / w0 (cpt X (x) z) : V (nd X))) 0).det ≠ 0 → ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (lact γ (rmul x b)) z) / w0 (cpt X (lact γ (rmul x b)) z) : V (nd X))) 0).det ≠ 0) := by
  intro hK r X L w0 s hw0 hs x hx hwx hdet γ hγ b hb
  obtain ⟨U, Φ, bf, hU, h0U, hΦ, hΦ0, hsw⟩ := exists_swap X hb
  set y := lact γ (rmul x b) with hy
  have hyd : y ∈ X.dom := OntoS.dom_lact X hγ (OntoS.dom_rmul X hx hb)
  have hcpt : ∀ z ∈ U, cpt X y z = lact γ (rmul (cpt X x (Φ z)) (bf z)) := by
    intro z hz
    unfold cpt
    rw [hy, ← FundSetPf.lact_rmul, ExtFPf.rmul_assoc, (hsw z hz).2, ExtFPf.rmul_assoc]
  have h0y : (0 : V (nd X)) ∈ OmF X y := by
    show cpt X y 0 ∈ X.dom
    rwa [IW.cpt_zero]
  have h0x : (0 : V (nd X)) ∈ OmF X x := by
    show cpt X x 0 ∈ X.dom
    rwa [IW.cpt_zero]
  have hJ : (fderiv ℂ Φ 0).det = bchar (kapW X) (bf 0) :=
    hK r X y x γ (U ∩ OmF X y) Φ bf (hU.inter (OntoB.isOpen_OmF X y)) (hΦ.mono Set.inter_subset_left)
      (fun z hz => ⟨hz.2, (hsw z hz.1).1, hcpt z hz.1⟩) 0 ⟨h0U, h0y⟩
  have hJ0 : (fderiv ℂ Φ 0).det ≠ 0 := hJ ▸ OntoE.bchar_ne X _ (hsw 0 h0U).1
  have hΦd : DifferentiableAt ℂ Φ 0 := hΦ.differentiableAt (hU.mem_nhds h0U)
  have hnx : OmF X x ∈ 𝓝 (0 : V (nd X)) := (OntoB.isOpen_OmF X x).mem_nhds h0x
  set F : V (nd X) → V (nd X) := fun z : V (nd X) =>
    (WithLp.toLp 2 fun k => s k (cpt X (x) z) / w0 (cpt X (x) z) : V (nd X)) with hF
  have hFd : DifferentiableAt ℂ F 0 := by
    have hw : DifferentiableAt ℂ (fun z => w0 (cpt X x z)) 0 :=
      (OntoB.hol_comp X x hw0.1).differentiableAt hnx
    have hsk : ∀ k, DifferentiableAt ℂ (fun z => s k (cpt X x z)) 0 := fun k =>
      (OntoB.hol_comp X x (hs k).1).differentiableAt hnx
    rw [hF]
    refine (differentiableAt_piLp 2).2 fun k => ?_
    have hne : w0 (cpt X x 0) ≠ 0 := by rwa [IW.cpt_zero]
    have := (hsk k).mul (hw.inv hne)
    simp only [div_eq_mul_inv]
    exact this
  have hev : (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      s k (cpt X y z) / w0 (cpt X y z) : V (nd X))) =ᶠ[𝓝 0] F ∘ Φ := by
    have h1 : ∀ᶠ z in 𝓝 (0 : V (nd X)), Φ z ∈ OmF X x :=
      hΦd.continuousAt.preimage_mem_nhds (by rwa [hΦ0])
    filter_upwards [hU.mem_nhds h0U, h1] with z hz hzx
    have hzx' : cpt X x (Φ z) ∈ X.dom := hzx
    have hbz := (hsw z hz).1
    have hd := OntoS.dom_rmul X hzx' hbz
    have hχ : X.χ L γ ≠ 0 := by
      intro h
      have := OntoE.chi_norm X L hγ
      rw [h, norm_zero] at this
      exact zero_ne_one this
    show _ = F (Φ z)
    rw [hF]
    show (WithLp.toLp 2 _ : V (nd X)) = WithLp.toLp 2 _
    congr 1
    funext k
    rw [hcpt z hz, (hs k).2.2 γ hγ _ hd, hw0.2.2 γ hγ _ hd, mul_div_mul_left _ _ hχ,
      (hs k).2.1 _ hzx' _ hbz, hw0.2.1 _ hzx' _ hbz, mul_div_mul_left _ _ (OntoE.bchar_ne X L hbz)]
  rw [hev.fderiv_eq, fderiv_comp 0 (by rwa [hΦ0]) hΦd, hΦ0]
  have : ((fderiv ℂ F 0).comp (fderiv ℂ Φ 0)).det = (fderiv ℂ F 0).det * (fderiv ℂ Φ 0).det := by
    unfold ContinuousLinearMap.det
    rw [← LinearMap.det_comp]
    rfl
  rw [this]
  exact mul_ne_zero hdet hJ0

end GlobalTheory.OrbitCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DminCptEq
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.OrthNear

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.OrthNear.isOrth_x0F {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.x0F X) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.x0F _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth
  intro τ
  generalize_proofs h
  exact (h τ).choose_spec.2

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem mat_cpt_eq_mat_mul_mat_nmat {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X z) τ := rfl

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem gram_mul_apply_eq_sum {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M N : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G (M * N) = Matrix.of fun a b =>
      ∑ c, ∑ d, N c a * _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G M c d * starRingEnd ℂ (N d b) := by
  have hcol : ∀ a, _root_.ReciprocityTheory.ChartRestriction.G.FD.col (M * N) a = ∑ c, N c a • _root_.ReciprocityTheory.ChartRestriction.G.FD.col M c := by
    intro a
    rw [← _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.mulVec_eq_sum_col]
    ext k
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  ext a b
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, hcol, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_left, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_sum_right, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_left, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem gram_chartCoord_orthonormal_indep_lemma {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y)
    (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) τ) := by
  have hx' : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ) :=
    (hx τ).trans (hy τ).symm
  rw [mat_cpt_eq_mat_mul_mat_nmat, mat_cpt_eq_mat_mul_mat_nmat, gram_mul_apply_eq_sum, gram_mul_apply_eq_sum, hx']

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.OrthNear.dmin_cpt_eq {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y)
    (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (τ : X.Ψ) (i : Fin (r + 1)) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ i = _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) τ i := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin, gram_chartCoord_orthonormal_indep_lemma X hx hy z τ]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem densF_eq_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x z = _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X y z := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF, _root_.GlobalTheory.OrthNear.dmin_cpt_eq X hx hy z]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem nfac_cpt_eq_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) :
    X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.nfac, _root_.GlobalTheory.OrthNear.dmin_cpt_eq X hx hy z]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem cpt_mem_dom_iff_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom ↔ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z ∈ X.dom := by
  have hdet : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) τ).det ≠ 0 ↔
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X y z) τ).det ≠ 0 := by
    intro τ
    rw [mat_cpt_eq_mat_mul_mat_nmat, mat_cpt_eq_mat_mul_mat_nmat, Matrix.det_mul, Matrix.det_mul]
    simp [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.det_ne_of_orth X hx τ, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.det_ne_of_orth X hy τ]
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom, _root_.ReciprocityTheory.ChartRestriction.G.FD.GG, Set.mem_setOf_eq, hdet,
    _root_.GlobalTheory.OrthNear.dmin_cpt_eq X hx hy z]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.OrthNear.orthNear : (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r), ∃ ρ c C : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ x, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ∀ z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ < ρ → _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom ∧ c ≤ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x z ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x z ≤ C ∧ c ≤ X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∧ X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ≤ C) := by
  intro r X la
  set x0 := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.x0F X
  have h0 : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 := _root_.GlobalTheory.OrthNear.isOrth_x0F X
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.isOpen_iff.mp (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExF.isOpen_OmF X x0) 0 (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IW.zero_mem_OmF X x0 h0)
  set K := Metric.closedBall (0 : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (ρ0 / 2)
  have hKsub : K ⊆ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0 :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKne : K.Nonempty := ⟨0, Metric.mem_closedBall_self (by linarith)⟩
  have hd : ContinuousOn (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x0) K := (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.densF_continuousOn (X := X) (x0 := x0)).mono hKsub
  have hn : ContinuousOn (fun z => X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) K :=
    (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.nfac_cont X x0 la).mono hKsub
  obtain ⟨z1, hz1, hmin1⟩ := hK.exists_isMinOn hKne hd
  obtain ⟨z2, hz2, hmin2⟩ := hK.exists_isMinOn hKne hn
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn hd
  obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn hn
  refine ⟨ρ0 / 2, min (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.densF X x0 z1) (X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z2)), max C1 C2,
    by linarith, lt_min (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.densF_pos (hKsub hz1)) (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.nfac_pos X x0 (hKsub hz2)), ?_⟩
  intro x hx z hz
  have hzK : z ∈ K := Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hz.le)
  have hdom : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z ∈ X.dom := hKsub hzK
  rw [densF_eq_of_isOrth X hx h0, nfac_cpt_eq_of_isOrth X hx h0,
    cpt_mem_dom_iff_of_isOrth X hx h0]
  exact ⟨hdom, (min_le_left _ _).trans (isMinOn_iff.mp hmin1 z hzK),
    (Real.le_norm_self _).trans ((hC1 z hzK).trans (le_max_left _ _)),
    (min_le_right _ _).trans (isMinOn_iff.mp hmin2 z hzK),
    (Real.le_norm_self _).trans ((hC2 z hzK).trans (le_max_right _ _))⟩

end GlobalTheory.OrthNear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBoundOrthonormalFrameMahler
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.OrthFrameMahler

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuousOn_rmul_self {Ψ : Finset (E →+* ℂ)} {r : ℕ} {β : Frame Ψ r → Frame Ψ r}
    {K : Set (Frame Ψ r)} (hβ : ContinuousOn β K) : ContinuousOn (fun y => rmul y (β y)) K := by
  refine continuousOn_pi.2 fun τ => continuousOn_pi.2 fun a => continuousOn_pi.2 fun c => ?_
  show ContinuousOn (fun y : Frame Ψ r => ∑ k, y τ a k * β y τ k c) K
  refine continuousOn_finset_sum _ fun k _ => ContinuousOn.mul (by fun_prop) ?_
  exact continuousOn_pi.1 (continuousOn_pi.1 (continuousOn_pi.1 hβ τ) k) c

theorem norm_apply_le_of_diagonal {Ψ : Finset (E →+* ℂ)} {r : ℕ} (z t : Frame Ψ r)
    (hdiag : ∀ τ a, ‖t τ a a‖ = 1 ∧ ∀ c, c ≠ a → t τ a c = 0) (τ : Ψ) (a c : Fin r) :
    ‖z τ a c‖ ≤ ‖rmul z t‖ := by
  have h1 : rmul z t τ a c = z τ a c * t τ c c := by
    show ∑ k, z τ a k * t τ k c = _
    refine Finset.sum_eq_single c (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ c) h)
    rw [(hdiag τ k).2 c (Ne.symm hk), mul_zero]
  calc ‖z τ a c‖ = ‖rmul z t τ a c‖ := by
        rw [h1, norm_mul, (hdiag τ c).1, mul_one]
    _ ≤ ‖rmul z t τ a‖ := norm_le_pi_norm _ c
    _ ≤ ‖rmul z t τ‖ := norm_le_pi_norm _ a
    _ ≤ ‖rmul z t‖ := norm_le_pi_norm _ τ

theorem exists_bound_orthonormal_frame :
    (∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x, IsOrth X x → ε ≤ X.la1 x →
      ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ a b, ‖lact γ x τ a b‖ ≤ R) := by
  intro r X ε hε
  obtain ⟨K, hKc, hKd, hK⟩ := GlobalTheory.FlagMahler.mahler_compactness (E := E) r X ε hε
  obtain ⟨β, hβc, hβ⟩ := GlobalTheory.GramSchmidtCont.exists_continuous_gramSchmidt (E := E) r X
  obtain ⟨R, hR⟩ := hKc.exists_bound_of_continuousOn (continuousOn_rmul_self (hβc.mono hKd))
  refine ⟨R, fun x hx hla => ?_⟩
  obtain ⟨γ, hγ, b, hb, hy⟩ := hK x (IW.orth_mem_dom X x hx) hla
  refine ⟨γ, X.Γ_stab γ hγ, fun τ a c => ?_⟩
  obtain ⟨hβb, hβo⟩ := hβ _ (hKd hy)
  have hRy : ‖rmul (lact γ (rmul x b)) (β (lact γ (rmul x b)))‖ ≤ R := hR _ hy
  generalize β (lact γ (rmul x b)) = s at hβb hβo hRy
  rw [FundSetPf.lact_rmul, ExtFPf.rmul_assoc] at hβo hRy
  have hγo : IsOrth X (lact γ x) := fun σ => by rw [OntoS.gram_lact X hγ]; exact hx σ
  have hdiag := (GlobalTheory.isOrth_rmul_iff_unitary_diagonal r X _ _ hγo (ExtFPf.mul_mem X hb hβb)).1 hβo
  exact (norm_apply_le_of_diagonal _ _ hdiag τ a c).trans hRy

end GlobalTheory.OrthFrameMahler
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDriftFunctionRealUnitaryGroup
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.DriftUnitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma cmType_nonempty {r : ℕ} (X : Data E r) : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · refine ⟨⟨ComplexEmbedding.conjugate τ, ?_⟩⟩
    by_contra h'
    exact h ((X.cmType τ).2 h')

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.DriftUnitary.continuous_orbit {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ))
    (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    Continuous fun g : H => X.lmulC
      (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.lmulC
  refine continuous_pi fun τ => ?_
  exact (Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)).matrix_mul
    continuous_const

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem single_one_mulVec_eq_pi_single (r : ℕ) (j k : Fin r) (w : Fin r → ℂ) :
    (Matrix.single j k (1 : ℂ)).mulVec w = Pi.single j (w k) := by
  ext i
  by_cases hi : i = j
  · subst hi; simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, hi, Ne.symm hi]

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem eq_bot_or_eq_whole_of_single_mulVec_invariant (r p : ℕ) (hp : 0 < p) (hpr : p < r)
    (W : Submodule ℂ (Fin r → ℂ))
    (hW : ∀ (j k : Fin r), (j : ℕ) < p → p ≤ (k : ℕ) → ∀ v ∈ W,
      (Matrix.single j k 1).mulVec v ∈ W ∧ (Matrix.single k j 1).mulVec v ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨m, hm⟩ : ∃ m, v m ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 (funext h)
  have hsmul : ∀ (i : Fin r) (z : ℂ), z ≠ 0 → Pi.single i z ∈ W → Pi.single i (1 : ℂ) ∈ W := by
    intro i z hz h
    have e : z⁻¹ • (Pi.single i z : Fin r → ℂ) = Pi.single i 1 := by
      ext l
      by_cases hl : l = i <;> simp [hl, hz]
    rw [← e]
    exact W.smul_mem _ h
  let j0 : Fin r := ⟨0, by omega⟩
  let k0 : Fin r := ⟨p, hpr⟩
  have hj0 : (j0 : ℕ) < p := hp
  have hk0' : p ≤ (k0 : ℕ) := le_rfl
  have hk0 : Pi.single k0 (1 : ℂ) ∈ W := by
    rcases Nat.lt_or_ge (m : ℕ) p with h | h
    · have h1 := (hW m k0 h hk0' v hvW).2
      rw [single_one_mulVec_eq_pi_single] at h1
      exact hsmul _ _ hm h1
    · have h1 := (hW j0 m hj0 h v hvW).1
      rw [single_one_mulVec_eq_pi_single] at h1
      have h3 := (hW j0 k0 hj0 hk0' _ (hsmul _ _ hm h1)).2
      rw [single_one_mulVec_eq_pi_single] at h3
      simpa using h3
  have he0 : Pi.single j0 (1 : ℂ) ∈ W := by
    have h1 := (hW j0 k0 hj0 hk0' _ hk0).1
    rw [single_one_mulVec_eq_pi_single] at h1
    simpa using h1
  have hall : ∀ i : Fin r, Pi.single i (1 : ℂ) ∈ W := by
    intro i
    rcases Nat.lt_or_ge (i : ℕ) p with h | h
    · have h1 := (hW i k0 h hk0' _ hk0).1
      rw [single_one_mulVec_eq_pi_single] at h1
      simpa using h1
    · have h1 := (hW j0 i hj0 h _ he0).2
      rw [single_one_mulVec_eq_pi_single] at h1
      simpa using h1
  rw [eq_top_iff]
  intro w _
  have hw : w = ∑ i, w i • (Pi.single i (1 : ℂ) : Fin r → ℂ) := by
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hw]
  exact Submodule.sum_mem _ fun i _ => W.smul_mem _ (hall i)

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.DriftUnitary.exists_drift_function :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H], 0 < X.p0 → X.p0 < r → ∀ x0, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ∃ (σ : Type) (_ : Fintype σ) (_ : Nonempty σ) (h : σ → H) (f : H → ℝ) (c b : ℝ), (∀ s, ∃ k : H, k * h s = (h s)⁻¹ * k) ∧ Measurable f ∧ (∀ g, 0 ≤ f g) ∧ (∀ u : H, (∃ γ : GL (Fin r) E, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) → ∀ g, f (u * g) = f g) ∧ 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ (∀ g, ∑ s, f (g * h s) ≤ Fintype.card σ * (c * f g + b)) ∧ ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ g : H, f g ≤ M → ε ≤ X.la1 (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) := by
  intro r X H hH _ _ hp0 hpr x0 hx0
  obtain ⟨S, hSne, hS1, hS2, hS3⟩ := _root_.GlobalTheory.exists_finite_symmetric_irreducible_rotations
    eq_bot_or_eq_whole_of_single_mulVec_invariant r X.p0 hp0 hpr
  obtain ⟨τ0⟩ := _root_.GlobalTheory.LineHeight.nonempty_cmType X
  obtain ⟨f, c, b, hc0, hc1, hb, hlsc, hf0, hfinv, hdrift, hla⟩ :=
    _root_.GlobalTheory.exists_drift_function_orthFrames r X hp0 hpr τ0 S hS1 hS2 (fun a ha => (hS3 a ha).1)
  have horb := (((_root_.GlobalTheory.UnitaryFrames.unitary_group_frames (E := E)).2 r X H hH).2.2 x0 hx0).1
  have hstep := fun a : S => _root_.GlobalTheory.UnitaryLift.step_of_right_mul r X H hH x0 hx0 τ0 a.1
    (hS3 a.1 a.2).2.choose (hS3 a.1 a.2).1 (hS3 a.1 a.2).2.choose_spec.1 (hS3 a.1 a.2).2.choose_spec.2
  choose hS kS hkS hupd using hstep
  refine ⟨S, inferInstance, hSne.to_subtype, hS,
    fun g => f (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0), c, b,
    fun s => ⟨kS s, hkS s⟩, ?_, fun g => hf0 _ (horb g), ?_, hc0, hc1, hb, ?_, ?_⟩
  · have hcont := _root_.GlobalTheory.DriftUnitary.continuous_orbit X H x0
    have hl : LowerSemicontinuous fun g : H =>
        f (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) := by
      intro g y hy
      have ht : Filter.Tendsto (fun g : H =>
          X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) (𝓝 g)
          (𝓝[{x | _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x}] (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) :=
        tendsto_nhdsWithin_iff.2 ⟨hcont.tendsto g, Filter.Eventually.of_forall fun g' => show _ ∈ {x | _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x} from horb g'⟩
      exact ht.eventually (hlsc _ (horb g) y hy)
    exact hl.measurable
  · rintro u ⟨γ, hγ, hu⟩ g
    have e : X.lmulC (fun τ => (((u * g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0 =
        _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) := by
      funext τ
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.lmulC, _root_.ReciprocityTheory.ChartRestriction.G.FD.lact, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat, Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, hu τ,
        Matrix.mul_assoc]
      rfl
    show f _ = f _
    rw [e]
    exact hfinv γ hγ _ (horb g)
  · intro g
    simp only [hupd, Fintype.card_coe]
    exact (Finset.sum_coe_sort S _).trans_le (hdrift _ (horb g))
  · intro M
    obtain ⟨ε, hε, h⟩ := hla M
    exact ⟨ε, hε, fun g hg => h _ (horb g) hg⟩

end GlobalTheory.DriftUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStabiliserImageSubgroup
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def uStabSubgroup {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    Subgroup (GL (Fin r) E) where
  carrier := {γ | IsUStab G Λ γ}
  one_mem' := by simp [IsUStab]
  mul_mem' := fun {γ δ} hγ hδ => by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hγ.1, hδ.1]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hγ.2, ← hδ.2]
  inv_mem' := fun h => isUStab_inv h

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.FiniteCovolume.exists_stabiliser_image_subgroup :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∃ Γ : Subgroup H, ∀ g : H, g ∈ Γ ↔ (∃ γ : GL (Fin r) E, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1)) := by
  intro r X H _
  refine ⟨((_root_.GlobalTheory.FiniteCovolume.uStabSubgroup X.Gm X.Λ).map (_root_.GlobalTheory.FiniteCovolume.embGL X.Ψ)).comap
    H.subtype, fun g => ?_⟩
  simp only [Subgroup.mem_comap, Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  · rintro ⟨γ, hγ, hg⟩
    refine ⟨γ, hγ, fun τ => ?_⟩
    rw [← hg, _root_.GlobalTheory.FiniteCovolume.embGL_val]
  · rintro ⟨γ, hγ, hg⟩
    refine ⟨γ, hγ, funext fun τ => Units.ext ?_⟩
    rw [_root_.GlobalTheory.FiniteCovolume.embGL_val, hg]

end GlobalTheory.FiniteCovolume
end

