import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0020
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsLeNormDev
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.GrpSep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable def dev {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : Frame Ψ r) (γ : GL (Fin r) E) :
    Frame Ψ r :=
  fun τ => ((mat x0 τ)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x0 τ - 1 :
    Matrix (Fin r) (Fin r) ℂ)

noncomputable def shift {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 M : Frame Ψ r) : Frame Ψ r :=
  fun τ => (mat x0 τ * (mat M τ + 1) : Matrix (Fin r) (Fin r) ℂ)

noncomputable def oneF (Ψ : Finset (E →+* ℂ)) (r : ℕ) : Frame Ψ r :=
  fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)

omit [NumberField E] [IsCMField E] in
theorem oneF_mem (Ψ : Finset (E →+* ℂ)) (r : ℕ) : oneF Ψ r ∈ Bor Ψ r := by
  intro τ
  refine ⟨?_, fun a c h => ?_⟩
  · change (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp
  · exact Matrix.one_apply_ne h.ne'

omit [NumberField E] [IsCMField E] in
theorem rmul_oneF {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : Frame Ψ r) : rmul x (oneF Ψ r) = x := by
  funext τ
  change mat x τ * (1 : Matrix (Fin r) (Fin r) ℂ) = mat x τ
  exact Matrix.mul_one _

end GlobalTheory.GrpSep

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma sgn_ne_zero_torus_haar_measure (p a : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn p a ≠ 0 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn; split_ifs <;> norm_num

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma det_mat_ne_zero_of_isOrth' {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (h : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) (τ : X.Ψ) : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ).det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det (h τ)
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at this
  exact (Finset.prod_ne_zero_iff.mpr fun a _ => by exact_mod_cast sgn_ne_zero_torus_haar_measure X.p0 a) this.symm

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma mem_dom_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (h : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) : x0 ∈ X.dom := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG
  refine fun τ => ⟨det_mat_ne_zero_of_isOrth' X h τ, fun i => ?_⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor
  rw [h τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
  simp only [Function.comp_apply, Fin.coe_castLE]
  rw [← Complex.ofReal_prod, Complex.ofReal_re,
    Fin.prod_univ_eq_prod_range (fun j => _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j) i]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn
  exact mul_self_pos.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => sgn_ne_zero_torus_haar_measure X.p0 a)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma continuous_shift' {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    Continuous (fun M : Ψ → Fin r → Fin r → ℂ =>
      (_root_.GlobalTheory.GrpSep.shift x0 M : Ψ → Fin r → Fin r → ℂ)) := by
  unfold _root_.GlobalTheory.GrpSep.shift _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
  refine continuous_pi fun τ => ?_
  exact continuous_const.matrix_mul ((continuous_apply τ).add continuous_const)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma shift_zero_torus_haar_measure {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    _root_.GlobalTheory.GrpSep.shift x0 0 = x0 := by
  funext τ
  change _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ * (0 + 1) = x0 τ
  rw [zero_add, Matrix.mul_one]; rfl

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exists_pos_le_of_finite_pos {α : Type*} (S : Set α) (hS : S.Finite) (f : α → ℝ)
    (hf : ∀ a ∈ S, 0 < f a) : ∃ δ > 0, ∀ a ∈ S, δ ≤ f a := by
  rcases S.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨a0, ha0, hmin⟩ := Set.exists_min_image S f hS h
    exact ⟨f a0, hf a0 ha0, hmin⟩

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma oneF_mem_bor {Ψ : Finset (E →+* ℂ)} {r : ℕ} :
    _root_.GlobalTheory.GrpSep.oneF Ψ r ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor
  refine fun τ => ⟨?_, fun a c h => ?_⟩
  · change (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp
  · change (1 : Matrix (Fin r) (Fin r) ℂ) a c = 0
    exact Matrix.one_apply_ne h.ne'

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma shift_dev_eq_lact {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r)
    (hdet : ∀ τ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ).det ≠ 0) (γ : GL (Fin r) E) :
    _root_.GlobalTheory.GrpSep.shift x0 (_root_.GlobalTheory.GrpSep.dev x0 γ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x0 := by
  funext τ
  change _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
    _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ - 1 + 1) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ
  rw [sub_add_cancel, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (Ne.isUnit (hdet τ)), Matrix.one_mul]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma rmul_oneF' {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x0 (_root_.GlobalTheory.GrpSep.oneF Ψ r) = x0 := by
  funext τ
  change (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ * 1 : Matrix (Fin r) (Fin r) ℂ) = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ
  exact Matrix.mul_one _

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.grpSep : ∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r),
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc X →
    ∃ c : ℝ, 0 < c ∧ ∀ γ ∈ X.Γ, γ ≠ 1 → ∃ (τ : X.Ψ) (a b : Fin r),
      c ≤ ‖((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ)⁻¹ * (γ : Matrix (Fin r) (Fin r) E).map τ.1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ - 1) a b‖ := by
  intro r X x0 hO hP
  have hdom := mem_dom_of_isOrth X hO
  have hdet := det_mat_ne_zero_of_isOrth' X hO
  obtain ⟨U, hU, U', hU', hfin⟩ := hP x0 hdom x0 hdom
  have hV : (fun M : X.Ψ → Fin r → Fin r → ℂ =>
      (_root_.GlobalTheory.GrpSep.shift x0 M : X.Ψ → Fin r → Fin r → ℂ)) ⁻¹' U' ∈
      nhds (0 : X.Ψ → Fin r → Fin r → ℂ) :=
    (continuous_shift' x0).continuousAt.preimage_mem_nhds (by erw [shift_zero_torus_haar_measure]; exact hU')
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨δ, hδ, hmin⟩ := exists_pos_le_of_finite_pos _ (hfin.subset Set.diff_subset)
    (fun γ => ‖(_root_.GlobalTheory.GrpSep.dev x0 γ : X.Ψ → Fin r → Fin r → ℂ)‖) (by
      rintro γ ⟨hγ, h1⟩
      refine norm_pos_iff.mpr fun h0 => h1 ?_
      refine X.Γ_free γ hγ.1 x0 hdom (_root_.GlobalTheory.GrpSep.oneF X.Ψ r) oneF_mem_bor ?_
      rw [← shift_dev_eq_lact x0 hdet, rmul_oneF']
      exact (congrArg (_root_.GlobalTheory.GrpSep.shift x0) h0).trans (shift_zero_torus_haar_measure x0))
  refine ⟨min ε δ, lt_min hε hδ, fun γ hγ h1 => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hlt : ‖(_root_.GlobalTheory.GrpSep.dev x0 γ : X.Ψ → Fin r → Fin r → ℂ)‖ < min ε δ := by
    refine (pi_norm_lt_iff (lt_min hε hδ)).mpr fun τ => (pi_norm_lt_iff (lt_min hε hδ)).mpr
      fun a => (pi_norm_lt_iff (lt_min hε hδ)).mpr fun b => hcon τ a b
  have hmem : _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x0 ∈ U' := by
    rw [← shift_dev_eq_lact x0 hdet]
    exact hball (mem_ball_zero_iff.mpr (hlt.trans_le (min_le_left _ _)))
  have hS := hmin γ ⟨⟨hγ, x0, mem_of_mem_nhds hU, _, hmem, _root_.GlobalTheory.GrpSep.oneF X.Ψ r,
    oneF_mem_bor, (rmul_oneF' _).symm⟩, h1⟩
  exact absurd hS (not_le.mpr (hlt.trans_le (min_le_right _ _)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsOpenSaturation
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.SatOpen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_lact {r : ℕ} {Ψ : Finset (E →+* ℂ)} (δ : GL (Fin r) E) :
    Continuous (lact δ : Frame Ψ r → Frame Ψ r) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  simp only [lact, mat, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem isOpen_cell {r : ℕ} (X : Data E r) {x1 : Frame X.Ψ r} (ho : IsOrth X x1)
    {N : Set (V (nd X))} (hN : IsOpen N) (hNO : N ⊆ OmF X x1) :
    IsOpen {x | ∃ y ∈ N, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x1 y) b} := by
  obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hsplit, huniq⟩ := lu_holds r X x1 ho
  have hU : IsOpen {x | x ∈ X.dom ∧ Δ x ≠ 0} :=
    (FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
  have heq : {x | ∃ y ∈ N, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x1 y) b} =
      {x | x ∈ X.dom ∧ Δ x ≠ 0} ∩ zOf ⁻¹' N := by
    ext x
    constructor
    · rintro ⟨y, hy, b, hb, rfl⟩
      obtain ⟨h1, h2, -⟩ := huniq y (hNO hy) b hb
      refine ⟨⟨OntoS.dom_rmul X (hNO hy) hb, h1⟩, ?_⟩
      rw [Set.mem_preimage, h2]
      exact hy
    · rintro ⟨⟨hx, hd⟩, hzN⟩
      obtain ⟨-, h2, h3⟩ := hsplit x hx hd
      exact ⟨zOf x, hzN, bOf x, h2, h3⟩
  rw [heq]
  exact hz.continuousOn.isOpen_inter_preimage hU hN

theorem isOpen_saturation : ∀ (r : ℕ) (X : Data E r) (x1 : Frame X.Ψ r), IsOrth X x1 →
    ∀ N : Set (V (nd X)), IsOpen N → N ⊆ OmF X x1 →
    IsOpen {x | ∃ y ∈ N, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (cpt X x1 y) b)} := by
  intro r X x1 ho N hN hNO
  have heq : {x | ∃ y ∈ N, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (cpt X x1 y) b)} =
      ⋃ γ ∈ X.Γ, lact γ⁻¹ ⁻¹' {x | ∃ y ∈ N, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x1 y) b} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, γ, hγ, b, hb, rfl⟩
      exact ⟨γ, hγ, y, hy, b, hb, FundSetPf.lact_inv _ _⟩
    · rintro ⟨γ, hγ, y, hy, b, hb, h⟩
      refine ⟨y, hy, γ, hγ, b, hb, ?_⟩
      rw [← h, ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one]
  rw [heq]
  exact isOpen_biUnion fun γ _ => (isOpen_cell X ho hN hNO).preimage (continuous_lact _)

end GlobalTheory.SatOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsomOfGramEq
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate

namespace GlobalTheory.MajNear

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
theorem hermC_mulVec {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r → ℂ) :
    hermC τ G (M *ᵥ a) (M *ᵥ b) = ∑ i, ∑ j, a i * gram τ G M i j * conj (b j) := by
  simp only [hermC, gram, col, Matrix.of_apply, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  have h : ∀ (f : Fin r → Fin r → Fin r → Fin r → ℂ),
      ∑ k, ∑ l, ∑ j, ∑ i, f k l i j = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := by
    intro f
    calc ∑ k, ∑ l, ∑ j, ∑ i, f k l i j = ∑ k, ∑ l, ∑ i, ∑ j, f k l i j :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ l, ∑ j, f k l i j := Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ l, ∑ j, f k l i j := Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ j, ∑ l, f k l i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [h (fun k l i j => M k i * a i * τ (G k l) * (conj (M l j) * conj (b j)))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

omit [NumberField E] [IsCMField E] in

theorem isom_of_gram_eq {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    {M N : Matrix (Fin r) (Fin r) ℂ} (hN : N.det ≠ 0) (h : gram τ G M = gram τ G N)
    (u v : Fin r → ℂ) :
    hermC τ G ((M * N⁻¹) *ᵥ u) ((M * N⁻¹) *ᵥ v) = hermC τ G u v := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hermC_mulVec, h, ← hermC_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hN),
    Matrix.one_mulVec, Matrix.one_mulVec]

theorem col_mul {r : ℕ} (g M : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (g * M) a = g *ᵥ col M a := by
  funext k
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

omit [NumberField E] [IsCMField E] in
theorem gram_isom {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    {g : Matrix (Fin r) (Fin r) ℂ} (hg : ∀ u v, hermC τ G (g *ᵥ u) (g *ᵥ v) = hermC τ G u v)
    (M : Matrix (Fin r) (Fin r) ℂ) : gram τ G (g * M) = gram τ G M := by
  ext a b
  simp only [gram, Matrix.of_apply, col_mul, hg]

theorem maj_isom {r : ℕ} (X : Data E r) (τ : X.Ψ) {x y : Frame X.Ψ r}
    {g : Matrix (Fin r) (Fin r) ℂ}
    (hg : ∀ u v, hermC τ.1 X.Gm (g *ᵥ u) (g *ᵥ v) = hermC τ.1 X.Gm u v)
    (hxy : mat y τ = g * mat x τ) (v : Fin r → ℂ) :
    X.maj y τ (g *ᵥ v) = X.maj x τ v := by
  simp only [Data.maj, Data.posPart, Data.gramPos, hxy, gram_isom τ.1 X.Gm hg, col_mul, hg]

theorem mat_cpt {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (z : V (nd X)) (τ : X.Ψ) :
    mat (cpt X x z) τ = mat x τ * mat (nmat X z) τ := rfl

theorem continuous_cpt {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) : Continuous (cpt X x) :=
  continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b =>
    (IW.cpt_entry_cd X x τ a b).continuous

theorem maj_near_orth :
    (∀ (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj y τ v ∧ X.maj y τ v ≤ (1 + ε) * X.maj x τ v) → (∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj (cpt X x z) τ v ∧ X.maj (cpt X x z) τ v ≤ (1 + ε) * X.maj x τ v) := by
  intro H r X ε hε
  have ho : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
  have hd : x0F X ∈ X.dom := IW.orth_mem_dom X _ ho
  have ht : Filter.Tendsto (cpt X (x0F X)) (𝓝 0) (𝓝 (x0F X)) := by
    have := (continuous_cpt X (x0F X)).tendsto 0
    rwa [IW.cpt_zero] at this
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1 (ht.eventually (H r X _ hd ε hε))
  refine ⟨min δ 1, lt_min hδ one_pos, min_le_right _ _, fun x hx z hz => ?_⟩
  obtain ⟨hz0, hm⟩ := hb (y := z) (by rw [dist_zero_right]; exact hz.trans_le (min_le_left _ _))
  have hxd : x ∈ X.dom := IW.orth_mem_dom X _ hx
  have hiso : ∀ τ : X.Ψ, ∀ u v, hermC τ.1 X.Gm ((mat x τ * (mat (x0F X) τ)⁻¹) *ᵥ u)
      ((mat x τ * (mat (x0F X) τ)⁻¹) *ᵥ v) = hermC τ.1 X.Gm u v := fun τ =>
    isom_of_gram_eq τ.1 X.Gm (hd τ).1 ((hx τ).trans (ho τ).symm)
  have h1 : ∀ τ : X.Ψ, mat x τ = (mat x τ * (mat (x0F X) τ)⁻¹) * mat (x0F X) τ := fun τ => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit (hd τ).1), Matrix.mul_one]
  have h2 : ∀ τ : X.Ψ, mat (cpt X x z) τ =
      (mat x τ * (mat (x0F X) τ)⁻¹) * mat (cpt X (x0F X) z) τ := fun τ => by
    rw [mat_cpt, mat_cpt, ← Matrix.mul_assoc, ← h1]
  have hdet : ∀ τ : X.Ψ, (mat x τ * (mat (x0F X) τ)⁻¹).det ≠ 0 := fun τ h0 => by
    have := (hxd τ).1
    rw [h1, Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  refine ⟨fun τ => ⟨?_, fun i => ?_⟩, fun τ v => ?_⟩
  · rw [h2, Matrix.det_mul]
    exact mul_ne_zero (hdet τ) (hz0 τ).1
  · have := (hz0 τ).2 i
    simp only [dmin] at this ⊢
    rwa [h2, gram_isom τ.1 X.Gm (hiso τ)]
  · obtain ⟨w, rfl⟩ : ∃ w, v = (mat x τ * (mat (x0F X) τ)⁻¹) *ᵥ w :=
      ⟨(mat x τ * (mat (x0F X) τ)⁻¹)⁻¹ *ᵥ v, by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit (hdet τ)), Matrix.one_mulVec]⟩
    rw [maj_isom X τ (hiso τ) (h1 τ), maj_isom X τ (hiso τ) (h2 τ)]
    exact hm τ w

end GlobalTheory.MajNear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralFundSetInterLe
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Unfold

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem lintegral_fundSet_inter_le : MeasInvStatement (E := E) → ∀ (r : ℕ) (X : Data E r) (x0 x1 : Frame X.Ψ r), IsOrth X x0 → IsOrth X x1 →
    ∀ FF, IsFundSet X x0 FF → ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ →
    (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (lact γ (rmul x b)) = φ x) →
    ∀ N : Set (V (nd X)), MeasurableSet N → N ⊆ OmF X x1 →
    ∫⁻ z in FF ∩ {z | ∃ y ∈ N, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, cpt X x0 z = lact γ (rmul (cpt X x1 y) b)},
      φ (cpt X x0 z) ∂muF X x0 ≤ ∫⁻ y in N, φ (cpt X x1 y) ∂muF X x1 := by
  intro hM r X x0 x1 ho0 ho1 FF hF φ hφ hinv N hN hNO
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hc : Measurable (cpt X x0) := (FundSetPf.cont_cpt X x0).measurable
  have hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x := fun x hx b hb => by
    have h := hinv 1 X.Γ.one_mem x hx b hb
    rwa [FundSetPf.lact_one] at h
  let ψ : Frame X.Ψ r → ℝ≥0∞ := (satFrames X x1 N).indicator φ
  have hψ : Measurable ψ := hφ.indicator (measurableSet_satFrames X ho1 hN hNO)
  have hψB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x := by
    intro x hx b hb
    simp only [ψ, Set.indicator, rmul_mem_satFrames_iff X x1 N _ hb, hφB x hx b hb]
  have h1 : ∫⁻ y in N, φ (cpt X x1 y) ∂muF X x1 = ∫⁻ y, ψ (cpt X x1 y) ∂muF X x1 := by
    rw [← lintegral_indicator hN]
    refine lintegral_congr fun z => ?_
    simp only [ψ, Set.indicator, cpt_mem_satFrames_iff X ho1]
  rw [h1, ← hM r X x0 x1 ho0 ho1 ψ hψ hψB, lintegral_unfold hM r X x0 ho0 FF hF ψ hψ hψB]
  refine le_trans (setLIntegral_mono (g := fun z => ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z))) ?_ ?_)
    (lintegral_mono_set Set.inter_subset_left)
  · exact Measurable.tsum fun γ => (hψ.comp (continuous_lact X γ.1).measurable).comp hc
  · rintro z ⟨-, y, hy, γ, hγ, b, hb, h⟩
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (⟨γ⁻¹, X.Γ.inv_mem hγ⟩ : X.Γ))
    have hm : rmul (cpt X x1 y) b ∈ satFrames X x1 N := ⟨y, hy, b, hb, rfl⟩
    show φ (cpt X x0 z) = ψ (lact γ⁻¹ (cpt X x0 z))
    rw [h, FundSetPf.lact_inv, hinv γ hγ _ (hNO hy) b hb]
    show _ = (satFrames X x1 N).indicator φ _
    rw [Set.indicator_of_mem hm, hφB _ (hNO hy) b hb]

end GlobalTheory.Unfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MuFLtTopOfIsCompact
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.SatFin

open GlobalTheory.FrameMeas

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem muF_lt_top_of_isCompact {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) {K : Set (V (nd X))}
    (hK : IsCompact K) (hKO : K ⊆ OmF X x0) : muF X x0 K < ⊤ := by
  obtain ⟨M, hM⟩ := hK.bddAbove_image (OntoB.densF_continuousOn.mono hKO)
  unfold muF
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ z in K, ENNReal.ofReal (densF X x0 z) ∂(volume.restrict (OmF X x0))
      ≤ ∫⁻ _ in K, ENNReal.ofReal M ∂(volume.restrict (OmF X x0)) :=
        setLIntegral_mono' hK.measurableSet fun z hz =>
          ENNReal.ofReal_le_ofReal (hM ⟨z, hz, rfl⟩)
    _ = ENNReal.ofReal M * (volume.restrict (OmF X x0)) K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top)

theorem muF_borSat_eq (hI : MeasInvStatement (E := E)) {r : ℕ} (X : Data E r)
    {x0 x1 : Frame X.Ψ r} (h0 : IsOrth X x0) (h1 : IsOrth X x1) {C : Set (Frame X.Ψ r)}
    (hK : IsCompact C) (hC : C ⊆ X.dom) :
    muF X x0 (cpt X x0 ⁻¹' borSat X C) = muF X x1 (cpt X x1 ⁻¹' borSat X C) := by
  have hS := measurableSet_borSat X hK hC
  have h := hI r X x0 x1 h0 h1 ((borSat X C).indicator 1) (measurable_one.indicator hS) (by
    intro x _ b hb
    by_cases hxS : x ∈ borSat X C
    · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem ((rmul_mem_borSat_iff X C hb).mpr hxS)]
      rfl
    · rw [Set.indicator_of_notMem hxS,
        Set.indicator_of_notMem fun h => hxS ((rmul_mem_borSat_iff X C hb).mp h)])
  rw [← lintegral_indicator_one ((FundSetPf.cont_cpt X x0).measurable hS),
    ← lintegral_indicator_one ((FundSetPf.cont_cpt X x1).measurable hS)]
  exact h

theorem muF_sat_lt_top (hI : MeasInvStatement (E := E)) (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r)
    (hx0 : IsOrth X x0) (C : Set (Frame X.Ψ r)) (hK : IsCompact C) (hC : C ⊆ X.dom) :
    muF X x0 (sat X x0 C) < ⊤ := by
  rw [sat_eq_preimage X x0 hC]
  refine hK.induction_on (p := fun s => muF X x0 (cpt X x0 ⁻¹' borSat X s) < ⊤) ?_ ?_ ?_ ?_
  · have : borSat X (∅ : Set (Frame X.Ψ r)) = ∅ := by
      ext y; simp [borSat]
    simp [this]
  · intro s t hst ht
    refine (measure_mono fun z hz => ?_).trans_lt ht
    obtain ⟨x, hx, h⟩ := hz
    exact ⟨x, hst hx, h⟩
  · intro s t hs ht
    refine (measure_mono (t := cpt X x0 ⁻¹' borSat X s ∪ cpt X x0 ⁻¹' borSat X t)
      fun z hz => ?_).trans_lt (measure_union_lt_top hs ht)
    obtain ⟨x, hx | hx, h⟩ := hz
    · exact Or.inl ⟨x, hx, h⟩
    · exact Or.inr ⟨x, hx, h⟩
  · intro x hx
    have hxd := hC hx
    obtain ⟨x1, hx1, b1, hb1, hxe⟩ := ortho_holds r X x hxd
    obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hdec, huniq⟩ := lu_holds r X x1 hx1
    have h0 := IW.zero_mem_OmF X x1 hx1
    obtain ⟨u1, u2, -⟩ := huniq 0 h0 b1 hb1
    rw [IW.cpt_zero, ← hxe] at u1 u2
    obtain ⟨ρ, hρ, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      ((OntoB.isOpen_OmF X x1).mem_nhds h0)
    have hW : {y | y ∈ X.dom ∧ Δ y ≠ 0} ∈ 𝓝 x :=
      ((FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)).mem_nhds
        ⟨hxd, u1⟩
    have hzc : ContinuousAt zOf x := hz.continuousOn.continuousAt hW
    have hV : zOf ⁻¹' Metric.closedBall 0 ρ ∈ 𝓝 x :=
      hzc.preimage_mem_nhds (by rw [u2]; exact Metric.closedBall_mem_nhds _ hρ)
    refine ⟨{y | y ∈ X.dom ∧ Δ y ≠ 0} ∩ zOf ⁻¹' Metric.closedBall 0 ρ,
      mem_nhdsWithin_of_mem_nhds (Filter.inter_mem hW hV), ?_⟩
    have hKc : IsCompact (cpt X x1 '' Metric.closedBall 0 ρ) :=
      (isCompact_closedBall _ _).image (FundSetPf.cont_cpt X x1)
    have hKd : cpt X x1 '' Metric.closedBall 0 ρ ⊆ X.dom := by
      rintro _ ⟨z, hz, rfl⟩
      exact hball hz
    calc muF X x0 (cpt X x0 ⁻¹' borSat X
          ({y | y ∈ X.dom ∧ Δ y ≠ 0} ∩ zOf ⁻¹' Metric.closedBall 0 ρ))
        ≤ muF X x0 (cpt X x0 ⁻¹' borSat X (cpt X x1 '' Metric.closedBall 0 ρ)) := by
          refine measure_mono fun z hz => ?_
          obtain ⟨y, ⟨⟨hyd, hyΔ⟩, hyz⟩, b, hb, h⟩ := hz
          obtain ⟨-, hb', hy⟩ := hdec y hyd hyΔ
          refine ⟨_, ⟨zOf y, hyz, rfl⟩, rmul (bOf y) b, ExtFPf.mul_mem X hb' hb, ?_⟩
          rw [← ExtFPf.rmul_assoc, ← hy, h]
      _ = muF X x1 (cpt X x1 ⁻¹' borSat X (cpt X x1 '' Metric.closedBall 0 ρ)) :=
          muF_borSat_eq hI X hx0 hx1 hKc hKd
      _ ≤ muF X x1 (Metric.closedBall 0 ρ) := by
          refine measure_mono fun z hz => ?_
          obtain ⟨_, ⟨z', hz', rfl⟩, b, hb, h⟩ := hz
          rw [← ExtFPf.rmul_oneF X (cpt X x1 z)] at h
          rwa [FundSetPf.cpt_uniq X hx1 (ExtFPf.oneF_mem X) hb h]
      _ < ⊤ := muF_lt_top_of_isCompact X x1 (isCompact_closedBall _ _) hball

end GlobalTheory.SatFin
end

