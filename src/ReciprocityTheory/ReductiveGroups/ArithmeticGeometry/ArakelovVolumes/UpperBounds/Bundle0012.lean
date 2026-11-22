import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantNormalForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfD
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix MeasureTheory

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

abbrev UpI (ι : Type*) (r : ℕ) : Type _ := {i : Ix ι r // ¬ i.2.2 < i.2.1}

abbrev LoI (ι : Type*) (r : ℕ) : Type _ := {i : Ix ι r // i.2.2 < i.2.1}

def Umat (y : UpI ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if h : ¬ b < a then y ⟨(τ, a, b), h⟩ else 0

lemma Umat_add (y y' : UpI ι r → ℂ) (τ : ι) : Umat (y + y') τ = Umat y τ + Umat y' τ := by
  ext a b
  simp only [Umat, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp

lemma Umat_smul (c : ℂ) (y : UpI ι r → ℂ) (τ : ι) : Umat (c • y) τ = c • Umat y τ := by
  ext a b
  simp only [Umat, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

def Lβ (β : ι → Matrix (Fin r) (Fin r) ℂ) : (UpI ι r → ℂ) →ₗ[ℂ] (UpI ι r → ℂ) where
  toFun y i := (β i.1.1 * Umat y i.1.1) i.1.2.1 i.1.2.2
  map_add' y y' := by funext i; simp [Umat_add, Matrix.mul_add]
  map_smul' c y := by funext i; simp [Umat_smul]

def keyU (e : ι ≃ Fin (Fintype.card ι)) (i : UpI ι r) : ℕ ×ₗ (ℕ ×ₗ Fin (Fintype.card ι)) :=
  toLex ((i.1.2.2 : ℕ), toLex (r - (i.1.2.1 : ℕ), e i.1.1))

lemma keyU_injective (e : ι ≃ Fin (Fintype.card ι)) : Function.Injective (keyU (r := r) e) := by
  rintro ⟨⟨τ, a, b⟩, hi⟩ ⟨⟨τ', a', b'⟩, hj⟩ h
  simp only [keyU, toLex_inj, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have ha : (a : ℕ) = a' := by have := a.isLt; have := a'.isLt; omega
  apply Subtype.ext
  simp only [Prod.mk.injEq]
  exact ⟨e.injective h3, Fin.ext ha, Fin.ext h1⟩

private lemma toMatrix_entry_lemma (β : ι → Matrix (Fin r) (Fin r) ℂ) (i j : UpI ι r) :
    LinearMap.toMatrix' (Lβ β) i j =
      if j.1.1 = i.1.1 ∧ j.1.2.2 = i.1.2.2 then β i.1.1 i.1.2.1 j.1.2.1 else 0 := by
  obtain ⟨⟨τ, a, b⟩, hi⟩ := i
  obtain ⟨⟨τ', a', b'⟩, hj⟩ := j
  rw [LinearMap.toMatrix'_apply]
  simp only [Lβ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, Umat, Matrix.of_apply]
  rw [Finset.sum_eq_single a']
  · by_cases h : τ' = τ ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := h
      simp [hj, Pi.single_apply]
    · rw [if_neg h]
      split_ifs with h'
      · simp
      · rw [Pi.single_apply, if_neg, mul_zero]
        intro heq
        apply h
        simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
        exact ⟨heq.1.symm, heq.2.2.symm⟩
  · intro c _ hc
    split_ifs with h'
    · simp
    · rw [Pi.single_apply, if_neg, mul_zero]
      intro heq
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
      exact hc heq.2.1
  · simp

lemma toMatrix_Lβ_zero (e : ι ≃ Fin (Fintype.card ι)) (β : ι → Matrix (Fin r) (Fin r) ℂ)
    (hβ : ∀ τ, (β τ).BlockTriangular id) (i j : UpI ι r) (hij : keyU e i < keyU e j) :
    LinearMap.toMatrix' (Lβ β) i j = 0 := by
  rw [toMatrix_entry_lemma]
  split_ifs with h
  · obtain ⟨⟨τ, a, b⟩, hi⟩ := i
    obtain ⟨⟨τ', a', b'⟩, hj⟩ := j
    obtain ⟨rfl, rfl⟩ := h
    simp only [keyU, Prod.Lex.toLex_lt_toLex, lt_irrefl, false_or, and_false, or_false,
      true_and] at hij
    apply hβ _
    have := a.isLt; have := a'.isLt
    show (a' : ℕ) < a
    omega
  · rfl

lemma toMatrix_Lβ_diag (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) (i : UpI ι r) :
    LinearMap.toMatrix' (Lβ β) i i = β i.1.1 i.1.2.1 i.1.2.1 := by
  rw [toMatrix_entry_lemma, if_pos ⟨rfl, rfl⟩]

theorem det_Lβ (β : ι → Matrix (Fin r) (Fin r) ℂ) (hβ : ∀ τ, (β τ).BlockTriangular id) :
    LinearMap.det (Lβ β) = ∏ i : UpI ι r, β i.1.1 i.1.2.1 i.1.2.1 := by
  rw [← LinearMap.det_toMatrix']
  let e := Fintype.equivFin ι
  letI : LinearOrder (UpI ι r) := LinearOrder.lift' (keyU (r := r) e) (keyU_injective e)
  have h := Matrix.det_of_lowerTriangular (LinearMap.toMatrix' (Lβ β)) (fun i j hij =>
    toMatrix_Lβ_zero e β hβ i j hij)
  convert h using 2 with i
  exact (toMatrix_Lβ_diag β hβ i).symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace ModeHalfA

open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

noncomputable def sf (p0 : ℕ) (α β : Fin r → ℂ) : ℂ :=
  ∑ k : Fin r, ((sgn p0 (k : ℕ) : ℝ) : ℂ) * α k * conj (β k)

def cl (N : Fin r → Fin r → ℂ) (a : Fin r) : Fin r → ℂ := fun k => N k a

noncomputable def Ag (p0 : ℕ) (hp : p0 ≤ r) (N : Fin r → Fin r → ℂ) : Matrix (Fin p0) (Fin p0) ℂ :=
  Matrix.of fun a b => sf p0 (cl N (Fin.castLE hp a)) (cl N (Fin.castLE hp b))

noncomputable def Ms (p0 : ℕ) (hp : p0 ≤ r) (N : Fin r → Fin r → ℂ) (v : Fin r → ℂ) : ℝ :=
  2 * (∑ a : Fin p0, ∑ b : Fin p0, sf p0 v (cl N (Fin.castLE hp a)) * (Ag p0 hp N)⁻¹ a b *
    conj (sf p0 v (cl N (Fin.castLE hp b)))).re - (sf p0 v v).re

private lemma hermC_eq_dotProduct_upper_bounds (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    hermC τ G u v = u ⬝ᵥ (G.map τ *ᵥ fun b => conj (v b)) := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.hermC, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, mul_assoc]

private lemma gram_eq_upper_bounds (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (Y : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G Y = Yᵀ * G.map τ * Y.map conj := by
  ext i j
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col,
    Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma hermC_mulVec_eq_dotProduct_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (Y : Matrix (Fin r) (Fin r) ℂ) (w n : Fin r → ℂ) :
    hermC τ G (Y *ᵥ w) (Y *ᵥ n) = w ⬝ᵥ (gram τ G Y *ᵥ fun b => conj (n b)) := by
  have hc : (fun b => conj ((Y *ᵥ n) b)) = Y.map conj *ᵥ fun b => conj (n b) := by
    funext b
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [hermC_eq_dotProduct_upper_bounds, hc, gram_eq_upper_bounds, dotProduct_comm, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, dotProduct_comm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

private lemma det_ne_zero_of_gram_eq_diagonal_sgn (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ)
    (Y : Matrix (Fin r) (Fin r) ℂ)
    (hY : gram τ G Y = diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) : Y.det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det hY
  rw [gram_eq_upper_bounds, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at h1
  exact (Finset.prod_ne_zero_iff.mpr fun a _ => by unfold sgn; split_ifs <;> norm_num) h1.symm

theorem maj_chart (X : Data E r) {w : Frame X.Ψ r} {τ : X.Ψ} {Y : Matrix (Fin r) (Fin r) ℂ}
    (hY : FD.gram τ.1 X.Gm Y = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (N : Fin r → Fin r → ℂ) (hw : mat w τ = Y * Matrix.of N) (v : Fin r → ℂ) :
    X.maj w τ v = Ms X.p0 X.p0_le N (Y⁻¹ *ᵥ v) := by
  have hS : ∀ u' n : Fin r → ℂ, hermC τ.1 X.Gm (Y *ᵥ u') (Y *ᵥ n) = sf X.p0 u' n := by
    intro u' n
    rw [hermC_mulVec_eq_dotProduct_gram, hY]
    simp only [sf, dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hdetY := det_ne_zero_of_gram_eq_diagonal_sgn τ.1 X.Gm X.p0 Y hY
  have hv : v = Y *ᵥ (Y⁻¹ *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetY), Matrix.one_mulVec]
  have hcol : ∀ a, FD.col (mat w τ) a = Y *ᵥ cl N a := by
    intro a
    rw [hw]
    funext k
    simp [ReciprocityTheory.ChartRestriction.G.FD.col, cl, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hgp : X.gramPos w τ = Ag X.p0 X.p0_le N := by
    ext a b
    simp only [Data.gramPos, Matrix.submatrix_apply, ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, Ag]
    rw [hcol, hcol, hS]
  unfold Data.maj Data.posPart Ms
  rw [hgp]
  conv_lhs => rw [hv]
  simp only [hcol, hS]

theorem dom_of_orth (X : Data E r) {u : Frame X.Ψ r} (hu : IsOrth X u) : u ∈ X.dom := by
  intro τ
  have hY := hu τ
  refine ⟨det_ne_zero_of_gram_eq_diagonal_sgn τ.1 X.Gm X.p0 _ hY, fun i => ?_⟩
  have hd : dmin X.Gm u τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [hY, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    simp only [Function.comp_apply, Fin.coe_castLE, psgn, Complex.ofReal_prod]
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) i
  rw [hd, Complex.ofReal_re]
  have hne : psgn X.p0 i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => by unfold sgn; split_ifs <;> norm_num
  exact mul_self_pos.mpr hne

theorem maj_orth (X : Data E r) {u : Frame X.Ψ r} (hu : IsOrth X u) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj u τ v = ∑ a, ‖((mat u τ)⁻¹ *ᵥ v) a‖ ^ 2 := by
  have hY := hu τ
  set N : Fin r → Fin r → ℂ := fun i j => (1 : Matrix (Fin r) (Fin r) ℂ) i j with hN
  have hw : mat u τ = mat u τ * Matrix.of N := by
    rw [show Matrix.of N = 1 from rfl, Matrix.mul_one]
  rw [maj_chart X hY N hw v]
  set w := (mat u τ)⁻¹ *ᵥ v
  have hsf : ∀ (α : Fin r → ℂ) (b : Fin r), sf X.p0 α (cl N b) = ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) * α b := by
    intro α b
    unfold sf cl
    rw [Finset.sum_eq_single b]
    · simp [hN]
    · intro k _ hk
      simp [hN, Matrix.one_apply_ne hk]
    · intro h
      exact absurd (Finset.mem_univ b) h
  have hAg : Ag X.p0 X.p0_le N = 1 := by
    ext a b
    simp only [Ag, Matrix.of_apply, hsf]
    by_cases hab : a = b
    · subst hab
      simp [cl, hN, sgn]
    · have hne : (Fin.castLE X.p0_le b : Fin r) ≠ Fin.castLE X.p0_le a :=
        fun h => hab (Fin.castLE_injective _ h).symm
      simp [cl, hN, Matrix.one_apply_ne hne, Matrix.one_apply_ne hab]
  have hcast : ∀ g : Fin r → ℝ, ∑ a : Fin X.p0, g (Fin.castLE X.p0_le a) =
      ∑ k : Fin r, if (k : ℕ) < X.p0 then g k else 0 := by
    intro g
    rw [← Finset.sum_filter]
    have hset : Finset.univ.filter (fun k : Fin r => (k : ℕ) < X.p0) =
        Finset.univ.map (Fin.castLEEmb X.p0_le) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro hk
        exact ⟨⟨k, hk⟩, Fin.ext rfl⟩
      · rintro ⟨a, rfl⟩
        exact a.isLt
    rw [hset, Finset.sum_map]
    rfl
  have hinner : ∀ a : Fin X.p0, ∑ b : Fin X.p0, sf X.p0 w (cl N (Fin.castLE X.p0_le a)) *
      (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) a b * conj (sf X.p0 w (cl N (Fin.castLE X.p0_le b))) =
      ((‖w (Fin.castLE X.p0_le a)‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    rw [Finset.sum_eq_single a (fun b _ hb => by rw [Matrix.one_apply_ne' hb, mul_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ a) h)]
    rw [Matrix.one_apply_eq, mul_one, hsf]
    have ha : ((Fin.castLE X.p0_le a : Fin r) : ℕ) < X.p0 := by simp
    simp only [sgn, ha, if_true, Complex.ofReal_one, one_mul]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hww : (sf X.p0 w w).re = ∑ k : Fin r, sgn X.p0 (k : ℕ) * ‖w k‖ ^ 2 := by
    unfold sf
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, Complex.ofReal_re]
  unfold Ms
  rw [hAg, inv_one]
  simp only [hinner]
  rw [← Complex.ofReal_sum, Complex.ofReal_re, hww]
  have hc := hcast (fun k => ‖w k‖ ^ 2)
  beta_reduce at hc
  rw [hc, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold sgn
  split_ifs <;> ring

end ModeHalfA

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB

open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
open scoped ComplexConjugate ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)

theorem cd_nmat (τ : X.Ψ) (a b : Fin r) : ContDiff ℂ ∞ fun z : V (nd X) => nmat X z τ a b := by
  unfold nmat
  by_cases h : b < a
  · simp only [dif_pos h]
    first
    | fun_prop
    | exact (EuclideanSpace.proj (𝕜 := ℂ) _).contDiff
  · simp only [dif_neg h]
    exact contDiff_const

theorem cd_cpt_entry (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℂ ∞ fun z : V (nd X) => cpt X x0 z τ a b := by
  have he : (fun z : V (nd X) => cpt X x0 z τ a b) = fun z => ∑ c, x0 τ a c * nmat X z τ c b := by
    funext z
    simp [cpt, rmul, mat, Matrix.mul_apply]
  rw [he]
  exact ContDiff.sum fun c _ => contDiff_const.mul (cd_nmat X τ c b)

theorem cd_cpt : ContDiff ℂ ∞ (cpt X x0) := contDiff_pi.mpr fun τ => contDiff_pi.mpr fun a => contDiff_pi.mpr fun b =>
  cd_cpt_entry X x0 τ a b

theorem hol_comp {f : Frame X.Ψ r → ℂ} (hf : DifferentiableOn ℂ f X.dom) :
    DifferentiableOn ℂ (fun z => f (cpt X x0 z)) (OmF X x0) := hf.comp ((cd_cpt X x0).differentiable (by simp)).differentiableOn (fun _ hz => hz)

theorem isOpen_OmF : IsOpen (OmF X x0) := by
  have hmat : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => mat x τ := fun τ =>
    continuous_matrix fun a b => (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))
  have hent : ∀ (τ : X.Ψ) (a b : Fin r), Continuous fun x : Frame X.Ψ r => x τ a b := fun τ a b =>
    (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))
  have hdmin : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor
    refine Continuous.matrix_det ?_
    refine continuous_matrix fun a b => ?_
    simp only [Matrix.submatrix_apply, ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC,
      ReciprocityTheory.ChartRestriction.G.FD.col, ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.of_apply]
    refine continuous_finset_sum _ fun c _ => continuous_finset_sum _ fun d _ => ?_
    exact ((hent τ c _).mul continuous_const).mul (Complex.continuous_conj.comp (hent τ d _))
  have hGG : GG X.Ψ X.Gm X.p0 = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x : Frame X.Ψ r | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x
    simp [GG]
  have hopen : IsOpen (GG X.Ψ X.Gm X.p0) := by
    rw [hGG]
    refine isOpen_iInter_of_finite fun τ => ?_
    refine IsOpen.inter (isOpen_ne_fun (hmat τ).matrix_det continuous_const)
      (isOpen_iInter_of_finite fun i => ?_)
    exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (hdmin τ i)))
  exact (cd_cpt X x0).continuous.isOpen_preimage _ hopen

theorem cd_dmin (τ : X.Ψ) (i : Fin (r + 1)) :
    ContDiff ℝ ∞ fun z : V (nd X) => dmin X.Gm (cpt X x0 z) τ i := by
  have hE : ∀ (τ : X.Ψ) (a b : Fin r), ContDiff ℝ ∞ fun z : V (nd X) => cpt X x0 z τ a b :=
    fun τ a b => (cd_cpt_entry X x0 τ a b).restrict_scalars ℝ
  have hC : ∀ (τ : X.Ψ) (a b : Fin r),
      ContDiff ℝ ∞ fun z : V (nd X) => starRingEnd ℂ (cpt X x0 z τ a b) := by
    intro τ a b
    have h := Complex.conjCLE.contDiff.comp (hE τ a b)
    simpa [Function.comp_def] using h
  unfold dmin lminor
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  refine contDiff_prod fun k _ => ?_
  simp only [Matrix.submatrix_apply, ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC,
      ReciprocityTheory.ChartRestriction.G.FD.col, ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.of_apply]
  refine ContDiff.sum fun c _ => ContDiff.sum fun d _ => ?_
  exact ((hE τ c _).mul contDiff_const).mul (hC τ d _)

variable {X x0}

theorem dmin_ne {z : V (nd X)} (hz : z ∈ OmF X x0) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (cpt X x0 z) τ i ≠ 0 := by
  intro h0
  have h1 : 0 < psgn X.p0 i * (dmin X.Gm (cpt X x0 z) τ i).re := (hz τ).2 i
  rw [h0, Complex.zero_re, mul_zero] at h1
  exact lt_irrefl _ h1

variable (X x0)

def LD (z : V (nd X)) : ℝ :=
  ∑ τ, ∑ i : Fin r, (-2) * Real.log ‖dmin X.Gm (cpt X x0 z) τ i.castSucc‖

variable {X x0}

theorem densF_pos {z : V (nd X)} (hz : z ∈ OmF X x0) : 0 < densF X x0 z := by
  unfold densF
  refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => ?_
  exact zpow_pos (norm_pos_iff.mpr (dmin_ne hz τ i.castSucc)) _

theorem log_densF {z : V (nd X)} (hz : z ∈ OmF X x0) : Real.log (densF X x0 z) = LD X x0 z := by
  have hp : ∀ (τ : X.Ψ) (i : Fin r), 0 < ‖dmin X.Gm (cpt X x0 z) τ i.castSucc‖ ^ (-2 : ℤ) :=
    fun τ i => zpow_pos (norm_pos_iff.mpr (dmin_ne hz τ i.castSucc)) _
  unfold densF LD
  rw [Real.log_prod (fun τ _ => (Finset.prod_pos fun i _ => hp τ i).ne')]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_prod (fun i _ => (hp τ i).ne')]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_zpow]
  norm_num

theorem LD_contDiffAt {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℝ ∞ (LD X x0) z := by
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)),
      ContDiffAt ℝ ∞ (fun w => Real.log ‖dmin X.Gm (cpt X x0 w) τ i‖) z := by
    intro τ i
    have hne := dmin_ne hz τ i
    have h1 : ContDiffAt ℝ ∞ (fun w => ‖dmin X.Gm (cpt X x0 w) τ i‖) z :=
      (contDiffAt_norm ℂ hne).comp z (cd_dmin X x0 τ i).contDiffAt
    exact h1.log (norm_ne_zero_iff.mpr hne)
  unfold LD
  exact ContDiffAt.sum fun τ _ => ContDiffAt.sum fun i _ => contDiffAt_const.mul (hd τ i.castSucc)

theorem logDens_contDiffAt {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℝ ∞ (fun w => Real.log (densF X x0 w)) z := by
  refine (LD_contDiffAt hz).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_OmF X x0).mem_nhds hz] with w hw using log_densF hw

theorem densF_continuousOn : ContinuousOn (densF X x0) (OmF X x0) := by
  intro z hz
  have h := Real.continuous_exp.continuousAt.comp (logDens_contDiffAt hz).continuousAt
  refine (ContinuousAt.congr h ?_).continuousWithinAt
  filter_upwards [(isOpen_OmF X x0).mem_nhds hz] with w hw using Real.exp_log (densF_pos hw)

theorem rhF_contDiffAt {z : V (nd X)} (hz : z ∈ OmF X x0) : ContDiffAt ℝ ∞ (rhF X x0) z := by
  have hd : ∀ (τ : X.Ψ) (i : Fin (r + 1)),
      ContDiffAt ℝ ∞ (fun w => Real.log ‖dmin X.Gm (cpt X x0 w) τ i‖) z := by
    intro τ i
    have hne := dmin_ne hz τ i
    have h1 : ContDiffAt ℝ ∞ (fun w => ‖dmin X.Gm (cpt X x0 w) τ i‖) z :=
      (contDiffAt_norm ℂ hne).comp z (cd_dmin X x0 τ i).contDiffAt
    exact h1.log (norm_ne_zero_iff.mpr hne)
  unfold rhF
  exact (ContDiffAt.sum fun τ _ => hd τ _).neg

theorem ka_contDiffAt (bb : ℝ) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℝ ∞ (kaF X x0 bb) z := by
  unfold kaF
  exact Real.contDiff_exp.contDiffAt.comp z (contDiffAt_const.mul (rhF_contDiffAt hz))

theorem levi_rh_nonneg (hGrad : RhGradFStatement (E := E)) (hx0 : IsOrth X x0) {z : V (nd X)}
    (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    0 ≤ (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re := by
  have hG := hGrad r X x0 hx0 z hz ξ
  by_cases hC : ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) = 0
  · have hwd : ∀ w ∈ OmF X x0, ∀ j,
        wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) w = 0 := by
      intro w hw j
      have h := hGrad r X x0 hx0 w hw (Pi.single j 1)
      rw [hC, zero_mul] at h
      have h' := le_antisymm h (Complex.normSq_nonneg _)
      rw [Complex.normSq_eq_zero] at h'
      simpa [Pi.single_apply] using h'
    have hwdb : ∀ w ∈ OmF X x0, ∀ k,
        wdb (nd X) k (fun w => ((rhF X x0 w : ℝ) : ℂ)) w = 0 := by
      intro w hw k
      have hd : DifferentiableAt ℝ (rhF X x0) w := (rhF_contDiffAt hw).differentiableAt (by simp)
      have hf : ∀ v, fderiv ℝ (fun w => ((rhF X x0 w : ℝ) : ℂ)) w v =
          ((fderiv ℝ (rhF X x0) w v : ℝ) : ℂ) := by
        intro v
        have hh : HasFDerivAt (fun w => ((rhF X x0 w : ℝ) : ℂ))
            (Complex.ofRealCLM.comp (fderiv ℝ (rhF X x0) w)) w :=
          Complex.ofRealCLM.hasFDerivAt.comp w hd.hasFDerivAt
        rw [hh.fderiv]
        rfl
      have h0 := hwd w hw k
      simp only [wd, hf] at h0
      simp only [wdb, hf]
      set p := fderiv ℝ (rhF X x0) w (bas (nd X) k)
      set q := fderiv ℝ (rhF X x0) w (Complex.I • bas (nd X) k)
      have h2 : (p : ℂ) - Complex.I * (q : ℂ) = 0 := by
        rcases div_eq_zero_iff.mp h0 with h0 | h0
        · exact h0
        · norm_num at h0
      have hp : p = 0 := by
        have h3 := congrArg Complex.re h2
        simpa using h3
      have hq : q = 0 := by
        have h3 := congrArg Complex.im h2
        simpa using h3
      rw [hp, hq]
      simp
    have hL : leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ = 0 := by
      unfold leviV
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
      have hev : wdb (nd X) k (fun w => ((rhF X x0 w : ℝ) : ℂ)) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
        filter_upwards [(isOpen_OmF X x0).mem_nhds hz] with w hw using hwdb w hw k
      have hfd : fderiv ℝ (wdb (nd X) k (fun w => ((rhF X x0 w : ℝ) : ℂ))) z = 0 := by
        rw [hev.fderiv_eq]
        simp
      simp [wd, hfd]
    rw [hL]
    simp
  · have hCpos : (0 : ℝ) < ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hC)
    have h0 : ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) * 0 ≤
        ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) *
          (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re := by
      rw [mul_zero]
      exact le_trans (Complex.normSq_nonneg _) hG
    exact le_of_mul_le_mul_left h0 hCpos

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
end

