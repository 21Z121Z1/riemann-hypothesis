import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
section
noncomputable section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

variable {r p q m : ℕ}

abbrev Low (m : ℕ) : Type := {s : Fin m × Fin m // s.2 < s.1}

def uni (y : Low m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun a b => if h : b < a then y ⟨(a, b), h⟩ else if a = b then 1 else 0

def dens (A : Matrix (Fin m) (Fin m) ℂ) (y : Low m → ℂ) : ℝ :=
  ∏ i : Fin m, ‖lminor ((uni y)ᴴ * A * uni y) i.castSucc‖ ^ (-2 : ℤ)

def IsBlockSL2Embedding (e : Fin r ≃ Fin p ⊕ Fin q) : Prop :=
  (∀ a, (e.symm (Sum.inl a) : ℕ) = q + a) ∧ ∀ a, (e.symm (Sum.inr a) : ℕ) = a

def toMat (v : Fin p × Fin q → ℂ) : Matrix (Fin p) (Fin q) ℂ := Matrix.of fun a b => v (a, b)

def glue (e : Fin r ≃ Fin p ⊕ Fin q) (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)) : Low r → ℂ :=
  fun s => fromBlocks (uni w.2.2) (toMat w.1 * uni w.2.1) 0 (uni w.2.1) (e s.1.1) (e s.1.2)

def base (e : Fin r ≃ Fin p ⊕ Fin q) (y : Low r → ℂ) : Fin p × Fin q → ℂ := vecOf (moeb (reindex e e (uni y)) 0)

def shear (A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Z : Matrix (Fin p) (Fin q) ℂ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  (fromBlocks 1 Z 0 1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * A * fromBlocks 1 Z 0 1

def schur (H : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  H.toBlocks₁₁ - H.toBlocks₁₂ * H.toBlocks₂₂⁻¹ * H.toBlocks₂₁

def sgnMat (r q : ℕ) : Matrix (Fin r) (Fin r) ℂ := diagonal fun a : Fin r => ((sgn q (a : ℕ) : ℝ) : ℂ)

theorem isBlockOrderedSumEquiv_trueIndex {r j : ℕ} (h : j ≤ r) : IsBlockSL2Embedding (idx h) := ⟨idx_symm_inl h, idx_symm_inr h⟩

theorem IsBlockSL2Embedding.card {e : Fin r ≃ Fin p ⊕ Fin q} (_ : IsBlockSL2Embedding e) : r = p + q := by
  simpa using Fintype.card_congr e

theorem exists_isBlockOrderedSumEquiv (p q : ℕ) : ∃ e : Fin (p + q) ≃ Fin p ⊕ Fin q, IsBlockSL2Embedding e :=
  ⟨((finCongr (add_comm p q)).trans finSumFinEquiv.symm).trans (Equiv.sumComm _ _), by
    constructor <;> intro a <;> simp [add_comm]⟩

@[simp] theorem toMat_vecOf (Z : Matrix (Fin p) (Fin q) ℂ) : toMat (vecOf Z) = Z := rfl

@[simp] theorem vecOf_toMat (v : Fin p × Fin q → ℂ) : vecOf (toMat v) = v := rfl

theorem det_uni (y : Low m → ℂ) : (uni y).det = 1 := by
  rw [det_of_lowerTriangular]
  · simp [uni]
  · intro a b h
    have h' : a < b := h
    simp [uni, not_lt_of_gt h', h'.ne]

theorem uni_eq_of_entries {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) (y : Low r → ℂ) (y1 : Low q → ℂ) (y2 : Low p → ℂ)
    (Y : Matrix (Fin p) (Fin q) ℂ) (h : ∀ s : Low r, y s = fromBlocks (uni y2) Y 0 (uni y1) (e s.1.1) (e s.1.2)) :
    reindex e e (uni y) = fromBlocks (uni y2) Y 0 (uni y1) := by
  ext a b
  rw [reindex_apply, submatrix_apply]
  by_cases hab : e.symm b < e.symm a
  · simp only [uni, of_apply, dif_pos hab]
    rw [h]; simp [uni]
  · simp only [uni, of_apply, dif_neg hab, EmbeddingLike.apply_eq_iff_eq]
    rw [Fin.lt_def] at hab
    rcases a with a | a <;> rcases b with b | b <;> simp only [he.1, he.2] at hab
    · have : ¬ b < a := by rw [Fin.lt_def]; omega
      simp [this]
    · have := b.2; omega
    · simp
    · have : ¬ b < a := by rw [Fin.lt_def]; omega
      simp [this]

theorem reindex_uni_glue {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e)
    (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)) :
    reindex e e (uni (glue e w)) = fromBlocks (uni w.2.2) (toMat w.1 * uni w.2.1) 0 (uni w.2.1) :=
  uni_eq_of_entries he _ _ _ _ fun _ => rfl

theorem base_glue {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e)
    (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ)) : base e (glue e w) = w.1 := by
  rw [base, reindex_uni_glue he, moeb_zero, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂,
    mul_nonsing_inv_cancel_right _ _ (by rw [det_uni]; exact isUnit_one), vecOf_toMat]

theorem glue_surjective {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) : Function.Surjective (glue e) := by
  intro y
  set M := reindex e e (uni y) with hM
  let y1 : Low q → ℂ := fun s => M (.inr s.1.1) (.inr s.1.2)
  refine ⟨(vecOf (M.toBlocks₁₂ * (uni y1)⁻¹), y1, fun s => M (.inl s.1.1) (.inl s.1.2)), funext fun s => ?_⟩
  obtain ⟨⟨a, b⟩, hab⟩ := s
  obtain ⟨a, rfl⟩ := e.symm.surjective a
  obtain ⟨b, rfl⟩ := e.symm.surjective b
  have hy : y ⟨(e.symm a, e.symm b), hab⟩ = M a b := by
    have hab' : e.symm b < e.symm a := hab
    simp only [hM, reindex_apply, submatrix_apply, uni, of_apply, dif_pos hab']
  rw [hy]
  simp only [glue, toMat_vecOf, Equiv.apply_symm_apply]
  rw [nonsing_inv_mul_cancel_right _ _ (by rw [det_uni]; exact isUnit_one)]
  replace hab : (e.symm b : ℕ) < e.symm a := hab
  rcases a with a | a <;> rcases b with b | b <;> simp only [he.1, he.2] at hab
  · have : b < a := by rw [Fin.lt_def]; omega
    simp [uni, this]
  · rfl
  · have := a.2; omega
  · have : b < a := hab
    simp [uni, this, y1]

theorem continuous_uni : Continuous (uni : (Low m → ℂ) → Matrix (Fin m) (Fin m) ℂ) := by
  refine continuous_matrix fun a b => ?_
  simp only [uni, of_apply]
  split_ifs <;> fun_prop

theorem continuous_toMat : Continuous (toMat : (Fin p × Fin q → ℂ) → Matrix (Fin p) (Fin q) ℂ) :=
  continuous_matrix fun a b => continuous_apply (a, b)

theorem continuous_glue (e : Fin r ≃ Fin p ⊕ Fin q) : Continuous (glue e) := by
  refine continuous_pi fun s => ?_
  have h1 : Continuous fun w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ) => uni w.2.1 :=
    continuous_uni.comp (by fun_prop)
  have h2 : Continuous fun w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ) => uni w.2.2 :=
    continuous_uni.comp (by fun_prop)
  exact (h2.matrix_fromBlocks ((continuous_toMat.comp continuous_fst).matrix_mul h1) continuous_const h1).matrix_elem _ _

theorem measurable_dens (A : Matrix (Fin m) (Fin m) ℂ) : Measurable (dens A) := by
  refine Finset.measurable_prod _ fun i _ => Measurable.pow_const (Continuous.measurable (Continuous.norm ?_)) _
  exact (((continuous_uni.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_uni).matrix_submatrix _ _).matrix_det

theorem dens_nonneg (A : Matrix (Fin m) (Fin m) ℂ) (y : Low m → ℂ) : 0 ≤ dens A y :=
  Finset.prod_nonneg fun _ _ => zpow_nonneg (norm_nonneg _) _

theorem measurable_moeb_zero {α : Type} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {g : α → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hg : Continuous g) (a : Fin p) (b : Fin q) :
    Measurable fun x => moeb (g x) 0 a b := by
  have h2 : Continuous fun x => (g x).toBlocks₂₂ := continuous_matrix fun _ _ => hg.matrix_elem _ _
  simp only [moeb_zero, mul_apply, inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact Finset.measurable_sum _ fun c _ => (hg.matrix_elem (.inl a) (.inr c)).measurable.mul
    (h2.matrix_det.measurable.inv.mul (h2.matrix_adjugate.matrix_elem _ _).measurable)

theorem measurable_base (e : Fin r ≃ Fin p ⊕ Fin q) : Measurable (base e) :=
  measurable_pi_lambda _ fun s => measurable_moeb_zero (continuous_uni.matrix_submatrix _ _) s.1 s.2

theorem det_shear (A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Z : Matrix (Fin p) (Fin q) ℂ) :
    (shear A Z).det = A.det := by
  simp [shear, det_conjTranspose, det_fromBlocks_zero₂₁]

theorem posDef_shear {A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hA : A.PosDef) (Z : Matrix (Fin p) (Fin q) ℂ) :
    (shear A Z).PosDef :=
  hA.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).2
    (by simp [det_fromBlocks_zero₂₁])))

theorem det_eq_mul_schur {H : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUnit H.toBlocks₂₂.det) :
    H.det = H.toBlocks₂₂.det * (schur H).det := by
  letI := invertibleOfIsUnitDet _ h
  conv_lhs => rw [← fromBlocks_toBlocks H, det_fromBlocks₂₂]
  rw [schur, invOf_eq_nonsing_inv]

theorem posDef_blocks {H : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : H.PosDef) :
    H.toBlocks₁₁.PosDef ∧ H.toBlocks₂₂.PosDef ∧ (schur H).PosDef := by
  have h1 : H.toBlocks₁₁.PosDef := h.submatrix Sum.inl_injective
  have h2 : H.toBlocks₂₂.PosDef := h.submatrix Sum.inr_injective
  refine ⟨h1, h2, ?_⟩
  letI := invertibleOfIsUnitDet _ h2.det_pos.ne'.isUnit
  have e : H.toBlocks₂₁ = H.toBlocks₁₂ᴴ := by
    ext a b
    exact (h.1.apply _ _).symm
  have h3 := h.posSemidef
  rw [← fromBlocks_toBlocks H, e, PosDef.fromBlocks₂₂ _ _ h2, ← e] at h3
  refine h3.posDef_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 ?_)
  have h4 := h.det_pos.ne'
  rw [det_eq_mul_schur h2.det_pos.ne'.isUnit] at h4
  exact (right_ne_zero_of_mul h4).isUnit

section Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (X : Data E r) {j : ℕ} (hj : j ≤ r) {Tau : Type}
  (ι : Tau → X.Ψ)

def coords (z : V (nd X)) : Tau → Low r → ℂ := fun t s => z (Fintype.equivFin (Ent X) ⟨ι t, s⟩)

def proj (z : V (nd X)) : Tau × Fin j × Fin (r - j) → ℂ := flat (domPt X hj ι (cpt X (x0F X) z))

theorem mat_nmat (z : V (nd X)) (t : Tau) : mat (nmat X z) (ι t) = uni (coords X ι z t) := rfl

theorem measurable_domPt : Measurable fun x : Frame X.Ψ r => flat (domPt X hj ι x) :=
  measurable_pi_lambda _ fun s => measurable_moeb_zero
    ((continuous_const.matrix_mul (KU.cont_mat X (ι s.1))).matrix_submatrix _ _) s.2.1 s.2.2

theorem measurable_proj : Measurable (proj X hj ι) := (measurable_domPt X hj ι).comp (KU.cont_cpt X _).measurable

theorem proj_eq (z : V (nd X)) (t : Tau) (s : Fin j × Fin (r - j)) :
    proj X hj ι z (t, s) = base (idx hj) (coords X ι z t) s := by
  have e : frameCo X hj (cpt X (x0F X) z) (ι t) = reindex (idx hj) (idx hj) (uni (coords X ι z t)) := by
    rw [frameCo, ← mat_nmat]
    congr 1
    exact nonsing_inv_mul_cancel_left _ _ (det_x0F X (ι t)).isUnit
  simp only [proj, flat, domPt, base, vecOf, e]

theorem dmin_cpt (z : V (nd X)) (t : Tau) (i : Fin (r + 1)) :
    dmin X.Gm (cpt X (x0F X) z) (ι t) i =
      lminor ((uni (coords X ι z t))ᴴ * sgnMat r X.p0 * uni (coords X ι z t)) i := by
  have h0 := congrArg transpose (isOrth_x0F X (ι t))
  rw [gram_eq_mul, diagonal_transpose] at h0
  have h1 := gram_eq_mul (ι t).1 X.Gm (mat (cpt X (x0F X) z) (ι t))
  have e : mat (cpt X (x0F X) z) (ι t) = mat (x0F X) (ι t) * uni (coords X ι z t) := rfl
  rw [sgnMat, ← h0, dmin, lminor, ← det_transpose, transpose_submatrix, h1, e, lminor]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

end Data

end GlobalTheory.FlagFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAndFderivMoebI
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.HodgeDomain.ActionDeriv

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem isOpen_domFlat : IsOpen (DomFlat ι p q) := by
  refine isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_
  have h : ∀ᶠ x in nhds x0, ∀ τ, (1 - (unflat x τ)ᴴ * unflat x τ).PosDef := by
    refine Filter.eventually_all.2 fun τ => ExhB.posDef_eventually _ (fun a b => ?_)
      (fun x => isHermitian_one.sub (isHermitian_conjTranspose_mul_self _)) x0 (hx0 τ)
    simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, unflat, Matrix.of_apply]
    fun_prop
  exact h

theorem diffOn_det {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {s : Set V} {n : ℕ}
    {M : V → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, ContDiffOn ℂ 1 (fun z => M z a b) s) :
    ContDiffOn ℂ 1 (fun z => (M z).det) s := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem diffOn_inv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {s : Set V} {n : ℕ}
    {M : V → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, ContDiffOn ℂ 1 (fun z => M z a b) s)
    (hd : ∀ z ∈ s, (M z).det ≠ 0) (a b : Fin n) : ContDiffOn ℂ 1 (fun z => (M z)⁻¹ a b) s := by
  have hadj : ContDiffOn ℂ 1 (fun z => (M z).adjugate a b) s := by
    simp only [adjugate_apply]
    refine diffOn_det fun i j => ?_
    by_cases e : i = b
    · simp only [e, updateRow_self]; exact contDiffOn_const
    · simp only [updateRow_ne e]; exact h i j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact ContDiffOn.mul (ContDiffOn.inv (diffOn_det h) hd) hadj

theorem diffOn_moebI {g : ι → GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ UpqI ι p q) :
    DifferentiableOn ℂ (fun v => flat (moebI g (unflat v))) (DomFlat ι p q) := by
  refine differentiableOn_pi.2 fun x => ?_
  obtain ⟨τ, a, b⟩ := x
  refine ContDiffOn.differentiableOn (n := 1) ?_ one_ne_zero
  have hinv : ∀ k, ContDiffOn ℂ 1 (fun v => (kapQ (g τ) (unflat v τ))⁻¹ k b) (DomFlat ι p q) := by
    intro k
    refine diffOn_inv (s := DomFlat ι p q) (M := fun v => kapQ (g τ) (unflat v τ)) (fun i j => ?_) (fun v hv => (kapQ_isUnit (hg τ (Set.mem_univ _)) (hv τ)).ne_zero) k b
    simp only [kapQ, Matrix.add_apply, Matrix.mul_apply, unflat, Matrix.of_apply]
    fun_prop
  simp only [flat, moebI, moeb, Matrix.mul_apply]
  refine ContDiffOn.sum fun k _ => ContDiffOn.mul ?_ (hinv k)
  simp only [Matrix.add_apply, Matrix.mul_apply, unflat, Matrix.of_apply]
  fun_prop

theorem hasDerivAt_affine {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin m) (Fin k) ℂ)
    (z ξ : Matrix (Fin n) (Fin k) ℂ) (a : Fin m) (b : Fin k) :
    HasDerivAt (fun t : ℂ => (A * (z + t • ξ) + B) a b) ((A * ξ) a b) 0 := by
  have e : (fun t : ℂ => (A * (z + t • ξ) + B) a b) = fun t => t * (A * ξ) a b + (A * z + B) a b := by
    funext t
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [e]
  simpa using ((hasDerivAt_id (0 : ℂ)).mul_const ((A * ξ) a b)).add_const ((A * z + B) a b)

theorem fderiv_moebI {g : ι → GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ UpqI ι p q) {z : Pt ι p q} (hz : z ∈ DomI ι p q)
    (ξ : Pt ι p q) :
    fderiv ℂ (fun v => flat (moebI g (unflat v))) (flat z) (flat ξ) =
      flat (fun τ => tanAct (g τ) (z τ) (ξ τ)) := by
  have hz' : flat z ∈ DomFlat ι p q := hz
  have hn := isOpen_domFlat.mem_nhds hz'
  have hF := ((diffOn_moebI hg).differentiableAt hn).hasFDerivAt
  set D := fderiv ℂ (fun v => flat (moebI g (unflat v))) (flat z) (flat ξ) with hD
  have hc : HasDerivAt (fun t : ℂ => flat z + t • flat ξ) (flat ξ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (flat ξ)).const_add (flat z)
  have hW : HasDerivAt (fun t : ℂ => flat (moebI g (unflat (flat z + t • flat ξ)))) D 0 :=
    hF.comp_hasDerivAt_of_eq (0 : ℂ) hc (by simp)
  have hev : ∀ᶠ t : ℂ in nhds 0, flat z + t • flat ξ ∈ DomFlat ι p q :=
    hc.continuousAt.eventually_mem (by simpa using hn)
  funext x
  obtain ⟨τ, a, b⟩ := x
  have hgτ := hg τ (Set.mem_univ _)
  have key : unflat D τ * kapQ (g τ) (z τ) = jW (g τ) (z τ) * ξ τ := by
    rw [jW, Matrix.sub_mul, eq_sub_iff_add_eq, Matrix.mul_assoc]
    ext i j
    have h1 := hasDerivAt_affine (g τ).1.toBlocks₁₁ (g τ).1.toBlocks₁₂ (z τ) (ξ τ) i j
    have h2 := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hasDerivAt_pi.1 hW (τ, i, k)).mul (hasDerivAt_affine (g τ).1.toBlocks₂₁ (g τ).1.toBlocks₂₂ (z τ) (ξ τ) k j)
    have h3 := h2.congr_of_eventuallyEq (f₁ := fun t : ℂ =>
      ((g τ).1.toBlocks₁₁ * (z τ + t • ξ τ) + (g τ).1.toBlocks₁₂) i j) (by
        filter_upwards [hev] with t ht
        have := moeb_mul_kapQ hgτ (ht τ)
        exact (congrFun (congrFun this i) j).symm)
    rw [h1.unique h3, Finset.sum_add_distrib, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [zero_smul, add_zero]
    rfl
  have e : unflat D τ = tanAct (g τ) (z τ) (ξ τ) := by
    rw [tanAct, ← key, mul_nonsing_inv_cancel_right _ _ (kapQ_isUnit hgτ (hz τ))]
  exact congrFun (congrFun e a) b

theorem isOpen_and_fderiv_moebI : ∀ (ι : Type) [Fintype ι] (p q : ℕ), IsOpen (DomFlat ι p q) ∧ ∀ g ∈ UpqI ι p q, DifferentiableOn ℂ (fun v => flat (moebI g (unflat v))) (DomFlat ι p q) ∧ ∀ z ∈ DomI ι p q, ∀ ξ : Pt ι p q, fderiv ℂ (fun v => flat (moebI g (unflat v))) (flat z) (flat ξ) = flat (fun τ => tanAct (g τ) (z τ) (ξ τ)) :=
  fun _ _ _ _ => ⟨isOpen_domFlat, fun _ hg => ⟨diffOn_moebI hg, fun _ hz ξ => fderiv_moebI hg hz ξ⟩⟩

end GlobalTheory.HodgeDomain.ActionDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStableOfNoBoundary
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.Models

namespace GlobalTheory.FiniteStable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem aut_bar (σ : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E) : σ (H.bar a) = H.bar (σ a) := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  let s : E ≃+* E := IsFractionRing.ringEquivOfRingEquiv σ
  have hs : ∀ x : 𝓞 E, ((σ x : 𝓞 E) : E) = s x := fun x =>
    (IsFractionRing.ringEquivOfRingEquiv_algebraMap σ x).symm
  apply RingOfIntegers.ext
  apply φ.injective
  rw [H.bar_eq, hs, hs, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  exact IsCMField.complexEmbedding_complexConj E (φ.comp s.toRingHom) _

@[reducible] def twist (σ : 𝓞 E ≃+* 𝓞 E) (hσ : σ H.w0 = H.w0) {S : Scheme.{0}} (t : SAB H S) : SAB H S where
  G := t.G
  semi := t.semi
  act :=
    { act := fun a => t.act.act (σ a)
      hom := fun a => t.act.hom _
      one := by rw [map_one, t.act.one]
      mul := fun a b => by rw [map_mul, t.act.mul]
      add := fun a b => by rw [map_add, t.act.add] }
  PP := t.PP
  cub := t.cub
  sym := t.sym
  adj a := by
    have := t.adj (σ a)
    rwa [← aut_bar] at this
  prim := by
    have := t.prim
    rwa [← hσ] at this

def twistCpt (σ : 𝓞 E ≃+* 𝓞 E) (hσ : σ H.w0 = H.w0) {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O]
    {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F} (C : Cpt c t β) : Cpt c (twist σ hσ t) β :=
  ⟨C.X, C.s, C.normal, C.proj, C.flat, C.jQ, C.jQ_over, C.jQ_open, C.jQ_dense, twist σ hσ C.t,
    ⟨C.m.cm, C.m.cart, C.m.base, fun a => C.m.act (σ a), C.m.lin⟩, C.ab_gen⟩

theorem exists_ext {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O]
    {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F} (C : Cpt c t β) (hβ : IsDedFrac β) (hO : Algebra.FiniteType ℤ O)
    (hs : IsFinite C.s) (γ : F →+* F) (γ₀ : O →+* O) (hγ : ∀ x, β (γ₀ x) = γ (β x)) (r : U ⟶ U)
    (hr : r ≫ c = c ≫ spMap γ) : ∃ ρ : C.X ⟶ C.X, ρ ≫ C.s = C.s ≫ spMap γ₀ ∧ C.j ≫ ρ = r ≫ C.j := by
  obtain ⟨-, h1, h2, h3, h4⟩ := C.arith_and_proOpen hβ hO
  have hj : C.j ≫ C.s = c ≫ spMap β := by
    rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]
  have e : spMap β ≫ spMap γ₀ = spMap γ ≫ spMap β := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact hγ x
  have : IsLocallyNoetherian C.X := by
    obtain ⟨⟨_, _⟩, -, hfr⟩ := hβ
    letI := β.toAlgebra
    exact (GlobalTheory.genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense).1
  obtain ⟨ρ, ⟨k1, k2⟩, -⟩ := GlobalTheory.existsUnique_lift_of_densePart C.X U _ C.X C.j C.normal h1 h2 h3 h4
    C.s (C.s ≫ spMap γ₀) (r ≫ C.j) inferInstance (by
      rw [Category.assoc, hj, reassoc_of% hj, reassoc_of% hr, e])
  exact ⟨ρ, k2, k1⟩

end GlobalTheory.FiniteStable
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaSeriesRationalOnGoodCoversOfUntwistedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeriesRationalOnGoodCovers_of_untwisted : GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.UntwRatS → GlobalTheory.SerStd.SeriesRatS := by
  first | exact @GlobalTheory.SerStdTwist.seriesRatS_of_untwRatS | exact GlobalTheory.SerStdTwist.seriesRatS_of_untwRatS | (intros; apply GlobalTheory.SerStdTwist.seriesRatS_of_untwRatS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationTorus_mono_and_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (t : SAB H (Sp R)) (P : PELUnif I t)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (a : R →+* A) (e : ℕ) (ha : ∀ x ∈ I ^ (e + 1), a x = 0)
    (G₀ : Over (Sp A)) [GrpObj G₀] (φ : G₀.left ⟶ t.G.left) (h : IsGrpPullback G₀ t.G (spMap a) φ),
    Mono (GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha h) ∧
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp A) X ⟶ G₀), IsMonHom i →
      ∃ ρ : P.D.toPre.X →+ X, i = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha h := by
  first | exact @GlobalTheory.TorusPart.mono_gtTorus_unif_and_factor | exact GlobalTheory.TorusPart.mono_gtTorus_unif_and_factor | (intros; apply GlobalTheory.TorusPart.mono_gtTorus_unif_and_factor <;> assumption)
end

