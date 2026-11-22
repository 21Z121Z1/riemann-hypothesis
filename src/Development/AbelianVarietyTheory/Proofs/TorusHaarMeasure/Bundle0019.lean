import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SublatticeCoefficients
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0009
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DifferentiableAtAdjugate
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.UnitriJac

open ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf

noncomputable section

abbrev Low (r : ℕ) : Type := {p : Fin r × Fin r // p.2 < p.1}

def lowMat {r : ℕ} (u : Low r → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a c => if h : c < a then u ⟨(a, c), h⟩ else 0

theorem sum_low {r : ℕ} (u : Low r → ℂ) (f : Fin r → Fin r → ℂ) :
    ∑ q : Low r, f q.1.1 q.1.2 * u q = ∑ a, ∑ c, f a c * lowMat u a c := by
  rw [← Fintype.sum_prod_type']
  have h1 : ∑ q : Low r, f q.1.1 q.1.2 * u q
      = ∑ q : Low r, f q.1.1 q.1.2 * lowMat u q.1.1 q.1.2 := by
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [lowMat, q.2]
  rw [h1, ← Finset.sum_subtype (Finset.univ.filter fun p : Fin r × Fin r => p.2 < p.1) (by simp)
    (fun p : Fin r × Fin r => f p.1 p.2 * lowMat u p.1 p.2), Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs with h
  · rfl
  · simp [lowMat, h]

def leftM {r : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) : Matrix (Low r) (Low r) ℂ :=
  Matrix.of fun p q : Low r => if p.1.2 = q.1.2 then N p.1.1 q.1.1 else 0

def adM {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) : Matrix (Low r) (Low r) ℂ :=
  Matrix.of fun p q : Low r => B p.1.1 q.1.1 * B⁻¹ q.1.2 p.1.2

theorem leftM_mulVec {r : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) (u : Low r → ℂ) (p : Low r) :
    (leftM N *ᵥ u) p = (N * lowMat u) p.1.1 p.1.2 := by
  have := sum_low u (fun a c => if p.1.2 = c then N p.1.1 a else 0)
  simp only [Matrix.mulVec, dotProduct, leftM, Matrix.of_apply]
  rw [this, Matrix.mul_apply]
  simp

theorem adM_mulVec {r : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (u : Low r → ℂ) (p : Low r) :
    (adM B *ᵥ u) p = (B * lowMat u * B⁻¹) p.1.1 p.1.2 := by
  have := sum_low u (fun a c => B p.1.1 a * B⁻¹ c p.1.2)
  simp only [Matrix.mulVec, dotProduct, adM, Matrix.of_apply]
  rw [this, Matrix.mul_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem lowMat_leftM {r : ℕ} {N : Matrix (Fin r) (Fin r) ℂ} (hN : LowU N) (u : Low r → ℂ) :
    lowMat (leftM N *ᵥ u) = N * lowMat u := by
  ext a c
  by_cases h : c < a
  · simp only [lowMat, Matrix.of_apply, dif_pos h]
    exact leftM_mulVec N u ⟨(a, c), h⟩
  · rw [Matrix.mul_apply]
    simp only [lowMat, Matrix.of_apply, dif_neg h]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : c < k
    · rw [hN.1 a k (lt_of_le_of_lt (not_lt.mp h) hk), zero_mul]
    · rw [dif_neg hk, mul_zero]

theorem differentiableAt_det {r : ℕ} (A : ℂ → Matrix (Fin r) (Fin r) ℂ) (t : ℂ)
    (h : ∀ i j, DifferentiableAt ℂ (fun s => A s i j) t) :
    DifferentiableAt ℂ (fun s => (A s).det) t := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_mul ?_ _
  exact DifferentiableAt.fun_finsetProd fun i _ => h _ _

theorem differentiableAt_adjugate {r : ℕ} (A : ℂ → Matrix (Fin r) (Fin r) ℂ) (t : ℂ)
    (h : ∀ i j, DifferentiableAt ℂ (fun s => A s i j) t) (i j : Fin r) :
    DifferentiableAt ℂ (fun s => (A s).adjugate i j) t := by
  simp only [Matrix.adjugate_apply]
  refine differentiableAt_det _ t fun k l => ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableAt_const _
  · exact h _ _

theorem hasDerivAt_mul {r : ℕ} {A B : ℂ → Matrix (Fin r) (Fin r) ℂ} {A' B' : Matrix (Fin r) (Fin r) ℂ}
    {t : ℂ} (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (B' i j) t) (i j : Fin r) :
    HasDerivAt (fun s => (A s * B s) i j) ((A' * B t + A t * B') i j) t := by
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => (hA i k).fun_mul (hB k j)

theorem deriv_rel {r : ℕ} {N M b : ℂ → Matrix (Fin r) (Fin r) ℂ} {g N' M' : Matrix (Fin r) (Fin r) ℂ}
    (hN : ∀ i j, HasDerivAt (fun s => N s i j) (N' i j) 0)
    (hM : ∀ i j, HasDerivAt (fun s => M s i j) (M' i j) 0)
    (hMd : ∀ s, (M s).det = 1) (hNd : (N 0).det = 1) (hbd : (b 0).det ≠ 0)
    (h : ∀ᶠ s in 𝓝 (0 : ℂ), g * N s = M s * b s ∧ ∀ a c : Fin r, c < a → b s a c = 0)
    (a c : Fin r) (hca : c < a) :
    ((M 0)⁻¹ * M') a c = (b 0 * ((N 0)⁻¹ * N') * (b 0)⁻¹) a c := by
  have hgN : ∀ i j, HasDerivAt (fun s => (g * N s) i j) ((g * N') i j) 0 := by
    intro i j
    have := hasDerivAt_mul (A := fun _ => g) (A' := 0) (fun i j => hasDerivAt_const _ _) hN i j
    simpa using this
  have hbe : ∀ i j, (fun s => b s i j) =ᶠ[𝓝 0] fun s => ((M s).adjugate * (g * N s)) i j := by
    intro i j
    filter_upwards [h] with s hs
    rw [hs.1, ← Matrix.mul_assoc, Matrix.adjugate_mul, hMd, one_smul, Matrix.one_mul]
  have hbdiff : ∀ i j, DifferentiableAt ℂ (fun s => b s i j) 0 := by
    intro i j
    refine DifferentiableAt.congr_of_eventuallyEq ?_ (hbe i j)
    exact (hasDerivAt_mul (A := fun s => (M s).adjugate)
      (A' := Matrix.of fun i j => deriv (fun s => (M s).adjugate i j) 0)
      (fun i j => (differentiableAt_adjugate M 0 (fun i j => (hM i j).differentiableAt) i j).hasDerivAt)
      hgN i j).differentiableAt
  set b' : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i j => deriv (fun s => b s i j) 0 with hb'
  have hb : ∀ i j, HasDerivAt (fun s => b s i j) (b' i j) 0 := fun i j => (hbdiff i j).hasDerivAt
  have hup : b'.BlockTriangular id := by
    intro i j hij
    have : (fun s => b s i j) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [h] with s hs using hs.2 i j hij
    show deriv (fun s => b s i j) 0 = 0
    rw [this.deriv_eq]; simp
  have hrel : g * N' = M' * b 0 + M 0 * b' := by
    ext i j
    refine (hgN i j).unique (HasDerivAt.congr_of_eventuallyEq (hasDerivAt_mul hM hb i j) ?_)
    filter_upwards [h] with s hs
    rw [hs.1]
  have h0 := h.self_of_nhds
  have uM : IsUnit (M 0).det := by rw [hMd]; exact isUnit_one
  have uN : IsUnit (N 0).det := by rw [hNd]; exact isUnit_one
  have ub : IsUnit (b 0).det := isUnit_iff_ne_zero.mpr hbd
  have hg : g = M 0 * b 0 * (N 0)⁻¹ := by
    rw [← h0.1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ uN, Matrix.mul_one]
  have key : b 0 * ((N 0)⁻¹ * N') * (b 0)⁻¹ = (M 0)⁻¹ * M' + b' * (b 0)⁻¹ := by
    have e1 : b 0 * ((N 0)⁻¹ * N') = (M 0)⁻¹ * (g * N') := by
      rw [hg]
      simp only [← Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul _ uM, Matrix.one_mul]
    rw [e1, hrel, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc (M 0)⁻¹ (M 0),
      Matrix.nonsing_inv_mul _ uM, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ ub, Matrix.mul_one]
  have hbinv : ((b 0)⁻¹).BlockTriangular id := by
    let _ := Matrix.invertibleOfIsUnitDet _ ub
    exact Matrix.blockTriangular_inv_of_blockTriangular fun i j hij => h0.2 i j hij
  rw [key, Matrix.add_apply, (hup.mul hbinv) hca, add_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def crd {r : ℕ} (X : Data E r) (v : V (nd X)) (τ : X.Ψ) : Low r → ℂ :=
  fun p => v ((Fintype.equivFin (Ent X)) ⟨τ, p⟩)

theorem hasDerivAt_nmat {r : ℕ} (X : Data E r) {w : ℂ → V (nd X)} {w' : V (nd X)} {t : ℂ}
    (hw : HasDerivAt w w' t) (τ : X.Ψ) (i j : Fin r) :
    HasDerivAt (fun s => mat (nmat X (w s)) τ i j) (lowMat (crd X w' τ) i j) t := by
  simp only [mat, nmat, lowMat, Matrix.of_apply]
  by_cases h : j < i
  · simp only [dif_pos h, crd]
    exact (EuclideanSpace.proj (𝕜 := ℂ)
      ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(i, j), h⟩⟩)).hasFDerivAt.comp_hasDerivAt t hw
  · simp only [dif_neg h]
    exact hasDerivAt_const _ _

theorem fderiv_rel {r : ℕ} (X : Data E r) (x0 x1 : Frame X.Ψ r) (γ : GL (Fin r) E) (U : Set (V (nd X)))
    (Φ : V (nd X) → V (nd X)) (bf : V (nd X) → Frame X.Ψ r) (hU : IsOpen U)
    (hΦ : DifferentiableOn ℂ Φ U)
    (h : ∀ z ∈ U, cpt X x0 z ∈ X.dom ∧ bf z ∈ Bor X.Ψ r ∧
      cpt X x0 z = lact γ (rmul (cpt X x1 (Φ z)) (bf z)))
    (z : V (nd X)) (hz : z ∈ U) (v : V (nd X)) (τ : X.Ψ) :
    leftM (mat (nmat X (Φ z)) τ)⁻¹ *ᵥ crd X (fderiv ℂ Φ z v) τ =
      (adM (mat (bf z) τ) * leftM (mat (nmat X z) τ)⁻¹) *ᵥ crd X v τ := by
  set G : Matrix (Fin r) (Fin r) ℂ := (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ with hG
  have hrel : ∀ y ∈ U, mat x0 τ * mat (nmat X y) τ = G * (mat (nmat X (Φ y)) τ * mat (bf y) τ) := by
    intro y hy
    have := congrFun (h y hy).2.2 τ
    rw [hG, Matrix.mul_assoc, ← Matrix.mul_assoc (mat x1 τ)]
    exact this
  have uG : IsUnit G.det := by
    have h1 : (mat x0 τ * mat (nmat X z) τ).det ≠ 0 := ((h z hz).1 τ).1
    rw [hrel z hz, Matrix.det_mul] at h1
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul h1)
  have hl : HasDerivAt (fun s : ℂ => z + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
  have hΦz : HasFDerivAt Φ (fderiv ℂ Φ z) (z + (0 : ℂ) • v) := by
    simpa using (hΦ.differentiableAt (hU.mem_nhds hz)).hasFDerivAt
  have hl2 : HasDerivAt (fun s : ℂ => Φ (z + s • v)) (fderiv ℂ Φ z v) 0 :=
    hΦz.comp_hasDerivAt (0 : ℂ) hl
  have hev : ∀ᶠ s in 𝓝 (0 : ℂ), z + s • v ∈ U :=
    hl.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simpa using hz))
  funext p
  have := deriv_rel (N := fun s => mat (nmat X (z + s • v)) τ)
    (M := fun s => mat (nmat X (Φ (z + s • v))) τ) (b := fun s => mat (bf (z + s • v)) τ)
    (g := G⁻¹ * mat x0 τ) (hasDerivAt_nmat X hl τ) (hasDerivAt_nmat X hl2 τ)
    (fun s => (nmat_lowU X _ τ).det) (nmat_lowU X _ τ).det
    (by simpa using ((h z hz).2.1 τ).1)
    (by
      filter_upwards [hev] with s hs
      refine ⟨?_, fun a c hca => ((h _ hs).2.1 τ).2 a c hca⟩
      rw [Matrix.mul_assoc, hrel _ hs, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ uG, Matrix.one_mul])
    p.1.1 p.1.2 p.2
  simp only [zero_smul, add_zero] at this
  rw [leftM_mulVec, ← Matrix.mulVec_mulVec, adM_mulVec, lowMat_leftM (nmat_lowU X z τ).inv]
  exact this

theorem blockDiagonal_mulVec {m o : Type} [Fintype m] [Fintype o] [DecidableEq o]
    (A : o → Matrix m m ℂ) (u : m × o → ℂ) (p : m) (τ : o) :
    (Matrix.blockDiagonal A *ᵥ u) (p, τ) = (A τ *ᵥ fun q => u (q, τ)) p := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.blockDiagonal_apply]

theorem kapGG_of_det :
    (∀ (r : ℕ) (B : Matrix (Fin r) (Fin r) ℂ), B.det ≠ 0 → (∀ a c : Fin r, c < a → B a c = 0) → (Matrix.of fun p q : {p : Fin r × Fin r // p.2 < p.1} => B p.1.1 q.1.1 * B⁻¹ q.1.2 p.1.2).det = ∏ a : Fin r, B a a ^ (2 * (a : ℤ) - ((r : ℤ) - 1))) → (∀ (r : ℕ) (N : Matrix (Fin r) (Fin r) ℂ), (∀ a c : Fin r, a < c → N a c = 0) → (∀ a, N a a = 1) → (Matrix.of fun p q : {p : Fin r × Fin r // p.2 < p.1} => if p.1.2 = q.1.2 then N p.1.1 q.1.1 else 0).det = 1) → (KapGGStatement (E := E)) := by
  classical
  intro hAd hL r X x0 x1 γ U Φ bf hU hΦ h z hz
  let e : Low r × X.Ψ ≃ Fin (nd X) := (Equiv.prodComm _ _).trans (Fintype.equivFin (Ent X))
  let β : Module.Basis (Low r × X.Ψ) ℂ (V (nd X)) :=
    (EuclideanSpace.basisFun (Fin (nd X)) ℂ).toBasis.reindex e.symm
  have hβ : ∀ (v : V (nd X)) (τ : X.Ψ), (fun q => β.repr v (q, τ)) = crd X v τ := by
    intro v τ
    funext q
    simp only [β, Module.Basis.repr_reindex_apply, Equiv.symm_symm,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
    rfl
  set D : V (nd X) →ₗ[ℂ] V (nd X) := (fderiv ℂ Φ z).toLinearMap with hD
  have hmat : Matrix.blockDiagonal (fun τ => leftM (mat (nmat X (Φ z)) τ)⁻¹) * LinearMap.toMatrix β β D =
      Matrix.blockDiagonal (fun τ => adM (mat (bf z) τ) * leftM (mat (nmat X z) τ)⁻¹) := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    obtain ⟨v, rfl⟩ : ∃ v, (β.repr v : Low r × X.Ψ → ℂ) = u := ⟨β.equivFun.symm u, by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]⟩
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix_mulVec_repr]
    funext ⟨p, τ⟩
    rw [blockDiagonal_mulVec, blockDiagonal_mulVec, hβ, hβ]
    exact congrFun (fderiv_rel X x0 x1 γ U Φ bf hU hΦ h z hz v τ) p
  have hdet := congrArg Matrix.det hmat
  have hL' : ∀ (y : V (nd X)) (τ : X.Ψ), (leftM (mat (nmat X y) τ)⁻¹).det = 1 := fun y τ => by
    have := hL r _ (nmat_lowU X y τ).inv.1 (nmat_lowU X y τ).inv.2
    exact this
  have hA' : ∀ τ : X.Ψ, (adM (mat (bf z) τ)).det = ∏ a : Fin r, bf z τ a a ^ kapW X τ a := fun τ => by
    have := hAd r (mat (bf z) τ) ((h z hz).2.1 τ).1 ((h z hz).2.1 τ).2
    exact this
  rw [Matrix.det_mul, Matrix.det_blockDiagonal, Matrix.det_blockDiagonal, LinearMap.det_toMatrix] at hdet
  simp only [Matrix.det_mul, hL', hA', Finset.prod_const_one, one_mul, mul_one] at hdet
  exact hdet

end

end GlobalTheory.UnitriJac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.NormFactor

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma nfac_eq_prod_norm_dmin_ratio_rpow {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    X.nfac la x = ∏ τ, ∏ i : Fin r,
      ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.nfac _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
  rfl

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma blockTriangular_id_of_mem_bor {r : ℕ} {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r} (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r)
    (τ : Ψ) : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).BlockTriangular id := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor at hb
  intro a c hca
  exact (hb τ).2 a c hca

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma mat_diag_ne_zero_of_mem_bor {r : ℕ} {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r}
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) (τ : Ψ) (j : Fin r) : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ j j ≠ 0 := by
  have hdet := (show (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0 by unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor at hb; exact (hb τ).1)
  rw [Matrix.det_of_upperTriangular (blockTriangular_id_of_mem_bor hb τ)] at hdet
  exact Finset.prod_ne_zero_iff.1 hdet j (Finset.mem_univ j)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma diag_prod_ne_zero_of_mem_bor {r : ℕ} {Ψ : Finset (E →+* ℂ)} {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r}
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r) (τ : Ψ) (i : Fin (r + 1)) :
    ∏ j : Fin i, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => mat_diag_ne_zero_of_mem_bor hb τ _

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma gram_rmul_eq_transpose_mul_gram {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ) =
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).transpose * _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ).map (starRingEnd ℂ) := by
  have hmul : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul
    conv_lhs => unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    rfl
  rw [hmul, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_mul]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma dmin_rmul_eq_diag_prod_mul_conj {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r)
    (τ : X.Ψ) (i : Fin (r + 1)) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ i = (∏ j : Fin i, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)) *
      _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i * starRingEnd ℂ (∏ j : Fin i, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
  rw [gram_rmul_eq_transpose_mul_gram]
  exact _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_conj (blockTriangular_id_of_mem_bor hb τ) i

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma diag_prod_succ {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (i : Fin r) :
    ∏ j : Fin (i.succ : ℕ), M (Fin.castLE (by omega) j) (Fin.castLE (by omega) j) =
      (∏ j : Fin (i.castSucc : ℕ), M (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)) * M i i := by
  show ∏ j : Fin ((i : ℕ) + 1), M (Fin.castLE (by omega) j) (Fin.castLE (by omega) j) = _
  rw [Fin.prod_univ_castSucc]
  rfl

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma norm_ratio_rmul_lemma_2 {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r) (τ : X.Ψ) (i : Fin r) :
    ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ i.castSucc‖ =
      ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ i i‖ ^ 2 * ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ := by
  have hp := diag_prod_ne_zero_of_mem_bor hb τ i.castSucc
  rw [dmin_rmul_eq_diag_prod_mul_conj X x b hb τ i.succ, dmin_rmul_eq_diag_prod_mul_conj X x b hb τ i.castSucc, diag_prod_succ]
  simp only [norm_div, norm_mul, map_mul, RCLike.norm_conj]
  have hp' : ‖∏ j : Fin (i.castSucc : ℕ), _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ (Fin.castLE (by omega) j) (Fin.castLE (by omega) j)‖ ≠ 0 :=
    norm_ne_zero_iff.2 hp
  by_cases hm : ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ = 0
  · simp [hm]
  · field_simp

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma rpow_sq_mul_eq_inv_zpow_mul_rpow {d t : ℝ} (hd : 0 ≤ d) (ht : 0 ≤ t) (l : ℤ) :
    (d ^ 2 * t) ^ (-(l : ℝ) / 2) = (d ^ l)⁻¹ * t ^ (-(l : ℝ) / 2) := by
  rw [Real.mul_rpow (by positivity) ht, ← Real.rpow_natCast, ← Real.rpow_mul hd]
  congr 1
  rw [show ((2 : ℕ) : ℝ) * (-(l : ℝ) / 2) = -(l : ℝ) by push_cast; ring, Real.rpow_neg hd,
    Real.rpow_intCast]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.NormFactor.norm_bchar_mul_nfac_rmul {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    {x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r) :
    ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la b‖ * X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) = X.nfac la x := by
  rw [nfac_eq_prod_norm_dmin_ratio_rpow, nfac_eq_prod_norm_dmin_ratio_rpow]
  simp_rw [norm_ratio_rmul_lemma_2 X x b hb, rpow_sq_mul_eq_inv_zpow_mul_rpow (norm_nonneg _) (norm_nonneg _),
    Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have hbc : ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la b‖ = ∏ τ, ∏ i : Fin r, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ i i‖ ^ la τ i := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.bchar _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    simp [norm_prod, norm_zpow]
  have hne : ∏ τ, ∏ i : Fin r, ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ i i‖ ^ la τ i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ =>
      zpow_ne_zero _ (norm_ne_zero_iff.2 (mat_diag_ne_zero_of_mem_bor hb τ i))
  rw [hbc, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.NormFactor.nfacRmul_holds : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement (E := E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement
  intro r X la x hx b hb
  have hne : ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la b‖ ≠ 0 := norm_ne_zero_iff.2 (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.bchar_ne X la hb)
  rw [eq_inv_mul_iff_mul_eq₀ hne]
  exact _root_.GlobalTheory.NormFactor.norm_bchar_mul_nfac_rmul X la hx hb

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.NormFactor.dmin_lact {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) τ i = _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin
  rw [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.gram_lact X hγ x τ]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.NormFactor.nfacLact_holds : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement (E := E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement
  intro r X la γ hγ x _
  rw [nfac_eq_prod_norm_dmin_ratio_rpow, nfac_eq_prod_norm_dmin_ratio_rpow]
  simp only [_root_.GlobalTheory.NormFactor.dmin_lact X hγ]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.NormFactor.pnormInv_holds : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PnormInvStatement (E := E) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PnormInvStatement
  intro r X la P hP γ hγ x hx b hb
  have hpn : ∀ y, X.pnorm la P y = ‖P y‖ * X.nfac la y := by
    intro y
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    rw [nfac_eq_prod_norm_dmin_ratio_rpow]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsSec at hP
  obtain ⟨-, hPb, hPγ⟩ := hP
  have hxb := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb
  have hlact := _root_.GlobalTheory.NormFactor.nfacLact_holds (E := E)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement at hlact
  rw [hpn, hpn, hPγ γ hγ _ hxb, norm_mul, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.chi_norm X la hγ, one_mul, hlact r X la γ hγ _ hxb,
    hPb x hx b hb, norm_mul, ← _root_.GlobalTheory.NormFactor.norm_bchar_mul_nfac_rmul X la hx hb]
  ring

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.NormFactor.nfac_transform :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement (E := E) ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement (E := E) ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PnormInvStatement (E := E) :=
  ⟨_root_.GlobalTheory.NormFactor.nfacRmul_holds, _root_.GlobalTheory.NormFactor.nfacLact_holds, _root_.GlobalTheory.NormFactor.pnormInv_holds⟩

end GlobalTheory.NormFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SqLeQyOfLeFirstMinimum
section
namespace GlobalTheory.FJCompare

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.RealPointModes
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def vec (i : Idx E) : X.Ψ → ℝ := modeAt X (integralBasis (maximalRealSubfield E) i)

def SignDecayOn (S : Set ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (C A : ℝ), A ∈ S → X.IsSec la P →
    (∀ x ∈ X.dom, X.pnorm la P x ≤ C * X.la1 x ^ (-A)) →
    (∀ ξ, X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom, X.fj la ξ ν P x ≠ 0 → ∀ τ, 0 ≤ ν τ) ∧
    ∀ η : ℝ, 0 < η → η < 1 → ∃ Cη : ℝ, ∀ ξ, X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom,
      (∀ τ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1) →
      ‖X.fj la ξ ν P x‖ * X.nfac la x ≤
        Cη * X.la1 x ^ (-A) * Real.exp (-4 * Real.pi * (1 - η) * ∑ τ, ν τ * X.tt ξ x τ)

theorem SignDecayOn.mono {S T : Set ℝ} (h : SignDecayOn T E) (hST : S ⊆ T) : SignDecayOn S E :=
  fun r X la P C A hA => h r X la P C A (hST hA)

def ProductSupport (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la la' : Wt X.Ψ r) (P Q : Frame X.Ψ r → ℂ),
    X.IsSec la P → X.IsSec la' Q → X.IsModerate la P → X.IsModerate la' Q →
    ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, ∀ ν : X.Ψ → ℝ, X.fj (la + la') ξ ν (P * Q) x ≠ 0 →
      ∃ ν' : X.Ψ → ℝ, X.fj la ξ ν' P x * X.fj la' ξ (ν - ν') Q x ≠ 0

end

end GlobalTheory.FJCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.WeightedHeightSupDriftOrthonormalFramesStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.weighted_height_sup_drift_orthonormal_frames : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ (τ0 : X.Ψ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1)) → ∃ δ : ℝ, 0 < δ ∧ ∀ α : ℕ → Frame X.Ψ r → ℝ, (∀ i ≤ r, ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → IsLUB ((fun W => d x W ^ (-δ)) '' {W | Module.finrank E W = i}) (α i x)) → ∃ (e : ℕ → ℝ) (c b : ℝ), (∀ i, 0 < e i) ∧ 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ ∀ x, IsOrth X x → ∑ a ∈ S, (∑ i ∈ Finset.Ioo 0 r, e i * α i (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ))) ≤ S.card * (c * (∑ i ∈ Finset.Ioo 0 r, e i * α i x) + b)) := by
  first | exact @GlobalTheory.FiniteCovolume.weighted_sup_drift_on_orthonormal_frames | exact GlobalTheory.FiniteCovolume.weighted_sup_drift_on_orthonormal_frames | (intros; apply GlobalTheory.FiniteCovolume.weighted_sup_drift_on_orthonormal_frames <;> assumption)
end

