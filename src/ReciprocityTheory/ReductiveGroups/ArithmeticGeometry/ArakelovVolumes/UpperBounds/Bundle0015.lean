import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0009
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfC
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace ModeHalfC

open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter ModeHalfA ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates Module

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem posDef_int_lower {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef) :
    ∃ m0 : ℝ, 0 < m0 ∧ ∀ x : Fin N → ℤ, x ≠ 0 →
      m0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (x i : ℝ)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact ⟨1, one_pos, fun x hx => absurd (Subsingleton.elim x 0) hx⟩
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let q : (Fin N → ℝ) → ℝ := fun y => y ⬝ᵥ (A *ᵥ y)
  have hqc : Continuous q :=
    continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  have hpos : ∀ y : Fin N → ℝ, y ≠ 0 → 0 < q y := by
    intro y hy
    have h0 := hA.dotProduct_mulVec_pos hy
    simpa [q] using h0

  obtain ⟨y0, hy0, hmin⟩ := (isCompact_sphere (0 : Fin N → ℝ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hqc.continuousOn
  have hy0ne : y0 ≠ 0 := by
    intro h
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hy0
    exact zero_ne_one hy0
  refine ⟨q y0, hpos y0 hy0ne, fun x hx => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx (funext hc)
  have hs1 : 1 ≤ ‖(fun i => (x i : ℝ))‖ := by
    have h1 : (1 : ℝ) ≤ |(x i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
    calc (1 : ℝ) ≤ ‖(x i : ℝ)‖ := by rw [Real.norm_eq_abs]; exact h1
      _ ≤ ‖(fun i => (x i : ℝ))‖ := norm_le_pi_norm (fun i => (x i : ℝ)) i
  set xr : Fin N → ℝ := fun i => (x i : ℝ) with hxr
  have hs0 : ‖xr‖ ≠ 0 := (lt_of_lt_of_le one_pos hs1).ne'
  have hy : ‖xr‖⁻¹ • xr ∈ Metric.sphere (0 : Fin N → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs0]
  have hq : q xr = ‖xr‖ ^ 2 * q (‖xr‖⁻¹ • xr) := by
    simp only [q, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    field_simp
  have h3 : q y0 ≤ q (‖xr‖⁻¹ • xr) := hmin hy
  have h4 : 0 < q y0 := hpos y0 hy0ne
  have hs2 : 1 ≤ ‖xr‖ ^ 2 := by nlinarith
  show q y0 ≤ q xr
  rw [hq]
  nlinarith

theorem first_minimum_pos (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hne : ∃ v ∈ X.Λ, v ≠ 0) :
    0 < X.la1 x := by
  obtain ⟨b, hb, h⟩ := ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.exists_normal_frame (X := X) hx
  have horth : IsOrth X (rmul x b) := fun τ => (h τ).1
  have hdet : ∀ τ, (mat (rmul x b) τ).det ≠ 0 := fun τ => (dom_of_orth X horth τ).1
  have hm : ∀ τ v, X.maj x τ v = ∑ a, ‖((mat (rmul x b) τ)⁻¹ *ᵥ v) a‖ ^ 2 :=
    fun τ v => (h τ).2 v
  obtain ⟨m0, hm0, hlow⟩ := posDef_int_lower
    (ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Am_posDef (X := X) (mat (rmul x b)) hdet
      (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)))

  have hQ : ∀ v ∈ X.Λ, v ≠ 0 → m0 ≤ ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) := by
    intro v hv hv0
    have e1 : ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) =
        ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X (mat (rmul x b)) v := by
      simp only [ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy, hm]
    have hc : (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)).repr ⟨v, hv⟩ ≠ 0 := by
      intro h0
      have h1 := (LinearEquiv.map_eq_zero_iff _).mp h0
      exact hv0 (by simpa using congrArg Subtype.val h1)
    have hx0 : (fun i => (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)).repr ⟨v, hv⟩ i) ≠ 0 := by
      intro h0
      apply hc
      ext i
      exact congrFun h0 i
    have e2 := ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.quad_int (X := X) (mat (rmul x b))
      (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X))
      (fun i => (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)).repr ⟨v, hv⟩ i)
    have e3 := ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.coe_expand (X := X)
      (ReciprocityTheory.ChartRestriction.G.FD.RealPlaceEmbeddings.zb (X := X)) ⟨v, hv⟩
    rw [e1]
    calc m0 ≤ _ := hlow _ hx0
      _ = _ := e2
      _ = ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.Qy X (mat (rmul x b)) v := by rw [← e3]
  have hS : m0 ≤ X.firstMinimumSq x := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq
    obtain ⟨v, hv, hv0⟩ := hne
    refine le_csInf ⟨_, v, hv, hv0, rfl⟩ ?_
    rintro t ⟨w, hw, hw0, rfl⟩
    exact hQ w hw hw0
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.la1
  exact Real.sqrt_pos.mpr (lt_of_lt_of_le hm0 hS)

theorem orthonormalize (X : Data E r) {p : Frame X.Ψ r} (hp : p ∈ X.dom) :
    ∃ b ∈ Bor X.Ψ r, IsOrth X (rmul p b) ∧ ∀ τ v, X.maj (rmul p b) τ v = X.maj p τ v := by
  obtain ⟨b, hb, h⟩ := ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.exists_normal_frame (X := X) hp
  have horth : IsOrth X (rmul p b) := fun τ => (h τ).1
  refine ⟨b, hb, horth, fun τ v => ?_⟩
  rw [maj_orth X horth, (h τ).2 v]

theorem maj_nonneg_orth (X : Data E r) {u : Frame X.Ψ r} (hu : IsOrth X u) (τ : X.Ψ) (v : Fin r → ℂ) :
    0 ≤ X.maj u τ v := by
  rw [maj_orth X hu]
  positivity

end ModeHalfC

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradFPfA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RGF

open Filter Topology Set ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives ReciprocityTheory.L2DbarEstimates.Y
open scoped ContDiff

noncomputable section

theorem gc_wdb_comp (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (J : V n →L[ℂ] V d) (v : V n)
    (hg : DifferentiableAt ℝ g (F v)) (hF : HasFDerivAt F J v) (j : Fin n) :
    wdb n j (g ∘ F) v = ∑ a, wdb d a g (F v) * (starRingEnd ℂ) (J (bas n j) a) := by
  have hd : fderiv ℝ (g ∘ F) v = (fderiv ℝ g (F v)).comp (J.restrictScalars ℝ) :=
    (hg.hasFDerivAt.comp v (hF.restrictScalars ℝ)).fderiv
  rw [wdb, hd]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul]
  set D := fderiv ℝ g (F v)
  set c := J (bas n j)
  rw [fc_clm_decomp d D c, fc_clm_decomp d D (Complex.I • c), Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, wdb, wd]
  linear_combination ((D (bas d a) - Complex.I * D (Complex.I • bas d a)) / 2 * c a / 2 -
    (D (bas d a) + Complex.I * D (Complex.I • bas d a)) / 2 * (starRingEnd ℂ) (c a) / 2) *
      Complex.I_sq

theorem gc_wd_comp (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (J : V n →L[ℂ] V d) (v : V n)
    (hg : DifferentiableAt ℝ g (F v)) (hF : HasFDerivAt F J v) (j : Fin n) :
    wd n j (g ∘ F) v = ∑ a, wd d a g (F v) * J (bas n j) a := by
  have hd : fderiv ℝ (g ∘ F) v = (fderiv ℝ g (F v)).comp (J.restrictScalars ℝ) :=
    (hg.hasFDerivAt.comp v (hF.restrictScalars ℝ)).fderiv
  rw [wd, hd]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul]
  set D := fderiv ℝ g (F v)
  set c := J (bas n j)
  rw [fc_clm_decomp d D c, fc_clm_decomp d D (Complex.I • c), Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, wdb, wd]
  linear_combination (-(D (bas d a) - Complex.I * D (Complex.I • bas d a)) / 2 * c a / 2 +
    (D (bas d a) + Complex.I * D (Complex.I • bas d a)) / 2 * (starRingEnd ℂ) (c a) / 2) *
      Complex.I_sq

theorem gc_toLp_apply (n d : ℕ) (J : V n →L[ℂ] V d) (ξ : Fin n → ℂ) (b : Fin d) :
    J (WithLp.toLp 2 ξ) b = ∑ j, ξ j * J (bas n j) b := by
  have h : WithLp.toLp 2 ξ = ∑ j, ξ j • bas n j := by
    ext k
    simp [bas, Pi.single_apply]
  rw [h, map_sum]
  simp [map_smul]

theorem gc_sum_wd_comp (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (J : V n →L[ℂ] V d) (v : V n)
    (hg : DifferentiableAt ℝ g (F v)) (hF : HasFDerivAt F J v) (ξ : Fin n → ℂ) :
    ∑ j, wd n j (g ∘ F) v * ξ j = ∑ a, wd d a g (F v) * J (WithLp.toLp 2 ξ) a := by
  simp only [gc_wd_comp n d g F J v hg hF, gc_toLp_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring

theorem sum_four_indices_comm (n d : ℕ) (f : Fin n → Fin n → Fin d → Fin d → ℂ) :
    ∑ j, ∑ k, ∑ a, ∑ b, f j k a b = ∑ b, ∑ a, ∑ j, ∑ k, f j k a b := by
  calc ∑ j, ∑ k, ∑ a, ∑ b, f j k a b = ∑ j, ∑ k, ∑ b, ∑ a, f j k a b :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ j, ∑ b, ∑ k, ∑ a, f j k a b := Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ k, ∑ a, f j k a b := Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ a, ∑ k, f j k a b :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ j, ∑ k, f j k a b := Finset.sum_congr rfl fun b _ => Finset.sum_comm

theorem gc_leviV_comp (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (U : Set (V n)) (hU : IsOpen U)
    (v : V n) (hv : v ∈ U) (hF : ContDiffOn ℂ 2 F U) (hg : ContDiffAt ℝ 2 g (F v))
    (ξ : Fin n → ℂ) :
    leviV n (g ∘ F) v ξ = leviV d g (F v) (fun b => fderiv ℂ F v (WithLp.toLp 2 ξ) b) := by
  have hFd : ∀ y ∈ U, HasFDerivAt F (fderiv ℂ F y) y := fun y hy =>
    (((hF.differentiableOn (by norm_num)) y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  have hgev : ∀ᶠ y in 𝓝 v, ContDiffAt ℝ 2 g (F y) :=
    (hFd v hv).continuousAt.eventually (hg.eventually (by simp))
  have hwdb : ∀ k, wdb n k (g ∘ F) =ᶠ[𝓝 v]
      fun y => ∑ a, wdb d a g (F y) * (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a) := by
    intro k
    filter_upwards [hgev, hU.mem_nhds hv] with y hy hyU
    exact gc_wdb_comp n d g F _ y (hy.differentiableAt (by simp)) (hFd y hyU) k
  have hD : DifferentiableAt ℝ (fderiv ℝ g) (F v) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hWg : ∀ a, DifferentiableAt ℝ (wdb d a g) (F v) := by
    intro a
    show DifferentiableAt ℝ (fun y => (fderiv ℝ g y (bas d a) +
      Complex.I * fderiv ℝ g y (Complex.I • bas d a)) / 2) (F v)
    have h1 := hD.clm_apply (differentiableAt_const (bas d a))
    have h2 := hD.clm_apply (differentiableAt_const (Complex.I • bas d a))
    have h3 := (h1.add (h2.const_mul Complex.I)).mul_const ((2 : ℂ)⁻¹)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp [div_eq_mul_inv]
  have hWa : ∀ a, DifferentiableAt ℝ (fun y => wdb d a g (F y)) v := fun a =>
    (hWg a).comp v ((hFd v hv).restrictScalars ℝ).differentiableAt
  have hDF : DifferentiableAt ℂ (fun y => fderiv ℂ F y) v :=
    ((hF.fderiv_of_isOpen hU (m := 1) (by norm_num)).contDiffAt (hU.mem_nhds hv)).differentiableAt
      (by norm_num)
  have hPa : ∀ k a, DifferentiableAt ℂ (fun y => fderiv ℂ F y (bas n k) a) v := fun k a =>
    (differentiableAt_piLp 2).1 (hDF.clm_apply (differentiableAt_const _)) a
  have hCa : ∀ k a, DifferentiableAt ℝ
      (fun y => (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a)) v := by
    intro k a
    have := Complex.conjCLE.differentiableAt.comp v ((hPa k a).restrictScalars ℝ)
    simpa [Function.comp_def] using this
  have step : ∀ j k, wd n j (wdb n k (g ∘ F)) v = ∑ a, ∑ b,
      wd d b (wdb d a g) (F v) * fderiv ℂ F v (bas n j) b *
        (starRingEnd ℂ) (fderiv ℂ F v (bas n k) a) := by
    intro j k
    rw [wd_congr n j _ _ v (hwdb k),
      fc_wd_sum n j Finset.univ (fun a y => wdb d a g (F y) *
        (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a)) v (fun a _ => (hWa a).mul (hCa k a))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [wd_mul' n j _ _ v (hWa a) (hCa k a), wd_conj', fc_wdb_holo n _ v (hPa k a) j, map_zero,
      mul_zero, add_zero]
    have := gc_wd_comp n d (wdb d a g) F (fderiv ℂ F v) v (hWg a) (hFd v hv) j
    rw [show (fun y => wdb d a g (F y)) = wdb d a g ∘ F from rfl, this, Finset.sum_mul]
  unfold leviV
  simp only [step, gc_toLp_apply, Finset.sum_mul, map_sum, map_mul, Finset.mul_sum]
  rw [sum_four_indices_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.RGF
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SCoordStatementPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

noncomputable section

namespace SchubertCoordinates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem diff_coord {n : ℕ} (i : Fin n) : Differentiable ℂ fun v : V n => v i := by
  exact (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable

theorem diff_nmat (X : FD.Data E r) (τ : X.Ψ) (a b : Fin r) :
    Differentiable ℂ fun z : V (nd X) => nmat X z τ a b := by
  unfold nmat
  split_ifs
  · exact diff_coord _
  · exact differentiable_const _
  · exact differentiable_const _

theorem diff_cpt (X : FD.Data E r) (x0 : Frame X.Ψ r) : Differentiable ℂ (cpt X x0) := by
  unfold cpt rmul
  refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
  simp only [mat, Matrix.mul_apply, Matrix.of_apply]
  exact Differentiable.fun_sum fun k _ => (differentiable_const _).mul (diff_nmat X τ k b)

theorem nmat_zero (X : FD.Data E r) (τ : X.Ψ) : mat (nmat X 0) τ = 1 := by
  ext a b
  simp only [mat, nmat, Matrix.of_apply, Matrix.one_apply]
  by_cases h1 : b < a
  · have h2 : a ≠ b := fun h => by subst h; exact lt_irrefl _ h1
    simp [h1, h2]
    rfl
  · simp [h1]

theorem cpt_zero (X : FD.Data E r) (x : Frame X.Ψ r) : cpt X x 0 = x := by
  funext τ
  show (mat x τ * mat (nmat X 0) τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [nmat_zero, Matrix.mul_one]
  rfl

theorem cont_gram (X : FD.Data E r) (τ : X.Ψ) :
    Continuous fun x : Frame X.Ψ r => gram τ.1 X.Gm (mat x τ) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [gram, hermC, col, mat, Matrix.of_apply]
  fun_prop

theorem isOpen_dom (X : FD.Data E r) : IsOpen X.dom := by
  have hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det :=
    fun τ => Continuous.matrix_det (continuous_apply τ)
  have hmin : ∀ τ : X.Ψ, ∀ i : Fin (r + 1), Continuous fun x : Frame X.Ψ r => (dmin X.Gm x τ i).re := by
    intro τ i
    refine Complex.continuous_re.comp ?_
    unfold dmin lminor
    exact Continuous.matrix_det ((cont_gram X τ).matrix_submatrix _ _)
  have hset : X.dom = ⋂ τ : X.Ψ, ({x | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x
    simp [FD.Data.dom, GG, Set.mem_iInter]
  rw [hset]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter (isOpen_ne_fun (hdet τ) continuous_const)
    (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_const.mul (hmin τ i)))

end SchubertCoordinates

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
  {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem SCoordStatement_holds :
    SCoordStatement (K := K) (ι := ι) (Ω := Ω) (WT := WT) (A := A) (𝒜 := 𝒜) (E := E) := by
  intro d c r X sg R Xa hD e t hH x hx hs hw0
  obtain ⟨hd, -, -, ht, -⟩ := hH
  obtain ⟨j0, jj, hj0, hJ⟩ := R.coordAt x hx
  obtain ⟨W, hWdef⟩ : ∃ W : Fin (d.N + 1) → Frame X.Ψ r → ℂ,
      W = fun j => R.rd ⟨d.w j c, R.w_mem j⟩ := ⟨_, rfl⟩
  have hsW : ∀ i y, sR d c R t hD i y = ∑ j, t ((Fin.cast hD i).succ, j) * W j y := fun i y => by
    rw [hWdef]; rfl
  have hw0W : ∀ y, w0R d c R t y = ∑ j, t (0, j) * W j y := fun y => by rw [hWdef]; rfl
  have hWd : ∀ j, DifferentiableOn ℂ (W j) X.dom := fun j => by
    rw [hWdef]; exact (R.sec d.wL R.wL_mem _ (R.w_mem j) (hd.w_mem j c)).1
  have hw0ne : d.w j0 c ≠ 0 := by
    intro h
    apply hj0
    have h0 : (⟨d.w j0 c, R.w_mem j0⟩ : R.Rg) = 0 := Subtype.ext h
    rw [h0, map_zero]
    rfl
  have hWu : ∀ y ∈ R.Gen, ∀ j, W j y = R.pt y (ratio (Ω := Ω c) (d.w j c) (d.w j0 c)) * W j0 y :=
    fun y hy j => by
      rw [hWdef]
      exact R.ratio_rd d.wL _ (R.w_mem j) _ (R.w_mem j0) (hd.w_mem j c) (hd.w_mem j0 c) hw0ne y hy
  have hpt : ∀ y ∈ R.Gen, (R.pt y).comp (algebraMap K (Ω c)) = sg := fun y hy => R.pt_mem y hy
  have hx0 : W j0 x ≠ 0 := by rw [hWdef]; exact hj0
  have hJ' : (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      W (jj k) (cpt X x z) / W j0 (cpt X x z) : V (nd X))) 0).det ≠ 0 := by
    rw [hWdef]; exact hJ
  have hfun : (fun z : V (nd X) => (WithLp.toLp 2 fun i =>
      sR d c R t hD i (cpt X x z) / w0R d c R t (cpt X x z) : V (nd X))) =
      fun z : V (nd X) => (WithLp.toLp 2 fun i =>
        (∑ j, t ((Fin.cast hD i).succ, j) * W j (cpt X x z)) / (∑ j, t (0, j) * W j (cpt X x z)) :
          V (nd X)) := by
    funext z
    simp only [hsW, hw0W]
  rw [hfun]
  exact SCoF.core hD sg (SchubertCoordinates.isOpen_dom X) R.Gen_sub R.Gen_dense R.pt hpt (hd.trdeg c) W hWd
    (fun j => ratio (Ω := Ω c) (d.w j c) (d.w j0 c)) j0 hWu (cpt X x) (SchubertCoordinates.diff_cpt X x)
    (SchubertCoordinates.cpt_zero X x) hx hx0 jj hJ' t ht (fun i => by rw [← hsW]; exact hs i)
    (by rw [← hw0W]; exact hw0)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

