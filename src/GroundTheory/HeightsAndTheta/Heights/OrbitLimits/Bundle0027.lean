import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsBilinear
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff

namespace PointsBilinear

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem contDiffAt_comp {D : ℕ} {u : ((Σ k, ι k) → ℂ) → ℝ} (hu : IsDegZeroSmooth u)
    {γ : (Fin D → ℂ) → (Σ k, ι k) → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ 2 (fun y' => u (γ y')) y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.mp hγ
  have hdU : DifferentiableOn ℂ γ U := fun y' h => (hU y' h).differentiableWithinAt
  have hc : ContDiffAt ℝ ∞ γ y :=
    ((ReciprocityTheory.ChartRestriction.DS.S7.cca_contDiffOn hUo hdU).contDiffAt (hUo.mem_nhds hyU)).restrict_scalars ℝ
  have hρ : ContDiffAt ℝ ∞ u (γ y) := hu.1.contDiffAt (isOpen_blockNonzero.mem_nhds hy)
  exact_mod_cast (contDiffAt_infty.mp (hρ.comp y hc)) 2

theorem cxHessian_sum {D : ℕ} {T : Type} [Fintype T] (f : T → (Fin D → ℂ) → ℝ) {y : Fin D → ℂ}
    (hf : ∀ t, ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (f t) y') :
    cxHessian (fun y' => ∑ t, f t y') y = ∑ t, cxHessian (f t) y := by
  have h1 : fderiv ℝ (fun y' => ∑ t, f t y') =ᶠ[𝓝 y] fun y' => ∑ t, fderiv ℝ (f t) y' := by
    filter_upwards [eventually_all.mpr hf] with y' hy'
    exact fderiv_fun_sum fun t _ => (hy' t).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ (fun y' => ∑ t, f t y')) y = ∑ t, fderiv ℝ (fderiv ℝ (f t)) y := by
    rw [h1.fderiv_eq]
    exact fderiv_fun_sum fun t _ =>
      ((hf t).self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  ext i j
  simp only [cxHessian, h2, FunLike.coe_sum, Finset.sum_apply, Matrix.sum_apply]
  push_cast
  rw [← Finset.sum_div]
  congr 1
  simp only [Finset.sum_add_distrib]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]

theorem mixedDisc_update_sum {D : ℕ} {T : Type} [Fintype T] (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (k : Fin D) (B : T → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (Function.update A k (∑ t, B t)) = ∑ t, mixedDisc (Function.update A k (B t)) := by
  obtain ⟨M, hM⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := D)
  have e : ∀ C, mixedDisc (Function.update A k C) = M.toLinearMap A k C := fun C => by
    rw [MultilinearMap.toLinearMap_apply, hM]
    rfl
  simp only [e, map_sum]

theorem cxHessian_cons {n : ℕ} (L : Fin n → HermLine ι) (f v : ((Σ k, ι k) → ℂ) → ℝ)
    (γ : (Fin (n + 1) → ℂ) → (Σ k, ι k) → ℂ) (y : Fin (n + 1) → ℂ) :
    (fun k => cxHessian
        (fun y' => (Fin.cons f (pot L) : Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) k (γ y')) y) =
      Function.update (fun k => cxHessian
        (fun y' => (Fin.cons v (pot L) : Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) k (γ y')) y) 0
        (cxHessian (fun y' => f (γ y')) y) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · rw [Function.update_self]
    simp only [Fin.cons_zero]
  · rw [Function.update_of_ne (Fin.succ_ne_zero j)]
    simp only [Fin.cons_succ]

theorem maDensity_cons_sum {n : ℕ} (L : Fin n → HermLine ι) {T : Type} [Fintype T]
    {u : T → ((Σ k, ι k) → ℂ) → ℝ} (hu : ∀ t, IsDegZeroSmooth (u t))
    {γ : (Fin (n + 1) → ℂ) → (Σ k, ι k) → ℂ} {y : Fin (n + 1) → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0) :
    maDensity (fun j y' => (Fin.cons (fun z => ∑ t, u t z) (pot L) :
        Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) j (γ y')) y =
      ∑ t, maDensity (fun j y' => (Fin.cons (u t) (pot L) :
        Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) j (γ y')) y := by
  have hev := hγ.eventually_nhds
  have hc : ∀ t, ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => u t (γ y'')) y' := fun t => by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_comp (hu t) (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hH := cxHessian_sum (fun t y' => u t (γ y')) hc
  simp only [maDensity]
  rw [cxHessian_cons L _ (fun _ => 0) γ y]
  simp only [hH, mixedDisc_update_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [cxHessian_cons L (u t) (fun _ => 0) γ y]

omit [∀ k, Fintype (ι k)] in

theorem sheetDensity_sum_left {n : ℕ} (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (φ : Fin n → ((Σ k, ι k) → ℂ) → ℝ)
    {T : Type} [Fintype T] (u : T → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin n → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ (fun z => ∑ t, u t z) y w = ∑ t, sheetDensity P Ψ φ (u t) y w := by
  unfold sheetDensity
  by_cases h : ∃ γ, IsSheet P Ψ y w γ
  · simp only [dif_pos h, Finset.sum_mul]
  · simp only [dif_neg h, Finset.sum_const_zero]

theorem sheetDensity_sum_right {n : ℕ} (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ)) (L : Fin n → HermLine ι)
    {T : Type} [Fintype T] {u : T → ((Σ k, ι k) → ℂ) → ℝ} (hu : ∀ t, IsDegZeroSmooth (u t))
    (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ (Fin.cons (fun z => ∑ t, u t z) (pot L)) g y w =
      ∑ t, sheetDensity P Ψ (Fin.cons (u t) (pot L)) g y w := by
  unfold sheetDensity
  by_cases h : ∃ γ, IsSheet P Ψ y w γ
  · simp only [dif_pos h]
    have hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ h.choose y' ∧ ∀ k, ∃ i, h.choose y' ⟨k, i⟩ ≠ 0 := by
      filter_upwards [h.choose_spec.2] with y' hy'
      exact ⟨hy'.1, hy'.2.1.1⟩
    rw [maDensity_cons_sum L hu hγ, Finset.mul_sum]
  · simp only [dif_neg h, Finset.sum_const_zero]

theorem finsum_mem_sum_comm {α T : Type*} [Fintype T] {S : Set α} (hS : S.Finite) (F : T → α → ℝ) :
    ∑ᶠ w ∈ S, ∑ t, F t w = ∑ t, ∑ᶠ w ∈ S, F t w := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => (finsum_mem_eq_finite_toFinset_sum _ hS).symm

theorem isSmoothHerm_ofWeight {w : ((Σ k, ι k) → ℂ) → ℝ}
    (hw : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → w (fun p => c p.1 * z p) = w z)
    (hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) :
    IsSmoothHerm (HermLine.ofWeight w hw) := by
  have e : (HermLine.ofWeight w hw).h = fun z => Real.exp (-w z) := rfl
  unfold IsSmoothHerm
  rw [e]
  exact Real.contDiff_exp.comp_contDiffOn hs.neg

theorem integrable_fibreSum (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {n : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ)) (L : Fin n → HermLine ι)
    {f g : ((Σ k, ι k) → ℂ) → ℝ} (hP : IsArithVar P (n + 2)) (hΨ : IsGoodProj P Ψ)
    (hL : ∀ j, IsSmoothHerm (L j)) (hf : IsDegZeroSmooth f) (hg : IsDegZeroSmooth g) :
    Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (Fin.cons f (pot L)) g y w) := by
  have hf' : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → -f (fun p => c p.1 * z p) = -f z :=
    fun c z hc => by simp only [hf.2 c z hc]
  have hF := isSmoothHerm_ofWeight (w := fun z => -f z) hf' hf.1.neg
  have hG := isSmoothHerm_ofWeight hg.2 hg.1
  have hLF : ∀ j, IsSmoothHerm ((Fin.cons (HermLine.ofWeight (fun z => -f z) hf') L : Fin (n + 1) → HermLine ι) j) := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [Fin.cons_zero] using hF
    · simpa only [Fin.cons_succ] using hL j
  have hpot : pot (Fin.cons (HermLine.ofWeight (fun z => -f z) hf') L : Fin (n + 1) → HermLine ι) = Fin.cons f (pot L) := by
    funext j z
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [pot, HermLine.ofWeight, Real.log_exp]
    · simp [pot]
  have hlog : logNorm (HermLine.ofWeight g hg.2) 1 = g := by
    funext z
    simp [logNorm, HermLine.ofWeight, Real.log_exp]
  have h1 : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  have hm : IsMultiHomog (1 : MRing ι) (fun _ => 0) := by
    intro m hm k
    rw [MvPolynomial.support_one] at hm
    simp only [Finset.mem_singleton] at hm
    subst hm
    simp
  have hsec : IsSectionOn P (HermLine.ofWeight g hg.2) 1 :=
    ⟨fun _ => 0, fun k => by simp [HermLine.ofWeight], hm, h1⟩
  have := hInt K ι P (n + 1) Ψ _ _ 1 hP hΨ hLF hG hsec
  rwa [hpot, hlog] at this

end PointsBilinear

open PointsBilinear in

theorem PtsBilinear.proof (hAbs : Inter.PtsAbsIntegrable.Statement) (hMeas : PtsSumMeasurable.Statement) :
    PtsBilinear.Statement := by
  have hInt := PtsIntegrable.of_found hAbs hMeas
  intro K _ ι _ P n L T _ u v hP hL hu hv
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ), IsGoodProj P Ψ
  · simp only [dif_pos hΨ]
    have hfin := fibreFinite K ι P (n + 1) hΨ.choose hP hΨ.choose_spec
    unfold ptsIntegralAt
    constructor
    · rw [← integral_finsetSum _ fun t _ =>
        integrable_fibreSum hInt hΨ.choose L hP hΨ.choose_spec hL hv (hu t)]
      congr 1
      funext y
      rw [finsum_mem_congr rfl fun w _ => sheetDensity_sum_left P hΨ.choose _ u y w,
        finsum_mem_sum_comm (hfin y)]
    · rw [← integral_finsetSum _ fun t _ =>
        integrable_fibreSum hInt hΨ.choose L hP hΨ.choose_spec hL (hu t) hv]
      congr 1
      funext y
      rw [finsum_mem_congr rfl fun w _ => sheetDensity_sum_right P hΨ.choose L hu v y w,
        finsum_mem_sum_comm (hfin y)]
  · simp only [dif_neg hΨ, Finset.sum_const_zero, and_self]

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsIntegralProjIndep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj IsSheet ptsIntegralAt sheetDensity
  fibre pot mcPts fibreFinite isOpen_blockNonzero)

section

variable {K : Type*} [Fintype K] {ι : K → Type*} {e : ℕ} {P : Ideal (MRing ι)}
  {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ}

theorem sheetDensity_neg (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ (fun z => -g z) y w = -sheetDensity P Ψ φ g y w := by
  unfold sheetDensity
  split_ifs <;> simp [neg_mul]

theorem sheetDensity_congr {g g' : ((Σ k, ι k) → ℂ) → ℝ} (h : ∀ z ∈ mcPts P, g z = g' z) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : sheetDensity P Ψ φ g y w = sheetDensity P Ψ φ g' y w := by
  unfold sheetDensity
  split_ifs with hγ
  · have hs : IsSheet P Ψ y w hγ.choose := hγ.choose_spec
    rw [h _ hs.2.self_of_nhds.2.1]
  · rfl

end

theorem PtsIntegralProjIndep.proof (hInt : PtsPosDensIntegrable.Statement)
    (hPos : PtsPosPartProjIndep.Statement) : PtsIntegralProjIndep.Statement := by
  intro K _ ι _ P e Ψ Ψ' L g hP hΨ hΨ' hL hg
  classical
  set S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hSdef
  set g₀ : ((Σ k, ι k) → ℂ) → ℝ := S.piecewise g 0 with hg₀def
  have hg₀m : Measurable g₀ :=
    hg.1.continuousOn.measurable_piecewise continuousOn_const isOpen_blockNonzero.measurableSet
  have hg₀inv : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      g₀ (fun p => c p.1 * z p) = g₀ z := by
    intro c z hc
    have hmem : (fun p : Σ k, ι k => c p.1 * z p) ∈ S ↔ z ∈ S := by
      simp only [hSdef, Set.mem_ofPred_eq, ne_eq, mul_eq_zero, hc, false_or]
    by_cases hz : z ∈ S
    · rw [hg₀def, Set.piecewise_eq_of_mem _ _ _ hz, Set.piecewise_eq_of_mem _ _ _ (hmem.2 hz), hg.2 c z hc]
    · rw [hg₀def, Set.piecewise_eq_of_notMem _ _ _ hz, Set.piecewise_eq_of_notMem _ _ _ (mt hmem.1 hz)]
      rfl
  have hag : ∀ z ∈ mcPts P, g z = g₀ z := fun z hz =>
    (Set.piecewise_eq_of_mem S _ _ (show z ∈ S from hz.1)).symm
  have hagn : ∀ z ∈ mcPts P, -g z = -g₀ z := fun z hz => by rw [hag z hz]
  have hneg : IsDegZeroSmooth (fun z => -g z) :=
    ⟨hg.1.neg, fun c z hc => by simp only [hg.2 c z hc]⟩
  have hnn : ∀ (Ψ₀ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (u : ((Σ k, ι k) → ℂ) → ℝ) y,
      0 ≤ ptsPosDens P Ψ₀ (pot L) u y := fun Ψ₀ u y =>
    finsum_nonneg fun w => finsum_nonneg fun _ => le_max_right _ _

  have key : ∀ Ψ₀ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ₀ →
      ptsIntegralAt P Ψ₀ (pot L) g =
        (∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ₀ (pot L) g₀ y)).toReal -
          (∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ₀ (pot L) (fun z => -g₀ z) y)).toReal := by
    intro Ψ₀ h₀
    have hp := hInt K ι P e Ψ₀ L g hP h₀ hL hg
    have hn := hInt K ι P e Ψ₀ L (fun z => -g z) hP h₀ hL hneg
    have e₁ : ptsPosDens P Ψ₀ (pot L) g₀ = ptsPosDens P Ψ₀ (pot L) g := by
      funext y
      simp only [ptsPosDens, sheetDensity_congr (Ψ := Ψ₀) (φ := pot L) hag]
    have e₂ : ptsPosDens P Ψ₀ (pot L) (fun z => -g₀ z) = ptsPosDens P Ψ₀ (pot L) (fun z => -g z) := by
      funext y
      simp only [ptsPosDens, sheetDensity_congr (Ψ := Ψ₀) (φ := pot L) hagn]
    have hsplit : ∀ y, (∑ᶠ w ∈ fibre P Ψ₀ y, sheetDensity P Ψ₀ (pot L) g y w) =
        ptsPosDens P Ψ₀ (pot L) g y - ptsPosDens P Ψ₀ (pot L) (fun z => -g z) y := by
      intro y
      have hF := fibreFinite K ι P e Ψ₀ hP h₀ y
      simp only [ptsPosDens, finsum_mem_eq_finite_toFinset_sum _ hF, sheetDensity_neg,
        ← Finset.sum_sub_distrib, max_zero_sub_max_neg_zero_eq_self]
    unfold ptsIntegralAt
    simp only [hsplit]
    rw [integral_sub hp hn, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnn Ψ₀ g)) hp.1,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnn Ψ₀ _)) hn.1, e₁, e₂]
  rw [key Ψ hΨ, key Ψ' hΨ', hPos K ι P e Ψ Ψ' L g₀ hP hΨ hΨ' hL hg₀m hg₀inv,
    hPos K ι P e Ψ Ψ' L (fun z => -g₀ z) hP hΨ hΨ' hL hg₀m.neg fun c z hc => by simp only [hg₀inv c z hc]]

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosPartProjIndep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj mcPts segre fibre IsSheet sheetDensity
  pot fibreFinite)

theorem ptsPosDens_split {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
    {P : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (E : ℕ → Set ((Σ k, ι k) → ℂ))
    (y : Fin e → ℂ) (hfin : (fibre P Ψ y).Finite) (hE : Pairwise (Function.onFun Disjoint E))
    (hcov : ∀ w ∈ fibre P Ψ y, (∃ γ, IsSheet P Ψ y w γ) → ∀ z ∈ mcPts P, segre z = w → ∃ k, z ∈ E k) :
    ENNReal.ofReal (ptsPosDens P Ψ φ g y) =
      ∑' k, ENNReal.ofReal (ptsPosDens P Ψ φ ((E k).indicator g) y) := by
  classical
  unfold ptsPosDens
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hT0 : ∀ (g' : ((Σ k, ι k) → ℂ) → ℝ) w, 0 ≤ max (sheetDensity P Ψ φ g' y w) 0 :=
    fun _ _ => le_max_right _ _
  have hpt : ∀ w ∈ hfin.toFinset, ENNReal.ofReal (max (sheetDensity P Ψ φ g y w) 0) =
      ∑' k, ENNReal.ofReal (max (sheetDensity P Ψ φ ((E k).indicator g) y w) 0) := by
    intro w hw
    have hw' : w ∈ fibre P Ψ y := hfin.mem_toFinset.mp hw
    by_cases hs : ∃ γ, IsSheet P Ψ y w γ
    · have hz : hs.choose y ∈ mcPts P := hs.choose_spec.2.self_of_nhds.2.1
      obtain ⟨k₀, hk₀⟩ := hcov w hw' hs _ hz hs.choose_spec.1
      rw [tsum_eq_single k₀]
      · simp only [sheetDensity, dif_pos hs, Set.indicator_of_mem hk₀]
      · intro k hk
        have hxk : hs.choose y ∉ E k := fun hxk => Set.disjoint_left.mp (hE hk) hxk hk₀
        simp [sheetDensity, dif_pos hs, Set.indicator_of_notMem hxk]
    · simp [sheetDensity, dif_neg hs]
  rw [ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 g w), Finset.sum_congr rfl hpt,
    ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact tsum_congr fun k => (ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 _ w)).symm

theorem PtsPosPartProjIndep.proof (hS : PtsSheetSimpleNull.Statement) (hO : PtsSheetOnlyNull.Statement)
    (hL : PtsPosPartLocal.Statement) (hM : PtsPosDensMeasurable.Statement) :
    PtsPosPartProjIndep.Statement := by
  intro K _ ι _ P e Ψ Ψ' L g hP hΨ hΨ' hLs hg hg0
  classical

  set Inv : Set ((Σ k, ι k) → ℂ) → Prop := fun S => ∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
    ((fun p => c p.1 * z' p) ∈ S ↔ z' ∈ S) with hInv

  set Q : ((Σ k, ι k) → ℂ) → Prop := fun z => z ∈ mcPts P ∧
    IsSimpleSheetPt P Ψ ((Ψ (segre z) 0)⁻¹ • segre z) ∧
    IsSimpleSheetPt P Ψ' ((Ψ' (segre z) 0)⁻¹ • segre z) with hQ
  have key : ∀ z, ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ Inv W ∧ (Q z → z ∈ W) ∧
      ∀ E, MeasurableSet E → Inv E → E ⊆ W →
        ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) (E.indicator g) y) =
          ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ' (pot L) (E.indicator g) y) := by
    intro z
    by_cases hz : Q z
    · obtain ⟨W, hW, hzW, hWi, hWE⟩ := hL K ι P e Ψ Ψ' L g z hP hΨ hΨ' hLs hg hg0 hz.1 hz.2.1 hz.2.2
      exact ⟨W, hW, hWi, fun _ => hzW, hWE⟩
    · refine ⟨∅, isOpen_empty, fun _ _ _ => Iff.rfl, fun h => absurd h hz, fun E _ _ hE => ?_⟩
      rw [Set.subset_empty_iff.1 hE, Set.indicator_empty]
      simp [ptsPosDens, sheetDensity]
  choose W hWo hWi hzW hWE using key
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨f, hf⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  set E : ℕ → Set ((Σ k, ι k) → ℂ) := disjointed (fun k => W (f k)) with hE
  have hEm : ∀ k, MeasurableSet (E k) := MeasurableSet.disjointed fun k => (hWo (f k)).measurableSet
  have hEW : ∀ k, E k ⊆ W (f k) := disjointed_subset _
  have hEd : Pairwise (Function.onFun Disjoint E) := disjoint_disjointed _
  have hEi : ∀ k, Inv (E k) := by
    intro k c z' hc
    simp only [hE, disjointed_eq_inter_compl, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
      hWi _ c z' hc]
  have hgE : ∀ k (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      (E k).indicator g (fun p => c p.1 * z' p) = (E k).indicator g z' := by
    intro k c z' hc
    simp only [Set.indicator_apply, hEi k c z' hc, hg0 c z' hc]
  have hcov : ∀ z, Q z → ∃ k, z ∈ E k := by
    intro z hq
    have : z ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨z, hzW z hq⟩
    obtain ⟨i, hiT, hzi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨m, rfl⟩ : i ∈ Set.range f := hf ▸ Set.mem_insert_of_mem 0 hiT
    have : z ∈ ⋃ k, E k := by
      rw [hE, iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hzi⟩
    exact Set.mem_iUnion.1 this

  have hae : ∀ B B' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P B → IsGoodProj P B' →
      (∀ z ∈ mcPts P, IsSimpleSheetPt P B ((B (segre z) 0)⁻¹ • segre z) →
        IsSimpleSheetPt P B' ((B' (segre z) 0)⁻¹ • segre z) → ∃ k, z ∈ E k) →
      ∀ᵐ y, ENNReal.ofReal (ptsPosDens P B (pot L) g y) =
        ∑' k, ENNReal.ofReal (ptsPosDens P B (pot L) ((E k).indicator g) y) := by
    intro B B' hB hB' hc
    have hnull := measure_union_null (hS K ι P e B hP hB) (hO K ι P e B B' hP hB hB')
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
    refine ptsPosDens_split _ _ E y (fibreFinite K ι P e B hP hB y) hEd fun w hw hs z hz hzw => ?_
    have hw1 : B w 0 = 1 := by
      obtain ⟨_, _, _, h⟩ := hw
      rw [h]
      rfl
    have hs1 : IsSimpleSheetPt P B w := by
      by_contra hn
      exact hy (Or.inl ⟨w, hw, hs, hn⟩)
    have hs2 : IsSimpleSheetPt P B' ((B' w 0)⁻¹ • w) := by
      by_contra hn
      exact hy (Or.inr ⟨w, hw, hs1, hn⟩)
    subst hzw
    refine hc z hz ?_ hs2
    rwa [hw1, inv_one, one_smul]
  have hint : ∀ B : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P B →
      (∀ᵐ y, ENNReal.ofReal (ptsPosDens P B (pot L) g y) =
        ∑' k, ENNReal.ofReal (ptsPosDens P B (pot L) ((E k).indicator g) y)) →
      ∫⁻ y, ENNReal.ofReal (ptsPosDens P B (pot L) g y) =
        ∑' k, ∫⁻ y, ENNReal.ofReal (ptsPosDens P B (pot L) ((E k).indicator g) y) := by
    intro B hB h2
    rw [lintegral_congr_ae h2, lintegral_tsum fun k =>
      (hM K ι P e B L _ hP hB hLs (hg.indicator (hEm k)) (hgE k)).ennreal_ofReal]
  rw [hint Ψ hΨ (hae Ψ Ψ' hΨ hΨ' fun z hz h1 h2 => hcov z ⟨hz, h1, h2⟩),
    hint Ψ' hΨ' (hae Ψ' Ψ hΨ' hΨ fun z hz h1 h2 => hcov z ⟨hz, h2, h1⟩)]
  exact tsum_congr fun k => hWE (f k) (E k) (hEm k) (hEi k) (hEW k)

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSheetSimpleNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre fibre IsSheet segre_differentiableAt)

theorem PtsSheetSimpleNull.simple_of_count {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
    {P : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {d : ℕ} {y : Fin e → ℂ}
    (hbd : ∀ y', (fibre P Ψ y').encard ≤ d) (hy : (fibre P Ψ y).encard = d)
    (hsh : ∀ w ∈ fibre P Ψ y, ∃ γ, IsSheet P Ψ y w γ) {w : ((k : K) → ι k) → ℂ}
    (hw : w ∈ fibre P Ψ y) : IsSimpleSheetPt P Ψ w := by
  have hF : (fibre P Ψ y).Finite := Set.finite_of_encard_eq_coe hy
  choose! γ hγ using hsh
  obtain ⟨U, hU, hdisj⟩ := hF.t2_separation

  have hev : ∀ᶠ y' in 𝓝 y, ∀ a ∈ fibre P Ψ y,
      (γ a y' ∈ mcPts P ∧ Ψ (segre (γ a y')) = Fin.cons 1 y') ∧ segre (γ a y') ∈ U a := by
    refine (hF.eventually_all).2 fun a ha => ?_
    have hc := (segre_differentiableAt (hγ a ha).2.self_of_nhds.1).continuousAt
    have hmem : U a ∈ 𝓝 (segre (γ a y)) := by
      rw [(hγ a ha).1]
      exact (hU a).2.mem_nhds (hU a).1
    filter_upwards [(hγ a ha).2, hc.preimage_mem_nhds hmem] with y' h1 h2
    exact ⟨⟨h1.2.1, h1.2.2⟩, h2⟩

  have hfib : ∀ y', (∀ a ∈ fibre P Ψ y, (γ a y' ∈ mcPts P ∧ Ψ (segre (γ a y')) = Fin.cons 1 y') ∧
      segre (γ a y') ∈ U a) → fibre P Ψ y' = (fun a => segre (γ a y')) '' fibre P Ψ y := by
    intro y' h
    have hinj : Set.InjOn (fun a => segre (γ a y')) (fibre P Ψ y) := by
      intro a ha b hb hab
      by_contra hne
      exact Set.disjoint_left.mp (hdisj ha hb hne) (h a ha).2 (by simp only at hab; rw [hab]; exact (h b hb).2)
    have hsub : (fun a => segre (γ a y')) '' fibre P Ψ y ⊆ fibre P Ψ y' := by
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨γ a y', (h a ha).1.1, rfl, (h a ha).1.2⟩
    refine ((hF.image _).eq_of_subset_of_encard_le hsub ?_).symm
    rw [hinj.encard_image, hy]
    exact hbd y'
  refine ⟨y, γ w, hγ w hw, ?_⟩
  filter_upwards [hev.prodMk_nhds ((hU w).2.mem_nhds (hU w).1)] with q hq hq2
  rw [hfib q.1 hq.1] at hq2
  obtain ⟨a, ha, hqa⟩ := hq2
  have haw : a = w := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj ha hw hne) (by rw [← hqa]; exact (hq.1 a ha).2) hq.2
  rw [← hqa, haw]

theorem PtsSheetSimpleNull.proof (hG : PtsGenericCount.Statement) : PtsSheetSimpleNull.Statement := by
  intro K _ ι _ P e Ψ hP hΨ
  obtain ⟨d, hbd, hnull⟩ := hG K ι P e Ψ hP hΨ
  refine measure_mono_null (fun y hy => ?_) hnull
  obtain ⟨w, hw, -, hns⟩ := hy
  exact fun hgood => hns (PtsSheetSimpleNull.simple_of_count hbd hgood.1 hgood.2 hw)

end GroundTheory.Heights₂.Heights
end
end

