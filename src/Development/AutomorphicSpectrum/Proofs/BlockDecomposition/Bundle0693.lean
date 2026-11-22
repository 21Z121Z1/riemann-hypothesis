import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0680
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0643
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0079
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0061
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0617
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0398
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0414
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0674
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0512

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarizationCoordinateDerivativeBounds
section
open Ad3.LR Ad3.LR.DTr GlobalTheory.CompanionTheory.DInt2

noncomputable section

namespace GlobalTheory.CompanionTheory.DInt2.Drho

def pr (i j : Fin 2) : M22 →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℝ) i))

theorem pr_apply (i j : Fin 2) (h : M22) : pr i j h = (h i j : ℂ) := rfl

def eps (d : Fin 2) : ℂ := if d = 0 then 1 else Complex.I

theorem norm_eps (d : Fin 2) : ‖eps d‖ = 1 := by
  unfold eps
  split_ifs <;> simp

def alC : M22 →L[ℝ] ℂ := pr 0 0 + Complex.I • pr 1 0

theorem alC_apply (h : M22) : alC h = al h := by
  simp [alC, al, pr_apply, mul_comm]

def rC (c d : Fin 2) : M22 →L[ℝ] ℂ := eps d • pr c 0

theorem al_rpol (c d : Fin 2) (h : M22) : al (rpol c d h) = eps d * (h c 0 : ℂ) := by
  fin_cases d <;> simp [al, rpol, eps, mul_comm]

theorem rC_apply (c d : Fin 2) (h : M22) : rC c d h = al (rpol c d h) := by
  simp [rC, al_rpol, pr_apply]

theorem norm_entry_le (a : Fin 2) (h : M22) : ‖((h a 0 : ℝ) : ℂ)‖ ≤ ‖al h‖ := by
  have h1 : (al h).re = h 0 0 := by simp [al]
  have h2 : (al h).im = h 1 0 := by simp [al]
  fin_cases a
  · simpa [h1] using Complex.abs_re_le_norm (al h)
  · simpa [h2] using Complex.abs_im_le_norm (al h)

theorem norm_al_rpol_le (c d : Fin 2) (h : M22) : ‖al (rpol c d h)‖ ≤ ‖al h‖ := by
  rw [al_rpol, norm_mul, norm_eps, one_mul]
  exact norm_entry_le c h

theorem norm_al_rpol_rpol_le (a b c d : Fin 2) (h : M22) :
    ‖al (rpol c d (rpol a b h))‖ ≤ ‖al h‖ := by
  rw [al_rpol, norm_mul, norm_eps, one_mul]
  by_cases hcb : c = b
  · have : rpol a b h c 0 = h a 0 := by simp [rpol, hcb]
    rw [this]
    exact norm_entry_le a h
  · have : rpol a b h c 0 = 0 := by simp [rpol, hcb]
    rw [this]
    simp

theorem al_ne (h : M22) (hΔ : 0 < (Matrix.of h).det) : al h ≠ 0 :=
  GlobalTheory.CompanionTheory.WeightClosed.alpha_ne_zero h hΔ

theorem hasFDerivAt_quot {f g : M22 → ℂ} {f' g' : M22 →L[ℝ] ℂ} {h : M22}
    (hf : HasFDerivAt f f' h) (hg : HasFDerivAt g g' h) (h0 : g h ≠ 0) :
    HasFDerivAt (fun x => f x / g x) ((g h)⁻¹ • f' + (f h * (-(g h ^ 2)⁻¹)) • g') h := by
  have hi : HasFDerivAt (fun x => (g x)⁻¹) ((-(g h ^ 2)⁻¹) • g') h :=
    (hasDerivAt_inv h0).comp_hasFDerivAt h hg
  simp only [div_eq_mul_inv]
  refine (hf.fun_mul hi).congr_fderiv ?_
  ext X
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem hasFDerivAt_rho (c d : Fin 2) (h : M22) (h0 : al h ≠ 0) :
    HasFDerivAt (rho c d)
      ((al h)⁻¹ • rC c d + (al (rpol c d h) * (-(al h ^ 2)⁻¹)) • alC) h := by
  have e : rho c d = fun x => rC c d x / alC x := by
    funext x
    rw [rC_apply, alC_apply, rho]
  rw [e]
  have := hasFDerivAt_quot (rC c d).hasFDerivAt alC.hasFDerivAt
    (h := h) (by rwa [alC_apply])
  simpa only [rC_apply, alC_apply] using this

def detC (h : M22) : M22 →L[ℝ] ℂ :=
  ((h 0 0 : ℂ) • pr 1 1 + (h 1 1 : ℂ) • pr 0 0) - ((h 0 1 : ℂ) • pr 1 0 + (h 1 0 : ℂ) • pr 0 1)

theorem detC_apply (h X : M22) : detC h X = (dd h X : ℂ) := by
  simp only [detC, dd, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, pr_apply]
  push_cast
  ring

theorem hasFDerivAt_det (h : M22) :
    HasFDerivAt (fun x : M22 => (((Matrix.of x).det : ℝ) : ℂ)) (detC h) h := by
  have e : (fun x : M22 => (((Matrix.of x).det : ℝ) : ℂ)) =
      fun x => pr 0 0 x * pr 1 1 x - pr 0 1 x * pr 1 0 x := by
    funext x
    rw [Matrix.det_fin_two]
    simp [pr_apply]
  rw [e]
  exact ((pr 0 0).hasFDerivAt.fun_mul (pr 1 1).hasFDerivAt).fun_sub
    ((pr 0 1).hasFDerivAt.fun_mul (pr 1 0).hasFDerivAt)

theorem hasFDerivAt_tt (h : M22) (h0 : al h ≠ 0) :
    HasFDerivAt tt
      ((al h ^ 2)⁻¹ • detC h +
        ((((Matrix.of h).det : ℝ) : ℂ) * (-((al h ^ 2) ^ 2)⁻¹)) • (al h • alC + al h • alC)) h := by
  have e : tt = fun x => (((Matrix.of x).det : ℝ) : ℂ) / (alC x * alC x) := by
    funext x
    rw [alC_apply, tt, sq]
  have hsq : HasFDerivAt (fun x => alC x * alC x) (al h • alC + al h • alC) h := by
    have := alC.hasFDerivAt.fun_mul (alC.hasFDerivAt (x := h))
    simpa only [alC_apply] using this
  have hne : alC h * alC h ≠ 0 := by
    rw [alC_apply]
    exact mul_ne_zero h0 h0
  have := hasFDerivAt_quot (hasFDerivAt_det h) hsq hne
  rw [e]
  simpa only [alC_apply, ← sq] using this

theorem dd_rpol (a b : Fin 2) (h : M22) :
    dd h (rpol a b h) = if a = b then (Matrix.of h).det else 0 := by
  fin_cases a <;> fin_cases b <;> simp [dd, rpol, Matrix.det_fin_two] <;> ring

theorem norm_tt (h : M22) (hΔ : 0 < (Matrix.of h).det) : ‖tt h‖ = uu h := by
  rw [tt, uu, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΔ]

theorem norm_fderiv_rho (a b c d : Fin 2) (h : M22) (h0 : al h ≠ 0) :
    ‖fderiv ℝ (rho c d) h (rpol a b h)‖ ≤ 2 := by
  rw [(hasFDerivAt_rho c d h h0).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    rC_apply, alC_apply]
  have hA : 0 < ‖al h‖ := norm_pos_iff.mpr h0
  have b1 : ‖(al h)⁻¹ * al (rpol c d (rpol a b h))‖ ≤ 1 := by
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ hA, mul_one]
    exact norm_al_rpol_rpol_le a b c d h
  have b2 : ‖al (rpol c d h) * (-(al h ^ 2)⁻¹) * al (rpol a b h)‖ ≤ 1 := by
    rw [norm_mul, norm_mul, norm_neg, norm_inv, norm_pow]
    have p1 := norm_al_rpol_le c d h
    have p2 := norm_al_rpol_le a b h
    have : ‖al (rpol c d h)‖ * ‖al (rpol a b h)‖ ≤ ‖al h‖ ^ 2 := by
      rw [sq]
      exact mul_le_mul p1 p2 (norm_nonneg _) (norm_nonneg _)
    calc ‖al (rpol c d h)‖ * (‖al h‖ ^ 2)⁻¹ * ‖al (rpol a b h)‖
        = (‖al (rpol c d h)‖ * ‖al (rpol a b h)‖) / ‖al h‖ ^ 2 := by
          rw [div_eq_mul_inv]; ring
      _ ≤ 1 := div_le_one_of_le₀ this (by positivity)
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add b1 b2
    _ = 2 := by norm_num

theorem norm_fderiv_tt (a b : Fin 2) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    ‖fderiv ℝ tt h (rpol a b h)‖ ≤ 3 * uu h := by
  have h0 := al_ne h hΔ
  rw [(hasFDerivAt_tt h h0).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    alC_apply, detC_apply, dd_rpol]
  set δ : ℂ := if a = b then 1 else 0 with hδ
  have hdd : (((if a = b then (Matrix.of h).det else 0 : ℝ)) : ℂ) =
      δ * (((Matrix.of h).det : ℝ) : ℂ) := by
    rw [hδ]
    split_ifs <;> simp
  rw [hdd]
  have key : (al h ^ 2)⁻¹ * (δ * (((Matrix.of h).det : ℝ) : ℂ)) +
      (((Matrix.of h).det : ℝ) : ℂ) * (-((al h ^ 2) ^ 2)⁻¹) *
        (al h * al (rpol a b h) + al h * al (rpol a b h)) =
      tt h * (δ - 2 * (al (rpol a b h) / al h)) := by
    rw [tt]
    field_simp
    ring
  rw [key, norm_mul, norm_tt h hΔ, mul_comm]
  have hA : 0 < ‖al h‖ := norm_pos_iff.mpr h0
  have huu : 0 ≤ uu h := by
    rw [← norm_tt h hΔ]
    exact norm_nonneg _
  refine mul_le_mul_of_nonneg_right ?_ huu
  have n1 : ‖δ‖ ≤ 1 := by
    rw [hδ]
    split_ifs <;> simp
  have n2 : ‖2 * (al (rpol a b h) / al h)‖ ≤ 2 := by
    rw [norm_mul, norm_div]
    have : ‖al (rpol a b h)‖ / ‖al h‖ ≤ 1 := div_le_one_of_le₀ (norm_al_rpol_le a b h) hA.le
    simpa using this
  calc _ ≤ ‖δ‖ + ‖2 * (al (rpol a b h) / al h)‖ := norm_sub_le _ _
    _ ≤ 1 + 2 := add_le_add n1 n2
    _ = 3 := by norm_num

theorem main : ∀ (a b c d : Fin 2) (h : M22), 0 < (Matrix.of h).det →
    DifferentiableAt ℝ (rho c d) h ∧ DifferentiableAt ℝ tt h ∧
      ‖fderiv ℝ (rho c d) h (rpol a b h)‖ ≤ 2 ∧ ‖fderiv ℝ tt h (rpol a b h)‖ ≤ 3 * uu h := by
  intro a b c d h hΔ
  have h0 := al_ne h hΔ
  exact ⟨(hasFDerivAt_rho c d h h0).differentiableAt, (hasFDerivAt_tt h h0).differentiableAt,
    norm_fderiv_rho a b c d h h0, norm_fderiv_tt a b h hΔ⟩

end GlobalTheory.CompanionTheory.DInt2.Drho
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackSchwartzLinearIndependent
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.PullSch

theorem exists_mul_eq_one_of_linearIndependent {K : Type} [Field K] {r n : ℕ} (c : Matrix (Fin r) (Fin n) K)
    (hc : LinearIndependent K c) : ∃ d : Matrix (Fin n) (Fin r) K, c * d = 1 := by
  have hinj : Function.Injective (Matrix.toLin' cᵀ) := by
    intro v w hvw
    have h1 : ∀ u : Fin r → K, Matrix.toLin' cᵀ u = ∑ i, u i • c i := by
      intro u
      funext j
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [h1, h1] at hvw
    have h2 := Fintype.linearIndependent_iff.1 hc (v - w) (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hvw, sub_self])
    funext i
    exact sub_eq_zero.1 (h2 i)
  obtain ⟨h, hh⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' cᵀ) (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨(LinearMap.toMatrix' h)ᵀ, ?_⟩
  have e : LinearMap.toMatrix' h * cᵀ = 1 := by
    rw [← LinearMap.toMatrix'_toLin' cᵀ, ← LinearMap.toMatrix'_comp, hh, LinearMap.toMatrix'_id]
  rw [← Matrix.transpose_transpose c, ← Matrix.transpose_mul, e, Matrix.transpose_one]

theorem mul_map_finPart (D : D7) {m r n : ℕ} (x : Mx D m r) (C : Mx D r n) (Dm : Mx D n r) (hCD : C * Dm = 1) :
    (x * C).map (finPart D) * Dm.map (finPart D) = x.map (finPart D) := by
  have e1 : x = x * C * Dm := by rw [Matrix.mul_assoc, hCD, Matrix.mul_one]
  conv_rhs => rw [e1]
  simp only [Matrix.map_mul]

theorem exists_finPart_section (D : D7) :
    ∃ s : Af D.host.F ⊗[D.host.F] D.host.E → AE D, Continuous s ∧ ∀ a, finPart D (s a) = a := by
  obtain ⟨e, he, -, hes⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨fun a => e.symm (0, a), hes.comp (continuous_const.prodMk continuous_id), fun a => ?_⟩
  have h := (he (e.symm (0, a))).2
  have h2 : (e (e.symm (0, a))).2 = a := by simp
  exact h.symm.trans h2

theorem continuous_lift_mul (D : D7) {m n r : ℕ} (Dm : Mx D n r) (s : Af D.host.F ⊗[D.host.F] D.host.E → AE D)
    (hs : Continuous s) :
    Continuous (fun z : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => (z.map s * Dm).map (finPart D)) :=
  ((continuous_id.matrix_map hs).matrix_mul continuous_const).matrix_map (GlobalTheory.Member.continuous_finPart D)

def mulR (D : D7) (m : ℕ) {r n : ℕ} (C : Mx D r n) : Mx D m r →+ Mx D m n where
  toFun y := y * C
  map_zero' := Matrix.zero_mul _
  map_add' a b := Matrix.add_mul a b C

theorem mulR_apply (D : D7) (m : ℕ) {r n : ℕ} (C : Mx D r n) (y : Mx D m r) : mulR D m C y = y * C := rfl

theorem continuous_mulR (D : D7) (m : ℕ) {r n : ℕ} (C : Mx D r n) : Continuous (mulR D m C) :=
  continuous_id.matrix_mul continuous_const

theorem injective_mulR (D : D7) (m : ℕ) {r n : ℕ} (C : Mx D r n) (Dm : Mx D n r) (hCD : C * Dm = 1) :
    Function.Injective (mulR D m C) := fun a b h => by
  have h' : a * C * Dm = b * C * Dm := congrArg (· * Dm) h
  rwa [Matrix.mul_assoc, Matrix.mul_assoc, hCD, Matrix.mul_one, Matrix.mul_one] at h'

theorem isRealParam_mulR_comp (D : D7) {m r n k : ℕ} (C : Mx D r n) (L : (Fin k → ℝ) →+ Mx D m r)
    (hL : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam L) : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam ((mulR D m C).comp L) := by
  refine ⟨(continuous_mulR D m C).comp hL.1, fun t => ?_⟩
  rw [AddMonoidHom.comp_apply, mulR_apply, Matrix.map_mul, hL.2 t, Matrix.zero_mul]

theorem injective_comp (D : D7) {m r n k : ℕ} (C : Mx D r n) (Dm : Mx D n r) (hCD : C * Dm = 1)
    (L : (Fin k → ℝ) →+ Mx D m r) (hL : Function.Injective L) : Function.Injective ((mulR D m C).comp L) := by
  intro a b h
  exact hL (injective_mulR D m C Dm hCD h)

theorem pullSchLI : PositivityTheory.GramSchwartzFunctions.PullSchLI := by
  intro D θ hθ m r n c hc φ hφ
  obtain ⟨d, hcd⟩ := exists_mul_eq_one_of_linearIndependent c hc
  rw [← GlobalTheory.SchwartzIff.isSchwartzBruhat_iff_mem_schwartzA D θ hθ] at hφ ⊢
  set C : Mx D r n := c.map (incA D) with hC
  set Dm : Mx D n r := d.map (incA D) with hD
  have hCD : C * Dm = 1 := by
    rw [hC, hD, ← Matrix.map_mul, hcd, Matrix.map_one _ (map_zero _) (map_one _)]
  have hpull : ∀ y, pull c φ y = φ (mulR D m C y) := fun y => rfl
  obtain ⟨hlev, hsupp, hsch⟩ := hφ
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨U, hUo, hU⟩ := hlev
    refine ⟨U.comap (mulR D m C), hUo.preimage (continuous_mulR D m C), fun u hu h0 x => ?_⟩
    have h0' : (mulR D m C u).map (infPart D) = 0 := by
      rw [mulR_apply, Matrix.map_mul, h0, Matrix.zero_mul]
    rw [hpull, hpull, map_add, hU _ hu h0']
  · obtain ⟨K, hK, hKs⟩ := hsupp
    obtain ⟨s, hs, hfs⟩ := exists_finPart_section D
    have h1 : ∀ y : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E), (y.map s).map (finPart D) = y :=
      fun y => by
        ext i j
        simp [hfs]
    refine ⟨(fun z => (z.map s * Dm).map (finPart D)) '' K, hK.image (continuous_lift_mul D Dm s hs),
      fun x hx => ⟨(mulR D m C x).map (finPart D), hKs _ hx, ?_⟩⟩
    rw [mulR_apply]
    show ((((x * C).map (finPart D)).map s) * Dm).map (finPart D) = x.map (finPart D)
    rw [Matrix.map_mul (L := ((x * C).map (finPart D)).map s), h1]
    exact mul_map_finPart D x C Dm hCD
  · intro k L hL hLinj x
    obtain ⟨g, hg⟩ := hsch k ((mulR D m C).comp L) (isRealParam_mulR_comp D C L hL)
      (injective_comp D C Dm hCD L hLinj) (mulR D m C x)
    exact ⟨g, fun t => by rw [hg, hpull, map_add, AddMonoidHom.comp_apply]⟩

end GlobalTheory.CompanionTheory.PullSch
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalCharacterKernelScaling
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatTest

theorem trace_tmul_eq {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] (r : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] e) = r * algebraMap F R (Algebra.trace F E e) := by
  have h1 : (r ⊗ₜ[F] e : R ⊗[F] E) = r • ((1 : R) ⊗ₜ[F] e) := by
    simp [TensorProduct.smul_tmul']
  have h2 : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e)
      = LinearMap.baseChange R (Algebra.lmul F E e) := by
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s y => simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [h1, map_smul, Algebra.trace_apply, h2, LinearMap.trace_baseChange, Algebra.trace_apply]
  simp

theorem inNOh_tmul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (N : ℕ) {α : Af F} (hα : α ∈ Oh F) (k : Fin d) :
    InNOh b N (((N : Af F) * α) ⊗ₜ[F] b k) := by
  intro j
  by_cases h : j = k
  · subst h
    exact ⟨α, hα, by simp [Algebra.TensorProduct.basis_repr_tmul]⟩
  · refine ⟨0, fun v => zero_mem _, ?_⟩
    simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.single_apply, Ne.symm h]

theorem exists_common_denom {E : Type} [Field E] [NumberField E] {d : ℕ} (ε : Fin d → E) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ k, IsIntegral ℤ ((y : E) * ε k) := by
  have hex : ∀ k, ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * ε k) := by
    intro k
    obtain ⟨y, hy, h⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic (ε k)))
    exact ⟨y, hy, by simpa [zsmul_eq_mul] using h⟩
  choose y hy hint using hex
  refine ⟨∏ k, y k, Finset.prod_ne_zero_iff.mpr fun k _ => hy k, fun k => ?_⟩
  have h1 : (((∏ j, y j : ℤ)) : E) * ε k
      = ((∏ j ∈ Finset.univ.erase k, y j : ℤ) : E) * ((y k : E) * ε k) := by
    rw [← mul_assoc, ← Int.cast_mul, mul_comm (∏ j ∈ Finset.univ.erase k, y j) (y k),
      Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  rw [h1]
  have h2 : IsIntegral ℤ (((∏ j ∈ Finset.univ.erase k, y j : ℤ)) : E) := by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (∏ j ∈ Finset.univ.erase k, y j : ℤ))
  exact h2.mul (hint k)

theorem rat_test : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ),
    IsCharAF F ψ → ∀ N : ℕ, 0 < N → ∀ D : ℕ, 0 < D → (∀ f : F,
      (∀ r : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F (f * (r : F)) = m) → ∃ o : 𝓞 F, (o : F) = (D : F) * f) →
    ∃ t : F, t ≠ 0 ∧ ∀ w : E, (∀ x : Af F ⊗[F] E, InNOh b N x →
        psiFin F ψ (Algebra.trace (Af F) (Af F ⊗[F] E) (sigR (Af F) σ x * inclR (Af F) w)) = 1) →
      ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = t • w := by
  intro F E _ _ _ _ _ σ hCM d b ψ hψ N hN D hD hDint
  have hF : IsTotallyReal F := hCM.1
  obtain ⟨ρ, e, h1, h2, h3, -, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hF
  obtain ⟨a, ha, -, ψf, hstd, hpsi⟩ := GlobalTheory.T.adelic_character_archimedean_form F hF ρ e h1 h2 h3 ψ hψ
  have hbeta := ((GlobalTheory.T.standard_adelic_character F).2 ψf hstd).2.2
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  let τ : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  let b' : Module.Basis (Fin d) F E := b.map τ.toLinearEquiv
  have hb' : ∀ k, b' k = σ (b k) := fun k => by simp [b', τ]
  let ε := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b'
  obtain ⟨y, hy, hyint⟩ := exists_common_denom (fun k => ε k)
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hDF : (D : F) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
  have hyF : (y : F) ≠ 0 := Int.cast_ne_zero.mpr hy
  refine ⟨(y : F) * ((D : F) * (a * (N : F))), mul_ne_zero hyF (mul_ne_zero hDF (mul_ne_zero ha hNF)), ?_⟩
  intro w hw

  have hcoord : ∀ k, ∃ o : 𝓞 F, (o : F) = (D : F) * (a * (N : F) * ε.repr w k) := by
    intro k
    have hrepr : ε.repr w k = Algebra.trace F E (σ (b k) * w) := by
      rw [LinearMap.BilinForm.dualBasis_repr_apply, hb', Algebra.traceForm_apply, mul_comm]
    refine hDint _ ((hbeta _).mp fun α hα => ?_)
    have hx := hw (((N : Af F) * α) ⊗ₜ[F] b k) (inNOh_tmul b N hα k)
    have e1 : sigR (Af F) σ (((N : Af F) * α) ⊗ₜ[F] b k) * inclR (Af F) w
        = ((N : Af F) * α) ⊗ₜ[F] (σ (b k) * w) := by
      change (((N : Af F) * α) ⊗ₜ[F] σ (b k)) * ((1 : Af F) ⊗ₜ[F] w) = _
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [e1, trace_tmul_eq] at hx
    change ψ (pairA F 0 _) = 1 at hx
    rw [hpsi] at hx
    rw [hrepr, ← hx]
    congr 1
    simp only [map_mul, map_natCast]
    ring
  choose o ho using hcoord
  rw [← IsIntegralClosure.isIntegral_iff (A := 𝓞 E) (R := ℤ), ← ε.sum_repr w, Finset.smul_sum]
  refine IsIntegral.sum _ fun k _ => ?_
  have e2 : ((y : F) * ((D : F) * (a * (N : F)))) • (ε.repr w k • ε k)
      = algebraMap F E (o k : F) * ((y : E) * ε k) := by
    have e3 : (y : F) * ((D : F) * (a * (N : F))) * ε.repr w k
        = (y : F) * ((D : F) * (a * (N : F) * ε.repr w k)) := by ring
    rw [smul_smul, Algebra.smul_def, e3, ho k, map_mul, map_intCast]
    ring
  rw [e2]
  exact (IsIntegral.algebraMap (RingOfIntegers.isIntegral_coe (o k))).mul (hyint k)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatTest
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReversedProductSameSubquotients
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenRev

theorem isSubquotient_of_equiv {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} {ρ' : Representation ℂ G U}
    (h : IsSubquotient σ ρ) (E : ρ.Equiv ρ') : IsSubquotient σ ρ' :=
  h.trans (IsSubquotient.of_surjective E.symm.toIntertwiningMap E.symm.surjective)

theorem isSubquotient_of_equiv_left {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {τ : Representation ℂ G U}
    {ρ : Representation ℂ G V} (E : σ.Equiv τ) (h : IsSubquotient σ ρ) : IsSubquotient τ ρ :=
  (IsSubquotient.of_surjective E.toIntertwiningMap E.surjective).trans h

set_option maxHeartbeats 2000000 in

theorem isSubquotient_prodIrr_rev : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k →
    ∀ {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x (Fin.rev a)).1 = N) {W : Type}
      [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible →
      IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (Fin.rev a)) hd') := by
  intro k _ _ _ _ hA hGK h N x hd hd' W _ _ σ _ hi hsq

  obtain ⟨hdy, ⟨E1⟩⟩ := GlobalTheory.T.contragredient_product_irreducible hA (fun a => x (Fin.rev a)) hd'

  obtain ⟨hd2, ⟨E2⟩⟩ := GlobalTheory.T.product_transpose_inverse_dual_reverse hA hGK (fun a => Zc.dualCl (x (Fin.rev a))) hdy
  have ex : (fun a => Zc.dualCl ((fun a => Zc.dualCl (x (Fin.rev a))) (Fin.rev a))) = x := funext fun a => by
    simp only [Fin.rev_rev]
    exact GlobalTheory.T.dual_class_involutive hA (x a)
  obtain ⟨E3⟩ := GlobalTheory.CompanionTheory.LSocle.prodIrr_congr ex hd2 hd
  have h1 : IsSubquotient σ ((prodIrr (fun a => Zc.dualCl (x (Fin.rev a))) hdy).comp (Zc.Cos.thetaW k N)) :=
    isSubquotient_of_equiv hsq (E2.trans E3).symm
  have h2 : IsSubquotient (σ.comp (Zc.Cos.thetaW k N)) (prodIrr (fun a => Zc.dualCl (x (Fin.rev a))) hdy) := by
    have := GlobalTheory.CompanionTheory.WordProd.RowCell.isSubquotient_pullback (Zc.Cos.thetaW k N) h1
    rwa [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW] at this
  have hs : IsSmooth (σ.comp (Zc.Cos.thetaW k N)) := h2.isSmooth (isSmooth_prodIrr _ _)
  have hi' : Representation.IsIrreducible (σ.comp (Zc.Cos.thetaW k N)) :=
    GlobalTheory.CosocleComp.isIrreducible_comp (GlobalTheory.CompanionTheory.LSocle.thetaW_surjective N) hi
  have h3 : IsSubquotient (σ.comp (Zc.Cos.thetaW k N)) (contra (prodIrr (fun a => x (Fin.rev a)) hd')) :=
    isSubquotient_of_equiv h2 E1.symm
  have h4 := GlobalTheory.T.isSubquotient_contra_of_isSubquotient (GlobalTheory.SqIntUnit.compactOpen_basis k N) _ _ (isSmooth_contra _) h3
  obtain ⟨E4⟩ := GlobalTheory.T.double_contragredient_of_induced_product hA (fun a => x (Fin.rev a)) hd'
  obtain ⟨E5⟩ := GlobalTheory.CompanionTheory.LSocle.equiv_contra_comp_thetaW hGK σ hs hi'
  exact isSubquotient_of_equiv_left E5.symm (isSubquotient_of_equiv h4 E4)

end GlobalTheory.CompanionTheory.GenRev
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportSubschemeEmbedding
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.SubEmb

theorem subEmbedding : Ysupp.SubEmbedding :=
  subEmbedding_of_stage GlobalTheory.T.product_irreducible_append_equiv

end GlobalTheory.CompanionTheory.SubEmb
end

