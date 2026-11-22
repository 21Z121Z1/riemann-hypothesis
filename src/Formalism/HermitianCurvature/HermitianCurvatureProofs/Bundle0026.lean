import Formalism.HermitianCurvature.StatementG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhaseFunctionCriticalPoints
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AffineChangeOfVariables
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralConvergesAbs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardCharacterExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0009
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeakApproximationGL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WhittakerVanishingImpliesZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0012
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitTailEstimates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WirtingerIntegrationByParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhaseFunctionDerivatives
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EtaleIntegralityFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StationaryPhaseEstimates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StationaryPhaseModel
import Formalism.HermitianCurvature.StatementM
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0023

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChangeOfVariablesXy
section
namespace Formalism.FourierDecayAlt.P

theorem orbit_tail_estimate : Formalism.FourierDecayAlt.G.TailStep :=
  tail_estimate_of_bound tailBound_statement matrix_cutoff_spec cutoff_phase_bound

theorem change_of_variables_xy : Formalism.FourierDecayAlt.G.InnerXY :=
  inner_xy_of_reduced orbital_integral_reduced reduced_integrand_integrable split_xy_coordinates amplitude_eq

theorem nonstationary_estimate : Formalism.FourierDecayAlt.G.NonStatStep :=
  nonstationary_estimate_of_parts nonstationary_phase gradient_lower_bound phase_function_deriv phase_relative_deriv
    critical_cutoff_spec amplitude_bound_far orbital_integral_converges_abs cutoff_phase_bound change_of_variables_xy

theorem stationary_estimate : Formalism.FourierDecayAlt.G.StatStep :=
  stationary_estimate_of_parts stationary_phase_holomorphic phase_function_deriv phase_function_critical_points hessian_at_critical hessian_determinant
    phase_near_critical critical_cutoff_spec amplitude_bound_critical amplitude_continuous_at_critical majorant_y
    orbital_integral_converges_abs cutoff_phase_bound change_of_variables_xy

theorem germ_rate : Formalism.FourierDecayAlt.G.GermRate :=
  germ_rate_of_estimates orbital_integral_converges_abs cutoff_phase_bound critical_cutoff_spec exists_small_delta
    root_set_characterization orbit_tail_estimate change_of_variables_xy nonstationary_estimate stationary_estimate amplitude_limit
    limit_integral stationary_leading_constant germ_large_parameter

theorem germExpansion_true : Formalism.FourierDecayAlt.G.Germ :=
  germ_of_rate germ_rate

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelWordsAssemble
section
namespace Formalism.FourierDecayAlt.P

open Matrix Finset Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.M

namespace Mx9

theorem eq_ofReal {z : ℂ} (h : z.im = 0) : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h])

theorem star_eq {z : ℂ} (h : z.im = 0) : star z = z := by
  exact Complex.conj_eq_iff_im.mpr h

theorem far {z z' : ℂ} (h : 2 < |z.re - z'.re|) (n : ℤ) (hn : |n| ≤ 2) : z - z' ≠ (n : ℂ) := by
  intro heq
  have h1 := congrArg Complex.re heq
  simp only [Complex.sub_re, Complex.intCast_re] at h1
  rw [h1] at h
  have h2 : ((|n| : ℤ) : ℝ) ≤ 2 := by exact_mod_cast hn
  rw [Int.cast_abs] at h2
  linarith

noncomputable def ty0 (P : Par) : Ty P := fun _ => 0

theorem xC_ne (hR : RealPoints) (P : Par) (π : Ty P) (n : ℕ) (Y : ℝ)
    (h : 0 < (-1 : ℝ) ^ n * I.xpoly P.k (rho P π) Y) : xC P π (Y : ℂ) ≠ 0 := by
  intro h0
  rw [(hR P π Y).1] at h0
  have h1 : I.xpoly P.k (rho P π) Y = 0 := by exact_mod_cast h0
  rw [h1, mul_zero] at h
  exact lt_irrefl _ h

theorem qC_ne (hR : RealPoints) (P : Par) (Y : ℝ)
    (h : 0 < I.qpoly P.k P.T P.T' P.u P.u' Y) : qC P (Y : ℂ) ≠ 0 := by
  intro h0
  rw [(hR P (ty0 P) Y).2] at h0
  have h1 : I.qpoly P.k P.T P.T' P.u P.u' Y = 0 := by exact_mod_cast h0
  rw [h1] at h
  exact lt_irrefl _ h

theorem ypt_im {S : Type} (a : Letter ℂ S) (h : a.pt.im = 0) : (ypt a).im = 0 := by
  unfold ypt
  split_ifs <;> simp [h]

theorem site_mem (P : Par) (i : Fin P.r) : siteA P i ∈ sitesFrom P 0 := by
  simp [sitesFrom, List.mem_ofFn]

end Mx9

open Mx9

theorem model_words_assemble : Formalism.FourierDecayAlt.M.ModelWordsAssemble := by
  intro hW hLS hSO hCh hLC P hP l S _ _ w hw
  refine ⟨fun i hi => hW.1 ℂ (A P) S (QQlev P l i) (qC P) w (hLS P hP l i hi) hw, ?_, ?_⟩
  · intro i
    have hσ := ((hSO P l).1 (siteA P i) (site_mem P i))
    refine hW.2.1 ℂ (A P) S (siteA P i) (QQlev P l (i + 1)) (QQlev P l i) w hσ.1 (hLC P l i) ?_ hw
    intro Y hY
    have h := (hCh P l).2 i Y
    rw [hY] at h
    exact h
  · intro Y hY hs z
    exact hW.2.2.2.1 ℂ (A P) S _ _ w Y (hSO P l) hw hY hs z

theorem cut_admissible : Formalism.FourierDecayAlt.M.CutAdm := by
  intro hIS hQP hQS hTy hR P hP l hl1 hlk S _ _ w hw
  obtain ⟨hnd, hpt, hpw⟩ := hw
  have key : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → ∀ e ∈ ({-1, 0, 1} : Finset ℝ),
      ((Y + e : ℝ) : ℂ) ∈ (startM P l).inv := by
    intro Y hY e he
    show ∀ π, xC P π _ ≠ 0
    intro π
    exact xC_ne hR P π (P.k - l) (Y + e) (hIS P.k P.u P.u' (rho P π) l Y hl1 hlk (hTy P hP π) hY e he)
  have qpos : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → (startM P l).q (Y : ℂ) ≠ 0 := by
    intro Y hY
    exact qC_ne hR P Y (hQP P.k P.u P.u' (rho P (ty0 P)) l Y P.T P.T' hl1 hlk (hTy P hP (ty0 P)) hY
      hP.T_pos hP.T'_pos)
  have qsh : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → (startM P l).q ((Y : ℂ) - 1) ≠ 0 := by
    intro Y hY
    have h := qC_ne hR P (Y - 1) (hQS P.k P.u P.u' (rho P (ty0 P)) l Y P.T P.T' hl1 hlk (hTy P hP (ty0 P)) hY
      hP.T_pos hP.T'_pos)
    push_cast at h
    exact h
  refine ⟨hnd, fun a ha => star_eq (hpt a ha).1, fun a ha => ?_, hpw.imp fun h n hn => far h n hn⟩
  obtain ⟨him, hcut⟩ := hpt a ha
  have hz : a.pt = ((a.pt.re : ℝ) : ℂ) := eq_ofReal him
  rw [hz]
  refine ⟨?_, ?_, ?_, qpos _ hcut, qsh _ hcut⟩
  · convert key _ hcut 0 (by norm_num) using 1 <;> push_cast <;> ring
  · convert key _ hcut 1 (by norm_num) using 1 <;> push_cast <;> ring
  · convert key _ hcut (-1) (by norm_num) using 1 <;> push_cast <;> ring

theorem cut_admissible_base : Formalism.FourierDecayAlt.M.CutAdmBase := by
  intro hIS hIS2 hQP hQS hTy hR P hP l hl1 hlk S _ _ w hw
  obtain ⟨hnd, hpt, hpw⟩ := hw
  have key : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → ∀ e ∈ ({-1, 0, 1} : Finset ℝ),
      ((Y + e : ℝ) : ℂ) ∈ (startM P l).inv := by
    intro Y hY e he
    show ∀ π, xC P π _ ≠ 0
    intro π
    exact xC_ne hR P π (P.k - l) (Y + e) (hIS P.k P.u P.u' (rho P π) l Y hl1 hlk (hTy P hP π) hY e he)
  have qpos : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → (startM P l).q (Y : ℂ) ≠ 0 := by
    intro Y hY
    exact qC_ne hR P Y (hQP P.k P.u P.u' (rho P (ty0 P)) l Y P.T P.T' hl1 hlk (hTy P hP (ty0 P)) hY
      hP.T_pos hP.T'_pos)
  have qsh : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → (startM P l).q ((Y : ℂ) - 1) ≠ 0 := by
    intro Y hY
    have h := qC_ne hR P (Y - 1) (hQS P.k P.u P.u' (rho P (ty0 P)) l Y P.T P.T' hl1 hlk (hTy P hP (ty0 P)) hY
      hP.T_pos hP.T'_pos)
    push_cast at h
    exact h
  have key2 : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → ((Y + 2 : ℝ) : ℂ) ∈ (startM P l).inv := by
    intro Y hY
    show ∀ π, xC P π _ ≠ 0
    intro π
    exact xC_ne hR P π (P.k - l) (Y + 2) (hIS2 P.k P.u P.u' (rho P π) l Y hl1 hlk (hTy P hP π) hY 2 (by norm_num))
  refine ⟨hnd, fun a ha => star_eq (hpt a ha).1, fun a ha => ?_, hpw.imp fun h n hn => far h n hn⟩
  obtain ⟨him, hcut⟩ := hpt a ha
  have hz : ypt a = (((ypt a).re : ℝ) : ℂ) := eq_ofReal (ypt_im a him)
  rw [hz]
  rcases hcut with hc | hc
  · refine ⟨?_, ?_, fun _ => ?_, qpos _ hc⟩
    · convert key _ hc 0 (by norm_num) using 1 <;> push_cast <;> ring
    · convert key _ hc 1 (by norm_num) using 1 <;> push_cast <;> ring
    · convert key2 _ hc using 1 <;> push_cast <;> ring
  · refine ⟨?_, ?_, fun _ => ?_, ?_⟩
    · convert key _ hc (-1) (by norm_num) using 1 <;> push_cast <;> ring
    · convert key _ hc 0 (by norm_num) using 1 <;> push_cast <;> ring
    · convert key _ hc 1 (by norm_num) using 1 <;> push_cast <;> ring
    · convert qsh _ hc using 2 <;> push_cast <;> ring

theorem model_assemble : Formalism.FourierDecayAlt.M.ModelAssemble := by
  intro hIS hQP hQS hCP hCPC hFA hFW hCD hLE hLS hSO hTy hR hCA P hP l hl1 hlk
  obtain ⟨L, hL⟩ := hLE P
  have hst := hLS P L hL
  have hstart := hSO P hP l L hL
  refine ⟨L, hL, hst, hstart, ?_⟩
  intro S _ _ w hw
  have hAdm := hCA hIS hQP hQS hTy hR P hP l hl1 hlk S w hw
  obtain ⟨_, _, h3, h4, h5⟩ := hFW (A P) S P.r L (startM P l) w hst hstart hAdm
  refine ⟨hFA (A P) S P.r L (startM P l) w hst hstart hAdm, h3, h4, h5, ?_, ?_⟩
  · exact (hCD (A P) S P.r L (startM P l) (Ty P) (kap P) (fun π Y => x0 P l π Y)
      (fun Y => rfl) (fun Y => rfl) w).2.2
  · intro e π
    exact hCPC hIS hQP hQS hCP S P.k P.u P.u' (rho P π) l P.T P.T' w hl1 hlk (hTy P hP π)
      hP.T_pos hP.T'_pos hw.2.1 hw.2.2 e

theorem model_assemble_base : Formalism.FourierDecayAlt.M.ModelAssembleBase := by
  intro hIS hIS2 hQP hQS hCPB hCPCB hFAR hARB hWJ hCD hLE hLS hSO hTy hR hCAB P hP l hl1 hlk
  obtain ⟨L, hL⟩ := hLE P
  have hst := hLS P L hL
  have hstart := hSO P hP l L hL
  refine ⟨L, hL, hst, hstart, ?_⟩
  intro S _ _ w hw
  have hAB := hCAB hIS hIS2 hQP hQS hTy hR P hP l hl1 hlk S w hw
  have hAR := hARB (A P) S P.r L (startM P l) w hAB
  have hF := hFAR (A P) S P.r L (startM P l) w hst hstart hAR
  obtain ⟨jRR, jTT, _, jN, jreg⟩ := hWJ (A P) S P.r L (startM P l) w
  refine ⟨hF, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← jRR, hF.form, FrameData.d, jN]
  · intro Y hY
    have h := hF.frame_τ Y (by rw [jreg]; exact hY)
    rwa [jTT] at h
  · intro Y hY hY1
    have h := hF.frame_l Y hY hY1
    rwa [jTT, FrameData.l] at h
  · exact (hCD (A P) S P.r L (startM P l) (Ty P) (kap P) (fun π Y => x0 P l π Y)
      (fun Y => rfl) (fun Y => rfl) w).2.2
  · intro e π
    exact hCPCB hIS hQP hQS hCPB S P.k P.u P.u' (rho P π) l P.T P.T' w hl1 hlk (hTy P hP π)
      hP.T_pos hP.T'_pos hw.2.1 hw.2.2 e

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MultiplicationOpHom
section
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset

namespace Formalism.FourierDecayAlt.P.Mx1

theorem coord_ne (r : ℕ) (v : Var r) : coord v ≠ 0 := by
  simp [coord]

theorem vz_ne {r : ℕ} : (vz : Var r) ≠ vzb := by
  simp [vz, vzb]

theorem euler_support {r : ℕ} (v : Var r) (f : Fn r) : (euler v f).support ⊆ f.support := by
  intro γ hγ
  rw [HahnSeries.mem_support] at hγ ⊢
  intro h
  apply hγ
  show ((ofLex γ v : ℤ) : ℂ) * f.coeff γ = 0
  rw [h, mul_zero]

theorem star_sc (P : Par) (w : Pr P.r) : star (sc P w) = sc P (star w) := by
  unfold sc
  ext i j
  rw [Matrix.star_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

end Formalism.FourierDecayAlt.P.Mx1

namespace Formalism.FourierDecayAlt.P

open Mx1

theorem multiplication_op_hom : Formalism.FourierDecayAlt.M.MulOpHom := by
  intro r f g z
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine LinearMap.ext fun x => ?_ <;>
    simp [mulOp, mul_assoc, add_mul, Algebra.smul_def]

theorem euler_leibniz : Formalism.FourierDecayAlt.M.EulerLeibniz := by
  intro r v f g
  have hc : ∀ (v : Var r) (h : Fn r) (γ : Expo r), (euler v h).coeff γ = ((ofLex γ v : ℤ) : ℂ) * h.coeff γ :=
    fun _ _ _ => rfl
  ext γ
  rw [hc, HahnSeries.coeff_add, HahnSeries.coeff_mul_left' f.isPWO_support (Mx1.euler_support v f),
    HahnSeries.coeff_mul_right' g.isPWO_support (Mx1.euler_support v g), HahnSeries.coeff_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  obtain ⟨-, -, hsum⟩ := Finset.mem_addAntidiagonal.1 hij
  rw [hc, hc, ← hsum, ofLex_add, Pi.add_apply]
  push_cast
  ring

theorem euler_coordinates : Formalism.FourierDecayAlt.M.EulerCoord := by
  intro r v w z
  have hc : ∀ (v : Var r) (h : Fn r) (γ : Expo r), (euler v h).coeff γ = ((ofLex γ v : ℤ) : ℂ) * h.coeff γ :=
    fun _ _ _ => rfl
  constructor
  · ext γ
    rw [hc]
    by_cases hvw : v = w
    · subst hvw
      rw [if_pos rfl]
      simp only [coord, HahnSeries.coeff_single]
      split_ifs with hγ
      · subst hγ
        simp
      · simp
    · rw [if_neg hvw]
      simp only [coord, HahnSeries.coeff_single, HahnSeries.coeff_zero]
      split_ifs with hγ
      · subst hγ
        simp [Pi.single_apply, hvw]
      · simp
  · ext γ
    rw [hc]
    simp only [HahnSeries.algebraMap_apply, HahnSeries.C_apply, HahnSeries.coeff_single,
      HahnSeries.coeff_zero, Algebra.algebraMap_self, RingHom.id_apply]
    split_ifs with hγ
    · subst hγ
      simp
      left
      rfl
    · simp

theorem euler_commute : Formalism.FourierDecayAlt.M.EulerComm := by
  intro r v w
  have hc : ∀ (v : Var r) (h : Fn r) (γ : Expo r), (euler v h).coeff γ = ((ofLex γ v : ℤ) : ℂ) * h.coeff γ :=
    fun _ _ _ => rfl
  refine LinearMap.ext fun f => ?_
  ext γ
  simp only [Module.End.mul_apply, hc]
  ring

theorem eulerMul_statement : Formalism.FourierDecayAlt.M.EulerMul := by
  intro r v f
  refine LinearMap.ext fun g => ?_
  simp only [Module.End.mul_apply, LinearMap.add_apply, mulOp, LinearMap.mulLeft_apply]
  rw [euler_leibniz r v f g, add_comm]

theorem function_nonzero : Formalism.FourierDecayAlt.M.FnNonzero := by
  intro r v TT
  refine ⟨coord_ne r v, fun h => ?_⟩
  have he : (toLex (Pi.single vz 1) + toLex (Pi.single vzb 1) : Expo r) ≠ 0 := by
    intro h0
    have := congrFun (congrArg ofLex h0) vz
    change ((Pi.single vz (1 : ℤ) + Pi.single vzb 1 : Var r → ℤ) vz) = (0 : Var r → ℤ) vz at this
    simp [Pi.single_apply, vz_ne (r := r)] at this
  have hc := congrArg (fun s : Fn r => s.coeff (toLex (Pi.single vz 1) + toLex (Pi.single vzb 1))) h
  simp [gg, coord, HahnSeries.single_mul_single, HahnSeries.algebraMap_apply, HahnSeries.C_apply,
    HahnSeries.coeff_single, he] at hc

theorem model_nontrivial : Formalism.FourierDecayAlt.M.ModelNontrivial := by
  intro P
  have key : ∀ w : Pr P.r, sc P w = 0 → w = 0 := by
    intro w h
    have := congrFun (congrFun h (fun _ => 0)) (fun _ => 0)
    simpa [sc] using this
  refine ⟨⟨⟨0, 1, fun h => ?_⟩⟩, fun f fb h => ?_⟩
  · have h1 : (1 : Pr P.r) = 0 := key 1 (by unfold sc; rw [map_one]; exact h.symm)
    have h2 : (1 : Op P.r) (1 : Fn P.r) = (0 : Op P.r) 1 :=
      congrArg (fun w : Pr P.r => (w.1 : Op P.r) (1 : Fn P.r)) h1
    simp at h2
  · have h1 := key _ h
    have h2 : (mulOp f) (1 : Fn P.r) = (0 : Op P.r) 1 :=
      congrArg (fun w : Pr P.r => (w.1 : Op P.r) (1 : Fn P.r)) h1
    simpa [mulOp] using h2

theorem star_generators : Formalism.FourierDecayAlt.M.StarGens := by
  intro P
  have hs : ∀ X Y : Op P.r, star (mk X Y) = mk Y X := fun X Y => rfl
  have hneg : ∀ X Y : Op P.r, -(mk X Y : Pr P.r) = mk (-X) (-Y) := fun X Y => rfl
  have mc : ∀ f g : Fn P.r, mulOp f * mulOp g = mulOp g * mulOp f := fun f g => by
    refine LinearMap.ext fun x => ?_
    simp only [mulOp, Module.End.mul_apply, LinearMap.mulLeft_apply, ← mul_assoc, mul_comm f g]
  refine ⟨fun l => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · unfold cA cbA; rw [star_sc]; rfl
  · unfold ciA cbiA; rw [star_sc]; rfl
  · unfold pA pbA
    rw [star_sc]
    unfold sc
    rw [← map_neg]
    congr 1
    unfold pP pbP
    rw [hs, hneg, neg_neg]
  · unfold zA zbA; rw [star_sc]; rfl
  · unfold ziA zbiA; rw [star_sc]; rfl
  · unfold ggA; rw [star_sc]; rfl
  · unfold ggiA; rw [star_sc]; rfl
  · have e1 : star (dzP : Pr P.r) = -dzbP := by
      unfold dzP dzbP
      rw [hs, hneg, neg_neg]
    have e2 : star (zbP : Pr P.r) = zP := rfl
    have e3 : star (ggiP P.TT : Pr P.r) = ggiP P.TT := rfl
    have e4 : (ggiP P.TT : Pr P.r) * zP = zP * ggiP P.TT := by
      unfold ggiP zP fnP M.mk
      refine Prod.ext (mc _ _) ?_
      show MulOpposite.op _ * MulOpposite.op _ = MulOpposite.op _ * MulOpposite.op _
      rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, mc]
    unfold nabA nabsA
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext π
    rw [Pi.star_apply, star_add, star_smul, star_mul, e1, e2, e3, e4, Complex.star_def, Complex.conj_ofReal]

theorem level_star : Formalism.FourierDecayAlt.M.LevelStar := by
  intro P L hL
  obtain ⟨-, -, -, -, -, -, hz, -, hzb, -, -, -, hn, hns, hT⟩ := hL
  have hS := star_generators P
  refine ⟨?_, ?_, ?_⟩
  · rw [hz, hzb]
    exact hS.2.1
  · rw [hn, hns]
    exact hS.2.2.2.2.2
  · rw [hT]
    simp [Complex.star_def, Complex.conj_ofReal]

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThShiftInt
section
open Set Filter Topology Complex MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

theorem Hh_add_int {w : ℂ} (k : ℤ) : w + (k : ℂ) * (2 * Real.pi * I) ∈ Hh TT ↔ w ∈ Hh TT := by
  simp only [Hh, Set.mem_ofPred_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem Hh_add_one {w : ℂ} (hw : w ∈ Hh TT) : w + 2 * Real.pi * I ∈ Hh TT := by
  have := (Hh_add_int (TT := TT) (w := w) 1).2 hw
  simpa using this

theorem th_shift (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) {w : ℂ} (hw : w ∈ Hh TT) :
    th TT α (w + 2 * Real.pi * I) = th TT α w + 2 * (circleIntegral α 0 (TT + 1)).im := by
  have hc : ∀ z ∈ Hh TT, HasFDerivAt (fun z => th TT α (z + 2 * Real.pi * I) - th TT α z)
      (0 : ℂ →L[ℝ] ℝ) z := by
    intro z hz
    have h1 : HasFDerivAt (fun z => th TT α (z + 2 * Real.pi * I)) (om α (z + 2 * Real.pi * I)) z := by
      have := (hasFDerivAt_th hTT hα hcurv (Hh_add_one hz)).comp z
        ((hasFDerivAt_id z).add_const (2 * Real.pi * I))
      exact this
    have h2 := hasFDerivAt_th hTT hα hcurv hz
    have hom : om α (z + 2 * Real.pi * I) = om α z := by
      have := bet_periodic α z 1
      simp only [Int.cast_one, one_mul] at this
      simp only [om, this]
    have := h1.sub h2
    rwa [hom, sub_self] at this
  have hconst := (convex_Hh TT).is_const_of_fderivWithin_eq_zero
    (fun z hz => (hc z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hc z hz).hasFDerivWithinAt.fderivWithin ((isOpen_Hh TT).uniqueDiffWithinAt hz))
    (base_point_mem_half_plane hTT) hw
  rw [th_top hTT hα, theta_at_base_point_zero, sub_zero] at hconst
  linarith

theorem th_shift_int (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) (k : ℤ) :
    ∀ w ∈ Hh TT, th TT α (w + (k : ℂ) * (2 * Real.pi * I)) = th TT α w + k * (2 * (circleIntegral α 0 (TT + 1)).im) := by
  intro w hw
  refine Int.induction_on k ?_ ?_ ?_
  · simp
  · intro n ih
    have hmem : w + ((n : ℤ) : ℂ) * (2 * Real.pi * I) ∈ Hh TT := (Hh_add_int (n : ℤ)).2 hw
    have h1 := th_shift hTT hα hcurv hmem
    push_cast at ih h1 ⊢
    rw [show w + ((n : ℂ) + 1) * (2 * Real.pi * I) = w + (n : ℂ) * (2 * Real.pi * I) + 2 * Real.pi * I by ring,
      h1, ih]
    ring
  · intro n ih
    have hmem : w + ((-(n : ℤ) - 1 : ℤ) : ℂ) * (2 * Real.pi * I) ∈ Hh TT := (Hh_add_int _).2 hw
    have h1 := th_shift hTT hα hcurv hmem
    push_cast at ih h1 ⊢
    rw [show w + (-(n : ℂ) - 1) * (2 * Real.pi * I) + 2 * Real.pi * I = w + -(n : ℂ) * (2 * Real.pi * I) by ring,
      ih] at h1
    linarith

theorem expI_th_eq (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n)
    {w w' : ℂ} (hw : w ∈ Hh TT) (hw' : w' ∈ Hh TT) (he : Complex.exp w = Complex.exp w') :
    Complex.exp (I * (th TT α w : ℂ)) = Complex.exp (I * (th TT α w' : ℂ)) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  obtain ⟨m, hm⟩ := hhol
  have h := th_shift_int hTT hα hcurv n w' hw'
  rw [← hn, hm] at h
  apply Complex.exp_eq_exp_iff_exists_int.2
  refine ⟨n * m, ?_⟩
  rw [h]
  push_cast
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

