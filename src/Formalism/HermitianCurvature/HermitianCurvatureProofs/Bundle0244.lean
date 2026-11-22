import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0239
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0198
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AestronglyMeasurableGermIntegrand
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0238
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0166
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0192
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0203
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0235

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtRightDerivativeCurve
section
open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section RdV

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def cur (X : Q.Mx k ρ) (y : Mt k ρ) (t : ℝ) : Mt k ρ :=
  Matrix.of.symm (Matrix.of y * NormedSpace.exp ((t : ℂ) • X))

theorem cur_zero (X : Q.Mx k ρ) (y : Mt k ρ) : cur X y 0 = y := by
  simp [cur, NormedSpace.exp_zero]

theorem cur_add (X : Q.Mx k ρ) (y : Mt k ρ) (s t : ℝ) : cur X (cur X y s) t = cur X y (s + t) := by
  have hc : Commute ((s : ℂ) • X) ((t : ℂ) • X) := ((Commute.refl X).smul_left _).smul_right _
  have e : NormedSpace.exp (((s + t : ℝ) : ℂ) • X) =
      NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X) := by
    rw [← Matrix.exp_add_of_commute _ _ hc, Complex.ofReal_add, add_smul]
  unfold cur
  rw [Equiv.apply_symm_apply, e, Matrix.mul_assoc]

theorem cur_hasDerivAt0 (X : Q.Mx k ρ) (y : Mt k ρ) :
    HasDerivAt (cur X y) (Matrix.of.symm (Matrix.of y * X)) 0 :=
  Formalism.REAL.hasDerivAt_mul_exp_smul_zero (Matrix.of y) X

theorem cur_hasDerivAt (X : Q.Mx k ρ) (y : Mt k ρ) (s : ℝ) :
    HasDerivAt (cur X y) (Matrix.of.symm (Matrix.of (cur X y s) * X)) s := by
  have h0 := cur_hasDerivAt0 X (cur X y s)
  rw [← sub_self s] at h0
  have h1 := h0.comp_sub_const s s
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show cur X y t = cur X (cur X y s) (t - s)
  rw [cur_add, add_sub_cancel]

def mulX (X : Q.Mx k ρ) : Mt k ρ →ₗ[ℝ] Mt k ρ where
  toFun y := Matrix.of.symm (Matrix.of y * X)
  map_add' a b := by
    show Matrix.of.symm ((Matrix.of a + Matrix.of b) * X) = _
    rw [Matrix.add_mul]; rfl
  map_smul' c a := by
    show Matrix.of.symm ((c • Matrix.of a) * X) = _
    rw [Matrix.smul_mul]; rfl

variable {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par]

def dirL (X : Q.Mx k ρ) : Par × Mt k ρ →L[ℝ] Par × Mt k ρ :=
  (ContinuousLinearMap.inr ℝ Par (Mt k ρ)).comp
    ((LinearMap.toContinuousLinearMap (mulX X)).comp (ContinuousLinearMap.snd ℝ Par (Mt k ρ)))

theorem rdv_local {X : Q.Mx k ρ} (hX : Formalism.FourierDecayAlt.P.Qx3.LieLev (Fin.last ρ) X) {f : Par → Q.Mx k ρ → E}
    {U : Set (Par × Mt k ρ)} {F : Par × Mt k ρ → E} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ q ∈ U, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → f q.1 (Matrix.of q.2) = F q)
    {q : Par × Mt k ρ} (hq : q ∈ U) (hqG : Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ)) :
    HasDerivAt (fun t : ℝ => f q.1 (Matrix.of (cur X q.2 t))) (fderiv ℝ F q (dirL X q)) 0 := by
  have hc := cur_hasDerivAt0 X q.2
  have hγ : HasDerivAt (fun t : ℝ => ((q.1, cur X q.2 t) : Par × Mt k ρ)) (dirL X q) 0 :=
    (hasDerivAt_const (0 : ℝ) q.1).prodMk hc
  have hγ0 : ((q.1, cur X q.2 0) : Par × Mt k ρ) = q := by rw [cur_zero]
  have hFd : DifferentiableAt ℝ F q := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hq)
  have hcomp := hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  refine hcomp.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, ((q.1, cur X q.2 t) : Par × Mt k ρ) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hq)
  filter_upwards [hmem] with t ht
  exact hfF _ ht (Formalism.FourierDecayAlt.P.Qx3.glev_mul hqG (hX t))

theorem parFam_contAt_comp {Y : Type} [TopologicalSpace Y] {U₀ : Set (Par × Mt k ρ)} {g : Par × Mt k ρ → E}
    (hg : PBI.ParFam k ρ U₀ g) {m : Y → Par × Mt k ρ} {y₀ : Y} (hm : ContinuousAt m y₀) (hU : m y₀ ∈ U₀)
    (hG : ∀ y, Matrix.of (m y).2 ∈ Q.Glev k ρ (Fin.last ρ)) : ContinuousAt (fun y => g (m y)) y₀ := by
  obtain ⟨U, F, hUo, hqU, hF, hgF⟩ := hg (m y₀) hU (hG y₀)
  have hcF : ContinuousAt F (m y₀) := hF.continuousOn.continuousAt (hUo.mem_nhds hqU)
  have h := ContinuousAt.comp (g := F) (f := m) (x := y₀) hcF hm
  refine h.congr ?_
  have hmem : ∀ᶠ y in 𝓝 y₀, m y ∈ U := hm.preimage_mem_nhds (hUo.mem_nhds hqU)
  filter_upwards [hmem] with y hy
  exact (hgF (m y) hy (hG y)).symm

theorem rdv_parFam {X : Q.Mx k ρ} (hX : Formalism.FourierDecayAlt.P.Qx3.LieLev (Fin.last ρ) X) {U₀ : Set (Par × Mt k ρ)}
    {f : Par → Q.Mx k ρ → E} (hf : PBI.ParFam k ρ U₀ (fun q => f q.1 (Matrix.of q.2))) :
    PBI.ParFam k ρ U₀ (fun q => RdV X (f q.1) (Matrix.of q.2)) := by
  intro q₀ hq₀ hG₀
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq₀ hG₀
  refine ⟨U, fun q => fderiv ℝ F q (dirL X q), hU, hqU, ?_, fun q hq hqG => ?_⟩
  · exact (hF.fderiv_of_isOpen (m := ∞) hU Formalism.REAL.withTop_enat_infty_add_one_le_infty).clm_apply
      (ContinuousLinearMap.contDiff (n := ∞) (dirL (Par := Par) (k := k) (ρ := ρ) X)).contDiffOn
  · exact (rdv_local hX hU hF hfF hq hqG).deriv

theorem hasDerivAt_right_derivative_curve {X : Q.Mx k ρ} (hX : Formalism.FourierDecayAlt.P.Qx3.LieLev (Fin.last ρ) X) {U₀ : Set (Par × Mt k ρ)}
    {f : Par → Q.Mx k ρ → E} (hf : PBI.ParFam k ρ U₀ (fun q => f q.1 (Matrix.of q.2))) (Z : Par) (y : Mt k ρ)
    (s : ℝ) (hq : (Z, cur X y s) ∈ U₀) (hG : Matrix.of (cur X y s) ∈ Q.Glev k ρ (Fin.last ρ)) :
    HasDerivAt (fun t : ℝ => f Z (Matrix.of (cur X y t))) (RdV X (f Z) (Matrix.of (cur X y s))) s := by
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf _ hq hG
  have h0 := rdv_local hX hU hF hfF hqU hG
  have h1 : HasDerivAt (fun t : ℝ => f Z (Matrix.of (cur X (cur X y s) t)))
      (RdV X (f Z) (Matrix.of (cur X y s))) 0 := h0.differentiableAt.hasDerivAt
  rw [← sub_self s] at h1
  have h2 := h1.comp_sub_const s s
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show f Z (Matrix.of (cur X y t)) = f Z (Matrix.of (cur X (cur X y s) (t - s)))
  rw [cur_add, add_sub_cancel]

end RdV

theorem parOK_rdV {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {X : Q.Mx k ρ}
    (hX : Formalism.FourierDecayAlt.P.Qx3.LieLev (Fin.last ρ) X) : ParOK k ρ (E := E) (RdV X) := by
  intro Par _ _ _ _ _ U₀ hU₀ f hf
  have hD := rdv_parFam hX hf
  refine ⟨hD, fun q hq hG W hW hqW hz => ?_, fun ν _ Kp hKp hν fi y V hV hyV hyG hKV hi => ?_⟩
  · show deriv (fun t : ℝ => f q.1 (Matrix.of (cur X q.2 t))) 0 = 0
    have hγ : ContinuousAt (fun t : ℝ => ((q.1, cur X q.2 t) : Par × Mt k ρ)) 0 :=
      continuousAt_const.prodMk (cur_hasDerivAt0 X q.2).continuousAt
    have hγ0 : ((q.1, cur X q.2 0) : Par × Mt k ρ) = q := by rw [cur_zero]
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, ((q.1, cur X q.2 t) : Par × Mt k ρ) ∈ W :=
      hγ.preimage_mem_nhds (by rw [hγ0]; exact hW.mem_nhds hqW)
    have hev : (fun t : ℝ => f q.1 (Matrix.of (cur X q.2 t))) =ᶠ[𝓝 0] (fun _ => (0 : E)) := by
      filter_upwards [hmem] with t ht
      exact hz _ ht (Formalism.FourierDecayAlt.P.Qx3.glev_mul hG (hX t))
    rw [hev.deriv_eq, deriv_const]
  · have hGt : ∀ t : ℝ, Matrix.of (cur X y t) ∈ Q.Glev k ρ (Fin.last ρ) := fun t =>
      Formalism.FourierDecayAlt.P.Qx3.glev_mul hyG (hX t)
    have hpre : cur X y ⁻¹' V ∈ 𝓝 (0 : ℝ) :=
      (cur_hasDerivAt0 X y).continuousAt.preimage_mem_nhds (by rw [cur_zero]; exact hV.mem_nhds hyV)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
    have hδ : 0 < ε / 2 := half_pos hε
    have hcb : Metric.closedBall (0 : ℝ) (ε / 2) ⊆ cur X y ⁻¹' V := fun t ht =>
      hball (Metric.closedBall_subset_ball (half_lt_self hε) ht)
    have hUt : ∀ t ∈ Metric.closedBall (0 : ℝ) (ε / 2), ∀ Z ∈ Kp, (Z, cur X y t) ∈ U₀ :=
      fun t ht Z hZ => hKV ⟨hZ, hcb ht⟩
    have hcont : ContinuousOn (fun p : Par × ℝ => RdV X (f p.1) (Matrix.of (cur X y p.2)))
        (Kp ×ˢ Metric.closedBall (0 : ℝ) (ε / 2)) := by
      intro p hp
      have hm : ContinuousAt (fun p : Par × ℝ => ((p.1, cur X y p.2) : Par × Mt k ρ)) p :=
        continuous_fst.continuousAt.prodMk
          (ContinuousAt.comp (g := cur X y) (f := Prod.snd) (x := p) (cur_hasDerivAt X y p.2).continuousAt
            continuous_snd.continuousAt)
      exact (parFam_contAt_comp (g := fun q => RdV X (f q.1) (Matrix.of q.2)) hD hm (hUt p.2 hp.2 p.1 hp.1)
        (fun p => hGt p.2)).continuousWithinAt
    obtain ⟨C, hC⟩ := (hKp.prod (isCompact_closedBall (0 : ℝ) (ε / 2))).exists_bound_of_continuousOn hcont
    have hae : ∀ᵐ Z ∂ν, Z ∈ Kp := by
      rw [ae_iff]
      simpa [Set.compl_def] using hν
    have hb : Metric.ball (0 : ℝ) (ε / 2) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hδ
    have hin : ∀ t ∈ Metric.ball (0 : ℝ) (ε / 2), t ∈ Metric.closedBall (0 : ℝ) (ε / 2) :=
      fun t ht => Metric.ball_subset_closedBall ht
    have hF_int : ∀ t ∈ Metric.closedBall (0 : ℝ) (ε / 2),
        Integrable (fun Z => f Z (Matrix.of (cur X y t))) ν := fun t ht =>
      parFam_integrable (f := fun q => f q.1 (Matrix.of q.2)) hf hKp hν (hGt t) (fun Z hZ => hUt t ht Z hZ)
    have h0c : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) (ε / 2) := Metric.mem_closedBall_self hδ.le
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
      (F := fun t Z => f Z (Matrix.of (cur X y t)))
      (F' := fun t Z => RdV X (f Z) (Matrix.of (cur X y t))) (x₀ := 0) (bound := fun _ => C) hb
      (by
        filter_upwards [hb] with t ht
        exact (hF_int t (hin t ht)).aestronglyMeasurable)
      (hF_int 0 h0c)
      ((parFam_integrable (f := fun q => RdV X (f q.1) (Matrix.of q.2)) hD hKp hν (hGt 0)
        (fun Z hZ => hUt 0 h0c Z hZ)).aestronglyMeasurable)
      (by
        filter_upwards [hae] with Z hZ
        intro t ht
        exact hC (Z, t) ⟨hZ, hin t ht⟩)
      (integrable_const C)
      (by
        filter_upwards [hae] with Z hZ
        intro t ht
        exact hasDerivAt_right_derivative_curve hX hf Z y t (hUt t (hin t ht) Z hZ) (hGt t))
    show deriv (fun t : ℝ => fi (Matrix.of (cur X y t))) 0 = ∫ Z, RdV X (f Z) (Matrix.of y) ∂ν
    have hev : (fun t : ℝ => fi (Matrix.of (cur X y t))) =ᶠ[𝓝 0]
        (fun t => ∫ Z, f Z (Matrix.of (cur X y t)) ∂ν) := by
      filter_upwards [hb] with t ht
      exact hi (cur X y t) (hcb (hin t ht)) (hGt t)
    rw [hev.deriv_eq, key.2.deriv, cur_zero]

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section pt

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem rn_zero : U.Rn k p ρ 0 = 1 := by
  have h1 : U.skewOf (0 : (G.UT p → ℂ) × (Fin p → ℝ)) = 0 := by
    unfold U.skewOf; ext a b; simp [G.strictUpper]
  unfold U.Rn
  rw [← Formalism.FourierDecayAlt.P.Ux3.block3_one]
  simp only [Prod.fst_zero, Prod.snd_zero, h1]
  congr 1 <;> ext <;> simp

theorem upper_zero : G.upper (0 : G.UT p → ℂ) = 1 := by
  unfold G.upper G.strictUpper; ext a b; simp

theorem rcAct_one_zero : rcAct (1 : B.Mat k ρ) (0 : U.RC k p ρ) = 0 := by
  unfold rcAct; ext <;> simp

theorem sxL_mem (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) (x : XL k p ρ σ) :
    sxL Bj σ x ∈ Sset k (p + ρ) (liftVec k p ρ Bj.z) := by
  by_cases hx : GoodL Bj σ x
  · rw [sxL, if_pos hx]
    exact left_factor_mem k p ρ Bj.z (-x.2.1) (lhOf σ x.2.2.2) (Matrix.of x.1.1) (Matrix.of x.1.2) Bj.z_mem
      (lh_lower σ _) hx.1 hx.2
  · rw [sxL, if_neg hx]
    refine ⟨1, (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k (p + ρ) _).one_mem, 1,
      (Formalism.FourierDecayAlt.P.unipotent_radical_closed k (p + ρ)).one_mem, by simp⟩

theorem goodL_pt (Bj : B.RealPlaceData k ρ Wp Wq) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (g : B.Mat k ρ) (hg : g ∈ B.GV k ρ) (x : XL k p ρ σ) (hx : GoodL Bj σ x) :
    sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g ∈ B.GV k (p + ρ) ∧
      U.DjU k p ρ (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g) ≠ 0 := by
  set ξ0 : U.Xi k p 0 ρ σ := ((x.2.1, 0), (x.2.2.1, (x.2.2.2, 0))) with hξ0
  have uh : IsUnit (Matrix.of x.1.1 : B.Mat k ρ).det := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k ρ Bj.z).unit _ hx.1
  have uν : IsUnit (Matrix.of x.1.2 : B.Mat k ρ).det := (Formalism.FourierDecayAlt.P.unipotent_radical_closed k ρ).unit _ hx.2
  have hH1 : (1 : B.Mat k ρ)ᴴ * Hpk k ρ * 1 = Hpk k ρ := by simp
  have e := gamma_xi_split k p ρ σ d ξ0 (fun a => a.elim0) (Matrix.of x.1.1) (Matrix.of x.1.2) 1 1 g uh uν hH1
  simp only [hξ0, Formalism.FourierDecayAlt.P.PBM.embG_one, upper_zero, Formalism.FourierDecayAlt.P.PBM.muP_one, rcAct_one_zero, rn_zero,
    Matrix.mul_one] at e
  have hx' : sxL Bj σ x = U.Rn k p ρ (-x.2.1) * U.muP k p ρ (lhOf σ x.2.2.2)ᴴ⁻¹ *
      U.embG k p ρ ((Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹) := if_pos hx
  have cG := Formalism.FourierDecayAlt.P.unitary_group_closed k ρ
  have hγ : (Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹ * g ∈ B.GV k ρ :=
    cG.mul_mem _ (cG.mul_mem _ (cG.inv_mem _ hx.1.1) _ (cG.inv_mem _ hx.2.1)) _ hg
  rw [hx', ← e]
  have hZ : G.detM (fun a : Fin 0 => a.elim0 : G.Mat 0) ≠ 0 := by rw [detM_zero]; exact one_ne_zero
  refine ⟨Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation σ d hd ξ0 _ hZ hγ, ?_⟩
  intro h0
  have h1 := Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice σ d ξ0 (fun a : Fin 0 => a.elim0)
    ((Matrix.of x.1.1 : B.Mat k ρ)⁻¹ * (Matrix.of x.1.2 : B.Mat k ρ)⁻¹ * g)
  rw [detM_zero, mul_one] at h1
  exact Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne σ d hd (h1.symm.trans h0)

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem core_lf (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq) (hz' : B0.z' = liftVec k p ρ Bj.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl)) (hNj : Bj.μN = D.muN k ρ)
    (hN0 : B0.μN = D.muN k (p + ρ))
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k (p + ρ), H x ≠ 0 → B.gN x ≤ R) :
    Integrable (fun x => ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g))) (muL Bj σ) ∧
    B.JF Bj (U.PhiFun (s := 0) k ρ σ d (liftVec k p ρ Bj.z) (liftVec k p ρ Bj.z') H (fun a => a.elim0)) g =
      ∫ x, ellL Bj σ x (PBG.Kr B0 H (sxL Bj σ x * U.mMap k p ρ (U.hMat σ d) g)) ∂(muL Bj σ) :=
  core_main gamma_xi_split psi_right_equivariant psi_right_action_comm psi_measure_preserving right_measure_preserving hp σ d hd Bj B0 hz' hπ' hW'
    hW0' hNj hN0 g hg H hHc R hR (fl_aesm Bj σ d hd H hHc g hg.1)
    (aestronglyMeasurable_germ_integrand gamma_xi_split Bj B0 hz' hπ' σ d hd H hHc g hg.1)
    (fun x hx => Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra.krI_aesm B0 H hHc _ (goodL_pt Bj σ d hd g hg.1 x hx).1
      (goodL_pt Bj σ d hd g hg.1 x hx).2)
    (fun γ hγ => slice_int_cont σ d hd H hHc _ _ γ hγ)

end pt

theorem left_fubini_reduced_form : CoreLF := by
  intro k p m n e hp σ d hd Wp Wq _ _ _ _ _ _ Bj B0 hz hz' hπ' hW' hW0' hNj hN0
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl] at hz hz'
  refine ⟨XL k p m σ, inferInstance, muL Bj σ, ellL Bj σ, sxL Bj σ, fun x => hz ▸ sxL_mem Bj σ x, ?_⟩
  intro g hg H hHc hRb
  obtain ⟨R, hR⟩ := hRb
  have hπ'' : ∀ y : B.Mat k m, Bj.π' y = B0.π' (U.embG k p m y) := fun y => by
    rw [hπ' y, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
  have hset : {x | x ∈ B.GV k (p + m) ∧ Dmin k (p + m) B0.z B0.z' x ⟨p, by omega⟩ ≠ 0} =
      {x | x ∈ B.GV k (p + m) ∧ U.DjU k p m x ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [Formalism.FourierDecayAlt.P.hat_z_minimum_degree k p m B0.z B0.z' x]
  have hHc' : ContinuousOn H {x | x ∈ B.GV k (p + m) ∧ U.DjU k p m x ≠ 0} := hset ▸ hHc
  have h := core_lf hp σ d hd Bj B0 hz'.symm hπ'' hW' hW0' hNj hN0 g hg H hHc' R hR
  have hF : D.castF (rfl : p + m = p + m) H = H := funext fun y => by
    simp only [D.castF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  have hV : ∀ v : Fin (2 * (p + m) + k + 1) → ℂ, D.castV (rfl : p + m = p + m).symm v = v :=
    fun v => Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl v
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, hF, hV, ← hz, ← hz']
  exact h

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas

namespace Formalism.FourierDecayAlt.P

theorem left_fubini_normalized_tower : LeftFubiniLemmas.LeftFubini := LeftFubiniReduction.leftFubini_of_core LeftFubiniLemmas.left_fubini_reduced_form

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftLocalBuiltPlaces
section
namespace Formalism.FourierDecayAlt.P.LiftDegreeLemmas

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section consts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def lamLift (S : C.HidaSetting E Wp Wq) (b s : ℕ) (v : Fin S.f) : ℝ :=
  (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r b s)) * Real.exp 1 * (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) *
    J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v)

theorem g_cast' (S : C.HidaSetting E Wp Wq) : ((S.g : ℕ) : ℝ) = S.G.g := by
  unfold C.HidaSetting.g Sz.Glob.g; push_cast; rfl

theorem len_eq' (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : S.cutHi v - S.cutLo v = S.G.lenI := by
  simp only [C.HidaSetting.cutHi, C.HidaSetting.cutLo, Sz.Glob.lenI, Sz.Glob.place]; ring

theorem norm_lamB' (S : C.HidaSetting E Wp Wq) (hg : 0 < S.G.g) (b s : ℕ) :
    ‖lamB S b s‖ = (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r b s)) := by
  have hg' : (0 : ℝ) < (S.g : ℝ) := by rw [g_cast']; exact hg
  rw [norm_lamB S hg' b s, g_cast', zpow_neg, ← inv_zpow, inv_div]

variable {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem lenI_pos' (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) : 0 < S.G.lenI := by
  have hGo := hB.2.2.2.2.2.2.2.2.2.2.1
  have h := (hGo v).1
  rw [len_eq'] at h
  have : (0 : ℝ) < 6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop := by have := PBD.ntop_ge S; positivity
  linarith

theorem lamLift_nonneg (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (b s : ℕ) (v : Fin S.f) : 0 ≤ lamLift S b s v := by
  obtain ⟨hg, hk⟩ := glob_pos' hB
  have hl := lenI_pos' hB v
  have hN : (0 : ℝ) ≤ S.G.N := by unfold Sz.Glob.N; positivity
  have hA := supA_nonneg S hg hk v false
  unfold lamLift
  have : 0 < 2 * Real.pi / S.G.g := by positivity
  positivity

theorem thr_lift (hCc : 28 * Real.exp 1 ≤ Cc) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (b s : ℕ) (hb : 1 ≤ b)
    (hs : 1 ≤ s) (hbs : b + s ≤ S.G.r + 1) (v : Fin S.f) :
    0 ≤ lamLift S b s v ∧ lamLift S b s v ≤ S.base.szL b s v := by
  obtain ⟨hg, hk⟩ := glob_pos' hB
  have hl := lenI_pos' hB v
  have hCA : Cc ≤ S.CA := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hN : (0:ℝ) ≤ S.G.N := by unfold Sz.Glob.N; positivity
  have hcg : (0:ℝ) ≤ (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) := by positivity
  have h := (Formalism.FourierDecayAlt.P.frame_threshold_bound_holds (InfinitePlace E) S.G S.CA S.de S.de' S.T S.T' S.l (S.pl v) hg hl
    (hCc.trans hCA) (fun one => supA_nonneg S hg hk v one)).1 b s (Real.exp 1)
    ((28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s)) hb (Real.exp_pos 1).le le_rfl hcg le_rfl
  have hdec : decide (b = 1 ∧ s + 1 = 1) = false := decide_eq_false (by omega)
  rw [hdec] at h
  refine ⟨lamLift_nonneg hB b s v, ?_⟩
  show lamLift S b s v ≤ (if b + s ≤ S.G.r + 1 then _ else _)
  rw [if_pos hbs]
  unfold lamLift
  exact h

theorem lift_K (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (b s j K : ℕ) (hjb : b + s = j + 1)
    (grid : Fin K → Fin (2 * (j - s) + s + 1) → ℝ)
    (hl1 : ∀ c, ∑ i, |F7.lagCo (grid c) i| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ (2 * (j - s) + s)) :
    (∏ c, ∑ i, |F7.lagCo (grid c) i|) * ‖lamB S b s‖ ^ K *
      (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v)) ^ K ≤ (lamLift S b s v) ^ K := by
  obtain ⟨hg, hk⟩ := glob_pos' hB
  have hl := lenI_pos' hB v
  rw [norm_lamB' S hg b s]
  have hexp : 2 * (j - s) + s = 2 * (b - 1) + s := by omega
  have hl1' : ∀ c, ∑ i, |F7.lagCo (grid c) i| ≤ (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) := fun c =>
    (hl1 c).trans_eq (by rw [hexp, ntop_eq_N', len_eq'])
  unfold lamLift
  set cg := (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) with hcg
  set Tf := (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r b s)) with hTf
  set A := J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) with hA
  have hA0 : 0 ≤ A := supA_nonneg S hg hk v _
  have hgg : 0 < 2 * Real.pi / S.G.g := by positivity
  have hTf0 : 0 ≤ Tf := by positivity
  have hprod : (∏ c, ∑ i, |F7.lagCo (grid c) i|) ≤ cg ^ K := by
    calc (∏ c, ∑ i, |F7.lagCo (grid c) i|) ≤ ∏ _c : Fin K, cg :=
          Finset.prod_le_prod (fun c _ => Finset.sum_nonneg fun i _ => abs_nonneg _) fun c _ => hl1' c
      _ = cg ^ K := by simp
  have h1 : 0 ≤ Tf ^ K * (Real.exp 1 * A) ^ K := by positivity
  calc (∏ c, ∑ i, |F7.lagCo (grid c) i|) * Tf ^ K * (Real.exp 1 * A) ^ K
      = (∏ c, ∑ i, |F7.lagCo (grid c) i|) * (Tf ^ K * (Real.exp 1 * A) ^ K) := by ring
    _ ≤ cg ^ K * (Tf ^ K * (Real.exp 1 * A) ^ K) := mul_le_mul_of_nonneg_right hprod h1
    _ = (Tf * Real.exp 1 * cg * A) ^ K := by ring

theorem norm_u (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < S.g) (b s K : ℕ) :
    ‖((((‖lamB S b s‖ : ℝ) : ℂ) * (-1) ^ (s - 1) * (lamB S b s)⁻¹) ^ K)‖ = 1 := by
  rw [norm_pow, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), norm_pow,
    norm_neg, norm_one, one_pow, mul_one, mul_inv_cancel₀ (norm_ne_zero_iff.2 (lamB_ne S hg b s)), one_pow]

end consts

def LiftLocB : Prop :=
  P5.ThmPActual → KB.SizeStd → KB.DegLift → FormPos →
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    28 * Real.exp 1 ≤ Cc → KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∃ Λ : ℕ → ℕ → Fin S.f → ℝ,
      (∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v ∧ Λ b s v ≤ S.base.szL b s v) ∧
      ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.LiftLoc (setC S p F) v fun b s => Λ b s v

end

end Formalism.FourierDecayAlt.P.LiftDegreeLemmas
end

