import Formalism.LocalToGlobal.IndefiniteReal.GvPairOfOrbitDerivCont
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0011
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0010
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0008
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0086
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0006

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ApproxId
section
noncomputable section

open MeasureTheory Matrix Metric Topology
open scoped ContDiff

namespace Formalism.IndefR.Eqv.KerDiag

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def qdist (m : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, ((m i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j).re ^ 2 + (m i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j).im ^ 2)

theorem contDiff_entry (i j : Fin n) : ContDiff ℝ ∞ (fun m : Matrix (Fin n) (Fin n) ℂ => m i j) := by
  fun_prop

theorem contDiff_qdist : ContDiff ℝ ∞ (qdist (n := n)) := by
  unfold qdist
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  have he : ContDiff ℝ ∞ (fun m : Matrix (Fin n) (Fin n) ℂ => m i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j) :=
    (contDiff_entry i j).sub contDiff_const
  exact ((Complex.reCLM.contDiff.comp he).pow 2).add ((Complex.imCLM.contDiff.comp he).pow 2)

theorem entry_sq_le_qdist (m : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖m i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 ≤ qdist m := by
  have e : ‖m i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 =
      (m i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j).re ^ 2 + (m i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [e]
  unfold qdist
  calc _ ≤ ∑ j', ((m i j' - (1 : Matrix (Fin n) (Fin n) ℂ) i j').re ^ 2 +
        (m i j' - (1 : Matrix (Fin n) (Fin n) ℂ) i j').im ^ 2) :=
        Finset.single_le_sum (f := fun j' => (m i j' - (1 : Matrix (Fin n) (Fin n) ℂ) i j').re ^ 2 +
          (m i j' - (1 : Matrix (Fin n) (Fin n) ℂ) i j').im ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j', ((m i' j' - (1 : Matrix (Fin n) (Fin n) ℂ) i' j').re ^ 2 +
          (m i' j' - (1 : Matrix (Fin n) (Fin n) ℂ) i' j').im ^ 2)) (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
          (Finset.mem_univ i)

theorem qdist_one : qdist (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by simp [qdist]

def bumpQ (r : ℝ) (m : Matrix (Fin n) (Fin n) ℂ) : ℝ := Real.smoothTransition (1 - qdist m / r ^ 2)

theorem bumpQ_contDiff (r : ℝ) : ContDiff ℝ ∞ (bumpQ (n := n) r) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_qdist.div_const _))

theorem bumpQ_nonneg (r : ℝ) (m : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ bumpQ r m := Real.smoothTransition.nonneg _

theorem bumpQ_pos_one {r : ℝ} : 0 < bumpQ (n := n) r 1 := by
  unfold bumpQ
  apply Real.smoothTransition.pos_of_pos
  rw [qdist_one]
  simp

theorem bumpQ_eq_zero {r : ℝ} (hr : 0 < r) {m : Matrix (Fin n) (Fin n) ℂ} (hm : r ≤ ‖m - 1‖) : bumpQ r m = 0 := by
  unfold bumpQ
  apply Real.smoothTransition.zero_of_nonpos
  have : r ^ 2 ≤ qdist m := by

    by_contra hlt
    push Not at hlt
    have hall : ∀ i j, ‖(m - 1) i j‖ < r := fun i j => by
      have h := entry_sq_le_qdist m i j
      rw [Matrix.sub_apply]
      nlinarith [norm_nonneg (m i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j)]
    exact absurd (Matrix.norm_lt_iff hr |>.2 hall) (not_lt.2 hm)
  rw [sub_nonpos, le_div_iff₀ (by positivity)]
  linarith

theorem bumpQ_support {r : ℝ} (hr : 0 < r) {m : Matrix (Fin n) (Fin n) ℂ} (hm : bumpQ r m ≠ 0) : ‖m - 1‖ < r := by
  by_contra h
  push_neg at h
  exact hm (bumpQ_eq_zero hr h)

theorem bumpQ_compact {r : ℝ} (hr : 0 < r) : HasCompactSupport (bumpQ (n := n) r) := by
  refine HasCompactSupport.intro (isCompact_closedBall (1 : Matrix (Fin n) (Fin n) ℂ) r) fun m hm => ?_
  rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hm
  exact bumpQ_eq_zero hr hm.le

theorem approx_id (ε : Fin n → Bool) (f : PI.UpqRep.UJ ε → ℂ) (hf : Continuous f) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Φ : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧
      ‖(∫ h, Φ (PI.UpqRep.umat h) * f h ∂(PI.UpqRep.muG ε)) - f 1‖ ≤ δ := by
  have hemb : Topology.IsClosedEmbedding (PI.UpqRep.umat (ε := ε)) := (PI.UpqRep.isClosedEmbeddingMatrix n ε).1
  have hcont1 : ∀ᶠ h in 𝓝 (1 : PI.UpqRep.UJ ε), ‖f h - f 1‖ < δ := by
    have hev := (hf.tendsto 1).eventually (Metric.ball_mem_nhds (f 1) hδ)
    filter_upwards [hev] with h hh
    rwa [dist_eq_norm] at hh
  rw [hemb.isInducing.nhds_eq_comap, Filter.eventually_comap] at hcont1
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hcont1
  have hu1 : PI.UpqRep.umat (1 : PI.UpqRep.UJ ε) = 1 := rfl
  set b : PI.UpqRep.UJ ε → ℝ := fun h => bumpQ r (PI.UpqRep.umat h) with hb_def
  have hb_cont : Continuous b := (bumpQ_contDiff r).continuous.comp hemb.continuous
  have hb_cs : HasCompactSupport b := (bumpQ_compact hr).comp_isClosedEmbedding hemb
  have hb_nn : 0 ≤ b := fun h => bumpQ_nonneg r _
  have hb1 : b 1 ≠ 0 := by
    show bumpQ r (PI.UpqRep.umat (1 : PI.UpqRep.UJ ε)) ≠ 0
    rw [hu1]
    exact bumpQ_pos_one.ne'
  have hI : 0 < ∫ h, b h ∂(PI.UpqRep.muG ε) :=
    hb_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero hb_cs hb_nn hb1
  set I := ∫ h, b h ∂(PI.UpqRep.muG ε) with hI_def
  have hint_b : Integrable b (PI.UpqRep.muG ε) := hb_cont.integrable_of_hasCompactSupport hb_cs
  refine ⟨fun m => ((bumpQ r m / I : ℝ) : ℂ), ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((bumpQ_contDiff r).div_const I)
  · exact (bumpQ_compact hr).comp_left (g := fun x : ℝ => ((x / I : ℝ) : ℂ)) (by simp)
  · show ‖(∫ h, ((b h / I : ℝ) : ℂ) * f h ∂(PI.UpqRep.muG ε)) - f 1‖ ≤ δ
    have hsum1 : ∫ h, ((b h / I : ℝ) : ℂ) ∂(PI.UpqRep.muG ε) = 1 := by
      rw [integral_complex_ofReal, integral_div, div_self hI.ne']
      simp
    have hi1 : Integrable (fun h => ((b h / I : ℝ) : ℂ) * f h) (PI.UpqRep.muG ε) := by
      apply Continuous.integrable_of_hasCompactSupport
      · exact (Complex.continuous_ofReal.comp (hb_cont.div_const I)).mul hf
      · exact (hb_cs.comp_left (g := fun x : ℝ => ((x / I : ℝ) : ℂ)) (by simp)).mul_right
    have hi2 : Integrable (fun h => ((b h / I : ℝ) : ℂ) * f 1) (PI.UpqRep.muG ε) :=
      (hint_b.div_const I).ofReal.mul_const _
    have key : (∫ h, ((b h / I : ℝ) : ℂ) * f h ∂(PI.UpqRep.muG ε)) - f 1
        = ∫ h, ((b h / I : ℝ) : ℂ) * (f h - f 1) ∂(PI.UpqRep.muG ε) := by
      simp_rw [mul_sub]
      rw [integral_sub hi1 hi2, integral_mul_const, hsum1, one_mul]
    rw [key]
    calc ‖∫ h, ((b h / I : ℝ) : ℂ) * (f h - f 1) ∂(PI.UpqRep.muG ε)‖
        ≤ ∫ h, (b h / I) * δ ∂(PI.UpqRep.muG ε) := by
          apply norm_integral_le_of_norm_le ((hint_b.div_const I).mul_const δ)
          refine Filter.Eventually.of_forall fun h => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hb_nn h) hI.le)]
          by_cases hz : b h = 0
          · simp [hz]
          · apply mul_le_mul_of_nonneg_left _ (div_nonneg (hb_nn h) hI.le)
            have hlt := bumpQ_support hr hz
            refine (hball _ ?_ h rfl).le
            rw [Metric.mem_ball, dist_eq_norm, hu1]
            exact hlt
      _ = δ := by rw [integral_mul_const, integral_div, div_self hI.ne', one_mul]

end Formalism.IndefR.Eqv.KerDiag

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.EFinSmulEqOfFinPart
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

theorem actO_smul (c : AF D.host.F) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (c • x) = c • actO S T g h x := by
  unfold actO
  simp [Matrix.mul_smul, Matrix.smul_mul]

theorem actO_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  simp [Matrix.mul_add, Matrix.add_mul, smul_add]

theorem actO_inv (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  unfold actO
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (L2.Theta.mt T h)]
  unfold L2.Theta.mt
  simp

theorem actO_inv' (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  simpa using actO_inv g⁻¹ h⁻¹ x

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqTie
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lift

variable {D : D7} (V : HSp D)

theorem thetaC_inj {y y' : Ainf D.host.F ⊗[D.host.F] D.host.E} (h : ∀ τ, thetaC D τ y = thetaC D τ y') : y = y' :=
  (splitEquiv D).injective (funext h)

theorem infHom_infOnly (h : GA D V) : infHom V (infOnly D V h) = infHom V h := by
  apply Units.ext
  funext i j
  show infPart D (matA D V (infOnly D V h) i j) = infPart D (matA D V h i j)
  apply thetaC_inj
  intro τ
  have e := congrFun (congrFun (infMat_infOnly D V h τ) i) j
  rw [infMat_thetaC, infMat_thetaC] at e
  exact e

theorem exists_finLift (q : Bridge.Gf V) : ∃ κ ∈ GfC V, finHom V κ = q := by
  obtain ⟨κ0, hκ0⟩ := q.2
  refine ⟨(infOnly D V κ0)⁻¹ * κ0, ?_, ?_⟩
  · show infHom V ((infOnly D V κ0)⁻¹ * κ0) = 1
    rw [map_mul, map_inv, infHom_infOnly, inv_mul_cancel]
  · have h1 : finHom V (infOnly D V κ0) = 1 := infOnly_mem_GinfC D V κ0
    rw [map_mul, map_inv, h1, inv_one, one_mul, hκ0]

end Lift

section Ad

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* G)

theorem mem_adForms_iff (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (F : G → W) :
    F ∈ Bridge.AdForms ι ρ J χ ↔ ∀ (γ : Γ) (h : G) (k : J), F (ι γ * h * k) = (χ k : ℂ) • ρ γ (F h) := Iff.rfl

end Ad

section Coef

variable {D : D7} {V : HSp D} (c : CoefA V)

theorem coefExt_mul (hc : c.Is) (f : Bridge.Gf V → c.W) (h κ : GA D V) (hκ : κ ∈ GfC V) :
    c.ext f (h * κ) = c.ρ h⁻¹ (f ((finHom V).rangeRestrict h * (finHom V).rangeRestrict κ)) := by
  have e1 : (finHom V).rangeRestrict (h * κ) = (finHom V).rangeRestrict h * (finHom V).rangeRestrict κ := map_mul _ _ _
  have e2 : c.ρ (h * κ)⁻¹ = c.ρ h⁻¹ := by
    rw [_root_.mul_inv_rev, map_mul, hc.1 _ (Subgroup.inv_mem _ hκ), one_mul]
  exact congrArg₂ (fun (L : Module.End ℂ c.W) z => L (f z)) e2 e1

theorem toMap_g0Act (hc : c.Is) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm] (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ)
    {Q : Subgroup (Bridge.Gf V)} (ch : Q →* ℂˣ) (q : Q) (κ : GA D V) (hκ : κ ∈ GfC V)
    (hκq : (finHom V).rangeRestrict κ = q) (F : Bridge.Gf V → c.W) (v : Dm) (h : GA D V) :
    c.toMap pr (Bridge.g0Act ch q F) v h = ((ch q : ℂˣ) : ℂ)⁻¹ * c.toMap pr F v (h * κ) := by
  have e : c.toMap pr (Bridge.g0Act ch q F) v h =
      pr (c.ρ h⁻¹ ((((ch q)⁻¹ : ℂˣ) : ℂ) • F ((finHom V).rangeRestrict h * q))) v := rfl
  have e2 : c.ρ h⁻¹ ((((ch q)⁻¹ : ℂˣ) : ℂ) • F ((finHom V).rangeRestrict h * q)) =
      (((ch q)⁻¹ : ℂˣ) : ℂ) • c.ρ h⁻¹ (F ((finHom V).rangeRestrict h * q)) := LinearMap.map_smul _ _ _
  have e3 : pr ((((ch q)⁻¹ : ℂˣ) : ℂ) • c.ρ h⁻¹ (F ((finHom V).rangeRestrict h * q))) =
      (((ch q)⁻¹ : ℂˣ) : ℂ) • pr (c.ρ h⁻¹ (F ((finHom V).rangeRestrict h * q))) := LinearMap.map_smul _ _ _
  have e4 : (((ch q)⁻¹ : ℂˣ) : ℂ) = ((ch q : ℂˣ) : ℂ)⁻¹ := Units.val_inv_eq_inv_val (ch q)
  have e5 := coefExt_mul c hc F h κ hκ
  have e6 : c.ext F (h * κ) = c.ρ h⁻¹ (F ((finHom V).rangeRestrict h * q)) := hκq ▸ e5
  have s1 : pr (c.ρ h⁻¹ ((((ch q)⁻¹ : ℂˣ) : ℂ) • F ((finHom V).rangeRestrict h * q))) v =
      (((ch q)⁻¹ : ℂˣ) : ℂ) * pr (c.ρ h⁻¹ (F ((finHom V).rangeRestrict h * q))) v :=
    (congrArg (fun L : Dm →ₗ[ℂ] ℂ => L v) ((congrArg pr e2).trans e3)).trans (LinearMap.smul_apply _ _ _)
  have s2 : (((ch q)⁻¹ : ℂˣ) : ℂ) * pr (c.ρ h⁻¹ (F ((finHom V).rangeRestrict h * q))) v =
      ((ch q : ℂˣ) : ℂ)⁻¹ * c.toMap pr F v (h * κ) :=
    congrArg₂ (· * ·) e4 (congrArg (fun w => pr w v) e6.symm)
  exact e.trans (s1.trans s2)

end Coef

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem lift_X (hred : R.grp_red_R) (t : T) (g : G) : ∃ κ, IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ := by
  obtain ⟨q1, hq1⟩ := (R.B.R t).act_tie.red_surj g
  obtain ⟨κ1, hκ1f, hκ1q⟩ := exists_finLift D.sp.X' (q1 : Bridge.Gf D.sp.X')
  have hq : finE D.sp.X' κ1 ∈ lev D.sp.cm D.sp.X'.gram R.βX (flagL (R.datXt t)) := by
    rw [finE_eq, hκ1q]; exact q1.2
  refine ⟨κ1, hκ1f, hq.1, ?_⟩
  rw [finE_eq, hκ1q, ← hred t q1, hq1]

theorem mem_Q_of_lift (t : T) (g : G) {κ0 : GA D D.sp.X'} (hκ0 : IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ0) :
    (finHom D.sp.X').rangeRestrict κ0 ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q := by
  show Formalism.UG.bc (swapAE D) (finHom D.sp.X' κ0) ∈ lev D.sp.cm D.sp.X'.gram R.βX (flagL (R.datXt t))
  rw [← finE_eq]
  exact ⟨hκ0.2.1, Subgroup.mem_top _⟩

theorem red_of_lift (hred : R.grp_red_R) (t : T) (g : G) {κ0 : GA D D.sp.X'}
    (hκ0 : IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ0) :
    (R.B.R t).act_tie.red (⟨_, mem_Q_of_lift R t g hκ0⟩ : (levEnv D.sp.X' R.βX (R.datXt t)).Q) = g := by
  apply R.eG.injective
  rw [hred t ⟨_, mem_Q_of_lift R t g hκ0⟩]
  exact hκ0.2.2

theorem actX_apply (t : T) (g : G) (hex : ∃ κ, IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ) (F : GA D D.sp.X' → ℂ)
    (h : GA D D.sp.X') :
    actX R t g F h = (levChi D.sp.X' R.βX (flagL (R.datXt t)) hex.choose)⁻¹ * F (h * hex.choose) := by
  show actG0 D.sp.X' R.βX (R.datXt t) (R.eG g) F h = _
  unfold actG0
  rw [dif_pos hex]

theorem jX_act (hM : R.IsModels) (t : T) (g : G) (x : A.fam.amb.FR t) (q0 : (levEnv D.sp.X' R.βX (R.datXt t)).Q)
    (hred0 : (R.B.R t).act_tie.red q0 = g) :
    (R.HX t).e (R.jX t (A.fam.amb.opR t (Sum.inr g) x)) =
      Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch q0 ((R.HX t).e (R.jX t x)) := by
  have hext := (R.B.R t).act_tie.act_eq g q0 hred0 x
  exact (hM.jX t _).trans (hext.trans (congrArg (Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch q0) (hM.jX t x).symm))

theorem actTieXOf_holds : ActTieXOf R := by
  intro hM hred t g x
  have hex := lift_X R hred t g
  have hκ0 := hex.choose_spec
  have hmem := mem_Q_of_lift R t g hκ0
  have hred0 := red_of_lift R hred t g hκ0
  have hch : (((levEnv D.sp.X' R.βX (R.datXt t)).ch ⟨_, hmem⟩ : ℂˣ) : ℂ) =
      levChi D.sp.X' R.βX (flagL (R.datXt t)) hex.choose := rfl
  refine LinearMap.ext fun v => funext fun h => ?_
  have e1 := congrArg (fun F : Bridge.Gf D.sp.X' → R.cX.W => R.cX.toMap R.prX F v h) (jX_act R hM t g x _ hred0)
  have e2 := toMap_g0Act R.cX hM.cX R.prX (levEnv D.sp.X' R.βX (R.datXt t)).ch ⟨_, hmem⟩ hex.choose hκ0.1 rfl
    ((R.HX t).e (R.jX t x)) v h
  have e3 := actX_apply R t g hex (fX R t (R.jX t x) v) h
  exact e1.trans (e2.trans ((congrArg (fun c : ℂ => c⁻¹ * R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) v (h * hex.choose))
    hch).trans e3.symm))

end Formalism.IndefR.Eqv.Act

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.VanishTranslates
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.KerDiag

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Gen

variable {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)

def KfLow (τ : D.what₂.Tau) : Submodule ℂ (M.sm τ) :=
  Submodule.span ℂ {w | ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∃ w0 : lowT M τ,
    (w : M.H τ) = M.rep τ g ((w0 : M.sm τ) : M.H τ)}

open Classical in

theorem mult_equiv {T : MMap M} (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (v : M.Vec) (w : M.sm τ) (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact hT.equiv τ g hg v w hw
  | zero => rfl
  | add T T' _ _ h1 h2 =>
    simp only [_root_.add_apply, h1, h2]
    rfl
  | smul c T _ h =>
    simp only [_root_.smul_apply, h]
    rfl

open Classical in

theorem vanish_KfLow {T : MMap M} (hT : T ∈ Mult θ M J χ)
    (hlow : ∀ v : ∀ ρ, lowT M ρ, T (fun ρ => v ρ) = 0) :
    ∀ (s : Finset D.what₂.Tau) (v : M.Vec), (∀ τ ∈ s, v τ ∈ KfLow M τ) →
      (∀ τ ∉ s, ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∃ w0 : lowT M τ,
        (v τ : M.H τ) = M.rep τ g ((w0 : M.sm τ) : M.H τ)) → T v = 0 :=
  by apply _root_.UpperTheory.Reformulated.B.LowTypeThetaMapVanishing.vanish_KfLow <;> assumption

end Gen

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def DensLow : Prop :=
  ∀ i τ (ℓ : (R.MW i (sg0 D A)).H τ →ₗ[ℂ] ℂ),
    Sobolev₂ (lieAt (Wc D i) τ) ((R.MW i (sg0 D A)).rep τ) ℓ →
      (∀ w ∈ KfLow (R.MW i (sg0 D A)) τ, ℓ (w : (R.MW i (sg0 D A)).H τ) = 0) →
        ∀ w : (R.MW i (sg0 D A)).sm τ, ℓ (w : (R.MW i (sg0 D A)).H τ) = 0

open Classical in
theorem spanP_of (h : DensLow R) : Formalism.IndefR.Eqv.Act.SpanP R := by
  intro i F hS hlow
  let M := R.MW i (sg0 D A)
  let Kf : ∀ τ, Submodule ℂ (M.sm τ) := fun τ => KfLow M τ
  let Tm : ℂ →ₗ[ℂ] (⨂[ℂ] τ, Kf τ) →ₗ[ℂ] (⨂[ℂ] τ, M.sm τ) :=
    LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (PiTensorProduct.map fun τ => (Kf τ).subtype)
  have hS' : F ∈ Mult R.θ M (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) := hS
  have hu : PiTensorProduct.lift F ∈ MultT R.θ M (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) := by
    rw [mem_multT, LinearEquiv.symm_apply_apply]; exact hS'
  have hvan0 : ∀ v : ∀ τ, Kf τ, F (fun τ => (v τ : M.sm τ)) = 0 := fun v =>
    vanish_KfLow R.θ M _ _ hS' hlow Finset.univ _ (fun τ _ => (v τ).2) (fun τ h => absurd (Finset.mem_univ τ) h)
  have hvan : ∀ (φ : ℂ) (w : ⨂[ℂ] τ, Kf τ), PiTensorProduct.lift F (Tm φ w) = 0 := by
    intro φ w
    simp only [Tm, LinearMap.smulRight_apply, LinearMap.id_apply, LinearMap.smul_apply, map_smul]
    rw [smul_eq_zero]
    right
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, PiTensorProduct.map_tprod, map_smul, PiTensorProduct.lift.tprod]
      simp only [Submodule.subtype_apply]
      rw [hvan0 v, smul_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  have hspan : ∀ v : ∀ τ, M.sm τ, (∀ τ, v τ ∈ Kf τ) →
      PiTensorProduct.tprod ℂ v ∈ Submodule.span ℂ {x | ∃ φ w, Tm φ w = x} := by
    intro v hv
    refine Submodule.subset_span ⟨1, PiTensorProduct.tprod ℂ (fun τ => (⟨v τ, hv τ⟩ : Kf τ)), ?_⟩
    simp only [Tm, LinearMap.smulRight_apply, LinearMap.id_apply, LinearMap.smul_apply, one_smul,
      PiTensorProduct.map_tprod]
    rfl
  have h0 := Formalism.IndefR.Eqv.ioUniqueAt_holds D _ _ M R.θ _ _ Kf ℂ (⨂[ℂ] τ, Kf τ) Tm (fun τ ℓ hℓ hK => h i τ ℓ hℓ hK)
    hspan _ hu hvan
  have : F = PiTensorProduct.lift.symm (PiTensorProduct.lift F) := by simp
  rw [this, h0, map_zero]

end Formalism.IndefR.Eqv.KerDiag

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.VecDiagYOf
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.KerDiag

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

open Classical in

structure SideY (t : T) (k : ℕ) : Prop where
  hST : (Yc D k).rank ≤ (Yc D (k + 1)).rank
  step : R.datYt t (k + 1) R.triv = Formalism.IndefR.Fin.stepLev (R.datYt t k R.triv) (R.chi (k + 1)) (Yc D (k + 1)).rank hST
  dat : ∃ (BS : D.what₂.Tau → Matrix (Fin (Yc D k).rank) (Fin (Yc D k).rank) ℂ)
    (BT : D.what₂.Tau → Matrix (Fin (Yc D (k + 1)).rank) (Fin (Yc D (k + 1)).rank) ℂ) (pS pT : D.what₂.Tau → ℕ),
    IsDatumStep R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) BS BT pS pT (R.ΛY k)
      (R.ΛY (k + 1)) (R.βY k) (R.βY (k + 1)) (R.datYt t k R.triv) (R.chi (k + 1)) (R.Q t) (R.xiR t) (R.vac k) (R.vY t k)
  sph : Formalism.IndefR.WeilFull.SphInertAtO R.ψ (Yc D k) (Yc D (k + 1)) (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1
    (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.ωY t k)
  rS : (Yc D k).rank = (R.datYt t k R.triv).r + (R.datYt t k R.triv).s * (R.datYt t k R.triv).t
  rT : (Yc D (k + 1)).rank = (Yc D k).rank + (R.datYt t k R.triv).t
  odd : Odd (R.datYt t k R.triv).t
  hQ : (R.datYt t k R.triv).Q = R.Q t
  xq : (R.datYt t k R.triv).xq = fun PP => (R.xiR t PP)⁻¹
  hP : (R.datYt t k R.triv).P = Formalism.L2.DIV.LevelP.triv (R.datYt t k R.triv).Pg (R.datYt t k R.triv).r ℂ
  unr : ∀ e, IsIdemSum e ((R.datYt t k R.triv).Pg ∪ R.Q t) →
    Formalism.IndefR.Fin.UnrOff e (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 ∧
      Formalism.IndefR.Fin.UnrOff e (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2
  tameG : ∀ PP ∈ (R.datYt t k R.triv).Pg, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP →
    Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 (R.chi (k + 1) PP) (-1) ∧
      Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.chi (k + 1) PP) (-1)
  tameQ : ∀ PP ∈ R.Q t, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP →
    Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 (R.xiR t PP) 1 ∧
      Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.xiR t PP) 1

open Classical in

structure SideYR (t : T) (k : ℕ) : Prop where
  dat : ∃ (BS : D.what₂.Tau → Matrix (Fin (Yc D k).rank) (Fin (Yc D k).rank) ℂ)
    (BT : D.what₂.Tau → Matrix (Fin (Yc D (k + 1)).rank) (Fin (Yc D (k + 1)).rank) ℂ) (pS pT : D.what₂.Tau → ℕ),
    IsDatumStep R.ψ R.θ (Yc D k) (Yc D (k + 1)) (cart (R.MY k)) (cart (R.MY (k + 1))) BS BT pS pT (R.ΛY k)
      (R.ΛY (k + 1)) (R.βY k) (R.βY (k + 1)) (R.datYt t k R.triv) (R.chi (k + 1)) (R.Q t) (R.xiR t) (R.vac k) (R.vY t k)
  sph : Formalism.IndefR.WeilFull.SphInertAtO R.ψ (Yc D k) (Yc D (k + 1)) (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1
    (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.ωY t k)
  unr : ∀ e, IsIdemSum e ((R.datYt t k R.triv).Pg ∪ R.Q t) →
    Formalism.IndefR.Fin.UnrOff e (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 ∧
      Formalism.IndefR.Fin.UnrOff e (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2
  tameG : ∀ PP ∈ (R.datYt t k R.triv).Pg, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP →
    Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 (R.chi (k + 1) PP) (-1) ∧
      Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.chi (k + 1) PP) (-1)
  tameQ : ∀ PP ∈ R.Q t, ∀ e, Formalism.L2.NTheta.IsIdemAt e PP →
    Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1 (R.xiR t PP) 1 ∧
      Formalism.IndefR.Fin.TameAt e PP (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.xiR t PP) 1

end Formalism.IndefR.Eqv.KerDiag

end
end

