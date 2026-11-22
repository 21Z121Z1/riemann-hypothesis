import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.HomogeneousComponentMulForm
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationExists
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepTwoPiece
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0043

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.InterSumEventuallyEqInterNum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Symmetry

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem tensorSub_eq_foldl_map {n : ℕ} (L : Fin n → SubSystem S x Ω) (T : Finset (Fin n)) :
    tensorSub L T = (((List.finRange n).filter (· ∈ T)).map L).foldl
      (fun F Q => F.twist Q) (twistSys S x 0) := by
  unfold tensorSub
  rw [List.foldl_map]

theorem tensorSub_comp_perm {n : ℕ} (L : Fin n → SubSystem S x Ω) (σ : Equiv.Perm (Fin n))
    (T : Finset (Fin n)) :
    tensorSub (fun i => L (σ i)) T = tensorSub L (T.map σ.toEmbedding) := by
  rw [tensorSub_eq_foldl_map, tensorSub_eq_foldl_map]
  have hp : (((List.finRange n).filter (· ∈ T)).map σ).Perm
      ((List.finRange n).filter (· ∈ T.map σ.toEmbedding)) := by
    rw [List.perm_ext_iff_of_nodup (((List.nodup_finRange n).filter _).map σ.injective)
      ((List.nodup_finRange n).filter _)]
    intro a
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      Finset.mem_map_equiv]
    constructor
    · rintro ⟨b, hb, rfl⟩
      simpa using hb
    · intro ha
      exact ⟨σ.symm a, ha, by simp⟩
  have hfun : (fun i => L (σ i)) = L ∘ σ := rfl
  rw [hfun, ← List.map_map]
  exact (hp.map L).foldl_eq' (fun F _ P _ Q => by
    rw [SubSystem.twist_assoc, SubSystem.twist_comm F, ← SubSystem.twist_assoc]) _

theorem interSum_comp_perm (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω)
    (σ : Equiv.Perm (Fin n)) (c : ℕ) :
    interSum pp (fun i => L (σ i)) c = interSum pp L c := by
  unfold interSum
  refine Fintype.sum_equiv (Equiv.finsetCongr σ) _ _ fun T => ?_
  rw [Equiv.finsetCongr_apply, Finset.card_map, tensorSub_comp_perm]

theorem interNum_comp_perm (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω)
    (σ : Equiv.Perm (Fin n)) :
    interNum pp (fun i => L (σ i)) = interNum pp L := by
  unfold interNum
  congr 1
  funext c
  exact interSum_comp_perm pp L σ c

theorem interSum_eventually_eq_interNum (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω)
    {m : ℤ} (h : ∀ᶠ c : ℕ in atTop, interSum pp L c = m) :
    ∀ᶠ c : ℕ in atTop, interSum pp L c = interNum pp L := by
  have ht : Tendsto (interSum pp L) atTop (nhds m) :=
    tendsto_const_nhds.congr' (h.mono fun _ hc => hc.symm)
  have hm : interNum pp L = m := ht.limUnder_eq
  rw [hm]
  exact h

end Symmetry

theorem GenericPointSectionInput.proof (hE : InterNumEventual.Statement.{u, w})
    (hA : InterNumAdditive.Statement.{u, w}) (hC : InterNumCut.Statement.{u, w})
    (hP : InterNumPointDeg.Statement.{u, w}) : GenericPointSectionInput.Statement.{u, w} := by
  intro k _ Ω _ _ N x
  refine ⟨fun n pp L hW => ?_, fun n pp L σ _ => ?_, fun n pp L i L' L'' hW => ?_,
    fun n pp L Lc s hW hs hne => ?_, fun pp hW => ?_⟩
  · obtain ⟨m, hm⟩ := hE k Ω N x n pp L hW
    exact interSum_eventually_eq_interNum pp _ hm
  · exact interNum_comp_perm pp (fun i => (L i).toSubSystem) σ
  · exact hA k Ω N x n pp L i L' L'' hW
  · exact hC k Ω N x n pp L Lc s hW hs hne
  · exact hP k Ω N x pp hW

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDivisionNearSDensity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

namespace DivisionNearS

variable {D : ℕ}

theorem exp_identity (T : ℕ) (t G g₂ E φc : ℝ) (hG : 0 < G) (hg₂ : 0 < g₂) :
    g₂ * G ^ (D + T) * G ^ (-(t + 1)) *
        Real.exp (-(φc + Real.log g₂ + (D : ℝ) * Real.log G +
          ((T : ℝ) - 1 - t) * (Real.log G + Real.log E))) =
      Real.exp (-(φc + ((T : ℝ) - 1 - t) * Real.log E)) := by
  obtain ⟨a, rfl⟩ : ∃ a, g₂ = Real.exp a := ⟨_, (Real.exp_log hg₂).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b, G = Real.exp b := ⟨_, (Real.exp_log hG).symm⟩
  rw [Real.log_exp, Real.log_exp, ← Real.rpow_natCast, ← Real.exp_mul, ← Real.exp_mul,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem dens_transform (X : EmbDatum D) (Z : ZeroDatum X) (φA : TwistWeight X.A X.L₂ X.L D)
    (T : ℕ) (t : ℝ) (F : Fin X.A.n → X.U → ℂ) (hF : F ∈ topSections X.A X.L₂ X.L (D + T))
    (j c : Fin X.A.n) (x : X.U) (hx : x ∈ (X.A.chart j).source ∩ (X.A.chart c).source) :
    2 ^ D * ‖F j x‖ ^ 2 * (∑ i, ‖Z.s i j x‖ ^ 2) ^ (-(t + 1)) *
        Real.exp (-(φA.φ j x + ((T : ℝ) - 1 - t) * fsWeight X.e j x)) =
      ‖jac X.A j c x‖ ^ 2 * (2 ^ D * ‖F c x‖ ^ 2 * (∑ i, ‖Z.s i c x‖ ^ 2) ^ (-(t + 1)) *
        Real.exp (-(φA.φ c x + ((T : ℝ) - 1 - t) * fsWeight X.e c x))) := by
  have hG : 0 < ‖X.L.g j c x‖ ^ 2 := by
    have := X.L.ne_zero j c x hx; positivity
  have hg₂ : 0 < ‖X.L₂.g j c x‖ ^ 2 := by
    have := X.L₂.ne_zero j c x hx; positivity
  have hE := esum_pos X c x hx.2
  have hS : 0 ≤ ∑ i, ‖Z.s i c x‖ ^ 2 := by positivity
  have hFj : ‖F j x‖ ^ 2 = ‖jac X.A j c x‖ ^ 2 * ‖X.L₂.g j c x‖ ^ 2 *
      (‖X.L.g j c x‖ ^ 2) ^ (D + T) * ‖F c x‖ ^ 2 := by
    rw [hF.2.1 j c x hx, norm_mul, norm_mul, norm_mul, norm_pow]; ring
  have key := exp_identity (D := D) T t _ _ (∑ k, ‖X.e k c x‖ ^ 2) (φA.φ c x) hG hg₂
  rw [hFj, ssum_transform X Z j c x hx, Real.mul_rpow hG.le hS, φA.compat j c x hx]
  unfold fsWeight
  rw [esum_transform X j c x hx, Real.log_mul hG.ne' hE.ne', ← key]
  ring

theorem dens_eq (X : EmbDatum D) (φA : TwistWeight X.A X.L₂ X.L D) (T : ℕ) (t : ℝ)
    (j : Fin X.A.n) (x : X.U) (hx : x ∈ (X.A.chart j).source) (a S : ℝ) :
    a * S ^ (-(t + 1)) * Real.exp (-(φA.φ j x + ((T : ℝ) - 1 - t) * fsWeight X.e j x)) =
      a * Real.exp (-(φA.φ j x + (T : ℝ) * fsWeight X.e j x)) *
        (S ^ (-(t + 1)) * (∑ k, ‖X.e k j x‖ ^ 2) ^ (t + 1)) := by
  have hE := esum_pos X j x hx
  rw [Real.rpow_def_of_pos hE (t + 1)]
  unfold fsWeight
  have : Real.exp (-(φA.φ j x + ((T : ℝ) - 1 - t) * Real.log (∑ k, ‖X.e k j x‖ ^ 2))) =
      Real.exp (-(φA.φ j x + (T : ℝ) * Real.log (∑ k, ‖X.e k j x‖ ^ 2))) *
        Real.exp (Real.log (∑ k, ‖X.e k j x‖ ^ 2) * (t + 1)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]; ring

theorem ratio_le_of_nonpos (t S E r : ℝ) (ht : t + 1 ≤ 0) (hE : 0 < E) (hS : 0 ≤ S)
    (hr : 0 ≤ r) (hSE : S ≤ r * E) :
    S ^ (-(t + 1)) * E ^ (t + 1) ≤ r ^ (-(t + 1)) := by
  have h1 : S ^ (-(t + 1)) ≤ (r * E) ^ (-(t + 1)) := Real.rpow_le_rpow hS hSE (by linarith)
  rw [Real.mul_rpow hr hE.le] at h1
  have hEp : 0 < E ^ (t + 1) := Real.rpow_pos_of_pos hE _
  calc S ^ (-(t + 1)) * E ^ (t + 1) ≤ r ^ (-(t + 1)) * E ^ (-(t + 1)) * E ^ (t + 1) := by gcongr
    _ = r ^ (-(t + 1)) := by
      rw [Real.rpow_neg hE.le, mul_assoc, inv_mul_cancel₀ hEp.ne', mul_one]

theorem ratio_le_of_nonneg (t S E C : ℝ) (ht : 0 ≤ t + 1) (hE : 0 < E) (hS : 0 < S)
    (hSE : E ≤ C * S) :
    S ^ (-(t + 1)) * E ^ (t + 1) ≤ C ^ (t + 1) := by
  have h1 : E / S ≤ C := (div_le_iff₀ hS).mpr hSE
  have h2 : (E / S) ^ (t + 1) ≤ C ^ (t + 1) := Real.rpow_le_rpow (by positivity) h1 ht
  rw [Real.div_rpow hE.le hS.le, div_eq_mul_inv, ← Real.rpow_neg hS.le, mul_comm] at h2
  exact h2

theorem local_bound (X : EmbDatum D) (Z : ZeroDatum X) (φA : TwistWeight X.A X.L₂ X.L D)
    (T : ℕ) (hDT : D ≤ T) (F : Fin X.A.n → X.U → ℂ) (hF : F ∈ topSections X.A X.L₂ X.L (D + T))
    (hfil : IsFil X.A Z.s F (T - D)) (t : ℝ) (ht : 0 < t + 1) (x₀ : X.U)
    (hx₀ : x₀ ∈ zeroSet X.A Z.s) (c : Fin X.A.n) (hc : c = chartIdx X.A x₀) :
    ∃ ε > (0 : ℝ), ∃ K : ℝ, Metric.ball (X.A.chart c x₀) ε ⊆ (X.A.chart c).target ∧
      ∀ w ∈ Metric.ball (X.A.chart c x₀) ε,
        ENNReal.ofReal (2 ^ D * ‖F c ((X.A.chart c).symm w)‖ ^ 2 *
            (∑ i, ‖Z.s i c ((X.A.chart c).symm w)‖ ^ 2) ^ (-(t + 1)) *
            Real.exp (-(φA.φ c ((X.A.chart c).symm w) +
              ((T : ℝ) - 1 - t) * fsWeight X.e c ((X.A.chart c).symm w)))) ≤
          ENNReal.ofReal (K * ‖w - X.A.chart c x₀‖ ^ (2 * ((T : ℝ) - D) - 2 * (t + 1))) := by
  subst hc
  set c := chartIdx X.A x₀
  set w₀ := X.A.chart c x₀
  have hx₀s : x₀ ∈ (X.A.chart c).source := mem_source_chartIdx X.A x₀
  have hw₀t : w₀ ∈ (X.A.chart c).target := (X.A.chart c).map_source hx₀s
  have hsymm : (X.A.chart c).symm w₀ = x₀ := (X.A.chart c).left_inv hx₀s
  have hmem : w₀ ∈ (X.A.chart c).target ∩ (X.A.chart c).symm ⁻¹' (X.A.chart c).source :=
    ⟨hw₀t, by simpa [hsymm] using hx₀s⟩
  have hnhd : (X.A.chart c).target ∩ (X.A.chart c).symm ⁻¹' (X.A.chart c).source ∈ 𝓝 w₀ :=
    ((X.A.chart c).continuousOn_symm.isOpen_inter_preimage (X.A.chart c).open_target
      (X.A.chart c).open_source).mem_nhds hmem

  have hfan : AnalyticAt ℂ (F c ∘ (X.A.chart c).symm) w₀ := hF.1 c c w₀ hmem
  obtain ⟨C₁, hC₁⟩ := exists_bound_of_iteratedFDeriv_eq_zero hfan (T - D)
    (fun k hk => hfil x₀ hx₀ k hk)

  set σ : (Fin D → ℂ) → (Fin D → ℂ) := fun z i => Z.s i c ((X.A.chart c).symm z)
  have hσd : DifferentiableAt ℂ σ w₀ :=
    differentiableAt_pi.mpr fun i => ((s_mem X Z i).1 c c w₀ hmem).differentiableAt
  have hdet : LinearMap.det (fderiv ℂ σ w₀ : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) ≠ 0 :=
    Z.nondeg x₀ hx₀
  have hσ0 : σ w₀ = 0 := funext fun i => by simp only [σ, hsymm]; exact hx₀ i
  obtain ⟨κ, hκ, hκb⟩ := exists_lowerBound_of_det_ne_zero hσd.hasFDerivAt hdet hσ0

  set h : (Fin D → ℂ) → ℝ := fun w => Real.exp (-(φA.φ c ((X.A.chart c).symm w) +
    ((T : ℝ) - 1 - t) * fsWeight X.e c ((X.A.chart c).symm w)))
  have hφc : ContinuousAt (fun w => φA.φ c ((X.A.chart c).symm w)) w₀ :=
    ((φA.smooth c c).continuousOn).continuousAt hnhd
  have hEc : ContinuousAt (fun w => ∑ k, ‖X.e k c ((X.A.chart c).symm w)‖ ^ 2) w₀ := by
    have hk : ∀ k, ContinuousAt (fun w => X.e k c ((X.A.chart c).symm w)) w₀ := fun k =>
      ((X.e_mem k).1 c c w₀ hmem).continuousAt
    exact tendsto_finsetSum Finset.univ fun k _ => (hk k).norm.pow 2
  have hE0 : (∑ k, ‖X.e k c ((X.A.chart c).symm w₀)‖ ^ 2) ≠ 0 := by
    rw [hsymm]; exact (esum_pos X c x₀ hx₀s).ne'
  have hcont : ContinuousAt h w₀ :=
    (hφc.add (continuousAt_const.mul (hEc.log hE0))).neg.rexp
  have hev : ∀ᶠ w in 𝓝 w₀, h w < h w₀ + 1 := hcont.eventually (gt_mem_nhds (lt_add_one _))
  have hall := (show ∀ᶠ w in 𝓝 w₀, w ∈ (X.A.chart c).target from
    (X.A.chart c).open_target.mem_nhds hw₀t).and (hC₁.and (hκb.and hev))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hall
  have hh0 : 0 < h w₀ := Real.exp_pos _
  refine ⟨ε, hε, 2 ^ D * C₁ ^ 2 * (κ ^ 2) ^ (-(t + 1)) * (h w₀ + 1), fun w hw => (hball w hw).1,
    fun w hw => ?_⟩
  obtain ⟨-, h1, h2, h3⟩ := hball w hw
  apply ENNReal.ofReal_le_ofReal
  have hK : 0 ≤ 2 ^ D * C₁ ^ 2 * (κ ^ 2) ^ (-(t + 1)) * (h w₀ + 1) := by positivity
  by_cases hw0 : w = w₀
  · have hS0 : ∑ i, ‖Z.s i c ((X.A.chart c).symm w)‖ ^ 2 = 0 := by
      rw [hw0, hsymm]; simp [show ∀ i, Z.s i c x₀ = 0 from hx₀]
    rw [hS0, Real.zero_rpow (by linarith)]
    simp only [mul_zero, zero_mul]
    exact mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _)
  · set r := ‖w - w₀‖ with hr
    have hr0 : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hw0)
    set S := ∑ i, ‖Z.s i c ((X.A.chart c).symm w)‖ ^ 2
    have hσS : ‖σ w‖ ≤ Real.sqrt S := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
      refine Real.le_sqrt_of_sq_le ?_
      exact Finset.single_le_sum (f := fun i => ‖Z.s i c ((X.A.chart c).symm w)‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ i)
    have hS : κ ^ 2 * r ^ 2 ≤ S := by
      have : (κ * r) ^ 2 ≤ (Real.sqrt S) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (h2.trans hσS) 2
      rwa [Real.sq_sqrt (by positivity), mul_pow] at this
    have hSr : S ^ (-(t + 1)) ≤ (κ ^ 2 * r ^ 2) ^ (-(t + 1)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hS (by linarith)
    have hF2 : ‖F c ((X.A.chart c).symm w)‖ ^ 2 ≤ (C₁ * r ^ (T - D)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hra : r ^ (2 * ((T : ℝ) - D) - 2 * (t + 1)) =
        (r ^ (T - D)) ^ 2 * (r ^ 2) ^ (-(t + 1)) := by
      rw [← pow_mul, ← Real.rpow_natCast r ((T - D) * 2), ← Real.rpow_two r,
        ← Real.rpow_mul hr0.le, ← Real.rpow_add hr0]
      congr 1
      push_cast [Nat.cast_sub hDT]
      ring
    calc 2 ^ D * ‖F c ((X.A.chart c).symm w)‖ ^ 2 * S ^ (-(t + 1)) * h w
        ≤ 2 ^ D * (C₁ * r ^ (T - D)) ^ 2 * (κ ^ 2 * r ^ 2) ^ (-(t + 1)) * (h w₀ + 1) := by
          gcongr
      _ = 2 ^ D * C₁ ^ 2 * (κ ^ 2) ^ (-(t + 1)) * (h w₀ + 1) *
            r ^ (2 * ((T : ℝ) - D) - 2 * (t + 1)) := by
          rw [hra, Real.mul_rpow (by positivity) (by positivity)]; ring

end DivisionNearS

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperQuotFiltX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace SnapperQuotFilt

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

def pieceIso (N₀ N₁ : FinGradedSub (S := S) (x := x) E) {g : E} {e : ℤ} {pp : Ideal (Poly S N)}
    (Q : LineBundle S x) (c : ℤ) (hpp : pp.IsPrime) (hg : g ∈ N₁.piece e)
    (hN : ∀ c, N₁.piece c = N₀.piece c ⊔ Submodule.span S
      {z | ∃ (f : Poly S N) (d : ℕ), f.IsHomogeneous d ∧ e + d = c ∧ z = aeval x f • g})
    (hiff : ∀ (f : Poly S N) (d : ℕ), f.IsHomogeneous d → (f ∈ pp ↔ aeval x f • g ∈ N₀.piece (e + d))) :
    QuotIso ((N₁.tildeSys 0).twist (Q.twist (twistSys S x c))) ((N₀.tildeSys 0).twist (Q.twist (twistSys S x c)))
      (Q.twist (twistSys S x (c - e))) ((Q.twist (twistSys S x (c - e))).twist (idealSys x pp)) where
  equiv I := (LinearEquiv.ofBijective (StepTwo.Piece.gBar N₀ N₁ Q c hg hiff I)
    (StepTwo.Piece.gBar_bijective N₀ N₁ Q c hpp hg hN hiff I)).symm
  comm I J h y := by
    apply (LinearEquiv.ofBijective _ (StepTwo.Piece.gBar_bijective N₀ N₁ Q c hpp hg hN hiff J)).injective
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.ofBijective_apply, StepTwo.Piece.gBar_comm]
    congr 1
    exact ((LinearEquiv.ofBijective _ (StepTwo.Piece.gBar_bijective N₀ N₁ Q c hpp hg hN hiff I)).apply_symm_apply
      y).symm

end SnapperQuotFilt

open SnapperQuotFilt in

theorem SnapperQuotFilt.proof : SnapperQuotFilt.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F₁ F₂ hfg hle J hJ hxJ hJF
  classical
  have hfg₂ : ∀ I, (F₂.sub I).FG := fg_of_le F₁ F₂ hfg hle
  obtain ⟨M₁, -, hM₁⟩ := Extension.proof k Ω N x E F₁ hfg
  obtain ⟨M₀, -, hM₀⟩ := Extension.proof k Ω N x E F₂ hfg₂
  obtain ⟨H, hHJ, hHspan, hHhom⟩ := IdealTwistFamily.exists_finset_forms J hJ
  set hs : Fin H.card → Poly k N := fun l => (H.equivFin.symm l : Poly k N) with hs_def
  have hrange : Set.range hs = ↑H := by
    ext f
    constructor
    · rintro ⟨l, rfl⟩
      exact (H.equivFin.symm l).2
    · intro hf
      exact ⟨H.equivFin ⟨f, hf⟩, by simp [hs_def]⟩
  have hhom : ∀ l, (hs l).IsHomogeneous (hs l).totalDegree := fun l => hHhom _ (H.equivFin.symm l).2
  have hsJ : ∀ l, hs l ∈ J := fun l => hHJ (H.equivFin.symm l).2
  set A := gsup M₁ M₀ with hA_def
  set B := gsup M₀ (gmul A hs fun l => (hs l).totalDegree) with hB_def
  have hA : ∀ I, A.tilde 0 I = F₁.sub I := fun I => by
    rw [hA_def, tilde_gsup, hM₁, hM₀]
    exact sup_eq_left.mpr (hle I)
  have hB : ∀ I, B.tilde 0 I = F₂.sub I := fun I => by
    rw [hB_def, tilde_gsup, hM₀]
    exact sup_eq_left.mpr ((tilde_gmul_le A hs _ hhom hsJ F₁.toSubSystem (fun I => (hA I).le) I).trans (hJF I))
  have hBA : ∀ c, B.piece c ≤ A.piece c := fun c => by
    refine sup_le le_sup_right (Submodule.span_le.mpr ?_)
    rintro _ ⟨l, b, m, hm, hb, rfl⟩
    have := A.smul_mem _ b (hs l) m (hhom l) hm
    rwa [hb] at this
  have hkill : ∀ (f : Poly k N) (e : ℕ), f ∈ J → f.IsHomogeneous e → ∀ (a : ℤ), ∀ z ∈ A.piece a,
      aeval x f • z ∈ B.piece (a + e) := fun f e hf hfe a z hz =>
    Submodule.mem_sup_right (smul_mem_gmul A hs _ hhom (by rw [hrange, hHspan]) hf hfe hz)
  obtain ⟨n, Nf, g, deg, pr, h0, hlast, hk⟩ :=
    StepTwo.Filt.proof PrimeFiltration.Exists.proof k Ω N x E A B hBA J hkill
  have hstep : ∀ (j : Fin n) (c : ℤ), (Nf j.castSucc).piece c ≤ (Nf j.succ).piece c := fun j c => by
    rw [(hk j).2.2.2.2.2.1 c]
    exact le_sup_left
  have hmono : ∀ (i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) (c : ℤ),
      (Nf ⟨i, by omega⟩).piece c ≤ (Nf ⟨j, by omega⟩).piece c := by
    intro i j hij hj c
    induction j with
    | zero =>
      obtain rfl : i = 0 := by omega
      exact le_rfl
    | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with h | h
      · subst h
        exact le_rfl
      · exact (ih (by omega) (by omega)).trans (hstep ⟨j, by omega⟩ c)
  have hNf : ∀ m (hm : m ≤ n), Nf ⟨min m n, by omega⟩ = Nf ⟨m, by omega⟩ := fun m hm =>
    congrArg Nf (Fin.ext (Nat.min_eq_left hm))
  set G : ℕ → SubFamily k x E := fun m => tildeFam (Nf ⟨min m n, by omega⟩) with hG_def
  have hGle : ∀ m I, (G m).sub I ≤ F₁.sub I := fun m I => by
    rw [← hA, ← hlast]
    exact tilde_mono (hmono _ n (by omega) le_rfl) 0 I
  refine ⟨n, G, pr, fun m => -deg m, fun m I => fg_of_le F₁ (G m) hfg (hGle m) I, ?_, ?_, ?_, ?_, ?_⟩
  · refine SubSystem.ext_sub fun I => ?_
    change (Nf ⟨min 0 n, _⟩).tilde 0 I = F₂.sub I
    rw [hNf 0 (Nat.zero_le n), Fin.mk_zero, h0, hB]
  · refine SubSystem.ext_sub fun I => ?_
    change (Nf ⟨min n n, _⟩).tilde 0 I = F₁.sub I
    rw [hNf n le_rfl]
    change (Nf (Fin.last n)).tilde 0 I = F₁.sub I
    rw [hlast, hA]
  · intro m hm I
    change (Nf ⟨min m n, _⟩).tilde 0 I ≤ (Nf ⟨min (m + 1) n, _⟩).tilde 0 I
    rw [hNf m hm.le, hNf (m + 1) hm]
    exact tilde_mono (hstep ⟨m, hm⟩) 0 I
  · intro m
    obtain ⟨hp, hh, -, hJf, -⟩ := hk m
    exact ⟨hp, hh, le_of_forms hJ hJf⟩
  · intro m t L n' c
    obtain ⟨hp, -, -, -, hg, hN, hiff⟩ := hk m
    dsimp only
    have e1 : (G (m + 1)).toSubSystem = (Nf m.succ).tildeSys 0 := by
      change (Nf ⟨min (m + 1) n, _⟩).tildeSys 0 = _
      rw [hNf _ m.2]
      rfl
    have e2 : (G m).toSubSystem = (Nf m.castSucc).tildeSys 0 := by
      change (Nf ⟨min m n, _⟩).tildeSys 0 = _
      rw [hNf _ m.2.le]
      rfl
    have hs1 : ∀ T : SubSystem k x E, (T.twistPows t (fun j => (L j).toSubSystem) n').twist (twistSys k x c) =
        T.twist ((powsBundle t L n').toSubSystem.twist (twistSys k x c)) := fun T => by
      rw [twistPows_eq, twist_twist]
    have ht1 : ((twistSys k x (-deg m)).twistPows t (fun j => (L j).toSubSystem) n').twist (twistSys k x c) =
        (powsBundle t L n').toSubSystem.twist (twistSys k x (c - deg m)) := by
      rw [twistPows_eq]
      refine SubSystem.ext_sub fun I => ?_
      simp only [SubSystem.twist_sub_eq_mul_of_line]
      rw [sub_eq_add_neg, ← twistSys_sub_mul]
      ring
    have ht2 : (((twistSys k x (-deg m)).twist (idealSys x (pr m))).twistPows t (fun j => (L j).toSubSystem)
        n').twist (twistSys k x c) =
        ((powsBundle t L n').toSubSystem.twist (twistSys k x (c - deg m))).twist (idealSys x (pr m)) := by
      rw [twistPows_eq]
      refine SubSystem.ext_sub fun I => ?_
      simp only [SubSystem.twist_sub_eq_mul_of_line]
      rw [sub_eq_add_neg, ← twistSys_sub_mul]
      ring
    rw [e1, e2, hs1, hs1, ht1, ht2]
    exact ⟨pieceIso (Nf m.castSucc) (Nf m.succ) (powsBundle t L n') c hp hg hN hiff⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSubFamilyTwistX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

section

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

omit [Module S E] [IsScalarTower S Ω E] in

theorem SubSystem.twist_sub_fg (F : SubSystem S x E) (Q : SubSystem S x Ω) (I : Chart x)
    (hF : (F.sub I).FG) (hQ : (Q.sub I).FG) : ((F.twist Q).sub I).FG := by
  obtain ⟨sF, hsF⟩ := hF
  obtain ⟨sQ, hsQ⟩ := hQ
  classical
  refine ⟨Finset.image₂ (fun q y => q • y) sQ sF, ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    rw [Finset.coe_image₂] at hz
    obtain ⟨q, hq, y, hy, rfl⟩ := hz
    exact Submodule.subset_span ⟨q, hsQ ▸ Submodule.subset_span hq, y, hsF ▸ Submodule.subset_span hy, rfl⟩
  · change Submodule.span _ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨q, hq, y, hy, rfl⟩
    rw [← hsQ] at hq
    rw [← hsF] at hy
    refine Submodule.span_induction (p := fun q _ => q • y ∈
      Submodule.span (chartRing S x I) ((Finset.image₂ (fun q y => q • y) sQ sF : Finset E) : Set E)) ?_ ?_ ?_ ?_ hq
    · intro q hq
      refine Submodule.span_induction (p := fun y _ => q • y ∈
        Submodule.span (chartRing S x I) ((Finset.image₂ (fun q y => q • y) sQ sF : Finset E) : Set E)) ?_ ?_ ?_ ?_ hy
      · intro y hy
        exact Submodule.subset_span (by rw [Finset.coe_image₂]; exact ⟨q, hq, y, hy, rfl⟩)
      · rw [smul_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
      · intro a z _ hz
        rw [Subalgebra.smul_def, smul_comm]
        exact Submodule.smul_mem _ a hz
    · rw [zero_smul]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [add_smul]; exact Submodule.add_mem _ ha hb
    · intro a q _ hq
      rw [smul_assoc]
      exact Submodule.smul_mem _ a hq

end

theorem SubFamilyTwist.proof : SubFamilyTwist.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F Q hF
  exact ⟨F.twistFam Q.toSubFamily, rfl, fun I =>
    SubSystem.twist_sub_fg F.toSubSystem Q.toSubSystem I (hF I) (Q.fg I)⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

