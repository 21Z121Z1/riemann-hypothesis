import Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoIntUv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0161

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFderivChiBound
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Bump

def bump0 : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩

def chi (w : ℂ) : ℂ := ((bump0 w : ℝ) : ℂ)

def chin (n : ℕ) (w : ℂ) : ℂ := chi (((n : ℝ) + 1)⁻¹ • w)

theorem chi_contDiff : ContDiff ℝ ∞ chi := by
  unfold chi
  exact Complex.ofRealCLM.contDiff.comp bump0.contDiff

theorem chin_contDiff (n : ℕ) : ContDiff ℝ ∞ (chin n) := by
  unfold chin
  exact chi_contDiff.comp (contDiff_const_smul _)

theorem norm_chin_le (n : ℕ) (w : ℂ) : ‖chin n w‖ ≤ 1 := by
  unfold chin chi
  rw [Complex.norm_real, Real.norm_of_nonneg bump0.nonneg]
  exact bump0.le_one

theorem chin_zero (n : ℕ) (w : ℂ) (hw : 2 * ((n : ℝ) + 1) ≤ ‖w‖) : chin n w = 0 := by
  unfold chin chi
  rw [bump0.zero_of_le_dist, Complex.ofReal_zero]
  show (2 : ℝ) ≤ dist (((n : ℝ) + 1)⁻¹ • w) 0
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹),
    inv_mul_eq_div, le_div_iff₀ (by positivity)]
  exact hw

theorem chin_eventually_one (n : ℕ) (w : ℂ) (hw : ‖w‖ < (n : ℝ) + 1) : chin n =ᶠ[𝓝 w] fun _ => 1 := by
  have hopen : IsOpen {v : ℂ | ‖v‖ < (n : ℝ) + 1} := isOpen_lt continuous_norm continuous_const
  filter_upwards [hopen.mem_nhds hw] with v hv
  show chin n v = 1
  unfold chin chi
  rw [bump0.one_of_mem_closedBall, Complex.ofReal_one]
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1)⁻¹)]
  show ((n : ℝ) + 1)⁻¹ * ‖v‖ ≤ 1
  rw [inv_mul_le_iff₀ (by positivity)]
  linarith

theorem fderiv_chin_zero (n : ℕ) (w : ℂ) (hw : ‖w‖ < (n : ℝ) + 1) : fderiv ℝ (chin n) w = 0 := by
  rw [(chin_eventually_one n w hw).fderiv_eq]
  exact fderiv_const_apply _

theorem exists_fderiv_chi_bound : ∃ C : ℝ, ∀ w, ‖fderiv ℝ chi w‖ ≤ C := by
  have hcs : HasCompactSupport chi := by
    show HasCompactSupport ((fun x : ℝ => (x : ℂ)) ∘ bump0)
    exact bump0.hasCompactSupport.comp_left Complex.ofReal_zero
  exact (chi_contDiff.continuous_fderiv (by simp)).bounded_above_of_compact_support (hcs.fderiv ℝ)

theorem norm_fderiv_chin_le {C : ℝ} (hC : ∀ w, ‖fderiv ℝ chi w‖ ≤ C) (n : ℕ) (w : ℂ) :
    ‖fderiv ℝ (chin n) w‖ ≤ C := by
  have hs0 : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  have hs1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hd : HasFDerivAt (chin n)
      ((fderiv ℝ chi (((n : ℝ) + 1)⁻¹ • w)).comp (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ ℂ)) w := by
    have h1 := (chi_contDiff.differentiable (by simp) (((n : ℝ) + 1)⁻¹ • w)).hasFDerivAt
    have h2 : HasFDerivAt (fun v : ℂ => ((n : ℝ) + 1)⁻¹ • v) (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ ℂ) w :=
      (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ ℂ).hasFDerivAt
    exact h1.comp w h2
  have hn : ‖((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg hs0.le]
    have := (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℝ ℂ‖ ≤ 1)
    nlinarith [norm_nonneg (ContinuousLinearMap.id ℝ ℂ)]
  rw [hd.fderiv]
  calc _ ≤ ‖fderiv ℝ chi (((n : ℝ) + 1)⁻¹ • w)‖ * ‖((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ ℂ‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ C * 1 := mul_le_mul (hC _) hn (norm_nonneg _) (le_trans (norm_nonneg _) (hC 0))
    _ = C := mul_one C

theorem norm_dZ_le (f : ℂ → ℂ) (w : ℂ) : ‖NF.dZ f w‖ ≤ ‖fderiv ℝ f w‖ := by
  show ‖(1 / 2 : ℂ) * (fderiv ℝ f w 1 - Complex.I * fderiv ℝ f w Complex.I)‖ ≤ _
  set L := fderiv ℝ f w
  have h1 : ‖L 1‖ ≤ ‖L‖ := by simpa using L.le_opNorm 1
  have h2 : ‖L Complex.I‖ ≤ ‖L‖ := by simpa using L.le_opNorm Complex.I
  have h3 : ‖L 1 - Complex.I * L Complex.I‖ ≤ ‖L 1‖ + ‖L Complex.I‖ := by
    calc ‖L 1 - Complex.I * L Complex.I‖ ≤ ‖L 1‖ + ‖Complex.I * L Complex.I‖ := norm_sub_le _ _
      _ = ‖L 1‖ + ‖L Complex.I‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hh : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [norm_mul, hh]
  linarith

theorem norm_dZb_le (f : ℂ → ℂ) (w : ℂ) : ‖NF.dZb f w‖ ≤ ‖fderiv ℝ f w‖ := by
  show ‖(1 / 2 : ℂ) * (fderiv ℝ f w 1 + Complex.I * fderiv ℝ f w Complex.I)‖ ≤ _
  set L := fderiv ℝ f w
  have h1 : ‖L 1‖ ≤ ‖L‖ := by simpa using L.le_opNorm 1
  have h2 : ‖L Complex.I‖ ≤ ‖L‖ := by simpa using L.le_opNorm Complex.I
  have h3 : ‖L 1 + Complex.I * L Complex.I‖ ≤ ‖L 1‖ + ‖L Complex.I‖ := by
    calc ‖L 1 + Complex.I * L Complex.I‖ ≤ ‖L 1‖ + ‖Complex.I * L Complex.I‖ := norm_add_le _ _
      _ = ‖L 1‖ + ‖L Complex.I‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hh : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [norm_mul, hh]
  linarith

theorem dZ_contDiff {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (NF.dZ f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.1 hf).2
  have h1 : ContDiff ℝ ∞ (fun w => fderiv ℝ f w 1) := hd.clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ (fun w => fderiv ℝ f w Complex.I) := hd.clm_apply contDiff_const
  show ContDiff ℝ ∞ (fun w => (1 / 2 : ℂ) * (fderiv ℝ f w 1 - Complex.I * fderiv ℝ f w Complex.I))
  exact contDiff_const.mul (h1.sub (contDiff_const.mul hI))

theorem dZb_contDiff {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (NF.dZb f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.1 hf).2
  have h1 : ContDiff ℝ ∞ (fun w => fderiv ℝ f w 1) := hd.clm_apply contDiff_const
  have hI : ContDiff ℝ ∞ (fun w => fderiv ℝ f w Complex.I) := hd.clm_apply contDiff_const
  show ContDiff ℝ ∞ (fun w => (1 / 2 : ℂ) * (fderiv ℝ f w 1 + Complex.I * fderiv ℝ f w Complex.I))
  exact contDiff_const.mul (h1.add (contDiff_const.mul hI))

theorem dZ_chin_zero (n : ℕ) (w : ℂ) (hw : ‖w‖ < (n : ℝ) + 1) : NF.dZ (chin n) w = 0 := by
  show (1 / 2 : ℂ) * (fderiv ℝ (chin n) w 1 - Complex.I * fderiv ℝ (chin n) w Complex.I) = 0
  rw [fderiv_chin_zero n w hw]
  simp

theorem dZb_chin_zero (n : ℕ) (w : ℂ) (hw : ‖w‖ < (n : ℝ) + 1) : NF.dZb (chin n) w = 0 := by
  show (1 / 2 : ℂ) * (fderiv ℝ (chin n) w 1 + Complex.I * fderiv ℝ (chin n) w Complex.I) = 0
  rw [fderiv_chin_zero n w hw]
  simp

theorem eventually_lt (w : ℂ) : ∀ᶠ n : ℕ in atTop, ‖w‖ < (n : ℝ) + 1 := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop ‖w‖] with n hn
  linarith

end Bump

end Formalism.FourierDecayAlt.P5.HerB
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermStep
section
namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem germ_step (S : C.HidaSetting E Wp Wq) (hpos : C.ThmPPos S) (hI : KB.IntAll S) (hg : 0 < S.g)
    (Λ : ℕ → ℕ → Fin S.f → ℝ) (hLL : ∀ v, KB.LiftLoc S v fun b s => Λ b s v) (hGL : ∀ v, KB.GermLoc S v)
    (hΛ0 : ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (hn : 2 ≤ n) (b : ℕ) (hb : 1 ≤ b) (hbn : b + n ≤ S.G.r + 2) (P' : ℝ) (hP' : GSup S ε b (n - 1) P')
    (hP'0 : 0 ≤ P') (w' : S.W) (hw' : w' ∈ S.base.Wall) (hcnt : S.base.cnt w' + n * C.Kst ≤ S.Ntop)
    (La : Submodule ℤ (crystallineComparison.V S.f)) [DiscreteTopology La] [IsZLattice ℝ La]
    (hsm : Summable fun σ : crystallineComparison.dualSet La => crystallineComparison.mL C.Kst (fun v => Λ b (n - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) :
    ∃ θ : S.W → ℝ, TB.IsProb (S.base.Wb (S.base.cnt w' + n * C.Kst)) θ ∧
      ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = b - 1) → ∀ κ, TB.PSDOn Y κ →
        ∀ (z₀ : crystallineComparison.V S.f) (Ss : Finset (crystallineComparison.V S.f)), (∀ z ∈ Ss, z - z₀ ∈ La) → (∀ z ∈ Ss, Good z) →
          ZLattice.covolume La * ∑ z ∈ Ss, (KB.NstV S ε (b + n - 1) n w' Y κ z z).re ≤
            (∏ _v : Fin S.f, KB.dlB S b n) *
              ((∑' σ : crystallineComparison.dualSet La, crystallineComparison.mL C.Kst (fun v => Λ b (n - 1) v) ((S.g : ℝ) • (σ : crystallineComparison.V S.f))) * P') *
              ∑ u ∈ S.base.Wb (S.base.cnt w' + n * C.Kst), θ u * S.base.N0 ε (b - 1) u Y κ := by
  have hk : n * C.Kst = (n - 1) * C.Kst + C.Kst := by
    have : n = (n - 1) + 1 := by omega
    conv_lhs => rw [this]
    rw [add_mul, one_mul]
  have hg' : (0 : ℝ) < S.g := by exact_mod_cast hg
  set L : Fin S.f → ℝ := fun v => Λ b (n - 1) v with hLdef
  have hL0 : ∀ v, 0 ≤ L v := fun v => hΛ0 b (n - 1) hb (by omega) (by omega) v

  obtain ⟨θL, hθL, hLV⟩ := Formalism.FourierDecayAlt.P.lift_bound_below_top_all_places E Wp Wq S Λ hpos hLL ε hε (b + n - 2) (n - 1) (by omega)
    (by omega) (by omega) w' hw' (by omega)
  have hΛi : b + n - 2 - (n - 1) + 1 = b := by omega
  rw [hΛi] at hLV

  choose! θ'' hθ'' using hP'
  set Wd := S.base.Wb (S.base.cnt w' + n * C.Kst) with hWd
  set pairs := S.base.Wb (S.base.cnt w' + C.Kst) ×ˢ S.base.Wb (S.base.cnt w' + C.Kst) with hpairs
  have hpw : ∀ x ∈ pairs, (x.1 ∈ S.base.Wall ∧ S.base.cnt x.1 + (n - 1) * C.Kst ≤ S.Ntop ∧
      S.base.Wb (S.base.cnt x.1 + (n - 1) * C.Kst) ⊆ Wd) ∧
      (x.2 ∈ S.base.Wall ∧ S.base.cnt x.2 + (n - 1) * C.Kst ≤ S.Ntop ∧
      S.base.Wb (S.base.cnt x.2 + (n - 1) * C.Kst) ⊆ Wd) := by
    intro x hx
    rw [hpairs, Finset.mem_product, mem_Wb_iff, mem_Wb_iff] at hx
    exact ⟨⟨hx.1.1, by omega, Wb_mono S (by omega)⟩, ⟨hx.2.1, by omega, Wb_mono S (by omega)⟩⟩
  have hpr : ∀ u, u ∈ S.base.Wall → S.base.cnt u + (n - 1) * C.Kst ≤ S.Ntop →
      TB.IsProb (S.base.Wb (S.base.cnt u + (n - 1) * C.Kst)) (θ'' u) := fun u h1 h2 => (hθ'' u h1 h2).1
  let q : crystallineComparison.V S.f → S.W → ℝ := fun σ u =>
    ∑ x ∈ pairs, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x * ((θ'' x.1 u + θ'' x.2 u) / 2)
  have hq : ∀ σ, TB.IsProb Wd (q σ) := by
    intro σ
    set A := crystallineComparison.pat L ((S.g : ℝ) • σ)
    refine ⟨fun u => Finset.sum_nonneg fun x hx => mul_nonneg ((hθL A).1 x) (div_nonneg (add_nonneg
      ((hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1).1 u) ((hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1).1 u)) (by norm_num)),
      fun u hu => Finset.sum_eq_zero fun x hx => ?_, ?_⟩
    · have h1 : θ'' x.1 u = 0 := (hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1).2.1 u fun h => hu ((hpw x hx).1.2.2 h)
      have h2 : θ'' x.2 u = 0 := (hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1).2.1 u fun h => hu ((hpw x hx).2.2.2 h)
      simp [h1, h2]
    · show ∑ u ∈ Wd, ∑ x ∈ pairs, θL A x * ((θ'' x.1 u + θ'' x.2 u) / 2) = 1
      rw [Finset.sum_comm, ← (hθL A).2.2]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib,
        prob_sum_sub (hpr _ (hpw x hx).1.1 (hpw x hx).1.2.1) (hpw x hx).1.2.2,
        prob_sum_sub (hpr _ (hpw x hx).2.1 (hpw x hx).2.2.1) (hpw x hx).2.2.2]
      norm_num
  obtain ⟨θn, hθn, hmix⟩ := tsum_mix Wd (fun σ : crystallineComparison.dualSet La => crystallineComparison.mL C.Kst L ((S.g : ℝ) • (σ : crystallineComparison.V S.f)))
    (fun σ => mL_nonneg _ _ hL0 _) hsm
    (by linarith [one_le_tsum_mL La C.Kst L hL0 (S.g : ℝ) hsm]) (fun σ => q σ) (fun σ => hq σ)
  refine ⟨θn, hθn, fun Y hY κ hκ z₀ Ss hS hgood => ?_⟩
  obtain ⟨Pq, Qq, hreg, hGD⟩ := germ_global S hpos hI hg Λ hLL hGL hΛ0 ε hε n hn b hb hbn w' hcnt Y hY
  obtain ⟨Lm, j1, j2, hLm⟩ := GlobalTheory.dual_smul_mem La (S.g : ℝ) hg'.ne'
  have := j1; have := j2
  set N' : S.W → ℝ := fun u => P' * S.base.N0 ε (b - 1) u Y κ with hN'
  let D : Fin S.f → TB.Pt E → TB.Pt E → ℂ → ℂ := fun v h h' c =>
    KB.gN S v ε (b + n - 1) (w'.1 v) (C.loc (S.σ v) h ++ [(n, c)]) (C.loc (S.σ v) h' ++ [(n, c)])
  have hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z) := by
    intro v z _
    have := PBB.gN_psd S hpos v ε hε (b + n - 1) (by omega) w' (Y.image fun h => C.loc (S.σ v) h ++ [(n, z)])
    exact JCx1.decay.psd_pull _ _ this Y (fun h => C.loc (S.σ v) h ++ [(n, z)])
      (fun h hh => Finset.mem_image_of_mem _ hh)
  let U : Fin S.f → TB.Pt E × ℂ → TB.Pt E × ℂ → ℂ := fun v p q =>
    KB.gN S v ε (b + n - 2) (w'.1 v) (C.loc (S.σ v) p.1 ++ [(n - 1, p.2⁻¹)]) (C.loc (S.σ v) q.1 ++ [(n - 1, q.2⁻¹)])
  have hsub : ∀ x' ∈ pairs, ∀ (t : crystallineComparison.V S.f), Good t →
      (KB.NstV S ε (b + n - 2) (n - 1) x'.1 Y κ t t).re ≤ ∑ u ∈ Wd, θ'' x'.1 u * N' u ∧
      (KB.NstV S ε (b + n - 2) (n - 1) x'.2 Y κ t t).re ≤ ∑ u ∈ Wd, θ'' x'.2 u * N' u := by
    intro x' hx' t ht
    have e : b + (n - 1) - 1 = b + n - 2 := by omega
    have h1 := (hθ'' x'.1 (hpw x' hx').1.1 (hpw x' hx').1.2.1).2 Y hY κ hκ t ht
    have h2 := (hθ'' x'.2 (hpw x' hx').2.1 (hpw x' hx').2.2.1).2 Y hY κ hκ t ht
    rw [e] at h1 h2
    have s1 : ∑ u ∈ Wd, θ'' x'.1 u * N' u =
        P' * ∑ u ∈ S.base.Wb (S.base.cnt x'.1 + (n - 1) * C.Kst), θ'' x'.1 u * S.base.N0 ε (b - 1) u Y κ := by
      rw [Finset.mul_sum, ← Finset.sum_subset (hpw x' hx').1.2.2 fun u _ hu => by
        rw [(hpr _ (hpw x' hx').1.1 (hpw x' hx').1.2.1).2.1 u hu]; ring]
      exact Finset.sum_congr rfl fun u _ => by simp only [hN']; ring
    have s2 : ∑ u ∈ Wd, θ'' x'.2 u * N' u =
        P' * ∑ u ∈ S.base.Wb (S.base.cnt x'.2 + (n - 1) * C.Kst), θ'' x'.2 u * S.base.N0 ε (b - 1) u Y κ := by
      rw [Finset.mul_sum, ← Finset.sum_subset (hpw x' hx').2.2.2 fun u _ hu => by
        rw [(hpr _ (hpw x' hx').2.1 (hpw x' hx').2.2.1).2.1 u hu]; ring]
      exact Finset.sum_congr rfl fun u _ => by simp only [hN']; ring
    exact ⟨s1 ▸ h1, s2 ▸ h2⟩
  have hF : ∀ σ ∈ crystallineComparison.dualSet La, ∀ x : crystallineComparison.V S.f, Good x → Good (x + (S.g : ℝ) • σ) →
      ‖phi Y κ U x (x + (S.g : ℝ) • σ)‖ ≤
        crystallineComparison.mL C.Kst L ((S.g : ℝ) • σ) * ∑ u ∈ Wd, q σ u * N' u := by
    intro σ _ x hx hx'
    set t : crystallineComparison.V S.f := fun v => (x v)⁻¹ with ht_def
    set t' : crystallineComparison.V S.f := fun v => ((x + (S.g : ℝ) • σ) v)⁻¹ with ht'_def
    have ht : Good t := fun v => inv_ne_zero (hx v)
    have ht' : Good t' := fun v => inv_ne_zero (hx' v)
    have ephi : phi Y κ U x (x + (S.g : ℝ) • σ) = KB.NstV S ε (b + n - 2) (n - 1) w' Y κ t t' := by
      rw [nstV_eq]; rfl
    have hlv := hLV Y κ κ κ (fun h hh => by rw [hY h hh]; omega) (blockPSD_same Y κ hκ) t t' ht ht'
      (crystallineComparison.pat L ((S.g : ℝ) • σ))
    have ediff : ∀ v, (t v)⁻¹ - (t' v)⁻¹ = -(((S.g : ℝ) • σ) v) := by
      intro v; simp only [t, t', inv_inv, Pi.add_apply]; ring
    simp only [ediff, norm_neg] at hlv
    rw [ephi]
    refine bound_mL C.Kst L hL0 _ _ _ (hlv.trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun v _ => pow_nonneg (hL0 v) _)
    show _ ≤ ∑ u ∈ Wd, (∑ x ∈ pairs, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x * ((θ'' x.1 u + θ'' x.2 u) / 2)) * N' u
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun x' hx' => ?_
    have hs := hsub x' hx'
    have e2 : ∑ u ∈ Wd, θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x' * ((θ'' x'.1 u + θ'' x'.2 u) / 2) * N' u =
        θL (crystallineComparison.pat L ((S.g : ℝ) • σ)) x' * ((∑ u ∈ Wd, θ'' x'.1 u * N' u + ∑ u ∈ Wd, θ'' x'.2 u * N' u) / 2) := by
      rw [← Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [e2]
    refine mul_le_mul_of_nonneg_left ?_ ((hθL _).1 x')
    linarith [(hs t ht).1, (hs t' ht').2]
  have hH := herglotz_germ (H := TB.Pt E) Y κ hκ D hD (fun v h hh h' hh' => (hreg v h hh h' hh').1)
    (fun v h hh h' hh' => (hreg v h hh h' hh').2) (S.g : ℝ) hg' (fun _ => KB.dlB S b n)
    (fun _ => dlB_pos S hg b n) U Pq Qq
    (fun v σ h h' => KB.hatB S v ε b n (w'.1 v) σ (C.loc (S.σ v) h) (C.loc (S.σ v) h')) hGD
    (fun _ _ _ _ => rfl) La Lm hLm
    (fun σ : crystallineComparison.V S.f => crystallineComparison.mL C.Kst L ((S.g : ℝ) • σ) * ∑ u ∈ Wd, q σ u * N' u) (hmix N').1 hF z₀ Ss hS
  rw [(hmix N').2] at hH
  have hN : ∑ z ∈ Ss, Nz Y κ D z = ∑ z ∈ Ss, (KB.NstV S ε (b + n - 1) n w' Y κ z z).re :=
    Finset.sum_congr rfl fun z hz => by
      simp only [Nz, if_pos (hgood z hz)]
      rw [nstV_eq]
      rfl
  rw [hN] at hH
  refine hH.trans (le_of_eq ?_)
  have e3 : ∑ u ∈ Wd, θn u * N' u = P' * ∑ u ∈ Wd, θn u * S.base.N0 ε (b - 1) u Y κ := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u _ => by simp only [hN']; ring
  rw [e3]
  ring

end

end Formalism.FourierDecayAlt.P.PBC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.UnfoldIint
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem l_le_I {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp]
    {σ : Mx k r → (H →L[ℂ] H)} {w0 : H} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    {l : H → Wp} (hbe : ∀ x ∈ DDsp σ w0, ∀ y ∈ DDsp σ w0,
        be z c π σ μW μN x y = (innerSL ℂ (l y)).smulRight (l x))
    {v : H} (hv : v ∈ DDsp σ w0) (hlv : l v ≠ 0) (hw0DD : w0 ∈ DDsp σ w0)
    {e1 : Mx k r → ℂ} (hee1 : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), e1 g = ⟪v, σ g w0⟫_ℂ)
    {zz : Formalism.QuantumDeterminants.Mt k r} (hz : Matrix.of zz ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    ‖l (σ (Matrix.of zz) w0)‖ₑ ≤ (‖((‖l v‖ ^ 2 : ℝ) : ℂ)⁻¹‖ₑ * ‖l v‖ₑ) *
      ∫⁻ p, (fun m : Formalism.QuantumDeterminants.Mt k r => ‖e1 (Matrix.of m)‖ₑ)
        (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of zz) i j) ∂(μW.prod μN) := by
  have b1 := l_enorm_le (c := c) hds hT hπ hW hN hbe hv hlv hw0DD hz
  refine b1.trans (le_of_eq ?_)
  congr 1
  apply lintegral_congr_ae
  filter_upwards [prod_ae hW hN] with p hp
  show ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of zz) w0⟫_ℂ‖ₑ =
    ‖e1 (Matrix.of p.1 * Matrix.of p.2 * Matrix.of zz)‖ₑ
  rw [hee1 _ (DDSmoothness.uh_mul (DDSmoothness.uh_mul hp.1.1 hp.2.1) hz)]

theorem e_weight {e : Mx k r → ℂ} {C a b : ℝ}
    (hb : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖e y‖ ≤ C * B.gN y ^ (-a))
    {x : Mx k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hpos : 0 < B.gN x) :
    ‖e x‖ₑ * ENNReal.ofReal (B.gN x ^ b) ≤ ENNReal.ofReal |C| * ‖B.gN x ^ (-(a - b))‖ₑ := by
  have h1 := hb x hx
  have h2 : ‖e x‖ * B.gN x ^ b ≤ |C| * B.gN x ^ (-(a - b)) := by
    have e2 : B.gN x ^ (-(a - b)) = B.gN x ^ (-a) * B.gN x ^ b := by
      rw [← Real.rpow_add hpos]
      ring_nf
    rw [e2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hpos.le _)))
      (Real.rpow_nonneg hpos.le _)
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _),
    ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h2

def Iint (A : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (μ : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (z : Formalism.QuantumDeterminants.Mt k r) :
    ℝ≥0∞ :=
  ∫⁻ p, A (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j) ∂μ

def Aext (e : Mx k r → ℂ) (m : Formalism.QuantumDeterminants.Mt k r) : ℝ≥0∞ := ‖e (Matrix.of m)‖ₑ

theorem Aext_meas {e : Mx k r → ℂ} (he : Continuous e) : Measurable (Aext e) := by
  unfold Aext
  exact (Continuous.enorm (he.comp (show Continuous (fun m : Formalism.QuantumDeterminants.Mt k r => Matrix.of m) from continuous_id))).measurable

theorem Iint_meas {A : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hA : Measurable A)
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) [SFinite μ] : Measurable (Iint A μ) := by
  unfold Iint
  refine Measurable.lintegral_prod_right' (f := fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
    A (fun i j => (Matrix.of q.2.1 * Matrix.of q.2.2 * Matrix.of q.1) i j)) ?_
  refine hA.comp (Continuous.measurable ?_)
  exact ((continuous_snd.fst.matrix_mul continuous_snd.snd).matrix_mul continuous_fst)

theorem unfold_Iint {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} [SigmaFinite μW] [SigmaFinite μN]
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG (muSof μW μN) νq)
    {A Ψ : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞} (hA : Measurable A) (hΨ : Measurable Ψ)
    (hinv : ∀ᵐ z ∂νq, ∀ᵐ p ∂(μW.prod μN),
      Ψ (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j) = Ψ z) :
    ∫⁻ z, Iint A (μW.prod μN) z * Ψ z ∂νq = ∫⁻ x, A x * Ψ x ∂μG := by
  have hcont : ∀ z : Formalism.QuantumDeterminants.Mt k r,
      Continuous (fun s : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of s * Matrix.of z) i j : Formalism.QuantumDeterminants.Mt k r)) :=
    fun z => Continuous.matrix_mul continuous_id continuous_const
  have hg : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) :=
    (show Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) from
      Continuous.matrix_mul continuous_fst continuous_snd).measurable
  rw [hq (fun x => A x * Ψ x) (hA.mul hΨ)]
  refine lintegral_congr_ae ?_
  filter_upwards [hinv] with z hz
  unfold Iint Formalism.FourierDecayAlt.ThreeDimData.muSof
  rw [lintegral_map (f := fun s : Formalism.QuantumDeterminants.Mt k r => A (fun i j => (Matrix.of s * Matrix.of z) i j) *
      Ψ (fun i j => (Matrix.of s * Matrix.of z) i j))
    (by exact (hA.comp (hcont z).measurable).mul (hΨ.comp (hcont z).measurable)) hg]
  have hmA : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      A (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j)) :=
    hA.comp ((show Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2 * Matrix.of z) i j : Formalism.QuantumDeterminants.Mt k r)) from
      Continuous.matrix_mul (Continuous.matrix_mul continuous_fst continuous_snd) continuous_const).measurable)
  rw [← lintegral_mul_const _ hmA]
  refine lintegral_congr_ae ?_
  filter_upwards [hz] with p hp
  exact congrArg _ hp.symm

theorem pull2 {νq νq' : Measure (Formalism.QuantumDeterminants.Mt k r)} (F G : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
    (M : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) {K : ℝ≥0∞} (hK : K ≠ ⊤)
    (hm : ∀ z, Measurable fun z' => G z' * M z z') :
    ∫⁻ z, ∫⁻ z', K * (F z * (G z' * M z z')) ∂νq' ∂νq = K * ∫⁻ z, F z * ∫⁻ z', G z' * M z z' ∂νq' ∂νq := by
  have h1 : ∀ z, ∫⁻ z', K * (F z * (G z' * M z z')) ∂νq' = K * (F z * ∫⁻ z', G z' * M z z' ∂νq') := by
    intro z
    have e1 : (fun z' => K * (F z * (G z' * M z z'))) = fun z' => (K * F z) * (G z' * M z z') := by
      funext z'
      ring
    rw [e1, lintegral_const_mul _ (hm z), mul_assoc]
  simp_rw [h1]
  exact lintegral_const_mul' K _ hK

theorem final2 {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (Fx : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (hF : Measurable Fx)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    ∫⁻ x, ∫⁻ y, c * (Fx x * Fx y) ∂μG ∂μG = c * ((∫⁻ x, Fx x ∂μG) * ∫⁻ y, Fx y ∂μG) := by
  have h1 : ∀ x, ∫⁻ y, c * (Fx x * Fx y) ∂μG = (c * Fx x) * ∫⁻ y, Fx y ∂μG := by
    intro x
    simp_rw [← mul_assoc]
    exact lintegral_const_mul _ hF
  simp_rw [h1]
  rw [lintegral_mul_const _ (hF.const_mul c), lintegral_const_mul _ hF, mul_assoc]

end Formalism.FourierDecayAlt.P.S3dx4
end
end

