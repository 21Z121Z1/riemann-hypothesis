import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndTauSLeHalf
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Formalism.LatticeRigidity.HeightMinimum.Bundle0001
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CuspidalRangeOfReproUnipotent
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0008
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0007

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CndHsLeDist
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

abbrev cnd_V (n : ℕ) : Type := EuclideanSpace ℂ (Fin n × Fin n)

def cnd_vec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : cnd_V n := WithLp.toLp 2 fun p => M p.1 p.2

theorem cnd_norm_vec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ‖cnd_vec M‖ = Real.sqrt (Formalism.REAL.hs M) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  unfold Formalism.REAL.hs
  rw [Fintype.sum_prod_type]
  rfl

theorem cnd_vec_sub {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) : cnd_vec M - cnd_vec N = cnd_vec (M - N) := rfl

theorem cnd_finrank (n : ℕ) : Module.finrank ℝ (cnd_V n) = 2 * n ^ 2 := by
  have e : cnd_V n ≃ₗ[ℝ] (Fin n × Fin n → ℂ) := WithLp.linearEquiv 2 ℝ _
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex]
  ring

theorem cnd_hs_le_dist {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) :
    Real.sqrt (Formalism.REAL.hs (umat g)) ≤ Real.sqrt (n : ℝ) * Real.exp (cartanDistance ε g) := by
  have hgU : Formalism.REAL.inUJ ε (umat g) := g.2
  obtain ⟨k₀, X₀, hk, hX, hg⟩ := (Formalism.REAL.polar_decomposition_holds n ε).1 _ hgU
  have hset : {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
      umat g = k * NormedSpace.exp X ∧ t = Real.sqrt (Formalism.REAL.hs X)} = {Real.sqrt (Formalism.REAL.hs X₀)} := by
    ext t
    constructor
    · rintro ⟨k, X, hk', hX', hg', rfl⟩
      have := ((Formalism.REAL.polar_decomposition_holds n ε).2.1 k k₀ X X₀ hk' hk hX' hX (hg'.symm.trans hg)).2
      rw [this]
      rfl
    · intro ht
      exact ⟨k₀, X₀, hk, hX, hg, ht⟩
  have hd : cartanDistance ε g = Real.sqrt (Formalism.REAL.hs X₀) := by
    unfold cartanDistance
    rw [hset, csInf_singleton]
  have h1 := hilbert_schmidt_polar_bound k₀ X₀ hk.1 (hermitian_of_mem_p ε X₀ hX).1
  rw [hd, hg]
  calc Real.sqrt (Formalism.REAL.hs (k₀ * NormedSpace.exp X₀))
      ≤ Real.sqrt ((n : ℝ) * Real.exp (Real.sqrt (Formalism.REAL.hs X₀)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt (n : ℝ) * Real.exp (Real.sqrt (Formalism.REAL.hs X₀)) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]

def cnd_pt (X : CData) (x : X.I.GA) (γ : X.I.GFset) (v : InfinitePlace X.I.F) : Matrix (Fin X.I.n) (Fin X.I.n) ℂ :=
  umat ((x⁻¹ * (γ : X.I.GA) * x).1 v)

def CSize.SepStep {X : CData} (S : CSize X) : Prop :=
  ∀ (x : X.I.GA) (γ γ' : X.I.GFset), γ ≠ γ' → X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0 → X.φ (x⁻¹ * (γ' : X.I.GA) * x) ≠ 0 →
    S.tau1 x ^ 2 ≤ (∏ v, Real.sqrt (Formalism.REAL.hs (cnd_pt X x γ v - cnd_pt X x γ' v))) ^
      ((1 : ℝ) / (Fintype.card (InfinitePlace X.I.F) : ℝ))

theorem cnd_pack {X : CData} (S : CSize X) (hn : 1 ≤ X.I.n) (hst : S.Strata) (hsep : S.SepStep) : S.PackCount := by
  classical
  intro x r hr T hT
  have hτ := (hst.2.2.2.2.2.1 x).1
  have hτ2 : 0 < S.tau1 x ^ 2 := by positivity
  set p : X.I.GFset → (∀ _ : InfinitePlace X.I.F, cnd_V X.I.n) := fun γ v => cnd_vec (cnd_pt X x γ v) with hp
  have hsepP : ∀ γ ∈ T, ∀ γ' ∈ T, γ ≠ γ' → S.tau1 x ^ 2 ≤
      (∏ v, ‖p γ v - p γ' v‖) ^ ((1 : ℝ) / (Fintype.card (InfinitePlace X.I.F) : ℝ)) := by
    intro γ hγ γ' hγ' hne
    have := hsep x γ γ' hne (hT γ hγ).1 (hT γ' hγ').1
    simpa only [hp, cnd_vec_sub, cnd_norm_vec] using this
  have hcard : (0 : ℝ) < (Fintype.card (InfinitePlace X.I.F) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hinj : Set.InjOn p (T : Set X.I.GFset) := by
    intro γ hγ γ' hγ' h
    by_contra hne
    have h1 := hsepP γ hγ γ' hγ' hne
    rw [h] at h1
    have hz : (∏ v : InfinitePlace X.I.F, ‖p γ' v - p γ' v‖) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary _)) (by rw [sub_self, norm_zero])
    rw [hz, Real.zero_rpow (by positivity)] at h1
    linarith
  have hs : 0 < Real.sqrt (X.I.n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have h := Formalism.SA.P.packing_count_geometric_mean (InfinitePlace X.I.F) (fun _ => cnd_V X.I.n) (2 * X.I.n ^ 2)
    (fun _ => cnd_finrank X.I.n) (T.image p) (S.tau1 x ^ 2) (fun v => Real.sqrt (X.I.n : ℝ) * Real.exp (r v)) hτ2
    (fun v => mul_pos hs (Real.exp_pos _))
    (by
      intro a ha b hb hab
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.1 hb
      exact hsepP γ hγ γ' hγ' (fun e => hab (by rw [e])))
    (by
      intro a ha v
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 ha
      show ‖cnd_vec (cnd_pt X x γ v)‖ ≤ _
      rw [cnd_norm_vec]
      refine le_trans (cnd_hs_le_dist (X.I.ε v) _) ?_
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ((hT γ hγ).2 v)) hs.le)
  rw [Finset.card_image_of_injOn hinj] at h
  exact h

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CuspidalRangeOfReducedFacts
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem cu_countGF (X : CData) : cu.CountGF X := by
  have h : Countable (rr_GF X.I) := inferInstance
  exact (Set.countable_coe_iff (s := X.I.GFset)).1 h

theorem cu_measMul (X : CData) (hH : X.μf.IsHaarMeasure) : cu.MeasMul X := by
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  exact measurable_fst.mul measurable_snd

theorem cu_extInv (X : CData) (hd : RegData X) : cu.ExtInv X := by
  classical
  intro T _ _ Fv _
  obtain ⟨hH, hF, -⟩ := hd
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have hfd := rr_FD_of X.I X.μf X.fund hF
  refine ⟨fun z => if z ∈ rr_N (rr_GF X.I) X.fund then 0 else X.I.ext Fv z, fun γ hγ y => ?_, ?_⟩
  · by_cases hy : y ∈ rr_N (rr_GF X.I) X.fund
    · have h2 : γ * y ∈ rr_N (rr_GF X.I) X.fund := by
        by_contra hcon
        have := rr_N_smul (Γ := rr_GF X.I) (D := X.fund) ((rr_GF X.I).inv_mem hγ) hcon
        rw [inv_mul_cancel_left] at this
        exact this hy
      simp only [hy, h2, if_true]
    · have h2 : γ * y ∉ rr_N (rr_GF X.I) X.fund := rr_N_smul (Γ := rr_GF X.I) hγ hy
      simp only [hy, h2, if_false]
      show (Fv : X.I.GA → ℂ) (rr_rep X.I.GFset X.fund (γ * y)) = (Fv : X.I.GA → ℂ) (rr_rep X.I.GFset X.fund y)
      rw [show rr_rep X.I.GFset X.fund (γ * y) = rr_rep X.I.GFset X.fund y from rr_rep_smul hfd hγ hy]
  · have hN : cu_mu X (rr_N (rr_GF X.I) X.fund) = 0 := rr_N_null hfd
    filter_upwards [compl_mem_ae_iff.2 hN] with z hz
    have hz' : z ∉ rr_N (rr_GF X.I) X.fund := hz
    simp only [hz', if_false]

theorem cu_extMeas (X : CData) (hd : RegData X) : cu.ExtMeas X := by
  intro T _ _ Fv _
  obtain ⟨hH, hF, -⟩ := hd
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have hfd := rr_FD_of X.I X.μf X.fund hF
  obtain ⟨r, hrm, hr⟩ := rr_exists_meas_rep hfd
  have hN : cu_mu X (rr_N (rr_GF X.I) X.fund) = 0 := rr_N_null hfd
  refine (((Lp.stronglyMeasurable Fv).comp_measurable hrm).aestronglyMeasurable).congr ?_
  filter_upwards [compl_mem_ae_iff.2 hN] with z hz
  obtain ⟨γ, h1, h2, h3⟩ := hr z
  show (Fv : X.I.GA → ℂ) (r z) = (Fv : X.I.GA → ℂ) (rr_rep X.I.GFset X.fund z)
  rw [h2, show rr_rep X.I.GFset X.fund z = γ * z from rr_rep_eq hfd hz h1 h3]

theorem cu_reproAE (X : CData) (hd : RegData X) (hu : UnimodA X) (hφm : Measurable X.φ) : cu.ReproAE X := by
  intro T hT hP Fv hFv
  obtain ⟨hH, hF, hR⟩ := hd
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have hL : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have : (X.I.muA X.μf).IsMulRightInvariant := hu
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  have hfd := rr_FD_of X.I X.μf X.fund hF
  obtain ⟨r, hrm, hr⟩ := rr_exists_meas_rep hfd
  have hTF : T Fv = Fv := by
    obtain ⟨u, rfl⟩ := hFv
    have h2 : T * T = T := hP.isIdempotentElem
    exact congrArg (fun S : X.L2 →L[ℂ] X.L2 => S u) h2
  have h1 := rrkb_step1 hfd hφm hrm hr (rr_IsReg_of X.I X.μf X.fund X.R hR) T hT.1 hT.2 Fv
  rw [hTF] at h1
  have hZ : X.μ {x | ¬ (Fv : X.I.GA → ℂ) x = ∫ g, X.φ g * (Fv : X.I.GA → ℂ) (r (x * g)) ∂(X.I.muA X.μf)} = 0 :=
    ae_iff.1 h1
  have hN : cu_mu X (rr_N (rr_GF X.I) X.fund) = 0 := rr_N_null hfd
  filter_upwards [cu_rep_avoid X hL (cu_countGF X) hF _ hZ] with z hz
  have hz' : (Fv : X.I.GA → ℂ) (X.I.rep X.fund z) =
      ∫ g, X.φ g * (Fv : X.I.GA → ℂ) (r (X.I.rep X.fund z * g)) ∂(X.I.muA X.μf) := by
    by_contra hcon
    exact hz hcon
  show (Fv : X.I.GA → ℂ) (X.I.rep X.fund z) = _
  rw [hz']
  obtain ⟨γ, g1, g2, -⟩ := rr_rep_spec hfd z
  have hNz : cu_mu X ((fun g => z * g) ⁻¹' rr_N (rr_GF X.I) X.fund) = 0 := by
    rw [measure_preimage_mul]; exact hN
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.2 hNz] with g hg
  have hg' : z * g ∉ rr_N (rr_GF X.I) X.fund := hg
  have e1 : X.I.rep X.fund z = γ * z := g2
  obtain ⟨γ', k1, k2, k3⟩ := hr (X.I.rep X.fund z * g)
  have e2 : r (X.I.rep X.fund z * g) = rr_rep X.I.GFset X.fund (z * g) := by
    rw [k2, e1]
    have k3' : (γ' * γ) * (z * g) ∈ X.fund := by
      rw [e1] at k3
      simpa [mul_assoc] using k3
    rw [show rr_rep X.I.GFset X.fund (z * g) = (γ' * γ) * (z * g) from
      rr_rep_eq hfd hg' ((rr_GF X.I).mul_mem k1 g1) k3']
    simp only [mul_assoc]
  rw [e2, mul_comm]
  rfl

def cu.Core (X : CData) : Prop :=
  cu.UnipFine X ∧ cu.HaarGrowth X ∧ cu.SizeStep X ∧ X.KernelDiag ∧ UnimodA X

theorem cu_fine_of_core (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (h : cu.Core X) : cu.Fine X := by
  obtain ⟨sU, sH, sS, sK, sA⟩ := h
  have hd := RegData_of_HypB X hX
  exact ⟨sU, sH, sS, sK, cu_reproAE X hd sA (rrk_phi_meas X hX), cu_extInv X hd, cu_extMeas X hd, cu_measMul X hd.1,
    cu_countGF X⟩

def cu_StepsCore (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ X : CData, X.HypB n₀ A → X.GapAboveThreeHalvesPower → X.GapAboveSquareRootThreshold C → cu.Core X

theorem cuspidal_range_of_reduced_facts (X : CData) (D : Formalism.BasicNotions.D7) (hdec : DiscreteSeriesDecayBound D) {n₀ : ℕ} {A C : ℝ} (hn₀ : 1 ≤ n₀)
    (hC : 46 ≤ C) (hX : X.HypB n₀ A) (h1 : X.GapAboveThreeHalvesPower) (h2 : X.GapAboveSquareRootThreshold C) (hE : X.LowProj) (hF : cu.FinStep X)
    (hS : cu.Core X) : X.CuspStep :=
  cuspidal_range_of_fine_facts X D hdec hn₀ hC hX h1 h2 hE hF (cu_fine_of_core X hX hS)

end Formalism.MainNotions.LeviCoordinates
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.KernelDiagonalOfAbsoluteConvergence
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set TopologicalSpace
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def AbsKernelSquareIntegrable (X : CData) : Prop :=
  ∀ᵐ x ∂X.μ, ∫⁻ y, (∑' γ : X.I.GFset, ‖X.φ (x⁻¹ * (γ : X.I.GA) * y)‖ₑ) ^ 2 ∂X.μ ≠ ∞

def PhiIdem (X : CData) : Prop :=
  Measurable X.φ ∧ (∀ z, X.φ z⁻¹ = star (X.φ z)) ∧ ∀ z, ∫ g, X.φ g * X.φ (g⁻¹ * z) ∂(X.I.muA X.μf) = X.φ z

theorem rrk_steps_of_abs (X : CData) (hd : RegData X) (hu : UnimodA X) (hφ : PhiIdem X) (hK : AbsKernelSquareIntegrable X) :
    KernelL2RowsColumns X ∧ KerUnfold X ∧ KerIdem X := by
  obtain ⟨hH, hF, hR⟩ := hd
  have := hH
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have : (X.I.muA X.μf).IsMulRightInvariant := hu
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  have h1 := rr_FD_of X.I X.μf X.fund hF
  have h2 := rr_IsReg_of X.I X.μf X.fund X.R hR
  have hK' : ∀ᵐ x ∂(X.I.muA X.μf).restrict X.fund,
      ∫⁻ y in X.fund, (rrk_Kab (rr_GF X.I) X.φ x y) ^ 2 ∂(X.I.muA X.μf) ≠ ∞ := hK
  refine ⟨?_, ?_, ?_⟩
  · unfold KernelL2RowsColumns CData.μ
    filter_upwards [hK'] with x hx
    exact (rrk_idem h1 hφ.1 hφ.2.1 hφ.2.2 x hx).2.2
  · intro T hT f
    exact rrk_unfold h1 hφ.1 h2 T hT.1 hT.2 hK' f
  · unfold KerIdem CData.μ
    filter_upwards [hK'] with x hx
    have := rrk_idem h1 hφ.1 hφ.2.1 hφ.2.2 x hx
    exact ⟨this.1, this.2.1⟩

theorem kernel_diagonal_of_absolute_convergence (X : CData) (hd : RegData X) (hu : UnimodA X) (hφ : PhiIdem X) (hK : AbsKernelSquareIntegrable X) :
    X.KernelDiag := by
  obtain ⟨a, b, c⟩ := rrk_steps_of_abs X hd hu hφ hK
  exact kernel_diagonal_of_L2_unfold_idempotent X hd.1 a b c

theorem PhiIdem_of (D : Formalism.BasicNotions.D7) (hloc : LocalProjectorRealPlace D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (h1 : X.GapAboveThreeHalvesPower) :
    PhiIdem X :=
  ⟨rrk_phi_meas X hX, rrk_phi_star D hloc X hX h1, rrk_phi_idem D hloc X hX h1⟩

theorem kernel_diagonal_of_local_projector_of_abs_kernel_L2 (D : Formalism.BasicNotions.D7) (hloc : LocalProjectorRealPlace D) (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    (h1 : X.GapAboveThreeHalvesPower) (hu : UnimodA X) (hK : AbsKernelSquareIntegrable X) : X.KernelDiag :=
  kernel_diagonal_of_absolute_convergence X (RegData_of_HypB X hX) hu (PhiIdem_of D hloc X hX h1) hK

end Formalism.MainNotions.LeviCoordinates

end
end

