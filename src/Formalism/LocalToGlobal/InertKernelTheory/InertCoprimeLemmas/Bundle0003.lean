import Formalism.LocalToGlobal.InertKernelTheory.Bundle0010
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0008
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PowerSeriesEmbedding
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntTens
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMRead
import Formalism.LocalToGlobal.InertKernelTheory.K2OfAgreements
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMCoord
section
noncomputable section

namespace Formalism.L2.KerInert

namespace MMCoord

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def inclCL (D : D7) : (D.what₂.Tau → ℂ) →L[ℂ] VC D 1 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v τ _ _ => v τ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem inclCL_apply (v : D.what₂.Tau → ℂ) : inclCL D v = fun τ _ _ => v τ := rfl

theorem translate_theta_coordinates (B : Base D cc δ) (s₁ v : D.what₂.Tau → ℂ) :
    U D B.tor (fun τ _ _ => s₁ τ) (B.thZero 1 1) (fun τ _ _ => v τ) =
      Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) s₁ B.thMM v := by
  have hA : Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L := B.areaOK
  have hT : B.tor.abelian₂ = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ := rfl
  simp only [U, Formalism.MainNotions.TaylorLogMetric.Hf, Base.thZero, tensPow, Formalism.L2.Th1.H.opU, Formalism.L2.Th1.H.matH, LinearMap.mk₂'ₛₗ_apply, hOne,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.univ_unique, Finset.sum_singleton,
    Finset.prod_singleton, hT, hA]
  congr 1
  have e1 : ∀ w : D.what₂.Tau → ℂ, ∑ x, w x * ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ)⁻¹ * (starRingEnd ℂ) (s₁ x) =
      (∑ x, w x * (starRingEnd ℂ) (s₁ x)) / ((Formalism.L2.Th1.F.area B.L : ℝ) : ℂ) := fun w => by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [e1, e1]

theorem u_incl (B : Base D cc δ) (s : VC D 1 1) (v : D.what₂.Tau → ℂ) :
    U D B.tor s (B.thZero 1 1) (inclCL D v) =
      Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ 0 0) B.thMM v := by
  have hs : s = fun τ _ _ => s τ 0 0 := by
    funext τ i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  have h := translate_theta_coordinates B (fun τ => s τ 0 0) v
  rw [← hs] at h
  exact h

def projM (D : D7) : Matrix D.what₂.Tau (D.what₂.Tau × Fin 1 × Fin 1) ℂ :=
  Matrix.of fun τ k => if k = (τ, 0, 0) then 1 else 0

theorem projM_mulVec (w : D.what₂.Tau × Fin 1 × Fin 1 → ℂ) : (projM D).mulVec w = fun τ => w (τ, 0, 0) := by
  funext τ
  simp [projM, Matrix.mulVec, dotProduct, ite_mul, Finset.sum_ite_eq']

theorem flat_eq (w : D.what₂.Tau × Fin 1 × Fin 1 → ℂ) :
    Formalism.L2.AlgTh.flat D.what₂.Tau 1 1 w = inclCL D ((projM D).mulVec w) := by
  rw [projM_mulVec, inclCL_apply]
  funext τ i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  rfl

theorem linSubst_projM (T : MvPowerSeries D.what₂.Tau ℂ) :
    Formalism.L2.Th1.H.linSubst (projM D) T =
      MvPowerSeries.subst (fun τ : D.what₂.Tau =>
        (MvPowerSeries.X (τ, 0, 0) : MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ)) T := by
  unfold Formalism.L2.Th1.H.linSubst
  congr 1
  funext τ
  simp [projM, apply_ite MvPowerSeries.C, ite_mul, Finset.sum_ite_eq']

theorem map_subst_liftT {p : ℕ} [Fact p.Prime] (h : ℂ →+* ℂ_[p]) (T : MvPowerSeries D.what₂.Tau ℂ) :
    MvPowerSeries.map h (MvPowerSeries.subst (fun τ : D.what₂.Tau =>
        (MvPowerSeries.X (τ, 0, 0) : MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ)) T) =
      liftT D (MvPowerSeries.map h T) := by
  have ha : MvPowerSeries.HasSubst (fun τ : D.what₂.Tau =>
      (MvPowerSeries.X (τ, 0, 0) : MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ)) :=
    MvPowerSeries.HasSubst.X_comp (fun τ : D.what₂.Tau => ((τ, 0, 0) : D.what₂.Tau × Fin 1 × Fin 1))
  rw [MvPowerSeries.map_subst ha]
  unfold liftT
  congr 1
  funext τ
  simp [MvPowerSeries.map_X]

end MMCoord

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical MMCoord

theorem coordinates_one_theta_algebraic : CoordTieA := by
  intro D cc δ B _ _ p _ lam ι hι s
  refine ⟨fun hG => ?_, fun hs => ?_⟩
  · have hgG : Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ 0 0) B.thMM =
        fun v => U D B.tor s (B.thZero 1 1) (inclCL D v) := funext fun v => (u_incl B s v).symm
    have hg0 : AnalyticAt ℂ
        (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ 0 0) B.thMM) 0 := by
      rw [hgG]
      exact (hG.1 _ trivial).comp ((inclCL D).analyticAt 0)
    have hfun : (fun z => U D B.tor s (B.thZero 1 1) (Formalism.L2.AlgTh.flat D.what₂.Tau 1 1 z)) =
        fun w => Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ 0 0) B.thMM
          ((projM D).mulVec w) := by
      funext w
      rw [flat_eq, hgG]
    rw [power_series_embedding D 1 1 p lam ι hι _ hG.2, IntTens.taylorSer_eq_taylorMv _ hG.1, hfun,
      Formalism.L2.Th1.H.taylorMvComp _ _ (projM D) _ hg0, linSubst_projM]
    exact map_subst_liftT ι.toRingHom _
  · obtain ⟨n, hn, hcop, hmem⟩ := hs
    have h0 := B.lat0OK 1 1
    unfold Base.Lat0OK at h0
    rw [h0] at hmem
    refine ⟨n, hn, fun hd => ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hcop.symm) hd, ?_⟩
    have h00 : (fun τ => (n • s) τ 0 0) ∈ B.lamM := hmem 0 0
    convert h00 using 1
    funext τ
    simp [nsmul_eq_mul]

theorem coordTie_of (h : CoordTieA) (hz : AlgZero) : CoordTie := by
  intro D cc δ B hcc hδ p _ hp hin lam ι hι s hs
  obtain ⟨h1, h2⟩ := h D cc δ B hcc hδ p lam ι hι s
  exact ⟨h1 (hz D cc δ B hcc hδ p hp hin 1 1 s hs), h2 hs⟩

theorem coordTie_of_algZero (hz : AlgZero) : CoordTie := coordTie_of coordinates_one_theta_algebraic hz

end Formalism.L2.KerInert
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMReadS
section
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

open ParameterChangeLemmas IntegralOrthonormalChange

theorem change_of_parameters_const_scale : ReadChangeS := by
  intro D p _ hp lam Λ C wq ph h Uu κ hph0 h0 hhi h1 hlog hUu hexp r v e F hInt
  obtain ⟨g, g0, gI, hg⟩ := exists_inv h h0 hhi h1
  have hp2 : p ≠ 2 := by omega
  obtain ⟨S, hSi⟩ : ∃ S : Fin r → MvPowerSeries D.what₂.Tau ℂ_[p],
      ∀ i, S i = PowerSeries.subst (MvPowerSeries.X (e.symm i) : MvPowerSeries D.what₂.Tau ℂ_[p]) h :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨S', hS'i⟩ : ∃ S' : D.what₂.Tau → MvPowerSeries (Fin r) ℂ_[p],
      ∀ j, S' j = PowerSeries.subst (MvPowerSeries.X (e j) : MvPowerSeries (Fin r) ℂ_[p]) g :=
    ⟨_, fun _ => rfl⟩
  have hS0 : ∀ i, MvPowerSeries.constantCoeff (S i) = 0 := fun i => by rw [hSi]; exact constantCoeff_inVar_eq_zero _ h h0
  have hS'0 : ∀ j, MvPowerSeries.constantCoeff (S' j) = 0 := fun j => by rw [hS'i]; exact constantCoeff_inVar_eq_zero _ g g0
  have hSs : MvPowerSeries.HasSubst S := MvPowerSeries.hasSubst_of_constantCoeff_zero hS0
  have hS's : MvPowerSeries.HasSubst S' := MvPowerSeries.hasSubst_of_constantCoeff_zero hS'0
  have hh : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hgs : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' g0
  have hl0 := flog_constantCoeff (C • wModel lam Λ) wq

  have hA : MvPowerSeries.subst S (atLogV D lam Λ C wq v (liftT D F)) =
      ReadTh1 p (fun τ j => κ * v (e j) (τ, 0, 0)) F := by
    have hXfl : ∀ i : Fin r, MvPowerSeries.constantCoeff (PowerSeries.subst
        (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) = 0 :=
      fun i => constantCoeff_inVar_eq_zero i _ hl0
    have hΦ : MvPowerSeries.HasSubst (fun k : D.what₂.Tau × Fin 1 × Fin 1 =>
        ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * v i k) *
          PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro k
      simp [map_sum, hXfl]
    have hΦ' : MvPowerSeries.HasSubst (fun τ : D.what₂.Tau =>
        ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * v i (τ, 0, 0)) *
          PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro k
      simp [map_sum, hXfl]
    have hL : MvPowerSeries.HasSubst (fun τ : D.what₂.Tau =>
        (MvPowerSeries.X (τ, 0, 0) : MvPowerSeries (D.what₂.Tau × Fin 1 × Fin 1) ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun τ => MvPowerSeries.constantCoeff_X _)
    unfold atLogV liftT ReadTh1
    try dsimp only
    rw [MvPowerSeries.subst_comp_subst_apply hL hΦ]
    simp only [MvPowerSeries.subst_X hΦ]
    rw [MvPowerSeries.subst_comp_subst_apply hΦ' hSs]
    congr 1
    funext τ
    rw [← MvPowerSeries.coe_substAlgHom hSs, map_sum]
    simp only [map_mul, AlgHom.commutes, MvPowerSeries.coe_substAlgHom, subst_single_var S hSs]
    refine (Fintype.sum_equiv e _ _ fun j => ?_).symm
    rw [hSi, e.symm_apply_apply, ← PowerSeries.subst_comp_subst_apply hh (PowerSeries.HasSubst.X j)]
    unfold Formalism.InvariantFactorPaths.G7.at1
    have key := congrArg (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p])) hlog
    rw [PowerSeries.subst_mul (PowerSeries.HasSubst.X j), PowerSeries.subst_mul (PowerSeries.HasSubst.X j),
      PowerSeries.subst_C, PowerSeries.subst_C] at key
    have hid : ∀ x : ℂ_[p], algebraMap ℂ_[p] ℂ_[p] x = x := fun _ => rfl
    simp only [MvPowerSeries.algebraMap_apply, hid] at key ⊢
    first
      | linear_combination (MvPowerSeries.C (v (e j) (τ, 0, 0)) : MvPowerSeries D.what₂.Tau ℂ_[p]) * key
      | linear_combination (-(MvPowerSeries.C (v (e j) (τ, 0, 0)) : MvPowerSeries D.what₂.Tau ℂ_[p])) * key

  have hB : MvPowerSeries.subst S (ePh lam Λ C wq r) =
      (∏ j, PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p]) Uu) *
        Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries D.what₂.Tau ℂ_[p]) := by
    have hfac : ∀ i : Fin r, MvPowerSeries.subst S
        (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (ePhi1 lam Λ C wq))⁻¹ =
        PowerSeries.subst (MvPowerSeries.X (e.symm i) : MvPowerSeries D.what₂.Tau ℂ_[p])
          (Uu * (Formalism.DworkPowerSeriesWeights.mvExp ph : PowerSeries ℂ_[p])) := by
      intro i
      rw [← subst_inv _ (MvPowerSeries.constantCoeff_X i) (ePhi1 lam Λ C wq), subst_single_var S hSs, hSi,
        ← PowerSeries.subst_comp_subst_apply hh (PowerSeries.HasSubst.X _), hexp]
    unfold ePh
    rw [if_neg hp2, ← MvPowerSeries.coe_substAlgHom hSs, map_prod]
    simp only [MvPowerSeries.coe_substAlgHom, hfac]
    rw [Fintype.prod_equiv e.symm
      (fun i => PowerSeries.subst (MvPowerSeries.X (e.symm i) : MvPowerSeries D.what₂.Tau ℂ_[p])
        (Uu * (Formalism.DworkPowerSeriesWeights.mvExp ph : PowerSeries ℂ_[p])))
      (fun j => PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p])
        (Uu * (Formalism.DworkPowerSeriesWeights.mvExp ph : PowerSeries ℂ_[p]))) (fun _ => rfl)]
    simp only [PowerSeries.subst_mul (PowerSeries.HasSubst.X _)]
    rw [Finset.prod_mul_distrib]
    congr 1
    have hph : ∀ j : D.what₂.Tau, MvPowerSeries.constantCoeff
        (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p]) ph) = 0 :=
      fun j => constantCoeff_inVar_eq_zero j ph hph0
    change _ = Formalism.L2.Th1.C.mvExp (∑ j, PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p]) ph)
    rw [Formalism.L2.Th1.C.mvExp_sum _ _ (fun j _ => hph j)]
    refine Finset.prod_congr rfl fun j _ => ?_
    exact Formalism.L2.Th1.C.subst_mvExp hph0 (MvPowerSeries.constantCoeff_X j)

  have hSG : IntegralMv (MvPowerSeries.subst S (atLogV D lam Λ C wq v (liftT D F) * ePh lam Λ C wq r)) := by
    rw [← MvPowerSeries.coe_substAlgHom hSs, map_mul, MvPowerSeries.coe_substAlgHom, hA, hB]
    have hInt' : IntegralMv (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries D.what₂.Tau ℂ_[p]) *
        ReadTh1 p (fun τ j => κ * v (e j) (τ, 0, 0)) F) := hInt
    have hU : IntegralMv (∏ j, PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries D.what₂.Tau ℂ_[p]) Uu) :=
      integral_prod _ _ fun j _ => integral_subst_single_variable j Uu hUu
    have := integral_mul hU hInt'
    convert this using 1
    ring

  have hback : MvPowerSeries.subst S' (MvPowerSeries.subst S
      (atLogV D lam Λ C wq v (liftT D F) * ePh lam Λ C wq r)) =
      atLogV D lam Λ C wq v (liftT D F) * ePh lam Λ C wq r := by
    rw [MvPowerSeries.subst_comp_subst_apply hSs hS's]
    have hid : (fun i => MvPowerSeries.subst S' (S i)) = MvPowerSeries.X := by
      funext i
      rw [hSi, subst_single_var S' hS's, hS'i, e.apply_symm_apply,
        ← PowerSeries.subst_comp_subst_apply hgs (PowerSeries.HasSubst.X i), hg,
        PowerSeries.subst_X (PowerSeries.HasSubst.X i)]
    rw [hid, MvPowerSeries.subst_self]
    rfl
  rw [← hback]
  exact integral_subst S' hS'0 (fun j => by rw [hS'i]; exact integral_subst_single_variable _ g gI) hSG

end Formalism.L2.KerInert
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelNonzeroUnit
section
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.K2

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem p_ne_zero_Kf (Y : Pend X) : (p : X.G.Kf) ≠ 0 := by
  intro h
  have h1 : algebraMap (K0 p) Y.Kc (p : K0 p) = 0 := by
    rw [map_natCast, ← map_natCast (algebraMap X.G.Kf Y.Kc), h, map_zero]
  rw [map_eq_zero_iff _ (algebraMap (K0 p) Y.Kc).injective] at h1
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h1

theorem eS_ne_zero (Y : Pend X) (j : ℕ) (La : X.Lt j) : Y.eS j La ≠ 0 := by
  unfold Pend.eS
  exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (p_ne_zero_Kf Y)

theorem eT_ne_zero (Y : Pend X) (j : ℕ) (La' : X.Lt (j + 1)) : Y.eT j La' ≠ 0 := by
  unfold Pend.eT
  exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (p_ne_zero_Kf Y)

theorem kernel_of_smul : KerOfSmul := by
  intro p _ X Y j La La' f h G
  have hne : Y.eS j La * (Y.eT j La')⁻¹ ≠ 0 :=
    mul_ne_zero (eS_ne_zero Y j La) (inv_ne_zero (eT_ne_zero Y j La'))
  unfold Pend.ker Pend.kerF
  rw [h, map_smul, smul_smul, mul_inv_cancel₀ hne, one_smul]

theorem ker_zero (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : Y.ker j La La' 0 = 0 := by
  simp only [Pend.ker, Pend.kerF, map_zero, LinearMap.zero_apply, smul_zero]

theorem ker_add (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (G1 G2 : (X.Pj j).Xsp) :
    Y.ker j La La' (G1 + G2) = Y.ker j La La' G1 + Y.ker j La La' G2 := by
  simp only [Pend.ker, Pend.kerF, map_add, LinearMap.add_apply, smul_add]

theorem ker_smul (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (a : X.G.Kf) (G : (X.Pj j).Xsp) :
    Y.ker j La La' (a • G) = a • Y.ker j La La' G := by
  simp only [Pend.ker, Pend.kerF, map_smul, LinearMap.smul_apply]
  rw [smul_smul, smul_smul, mul_comm]

theorem map_smul_Kf (Y : Pend X) {σ : Type} (a : X.G.Kf) (P : MvPolynomial σ X.G.Kf) :
    MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (a • P) = a • MvPolynomial.map (algebraMap X.G.Kf Y.Kc) P := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, algebraMap_smul]

theorem tieChain_of_K {Y : Pend X} (R : RecSide X Y) (hC : TieChainK R) (hR : TieRat R) : TieChain R :=
  fun j hj x => hC j hj x (R.KL j x) (hR j hj x)

theorem body_of_span (Y : Pend X) (j : ℕ) (cK : Y.Kc) (S : Set (X.Fm j))
    (hS : ∀ F ∈ S, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ La ∈ Y.Rep j, (((X.stab j La : Y.Kc))⁻¹ * cK) • Y.ker j La (c', L') (F La.1 La.2))
    (F : X.Fm j) (hF : F ∈ Submodule.span X.G.Kf S) :
    ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ La ∈ Y.Rep j, (((X.stab j La : Y.Kc))⁻¹ * cK) • Y.ker j La (c', L') (F La.1 La.2) := by
  induction hF using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    intro c' L' _
    simp only [map_zero, Pi.zero_apply, ker_zero, smul_zero, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
    intro c' L' hL
    simp only [map_add, Pi.add_apply, ker_add, smul_add, Finset.sum_add_distrib, hx c' L' hL, hy c' L' hL]
  | smul a x _ hx =>
    intro c' L' hL
    simp only [map_smul, Pi.smul_apply, ker_smul]
    rw [map_smul_Kf Y, hx c' L' hL, Finset.smul_sum]
    refine Finset.sum_congr rfl fun La _ => ?_
    rw [smul_comm]

theorem second_kernel_nonzero_unit : K2OfAgreements := by
  intro D p _ X Y R hC hR hS hRd hCl hSer hDel hSp
  have body : K2NonzeroUnit X Y := by
    intro j hj
    obtain ⟨cK, h1, h2, h3, hD⟩ := hDel j hj
    refine ⟨cK, h1, h2, h3, ?_⟩
    intro F hF
    refine body_of_span Y j cK (R.cmp j '' R.Sh j) ?_ F (hSp j hj hF)
    rintro _ ⟨x, hx, rfl⟩ c' L' hL
    rw [hC j hj x, hRd j hj _ c' L' hL, hR j hj x, hS j hj x hx, map_sum]
    rw [← Equiv.sum_comp (R.e j), ← Finset.sum_coe_sort (Y.Rep j)]
    refine Finset.sum_congr rfl fun La _ => ?_
    rw [map_smulₛₗ, map_inv₀, map_natCast, hCl j hj La, hD La x hx c' L' hL,
      kernel_of_smul p X Y j La.1 (c', L') _ (hSer j hj La.1 La.2 c' L' hL), mul_smul]
  refine ⟨body, fun j hj => ?_⟩
  obtain ⟨cK, h1, h2, _, h⟩ := body j hj
  exact ⟨cK, h1, h2, h⟩

theorem admissible_third_of_forms : Adm3bOf := by
  intro D p _ X Y R hC hSp hUp j hj F hF
  have hspan := hSp j hj hF
  clear hF
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    rw [hC j hj y]
    exact hUp j hj _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

section Rec

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}

theorem sharpQ_qOf {t : KerEntTied ex} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {i : ℕ}
    {x : ((Tw.fm u μ).lat i).V} (h : ∃ Q, SharpQ t Tw u μ i x Q) : SharpQ t Tw u μ i x (qOf t Tw u μ i x) := by
  unfold qOf
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem recSum_recOf {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) (t : KerEntTied ex) (Tw : TwForms D)
    (u : D.what₂.Word) (μ : D.what₂.Tup) (ι : ℂ →+* Y.Kc) (σ : D.what₂.LL →+* X.G.Kf)
    (cmp : ∀ j, ((Tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (e : ∀ j, ↥(Y.Rep j) ≃ (D.chTw u μ).cls j)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (hm : X.mm ≤ D.R.m) :
    RecSum (recOf X Y t Tw u μ ι σ cmp Rd e Sr) := by
  intro j hj x hx
  have hQ := sharpQ_qOf hx
  funext c' y'
  show (D.chTw u μ).K j ((Tw.fm u μ).emb j x) c' y' =
    (∑ c : (D.chTw u μ).cls j, (((Nat.card ((D.chTw u μ).stab j c) : ℕ) : ℂ))⁻¹ • entRec t Tw u μ j c x) c' y'
  rw [compatible_lift_exists D L hT Gi Gl Kc0 Dx cX ex t u μ j (lt_of_lt_of_le hj hm) _ _ hQ.1 hQ.2 c' y']
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, entRec]

theorem tieRat_recOf {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) (t : KerEntTied ex) (Tw : TwForms D)
    (u : D.what₂.Word) (μ : D.what₂.Tup) (ι : ℂ →+* Y.Kc) (σ : D.what₂.LL →+* X.G.Kf)
    (cmp : ∀ j, ((Tw.fm u μ).lat j).V →ₛₗ[σ] X.Fm j)
    (Rd : ∀ j, X.Lv.comp (j + 1) → (X.Pj (j + 1)).Tup →
      ((D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) →ₛₗ[ι] XspC (X.Pj (j + 1)) Y.Kc)
    (e : ∀ j, ↥(Y.Rep j) ≃ (D.chTw u μ).cls j)
    (Sr : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Y.Kc) (hK : ∀ j < X.mm, (Tw.fm u μ).KRat j) :
    TieRat (recOf X Y t Tw u μ ι σ cmp Rd e Sr) := by
  intro j hj x
  change ((Tw.fm u μ).lat j).V at x
  obtain ⟨y, hy⟩ := hK j hj x
  show (Tw.fm u μ).emb (j + 1) (klRec Tw u μ j x) = (D.chTw u μ).K j ((Tw.fm u μ).emb j x)
  rw [klRec, Formalism.L2.G.Cmp.ratMap_eq _ _ _ _ x y (by exact hy)]
  exact hy

theorem second_kernel_of_data : K2OfParams := by
  intro D L hT Gi Gl Kc0 Dx cX ex t Tw u μ p _ X Y ι σ cmp Rd e Sr hm hK hC hRd hCl hSer hDel hSp
  have hR := tieRat_recOf X Y t Tw u μ ι σ cmp Rd e Sr hK
  exact second_kernel_nonzero_unit D p X Y _ (tieChain_of_K _ hC hR) hR
    (recSum_recOf X Y t Tw u μ ι σ cmp Rd e Sr hm) hRd hCl hSer hDel hSp

theorem admissible_third_of_data : Adm3bOfRec := by
  intro D L hT Gi Gl Kc0 Dx cX ex t Tw u μ p _ X Y ι σ cmp Rd e Sr hK hC hSp hUp
  exact admissible_third_of_forms D p X Y _ (tieChain_of_K _ hC (tieRat_recOf X Y t Tw u μ ι σ cmp Rd e Sr hK)) hSp hUp

end Rec

end Formalism.L2.KerInert.K2
end
end

