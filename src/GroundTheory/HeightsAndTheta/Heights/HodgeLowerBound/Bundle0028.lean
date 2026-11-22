import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0025
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0058
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0091
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitEps
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace StokesLimitEps

open Matrix

theorem coeff_tendsto {N : ℕ} (c : ℕ → ℝ → ℝ) (f : ℕ → ℝ → ℝ) (g : ℕ → ℝ)
    (hf : ∀ q : ℕ, 1 ≤ q → ∀ᶠ t in 𝓝[>] (0 : ℝ), f q t = ∑ i ∈ Finset.range N, c i t * (1 / (q : ℝ)) ^ i)
    (hg : ∀ q : ℕ, 1 ≤ q → Tendsto (f q) (𝓝[>] 0) (𝓝 (g q))) :
    ∃ ℓ : ℕ → ℝ, (∀ i < N, Tendsto (c i) (𝓝[>] 0) (𝓝 (ℓ i))) ∧
      ∀ q : ℕ, 1 ≤ q → g q = ∑ i ∈ Finset.range N, ℓ i * (1 / (q : ℝ)) ^ i := by

  let x : Fin N → ℝ := fun j => 1 / (((j : ℕ) + 1 : ℕ) : ℝ)
  have hinj : Function.Injective x := by
    intro j k h
    simp only [x, one_div, _root_.inv_inj, Nat.cast_inj] at h
    exact Fin.ext (by omega)
  have hdet : IsUnit (Matrix.vandermonde x).det := by
    rw [isUnit_iff_ne_zero, Matrix.det_vandermonde_ne_zero_iff]
    exact hinj
  let F : ℝ → Fin N → ℝ := fun t j => f ((j : ℕ) + 1) t

  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (fun i : Fin N => c i t) = (Matrix.vandermonde x)⁻¹ *ᵥ F t := by
    filter_upwards [Filter.eventually_all.2 fun j : Fin N => hf ((j : ℕ) + 1) (by omega)] with t ht
    have hval : F t = Matrix.vandermonde x *ᵥ fun i : Fin N => c i t := by
      funext j
      simp only [F, ht j, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, x]
      rw [← Fin.sum_univ_eq_sum_range (fun i => c i t * (1 / (((j : ℕ) + 1 : ℕ) : ℝ)) ^ i)]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hval, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hF : Tendsto F (𝓝[>] 0) (𝓝 fun j : Fin N => g ((j : ℕ) + 1)) :=
    tendsto_pi_nhds.2 fun j => hg _ (by omega)
  have hC : Tendsto (fun t => fun i : Fin N => c i t) (𝓝[>] 0)
      (𝓝 ((Matrix.vandermonde x)⁻¹ *ᵥ fun j : Fin N => g ((j : ℕ) + 1))) :=
    (((continuous_const.matrix_mulVec continuous_id).tendsto _).comp hF).congr' (hev.mono fun t ht => ht.symm)
  let ℓ : ℕ → ℝ := fun i => if h : i < N then
    ((Matrix.vandermonde x)⁻¹ *ᵥ fun j : Fin N => g ((j : ℕ) + 1)) ⟨i, h⟩ else 0
  have hℓ : ∀ i < N, Tendsto (c i) (𝓝[>] 0) (𝓝 (ℓ i)) := by
    intro i hi
    simpa only [ℓ, dif_pos hi] using tendsto_pi_nhds.1 hC ⟨i, hi⟩
  refine ⟨ℓ, hℓ, fun q hq => tendsto_nhds_unique (hg q hq) ?_⟩
  refine Tendsto.congr' ((hf q hq).mono fun t ht => ht.symm) ?_
  exact tendsto_finsetSum _ fun i hi => (hℓ i (Finset.mem_range.1 hi)).mul_const _

theorem tendsto_const_coeff {N : ℕ} (ℓ : ℕ → ℝ) (hN : 1 ≤ N) :
    Tendsto (fun m : ℕ => ∑ i ∈ Finset.range N, ℓ i * (1 / ((m + 1 : ℕ) : ℝ)) ^ i) atTop (𝓝 (ℓ 0)) := by
  have h0 : Tendsto (fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hs := tendsto_finsetSum (Finset.range N) fun i _ => (h0.pow i).const_mul (ℓ i)
  have e : ∑ i ∈ Finset.range N, ℓ i * (0 : ℝ) ^ i = ℓ 0 := by
    rw [Finset.sum_eq_single 0 (fun b _ hb => by simp [zero_pow hb])
      (fun h => absurd (Finset.mem_range.2 hN) h)]
    simp
  rwa [e] at hs

end StokesLimitEps

theorem StokesLimitEps.proof (hT : StokesLimitT.Statement) (hTop : TopNPoly.Statement)
    (hOm : OmNPoly.Statement) (hMu : MuMeasureLimit.Statement) : StokesLimitEps.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B hII hAr
  have hTq := fun q (hq : 1 ≤ q) => hT II Ψ K ι Ω E D O Lt X B 1 q hII hAr le_rfl hq
  obtain ⟨c, hc0, hc⟩ := hTop II Ψ K ι Ω E D O Lt X B hII hAr
  obtain ⟨v, d, hv0, hd0, hvd⟩ := hOm II Ψ K ι Ω E D O Lt X B hII hAr
  obtain ⟨hmuV, hmuD⟩ := hMu II Ψ K ι Ω E D O Lt X B hII hAr
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨ℓ, hℓ, hg⟩ := StokesLimitEps.coeff_tendsto c (fun q => X.topN B 1 q) (X.topNLim B 1) hc
      fun q hq => (hTq q hq).1
    have h0 : ℓ 0 = arLim X.H X.S B := by
      obtain ⟨L, hL⟩ := hAr
      have e1 : arLim X.H X.S B = L := by unfold arLim; exact hL.limUnder_eq
      have h := hℓ 0 (by omega)
      rw [hc0] at h
      rw [e1]; exact tendsto_nhds_unique h hL
    rw [← h0]
    exact (StokesLimitEps.tendsto_const_coeff ℓ (N := D.n + 2) (by omega)).congr fun m =>
      (hg (m + 1) (by omega)).symm
  · obtain ⟨ℓ, hℓ, hg⟩ := StokesLimitEps.coeff_tendsto v (fun q => X.Vb B 1 q) (X.VbLim B 1)
      (fun q hq => (hvd q hq).mono fun t h => h.1) fun q hq => (hTq q hq).2.1
    have h0 : ℓ 0 = meanU X.H X.Cd * degMu X.H / 2 := by
      have h := hℓ 0 (by omega)
      rw [hv0] at h
      exact tendsto_nhds_unique h hmuV
    rw [← h0]
    exact (StokesLimitEps.tendsto_const_coeff ℓ (N := D.n + 1) (by omega)).congr fun m =>
      (hg (m + 1) (by omega)).symm
  · obtain ⟨ℓ, hℓ, hg⟩ := StokesLimitEps.coeff_tendsto d (fun q => X.degN B 1 q) (X.degNLim B 1)
      (fun q hq => (hvd q hq).mono fun t h => h.2) fun q hq => (hTq q hq).2.2
    have h0 : ℓ 0 = degMu X.H := by
      have h := hℓ 0 (by omega)
      rw [hd0] at h
      exact tendsto_nhds_unique h hmuD
    rw [← h0]
    exact (StokesLimitEps.tendsto_const_coeff ℓ (N := D.n + 1) (by omega)).congr fun m =>
      (hg (m + 1) (by omega)).symm

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesStep
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology

namespace StokesStep

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_multicone : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem ptsIntegral_congr_g (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {g g' : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ mcPts P, g z = g' z) :
    ptsIntegral P φ g = ptsIntegral P φ g' := by
  classical
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · congr 1
    funext y
    refine finsum_congr fun w => finsum_congr fun _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · rw [hg _ hγ.choose_spec.2.self_of_nhds.2.1]
    · rfl
  · rfl

theorem isConeTangent_lift {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (x : R.X)
    (j : Fin R.A.n) {y : Fin e → ℂ}
    (hy : y ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) (w : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P (R.lift x ((R.A.chart j).symm y))
      (fderiv ℂ (fun y' => R.lift x ((R.A.chart j).symm y')) y w) := by
  set τ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' => R.lift x ((R.A.chart j).symm y') with hτdef
  have hO : IsOpen ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :=
    (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)
  have hτ : AnalyticAt ℂ τ y := analyticAt_pi_iff.mpr fun p => R.holo x p j y hy
  intro f hf
  set F := map (Int.castRingHom ℂ) f
  have h0 : (fun y' => eval (τ y') F) =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hO.mem_nhds hy] with y' hy'
    exact (R.mem x _ hy'.2).2 f hf
  have hD := (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (τ y)).comp y hτ.differentiableAt.hasFDerivAt
  have hD0 : HasFDerivAt (fun y' => eval (τ y') F) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq h0
  have h1 := congrArg (fun L => L w) (hD.unique hD0)
  simpa [smul_eq_mul, mul_comm] using h1

theorem isPsh_potOf {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {A : HermLine ι}
    (hA : IsSemipositiveH P A) : IsPsh R.A (potOf R A) := by
  intro x j y hy w
  have hy' : y ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x := hy
  set τ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' => R.lift x ((R.A.chart j).symm y') with hτdef
  have hτ : AnalyticAt ℂ τ y := analyticAt_pi_iff.mpr fun p => R.holo x p j y hy'
  have hz : τ y ∈ mcPts P := R.mem x _ hy'.2
  have hS : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∈ 𝓝 (τ y) :=
    isOpen_multicone.mem_nhds hz.1
  have hφ : ContDiffAt ℝ 2 (fun z => Real.log (A.h z)) (τ y) :=
    ((hA.1.contDiffAt hS).of_le (WithTop.coe_le_coe.mpr le_top)).log (A.pos _ hz.1).ne'
  have hc : (potOf R A).φ x ∘ (R.A.chart j).symm = (fun z => Real.log (A.h z)) ∘ τ := rfl
  rw [hc, ReciprocityTheory.AnForm.levi_comp w hτ hφ]
  exact hA.2 _ hz _ (isConeTangent_lift R x j hy' w)

end StokesStep

open StokesStep in

theorem StokesStep.proof (hE : ResExistsStatement) : StokesStep.Statement := by
  intro K _ ι _ P n i A A' hP ha hA hA' hi
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hE hP
  set C := A'.tensor A.inv with hCdef
  have hC0 : C.a = 0 := by simp [C, HermLine.tensor, HermLine.inv, ha]
  have hCs : IsSmoothHerm C := hA'.1.mul (isSmoothHerm_inv hA.1)
  have hlogC : ∀ z, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      Real.log (C.h z) = Real.log (A'.h z) - Real.log (A.h z) := by
    intro z hz
    show Real.log (A'.h z * (A.h z)⁻¹) = _
    rw [Real.log_mul (A'.pos z hz).ne' (inv_ne_zero (A.pos z hz).ne'), Real.log_inv]
    ring
  let L : ℕ → Fin (m + 1) → HermLine ι := fun l j => if j.val < l then A' else A
  have hpot : ∀ l, stokesMixPot A A' (m + 1) l = pot (L l) := by
    intro l
    funext j z
    simp only [stokesMixPot, pot, L]
    split_ifs <;> rfl
  have hLsp : ∀ l j, IsSemipositiveH P (L l j) := fun l j => by
    simp only [L]
    split_ifs
    exacts [hA', hA]
  have hL : ∀ l j, IsSmoothHerm (L l j) := fun l j => (hLsp l j).1
  have hs := isSectionOn_inv_one hP.2.1.1 hC0
  set v : R.X → ℝ := fun x => Real.log (C.h (R.lift x x)) with hvdef
  have key : ∀ l, ptsIntegral P (stokesMixPot A A' (m + 1) l)
      (fun z => Real.log (A'.h z) - Real.log (A.h z)) = mInt R.A (fun j => potOf R (L l j)) v := by
    intro l
    rw [ptsIntegral_congr_g P _ (g' := logNorm C.inv 1) fun z hz => by
      rw [logNorm_inv_one, hlogC z hz.1], hpot,
      ptsIntegral_eq_mInt' hE resBridge R hP (hL l) (isSmoothHerm_inv hCs) hs]
    congr 1
    funext x
    exact logNorm_inv_one C _
  rw [key, key]

  set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 ⟨i, hi⟩ with hσ
  rw [← mIntSymm R.A (fun j => potOf R (L (i + 1) j)) σ v,
    ← mIntSymm R.A (fun j => potOf R (L i j)) σ v]
  set T : Fin m → LocPot R.X := fun k => potOf R (L i (σ k.succ)) with hT
  have hne : ∀ j : Fin (m + 1), j ≠ ⟨i, hi⟩ → L (i + 1) j = L i j := by
    intro j hj
    have hj' : j.val ≠ i := fun h => hj (Fin.ext h)
    simp only [L]
    by_cases h : j.val < i
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  have hσs : ∀ k : Fin m, σ k.succ ≠ ⟨i, hi⟩ := by
    intro k hk
    rw [hσ, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at hk
    exact Fin.succ_ne_zero k hk
  have e1 : (fun j => potOf R (L (i + 1) j)) ∘ σ = Fin.cons (potOf R A') T := by
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [σ, L]
    · simp only [Function.comp_apply, Fin.cons_succ, T]
      rw [hne _ (hσs k)]
  have e0 : (fun j => potOf R (L i j)) ∘ σ = Fin.cons (potOf R A) T := by
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · simp [σ, L]
    · simp only [Function.comp_apply, Fin.cons_succ, T]
  rw [e1, e0]

  have hv : R.A.Smooth v := smooth_diag R hCs hC0
  have hgerm : mInt R.A (Fin.cons (potOf R A') T) v =
      mInt R.A (Fin.cons (potOf R A + LocPot.ofFun v) T) v := by
    refine ReciprocityTheory.ChartRestriction.G.Geo.mInt_congr R.A (locDens_cons_congr R.A T fun j y hy => ?_) fun _ => rfl
    set x0 := (R.A.chart j).symm y
    filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)).mem_nhds
      ⟨hy, R.mem_U x0⟩] with y' hy'
    have hmc := (R.mem x0 _ hy'.2).1
    show Real.log (A'.h (R.lift x0 _)) = Real.log (A.h (R.lift x0 _)) + v _
    rw [hvdef]
    simp only
    rw [← h_eq_of_sameOrbit hC0 (R.compat x0 _ _ ⟨hy'.2, R.mem_U _⟩), hlogC _ hmc]
    ring
  have hpA : IsPotential R.A (potOf R A) := isPotential_potOf R hA.1
  have hpv : IsPotential R.A (LocPot.ofFun v) := isPotential_ofFun R.A v hv
  have hTp : ∀ k, IsPotential R.A (T k) := fun k => isPotential_potOf R (hL i _)
  have hTpsh : ∀ k, IsPsh R.A (T k) := fun k => isPsh_potOf R (hLsp i _)
  have hcons : ∀ Q, IsPotential R.A Q → ∀ k, IsPotential R.A ((Fin.cons Q T : Fin (m + 1) → LocPot R.X) k) :=
    fun Q hQ k => by
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hQ
      · simpa using hTp k
  have hvc : Continuous v := PLC.continuous_of_smooth R.A hv
  have hadd := mIntAdd R.A (potOf R A) (LocPot.ofFun v) T hpA hpv hTp v
    (mIntegrableCont R.A _ (hcons _ hpA) v hvc) (mIntegrableCont R.A _ (hcons _ hpv) v hvc)
  have hneg := byPartsNonpos R.A v hv T hTp hTpsh
  rw [hgerm, hadd]
  linarith

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTopNPoly
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace TopNPoly

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem orbitRep_orbitRep (z : (Σ k, ι k) → ℂ) : orbitRep (orbitRep z) = orbitRep z := by
  simp only [orbitRep, Quotient.out_eq]

theorem orbitRep_blocks {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, orbitRep z ⟨k, i⟩ ≠ 0 := by
  obtain ⟨c, -, hzc⟩ := exists_eq_smul_orbitRep z
  intro k
  obtain ⟨i, hi⟩ := hz k
  refine ⟨i, fun h => hi ?_⟩
  rw [hzc]
  simp [torusSmul, h]

theorem hermOfFun_h_orbitRep {a : K → ℤ} {F : ((Σ k, ι k) → ℂ) → ℝ} {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (hF : 0 < F (orbitRep z)) :
    (hermOfFun ι a F).h (orbitRep z) = F (orbitRep z) := by
  have hR := refNorm_pos a (orbitRep_blocks hz)
  simp only [hermOfFun]
  rw [orbitRep_orbitRep, Real.exp_log (div_pos hF hR), mul_div_cancel₀ _ hR.ne']

theorem hermOfFun_h_smul {a : K → ℤ} {F : ((Σ k, ι k) → ℂ) → ℝ} {z : (Σ k, ι k) → ℂ} {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) (hzc : z = torusSmul c (orbitRep z)) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hF : 0 < F (orbitRep z)) :
    (hermOfFun ι a F).h z = (∏ k, ‖c k‖ ^ a k) * F (orbitRep z) := by
  have h1 := hermOfFun_h_orbitRep (a := a) hz hF
  conv_lhs => rw [hzc]
  exact ((hermOfFun ι a F).smul c (orbitRep z) hc).trans (by rw [h1]; rfl)

theorem prod_norm_zpow_add {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (a b : K → ℤ) (q : ℕ) :
    (∏ k, ‖c k‖ ^ ((q : ℤ) • a + ((1 : ℕ) : ℤ) • b) k) = (∏ k, ‖c k‖ ^ a k) ^ q * ∏ k, ‖c k‖ ^ b k := by
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h0 : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_one, one_mul]
  rw [zpow_add₀ h0, show (q : ℤ) * a k = a k * q by ring, zpow_mul, zpow_natCast]

theorem smoothRep_smooth_of {P : Ideal (MRing ι)} {A Z : HermLine ι} (ha : Z.a = A.a) (hZ : IsSmoothHerm Z)
    (hh : ∀ z ∈ mcPts P, Z.h z = A.h z) : IsSmoothHerm (smoothRep P A) := by
  classical
  unfold smoothRep
  split_ifs with h
  · exact h.choose_spec.2.1
  · exact absurd ⟨Z, ha, hZ, hh⟩ h

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

omit [DecidableEq Ψ] in

theorem NbarQ_h_eq (hV : VertFactorPos.Statement) (X : ComponentSetting D O Lt) (B q : ℕ) (t : ℝ)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    (X.NbarQ B 1 q t).h z = (muReg X.H X.S B t).h z ^ q * D.A'.h z := by
  obtain ⟨c, hc, hzc⟩ := exists_eq_smul_orbitRep z
  have hz0 := hz.1
  have hw0 := orbitRep_blocks hz0
  have hwP : orbitRep z ∈ mcPts (mCoordIdeal D.y) := by
    have h := mcPts_smul D.arith.2.1.2.1 (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hz
    convert h using 1
    funext p
    have hp : z p = c p.1 * orbitRep z p := congrFun hzc p
    rw [hp, ← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]
  have hvf : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z) :=
    Finset.prod_pos fun p' hp' => hV II Ψ K ι Ω E D p' (Finset.mem_filter.1 hp').1 _ hwP
  have hG0 : 0 < X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    mul_pos (X.S.ref.pos _ hw0) (Real.exp_pos _)
  have hreg : (X.S.regLine t).h (orbitRep z) =
      X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    hermOfFun_h_orbitRep hz0 hG0
  have hM : (muReg X.H X.S B t).h z = (∏ k, ‖c k‖ ^ muTwDeg X.H B k) *
      ((X.S.regLine t).h (orbitRep z) * ∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z)) := by
    unfold muReg
    rw [smoothRep_h _ hz]
    exact hermOfFun_h_smul hc hzc hz0 (by rw [hreg]; exact mul_pos hG0 hvf)
  have hN : (X.NbarQ B 1 q t).h z = (∏ k, ‖c k‖ ^ ((q : ℤ) • muTwDeg X.H B + ((1 : ℕ) : ℤ) • D.a') k) *
      ((X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z)))) ^ q *
        (∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z)) ^ q * D.A'.h (orbitRep z) ^ 1) := by
    unfold ComponentSetting.NbarQ
    rw [smoothRep_h _ hz]
    exact hermOfFun_h_smul hc hzc hz0
      (mul_pos (mul_pos (pow_pos hG0 _) (pow_pos hvf _)) (pow_pos (D.A'.pos _ hw0) _))
  have hA : D.A'.h z = (∏ k, ‖c k‖ ^ D.a' k) * D.A'.h (orbitRep z) := by
    conv_lhs => rw [hzc]
    exact (D.A'.smul c (orbitRep z) hc).trans (by rw [D.A'_deg])
  rw [hN, hM, hA, hreg, prod_norm_zpow_add hc]
  ring

end TopNPoly

open TopNPoly in

theorem TopNPoly.proof (hIso : HilbertSamuel.IsomInvariance.Statement) (hV : VertFactorPos.Statement)
    (hS : MuRegSmooth.Statement) : TopNPoly.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B hII _
  have hP : IsArithVar (mCoordIdeal D.y) (D.n + 1) := D.arith
  have hA : IsSmoothHerm D.A' := D.A'_pos.1
  refine ⟨fun i t => if i = 0 then arLimFun X.H X.S B t else ((D.n + 1).choose i : ℝ) *
      II K ι (mCoordIdeal D.y) (D.n + 1)
        (fun j : Fin (D.n + 1) => if (j : ℕ) < D.n + 1 - i then muReg X.H X.S B t else D.A'),
    by funext t; simp, fun q hq => ?_⟩
  filter_upwards [hS II Ψ K ι Ω E D O Lt X B] with t ht
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set Z := HilbertSamuel.HermLine.zcomb (muReg X.H X.S B t) D.A' (q : ℤ) ((1 : ℕ) : ℤ) with hZdef
  have hZ : IsSmoothHerm Z := HilbertSamuel.ZCombLimit.isSmoothHerm_zcomb_int ht hA _ _
  have hagree : ∀ z ∈ mcPts (mCoordIdeal D.y), Z.h z = (X.NbarQ B 1 q t).h z := by
    intro z hz
    rw [NbarQ_h_eq hV X B q t hz]
    show (muReg X.H X.S B t).h z ^ (q : ℤ) * D.A'.h z ^ ((1 : ℕ) : ℤ) = _
    simp
  have hdeg : Z.a = (X.NbarQ B 1 q t).a := by
    unfold ComponentSetting.NbarQ
    rw [smoothRep_a]
    show (q : ℤ) • (muReg X.H X.S B t).a + ((1 : ℕ) : ℤ) • D.A'.a = _
    rw [muReg, smoothRep_a, D.A'_deg]
    rfl
  have hN : IsSmoothHerm (X.NbarQ B 1 q t) := by
    unfold ComponentSetting.NbarQ
    refine smoothRep_smooth_of (Z := Z) ?_ hZ fun z hz => ?_
    · rw [hdeg]; unfold ComponentSetting.NbarQ; rw [smoothRep_a]
    · rw [hagree z hz]; unfold ComponentSetting.NbarQ; rw [smoothRep_h _ hz]
  have hne : (1 : MRing ι) ∉ mCoordIdeal D.y := fun h =>
    hP.2.1.1.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hiso : ∀ j : Fin (D.n + 1), HilbertSamuel.IsIsometricOn (mCoordIdeal D.y)
      ((fun _ => X.NbarQ B 1 q t) j) ((fun _ => Z) j) := fun _ =>
    ⟨1, 1, 0, 0, by simpa using isMultiHomog_C_zero (ι := ι) 1, by simpa using isMultiHomog_C_zero (ι := ι) 1,
      hne, hne, fun k => by simp [hdeg], rfl, fun z hz => by simp [hagree z hz]⟩
  have hI := hIso K ι (II K ι) (hII K ι) (mCoordIdeal D.y) (D.n + 1) (fun _ => X.NbarQ B 1 q t) (fun _ => Z) hP
    (fun _ => hN) (fun _ => hZ) hiso
  have hE := (HilbertSamuel.ZCombExpand.proof K ι (II K ι) (hII K ι) (mCoordIdeal D.y) (D.n + 1)
    (muReg X.H X.S B t) D.A' q 1 hP ht hA).1
  show II K ι (mCoordIdeal D.y) (D.n + 1) (fun _ => X.NbarQ B 1 q t) / (q : ℝ) ^ (D.n + 1) = _
  rw [hI, hE, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ D.n + 1 := by simp at hi; omega
  have hpow : (q : ℝ) ^ (D.n + 1) = (q : ℝ) ^ (D.n + 1 - i) * (q : ℝ) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  split_ifs with h0
  · subst h0
    have hall : (fun j : Fin (D.n + 1) => if (j : ℕ) < D.n + 1 - 0 then muReg X.H X.S B t else D.A') =
        fun _ => muReg X.H X.S B t := by
      funext j; simp [j.isLt]
    rw [hall]
    simp only [arLimFun, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul, Nat.sub_zero, pow_zero]
    field_simp
  · rw [hpow, Nat.cast_one, one_pow, mul_one, one_div, inv_pow]
    field_simp

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBdPtsNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def BdPtsNull.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E),
    IsPtsNull (mCoordIdeal D.y) D.n D.Bd

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBoundaryNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def BoundaryNull.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E),
    IsPtsNull (mCoordIdeal D.y) D.n D.Bd

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

