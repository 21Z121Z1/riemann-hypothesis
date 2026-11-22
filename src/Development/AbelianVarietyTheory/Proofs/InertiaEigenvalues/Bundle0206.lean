import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0203
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ClosedBallValuationSubringToSubring
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleOrbitalFourierRankOneTransfer
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0198
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcris
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0199
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0200
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0191
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutiveAlgebraProductIdentity
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutingIntegralMatrixTopnil
section
open Matrix Polynomial

namespace GlobalTheory.UnitDiscAlg

section Residue
variable (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]

def unitBallMaxIdeal : Ideal (unitBallSubring E) := GlobalTheory.ClosedBallValuationSubring.openBallIdeal E

theorem mem_unitBallMaxIdeal {t : unitBallSubring E} :
    t ∈ unitBallMaxIdeal E ↔ ‖(t : E)‖ < 1 := Iff.rfl

theorem unitBallMaxIdeal_isMaximal : (unitBallMaxIdeal E).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · intro h
    have h' : ‖((1 : E))‖ < 1 := h
    simp at h'
  · intro J x _ hx hxJ
    have hx1 : ¬ ‖(x : E)‖ < 1 := hx
    have hx2 : ‖(x : E)‖ ≤ 1 := x.2
    have hn : ‖(x : E)‖ = 1 := le_antisymm hx2 (not_lt.mp hx1)
    have hx0 : (x : E) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hn
      exact zero_ne_one hn
    have hinv : ‖(x : E)⁻¹‖ ≤ 1 := by rw [norm_inv, hn, inv_one]
    have hmem := J.mul_mem_left ⟨(x : E)⁻¹, hinv⟩ hxJ
    convert hmem using 1
    apply Subtype.ext
    exact (inv_mul_cancel₀ hx0).symm

end Residue

theorem norm_lt_one_of_pow_of_commute (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E]
    (n : ℕ) (N : Matrix (Fin n) (Fin n) E) (hN : ∀ i j, ‖N i j‖ ≤ 1)
    (hb : ∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧
      u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (w : Matrix (Fin n) (Fin n) E) (hwN : w * N = N * w) (hw : ∀ i j, ‖w i j‖ ≤ 1)
    (M : ℕ) (hM : ∀ i j, ‖(w ^ M) i j‖ < 1) : ∀ i j, ‖w i j‖ < 1 := by
  intro i j
  have hM0 : M ≠ 0 := by
    rintro rfl
    have := hM i i
    simp at this
  obtain ⟨u, v, hu, hv, huv⟩ := hb
  haveI := unitBallMaxIdeal_isMaximal E
  letI : Field (unitBallSubring E ⧸ unitBallMaxIdeal E) := Ideal.Quotient.field _
  let O := unitBallSubring E
  let π : O →+* (unitBallSubring E ⧸ unitBallMaxIdeal E) := Ideal.Quotient.mk _
  let N' : Matrix (Fin n) (Fin n) O := fun a b => ⟨N a b, hN a b⟩
  let w' : Matrix (Fin n) (Fin n) O := fun a b => ⟨w a b, hw a b⟩
  have hNm : O.subtype.mapMatrix N' = N := by ext; rfl
  have hwm : O.subtype.mapMatrix w' = w := by ext; rfl
  have hinj : Function.Injective (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O →+* _) := by
    intro a b h
    ext x y
    exact congrFun (congrFun h x) y
  have hwN' : w' * N' = N' * w' := hinj (by rw [map_mul, map_mul, hNm, hwm, hwN])
  have hu' : (u.coeffs : Set E) ⊆ O := by
    intro c hc
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hc
    obtain ⟨m, -, rfl⟩ := hc
    exact hu m
  have hv' : (v.coeffs : Set E) ⊆ O := by
    intro c hc
    rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hc
    obtain ⟨m, -, rfl⟩ := hc
    exact hv m
  have hNmap : N'.map O.subtype = N := by ext; rfl
  have hbO : u.toSubring O hu' * N'.charpoly + v.toSubring O hv' * derivative N'.charpoly = 1 := by
    apply Polynomial.map_injective O.subtype Subtype.val_injective
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
      Polynomial.map_toSubring, Polynomial.map_toSubring, ← Matrix.charpoly_map, hNmap,
      Polynomial.map_one]
    exact huv
  set N'' := N'.map π with hN''
  set w'' := w'.map π with hw''
  have hbk : (u.toSubring O hu').map π * N''.charpoly
      + (v.toSubring O hv').map π * derivative N''.charpoly = 1 := by
    have := congrArg (Polynomial.map π) hbO
    simpa [hN'', Polynomial.map_add, Polynomial.map_mul, Polynomial.derivative_map,
      Matrix.charpoly_map] using this
  have hwk : w'' * N'' = N'' * w'' := by
    rw [hN'', hw'', ← Matrix.map_mul, ← Matrix.map_mul, hwN']
  have hs : N''.charpoly.Separable := ⟨_, _, hbk⟩
  obtain ⟨x, hx⟩ := GlobalTheory.RegSS.cyclicField (unitBallSubring E ⧸ unitBallMaxIdeal E) (Fin n) N'' hs
  have hbij := (GlobalTheory.RegSS.CycAlg.cyclicAlgebra _ (Fin n) N'' x hx).2.2
  have hmem : w'' ∈ Algebra.adjoin (unitBallSubring E ⧸ unitBallMaxIdeal E) {N''} :=
    GlobalTheory.RegSS.mem_genAlg_of_commute hbij hwk
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨f, hf⟩ := hmem
  have hpowm : O.subtype.mapMatrix (w' ^ M) = w ^ M := by rw [map_pow, hwm]
  have hpow : w'' ^ M = 0 := by
    rw [hw'', ← Matrix.map_pow]
    ext a b
    rw [Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem, mem_unitBallMaxIdeal]
    have := congrFun (congrFun hpowm a) b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at this
    show ‖(((w' ^ M) a b : O) : E)‖ < 1
    rw [show (((w' ^ M) a b : O) : E) = (w ^ M) a b from this]
    exact hM a b
  have hfM : aeval N'' (f ^ M) = 0 := by
    rw [map_pow]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf
    rw [hf, hpow]
  have hdvd := minpoly.dvd _ N'' hfM
  have hsq : Squarefree (minpoly (unitBallSubring E ⧸ unitBallMaxIdeal E) N'') :=
    hs.squarefree.squarefree_of_dvd (Matrix.minpoly_dvd_charpoly N'')
  have hdvd' := (Squarefree.dvd_pow_iff_dvd hsq hM0).mp hdvd
  have hf0 : aeval N'' f = 0 := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdvd' (minpoly.aeval _ _)
  have hw0 : w'' = 0 := by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf
    rw [← hf, hf0]
  have hij := congrFun (congrFun hw0 i) j
  rw [hw'', Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem,
    mem_unitBallMaxIdeal] at hij
  exact hij

end GlobalTheory.UnitDiscAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleOrbitalFourierRankOneTransferStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleOrbitalFourier_rankOne_transfer : RankOne := by
  first | exact @GlobalTheory.JR.RankOneTransfer.rankOne | exact GlobalTheory.JR.RankOneTransfer.rankOne | (intros; apply GlobalTheory.JR.RankOneTransfer.rankOne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEisensteinPowSmulMonodromyMemBreuilKisin
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries

theorem exists_pow_E_smul_EN_mem_Man : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι),
    ∃ n : ℕ, ∀ m ∈ P.M, E K l e ^ n • P.EN m ∈ P.Man := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P
  obtain ⟨α, β, hα, hβ⟩ := P.exists_exponents
  have hk : 1 / ((e : ℝ) * l) < 1 / (e : ℝ) := by
    have he : (0 : ℝ) < e := by exact_mod_cast NeZero.pos e
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    exact one_div_lt_one_div_of_lt he (by nlinarith)

  have hL : ∀ v ∈ P.L, E K l e ^ α • P.conn v ∈ P.Man := by
    intro v hv
    have hv' : v ∈ P.Lk (1 / (e : ℝ)) := P.ext_mono (A_le_Rpi l e) hv
    obtain ⟨w, rfl⟩ := P.xiExt.surjective v
    have hw : w ∈ P.Mext (R O K l (1 / (e : ℝ))) :=
      (GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι P (1 / (e : ℝ)) hk w).1 hv'
    have hNw : (fun τ i => N K (w τ i)) ∈ P.Mext (R O K l (1 / (e : ℝ))) :=
      mem_tot.2 fun τ i => N_mem (derivative_mem_R l (mem_tot.1 hw τ i))
    have h1 : P.conn (P.xiExt w) ∈ P.ext (Rpi O K l e) := by
      rw [PhiMod.conn_xiExt]
      exact (GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι P (1 / (e : ℝ)) hk _).2 hNw
    exact P.smul_mem_Mext_of_basis (fun i => hα _ (P.phi_mem_L (P.bas_mem_M i))) (A_le_Rpi l e) h1
  refine ⟨α + β, fun m hm => ?_⟩
  have hv := hL _ (hβ m hm)
  rw [PhiMod.conn_smul, smul_add, smul_smul, smul_smul, ← pow_add] at hv
  have h2 : (E K l e ^ α * N K (E K l e ^ β)) • m ∈ P.Man :=
    P.smul_mem_Man (mul_mem (pow_mem (E_mem l e _) α) (N_mem (derivative_mem_R l (pow_mem (E_mem l e _) β))))
      (P.M_le_Man hm)
  have h3 : E K l e ^ (α + β) • P.conn m ∈ P.Man := by
    have := sub_mem hv h2
    rwa [add_sub_cancel_left] at this
  rw [PhiMod.EN_apply, smul_comm]
  exact P.smul_mem_Man (E_mem l e _) h3

end GlobalTheory.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcrisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gauss_norm_extension_acris : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ), (l : ℝ)⁻¹ ≤ r → r < 1 → ∃ N : Per.Acris l → ℝ, (∀ x, 0 ≤ N x ∧ N x ≤ 1) ∧ (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧ (∀ x, N (-x) = N x) ∧ (∀ x y, N (x * y) = N x * N y) ∧ ∀ a : Per.Ainf l, N (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n := by
  first | exact @GlobalTheory.GaussExt.exists_gauss_acris | exact GlobalTheory.GaussExt.exists_gauss_acris | (intros; apply GlobalTheory.GaussExt.exists_gauss_acris <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralFlagChartEnlargeContainingValueStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralFlagChart_enlarge_containing_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [Algebra O c.F] [IsFractionRing O c.F] (f : Rul Xo c) (P : GlobalTheory.Reg.PChart Xo c (algebraMap O c.F)), (∀ e ∈ P.es, evR Xo c f P.yg ∈ P.R e) → IsIntegral (Algebra.adjoin c.F (P.gens : Set P.Ω)) (evR Xo c f P.yg) → ∃ P' : GlobalTheory.Reg.PChart Xo c (algebraMap O c.F), evR Xo c f P'.yg ∈ Algebra.adjoin c.F (P'.gens : Set P'.Ω) ∧ ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L), (∀ a : O, algebraMap c.F L (algebraMap O c.F a) ∈ W) → ∀ y : FrPt Xo c L, P.Catches W y → P'.Catches W y := by
  first | exact @GlobalTheory.Reg.Enlarge.enlarge_exists | exact GlobalTheory.Reg.Enlarge.enlarge_exists | (intros; apply GlobalTheory.Reg.Enlarge.enlarge_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralIdempotentLiftNewtonStatement
section
open GlobalTheory.UnitDiscAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_idempotent_lift_newton : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [CompleteSpace E] (n : ℕ) (N x a : Matrix (Fin n) (Fin n) E) (ϖ : E), ‖ϖ‖ < 1 → x * N = N * x → (∀ i j, ‖x i j‖ ≤ 1) → (∀ i j, ‖a i j‖ ≤ 1) → x * x - x = ϖ • a → ∃ e a' : Matrix (Fin n) (Fin n) E, e * N = N * e ∧ a' * N = N * a' ∧ e * e = e ∧ (∀ i j, ‖e i j‖ ≤ 1) ∧ (∀ i j, ‖a' i j‖ ≤ 1) ∧ e - x = ϖ • a' := by
  first | exact @GlobalTheory.IdemLift.idem_lift | exact GlobalTheory.IdemLift.idem_lift | (intros; apply GlobalTheory.IdemLift.idem_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaNablaMemOfKillingPolynomialStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gammaNabla_mem_of_killing_polynomial : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (i : ZMod n) (N : Submodule k⟦X⟧ (Vc k m)) (s : ℤ), CondC (D.γ i) N → EPoly (D.γ i) N s → ∀ x ∈ N, (∃ j : ℕ, ((nab (D.γ i)) ^ j) x ∈ sh s N) → nab (D.γ i) x ∈ sh s N := by
  first | exact @GlobalTheory.GenKernelFit.nab_mem_of_ePoly | exact GlobalTheory.GenKernelFit.nab_mem_of_ePoly | (intros; apply GlobalTheory.GenKernelFit.nab_mem_of_ePoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisTeichmullerTiltSubEqOne
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.Gauss

lemma gA_term_le_one (l : ℕ) [Fact l.Prime] (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (a : Formalism.Per.Ainf l) (n : ℕ) :
    ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n ≤ 1 := by
  have hx0 : 0 ≤ ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ := norm_nonneg _
  have hx1 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 ((a.coeff n).untilt).2
  have he : 0 ≤ (1 : ℝ) / (l : ℝ) ^ n := by positivity
  have h2 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) ≤ 1 :=
    Real.rpow_le_one hx0 hx1 he
  have h3 : ρ ^ n ≤ 1 := pow_le_one₀ h0 h1
  calc _ ≤ 1 * 1 := mul_le_mul h2 h3 (pow_nonneg h0 n) zero_le_one
    _ = 1 := one_mul 1

theorem gC_teich_sub_eq_one : ∀ (l : ℕ) [Fact l.Prime] (ζ ζ' : Formalism.Per.Fl l),
    ‖(((ζ - ζ').untilt : Formalism.Per.OC l) : ℂ_[l])‖ = 1 →
      ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (tc l ζ - tc l ζ') = 1 := by
  intro l _ ζ ζ' hζ ρ hρ hρ1
  have hex : ∃ N, IsGauss l ρ N := GlobalTheory.GaussExt.exists_gauss_acris l ρ hρ hρ1
  have hg : IsGauss l ρ (Classical.choose hex) := Classical.choose_spec hex
  have hC : gC l ρ (tc l ζ - tc l ζ') = Classical.choose hex (tc l ζ - tc l ζ') := by
    unfold gC; rw [dif_pos hex]
  have hsub : tc l ζ - tc l ζ' =
      algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.tm ζ - Formalism.Per.tm ζ') := by
    unfold tc; rw [map_sub]
  rw [hC, hsub, hg.2.2.2.2]
  have hl : (0 : ℝ) < (l : ℝ)⁻¹ := by
    have : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  have h0 : 0 ≤ ρ := le_of_lt (lt_of_lt_of_le hl hρ)
  have hc0 : (Formalism.Per.tm ζ - Formalism.Per.tm ζ').coeff 0 = ζ - ζ' := by
    have := map_sub (WittVector.constantCoeff (p := l) (R := Formalism.Per.Fl l)) (Formalism.Per.tm ζ) (Formalism.Per.tm ζ')
    simpa [Formalism.Per.tm] using this
  unfold gA
  apply le_antisymm
  · exact ciSup_le (fun n => gA_term_le_one l ρ h0 hρ1.le _ n)
  · have hb : BddAbove (Set.range fun n : ℕ =>
        ‖((((Formalism.Per.tm ζ - Formalism.Per.tm ζ').coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^
          ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n) :=
      ⟨1, by rintro _ ⟨n, rfl⟩; exact gA_term_le_one l ρ h0 hρ1.le _ n⟩
    refine le_trans ?_ (le_ciSup hb 0)
    simp [hc0, hζ]

end GlobalTheory.PMon.Gauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisUniqueStatement
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussNormAcris_unique : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ) (N N' : Formalism.Per.Acris l → ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → IsGauss l ρ N → IsGauss l ρ N' → N = N' := by
  first | exact @GlobalTheory.PMon.Gauss.isGauss_unique | exact GlobalTheory.PMon.Gauss.isGauss_unique | (intros; apply GlobalTheory.PMon.Gauss.isGauss_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
section
namespace GlobalTheory.Per

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

private theorem isIntegral_iff_spectralNorm_le_one' {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra ℚ_[p] K]
    [Algebra.IsAlgebraic ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] (x : K) :
    IsIntegral ℤ_[p] x ↔ spectralNorm ℚ_[p] K x ≤ 1 := by
  have hx : IsIntegral ℚ_[p] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hlift : minpoly ℚ_[p] x ∈ Polynomial.lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨(minpoly ℚ_[p] x).coeff n, h n⟩, rfl⟩
    obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (minpoly.monic hx)
    refine ⟨g, hgm, ?_⟩
    have h0 := minpoly.aeval ℚ_[p] x
    rw [← hg, Polynomial.aeval_map_algebraMap, Polynomial.aeval_def] at h0
    exact h0

private theorem spectralNorm_mul_zpadic {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra ℚ_[p] K]
    [Algebra.IsAlgebraic ℚ_[p] K] (x y : K) :
    spectralNorm ℚ_[p] K (x * y) = spectralNorm ℚ_[p] K x * spectralNorm ℚ_[p] K y := by
  simpa only [spectralMulAlgNorm_def] using map_mul (spectralMulAlgNorm ℚ_[p] K) x y

private theorem isUnit_iff_spectralNorm_eq_one {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra ℚ_[p] K]
    [Algebra.IsAlgebraic ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]
    (b : integralClosure ℤ_[p] K) : IsUnit b ↔ spectralNorm ℚ_[p] K (b : K) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ((u : integralClosure ℤ_[p] K) : K) * ((u⁻¹ : (integralClosure ℤ_[p] K)ˣ) : K) = 1 := by
      have := congrArg (fun z : integralClosure ℤ_[p] K => (z : K)) u.mul_inv
      simpa only [Subalgebra.coe_mul, Subalgebra.coe_one] using this
    have h2 := congrArg (spectralNorm ℚ_[p] K) h1
    rw [spectralNorm_mul_zpadic, spectralNorm_one] at h2
    have ha := (isIntegral_iff_spectralNorm_le_one' _).mp (u : integralClosure ℤ_[p] K).2
    have hb := (isIntegral_iff_spectralNorm_le_one' _).mp ((u⁻¹ : (integralClosure ℤ_[p] K)ˣ) : integralClosure ℤ_[p] K).2
    have ha0 := spectralNorm_nonneg (K := ℚ_[p]) ((u : integralClosure ℤ_[p] K) : K)
    have hb0 := spectralNorm_nonneg (K := ℚ_[p])
      (((u⁻¹ : (integralClosure ℤ_[p] K)ˣ) : integralClosure ℤ_[p] K) : K)
    nlinarith
  · intro h
    have hb0 : (b : K) ≠ 0 := by
      intro h0
      rw [h0, spectralNorm_zero] at h
      exact zero_ne_one h
    have hinv : IsIntegral ℤ_[p] (b : K)⁻¹ := by
      rw [isIntegral_iff_spectralNorm_le_one']
      have h2 := spectralNorm_mul_zpadic (p := p) (b : K) (b : K)⁻¹
      rw [mul_inv_cancel₀ hb0, spectralNorm_one, h, one_mul] at h2
      exact h2.symm.le
    exact isUnit_iff_exists_inv.mpr ⟨⟨(b : K)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hb0)⟩

private theorem isLocalRing_integralClosure_zpadic {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra ℚ_[p] K]
    [Algebra.IsAlgebraic ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] :
    IsLocalRing (integralClosure ℤ_[p] K) := by
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb hab
  have hlt : ∀ c : integralClosure ℤ_[p] K, ¬IsUnit c → spectralNorm ℚ_[p] K (c : K) < 1 :=
    fun c hc => lt_of_le_of_ne ((isIntegral_iff_spectralNorm_le_one' _).mp c.2) (fun h => hc ((isUnit_iff_spectralNorm_eq_one c).mpr h))
  have h1 := hlt a ha
  have h2 := hlt b hb
  have h3 := (isUnit_iff_spectralNorm_eq_one (a + b)).mp hab
  have h4 := isNonarchimedean_spectralNorm (K := ℚ_[p]) (L := K) (a : K) (b : K)
  have h5 : ((a + b : integralClosure ℤ_[p] K) : K) = (a : K) + (b : K) := rfl
  rw [h5] at h3
  rw [h3] at h4
  exact absurd h4 (not_le.mpr (max_lt h1 h2))

private theorem isPrecomplete_maximalIdeal_of_free_finite_zpadic {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]
    [Module ℤ_[p] M] [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M] :
    IsPrecomplete (IsLocalRing.maximalIdeal ℤ_[p]) M := by
  classical
  set b := Module.Free.chooseBasis ℤ_[p] M
  have key : ∀ (n : ℕ) (x : M), x ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n • (⊤ : Submodule ℤ_[p] M) ↔
      ∀ i, b.equivFun x i ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n := by
    intro n x
    constructor
    · intro hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr m _ i
        simp only [map_smul, Pi.smul_apply, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
      · intro x y hx hy i
        simp only [map_add, Pi.add_apply]
        exact add_mem (hx i) (hy i)
    · intro h
      rw [← b.sum_equivFun x]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top)
  have key1 : ∀ (n : ℕ) (y : ℤ_[p]),
      y ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n • (⊤ : Submodule ℤ_[p] ℤ_[p]) ↔
        y ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n := by
    intro n y
    change y ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n • (⊤ : Ideal ℤ_[p]) ↔ _
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  rw [isPrecomplete_iff]
  intro f hf
  have hc : ∀ i, ∃ L : ℤ_[p], ∀ n, b.equivFun (f n) i ≡ L
      [SMOD ((IsLocalRing.maximalIdeal ℤ_[p]) ^ n • ⊤ : Submodule ℤ_[p] ℤ_[p])] := by
    intro i
    refine IsPrecomplete.prec inferInstance ?_
    intro m n hmn
    rw [SModEq.sub_mem, key1]
    have := (key m _).mp (SModEq.sub_mem.mp (hf hmn)) i
    simpa only [map_sub, Pi.sub_apply] using this
  choose L hL using hc
  refine ⟨b.equivFun.symm L, fun n => ?_⟩
  rw [SModEq.sub_mem, key]
  intro i
  have := (key1 n _).mp (SModEq.sub_mem.mp (hL i n))
  simpa only [map_sub, Pi.sub_apply, LinearEquiv.apply_symm_apply] using this

private theorem isPrecomplete_of_isPrecomplete_pow {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (he : 0 < e)
    (h : IsPrecomplete (I ^ e) R) : IsPrecomplete I R := by
  rw [isPrecomplete_iff]
  intro f hf
  obtain ⟨L, hL⟩ := h.prec (f := fun k => f (e * k)) (fun {m n} hmn => by
    rw [← pow_mul]
    exact hf (Nat.mul_le_mul_left e hmn))
  refine ⟨L, fun n => ?_⟩
  have hn : n ≤ e * n := by nlinarith
  have h1 : f n ≡ f (e * n) [SMOD (I ^ n • ⊤ : Submodule R R)] := hf hn
  have h2 := hL n
  rw [← pow_mul] at h2
  exact h1.trans (h2.mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hn)))

private theorem isAdicComplete_maximalIdeal_of_free_finite_zpadic {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra ℤ_[p] B] [Module.Free ℤ_[p] B] [Module.Finite ℤ_[p] B]
    (hp0 : (p : B) ≠ 0) (hpu : ¬IsUnit (p : B)) :
    IsAdicComplete (IsLocalRing.maximalIdeal B) B := by
  have hJ : (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] B) = Ideal.span {(p : B)} := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  have hprecJ : IsPrecomplete ((IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] B)) B :=
    IsPrecomplete.map_algebraMap_iff.mpr isPrecomplete_maximalIdeal_of_free_finite_zpadic
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {(p : B)}) (by rwa [Ne, Ideal.span_singleton_eq_bot]) hϖ
  rw [← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq] at he
  have he0 : 0 < e := Nat.pos_of_ne_zero (fun h => by
    rw [h, pow_zero, Ideal.one_eq_top] at he
    exact hpu (Ideal.span_singleton_eq_top.mp he))
  have hprec : IsPrecomplete (IsLocalRing.maximalIdeal B ^ e) B := by
    rw [← he, ← hJ]
    exact hprecJ
  exact { toIsHausdorff := inferInstance,
          toIsPrecomplete := isPrecomplete_of_isPrecomplete_pow _ e he0 hprec }

theorem integers_completeDVR : ∀ (l : ℕ) [Fact l.Prime], ∀ LL : FinExt l,
    ∃ _ : IsDiscreteValuationRing ↥(OL LL),
      IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) ∧ ((l : ℕ) : ↥(OL LL)) ≠ 0 ∧
      ¬ IsUnit ((l : ℕ) : ↥(OL LL)) ∧ Module.Free ℤ_[l] ↥(OL LL) ∧ Module.Finite ℤ_[l] ↥(OL LL) ∧
      IsFractionRing ↥(OL LL) ↥LL.1 := by
  intro l _ LL
  unfold OL
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : Algebra.IsAlgebraic ℚ_[l] ↥LL.1 := Algebra.IsAlgebraic.of_finite ℚ_[l] ↥LL.1
  have hloc : IsLocalRing (integralClosure ℤ_[l] ↥LL.1) := isLocalRing_integralClosure_zpadic
  have hN : spectralNorm ℚ_[l] ↥LL.1 (((l : ℕ) : integralClosure ℤ_[l] ↥LL.1) : ↥LL.1) =
      (l : ℝ)⁻¹ := by
    have : (((l : ℕ) : integralClosure ℤ_[l] ↥LL.1) : ↥LL.1) = algebraMap ℚ_[l] ↥LL.1 (l : ℚ_[l]) := by
      simp
    rw [this, spectralNorm_extends, Padic.norm_p]
  have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl0 : (l : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have hpu : ¬IsUnit ((l : ℕ) : integralClosure ℤ_[l] ↥LL.1) := by
    intro h
    have := (isUnit_iff_spectralNorm_eq_one _).mp h
    rw [hN] at this
    exact absurd this hl1.ne
  have hp0 : ((l : ℕ) : integralClosure ℤ_[l] ↥LL.1) ≠ 0 := by
    intro h
    rw [h] at hN
    simp only [ZeroMemClass.coe_zero, spectralNorm_zero] at hN
    exact hl0 hN.symm
  have hnf : ¬IsField (integralClosure ℤ_[l] ↥LL.1) := by
    intro h
    obtain ⟨c, hc⟩ := h.mul_inv_cancel hp0
    exact hpu (isUnit_iff_exists_inv.mpr ⟨c, hc⟩)
  have hded : IsDedekindDomain (integralClosure ℤ_[l] ↥LL.1) := inferInstance
  have hdvr : IsDiscreteValuationRing (integralClosure ℤ_[l] ↥LL.1) :=
    ((IsDiscreteValuationRing.TFAE _ hnf).out 0 2).mpr hded
  have hfin : Module.Finite ℤ_[l] (integralClosure ℤ_[l] ↥LL.1) := inferInstance
  have htf : Module.IsTorsionFree ℤ_[l] (integralClosure ℤ_[l] ↥LL.1) := by
    refine ⟨fun r hr x y hxy => ?_⟩
    have hr0 : r ≠ 0 := hr.ne_zero
    have hne : algebraMap ℤ_[l] ↥LL.1 r ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]
      exact (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).mpr hr0)
    have h : ((r • x : integralClosure ℤ_[l] ↥LL.1) : ↥LL.1) =
        ((r • y : integralClosure ℤ_[l] ↥LL.1) : ↥LL.1) := congrArg Subtype.val hxy
    change r • (x : ↥LL.1) = r • (y : ↥LL.1) at h
    rw [Algebra.smul_def, Algebra.smul_def] at h
    exact Subtype.ext (mul_left_cancel₀ hne h)
  have hfree : Module.Free ℤ_[l] (integralClosure ℤ_[l] ↥LL.1) :=
    Module.free_of_finite_type_torsion_free'
  exact ⟨hdvr, isAdicComplete_maximalIdeal_of_free_finite_zpadic hp0 hpu, hp0, hpu, hfree, hfin,
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1⟩

end GlobalTheory.Per
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutiveAlgebraProductIdentityStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.involutive_algebra_product_identity : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → (∃ e ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A), e * e = e ∧ e + (B₁.prod B₂).σ e = 1) → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.Swap.identity_of_swap | exact GlobalTheory.UnitLemma.Swap.identity_of_swap | (intros; apply GlobalTheory.UnitLemma.Swap.identity_of_swap <;> assumption)
end

