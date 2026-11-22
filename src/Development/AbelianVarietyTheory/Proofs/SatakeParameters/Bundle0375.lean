import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0350
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0349
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0363
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0362
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0372
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0348
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0373
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0032
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0367
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0370
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0009
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0342
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0327
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0303
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoUnitsAtPlaceUniformizingIdele

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleFrameScalarOddPositionsDet
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem zpow_toNat_div' {K : Type} [Field K] (x : K) (hx : x ≠ 0) (e : ℤ) :
    x ^ e.toNat * (x ^ (-e).toNat)⁻¹ = x ^ e := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hx]
  congr 1
  omega

theorem blk_scal_odd {K : Type} [Field K] (c δ : K) (hc : c ≠ 0) (hδ : δ ≠ 0) (N : ℕ) (hN : 1 ≤ N) (cM sz : ℤ)
    (h0 : 0 ≤ (N : ℤ) * cM - sz) :
    ((c * δ⁻¹) ^ (N - 1)) ^ ((N : ℤ) * cM - sz).toNat *
      ((δ⁻¹) ^ (cM - sz).toNat * ((c * δ⁻¹) ^ N) ^ (cM - (N : ℤ) * cM + sz).toNat) *
      ((δ⁻¹) ^ (-(cM - sz)).toNat * ((c * δ⁻¹) ^ N) ^ (-(cM - (N : ℤ) * cM + sz)).toNat)⁻¹ =
    c ^ sz * δ ^ (-cM) := by
  have hκ : c * δ⁻¹ ≠ 0 := mul_ne_zero hc (inv_ne_zero hδ)
  have hd : δ⁻¹ ≠ 0 := inv_ne_zero hδ
  have hκN : (c * δ⁻¹) ^ N ≠ 0 := pow_ne_zero _ hκ
  have e1 : ((c * δ⁻¹) ^ (N - 1)) ^ ((N : ℤ) * cM - sz).toNat = (c * δ⁻¹) ^ (((N : ℤ) - 1) * ((N : ℤ) * cM - sz)) := by
    rw [← pow_mul, ← zpow_natCast]
    congr 1
    push_cast [Int.toNat_of_nonneg h0, Nat.cast_sub hN]
    ring
  calc _ = ((c * δ⁻¹) ^ (N - 1)) ^ ((N : ℤ) * cM - sz).toNat *
        ((δ⁻¹) ^ (cM - sz).toNat * ((δ⁻¹) ^ (-(cM - sz)).toNat)⁻¹) *
        (((c * δ⁻¹) ^ N) ^ (cM - (N : ℤ) * cM + sz).toNat * (((c * δ⁻¹) ^ N) ^ (-(cM - (N : ℤ) * cM + sz)).toNat)⁻¹) := by
          ring
    _ = (c * δ⁻¹) ^ (((N : ℤ) - 1) * ((N : ℤ) * cM - sz)) * (δ⁻¹) ^ (cM - sz) *
        (c * δ⁻¹) ^ ((N : ℤ) * (cM - (N : ℤ) * cM + sz)) := by
          rw [zpow_toNat_div' _ hd, zpow_toNat_div' _ hκN, e1, ← zpow_natCast (c * δ⁻¹) N, ← zpow_mul]
    _ = c ^ (((N : ℤ) - 1) * ((N : ℤ) * cM - sz) + (N : ℤ) * (cM - (N : ℤ) * cM + sz)) *
        δ ^ (-(((N : ℤ) - 1) * ((N : ℤ) * cM - sz)) + -(cM - sz) + -((N : ℤ) * (cM - (N : ℤ) * cM + sz))) := by
          rw [mul_zpow, mul_zpow, inv_zpow', inv_zpow', inv_zpow', zpow_add₀ hc, zpow_add₀ hδ, zpow_add₀ hδ]
          ring
    _ = _ := by
          congr 2 <;> ring

set_option maxHeartbeats 1000000 in

theorem scal_tauV : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (c : Kc), c ≠ 0 → ∀ (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → GlobalTheory.FrameB.sS X Kc j (GlobalTheory.FrameB.kV Kc fd c j La') * GlobalTheory.FrameB.kN X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') (GlobalTheory.FrameB.kV Kc fd c j La') * (GlobalTheory.FrameB.kD X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') (GlobalTheory.FrameB.kV Kc fd c j La'))⁻¹ = ∏ τ, if IsOddPos (pos.symm τ).2 then c ^ szT X D pos j τ * ι (embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det) ^ cT1 X D pos j τ else 1 := by
  intro p _ X D pos Kc _ _ _ ι ρ hT fd c hc j hN La' M hU hFr ν hν
  obtain ⟨-, hsz, -, hle, -⟩ := GlobalTheory.T.modelPartition_size_extension_firstLast_rows X D pos j hN ν hν
  have hN1 : 1 ≤ NN X.G.P.m X.t j := by unfold NN; omega

  have hdet : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), (GlobalTheory.FrameB.mk Kc fd j La' v s).det =
      Formalism.L2.G.Pend.tw X Kc v s (ρ v (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det) := by
    intro v s
    unfold GlobalTheory.FrameB.mk
    rw [det_mAt, hFr v, Matrix.det_submatrix_equiv_self, RingHom.map_det (ρ v)]
    rfl
  have hdet0 : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), (GlobalTheory.FrameB.mk Kc fd j La' v s).det ≠ 0 := by
    intro v s
    rw [hdet]
    exact (((M.isUnit.map (Matrix.detMonoidHom))).map (ρ v)).map (Formalism.L2.G.Pend.tw X Kc v s) |>.ne_zero

  have hbd : ∀ b : (Σ v : X.Pl, Fin (X.G.P.n' v)),
      0 ≤ (NN X.G.P.m X.t j : ℤ) * cMu X j b.1 b.2 - szMu X j b.1 b.2 := by
    intro b
    have h1 : szMu X j b.1 b.2 = szT X D pos j (pos b) := by
      show _ = szMu X j (pos.symm (pos b)).1 (pos.symm (pos b)).2; rw [Equiv.symm_apply_apply]
    have h2 : cMu X j b.1 b.2 = cT1 X D pos j (pos b) := by
      show _ = cMu X j (pos.symm (pos b)).1 (pos.symm (pos b)).2; rw [Equiv.symm_apply_apply]
    rw [h1, h2, hsz, ← hN.1]
    have : ∑ r : Fin (D.R.N j), (ν (pos b) r : ℤ) ≤ ∑ _r : Fin (D.R.N j), cT1 X D pos j (pos b) := by
      refine Finset.sum_le_sum fun r _ => ?_
      have := hle (pos b) (Fin.castLE (rk_le X D hN) r)
      simpa [extNu] using this
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  have hkN : GlobalTheory.FrameB.kN X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') (GlobalTheory.FrameB.kV Kc fd c j La') =
      ∏ b : (Σ v : X.Pl, Fin (X.G.P.n' v)), if IsOddPos b.2 then
        ((GlobalTheory.FrameB.wV Kc fd c j La' b.1 b.2).det⁻¹) ^ (exY X j b.1 b.2).toNat *
          (GlobalTheory.FrameB.kV Kc fd c j La' b.1 b.2 ^ NN X.G.P.m X.t j) ^ (exT X j b.1 b.2).toNat else 1 := by
    unfold GlobalTheory.FrameB.kN
    rw [Fintype.prod_sigma]
  have hkD : GlobalTheory.FrameB.kD X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') (GlobalTheory.FrameB.kV Kc fd c j La') =
      ∏ b : (Σ v : X.Pl, Fin (X.G.P.n' v)), if IsOddPos b.2 then
        ((GlobalTheory.FrameB.wV Kc fd c j La' b.1 b.2).det⁻¹) ^ (-exY X j b.1 b.2).toNat *
          (GlobalTheory.FrameB.kV Kc fd c j La' b.1 b.2 ^ NN X.G.P.m X.t j) ^ (-exT X j b.1 b.2).toNat else 1 := by
    unfold GlobalTheory.FrameB.kD
    rw [Fintype.prod_sigma]
  rw [← Fintype.prod_equiv pos _ _ (fun _ => rfl), hkN, hkD, GlobalTheory.FrameB.sS, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  beta_reduce
  rw [Equiv.symm_apply_apply]
  by_cases ho : IsOddPos b.2
  · simp only [if_pos ho]
    have hw : GlobalTheory.FrameB.wV Kc fd c j La' b.1 b.2 = GlobalTheory.FrameB.mk Kc fd j La' b.1 b.2 := by
      unfold GlobalTheory.FrameB.wV; rw [if_pos ho]
    have hk : GlobalTheory.FrameB.kV Kc fd c j La' b.1 b.2 = c * (GlobalTheory.FrameB.mk Kc fd j La' b.1 b.2).det⁻¹ := by
      unfold GlobalTheory.FrameB.kV; rw [if_pos ho]
    rw [hw, hk, exY, exT, blk_scal_odd c _ hc (hdet0 b.1 b.2) _ hN1 _ _ (hbd b)]
    have h1 : szMu X j b.1 b.2 = szT X D pos j (pos b) := by
      show _ = szMu X j (pos.symm (pos b)).1 (pos.symm (pos b)).2; rw [Equiv.symm_apply_apply]
    have h2 : cMu X j b.1 b.2 = cT1 X D pos j (pos b) := by
      show _ = cMu X j (pos.symm (pos b)).1 (pos.symm (pos b)).2; rw [Equiv.symm_apply_apply]
    have h3 := (GlobalTheory.T.unitaryBlockMatrices_read_in_placeField X D pos Kc ι ρ hT M hU b.1 b.2).2
    rw [if_pos ho] at h3
    rw [h1, h2, hdet, h3, ← zpow_mul]
    congr 2
    ring
  · simp only [if_neg ho]
    simp

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleMoveScalarPowerOfPStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTupleMove_scalar_power_of_p : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → S.Pair → ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → ∀ La' : (sysS H X std).Lt (j + 1), ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; GlobalTheory.TwU.pPow (sysS H X std) j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La))) ((J.fd std).kerN (j + 1) La'))⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹)) = (kapG (sysS H X std) ℂ_[D.what₂.places.resChar w] j c γ)⁻¹ * (GlobalTheory.TwU.pPow (sysS H X std) j (c, La) La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, La) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, La)) ((J.fd std).kerN (j + 1) La'))⁻¹))) := by
  first | exact @GlobalTheory.TwV.Xc.moveBy_scal | exact GlobalTheory.TwV.Xc.moveBy_scal | (intros; apply GlobalTheory.TwV.Xc.moveBy_scal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleReadingEqOfRealisingPolynomial
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Formalism.MainNotions.G.CmpJ.PStabEq

namespace GlobalTheory.TwV.DelA

theorem castSt_K_U {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (e : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    (S : GlobalTheory.TwU.StepCharts C i hi) (c : C.cls i) :
    ((castSt e S).K ((castSt e S).chOf (castCls e i c))).lev.U = (S.K (S.chOf c)).lev.U := by
  subst e; rfl

theorem castSt_y {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (e : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    (S : GlobalTheory.TwU.StepCharts C i hi) (c : C.cls i) :
    (castSt e S).y (castCls e i c) = S.y c := by
  subst e; rfl

set_option maxHeartbeats 2000000 in

theorem rdJ_eq_of_realAt : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ (φ : (D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) (V : XR ((sysS H X std).Pj (j + 1)) ℂ), (∀ d : Dec J std, RealAt d (j + 1) hj h La φ V) → rdJ I X.onCh ι j La.1 La.2 φ = MvPolynomial.map ι V) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict ι j hj h La hLa φ V hR
  refine rdJ_of_isValV I X.onCh H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds ι j hj La.1 La.2 hLa φ V ?_
  intro g hg c γ hγ κ hpt z z' hz
  have hcls : IsCG (I.at' j hj).st La.1 La.2 c.1 γ :=
    ⟨_, _, c.2, g, κ, (I.at' j hj).st.eC.apply_symm_apply La.1, hg, hγ, hpt⟩
  have hc0 : clsOf (H.core j hj) La.1 La.2 = c.1 := clsOf_eq (H.core j hj) hcls
  have hclsAt : clsAt X H (j + 1) La.1 La.2 = castCls (X.onCh j hj) (j + 1) c.1 := by
    rw [clsAt_succ X H j hj, hc0]
  obtain ⟨g', hg', hpt'⟩ := GlobalTheory.T.latticeTupleSuccLevel_point_isComponentPointInChart S hDict j hj La hLa
  have hx : Formalism.UG.bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ *
      (((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y c).1 * κ.1 ∈
      UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (bc_mem hγ) (((I.at' j hj).st.K _).y c).2) (U_le κ.2)
  obtain ⟨κ₀, e₀, hχ₀⟩ := Formalism.L2.G.ptOne_of ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev
    (H.core j hj ((I.at' j hj).st.eC.symm La.1).1).int (H.core j hj ((I.at' j hj).st.eC.symm La.1).1).hypP (H.core j hj ((I.at' j hj).st.eC.symm La.1).1).bad_p ((I.at' j hj).st.eC.symm La.1).2 La.2 g g' ⟨_, hx⟩
    (J.pt std (j + 1) hj La) hg hg' hpt hpt'
  have hU : ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U =
      ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.U := by
    unfold Joint.chart
    rw [hclsAt, J.st j hj, castSt_K_U]
    exact congrArg (fun β => ((I.at' j hj).st.K β).lev.U) c.2
  have hy : ((J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2)).1 =
      (((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y c).1 := by
    rw [hclsAt, J.st j hj, castSt_y]
    exact congrArg Subtype.val ((GlobalTheory.TwU.StepCharts.ofStepIn (I.at' j hj).st).y_eq c).symm
  let κ' : ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U := ⟨(κ * κ₀).1, by rw [hU]; exact (κ * κ₀).2⟩
  obtain ⟨d, hdγ, hdκ⟩ := GlobalTheory.T.latticeTupleDecomposition_occurs_in_family S hDict j hj La hLa γ hγ κ' (by
    rw [e₀, hy]
    show _ = _ * _ * (κ.1 * κ₀.1)
    simp only [mul_assoc])
  obtain ⟨c₂, κ₂, hc₂, hκ₂, -, hiff⟩ := GlobalTheory.T.realAt_succ_iff_decomposition_values S d j hj h La hLa
  have ec : c₂ = c := Subtype.ext (castCls_inj (X.onCh j hj) (j + 1) (hc₂.trans hclsAt))
  have eκ : κ₂ = κ * κ₀ := Subtype.ext (hκ₂.trans (by rw [hdκ]))
  have key := (hiff φ V).1 (hR d) z z' (by rw [hdγ]; exact hz)
  rw [key, ec, eκ, map_mul, Units.val_mul, hχ₀, mul_one]

end GlobalTheory.TwV.DelA

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorIdentityLeftSideComplexPointStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operatorIdentity_leftSide_complexPoint : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → evD X D pos ι hN d f' (subD X Kc j G * numD X Kc j) * ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) = evD X D pos ι hN d f' (denD X Kc j) * ι (sgO X D pos j * (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * GL3Theta.evFr D Q (dfr X D hN d f')) := by
  first | exact @GlobalTheory.TwV.DelA.leftSide_at_point | exact GlobalTheory.TwV.DelA.leftSide_at_point | (intros; apply GlobalTheory.TwV.DelA.leftSide_at_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChartBasisDetNormOneStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalChartBasis_det_norm_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j ≤ D.R.m) (a : Lv.comp j) τ, ‖ι (embT D τ (uB J j hj a).1.det)‖ = 1) := by
  first | exact @GlobalTheory.TwV.DelA.uB_det_unit | exact GlobalTheory.TwV.DelA.uB_det_unit | (intros; apply GlobalTheory.TwV.DelA.uB_det_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TargetStepScalarEqStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.targetStep_scalar_eq : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (La' : (sysS H X std).Lt (j + 1)), dPow (mM d (j + 1) hj La').1 (fun τ => -(wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) * sPt d (j + 1) hj La' = d.uT S j La' * kT J j hj La'.1) := by
  first | exact @GlobalTheory.TwV.DelA.target_scalar | exact GlobalTheory.TwV.DelA.target_scalar | (intros; apply GlobalTheory.TwV.DelA.target_scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesScalarBoundedOfPosPairStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_scalar_bounded_of_pos_pair : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → S.Pair → S.Scal) := by
  first | exact @GlobalTheory.TwV.Xc.scal_of_pos_pair | exact GlobalTheory.TwV.Xc.scal_of_pos_pair | (intros; apply GlobalTheory.TwV.Xc.scal_of_pos_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesSiteEqChangedFrameClassSeriesStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_site_eq_changedFrame_classSeries : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → ∀ (d : Dec J std), ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j < D.R.m, d.SerAt S ι j) := by
  first | exact @GlobalTheory.TwV.DelB.serAt_all | exact GlobalTheory.TwV.DelB.serAt_all | (intros; apply GlobalTheory.TwV.DelB.serAt_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedPolynomialComplexPointEvaluation
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.DelA

open MvPolynomial

theorem transpC_eval_aeval {σ κ : Type} (x : κ → ℂ) (g : σ → MvPolynomial κ ℂ) (Q : MvPolynomial σ ℂ) :
    eval x (aeval g Q) = eval (fun i => eval x (g i)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p v hp => rw [map_mul, map_mul, hp, map_mul, aeval_X, eval_X]

theorem transpC_map_eval {σ Kc : Type} [CommRing Kc] (ι : ℂ →+* Kc) (x : σ → ℂ) (R : MvPolynomial σ ℂ) :
    eval (fun i => ι (x i)) (map ι R) = ι (eval x R) := by
  induction R using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p v hp => rw [map_mul, map_mul, hp, map_mul, map_X, eval_X, eval_X, map_mul]

theorem transpC_hom_aeval {σ ι' κ : Type} (φ : MvPolynomial ι' (MvPolynomial κ ℂ) →+* ℂ) (hφ : ∀ c, φ (C (C c)) = c)
    (g : σ → MvPolynomial ι' (MvPolynomial κ ℂ)) (Q : MvPolynomial σ ℂ) :
    φ (aeval g Q) = eval (fun i => φ (g i)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.algebraMap_apply, hφ]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p v hp => rw [map_mul, map_mul, hp, map_mul, aeval_X, eval_X]

theorem evFr_scalar_of_wtPol (D : D7) {N : ℕ} (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (hQ : Q ∈ WtPol ℂ ν) (s : D.what₂.Tau → ℂ) (hs : ∀ τ, s τ ≠ 0) (y : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) :
    GL3Theta.evFr D Q (fun τ => s τ • y τ) = (∏ τ, ∏ r, s τ ^ ν τ r) * GL3Theta.evFr D Q y := by
  have hB : IsBor (fun τ => s τ • (1 : Matrix (Fin N) (Fin N) ℂ)) := fun τ =>
    ⟨fun r c hcr => by simp [Matrix.one_apply_ne hcr.ne'], fun r => by simp [hs τ]⟩
  have h1 : colSub (fun τ => s τ • (1 : Matrix (Fin N) (Fin N) ℂ)) Q = _ := hQ _ hB
  have h2 := congrArg (eval (fun k : GL3Theta.FrV D N => y k.1 k.2.1 k.2.2)) h1
  simp only [colSub, transpC_eval_aeval, smul_eval] at h2
  have h3 : (∏ τ, ∏ r, (s τ • (1 : Matrix (Fin N) (Fin N) ℂ)) r r ^ ν τ r) = ∏ τ, ∏ r, s τ ^ ν τ r := by simp
  rw [h3] at h2
  unfold GL3Theta.evFr
  rw [← h2]
  refine congrArg (fun x => eval x Q) ?_
  funext k
  simp [Matrix.smul_apply, Matrix.one_apply, mul_comm]

theorem transpC_polDY_eval (D : D7) {N N' : ℕ} (hle : N ≤ N') (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (d : D.what₂.Tau → Matrix (Fin N) (Fin N') ℂ) (f' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) :
    MvPolynomial.eval₂Hom (MvPolynomial.eval (fun k : GL3Theta.FrV D N' => f' k.1 k.2.1 k.2.2)) (fun k : GL3Theta.Idx D N N' => d k.1 k.2.2 k.2.1)
        (polDY D s Q (N' := N')) =
      GL3Theta.evFr D Q (fun τ => s τ • (d τ * f' τ).submatrix id (Fin.castLE hle)) := by
  unfold polDY
  rw [transpC_hom_aeval _ (fun c => by simp)]
  unfold GL3Theta.evFr
  refine congrArg (fun x => MvPolynomial.eval x Q) ?_
  funext k
  have hk : ((k.2.2 : Fin N) : ℕ) < N' := lt_of_lt_of_le k.2.2.2 hle
  simp [dfr, Matrix.mul_apply, Finset.mul_sum, hk]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_assoc, mul_comm (f' k.1 b _)]
  rfl

theorem evD_trDY_polDY : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → evD X D pos ι hN d f' (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) * ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) = ι ((∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * (∏ τ, s τ ^ szT X D pos j τ) * GL3Theta.evFr D Q (dfr X D hN d f')) := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ s hs d f' hf
  classical
  have h' := rkT X D hN
  obtain ⟨-, hsz, -, hle, -⟩ := GlobalTheory.T.modelPartition_size_extension_firstLast_rows X D pos j hN ν hν
  have hco := (GlobalTheory.T.operatorPolynomial_coeffs_weight_extended_by_zero D (rk_le X D hN) s ν Q hQ).1
  have hreal : ∀ α, Realises X D pos (j + 1) h' (wT X D pos j) (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1))))
      (phiC X D pos (j + 1) h' (wT X D pos j) (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1))))) := by
    intro α
    obtain ⟨R, hR⟩ := GlobalTheory.T.frame_polynomials_weight_realised_next_level X D pos j h' (extNu _ ν) hle _ (hco α)
    exact selOf_mem (relPhi X D pos (j + 1) h' (wT X D pos j)) _ (Submodule.mem_map.2 ⟨(_, R), hR, rfl⟩)
  let F : Fr1 D (D.R.N (j + 1)) := ⟨f', fun τ => isUnit_iff_ne_zero.2 (hf τ)⟩
  have hval : ∀ α, (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) *
      valZ X D pos (j + 1) h' (phiC X D pos (j + 1) h' (wT X D pos j) (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1))))) f' =
      (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * GL3Theta.evFr D (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1)))) f' := by
    intro α
    have := hreal α F
    rw [ev1_eq_prod_det_pow_mul_valZ] at this
    exact this
  have hD : evD X D pos ι hN d f' (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) =
      ι (∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support,
        valZ X D pos (j + 1) h' (phiC X D pos (j + 1) h' (wT X D pos j) (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1))))) f' *
          ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k) := by
    unfold trDY
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    unfold evD
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial,
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    unfold phi0
    rw [dif_pos h', map_mul, map_prod]
    congr 1
    · unfold valZ
      exact transpC_map_eval ι _ _
    · unfold Finsupp.prod
      refine Finset.prod_congr rfl fun k _ => ?_
      simp [eIdx, map_pow]
  have hP : ∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support,
        GL3Theta.evFr D (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1)))) f' * ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k =
      (∏ τ, s τ ^ szT X D pos j τ) * GL3Theta.evFr D Q (dfr X D hN d f') := by
    let φ : MvPolynomial (GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1))) (MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ) →+* ℂ :=
      MvPolynomial.eval₂Hom (MvPolynomial.eval (fun k : GL3Theta.FrV D (D.R.N (j + 1)) => f' k.1 k.2.1 k.2.2))
        (fun k => d k.1 k.2.2 k.2.1)
    have e1 : φ (polDY D s Q (N' := D.R.N (j + 1))) = ∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support,
        GL3Theta.evFr D (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1)))) f' * ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k := by
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
      rfl
    have e2 : φ (polDY D s Q (N' := D.R.N (j + 1))) = GL3Theta.evFr D Q (fun τ => s τ • dfr X D hN d f' τ) :=
      transpC_polDY_eval D (rk_le X D hN) s Q d f'
    have e3 : ∀ τ, ∏ r, s τ ^ ν τ r = s τ ^ szT X D pos j τ := by
      intro τ
      rw [hsz τ, Finset.prod_pow_eq_pow_sum, ← Nat.cast_sum, zpow_natCast]
    rw [← e1, e2, evFr_scalar_of_wtPol D ν Q hQ s hs]
    simp only [e3]
  rw [hD, ← map_mul]
  congr 1
  rw [Finset.sum_mul]
  calc _ = ∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support, (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) *
        (GL3Theta.evFr D (MvPolynomial.coeff α (polDY D s Q (N' := D.R.N (j + 1)))) f' * ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k) := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [← mul_assoc, ← hval α]
        ring
    _ = _ := by rw [← Finset.mul_sum, hP, mul_assoc]

end GlobalTheory.TwV.DelA

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnChoiceGoodChartsEveryStage
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue

set_option maxHeartbeats 1000000 in

theorem goodCharts_all : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi) (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (Kc : ∀ i hi, Fam I l Z u a i hi (badQ (I.rec7 l Z) Q) (chOf i hi)), (∀ i hi, Finite (Ch i hi) ∧ I.IdY l Z u a i hi (eY i hi) ∧ ReadsOne I l Z u a i hi (chOf i hi) (Kc i hi) ∧ ∀ β, FunKilled ((Kc i hi) β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, ((Kc i hi) β).lev.chi κ ^ n = 1) ∧ Subsingleton (Ch 0 (Nat.zero_le _)) ∧ (∀ β, ((Kc 0 (Nat.zero_le _)) β).lev.Lb = F.to0.cls0.lev.Lb ∧ ((Kc 0 (Nat.zero_le _)) β).lev.Uloc = F.to0.cls0.lev.Uloc ∧ ((Kc 0 (Nat.zero_le _)) β).lev.U = F.to0.cls0.lev.U ∧ ∀ (κ : ((Kc 0 (Nat.zero_le _)) β).lev.U) (κ' : F.to0.cls0.lev.U), κ.1 = κ'.1 → ((Kc 0 (Nat.zero_le _)) β).lev.chi κ = F.to0.cls0.lev.chi κ') ∧ ∀ c, ∃ κ : F.to0.cls0.lev.U, (((Kc 0 (Nat.zero_le _)) ((chOf 0 (Nat.zero_le _)) (I.eCls0 l u a c))).y ⟨I.eCls0 l u a c, rfl⟩).1 = (F.to0.cls0.y c).1 * κ.1 ∧ F.to0.cls0.lev.chi κ = 1 ∧ ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1 := by
  intro B X I hOk hPins l Z u Ch0 chOf0 F a Q hQ hStd

  have hS : ∀ (i : ℕ) (hi : i ≤ B.R.m), 1 ≤ i → ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a i).Cl → Ch)
      (Kc : Fam I l Z u a i hi (badQ (I.rec7 l Z) Q) chOf), ReadsOne I l Z u a i hi chOf Kc ∧
        ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1 := by
    intro i hi h1
    rcases lt_or_eq_of_le hi with hlt | heq
    · exact GlobalTheory.T.trueColumns_goodCharts_middleSteps I hOk hPins l Z u F a Q hQ hStd i hi h1 hlt
    · subst heq
      exact GlobalTheory.T.exists_good_chart_lastStep_allTuples I hOk hPins l Z u F a Q hQ hStd
  choose ChS hfin chOfS KcS hgood using hS
  obtain ⟨K0, h0a, h0b, h0c⟩ := GlobalTheory.T.trueColumnChoice_stepZero_charts_good I hOk hPins l Z u F a Q hQ hStd
  have hC := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z
  have hE : ∀ i (hi : i ≤ B.R.m), ∃ eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi,
      I.IdY l Z u a i hi eY := by
    intro i hi
    obtain ⟨e, he, -⟩ := ((hC.2.2.2 i hi).2.2 u a).2
    exact ⟨e, he⟩
  choose eY heY using hE
  let Ch : ∀ i, i ≤ B.R.m → Type := fun i => Nat.casesOn (motive := fun i => i ≤ B.R.m → Type) i
    (fun _ => Unit) (fun j hj => ChS (j+1) hj (Nat.succ_le_succ (Nat.zero_le j)))
  let chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi := fun i => Nat.casesOn
    (motive := fun i => ∀ hi : i ≤ B.R.m, (I.stp u a i).Cl → Ch i hi) i
    (fun _ _ => ()) (fun j hj => chOfS (j+1) hj (Nat.succ_le_succ (Nat.zero_le j)))
  let Kc : ∀ i hi, Fam I l Z u a i hi (badQ (I.rec7 l Z) Q) (chOf i hi) := fun i => Nat.casesOn
    (motive := fun i => ∀ hi : i ≤ B.R.m, Fam I l Z u a i hi (badQ (I.rec7 l Z) Q) (chOf i hi)) i
    (fun _ => K0) (fun j hj => KcS (j+1) hj (Nat.succ_le_succ (Nat.zero_le j)))
  refine ⟨Ch, chOf, eY, Kc, ?_, ?_, ?_, ?_⟩
  · intro i hi
    cases i with
    | zero =>
      refine ⟨(inferInstance : Finite Unit), heY 0 hi, h0a.1, h0a.2⟩
    | succ j =>
      exact ⟨hfin _ hi _, heY _ hi, (hgood _ hi _).1, (hgood _ hi _).2⟩
  · show Subsingleton Unit
    infer_instance
  · exact h0b
  · exact h0c

end GlobalTheory.TwU.AtTrue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoUnitsAtPlaceUniformizingIdeleStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_units_at_place_uniformizing_idele : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => KIn t → S.Pos → ∀ v π, IsUnifAt J v π → ∀ j < D.R.m, (sysS H X std).Lv.comp j → (sysS H X std).Lv.comp (j + 1) → ∃ a b : (sysS H X std).G.Kf, (sysS H X std).vEqK a 0 ∧ (sysS H X std).vEqK b 0 ∧ S.E.iK a = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (-((sysS H X std).vm v (j + 1))) * TaylorLogMetric.lamC S.lam (S.muT (j + 1) π * chiI J π ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) ∧ S.E.iK b = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ ((sysS H X std).vm v (j + 1)) * TaylorLogMetric.lamC S.lam ((S.muT (j + 1) π)⁻¹ * chiI J π ^ (-((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))))) := by
  first | exact @GlobalTheory.TwV.Xc.two_units | exact GlobalTheory.TwV.Xc.two_units | (intros; apply GlobalTheory.TwV.Xc.two_units <;> assumption)
end

