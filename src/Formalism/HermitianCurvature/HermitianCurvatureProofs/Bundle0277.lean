import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0265
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0234
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RdVZeroOfVanish
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialBesselSmoothCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0244
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0166
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0051
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0183
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0276
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0275
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0246
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0257
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRvStepB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0212
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0070
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0072
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0076
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0164
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0213
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0167
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0151
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0189
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLTorus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EventuallyLevelPointMemOpen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0273
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0271
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelOneSquareIntegrableGeneral

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbSuppOrbit
section
open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbSupp

section gen

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem exists_orbit (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (g0 : B.Mat k n) (h : PBQ.pbF Bj B0 e H g0 ≠ 0) :
    ∃ x, PBQ.GoodP Bj x ∧ ∃ ξ : Mt k n × Mt k n, PBG.InR B0 ξ ∧
      H (D.castM e (PBQ.sP Bj x) * g0 * Matrix.of ξ.2 * Matrix.of ξ.1) ≠ 0 := by
  by_contra hno
  push Not at hno
  apply h
  unfold PBQ.pbF
  rw [← integral_zero (PBQ.XP k p ρ) (Wq →L[ℂ] Wp)]
  refine integral_congr_ae ?_
  filter_upwards [PBQ.ae_goodP (p := p) Bj] with x hx
  show PBQ.pbI Bj B0 e H g0 x = 0
  unfold PBQ.pbI
  have hK : PBG.Kr B0 H (D.castM e (PBQ.sP Bj x) * g0) = 0 := by
    unfold PBG.Kr
    rw [← integral_zero (Mt k n × Mt k n) (Wq →L[ℂ] Wp)]
    refine integral_congr_ae ?_
    filter_upwards [PBG.ae_inR B0] with ξ hξ
    show _ = 0
    rw [hno x hx ξ hξ, ContinuousLinearMap.zero_comp, smul_zero]
  rw [hK, ContinuousLinearMap.comp_zero, smul_zero]

theorem norm_entry_le_gN (g : B.Mat k n) (i j : Fin (2 * n + k + 1)) : ‖g i j‖ ≤ B.gN g := by
  unfold B.gN
  rw [Complex.norm_def]
  refine Real.sqrt_le_sqrt ?_
  calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (g i j')) (fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

theorem orbit_gen (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (hz : B0.z = D.castV e (liftVec k p ρ Bj.z))
    (Z : Matrix (Fin p) (Fin p) ℂ) (μ : B.Mat k ρ) (hZ : Z.det ≠ 0) (hμ : μ ∈ B.GV k ρ)
    (x : PBQ.XP k p ρ) (hx : PBQ.GoodP Bj x) (ξ : Mt k n × Mt k n) (hξ : PBG.InR B0 ξ) (g : B.Mat k n)
    (hg : g = D.castM e (PBQ.sP Bj x) * D.castM e (U.mMap k p ρ Z μ) * Matrix.of ξ.2 * Matrix.of ξ.1) :
    g ∈ B.GV k n ∧ (∃ u : Matrix (Fin p) (Fin p) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧ ∀ a b, ‖(Z * u) a b‖ ≤ B.gN g) ∧
      (∀ l, Dmin k n B0.z B0.z' g l = Dmin k n B0.z B0.z' (D.castM e (U.mMap k p ρ Z μ)) l) ∧
      Gf k n B0.z B0.z' g = Gf k n B0.z B0.z' (D.castM e (U.mMap k p ρ Z μ)) := by
  subst e
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl] at hg ⊢
  rw [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl] at hz
  have hm : U.mMap k p ρ Z μ ∈ B.GV k (p + ρ) := (Formalism.FourierDecayAlt.P.slice_membership k p ρ).1 Z μ hZ hμ
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (PartialBesselProperness.sP_GV Bj x) hm) hξ.2.1)
      hξ.1.1
  · refine ⟨G.upper (fun q : G.UT p => (Matrix.of ξ.2 : B.Mat k (p + ρ)) ⟨q.1.1.val, by omega⟩ ⟨q.1.2.val, by omega⟩),
      LeftFubiniLemmas.upper_isUpUni _, fun a b => ?_⟩
    have hZh : U.Zh k p ρ g = Z * G.upper (fun q : G.UT p =>
        (Matrix.of ξ.2 : B.Mat k (p + ρ)) ⟨q.1.1.val, by omega⟩ ⟨q.1.2.val, by omega⟩) := by
      have e0 := Formalism.FourierDecayAlt.P.hat_z_on_slice k p ρ 0 0 Z μ
      rw [LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e0
      rw [hg, PBQ.zh_mul_UW _ _ _ hξ.1, LeftFubiniLemmas.zh_mul_N _ _ hξ.2, PBQ.zh_sP_mul, e0,
        PBQ.nblk_upper _ hξ.2]
    rw [← hZh]
    exact norm_entry_le_gN g _ _
  · obtain ⟨h, hh, m, hmN, hs⟩ := PartialBesselProperness.leftFactor_mem Bj x
    rw [← hz] at hh
    have hhu : IsUnit h.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
    have hmu : IsUnit m.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hmN.1
    set pp : B.SS k (p + ρ) := ((Matrix.of.symm h⁻¹, Matrix.of.symm m⁻¹), ξ) with hpp
    have hin : B0.inSS pp := ⟨Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh, Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hmN, hξ.1, hξ.2⟩
    have hsg : B.sgs pp (U.mMap k p ρ Z μ) = g := by
      rw [hg, hs]
      simp only [B.sgs, hpp]
      change (h⁻¹)⁻¹ * (m⁻¹)⁻¹ * U.mMap k p ρ Z μ * Matrix.of ξ.2 * Matrix.of ξ.1 = _
      rw [Matrix.nonsing_inv_nonsing_inv _ hhu, Matrix.nonsing_inv_nonsing_inv _ hmu]
    refine ⟨fun l => ?_, ?_⟩
    · rw [← hsg]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs B0 hin _ l
    · rw [← hsg]; exact Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs B0 hin _

end gen

theorem gf_castM {k a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (g : B.Mat k a) :
    Gf k b z z' (D.castM e g) = Gf k a (D.castV e.symm z) (D.castV e.symm z') g := by
  subst e
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

theorem castV_castV' {k a b c : ℕ} (h1 : a = b) (h2 : b = c) (v : Fin (2 * a + k + 1) → ℂ) :
    D.castV h2 (D.castV h1 v) = D.castV (h1.trans h2) v := by
  subst h1 h2; rfl

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem lowV_top {P : M.Par} (p : KB.Pl P Wp Wq) (e : P.r + (P.r - P.r) = P.r) :
    U.lowV P.k P.r (P.r - P.r) (D.castV e.symm p.T.base.z) = (p.T.bs P.r).z ∧
      U.lowV P.k P.r (P.r - P.r) (D.castV e.symm p.T.base.z') = (p.T.bs P.r).z' := by
  unfold D.LevTower.base
  rw [← p.T.z_lev P.r le_rfl, ← p.T.z'_lev P.r le_rfl, castV_castV', castV_castV']
  exact ⟨Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _, Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _⟩

theorem orbit_point {P : M.Par} (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Z : Matrix (Fin P.r) (Fin P.r) ℂ) (μ : B.Mat P.k (P.r - P.r)) (hZ : Z.det ≠ 0)
    (hμ : μ ∈ Q.Glev P.k (P.r - P.r) (Fin.last _)) (h : CutEX.pbTop p G Z μ ≠ 0) :
    ∃ g ∈ B.GV P.k P.r, G g ≠ 0 ∧ ∃ u : Matrix (Fin P.r) (Fin P.r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧
      (∀ a b, ‖(Z * u) a b‖ ≤ B.gN g) ∧ Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨P.r, by omega⟩ = Z.det ∧
      Gf P.k P.r p.T.base.z p.T.base.z' g =
        Complex.normSq Z.det * Gf P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' μ := by
  have e : P.r + (P.r - P.r) = P.r := by omega
  have hμGV : μ ∈ B.GV P.k (P.r - P.r) := hμ.1
  unfold CutEX.pbTop PBQ.pbT at h
  obtain ⟨x, hx, ξ, hξ, hG⟩ := exists_orbit _ _ _ _ _ h
  have hz : p.T.base.z = D.castV e (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z) := (p.T.z_lev P.r le_rfl).symm
  obtain ⟨hGV, ⟨u, hu, hb⟩, hD, hGf⟩ := orbit_gen (p.T.bs P.r) p.T.base e hz Z μ hZ hμGV x hx ξ hξ _ rfl
  refine ⟨_, hGV, hG, u, hu, hb, ?_, ?_⟩
  · rw [hD]
    rw [Formalism.FourierDecayAlt.P.PBI.dmin_castM e _ _ _ P.r (by omega) (by omega), Formalism.FourierDecayAlt.P.hat_z_minimum_degree P.k P.r (P.r - P.r)]
    have e0 := Formalism.FourierDecayAlt.P.hat_z_on_slice P.k P.r (P.r - P.r) 0 0 Z μ
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e0
    unfold U.DjU
    rw [e0]
  · rw [hGf, gf_castM e]
    have hz0 := Formalism.FourierDecayAlt.P.PBH.inWb_castV e.symm p.T.base.z_mem
    have hz0' := Formalism.FourierDecayAlt.P.PBH.inWb_castV e.symm p.T.base.z'_mem
    have hG0 := Formalism.FourierDecayAlt.P.level_function_slice P.k P.r (P.r - P.r) _ _ hz0 hz0' 0 0 Z μ
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at hG0
    obtain ⟨hl1, hl2⟩ := lowV_top p e
    rw [hG0, hl1, hl2]

end Formalism.FourierDecayAlt.P.CutEXPbSupp
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBSupp
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.PBQ

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ProperDomP : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (Cs : Set (B.Mat P.k P.r)), IsCompact Cs →
    PartialBesselProperness.Proper (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) Cs (domP P.k P.r j p.T.base.z p.T.base.z')

theorem zxH_rfl (h : C.LPt) (v : XH h) : zxH h (D.ptSize h) rfl v = LeftFubiniLemmas.lhOf (D.ptPerm h) v *
    U.hMat (D.ptPerm h) (D.ptDiag h) := by
  first
  | rfl
  | simp [zxH]

theorem supp_of (hW : PartialBesselProperness.PbWords) (hP : ProperDomP) : Supp := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hF hw hγ hΩ K _ hK0
  obtain ⟨hh1, hh2⟩ := hh
  subst hh2
  have hhh : D.IsLocPt h (D.ptSize h) := ⟨hh1, rfl⟩
  obtain ⟨R, hR⟩ := hF.2.1
  set Cs : Set (B.Mat P.k P.r) := {g | B.gN g ≤ R} with hCs
  have hCc : IsCompact Cs := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R
  have e : D.ptSize h + (P.r - D.ptSize h) = P.r := by omega
  have hd : ∀ i, D.ptDiag h i ≠ 0 := ptDiag_ne hhh

  have hR1 : ∀ ew : Wd.Ix (Fin w.length), ∃ R1 : ℝ, ∀ v : XH h, R1 < ‖v‖ → ∀ g ∈ B.GV P.k P.r,
      U.Zh P.k (D.ptSize h) (P.r - D.ptSize h) (D.castM e.symm g) =
        LeftFubiniLemmas.lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h) →
      pbF (p.T.bs (D.ptSize h)) p.T.base e
        (D.uwG P.k P.r p.T.base.z p.T.base.z' F (D.ptSize h) (by omega) w ew) g = 0 := by
    intro ew
    refine pb_head_support (p.T.bs (D.ptSize h)) p.T.base e (D.ptPerm h) (D.ptDiag h) hd _ Cs hCc ?_
    intro g hg hgC
    by_contra hne
    exact hgC (Formalism.FourierDecayAlt.P.PBG.uwG_supp p.T.base.z p.T.base.z' F R hR (D.ptSize h) (by omega) w ew g hg hne)
  choose R1 hR1 using hR1
  refine ⟨⋃ ew, Metric.closedBall (0 : XH h) (R1 ew), isCompact_iUnion fun ew => isCompact_closedBall _ _,
    fun v hv τ hτK ew => ?_⟩
  have hτ : τ ≠ 0 := hK0 hτK
  have hvR : R1 ew < ‖v‖ := by
    by_contra hle
    have hle : ‖v‖ ≤ R1 ew := not_lt.mp hle
    exact hv (Set.mem_iUnion.2 ⟨ew, by rw [Metric.mem_closedBall, dist_zero_right]; exact hle⟩)
  have hpt := pts Wp Wq P p (D.ptSize h) hj h hhh γ hγ hΩ v
  have hyD := hpt.2 τ hτ
  have hyG := x0_GV hj hpt.1 hτ hγ
  have hz : p.T.base.z = D.castV e (liftVec P.k (D.ptSize h) (P.r - D.ptSize h) (p.T.bs (D.ptSize h)).z) :=
    (p.T.z_lev (D.ptSize h) (by omega)).symm
  have hPW := hW P.k (D.ptSize h) (P.r - D.ptSize h) P.r Wp Wq (p.T.bs (D.ptSize h)) p.T.base e hz (D.ptSize h)
    (by omega) F Cs (fun g hg _ => hF.1 g hg) hCc
    (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne))
    (domP P.k P.r (D.ptSize h) p.T.base.z p.T.base.z') (isOpen_domP _ _ _ _ _)
    (fun g hg => hg.1 ⟨D.ptSize h, by omega⟩ (show D.ptSize h ≤ D.ptSize h from le_rfl) (show D.ptSize h ≤ P.r by omega))
    (hP Wp Wq P p (D.ptSize h) (by omega) Cs hCc) w ew _ hyD hyG
  unfold phf
  unfold pbT
  rw [hPW]
  refine hR1 ew v hvR _ hyG ?_
  rw [leading_block_of_base_point hj _ τ γ e.symm, zxH_rfl]

end Formalism.FourierDecayAlt.P.CutHB
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatOpRFinal
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

theorem residue_operator_holds : JDOpR := jDOpR_of_vStepB mirror_residue_second_move

theorem hat_quadratic_operator_holds : JDHatOpQQ :=
  jDHatOpQQ_of_opA_opR_residue_splitting (jDOpA_of_parts polynomial_decay_admissible capelli_minors_holds) residue_operator_holds residue_splitting_holds
    mirror_residue_splitting_holds hat_lagrange_decay_holds hat_nodes_decay_holds

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFGAsm
section
open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem sliceFamGood_of (hGf : GfStep) (hRP : RadProper) (hPS : ParamSmooth) (hPt : PtSmooth) (hGV : PtGV)
    (hE : CkExt) : CutSH.SliceFamGood := by
  intro Wp Wq _ _ _ _ _ _ P T _ _ j hj _ _ F hF
  have e : P.r - (j + 1) + 1 = P.r - j := by omega
  obtain ⟨⟨hcc, ε, hε, hFG⟩, hcs⟩ := hF
  have hFs : B.CkOn (⊤ : ℕ∞) (B.GV P.k (P.r - j)) F :=
    Formalism.FourierDecayAlt.P.PBE.ckOn_top_of_nat fun m => (hcc 0 m).choose_spec.1
  obtain ⟨Ft, hFt, -, hFtF⟩ := hE P.k (P.r - j) _ F hFs hcs
  obtain ⟨R, hR⟩ := (hcs.isCompact.image_of_continuousOn
    (Formalism.FourierDecayAlt.P.B6.gN_continuous (k := P.k) (r := P.r - j)).continuousOn).bddAbove
  have hRF : ∀ g, F g ≠ 0 → B.gN g ≤ R := fun g hne => hR ⟨g, subset_tsupport _ hne, rfl⟩
  have hsl : ∀ (t : ℂ) (γ : B.Mat P.k (P.r - (j + 1))), γ ∈ B.GV P.k (P.r - (j + 1)) → sliceFam T j hj F t γ =
      ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • ∫ xx : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)),
        (psi P.k (P.r - j) (T.bs j).z cStd (rn1 e xx.1) * star (psi P.k (P.r - j) (T.bs j).z' cStd (rn1 e xx.2))) •
          F (pt e t γ xx) ∂((U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1)))) := by
    intro t γ hγ
    unfold sliceFam
    rw [Set.indicator_of_mem hγ]
    rfl
  refine ⟨?_, ?_⟩
  ·
    intro t₀ ht₀ γ₀ _
    have ht₀p : 0 < ‖t₀‖ := norm_pos_iff.2 ht₀
    set δ : ℝ := ‖t₀‖ / 2 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    obtain ⟨Kx, C, hKx, -, hKC⟩ := hRP P.k (P.r - (j + 1)) (P.r - j) e δ R hδ0
    obtain ⟨R1, hR1⟩ :=
      hKx.isBounded.subset_closedBall (0 : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)))
    have : HasContDiffBump (U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) := inferInstance
    set χ : ContDiffBump (0 : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) :=
      ⟨max R1 0 + 1, max R1 0 + 2, by positivity, by linarith⟩ with hχ
    set s : Set (ℂ × B.Mat P.k (P.r - (j + 1))) := {p | δ < ‖p.1‖} with hs
    have hso : IsOpen s := isOpen_lt continuous_const (continuous_norm.comp continuous_fst)
    have hs0 : ∀ p ∈ s, p.1 ≠ 0 := fun p hp => norm_pos_iff.1 (hδ0.trans hp)
    set hI : ℂ × B.Mat P.k (P.r - (j + 1)) → U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)) →
        (Wq →L[ℂ] Wp) :=
      fun p xx => χ xx • ((psi P.k (P.r - j) (T.bs j).z cStd (rn1 e xx.1) *
        star (psi P.k (P.r - j) (T.bs j).z' cStd (rn1 e xx.2))) • Ft (pt e p.1 p.2 xx)) with hIdef
    refine ⟨s, fun p => ((‖p.1‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) •
      ∫ xx, hI p xx ∂((U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1)))), hso, ?_, ?_, ?_⟩
    · show δ < ‖t₀‖
      rw [hδ]; linarith
    ·
      have : BorelSpace (U.RC P.k 1 (P.r - (j + 1))) := Prod.borelSpace
      have : BorelSpace (U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) := Prod.borelSpace
      have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := P.k) 1 (P.r - (j + 1))
      have := Formalism.FourierDecayAlt.P.PartialBesselLeftWordLemmas.fmc_RC P.k 1 (P.r - (j + 1))
      have hsc : ContDiffOn ℝ ∞ (fun p : ℂ × B.Mat P.k (P.r - (j + 1)) =>
          ((‖p.1‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ)) s := by
        intro p hp
        have hn : ContDiffAt ℝ ∞ (fun p : ℂ × B.Mat P.k (P.r - (j + 1)) => ‖p.1‖) p :=
          (contDiffAt_norm ℝ (hs0 p hp)).comp p contDiffAt_fst
        exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p (hn.pow _)).contDiffWithinAt
      have hps := (hPt P.k (P.r - (j + 1)) (P.r - j) e).2
      have hpt := (hPt P.k (P.r - (j + 1)) (P.r - j) e).1
      have hjoint : ContDiffOn ℝ ∞
          (fun q : (ℂ × B.Mat P.k (P.r - (j + 1))) × (U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) =>
            hI q.1 q.2) (s ×ˢ Set.univ) := by
        have h1 : ContDiff ℝ ∞ (fun q : (ℂ × B.Mat P.k (P.r - (j + 1))) ×
            (U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) => χ q.2) :=
          χ.contDiff.comp contDiff_snd
        have h2 : ContDiff ℝ ∞ (fun q : (ℂ × B.Mat P.k (P.r - (j + 1))) ×
            (U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) =>
            psi P.k (P.r - j) (T.bs j).z cStd (rn1 e q.2.1) *
              star (psi P.k (P.r - j) (T.bs j).z' cStd (rn1 e q.2.2))) := by
          refine ((hps (T.bs j).z).comp (contDiff_fst.comp contDiff_snd)).mul ?_
          exact Complex.conjCLE.contDiff.comp ((hps (T.bs j).z').comp (contDiff_snd.comp contDiff_snd))
        have h3 : ContDiffOn ℝ ∞ (fun q : (ℂ × B.Mat P.k (P.r - (j + 1))) ×
            (U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) => Ft (pt e q.1.1 q.1.2 q.2))
            (s ×ˢ Set.univ) :=
          hFt.comp_contDiffOn (hpt.mono (Set.prod_mono (fun p hp => hs0 p hp) le_rfl))
        exact h1.contDiffOn.smul (h2.contDiffOn.smul h3)
      have hvan : ∀ p ∈ s, ∀ xx, xx ∉ tsupport χ → hI p xx = 0 := by
        intro p _ xx hxx
        simp only [hIdef, image_eq_zero_of_notMem_tsupport hxx, zero_smul]
      have hint := hPS _ _ _ ((U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1)))) hI s
        (tsupport χ) hso χ.hasCompactSupport hvan hjoint
      exact hsc.smul hint
    ·
      rintro ⟨t, γ⟩ hp hγ
      have ht : t ≠ 0 := hs0 _ hp
      have hδt : δ ≤ ‖t‖ := le_of_lt hp
      show sliceFam T j hj F t γ = _
      rw [hsl t γ hγ]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun xx => ?_)
      have hpG := hGV P.k (P.r - (j + 1)) (P.r - j) e t ht γ hγ xx
      have hFt' : Ft (pt e t γ xx) = F (pt e t γ xx) := hFtF _ hpG
      show _ = hI (t, γ) xx
      simp only [hIdef]
      rw [hFt']
      by_cases hF0 : F (pt e t γ xx) = 0
      · simp only [hF0, smul_zero]
      · have hxK : xx ∈ Kx := (hKC t γ xx hδt (hRF _ hF0)).1
        have h1 : χ xx = 1 := by
          apply χ.one_of_mem_closedBall
          have := hR1 hxK
          rw [Metric.mem_closedBall] at this ⊢
          show dist xx 0 ≤ max R1 0 + 1
          linarith [le_max_left R1 0]
        rw [h1, one_smul]
  ·
    intro K hK hK0
    by_cases hne : K.Nonempty
    · obtain ⟨t1, ht1K, hmin⟩ := hK.exists_isMinOn hne continuous_norm.continuousOn
      have hδ0 : 0 < ‖t1‖ := norm_pos_iff.2 (hK0 t1 ht1K)
      obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
      have hM' : ∀ t ∈ K, ‖t‖ ≤ M := fun t ht => by simpa using hM t ht
      have hMp : 0 < M := hδ0.trans_le (hM' t1 ht1K)
      obtain ⟨Kx, C, -, hC, hKC⟩ := hRP P.k (P.r - (j + 1)) (P.r - j) e ‖t1‖ R hδ0
      refine ⟨C, hC, ε / M ^ 2, by positivity, ?_⟩
      intro t htK γ hne'
      have ht : t ≠ 0 := hK0 t htK
      have hγ : γ ∈ B.GV P.k (P.r - (j + 1)) := by
        by_contra hγ
        apply hne'
        unfold sliceFam
        rw [Set.indicator_of_notMem hγ]
      rw [hsl t γ hγ] at hne'
      obtain ⟨xx, hxx⟩ : ∃ xx, F (pt e t γ xx) ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hne'
        simp only [hall, smul_zero, integral_zero]
      have hδt : ‖t1‖ ≤ ‖t‖ := hmin htK
      refine ⟨(hKC t γ xx hδt (hRF _ hxx)).2, fun _ => ?_⟩
      have hpG := hGV P.k (P.r - (j + 1)) (P.r - j) e t ht γ hγ xx
      have h1 : ε ≤ Gf P.k (P.r - j) (T.bs j).z (T.bs j).z' (pt e t γ xx) := hFG _ hpG hxx
      have hz : (T.bs j).z = D.castV e (D.castV (Nat.add_comm 1 (P.r - (j + 1)))
          (liftVec P.k 1 (P.r - (j + 1)) (T.bs (j + 1)).z)) := by
        rw [levTower_bs_z_eq_castV_liftVec T j hj, asm_castV_castV]
      have hz' : (T.bs j).z' = D.castV e (D.castV (Nat.add_comm 1 (P.r - (j + 1)))
          (liftVec P.k 1 (P.r - (j + 1)) (T.bs (j + 1)).z')) := by
        rw [levTower_bs_z'_eq_castV_liftVec T j hj, asm_castV_castV]
      rw [hz, hz', hGf P.k (P.r - (j + 1)) (P.r - j) e _ _ (T.bs (j + 1)).z_mem (T.bs (j + 1)).z'_mem t ht γ xx]
        at h1
      have htp : 0 < ‖t‖ := norm_pos_iff.2 ht
      have htM : ‖t‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hM' t htK) 2
      have hG0 : 0 < Gf P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' γ := by
        by_contra hle
        push Not at hle
        have : ‖t‖ ^ 2 * Gf P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' γ ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
        linarith
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    · exact ⟨∅, isCompact_empty, 1, one_pos, fun t ht => absurd ⟨t, ht⟩ hne⟩

end Formalism.FourierDecayAlt.P.CutSH.SFG

namespace Formalism.FourierDecayAlt.P.CutSH

theorem cutSH_sliceFamGood_of (hGf : SFG.GfStep) (hRP : SFG.RadProper) (hPS : SFG.ParamSmooth)
    (hPt : SFG.PtSmooth) : SliceFamGood :=
  SFG.sliceFamGood_of hGf hRP hPS hPt SFG.point_mem_unitary_group SFG.ckExt_proof

end Formalism.FourierDecayAlt.P.CutSH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadLetterOfMinusPos
section
namespace Formalism.FourierDecayAlt.P.CutHL

theorem headLetter_of_minusPos (hMP : MinusPosOfParts) : LevelPointCoordinates.HeadLetter :=
  headLetter_of_rest Formalism.FourierDecayAlt.P.LevelPointCoordinates.left_rule_level_point torus_action_x0 Formalism.FourierDecayAlt.P.star_rule_x0 star_torus_x0
    Formalism.FourierDecayAlt.P.LevelPointCoordinates.plusPosOfParts Formalism.FourierDecayAlt.P.plus_zero_of_parts hMP Formalism.FourierDecayAlt.P.minus_zero_of_parts

end Formalism.FourierDecayAlt.P.CutHL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelOneSquareIntegrableOfTransport
section
open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section Tr

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem fs_tr (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ) (t : ℂ)
    {zi zi' : Fin (2 * (r - l.succ) + k + 1) → ℂ} {πi : Mx k (r - l.succ) → (Wp →L[ℂ] Wp)}
    {πi' : Mx k (r - l.succ) → (Wq →L[ℂ] Wq)} (μi : Measure (Mt k (r - l.succ)))
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - l.succ) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' =
      (κ : ℂ) * pairAt μ Φ Ψ (glue l.succ (Function.update c l t) (Formalism.FourierDecayAlt.P.PTie.shiftCf l.succ c'')))
    (Φ Ψ : RadSp k r z z' π π') :
    fs μ l Φ Ψ c t = (κ : ℂ)⁻¹ * ∫ c'' : Cf (r - l.succ) 0, wtI 0 c'' *
      pairAt μi (T Φ) (T Ψ) (glue 0 (shiftV l.succ (Function.update c l t)) c'') := by
  have hjl : (0 : Fin (r - l.succ + 1)).val + l.succ.val = l.succ.val := by simp
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  unfold fs
  rw [← (shEqJ_mp l.succ l.succ 0 hjl).integral_comp', ← integral_const_mul]
  congr 1; funext c''
  rw [wtI_shEqJ, glue_shEqJ l.succ l.succ 0 hjl (Function.update c l t) (Function.update c l t) (fun _ _ => rfl), hT]
  field_simp

theorem level_one_square_integrable_of_transport (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ) (t : ℂ)
    {zi zi' : Fin (2 * (r - l.succ) + k + 1) → ℂ} {πi : Mx k (r - l.succ) → (Wp →L[ℂ] Wp)}
    {πi' : Mx k (r - l.succ) → (Wq →L[ℂ] Wq)} (μi : Measure (Mt k (r - l.succ)))
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - l.succ) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' =
      (κ : ℂ) * pairAt μ Φ Ψ (glue l.succ (Function.update c l t) (Formalism.FourierDecayAlt.P.PTie.shiftCf l.succ c'')))
    (Φ : RadSp k r z z' π π') (c₀ : Fin (r - l.succ) → ℂ) (h : LevelSquareIntegrable μi 0 (T Φ) c₀) :
    LevelSquareIntegrable μ l.succ Φ (Function.update c l t) :=
  level_square_integrable_of_transport μ l.succ (Function.update c l t) μi T κ hκ hT Φ c₀ h

end Tr

end Formalism.FourierDecayAlt.P5.HerD
end
end

