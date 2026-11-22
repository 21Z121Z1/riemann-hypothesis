import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0345
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0344
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0346
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0318
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0342
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0338
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0322
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0320
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0326
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0329
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0321
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0343

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorMatricesAtComplexPointStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operatorMatrices_at_complexPoint : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), evD X D pos ι hN d f' (yMat X Kc j v s).det = ι (zT X D pos f' (pos ⟨v, s⟩)).det ∧ (¬ IsOddPos s → (dyMat X Kc j v s).map (evD X D pos ι hN d f') = ((dfr X D hN d f' (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.1.symm) (Fin.cast hN.1.symm)) ∧ (IsOddPos s → (YtMat X Kc j v s).map (evD X D pos ι hN d f') = ι (zT X D pos f' (pos ⟨v, s⟩)).det • (((dfr X D hN d f' (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id).map ι).submatrix (Fin.cast hN.1.symm) (Fin.cast hN.1.symm)) := by
  first | exact @GlobalTheory.TwV.DelA.evD_blockMats | exact GlobalTheory.TwV.DelA.evD_blockMats | (intros; apply GlobalTheory.TwV.DelA.evD_blockMats <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorOnFrameAndClassSummandPolynomialStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operatorOnFrame_and_classSummand_polynomial : Formalism.L2.KerInert.SecondKernelDifference.ApplyFrame ∧ Formalism.L2.KerInert.SecondKernelDifference.EntQFrame := by
  first | exact @GlobalTheory.TwV.DelA.applyFrame_and_entQFrame | exact GlobalTheory.TwV.DelA.applyFrame_and_entQFrame | (intros; apply GlobalTheory.TwV.DelA.applyFrame_and_entQFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialCoeffsWeightExtendedByZeroStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operatorPolynomial_coeffs_weight_extended_by_zero : ∀ (D : D7) {N N' : ℕ}, N ≤ N' → ∀ (s : D.what₂.Tau → ℂ) (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ), Q ∈ WtPol ℂ ν → (∀ α, MvPolynomial.coeff α (polDY D s Q (N' := N')) ∈ WtPol ℂ (extNu N' ν)) ∧ ∀ Θ : TaylorLogMetric.VC D N N' → ℂ, framePol D s Q Θ ∈ WtPol ℂ (extNu N' ν) := by
  first | exact @GlobalTheory.TwV.DelA.wt_polDY_framePol | exact GlobalTheory.TwV.DelA.wt_polDY_framePol | (intros; apply GlobalTheory.TwV.DelA.wt_polDY_framePol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalLocalBasesCarryWittLattices
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.FrameLat

theorem colSpan_mul' (R : Type) {K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (M g : Matrix (Fin k) (Fin k) K) :
    Formalism.MainNotions.G.colSpan R (M * g) = (Formalism.MainNotions.G.colSpan R g).map ((M.mulVecLin).restrictScalars R) := by
  unfold Formalism.MainNotions.G.colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2

theorem latMap_pair' (D : D7) {p : ℕ} (R : Type) {K : Type} [CommRing R] [Field K] [Algebra R K] (ρ : D.host.E →+* K)
    (hu : ∀ s : ℕ, Nat.Coprime s p → IsUnit (s : R)) {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (G : Matrix (Fin N) (Fin N) K) (G' : Matrix (Fin N') (Fin N') K)
    (hG : Formalism.MainNotions.G.colSpan R G = locSp R ρ L) (hG' : Formalism.MainNotions.G.colSpan R G' = locSp R ρ L')
    (B : Matrix (Fin N') (Fin N) D.host.E) (hB : ∃ s : ℕ, Nat.Coprime s p ∧ ∀ x ∈ L, (s : D.host.E) • (B *ᵥ x) ∈ L')
    (hL : Formalism.BasicNotions.IsSDLat D.host.E N L) (hL' : Formalism.BasicNotions.IsSDLat D.host.E N' L') :
    (∀ c, (B.map ρ) *ᵥ (fun x => G x c) ∈ Formalism.MainNotions.G.colSpan R G') ∧
    (∀ c, (B.map (fun y => ρ (D.host.conj y)))ᵀ *ᵥ (fun x => G' x c) ∈ Formalism.MainNotions.G.colSpan R G) := by
  obtain ⟨s, hs, hB'⟩ := hB
  constructor
  · intro c
    rw [hG']
    refine locSp_maps_of_unit_smul R K ρ L L' B s (hu s hs) hB' _ ?_
    rw [← hG]
    exact Submodule.subset_span ⟨c, rfl⟩
  · intro c
    have e : (B.map (fun y => ρ (D.host.conj y)))ᵀ = ((B.map D.host.conj)ᵀ).map ρ := by
      ext a b
      rfl
    rw [e, hG]
    refine locSp_maps_of_unit_smul R K ρ L' L _ s (hu s hs) (adj_maps_sd D L L' B s hL hL' hB') _ ?_
    rw [← hG']
    exact Submodule.subset_span ⟨c, rfl⟩

end GlobalTheory.TwV.FrameLat

open GlobalTheory.TwV.FrameLat in

theorem GlobalTheory.TwV.frameLatMapLt_of_ties : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (fd : FData X D) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), (∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → (∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → TaylorLogMetric.admitted D _ _ (fd.kerN j La) (fd.kerN (j + 1) La') ∧ ∀ v, locSp (X.G.P.W v) (ρ v) (fd.kerN j La) = (X.latAt v j La.2).map (((fd.frM j La v).mulVecLin).restrictScalars (X.G.P.W v)) ∧ locSp (X.G.P.W v) (ρ v) (fd.kerN (j + 1) La') = (X.latAt v (j + 1) La'.2).map (((fd.frM (j + 1) La' v).mulVecLin).restrictScalars (X.G.P.W v))) → Lt.FrameLatMapLt X fd.frM hfin D (fun j La _ => fd.kerN j La) (fun j _ La' => fd.kerN (j + 1) La') ρ := by
  intro p _ X _ hfin D fd ρ hA hT
  intro j hj L0 hL0 La' hLa' φ r b hb _ i v
  have hL0' : (X.Pj j).IsLatTup L0.2 := Formalism.L2.G.Pend.repOf_lat X.Lv hfin j L0 hL0
  obtain ⟨hAd, hK⟩ := hT j hj L0 La' hL0' hLa'
  obtain ⟨hK1, hK2⟩ := hK v
  refine latMap_pair' D (X.G.P.W v) (ρ v) (natCast_isUnit_localRing X v) (Formalism.L2.KerInert.RepFrame.Gm X fd.frM φ v)
    (Formalism.L2.KerInert.RepFrame.Gp X fd.frM φ v) ?_ ?_ (b i)
    (GlobalTheory.TwV.YYMaps.locBasis_maps D p hA _ _ b hb i) hAd.2.2.1 hAd.2.2.2
  · rw [hK1]
    unfold Formalism.L2.KerInert.RepFrame.Gm
    rw [colSpan_mul', ← φ.hg v]
  · rw [hK2]
    unfold Formalism.L2.KerInert.RepFrame.Gp
    rw [colSpan_mul', ← φ.hg' v]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealPlaceBlockWeightLastEntryConsecutiveLevelsStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceBlockWeightLastEntry_consecutive_levels : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) (τ : D.what₂.Tau), (eT X D pos j τ = if IsOddPos (pos.symm τ).2 then wT X D pos j τ - cT1 X D pos j τ else X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j) - wT X D pos j τ) ∧ (eT X D pos (j + 1) τ = if IsOddPos (pos.symm τ).2 then wT X D pos j τ - cT1 X D pos j τ else -wT X D pos j τ) := by
  first | exact @GlobalTheory.TwV.DelA.eT_last_pair | exact GlobalTheory.TwV.DelA.eT_last_pair | (intros; apply GlobalTheory.TwV.DelA.eT_last_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsOfInputsAndJumps
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowsAll

theorem main : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), GlobalTheory.NRows.Inputs hL D → JumpsCard D.nd D.naut → GlobalTheory.NRows.Rows D := by
  intro hP hHC hCusp hL D I hJ
  have a : GlobalTheory.NRows.RowsA D := GlobalTheory.T.rows_a_of_jump_count hP hL D I.P hJ
  obtain ⟨J⟩ := GlobalTheory.T.nonempty_join_of_agreement hHC hCusp hL D I.P I.X I.agree
  obtain ⟨lamLoc, rank⟩ := GlobalTheory.T.thetaLiftSpaces_rank_const_and_localisation_scalars D I.isot I.lam
  obtain ⟨b, trip⟩ := GlobalTheory.T.rows_b_and_local_lifts hP hL D I.P J a I.adm1 lamLoc
  have Conclusion1 : Formalism.MainNotions.SumRepresentations.Conclusion1 D := I.Conclusion1 (GlobalTheory.T.parts_give_dimension D) a b
  have c : GlobalTheory.NRows.RowsC D := GlobalTheory.T.rows_c_of_local_lifts hL D I.P J a b I.adm1 I.isot Conclusion1 trip
  refine ⟨a, b, c, fun i => ?_, rank⟩
  exact GlobalTheory.T.type_nonzero_recursion_of_eigen hL D I.P I.X I.agree I.typeNZ i
    (GlobalTheory.T.eigen_string_of_agreement hP.fin hL D I.P I.X I.agree Conclusion1.1 a.temp a.tieLab i)
    (GlobalTheory.T.eigen_good_of_admissibility hL D I.P I.X Conclusion1.1 a.tieLab I.mtPar I.adm1 a.tie0 b.a4 a.a5 I.e0loc I.e0read i)

end GlobalTheory.RowsAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScalInvFrame
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwV.DelA

theorem scal_inv_frame : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (j : ℕ) (La : X.Lt j) {n : ℕ} (h : (X.Pj j).m + 1 = n) (M : GL (Fin n) D.host.E), StdU D M → FrIs fd ρ j La h M → Formalism.L2.G.Pend.cA X Kc j (BOf fd j La) = ι (∏ τ, embT D τ (M : Matrix (Fin n) (Fin n) D.host.E).det ^ (-(wT X D pos j τ))) := by
  intro p _ X D pos Kc _ _ _ ι ρ hT fd j La n h M hU hF
  have hMu : IsUnit (M : Matrix (Fin n) (Fin n) D.host.E).det := by
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using (Matrix.GeneralLinearGroup.det M).isUnit
  have hdet : ∀ v, (fd.frM j La v).det = ρ v (M : Matrix (Fin n) (Fin n) D.host.E).det := by
    intro v
    rw [hF v, Matrix.det_submatrix_equiv_self, RingHom.map_det]
    rfl
  have hu : ∀ v, IsUnit (fd.frM j La v).det := fun v => by rw [hdet v]; exact hMu.map (ρ v)
  have hfr : ∀ v, ((frGL fd j La v : GL _ _) : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) = fd.frM j La v := by
    intro v; unfold frGL; rw [dif_pos (hu v)]; rfl
  have hB : ∀ v s, tw X Kc v s ((BOf fd j La v : GL _ _) : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det =
      (tw X Kc v s (ρ v (M : Matrix (Fin n) (Fin n) D.host.E).det))⁻¹ := by
    intro v s
    have h1 : ((BOf fd j La v : GL _ _) : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det * (fd.frM j La v).det = 1 := by
      rw [← hfr v, ← Matrix.det_mul]
      unfold BOf
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    have h2 := congrArg (tw X Kc v s) h1
    rw [map_mul, map_one, hdet v] at h2
    exact eq_inv_of_mul_eq_one_left h2
  unfold Formalism.L2.G.Pend.cA
  have hterm : ∀ v s, (tw X Kc v s ((BOf fd j La v : GL _ _) : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det) ^
      ((if IsOddPos s then -1 else 1) * X.w v (j + 1) s) =
      ι (embT D (pos ⟨v, s⟩) (M : Matrix (Fin n) (Fin n) D.host.E).det ^ (-(wT X D pos j (pos ⟨v, s⟩)))) := by
    intro v s
    rw [hB v s, (GlobalTheory.TwV.DelA.blkC_atR_read X D pos Kc ι ρ hT M hU v s).2, map_zpow₀]
    simp only [wT]
    rw [Equiv.symm_apply_apply]
    split_ifs <;> simp [zpow_neg, inv_inv]
  simp_rw [hterm]
  rw [map_prod]
  exact (Fintype.prod_sigma (fun x => ι (embT D (pos x) (M : Matrix (Fin n) (Fin n) D.host.E).det ^ (-(wT X D pos j (pos x)))))).symm.trans
    (Fintype.prod_equiv pos _ _ (fun _ => rfl))

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteBaseDatumIntegralOffBadPrimes
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

set_option maxHeartbeats 2000000 in

theorem Joint.site_base_datum_integral_off_bad_primes : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), ∀ j La La' z, IntOff (t.O u μ).S (J.xi0 std S.Xi j La La' z) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J S j La La' z
  unfold Joint.xi0
  split_ifs with h
  · exact S.law.int _ _ _ _ _ _ _
  · exact Formalism.L2.PairingIndexBounds.F.intOff_zero _

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteFiniteDataLevelPosBadPrimeFactors
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

set_option maxHeartbeats 2000000 in

theorem sNum_lev_site : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), SNum (t.O u μ).S (t.rd u μ).lev := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ _ _
  exact Formalism.L2.Ker.level_structure_counting D L hT Gi Gl Kc Dx cX ex t u μ

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SitePlaceInducesPositionEmbeddings
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section
namespace GlobalTheory.TwV

theorem pos_at_site : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S
  exact GlobalTheory.TwU.lamPos_of_posEmb (sysS H X std) S.E.toCEmb D _ S.lam _ (ex.cmp.embW u w hg) S.hK (J.Gd.cmp.tie u w hg).pos_emb

end GlobalTheory.TwV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteResidueCharNotMemBadPrimes
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.SitePrime

set_option maxHeartbeats 2000000 in

theorem resChar_not_mem_S : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), D.what₂.places.resChar w ∉ (t.O u μ).S := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ _ J hmem
  obtain ⟨-, -, -, hg'⟩ := GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg
  obtain ⟨-, -, -, -, -, hT'⟩ := id hg
  rw [t.O_S u μ] at hmem
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with h | (h | h) | h
  · exact hT' (h ▸ dvd_rfl)
  · exact hg' 0 h
  · exact hg' 1 h
  · exact J.away h

end GlobalTheory.TwV.SitePrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulDualSetLatAdMem
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory

theorem smul_dualSet_latAd_mem {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E)
    (hco : ∃ co, IsOrthCo (sp.cm.sig : E →+* E) J co) (T : ℕ) (Lb : Submodule (𝓞 E) (Fin N → E)) (hT : 0 < T)
    (hLb : Formalism.L2.GlobalTheoryTheory.Comp.IsLat Lb)
    (hdual : ∀ z ∈ dualSet (sp.cm.sig : E →+* E) J Lb, (T : E) • z ∈ Lb)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hy : y ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F))
    (z : Fin N → E) (hz : z ∈ dualSet (sp.cm.sig : E →+* E) J (latAd y Lb)) :
    (T : E) • z ∈ latAd y Lb := by
  have hlat : latAd y Lb = Formalism.UG.CS.globLat y Lb := Submodule.span_eq (Formalism.UG.CS.globLat y Lb)
  set a : 𝓞 E := (T : 𝓞 E) with ha
  have ha0 : a ≠ 0 := by
    rw [ha]; exact_mod_cast hT.ne'
  have hsm : ∀ w : Fin N → E, a • w = (T : E) • w := by
    intro w
    rw [← algebraMap_smul E a w, ha, map_natCast]

  have hdl : ∀ w ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb, a • w ∈ Lb := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => rw [hsm]; exact hdual w hw
    | zero => rw [smul_zero]; exact zero_mem _
    | add u v _ _ hu hv => rw [smul_add]; exact add_mem hu hv
    | smul c w _ hw => rw [smul_comm]; exact Lb.smul_mem c hw
  have hle : Ideal.span {a} • Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb ≤ Lb := by
    refine Submodule.smul_le.2 fun r hr w hw => ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul]
    exact Lb.smul_mem c (hdl w hw)

  have hz' : z ∈ Formalism.UG.CS.globLat y (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb) := by
    rw [Formalism.L2.GlobalTheoryTheory.Comp.glob_dl sp.cm.sig J (GlobalTheory.isLat_dl_of_isOrthCo sp J hco) hLb y hy]
    rw [hlat] at hz
    exact Submodule.subset_span hz
  have h1 : a • z ∈ Ideal.span {a} • Formalism.UG.CS.globLat y (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb) :=
    Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hz'
  have h2 := Formalism.L2.GlobalTheoryTheory.Comp.glob_mono y hle
    (Formalism.L2.GlobalTheoryTheory.Comp.smul_glob_le _ a y h1)
  rw [hlat, ← hsm]
  exact h2

end GlobalTheory
end
end

