import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableBcWeight
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0445
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0436
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0400
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0206
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0233
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0223
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0131
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0401
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0116
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0053
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0036
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0194
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0417
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0439
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0422
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0327
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0419
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0427
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0304
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0218
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0336
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0345
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0282

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SchurAlongFamily
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.GapAmp

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants in

theorem bessel_schur_gap (hH : GlobalTheory.GapIn.Hyp) (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ)
    (hCl : 1000 ≤ Cl) : BSch D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro hZ
  have hv1 : 1 ≤ D.host.v := hZ.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine GlobalTheory.T.besselMap_multipleIsometry_largeGap hH D large₂ C' Cl Cg cb Cu cT CT C0 hCl
    (fun _ _ _ _ _ h => GlobalTheory.BesselSchur.theta_pos D (by linarith) h) (fun w => ?_) hZ
  unfold Tr
  exact_mod_cast (D.mem w).A.T_prime.pos

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S in

theorem schur_along_family : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS →
    ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm →
      PX.RanksF Fm C0 Cg cb Cu cT CT →
        OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm11 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 C1 C := by
  intro _ hH _ Cg cb Cu cT CT C0 C1
  obtain ⟨C₀, hC⟩ := GlobalTheory.Amp.schurSt_of_big_tie Cg cb Cu cT CT C0 C1
  obtain ⟨m₀, hm⟩ := hC C₀ le_rfl
  obtain ⟨m₁, hL⟩ := GlobalTheory.T.amplitudeMultOneDecay_of_largeGapHypotheses hH Cg cb Cu cT CT C0
  refine ⟨C₀, 1000, fun eps Fm _ h2 _ => ?_⟩
  obtain ⟨x0, hx⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (max (max m₀ m₁) 1)
  refine ⟨x0, fun x hxx i => ?_⟩
  obtain ⟨-, hmM, -, -, hrd, -⟩ := hx x hxx i
  have hm1 : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := le_trans (le_max_right _ _) hmM
  have hCm : 1 ≤ sCl Fm * ((Fm.D x i).R.m : ℝ) := by nlinarith
  have hBig : ∀ m' : ℝ, m' ≤ max (max m₀ m₁) 1 → GlobalTheory.Amp.Big (Fm.D x i) (Fm.L x i) (sCl Fm) m' :=
    fun m' hm' => ⟨hrd, hCm, le_trans hm' hmM⟩
  exact hm (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm)
    (hBig m₀ (le_trans (le_max_left _ _) (le_max_left _ _))) (Fm.ties x i).cdScale_tie
    (bessel_schur_gap hH _ _ _ _ _ _ _ _ _ _ h2)
    (hL _ _ _ _ (hBig m₁ (le_trans (le_max_right _ _) (le_max_left _ _))))

end GlobalTheory.GapAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceBaseNeOfDistinctTypePrimes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.SplitPlaceDistinct

theorem not_mem_both {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    (h1 : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) (h2 : ((q : ℕ) : 𝓞 E) ∈ w.asIdeal) : False := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have e : ((a : 𝓞 E)) * ((p : ℕ) : 𝓞 E) + (b : 𝓞 E) * ((q : ℕ) : 𝓞 E) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hab
  rw [← e]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h1) (w.asIdeal.mul_mem_left _ h2)

theorem splitPlace_v_ne : ∀ (D : D7) (s s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (kv kv' : Σ k : Fin 2, D.nd.PlG k),
    s.w = D.naut.plGw kv.1 kv.2 → s'.w = D.naut.plGw kv'.1 kv'.2 → kv ≠ kv' → s.v ≠ s'.v := by
  intro D s s' kv kv' hs hs' hne hv
  obtain ⟨k, v⟩ := kv
  obtain ⟨k', v'⟩ := kv'
  have hgk : ∀ a b : Fin 2, a ≠ b → D.host.g a ≠ D.host.g b := by
    intro a b hab
    have h01 := D.host.g_ne
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · exact h01
    · exact h01.symm
    · exact absurd rfl hab
  have hover := D.naut.plGw_over
  rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s s'.w
      (s'.w_under.trans (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal hv.symm)) with e | e
  · rw [hs, hs'] at e
    by_cases hk : k = k'
    · subst hk
      exact hne (congrArg (Sigma.mk k) (D.naut.plGw_inj k e))
    · exact not_mem_both (D.host.g_prime k) (D.host.g_prime k') (hgk k k' hk) _ (hover k v)
        (e ▸ hover k' v')
  · rw [hs, hs'] at e
    by_cases hk : k = k'
    · subst hk
      exact D.naut.plGw_nconj k v' v e
    · have hm : ((D.host.g k' : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal :=
        (e _ _ (by simp)).1 (hover k' v')
      exact not_mem_both (D.host.g_prime k) (D.host.g_prime k') (hgk k k' hk) _ (hover k v) hm

end GlobalTheory.SplitPlaceDistinct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserCovolumeLeRootCoordinateCover
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory in

theorem GlobalTheory.LoopVol.packing_pinned {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (s : TT Y u u')
    {γw g g' : X.B.I.Ginf} {μw : Measure X.B.I.Ginf} (hg : g ∈ X.SinfU u) (hg' : g' ∈ X.SinfU u')
    (hdec : s.pt.1 = g * γw * g'⁻¹) (hH : IsHaarOnSet X.B.I (Formalism.L2.SG.RealObj.StInf X u u' γw) μw)
    {K B : Set X.B.I.Ginf} (hK : Formalism.L2.SG.LoopTerm.IsFundR s K) (hB : MeasurableSet B)
    (hcov : ∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset s, ∃ q ∈ Formalism.L2.SG.TermOp.ROinf s, q * r ∈ B) :
    (μw.map fun y => g * y * g⁻¹) K ≤ (μw.map fun y => g * y * g⁻¹) B := by
  obtain ⟨-, -, hconc, hinvw⟩ := hH
  obtain ⟨hKm, hKu⟩ := hK
  haveI := Formalism.L2.SG.TermOp.Vanish.ROsub_countable X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin
  set Γ := Formalism.L2.SG.TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin with hΓ
  set μR := μw.map fun y => g * y * g⁻¹ with hμR
  have hcm : Measurable fun y : X.B.I.Ginf => g * y * g⁻¹ :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hRm : MeasurableSet (Formalism.L2.SG.TermOp.Vanish.Rset s) :=
    (Formalism.L2.SG.Pf.rClosedC_holds D X Y u u' s).measurableSet
  have hRc : μR (Formalism.L2.SG.TermOp.Vanish.Rset s)ᶜ = 0 := by
    rw [hμR, Measure.map_apply hcm hRm.compl]
    exact measure_mono_null (fun y hy hySt => hy (Formalism.L2.SG.LoopTerm.stInf_conj hg hg' hdec hySt)) hconc
  have hinv : ∀ q ∈ Γ, μR.map (fun x => q * x) = μR := by
    intro q hq
    have hq' := Formalism.L2.SG.LoopTerm.stInf_conj_inv hg hg' hdec (Formalism.L2.SG.Pf.LoopBPin.roinf_sub_rset s hq)
    rw [hμR, Measure.map_map (measurable_const_mul q) hcm]
    have e : (fun x => q * x) ∘ (fun y => g * y * g⁻¹) =
        (fun y => g * y * g⁻¹) ∘ (fun y => (g⁻¹ * q * g) * y) := by
      funext y; simp only [Function.comp]; group
    rw [e, ← Measure.map_map hcm (measurable_const_mul _), hinvw _ hq']
  have hpre : ∀ q ∈ Γ, ∀ C, MeasurableSet C → μR ((fun x => q * x) ⁻¹' C) = μR C := by
    intro q hq C hC
    rw [← Measure.map_apply (measurable_const_mul q) hC, hinv q hq]
  have h1 : μR K ≤ ∑' q : Γ, μR (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) := by
    calc μR K = μR (K ∩ Formalism.L2.SG.TermOp.Vanish.Rset s) := (measure_inter_conull hRc).symm
      _ ≤ μR (⋃ q : Γ, K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) := by
          refine measure_mono fun r hr => ?_
          obtain ⟨q, hq, hqr⟩ := hcov r hr.2
          exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, hr.1, hqr⟩
      _ ≤ _ := measure_iUnion_le _
  have h2 : ∀ q : Γ, μR (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) =
      μR (B ∩ (fun x => ((q⁻¹ : Γ) : X.B.I.Ginf) * x) ⁻¹' K) := by
    intro q
    have hC : MeasurableSet (B ∩ (fun x => ((q⁻¹ : Γ) : X.B.I.Ginf) * x) ⁻¹' K) :=
      hB.inter (hKm.preimage (measurable_const_mul _))
    rw [← hpre q q.2 _ hC]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Subgroup.coe_inv, inv_mul_cancel_left]
    exact and_comm
  have h3 := Formalism.L2.SG.Pf.FormAllPf.decomp μR (Formalism.L2.SG.TermOp.Vanish.Rset s) hRc Γ B K hB hKm hKu
  have h4 : ∑' q : Γ, μR (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) = μR B := by
    rw [h3]
    simp_rw [h2]
    exact (Equiv.inv Γ).tsum_eq (fun q => μR (B ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K))
  exact h1.trans_eq h4

theorem GlobalTheory.LoopVol.ka_div_le_one {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} (hSt : Formalism.MainNotions.S.Cnt.Stand D u u') :
    D.host.ka / (X.B.g : ℝ) / Real.pi ≤ 1 := by
  have hrd := GlobalTheory.RealPlaces.one_le_rdE D
  have hg0 := hSt.2.2.2.2.2.2.2.1.two_le
  have hg1 := hSt.2.2.2.2.2.2.2.2.1.two_le
  have h0 : (2 : ℝ) ≤ (D.host.g 0 : ℝ) := by exact_mod_cast hg0
  have h1 : (2 : ℝ) ≤ (D.host.g 1 : ℝ) := by exact_mod_cast hg1
  have hgR : (4 : ℝ) ≤ (X.B.g : ℝ) := by rw [X.g_eq]; push_cast; nlinarith
  have e : D.host.ka / (X.B.g : ℝ) / Real.pi = 2 / (D.host.rdE * X.B.g) := by
    rw [show D.host.ka = Real.pi / (D.host.rdE / 2) from rfl]
    have : (0 : ℝ) < D.host.rdE := by linarith
    have : (0 : ℝ) < (X.B.g : ℝ) := by linarith
    field_simp
  rw [e, div_le_one (by positivity)]
  nlinarith

theorem GlobalTheory.LoopVol.covolume_le_cover : ∀ Cg cb Cu cT CT C0 A : ℝ, ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ s : TT Y u u', s.relevant → s.G ≠ 0 → ∀ (w : Point D.host.E (D.R.rS + 1)) (μR : MeasureTheory.Measure X.B.I.Ginf) (K : Set X.B.I.Ginf), s.toTerm.atPt w → Formalism.L2.SG.VolPin.IsPinnedR s w μR → Formalism.L2.SG.LoopTerm.IsFundR s K → ∀ (L U : Formalism.MainNotions.S.Cnt.GramM D), IsLoUni L → IsUpUni U → ZhatOM (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)) = L * ptMat w * U → ∀ Ω : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasurableSet Ω → (∀ c : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ, ∃ n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame), ∃ a : Formalism.MainNotions.S.Cnt.GramM D, (∀ j : Fin (D.R.rS + 1), n (frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) j) = ∑ i : Fin (D.R.rS + 1), ((-1) ^ (i.val + j.val) * a i j) • frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) i) ∧ (fun τ (q : GlobalTheory.LoopV.roots (ptMat w)) => ((U * a * U⁻¹).map (embS D τ) * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat w)) (c τ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ) q.1.1 q.1.2) ∈ Ω) → μR K ≤ MeasureTheory.volume Ω * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
  intro Cg cb Cu cT CT C0 A D X Y W large₂ u u' C' Cl hH s hrel hG w μR K hat hPin hK L U hL hU hZ Ω hΩ hcov
  obtain ⟨γw, sf, s', μw, hrep, hsf, hs', hdec, hμwH, hμwS, rfl⟩ := hPin
  obtain ⟨T, hT, hTc⟩ := GlobalTheory.T.integerPoints_cover_realPoints_rootCoordinates Cg cb Cu cT CT C0 A D X Y W large₂ u u' C' Cl hH s hrel hG w γw sf s' hat hrep hsf hs' hdec
    L U hL hU hZ Ω hcov
  have hTΩ : MeasurableSet (T ⁻¹' Ω) := hT.measurable hΩ
  have hBm : MeasurableSet (GlobalTheory.LoopVol.ratCoord X u' w γw sf ⁻¹' (T ⁻¹' Ω)) :=
    (GlobalTheory.LoopVol.ratCoord_cont X u' w γw sf).measurable hTΩ
  have hka := GlobalTheory.LoopVol.ka_div_le_one X hH.2.1
  calc (μw.map fun y => sf * y * sf⁻¹) K
      ≤ (μw.map fun y => sf * y * sf⁻¹) (GlobalTheory.LoopVol.ratCoord X u' w γw sf ⁻¹' (T ⁻¹' Ω)) :=
        GlobalTheory.LoopVol.packing_pinned s hsf hs' hdec hμwH hK hBm hTc
    _ ≤ MeasureTheory.volume (T ⁻¹' Ω) * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) :=
        GlobalTheory.T.stabiliserHaar_rootCoordinates_le_lebesgue D X u u' w γw sf μw hμwH hμwS hka _ hTΩ
    _ = MeasureTheory.volume Ω * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
        rw [hT.measure_preimage hΩ.nullMeasurableSet]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnfoldingGenusWeightsSumToMass
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.SumK

theorem inGen_symm_of {D : D7} {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS}
    (hE : ∀ p, Equivalence (LocNG.Datum.Rel (P := FP p))) {d y y' : Dat Z FP}
    (h : InGen d y) (h' : InGen d y') : InGen y y' := by
  refine ⟨fun p => (hE p).trans ((hE p).symm (h.1 p)) (h'.1 p), ?_⟩
  apply (h.2.union h'.2).subset
  intro p hp
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  exact hp (by rw [hc.1, hc.2])

theorem weights_add_up_to_mass_of
    (hRelEqv : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), Equivalence (LocNG.Datum.Rel (P := FP p)))
    (hInv : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (d y y' : Dat Z FP), LocOver Λ y → InGen d y → GRel F F' y y' → InGen d y') :
    ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ TS : Set (TauC Y u u'), LocClosed F F' Z FP TS → ∀ (t₀ : TauC Y u u') (Λ₀ : LV D) (y₀ d : Dat Z FP), t₀ ∈ TS → TG F F' t₀ Λ₀ → LocOver Λ₀ y₀ → InGen d y₀ → ∀ K, K = {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ} → ∀ ω : K → ℝ, (∀ κ : K, ∀ t : TauC Y u u', key t = κ.1 → ω κ = wt t ^ 2) → ∑' κ : K, ENNReal.ofReal (ω κ) = massA F F' d := by
  intro D X Y u u' F F' w hw hG Z FP hB hR TS hTS t₀ Λ₀ y₀ d ht₀ hTG₀ hLO₀ hIG₀ K hK ω hω
  subst hK
  obtain ⟨hEq, -, hRel⟩ := GlobalTheory.T.rationalClass_lattices_iff_rationalClass_localFramePairs D X Y u u' F F' w hw hG Z FP hB hR
  have hQ : ∀ y y' : Dat Z FP, (Quot.mk (GRel (Z := Z) (FP := FP) F F') y) = Quot.mk _ y' ↔ GRel F F' y y' :=
    fun y y' => ⟨fun h => hEq.eqvGen_iff.1 (Quot.eqvGen_exact h), Quot.sound⟩
  have hout : ∀ o : Quot (GRel (Z := Z) (FP := FP) F F'), ∀ y, Quot.mk _ y = o → GRel F F' o.out y := by
    intro o y h
    exact (hQ _ _).1 (by rw [h, Quot.out_eq])

  have hex : ∀ κ : {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ},
      ∃ y : Dat Z FP, ∃ t ∈ TS, ∃ Λ : LV D, TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ.1 := by
    rintro ⟨κ, t, ht, Λ, y, h1, h2, h3, h4⟩
    exact ⟨y, t, ht, Λ, h1, h2, h3, h4⟩
  choose yOf hyOf using hex
  set φ := fun κ => (Quot.mk (GRel (Z := Z) (FP := FP) F F') (yOf κ)) with hφ
  have hwd : ∀ (t t' : TauC Y u u') (Λ Λ' : LV D) (y y' : Dat Z FP), TG F F' t Λ → TG F F' t' Λ' →
      LocOver Λ y → LocOver Λ' y' → key t = key t' → GRel F F' y y' := fun t t' Λ Λ' y y' h1 h2 h3 h4 h5 =>
    ((hRel Λ Λ' y y' h3 h4).1).1 (GlobalTheory.T.same_row_doubleCoset_inner_data_one_rational_class D X Y u u' F F' w hw hG t t' Λ Λ' h1 h2 h5)
  have hImg : ∀ κ, InGen d (φ κ).out := by
    intro κ
    obtain ⟨t, -, Λ, h1, h2, h3, -⟩ := hyOf κ
    exact hInv D X Y u u' F F' w hw hG Z FP hB hR Λ d (yOf κ) _ h2 h3 (hEq.symm (hout _ _ rfl))
  unfold massA
  rw [← ENNReal.tsum_fiberwise _ φ]
  refine tsum_congr fun o => ?_
  by_cases ho : InGen d o.out
  · rw [if_pos ho]
    have hIG01 : InGen y₀ o.out := inGen_symm_of (hRelEqv D Z FP) hIG₀ ho
    obtain ⟨Λ₁, hLO₁, hloc⟩ := GlobalTheory.T.genusFamily_carried_by_lattice_in_localOrbits D X Y u u' F F' w hw hG Z FP hB hR Λ₀ y₀ o.out hLO₀ hIG01
    obtain ⟨t₁, hTG₁⟩ := GlobalTheory.T.exists_rowTerm_of_local_completions_terms D X Y u u' F F' w hw hG Z FP hB hR Λ₁ o.out hLO₁
    have ht₁ : t₁ ∈ TS := hTS t₀ t₁ Λ₀ Λ₁ hTG₀ hTG₁ hloc ht₀
    obtain ⟨-, hcarry, hwt, hmass⟩ := GlobalTheory.T.orbitCount_rows_doubleCosets_innerDatum_class D X Y u u' F F' w hw hG t₁ Λ₁ hTG₁ _ rfl
    have hRefl : LRel F F' Λ₁ Λ₁ := ((hRel Λ₁ Λ₁ o.out o.out hLO₁ hLO₁).1).2 (hEq.refl _)
    have hStab : stabL F F' Λ₁ = stabY F F' o.out := (hRel Λ₁ Λ₁ o.out o.out hLO₁ hLO₁).2

    have hfib : Subtype.val '' (φ ⁻¹' {o}) =
        {κ | ∃ (t : TauC Y u u') (Λ' : LV D), TG F F' t Λ' ∧ LRel F F' Λ₁ Λ' ∧ key t = κ} := by
      ext κ
      constructor
      · rintro ⟨b, hb, rfl⟩
        obtain ⟨t, -, Λ, h1, h2, -, h4⟩ := hyOf b
        have hb' : φ b = o := hb
        refine ⟨t, Λ, h1, ((hRel Λ₁ Λ o.out (yOf b) hLO₁ h2).1).2 (hout o _ hb'), h4⟩
      · rintro hκ
        obtain ⟨t, hTG, hkey⟩ := hcarry κ hκ
        have htS : t ∈ TS := hTS t₁ t Λ₁ Λ₁ hTG₁ hTG
          (fun p => ⟨1, Subgroup.one_mem _, by
            simp [LocNG.img]⟩) ht₁
        have hmem : κ ∈ {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ} :=
          ⟨t, htS, Λ₁, o.out, hTG, hLO₁, ho, hkey⟩
        refine ⟨⟨κ, hmem⟩, ?_, rfl⟩
        show φ ⟨κ, hmem⟩ = o
        obtain ⟨t', -, Λ', h1, h2, -, h4⟩ := hyOf ⟨κ, hmem⟩
        rw [hφ]
        simp only
        rw [← Quot.out_eq o]
        exact Quot.sound (hwd t' t Λ' Λ₁ _ _ h1 hTG h2 hLO₁ (h4.trans hkey.symm))
    have hconst : ∀ b : φ ⁻¹' {o}, ENNReal.ofReal (ω b.1) = ENNReal.ofReal (wt t₁ ^ 2) := by
      intro b
      have hb : b.1.1 ∈ Subtype.val '' (φ ⁻¹' {o}) := ⟨b.1, b.2, rfl⟩
      rw [hfib] at hb
      obtain ⟨t, hTG, hkey⟩ := hcarry _ hb
      rw [hω b.1 t hkey, hwt t Λ₁ hTG hRefl]
    rw [tsum_congr hconst, ENNReal.tsum_set_const, ← Subtype.val_injective.encard_image, hfib, hmass, hStab]
  · rw [if_neg ho]
    refine ENNReal.tsum_eq_zero.2 fun b => (ho ?_).elim
    have hb : φ b.1 = o := b.2
    rw [← hb]
    exact hImg b.1

theorem weights_add_up_to_mass : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ TS : Set (TauC Y u u'), LocClosed F F' Z FP TS → ∀ (t₀ : TauC Y u u') (Λ₀ : LV D) (y₀ d : Dat Z FP), t₀ ∈ TS → TG F F' t₀ Λ₀ → LocOver Λ₀ y₀ → InGen d y₀ → ∀ K, K = {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ} → ∀ ω : K → ℝ, (∀ κ : K, ∀ t : TauC Y u u', key t = κ.1 → ω κ = wt t ^ 2) → ∑' κ : K, ENNReal.ofReal (ω κ) = massA F F' d :=
  weights_add_up_to_mass_of GlobalTheory.T.equivalence_complementUnitaryOrbit_localInnerDatum_at_place GlobalTheory.T.genus_stable_under_rationalComplementGroup

end GlobalTheory.Unfold.SumK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAdelicQuotientVolumePosLtTop
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem fundDom_volume_pos_lt_top : VolumeStep → ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf]
    [μf.IsHaarMeasure] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∀ p q : ℕ, HasSig I p q → 2 ≤ p →
    0 < I.muA μf fund ∧ I.muA μf fund < ⊤ := by
  intro hstep I μf _ _ fund hfund p q hsig hp
  obtain ⟨hcov, hpos⟩ := GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter I μf fund Set.univ hfund MeasurableSet.univ
    (fun _ _ _ _ => Set.mem_univ _)
  rw [Set.univ_inter] at hcov
  refine ⟨hpos, ?_⟩
  obtain ⟨⟨I₀, hsame, hsig₀⟩, hratio⟩ := GlobalTheory.T.hermVolumeRatioSameKind_of_volumeRatioInduction hstep I p q 2 0 hsig hp (Nat.zero_le _) le_rfl
  choose c hc using fun v : InfinitePlace I.F => GlobalTheory.T.riemannianHaarGauge_exists_pos_unique I.n (I.ε v)
  choose c₀ hc₀ using fun v : InfinitePlace I₀.F => GlobalTheory.T.riemannianHaarGauge_exists_pos_unique I₀.n (I₀.ε v)
  obtain ⟨-, hlc, hsc, -⟩ := GlobalTheory.CongTop.adelic_topology I₀
  obtain ⟨-, -, -, hK, -⟩ := GlobalTheory.CongTop.adelic_topology I
  have hg : IsGaugeAll I c := fun v => (hc v).2.1
  have hg₀ : IsGaugeAll I₀ c₀ := fun v => (hc₀ v).2.1
  let μ₀ : Measure I₀.Gf := Measure.haar
  have heq := hratio I₀ hsame hsig₀ c μf c₀ μ₀ hg hg₀
  have hdef := GlobalTheory.T.unitaryGaugeVolume_le_classNumber_definite I₀ 2 hsig₀ c₀ μ₀ hg₀
  have hcl := GlobalTheory.T.rank_two_definite_unimodular_hermitian_class_bound I₀.E I₀.cm.cmUnram
  have h₀ : gaugeVol I₀ c₀ μ₀ < ⊤ :=
    hdef.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hcl.trans_lt ENNReal.ofReal_lt_top))
  have hfin : gaugeVol I c μf < ⊤ := by
    rw [heq]
    exact ENNReal.mul_lt_top h₀ ENNReal.ofReal_lt_top
  rw [gaugeVol, hcov] at hfin
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  have hcpos : ENNReal.ofReal (∏ v, c v) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Finset.prod_pos fun v _ => (hc v).1)).ne'
  rw [htop, ENNReal.mul_top hcpos, ENNReal.top_div_of_ne_top hK.measure_lt_top.ne] at hfin
  exact lt_irrefl _ hfin

end GlobalTheory.FlagMeas
end

