import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0025
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0053
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0383
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0462
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0460
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0469
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0473
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0020
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GoodLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0067
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0038
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefWeightedLocUncond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InstFactDecLow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0257
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0046
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0036
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCharPfRat
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0024
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0287
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0338
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0474
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphismCovolumeEqLatticeMass
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovMass

variable {D : D7} (X : HidaSetting D)

noncomputable def realPt (γ : Formalism.HermitianLatticesTheory.isom (VS D).hT) : X.B.I.Ginf :=
  (Classical.choose ((GlobalTheory.RatIsomPoint.ratLink_points D X).1 γ.1 γ.2)).1

theorem realPt_spec {γ : Formalism.HermitianLatticesTheory.isom (VS D).hT} {x : X.B.I.GA} (h : RatLink X x γ.1) : realPt X γ = x.1 := by
  have hs := Classical.choose_spec ((GlobalTheory.RatIsomPoint.ratLink_points D X).1 γ.1 γ.2)
  unfold realPt
  rw [hs.2 x h]

theorem realPt_link (γ : Formalism.HermitianLatticesTheory.isom (VS D).hT) : ∃ x : X.B.I.GA, RatLink X x γ.1 ∧ realPt X γ = x.1 :=
  ⟨_, (Classical.choose_spec ((GlobalTheory.RatIsomPoint.ratLink_points D X).1 γ.1 γ.2)).1, rfl⟩

noncomputable def realPtHom : Formalism.HermitianLatticesTheory.isom (VS D).hT →* X.B.I.Ginf where
  toFun := realPt X
  map_one' := by
    obtain ⟨x, hx, e⟩ := realPt_link X 1
    have h := ((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x x _ _ hx hx)
    have h2 := ((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x (x⁻¹) _ _ hx h.2.1).1
    have h3 : RatLink X (x * x⁻¹) (1 : Formalism.HermitianLatticesTheory.isom (VS D).hT).1 := by simpa using h2
    rw [realPt_spec X h3]; simp
  map_mul' := by
    intro γ δ
    obtain ⟨x, hx, ex⟩ := realPt_link X γ
    obtain ⟨y, hy, ey⟩ := realPt_link X δ
    have h := ((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x y _ _ hx hy).1
    rw [realPt_spec X (γ := γ * δ) h, ex, ey]; rfl

theorem realPtHom_injective : Function.Injective (realPtHom X) := by
  intro γ δ h
  obtain ⟨x, hx, ex⟩ := realPt_link X γ
  obtain ⟨y, hy, ey⟩ := realPt_link X δ
  have h' : x.1 = y.1 := by rw [← ex, ← ey]; exact h
  exact Subtype.ext (((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x y _ _ hx hy).2.2 h')

theorem realPts_eq_map (H : Subgroup ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (hH : H ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    realPts X (H : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) = ((H.subgroupOf (Formalism.HermitianLatticesTheory.isom (VS D).hT)).map (realPtHom X) : Set X.B.I.Ginf) := by
  ext y
  constructor
  · rintro ⟨x, n, hx, rfl, hn⟩
    exact ⟨⟨n, hH hn⟩, hn, realPt_spec X (γ := ⟨n, hH hn⟩) hx⟩
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨x, hx, ex⟩ := realPt_link X γ
    exact ⟨x, γ.1, hx, ex, hγ⟩

theorem realPts_countable (S : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) : (realPts X S).Countable := by
  have := Formalism.L2.SG.TermOp.Vanish.countable_nf X.B.I.E
  have hsub : realPts X S ⊆ ⋃ M : Fin X.B.I.n → Fin X.B.I.n → X.B.I.E,
      {y : X.B.I.Ginf | ∀ v, uMat (y v) = (X.B.I.P v)⁻¹ * (Matrix.of M).map (X.B.I.φ v) * X.B.I.P v} := by
    rintro _ ⟨x, n, ⟨M, -, h1, -⟩, rfl, -⟩
    exact Set.mem_iUnion.2 ⟨fun i j => (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) i j, h1⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion fun M => Set.Subsingleton.countable ?_)
  intro y hy y' hy'
  funext v
  exact Subtype.ext (Units.ext ((hy v).trans (hy' v).symm))

end GlobalTheory.CovMass

theorem GlobalTheory.CovMass.covol_eq_mass : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → ∀ μR, Formalism.L2.SG.VolPin.IsPinnedR t₀ w μR → ∀ K : Set X.B.I.Ginf, (MeasurableSet K ∧ ∀ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀, ∃! s, s ∈ ROinf t₀ ∧ s * y ∈ K) → (μR K).toReal = (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) * G.mu (c.lat ρ t₀.lam) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv hrel μR hPin K hK
  obtain ⟨hKm, hKu⟩ := hK
  have hlink := GlobalTheory.RatIsomPoint.ratLink_points D X
  have hgrp := GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  have hterm := (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv).1
  obtain ⟨KA, ⟨hKAm, hKAu⟩, hKA⟩ :=
    GlobalTheory.T.covolume_integralStabiliser_normalisedHaar D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv hrel μR hPin
  have hRO := GlobalTheory.T.realPoints_termAutomorphisms_eq_movedStabilizer D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  obtain ⟨hfin1, hfin2⟩ := GlobalTheory.T.latticeStabiliser_commensurable_integralPoints (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) _ _ G hk (c.lat ρ t₀.lam) hterm.1

  let cj : ((VS D).V ≃ₗ[D.host.E] (VS D).V) →* G.GLV :=
    { toFun := c.grp ρ
      map_one' := by ext x; simp [GlobalTheory.HL.GCoord.grp]
      map_mul' := by intro m n; ext x; simp [GlobalTheory.HL.GCoord.grp] }
  have hcj : ∀ n, cj n = c.grp ρ n := fun _ => rfl
  have hcjs : Function.Surjective cj := fun x => hgrp.2.2.2.1 ρ x
  have hconj : ∀ n, c.grp (ρ * t₀.lin) (t₀.lin⁻¹ * n * t₀.lin) = c.grp ρ n := by
    intro n
    have h1 : ∀ y, t₀.lin (t₀.lin⁻¹ y) = y := fun y => by
      show (t₀.lin * t₀.lin⁻¹) y = y
      rw [mul_inv_cancel]; rfl
    have h2 : ∀ z, t₀.lin ((ρ * t₀.lin).symm z) = ρ.symm z := fun z => by
      rw [LinearEquiv.eq_symm_apply]; exact (ρ * t₀.lin).apply_symm_apply z
    ext x
    simp only [GlobalTheory.HL.GCoord.grp, LinearEquiv.trans_apply, LinearEquiv.mul_apply, LinearEquiv.symm_trans_apply, h1, h2]

  have hStN : ∀ g, g ∈ G.St → g ∈ G.N := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', (Subgroup.mem_inf.1 hg').1, he⟩
  have hStN' : ∀ g, g ∈ G.St → g ∈ G.N' := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', (Subgroup.mem_inf.1 hg').2, he⟩
  have hK0St : G.K0 ≤ G.St := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', hg'.1.1, he⟩
  have hLSt : G.stabL (c.lat ρ t₀.lam) ≤ G.St := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', hg'.1, he⟩
  have hStI : G.St.comap cj ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun n hn =>
    ((hgrp.1 n).2 (hStN _ hn)).1
  set P := G.K0.comap cj with hP
  set Q := (G.stabL (c.lat ρ t₀.lam)).comap cj with hQ
  have hPI : P ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun n hn => hStI (hK0St hn)
  have hQI : Q ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun n hn => hStI (hLSt hn)
  set A := (P.subgroupOf (Formalism.HermitianLatticesTheory.isom (VS D).hT)).map (GlobalTheory.CovMass.realPtHom X) with hA
  set B := (Q.subgroupOf (Formalism.HermitianLatticesTheory.isom (VS D).hT)).map (GlobalTheory.CovMass.realPtHom X) with hB
  have hAset : (A : Set X.B.I.Ginf) = realPts X {σ | c.grp ρ σ ∈ G.K0} :=
    (GlobalTheory.CovMass.realPts_eq_map X P hPI).symm
  have hBset : (B : Set X.B.I.Ginf) = Formalism.L2.SG.TermOp.ROinf t₀ := by
    rw [hRO]; exact (GlobalTheory.CovMass.realPts_eq_map X Q hQI).symm
  have hAmem : ∀ y, y ∈ A ↔ y ∈ realPts X {σ | c.grp ρ σ ∈ G.K0} := fun y => by
    rw [← hAset]; rfl
  have hBmem : ∀ y, y ∈ B ↔ y ∈ Formalism.L2.SG.TermOp.ROinf t₀ := fun y => by
    rw [← hBset]; rfl

  obtain ⟨γw, s, s', μw, hγw, hs, hs', hdec, hμwH, hμwS, hμR⟩ := hPin
  have hH := Formalism.L2.SG.Pf.VolPinAsm.pinned_haar t₀ w γw s s' μw hs hs' hdec hμwH
  rw [← hμR] at hH
  have hAR : ∀ y ∈ A, y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀ := by
    intro y hy
    obtain ⟨x, n, hx, rfl, hn⟩ := (hAmem y).1 hy
    have hnS : c.grp ρ n ∈ G.St := hK0St hn
    refine ⟨((hlink.2.2 u x n hx).1).1 ((hgrp.1 n).2 (hStN _ hnS)), ?_⟩
    have hm : t₀.lin⁻¹ * n * t₀.lin ∈ NRat (lf D (X.Fu u')) :=
      (hgrp.2.1 _).2 (by rw [hconj]; exact hStN' _ hnS)
    have hl : RatLink X (t₀.pt⁻¹ * x * t₀.pt) (t₀.lin⁻¹ * n * t₀.lin) :=
      (hlink.2.1 _ _ _ _ (hlink.2.1 _ _ _ _ (hlink.2.1 _ _ _ _ t₀.rep.2.1 t₀.rep.2.1).2.1 hx).1 t₀.rep.2.1).1
    have h2 := ((hlink.2.2 u' _ _ hl).1).1 hm
    simpa [Prod.fst_mul, Prod.fst_inv] using h2
  have hBR : ∀ y ∈ B, y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀ := fun y hy =>
    Formalism.L2.SG.Pf.LoopBPin.roinf_sub_rset t₀ ((hBmem y).1 hy)
  haveI hCA : Countable A := by
    have := (GlobalTheory.CovMass.realPts_countable X {σ | c.grp ρ σ ∈ G.K0}).to_subtype
    rw [← hAset] at this; exact this
  haveI hCB : Countable B := by
    have := (GlobalTheory.CovMass.realPts_countable X {σ | c.grp ρ σ ∈ G.stabL (c.lat ρ t₀.lam)}).to_subtype
    rw [← hRO, ← hBset] at this; exact this

  have hiA : B.relIndex A = (G.stabL (c.lat ρ t₀.lam)).relIndex G.K0 := by
    rw [hA, hB, Subgroup.relIndex_map_map_of_injective _ _ (GlobalTheory.CovMass.realPtHom_injective X),
      Subgroup.relIndex_subgroupOf hPI, hQ, hP, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective hcjs]
  have hiB : A.relIndex B = G.K0.relIndex (G.stabL (c.lat ρ t₀.lam)) := by
    rw [hA, hB, Subgroup.relIndex_map_map_of_injective _ _ (GlobalTheory.CovMass.realPtHom_injective X),
      Subgroup.relIndex_subgroupOf hQI, hQ, hP, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective hcjs]
  have hcov := Formalism.L2.SG.Pf.CovolIdx.covol_commens μR (Formalism.L2.SG.TermOp.Vanish.Rset t₀) hH.2.2.1 A B
    (fun x hx => hH.2.2.2 x (hAR x hx)) (fun x hx => hH.2.2.2 x (hBR x hx))
    (fun x hx y hy => Formalism.L2.SG.Pf.VolPinAsm.rset_mul t₀ (hAR x hx) hy)
    (fun x hx y hy => Formalism.L2.SG.Pf.VolPinAsm.rset_mul t₀ (hBR x hx) hy) KA K hKAm hKm
    (fun y hy => by simpa only [hAmem] using hKAu y hy) (fun y hy => by simpa only [hBmem] using hKu y hy)
    (by rw [hiA]; exact hfin1) (by rw [hiB]; exact hfin2)
  rw [hiA, hiB, hKA] at hcov
  set a := (G.stabL (c.lat ρ t₀.lam)).relIndex G.K0 with ha
  set b := G.K0.relIndex (G.stabL (c.lat ρ t₀.lam)) with hb
  set gi : ℝ := ((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹ with hgi
  have hgi0 : 0 ≤ gi := by rw [hgi]; positivity
  have hbne : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hfin2
  have hKeq : μR K = ENNReal.ofReal gi * (a : ℝ≥0∞) / (b : ℝ≥0∞) := by
    rw [hcov, ENNReal.mul_div_cancel_right hbne (by simp)]
  rw [hKeq, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofReal hgi0]
  simp only [ENNReal.toReal_natCast]
  unfold GlobalTheory.HL.GFrames.mu GlobalTheory.HL.invVol
  rw [← ha, ← hb]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConstructedSpectralObjectsIrreducibilityConditio
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl Formalism.IndefR.principalLevelFrame
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

namespace GlobalTheory.Sat

theorem ties_at : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (F0 : ∀ u, Forms0 D u) (s : SAt R F eE F0) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r), StdPsi hF PY → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotE R.θ PY (R.MY 0) (JR R F) (chiR R F) R.e0 (rep (D.what₂.ft σ))) → GlobalTheory.LabPin.TypeLab D rep → GoodFTAll D → Formalism.MainNotions.S.AutTie D s.P.X.B s.P.X.pl ∧ RowDictTie s.P.X s.P.G s.S.hI.eHH ∧ GlobalTheory.LabPin.LabTie s.P.X s.S.hI.eHH := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F eE F0 s PY hF rep hP hiso hT hG
  exact ⟨s.S.autTie, s.S.rowTie,
    GlobalTheory.T.realisationLabels_normalised_of_rowsTypes_levels D s.P.X s.P.inst s.t PY hF G' Pl0 T A Ks R eE s.P.G s.S.j s.S.hI.eHH rep F hP s.P.pin s.S.rowPin s.rowJ
      s.see.levelMatchA hiso hT hG⟩

end GlobalTheory.Sat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBruhatFunctionLocalBesselIntegralEqL2MassStatement
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bruhatFunction_localBesselIntegral_eq_L2Mass : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word) (τ : D.what₂.Tau), ∃ β : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞, Measurable β ∧ (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))) = 1) ∧ ∫⁻ y, β y * ‖X.Wloc u (vOf X τ) y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) = l2SG (C.nuS u τ) (phiOf hB u τ) := by
  first | exact @GlobalTheory.SlocTie.loc_main | exact GlobalTheory.SlocTie.loc_main | (intros; apply GlobalTheory.SlocTie.loc_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLocalObjectFamilyClassesDetermineRowsStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localObjectFamily_classesDetermineRows : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl), (∀ t ∈ TS, t.G ≠ 0) → (∀ t ∈ TS, ∀ t' ∈ TS, cls t = cls t' → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t') → ∀ t₀ ∈ TS, t₀.relevant → ∃ Fm : LocFam (zOf Y) Cl (NuC D), FamTie TS cls (nmlOf Y u u') (ptPN t₀) Fm ∧ (∀ p ∈ Fm.P, (Fm.FP p).RelG (LocNG.theta ((zOf Y).M p))) ∧ (∀ p ∈ Fm.P, ∃ (d : LocNG.Datum (Fm.FP p)) (t : Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS), LocNG.IsTermOver (Fm.FP p) d t) ∧ (∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) ∧ (∀ c, 0 ≤ Fm.rw c) := by
  first | exact @GlobalTheory.FamGen.exists_famTie | exact GlobalTheory.FamGen.exists_famTie | (intros; apply GlobalTheory.FamGen.exists_famTie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocDatCOfBesselOfW
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.TypeAsm

theorem locDatC_of_besselOfW (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) : LocDatC := by
  haveI : Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc := ⟨GlobalTheory.Sloc.CoefWeighted.coefWeightedLoc_uncond⟩
  haveI : Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow := ⟨GlobalTheory.DecTransport.decLow_main⟩
  intro D X hne hG hT
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  have hB : WuBessel C := Formalism.L2.SG.Pf.wuBesselOfLoc_all C hG hBW
    (Formalism.L2.SG.Pf.LocF.locFactor_holds hG C) (fun τ => Formalism.L2.SG.Pf.dsTr C τ)
    (fun τ => Formalism.L2.SG.Pf.haarTr C τ) (fun u τ => Formalism.L2.SG.Pf.colsTypeTr C u τ)
  refine ⟨C, hB, Formalism.L2.SG.Pf.LocF.locFactor_holds hG C, fun u τ => ⟨?_, ?_⟩⟩
  · exact goodW_of C u u τ (Formalism.L2.SG.Pf.colsTypeTr C u τ) (Formalism.L2.SG.Pf.colsTypeTr C u τ)
      (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.haarTr C τ)
  · exact goodS_of _ u u τ (Formalism.L2.SG.Pf.goodSRest_all hG hT _ u u τ)

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataTailBoundClosedFormLargeGaps
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TypeAsm.TailTopGap

theorem tailP_of_gap : GlobalTheory.GapIn.Hyp → TailP := by
  intro hH Cg cb Cw cT CT C0 _ _
  obtain ⟨CH, hCH, hmom⟩ := GlobalTheory.T.majorantLength_twoSidedMoments_largeGap hH Cg cb Cw cT CT C0
  refine ⟨CH, hCH, fun C₁ => ⟨0, max 1000 (C₁ : ℝ), fun C' Cl _ hCl D large₂ _ hK hTr => ?_⟩⟩
  have hZ : HypZ D large₂ C' Cl Cg cb Cw cT CT C0 := hK.1
  have h1000 : (1000 : ℝ) ≤ Cl := le_trans (le_max_left _ _) hCl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv, -, -, -, -, hClm, -⟩ := hK.1.1

  have hC₁m : C₁ ≤ D.R.m := by
    have h : (C₁ : ℝ) ≤ (D.R.m : ℝ) := le_trans (le_max_right _ _) (le_trans hCl hClm)
    exact_mod_cast h
  have hrS : D.R.rS ≤ D.R.m := by
    unfold Formalism.BasicNotions.Ranks.rS
    omega
  have hm1 : 1 ≤ D.R.m := le_trans (by norm_num) D.R.two_le_m
  have hq : C₁ * D.R.k * D.R.rS ≤ D.R.k * D.R.m ^ 3 := by
    have h2 : C₁ * D.R.rS ≤ D.R.m ^ 3 :=
      calc C₁ * D.R.rS ≤ D.R.m * D.R.m := Nat.mul_le_mul hC₁m hrS
        _ ≤ D.R.m * D.R.m * D.R.m := Nat.le_mul_of_pos_right _ (by omega)
        _ = D.R.m ^ 3 := by ring
    calc C₁ * D.R.k * D.R.rS = D.R.k * (C₁ * D.R.rS) := by ring
      _ ≤ D.R.k * D.R.m ^ 3 := Nat.mul_le_mul_left _ h2
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  have hH1 : 0 < large₂.sc.b ^ (CH * (D.R.m : ℝ)) := Real.rpow_pos_of_pos hb _

  have hTrpos : ∀ w, 0 < Tr D w := by
    intro w
    have hk : 0 ≤ Formalism.MainNotions.S.Bridge.kaS D ^ (2 * D.R.rS) := (even_two_mul _).pow_nonneg _
    by_contra hneg
    push_neg at hneg
    have h0 : Tr D w * Formalism.MainNotions.S.Bridge.kaS D ^ (2 * D.R.rS) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg hk
    linarith [hTr w]
  have hv0 : 0 < D.host.v := by linarith
  intro τ u W hW A hA

  have side : ∀ W' : LocW D.R.k D.R.rS, GoodW D τ u u 1 W' → ∀ A' : LocS W', GoodS D (lamD D τ) A' →
      TailBd W'.z W'.νS A'.Φ (C₁ * D.R.k * D.R.rS) (large₂.sc.b ^ (CH * (D.R.m : ℝ))) := by
    intro W' hW' A' hA'
    obtain ⟨hM, hI⟩ := hmom D large₂ C' Cl h1000 hZ τ u W' hW' A' hA' _ hq
    obtain ⟨hzW, -, -, -, -, hG, hWH, -, hN, hQ, -, -, hcont, -, -⟩ :=
      (GlobalTheory.T.amplitude_one_side_of_good_local_data D τ u u 1 W' (lamD D τ) A' hv0 one_pos (hTrpos u) (hTrpos u) hW' hA').1
    have hnull : W'.νS {x | Matrix.of x ∉ GG D.R.k D.R.rS} = 0 := by
      have hf := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hWH hN
      exact ae_iff.mp (Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hf.1 hf.2 hQ)
    exact GlobalTheory.T.majorantLengthTailBound_of_moments D.R.k D.R.rS W'.z W'.νS A'.Φ _ _ hzW hH1 hnull hcont hM hI

  exact ⟨side W hW A hA, GlobalTheory.T.majorantLengthTailBound_primed_of_unprimed D τ u 1 (lamD D τ) _ _ side W hW A hA⟩

end GlobalTheory.TypeAsm.TailTopGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisedLiftAmplitudeEqCovolumeMulLocal
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AmpLift.amp_lift : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (s : TT Y u u') (x : Point D.host.E (D.R.rS + 1) × Measure X.B.I.Ginf × Set X.B.I.Ginf), s.relevant → s.G ≠ 0 → s.toTerm.atPt x.1 → Formalism.L2.SG.VolPin.IsPinnedR s x.1 x.2.1 → IsFundR s x.2.2 → (∀ v, ∀ r ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v), ∀ y, Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (r * y)) (X.Wloc u' v ((s.pt.1 v)⁻¹ * (r * y))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u v y) (X.Wloc u' v ((s.pt.1 v)⁻¹ * y))) → ∃ μl νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v)) (μl v)) ∧ (∀ v, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) (νl v)) ∧ (∀ τ, ∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) ((μl (vOf X τ)).map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ))))))) ∧ hsNormSq (Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s) = (Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) ^ 2 * (x.2.1 x.2.2).toReal ^ 2 * ∏ v, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (s.pt.1 v)) := by
  intro D X Y θ C u u' s x hrel _hG _hat hpin hfund hinv
  obtain ⟨μl, hμeq, hHaar, hHR, hroot⟩ := GlobalTheory.T.normalisedMeasure_eq_prod_besselRootMeasures D X Y θ C u u' s x.1 x.2.1 hpin
  obtain ⟨hq, ν, hν⟩ := GlobalTheory.T.exists_quotient_measure_unipotent_stabilisers D X u u' s.pt.1 μl hHaar
  choose νl hνl using hq
  refine ⟨μl, νl, hHaar, hνl, hroot, ?_⟩
  have hν' : IsQuotMeasS X.B.I x.2.1 ν := hμeq ▸ hν
  have hOO := Formalism.L2.SG.Pf.formAllC_holds D X Y u u' s x.2.1 ν x.2.2
    (Formalism.L2.SG.Pf.RelChar.relCharC_holds D X Y u u' s hrel) hHR hν' hfund.1 hfund.2
  have hprod := GlobalTheory.T.realOrbitalIntegral_hsNorm_eq_prod_local D X u u' s.pt.1 μl νl ν hHaar hνl hν hinv
  unfold Formalism.L2.SG.TermOp.ampN
  rw [Formalism.L2.SG.LoopTerm.hsNormSq_smul, Formalism.L2.SG.LoopTerm.hsNormSq_smul, hOO,
    ← Complex.coe_smul, Formalism.L2.SG.LoopTerm.hsNormSq_smul, hprod]
  have hc : Complex.normSq (Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base s.lam') : X.B.I.Gf) s.pt)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Formalism.L2.SG.Pf.FibreCounting.norm_chiN, one_pow]
  rw [hc, Complex.normSq_ofReal, Complex.normSq_ofReal]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PiPulledBackUnipotentMeasureEqBesselImage
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

namespace GlobalTheory

theorem pi_muNl_eq_dnB_image : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (A : Set X.B.I.Ginf), 0 < θ → MeasurableSet A → Measure.pi (fun v => muNl C (X.pl v) v) A = Measure.pi (fun _ : D.what₂.Tau => muNB D θ) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' A) := by
  intro D X θ C A hθ _hA
  have hsf : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.AmpWinGlob.muNv C v) := by
    have key : ∀ (τ : D.what₂.Tau) (w : InfinitePlace X.B.I.F), vOf X τ = w → SigmaFinite (muNl C τ w) := by
      rintro τ w rfl
      exact sf_muNl C τ hθ
    intro v
    exact key (X.pl v) v (X.pl.symm_apply_apply v)
  obtain ⟨hemb, hmap⟩ := Formalism.L2.SG.Pf.AmpWinGlob.map_trInf C hsf hθ
  have h := congrArg (fun μ => μ (Formalism.L2.SG.LoopTerm.trInf C '' A)) hmap
  rw [hemb.map_apply, Set.preimage_image_eq _ hemb.injective] at h
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowWeightsLocalOrbitsSumEqGenusMassStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs Formalism.FourierDecayAlt GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowWeights_localOrbits_sum_eq_genusMass : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) (Fm : LocFam (zOf Y) Cl (NuC D)), Based (zOf Y) Fm.FP (Tu D u) (Tu D u') F F' → ClsRow TS cls → LocClosed F F' (zOf Y) Fm.FP TS → (∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) → (∀ p, p ∉ Fm.P → ∀ t ∈ TS, ptPN t = toPts w → OverOrb Fm t p (Fm.d0 p)) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ ∀ p, p ∉ Fm.P → ∃ τ, LocNG.IsTermOver (Fm.FP p) (Fm.d0 p) τ ∧ τ.abelian₂ = lattice₂ D (zOf Y).M p Λ₀) → (∀ c ν, (Fm.dat c ν = none → ¬ ∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧ ∀ d, Fm.dat c ν = some d → (∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧ ∀ t ∈ TS, cls t = c → ptPN t = toPts w → nmlOf Y u u' t = ν → (∀ p (hp : p ∈ Fm.P), OverOrb Fm t p (d ⟨p, hp⟩).1) ∧ Fm.rw c = (wt t) ^ 2) → ∀ d : (∀ p : {p // p ∈ Fm.P}, {d // d ∈ Fm.Ds p.1}), (∃ x : Cl × NuC D, Fm.dat x.1 x.2 = some d) → ∀ dd : Dat (zOf Y) Fm.FP, (∀ p (hp : p ∈ Fm.P), dd p = (d ⟨p, hp⟩).1) → (∀ p, p ∉ Fm.P → dd p = Fm.d0 p) → (∀ p, ∃ τ, LocNG.IsTermOver (Fm.FP p) (dd p) τ) ∧ ∑' x : {x : Cl × NuC D // Fm.dat x.1 x.2 = some d}, ENNReal.ofReal (Fm.rw x.1.1) = massA F F' dd := by
  first | exact @GlobalTheory.Unfold.GenusRows.rows_mass_genus | exact GlobalTheory.Unfold.GenusRows.rows_mass_genus | (intros; apply GlobalTheory.Unfold.GenusRows.rows_mass_genus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubgroupHaarEqConstSmulPiLocalMeasuresStatement
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subgroupHaar_eq_const_smul_pi_localMeasures : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muH u = κ • Measure.pi (fun v => muHl C u (X.pl v) v) := by
  first | exact @GlobalTheory.MuHPi.muH_eq_pi | exact GlobalTheory.MuHPi.muH_eq_pi | (intros; apply GlobalTheory.MuHPi.muH_eq_pi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentHaarEqConstMulTransportedProduct
section
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
  Formalism.L2.SG.Pf.AmpWinLoc Formalism.L2.SG.Pf.WuDec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory

theorem muN_eq_const_mul_pi_trI : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB →
    ∀ u : D.what₂.Word, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ A : Set X.B.I.Ginf, MeasurableSet A →
      X.muN u A = c * Measure.pi (fun _ : D.what₂.Tau => muNB D 1) (trI C '' A) := by
  intro D X C hB hG u
  choose hsfN hsfH hN hH hH1 hconc β hβm hβ1 hloc using
    Formalism.L2.SG.Pf.AmpWinGlob.place_all C u hG.1 hB
  have hpiN : Set.pi Set.univ (Nloc X u) = X.NinfU u := by
    ext s; simp only [Set.mem_pi, Set.mem_univ, true_implies]; exact Iff.rfl
  obtain ⟨h1, h2, h3, h4⟩ := X.muN_haar u
  obtain ⟨cN, hcN0, hcNt, hcN⟩ := QPK.haar_measure_uniqueness X.B.I.Ginf (Set.pi Set.univ (Nloc X u))
    (isClosed_set_pi fun v _ => (place_facts X u v).1) (QPK.isGrp_pi _ fun v => (place_facts X u v).2.2.1)
    (X.muN u) (Measure.pi (Formalism.L2.SG.Pf.AmpWinGlob.muNv C)) ⟨h1, h2, by rw [hpiN]; exact h3, by rw [hpiN]; exact h4⟩
    (QPK.invOn_pi _ _ hN)
  obtain ⟨hemb, hmapT⟩ := Formalism.L2.SG.Pf.AmpWinGlob.map_trInf C (fun v => hsfN v) one_pos
  refine ⟨cN, hcN0, hcNt, fun A _ => ?_⟩
  have htr : trI C = Formalism.L2.SG.LoopTerm.trInf C := rfl
  have hcov : Measure.pi (Formalism.L2.SG.Pf.AmpWinGlob.muNv C) A =
      Measure.pi (fun _ : D.what₂.Tau => muNB D 1) (trI C '' A) := by
    rw [htr, show Measure.pi (fun _ : D.what₂.Tau => muNB D 1) = Formalism.L2.SG.LoopTerm.dnB D 1 from rfl, ← hmapT,
      hemb.map_apply, Set.preimage_image_eq _ hemb.injective]
  rw [hcN, Measure.smul_apply, smul_eq_mul, hcov]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentHaarEqConstSmulPiLocalMeasuresStatement
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentHaar_eq_const_smul_pi_localMeasures : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muN u = κ • Measure.pi (fun v => muNl C (X.pl v) v) := by
  first | exact @GlobalTheory.MuNPi.muN_eq_pi_muNl | exact GlobalTheory.MuNPi.muN_eq_pi_muNl | (intros; apply GlobalTheory.MuNPi.muN_eq_pi_muNl <;> assumption)
end

