import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0351
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0071
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0156
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0595
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0492
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0594
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0504
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdmissibleRanksAllMembers
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MemberRanks

theorem typePrimesLarge_of_val {C} {cD ch : ℝ} {D : D7} (L : SizeData₂ D) (hv : Val C cD ch L) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnipotentLevelStabilisers.TypePrimesLarge D := by
  intro i
  have h1 : ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (D.host.g i : ℝ) := (hv.host.2.2.2.2.1 i).1
  have hb : 1 ≤ L.sc.b := by
    unfold Scale.b
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _)
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h2 : (D.R.k : ℝ) ^ 8 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 :=
    pow_le_pow_left₀ hk0 (le_mul_of_one_le_right hk0 hb) 8
  have h3 : D.R.k ^ 8 ≤ D.host.g i := by exact_mod_cast h2.trans h1
  have hf : D.R.f ≤ D.R.k := D.R.f_le_k
  have hk : 5 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have h4 : D.R.k ^ 3 ≤ D.R.k ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h5 : 2 * D.R.f * D.R.k + 1 < D.R.k ^ 3 := by
    have : D.R.f * D.R.k ≤ D.R.k * D.R.k := Nat.mul_le_mul_right _ hf
    have h6 : 5 * (D.R.k * D.R.k) ≤ D.R.k ^ 3 := by
      rw [pow_succ, pow_two, mul_comm 5]; exact Nat.mul_le_mul_left _ hk
    have h7 : 25 ≤ D.R.k * D.R.k := Nat.mul_le_mul hk hk
    rw [mul_assoc]; omega
  omega

theorem dstar_mass (K : Ctx) (X : Stages) (hO : K.Over X.B.toPre)
    (hd : ∀ τ, X.S.dsig τ = Vol.trueDsig X.B.R (X.B.hc τ)) :
    X.toD7.what₂.Dstar =
      StandardLattice.DstarP X.toD7 (X.toD7.host.g 0) (X.toD7.host.g 1) (StandardLattice.massI X.toD7 X.toD7.R.r) X.toD7.dsig := by
  have e : X.toD7.what₂.Dstar = X.B.Dstar := (X.toD7.Dstar_eq X.toD7.u₀).symm.trans (X.C.A_Dstar _)
  rw [e, hO.sizes.2]
  unfold DsPre StandardLattice.DstarP
  congr 1
  exact Finset.prod_congr rfl fun τ _ => (hd τ).symm

theorem columnRowRanks_admissible_of_massFormula (D : D7) (Lv : LevelData D) (C : Formalism.L2.Forms.ColsTiedSym D)
    (hD : D.what₂.Dstar = StandardLattice.DstarP D (D.host.g 0) (D.host.g 1) (StandardLattice.massI D D.R.r) D.dsig)
    (hG : StandardLattice.GBig D) (hT : ∀ u, Formalism.MainNotions.S.SplitsE D (D.mem u).A.T) : LocalBesselAndTopKernel.FamilyMidVolume D := by
  have h4 := Formalism.MainNotions.StandardLattice.HarishChandraReduction.rankFormula_of_classNumber D Lv (GlobalTheory.ColClassNumber.classNumber_all D Lv)
  intro V _ _ _ _ h L _
  refine ⟨fun hL u => ?_, fun hL => ?_⟩
  · have e := h4 hG (Formalism.MainNotions.J.splitsF_g D) u (Formalism.MainNotions.J.splitsF_of_splitsE D _ (D.mem u).A.T_prime (hT u))
      (Formalism.MainNotions.Ext.Lw.mu0Tie_of_sym C u)
    have em : Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D D.R.k := Formalism.MainNotions.J.mass_ortho_eq hL (Formalism.MainNotions.J.std_ortho D.host.E D.R.k)
    rw [em, ← Formalism.MainNotions.J.idxColTie_holds D]
    exact e
  · have em : Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D D.R.r := Formalism.MainNotions.J.mass_ortho_eq hL (Formalism.MainNotions.J.std_ortho D.host.E D.R.r)
    rw [em, ← Formalism.MainNotions.J.idxRowTie_holds D, hD]
    rfl

theorem admissible_ranks_at_member : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D _ _ _ => Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D) := by
  intro hL p
  refine GlobalTheory.Fc.RowE.of_all fun κ K β c b h0 h1 h2 => ?_
  obtain ⟨hv, -⟩ :=
    GlobalTheory.Fc.built_val GlobalTheory.Fc.Bundle (Bl.IsGoodE p.s) (Bl.IsLinked p) κ β.D β.O c b (GlobalTheory.Fc.Built.intro h0 h1 h2)
  exact columnRowRanks_admissible_of_massFormula β.D β.O.lev b.R.T.cols (dstar_mass K β.X β.c.isOver β.c.dsig_eq)
    (GlobalTheory.Proof.ColumnStabilizerTrivialLocal.gBig_of_large (typePrimesLarge_of_val β.O.L hv)) (fun u => GlobalTheory.CollCompare.splits_level β.D u)

end GlobalTheory.MemberRanks
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistPlacesIntegralPeelOfDoubling
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChainTw.Peel

theorem qPeel_holds : GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, QPeel D := by
  intro hU hC D hgap c w hw k hk s s' hs hs' p hp m X hX a ha u₁ u₂ φ hq v₁ hv₁ v₂ hv₂ z hz hlev
  classical
  have hhaar : s.ν.IsHaarMeasure := by
    obtain ⟨hr, -, hfl⟩ := hs
    exact hfl.haar
  have : BorelSpace (GA D s.V) := ⟨rfl⟩
  obtain ⟨-, hmO, hlevIff, -, -, -⟩ := GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D c w hw k hk.le s hs
  have hmL : MeasurableSet (levSet s) := (GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D c w hw k hk.le s hs).1
  set F := flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z with hF
  have hloc := GlobalTheory.T.flatIntegrand_localFactor_splits_twistPlace hU hC D hgap c w hw k hk s s' hs hs' p hp m X hX a ha u₁ u₂ φ hq v₁ hv₁ v₂ hv₂ z hz
  choose J μ ζ hJo hμ hμJ hζi hζ1 hJiff hζv hFx using hloc

  have hQPg : ∀ PP ∈ w.Q, PP ∈ c.Pg := fun PP h => by rw [hw.union]; exact Finset.mem_union_right _ h
  have hQS : ∀ PP ∈ w.Q, PP.under (𝓞 D.host.F) ∈ c.S := fun PP h => Finset.mem_image_of_mem _ (hQPg PP h)
  have hinj := GlobalTheory.LevelPlaces.injOn_under D c hw.com

  let cond : Pl D.host.E → GA D s.V → Prop := fun PP g => gAt s.V (.inl (PP.under (𝓞 D.host.F))) g ∈ Lev.levG s.V s.β s.L
  let ET : Finset (Pl D.host.E) → Set (GA D s.V) := fun T => intOff c s ∩ {g | ∀ PP ∈ T, cond PP g}
  have hET : ∀ T, T ⊆ w.Q → MeasurableSet (ET T) := by
    intro T hT
    have e : {g : GA D s.V | ∀ PP ∈ T, cond PP g} = ⋂ PP ∈ T, {g | cond PP g} := by ext g; simp
    refine hmO.inter ?_
    rw [e]
    refine Finset.measurableSet_biInter T fun PP hPP => ?_
    have e2 : {g : GA D s.V | cond PP g} = (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram (PP.under (𝓞 D.host.F))) ⁻¹' (J PP (hT hPP) : Set _) := by
      ext g; exact hJiff PP (hT hPP) g
    rw [e2]
    exact ((hJo PP (hT hPP)).preimage (GlobalTheory.AdelicU.continuous_proj D.sp.cm.sig s.V.gram _)).measurableSet

  have hgAt : ∀ (v v' : HeightOneSpectrum (𝓞 D.host.F)), v' ≠ v → ∀ (x : GA D s.V) y,
      gAt s.V (.inl v') (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y) = gAt s.V (.inl v') x := by
    intro v v' hne x y
    show GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v' (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v' (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y)) =
      GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v' (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v' x)
    rw [map_mul, GlobalTheory.AdelicU.proj_emb_ne _ _ hne, mul_one]
  have hOff : ∀ v ∈ c.S, ∀ (x : GA D s.V) y, x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y ∈ intOff c s ↔ x ∈ intOff c s := by
    intro v hv x y
    refine forall_congr' fun v' => imp_congr_right fun hv' => ?_
    have hne : v' ≠ v := fun h => hv' (h ▸ hv)
    rw [map_mul, GlobalTheory.AdelicU.proj_emb_ne _ _ hne, mul_one]

  have key : ∀ T : Finset (Pl D.host.E), T ⊆ w.Q → IntegrableOn F (ET w.Q) s.ν →
      IntegrableOn F (ET (w.Q \ T)) s.ν ∧ (z = (D.R.t : ℝ) / 2 → ∫ g in ET (w.Q \ T), F g ∂s.ν =
        (∏ PP ∈ T, blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ)) * ∫ g in ET w.Q, F g ∂s.ν) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _ h; refine ⟨by simpa using h, fun _ => by simp⟩
    | insert PP T hPT ih =>
      intro hsub hint
      have hPP : PP ∈ w.Q := hsub (Finset.mem_insert_self _ _)
      obtain ⟨ih1, ih2⟩ := ih ((Finset.subset_insert _ _).trans hsub) hint
      set v := PP.under (𝓞 D.host.F) with hvdef
      have hE' : MeasurableSet (ET (w.Q \ insert PP T)) := hET _ Finset.sdiff_subset
      have hinv : ∀ (x : GA D s.V) y, x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y ∈ ET (w.Q \ insert PP T) ↔
          x ∈ ET (w.Q \ insert PP T) := by
        intro x y
        refine and_congr (hOff v (hQS PP hPP) x y) (forall₂_congr fun PP' hPP' => ?_)
        have hne : PP'.under (𝓞 D.host.F) ≠ v := by
          intro h
          have h1 := Finset.mem_sdiff.1 hPP'
          exact h1.2 (hinj (hQPg PP' h1.1) (hQPg PP hPP) h ▸ Finset.mem_insert_self _ _)
        show gAt s.V (.inl (PP'.under (𝓞 D.host.F))) (x * _) ∈ _ ↔ gAt s.V (.inl (PP'.under (𝓞 D.host.F))) x ∈ _
        rw [hgAt v _ hne]
      have hset : ET (w.Q \ insert PP T) ∩ {g | GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v g ∈ J PP hPP} = ET (w.Q \ T) := by
        ext g
        simp only [ET, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨h1, fun PP' hPP' => ?_⟩
          by_cases he : PP' = PP
          · subst he; exact (hJiff PP' hPP g).2 h3
          · refine h2 PP' (Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hPP').1, fun h => ?_⟩)
            rcases Finset.mem_insert.1 h with h | h
            · exact he h
            · exact (Finset.mem_sdiff.1 hPP').2 h
        · rintro ⟨h1, h2⟩
          refine ⟨⟨h1, fun PP' hPP' => h2 PP' (Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hPP').1,
            fun h => (Finset.mem_sdiff.1 hPP').2 (Finset.mem_insert_of_mem h)⟩)⟩, (hJiff PP hPP g).1 (h2 PP ?_)⟩
          exact Finset.mem_sdiff.2 ⟨hPP, hPT⟩
      have hFx' : ∀ x ∈ ET (w.Q \ insert PP T), GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v x = 1 → ∀ y,
          F (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y) = ζ PP hPP y * F x :=
        fun x hx h1 y => hFx PP hPP x hx.1 h1 y
      have hfub := GlobalTheory.T.integral_split_finite_place_fubini D s.V s.ν hhaar v (μ PP hPP) (hμ PP hPP) (J PP hPP) (hJo PP hPP) (hμJ PP hPP)
        (ET (w.Q \ insert PP T)) hE' hinv F (ζ PP hPP) (hζi PP hPP) (hζ1 PP hPP) hFx' (by rw [hset]; exact ih1)
      refine ⟨hfub.1, fun hz2 => ?_⟩
      rw [hfub.2, hset, ih2 hz2, hζv PP hPP hz2, Finset.prod_insert hPT]
      ring

  have hsub : levSet s ⊆ ET w.Q := fun g hg => ⟨((hlevIff g).1 hg).1, fun PP hPP => ((hlevIff g).1 hg).2 _ (hQS PP hPP)⟩
  have hzero : ∀ g ∈ ET w.Q \ levSet s, F g = 0 := by
    rintro g ⟨⟨h1, h2⟩, h3⟩
    by_contra hne
    apply h3
    refine (hlevIff g).2 ⟨h1, fun v hv => ?_⟩
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hv
    rw [hw.union] at hPP
    rcases Finset.mem_union.1 hPP with hP | hP
    · have hc : coefW p.ω m X (p.pt φ) g ≠ 0 := by
        intro h0
        apply hne
        simp only [hF, flatInt, GlobalTheory.Core.Rk.IP.integrand]
        rw [show GlobalTheory.Core.Rk.IP.wcoef p.ω m X (p.pt φ) (p.pt φ) g = coefW p.ω m X (p.pt φ) g from rfl, h0, zero_mul, zero_mul]
      exact GlobalTheory.T.twistedChain_coefficient_supported_principal_level D hgap c w hw k hk s s' hs hs' p hp m X hX φ g hc _
        (by simp only [Twist.S₀, Finset.coe_image]; exact Set.mem_image_of_mem _ hP)
    · exact h2 PP hP
  have hintR : IntegrableOn F (ET w.Q) s.ν := hlev.of_forall_diff_eq_zero (hET _ subset_rfl) hzero
  have hR := key w.Q subset_rfl hintR
  have hE0 : ET (w.Q \ w.Q) = intOff c s := by
    ext g; simp [ET]
  rw [hE0] at hR
  refine ⟨hR.1, fun hz2 => ?_⟩
  rw [hR.2 hz2, setIntegral_eq_of_subset_of_forall_diff_eq_zero (hET _ subset_rfl) hsub hzero]
  rfl

end GlobalTheory.ChainTw.Peel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColsStdOfBWit
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem colsStd_of_bWit {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : Bundle (q.w.D q.Z) q.O c) (h : Bl.BWit q b) :
    q.w.I.Ok ∧ Nonempty (GlobalTheory.Mem.Col2.TC.Pins q.B q.w.px) ∧ GlobalTheory.Mem.Col2.TC.IsTw q.w.I ∧
      Nonempty (GlobalTheory.Mem.Col2.TC.StdC q.w.I q.w.l q.Z b.R.T.cols) ∧ GlobalTheory.AdForm.TwStd (packB b) := by
  have hs := h.recPin.s
  refine ⟨q.w.ok, ⟨q.w.pins⟩, q.x.pin.isTw, ⟨?_⟩, ?_⟩
  · have e : b.R.T.cols = q.x.col.C := hs.cols
    rw [e]
    exact q.x.col.std
  · obtain ⟨he, hstd⟩ := hs.tw
    exact ⟨q.w.l0, _, he, (eqRec_heq _ _).symm, hstd⟩

end GlobalTheory.Fam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsVacuumVectorPrincipalCongruenceSupportStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vacuumVector_principalCongruenceSupport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∃ f, IsThetaFunO ψ A H f ∧ f ≠ 0 ∧ (∀ τ, IsFockVacAt (heisO ψ A H) θ τ (cplxO (sA τ) (sH τ)) f) ∧ IsSphOff ψ A H (frameLat A) (frameLat H) (under Z) f ∧ (∀ κ ∈ prin A β Z, om (κ, 1) f = f) ∧ ∀ ν 𝓕, IsCovolOne (ratL H A) ν 𝓕 → ∀ g ∈ openOff A (frameLat A) (under Z), g ∉ prinInf A β Z → wcoef om ν 𝓕 f f g = 0 := by
  first | exact @GlobalTheory.Core.Rk.Small.exists_small_vac_vec | exact GlobalTheory.Core.Rk.Small.exists_small_vac_vec | (intros; apply GlobalTheory.Core.Rk.Small.exists_small_vac_vec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JointOfFamilyAndServiceStatement
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joint_of_family_and_service : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), FamAllQ W → ServedQ W → Joint W := by
  first | exact @GlobalTheory.MiTop.joint_of_famAllQ | exact GlobalTheory.MiTop.joint_of_famAllQ | (intros; apply GlobalTheory.MiTop.joint_of_famAllQ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LargeGapAllMembers
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk.GapAt

theorem poly_bound {M k m f r L T n t N : ℝ} (hM : 1 ≤ M) (hk1 : 1 ≤ k) (hk : k ≤ M) (hm1 : 1 ≤ m) (hm : m ≤ M)
    (hf0 : 0 ≤ f) (hf : f ≤ M) (hr0 : 0 ≤ r) (hr : r ≤ M) (hL0 : 0 ≤ L) (hL : L ≤ M) (hT : T ≤ M) (hn0 : 0 ≤ n)
    (hn : n ≤ 10 * r * (f + f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m) + 8) (ht0 : 0 ≤ t) (ht : t ≤ 8 * f * r + 4 + T * n)
    (hN : N = k + m * (t + 1)) : 4 * N ^ 3 + 2 * t + 6 ≤ 300000 * M ^ 30 := by
  have hM0 : 0 ≤ M := by linarith
  have hk' : 0 ≤ k - 1 := by linarith
  have hk'' : k - 1 ≤ M := by linarith
  have pw : ∀ a b : ℕ, a ≤ b → M ^ a ≤ M ^ b := fun a b h => pow_le_pow_right₀ hM h
  have h1 : f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m ≤ M ^ 7 := by
    calc f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m ≤ f ^ 2 * (k - 1) ^ 3 * L ^ 2 := div_le_self (by positivity) hm1
      _ ≤ M ^ 2 * M ^ 3 * M ^ 2 := by gcongr
      _ = M ^ 7 := by ring
  have h10 : 0 ≤ f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m := by
    have : 0 ≤ m := by linarith
    positivity
  have h2 : n ≤ 28 * M ^ 8 := by
    have a1 : f ≤ M ^ 7 := by have := pw 1 7 (by norm_num); rw [pow_one] at this; linarith
    have a2 : r * (f + f ^ 2 * (k - 1) ^ 3 * L ^ 2 / m) ≤ M * (2 * M ^ 7) :=
      mul_le_mul hr (by linarith) (by linarith) hM0
    have a3 : M * (2 * M ^ 7) = 2 * M ^ 8 := by ring
    have a4 := pw 0 8 (by norm_num)
    rw [pow_zero] at a4
    rw [mul_assoc] at hn
    linarith
  have h3 : t ≤ 40 * M ^ 9 := by
    have a1 : f * r ≤ M * M := mul_le_mul hf hr hr0 hM0
    have a2 : T * n ≤ M * (28 * M ^ 8) := mul_le_mul hT h2 hn0 hM0
    have a3 : M * (28 * M ^ 8) = 28 * M ^ 9 := by ring
    have a4 := pw 0 9 (by norm_num)
    have a5 := pw 2 9 (by norm_num)
    rw [pow_zero] at a4
    rw [pow_two] at a5
    rw [mul_assoc] at ht
    linarith
  have h4 : N ≤ 42 * M ^ 10 := by
    have a4 := pw 0 9 (by norm_num)
    rw [pow_zero] at a4
    have a1 : m * (t + 1) ≤ M * (41 * M ^ 9) := mul_le_mul hm (by linarith) (by linarith) hM0
    have a3 : M * (41 * M ^ 9) = 41 * M ^ 10 := by ring
    have a5 := pw 1 10 (by norm_num)
    rw [pow_one] at a5
    linarith
  have hN0 : 0 ≤ N := by
    rw [hN]
    have : 0 ≤ m * (t + 1) := mul_nonneg (by linarith) (by linarith)
    linarith
  have h5 : N ^ 3 ≤ 74088 * M ^ 30 := by
    calc N ^ 3 ≤ (42 * M ^ 10) ^ 3 := pow_le_pow_left₀ hN0 h4 3
      _ = 74088 * M ^ 30 := by ring
  have a4 := pw 0 30 (by norm_num)
  have a5 := pw 9 30 (by norm_num)
  rw [pow_zero] at a4
  linarith

theorem rank_bound (s : Scale) (R : Ranks) (h : RankVal s R) :
    4 * ((R.N R.m : ℕ) : ℝ) ^ 3 + 2 * R.t + 6 ≤ 300000 * (4 * s.x ^ (377 : ℝ)) ^ 30 := by
  obtain ⟨-, -, ⟨-, hk⟩, ht⟩ := h
  have hx := s.one_lt_alt.le
  have e0 := s.eps_pos
  have e1 := s.eps_lt
  have hY : 1 ≤ s.x ^ (377 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hk2 : (R.k : ℝ) ≤ 2 * s.x ^ (377 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hx (show 9 / 2 + 10 * s.eps ≤ (377 : ℝ) by linarith)
    linarith
  have hL : s.L ≤ s.x ^ (377 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (show s.eps ≤ (377 : ℝ) by linarith)
  have hL0 : 0 ≤ s.L := Real.rpow_nonneg (by linarith) _
  have n1 := R.two_le_m
  have n2 := R.m_add_three_le_k
  have hm1 : (1 : ℝ) ≤ R.m := by exact_mod_cast (show 1 ≤ R.m by omega)
  have hk1 : (1 : ℝ) ≤ R.k := by exact_mod_cast (show 1 ≤ R.k by omega)
  have hmk : (R.m : ℝ) ≤ R.k := by exact_mod_cast (show R.m ≤ R.k by omega)
  have hfk : (R.f : ℝ) ≤ R.k := by exact_mod_cast (show R.f ≤ R.k from R.f_le_k)
  have hrk : (R.r : ℝ) ≤ 2 * R.k := by
    exact_mod_cast (show R.r ≤ 2 * R.k by unfold Ranks.r; omega)
  have hT : (TOv s : ℝ) ≤ 4 * s.x ^ (377 : ℝ) := by
    have := Nat.ceil_lt_add_one (show 0 ≤ s.x ^ (377 : ℝ) by linarith)
    unfold TOv
    linarith
  have hn : (nWv R s : ℝ) ≤ 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) + 8 := by
    have hk' : (0 : ℝ) ≤ (R.k : ℝ) - 1 := by linarith
    have := Nat.ceil_lt_add_one
      (show 0 ≤ 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8 by positivity)
    unfold nWv
    push_cast
    linarith
  have ht' : (R.t : ℝ) ≤ 8 * (R.f : ℝ) * R.r + 4 + (TOv s : ℝ) * nWv R s := by
    exact_mod_cast (show R.t ≤ 8 * R.f * R.r + 4 + TOv s * nWv R s by omega)
  refine poly_bound (by linarith) hk1 (by linarith) hm1 (by linarith) (Nat.cast_nonneg _) (by linarith) (Nat.cast_nonneg _)
    (by linarith) hL0 (by linarith) hT (Nat.cast_nonneg _) hn (Nat.cast_nonneg _) ht' ?_
  unfold Ranks.N
  push_cast
  rfl

theorem nodeGap_of_val {C : FC} {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (h : Val C cD ch L) : D.NodeGap (h0v L.sc ch : ℝ) := by
  intro u τ j hj
  obtain ⟨b1, hb, -⟩ := h.hc.2.2.1
  rw [D.hcW_b u τ, (hb τ _).1, (hb τ _).1]
  push_cast
  exact le_of_eq (by ring)

theorem bigGap_of_val {C : FC} {cD ch : ℝ} {D : D7} {L : SizeData₂ D} (h : Val C cD ch L) (hch : 11311 ≤ ch)
    (hx : 300000 * 4 ^ 30 ≤ L.sc.x) : BigGap D := by
  refine (nodeGap_of_val h).mono ((rank_bound L.sc D.R h.ranks).trans ?_)
  have h1 := L.sc.one_lt_alt
  have h0 : 0 < L.sc.x := by linarith
  have e1 : (L.sc.x ^ (377 : ℝ)) ^ 30 = L.sc.x ^ (11310 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le]; norm_num
  have e2 : L.sc.x * L.sc.x ^ (11310 : ℝ) ≤ L.sc.x ^ ch := by
    rw [mul_comm, ← Real.rpow_add_one h0.ne']
    exact Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
  have e3 : 0 ≤ L.sc.x ^ (11310 : ℝ) := Real.rpow_nonneg h0.le _
  have e4 := mul_le_mul_of_nonneg_right hx e3
  have e5 := Nat.le_ceil (L.sc.x ^ ch)
  have e6 : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℝ) := Nat.cast_nonneg _
  rw [mul_pow, e1, ← mul_assoc]
  unfold h0v
  push_cast
  linarith

theorem rowE_bigGap : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D _ _ _ => GlobalTheory.Core.Rk.BigGap D) := by
  intro hL p
  refine ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ =>
    ⟨11311, fun ch hch _ => ⟨300000 * 4 ^ 30, fun K hK hx β _ _ _ _ => ?_⟩⟩⟩⟩⟩
  show BigGap β.X.toD7
  refine bigGap_of_val β.val ?_ ?_
  · rw [hK.2.2.1]; exact hch
  · rw [β.sc]; exact hx

end GlobalTheory.Core.Rk.GapAt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterMatchesWitness
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem twistedAdelicData_characters_eq_frame (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : G.Inst (w.st Z).toD7 L)
    (Gl : G.LatInst (w.st Z).toD7) (Kc : G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC)
    (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : Bl.RowsT K w Z Wt ex.p0) (a : R3.TwArgs ex t) (j : Fin B.R.m) :
    Formalism.IndefR.Links.ChrEq (D := (w.st Z).toD7) (a.x.R.mu0 ((j : ℕ) + 1)) (w.I.C.mu0 j) := by
  have h1 : a.x.R.C = Fr.at (w.st Z) f := eq_of_heq (R3.twArgs_lev K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t a).1
  have h2 := a.x.pins.char.base.lev.mu0 j
  have h3 : a.x.R.C.mu0 j = w.I.C.mu0 j :=
    (congrArg (fun C => C.mu0 j) h1).trans (congrArg (fun g : Fr B.toPre => g.mu0 j) w.C_eq).symm
  exact h3 ▸ h2

theorem level_character_matches_witness : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → ∀ j : Fin q.B.R.m, Formalism.IndefR.Links.ChrEq ((pk (packB b)).mu0 ((j : ℕ) + 1)) (q.w.I.C.mu0 j) := by
  intro hL p K q c b hw j
  obtain ⟨x, a, ax, y, -⟩ := hw
  have hx : a.x = x := eq_of_heq ax
  have h0 := twistedAdelicData_characters_eq_frame _ _ _ _ q.w q.Z _ _ _ _ _ _ _ _ _ _ a j
  have e : b.B.Q.Rl.mu0 = x.R.mu0 := congrArg (fun k : Bl.RPk b.R b.S => k.B.Q.Rl.mu0) y.eq
  have e' : a.x.R.mu0 = x.R.mu0 := congrArg (fun z : R3.TwIn q.O.ex => z.R.mu0) hx
  have e2 : (pk (packB b)).mu0 = a.x.R.mu0 := e.trans e'.symm
  rw [e2]
  exact h0

end GlobalTheory.Fam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelMatchOfWitness
section
namespace GlobalTheory.Core.Mi

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem idE_levelMatch_of_bwit : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b →
      GlobalTheory.Core.Mi.IdE b.S.X ∧ ∀ u, Formalism.L2.SG.ColDict.LevelMatch b.S.X (b.S.tr u) b.S.Y.hK := by
  intro hL p K q c b hw
  obtain ⟨sP, sS, -, -, e⟩ := hw.s
  rw [e]
  exact ⟨sP.pin, sP.lev⟩

end GlobalTheory.Core.Mi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumFoldrLocalCombinationsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalDatum_foldr_local_combinations : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (P₀ Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (n : ℕ) (PPn : Fin n → Formalism.L2.DIV.Pl D.host.E), Function.Injective PPn → (∀ PP, PP ∈ Q ↔ ∃ i, PPn i = PP) → Disjoint P₀ Q → ∀ (c : Fin n → WO S T →₀ ℂ) (Ξl : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ), (∀ i, GlobalTheory.LocMod.IsLocFac D ψ S T (PPn i) (c i) (Ξl i)) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = intVec D S.rank → (ΛT : Set (Fin T.rank → D.host.E)) = intVec D T.rank → ∀ (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (f₀ f : WO S T → ℂ), IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → (∀ e₀, IsIdemSum e₀ P₀ → IsRatDatum ψ S T e₀ Ξ f₀ f) → ∀ e, IsIdemSum e (P₀ ∪ Q) → IsRatDatum ψ S T e (fun γ => Ξ γ * ∏ i, Ξl i γ) f₀ ((List.finRange n).foldr (fun i g => comb ψ S T (c i) g) f) := by
  first | exact @GlobalTheory.LocComb.ratDatum_foldr_comb | exact GlobalTheory.LocComb.ratDatum_foldr_comb | (intros; apply GlobalTheory.LocComb.ratDatum_foldr_comb <;> assumption)
end

