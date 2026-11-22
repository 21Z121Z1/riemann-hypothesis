import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0046
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0014
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSDivMem
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0009
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0013
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0033
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0044
import Formalism.SharpRestriction.LevelLetterCocycles.RingHypothesesOfCrystalline
import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0019
import Formalism.SharpRestriction.LevelLetterCocycles.JumpsInLetterOfEvenIndex
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0035
import Formalism.SharpRestriction.LevelLetterCocycles.RingClausesAtUniformizer
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowerCongruenceOfAdmitted
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0034
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0042
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0025
import Formalism.SharpRestriction.LevelLetterCocycles.LocalClauseOfFrobeniusHyps
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0014
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool
import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.MemOfSecEq
section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

variable {W}

theorem inFNc_add (T : LocLat G Qp LL O) (a : ZMod n) {x y : W.DD T} (hx : InFNc W T a 1 x)
    (hy : InFNc W T a 1 y) : InFNc W T a 1 (x + y) := by
  obtain ⟨x', hx', hxl, rfl⟩ := hx
  obtain ⟨y', hy', hyl, rfl⟩ := hy
  exact ⟨x' + y', (W.NΔ T).add_mem hx' hy', by rw [smul_add, hxl, hyl], by simp⟩

theorem inFNc_neg (T : LocLat G Qp LL O) (a : ZMod n) {x : W.DD T} (hx : InFNc W T a 1 x) :
    InFNc W T a 1 (-x) := by
  obtain ⟨x', hx', hxl, rfl⟩ := hx
  exact ⟨-x', (W.NΔ T).neg_mem hx', by rw [smul_neg, hxl], by simp⟩

theorem inFNc_zero (T : LocLat G Qp LL O) (a : ZMod n) : InFNc W T a 1 (0 : W.DD T) :=
  ⟨0, (W.NΔ T).zero_mem, smul_zero _, by simp⟩

theorem mem_of_sec_eq (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) (x z : W.DD T) (k k' t : ℕ) (f : Fin d → W.EE)
    (hxP : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • x))
    (hzP : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • z))
    (hzN : InFNc W T (c' + (e : ZMod n)) 1 z)
    (hx : RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol (lA W ^ k • x) f)
    (hz : RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol (lA W ^ k' • z)
      (fun m => lE W t * f m)) :
    InFNc W T (c' + (e : ZMod n)) 1 x := by
  set Λ := abelian₂ W A (c' + (e : ZMod n)) e with hΛdef
  have r1 := repVV_lA T c' e _ _ b sol x f (k + k' + t) k hx
  have r2 := repVV_lA T c' e _ _ b sol z _ (k' + k) k' hz
  have hsec : (fun m => lE W (k' + k) * (lE W t * f m)) = (fun m => lE W (k + k' + t) * f m) := by
    funext m; rw [lE_mul]; congr 2; ring
  rw [hsec] at r2
  have r3 := repVV_sub W C.hinj T c' e _ _ b sol _ _ _ _ r1 r2
  rw [sub_self] at r3
  have hΛu := lam_unit W C.hR A (c' + (e : ZMod n)) e
  have hwP : InFP W T c' e 1 (Λ • (lA W ^ (k + (k + k' + t)) • x - lA W ^ (k' + (k' + k)) • z)) := by
    rw [smul_sub, smul_comm Λ, smul_comm Λ (lA W ^ (k' + (k' + k)))]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_sub W T c' e _ (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ (lA_mem W _) hxP)
      (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ (lA_mem W _) hzP)
  have hw := piLam_of_sec W C.hR C.hsatP C.hCA T hT.1 A c' e _ b sol hb.1 _ hwP _ r3 (fun m => inFr_zero W)
  have hwN := inN_of_piLam W C.hR.1 T A c' e
    (Formalism.MainNotions.UnusedSlot80.ArcC.arc_up W C.hs C.hR C.h5 A hA c' hc' e T hT) _ hw
  have hzN' := inFNc_smul C.hR.1 T _ (lA_mem W (k' + (k' + k))) hzN
  have hxN := inFNc_add T _ hwN hzN'
  rw [sub_add_cancel] at hxN
  exact Formalism.MainNotions.UnusedSlot80.ArcC.arc_sat W C.hCA C.hsat C.hR T hT.1 A c' e
    (Formalism.MainNotions.UnusedSlot80.ArcC.arc_up W C.hs C.hR C.h5 A hA c' hc' e T hT) x hxP ⟨_, hxN⟩

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.UniformizerClauseOfAdmitted
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.bigCellDetWeightedEnergyIntegral

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
variable {CR CA CB CK : ℝ}

theorem caseA_loc' {l : ℕ} [Fact l.Prime] {K LL : Loc.FinExt l} (hg : Loc.Good K 1 LL)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg)) : Loc.CaseA K LL := by
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine ⟨fun x hx => ?_, by rw [← hpl]; exact hCA.2.2, hg⟩
  obtain ⟨y, hy⟩ := hCA.1.2 ⟨x, hx⟩
  have h2 := y.2.2
  have : ((y : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hy
  rw [this] at h2
  exact h2

theorem laurent_clause_of_admitted' (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.1

theorem uniformizer_clause_of_admitted (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.2.2.2.2.2.1

theorem level_tools_of_admitted' (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.WachCoordinates.adm7 D HW F Cm :=
  Formalism.MainNotions.UnusedSlot80.tools_unramified_statement D HW F Cm ⟨fun l _ K s LL h => (hA.1 l K s LL h).2.2.1, laurent_clause_of_admitted' D HW F Cm hA,
    uniformizer_clause_of_admitted D HW F Cm hA⟩

set_option maxHeartbeats 0 in

theorem dual_lemma_of_admitted (hA : admitted D HW F Cm CR CA CB CK) (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l)
    (hg : Loc.Good K 1 LL) [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))] : LemmaDN ((HW l).W K 1 LL hg) := by
  intro d T₁ T₂ F' b S η m hset
  have hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg) := hset.1
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := caseA_loc' D HW hg hCA
  have h5l : 5 ≤ l := by have := hset.2.1; rw [hpl] at this; omega
  set W := (HW l).W K 1 LL hg with hW
  have h1 := hA.1 l K 1 LL hg
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W := h1.2.2.2.2.2.2.2.2.1
  obtain ⟨hE, hC, hQ⟩ := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have hs : W.s = 1 := hCA.2.1
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := Formalism.MainNotions.RamifiedCoefficientChains.S9.DLev.complete_max LL
  have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W :=
    (((h9 _ (Formalism.MainNotions.LiftingTheory.gen_one_crys W)) hs hCA.2.2).2.2 (Formalism.MainNotions.UnusedSlot80.finrank_K0_eq_one_of_le_Kur hCAl.1)).1
  have C := ((Cm l).C K 1 LL hg).tie
  have hG := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie W hs C
  have hLev : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W := (level_tools_of_admitted' D HW F Cm hA l K LL hCAl h5l).2
  have hRu : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W := Formalism.MainNotions.N.Pv.LocalLengthBound.expRules_of W hLev hG.1 hG.2
  have hRing : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing W := Formalism.MainNotions.N.Pv.LocalLengthBound.expRing_of W hring
  have hpt := Formalism.MainNotions.UnusedSlot80.points_exist_of_ring_condition D HW F (uniformizer_clause_of_admitted D HW F Cm hA)
  have hL := Formalism.MainNotions.UnusedSlot80.levCoeff_of_pt D HW F Cm (laurent_clause_of_admitted' D HW F Cm hA) hpt
  have hBall : ∀ (l' : ℕ) [Fact l'.Prime] (K' LL' : FinExt l') (hg' : Good K' 1 LL')
      [NeZero (Module.finrank ℚ_[l'] ↥(K0 K'))], Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool ((HW l').W K' 1 LL' hg') := by
    intro l' _ K' LL' hg' _
    haveI : IsFractionRing ↥(OL LL') ↥LL'.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL'
    exact Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of _ (hA.1 l' K' 1 LL' hg').2.2.2.2.2.2.2.2.1
  have hEC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit W :=
    Formalism.MainNotions.N.Pv.LocalLengthBound.expCrit_D' D HW F Cm CR CA CB CK hA hL hBall l K LL hCAl h5l
  have hGM := Formalism.MainNotions.RamifiedCoefficientChains.S9.GM.gMem_of W hE hC hQ h1.2.2.2.2.1 h9 hRu hEC
  have hBas : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool W := Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of W h9
  have hΔ : IsUnit ((W.DelF.card : ℕ) : ↥(OL LL)) := by
    have hcard : W.DelF.card = l - 1 :=
      Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F (uniformizer_clause_of_admitted D HW F Cm hA) l K LL hCAl
    by_contra hnu
    have hm : ((W.DelF.card : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := hnu
    have hlm := Formalism.BasicNotions.Examples₂.LB.l_mem_max LL
    have e : ((l : ℕ) : ↥(OL LL)) - ((W.DelF.card : ℕ) : ↥(OL LL)) = 1 := by
      rw [hcard, Nat.cast_sub (by omega)]; simp
    have h3 := Submodule.sub_mem _ hlm hm
    rw [e] at h3
    exact (IsLocalRing.maximalIdeal.isMaximal ↥(OL LL)).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hTH : Formalism.MainNotions.CrystallineLiftingInputs.THor W := Formalism.MainNotions.CrystallineLiftingInputs.Tools.frobenius_power_congruence_local D HW F Cm hA.1 l K LL hg
  have hZ := Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.zTool_of W h9 (((Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData.truncation_clause_of_lattice_hypotheses D HW F Cm (uniformizer_clause_of_admitted D HW F Cm hA) hA.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.1).2 l K LL hg).2) hTH hBas hRu
    hRing hΔ
  have hAd : Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.AdaptBas W :=
    Formalism.MainNotions.RamifiedCoefficientChains.S9.AdM.adaptBas_of W hE hC hQ h1.2.2.1 h1.2.2.2.2.1 h9 (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL)
  have hpm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [hpl]; exact Formalism.BasicNotions.Examples₂.LB.l_mem_max LL
  have hPt : Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1),
      IsPrimitiveRoot ζ ((D.loc l).PD K).p →
      ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Formalism.MainNotions.LiftingTheory.Over W τ i ∧ Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hg i ζ τ := by
    intro _ c ζ hζ
    obtain ⟨τ, hτ⟩ := hpt l K LL hCAl h5l c ζ (by rwa [hpl] at hζ)
    refine ⟨τ, ?_, hτ⟩
    obtain ⟨τs, ⟨hemb, -⟩, hres⟩ := hτ
    apply AlgHom.ext
    intro x
    have hy : (x : Om l) ∈ Ks K 1 := (le_sup_left : K0 K ≤ Ks K 1) x.2
    show τ (algebraMap ↥(K0 K) ↥K.1 x) = _
    rw [hres (algebraMap ↥(K0 K) ↥K.1 x) ⟨x, hy⟩ rfl]
    exact hemb x ⟨x, hy⟩ rfl
  have hDT : Formalism.MainNotions.RamifiedCoefficientChains.Sh.DetTool W :=
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.detTool_of W h9 _ h1.2.2.2.1 hPt hQ hpm hset.2.2.2.2.1
  have hDet := Formalism.MainNotions.RamifiedCoefficientChains.S9.DetA.detAlg_of W hE hC hQ h1.2.2.2.2.1 h9 hBas (fun _ => hDT)
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord.gCoord_holds W)
  exact Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.lemmaDN_of_S1E W hZ hAd hGM hDet d T₁ T₂ F' b S η m hset

end Formalism.MainNotions.RamifiedCoefficientChains.S9.bigCellDetWeightedEnergyIntegral
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.UniformizerClauseOfAdmittedAlt
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.LocalLemmasFromLiterature

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
variable {CR CA CB CK : ℝ}

theorem caseA_loc' {l : ℕ} [Fact l.Prime] {K LL : Loc.FinExt l} (hg : Loc.Good K 1 LL)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg)) : Loc.CaseA K LL := by
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine ⟨fun x hx => ?_, by rw [← hpl]; exact hCA.2.2, hg⟩
  obtain ⟨y, hy⟩ := hCA.1.2 ⟨x, hx⟩
  have h2 := y.2.2
  have : ((y : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hy
  rw [this] at h2
  exact h2

theorem laurent_clause_of_admitted' (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.1

theorem uniformizer_clause_of_admitted (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.2.2.2.2.2.1

theorem level_tools_of_admitted' (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.WachCoordinates.adm7 D HW F Cm :=
  Formalism.MainNotions.UnusedSlot80.tools_unramified_statement D HW F Cm ⟨fun l _ K s LL h => (hA.1 l K s LL h).2.2.1, laurent_clause_of_admitted' D HW F Cm hA,
    uniformizer_clause_of_admitted D HW F Cm hA⟩

set_option maxHeartbeats 0 in

theorem local_lemmas_of_literature (hA : admitted D HW F Cm CR CA CB CK) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F)
    (hHerr : Formalism.MainNotions.ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F) (a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F)
    (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F) : cocyclesToWachVectorsBoundAtGoodExtensions D HW F := by
  intro l _ K LL hg _
  intro d T₁ T₂ F' b S η m hset
  have hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg) := hset.1
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := caseA_loc' D HW hg hCA
  have h5l : 5 ≤ l := by have := hset.2.1; rw [hpl] at this; omega
  set W := (HW l).W K 1 LL hg with hW
  have h1 := hA.1 l K 1 LL hg
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W := h1.2.2.2.2.2.2.2.2.1
  obtain ⟨hE, hC, hQ⟩ := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have hs : W.s = 1 := hCA.2.1
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W :=
    (((h9 _ (Formalism.MainNotions.LiftingTheory.gen_one_crys W)) hs hCA.2.2).2.2 (Formalism.MainNotions.UnusedSlot80.finrank_K0_eq_one_of_le_Kur hCAl.1)).1
  have C := ((Cm l).C K 1 LL hg).tie
  have hG := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie W hs C
  have hLev : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W := (level_tools_of_admitted' D HW F Cm hA l K LL hCAl h5l).2
  have hRu : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W := Formalism.MainNotions.N.Pv.LocalLengthBound.expRules_of W hLev hG.1 hG.2
  have hRing : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing W := Formalism.MainNotions.N.Pv.LocalLengthBound.expRing_of W hring
  have hpt := Formalism.MainNotions.UnusedSlot80.points_exist_of_ring_condition D HW F (uniformizer_clause_of_admitted D HW F Cm hA)
  have hL := Formalism.MainNotions.UnusedSlot80.levCoeff_of_pt D HW F Cm (laurent_clause_of_admitted' D HW F Cm hA) hpt
  have hBas : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool W := Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of W h9
  have hK : Formalism.MainNotions.RamifiedCoefficientChains.Sh.LemK W := Formalism.MainNotions.N.Pv.LocalLengthBound.lemK_D D HW F Cm CR CA CB CK hA hL l K LL hCAl h5l
  have hFD : Formalism.MainNotions.RamifiedCoefficientChains.Sh.FilDim W := Formalism.MainNotions.N.Pv.LocalLengthBound.filDim_of W hQ
  have hΔ : IsUnit ((W.DelF.card : ℕ) : ↥(OL LL)) := by
    have hcard : W.DelF.card = l - 1 :=
      Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F (uniformizer_clause_of_admitted D HW F Cm hA) l K LL hCAl
    by_contra hnu
    have hm : ((W.DelF.card : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := hnu
    have hlm := Formalism.BasicNotions.Examples₂.LB.l_mem_max LL
    have e : ((l : ℕ) : ↥(OL LL)) - ((W.DelF.card : ℕ) : ↥(OL LL)) = 1 := by
      rw [hcard, Nat.cast_sub (by omega)]; simp
    have h3 := Submodule.sub_mem _ hlm hm
    rw [e] at h3
    exact (IsLocalRing.maximalIdeal.isMaximal ↥(OL LL)).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hP9π : Formalism.MainNotions.LiftingTheory.P9π₀ W := (Formalism.MainNotions.LiftingTheory.uniformizer_ring_and_module_clauses W h9 hCA _ (Formalism.MainNotions.LiftingTheory.gen_one_crys W)).1
  have hRN : Formalism.MainNotions.LiftingTheory.CaseA W → Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W := fun hCA' =>
    Formalism.MainNotions.CrystallineLiftingInputs.RToolNum_holds (D.loc l) (HW l) K LL hg hCA'
  have hDss : Formalism.MainNotions.RamifiedCoefficientChains.DssLet W := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 l K 1 LL hg
  have hS1 : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step1 W :=
    Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.first_lift_of_uniformizer_clause W (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL) hP9π hRN h9 hDss hRu hRing hK hFD
      hBas hE hC hQ
  have hTZ' : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.TTool2Z W :=
    Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData.tTool2Z_DU D HW F (uniformizer_clause_of_admitted D HW F Cm hA) hA.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.1 l K LL hg
  have hFT : Formalism.MainNotions.CrystallineLiftingInputs.FTool W := Formalism.MainNotions.CrystallineLiftingInputs.Tools.local_clause_of_admitted_statements D HW F Cm hA l K LL hg
  have h2a : ∀ T : LocLat _ ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys _ T.ρ → Formalism.MainNotions.DeltaInvariantLattices.p2aK W T :=
    fun T hT => ((hA.2.2.1 l K 1 LL hg).1 T hT).2
  have hS2 : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2 W :=
    Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.second_lift_of_hypotheses W hTZ' hFT hBas hK hFD hRing hRu h2a h1.2.2.2.2.1 h9 hE hC hQ
  have hQT : Formalism.MainNotions.CrystallineLiftingInputs.QTool W := Formalism.MainNotions.CrystallineLiftingInputs.Tools.level_clause_of_admitted_statements D HW F Cm hA h23 l K LL hg
  have hdex : W.DelF.card = ((D.loc l).PD K).p - 1 → ∃ dd : ↥(OL LL), dd * (W.DelF.card : ↥(OL LL)) = 1 :=
    fun _ => hΔ.exists_left_inv
  have hExt : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExtTool W :=
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.extData_extTool W (hHerr l K 1 LL hg).2.2.2 (Formalism.MainNotions.LiftingTheory.liftb_HExt_holds D HW F l K 1 LL hg)
      (Formalism.MainNotions.LiftingTheory.liftb_HOne_holds D HW F l K 1 LL hg) (Formalism.MainNotions.LiftingTheory.lker_HKer_D D HW F a22 l K 1 LL hg)
      (h23 l K LL) ((hFont l K LL hCAl).2.1) hdex h1.2.2.2.2.1 h1.2.2.2.2.2.1 h9 hQT
  exact Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.cocyclesToWachVectorsBound_of_extTool W hExt hS1 hS2 d T₁ T₂ F' b S η m hset

end Formalism.MainNotions.RamifiedCoefficientChains.S9.LocalLemmasFromLiterature
end
end

