import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveIffGram
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0287
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0609
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0274
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0221
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNoetherianRingOL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinesAtOfLatticeAtLevels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0338
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0315
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfCrys
section
noncomputable section

namespace GlobalTheory.WachTensor

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts GlobalTheory.EtaleExact
open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation (LocQuotCrys LocTensorCrys LocDualCrys)

set_option synthInstance.maxHeartbeats 400000

variable {l : ℕ} [Fact l.Prime]

private theorem frobW_surjective_lemma : Function.Surjective (frobW l) := by
  have hC : IsAlgClosed (Cb l) := (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).1
  have hf : Function.Surjective (frobenius (Cb l) l) := by
    first
      | exact surjective_frobenius (Cb l) l
      | exact (bijective_frobenius (Cb l) l).2
      | exact fun y => ⟨(frobeniusEquiv (Cb l) l).symm y, by simp⟩
  intro y
  obtain ⟨x, hx⟩ := WittVector.map_surjective (p := l) _ hf y
  unfold frobW
  exact ⟨x, hx⟩

theorem φRW_surjective (LL : FinExt l) : Function.Surjective (φRW LL) := by
  have hg : Function.Surjective (frobW l).toLinearMap := frobW_surjective_lemma
  intro y
  obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective (↥(OL LL)) hg y
  refine ⟨x, ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [φRW]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem isFractionRing_OL (LL : FinExt l) : IsFractionRing ↥(OL LL) ↥LL.1 := by
  have : FiniteDimensional ℚ_[l] LL.1 := LL.2
  unfold OL
  exact integralClosure.isFractionRing_of_finite_extension ℚ_[l] _

theorem map_ne_top {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
    {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
    (E : EtSit P AI K s LL h W) (m : Ideal W.EE) (hm : m.IsMaximal) :
    m.map E.tie.ioE.toRingHom ≠ ⊤ := by
  have : Module.Finite ℤ_[l] ↥(OL LL) := GlobalTheory.EtaleExact.finite_OL LL
  have : IsNoetherianRing ↥(OL LL) := by
    first
      | infer_instance
      | exact isNoetherian_of_tower ℤ_[l] inferInstance
  refine GlobalTheory.EtaleExact.map_ne_top_of_tie E.tie (fun c => ?_) (fun x hx => ?_) m hm
  · rw [P.PD_p K]
    exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow P LL c
  · exact GlobalTheory.EtaleExact.sep_RW LL x (by simpa [P.PD_p K] using hx)

theorem descends {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
    {h : Good K s LL}
    {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
    (E : EtSit P AI K s LL h W) : Descends E.tie := by
  intro ι _ M w hg hw i
  exact GlobalTheory.T.mem_range_of_frobeniusEquation_cyclotomicFixed l P AI K s LL h W E ι M 0 w hg (fun i => by simpa using hw i) i

theorem unitSumTensorDual_of_crys (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (H : LocHW l P) (F : LocFon l P AI H) (hq : LocQuotCrys l P) (ht : LocTensorCrys l P)
    (hd : LocDualCrys l P) (hU : GlobalTheory.IndefiniteRowSideFullHecke.GammaStableInverse.WachUnique l P H)
    (hF : GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness.WachLettersFree l P H) : UnitSumTensorDual l P AI H F := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocQuotCrys GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocTensorCrys GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.LocDualCrys
    GlobalTheory.IndefiniteRowSideFullHecke.GammaStableInverse.WachUnique at *
  have : ∀ LL : FinExt l, IsFractionRing ↥(OL LL) ↥LL.1 := isFractionRing_OL
  refine ⟨GlobalTheory.WachUnit.unitPart l P AI H F, GlobalTheory.WachSum.sumPart l P H, fun K s LL h => ?_,
    fun K s LL h => ?_⟩
  · have := this LL
    exact tensorFor (F.E K s LL h).tie (fun m hm => map_ne_top (F.E K s LL h) m hm)
      (φRW_surjective LL) (descends (F.E K s LL h)) (hq K LL) (ht K LL) (hU K s LL h) (hF K s LL h)
  · have := this LL
    exact dualFor (F.E K s LL h).tie (fun m hm => map_ne_top (F.E K s LL h) m hm) (φRW_surjective LL)
      (descends (F.E K s LL h)) (hq K LL) (hd K LL) (hU K s LL h) (hF K s LL h)

theorem unitSumTensorDual (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (H : LocHW l P) (F : LocFon l P AI H) (hS : GlobalTheory.Per.IsStd P AI)
    (hU : GlobalTheory.IndefiniteRowSideFullHecke.GammaStableInverse.WachUnique l P H) (hF : GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness.WachLettersFree l P H) :
    UnitSumTensorDual l P AI H F := by
  obtain ⟨hq, ht, hd⟩ := GlobalTheory.T.crystalline_quotient_tensor_dual l P AI hS
  exact unitSumTensorDual_of_crys l P AI H F hq ht hd hU hF

end GlobalTheory.WachTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedGaloisHomsBoundedClassNumberOfArtinRecStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedGaloisHoms_bounded_classNumber_of_artinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity → ReciprocityTheory.ChartRestriction.T2.VhE := by
  first | exact @GlobalTheory.UnramifiedClassBound.vhE_of_globalArtinReciprocity | exact GlobalTheory.UnramifiedClassBound.vhE_of_globalArtinReciprocity | (intros; apply GlobalTheory.UnramifiedClassBound.vhE_of_globalArtinReciprocity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeComparisonDcris
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.CmpCris

theorem wachLattice_comparison_dcris (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) : P3 D HW F Cm := by
  intro l _ K s LL h T hT
  obtain ⟨h1, h2, -, h4⟩ := cmp_iso D HW F Cm l K s LL h T hT
  refine ⟨fun x hx => ?_, h2, fun x k hk => h4 x k hk⟩
  obtain ⟨y, rfl⟩ := (h1 x).1 hx
  exact ⟨y, y.2, rfl⟩

end GlobalTheory.NL.CmpCris
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionsStdBelowLevelStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLattice_expansions_std_below_level : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ (s - 1)) = 1 → Std (Di (HW l) h T i) (Lat C h T i ζ) := by
  first | exact @GlobalTheory.NL.LatLow.lat_low | exact GlobalTheory.NL.LatLow.lat_low | (intros; apply GlobalTheory.NL.LatLow.lat_low <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeUsedPropertiesOfAdmitted
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

noncomputable section

namespace GlobalTheory.WachQN

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem invBasis_of_basisModule [Nontrivial O] (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) {π' : LetA O n}
    (h : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π') :
    ∃ b : Fin (Module.finrank O ↥T.L.T) → W.DD T, (∀ j, b j ∈ W.NΔ T) ∧ LinearIndependent (LetA O n) b ∧
      W.N T = Submodule.span (LetA O n) (Set.range b) := by
  obtain ⟨⟨r, b, hbN, huniq, -⟩, -⟩ := h
  obtain ⟨a0, -, ha0⟩ := huniq 0 (W.N T).zero_mem
  have hli : LinearIndependent (LetA O n) b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    exact congrFun ((ha0 g hg.symm).trans (ha0 0 (by simp)).symm) j
  have hsp : W.N T = Submodule.span (LetA O n) (Set.range b) := by
    refine le_antisymm (fun x hx => ?_) (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact (hbN j).1))
    obtain ⟨a, ha, -⟩ := huniq x hx
    rw [ha]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hr : r = Module.finrank O ↥T.L.T := by
    let bN := (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hsp.symm)
    have hbc := W.N_base T hT
    let bD := (Algebra.TensorProduct.basis W.EE bN).map hbc.equiv
    haveI : Nontrivial W.EE := W.EE_inj.nontrivial
    rw [← (W.DD_free T).2, Module.finrank_eq_card_basis bD, Fintype.card_fin]
  subst hr
  exact ⟨b, hbN, hli, hsp⟩

end Generic

theorem invBasis_of_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F →
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), GlobalTheory.WachUse.InvBasis ((HW l).W K 1 LL hA.2.2) := by
  intro D HW F h9 l _ K LL hA T hT
  have hbij : Function.Bijective (algebraMap ↥(K0 K) ↥K.1) :=
    ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, x.2, hA.1 x.2⟩, rfl⟩⟩
  have hfr : Module.finrank ↥(K0 K) ↥K.1 = 1 :=
    (LinearEquiv.ofBijective (Algebra.linearMap ↥(K0 K) ↥K.1) hbij).finrank_eq.symm.trans (Module.finrank_self _)
  exact invBasis_of_basisModule _ T hT ((h9 l K 1 LL hA.2.2 T hT ((HW l).W_s K 1 LL hA.2.2)
    (by rw [(D.loc l).PD_p]; exact hA.2.1)).2.2 hfr).2

theorem heights_of_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.DeltaInvariantLattices.P5 D HW F →
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), GlobalTheory.WachUse.Heights ((HW l).W K 1 LL hA.2.2) := by
  intro D HW F h5 l _ K LL hA T U M hh hU hb i
  haveI := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ).1
  have hJ := GlobalTheory.WachUse.HeightsProof.jumpsOverLetters_of_crysWith _ T U M hh hU hb
  have hp := h5 l K 1 LL hA.2.2 T M hh hU.1
    (fun τ j hτ => hJ j τ (fun c => by simpa using congrArg (fun f => f c) hτ))
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · rw [← GlobalTheory.WachUse.HeightsProof.φD_letE]
    exact hp.1 i _ ⟨x, hx, rfl⟩
  · exact Submodule.span_mono (Set.image_mono (GlobalTheory.WachUse.HeightsProof.Nl_le _ T (i - 1)))
      (hp.2.1 i _ ⟨y, hy, rfl⟩)

theorem saturated_caseA (D : D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) :
    GlobalTheory.WachUse.Saturated ((HW l).W K 1 LL hA.2.2) := by
  intro T' T f hT hb x hx
  have hT' : IsCrys ((D.loc l).PD K) T'.ρ :=
    GlobalTheory.HTW.Rec.isCrys_of_equiv ((D.loc l).PD K) (LinearEquiv.ofBijective f.f hb) f.equiv hT
  exact ((GlobalTheory.NL.Isog.isog_loc (HW l) K 1 LL hA.2.2 T' T f hT' hT hb).2.2 x).1 hx

theorem qN_of_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    tableLineDegreeTwo.admitted D HW F Cm → ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL),
      GlobalTheory.WachUse.QN ((HW l).W K 1 LL hA.2.2) := by
  intro D HW F Cm h l _ K LL hA
  have hI := invBasis_of_admitted D HW F h.2.2.2.2.2.2.2.2.1 l K LL hA
  have hS := GlobalTheory.SenOperator.senOp_of_record D HW F Cm l K LL hA
  exact ⟨hI, heights_of_admitted D HW F h.2.2.2.2.1 l K LL hA,
    GlobalTheory.WachRankOne.rankOne_of_senOp (D.locA l) (HW l) (F l) (Cm l) K LL hA hI hS,
    saturated_caseA D HW l K LL hA,
    GlobalTheory.WachUse.additive_of_caseA (D.locA l) (HW l) (F l) (Cm l) K LL hA, hS⟩

end GlobalTheory.WachQN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightExceedsCenterBound
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

open GlobalTheory.SignedHC

theorem e_add_v_two_pos {R : Ranks} (P : HCParam R) (s ga : ℕ) (c : ℕ → ℤ) (j : Fin R.m) :
    0 < P.e j + ((GridData.ofHCParam P s ga c).v 2 : ℚ) := by
  obtain ⟨hv, hb, -⟩ := GridData.ofHCParam_spec P s ga c
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have h1 : (GridData.ofHCParam P s ga c).v (R.k - 2 + 2) < (GridData.ofHCParam P s ga c).v 2 :=
    (GridData.ofHCParam P s ga c).v_anti 2 _ le_rfl (by omega) (show R.k - 2 + 2 ≤ R.k by omega)
  have h2 : (GridData.ofHCParam P s ga c).b (0 + 1) ≤ (GridData.ofHCParam P s ga c).b (j.1 + 1) := by
    rcases Nat.eq_zero_or_pos j.1 with h | h
    · rw [h]
    · exact ((GridData.ofHCParam P s ga c).b_mono _ _ le_rfl (by omega) (show j.1 + 1 ≤ R.m from j.2)).le
  have h1' : P.v ⟨R.k - 2, by omega⟩ < ((GridData.ofHCParam P s ga c).v 2 : ℚ) := by
    rw [hv]; exact_mod_cast h1
  have h2' : P.b ⟨0, by omega⟩ ≤ P.b j := by
    rw [hb, hb]; exact_mod_cast h2
  have h3 := P.v_gt_u ⟨R.k - 2, by omega⟩
  have h4 := P.u_last_gt (by omega) (by omega)
  have h5 : P.u ⟨R.k - 2 + 1, by omega⟩ = P.u ⟨R.k - 1, by omega⟩ := by
    congr 2; omega
  have h6 := P.gap_be j
  have h7 : (0 : ℚ) ≤ R.t := by positivity
  simp only at h3
  linarith

theorem nFun_eq_bigN (D : D7) : BlochKatoReduction.Gen.NFun D.R = GlobalTheory.Grid.bigN D := by
  have hk := D.R.m_add_three_le_k
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have h : Odd (D.R.r + 6) := by
    rw [Nat.odd_iff]; unfold Ranks.r; omega
  simp only [BlochKatoReduction.Gen.NFun, BlochKatoReduction.Gen.sFun, if_pos h, GlobalTheory.Grid.bigN, GlobalTheory.Grid.sLen]

theorem nFun_add_one_lt_eExp_add_cen (D : D7) (j a : Fin D.R.m) (g : D.R.Psi) :
    (BlochKatoReduction.Gen.NFun D.R : ℚ) + 1 < eExp D j g + (GlobalTheory.Grid.cen D (D.eTau.symm g) (a.1 + 1) : ℚ) := by
  have h1 := e_add_v_two_pos (D.hc (D.eTau.symm g)) (GlobalTheory.Grid.sLen D) (GlobalTheory.Grid.gap D) 0 j
  have h2 := Int.lt_floor_add_one ((GlobalTheory.Grid.gridOf D (GlobalTheory.Grid.gap D) 0 (D.eTau.symm g)).mid (a.1 + 1))
  have h3 := (GlobalTheory.Grid.gridOf D (GlobalTheory.Grid.gap D) 0 (D.eTau.symm g)).mid_eq (i := a.1 + 1) (by omega)
  have h4 : (GlobalTheory.Grid.gridOf D (GlobalTheory.Grid.gap D) 0 (D.eTau.symm g)).a (a.1 + 1) =
      ((GlobalTheory.Grid.gridOf D (GlobalTheory.Grid.gap D) 0 (D.eTau.symm g)).v 2 : ℚ) + 1 / 2 +
        ((D.R.m : ℚ) + 1 - ((a.1 + 1 : ℕ) : ℚ)) * (GlobalTheory.Grid.gap D : ℚ) := rfl
  have h5 : ((GlobalTheory.Grid.gridOf D (GlobalTheory.Grid.gap D) 0 (D.eTau.symm g)).ga : ℚ) = GlobalTheory.Grid.gap D := rfl
  have h6 := (GlobalTheory.Grid.isLeast_gap D).1.2.1
  have h7 : GlobalTheory.Grid.bigN D ≤ GlobalTheory.Grid.bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  have h8 : ((GlobalTheory.Grid.bigN D + 2 : ℕ) : ℚ) ≤ GlobalTheory.Grid.gap D := by exact_mod_cast (by omega)
  have h9 : ((a.1 + 1 : ℕ) : ℚ) ≤ D.R.m := by exact_mod_cast a.2
  have h10 : (0 : ℚ) ≤ GlobalTheory.Grid.gap D := by positivity
  have h11 : (GlobalTheory.Grid.gap D : ℚ) ≤ ((D.R.m : ℚ) + 1 - ((a.1 + 1 : ℕ) : ℚ)) * (GlobalTheory.Grid.gap D : ℚ) := by nlinarith
  rw [nFun_eq_bigN]
  unfold eExp GlobalTheory.Grid.cen
  push_cast at h8
  linarith

end GlobalTheory.LamTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiValueGaloisSubMemFilZeroStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xi_value_galois_sub_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∃ m₀ : ℕ, ∀ w ∈ D.Mext (invL l (A O K)), (∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m₀ * h) → ∀ (hw : D.xiExt w ∈ D.MMl) (g : Gl l), sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩)) - R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩) ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.XiFil.xi_value_gal_sub_mem_filZero | exact GlobalTheory.BKGal.XiFil.xi_value_gal_sub_mem_filZero | (intros; apply GlobalTheory.BKGal.XiFil.xi_value_gal_sub_mem_filZero <;> assumption)
end

