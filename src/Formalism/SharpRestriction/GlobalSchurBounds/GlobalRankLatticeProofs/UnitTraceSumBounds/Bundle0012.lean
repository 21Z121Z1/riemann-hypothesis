import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0011
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0002
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0003
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0008
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CountHypothesesIffText
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0008
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0006
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0019
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0007
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0003

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EmbeddingPermutesLettersHolds
section
namespace Formalism.MainNotions.Ext

theorem permEmb_holds : PermEmb := embedding_permutation

theorem embedding_permutes_letters_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.StandardLatticesGL3.EmbeddingPermutesTypes D := embedding_permutes_letters permEmb_holds D

theorem charExt_holds : CharExt := PI.character_extension_exists

theorem traceSum_holds : TraceSum := sumEqTrace_holds

theorem trace_sum_over_letters_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.StandardLatticesGL3.TraceMapNormalisation D := trace_sum_over_letters traceSum_holds D

theorem induced_type_from_K_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.StandardLatticesGL3.admG1 D := ⟨Formalism.MainNotions.GL3Theta.induced_cm_type D, trace_sum_over_letters_holds D⟩

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FirstKernelRemainderOfLevelRestrictionOfLinPtW
section
namespace Formalism.MainNotions.Ext.CutA

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.GL3r7 Formalism.MainNotions.Ext

theorem firstKernelRemainder_of_levelRestriction_of_linPtW (HK : LevelRestrictionOfGroupLaw) (HL : LinPtW) (D : D7) : StatementFirstKernelRemainder D := by
  intro hph ha he hSD hPD p _ cc δ g hA h5 hI hW κ ι ι' _ _ _ b b' b'' hb hb' hb'' hd ho1 ho2
  have hOk : g.Ok := hA.2.2.2.2
  have hP : CoefWf g.ph := hph p cc δ g hA h5 hI hW
  have hF := (ha p cc δ g hA).2 hW
  have hmem : ∀ (e : (ι ⊕ ι) ⊕ ι') (k : κ), Sum.elim (Sum.elim b b') b'' e k ∈ OKp D g.lam := by
    rintro ((e | e) | e) k
    · exact hb e k
    · exact hb' e k
    · exact hb'' e k
  refine ⟨?_, ?_⟩
  · exact coefWf_sum _ _ fun k _ => coefWf_phAt g hP
      (HL p g hOk hF _ _ (fun e => he p cc δ g hA h5 hI hW _ (hmem e k)) _ _ fun e => ptW_X e)
  · exact HK p g (OKp D g.lam) hOk
      (fun κ ι ι' _ _ _ a a' h1 h2 => (hSD p cc δ g hA h5 hI hW κ ι ι' a a' h1 h2).2.1)
      (fun κ ι _ _ c c' h1 h2 h3 => (hPD p cc δ g hA h5 hI hW κ ι c c' h1 h2 h3).2)
      κ ι ι' b b' b'' hb hb' hb'' hd ho1 ho2

end Formalism.MainNotions.Ext.CutA
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LwRankTies
section
noncomputable section

namespace Formalism.MainNotions.Ext.Lw

open Formalism.BasicNotions Formalism.MainNotions

theorem splitsF_g_all (D : D7) : ∀ j, StandardLattice.SplitsF D (D.host.g j) := fun j => J.splitsF_g D j

theorem splitsF_T_all (D : D7) (u : D.what₂.Word) : StandardLattice.SplitsF D (D.mem u).A.T := J.level_prime_splits_totally_real D u

theorem rank_conditions_iff_lowest_space {eps : ℝ} (Fm : FamP eps) :
    RankTiesF Fm ↔ ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), StandardLattice.Mu0Tie (Fm.D x i) u := by
  unfold RankTiesF
  constructor
  · rintro ⟨x0, hx0⟩
    exact ⟨x0, fun x hx i u => ((hx0 x hx i).2 u).2⟩
  · rintro ⟨x0, hx0⟩
    exact ⟨x0, fun x hx i => ⟨splitsF_g_all (Fm.D x i), fun u => ⟨splitsF_T_all (Fm.D x i) u, hx0 x hx i u⟩⟩⟩

theorem rank_conditions_of_lowest_space {eps : ℝ} (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), StandardLattice.Mu0Tie (Fm.D x i) u) : RankTiesF Fm :=
  (rank_conditions_iff_lowest_space Fm).2 h

theorem rankTiesF_of_col {eps : ℝ} (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      StandardLattice.adm17 (Fm.D x i) (Fm.ex x hx i).lev ∧ StandardLattice.Conclusion4p (Fm.D x i) (Fm.ex x hx i).lev ∧ StandardLattice.AdmittedWeylDimension (Fm.D x i) ∧
        ∀ u : (Fm.D x i).what₂.Word, ∃ X : StandardLattice.ColRep (Fm.D x i) (Fm.ex x hx i).lev u,
          StandardLattice.BaseWeightColumnCondition (Fm.D x i) (Fm.ex x hx i).lev u X) :
    RankTiesF Fm := by
  obtain ⟨x0, h⟩ := h
  refine rank_conditions_of_lowest_space Fm ⟨max x0 (max 3 (Fm.x1 + 1)), fun x hx i u => ?_⟩
  have e0 : x0 ≤ x := (le_max_left _ _).trans hx
  have e3 : 3 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have e1 : Fm.x1 < x := by
    have := ((le_max_right 3 (Fm.x1 + 1)).trans (le_max_right x0 _)).trans hx
    linarith
  obtain ⟨h17, hp, hW, hX⟩ := h x e1 e0 i
  obtain ⟨X, hX⟩ := hX u
  exact StandardLattice.mu0Tie_of_col (Fm.D x i) (Fm.ex x e1 i).lev h17 hp (GlobalTheoryTheory.JDB.gBig_fam Fm x e3 e1 i) hW u X hX

end Formalism.MainNotions.Ext.Lw

end
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.SplitZeroOf
section
namespace Formalism.MainNotions.Ext.CutA

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.Ext

def OkpSplit (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 → SplitK D p →
    ∃ α ∈ OKp D lam, ∃ a b : ℤ_[p], α = (zc a, zc b) ∧ IsUnit (a - b)

def OkpNorm (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ∀ α ∈ OKp D lam, ∃ n : ℤ_[p], α.1 * α.2 = zc n

def OkpTwoUnits (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 →
    ∀ α ∈ OKp D lam, ∃ β ∈ OKp D lam, ∃ γ ∈ OKp D lam, ‖β.1‖ = 1 ∧ ‖γ.1‖ = 1 ∧ α = β + γ

theorem sDiff_of (H : SDiffOfGram) (D : D7) : GL3r7.StatementSymmetricDifference D := by
  intro hPG hbc p _ cc δ g hAt hp
  exact H p g (OKp D g.lam) hAt.2.2.2.2 (okp_zero D g.lam) (fun β hβ => okp_swap D g.lam β hβ)
    (fun β hβ γ hγ => okp_add D g.lam β γ hβ hγ) (fun β hβ γ hγ => okp_mul D g.lam β γ hβ hγ)
    (hPG p cc δ g hAt hp) (hbc p cc δ g hAt hp)

theorem splitZero_of (H : SplitZeroG) (D : D7) (hsp : OkpSplit D) (he : endInt D) (ha : addInt D) (hn : phNorm D)
    (hb : beConj D) (hB : beBiadd D) : splitZero D := by
  intro p _ cc δ g hAt hp hspl
  refine H p g (OKp D g.lam) hAt.2.2.2.2 hp (fun α hα => okpSwap_holds D p g.lam α hα)
    (fun α hα => he p cc δ g hAt α hα) (ha p cc δ g hAt).1 (fun α hα => hb p cc δ g hAt hp α hα)
    (hB p cc δ g hAt).1 ?_ (hsp p g.lam hp hspl)
  have h := hn p cc δ g hAt hp _ (okpNeg_holds D p g.lam)
  simpa using h

theorem beConj_of (H : BeConjOfNorm) (D : D7) (hN : OkpNorm D) (hU : OkpTwoUnits D) (he : endInt D) (ha : addInt D)
    (hn : phNorm D) (hB : beBiadd D) : beConj D := by
  intro p _ cc δ g hAt hp α hα
  have hadd : ∀ β ∈ OKp D g.lam, ∀ γ ∈ OKp D g.lam, β + γ ∈ OKp D g.lam :=
    fun β hβ γ hγ => okp_add D g.lam β γ hβ hγ
  exact H p g (OKp D g.lam) hAt.2.2.2.2 (fun β hβ => okpSwap_holds D p g.lam β hβ) hadd
    (fun β hβ => he p cc δ g hAt β hβ) (ha p cc δ g hAt).1 (fun β hβ => hN p g.lam β hβ)
    (fun β hβ => hU p g.lam hp β hβ) (fun β hβ => hn p cc δ g hAt hp β hβ) (hB p cc δ g hAt).1 α hα

end Formalism.MainNotions.Ext.CutA
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtEndIntWHolds
section
namespace Formalism.MainNotions.Ext

theorem okpInertG_holds : OkpInertG := integers_inert_prime

theorem inertPrime_holds : InertPrime := isPrime_span_of_jacobi_neg_one

theorem okpInert_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.okpInert D := okpInert_of okpInertG_holds inertPrime_holds D

theorem stmt_endIntW_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.StatementEndomorphismIntegralWitt D := stmt_endIntW_of_okp D (okpInert_holds D)

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtPhDualWHolds
section
namespace Formalism.MainNotions.Ext

theorem addPtW_holds : AddPtW :=
  fun p _ g hOk hF σ a b ha hb =>
    formal_group_add_generation ℂ_[p] (Formalism.MainNotions.GL3Theta.Wp p) g.l g.ex hOk.2.2.1 hOk.2.2.2 hF σ a b ha hb

theorem mulPtW_holds : MulPtW :=
  fun p _ g hOk c hc σ a ha =>
    formal_group_mul_generation ℂ_[p] (Formalism.MainNotions.GL3Theta.Wp p) g.l g.ex hOk.2.2.1 hOk.2.2.2 c hc σ a ha

theorem linPtW_holds : LinPtW :=
  fun p _ g hOk hF ι _ c hc σ a ha =>
    formal_group_lin_generation ℂ_[p] (Formalism.MainNotions.GL3Theta.Wp p) g.l g.ex hOk.2.2.1 hOk.2.2.2 hF ι c hc σ a ha

theorem stmt_beW_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.StatementBilinearWitt D :=
  beW_of addPtW_holds mulPtW_holds D fun _ _ _ _ hα => by apply okp_swap; exact hα

theorem stmt_PhDualW_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.StatementPhaseDualWitt D := phDualW_of addPtW_holds linPtW_holds D

theorem stmt_SDiffW_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3r7.StatementSymmetricDifferenceWitt D := sDiffW_of addPtW_holds mulPtW_holds linPtW_holds D

end Formalism.MainNotions.Ext
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtTransInvHolds
section
namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

theorem lamOf_lat_holds (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 ∧ lamOf D cc δ = lat2 w₁ w₂ :=
  lamOf_lat idealLattice_holds D cc hc δ hδ

theorem delta_ne_holds (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 :=
  delta_ne' idealLattice_holds D cc hc δ hδ

theorem sgStar_spec (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    Differentiable ℂ (sgStar (lamOf D cc δ)) ∧ deriv (sgStar (lamOf D cc δ)) 0 = 1 ∧
      (∀ z, sgStar (lamOf D cc δ) (-z) = -sgStar (lamOf D cc δ) z) := by
  obtain ⟨w₁, w₂, hw, hL⟩ := lamOf_lat_holds D cc hc δ (delta_ne_holds D cc hc δ hδ)
  have h := sigmaStarEx_holds w₁ w₂ hw
  rw [hL]
  unfold sgStar
  have hs := Classical.epsilon_spec h
  exact ⟨hs.1, hs.2.1, hs.2.2.1⟩

theorem area_lamOf (D : D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (hc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    area (lamOf D cc δ) = ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * Real.sqrt |(NumberField.discr D.host.K : ℝ)| / 2 := by
  have h := idealLattice_holds D.host.K (D.host.φ₀.comp (algebraMap D.host.K D.host.E))
    (Formalism.MainNotions.Ext.finrank_K D.host) (Formalism.MainNotions.Ext.no_real_K D.host) cc δ hc hδ
  exact h.2

end Formalism.MainNotions.Ext
end

