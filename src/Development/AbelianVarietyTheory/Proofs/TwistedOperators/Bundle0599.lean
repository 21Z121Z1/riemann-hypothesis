import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0560
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0580
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0431
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LawStep
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0851
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0512
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0559
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0581
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0582
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0567
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedAbsComplexPowHalfMemSubfieldOfSqrtNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host

noncomputable section

namespace GlobalTheory.HalfPowField

theorem apow_half_mem_of_sqrt : ∀ {D : D7} (F : Subfield ℂ) (w : Pl D.host.E), ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ F → ∀ u : (Kw w)ˣ, apow u (1 / 2) ∈ F := by
  intro D F w hs u
  simpa using GlobalTheory.MovedField.apow_half_mem hs u 1

end GlobalTheory.HalfPowField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacePartFixesStandardVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.OffPartVac

theorem unrOff_mu_locPl {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (j : Fin D.R.m) {e : AE D} (he : IsIdemSum e (locPl G t)) : Formalism.IndefR.Fin.UnrOff e (L.mu t ((j : ℕ) + 1)) := by

  have hbase : GlobalTheory.VecInv.UnrOff (e + cA D e) (L.mu0 ((j : ℕ) + 1)) := by
    refine GlobalTheory.ChrOff.unrOff_of_unrAt D _ (L.C.mu0 j) (locPl G t) e (hL.mu0 j) he ?_
    intro Q hQ hQc
    by_cases hg : ∀ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal
    · exact (L.C.isMu0 j).unr Q hg
    · exfalso
      push Not at hg
      obtain ⟨k, hk⟩ := hg
      have hk' := (GlobalTheory.FunObj.Good.natCast_mem_under Q (D.host.g k)).2 hk
      have hS1 : Q.under (𝓞 D.host.F) ∈ S1 D := by
        rw [GlobalTheory.ChiGrid.S1_mem_OmF]
        fin_cases k
        · exact Or.inl hk'
        · exact Or.inr (Or.inl hk')
      have hS0 : Q.under (𝓞 D.host.F) ∈ G.pl.S0 := G.pl.mem_S0_of_sum_eq.2 (Or.inr hS1)
      have hW0 : G.pl.w (Q.under (𝓞 D.host.F)) ∈ G.pl.W0 := by
        classical
        exact Finset.mem_image_of_mem _ hS0
      have hw : G.pl.w (Q.under (𝓞 D.host.F)) ∈ locPl G t := GlobalTheory.FunObj.GivenAdm.mem_locPl.2 (Or.inl hW0)
      rcases GlobalTheory.IdemSupport.eq_or_eq_cP (G.pl.under_w hS0).symm with h | h
      · exact hQ (by rw [h]; exact hw)
      · exact hQc _ hw ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 h)

  have htw : GlobalTheory.VecInv.UnrOff (e + cA D e) (L.xi t) := by
    refine GlobalTheory.ChrOff.unrOff_of_unrAt D _ (L.xiH t) (locPl G t) e (hL.xi t) he ?_
    intro Q hQ hQc
    by_contra hr
    rcases (hL.Q_ram t Q).1 hr with hq | ⟨Q', hQ', hc⟩
    · exact hQ (GlobalTheory.FunObj.GivenAdm.mem_locPl.2 (Or.inr hq))
    · exact hQc Q' (GlobalTheory.FunObj.GivenAdm.mem_locPl.2 (Or.inr hQ')) hc
  intro x h1 h2 h3 h4
  show (L.mu0 ((j : ℕ) + 1) * L.xi t) x = 1
  rw [MonoidHom.mul_apply, hbase x h1 h2 h3 h4, htw x h1 h2 h3 h4, one_mul]

private theorem cut_one_sub_eq_resG_one_sub_of_isIdempotentElem {D : D7} (V : HSp D) {ε : AF D.host.F} (hε : IsIdempotentElem ε) {f : AE D}
    (hf : algebraMap (AF D.host.F) (AE D) ε = f) (g : GA D V) :
    cutPart (1 - f) V g = Formalism.IndefR.Fin.LevelGroupLemmas.resG V (1 - ε) g := by
  have hid : IsIdempotentElem (1 - ε) := hε.one_sub
  have ha : algebraMap (AF D.host.F) (AE D) (1 - ε) = 1 - f := by rw [map_sub, map_one, hf]
  have h1 : (1 - f) * (1 - f) = 1 - f := by rw [← ha, ← map_mul, hid.eq]
  have h2 : cA D (1 - f) = 1 - f := by rw [← ha, GlobalTheory.IdemSupport.cA_algebraMap]
  apply Subtype.ext
  apply Units.ext
  change Formalism.L2.Theta.mt V _ = Formalism.L2.Theta.mt V _
  rw [mt_cutPart h1 h2, Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG' hid, ha]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem cut_conj_unipotent_mem_St_succ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m)
    (k : FinPt G (.top (j + 1))) (hk : finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj) {e : AE D}
    (he : IsIdemSum e (locPl G t)) :
    Lev.finE (G.V (.top (j + 1))) (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1)))
      ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))
      ∈ Formalism.L2.DIV.St ((Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1)⁻¹ * S.βp (j + 1)) := by
  have hlev : finG (G.V (.top (j + 1))) k ∈ prodLev (S.βp (j + 1)) (locPl G t) _ _ := hk
  refine GlobalTheory.OffPartLattice.finE_cut_mem_St (G.V (.top (j + 1))) (S.βp (j + 1))
    (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1) (finG (G.V (.top (j + 1))) k) _ ?_ he ?_
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, finG, MonoidHom.comp_apply, Subgroup.coe_subtype]
  · intro Q hQ
    have h2 := (Subgroup.mem_inf.1 hlev).2
    exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 Q) hQ)

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SplitHecke GlobalTheory.ThetaMove GlobalTheory.OffPartLattice in

theorem offPart_fixes_vac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    W.om (.top t (j + 1)) (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))), 1) (S.Z.vac (.top t (j + 1))) = S.Z.vac (.top t (j + 1)) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he

  have hv := S.Z.vac_is (.top t (j + 1)) hj
  unfold IsVacO at hv
  obtain ⟨_, hv2⟩ := hv
  obtain ⟨_, hθ, hlat, _, hcov, hnrm⟩ := hv2

  obtain ⟨⟨es, hes, hesum⟩, hc⟩ := id he
  have hε : IsIdempotentElem (Formalism.IndefR.Fin.LevelGroupLemmas.epsP (locPl G t)) :=
    Formalism.IndefR.Fin.LevelGroupLemmas.isIdempotentElem_placeIdempotent hes hesum hc _ subset_rfl
  have halg := Formalism.IndefR.Fin.LevelGroupLemmas.algebraMap_epsP hes hesum
  set ε := Formalism.IndefR.Fin.LevelGroupLemmas.epsP (locPl G t)
  have hid : IsIdempotentElem (1 - ε) := hε.one_sub

  have hle1 : j + 1 ≤ D.R.m := by omega
  have hle2 : j + 1 + 1 ≤ D.R.m := hj
  have hr1 := rank_top G hle1
  have hr2 := rank_top G hle2

  set V := G.V (.top (j + 1))
  set g : GA D V := (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D V)
  have hgf : g ∈ GfC V := ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))).2
  have hcut : cutPart (1 - (e + cA D e)) V g = Formalism.IndefR.Fin.LevelGroupLemmas.resG V (1 - ε) g :=
    cut_one_sub_eq_resG_one_sub_of_isIdempotentElem V hε halg g

  have hnodd : ¬ Odd (G.pS (Pair.top t (j + 1))).rank := by
    rw [Nat.not_odd_iff_even]
    change Even (G.V (.top (j + 1))).rank
    rw [hr1]
    exact rankX_even D _
  have hnodd' : ¬ Odd (G.pT (Pair.top t (j + 1))).rank := by
    rw [Nat.not_odd_iff_even]
    change Even (G.V (.top (j + 1 + 1))).rank
    rw [hr2]
    exact rankX_even D _
  have hmu : Formalism.IndefR.Fin.UnrOff e (L.mu t (j + 1 + 1)) := unrOff_mu_locPl G hL t ⟨j + 1, hj⟩ he
  have hchS : G.chrS (Pair.top t (j + 1)) = L.mu t (j + 1 + 1) := by
    simp only [GridData.chrS, Formalism.IndefR.Lift.attChr, hnodd, if_false]
    rfl
  have hchT : G.chrT (Pair.top t (j + 1)) = L.mu t (j + 1 + 1) := by
    simp only [GridData.chrT, Formalism.IndefR.Lift.attChr, hnodd', if_false]
    rfl

  have hfrS := isFrame_moved (S.N.latS (Pair.top t (j + 1))) (G.Λ (.top (j + 1))) (S.βp (j + 1))
    (Lev.finE V (S.N.u (.top (j + 1))).1) (S.βp_is (j + 1) hle1) (S.N.u_lat (.top (j + 1)) hle1)
  have hfrT := isFrame_moved (S.N.latT (Pair.top t (j + 1))) (G.Λ (.top (j + 1 + 1))) (S.βp (j + 1 + 1))
    (Lev.finE (G.V (.top (j + 1 + 1))) (S.N.u (.top (j + 1 + 1))).1) (S.βp_is (j + 1 + 1) hle2)
    (S.N.u_lat (.top (j + 1 + 1)) hle2)
  have hst := cut_conj_unipotent_mem_St_succ S j hj k hk he

  have hVF := Formalism.IndefR.Fin.LevelGroupLemmas.vacFixOff (Formalism.IndefR.Fin.splitLinF D) (Formalism.IndefR.Fin.placeModelAtF D)
    (Formalism.IndefR.Fin.splitOrInert D)
  have hW := W.om_is (Pair.top t (j + 1)) hle2
  refine hVF W.ψ _ _ _ _ _ hW (GlobalTheory.InertAll.inertAllO D _ _ _ _ _ _ hW) ?_ ?_ _ _
    (GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on _ hle1))
    (GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on _ hle2))
    _ _ hfrS hfrT (locPl G t) e he (by rw [hchS]; exact hmu) (by rw [hchT]; exact hmu) _ hθ hlat ?_ _ 1 ?_
    (Subgroup.one_mem _) hst (by rw [map_one]; exact Subgroup.one_mem _) ?_ ?_
  · change (G.V (.top (j + 1))).rank ≠ (G.V (.top (j + 1 + 1))).rank
    rw [hr1, hr2]
    unfold GlobalTheory.ChiGrid.rankX
    rw [add_mul (j + 1) 1, one_mul]
    generalize (j + 1) * (D.R.t + 1) = a
    omega
  · left
    change Even (G.V (.top (j + 1))).rank
    rw [hr1]
    exact rankX_even D _
  · obtain ⟨⟨μ, 𝓕⟩, hμ⟩ := hcov
    exact ⟨μ, 𝓕, hμ, hnrm ⟨μ, 𝓕⟩ hμ⟩
  · change cutPart (1 - (e + cA D e)) V g ∈ GfC V
    rw [hcut]
    exact Formalism.IndefR.Fin.LevelGroupLemmas.resG_mem_GfC V hid hgf
  · intro i j'
    change (e + cA D e) * (Formalism.L2.Theta.mt V (cutPart (1 - (e + cA D e)) V g) - 1) i j' = 0
    rw [hcut, Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG_sub hid, ← mul_assoc, ← halg, ← map_mul, mul_sub, mul_one, hε.eq,
      sub_self, map_zero, zero_mul]
  · intro i j'
    simp [Formalism.L2.Theta.mt]

end GlobalTheory.OffPartVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacesPartMovedLevelKeepsStandardHomLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.offPlacesPart_movedLevel_keeps_standardHomLattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ u : WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)),
      u ∈ stdLatO S (.top t (j + 1)) ↔ ∃ u₀ ∈ stdLatO S (.top t (j + 1)),
        u = actO _ _ (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1)))
          ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))))) 1 u₀ := by
  first | exact @GlobalTheory.OffPartLattice.offPart_keeps_stdLatO | exact GlobalTheory.OffPartLattice.offPart_keeps_stdLatO | (intros; apply GlobalTheory.OffPartLattice.offPart_keeps_stdLatO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmSplitHalves
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField
open MeasureTheory GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter
open scoped TensorProduct

namespace GlobalTheory.VacStabFixed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem parts_ext {x y : AE D} (h1 : infPart D x = infPart D y) (h2 : finPart D x = finPart D y) : x = y := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  exact e.injective (Prod.ext ((he _).1.trans (h1.trans (he _).1.symm)) ((he _).2.trans (h2.trans (he _).2.symm)))

theorem place_comp {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 ∧
      compFin D v (finPart D (algebraMap (AF D.host.F) (AE D) ε)) = 1 ∧
      ∀ w, w ≠ v → compFin D w (finPart D (algebraMap (AF D.host.F) (AE D) ε)) = 0 := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  refine ⟨TensorProduct.zero_tmul _ _, ?_, fun w hw => ?_⟩
  · change evalV D.host.F v α ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [h1]; rfl
  · change evalV D.host.F w α ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [h0 w hw, TensorProduct.zero_tmul]

theorem supp_iff {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) (z : AE D) :
    algebraMap (AF D.host.F) (AE D) ε * z = z ↔
      infPart D z = 0 ∧ ∀ w, w ≠ v → compFin D w (finPart D z) = 0 := by
  obtain ⟨hi, h1, h0⟩ := place_comp hε
  constructor
  · intro h
    refine ⟨by rw [← h, RingHom.map_mul, hi, zero_mul], fun w hw => ?_⟩
    rw [← h, RingHom.map_mul, RingHom.map_mul, h0 w hw, zero_mul]
  · rintro ⟨a, b⟩
    refine parts_ext (by rw [RingHom.map_mul, hi, zero_mul, a]) (GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun w => ?_)
    change compFin D w _ = compFin D w _
    rw [RingHom.map_mul, RingHom.map_mul]
    by_cases hw : w = v
    · subst hw; rw [h1, one_mul]
    · rw [b w hw, mul_zero]

theorem unramAt_of {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    {χ : (AE D)ˣ →* Circle} (hχ : CharUnramAt D χ v) : UnramAt ε χ := by
  intro x hx h1 h2
  obtain ⟨a, b⟩ := (supp_iff hε _).1 hx
  refine hχ x ?_ (fun w hw => ?_) h1 h2
  · rwa [RingHom.map_sub, RingHom.map_one, sub_eq_zero] at a
  · have := b w hw
    rwa [RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one, sub_eq_zero] at this

theorem map_sub_one {R R' n : Type} [CommRing R] [CommRing R'] [DecidableEq n] (φ : R →+* R') (M : Matrix n n R)
    (h : M.map φ = 1) (i j : n) : φ ((M - 1) i j) = 0 := by
  have h1 : φ (M i j) = (1 : Matrix n n R') i j := congrFun (congrFun h i) j
  rw [Matrix.sub_apply, map_sub, h1, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem suppPl_of {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {V : HSp D}
    {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {k : GA D V} (hk : InStabAt V L v k) : SuppPl ε V k :=
  fun i j => (supp_iff hε _).2 ⟨map_sub_one _ _ hk.1 i j,
    fun w hw => map_sub_one ((compFin D w).comp (finPart D)) _ (hk.2.1 w hw) i j⟩

theorem det_int {V : HSp D} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hL : Submodule.IsLattice D.host.E L) (g : GA D V)
    (h : ∀ y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)),
      (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E))) :
    finPart D (Formalism.L2.Theta.mt V g).det ∈ intAE D := by
  have hd : finPart D (Formalism.L2.Theta.mt V g).det = (finMat D.sp.cm.sig V.gram g).det :=
    RingHom.map_det (finPart D) (Formalism.L2.Theta.mt V g)
  rw [hd, GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers]
  exact GlobalTheory.DetTranslate.det_mem_int D.host.F L _ hL.fg hL.span_eq_top h

theorem unram_detAt {V : HSp D} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hL : Submodule.IsLattice D.host.E L) {g : GA D V}
    (h : ∀ y, y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)) ↔
      (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)))
    {e : AE D} (he : e * e = e) {ε : AF D.host.F} (hs : algebraMap (AF D.host.F) (AE D) ε * e = e)
    {χ : (AE D)ˣ →* Circle} (hχ : UnramAt ε χ) : χ (GlobalTheory.VecInv.detAt e he V g) = 1 := by
  refine hχ _ ?_ (GlobalTheory.Mem.DetUnit.part_mem_intAE he (det_int hL g fun y hy => (h y).1 hy)) ?_
  · change _ * (e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1
    linear_combination ((Formalism.L2.Theta.mt V g).det - 1) * hs
  · rw [← MonoidHom.map_inv]
    exact GlobalTheory.Mem.DetUnit.part_mem_intAE he (det_int hL g⁻¹ (GlobalTheory.LocalLatStab.inv_keeps V _ g h))

open GlobalTheory.SplitScalar GlobalTheory.SplitHecke in

theorem om_split_halves {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {e : AE D}
    (he : IsSplitIdem D e) {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h)
    (hL : ∀ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True,
      actO S T g h u ∈ (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) ∧
      actO S T g⁻¹ h⁻¹ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True)
    {x y : (AE D)ˣ} (hx : IsDetAt e S g x) (hy : IsDetAt e T h y) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (v1 : ∀ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True, IsHalf e u → heisO ψ S T u f = f)
    (v2 : ∀ u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True, IsHalf (cA D e) u → heisO ψ S T u f = f) :
    om (g, h) f = ((splitFacO χS χT x y : Circle) : ℂ) • f := by
  by_cases hf0 : f = 0
  · subst hf0
    simp only [map_zero, smul_zero]
  have he' := isSplitIdem_conj he
  have hψ := hW.std.1
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hW.std hS hT).1
  have hst := @GlobalTheory.SplitScalar.idem_smul_mem D S T (ΛS : Set _) (ΛT : Set _) _ he.1
  have hstc := @GlobalTheory.SplitScalar.idem_smul_mem D S T (ΛS : Set _) (ΛT : Set _) _ he'.1
  have hfin := @latO_fin D S T (ΛS : Set _) (ΛT : Set _)
  generalize latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) = Λ at *
  have hL' : ∀ u, actO S T g⁻¹ h⁻¹ u ∈ Λ ↔ u ∈ Λ := fun u =>
    ⟨fun hu => by
      have := (hL _ hu).1
      rwa [GlobalTheory.AdelicLatMove.actO_actO_inv] at this, fun hu => (hL u hu).2⟩
  have hd : ∀ y, IsHalf e y → y ∉ Λ → ∃ l ∈ Λ, IsHalf (cA D e) l ∧ ψ (symplO S T l y) ≠ 1 :=
    fun y hy hn => exists_dual_half he hdual hstc hy hn
  have hd' : ∀ y, IsHalf (cA D e) y → y ∉ Λ → ∃ l ∈ Λ, IsHalf e l ∧ ψ (symplO S T l y) ≠ 1 := fun y hy hn => by
    have := exists_dual_half he' hdual (by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hst) hy hn
    rwa [GlobalTheory.DualPairCheck.cA_cA] at this
  obtain ⟨r, hr, hom⟩ := om_eq_smul_sum hW he (fun u hu => (hdual u (hfin hu)).1 hu) hd hd' hg hh hx hy (R := {0})
    (fun u hu => by
      rw [Finset.mem_singleton.1 hu]
      exact ⟨(hL' 0).2 (zero_mem _), isHalf_zero e⟩)
    (fun w hw _ => ⟨0, ⟨Finset.mem_singleton_self _, by rw [sub_zero]; exact (hL' w).1 hw⟩,
      fun v hv => Finset.mem_singleton.1 hv.1⟩)
    (fun w hw _ => (hL' w).2 hw)
  simp only [Finset.sum_singleton, heisO_zero] at hom
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ⟩, c, hc⟩ := GlobalTheory.exists_normalise_meanSquare_of_cocompact (WO S T) (ratL T S) K hK hKc f hf.cont hf0
    (by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm (hf.quasi γ w)).trans (by rw [norm_mul, hψ.2.1, one_mul]))
  have hn : nrm2 μ 𝓕 (c • f) = 1 := hc μ 𝓕 hμ.1 hμ.2.1 hμ.2.2
  have hcf := GlobalTheory.WeilVacMove.isTheta_smul c hf
  have h1 := hom _ hcf (fun u hu hh => by rw [heisO_smul, v1 u hu hh])
    fun u hu hh => by rw [heisO_smul, v2 u hu hh]
  have h2 : nrm2 μ 𝓕 (om (g, h) (c • f)) = 1 := by
    rw [← hn, nrm2, nrm2, integral_normSq_eq _ (hW.om_pres _ _ hcf).cont.measurable,
      integral_normSq_eq _ hcf.cont.measurable, hW.om_unit μ 𝓕 hμ.1 hμ.2.1 _ _ hcf]
  have h3 : nrm2 μ 𝓕 ((splitFacO χS χT x y : ℂ) • c • f) = 1 := by
    rw [← hn, nrm2, nrm2]
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
  rw [h1, mul_smul, pairNorm_smul, h3, mul_one] at h2
  have h4 : r = 1 := by
    rw [← Real.sqrt_sq hr.le, h2, Real.sqrt_one]
  rw [hom f hf v1 v2, h4, Complex.ofReal_one, one_mul]

theorem half_mem_place {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {e : AE D}
    (hs : algebraMap (AF D.host.F) (AE D) ε * e = e) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True)
    (hh : IsHalf e u) : u ∈ latO S T LS LT fun w => w = v := by
  refine (GlobalTheory.VecInvInert.mem_place_iff hε u).2 ⟨hu, Matrix.ext fun i j => ?_⟩
  change _ * u i j = u i j
  rw [← hh i j, ← mul_assoc, hs]

theorem vacFixedAt (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : VacFixedAt D v := by
  intro ψ S T χS χT om hW uS uT LS LT hS hT f hf hvac k k' hk hk'
  obtain ⟨ε, hε⟩ : ∃ ε, IsPlaceIdem D v ε :=
    ⟨_, singleV D.host.F v 1, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _,
      fun w hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have uS' := unramAt_of hε uS
  have uT' := unramAt_of hε uT
  have sk := suppPl_of hε hk
  have sk' := suppPl_of hε hk'
  by_cases hsp : ∃ e : AE D, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε
  · obtain ⟨e, he, hb⟩ := hsp
    have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
    have s1 : algebraMap (AF D.host.F) (AE D) ε * e = e := by
      rw [← hb]; linear_combination he.1 + he.2.1
    have s2 : algebraMap (AF D.host.F) (AE D) ε * cA D e = cA D e := by
      rw [← hb]; linear_combination he'.1 + he.2.1
    have key := om_split_halves hW hS hT he (fun i j => by rw [hb]; exact sk i j) (fun i j => by rw [hb]; exact sk' i j)
      (fun u hu => ⟨GlobalTheory.LocalLatStab.actO_mem S T _ _ _ k k' (fun y hy => (hk.2.2 y).1 hy)
          (fun y hy => (hk'.2.2 y).1 hy) u hu,
        GlobalTheory.LocalLatStab.actO_mem S T _ _ _ k⁻¹ k'⁻¹ (GlobalTheory.LocalLatStab.inv_keeps S _ k hk.2.2)
          (GlobalTheory.LocalLatStab.inv_keeps T _ k' hk'.2.2) u hu⟩)
      (GlobalTheory.VecInv.isDetAt_detAt e he.1 S k) (GlobalTheory.VecInv.isDetAt_detAt e he.1 T k') hf
      (fun u hu hh => hvac.2 e he u (half_mem_place hε s1 hu hh) hh)
      (fun u hu hh => hvac.2 _ he' u (half_mem_place hε s2 hu hh) hh)
    rwa [splitFacO, unram_detAt hS.1 hk.2.2 he.1 s1 uT', unram_detAt hT.1 hk'.2.2 he.1 s1 uS', inv_one, mul_one,
      Circle.coe_one, one_smul] at key
  · have hv : NonSplitAt D v ε := ⟨hε, hsp⟩
    obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
    refine GlobalTheory.T.weilDatum_fixes_vacuum_nonSplitPlace_unramified D ψ hW.std S T LS LT hS hT χS χT om ⟨η, e1, e4, e3, e2⟩ hW v ε hv uS' uT' k k' sk sk'
      (GlobalTheory.LocalLatStab.mem_latO_place_iff_actO D S T LS LT hS hT v ε hε k k' hk.2.2 hk'.2.2) f hf fun u hu => ?_
    obtain ⟨a, ha, ha2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hv
    have h1 : 2 • (a • u) = u := by
      rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.VecInvInert.idem_smul_eq hε hu]
    have h2 := hvac.1 (a • u) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u hu)
    rwa [h1] at h2

theorem vacFixed (D : D7) : VacFixed D := fun v _ => vacFixedAt D v

end GlobalTheory.VacStabFixed

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OtherInstanceFormFlagPairingIntegralOnFrameLattiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.otherInstanceForm_flagPairing_integral_on_frameLattice : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ (PP : Pl D.host.E) (a : Fin (Yc D 0).rank) (z : Fin (Yc D 0).rank → EAf D), (∀ i, Matrix.mulVec (β⁻¹).val z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → GlobalTheory.SeeConjChar.hT X h (pairAt X h PP a) z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.SeeConjChar.hT_pairAt_int | exact GlobalTheory.SeeConjChar.hT_pairAt_int | (intros; apply GlobalTheory.SeeConjChar.hT_pairAt_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacesDistinctTranslationsDerivativesCommuteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaces_distinct_translations_derivatives_commute : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
    IsInfFam (D := D) θ → ∀ τ τ' : D.what₂.Tau, τ ≠ τ' →
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), ∀ f : GA D V → ℂ,
      rTr V (atTau θ V τ g) (rTr V (atTau θ V τ' h) f) = rTr V (atTau θ V τ' h) (rTr V (atTau θ V τ g) f)) ∧
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ X ∈ lieAt V τ', ∀ f : GA D V → ℂ,
      Rder θ V τ' X (rTr V (atTau θ V τ g) f) = rTr V (atTau θ V τ g) (Rder θ V τ' X f)) ∧
    (∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt V τ', ∀ f : GA D V → ℂ, IsAutFunSm θ V f →
      Rder θ V τ X (Rder θ V τ' Y f) = Rder θ V τ' Y (Rder θ V τ X f)) := by
  first | exact @GlobalTheory.PlaceComm.place_comm | exact GlobalTheory.PlaceComm.place_comm | (intros; apply GlobalTheory.PlaceComm.place_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealUnitaryFockColumnActionSurjectiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realUnitaryFockColumnAction_surjective : ∀ {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1), Function.Surjective (GlobalTheory.RealColAct.realCol θ hθ V hV) := by
  first | exact @GlobalTheory.RealColAct.realCol_surjective | exact GlobalTheory.RealColAct.realCol_surjective | (intros; apply GlobalTheory.RealColAct.realCol_surjective <;> assumption)
end

