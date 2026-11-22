import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0611
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0049
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0052
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0050
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0054
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0108
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0232
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0078
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0072
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0141
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0056
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0066
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0076
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0835
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0200
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0132
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0128
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0204
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0215
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0197
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0233
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0823
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0133
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0205
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0210
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0021
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0026
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0036
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0136
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0150
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0155
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0831
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0227

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LawsLinksOfGeoRowsCols
section
set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 4000000
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem GlobalTheory.Fam.lawsLinks_of_geo_rows_cols_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.StrongApproxSU → ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row, (∀ t, (row t).Is) → (∀ t t', (row t).Same (row t')) → (∀ k : _root_.GlobalTheory.Fam.FamilyConstants a, ∃ col w₀ w F, _root_.GlobalTheory.AdForm.FamilyColumnCondition (a.fam row col) ∧ _root_.GlobalTheory.Fam.ColumnOutputCondition (row := row) (col := col) k w₀ w F) → ∃ col, (a.fam row col).RowOK ∧ LawsX (a.fam row col).t ∧ _root_.GlobalTheory.MiTop.ChartAtZeroCondition (a.fam row col) ∧ _root_.GlobalTheory.MiTop.LinkTailCondition (a.fam row col) ∧ _root_.GlobalTheory.MiTop.LinkCommutes (a.fam row col) ∧ _root_.GlobalTheory.MiTop.FamilyRatioCondition (a.fam row col) := by
  intro hDS hHC hSA B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT row hrow hsame hcol
  letI := a.fld; letI := a.val; letI := a.top; haveI := a.loc
  have hRow : ∀ col, (a.fam row col).RowOK := fun col => ⟨ha.meas, ha.last, ha.x, hrow, hsame⟩
  obtain ⟨col₀, -, -, -, -, -⟩ := hcol ⟨fun _ _ => 1, fun _ => ⟨0, Fin.elim0, Fin.elim0⟩, 0, 0, 0, 0⟩
  have hcIs : (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is := (_root_.GlobalTheory.T.famCh_is_and_tuples_is_of_colOK hDS hHC W u hW.pk (a.fam row col₀) (hRow col₀)).1
  obtain ⟨ε, op, r, e, cG, hr, hcG, hkap, hvIs, hall⟩ :=
    GlobalTheory.T.seeSaw_latticeFramePins_finiteIntegralLaws _ _ a.v a.k a.ι a.o a.n a.G hcIs ha.last ha.vis ha.shape ha.gpin
  obtain ⟨s, hs, hζ⟩ := _root_.GlobalTheory.T.nonzero_scalars_roots_of_unity_alt _ _ _ _ _ _ _ _ _ W u (a.fam row col₀) hW.pk (hRow col₀) a.v ha.vis
    (ha.tie row col₀).1 a.n a.G a.pl ha.gpin (ha.tie row col₀).2
  choose ζ hζu hζv using hζ
  let k : _root_.GlobalTheory.Fam.FamilyConstants a := ⟨ε, op, r, e, cG, fun t j => s j * ζ t j⟩
  obtain ⟨col, w₀, w, F, hFC, hCO⟩ := hcol k
  have hQ : ∀ t p, p ∈ (w t).Q ↔ ∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, p = PP.under (𝓞 (I.rec7 l Z).host.F) := by
    intro t p
    rw [(hCO.same t).1, (hCO.pins t).places p]
    obtain ⟨pl, hpl⟩ := (hCO.lev t).places
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(pl i).1, (pl i).2, (hpl i).2⟩
    · rintro ⟨PP, hPP, rfl⟩
      exact ⟨pl.symm ⟨PP, hPP⟩, by rw [(hpl _).2, Equiv.apply_symm_apply]⟩
  have hVf : ∀ t, _root_.GlobalTheory.Fam.VectorFunctionCondition (a.fam row col) a.v (w t) (k.sc t) := by
    intro t
    let w' : VTup ((a.fam row col₀).t t) := ⟨(w₀ t).Q, 0, (w₀ t).eQ, (w₀ t).eQT, fun _ _ _ => 0, fun _ _ => 0, fun _ _ _ => 0, fun _ _ => ∅,
      fun _ => ∅, ∅, 0, 0⟩
    have h1 := hζv t w' (fun p => by rw [← (hCO.same t).1]; exact hQ t p)
      (fun j => ⟨(hCO.atQ t j).1, (hCO.atQ t j).2.1⟩) (hCO.vec t)
    obtain ⟨-, he, heT, -⟩ := hCO.same t
    refine ⟨fun j hj P b hb b' hb' => ?_, fun j h P => ?_⟩
    · rw [he]; exact h1.1 j hj P b hb b' hb'
    · rw [heT]; exact h1.2 j h P
  have hIs := _root_.GlobalTheory.T.famCh_is_and_tuples_is_of_colOK hDS hHC W u hW.pk (a.fam row col) (hRow col)
  have htIs : ∀ t, ((a.fam row col).t t).Is := hIs.2 hCO.ok
  have hweil := fun t => _root_.GlobalTheory.T.weilOK_of_rank_one_gram' W u hW.pk (a.fam row col) a.v (hRow col) hCO.ok (ha.tie row col).1
    (fun j h => ⟨ha.shape.pre.line.1, ha.shape.pre.tau j h⟩) t (w t) (hQ t)
  have hchars : ∀ t i, (a.G i).Chars ((a.fam row col).t t) := fun t => (hweil t).2.2.2.2.2.2 a.n a.G a.pl (ha.tie row col).2
  have hrowt := fun t => _root_.GlobalTheory.T.quadratic_family_level_identity_alt _ _ _ _ _ _ _ _ _ W u (a.fam row col) hW.pk (hRow col) a.v ha.vis (ha.tie row col).1 a.n a.G a.pl
    ha.gpin (ha.tie row col).2 t (w₀ t) (F t) (htIs t) (hCO.pins t) (hCO.lev t) (hchars t)
  have hVF : ∀ t, VForm k.v (w t) := by
    intro t
    obtain ⟨hsQ, he, heT, -, hFY, hFT⟩ := hCO.same t
    have hw := hweil t
    have hrw := hrowt t
    have htie := (ha.tie row col).1
    obtain ⟨S₀, hS⟩ := hCO.read t
    refine ⟨hw.2.2.2.2.1, hw.2.2.2.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrw.2.1⟩
    · intro j hj P b hb b' hb'
      rw [hCO.sc t]; exact (hVf t).1 j hj P b hb b' hb'
    · intro j h P
      rw [hCO.sc t]; exact (hVf t).2 j h P
    · intro j
      have := hCO.atQ t j
      rw [← hsQ, ← he, ← heT] at this
      exact this
    · intro j α
      obtain ⟨h1, h2⟩ := hCO.e t j α
      have hb : k.v.b j = a.g.b j := htie.b j
      refine ⟨by rw [hb]; exact h1, fun g hg => ?_⟩
      rw [hsQ]; exact h2 g hg
    · intro n h β
      obtain ⟨h1, h2⟩ := hCO.eT t n h β
      have hb : k.v.bT = a.g.bT := htie.bT.1
      refine ⟨by rw [hb]; exact h1, fun g hg => ?_⟩
      rw [hsQ]; exact h2 g hg
    · exact hCO.dd t
    · intro j hj ψ hψ α y
      refine ⟨?_, hCO.FX t j hj ψ hψ α y, hS.S j hj ψ hψ α y⟩
      show _ ∈ a.v.RamAd j
      rw [ha.shape.ram j]; exact hS.ram j (by omega) ψ hψ α y
    · intro j hj G x b hb
      obtain ⟨h1, h2⟩ := hrw.1 j hj G x b hb
      refine ⟨?_, fun κ hκ => h2 κ ?_⟩
      · rw [hFY]; exact ((hCO.FY t j _).2 h1)
      · have hoff : offP k.v (w t) = offP a.v (w₀ t) := by
          funext p
          show (p ∉ a.v.gP ∧ p ∉ (w t).Q) = (p ∉ a.v.gP ∧ p ∉ (w₀ t).Q)
          rw [hsQ]
        rw [hoff] at hκ; exact hκ
    · intro G x
      rw [hFT]; exact hCO.FT t _
  obtain ⟨hloc, hval, hlast⟩ := hall W.P.T (a.fam row col).t w fun t => ⟨htIs t, hVF t, (hweil t).1, (hrowt t).2.2, (hweil t).2.1,
    (hweil t).2.2.2.1, hchars t, (hCO.laws t).1, (hCO.laws t).2.1, (hCO.laws t).2.2, hCO.cT t, hCO.cv t⟩
  have hcls : ClsPinD (a.fam row col).t := _root_.GlobalTheory.T.cls_pin_d_of_true_family W u (a.fam row col) hW.tr hW.tw ha.top (hRow col) hFC
  have hlaws : LawsX (a.fam row col).t := ⟨hIs.1, htIs, hloc, _root_.GlobalTheory.T.realEq_of_colOK' W u hW.pk (a.fam row col) hCO.ok, hval, hlast,
    GlobalTheory.T.seeSawKernelLiftCombination_of_definiteClassData _ _ _ _ hIs.1 htIs hcls, GlobalTheory.T.seeSawLastPeriodFactorization_of_classData _ _ _ _ hIs.1 htIs hcls, GlobalTheory.T.seeSaw_scalarForms_continuous_automorphic_central _ _ _ _ hIs.1 htIs hcls⟩
  have hheq : ∀ t, W.P.I.tup t = (I.rec7 l Z).what₂.mu0 → ∀ φ, HEq (_root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ) ((I.rec7 l Z).eMu u φ).1 := by
    intro t ht φ
    show HEq ((I.rec7 l Z).e0Tw u (W.P.I.tup t) _) _
    rw [ht]
    exact heq_of_eq (GlobalTheory.Mem.Col2.TC.stepZeroTwist_reference_tuple_eq_id l u _)
  refine ⟨col, hRow col, hlaws, hCO.zero, _root_.GlobalTheory.MiTop.linkTail_of_topReadAt_alt W u (a.fam row col) ha.top hheq, ?_, ?_⟩
  · obtain ⟨ρ, hρ, hA⟩ := hcls
    choose S₀ hS₀ using hCO.read
    have hsh : ShapeOff k.v a.o := by
      have hs := ha.shape
      have hp := hs.pre
      exact ⟨⟨hp.nodup, hp.all, hp.inj, hp.tP, hp.char, hp.latT, hp.line, hp.tau, hp.lam, hp.normT, hp.topT⟩,
        fun x => ⟨(hs.good x).bf, (hs.good x).fb⟩, fun x hx => ⟨(hs.split x hx).core, (hs.split x hx).top⟩, hs.glued, hs.rep,
        hs.ram⟩
    have hne : ∀ {S : ℕ → Prop} {x y : ℂ}, UnitRatio S x y → x ≠ 0 := fun h => ((GlobalTheory.Fam.unitRatio_laws _).2.1 _ _ _ _ h h).2.2
    refine _root_.GlobalTheory.T.type_data_unit_shift_relation_alt W u (a.fam row col) a.k a.ι a.o ε S₀ (GlobalTheory.FinPl.RamUnit.ramUnitary_holds _) hIs.1
      (fun t => ⟨htIs t, ?_, ?_, ?_, hS₀ t⟩) ha.shape.pre.nodup ha.shape.pre.all ha.shape.pre.inj ?_ ?_ ?_
    · obtain ⟨⟨A, hAI⟩, -⟩ := hA t
      exact GlobalTheory.T.seeSawTuple_kernelBack_of_classKernelData _ _ _ ρ A hIs.1 (htIs t) hρ hAI fun j hj => hne (hCO.cK t j hj)
    · obtain ⟨-, A, hAI⟩ := hA t
      exact GlobalTheory.T.lastPeriodClasses_give_tailReading _ _ _ ρ A hAI (hne (hCO.cP t))
    · exact GlobalTheory.T.definiteLift_comm_levelPrimeOperators _ _ a.k a.ι k.v a.o _ (w t) (GlobalTheory.T.splitLiftExactConstant_proof _) hIs.1 (htIs t) hvIs (hVF t) hsh
        (_root_.GlobalTheory.T.type_data_local_relation_alt W u hW.pk (a.fam row col) a.v a.k a.ι a.o (hRow col) hCO.ok ha.vis (ha.tie row col).1 ha.shape t)
    · intro t
      obtain ⟨α₀, -⟩ := hCO.zero t
      exact ⟨α₀⟩
    · intro t φ
      obtain ⟨α₀, hα, -, h3, -⟩ := hCO.zero t
      exact ⟨(h3 φ).1, fun α y => by rw [hα α]; exact (h3 φ).2 y⟩
    · intro t
      obtain ⟨α₀, -, -, -, h4⟩ := hCO.zero t
      exact h4
  · intro n hn t
    have hsc : ∀ tt j, j < (I.rec7 l Z).R.m → UnitRatio (_root_.GlobalTheory.MiTop.qPrime_alt W tt) ((w tt).sc j) ((w W.P.A3.A.μ0).sc j) ∧
        UnitRatio (_root_.GlobalTheory.MiTop.qPrime_alt W tt) (((a.fam row col).t tt).cK j) (((a.fam row col).t W.P.A3.A.μ0).cK j) := by
      intro tt j hj
      refine ⟨?_, hCO.cK tt j hj⟩
      rw [hCO.sc tt, hCO.sc W.P.A3.A.μ0]
      obtain ⟨n₁, hn₁, e₁⟩ := hζu tt j
      obtain ⟨n₂, hn₂, e₂⟩ := hζu W.P.A3.A.μ0 j
      have hz : ζ W.P.A3.A.μ0 j ≠ 0 := fun h0 => by rw [h0, zero_pow hn₂.ne'] at e₂; exact zero_ne_one e₂
      refine (GlobalTheory.Fam.unitRatio_laws _).2.2.1 _ _ (n₁ * n₂) (mul_ne_zero (hs j) hz) (Nat.mul_pos hn₁ hn₂) ?_
      show (s j * ζ tt j) ^ (n₁ * n₂) = (s j * ζ W.P.A3.A.μ0 j) ^ (n₁ * n₂)
      rw [mul_pow, mul_pow, pow_mul (ζ tt j), e₁, mul_comm n₁ n₂, pow_mul (ζ W.P.A3.A.μ0 j), e₂, one_pow, one_pow]
    have hcI : ∀ tt j, j < (I.rec7 l Z).R.m → ((a.fam row col).t tt).cI j ≠ 0 := fun tt j hj =>
      GlobalTheory.Fam.GeoMeas.cIOf_ne_zero (_root_.GlobalTheory.Fam.complexLevelStructure W) ha.meas tt j hj
    have hci := fun tt => _root_.GlobalTheory.T.cI_mul_prod_idx_eq_cI_mu0 _ _ _ _ _ _ _ _ _ W u (a.fam row col) hW.pk (hRow col) a.v ha.vis (ha.tie row col).1 tt
      (w₀ tt) (F tt) (hCO.pins tt) (hCO.lev tt)
    have hq : ∀ tt j ρ, j + 2 * ρ + 2 = (I.rec7 l Z).R.m → (w tt).cQ j / (((a.fam row col).t tt).cI j * ((a.fam row col).t tt).cI (j + 1)) =
        (((a.fam row col).t W.P.A3.A.μ0).cI j * ((a.fam row col).t W.P.A3.A.μ0).cI (j + 1))⁻¹ := by
      intro tt j ρ h
      rw [(hCO.same tt).2.2.2.1, (hCO.pins tt).cQ j (by omega), ← hci tt j (by omega), ← hci tt (j + 1) (by omega),
        Finset.prod_inv_distrib, Finset.prod_mul_distrib, div_eq_mul_inv, ← mul_inv]
      congr 1
      ring
    have hct : ∀ tt j ρ, j + 2 * ρ + 2 = (I.rec7 l Z).R.m → UnitRatio (_root_.GlobalTheory.MiTop.qPrime_alt W tt) ((w tt).cT j) ((w W.P.A3.A.μ0).cT j) ∧
        UnitRatio (_root_.GlobalTheory.MiTop.qPrime_alt W tt) ((w tt).cQ j / (((a.fam row col).t tt).cI j * ((a.fam row col).t tt).cI (j + 1)))
          ((w W.P.A3.A.μ0).cQ j / (((a.fam row col).t W.P.A3.A.μ0).cI j * ((a.fam row col).t W.P.A3.A.μ0).cI (j + 1))) := by
      intro tt j ρ h
      refine ⟨?_, ?_⟩
      · rw [hCO.cT tt j ρ h, hCO.cT W.P.A3.A.μ0 j ρ h, ((hrow tt).sBF j ρ h).2.2.2, ((hrow W.P.A3.A.μ0).sBF j ρ h).2.2.2]
        exact GlobalTheory.SeeSaw.mono_unitRatio _ _ a.k a.ι a.o (r j) (e j) _ _ _ (hr j)
          ((_root_.GlobalTheory.T.root_of_unity_theta_twist_alt _ _ _ _ _ _ _ _ _ W u (a.fam row col) hW.pk (hRow col) tt).choose_spec.2.2.2 (j + 1))
      · rw [hq tt j ρ h, hq W.P.A3.A.μ0 j ρ h]
        exact (GlobalTheory.Fam.unitRatio_laws _).1 _ (inv_ne_zero (mul_ne_zero (hcI _ j (by omega)) (hcI _ (j + 1) (by omega))))
    obtain ⟨h1, -, h3⟩ := GlobalTheory.T.seeSaw_totalConstant_ratio_of_factor_ratios _ _ k.v W.P.T (a.fam row col).t w (_root_.GlobalTheory.MiTop.qPrime_alt W) W.P.A3.A.μ0 htIs hCO.cv hkap hcG hsc hct
      hCO.cP n hn t
    exact ⟨h1, h3⟩
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReductionSeriesB0
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
noncomputable section
namespace GlobalTheory.HeightCounting.Up.PointwiseSettings
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
open Formalism.L2.TwC in
theorem pointwise_alt_alt (hPr : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hSer : SerN) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) {K : Ctx} {B : Base}
    {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x)
    (G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩)
    (hF : GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x))) (hOk : (GlobalTheory.BigTop.Fun.lamOf G).Ok)
    (hC : (GlobalTheory.BigTop.Fun.lamOf G).C = cfOf x) (hq : (GlobalTheory.BigTop.Fun.lamOf G).q0 = AbsolutelyIrreducibleSpan.q0 (Dof x)) :
    ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevel hL x') ∧ ListSt cDep x' := by
  have hgal : GalEx (Dof x) :=
    _root_.GlobalTheory.HeightCounting.galEx_of_cgTrue_alt hL hPr.what₂.fin hPr.what₂.gal (Dof x) l.a.A.wdT ⟨l.a.cg⟩
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hPr.what₂.cheb (Dof x)
  obtain ⟨c0f, hf⟩ := _root_.GlobalTheory.T.row_cusp_multiplicity_input_alt hPr.what₂.art (Dof x) (cfOf x) l.a.jE l.a.A l.rat.S l.rat.In (lowAll (Dof x)) l.Pq
    l.mt.M _ (QOf P) l.mt.mt l.Pq_over hgal l.cusp hcheb l.a.elem.star l.a.elem.int l.a.elem.split
  have hJ := fun (p : ℕ) [Fact p.Prime] (v : HeightOneSpectrum (𝓞 ↥(Dof x).LL0))
      (hv : ((p : ℕ) : 𝓞 ↥(Dof x).LL0) ∈ v.asIdeal) => Formalism.BasicNotions.Examples₂.LB.exists_embAt (l := p) v hv
  obtain ⟨c0r, hr⟩ := GlobalTheory.T.exists_twistRings_characters_classGroups hPr.what₂.art (Dof x) (cfOf x) (fun p _ v hv => (hJ p v hv).choose)
    (fun p _ v hv y => (hJ p v hv).choose_spec y) l.a.val l.a.elem.star l.a.elem.int
  let b0 : Big (Dof x) := fun p _ j =>
    ⟨(c0f p j).1 ⊔ (c0r p j).1, by haveI := (c0f p j).2; haveI := (c0r p j).2; infer_instance⟩
  obtain ⟨Sx, hSx1, hSx2, hSx3⟩ := exists_Sx (Dof x)
  obtain ⟨T', Sp, -⟩ := hr b0 b0 Sx (fun p _ j => le_sup_right)
  have hSbSx : l.rat.In.Sb ⊆ Sx := l.rat.rat.Sb_le.subset hSx1
  obtain ⟨F, ex, h0, hfg, hsb⟩ := hf b0 b0 Sx T' Sp (fun p _ j => le_sup_left) hSbSx hSx3 hSx1
  have hSxS0 : ∀ i, ∀ Q ∈ Sx, Q ∈ T'.S0 i := fun i Q hQ => by
    have h := Sp.ringSpec_excludedPlaces_eq i
    have : Q ∈ (T'.S0 i : Set (HeightOneSpectrum (𝓞 (Dof x).host.E))) := by
      rw [h]; exact Or.inr (Finset.mem_coe.2 hQ)
    exact Finset.mem_coe.1 this
  have hratio : ∀ i, ∀ y ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)),
      ∀ z ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)), ‖y‖ ≤ ‖z‖ →
        y / z ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)) := fun i => by
    have h := GlobalTheory.CycClosure.exists_cyclotomic_integers (T'.l i) (Sp.K0 i) (Sp.Lw i) 0
    have h0 : Kt (T'.l i) (Sp.K0 i) (Sp.Lw i) ⊔ muK (T'.l i) 0 = Kt (T'.l i) (Sp.K0 i) (Sp.Lw i) := by
      rw [h.snd.2.2.2.2.1, sup_bot_eq]
    rw [h0] at h
    exact h.snd.2.2.2.1
  choose iC hiC using fun i => GlobalTheory.Mem.Df.exists_iC_of_clC (T'.l i) (T'.O i) _ (Sp.eO i) (hratio i)
  obtain ⟨L, hLam⟩ := GlobalTheory.T.exists_toricCharacters_in_twistCoefficientRings hPr.what₂.cheb hPr.what₂.art hSer.ratio (Dof x) l.a.A.bare (cfOf x) l.a.A.row
    (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL l.rat.In.eig l.rat.In.θ b0 b0 Sx T' Sp (GlobalTheory.BigTop.Fun.lamOf G) hC hOk
    (GlobalTheory.BigTop.Fun.lamOf_teich G) l.a.val (fun a => hF.values (a.1 + 1) (by omega) a.2)
    (fun i Q hQ => by
      obtain ⟨p, hp, hQp⟩ := GlobalTheory.T.conductor_primes_in_low_set (Dof x) _ hOk hq Q hQ
      exact hSxS0 i Q (Finset.mem_coe.1 (hSx1 p hp hQp)))
  obtain ⟨htie, hside⟩ := hLam F
  obtain ⟨th0⟩ := GlobalTheory.HeightCounting.exists_nth_of_fg_full (Dof x) (T'.ntw l.a.A.bare F (TwL.empty T')) ex
    (fun i => ⟨iC i, hiC i⟩) hfg
  obtain ⟨th1⟩ := GlobalTheory.HeightCounting.exists_nth_of_fg_full (Dof x) (T'.ntw l.a.A.bare F L) { ex with }
    (fun i => ⟨iC i, hiC i⟩) hfg
  have hB := hside ex h0 th0 (hsb th0) th1
  refine _root_.GlobalTheory.T.side_data_over_set_levels_alt hL cDep x l ⟨T'.ntw l.a.A.bare F L, { ex with }, h0, th1, Sp.br, Sp.br_ind⟩ hB
    (fun i => hSbSx.trans fun Q hQ => hSxS0 i Q hQ) (fun i Q hQ => ?_) G hF hOk hC hq htie
  have h := Sp.ringSpec_excludedPlaces_eq i
  have hQ' : Q ∈ (T'.S0 i : Set (HeightOneSpectrum (𝓞 (Dof x).host.E))) := Finset.mem_coe.2 hQ
  rw [h] at hQ'
  simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_coe] at hQ'
  rcases hQ' with (((h1 | ⟨k, h1⟩) | h1) | h1) | h1
  · exact ⟨_, Finset.mem_insert_self _ _, h1⟩
  · refine ⟨(Dof x).host.g k, Finset.mem_insert_of_mem ?_, h1⟩
    fin_cases k <;> simp [lowAll]
  · exact ⟨_, Finset.mem_insert_of_mem (by simp [lowAll]), h1⟩
  · exact ⟨_, Finset.mem_insert_of_mem (by simp [lowAll]), h1⟩
  · obtain ⟨p, hp, hQp⟩ := hSx2 Q h1
    exact ⟨p, Finset.mem_insert_of_mem hp, hQp⟩
theorem settings_forms_exist_list_of_published_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.SettingsFormsExistList' hL cDep := by
  intro hPr hSer hL cDep
  exact (_root_.GlobalTheory.T.exists_lam_grid_fieldHas_at_member hPr cDep).trans (StepW.of_all fun K B f T w _ _ h P x l => by
    obtain ⟨G, hF, hOk, hC, hq⟩ := h P x
    exact _root_.GlobalTheory.HeightCounting.Up.PointwiseSettings.pointwise_alt_alt hPr hSer hL cDep x l G hF hOk hC hq)
end GlobalTheory.HeightCounting.Up.PointwiseSettings
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.settingsFormsExistList_of_inputs_serN : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.SettingsFormsExistList' hL cDep := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.PointwiseSettings.settings_forms_exist_list_of_published_inputs | exact _root_.GlobalTheory.HeightCounting.Up.PointwiseSettings.settings_forms_exist_list_of_published_inputs | (intros; apply _root_.GlobalTheory.HeightCounting.Up.PointwiseSettings.settings_forms_exist_list_of_published_inputs <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SLarge
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
namespace GlobalTheory.CoefDuty
theorem large_of_large_rings_alt : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → _root_.GlobalTheory.CoefDuty.AutomorphicSideExists A M C tp.tup → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup (fun D' => (SumRepresentations.hypO D' → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D' ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D') ∧ GlobalTheory.BlockComplement.GaloisRepsCusp D') → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup Large := by
  intro hCheb D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh hEx hO
  have hStd : HeckeStdPlain := GlobalTheory.T.heckeDoubleCosetOperators_standardFacts
  have hConj := fun P₁ P₂ => (_root_.GlobalTheory.T.eventually_conjunction_mono_alt D cf jE A M C tp.tup P₁ P₂).1
  have hMono := fun P₁ P₂ => (_root_.GlobalTheory.T.eventually_conjunction_mono_alt D cf jE A M C tp.tup P₁ P₂).2.1
  have E1 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup SumRepresentations.hypO :=
    _root_.GlobalTheory.T.side_eigen_rationality_alt hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh
  have E2 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup GlobalTheory.SplitCoef.OSplit := by
    obtain ⟨big, hbig⟩ := _root_.GlobalTheory.T.side_multiplicity_cusp_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh
    refine ⟨big, fun L hB => ?_⟩
    obtain ⟨Sp, ⟨hA⟩, -⟩ := hB
    exact hbig L Sp hA
  have E3 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup (fun D' => ∀ i, ZDecomp D'.nd i) :=
    hMono _ _ (fun D' h => GlobalTheory.T.thetaLocusDecomposesOverCoefRing_of_chebotarev hCheb D' h.2) hO
  have E4 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup (fun D' => _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D' ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D') :=
    hMono _ _ (fun D' h => h.2.1 h.1) (hConj _ _ E1 hO)
  have E5 : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup TakenAll :=
    _root_.GlobalTheory.T.side_eigen_hecke_match_alt hCheb hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hStar hExp hSplit hCh hEx
      (hMono _ _ (fun D' h => ⟨h.1.1, h.2.1, h.2.2⟩) (hConj _ _ E4 (hConj _ _ E2 E3)))
  have EL : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup Large :=
    hMono _ _ (fun D' h => ⟨h.1, h.2.1, h.2.2⟩) (hConj _ _ E1 (hConj _ _ E2 E5))
  exact EL
end GlobalTheory.CoefDuty
end
namespace GlobalTheory.StEta
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
theorem sEta_alt_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PointStatement hL → _root_.GlobalTheory.HeightCounting.Up.EtaStatement' hL := by
  intro hP hL hPt
  refine ((((((hPt.and (_root_.GlobalTheory.T.eventually_etaJ_eq_eta_of_levelC hP hL hPt)).and (_root_.GlobalTheory.T.star_mem_LL0_at_level_c hP hL)).and (_root_.GlobalTheory.T.eExp_integer_of_levelC hP hL)).and (_root_.GlobalTheory.T.places_over_pde_isSplitPl_of_levelC hP hL)).and (_root_.GlobalTheory.T.chebSplit_of_published_inputs_at_level_c hP hL)).and
    (_root_.GlobalTheory.T.eventually_galoisRepsCusp_of_level_c hP hL)).trans (StepW.of_all ?_)
  intro K B f T w _ _ H P x l hB
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, hst⟩, hex⟩, hsp⟩, hch⟩, h4⟩ := H
  have law := fun P₁ P₂ => _root_.GlobalTheory.CoefDuty.LargeRing.evO_laws_alt (Dof x) (cfOf x) l.a.jE l.a.A l.mt.M l.c.ch l.c.tp.tup P₁ P₂
  have hin : _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' =>
      (SumRepresentations.hypO D' → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D' ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D') ∧ GlobalTheory.BlockComplement.GaloisRepsCusp D' :=
    (law _ _).1 ((law _ _).2.1 (fun D' h hO => ⟨(h.1 hO).1, (h.1 hO).2.1⟩) (h1 P x l)) (h4 P x l)
  have hMt : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
    show MtInput (Dof x) l.mt.M (fun μ j => (cfOf x).mu0 j * l.c.tp.xi μ) l.c.ch.Q
    rw [l.c.xi_eq, l.c.Q_eq]; exact l.mt.mt
  have hm := (_root_.GlobalTheory.CoefDuty.large_of_large_rings_alt hP.cheb (Dof x) (cfOf x) l.a.jE l.a.A (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL l.rat.In.eig
    l.rat.In.θ l.b.Bs l.mt.M l.c.ch l.c.tp l.c.side hMt (hst P x l) (hex P x l) (hsp P x l) (hch P x l) hB hin)
  refine (law _ _).2.1 ?_ ((law _ _).1 hm (h2 P x l))
  intro D' h
  have hO : SumRepresentations.hypO D' := by have h' := h.1; unfold GlobalTheory.CoefDuty.Large at h'; exact h'.1
  exact ⟨h.1, h.2 hO⟩
end GlobalTheory.StEta
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SRatOfIsotInternal
section
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
  GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000
namespace GlobalTheory.HeightCounting.RatSide
theorem sRat_of_isotInternal_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → (AllSt fun _ _ _ _ _ _ x => Formalism.BasicNotions.Rows.IsotInternal (Dof x).what₂) →
    ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL := by
  intro hp hs hi hL
  have A := StepW.and (_root_.GlobalTheory.HeightCounting.RatSide.formsC_at_state_alt hL) (StepW.and (_root_.GlobalTheory.HeightCounting.ThetaSt.main_alt_alt hL)
    (StepW.and (_root_.GlobalTheory.HeightCounting.RatSide.HeckeAtState.heckeAtState_alt hL hp.decay hs.hkTr hs.hkRead)
    (StepW.and (_root_.GlobalTheory.T.intC_state_of_lvlPsi_stabC_heckeRd hL hp.decay hs.hkInt hs.hkTr hs.hkRead) (_root_.GlobalTheory.HeightCounting.RatSide.eigenspace_span_of_isotypicInternal_alt hp hi hL))))
  refine StepW.trans A (StepW.of_all fun K B f T w _ _ H => ?_)
  intro P x hx
  obtain ⟨hF, hθ, hH, hI, hE⟩ := H
  obtain ⟨θ, θne, hlp⟩ := hθ P x hx
  obtain ⟨hL', hst, h0, hrd⟩ := hH P x hx
  obtain ⟨eig, hea, hsp⟩ := hE P x hx θ hL' θne hlp hst h0 hrd
  have hint := hI P x hx θ hL' hlp hst hrd
  have hrc := GlobalTheory.Mem.RatDatRExp.rhoStab_chiInLL0 (Dof x) _ _ _ _ _ x.m.z.core x.m.z.R x.m.z.F x.m.z.cG x.m.z.geo (kKsOf x)
    (hkOf x) x.m.z.pins x.m.inGeo
  exact ⟨⟨kKsOf x, hkOf x,
    { Sb := SbD (Dof x)
      rho := fun j a b => (hrc j a b).1
      chi := fun j a b => (hrc j a b).2
      ks := fun j a b => (hF P x hx j a b).1
      fd := fun j a b => (hF P x hx j a b).2.1
      mk_fg := fun j a b => (hF P x hx j a b).2.2
      hL := hL'
      hs := hst
      hL_zero := h0
      θ := θ
      θ_ne := θne
      eig := eig
      span := hsp
      hL_int := hint },
    { hecke := hrd
      eig := hea
      Sb_le := overSet_SbD _
      lvl := hlp.1
      psi := hlp.2 }⟩⟩
theorem sRat_of_isotInternal_inputs : GlobalTheory.Published.DiscreteSeriesUpqUnique → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN →
    (AllSt fun _ _ _ _ _ _ x => Formalism.BasicNotions.Rows.IsotInternal (Dof x).what₂) →
    ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL :=
  fun _ => _root_.GlobalTheory.HeightCounting.RatSide.sRat_of_isotInternal_alt_alt
end GlobalTheory.HeightCounting.RatSide
end
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SecondBoundOfPrimitive
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up.SeriesStep
open GlobalTheory.Mem.R3.Tr
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
theorem sb1l_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.SeriesExistList' hL cDep := by
  intro hPr hSer hL cDep
  refine (StepW.and (_root_.GlobalTheory.MtId.exists_matrix_input_identity_frame_of_inputs hPr) (StepW.of_all fun _ _ _ _ _ _ _ h => h)).trans
    (StepW.of_all fun K B f T w hK hF H P x l => ?_)
  obtain ⟨N, hN, hser⟩ := _root_.GlobalTheory.T.series_copy_embedding_of_cmDatum_alt hPr hSer hL hK hF H.2 x l
  obtain ⟨x', l', ho, hLc, hrow, hPq, hS, hSb, hhL, heig, hθ, hR, hcG, hgeo⟩ := _root_.GlobalTheory.T.twisted_state_transport_heq_levels' hL x l.toLI N
  obtain ⟨m, hm⟩ := H.1 P x'
  obtain ⟨b⟩ := hser x' l' ho hrow hPq hS hSb hhL heig hθ hR hcG hgeo m hm
  exact ⟨x', ⟨{ toLI := { l' with mt := m }, b := b }⟩, listSt_oTw cDep x N hN x' ho hLc⟩
end GlobalTheory.HeightCounting.Up.SeriesStep
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seriesExistList_of_inputs_serN : (_root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.SeriesExistList' hL cDep) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.SeriesStep.sb1l_alt_alt | exact _root_.GlobalTheory.HeightCounting.Up.SeriesStep.sb1l_alt_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.SeriesStep.sb1l_alt_alt <;> assumption)
end
end
end

