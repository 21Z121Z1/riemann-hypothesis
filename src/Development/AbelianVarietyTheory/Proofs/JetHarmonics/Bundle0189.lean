import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0187
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Development.AutomorphicArithmetic.CMTraceForms.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0188
import Formalism.HermitianCurvature.Bundle0007
import Formalism.HermitianCurvature.Bundle0004
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolyLiftConjLastMinorMulRadialPairTerm
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Formalism.LocalToGlobal.CharacterGerms.Bundle0009
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0065
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0069
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetAt0ProdRename
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0082
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CartHypOfFormalBiextension
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0064
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SubstOneVariableUncurryEqSubst
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0131
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0139
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0151
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0137
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0143
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0136
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0022
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0180
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0124
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0141
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0146
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0145
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0144
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0182
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ContractionMapsAtRepresentatives
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0039
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0113

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilyFunctionalSpanDualStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jN2_eq_const_mul_formal_degree_of_supG : Hyps → ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq) (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ) (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ), Num P.k P.r lam P.u b bv ga h q0 → Sup p lam q0 R l l' dg s J tau → ∃ c : ℝ, 0 < c ∧ ∀ ν, n1 ν ≤ q0 → (J ν = 0 ∧ TBB.jN2 p (J ν) = 0 ∧ ¬ (NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν))) ∨ (J ν ≠ 0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν) ∧ s ν ≠ 0 ∧ TBB.jN2 p (J ν) = ENNReal.ofReal (c * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)))) := by
  first | exact @GlobalTheory.SuppliedNorm.sup_norm | exact GlobalTheory.SuppliedNorm.sup_norm | (intros; apply GlobalTheory.SuppliedNorm.sup_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDepthLeResidueCharTwoStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralChartDepth_le_residueChar_two : ∀ (p : ℕ) [Fact p.Prime], AvFSt p → HTFSt p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), y.IsAlg → ¬ IsUnit ((p : ℕ) : T.V) → UpperTheory.Depth.SplitAt H.d p → ∀ (f : ℕ) (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitPlaces p H f vd → ∀ (e k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < e → DomW Dw a → Fintype.card (Lt1 Dw) ≤ n → ∀ Ap : ℝ, 0 ≤ Ap → (∀ τ, InPsi H τ → (a (τ, 0) : ℝ) ≤ Ap) → (open Classical in nuLocC Ch e k a n ≤ (((vV T.V ((p : ℕ) : T.Fr) : ℝ) / (e : ℝ) * ((f : ℝ) * Dw.q * (1 + vd / 2) * Ap + Dw.q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi H τ), (a (τ, 0) : ℝ)) : ℝ) : EReal)) := by
  first | exact @GlobalTheory.CharDepth.nuLocC_le_over_two | exact GlobalTheory.CharDepth.nuLocC_le_over_two | (intros; apply GlobalTheory.CharDepth.nuLocC_le_over_two <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormDiagonalBigCellImEqZeroStatement
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelZeroForm_diagonal_bigCell_im_eq_zero : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CutWord P p.l0 w → (p.RR H 0 w [] []).im = 0 := by
  first | exact @GlobalTheory.LevelFormsReal.levelZero_im_eq_zero | exact GlobalTheory.LevelFormsReal.levelZero_im_eq_zero | (intros; apply GlobalTheory.LevelFormsReal.levelZero_im_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolyLiftConjLastMinorMulRadialPairTermStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyLift_conjLastMinor_mul_radialPairTerm : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ y : ℝ, PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) (rh d y) := by
  first | exact @GlobalTheory.HatNF.LiftR.polyLift_rh | exact GlobalTheory.HatNF.LiftR.polyLift_rh | (intros; apply GlobalTheory.HatNF.LiftR.polyLift_rh <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RowDataSuppliedAtPairsOfPlaces
section
set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

theorem supply_pairs : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (Orb : Type) [Fintype Orb] (d : ℕ) [NeZero d] (lab : Lab E Orb d), LabArith V io ι lab → Function.Surjective (fun x : Orb × Fin 2 × ZMod d => lab.tau x.1 x.2.1 x.2.2) → lab.RankOK Dw → lab.j' < lab.n → (∀ o, (Even d ∧ ∀ s : ZMod d, (lab.big o 0 s ↔ Even s.val)) ∨ ∀ s, lab.big o 0 s) → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ (nW : ℕ) (ν : ℝ), (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW → Supply V d Orb Finset.univ lab.n (lab.j + lab.j') lab.big (fun o g s => Dw.mult (lab.tau o g s)) (fun o g s => gap (Dw.mult (lab.tau o g s)) fun i => a (lab.tau o g s, i)) nW ν := by
  intro hUp E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY hy hl Orb _ d _ lab ha hsurj hr hj hdich a hdom nW ν hν
  have hg : LabGeo C3 ι Y lab :=
    GlobalTheory.LabelledDirections.labGeoSt E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb d lab ha
  have hnd : NDG Y := GlobalTheory.T.biextension_nondegenerate_mod_maximalIdeal_integral_chart E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY
  have Hy : ∀ o, (Y.raw (pairOfLab ha hg o)).Hyps V := fun o =>
    FBChart.hyps GlobalTheory.cartHyp_of_formalBiextension axesFB GlobalTheory.RowLaw.germs_deriv_kernel_of_formal.1 GlobalTheory.RowLaw.germs_deriv_kernel_of_formal.2.1 GlobalTheory.RowLaw.germs_deriv_kernel_of_formal.2.2 Y (pairOfLab ha hg o)
      (rankHyp_ofLab ha hg hr o)
      (GlobalTheory.T.nonDeg_raw_pairData_and_rankMaximal.2 C V (𝓞 E) _ Y d _ (pairOfLab ha hg o) hnd (rankHyp_ofLab ha hg hr o) _)
      (GlobalTheory.T.characterBound_pairs_of_places_integralChart hUp E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY hy hl Orb d lab ha hg hr o _)
  have hfl := fun o => GlobalTheory.flag_of_numbering C V d (fun _ => ZMod d) (fun g s => Dw.mult (lab.tau o g s))
    (fun _ => Equiv.refl _) (JJ (lab.II Dw o)) (RF.rd Y (pairOfLab ha hg) Hy o) (fun _ _ => rfl)
  have hrk : ∀ o g s, (RF.rd Y (pairOfLab ha hg) Hy o).rkF g s = Dw.mult (lab.tau o g s) := fun o => (hfl o).1
  choose F hF using fun o => (hfl o).2
  refine ⟨fun o => lab.II Dw o, fun o => JJ (lab.II Dw o), inferInstance, inferInstance,
    fun o => RF.rd Y (pairOfLab ha hg) Hy o, F, fun o => ⟨rfl, rfl⟩, fun o _ g s => ⟨Iff.rfl, hrk o g s⟩, ?_⟩
  refine RF.valBlocks_of_nuPlE Y (pairOfLab ha hg) Hy (chartLetterSystem C3 V ι a) nW F Finset.univ _ ν
    (hν.trans (GlobalTheory.nuLocC_le_nuPlE_baseChange E H Dw lv Xo c T io y C3 C V ι hι k Y hY a nW))
    (pairsSep_ofLab ha hg) (GlobalTheory.RowVal.value_eq_prod C V (𝓞 E) _ Y d Orb _ (pairOfLab ha hg) Hy _ nW) GlobalTheory.JetProd.jetProd
    (GlobalTheory.T.blockProd_mem_chartFamily_at_place_pairs E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb d lab ha hg hsurj hr hj Hy F
      (fun o g s q => (hF o g s q).2) a hdom nW) ?_
  refine RF.blkAdm _ F Finset.univ _ (fun o _ => hdich o) (fun _ _ => hj) fun o _ g s q hq => ?_
  rw [hrk]
  by_contra hc
  exact hq (by unfold gap; rw [if_neg fun h => hc h.2])

end GlobalTheory.RowAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RowDataSuppliedAtSelfConjugatePlaces
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

def pairCols (n : ℕ) : Fin (n / 2) × Fin 2 ↪ Fin n where
  toFun x := ⟨2 * x.1.val + x.2.val, by have := x.1.2; have := x.2.2; omega⟩
  inj' := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : 2 * a.val + b.val = 2 * a'.val + b'.val := congrArg Fin.val h
    have := b.2
    have := b'.2
    exact Prod.ext (Fin.ext (by simp only; omega)) (Fin.ext (by simp only; omega))

def tyShift (g : Fin 2) : ZMod 2 ≃ ZMod 2 := if g = 0 then Equiv.refl _ else Equiv.addRight 1

theorem supplyC_selfConj : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], (∀ x : 𝓞 E, star x = H.bar x) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y → y.IsAlg → ∀ (Orb : Type) [Fintype Orb] (lab : LabS E Orb), ArithS V io ι lab → Function.Surjective (fun x : Orb × ZMod 2 => lab.tau x.1 x.2) → lab.RankOK Dw → lab.j' < lab.n → ∀ (a : (E →+* ℂ) × ℕ → ℕ), DomW Dw a → ∀ (nW : ℕ) (ν : ℝ), (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW → SupplyC V Orb lab.n (lab.j + lab.j') (fun o s => Dw.mult (lab.tau o s)) (fun o s => gap (Dw.mult (lab.tau o s)) fun i => a (lab.tau o s, i)) nW ν := by
  intro hUp E _ _ _ H Dw lv Xo c _ hstar T io y C3 C _ _ V ι hι k Y hY halg Orb _ lab ha hsurj hr hj a hdom nW ν hν
  obtain ⟨p, hp, hsep, hrk⟩ := GlobalTheory.T.exists_selfConjugatePlaceData_intChart E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb lab ha
  obtain ⟨hCart, hAx, hG0, hC, hR1⟩ := GlobalTheory.T.rowLaw_formal_statements_selfConjugate
  have hndg : NDG Y := GlobalTheory.T.biextension_nondegenerate_mod_maximalIdeal_integral_chart E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY
  have Hy : ∀ o, (Y.rawSelf (p o)).Hyps V := fun o =>
    { charZero := inferInstance
      algClosed := Y.algClosed
      l_odd := Y.l_odd
      k_unit := Y.k_unit
      cartH := hCart C V (𝓞 E) _ Y 2 _ (p o)
      rank := (hrk hr o).1
      axes := hAx C V (𝓞 E) _ Y 2 _ (p o)
      G0 := hG0 C V (𝓞 E) _ Y 2 _ (p o) _
      CEq := hC C V (𝓞 E) _ Y 2 _ (p o) (hrk hr o).1 _
      R1 := hR1 C V (𝓞 E) _ Y 2 _ (p o) (hrk hr o).1 _
        (GlobalTheory.T.rankMaximal_rawSelf_of_ndg C V (𝓞 E) _ Y 2 _ (p o) hndg _)
      R2 := GlobalTheory.T.rankMaximal_rawSelf_of_ndg C V (𝓞 E) _ Y 2 _ (p o) hndg _
      CH := GlobalTheory.T.characterBound_selfConjugate_degreeTwo_integralChart hUp E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY halg Orb lab ha hr p hp o _ }
  have hfl := fun o => GlobalTheory.T.flag_of_letterNumbering_rowData C V 2 (fun _ => ZMod 2) (fun _ s => Dw.mult (lab.tau o s)) tyShift
    (JJ fun _ => lab.II Dw o) ((Y.rawSelf (p o)).rowData (Hy o)) (by
      intro g x
      show (if g = 0 then (p o).ty0 x else (p o).ty0 x + (p o).hd) = _
      rw [hp.ty0, hp.hd]
      unfold tyShift
      split_ifs <;> rfl)
  have hrkF : ∀ o s, ((Y.rawSelf (p o)).rowData (Hy o)).rkF 0 s = Dw.mult (lab.tau o s) :=
    fun o s => (hfl o).1 0 s
  choose F hF using fun o => (hfl o).2
  refine ⟨fun o _ => lab.II Dw o, fun o => JJ fun _ => lab.II Dw o, inferInstance, inferInstance,
    fun o => (Y.rawSelf (p o)).rowData (Hy o), F, fun o => ⟨hp.n o, ?_, (hrk hr o).2, hrkF o⟩, ?_⟩
  · show (p o).j + (p o).j' = _
    rw [hp.j, hp.j']
  · refine RF.valBlocksC_G (n := nW / 2)
      (GlobalTheory.T.chartValues_bound_products_on_planes C V (𝓞 E) _ Y 2 Orb _ p Hy (chartLetterSystem C3 V ι a) (nW / 2) nW (pairCols nW) ν hsep
        (hν.trans (GlobalTheory.nuLocC_le_nuPlE_baseChange E H Dw lv Xo c T io y C3 C V ι hι k Y hY a nW)))
      GlobalTheory.JetProd.jetProd F nW (by omega) _
      (GlobalTheory.T.blockProd_mem_at_selfConj_places E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY Orb lab ha hsurj hr hj p hp Hy F
        (fun o g s q => (hF o g s q).2) a hdom (nW / 2) nW (pairCols nW)) ?_
    refine RF.blkAdmC _ F _ (fun o => (hrk hr o).2) (fun o => ?_) (fun o s k' hk => ?_)
    · show (p o).j' < (p o).n
      rw [hp.j', hp.n]
      exact hj
    · rw [hrkF]
      by_contra hlt
      apply hk
      unfold gap
      rw [if_neg (fun h => hlt h.2)]

end GlobalTheory.RowAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaLatticeDepthLeAtPlacesOverLevel
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.DepthOverLevel

theorem lattice_terms_le (R N φ Φ e n n₁ r Dg g c : ℝ) (hR : 0 < R) (hN : 0 < N) (he : 0 < e) (hΦ : 0 ≤ Φ)
    (hΦe : Φ ≤ e * (R * N ^ 3 * φ)) (hn0 : 0 ≤ n₁) (hn : n₁ ≤ n) (hr0 : 0 ≤ r) (hr : r ≤ N) (hD : 1 ≤ Dg) (hg : 0 < g)
    (hc : R * (N ^ 4 * n + 2 * N ^ 3) * Dg ^ 2 / g ≤ c) :
    (n₁ * r * Φ / (4 * g) + 2 * Dg ^ 2 * Φ / g) / e ≤ c * φ := by
  have hφ : 0 ≤ φ := by
    have h1 : 0 ≤ (e * (R * N ^ 3)) * φ := by linarith
    exact nonneg_of_mul_nonneg_right h1 (by positivity)
  have hD2 : 1 ≤ Dg ^ 2 := one_le_pow₀ hD
  have hn' : 0 ≤ n := hn0.trans hn
  have h1 : n₁ * r / 4 ≤ n * N * Dg ^ 2 := by
    have h2 : n₁ * r ≤ n * N := mul_le_mul hn hr hr0 hn'
    have h3 : n * N * 1 ≤ n * N * Dg ^ 2 := mul_le_mul_of_nonneg_left hD2 (by positivity)
    have h4 : 0 ≤ n₁ * r := by positivity
    linarith
  calc (n₁ * r * Φ / (4 * g) + 2 * Dg ^ 2 * Φ / g) / e = (n₁ * r / 4 + 2 * Dg ^ 2) * Φ / g / e := by
        field_simp
    _ ≤ (n * N * Dg ^ 2 + 2 * Dg ^ 2) * (e * (R * N ^ 3 * φ)) / g / e := by gcongr
    _ = R * (N ^ 4 * n + 2 * N ^ 3) * Dg ^ 2 / g * φ := by field_simp
    _ ≤ c * φ := by gcongr

theorem not_isUnit_of_vV_ne_zero (S : CDVR) (N : ℕ) (h : vV S.V ((N : ℕ) : S.Fr) ≠ 0) : ¬ IsUnit ((N : ℕ) : S.V) := by
  intro hu
  apply h
  have h2 : valV S.V (algebraMap S.V S.Fr ((N : ℕ) : S.V)) = 1 := by
    unfold valV
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (mem_nonunits_iff.1 h) hu
  rw [map_natCast] at h2
  unfold vV
  rw [h2]
  simp

theorem vLa_sWt {D : D7} {j : ℕ} (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (w : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO)) (i : Fin 2) (hg : ((D.host.g i : ℕ) : 𝓞 B.KO) ∈ la.asIdeal) :
    sWt B hinj EX w ≠ 0 ∧ ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) ≠ 0 ∧
      vLa la ((sWt B hinj EX w : 𝓞 B.KO) : B.KO) = vLa la ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) := by
  have hq : D.host.q.Prime := D.host.hyp.1
  have hd : D.host.d.Prime := D.host.hyp.2.1
  have hq8 : D.host.q % 8 = 3 := D.host.hyp.2.2.1
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hnd : ¬ D.host.g i ∣ D.host.condN := fun h => by
    have hc : D.host.g i % D.host.condN = 1 := D.ntypes.g_cond i
    have h1 := Nat.mod_mod_of_dvd (D.host.g i) h
    rw [hc, Nat.mod_self, Nat.mod_eq_of_lt (D.host.g_prime i).one_lt] at h1
    exact one_ne_zero h1
  have hl : resCharOf la = D.host.g i := (RPfVal.prime_mem_iff la (D.host.g_prime i)).1 hg
  have hnn : nnW B hinj EX w ≠ 0 := by
    have hπ : ∀ k, iE D hinj B (EX.piG k) ≠ 0 ∧ iE D hinj B (piBarO EX k) ≠ 0 := by
      intro k
      rw [← mul_ne_zero_iff, ← map_mul, RPfVal.piG_mul_bar, map_natCast]
      exact Nat.cast_ne_zero.2 (D.host.g_prime k).ne_zero
    exact Finset.prod_ne_zero_iff.2 fun k _ => mul_ne_zero (pow_ne_zero _ (hπ k).1) (pow_ne_zero _ (hπ k).2)
  have hnn0 : ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) ≠ 0 := fun h =>
    hnn (NumberField.RingOfIntegers.coe_eq_zero_iff.1 h)
  have hP : pPow D (c2 D w) (cHalf w) (cHalf w) = D.host.QS ^ c2 D w * D.host.q ^ cHalf w * D.host.d ^ cHalf w := rfl
  have hN : pPow D (c2 D w) (cHalf w) (cHalf w) ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ hq.ne_zero))
      (pow_ne_zero _ hd.ne_zero)
  refine ⟨mul_ne_zero hnn (Nat.cast_ne_zero.2 hN), hnn0, ?_⟩
  have hc : ((sWt B hinj EX w : 𝓞 B.KO) : B.KO) =
      ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) * ((pPow D (c2 D w) (cHalf w) (cHalf w) : ℕ) : B.KO) := by
    show algebraMap (𝓞 B.KO) B.KO (_ * _) = _
    rw [map_mul, map_natCast]
  rw [hc, Crude.crv_vLa_mul la hnn0 (Nat.cast_ne_zero.2 hN), hP, RPfVal.vLa_pPow la D.host.QS_pos.ne' hq hd, hl,
    padicValNat.eq_zero_of_not_dvd (fun h => hnd (h.trans D.host.QS_dvd_condN)),
    if_neg (D.host.ne_q_of_not_dvd hnd), if_neg (D.host.ne_d_of_not_dvd hnd)]
  simp

theorem nusOf_of_mem {D : D7} {j : ℕ} (B : WeightFamilies.Prov D) (w : WeightFamilies.Wt D j) (nu : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (la : HeightOneSpectrum (𝓞 B.KO)) (i : Fin 2) (hg : ((D.host.g i : ℕ) : 𝓞 B.KO) ∈ la.asIdeal) :
    nusOf B w nu la = (ramOverZ la : ℝ) * (WeightAlgebra.DF w : ℝ) / ((D.host.g i : ℝ) - 1) := by
  have h : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 B.KO) ∈ la.asIdeal := ⟨i, hg⟩
  have h1 : D.host.g (Classical.choose h) = D.host.g i :=
    ((RPfVal.prime_mem_iff la (D.host.g_prime _)).1 (Classical.choose_spec h)).symm.trans
      ((RPfVal.prime_mem_iff la (D.host.g_prime i)).1 hg)
  unfold nusOf
  rw [dif_pos h, h1, H1algLink.eWL_eq]

theorem wtA_antitone {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (τ : D.host.E →+* ℂ) : Antitone fun i => wtA w (τ, i) := by
  intro i i' hii
  unfold wtA
  refine Finset.sum_le_sum fun t _ => add_le_add ?_ ?_
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aPlus_antitone t) hii
    · exact le_rfl
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aM_anti t) hii
    · exact le_rfl

theorem depth_le_over_level : (∀ (p : ℕ) [Fact p.Prime], Pdiv.ChartF.HTFSt p) → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (c : ℝ), Oriented T EX → RunNum D w c → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (i : Fin 2), ((D.host.g i : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal → ∀ y : T.PtA j la, (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤ ((nusOf (recB h.toLawsCore) w (nuWt T w) la + c * (recPJ h j hj).phiC la y : ℝ) : EReal) := by
  intro hHT D T h j hj hinj EX w c hO hR la i hg y
  letI := T.Q.H.starRing
  obtain ⟨hlast, hn, hDg, hc0, hc⟩ := hR
  obtain ⟨S, io, e, ho, z, hz, hl, C, Pu, hC, hPu, hval⟩ := GlobalTheory.T.exists_uniformisedModel_integralChart_at_point D T h j hj la y
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.V
  obtain ⟨⟨Q, hQ⟩, -⟩ := GlobalTheory.PowData.exists_powData _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S io z C Pu ϖ hϖ
  obtain ⟨r, Φ, M0, ⟨hΦ, b, hb1, hb2⟩, hr, hM0, hjm, hΦe⟩ :=
    GlobalTheory.ShortBasisAt.exists_shortBasis D T h j hj la S io e ho z hz (imgV y) hl C Pu ϖ hϖ Q hQ
  have hphi : (recPJ h j hj).phiC la (PtV.mk la ho z hz (imgV y) hl) = (recPJ h j hj).phiC la y := rfl
  rw [hphi] at hΦe
  have hM := h.toLawsCore.toLawsM
  obtain ⟨hDF, -, hpos, -, -, hf1, hr1, hrank⟩ := GlobalTheory.WeightOnDatum.weight_on_datum D T.toCore hM.pins j hj w
  have hD1 := (hpos hlast).2
  have hpq := ((GlobalTheory.PinNum.numerics_of_pins D T.Q hM.pins).2.2.2.2.2.2 j hj).1
  obtain ⟨-, hst, hMb, -⟩ := GlobalTheory.HalfGen.half_principal_and_split D T.toCore hM EX
  have hMb := hMb hO
  have hnab : IsNab (T.Q.Xo j) T.Q.c (T.nab j) := by
    obtain ⟨st, hn⟩ := h.nabPin j hj
    have := GlobalTheory.PowGerm.starSt _ T.Q.H st hn.1
    subst this
    exact hn
  obtain ⟨i', hne, hMg, hMb', hα⟩ : ∃ i' : Fin 2, D.host.g i ≠ D.host.g i' ∧ T.Q.l.M = D.host.g i' * D.host.g i ∧
      T.Q.l.Mb = Ideal.span {piBarO EX i * piBarO EX i'} ∧
      star (piBarO EX i) * star (piBarO EX i') = EX.piG 0 * EX.piG 1 := by
    have hs : ∀ k, star (piBarO EX k) = EX.piG k := fun k => by rw [← (hst k).1, star_star]
    have hLM := level_M T.toCore hM
    fin_cases i
    · exact ⟨1, D.host.g_ne, hLM.trans (mul_comm _ _), hMb, by rw [hs, hs]; rfl⟩
    · exact ⟨0, D.host.g_ne.symm, hLM, by rw [hMb, mul_comm]; rfl, by rw [hs, hs, mul_comm]; rfl⟩
  have hres : resCharOf la = D.host.g i := (RPfVal.prime_mem_iff la (D.host.g_prime i)).1 hg
  have hvg : vV S.V ((D.host.g i : ℕ) : S.Fr) = (e : ℤ) * ramOverZ la := by
    rw [← map_natCast io, ho.2, ← hres, Crude.crv_vLa_char]
  have hnu : ¬ IsUnit ((D.host.g i : ℕ) : S.V) := by
    refine not_isUnit_of_vV_ne_zero S _ ?_
    rw [hvg]
    exact mul_ne_zero (Nat.cast_ne_zero.2 ho.1.ne') (Nat.cast_ne_zero.2 (H1algLink.ramOverZ_ne_zero la))
  have hsp := GlobalTheory.LevelSplit.splitsIn_level_prime D i
  have hg' : (0 : ℝ) < D.host.g i' := by exact_mod_cast (D.host.g_prime i').pos
  have he : (0 : ℝ) < e := by exact_mod_cast ho.1
  have hnr : 2 * D.R.r ≤ w.n := le_trans (by nlinarith) hn
  have hDM : (WeightAlgebra.DF w : ℝ) * M0 < D.host.g i' := by
    by_cases hlt : j < D.R.m
    · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hM0 (Nat.cast_nonneg _)) (hc hlt i').1
    · rw [(hjm (not_lt.1 hlt)).1, mul_zero]; exact hg'
  have hA := GlobalTheory.T.theta_generators_least_value_over_level_prime hHT _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c (T.nab j) hnab (h.thTot j hj) S io z C hC
    Pu hPu hz ϖ hϖ Q hQ Φ M0 r b hΦ hb1 hb2 (D.host.g i) (D.host.g i') (D.host.g_prime i) (D.host.g_prime i') hne hMg
    (piBarO EX i) (piBarO EX i') (hst i).2 (hst i').2 hMb' hsp.1 hsp.2 hnu (wtA w) w.n e
    (wtA_antitone w) (by rw [hpq]; exact hnr) (by omega) ho.1
    (by rw [hDF]; have := hDg i; omega) (by rw [hDF]; exact hDg i') (by rw [hDF]; exact hDM)
  obtain ⟨hs0, hnn0, hsv⟩ := vLa_sWt (recB h.toLawsCore) hinj EX w la i hg
  have hN : nval S.V e (∏ τ : D.host.E →+* ℂ, (io (embK T.Q.c τ (star (piBarO EX i) * star (piBarO EX i')))) ^
      (∑ k : Fin ((T.Q.Dw j).mult τ), wtA w (τ, k))) =
      (((vLa la ((sWt (recB h.toLawsCore) hinj EX w : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ) : EReal) := by
    have h1 : (∏ τ : D.host.E →+* ℂ, (io (embK T.Q.c τ (star (piBarO EX i) * star (piBarO EX i')))) ^
        (∑ k : Fin ((T.Q.Dw j).mult τ), wtA w (τ, k))) =
        io ((nnW (recB h.toLawsCore) hinj EX w : 𝓞 T.Q.c.F) : T.Q.c.F) := by
      rw [← GlobalTheory.PtTie.nrm_eq_nnW D T h j hj hinj EX w, hα]
      unfold nrm
      simp only [map_prod, map_pow]
    rw [h1, nval_of_ne ((map_ne_zero io).2 hnn0), ho.2]
    refine congrArg (fun x : ℝ => (x : EReal)) ?_
    rw [Int.cast_mul, Int.cast_natCast, mul_div_cancel_left₀ _ he.ne']
    exact congrArg (fun x : ℤ => (x : ℝ)) hsv.symm
  rw [hN, hDF, hpq, hvg] at hA
  have hdep : (recPJ h j hj).depth (sWt (recB h.toLawsCore) hinj EX w) w la y ≤
      (⨅ f ∈ T.th j w, nval S.V e (evI z f)) +
        (((vLa la ((sWt (recB h.toLawsCore) hinj EX w : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ) : EReal) := by
    rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    refine le_iInf₂ fun f hf => ?_
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← hval w f hf, add_comm]
    exact GlobalTheory.DepthRule.depth_le_scaled_value D T h j hj w hlast _ hs0 la y f hf
  refine hdep.trans (le_trans hA (EReal.coe_le_coe_iff.2 ?_))
  rw [nusOf_of_mem (recB h.toLawsCore) w _ la i hg, add_assoc, add_div]
  refine add_le_add (le_of_eq ?_) ?_
  · push_cast
    rw [mul_assoc, mul_div_assoc, mul_div_cancel_left₀ _ he.ne']
  · by_cases hlt : j < D.R.m
    · have hm := D.R.two_le_m
      have hf' : (0 : ℝ) < D.R.f := by exact_mod_cast hf1
      have hm' : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
      refine lattice_terms_le (rr0 D) (2 * D.R.f * D.R.m) _ Φ e w.n _ r _ _ c ?_ (by positivity) he hΦ hΦe
        (Nat.cast_nonneg _) (by exact_mod_cast (by omega : D.R.r ≤ w.n)) (Nat.cast_nonneg _) (by exact_mod_cast hr)
        (by exact_mod_cast hD1) hg' (hc hlt i').2
      unfold rr0
      have hd : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
        abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero _))
      have hk : (0 : ℝ) < Module.finrank ℚ D.host.E := by exact_mod_cast Module.finrank_pos
      positivity
    · have h0 : (recPJ h j hj).phiC la y = 0 := by
        unfold WeightAlgebra.PJ.phiC
        rw [if_neg hlt]
      rw [h0, (hjm (not_lt.1 hlt)).2]
      simp

end GlobalTheory.DepthOverLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerMapsThreePlacesExists
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutBP2

namespace GlobalTheory.WigSh

theorem par_gap_right (P : M.Par) (hP : P.OK) :
    ∀ i ∈ Finset.Icc 1 (P.k - 1), ∃ N : ℕ, P.u' i - P.u' (i + 1) = (N : ℝ) + 1 := by
  intro i hi
  have hi' := Finset.mem_Icc.mp hi
  obtain ⟨a, ha⟩ := hP.int_u' i (Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩)
  obtain ⟨c, hc⟩ := hP.int_u' (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hg := hP.gap i hi
  unfold M.Par.lo M.Par.hi at hg
  have h1 := le_max_right (P.u (i + 1)) (P.u' (i + 1))
  have h2 := min_le_right (P.u i) (P.u' i)
  have h3 : ((1 : ℤ) : ℝ) ≤ ((a - c : ℤ) : ℝ) := by push_cast; linarith
  have h4 : (1 : ℤ) ≤ a - c := by exact_mod_cast h3
  obtain ⟨N, hN⟩ : ∃ N : ℕ, a - c - 1 = (N : ℤ) := ⟨(a - c - 1).toNat, by omega⟩
  refine ⟨N, ?_⟩
  have h5 : ((a - c - 1 : ℤ) : ℝ) = ((N : ℤ) : ℝ) := by rw [hN]
  push_cast at h5
  linarith

theorem amapsShExists : GlobalTheory.WigSh.AmapsShExists := by
  obtain ⟨c₃, hc⟩ := GlobalTheory.WigSh.contraction_maps_at_representatives
  refine ⟨c₃, ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm l n₀ b hpz hpz' hmz hmz' hpπ hmπ
    hpν hpm hmν hmm hl hlk hn hb hnb h1b hup hum
  have h0 := p.hT 0 (Nat.zero_le _)
  have h1 := pp.hT 0 (Nat.zero_le _)
  have h2 := pm.hT 0 (Nat.zero_le _)
  have hp : Q.IsType P.k P.r p.T.base.z' pp.T.base.π' up' := hpz' ▸ pp.hP.2.2.2.2.2.2
  have hm : Q.IsType P.k P.r p.T.base.z' pm.T.base.π' um' := hmz' ▸ pm.hP.2.2.2.2.2.2
  have hμp : pp.T.base.μSS = p.T.base.μSS :=
    GlobalTheory.unitaryMeasureDatum_productMeasure_eq_of_same_vectors Wp Wq Wqp P.k P.r p.T.base pp.T.base hpz hpz' h0.1 h0.2.1 h1.1 h1.2.1
      (h1.2.2.trans h0.2.2.symm)
  have hμm : pm.T.base.μSS = p.T.base.μSS :=
    GlobalTheory.unitaryMeasureDatum_productMeasure_eq_of_same_vectors Wp Wq Wqm P.k P.r p.T.base pm.T.base hmz hmz' h0.1 h0.2.1 h2.1 h2.2.1
      (h2.2.2.trans h0.2.2.symm)
  obtain ⟨Ap', Am', hAp, hAm, hlow⟩ := GlobalTheory.WigSh.exists_wigMap_pair_of_isType Wq Wqp Wqm P.k P.r p.T.base.z'
    p.T.base.π' pp.T.base.π' pm.T.base.π' P.u' up' um' l n₀ b p.T.base.z'_mem p.T.base.T'_pos
    p.hP.2.2.2.2.2.2 (par_gap_right P p.hP.1) hl hlk hn hb hnb h1b hp hm hup hum
  obtain ⟨Ap, Am, ApPt, AmPt, hPp, hPm, hrep, -, hfac, he, hbp, hbm⟩ :=
    hc Wp Wq Wqp Wqm P.k P.r p.T.base pp.T.base pm.T.base p.ν' p.m₀ n₀ b Ap' Am' hpz hpz' hpπ hμp hmz hmz' hmπ hμm
      p.hF hAp hAm hlow
  refine ⟨Ap, Am, ApPt, AmPt, hPp, hPm, hrep, ?_⟩
  intro A₀ f hA₀ hf
  obtain ⟨hfp, hfm⟩ := hfac A₀ f hA₀ hf
  refine ⟨?_, ?_, he, hbp, hbm⟩
  · intro γ hγ hG
    have h := hfp γ hγ hG
    unfold KB.Pl.V
    rw [hpν, hpm]
    exact h
  · intro γ hγ hG
    have h := hfm γ hγ hG
    unfold KB.Pl.V
    rw [hmν, hmm]
    exact h

end GlobalTheory.WigSh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WordBoundCompactSupportCoefficientsStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wordBound_compactSupportCoefficients : ∀ a : ℕ → ℕ, BasicLiftAll a → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (w : List C.Letter), KB.CutWord P p.l0 w → ∃ (C : ℝ) (J : ℕ) (Θs : List (B.DiffOp P.k P.r Wp Wq)), WordBound p (a P.r) w C J Θs (fun φ f => ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ KB.CptCoef p.T.base f) := by
  first | exact @GlobalTheory.HatNF.wordBound_cptCoef | exact GlobalTheory.HatNF.wordBound_cptCoef | (intros; apply GlobalTheory.HatNF.wordBound_cptCoef <;> assumption)
end

