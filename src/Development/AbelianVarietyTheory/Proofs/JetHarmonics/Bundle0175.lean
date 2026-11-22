import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0112
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0111
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0146
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPolyDiffOpRadialPartEqShiftedOperator
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.CmLiftConditionOfLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0115
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0088
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0094
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0080
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueConnectionIntegralChart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0173
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleIntegralPointValueBaseChange

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ActLevFullLevelGroupFramedPointsStatement
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.actLev_full_level_group_framedPoints : ∀ (D : D7) (Q : Par D) (j : ℕ), 1 ≤ (Q.Dw j).p + (Q.Dw j).q → Q.l.A = 1 → ActLev (Xo := Q.Xo j) Q.c (levFull (Q.Dw j) Q.l) := by
  first | exact @GlobalTheory.FullLevelAction.actLev_levFull | exact GlobalTheory.FullLevelAction.actLev_levFull | (intros; apply GlobalTheory.FullLevelAction.actLev_levFull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DescentIdFOfLaws
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowDescent

theorem eq_famCast_of_heq {R : Type} [CommRing R] [IsDomain R] {Dp : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k k' : ℕ} (e : k = k') (r : Fam Dp F k') (s : Fam Dp F k) (h : HEq r s) :
    r = famCast e s := by
  subst e
  exact eq_of_heq h

theorem descent_cast (hL : Laws) (hL2 : Laws2) (hL4 : Laws4) (hT : TwistBaseChangeStatement)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V))
    (P : PELUnif (maximalIdeal V) t) (hP : P.TorsionIso) :
    letI := H.starRing
    ∀ (a a' : 𝓞 E) (g g' k : ℕ) (e : 1 * g' = k), 1 ≤ g → 1 ≤ g' → Nat.Coprime g g' →
      a * star a = (g : 𝓞 E) → a' * star a' = (g' : 𝓞 E) →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [IsAlgClosed F] (θ : Fam P.D.toPre F 1)
      (θα : Fam P.D.toPre F (1 * g')), PullAl P.D F P.oD a' 1 g' θ θα →
    ∀ (pb : QkPt P.D.toPre F (1 * g'))
      (wb : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F pb.g.b) (DegPre.lineε (1 * g'))))
      (ζb : F) (xb : TFK (R := V) F ⟶ P.A.A) (tb₀ tb : Fam P.D.toPre F (1 * g')),
      P.ToA F (1 * g') pb xb → xb ≫ P.oA.act (star a') = 1 → wb.IsGen → ζb ≠ 0 →
      FinOrd P.D F (1 * g') pb wb ζb → PhiRel P.D.toPre F (1 * g') pb wb θα tb₀ →
      Fam.IsSmul P.D.toPre F ζb tb₀ tb →
    ∀ (p : QkPt P.D.toPre F (k * g))
      (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε (k * g))))
      (ζ : F) (x : TFK (R := V) F ⟶ P.A.A), w.IsGen → ζ ≠ 0 → FinOrd P.D F (k * g) p w ζ →
      P.ToA F (k * g) p x → x ≫ P.oA.act (star a) = 1 →
    ∀ (s₂ t₀ r : Fam P.D.toPre F (k * g)), PullAl P.D F P.oD a k g (famCast (Dp := P.D.toPre) (F := F) e tb) s₂ →
      PhiRel P.D.toPre F (k * g) p w s₂ t₀ → Fam.IsSmul P.D.toPre F ζ t₀ r →
    ∃ (θα₂ : Fam P.D.toPre F (1 * (g' * g))) (p₂ : QkPt P.D.toPre F (1 * (g' * g)))
      (w₂ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p₂.g.b) (DegPre.lineε (1 * (g' * g)))))
      (ζ₂ : F) (x₂ : TFK (R := V) F ⟶ P.A.A) (r₀ r₂ : Fam P.D.toPre F (1 * (g' * g))),
      PullAl P.D F P.oD (a * a') 1 (g' * g) θ θα₂ ∧ P.ToA F (1 * (g' * g)) p₂ x₂ ∧
      x₂ ≫ P.oA.act (star (a * a')) = 1 ∧ w₂.IsGen ∧ ζ₂ ≠ 0 ∧ FinOrd P.D F (1 * (g' * g)) p₂ w₂ ζ₂ ∧
      PhiRel P.D.toPre F (1 * (g' * g)) p₂ w₂ θα₂ r₀ ∧ Fam.IsSmul P.D.toPre F ζ₂ r₀ r₂ ∧ HEq r r₂ := by
  letI := H.starRing
  intro a a' g g' k e
  subst e
  exact descent_one_generator hL hL2 hL4 hT V E H t P hP a a' g g'

theorem descentIdF_of_laws :
    Laws → Laws2 → Laws3 → Laws4 → Laws5 → TwistBaseChangeStatement → DescentIdF := by
  intro hL hL2 hL3 hL4 hL5 hT E _ _ _ H Dw l Xo c n
  letI := H.starRing
  intro T io y _ C P _ g g' hg hg' hne _ _ π π' hπ hπ' _ _ _ F _ _ _ _ _ _ v ϖ _ _ Q _ D' A' G' gr cm pD pA pG U' PU
    md oD' hx hoD oA' hoA θ θα hθ pb wb ζb xb tb₀ tb hxb hxba hwb hζb hfb hΦb hsb p w ζ x hw hζ hf hpx hxπ
    s₂ t₀ r hs₂ hΦ hr
  obtain ⟨oA'', hoA'', t', P', e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉⟩ :=
    exists_pelUnif_of_unifPow hL hL2 hL4 hT T.V E H C.I.G P n D' A' G' pD pA pG U' PU oD' hx hoD
  have hact : ∀ a, oA'.act a = oA''.act a := fun a =>
    Fan.IsLimit.hom_ext pA.lim _ _ fun i => (hoA a i).trans (hoA'' a i).symm
  have hxa : x ≫ oA''.act (star (star π)) = 1 := by
    refine Fan.IsLimit.hom_ext pA.lim _ _ fun i => ?_
    have := pA.hom i
    change (x ≫ oA''.act (star (star π))) ≫ pA.pr i = 1 ≫ pA.pr i
    rw [star_star, Category.assoc, hoA'', hxπ, MonObj.one_comp]
  have htors : P'.TorsionIso :=
    GlobalTheory.T.torsionIso_of_linear_uniformisation_triple ⟨hL, hL2, hL3, hL4, hL5⟩ (twistBCSpan_of hT) GlobalTheory.RatioVal.main
      (twisting_statements_of_laws hL hT).1 (GlobalTheory.UnitBallFree.main hL.globalFns hT) E H T.V (maximalIdeal T.V)
      ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩ t' P'
  rw [hact] at hxba
  simp only [hact]
  clear hoA hact hoA'' hxπ hx hoD PU pD pA pG
  subst e₁ e₄ e₇
  cases e₂
  cases e₃
  cases e₅
  cases e₆
  cases e₈
  cases e₉
  obtain ⟨θα₂, p₂, w₂, ζ₂, x₂, r₀, r₂, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉⟩ :=
    descent_cast hL hL2 hL4 hT T.V E H t' P' htors (star π) (star π') g g' g' (one_mul g') hg.one_le hg'.one_le
      ((Nat.coprime_primes hg hg').2 hne) (by rw [star_star, _root_.mul_comm, hπ])
      (by rw [star_star, _root_.mul_comm, hπ']) F θ θα hθ pb wb ζb xb tb₀ tb hxb hxba hwb hζb hfb hΦb hsb
      p w ζ x hw hζ hf hpx hxa s₂ t₀ r hs₂ hΦ hr
  exact ⟨θα₂, p₂, w₂, ζ₂, x₂, r₀, r₂, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, eq_famCast_of_heq _ _ _ k₉⟩

end GlobalTheory.PowDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPolyDiffOpRadialPartEqShiftedOperatorStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polyDiffOp_radialPart_eq_shiftedOperator : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ y : ℝ, PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) (d.L.Ahat y) := by
  first | exact @GlobalTheory.HatNF.polyLift_ahat | exact GlobalTheory.HatNF.polyLift_ahat | (intros; apply GlobalTheory.HatNF.polyLift_ahat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTermLe
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.SmallTranslate

theorem exists_term_le {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {I J : Type} [Fintype I] [Fintype J]
    (a : I → F) (c : J → F) (x : J → I → F) (ha : ∀ i, 0 ≤ v (a i)) (hc : ∀ j, 0 ≤ v (c j)) (r : ℚ)
    (h : v (∑ j, c j * ∑ i, a i * x j i) = (r : WithTop ℚ)) :
    ∃ (i : I) (j : J) (ρ : ℚ), v (x j i) = (ρ : WithTop ℚ) ∧ ρ ≤ r := by
  by_contra hne
  have hlt : ∀ i j, (r : WithTop ℚ) < v (x j i) := fun i j => by
    by_contra hle
    obtain ⟨ρ, hρ, hρr⟩ := WithTop.le_coe_iff.1 (not_lt.1 hle)
    exact hne ⟨i, j, ρ, hρ, hρr⟩
  have : (r : WithTop ℚ) < v (∑ j, c j * ∑ i, a i * x j i) := by
    refine AddValuation.map_lt_sum v WithTop.coe_ne_top fun j _ => ?_
    rw [v.map_mul]
    refine lt_add_of_nonneg_of_lt (hc j) (AddValuation.map_lt_sum v WithTop.coe_ne_top fun i _ => ?_)
    rw [v.map_mul]
    exact lt_add_of_nonneg_of_lt (ha i) (hlt i j)
  exact absurd h this.ne'

theorem span_pow (h1 : Laws) (h2 : Laws2) (h3 : Laws3) (h4 : Laws4) (h5 : Laws5) (hT : TwistBaseChangeStatement)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [hc : IsAdicComplete (maximalIdeal V) V] [CharZero V]
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t)
    (Dw : Datum H) (ϖ : V) (hϖ : Irreducible ϖ) (Q : P.D.toPre.X → ℤ) (hQ : IsQ P.D.toPre ϖ Q)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v)
    (I : TateIso Dw F (TFK (R := V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a)
      (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z)))
    (n : ℕ) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G' : Over (Sp V))
    [gG : GrpObj G'] [cG : IsCommMonObj G']
    (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' t.G n)
    (U' : Unif (maximalIdeal V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) :
    letI := H.starRing
    ∀ [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) →
    ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) → IsUnit ((N : ℕ) : V) →
    ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), NuGe D' (sumQ pD.xe Q) F v 1 θ 0 → ThFrame D' ϖ F θ →
      PullAl D' F oD' α 1 N θ θα →
    ∀ s : Fam D'.toPre F (1 * N), NuGe D' (sumQ pD.xe Q) F v (1 * N) s 0 →
      ∃ (m : ℕ) (p : Fin m → QkPt D'.toPre F (1 * N)) (x : Fin m → (TFK (R := V) F ⟶ A'.A))
        (w : ∀ i, LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F (p i).g.b) (DegPre.lineε (1 * N))))
        (ζ : Fin m → F) (t : Fin m → Fam D'.toPre F (1 * N)) (a : Fin m → F),
        (∀ i, QkToAkU U'.toUnifPre F (1 * N) (p i) (x i)) ∧
        (∀ i k, x i ≫ pA.pr k ≫ P.oA.act (star α) = 1) ∧
        (∀ i, (w i).IsGen ∧ ζ i ≠ 0 ∧ FinOrd D' F (1 * N) (p i) (w i) (ζ i)) ∧
        (∀ i, ∃ t' : Fam D'.toPre F (1 * N),
          PhiRel D'.toPre F (1 * N) (p i) (w i) θα t' ∧ Fam.IsSmul D'.toPre F (ζ i) t' (t i)) ∧
        (∀ i, (0 : WithTop ℚ) ≤ v (a i)) ∧
        s = ∑ i, a i • t i := by
  let _ := H.starRing
  intro md oD' hx hoD α N hN hα hcop hu θ θα hθ hθF hθα s hs
  obtain ⟨oA', hoA, t', P', hG, hgrp, hcomm, hD, hmod, hoD', hA, hoA', hU⟩ :=
    GlobalTheory.exists_pelUnif_of_unifPow h1 h2 h4 hT V E H t P n D' A' G' pD pA pG U' PU oD' hx hoD
  obtain ⟨Dw', ⟨I'⟩⟩ := GlobalTheory.exists_tateIso_of_isPowPolAV h1 h2 h4 hT E H V n P.A A' pA F P.oA.act oA'.act hoA Dw I
  have hQ' : IsQ D'.toPre ϖ (sumQ pD.xe Q) := GlobalTheory.QBox.main V ϖ hϖ n P.D D' pD Q hQ
  have hUU : UUStatement := GlobalTheory.UnitBallFree.main h1.globalFns hT
  have hP' : P'.TorsionIso := GlobalTheory.T.torsionIso_of_linear_uniformisation_triple ⟨h1, h2, h3, h4, h5⟩ (twistBCSpan_of hT) GlobalTheory.RatioVal.main
    (GlobalTheory.twisting_statements_of_laws h1 hT).1 hUU E H V _
    ⟨inferInstance, inferInstance, inferInstance, hc⟩ t' P'
  subst hG hD hA
  cases hgrp
  cases hmod
  cases hoD'
  cases hoA'
  cases hU
  obtain ⟨m, p, x, w, ζ, tt, a, e1, e2, e3, e4, e5, e6⟩ := ReciprocityTheory.ChartRestriction.G.H1.cmLiftCondition_of_laws h1 n1c (GlobalTheory.twisting_statements_of_laws h1 hT).1 hUU E H V t' P' hP' α N hN hα hcop hu ϖ hϖ _ hQ' F v hv
    Dw' I' θ hθ hθF θα hθα s hs
  refine ⟨m, p, x, w, ζ, tt, a, e1, fun i k => ?_, e3, e4, e5, e6⟩
  have := pA.toIsPowGrp.hom k
  rw [← hoA, ← Category.assoc, e2 i]
  exact MonObj.one_comp _

theorem main : Laws → Laws2 → Laws3 → Laws4 → Laws5 → TwistBaseChangeStatement → RPointT := by
  intro h1 h2 h3 h4 h5 hT E _ _ _ H Dw l Xo c
  let _ := H.starRing
  intro T io y C hFT P hP hy ϖ hϖ Q hQ F _ _ _ _ _ _ v hv I Φ M0 r b hΦ hb hbw n D' A' G' _ _ pD pA pG U' PU _ oD' hx hoD hn
    α N Dg hα hcop hu hN hM θ θα hθ hθF hθα J _ Pi a ha hdeg f hf gm hval
  let _ := io.toAlgebra
  have hN1 : 1 ≤ 1 * N := by omega
  obtain ⟨s, σ', g, lam, hs, hσ', hg, -, ⟨ρl, hlam, hρl⟩, hjet⟩ :=
    GlobalTheory.T.jets_on_copies_of_compatible_frames h1 h2 h4 hT E H Dw l Xo c (fun _ => rfl) T io y hy C hFT P ϖ hϖ Q hQ Φ M0 r b hΦ hb hbw n hn D' A' G'
      pD pA pG U' PU F v hv (1 * N) Dg (by omega) (by rwa [Nat.one_mul]) f hf
  obtain ⟨m, p, x, w, ζ, t, cf, e1, e2, e3, e4, e5, e6⟩ := span_pow h1 h2 h3 h4 h5 hT T.V E H C.I.G P Dw ϖ hϖ Q hQ F v hv I
    n D' A' G' pD pA pG U' PU oD' hx hoD α N (by omega) hα hcop hu θ θα hθ hθF hθα s hs
  obtain ⟨τ, hτ, hτT, hiff⟩ := GlobalTheory.PowGerm.frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hz := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n _ pG C.xT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C)
  obtain ⟨huniq, hlin, hex⟩ := GlobalTheory.GermBasic.main T.V D' A' G' U' _ _ hz τ hτ F (1 * N)
  have hbij := (GlobalTheory.expandsG_bijective_of_dvr h1 h2 h4 hT T.V D' A' G' U' F (1 * N) hN1).2
  choose σ hσ using fun j => (hbij (t j)).exists
  choose h hh using fun j => hex (hτT hFT) (σ j)
  have hsum : g = ∑ j, cf j • h j := by
    let σ₀ : U'.toUnifPre.SecGF F (1 * N) := GlobalTheory.ExpansionLinear.secComb
      (fun j => Out.scal (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj G')).left (cf j)) σ
    have k1 := GlobalTheory.GroupExpansionLinear.expandsG_sum T.V D' A' G' U' F (1 * N) m cf σ t σ₀ hσ (fun _ => rfl)
    rw [← e6] at k1
    have k2 : σ' = σ₀ := (hbij s).unique hσ' k1
    exact huniq σ' _ _ ((hiff F _ σ' g).1 hg) (hlin m cf σ h σ' hh (fun _ => by rw [k2]; rfl))
  obtain ⟨n1, n2, n3⟩ := GlobalTheory.PowGerm.nabJet _ _ _ C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * N) n
    (LtN Dw n) (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
  have k1 := n1 (∑ i, a i • Pi i) _ _ (fun e he => hjet e (he.trans hdeg))
  have k2 := n2 (∑ i, a i • Pi i) Unit (fun _ => lam) (fun _ => MvPowerSeries.map (algebraMap T.Fr F) f)
  rw [Finset.univ_unique, Finset.sum_singleton, Finset.sum_singleton] at k2
  have k3 := n2 (∑ i, a i • Pi i) (Fin m) cf h
  rw [← hsum, k1, k2, Finset.sum_congr rfl fun j _ => congrArg (cf j * ·) (n3 (h j) J a Pi)] at k3
  have k4 := congrArg v k3
  rw [v.map_mul, hlam] at k4
  obtain ⟨i, j, ρ, hρ, hle⟩ := exists_term_le v a cf _ ha e5 (ρl + gm)
    (k4.symm.trans (by rw [WithTop.coe_add]; exact congrArg _ hval))
  obtain ⟨t₀, ht₀, ht⟩ := e4 j
  refine ⟨i, p j, w j, ζ j, x j, t₀, t j, σ j, h j, ρ, (e3 j).1, (e3 j).2.1, (e3 j).2.2, e1 j, e2 j, ht₀, ht, hσ j,
    (hiff F _ _ _).2 (hh j), hρ, ?_⟩
  rw [Nat.one_mul] at hρl
  have : (ρ : ℝ) ≤ ρl + gm := by exact_mod_cast hle
  linarith

end GlobalTheory.SmallTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateEqUnitMulNormaliserThetaVa
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PtTie

theorem addVal_eq_zero_of_pow_eq_one {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (u : F) (m : ℕ) (hm : 0 < m)
    (hu : u ^ m = 1) : v u = 0 := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hu
    exact zero_ne_one hu
  have h1 : m • v u = 0 := by rw [← AddValuation.map_pow, hu, AddValuation.map_one]
  have ht : v u ≠ ⊤ := by rwa [Ne, AddValuation.top_iff]
  lift v u to ℚ using ht with q hq
  have h3 : m • q = 0 := by exact_mod_cast h1
  rw [nsmul_eq_mul] at h3
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd h (by exact_mod_cast hm.ne')
  · rw [h]; rfl

theorem addVal_prod_eq_zero {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {K : Type} (s : Finset K) (u : K → F)
    (hu : ∀ i, v (u i) = 0) : v (∏ i ∈ s, u i) = 0 := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, AddValuation.map_mul, hu, ih, add_zero]

theorem boxSer_smul {k : Type} [CommRing k] {n d : ℕ} (u : Fin n → k) (f : Fin n → PS k 1 d) :
    boxSer (fun i => u i • f i) = (∏ i, u i) • boxSer f := by
  simp only [boxSer, map_smul]
  simp only [Algebra.smul_def, Finset.prod_mul_distrib, map_prod]

set_option maxHeartbeats 1600000 in

theorem harmonicValue_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (α : 𝓞 E) (N : ℕ), N = l.M → α * star α = (N : 𝓞 E) → l.Mb = Ideal.span {star α} → ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), ThFrame D' ϖ F θ → PullAl D' F oD' α 1 N θ θα → ∀ (p : QkPt D'.toPre F (1 * N)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * N)) (q : ℕ) (e : 1 * N = q) (σ' : U'.toUnifPre.SecGF F q) (h : PS F n (chD C.ch)), w.IsGen → ζ ≠ 0 → FinOrd D' F (1 * N) p w ζ → QkToAkU U'.toUnifPre F (1 * N) p x → PhiRel D'.toPre F (1 * N) p w θα t₀ → Fam.IsSmul D'.toPre F ζ t₀ t → U'.toUnifPre.ExpandsG F q σ' (PowGerm.famCast (Dp := D'.toPre) (F := F) e t) → IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' h → (∀ k, x ≫ pA.pr k ≫ P.oA.act (star α) = 1) → letI := io.toAlgebra; ∃ (xx : Fin n → Dw.La) (u : F), v u = 0 ∧ ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∀ f, IsThRule Xo c nab xx Pp f → nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 q h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) = u * algebraMap T.Fr F (io (nrm Dw c a α) * evI y f) := by
  intro E _ _ _ H Dw l Xo c nab hnab T io y C hFT P hTors hAlg ϖ hϖ Q hQ F _ _ _ _ _ _ v hv n D' A' G' _ _ pD pA pG
    U' PU _ oD' hxe hoD α N hN hα hMb θ θα hθ hθα p w ζ x t₀ t q e σ' h hw hζ hFin hQk hPhi hSm hExp hGerm hx
  letI := H.starRing
  letI := io.toAlgebra
  subst hN
  obtain rfl : q = l.M := by rw [← e, Nat.one_mul]
  have hodd : Odd l.M := l.odd
  have h1 : 1 ≤ l.M := le_trans (by norm_num) l.three_le

  obtain ⟨τ, hτG, hτEL, hτT⟩ := frame1St_holds E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.15 C.17 C.18
  have hUJ : IsUnivJ C.I.G.G (Fin 1 × Fin (chD C.ch)) C.xT := GlobalTheory.T.universal_statement E H Dw l Xo c T io y C
  have hAG := GlobalTheory.GermBasic.main T.V _ _ _ P.U _ C.xT hUJ τ hτG F l.M

  letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra
  let φ : T.Fr →ₐ[c.F] F := { algebraMap T.Fr F with commutes' := fun _ => rfl }
  obtain ⟨yF, hyF⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c T.Fr F φ y.1

  obtain ⟨θ₁, θα₁, hθ₁, hθα₁, hcol⟩ := GlobalTheory.OneColTranslate.oneColumn_translate E H Dw l Xo c T io y.1 C.I P ϖ hϖ F φ rfl
    yF hyF α l.M hodd hα

  obtain ⟨u₀, p₁, w₁, ζ₁, r₀, r, σ₁, f, hu₀, hhf, hcols⟩ := GlobalTheory.ColumnSplit.main E H Dw l Xo c T io y C hFT P hTors hAlg
    ϖ hϖ Q hQ F v hv n D' A' G' pD pA pG U' PU oD' hxe hoD τ hτG hτEL α l.M h1 hα θ₁ θα₁ hθ₁ hθα₁ θ θα hθ hθα p w ζ x t₀
    t l.M e σ' h hw hζ hFin hQk hPhi hSm hExp hGerm
  have hall := fun i => hcol (p₁ i) (w₁ i) (ζ₁ i) (x ≫ pA.pr i) (r₀ i) (r i) (σ₁ i) (hcols i).1 (hcols i).2.1
    (hcols i).2.2.1 ((Category.assoc _ _ _).trans (hx i)) (hcols i).2.2.2.1 (hcols i).2.2.2.2.1 (hcols i).2.2.2.2.2.1
  choose U B HH S0 hU hB hTP hTie hσ using hall

  have hex : ∀ i, ∃ g, GermA P.U.toUnifPre C.xT τ F l.M (S0 i) g := fun i => hAG.2.2 (hτT hFT) (S0 i)
  choose f' hf' using hex
  have hff : ∀ i, f i = U i • f' i := by
    intro i
    have hlin := hAG.2.1 1 (fun _ => U i) (fun _ => S0 i) (fun _ => f' i) (σ₁ i) (fun _ => hf' i)
      (by intro jj; rw [Fin.sum_univ_one]; exact hσ i jj)
    have := hAG.1 (σ₁ i) _ _ (hcols i).2.2.2.2.2.2 hlin
    rw [Fin.sum_univ_one] at this
    exact this
  have hh2 : h = (u₀ * ∏ i, U i) • boxSer f' := by
    rw [hhf, show f = fun i => U i • f' i from funext hff, boxSer_smul, smul_smul]
  have hv0 : v (u₀ * ∏ i, U i) = 0 := by
    rw [AddValuation.map_mul, hu₀, zero_add]
    refine addVal_prod_eq_zero v Finset.univ U (fun i => ?_)
    obtain ⟨m, hm, hum⟩ := hU i
    exact addVal_eq_zero_of_pow_eq_one v (U i) m hm hum

  have hT := GlobalTheory.harmonic_value_of_tied_sections E H Dw l Xo c nab hnab T io y C P τ hτG hτEL F φ rfl yF hyF l.M n S0
    HH f' hTie hf'
  obtain ⟨xx, Fs, hFs, hA⟩ := GlobalTheory.AlphaForm.alphaForm_at_point E H Dw l Xo c nab hnab F yF α hα hMb n B HH hB hTP
  refine ⟨xx, u₀ * ∏ i, U i, hv0, ?_⟩
  intro a Pp hP fth hth
  have h9918 := GlobalTheory.PtTie.evI_eq_thExpr_ext E H Dw l Xo c nab hnab T io y F φ rfl yF hyF a n xx Pp hP Fs hFs fth hth
  have key : ∀ (g : PS F n (chD C.ch)) (s : F),
      nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 l.M (s • g) (fun ℓ : LtN Dw n => ℓ.2.2)
        (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
        (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) =
      s * nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 l.M g (fun ℓ : LtN Dw n => ℓ.2.2)
        (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
        (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) := by
    intro g s
    have := (GlobalTheory.PowGerm.nabJet _ _ _ C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 l.M n (LtN Dw n)
      (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))).2.1
      (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) (Fin 1) (fun _ => s) (fun _ => g)
    simp only [Fin.sum_univ_one] at this
    exact this
  have hT' := hT a Pp hP
  rw [hA a Pp hP] at hT'
  rw [hh2, key, map_mul, h9918]
  exact congrArg (fun z => (u₀ * ∏ i, U i) * z) hT'.symm

end GlobalTheory.PtTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowPELOfLaws
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

theorem powPEL_of_laws : Laws → Laws2 → Laws3 → Laws4 → Laws5 → TwistBaseChangeStatement → PowPELF := by
  intro h₁ h₂ h₃ h₄ h₅ hT E _ _ _ H Dw l Xo c n T io y _ C P _ g g' _ _ _ _ _ π π' _ _ _ _ _ F _ _ _ _ _ _ v ϖ hϖ _ I Q hQ
    D' A' G' _ _ pD pA pG U' PU _ oD' hx hB
  letI := H.starRing
  have hA : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨oA', hoA, t', P', hP'⟩ :=
    GlobalTheory.exists_pelUnif_of_unifPow h₁ h₂ h₄ hT T.V E H C.I.G P n D' A' G' pD pA pG U' PU oD' hx hB
  refine ⟨oA', hoA, GlobalTheory.QBox.main T.V ϖ hϖ n P.D D' pD Q hQ,
    GlobalTheory.exists_tateIso_of_isPowPolAV h₁ h₂ h₄ hT E H T.V n P.A A' pA F _ _ hoA Dw I, t', P', ?_, hP'⟩
  exact GlobalTheory.T.torsionIso_of_linear_uniformisation_triple ⟨h₁, h₂, h₃, h₄, h₅⟩ (twistBCSpan_of hT) GlobalTheory.RatioVal.main
    (GlobalTheory.twisting_statements_of_laws h₁ hT).1 (GlobalTheory.UnitBallFree.main h₁.globalFns hT) E H T.V _ hA t' P'

end GlobalTheory.PowGerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleIntegralPointValueBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRule_integralPoint_value_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T T' : CDVR) (io : c.F →+* T.Fr) (io' : c.F →+* T'.Fr) (y : IntFr Xo c T io) (y' : IntFr Xo c T' io'), letI := io.toAlgebra; letI := io'.toAlgebra; ∀ φ : T.Fr →ₐ[c.F] T'.Fr, FrMap φ y.1 y'.1 → ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (n : ℕ), ∀ f ∈ thGen Xo c nab a n, φ (evI y f) = evI y' f := by
  first | exact @GlobalTheory.ThetaRuleValue.evI_baseChange | exact GlobalTheory.ThetaRuleValue.evI_baseChange | (intros; apply GlobalTheory.ThetaRuleValue.evI_baseChange <;> assumption)
end

