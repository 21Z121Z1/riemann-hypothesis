import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0171
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0160
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0016
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0152
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MirrorTodaRadialOperatorPolynomialCoefficientLif
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalizedPullbackConjugateTranslateEqTranslateL
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0143
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0172
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0166
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0088
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0099
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0097
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0100
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0090
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0167

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsGeneratorRatioEqOneOfUnitFrameMoveStatement
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_generatorRatio_eq_one_of_unitFrame_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMove ρ ν (U.un k x) y' → FrBor t (U.un k' x') y' → IsUnitFr (U.X k) x.1 → IsUnitFr (U.X k') x'.1 → cabs (t none : CAt σ) = 1 := by
  first | exact @GlobalTheory.LevelCusp.cabs_gen_eq_one_of_move | exact GlobalTheory.LevelCusp.cabs_gen_eq_one_of_move | (intros; apply GlobalTheory.LevelCusp.cabs_gen_eq_one_of_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBelowOneOfHodgeTateChartForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.PowGerm

theorem lemmaBT_of_hodgeTate_chart : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.HTFSt p) → LemmaBT := fun h =>
  lemmaBT_of_characters GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1 GlobalTheory.firstFiveLaws.2.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.1 (GlobalTheory.T.exists_characters_boundedMinors_of_hodgeTateChartBound h)

end GlobalTheory.PowGerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MirrorTodaRadialOperatorPolynomialCoefficientLifStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirrorTodaRadialOperator_polynomialCoefficient_lift : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ y : ℝ, PolyLift P Bs (2 * P.r + P.k + 1) (8 * (P.r + 1) * (2 * P.r + P.k + 1)) (d.L.Ahatv y) := by
  first | exact @GlobalTheory.MirrorToda.polyLift_ahatv | exact GlobalTheory.MirrorToda.polyLift_ahatv | (intros; apply GlobalTheory.MirrorToda.polyLift_ahatv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalizedPullbackConjugateTranslateEqTranslateLStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedPullback_conjugate_translate_eq_translate_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (F : Type) [Field F] [IsAlgClosed F] (xF : Sp F ⟶ Xo.X) (α : 𝓞 E), α * star α = (l.M : 𝓞 E) → l.Mb = Ideal.span {star α} → ∀ (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo xF))) (b : ptO Xo xF ⟶ Xo.univ.t.G) (hh : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (l.M : ℤ) (ptO Xo xF))), b ≫ Xo.univ.t.act.act (star α) = 1 → IsTransPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) l.M s b hh → ∃ Fs : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo xF)), IsNormPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act (star α)) ((l.M : ℤ) ^ 2) (l.M : ℤ) hh Fs ∧ IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) s (b ≫ Xo.univ.t.act.act α) Fs := by
  first | exact @GlobalTheory.isVtOver_conj_pull_of_isTransPull | exact GlobalTheory.isVtOver_conj_pull_of_isTransPull | (intros; apply GlobalTheory.isVtOver_conj_pull_of_isTransPull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.OneColumnTranslateSectionRootOfUnityMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.OneColTranslate

theorem pow_eq_one_of_act {S : Scheme.{0}} {O : Type} [CommRing O] {G T : Over S} [GrpObj G]
    (a : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (b : T ⟶ G) (α β : O) (N : ℕ) (h : α * β = (N : O))
    (hb : b ≫ a.act β = 1) : b ^ N = 1 := by
  have h0 : a.act 0 = 1 := by
    have h1 := a.add 0 0
    rw [add_zero] at h1
    exact (mul_eq_left.mp h1.symm)
  have hn : ∀ n : ℕ, b ≫ a.act (n : O) = b ^ n := by
    intro n
    induction n with
    | zero => rw [Nat.cast_zero, h0, pow_zero, MonObj.comp_one]
    | succ n ih => rw [Nat.cast_succ, a.add, MonObj.comp_mul, ih, a.one, Category.comp_id, pow_succ]
  haveI := a.hom α
  rw [← hn, ← h, mul_comm, a.mul, ← Category.assoc, hb, MonObj.one_comp]

theorem oneColumn_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (ϖ : T.V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F], letI := io.toAlgebra; letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra; ∀ (φ : T.Fr →ₐ[c.F] F), φ.toRingHom = algebraMap T.Fr F → ∀ (yF : FrPt Xo c F), FrMap φ y yF → ∀ (α : 𝓞 E) (N : ℕ), Odd N → α * star α = (N : 𝓞 E) → ∃ (θ₁ : Fam P.D.toPre F 1) (θα₁ : Fam P.D.toPre F (1 * N)), ThFrame P.D ϖ F θ₁ ∧ PullAl P.D F P.oD α 1 N θ₁ θα₁ ∧ ∀ (p : QkPt P.D.toPre F (1 * N)) (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F) (x : TFK (R := T.V) F ⟶ P.A.A) (r₀ r : Fam P.D.toPre F (1 * N)) (σ : P.U.toUnifPre.SecGF F N), w.IsGen → FinOrd P.D F (1 * N) p w ζ → P.ToA F (1 * N) p x → x ≫ P.oA.act (star α) = 1 → PhiRel P.D.toPre F (1 * N) p w θα₁ r₀ → Fam.IsSmul P.D.toPre F ζ r₀ r → P.U.toUnifPre.ExpandsG F N σ (PowGerm.famCast (Dp := P.D.toPre) (F := F) (one_mul N) r) → ∃ (u : F) (b : ptO Xo yF.x ⟶ Xo.univ.t.G) (hh : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (N : ℤ) (ptO Xo yF.x))) (σ₀ : P.U.toUnifPre.SecGF F N), (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ b ≫ Xo.univ.t.act.act (star α) = 1 ∧ IsTransPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) N yF.s b hh ∧ SecTieF I P F yF.x N σ₀ hh ∧ ∀ jj, σ.f jj = resTop ((LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (R := T.V) (G := I.G.G) F) (fun _ => (N : ℤ))).U jj) (scal (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left u) * σ₀.f jj := by
  intro E _ _ _ H Dw l Xo c T io y I P ϖ hϖ F _ _ _ φ hφ yF hyF α N hN hα
  letI := H.starRing
  letI := io.toAlgebra
  letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra
  have hLL := GlobalTheory.firstFiveLaws
  have hL : Laws := hLL.1
  have hN1 : 1 ≤ N := hN.pos
  have hx : yF.x = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) := by
    have h1 := hyF.1
    rw [hφ] at h1
    exact h1
  have hbij := GlobalTheory.expandsG_bijective_of_dvr hL hLL.2.1 hLL.2.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.1 T.V P.D P.A I.G.G P.U F
  have hsec := GlobalTheory.T.powPullbackSec_modelUniversal_bijective E H Dw l Xo c T io y I P F yF.x hx
  obtain ⟨σs, hσs, -⟩ := (hsec 1).2.1 yF.s
  obtain ⟨θ₁, hθ₁, -⟩ := (hbij 1 le_rfl).1 σs
  obtain ⟨π, -, hπ⟩ := GlobalTheory.PullLin.exists_pull_linearMap hL T.V P.D F (𝓞 E) P.oD H.w0 P.w0 α N 1 hN1 le_rfl hα
  have hpull : PullAl P.D F P.oD α 1 N θ₁ (π θ₁) := (hπ _ _).2 rfl
  refine ⟨θ₁, π θ₁, GlobalTheory.T.thetaFrame_expansion_framedPoint_generator E H Dw l Xo c T io y I P ϖ hϖ F φ hφ yF hyF σs θ₁ hσs hθ₁, hpull, ?_⟩
  intro p w ζ x r₀ r σ hw hfin hto hxk hphi hsm hσ
  obtain ⟨e, he, hea⟩ := GlobalTheory.T.exists_mulEquiv_uniformisedPoints_universal E H Dw l Xo c T io y I P F yF.x hx
  have hb : e x ≫ Xo.univ.t.act.act (star α) = 1 := by rw [← hea, hxk, map_one]
  have hbN : e x ^ N = 1 := pow_eq_one_of_act _ _ α (star α) N hα hb
  obtain ⟨hh, hhh⟩ := GlobalTheory.T.exists_translated_normalisedPullback_section E H Dw l Xo c F yF.x α N hN hα yF.s (e x) hbN
  obtain ⟨h₁, hnp, hsym⟩ := id hhh
  obtain ⟨σ₁, hσ₁, -⟩ := (hsec N).2.1 h₁
  obtain ⟨σ₀, hσ₀, -⟩ := (hsec N).2.1 hh
  have hex₁ := GlobalTheory.T.normalisedPullback_section_expands_family E H Dw l Xo c T io y I P F yF.x hx α N 1 N (_root_.one_mul N) hα hN1 (Or.inl rfl)
    σs yF.s θ₁ σ₁ h₁ (π θ₁) hσs hθ₁ hnp hσ₁ hpull
  have key : ∀ (q : ℕ) (eq : q = N) (θ : Fam P.D.toPre F q) (p : QkPt P.D.toPre F q)
      (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε q)))
      (r₀ r : Fam P.D.toPre F q),
      P.U.toUnifPre.ExpandsG F N σ₁ (PowGerm.famCast (Dp := P.D.toPre) (F := F) eq θ) →
      w.IsGen → FinOrd P.D F q p w ζ → P.ToA F q p x → PhiRel P.D.toPre F q p w θ r₀ →
      Fam.IsSmul P.D.toPre F ζ r₀ r →
      ∃ (u : F) (t' : Fam P.D.toPre F N), (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧
        Fam.IsSmul P.D.toPre F u (PowGerm.famCast (Dp := P.D.toPre) (F := F) eq r) t' ∧
        P.U.toUnifPre.ExpandsG F N σ₀ t' := by
    intro q eq
    obtain rfl : N = q := eq.symm
    intro θ p w r₀ r hθ hw hfin hto hphi hsm
    exact GlobalTheory.T.symmetric_lift_acts_root_of_unity_on_expansions E H Dw l Xo c T io y I P F yF.x hx N hN1 σ₁ σ₀ h₁ hh θ r₀ r x (e x) p w ζ hσ₁ hσ₀ hθ hsym
      ((he _ _).2 rfl) hto hw hfin hphi hsm
  obtain ⟨u, t', ⟨m, hm, hum⟩, hut, hex₀⟩ := key (1 * N) (one_mul N) (π θ₁) p w r₀ r hex₁ hw hfin hto hphi hsm
  have hu : u ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hum
    exact zero_ne_one hum
  rw [isSmul_iff] at hut
  let σ' : P.U.toUnifPre.SecGF F N := SecOps.secScale
    (Out.scal (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left u⁻¹) σ₀
  have hex' := GlobalTheory.GroupExpansionLinear.expandsG_sum T.V P.D P.A I.G.G P.U F N 1 (fun _ => u⁻¹) (fun _ => σ₀)
    (fun _ => t') σ' (fun _ => hex₀) (fun jj => by rw [Fin.sum_univ_one]; rfl)
  rw [Fin.sum_univ_one, hut, smul_smul, inv_mul_cancel₀ hu, one_smul] at hex'
  have hσσ : σ = σ' := ((hbij N hN1).2 _).unique hσ hex'
  refine ⟨u⁻¹, e x, hh, σ₀, ⟨m, hm, by rw [inv_pow, hum, inv_one]⟩, hb, hhh, hσ₀, fun jj => ?_⟩
  rw [hσσ]
  rfl

end GlobalTheory.OneColTranslate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaRuleValueIntegralFramedPointExtensionFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRule_value_integral_framed_point_extension_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (F : Type) [Field F] [Algebra T.Fr F], letI := io.toAlgebra; letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra; ∀ (φ : T.Fr →ₐ[c.F] F), φ.toRingHom = algebraMap T.Fr F → ∀ (yF : FrPt Xo c F), FrMap φ y.1 yF → ∀ (a : ((E →+* ℂ) × ℕ → ℕ)) (n : ℕ) (xx : Fin n → Dw.La) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∀ Fs : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo yF.x)), (∀ i, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) yF.s (levPt Xo yF.x (xx i)) (Fs i)) → ∀ f, IsThRule Xo c nab xx Pp f → algebraMap T.Fr F (evI y f) = thExpr Xo c nab yF Pp Fs := by
  first | exact @GlobalTheory.PtTie.evI_eq_thExpr_ext | exact GlobalTheory.PtTie.evI_eq_thExpr_ext | (intros; apply GlobalTheory.PtTie.evI_eq_thExpr_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TranslateThetaFrameGermEqUnitMulBoxProduct
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.ColumnSplit

theorem val_eq_zero_of_pow_eq_one {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {u : F} {m : ℕ} (hm : 0 < m)
    (h : u ^ m = 1) : v u = 0 := by
  have h1 : m • v u = 0 := by rw [← AddValuation.map_pow, h, AddValuation.map_one]
  induction hv : v u using WithTop.recTopCoe with
  | top =>
    rw [hv] at h1
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    simp [succ_nsmul] at h1
  | coe a =>
    rw [hv, ← WithTop.coe_nsmul, WithTop.coe_eq_zero] at h1
    simpa [hm.ne'] using h1

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ τ : Frames P.U.LG.L (κ := Fin 1 × Fin (chD C.ch)) C.xT, τ.Gen → IsEL P C.xT C.actT C.eT C.wPT τ → ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → ∀ (θ₁ : Fam P.D.toPre F 1) (θα₁ : Fam P.D.toPre F (1 * N)), ThFrame P.D ϖ F θ₁ → PullAl P.D F P.oD α 1 N θ₁ θα₁ → ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), ThFrame D' ϖ F θ → PullAl D' F oD' α 1 N θ θα → ∀ (p : QkPt D'.toPre F (1 * N)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * N)) (q : ℕ) (e : 1 * N = q) (σ' : U'.toUnifPre.SecGF F q) (h : PS F n (chD C.ch)), w.IsGen → ζ ≠ 0 → FinOrd D' F (1 * N) p w ζ → QkToAkU U'.toUnifPre F (1 * N) p x → PhiRel D'.toPre F (1 * N) p w θα t₀ → Fam.IsSmul D'.toPre F ζ t₀ t → U'.toUnifPre.ExpandsG F q σ' (PowGerm.famCast (Dp := D'.toPre) (F := F) e t) → IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' h → ∃ (u : F) (p₁ : Fin n → QkPt P.D.toPre F (1 * N)) (w₁ : ∀ i, LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p₁ i).g.b) (DegPre.lineε (1 * N)))) (ζ₁ : Fin n → F) (r₀ r : Fin n → Fam P.D.toPre F (1 * N)) (σ₁ : Fin n → P.U.toUnifPre.SecGF F q) (f : Fin n → PS F 1 (chD C.ch)), v u = 0 ∧ h = u • boxSer f ∧ ∀ i, (w₁ i).IsGen ∧ FinOrd P.D F (1 * N) (p₁ i) (w₁ i) (ζ₁ i) ∧ P.ToA F (1 * N) (p₁ i) (x ≫ pA.pr i) ∧ PhiRel P.D.toPre F (1 * N) (p₁ i) (w₁ i) θα₁ (r₀ i) ∧ Fam.IsSmul P.D.toPre F (ζ₁ i) (r₀ i) (r i) ∧ P.U.toUnifPre.ExpandsG F q (σ₁ i) (PowGerm.famCast (Dp := P.D.toPre) (F := F) e (r i)) ∧ GermA P.U.toUnifPre (κ := Fin 1 × Fin (chD C.ch)) C.xT τ F q (σ₁ i) (f i) := by
  obtain ⟨hL, hL2, -, hL4, -⟩ := GlobalTheory.firstFiveLaws
  have hT := GlobalTheory.twistBaseChange_and_valuation_statements.1
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C hTr P hTor _ ϖ hϖ Q _ F _ _ _ _ _ _ v hv n D' A' G' _ _ pD pA pG U' PU _ oD' hx hact τ hτ hEL
    α N hN hα θ₁ θα₁ hθ₁ hθα₁ θ θα hθ hθα p w ζ x t₀ t q e σ' h hw _ hfin hpx hΦt hsm hexp hgerm
  subst e
  have hG := hL.globalFns
  have hk : 1 ≤ 1 * N := by omega
  haveI : CharZero T.V := (algebraMap T.V F).charZero
  obtain ⟨p₁, hp, hp₁⟩ := UnboxQk.exists_isBoxQk_toA hL hL2 hL4 hT T.V E H C.I.G P hTor n D' A' G' pD pA pG U' PU F
    (1 * N) hk p
  have hw₁ : ∀ i, ∃ w₁ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p₁ i).g.b)
      (DegPre.lineε (1 * N))), w₁.IsGen := fun i =>
    H1.ClosedPointWeilPower.gen_local_linComb P.D.toPre.P.L P.D.toPre.P.isLB _ _
  choose w₁ hw₁ using hw₁
  choose ζ₁ _ hζ₁ using fun i => H1.finOrdExists_of (phiFun_of hL) (H1.phiPow_of hL) T.V P.D F (1 * N) hk (p₁ i) (w₁ i)
    (hw₁ i)
  choose Φ₁ hΦ₁ using fun i => phiFun_of hL T.V _ P.D F (1 * N) hk (p₁ i) (w₁ i) (hw₁ i)
  obtain ⟨τ₀, hτ₀, hEL₀, hT₀⟩ := frame1St_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT
    C.wPT C.chartT C.frameT C.primT
  have hLB : P.U.LG.L.IsLB := (congrArg RigLB.L P.bundle).symm ▸ C.I.G.PP.isLB
  obtain rfl : τ = τ₀ := funext fun m => TorusExt.gen_ext_val hLB (hτ m) (hτ₀ m) fun y J hJ =>
    (hEL m y J hJ).trans (hEL₀ m y J hJ).symm
  have hz₁ := GlobalTheory.T.universal_statement E H Dw l Xo c T io y C
  obtain ⟨gm₁, -, hgm₁⟩ := PairingLinear.exists_germ_linearMap hL hL2 hL4 hT T.V P.D P.A C.I.G.G P.U _ _ hz₁ τ hτ
    (hT₀ hTr) F (1 * N) hk
  choose σ₁ hσ₁ hf using fun i => hgm₁ (ζ₁ i • Φ₁ i θα₁)
  obtain ⟨bx₁, hbx₁⟩ := exists_boxFam_multilinear hG T.V n P.D.toPre D'.toPre pD F 1
  obtain ⟨bx, hbx⟩ := exists_boxFam_multilinear hG T.V n P.D.toPre D'.toPre pD F (1 * N)
  obtain ⟨u₀, hu₀, hθu⟩ := GlobalTheory.T.thetaFrameFamilies_differ_by_valuationZero_unit T.V ϖ hϖ D' F v hv _ θ
    (BoxFrame.main T.V ϖ hϖ n P.D D' pD F θ₁ _ hθ₁ ((hbx₁ _ _).2 rfl)) hθ
  have hw0 : TraceFormTwistIso D'.toPre oD' H.w0 := GlobalTheory.PsiWZeroProd.main T.V n P.D.toPre D'.toPre pD (𝓞 E)
    (fun a x => funext fun i => hx a x i) P.oD oD' hact H.w0 P.w0
  obtain ⟨pl, -, hpl⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw0 α N 1 hN le_rfl hα
  have hpull := BoxPull.main hL hL2 hL4 hT T.V n P.D D' pD F (𝓞 E) hx P.oD oD' hact α N 1 hN le_rfl hα
    (fun _ => θ₁) (fun _ => θα₁) _ _ (fun _ => hθα₁) ((hbx₁ _ _).2 rfl) ((hbx _ _).2 rfl)
  have hθα' : θα = u₀ • bx fun _ => θα₁ := by
    rw [(hpl _ _).1 hθα, (hpl _ _).1 hpull, (isSmul_iff _ _ _).1 hθu, map_smul]
  obtain ⟨w', hw', hΦ⟩ := BoxPhi.phiRel_box hG T.V n P.D.toPre D'.toPre pD F (1 * N) p p₁ hp w₁ hw₁
  have hfin' := finOrd_box hL hL2 hL4 hT T.V n P.D D' pD F (1 * N) hk p p₁ hp w₁ w' hw₁ hw' hΦ ζ₁ hζ₁
  obtain ⟨u₁, ⟨m, hm, hum⟩, hu₁⟩ := GlobalTheory.T.finiteOrder_thetaOperators_ratio_rootOfUnity T.V ϖ hϖ D' F (1 * N) hk p w' w (∏ i, ζ₁ i) ζ hw' hw hfin' hfin
  obtain ⟨Φ', hΦ'⟩ := phiFun_of hL T.V _ D' F (1 * N) hk p w' hw'
  have hbΦ : bx (fun i => Φ₁ i θα₁) = Φ' (bx fun _ => θα₁) :=
    (hΦ' _ _).1 (hΦ _ _ _ _ (fun i => (hΦ₁ i _ _).2 rfl) ((hbx _ _).2 rfl) ((hbx _ _).2 rfl))
  have ht : t = (u₁ * u₀) • bx fun i => ζ₁ i • Φ₁ i θα₁ := by
    rw [(isSmul_iff _ _ _).1 (hu₁ θα _ _ t₀ t ((hΦ' _ _).2 rfl) ((isSmul_iff _ _ _).2 rfl) hΦt hsm), hθα', map_smul,
      MultilinearMap.map_smul_univ, hbΦ, smul_comm (∏ i, ζ₁ i) u₀, smul_smul]
  obtain ⟨τn, hτn, hτT, hiff⟩ := frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT
    C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hz := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n _ pG C.xT hz₁
  obtain ⟨gm, hgm, hgmex⟩ := PairingLinear.exists_germ_linearMap hL hL2 hL4 hT T.V D' A' G' U' _ _ hz τn hτn (hτT hTr)
    F (1 * N) hk
  obtain ⟨σb, hσb, -⟩ := hgmex (bx fun i => ζ₁ i • Φ₁ i θα₁)
  have hbox := boxGermSt_holds hL hL2 hL4 hT E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT
    C.eT C.wPT C.chartT C.frameT C.primT τ hτ hEL n D' A' G' pD pA pG U' PU F (1 * N) hk σ₁ _ _ σb _
    (fun i => ⟨hσ₁ i, hf i⟩) ((hbx _ _).2 rfl) hσb
  refine ⟨u₁ * u₀, p₁, w₁, ζ₁, fun i => Φ₁ i θα₁, fun i => ζ₁ i • Φ₁ i θα₁, σ₁, fun i => gm₁ (ζ₁ i • Φ₁ i θα₁), ?_, ?_,
    fun i => ⟨hw₁ i, hζ₁ i, hp₁ x hpx i, (hΦ₁ i _ _).2 rfl, (isSmul_iff _ _ _).2 rfl, hσ₁ i, hf i⟩⟩
  · rw [AddValuation.map_mul, hu₀, val_eq_zero_of_pow_eq_one v hm hum, add_zero]
  · rw [hgm t σ' h hexp ((hiff F _ σ' h).1 hgerm), hgm _ σb _ hσb ((hiff F _ σb _).1 hbox), ht, map_smul]

end GlobalTheory.ColumnSplit
end
end

