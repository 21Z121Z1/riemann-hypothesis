import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.BarTorsionGenerators
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SplitOfFactorisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TransvectionEq
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0021
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0091
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0094
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0101
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricLiftActsRootOfUnityOnExpansions
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormGeneratorIffPrincipal
section
noncomputable section

namespace GlobalTheory.NoCommonZeroCompare

section Quadratic

structure IsQuad {R : Type} [CommRing R] (c : R →+* R) (w : R) (k : ℤ) (d : ℕ) : Prop where
  prime : d.Prime
  four : 4 * k = 1 + d
  sq : w * w = w - k
  conj : c w = 1 - w
  span : ∀ x : R, ∃ a b : ℤ, x = a + b * w
  indep : ∀ a b : ℤ, (a : R) + b * w = 0 → a = 0 ∧ b = 0

variable {R : Type} [CommRing R] {c : R →+* R} {w : R} {k : ℤ} {d : ℕ}

theorem IsQuad.cc (h : IsQuad c w k d) (x : R) : c (c x) = x := by
  obtain ⟨a, b, rfl⟩ := h.span x
  simp [h.conj]

end Quadratic

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.BarTorsionGenerators GlobalTheory.HostCompare

section Level

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

end Level

section Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

end Points

section Record

variable {D : D7}

end Record

def LongOn (P : ∀ (D : D7) (T : Top D) (j : ℕ), WeightFamilies.Wt D j → ℕ → Prop) : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (α : 𝓞 D.host.E) (q : ℕ),
    P D T j w q → D.R.r ≤ w.n → IsJetLevel T.Q.l α q → 4 * WeightAlgebra.DF w + 4 ≤ q →
    ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
      NoCommonZero (T.Q.Xo j) T.Q.c σ (gens (T.Q.Xo j) T.Q.c (T.nab j) α (wtA w) w.n)

def IsFull (D : D7) (T : Top D) (j : ℕ) (w : WeightFamilies.Wt D j) (q : ℕ) : Prop :=
  q = T.Q.l.M ∧ LastPos (T.Q.Dw j) (wtA w)

def IsRest (D : D7) (T : Top D) (j : ℕ) (w : WeightFamilies.Wt D j) (q : ℕ) : Prop :=
  q = D.host.g 0 ∨ q = D.host.g 1 ∨ ¬ LastPos (T.Q.Dw j) (wtA w)

end GlobalTheory.NoCommonZeroCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerRosatiTauBalAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem powerRosati_tauBal_action : BoxRosatiSt ∧ BoxTauBalSt ∧ PowOActSt :=
  ⟨boxRosati, BoxTauLin.boxTauBal_of_linear allSixLaws.1.globalFns,
    powOAct_of_globalFns allSixLaws.1.globalFns⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricLiftActsRootOfUnityOnExpansionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_lift_acts_root_of_unity_on_expansions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∀ (q : ℕ), 1 ≤ q → ∀ (σ σ' : P.U.toUnifPre.SecGF F q) (hh hh' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (q : ℤ) (ptO Xo xF))) (s t₀ t : Fam P.D.toPre F q) (x : TFK (R := T.V) F ⟶ P.A.A) (b : ptO Xo xF ⟶ Xo.univ.t.G) (p : QkPt P.D.toPre F q) (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε q))) (ζ : F), SecTieF I P F xF q σ hh → SecTieF I P F xF q σ' hh' → P.U.toUnifPre.ExpandsG F q σ s → IsSymAct Xo.univ.t.G Xo.univ.t.PP q b hh hh' → PtTieF I P F xF x b → P.ToA F q p x → w.IsGen → FinOrd P.D F q p w ζ → PhiRel P.D.toPre F q p w s t₀ → Fam.IsSmul P.D.toPre F ζ t₀ t → ∃ (u : F) (t' : Fam P.D.toPre F q), (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ Fam.IsSmul P.D.toPre F u t t' ∧ P.U.toUnifPre.ExpandsG F q σ' t' := by
  first | exact @GlobalTheory.SymActExpansion.exists_expandsG_of_isSymAct | exact GlobalTheory.SymActExpansion.exists_expandsG_of_isSymAct | (intros; apply GlobalTheory.SymActExpansion.exists_expandsG_of_isSymAct <;> assumption)
end

