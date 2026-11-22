import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2730
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2743
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0044
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0175
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0178
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueTranslateDivisorLevelIntegralChart
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2731
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2380
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2414
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2408
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2563
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1StructureBaseChangeExtensionStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h1_structure_base_change_extension : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0), ∃ e : ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → (GlobalTheory.CatCoh.H1 (OAff s₁) ≃+ GlobalTheory.CatCoh.H1 (ext R₁ (OAff s₀))), ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (Y₀ Y₁ : Scheme.{0}) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)), f₁ ≫ pr = pr' ≫ f₀ → ∀ c c', IsExtendedPullbackDegOne R₁ h₀ (e X₀ X₁ s₀ s₁ pr hp c) (e Y₀ Y₁ t₀ t₁ pr' hp' c') → IsPullO h₁ c c' := by
  first | exact @GlobalTheory.Obs.BC.extO1 | exact GlobalTheory.Obs.BC.extO1 | (intros; apply GlobalTheory.Obs.BC.extO1 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H2StructureBaseChangeExtensionStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h2_structure_base_change_extension : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0), ∃ e : ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → (GlobalTheory.CatCoh.H2 (OAff s₁) ≃+ GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))), ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (Y₀ Y₁ : Scheme.{0}) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) (hp' : IsPullback pr' t₁ t₀ (spMap (algebraMap R₀ R₁))) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)), f₁ ≫ pr = pr' ≫ f₀ → ∀ c c', IsExtendedPullbackDegTwo R₁ h₀ (e X₀ X₁ s₀ s₁ pr hp c) (e Y₀ Y₁ t₀ t₁ pr' hp' c') → IsPullbackH2Structure h₁ c c' := by
  first | exact @GlobalTheory.Obs.extCoef_two_equiv | exact GlobalTheory.Obs.extCoef_two_equiv | (intros; apply GlobalTheory.Obs.extCoef_two_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueIntegralGermFramePowerCharZeroStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.PowGerm GlobalTheory.PtTie GlobalTheory.RefSum
open GlobalTheory.ThetaLeast

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_value_integral_germ_frame_power_charZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), CharZero (IsLocalRing.ResidueField T.V) → letI := io.toAlgebra; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n k k' : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : PS T.Fr n (chD C.ch), IsIntPS T f → ∃ f' : PS T.Fr n (chD C.ch), IsIntPS T f' ∧ nabValN C.ch.B T.Fr C.ch.h H.w0 k f (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) = nabValN C.ch.B T.Fr C.ch.h H.w0 k' f' (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) := by
  first | exact @GlobalTheory.FramePower.exists_nabValN_eq_of_harmonic | exact GlobalTheory.FramePower.exists_nabValN_eq_of_harmonic | (intros; apply GlobalTheory.FramePower.exists_nabValN_eq_of_harmonic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueTranslateDivisorLevelIntegralChartStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.PowGerm GlobalTheory.PtTie GlobalTheory.RefSum
open GlobalTheory.ThetaLeast

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicValue_translate_divisor_level_integral_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G), P.TorsionIso → CharZero (IsLocalRing.ResidueField T.V) → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (n : ℕ) (D' : DegData T.V (IsLocalRing.maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (IsLocalRing.maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ (α : 𝓞 E) (N : ℕ), N ∣ l.M → α * star α = (N : 𝓞 E) → l.Mb ≤ Ideal.span {star α} → ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), ThFrame D' ϖ F θ → PullAl D' F oD' α 1 N θ θα → ∀ (p : QkPt D'.toPre F (1 * N)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * N)) (σ' : U'.toUnifPre.SecGF F (1 * N)) (h : PS F n (chD C.ch)), w.IsGen → ζ ≠ 0 → FinOrd D' F (1 * N) p w ζ → QkToAkU U'.toUnifPre F (1 * N) p x → PhiRel D'.toPre F (1 * N) p w θα t₀ → Fam.IsSmul D'.toPre F ζ t₀ t → U'.toUnifPre.ExpandsG F (1 * N) σ' t → IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (1 * N) σ' h → (∀ k, x ≫ pA.pr k ≫ P.oA.act (star α) = 1) → letI := io.toAlgebra; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (Pp : MvPolynomial (LtN Dw n) c.F), Pp ∈ harmA c a n → ∃ (xx : Fin n → Dw.La) (u : F), 0 ≤ v u ∧ ∀ f, IsThRule Xo c nab xx Pp f → nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * N) h (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map ((algebraMap T.Fr F).comp io) Pp) = u * algebraMap T.Fr F (evI y f) := by
  first | exact @GlobalTheory.DivLevel.harmonicValue_translate_dvd | exact GlobalTheory.DivLevel.harmonicValue_translate_dvd | (intros; apply GlobalTheory.DivLevel.harmonicValue_translate_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasChainW
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

namespace GlobalTheory.BundleChernComparison

def LocalW {D : D7} {p : ℕ} [Fact p.Prime] {N : ℕ} {rk : Emb D p → ℕ} (M : DV.Mdl D p N rk) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ m : ℕ, m + k = dimFl D.what₂.Tau N + 1 → ∀ Q : MvPolynomial M.Z.LB ℚ, Q.IsHomogeneous m →
    chk M.lieW k (evQ _ Q) + chk M.omW k (evQ _ Q) =
      (((p : ℝ) ^ k - 1)⁻¹ - ((p : ℝ) - 1)⁻¹) * chDiv M.lieW.x (k - 1) (evQ _ Q)

def HasChainW {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime}
    {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (jc : KW p →+* ℂ) : Prop :=
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  haveI := charP_residueField_of_mem_nonunits z.Z.i.c hp hW
  ∀ c : (nmodel z.Z).Comp, ∃ (B : Vert.Model (z.Z.i.c.V W)) (f : Vert.Model.Hom B ((nmodel z.Z).comp c))
    (Ch : Chain p B (id : Unit → Unit) 1), GlobalTheory.IsNormalScheme B.X ∧ f.relDim = 0 ∧
      (Ch.lw ()).r = D.R.f * N ∧ (Ch.oo ()).r = D.R.f * N ∧
      Reads p (mdlOf z jc).lieW (fun x => picSymPull f.f (picSymPull ((nmodel z.Z).compι c) x))
        (fun d => Vert.Model.vPullQ f.comp_str (NModel.vResQ c d))
        (haveI := (Ch.lw ()).iso; (Vert.Model.GenIso.ofHom (Ch.lw ()).ψ).symm) ∧
      Reads p (mdlOf z jc).omW (fun x => picSymPull f.f (picSymPull ((nmodel z.Z).compι c) x))
        (fun d => Vert.Model.vPullQ f.comp_str (NModel.vResQ c d))
        (haveI := (Ch.oo ()).iso; Vert.Model.GenIso.ofHom (Ch.oo ()).ψ)

def TermW {D : D7} (Y : ShimX D.what₂.Tau) (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] (w : ι → ℝ)
    (jc : ι → (KW p →+* ℂ)) (M : ∀ la, DV.Mdl D p Y.N (rkOf (PsiOf D (jc la)) Y.N Y.j))
    (rt : ∀ la, Bool × Rt D.what₂.Tau Y.N → (M la).Z.LB) : Prop :=
  (∑ la, w la = 1) ∧ ∀ (Sx : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ (k m : ℕ), 1 ≤ k → m + k = dimFl D.what₂.Tau Y.N + 1 →
    ∀ G : MvPolynomial (Vm D.what₂.Tau Y.N) ℚ, G.IsWeightedHomogeneous (wt D.what₂.Tau Y.N) m →
      Y.arMix Sx R p (dCh D.what₂.Tau Y.N k * toR G) = Real.log p * ∑ la, w la *
        ((chk (M la).lieW k (evC (M la) (rt la) G) + chk (M la).omW k (evC (M la) (rt la) G)) / ((M la).cov : ℝ))

def ConsW {D : D7} {p : ℕ} [Fact p.Prime] {N : ℕ} {rk : Emb D p → ℕ} (M : DV.Mdl D p N rk)
    (rt : Bool × Rt D.what₂.Tau N → M.Z.LB) (j : ℕ) (chern : MvPolynomial (Rt D.what₂.Tau N) ℝ →ₗ[ℝ] ℝ) : Prop :=
  ∀ m : ℕ, m + 1 = dimFl D.what₂.Tau N → ∀ G : MvPolynomial (Vm D.what₂.Tau N) ℚ,
    G.IsWeightedHomogeneous (wt D.what₂.Tau N) m →
    chDiv M.lieW.x 1 (evC M rt G) / (M.cov : ℝ) = chern (chLieA D N j 1 * collapse D N (toR G))

def AtAll (Q : ∀ (D : D7) (O : Setup D) (p : ℕ) [Fact p.Prime] (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits)
    (_ : KW p →+* ℂ) (_ : AdmAt O.S O.κ (Fact.out : p.Prime) hW), Prop) : Prop :=
  ∀ (D : D7) (O : Setup D), O.Core → ∀ (p : ℕ) [Fact p.Prime] (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits)
    (jc : KW p →+* ℂ), Pin W jc → ∀ z : AdmAt O.S O.κ (Fact.out : p.Prime) hW, Q D O p W hW jc z

def ChainWSt : Prop := AtAll fun _ _ _ _ _ _ jc z => HasChainW z jc

def ConsWSt : Prop := AtAll fun _ O _ _ _ _ jc z => ConsW (mdlOf z jc) (rootOf z jc) O.Y.j O.Y.chern

def TermWSt : Prop := ∀ (D : D7) (O : Setup D), O.Core → ∀ (p : ℕ) [Fact p.Prime],
  ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (W : ι → ValuationSubring ℂ) (hW : ∀ la, (p : ℂ) ∈ (W la).nonunits)
    (jc : ι → (KW p →+* ℂ)) (z : ∀ la, AdmAt O.S O.κ (Fact.out : p.Prime) (hW la)), (∀ la, Pin (W la) (jc la)) ∧
    TermW O.Y p w jc (fun la => mdlOf (z la) (jc la)) (fun la => rootOf (z la) (jc la))

end GlobalTheory.BundleChernComparison

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDivOfHasDivThetaSymmetricFunctionsDegreeFacto
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem hasDiv_of_hasDiv_symTup : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (N : ℕ)
    (c : Fin N → Ω), Geo.Tor.IsNormalScheme M.Z → M.HasDiv (symTup c) → M.HasDiv c := by
  intro k Ω _ _ _ M N c hn hd z
  obtain ⟨j, he, hdiv⟩ := hd z
  haveI := RatModel.isIntegrallyClosed_O hn z
  set D := N.factorial with hD
  set e := symTup c j with he'
  have hD1 : 1 ≤ D := Nat.factorial_pos N

  haveI : IsFractionRing (M.O z).toSubring Ω := inferInstanceAs (IsFractionRing (M.O z) Ω)
  haveI : IsIntegrallyClosed (M.O z).toSubring := inferInstanceAs (IsIntegrallyClosed (M.O z))
  haveI hcl : IsIntegrallyClosedIn (M.O z).toSubring Ω :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn Ω).1 inferInstance
  have h1 : ∀ a, c a ^ D / e ∈ M.O z := by
    intro a
    have hmem : c a ^ D / e ∈ ⨅ V : {V : ValuationSubring Ω // (M.O z).toSubring ≤ V.toSubring}, V.1.toSubring := by
      refine Subring.mem_iInf.2 fun V => ?_
      refine pow_div_mem_of_esymm_pow_div_mem Ω V.1 (Fin N) c D e he (fun i hi1 hi2 => ?_) a
      simp only [Fintype.card_fin] at hi2
      refine ⟨Nat.dvd_factorial hi1 hi2, V.2 ?_⟩
      have := hdiv ⟨i - 1, by omega⟩
      simp only [symTup, Nat.sub_add_cancel hi1] at this
      exact this
    rw [← Subring.eq_iInf_of_isIntegrallyClosedIn] at hmem
    exact hmem
  haveI : IsLocalRing (M.O z).toSubring := inferInstanceAs (IsLocalRing (M.O z))
  obtain ⟨a, ha, hea⟩ := exists_esymm_pow_div_mem_of_isLocalRing Ω (M.O z).toSubring (Fin N) c D ((j : ℕ) + 1) e hD1
    (by omega) (Nat.dvd_factorial (by omega) (by omega)) he rfl h1
  refine ⟨a, ha, fun b => ?_⟩
  have hpow : (c b / c a) ^ D ∈ M.O z := by
    have : (c b / c a) ^ D = (c b ^ D / e) * (e / c a ^ D) := by
      rw [div_pow, div_mul_div_cancel₀ he]
    rw [this]
    exact mul_mem (h1 b) hea
  have hint : IsIntegral (M.O z) (c b / c a) :=
    IsIntegral.of_pow (by omega) (isIntegral_algebraMap (R := M.O z) (x := ⟨_, hpow⟩))
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact hy ▸ y.2

end GlobalTheory.UMin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingTransportOfCmTypeEmbeddingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasMarkingTransport_of_cmType_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (e : c.F →+* ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsClosed (U : Set (Xo.XF c)) → IsOpenImmersion io → Set.range io = compactOf Y U → io ≫ genStr Y = B.str → 1 ≤ D.p + D.q → Formalism.L2.PjFree.GoodEmb c e → HasTransport Xo c U e := by
  first | exact @GlobalTheory.DetLine.GoodTransport.hasTransport_of_goodEmb | exact GlobalTheory.DetLine.GoodTransport.hasTransport_of_goodEmb | (intros; apply GlobalTheory.DetLine.GoodTransport.hasTransport_of_goodEmb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepOfFiniteProductAlgebras
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.ProdGlue

theorem hasRepAF_of_disjoint_cover {S : Scheme.{0}} (A : Over S) [GrpObj A] (g : ℕ) {κ : Type} [Finite κ] (X : Over S)
    (V : κ → X.left.Opens) (hcov : ⨆ i, V i = ⊤) (hdisj : Pairwise fun i i' => Disjoint (V i) (V i'))
    (h : ∀ i, HasRepAF A g (Over.mk ((V i).ι ≫ X.hom))) : HasRepAF A g X := by
  choose B b P hP using h
  let Bt : Over S := Over.mk (Sigma.desc fun i => (B i).hom)
  let j : ∀ i, B i ⟶ Bt := fun i => Over.homMk (Sigma.ι (fun i => (B i).left) i) (by simp [Bt])
  have hjl : ∀ i, (j i).left = Sigma.ι (fun i => (B i).left) i := fun i => rfl
  haveI : ∀ i, IsOpenImmersion (j i).left := fun i => by rw [hjl]; infer_instance
  have hjc : ⨆ i, (j i).left.opensRange = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk fun i => (B i).left).surjective x
    rw [sigmaMk_mk]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, y, by rw [hjl]⟩
  have hjd : Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange := fun i i' hii' => by
    simp only [hjl]; exact disjoint_opensRange_sigmaι _ i i' hii'
  let bt : Bt ⟶ X := Over.homMk (Sigma.desc fun i => (b i).left ≫ (V i).ι) (by
    refine Sigma.hom_ext _ _ fun i => ?_
    simp only [Bt, Over.mk_hom, colimit.ι_desc_assoc, Cofan.mk_ι_app, Discrete.functor_obj_eq_as, colimit.ι_desc, Category.assoc]
    exact Over.w (b i))
  have hb : ∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι := fun i => by
    ext1; simp [j, bt]

  have hk : ∀ i, IsOpenImmersion (A ◁ j i).left := fun i => (GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd A (j i)).1
  have hkc : ⨆ i, (A ◁ j i).left.opensRange = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : (snd A Bt).left z ∈ ⨆ i, (j i).left.opensRange := by rw [hjc]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    change z ∈ Set.range (A ◁ j i).left
    rw [(GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd A (j i)).2]
    exact hi
  have hkd : Pairwise fun i i' => Disjoint (A ◁ j i).left.opensRange (A ◁ j i').left.opensRange := by
    intro i i' hii'
    rw [disjoint_iff, eq_bot_iff]
    rintro z ⟨h1, h2⟩
    change z ∈ Set.range (A ◁ j i).left at h1
    change z ∈ Set.range (A ◁ j i').left at h2
    rw [(GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd A (j i)).2] at h1
    rw [(GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd A (j i')).2] at h2
    exact (disjoint_iff.1 (hjd hii')).le ⟨h1, h2⟩
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_cechPicard_glue_finite_disjoint_cover (fun i => (A ◁ j i).left) hkc hkd (fun i => cls (P i) (hP i).1.fam.isLB)
  obtain ⟨Pt, hPt, rfl⟩ := cls_surj d
  have hPi : ∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i) := fun i =>
    (cls_eq_iff (pull_isLB hPt _) (hP i).1.fam.isLB).1 ((cls_pull hPt _ _).trans (hd i))
  refine ⟨Bt, bt, Pt, ⟨GlobalTheory.T.additiveLineBundleFamily_of_disjoint_open_pieces A Bt B j hjc hjd P Pt (fun i => (hP i).1.fam) hPt hPi, fun T t N hN => ?_⟩, ?_, ?_⟩
  · obtain ⟨x, hx, hxN⟩ := GlobalTheory.T.exists_point_disjointUnion_representingAdditiveFamily A X V hcov hdisj Bt B j hjc hjd b bt hb P Pt (fun i => (hP i).1) hPt hPi T t N hN
    refine ⟨x, ⟨hx, hxN⟩, fun y hy => ?_⟩
    refine GlobalTheory.T.point_disjointUnion_representingFamily_unique A X V hcov hdisj Bt B j hjc hjd b bt hb P Pt (fun i => (hP i).1) hPt hPi T y x (hy.1.trans hx.symm) ?_
    rw [Same, ← cls_eq_iff (pull_isLB hPt _) (pull_isLB hPt _), ← (cls_eq_iff hN.isLB (pull_isLB hPt _)).2 hy.2,
      ← (cls_eq_iff hN.isLB (pull_isLB hPt _)).2 hxN]
  · exact GlobalTheory.T.properSmoothGeomConnected_sigmaDesc_disjoint_cover V hcov hdisj (fun i => (b i).left) g (fun i => (hP i).2.1)
  · exact GlobalTheory.T.finiteSetsInAffineOpen_finite_coproduct (fun i => (B i).left) (fun i => (hP i).2.2)

theorem hasRepAF_pi : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → ∀ (n : ℕ) (D : Fin n → Type) [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)], (∀ i, HasRepAF A g (Over.mk (spMap (algebraMap R (D i))))) → HasRepAF A g (Over.mk (spMap (algebraMap R (∀ i, D i)))) := by
  intro R _ A _ g _ n D _ _ h
  obtain ⟨V, hcov, hdisj, he⟩ := GlobalTheory.T.spec_pi_disjoint_open_cover_factors R n D
  exact hasRepAF_of_disjoint_cover A g (Over.mk (spMap (algebraMap R (∀ i, D i)))) V hcov hdisj
    (fun i => GlobalTheory.T.hasProperSmoothDualRepresentativeFinAffine_of_iso A g (he i).some.symm (h i))

end GlobalTheory.DualCon.ProdGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeOfLocalStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProperSmoothDualRepresentative_of_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (g : ℕ), IsAbelianScheme A → (∀ s : S, ∃ V : S.Opens, s ∈ V ∧ HasRep A g (Over.mk V.ι)) → HasRep A g (𝟙_ _) := by
  first | exact @GlobalTheory.DualCon.hasRep_of_local | exact GlobalTheory.DualCon.hasRep_of_local | (intros; apply GlobalTheory.DualCon.hasRep_of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLatticeBasisOfEigenvectorsStatement
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_lattice_basis_of_eigenvectors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p : ℕ) [Fact p.Prime]
    (l : Level H) (c : Coeff l) [Algebra c.F ℂ_[p]],
    letI := H.starRing; ∀ (Q : PtP E p) (τ : Psi H) (n : ℕ) (xx : Fin n → LieG Q.Gt) (g : Matrix (Fin n) (Fin n) ℂ_[p]),
      (∀ j, AvDefs.IsEig Q.Gt Q.oGt (embInt c Q.integers (conjEmb τ.1)) (xx j)) →
      IsLatBasis ℂ_[p] (htLat c Q (conjEmb τ.1)) (fun i => ∑ j, g i j • Q.bLie (xx j)) → ∀ a : Fin n → ℂ_[p],
        (∑ i, a i • ∑ j, g i j • Q.bLie (xx j) ∈ Q.latT ↔ ∀ i, ‖(1 : ℂ_[p]) * a i‖ ≤ 1) := by
  first | exact @GlobalTheory.eigconj_sum_mem_latT_iff | exact GlobalTheory.eigconj_sum_mem_latT_iff | (intros; apply GlobalTheory.eigconj_sum_mem_latT_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionOfRepStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermLBLeBySmallSection_of_rep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (a b a' b' : ℤ) (M M' : HermLB p) (f : X.functionField), P.Rep a b M → P.Rep a' b' M' → f ≠ 0 → f ∈ P.Bl (a - a') (b - b') 1 → Le M' M := by
  first | exact @GlobalTheory.HSNef.le_of_rep | exact GlobalTheory.HSNef.le_of_rep | (intros; apply GlobalTheory.HSNef.le_of_rep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateDifferenceSection
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem aH_left_π_ptMap {G' : Over (Sp O)} {π : G'.left ⟶ t.G.left}
    (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) {D : Type} [CommRing D] [Algebra O D]
    (a : Bt P' x0 hu →ₐ[O] D) :
    (ptMap a ≫ aH P' x0 hu hπ).left ≫ π = spMap (a.toRingHom.comp (inB P' x0 hu)) ≫ P'.u.left := by
  rw [Over.comp_left, Category.assoc, aH_left_π]
  change spMap a.toRingHom ≫ spMap (inB P' x0 hu) ≫ P'.u.left = _
  rw [GlobalTheory.HTMap.spc_assoc]

theorem str_of_alg {D : Type} [CommRing D] [Algebra O D] (a : Bt P' x0 hu →ₐ[O] D) :
    (a.toRingHom.comp (inB P' x0 hu)).comp P'.str = (algebraMap O D).comp x0 := by
  rw [RingHom.comp_assoc, inB_str, ← RingHom.comp_assoc]
  congr 1
  exact a.comp_algebraMap

theorem at_alg {D : Type} [CommRing D] [Algebra O D] (a : Bt P' x0 hu →ₐ[O] D) :
    P'.At ((algebraMap O D).comp x0) (spMap (a.toRingHom.comp (inB P' x0 hu)) ≫ P'.u.left)
      (a.toRingHom.comp (inB P' x0 hu)) :=
  ⟨str_of_alg P' x0 hu a, rfl⟩

theorem exists_mul_affine {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left}
    (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) {D : Type} [CommRing D] [Algebra O D]
    (a b : Bt P' x0 hu →ₐ[O] D) :
    ∃ z : specO O D ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 =
      (ptMap a ≫ aH P' x0 hu hg.1) * (ptMap b ≫ aH P' x0 hu hg.1) := by
  have ha := at_alg P' x0 hu a
  have hb := at_alg P' x0 hu b
  let w₁ : Over.mk ((specO O D).hom ≫ spMap x0 ≫ ξ) ⟶ t.G :=
    GlobalTheory.HTMap.mkPt _ (ha.over.trans (GlobalTheory.HTMap.spc_assoc _ _ _).symm)
  let w₂ : Over.mk ((specO O D).hom ≫ spMap x0 ≫ ξ) ⟶ t.G :=
    GlobalTheory.HTMap.mkPt _ (hb.over.trans (GlobalTheory.HTMap.spc_assoc _ _ _).symm)
  obtain ⟨β'', h''⟩ := GlobalTheory.HTMap.FP.At.mul (w := w₁) (w' := w₂) ha hb
  refine ⟨ptOf P' x0 hu β'' h''.1, ?_⟩
  refine Over.OverMorphism.ext (hg.1.hom_ext ?_ ?_)
  · rw [ptOf_aH_π, h''.2]
    exact hg.2 (specO O D) _ _ w₁ w₂ (aH_left_π_ptMap P' x0 hu hg.1 a).symm
      (aH_left_π_ptMap P' x0 hu hg.1 b).symm
  · rw [Over.w, Over.w]

end GlobalTheory.FinPartAt

namespace GlobalTheory.FinPartAt

theorem exists_mul_factor {O : Type} [CommRing O] {C : Type} [CommRing C] [Algebra O C] (S : Over (Sp O))
    (x y : S ⟶ specO O C) :
    ∃ c : S ⟶ specO O (C ⊗[O] C),
      c ≫ ptMap (Algebra.TensorProduct.includeLeft : C →ₐ[O] C ⊗[O] C) = x ∧
      c ≫ ptMap (Algebra.TensorProduct.includeRight : C →ₐ[O] C ⊗[O] C) = y := by
  have hxy : x.left ≫ (specO O C).hom = y.left ≫ (specO O C).hom := by rw [Over.w, Over.w]
  let l := pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom
  have hl : l ≫ (specO O (C ⊗[O] C)).hom = S.hom := by
    change (pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap O (C ⊗[O] C))) = _
    rw [Category.assoc, pullbackSpecIso_hom_base, ← Category.assoc]
    erw [pullback.lift_fst]
    exact Over.w x
  refine ⟨Over.homMk l hl, ?_, ?_⟩
  · refine Over.OverMorphism.ext ?_
    change (pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom)) = _
    rw [Category.assoc, pullbackSpecIso_hom_fst]
    erw [pullback.lift_fst]
  · refine Over.OverMorphism.ext ?_
    change (pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom)) = _
    rw [Category.assoc]
    erw [pullbackSpecIso_hom_snd]
    erw [pullback.lift_snd]

theorem exists_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) (G' : Over (Sp O)) [GrpObj G'] (π : G'.left ⟶ t.G.left) (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (S : Over (Sp O)) (x y : S ⟶ Hs P' x0 hu), ∃ z : S ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 = (x ≫ aH P' x0 hu hg.1) * (y ≫ aH P' x0 hu hg.1) := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu G' _ π hg S x y
  obtain ⟨c, hc₁, hc₂⟩ := exists_mul_factor S x y
  obtain ⟨z₀, hz₀⟩ := exists_mul_affine P' x0 hu hg
    (Algebra.TensorProduct.includeLeft : Bt P' x0 hu →ₐ[O] Bt P' x0 hu ⊗[O] Bt P' x0 hu)
    Algebra.TensorProduct.includeRight
  refine ⟨c ≫ z₀, ?_⟩
  rw [Category.assoc, hz₀, MonObj.comp_mul, ← Category.assoc, hc₁, ← Category.assoc, hc₂]

end GlobalTheory.FinPartAt
end
end

