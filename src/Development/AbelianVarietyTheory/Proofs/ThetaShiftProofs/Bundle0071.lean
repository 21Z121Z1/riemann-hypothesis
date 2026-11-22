import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0070
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcDatumFamilyFunctionalBoundedLinearOnCuspForStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmArcDatumFamily_functional_bounded_linear_on_cuspForms : Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (large₂ : SizeData₂ D), GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m → ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁), FamQ T j ka CR Tt cc K₁ d → ∃ φ : (recB h).Cusp j ka →ₗ[T.Q.c.F] K₁, (∀ F, φ F = cfOf d.yF d.μ d.jj F.1) ∧ @NumGood T.Q.c.F ((recB h).Cusp j ka) _ _ ((recB h).acgC j ka) ((recB h).modC j ka) {F | F ∈ (recB h).Mlat j ka} (fun σ F => (recB h).supN j ka σ F) (beOf D.host.E (nAt D j ka CR Tt cc) (absA (T.Q.Dw j) (wtA ka))) (CarchAt D j ka CR Tt cc) (BdegAt large₂ j ka CR Tt cc) K₁ _ _ _ φ := by
  first | exact @GlobalTheory.ArcCM.numGood_of_famQ | exact GlobalTheory.ArcCM.numGood_of_famQ | (intros; apply GlobalTheory.ArcCM.numGood_of_famQ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFamilyMemberFunctionalNeZeroStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_familyMember_functional_ne_zero : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r) (k : U.Comp) (Xx : DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ w : ℝ), ModelsAt Xo c → IsUnf U → l.A = 1 → 3 ≤ r → GlobalTheory.FrameNorm.HasPrinc U l.M → Dom a' n → (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → Xx.g = l.M → 0 < c₁ → ((absA Dw a' : ℝ) + (fdeg E : ℝ) * n + r ≤ w) → ∀ F ∈ sec Xo c a' n, (∀ k', rdU U F k' ∈ (U.X k').SS (laU U a' n k')) → rdU U F k ∉ (U.X k).SSgt (laU U a' n k) c₁ → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra c.F K₁) (d : ArcDatum Xo c K₁), Fam (nQ E r l.M Xx.NA Xx.NC c₁ w) (LaQ E r Dw.q l.M Xx.NA Xx.NC c₁ w) c₁ d ∧ cfOf d.yF d.μ d.jj F ≠ 0 := by
  first | exact @GlobalTheory.ArcDetect.exists_fam_cfOf_ne_zero | exact GlobalTheory.ArcDetect.exists_fam_cfOf_ne_zero | (intros; apply GlobalTheory.ArcDetect.exists_fam_cfOf_ne_zero <;> assumption)
end

