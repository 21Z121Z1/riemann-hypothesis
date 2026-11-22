import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0046
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsOpenSameModel
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0046
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0049
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0045
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsComponentOfModelChartsStatement
section
open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.Reg
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_component_of_modelCharts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.IsUnf U → ∀ (h : GenFrEx Xo c) (k : U.Comp), ∃ Z : Comp Xo c, ∀ (x : (U.X k).dom) (C : FChart h) (ψ : C.R →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap ψ C.y z → FrBor t z (U.un k x) → C.Z = Z := by
  first | exact @GlobalTheory.OneComp.exists_comp_of_charts | exact GlobalTheory.OneComp.exists_comp_of_charts | (intros; apply GlobalTheory.OneComp.exists_comp_of_charts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCountableFlagSpaceAtlasStatement
section
open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.Reg
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_countable_flagSpace_atlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (h : GenFrEx Xo c), ∃ (ι : Type) (_ : Countable ι) (C : ι → FChart h), ∀ (L : Type) [Field L] [Algebra c.F L] (y : FrPt Xo c L), ∃ (i : ι) (ψ : (C i).R →ₐ[c.F] L) (z : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ (C i).y z ∧ FrBor t z y := by
  first | exact @GlobalTheory.Reg.exists_countable_atlas | exact GlobalTheory.Reg.exists_countable_atlas | (intros; apply GlobalTheory.Reg.exists_countable_atlas <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCuspFormNonzeroEveryComponentStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspForm_nonzero_everyComponent : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (hG : GenFrEx (T.Q.Xo j) T.Q.c), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → (∃ g0 : (recB h.toLawsCore).Cusp j wF, (recPJ h j hj).NonZeroComp wF g0 ∧ ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z g0.1 ≠ 0) ∧ ∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u), (recPJ h j hj).NonZeroComp u F → (∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z F.1 ≠ 0) ∧ ∀ σ, GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp, ∃ x ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) F.1 k x ≠ 0 := by
  first | exact @GlobalTheory.RunJoin.exists_nonZeroComp_and_ne_zero | exact GlobalTheory.RunJoin.exists_nonZeroComp_and_ne_zero | (intros; apply GlobalTheory.RunJoin.exists_nonZeroComp_and_ne_zero <;> assumption)
end

