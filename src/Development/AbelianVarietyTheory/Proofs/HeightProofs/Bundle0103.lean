import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRealisationPrimeDataCurveLiftingStatement
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPrimeDataCurveLiftingHeightBounds
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunPrimeData

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_primeData_heights : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (CL : ℝ), FnAlgClosed (T.Q.Xo j) T.Q.c → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → 0 < CL → (∀ w : WeightFamilies.Wt D j, LAMwAt large₂ (recB h.toLawsCore) j w CL 2) → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → G.TiedTh S (gcR large₂ (recB h.toLawsCore)) → (∀ la, InBasis G la) → Real.log G.del ≤ 1041 * Zb D large₂ ^ 3 → CombBound G S (cc D large₂ C2 A2 7 wL) nus → ∃ Qf : ∀ la, LocalPointData (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) la, (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S (gcR large₂ (recB h.toLawsCore)) (prwR large₂) Tn) ∧ Heights Qf (gcR large₂ (recB h.toLawsCore)) (phR large₂ (recB h.toLawsCore) CL wL) (prwR large₂) (WeightFamilies.PPv D large₂ 200000 2) :=
  exists_primeData_heights_of GlobalTheory.T.heightInequalities_indefinite_liftIndex GlobalTheory.T.heightInequality_definite_liftIndex GlobalTheory.T.exists_realisationPrimeData_curve_lifting

end GlobalTheory.RunPrimeData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.MoreOfTiesB
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

theorem more_of_tiesB : ∀ (D : D7) (O : GlobalTheory.EX.OB.Obj D) (c : ℝ) (b : BdPt D O c),
    TiesB D O c b → FieldSmall D O.L → SingleIndexPlacesAreTwisted b → More b := by
  intro D O c b hT hS hW
  obtain ⟨hs, hr⟩ := hT
  refine ⟨hW, ?_, ?_⟩
  · exact GlobalTheory.Plug.coreTies_of_tied D _ _ _ _ O.L O.ex.errX b.T (R2 b) b.P.A3.A.μ0 hs.tied b.charW.base.lev hS
  · exact ⟨hs.series, hs.level, hs.data, hs.psi, hs.psiVal, hs.small, hs.types, hr⟩

end GlobalTheory.PlugPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.PathCoreConditionsOfSizeFreeConditions
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

theorem ties_core_of_tiesB : ∀ (D : D7) (O : GlobalTheory.EX.OB.Obj D) (c : ℝ) (b : BdPt D O c), TiesB D O c b → FieldSmall D O.L →
    CoreTies O.L O.ex.errX b.T b.R.toRealDat ∧ b.T.pb = b.R.C.P.pb ∧ GlobalTheory.GLq.ESerTie D ∧ b.LevelTie ∧ b.DataTie := by
  intro D O c b h hF
  obtain ⟨hT, -⟩ := h
  refine ⟨GlobalTheory.Plug.coreTies_of_tied D _ _ _ _ O.L O.ex.errX b.T b.R.toRealDat _ hT.tied b.charW.base.lev hF,
    hT.tied.core.pb, hT.types.eSerTie, hT.level, hT.data⟩

end GlobalTheory.PlugPt
end

