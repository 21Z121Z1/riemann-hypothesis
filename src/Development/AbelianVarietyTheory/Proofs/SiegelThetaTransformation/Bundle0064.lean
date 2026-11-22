import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0063
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsVacuaInnerEqConstMulTestInnerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vacua_inner_eq_const_mul_testInner : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∃ a : ℂ, a ≠ 0 ∧ ∀ B, C.IsB B → ∀ φ φ' : TF S.rank C.g, SW.IsSB φ → SW.IsSB φ' → ipO μ 𝓕 (C.Th (C.xB B) φ) (C.Th (C.xB B) φ') = a * ip φ φ' := by
  first | exact @GlobalTheory.KerVacIp.ip_vacua | exact GlobalTheory.KerVacIp.ip_vacua | (intros; apply GlobalTheory.KerVacIp.ip_vacua <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatticeVacuaTensorCorrespondLineStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeVacua_tensor_correspond_line : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ w : D.host.E, IsIntegral ℤ w → w + cc w = 1 → IdemTwo w → ∀ (M : ℕ), ∀ Λ ∈ Vset D.host.E S.rank M, ∀ L : Lt D.host.E T.rank, SelfD C.X L → (∀ x ∈ C.X.dom, ∀ φ : TF S.rank C.g, SW.IsSB φ → (IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) (C.Th x φ) ↔ ∀ y ∈ tens Λ L, epsW C.X w y • heisG C.X C.bas y φ = φ)) ∧ ∀ B, C.IsB B → ∀ v, IsVac C.X C.bas w (tens Λ L) v → ∀ f, C.IsTh f → C.IsFock B f → IsLatVac (heisO C.ψ S T) (hatA S T (tens Λ L)) f → ∃ t : ℂ, f = t • (C.Th (C.xB B) v) := by
  first | exact @GlobalTheory.Ker.latVac_th_line | exact GlobalTheory.Ker.latVac_th_line | (intros; apply GlobalTheory.Ker.latVac_th_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilRepRationalPointsThetaFunctionsFockStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_rationalPoints_thetaFunctions_fock : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → (∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, C.IsTh f → ∀ w, om (γ, γ') f w = f (actO S T γ⁻¹ γ'⁻¹ w)) ∧ ∀ (ga : GL (Fin T.rank) D.host.E) (γ : GA D T), IsRatOf T ga γ → ∀ φ : TF S.rank C.g, SW.IsSB φ → (∀ x ∈ C.X.dom, om (1, γ) (C.Th x φ) = C.Th (lact ga x) (wG C.X C.bas C.idx ga φ)) ∧ ∀ B, C.IsB B → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, om (1, γ) (C.fvec B (C.Th (C.xB B) φ) Q) = C.fvec (C.mvB γ B) (C.Th (C.xB (C.mvB γ B)) (wG C.X C.bas C.idx ga φ)) Q := by
  first | exact @GlobalTheory.Ker.OmRat.om_rat | exact GlobalTheory.Ker.OmRat.om_rat | (intros; apply GlobalTheory.Ker.OmRat.om_rat <;> assumption)
end

