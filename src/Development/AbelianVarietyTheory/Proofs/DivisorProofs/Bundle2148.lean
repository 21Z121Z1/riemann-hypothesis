import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2127
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2099
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2128
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0083
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0929
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaValueValuationLeDivSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField
import Formalism.PieriBlockIdeals.PieriColumnMinors.RealLocalDeltaNabla
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioFieldDataConjugateStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toric_ratio_field_data_conjugate : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.Rows → Fitted (@Comparison₂) p CF d → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → (∃ (_ : IsCMField D.host.E) (_ : IsAbelianGalois ℚ D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (GlobalTheory.FunObj.SqNum.cmPhi D) ∧
    GlobalTheory.CMVal.IsBaseCond (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∧ ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ) → (∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → ∀ c : Option Bool,
    ∃ x, IsTor d.G i j s (fam d.G p.P.A3.A.μ0 i j c) x ∧ x ≠ 0 ∧ (∀ Λ, GlobalTheory.CMVal.IsHeckeL (fam d.G p.P.A3.A.μ0 i j c) Λ → x = Λ s) ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ → IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) Λ x)) → ∀ w : D.what₂.places.Pl, TwistedAt D w → ∀ (i j : Fin D.R.m) (s : ℕ) (Λ Λd : ℂ → ℂ), 1 ≤ s → s ≤ halfRank D i j →
    GlobalTheory.CMVal.IsHeckeL ((nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) * p.Tp.psi w) Λ → GlobalTheory.CMVal.IsHeckeL (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) Λd →
    ∃ (T₀ : ℂ) (ψc : PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) (T : (PicO (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) →* ℂˣ) → ℂ), IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) ∅ (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ∧
      IsToricSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (GlobalTheory.FunObj.SqNum.condF d.G.pl) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) T₀ ∧ T₀ ≠ 0 ∧ Λd s = T₀ ∧
      (∀ y, finPart (p.Tp.psi w) y = ψc (QuotientGroup.mk y)) ∧
      (∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsTwistedSum (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D 1 i j s) (condQ (GlobalTheory.FunObj.SqNum.condF d.G.pl) (GlobalTheory.ToricDenom.belowSet (ex.nch.Q w))) (nuH d.G p.P.A3.A.μ0 i j * p.R.C.delAt (D.what₂.places.resChar w)) ψ (T ψ)) ∧ Λ s = T ψc := by
  first | exact @GlobalTheory.ThmARatio.values_as_toric_sums | exact GlobalTheory.ThmARatio.values_as_toric_sums | (intros; apply GlobalTheory.ThmARatio.values_as_toric_sums <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfMemDualWeylLattice
section
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.DualWeylDeg

theorem weight_colW_apply {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (t : Fin N) :
    (Finsupp.weight (colW N N) m) t = ∑ a : Fin N, m (a, t) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, Pi.smul_apply, colW, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp only [Pi.single_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hb; simp; intro h; exact absurd h.symm hb
  · simp

theorem totalDegree_le_of_mem_dualWeyl : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O), f ∈ dualWeyl O N N ν → f.totalDegree ≤ ∑ a, ν a := by
  intro O _ N ν f hf
  have h1 : f ∈ weightedHomogeneousSubmodule O (colW N N) ν := (Submodule.mem_inf.mp hf).1
  rw [mem_weightedHomogeneousSubmodule] at h1
  rw [totalDegree]
  refine Finset.sup_le fun m hm => ?_
  have h2 : Finsupp.weight (colW N N) m = ν := h1 (mem_support_iff.mp hm)
  have h3 : m.sum (fun _ e => e) = ∑ t, ∑ a : Fin N, m (a, t) := by
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type, Finset.sum_comm]
  rw [h3]
  refine le_of_eq (Finset.sum_congr rfl fun t _ => ?_)
  rw [← weight_colW_apply, h2]

end GlobalTheory.DualWeylDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedFiniteDatumEqStandardPairSecondMemberStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translated_finite_datum_eq_standardPairSecondMember : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    ∀ t, IsThetaAt ψ (symplO A' WW) (heisO ψ A' WW) (cA D ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t)) (latO A' WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA'.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ fun _ => True) 1 (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac'
    (stdSnd (α t / β t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ideal S t) A.rank A' WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA'.β (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.β) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').f' t) := by
  first | exact @GlobalTheory.BotMoveSnd.snd_moved | exact GlobalTheory.BotMoveSnd.snd_moved | (intros; apply GlobalTheory.BotMoveSnd.snd_moved <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceStepFactorInverseAwayUnitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlace_stepFactor_inverse_awayUnit : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T)
    (Bs : Base D.host.F D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs → ∀ (v : Bs.P), v.1 ∈ (GlobalTheory.SqStep.chs G i j t).T →
    v.1 ∉ G.pl.S0 → ∀ (s : ℤˣ) (z : ℤ), ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) ≠ 0 → ∃ b : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) b ∧
      D.what₂.embLL b * ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) = 1 := by
  first | exact @GlobalTheory.SqTwist.twist_factor | exact GlobalTheory.SqTwist.twist_factor | (intros; apply GlobalTheory.SqTwist.twist_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedClassSumsRationalOfRayClassFieldsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open GlobalTheory.OntoChain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedClassSums_rational_of_rayClassFields : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (O : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)), R.Char F → IoExt R → R.LUnif → (∀ i, OMPins J R κ v₀ O i) → QGuard R → (∀ i, OneMapRowR J R κ v₀ O (fun _ => 1) i) → BaseLinks R F → RankRows ((R.toCx F).data F.cr false) → (∀ t, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t)) → TwistedRational R F (fun _ => 1) := by
  first | exact @GlobalTheory.TwistedRatBase.twistedRational_of_rayField | exact GlobalTheory.TwistedRatBase.twistedRational_of_rayField | (intros; apply GlobalTheory.TwistedRatBase.twistedRational_of_rayField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelCharacterIsTameHeckeUnramifiedStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedKernelCharacter_isTameHecke_unramified : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (e : AE D) (Ps : Finset (Pl D.host.E)) (yd : (AE D)ˣ), h ∈ GfC (Vc D i) → IsIdemSum e Ps → (∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∃ (ψ : Formalism.L2.Host.HChar D.host.E) (b : ℕ) (I : Type) (_ : Fintype I) (φs : I → D.host.E →+* ℂ) (n : I → ℤ), b ≠ 0 ∧ (∀ Q ∈ Ps, (b : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ ChrEq (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ψ ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → ψ.UnrAt Q) ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k : D.host.Fˣ, ψ.resFin (Q.under (𝓞 D.host.F)) k = 1) ∧ (∀ Q, ψ.TameAt Q) ∧ ψ.HasInf φs n := by
  first | exact @GlobalTheory.TwistedKernelChar.twisted_kernel_char | exact GlobalTheory.TwistedKernelChar.twisted_kernel_char | (intros; apply GlobalTheory.TwistedKernelChar.twisted_kernel_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedLiftInvariantExtensionLocalisation
section
open IsLocalRing

namespace GlobalTheory

theorem twisted_lift_to_localisation (A B A₂ : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    [CommRing A₂] [IsLocalRing A₂] (G : Type) [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G A B] [Algebra.IsInvariant A B G] (f : B →+* A₂) :
    IsLocalHom (f.comp (algebraMap A B)) → (∀ y : A₂, ∃ b s : B, IsUnit (f s) ∧ y * f s = f b) →
    (∀ b : B, f b = 0 → ∃ s : B, IsUnit (f s) ∧ s * b = 0) →
    ∀ (V' : Type) [CommRing V'] [IsLocalRing V'] (e₁ : A →+* V') (β : B →+* V'),
      IsLocalHom e₁ → β.comp (algebraMap A B) = e₁ →
      ∃ ev₂ : A₂ →+* V', IsLocalHom ev₂ ∧ ev₂.comp (f.comp (algebraMap A B)) = e₁ := by
  intro hfl hsurj hker V' _ _ e₁ β he₁ hβ
  set q : Ideal B := (maximalIdeal A₂).comap f with hq
  set c : Ideal B := (maximalIdeal V').comap β with hc
  haveI : q.IsPrime := Ideal.comap_isPrime f (maximalIdeal A₂)
  haveI : c.IsPrime := Ideal.comap_isPrime β (maximalIdeal V')
  have hqA : Ideal.under A q = maximalIdeal A := by
    ext a
    simp only [Ideal.under, Ideal.mem_comap, hq, mem_maximalIdeal, mem_nonunits_iff]
    rw [← RingHom.comp_apply, isUnit_map_iff (f.comp (algebraMap A B))]
  have hcA : Ideal.under A c = maximalIdeal A := by
    ext a
    simp only [Ideal.under, Ideal.mem_comap, hc, mem_maximalIdeal, mem_nonunits_iff]
    rw [← RingHom.comp_apply, hβ, isUnit_map_iff e₁]
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G c q (hcA.trans hqA.symm)
  set β' : B →+* V' := β.comp (MulSemiringAction.toRingHom G B σ⁻¹) with hβ'
  have hβ'q : ∀ b : B, b ∈ q ↔ ¬ IsUnit (β' b) := by
    intro b
    rw [hσ, Ideal.mem_pointwise_smul_iff_inv_smul_mem, hc, Ideal.mem_comap, mem_maximalIdeal,
      mem_nonunits_iff]
    rfl
  have hfq : ∀ b : B, b ∈ q ↔ ¬ IsUnit (f b) := by
    intro b
    rw [hq, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  have hβ'A : β'.comp (algebraMap A B) = e₁ := by
    rw [← hβ]
    ext a
    simp only [hβ', RingHom.comp_apply, MulSemiringAction.toRingHom_apply, smul_algebraMap]
  letI : Algebra B A₂ := f.toAlgebra
  haveI hloc : IsLocalization q.primeCompl A₂ := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨s, hs⟩
      have : s ∉ q := hs
      rw [hfq, not_not] at this
      exact this
    · intro z
      obtain ⟨b, s, hs, h⟩ := hsurj z
      have hs' : s ∈ q.primeCompl := by
        show s ∉ q
        rw [hfq, not_not]; exact hs
      exact ⟨(b, ⟨s, hs'⟩), h⟩
    · intro x y hxy
      have h0 : f (x - y) = 0 := by
        rw [map_sub]; exact sub_eq_zero.mpr hxy
      obtain ⟨s, hs, h⟩ := hker _ h0
      have hs' : s ∈ q.primeCompl := by
        show s ∉ q
        rw [hfq, not_not]; exact hs
      refine ⟨⟨s, hs'⟩, ?_⟩
      show s * x = s * y
      rw [mul_sub] at h
      exact sub_eq_zero.mp h
  have hunits : ∀ y : q.primeCompl, IsUnit (β' y) := by
    rintro ⟨s, hs⟩
    have : s ∉ q := hs
    rw [hβ'q, not_not] at this
    exact this
  have hcomp : (IsLocalization.lift hunits).comp f = β' :=
    IsLocalization.lift_comp (M := q.primeCompl) (S := A₂) hunits
  refine ⟨IsLocalization.lift hunits, ?_, ?_⟩
  · refine ⟨fun x hx => ?_⟩
    obtain ⟨b, s, hs, h⟩ := hsurj x
    have hsq : IsUnit (β' s) := by
      have : s ∉ q := by rw [hfq, not_not]; exact hs
      rw [hβ'q, not_not] at this
      exact this
    have hb : IsUnit (β' b) := by
      have h2 := congrArg (IsLocalization.lift hunits) h
      rw [map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, hcomp] at h2
      rw [← h2]
      exact hx.mul hsq
    have hfb : IsUnit (f b) := by
      have : b ∉ q := by rw [hβ'q, not_not]; exact hb
      rw [hfq, not_not] at this
      exact this
    rw [← h] at hfb
    exact isUnit_of_mul_isUnit_left hfb
  · rw [← RingHom.comp_assoc, hcomp, hβ'A]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSplittingCharacterUnitOffPlaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DilChi
open GlobalTheory.ChiUnit

theorem natCast_mem_conjPl {E : Type} [Field E] [NumberField E] [StarRing E] (P : Pl E) (m : ℕ) :
    (m : 𝓞 E) ∈ (conjPl P).asIdeal ↔ (m : 𝓞 E) ∈ P.asIdeal := by
  show Formalism.L2.DIV.starOHom (m : 𝓞 E) ∈ P.asIdeal ↔ _
  rw [map_natCast]

theorem conjO_mem_conjPl {E : Type} [Field E] [NumberField E] [StarRing E] (P : Pl E) (a : 𝓞 E) :
    Formalism.L2.DIV.starO a ∈ (conjPl P).asIdeal ↔ a ∈ P.asIdeal := by
  show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO a) ∈ P.asIdeal ↔ _
  rw [Formalism.L2.DIV.starO_starO]

theorem conjO_not_mem_sq {E : Type} [Field E] [NumberField E] [StarRing E] {P : Pl E} {a : 𝓞 E}
    (h : a ∉ P.asIdeal ^ 2) : Formalism.L2.DIV.starO a ∉ (conjPl P).asIdeal ^ 2 := by
  intro ha
  apply h
  have h1 : Formalism.L2.DIV.starOHom (Formalism.L2.DIV.starO a) ∈ Ideal.map Formalism.L2.DIV.starOHom ((conjPl P).asIdeal ^ 2) := Ideal.mem_map_of_mem _ ha
  rw [Ideal.map_pow] at h1
  have h2 : Ideal.map Formalism.L2.DIV.starOHom (conjPl P).asIdeal ≤ P.asIdeal := Ideal.map_comap_le
  have h3 := Ideal.pow_right_mono h2 2 h1
  rwa [show Formalism.L2.DIV.starOHom (Formalism.L2.DIV.starO a) = a from Formalism.L2.DIV.starO_starO a] at h3

theorem natCard_mem {E : Type} [Field E] [NumberField E] (P : Pl E) (h : Nat.card (kP P) ≠ 0) :
    ((Nat.card (kP P) : ℕ) : 𝓞 E) ∈ P.asIdeal := by
  haveI : Finite (kP P) := Nat.finite_of_card_ne_zero h
  letI := Fintype.ofFinite (kP P)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, Nat.card_eq_fintype_card]
  exact Nat.cast_card_eq_zero (kP P)

theorem units_mul_relation_rearrange_commRing {Rg : Type*} [CommRing Rg] (c e i s : Rg) (n : ℕ) (hc2 : c * c = c) (hce : c * e = 0) :
    c * (e * i + c * s + (1 - e - c)) ^ n + (1 - c) = 1 + c * (s ^ n - 1) := by
  have hca : c * (e * i + c * s + (1 - e - c)) = c * s := by
    linear_combination (i - 1) * hce + (s - 1) * hc2
  have hpow : ∀ m : ℕ, c * (e * i + c * s + (1 - e - c)) ^ m = c * s ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc c * (e * i + c * s + (1 - e - c)) ^ (m + 1) = (c * (e * i + c * s + (1 - e - c)) ^ m) * (e * i + c * s + (1 - e - c)) := by ring
        _ = s ^ m * (c * (e * i + c * s + (1 - e - c))) := by rw [ih]; ring
        _ = c * s ^ (m + 1) := by rw [hca]; ring
  linear_combination hpow n

theorem detIdele_eq_locE (D : D7) (V : HSp D) (Q : Finset (Pl D.host.E)) (eQ : AE D) (heQ : IsIdemSum eQ Q)
    (ϖ : D.host.E) (z : GA D V)
    (hz : mt V z = Matrix.diagonal (fun _ => eQ * incA D ϖ⁻¹ + cA D eQ * cA D (incA D ϖ) + (1 - eQ - cA D eQ)))
    (x : (AE D)ˣ) (hx : IsDetAt (cA D eQ) V z x) :
    (x : AE D) = Formalism.L2.JoinChr.locE D (cA D eQ) (star ϖ ^ V.rank) := by
  have he : eQ * eQ = eQ := by
    classical
    obtain ⟨es, hes, hsum, horth⟩ := Formalism.IndefR.Fin.idemSum_orth Q eQ heQ
    rw [hsum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single i (fun j hj hji => (horth i hi j hj (Ne.symm hji)).1) (fun h => absurd hi h)]
    exact (hes i hi).1
  have hc2 : cA D eQ * cA D eQ = cA D eQ := by rw [← map_mul, he]
  have hce : cA D eQ * eQ = 0 := by rw [mul_comm]; exact heQ.2
  have hs : incA D (star ϖ) = cA D (incA D ϖ) := rfl
  rw [hx, hz, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold Formalism.L2.JoinChr.locE
  rw [map_pow, hs]
  exact units_mul_relation_rearrange_commRing _ _ _ _ V.rank hc2 hce

theorem chi_unitOff : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, (ϖ : D.host.E) ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D (Vc D i), mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) + (1 - eQ - cA D eQ)) → ∀ x : (AE D)ˣ, IsDetAt (cA D eQ) (Vc D i) z x → UnitOff N ((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ))⁻¹ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i hV ξ χ ξR Q ω φ hK hQt N hN hNQ eQ heQ ϖ hϖ0 hϖ z hz x hx
  show GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff N _
  have hlev := hC.lev
  have hs0 : star ((ϖ : 𝓞 D.host.E) : D.host.E) ≠ 0 := by simpa using hϖ0
  set u : D.host.Eˣ := Units.mk0 _ hs0 with hu
  have hxl : (x : AE D) = Formalism.L2.JoinChr.locE D (cA D eQ) (((u ^ (Vc D i).rank : D.host.Eˣ)) : D.host.E) := by
    rw [detIdele_eq_locE D (Vc D i) Q eQ heQ _ z hz x hx, Units.val_pow_eq_pow_val]; rfl
  have hval : ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ →
      ((c x : Circle) : ℂ) = ∏ P ∈ Q, (((ψ.locK (conjPl P) u : ℂˣ) : ℂ)) ^ (Vc D i).rank := by
    intro c ψ hc
    rw [GlobalTheory.T.heckeCharacter_conjHalfIdele_eq_prod_local D Q eQ heQ (u ^ (Vc D i).rank) x hxl c ψ hc]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [map_pow, Units.val_pow_eq_pow_val]
  have e : ((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)) =
      (((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ)) * (((χ x : Circle) : ℂ)) * (((R.eta x : Circle) : ℂ))⁻¹ := by
    simp only [Lift.chrTh, Lift.tup, MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv]
  rw [e, hval _ _ (hlev.mu0 i), hval _ _ hK.chr, hval _ _ hlev.eta]
  have hb : ∀ P ∈ Q, Formalism.L2.DIV.starO ϖ ∈ (conjPl P).asIdeal ∧ Formalism.L2.DIV.starO ϖ ∉ (conjPl P).asIdeal ^ 2 := fun P hP =>
    ⟨(conjO_mem_conjPl P ϖ).2 (hϖ P hP).1, conjO_not_mem_sq (hϖ P hP).2⟩
  have hNc : ∀ P ∈ Q, (N : 𝓞 D.host.E) ∈ (conjPl P).asIdeal := fun P hP => (natCast_mem_conjPl P N).2 (hNQ P hP)
  have hunr : ∀ P ∈ Q, (R.C.mu0 i).UnrAt (conjPl P) := fun P hP => by
    obtain ⟨⟨q, hq, hqc, -, hqg⟩, -⟩ := hK.pl P hP
    have hqm : (q : 𝓞 D.host.E) ∈ (conjPl P).asIdeal := by
      rw [natCast_mem_conjPl, ← hqc]; exact natCard_mem P (by rw [hqc]; exact hq.ne_zero)
    exact (R.C.isMu0 i).unr (conjPl P) fun k hk =>
      not_mem_of_prime_ne (conjPl P) (D.host.g_prime k) hq (hqg k) hqm hk
  have hcoe : (u : D.host.E) = ((Formalism.L2.DIV.starO ϖ : 𝓞 D.host.E) : D.host.E) := by rw [Formalism.L2.DIV.starO_coe]; rfl
  obtain ⟨nμ, -, hnμ⟩ := (R.C.isMu0 i).inf
  obtain ⟨n, hn, hnx⟩ := hK.fin
  refine unitOff_inv (unitOff_mul (unitOff_mul (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)
    (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)) (unitOff_inv (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)))
  · rw [locK_eq_val _ (hunr P hP) u _ hcoe (hb P hP).1 (hb P hP).2]
    exact GlobalTheory.ValUnit.unitOff_val _ _ _ _ nμ (conjPl P) _ hnμ (finite_ramified_places_hecke_character _ (R.C.isMu0 i).unr)
      (R.C.isMu0 i).tame (hunr P hP) (hNc P hP)
  · refine unitOff_of_pow_eq_one _ hn ?_
    have h := LR ξ n hnx (conjPl P) u
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  · rw [locK_eq_val _ (R.C.isEta.unr (conjPl P)) u _ hcoe (hb P hP).1 (hb P hP).2]
    exact GlobalTheory.ValUnit.unitOff_val _ _ _ _ _ (conjPl P) _ R.C.isEta.inf
      (Set.Finite.subset Set.finite_empty fun w hw => hw (R.C.isEta.unr w)) (fun w y hy _ => R.C.isEta.unr w y hy)
      (R.C.isEta.unr (conjPl P)) (hNc P hP)

end GlobalTheory.DilChi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaValueValuationLeDivSqStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedThetaValue_valuation_le_div_sq : ∀ {D : D7} (nch : NChoice D) (w : D.what₂.places.Pl) (N0 : D.ntw.Tw → ℕ) (lam : D.ntw.abelian₂ (nch.twI w)) (a : ℤ)
    (u : (nch.Oe w)ˣ) (z : D.what₂.LL),
    BlochKatoReduction.Gen.partC N0 (nch.twI w) (nch.Q w) (nch.k' w) (nch.psi' w ^ a) (twEps D (nch.twI w)) →
    nch.embW w z * nch.kMapE w (BlochKatoReduction.Gen.kMap D.ntw (nch.twI w) (nch.k' w) (∑ δ, D.ntw.th (nch.twI w) ∅ lam δ)) =
      algebraMap (nch.Oe w) (FractionRing (nch.Oe w)) (u : nch.Oe w) *
        nch.kMapE w (BlochKatoReduction.Gen.thEval D.ntw (nch.twI w) (nch.Q w) lam (nch.k' w)
          (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (nch.twI w) lam) (nch.psi' w ^ a))) →
    (Formalism.DivisionValues.vw (D.plEq w) z : ℝ) ≤ (Formalism.DivisionValues.vw (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) : ℝ) / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ 2 := by
  first | exact @GlobalTheory.TwistValBound.vw_le_of_bound | exact GlobalTheory.TwistValBound.vw_le_of_bound | (intros; apply GlobalTheory.TwistValBound.vw_le_of_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularMatricesPreserveFrameLattices
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRead

theorem exists_gl_preimage {O C : Type} [CommRing O] [CommRing C] (φ : O →+* C) (hφ : Function.Injective φ) {n : ℕ}
    (u : GL (Fin n) C) (h : ∀ a b, u.val a b ∈ Set.range φ ∧ (u⁻¹).val a b ∈ Set.range φ) :
    ∃ u0 : GL (Fin n) O, Matrix.GeneralLinearGroup.map φ u0 = u := by
  choose M hM using fun a b => (h a b).1
  choose M' hM' using fun a b => (h a b).2
  have e1 : φ.mapMatrix (Matrix.of M) = u.val := by ext a b; simp [hM]
  have e2 : φ.mapMatrix (Matrix.of M') = (u⁻¹).val := by ext a b; simp [hM']
  have inj : Function.Injective (φ.mapMatrix : Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) C) := fun A B hAB => by
    ext a b; exact hφ (congrFun (congrFun hAB a) b)
  have h1 : Matrix.of M * Matrix.of M' = 1 := inj (by rw [map_mul, map_one, e1, e2, Units.mul_inv])
  have h2 : Matrix.of M' * Matrix.of M = 1 := inj (by rw [map_mul, map_one, e1, e2, Units.inv_mul])
  refine ⟨⟨Matrix.of M, Matrix.of M', h1, h2⟩, Units.ext ?_⟩
  exact e1

theorem det_map_gl {O C : Type} [CommRing O] [CommRing C] (φ : O →+* C) {n : ℕ} (g : GL (Fin n) O) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map φ g) = Units.map φ.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
  ext
  simp [Matrix.GeneralLinearGroup.map, RingHom.map_det]

theorem lamG_mem_lattices : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (F : Frame l ι n), Function.Injective F.emb → (∀ τ, Antitone (res n (lamW τ))) → ∀ u : ι → GL (Fin n) (PadicAlgCl l), (∀ τ a b, (u τ).val a b ∈ Set.range F.emb ∧ (u τ)⁻¹.val a b ∈ Set.range F.emb) → ∀ z, (z ∈ F.latN lamW → lamG (PadicAlgCl l) n lamW c u z ∈ F.latN lamW) ∧ (z ∈ F.latD lamW → lamG (PadicAlgCl l) n lamW c u z ∈ F.latD lamW) := by
  intro l _ ι _ _ n lamW c F hinj hlam u hu z
  choose u0 hu0 using fun τ => exists_gl_preimage F.emb hinj (u τ) (hu τ)
  have hu' : u = fun τ => Matrix.GeneralLinearGroup.map F.emb (u0 τ) := funext fun τ => (hu0 τ).symm
  subst hu'
  have hs : ((∏ τ, Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map F.emb (u0 τ)) ^ c τ : (PadicAlgCl l)ˣ) : PadicAlgCl l) =
      F.emb ((∏ τ, Matrix.GeneralLinearGroup.det (u0 τ) ^ c τ : F.Oˣ) : F.O) := by
    simp only [det_map_gl, ← map_zpow, ← map_prod]
    rfl
  have key : ∀ x, lamG (PadicAlgCl l) n lamW c (fun τ => Matrix.GeneralLinearGroup.map F.emb (u0 τ)) (GlobalTheory.LatBC.bc F.emb n lamW x) =
      GlobalTheory.LatBC.bc F.emb n lamW (((∏ τ, Matrix.GeneralLinearGroup.det (u0 τ) ^ c τ : F.Oˣ) : F.O) • grp F.O n lamW u0 x) := by
    intro x
    rw [lamG_apply, hs, ← GlobalTheory.LatBC.bc_grp, LinearMap.map_smulₛₗ]
  constructor
  · intro hz
    obtain ⟨x, rfl⟩ := (GlobalTheory.LatBC.latN_iff F lamW _).1 hz
    exact (GlobalTheory.LatBC.latN_iff F lamW _).2 ⟨_, (key x).symm⟩
  · intro hz
    obtain ⟨x, hx, rfl⟩ := (GlobalTheory.LatBC.latD_iff F lamW hlam _).1 hz
    refine (GlobalTheory.LatBC.latD_iff F lamW hlam _).2 ⟨_, ?_, (key x).symm⟩
    exact Submodule.smul_mem _ _ (Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep_mem_delta F.O ι (fun _ => n) (fun _ => n) (fun _ => le_rfl)
      (fun τ => res n (lamW τ)) u0 x hx)

end GlobalTheory.FrameRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperLevelTrivialDefiniteNoContractionStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperLevel_trivial_definite_noContraction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (G : Subgroup (GL (Fin r) E)) (g : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g → 3 * r < g → (∀ γ ∈ G, IsUStab X.Gm X.L' γ) → (∀ γ ∈ G, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g γ) → (X.p0 = 0 ∨ X.p0 = r) → ∀ x ∈ X.dom, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x → ∀ γ ∈ G, γ = 1 := by
  first | exact @GlobalTheory.DefiniteLevel.eq_one_of_definite | exact GlobalTheory.DefiniteLevel.eq_one_of_definite | (intros; apply GlobalTheory.DefiniteLevel.eq_one_of_definite <;> assumption)
end

