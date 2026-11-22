import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0747
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0748
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0749
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0316
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.CylinderCountFamily
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JCountP
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0744
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterNeZeroOfSameTransform

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeFunIAddSmulStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeFunI_add_and_smul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h₁ h₂ : Formalism.UG.GU Dv.σw n → ℂ), h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → ∀ (c : ℂ) (f : GAf L n → W), heckeFunI L n U Dv (h₁ + h₂) f = heckeFunI L n U Dv h₁ f + heckeFunI L n U Dv h₂ f ∧ heckeFunI L n U Dv (c • h₁) f = c • heckeFunI L n U Dv h₁ f := by
  first | exact @GlobalTheory.InertHeckeAdd.heckeFunI_add_smul | exact GlobalTheory.InertHeckeAdd.heckeFunI_add_smul | (intros; apply GlobalTheory.InertHeckeAdd.heckeFunI_add_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalMemIntegralPointsOfLatticeStabilizerStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertLocal_mem_integralPoints_of_latticeStabilizer : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (x : GAf L n), x ∈ Umax L n → ∀ hg : Dv.loc x ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc x, hg⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n := by
  first | exact @GlobalTheory.InertKU.loc_mem_KU | exact GlobalTheory.InertKU.loc_mem_KU | (intros; apply GlobalTheory.InertKU.loc_mem_KU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalMemUnitaryGroupAntidiagonalFormStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertLocal_mem_unitaryGroup_antidiagonalForm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (x : GAf L n), Dv.loc x ∈ Formalism.UG.GU Dv.σw n := by
  first | exact @GlobalTheory.LocalUnitary.loc_mem_GU | exact GlobalTheory.LocalUnitary.loc_mem_GU | (intros; apply GlobalTheory.LocalUnitary.loc_mem_GU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalSurjectiveFromTrivOutsideStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertLocal_surjective_from_trivOutside : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (y : GL (Fin n) (w.adicCompletion L)), y ∈ Formalism.UG.GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = y := by
  first | exact @GlobalTheory.InertSurj.loc_surj | exact GlobalTheory.InertSurj.loc_surj | (intros; apply GlobalTheory.InertSurj.loc_surj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertOfUnramifiedIsometricInvolutionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_of_unramifiedIsometricInvolution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal ∧ ¬ IsSplitAt w ∧ q = Formalism.UG.qV (maximalRealSubfield L) v := by
  first | exact @GlobalTheory.InertOfUnramInv.inert_of_isUnramInv | exact GlobalTheory.InertOfUnramInv.inert_of_isUnramInv | (intros; apply GlobalTheory.InertOfUnramInv.inert_of_isUnramInv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFundamentalDomainEqIteratedRationalSplitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fundamentalDomain_eq_iterated_rationalSplitting : ∀ (D : D7) (r m s t : ℕ) (J : Matrix (Fin r) (Fin s) D.host.E) (K : Matrix (Fin r) (Fin t) D.host.E) (L : Matrix (Fin s) (Fin r) D.host.E) (M : Matrix (Fin t) (Fin r) D.host.E), L * J = 1 → L * K = 0 → M * J = 0 → M * K = 1 → J * L + K * M = 1 → ∀ (μ : Measure (Mx D r m)) (𝓕 : Set (Mx D r m)), IsCovolOne (GlobalTheory.MixModel.ratMx D r m) μ 𝓕 → ∀ (ν : Measure (Mx D s m)) (𝓨 : Set (Mx D s m)), IsCovolOne (GlobalTheory.MixModel.ratMx D s m) ν 𝓨 → ∀ (η : Measure (Mx D t m)) (𝓥 : Set (Mx D t m)), IsCovolOne (GlobalTheory.MixModel.ratMx D t m) η 𝓥 → ∃ κ : ℝ, ∀ T : Mx D r m → ℂ, Continuous T → (∀ γ ∈ GlobalTheory.MixModel.ratMx D r m, ∀ u, T (γ + u) = T u) → ∫ u in 𝓕, T u ∂μ = κ * ∫ v in 𝓥, (∫ y in 𝓨, T (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) ∂ν) ∂η := by
  first | exact @GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated_split | exact GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated_split | (intros; apply GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableLatticeInMatrixAlgebraLayer
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.LayerSst

open Module

section Sum

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℚ_[l] (V i)]
  {V' : Type} [AddCommGroup V'] [Module ℚ_[l] V']
  {ρ : ∀ i, Representation ℚ_[l] ↥(GK K) (V i)} {ρ' : Representation ℚ_[l] ↥(GK K) V'}
  {E : V' ≃ₗ[ℚ_[l]] (∀ i, V i)}
  (hE : ∀ g x i, E (ρ' g x) i = ρ i g (E x i))
include hE

theorem mem_Dst_iff (x : V' ⊗[ℚ_[l]] Bst P) :
    x ∈ Dst P ρ' ↔ ∀ i, GlobalTheory.BlockSum.tensComp E (Bst P) x i ∈ Dst P (ρ i) := by
  simp only [mem_Dst]
  rw [forall_comm]
  refine forall_congr' fun g => ?_
  rw [← (GlobalTheory.BlockSum.tensComp E (Bst P)).injective.eq_iff, funext_iff]
  refine forall_congr' fun i => ?_
  have key : GlobalTheory.BlockSum.tensComp E (Bst P) (stRep P ρ' g x) i =
      stRep P (ρ i) g (GlobalTheory.BlockSum.tensComp E (Bst P) x i) :=
    GlobalTheory.BlockSum.tensComp_map E (ρ' g) (fun i => ρ i g) (hE g) (actSt P (g : GQ l)).toLinearMap x i
  rw [key]

theorem isSst_sum [∀ i, FiniteDimensional ℚ_[l] (V i)] (h : ∀ i, IsSst P (ρ i)) : IsSst P ρ' := by
  have := fun i => finiteDimensional_Dst_of_isSst l P K (V i) (ρ i) (h i)
  unfold IsSst at h ⊢
  rw [GlobalTheory.BlockSum.finrank_eq_sum (GlobalTheory.BlockSum.tensComp E (Bst P)) _ _ (mem_Dst_iff P hE), E.finrank_eq,
    Module.finrank_pi_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => h i

end Sum

theorem isSst_resQ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (ρ : Representation LL ↥(GK K) V) (h : IsSst P ρ) : IsSst P (GlobalTheory.PstCoeff.resQ ρ) := by
  have hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l] := by
    ext x
    simp [mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]
  have e : finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) = finrank ℚ_[l] LL * finrank LL ↥(Dst P ρ) := by
    rw [hD, finrank_mul_finrank]
    rfl
  rw [IsSst, e, h, ← finrank_mul_finrank ℚ_[l] LL V]
  ring

section Layer

variable {l : ℕ} [Fact l.Prime] {K L₀ : FinExt l} {a d : ℕ} {Cl : Set (↥(GK K) →* GL (Fin a) (Om l))}
  {ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]} (Ly : Layer L₀ Cl ρ)

def matL (k : Fin Ly.m) (g : ↥(GK K)) : Matrix (Fin a) (Fin a) ↥(Ly.L k).1 :=
  fun i j => ⟨(Ly.rep k g).val i j, Ly.rep_mem k g i j⟩

def repL (k : Fin Ly.m) : ↥(GK K) →* GL (Fin a) ↥(Ly.L k).1 :=
  MonoidHom.toHomUnits
    { toFun := matL Ly k
      map_one' := by
        ext i j
        simp only [matL, map_one, Units.val_one, Matrix.one_apply]
        split_ifs <;> rfl
      map_mul' := fun g h => by
        ext i j
        simp [matL, Matrix.mul_apply] }

theorem repL_val (k : Fin Ly.m) (g : ↥(GK K)) (i j : Fin a) :
    (((repL Ly k g).val i j : ↥(Ly.L k).1) : Om l) = (Ly.rep k g).val i j := rfl

def RL (k : Fin Ly.m) : Representation ↥(Ly.L k).1 ↥(GK K) (Fin a → ↥(Ly.L k).1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥(Ly.L k).1 ≃ₐ[↥(Ly.L k).1] _) : _ →* _).comp
    ((Units.coeHom _).comp (repL Ly k))

theorem RL_apply (k : Fin Ly.m) (g : ↥(GK K)) (v : Fin a → ↥(Ly.L k).1) : RL Ly k g v = (repL Ly k g).val *ᵥ v := by
  simp [RL, Matrix.toLinAlgEquiv'_apply]

def coordM (v : Fin d → ℚ_[l]) (k : Fin Ly.m) : Matrix (Fin a) (Fin a) (Om l) :=
  ∑ s, algebraMap ℚ_[l] (Om l) (v s) • Ly.b s k

theorem coordM_mem (v : Fin d → ℚ_[l]) (k : Fin Ly.m) (i j : Fin a) : coordM Ly v k i j ∈ (Ly.L k).1 := by
  simp only [coordM, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact sum_mem fun s _ => mul_mem (IntermediateField.algebraMap_mem _ _) (Ly.b_mem s k i j)

theorem sum_b (v : Fin d → ℚ_[l]) : ∑ s, v s • Ly.b s = fun k => coordM Ly v k := by
  funext k
  simp [coordM, Finset.sum_apply, algebraMap_smul]

end Layer

section Layer2

variable {l : ℕ} [Fact l.Prime] {K L₀ : FinExt l} {a d : ℕ} {Cl : Set (↥(GK K) →* GL (Fin a) (Om l))}
  {ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]} (Ly : Layer L₀ Cl ρ)

def coordLin : (Fin d → ℚ_[l]) →ₗ[ℚ_[l]] ((p : Fin Ly.m × Fin a) → Fin a → ↥(Ly.L p.1).1) where
  toFun v p i := ⟨coordM Ly v p.1 i p.2, coordM_mem Ly v p.1 i p.2⟩
  map_add' v w := by
    funext p i
    apply Subtype.ext
    simp [coordM, Finset.sum_add_distrib, add_smul, Matrix.sum_apply]
  map_smul' c v := by
    funext p i
    apply Subtype.ext
    show coordM Ly (c • v) p.1 i p.2 = c • coordM Ly v p.1 i p.2
    simp only [coordM, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, map_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Algebra.smul_def, mul_assoc]

theorem coordLin_apply (v : Fin d → ℚ_[l]) (p : Fin Ly.m × Fin a) (i : Fin a) :
    ((coordLin Ly v p i : ↥(Ly.L p.1).1) : Om l) = coordM Ly v p.1 i p.2 := rfl

theorem coordLin_bijective : Function.Bijective (coordLin Ly) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h0 : ∑ s, v s • Ly.b s = 0 := by
      rw [sum_b]
      funext k i j
      have := congrArg Subtype.val (congrFun (congrFun hv (k, j)) i)
      exact this
    exact funext (Fintype.linearIndependent_iff.1 Ly.indep v h0)
  · intro y
    let x : Fin Ly.m → Matrix (Fin a) (Fin a) (Om l) := fun k i j => ((y (k, j) i : ↥(Ly.L k).1) : Om l)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ_[l]).1 (Ly.span x fun k i j => (y (k, j) i).2)
    refine ⟨c, ?_⟩
    funext p i
    apply Subtype.ext
    rw [coordLin_apply]
    rw [sum_b] at hc
    exact congrFun (congrFun (congrFun hc p.1) i) p.2

def coordEquiv : (Fin d → ℚ_[l]) ≃ₗ[ℚ_[l]] ((p : Fin Ly.m × Fin a) → Fin a → ↥(Ly.L p.1).1) :=
  LinearEquiv.ofBijective (coordLin Ly) (coordLin_bijective Ly)

theorem coordM_mulVec (g : ↥(GK K)) (v : Fin d → ℚ_[l]) (k : Fin Ly.m) :
    coordM Ly (((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v) k = (Ly.rep k g).val * coordM Ly v k := by
  have hr : ∀ t, (Ly.rep k g).val * Ly.b t k = ∑ s, zOm l ((ρ g).val s t) • Ly.b s k :=
    fun t => (Ly.reads k).equi g t
  calc coordM Ly (((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v) k
      = ∑ s, ∑ t, (algebraMap ℚ_[l] (Om l) (v t) * zOm l ((ρ g).val s t)) • Ly.b s k := by
        simp only [coordM, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_smul, Matrix.map_apply]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
        rw [mul_comm]
        rfl
    _ = ∑ t, ∑ s, (algebraMap ℚ_[l] (Om l) (v t) * zOm l ((ρ g).val s t)) • Ly.b s k := Finset.sum_comm
    _ = (Ly.rep k g).val * coordM Ly v k := by
        simp only [coordM, Finset.mul_sum, Matrix.mul_smul, hr, Finset.smul_sum, smul_smul]

theorem coordEquiv_equi (g : ↥(GK K)) (v : Fin d → ℚ_[l]) (p : Fin Ly.m × Fin a) :
    coordEquiv Ly (qRep ρ g v) p = GlobalTheory.PstCoeff.resQ (RL Ly p.1) g (coordEquiv Ly v p) := by
  funext i
  apply Subtype.ext
  have hq : qRep ρ g v = ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ v := by
    simp [qRep, Matrix.toLinAlgEquiv'_apply]
  rw [GlobalTheory.PstCoeff.resQ_apply, RL_apply]
  change coordM Ly (qRep ρ g v) p.1 i p.2 = _
  rw [hq, coordM_mulVec, Matrix.mul_apply]
  simp [Matrix.mulVec, dotProduct, repL_val, coordEquiv, coordLin_apply]

end Layer2

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ) (Cl : Set (↥(GK K) →* GL (Fin a) (Om l))) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (Ly : Layer L₀ Cl ρ), ((∀ ρ₁ ∈ Cl, ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R) → IsSst P (qRep ρ)) ∧ ((∀ ρ₁ ∈ Cl, (∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsCrys (P.PD K) R)) → IsCrys (P.PD K) (qRep ρ)) := by
  intro l _ K L₀ P AI T a Cl d ρ Ly
  have hfin : ∀ p : Fin Ly.m × Fin a, FiniteDimensional ℚ_[l] (Fin a → ↥(Ly.L p.1).1) := fun p => by
    have := (Ly.L p.1).2
    infer_instance
  have hE := coordEquiv_equi Ly
  refine ⟨fun hS => ?_, fun hC => ?_⟩
  · refine isSst_sum P (E := coordEquiv Ly) (fun g x p => hE g x p) fun p => ?_
    have := (Ly.L p.1).2
    exact isSst_resQ P _ (hS (Ly.rep p.1) (Ly.mem p.1) (Ly.L p.1) (repL Ly p.1) (RL Ly p.1) (Ly.le p.1)
      (fun g v => RL_apply Ly p.1 g v) (fun g i j => repL_val Ly p.1 g i j))
  · refine GlobalTheory.BlockSum.isCrys_sum (P.PD K) (E := coordEquiv Ly) (fun g x p => hE g x p) fun p => ?_
    have := (Ly.L p.1).2
    exact (GlobalTheory.BSCoeff.isCrys_resQ_iff P (RL Ly p.1)).2 (hC (Ly.rep p.1) (Ly.mem p.1) (Ly.L p.1) (repL Ly p.1)
      (RL Ly p.1) (Ly.le p.1) (fun g v => RL_apply Ly p.1 g v) (fun g i j => repL_val Ly p.1 g i j))

end GlobalTheory.LayerSst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUniUpMul
section
namespace GlobalTheory.UnipotentUpperMul

theorem isUniUp_mul : ∀ {R : Type} [inst : CommRing R] {N : ℕ} {M M' : Matrix (Fin N) (Fin N) R},
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp M → Formalism.MainNotions.ArithmeticCylinders.IsUniUp M' → Formalism.MainNotions.ArithmeticCylinders.IsUniUp (M * M') := by
  intro R _ N M M' hM hM' a b
  constructor
  · intro hba
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k a with hka | hak
    · rw [(hM a k).1 hka, zero_mul]
    · rw [(hM' k b).1 (lt_of_lt_of_le hba hak), mul_zero]
  · intro hab
    subst hab
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [(hM a a).2 rfl, (hM' a a).2 rfl, mul_one]
    · intro k _ hka
      rcases lt_or_gt_of_ne hka with h | h
      · rw [(hM a k).1 h, zero_mul]
      · rw [(hM' k a).1 h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

end GlobalTheory.UnipotentUpperMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitCardResidueFieldOffExceptionalPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_card_residueField_off_exceptional_places : ∀ {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (k : ℕ) (PP : Pl D.host.E),
  PP ∉ X.S0 i → IsUnit ((Nat.card (kP PP) : ℕ) : X.Ok i k) := by
  first | exact @GlobalTheory.ResidueUnit.isUnit_card_residueField_Ok | exact GlobalTheory.ResidueUnit.isUnit_card_residueField_Ok | (intros; apply GlobalTheory.ResidueUnit.isUnit_card_residueField_Ok <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LadicCharacterRestrictCmFieldEqCyclotomicPow
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

namespace GlobalTheory.PolCharRes

theorem val_below_of_degree_one (E : Type) [Field E] [NumberField E] [IsCMField E] (ν : Formalism.L2.Host.HChar E) (s : ℝ)
    (hν : ν.IsAbsPow s) (χ : Formalism.L2.Host.HChar (maximalRealSubfield E))
    (hχ : compNorm E χ = ν * (GlobalTheory.ThetaPull.thetaChar ν)⁻¹) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 → w.asIdeal.ramificationIdx ℤ = 1 →
      χ.UnrAt (w.under (𝓞 (maximalRealSubfield E))) ∧
      ((χ.val (w.under (𝓞 (maximalRealSubfield E))) : ℂˣ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(2 * s : ℂ)) := by
  have hr : compNorm E (GlobalTheory.PolChar.resReal ν) = ν * (GlobalTheory.ThetaPull.thetaChar ν)⁻¹ := by
    refine Subtype.ext (MonoidHom.ext fun x => ?_)
    change ν.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E (GlobalTheory.GalOfCusp.ideleNorm E x)) =
      ν.1 x * ((ν.1 (Units.map (GlobalTheory.UnitaryBC.conjAd E).toMonoidHom x))⁻¹)⁻¹
    rw [GlobalTheory.GalOfCusp.ideleMap_ideleNorm, map_mul, GlobalTheory.PolChar.ideleConj_eq, inv_inv]
  set ε := χ * (GlobalTheory.PolChar.resReal ν)⁻¹ with hε
  have hεc : compNorm E ε = 1 := by rw [hε, map_mul, map_inv, hχ, hr, mul_inv_cancel]
  have hχe : χ = GlobalTheory.PolChar.resReal ν * ε := by rw [hε, mul_comm χ, mul_inv_cancel_left]
  filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under (maximalRealSubfield E) E).eventually
    (GlobalTheory.HeckeSplit.eventually_unrAt χ.1 χ.2.1)] with w hu hf he
  obtain ⟨hsp, hcard, hw'⟩ := GlobalTheory.T.degreeOne_prime_CMField_over_split_maxRealSubfield E w hf he
  refine ⟨hu, ?_⟩
  have hεv : ε.val (w.under (𝓞 (maximalRealSubfield E))) = 1 := GlobalTheory.T.heckeChar_local_eq_one_of_trivial_on_norms_split E ε hεc _ hsp _
  rw [hχe, Formalism.L2.Host.HChar.val_mul, hεv, mul_one, GlobalTheory.T.heckeCharRestrictMaxReal_val_eq_prod_above E ν _ (fun w' h => ⟨hν.1 w', (hw' w' h).2⟩),
    Units.coe_prod, Finset.prod_congr rfl (fun w' h => by rw [hν.2.1 w', (hw' w' h).1]), Finset.prod_const, hcard,
    ← Complex.cpow_nat_mul]
  congr 1
  push_cast
  ring

theorem restrict_eq_cycBar_pow : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ν : Formalism.L2.Host.HChar E) (s : ℝ), ν.IsAbsPow s →
    ∀ ψ : Formalism.L2.Host.HChar (maximalRealSubfield E), compNorm E ψ = ν * (GlobalTheory.ThetaPull.thetaChar ν)⁻¹ →
    ∀ (k : ℕ) (μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ), IsLAdicCharOf ι (ψ * quadChar E ^ k) μ →
    ∀ m : ℤ, (m : ℝ) = 2 * s → μ.comp (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) = cycBar E Ω l ^ m := by
  intro E Ω _ _ _ _ _ _ l _ ι ν s hν ψ hψ k μ hμ m hm
  obtain ⟨hμc, art, n, hart, -, hlad⟩ := hμ
  have hχ : compNorm E (ψ * quadChar E ^ k) = ν * (GlobalTheory.ThetaPull.thetaChar ν)⁻¹ := by
    rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one, hψ]
  have hcyc : Continuous (cycBar E Ω l) :=
    (Continuous.units_map _ (show Continuous (fun x : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (x : ℚ_[l])) from
      (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (ReciprocityTheory.Gal.continuous_cycZ E Ω l)
  rw [← div_eq_one]
  refine GlobalTheory.T.galoisCharacter_eq_one_of_trivial_degreeOne_frobenius E Ω l _ ((hμc.comp (GlobalTheory.T.continuous_restrictScalarsHom_maximalRealSubfield E Ω)).div' (hcyc.zpow m)) ?_
  filter_upwards [val_below_of_degree_one E ν s hν _ hχ, GlobalTheory.HeightCounting.eventually_natCast_notMem E l] with w h1 hl hf he A σ hA hσ
  obtain ⟨hu, hv⟩ := h1 hf he
  set F := maximalRealSubfield E
  have hA' : IsPlaceOver (F := F) A (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F E Ω]
    exact hA (algebraMap (𝓞 F) (𝓞 E) x)
  have hσ' : IsFrob (F := F) A (normV (w.under (𝓞 F))) (AlgEquiv.restrictScalarsHom F σ) := by
    rw [GlobalTheory.T.absNorm_under_eq_of_inertiaDeg_one F E w hf]
    exact ⟨hσ.1, hσ.2⟩
  have hl' : ((l : ℕ) : 𝓞 F) ∉ (w.under (𝓞 F)).asIdeal := fun h => hl (by
    have := (Ideal.mem_comap).1 h
    simpa using this)
  have e1 := hlad.frob_unr hart (Or.inl hl') hu hA' hσ'
  have e2 := ReciprocityTheory.Gal.cycZ_of_isFrob hl hA hσ
  rw [MonoidHom.div_apply, div_eq_one]
  apply Units.ext
  rw [MonoidHom.comp_apply, e1, hv]
  have hN : (Ideal.absNorm w.asIdeal : ℕ) = normV w := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hmC : (-(2 * (s : ℂ))) = (((-m : ℤ)) : ℂ) := by
    have : (2 * (s : ℂ)) = ((m : ℝ) : ℂ) := by rw [hm]; push_cast; ring
    rw [this]; push_cast; ring
  have e3 : ((cycBar E Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : Qbar l) := by
    change algebraMap ℚ_[l] (Qbar l) (((ReciprocityTheory.Gal.cycZ E Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = _
    rw [e2]; simp
  rw [hN, hmC, Complex.cpow_intCast, map_zpow₀, map_natCast, ← zpow_neg, neg_neg]
  change _ = (((cycBar E Ω l σ) ^ m : (Qbar l)ˣ) : Qbar l)
  rw [Units.val_zpow_eq_zpow_val, e3]

end GlobalTheory.PolCharRes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsSpehProductStatement
section
open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.DefiniteBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_langlands_speh_product : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)),
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    ∀ (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h),
    IsRec h rc → GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL →
    ∀ (a d n : ℕ) (hd : ∑ _ : Fin d, a = n) (σ : LocIrr w a) (σ' : LocIrr w n),
      IsUnitarisable σ.ρ → IsGeneric σ.ρ → IsSpehQuot hd σ σ' →
      rc (cls (ParLaws.toRep σ')) =
        sumList ((List.range d).map fun k : ℕ => (rc (cls (ParLaws.toRep σ))).lpTw (((d : ℝ) - 1) / 2 - k)) := by
  first | exact @GlobalTheory.SpehRec.rec_spehQuot | exact GlobalTheory.SpehRec.rec_spehQuot | (intros; apply GlobalTheory.SpehRec.rec_spehQuot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterNeZeroOfSameTransformStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satakeParameter_ne_zero_of_sameTransform : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ (α : Fin (n / 2) → ℂ) (β : Fin (n / 2) → ℂˣ), (∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), Formalism.UG.SatU ϖ q h α = Formalism.UG.SatU ϖ q h (fun i => (β i : ℂ))) → ∀ i, α i ≠ 0 := by
  first | exact @GlobalTheory.SatNonzero.satU_ne_zero | exact GlobalTheory.SatNonzero.satU_ne_zero | (intros; apply GlobalTheory.SatNonzero.satU_ne_zero <;> assumption)
end

