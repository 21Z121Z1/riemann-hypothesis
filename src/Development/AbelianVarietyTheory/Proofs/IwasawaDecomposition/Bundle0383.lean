import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0379
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0348
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0031
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0035
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantTermHeisOAlong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle0009
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0131
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0088

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutRepIsotypicSplitPlaceLocalComponentStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autRep_isotypic_splitPlace_localComponent : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) (s : SplitPlace L)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : σ.V →ₗ[ℂ] (GAf L n → π.W)),
    Function.Injective T → (∀ a, T a ∈ π.S) → GlobalTheory.HeckeFrob.IsLocMap s σ i T →
    ∀ g ∈ π.S, g ∈ ⨆ (T' : {T' : σ.V →ₗ[ℂ] (GAf L n → π.W) // (∀ a, T' a ∈ π.S) ∧ GlobalTheory.HeckeFrob.IsLocMap s σ i T'}),
      LinearMap.range T'.1 := by
  first | exact @GlobalTheory.HeckeFrob.mem_iSup_range_locMap | exact GlobalTheory.HeckeFrob.mem_iSup_range_locMap | (intros; apply GlobalTheory.HeckeFrob.mem_iSup_range_locMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumsEqPairingsTopChainLiftsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSums_eq_pairings_topChain_lifts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → A.fam.Ok 1 → let C := toChainReal R F tupT hm hTop; let L := toLiftReal R F tupT hm hTop hinj; ∀ μ : D.what₂.Tup, (let a := fun x => R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P1 F.ψ1 (tupT μ) x))); Submodule.span ℂ (Set.range a) = C.CCXP true μ ∧ ∀ x y, C.ipXP true μ (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A F.P1 F.ψ1 (tupT μ)) x y)) ∧ (let a := fun x => R.cX.toMap R.prX ((R.HX (tupT μ)).e (R.jX (tupT μ) (rowForm A F.P0 F.ψ0 (tupT μ) x))); Submodule.span ℂ (Set.range a) = C.CCXP false μ ∧ ∀ x y, C.ipXP false μ (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A F.P0 F.ψ0 (tupT μ)) x y)) ∧ ∀ i : Fin D.R.m, (let a := fun x => R.extV i (tupT μ) (R.jV i (tupT μ) (liftForm A F.P0 F.ψ0 i (tupT μ) x)); Submodule.span ℂ (Set.range a) = L.Amt μ i ∧ ∀ x y, L.ipA μ i (a x) (a y) = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i (tupT μ)) x y)) := by
  first | exact @GlobalTheory.TopNorm.classSums_topNorm | exact GlobalTheory.TopNorm.classSums_topNorm | (intros; apply GlobalTheory.TopNorm.classSums_topNorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugatedIntertwinerEvaluationHasRowLevelStatement
section
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugatedIntertwinerEvaluation_has_row_level : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, ∀ k ∈ JR R F, ∀ g : GA D (Yc D 0), GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ g k) = chiR R F k * GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u g := by
  first | exact @GlobalTheory.ConjRowLevelSee.conjMap_level_of_seeAt | exact GlobalTheory.ConjRowLevelSee.conjMap_level_of_seeAt | (intros; apply GlobalTheory.ConjRowLevelSee.conjMap_level_of_seeAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantTermHeisOAlongStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_om_heisO_along_eq_integral_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∀ τ, (gramAt D S τ).PosDef) → ∀ ξ, IsoVec T ξ → ∀ (μ : Measure (ZI T ξ)) (𝓕 : Set (ZI T ξ)), μ.IsHaarMeasure → IsFundamentalDomain ((GQ T).subgroupOf (ZI T ξ)) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → ∀ a, ∫ z in 𝓕, om (1, (z : GA D T)) (heisO ψ S T (along S T ξ a) f) 0 ∂μ = ∫ z in 𝓕, om (1, (z : GA D T)) f 0 ∂μ := by
  first | exact @GlobalTheory.TransvConst.constantTerm_heisO_along | exact GlobalTheory.TransvConst.constantTerm_heisO_along | (intros; apply GlobalTheory.TransvConst.constantTerm_heisO_along <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegreeRootDiscrBoundKummerFieldOfPowerIdealRoots
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize.KummerSize

open GlobalTheory.FieldSize.Capit

variable {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ)

theorem step (F : IntermediateField ℚ ℂ) (a b : ℝ) (hF : Sz F a b) (h : ∀ x, φ x ∈ F) (k : ℕ) (hk : 0 < k)
    (J : Ideal (𝓞 E)) (γ : 𝓞 E) (hγ : γ ≠ 0) (hJ : J ^ k = Ideal.span {γ}) (z : ℂ) (hz : z ^ k = φ (γ : E)) :
    Sz (F ⊔ ℚ⟮z⟯) (a + Real.log k) (b + Real.log k) := by
  have hyF : (intMap φ F h γ : F) ≠ 0 := by
    intro h0
    have h1 : φ (γ : E) = 0 := by rw [← coe_intMap φ F h, h0]; rfl
    exact hγ (RingOfIntegers.ext ((map_eq_zero φ).1 h1))
  exact GlobalTheory.FieldSize.sz_sup_adjoin_root F a b k (intMap φ F h γ : F)
    (IsLocalization.coeSubmodule F (J.map (intMap φ F h))) z hF hk hyF
    (by rw [← coeSubmodule_pow, ← Ideal.map_pow, hJ, Ideal.map_span, Set.image_singleton,
      IsLocalization.coeSubmodule_span_singleton]) hz

theorem sz_adjoin_roots (F : IntermediateField ℚ ℂ) (a b : ℝ) (hF : Sz F a b) (h : ∀ x, φ x ∈ F) {ι : Type}
    (k : ι → ℕ) (hk : ∀ i, 0 < k i) (J : ι → Ideal (𝓞 E)) (γ : ι → 𝓞 E) (hγ : ∀ i, γ i ≠ 0)
    (hJ : ∀ i, J i ^ k i = Ideal.span {γ i}) (z : ι → ℂ) (hz : ∀ i, z i ^ k i = φ (γ i : E)) (s : Finset ι) :
    Sz (F ⊔ IntermediateField.adjoin ℚ (z '' s)) (a + ∑ i ∈ s, Real.log (k i)) (b + ∑ i ∈ s, Real.log (k i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hF
  | insert i s hi ih =>
    have h' : ∀ x, φ x ∈ F ⊔ IntermediateField.adjoin ℚ (z '' s) := fun x => (le_sup_left : F ≤ F ⊔ _) (h x)
    have hS := step φ _ _ _ ih h' (k i) (hk i) (J i) (γ i) (hγ i) (hJ i) (z i) (hz i)
    have he : F ⊔ IntermediateField.adjoin ℚ (z '' ↑(insert i s)) =
        F ⊔ IntermediateField.adjoin ℚ (z '' s) ⊔ ℚ⟮z i⟯ := by
      rw [Finset.coe_insert, Set.image_insert_eq, Set.insert_eq, IntermediateField.adjoin_union, sup_comm
        (IntermediateField.adjoin ℚ {z i}), sup_assoc]
    rw [he, Finset.sum_insert hi]
    refine sz_mono' hS (by linarith) (by linarith)

end GlobalTheory.FieldSize.KummerSize

namespace GlobalTheory.FieldSize.KummerSize

variable {E : Type} [Field E] [NumberField E]

open GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis in

theorem exists_decomp (b : ClassBasis E) (J : Fin b.k → (Ideal (𝓞 E))⁰)
    (hJc : ∀ i, ClassGroup.mk0 (J i) = ClassGroup.mk E (b.c i)) (γ : Fin b.k → 𝓞 E) (hγ0 : ∀ i, γ i ≠ 0)
    (hγ : ∀ i, (J i : Ideal (𝓞 E)) ^ b.h i = Ideal.span {γ i}) {h : ℕ} (hh : 0 < h) {y : E}
    (hy : y ∈ powIdealElts E h) :
    ∃ (u : (𝓞 E)ˣ) (t : Eˣ) (a m : Fin b.k → ℤ), (∀ i, (h : ℤ) * a i = b.h i * m i) ∧
      y = (u : E) * (t : E) ^ h * ∏ i, (γ i : E) ^ m i := by
  obtain ⟨hy0, 𝔞, h𝔞⟩ := hy
  have h𝔞0 : 𝔞 ≠ 0 := by
    rintro rfl
    rw [zero_pow hh.ne'] at h𝔞
    exact hy0 (FractionalIdeal.spanSingleton_eq_zero_iff.1 h𝔞)
  set U := Units.mk0 𝔞 h𝔞0 with hU
  set Y := Units.mk0 y hy0 with hY
  have hUY : U ^ h = toPrincipalIdeal (𝓞 E) E Y := by
    refine Units.ext ?_
    rw [coe_toPrincipalIdeal, Units.val_pow_eq_pow_val, hU, Units.val_mk0, hY, Units.val_mk0, h𝔞]
  have hγE : ∀ i, (γ i : E) ≠ 0 := fun i h0 => hγ0 i (RingOfIntegers.ext h0)
  let G : Fin b.k → Eˣ := fun i => Units.mk0 (γ i : E) (hγE i)
  let P : Fin b.k → (FractionalIdeal (𝓞 E)⁰ E)ˣ := fun i => FractionalIdeal.mk0 E (J i)
  have hP : ∀ i, ClassGroup.mk E (P i) = ClassGroup.mk E (b.c i) := fun i => by
    rw [ClassGroup.mk_mk0, hJc]
  have hPG : ∀ i, P i ^ b.h i = toPrincipalIdeal (𝓞 E) E (G i) := fun i => by
    refine Units.ext ?_
    rw [coe_toPrincipalIdeal, Units.val_pow_eq_pow_val, FractionalIdeal.coe_mk0, ← FractionalIdeal.coeIdeal_pow,
      hγ i, FractionalIdeal.coeIdeal_span_singleton]
    rfl
  obtain ⟨a, ha⟩ := b.span (ClassGroup.mk E U)
  have hx1 : ClassGroup.mk E U ^ h = 1 := by
    rw [← map_pow, hUY, ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
    exact ⟨⟨_, rfl⟩⟩
  have hm : ∀ i, ∃ m : ℤ, (h : ℤ) * a i = b.h i * m := by
    have h1 := b.indep (fun i => (h : ℤ) * a i) (by
      simp only [zpow_mul', zpow_natCast]
      rw [Finset.prod_pow, ← ha, hx1])
    intro i
    exact orderOf_dvd_iff_zpow_eq_one.2 (h1 i)
  choose m hm using hm
  have h2 : ClassGroup.mk E (U * (∏ i, P i ^ a i)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_prod, ha]
    simp only [map_zpow, hP, mul_inv_cancel]
  obtain ⟨t, ht⟩ := exists_gen h2
  have hU' : U = toPrincipalIdeal (𝓞 E) E t * ∏ i, P i ^ a i := by
    rw [← ht, inv_mul_cancel_right]
  have h3 : toPrincipalIdeal (𝓞 E) E (t ^ h * ∏ i, G i ^ m i) = toPrincipalIdeal (𝓞 E) E Y := by
    rw [← hUY, hU', mul_pow, map_mul, map_pow, map_prod, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, ← hPG, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← hm i, mul_comm]
  rw [toPrincipalIdeal_eq_iff, coe_toPrincipalIdeal, FractionalIdeal.spanSingleton_eq_spanSingleton] at h3
  obtain ⟨u, hu⟩ := h3
  refine ⟨u, t, a, m, hm, ?_⟩
  show (Y : E) = _
  rw [← hu, Units.smul_def, Algebra.smul_def]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_prod, Units.val_zpow_eq_zpow_val, G, Units.val_mk0]
  ring

end GlobalTheory.FieldSize.KummerSize

namespace GlobalTheory.FieldSize

open GlobalTheory.FieldSize.KummerSize GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis

theorem sz_kummerField : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (h : ℕ), 0 < h →
    Sz (kummerField φ h) (Real.log (Module.finrank ℚ E) + ((NumberField.Units.rank E + 2) * Real.log h +
      Real.log (classNumber E))) (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E +
      ((NumberField.Units.rank E + 2) * Real.log h + Real.log (classNumber E))) := by
  intro E _ _ φ h hh
  classical

  let b : ClassBasis E := Classical.arbitrary _
  choose J hJ using fun i => ClassGroup.mk0_surjective (ClassGroup.mk E (b.c i))
  have hprin : ∀ i, ((J i : Ideal (𝓞 E)) ^ b.h i).IsPrincipal := fun i => by
    have hmem : (J i : Ideal (𝓞 E)) ^ b.h i ∈ (Ideal (𝓞 E))⁰ := pow_mem (J i).2 _
    rw [← ClassGroup.mk0_eq_one_iff hmem]
    have : (⟨_, hmem⟩ : (Ideal (𝓞 E))⁰) = J i ^ b.h i := rfl
    rw [this, map_pow, hJ]
    exact pow_orderOf_eq_one _
  choose γ hγ using fun i => (hprin i).principal
  have hγ' : ∀ i, (J i : Ideal (𝓞 E)) ^ b.h i = Ideal.span {γ i} := fun i => by
    rw [hγ i, Ideal.submodule_span_eq]
  have hγ0 : ∀ i, γ i ≠ 0 := fun i h0 => by
    have h1 := hγ' i
    rw [h0, Ideal.span_singleton_eq_bot.2 rfl] at h1
    exact nonZeroDivisors.coe_ne_zero (J i ^ b.h i) h1

  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := NumberField.Units.torsion E)
  let uγ : Option (Fin (NumberField.Units.rank E)) → (𝓞 E)ˣ :=
    fun o => o.elim (g : (𝓞 E)ˣ) (NumberField.Units.fundSystem E)
  have huJ : ∀ o, (⊤ : Ideal (𝓞 E)) ^ h = Ideal.span {((uγ o : (𝓞 E)ˣ) : 𝓞 E)} := fun o => by
    rw [Ideal.top_pow, eq_comm, Ideal.span_singleton_eq_top]
    exact (uγ o).isUnit
  have hu0 : ∀ o, ((uγ o : (𝓞 E)ˣ) : 𝓞 E) ≠ 0 := fun o => (uγ o).ne_zero

  choose ρ hρ using fun o => IsAlgClosed.exists_pow_nat_eq (φ (((uγ o : (𝓞 E)ˣ) : 𝓞 E) : E)) hh
  choose β hβ using fun i => IsAlgClosed.exists_pow_nat_eq (φ ((γ i : 𝓞 E) : E)) (b.h_pos i)

  have hF1 : Sz (imField φ ⊔ cycField h) (Real.log (Module.finrank ℚ E) + Real.log h)
      (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E + Real.log h) :=
    sz_sup _ _ _ _ _ _ (sz_fieldRange_embedding E φ) (sz_adjoin_rootOfUnity h hh)
  have hφ1 : ∀ x, φ x ∈ imField φ ⊔ cycField h := fun x => (le_sup_left : imField φ ≤ _) ⟨x, rfl⟩
  have hF2 := sz_adjoin_roots φ _ _ _ hF1 hφ1 (fun _ => h) (fun _ => hh) (fun _ => ⊤)
    (fun o => ((uγ o : (𝓞 E)ˣ) : 𝓞 E)) hu0 huJ ρ hρ Finset.univ
  set F2 := imField φ ⊔ cycField h ⊔ IntermediateField.adjoin ℚ (ρ '' ↑(Finset.univ : Finset (Option (Fin (NumberField.Units.rank E))))) with hF2def
  have hφ2 : ∀ x, φ x ∈ F2 := fun x => (le_sup_left : _ ≤ F2) (hφ1 x)
  have hF3 := sz_adjoin_roots φ _ _ _ hF2 hφ2 b.h b.h_pos (fun i => (J i : Ideal (𝓞 E))) γ hγ0 hγ' β hβ Finset.univ
  set F3 := F2 ⊔ IntermediateField.adjoin ℚ (β '' ↑(Finset.univ : Finset (Fin b.k))) with hF3def
  have hsum1 : ∑ _o ∈ (Finset.univ : Finset (Option (Fin (NumberField.Units.rank E)))), Real.log (h : ℕ) =
      (NumberField.Units.rank E + 1) * Real.log h := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_option]
  have hsum2 : ∑ i ∈ (Finset.univ : Finset (Fin b.k)), Real.log (b.h i) ≤ Real.log (classNumber E) := by
    have h1 : ∏ i, b.h i ≤ classNumber E := prod_orderOf_le_card_of_indep _ b.indep
    rw [← Real.log_prod (fun i _ => by exact_mod_cast (b.h_pos i).ne')]
    refine Real.log_le_log (Finset.prod_pos fun i _ => by exact_mod_cast b.h_pos i) ?_
    exact_mod_cast h1
  have hF3' := (sz_mono_and_of_le.1 F3 _ _ _ _ hF3 (by rw [hsum1] at *; linarith) (by rw [hsum1] at *; linarith) :
    Sz F3 (Real.log (Module.finrank ℚ E) + ((NumberField.Units.rank E + 2) * Real.log h +
      Real.log (classNumber E))) (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E +
      ((NumberField.Units.rank E + 2) * Real.log h + Real.log (classNumber E))))
  refine sz_mono_and_of_le.2 _ _ _ _ ?_ hF3'

  have h23 : F2 ≤ F3 := le_sup_left
  have h13 : imField φ ⊔ cycField h ≤ F3 := le_sup_left.trans h23
  have hρF : ∀ o, ρ o ∈ F3 := fun o => h23 ((le_sup_right : _ ≤ F2)
    (IntermediateField.subset_adjoin ℚ _ ⟨o, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩))
  have hβF : ∀ i, β i ∈ F3 := fun i => (le_sup_right : _ ≤ F3)
    (IntermediateField.subset_adjoin ℚ _ ⟨i, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩)
  refine (kummerField_le_iff φ).2 ⟨fun x => h13 (hφ1 x), h13 ((le_sup_right : cycField h ≤ _)
    (IntermediateField.mem_adjoin_simple_self ℚ _)), fun y hy z hz => ?_⟩
  have hy0 : y ≠ 0 := hy.1
  obtain ⟨u, t, a, m, hm, rfl⟩ := exists_decomp b J hJ γ hγ0 hγ' hh hy
  obtain ⟨⟨ζ, e⟩, hζe, -⟩ := NumberField.Units.exist_unique_eq_mul_prod E u
  obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.1 (hg ζ)
  let Φ : (𝓞 E)ˣ →* ℂˣ := Units.map ((φ.comp (algebraMap (𝓞 E) E)) : 𝓞 E →* ℂ)
  have hΦ : ∀ v : (𝓞 E)ˣ, ((Φ v : ℂˣ) : ℂ) = φ ((v : 𝓞 E) : E) := fun v => rfl
  set w : ℂ := ρ none ^ c * (∏ j, ρ (some j) ^ e j) * φ (t : E) * ∏ i, β i ^ a i with hw
  have hwF : w ∈ F3 := mul_mem (mul_mem (mul_mem (zpow_mem (hρF none) _)
    (prod_mem fun j _ => zpow_mem (hρF (some j)) _)) (h13 (hφ1 _))) (prod_mem fun i _ => zpow_mem (hβF i) _)
  have hA : ∀ o (k : ℤ), (ρ o ^ k) ^ h = ((Φ (uγ o) ^ k : ℂˣ) : ℂ) := fun o k => by
    rw [Units.val_zpow_eq_zpow_val, hΦ, ← hρ o, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  have hB : ∀ i, (β i ^ a i) ^ h = φ ((γ i : 𝓞 E) : E) ^ m i := fun i => by
    rw [← hβ i, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm (a i), hm i]
  have hu : φ ((u : 𝓞 E) : E) = ((Φ (uγ none) ^ c : ℂˣ) : ℂ) * ∏ j, ((Φ (uγ (some j)) ^ e j : ℂˣ) : ℂ) := by
    rw [← hΦ, hζe, ← hc, map_mul, Units.val_mul, map_prod, Units.coe_prod]
    congr 1
    · rw [Subgroup.coe_zpow, map_zpow]; rfl
    · exact Finset.prod_congr rfl fun j _ => by rw [map_zpow]; rfl
  have hwh : w ^ h = φ ((u : E) * (t : E) ^ h * ∏ i, ((γ i : 𝓞 E) : E) ^ m i) := by
    rw [hw, mul_pow, mul_pow, mul_pow, ← Finset.prod_pow, ← Finset.prod_pow, hA]
    simp only [hA, hB]
    rw [map_mul, map_mul, map_pow, map_prod, hu]
    simp only [map_zpow₀]
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, zero_pow hh.ne', eq_comm, map_eq_zero] at hwh
    exact hy0 hwh
  have hzw : z / w ∈ cycField h := mem_cycField hh.ne' (by rw [div_pow, hz, ← hwh, div_self (pow_ne_zero _ hw0)])
  have := mul_mem (h13 ((le_sup_right : cycField h ≤ _) hzw)) hwF
  rwa [div_mul_cancel₀ _ hw0] at this

end GlobalTheory.FieldSize

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetCharEqOneOfHasWt
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.NonTriv

section Char

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_unit (k : Eˣ) (hk : diagUnits E k ∈ unitIdl E) : ∃ u : (𝓞 E)ˣ, ((u : 𝓞 E) : E) = k := by
  have hv : ∀ x : Eˣ, diagUnits E x ∈ unitIdl E → ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (x : E) ≤ 1 :=
    fun x hx v => by rw [← GlobalTheory.Mem.Chr.AntiExist.val_diag v x, hx v]
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) (k : E) (hv k hk)
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) ((k⁻¹ : Eˣ) : E)
    (hv k⁻¹ (inv_mem hk))
  have hab : a * b = 1 := RingOfIntegers.ext (by
    change algebraMap (𝓞 E) E (a * b) = algebraMap (𝓞 E) E 1
    rw [map_mul, ha, hb, map_one, Units.mul_inv])
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩

theorem phase_pow_eq_one (u : (𝓞 E)ˣ) (τ : E →+* ℂ) :
    (τ ((u : 𝓞 E) : E) / ((‖τ ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) ^ (2 * (Nat.card (Units.torsion E) : ℤ)) = 1 := by
  set z := τ ((u : 𝓞 E) : E) with hz
  have h0 : z ≠ 0 := by
    rw [hz, map_ne_zero]
    exact Units.coe_ne_zero u
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
  have hc : starRingEnd ℂ z ≠ 0 := by simpa using h0
  have h1 : (z / ((‖z‖ : ℝ) : ℂ)) ^ 2 = z / starRingEnd ℂ z := by
    rw [div_pow, div_eq_div_iff (pow_ne_zero 2 hn) hc]
    have e : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * starRingEnd ℂ z := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    rw [e]; ring
  set ζ := IsCMField.unitsMulComplexConjInv E u with hζ
  have h2 : τ (((ζ : (𝓞 E)ˣ) : 𝓞 E) : E) * starRingEnd ℂ z = z := by
    have e : (ζ : (𝓞 E)ˣ) * IsCMField.unitsComplexConj E u = u := by
      rw [hζ, IsCMField.unitsMulComplexConjInv_apply, inv_mul_cancel_right]
    have e2 := congrArg (fun x : (𝓞 E)ˣ => τ (algebraMap (𝓞 E) E (x : 𝓞 E))) e
    simp only [Units.val_mul, map_mul] at e2
    have hcu : τ (algebraMap (𝓞 E) E ((IsCMField.unitsComplexConj E u : (𝓞 E)ˣ) : 𝓞 E)) = starRingEnd ℂ z := by
      rw [hz, ← IsCMField.complexEmbedding_complexConj]
      rfl
    rw [hcu] at e2
    exact e2
  have h3 : z / starRingEnd ℂ z = τ (((ζ : (𝓞 E)ˣ) : 𝓞 E) : E) := by
    rw [div_eq_iff hc, h2]
  have h4 : ζ ^ Nat.card (Units.torsion E) = 1 := pow_card_eq_one'
  rw [show (2 * (Nat.card (Units.torsion E) : ℤ)) = ((2 * Nat.card (Units.torsion E) : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast, pow_mul, h1, h3, ← map_pow]
  have h5 := congrArg (fun x : Units.torsion E => algebraMap (𝓞 E) E ((x : (𝓞 E)ˣ) : 𝓞 E)) h4
  simp only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, map_pow, OneMemClass.coe_one,
    Units.val_one, map_one] at h5
  change τ (algebraMap (𝓞 E) E ((ζ : (𝓞 E)ˣ) : 𝓞 E) ^ Nat.card (Units.torsion E)) = 1
  rw [h5, map_one]

end Char

section Char

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

variable (E) in

abbrev expT : ℤ := 2 * (Nat.card (Units.torsion E) : ℤ)

theorem expT_ne_zero : expT E ≠ 0 := by
  have : 0 < Nat.card (Units.torsion E) := Nat.card_pos
  unfold expT
  omega

theorem exists_hchar : ∃ χ : HChar E, χ.HasInf (fun w : InfinitePlace E => w.embedding) (fun _ => expT E) := by
  classical
  have hbij : Function.Bijective fun w : InfinitePlace E => InfinitePlace.mk w.embedding := by
    simp only [InfinitePlace.mk_embedding]
    exact Function.bijective_id
  obtain ⟨ψ, hψ, hψu, hψi, -, -, hψd⟩ := GlobalTheory.ModelChar.exists_modelChar E (InfinitePlace E) (fun w => w.embedding)
    hbij (fun _ => expT E) ∅ (fun _ => 1) (by simp)
  have hinf := (GlobalTheory.InfTypeLocal.infType_iff_local E (InfinitePlace E) (fun w => w.embedding) hbij ψ hψ _).2 hψi
  have hmem : ∀ k : Eˣ, infDiag k ∈ unitIdl E := fun k => by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply]
    exact Subgroup.prod_mem _ fun w _ => GlobalTheory.Mem.Chr.AntiExist.inf_mem w _
  obtain ⟨χ, hχ, -, hχU, hχd⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (Ideles E) Eˣ (unitIdl E)
    GlobalTheory.Mem.UnitOpen.isOpen_unitIdl (diagUnits E) 1 ψ hψ hψu (fun _ => by simp) (fun k hk => by
      obtain ⟨u, hu⟩ := exists_unit k hk
      show (1 : ℂˣ) = ψ (diagUnits E k)
      rw [hψd, Finset.prod_empty, mul_one]
      refine (Units.ext ?_).symm
      rw [hinf k, Units.val_one]
      refine Finset.prod_eq_one fun w _ => ?_
      rw [← hu]
      exact phase_pow_eq_one u w.embedding)
  refine ⟨⟨χ, hχ, fun k => by rw [hχd]; rfl⟩, fun k => ?_⟩
  show ((χ (infDiag k) : ℂˣ) : ℂ) = _
  rw [hχU _ (hmem k)]
  exact hinf k

end Char

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end GlobalTheory.DefU.NonTriv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DsPPosAndLower
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.DsLow

theorem dimV_cast {n n' : ℕ} (h : n = n') (x : Fin n' → ℝ) :
    StandardLattice.dimV (fun i : Fin n => x (Fin.cast h i)) = StandardLattice.dimV x := by
  subst h; rfl

theorem trueDsig_eq_dimV (R : Ranks) (p : HCParam R) :
    Vol.trueDsig R p =
      StandardLattice.dimV (Fin.append (fun i => ((p.v i : ℚ) : ℝ)) (fun j => -((p.b j : ℚ) : ℝ))) := by
  have hk := R.m_add_three_le_k
  have hd : 2 * R.rS + R.k + 1 = R.k - 1 + R.m := by
    rw [Formalism.MainNotions.S.dimS_eq R]; simp only [Ranks.r]; omega
  unfold Vol.trueDsig
  rw [← StandardLattice.dimV_eq_fdegHC _ (Vol.lamSH_isHCParam R p).1, ← dimV_cast hd]
  congr 1
  funext a
  have key : ∀ (c : Fin (R.k - 1 + R.m)) (d : Fin R.r), d.val = c.val → Formalism.MainNotions.S.lamS R p d =
      Fin.append (fun i => ((p.v i : ℚ) : ℝ)) (fun j => -((p.b j : ℚ) : ℝ)) c := by
    intro c d hcd
    unfold Formalism.MainNotions.S.lamS
    induction c using Fin.addCases with
    | left i =>
      have hi : d.val = i.val := hcd
      have h1 : d.val < R.k - 1 := hi ▸ i.2
      rw [Fin.append_left, dif_pos h1]
      have e : (⟨d.val, h1⟩ : Fin (R.k - 1)) = i := Fin.ext hi
      rw [e]
    | right j =>
      have hj : d.val = R.k - 1 + j.val := hcd
      have h1 : ¬ d.val < R.k - 1 := by omega
      have h2 : d.val - (R.k - 1) < R.m := by have := j.2; omega
      rw [Fin.append_right, dif_neg h1, dif_pos h2]
      have e : (⟨d.val - (R.k - 1), h2⟩ : Fin R.m) = j := Fin.ext (by simp only; omega)
      rw [e]
  exact key _ _ rfl

theorem idxRowLoc_pos (g k m : ℕ) (hg : g.Prime) : 0 < StandardLattice.idxRowLoc g k m := by
  haveI : NeZero g := ⟨hg.ne_zero⟩
  unfold StandardLattice.idxRowLoc StandardLattice.idxLoc
  haveI : Nonempty {A : GL (Fin (k + m - 1)) (ZMod g) //
      StandardLattice.IsRowLev k (m / 2 - 1) (A : Matrix (Fin (k + m - 1)) (Fin (k + m - 1)) (ZMod g))} := by
    refine ⟨⟨1, ?_, ?_, ?_, ?_⟩⟩
    · intro i j h
      have : i ≠ j := by rintro rfl; exact lt_irrefl _ h
      simp [Matrix.one_apply_ne this]
    · intro i; simp
    · intro i j _ h
      simp [Matrix.one_apply_ne h.ne']
    · intro i j _ h _
      simp [Matrix.one_apply_ne h]
  apply div_pos
  · exact_mod_cast Nat.card_pos
  · exact_mod_cast Nat.card_pos

theorem DsP_pos_and_lower : ∀ P : PreCh, 0 < DsP P ∧ (2 / 3 : ℝ) ^ P.R.f * (letI := P.H.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm P.H.E P.R.r) (StandardLattice.stdLat P.H.E P.R.r)) * (StandardLattice.idxRowLoc (P.H.g 0) P.R.k P.R.m ^ P.R.f * StandardLattice.idxRowLoc (P.H.g 1) P.R.k P.R.m ^ P.R.f) * ∏ τ : Tau P.R, StandardLattice.dimV (Fin.append (fun i => (((P.hcW P.u₀ τ).v i : ℚ) : ℝ)) (fun j => -(((P.hcW P.u₀ τ).b j : ℚ) : ℝ))) ≤ DsP P := by
  intro P
  have hm : 0 < (letI := P.H.cmStar; Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm P.H.E P.R.r) (StandardLattice.stdLat P.H.E P.R.r)) := by
    letI := P.H.cmStar
    show 0 < Formalism.HermitianLatticesTheory.mass (StandardLattice.stdForm P.H.E P.R.r) (StandardLattice.stdLat P.H.E P.R.r)
    rw [StandardLattice.standard_form_eq_telescope_form, StandardLattice.standard_lattice_eq_telescope_lattice]
    exact Formalism.HermitianLatticesTheory.massTelescope_std_pos P.H.E (host_cmData P.R P.H).cmUnram _
  have h0 := idxRowLoc_pos _ P.R.k P.R.m (P.H.g_prime 0)
  have h1 := idxRowLoc_pos _ P.R.k P.R.m (P.H.g_prime 1)
  have hp : 0 < ∏ τ : Tau P.R, Vol.trueDsig P.R (P.hcW P.u₀ τ) :=
    Finset.prod_pos fun τ _ => (Vol.lamSH_isHCParam_and_trueDsig_pos _ _).2
  have hD : 0 < DsP P := by
    unfold DsP
    exact mul_pos (mul_pos hm (mul_pos (pow_pos h0 _) (pow_pos h1 _))) hp
  refine ⟨hD, ?_⟩
  have hc : (2 / 3 : ℝ) ^ P.R.f ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have he : ∏ τ : Tau P.R, StandardLattice.dimV (Fin.append (fun i => (((P.hcW P.u₀ τ).v i : ℚ) : ℝ))
      (fun j => -(((P.hcW P.u₀ τ).b j : ℚ) : ℝ))) = ∏ τ : Tau P.R, Vol.trueDsig P.R (P.hcW P.u₀ τ) :=
    Finset.prod_congr rfl fun τ _ => (trueDsig_eq_dimV _ _).symm
  rw [he]
  calc _ = (2 / 3 : ℝ) ^ P.R.f * DsP P := by unfold DsP; ring
    _ ≤ DsP P := mul_le_of_le_one_left hD.le hc

end GlobalTheory.Mem.Top.DsLow
end

