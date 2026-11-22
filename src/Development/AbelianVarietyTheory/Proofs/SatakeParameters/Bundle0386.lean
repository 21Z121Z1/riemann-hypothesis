import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0384
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0035
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaSatakeParametersInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0261
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0263
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0262
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0383
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0222
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Formalism.LocalToGlobal.HermitianForms.Bundle0007
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.HermitianForms.TiedTwSymAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0259
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0185
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0258
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0030
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0283
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0285

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BijectiveOfSplit
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CharLiftStep

open Matrix

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem cycAt_or_split [IsGalois K M] (hp : (Module.finrank K M).Prime) (v : HeightOneSpectrum (𝓞 K))
    (u : HeightOneSpectrum (𝓞 M)) [u.asIdeal.LiesOver v.asIdeal] :
    GlobalTheory.FunExt.CycAt v u ∨ (u.asIdeal.ramificationIdx (𝓞 K) = 1 ∧ u.asIdeal.inertiaDeg (𝓞 K) = 1) := by
  have h2 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 M) Gal(M/K)
  rw [IsGalois.card_aut_eq_finrank, Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal u.asIdeal Gal(M/K),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal u.asIdeal Gal(M/K)] at h2
  have hp' := hp
  rw [← h2] at hp'
  rcases Nat.prime_mul_iff.1 hp' with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inr (mul_eq_one.1 h)
  · left
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h
    have hu : u.under (𝓞 K) = v :=
      HeightOneSpectrum.ext (Ideal.LiesOver.over (P := u.asIdeal) (p := v.asIdeal)).symm
    refine ⟨inferInstance, hp, hu, fun u' hu' => ?_⟩
    have : u'.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hu']; rfl⟩
    have m1 : u.asIdeal ∈ v.asIdeal.primesOver (𝓞 M) := ⟨u.isPrime, inferInstance⟩
    have m2 : u'.asIdeal ∈ v.asIdeal.primesOver (𝓞 M) := ⟨u'.isPrime, inferInstance⟩
    rw [ha, Set.mem_singleton_iff] at m1 m2
    exact HeightOneSpectrum.ext (m2.trans m1.symm)

section Split

variable (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 M)) [u.asIdeal.LiesOver v.asIdeal]

theorem bijective_of_split (he : u.asIdeal.ramificationIdx (𝓞 K) = 1) (hf : u.asIdeal.inertiaDeg (𝓞 K) = 1) :
    Function.Bijective (GroundTheory.Global.adicCompletionMap v u) := by
  letI : Algebra (v.adicCompletion K) (u.adicCompletion M) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  have : ContinuousSMul (v.adicCompletion K) (u.adicCompletion M) :=
    continuousSMul_of_algebraMap _ _ (GroundTheory.Global.continuous_adicCompletionMap v u)
  have : IsScalarTower K (v.adicCompletion K) (u.adicCompletion M) :=
    .of_algebraMap_eq fun x => by
      show _ = GroundTheory.Global.adicCompletionMap v u _
      rw [GroundTheory.Global.adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply K M (u.adicCompletion M)]
  have h1 : Module.finrank (v.adicCompletion K) (u.adicCompletion M) = 1 := by
    rw [GroundTheory.Global.finrank_adicCompletion v u, he, hf]
  refine ⟨(GroundTheory.Global.adicCompletionMap v u).injective, fun y => ?_⟩
  have hy : y ∈ (⊥ : Subalgebra (v.adicCompletion K) (u.adicCompletion M)) :=
    (Subalgebra.bot_eq_top_of_finrank_eq_one h1) ▸ Algebra.mem_top
  obtain ⟨x, hx⟩ := Algebra.mem_bot.1 hy
  exact ⟨x, hx⟩

theorem normU_of_split (he : u.asIdeal.ramificationIdx (𝓞 K) = 1) (hf : u.asIdeal.inertiaDeg (𝓞 K) = 1) :
    Continuous (RingEquiv.ofBijective _ (bijective_of_split v u he hf)).symm ∧
      ∀ y : (u.adicCompletion M)ˣ, ((GlobalTheory.BCChar.normU v u y : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
        (RingEquiv.ofBijective _ (bijective_of_split v u he hf)).symm y := by
  set i := RingEquiv.ofBijective _ (bijective_of_split v u he hf)
  letI : Algebra (v.adicCompletion K) (u.adicCompletion M) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  have : ContinuousSMul (v.adicCompletion K) (u.adicCompletion M) :=
    continuousSMul_of_algebraMap _ _ (GroundTheory.Global.continuous_adicCompletionMap v u)
  have : IsScalarTower K (v.adicCompletion K) (u.adicCompletion M) :=
    .of_algebraMap_eq fun x => by
      show _ = GroundTheory.Global.adicCompletionMap v u _
      rw [GroundTheory.Global.adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply K M (u.adicCompletion M)]
  have h1 : Module.finrank (v.adicCompletion K) (u.adicCompletion M) = 1 := by
    rw [GroundTheory.Global.finrank_adicCompletion v u, he, hf]
  have hfd : FiniteDimensional (v.adicCompletion K) (u.adicCompletion M) := GroundTheory.Global.finite_adicCompletion v u
  have hc := (GlobalTheory.adicCompletion_trace_norm_continuous K M v u _ (GroundTheory.Global.continuous_adicCompletionMap v u) hfd).2
  have key : ∀ y : u.adicCompletion M, Algebra.norm (v.adicCompletion K) y = i.symm y := by
    intro y
    conv_lhs => rw [← i.apply_symm_apply y]
    show Algebra.norm (v.adicCompletion K) (algebraMap (v.adicCompletion K) (u.adicCompletion M) (i.symm y)) = _
    rw [Algebra.norm_algebraMap, h1, pow_one]
  refine ⟨?_, fun y => key y⟩
  have e : (i.symm : u.adicCompletion M → v.adicCompletion K) = fun y => Algebra.norm (v.adicCompletion K) y :=
    funext fun y => (key y).symm
  rw [e]
  exact hc

end Split

section Char

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem trGL_ofChar (i : k ≃+* k') (hi' : Continuous i.symm) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (χ' : k'ˣ →* ℂˣ) (hχ' : IsSmoothChar χ')
    (h : ∀ y : k'ˣ, χ' y = χ (Units.map (i.symm : k' →* k) y)) :
    GlobalTheory.SuppIne.trGL i hi' (IrrGL.ofChar χ hχ) = IrrGL.ofChar χ' hχ' := by
  refine congrArg (Sigma.mk 1) (IrrRep.cl_eq_iff.2 ?_)
  obtain ⟨φ⟩ := IrrRep.nonempty_equiv_rep (IrrRep.det (Fin 1) χ hχ)
  refine ⟨Representation.Equiv.mk φ.toLinearEquiv fun g => ?_⟩
  have H := φ.toIntertwiningMap.isIntertwining' (Matrix.GeneralLinearGroup.map (n := Fin 1) i.symm.toRingHom g)
  refine LinearMap.ext fun x => ?_
  have Hx := LinearMap.congr_fun H x
  simp only [LinearMap.coe_comp, Function.comp_apply] at Hx ⊢
  change φ.toLinearEquiv _ = _
  refine Hx.trans ?_
  erw [Function.comp_apply, LinearMap.comp_apply, SmGL.twist_apply, SmGL.twist_apply]
  have e1 : ∀ g' : GL (Fin 1) k', (detChar (Fin 1) χ') g' =
      (detChar (Fin 1) χ) (GeneralLinearGroup.map i.symm.toRingHom g') := fun g' => by
    rw [detChar_apply, detChar_apply, Matrix.GeneralLinearGroup.map_det]; exact h _
  erw [e1 g]
  rfl

end Char

end GlobalTheory.CharLiftStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtOfSphericalAndTwistSphericalStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_unrAt_of_spherical_and_twist_spherical : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)), (∃ B, (CG.mk π).HasSat w B) → GlobalTheory.LGrp.IsSpherical ((π.twist ξ).locRep w) (GlobalTheory.LFun.KGL w a) → ξ.UnrAt w := by
  first | exact @GlobalTheory.SphTwistUnr.unrAt_of_isSpherical_twist | exact GlobalTheory.SphTwistUnr.unrAt_of_isSpherical_twist | (intros; apply GlobalTheory.SphTwistUnr.unrAt_of_isSpherical_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtUnderOfCompNormUnramifiedStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_unrAt_under_of_compNorm_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar (maximalRealSubfield E)) (w : HeightOneSpectrum (𝓞 E)), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → (compNorm E χ).UnrAt w → χ.UnrAt (w.under (𝓞 (maximalRealSubfield E))) := by
  first | exact @GlobalTheory.NormBelow.unrAt_under_of_compNorm | exact GlobalTheory.NormBelow.unrAt_under_of_compNorm | (intros; apply GlobalTheory.NormBelow.unrAt_under_of_compNorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfiniteQuadraticCMGoodBaseChangeSplitStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_quadraticCM_goodBaseChange_split : AutomorphicFormsFiniteGL → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (a : ℕ) (π : CuspSub E a) (w₀ : HeightOneSpectrum (𝓞 E)), {Q : GlobalTheory.RealGal.QCM E Ω | (∀ A : ValuationSubring Ω, IsPlaceOver A w₀ → Dec (F := E) A ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range) ∧ (∀ w : HeightOneSpectrum (𝓞 ↥Q.K), w.under (𝓞 E) = w₀ → GlobalTheory.UnitaryBC.IsSplitAt w) ∧ (∃ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ Algebra.IsUnramifiedAt (𝓞 E) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 E)) B) ∧ ∀ P : CuspSub ↥Q.K a, IsLift π P → Good l P}.Infinite := by
  first | exact @GlobalTheory.GalCut.infinite_qcm_split_good | exact GlobalTheory.GalCut.infinite_qcm_split_good | (intros; apply GlobalTheory.GalCut.infinite_qcm_split_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfContragredientConjugateStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSpherical_twist_of_contragredient_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (ψ : HChar E), GlobalTheory.ContraPair.DualIsConjBy π ψ → ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → (∃ B, (CG.mk π).HasSat w B) → GlobalTheory.LGrp.IsSpherical ((π.twist ψ⁻¹).locRep w) (GlobalTheory.LFun.KGL w a) := by
  first | exact @GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy | exact GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy | (intros; apply GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointDataAtPAndAdelicDatumNonemptyStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jointData_at_p_and_adelicDatum_nonempty : Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), Nonempty (J.At std) := by
  first | exact @GlobalTheory.TwV.joint_at_nonempty | exact GlobalTheory.TwV.joint_at_nonempty | (intros; apply GlobalTheory.TwV.joint_at_nonempty <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelRelationTrueColumnsJointsAllTuplesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.TwV
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_relation_true_columns_joints_all_tuples : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp) (nch : NChoice (I.rec7 l Z)) (tp : Formalism.L2.Host.TupTied (I.rec7 l Z) (I.cf l Z) nch), tp.xi = I.xi → I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → I.StdC l Z C → (∀ u, I.StdLvC l Z u (C.forms u)) → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → G.LatTied hT Gi Gl → (∃ t' : KerEntTied ex, ∀ μ, JointsAt t' μ) ∧ ∀ u, ex.tw.e0 u (I.rec7 l Z).what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _) := by
  first | exact @GlobalTheory.Pdv.oneTie_jointsAt_all | exact GlobalTheory.Pdv.oneTie_jointsAt_all | (intros; apply GlobalTheory.Pdv.oneTie_jointsAt_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedFormsOperatorDegreesAtKernelSourceStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedForms_operator_degrees_at_kernelSource : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std), ∀ j < D.R.m, Nonempty (Lv.comp (j + 1)) → ∀ (hN : RankTie (sysS H X std) D j), MoveH S.Y u μ (kaAt X H hT).cmp (fun j La => glInv (sysS H X std) j (BOf d.fd2 j La)) (gmS d) j ∧ TieOpS (Y := S.Y) t u μ (clsAt X H) (gmS d) (sO d ι) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) (ι := ι) (phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j) ∧ KernelEntryDegreeCondition (Y := S.Y) t u μ (clsAt X H) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN)) := by
  first | exact @GlobalTheory.TwV.DelA.moved_forms_at_source | exact GlobalTheory.TwV.DelA.moved_forms_at_source | (intros; apply GlobalTheory.TwV.DelA.moved_forms_at_source <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairSatakeParameterConjugatePlaceStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarizedPair_satakeParameter_conjugatePlace : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), GlobalTheory.ContraPair.PolarizedPair π χ → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ B : Multiset ℂˣ, (CG.mk π).HasSat w B → (CG.mk π).HasSat (UpperTheory.V.Af.Bc.cPl w) (B.map fun α => α⁻¹ * (compNorm E χ).val w) := by
  first | exact @GlobalTheory.PolarizedSat.hasSat_conjPlace | exact GlobalTheory.PolarizedSat.hasSat_conjPlace | (intros; apply GlobalTheory.PolarizedSat.hasSat_conjPlace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticHeckeCharUnramifiedOfIsUnramifiedAtStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticHeckeChar_unramified_of_isUnramifiedAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → (quadChar E).UnrAt (w.under (𝓞 (maximalRealSubfield E))) := by
  first | exact @GlobalTheory.QuadCharUnr.quadChar_unrAt_of_isUnramifiedAt | exact GlobalTheory.QuadCharUnr.quadChar_unrAt_of_isUnramifiedAt | (intros; apply GlobalTheory.QuadCharUnr.quadChar_unrAt_of_isUnramifiedAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SolvableAscentInduction
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.SolvUp

theorem exists_normal_prime_index (Γ : Type) [Group Γ] [Finite Γ] [Nontrivial Γ] [Group.IsSolvable Γ] :
    ∃ H : Subgroup Γ, H.Normal ∧ H.index.Prime := by
  obtain ⟨H, hH, hle⟩ := (eq_top_or_exists_le_coatom (commutator Γ)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial Γ).ne
  have hn : H.Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ H :=
      hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    simpa using H.mul_mem h1 hn⟩
  refine ⟨H, hn, ?_⟩
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (Γ ⧸ H)) (mt Subgroup.index_eq_one.1 hH.1)
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  have h1 : (Subgroup.zpowers g).comap (QuotientGroup.mk' H) = ⊤ := by
    refine hH.2 _ (lt_of_le_of_ne (fun x hx => ?_) fun e => ?_)
    · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact one_mem _
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H g
      have hx : x ∈ H := e ▸ Subgroup.mem_zpowers _
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx, orderOf_one] at hg
      exact hp.one_lt.ne hg
  have h2 : Subgroup.zpowers g = ⊤ :=
    Subgroup.comap_injective (QuotientGroup.mk'_surjective H) (h1.trans (Subgroup.comap_top _).symm)
  rw [Subgroup.index, ← Subgroup.card_top, ← h2, Nat.card_zpowers, hg]
  exact hp

theorem isCMField_of_ringEquiv {A B : Type} [Field A] [NumberField A] [Field B] [NumberField B] [IsCMField A]
    (e : A ≃+* B) : IsCMField B := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  haveI : IsTotallyComplex B := isTotallyComplex_of_algebra A B
  letI : Algebra (maximalRealSubfield A) B :=
    ((e : A →+* B).comp (algebraMap (maximalRealSubfield A) A)).toAlgebra
  let f : A ≃ₐ[maximalRealSubfield A] B := { e with commutes' := fun _ => rfl }
  haveI : Module.Free (maximalRealSubfield A) B := Module.Free.of_equiv f.toLinearEquiv
  haveI : Algebra.IsQuadraticExtension (maximalRealSubfield A) B :=
    ⟨by rw [← f.toLinearEquiv.finrank_eq]; exact Algebra.IsQuadraticExtension.finrank_eq_two _ _⟩
  exact IsCMField.ofCMExtension (maximalRealSubfield A) B

end GlobalTheory.SolvUp

namespace GlobalTheory.SolvUp

theorem isCMField_intermediate (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [IsCMField M] [Algebra M Ω] [Algebra K M]
    [IsScalarTower K M Ω] (L : IntermediateField K M) : IsCMField L := by
  let f := IsScalarTower.toAlgHom K M Ω
  haveI : NumberField f.fieldRange := NumberField.of_ringEquiv M _ (AlgEquiv.ofInjectiveField f).toRingEquiv
  haveI : NumberField (L.map f) := NumberField.of_ringEquiv L _ (IntermediateField.equivMap L f).toRingEquiv
  haveI : IsCMField f.fieldRange := isCMField_of_ringEquiv (AlgEquiv.ofInjectiveField f).toRingEquiv
  have hle : L.map f ≤ f.fieldRange := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := (IntermediateField.mem_map L).1 hy
    exact AlgHom.mem_fieldRange.2 ⟨x, rfl⟩
  haveI : IsCMField (L.map f) := (GlobalTheory.T.cm_subfields_compositum_closed Ω K).2.1 f.fieldRange (L.map f) hle inferInstance
  exact isCMField_of_ringEquiv (IntermediateField.equivMap L f).symm.toRingEquiv

end GlobalTheory.SolvUp
end
end

