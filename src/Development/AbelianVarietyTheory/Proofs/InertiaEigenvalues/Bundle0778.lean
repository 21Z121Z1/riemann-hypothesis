import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalUnitaryDoubledLagrangianFrameWitt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0756
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0757
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0773
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0772
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeAleph0SmoothIrreducibleUnitaryAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0398
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeLocus
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0320
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0200
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0358
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0758
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0774
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalUnitaryDoubledLagrangianFrameWittStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_unitary_doubledLagrangianFrame_witt : ∀ (D : D7) (W : HSp D) (Y : Lag W), ∃ γ : GA D (GlobalTheory.Doubling.dblSp W), γ ∈ GQ (GlobalTheory.Doubling.dblSp W) ∧ ∃ (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E), Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D) ∧ IsLagFrame W Y (frameOf W g₀) := by
  first | exact @GlobalTheory.SWLagTerms.exists_rat_unitary_lagFrame | exact GlobalTheory.SWLagTerms.exists_rat_unitary_lagFrame | (intros; apply GlobalTheory.SWLagTerms.exists_rat_unitary_lagFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterInertDatumOfDictionarySpher
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SatExist

theorem exists_satAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α := by
  classical
  intro L _ _ _ n F π U₀ _ v w _ hsph Dv
  obtain ⟨f₀, hf₀S, hf₀0, hf₀K⟩ := hsph
  obtain ⟨-, N, hN, hf₀N⟩ := π.irrS.1.le hf₀S
  obtain ⟨U, hCU, hU, hdec⟩ := GlobalTheory.T.exists_level_full_at_inert_place_principal_elsewhere L n v N hN
  have hdec' : ∀ κ ∈ U, ∃ a b : GAf L n, κ = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ b ∈ U ∧
      ∀ x : GAf L n, TrivOutside {v} x → b * x = x * b := fun κ hκ => by
    obtain ⟨a, b, e, ha, hta, hb, hc⟩ := hdec κ hκ
    exact ⟨a, b, e, ha, hta, hCU b hb, hc⟩
  have hf₀U : ∀ κ ∈ U, NG.rt L n κ f₀ = f₀ := fun κ hκ => by
    obtain ⟨a, b, rfl, ha, hta, hb, -⟩ := hdec κ hκ
    funext g
    show f₀ (g * (a * b)) = f₀ g
    rw [← mul_assoc, hf₀N b hb]
    exact congrFun (hf₀K a ha hta) g
  let V : Submodule ℂ (GAf L n → π.W) :=
    { carrier := {f | f ∈ π.S ∧ ∀ κ ∈ U, NG.rt L n κ f = f}
      add_mem' := fun {f f'} hf hf' => ⟨π.S.add_mem hf.1 hf'.1, fun κ hκ => by
        rw [map_add, hf.2 κ hκ, hf'.2 κ hκ]⟩
      zero_mem' := ⟨π.S.zero_mem, fun κ _ => map_zero _⟩
      smul_mem' := fun c f hf => ⟨π.S.smul_mem c hf.1, fun κ hκ => by rw [map_smul, hf.2 κ hκ]⟩ }
  haveI : FiniteDimensional ℂ π.W := π.alg.1
  haveI := GlobalTheory.AlgFormsFin.fixedForms_finite L n π.ρ (GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n) hN
  haveI hVfin : FiniteDimensional ℂ V :=
    Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n π.ρ N) fun f hf =>
      ⟨(π.irrS.1.le hf.1).1, fun κ hκ g => congrFun (hf.2 κ (hCU κ hκ)) g⟩
  have hfin := fun h hh => GlobalTheory.SatInd.CosetFin.finite_inert_support L n v w Dv
    (GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram)
    (GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv) U hU h hh
  have hmemV : ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), ∀ f ∈ V, heckeFunI L n U Dv h f ∈ V := by
    intro h hh f hf
    refine ⟨?_, GlobalTheory.T.inertHeckeOperator_preserves_productLevel_invariance L n v w Dv U hU hdec' π.W h hh f hf.2⟩
    obtain ⟨C, a, x, hC⟩ := GlobalTheory.SatIso.heckeFunI_eq_sum Dv U h (hfin h hh)
    rw [hC]
    exact π.S.sum_mem fun c _ => π.S.smul_mem _ (π.irrS.1.stable _ _ hf.1)
  let T : (Formalism.UG.GU Dv.σw n → ℂ) → Module.End ℂ V := fun h =>
    if hh : h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) then
      { toFun := fun f => ⟨heckeFunI L n U Dv h f, hmemV h hh f f.2⟩
        map_add' := fun f f' => Subtype.ext (by
          obtain ⟨C, a, x, hC⟩ := GlobalTheory.SatIso.heckeFunI_eq_sum Dv U h (hfin h hh)
          simp only [Submodule.coe_add, hC, map_add, smul_add, Finset.sum_add_distrib])
        map_smul' := fun c f => Subtype.ext (by
          obtain ⟨C, a, x, hC⟩ := GlobalTheory.SatIso.heckeFunI_eq_sum Dv U h (hfin h hh)
          simp only [Submodule.coe_smul, hC, map_smul, RingHom.id_apply, Finset.smul_sum]
          exact Finset.sum_congr rfl fun c' _ => smul_comm _ _ _) }
    else 0
  have hT : ∀ h (hh : h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n)) (f : V),
      ((T h f : V) : GAf L n → π.W) = heckeFunI L n U Dv h f := fun h hh f => by
    simp only [T, dif_pos hh]
    rfl
  have hK := Formalism.UG.P.isCommensurated_integral_unitary_of_unramified Dv.unram n
  obtain ⟨α, x, hx0, hx⟩ := GlobalTheory.T.exists_satU_eigenvector_alt Dv.ϖ Dv.σw _ n Dv.unram V T
    (fun h₁ hh₁ h₂ hh₂ => LinearMap.ext fun f => Subtype.ext (by
      rw [LinearMap.add_apply, Submodule.coe_add, hT (h₁ + h₂) (add_mem hh₁ hh₂) f, hT h₁ hh₁ f, hT h₂ hh₂ f]
      exact (GlobalTheory.T.heckeFunI_add_and_smul L n v w Dv U hU π.W h₁ h₂ hh₁ hh₂ 0 f).1))
    (fun c h hh => LinearMap.ext fun f => Subtype.ext (by
      rw [LinearMap.smul_apply, Submodule.coe_smul, hT (c • h) (Submodule.smul_mem _ c hh) f, hT h hh f]
      exact (GlobalTheory.T.heckeFunI_add_and_smul L n v w Dv U hU π.W h h hh hh c f).2))
    (LinearMap.ext fun f => Subtype.ext (by
      rw [hT _ (Formalism.UG.Final.DosetIndMem _ _ ℂ 1) f]
      exact GlobalTheory.T.inertHeckeOperator_maximalCompact_indicator_eq_id L n v w Dv U hU π.W f f.2.2))
    (fun h₁ hh₁ h₂ hh₂ => LinearMap.ext fun f => Subtype.ext (by
      rw [Module.End.mul_apply, hT _ (Formalism.UG.Final.HeckeConvMem _ _ ℂ hK _ hh₁ _ hh₂) f, hT h₁ hh₁ (T h₂ f), hT h₂ hh₂ f]
      exact GlobalTheory.T.inertHeckeOperator_convolution_eq_comp L n v w Dv U hU π.W h₁ h₂ hh₁ hh₂ f f.2.2))
    ⟨f₀, hf₀S, hf₀U⟩ (fun h => hf₀0 (congrArg Subtype.val h))
  refine ⟨α, x, x.2.1, fun h => hx0 (Subtype.ext h), U, x.2.2, hU, fun h hh => ?_⟩
  have e := congrArg Subtype.val (hx h hh)
  rw [hT h hh] at e
  exact e

end GlobalTheory.SatExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitOfGPl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain GlobalTheory.HeightCounting
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FormInner

section Plain

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

open GlobalTheory.InertUmax

omit [IsCMField L] in

theorem exists_trunc (b : AFplus L) : ∃ c : AFplus L, (∀ w, c w ∈ w.adicCompletionIntegers (maximalRealSubfield L)) ∧
    ∀ w, b w ∈ w.adicCompletionIntegers (maximalRealSubfield L) → c w = b w := by
  have h : ∀ w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)), ∃ z : w.adicCompletion (maximalRealSubfield L),
      z ∈ w.adicCompletionIntegers (maximalRealSubfield L) ∧ (b w ∈ w.adicCompletionIntegers (maximalRealSubfield L) → z = b w) := by
    intro w
    by_cases hw : b w ∈ w.adicCompletionIntegers (maximalRealSubfield L)
    · exact ⟨b w, hw, fun _ => rfl⟩
    · exact ⟨0, zero_mem _, fun h => absurd h hw⟩
  choose z h1 h2 using h
  exact ⟨⟨z, Filter.Eventually.of_forall h1⟩, h1, h2⟩

theorem exists_int_off (z : AL L) : ∃ S : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L))), ∃ Y ∈ ALint L,
    ∀ w ∉ S, ReciprocityTheory.Aut.compAt L w z = ReciprocityTheory.Aut.compAt L w Y := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨∅, 0, zero_mem _, fun _ _ => rfl⟩
  | add x y hx hy =>
    obtain ⟨S, Y, hY, h⟩ := hx
    obtain ⟨S', Y', hY', h'⟩ := hy
    refine ⟨S ∪ S', Y + Y', add_mem hY hY', fun w hw => ?_⟩
    rw [Finset.mem_union, not_or] at hw
    rw [map_add, map_add, h w hw.1, h' w hw.2]
  | tmul x a =>
    obtain ⟨m, hm, o, ho⟩ := GlobalTheory.FinTypCount.exists_nat_smul_int x
    have hm' : (m : maximalRealSubfield L) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    obtain ⟨b, hb⟩ : ∃ b : AFplus L, b = (m : maximalRealSubfield L)⁻¹ • a := ⟨_, rfl⟩
    have e : (x ⊗ₜ[maximalRealSubfield L] a : AL L) = (o : L) ⊗ₜ[maximalRealSubfield L] b := by
      rw [ho, hb, ← Nat.cast_smul_eq_nsmul (maximalRealSubfield L), TensorProduct.smul_tmul, smul_inv_smul₀ hm']
    have hfin : {w : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) |
        b w ∉ w.adicCompletionIntegers (maximalRealSubfield L)}.Finite := Filter.eventually_cofinite.1 b.2
    obtain ⟨c, hc, hc'⟩ := exists_trunc b
    refine ⟨hfin.toFinset, (o : L) ⊗ₜ[maximalRealSubfield L] c, GlobalTheory.FinTypCount.tmul_mem_ALint o hc, fun w hw => ?_⟩
    rw [e, compAt_tmul, compAt_tmul, hc' w (by simpa using hw)]

theorem mem_ALint_of_comp (z : AL L) (h : ∀ w, ∃ Y ∈ ALint L, ReciprocityTheory.Aut.compAt L w Y = ReciprocityTheory.Aut.compAt L w z) : z ∈ ALint L := by
  classical
  obtain ⟨S, Y, hY, hS⟩ := exists_int_off z
  choose Z hZ e using h
  have key : z - (Y + ∑ v ∈ S, (Z v - Y) * ((1 : L) ⊗ₜ[maximalRealSubfield L] sgl L v 1)) = 0 := by
    apply eq_zero_of_compAt
    intro w
    rw [map_sub, map_add, map_sum]
    simp only [map_mul, compAt_tmul]
    by_cases hw : w ∈ S
    · rw [Finset.sum_eq_single w (fun v _ hv => by rw [sgl_ne L v 1 (Ne.symm hv), TensorProduct.tmul_zero, mul_zero])
        (fun h => absurd hw h), sgl_same, ← Algebra.TensorProduct.one_def, mul_one, map_sub, e]
      ring
    · rw [Finset.sum_eq_zero fun v hv => by
        rw [sgl_ne L v 1 (fun h : w = v => hw (h ▸ hv)), TensorProduct.tmul_zero, mul_zero], hS w hw]
      ring
  rw [sub_eq_zero.1 key]
  exact add_mem hY (Subring.sum_mem _ fun v _ => mul_mem (sub_mem (hZ v) hY) (one_tmul_sgl_mem L v 1 (one_mem _)))

theorem le_Umax_of_prod {J : Subgroup (GAf L n)} (hJ : NG.IsProdLevel J)
    (h : ∀ v, ∀ κ ∈ J, TrivOutside {v} κ → κ ∈ Umax L n) : J ≤ Umax L n := by
  intro κ hκ i j
  refine mem_ALint_of_comp _ fun w => ?_
  obtain ⟨κ', h1, h2, h3⟩ := hJ κ hκ w
  exact ⟨_, h w κ' h1 h2 i j, congrFun (congrFun h3 i) j⟩

theorem mem_Umax_of_para (s : SplitPlace L) {r : ℕ} {κ : GAf L n} (h1 : TrivOutside {s.v} κ) (h2 : NG.ParaRT s r (s.loc n κ)) :
    κ ∈ Umax L n := by
  have h := GlobalTheory.HeckeStdFacts.mem_GLint_iff.1 h2.1
  refine GlobalTheory.HeckeStdFacts.mem_Umax_of_loc s κ h1 h.1 fun i j => ?_
  rw [map_inv]
  exact h.2 i j

end Plain

theorem exists_split_of_gPl (D : D7) : ∀ v ∈ Formalism.L2.gPl D, ∃ (k : Fin 2) (u : D.nd.PlG k) (s : SplitPlace D.host.E),
    s.v = v ∧ s.w = D.naut.plGw k u := by
  rintro v ⟨w, hw, k, hk⟩
  obtain ⟨u, hu⟩ := GlobalTheory.DimPartsCompare.cover k w hk
  obtain ⟨s, hs⟩ := GlobalTheory.SplitPlaceOfFixed.exists_splitPlace_plGw D ⟨k, u⟩
  refine ⟨k, u, s, HeightOneSpectrum.ext ?_, hs⟩
  rw [← s.w_under, hs]
  refine Eq.trans ?_ hw
  rcases hu with rfl | rfl
  · rfl
  · ext a
    refine GlobalTheory.DimPartsCompare.isConjPl_cPl _ _ _ ?_
    rw [GlobalTheory.SplitPlaceOver.host_conj_eq']
    exact ((IsCMField.complexConj D.host.E).commutes (a : maximalRealSubfield D.host.E)).symm

theorem level_le_Umax {D : D7} {M : MtFam D} {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E}
    {Q : D.what₂.places.Pl → Finset (PlE D.host)} (h : MtInput D M tup Q) (w : D.what₂.places.Pl) (j : Fin D.R.m) :
    (M (D.what₂.muTw w) (j.1 + 1) (by omega) (by omega)).J ≤ Umax D.host.E D.R.nV := by
  refine le_Umax_of_prod (h.prod w j) fun v κ hκ hv => ?_
  by_cases hg : v ∈ Formalism.L2.gPl D
  · obtain ⟨k, u, s, rfl, hs⟩ := exists_split_of_gPl D v hg
    obtain ⟨ψ₀, ξ, -, -, hl⟩ := h.uni w j k u s hs
    exact mem_Umax_of_para s hv ((hl.mem κ hv).1 hκ).1
  by_cases hq : v ∈ qPl D (tup (D.what₂.muTw w) j)
  · obtain ⟨s, ξ, rfl, -, hl⟩ := h.para w j v hq
    exact mem_Umax_of_para s hv ((hl.mem κ hv).1 hκ)
  · refine (h.hyp w j κ fun u hu => hv u ?_).1.1 hκ
    rintro rfl
    exact hu fun h' => h'.elim hg hq

end GlobalTheory.FormInner

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeLocusStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_type_locus : ∀ (D : D7) (P : Pend D), GlobalTheory.TypeLeaf.SerLoc D → admBC (D := D) → LocalGlobalCompatibilityAlt (D := D) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → EigSpan P → CentralElt D → ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → ∀ π ∈ D.nd.Zgood i, ∃ (Xs : Set (D.nd.X i)) (β : Module.End (D.nd.O i) (D.nd.Mt i)) (b : D.nd.O i), CutAt i k π Xs β b ∧ TypeLocus P i k Xs := by
  first | exact @GlobalTheory.CutAtGood.main | exact GlobalTheory.CutAtGood.main | (intros; apply GlobalTheory.CutAtGood.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtTensorTwistApply
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.IndChain.SuppStep

open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LocGL
open scoped TensorProduct

variable {g : ℕ} [Fact g.Prime]

theorem isUnram_of_supp {ν : ℚ_[g]ˣ →* ℂˣ} (h : Supp.IsUnram ν) : GlobalTheory.SplitWeil.IsUnram ν := by
  intro x hx
  have a1 := GlobalTheory.SplitWeil.padic_valuation_lt_iff g (x : ℚ_[g]) 1
  have a2 := GlobalTheory.SplitWeil.padic_valuation_lt_iff g 1 (x : ℚ_[g])
  rw [hx, map_one] at a1 a2
  have h1 : ‖(x : ℚ_[g])‖ = 1 := by
    simp only [lt_self_iff_false, norm_one, false_iff, not_lt] at a1 a2
    exact le_antisymm a2 a1
  have := h (PadicInt.mkUnits h1)
  convert this using 2
  exact Units.ext rfl

theorem extTensor_twist_apply {a b : ℕ} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W')
    (χ₁ : GL (Fin a) ℚ_[g] →* ℂˣ) (χ₂ : GL (Fin b) ℚ_[g] →* ℂˣ) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g])
    (w : W ⊗[ℂ] W') :
    extTensor (twist σ χ₁) (twist ρ χ₂) (x, y) w = ((χ₁ x * χ₂ y : ℂˣ) : ℂ) • TensorProduct.map (σ x) (ρ y) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => rw [map_add, hu, hv, map_add, smul_add]
  | tmul u v =>
    rw [extTensor_tmul, TensorProduct.map_tmul, twist_apply, twist_apply, TensorProduct.smul_tmul_smul,
      Units.val_mul]

theorem scal_eq (ν₁ ν₂ A B : ℚ_[g]ˣ →* ℂˣ) (u v : ℚ_[g]ˣ) :
    (A u * B v) * ((ν₁ * A⁻¹) u * (ν₂ * B⁻¹) v) = ν₁ u * ν₂ v := by
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
  simp [mul_assoc, mul_comm, mul_left_comm]

theorem law {a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (π : Representation ℂ (GL (Fin (a + b)) ℚ_[g]) V)
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W')
    (ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ) (Λ : V →ₗ[ℂ] W ⊗[ℂ] W')
    (hΛ : ∀ (p : GL (Fin (a + b)) ℚ_[g]) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g]),
      (∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j = 0) →
      (∀ i j : Fin a, (x : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
        Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j) →
      (∀ i j : Fin b, (y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
        Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (a + i) (a + j)) →
      ∀ v, Λ (π p v) = ((ν₁ (Matrix.GeneralLinearGroup.det x) * ν₂ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) •
        TensorProduct.map (σ x) (ρ y) (Λ v))
    (q : parab ℚ_[g] (two (stdSum (rfl : a + b = a + b)))) (w : V) :
    Λ (π q w) = (deltaHalf ℚ_[g] (Two (Fin a) (Fin b)) (leviProj ℚ_[g] _ q) : ℂ) •
      extTensor (twist σ (detChar (Fin a) (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹)))
        (twist ρ (detChar (Fin b) (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹)))
        ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)) (Λ w) := by
  set X := ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)).1 with hX
  set Y := ((leviTwo ℚ_[g] (Fin a) (Fin b)).symm (leviProj ℚ_[g] _ q)).2 with hY
  have hL : leviProj ℚ_[g] _ q = leviTwo ℚ_[g] _ _ (X, Y) := (MulEquiv.apply_symm_apply _ _).symm
  have hpar := (mem_parab_two ℚ_[g]).1 q.2
  have h0 : ∀ i j : Fin (a + b), (j : ℕ) < a → a ≤ (i : ℕ) →
      ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j = 0 := by
    intro i j hj hi
    have e1 : stdSum (rfl : a + b = a + b) (.inr ⟨i - a, by omega⟩) = i := Fin.ext (by rw [stdSum_inr]; simp; omega)
    have e2 : stdSum (rfl : a + b = a + b) (.inl ⟨j, hj⟩) = j := Fin.ext (by rw [stdSum_inl])
    have := hpar ⟨i - a, by omega⟩ ⟨j, hj⟩
    rwa [e1, e2] at this
  have hx : ∀ i j : Fin a, (X : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) i j := by
    intro i j
    have hi := i.2
    have hj := j.2
    rw [Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos ⟨by omega, by omega⟩]
    show ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (stdSum (rfl : a + b = a + b) (.inl i)) (stdSum (rfl : a + b = a + b) (.inl j)) = _
    congr 1 <;> exact Fin.ext (stdSum_inl _ _)
  have hy : ∀ i j : Fin b, (Y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (a + i) (a + j) := by
    intro i j
    have hi := i.2
    have hj := j.2
    rw [Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos ⟨by omega, by omega⟩]
    show ((q : GL (Fin (a + b)) ℚ_[g]) : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[g]) (stdSum (rfl : a + b = a + b) (.inr i)) (stdSum (rfl : a + b = a + b) (.inr j)) = _
    congr 1 <;> exact Fin.ext (stdSum_inr _ _)
  rw [hΛ q X Y h0 hx hy w, hL, MulEquiv.symm_apply_apply, deltaHalf_two, extTensor_twist_apply, smul_smul,
    ← Units.val_mul, detChar_apply, detChar_apply]
  simp only [Fintype.card_fin]
  rw [scal_eq]

theorem supp_of_mapsToProd : GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (g : ℕ) [Fact g.Prime] (n a b : ℕ) (V W W' : Type)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W)
    (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W'),
    GlobalTheory.PRep.IsSmooth π → π.IsIrreducible → Supp.MapsToProd π σ ρ →
    ∀ (ys yr : Multiset (GlobalTheory.LocGL.IrrGL ℚ_[g])), GlobalTheory.LocGL.HasSupport σ ys → GlobalTheory.LocGL.HasSupport ρ yr →
    ∃ (μ₁ μ₂ : ℚ_[g]ˣ →* ℂˣ) (h₁ : GlobalTheory.SplitWeil.IsUnram μ₁) (h₂ : GlobalTheory.SplitWeil.IsUnram μ₂),
      GlobalTheory.LocGL.HasSupport π (ys.map (fun x => x.tw μ₁ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₁)) +
        yr.map (fun x => x.tw μ₂ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₂))) := by
  intro hZ g _ n a b V W W' _ _ _ _ _ _ π σ ρ hs hπ hM ys yr hys hyr
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hZ ℚ_[g]
  obtain ⟨hn, ν₁, ν₂, Λ, h₁, h₂, hΛ0, hΛ⟩ := hM
  subst hn
  have hμ₁ : GlobalTheory.SplitWeil.IsUnram (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹) :=
    isUnram_mul (isUnram_of_supp h₁) (isUnram_inv (isUnram_absPow _ _))
  have hμ₂ : GlobalTheory.SplitWeil.IsUnram (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹) :=
    isUnram_mul (isUnram_of_supp h₂) (isUnram_inv (isUnram_absPow _ _))
  refine ⟨_, _, hμ₁, hμ₂, ?_⟩
  let T : π.IntertwiningMap (prod₂ (twist σ (detChar (Fin a) (ν₁ * (absPow ℚ_[g] ((b : ℂ) / 2))⁻¹)))
      (twist ρ (detChar (Fin b) (ν₂ * (absPow ℚ_[g] (-(a : ℂ) / 2))⁻¹)))) :=
    { toFun := fun v => ⟨⟨fun x => Λ (π x v), fun q x => by
          show Λ (π (q * x) v) = _
          rw [map_mul, Module.End.mul_apply]
          exact law π σ ρ ν₁ ν₂ Λ hΛ q (π x v)⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hs v).mem_nhds (by simp)) fun h hh => by
          have hh' : π h v = v := hh
          refine Subtype.ext (funext fun x => ?_)
          show Λ (π (x * h) v) = Λ (π x v)
          rw [map_mul, Module.End.mul_apply, hh'])⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by
        show Λ (π x (v + w)) = Λ (π x v) + Λ (π x w)
        rw [map_add, map_add]))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by
        show Λ (π x (c • v)) = c • Λ (π x v)
        rw [map_smul, map_smul]))
      isIntertwining' := fun h => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
        show Λ (π x (π h v)) = Λ (π (x * h) v)
        rw [map_mul, Module.End.mul_apply])) }
  have hT : Function.Injective T := by
    haveI := hπ
    refine (Representation.IsIrreducible.injective_or_eq_zero T).resolve_right fun h0 => hΛ0 (LinearMap.ext fun v => ?_)
    have h1 : (T v).1.1 1 = 0 := by rw [h0]; rfl
    change Λ (π 1 v) = 0 at h1
    simpa using h1
  have hσ' := hys.tw _ (isSmoothChar_of_isUnram hμ₁)
  have hρ' := hyr.tw _ (isSmoothChar_of_isUnram hμ₂)
  obtain ⟨φ⟩ := nonempty_prod₂_equiv_prodIrr _ hσ'.isSmooth hσ'.isIrreducible _ hρ'.isSmooth hρ'.isIrreducible
    (Fin.sum_univ_two _)
  have hsub := (IsSubquotient.of_injective T hT).trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have key := SupportRing.hasSupport_of_isSubquotient_prodIrr hΨ
    (t := ![_, _]) (Fin.forall_fin_two.2 ⟨hσ'.of_equiv (IrrGL.equivOf _ _ _), hρ'.of_equiv (IrrGL.equivOf _ _ _)⟩)
    hπ hsub
  rw [Fin.sum_univ_two] at key
  exact key

end GlobalTheory.IndChain.SuppStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinCompatLocalDegreeOneStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalArtin_compat_localDegreeOne : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∀ (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω) (art' : Neutral.B1.Ideles E' →* GlobalTheory.HeckeGal.Gab E' Ω'), GlobalTheory.HeckeGal.IsGlobalArtin art → GlobalTheory.HeckeGal.IsGlobalArtin art' → ∀ (σ : Weil h) (σ' : Weil h') (x : (w.adicCompletion E)ˣ), WeilRel φ σ σ' → art' (Neutral.B1.localIdele E' w' (Units.map i.toRingHom.toMonoidHom x)) = GlobalTheory.HeckeGal.toAb E' Ω' σ' → art (Neutral.B1.localIdele E w x) = GlobalTheory.HeckeGal.toAb E Ω σ := by
  first | exact @GlobalTheory.LocDegOne.artin_of_placeIso | exact GlobalTheory.LocDegOne.artin_of_placeIso | (intros; apply GlobalTheory.LocDegOne.artin_of_placeIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisenbergRealPointFockVacuumPairingScalarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_realPoint_fockVacuum_pairing_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) →
    IsInfFam θ → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ),
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
    ∀ w : WO S T, w.map (finPart D) = 0 → ∃ κ : ℂ, ∀ h e : WO S T → ℂ, IsThetaFunO ψ S T h → IsThetaFunO ψ S T e →
    (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) h) →
    (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) e) →
    thetaIP μ 𝓕 h (heisO ψ S T w e) = κ * thetaIP μ 𝓕 h e := by
  first | exact @GlobalTheory.RealVacScalar.compress_real | exact GlobalTheory.RealVacScalar.compress_real | (intros; apply GlobalTheory.RealVacScalar.compress_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFderivRealLieChartEqSumKernelOperators
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

theorem integral_fderiv_chart_eq : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a,
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) → ∀ g,
      ∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν =
        ∑ p, kerOp ν (fun x => k x * adCoef (γ x) p) γ (lie E a (lieBasis E a p.1) φ).1 g • lieCoord E a p.2 :=
  fun E _ _ _ a X _ ν k γ hk φ hb g =>
    integral_fderiv_chart_eq_of ν k γ (fun p => GlobalTheory.T.rapidlyDecreasingKernel_mul_adjointConjCoefficient E a X ν k γ hk p) φ hb g

end GlobalTheory.JSW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralHermitianAdjointCovolOnePeriodicEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_hermitianAdjoint_covolOne_periodic_eq : ∀ (D : D7) (V W : HSp D) (ν : Measure (Mx D V.rank W.rank)) (𝓖' : Set (Mx D V.rank W.rank)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL V W) ν 𝓖' → IsCovolOne (ratL W V) μ 𝓕 → ∀ (Φ : WO V W → ℂ), (∀ (γ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (u : WO V W), Φ (ratW W V γ + u) = Φ u) → ∫ y in 𝓖', Φ (GlobalTheory.PairLift.adjO V W y) ∂ν = ∫ u in 𝓕, Φ u ∂μ := by
  first | exact @GlobalTheory.SWChangeVar.integral_adjO_eq | exact GlobalTheory.SWChangeVar.integral_adjO_eq | (intros; apply GlobalTheory.SWChangeVar.integral_adjO_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeParameterSquarefreeStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_parameter_squarefree : StepType := by
  first | exact @GlobalTheory.Pass.stepType_proof | exact GlobalTheory.Pass.stepType_proof | (intros; apply GlobalTheory.Pass.stepType_proof <;> assumption)
end

