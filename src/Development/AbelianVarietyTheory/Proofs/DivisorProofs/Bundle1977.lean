import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1964
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1946
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1699
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0386
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0034
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0398
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0688
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0253
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Formalism.LocalToGlobal.Divisibility.DivisibilityConstruction.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.FaceOf3
import Formalism.LocalToGlobal.Divisibility.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1967
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterNormEulerFactorization
section
noncomputable section

namespace GlobalTheory.ThK.ConeEulerChr

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_liftV (a : ∀ v : Pl F, Fv F v) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) :
    Tendsto (fun v => GlobalTheory.LatVac.liftV v (a v)) cofinite (𝓝 0) := by
  have hf : ∀ v w : Pl F, evalV F w (singleFin v (a v)) ∈ w.adicCompletionIntegers F := fun v w => by
    by_cases h : w = v
    · subst h; rw [evalV_singleFin_self]; exact ha w
    · rw [evalV_singleFin_ne h]; exact zero_mem _
  have hc := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := cofinite)).continuous
  have ht : Tendsto (fun v : Pl F => fun w : HeightOneSpectrum (𝓞 F) =>
      (⟨evalV F w (singleFin v (a v)), hf v w⟩ : (w.adicCompletionIntegers F : Set (w.adicCompletion F)))) cofinite
      (𝓝 fun w => ⟨0, zero_mem (w.adicCompletionIntegers F)⟩) := by
    refine tendsto_pi_nhds.2 fun w => tendsto_subtype_rng.2 ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_cofinite_ne w] with v hv
    exact (evalV_singleFin_ne (Ne.symm hv) _).symm
  have h2 : Tendsto (fun v : Pl F => singleFin v (a v)) cofinite (𝓝 (0 : Af F)) := (hc.tendsto _).comp ht
  have hp : Continuous fun β : Af F => pairA F 0 β := continuous_const.prodMk continuous_id
  exact (hp.tendsto 0).comp h2

theorem exists_coords {v : Pl F} {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fv F v, (∀ i, a i ∈ v.adicCompletionIntegers F) ∧
      y = ∑ i, a i ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
  refine intLoc_induction (p := fun y => ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fv F v,
    (∀ i, a i ∈ v.adicCompletionIntegers F) ∧ y = ∑ i, a i ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E))
    (fun a ha x => ?_) ⟨0, fun _ => zero_mem _, by simp⟩ ?_ ?_ hy
  · refine ⟨fun i => (RingOfIntegers.basis E).repr x i • a, fun i => zsmul_mem ha _, ?_⟩
    have hx : (x : E) = ∑ i, (RingOfIntegers.basis E).repr x i • ((RingOfIntegers.basis E i : 𝓞 E) : E) := by
      conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr x]
      simp
    rw [hx, TensorProduct.tmul_sum]
    exact Finset.sum_congr rfl fun i _ => (TensorProduct.smul_tmul _ _ _).symm
  · rintro _ _ ⟨a, ha, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨a + c, fun i => add_mem (ha i) (hc i), by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨-a, fun i => neg_mem (ha i), by simp [TensorProduct.neg_tmul]⟩

theorem tendsto_zero_of_intLoc (x : Pl F → AE F E)
    (h : ∀ᶠ v in cofinite, At (evFin F v) (x v) ∧ compFin F E v (x v) ∈ intLoc F E v) :
    Tendsto x cofinite (𝓝 0) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have key : ∀ v : Pl F, ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fv F v,
      (∀ i, a i ∈ v.adicCompletionIntegers F) ∧ (At (evFin F v) (x v) ∧ compFin F E v (x v) ∈ intLoc F E v →
      x v = ∑ i, GlobalTheory.LatVac.liftV v (a i) • ((1 : AF F) ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E))) := fun v => by
    by_cases hv : At (evFin F v) (x v) ∧ compFin F E v (x v) ∈ intLoc F E v
    · obtain ⟨a, ha, e⟩ := exists_coords hv.2
      obtain ⟨h1, h2⟩ := at_evFin_iff.1 hv.1
      refine ⟨a, ha, fun _ => GlobalTheory.Doubling.adele_ext (fun w => ?_) fun w => ?_⟩
      · rw [h1, map_sum]
        exact (Finset.sum_eq_zero fun i _ => by
          rw [compInf_smul, show evInf F w (GlobalTheory.LatVac.liftV v (a i)) = 0 from rfl, zero_smul]).symm
      · rw [map_sum]
        by_cases hw : w = v
        · subst hw
          rw [e]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [compFin_smul, GlobalTheory.LatVac.evFin_liftV]
          change _ = a i • (evFin F w 1 ⊗ₜ[F] _)
          rw [map_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          rfl
        · rw [h2 w hw]
          exact (Finset.sum_eq_zero fun i _ => by
            rw [compFin_smul, show evFin F w (GlobalTheory.LatVac.liftV v (a i)) = 0 from evalV_singleFin_ne hw _,
              zero_smul]).symm
    · exact ⟨0, fun _ => zero_mem _, fun h => absurd h hv⟩
  choose a ha e using key
  have ht : Tendsto (fun v => ∑ i, GlobalTheory.LatVac.liftV v (a v i) •
      ((1 : AF F) ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E) : AE F E)) cofinite
      (𝓝 (∑ i, (0 : AF F) • ((1 : AF F) ⊗ₜ[F] ((RingOfIntegers.basis E i : 𝓞 E) : E) : AE F E))) :=
    tendsto_finset_sum _ fun i _ => (tendsto_liftV (fun v => a v i) fun v => ha v i).smul_const _
  simp only [zero_smul, Finset.sum_const_zero] at ht
  refine ht.congr' ?_
  filter_upwards [h] with v hv using (e v hv).symm

theorem tendsto_one_of_unitsAt (m : Pl F → (AE F E)ˣ) (h : ∀ᶠ v in cofinite, m v ∈ unitsAt E v) :
    Tendsto m cofinite (𝓝 1) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have key : ∀ m : Pl F → (AE F E)ˣ, (∀ᶠ v in cofinite, m v ∈ unitsAt E v) →
      Tendsto (fun v => (m v : AE F E)) cofinite (𝓝 1) := fun m h => by
    have := (tendsto_zero_of_intLoc (fun v => (m v : AE F E) - 1) (h.mono fun v hv => ⟨hv.1, by
      rw [map_sub, map_one]; exact sub_mem (mem_unitsAt.1 hv).2.1 (one_mem _)⟩)).add_const 1
    simpa using this
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact (key m h).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp
    (key (fun v => (m v)⁻¹) (h.mono fun v hv => inv_mem hv)))

theorem eventually_chr_eq_one {ν : Chr F E} (hν : Continuous ν) (m : Pl F → (AE F E)ˣ)
    (h : ∀ᶠ v in cofinite, m v ∈ unitsAt E v) : ∀ᶠ v in cofinite, ν (m v) = 1 := by
  have key : ∀ v, ∃ n : ℕ, ‖(ν (m v) : ℂ) ^ n - 1‖ < 1 → ν (m v) = 1 := fun v => by
    by_contra hc
    push Not at hc
    exact (hc 0).2 (GlobalTheory.CharDualMat.circle_eq_one_of_pow_near _ fun n => (hc n).1)
  choose n hn using key
  have ht := tendsto_one_of_unitsAt (fun v => m v ^ n v) (h.mono fun v hv => pow_mem hv _)
  have hc : Continuous fun x : (AE F E)ˣ => ‖(ν x : ℂ) - 1‖ :=
    ((continuous_subtype_val.comp hν).sub continuous_const).norm
  have h1 := ((hc.tendsto 1).comp ht).eventually (gt_mem_nhds (show ‖(ν 1 : ℂ) - 1‖ < 1 by simp))
  filter_upwards [h1] with v hv
  exact hn v (by simpa using hv)

theorem cutIdele_eq (S : Finset (Pl F)) (l : (AE F E)ˣ) :
    GlobalTheory.Doubling.cutIdele S l = unitArch F E l * ∏ v ∈ S, unitAt E v l := by
  have h1 : (eInf F).1 = 1 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by
    rw [map_one]; exact evI_realAd_one)
  have ha : GlobalTheory.Doubling.cutIdele ∅ l = unitArch F E l := by
    refine GlobalTheory.Doubling.idele_ext (fun w => ?_) fun v => ?_
    · rw [GlobalTheory.Doubling.unitInf_cutIdele]
      refine Units.ext ?_
      change compInf F E w l = compInf F E w (eInf F • (l : AE F E) + (1 - eInf F) • 1)
      have h : evInf F w (eInf F) = 1 := congrFun h1 w
      rw [map_add, compInf_smul, compInf_smul, map_sub, map_one, h, sub_self, zero_smul, one_smul, add_zero]
    · rw [GlobalTheory.Doubling.unitFin_cutIdele_of_notMem _ (Finset.notMem_empty v)]
      have := at_evI_iff.1 (unitArch_mem l) v
      rw [map_sub, map_one, sub_eq_zero] at this
      exact Units.ext this.symm
  rw [← ha, GlobalTheory.Doubling.cutIdele, GlobalTheory.Doubling.cutIdele, Finset.prod_empty, mul_one]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← ideleAt_unitFin (unitAt_mem v l)]
  exact congrArg _ (Units.ext (compFin_unitAt_self v l).symm)

theorem chr_abs_eq_finprod : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ν : Chr F E), Continuous ν → ∀ (l : (AE F E)ˣ) (z : ℕ),
    (Function.mulSupport fun v : Pl F => (ν (unitAt E v l) : ℂ) * ((absE F E (unitAt E v l) : ℝ) : ℂ) ^ z).Finite ∧
    (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z = (ν (unitArch F E l) : ℂ) * ((absE F E (unitArch F E l) : ℝ) : ℂ) ^ z *
      ∏ᶠ v : Pl F, (ν (unitAt E v l) : ℂ) * ((absE F E (unitAt E v l) : ℝ) : ℂ) ^ z := by
  intro F E _ _ _ _ _ ν hν l z
  have hu := eventually_unitAt_mem_unitsAt F E l
  have hfin : (Function.mulSupport fun v : Pl F =>
      (ν (unitAt E v l) : ℂ) * ((absE F E (unitAt E v l) : ℝ) : ℂ) ^ z).Finite := by
    refine (eventually_cofinite.1 (hu.and (eventually_chr_eq_one hν _ hu))).subset fun v hv h => hv ?_
    simp only [h.2, absE_of_mem_unitsAt h.1]
    simp
  refine ⟨hfin, ?_⟩
  let χ : (AE F E)ˣ →* ℂ :=
    { toFun := fun x => (ν x : ℂ) * ((absE F E x : ℝ) : ℂ) ^ z
      map_one' := by simp
      map_mul' := fun x y => by simp only [map_mul, Circle.coe_mul, NNReal.coe_mul, Complex.ofReal_mul]; ring }
  have hχ : Continuous χ := (continuous_subtype_val.comp hν).mul
    ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE)).pow z)
  refine tendsto_nhds_unique ((hχ.tendsto l).comp (GlobalTheory.Doubling.tendsto_cutIdele l)) (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop hfin.toFinset] with S hS
  rw [finprod_eq_prod_of_mulSupport_toFinset_subset _ hfin hS, Function.comp_apply, cutIdele_eq, map_mul, map_prod]
  rfl

end GlobalTheory.ThK.ConeEulerChr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPointMemTensorLatticeIffIntegralCoordsStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.InertCoord
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPoint_mem_tensorLattice_iff_integral_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (A : GL (Fin n) (w.adicCompletion E)) (Bm : GL (Fin d) (w.adicCompletion E)),
    IsFrameAt w X.L A → IsFrameAt w Y.L Bm → ∀ x,
      (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion E)) ↔
        kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x ∈ latAtV X Y v := by
  first | exact @GlobalTheory.InertLat.kap_mem_latAtV_iff | exact GlobalTheory.InertLat.kap_mem_latAtV_iff | (intros; apply GlobalTheory.InertLat.kap_mem_latAtV_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteCountOfDepthStatement
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_count_of_depth : GlobalTheory.FunPr.Hypotheses₂ → DepthK → InfCountK := by
  first | exact @GlobalTheory.SumCount.infCountK | exact GlobalTheory.SumCount.infCountK | (intros; apply GlobalTheory.SumCount.infCountK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableThetaKernelWeilRangeStatement
section
open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_thetaKernel_weilRange : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (A B : HSp D) (m : Measure (GA D B)), m.IsHaarMeasure → 1 ≤ A.rank → (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ ω → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ g, Integrable (descend (GQ B) fun h => thetaKO ω g h f) (autMeasure B m) := by
  first | exact @GlobalTheory.WeilThetaInt.integrable_thetaKO | exact GlobalTheory.WeilThetaInt.integrable_thetaKO | (intros; apply GlobalTheory.WeilThetaInt.integrable_thetaKO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGLConjPlaceOfSelfDualBaseFrameStatement
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralGL_conjPlace_of_selfDual_baseFrame : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Lev.IsBaseFrame V β Λ 1 → ∀ x ∈ UA D.sp.cm V.gram, ∀ w : Pl D.host.E, inBasis rfl β w x ∈ KO (Kw w) (Fin V.rank) → inBasis rfl β (Formalism.DivisionValues.conjPl w) x ∈ KO (Kw (Formalism.DivisionValues.conjPl w)) (Fin V.rank) := by
  first | exact @GlobalTheory.ConjPlaceLev.inBasis_conjPl_mem_KO_of_isBaseFrame | exact GlobalTheory.ConjPlaceLev.inBasis_conjPl_mem_KO_of_isBaseFrame | (intros; apply GlobalTheory.ConjPlaceLev.inBasis_conjPl_mem_KO_of_isBaseFrame <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveFrameMatrixTransportIffStatement
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrimitiveFrame_matrixTransport_iff : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {A D A₂ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype A₂] [DecidableEq A₂] [Fintype D₂] [DecidableEq D₂], IsLocIso j → ∀ (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}, LatCorr j cD Λ Λ₂ → ∀ (Z : Matrix A D k), IsPrimFrame Λ₂ (trM j rA cD Z) ↔ IsPrimFrame Λ Z := by
  first | exact @GlobalTheory.PureMatch.Transport.isPrimFrame_trM_iff | exact GlobalTheory.PureMatch.Transport.isPrimFrame_trM_iff | (intros; apply GlobalTheory.PureMatch.Transport.isPrimFrame_trM_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTameWDOfWdRel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LocLanglands GlobalTheory.WeilDeligne GlobalTheory.LocGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TameTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {A : ValuationSubring Ω} {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω']
  {A' : ValuationSubring Ω'} {φ : Ω ≃+* Ω'}

theorem val_lt_val_iff (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) (a b : Ω) (hb : b ≠ 0) :
    A'.valuation (φ a) < A'.valuation (φ b) ↔ A.valuation a < A.valuation b := by
  have hb' : φ b ≠ 0 := (map_ne_zero φ).mpr hb
  have h1 : A'.valuation (φ b) ≠ 0 := by simpa using hb'
  have h2 : A.valuation b ≠ 0 := by simpa using hb
  have e1 : A'.valuation (φ a) < A'.valuation (φ b) ↔ A'.valuation (φ (a / b)) < 1 := by
    rw [map_div₀, map_div₀, div_lt_one₀ (zero_lt_iff.mpr h1)]
  have e2 : A.valuation a < A.valuation b ↔ A.valuation (a / b) < 1 := by
    rw [map_div₀, div_lt_one₀ (zero_lt_iff.mpr h2)]
  rw [e1, e2, GlobalTheory.WeilTransport.val_lt_one_iff hm]

theorem isWild_of_rel (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) {σ : G E Ω} {σ' : G E' Ω'}
    (hrel : ∀ z, φ (σ z) = σ' (φ z)) (hσ : Formalism.MainNotions.BlochKatoReduction.IsWild A σ) : Formalism.MainNotions.BlochKatoReduction.IsWild A' σ' := by
  obtain ⟨⟨hdec, hin⟩, hw⟩ := hσ
  refine ⟨⟨(GlobalTheory.WeilTransport.mem_Dec_iff hm hrel).mpr hdec, fun x hx => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨z, rfl⟩ := φ.surjective x
    rw [GlobalTheory.WeilTransport.val_le_one_iff hm] at hx
    rw [← hrel, ← map_sub, GlobalTheory.WeilTransport.val_lt_one_iff hm]
    exact hin z hx
  · obtain ⟨z, rfl⟩ := φ.surjective x
    have hz : z ≠ 0 := by rintro rfl; exact hx (map_zero φ)
    rw [← hrel, ← map_sub, val_lt_val_iff hm _ _ hz]
    exact hw z hz

end GlobalTheory.TameTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOnWeilDatumTransportAdelicSchwartzStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnitaryOn_weilDatum_transport_adelicSchwartz : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsUnitaryOn (adeleClass F) om := by
  first | exact @GlobalTheory.WeilUnitaryTransportF.isUnitaryOn_transportF | exact GlobalTheory.WeilUnitaryTransportF.isUnitaryOn_transportF | (intros; apply GlobalTheory.WeilUnitaryTransportF.isUnitaryOn_transportF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewiseStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    (∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T Φ ∈ GlobalTheory.WeilM.schA F κ) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∫⁻ y, ‖T Φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖Φ y‖ₑ ^ 2 ∂μ) →
    (∀ u : AF F, evFin F v u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
      T (GlobalTheory.WeilM.schr ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : κ → AF F, (∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → Φ (y + z) = 0) → T Φ y = 0 := by
  first | exact @GlobalTheory.FibreLocality.eq_zero_of_vanish_fibre | exact GlobalTheory.FibreLocality.eq_zero_of_vanish_fibre | (intros; apply GlobalTheory.FibreLocality.eq_zero_of_vanish_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelColumnsFromTiesStatement
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_columns_from_ties : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) [IsTotallyComplex D.what₂.LL] (T : Formalism.L2.TiedDataSK ex) (P : RowSideFamily ex) (K : SquareIntegrableColumnsCompatible T P) (W : Formalism.L2.Col.Wts T.ker.X T.ker.Pr.Word D.R) (Del h0 : ℕ), ColPins K → HEq K.c.W W → KerTies T.ker W Del h0 → KerSizes T.ker W Del h0 CY CT → DV.NprimeDef D L → D.NuFull → (∀ u, 0 < (D.div.Nu u).rank) → ∀ (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (cf : ConvFace P.A3.fam3.base3) (Cl CHl : ℝ) (Pk : IndefPkgR P.A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 P.A3 P.P0 P.ψ0 P.Ps P.ψs K.c.face K.Sp Zsc) cf Cl CHl), Pk.Zs = P.Zs → ∀ (u : D.what₂.Word) (lam0 c0 ce Ch Sw C1 : ℝ) (H : (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 c0 ce Ch Sw C1) (w : (K.c.face Pk.Zs).Mem) (e : (Fin ((K.c.face Pk.Zs).a w) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V), HEq w u → C0 ≤ Ch → ∃ (ch : ColChain (K.c.face Pk.Zs) w) (Tc : ChainTie ch (K.c.memQ w)), FirstCols K.c.hE Tc ∧ ∃ (X0 : InfinitePlace D.what₂.LL → Matrix (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) ℂ) (_ : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = ((P.A3.side3 P.Ps P.ψs Pk.Zs).HV P.A3.fam3.base3.μ0).map v.embedding) (hn : HtNums (RecNums.ofNum (ofRecord D L Del h0) (Equiv.refl _) (letterOf D L Del h0 u) (D.mem u).A.T L.Nc lam0 c0 ce Ch Sw C1 H) (InfinitePlace D.what₂.LL)) (_ : ∀ v, Formalism.HN.opNormAt (Pi.basisFun D.what₂.LL (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm)) (Pi.basisFun D.what₂.LL (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hn.hPn) (cb : CBData ch.X ch.Kj), (∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v) ∧ (∀ v, IsUnit ((K.c.face Pk.Zs).Xc w v).det) ∧ 0 < (K.c.face Pk.Zs).a w ∧ Submodule.IsLattice D.what₂.LL (Cons.nuOf L u e) := by
  first | exact @GlobalTheory.ColRows.rowsU_of_colPins | exact GlobalTheory.ColRows.rowsU_of_colPins | (intros; apply GlobalTheory.ColRows.rowsU_of_colPins <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemiLocalMirabolicAbstractStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kirillov_semiLocal_mirabolic_abstract : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart b g) (invSet E (m + 1))) → ∀ 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ), (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, (fun g => W (g * h)) ∈ 𝒲) → (∀ W ∈ 𝒲, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.JSW.kerInf ν k γ W ∈ 𝒲) → (∀ W ∈ 𝒲, ∀ g, Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (g * infGL E (m + 1) y)) ∧ ∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (g * infGL E (m + 1) y)‖ ≤ C * height y ^ N) → (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∃ W ∈ 𝒲, ∃ p ∈ GlobalTheory.JSW.mirS E S m, W p ≠ 0) → ∃ W ∈ 𝒲, ∀ p ∈ GlobalTheory.JSW.mirS E S m, W p = b p := by
  first | (exact @GlobalTheory.JSW.MirSemi.kirillov_semiLocal) | (exact GlobalTheory.JSW.MirSemi.kirillov_semiLocal) | (intros; apply GlobalTheory.JSW.MirSemi.kirillov_semiLocal  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LargePlaceRatioRamifiedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.large_place_ratio_ramified : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∈ S1 D → ∀ i j : Fin D.R.m, ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) / G.ch.chi (D.R.m - i)) := by
  first | exact @GlobalTheory.RamifiedOnLargePlaces.not_unramAt | exact GlobalTheory.RamifiedOnLargePlaces.not_unramAt | (intros; apply GlobalTheory.RamifiedOnLargePlaces.not_unramAt <;> assumption)
end

