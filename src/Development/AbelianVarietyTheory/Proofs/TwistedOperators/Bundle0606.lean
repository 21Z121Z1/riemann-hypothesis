import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0520
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactPairRealAverageFockEqJetOperator
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0578
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchSupportedSmulConjugateUnitarySubOneEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ConjFinArch

variable {D : D7}

def eInf (F : Type) [Field F] [NumberField F] : AF F :=
  ((1 : Ainf F), (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F))

theorem one_sub_eInf_fst (F : Type) [Field F] [NumberField F] : (1 - eInf F).1 = 0 := by
  show (1 : Ainf F) - 1 = 0
  exact sub_self _

theorem evI_sub_eInf (F : Type) [Field F] [NumberField F] : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (1 - eInf F) = 0 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI, one_sub_eInf_fst, map_zero]

theorem eInf_smul_tmul (a : AF D.host.F) (y : D.host.E) :
    eInf D.host.F • (a ⊗ₜ[D.host.F] y) = (eInf D.host.F * a) ⊗ₜ[D.host.F] y := by
  rfl

def incInf (F : Type) [Field F] [NumberField F] : Ainf F →ₗ[F] AF F where
  toFun x := ((x, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : AF F)
  map_add' x y := by
    show ((x + y, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = (x + y, 0 + 0)
    rw [add_zero]
  map_smul' c x := by
    show ((c • x, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = (c • x, c • (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F))
    rw [smul_zero]

theorem eInf_mul' (a : AF D.host.F) : eInf D.host.F * a = incInf D.host.F (fstA D.host.F a) := by
  show ((1 : Ainf D.host.F) * a.1, (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * a.2) = (a.1, 0)
  rw [one_mul, zero_mul]

theorem cA_tmul (a : AF D.host.F) (y : D.host.E) :
    cA D (a ⊗ₜ[D.host.F] y) = a ⊗ₜ[D.host.F] D.sp.cm.sig y := by
  show Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig (a ⊗ₜ[D.host.F] y) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem smul_tmul_AF (r a : AF D.host.F) (y : D.host.E) :
    r • (a ⊗ₜ[D.host.F] y) = (r * a) ⊗ₜ[D.host.F] y := rfl

theorem cA_smul (r : AF D.host.F) (x : AF D.host.F ⊗[D.host.F] D.host.E) : cA D (r • x) = r • cA D x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul a y => rw [smul_tmul_AF, cA_tmul, cA_tmul, smul_tmul_AF]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem eInf_smul (x : AF D.host.F ⊗[D.host.F] D.host.E) :
    eInf D.host.F • x = TensorProduct.map (incInf D.host.F) LinearMap.id
      (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) x) := by
  have key : DistribMulAction.toLinearMap D.host.F (AF D.host.F ⊗[D.host.F] D.host.E) (eInf D.host.F) =
      (TensorProduct.map (incInf D.host.F) (LinearMap.id : D.host.E →ₗ[D.host.F] D.host.E)).comp
        (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toLinearMap := by
    refine TensorProduct.ext' fun a y => ?_
    show eInf D.host.F • (a ⊗ₜ[D.host.F] y) = TensorProduct.map (incInf D.host.F) LinearMap.id
      (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (a ⊗ₜ[D.host.F] y))
    rw [eInf_smul_tmul, eInf_mul', Algebra.TensorProduct.map_tmul]
    rfl
  exact LinearMap.congr_fun key x

theorem eInf_smul_eq_zero {x : AF D.host.F ⊗[D.host.F] D.host.E}
    (hx : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) x = 0) : eInf D.host.F • x = 0 := by
  rw [eInf_smul, hx, map_zero]

theorem one_apply_map {R S : Type} [Semiring R] [Semiring S] {n : ℕ} (f : R →+* S) (i j : Fin n) :
    f ((1 : Matrix (Fin n) (Fin n) R) i j) = (1 : Matrix (Fin n) (Fin n) S) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem eInf_smul_conjU_sub_one (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (hJ : J = c • V.gram) {g : GA D V} (hg : g ∈ GfC V) (i j : Fin V.rank) :
    eInf D.host.F • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) i j = 0 := by
  have hm : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) i j = cA D (mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [map_sub, Matrix.sub_apply, one_apply_map]
    rfl
  have hinf : infHom V g = 1 := hg
  have he : Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (mt V g i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := by
    have := congrArg (fun h : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => h.1 i j) hinf
    exact this
  rw [hm, ← cA_smul, eInf_smul_eq_zero, map_zero]
  rw [map_sub, he]
  exact sub_eq_zero.2 (one_apply_map (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom i j).symm

end GlobalTheory.ConjFinArch

theorem GlobalTheory.ConjFinArch.smul_mat_conjU_sub_one : ∀ (D : D7) (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E) (hJ : J = c • V.gram)
    (g : GA D V), g ∈ GfC V → ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
      u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) = 0 := by
  intro D V J c hJ g hg u hu
  have h1 : (1 - GlobalTheory.ConjFinArch.eInf D.host.F) * u = 0 := hu _ (GlobalTheory.ConjFinArch.evI_sub_eInf _)
  have h2 : u = u * GlobalTheory.ConjFinArch.eInf D.host.F := by
    rw [sub_mul, one_mul, sub_eq_zero] at h1
    rw [mul_comm]; exact h1
  rw [h2, mul_smul]
  have h3 : GlobalTheory.ConjFinArch.eInf D.host.F • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hJ g) - 1) = 0 := by
    ext i j
    rw [Matrix.smul_apply, GlobalTheory.ConjFinArch.eInf_smul_conjU_sub_one V c hJ hg i j, Matrix.zero_apply]
  rw [h3, smul_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanOneParameterFamilyContinuous
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical
noncomputable section

namespace GlobalTheory.ArchFamilyCont

theorem continuous_family : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ t (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    (∀ (f : SInf F (Fin n × Fin d)) y, Continuous fun t => T t f y) ∧
    ∀ (μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure → ∀ f φ : SInf F (Fin n × Fin d),
      Continuous fun t => ∫ x, T t f x * starRingEnd ℂ (φ x) ∂μ := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hW γ hγ T hT
  classical
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
  have hc : IsContOn (adeleClass F) om := hW.2.2
  have hline : Continuous fun t : ℝ => ((1 : UA σ X.J), γ (Multiplicative.ofAdd t)) :=
    continuous_const.prodMk (hγ.1.comp continuous_ofAdd)
  have key : ∀ t (f : SInf F (Fin n × Fin d)),
      om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R) = tens (evI F) ⇑(T t f) R :=
    fun t f => hT t f R (hR f)
  have hRl : ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F, R (liftV y) = R 0 := by
    intro y
    have hat : At (evI F) (liftV y) := by
      intro u hu
      have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
      funext i
      show u * liftV y i = 0
      exact Prod.ext (show u.1 * _ = 0 by rw [hu1, zero_mul]) (show u.2 * 0 = 0 from mul_zero _)
    have := (hR 0).1 0 (liftV y) hat
    simpa using this
  have hev : ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F, (fun i => evI F (liftV y i)) = y := by
    intro y; funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) = y i
    exact RingEquiv.apply_symm_apply _ _
  have hfin : ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F, (fun i => (liftV y i).2) = 0 := by
    intro y; funext i; rfl
  have htl : ∀ (f : SInf F (Fin n × Fin d)) y, tens (evI F) ⇑f R (liftV y) = f y * R 0 := by
    intro f y
    show f (fun i => evI F (liftV y i)) * R (liftV y) = _
    rw [hev, hRl]
  refine ⟨fun f y => ?_, fun μ hμ f φ => ?_⟩
  ·
    let l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) (liftV y)
    have hl : l ∈ (adeleClass F).adm (Fin n × Fin d) := by
      intro g _
      refine ⟨g 0 • ((BoundedContinuousFunction.evalCLM ℂ y).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f' => ?_⟩
      show pureA F (⇑f') g (liftV y) = _
      simp only [pureA, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        BoundedContinuousFunction.evalCLM_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply, smul_eq_mul]
      have e1 := hev y
      have e2 := hfin y
      simp only [evI] at e1
      rw [e1, e2, mul_comm]
    have h1 := hc l hl _ (hR f).2
    have h2 : Continuous fun t : ℝ => l (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R)) := h1.comp hline
    have h3 : (fun t : ℝ => T t f y) = fun t => l (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R)) / R 0 := by
      funext t
      rw [key]
      show _ = tens (evI F) ⇑(T t f) R (liftV y) / R 0
      rw [htl, mul_div_cancel_right₀ _ hR0]
    rw [h3]
    exact h2.div_const _
  ·
    haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := inferInstance
    haveI : μ.HasTemperateGrowth := MeasureTheory.Measure.IsAddHaarMeasure.instHasTemperateGrowth
    let Tφ : SInf F (Fin n × Fin d) →L[ℂ] ℂ :=
      (innerSL ℂ (φ.toLp 2 μ)).comp (SchwartzMap.toLpCLM ℂ ℂ 2 μ)
    have hTφ : ∀ g : SInf F (Fin n × Fin d), Tφ g = ∫ x, g x * starRingEnd ℂ (φ x) ∂μ := by
      intro g
      show inner ℂ (φ.toLp 2 μ) (g.toLp 2 μ) = _
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [SchwartzMap.coeFn_toLp φ 2 μ, SchwartzMap.coeFn_toLp g 2 μ] with x hx1 hx2
      rw [hx1, hx2, RCLike.inner_apply, mul_comm]
    let cL : SInf F (Fin n × Fin d) →ₗ[ℂ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) :=
      { toFun := fun g => ⇑g, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective cL := fun a b h => DFunLike.coe_injective h
    let eq := LinearEquiv.ofInjective cL hinj
    obtain ⟨L, hL⟩ := LinearMap.exists_extend (Tφ.toLinearMap ∘ₗ eq.symm.toLinearMap)
    have hLc : ∀ g : SInf F (Fin n × Fin d), L ⇑g = Tφ g := by
      intro g
      have := LinearMap.congr_fun hL (eq g)
      simp at this
      exact this
    let l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ := L ∘ₗ LinearMap.funLeft ℂ ℂ liftV
    have hl : l ∈ (adeleClass F).adm (Fin n × Fin d) := by
      intro g _
      refine ⟨g 0 • Tφ, fun f' => ?_⟩
      have e : (LinearMap.funLeft ℂ ℂ liftV (pureA F (⇑f') g) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ)
          = ⇑(g 0 • f') := by
        funext x
        have e1 := hev x
        have e2 := hfin x
        simp only [evI] at e1
        simp only [LinearMap.funLeft_apply, Function.comp_apply, pureA, SchwartzMap.smul_apply, smul_eq_mul]
        rw [e1, e2, mul_comm]
      show L (LinearMap.funLeft ℂ ℂ liftV (pureA F (⇑f') g)) = _
      rw [e, hLc, map_smul]
      rfl
    have h1 := hc l hl _ (hR f).2
    have h2 : Continuous fun t : ℝ => l (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R)) := h1.comp hline
    have h3 : (fun t : ℝ => ∫ x, T t f x * starRingEnd ℂ (φ x) ∂μ) =
        fun t => l (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f R)) / R 0 := by
      funext t
      rw [key]
      have e : (LinearMap.funLeft ℂ ℂ liftV (tens (evI F) ⇑(T t f) R) :
          (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) = ⇑(R 0 • T t f) := by
        funext x
        simp only [LinearMap.funLeft_apply, Function.comp_apply, SchwartzMap.smul_apply, smul_eq_mul]
        rw [htl, mul_comm]
      show _ = L (LinearMap.funLeft ℂ ℂ liftV (tens (evI F) ⇑(T t f) R)) / R 0
      rw [e, hLc, map_smul, smul_eq_mul, hTφ, mul_div_cancel_left₀ _ hR0]
    rw [h3]
    exact h2.div_const _

end GlobalTheory.ArchFamilyCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanPointPureTensorKeepsFiniteFactorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanPoint_pureTensor_keeps_finiteFactor : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Wd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F), ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    ∃ c : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      om (1, g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure c φ := by
  first | exact @GlobalTheory.ArchPure.pure_arch | exact GlobalTheory.ArchPure.pure_arch | (intros; apply GlobalTheory.ArchPure.pure_arch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseExOf
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowEx

theorem baseEx_of (hP : GlobalTheory.FunPr.Hypotheses₂) (hC : ConstEx) : BaseEx := by
  obtain ⟨CF0, hC⟩ := hC
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hC ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS => ?_⟩
  have hQ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS
  intro G W hW S₀
  obtain ⟨rm, c, hrm, hc⟩ := hQ G W hW S₀.B
  have hL := hS.core.lev
  obtain ⟨M, hM⟩ := exists_vol G hL A.μ0
  obtain ⟨n, e, -, -, -, -⟩ := TestLatModel.exists_testLat (G := G)
    (node_isV G hL (X := .grid 0 0) ⟨Nat.zero_le _, Nat.zero_le _⟩).sd.1.fg default
  obtain ⟨Pm, -, -⟩ := hS.size.1
  have hCh : ∀ k, GlobalTheory.Chain.ChainPar D k := GlobalTheory.Corev.ChainParOfGap.chainPar_of_nodeGap D
    (GlobalTheory.Core.Rk.GapOfNodes.harishChandraNodesFarApart_of_cubic_node_gap D (by simpa using Pm.nodeGap_ge_cubic_rank))
  obtain ⟨cv, hcv⟩ := GlobalTheory.RowTest.WVec.exists_w_ne hP.discreteSeriesCover hP.harishChandraModules hCh R hL
    hS.core.chain hS.core.models.inf
  obtain ⟨S'⟩ := sumChoice_nonempty W S₀ hS.core.fam.tie (GlobalTheory.ForcedWeights.lamRForced D)
  exact ⟨M, fun _ => 0, 0, cv, rm, { S' with toGridChoice := S₀ }, default, n, e, c, rfl,
    ⟨guard_of_qGuard hS.guard, hW, hM.isRow, hrm, hcv, hc⟩⟩

end GlobalTheory.RowEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiGridHighestWeightEqCompactChainParameter
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.ChiGrid GlobalTheory.RowReal
open Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.RowReal.WeightsX

open GlobalTheory.SignedHC

theorem mem_listBlock_iff {c x : ℚ} {n : ℕ} : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block c n ↔ x ∈ TPar.block c n := by
  rw [GlobalTheory.SignedHC.mem_block]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block, List.mem_map, List.mem_range]
  exact ⟨fun ⟨a, h, e⟩ => ⟨a, h, e.symm⟩, fun ⟨a, h, e⟩ => ⟨a, h, e.symm⟩⟩

theorem pairwise_listBlock (c : ℚ) (n : ℕ) : (GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block c n).Pairwise (· > ·) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block
  rw [List.pairwise_map]
  refine (List.pairwise_lt_range (n := n)).imp fun {a b} h => ?_
  have : (a : ℚ) < b := by exact_mod_cast h
  linarith

theorem psiPar_eq (D : D7) (C : ℝ) (τ : D.what₂.Tau) : (rowEntries D C τ).psiPar =
    (num D C τ).a 0 :: ((List.finRange D.R.m).flatMap (fun i : Fin D.R.m =>
      GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (((num D C τ).cen ((i : ℕ) + 1) : ℤ) : ℚ) (sLen D - 1) ++ [(num D C τ).a ((i : ℕ) + 1)]) ++
      (List.finRange (D.R.k - 1)).map fun i : Fin (D.R.k - 1) => (num D C τ).vHalf ((i : ℕ) + 2)) := rfl

theorem psiPar_props (D : D7) (C : ℝ) (τ : D.what₂.Tau) :
    (rowEntries D C τ).psiPar.Pairwise (· > ·) ∧ ∀ x ∈ (rowEntries D C τ).psiPar, x ∈ (num D C τ).weightX 0 := by
  have hm : (num D C τ).NearMid := num_nearMid D C τ
  have hs : 1 ≤ (num D C τ).s := (odd_sLen D).pos
  have hg : (num D C τ).s < (num D C τ).ga := sLen_lt_gap D C
  have hGm : (num D C τ).m = D.R.m := rfl
  have hGk : (num D C τ).k = D.R.k := rfl
  have hga : (0 : ℚ) < (num D C τ).ga := by exact_mod_cast (by omega : 0 < (num D C τ).ga)
  have hle : ∀ {i j : ℕ}, i ≤ j → (num D C τ).a j ≤ (num D C τ).a i := fun h => by
    rcases h.eq_or_lt with rfl | h
    · exact le_rfl
    · linarith [a_add_le (G := num D C τ) h]
  have hB : ∀ (i : Fin D.R.m) x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (((num D C τ).cen ((i : ℕ) + 1) : ℤ) : ℚ) (sLen D - 1) →
      (num D C τ).a ((i : ℕ) + 1) < x ∧ x < (num D C τ).a ((i : ℕ) + 1) + (num D C τ).ga := fun i x hx =>
    blockC'_between hm hs hg (by omega) (by have := i.2; omega) (mem_listBlock_iff.1 hx)
  have piece : ∀ (i : Fin D.R.m) y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (((num D C τ).cen ((i : ℕ) + 1) : ℤ) : ℚ) (sLen D - 1) ++
      [(num D C τ).a ((i : ℕ) + 1)] → (num D C τ).a ((i : ℕ) + 1) ≤ y ∧ y < (num D C τ).a i := by
    intro i y hy
    rw [(num D C τ).a_eq_succ_add i]
    rcases List.mem_append.1 hy with h | h
    · have := hB i y h; exact ⟨this.1.le, this.2⟩
    · rw [List.mem_singleton] at h; subst h
      exact ⟨le_rfl, by linarith⟩
  have hU : ∀ y ∈ (List.finRange (D.R.k - 1)).map (fun i : Fin (D.R.k - 1) => (num D C τ).vHalf ((i : ℕ) + 2)),
      y ∈ (num D C τ).cloudHalf := by
    intro y hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact GridData.mem_cloudHalf.2 ⟨(i : ℕ) + 2, by omega, by have := i.2; omega, rfl⟩
  rw [psiPar_eq]
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_cons, List.pairwise_append, List.pairwise_flatMap, List.pairwise_map]
    refine ⟨?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
    · intro y hy
      rcases List.mem_append.1 hy with h | h
      · obtain ⟨i, -, h⟩ := List.mem_flatMap.1 h
        have := piece i y h
        linarith [hle (Nat.zero_le (i : ℕ))]
      · have := cloudHalf_lt (hU y h)
        linarith [hle (Nat.zero_le (num D C τ).m)]
    · intro i _
      rw [List.pairwise_append]
      refine ⟨pairwise_listBlock _ _, List.pairwise_singleton _ _, ?_⟩
      intro x hx y hy
      rw [List.mem_singleton] at hy; subst hy
      exact (hB i x hx).1
    · refine (List.pairwise_lt_finRange D.R.m).imp fun {i j} hij => ?_
      intro x hx y hy
      have h1 := piece i x hx
      have h2 := piece j y hy
      have h3 : (i : ℕ) + 1 ≤ j := hij
      linarith [hle h3]
    · refine (List.pairwise_lt_finRange (D.R.k - 1)).imp fun {i j} hij => ?_
      have hij' : (i : ℕ) < j := hij
      have := (num D C τ).v_anti ((i : ℕ) + 2) ((j : ℕ) + 2) (by omega) (by omega) (by have := j.2; omega)
      have h' : ((num D C τ).v ((j : ℕ) + 2) : ℚ) < (num D C τ).v ((i : ℕ) + 2) := by exact_mod_cast this
      simp only [GridData.vHalf]; linarith
    · intro x hx y hy
      obtain ⟨i, -, h⟩ := List.mem_flatMap.1 hx
      have h1 := piece i x h
      have h2 := cloudHalf_lt (hU y hy)
      have h3 : (i : ℕ) + 1 ≤ (num D C τ).m := by have := i.2; omega
      linarith [hle h3]
  · intro y hy
    rw [GridData.mem_weightX]
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Or.inl (GridData.mem_tops.2 ⟨0, by omega, rfl⟩)
    rcases List.mem_append.1 hy with h | h
    · obtain ⟨i, -, h⟩ := List.mem_flatMap.1 h
      rcases List.mem_append.1 h with h | h
      · exact Or.inr (Or.inr (Or.inl ⟨(i : ℕ) + 1, by omega, by have := i.2; omega, mem_listBlock_iff.1 h⟩))
      · rw [List.mem_singleton] at h; subst h
        exact Or.inl (GridData.mem_tops.2 ⟨(i : ℕ) + 1, by have := i.2; omega, rfl⟩)
    · exact Or.inr (Or.inl (hU y h))

theorem length_psiPar (D : D7) (C : ℝ) (τ : D.what₂.Tau) : (rowEntries D C τ).psiPar.length = rankP D D.R.m := by
  rw [length_psi, rowSizes_nR]; simp [rankX]

end GlobalTheory.RowReal.WeightsX

namespace GlobalTheory.RowReal

open GlobalTheory.SignedHC GlobalTheory.RowReal.WeightsX

end GlobalTheory.RowReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactPairRealAverageFockEqJetOperatorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open GlobalTheory.FockReal MvPolynomial
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactPair_realAverage_fock_eq_jetOperator : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T},
    L.Is μ0 → ∀ (i : ℕ), i < D.R.m →
    ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D (G.chrS (.chi i D.R.m : Pair T)) τ (a τ)) → (∀ τ, HasInfExp D (G.chrT (.chi i D.R.m : Pair T)) τ (b τ)) →
    ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ + sgnP (.chi i D.R.m : Pair T) * (G.pS (.chi i D.R.m : Pair T)).rank / 2) →
      (∀ τ, (e₂ τ : ℚ) = -(b τ + sgnP (.chi i D.R.m : Pair T) * (G.pT (.chi i D.R.m : Pair T)).rank / 2)) →
    ∀ (Q : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank) (Λ : Module.Dual ℂ (VV ℂ (wt G (.grid i D.R.m)))),
    ∃ Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid (i + 1) D.R.m))),
      ∀ (ℓ : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →ₗ[ℂ] ℂ) (κ : Measure (GinfC (G.V (.grid i D.R.m)))), κ.IsHaarMeasure → IsProbabilityMeasure κ →
        ∀ (k' : GA D (G.V (.grid (i + 1) D.R.m))), k' ∈ GinfC (G.V (.grid (i + 1) D.R.m)) →
        ∀ v : VV ℂ (wt G (.grid i D.R.m)),
          ∫ k, realChar W (.chi i D.R.m) e₁ e₂ (k : GA D (G.V (.grid i D.R.m))) k' *
              ℓ (realSubst W S.N.frC (.chi i D.R.m) (k : GA D (G.V (.grid i D.R.m))) k' Q) *
              Λ (realAct W.θ S.N.fr (.grid i D.R.m) ((k : GA D (G.V (.grid i D.R.m)))⁻¹) v) ∂κ =
            Λ' (realAct W.θ S.N.fr (.grid (i + 1) D.R.m) k'⁻¹
              (Formalism.L2.Ker.jetOp (wt G (.grid i D.R.m)) (wt G (.grid (i + 1) D.R.m))
                (fun m => ℓ (MvPolynomial.monomial (m.mapDomain (fvar G (.chi i D.R.m : Pair T))) 1)) (nuEnd G (.chi i D.R.m : Pair T)) v)) := by
  first | exact @GlobalTheory.RowHoweAvg.real_average_jet | exact GlobalTheory.RowHoweAvg.real_average_jet | (intros; apply GlobalTheory.RowHoweAvg.real_average_jet <;> assumption)
end

