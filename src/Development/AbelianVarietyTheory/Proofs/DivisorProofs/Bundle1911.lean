import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1785
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1746
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1886
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1762
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeOIffScaleMulFinitePartMemIdealLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1829
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.Bundle0004
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0559
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1864

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqComponentTensorEqConstMulStatement
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
theorem _root_.GlobalTheory.T.lintegral_normSq_componentTensor_eq_const_mul : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (r : (κ → AF F) → ℂ),
    @Measurable _ _ (borel _) _ r →
    (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → r (x + z) = r x) →
    ∀ μA : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μA →
    ∀ μ : @MeasureTheory.Measure (κ → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ K : Set (κ → Fv F v), IsCompact K → (interior K).Nonempty →
    ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ 0 →
    ∫⁻ x, K.indicator 1 (fun i => evFin F v (x i)) * ‖r x‖ₑ ^ 2 ∂μA ≠ ⊤ →
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ φ : (κ → Fv F v) → ℂ, Continuous φ → HasCompactSupport φ →
      ∫⁻ x, ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r x‖ₑ ^ 2 ∂μA = C * ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.AdelicPush.lintegral_tens_eq_const_mul | exact GlobalTheory.AdelicPush.lintegral_tens_eq_const_mul | (intros; apply GlobalTheory.AdelicPush.lintegral_tens_eq_const_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentRealisedOnAdelicSchwartz
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix

namespace GlobalTheory.AdelicSvNQuad

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic
open scoped Classical

def quad {R κ : Type} [CommRing R] [Fintype κ] (h : R) (A : Matrix κ κ R) (x : κ → R) : R := h * (x ⬝ᵥ (A *ᵥ x))

theorem map_quad {R S κ : Type} [CommRing R] [CommRing S] [Fintype κ] (q : R →+* S) (h : R) (A : Matrix κ κ R)
    (x : κ → R) : q (quad h A x) = quad (q h) (A.map q) (fun i => q (x i)) := by
  simp [quad, dotProduct, Matrix.mulVec, map_sum]

theorem quad_neg {R κ : Type} [CommRing R] [Fintype κ] (h : R) (A : Matrix κ κ R) (x : κ → R) :
    quad h (-A) x = -quad h A x := by
  simp [quad, Matrix.neg_mulVec]

theorem continuous_quad {R κ : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Fintype κ] (h : R)
    (A : Matrix κ κ R) : Continuous (quad h A) :=
  continuous_const.mul (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id))

theorem quad_add {R κ : Type} [CommRing R] [Invertible (2 : R)] [Fintype κ] (A : Matrix κ κ R) (hA : Aᵀ = A)
    (x u v : κ → R) : quad (⅟2) A x + (x ⬝ᵥ v + ⅟(2 : R) * (u ⬝ᵥ v)) =
      (x ⬝ᵥ (-(A *ᵥ u) + v) + ⅟(2 : R) * (u ⬝ᵥ (-(A *ᵥ u) + v))) + quad (⅟2) A (x + u) := by
  have hs : u ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ u) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self _
  simp only [quad, Matrix.mulVec_add, dotProduct_add, add_dotProduct, dotProduct_neg, hs]
  linear_combination (-(x ⬝ᵥ (A *ᵥ u))) * h2

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def archMul (h : mixedEmbedding.mixedSpace F) (A : Matrix κ κ (mixedEmbedding.mixedSpace F))
    (y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  eChar (-Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (quad h A y))

theorem archMul_temperate (h : mixedEmbedding.mixedSpace F) (A : Matrix κ κ (mixedEmbedding.mixedSpace F)) :
    Function.HasTemperateGrowth (archMul h A) := by
  have hp : ∀ i : κ, Function.HasTemperateGrowth fun y : κ → mixedEmbedding.mixedSpace F => y i := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => mixedEmbedding.mixedSpace F) i).hasTemperateGrowth
  have hq : Function.HasTemperateGrowth (quad h A) := by
    have e : quad h A = fun y => h * ∑ i, y i * ∑ j, A i j * y j := rfl
    rw [e]
    refine (Function.HasTemperateGrowth.const h).mul (Function.HasTemperateGrowth.sum fun i _ => (hp i).mul ?_)
    exact Function.HasTemperateGrowth.sum fun j _ => (Function.HasTemperateGrowth.const _).mul (hp j)
  let L : mixedEmbedding.mixedSpace F →L[ℝ] ℝ :=
    -LinearMap.toContinuousLinearMap (Algebra.trace ℝ (mixedEmbedding.mixedSpace F))
  exact hasTemperateGrowth_eChar.comp (L.hasTemperateGrowth.comp hq)

def mulQ (ψ : AddChar (AF F) ℂ) (h : AF F) (A : Matrix κ κ (AF F)) :
    ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun φ x := ψ (quad h A x) * φ x
  map_add' φ φ' := funext fun x => mul_add _ _ _
  map_smul' a φ := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem mulQ_apply (ψ : AddChar (AF F) ℂ) (h : AF F) (A : Matrix κ κ (AF F)) (φ : (κ → AF F) → ℂ) (x : κ → AF F) :
    mulQ ψ h A φ x = ψ (quad h A x) * φ x := rfl

theorem mulQ_pureA (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (h : AF F) (A : Matrix κ κ (AF F))
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ g' ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ M : SInf F κ →L[ℂ] SInf F κ,
      ∀ f : SInf F κ, mulQ ψ h A (pureA F f g) = pureA F (M f) g' := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F := e.toRingHom.comp p1
  refine ⟨fun z => finChar ψ (quad (p2 h) (A.map p2) z) * g z,
    ⟨((finChar_isLocallyConstant ψ hψ.1).comp_continuous (continuous_quad _ _)).mul hg.1, hg.2.mul_left⟩,
    SchwartzMap.smulLeftCLM ℂ (archMul (q h) (A.map q)), fun f => funext fun x => ?_⟩
  let y : κ → mixedEmbedding.mixedSpace F := fun i => q (x i)
  let z : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (x i)
  have h3 : ψ (quad h A x) = archMul (q h) (A.map q) y * finChar ψ (quad (p2 h) (A.map p2) z) := by
    rw [map_eq_mul ψ, hψ.2.2 _ (at_mk _)]
    congr 1
    · have e1 : evI F (mk (p1 (quad h A x)) 0) = quad (q h) (A.map q) y := map_quad q h A x
      rw [e1, archMul, eChar_apply]
      congr 1
      push_cast
      ring
    · exact congrArg _ (map_quad p2 h A x)
  change ψ (quad h A x) * (f y * g z) =
    SchwartzMap.smulLeftCLM ℂ (archMul (q h) (A.map q)) f y * (finChar ψ (quad (p2 h) (A.map p2) z) * g z)
  rw [h3, SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_eq_mul]
  ring

theorem mulQ_mem (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (h : AF F) (A : Matrix κ κ (AF F)) :
    ∀ φ ∈ schA F κ, mulQ ψ h A φ ∈ schA F κ := by
  have hle : schA F κ ≤ (schA F κ).comap (mulQ ψ h A) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, g, hg, rfl⟩
    obtain ⟨g', hg', M, hM⟩ := mulQ_pureA ψ hψ h A hg
    exact Submodule.subset_span ⟨M f, g', hg', hM f⟩
  exact fun φ hφ => hle hφ

theorem act_unip {K R ι : Type} [Field K] [CommRing R] [Algebra K R] [Fintype ι] [DecidableEq ι] (C : Matrix ι ι K)
    (w : (ι → R) × (ι → R)) :
    AdelicSvN.act (Matrix.fromBlocks 1 0 (-C) 1) w = (w.1, -(C.map (algebraMap K R) *ᵥ w.1) + w.2) := by
  have h1 : (1 : Matrix ι ι K).map (algebraMap K R) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h0 : (0 : Matrix ι ι K).map (algebraMap K R) = 0 := Matrix.map_zero _ (map_zero _)
  have hn : (-C).map (algebraMap K R) = -C.map (algebraMap K R) := Matrix.map_neg _ (map_neg _) _
  simp only [AdelicSvN.act, Matrix.fromBlocks_map, h1, h0, hn, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, Matrix.neg_mulVec]

theorem realised_unip : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ] (C : Matrix κ κ F), Cᵀ = C → Realised ψ (Matrix.fromBlocks 1 0 (-C) 1) := by
  intro F _ _ ψ hψ κ _ _ C hC
  let A : Matrix κ κ (AF F) := C.map (algebraMap F (AF F))
  have hA : Aᵀ = A := by rw [← Matrix.transpose_map, hC]
  refine ⟨mulQ ψ (⅟2) A, mulQ_mem ψ hψ _ A, fun φ hφ => ⟨mulQ ψ (⅟2) (-A) φ, mulQ_mem ψ hψ _ _ φ hφ, ?_⟩,
    fun l hl => ⟨l ∘ₗ mulQ ψ (⅟2) A, fun g hg => ?_, fun _ _ => rfl⟩, fun w φ _ => funext fun x => ?_⟩
  · funext x
    rw [mulQ_apply, mulQ_apply, ← mul_assoc, ← AddChar.map_add_eq_mul, quad_neg, add_neg_cancel,
      AddChar.map_zero_eq_one, one_mul]
  · obtain ⟨g', hg', M, hM⟩ := mulQ_pureA ψ hψ (⅟2) A hg
    obtain ⟨T, hT⟩ := hl g' hg'
    exact ⟨T.comp M, fun f => (congrArg l (hM f)).trans (hT (M f))⟩
  · rw [act_unip, mulQ_apply]
    simp only [schr]
    rw [mulQ_apply, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, quad_add A hA]

end GlobalTheory.AdelicSvNQuad

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBottomPairFinitePlacesBelowOfMemExceptional
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section

namespace GlobalTheory.BottomIPData

private theorem mem_bottomPairFinitePlacesBelow_of_mem_exceptional {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (t : T)
    {v : FinPl D} (hv : v ∈ G.pl.S0) : v ∈ sfB G t := by
  classical
  have hw : G.pl.w v ∈ locPl G t := by
    unfold locPl GlobalTheory.ChiGrid.Places.W0
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)
  unfold sfB
  simp only [Finset.mem_image]
  exact ⟨_, hw, G.pl.under_w hv⟩

private theorem under_mem_sfB {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (t : T)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ locPl G t) : w.under (𝓞 D.host.F) ∈ sfB G t := by
  classical
  unfold sfB
  simp only [Finset.mem_image]
  exact ⟨w, hw, rfl⟩

private theorem unrOff_betaB_div_alphaB {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc)
    {μ₀ : T} (hL : Lc.Is μ₀) (i j : Fin D.R.m) (t : T) :
    GlobalTheory.LFun.UnrOff (betaB G i j / alphaB Lc i j t) ((sfB G t : Finset (FinPl D)) : Set (FinPl D)) := by
  classical
  intro w hw
  have hw' : w.under (𝓞 D.host.F) ∉ sfB G t := hw
  have hv : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h => hw' (mem_bottomPairFinitePlacesBelow_of_mem_exceptional G t h)
  have hQ : ∀ P ∈ Lc.Q t, P.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F) := fun P hP e =>
    hw' (e ▸ under_mem_sfB G t (by unfold locPl; exact Finset.mem_union_right _ hP))
  have h1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  have hχ : GlobalTheory.LFun.UnrAt (G.ch.chi (D.R.m - i)) w :=
    (GlobalTheory.LFun.unrAt_iff_of_chrEq (G.ch.chi_eq _ h1 h2) w).2 (G.ch.unr _ h1 h2 w hv)
  have hμ0 : GlobalTheory.LFun.UnrAt (Lc.mu0 ((j : ℕ) + 1)) w := by
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 j) w).2 ((Lc.C.isMu0 j).unr w fun k hk => hv ?_)
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ w.asIdeal
      rw [map_natCast]
      exact hk
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl hk'
    · exact Or.inr (Or.inl hk')
  have hξ : GlobalTheory.LFun.UnrAt (Lc.xi t) w := by
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_
    by_contra hn
    rcases (hL.Q_ram t w).1 hn with hq | ⟨P', hq, hc⟩
    · exact hQ w hq rfl
    · exact hQ P' hq (GlobalTheory.BotTripleUnr.under_eq_of_isConjPl hc)
  have e : betaB G i j / alphaB Lc i j t = G.ch.chi (D.R.m - i) * (Lc.mu0 ((j : ℕ) + 1) * Lc.xi t)⁻¹ := by
    unfold betaB alphaB
    rw [mul_div_mul_right_eq_div, div_eq_mul_inv]
    rfl
  rw [e]
  exact hχ.mul (hμ0.mul hξ).inv

private theorem isSphOff_pureTensorO {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (S T : HSp D) (sS : RealMat S) (sT : RealMat T)
    (BS : RealMat S) (BT : RealMat T) (LS : Lat S) (LT : Lat T) {f₀ Φ f : WO S T → ℂ}
    (hvac : IsVacO ψ θ S T sS sT LS LT f₀) {e : AE D} {Pset : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e Pset)
    (hth : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T LS LT fun _ => True) 1 f₀ Φ f)
    (Sf : Finset (FinPl D)) (hP : ∀ PP ∈ Pset, PP.under (𝓞 D.host.F) ∈ Sf)
    (hpt : ∀ φ, IsFockVec ψ θ S T sS sT (pureTensorO ψ θ S T sS sT BS BT f φ)) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsSphOff ψ S T LS LT Sf (pureTensorO ψ θ S T sS sT BS BT f φ) :=
  GlobalTheory.FockSph.isLatVac_pureTensorO_off hvac.2.inf BS BT hvac he hth Sf hP (fun φ => (hpt φ).1) φ

theorem _root_.GlobalTheory.T.unramifiedInnerProductData_definiteBottom_largeGrids : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ P : PolF D WW.rank A.rank, Unram W.ψ (GlobalTheory.Grid.neg A) WW (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t) X.rA.Λ X.rW.Λ (GlobalTheory.BottomIPData.sfB G t) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro W i j A A' WW X hX t P
  have h := isBottomTri_is hX
  have hψ : IsStdChar D W.ψ (-1) := h.isVac.1
  have hθ : IsInfFam W.θ := h.isVac.2.inf
  have cS : ∀ τ, IsCartanInv (gramAt D (GlobalTheory.Grid.neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (h.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (h.rigW.2.2 τ).1
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f t) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (h.fst t) h.isVac.2.theta
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (h.idem t)
  have hv : ∀ τ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f t) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (h.fst t)
      h.isVac.2.theta hf (h.isVac.2.fock τ)
  have hpt := GlobalTheory.FockSph.isFockVec_pureTensorO (S := GlobalTheory.Grid.neg A) (T := WW) (sS := fun τ => -X.rA.s τ) (sT := X.rW.s)
    hψ hθ cS cT X.rA.B X.rW.B hf hv
  have hs := isSphOff_pureTensorO (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.rA.Λ X.rW.Λ
    h.isVac (h.idem t) (h.fst t) (sfB G t) (fun PP hPP => under_mem_sfB G t hPP) hpt P
  exact ⟨GlobalTheory.RowTest.isSelfDualC_neg' h.rigA.1, h.rigW.1, fun v _ h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2,
    unrOff_betaB_div_alphaB G hL i j t, hs, hs⟩

end GlobalTheory.BottomIPData

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeOIffScaleMulFinitePartMemIdealLatticeStatement
section
open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_latticeO_iff_scale_mul_finitePart_mem_idealLattice : ∀ (D : D7) (S T : HSp D), S.gram = 1 → ∀ (cc : Ideal (𝓞 D.host.K)) (r : D.host.E), cc ≠ ⊥ → IsScale D cc r →
  ∀ u : WO S T, u.map (infPart D) = 0 →
  (u ∈ latO S T (GlobalTheory.VacRead.lsB D cc r S.rank : Set (Fin S.rank → D.host.E)) (stdL D T.rank : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
    ∀ i j, Formalism.MainNotions.StandardLatticesGL3.inc D r * finQ D (u i j) ∈ Formalism.MainNotions.StandardLatticesGL3.IhE D cc) := by
  first | exact @GlobalTheory.SplitLatDict.mem_latO_iff_ihE | exact GlobalTheory.SplitLatDict.mem_latO_iff_ihE | (intros; apply GlobalTheory.SplitLatDict.mem_latO_iff_ihE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfClosedSubmoduleGaussianConvolution
section
open FourierTransform MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.ConvSeries

theorem mem_of_conv_gaussian : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    ∀ (b c : ℝ), 0 < b → 0 < c →
    (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
    ∀ (h u : SchwartzMap E ℂ),
      (∀ y, u y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) →
      u ∈ M := by
  intro E _ _ _ _ _ M hM hℓ b c hb hc hg h u hu
  have ht : ∀ j, ∃ t ∈ M, ∀ y, t y = term b c h j y := by
    intro j
    obtain ⟨t, htM, ht⟩ := GlobalTheory.T.gaussian_mul_multilinear_diagonal_mem_schwartzSubmodule E M hℓ c hc hg j (coef b c h j)
    refine ⟨(((2 * c) ^ j / (j.factorial : ℝ) : ℝ) : ℂ) • t, M.smul_mem _ htM, fun y => ?_⟩
    simp only [SchwartzMap.smul_apply, ht, term, smul_eq_mul]
    ring
  choose t htM hty using ht
  have hs : Summable t := GlobalTheory.T.summable_schwartz_of_summable_seminorms E t (GlobalTheory.T.summable_seminorm_gaussianConvolutionSeriesTerm E b c hb hc h t hty)
  have hL := hs.hasSum
  have hev : ∀ y, (∑' j, t j) y = u y := by
    intro y
    let φ : SchwartzMap E ℂ →L[ℂ] ℂ :=
      (BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ E ℂ)
    have h1 : HasSum (fun j => t j y) ((∑' j, t j) y) := hL.mapL φ
    have h2 : HasSum (fun j => t j y) (u y) := by
      rw [hu y]
      exact (GlobalTheory.T.hasSum_gaussianConvolutionSeriesTerm_integral E b c hb hc h y).congr_fun (fun j => hty j y)
    exact h1.unique h2
  have hLu : (∑' j, t j) = u := SchwartzMap.ext hev
  rw [← hLu]
  exact hM.mem_of_tendsto hL (Eventually.of_forall fun s => M.sum_mem fun j _ => htM j)

end GlobalTheory.ConvSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVertexLatticeOrthonormalCoordsTopNodeIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopLatSplit

open Formalism.L2.Col.Br

private theorem forall_idx {N n : ℕ} (hN : N = n + 1) (p : Fin N → Prop) :
    (∀ i, p i) ↔ (∀ k, p (iC hN k)) ∧ p (iL hN) := by
  subst hN
  exact Fin.forall_fin_succ'

private theorem frame_mulVec {R : Type} [CommRing R] {N n : ℕ} (hN : N = n + 1) (Fr : Matrix (Fin N) (Fin N) R)
    (Q : Matrix (Fin N) (Fin n) R) (a : Fin N → R) (hC : ∀ i k, Fr i (iC hN k) = Q i k) (hL : ∀ i, Fr i (iL hN) = a i)
    (t : Fin N → R) : Fr *ᵥ t = Q *ᵥ (fun k => t (iC hN k)) + t (iL hN) • a := by
  subst hN
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hC, ← hL]
  rw [Fin.sum_univ_castSucc, mul_comm (t _)]
  rfl

private theorem block {R : Type} [CommRing R] {N n : ℕ} (hN : N = n + 1) (A Fr : GL (Fin N) R) (B fr : GL (Fin n) R)
    (P : Matrix (Fin N) (Fin n) R) (a : Fin N → R) (hP : A.val * P = P * B.val) (ha : A.val *ᵥ a = a)
    (hC : ∀ i k, Fr.val i (iC hN k) = (P * fr.val) i k) (hL : ∀ i, Fr.val i (iL hN) = a i) (v : Fin N → R) :
    (∀ k, (((Fr⁻¹ * A * Fr)⁻¹).val *ᵥ v) (iC hN k) = (((fr⁻¹ * B * fr)⁻¹).val *ᵥ fun k => v (iC hN k)) k) ∧
      (((Fr⁻¹ * A * Fr)⁻¹).val *ᵥ v) (iL hN) = v (iL hN) := by
  obtain ⟨z, hzC, hzL⟩ : ∃ z : Fin N → R, (∀ k, z (iC hN k) = (((fr⁻¹ * B * fr)⁻¹).val *ᵥ fun k => v (iC hN k)) k) ∧
      z (iL hN) = v (iL hN) := by
    subst hN
    refine ⟨Fin.snoc (α := fun _ => R) (((fr⁻¹ * B * fr)⁻¹).val *ᵥ fun k => v (iC rfl k)) (v (iL rfl)), fun k => ?_, ?_⟩
    · exact Fin.snoc_castSucc (α := fun _ => R) _ _ k
    · exact Fin.snoc_last (α := fun _ => R) _ _
  have e1 : B.val * fr.val * ((fr⁻¹ * B * fr)⁻¹).val = fr.val := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have e2 : A.val *ᵥ (Fr.val *ᵥ z) = Fr.val *ᵥ v := by
    rw [frame_mulVec hN Fr.val _ a hC hL z, frame_mulVec hN Fr.val _ a hC hL v, funext hzC, hzL, Matrix.mulVec_add,
      Matrix.mulVec_smul, ha, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hP, Matrix.mul_assoc P,
      Matrix.mul_assoc P, e1]
  have e3 : ((Fr⁻¹ * A * Fr)⁻¹).val *ᵥ v = z := by
    have e4 : (Fr⁻¹ * A * Fr).val *ᵥ z = v := by
      rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e2, Matrix.mulVec_mulVec,
        Units.inv_mul, Matrix.one_mulVec]
    rw [← e4, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [e3]
  exact ⟨hzC, hzL⟩

private theorem mem_latAt {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (hX : DefNode D.R.m X) (x : FinPt G X)
    (v : Fin (G.V X).rank → D.host.E) :
    v ∈ GlobalTheory.SumSize.latAt S X x ↔ ∀ i, ((((Formalism.UG.bc (eToEAf D) (S.N.fr X))⁻¹ *
      (Lev.finE (G.V X) x.1 * Lev.finE (G.V X) (S.N.u X).1) * Formalism.UG.bc (eToEAf D) (S.N.fr X))⁻¹).val *ᵥ
        fun i => eToEAf D (v i)) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [← map_inv]
  exact (GlobalTheory.MovedSD.mem_globLat_move D (G.Λ X) (S.N.fr X) _ _ (S.N.u_lat X hX) v).trans (Formalism.L2.Col.mem_latS_std _)

private theorem finE_val {D : D7} (V : HSp D) (g : Formalism.L2.Theta.GA D V) : (Lev.finE V g).val = (mt V g).map (toEAf D) := by
  ext i j
  rfl

private theorem emb_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {N n : ℕ} (x u : Matrix (Fin N) (Fin N) R)
    (y u' : Matrix (Fin n) (Fin n) R) (P : Matrix (Fin N) (Fin n) R) (hx : x * P = P * y) (hu : u * P = P * u') :
    x.map f * u.map f * P.map f = P.map f * (y.map f * u'.map f) := by
  rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.mul_assoc, hu, ← Matrix.mul_assoc, hx,
    Matrix.mul_assoc]

private theorem vec_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {N : ℕ} (x u : Matrix (Fin N) (Fin N) R)
    (a : Fin N → R) (hx : x *ᵥ a = a) (hu : u *ᵥ a = a) :
    (x.map f * u.map f) *ᵥ (fun i => f (a i)) = fun i => f (a i) := by
  funext i
  rw [← Matrix.map_mul]
  refine (RingHom.map_mulVec f (x * u) a i).symm.trans ?_
  rw [← Matrix.mulVec_mulVec, hu, hx]

end GlobalTheory.TopLatSplit

open GlobalTheory.TopLatSplit in
set_option maxHeartbeats 800000 in
theorem _root_.GlobalTheory.T.mem_vertexLatticeOrthonormalCoords_topNode_iff : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ)
    (y : FinPt G (.grid D.R.m D.R.m)) (v : Fin (G.V (.top D.R.m)).rank → D.host.E),
    v ∈ GlobalTheory.SumSize.latAt S (.top D.R.m) (finEmb G.sp.topDec y) ↔
      (fun k => v (Formalism.L2.Col.Br.iC G.sp.topDec.rank.symm k)) ∈ GlobalTheory.SumSize.latAt S (.grid D.R.m D.R.m) y ∧
        ∃ c : 𝓞 D.host.E, (c : D.host.E) = v (Formalism.L2.Col.Br.iL G.sp.topDec.rank.symm) := by
  intro D T L sc G W S y v
  have hrel := finEmb_rel G.sp.topDec y
  have hx1 : mt (G.V (.top D.R.m)) (finEmb G.sp.topDec y).1 * topEmb G = topEmb G * mt (G.V (.grid D.R.m D.R.m)) y.1 := hrel.1
  have hx2 : mt (G.V (.top D.R.m)) (finEmb G.sp.topDec y).1 *ᵥ topVec G = topVec G :=
    hrel.2 (fun i => G.sp.topDec.a i 0) (funext fun k => congr_fun (congr_fun G.sp.topDec.perp k) 0)
  have hb := block (R := Lev.EAf D) (N := (G.V (.top D.R.m)).rank) (n := (G.V (.grid D.R.m D.R.m)).rank) G.sp.topDec.rank.symm
    (Lev.finE (G.V (.top D.R.m)) (finEmb G.sp.topDec y).1 * Lev.finE (G.V (.top D.R.m)) (S.N.u (.top D.R.m)).1)
    (Formalism.UG.bc (eToEAf D) (S.N.fr (.top D.R.m)))
    (Lev.finE (G.V (.grid D.R.m D.R.m)) y.1 * Lev.finE (G.V (.grid D.R.m D.R.m)) (S.N.u (.grid D.R.m D.R.m)).1)
    (Formalism.UG.bc (eToEAf D) (S.N.fr (.grid D.R.m D.R.m)))
    ((topEmb G).map (toEAf D)) (fun i => toEAf D (topVec G i))
    (by
      rw [Units.val_mul, Units.val_mul, finE_val, finE_val, finE_val, finE_val]
      exact emb_map (toEAf D) _ _ _ _ _ hx1 S.N.u_top)
    (by
      rw [Units.val_mul, finE_val, finE_val]
      exact vec_map (toEAf D) _ _ _ hx2 S.N.u_last)
    (fun i k => by
      have e := congrArg (eToEAf D) (S.N.fr_top i k)
      exact e.trans (congr_fun (congr_fun (Matrix.map_mul (f := eToEAf D)) i) k))
    (fun i => congrArg (eToEAf D) (S.N.fr_last i))
    (fun i => eToEAf D (v i))
  refine (mem_latAt S (.top D.R.m) (le_refl D.R.m) (finEmb G.sp.topDec y) v).trans ?_
  refine (forall_idx (N := (G.V (.top D.R.m)).rank) (n := (G.V (.grid D.R.m D.R.m)).rank) G.sp.topDec.rank.symm _).trans ?_
  refine and_congr ?_ ?_
  · refine Iff.trans ?_ (mem_latAt S (.grid D.R.m D.R.m) ⟨le_refl _, rfl⟩ y _).symm
    exact forall_congr' fun k => Iff.of_eq (congrArg (· ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hb.1 k))
  · refine (Iff.of_eq (congrArg (· ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) hb.2)).trans ?_
    exact GlobalTheory.NormSum.AdLattice.incl_mem_iff _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OppositeKernelsRationalRowMapLargeConstantsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oppositeKernelsRationalRowMap_largeConstants : BigC fun _ ch _ _ => RatRowAt ch := by
  first | exact @GlobalTheory.KerConjMean.ratRowAt_big | exact GlobalTheory.KerConjMean.ratRowAt_big | (intros; apply GlobalTheory.KerConjMean.ratRowAt_big <;> assumption)
end

