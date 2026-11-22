import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0089
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0127
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0145
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0175
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0146
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0100
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0107
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0101
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0111
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0174
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0173
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0144
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0176

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepSL2GlBorderedBlock
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilMix

variable {r : ℕ} {F : Type} [NontriviallyNormedField F]

theorem rowMap_mul (g h : SpecialLinearGroup (Fin 2) F) (Y : Gl r F) :
    rowMap (g * h) Y = rowMap h (rowMap g Y) := by
  obtain ⟨A, u, c, l⟩ := Y
  simp only [rowMap, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Prod.mk.injEq, true_and, and_true]
  constructor <;> funext i <;> ring

theorem rowMap_one (Y : Gl r F) : rowMap (1 : SpecialLinearGroup (Fin 2) F) Y = Y := by
  obtain ⟨A, u, c, l⟩ := Y
  simp [rowMap]

theorem continuous_rowMap (g : SpecialLinearGroup (Fin 2) F) : Continuous (rowMap (r := r) g) := by
  unfold rowMap
  fun_prop

theorem isTest_rowAct (g : SpecialLinearGroup (Fin 2) F) (h : Gl r F → ℂ) (hh : IsTest h) : IsTest (rowAct g h) := by
  let e : Gl r F ≃ₜ Gl r F :=
    { toFun := rowMap g, invFun := rowMap g⁻¹
      left_inv := fun Y => by simp [← rowMap_mul, rowMap_one]
      right_inv := fun Y => by simp [← rowMap_mul, rowMap_one]
      continuous_toFun := continuous_rowMap g, continuous_invFun := continuous_rowMap g⁻¹ }
  exact ⟨hh.1.comp_continuous (continuous_rowMap g), hh.2.comp_homeomorph e⟩

end GlobalTheory.JR.WeilMix

open GlobalTheory.JR.WeilMix in
theorem GlobalTheory.JR.weil_repG : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∃ W : SpecialLinearGroup (Fin 2) F → (Gl r F → ℂ) → Gl r F → ℂ, IsTestRep W ∧ ∀ f, IsTest f → (∀ t Y, W (nS t) f Y = ψ (t * mom Y 0) * f Y) ∧ W (wS F) f = fourG M ψ f := by
  intro F E _ _ _ _ _ r M ψ hψ
  have hT := GlobalTheory.T.isLocallyConstantCompactSupport_mixedModelPartialFourierColumn F E r M ψ hψ
  have hI := GlobalTheory.T.mixedModelPartialFourierColumn_twice_neg_column F E r M ψ hψ
  have hL := GlobalTheory.T.mixedModelPartialFourier_linear F E r M ψ hψ
  have hW := GlobalTheory.T.mixedModel_weylElement_eq_partialFourier F E r M ψ hψ
  have hψc : IsLocallyConstant (fun x : F => ψ x) := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).1
  have h4 : ∀ f, IsTest f → ptrB M ψ (ptrB M ψ (ptrB M ψ (ptrB M ψ f))) = f := by
    intro f hf
    rw [hI _ (hT _ (hT _ hf)), hI _ hf]
    funext Y; simp [negB]
  refine ⟨weil M ψ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g f hf
    exact hT _ (hT _ (hT _ (isTest_rowAct g _ (hT _ hf))))
  · intro f hf
    have : rowAct (1 : SpecialLinearGroup (Fin 2) F) (ptrB M ψ f) = ptrB M ψ f := by
      funext Y; simp [rowAct, rowMap_one]
    simp only [weil, this]
    exact h4 f hf
  · intro g h f hf
    simp only [weil]
    rw [h4 _ (isTest_rowAct h _ (hT _ hf))]
    congr 3
    funext Y; simp [rowAct, rowMap_mul]
  · intro g c f f' hf hf'
    have hR : ∀ (a b : Gl r F → ℂ), rowAct g (c • a + b) = c • rowAct g a + rowAct g b := by
      intro a b; funext Y; simp [rowAct]
    simp only [weil]
    rw [hL c f f' hf hf', hR, hL _ _ _ (isTest_rowAct g _ (hT _ hf)) (isTest_rowAct g _ (hT _ hf')),
      hL _ _ _ (hT _ (isTest_rowAct g _ (hT _ hf))) (hT _ (isTest_rowAct g _ (hT _ hf'))),
      hL _ _ _ (hT _ (hT _ (isTest_rowAct g _ (hT _ hf)))) (hT _ (hT _ (isTest_rowAct g _ (hT _ hf'))))]
  · intro f hf
    refine ⟨fun t Y => ?_, ?_⟩
    · let ft : Gl r F → ℂ := fun Y => ψ (t * mom Y 0) * f Y
      have hft : IsTest ft := by
        refine ⟨IsLocallyConstant.mul (hψc.comp_continuous ?_) hf.1, hf.2.mul_left⟩
        simp only [mom, pow_zero, Matrix.one_mulVec]
        fun_prop
      have key : rowAct (nS t) (ptrB M ψ f) = ptrB M ψ ft := by
        funext Y
        obtain ⟨A, u, c, l⟩ := Y
        simp only [rowAct, rowMap, ptrB, nS, ft]
        congr 1
        funext b
        simp only [SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, mul_zero, add_zero,
          mul_one, zero_add, mom, pow_zero, Matrix.one_mulVec]
        have hu : (fun i => c i * t + u i) = t • c + u := by funext i; simp [mul_comm]
        rw [hu, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm b c,
          AddChar.map_add_eq_mul]
        ring
      show ptrB M ψ (ptrB M ψ (ptrB M ψ (rowAct (nS t) (ptrB M ψ f)))) Y = _
      rw [key, h4 ft hft]
    · show ptrB M ψ (ptrB M ψ (ptrB M ψ (rowAct (wS F) (ptrB M ψ f)))) = _
      rw [hI _ (hT _ (isTest_rowAct _ _ (hT _ hf)))]
      exact hW f hf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepSL2HermitianBlock
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem sl2Map_nS {F K : Type} [Field F] [CommRing K] [Algebra F K] (t : F) :
    SpecialLinearGroup.map (algebraMap F K) (nS t) = nS (algebraMap F K t) := by
  apply Subtype.ext
  show (algebraMap F K).mapMatrix !![1, t; 0, 1] = !![1, algebraMap F K t; 0, 1]
  ext i k; fin_cases i <;> fin_cases k <;> simp

theorem sl2Map_wS {F K : Type} [Field F] [CommRing K] [Algebra F K] :
    SpecialLinearGroup.map (algebraMap F K) (wS F) = wS K := by
  apply Subtype.ext
  show (algebraMap F K).mapMatrix !![0, 1; -1, 0] = !![0, 1; -1, 0]
  ext i k; fin_cases i <;> fin_cases k <;> simp

theorem weilSL2_hermitian : WeilEt → GammaOne → ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∃ W : SpecialLinearGroup (Fin 2) F → (Hn r F E → ℂ) → Hn r F E → ℂ, IsTestRep W ∧ ∀ f, IsTest f → (∀ t X, W (nS t) f X = ψ (t * Algebra.trace F E (star X.2.1 ⬝ᵥ X.2.1) / 2) * f X) ∧ W (wS F) f = fourU M ψ f := by
  intro hW hG F E _ _ _ _ _ r M ψ hψ
  obtain ⟨A, e, j, hj, hNe⟩ := GlobalTheory.T.exists_split_etaleHermitianPair_isometry F E r
  haveI : LocallyCompactSpace E := Unram.lcE (F := F)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : SecondCountableTopology E := secondCountable_of_proper
  haveI : CharZero F := Unram.charZero (E := E)
  letI mE : MeasurableSpace E := M.mE
  haveI : BorelSpace E := M.bE
  obtain ⟨hjc, hjsc⟩ := GlobalTheory.T.finiteEtaleHermitian_linearEquiv_continuous F E A r j
  let jh : A.L ≃ₜ (Fin r → E) := { j.toEquiv with continuous_toFun := hjc, continuous_invFun := hjsc }
  let μE : Measure (Fin r → E) := Measure.pi fun _ => M.μE
  let B : (Fin r → E) → (Fin r → E) → ℂ := fun c b => ψ (Algebra.trace F E (star c ⬝ᵥ b))
  have hsd : SelfDual μE B := GlobalTheory.T.isSelfDual_pi_haar_traceStarDotProduct_unramified F E r M ψ hψ
  obtain ⟨hT1, hT2⟩ := GlobalTheory.T.transport_selfDualHaarMeasureKernel_addEquiv j.toAddEquiv hjc hjsc μE B
  have hker : A.kerL ψ ((1 : A.Kˣ) : A.K) = fun x y => B (j.toAddEquiv x) (j.toAddEquiv y) := by
    funext x y
    have h1 := hj x y
    simp only [map_one, one_mul] at h1
    show ψ (Algebra.trace F A.K (((1 : A.Kˣ) : A.K) * Algebra.trace A.K A.L (star x * y))) = ψ (Algebra.trace F E (star (j x) ⬝ᵥ j y))
    rw [Units.val_one, one_mul, GlobalTheory.T.trace_tower_finiteEtaleHermitianPair, h1]
  have hsdL : SelfDual (Measure.map j.toAddEquiv.symm μE) (A.kerL ψ ((1 : A.Kˣ) : A.K)) := by
    rw [hker]; exact hT1 hsd
  obtain ⟨γ, Wk, hWk⟩ := hW F E A ψ hψ 1 _ hsdL
  have hγ : γ = 1 := hG F E A ψ hψ 1 _ hsdL A.etaK γ Wk hWk r j (by simpa using hj)
  obtain ⟨hTrE, -, -⟩ := GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E
  have htr2 : ∀ a : F, Algebra.trace F E (algebraMap F E a) = 2 * a := by
    intro a
    apply (algebraMap F E).injective
    rw [hTrE, Unram.star_fix (F := F) (E := E) a, map_mul, map_ofNat]; ring
  have hnorm : ∀ y : A.L, Algebra.trace F A.K (A.NL y) = Algebra.trace F E (star (j y) ⬝ᵥ j y) / 2 := by
    intro y
    have : star (j y) ⬝ᵥ j y = algebraMap F E (∑ i, e (A.NL y) i) := by
      simp only [dotProduct, Pi.star_apply, map_sum, hNe y, mul_comm]
    rw [this, htr2, GlobalTheory.T.trace_eq_sum_of_algEquiv_pi r e]; field_simp
  have testj : ∀ φ : (Fin r → E) → ℂ, IsTest φ → IsTest (fun y : A.L => φ (j y)) := fun φ hφ =>
    ⟨hφ.1.comp_continuous hjc, hφ.2.comp_homeomorph jh⟩
  have testjs : ∀ φ : A.L → ℂ, IsTest φ → IsTest (fun b => φ (j.symm b)) := fun φ hφ =>
    ⟨hφ.1.comp_continuous hjsc, hφ.2.comp_homeomorph jh.symm⟩
  have hz : IsTest (0 : A.L → ℂ) := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  have hW0 : ∀ G, Wk G 0 = 0 := by
    intro G
    have := hWk.1.2.2.2 G 1 0 0 hz hz
    simp only [one_smul, add_zero] at this
    simpa using this
  let ι : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) A.K := SpecialLinearGroup.map (algebraMap F A.K)
  let T : SpecialLinearGroup (Fin 2) F → ((Fin r → E) → ℂ) → (Fin r → E) → ℂ :=
    fun g φ b => Wk (ι g) (fun y => φ (j y)) (j.symm b)
  have hTt : ∀ g φ, IsTest φ → IsTest (T g φ) := fun g φ hφ => testjs _ (hWk.1.1 _ _ (testj φ hφ))
  have hT0 : ∀ g, T g 0 = 0 := by
    intro g; funext b
    show Wk (ι g) (fun y => (0 : (Fin r → E) → ℂ) (j y)) (j.symm b) = 0
    have : (fun y => (0 : (Fin r → E) → ℂ) (j y)) = 0 := rfl
    rw [this, hW0]; rfl
  have hsl : ∀ f : Hn r F E → ℂ, IsTest f → ∀ X : Hn r F E, IsTest (fun y : A.L => f (X.1, j y, X.2.2)) :=
    fun f hf X => testj _ ((GlobalTheory.T.locallyConstantCompactSupport_slices_operator_apply (T 1) (hTt 1) (hT0 1) f hf).1 X.1 X.2.2)
  refine ⟨fun g f X => T g (fun v => f (X.1, v, X.2.2)) X.2.1, ⟨fun g f hf => (GlobalTheory.T.locallyConstantCompactSupport_slices_operator_apply (T g) (hTt g) (hT0 g) f hf).2, ?_, ?_, ?_⟩, ?_⟩
  · intro f hf; funext X
    show Wk (ι 1) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = f X
    rw [map_one, hWk.1.2.1 _ (hsl f hf X)]
    simp
  · intro g h f hf; funext X
    show Wk (ι (g * h)) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = Wk (ι g) (fun y => Wk (ι h) (fun y' => f (X.1, j y', X.2.2)) (j.symm (j y))) (j.symm X.2.1)
    simp only [LinearEquiv.symm_apply_apply]
    rw [map_mul, hWk.1.2.2.1 _ _ _ (hsl f hf X)]
  · intro g c f f' hf hf'; funext X
    show Wk (ι g) (fun y => (c • f + f') (X.1, j y, X.2.2)) (j.symm X.2.1) = c * Wk (ι g) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) + Wk (ι g) (fun y => f' (X.1, j y, X.2.2)) (j.symm X.2.1)
    have key : (fun y => (c • f + f') (X.1, j y, X.2.2)) = c • (fun y => f (X.1, j y, X.2.2)) + (fun y => f' (X.1, j y, X.2.2)) := rfl
    rw [key, hWk.1.2.2.2 _ _ _ _ (hsl f hf X) (hsl f' hf' X)]
    rfl
  · intro f hf
    refine ⟨fun t X => ?_, ?_⟩
    · have hι : ι (nS t) = nS (algebraMap F A.K t) := by
        exact sl2Map_nS t
      show Wk (ι (nS t)) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = _
      rw [hι, (hWk.2 _ (hsl f hf X)).1]
      have hy := hnorm (j.symm X.2.1)
      rw [LinearEquiv.apply_symm_apply] at hy
      simp only [LinearEquiv.apply_symm_apply, Et.psiK, Units.val_one, mul_one, ← Algebra.smul_def, map_smul, smul_eq_mul, hy, mul_div_assoc]
    · have hι : ι (wS F) = wS A.K := by
        exact sl2Map_wS
      funext X
      show Wk (ι (wS F)) (fun y => f (X.1, j y, X.2.2)) (j.symm X.2.1) = fourU M ψ f X
      rw [hι, (hWk.2 _ (hsl f hf X)).2.2, hγ, one_mul, hker, hT2]
      have e1 : j.toAddEquiv (j.symm X.2.1) = X.2.1 := j.apply_symm_apply _
      rw [e1]
      show ∫ c, f (X.1, j (j.symm c), X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) ∂μE = ∫ c, f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) ∂(Measure.pi fun _ : Fin r => M.μE)
      simp only [LinearEquiv.apply_symm_apply]
      rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePowSmulTorsionLatticeQuotient
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LatTorsFinite

theorem finite_quot_of_isOpen {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [CompactSpace O] (I : Ideal O) (hI : IsOpen (I : Set O)) : Finite (O ⧸ I) := by
  have hU : ∀ x : O, IsOpen ((fun y => y - x) ⁻¹' (I : Set O)) := fun x =>
    hI.preimage (continuous_id.sub continuous_const)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : O => (fun y => y - x) ⁻¹' (I : Set O))
    hU (fun y _ => Set.mem_iUnion.2 ⟨y, by simp [I.zero_mem]⟩)
  refine Finite.of_surjective (fun x : t => Ideal.Quotient.mk I (x : O)) ?_
  intro q
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  refine ⟨⟨x, hx⟩, ?_⟩
  exact (Ideal.Quotient.eq.2 hyx).symm

theorem finite_quot_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] (hO : IsTopologicalRing O) (hc : CompactSpace O)
    (hA : IsAdic (IsLocalRing.maximalIdeal O)) {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    Finite (O ⧸ Ideal.span {ϖ ^ n}) := by
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hopen : IsOpen (((IsLocalRing.maximalIdeal O) ^ n : Ideal O) : Set O) :=
    (isAdic_iff.1 hA).1 n
  rw [hm, Ideal.span_singleton_pow] at hopen
  exact finite_quot_of_isOpen _ hopen

theorem finite_ker_pow_smul {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] (T : Submodule O V) (hO : IsTopologicalRing O)
    (hc : CompactSpace O) (hA : IsAdic (IsLocalRing.maximalIdeal O)) (hT : IsLatticeIn T)
    (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) :
    Finite ↥(LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n))) := by
  haveI := finite_quot_pow hO hc hA hϖ n
  haveI : Module.Finite O T := Module.Finite.iff_fg.2 hT.1
  haveI : Module.Finite (O ⧸ Ideal.span {ϖ ^ n})
      (T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T)) :=
    Module.Finite.of_restrictScalars_finite O _ _
  haveI : Finite (T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T)) :=
    Module.finite_of_finite (O ⧸ Ideal.span {ϖ ^ n})

  let rep : V ⧸ T → V := fun q => Classical.choose (Submodule.Quotient.mk_surjective T q)
  have hrep : ∀ q, Submodule.Quotient.mk (p := T) (rep q) = q := fun q =>
    Classical.choose_spec (Submodule.Quotient.mk_surjective T q)
  have hmem : ∀ x : LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n)),
      ϖ ^ n • rep (x : V ⧸ T) ∈ T := by
    intro x
    have hx : (ϖ ^ n) • (x : V ⧸ T) = 0 := x.2
    rw [← hrep (x : V ⧸ T), ← Submodule.Quotient.mk_smul] at hx
    exact (Submodule.Quotient.mk_eq_zero T).1 hx

  have hinj : ∀ v w : V, ϖ ^ n • v = ϖ ^ n • w → v = w := by
    intro v w h
    have h0 : algebraMap O (FractionRing O) (ϖ ^ n) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact pow_ne_zero _ hϖ.ne_zero
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n) v,
      ← algebraMap_smul (FractionRing O) (ϖ ^ n) w] at h
    exact smul_right_injective V h0 h
  let f : LinearMap.ker (LinearMap.lsmul O (V ⧸ T) (ϖ ^ n)) →
      T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O T) :=
    fun x => Submodule.Quotient.mk ⟨ϖ ^ n • rep (x : V ⧸ T), hmem x⟩
  refine Finite.of_injective f ?_
  intro x y hxy
  rw [Submodule.Quotient.eq, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hxy
  obtain ⟨t, -, ht⟩ := hxy
  have ht' : ϖ ^ n • (t : V) = ϖ ^ n • (rep (x : V ⧸ T) - rep (y : V ⧸ T)) := by
    rw [smul_sub]
    exact congrArg Subtype.val ht
  have hd := hinj _ _ ht'
  apply Subtype.ext
  rw [← hrep (x : V ⧸ T), ← hrep (y : V ⧸ T), Submodule.Quotient.eq, ← hd]
  exact t.2

end GlobalTheory.LatTorsFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierDescendedFunctionEqPartialFourier
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.FourDesc

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem continuous_of_isStdChar {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : Continuous (fun x => ψ x) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have h : ∀ᶠ z in 𝓝 x, ψ x = ψ z := by
    filter_upwards [Metric.closedBall_mem_nhds x one_pos] with z hz
    have hz' : ‖z - x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have e : z = x + (z - x) := by abel
    rw [e, AddChar.map_add_eq_mul, hψ.1 (z - x) hz', mul_one]
  exact continuousAt_const.congr h

theorem continuous_star_E [Unram F E] : Continuous (star : E → E) :=
  (Isometry.of_dist_eq fun a b => by
    rw [dist_eq_norm, dist_eq_norm, ← star_sub, Unram.norm_star (F := F)]).continuous

end GlobalTheory.JR.FourDesc

open GlobalTheory.JR.FourDesc in
theorem GlobalTheory.JR.fourB_descFn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → ∀ (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → fourB μ (A.kerL ψ x) (A.descFn M Ax j lam α f) = A.descFn M Ax j lam α (fourU M ψ f) := by
  intro F E _ _ _ _ _ A ψ hψ r M x j hx μ hμ Ax lam α hα hαc f hf
  haveI : LocallyCompactSpace E := Unram.lcE (F := F) (E := E)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : LocallyCompactSpace F := Unram.lcF (F := F) (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  letI := M.mE
  haveI := M.bE
  letI := M.mU
  haveI := M.bU
  haveI := M.haarE
  haveI := M.haarU
  haveI : SigmaFinite M.μE := sigmaFinite_of_locallyFinite
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ (Unram.finrank_eq (F := F) (E := E))
  haveI : ContinuousStar E := ⟨continuous_star_E (F := F)⟩
  obtain ⟨P, hP⟩ : ∃ P : Measure (Fin r → E), P = Measure.pi fun _ => M.μE := ⟨_, rfl⟩
  haveI : SigmaFinite P := by rw [hP]; infer_instance
  haveI : IsFiniteMeasureOnCompacts P := by rw [hP]; infer_instance
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (Matrix.unitaryGroup (Fin r) E), ν = M.μU.restrict (tsupport α) := ⟨_, rfl⟩
  haveI : IsFiniteMeasure ν := by
    rw [hν]; exact isFiniteMeasure_restrict.2 hαc.isCompact.measure_lt_top.ne
  haveI : IsFiniteMeasureOnCompacts (P.prod ν) := inferInstance
  have hψc := continuous_of_isStdChar hψ
  have htr : Continuous (fun e : E => Algebra.trace F E e) :=
    LinearMap.continuous_of_finiteDimensional (Algebra.trace F E)
  have hfc : Continuous f := hf.1.continuous
  have hαcont : Continuous α := hα.continuous
  have hstar : ∀ (g : Matrix.unitaryGroup (Fin r) E) (v w : Fin r → E),
      star (g.1 *ᵥ v) ⬝ᵥ (g.1 *ᵥ w) = star v ⬝ᵥ w := by
    intro g v w
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
      Unitary.star_mul_self_of_mem g.2, Matrix.one_mulVec]
  let jg : Matrix.unitaryGroup (Fin r) E → (A.L ≃ₗ[E] (Fin r → E)) :=
    fun g => j.trans (Matrix.UnitaryGroup.toLinearEquiv g)
  have hjg : ∀ g y, jg g y = g.1 *ᵥ j y := fun g y => rfl
  have hjgI : ∀ g, A.IsIsom x (jg g) := fun g y y' => by rw [hjg, hjg, hstar, hx]
  have I := GlobalTheory.T.map_isIsom_selfDualMeasure_kerL_eq_pi_haar F E A ψ hψ r M x
  have hker : ∀ y' y, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y)) := (I j hx).1
  have hmapj : Measure.map j μ = P := by rw [hP]; exact (I j hx).2 μ hμ
  have hmapg : ∀ g, Measure.map (jg g) μ = P := fun g => by rw [hP]; exact (I (jg g) (hjgI g)).2 μ hμ
  have hjc : Continuous j :=
    IsModuleTopology.continuous_of_linearMap (R := F) ((j : A.L →ₗ[E] (Fin r → E)).restrictScalars F)
  have hjm : Measurable j := hjc.measurable
  have hgc : ∀ g : Matrix.unitaryGroup (Fin r) E, Continuous (fun v : Fin r → E => g.1 *ᵥ v) :=
    fun g => continuous_const.matrix_mulVec continuous_id
  have hPg : ∀ g : Matrix.unitaryGroup (Fin r) E, Measure.map (fun v => g.1 *ᵥ v) P = P := by
    intro g
    have e : (fun v => g.1 *ᵥ v) ∘ j = ⇑(jg g) := funext fun y => (hjg g y).symm
    conv_lhs => rw [← hmapj]
    rw [Measure.map_map (hgc g).measurable hjm, e, hmapg g]
  have hres : ∀ h : Matrix.unitaryGroup (Fin r) E → ℂ, (∀ g, g ∉ tsupport α → h g = 0) →
      ∫ g, h g ∂ν = ∫ g, h g ∂M.μU := by
    intro h hh
    rw [hν]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hh
  funext y
  let G : (Fin r → E) → Matrix.unitaryGroup (Fin r) E → ℂ := fun v g =>
    f (actU g (Ax, v, lam)) * (α g : ℂ) * ψ (Algebra.trace F E (star v ⬝ᵥ j y))
  have hact : Continuous (fun p : (Fin r → E) × Matrix.unitaryGroup (Fin r) E => actU p.2 (Ax, p.1, lam)) := by
    unfold actU
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.prodMk ?_ continuous_const)
    · fun_prop
    · fun_prop
  have hGc : Continuous (Function.uncurry G) := by
    have h1 : Continuous (fun p : (Fin r → E) × Matrix.unitaryGroup (Fin r) E => star p.1 ⬝ᵥ j y) := by fun_prop
    exact ((hfc.comp hact).mul (Complex.continuous_ofReal.comp (hαcont.comp continuous_snd))).mul
      (hψc.comp (htr.comp h1))
  have hGs : HasCompactSupport (Function.uncurry G) := by
    refine HasCompactSupport.intro (((hf.2.isCompact.prod hαc.isCompact).image
      (f := fun q : Hn r F E × Matrix.unitaryGroup (Fin r) E => (star q.2.1 *ᵥ q.1.2.1, q.2)) (by fun_prop))) ?_
    rintro ⟨v, g⟩ hvg
    by_contra hne
    apply hvg
    have h1 : f (actU g (Ax, v, lam)) ≠ 0 := fun h => hne (by simp [G, h])
    have h2 : α g ≠ 0 := fun h => hne (by simp [G, h])
    refine ⟨(actU g (Ax, v, lam), g), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, ?_⟩
    simp only [actU, Prod.mk.injEq, and_true]
    rw [Matrix.mulVec_mulVec, Unitary.star_mul_self_of_mem g.2, Matrix.one_mulVec]
  have hGi : Integrable (Function.uncurry G) (P.prod ν) := hGc.integrable_of_hasCompactSupport hGs
  have hL : fourB μ (A.kerL ψ x) (A.descFn M Ax j lam α f) y = ∫ v, ∫ g, G v g ∂ν ∂P := by
    have e : ∀ y', A.descFn M Ax j lam α f y' * A.kerL ψ x y' y = (fun v => ∫ g, G v g ∂ν) (j y') := by
      intro y'
      simp only [Et.descFn, hker, G]
      rw [← hres _ (fun g hg => by simp [image_eq_zero_of_notMem_tsupport hg]), ← integral_mul_const]
    simp only [fourB, e]
    rw [← hmapj, integral_map hjm.aemeasurable (by
      rw [hmapj]; exact (hGc.stronglyMeasurable.integral_prod_right (ν := ν)).aestronglyMeasurable)]
  rw [hL, integral_integral_swap hGi]
  simp only [Et.descFn]
  rw [← hres _ (fun g hg => by simp [image_eq_zero_of_notMem_tsupport hg])]
  congr 1
  funext g
  have e1 : ∀ v, G v g = (f ((actU g (Ax, j y, lam)).1, g.1 *ᵥ v, lam) *
      ψ (Algebra.trace F E (star (g.1 *ᵥ v) ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) * (α g : ℂ) := by
    intro v
    simp only [G, actU, hstar]
    ring
  simp_rw [e1]
  rw [integral_mul_const]
  congr 1
  have hHc : Continuous (fun c : Fin r → E => f ((actU g (Ax, j y, lam)).1, c, lam) *
      ψ (Algebra.trace F E (star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) := by
    have h1 : Continuous (fun c : Fin r → E => star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1) := by fun_prop
    have h2 : Continuous (fun c : Fin r → E => ((actU g (Ax, j y, lam)).1, c, lam)) := by fun_prop
    exact (hfc.comp h2).mul (hψc.comp (htr.comp h1))
  have key : ∫ c, (fun c : Fin r → E => f ((actU g (Ax, j y, lam)).1, c, lam) *
      ψ (Algebra.trace F E (star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) c ∂(Measure.map (fun v => g.1 *ᵥ v) P) =
      ∫ v, (fun c : Fin r → E => f ((actU g (Ax, j y, lam)).1, c, lam) *
      ψ (Algebra.trace F E (star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) (g.1 *ᵥ v) ∂P :=
    integral_map (hgc g).measurable.aemeasurable (by rw [hPg g]; exact hHc.aestronglyMeasurable)
  rw [hPg g] at key
  rw [key.symm]
  simp only [fourU]
  rw [hP]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMemRigidFunctionsOfMemInvertEisensteinStatement
section
open PowerSeries GlobalTheory.BK Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_mem_rigidFunctions_of_mem_invertEisenstein : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (k : ℝ), 1 / ((e : ℝ) * l) < k → ∀ f ∈ invE l e (A O K), frob K l f ∈ R O K l k := by
  first | exact @GlobalTheory.BK.frob_mem_R_of_mem_invE_A | exact GlobalTheory.BK.frob_mem_R_of_mem_invE_A | (intros; apply GlobalTheory.BK.frob_mem_R_of_mem_invE_A <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusRecursionDifferencesDecayGaussNormStatement
section
open PowerSeries GlobalTheory.BK Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_recursion_differences_decay_gaussNorm : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l a : ℕ) [Fact l.Prime] [NeZero a] (ι : Type) [Fintype ι] [DecidableEq ι] (k : ℝ), 0 < k → ∀ (B : ZMod a → Matrix ι ι K⟦X⟧) (c : ZMod a → Matrix ι ι K) (Z : ℕ → ZMod a → Matrix ι ι K⟦X⟧), (∀ τ i j, B τ i j ∈ R O K l k) → (∀ τ, Z 0 τ = (c τ).map C) → (∀ n τ, Z (n + 1) τ = B τ * (Z n (τ - 1)).map (frob K l) * (c τ).map C) → (∀ τ i j, (X : K⟦X⟧) ∣ Z 1 τ i j - Z 0 τ i j) → ∃ M β : ℝ, 0 ≤ β ∧ ∀ n τ i j, Z n τ i j ∈ R O K l k ∧ normR l k (Z (n + 1) τ i j - Z n τ i j) ≤ M * β ^ n * rad l k ^ (l ^ n) := by
  first | exact @GlobalTheory.BK.frob_recursion_decay | exact GlobalTheory.BK.frob_recursion_decay | (intros; apply GlobalTheory.BK.frob_recursion_decay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeneralizedEigenPartProjectorMemHeckeAlgebraStatement
section
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generalizedEigenPartProjector_mem_heckeAlgebra : ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V] (S : Set (Module.End K V)), (∀ a ∈ S, ∀ b ∈ S, Commute a b) → (∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤) → (∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range) → ∀ (L : Submodule O V), L.FG → Submodule.span K (L : Set V) = ⊤ → (∀ a ∈ S, ∀ x ∈ L, a x ∈ L) → ∀ 𝔪 : Ideal (Algebra.adjoin O S), ∃ t ∈ Algebra.adjoin O S, (∀ x ∈ NCov.part (Algebra.adjoin O S) 𝔪, t x = x) ∧ ∀ x ∈ NCov.off (Algebra.adjoin O S) 𝔪, t x = 0 := by
  first | exact @GlobalTheory.part_projector_mem_adjoin | exact GlobalTheory.part_projector_mem_adjoin | (intros; apply GlobalTheory.part_projector_mem_adjoin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HighestWeightAtConjugateEmbeddingRevNegStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highestWeightAt_conjugate_embedding_rev_neg : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (τ : L →+* ℂ) (lam' : Fin n → ℤ), a.HWAt (ComplexEmbedding.conjugate τ) lam' → a.HWAt τ (fun i => -lam' (Fin.rev i)) := by
  first | exact @GlobalTheory.hwAt_conj_swap | exact GlobalTheory.hwAt_conj_swap | (intros; apply GlobalTheory.hwAt_conj_swap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedClassFunctionMemInducedDegreeOneCharDiffStatement
section
open GlobalTheory.BI GlobalTheory.BrauerZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inducedClassFunction_mem_inducedDegreeOneCharDiff : ∀ {G : Type} [Group G] [Finite G] (E : Subgroup G) (f : E → ℂ), f ∈ D0 E → ind E f ∈ D0 G := by
  first | exact @GlobalTheory.BrauerZero.ind_mem_D0_of_mem_D0 | exact GlobalTheory.BrauerZero.ind_mem_D0_of_mem_D0 | (intros; apply GlobalTheory.BrauerZero.ind_mem_D0_of_mem_D0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveOfPhiModuleExactTripleStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_of_phiModule_exact_triple : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : Hom P Q) (G : Hom Q T), IsExactTriple F G → Function.Injective F.app := by
  first | exact @GlobalTheory.BK.IsExactTriple.injective_app | exact GlobalTheory.BK.IsExactTriple.injective_app | (intros; apply GlobalTheory.BK.IsExactTriple.injective_app <;> assumption)
end

