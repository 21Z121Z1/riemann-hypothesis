import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0354
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0220
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormMeanInfPosLogLeDefiniteThetaPair
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationCompEqCocycleMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormPadicWeierstrassModelAbscissaTwoTorsionLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0244

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousToK
section
noncomputable section

open scoped MatrixGroups
open Polynomial

namespace GlobalTheory.K4.TopEta

open GlobalTheory.KZ GlobalTheory.NeedB GlobalTheory.KEdge

section General

variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]

def toK : geo F K Ω →* (Ω ≃ₐ[K] Ω) :=
  MonoidHom.mk' (fun g => { (g : Ω ≃ₐ[F] Ω).toRingEquiv with commutes' := (TopW.mem_geo _).1 g.2 })
    (fun _ _ => AlgEquiv.ext fun _ => rfl)

theorem toK_apply (g : geo F K Ω) (z : Ω) : toK g z = (g : Ω ≃ₐ[F] Ω) z := rfl

theorem continuous_toK [Algebra.IsAlgebraic F Ω] : Continuous (toK : geo F K Ω →* (Ω ≃ₐ[K] Ω)) := by
  apply continuous_of_continuousAt_one
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, hE, hsub⟩ := hs
  let b := Module.finBasis K E
  have hop : IsOpen (⋂ i, (MulAction.stabilizer (Ω ≃ₐ[F] Ω) (b i : Ω) : Set (Ω ≃ₐ[F] Ω))) :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral (K := F) (b i : Ω)
  refine Filter.mem_map.2 (Filter.mem_of_superset ((hop.preimage continuous_subtype_val).mem_nhds ?_) ?_)
  · simp only [Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe]
    exact fun i => Subgroup.one_mem _
  · intro g hg
    simp only [Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hg
    apply hsub
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    have hlin : (((toK g).toLinearMap).comp E.val.toLinearMap) = E.val.toLinearMap :=
      b.ext fun i => hg i
    exact LinearMap.congr_fun hlin ⟨z, hz⟩

theorem exists_extend [Algebra.IsAlgebraic F Ω] {N : ℕ} {ζ α β : Ω} {x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)}
    (hx : ∀ g, (x g).toAdd = kum (K := F) (N := N) ζ α g) (hy : ∀ g, (y g).toAdd = kum (K := F) (N := N) ζ β g)
    (R : Subring K) (η : (Ω ≃ₐ[K] Ω) → ZMod N) (h1 : IsLocallyConstant η)
    (h2 : ∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g)
    (h3 : ∀ B : ValuationSubring Ω, Over R B → ∀ g, Inert B g → η g = 0) :
    ∃ η' : (Ω ≃ₐ[F] Ω) → ZMod N, CobOn (geo F K Ω) x y η' ∧ IsLocallyConstant (fun g : geo F K Ω => η' g) ∧
      ∀ (B : ValuationSubring Ω) (g : Ω ≃ₐ[F] Ω), Over R B →
        (∀ z, B.valuation z ≤ 1 → B.valuation (g z - z) < 1) → g ∈ geo F K Ω → η' g = 0 := by
  classical
  refine ⟨fun g => if h : g ∈ geo F K Ω then η (toK ⟨g, h⟩) else 0, fun g hg h hh => ?_, ?_, fun B g hB hi hg => ?_⟩
  · simp only [dif_pos hg, dif_pos hh, dif_pos (mul_mem hg hh)]
    rw [hx, hy]
    have e : toK (⟨g * h, mul_mem hg hh⟩ : geo F K Ω) = toK ⟨g, hg⟩ * toK ⟨h, hh⟩ := map_mul toK ⟨g, hg⟩ ⟨h, hh⟩
    rw [e]
    exact h2 (toK ⟨g, hg⟩) (toK ⟨h, hh⟩)
  · have e : (fun g : geo F K Ω => if h : (g : Ω ≃ₐ[F] Ω) ∈ geo F K Ω then η (toK ⟨(g : Ω ≃ₐ[F] Ω), h⟩) else 0) = η ∘ toK :=
      funext fun g => by rw [dif_pos g.2]; rfl
    rw [e]
    exact h1.comp_continuous continuous_toK
  · simp only [dif_pos hg]
    exact h3 B hB _ hi

end General

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem fixMu_eq {M : ℕ} (hM : M ≠ 0) {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) :
    fixMu Ω M = (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup := by
  haveI : NeZero M := ⟨hM⟩
  unfold fixMu
  congr 1
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
    exact pow_mem (IntermediateField.subset_adjoin ℚ {ζ} rfl) i
  · exact IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.2 hζ.pow_eq_one)

attribute [local instance] algMdl

theorem normal_top [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {M : ℕ} (hM : M ≠ 0) : Normal (topF X M) (topL X M) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have h := LevNormal.normal Ω ε X (CongruenceSubgroup.Gamma M) M _ (Nat.pos_of_ne_zero hM) (isPrimitiveRoot_eOm ε hM) le_rfl
  rw [← fixMu_eq hM (isPrimitiveRoot_eOm ε hM)] at h
  exact h

theorem over_iff (X : Tower Ω ε) (M : ℕ) (B : ValuationSubring (topBar X M)) :
    letI := algPoly X (CongruenceSubgroup.Gamma M)
    Over (FunctionField.ringOfIntegers Ω (topL X M)).toSubring B ↔
      ∀ f : topL X M, ((f : X.K) = X.jK ∨ (f : X.K) ∈ Set.range (algebraMap Ω X.K)) →
        algebraMap (topL X M) (topBar X M) f ∈ B := by
  letI := algPoly X (CongruenceSubgroup.Gamma M)
  constructor
  · intro h f hf
    apply h
    have : ∃ P : Polynomial Ω, algebraMap (Polynomial Ω) (topL X M) P = f := by
      rcases hf with hf | ⟨c, hc⟩
      · exact ⟨Polynomial.X, Subtype.ext ((coe_jPoly X _ _).trans (by rw [aeval_X, hf]))⟩
      · exact ⟨C c, Subtype.ext ((coe_jPoly X _ _).trans (by rw [aeval_C, hc]))⟩
    obtain ⟨P, rfl⟩ := this
    exact Subalgebra.algebraMap_mem _ P
  · intro h f hf
    have hP : ∀ P : Polynomial Ω,
        ((algebraMap (topL X M) (topBar X M)).comp (algebraMap (Polynomial Ω) (topL X M))) P ∈ B := by
      intro P
      induction P using Polynomial.induction_on with
      | C c => exact h _ (Or.inr ⟨c, ((coe_jPoly X _ _).trans (by rw [aeval_C])).symm⟩)
      | add p q hp hq => rw [map_add]; exact add_mem hp hq
      | monomial k c hk =>
        rw [pow_succ, ← mul_assoc, map_mul]
        exact mul_mem hk (h _ (Or.inl ((coe_jPoly X _ _).trans (by rw [aeval_X]))))
    obtain ⟨q, hq, h0⟩ : IsIntegral (Polynomial Ω) f := hf
    let φ : Polynomial Ω →+* B := RingHom.codRestrict _ B hP
    have hi : IsIntegral B (algebraMap (topL X M) (topBar X M) f) := by
      refine ⟨q.map φ, hq.map φ, ?_⟩
      rw [eval₂_map]
      have := congrArg (algebraMap (topL X M) (topBar X M)) h0
      rw [hom_eval₂, map_zero] at this
      exact this
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
    rw [← hy]
    exact y.2

theorem spec_of_units [IsAlgClosure ℚ Ω] (X : Tower Ω ε) {M l n : ℕ} (hM : M ≠ 0) (hl : l ≠ 0) (hlM : l ^ n ∣ M) {u v : X.K}
    (hu : TopUnits.IsTopUnit X M u) (hv : TopUnits.IsTopUnit X M v) :
    (∃ η, IsTopEta X M (topChar X M l n u) (topChar X M l n v) η) ∧
      ∀ φ : topGal X M, IsTopW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v)
        (topEta X M (topChar X M l n u) (topChar X M l n v)) φ
        (topW (K := topL X M) (topZeta X M l n) (topChar X M l n u) (topChar X M l n v)
          (topEta X M (topChar X M l n u) (topChar X M l n v)) φ) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : CharZero Ω := algebraRat.charZero Ω
  letI := algPoly X (CongruenceSubgroup.Gamma M)
  letI := algRat X (CongruenceSubgroup.Gamma M)
  haveI := isScalarTower_poly_rat X (CongruenceSubgroup.Gamma M)
  haveI : FiniteDimensional (RatFunc Ω) (topL X M) := GlobalTheory.T.finiteDimensional_lev_of_gamma_le Ω ε X _ M (Nat.pos_of_ne_zero hM) le_rfl
  haveI := normal_top X hM
  haveI : Algebra.IsAlgebraic (topF X M) (topBar X M) := Algebra.IsAlgebraic.trans _ (topL X M) _
  obtain ⟨hu0, huF, huL, hu1, hu2⟩ := hu
  obtain ⟨hv0, hvF, hvL, hv1, hv2⟩ := hv
  have hN : 0 < l ^ n := Nat.pos_of_ne_zero (pow_ne_zero n hl)
  have hζ := isPrimitiveRoot_topZeta X M hl n
  have hα := topRoot_pow X M hN.ne' huL
  have hβ := topRoot_pow X M hN.ne' hvL
  have hx := topChar_apply X hl hlM huF hu0
  have hy := topChar_apply X hl hlM hvF hv0
  have ha : ∃ η, IsTopEta X M (topChar X M l n u) (topChar X M l n v) η := by
    obtain ⟨-, -, -, -, η, h1, h2, h3⟩ := GlobalTheory.T.kummerCupProduct_coboundary_theorem Ω (topL X M) (topBar X M) (l ^ n) _ hN hζ ⟨u, huL⟩ ⟨v, hvL⟩ _ _
      (fun h => hu0 (congrArg Subtype.val h)) (fun h => hv0 (congrArg Subtype.val h)) hu1 hu2 hv1 hv2 hα hβ
    obtain ⟨η', g1, g2, g3⟩ := exists_extend hx hy _ η h1 h2 h3
    exact ⟨η', g1, g2, fun B g hB => g3 B g ((over_iff X M B).2 hB)⟩
  refine ⟨ha, fun φ => ?_⟩
  obtain ⟨g1, g2, g3⟩ := isTopEta_topEta X M ha
  refine isTopW_topW Ω (topL X M) (topBar X M) (topF X M) (l ^ n) _ hN hζ (topGal_topZeta X hl hlM)
    (map_mem_ringOfIntegers_of_fix_mdl Ω ε X _ _) ⟨u, huF⟩ ⟨v, hvF⟩ (topRoot X M (l ^ n) u) (topRoot X M (l ^ n) v)
    (fun h => hu0 (congrArg Subtype.val h)) (fun h => hv0 (congrArg Subtype.val h)) hu1 hu2 hv1 hv2 ?_ ?_ _ _ hx hy _ g1 g2
    (fun B g hB => g3 B g ((over_iff X M B).1 hB)) φ
  · rw [hα, IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M)]
    rfl
  · rw [hβ, IsScalarTower.algebraMap_apply (topF X M) (topL X M) (topBar X M)]
    rfl

end GlobalTheory.K4.TopEta

namespace GlobalTheory.K4

open GlobalTheory.KZ

attribute [local instance] algMdl

theorem wkTop_spec : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (l n r N : ℕ) (x : ZMod N) (c d : ℕ), l.Prime → 0 < N → 1 ≤ r + n → Nat.Coprime l N → 1 < c → 1 < d →
    Nat.Coprime c (6 * l * N) → Nat.Coprime d (6 * l * N) →
    (∃ η, IsTopEta X (l ^ (r + n) * N) (topChar X (l ^ (r + n) * N) l n (topU X l (r + n) N x c))
      (topChar X (l ^ (r + n) * N) l n (topV X l (r + n) N d)) η) ∧
    ∀ σ ∈ fixMu Ω (l ^ (r + n) * N),
      IsTopW (K := topL X (l ^ (r + n) * N)) (topZeta X (l ^ (r + n) * N) l n)
        (topChar X (l ^ (r + n) * N) l n (topU X l (r + n) N x c))
        (topChar X (l ^ (r + n) * N) l n (topV X l (r + n) N d))
        (topEta X (l ^ (r + n) * N) (topChar X (l ^ (r + n) * N) l n (topU X l (r + n) N x c))
          (topChar X (l ^ (r + n) * N) l n (topV X l (r + n) N d)))
        (topLift X (l ^ (r + n) * N) σ)⁻¹ ⟨wkTop X l n r N x c d σ, wkTop_mem X l n r N x c d σ⟩ := by
  intro Ω _ _ _ ε X l n r N x c d hl hN hs hlN hc1 hd1 hc hd
  obtain ⟨hu, hv⟩ := TopUnits.isTopUnit_topU_topV X x hl hN hs hlN hc1 hd1 hc hd
  obtain ⟨h1, h2⟩ := TopEta.spec_of_units X (mul_ne_zero (pow_ne_zero _ hl.ne_zero) hN.ne') hl.ne_zero
    (pow_dvd_topLevel l n r N) hu hv
  exact ⟨h1, fun σ _ => h2 _⟩

end GlobalTheory.K4
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeClassEqKummerCharacterOfChosenRootFunctionFiStatement
section
open GlobalTheory.K4 GlobalTheory.KEdge GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.edgeClass_eq_kummerCharacter_of_chosen_root_function_field : ∀ (k K Ω F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field F] [Algebra F K] [Algebra F Ω] [IsScalarTower F K Ω] [Normal F K]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[F] Ω, g ζ = ζ) →
  (∀ τ : K ≃ₐ[F] K, ∀ x ∈ FunctionField.ringOfIntegers k K, τ x ∈ FunctionField.ringOfIntegers k K) →
  ∀ (a b : F) (α β : Ω), a ≠ 0 → b ≠ 0 → algebraMap F K a ∈ FunctionField.ringOfIntegers k K → (algebraMap F K a)⁻¹ ∈ FunctionField.ringOfIntegers k K →
    algebraMap F K b ∈ FunctionField.ringOfIntegers k K → (algebraMap F K b)⁻¹ ∈ FunctionField.ringOfIntegers k K →
    α ^ N = algebraMap F Ω a → β ^ N = algebraMap F Ω b →
  ∀ (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)), (∀ g, (x g).toAdd = kum (N := N) ζ α g) → (∀ g, (y g).toAdd = kum (N := N) ζ β g) →
  ∀ η : (Ω ≃ₐ[F] Ω) → ZMod N, CobOn (geo F K Ω) x y η →
    IsLocallyConstant (fun g : geo F K Ω => η g) →
    (∀ (B : ValuationSubring Ω) (g : Ω ≃ₐ[F] Ω), Over (FunctionField.ringOfIntegers k K).toSubring B →
      (∀ z, B.valuation z ≤ 1 → B.valuation (g z - z) < 1) → g ∈ geo F K Ω → η g = 0) →
  ∀ σ : Ω ≃ₐ[F] Ω, IsTopW (K := K) ζ x y η σ (topW (K := K) ζ x y η σ) := by
  first | exact @GlobalTheory.K4.isTopW_topW | exact GlobalTheory.K4.isTopW_topW | (intros; apply GlobalTheory.K4.isTopW_topW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularUnitsOfRootMemKummerAdjoinStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_modularUnits_of_root_mem_kummer_adjoin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (m l : ℕ), 0 < m → 0 < l → ∀ (θ : AlgebraicClosure X.K) (f : X.Kˣ), θ ∈ IntermediateField.adjoin X.K {y : AlgebraicClosure X.K | ∃ U ∈ X.Un m, y ^ m = algebraMap X.K (AlgebraicClosure X.K) (U : X.K)} → θ ^ l = algebraMap X.K (AlgebraicClosure X.K) (f : X.K) → f ∈ X.Un l := by
  first | exact @GlobalTheory.KZ.UnRoot.mem_Un_of_root_mem_adjoin | exact GlobalTheory.KZ.UnRoot.mem_Un_of_root_mem_adjoin | (intros; apply GlobalTheory.KZ.UnRoot.mem_Un_of_root_mem_adjoin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormMeanInfPosLogLeDefiniteThetaPairStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_meanInf_posLog_le_definiteThetaPair : ∃ C : ℝ, 0 < C ∧ ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → 0 < Q → ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (σ : K →+* ℂ) (N : ℕ) (B L : ℝ) (P : Pair D cc δ t0 Q) (x : K), 1 ≤ N → 1 ≤ B → 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → P.Small N B → σ x = (P.norm : ℂ) → Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.posLog ‖v.embedding x‖) ≤ C * fF D * (2 * (N : ℝ)) * B * (L + Real.log (B * (2 * (N : ℝ)))) + C * fF D * (N : ℝ) ^ 2 * (L + Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B)) + C * (N : ℝ) ^ 2 * Real.log Q := by
  first | exact @GlobalTheory.ArchFree.norm.norm_meanInf_posLog_le | exact GlobalTheory.ArchFree.norm.norm_meanInf_posLog_le | (intros; apply GlobalTheory.ArchFree.norm.norm_meanInf_posLog_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaJetClassSumArchimedeanBoundOfCmThetaStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaJetClassSum_archimedeanBound_of_cmTheta : (∀ D, Inp D) → ArchSt := by
  first | exact @GlobalTheory.ArchTop.archSt_of_inp | exact GlobalTheory.ArchTop.archSt_of_inp | (intros; apply GlobalTheory.ArchTop.archSt_of_inp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionTranslateThetaJetsDenominatorBound
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TorsionJets

open PowerSeries GlobalTheory.ThetaParam

variable {p : ℕ} [Fact p.Prime]

theorem lamC_natCast (lam : Qbar →+* ℂ_[p]) (n : ℕ) : lamC lam (n : ℂ) = n := by
  have h : (n : ℂ) ∈ Qbar := natCast_mem _ n
  simp only [lamC, dif_pos h]
  rw [← map_natCast lam n]; rfl

theorem iteratedDeriv_scale (G : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => G (c * z)) = fun z => c ^ n * iteratedDeriv n G (c * z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    funext z
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field, deriv_comp_mul_left, iteratedDeriv_succ,
      smul_eq_mul, pow_succ, mul_assoc]

theorem deriv_mem_iff (G : ℂ → ℂ) (n : ℕ) : iteratedDeriv n G 0 ∈ Qbar ↔ coef1 G n ∈ Qbar := by
  have h : ((n.factorial : ℕ) : ℂ) ∈ Qbar := natCast_mem _ _
  have h0 : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  constructor
  · intro hG
    exact div_mem hG h
  · intro hG
    have := mul_mem h hG
    rwa [coef1, mul_div_cancel₀ _ h0] at this

theorem jet_atU (g : GL3Theta.G1 p) (hOk : g.Ok) (G : ℂ → ℂ) (n : ℕ) (hG : iteratedDeriv n G 0 ∈ Qbar) :
    (n.factorial : ℂ_[p]) * coeff n (subst g.ex (g.atU G) : PowerSeries ℂ_[p]) =
      ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ n * lamC g.lam (iteratedDeriv n G 0) := by
  have hex : HasSubst g.ex := HasSubst.of_constantCoeff_zero' hOk.2.2.1
  have harg := HasSubst.of_constantCoeff_zero' (constantCoeff_arg g)
  have e : (subst g.ex (g.atU G) : PowerSeries ℂ_[p]) =
      rescale ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) (GL3Theta.ser1 g.lam G) := by
    rw [GL3Theta.G1.atU, subst_comp_subst_apply harg hex, rescale_eq_subst]
    congr 1
    rw [← Algebra.smul_def, subst_smul hex, hOk.2.2.2]
  have h : ((n.factorial : ℕ) : ℂ) ∈ Qbar := natCast_mem _ _
  have h0 : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [e, coeff_rescale, GL3Theta.ser1, coeff_mk, mul_left_comm, ← lamC_natCast g.lam,
    ← lamC_mul _ h (div_mem hG h), mul_div_cancel₀ _ h0]

theorem norm_jet_atU (g : GL3Theta.G1 p) (hOk : g.Ok) (hu : ‖((g.C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1)
    (G : ℂ → ℂ) (n : ℕ) (hG : iteratedDeriv n G 0 ∈ Qbar) :
    ‖(n.factorial : ℂ_[p]) * coeff n (subst g.ex (g.atU G) : PowerSeries ℂ_[p])‖ =
      ‖lamC g.lam (iteratedDeriv n G 0)‖ := by
  rw [jet_atU g hOk G n hG, norm_mul, norm_pow, Units.val_inv_eq_inv_val, norm_inv, hu]
  simp

theorem norm_jet_atU_scale (g : GL3Theta.G1 p) (hOk : g.Ok) (hu : ‖((g.C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1)
    (G : ℂ → ℂ) (N n : ℕ) (hG : iteratedDeriv n G 0 ∈ Qbar) :
    ‖(n.factorial : ℂ_[p]) * coeff n (subst g.ex (g.atU fun z => G ((N : ℂ) * z)) : PowerSeries ℂ_[p])‖ =
      ‖(N : ℂ_[p])‖ ^ n * ‖lamC g.lam (iteratedDeriv n G 0)‖ := by
  have hN : ((N : ℂ)) ^ n ∈ Qbar := pow_mem (natCast_mem _ _) _
  have e : iteratedDeriv n (fun z => G ((N : ℂ) * z)) 0 = (N : ℂ) ^ n * iteratedDeriv n G 0 := by
    rw [iteratedDeriv_scale]; simp
  rw [norm_jet_atU g hOk hu _ n (e ▸ mul_mem hN hG), e, lamC_mul _ hN hG, ← Nat.cast_pow,
    lamC_natCast, norm_mul, Nat.cast_pow, norm_pow]

theorem expPS_logOf (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 1) : expPS (logOf F) = F := by
  have h0 : constantCoeff (logOf F) = 0 := constantCoeff_logOf hF
  have h1 : constantCoeff (-logOf F) = 0 := by simp [h0]
  have e : expPS (logOf F) * expPS (-logOf F) = 1 := by
    refine derivative.ext ?_ ?_
    · rw [Derivation.leibniz, GlobalTheory.ExpJets.derivative_expPS _ h0,
        GlobalTheory.ExpJets.derivative_expPS _ h1, map_neg, derivative_one]
      simp only [smul_eq_mul]
      ring
    · simp [constantCoeff_expPS]
  have e2 := exp_neg_log_mul F hF
  linear_combination F * e - expPS (logOf F) * e2

theorem subst_expPS {a F : PowerSeries ℂ_[p]} (ha : constantCoeff a = 0) (hF : constantCoeff F = 0) :
    (subst a (expPS F) : PowerSeries ℂ_[p]) = expPS (subst a F) := by
  rw [GlobalTheory.ExpJets.expPS_eq_subst F hF,
    GlobalTheory.ExpJets.expPS_eq_subst _ (by rw [constantCoeff_subst' ha, hF]),
    subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hF) (HasSubst.of_constantCoeff_zero' ha)]

theorem deriv_translate_mem (D : D7) (hI : Inp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (hCrv : Crv D cc δ) (t0 : ℂ) (hT : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (y : ℂ) (N : ℕ) (hN : 0 < N)
    (hy : (N : ℂ) * y ∈ lamOf D cc δ) (n : ℕ) :
    iteratedDeriv n (U1 (lamOf D cc δ) y (GL3Theta.th0 (lamOf D cc δ) t0)) 0 ∈ Qbar := by
  set L := lamOf D cc δ with hL
  obtain ⟨⟨-, hd, -, hq⟩, -⟩ :=
    GlobalTheory.OddTheta.sgStar_laws L (GlobalTheory.CurveLattice.lattice_of_curve D hI.g1 cc δ hCrv).1
  have halg : ∀ x, InRationalLattice L x → ∀ n, coef1 (U1 L x (sgStar L)) n ∈ Qbar := (hI.use1 cc δ hCrv).1
  have hne : ∃ z, sgStar L z ≠ 0 := by
    by_contra h
    push Not at h
    rw [show sgStar L = fun _ => 0 from funext h] at hd
    simp at hd
  have h2 : ((2 : ℕ) : ℂ) * t0 ∈ L := by simpa using hT.1
  set c := U1 L t0 (sgStar L) 0 with hcdef
  have hcQ : c ∈ Qbar := by
    have := halg t0 ⟨2, two_pos, h2⟩ 0
    simpa [coef1] using this
  have hth : GL3Theta.th0 L t0 = fun z => c⁻¹ * U1 L t0 (sgStar L) z := by
    funext z
    rw [GL3Theta.th0, div_eq_inv_mul]
  have hU : U1 L y (GL3Theta.th0 L t0) =
      fun z => (c⁻¹ * cocy L y t0) * U1 L (y + t0) (sgStar L) z := by
    rw [hth, thetaTranslation_const_mul]
    funext z
    rw [thetaTranslation_comp_eq_cocycle_mul, mul_assoc]
  have hr := cocy_root hne hq hy h2
  have hsum : ((N * 2 : ℕ) : ℂ) * (y + t0) ∈ L := by
    have := add_mem (nsmul_mem hy 2) (nsmul_mem h2 N)
    convert this using 1
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [hU, iteratedDeriv_const_mul_field]
  exact mul_mem (mul_mem (inv_mem hcQ) (root_mem (by positivity) hr))
    ((deriv_mem_iff _ n).2 (halg _ ⟨N * 2, by positivity, hsum⟩ n))

theorem norm_natCast_of_coprime {N : ℕ} (h : ¬ p ∣ N) : ‖(N : ℂ_[p])‖ = 1 := by
  have e : (N : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (N : ℚ_[p]) := (map_natCast _ _).symm
  rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 h

theorem jet_translate_le : ∀ (D : D7), Inp D → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → Nat.Coprime (Ideal.absNorm cc) p → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (y : ℂ) (Nn : ℕ), 0 < Nn → (Nn : ℂ) * y ∈ (lamOf D cc δ) → (p ∣ Nn → SplitIn D p) → ∀ n : ℕ, iteratedDeriv n (U1 (lamOf D cc δ) y (GL3Theta.th0 (lamOf D cc δ) t0)) 0 ∈ Qbar ∧ ‖lamC lam (iteratedDeriv n (U1 (lamOf D cc δ) y (GL3Theta.th0 (lamOf D cc δ) t0)) 0)‖ ≤ (‖(Nn : ℂ_[p])‖⁻¹) ^ n * (if p = D.host.d then (p : ℝ) ^ ((n : ℝ) / 4) else 1) := by
  intro D hI p hp lam cc δ hCrv hcop t0 hT y N hN hy hsp n
  have halg := deriv_translate_mem D hI cc δ hCrv t0 hT y N hN hy
  have halg0 : ∀ m, iteratedDeriv m (GL3Theta.th0 (lamOf D cc δ) t0) 0 ∈ Qbar := fun m =>
    (deriv_mem_iff _ m).2 ((hI.use1 cc δ hCrv).2.1 t0 hT m)
  refine ⟨halg n, ?_⟩
  obtain ⟨g, hAt, rfl, hu⟩ := GlobalTheory.GenusOneDatum.exists_genusOne_datum D hI.model p lam cc δ hCrv hcop
  have hL : g.abelian₂ = lamOf D cc δ := hAt.2.2.2.1
  have hOk := hAt.2.2.2.2
  rw [← hL] at hT hy halg halg0 ⊢
  have hex0 : constantCoeff g.ex = 0 := hOk.2.2.1
  have hex : HasSubst g.ex := HasSubst.of_constantCoeff_zero' hex0
  have hD := (GlobalTheory.IntDLog.int_dlog p g hOk).1
  obtain ⟨hodd, hsplit⟩ := theta_param_integral D hI p cc δ g hAt t0 hT
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_le
  have hfac : (1 : ℝ) ≤ (if p = D.host.d then (p : ℝ) ^ ((n : ℝ) / 4) else 1) := by
    split_ifs
    · exact Real.one_le_rpow hp1 (by positivity)
    · exact le_rfl
  by_cases hpN : p ∣ N
  · obtain ⟨h, hh, e⟩ := GlobalTheory.PullBackSplit.pull_back_split D hI p cc δ g hAt t0 hT y N hN hy hpN (hsp hpN)
    have h0 := (integral_iff _).1 (hsplit (hsp hpN)).1
    have hN1 : ‖(N : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
    have hN0 : 0 < ‖(N : ℂ_[p])‖ := norm_pos_iff.2 (by exact_mod_cast hN.ne')
    have key := norm_jet_atU_scale g hOk hu _ N n (halg n)
    rw [e, subst_mul hex] at key
    have hle := GlobalTheory.ExpJets.norm_jet_mul_le (subst g.ex h)
      (subst g.ex (g.atU fun z => GL3Theta.th0 g.abelian₂ t0 ((N : ℂ) * z))) n 1 zero_le_one fun i j _ => by
        refine mul_le_one₀ (hD h hh i) (norm_nonneg _) ?_
        rw [norm_jet_atU_scale g hOk hu _ N j (halg0 j), ← norm_jet_atU g hOk hu _ j (halg0 j)]
        exact mul_le_one₀ (pow_le_one₀ hN0.le hN1) (norm_nonneg _) (hD _ h0 j)
    rw [key] at hle
    refine le_trans ?_ (le_mul_of_one_le_right (by positivity) hfac)
    rw [inv_pow, ← mul_one (_ ^ n)⁻¹, le_inv_mul_iff₀ (by positivity)]
    exact hle
  · have hc : Nat.Coprime N p := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpN).symm
    rw [norm_natCast_of_coprime hpN, inv_one, one_pow, one_mul, ← norm_jet_atU g hOk hu _ n (halg n)]
    by_cases hp2 : p = 2
    · exact (hD _ ((integral_iff _).1 ((hsplit (Or.inl hp2)).2 y N hc hy)) n).trans hfac
    have hf := (integral_iff _).1 ((hodd hp2).2 y N hc hy)
    obtain ⟨⟨-, hd, -, -⟩, -⟩ :=
      GlobalTheory.OddTheta.sgStar_laws g.abelian₂ (hL ▸ (GlobalTheory.CurveLattice.lattice_of_curve D hI.g1 cc δ hCrv).1)
    have he := constantCoeff_ePhi1 g hOk.2.1 hd
    set E := ePhi1 g.lam g.abelian₂ g.C g.wq with hE
    set f := E⁻¹ * g.atU (U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0)) with hfdef
    have hinv : E * E⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [he]; exact one_ne_zero)
    have hph : -g.ph = logOf E := by
      rw [GL3Theta.G1.ph, neg_neg]
      exact logMv_eq E he
    have hph0 : constantCoeff g.ph = 0 := by
      have := constantCoeff_logOf he
      rw [← hph] at this
      simpa using this
    have e : (subst g.ex (g.atU (U1 g.abelian₂ y (GL3Theta.th0 g.abelian₂ t0))) : PowerSeries ℂ_[p]) =
        expPS (-(subst g.ex g.ph)) * subst g.ex f := by
      have e1 : (-(subst g.ex g.ph) : PowerSeries ℂ_[p]) = subst g.ex (logOf E) := by
        rw [← hph, ← coe_substAlgHom hex, map_neg]
      rw [e1, ← subst_expPS hex0 (constantCoeff_logOf he), expPS_logOf E he, ← subst_mul hex,
        hfdef, ← mul_assoc, hinv, one_mul]
    obtain ⟨j1, -, j2, j3⟩ := hI.jets p cc δ g hAt hp2
    have hmain := fun (s : ℝ) (hs : 1 ≤ s) h2 =>
      GlobalTheory.ExpJets.norm_jet_exp_neg_mul_le p (subst g.ex g.ph) s hs
        (by rw [constantCoeff_subst' hex0, hph0]) j1 h2 (subst g.ex f) (hD f hf) n
    have hj : g.jetPh 2 = 2 * coeff 2 (subst g.ex g.ph : PowerSeries ℂ_[p]) := by
      simp [GL3Theta.G1.jetPh]
    rw [e]
    split_ifs with hd'
    · have := hmain ((p : ℝ) ^ ((1 : ℝ) / 4)) (Real.one_le_rpow hp1 (by positivity)) (by
        rw [← hj, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        convert j3 hd' using 2
        norm_num)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at this
      convert this using 2
      ring
    · have := hmain 1 le_rfl (by rw [← hj, one_pow]; exact j2 hd')
      rwa [one_pow] at this

end GlobalTheory.TorsionJets
end

