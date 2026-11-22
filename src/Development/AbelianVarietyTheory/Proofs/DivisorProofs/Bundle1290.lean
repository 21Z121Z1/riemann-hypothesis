import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralEqOfLineBundleIso
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
namespace GlobalTheory

theorem chernInt_indep_of_iso : ∀ (Y : Var ℂ) (L A : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L) (ψ : Weight Y.str (RingHom.id ℂ) A), LBIso L A → φ.IsCInf → ψ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = Weight.chernInt ψ Y.dim Set.univ (fun _ => 1) := by
  intro Y L A φ ψ hLA hφ hψ
  obtain ⟨w, hw⟩ := hLA
  obtain ⟨h1, h2⟩ := GlobalTheory.T.chernMass_lineBundleWeightOfIso Y L A φ ψ.isLB w hw hφ
  rw [← h2]
  exact GlobalTheory.T.chernIntegral_top_independent_of_smooth_weight Y A _ ψ h1 hψ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTwoDdcExtTraceStatement
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_two_ddc_ext_trace : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) (hc : ∀ ξ η, chernOne H z ξ η = chernOne (gramS H) z ξ η + chernOne (gramQ H) z ξ η) (hd : ∀ ξ₁ η₁ ξ₂ η₂, ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ = chTwo (gramS H) z ξ₁ η₁ ξ₂ η₂ + chTwo (gramQ H) z ξ₁ η₁ ξ₂ η₂ - chTwo H z ξ₁ η₁ ξ₂ η₂) (ξ₁ η₁ ξ₂ η₂ : V), ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ = chernTwo H z ξ₁ η₁ ξ₂ η₂ - wedge (chernOne (gramS H) z) (chernOne (gramQ H) z) ξ₁ η₁ ξ₂ η₂ := by
  first | exact @GlobalTheory.ddcForm_extTrace_eq_rank_two | exact GlobalTheory.ddcForm_extTrace_eq_rank_two | (intros; apply GlobalTheory.ddcForm_extTrace_eq_rank_two <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiDeltaUConjLongSimpleReflectionUnitaryStatement
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chiDeltaU_conj_longSimpleReflection_unitary : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n →
    ∀ (y : GU σ n), IsWeylRep (simpleU k) (y : GL (Fin n) L) → ∀ (α : Fin (n / 2) → ℂˣ) (t : GU σ n),
    (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
    chiDeltaU q (fun i => (α i : ℂ)) (y⁻¹ * t * y) *
        (q : ℂ) ^ (-2 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) =
      chiDeltaU q (fun i => (actU k α i : ℂ)) t := by
  first | exact @GlobalTheory.GKUnitary.chiDeltaU_conj_simpleU_long | exact GlobalTheory.GKUnitary.chiDeltaU_conj_simpleU_long | (intros; apply GlobalTheory.GKUnitary.chiDeltaU_conj_simpleU_long <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionIdeleConjIdeleMapMaxRealSubfield
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ConjIdeleReal

theorem adeleMap_eq_baseChange (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap K L = GroundTheory.Global.AdeleBaseChange.adeleMap K L := rfl

theorem ideleConj_ideleMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b := by
  intro E _ _ _ b
  let alg : Algebra E E := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  have tw : @IsScalarTower (maximalRealSubfield E) E E _ (@Algebra.toSMul _ _ _ _ alg) _ :=
    @IsScalarTower.of_algebraMap_eq (maximalRealSubfield E) E E _ _ _ _ alg _ fun x =>
      ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).commutes x).symm
  have h := @GroundTheory.Global.AdeleBaseChange.adeleMap_adeleMap (maximalRealSubfield E) E E _ _ _ _ _ _ _ alg _ tw
    (b : AdeleRing _ _)
  rw [← adeleMap_eq_baseChange, ← adeleMap_eq_baseChange] at h
  apply Units.ext
  exact h

end GlobalTheory.ConjIdeleReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionIdeleConjMemFiniteUnitIdeles
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjUnit

theorem ideleConj_mem_unitIdl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (y : Neutral.B1.Ideles E), y ∈ GlobalTheory.Mem.Chr.unitIdl E →
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y ∈ GlobalTheory.Mem.Chr.unitIdl E := by
  intro E _ _ _ y hy
  letI : Algebra E E := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  have key : ∀ z : Neutral.B1.Ideles E, z ∈ GlobalTheory.Mem.Chr.unitIdl E → ∀ w : HeightOneSpectrum (𝓞 E),
      Valued.v (((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E z : AdeleRing (𝓞 E) E)).2 w) ≤ 1 := by
    intro z hz w
    have hz' : ∀ v : HeightOneSpectrum (𝓞 E), ((z : AdeleRing (𝓞 E) E)).2 v ∈ v.adicCompletionIntegers E :=
      fun v => (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 E) (K := E) (v := v)).mpr (hz v).le
    exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_mapsTo E E w (hz' _)
  intro w
  have h1 := key y hy w
  have h2 := key y⁻¹ (inv_mem hy) w
  have e : ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y : AdeleRing (𝓞 E) E)).2 w *
      ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y⁻¹ : AdeleRing (𝓞 E) E)).2 w = 1 := by
    rw [map_inv]
    exact congrArg (fun a : AdeleRing (𝓞 E) E => a.2 w) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E y).mul_inv
  have e' := congrArg Valued.v e
  rw [map_mul, map_one] at e'
  exact eq_one_of_one_le_mul_left h1 h2 e'.ge

end GlobalTheory.ConjUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompLinearAutLocallyConstantCompactSupportMatrixStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comp_linearAut_locallyConstant_compactSupport_matrix : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) (L : Matrix (Fin a) (Fin b) (w.adicCompletion E) →ₗ[w.adicCompletion E] Matrix (Fin a) (Fin b) (w.adicCompletion E)) (φ : Matrix (Fin a) (Fin b) (w.adicCompletion E) → ℂ), LinearMap.det L ≠ 0 → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (x + y) = φ x) → HasCompactSupport φ → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (L (x + y)) = φ (L x)) ∧ HasCompactSupport (fun x => φ (L x)) ∧ LocallyCompactSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := by
  first | exact @GlobalTheory.LeviDesc.comp_linearAut_smooth_compact | exact GlobalTheory.LeviDesc.comp_linearAut_smooth_compact | (intros; apply GlobalTheory.LeviDesc.comp_linearAut_smooth_compact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactPartCentralizerLeConjIntegralUnitary
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CptCent

theorem mem_GLint_of_entries' {K : Type} [Field K] {n : ℕ} (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ a b, g.val a b ∈ O) (h2 : ∀ a b, (g⁻¹).val a b ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem entry_mem_of_mem_GLint' {K : Type} [Field K] {n : ℕ} (O : Subring K) {g : GL (Fin n) K}
    (hg : g ∈ Formalism.UG.GLint (Fin n) O) (a b : Fin n) : g.val a b ∈ O := by
  obtain ⟨h, rfl⟩ := hg
  exact (h.val a b).2

theorem conj_zpow' {G : Type} [Group G] (g t : G) (k : ℤ) : (g⁻¹ * t * g) ^ k = g⁻¹ * t ^ k * g := by
  have := map_zpow (MulAut.conj g⁻¹) t k
  simpa [MulAut.conj_apply] using this.symm

theorem cptPart_le_conj_KL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (P₀ : (w.adicCompletionIntegers E)[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∀ g : UL n w, g⁻¹ * γ * g ∈ KL n w →
    cptPart (twCent (MonoidHom.id (UL n w)) γ) ≤ (KL n w).map (MulAut.conj g).toMonoidHom := by
  intro E _ _ _ n w P₀ hP₀ γ hγ g hg
  have hgK : ((g⁻¹ * γ * g : UL n w) : GLw n w) ∈ GlobalTheory.LFun.KGL w n := (Subgroup.mem_subgroupOf).1 hg
  set A : Matrix (Fin n) (Fin n) (w.adicCompletion E) := ((g⁻¹ * γ * g : UL n w) : GLw n w).val with hAdef
  have hA : ∀ i j, A i j ∈ w.adicCompletionIntegers E := fun i j => entry_mem_of_mem_GLint' _ hgK i j
  have hAc : A.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
    rw [← hγ, hAdef]
    have : ((g⁻¹ * γ * g : UL n w) : GLw n w).val = ((g : GLw n w)⁻¹).val * (γ : GLw n w).val * (g : GLw n w).val := by
      simp
    rw [this, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj' (g : GLw n w) ((γ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
  show Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  rintro t ⟨ht, hcpt⟩
  have htγ : t * γ = γ * t := by simpa [twCent] using ht
  obtain ⟨B, hB⟩ := GlobalTheory.T.conj_zpowers_entries_valued_bounded_of_compact_closure E n w t g hcpt
  set x : UL n w := g⁻¹ * t * g with hx
  have hxA : x * (g⁻¹ * γ * g) = (g⁻¹ * γ * g) * x := by
    simp only [hx, mul_assoc, mul_inv_cancel_left]
    rw [← mul_assoc t, htγ, mul_assoc]
  have val_pow : ∀ (y : UL n w) (k : ℕ), ((y ^ k : UL n w) : GLw n w).val = ((y : GLw n w).val) ^ k := by
    intro y k; simp
  have entries : ∀ (y : UL n w), y * (g⁻¹ * γ * g) = (g⁻¹ * γ * g) * y →
      (∀ k : ℕ, ∃ m : ℤ, y ^ k = g⁻¹ * t ^ m * g) → ∀ i j, (y : GLw n w).val i j ∈ w.adicCompletionIntegers E := by
    intro y hy hpow
    refine GlobalTheory.T.mem_integral_of_commute_separable_reduction E w n P₀ hP₀ A _ hA hAc ?_ ⟨B, fun k i j => ?_⟩
    · have := congrArg (fun z : UL n w => (z : GLw n w).val) hy
      simpa [Commute, SemiconjBy, hAdef] using this
    · obtain ⟨m, hm⟩ := hpow k
      rw [← val_pow, hm]
      exact hB m i j
  have hxO := entries x hxA (fun k => ⟨k, by rw [hx, ← conj_zpow']; simp⟩)
  have hxiO := entries x⁻¹ (by
      have := congrArg (fun z => x⁻¹ * z * x⁻¹) hxA
      simpa [mul_assoc] using this.symm)
    (fun k => ⟨-(k : ℤ), by rw [hx, ← conj_zpow', _root_.zpow_neg, zpow_natCast, inv_pow]⟩)
  refine ⟨x, ?_, ?_⟩
  · show x ∈ KL n w
    refine (Subgroup.mem_subgroupOf).2 (mem_GLint_of_entries' _ _ hxO fun a b => ?_)
    have := hxiO a b
    simpa using this
  · simp [hx, MulAut.conj_apply, mul_assoc]

end GlobalTheory.CptCent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjAverageUnipotentLocallyConstantCompactSupporStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjAverage_unipotent_locallyConstant_compactSupport : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw b w, (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) f (blk h w m (x + y)) = GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) f (blk h w m x)) ∧ HasCompactSupport (fun X => GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) f (blk h w m X)) := by
  first | exact @GlobalTheory.LeviDesc.UnipMean.cavg_blk_locConst_compactSupport | exact GlobalTheory.LeviDesc.UnipMean.cavg_blk_locConst_compactSupport | (intros; apply GlobalTheory.LeviDesc.UnipMean.cavg_blk_locConst_compactSupport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemPrincipalCongruenceSubgroupIffStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_mem_principalCongruenceSubgroup_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n m : ℕ) (h k : GLw n w), k ∈ GlobalTheory.LFun.KGL w n → (k⁻¹ * h * k ∈ congSet w n m ↔ h ∈ congSet w n m) := by
  first | exact @GlobalTheory.KapOrb.conj_mem_congSet_iff | exact GlobalTheory.KapOrb.conj_mem_congSet_iff | (intros; apply GlobalTheory.KapOrb.conj_mem_congSet_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjQuotNsUnitsEqOne
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ConsEta
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele

theorem under_under_of_compat {F K L : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra F K] [Algebra F L] [alg : Algebra K L]
    (hc : ∀ x : F, algebraMap K L (algebraMap F K x) = algebraMap F L x) (w : HeightOneSpectrum (𝓞 L)) :
    (w.under (𝓞 K)).under (𝓞 F) = w.under (𝓞 F) := by
  ext x
  simp only [HeightOneSpectrum.under_asIdeal, Ideal.mem_under]
  have : algebraMap (𝓞 K) (𝓞 L) (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 L) x := by
    apply RingOfIntegers.ext
    exact hc (x : F)
  rw [this]

theorem finEval_ideleMap_localIdele {F K L : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra F K] [Algebra F L] [alg : Algebra K L]
    (hc : ∀ x : F, algebraMap K L (algebraMap F K x) = algebraMap F L x) (w : HeightOneSpectrum (𝓞 L))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.under (𝓞 F) ≠ w.under (𝓞 F)) (a : (v.adicCompletion K)ˣ) :
    Units.map (GlobalTheory.IdeleNormChar.finEval w) (ideleMap K L (Neutral.B1.localIdele K v a)) = 1 := by
  have hne : w.under (𝓞 K) ≠ v := fun h => hv (h ▸ under_under_of_compat hc w)
  apply Units.ext
  show finiteCompletionMap K L w ((Neutral.B1.localIdele K v a : AdeleRing (𝓞 K) K).2 (w.under (𝓞 K))) = 1
  rw [(Neutral.B1.localIdele_isSupportedAt K v a).2 _ hne, map_one]

theorem isSplitAt_of_under_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {v w : HeightOneSpectrum (𝓞 E)}
    (hw : GlobalTheory.UnitaryBC.IsSplitAt w)
    (h : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) :
    GlobalTheory.UnitaryBC.IsSplitAt v := by
  obtain ⟨u, hu, hu'⟩ := hw
  by_cases hvw : v = w
  · subst hvw; exact ⟨u, hu, hu'⟩
  · exact ⟨w, Ne.symm hvw, h.symm⟩

theorem conjQuot_nsUnits_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)),
    GlobalTheory.UnitaryBC.IsSplitAt w → ∀ u ∈ GlobalTheory.MuExist.nsUnits E, GlobalTheory.ConsEta.conjQuot E w u = 1 := by
  intro E _ _ _ w hw u hu
  have key : GlobalTheory.MuExist.nsUnits E ≤ (conjQuot E w).ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨w', a, hw', -, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have hne : w' ≠ w := fun h => hw' (h ▸ hw)
    have hunder : w'.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) :=
      fun h => hw' (isSplitAt_of_under_eq hw h)
    have h1 : Units.map (GlobalTheory.IdeleNormChar.finEval w) (Neutral.B1.localIdele E w' a) = 1 :=
      Units.ext ((Neutral.B1.localIdele_isSupportedAt E w' a).2 w hne.symm)
    have h2 : Units.map (GlobalTheory.IdeleNormChar.finEval w)
        (ideleConj (maximalRealSubfield E) E (Neutral.B1.localIdele E w' a)) = 1 :=
      finEval_ideleMap_localIdele (F := maximalRealSubfield E)
        (alg := (conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra)
        (fun x => (conj (maximalRealSubfield E) E).commutes x) w w' hunder a
    simp only [conjQuot, MonoidHom.comp_apply, MonoidHom.div_apply, MonoidHom.id_apply, _root_.map_div, h1, h2, div_one]
  exact key hu

end GlobalTheory.ConsEta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionBlocksHermitianFrameStatement
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connection_blocks_hermitian_frame : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U), ConnBlocks H z (fun η => -secondFormAdj H z η) (secondForm H z) := by
  first | exact @GlobalTheory.SubQuotConn.connBlocks_secondForm | exact GlobalTheory.SubQuotConn.connBlocks_secondForm | (intros; apply GlobalTheory.SubQuotConn.connBlocks_secondForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffConstantTermCocompactSmoothParameterFami
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology

noncomputable section

namespace GlobalTheory.Cusp.SmoothParam

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ N : Subgroup G} [DiscreteTopology Γ] [LocallyCompactSpace N]

omit [SecondCountableTopology G] [DiscreteTopology Γ] [LocallyCompactSpace N] in

theorem aestronglyMeasurable_out {E : Type} [NormedAddCommGroup E] [SecondCountableTopology E]
    {Φ : G → E} (hΦ : Continuous Φ) (hinv : ∀ γ ∈ Γ, ∀ x, Φ (γ * x) = Φ x) (g : G)
    (μ : Measure (Quot (Γ.subgroupOf N))) :
    AEStronglyMeasurable (fun q : Quot (Γ.subgroupOf N) => Φ ((q.out : N) * g)) μ := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have hl : LeftInv (Γ.subgroupOf N) (fun n : N => Φ (n * g)) := fun γ hγ n => by
    simp only [Subgroup.coe_mul, mul_assoc]; exact hinv _ hγ _
  have hm : Measurable (fun n : N => Φ (n * g)) :=
    (hΦ.comp ((continuous_subtype_val).mul continuous_const)).measurable
  have hq : Measurable (descend (Γ.subgroupOf N) (fun n : N => Φ (n * g))) := by
    refine measurable_from_quotient.2 ?_
    have e : (descend (Γ.subgroupOf N) (fun n : N => Φ (n * g))) ∘ Quotient.mk'' = fun n : N => Φ (n * g) :=
      hl.lift_descend
    rw [e]; exact hm
  exact hq.aestronglyMeasurable

omit [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ] [LocallyCompactSpace N] in

theorem exists_bound {T E : Type} [TopologicalSpace T] [NormedAddCommGroup E] (hc : Cocompact Γ N)
    {Ψ : G → T → E} (hΨ : Continuous fun p : G × T => Ψ p.1 p.2) (hinv : ∀ γ ∈ Γ, ∀ x t, Ψ (γ * x) t = Ψ x t)
    (g : G) {S : Set T} (hS : IsCompact S) : ∃ C, ∀ (n : N) t, t ∈ S → ‖Ψ (n * g) t‖ ≤ C := by
  obtain ⟨K, hK, hs⟩ := hc
  obtain ⟨C, hC⟩ := (hK.prod hS).exists_bound_of_continuousOn (f := fun p : N × T => Ψ (p.1 * g) p.2)
    (hΨ.comp (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd)).continuousOn
  refine ⟨C, fun n t ht => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := hs n
  have e : Ψ (((γ * n : N) : G) * g) t = Ψ (n * g) t := by
    simp only [Subgroup.coe_mul, mul_assoc]; exact hinv _ hγ _ _
  exact e ▸ hC (γ * n, t) ⟨hk, ht⟩

theorem hasFDerivAt_param {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hc : Cocompact Γ N) (H : G → (Fin k → ℝ) → E)
    (hinv : ∀ γ ∈ Γ, ∀ x t, H (γ * x) t = H x t) (hd : ∀ x, Differentiable ℝ (H x))
    (h0 : Continuous fun p : G × (Fin k → ℝ) => H p.1 p.2)
    (h1 : Continuous fun p : G × (Fin k → ℝ) => fderiv ℝ (H p.1) p.2) (g : G) (t₀ : Fin k → ℝ) :
    HasFDerivAt (fun t => ∫ q, H ((q.out : N) * g) t ∂probMeasure Γ N)
      (∫ q, fderiv ℝ (H ((q.out : N) * g)) t₀ ∂probMeasure Γ N) t₀ := by
  have := hc.isProbabilityMeasure
  have hinv' : ∀ γ ∈ Γ, ∀ x t, fderiv ℝ (H (γ * x)) t = fderiv ℝ (H x) t := fun γ hγ x t => by
    rw [show H (γ * x) = H x from funext (hinv γ hγ x)]
  obtain ⟨C, hC⟩ := exists_bound (Ψ := fun x t => fderiv ℝ (H x) t) hc h1 hinv' g (isCompact_closedBall t₀ 1)
  obtain ⟨C0, hC0⟩ := exists_bound (Ψ := H) hc h0 hinv g (isCompact_closedBall t₀ 1)
  have hm : ∀ t, AEStronglyMeasurable (fun q : Quot (Γ.subgroupOf N) => H ((q.out : N) * g) t) (probMeasure Γ N) :=
    fun t => aestronglyMeasurable_out (Φ := fun x => H x t) (h0.comp (continuous_id.prodMk continuous_const))
      (fun γ hγ x => hinv γ hγ x t) g _
  have hm' : AEStronglyMeasurable (fun q : Quot (Γ.subgroupOf N) => fderiv ℝ (H ((q.out : N) * g)) t₀)
      (probMeasure Γ N) :=
    aestronglyMeasurable_out (Φ := fun x => fderiv ℝ (H x) t₀) (h1.comp (continuous_id.prodMk continuous_const))
      (fun γ hγ x => hinv' γ hγ x t₀) g _
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (Metric.ball_mem_nhds t₀ one_pos) (.of_forall hm)
    (Integrable.of_bound (hm t₀) C0 (.of_forall fun q => hC0 _ t₀ (Metric.mem_closedBall_self zero_le_one))) hm'
    (.of_forall fun q t ht => hC _ t (Metric.ball_subset_closedBall ht)) (integrable_const C)
    (.of_forall fun q t _ => (hd _ t).hasFDerivAt)

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in

theorem iteratedFDeriv_fderiv_eq {k : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin k → ℝ) → E) (m : ℕ) (t : Fin k → ℝ) :
    iteratedFDeriv ℝ m (fderiv ℝ f) t =
      (continuousMultilinearCurryRightEquiv' ℝ m (Fin k → ℝ) E) (iteratedFDeriv ℝ (m + 1) f t) := by
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in

theorem continuous_of_iteratedFDeriv_zero {X : Type} [TopologicalSpace X] {k : ℕ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : X → (Fin k → ℝ) → E}
    (h : Continuous fun p : X × (Fin k → ℝ) => iteratedFDeriv ℝ 0 (H p.1) p.2) :
    Continuous fun p : X × (Fin k → ℝ) => H p.1 p.2 := by
  have e : (fun p : X × (Fin k → ℝ) => H p.1 p.2) =
      fun p => continuousMultilinearCurryFin0 ℝ (Fin k → ℝ) E (iteratedFDeriv ℝ 0 (H p.1) p.2) := by
    funext p; simp [continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply]
  rw [e]; exact (continuousMultilinearCurryFin0 ℝ (Fin k → ℝ) E).continuous.comp h

theorem contDiff_param (hc : Cocompact Γ N) (g : G) {k : ℕ} (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (H : G → (Fin k → ℝ) → E),
      (∀ γ ∈ Γ, ∀ x t, H (γ * x) t = H x t) → (∀ x, ContDiff ℝ ∞ (H x)) →
      (∀ m : ℕ, Continuous fun p : G × (Fin k → ℝ) => iteratedFDeriv ℝ m (H p.1) p.2) →
      ContDiff ℝ n fun t => ∫ q, H ((q.out : N) * g) t ∂probMeasure Γ N := by
  induction n with
  | zero =>
    intro E _ _ _ H hinv hs hm
    have h1 : Continuous fun p : G × (Fin k → ℝ) => fderiv ℝ (H p.1) p.2 := by
      refine continuous_of_iteratedFDeriv_zero (H := fun x => fderiv ℝ (H x)) ?_
      simp only [iteratedFDeriv_fderiv_eq]
      exact (continuousMultilinearCurryRightEquiv' ℝ 0 (Fin k → ℝ) E).continuous.comp (hm 1)
    refine contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => ?_)
    exact (hasFDerivAt_param hc H hinv (fun x => (hs x).differentiable (by simp))
      (continuous_of_iteratedFDeriv_zero (hm 0)) h1 g t).continuousAt
  | succ n ih =>
    intro E _ _ _ H hinv hs hm
    have hm' : ∀ m : ℕ, Continuous fun p : G × (Fin k → ℝ) => iteratedFDeriv ℝ m (fderiv ℝ (H p.1)) p.2 := by
      intro m
      simp only [iteratedFDeriv_fderiv_eq]
      exact (continuousMultilinearCurryRightEquiv' ℝ m (Fin k → ℝ) E).continuous.comp (hm (m + 1))
    have hinv' : ∀ γ ∈ Γ, ∀ x t, fderiv ℝ (H (γ * x)) t = fderiv ℝ (H x) t := fun γ hγ x t => by
      rw [show H (γ * x) = H x from funext (hinv γ hγ x)]
    refine contDiff_succ_iff_hasFDerivAt.2 ⟨_, ih (fun x => fderiv ℝ (H x)) hinv'
      (fun x => (contDiff_infty_iff_fderiv.1 (hs x)).2) hm', fun t => ?_⟩
    exact hasFDerivAt_param hc H hinv (fun x => (contDiff_infty_iff_fderiv.1 (hs x)).1)
      (continuous_of_iteratedFDeriv_zero (hm 0))
      (continuous_of_iteratedFDeriv_zero (H := fun x => fderiv ℝ (H x)) (hm' 0)) g t

end GlobalTheory.Cusp.SmoothParam

theorem GlobalTheory.Cusp.contDiff_constTermOn_param : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ N : Subgroup G} [DiscreteTopology Γ]
    [LocallyCompactSpace N], GlobalTheory.Cusp.Cocompact Γ N → ∀ {k : ℕ} (F : G → (Fin k → ℝ) → ℂ),
    (∀ γ ∈ Γ, ∀ x t, F (γ * x) t = F x t) → (∀ x, ContDiff ℝ ∞ (F x)) →
    (∀ m : ℕ, Continuous fun p : G × (Fin k → ℝ) => iteratedFDeriv ℝ m (F p.1) p.2) →
    ∀ g : G, ContDiff ℝ ∞ fun t => GlobalTheory.Cusp.constTermOn Γ N (fun x => F x t) g := by
  intro G _ _ _ _ _ _ Γ N _ _ hc k F hinv hs hm g
  exact contDiff_infty.2 fun n => GlobalTheory.Cusp.SmoothParam.contDiff_param hc g n F hinv hs hm
end
end

