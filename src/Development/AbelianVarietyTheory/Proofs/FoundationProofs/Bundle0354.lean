import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0353
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitMulPowOfKummerVanishesOnInertiaCurve
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfiedStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied : ∀ D, Inp D := by
  first | exact @GlobalTheory.NormSum.inp_all | exact GlobalTheory.NormSum.inp_all | (intros; apply GlobalTheory.NormSum.inp_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EdgeClassEqKummerCharacterOfChosenRootFunctionFi
section
open GlobalTheory.K4 GlobalTheory.KEdge GlobalTheory.NeedB Polynomial

namespace GlobalTheory.K4.TopSpec

variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]

open Polynomial in
variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
  [IsScalarTower F K Ω] in
theorem _root_.GlobalTheory.K4.TopSpec.res_mem_geo (g : Ω ≃ₐ[K] Ω) :
    AlgEquiv.restrictScalarsHom F g ∈ _root_.GlobalTheory.K4.geo F K Ω := by
  rw [_root_.GlobalTheory.K4.TopW.mem_geo]
  intro z
  exact g.commutes z

open Polynomial in
variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
  [IsScalarTower F K Ω] in
theorem _root_.GlobalTheory.K4.TopSpec.exists_res {g : Ω ≃ₐ[F] Ω}
    (hg : g ∈ _root_.GlobalTheory.K4.geo F K Ω) :
    ∃ g' : Ω ≃ₐ[K] Ω, AlgEquiv.restrictScalarsHom F g' = g := by
  rw [_root_.GlobalTheory.K4.TopW.mem_geo] at hg
  refine ⟨{ g.toRingEquiv with commutes' := hg }, ?_⟩
  ext y
  rfl

open Polynomial in
variable {F K Ω : Type} [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
  [IsScalarTower F K Ω] in
theorem _root_.GlobalTheory.K4.TopSpec.continuous_res [Algebra.IsAlgebraic K Ω] :
    Continuous (AlgEquiv.restrictScalarsHom F : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[F] Ω)) := by
  classical
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  intro s hs
  rw [krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, hE, hEs⟩ := hs
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  let b := Module.finBasis F E
  refine ⟨IntermediateField.adjoin K (Set.range fun i => (b i : Ω)), ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  · intro g hg
    apply hEs
    have hfix : ∀ i, g (b i : Ω) = b i := fun i =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg _
        (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have key : ∀ z : E, AlgEquiv.restrictScalarsHom F g (z : Ω) = z := by
      intro z
      induction (b.mem_span z) using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨i, rfl⟩ := hu
        exact hfix i
      | zero => simp
      | add u v _ _ hu hv => rw [IntermediateField.coe_add, map_add, hu, hv]
      | smul a u _ hu => rw [IntermediateField.coe_smul, map_smul, hu]
    exact key ⟨y, hy⟩

end GlobalTheory.K4.TopSpec

open Polynomial in

theorem _root_.GlobalTheory.K4.isTopW_topW : ∀ (k K Ω F : Type) [Field k]
    [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] [Field F] [Algebra F K] [Algebra F Ω] [IsScalarTower F K Ω] [Normal F K]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[F] Ω, g ζ = ζ) →
    (∀ τ : K ≃ₐ[F] K, ∀ x ∈ FunctionField.ringOfIntegers k K,
      τ x ∈ FunctionField.ringOfIntegers k K) →
    ∀ (a b : F) (α β : Ω), a ≠ 0 → b ≠ 0 → algebraMap F K a ∈ FunctionField.ringOfIntegers k K →
      (algebraMap F K a)⁻¹ ∈ FunctionField.ringOfIntegers k K →
      algebraMap F K b ∈ FunctionField.ringOfIntegers k K →
      (algebraMap F K b)⁻¹ ∈ FunctionField.ringOfIntegers k K →
      α ^ N = algebraMap F Ω a → β ^ N = algebraMap F Ω b →
    ∀ (x y : (Ω ≃ₐ[F] Ω) →* Multiplicative (ZMod N)),
      (∀ g, (x g).toAdd = _root_.GlobalTheory.NeedB.kum (N := N) ζ α g) →
      (∀ g, (y g).toAdd = _root_.GlobalTheory.NeedB.kum (N := N) ζ β g) →
    ∀ η : (Ω ≃ₐ[F] Ω) → ZMod N,
      _root_.GlobalTheory.KEdge.CobOn (_root_.GlobalTheory.K4.geo F K Ω) x y η →
      IsLocallyConstant (fun g : _root_.GlobalTheory.K4.geo F K Ω => η g) →
      (∀ (B : ValuationSubring Ω) (g : Ω ≃ₐ[F] Ω),
        _root_.GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
        (∀ z, B.valuation z ≤ 1 → B.valuation (g z - z) < 1) →
        g ∈ _root_.GlobalTheory.K4.geo F K Ω → η g = 0) →
    ∀ σ : Ω ≃ₐ[F] Ω, _root_.GlobalTheory.K4.IsTopW (K := K) ζ x y η σ
      (_root_.GlobalTheory.K4.topW (K := K) ζ x y η σ) := by
  intro k K Ω F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ hfix _ a b α β ha hb _ _ _ _ hα hβ
    x y hx hy η hcob hη _ σ
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : CharZero (RatFunc k) :=
    charZero_of_injective_algebraMap (algebraMap k (RatFunc k)).injective
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc k) K).injective
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.trans F K Ω
  set H := _root_.GlobalTheory.K4.geo F K Ω with hH
  haveI : H.Normal := ⟨fun h hh g => _root_.GlobalTheory.K4.TopW.conj_mem_geo g hh⟩
  obtain ⟨hhom, -, -⟩ := _root_.GlobalTheory.KEdge.edge_cup_props _ N H x y η hcob
  have hres := _root_.GlobalTheory.K4.TopSpec.continuous_res (F := F) (K := K) (Ω := Ω)
  have hmem : ∀ g : Ω ≃ₐ[K] Ω, AlgEquiv.restrictScalarsHom F g ∈ H :=
    _root_.GlobalTheory.K4.TopSpec.res_mem_geo
  have hne : ∀ {γ : Ω} {c : F}, c ≠ 0 → γ ^ N = algebraMap F Ω c → γ ≠ 0 := by
    intro γ c hc hγ h0
    rw [h0, zero_pow hN.ne'] at hγ
    exact hc ((algebraMap F Ω).injective (hγ.symm.trans (map_zero _).symm))
  have hkum : ∀ {γ : Ω} {c : F}, c ≠ 0 → γ ^ N = algebraMap F Ω c →
      IsLocallyConstant (_root_.GlobalTheory.NeedB.kum (K := F) (N := N) ζ γ) :=
    fun hc hγ => (_root_.GlobalTheory.NeedB.KumLemma.kummer_character_main F Ω N ζ _ hN hζ hfix
      (hne hc hγ) ⟨_, hγ.symm⟩).1
  have hx_lc : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω =>
      Multiplicative.toAdd (x (AlgEquiv.restrictScalarsHom F g)) := by
    have hfun : (fun g : Ω ≃ₐ[K] Ω => Multiplicative.toAdd (x (AlgEquiv.restrictScalarsHom F g))) =
        _root_.GlobalTheory.NeedB.kum ζ α ∘ AlgEquiv.restrictScalarsHom F := funext fun g => hx _
    rw [hfun]
    exact (hkum ha hα).comp_continuous hres
  have hy_lc : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω =>
      Multiplicative.toAdd (y (AlgEquiv.restrictScalarsHom F g)) := by
    have hfun : (fun g : Ω ≃ₐ[K] Ω => Multiplicative.toAdd (y (AlgEquiv.restrictScalarsHom F g))) =
        _root_.GlobalTheory.NeedB.kum ζ β ∘ AlgEquiv.restrictScalarsHom F := funext fun g => hy _
    rw [hfun]
    exact (hkum hb hβ).comp_continuous hres
  have hη₁ : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω => η (AlgEquiv.restrictScalarsHom F g) :=
    hη.comp_continuous (f := fun g : Ω ≃ₐ[K] Ω => (⟨AlgEquiv.restrictScalarsHom F g, hmem g⟩ : H))
      (hres.subtype_mk _)
  have hη₂ : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω => η (σ * AlgEquiv.restrictScalarsHom F g * σ⁻¹) :=
    hη.comp_continuous (f := fun g : Ω ≃ₐ[K] Ω =>
      (⟨σ * AlgEquiv.restrictScalarsHom F g * σ⁻¹,
        _root_.GlobalTheory.K4.TopW.conj_mem_geo σ (hmem g)⟩ : H))
      (((continuous_const.mul hres).mul continuous_const).subtype_mk _)
  let χ : (Ω ≃ₐ[K] Ω) → ZMod N := fun g =>
    _root_.GlobalTheory.KEdge.edge x y η σ (AlgEquiv.restrictScalarsHom F g)
  have hlc : IsLocallyConstant χ := by
    have hfun : χ = fun g => η (σ * AlgEquiv.restrictScalarsHom F g * σ⁻¹) -
        η (AlgEquiv.restrictScalarsHom F g) -
        Multiplicative.toAdd (x (AlgEquiv.restrictScalarsHom F g)) * Multiplicative.toAdd (y σ) +
        Multiplicative.toAdd (x σ) * Multiplicative.toAdd (y (AlgEquiv.restrictScalarsHom F g)) :=
      rfl
    rw [hfun]
    exact ((hη₂.comp₂ hη₁ (· - ·)).comp₂ (hx_lc.comp (· * Multiplicative.toAdd (y σ))) (· - ·)).comp₂
      (hy_lc.comp (Multiplicative.toAdd (x σ) * ·)) (· + ·)
  have hadd : ∀ g ∈ (⊥ : IntermediateField K Ω).fixingSubgroup,
      ∀ h ∈ (⊥ : IntermediateField K Ω).fixingSubgroup, χ (g * h) = χ g + χ h := by
    intro g _ h _
    simp only [χ, map_mul]
    exact hhom σ _ (hmem g) _ (hmem h)
  obtain ⟨θ, hθ0, hθN, hθ⟩ :=
    _root_.GlobalTheory.kummer_generator_of_char K Ω N ζ hN hζ (fun g => hfix (AlgEquiv.restrictScalarsHom F g)) ⊥ χ hlc hadd
  obtain ⟨w, hw⟩ := IntermediateField.mem_bot.mp hθN
  apply _root_.GlobalTheory.K4.TopW.isTopW_topW_of_exists
  refine ⟨w, ?_, θ, hw.symm, ?_⟩
  · rintro rfl
    rw [map_zero] at hw
    exact hθ0 ((pow_eq_zero_iff hN.ne').mp hw.symm)
  · intro g hg
    obtain ⟨g', rfl⟩ := _root_.GlobalTheory.K4.TopSpec.exists_res hg
    apply _root_.GlobalTheory.NeedB.kum_eq_of hζ hθ0
    exact hθ g' (by rw [IntermediateField.fixingSubgroup_bot]; exact Subgroup.mem_top _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularUnitsOfRootMemKummerAdjoin
section
open scoped MatrixGroups TensorProduct
open Polynomial

namespace GlobalTheory.KZ.UnRoot

theorem exists_comap_eq {K L : Type} [Field K] [Field L] (f : K →+* L) (U : ValuationSubring K) :
    ∃ W : ValuationSubring L, W.comap f = U := by
  obtain ⟨W, hW, hloc⟩ := IsLocalRing.exists_factor_valuationRing (f.comp U.subtype)
  have key : ∀ x ∈ U.nonunits, f x ∈ W.nonunits := by
    intro x hx
    obtain ⟨hxU, hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.1 hx
    refine ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.2 ⟨hW ⟨x, hxU⟩, ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm ⊢
    exact fun hu => hm (hloc.map_nonunit ⟨x, hxU⟩ hu)
  refine ⟨W, le_antisymm ?_ ?_⟩
  · intro x hx
    by_contra hxU
    have h0 : x ≠ 0 := by rintro rfl; exact hxU U.zero_mem
    have h1 : x⁻¹ ∈ U.nonunits := by
      rw [ValuationSubring.mem_nonunits_iff, map_inv₀]
      have : 1 < U.valuation x := by
        rw [← not_le, ValuationSubring.valuation_le_one_iff]; exact hxU
      exact inv_lt_one_of_one_lt₀ this
    have h2 := key _ h1
    rw [ValuationSubring.mem_nonunits_iff, map_inv₀, map_inv₀] at h2
    have h3 : W.valuation (f x) ≤ 1 := (W.valuation_le_one_iff _).2 hx
    have h4 : 0 < W.valuation (f x) := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]; exact (map_ne_zero f).2 h0
    exact absurd ((inv_lt_one₀ h4).1 h2) (not_lt.2 h3)
  · intro x hx
    exact hW ⟨x, hx⟩

theorem val_eq_one_iff {F : Type} [Field F] (T : ValuationSubring F) (y : F) :
    T.valuation y = 1 ↔ y ≠ 0 ∧ y ∈ T ∧ y⁻¹ ∈ T := by
  rw [← T.valuation_le_one_iff, ← T.valuation_le_one_iff, map_inv₀]
  constructor
  · intro h
    refine ⟨fun h0 => ?_, h.le, by rw [h, inv_one]⟩
    rw [h0, map_zero] at h
    exact zero_ne_one h
  · rintro ⟨h0, h₁, h₂⟩
    have : 0 < T.valuation y := zero_lt_iff.2 ((_root_.map_ne_zero _).2 h0)
    exact le_antisymm h₁ ((inv_le_one₀ this).1 h₂)

theorem val_comap_eq_one {K K' : Type} [Field K] [Field K'] (f : K →+* K') (S : ValuationSubring K') (x : K) :
    (S.comap f).valuation x = 1 ↔ S.valuation (f x) = 1 := by
  rw [val_eq_one_iff, val_eq_one_iff, ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀,
    _root_.map_ne_zero]

theorem val_eq_one_of_pow {L : Type} [Field L] (A : ValuationSubring L) {x : L} {n : ℕ} (hn : n ≠ 0)
    (h : A.valuation (x ^ n) = 1) : A.valuation x = 1 := by
  rw [map_pow] at h
  rcases lt_trichotomy (A.valuation x) 1 with h1 | h1 | h1
  · exact absurd h (ne_of_lt (pow_lt_one₀ zero_le' h1 hn))
  · exact h1
  · exact absurd h (ne_of_gt (one_lt_pow₀ h1 hn))

theorem root_eq_one {F : Type} [Field F] (V : ValuationSubring F) {m : ℕ} (hm : V.valuation (m : F) = 1) {ζ : F}
    (hζ : ζ ^ m = 1) (hV : V.valuation (ζ - 1) < 1) : ζ = 1 := by
  first
  | exact @_root_.GlobalTheory.RootOfUnityEqOne.main
  | exact _root_.GlobalTheory.RootOfUnityEqOne.main
  | (apply _root_.GlobalTheory.RootOfUnityEqOne.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootOfUnityEqOne.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootOfUnityEqOne.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootOfUnityEqOne.main ..)

theorem fix_root {L : Type} [Field L] (B : ValuationSubring L) {m : ℕ} (hm0 : m ≠ 0) (hm : B.valuation (m : L) = 1)
    {y U g : L} (hy : y ^ m = U) (hg : g ≠ 0) (hu : B.valuation (U / g ^ m) = 1) (φ : L →+* L) (hU : φ U = U)
    (hφg : φ g = g) (hφ : ∀ x, B.valuation x ≤ 1 → B.valuation (φ x - x) < 1) : φ y = y := by
  have hz : B.valuation (y / g) = 1 := val_eq_one_of_pow B hm0 (by rw [div_pow, hy]; exact hu)
  have hz0 : y / g ≠ 0 := ((val_eq_one_iff B _).1 hz).1
  have hy0 : y ≠ 0 := fun h => hz0 (by rw [h, zero_div])
  have h1 : (φ y / y) ^ m = 1 := by
    rw [div_pow, ← map_pow, hy, hU, div_self]
    rw [← hy]; exact pow_ne_zero _ hy0
  have h2 := hφ _ hz.le
  have e : φ (y / g) - y / g = (φ y / y - 1) * (y / g) := by
    rw [map_div₀, hφg]; field_simp
  rw [e, map_mul, hz, mul_one] at h2
  have := root_eq_one B hm h1 h2
  exact (div_eq_one_iff_eq hy0).1 this

theorem fix_adjoin {K L : Type} [Field K] [Field L] [Algebra K L] (Q : (L →+* L) → Prop) (S : Set L)
    (hS : ∀ y ∈ S, ∃ T : Finset K, ∀ φ, Q φ → (∀ t ∈ T, φ (algebraMap K L t) = algebraMap K L t) → φ y = y)
    {θ : L} (hθ : θ ∈ IntermediateField.adjoin K S) :
    ∃ T : Finset K, ∀ φ, Q φ → (∀ t ∈ T, φ (algebraMap K L t) = algebraMap K L t) → φ θ = θ := by
  classical
  induction hθ using IntermediateField.adjoin_induction with
  | mem x hx => exact hS x hx
  | algebraMap x => exact ⟨{x}, fun φ _ h => h x (Finset.mem_singleton_self x)⟩
  | add x y _ _ hx hy =>
    obtain ⟨T, hT⟩ := hx
    obtain ⟨T', hT'⟩ := hy
    exact ⟨T ∪ T', fun φ hq h => by
      rw [map_add, hT φ hq fun t ht => h t (Finset.mem_union_left _ ht),
        hT' φ hq fun t ht => h t (Finset.mem_union_right _ ht)]⟩
  | inv x _ hx =>
    obtain ⟨T, hT⟩ := hx
    exact ⟨T, fun φ hq h => by rw [map_inv₀, hT φ hq h]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨T, hT⟩ := hx
    obtain ⟨T', hT'⟩ := hy
    exact ⟨T ∪ T', fun φ hq h => by
      rw [map_mul, hT φ hq fun t ht => h t (Finset.mem_union_left _ ht),
        hT' φ hq fun t ht => h t (Finset.mem_union_right _ ht)]⟩

theorem core {k K L : Type} [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [Algebra.IsAlgebraic (RatFunc k) K] [Field L] [Algebra K L] [IsAlgClosure K L]
    (B : ValuationSubring L) (hB : ∀ p : k[X], algebraMap K L (algebraMap k[X] K p) ∈ B) {l : ℕ} (hl : 0 < l)
    (f : K) (hf : f ≠ 0) (θ : L) (hθ : θ ^ l = algebraMap K L f) (T : Finset K)
    (hT : ∀ φ : L →+* L, (∀ x, B.valuation x ≤ 1 → B.valuation (φ x - x) < 1) →
      (∀ t ∈ T, φ (algebraMap K L t) = algebraMap K L t) → φ θ = θ) :
    ∃ c : K, c ≠ 0 ∧ B.valuation (algebraMap K L (f / c ^ l)) = 1 := by
  classical
  let E : IntermediateField (RatFunc k) K := IntermediateField.adjoin (RatFunc k) ((insert f T : Finset K) : Set K)
  have hE : ∀ t ∈ insert f T, t ∈ E := fun t ht => IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 ht)
  haveI : FiniteDimensional (RatFunc k) E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic E K := inferInstance
  haveI : Module.IsTorsionFree E L := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure E L := ⟨inferInstance, Algebra.IsAlgebraic.trans E K L⟩
  haveI : CharZero K := charZero_of_injective_ringHom (algebraMap (RatFunc k) K).injective
  haveI : CharZero L := charZero_of_injective_ringHom (algebraMap K L).injective
  haveI : NeZero (l : L) := ⟨Nat.cast_ne_zero.2 hl.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L l
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    rw [zero_pow hl.ne'] at hθ
    exact hf ((map_eq_zero _).1 hθ.symm)
  obtain ⟨c, hc, hv⟩ := GlobalTheory.KumVal.exists_unit_of_kum_eq_zero k E L l ζ hl hζ ⟨f, hE f (Finset.mem_insert_self _ _)⟩ θ
    (fun h => hf (congrArg Subtype.val h)) hθ B (by
      intro x hx
      have hx' : IsIntegral k[X] x := hx
      obtain ⟨p, hp, hpx⟩ := hx'
      let ρ : k[X] →+* B := ((algebraMap K L).comp (algebraMap k[X] K)).codRestrict B hB
      have hi : IsIntegral B (algebraMap E L x) := by
        refine ⟨p.map ρ, hp.map ρ, ?_⟩
        rw [eval₂_map]
        have := congrArg (algebraMap E L) hpx
        rw [hom_eval₂, map_zero] at this
        exact this
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
      rw [← hy]; exact y.2)
    (fun g hg => GlobalTheory.NeedB.kum_eq_of hζ hθ0 0 (by
      have := hT (g : L →+* L) hg fun t ht => g.commutes ⟨t, hE t (Finset.mem_insert_of_mem ht)⟩
      simpa using this))
  refine ⟨c, fun h => hc (Subtype.ext h), ?_⟩
  exact hv

end GlobalTheory.KZ.UnRoot

open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.UnRoot

theorem mem_Un_of_root_mem_adjoin : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (m l : ℕ), 0 < m → 0 < l → ∀ (θ : AlgebraicClosure X.K) (f : X.Kˣ), θ ∈ IntermediateField.adjoin X.K {y : AlgebraicClosure X.K | ∃ U ∈ X.Un m, y ^ m = algebraMap X.K (AlgebraicClosure X.K) (U : X.K)} → θ ^ l = algebraMap X.K (AlgebraicClosure X.K) (f : X.K) → f ∈ X.Un l := by
  intro Ω _ _ _ ε X m l hm hl θ f hθ hf W hW
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_ringHom (algebraMap ℚ Ω).injective
  obtain ⟨B, rfl⟩ := exists_comap_eq (algebraMap X.K (AlgebraicClosure X.K)) W
  let e := RatFunc.algEquivOfTranscendental X.jK (GlobalTheory.K4.jK_transcendental X)
  let ψ : RatFunc Ω →ₐ[Ω] X.K := (IntermediateField.val _).comp e.toAlgHom
  letI : Algebra (RatFunc Ω) X.K := ψ.toRingHom.toAlgebra
  letI : Algebra (Polynomial Ω) X.K := (ψ.toRingHom.comp (algebraMap (Polynomial Ω) (RatFunc Ω))).toAlgebra
  haveI : IsScalarTower (Polynomial Ω) (RatFunc Ω) X.K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic (RatFunc Ω) X.K := ⟨fun x => by
    refine (X.alg_j x).ringHom_of_comp_eq (e.symm : _ →+* RatFunc Ω) (RingHom.id _) e.symm.injective ?_
    ext a
    show ((e (e.symm a) : _) : X.K) = a
    rw [e.apply_symm_apply]⟩
  have hp : ∀ p : (Polynomial Ω), algebraMap (Polynomial Ω) X.K p ∈ B.comap (algebraMap X.K (AlgebraicClosure X.K)) := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
      have : algebraMap (Polynomial Ω) X.K (C a) = algebraMap Ω X.K a := by
        rw [← ψ.commutes a]; rfl
      rw [this]; exact hW.1 a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n a h =>
      have : algebraMap (Polynomial Ω) X.K Polynomial.X = X.jK := by
        show ((e (algebraMap (Polynomial Ω) (RatFunc Ω) Polynomial.X) : _) : X.K) = _
        rw [RatFunc.algebraMap_X, RatFunc.algEquivOfTranscendental_X]
      rw [pow_succ, ← mul_assoc, map_mul, this]
      exact mul_mem h hW.2
  have hmB : B.valuation (m : AlgebraicClosure X.K) = 1 := by
    have h1 : (B.comap (algebraMap X.K (AlgebraicClosure X.K))).valuation (algebraMap Ω X.K (m : Ω)) = 1 := by
      rw [val_eq_one_iff, ← map_inv₀]
      exact ⟨(_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 hm.ne'), hW.1 _, hW.1 _⟩
    rw [val_comap_eq_one] at h1
    simpa using h1
  obtain ⟨T, hT⟩ := fix_adjoin (fun φ => ∀ x, B.valuation x ≤ 1 → B.valuation (φ x - x) < 1) _ (by
    rintro y ⟨U, hU, hy⟩
    obtain ⟨g, hg⟩ := hU _ hW
    rw [val_comap_eq_one, map_div₀, map_pow] at hg
    exact ⟨{(U : X.K), (g : X.K)}, fun φ hq h => fix_root B hm.ne' hmB hy ((_root_.map_ne_zero _).2 g.ne_zero) hg φ
      (h _ (by simp)) (h _ (by simp)) hq⟩) hθ
  obtain ⟨c, hc, hv⟩ := core (k := Ω) B hp hl (f : X.K) f.ne_zero θ hf T hT
  exact ⟨Units.mk0 c hc, (val_comap_eq_one _ _ _).2 hv⟩

end GlobalTheory.KZ.UnRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaJetClassSumArchimedeanBoundOfCmTheta
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchTop

theorem archSt_of_inp : (∀ D, Inp D) → ArchSt := by
  intro hI
  obtain ⟨C, hC, h⟩ := GlobalTheory.ArchNorm.norm_meanInf_posLog_le
  refine ⟨C, hC, ?_⟩
  intro D cc δ t0 Q hc ht hQ K _ _ _ σ ι N B L P P' zA zA' hN hB h1 hL hd hs hn i
  exact ⟨h D (hI D) cc δ t0 Q hc ht hQ K σ N B L (P i) (zA i) hN hB h1 hL hd (hs i).1 (hn i).1,
    h D (hI D) cc δ t0 Q hc ht hQ K σ N B L (P' i) (zA' i) hN hB h1 hL hd (hs i).2 (hn i).2⟩

end GlobalTheory.ArchTop
end

