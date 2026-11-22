import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsLocExtFinrankEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0101
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Formalism.SharpRestriction.LevelLetterCocycles.GaloisEquivariantKeyFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0073
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0687
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallySemistableReducibleUnramifiedSplit
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsValuationEqOfIneFixes
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DelEps
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Pointwise
noncomputable section
namespace GlobalTheory.InertFixVal

theorem exists_mem_Ine_lift_int {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) (M : Type*) [Field M] [Algebra F M]
    [Algebra M Ω] [IsScalarTower F M Ω] [FiniteDimensional F M] [IsGalois F M] (τ : M ≃ₐ[F] M)
    (h : ∀ x : 𝓞 M, A.valuation (algebraMap M Ω (τ (x : M)) - algebraMap M Ω (x : M)) < 1) :
    ∃ σ ∈ Ine (F := F) A, ∀ x : M, σ (algebraMap M Ω x) = algebraMap M Ω (τ x) := by
  haveI : NumberField M := NumberField.of_module_finite F M
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : IsAlgClosure M Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) M⟩
  let σ₁ : Ω ≃ₐ[F] Ω := τ.liftNormal Ω
  have h₁ : ∀ x : M, σ₁ (algebraMap M Ω x) = algebraMap M Ω (τ x) := fun x => τ.liftNormal_commutes Ω x
  obtain ⟨g, hg⟩ := GlobalTheory.InertiaLift.exists_smul_eq (F := M) (A := A) (A' := σ₁⁻¹ • A) (by
    intro x
    rw [smul_valuation_lt_one_iff, inv_inv]
    change A.valuation (algebraMap M Ω (x : M)) < 1 ↔ A.valuation (σ₁ (algebraMap M Ω (x : M))) < 1
    rw [h₁]
    have hx := h x
    constructor
    · intro hl
      simpa using Valuation.map_add_lt _ hx hl
    · intro hl
      simpa using Valuation.map_sub_lt _ hl hx)
  let σ₂ : Ω ≃ₐ[F] Ω := σ₁ * g.restrictScalars F
  have h₂ : ∀ x : M, σ₂ (algebraMap M Ω x) = algebraMap M Ω (τ x) := fun x => by
    rw [← h₁]
    exact congrArg σ₁ (g.commutes x)
  have h₂' : ∀ y, A.valuation (σ₂ y) < 1 ↔ A.valuation y < 1 := fun y => by
    rw [← hg y, smul_valuation_lt_one_iff, inv_inv]
    rfl
  obtain ⟨k, hk, hk'⟩ := GlobalTheory.InertiaLift.exists_congr (F := M) (A := A) σ₂.toRingEquiv h₂' (by
    intro x
    change A.valuation (σ₂ (algebraMap M Ω (x : M)) - algebraMap M Ω (x : M)) < 1
    rw [h₂]
    exact h x)
  have hkinv : ∀ y, A.valuation (k.symm y) < 1 ↔ A.valuation y < 1 := fun y => by
    rw [← valuation_apply_lt_one_iff hk, k.apply_symm_apply]
  refine ⟨k.symm.restrictScalars F * σ₂, GlobalTheory.InertiaLift.mem_Ine_of_integral
    (GlobalTheory.InertiaLift.mem_Dec_of_lt fun y => ?_) fun b hb => ?_, fun x => ?_⟩
  · change A.valuation (k.symm (σ₂ y)) < 1 ↔ _
    rw [hkinv, h₂']
  · change A.valuation (k.symm (σ₂ b) - b) < 1
    rw [← valuation_apply_lt_one_iff hk, map_sub, k.apply_symm_apply, Valuation.map_sub_swap]
    exact hk' b hb
  · change k.symm (σ₂ (algebraMap M Ω x)) = _
    rw [h₂]
    exact k.symm.commutes (τ x)

def primeUnder {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) (M : Type*) [Field M] [NumberField M] [Algebra M Ω] :
    Ideal (𝓞 M) :=
  Ideal.comap (((algebraMap M Ω).comp (algebraMap (𝓞 M) M)).codRestrict A.toSubring fun x =>
    mem_of_isIntegral_int A (x.isIntegral_coe.map (algebraMap M Ω).toIntAlgHom)) (IsLocalRing.maximalIdeal A)

theorem mem_primeUnder {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) (M : Type*) [Field M] [NumberField M]
    [Algebra M Ω] (x : 𝓞 M) : x ∈ primeUnder A M ↔ A.valuation (algebraMap M Ω (x : M)) < 1 := by
  rw [primeUnder, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

theorem ramificationIdx_eq_one {K Ω L : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (hv : IsPlaceOver A v) (hw : IsPlaceOver A w)
    (hI : ∀ σ ∈ Ine (F := K) A, ∀ x : L, σ (algebraMap L Ω x) = algebraMap L Ω x) :
    w.asIdeal.LiesOver v.asIdeal ∧ w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  let N : IntermediateField K Ω := IntermediateField.normalClosure K L Ω
  let M : Type := N
  haveI : FiniteDimensional K M := inferInstance
  haveI : NumberField M := NumberField.of_module_finite K M
  haveI : IsGalois K M := IsGalois.normalClosure K L Ω
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  let P : Ideal (𝓞 M) := primeUnder A M
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hPv : P.under (𝓞 K) = v.asIdeal := by
    ext x
    rw [Ideal.mem_comap, mem_primeUnder, ← hv x]
    congr! 2
  have hPw : P.under (𝓞 L) = w.asIdeal := by
    ext x
    rw [Ideal.mem_comap, mem_primeUnder, ← hw x]
    congr! 2
  haveI hPv' : P.LiesOver v.asIdeal := ⟨hPv.symm⟩
  haveI hPw' : P.LiesOver w.asIdeal := ⟨hPw.symm⟩
  haveI hwv : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hPw, Ideal.under_under, hPv]⟩
  refine ⟨hwv, ?_⟩
  have hv0 := v.ne_bot
  have hw0 := w.ne_bot
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hv0 P
  have := v.isMaximal
  have := w.isMaximal
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hv0
  have : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hw0
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[K] M) v.asIdeal P
  have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[L] M) w.asIdeal P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (M ≃ₐ[K] M)] at h1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (M ≃ₐ[L] M)] at h2
  have h3 := Ideal.ramificationIdx_tower (R := 𝓞 K) w.asIdeal P

  have hfix : ∀ τ ∈ P.toAddSubgroup.inertia (M ≃ₐ[K] M), ∀ x : L, τ (algebraMap L M x) = algebraMap L M x := by
    intro τ hτ x
    obtain ⟨σ, hσ, hστ⟩ := exists_mem_Ine_lift_int A M τ fun y => by
      have := (mem_primeUnder A M _).1 (hτ y)
      have e : ((τ • y - y : 𝓞 M) : M) = τ (y : M) - (y : M) := rfl
      rw [← map_sub, ← e]
      exact this
    apply (algebraMap M Ω).injective
    rw [← hστ, ← IsScalarTower.algebraMap_apply, hI σ hσ x]
  let f : P.toAddSubgroup.inertia (M ≃ₐ[K] M) → P.toAddSubgroup.inertia (M ≃ₐ[L] M) := fun τ =>
    ⟨{ (τ : M ≃ₐ[K] M).toRingEquiv with commutes' := hfix τ τ.2 }, fun y => τ.2 y⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply AlgEquiv.ext
    intro y
    exact DFunLike.congr_fun (congrArg Subtype.val hab) y
  have h4 := Nat.card_le_card_of_injective f hf
  rw [h1, h2, h3] at h4
  have hpos : 0 < P.ramificationIdx (𝓞 K) := h1 ▸ Nat.card_pos
  rw [h3] at hpos
  have ha : w.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have hb : P.ramificationIdx (𝓞 L) ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have hle : w.asIdeal.ramificationIdx (𝓞 K) ≤ 1 := by
    by_contra hc
    push_neg at hc
    have : 2 * P.ramificationIdx (𝓞 L) ≤ w.asIdeal.ramificationIdx (𝓞 K) * P.ramificationIdx (𝓞 L) :=
      Nat.mul_le_mul_right _ hc
    omega
  omega

end GlobalTheory.InertFixVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HaarMeasureUniformizerTranslateStatement
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_uniformizer_translate : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (ν : Measure (GlobalTheory.CellDec.NA E n)) [ν.IsHaarMeasure] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ))
    (A : Set (GlobalTheory.CellDec.NA E n)), MeasurableSet A →
    ν {u : GlobalTheory.CellDec.NA E n | ∃ a ∈ A, (a : GA E n) = GlobalTheory.CellDec.tl n ϖ l * (u : GA E n) * (GlobalTheory.CellDec.tl n ϖ l)⁻¹} =
      ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) * ν A := by
  first | exact @GlobalTheory.CellDec.ModulusPf.modulus_conj | exact GlobalTheory.CellDec.ModulusPf.modulus_conj | (intros; apply GlobalTheory.CellDec.ModulusPf.modulus_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterValueAtSplitPlaceDeterminantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_value_at_splitPlace_determinant : ∀ {D : D7} (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (Q : Finset (Pl D.host.E)) (V : HSp D) (P : Pl D.host.E) (k : ℕ) (α : GA D V) (z : (AE D)ˣ), ChrEq c χ → GlobalTheory.ExportSeries.UnramOutside c Q → GlobalTheory.ExportSeries.SplitSet Q → Bridge.SplitOff P (Q : Set (Pl D.host.E)) → IsHeckeAt V P k α → IsDetAt (idemAt P) V α z → ((c z : Circle) : ℂ) = ((χ.val P : ℂˣ) : ℂ) ^ k := by
  first | exact @GlobalTheory.HeckeDetValue.chr_detAt | exact GlobalTheory.HeckeDetValue.chr_detAt | (intros; apply GlobalTheory.HeckeDetValue.chr_detAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertSatakeHeckeEigenvaluesAlgebraicAutomorphicStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertSatake_heckeEigenvalues_algebraic_automorphic : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.SatAt π Dv α → ∀ α0 : Fin (n / 2) → ℂˣ, HasSatAt U w Dv.σw Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) α0 → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h (fun i => (α0 i : ℂ)) := by
  first | exact @GlobalTheory.InertHeckeCmp.satU_eq | exact GlobalTheory.InertHeckeCmp.satU_eq | (intros; apply GlobalTheory.InertHeckeCmp.satU_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCDVRFractionFieldReadingInCpFiniteExtension
section
open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie GlobalTheory.GoodPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoTie.ReadExt

section Val

open Classical

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem vV_unit' (u : Vˣ) : vV V (algebraMap V K u) = 0 := by
  have : valV V (algebraMap V K u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit
  simp [vV, this]

theorem vV_irr' {a : V} (ha : Irreducible a) : vV V (algebraMap V K a) = 1 := by
  have : valV V (algebraMap V K a) = WithZero.exp (-1 : ℤ) := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ ha.ne_zero ha.maximalIdeal_eq
  simp [vV, this]

theorem vV_pow' {x : K} (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  simp [vV]

variable (V K) in

def absOfVal (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) : AbsoluteValue K ℝ where
  toFun x := if x = 0 then 0 else c ^ (vV V x)
  map_mul' x y := by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    simp [hx, hy, vV_mul hx hy, zpow_add₀ hc0.ne']
  nonneg' x := by
    show 0 ≤ (if x = 0 then 0 else c ^ (vV V x))
    split_ifs
    · exact le_rfl
    · positivity
  eq_zero' x := by
    show (if x = 0 then 0 else c ^ (vV V x)) = 0 ↔ x = 0
    split_ifs with h
    · simp [h]
    · simp [h, zpow_ne_zero _ hc0.ne']
  add_le' x y := by
    show (if x + y = 0 then 0 else c ^ (vV V (x + y))) ≤
      (if x = 0 then 0 else c ^ (vV V x)) + (if y = 0 then 0 else c ^ (vV V y))
    by_cases hx : x = 0
    · subst hx; simp
    by_cases hy : y = 0
    · subst hy; simp
    have px := zpow_pos hc0 (vV V x)
    have py := zpow_pos hc0 (vV V y)
    by_cases hxy : x + y = 0
    · simp only [hxy, hx, hy, if_true, if_false]; positivity
    simp only [hxy, hx, hy, if_false]
    rcases min_le_iff.1 (min_le_vV_add (V := V) hx hy hxy) with h | h
    · have := zpow_le_zpow_right_of_le_one₀ hc0 hc1 h
      linarith
    · have := zpow_le_zpow_right_of_le_one₀ hc0 hc1 h
      linarith

theorem absOfVal_of_ne (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) {x : K} (hx : x ≠ 0) :
    absOfVal V K c hc0 hc1 x = c ^ (vV V x) := by
  show (if x = 0 then 0 else c ^ (vV V x)) = _
  simp [hx]

end Val

theorem norm_eq_zpow (T : CDVR) {C : Type} [NormedField C] (k : T.Fr →+* C)
    (hball : ∀ x, ‖k x‖ ≤ 1 ↔ InV T x) {π : T.V} (hπ : Irreducible π) (x : T.Fr) (hx : x ≠ 0) :
    ‖k x‖ = ‖k (algebraMap T.V T.Fr π)‖ ^ vV T.V x := by
  have hu : ∀ u : T.Vˣ, ‖k (algebraMap T.V T.Fr u)‖ = 1 := by
    intro u
    have h1 := (hball (algebraMap T.V T.Fr u)).2 ⟨u, rfl⟩
    have h2 := (hball (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ))).2 ⟨_, rfl⟩
    have h3 : ‖k (algebraMap T.V T.Fr u)‖ * ‖k (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, map_one,
        norm_one]
    nlinarith [norm_nonneg (k (algebraMap T.V T.Fr u)), norm_nonneg (k (algebraMap T.V T.Fr (u⁻¹ : T.Vˣ)))]
  have hπ0 : algebraMap T.V T.Fr π ≠ 0 := by
    simpa using hπ.ne_zero
  have hρ0 : ‖k (algebraMap T.V T.Fr π)‖ ≠ 0 := by
    simpa using hπ0
  have key : ∀ a : T.V, a ≠ 0 →
      ‖k (algebraMap T.V T.Fr a)‖ = ‖k (algebraMap T.V T.Fr π)‖ ^ vV T.V (algebraMap T.V T.Fr a) := by
    intro a ha
    obtain ⟨s, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    have hu0 : algebraMap T.V T.Fr u ≠ 0 := by simp
    rw [map_mul, map_pow, vV_mul hu0 (pow_ne_zero _ hπ0), vV_pow', vV_unit', vV_irr' hπ, map_mul, norm_mul, hu,
      map_pow, norm_pow]
    simp
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := T.V) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap T.V T.Fr b ≠ 0 := by simpa using hb0
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have hv := vV_mul (V := T.V) hx hb1
  rw [div_mul_cancel₀ _ hb1] at hv
  rw [map_div₀, norm_div, key a ha0, key b hb0, ← zpow_sub₀ hρ0, hv]
  congr 1
  ring

theorem isReading_ext : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR)
    (io : F →+* T.Fr) (k : T.Fr →+* ℂ_[p]), IsReading φ T io k → ∀ (T' : CDVR) (i : T.Fr →+* T'.Fr),
    GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsFinExt T T' i → ∀ j : T'.Fr →+* ℂ_[p], j.comp i = k → IsReading φ T' (i.comp io) j := by
  intro p _ F _ _ φ T io k hk T' i hi j hj
  have hji : ∀ y, j (i y) = k y := fun y => by rw [← hj]; rfl
  refine ⟨fun a => by rw [RingHom.comp_apply, hji]; exact hk.comp a, fun x => ?_⟩
  obtain ⟨hfin, r, hr, hv⟩ := hi
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hπ0 : algebraMap T.V T.Fr π ≠ 0 := by simpa using hπ.ne_zero
  set ρ := ‖k (algebraMap T.V T.Fr π)‖ with hρ
  have hρ0 : 0 < ρ := norm_pos_iff.2 ((map_ne_zero k).2 hπ0)
  have hρ1 : ρ < 1 := by
    by_contra hc
    push_neg at hc
    have h1 : ‖k (algebraMap T.V T.Fr π)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hc
    obtain ⟨v, hv'⟩ := (hk.int _).1 h1
    apply hπ.not_isUnit
    refine IsUnit.of_mul_eq_one v ?_
    apply IsFractionRing.injective T.V T.Fr
    rw [map_mul, hv', map_one, mul_inv_cancel₀ hπ0]
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  set c : ℝ := ρ ^ ((1 : ℝ) / r) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hρ0 _
  have hc1 : c < 1 := Real.rpow_lt_one hρ0.le hρ1 (by positivity)
  have hcr : c ^ r = ρ := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hρ0.le, one_div, inv_mul_cancel₀ hr0.ne', Real.rpow_one]
  letI NF : NontriviallyNormedField T.Fr :=
    { NormedField.induced T.Fr ℂ_[p] k k.injective with
      non_trivial := ⟨(algebraMap T.V T.Fr π)⁻¹, by
        show 1 < ‖k (algebraMap T.V T.Fr π)⁻¹‖
        rw [map_inv₀, norm_inv]
        exact (one_lt_inv₀ hρ0).2 hρ1⟩ }
  have hnk : ∀ y : T.Fr, ‖y‖ = ‖k y‖ := fun y => rfl
  haveI : IsUltrametricDist T.Fr :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
      rw [hnk, hnk, hnk, map_add]
      exact IsUltrametricDist.norm_add_le_max _ _
  haveI : CompleteSpace T.Fr := Formalism.MainNotions.ExistsIdealDenominator.complete_of_adic (O := T.V) (K := T.Fr) (fun y => hk.int y) inferInstance
  letI := i.toAlgebra
  haveI : FiniteDimensional T.Fr T'.Fr := hfin
  have e1 := spectralNorm_unique_field_norm_ext (K := T.Fr) (L := T'.Fr)
    (f := (NormedField.toAbsoluteValue ℂ_[p]).comp j.injective) (fun y => by
      show ‖j (i y)‖ = ‖y‖
      rw [hji, hnk]) x
  have e2 := spectralNorm_unique_field_norm_ext (K := T.Fr) (L := T'.Fr)
    (f := absOfVal T'.V T'.Fr c hc0 hc1.le) (fun y => by
      show absOfVal T'.V T'.Fr c hc0 hc1.le (i y) = ‖y‖
      by_cases hy : y = 0
      · subst hy; simp
      rw [absOfVal_of_ne _ _ _ ((map_ne_zero i).2 hy), hv, zpow_mul, zpow_natCast, hcr, hnk,
        norm_eq_zpow T k hk.int hπ y hy]) x
  have hx : ‖j x‖ = absOfVal T'.V T'.Fr c hc0 hc1.le x := e1.trans e2.symm
  rw [hx]
  by_cases hx0 : x = 0
  · subst hx0
    simp only [map_zero, zero_le_one, true_iff]
    exact ⟨0, map_zero _⟩
  rw [absOfVal_of_ne _ _ _ hx0]
  change _ ↔ ∃ a : T'.V, algebraMap T'.V T'.Fr a = x
  rw [GlobalTheory.CompleteValExt.exists_algebraMap_eq_iff]
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    have := one_lt_zpow_of_neg₀ hc0 hc1 hn
    linarith
  · intro h
    exact zpow_le_one₀ hc0 hc1.le h

end GlobalTheory.GeoTie.ReadExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRatConstMul
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SerRatRay

def UntwRat : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i), GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV →
    ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) R.Q (labLL D)
        (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
    ∀ u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) →
      ∃ ph : ℂ, ‖ph‖ = 1 ∧ ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, GoodCover T R i C (κ i).n →
        ∀ s ∈ GfC (Vc D i), ∀ f : WO (Vc D i) (Wc D i) → ℂ,
          IsLevDatum R.ψ (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (T.Q.l.M * C.d.pd) C.σ₂.fieldRange (R.vacP i) f →
          ∀ w ∈ ratVec R i (c0L i) C.σ₂.fieldRange,
            IsRat T i hV C (κ i) (fun g => ph * thetaKO (R.ωP i A.μ0) s g (harmVec R i u w f))

theorem isRat_const_mul {D : D7} (T : CoreJ D) (i : Fin D.R.m) {σ : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (C : Cover T ((i : ℕ) + 1) σ) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (φ : GA D (Wc D i) → ℂ) (c : ℂ)
    (h : IsRat T i hV C κ φ) (hc : c ∈ C.σ₂.fieldRange) : IsRat T i hV C κ (fun g => c * φ g) := by
  obtain ⟨φ', ⟨f₂, hf₂, rfl⟩, rfl⟩ := h
  obtain ⟨c', rfl⟩ := RingHom.mem_fieldRange.1 hc
  refine ⟨C.rd (wtA κ) (c' • f₂), ⟨c' • f₂, ⟨(sec _ _ _ _).smul_mem c' hf₂.1, ?_⟩, rfl⟩, ?_⟩
  · rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ hf₂.2
  · funext g
    simp only [castDict, Cover.rd, map_smulₛₗ, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

end GlobalTheory.SerRatRay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTateEpsTateEpsAndNeZero
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.DelEps

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DelEps

theorem isTateEps_tateEps_and_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (χ : kˣ →* ℂˣ), IsSmoothChar χ →
    IsTateEps ψ χ (tateEps ψ χ) ∧ tateEps ψ χ ≠ 0 := by
  intro k _ _ _ _ ψ hψ h1 χ hχ
  obtain ⟨⟨e, he, -⟩, hne⟩ := existsUnique_isTateEps ψ hψ h1 χ hχ
  have hx : ∃ e, IsTateEps ψ χ e := ⟨e, he⟩
  have hs : IsTateEps ψ χ (tateEps ψ χ) := by
    unfold tateEps
    rw [dif_pos hx]
    exact hx.choose_spec
  exact ⟨hs, hne _ hs⟩

end GlobalTheory.DelEps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormVLeOfFix
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

noncomputable section

open scoped Pointwise

namespace GlobalTheory.WeilRestrict

section

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K Ω] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]

def liftG (τ : G K Ω) (hτ : ∀ x : L, τ (algebraMap L Ω x) = algebraMap L Ω x) : G L Ω :=
  AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) hτ

@[simp] theorem liftG_apply (τ : G K Ω) (hτ : ∀ x : L, τ (algebraMap L Ω x) = algebraMap L Ω x)
    (z : Ω) : liftG τ hτ z = τ z := rfl

end

end GlobalTheory.WeilRestrict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallySemistableReducibleUnramifiedSplitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentially_semistable_reducible_unramified_split : RedStep := by
  first | exact @GlobalTheory.PMon.Red.redStep | exact GlobalTheory.PMon.Red.redStep | (intros; apply GlobalTheory.PMon.Red.redStep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteralStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rec_of_rec_literal : DepthZeroCuspidalLL → DepthZeroInduction → LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecLit h rc → IsRec h rc := by
  first | exact @GlobalTheory.LocLanglands.isRec_of_isRecLit | exact GlobalTheory.LocLanglands.isRec_of_isRecLit | (intros; apply GlobalTheory.LocLanglands.isRec_of_isRecLit <;> assumption)
end

