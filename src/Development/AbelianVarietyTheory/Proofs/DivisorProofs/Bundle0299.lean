import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0247
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0267
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0268
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureOverGenericFibreHartogs
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.ClosureHartogs

theorem closure_hart : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R] [IsNoetherianRing R],
    GlobalTheory.GoodEtale.Hart A R R →
    Function.Injective (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
      (τ : D →ₗ[GlobalTheory.LocAcyc.GenFib A R] GlobalTheory.LocAcyc.GenFib A R),
      (∀ c ∈ GlobalTheory.KeyOriginNoeth.closure A R D, ∃ r : R, algebraMap R _ r = τ c) →
    ∀ (a₀ : A), a₀ ≠ 0 → ∀ (n : ℕ) (x y : Fin n → D),
      (∀ i, y i ∈ GlobalTheory.KeyOriginNoeth.closure A R D) →
      (∀ d : D, ∑ i, x i * algebraMap _ D (τ (y i * d)) =
        GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a₀) * d) →
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    GlobalTheory.GoodEtale.Hart A R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  intro A R _ _ _ _ _ hHR hinj D _ _ τ hτC a₀ ha₀ n x y hy hid
  set F := GlobalTheory.LocAcyc.GenFib A R
  set C := GlobalTheory.KeyOriginNoeth.closure A R D
  letI : Algebra R D := (GlobalTheory.KeyOriginNoeth.baseHom A R D).toAlgebra
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  have hbase : ∀ r : R, GlobalTheory.KeyOriginNoeth.baseHom A R D r = algebraMap F D (algebraMap R F r) :=
    fun r => rfl
  have hmemC : ∀ z : D, z ∈ C ↔ IsIntegral R z := fun z => Iff.rfl
  have hsmulC : ∀ (r : R) (c : C), ((r • c : C) : D) = GlobalTheory.KeyOriginNoeth.baseHom A R D r * c :=
    fun r c => rfl
  have hτm : ∀ (f : F) (w : D), τ (algebraMap F D f * w) = f * τ w := by
    intro f w; rw [← Algebra.smul_def, τ.map_smul, smul_eq_mul]

  have hunit : ∀ a : A, a ≠ 0 → IsUnit (algebraMap R F (algebraMap A R a)) := by
    intro a ha
    exact IsLocalization.map_units F
      (⟨algebraMap A R a, Algebra.mem_algebraMapSubmonoid_of_mem (⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩ :
        nonZeroDivisors A)⟩ : Algebra.algebraMapSubmonoid R (nonZeroDivisors A))

  let N : Submodule R D :=
    { carrier := {d | ∀ z ∈ C, ∃ r : R, algebraMap R F r = τ (d * z)}
      add_mem' := by
        intro d₁ d₂ h₁ h₂ z hz
        obtain ⟨r₁, e₁⟩ := h₁ z hz
        obtain ⟨r₂, e₂⟩ := h₂ z hz
        exact ⟨r₁ + r₂, by rw [map_add, e₁, e₂, add_mul, map_add]⟩
      zero_mem' := by
        intro z _
        exact ⟨0, by simp⟩
      smul_mem' := by
        intro r d h z hz
        obtain ⟨r₁, e₁⟩ := h z hz
        refine ⟨r * r₁, ?_⟩
        rw [Algebra.smul_def, mul_assoc]
        change _ = τ (algebraMap F D (algebraMap R F r) * (d * z))
        rw [hτm, ← e₁, map_mul] }
  have hmemN : ∀ d, d ∈ N ↔ ∀ z ∈ C, ∃ r : R, algebraMap R F r = τ (d * z) := fun d => Iff.rfl
  have h1N : (1 : D) ∈ N := by
    intro z hz
    simpa using hτC z hz

  obtain ⟨c₀, hc₀⟩ := hunit a₀ ha₀
  let S : Submodule R D := Submodule.span R (Set.range fun i => algebraMap F D (↑c₀⁻¹ : F) * x i)
  have hNS : N ≤ S := by
    intro d hd
    have hr : ∀ i, ∃ r : R, algebraMap R F r = τ (y i * d) := by
      intro i
      obtain ⟨r, e⟩ := hd (y i) (hy i)
      exact ⟨r, by rw [e, mul_comm]⟩
    choose r hr using hr
    have hd' : d = ∑ i, r i • (algebraMap F D (↑c₀⁻¹ : F) * x i) := by
      have h := hid d
      have h2 : d = algebraMap F D (↑c₀⁻¹ : F) *
          (GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a₀) * d) := by
        rw [hbase, ← mul_assoc, ← map_mul, ← hc₀, Units.inv_mul, map_one, one_mul]
      rw [h2, ← h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, ← hr i]
      change _ = algebraMap F D (algebraMap R F (r i)) * _
      ring
    rw [hd']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hSnoeth : IsNoetherian R S :=
    isNoetherian_of_fg_of_noetherian S (Submodule.fg_span (Set.finite_range _))

  intro a ha m hm
  obtain ⟨c, hc⟩ := hunit a ha
  set ξ : D := algebraMap F D (↑c⁻¹ : F) * (m : D) with hξ

  have hξN : ∀ d ∈ N, ξ * d ∈ N := by
    intro d hd z hz
    have hmz : (m : D) * z ∈ C := C.mul_mem m.2 hz
    obtain ⟨r₀, e₀⟩ := hd _ hmz
    have hdiv : ∃ r'' : R, r₀ = algebraMap A R a • r'' := by
      apply hHR a ha r₀
      intro p hp hph
      obtain ⟨u, hu, m', hm'⟩ := hm p hp hph
      have hm'z : (m' : D) * z ∈ C := C.mul_mem m'.2 hz
      obtain ⟨r', e'⟩ := hd _ hm'z
      refine ⟨u, hu, r', ?_⟩
      apply hinj
      have hv := congrArg Subtype.val hm'
      rw [hsmulC, hsmulC, hbase, hbase] at hv
      rw [smul_eq_mul, smul_eq_mul, map_mul, map_mul, e₀, e', ← hτm, ← hτm]
      congr 1
      linear_combination (d * z) * hv
    obtain ⟨r'', e''⟩ := hdiv
    refine ⟨r'', ?_⟩
    have : ξ * d * z = algebraMap F D (↑c⁻¹ : F) * (d * ((m : D) * z)) := by
      rw [hξ]; ring
    rw [this, hτm, ← e₀, e'', smul_eq_mul, map_mul, ← hc, ← mul_assoc, Units.inv_mul, one_mul]
  have hpow : ∀ k : ℕ, ξ ^ k ∈ N := by
    intro k
    induction k with
    | zero => simpa using h1N
    | succ k ih => rw [pow_succ']; exact hξN _ ih
  have hadj : Subalgebra.toSubmodule (Algebra.adjoin R {ξ}) ≤ S := by
    rw [Algebra.adjoin_eq_span]
    refine le_trans ?_ hNS
    rw [Submodule.span_le]
    intro w hw
    obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.mp hw
    exact hpow k
  have hfg : (Subalgebra.toSubmodule (Algebra.adjoin R {ξ})).FG :=
    isNoetherian_submodule.mp hSnoeth _ hadj
  have hξC : ξ ∈ C :=
    (hmemC ξ).mpr (IsIntegral.of_mem_of_fg _ hfg ξ (Algebra.self_mem_adjoin_singleton R ξ))
  refine ⟨⟨ξ, hξC⟩, Subtype.ext ?_⟩
  rw [hsmulC, hbase]
  change (m : D) = algebraMap F D (algebraMap R F (algebraMap A R a)) * ξ
  rw [hξ, ← mul_assoc, ← map_mul, ← hc, Units.mul_inv, map_one, one_mul]

end GlobalTheory.ClosureHartogs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingAtPrimeOfEtale
section
open GlobalTheory.EtC

open TensorProduct

namespace GlobalTheory

theorem isAlgClosed_fractionRing_atPrime_of_etale : ∀ (T E : Type) [CommRing T] [IsDomain T]
    [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime]
    [IsDomain (Localization.AtPrime P)],
    IsAlgClosed (FractionRing T) → IsAlgClosed (FractionRing (Localization.AtPrime P)) := by
  intro T E _ _ _ _ _ P _ _ hK
  haveI : Module.Flat T (Localization.AtPrime P) := Module.Flat.trans T E (Localization.AtPrime P)
  have hTEp : Function.Injective (algebraMap T (Localization.AtPrime P)) := by
    rw [injective_iff_map_eq_zero]
    intro t ht
    by_contra h0
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := (Localization.AtPrime P))
      (mem_nonZeroDivisors_of_ne_zero h0)
    apply one_ne_zero (α := (Localization.AtPrime P))
    apply hreg
    simp [Algebra.smul_def, ht]
  have hTL : Function.Injective (algebraMap T (FractionRing (Localization.AtPrime P))) := by
    rw [IsScalarTower.algebraMap_eq T (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))]
    exact (IsFractionRing.injective (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))).comp hTEp
  haveI : FaithfulSMul T (FractionRing (Localization.AtPrime P)) := (faithfulSMul_iff_algebraMap_injective T (FractionRing (Localization.AtPrime P))).2 hTL
  letI : Algebra (FractionRing T) (FractionRing (Localization.AtPrime P)) := FractionRing.liftAlgebra T (FractionRing (Localization.AtPrime P))
  haveI : IsScalarTower T (FractionRing T) (FractionRing (Localization.AtPrime P)) := FractionRing.isScalarTower_liftAlgebra T (FractionRing (Localization.AtPrime P))
  haveI : Module.Finite (FractionRing T) ((FractionRing T) ⊗[T] E) := Algebra.FormallyUnramified.finite_of_free (FractionRing T) ((FractionRing T) ⊗[T] E)
  let φ : (FractionRing T) ⊗[T] E →ₐ[(FractionRing T)] (FractionRing (Localization.AtPrime P)) := Algebra.TensorProduct.lift (Algebra.ofId (FractionRing T) (FractionRing (Localization.AtPrime P)))
    (IsScalarTower.toAlgHom T E (FractionRing (Localization.AtPrime P))) (fun _ _ => Commute.all _ _)
  have hE : ∀ e : E, IsIntegral (FractionRing T) (algebraMap E (FractionRing (Localization.AtPrime P)) e) := by
    intro e
    have h1 : IsIntegral (FractionRing T) ((1 : (FractionRing T)) ⊗ₜ[T] e) := Algebra.IsIntegral.isIntegral _
    have h2 := h1.map φ
    simpa [φ] using h2
  have hEp : ∀ x : (Localization.AtPrime P), algebraMap (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) x ∈ algebraicClosure (FractionRing T) (FractionRing (Localization.AtPrime P)) := by
    intro x
    obtain ⟨⟨e, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl x
    have hs : algebraMap E (FractionRing (Localization.AtPrime P)) s ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply E (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))]
      exact (map_ne_zero_iff _ (IsFractionRing.injective (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)))).2
        (IsLocalization.map_units (Localization.AtPrime P) s).ne_zero
    have heq : algebraMap (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) (IsLocalization.mk' (Localization.AtPrime P) e s) =
        algebraMap E (FractionRing (Localization.AtPrime P)) e / algebraMap E (FractionRing (Localization.AtPrime P)) s := by
      rw [eq_div_iff hs, IsScalarTower.algebraMap_apply E (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) e,
        IsScalarTower.algebraMap_apply E (Localization.AtPrime P) (FractionRing (Localization.AtPrime P)) (s : E), ← map_mul, IsLocalization.mk'_spec]
    simp only at heq ⊢
    rw [heq]
    exact div_mem (mem_algebraicClosure_iff.2 (hE e).isAlgebraic)
      (mem_algebraicClosure_iff.2 (hE s).isAlgebraic)
  have hL : (algebraMap (FractionRing T) (FractionRing (Localization.AtPrime P))).IsIntegral := by
    intro z
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (Localization.AtPrime P) z
    exact (mem_algebraicClosure_iff.1 (div_mem (hEp x) (hEp y))).isIntegral
  haveI := hK
  exact IsAlgClosed.of_ringEquiv (FractionRing T) (FractionRing (Localization.AtPrime P))
    (RingEquiv.ofBijective (algebraMap (FractionRing T) (FractionRing (Localization.AtPrime P))) (IsAlgClosed.ringHom_bijective_of_isIntegral _ hL))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedOfIsAnalyticSubset
section
namespace GlobalTheory.LogResInt
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions

noncomputable section

variable {d : ℕ} {X : Type} [TopologicalSpace X]

def HasHoloImm (A : FinHolAtlas d X) (T : Set X) (k : ℕ) : Prop :=
  ∃ (U : Set (Fin k → ℂ)) (g : (Fin k → ℂ) → X) (j : Fin A.n),
    IsOpen U ∧ U.Nonempty ∧ Set.MapsTo g U (T ∩ (A.chart j).source) ∧
    AnalyticOnNhd ℂ (A.chart j ∘ g) U ∧
    ∀ z ∈ U, Function.Injective (fderiv ℂ (A.chart j ∘ g) z)

theorem HasHoloImm.mono {A : FinHolAtlas d X} {T T' : Set X} {k : ℕ} (h : HasHoloImm A T k)
    (hT : T ⊆ T') : HasHoloImm A T' k := by
  obtain ⟨U, g, j, hU, hne, hmaps, han, hinj⟩ := h
  exact ⟨U, g, j, hU, hne, fun z hz => ⟨hT (hmaps hz).1, (hmaps hz).2⟩, han, hinj⟩

theorem holoOn_continuousAt {A : FinHolAtlas d X} {W : Set X} {f : X → ℂ} (hf : A.HoloOn W f)
    {x : X} (hx : x ∈ W) : ContinuousAt f x := by
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
    (hf j (A.chart j x) ⟨(A.chart j).map_source hj, by
      simpa [Set.mem_preimage, (A.chart j).left_inv hj] using hx⟩).continuousAt
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) x :=
    h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem isClosed_of_isAnalyticSubset {A : FinHolAtlas d X} {S : Set X}
    (hS : A.IsAnalyticSubset S) : IsClosed S := by
  refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun x hx => ?_)
  obtain ⟨W, hW, hxW, r, f, hf, hSW⟩ := hS x
  have : ¬ ∀ i, f i x = 0 := fun h => hx (hSW.ge ⟨hxW, h⟩).1
  push_neg at this
  obtain ⟨i, hi⟩ := this
  have hev : ∀ᶠ y in nhds x, f i y ≠ 0 := (holoOn_continuousAt (hf i) hxW).eventually_ne hi
  filter_upwards [hev, hW.mem_nhds hxW] with y hy hyW hyS
  exact hy ((hSW.le ⟨hyS, hyW⟩).2 i)

theorem isAnalyticSubset_inter {A : FinHolAtlas d X} {S T : Set X} (hS : A.IsAnalyticSubset S)
    (hT : A.IsAnalyticSubset T) : A.IsAnalyticSubset (S ∩ T) := by
  intro x
  obtain ⟨W, hW, hxW, r, f, hf, hSW⟩ := hS x
  obtain ⟨W', hW', hxW', r', f', hf', hTW⟩ := hT x
  refine ⟨W ∩ W', hW.inter hW', ⟨hxW, hxW'⟩, r + r', Fin.append f f', fun i => ?_, ?_⟩
  · induction i using Fin.addCases with
    | left i =>
      simp only [Fin.append_left]
      exact fun j => (hf i j).mono fun z hz => ⟨hz.1, hz.2.1⟩
    | right i =>
      simp only [Fin.append_right]
      exact fun j => (hf' i j).mono fun z hz => ⟨hz.1, hz.2.2⟩
  · ext y
    constructor
    · rintro ⟨⟨hyS, hyT⟩, hyW, hyW'⟩
      refine ⟨⟨hyW, hyW'⟩, fun i => ?_⟩
      induction i using Fin.addCases with
      | left i => simpa using (hSW.le ⟨hyS, hyW⟩).2 i
      | right i => simpa using (hTW.le ⟨hyT, hyW'⟩).2 i
    · rintro ⟨⟨hyW, hyW'⟩, h⟩
      exact ⟨⟨(hSW.ge ⟨hyW, fun i => by simpa using h (Fin.castAdd r' i)⟩).1,
        (hTW.ge ⟨hyW', fun i => by simpa using h (Fin.natAdd r i)⟩).1⟩, hyW, hyW'⟩

theorem isSection_zero_iff {A : FinHolAtlas d X} {L : LocPot X} {s : X → X → ℂ}
    (hs : IsSection A L s) {x y : X} (hy : y ∈ L.U x) : s x y = 0 ↔ s y y = 0 := by
  have h := hs.2 x y y ⟨hy, L.mem_U y⟩
  constructor
  · intro h0
    rw [h0, norm_zero, zero_mul] at h
    exact norm_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_right (Real.exp_pos _).ne')
  · intro h0
    rw [h0, norm_zero, zero_mul] at h
    exact norm_eq_zero.1 ((mul_eq_zero.1 h).resolve_right (Real.exp_pos _).ne')

theorem isAnalyticSubset_zero {A : FinHolAtlas d X} {L : LocPot X} {s : X → X → ℂ}
    (hs : IsSection A L s) : A.IsAnalyticSubset {y | s y y = 0} := by
  intro x
  refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hs.1 x, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hy, hyU⟩
    exact ⟨hyU, fun _ => (isSection_zero_iff hs hyU).2 hy⟩
  · rintro ⟨hyU, h⟩
    exact ⟨(isSection_zero_iff hs hyU).1 (h 0), hyU⟩

theorem isAnalyticSubset_boundary {A : FinHolAtlas d X} {m : ℕ} {Λ : Fin m → LocPot X}
    {σ : Fin m → X → X → ℂ} (hσ : ∀ i, IsSection A (Λ i) (σ i)) :
    A.IsAnalyticSubset (boundary σ) := by
  intro x
  refine ⟨⋂ i, (Λ i).U x, isOpen_iInter_of_finite fun i => (Λ i).isOpen_U x,
    Set.mem_iInter.2 fun i => (Λ i).mem_U x, 1, fun _ y => ∏ i, σ i x y, fun _ j => ?_, ?_⟩
  · have h : ∀ i, AnalyticOnNhd ℂ (σ i x ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ⋂ i, (Λ i).U x) :=
      fun i => ((hσ i).1 x j).mono fun z hz => ⟨hz.1, Set.mem_iInter.1 hz.2 i⟩
    exact Finset.univ.analyticOnNhd_fun_prod (fun i _ => h i)
  · ext y
    simp only [boundary, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter,
      Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, hi⟩, hU⟩
      exact ⟨hU, fun _ => ⟨i, (isSection_zero_iff (hσ i) (hU i)).2 hi⟩⟩
    · rintro ⟨hU, h⟩
      obtain ⟨i, hi⟩ := h 0
      exact ⟨⟨i, (isSection_zero_iff (hσ i) (hU i)).1 hi⟩, hU⟩

end

end GlobalTheory.LogResInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedOfLocalIdealPointProperty
section
noncomputable section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.PtClosed

theorem closed_of_points : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (x : Sp R' ⟶ S), P R' x → P R'' (spMap g ≫ x)) →
  (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
     (∀ r ∈ t, P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) → P R' x) →
  (∀ z : S, ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ K : Ideal Γ(S, U),
     ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'), P R' (spMap f ≫ hU.fromSpec) ↔ K ≤ RingHom.ker f) →
  ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧
    ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S), (∃ y : Sp R' ⟶ Z, y ≫ i = x) ↔ P R' x := by
  intro S P hBC hLoc hCov
  have hrep : ∀ (V : S.Opens) (hV : IsAffineOpen V),
      Represents (ptQ P V hV) (killIdeal (ptQ P V hV)) := by
    intro V hV
    obtain ⟨s, hs, hJ⟩ := GlobalTheory.T.exists_basicOpen_cover_idealRepresents S P hCov V hV
    have hQbc : ∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'')
        (f : Γ(S, V) →+* R'), ptQ P V hV R' f → ptQ P V hV R'' (g.comp f) := by
      intro R' _ R'' _ g f hf
      have := hBC R' R'' g _ hf
      simpa [ptQ, spMap, CommRingCat.ofHom_comp, Spec.map_comp] using this
    have hQloc : ∀ (R' : Type) [CommRing R'] (f : Γ(S, V) →+* R') (t : Finset R'),
        Ideal.span (t : Set R') = ⊤ →
        (∀ r ∈ t, ptQ P V hV (Localization.Away r) ((algebraMap R' (Localization.Away r)).comp f)) →
        ptQ P V hV R' f := by
      intro R' _ f t ht H
      refine hLoc R' _ t ht fun r hr ↦ ?_
      have := H r hr
      simpa [ptQ, spMap, CommRingCat.ofHom_comp, Spec.map_comp] using this
    obtain ⟨J, hJ'⟩ := GlobalTheory.T.idealRepresents_of_away_cover Γ(S, V) (ptQ P V hV) hQbc hQloc s hs hJ
    exact represents_killIdeal hJ'
  let I : S.IdealSheafData :=
    { ideal := fun V ↦ killIdeal (ptQ P V.1 V.2)
      map_ideal_basicOpen := fun U f ↦ by
        have h1 := represents_restrict S P U.1 (S.basicOpen f) U.2 (U.2.basicOpen f) (S.basicOpen_le f) _
          (hrep U.1 U.2)
        exact (killIdeal_eq h1).symm }
  refine ⟨I.subscheme, I.subschemeι, inferInstance, fun R' _ x ↦ ?_⟩
  have key : I ≤ x.ker ↔ P R' x := by
    rw [Scheme.Hom.ker, Scheme.IdealSheafData.le_ofIdeals_iff]
    constructor
    · intro h
      exact GlobalTheory.T.affinePointProperty_of_le_ker_app S P hLoc hrep R' x fun V hV ↦ h ⟨V, hV⟩
    · intro h V
      exact GlobalTheory.T.idealKilledByRingMapsWithProperty_le_ker_app S P hBC R' x h V.1 V.2
  rw [← key]
  constructor
  · rintro ⟨y, rfl⟩
    have := y.le_ker_comp I.subschemeι
    rwa [Scheme.IdealSheafData.ker_subschemeι] at this
  · intro h
    exact ⟨IsClosedImmersion.lift I.subschemeι x (by rwa [Scheme.IdealSheafData.ker_subschemeι]),
      IsClosedImmersion.lift_fac _ _ _⟩
end GlobalTheory.PtClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitLeftFuncAndCechConerveLevels
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isColimit_leftFunc_and_cechConerve_levels :
    ∀ (J : Type) [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{0}) (c : Cocone D), IsColimit c →
      Nonempty (IsColimit (Arrow.leftFunc.mapCocone c)) ∧
      ∀ k : SimplexCategory, Nonempty (IsColimit ((CosimplicialObject.cechConerve ⋙
        (evaluation SimplexCategory CommRingCat.{0}).obj k).mapCocone c)) := by
  intro J _ D c hc
  refine ⟨⟨isColimitOfPreserves Arrow.leftFunc hc⟩, fun k => ⟨?_⟩⟩
  have e : (CosimplicialObject.cechConerve ⋙ (evaluation SimplexCategory CommRingCat.{0}).obj k) =
      CosimplicialObject.augmentedCechConerve ⋙ CosimplicialObject.Augmented.drop ⋙
        (evaluation SimplexCategory CommRingCat.{0}).obj k := rfl
  rw [e]
  have h1 : PreservesColimitsOfSize.{0, 0} (CosimplicialObject.augmentedCechConerve (C := CommRingCat.{0})) :=
    CosimplicialObject.cechConerveAdjunction.leftAdjoint_preservesColimits
  have h0 : PreservesColimitsOfShape J (CosimplicialObject.const CommRingCat.{0}) :=
    preservesColimitsOfShape_of_evaluation _ J fun m => by
      have : PreservesColimitsOfShape J (𝟭 CommRingCat.{0}) := inferInstance
      exact this
  have h2 : PreservesColimitsOfShape J (CosimplicialObject.Augmented.drop (C := CommRingCat.{0})) :=
    Comma.preservesColimitsOfShape_snd
  have h3 : PreservesColimitsOfShape J ((evaluation SimplexCategory CommRingCat.{0}).obj k) := inferInstance
  exact @isColimitOfPreserves _ _ _ _ _ _ _ ((evaluation SimplexCategory CommRingCat.{0}).obj k) _
    (isColimitOfPreserves CosimplicialObject.Augmented.drop
      (isColimitOfPreserves CosimplicialObject.augmentedCechConerve hc)) h3.preservesColimit

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPiUpperHalfPlaneImBoundsStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_im_bounds_of_isCompact_upperHalfPlane : ∀ (ι : Type) [Fintype ι] (L : Set (ι → ℂ)), IsCompact L → (∀ z ∈ L, ∀ i, 0 < (z i).im) →
    ∃ c c' : ℝ, 0 < c ∧ ∀ z ∈ L, ∀ i, c ≤ (z i).im ∧ (z i).im ≤ c' := by
  first | exact @GlobalTheory.isCompact_pi_upperHalfPlane_im_bounds | exact GlobalTheory.isCompact_pi_upperHalfPlane_im_bounds | (intros; apply GlobalTheory.isCompact_pi_upperHalfPlane_im_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldStalkImageOfGenericPointStatement
section
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isField_stalk_imageOfGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z], IsOpen (Set.range π) →
    IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) := by
  first | exact @GlobalTheory.NormSheafDescent.isField_stalk_genPt | exact GlobalTheory.NormSheafDescent.isField_stalk_genPt | (intros; apply GlobalTheory.NormSheafDescent.isField_stalk_genPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOfFinOrderPicOfIsReducedFiniteInt
section
namespace GlobalTheory.PicReducedTors

theorem pic_isOfFinOrder : ∀ (B : Type) [CommRing B] [IsReduced B] [Module.Finite ℤ B] (M : CommRing.Pic B),
    IsOfFinOrder M := by
  intro B _ _ _ M
  haveI : IsNoetherian ℤ B := inferInstance
  haveI : IsNoetherianRing B := isNoetherian_of_tower ℤ inferInstance
  haveI : Finite (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).to_subtype
  let φ := Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)
  haveI : Module.Finite ℤ ((P : minimalPrimes B) → B ⧸ (P : Ideal B)) := inferInstance
  obtain ⟨n, hn, hmul⟩ := GlobalTheory.T.exists_nat_mul_mem_range_pi_quotient_minimalPrimes' B
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have hrad : b ∈ (⊥ : Ideal B).radical := by
      rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
      intro P hP
      have := congrFun hb ⟨P, hP⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact this
    obtain ⟨k, hk⟩ := hrad
    exact IsReduced.eq_zero b ⟨k, by simpa using hk⟩
  refine GlobalTheory.T.isOfFinOrder_of_isOfFinOrder_pic_mapRingHom B _ φ n hinj hn hmul M ?_
  refine GlobalTheory.T.pic_pi_isOfFinOrder' _ _ (fun P N => ?_) _
  haveI : (P : Ideal B).IsPrime := P.2.1.1
  exact GlobalTheory.T.pic_isOfFinOrder_of_finite_int' _ N

end GlobalTheory.PicReducedTors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfForallIsPushoutAppStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_of_isAffine_of_forall_isPushout_appLE : ∀ (X Y S S' : Scheme.{0}) (j : X ⟶ Y) (p : X ⟶ S') (y : Y ⟶ S) (q : S' ⟶ S), IsAffine S → IsAffine S' → IsAffineHom j → j ≫ y = p ≫ q → (∀ V : Y.Opens, IsAffineOpen V → IsPushout (y.appLE ⊤ V (fun _ _ => trivial)) q.appTop (j.app V) (p.appLE ⊤ (j ⁻¹ᵁ V) (fun _ _ => trivial))) → IsPullback j p y q := by
  first | exact @GlobalTheory.PushoutSquare.isPullback_of_forall_isPushout_app | exact GlobalTheory.PushoutSquare.isPullback_of_forall_isPushout_app | (intros; apply GlobalTheory.PushoutSquare.isPullback_of_forall_isPushout_app <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSMulRegularOfEtalePuncturedOfDepthPosDomainStatement
section
open IsLocalRing TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos_domain' : ∀ (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsDomain S] (A : Type) [CommRing A] [Algebra S A], ReciprocityTheory.CA.ModDepthGE S A 1 → (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A)) → ∀ s : S, s ≠ 0 → IsSMulRegular A s := by
  first | exact @GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos_domain | exact GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos_domain | (intros; apply GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos_domain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSMulRegularOfEtalePuncturedOfDepthPosStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSMulRegular_of_etale_punctured_of_depth_pos' : ∀ (R A : Type) [CommRing R] [IsRegularLocalRing R] [CommRing A] [Algebra R A] [Module.Finite R A], ReciprocityTheory.CA.ModDepthGE R A 1 → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ∀ f : R, f ≠ 0 → IsSMulRegular A f := by
  first | exact @GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos | exact GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos | (intros; apply GlobalTheory.isSMulRegular_of_etale_punctured_of_depth_pos <;> assumption)
end

