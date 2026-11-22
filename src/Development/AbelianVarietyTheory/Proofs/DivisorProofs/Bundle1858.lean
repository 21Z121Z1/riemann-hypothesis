import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1829
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1827
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.Bundle0004
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Formalism.LocalToGlobal.Divisibility.Bundle0002
import Formalism.LocalToGlobal.Columns.Bundle0014
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0253

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexIdealRankOneTensorImageEqMap
section
set_option autoImplicit false

noncomputable section

open NumberField

namespace GlobalTheory.IdxTensor
theorem cut_idxmap : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    [IsScalarTower (𝓞 F) F V] (p : ℕ) (φ : (Fin p → F) →ₗ[F] V), Function.Injective φ →
    ∀ (L N : Submodule (𝓞 F) (Fin p → F)),
    GlobalTheory.FlatCM.idx F p (L.map (φ.restrictScalars (𝓞 F))) (N.map (φ.restrictScalars (𝓞 F))) =
      (GlobalTheory.IdxTensor.dets F p N).colon (GlobalTheory.IdxTensor.dets F p L : Set F) := GlobalTheory.T.latticeDeterminantIndexIdeal_map_injective_eq_colon

theorem cut_detsspan : ∀ {F : Type} [Field F] [NumberField F] (p : ℕ) (S : Set (Fin p → F)),
    GlobalTheory.IdxTensor.dets F p (Submodule.span (𝓞 F) S) =
      Submodule.span (𝓞 F) {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ S) ∧ d = (Matrix.of y).det} := GlobalTheory.T.latticeDeterminantSpan_span_eq_generator_dets

theorem cut_rankone : ∀ {K : Type} [Field K] [NumberField K] {m : ℕ} (ell : Submodule (𝓞 K) (Fin m → K)),
    ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → ell.FG →
    ∃ v : Fin m → K, v ≠ 0 ∧ ∃ 𝔟 : Submodule (𝓞 K) K, 𝔟.FG ∧ 𝔟 ≠ ⊥ ∧
      ∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v := GlobalTheory.T.rankOne_fg_lattice_eq_fractionalIdeal_smul_vector

theorem cut_linindep : ∀ {K : Type} [Field K] [NumberField K] {p m n : ℕ} (ell : Submodule (𝓞 K) (Fin m → K))
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (v : Fin m → K), v ≠ 0 → ∀ (𝔟 : Submodule (𝓞 K) K),
    𝔟 ≠ ⊥ → (∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v) → (∀ a, Function.Injective (M a)) →
    iSupIndep (fun a => Submodule.span K
      ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) →
    LinearIndependent K (fun a => M a v) := GlobalTheory.T.linearIndependent_images_of_iSupIndep_rankOne

theorem cut_cancel : ∀ {K : Type} [Field K] [NumberField K] (𝔟 : Submodule (𝓞 K) K), 𝔟.FG → 𝔟 ≠ ⊥ →
    ∀ (p : ℕ) (A N : Submodule (𝓞 K) K),
    (𝔟 ^ p * N).colon ((𝔟 ^ p * A : Submodule (𝓞 K) K) : Set K) = N.colon (A : Set K) := GlobalTheory.T.colon_pow_mul_cancel_fg_fractional

theorem cut_extend : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K), (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
    ∀ (A : Submodule (𝓞 E) E), A.FG → (1 : E) ∈ A →
    (1 : Submodule (𝓞 K) K).colon (Submodule.span (𝓞 K) (τE '' A) : Set K) =
      ((1 : Submodule (𝓞 E) E).colon (A : Set E)).map τ := GlobalTheory.T.colon_one_span_image_eq_map_colon

theorem cut_twistgens : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K), (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) → ∀ (p : ℕ)
    (𝔟 : Submodule (𝓞 K) K) (Λ : Submodule (𝓞 E) (Fin p → E)),
    Submodule.span (𝓞 K) {d | ∃ y : Fin p → Fin p → K,
        (∀ i, y i ∈ {x : Fin p → K | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}) ∧ d = (Matrix.of y).det} =
      𝔟 ^ p * Submodule.span (𝓞 K) (τE '' GlobalTheory.IdxTensor.dets E p Λ) := GlobalTheory.T.span_scaled_mapped_row_dets_eq_pow_mul_span

theorem span_image_one {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K) (hτ : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) :
    Submodule.span (𝓞 K) (τE '' (1 : Submodule (𝓞 E) E)) = 1 := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.mem_one.1 hy
    exact Submodule.mem_one.2 ⟨τ z, (hτ z).symm⟩
  · rw [Submodule.one_le]
    apply Submodule.subset_span
    exact ⟨1, Submodule.mem_one.2 ⟨1, map_one _⟩, map_one τE⟩

theorem one_mem_dets {F : Type} [Field F] [NumberField F] (p : ℕ) (L : Submodule (𝓞 F) (Fin p → F))
    (h : ∀ a, (Pi.single a (1 : F) : Fin p → F) ∈ L) : (1 : F) ∈ dets F p L := by
  unfold dets
  apply Submodule.subset_span
  refine ⟨fun a => Pi.single a 1, h, ?_⟩
  have hI : Matrix.of (fun a : Fin p => (Pi.single a (1 : F) : Fin p → F)) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Pi.single_apply, Matrix.one_apply, hij, Ne.symm hij]
  rw [hI, Matrix.det_one]

theorem dets_std {F : Type} [Field F] [NumberField F] (p : ℕ) :
    dets F p (Submodule.span (𝓞 F) (Set.range fun a => (Pi.single a (1 : F) : Fin p → F))) = 1 := by
  rw [cut_detsspan]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro d ⟨y, hy, rfl⟩
    choose f hf using fun i => Set.mem_range.1 (hy i)
    have hM : Matrix.of y =
        (Matrix.of fun i j => (Pi.single (f i) (1 : 𝓞 F) : Fin p → 𝓞 F) j).map (algebraMap (𝓞 F) F) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.map_apply]
      rw [← hf i]
      by_cases hij : j = f i
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    rw [hM]
    exact Submodule.mem_one.2 ⟨_, RingHom.map_det _ _⟩
  · rw [Submodule.one_le]
    apply Submodule.subset_span
    refine ⟨fun a => Pi.single a 1, fun i => ⟨i, rfl⟩, ?_⟩
    have hI : Matrix.of (fun a : Fin p => (Pi.single a (1 : F) : Fin p → F)) = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [Pi.single_apply, Matrix.one_apply, hij, Ne.symm hij]
    rw [hI, Matrix.det_one]

theorem big_eq_map {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (τE : E →+* K) {p m n : ℕ}
    (ell : Submodule (𝓞 K) (Fin m → K)) (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K)))
    (Λ : Submodule (𝓞 E) (Fin p → E)) (v : Fin m → K) (𝔟 : Submodule (𝓞 K) K)
    (hell : ∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v) :
    Submodule.span (𝓞 K) {w | ∃ c ∈ Λ, ∃ e ∈ ell, w = ∑ a, τE (c a) • M a e} =
      (Submodule.span (𝓞 K) {x | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}).map
        ((Fintype.linearCombination K (fun a => M a v)).restrictScalars (𝓞 K)) := by
  rw [Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨c, hc, e, he, rfl⟩
    obtain ⟨β, hβ, rfl⟩ := (hell e).1 he
    refine ⟨β • fun a => τE (c a), ⟨β, hβ, c, hc, rfl⟩, ?_⟩
    rw [LinearMap.coe_restrictScalars, Fintype.linearCombination_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.smul_apply, map_smul, smul_smul, smul_eq_mul, mul_comm]
  · rintro ⟨x, ⟨β, hβ, c, hc, rfl⟩, rfl⟩
    refine ⟨c, hc, β • v, (hell _).2 ⟨β, hβ, rfl⟩, ?_⟩
    rw [LinearMap.coe_restrictScalars, Fintype.linearCombination_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Pi.smul_apply, map_smul, smul_smul, smul_eq_mul, mul_comm]

private lemma sum_single_smul_eq_apply {E K : Type} [Field E] [Field K] (τE : E →+* K) {p m n : ℕ}
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (b : Fin p) (e : Fin m → K) :
    ∑ a, τE ((Pi.single b (1 : E) : Fin p → E) a) • M a e = M b e := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro a _ hab
    simp [Pi.single_apply, hab]
  · simp

theorem small_eq_big_std {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K) (hτ : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) {p m n : ℕ}
    (ell : Submodule (𝓞 K) (Fin m → K)) (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) :
    (⨆ a, ell.map ((M a).restrictScalars (𝓞 K))) =
      Submodule.span (𝓞 K) {w | ∃ c ∈ Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)),
        ∃ e ∈ ell, w = ∑ a, τE (c a) • M a e} := by
  apply le_antisymm
  · refine iSup_le fun b => ?_
    rintro w ⟨e, he, rfl⟩
    exact Submodule.subset_span
      ⟨Pi.single b 1, Submodule.subset_span ⟨b, rfl⟩, e, he, (sum_single_smul_eq_apply τE M b e).symm⟩
  · rw [Submodule.span_le]
    rintro w ⟨c, hc, e, he, rfl⟩
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      beta_reduce
      rw [sum_single_smul_eq_apply τE M b e]
      exact Submodule.mem_iSup_of_mem b ⟨e, he, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
      exact add_mem hx hy
    | smul r x _ hx =>
      have key : ∀ a, τE ((r • x) a) • M a e = τ r • (τE (x a) • M a e) := by
        intro a
        rw [Pi.smul_apply, Algebra.smul_def r (x a), map_mul, mul_smul, ← algebraMap_smul K (τ r)]
        congr 1
        exact hτ r
      rw [Finset.sum_congr rfl (fun a _ => key a), ← Finset.smul_sum]
      exact Submodule.smul_mem _ _ hx

theorem dets_fg {F : Type} [Field F] [NumberField F] (p : ℕ) (L : Submodule (𝓞 F) (Fin p → F)) (h : L.FG) :
    (dets F p L).FG := by
  obtain ⟨S, rfl⟩ := h
  rw [cut_detsspan]
  apply Submodule.fg_span
  refine ((Set.Finite.pi (fun _ : Fin p => S.finite_toSet)).image
    (fun y : Fin p → Fin p → F => (Matrix.of y).det)).subset ?_
  rintro d ⟨y, hy, rfl⟩
  exact ⟨y, fun i _ => hy i, rfl⟩

theorem dets_twist {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K) (hτ : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) (p : ℕ)
    (𝔟 : Submodule (𝓞 K) K) (Λ : Submodule (𝓞 E) (Fin p → E)) :
    dets K p (Submodule.span (𝓞 K) {x | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}) =
      𝔟 ^ p * Submodule.span (𝓞 K) (τE '' dets E p Λ) := by
  rw [cut_detsspan]
  exact cut_twistgens τ τE hτ p 𝔟 Λ

theorem idx_image_eq_map : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K),
    (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) → ∀ (p m n : ℕ) (ell : Submodule (𝓞 K) (Fin m → K))
    (M : Fin p → ((Fin m → K) →ₗ[K] (Fin n → K))) (Λ : Submodule (𝓞 E) (Fin p → E)),
    ell.FG → ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → (∀ a, Function.Injective (M a)) →
    iSupIndep (fun a => Submodule.span K ((ell.map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K))) →
    Λ.FG → (∀ x : Fin p → 𝓞 E, (fun a => (x a : E)) ∈ Λ) →
    GlobalTheory.FlatCM.idx K p (Submodule.span (𝓞 K) {w | ∃ c ∈ Λ, ∃ e ∈ ell, w = ∑ a, τE (c a) • M a e})
                 (⨆ a, ell.map ((M a).restrictScalars (𝓞 K))) =
      (GlobalTheory.FlatCM.idx E p Λ (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)))).map τ := by
  intro E K _ _ _ _ τ τE hτ p m n ell M Λ hfg hrk hinj hind hΛfg hΛ
  obtain ⟨v, hv, 𝔟, h𝔟fg, h𝔟, hell⟩ := cut_rankone ell hrk hfg
  have hφ : Function.Injective (Fintype.linearCombination K (fun a => M a v)) :=
    (cut_linindep ell M v hv 𝔟 h𝔟 hell hinj hind).fintypeLinearCombination_injective
  have hsing : ∀ a, (Pi.single a (1 : E) : Fin p → E) ∈ Λ := by
    intro a
    have h1 := hΛ (Pi.single a 1)
    convert h1 using 1
    funext b
    by_cases hab : b = a
    · subst hab; simp
    · simp [Pi.single_apply, hab]
  have hD1 : (1 : E) ∈ GlobalTheory.IdxTensor.dets E p Λ := one_mem_dets p Λ hsing
  have hDfg : (GlobalTheory.IdxTensor.dets E p Λ).FG := dets_fg p Λ hΛfg
  have hR := cut_idxmap (V := Fin p → E) p (LinearMap.id) Function.injective_id Λ
    (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a (1 : E) : Fin p → E)))
  have hmapid : ∀ L : Submodule (𝓞 E) (Fin p → E),
      L.map ((LinearMap.id : (Fin p → E) →ₗ[E] (Fin p → E)).restrictScalars (𝓞 E)) = L := by
    intro L
    ext x
    simp
  rw [hmapid, hmapid] at hR
  rw [hR, small_eq_big_std τ τE hτ ell M, big_eq_map τE ell M Λ v 𝔟 hell, big_eq_map τE ell M _ v 𝔟 hell,
    cut_idxmap p _ hφ, dets_twist τ τE hτ, dets_twist τ τE hτ, dets_std, span_image_one τ τE hτ,
    cut_cancel 𝔟 h𝔟fg h𝔟 p _ 1]
  exact cut_extend τ τE hτ _ hDfg hD1

end GlobalTheory.IdxTensor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartAlgebraMapLiftV
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.BigDat

section Halves

variable {D : D7}

theorem hO_cA_smul (S₁ S₂ : HSp D) (a : AE D) (z y : WO S₁ S₂) : hO S₁ S₂ z (cA D a • y) = hO S₁ S₂ (a • z) y := by
  unfold hO
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun s _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, GlobalTheory.DualPairCheck.cA_cA]
  ring

theorem symplO_cA_smul (S₁ S₂ : HSp D) (a : AE D) (z y : WO S₁ S₂) :
    symplO S₁ S₂ z (cA D a • y) = symplO S₁ S₂ (a • z) y := by
  unfold symplO
  rw [hO_cA_smul]

theorem symplO_zero_right' (S₁ S₂ : HSp D) (z : WO S₁ S₂) : symplO S₁ S₂ z 0 = 0 := by
  simp [symplO, hO]

theorem isHalf_smul_self {m n : ℕ} {b : AE D} (hb : b * b = b) (x : Matrix (Fin m) (Fin n) (AE D)) : IsHalf b (b • x) :=
  fun p q => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hb]

theorem smul_of_isHalf {m n : ℕ} {b : AE D} {x : Matrix (Fin m) (Fin n) (AE D)} (hx : IsHalf b x) : b • x = x :=
  Matrix.ext fun p q => hx p q

theorem smul_eq_zero_of_isHalf (v : Pl D.host.F) {b : AE D}
    (hb : b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = b) {m n : ℕ} {x : Matrix (Fin m) (Fin n) (AE D)}
    (hx : IsHalf b x) (c : AF D.host.F) (hc : evFin D.host.F v c = 0) : c • x = 0 := by
  have h0 : c * GlobalTheory.LatVac.liftV v 1 = 0 := GlobalTheory.LatVac.at_liftV v 1 c hc
  ext p q
  rw [Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def]
  have e : algebraMap (AF D.host.F) (AE D) c * x p q =
      b * algebraMap (AF D.host.F) (AE D) (c * GlobalTheory.LatVac.liftV v 1) * x p q := by
    conv_lhs => rw [← hx p q, ← hb]
    rw [map_mul]
    ring
  rw [e, h0, map_zero, mul_zero, zero_mul]

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem at_of_mixHalf (e : Num G i j) (v : Pl D.host.F) {b : AE D}
    (hb : b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = b) {u : Pt G i j} (hu : u ∈ mixHalf e b) :
    At (evFin D.host.F v) u := by
  intro c hc
  apply (maps e).injective
  rw [map_smul, map_zero, maps_apply, Prod.smul_mk, smul_eq_zero_of_isHalf v hb hu.1 c hc,
    smul_eq_zero_of_isHalf v hb hu.2 c hc, Prod.mk_zero_zero]

theorem ofMaps_smul_mem (e : Num G i j) {b : AE D} (hb : b * b = b) (x₁ : HomV G i j) (x₂ : HomW G i j) :
    ofMaps e (b • x₁, b • x₂) ∈ mixHalf e b := by
  refine ⟨?_, ?_⟩
  · show IsHalf b (mapV e (ofMaps e _))
    rw [mapV_ofMaps]
    exact isHalf_smul_self hb _
  · show IsHalf b (mapW e (ofMaps e _))
    rw [mapW_ofMaps]
    exact isHalf_smul_self hb _

theorem ofMaps_add_ofMaps (e : Num G i j) (v : Pl D.host.F) {a : AE D}
    (hsum : a + cA D a = algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1)) {u : Pt G i j}
    (hu : At (evFin D.host.F v) u) :
    ofMaps e (a • mapV e u, a • mapW e u) + ofMaps e (cA D a • mapV e u, cA D a • mapW e u) = u := by
  have h1 : (1 - GlobalTheory.LatVac.liftV v 1) • u = 0 :=
    hu _ (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
  have hℓu : GlobalTheory.LatVac.liftV v 1 • u = u := by
    rw [sub_smul, one_smul, sub_eq_zero] at h1
    exact h1.symm
  apply (maps e).injective
  refine Prod.ext ?_ ?_
  · show mapV e (_ + _) = mapV e u
    rw [mapV_add, mapV_ofMaps, mapV_ofMaps, ← add_smul, hsum, algebraMap_smul, ← mapV_smul, hℓu]
  · show mapW e (_ + _) = mapW e u
    rw [mapW_add, mapW_ofMaps, mapW_ofMaps, ← add_smul, hsum, algebraMap_smul, ← mapW_smul, hℓu]

theorem infPart_algebraMap_liftV (v : Pl D.host.F) :
    infPart D (algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1)) = 0 :=
  GlobalTheory.LatVac.infPart_pair (GlobalTheory.AdelicU.singleFin v 1) 1

theorem map_infPart_of_isHalf (v : Pl D.host.F) {b : AE D}
    (hb : b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = b) {m n : ℕ} {x : Matrix (Fin m) (Fin n) (AE D)}
    (hx : IsHalf b x) : x.map (infPart D) = 0 := by
  ext p q
  rw [Matrix.map_apply, Matrix.zero_apply, ← hx p q, ← hb, map_mul, map_mul, infPart_algebraMap_liftV, mul_zero, zero_mul]

theorem mapV_mem_latV_of_char (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram)
    (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e) {ψ : AddChar (AF D.host.F) ℂ} (hstd : IsStdChar D ψ (-1))
    (hS : IsSelfDualC (negSp (spW G i j)) (G.Λ (.grid (i + 1) (j + 1))))
    (hT : IsSelfDualC (spV G i j) (G.Λ (.grid i (j + 1)))) (v : Pl D.host.F) {a : AE D}
    (ha1 : a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = a) (hcc : cA D a * cA D a = cA D a)
    (hc1 : cA D a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = cA D a) (hfc : finPart D (cA D a) ∈ intAE D)
    {x : Pt G i j} (hx : x ∈ mixHalf e a)
    (hψ : ∀ y ∈ latPt e v, y ∈ mixHalf e (cA D a) → ψ (sympPt Γ x y) = 1) : mapV e x ∈ latV G i j := by
  refine GlobalTheory.LatVac.mem_of_char hstd hS hT (map_infPart_of_isHalf v ha1 hx.1) fun l hl => ?_
  have hy : ofMaps e (cA D a • l, (0 : HomW G i j)) ∈ mixHalf e (cA D a) := by
    refine ⟨?_, ?_⟩
    · show IsHalf _ (mapV e (ofMaps e _))
      rw [mapV_ofMaps]
      exact isHalf_smul_self hcc _
    · show IsHalf _ (mapW e (ofMaps e _))
      rw [mapW_ofMaps]
      exact fun p q => mul_zero _
  have hyl : ofMaps e (cA D a • l, (0 : HomW G i j)) ∈ latPt e v := by
    refine ⟨at_of_mixHalf e v hc1 hy, ?_, ?_⟩
    · show mapV e (ofMaps e _) ∈ latV G i j
      rw [mapV_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfc l hl
    · show mapW e (ofMaps e _) ∈ latW G i j
      rw [mapW_ofMaps]
      exact zero_mem _
  have h := hψ _ hyl hy
  rw [symp_eq e Γ hW hWW, mapV_ofMaps, mapW_ofMaps, symplO_cA_smul, smul_of_isHalf hx.1, symplO_zero_right',
    add_zero] at h
  exact h

theorem mapW_mem_latW_of_char (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram)
    (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e) {ψ : AddChar (AF D.host.F) ℂ} (hstd : IsStdChar D ψ (-1))
    (hS : IsSelfDualC (spV₁ G i j) (G.Λ (.grid (i + 1) j)))
    (hT : IsSelfDualC (spW G i j) (G.Λ (.grid (i + 1) (j + 1)))) (v : Pl D.host.F) {a : AE D}
    (ha1 : a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = a) (hcc : cA D a * cA D a = cA D a)
    (hc1 : cA D a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = cA D a) (hfc : finPart D (cA D a) ∈ intAE D)
    {x : Pt G i j} (hx : x ∈ mixHalf e a)
    (hψ : ∀ y ∈ latPt e v, y ∈ mixHalf e (cA D a) → ψ (sympPt Γ x y) = 1) : mapW e x ∈ latW G i j := by
  refine GlobalTheory.LatVac.mem_of_char hstd hS hT (map_infPart_of_isHalf v ha1 hx.2) fun l hl => ?_
  have hy : ofMaps e ((0 : HomV G i j), cA D a • l) ∈ mixHalf e (cA D a) := by
    refine ⟨?_, ?_⟩
    · show IsHalf _ (mapV e (ofMaps e _))
      rw [mapV_ofMaps]
      exact fun p q => mul_zero _
    · show IsHalf _ (mapW e (ofMaps e _))
      rw [mapW_ofMaps]
      exact isHalf_smul_self hcc _
  have hyl : ofMaps e ((0 : HomV G i j), cA D a • l) ∈ latPt e v := by
    refine ⟨at_of_mixHalf e v hc1 hy, ?_, ?_⟩
    · show mapV e (ofMaps e _) ∈ latV G i j
      rw [mapV_ofMaps]
      exact zero_mem _
    · show mapW e (ofMaps e _) ∈ latW G i j
      rw [mapW_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfc l hl
  have h := hψ _ hyl hy
  rw [symp_eq e Γ hW hWW, mapV_ofMaps, mapW_ofMaps, symplO_cA_smul, smul_of_isHalf hx.2, symplO_zero_right',
    zero_add] at h
  exact h

theorem halves_split : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (i j : Fin D.R.m) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j),
    Γ.V.J = (1 : D.host.E) • (spW G i j).gram → Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e → ∀ (v : Pl D.host.F) (a : AE D), IsSplitIdem D a →
    a + cA D a = algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) →
    (∀ u ∈ mixHalf e a, At (evFin D.host.F v) u) ∧ (∀ u ∈ mixHalf e (cA D a), At (evFin D.host.F v) u) ∧
    (∀ u : Pt G i j, At (evFin D.host.F v) u → ∃ x ∈ mixHalf e a, ∃ y ∈ mixHalf e (cA D a), u = x + y) ∧
    (∀ x ∈ mixHalf e a, (∀ y ∈ latPt e v, y ∈ mixHalf e (cA D a) → W.ψ (sympPt Γ x y) = 1) → x ∈ latPt e v) ∧
    ∀ u : Pt G i j, ofMaps e (a • mapV e u, a • mapW e u) ∈ mixHalf e a ∧
      (∀ y ∈ mixHalf e (cA D a), sympPt Γ u y = sympPt Γ (ofMaps e (a • mapV e u, a • mapW e u)) y) ∧
      (mapV e u ∈ latV G i j → mapW e u ∈ latW G i j → ofMaps e (a • mapV e u, a • mapW e u) ∈ latPt e v) := by
  intro D T L sc G μ₀ hL W i j e Γ hW hWW v a ha hsum
  obtain ⟨haa, hac, -⟩ := ha
  have hcc : cA D a * cA D a = cA D a := by rw [← map_mul, haa]
  have hca : cA D a * a = 0 := by rw [mul_comm, hac]
  have ha1 : a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = a := by
    rw [← hsum, mul_add, haa, hac, add_zero]
  have hc1 : cA D a * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v 1) = cA D a := by
    rw [← hsum, mul_add, hca, hcc, zero_add]
  have hfa : finPart D a ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, haa])
  have hfc : finPart D (cA D a) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hcc])
  have hS : IsSelfDualC (negSp (spW G i j)) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) :=
    isSelfDualC_neg (node_isV G hL (X := .grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨i.2, j.2⟩).sd
  have hT : IsSelfDualC (spV G i j) (G.Λ (.grid (i : ℕ) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have hS₁ : IsSelfDualC (spV₁ G i j) (G.Λ (.grid ((i : ℕ) + 1) (j : ℕ))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  have hT₁ : IsSelfDualC (spW G i j) (G.Λ (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))) :=
    (node_isV G hL (X := .grid ((i : ℕ) + 1) ((j : ℕ) + 1)) ⟨i.2, j.2⟩).sd
  refine ⟨fun u hu => at_of_mixHalf e v ha1 hu, fun u hu => at_of_mixHalf e v hc1 hu, fun u hu =>
    ⟨_, ofMaps_smul_mem e haa _ _, _, ofMaps_smul_mem e hcc _ _, (ofMaps_add_ofMaps e v hsum hu).symm⟩,
    fun x hx hψ => ⟨at_of_mixHalf e v ha1 hx,
      mapV_mem_latV_of_char e Γ hW hWW W.ψ_std hS hT v ha1 hcc hc1 hfc hx hψ,
      mapW_mem_latW_of_char e Γ hW hWW W.ψ_std hS₁ hT₁ v ha1 hcc hc1 hfc hx hψ⟩, fun u => ?_⟩
  refine ⟨ofMaps_smul_mem e haa _ _, fun y hy => ?_, fun hV hW' => ?_⟩
  · rw [symp_eq e Γ hW hWW, symp_eq e Γ hW hWW, mapV_ofMaps, mapW_ofMaps, ← symplO_cA_smul, ← symplO_cA_smul,
      smul_of_isHalf hy.1, smul_of_isHalf hy.2]
  · refine ⟨at_of_mixHalf e v ha1 (ofMaps_smul_mem e haa _ _), ?_, ?_⟩
    · show mapV e (ofMaps e _) ∈ latV G i j
      rw [mapV_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfa _ hV
    · show mapW e (ofMaps e _) ∈ latW G i j
      rw [mapW_ofMaps]
      exact GlobalTheory.LatticeStable.smul_mem_latO D _ _ _ _ _ _ hfa _ hW'

end Halves

end GlobalTheory.BigDat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAdelicPointOfUnitaryGroupOne
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotFormula

theorem isFinPt_one : ∀ {D : D7} (V : HSp D) {n : ℕ}, V.rank = n → IsFinPt V (1 : GA D V) (1 : Formalism.MainNotions.StandardLatticesGL3.GA D n) := by
  intro D V n hn
  subst hn
  refine ⟨one_mem _, rfl, fun i j => ?_⟩
  have hL : (finHom V (1 : GA D V)).val = 1 := by
    rw [map_one]; rfl
  rw [hL, Fin.cast_eq_self, Fin.cast_eq_self]
  show _ = toFinE D ((1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j)
  by_cases hij : i = j
  · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero, map_zero]

end GlobalTheory.BotFormula
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeOfLastCoordinateExtensionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_of_lastCoordinate_extension : ∀ {E : Type} [Field E] [NumberField E] {n N : ℕ} (hN : N = n + 1)
    (M : Submodule (𝓞 E) (Fin n → E)) (L : Submodule (𝓞 E) (Fin N → E)), Submodule.IsLattice E M →
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    Submodule.IsLattice E L := by
  first | exact @GlobalTheory.latLast_isLattice | exact GlobalTheory.latLast_isLattice | (intros; apply GlobalTheory.latLast_isLattice <;> assumption)
end

