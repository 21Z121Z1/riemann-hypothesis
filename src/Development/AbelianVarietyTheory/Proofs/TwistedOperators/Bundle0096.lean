import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSquareMulInfinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenCardOfNotLone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0092
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0083
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrgCountableField
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEverywhereNormDivOfEtaProdEqOne
section
open NumberField IsDedekindDomain GlobalTheory.QNorm GlobalTheory.QuadSymbol.NormIndex

noncomputable section

namespace GlobalTheory.HilbertRecip

variable {F : Type} [Field F] [NumberField F]

theorem exists_not_mem_nrm_iff {b : Fˣ} (L : Finset (Place F)) (hb : ∀ p ∈ L, b ∉ sqr p)
    (hev : Even L.card) : ∃ a : Fˣ, ∀ p, a ∉ nrm p b ↔ p ∈ L := by
  classical
  rcases L.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact ⟨1, fun p => by simp [one_mem]⟩
  have hns : ¬ IsSquare (b : F) := fun h => hb p₀ hp₀ (mem_sqr_of_isSquare _ h)
  choose O hO using exists_over (F := F)
  obtain ⟨S₁, hS₁, h₁⟩ := exists_superset_mem_sUnits F {b} (L.biUnion O)
  obtain ⟨S₂, hS₂, hadm⟩ := exists_admissible_superset_finite_places F S₁
  obtain ⟨S, hS, hidx⟩ := exists_index_le_two hns hadm (h₁ S₂ hS₂ b (by simp))
  have hadm' := hadm.mono hS
  have hbS : b ∈ sUnits F S := h₁ S (hS₂.trans hS) b (by simp)
  have hover : ∀ p ∈ L, Over S p := fun p hp =>
    (hO p).mono ((Finset.subset_biUnion_of_mem O hp).trans (hS₁.trans (hS₂.trans hS)))
  have hex : ∀ p, ∃ x : Fˣ, p ∈ L → x ∉ nrm p b ∧ ∀ q, Over S q → q ≠ p → x ∈ sqr q := by
    intro p
    by_cases hp : p ∈ L
    · obtain ⟨x, hx⟩ := exists_single S (hover p hp) (hb p hp)
      exact ⟨x, fun _ => hx⟩
    · exact ⟨1, fun h => absurd h hp⟩
  choose x hx using hex
  have hxH : ∀ p ∈ L, x p ∉ sUnits F S ⊔ locNorm F b S := by
    intro p hp hmem
    obtain ⟨u, hu, n, hn, hun⟩ := Subgroup.mem_sup.1 hmem
    rw [mem_locNorm_iff] at hn
    refine not_lone p ⟨u, b, fun h => (hx p hp).1 (hun ▸ mul_mem h (hn p (hover p hp))),
      fun q hq => ?_⟩
    by_cases hq' : Over S q
    · have := sqr_le_nrm q b ((hx p hp).2 q hq' hq)
      rw [← hun] at this
      exact (mul_mem_cancel_right (hn q hq')).1 this
    · exact mem_nrm_of_not_over hadm' hu hbS hq'
  have h2 : (sUnits F S ⊔ locNorm F b S).index = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h | h
    · rw [Subgroup.index_eq_one] at h
      exact absurd (h ▸ Subgroup.mem_top _) (hxH p₀ hp₀)
    · exact h
  obtain ⟨u, hu, n, hn, hun⟩ := Subgroup.mem_sup.1 ((even_of_prod_mem h2 L x hxH).2 hev)
  rw [mem_locNorm_iff] at hn
  refine ⟨u, fun q => ?_⟩
  by_cases hq : Over S q
  · have e := hs_prod L x q b (fun h => (hx q h).1)
      fun p hp hpq => sqr_le_nrm q b ((hx p hp).2 q hq hpq.symm)
    rw [← hun, hs_mul_left, hs_eq_one_iff.2 (hn q hq), mul_one] at e
    split_ifs at e with h
    · exact iff_of_true (hs_eq_neg_one_iff.1 e) h
    · exact iff_of_false (not_not.2 (hs_eq_one_iff.1 e)) h
  · exact iff_of_false (not_not.2 (mem_nrm_of_not_over hadm' hu hbS hq)) fun h => hq (hover q h)

theorem exists_hs_eq {b : Fˣ} (ε : Place F → ℤˣ) (T : Finset (Place F))
    (hT : ∀ p, ε p ≠ 1 → p ∈ T) (hb : ∀ p, b ∈ sqr p → ε p = 1) (hprod : ∏ p ∈ T, ε p = 1) :
    ∃ a : Fˣ, ∀ p, hs p a b = ε p := by
  classical
  have hneg : ∀ p, ε p ≠ 1 → ε p = -1 := fun p h => (Int.units_eq_one_or (ε p)).resolve_left h
  rw [← Finset.prod_filter_mul_prod_filter_not T fun p => ε p ≠ 1,
    Finset.prod_eq_one (s := T.filter fun p => ¬ ε p ≠ 1)
      fun p hp => not_not.1 (Finset.mem_filter.1 hp).2, mul_one,
    Finset.prod_congr rfl fun p hp => hneg p (Finset.mem_filter.1 hp).2,
    Finset.prod_const] at hprod
  obtain ⟨a, ha⟩ := exists_not_mem_nrm_iff (b := b) (T.filter fun p => ε p ≠ 1)
    (fun p hp h => (Finset.mem_filter.1 hp).2 (hb p h))
    ((neg_one_pow_eq_one_iff_even (by decide)).1 hprod)
  refine ⟨a, fun p => ?_⟩
  by_cases h : ε p = 1
  · rw [h, hs_eq_one_iff]
    exact not_not.1 fun h' => (Finset.mem_filter.1 ((ha p).1 h')).2 h
  · rw [hneg p h, hs_eq_neg_one_iff, ha]
    exact Finset.mem_filter.2 ⟨hT p h, h⟩

end GlobalTheory.HilbertRecip

namespace GlobalTheory.QuadSymbol

open GlobalTheory.HilbertRecip

namespace Converse

variable {K : Type} [Field K]

def realPlace (σ : K →+* ℝ) : InfinitePlace K := InfinitePlace.mk (Complex.ofRealHom.comp σ)

theorem isReal_comp (σ : K →+* ℝ) : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp

theorem isReal_realPlace (σ : K →+* ℝ) : (realPlace σ).IsReal :=
  InfinitePlace.isReal_mk_iff.2 (isReal_comp σ)

theorem embedding_realPlace (σ : K →+* ℝ) :
    InfinitePlace.embedding_of_isReal (isReal_realPlace σ) = σ := by
  ext x
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, realPlace,
    InfinitePlace.embedding_mk_eq_of_isReal (isReal_comp σ)]
  simp

theorem realPlace_embedding {w : InfinitePlace K} (h : w.IsReal) :
    realPlace (InfinitePlace.embedding_of_isReal h) = w := by
  have : Complex.ofRealHom.comp (InfinitePlace.embedding_of_isReal h) = w.embedding := by
    ext x
    simp
  rw [realPlace, this, InfinitePlace.mk_embedding]

theorem realPlace_injective : Function.Injective (realPlace (K := K)) := by
  intro σ τ h
  have H : ∀ (w w' : InfinitePlace K) (h : w.IsReal) (h' : w'.IsReal), w = w' →
      InfinitePlace.embedding_of_isReal h = InfinitePlace.embedding_of_isReal h' := by
    rintro w _ h h' rfl
    rfl
  rw [← embedding_realPlace σ, ← embedding_realPlace τ]
  exact H _ _ _ _ h

theorem isSquare_completion {σ : K →+* ℝ} {δ : K} (h : IsSquare (σ δ)) :
    IsSquare (algebraMap K (realPlace σ).Completion δ) := by
  have hw := isReal_realPlace σ
  let f := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hf : f (algebraMap K (realPlace σ).Completion δ) = InfinitePlace.embedding_of_isReal hw δ :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv _).symm δ)
  rw [embedding_realPlace] at hf
  rw [← hf] at h
  simpa using h.map f.symm

variable {L : Type} [Field L] [Algebra K L]

theorem mem_normGroup_of_isComplex (e : Module.Basis (Fin 2) K L) (h0 : e 0 = 1) {δ : K}
    (h1 : e 1 * e 1 = algebraMap K L δ) {w : InfinitePlace K} (h : w.IsComplex)
    (z : (w.Completion)ˣ) : z ∈ normGroup K L w.Completion := by
  rw [mem_normGroup_iff_form e h0 h1]
  let f := InfinitePlace.Completion.ringEquivComplexOfIsComplex h
  have h2 : IsSquare (f z) := IsAlgClosed.exists_eq_mul_self _
  exact Nm.of_isSquare _ (by simpa using h2.map f.symm)

theorem mem_normGroup_of_isSquare [CharZero K] (e : Module.Basis (Fin 2) K L) (h0 : e 0 = 1) {δ : K}
    (hδ : δ ≠ 0) (h1 : e 1 * e 1 = algebraMap K L δ) {A : Type} [Field A] [Algebra K A]
    (h : IsSquare (algebraMap K A δ)) (z : Aˣ) : z ∈ normGroup K L A := by
  haveI : CharZero A := charZero_of_injective_algebraMap (algebraMap K A).injective
  rw [mem_normGroup_iff_form e h0 h1]
  exact Nm.of_isSquare_left two_ne_zero ((map_ne_zero _).2 hδ) h _

theorem div_mem_normGroup {A : Type} [CommRing A] [Algebra K A]
    (h : ∀ a b : Aˣ, eta K L A (a * b) = eta K L A a * eta K L A b) {a b : Aˣ}
    (hab : eta K L A b = eta K L A a) : a / b ∈ normGroup K L A := by
  have := h (a / b) b
  rw [div_mul_cancel, hab, right_eq_mul] at this
  exact eta_eq_one_iff.1 this

end Converse

open Converse in

theorem exists_everywhereNorm_div_of_etaProd_eq_one :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [Algebra.IsQuadraticExtension K L], ∀ (x : FinFam K) (y : InfFam K),
      AlmostNorm K L x → etaProd K L x y = 1 →
        ∃ t : Kˣ, EverywhereNorm K L (x / finDiag K t) (y / infDiag K t) := by
  intro K L _ _ _ _ _ _ x y hA hprod
  classical
  obtain ⟨δ, e, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  lift δ to Kˣ using hδ0.isUnit
  haveI : Fintype (K →+* ℝ) := Fintype.ofFinite _
  have hA' : {v | x v ∉ normGroup K L (v.adicCompletion K)}.Finite := hA
  have hinf : ∏ σ : K →+* ℝ, eta K L (realPlace σ).Completion (y (realPlace σ)) =
      ∏ w : InfinitePlace K, eta K L w.Completion (y w) := by
    refine Finset.prod_of_injOn realPlace realPlace_injective.injOn (fun _ _ => by simp)
      (fun w _ hn => ?_) fun σ _ => rfl
    rcases w.isReal_or_isComplex with h | h
    · exact absurd ⟨InfinitePlace.embedding_of_isReal h, by simp, realPlace_embedding h⟩ hn
    · exact eta_eq_one_iff.2 (mem_normGroup_of_isComplex e h0 h1 h _)
  obtain ⟨t, ht⟩ := exists_hs_eq (b := δ)
    (Sum.elim (fun v => eta K L (v.adicCompletion K) (x v))
      fun σ => eta K L (realPlace σ).Completion (y (realPlace σ)))
    (hA'.toFinset.disjSum Finset.univ)
    (by
      rintro (v | σ) hv
      · rw [Finset.inl_mem_disjSum, Set.Finite.mem_toFinset]
        exact fun h' => hv (eta_eq_one_iff.2 h')
      · simp)
    (by
      rintro (v | σ) hv
      · exact eta_eq_one_iff.2 (mem_normGroup_of_isSquare e h0 hδ0 h1 hv _)
      · exact eta_eq_one_iff.2 (mem_normGroup_of_isSquare e h0 hδ0 h1 (isSquare_completion hv) _))
    (by
      rw [etaProd, ← hinf, finprod_eq_prod_of_mulSupport_subset _ (s := hA'.toFinset) fun v hv => by
        rw [Set.Finite.coe_toFinset]
        exact fun hm => hv (eta_eq_one_iff.2 hm)] at hprod
      rw [Finset.prod_disjSum]
      exact hprod)
  obtain ⟨hc1, hc2⟩ := localCharacters K L
  refine ⟨t, fun v => div_mem_normGroup (hc1 v) ?_, fun w => ?_⟩
  · have key : finDiag K t v ∈ normGroup K L (v.adicCompletion K) ↔ t ∈ nrm (.inl v) δ :=
      mem_normGroup_iff_form e h0 h1
    refine Eq.trans ?_ (ht (.inl v))
    by_cases h : finDiag K t v ∈ normGroup K L (v.adicCompletion K)
    · rw [eta_eq_one_iff.2 h, hs_eq_one_iff.2 (key.1 h)]
    · rw [eta_eq_neg_one_iff.2 h, hs_eq_neg_one_iff.2 fun h' => h (key.2 h')]
  · rcases w.isReal_or_isComplex with h | h
    · refine div_mem_normGroup (hc2 w) ?_
      rw [eta_infinite_real e h0 h1 t h, ht]
      exact congrArg (fun w : InfinitePlace K => eta K L w.Completion (y w)) (realPlace_embedding h)
    · exact mem_normGroup_of_isComplex e h0 h1 h _

end GlobalTheory.QuadSymbol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtExpTwoAddSmulSinhcAdjointStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_exp_two_add_smul_sinhcAdjoint : ∀ (p q : ℕ) (Y V : Mat p q) (a b : Ix p q), HasDerivAt (fun t : ℝ => NormedSpace.exp (Y + Y + t • V) a b) ((NormedSpace.exp Y * sAd Y V * NormedSpace.exp Y) a b) 0 := by
  first | exact @GlobalTheory.PolarU.hasDerivAt_exp_two_add_smul | exact GlobalTheory.PolarU.hasDerivAt_exp_two_add_smul | (intros; apply GlobalTheory.PolarU.hasDerivAt_exp_two_add_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HformSpanEqZero
section
noncomputable section

namespace GlobalTheory.HermitianFormLinearity

open NumberField

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem hform_add_left (J : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J (x + x') y =
      Formalism.UG.hform (starRingEnd E) J x y + Formalism.UG.hform (starRingEnd E) J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_add_right (J : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x (y + y') =
      Formalism.UG.hform (starRingEnd E) J x y + Formalism.UG.hform (starRingEnd E) J x y' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_left (J : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J (c • x) y =
      starRingEnd E c * Formalism.UG.hform (starRingEnd E) J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem hform_smul_right (J : Matrix (Fin n) (Fin n) E) (c : E) (x y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x (c • y) =
      c * Formalism.UG.hform (starRingEnd E) J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_zero_left (J : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J 0 y = 0 := by
  simp [Formalism.UG.hform]

theorem hform_zero_right (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x 0 = 0 := by
  simp [Formalism.UG.hform]

theorem hform_span_eq_zero (J : Matrix (Fin n) (Fin n) E) (S : Set (Fin n → E))
    (hS : ∀ y ∈ S, ∀ z ∈ S, Formalism.UG.hform (starRingEnd E) J y z = 0) :
    ∀ x ∈ Submodule.span E S, ∀ y ∈ Submodule.span E S,
      Formalism.UG.hform (starRingEnd E) J x y = 0 := by
  have h1 : ∀ x ∈ S, ∀ y ∈ Submodule.span E S, Formalism.UG.hform (starRingEnd E) J x y = 0 := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact hS x hx z hz
    | zero => exact hform_zero_right J x
    | add a b _ _ ha hb => rw [hform_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [hform_smul_right, ha, mul_zero]
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem z hz => exact h1 z hz y hy
  | zero => exact hform_zero_left J y
  | add a b _ _ ha hb => rw [hform_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [hform_smul_left, ha, mul_zero]

theorem main : ∀ (I : Formalism.MainNotions.S.AutInst)
    (R : Submodule (NumberField.RingOfIntegers (Formalism.MainNotions.S.AutInst.E I))
      (Fin (Formalism.MainNotions.S.AutInst.n I) → Formalism.MainNotions.S.AutInst.E I)),
    R ≠ ⊥ →
    (∀ y ∈ R, ∀ z ∈ R, Formalism.UG.hform (starRingEnd (Formalism.MainNotions.S.AutInst.E I)) (Formalism.MainNotions.S.AutInst.J I) y z
      = (0 : Formalism.MainNotions.S.AutInst.E I)) →
    Formalism.MainNotions.S.AutInst.IsIsot I (Submodule.span (Formalism.MainNotions.S.AutInst.E I)
      (↑R : Set (Fin (Formalism.MainNotions.S.AutInst.n I) → Formalism.MainNotions.S.AutInst.E I))) := by
  intro I R hR hiso
  refine ⟨?_, hform_span_eq_zero I.J _ hiso⟩
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR
  intro h
  apply hr0
  have : r ∈ Submodule.span I.E (↑R : Set (Fin I.n → I.E)) := Submodule.subset_span hr
  rw [h] at this
  exact (Submodule.mem_bot _).1 this

end GlobalTheory.HermitianFormLinearity
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HolomorphicLeftInvariantDerivativeCalculusNearOn
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJetCalc

section General

variable {A B : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
  [CompleteSpace B]

theorem analyticAt_linField {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (L : A →L[ℂ] A) :
    AnalyticAt ℂ (fun w => fderiv ℂ f w (L w)) z := by

  have hd : AnalyticAt ℂ (fderiv ℂ f) z := hf.fderiv
  have hp : AnalyticAt ℂ (fun w => (fderiv ℂ f w, L w)) z := hd.prod (L.analyticAt z)
  have hev : AnalyticAt ℂ (fun q : (A →L[ℂ] B) × A => q.1 q.2) (fderiv ℂ f z, L z) :=
    (ContinuousLinearMap.id ℂ (A →L[ℂ] B)).analyticAt_bilinear _
  exact AnalyticAt.comp (g := fun q : (A →L[ℂ] B) × A => q.1 q.2)
    (f := fun w => (fderiv ℂ f w, L w)) hev hp

theorem fderiv_linField {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (L : A →L[ℂ] A) (M : A) :
    fderiv ℂ (fun w => fderiv ℂ f w (L w)) z M
      = fderiv ℂ (fderiv ℂ f) z M (L z) + fderiv ℂ f z (L M) := by

  have hD : HasFDerivAt (fderiv ℂ f) (fderiv ℂ (fderiv ℂ f) z) z :=
    hf.fderiv.differentiableAt.hasFDerivAt
  have hP := hD.clm_apply L.hasFDerivAt
  rw [hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

theorem snd_symm {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (M N : A) :
    fderiv ℂ (fderiv ℂ f) z M N = fderiv ℂ (fderiv ℂ f) z N M := by

  have hS : IsSymmSndFDerivAt ℂ f z := hf.contDiffAt.isSymmSndFDerivAt_of_omega
  exact hS M N

theorem comm_linField {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (L K : A →L[ℂ] A) :
    fderiv ℂ (fun w => fderiv ℂ f w (L w)) z (K z) - fderiv ℂ (fun w => fderiv ℂ f w (K w)) z (L z)
      = fderiv ℂ f z (L (K z) - K (L z)) := by

  rw [fderiv_linField hf L, fderiv_linField hf K, snd_symm hf (K z) (L z), map_sub]
  abel

end General

theorem leftInvariant_calculus (n : ℕ) (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (f : Matrix (Fin n) (Fin n) ℂ → B) (hf : AnalyticAt ℂ f 1) :
    (∀ Z, AnalyticAt ℂ (Rz Z f) 1) ∧
    (∀ A Z, (fun z => Rz A (Rz Z f) z - Rz Z (Rz A f) z) =ᶠ[𝓝 1] Rz (A * Z - Z * A) f) ∧
    ∀ Y Z : Matrix (Fin n) (Fin n) ℂ, (fun z => fderiv ℂ (Rz Z f) z (Y * z)) =ᶠ[𝓝 1]
      Rz Z (fun z => fderiv ℂ f z (Y * z)) := by

  let RM : Matrix (Fin n) (Fin n) ℂ → (Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) :=
    fun Z => LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ Z)
  let LM : Matrix (Fin n) (Fin n) ℂ → (Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) :=
    fun Y => LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ Y)
  have hRz : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (g : Matrix (Fin n) (Fin n) ℂ → B),
      Rz Z g = fun w => fderiv ℂ g w (RM Z w) := fun Z g => rfl
  have hev : ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), AnalyticAt ℂ f z :=
    hf.eventually_analyticAt
  refine ⟨fun Z => ?_, fun A Z => ?_, fun Y Z => ?_⟩
  · rw [hRz]
    exact analyticAt_linField hf (RM Z)
  · filter_upwards [hev] with z hz
    have hc := comm_linField hz (RM Z) (RM A)
    have hb : (RM Z) ((RM A) z) - (RM A) ((RM Z) z) = z * (A * Z - Z * A) := by
      show z * A * Z - z * Z * A = z * (A * Z - Z * A)
      rw [mul_sub, mul_assoc, mul_assoc]
    rw [hb] at hc
    exact hc
  · filter_upwards [hev] with z hz
    have hc := comm_linField hz (RM Z) (LM Y)
    have hb : (RM Z) ((LM Y) z) - (LM Y) ((RM Z) z) = 0 := by
      show Y * z * Z - Y * (z * Z) = 0
      rw [mul_assoc, sub_self]
    rw [hb, map_zero, sub_eq_zero] at hc
    exact hc

end GlobalTheory.SphJetCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedDerivInnerExpEqWordJetForms
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet.Taylor

variable {n : ℕ}

theorem analyticAt_Rz {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {f : Matrix (Fin n) (Fin n) ℂ → B} (hf : AnalyticAt ℂ f 1) (Z : Matrix (Fin n) (Fin n) ℂ) :
    AnalyticAt ℂ (Rz Z f) 1 := by
  unfold Rz
  exact (ContinuousLinearMap.id ℂ (Matrix (Fin n) (Fin n) ℂ →L[ℂ] B)).analyticAt_bilinear _ |>.comp₂ hf.fderiv
    (analyticAt_id.mul analyticAt_const)

theorem analyticAt_Rw {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (ε : Fin n → Bool)
    {f : Matrix (Fin n) (Fin n) ℂ → B} (hf : AnalyticAt ℂ f 1) (l : List (Fin n × Fin n)) :
    AnalyticAt ℂ (Rw ε l f) 1 := by
  induction l with
  | nil => exact hf
  | cons p l ih => exact analyticAt_Rz ih _

theorem hasDerivAt_expC (Z : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    HasDerivAt (fun t : ℂ => NormedSpace.exp (t • Z)) (NormedSpace.exp (s • Z) * Z) s :=
  hasDerivAt_exp_smul_const Z s

theorem analyticAt_expC (Z : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    AnalyticAt ℂ (fun t : ℂ => NormedSpace.exp (t • Z)) s :=
  Differentiable.analyticAt (fun t => (hasDerivAt_expC Z t).differentiableAt) s

theorem analyticAt_comp {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    {g : Matrix (Fin n) (Fin n) ℂ → B} (hg : AnalyticAt ℂ g 1) (L : B →L[ℂ] ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    AnalyticAt ℝ (fun t : ℝ => L (g (NormedSpace.exp ((t : ℂ) • Z)))) 0 := by
  have h1 : AnalyticAt ℂ (fun t : ℂ => L (g (NormedSpace.exp (t • Z)))) 0 :=
    (L.analyticAt _).comp (AnalyticAt.comp_of_eq hg (analyticAt_expC Z 0) (by simp))
  have h2 := AnalyticAt.comp_of_eq (h1.restrictScalars (𝕜 := ℝ)) (Complex.ofRealCLM.analyticAt 0) (by simp)
  exact h2

theorem deriv_comp_eventually {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {g : Matrix (Fin n) (Fin n) ℂ → B} (hg : AnalyticAt ℂ g 1) (L : B →L[ℂ] ℂ) (Z : Matrix (Fin n) (Fin n) ℂ) :
    deriv (fun t : ℝ => L (g (NormedSpace.exp ((t : ℂ) • Z)))) =ᶠ[𝓝 0]
      fun t : ℝ => L (Rz Z g (NormedSpace.exp ((t : ℂ) • Z))) := by
  have hc : Tendsto (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Z)) (𝓝 0) (𝓝 1) := by
    have : ContinuousAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Z)) 0 :=
      (hasDerivAt_expC Z ((0 : ℝ) : ℂ)).continuousAt.comp Complex.continuous_ofReal.continuousAt
    simpa [ContinuousAt] using this
  filter_upwards [hc.eventually hg.eventually_analyticAt] with t ht
  have h1 : HasDerivAt (fun s : ℂ => L (g (NormedSpace.exp (s • Z))))
      (L (Rz Z g (NormedSpace.exp ((t : ℂ) • Z)))) (t : ℂ) :=
    L.hasFDerivAt.comp_hasDerivAt _ (ht.differentiableAt.hasFDerivAt.comp_hasDerivAt _ (hasDerivAt_expC Z t))
  exact h1.comp_ofReal.deriv

theorem Rz_thM {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (ε : Fin n → Bool)
    (X : Matrix (Fin n) (Fin n) ℂ) (g : Matrix (Fin n) (Fin n) ℂ → B) (z : Matrix (Fin n) (Fin n) ℂ) :
    Rz (thM ε X) g z = ∑ p : Fin n × Fin n, X p.1 p.2 • Rz (thE ε p) g z := by
  simp only [Rz, thM, Finset.mul_sum, map_sum, mul_smul_comm, map_smul]

theorem iteratedDeriv_inner_exp : ∀ (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) [CompleteSpace W] (j : W →ₗᵢ[ℂ] V) (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)), AnalyticAt ℂ f 1 → (∀ l, funJet ε f l = modJet E j l) → ∀ (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (y x : W), iteratedDeriv m (fun t : ℝ => ⟪y, f (NormedSpace.exp ((t : ℂ) • thM ε X)) x⟫_ℂ) 0 = ⟪j y, (actM E X ^ m) (j x)⟫_ℂ := by
  intro V W _ _ _ _ n ε E _ j f hf hJ X m y x
  let L : (W →L[ℂ] W) →L[ℂ] ℂ := (innerSL ℂ y).comp (ContinuousLinearMap.apply ℂ W x)
  have hL : ∀ T : W →L[ℂ] W, L T = ⟪y, T x⟫_ℂ := fun T => rfl
  have key : ∀ (m : ℕ) (l : List (Fin n × Fin n)),
      iteratedDeriv m (fun t : ℝ => L (Rw ε l f (NormedSpace.exp ((t : ℂ) • thM ε X)))) 0 =
        ⟪j y, (actM E X ^ m) (ew E l (j x))⟫_ℂ := by
    intro m
    induction m with
    | zero =>
      intro l
      have := congrArg (fun B => B y x) (hJ l)
      simp only [funJet_apply, modJet_apply] at this
      simpa [hL] using this
    | succ m ih =>
      intro l
      rw [iteratedDeriv_succ', (deriv_comp_eventually (analyticAt_Rw ε hf l) L _).iteratedDeriv_eq]
      have e : (fun t : ℝ => L (Rz (thM ε X) (Rw ε l f) (NormedSpace.exp ((t : ℂ) • thM ε X)))) =
          fun t : ℝ => ∑ p : Fin n × Fin n,
            X p.1 p.2 * L (Rw ε (p :: l) f (NormedSpace.exp ((t : ℂ) • thM ε X))) := by
        funext t
        rw [Rz_thM, map_sum]
        simp only [map_smul, smul_eq_mul]
        rfl
      rw [e, iteratedDeriv_fun_sum (fun p _ =>
        contDiffAt_const.mul (analyticAt_comp (analyticAt_Rw ε hf (p :: l)) L _).contDiffAt)]
      have e2 : ∀ p : Fin n × Fin n, iteratedDeriv m (fun t : ℝ =>
            X p.1 p.2 * L (Rw ε (p :: l) f (NormedSpace.exp ((t : ℂ) • thM ε X)))) 0 =
          X p.1 p.2 * ⟪j y, (actM E X ^ m) (E p.1 p.2 (ew E l (j x)))⟫_ℂ := by
        intro p
        rw [iteratedDeriv_const_mul _ (analyticAt_comp (analyticAt_Rw ε hf (p :: l)) L _).contDiffAt, ih]
        simp [ew]
      simp only [e2]
      rw [pow_succ, Module.End.mul_apply]
      have e3 : ∀ v : V, actM E X v = ∑ p : Fin n × Fin n, X p.1 p.2 • E p.1 p.2 v := by
        intro v
        simp [actM, Fintype.sum_prod_type, LinearMap.sum_apply]
      rw [e3, map_sum, inner_sum]
      simp only [map_smul, inner_smul_right]
  simpa [hL, Rw, ew] using key m []

end GlobalTheory.SphJet.Taylor
end
end

