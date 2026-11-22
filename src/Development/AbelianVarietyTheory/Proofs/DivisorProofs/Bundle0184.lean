import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0100
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0077
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0101

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelSpecMapIsIsoOverBasicOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relSpec_map_isIso_over_basicOpen_alt : ∀ (X : Scheme.{0}) (F F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (hα : α.Coequifibered) (hα' : α'.Coequifibered) (ι : F' ⟶ F), α' ≫ ι = α → ∀ (g : (relativeGluingData hα).glued ⟶ (relativeGluingData hα').glued), g ≫ (relativeGluingData hα').toBase = (relativeGluingData hα).toBase → (∀ V, (relativeGluingData hα).cover.f V ≫ g = Spec.map (ι.app (Opposite.op V)) ≫ (relativeGluingData hα').cover.f V) → ∀ (V : X.AffineZariskiSite) (b : F'.obj (Opposite.op V)), Function.Bijective (Localization.awayMap (ι.app (Opposite.op V)).hom b) → ∀ (W : (relativeGluingData hα').glued.Opens), (W : Set (relativeGluingData hα').glued) = (relativeGluingData hα').cover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (F'.obj (Opposite.op V)))) → IsIso (g ∣_ W) ∧ ((g ⁻¹ᵁ W : (relativeGluingData hα).glued.Opens) : Set (relativeGluingData hα).glued) = (relativeGluingData hα).cover.f V '' (PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) : Set (PrimeSpectrum (F.obj (Opposite.op V)))) := by
  first | exact @GlobalTheory.relSpec_map_isIso_over_basicOpen | exact GlobalTheory.relSpec_map_isIso_over_basicOpen | (intros; apply GlobalTheory.relSpec_map_isIso_over_basicOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
section
noncomputable section

open NumberField nonZeroDivisors

namespace GlobalTheory.LipschitzTR

variable (F : Type) [Field F] [NumberField F]

abbrev RSp := EuclideanSpace ℝ (F →+* ℝ)

def remb : F →+ RSp F where
  toFun a := WithLp.toLp 2 (fun τ : F →+* ℝ => τ a)
  map_zero' := by ext τ; simp
  map_add' a b := by ext τ; simp

variable {F}

@[simp] theorem remb_apply (a : F) (τ : F →+* ℝ) : remb F a τ = τ a := rfl

def latOf (N : FractionalIdeal (𝓞 F)⁰ F) : Submodule ℤ (RSp F) :=
  Submodule.map (remb F).toIntLinearMap ((N : Submodule (𝓞 F) F).restrictScalars ℤ)

theorem mem_latOf (N : FractionalIdeal (𝓞 F)⁰ F) (x : RSp F) :
    x ∈ latOf N ↔ ∃ a ∈ N, remb F a = x := by
  simp [latOf]

def phi1 (k : ℕ) (w : ℂ) (t : ℝ) : ℂ :=
  if 0 < (SignType.sign w.im : ℝ) * t then
    ((|t| ^ (k - 1) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t * w)
  else 0

def Phi (k : ℕ) (z : (F →+* ℝ) → ℂ) (ξ : RSp F) : ℂ :=
  ∏ τ : F →+* ℝ, phi1 k (z τ) (ξ τ)

example : phi1 2 Complex.I 1 ≠ 0 := by
  simp [phi1, Complex.exp_ne_zero]

end GlobalTheory.LipschitzTR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepNeZero
section
noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.SlopeTestRemainingChoices.EisFibre

variable {F : Type} [Field F] [NumberField F]

def NzElt (𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : Type :=
  {b : F // b ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ∧ b ≠ 0}

def unitRel (𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : Setoid (NzElt 𝔟) where
  r p q := ∃ ε : (𝓞 F)ˣ, q.1 = ((ε : 𝓞 F) : F) * p.1
  iseqv :=
    { refl := fun _ => ⟨1, by simp⟩
      symm := fun {p q} ⟨ε, h⟩ => ⟨ε⁻¹, by rw [h, ← mul_assoc, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.unit_inv_mul, one_mul]⟩
      trans := fun {p q r} ⟨ε, h⟩ ⟨ε', h'⟩ => ⟨ε' * ε, by rw [h', h, ← mul_assoc]; simp⟩ }

def NzCls (𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : Type := Quotient (unitRel 𝔟)

def rep {𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} (β : NzCls 𝔟) : F := (Quotient.out β : NzElt 𝔟).1

theorem rep_mem {𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} (β : NzCls 𝔟) : rep β ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) :=
  (Quotient.out β : NzElt 𝔟).2.1

theorem rep_ne_zero {𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} (β : NzCls 𝔟) : rep β ≠ 0 :=
  (Quotient.out β : NzElt 𝔟).2.2

def posCone (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (b : F) : Type :=
  {ν : F // ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ τ : F →+* ℝ, 0 < τ (ν * b)}

example : NzCls (1 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) :=
  Quotient.mk _ ⟨1, by simp [FractionalIdeal.one_mem_one], one_ne_zero⟩

end GlobalTheory.SlopeTestRemainingChoices.EisFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepTraceEqMulTraceStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_ringHom_eq_mul_algebraTrace : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (s : ℕ), r = s * Module.finrank ℚ E → ∀ a : 𝓞 E, (ρ a).trace = s * Algebra.trace ℤ (𝓞 E) a := by
  first | exact @GlobalTheory.repTrace_eq_mul_trace | exact GlobalTheory.repTrace_eq_mul_trace | (intros; apply GlobalTheory.repTrace_eq_mul_trace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentationsEqualTracesConjugate
section
open Matrix

namespace GlobalTheory

def piMatUnit {I : Type} [DecidableEq I] (m : ℕ) (τ : I) (i j : Fin m) :
    I → Matrix (Fin m) (Fin m) ℂ :=
  Pi.single τ (Matrix.single i j 1)

lemma piMatUnit_mul {I : Type} [DecidableEq I] (m : ℕ) (τ τ' : I) (i j k l : Fin m) :
    piMatUnit m τ i j * piMatUnit m τ' k l =
      if τ = τ' ∧ j = k then piMatUnit m τ i l else 0 := by
  funext ρ
  simp only [piMatUnit, Pi.mul_apply]
  by_cases h1 : τ = τ'
  · subst h1
    by_cases h2 : j = k
    · subst h2
      by_cases h3 : ρ = τ
      · subst h3; simp [Matrix.single_mul_single_same]
      · simp [Pi.single_apply, h3]
    · by_cases h3 : ρ = τ
      · subst h3; simp [Matrix.single_mul_single_of_ne, h2]
      · simp [Pi.single_apply, h3, h2]
  · by_cases h3 : ρ = τ
    · subst h3
      have : ρ ≠ τ' := h1
      simp [Pi.single_apply, this, h1]
    · simp [Pi.single_apply, h3, h1]

lemma piMatUnit_decomp {I : Type} [Fintype I] [DecidableEq I] (m : ℕ)
    (x : I → Matrix (Fin m) (Fin m) ℂ) :
    x = ∑ τ, ∑ i, ∑ j, x τ i j • piMatUnit m τ i j := by
  funext ρ
  ext a b
  simp only [Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply, piMatUnit,
    Pi.single_apply]
  simp only [show ∀ (c : Prop) [Decidable c] (M : Matrix (Fin m) (Fin m) ℂ),
      (if c then M else 0) a b = if c then M a b else 0 from fun c _ M => by split_ifs <;> rfl]
  simp [Matrix.zero_apply, Matrix.single_apply, mul_ite, ite_and, Finset.sum_ite_eq,
    Finset.sum_ite_eq']

lemma sum_piMatUnit_diag {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (τ : I) :
    ∑ i, piMatUnit m τ i i = Pi.single τ 1 := by
  funext ρ
  ext a b
  by_cases h : ρ = τ
  · subst h
    simp only [piMatUnit, Finset.sum_apply, Matrix.sum_apply, Pi.single_eq_same, Matrix.single_apply,
      Matrix.one_apply]
    rcases eq_or_ne a b with rfl | hab
    · simp
    · simp [hab]
  · simp [piMatUnit, Finset.sum_apply, Matrix.sum_apply, Pi.single_apply, h]

lemma exists_mul_idem_mul_eq_of_trace_eq {g : ℕ} (P P' : Matrix (Fin g) (Fin g) ℂ)
    (hP : IsIdempotentElem P) (hP' : IsIdempotentElem P') (ht : P.trace = P'.trace) :
    ∃ X Y : Matrix (Fin g) (Fin g) ℂ, Y * P' * X = P := by
  first
  | exact @_root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq
  | exact _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq
  | (apply _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq ..)

theorem conj_of_trace_central_idem_eq :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (m g : ℕ), 0 < m →
      ∀ (σ σ' : (I → Matrix (Fin m) (Fin m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ),
        (∀ τ, (σ (Pi.single τ 1)).trace = (σ' (Pi.single τ 1)).trace) →
          ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ ∀ x, σ' x * h = h * σ x := by
  intro I _ _ m g hm σ σ' htr
  set z : Fin m := ⟨0, hm⟩

  have hdiag : ∀ (ρ : (I → Matrix (Fin m) (Fin m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) (τ : I),
      (ρ (Pi.single τ 1)).trace = (m : ℂ) * (ρ (piMatUnit m τ z z)).trace := by
    intro ρ τ
    have hi : ∀ i, (ρ (piMatUnit m τ i i)).trace = (ρ (piMatUnit m τ z z)).trace := by
      intro i
      have e1 : piMatUnit m τ i i = piMatUnit m τ i z * piMatUnit m τ z i := by
        rw [piMatUnit_mul]; simp
      have e2 : piMatUnit m τ z z = piMatUnit m τ z i * piMatUnit m τ i z := by
        rw [piMatUnit_mul]; simp
      rw [e1, e2, map_mul, map_mul, Matrix.trace_mul_comm]
    rw [← sum_piMatUnit_diag, map_sum, Matrix.trace_sum, Finset.sum_congr rfl (fun i _ => hi i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hidem : ∀ (ρ : (I → Matrix (Fin m) (Fin m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) (τ : I),
      IsIdempotentElem (ρ (piMatUnit m τ z z)) := by
    intro ρ τ
    unfold IsIdempotentElem
    rw [← map_mul, piMatUnit_mul]; simp
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have htr' : ∀ τ, (σ (piMatUnit m τ z z)).trace = (σ' (piMatUnit m τ z z)).trace := by
    intro τ
    have := htr τ
    rw [hdiag σ, hdiag σ'] at this
    exact mul_left_cancel₀ hm' this
  choose X Y hYX using fun τ => exists_mul_idem_mul_eq_of_trace_eq _ _ (hidem σ τ) (hidem σ' τ) (htr' τ)
  set h : Matrix (Fin g) (Fin g) ℂ :=
    ∑ τ, ∑ i, σ' (piMatUnit m τ i z) * X τ * σ (piMatUnit m τ z i) with hh
  set h' : Matrix (Fin g) (Fin g) ℂ :=
    ∑ τ, ∑ i, σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) with hh'

  have hE : ∀ τ k l, σ' (piMatUnit m τ k l) * h = h * σ (piMatUnit m τ k l) := by
    intro τ k l
    have hL : ∀ τ' i, σ' (piMatUnit m τ k l) * (σ' (piMatUnit m τ' i z) * X τ' * σ (piMatUnit m τ' z i))
        = if τ = τ' ∧ l = i then σ' (piMatUnit m τ k z) * X τ * σ (piMatUnit m τ z l) else 0 := by
      intro τ' i
      rw [← mul_assoc, ← mul_assoc, ← map_mul, piMatUnit_mul]
      split_ifs with hc
      · obtain ⟨rfl, rfl⟩ := hc; rfl
      · simp
    have hR : ∀ τ' i, σ' (piMatUnit m τ' i z) * X τ' * σ (piMatUnit m τ' z i) * σ (piMatUnit m τ k l)
        = if τ = τ' ∧ k = i then σ' (piMatUnit m τ k z) * X τ * σ (piMatUnit m τ z l) else 0 := by
      intro τ' i
      rw [mul_assoc _ (σ _), ← map_mul, piMatUnit_mul]
      by_cases hc : τ' = τ ∧ i = k
      · obtain ⟨rfl, rfl⟩ := hc; simp
      · have hc' : ¬ (τ = τ' ∧ k = i) := fun h => hc ⟨h.1.symm, h.2.symm⟩
        simp [hc, hc']
    rw [hh, Finset.mul_sum, Finset.sum_mul]
    simp only [Finset.mul_sum, Finset.sum_mul, hL, hR]
    simp [ite_and, Finset.sum_ite_eq]
  have hint : ∀ x, σ' x * h = h * σ x := by
    intro x
    rw [piMatUnit_decomp m x]
    simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, hE]

  have hprod : ∀ τ i τ' j, σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) *
      (σ' (piMatUnit m τ' j z) * X τ' * σ (piMatUnit m τ' z j))
        = if τ = τ' ∧ i = j then σ (piMatUnit m τ i i) else 0 := by
    intro τ i τ' j
    have e : σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) *
        (σ' (piMatUnit m τ' j z) * X τ' * σ (piMatUnit m τ' z j)) =
        σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i * piMatUnit m τ' j z) * X τ' *
          σ (piMatUnit m τ' z j) := by
      rw [map_mul]; simp only [mul_assoc]
    rw [e, piMatUnit_mul]
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc
      rw [show σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z z) * X τ * σ (piMatUnit m τ z i) =
          σ (piMatUnit m τ i z) * (Y τ * σ' (piMatUnit m τ z z) * X τ) * σ (piMatUnit m τ z i) by
            simp only [mul_assoc], hYX τ, ← map_mul, ← map_mul]
      simp [piMatUnit_mul]
    · simp
  have hrow : ∀ τ i, σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) * h =
      σ (piMatUnit m τ i i) := by
    intro τ i
    rw [hh]
    simp only [Finset.mul_sum, hprod]
    simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have hinv : h' * h = 1 := by
    rw [hh', Finset.sum_mul]
    simp only [Finset.sum_mul, hrow]
    rw [← map_one σ, ← Finset.univ_sum_single (1 : I → Matrix (Fin m) (Fin m) ℂ), map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Pi.one_apply, ← sum_piMatUnit_diag, map_sum]
  exact ⟨h, (Matrix.isUnit_iff_isUnit_det h).mpr (Matrix.isUnit_det_of_left_inverse hinv), hint⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentativeParametricIntegralContinuousFamily
section
open MeasureTheory
open scoped ContDiff

namespace GlobalTheory.LocRep

theorem rep_parametric_integral : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ι : K → G → ℂ), (∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) → (∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) → ∀ (T : Type) [TopologicalSpace T] [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T] (ν : Measure T) [IsLocallyFiniteMeasure ν] (Q : Set T) (w : T → K) (φ : T → G → ℂ), IsCompact Q → Continuous w → Continuous (Function.uncurry φ) → (∀ t, ι (w t) =ᵐ[μ] φ t) → (Continuous fun x => ∫ t in Q, φ t x ∂ν) ∧ ι (∫ t in Q, w t ∂ν) =ᵐ[μ] fun x => ∫ t in Q, φ t x ∂ν := by
  intro G _ _ _ _ _ _ _ _ μ _ K _ _ _ ι hloc hlin T _ _ _ _ _ ν _ Q w φ hQ hw hφ hrep
  have hcont : Continuous fun x => ∫ t in Q, φ t x ∂ν :=
    continuous_parametric_integral_of_continuous (f := fun x t => φ t x)
      (hφ.comp continuous_swap) hQ
  refine ⟨hcont, rep_of_pairing hloc hcont.locallyIntegrable fun C hC => ?_⟩
  obtain ⟨Λ, hΛ⟩ := exists_pairing hloc hlin hC
  have hwi : IntegrableOn w Q ν := hw.continuousOn.integrableOn_compact hQ
  have hint : Integrable (Function.uncurry φ) ((ν.restrict Q).prod (μ.restrict C)) := by
    rw [Measure.prod_restrict]
    exact hφ.continuousOn.integrableOn_compact (hQ.prod hC)
  rw [← hΛ, ← Λ.integral_comp_comm hwi, ← integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [hΛ]
  exact integral_congr_ae (ae_restrict_of_ae (hrep t))

end GlobalTheory.LocRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsKillIdeal
section
noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PtClosed

def killIdeal {A : Type} [CommRing A] (Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop) :
    Ideal A where
  carrier := {a | ∀ (R' : Type) [CommRing R'] (f : A →+* R'), Q R' f → f a = 0}
  add_mem' {a b} ha hb R' _ f hf := by rw [map_add, ha R' f hf, hb R' f hf, add_zero]
  zero_mem' R' _ f _ := map_zero f
  smul_mem' c a ha R' _ f hf := by rw [smul_eq_mul, map_mul, ha R' f hf, mul_zero]

def Represents {A : Type} [CommRing A] (Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop)
    (J : Ideal A) : Prop :=
  ∀ (R' : Type) [CommRing R'] (f : A →+* R'), Q R' f ↔ J ≤ RingHom.ker f

def ptQ {S : Scheme.{0}} (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop) (V : S.Opens)
    (hV : IsAffineOpen V) : ∀ (R' : Type) [CommRing R'], (Γ(S, V) →+* R') → Prop :=
  fun R' _ f ↦ P R' (spMap f ≫ hV.fromSpec)

theorem killIdeal_eq {A : Type} [CommRing A]
    {Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop} {J : Ideal A} (h : Represents Q J) :
    killIdeal Q = J := by
  apply le_antisymm
  · intro a ha
    have := ha (A ⧸ J) (Ideal.Quotient.mk J) ((h _ _).2 (by simp [Ideal.mk_ker]))
    simpa [Ideal.Quotient.eq_zero_iff_mem] using this
  · intro a ha R' _ f hf
    exact (h R' f).1 hf ha

theorem represents_killIdeal {A : Type} [CommRing A]
    {Q : ∀ (R' : Type) [CommRing R'], (A →+* R') → Prop} {J : Ideal A} (h : Represents Q J) :
    Represents Q (killIdeal Q) := by
  rw [killIdeal_eq h]; exact h

theorem represents_restrict : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop)
  (U W : S.Opens) (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U) (J : Ideal Γ(S, U)),
  Represents (ptQ P U hU) J → Represents (ptQ P W hW) (J.map (S.presheaf.map (homOfLE h).op).hom) := by
  intro S P U W hU hW h J hJ R' _ f
  have e : spMap f ≫ hW.fromSpec =
      spMap (f.comp (S.presheaf.map (homOfLE h).op).hom) ≫ hU.fromSpec := by
    rw [← hU.map_fromSpec hW (homOfLE h).op]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom]
  show P R' (spMap f ≫ hW.fromSpec) ↔ _
  rw [e, Ideal.map_le_iff_le_comap, RingHom.comap_ker]
  exact hJ R' _

end GlobalTheory.PtClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqInertiaDegAffineChartStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueDegree_eq_inertiaDeg_affine_chart : ∀ (X Y : Scheme.{0}) (g : Y ⟶ X) (V : X.Opens), IsAffineOpen V → ∀ (hU : IsAffineOpen (g ⁻¹ᵁ V)) (w : Y) (hw : w ∈ g ⁻¹ᵁ V), g.residueDegree w = @Ideal.inertiaDeg Γ(Y, g ⁻¹ᵁ V) _ (hU.primeIdealOf ⟨w, hw⟩).asIdeal Γ(X, V) _ (g.app V).hom.toAlgebra := by
  first | exact @GlobalTheory.ResidueDegreeChart.residueDegree_eq_inertiaDeg | exact GlobalTheory.ResidueDegreeChart.residueDegree_eq_inertiaDeg | (intros; apply GlobalTheory.ResidueDegreeChart.residueDegree_eq_inertiaDeg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldAtPrimeIsSepClosedOfFiniteTypeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueField_atPrime_isSepClosed_of_finiteType : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B] (P : Ideal B) [P.IsMaximal], IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) := by
  first | (exact @GlobalTheory.residueField_localization_atPrime_isSepClosed_of_finiteType) | (exact GlobalTheory.residueField_localization_atPrime_isSepClosed_of_finiteType) | (intros; apply GlobalTheory.residueField_localization_atPrime_isSepClosed_of_finiteType <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldMapSurjectiveOfMonoStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueFieldMap_surjective_of_mono' : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [Mono f] (x : X), Function.Surjective (f.residueFieldMap x).hom := by
  first | exact @GlobalTheory.residueFieldMap_surjective_of_mono | exact GlobalTheory.residueFieldMap_surjective_of_mono | (intros; apply GlobalTheory.residueFieldMap_surjective_of_mono <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueNormalOfProfiniteInvariantsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_normal_of_profinite_invariants : ∀ {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (G : Type) [Group G] [MulSemiringAction G B] [SMulCommClass G A B] [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B] [Algebra.IsInvariant A B G] (P : Ideal A) (Q : Ideal B) [Q.LiesOver P] [P.IsMaximal] [Q.IsMaximal], letI := Ideal.Quotient.field P; letI := Ideal.Quotient.field Q; Normal (A ⧸ P) (B ⧸ Q) := by
  first | exact @GlobalTheory.Ideal.Quotient.normal_of_profinite | exact GlobalTheory.Ideal.Quotient.normal_of_profinite | (intros; apply GlobalTheory.Ideal.Quotient.normal_of_profinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannSumOfOneSidedIncrementsStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_sub_of_one_sided_increment_bound_derivative : ∀ (s : Polynomial ℝ) (ℓ : ℚ → ℕ → ℝ), (∀ t t' : ℚ, 0 ≤ t → t ≤ 1 → 0 ≤ t' → t' ≤ 1 → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, ℓ t m - ℓ t' m ≤ ((t' : ℝ) - t) * s.derivative.eval (t : ℝ) + ε) → Tendsto (fun m => ℓ 0 m - ℓ 1 m) atTop (𝓝 (s.eval 1 - s.eval 0)) := by
  first | exact @GlobalTheory.riemann_sum_of_one_sided_increments | exact GlobalTheory.riemann_sum_of_one_sided_increments | (intros; apply GlobalTheory.riemann_sum_of_one_sided_increments <;> assumption)
end

