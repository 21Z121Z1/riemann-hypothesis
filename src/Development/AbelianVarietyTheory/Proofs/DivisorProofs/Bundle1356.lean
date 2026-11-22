import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0949
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1330
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordHolomorphicAndUniform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreduciblePencilLinePolynomialGenericLine
section
set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

namespace GlobalTheory.PencilDisc.GenericLine

variable (F : Type) [Field F] (D N : ℕ)

abbrev Idx := (Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)

def shiftFun (c : F) : Option (Idx D N) → MvPolynomial (Option (Idx D N)) F
  | some (Sum.inr (Sum.inl j)) =>
      X (some (Sum.inr (Sum.inl j))) + C c * (X (some (Sum.inr (Sum.inr j))) * X none)
  | o => X o

def shift (c : F) : MvPolynomial (Option (Idx D N)) F →ₐ[F] MvPolynomial (Option (Idx D N)) F :=
  aeval (shiftFun F D N c)

theorem shift_comp (c : F) : (shift F D N c).comp (shift F D N (-c)) = AlgHom.id F _ := by
  apply MvPolynomial.algHom_ext
  rintro (_ | (p | j | j))
  · simp [shift, shiftFun]
  · simp [shift, shiftFun]
  · simp [shift, shiftFun]
  · simp [shift, shiftFun]

def theta : MvPolynomial (Option (Idx D N)) F ≃ₐ[F] MvPolynomial (Option (Idx D N)) F :=
  AlgEquiv.ofAlgHom (shift F D N 1) (shift F D N (-1))
    (by simpa using shift_comp F D N 1) (by simpa using shift_comp F D N (-1))

def place : Fin (D + 1) × Fin N → Option (Idx D N) := fun p =>
  Fin.lastCases (motive := fun _ => Option (Idx D N)) (some (Sum.inr (Sum.inl p.2)))
    (fun i => some (Sum.inl (i, p.2))) p.1

theorem place_injective : Function.Injective (place D N) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  induction a using Fin.lastCases <;> induction a' using Fin.lastCases <;> simp_all [place]

theorem line_eq (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    GlobalTheory.PencilDisc.line (fun i j => (X (Sum.inl (i, j)) : MvPolynomial (Idx D N) F))
      (fun j => X (Sum.inr (Sum.inl j))) (fun j => X (Sum.inr (Sum.inr j))) f =
    optionEquivLeft F (Idx D N) (theta F D N (rename (place D N) f)) := by
  have key : (aeval (join (fun i j => (Polynomial.C (X (Sum.inl (i, j)) : MvPolynomial (Idx D N) F)))
      (fun j => Polynomial.C (X (Sum.inr (Sum.inl j))) + Polynomial.C (X (Sum.inr (Sum.inr j))) * Polynomial.X)) :
      MvPolynomial (Fin (D + 1) × Fin N) F →ₐ[F] Polynomial (MvPolynomial (Idx D N) F)) =
      ((optionEquivLeft F (Idx D N)).toAlgHom.comp ((theta F D N).toAlgHom.comp (rename (place D N)))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    induction i using Fin.lastCases <;> simp [join, place, theta, shift, shiftFun, AlgEquiv.ofAlgHom_apply]
  exact congrArg (fun φ => φ f) key

end GlobalTheory.PencilDisc.GenericLine

private theorem irreducible_rename_of_injective' {σ τ K : Type} [Field K] (g : σ → τ)
    (hg : Function.Injective g) (f : MvPolynomial σ K) (hf : Irreducible f) :
    Irreducible (rename g f) := by
  classical
  have hk : ∀ p : MvPolynomial σ K, killCompl hg (rename g p) = p := killCompl_rename_app hg
  have hf0 : rename g f ≠ 0 := by
    intro h
    apply hf.ne_zero
    rw [← hk f, h, map_zero]
  have hvars : ∀ a : MvPolynomial τ K, a ∣ rename g f → ∃ q, rename g q = a := by
    rintro a ⟨b, hab⟩
    have ha : a ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hab
      exact hf0 hab
    have hb : b ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hab
      exact hf0 hab
    refine exists_rename_eq_of_vars_subset_range a g hg ?_
    intro i hi
    by_contra hni
    have h1 : degreeOf i (rename g f) = 0 := by
      by_contra hne
      have hmem : i ∈ (rename g f).vars := mem_vars_iff_degreeOf_ne_zero.2 hne
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (vars_rename g f hmem)
      exact hni ⟨j, rfl⟩
    rw [hab, degreeOf_mul_eq ha hb] at h1
    exact mem_vars_iff_degreeOf_ne_zero.1 (Finset.mem_coe.1 hi) (by omega)
  refine irreducible_iff.2 ⟨?_, ?_⟩
  · intro hu
    exact (irreducible_iff.1 hf).1 (by simpa [hk] using hu.map (killCompl hg))
  · intro a b hab
    obtain ⟨a', rfl⟩ := hvars a ⟨b, hab⟩
    obtain ⟨b', rfl⟩ := hvars b ⟨rename g a', by rw [hab, mul_comm]⟩
    rw [← map_mul] at hab
    rcases (irreducible_iff.1 hf).2 (rename_injective g hg hab) with h | h
    · exact Or.inl (h.map _)
    · exact Or.inr (h.map _)

open GlobalTheory.PencilDisc.GenericLine in

theorem GlobalTheory.PencilDisc.irreducible_line_generic (F : Type) [Field F] (D N : ℕ)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (hf : Irreducible f) :
    Irreducible (GlobalTheory.PencilDisc.line
      (fun i j => (MvPolynomial.X (Sum.inl (i, j)) : MvPolynomial ((Fin D × Fin N) ⊕ (Fin N ⊕ Fin N)) F))
      (fun j => MvPolynomial.X (Sum.inr (Sum.inl j))) (fun j => MvPolynomial.X (Sum.inr (Sum.inr j))) f) := by
  rw [line_eq F D N f, MulEquiv.irreducible_iff, MulEquiv.irreducible_iff]
  exact irreducible_rename_of_injective' (place D N) (place_injective D N) f hf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiHomogeneousCofactor
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.CofactorHom

theorem wcomp_mul_of_left {σ F : Type} [Field F] (w : σ → ℕ) (n : ℕ) {P : MvPolynomial σ F} {k : ℕ}
    (hP : IsWeightedHomogeneous w P k) (Q : MvPolynomial σ F) :
    weightedHomogeneousComponent w n (P * Q) =
      if k ≤ n then P * weightedHomogeneousComponent w (n - k) Q else 0 := by
  classical
  letI := weightedGradedAlgebra F w
  have h := DirectSum.coe_decompose_mul_of_left_mem (weightedHomogeneousSubmodule F w) (a := P) (b := Q) n
    ((mem_weightedHomogeneousSubmodule F w k P).2 hP)
  have e : ∀ (m : ℕ) (R : MvPolynomial σ F),
      ((DirectSum.decompose (weightedHomogeneousSubmodule F w) R m : weightedHomogeneousSubmodule F w m) :
        MvPolynomial σ F) = weightedHomogeneousComponent w m R :=
    fun m R => weightedDecomposition.decompose'_apply F w R m
  rw [e, e] at h
  exact h

theorem weight_add_of_mul {σ F : Type} [Field F] (w : σ → ℕ) {P Q : MvPolynomial σ F} {k m : ℕ}
    (hPQ : P * Q ≠ 0) (hP : IsWeightedHomogeneous w P k) (hm : IsWeightedHomogeneous w (P * Q) m)
    (s : σ →₀ ℕ) (hs : s ∈ Q.support) : k + Finsupp.weight w s = m := by
  classical
  have hP0 : P ≠ 0 := left_ne_zero_of_mul hPQ
  set j := Finsupp.weight w s
  have hc : weightedHomogeneousComponent w j Q ≠ 0 := by
    intro h0
    have := congrArg (coeff s) h0
    rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
    exact (mem_support_iff.mp hs) this
  have hne : weightedHomogeneousComponent w (k + j) (P * Q) ≠ 0 := by
    rw [wcomp_mul_of_left w (k + j) hP Q, if_pos (Nat.le_add_right k j), Nat.add_sub_cancel_left]
    exact mul_ne_zero hP0 hc
  by_contra hkm
  exact hne (hm.weightedHomogeneousComponent_ne (k + j) hkm)

end GlobalTheory.CofactorHom

open GlobalTheory.CofactorHom in

theorem GlobalTheory.HSShort.isMultiHomogeneous_cofactor :
    ∀ (F : Type) [Field F] (B N : ℕ) (a a₁ : Fin B → ℕ) (G G' : MvPolynomial (Fin B × Fin N) F),
      G * G' ≠ 0 → IsMultiHomogeneous a (G * G') → IsMultiHomogeneous a₁ G →
        ∃ a' : Fin B → ℕ, IsMultiHomogeneous a' G' ∧ ∀ i, a₁ i + a' i = a i := by
  intro F _ B N a a₁ G G' h0 ha ha₁
  rw [isMultiHomogeneous_iff_forall_weighted_lh0BlockWt] at ha ha₁
  have key : ∀ b, ∀ s ∈ G'.support, a₁ b + ∑ j : Fin N, s (b, j) = a b := fun b s hs => by
    rw [← weight_lh0BlockWt_apply]
    exact weight_add_of_mul _ h0 (ha₁ b) (ha b) s hs
  obtain ⟨s₀, hs₀⟩ : ∃ s, s ∈ G'.support := by
    by_contra hno
    push_neg at hno
    apply h0
    rw [show G' = 0 from by
      ext s; by_contra hc; exact hno s (mem_support_iff.mpr hc), mul_zero]
  refine ⟨fun b => a b - a₁ b, fun s hs b => ?_, fun i => ?_⟩
  · have := key b s hs
    show _ = a b - a₁ b
    omega
  · have := key i s₀ hs₀
    show a₁ i + (a i - a₁ i) = a i
    omega
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiHomogeneousProd
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open GlobalTheory.IndefiniteRowSideFullHecke.FramedLatticeZeroCycleHeight

namespace GlobalTheory.ZeroCycleHt

theorem linSubst_mul {R : Type} [CommRing R] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) R)
    (f g : MvPolynomial (Fin B × Fin N) R) : linSubst M (f * g) = linSubst M f * linSubst M g := by
  simp [linSubst]

theorem exists_rightInv {F : Type} [Field F] {N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    (hw : Function.Surjective w.mulVec) : ∃ P : Matrix (Fin n) (Fin N) F, w * P = 1 := by
  classical
  choose x hx using fun j : Fin N => hw (Pi.single j 1)
  refine ⟨Matrix.of fun k j => x j k, ?_⟩
  ext i j
  have := congrFun (hx j) i
  simp only [Matrix.mulVec, dotProduct] at this
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply]
  rw [this, Pi.single_apply]

theorem formHeight_mul {F : Type} [Field F] [NumberField F] {B N n : ℕ} (δ δ' : ℕ)
    {w : Matrix (Fin N) (Fin n) F} {P : Matrix (Fin n) (Fin N) F} (hP : w * P = 1)
    {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} (hA : ∀ σ, (A σ).det ≠ 0) {a a' : Fin B → ℕ}
    {f g : MvPolynomial (Fin B × Fin N) F} (hf : f ≠ 0) (hg : g ≠ 0)
    (ha : IsMultiHomogeneous a f) (ha' : IsMultiHomogeneous a' g) :
    formHeight (δ + δ') w A (f * g) = formHeight δ w A f + formHeight δ' w A g := by
  have hlf := GlobalTheory.HeightUnique.linSubst_ne_zero hP hf
  have hlg := GlobalTheory.HeightUnique.linSubst_ne_zero hP hg
  have hfin : ∑ᶠ v : FinitePlace F, Real.log (gaussAbs v (linSubst w (f * g))) =
      ∑ᶠ v : FinitePlace F, Real.log (gaussAbs v (linSubst w f)) +
        ∑ᶠ v : FinitePlace F, Real.log (gaussAbs v (linSubst w g)) := by
    rw [← finsum_add_distrib (gauss_abs_log_support_finite _ hlf) (gauss_abs_log_support_finite _ hlg)]
    refine finsum_congr fun v => ?_
    rw [linSubst_mul, gauss_abs_mul v _ _ hlf hlg,
      Real.log_mul (gauss_abs_pos_of_ne_zero v _ hlf).ne' (gauss_abs_pos_of_ne_zero v _ hlg).ne']
  have hne : ∀ (σ : F →+* ℂ) {h : MvPolynomial (Fin B × Fin N) F}, h ≠ 0 →
      linSubst (A σ) (MvPolynomial.map σ h) ≠ 0 := fun σ h hh =>
    GlobalTheory.HeightUnique.linSubst_ne_zero ((A σ).mul_nonsing_inv (hA σ).isUnit) fun h0 =>
      hh (MvPolynomial.map_injective σ σ.injective (by rw [h0, map_zero]))
  have hinf : ∀ σ : F →+* ℂ, blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ (f * g))) =
      blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ f)) +
        blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ g)) := by
    intro σ
    rw [map_mul, linSubst_mul]
    exact sphere_mean_mul_multihomogeneous Closed.sphereLogIntegrable B N a a' _ _ (hne σ hf) (hne σ hg)
      (GlobalTheory.HeightUnique.linSubst_homog _ (isMultiHomogeneous_map_ring a f ha σ))
      (GlobalTheory.HeightUnique.linSubst_homog _ (isMultiHomogeneous_map_ring a' g ha' σ))
  unfold formHeight
  rw [hfin]
  simp only [hinf, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.cast_add]
  ring

theorem formHeight_one {F : Type} [Field F] [NumberField F] {B N n : ℕ}
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) :
    formHeight 0 w A (1 : MvPolynomial (Fin B × Fin N) F) = 0 := by
  have h1 : ∀ v : FinitePlace F, gaussAbs v (1 : MvPolynomial (Fin B × Fin n) F) = 1 := fun v => by
    simpa using GlobalTheory.HeightUnique.gaussAbs_C (σ := Fin B × Fin n) v (1 : F)
  unfold formHeight
  simp [linSubst, h1, blockSphereMean]

end GlobalTheory.ZeroCycleHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularSemisimpleTorusEllipticElementRealPlace
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

noncomputable section

namespace GlobalTheory.RegularGamma

open Polynomial

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
  (k : Type) [CommRing k] [Algebra F k]

abbrev pbL : PowerBasis E (Fld P) := AdjoinRoot.powerBasis P.2.2.1.ne_zero

def vec : Fin (pbL P).dim → k ⊗[F] Fld P := fun i => (1 : k) ⊗ₜ (pbL P).basis i

theorem smul_tmul' (a : k) (e : E) (b : k) (l : Fld P) :
    (a ⊗ₜ[F] e : k ⊗[F] E) • (b ⊗ₜ[F] l : k ⊗[F] Fld P) = (a * b) ⊗ₜ (algebraMap E (Fld P) e * l) := by
  rw [Algebra.smul_def]
  change (Algebra.TensorProduct.map (AlgHom.id F k) (IsScalarTower.toAlgHom F E (Fld P))) (a ⊗ₜ[F] e) * _ = _
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  rfl

theorem span_vec : Submodule.span (k ⊗[F] E) (Set.range (vec P k)) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul a l =>
    rw [← (pbL P).basis.sum_repr l, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : a ⊗ₜ[F] ((pbL P).basis.repr l i • (pbL P).basis i) =
        (a ⊗ₜ[F] (pbL P).basis.repr l i : k ⊗[F] E) • vec P k i := by
      rw [vec, smul_tmul', mul_one, Algebra.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem bijective_vec (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    Function.Bijective (Fintype.linearCombination (k ⊗[F] E) (vec P k)) := by
  have hs : Function.Surjective (Fintype.linearCombination (k ⊗[F] E) (vec P k)) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, span_vec]
  have hd : (pbL P).dim = r := (AdjoinRoot.powerBasis_dim _).trans P.2.2.2.1
  let ψ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin (pbL P).dim → k ⊗[F] E) :=
    φ.trans (LinearEquiv.funCongrLeft _ _ (finCongr hd))
  haveI : Module.Finite (k ⊗[F] E) (k ⊗[F] Fld P) := Module.Finite.equiv φ.symm
  have hi := OrzechProperty.injective_of_surjective_endomorphism
    ((Fintype.linearCombination (k ⊗[F] E) (vec P k)) ∘ₗ ψ.toLinearMap) (hs.comp ψ.surjective)
  refine ⟨fun y y' hyy => ?_, hs⟩
  obtain ⟨z, rfl⟩ := ψ.surjective y
  obtain ⟨z', rfl⟩ := ψ.surjective y'
  rw [hi hyy]

def bas (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    Module.Basis (Fin (pbL P).dim) (k ⊗[F] E) (k ⊗[F] Fld P) :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ (bijective_vec P k φ)).symm

theorem bas_apply (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) (i : Fin (pbL P).dim) :
    bas P k φ i = vec P k i := by
  simp [bas, Module.Basis.coe_ofEquivFun]

theorem mul_vec (j : Fin (pbL P).dim) :
    ((1 : k) ⊗ₜ[F] alpha P) * vec P k j =
      ∑ i, (inclR (F := F) k (Algebra.leftMulMatrix (pbL P).basis (alpha P) i j)) • vec P k i := by
  have hinc : ∀ e : E, inclR (F := F) k e = (1 : k) ⊗ₜ[F] e := fun _ => rfl
  simp only [vec, hinc, smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← TensorProduct.tmul_sum]
  congr 1
  simp only [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', ← Algebra.smul_def]
  exact ((pbL P).basis.sum_repr _).symm

theorem charpoly_mul_alpha (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    haveI := Module.Free.of_basis (bas P k φ)
    haveI := Module.Finite.of_basis (bas P k φ)
    (LinearMap.mul (k ⊗[F] E) (k ⊗[F] Fld P) ((1 : k) ⊗ₜ[F] alpha P)).charpoly = P.1.map (inclR (F := F) k) := by
  haveI := Module.Free.of_basis (bas P k φ)
  haveI := Module.Finite.of_basis (bas P k φ)
  rw [← LinearMap.charpoly_toMatrix _ (bas P k φ)]
  have hM : LinearMap.toMatrix (bas P k φ) (bas P k φ)
      (LinearMap.mul (k ⊗[F] E) (k ⊗[F] Fld P) ((1 : k) ⊗ₜ[F] alpha P)) =
      (Algebra.leftMulMatrix (pbL P).basis (alpha P)).map (inclR (F := F) k) := by
    ext i j
    rw [LinearMap.toMatrix_apply, LinearMap.mul_apply', bas_apply, mul_vec]
    simp_rw [← bas_apply P k φ]
    rw [Module.Basis.repr_sum_self]
    rfl
  rw [hM, Matrix.charpoly_map, show alpha P = (pbL P).gen from (AdjoinRoot.powerBasis_gen _).symm,
    charpoly_leftMulMatrix]
  exact congrArg _ (AdjoinRoot.minpoly_powerBasis_gen_of_monic P.2.1)

theorem charpoly_mulMat (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    (mulMat φ ((1 : k) ⊗ₜ[F] alpha P)).charpoly = P.1.map (inclR (F := F) k) := by
  haveI := Module.Free.of_basis (bas P k φ)
  haveI := Module.Finite.of_basis (bas P k φ)
  change (LinearMap.toMatrix' (φ.conj (LinearMap.mul (k ⊗[F] E) (k ⊗[F] Fld P) ((1 : k) ⊗ₜ[F] alpha P)))).charpoly = _
  rw [← LinearMap.toMatrix_eq_toMatrix', LinearMap.charpoly_toMatrix, LinearEquiv.charpoly_conj,
    charpoly_mul_alpha P k φ]

variable {P k}

theorem gam_val {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {x : k ⊗[F] Fld P}
    {φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) :
    ((gam h).1 : Matrix (Fin n) (Fin n) (k ⊗[F] E)) = mulMat φ ((1 : k) ⊗ₜ[F] alpha P) := by
  change mulMat φ (torUnit _).1 = _
  congr 1
  change Matrix.det _ = _
  rw [Matrix.det_fin_one]
  rfl

end GlobalTheory.RegularGamma

namespace GlobalTheory.RegularGamma

open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots

theorem isRegSS_gam {D : D7} (V : HSp D) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau) {x φ}
    (h : IsIsom P (placeOf D ρ).Completion V.gram x φ) : IsRegSS (matAt V ρ (gam h)) := by
  have hm : matAt V ρ (gam h) = (mulMat φ ((1 : (placeOf D ρ).Completion) ⊗ₜ alpha P)).map (infEmb (embOverOf D ρ)) := by
    rw [← gam_val h]
    rfl
  change (matAt V ρ (gam h)).charpoly.Separable
  rw [hm, Matrix.charpoly_map, charpoly_mulMat, Polynomial.map_map]
  exact (Irreducible.separable P.2.2.1).map

end GlobalTheory.RegularGamma
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmMulRightOfIsCMExt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th GlobalTheory.UAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped NNReal Matrix Topology ContDiff
open GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.UAut.RightTranslate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem isRealLine_conj (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (a : GAd σ J) :
    IsRealLine σ J fun t => a⁻¹ * γ t * a := by
  obtain ⟨w, τ, Z, hZ, hγ⟩ := hγ
  have hu : ∀ x : GArch σ J w, (GlobalTheory.Orb.archMat σ J τ x)ᴴ * J.map τ.1 * GlobalTheory.Orb.archMat σ J τ x = J.map τ.1 :=
    fun x => (archEquiv J h τ x).2
  have h1 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h2 : GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have u1 := hu (projArch σ J w a)
  have u2 := hu (projArch σ J w a)⁻¹
  refine ⟨w, τ, GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ * Z * GlobalTheory.Orb.archMat σ J τ (projArch σ J w a), ?_,
    fun t => ?_⟩
  · generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
    generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
    generalize J.map τ.1 = Q at u1 u2 hZ ⊢
    have e1 : M'ᴴ * Q = Q * M := by
      conv_rhs => rw [← u2, Matrix.mul_assoc, h1, Matrix.mul_one]
    have e2 : Q * M' = Mᴴ * Q := by
      conv_lhs => rw [← u1, Matrix.mul_assoc, h2, Matrix.mul_one]
    calc (M' * Z * M)ᴴ * Q + Q * (M' * Z * M) = Mᴴ * Zᴴ * (M'ᴴ * Q) + (Q * M') * Z * M := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Mᴴ * (Zᴴ * Q + Q * Z) * M := by
          rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hZ, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨y, e1, e2⟩ := hγ t
    refine ⟨(projArch σ J w a)⁻¹ * y * projArch σ J w a, ?_, ?_⟩
    · show a⁻¹ * γ t * a = _
      rw [e1]
      refine GAd_ext σ J (fun u => ?_) fun v => by simp
      by_cases e : u = w
      · subst e; simp
      · simp [projArch_embArch_ne σ J e]
    · rw [map_mul, map_mul, e2]
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a)⁻¹ = M' at *
      generalize GlobalTheory.Orb.archMat σ J τ (projArch σ J w a) = M at *
      have hM : IsUnit M := ⟨⟨M, M', h2, h1⟩, rfl⟩
      rw [← Matrix.inv_eq_left_inv h1, ← Matrix.exp_conj' _ _ hM, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.UAut.RightTranslate

open GlobalTheory.UAut.RightTranslate in

theorem GlobalTheory.UAut.isSm_mul_right_of_isCMExt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E), IsCMExt F E σ → ∀ (f : GlobalTheory.AdelicU.GAd σ J → ℂ) (a : GlobalTheory.AdelicU.GAd σ J), GlobalTheory.UAut.IsSm σ J f → GlobalTheory.UAut.IsSm σ J (fun x => f (x * a)) := by
  intro F E _ _ _ _ _ σ n J h f a hf
  intro k γ hγ g
  have hc : ∀ l : List (GAd σ J), (l.map fun x => a⁻¹ * x * a).prod = a⁻¹ * l.prod * a := fun l => by
    induction l with
    | nil => simp
    | cons x l ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih]; simp [mul_assoc]
  have e : (fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * a)) =
      fun t => f (g * a * (List.ofFn fun i => a⁻¹ * γ i (t i) * a).prod) := funext fun t => by
    rw [show (List.ofFn fun i => a⁻¹ * γ i (t i) * a) = (List.ofFn fun i => γ i (t i)).map fun x => a⁻¹ * x * a from by
      rw [List.map_ofFn]; rfl, hc]
    simp [mul_assoc]
  show ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * a)
  rw [e]
  exact hf k (fun i t => a⁻¹ * γ i t * a) (fun i => isRealLine_conj h (hγ i) a) (g * a)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalTwistAbsDetPowGLStatement
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSpherical_twist_absDetPow_GL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (s : ℝ), GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w a) →
    GlobalTheory.SmGL.IsSpherical (σ.twist (CuspSub.locDet a (GlobalTheory.HeckeGal.Model.absPow E s) w)
      (CuspSub.isOpen_ker_locDet _ w)).ρ := by
  first | exact @GlobalTheory.TwistSph.isSpherical_twist_absPow | exact GlobalTheory.TwistSph.isSpherical_twist_absPow | (intros; apply GlobalTheory.TwistSph.isSpherical_twist_absPow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroupStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_productGroup : ∀ (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G'] (θ : G →* G) (θ' : G' →* G') (K : Subgroup G) (K' : Subgroup G') (δ : G) (δ' : G') (f : G → ℂ) (f' : G' → ℂ), (∀ x : G, (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0) → (∀ x : G', (rStab fun k : K' => f' ((x * k)⁻¹ * δ' * θ' (x * k))).index ≠ 0) → {q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G) | ∃ k ∈ K, f ((Quotient.out q * k)⁻¹ * δ * θ (Quotient.out q * k)) ≠ 0}.Finite → {q : DoubleCoset.Quotient (twCent θ' δ' : Set G') (K' : Set G') | ∃ k ∈ K', f' ((Quotient.out q * k)⁻¹ * δ' * θ' (Quotient.out q * k)) ≠ 0}.Finite → twOrb (θ.prodMap θ') (K.prod K') (δ, δ') (fun y => f y.1 * f' y.2) = twOrb θ K δ f * twOrb θ' K' δ' f' := by
  first | exact @GlobalTheory.BCT.OrbProd.twOrb_prod | exact GlobalTheory.BCT.OrbProd.twOrb_prod | (intros; apply GlobalTheory.BCT.OrbProd.twOrb_prod <;> assumption)
end

