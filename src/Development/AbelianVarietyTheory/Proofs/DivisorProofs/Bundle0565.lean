import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelOfDivisorOfConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0555
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0556
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FittingDatumBaseChangeLocalEnlargement
section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EnlargeBaseChange

end GlobalTheory.EnlargeBaseChange

namespace GlobalTheory.EnlargeBaseChange

open IsLocalRing Polynomial in
open scoped TensorProduct in
private theorem exists_ringHom_tensor_of_comp_eq {R S E : Type} [CommRing R] [CommRing S]
    [CommRing E] [Algebra R S] [Algebra R E] (Z : Type) [CommRing Z] (u : S →+* Z) (v : E →+* Z)
    (h : u.comp (algebraMap R S) = v.comp (algebraMap R E)) :
    ∃ w : S ⊗[R] E →+* Z, w.comp (algebraMap S (S ⊗[R] E)) = u ∧
      w.comp (Algebra.TensorProduct.includeRight.toRingHom : E →+* S ⊗[R] E) = v := by
  letI : Algebra R Z := (v.comp (algebraMap R E)).toAlgebra
  let u' : S →ₐ[R] Z := { u with commutes' := fun r => RingHom.congr_fun h r }
  let v' : E →ₐ[R] Z := { v with commutes' := fun _ => rfl }
  refine ⟨(Algebra.TensorProduct.lift u' v' fun _ _ => Commute.all _ _).toRingHom, ?_, ?_⟩
  · refine RingHom.ext fun s => ?_
    simp [Algebra.TensorProduct.algebraMap_apply, u', v']
  · refine RingHom.ext fun e => ?_
    simp [u', v']

open IsLocalRing Polynomial in
open scoped TensorProduct in
private theorem includeRight_comp_algebraMap_eq {R S E : Type} [CommRing R] [CommRing S]
    [CommRing E] [Algebra R S] [Algebra R E] :
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := E)).toRingHom.comp
        (algebraMap R E) = (algebraMap S (S ⊗[R] E)).comp (algebraMap R S) := by
  ext r
  simp [Algebra.TensorProduct.algebraMap_apply]

open IsLocalRing Polynomial in
open scoped TensorProduct in
private theorem tensorProduct_ringHom_ext_of_comp_eq {R S E Z : Type} [CommRing R] [CommRing S] [CommRing E]
    [CommRing Z] [Algebra R S] [Algebra R E] (w₁ w₂ : S ⊗[R] E →+* Z)
    (h₁ : w₁.comp (algebraMap S (S ⊗[R] E)) = w₂.comp (algebraMap S (S ⊗[R] E)))
    (h₂ : w₁.comp (Algebra.TensorProduct.includeRight.toRingHom : E →+* S ⊗[R] E) =
      w₂.comp (Algebra.TensorProduct.includeRight.toRingHom : E →+* S ⊗[R] E)) : w₁ = w₂ := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s e =>
    have hs := RingHom.congr_fun h₁ s
    have he : w₁ ((1 : S) ⊗ₜ[R] e) = w₂ ((1 : S) ⊗ₜ[R] e) := RingHom.congr_fun h₂ e
    simp only [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply] at hs
    rw [show s ⊗ₜ[R] e = (s ⊗ₜ[R] (1 : E)) * ((1 : S) ⊗ₜ[R] e) by simp, map_mul, map_mul, hs, he]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

open IsLocalRing Polynomial in
open scoped TensorProduct in

theorem _root_.GlobalTheory.EnlargeBaseChange.fits_baseChange : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], _root_.GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = _root_.GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : _root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* _root_.GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    _root_.GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] (f : A →+* A₁) (i₁ : A₁ →+* T),
    Function.Injective i₁ → IsLocalHom i₁ → i₁.comp f = i →
    ∃ (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A₁) EA') (_ : Algebra A₁ EA')
      (_ : IsScalarTower A₁ (Polynomial A₁) EA') (_ : Algebra.Etale (Polynomial A₁) EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : _root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA') →+* _root_.GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')] DA')),
      _root_.GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA' QA' jA' ψA' DA' actA' ∧
      (∃ (β : _root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* _root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA'))
        (h : DA →+* DA'), ψA'.comp β = ψA ∧
        h.comp (algebraMap (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
          (algebraMap (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) DA').comp β) ∧
      ∃ γ : EA →+* EA',
        γ.comp (algebraMap (Polynomial A) EA) = (algebraMap (Polynomial A₁) EA').comp (Polynomial.mapRingHom f) ∧
        jA'.comp ((algebraMap EA' (Localization.AtPrime QA')).comp γ) = jA.comp (algebraMap EA (Localization.AtPrime QA)) ∧
        QA' = (maximalIdeal O).comap (jA'.comp (algebraMap EA' (Localization.AtPrime QA'))) ∧
        (∀ (Z : Type) [CommRing Z] (u : Polynomial A₁ →+* Z) (v : EA →+* Z),
          u.comp (Polynomial.mapRingHom f) = v.comp (algebraMap (Polynomial A) EA) →
          ∃ w : EA' →+* Z, w.comp (algebraMap (Polynomial A₁) EA') = u ∧ w.comp γ = v) ∧
        (∀ (Z : Type) [CommRing Z] (w₁ w₂ : EA' →+* Z),
          w₁.comp (algebraMap (Polynomial A₁) EA') = w₂.comp (algebraMap (Polynomial A₁) EA') →
          w₁.comp γ = w₂.comp γ → w₁ = w₂) := by
  intro T O _ _ _ _ _ _ _ _ _ P _ φ hφ hφs hP q hq _ A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _
    actA hfits A₁ _ _ _ f i₁ hi₁ hloc hcomp
  obtain ⟨hi, -, hqA, -, hjA, hψA, htors⟩ := hfits
  haveI : IsLocalHom φ := hφs.2.2.1
  letI : Algebra A[X] A₁[X] := (Polynomial.mapRingHom f).toAlgebra

  have huv : ((algebraMap T[X] O).comp (Polynomial.mapRingHom i₁)).comp (algebraMap A[X] A₁[X]) =
      (jA.comp (algebraMap EA (Localization.AtPrime QA))).comp (algebraMap A[X] EA) := by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hjA,
      RingHom.algebraMap_toAlgebra, Polynomial.mapRingHom_comp, hcomp]
  obtain ⟨g, hgu, hgv⟩ := exists_ringHom_tensor_of_comp_eq O _ _ huv
  let QA' : Ideal (A₁[X] ⊗[A[X]] EA) := (maximalIdeal O).comap g
  have hmemQ : ∀ z, z ∈ QA' ↔ ¬IsUnit (g z) := fun z => by
    simp [QA', Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  haveI : QA'.IsPrime := Ideal.comap_isPrime _ _
  let jA' : Localization.AtPrime QA' →+* O :=
    IsLocalization.lift (M := QA'.primeCompl) (g := g) fun s => by
      by_contra hs
      exact s.2 ((hmemQ s).2 hs)
  have hjA'comp : jA'.comp (algebraMap _ (Localization.AtPrime QA')) = g :=
    IsLocalization.lift_comp _
  have hjA'g : ∀ z, jA' (algebraMap _ (Localization.AtPrime QA') z) = g z := fun z =>
    RingHom.congr_fun hjA'comp z
  have hgγ : ∀ e, g (Algebra.TensorProduct.includeRight e) =
      jA (algebraMap EA (Localization.AtPrime QA) e) := fun e => RingHom.congr_fun hgv e
  have hgA₁ : ∀ a : A₁, g (algebraMap A₁ _ a) = algebraMap T O (i₁ a) := fun a => by
    have := RingHom.congr_fun hgu (Polynomial.C a)
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C] at this
    rw [IsScalarTower.algebraMap_apply A₁ A₁[X] (A₁[X] ⊗[A[X]] EA), Polynomial.algebraMap_eq,
      IsScalarTower.algebraMap_apply T T[X] O, Polynomial.algebraMap_eq]
    exact this
  have hjA'A₁ : ∀ a : A₁, jA' (algebraMap A₁ (Localization.AtPrime QA') a) = algebraMap T O (i₁ a) :=
    fun a => by
      rw [IsScalarTower.algebraMap_apply A₁ (A₁[X] ⊗[A[X]] EA) (Localization.AtPrime QA'), hjA'g, hgA₁]
  have hunitT : ∀ a : A₁, a ∈ nonZeroDivisors A₁ →
      IsUnit (algebraMap O (_root_.GlobalTheory.LocAcyc.GenFib T O) (algebraMap T O (i₁ a))) := fun a ha =>
    IsLocalization.map_units (M := Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
      (_root_.GlobalTheory.LocAcyc.GenFib T O)
      ⟨algebraMap T O (i₁ a), ⟨i₁ a, mem_nonZeroDivisors_of_ne_zero
        ((map_ne_zero_iff i₁ hi₁).2 (nonZeroDivisors.ne_zero ha)), rfl⟩⟩
  haveI hlocA₁ : IsLocalization
      (Algebra.algebraMapSubmonoid (Localization.AtPrime QA') (nonZeroDivisors A₁))
      (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) := by
    unfold _root_.GlobalTheory.LocAcyc.GenFib
    exact Localization.isLocalization
  let ψA' : _root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA') →+* _root_.GlobalTheory.LocAcyc.GenFib T O :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid (Localization.AtPrime QA') (nonZeroDivisors A₁))
      (g := (algebraMap O (_root_.GlobalTheory.LocAcyc.GenFib T O)).comp jA') fun s => by
        obtain ⟨a, ha, hs⟩ := s.2
        rw [RingHom.comp_apply, ← hs, hjA'A₁]
        exact hunitT a ha
  have hψA'comp : ψA'.comp (algebraMap _ (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA'))) =
      (algebraMap O (_root_.GlobalTheory.LocAcyc.GenFib T O)).comp jA' := IsLocalization.lift_comp _
  have hψA'alg : ∀ y, ψA' (algebraMap _ (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) y) =
      algebraMap O (_root_.GlobalTheory.LocAcyc.GenFib T O) (jA' y) := fun y => RingHom.congr_fun hψA'comp y
  let ℓ : Localization.AtPrime QA →+* Localization.AtPrime QA' :=
    IsLocalization.lift (M := QA.primeCompl)
      (g := (algebraMap _ (Localization.AtPrime QA')).comp
        (Algebra.TensorProduct.includeRight.toRingHom : EA →+* A₁[X] ⊗[A[X]] EA)) fun s => by
        refine IsLocalization.map_units (M := QA'.primeCompl) (Localization.AtPrime QA')
          (⟨Algebra.TensorProduct.includeRight (s : EA), ?_⟩ : QA'.primeCompl)
        rw [Ideal.mem_primeCompl_iff, hmemQ, not_not, hgγ]
        exact (IsLocalization.map_units (Localization.AtPrime QA) s).map jA
  have hℓ : ∀ e, ℓ (algebraMap EA (Localization.AtPrime QA) e) =
      algebraMap (A₁[X] ⊗[A[X]] EA) (Localization.AtPrime QA')
        (Algebra.TensorProduct.includeRight (R := A[X]) (A := A₁[X]) e) := fun e =>
    IsLocalization.lift_eq _ e
  have hγ1 : (Algebra.TensorProduct.includeRight.toRingHom : EA →+* A₁[X] ⊗[A[X]] EA).comp
      (algebraMap A[X] EA) = (algebraMap A₁[X] (A₁[X] ⊗[A[X]] EA)).comp (Polynomial.mapRingHom f) :=
    includeRight_comp_algebraMap_eq
  have hγC : ∀ a : A, Algebra.TensorProduct.includeRight (R := A[X]) (A := A₁[X]) (algebraMap A EA a) =
      algebraMap A₁ (A₁[X] ⊗[A[X]] EA) (f a) := fun a => by
    rw [IsScalarTower.algebraMap_apply A A[X] EA, Polynomial.algebraMap_eq,
      IsScalarTower.algebraMap_apply A₁ A₁[X] (A₁[X] ⊗[A[X]] EA), Polynomial.algebraMap_eq]
    have := RingHom.congr_fun hγ1 (Polynomial.C a)
    simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
      AlgHom.coe_toRingHom] at this
    exact this
  let β : _root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+*
      _root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA') :=
    IsLocalization.lift (M := Algebra.algebraMapSubmonoid (Localization.AtPrime QA) (nonZeroDivisors A))
      (g := (algebraMap _ (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA'))).comp ℓ) fun s => by
        obtain ⟨a, ha, hs⟩ := s.2
        rw [RingHom.comp_apply, ← hs, IsScalarTower.algebraMap_apply A EA (Localization.AtPrime QA),
          hℓ, hγC, ← IsScalarTower.algebraMap_apply A₁ (A₁[X] ⊗[A[X]] EA) (Localization.AtPrime QA')]
        refine IsLocalization.map_units
          (M := Algebra.algebraMapSubmonoid (Localization.AtPrime QA') (nonZeroDivisors A₁)) _
          ⟨_, ⟨f a, mem_nonZeroDivisors_of_ne_zero fun h0 => ?_, rfl⟩⟩
        apply nonZeroDivisors.ne_zero ha
        apply hi
        rw [map_zero, ← hcomp, RingHom.comp_apply, h0, map_zero]
  have hβalg : ∀ y, β (algebraMap _ (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) y) =
      algebraMap _ (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) (ℓ y) := fun y =>
    IsLocalization.lift_eq _ y
  letI : Algebra (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))
      (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) := β.toAlgebra
  have htors' : _root_.GlobalTheory.LocAcyc.IsZModTorsor _ DA q actA := by
    unfold _root_.GlobalTheory.KeyOriginCut.IsZTorsor at htors
    unfold _root_.GlobalTheory.LocAcyc.IsZModTorsor
    exact htors
  obtain ⟨act', -, hact'⟩ := _root_.GlobalTheory.LocAcyc.isZModTorsor_baseChange
    (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))
    (_root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) DA q hq actA htors'
  refine ⟨A₁[X] ⊗[A[X]] EA, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    QA', inferInstance, jA', ψA',
    _root_.GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA') ⊗[_root_.GlobalTheory.LocAcyc.GenFib A
      (Localization.AtPrime QA)] DA, inferInstance, inferInstance, act', ?_,
    ⟨β, Algebra.TensorProduct.includeRight.toRingHom, ?_, includeRight_comp_algebraMap_eq⟩,
    Algebra.TensorProduct.includeRight.toRingHom, hγ1, ?_, ?_, ?_, ?_⟩
  · unfold _root_.GlobalTheory.KeyOriginEnlarge.Fits
    refine ⟨hi₁, hloc, by simpa using hqA.map f, ?_, ?_, hψA'comp, ?_⟩
    · have hO : (maximalIdeal O).comap (algebraMap T[X] O) = _root_.GlobalTheory.KeyOriginCut.originIdeal T := by
        rw [← hφ, ← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap φ, ← hP]
        exact IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime P) P
      show ((maximalIdeal O).comap g).comap _ = _
      rw [Ideal.comap_comap, hgu, ← Ideal.comap_comap, hO]
      exact _root_.GlobalTheory.VertUnitsNoeth.comap_originIdeal' A₁ T i₁
    · rw [IsScalarTower.algebraMap_eq A₁[X] (A₁[X] ⊗[A[X]] EA) (Localization.AtPrime QA'),
        ← RingHom.comp_assoc, hjA'comp, hgu]
    · unfold _root_.GlobalTheory.LocAcyc.IsZModTorsor at hact'
      unfold _root_.GlobalTheory.KeyOriginCut.IsZTorsor
      exact hact'
  · refine _root_.GlobalTheory.LocAcyc.genFib_ringHom_ext fun y => ?_
    have key : (ψA'.comp β).comp
        (algebraMap (Localization.AtPrime QA) (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        ψA.comp (algebraMap (Localization.AtPrime QA)
          (_root_.GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) := by
      refine IsLocalization.ringHom_ext QA.primeCompl (RingHom.ext fun e => ?_)
      simp only [RingHom.comp_apply]
      rw [hβalg, hℓ, hψA'alg, hjA'g, hgγ]
      exact (RingHom.congr_fun hψA _).symm
    exact RingHom.congr_fun key y
  · rw [← RingHom.comp_assoc, hjA'comp, hgv]
  · rw [hjA'comp]
  · intro Z _ u v huv'
    exact exists_ringHom_tensor_of_comp_eq Z u v huv'
  · intro Z _ w₁ w₂ h₁ h₂
    exact tensorProduct_ringHom_ext_of_comp_eq w₁ w₂ h₁ h₂

end GlobalTheory.EnlargeBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDerivedActionsTensorMembers
section
noncomputable section
namespace GlobalTheory.FockEmbExp
open Formalism.BasicNotions.TH Matrix
open scoped Kronecker

section general
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem exp_kron_left (Y : Matrix m m ℂ) :
    NormedSpace.exp (Y ⊗ₖ (1 : Matrix n n ℂ)) = NormedSpace.exp Y ⊗ₖ (1 : Matrix n n ℂ) := by
  let f : Matrix m m ℂ →+* Matrix (m × n) (m × n) ℂ :=
    { toFun Y := Y ⊗ₖ (1 : Matrix n n ℂ)
      map_one' := Matrix.one_kronecker_one
      map_mul' A B := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
      map_zero' := Matrix.zero_kronecker _
      map_add' A B := Matrix.add_kronecker _ _ _ }
  have hf : Continuous f := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    show Continuous fun Y : Matrix m m ℂ => Y a.1 b.1 * (1 : Matrix n n ℂ) a.2 b.2
    fun_prop
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp f hf Y).symm

theorem exp_kron_right (Z : Matrix n n ℂ) :
    NormedSpace.exp ((1 : Matrix m m ℂ) ⊗ₖ Z) = (1 : Matrix m m ℂ) ⊗ₖ NormedSpace.exp Z := by
  let f : Matrix n n ℂ →+* Matrix (m × n) (m × n) ℂ :=
    { toFun Z := (1 : Matrix m m ℂ) ⊗ₖ Z
      map_one' := Matrix.one_kronecker_one
      map_mul' A B := by rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
      map_zero' := Matrix.kronecker_zero _
      map_add' A B := Matrix.kronecker_add _ _ _ }
  have hf : Continuous f := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    show Continuous fun Y : Matrix n n ℂ => (1 : Matrix m m ℂ) a.1 b.1 * Y a.2 b.2
    fun_prop
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp f hf Z).symm

theorem exp_reindex' (e : m ≃ n) (X : Matrix m m ℂ) :
    NormedSpace.exp (Matrix.reindex e e X) = Matrix.reindex e e (NormedSpace.exp X) := by
  open scoped Matrix.Norms.Operator in
  exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (by
    exact LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) X).symm

end general

variable {p q r s : ℕ}

theorem smul_mem {X : Mat p q} (hX : X ∈ upq p q) (t : ℝ) : t • X ∈ upq p q := by
  have h : Xᴴ * Jm p q + Jm p q * X = 0 := hX
  show (t • X)ᴴ * Jm p q + Jm p q * (t • X) = 0
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h,
    smul_zero]

theorem continuous_expt (T : GrpData p q) {X : Mat p q} (hX : X ∈ upq p q) :
    Continuous fun t : ℝ => T.expt (t • X) :=
  T.expt_cont.comp_continuous (by fun_prop) fun t => smul_mem hX t

theorem lift_unique (T : GrpData p q) {γ δ : ℝ → T.G} (hγ : Continuous γ) (hδ : Continuous δ)
    (hc : ∀ t, T.cov (γ t) = T.cov (δ t)) (h0 : γ 0 = δ 0) (t : ℝ) : γ t = δ t := by
  have hsq : Continuous T.sq := continuous_snd.comp T.emb.continuous
  have h := isPreconnected_univ.eq_of_sq_eq (α := ℝ)
    (f := fun t : ℝ => ((T.sq (γ t) : ℂˣ) : ℂ)) (g := fun t : ℝ => ((T.sq (δ t) : ℂˣ) : ℂ))
    (Units.continuous_val.comp (hsq.comp hγ)).continuousOn
    (Units.continuous_val.comp (hsq.comp hδ)).continuousOn (fun t _ => by
      simp only [Pi.pow_apply]
      rw [T.sq_sq, T.sq_sq, hc]) (fun _ => Units.ne_zero _) (Set.mem_univ 0) (by simp only [h0])
  exact T.emb.injective (Prod.ext (hc t) (Units.ext (h (Set.mem_univ t))))

theorem Jm_diag (p q : ℕ) :
    Jm p q = Matrix.diagonal fun a => if a.isLeft then (1 : ℂ) else -1 := by
  ext (a | a) (b | b) <;> simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem Jm_eq (p q r s : ℕ) : Jm (p * r + q * s) (p * s + q * r) =
    Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) (Jm p q ⊗ₖ Jm r s) := by
  rw [Jm_diag, Jm_diag, Jm_diag, Matrix.diagonal_kronecker_diagonal, Matrix.reindex_apply,
    Matrix.submatrix_diagonal_equiv]
  congr 1
  funext x
  obtain ⟨l, rfl⟩ := (lineEquiv p q r s).surjective x
  rw [lineEquiv_isLeft, Function.comp, Equiv.symm_apply_apply]
  rcases l with ⟨a | a, c | c⟩ <;> simp [linePos]

theorem left_mem {Y : Mat p q} (hY : Y ∈ upq p q) (r s : ℕ) :
    Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) (Y ⊗ₖ (1 : Mat r s)) ∈
      upq (p * r + q * s) (p * s + q * r) := by
  have h : Yᴴ * Jm p q + Jm p q * Y = 0 := hY
  show _ᴴ * _ + _ * _ = 0
  rw [Jm_eq, Matrix.conjTranspose_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have := congrArg (fun A : Mat p q => (A ⊗ₖ Jm r s).submatrix (lineEquiv p q r s).symm (lineEquiv p q r s).symm) h
  simpa [Matrix.add_kronecker, Matrix.submatrix_add] using this

theorem right_mem {Y : Mat r s} (hY : Y ∈ upq r s) (p q : ℕ) :
    Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) ((1 : Mat p q) ⊗ₖ Y) ∈
      upq (p * r + q * s) (p * s + q * r) := by
  have h : Yᴴ * Jm r s + Jm r s * Y = 0 := hY
  show _ᴴ * _ + _ * _ = 0
  rw [Jm_eq, Matrix.conjTranspose_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have := congrArg (fun A : Mat r s => (Jm p q ⊗ₖ A).submatrix (lineEquiv p q r s).symm (lineEquiv p q r s).symm) h
  simpa [Matrix.kronecker_add, Matrix.submatrix_add] using this

variable {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q} {T2 : GrpData r s}

theorem continuous_emb (F : FockData T0 T1 T2) : Continuous F.emb := by
  have h1 : Continuous T1.cov := continuous_fst.comp T1.emb.continuous
  have h2 : Continuous T2.cov := continuous_fst.comp T2.emb.continuous
  have s1 : Continuous T1.sq := continuous_snd.comp T1.emb.continuous
  have s2 : Continuous T2.sq := continuous_snd.comp T2.emb.continuous
  have hv : Continuous fun x : T1.G × T2.G =>
      ((T0.cov (F.emb x) : GL _ ℂ) : Mat (p * r + q * s) (p * s + q * r)) := by
    have c1 := (Units.continuous_val.comp h1).comp (continuous_fst (X := T1.G) (Y := T2.G))
    have c2 := (Units.continuous_val.comp h2).comp (continuous_snd (X := T1.G) (Y := T2.G))
    refine continuous_pi fun a => continuous_pi fun b => ?_
    have := (c1.matrix_elem ((lineEquiv p q r s).symm a).1 ((lineEquiv p q r s).symm b).1).mul
      (c2.matrix_elem ((lineEquiv p q r s).symm a).2 ((lineEquiv p q r s).symm b).2)
    refine this.congr fun x => ?_
    rw [show x = (x.1, x.2) from rfl, F.emb_cov]
    rfl
  rw [T0.emb.isInducing.continuous_iff]
  refine Continuous.prodMk (Units.continuous_iff.2 ⟨hv, ?_⟩) ?_
  · refine (hv.comp continuous_inv).congr fun x => ?_
    simp only [Function.comp, map_inv]
  · refine (((s1.comp continuous_fst).pow (r + s)).mul ((s2.comp continuous_snd).pow (p + q))).congr
      fun x => ?_
    exact (F.emb_sq x.1 x.2).symm

theorem emb_expt_left (F : FockData T0 T1 T2) {Y : Mat p q} (hY : Y ∈ upq p q) (t : ℝ) :
    F.emb (T1.expt (t • Y), 1) = T0.expt (t • Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
      (Y ⊗ₖ (1 : Mat r s))) := by
  refine lift_unique T0 (γ := fun t : ℝ => F.emb (T1.expt (t • Y), 1))
    ((continuous_emb F).comp ((continuous_expt T1 hY).prodMk continuous_const))
    (continuous_expt T0 (left_mem hY r s)) (fun t => Units.ext ?_) ?_ t
  · rw [F.emb_cov, T0.expt_cov _ (smul_mem (left_mem hY r s) t), T1.expt_cov _ (smul_mem hY t),
      map_one, Units.val_one, ← exp_kron_left, ← exp_reindex']
    congr 1
    ext a b
    simp
    ring
  · simp only [zero_smul, T1.expt_zero, T0.expt_zero]
    exact map_one F.emb

theorem emb_expt_right (F : FockData T0 T1 T2) {Y : Mat r s} (hY : Y ∈ upq r s) (t : ℝ) :
    F.emb (1, T2.expt (t • Y)) = T0.expt (t • Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
      ((1 : Mat p q) ⊗ₖ Y)) := by
  refine lift_unique T0 (γ := fun t : ℝ => F.emb (1, T2.expt (t • Y)))
    ((continuous_emb F).comp (continuous_const.prodMk (continuous_expt T2 hY)))
    (continuous_expt T0 (right_mem hY p q)) (fun t => Units.ext ?_) ?_ t
  · rw [F.emb_cov, T0.expt_cov _ (smul_mem (right_mem hY p q) t), T2.expt_cov _ (smul_mem hY t),
      map_one, Units.val_one, ← exp_kron_right, ← exp_reindex']
    congr 1
    ext a b
    simp
    ring
  · simp only [zero_smul, T2.expt_zero, T0.expt_zero]
    exact map_one F.emb

theorem fock_derived : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), Continuous F.emb ∧ (∀ Y ∈ upq p q, ∀ P, HasDerivAt (fun t : ℝ => F.π (T1.expt (t • Y), 1) (F.ι P)) (F.ι (fockAct1 p q r s Y P)) 0) ∧ (∀ Y ∈ upq r s, ∀ P, HasDerivAt (fun t : ℝ => F.π (1, T2.expt (t • Y)) (F.ι P)) (F.ι (fockAct2 p q r s Y P)) 0) := by
  intro p q r s T0 T1 T2 F
  refine ⟨continuous_emb F, fun Y hY P => ?_, fun Y hY P => ?_⟩
  · have h := F.der _ (left_mem hY r s) P
    rw [← Matrix.reindex_symm, Equiv.symm_apply_apply] at h
    simp only [FockData.π, MonoidHom.comp_apply, emb_expt_left F hY]
    exact h
  · have h := F.der _ (right_mem hY p q) P
    rw [← Matrix.reindex_symm, Equiv.symm_apply_apply] at h
    simp only [FockData.π, MonoidHom.comp_apply, emb_expt_right F hY]
    exact h

end GlobalTheory.FockEmbExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinShiftedLatticeFourier
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

noncomputable def shearSub {F : Type} [Field F] (x : F) : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) where
  toFun v := ![v 0, v 1 - v 0 * x]
  invFun v := ![v 0, v 1 + v 0 * x]
  map_add' v w := by
    ext i; fin_cases i
    · simp
    · simp; ring
  map_smul' c v := by
    ext i; fin_cases i
    · simp
    · simp; ring
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv v := by ext i; fin_cases i <;> simp

theorem shearSub_zero {F : Type} [Field F] (x : F) (v : Fin 2 → F) : shearSub x v 0 = v 0 := rfl

theorem shearSub_one {F : Type} [Field F] (x : F) (v : Fin 2 → F) : shearSub x v 1 = v 1 - v 0 * x := rfl

theorem hasSum_split_shift : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (w : Emb F → ℂ), Even k → IsCoef k 𝔞 𝔟 a₀ a → w ∈ upperHalf F → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * qPow ξ w) ((cK F k : ℂ) * gval k (split 𝔞 𝔟 x) w 1 / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x w hk hc hw
  have hw' : (fun i : Emb F ↦ w i + ((i x : ℝ) : ℂ)) ∈ upperHalf F := by
    intro i
    simpa using hw i
  have hg : gval k (split 𝔞 𝔟 x) w 1 = gval k (split 𝔞 𝔟 0) (fun i : Emb F ↦ w i + ((i x : ℝ) : ℂ)) 1 := by
    have := GlobalTheory.T.hilbertEisensteinValue_linear_change F k (split 𝔞 𝔟 x) (split 𝔞 𝔟 0) (shearSub x) w 1
      (fun i : Emb F ↦ w i + ((i x : ℝ) : ℂ)) 1 1 hk (fun v ↦ by
        change (_ ∧ _) ↔ (_ ∧ _)
        rw [shearSub_zero, shearSub_one, mul_zero, sub_zero]) (fun i ↦ by simp) (fun v i ↦ by
        simp only [coord, shearSub_zero, shearSub_one, Pi.one_apply, map_sub, map_mul]
        push_cast; ring)
    simpa using this
  have h := hc.2.2.2 _ hw'
  rw [hg]
  convert h using 2 with ξ
  rw [mul_assoc]
  congr 1
  unfold eTr qPow
  rw [← Complex.exp_add, ← GlobalTheory.T.sum_realEmbeddings_eq_trace_totallyReal F (ξ * x), ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul]; push_cast; ring

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapIdealSheafEqOfIsIsoRestrictStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_comap_idealSheaf_eq_of_isIso_restrict : ∀ (W W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) → ∀ (τ : W.IdealSheafData) (V : W.affineOpens), V.1 ≤ U → ((τ.comap π).map π).ideal V = τ.ideal V := by
  first | exact @GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict | exact GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict | (intros; apply GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemSqCounitKerStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mulP_mem_sq_counit_ker : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O], (p : O) ≠ 0 → ¬IsUnit (p : O) → (∀ a : O, ∃ b : O, b ^ p = a) → ∀ (G : GlobalTheory.PDivGroup p O) (n : ℕ) (b : G.A n), G.mulP n b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))) ^ 2 → b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ^ 2 := by
  first | exact @GlobalTheory.PDivGroup.mulP_mem_sq_counit | exact GlobalTheory.PDivGroup.mulP_mem_sq_counit | (intros; apply GlobalTheory.PDivGroup.mulP_mem_sq_counit <;> assumption)
end

