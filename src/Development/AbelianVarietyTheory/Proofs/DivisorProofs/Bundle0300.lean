import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0268
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0250

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainMonicRootsOfIsIndEtaleLocal
section
open GlobalTheory.EtC

namespace GlobalTheory.LocalIndEtAIC

open Polynomial IsLocalRing

theorem lift_atComap {W O : Type} [CommRing W] [CommRing O] [IsLocalRing O] (v : W →+* O) :
    ∃ φ : Localization.AtPrime ((maximalIdeal O).comap v) →+* O,
      ∀ w, φ (algebraMap W _ w) = v w := by
  have hu : ∀ y : ((maximalIdeal O).comap v).primeCompl, IsUnit (v y) := fun y => by
    by_contra hy
    exact y.2 hy
  exact ⟨IsLocalization.lift hu, fun w => IsLocalization.lift_eq hu w⟩

theorem isDomain_aic_of_indEt : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O],
    IndEt T O → (∀ (E : Type) [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime],
      IsDomain (Localization.AtPrime P) ∧ AIC (Localization.AtPrime P)) → IsDomain O ∧ AIC O := by
  intro T O _ _ _ _ h hE
  have hdom : IsDomain O := by
    refine @NoZeroDivisors.to_isDomain O _ _ ⟨fun {x y} hxy => ?_⟩
    let I : Ideal (MvPolynomial (Fin 2) T) := Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
    haveI : Algebra.FinitePresentation T (MvPolynomial (Fin 2) T ⧸ I) :=
      Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
    let g : (MvPolynomial (Fin 2) T ⧸ I) →ₐ[T] O :=
      Ideal.Quotient.liftₐ I (MvPolynomial.aeval ![x, y]) (by
        intro a ha
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        simp [hxy])
    obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h g
    let w : Fin 2 → W := fun i => u (Ideal.Quotient.mkₐ T I (MvPolynomial.X i))
    have hw : ∀ i, v (w i) = ![x, y] i := fun i => by
      have := DFunLike.congr_fun huv (Ideal.Quotient.mkₐ T I (MvPolynomial.X i))
      exact this.trans (MvPolynomial.aeval_X _ i)
    have h0 : w 0 * w 1 = 0 := by
      have : Ideal.Quotient.mkₐ T I (MvPolynomial.X 0) * Ideal.Quotient.mkₐ T I (MvPolynomial.X 1) = 0 := by
        rw [← map_mul]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      simp only [w, ← map_mul, this, map_zero]
    obtain ⟨φ, hφ⟩ := lift_atComap (v : W →+* O)
    haveI := (hE W ((maximalIdeal O).comap (v : W →+* O))).1
    have hm : algebraMap W (Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))) (w 0) *
        algebraMap W _ (w 1) = 0 := by rw [← map_mul, h0, map_zero]
    rcases mul_eq_zero.mp hm with h1 | h1
    · left
      have e := hφ (w 0)
      rw [h1, map_zero] at e
      have := hw 0
      simp only [AlgHom.coe_toRingHom] at e
      rw [← e] at this
      simpa using this.symm
    · right
      have e := hφ (w 1)
      rw [h1, map_zero] at e
      have := hw 1
      simp only [AlgHom.coe_toRingHom] at e
      rw [← e] at this
      simpa using this.symm
  refine ⟨hdom, ?_⟩
  intro p hpm hdeg
  set n := p.natDegree with hn
  let g : MvPolynomial (Fin n) T →ₐ[T] O := MvPolynomial.aeval (fun i => p.coeff i)
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h g
  let c : Fin n → W := fun i => u (MvPolynomial.X i)
  have hc : ∀ i, v (c i) = p.coeff i := fun i => by
    have := DFunLike.congr_fun huv (MvPolynomial.X i)
    exact this.trans (MvPolynomial.aeval_X _ i)
  let p' : W[X] := X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)
  have hp'm : p'.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hp' : p'.map (v : W →+* O) = p := by
    conv_rhs => rw [hpm.as_sum]
    simp only [p', Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_C]
    rw [← Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i)]
    simp [hc]
    rfl
  have hp'd : p'.natDegree = n := by
    have e1 := hp'm.natDegree_map (v : W →+* O)
    rw [hp'] at e1
    rw [← e1]
  obtain ⟨φ, hφ⟩ := lift_atComap (v : W →+* O)
  set L := Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))
  haveI := (hE W ((maximalIdeal O).comap (v : W →+* O))).1
  have hL := (hE W ((maximalIdeal O).comap (v : W →+* O))).2
  have hmL : (p'.map (algebraMap W L)).Monic := hp'm.map _
  have hdL : 0 < (p'.map (algebraMap W L)).natDegree := by
    rw [hp'm.natDegree_map, hp'd]; exact hdeg
  obtain ⟨r, hr⟩ := hL _ hmL hdL
  refine ⟨φ r, ?_⟩
  have hcomp : φ.comp (algebraMap W L) = (v : W →+* O) := RingHom.ext hφ
  have hpL : p = (p'.map (algebraMap W L)).map φ := by rw [Polynomial.map_map, hcomp, hp']
  rw [hpL, Polynomial.eval_map, Polynomial.eval₂_at_apply, hr, map_zero]

end GlobalTheory.LocalIndEtAIC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedInClosureLocalization
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth

theorem isIntegrallyClosedIn_closure_localization : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra A R], Function.Injective (algebraMap A R) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    IsIntegrallyClosedIn (GlobalTheory.KeyOriginNoeth.closure A R D)
      (Localization (Algebra.algebraMapSubmonoid (GlobalTheory.KeyOriginNoeth.closure A R D)
        (nonZeroDivisors R))) := by
  intro A R _ _ _ _ _ _ _ hinj D _ _ _ _
  letI := closureAlg A R D
  let M : Submonoid R := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  have hM : M ≤ nonZeroDivisors R := by
    rintro _ ⟨a, ha, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero ha ?_
    exact hinj (h.trans (map_zero _).symm)
  haveI : IsDomain (GlobalTheory.LocAcyc.GenFib A R) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  haveI : IsIntegrallyClosed (GlobalTheory.LocAcyc.GenFib A R) :=
    isIntegrallyClosed_of_isLocalization (GlobalTheory.LocAcyc.GenFib A R) M hM
  have hRGF : Function.Injective (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) :=
    IsLocalization.injective (GlobalTheory.LocAcyc.GenFib A R) hM
  have h1 : IsIntegrallyClosedIn D (D ⊗[GlobalTheory.LocAcyc.GenFib A R] FractionRing (GlobalTheory.LocAcyc.GenFib A R)) :=
    GlobalTheory.isIntegrallyClosedIn_tensor_of_smooth
  obtain ⟨hDinj, hDcl⟩ := isIntegrallyClosedIn_iff.mp h1
  let g : closure A R D →+* D ⊗[GlobalTheory.LocAcyc.GenFib A R] FractionRing (GlobalTheory.LocAcyc.GenFib A R) :=
    (algebraMap D _).comp (closure A R D).subtype
  have hg : Function.Injective g := hDinj.comp Subtype.val_injective
  have hunit : ∀ n : Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R), IsUnit (g n) := by
    rintro ⟨_, s, hs, rfl⟩
    have hs0 : algebraMap R (GlobalTheory.LocAcyc.GenFib A R) s ≠ 0 := by
      intro h
      exact nonZeroDivisors.ne_zero hs (hRGF (h.trans (map_zero _).symm))
    have hL : IsUnit (algebraMap (GlobalTheory.LocAcyc.GenFib A R) (FractionRing (GlobalTheory.LocAcyc.GenFib A R))
        (algebraMap R (GlobalTheory.LocAcyc.GenFib A R) s)) :=
      ((IsFractionRing.injective (GlobalTheory.LocAcyc.GenFib A R) _).ne_iff' (map_zero _)).mpr hs0 |>.isUnit
    have heq : g (algebraMap R (closure A R D) s) = Algebra.TensorProduct.includeRight
        (algebraMap (GlobalTheory.LocAcyc.GenFib A R) (FractionRing (GlobalTheory.LocAcyc.GenFib A R))
          (algebraMap R (GlobalTheory.LocAcyc.GenFib A R) s)) := by
      rw [Algebra.TensorProduct.includeRight.commutes]
      rfl
    rw [heq]
    exact hL.map _
  let φ := IsLocalization.lift (M := Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R))
    (S := Localization (Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R))) hunit
  have hφ : φ.comp (algebraMap (closure A R D) _) = g := IsLocalization.lift_comp _

  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨c, n⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R)) z
    have hc : g c = 0 := by
      have := (IsLocalization.lift_mk'_spec (M := Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R))
        (S := Localization (Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R))) (hg := hunit) c 0 n).mp hz
      rw [mul_zero] at this
      exact this
    have : c = 0 := hg (hc.trans (map_zero g).symm)
    simp only [this, IsLocalization.mk'_zero]
  refine isIntegrallyClosedIn_iff.mpr ⟨?_, fun {x} hx => ?_⟩
  · intro a b hab
    apply hg
    rw [← hφ, RingHom.comp_apply, RingHom.comp_apply, hab]
  · obtain ⟨p, hp, hpx⟩ := hx
    have hev : Polynomial.eval₂ g (φ x) p = 0 := by
      have := Polynomial.hom_eval₂ p (algebraMap (closure A R D) _) φ x
      rw [hpx, map_zero, hφ] at this
      exact this.symm
    have hxD : IsIntegral D (φ x) := by
      refine ⟨p.map (closure A R D).subtype, hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      exact hev
    obtain ⟨d, hd⟩ := hDcl hxD

    have hdC : Polynomial.eval₂ (closure A R D).subtype d p = 0 := by
      apply hDinj
      rw [Polynomial.hom_eval₂, hd, map_zero]
      exact hev
    have hdmem : d ∈ closure A R D := by
      letI : Algebra R D := (baseHom A R D).toAlgebra
      letI : Algebra (closure A R D) D := (closure A R D).subtype.toAlgebra
      haveI : IsScalarTower R (closure A R D) D := .of_algebraMap_eq fun _ => rfl
      haveI : Algebra.IsIntegral R (closure A R D) := ⟨fun c => by
        let f : closure A R D →ₐ[R] D := { (closure A R D).subtype with commutes' := fun _ => rfl }
        exact (isIntegral_algHom_iff f Subtype.val_injective).mp c.2⟩
      have hxC : IsIntegral (closure A R D) d := ⟨p, hp, hdC⟩
      exact isIntegral_trans _ hxC
    refine ⟨⟨d, hdmem⟩, hφinj ?_⟩
    rw [← RingHom.comp_apply, hφ]
    exact hd

end GlobalTheory.KeyOriginNoeth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedOfFormallyEtale
section
open IsLocalRing TensorProduct

namespace GlobalTheory.RootFibre

section
variable (R K L : Type) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
include K

end

variable (R L Q : Type) [CommRing R] [CommRing L] [Algebra R L] [CommRing Q] [Algebra R Q] [IsDomain Q]

noncomputable def toFrac : Q ⊗[R] L →ₐ[Q] FractionRing Q ⊗[R] L :=
  Algebra.TensorProduct.map (Algebra.ofId Q (FractionRing Q)) (AlgHom.id R L)

theorem toFrac_injective [Module.Flat R L] : Function.Injective (toFrac R L Q) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := L)
    ((IsScalarTower.toAlgHom R Q (FractionRing Q)).toLinearMap)
    (IsFractionRing.injective Q (FractionRing Q))
  have e : ⇑(toFrac R L Q) =
      ⇑(LinearMap.rTensor L (IsScalarTower.toAlgHom R Q (FractionRing Q)).toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [toFrac]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [e]; exact h

theorem finite_integralClosure [Module.Flat R L] [Algebra.FormallyEtale R L] [Algebra.EssFiniteType R L]
    [IsIntegrallyClosed Q] [IsNoetherianRing Q] :
    Module.Finite Q (integralClosure Q (Q ⊗[R] L)) := by
  classical
  have : Algebra.EssFiniteType (FractionRing Q) (FractionRing Q ⊗[R] L) :=
    Algebra.EssFiniteType.baseChange R L (FractionRing Q)
  have hfin : Module.Finite (FractionRing Q) (FractionRing Q ⊗[R] L) :=
    Algebra.FormallyUnramified.finite_of_free _ _
  obtain ⟨I, _, A, _, _, e, hsep⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod (FractionRing Q) (FractionRing Q ⊗[R] L)).1
      inferInstance
  letI : ∀ i, Algebra Q (A i) := fun i =>
    ((algebraMap (FractionRing Q) (A i)).comp (algebraMap Q (FractionRing Q))).toAlgebra
  haveI : ∀ i, IsScalarTower Q (FractionRing Q) (A i) := fun i =>
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : ∀ i, FiniteDimensional (FractionRing Q) (A i) := fun i =>
    Module.Finite.of_surjective ((Pi.evalAlgHom (FractionRing Q) A i).comp e.toAlgHom).toLinearMap
      (fun a => ⟨e.symm (Pi.single i a), by simp⟩)
  haveI : ∀ i, IsNoetherian Q (integralClosure Q (A i)) := fun i =>
    IsIntegralClosure.isNoetherian Q (FractionRing Q) (A i) (integralClosure Q (A i))
  let g : Q ⊗[R] L →ₐ[Q] (∀ i, A i) :=
    ((e.toAlgHom).restrictScalars Q).comp (toFrac R L Q)
  have hg : Function.Injective g := e.injective.comp (toFrac_injective R L Q)
  let ψ : integralClosure Q (Q ⊗[R] L) →ₗ[Q] (∀ i, integralClosure Q (A i)) :=
    { toFun := fun y i => ⟨g y i, ((y.2.map g).map (Pi.evalAlgHom Q A i))⟩
      map_add' := fun a b => by ext i; simp
      map_smul' := fun c a => by ext i; simp }
  have hψ : Function.Injective ψ := by
    intro a b hab
    apply Subtype.ext
    apply hg
    funext i
    have := congrArg (fun f => ((f i : A i))) hab
    simpa [ψ] using this
  have : IsNoetherian Q (integralClosure Q (Q ⊗[R] L)) := isNoetherian_of_injective ψ hψ
  exact Module.IsNoetherian.finite Q _

end GlobalTheory.RootFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSiegelUpperHalfSpaceNegMulInvSymplecticStatement
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSiegelUpperHalfSpace_neg_mul_inv_symplectic : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → s ∈ Matrix.symplecticGroup l ℝ → P.det ≠ 0 → (-(Q * P⁻¹)).IsSymm → GlobalTheory.IsSiegel (-(Q * P⁻¹)) := by
  first | exact @GlobalTheory.IsSiegel.neg_mul_inv_of_symplectic | exact GlobalTheory.IsSiegel.neg_mul_inv_of_symplectic | (intros; apply GlobalTheory.IsSiegel.neg_mul_inv_of_symplectic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorFiniteProjectiveBaseChangeStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isZModTorsorFiniteProjective_baseChange : ∀ (B B' D : Type) [CommRing B] [CommRing B'] [CommRing D] [Algebra B B'] [Algebra B D]
    (q : ℕ), 0 < q → ∀ (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.LocAcyc.IsZModTorsor B D q act →
    ∃ act' : Multiplicative (ZMod q) →* ((B' ⊗[B] D) ≃ₐ[B'] (B' ⊗[B] D)),
      (∀ (g : Multiplicative (ZMod q)) (b : B') (x : D), act' g (b ⊗ₜ[B] x) = b ⊗ₜ[B] act g x) ∧
      GlobalTheory.LocAcyc.IsZModTorsor B' (B' ⊗[B] D) q act' := by
  first | (exact @GlobalTheory.LocAcyc.isZModTorsor_baseChange) | (exact GlobalTheory.LocAcyc.isZModTorsor_baseChange) | (intros; apply GlobalTheory.LocAcyc.isZModTorsor_baseChange  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZModTorsorIff
section
open CategoryTheory Limits TensorProduct

noncomputable section

namespace GlobalTheory.TorsorColim

def bcAct (S : Type) {R A G : Type} [CommRing R] [CommRing S] [CommRing A] [Algebra R S]
    [Algebra R A] [Monoid G] (act : G →* (A ≃ₐ[R] A)) : G →* (S ⊗[R] A ≃ₐ[S] S ⊗[R] A) where
  toFun g := Algebra.TensorProduct.congr AlgEquiv.refl (act g)
  map_one' := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a => simp
    | add x y hx hy => rw [map_add, hx, hy, map_add]
  map_mul' g h := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a => simp
    | add x y hx hy => rw [map_add, hx, hy, map_add]

@[simp]
theorem bcAct_tmul (S : Type) {R A G : Type} [CommRing R] [CommRing S] [CommRing A] [Algebra R S]
    [Algebra R A] [Monoid G] (act : G →* (A ≃ₐ[R] A)) (g : G) (s : S) (a : A) :
    bcAct S act g (s ⊗ₜ[R] a) = s ⊗ₜ[R] act g a := rfl

def prodMapOf (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) :
    D ⊗[B] D →ₐ[B] (Multiplicative (ZMod q) → D) :=
  Algebra.TensorProduct.productMap
    (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
    (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))

@[simp]
theorem prodMapOf_tmul (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) (x y : D) (g : Multiplicative (ZMod q)) :
    prodMapOf B D q act (x ⊗ₜ[B] y) g = x * act g y := by
  simp [prodMapOf]

theorem eventually_and {J : Type} [Category J] [IsFiltered J] {j : J}
    (P Q : ∀ k : J, (j ⟶ k) → Prop)
    (hP : ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), P k (f₀ ≫ f))
    (hQ : ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), Q k (f₀ ≫ f)) :
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), P k (f₀ ≫ f) ∧ Q k (f₀ ≫ f) := by
  obtain ⟨k₁, f₁, h₁⟩ := hP
  obtain ⟨k₂, f₂, h₂⟩ := hQ
  let a := IsFiltered.leftToMax k₁ k₂
  let b := IsFiltered.rightToMax k₁ k₂
  let e := IsFiltered.coeqHom (f₁ ≫ a) (f₂ ≫ b)
  have he : (f₁ ≫ a) ≫ e = (f₂ ≫ b) ≫ e := IsFiltered.coeq_condition _ _
  refine ⟨IsFiltered.coeq (f₁ ≫ a) (f₂ ≫ b), (f₁ ≫ a) ≫ e, fun k f => ⟨?_, ?_⟩⟩
  · have := h₁ k (a ≫ e ≫ f)
    simpa only [Category.assoc] using this
  · have := h₂ k (b ≫ e ≫ f)
    rw [he]
    simpa only [Category.assoc] using this

end GlobalTheory.TorsorColim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivHeckePhiFourierTransformBoundStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDeriv_heckePhiFourierTransform_bound : (∀ j : ℕ, ∃ (S : Finset (ℕ × ℕ × ℕ)) (P : ℕ × ℕ × ℕ → Polynomial ℂ),
    (∀ p ∈ S, 2 ≤ p.1 + 2 * p.2.1 ∧ p.1 + 2 * p.2.1 = p.2.2 + 2 + j) ∧
    ∀ σ ∈ halfPlane, ∀ ν y : ℝ, y ≠ 0 →
      iteratedDeriv j (hTrans σ ν) y = ∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y) → (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ a b m : ℕ, 2 ≤ a + 2 * b → ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖GlobalTheory.HeckeTwo.TermSmooth.intT σ ν a b m y‖ ≤ C * |y| ^ ((m : ℝ) + 1 - a - 2 * b - 2 * σ.re) / (1 + |ν * y|) ^ N) →
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ j : ℕ, ∃ s : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖iteratedDeriv j (hTrans σ ν) y‖ ≤ C * (|y| + |y|⁻¹) ^ s / (1 + |ν * y|) ^ N := by
  first | exact @GlobalTheory.HeckeTwo.TermBoundDeriv.iteratedDeriv_hTrans_bound | exact GlobalTheory.HeckeTwo.TermBoundDeriv.iteratedDeriv_hTrans_bound | (intros; apply GlobalTheory.HeckeTwo.TermBoundDeriv.iteratedDeriv_hTrans_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivHeckePhiFourierTransformReprStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDeriv_heckePhiFourierTransform_repr : ∀ j : ℕ, ∃ (S : Finset (ℕ × ℕ × ℕ)) (P : ℕ × ℕ × ℕ → Polynomial ℂ),
    (∀ p ∈ S, 2 ≤ p.1 + 2 * p.2.1 ∧ p.1 + 2 * p.2.1 = p.2.2 + 2 + j) ∧
    ∀ σ ∈ halfPlane, ∀ ν y : ℝ, y ≠ 0 →
      iteratedDeriv j (hTrans σ ν) y = ∑ p ∈ S, (P p).eval σ * GlobalTheory.HeckeTwo.TermSmooth.intT σ ν p.1 p.2.1 p.2.2 y := by
  first | exact @GlobalTheory.HeckeTwo.TermSmooth.iteratedDeriv_hTrans_repr | exact GlobalTheory.HeckeTwo.TermSmooth.iteratedDeriv_hTrans_repr | (intros; apply GlobalTheory.HeckeTwo.TermSmooth.iteratedDeriv_hTrans_repr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivHeckePhiTransformHasDerivAtHoloStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDeriv_heckePhiTransform_hasDerivAt_holo : (∀ (a b : ℕ) (σ : ℂ) (ν y : ℝ), 2 ≤ a + b → σ ∈ halfPlane → y ≠ 0 →
    HasDerivAt (fun y' : ℝ => hTransAB a b σ ν y')
      (I * (-(a : ℂ) - σ) * hTransAB (a + 1) b σ ν y + I * ((b : ℂ) + σ) * hTransAB a (b + 1) σ ν y) y) → (∀ (a b : ℕ) (ν y : ℝ), 2 ≤ a + b → y ≠ 0 → DifferentiableOn ℂ (fun σ => hTransAB a b σ ν y) halfPlane) →
  (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane) := by
  first | exact @GlobalTheory.HeckeTwo.iteratedDeriv_hTrans_jet | exact GlobalTheory.HeckeTwo.iteratedDeriv_hTrans_jet | (intros; apply GlobalTheory.HeckeTwo.iteratedDeriv_hTrans_jet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModRepsCardLeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reps_mod_lattice_card_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ M → Λ.FG → ∃ T : Finset (Fin r → E), T.card ≤ M ^ (2 * fdeg E * r) ∧ (∀ t ∈ T, t ∈ Λ) ∧ ∀ x ∈ Λ, ∃ t ∈ T, ∃ y ∈ Λ, x = t + M • y := by
  first | exact @GlobalTheory.lattice_mod_reps_card_le | exact GlobalTheory.lattice_mod_reps_card_le | (intros; apply GlobalTheory.lattice_mod_reps_card_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeScalingValuationEqStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_scaling_valuation_eq : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (V W : Type) [AddCommGroup V] [Module C V] [AddCommGroup W] [Module C W] (LV : Set V) (LW : Set W) (δ : V ≃ₗ[C] C) (δ' : W ≃ₗ[C] C) (ι : V →ₗ[C] W) (lam : C), v.Integers O → (∀ w, w ∈ LV ↔ δ w ∈ (algebraMap O C).range) → (∀ w, w ∈ LW ↔ δ' w ∈ (algebraMap O C).range) → ι '' LV = (fun w => lam • w) '' LW → ∃ l₀ : C, v l₀ = v lam ∧ ∀ w, δ' (ι w) = l₀ * δ w := by
  first | exact @GlobalTheory.DetInv.scalar_of_lattice_image | exact GlobalTheory.DetInv.scalar_of_lattice_image | (intros; apply GlobalTheory.DetInv.scalar_of_lattice_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadDet
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.LeadDet

theorem lead_det : ∀ (R C : Type) [CommRing R] [Field C] (f : R →+* C) (ξ ν : R) (N : ℕ) (F G : Matrix (Fin N) (Fin N) R) (lam : C), F * G = (ξ * ν) • (1 : Matrix (Fin N) (Fin N) R) → IotaScalar (F.map f) (G.map f) (G.map f).rank lam → Lead f ξ F.det (G.map f).rank (lam * f ν ^ (G.map f).rank) := by
  intro R C _ _ f ξ ν N F G lam hFG hI
  set a := (G.map f).rank with ha
  obtain ⟨haN, k, k', hdet⟩ := GlobalTheory.ColComplete.cols_complete C N (G.map f)
  rw [← ha] at hdet
  let X : Fin N → Fin N → R := fun i => if (i : ℕ) < a then G *ᵥ Pi.single (k i) 1 else Pi.single (k' i) 1
  let Y : Fin N → Fin N → R := fun i => if (i : ℕ) < a then Pi.single (k i) 1 else F *ᵥ Pi.single (k' i) 1
  let c : Fin N → R := fun i => if (i : ℕ) < a then ξ * ν else 1
  have hFGv : ∀ v, F *ᵥ (G *ᵥ v) = (ξ * ν) • v := by
    intro v; rw [mulVec_mulVec, hFG]; ext j; simp [mulVec, dotProduct, Matrix.one_apply, Finset.mul_sum]
  have hrow : Matrix.of X * Fᵀ = diagonal c * Matrix.of Y := by
    ext i j
    rw [diagonal_mul, mul_apply]
    have : (∑ l, Matrix.of X i l * Fᵀ l j) = (F *ᵥ X i) j := by
      simp [mulVec, dotProduct, mul_comm]
    rw [this]
    by_cases hi : (i : ℕ) < a
    · simp only [X, Y, c, hi, if_true, of_apply]; rw [hFGv]; simp
    · simp [X, Y, c, hi]
  have hdetR : (Matrix.of X).det * F.det = (ξ * ν) ^ a * (Matrix.of Y).det := by
    have := congrArg Matrix.det hrow
    rw [det_mul, det_mul, det_transpose, det_diagonal] at this
    rw [this]; congr 1
    simp only [c]
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    congr 1
    rw [← ha] at haN
    have hm : (Finset.univ.filter (fun i : Fin N => (i : ℕ) < a)).map Fin.valEmbedding = Finset.range a := by
      ext m; simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply, Finset.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro h; exact ⟨⟨m, by omega⟩, h, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, hm, Finset.card_range]
  have hxmap : (Matrix.of X).map f = Matrix.of (fun i : Fin N => if (i : ℕ) < a then G.map f *ᵥ Pi.single (k i) 1 else Pi.single (k' i) 1) := by
    ext i j
    by_cases hi : (i : ℕ) < a
    · simp [X, hi, RingHom.map_mulVec]
    · simp [X, hi, Pi.single_apply, apply_ite f]
  have hymap : ∀ i, (Matrix.of Y).map f i = if (i : ℕ) < a then Pi.single (k i) 1 else F.map f *ᵥ Pi.single (k' i) 1 := by
    intro i; ext j
    by_cases hi : (i : ℕ) < a
    · simp [Y, hi, Pi.single_apply, apply_ite f]
    · simp [Y, hi, RingHom.map_mulVec]
  have hY := hI (fun i => if (i : ℕ) < a then G.map f *ᵥ Pi.single (k i) 1 else Pi.single (k' i) 1) (fun i => (Matrix.of Y).map f i)
    (by intro i hi; rw [hymap]; simp [hi]) (by intro i hi; rw [hymap]; simp [Nat.not_lt.mpr hi])
  refine ⟨(Matrix.of X).det, ν ^ a * (Matrix.of Y).det, ?_, ?_, ?_⟩
  · rw [RingHom.map_det, RingHom.mapMatrix_apply, hxmap]; exact hdet
  · rw [hdetR, mul_pow]; ring
  · rw [map_mul, map_pow, RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hxmap]
    have : Matrix.of (fun i => (Matrix.of Y).map f i) = (Matrix.of Y).map f := rfl
    rw [this] at hY; rw [hY]; ring

end GlobalTheory.LeadDet
end

