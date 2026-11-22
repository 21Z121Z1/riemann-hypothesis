import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0413
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0420
import Development.AbelianVarietyTheory.Definitions.Divisors.Rosati
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0165
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0107
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldMonicRootsTensorFractionRingStrictlyHense
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

open Polynomial

namespace AICStalk

theorem isIntegrallyClosed_of_aic {A : Type} [CommRing A] [IsDomain A] (h : GlobalTheory.EtC.AIC A) :
    IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  rintro x ⟨p, hpm, hp⟩
  suffices H : ∀ n : ℕ, ∀ p : A[X], p.Monic → p.natDegree = n → aeval x p = 0 →
      ∃ y, algebraMap A (FractionRing A) y = x by
    exact H _ p hpm rfl (by rwa [aeval_def])
  intro n
  induction n with
  | zero =>
    intro p hpm hdeg hp
    rw [Polynomial.eq_one_of_monic_natDegree_zero hpm hdeg] at hp
    simp at hp
  | succ n ih =>
    intro p hpm hdeg hp
    obtain ⟨a, ha⟩ := h p hpm (by omega)
    have hq : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    have hqm : (p /ₘ (X - C a)).Monic := Polynomial.Monic.of_mul_monic_left (monic_X_sub_C a) (by rw [hq]; exact hpm)
    have hqd : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic p (monic_X_sub_C a), natDegree_X_sub_C, hdeg]; rfl
    rw [← hq, map_mul] at hp
    simp only [map_sub, aeval_X, aeval_C] at hp
    rcases mul_eq_zero.mp hp with h1 | h1
    · exact ⟨a, (sub_eq_zero.mp h1).symm⟩
    · exact ih _ hqm hqd h1

theorem aic_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : GlobalTheory.EtC.AIC R) :
    GlobalTheory.EtC.AIC S := by
  intro p hpm hdeg
  have hm : (p.map (e.symm : S →+* R)).Monic := hpm.map _
  have hd : (p.map (e.symm : S →+* R)).natDegree = p.natDegree :=
    natDegree_map_eq_of_injective e.symm.injective p
  obtain ⟨a, ha⟩ := h _ hm (hd ▸ hdeg)
  refine ⟨e a, ?_⟩
  have hp : p = (p.map (e.symm : S →+* R)).map (e : R →+* S) := by
    rw [Polynomial.map_map]; ext n; simp
  rw [hp, Polynomial.eval_map, show e a = (e : R →+* S) a from rfl, Polynomial.eval₂_at_apply, ha, map_zero]

theorem aic_of_isAlgClosed (K : Type) [Field K] [IsAlgClosed K] : GlobalTheory.EtC.AIC K := by
  intro p _ hdeg
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (by
    rw [degree_eq_natDegree (ne_zero_of_natDegree_gt hdeg)]; exact_mod_cast hdeg.ne')
  exact ⟨a, ha⟩

theorem algebraMap_injective_of_indEt {A O : Type} [CommRing A] [IsDomain A] [CommRing O]
    [Nontrivial O] [Algebra A O] (h : GlobalTheory.EtC.IndEt A O) : Function.Injective (algebraMap A O) := by
  haveI : Module.Flat A O := GlobalTheory.IndEtaleLocal.flat_of_isIndEtale h
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  have hmem : (1 : O) ∈ Submodule.torsion A O := by
    rw [Submodule.mem_torsion_iff]
    exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha0⟩, by simp [Algebra.smul_def, ha]⟩
  rw [Module.Flat.torsion_eq_bot] at hmem
  exact one_ne_zero ((Submodule.mem_bot A).mp hmem)

theorem isDomain_of_indEt {A O : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing O] [IsLocalRing O] [Algebra A O] (h : GlobalTheory.EtC.IndEt A O) : IsDomain O := by
  refine @NoZeroDivisors.to_isDomain O _ _ ⟨fun {x y} hxy => ?_⟩
  let I : Ideal (MvPolynomial (Fin 2) A) := Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
  haveI : Algebra.FinitePresentation A (MvPolynomial (Fin 2) A ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
  let g : (MvPolynomial (Fin 2) A ⧸ I) →ₐ[A] O :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval ![x, y]) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [hxy])
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h g
  let w : Fin 2 → W := fun i => u (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))
  have hw : ∀ i, v (w i) = ![x, y] i := fun i => by
    have := DFunLike.congr_fun huv (Ideal.Quotient.mkₐ A I (MvPolynomial.X i))
    exact this.trans (MvPolynomial.aeval_X _ i)
  have h0 : w 0 * w 1 = 0 := by
    have : Ideal.Quotient.mkₐ A I (MvPolynomial.X 0) * Ideal.Quotient.mkₐ A I (MvPolynomial.X 1) = 0 := by
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    simp only [w, ← map_mul, this, map_zero]
  let q : Ideal W := (IsLocalRing.maximalIdeal O).comap v
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨hdom, -⟩ := GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed A W q
  have hq : ∀ t ∈ q.primeCompl, IsUnit (v t) := fun t ht => by
    by_contra hc
    exact ht (IsLocalRing.mem_maximalIdeal _ |>.mpr hc)
  have hm : algebraMap W (Localization.AtPrime q) (w 0) * algebraMap W (Localization.AtPrime q) (w 1) = 0 := by
    rw [← map_mul, h0, map_zero]
  rcases mul_eq_zero.mp hm with h1 | h1
  · obtain ⟨⟨t, ht⟩, hte⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ _).mp h1
    have := congrArg v hte
    rw [map_mul, map_zero, hw] at this
    exact Or.inl (((hq t ht).mul_right_eq_zero).mp this)
  · obtain ⟨⟨t, ht⟩, hte⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ _).mp h1
    have := congrArg v hte
    rw [map_mul, map_zero, hw] at this
    exact Or.inr (((hq t ht).mul_right_eq_zero).mp this)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem isIntegral_tmul_one {A O : Type} [CommRing A] [IsDomain A] [CommRing O] [Algebra A O]
    (h : GlobalTheory.EtC.IndEt A O) (o : O) :
    IsIntegral (FractionRing A) (o ⊗ₜ[A] (1 : FractionRing A)) := by
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h (Polynomial.aeval (R := A) o)
  haveI : Algebra.Etale (FractionRing A) (FractionRing A ⊗[A] W) := Algebra.Etale.baseChange A W _
  haveI : Module.Finite (FractionRing A) (FractionRing A ⊗[A] W) :=
    Algebra.FormallyUnramified.finite_of_free _ _
  haveI : Algebra.IsIntegral (FractionRing A) (FractionRing A ⊗[A] W) := Algebra.IsIntegral.of_finite _ _
  let χ : W →ₐ[A] O ⊗[A] FractionRing A := (Algebra.TensorProduct.includeLeft (S := A)).comp v
  let Χ : FractionRing A ⊗[A] W →ₐ[FractionRing A] O ⊗[A] FractionRing A :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) χ (fun _ _ => Commute.all _ _)
  have hX : Χ (1 ⊗ₜ (u Polynomial.X)) = o ⊗ₜ 1 := by
    have := DFunLike.congr_fun huv Polynomial.X
    simp only [AlgHom.comp_apply, Polynomial.aeval_X] at this
    simp [Χ, χ, this]
  rw [← hX]
  exact (Algebra.IsIntegral.isIntegral _).map Χ

end AICStalk

open AICStalk in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem isField_aic_tensor_fractionRing_of_strictlyHenselian :
    ∀ (A O : Type) [CommRing A] [IsDomain A] [CommRing O] [Algebra A O], GlobalTheory.EtC.AIC A →
      GlobalTheory.EtC.SH O → GlobalTheory.EtC.IndEt A O →
      IsField (O ⊗[A] FractionRing A) ∧ GlobalTheory.EtC.AIC (O ⊗[A] FractionRing A) := by
  intro A O _ _ _ _ hA hO h
  haveI := isIntegrallyClosed_of_aic hA
  obtain ⟨hH, -⟩ := hO
  haveI := hH
  haveI := isDomain_of_indEt h
  haveI : IsAlgClosed (FractionRing A) := GlobalTheory.T.isAlgClosed_fractionRing_of_monic_polynomials_have_roots A hA
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors A))
      (O ⊗[A] FractionRing A) := by
    rw [Algebra.isLocalization_iff_isPushout (nonZeroDivisors A) (FractionRing A)]
    infer_instance
  have hinj := algebraMap_injective_of_indEt h
  haveI : IsDomain (O ⊗[A] FractionRing A) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (M := Algebra.algebraMapSubmonoid O (nonZeroDivisors A)) (O ⊗[A] FractionRing A) (by
      rintro _ ⟨a, ha, rfl⟩
      exact mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero ha)))
  have hall : ∀ x : O ⊗[A] FractionRing A, IsIntegral (FractionRing A) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul o k =>
      have : o ⊗ₜ[A] k = (o ⊗ₜ[A] (1 : FractionRing A)) * algebraMap (FractionRing A) _ k := by
        rw [show algebraMap (FractionRing A) (O ⊗[A] FractionRing A) k = 1 ⊗ₜ k from rfl,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this]
      exact (isIntegral_tmul_one h o).mul isIntegral_algebraMap
    | add x y hx hy => exact hx.add hy
  haveI : Algebra.IsIntegral (FractionRing A) (O ⊗[A] FractionRing A) := ⟨hall⟩
  let e := RingEquiv.ofBijective _
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := FractionRing A) (K := O ⊗[A] FractionRing A))
  exact ⟨MulEquiv.isField (Field.toIsField (FractionRing A)) e.symm.toMulEquiv,
    aic_of_ringEquiv e (aic_of_isAlgClosed _)⟩

end GlobalTheory

example : ∀ (A O : Type) [CommRing A] [IsDomain A] [CommRing O] [Algebra A O], AIC A → SH O → IndEt A O → IsField (O ⊗[A] FractionRing A) ∧ AIC (O ⊗[A] FractionRing A) :=
  GlobalTheory.isField_aic_tensor_fractionRing_of_strictlyHenselian
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelOn
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}

def IsLevelOn {Y : Scheme.{0}} {s : Y ⟶ Sp R} (o₀ : Pre b s) {G : Over Y} [GrpObj G] {g : ℕ}
    (f : (Fin g ⊕ Fin g → ℤ) →ₗ[ℤ] D.La) (n d L : ℕ) (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over Y) ⟶ G))
    (χ : o₀.A ⟶ G) (ψ : D.La → (𝟙_ (Over Y) ⟶ G)) (T : Over Y) (lv : D.La → (T ⟶ o₀.A)) : Prop :=
  (∀ x y, lv (x + y) = lv x * lv y) ∧ (∀ (c : D.O) x, lv (c • x) = lv x ≫ o₀.act.act c) ∧
    (∀ x, lv (L • x) = 1) ∧ (∀ a, toUnit T ≫ lev a = (lv (f a) ^ d) ≫ χ) ∧
    (∀ y, (lv y ^ (d * n)) ≫ χ = toUnit T ≫ ψ y) ∧
    ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ T.left) (β : R →+* κ), x ≫ T.hom ≫ s = spMap β →
      ∃ I : TateIsoO D κ (Over.mk (x ≫ T.hom) ⟶ o₀.A) (fun c g' => g' ≫ o₀.act.act c)
          (fun m g₁ g₂ z => Out.WeilIs o₀.A (o₀.P.pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left) m g₁ g₂ (unitOn z)),
        ∀ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv y = I.ev L y

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIsIrreducibleComponentOfRationalPointSmoot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isOpen_and_isIrreducible_sectionComponent_of_smooth_field
    (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
    (e : Spec (CommRingCat.of k) ⟶ X) (hf : Smooth f) (he : e ≫ f = 𝟙 _) :
    IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} ∧
      IsIrreducible {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  have hsub : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum k))
  have hZ : {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))}
      = connectedComponent (e p) := by
    ext x
    have h1 : (f ⁻¹' {f x} : Set X) = Set.univ :=
      Set.eq_univ_of_forall fun y => Subsingleton.elim _ _
    have h2 : f x = p := Subsingleton.elim _ _
    rw [Set.mem_setOf_eq, h1, h2, connectedComponentIn_univ]
  rw [hZ]
  have hN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hO : IsOpen (connectedComponent (e p)) := GlobalTheory.T.isOpen_connectedComponent_of_isLocallyNoetherian' X hN (e p)
  refine ⟨hO, ?_⟩
  let U : X.Opens := ⟨connectedComponent (e p), hO⟩
  have hc : ConnectedSpace U.toScheme :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := e p))
  have hi : IrreducibleSpace U.toScheme :=
    GlobalTheory.T.irreducibleSpace_of_smooth_over_field_of_connected k U.toScheme (U.ι ≫ f) inferInstance hc
  exact isIrreducible_iff_irreducibleSpace.mpr hi

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSubgroupOfSiegelAndOppositeNhds
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary Filter Topology
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.OpenCrit

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {ν : Type} [Fintype ν] [DecidableEq ν]

def vOf (g : UG c (stdJ ν E)) : Matrix ν ν E := (mat c g).toBlocks₂₂⁻¹ * (mat c g).toBlocks₂₁

theorem lower_rel (g : UG c (stdJ ν E)) :
    (mat c g).toBlocks₂₁ * ((mat c g).toBlocks₂₂.map c)ᵀ = (mat c g).toBlocks₂₂ * ((mat c g).toBlocks₂₁.map c)ᵀ := by
  have h : mat c g * stdJ ν E * ((mat c g).map c)ᵀ = stdJ ν E := (mem_UG_iff c _).mp g.2
  have h2 := congrArg Matrix.toBlocks₂₂ h
  rw [← fromBlocks_toBlocks (mat c g)] at h2
  simp [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply] at h2
  rw [neg_add_eq_zero] at h2
  exact h2.symm

theorem vOf_herm (g : UG c (stdJ ν E)) (hd : IsUnit (mat c g).toBlocks₂₂.det) :
    ((-vOf c g).map c)ᵀ = -vOf c g := by
  set D := (mat c g).toBlocks₂₂ with hD
  set C := (mat c g).toBlocks₂₁ with hC
  have hrel : C * (D.map c)ᵀ = D * (C.map c)ᵀ := lower_rel c g
  have hdetc : ((D.map c)ᵀ).det = c D.det := by
    rw [det_transpose, show D.map c = (c : E →+* E).mapMatrix D from rfl, ← RingHom.map_det]; rfl
  have hDs : IsUnit ((D.map c)ᵀ).det := by rw [hdetc]; exact hd.map c
  have hV : vOf c g = D⁻¹ * C := rfl
  have hDV : D * vOf c g = C := by rw [hV, mul_nonsing_inv_cancel_left _ _ hd]
  have hstar : ((vOf c g).map c)ᵀ * (D.map c)ᵀ = (C.map c)ᵀ := by
    rw [← transpose_mul, ← hDV]
    exact congrArg Matrix.transpose (Matrix.map_mul (f := c.toRingHom) (L := D) (M := vOf c g)).symm
  have key : D * ((vOf c g).map c)ᵀ * (D.map c)ᵀ = D * vOf c g * (D.map c)ᵀ := by
    rw [Matrix.mul_assoc, hstar, hDV, hrel]
  have h3 : ((vOf c g).map c)ᵀ = vOf c g := by
    have := congrArg (fun X => D⁻¹ * X * ((D.map c)ᵀ)⁻¹) key
    simp only [Matrix.mul_assoc] at this
    rw [nonsing_inv_mul_cancel_left _ _ hd, nonsing_inv_mul_cancel_left _ _ hd, mul_nonsing_inv _ hDs, Matrix.mul_one,
      Matrix.mul_one] at this
    exact this
  rw [Matrix.map_neg _ (map_neg c), transpose_neg, h3]

open scoped Classical in

def nOf (g : UG c (stdJ ν E)) : UG c (stdJ ν E) :=
  if h : IsUnit (mat c g).toBlocks₂₂.det then unip c (-vOf c g) (vOf_herm c g h) else 1

def kOf (g : UG c (stdJ ν E)) : UG c (stdJ ν E) := (weyl c ν)⁻¹ * nOf c g * weyl c ν

def pOf (g : UG c (stdJ ν E)) : UG c (stdJ ν E) := g * (kOf c g)⁻¹

theorem nOf_mem (g : UG c (stdJ ν E)) : nOf c g ∈ sieg c ν := by
  unfold nOf
  split_ifs with h
  · rw [mem_sieg]
    change (fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₂₁ = 0
    simp
  · exact (sieg c ν).one_mem

theorem pOf_mem (g : UG c (stdJ ν E)) (hd : IsUnit (mat c g).toBlocks₂₂.det) : pOf c g ∈ sieg c ν := by
  rw [mem_sieg]
  have hk : mat c (pOf c g) = mat c g * (-stdJ ν E * (fromBlocks 1 (-(-vOf c g)) 0 1 * stdJ ν E)) := by
    simp only [pOf, kOf, _root_.mul_inv_rev, inv_inv, nOf, dif_pos hd]
    rfl
  rw [hk]
  have hDV : (mat c g).toBlocks₂₂ * vOf c g = (mat c g).toBlocks₂₁ := mul_nonsing_inv_cancel_left _ _ hd
  set M := mat c g
  rw [← fromBlocks_toBlocks M]
  simp [stdJ, fromBlocks_multiply, fromBlocks_neg]
  rw [hDV, add_neg_cancel]

section Top

variable [TopologicalSpace E] [IsTopologicalRing E] [ContinuousInv₀ E] [T2Space E]

theorem continuous_mat : Continuous (mat c : UG c (stdJ ν E) → Matrix (ν ⊕ ν) (ν ⊕ ν) E) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_blk₂₂ : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₂ :=
  continuous_matrix fun _ _ => (continuous_mat c).matrix_elem _ _

theorem continuous_blk₂₁ : Continuous fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₁ :=
  continuous_matrix fun _ _ => (continuous_mat c).matrix_elem _ _

theorem blk₂₂_one : (mat c (1 : UG c (stdJ ν E))).toBlocks₂₂ = 1 := by
  ext i j; simp [mat, toBlocks₂₂, one_apply]

theorem blk₂₁_one : (mat c (1 : UG c (stdJ ν E))).toBlocks₂₁ = 0 := by
  ext i j; simp [mat, toBlocks₂₁, one_apply]

theorem eventually_isUnit : ∀ᶠ g in 𝓝 (1 : UG c (stdJ ν E)), IsUnit (mat c g).toBlocks₂₂.det := by
  have h : Tendsto (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₂.det) (𝓝 1) (𝓝 1) := by
    have := ((continuous_blk₂₂ c).matrix_det).tendsto (1 : UG c (stdJ ν E))
    rwa [blk₂₂_one, det_one] at this
  filter_upwards [h.eventually_ne one_ne_zero] with g hg
  exact isUnit_iff_ne_zero.mpr hg

theorem tendsto_vOf : Tendsto (vOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 0) := by
  have hinv : ContinuousAt (fun g : UG c (stdJ ν E) => (mat c g).toBlocks₂₂⁻¹) 1 := by
    refine ContinuousAt.comp (g := Inv.inv) ?_ (continuous_blk₂₂ c).continuousAt
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv', blk₂₂_one, det_one]
    exact continuousAt_inv₀ one_ne_zero
  have h2 : Tendsto (vOf c) (𝓝 1) (𝓝 (vOf c 1)) := (hinv.mul (continuous_blk₂₁ c).continuousAt).tendsto
  have h0 : vOf c (1 : UG c (stdJ ν E)) = 0 := by rw [vOf, blk₂₁_one, Matrix.mul_zero]
  rwa [h0] at h2

theorem tendsto_nOf : Tendsto (nOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := by
  rw [tendsto_subtype_rng, Units.isInducing_embedProduct.tendsto_nhds_iff]
  have hv := tendsto_vOf c (ν := ν)
  have hA : Tendsto (fun g => (fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) (𝓝 1) (𝓝 1) := by
    have hc : Continuous fun v : Matrix ν ν E => (fromBlocks 1 (-v) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E) :=
      continuous_const.matrix_fromBlocks continuous_neg continuous_const continuous_const
    have := (hc.tendsto 0).comp hv
    rwa [neg_zero, fromBlocks_one] at this
  have hB : Tendsto (fun g => (fromBlocks 1 (-(-vOf c g)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E)) (𝓝 1) (𝓝 1) := by
    have hc : Continuous fun v : Matrix ν ν E => (fromBlocks 1 (-(-v)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E) :=
      continuous_const.matrix_fromBlocks continuous_neg.neg continuous_const continuous_const
    have := (hc.tendsto 0).comp hv
    rwa [neg_zero, neg_zero, fromBlocks_one] at this
  have hE : (fun g => ((fromBlocks 1 (-vOf c g) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E),
      MulOpposite.op (fromBlocks 1 (-(-vOf c g)) 0 1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E))) =ᶠ[𝓝 1]
      (Units.embedProduct _ ∘ fun g => ((nOf c g : UG c (stdJ ν E)) : GL (ν ⊕ ν) E)) := by
    filter_upwards [eventually_isUnit c] with g hg
    simp only [Function.comp_apply, nOf, dif_pos hg]
    rfl
  refine Tendsto.congr' hE ?_
  have h1 : Units.embedProduct _ ((1 : UG c (stdJ ν E)) : GL (ν ⊕ ν) E) = (1, MulOpposite.op 1) := rfl
  rw [h1]
  exact hA.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hB)

end Top

end GlobalTheory.KSp.OpenCrit

namespace GlobalTheory.KSp

open OpenCrit in

theorem isOpen_of_sieg_of_opp (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E)))
    (h1 : ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → g ∈ U)
    (h2 : ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → (weyl c ν)⁻¹ * g * weyl c ν ∈ U) :
    IsOpen (U : Set (UG c (stdJ ν E))) := by
  obtain ⟨-, hTR, hCI, hT2, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  haveI := hTR
  haveI := hCI
  haveI := hT2
  refine Subgroup.isOpen_of_mem_nhds U (g := 1) ?_
  have hn : Tendsto (nOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := tendsto_nOf c
  have hk : Tendsto (kOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (weyl c ν)⁻¹)).mul hn).mul (tendsto_const_nhds (x := weyl c ν))
    rwa [mul_one, inv_mul_cancel] at this
  have hp : Tendsto (pOf c) (𝓝 (1 : UG c (stdJ ν E))) (𝓝 1) := by
    have := (tendsto_id (x := 𝓝 (1 : UG c (stdJ ν E)))).mul hk.inv
    rwa [inv_one, mul_one] at this
  filter_upwards [hp.eventually h1, hn.eventually h2, eventually_isUnit c] with g hpg hng hd
  have hg : g = pOf c g * kOf c g := by rw [pOf, inv_mul_cancel_right]
  rw [hg]
  exact U.mul_mem (hpg (pOf_mem c g hd)) (hng (nOf_mem c g))

end GlobalTheory.KSp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwahoriRegularSplit
section
open Polynomial ValuativeRel

namespace GlobalTheory.IwahoriRegular

theorem regular_split : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ),
  ValuativeRel.valuation k (ϖ : k) = ValuativeRel.uniformizer k →
  ∀ ν : Fin N → ℤ, StrictAnti ν → ∀ x ∈ GlobalTheory.SmGL.iwahori k (Fin N), ∀ y ∈ GlobalTheory.SmGL.iwahori k (Fin N),
    let g := x * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν * y
    (g : Matrix (Fin N) (Fin N) k).charpoly.Separable ∧ (g : Matrix (Fin N) (Fin N) k).charpoly.Splits := by
  intro k _ _ _ _ N ϖ hϖ ν hν x hx y hy
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  let w : 𝒪[k] := ⟨ϖ, hlt.le⟩
  have hw : Irreducible w := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    ext z
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one,
      Ideal.mem_span_singleton, (Valuation.integer.integers (valuation k)).dvd_iff_le, ← le_uniformizer_iff, ← hϖ]
    rfl
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  have low : ∀ h : GL (Fin N) 𝒪[k], h ∈ (GlobalTheory.SmGL.borel 𝓀[k] (Fin N)).comap
      (Matrix.GeneralLinearGroup.map (n := Fin N) (IsLocalRing.residue 𝒪[k])) →
      ∀ i j, j < i → (h : Matrix (Fin N) (Fin N) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    intro h hh i j hij
    have := (GlobalTheory.SmGL.mem_borel _).1 hh i j hij
    exact (IsLocalRing.residue_eq_zero_iff _).1 this
  obtain ⟨r, hr, hchar⟩ := GlobalTheory.IwahoriRoots.iwahori_roots 𝒪[k] k w hw N ν hν x' y' (low x' hx') (low y' hy')
  have hinj : Function.Injective r := fun i j h => hν.injective (by rw [← (hr i).2, ← (hr j).2, h])
  have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) x' * GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν *
      Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) y' : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      (x' : Matrix (Fin N) (Fin N) 𝒪[k]).map (algebraMap 𝒪[k] k) *
        Matrix.diagonal (fun i => algebraMap 𝒪[k] k w ^ ν i) *
        (y' : Matrix (Fin N) (Fin N) 𝒪[k]).map (algebraMap 𝒪[k] k) := by
    rw [Units.val_mul, Units.val_mul, GlobalTheory.GLDoubling.val_torusElt]
    rfl
  show Separable (Matrix.charpoly _) ∧ Splits (Matrix.charpoly _)
  rw [e, hchar]
  exact ⟨separable_prod_X_sub_C_iff.2 hinj, Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _⟩

end GlobalTheory.IwahoriRegular
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerNeBotAndNotEffCartierStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_ne_bot_and_not_effCartier_of_two_le_dim : ∀ {W Y : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian Y] (i : W ⟶ Y) [IsClosedImmersion i], 2 ≤ ringKrullDim (Y.presheaf.stalk (i (genericPoint W))) → i.ker ≠ ⊥ ∧ ∀ U : Y.Opens, i (genericPoint W) ∈ U → ¬ FinalTheorems.EffCartier (i.ker.comap U.ι) := by
  first | exact @GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier | exact GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier | (intros; apply GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelSpecTensorPowerStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentCechNerve_level_spec_tensorPower : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (k : ℕ),
  ∃ (e0 : yoneda.obj (Spec (CommRingCat.of (PiTensorProduct A (fun _ : Fin (k + 1) => A')))) ≅ (cech (baseHom A A')).obj (op ⦋k⦌))
    (e : yoneda.obj (Spec (CommRingCat.of (LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))))) ≅
      (cech (laurentHom A A')).obj (op ⦋k⦌)),
    e.hom ≫ (cechC A A').app (op ⦋k⦌) =
      yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : PiTensorProduct A (fun _ : Fin (k + 1) => A') →+*
        LaurentPolynomial (PiTensorProduct A (fun _ : Fin (k + 1) => A'))))) ≫ e0.hom ∧
    e.hom ≫ (cechAug (laurentHom A A')).app (op ⦋k⦌) =
      yoneda.map (Spec.map (CommRingCat.ofHom (laurentMap (algebraMap A (PiTensorProduct A (fun _ : Fin (k + 1) => A')))))) := by
  first | (exact @GlobalTheory.EtC.GmStep.LevelIso.level_iso) | (exact GlobalTheory.EtC.GmStep.LevelIso.level_iso) | (intros; apply GlobalTheory.EtC.GmStep.LevelIso.level_iso  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPiBijective
section
open GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_pi_bijective : ∀ (n : ℕ) (B : Fin n → Type) [∀ j, CommRing (B j)], Function.Bijective (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)) := by
  first | (exact @GlobalTheory.EtC.GmStep.laurentPi_bijective) | (exact GlobalTheory.EtC.GmStep.laurentPi_bijective) | (intros; apply GlobalTheory.EtC.GmStep.laurentPi_bijective  <;> assumption)
end

