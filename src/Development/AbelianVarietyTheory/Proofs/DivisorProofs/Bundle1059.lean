import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0413
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0454
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprime
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1018

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubringStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_descends_to_finitelyGenerated_subring : ∀ (R : Type) [CommRing R] (g : ℕ) (A : Over (Sp R)) [GrpObj A] (F : Finset R), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧
      IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ IsGrpPullback A B (spMap S.subtype) φ := by
  first | exact @GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring | exact GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring | (intros; apply GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsolutelyIntegrallyClosedDomainTateTwistAcyclic
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.AicAcyc

theorem aic_of_isAlgClosed (K : Type) [Field K] [IsAlgClosed K] : AIC K := by
  intro p hp hdeg
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero]; exact_mod_cast hdeg.ne')
  exact ⟨a, ha⟩

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem isIso_spMap {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) : IsIso (spMap (e : A →+* B)) := by
  haveI : IsIso (CommRingCat.ofHom (e : A →+* B)) := (RingEquiv.toCommRingCatIso e).isIso_hom
  unfold spMap
  infer_instance

end GlobalTheory.EtC.AicAcyc

namespace GlobalTheory.EtC

open GlobalTheory.EtC.AicAcyc in

theorem b5 : B5 := by
  intro q A _ _ hA hq n i hn
  haveI := GlobalTheory.T.isAlgClosed_fractionRing_of_monic_polynomials_have_roots A hA
  have hK : SH (FractionRing A) :=
    GlobalTheory.T.isStrictlyHenselian_of_isField_monicRoots (FractionRing A) (Field.toIsField _) (aic_of_isAlgClosed _)
  have hE := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have heqv : Eqv (ZMod q) (spMap (algebraMap A (FractionRing A))) (tw q i) := by
    refine GlobalTheory.T.etaleCohomology_local_to_global_ringMap_indEtale (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) A A (FractionRing A)
      (Algebra.ofId A (FractionRing A)) ?_
    intro O _ _ hO hOind
    obtain ⟨hfield, haic⟩ := GlobalTheory.T.isField_monicRoots_tensor_fractionRing_strictlyHenselian A O hA hO hOind
    have hSH : SH (O ⊗[A] FractionRing A) := GlobalTheory.T.isStrictlyHenselian_of_isField_monicRoots _ hfield haic
    have hqO : IsUnit (q : O) := by
      simpa using hq.map (algebraMap A O)
    let e := Algebra.TensorProduct.rid A A O
    let j : O →ₐ[A] O ⊗[A] FractionRing A := Algebra.TensorProduct.includeLeft
    have hψ : (Algebra.TensorProduct.map (AlgHom.id A O) (Algebra.ofId A (FractionRing A))) =
        j.comp e.toAlgHom := by
      apply Algebra.TensorProduct.ext'
      intro o a
      simp [j, e, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [hψ]
    have h1 : Eqv (ZMod q) (spMap (j : O →+* O ⊗[A] FractionRing A)) (tw q i) :=
      GlobalTheory.T.eqv_spMap_tw_of_isUnit q i O _ (j : O →+* O ⊗[A] FractionRing A) hO hSH hqO
    have h2 : Eqv (ZMod q) (spMap ((e : O ⊗[A] A ≃+* O) : O ⊗[A] A →+* O)) (tw q i) := by
      haveI := isIso_spMap (e : O ⊗[A] A ≃+* O)
      exact hE.1 _ _ _ inferInstance
    have h3 := (hE.2.1 _ _ _ _ _).1 h1 h2
    rw [← spMap_comp] at h3
    exact h3
  have hacK : AcycF (ZMod q) (sp (FractionRing A)) (tw q i) :=
    fun m hm => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) (FractionRing A) hK (tw q i) m hm
  exact (hE.2.2.2 _ _ _ heqv).1 hacK n hn

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprimeStatement
section
open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_plane_hermitian_ideal_coprime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) (i₀ i₁ r s : ℕ),
    B.IsGood σ → Y.IsHerm σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → i₀ < n → i₁ < n →
    H.𝔟 ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P → FractionalIdeal.count E w H.𝔟 = 0 := by
  first | exact @GlobalTheory.AdaptedPlaneIdeal.ideal_ne_zero_and_count_eq_zero | exact GlobalTheory.AdaptedPlaneIdeal.ideal_ne_zero_and_count_eq_zero | (intros; apply GlobalTheory.AdaptedPlaneIdeal.ideal_ne_zero_and_count_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditivePicClassOfLocallyAdditiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_picClass_of_locally_additive : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A], IsAbelianScheme A → ∀ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (lift (1 : T ⟶ A) (𝟙 T)).left c = 0 → (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧ AddCls A (GlobalTheory.CechPic.pull (A ◁ z).left c)) → AddCls A c := by
  first | exact @GlobalTheory.PicGlue.addCls_of_locally | exact GlobalTheory.PicGlue.addCls_of_locally | (intros; apply GlobalTheory.PicGlue.addCls_of_locally <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelesSelfDual
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.CentPos

theorem eq_smul_of_eigen {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (Z : GL (Fin n) ℂ) (lam : Fin n → ℂ)
    (hlam : Function.Injective lam) (hZ : M * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * diagonal lam)
    (μ : ℂ) (u w : Fin n → ℂ) (hu : M *ᵥ u = μ • u) (hw : M *ᵥ w = μ • w) (hu0 : u ≠ 0) :
    ∃ l : ℂ, w = l • u := by
  set Zm : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ)
  set Zi : Matrix (Fin n) (Fin n) ℂ := ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
  have h1 : Zi * Zm = 1 := by simp [Zi, Zm, ← Units.val_mul]
  have h2 : Zm * Zi = 1 := by simp [Zi, Zm, ← Units.val_mul]
  have hD : Zi * M = diagonal lam * Zi := by
    calc Zi * M = Zi * (M * Zm) * Zi := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = Zi * (Zm * diagonal lam) * Zi := by rw [hZ]
      _ = diagonal lam * Zi := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hcoord : ∀ a : Fin n → ℂ, M *ᵥ a = μ • a → ∀ j, lam j * (Zi *ᵥ a) j = μ * (Zi *ᵥ a) j := by
    intro a ha j
    have e : diagonal lam *ᵥ (Zi *ᵥ a) = μ • (Zi *ᵥ a) := by
      rw [mulVec_mulVec, ← hD, ← mulVec_mulVec, ha, mulVec_smul]
    have := congrFun e j
    rwa [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
  have hback : ∀ a : Fin n → ℂ, Zm *ᵥ (Zi *ᵥ a) = a := by
    intro a; rw [mulVec_mulVec, h2, one_mulVec]
  set u' := Zi *ᵥ u
  set w' := Zi *ᵥ w
  have hu'0 : u' ≠ 0 := by
    intro h; apply hu0; rw [← hback u]; show Zm *ᵥ u' = 0; rw [h, mulVec_zero]
  obtain ⟨i0, hi0⟩ : ∃ i0, u' i0 ≠ 0 := by
    by_contra h; push_neg at h; exact hu'0 (funext h)
  have hlam0 : lam i0 = μ := mul_right_cancel₀ hi0 (hcoord u hu i0)
  refine ⟨w' i0 / u' i0, ?_⟩
  have hw' : w' = (w' i0 / u' i0) • u' := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases hj : j = i0
    · subst hj; field_simp
    · have hne : lam j - μ ≠ 0 := by
        intro h; apply hj; apply hlam; rw [hlam0]; exact sub_eq_zero.1 h
      have hu0j : u' j = 0 := by
        have := hcoord u hu j
        have h' : (lam j - μ) * u' j = 0 := by rw [sub_mul]; exact sub_eq_zero.2 this
        exact (mul_eq_zero.1 h').resolve_left hne
      have hw0j : w' j = 0 := by
        have := hcoord w hw j
        have h' : (lam j - μ) * w' j = 0 := by rw [sub_mul]; exact sub_eq_zero.2 this
        exact (mul_eq_zero.1 h').resolve_left hne
      rw [hu0j, hw0j, mul_zero]
  calc w = Zm *ᵥ w' := (hback w).symm
    _ = Zm *ᵥ ((w' i0 / u' i0) • u') := by rw [← hw']
    _ = (w' i0 / u' i0) • u := by rw [mulVec_smul, hback u]

theorem cent_form_law {p : ℕ} [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F)
    (y : G.Cˣ × ℚˣ) (hy : y ∈ P.cent) :
    (G.psi v (y.1 : G.C))ᴴ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) * G.psi v (y.1 : G.C) =
      (((y.2 : ℚˣ) : ℚ) : ℂ) • (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
  have hsim : (y.1 : G.C) * P.β * sh G y.1 = algebraMap ℚ G.C (y.2 : ℚ) * P.β := hy.2
  have hgu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.mpr (G.gram_det v)
  have hgg : G.gram v * (G.gram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have hgg' : (G.gram v)⁻¹ * G.gram v = 1 := Matrix.nonsing_inv_mul _ hgu
  have hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹ := by
    intro x
    have e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := G.psi_star v x
    rw [e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]
  have hu : sh G (y.1 : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1 =
      algebraMap ℚ G.C (y.2 : ℚ) * ((P.β⁻¹ : G.Cˣ) : G.C) := by
    apply (Units.mul_right_inj (y.1 * P.β)).mp
    rw [Units.val_mul, ← Algebra.smul_def]
    calc (y.1 : G.C) * P.β * (sh G (y.1 : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1)
        = ((y.1 : G.C) * P.β * sh G (y.1 : G.C)) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1 := by
          simp only [mul_assoc]
      _ = (y.2 : ℚ) • ((P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1) := by
          rw [hsim, ← Algebra.smul_def]; simp only [smul_mul_assoc]
      _ = (y.2 : ℚ) • ((y.1 : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C)) := by
          rw [Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [mul_smul_comm, mul_assoc]
  rw [hH]
  calc G.gram v * G.psi v (sh G (y.1 : G.C)) * (G.gram v)⁻¹ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *
        G.psi v (y.1 : G.C)
      = G.gram v * (G.psi v (sh G (y.1 : G.C)) * ((G.gram v)⁻¹ * G.gram v) *
          G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) * G.psi v (y.1 : G.C)) := by simp only [mul_assoc]
    _ = G.gram v * G.psi v (sh G (y.1 : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1) := by
        rw [hgg', mul_one, map_mul, map_mul]
    _ = G.gram v * (((y.2 : ℚˣ) : ℚ) • G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
        rw [hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]
    _ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]

end GlobalTheory.LKMid.CentPos

namespace GlobalTheory.LKMid

open GlobalTheory.LKMid.CentPos in

theorem cent_sim_pos : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ y ∈ P.cent, 0 < ((y.2 : ℚˣ) : ℚ) := by
  intro p _ G P μ _ hm y hy
  obtain ⟨v, -, x, hx, hpos⟩ := hm
  set H := G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) with hHdef
  set M := G.psi v (P.γ : G.C) with hMdef
  set Y := G.psi v (y.1 : G.C) with hYdef
  have hc : (y.1 : G.C) * P.γ = P.γ * y.1 := by
    have := congrArg Units.val hy.1; simpa using this
  have hMY : M * Y = Y * M := by rw [hMdef, hYdef, ← map_mul, ← map_mul, hc]
  have hform : Yᴴ * H * Y = (((y.2 : ℚˣ) : ℚ) : ℂ) • H := cent_form_law G P v y hy
  obtain ⟨Z, lam, hinj, -, hZ⟩ := psi_eigenbasis p G P v
  have hx0 : x ≠ 0 := by rintro rfl; simp at hpos
  have hYx : M *ᵥ (Y *ᵥ x) = μ • (Y *ᵥ x) := by
    rw [mulVec_mulVec, hMY, ← mulVec_mulVec, hx, mulVec_smul]
  obtain ⟨l, hl⟩ := eq_smul_of_eigen M Z lam hinj hZ μ x (Y *ᵥ x) hx hYx hx0
  have key : star (Y *ᵥ x) ⬝ᵥ (H *ᵥ (Y *ᵥ x)) = star x ⬝ᵥ ((Yᴴ * H * Y) *ᵥ x) := by
    rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_vecMul]
    simp only [hHdef, Matrix.mul_assoc]
  rw [hform, hl] at key
  simp only [Matrix.smul_mulVec, mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at key
  set q := star x ⬝ᵥ (H *ᵥ x) with hq
  have hq0 : q ≠ 0 := by intro h; rw [h] at hpos; simp at hpos
  have hs : star l * l = (((y.2 : ℚˣ) : ℚ) : ℂ) := by
    rw [← mul_assoc] at key; have := mul_right_cancel₀ hq0 key; rw [mul_comm] at this; exact this
  have hsre : ((((y.2 : ℚˣ) : ℚ) : ℂ)).re = ((y.2 : ℚˣ) : ℚ) := by simp
  have hnn : (0 : ℝ) ≤ (((y.2 : ℚˣ) : ℚ) : ℝ) := by
    have : (star l * l).re = Complex.normSq l := by
      rw [mul_comm, Complex.star_def, Complex.mul_conj]; simp
    rw [hs] at this
    have h2 : ((((y.2 : ℚˣ) : ℚ) : ℂ)).re = (((y.2 : ℚˣ) : ℚ) : ℝ) := by simp
    rw [← h2, this]; exact Complex.normSq_nonneg l
  have hnn' : (0 : ℚ) ≤ ((y.2 : ℚˣ) : ℚ) := by exact_mod_cast hnn
  exact lt_of_le_of_ne hnn' (Ne.symm (y.2.ne_zero))

example : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ y ∈ P.cent, 0 < ((y.2 : ℚˣ) : ℚ) := cent_sim_pos

end GlobalTheory.LKMid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicModuleNormRationalUnitEqOneStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicModule_norm_rationalUnit_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (u : (AE F E)ˣ) (z : E), (u : AE F E) = inclR (AF F) z → (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) u) = 1 := by
  first | exact @GlobalTheory.NormModule.modu_norm_rat | exact GlobalTheory.NormModule.modu_norm_rat | (intros; apply GlobalTheory.NormModule.modu_norm_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictTranslatedDiagonalMem
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix

noncomputable section
namespace GlobalTheory.DiagShift

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField

variable (F κ) in

def diagA : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ ⊕ κ → mixedEmbedding.mixedSpace F) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => Sum.elim x x
      map_add' := fun x x' => by funext i; cases i <;> simp
      map_smul' := fun c x => by funext i; cases i <;> simp }

theorem diagA_apply (x : κ → mixedEmbedding.mixedSpace F) : diagA F κ x = Sum.elim x x := rfl

theorem norm_le_diagA (x : κ → mixedEmbedding.mixedSpace F) : ‖x‖ ≤ ‖diagA F κ x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => by
    simpa [diagA_apply] using norm_le_pi_norm (diagA F κ x) (Sum.inl j)

variable (F κ) in

def restrA : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
  SchwartzMap.compCLM ℂ (diagA F κ).hasTemperateGrowth
    ⟨1, 1, fun x => by
      have := norm_le_diagA x
      have h0 := norm_nonneg (diagA F κ x)
      rw [pow_one, one_mul]; linarith⟩

theorem restrA_apply (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ) (x : κ → mixedEmbedding.mixedSpace F) :
    restrA F κ f x = f (Sum.elim x x) := rfl

theorem shift_mem_finite {g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F)) (b : κ → FiniteAdeleRing (𝓞 F) F) :
    (fun y : κ → FiniteAdeleRing (𝓞 F) F => g (Sum.elim (y + b) y)) ∈ finiteSchwartzBruhatPi F := by
  have hd : Continuous fun y : κ → FiniteAdeleRing (𝓞 F) F =>
      (Sum.elim (y + b) y : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :=
    continuous_pi fun i => by
      cases i with
      | inl j => exact (continuous_apply j).add continuous_const
      | inr j => exact continuous_apply j
  have hr : Continuous fun z : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F => fun j => z (Sum.inr j) :=
    continuous_pi fun j => continuous_apply _
  refine ⟨hg.1.comp_continuous hd, ?_⟩
  refine HasCompactSupport.intro (hg.2.isCompact.image hr) fun y hy => ?_
  by_contra h
  exact hy ⟨Sum.elim (y + b) y, subset_tsupport _ h, rfl⟩

theorem shift_pureA_mem (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F))
    (u : κ → AdeleRing (𝓞 F) F) :
    (fun t : κ → AdeleRing (𝓞 F) F => pureA F f g (Sum.elim (t + u) t)) ∈ schwartzBruhatPi F κ := by
  have key : (fun t : κ → AdeleRing (𝓞 F) F => pureA F f g (Sum.elim (t + u) t)) =
      schwartzBruhatTensorPi
        (restrA F κ (SchwartzMap.compSubConstCLM ℂ (-Sum.elim (infPartPi u) 0) f))
        (fun y : κ → FiniteAdeleRing (𝓞 F) F => g (Sum.elim (y + finPartPi u) y)) := by
    funext t
    simp only [schwartzBruhatTensorPi, restrA_apply, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
    unfold pureA
    congr 1
    · congr 1
      funext i
      cases i with
      | inl j => exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (t j).1 (u j).1
      | inr j => exact (add_zero _).symm
    · congr 1
      funext i
      cases i <;> rfl
  rw [key]
  exact schwartzBruhatTensorPi_mem _ (shift_mem_finite hg _)

theorem shift_mem_schwartzBruhatPi (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (φ : (κ ⊕ κ → AF F) → ℂ) (hφ : φ ∈ schA F (κ ⊕ κ)) (u : κ → AF F) :
    (fun t : κ → AF F => φ (Sum.elim (t + u) t)) ∈ schwartzBruhatPi F κ := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    exact shift_pureA_mem f hg u
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

end GlobalTheory.DiagShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartzSpace_translate_mem : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : κ → AF F), ∀ φ ∈ schA F κ, (fun x => φ (x + a)) ∈ schA F κ := by
  first | exact @GlobalTheory.SchwartzTranslate.main | exact GlobalTheory.SchwartzTranslate.main | (intros; apply GlobalTheory.SchwartzTranslate.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaDistributionSumProductFunctionStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicThetaDistributionSum_productFunction : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ', thetaSum F (boxFun φ₁ φ₂) = thetaSum F φ₁ * thetaSum F φ₂ := by
  first | exact @GlobalTheory.ThetaBox.thetaSum_boxFun | exact GlobalTheory.ThetaBox.thetaSum_boxFun | (intros; apply GlobalTheory.ThetaBox.thetaSum_boxFun <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisOfTraceMemEventually
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LocIntSpan

theorem isIntB_of_trace_mem :
    ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (bL : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ E : v.adicCompletion ℚ ⊗[ℚ] L,
      (∀ i, Algebra.trace (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L)
          (E * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] bL i)) ∈ v.adicCompletionIntegers ℚ) →
        IsIntB v bL E := by
  intro L _ _ κ bL
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex bL
  have hd : Algebra.discr ℚ bL ≠ 0 := Algebra.discr_not_zero_of_basis ℚ bL
  obtain ⟨S, hS⟩ := exists_finset_algebraMap_mem
    (insert (Algebra.discr ℚ bL)⁻¹
      (Finset.univ.image fun p : κ × κ => Algebra.trace ℚ L (bL p.1 * bL p.2)))
  refine ⟨S, fun v hv E hE => ?_⟩
  set Q := v.adicCompletion ℚ
  let B := Algebra.TensorProduct.basis Q bL
  have hB : ∀ i, B i = (1 : Q) ⊗ₜ[ℚ] bL i := fun i => by
    simp [B, Algebra.TensorProduct.basis_apply]
  have htr : ∀ i j, Algebra.trace Q (Q ⊗[ℚ] L) (B i * B j) =
      algebraMap ℚ Q (Algebra.trace ℚ L (bL i * bL j)) := fun i j => by
    rw [hB, hB, Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_one_tmul']
  have hTM : Algebra.traceMatrix Q B = (algebraMap ℚ Q).mapMatrix (Algebra.traceMatrix ℚ bL) := by
    refine Matrix.ext fun i j => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, Algebra.traceForm_apply]
    exact htr i j
  have hdet : (Algebra.traceMatrix Q B).det = algebraMap ℚ Q (Algebra.discr ℚ bL) := by
    rw [hTM, ← RingHom.map_det, Algebra.discr_def]
  have hG : ∀ i j, ∃ u : v.adicCompletionIntegers ℚ, algebraMap (v.adicCompletionIntegers ℚ) Q u =
      Algebra.trace Q (Q ⊗[ℚ] L) (B i * B j) := fun i j =>
    ⟨⟨_, hS v hv _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))⟩,
      (htr i j).symm⟩
  have hω : ∀ i, ∃ u : v.adicCompletionIntegers ℚ, algebraMap (v.adicCompletionIntegers ℚ) Q u =
      Algebra.trace Q (Q ⊗[ℚ] L) (E * B i) := fun i => ⟨⟨_, by rw [hB]; exact hE i⟩, rfl⟩
  obtain ⟨u, hu⟩ := GlobalTheory.DiscConductor.det_smul_eq_sum (v.adicCompletionIntegers ℚ) Q (Q ⊗[ℚ] L) κ B E hG hω
  intro j
  have hrep : B.repr E j = (algebraMap ℚ Q (Algebra.discr ℚ bL))⁻¹ *
      algebraMap (v.adicCompletionIntegers ℚ) Q (u j) := by
    have h1 := congrArg (fun x => B.repr x j) hu
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_sum, Finsupp.coe_finset_sum,
      Finset.sum_apply, Module.Basis.repr_self, Finsupp.single_apply, hdet] at h1
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)] at h1
    simp only [if_true, mul_one] at h1
    have hne : algebraMap ℚ Q (Algebra.discr ℚ bL) ≠ 0 := (map_ne_zero _).2 hd
    rw [← h1, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  show B.repr E j ∈ v.adicCompletionIntegers ℚ
  rw [hrep, ← map_inv₀]
  exact mul_mem (hS v hv _ (Finset.mem_insert_self _ _)) (u j).2

end GlobalTheory.LocIntSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisRingEventually
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

theorem isIntB_one_mul_eventually : ∀ (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (κ : Type)
    (b : Module.Basis κ ℚ A),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, IsIntB v b 1 ∧
      ∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z) := by
  intro A _ _ _ κ b
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hc : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b t.1 * b t.2.1) t.2.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have h1 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ k : κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr 1 k) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun k => rat_mem_adicCompletionIntegers_eventually _
  have hfin := Filter.eventually_cofinite.1 (hc.and h1)
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  obtain ⟨hcv, h1v⟩ := hv
  refine ⟨fun k => ?_, fun y z hy hz k => ?_⟩
  · rw [Algebra.TensorProduct.one_def, repr_tmul_apply, one_mul]
    exact h1v k
  · rw [eq_sum_tmul b v y, eq_sum_tmul b v z, Finset.sum_mul_sum, map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun i _ => ?_
    rw [map_sum, Finsupp.finset_sum_apply]
    refine sum_mem fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply]
    exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))

end GlobalTheory.AdicSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalEqZeroOfSqEqZeroOfPosDefSimilitudeStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_eq_zero_of_sq_eq_zero_of_posDef_similitude : ∀ (n : ℕ) (H M : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), H.PosDef → 0 < s → Mᴴ * H * M = (s : ℂ) • H → ∀ P : Polynomial ℂ, Polynomial.aeval M P * Polynomial.aeval M P = 0 → Polynomial.aeval M P = 0 := by
  first | (exact @GlobalTheory.aeval_eq_zero_of_mul_self_eq_zero_of_similitude) | (exact GlobalTheory.aeval_eq_zero_of_mul_self_eq_zero_of_similitude) | (intros; apply GlobalTheory.aeval_eq_zero_of_mul_self_eq_zero_of_similitude  <;> assumption)
end

