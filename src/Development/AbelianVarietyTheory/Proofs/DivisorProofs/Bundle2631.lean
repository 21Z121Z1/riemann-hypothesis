import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenOfIsTopFormFrameStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCoordinatesOnOpen_of_isTopFormFrame : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (V : Y.Opens) (z : Fin n → Γ(Y, V)), IsFrame (dOn q z) → IsAffineOpen V ∧ IsEtCoord q V z := by
  first | exact @GlobalTheory.FrameEtale.isEtCoord_of_isFrame | exact GlobalTheory.FrameEtale.isEtCoord_of_isFrame | (intros; apply GlobalTheory.FrameEtale.isEtCoord_of_isFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFromSpecResidueFieldCompOfIsClosedOfClos
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem isFinite_fromSpecResidueField_comp_of_isClosed_of_closedPoint : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Over (Sp R)), LocallyOfFiniteType X.hom → ∀ x : X.left, X.hom x = closedPoint R → IsClosed ({x} : Set X.left) → IsFinite (X.left.fromSpecResidueField x ≫ X.hom) := by
  intro R _ _ X hX x hx hc
  haveI := hX
  haveI := isClosed_singleton_iff_isClosedImmersion.mp hc
  have hf : LocallyOfFiniteType (X.left.fromSpecResidueField x ≫ X.hom) := inferInstance
  have hpt : ∀ p : Spec (X.left.residueField x), (X.left.fromSpecResidueField x ≫ X.hom) p = closedPoint R := by
    intro p
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply, hx]
  rw [← Spec.map_preimage (X.left.fromSpecResidueField x ≫ X.hom)] at hf hpt ⊢
  rw [IsFinite.SpecMap_iff]
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hf
  generalize Spec.preimage (X.left.fromSpecResidueField x ≫ X.hom) = φ at hf hpt ⊢
  let K := X.left.residueField x
  let p0 : PrimeSpectrum K := ⟨⊥, Ideal.bot_prime⟩
  have hker : RingHom.ker φ.hom = maximalIdeal R := by
    have h1 := congrArg PrimeSpectrum.asIdeal (hpt p0)
    have h2 : (Spec.map φ).base p0 = PrimeSpectrum.comap φ.hom p0 := rfl
    rw [show (Spec.map φ) p0 = (Spec.map φ).base p0 from rfl, h2] at h1
    have h3 : Ideal.comap φ.hom ⊥ = (closedPoint R).asIdeal := by simpa [p0] using h1
    exact h3
  let k := ResidueField R
  let ψ : k →+* K := Ideal.Quotient.lift (maximalIdeal R) φ.hom (fun a ha => by
    rw [← RingHom.mem_ker, hker]; exact ha)
  have hφ : φ.hom = ψ.comp (residue R) := by
    ext a; rfl
  rw [hφ] at hf ⊢
  have hψ : ψ.FiniteType := RingHom.FiniteType.of_comp_finiteType hf
  letI : Algebra k K := ψ.toAlgebra
  haveI : Algebra.FiniteType k K := hψ
  have : Module.Finite k K := finite_of_finite_type_of_isJacobsonRing k K
  have hψf : ψ.Finite := this
  exact hψf.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.FlagConnect

def Carries {B Y T : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g)
    (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a)) : Prop :=
  ∀ a i, ∃ e : (Scheme.Modules.pullback g').obj ((fl a).F i) ≅ (fl' a).F i,
    e.hom ≫ (fl' a).ι i = (Scheme.Modules.pullback g').map ((fl a).ι i) ≫
      (Scheme.Modules.pullbackComp g' π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a)

theorem isFlagBundle_iff {B Y : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) :
    CovTest.IsFlagBundle π E n fl ↔ ∀ (T : Scheme.{0}) (g : T ⟶ B)
      (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a)),
      ∃! g' : T ⟶ Y, ∃ w : g' ≫ π = g, Carries π E n fl g' g w fl' := Iff.rfl

def carried {B Y T : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g) :
    ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a) := fun a =>
  ((fl a).pull g').ofIso ((Scheme.Modules.pullbackComp g' π).app (E a) ≪≫ (Scheme.Modules.pullbackCongr w).app (E a))

theorem carries_carried {B Y T : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g) :
    Carries π E n fl g' g w (carried π E n fl g' g w) := fun a i =>
  ⟨Iso.refl _, by simp [carried, Vert.Flag.ofIso, Vert.Flag.pull]⟩

theorem carries_comp {B Y T T' : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g)
    (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a)) (h : T' ⟶ T) (k : T' ⟶ B) (v : h ≫ g = k)
    (fl'' : ∀ a, Vert.Flag ((Scheme.Modules.pullback k).obj (E a)) (n a)) (w' : (h ≫ g') ≫ π = k) :
    Carries π E n fl g' g w fl' → Carries g E n fl' h k v fl'' → Carries π E n fl (h ≫ g') k w' fl'' := by
  subst w v
  intro H₁ H₂ a i
  obtain ⟨e, he⟩ := H₁ a i
  obtain ⟨e', he'⟩ := H₂ a i
  refine ⟨(Scheme.Modules.pullbackComp h g').symm.app _ ≪≫ (Scheme.Modules.pullback h).mapIso e ≪≫ e', ?_⟩
  have assoc := congr_arg (fun φ => φ.app (E a)) (Scheme.Modules.pseudofunctor_associativity h g' π)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp, eqToHom_app] at assoc
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc, he']
  rw [← Functor.map_comp_assoc, he]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id,
    Functor.map_comp, Category.assoc]
  erw [← NatTrans.naturality_assoc]
  congr 1
  rw [← cancel_epi ((Scheme.Modules.pullbackComp h (g' ≫ π)).symm.app (E a) ≪≫
    (Scheme.Modules.pullback h).mapIso ((Scheme.Modules.pullbackComp g' π).symm.app (E a)) ≪≫
      (Scheme.Modules.pullbackComp h g').app _).hom]
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% assoc]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app, eqToIso.hom, eqToHom_app, eqToHom_trans, eqToHom_refl]
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]

end GlobalTheory.FlagConnect

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenWedgeFormOfFormallyEtaleMvPolynomial
section
open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct

namespace GlobalTheory.TopFrameEt

theorem isFreeGen_dForm_of_formallyEtale_mvPolynomial :
    ∀ {k A₀ A : Type} [CommRing k] [CommRing A₀] [CommRing A] (α : k →+* A₀) (β : k →+* A)
    (ρ : A₀ →+* A), ρ.comp α = β → ∀ {n r : ℕ} (z : Fin n → A₀) (b : Module.Basis (Fin n) A₀ (Omega α)),
    (∀ i, b i = dFun α (z i)) → ∀ (t : Fin r → A), (MvPolynomial.eval₂Hom ρ t).FormallyEtale →
    IsFreeGen A (dForm β (Fin.append t (fun i => ρ (z i)))) := by
  intro k A₀ A _ _ _ α β ρ hc n r z b hb t hφ
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A₀ A := IsScalarTower.of_algebraMap_eq' hc.symm
  let φ := MvPolynomial.eval₂Hom ρ t
  letI : Algebra (MvPolynomial (Fin r) A₀) A := φ.toAlgebra
  haveI : IsScalarTower A₀ (MvPolynomial (Fin r) A₀) A :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change _ = φ (MvPolynomial.C a)
      simp [φ, RingHom.algebraMap_toAlgebra]
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) A₀) A := hφ
  haveI : Algebra.FormallySmooth A₀ A :=
    Algebra.FormallySmooth.comp A₀ (MvPolynomial (Fin r) A₀) A
  haveI : Subsingleton (Algebra.H1Cotangent A₀ A) :=
    Algebra.FormallySmooth.subsingleton_h1Cotangent
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange k A₀ A) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k A₀ A y).1 hy
    rw [Subsingleton.elim w 0, map_zero]
  let w : Module.Basis (Fin r) A (Ω[A⁄A₀]) :=
    (KaehlerDifferential.isBaseChange_of_formallyEtale A₀ (MvPolynomial (Fin r) A₀) A).basis
      (KaehlerDifferential.mvPolynomialBasis A₀ (Fin r))
  have hw : ∀ i, w i = KaehlerDifferential.D A₀ A (t i) := fun i ↦ by
    simp [w, IsBaseChange.basis_apply, KaehlerDifferential.mvPolynomialBasis_apply,
      KaehlerDifferential.map_D, RingHom.algebraMap_toAlgebra, φ]
  obtain ⟨B, hB⟩ := exists_basis_of_exact
    (KaehlerDifferential.mapBaseChange k A₀ A) (KaehlerDifferential.map k A₀ A A) hinj
    (KaehlerDifferential.exact_mapBaseChange_map k A₀ A)
    (b.baseChange A) w (fun i ↦ KaehlerDifferential.D k A (t i))
    (fun i ↦ by rw [hw, KaehlerDifferential.map_D]; rfl)
  let e : Fin (r + n) ≃ Fin n ⊕ Fin r := finSumFinEquiv.symm.trans (Equiv.sumComm _ _)
  refine isFreeGen_dForm _ (B.reindex e.symm) fun a ↦ ?_
  rw [Module.Basis.reindex_apply, Equiv.symm_symm, hB]
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) a
  · simp [e, Fin.append_left]
  · simp only [e, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumComm_apply,
      Sum.swap_inr, Sum.elim_inl, Module.Basis.baseChange_apply,
      KaehlerDifferential.mapBaseChange_tmul, one_smul, hb, dFun, KaehlerDifferential.map_D,
      Fin.append_right]
    rfl

end GlobalTheory.TopFrameEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackBaseChangeWithSquareStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGrpPullback_baseChange_with_square : ∀ {S S' T : Scheme.{0}} (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ t : T ⟶ S', IsGrpPullback ((Over.pullback t).obj G') G (t ≫ f) (pullback.fst G'.hom t ≫ φ) ∧ ∃ φ₂ : (G2 ((Over.pullback t).obj G')).left ⟶ (G2 G).left, IsSquare (pullback.fst G'.hom t ≫ φ) φ₂ := by
  first | exact @GlobalTheory.GrpPB.baseChange_square | exact GlobalTheory.GrpPB.baseChange_square | (intros; apply GlobalTheory.GrpPB.baseChange_square <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertEisensteinLatticeValueOfEisensteinSerieStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHilbertEisensteinLatticeValue_of_eisensteinSeries : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (G : (Emb F → ℂ) → ℂ) (w : Emb F → ℂ), Even k → IsEis 𝔞 𝔟 k G → w ∈ upperHalf F → IsGVal k (split 𝔞 𝔟 0) w 1 (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F) ^ k * G w) := by
  first | exact @GlobalTheory.HilbFam.EisCmp.isGVal_of_isEis | exact GlobalTheory.HilbFam.EisCmp.isGVal_of_isEis | (intros; apply GlobalTheory.HilbFam.EisCmp.isGVal_of_isEis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralDiscMulCoordsOfCmFieldIntegralStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_disc_mul_coords_of_cmField_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (θ : E) (D : ℕ) (x : Fin 2 → FR E), 0 < D → IsIntegral ℤ θ → (θ - IsCMField.complexConj E θ) ^ 2 = -(D : E) → IsIntegral ℤ ((x 0 : E) * θ + (x 1 : E)) → ∀ j, IsIntegral ℤ ((D : FR E) * x j ^ 2) ∧ IsIntegral ℤ ((D : FR E) * x j) := by
  first | exact @GlobalTheory.HilbFam.isIntegral_coord_of_isIntegral | exact GlobalTheory.HilbFam.isIntegral_coord_of_isIntegral | (intros; apply GlobalTheory.HilbFam.isIntegral_coord_of_isIntegral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralImageOfField
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem isIntegral_image_of_field {K : Type} [Field K] {S : Scheme.{0}} (g : Sp K ⟶ S) : IsIntegral g.image := by
  have : QuasiCompact g := inferInstance
  have := GlobalTheory.isSchemeTheoreticallyDominant_toImage g
  have : IsReduced g.image := IsSchemeTheoreticallyDominant.isReduced g.toImage
  have hi : IsIrreducible (Set.range g.toImage) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ g.toImage.continuous.continuousOn
  have hc := hi.closure
  rw [g.toImage.denseRange.closure_range] at hc
  have : IrreducibleSpace g.image := { isPreirreducible_univ := hc.2, toNonempty := ⟨hc.1.some⟩ }
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem lbIso_factor {X Y Z : Scheme.{0}} {L : LB X} {L' : LB Y} {M : LB Z} (hL : L.IsLB) (hL' : L'.IsLB) (hM : M.IsLB)
    {F : Y ⟶ X} {a' : Z ⟶ Y} {a : Z ⟶ X} (e : a' ≫ F = a) (h' : LBIso L' (L.pull F)) (h : LBIso M (L.pull a)) :
    LBIso M (L'.pull a') :=
  LBIso.trans hM (pull_isLB hL _) (pull_isLB hL' _) h
    (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L' a' a' rfl) (chartPullSame L (fun _ => a) (fun _ => F) _ a' fun _ => e.symm) h').symm

theorem exists_grpPullback_factor {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {G'' : Over S''} [GrpObj G'']
    (f : S' ⟶ S) (g : S'' ⟶ S') {F : G''.left ⟶ G.left} (h : IsGrpPullback G'' G (g ≫ f) F) :
    ∃ F' : G''.left ⟶ ((Over.pullback f).obj G).left, F' ≫ pullback.fst G.hom f = F ∧
      IsGrpPullback G'' ((Over.pullback f).obj G) g F' := by
  have hF : pullback.lift F (G''.hom ≫ g) (by rw [h.1.w, Category.assoc]) ≫ pullback.fst G.hom f = F :=
    pullback.lift_fst _ _ _
  exact ⟨_, hF, (isGrpPullback_pullback G f).cancel (h.congr rfl hF.symm) (pullback.lift_snd _ _ _)⟩

theorem PreCover.nonempty_labCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (D : DegData R (maximalIdeal R)), PreCover D → Nonempty (LabCover D) := by
  intro R _ _ _ D C
  have := C.proper
  have : QuasiCompact C.gp := inferInstance
  obtain ⟨P', w, hP⟩ := GlobalTheory.UU.exists_pull C.P (GlobalTheory.UU.toBase_mul_pullback C.G C.gp.imageι)
  obtain ⟨α', hα, hα'⟩ := exists_grpPullback_factor C.gp.imageι C.gp.toImage
    (C.α_cart.congr C.gp.toImage_imageι.symm rfl)
  refine ⟨{ S := C.gp.image
            π := C.gp.imageι ≫ C.π
            proper := inferInstance
            integral := isIntegral_image_of_field C.gp
            gp := C.gp.toImage
            gp_π := by rw [C.gp.toImage_imageι_assoc, C.gp_π]
            dominant := inferInstance
            G := (Over.pullback C.gp.imageι).obj C.G
            semi := IsSemiAbelian.pullback _ _ C.semi
            P := P'
            A := C.A
            α := α'
            α_cart := hα'
            α_lb := lbIso_factor C.P.L.isLB P'.L.isLB C.A.isLB hα ⟨w, hP.gen⟩ C.α_lb
            n := C.n
            n_prime := C.n_prime
            n_odd := C.n_odd
            n_unit := C.n_unit
            lab := C.lab
            trait := ?_ }⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', i₁, i₂, i₃, io, G', j₁, j₂, β, D', A', U', hD, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    C.trait W hW φ (ξ ≫ C.gp.imageι) hφ hloc (by rw [Category.assoc, hξ])
  obtain ⟨β', hβ, hβ'⟩ := exists_grpPullback_factor C.gp.imageι (spMap io ≫ ξ)
    (h₄.congr (Category.assoc _ _ _).symm rfl)
  refine ⟨W', i₁, i₂, i₃, io, G', j₁, j₂, β', D', A', U', hD, h₁, h₂, h₃, hβ',
    lbIso_factor C.P.L.isLB P'.L.isLB U'.LG.isLB hβ ⟨w, hP.gen⟩ h₅, ?_⟩
  intro F _ _ _ _ em hF j p p₁ p' x' a b c d
  refine h₆ F em hF j p p₁ p' x' a b c ?_
  have := congrArg (· ≫ pullback.fst C.G.hom C.gp.imageι) d
  simp only [Category.assoc] at this
  rw [← hα, ← hβ]
  exact this

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralPullbackRationalSaturationModelOpen
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.UPoinc GlobalTheory.ZH

namespace GlobalTheory.UPoinc

theorem isReduced_of_flat_isPreimmersion {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] [IsPreimmersion f] [IsReduced Y] :
    IsReduced X := by
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have hfl := Flat.stalkMap f x
    have hs := f.stalkMap_surjective x
    letI := (f.stalkMap x).hom.toAlgebra
    haveI : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := hfl
    haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)
    have hi : Function.Injective (f.stalkMap x).hom :=
      FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
    exact isReduced_of_injective (RingEquiv.ofBijective _ ⟨hi, hs⟩).symm (RingEquiv.injective _)
  exact isReduced_of_isReduced_stalk X

theorem isIntegral_pullback_toRat : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [CharZero Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (R : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp R), (U₀ : Set M.Z).Nonempty → (∀ x : Sp Ω ⟶ U₀.toScheme, x ≫ U₀.ι = M.pt → x ≫ u₀ = spMap R.val.toRingHom) → IsIntegral (pullback u₀ (spMap (toRat R))) ∧ ∃ pt : Sp Ω ⟶ pullback u₀ (spMap (toRat R)), pt ≫ pullback.fst _ _ ≫ U₀.ι = M.pt ∧ Dense (Set.range pt) := by
  intro o Ω _ _ _ _ M U₀ R u₀ hne hgen
  haveI := M.integral
  letI := (toRat R).toAlgebra
  haveI := isLocalization_ratHull R
  haveI : IsPreimmersion (spMap (toRat R)) :=
    IsPreimmersion.of_isLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ))
  haveI : Flat (spMap (toRat R)) := (HasRingHomProperty.Spec_iff (P := @Flat)).2
    (IsLocalization.flat (ratHull R) (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ)))
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hne (show w ∈ (⊤ : (Sp Ω).Opens) from trivial)
  have hx := IsOpenImmersion.lift_fac U₀.ι M.pt hr
  have w : IsOpenImmersion.lift U₀.ι M.pt hr ≫ u₀ = spMap (ratHull R).val.toRingHom ≫ spMap (toRat R) :=
    (hgen _ hx).trans (spMap_val_toRat R).symm
  let pt := pullback.lift _ _ w
  let j : pullback u₀ (spMap (toRat R)) ⟶ M.Z := pullback.fst _ _ ≫ U₀.ι
  have hpt : pt ≫ j = M.pt := by rw [← Category.assoc, pullback.lift_fst, hx]
  haveI : IsPreimmersion j := inferInstance
  haveI : Flat j := inferInstance
  haveI := isReduced_of_flat_isPreimmersion j
  have hj : ∀ y, j (pt y) = genericPoint M.Z := fun y => by
    rw [← Scheme.Hom.comp_apply, hpt]
    exact M.gen.le ⟨y, rfl⟩
  have hg : IsGenericPoint (pt default) Set.univ := by
    refine isGenericPoint_iff_specializes.2 fun z => ⟨fun _ => trivial, fun _ => ?_⟩
    rw [← j.isEmbedding.isInducing.specializes_iff, hj]
    exact genericPoint_specializes _
  haveI : IrreducibleSpace (pullback u₀ (spMap (toRat R)) :) :=
    (irreducibleSpace_def _).2 hg.isIrreducible
  refine ⟨isIntegral_of_irreducibleSpace_of_isReduced _, pt, hpt, ?_⟩
  exact Dense.mono (Set.singleton_subset_iff.2 ⟨default, rfl⟩) (dense_iff_closure_eq.2 hg)

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfEtaleOfSurjectiveOfUniversallyInjectiveAl
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isIso_of_etale_of_surjective_of_universallyInjective :
    ∀ (X Z : Scheme.{0}) (h : X ⟶ Z), Etale h → Surjective h → UniversallyInjective h → IsIso h := by
  intro X Z h het hs hui
  have hd : Surjective (pullback.diagonal h) := (UniversallyInjective.iff_diagonal h).1 hui
  have : IsIso (pullback.diagonal h) :=
    (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hd⟩
  have : Mono h := (pullback.isIso_diagonal_iff h).1 this
  have : IsOpenImmersion h := IsOpenImmersion.of_flat_of_mono h
  exact (isIso_iff_isOpenImmersion_and_surjective h).2 ⟨this, hs⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomRescaledRealisationSameGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMonHom_rescaled_realisation_same_genericFibre : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) → ∀ E, IsMonHom (ε' E) := by
  first | exact @GlobalTheory.Poinc.isMonHom_of_same_rechart | exact GlobalTheory.Poinc.isMonHom_of_same_rechart | (intros; apply GlobalTheory.Poinc.isMonHom_of_same_rechart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauFirstCoordsOfUnitLastCoords
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem isMonomialTau_inl_of_tauIn : ∀ (V : Type) [CommRing V] [IsDomain V] (Q : Data V) (τ₀ : GlobalTheory.Poinc.Sep.Gens Q) (m N : ℕ) (s : Fin m ⊕ Fin N → V) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X), (∀ k, IsUnit (s (.inr k))) → GlobalTheory.Poinc.Sep.TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → Q.IsMonomialTau (fun k => s (.inl k)) (fun k => ε (.inl k)) := by
  intro V _ _ Q τ₀ m N s ε hs h a b
  obtain ⟨k, hk, hc⟩ := Model.isMonomialTau_of_tauIn h a b
  let alg : V →* FractionRing V := (algebraMap V (FractionRing V) : V →* FractionRing V)
  let w : Vˣ := ∏ j : Fin N, (hs j).unit ^ ε (.inr j) a b
  refine ⟨k * Units.map alg w⁻¹, ?_, GlobalTheory.PolDeg.Taut.tauCoord_mul_unit hc w⁻¹⟩
  have hprod : (k : FractionRing V) = (∏ i : Fin m, algebraMap V (FractionRing V) (s (.inl i)) ^ ε (.inl i) a b) *
      ∏ j : Fin N, algebraMap V (FractionRing V) (s (.inr j)) ^ ε (.inr j) a b := by
    rw [hk, ← Fintype.prod_sum_type (fun x => algebraMap V (FractionRing V) (s x) ^ ε x a b)]
    exact Fintype.prod_equiv finSumFinEquiv.symm _ _ (fun _ => rfl)
  have hw : ((Units.map alg w : (FractionRing V)ˣ) : FractionRing V) =
      ∏ j : Fin N, algebraMap V (FractionRing V) (s (.inr j)) ^ ε (.inr j) a b := by
    simp [w, alg, Units.coe_prod, map_zpow₀]
  rw [Units.val_mul, map_inv, Units.val_inv_eq_inv_val, hw, hprod, mul_inv_cancel_right₀]
  exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _
    ((IsFractionRing.injective V (FractionRing V)).ne_iff' (map_zero _) |>.2 (hs j).ne_zero)

end GlobalTheory.Poinc.Sep
end
end

