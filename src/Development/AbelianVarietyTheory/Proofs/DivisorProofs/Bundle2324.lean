import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2271
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2270
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2272
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelRefinementGenerating
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteLocalDomainLiftCyclotomicAwayStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeLocalDomain_lift_cyclotomicAway : ∀ (n : ℕ), 3 ≤ n → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : cycAway n →+* K), ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (_ : IsNoetherianRing V) (βV : cycAway n →+* V) (π : V →+* K), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ Function.Injective βV ∧ Function.Surjective π ∧ π.comp βV = β := by
  first | exact @GlobalTheory.SiegelTor.CycLift.exists_complete_domain_lift | exact GlobalTheory.SiegelTor.CycLift.exists_complete_domain_lift | (intros; apply GlobalTheory.SiegelTor.CycLift.exists_complete_domain_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentStalkDerivationOfFunctionFieldExt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.LogKSDiv.LocalExt

theorem exists_restrict_der {k A K R : Type} [CommRing k] [CommRing A] [CommRing K] [CommRing R]
    [Algebra k A] [Algebra k K] (φ : A →+* K) (hφ : Function.Injective φ)
    (hk : ∀ c : k, φ (algebraMap k A c) = algebraMap k K c)
    (h : R →+* A) (hfr : ∀ a : A, ∃ r s : R, IsUnit (h s) ∧ a * h s = h r)
    (d : Derivation ℤ R R) (D : Derivation k K K)
    (hD : ∀ r, D (φ (h r)) = φ (h (d r))) :
    ∃ δ : Derivation k A A, (∀ a, D (φ a) = φ (δ a)) ∧ ∀ r, δ (h r) = h (d r) := by
  have hmem : ∀ a, ∃ b, φ b = D (φ a) := by
    intro a
    obtain ⟨r, s, ⟨u, hu⟩, hrs⟩ := hfr a
    refine ⟨(h (d r) - a * h (d s)) * ((u⁻¹ : Aˣ) : A), ?_⟩
    have e1 : D (φ a * φ (h s)) = φ (h (d r)) := by rw [← map_mul, hrs, hD]
    rw [Derivation.leibniz, hD, smul_eq_mul, smul_eq_mul] at e1
    have hinv : φ (h s) * φ ((u⁻¹ : Aˣ) : A) = 1 := by rw [← map_mul, ← hu, Units.mul_inv, map_one]
    rw [map_mul, map_sub, map_mul, ← e1]
    linear_combination (D (φ a)) * hinv
  choose δ0 hδ0 using hmem
  let δ : Derivation k A A :=
    { toFun := δ0
      map_add' := fun a b => hφ (by simp only [hδ0, map_add])
      map_smul' := fun c a => hφ (by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul, hk, hδ0]
        rw [← Algebra.smul_def, D.map_smul, Algebra.smul_def])
      map_one_eq_zero' := hφ (by show φ (δ0 1) = φ 0; rw [hδ0, map_one, Derivation.map_one_eq_zero, map_zero])
      leibniz' := fun a b => hφ (by
        show φ (δ0 (a * b)) = φ (a • δ0 b + b • δ0 a)
        simp only [hδ0, map_mul, map_add, smul_eq_mul, Derivation.leibniz]) }
  refine ⟨δ, fun a => (hδ0 a).symm, fun r => hφ ?_⟩
  show φ (δ0 (h r)) = _
  rw [hδ0, hD]

end GlobalTheory.LogKSDiv.LocalExt

namespace GlobalTheory.LogKSDiv.LocalExt

theorem exists_frac_germ {X : Scheme.{0}} (B : X.Opens) (y : B.toScheme) (U : X.affineOpens) (hy : B.ι y ∈ U.1)
    (a : B.toScheme.presheaf.stalk y) :
    ∃ r s : Γ(X, U.1), IsUnit ((B.ι.stalkMap y).hom (X.presheaf.germ U.1 (B.ι y) hy s)) ∧
      a * (B.ι.stalkMap y).hom (X.presheaf.germ U.1 (B.ι y) hy s) =
        (B.ι.stalkMap y).hom (X.presheaf.germ U.1 (B.ι y) hy r) := by
  letI := X.presheaf.algebra_section_stalk (⟨B.ι y, hy⟩ : U.1)
  haveI := U.2.isLocalization_stalk ⟨B.ι y, hy⟩
  let e := asIso (B.ι.stalkMap y)
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (U.2.primeIdealOf ⟨B.ι y, hy⟩).asIdeal.primeCompl (e.inv.hom a)
  refine ⟨r, s, (IsLocalization.map_units (X.presheaf.stalk (B.ι y)) s).map (B.ι.stalkMap y).hom, ?_⟩
  have h2 := congrArg (B.ι.stalkMap y).hom hrs
  rw [map_mul] at h2
  have h3 : (B.ι.stalkMap y).hom (e.inv.hom a) = a := by
    change (e.inv ≫ e.hom).hom a = a
    rw [Iso.inv_hom_id]
    rfl
  rw [h3] at h2
  exact h2

end GlobalTheory.LogKSDiv.LocalExt

namespace GlobalTheory.LogKSDiv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem stalkHom_eq_stalkMap (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) (r : Γ(TF.Y.X, U.1)) :
    stalkHom TF Z x U hx r = ((barComp TF.Y Z).ι.stalkMap x).hom (TF.Y.X.presheaf.germ U.1 _ hx r) :=
  (Scheme.Hom.germ_stalkMap_apply _ _ _ _ _).symm

theorem stalkHom_frac (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) (a : (X₀ TF.Y Z).presheaf.stalk x) :
    ∃ r s : Γ(TF.Y.X, U.1), IsUnit (stalkHom TF Z x U hx s) ∧ a * stalkHom TF Z x U hx s = stalkHom TF Z x U hx r := by
  obtain ⟨r, s, hu, e⟩ := LocalExt.exists_frac_germ (barComp TF.Y Z) x U hx a
  exact ⟨r, s, by rw [stalkHom_eq_stalkMap]; exact hu, by rw [stalkHom_eq_stalkMap, stalkHom_eq_stalkMap]; exact e⟩

end GlobalTheory.LogKSDiv

theorem GlobalTheory.LogKSDiv.exists_stalkDer_extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), (∀ r, ρ r = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r)) → ∀ (d : Fin Dw.dim → Derivation ℤ Γ(TF.Y.X, U.1) Γ(TF.Y.X, U.1)) (D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ (d j r)) → letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∃ δ : Fin Dw.dim → Derivation c.F ((X₀ TF.Y Z).presheaf.stalk x) ((X₀ TF.Y Z).presheaf.stalk x), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j a, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField a) = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (δ j a)) ∧ ∀ j r, δ j (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) = GlobalTheory.LogKSDiv.stalkHom TF Z x U hx (d j r) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U _ hx ρ hρ d D hD
  letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra
  have key := fun j => GlobalTheory.LogKSDiv.LocalExt.exists_restrict_der (k := c.F)
    (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)
    (IsFractionRing.injective _ _)
    (fun c => RingHom.congr_fun (GlobalTheory.LogKSDiv.algebraMap_comp_stalkAlg TF Z x) c)
    (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx) (GlobalTheory.LogKSDiv.stalkHom_frac TF Z x U hx) (d j) (D j)
    (fun r => by rw [← hρ, ← hρ]; exact hD j r)
  choose δ h1 h2 using key
  exact ⟨δ, h1, h2⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantComponentFunctionComplexValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.OneValue

theorem isAlgebraic_of_one_value {F A C : Type} [Field F] [CommRing A] [Nontrivial A] [IsReduced A] [Algebra F A]
    [Algebra.FiniteType F A] [Field C] [IsAlgClosed C] [Algebra F C] (s : A)
    (h : ∀ φ ψ : A →ₐ[F] C, φ s = ψ s) : IsAlgebraic F s := by
  have hJ : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := F)
  have key : ∀ m : Ideal A, m.IsMaximal →
      ∃ φ : A →ₐ[F] C, (∀ a, φ a = 0 → a ∈ m) ∧ IsAlgebraic F (φ s) := by
    intro m hm
    letI := Ideal.Quotient.field m
    have : Module.Finite F (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ m)
    let σ : (A ⧸ m) →ₐ[F] C := IsAlgClosed.lift
    refine ⟨σ.comp (Ideal.Quotient.mkₐ F m), fun a ha => ?_, ?_⟩
    · exact Ideal.Quotient.eq_zero_iff_mem.1 (σ.toRingHom.injective (ha.trans (map_zero σ.toRingHom).symm))
    · exact (Algebra.IsAlgebraic.isAlgebraic (R := F) (Ideal.Quotient.mkₐ F m s)).algHom σ
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal A
  obtain ⟨φ₀, -, P, hP, hPs⟩ := key m₀ hm₀
  refine ⟨P, hP, ?_⟩
  have hj : Polynomial.aeval s P ∈ (⊥ : Ideal A).jacobson := by
    refine Ideal.mem_sInf.2 ?_
    rintro m ⟨-, hm⟩
    obtain ⟨φ, hφ, -⟩ := key m hm
    refine hφ _ ?_
    rw [← Polynomial.aeval_algHom_apply, h φ φ₀, hPs]
  rwa [hJ.out (Ideal.isRadical_bot_iff.2 inferInstance), Ideal.mem_bot] at hj

theorem valR_spMap_fromSpec {X : Scheme.{0}} {R : Type} [CommRing R] {U W : X.Opens} (hW : IsAffineOpen W)
    (e : W ≤ U) (φ : Γ(X, W) →+* R) (f : Γ(X, U)) :
    valR (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec : Sp R ⟶ X) U f = φ (resG X e f) := by
  have h0 : ⊤ ≤ hW.fromSpec ⁻¹ᵁ W := hW.fromSpec_preimage_self.ge
  have h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec : Sp R ⟶ X) ⁻¹ᵁ U :=
    fun y _ => e (h0 (Set.mem_univ ((Spec.map (CommRingCat.ofHom φ)) y)))
  unfold valR
  rw [dif_pos h]
  have e1 : (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec : Sp R ⟶ X).appLE U ⊤ h =
      X.presheaf.map (homOfLE e).op ≫ hW.fromSpec.appLE W ⊤ h0 ≫ (Spec.map (CommRingCat.ofHom φ)).appTop := by
    rw [← Category.assoc, Scheme.Hom.map_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ _ le_rfl).symm
  have e2 : hW.fromSpec.appLE W ⊤ h0 = (Scheme.ΓSpecIso Γ(X, W)).inv := by
    rw [Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg (_ ≫ ·) ((Spec Γ(X, W)).presheaf.map_id _)).trans (Category.comp_id _)
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  change ((Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec : Sp R ⟶ X).appLE U ⊤ h ≫
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom f =
    (X.presheaf.map (homOfLE e).op ≫ CommRingCat.ofHom φ).hom f
  rw [e1, e2, Category.assoc, Category.assoc]
  erw [n]
  erw [(Scheme.ΓSpecIso Γ(X, W)).inv_hom_id_assoc]

theorem exists_eq_algX {F : Type} [Field F] {Y : Scheme.{0}} (p : Y ⟶ Sp F) [GeometricallyIntegral p]
    [LocallyOfFiniteType p] (e : F →+* ℂ) (f : Γ(Y, ⊤))
    (h : ∀ y y' : Sp ℂ ⟶ Y, y ≫ p = spMap e → y' ≫ p = spMap e → valR y ⊤ f = valR y' ⊤ f) :
    ∃ a : F, f = algX p ⊤ a := by
  have : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton p
  obtain ⟨U, hU, hxU, hUV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (show genericPoint Y ∈ (⊤ : Y.Opens) from trivial)
  replace hU : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have hc : (algX p U).FiniteType := by
    have h1 : (p.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2)
  letI : Algebra F Γ(Y, U) := (algX p U).toAlgebra
  have : Algebra.FiniteType F Γ(Y, U) := hc
  letI : Algebra F ℂ := e.toAlgebra
  have hg : hU.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F Γ(Y, U))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)
    rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have hpt : ∀ φ : Γ(Y, U) →ₐ[F] ℂ,
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hU.fromSpec : Sp ℂ ⟶ Y) ≫ p = spMap e := by
    intro φ
    rw [Category.assoc, hg, ← Spec.map_comp]
    congr 1
    ext a
    exact φ.commutes a
  obtain ⟨P, hP, hPs⟩ := isAlgebraic_of_one_value (F := F) (C := ℂ) (resG Y hUV f) fun φ ψ => by
    have := h _ _ (hpt φ) (hpt ψ)
    rwa [valR_spMap_fromSpec hU hUV, valR_spMap_fromSpec hU hUV] at this
  obtain ⟨a, ha⟩ := GlobalTheory.GeomIntConst.mem_range_constFn F Y p (GlobalTheory.Cartier.fnOf ⊤ trivial f) ⟨P, hP, by
    rw [← GlobalTheory.Cartier.fnOf_comp_algX p U hxU, ← GlobalTheory.Cartier.fnOf_resG hUV hxU, ← Polynomial.hom_eval₂]
    exact (congrArg _ hPs).trans (map_zero _)⟩
  exact ⟨a, (GlobalTheory.Cartier.fnOf_injective ⊤ trivial ha).symm⟩

theorem exists_eq_constFn_of_one_value :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens) (e : c.F →+* ℂ) (f : Γ(Xo.XF c, U)), GeometricallyConnected (U.ι ≫ toF Xo c) → (∀ y y' : Sp ℂ ⟶ Xo.XF c, y ≫ toF Xo c = spMap e → y' ≫ toF Xo c = spMap e → Set.range y ⊆ U → Set.range y' ⊆ U → valR y U f = valR y' U f) → ∃ a : c.F, f = ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn (toF Xo c) U a := by
  intro E _ _ _ H D l Xo c U e f hU h
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  have : Smooth (toF Xo c) := inferInstanceAs (Smooth (pullback.snd _ _))
  have : GeometricallyIntegral (U.ι ≫ toF Xo c) := GlobalTheory.geometricallyIntegral_of_smooth _
  have hle : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := fun x _ => x.2
  have hval : ∀ y : Sp ℂ ⟶ U.toScheme, valR y ⊤ ((U.ι.appLE U ⊤ hle).hom f) = valR (y ≫ U.ι) U f := by
    intro y
    have h1 : ⊤ ≤ y ⁻¹ᵁ ⊤ := le_top
    have h2 : ⊤ ≤ (y ≫ U.ι) ⁻¹ᵁ U := fun x _ => (y x).2
    unfold valR
    rw [dif_pos h1, dif_pos h2, ← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ hle h1]
    rfl
  have hr : ∀ y : Sp ℂ ⟶ U.toScheme, Set.range (y ≫ U.ι) ⊆ U := by
    rintro y _ ⟨x, rfl⟩
    exact (y x).2
  obtain ⟨a, ha⟩ := exists_eq_algX (U.ι ≫ toF Xo c) e ((U.ι.appLE U ⊤ hle).hom f) fun y y' hy hy' => by
    rw [hval, hval]
    exact h _ _ ((Category.assoc _ _ _).trans hy) ((Category.assoc _ _ _).trans hy') (hr y) (hr y')
  refine ⟨a, ?_⟩
  have hiso : IsIso (U.ι.appLE U ⊤ hle) := by
    rw [Scheme.Opens.ι_appLE]
    have : U.ι ''ᵁ ⊤ = U := U.ι_image_top
    have : IsIso (homOfLE (x := U.ι ''ᵁ ⊤) (y := U) this.le) := ⟨homOfLE this.ge, rfl, rfl⟩
    exact Functor.map_isIso _ (homOfLE (x := U.ι ''ᵁ ⊤) (y := U) U.ι_image_top.le).op
  refine (ConcreteCategory.bijective_of_isIso (U.ι.appLE U ⊤ hle)).1 (ha.trans ?_)
  have := Scheme.Hom.appLE_comp_appLE U.ι (toF Xo c) ⊤ U ⊤ (fun _ _ => trivial) hle
  exact (congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom a)) this).symm

end GlobalTheory.OneValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantFunctionNormalCompactification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.CptConst

theorem exists_eq_algX {F : Type} [Field F] {X Z : Scheme.{0}} (p : X ⟶ Sp F) [IsIntegral X] [UniversallyClosed p]
    (g : Z ⟶ X) [GeometricallyIntegral (g ≫ p)] (f : Γ(X, ⊤)) : ∃ a : F, f = algX p ⊤ a := by
  have : IsIntegral Z := GeometricallyIntegral.isIntegral_of_subsingleton (g ≫ p)
  have hal : ∀ {W : Scheme.{0}} (q : W ⟶ Sp F),
      algX q ⊤ = ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ q.appTop).hom := by
    intro W q
    have : q.appLE ⊤ ⊤ le_top = q.appTop := q.appLE_eq_app
    rw [← this]
    rfl
  have hint : (algX p ⊤).IsIntegral := by
    rw [hal]
    let G := (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop
    have : G.hom.IsIntegral := by
      apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
      exact isIntegral_appTop_of_universallyClosed p
    exact this
  have hcomp : g.appTop.hom.comp (algX p ⊤) = algX (g ≫ p) ⊤ := by
    rw [hal, hal, Scheme.Hom.comp_appTop]
    rfl
  letI := (isField_of_universallyClosed F p).toField
  let φ : Γ(X, ⊤) →+* Z.functionField := (GlobalTheory.Cartier.fnOf ⊤ trivial).comp g.appTop.hom
  have hφ : φ.comp (algX p ⊤) = GlobalTheory.Cartier.constFn (g ≫ p) := by
    rw [RingHom.comp_assoc, hcomp]
    rfl
  obtain ⟨P, hP, hPf⟩ := hint f
  obtain ⟨a, ha⟩ := GlobalTheory.GeomIntConst.mem_range_constFn F Z (g ≫ p) (φ f) ⟨P, hP.ne_zero, by
    rw [← hφ, ← Polynomial.hom_eval₂, hPf, map_zero]⟩
  refine ⟨a, φ.injective ?_⟩
  rw [← ha, ← hφ]
  rfl

theorem exists_eq_constFn_compactOf :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (V : (gen Y).Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → (V : Set (gen Y)) = compactOf Y U → ∀ f : Γ(gen Y, V), ∃ a : c.F, f = ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn (genStr Y) V a := by
  intro E _ _ _ H D l Xo c O _ β Y U V hn _ hU hV f
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  have : Smooth (toF Xo c) := inferInstanceAs (Smooth (pullback.snd _ _))
  have hgi : GeometricallyIntegral (U.ι ≫ toF Xo c) := GlobalTheory.geometricallyIntegral_of_smooth _
  have : IsIntegral U.toScheme := GeometricallyIntegral.isIntegral_of_subsingleton (U.ι ≫ toF Xo c)
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsReduced (gen Y) := GlobalTheory.IsNormalScheme.isReduced
  have := isProper_genStr Y
  have hUirr : IsIrreducible (U : Set (Xo.XF c)) :=
    isIrreducible_iff_irreducibleSpace.2 (inferInstanceAs (IrreducibleSpace U.toScheme))
  have hirr : IsIrreducible (V : Set (gen Y)) :=
    hV ▸ (hUirr.image _ Y.jQ.continuous.continuousOn).closure
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace hirr
  have : IsIntegral V.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι, hV]
    exact isClosed_closure)
  have hr : Set.range (U.ι ≫ Y.jQ) ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, hV]
    exact subset_closure ⟨x.1, x.2, rfl⟩
  let g : U.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι (U.ι ≫ Y.jQ) hr
  have hg : g ≫ V.ι ≫ genStr Y = U.ι ≫ toF Xo c := by
    rw [IsOpenImmersion.lift_fac_assoc, Category.assoc]
    exact congrArg (U.ι ≫ ·) Y.jQ_over
  have : GeometricallyIntegral (g ≫ V.ι ≫ genStr Y) := hg ▸ hgi
  have hle : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := fun x _ => x.2
  obtain ⟨a, ha⟩ := exists_eq_algX (V.ι ≫ genStr Y) g ((V.ι.appLE V ⊤ hle).hom f)
  refine ⟨a, ?_⟩
  have hiso : IsIso (V.ι.appLE V ⊤ hle) := by
    rw [Scheme.Opens.ι_appLE]
    have : V.ι ''ᵁ ⊤ = V := V.ι_image_top
    have : IsIso (homOfLE (x := V.ι ''ᵁ ⊤) (y := V) this.le) := ⟨homOfLE this.ge, rfl, rfl⟩
    exact Functor.map_isIso _ (homOfLE (x := V.ι ''ᵁ ⊤) (y := V) V.ι_image_top.le).op
  refine (ConcreteCategory.bijective_of_isIso (V.ι.appLE V ⊤ hle)).1 (ha.trans ?_)
  have := Scheme.Hom.appLE_comp_appLE V.ι (genStr Y) ⊤ V ⊤ (fun _ _ => trivial) hle
  exact (congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom a)) this).symm

end GlobalTheory.CptConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelicStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_realComponentHom_unitaryAdelic : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V), V.SigOK → IsInfFam θ → IsFrames V A → ∃ rp : GA D V →* (∀ ρ, Upq V ρ), Continuous rp ∧ IsRealPart V θ A rp := by
  first | exact @GlobalTheory.CovTop.VolUp.exists_realPart_hom | exact GlobalTheory.CovTop.VolUp.exists_realPart_hom | (intros; apply GlobalTheory.CovTop.VolUp.exists_realPart_hom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesExtendingRegularParameters
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

open scoped TensorProduct

namespace GlobalTheory.CoordExt

theorem formallySmooth_of_charZero (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] :
    Algebra.FormallySmooth F K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  haveI := hs.isAlgebraic_field
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : CharZero (IntermediateField.adjoin F (Set.range ((↑) : s → K))) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : Algebra.IsSeparable (IntermediateField.adjoin F (Set.range ((↑) : s → K))) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

theorem span_D_algebraMap_eq_top (F A R : Type) [Field F] [CommRing A] [CommRing R]
    [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] (P : Ideal A) [P.IsPrime]
    [IsLocalization.AtPrime R P] :
    Submodule.span R (Set.range fun y : A => KaehlerDifferential.D F R (algebraMap A R y)) = ⊤ := by
  set S := Submodule.span R (Set.range fun y : A => KaehlerDifferential.D F R (algebraMap A R y))
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl r
  have hu : IsUnit (algebraMap A R s) := IsLocalization.map_units R s
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have key : algebraMap A R s • KaehlerDifferential.D F R (IsLocalization.mk' R y s) =
      KaehlerDifferential.D F R (algebraMap A R y) -
        IsLocalization.mk' R y s • KaehlerDifferential.D F R (algebraMap A R s) := by
    rw [eq_sub_iff_add_eq, add_comm, ← Derivation.leibniz, IsLocalization.mk'_spec]
  have hmem : algebraMap A R s • KaehlerDifferential.D F R (IsLocalization.mk' R y s) ∈ S := by
    rw [key]
    exact sub_mem (Submodule.subset_span ⟨y, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩))
  have : KaehlerDifferential.D F R (IsLocalization.mk' R y s) =
      v • (algebraMap A R s • KaehlerDifferential.D F R (IsLocalization.mk' R y s)) := by
    rw [smul_smul, hv, one_smul]
  change _ ∈ S
  rw [this]
  exact Submodule.smul_mem _ _ hmem

theorem span_tmul_eq_top {R M : Type} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {ι : Type} (f : ι → M) (hf : Submodule.span R (Set.range f) = ⊤) :
    Submodule.span (IsLocalRing.ResidueField R)
      (Set.range fun i => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f i) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.TensorUnitSpanTop.main
  | exact _root_.GlobalTheory.TensorUnitSpanTop.main
  | (apply _root_.GlobalTheory.TensorUnitSpanTop.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.TensorUnitSpanTop.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TensorUnitSpanTop.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TensorUnitSpanTop.main ..)

end GlobalTheory.CoordExt

open GlobalTheory.CoordExt in

theorem GlobalTheory.exists_coords_extending_regularParams : ∀ (F A R : Type) [Field F] [CharZero F] [CommRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (n : ℕ) [Module.Free R Ω[R⁄F]] [Module.Finite R Ω[R⁄F]], Module.finrank R Ω[R⁄F] = n → ∀ (m : ℕ) (a : Fin m → A), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m (fun i => algebraMap A R (a i)) → ∃ (x : Fin n → A) (e : Fin m ↪ Fin n), (∀ j, x (e j) = a j) ∧ ∃ bs : Module.Basis (Fin n) R Ω[R⁄F], ∀ i, bs i = KaehlerDifferential.D F R (algebraMap A R (x i)) := by
  classical
  intro F A R _ _ _ _ _ _ _ _ _ _ _ P _ _ n _ _ hn m a hrsp
  haveI : Algebra.FormallySmooth F (IsLocalRing.ResidueField R) := formallySmooth_of_charZero F _
  set r : Fin m → R := fun i => algebraMap A R (a i) with hr_def
  have hr : ∀ i, r i ∈ IsLocalRing.maximalIdeal R := fun i => hrsp.1 ▸ Ideal.subset_span ⟨i, rfl⟩

  have hcot : LinearIndependent (IsLocalRing.ResidueField R) (fun i =>
      ((IsLocalRing.maximalIdeal R).toCotangent ⟨r i, hr i⟩ : IsLocalRing.CotangentSpace R)) := by
    have hfr : Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = m := by
      have := (IsRegularLocalRing.iff_finrank_cotangentSpace R).1 inferInstance
      rw [← hrsp.2] at this
      exact_mod_cast this
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp [hfr])
    have hsp : Submodule.span R (Set.range fun i => (⟨r i, hr i⟩ : IsLocalRing.maximalIdeal R)) = ⊤ := by
      apply Submodule.map_injective_of_injective (IsLocalRing.maximalIdeal R).injective_subtype
      rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
      exact hrsp.1
    rw [← IsLocalRing.CotangentSpace.span_image_eq_top_iff] at hsp
    rw [← Set.range_comp] at hsp
    exact hsp.ge
  have hw := GlobalTheory.AdaptedFrame.linearIndependent_tmul_D (k := F) r hr hcot
  let φ : A → IsLocalRing.ResidueField R ⊗[R] Ω[R⁄F] :=
    fun y => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] KaehlerDifferential.D F R (algebraMap A R y)
  have hw' : LinearIndependent (IsLocalRing.ResidueField R) (φ ∘ a) := hw
  have ha : Function.Injective a := fun i j h => hw'.injective (by simp only [Function.comp_apply, h])
  have hli : LinearIndepOn (IsLocalRing.ResidueField R) φ (Set.range a) :=
    (linearIndepOn_range_iff ha φ).2 hw'
  obtain ⟨b, -, hab, hbsp, hbli⟩ := exists_linearIndepOn_extension hli (Set.subset_univ _)
  have hVsp : Submodule.span (IsLocalRing.ResidueField R) (Set.range φ) = ⊤ :=
    span_tmul_eq_top _ (span_D_algebraMap_eq_top F A R P)
  have hbtop : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField R) (Set.range fun y : b => φ y) := by
    rw [← Set.image_eq_range, ← hVsp, ← Set.image_univ]
    exact Submodule.span_le.2 hbsp
  let bV := Module.Basis.mk hbli hbtop
  haveI : Finite b := Module.Finite.finite_basis bV
  letI : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = n := by
    rw [← Module.finrank_eq_card_basis bV, Module.finrank_baseChange, hn]
  let σ := Fintype.equivFinOfCardEq hcard
  let e0 : Fin m ↪ b := ⟨fun j => ⟨a j, hab ⟨j, rfl⟩⟩, fun i j h => ha (congrArg Subtype.val h)⟩
  refine ⟨fun i => ((σ.symm i : b) : A), e0.trans σ.toEmbedding, fun j => by
    simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
    rfl, ?_⟩
  let ω : Fin n → Ω[R⁄F] := fun i => KaehlerDifferential.D F R (algebraMap A R (σ.symm i : b))
  have hb' : ∀ i, (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] ω i = bV.reindex σ i := by
    intro i
    rw [Module.Basis.reindex_apply]
    exact (Module.Basis.mk_apply hbli hbtop _).symm
  have hspan := IsLocalRing.span_eq_top_of_tmul_eq_basis ω (bV.reindex σ) hb'
  have hli2 : LinearIndependent R ω :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (by simp [hn])
  exact ⟨Module.Basis.mk hli2 hspan.ge, fun i => by rw [Module.Basis.mk_apply]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCountableCosetRepresentativesStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_countable_coset_representatives : ∀ (D : D7) (V : HSp D) (Λ : Set (Fin V.rank → D.host.E)) (K₀ : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))), IsOpen {h : GA D V | finE V h ∈ K₀} → (∀ h : GA D V, IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) Λ 1 ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → finE V h ∈ K₀) → ∃ (J : Type) (_ : Countable J) (g : J → GA D V), (∀ j, g j ∈ GfC V) ∧ (∀ i j, UEquiv (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) Λ 3 ((finHom V (g i)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) ((finHom V (g j)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → i = j) ∧ ∀ h : GA D V, ∃ j, ∃ γ ∈ GQ V, finE V ((g j)⁻¹ * γ * h) ∈ K₀ := by
  first | exact @GlobalTheory.CovTop.VolUp.Reps.exists_reps | exact GlobalTheory.CovTop.VolUp.Reps.exists_reps | (intros; apply GlobalTheory.CovTop.VolUp.Reps.exists_reps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorIdealSheafPrincipalisingFamilyStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominatorIdealSheaf_principalising_family : ∀ (Y : Scheme.{0}) [IsIntegral Y] (N : ℕ) (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)) (U : Y.Opens),
    w i₀ = 1 → (∀ y ∈ U, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) →
    ∃ I : Y.IdealSheafData, I ≠ ⊥ ∧ (∀ y ∈ U, y ∉ I.support) ∧
      ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (s : Y' ⟶ Y) (hη : s (genericPoint Y') = genericPoint Y),
        ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (I.comap s) → ∀ y' : Y', ∃ k,
          GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k) ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y'
            (GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k)) := by
  first | exact @GlobalTheory.DenomIdeal.exists_idealSheaf | exact GlobalTheory.DenomIdeal.exists_idealSheaf | (intros; apply GlobalTheory.DenomIdeal.exists_idealSheaf <;> assumption)
end

