import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import GroundTheory.AutomorphicForms.Anisotropic
import GroundTheory.AutomorphicForms.HermitianNormLocal

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalPrimeExists
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE

namespace KrullPts

theorem exists_specialization_over {W S : Type*} [TopologicalSpace W] [TopologicalSpace S]
    {q : W → S} (hq : IsClosedMap q) {y₀ : W} {m : S} (h : q y₀ ⤳ m) :
    ∃ y₁, y₀ ⤳ y₁ ∧ q y₁ = m := by
  have hcl : IsClosed (q '' closure {y₀}) := hq _ isClosed_closure
  have hmem : q y₀ ∈ q '' closure {y₀} := ⟨y₀, subset_closure rfl, rfl⟩
  obtain ⟨y₁, hy₁, rfl⟩ := h.mem_closed hcl hmem
  exact ⟨y₁, specializes_iff_mem_closure.mpr hy₁, rfl⟩

theorem exists_chart_map {X Z W : Scheme.{0}} (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V)
    {R : Type} [CommRing R] [Algebra Γ(X, V) R] (a : W ⟶ Z) (q : W ⟶ Spec (.of R))
    (hc : a ≫ φ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) ≫ hV.fromSpec)
    (U : Z.Opens) (hU : IsAffineOpen U) (h : U ≤ φ ⁻¹ᵁ V) :
    letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
    ∃ l : (a ⁻¹ᵁ U).toScheme ⟶ Spec (.of (R ⊗[Γ(X, V)] Γ(Z, U))),
      l ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U))) =
        (a ⁻¹ᵁ U).ι ≫ q := by
  letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
  have e : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) Γ(Z, U))) ≫ hV.fromSpec =
      hU.fromSpec ≫ φ := IsAffineOpen.SpecMap_appLE_fromSpec φ hV hU h
  have key : ((a ⁻¹ᵁ U).ι ≫ q) ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) =
      ((a ∣_ U) ≫ hU.isoSpec.hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) Γ(Z, U))) := by
    rw [← cancel_mono hV.fromSpec]
    simp only [Category.assoc, e]
    rw [← hc, ← hU.isoSpec_inv_ι]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι_assoc]
  exact ⟨pullback.lift _ _ key ≫ (pullbackSpecIso _ _ _).hom, by
    rw [Category.assoc, pullbackSpecIso_hom_fst, pullback.lift_fst]⟩

theorem exists_chart_primes {X Z : Scheme.{0}} (φ : Z ⟶ X) [IsProper φ] (V : X.Opens)
    (hV : IsAffineOpen V) {R : Type} [CommRing R] [Algebra Γ(X, V) R] (p : Ideal R) (hp : p.IsPrime)
    (hz : ∃ z : Z, φ z = hV.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R))
      (⟨p, hp⟩ : PrimeSpectrum R))) :
    ∃ (U : Z.Opens) (_ : IsAffineOpen U) (h : U ≤ φ ⁻¹ᵁ V),
      letI : Algebra Γ(X, V) Γ(Z, U) := (φ.appLE V U h).hom.toAlgebra
      ∃ Q₀ Q₁ : Ideal (R ⊗[Γ(X, V)] Γ(Z, U)), Q₀.IsPrime ∧ Q₁.IsPrime ∧ Q₀ ≤ Q₁ ∧
        Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U)) = p ∧
        (Q₁.comap (Algebra.TensorProduct.includeLeftRingHom :
          R →+* R ⊗[Γ(X, V)] Γ(Z, U))).IsMaximal := by
  obtain ⟨z₀, hz₀⟩ := hz
  let g : Spec (.of R) ⟶ X := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) ≫ hV.fromSpec
  let a := pullback.fst φ g
  let q := pullback.snd φ g
  have hc : a ≫ φ = q ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) ≫ hV.fromSpec :=
    pullback.condition
  obtain ⟨y₀, -, hq₀⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ) (g := g) z₀
    (⟨p, hp⟩ : PrimeSpectrum R) hz₀
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hp.ne_top
  have hspec : q y₀ ⤳ (⟨m, hm.isPrime⟩ : PrimeSpectrum R) := by
    change pullback.snd φ g y₀ ⤳ _
    rw [hq₀]
    exact (PrimeSpectrum.le_iff_specializes _ _).mp hpm
  obtain ⟨y₁, hsp, hq₁⟩ := exists_specialization_over q.isClosedMap hspec
  have hy₁ : a y₁ ∈ φ ⁻¹ᵁ V := by
    have e : φ (a y₁) = hV.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) (q y₁)) := by
      have := congr($hc y₁)
      simpa using this
    change φ (a y₁) ∈ V
    rw [e]
    exact hV.range_fromSpec.subset ⟨_, rfl⟩
  obtain ⟨U', hU', hmem, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens hy₁
  have hU : IsAffineOpen U' := hU'
  refine ⟨U', hU, hle, ?_⟩
  letI : Algebra Γ(X, V) Γ(Z, U') := (φ.appLE V U' hle).hom.toAlgebra
  obtain ⟨l, hl⟩ := exists_chart_map φ V hV a q hc U' hU hle
  have hT₁ : y₁ ∈ a ⁻¹ᵁ U' := hmem
  have hT₀ : y₀ ∈ a ⁻¹ᵁ U' := hsp.mem_open (a ⁻¹ᵁ U').isOpen hT₁
  let t₀ : (a ⁻¹ᵁ U').toScheme := ⟨y₀, hT₀⟩
  let t₁ : (a ⁻¹ᵁ U').toScheme := ⟨y₁, hT₁⟩
  have ht : t₀ ⤳ t₁ := Topology.IsInducing.subtypeVal.specializes_iff.mp hsp
  have hcomp : ∀ t : (a ⁻¹ᵁ U').toScheme, Spec.map (CommRingCat.ofHom
      Algebra.TensorProduct.includeLeftRingHom) (l t) = q t.1 := fun t => congr($hl t)
  let P₀ : PrimeSpectrum (R ⊗[Γ(X, V)] Γ(Z, U')) := l t₀
  let P₁ : PrimeSpectrum (R ⊗[Γ(X, V)] Γ(Z, U')) := l t₁
  refine ⟨P₀.asIdeal, P₁.asIdeal, P₀.isPrime, P₁.isPrime, ?_, ?_, ?_⟩
  · exact (PrimeSpectrum.le_iff_specializes P₀ P₁).mpr (ht.map l.continuous)
  · exact congrArg PrimeSpectrum.asIdeal ((hcomp t₀).trans hq₀)
  · have e : P₁.asIdeal.comap
        (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U')) = m :=
      congrArg PrimeSpectrum.asIdeal ((hcomp t₁).trans hq₁)
    rw [e]
    exact hm

end KrullPts

theorem exists_chart_primes_of_isProper : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens) (hV : IsAffineOpen V) {R : Type} [CommRing R] [Algebra Γ(X, V) R] (f : Γ(X, V)), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ p : Ideal R, p.IsPrime → (J.ideal ⟨V, hV⟩).map (algebraMap Γ(X, V) R) ≤ p → algebraMap Γ(X, V) R f ∉ p → ∃ (U : Z.Opens) (_ : IsAffineOpen U) (h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V), letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∃ Q₀ Q₁ : Ideal (R ⊗[Γ(X, V)] Γ(Z, U)), Q₀.IsPrime ∧ Q₁.IsPrime ∧ Q₀ ≤ Q₁ ∧ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U)) = p ∧ (Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U))).IsMaximal := by
  intro X J Z ψ hψ V hV R _ _ f hiso p hp hJ hf
  haveI := hψ
  refine KrullPts.exists_chart_primes (ψ ≫ J.subschemeι) V hV p hp ?_
  let P : PrimeSpectrum Γ(X, V) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) R)) (⟨p, hp⟩ : PrimeSpectrum R)
  change ∃ z : Z, (ψ ≫ J.subschemeι) z = hV.fromSpec P
  have hxf : hV.fromSpec P ∈ X.basicOpen f := by
    have h1 : P ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hV.fromSpec_preimage_basicOpen]
      exact hf
    exact h1
  have hxV : hV.fromSpec P ∈ (V : Set X) := hV.range_fromSpec.subset ⟨_, rfl⟩
  have hxs : hV.fromSpec P ∈ (J.support : Set X) := by
    have h1 : hV.fromSpec P ∈ (J.support : Set X) ∩ (V : Set X) := by
      have e := J.coe_support_inter ⟨V, hV⟩
      refine e.symm.subset ⟨?_, hxV⟩
      rw [Scheme.mem_zeroLocus_iff]
      intro b hb hbx
      have h2 : P ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen b := hbx
      rw [hV.fromSpec_preimage_basicOpen] at h2
      exact h2 (hJ (Ideal.mem_map_of_mem _ hb))
    exact h1.1
  obtain ⟨y, hy⟩ := J.range_subschemeι.ge hxs
  have hyD : y ∈ J.subschemeι ⁻¹ᵁ X.basicOpen f := by
    change J.subschemeι y ∈ X.basicOpen f
    rw [hy]
    exact hxf
  haveI := hiso
  obtain ⟨w, hw⟩ := (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)).surjective ⟨y, hyD⟩
  have hψw : ψ w.1 = y :=
    (morphismRestrict_base_coe ψ _ w).symm.trans (congrArg Subtype.val hw)
  refine ⟨w.1, ?_⟩
  rw [Scheme.Hom.comp_apply, hψw, hy]

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperSupportPullbackSystem
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.PullSupp

theorem supportedIn_pullback {X Z : Scheme.{0}} (φ : Z ⟶ X) {C : X.Modules} {T₀ : Set X}
    (hT : IsClosed T₀) (h : Scheme.Modules.SupportedIn C T₀) :
    Scheme.Modules.SupportedIn ((Scheme.Modules.pullback φ).obj C) (φ.base ⁻¹' T₀) := by
  refine Scheme.Modules.SupportedIn.of_isZero_restrict fun U hU => ?_
  let V : X.Opens := ⟨T₀ᶜ, hT.isOpen_compl⟩
  have hr : Set.range (U.ι ≫ φ) ⊆ Set.range V.ι := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    intro hx
    exact Set.disjoint_left.1 hU u.2 hx
  let g := IsOpenImmersion.lift V.ι (U.ι ≫ φ) hr
  have hg : g ≫ V.ι = U.ι ≫ φ := IsOpenImmersion.lift_fac _ _ _
  have h0 : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj C) :=
    h.isZero_restrict V disjoint_compl_left
  have h1 : IsZero ((Scheme.Modules.pullback g).obj ((Scheme.Modules.restrictFunctor V.ι).obj C)) :=
    Functor.map_isZero _ h0
  refine h1.of_iso ?_
  exact (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫
    (Scheme.Modules.pullbackComp U.ι φ).app C ≪≫ (Scheme.Modules.pullbackCongr hg.symm).app C ≪≫
    ((Scheme.Modules.pullbackComp g V.ι).app C).symm ≪≫
    (Scheme.Modules.pullback g).mapIso ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app C).symm

end GlobalTheory.CompanionTheory.GE.PullSupp

namespace GlobalTheory.CompanionTheory.GE.PullSupp

theorem supportedIn_cokernel_pullSys {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X Z : Scheme.{0}} [Z.Over (Spec (.of A))] (φ : Z ⟶ X) (E : X.Modules) (S : ℕ → Subobject E)
    {T₀ : Set X} (hT : IsClosed T₀) (h : Scheme.Modules.SupportedIn (cokernel (S 0).arrow) T₀) :
    Scheme.Modules.SupportedIn (cokernel (pullSys I φ E S 0).arrow) (φ.base ⁻¹' T₀) := by
  let f := (Scheme.Modules.pullback φ).map (S 0).arrow
  have hle : imageSubobject f ≤ pullSys I φ E S 0 := le_sup_left
  have w : f ≫ cokernel.π (pullSys I φ E S 0).arrow = 0 := by
    rw [← imageSubobject_arrow_comp f, ← Subobject.ofLE_arrow hle, Category.assoc, Category.assoc,
      cokernel.condition, comp_zero, comp_zero]
  have hd : Epi (cokernel.desc f _ w) := epi_of_epi_fac (cokernel.π_desc f _ w)
  have h1 : Scheme.Modules.SupportedIn (cokernel f) (φ.base ⁻¹' T₀) :=
    (supportedIn_pullback φ hT h).of_iso (PreservesCokernel.iso (Scheme.Modules.pullback φ) (S 0).arrow)
  exact Scheme.Modules.SupportedIn.of_epi (cokernel.desc f _ w) h1

theorem exists_proper_preimage {A : Type} [CommRing A] {X Z : Scheme.{0}} [X.Over (Spec (.of A))]
    [Z.Over (Spec (.of A))] (φ : Z ⟶ X) (hφ : IsProper φ)
    (hc : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) (T : X.IdealSheafData)
    (hT : IsProper (T.subschemeι ≫ (X ↘ Spec (.of A)))) :
    ∃ T' : Z.IdealSheafData, IsProper (T'.subschemeι ≫ (Z ↘ Spec (.of A))) ∧
      φ.base ⁻¹' (T.support : Set X) ⊆ (T'.support : Set Z) := by
  let p := pullback.fst φ T.subschemeι
  let q := pullback.snd φ T.subschemeι
  have hpc : IsClosedImmersion p := inferInstance
  let T' : Z.IdealSheafData := p.ker
  have hk1 : p.ker ≤ T'.subschemeι.ker := by rw [Scheme.IdealSheafData.ker_subschemeι]
  have hk2 : T'.subschemeι.ker ≤ p.ker := by rw [Scheme.IdealSheafData.ker_subschemeι]
  let u := IsClosedImmersion.lift p T'.subschemeι hk1
  let v := IsClosedImmersion.lift T'.subschemeι p hk2
  have hu : u ≫ p = T'.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have hv : v ≫ T'.subschemeι = p := IsClosedImmersion.lift_fac _ _ _
  refine ⟨T', ?_, ?_⟩
  · have hq : IsProper q := by haveI := hφ; infer_instance
    have huc : IsClosedImmersion u := by
      have : IsClosedImmersion (u ≫ p) := by rw [hu]; infer_instance
      exact IsClosedImmersion.of_comp u p
    have e : T'.subschemeι ≫ (Z ↘ Spec (.of A)) = u ≫ q ≫ (T.subschemeι ≫ (X ↘ Spec (.of A))) := by
      rw [← hu, ← hc, Category.assoc, ← Category.assoc p, pullback.condition]
      simp only [Category.assoc]
      rfl
    rw [e]
    infer_instance
  · intro z hz
    obtain ⟨w, hw⟩ := T.range_subschemeι.ge hz
    obtain ⟨t, ht, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ) (g := T.subschemeι) z w hw.symm
    rw [← T'.range_subschemeι]
    refine ⟨v t, ?_⟩
    have hv' : v ≫ T'.subschemeι = pullback.fst φ T.subschemeι := hv
    rw [← ht, ← hv']
    rfl

theorem propSupp_pullSys : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}}
    [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), IsProper φ →
    φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E →
    ∀ {S : ℕ → Subobject E}, ClosedSys I E S → PropSupp A (S 0) → PropSupp A (pullSys I φ E S 0) := by
  intro A _ _ I X Z _ _ _ φ hφ hc E _ S _ hS
  obtain ⟨T, hTp, hTs⟩ := hS
  obtain ⟨T', hT'p, hT's⟩ := exists_proper_preimage φ hφ hc T hTp
  exact ⟨T', hT'p, (supportedIn_cokernel_pullSys I φ E S T.support.isClosed hTs).mono hT's⟩

end GlobalTheory.CompanionTheory.GE.PullSupp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardClosedSystemAuxiliary
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.KerSupp

theorem supportedIn_cokernel_kernelSubobject {X : Scheme.{0}} {F G : X.Modules} (g : F ⟶ G) {T : Set X}
    (h : Scheme.Modules.SupportedIn G T) :
    Scheme.Modules.SupportedIn (cokernel (kernelSubobject g).arrow) T := by
  let S : ShortComplex X.Modules := ShortComplex.mk (kernel.ι g) g (kernel.condition _)
  have hex : S.Exact := ShortComplex.exact_kernel _
  have hm : Mono (cokernel.desc S.f S.g S.zero) := S.exact_iff_mono_cokernel_desc.1 hex
  have h1 : Scheme.Modules.SupportedIn (cokernel (kernel.ι g)) T :=
    Scheme.Modules.SupportedIn.of_mono (cokernel.desc S.f S.g S.zero) h
  have e : (kernelSubobjectIso g).hom ≫ kernel.ι g = (kernelSubobject g).arrow :=
    kernelSubobject_arrow g
  let i : cokernel (kernelSubobject g).arrow ≅ cokernel (kernel.ι g) :=
    cokernelIsoOfEq e.symm ≪≫ (cokernelEpiComp (kernelSubobjectIso g).hom _)
  exact h1.of_iso i.symm

theorem toImage_surjective {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f] : Surjective f.toImage := by
  refine ⟨fun y => ?_⟩
  have h1 : f.imageι y ∈ (f.ker.support : Set X) := f.ker.range_subschemeι.le ⟨y, rfl⟩
  rw [Scheme.Hom.support_ker, f.isClosedMap.isClosed_range.closure_eq] at h1
  obtain ⟨x, hx⟩ := h1
  refine ⟨x, f.imageι.isEmbedding.injective ?_⟩
  rw [← hx, ← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]

theorem isProper_image {S Y X : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [IsSeparated p]
    [LocallyOfFiniteType p] [QuasiCompact p] [IsProper f] (hY : IsProper (f ≫ p)) :
    IsProper (f.ker.subschemeι ≫ p) := by
  have := toImage_surjective f
  have hu : UniversallyClosed (f.toImage ≫ f.ker.subschemeι ≫ p) := by
    rw [← Category.assoc]
    change UniversallyClosed ((f.toImage ≫ f.imageι) ≫ p)
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  have : UniversallyClosed (f.ker.subschemeι ≫ p) := .of_comp_surjective f.toImage _
  exact ⟨⟩

theorem propSupp_adjKer {A : Type} [CommRing A] [IsNoetherianRing A] {X Z : Scheme.{0}}
    [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))]
    [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] (φ : Z ⟶ X)
    (hφ : IsProper φ) (hc : φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A))) {E : X.Modules}
    (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (hB : PropSupp A B) :
    PropSupp A (adjKer φ B) := by
  obtain ⟨TZ, hTZ, hsupp⟩ := hB
  let f : TZ.subscheme ⟶ X := TZ.subschemeι ≫ φ
  have hf : IsProper f := inferInstance
  have hfp : IsProper (f ≫ (X ↘ Spec (.of A))) := by
    change IsProper ((TZ.subschemeι ≫ φ) ≫ (X ↘ Spec (.of A)))
    rw [Category.assoc, hc]
    exact hTZ
  refine ⟨f.ker, isProper_image f _ hfp, ?_⟩
  have hpush := hsupp.pushforward φ
  have hsub : φ.base '' (TZ.support : Set Z) ⊆ (f.ker.support : Set X) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw⟩ := TZ.range_subschemeι.ge hz
    rw [Scheme.Hom.support_ker]
    refine subset_closure ⟨w, ?_⟩
    rw [← hw]
    rfl
  exact supportedIn_cokernel_kernelSubobject (adjMap φ B) (hpush.mono hsub)

end GlobalTheory.CompanionTheory.GE.KerSupp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionClassNumberFinite
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.Compact

section General

open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic
open scoped NumberField.AdeleRing

attribute [local instance] adeleTensorTopology isModuleTopology_adeleTensor
  isTopologicalRing_adeleTensor t2Space_adeleTensor

set_option maxSynthPendingDepth 1 in

theorem exists_compact_transport {K D B : Type*} [Field K] [NumberField K] [DivisionRing D] [Algebra K D]
    [FiniteDimensional K D] [Ring B] [Algebra 𝔸[K] B] [TopologicalSpace B] [IsTopologicalRing B]
    [ContinuousSMul 𝔸[K] B] (Φ : 𝔸[K] ⊗[K] D ≃ₐ[𝔸[K]] B) :
    ∃ C : Set Bˣ, IsCompact C ∧ ∀ y : Bˣ, ∃ c ∈ C, ∃ δ : Dˣ, ∃ z : (𝔸[K])ˣ,
      y = c * Units.map (Φ : 𝔸[K] ⊗[K] D →* B) (rationalUnits K D δ) *
        Units.map (Φ : 𝔸[K] ⊗[K] D →* B) (scalarUnits K D z) := by
  obtain ⟨Ω, hΩ, hdec⟩ := exists_isCompact_normOneUnits (K := K) (D := D) (Module.finBasis K D)
  let f : (𝔸[K] ⊗[K] D)ˣ →* Bˣ := Units.map (Φ : 𝔸[K] ⊗[K] D →* B)
  have hΦ : Continuous (Φ : 𝔸[K] ⊗[K] D →* B) :=
    IsModuleTopology.continuous_of_linearMap Φ.toLinearEquiv.toLinearMap
  have hf : Continuous f := Continuous.units_map _ hΦ
  refine ⟨(fun w => (f w)⁻¹) '' Ω, hΩ.image hf.inv, fun y => ?_⟩
  let g : Bˣ →* (𝔸[K] ⊗[K] D)ˣ := Units.map (Φ.symm : B →* 𝔸[K] ⊗[K] D)
  have hfg : f (g y) = y := Units.ext (by simp [f, g])
  obtain ⟨a, ha⟩ := exists_scalar_mem_normOneUnits (Module.finBasis K D) (g y)⁻¹
  obtain ⟨δ, hδ⟩ := hdec _ ha
  refine ⟨_, ⟨_, hδ, rfl⟩, δ⁻¹, a, ?_⟩
  change y = (f _)⁻¹ * f (rationalUnits K D δ⁻¹) * f (scalarUnits K D a)
  simp only [map_mul, map_inv, hfg]
  group

end General

section Quat

variable {F : Type} [Field F] {d β : F} {R : Type} [CommRing R] [Algebra F R]

@[reducible] def divRing (h : ∀ x : Q d β F, qn x = 0 → x = 0) : DivisionRing (Q d β F) :=
  { (inferInstance : Ring (Q d β F)) with
    inv := fun x => (qn x)⁻¹ • star x
    exists_pair_ne := ⟨0, 1, fun e => zero_ne_one (congrArg QuaternionAlgebra.re e)⟩
    mul_inv_cancel := fun x hx => by
      have hq : qn x ≠ 0 := fun e => hx (h x e)
      change x * ((qn x)⁻¹ • star x) = 1
      rw [mul_smul_comm, mul_star_eq, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hq, map_one]
    inv_zero := by
      change (qn (0 : Q d β F))⁻¹ • star (0 : Q d β F) = 0
      simp
    nnqsmul := _
    qsmul := _ }

def ratA : Q d β F →ₐ[F] Q d β R :=
  { (rat : Q d β F →+* Q d β R) with
    commutes' := fun r => by
      have e : algebraMap F (Q d β R) r = ⟨algebraMap F R r, 0, 0, 0⟩ := rfl
      ext <;> simp [rat, qmap, Algebra.ofId_apply, QuaternionAlgebra.algebraMap_eq, e] }

def phi : R ⊗[F] Q d β F →ₐ[R] Q d β R :=
  Algebra.TensorProduct.lift (Algebra.ofId R (Q d β R)) ratA (fun a _ => Algebra.commutes a _)

theorem phi_tmul (a : R) (x : Q d β F) :
    phi (d := d) (β := β) (R := R) (a ⊗ₜ[F] x) = algebraMap R (Q d β R) a * rat x := by
  exact Algebra.TensorProduct.lift_tmul _ _ _ a x

def psi (x : Q d β R) : R ⊗[F] Q d β F :=
  x.re ⊗ₜ[F] (⟨1, 0, 0, 0⟩ : Q d β F) + x.imI ⊗ₜ[F] (⟨0, 1, 0, 0⟩ : Q d β F) +
    x.imJ ⊗ₜ[F] (⟨0, 0, 1, 0⟩ : Q d β F) + x.imK ⊗ₜ[F] (⟨0, 0, 0, 1⟩ : Q d β F)

theorem phi_psi (x : Q d β R) : phi (d := d) (β := β) (R := R) (psi x) = x := by
  simp only [psi, map_add, phi_tmul]
  ext <;> simp [rat, qmap, QuaternionAlgebra.algebraMap_eq]

theorem psi_add (x y : Q d β R) : psi (x + y) = psi x + psi y := by
  simp only [psi, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
    QuaternionAlgebra.imK_add, TensorProduct.add_tmul]
  abel

theorem mul_algebraMap_tmul (a : R) (c : F) (y : Q d β F) :
    (a * algebraMap F R c) ⊗ₜ[F] y = a ⊗ₜ[F] (c • y) := by
  rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]

theorem psi_phi (t : R ⊗[F] Q d β F) : psi (phi (d := d) (β := β) (R := R) t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp [psi]
  | add x y hx hy => rw [map_add, psi_add, hx, hy]
  | tmul a x =>
    rw [phi_tmul]
    have e : x = x.re • (⟨1, 0, 0, 0⟩ : Q d β F) + x.imI • (⟨0, 1, 0, 0⟩ : Q d β F) +
        x.imJ • (⟨0, 0, 1, 0⟩ : Q d β F) + x.imK • (⟨0, 0, 0, 1⟩ : Q d β F) := by
      ext <;> simp
    have key : psi (algebraMap R (Q d β R) a * rat x) =
        (a * algebraMap F R x.re) ⊗ₜ[F] (⟨1, 0, 0, 0⟩ : Q d β F) +
          (a * algebraMap F R x.imI) ⊗ₜ[F] (⟨0, 1, 0, 0⟩ : Q d β F) +
          (a * algebraMap F R x.imJ) ⊗ₜ[F] (⟨0, 0, 1, 0⟩ : Q d β F) +
          (a * algebraMap F R x.imK) ⊗ₜ[F] (⟨0, 0, 0, 1⟩ : Q d β F) := by
      simp [psi, rat, qmap, QuaternionAlgebra.algebraMap_eq, Algebra.ofId_apply]
    rw [key]
    simp only [mul_algebraMap_tmul]
    rw [← TensorProduct.tmul_add, ← TensorProduct.tmul_add, ← TensorProduct.tmul_add, ← e]

def phiEquiv : R ⊗[F] Q d β F ≃ₐ[R] Q d β R :=
  AlgEquiv.ofBijective (phi (d := d) (β := β) (R := R))
    ⟨Function.LeftInverse.injective psi_phi, Function.RightInverse.surjective phi_psi⟩

theorem continuousSMul_q [TopologicalSpace R] [IsTopologicalRing R] : ContinuousSMul R (Q d β R) := by
  constructor
  rw [continuous_q_iff]
  simp only [QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, smul_eq_mul]
  exact ⟨continuous_fst.mul (continuous_re.comp continuous_snd),
    continuous_fst.mul (continuous_imI.comp continuous_snd),
    continuous_fst.mul (continuous_imJ.comp continuous_snd),
    continuous_fst.mul (continuous_imK.comp continuous_snd)⟩

end Quat

theorem exists_isCompact_units :
    ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∃ C : Set (Q d β (AF F))ˣ, IsCompact C ∧ ∀ y : (Q d β (AF F))ˣ, ∃ c ∈ C, ∃ δ : (Q d β F)ˣ, ∃ z : (AF F)ˣ,
    y = c * Units.map (rat (R := AF F) : Q d β F →+* Q d β (AF F)).toMonoidHom δ *
      Units.map (algebraMap (AF F) (Q d β (AF F))).toMonoidHom z := by
  intro F _ _ d β h
  letI : DivisionRing (Q d β F) := divRing h
  haveI : ContinuousSMul (AF F) (Q d β (AF F)) := continuousSMul_q
  obtain ⟨C, hC, hdec⟩ := exists_compact_transport (K := F) (D := Q d β F) (B := Q d β (AF F)) phiEquiv
  refine ⟨C, hC, fun y => ?_⟩
  obtain ⟨c, hc, δ, z, e⟩ := hdec y
  refine ⟨c, hc, δ, z, ?_⟩
  have h1 : Units.map (phiEquiv (d := d) (β := β) (R := AF F) : AF F ⊗[F] Q d β F →* Q d β (AF F))
      (GroundTheory.Automorphic.Anisotropic.rationalUnits F (Q d β F) δ) =
      Units.map (rat (R := AF F) : Q d β F →+* Q d β (AF F)).toMonoidHom δ := by
    refine Units.ext ?_
    change phi (d := d) (β := β) (R := AF F) ((1 : AF F) ⊗ₜ[F] (δ : Q d β F)) = rat (δ : Q d β F)
    rw [phi_tmul, map_one, one_mul]
  have h2 : Units.map (phiEquiv (d := d) (β := β) (R := AF F) : AF F ⊗[F] Q d β F →* Q d β (AF F))
      (GroundTheory.Automorphic.Anisotropic.scalarUnits F (Q d β F) z) =
      Units.map (algebraMap (AF F) (Q d β (AF F))).toMonoidHom z :=
    Units.ext ((phiEquiv (d := d) (β := β) (R := AF F)).commutes (z : AF F))
  rw [e, h1, h2]

end GlobalTheory.CompanionTheory.PlaneSA.Compact
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionRamifiedPlacesFinite
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem exists_isotropic_of_sq_sub_mul_sq {F K : Type} [Field F] [Field K] [Algebra F K] {d β : F} {x y : K}
    (h : x ^ 2 - algebraMap F K d * y ^ 2 = algebraMap F K β) :
    ∃ q : Q d β K, qn q = 0 ∧ q ≠ 0 := by
  refine ⟨⟨x, y, 1, 0⟩, ?_, fun hq => ?_⟩
  · simp only [qn]
    rw [← h]
    ring
  · exact one_ne_zero (congrArg QuaternionAlgebra.imJ hq : (1 : K) = 0)

theorem finite_anisotropic_places {F : Type} [Field F] [NumberField F] (d β : F)
    (hd : ∀ r : F, r ^ 2 ≠ d) (hβ : β ≠ 0) :
    {u : Pl F | ∀ x : Q d β (Kp u), qn x = 0 → x = 0}.Finite := by
  have hB := GroundTheory.Automorphic.eventually_exists_sq_sub_mul_sq hd hβ
  rw [Filter.eventually_cofinite] at hB
  refine ((Set.finite_univ (α := InfinitePlace F)).image Sum.inl |>.union (hB.image Sum.inr)).subset ?_
  rintro (w | v) hu
  · exact Or.inl ⟨w, Set.mem_univ _, rfl⟩
  · refine Or.inr ⟨v, ?_, rfl⟩
    rintro ⟨x, y, hxy⟩
    obtain ⟨q, hq0, hq⟩ := exists_isotropic_of_sq_sub_mul_sq (F := F) (K := Kp (Sum.inr v : Pl F))
      (d := d) (β := β) (x := x) (y := y) hxy
    exact hq (hu q hq0)

end GlobalTheory.CompanionTheory.PlaneSA
end

