import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfHasRepUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2533
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2534
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolydiscCmUniformization
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointCochainPullbackBaseChangeCocycleCoboundaryW
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {X : Over (Sp R)} {X' : Over (Sp R')}
  {q : X'.left ⟶ X.left}

theorem ptVia_spOver (w : q ≫ X.hom = X'.hom ≫ spMap σ) {E E' : Type} [CommRing E] [Algebra R' E]
    [CommRing E'] [Algebra R' E'] (φ : E →ₐ[R'] E') (y : Pt X' E) :
    ptVia w (spOver φ ≫ y) =
      @CategoryStruct.comp _ _ _ _ _ (@spOver R _ E E' _ (algVia σ E) _ (algVia σ E') (homVia σ φ)) (ptVia w y) := by
  letI := algVia σ E
  letI := algVia σ E'
  apply Over.OverMorphism.ext
  change (spMap (φ : E →+* E') ≫ y.left) ≫ q = spMap (φ : E →+* E') ≫ (y.left ≫ q)
  rw [Category.assoc]

theorem bcPull_coc_cob (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X) :
    (IsCoc (whole X) u → IsCoc (whole X') (bcPull w u)) ∧
      ((∃ k, IsCob (whole X) u k) → ∃ k, IsCob (whole X') (bcPull w u) k) := by
  constructor
  · intro h E _ _ E' _ _ E'' _ _ φ ψ y _
    letI := algVia σ E
    letI := algVia σ E'
    letI := algVia σ E''
    have e := h E E' E'' (homVia σ φ) (homVia σ ψ) (ptVia w y) (sm_whole _)
    have hc : (homVia σ ψ).comp (homVia σ φ) = homVia σ (ψ.comp φ) := AlgHom.ext fun _ ↦ rfl
    rw [hc, ← ptVia_spOver] at e
    exact e
  · rintro ⟨k, hk⟩
    refine ⟨fun E _ _ y ↦ @k E _ (algVia σ E) (ptVia w y), ?_⟩
    intro E _ _ E' _ _ φ y _
    letI := algVia σ E
    letI := algVia σ E'
    have e := hk E E' (homVia σ φ) (ptVia w y) (sm_whole _)
    rw [← ptVia_spOver] at e
    exact e

theorem bcPull_keeps : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R)) (X' : Over (Sp R')) (q : X'.left ⟶ X.left) (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X), (IsCoc (whole X) u → IsCoc (whole X') (bcPull w u)) ∧ ((∃ k, IsCob (whole X) u k) → ∃ k, IsCob (whole X') (bcPull w u) k) :=
  fun _ _ _ _ _ _ _ _ w u ↦ bcPull_coc_cob w u

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointDisjointUnionRepresentingFamilyUnique
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.ProdGlue

theorem same_precomp {S : Scheme.{0}} {A T U Y Z : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left}
    (hN : N.IsLB) (hM : M.IsLB) {y : Y ⟶ T} {u : Y ⟶ U} (z : Z ⟶ Y)
    (e : Same A N M y u) : Same A N M (z ≫ y) (z ≫ u) := by
  have e' := congrArg (CechPic.pull (lift (fst A Z) (snd A Z ≫ z)).left) ((same_iff hN hM _ _).1 e)
  rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc, Category.assoc, Category.assoc] at e'
  exact (same_iff hN hM _ _).2 e'

theorem eq_of_same_of_disjoint_cover : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (X : Over S) (V : κ → X.left.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left], (⨆ i, (j i).left.opensRange = ⊤) → (Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) → ∀ (b : ∀ i, B i ⟶ Over.mk ((V i).ι ≫ X.hom)) (bt : Bt ⟶ X), (∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι) → ∀ (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left), (∀ i, Rep A (b i) (P i)) → Pt.IsLB → (∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) → ∀ (T : Over S) (x y : T ⟶ Bt), x ≫ bt = y ≫ bt → Same A Pt Pt x y → x = y := by
  intro S A _ κ _ X V hV hVd Bt B j _ hj hjd b bt hb P Pt hP hPt hPi T x y hxy e

  have mem : ∀ i (p : Bt.left), bt.left p ∈ V i → p ∈ Set.range (j i).left := by
    intro i p hp
    have hp' : p ∈ (⨆ i', (j i').left.opensRange) := by rw [hj]; trivial
    obtain ⟨i', q, rfl⟩ := (TopologicalSpace.Opens.mem_iSup.1 hp')
    have h1 : bt.left ((j i').left q) ∈ V i' := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hb i', Over.comp_left, Scheme.Hom.comp_apply]
      change (V i').ι ((b i').left q) ∈ V i'
      exact (Scheme.Opens.range_ι (V i')).subset ⟨_, rfl⟩
    by_cases hii : i' = i
    · subst hii; exact ⟨q, rfl⟩
    · exact absurd (⟨h1, hp⟩ : bt.left ((j i').left q) ∈ (V i' ⊓ V i : X.left.Opens))
        (fun h ↦ (hVd hii).le_bot h)
  have loc : ∀ i, ((x ≫ bt).left ⁻¹ᵁ V i).ι ≫ x.left = ((x ≫ bt).left ⁻¹ᵁ V i).ι ≫ y.left := by
    intro i
    let Ti : Over S := Over.mk (((x ≫ bt).left ⁻¹ᵁ V i).ι ≫ T.hom)
    let w : Ti ⟶ T := Over.homMk ((x ≫ bt).left ⁻¹ᵁ V i).ι rfl
    have lf : ∀ z : T ⟶ Bt, z ≫ bt = x ≫ bt → ∃ zi : Ti ⟶ B i, zi ≫ j i = w ≫ z := by
      intro z hz
      have r : Set.range (w ≫ z).left ⊆ Set.range (j i).left := by
        rintro _ ⟨p, rfl⟩
        apply mem i
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Category.assoc, hz, Over.comp_left,
          Scheme.Hom.comp_apply]
        exact (Scheme.Opens.range_ι ((x ≫ bt).left ⁻¹ᵁ V i)).subset ⟨p, rfl⟩
      exact ⟨Over.homMk (IsOpenImmersion.lift (j i).left _ r)
        (by rw [← Over.w (j i), IsOpenImmersion.lift_fac_assoc, Over.w]),
        Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)⟩
    obtain ⟨xi, hx⟩ := lf x rfl
    obtain ⟨yi, hy⟩ := lf y hxy.symm
    have hQ := (hP i).fam.isLB
    have hb' : xi ≫ b i = yi ≫ b i := by
      have k : xi ≫ b i ≫ Over.homMk (V i).ι = yi ≫ b i ≫ Over.homMk (V i).ι := by
        rw [← hb, reassoc_of% hx, reassoc_of% hy, hxy]
      apply Over.OverMorphism.ext
      rw [← cancel_mono (V i).ι]
      exact congrArg (fun q ↦ q.left) k
    have hs : Same A (P i) (P i) xi yi := by
      have e2 := (same_iff hPt hPt _ _).1 (same_precomp hPt hPt w e)
      rw [same_iff hQ hQ, ← evc_comp_of_iso (j i) hPt hQ (hPi i), ← evc_comp_of_iso (j i) hPt hQ (hPi i),
        Category.assoc, Category.assoc, hx, hy]
      exact e2
    have h3 := Model.rep_ext (hP i) hb' hs
    exact congrArg (fun q ↦ q.left) (show w ≫ x = w ≫ y by rw [← hx, ← hy, h3])
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun z ↦ ?_)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show (x ≫ bt).left z ∈ ⨆ i, V i by rw [hV]; trivial)
  exact ⟨_, hi, loc i⟩

end GlobalTheory.DualCon.ProdGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseCocycleLocalSectionsGlueBasicOpenCover
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtExt.GlueSec

variable {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} {W : K → X.left.Opens} {u : Fn1 X}
  {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) {n : ℕ}
  (τ : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E)

def locVal (u : Fn1 X) (a : Fin n) {E : Type} [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E)
    (F : Type) [CommRing F] [Algebra R F] (ρ : E →ₐ[R] F) : F :=
  τ a F (ρ.comp ψ) - u E F ρ (spOver ψ ≫ x)

theorem pt_comp {E F : Type} [CommRing E] [Algebra R E] [CommRing F] [Algebra R F]
    (ψ : D →ₐ[R] E) (ρ : E →ₐ[R] F) : spOver (ρ.comp ψ) ≫ x = spOver ρ ≫ (spOver ψ ≫ x) := by
  rw [← spOver_comp, Category.assoc]

theorem sm_comp {E F : Type} [CommRing E] [Algebra R E] [CommRing F] [Algebra R F]
    (ψ : D →ₐ[R] E) (ρ : E →ₐ[R] F) (h : Sm W (spOver ψ ≫ x)) : Sm W (spOver (ρ.comp ψ) ≫ x) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, fun p _ ↦ ?_⟩
  rw [pt_comp]
  exact hi trivial

variable {x τ} {s : Fin n → D}

theorem locVal_map (hu : IsCoc W u)
    (hsec : ∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) →
      τ a E' (θ.comp ψ) - θ (τ a E ψ) = u E E' θ (spOver ψ ≫ x))
    (a : Fin n) {E : Type} [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E) (hsm : Sm W (spOver ψ ≫ x))
    {F G : Type} [CommRing F] [Algebra R F] [CommRing G] [Algebra R G] (ρ : E →ₐ[R] F) (θ : F →ₐ[R] G)
    (hunit : IsUnit (ρ (ψ (s a)))) :
    θ (locVal x τ u a ψ F ρ) = locVal x τ u a ψ G (θ.comp ρ) := by
  have h1 := hsec a F G (ρ.comp ψ) θ hunit
  have h2 := hu E F G ρ θ (spOver ψ ≫ x) hsm
  rw [pt_comp] at h1
  unfold locVal
  rw [map_sub, AlgHom.comp_assoc]
  linear_combination h2 - h1

theorem locVal_agree
    (hagree : ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → τ a E ψ = τ b E ψ)
    (a b : Fin n) {E : Type} [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E)
    {F : Type} [CommRing F] [Algebra R F] (ρ : E →ₐ[R] F)
    (ha : IsUnit (ρ (ψ (s a)))) (hb : IsUnit (ρ (ψ (s b)))) :
    locVal x τ u a ψ F ρ = locVal x τ u b ψ F ρ := by
  unfold locVal
  rw [hagree a b F (ρ.comp ψ) ha hb]

theorem span_range (hs : Ideal.span (Set.range s) = ⊤) {E : Type} [CommRing E] [Algebra R E]
    (ψ : D →ₐ[R] E) : Ideal.span (Set.range fun a ↦ ψ (s a)) = ⊤ := by
  have : (Set.range fun a ↦ ψ (s a)) = ψ '' Set.range s := (Set.range_comp ψ s)
  rw [this, ← Ideal.map_span, hs, Ideal.map_top]

end GlobalTheory.PtExt.GlueSec

namespace GlobalTheory.PtExt.GlueSec

variable {R : Type} [CommRing R] {X : Over (Sp R)} {K : Type} {W : K → X.left.Opens} {u : Fn1 X}
  {D : Type} [CommRing D] [Algebra R D] {x : Pt X D} {n : ℕ}
  {τ : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E} {s : Fin n → D}

theorem isUnit_locAlg {E : Type} [CommRing E] [Algebra R E] (t : E) : IsUnit (locAlg R t t) :=
  IsLocalization.Away.algebraMap_isUnit t

theorem glue_exists (hs : Ideal.span (Set.range s) = ⊤) (hu : IsCoc W u)
    (hsec : ∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) →
      τ a E' (θ.comp ψ) - θ (τ a E ψ) = u E E' θ (spOver ψ ≫ x))
    (hagree : ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → τ a E ψ = τ b E ψ)
    {E : Type} [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E) (hsm : Sm W (spOver ψ ≫ x)) :
    ∃ e : E, ∀ (F : Type) [CommRing F] [Algebra R F] (ρ : E →ₐ[R] F) (a : Fin n),
      IsUnit (ρ (ψ (s a))) → ρ e = locVal x τ u a ψ F ρ := by
  let T : Set E := Set.range fun a ↦ ψ (s a)
  have hT : Ideal.span T = ⊤ := span_range hs ψ
  have hc : ∀ t : T, ∃ a, ψ (s a) = t.1 := fun t ↦ t.2
  choose c hc using hc
  have hcu : ∀ t : T, IsUnit (locAlg R t.1 (ψ (s (c t)))) := fun t ↦ by
    rw [hc t]; exact isUnit_locAlg _
  let v : ∀ t : T, Localization.Away t.1 := fun t ↦ locVal x τ u (c t) ψ _ (locAlg R t.1)
  obtain ⟨e, he, -⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top T hT v (fun t₁ t₂ ↦ by
    change awR R t₁.1 t₂.1 (v t₁) = awL R t₁.1 t₂.1 (v t₂)
    have hm : IsUnit (locAlg R (t₁.1 * t₂.1) (t₁.1 * t₂.1)) := isUnit_locAlg _
    rw [map_mul] at hm
    simp only [v]
    rw [locVal_map hu hsec _ ψ hsm _ _ (hcu t₁), locVal_map hu hsec _ ψ hsm _ _ (hcu t₂), awR_comp, awL_comp]
    apply locVal_agree hagree
    · rw [hc t₁]; exact isUnit_of_mul_isUnit_left hm
    · rw [hc t₂]; exact isUnit_of_mul_isUnit_right hm)
  refine ⟨e, fun F _ _ ρ a ha ↦ ?_⟩
  apply Localization.algebraMap_injective_of_span_eq_top _ (span_range hs (ρ.comp ψ))
  funext ⟨_, b, rfl⟩
  let t : T := ⟨ψ (s b), b, rfl⟩
  let lam : F →ₐ[R] Localization.Away (ρ (ψ (s b))) := locAlg R (ρ (ψ (s b)))
  let mu : Localization.Away t.1 →ₐ[R] Localization.Away (ρ (ψ (s b))) := Localization.awayMapₐ ρ t.1
  have hmu : mu.comp (locAlg R t.1) = lam.comp ρ := AlgHom.ext fun z ↦ by
    simp [mu, lam, t, Localization.awayMapₐ, IsLocalization.Away.mapₐ, IsLocalization.Away.map,
      IsLocalization.map_eq]
  change lam (ρ e) = lam (locVal x τ u a ψ F ρ)
  have het : locAlg R t.1 e = v t := he t
  rw [locVal_map hu hsec a ψ hsm ρ lam ha]
  rw [show lam (ρ e) = mu (locAlg R t.1 e) from (DFunLike.congr_fun hmu e).symm, het]
  simp only [v]
  rw [locVal_map hu hsec _ ψ hsm _ _ (hcu t), hmu]
  apply locVal_agree hagree
  · rw [AlgHom.comp_apply, hc t]; exact isUnit_locAlg _
  · exact ha.map lam

end GlobalTheory.PtExt.GlueSec

namespace GlobalTheory.PtExt

open GlueSec in

theorem glue_sections : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens) (u : Fn1 X), IsCoc W u → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D) (n : ℕ) (s : Fin n → D), Ideal.span (Set.range s) = ⊤ → ∀ τ : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, (∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) → τ a E' (θ.comp ψ) - θ (τ a E ψ) = u E E' θ (spOver ψ ≫ x)) → (∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → τ a E ψ = τ b E ψ) → ∃ σ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), Sm W (spOver ψ ≫ x) → σ E' (θ.comp ψ) - θ (σ E ψ) = u E E' θ (spOver ψ ≫ x) := by
  intro R _ X K W u hu D _ _ x n s hs τ hsec hagree
  classical
  let σ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E := fun E _ _ ψ ↦
    if h : Sm W (spOver ψ ≫ x) then Classical.choose (glue_exists hs hu hsec hagree ψ h) else 0
  refine ⟨σ, fun E _ _ E' _ _ ψ θ hsm ↦ ?_⟩
  have hsm' : Sm W (spOver (θ.comp ψ) ≫ x) := sm_comp x ψ θ hsm
  have P := Classical.choose_spec (glue_exists hs hu hsec hagree ψ hsm)
  have P' := Classical.choose_spec (glue_exists hs hu hsec hagree (θ.comp ψ) hsm')
  have e1 : σ E ψ = Classical.choose (glue_exists hs hu hsec hagree ψ hsm) := dif_pos hsm
  have e2 : σ E' (θ.comp ψ) = Classical.choose (glue_exists hs hu hsec hagree (θ.comp ψ) hsm') := dif_pos hsm'
  rw [e1, e2]
  apply Localization.algebraMap_injective_of_span_eq_top _ (span_range hs (θ.comp ψ))
  funext ⟨_, a, rfl⟩
  let lam : E' →ₐ[R] Localization.Away ((θ.comp ψ) (s a)) := locAlg R ((θ.comp ψ) (s a))
  let lt : E →ₐ[R] Localization.Away ((θ.comp ψ) (s a)) := lam.comp θ
  change lam (Classical.choose (glue_exists hs hu hsec hagree (θ.comp ψ) hsm') - θ (Classical.choose (glue_exists hs hu hsec hagree ψ hsm))) = lam (u E E' θ (spOver ψ ≫ x))
  rw [map_sub, P' (Localization.Away ((θ.comp ψ) (s a))) lam a (isUnit_locAlg ((θ.comp ψ) (s a))),
    show lam (θ (Classical.choose (glue_exists hs hu hsec hagree ψ hsm))) =
      lt (Classical.choose (glue_exists hs hu hsec hagree ψ hsm)) from rfl,
    P (Localization.Away ((θ.comp ψ) (s a))) lt a (isUnit_locAlg (R := R) ((θ.comp ψ) (s a)))]
  have h2 := hu E E' (Localization.Away ((θ.comp ψ) (s a))) θ lam (spOver ψ ≫ x) hsm
  unfold locVal
  simp only [lt]
  rw [pt_comp x ψ θ, AlgHom.comp_assoc]
  linear_combination h2

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVDimEqOfGrpPullbackFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polAV_dim_eq_of_grpPullback_field : ∀ (K : Type) [Field K] (T : Scheme.{0}) (P : PolAV T) (P₀ : PolAV (Sp K)) (f : Sp K ⟶ T) (a : P₀.A.left ⟶ P.A.left), IsGrpPullback P₀.A P.A f a → P₀.g = P.g := by
  first | exact @GlobalTheory.polAV_g_eq_of_isGrpPullback | exact GlobalTheory.polAV_g_eq_of_isGrpPullback | (intros; apply GlobalTheory.polAV_g_eq_of_isGrpPullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedPeriodComparisonSymmCocycleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedPeriod_comparison_symm_cocycle : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (f : D.X → D.X → (FractionRing R')ˣ), Function.Injective ρ → Half Q ρ D e f → (∀ a b, f a b = f b a) ∧ ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c := by
  first | exact @GlobalTheory.PolDeg.half_symm_cocycle | exact GlobalTheory.PolDeg.half_symm_cocycle | (intros; apply GlobalTheory.PolDeg.half_symm_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormExistsForCmObject
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
open GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolPairing

theorem exists_isCorrForm_diag : GlobalTheory.Published.AbelianDeRham → ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R : Type) [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt), ∃ ψ : LinearMap.BilinForm R (HdR X.A),
      GlobalTheory.AbDual.IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) ψ ∧ IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ((2 : R) • ψ) := by
  intro H F _ _ 𝔠 R _ X c
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab
  have gAB := smooth_prod X.dim X.dim
  have C := cupSquare_of_free H.1 hAB gAB
  have hP := X.isLB c
  obtain ⟨φ, hφ⟩ := exists_isCorrForm C hP (X.rig₁ c) (X.rig₂ c)
  have anti : ∀ x y, φ y x = -φ x y := by
    obtain ⟨n, a, b, hc, hφe⟩ := id hφ
    let s : X.A ⊗ X.A ⟶ X.A ⊗ X.A := lift (snd X.A X.A) (fst X.A X.A)
    have m : IsMor (dp0 R) ((X.A ⊗ X.A).hom ≫ 𝟙 _) (dp0 R) ((X.A ⊗ X.A).hom ≫ 𝟙 _) (RingHom.id R) s.left :=
      IsMor.of_over _ (by rw [← Category.assoc, Over.w])
    have e₁ : ∀ z, m.pull1 (pullOver (dp0 R) (𝟙 _) (fst X.A X.A) z) = pullOver (dp0 R) (𝟙 _) (snd X.A X.A) z :=
      fun z ↦ (pullOver_pullOver _ _ s (fst X.A X.A) z).trans (by rw [lift_fst])
    have e₂ : ∀ z, m.pull1 (pullOver (dp0 R) (𝟙 _) (snd X.A X.A) z) = pullOver (dp0 R) (𝟙 _) (fst X.A X.A) z :=
      fun z ↦ (pullOver_pullOver _ _ s (snd X.A X.A) z).trans (by rw [lift_snd])
    have hs := isChern_pull m hc
    rw [map_sum] at hs
    simp only [IsMor.pullCohomologyTwo_cup, e₁, e₂] at hs
    have hs' := (isChern_existsUnique_and_iso R _ (dp0 R) _ _).2 _ _ (pull_isLB hP _) hP
      (LBIso.symm (X.symm c)) _ hs
    have H' : IsCorrForm (dp0 R) (𝟙 _) X.A X.A (X.P c) (-φ.flip) := by
      refine ⟨n, fun k ↦ -b k, a, ?_, fun x y ↦ ?_⟩
      · convert hs' using 1
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [Submodule.coe_neg, map_neg, map_neg, LinearMap.neg_apply]
        exact neg_eq_of_add_eq_zero_right (cup_add_cup _ _ _)
      · simp only [LinearMap.neg_apply, LinearMap.flip_apply, hφe, map_neg, neg_mul, Finset.sum_neg_distrib]
        exact congrArg Neg.neg (Finset.sum_congr rfl fun k _ ↦ mul_comm _ _)
    have hu := hφ.unique C hP H'
    intro x y
    have := LinearMap.congr_fun₂ hu y x
    simpa using this
  refine ⟨φ, hφ, ?_⟩
  obtain ⟨ψ, hψ, e⟩ := hφ.isPolForm
  obtain ⟨ψ', hψ', e'⟩ := hψ.pull (homMor (dp0 R) (𝟙 _) (lift (𝟙 X.A) (𝟙 X.A)))
  have h2 : (2 : R) • φ = ψ' := by
    refine LinearMap.ext₂ fun x y ↦ ?_
    rw [e' (push _ _ (lift (𝟙 X.A) (𝟙 X.A)) x) x (push _ _ (lift (𝟙 X.A) (𝟙 X.A)) y) y (fun _ ↦ rfl) (fun _ ↦ rfl),
      RingHom.id_apply, e, push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _),
      push_push _ _ _ (lift_fst _ _), push_push _ _ _ (lift_snd _ _), push_id, LinearMap.id_apply,
      LinearMap.id_apply, anti x y, LinearMap.smul_apply, LinearMap.smul_apply, two_smul]
    simp only [LinearMap.add_apply, sub_neg_eq_add]
  rw [h2]
  exact hψ'

end GlobalTheory.PolPairing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormExistsFreeDeRhamStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_form_exists_free_de_rham : GlobalTheory.Published.AbelianDeRham.Free → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt), ∃ ψ : LinearMap.BilinForm R (HdR X.A), IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ := by
  first | exact @GlobalTheory.DiagPolForm.diag_polForm_exists | exact GlobalTheory.DiagPolForm.diag_polForm_exists | (intros; apply GlobalTheory.DiagPolForm.diag_polForm_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolydiscCmUniformizationStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polydisc_cm_uniformization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (𝔞 𝔟 : FracId (FR E))
    (φ : I → E →+* ℂ) (c : Ideal (OF E)) (y : (Af E)ˣ), IsCMType φ → c ≠ ⊥ → ∀ s : ℕ, 1 ≤ s →
    ∀ z ∈ polydisc I, ∀ (ue : Fin (Module.finrank ℚ (FR E)) ≃ I) (e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ))
      (τ : (FR E →+* ℝ) → ℂ) (lam : Fin (Module.finrank ℚ (FR E)) → ℂ),
      (∀ j (x : FR E), (e j x : ℂ) = φ (ue j) (x : E)) → τ ∈ halfSpace (FR E) → (∀ j, lam j ≠ 0) →
      (∀ w : Fin (Module.finrank ℚ (FR E)) → ℂ, (∃ x ∈ lattice c y, w = fun j ↦ defCoord φ z x (ue j)) ↔
        ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt,
          w = fun j ↦ lam j * (2 * Real.pi * Complex.I * ((e j m : ℂ) + (e j β : ℂ) * τ (e j)))) →
      ∀ G, IsEis 𝔞 𝔟 (2 * s) G → ∀ g, IsDefSum φ (2 * s) (lattice c y) g →
        g z = (cWt E (2 * s) : ℂ) * ((∏ j, lam j)⁻¹) ^ (2 * s) * G τ := by
  first | exact @GlobalTheory.LatSumCmp.defSum_eq_eis | exact GlobalTheory.LatSumCmp.defSum_eq_eis | (intros; apply GlobalTheory.LatSumCmp.defSum_eq_eis <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfIsGrpPullbackOfInjectiveDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem pow_eq_one_of_isGrpPullback_of_injective : ∀ (Ω T : Type) [Field Ω] [CommRing T] [IsDomain T] (jT : T →+* Ω), Function.Injective jT → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → ∀ (x : baseOver (Sp Ω) ⟶ A.A) (y : baseOver (Sp T) ⟶ P.A) (k : ℕ), x.left ≫ φ = spMap jT ≫ y.left → x ^ k = 1 → y ^ k = 1 := by
  intro Ω T _ _ _ jT hj A P φ hφ x y k hxy hx
  let U : Over.mk ((baseOver (Sp Ω)).hom ≫ spMap jT) ⟶ baseOver (Sp T) := Over.homMk (spMap jT) (by simp)
  have e1 : pushHom hφ (baseOver (Sp Ω)) x = U ≫ y := Over.OverMorphism.ext hxy
  have e2 : U ≫ y ^ k = U ≫ 1 :=
    calc U ≫ y ^ k = preHom U (y ^ k) := rfl
      _ = (preHom U y) ^ k := map_pow _ _ _
      _ = (pushHom hφ (baseOver (Sp Ω)) x) ^ k := by rw [e1]; rfl
      _ = pushHom hφ (baseOver (Sp Ω)) (x ^ k) := (map_pow _ _ _).symm
      _ = 1 := by rw [hx, map_one]
      _ = preHom U 1 := (map_one _).symm
  have e3 : spMap jT ≫ (y ^ k).left = spMap jT ≫ (1 : baseOver (Sp T) ⟶ P.A).left :=
    congrArg (fun z => z.left) e2
  have : IsDominant (spMap jT) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical jT).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot jT).1 hj]; exact bot_le)⟩
  have := P.isAb.proper
  have : IsReduced (baseOver (Sp T)).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of T)))
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated P.A.hom
    ((Over.w (y ^ k)).trans (Over.w (1 : baseOver (Sp T) ⟶ P.A)).symm) (spMap jT) e3)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorCentreThroughImageStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeDivisorCentre_through_image : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s] (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ y : Y, E'.Through y → E.Through (s y) := by
  first | exact @GlobalTheory.Discrepancy.DivOver.Over.through_image | exact GlobalTheory.Discrepancy.DivOver.Over.through_image | (intros; apply GlobalTheory.Discrepancy.DivOver.Over.through_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeOfRingOnEqNonunitsAtPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Points RatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_of_ringOn_eq_nonunits_at_point : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), IsAffineOpen U → (U : Set M.Z).Nonempty → ∀ P : Ideal (M.ringOn (U : Set M.Z)), P.IsPrime → ∃ z ∈ U, ∀ a : M.ringOn (U : Set M.Z), a ∈ P ↔ ((a : Ω) = 0 ∨ (a : Ω)⁻¹ ∉ M.O z) := by
  first | exact @GlobalTheory.Poinc.prime_eq_nonunits_at_point | exact GlobalTheory.Poinc.prime_eq_nonunits_at_point | (intros; apply GlobalTheory.Poinc.prime_eq_nonunits_at_point <;> assumption)
end

