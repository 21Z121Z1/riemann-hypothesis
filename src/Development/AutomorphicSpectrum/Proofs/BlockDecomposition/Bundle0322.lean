import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0320
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0264
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0263
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0260
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.QcohLocal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdmissibleLinearFunctional
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0315
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfEig
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0317
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0181
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0316
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemRestrictionSubobject
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.ImageOpen

lemma secs_mk {X : Scheme.{0}} {E F : X.Modules} (m : F ⟶ E) [Mono m] (W : X.Opens) :
    secs (Subobject.mk m) W = Set.range (m.app W) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    refine ⟨(Subobject.underlyingIso m).hom.app W x, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Subobject.underlyingIso_hom_comp_eq_mk]
  · rintro _ ⟨x, rfl⟩
    refine ⟨(Subobject.underlyingIso m).inv.app W x, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Subobject.underlyingIso_arrow]

lemma isQuasicoherent_image {X : Scheme.{0}} {F E : X.Modules} [F.IsQuasicoherent]
    [E.IsQuasicoherent] (g : F ⟶ E) :
    ((Subobject.mk (kernel.ι (cokernel.π g)) : Subobject E) : X.Modules).IsQuasicoherent :=
  haveI := isQuasicoherent_kernel (cokernel.π g)
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Subobject.underlyingIso (kernel.ι (cokernel.π g))).symm inferInstance

lemma secs_image {X : Scheme.{0}} {F E : X.Modules} [F.IsQuasicoherent]
    [E.IsQuasicoherent] (g : F ⟶ E) (W : X.Opens) (hW : IsAffineOpen W) :
    secs (Subobject.mk (kernel.ι (cokernel.π g))) W = Set.range (g.app W) := by
  rw [secs_mk]
  haveI := isQuasicoherent_kernel (cokernel.π g)
  have hs : Function.Surjective ((Abelian.factorThruImage g).app W) :=
    GlobalTheory.QCoh.app_surjective_of_epi_of_isAffineOpen (Abelian.factorThruImage g) hW
  have h : ∀ y, (kernel.ι (cokernel.π g)).app W ((Abelian.factorThruImage g).app W y) =
      g.app W y := fun y => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app]
    exact congrArg (fun φ : F ⟶ E => φ.app W y) (Abelian.image.fac g)
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hs x
    exact ⟨y, (h y).symm⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨(Abelian.factorThruImage g).app W x, h x⟩

end GlobalTheory.CompanionTheory.GE.ImageOpen

namespace GlobalTheory.CompanionTheory.GE.ImageOpen

attribute [local instance] algebraOfOver

lemma toFunctions_open {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (O : X.Opens) :
    letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
    ∀ (U : (O : Scheme.{0}).Opens) (r : A),
      (O.ι.appIso U).hom (toFunctions (A := A) (O.ι ''ᵁ U) r) = toFunctions (A := A) U r := by
  intro U r
  change (O.ι.appIso U).hom (X.presheaf.map (homOfLE le_top).op
      ((X ↘ Spec (.of A)).appTop ((Scheme.ΓSpecIso (.of A)).inv r))) =
    (O : Scheme.{0}).presheaf.map (homOfLE le_top).op
      ((O.ι ≫ (X ↘ Spec (.of A))).appTop ((Scheme.ΓSpecIso (.of A)).inv r))
  rw [Scheme.Hom.comp_appTop]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  rfl

end GlobalTheory.CompanionTheory.GE.ImageOpen

namespace GlobalTheory.CompanionTheory.GE.ImageOpen

lemma map_mem_secs_powSub {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] (O : X.Opens) :
    letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
    ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, P.IsQuasicoherent → E.IsQuasicoherent →
      ∀ (f : P.restrict O.ι ⟶ E) (n : ℕ) (U : (O : Scheme.{0}).Opens), IsAffineOpen U →
      ∀ x : Γ(P, O.ι ''ᵁ U), x ∈ secs (powSub I P n) (O.ι ''ᵁ U) →
        f.app U ((P.restrictAppIso O.ι U).inv x) ∈ secs (powSub I E n) U := by
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
  intro P E hP hE f n U hU x hx
  have hU' : IsAffineOpen (O.ι ''ᵁ U) := hU.image_of_isOpenImmersion O.ι
  rw [secs_powSub I P hP n _ hU'] at hx
  rw [secs_powSub I E hE n U hU]
  have hmul : ∀ (a : Γ(X, O.ι ''ᵁ U)) (m : Γ(P, O.ι ''ᵁ U)),
      f.app U ((P.restrictAppIso O.ι U).inv (a • m)) =
        (O.ι.appIso U).hom a • f.app U ((P.restrictAppIso O.ι U).inv m) := by
    intro a m
    rw [Scheme.Modules.smul_restrictAppIso_inv_apply, Scheme.Modules.Hom.app_smul]
  have hJ : ∀ a ∈ Ideal.map (toFunctions (A := A) (O.ι ''ᵁ U)) (I ^ n),
      (O.ι.appIso U).hom a ∈ Ideal.map (toFunctions (A := A) U) (I ^ n) := by
    intro a ha
    have := Ideal.mem_map_of_mem (O.ι.appIso U).hom.hom ha
    rw [Ideal.map_map] at this
    convert this using 2
    ext r
    exact (toFunctions_open O U r).symm
  change x ∈ (Ideal.map (toFunctions (A := A) (O.ι ''ᵁ U)) (I ^ n) • ⊤ :
    Submodule Γ(X, O.ι ''ᵁ U) Γ(P, O.ι ''ᵁ U)) at hx
  refine Submodule.smul_induction_on
    (p := fun x => f.app U ((P.restrictAppIso O.ι U).inv x) ∈
      (Ideal.map (toFunctions (A := A) U) (I ^ n) • ⊤ : Submodule Γ((O : Scheme.{0}), U) Γ(E, U)))
    hx ?_ ?_
  · intro a ha m _
    show _ ∈ _
    rw [hmul]
    exact Submodule.smul_mem_smul (hJ a ha) Submodule.mem_top
  · intro y z hy hz
    show _ ∈ _
    rw [map_add, map_add]
    exact Submodule.add_mem _ hy hz

end GlobalTheory.CompanionTheory.GE.ImageOpen

namespace GlobalTheory.CompanionTheory.GE.ImageOpen

lemma isQuasicoherent_powSub {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {Y : Scheme.{0}} [Y.Over (Spec (.of A))] (M : Y.Modules) [M.IsQuasicoherent] (n : ℕ) :
    ((powSub I M (n + 1) : Subobject M) : Y.Modules).IsQuasicoherent :=
  (closedSys_pow I M).qcoh n

theorem image_on_open : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (O : X.Opens), letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩; ∀ {P : X.Modules} {E : (O : Scheme.{0}).Modules}, IsCoherent P → IsCoherent E → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ S : ℕ → Subobject E, ClosedSys I E S → ∀ Sb : ℕ → Subobject P, (∀ e (W : (O : Scheme.{0}).Opens), IsAffineOpen W → ∀ x : Γ(P, O.ι ''ᵁ W), x ∈ secs (Sb e) (O.ι ''ᵁ W) ↔ f.app W ((P.restrictAppIso O.ι W).inv x) ∈ secs (S e) W) → ∀ Bb : Subobject P, (Bb : X.Modules).IsQuasicoherent → (∀ e, Bb ⊔ powSub I P (e + 1) = Sb e) → ∃ B : Subobject E, (B : (O : Scheme.{0}).Modules).IsQuasicoherent ∧ (∀ e, B ⊔ powSub I E (e + 1) = S e) ∧ ∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W = (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W) := by
  intro A _ _ I X _ _ O
  letI : (O : Scheme.{0}).Over (Spec (.of A)) := ⟨O.ι ≫ (X ↘ Spec (.of A))⟩
  intro P E hP hE f hf S hS Sb hSb Bb hBb hBS
  haveI := hP.1
  haveI := hE.1
  haveI : (Bb : X.Modules).IsQuasicoherent := hBb
  haveI : Epi f := hf
  haveI : ((Bb : X.Modules).restrict O.ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  haveI : (P.restrict O.ι).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor _ _
  let g : (Bb : X.Modules).restrict O.ι ⟶ E := (Scheme.Modules.restrictFunctor O.ι).map Bb.arrow ≫ f
  let B : Subobject E := Subobject.mk (kernel.ι (cokernel.π g))
  have hBq : (B : (O : Scheme.{0}).Modules).IsQuasicoherent := isQuasicoherent_image g
  have hsecs : ∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W =
      (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W) := by
    intro W hW
    rw [secs_image g W hW]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨Bb.arrow.app _ z, ⟨z, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
  refine ⟨B, hBq, fun e => ?_, hsecs⟩
  have hBle : Bb ≤ Sb e := hBS e ▸ le_sup_left
  apply le_antisymm
  · refine sup_le ?_ (hS.pow_le e)
    rw [le_iff_secs_subset]
    rintro ⟨W, hW⟩ y hy
    rw [hsecs W hW] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' : x ∈ secs (Sb e) (O.ι ''ᵁ W) :=
      (le_iff_secs_subset _ _).1 hBle ⟨_, hW.image_of_isOpenImmersion O.ι⟩ hx
    exact (hSb e W hW x).1 hx'
  · rw [le_iff_secs_subset]
    rintro ⟨W, hW⟩ y hy
    change y ∈ secs (S e) W at hy
    change y ∈ secs (B ⊔ powSub I E (e + 1)) W
    have hW' : IsAffineOpen (O.ι ''ᵁ W) := hW.image_of_isOpenImmersion O.ι
    rw [(supsecs hE.1 B (powSub I E (e + 1)) hBq (isQuasicoherent_powSub I E e)).2 W hW]
    obtain ⟨z, rfl⟩ := GlobalTheory.QCoh.app_surjective_of_epi_of_isAffineOpen f hW y
    have hx : (P.restrictAppIso O.ι W).hom z ∈ secs (Sb e) (O.ι ''ᵁ W) := (hSb e W hW _).2 hy
    rw [← hBS e, (supsecs hP.1 Bb (powSub I P (e + 1)) hBb (isQuasicoherent_powSub I P e)).2 _ hW']
      at hx
    obtain ⟨s, hs, t, ht, hst⟩ := hx
    refine ⟨f.app W ((P.restrictAppIso O.ι W).inv s), (hsecs W hW).symm ▸ ⟨s, hs, rfl⟩,
      f.app W ((P.restrictAppIso O.ι W).inv t),
      map_mem_secs_powSub I O hP.1 hE.1 f (e + 1) W hW t ht, ?_⟩
    rw [← map_add, ← map_add, ← hst]
    rfl

end GlobalTheory.CompanionTheory.GE.ImageOpen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
section
noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.LocVan

variable {n : ℕ}

abbrev thC (n : ℕ) : Monoid.End (GL (Fin n) ℂ) := thetaR (starRingEnd ℂ) n

theorem nil_sq_mul {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ nilrad W₁ W₂) : X * X * X = 0 := by
  have h : ∀ y, (X * X * X) *ᵥ y = 0 := fun y => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hX.2.2 _ (hX.2.1 _ (hX.1 y))
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa using this

def uOf {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (X : nilrad W₁ W₂) : GL (Fin n) ℂ where
  val := 1 + X.1
  inv := 1 - X.1 + X.1 * X.1
  val_inv := by
    have h := nil_sq_mul X.2
    noncomm_ring
    rw [← mul_assoc, h]; simp
  inv_val := by
    have h := nil_sq_mul X.2
    noncomm_ring
    rw [← mul_assoc, h]; simp

@[simp] theorem uOf_val {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (X : nilrad W₁ W₂) :
    (uOf X).val = 1 + X.1 := rfl

theorem continuous_uOf {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} :
    Continuous (uOf : nilrad W₁ W₂ → GL (Fin n) ℂ) := by
  have h : Continuous fun X : nilrad W₁ W₂ => X.1 := continuous_subtype_val
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add h
  · have : Continuous fun X : nilrad W₁ W₂ => (1 - X.1 + X.1 * X.1 : Matrix (Fin n) (Fin n) ℂ) :=
      (continuous_const.sub h).add (h.matrix_mul h)
    exact this

def NilChange : Prop := ∀ (n : ℕ) (d : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)),
  (d * thC n d).val.charpoly.Separable → W₁ ≠ ⊥ → W₁ ≤ W₂ →
  perpD (starRingEnd ℂ) d W₁ = W₂ → perpD (starRingEnd ℂ) d W₂ = W₁ →
  ∃ Φ : nilrad W₁ W₂ → nilrad W₁ W₂, Continuous Φ ∧
    (∀ X, uOf (Φ X) = (uOf X)⁻¹ * (d * thC n (uOf X) * d⁻¹)) ∧
    ∀ [MeasurableSpace (nilrad W₁ W₂)] [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂))
      [ν.IsAddHaarMeasure], ∃ c : NNReal, ν.map Φ = (c : ENNReal) • ν

def QuotVanish : Prop := ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
  (μ : Measure (GL (Fin n) ℂ)) [μ.IsHaarMeasure] (d : GL (Fin n) ℂ)
  (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] (W₁ W₂ : Submodule ℂ (Fin n → ℂ)),
  (d * thC n d).val.charpoly.Separable → W₁ ≠ ⊥ → W₁ ≤ W₂ →
  perpD (starRingEnd ℂ) d W₁ = W₂ → perpD (starRingEnd ℂ) d W₂ = W₁ →
  ∀ F : GL (Fin n) ℂ → ℂ, Measurable F → (∀ t ∈ twCent (thC n) d, ∀ x, F (t * x) = F x) →
    (∀ x k, thC n k = k → F (x * k) = F x) →
    (∀ [MeasurableSpace (nilrad W₁ W₂)] [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂))
      [ν.IsAddHaarMeasure] (q : GL (Fin n) ℂ), ∫ X, F (uOf X * q) ∂ν = 0) →
    quotIntegral μ (twCent (thC n) d) μd F = 0

theorem mem_img' (g : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    y ∈ img g W ↔ (g⁻¹ : GL (Fin n) ℂ).val *ᵥ y ∈ W := by
  have e1 : ∀ z : Fin n → ℂ, (g⁻¹ : GL (Fin n) ℂ).val *ᵥ (g.val *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul]; simp
  have e2 : ∀ z : Fin n → ℂ, g.val *ᵥ ((g⁻¹ : GL (Fin n) ℂ).val *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul]; simp
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Matrix.toLin'_apply, e1]; exact hx
  · intro h
    exact ⟨_, h, by rw [Matrix.toLin'_apply, e2]⟩

theorem img_mul (a b : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    img (a * b) W = img a (img b W) := by
  ext y
  simp only [mem_img', _root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

theorem img_one (W : Submodule ℂ (Fin n → ℂ)) : img (1 : GL (Fin n) ℂ) W = W := by
  ext y
  simp [mem_img']

theorem thC_val (q : GL (Fin n) ℂ) : (thC n q).val = (q⁻¹ : GL (Fin n) ℂ).valᴴ := by
  rw [thC, thetaR_val]; ext i j; simp [Matrix.conjTranspose_apply]

theorem mem_perp' (W : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    y ∈ perp (starRingEnd ℂ) W ↔ ∀ x ∈ W, star x ⬝ᵥ y = 0 := Iff.rfl

theorem perp_img (q : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    perp (starRingEnd ℂ) (img q W) = img (thC n q) (perp (starRingEnd ℂ) W) := by
  have hi : ((thC n q)⁻¹ : GL (Fin n) ℂ).val = q.valᴴ := by
    rw [← map_inv, thC_val, inv_inv]
  ext y
  rw [mem_img', mem_perp', mem_perp', hi]
  constructor
  · intro h x hx
    have := h (q.val *ᵥ x) ⟨x, hx, by rw [Matrix.toLin'_apply]⟩
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec] at this
    exact this
  · rintro h _ ⟨x, hx, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
    exact h x hx

theorem perpD_twConj (d q : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    perpD (starRingEnd ℂ) (twConj (thC n) q d) (img q⁻¹ W) =
      img q⁻¹ (perpD (starRingEnd ℂ) d W) := by
  rw [perpD, perpD, perp_img, ← img_mul, twConj, map_inv]
  simp only [mul_assoc, mul_inv_cancel, mul_one]
  rw [img_mul]

theorem img_le_img (g : GL (Fin n) ℂ) {W W' : Submodule ℂ (Fin n → ℂ)} (h : W ≤ W') :
    img g W ≤ img g W' := Submodule.map_mono h

theorem img_ne_bot (g : GL (Fin n) ℂ) {W : Submodule ℂ (Fin n → ℂ)} (h : W ≠ ⊥) : img g W ≠ ⊥ := by
  intro h0
  apply h
  have : img g⁻¹ (img g W) = W := by rw [← img_mul, inv_mul_cancel, img_one]
  rw [← this, h0]
  exact Submodule.map_bot _

theorem conj_mem (p : GL (Fin n) ℂ) {W₁ W₂ : Submodule ℂ (Fin n → ℂ)}
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ nilrad W₁ W₂) :
    p.val * X * (p⁻¹ : GL (Fin n) ℂ).val ∈ nilrad (img p W₁) (img p W₂) := by
  have hpp : ∀ y : Fin n → ℂ, (p⁻¹ : GL (Fin n) ℂ).val *ᵥ (p.val *ᵥ y) = y := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul]; simp
  have e : ∀ y : Fin n → ℂ, (p.val * X * (p⁻¹ : GL (Fin n) ℂ).val) *ᵥ y =
      p.val *ᵥ (X *ᵥ ((p⁻¹ : GL (Fin n) ℂ).val *ᵥ y)) := fun y => by
    simp only [Matrix.mulVec_mulVec, mul_assoc]
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · rw [e, mem_img', hpp]
    exact hX.1 _
  · rw [mem_img'] at hy
    rw [e, mem_img', hpp]
    exact hX.2.1 _ hy
  · rw [mem_img'] at hy
    rw [e, hX.2.2 _ hy, Matrix.mulVec_zero]

theorem img_inv_img (q : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) : img q (img q⁻¹ W) = W := by
  rw [← img_mul, mul_inv_cancel, img_one]

def cnF (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    nilrad (img q⁻¹ W₁) (img q⁻¹ W₂) := ⟨(q⁻¹ : GL (Fin n) ℂ).val * X.1 * q.val, by
    have := conj_mem q⁻¹ X.2
    rwa [inv_inv] at this⟩

def cnB (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (Z : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) :
    nilrad W₁ W₂ := ⟨q.val * Z.1 * (q⁻¹ : GL (Fin n) ℂ).val, by
    have := conj_mem q Z.2
    rwa [img_inv_img, img_inv_img] at this⟩

theorem cnF_val (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    (cnF q W₁ W₂ X).1 = (q⁻¹ : GL (Fin n) ℂ).val * X.1 * q.val := rfl

theorem cnB_val (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    (Z : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) :
    (cnB q W₁ W₂ Z).1 = q.val * Z.1 * (q⁻¹ : GL (Fin n) ℂ).val := rfl

theorem cnF_add (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X Y : nilrad W₁ W₂) :
    cnF q W₁ W₂ (X + Y) = cnF q W₁ W₂ X + cnF q W₁ W₂ Y :=
  Subtype.ext (by
    simp only [Submodule.coe_add, cnF_val, mul_add, add_mul])

theorem cnB_add (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    (X Y : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) :
    cnB q W₁ W₂ (X + Y) = cnB q W₁ W₂ X + cnB q W₁ W₂ Y :=
  Subtype.ext (by
    simp only [Submodule.coe_add, cnB_val, mul_add, add_mul])

theorem cnB_cnF (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    cnB q W₁ W₂ (cnF q W₁ W₂ X) = X :=
  Subtype.ext (by
    have h1 : q.val * (q⁻¹ : GL (Fin n) ℂ).val = 1 := by rw [← Units.val_mul]; simp
    rw [cnB_val, cnF_val]
    calc _ = (q.val * (q⁻¹ : GL (Fin n) ℂ).val) * X.1 * (q.val * (q⁻¹ : GL (Fin n) ℂ).val) := by
          simp only [mul_assoc]
      _ = X.1 := by rw [h1]; simp)

theorem cnF_cnB (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    (Z : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) : cnF q W₁ W₂ (cnB q W₁ W₂ Z) = Z :=
  Subtype.ext (by
    have h1 : (q⁻¹ : GL (Fin n) ℂ).val * q.val = 1 := by rw [← Units.val_mul]; simp
    rw [cnF_val, cnB_val]
    calc _ = ((q⁻¹ : GL (Fin n) ℂ).val * q.val) * Z.1 * ((q⁻¹ : GL (Fin n) ℂ).val * q.val) := by
          simp only [mul_assoc]
      _ = Z.1 := by rw [h1]; simp)

def conjNil (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    nilrad W₁ W₂ ≃+ nilrad (img q⁻¹ W₁) (img q⁻¹ W₂) :=
  AddMonoidHom.toAddEquiv (AddMonoidHom.mk' (cnF q W₁ W₂) (cnF_add q W₁ W₂))
    (AddMonoidHom.mk' (cnB q W₁ W₂) (cnB_add q W₁ W₂))
    (AddMonoidHom.ext fun X => cnB_cnF q W₁ W₂ X) (AddMonoidHom.ext fun Z => cnF_cnB q W₁ W₂ Z)
theorem conjNil_val (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    (conjNil q W₁ W₂ X).1 = (q⁻¹ : GL (Fin n) ℂ).val * X.1 * q.val := rfl

theorem continuous_conjNil (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    Continuous (conjNil q W₁ W₂) :=
  Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _

theorem continuous_conjNil_symm (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    Continuous (conjNil q W₁ W₂).symm :=
  Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _

theorem uOf_conjNil (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    uOf (conjNil q W₁ W₂ X) = q⁻¹ * uOf X * q := by
  apply Units.ext
  have h1 : (q⁻¹ : GL (Fin n) ℂ).val * q.val = 1 := by rw [← Units.val_mul]; simp
  simp only [uOf_val, conjNil_val, Units.val_mul, mul_add, add_mul, mul_one, h1]

theorem continuous_thC : Continuous (thC n) := by
  have hv : ∀ h : Continuous fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ),
      Continuous fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ) := id
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : Continuous fun g : GL (Fin n) ℂ => (g⁻¹ : GL (Fin n) ℂ).valᴴ :=
      (Units.continuous_val.comp continuous_inv).matrix_conjTranspose
    exact this.congr fun g => (thC_val g).symm
  · have : Continuous fun g : GL (Fin n) ℂ => (g : GL (Fin n) ℂ).valᴴ :=
      Units.continuous_val.matrix_conjTranspose
    refine this.congr fun g => ?_
    have : (((thC n g)⁻¹ : GL (Fin n) ℂ)).val = g.valᴴ := by
      rw [← map_inv, thC_val, inv_inv]
    exact this.symm

end GlobalTheory.CompanionTheory.LocVan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdmissibleLinearFunctionalStatement
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_linear_functional : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ w : ℂ, w ≠ 0 → ‖w‖ * (q : ℝ) ^ 2 < 1 →
    ∃ I : (L → ℂ) → ℂ,
      (∀ F G : L → ℂ, IsAdm w F → IsAdm w G → I (F + G) = I F + I G) ∧
      (∀ (c : ℂ) (F : L → ℂ), IsAdm w F → I (c • F) = c * I F) ∧
      (∀ (F : L → ℂ) (y : L), IsAdm w F → IsAdm w (fun x => F (x + y)) ∧ I (fun x => F (x + y)) = I F) ∧
      (∀ (F : L → ℂ) (c : L), IsAdm w F → c ≠ 0 →
        IsAdm w (fun x => F (c * x)) ∧ I (fun x => F (c * x)) = (q : ℂ) ^ (2 * ordL c) * I F) ∧
      IsAdm w (sphFn (L := L) w) ∧ I (sphFn w) = (1 - w) / (1 - w * (q : ℂ) ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.SwapInt.exists_invariant_integral | exact GlobalTheory.CompanionTheory.SwapInt.exists_invariant_integral | (intros; apply GlobalTheory.CompanionTheory.SwapInt.exists_invariant_integral <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthCoinvariantsSwapStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_length_coinvariants_swap : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ χ : kˣ →* ℂˣ), HasFiniteLength (coinv (omega b a μ⁻¹) (detChar b χ⁻¹)) → HasFiniteLength (coinv ((omega a b μ⁻¹).comp (MulEquiv.prodComm (M := GL b k) (N := GL a k)).toMonoidHom) (detChar b χ)) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaGLLen.Swap.coinv_swap_finiteLength | exact GlobalTheory.CompanionTheory.ThetaGLLen.Swap.coinv_swap_finiteLength | (intros; apply GlobalTheory.CompanionTheory.ThetaGLLen.Swap.coinv_swap_finiteLength <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSubquotientsStatement
section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_subquotients : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], FinSubq F ι := by
  first | exact @GlobalTheory.CompanionTheory.RepFinSubq.finSubq | exact GlobalTheory.CompanionTheory.RepFinSubq.finSubq | (intros; apply GlobalTheory.CompanionTheory.RepFinSubq.finSubq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FontaineLatticeDpowClosed
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCHc

theorem subsingleton_Bk_zero (l : ℕ) [Fact l.Prime] : Subsingleton (Lat.Bk l 0) := by
  refine Ideal.Quotient.subsingleton_iff.2 ?_
  rw [pow_zero, Ideal.span_singleton_one]

theorem hc_k : ∀ (l : ℕ) [Fact l.Prime] (M k : ℕ),
    Lat.DPClosed (Lat.ι (Lat.fk l k) (xi0 l) l M) (Lat.γB (Lat.fk l k) (xi0 l)) := by
  intro l _ M k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · intro x _ n
    haveI := subsingleton_Bk_zero l
    exact ⟨0, Subsingleton.elim _ _⟩
  · exact GlobalTheory.CompanionTheory.LatDP.dpClosed _ _ l M k (GlobalTheory.CompanionTheory.LatCHyp.hyp_k l k hk)

end GlobalTheory.CompanionTheory.LatCHc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesLatticeSubStatement
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_preserves_lattice_sub : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M k : ℕ) (g : K.fixingSubgroup) (hT : Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (Lat.gP l g)), ∀ x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M, Ideal.quotientMap _ (Lat.gP l g) hT x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  first | exact @GlobalTheory.CompanionTheory.LatGal.gal_mem_sub | exact GlobalTheory.CompanionTheory.LatGal.gal_mem_sub | (intros; apply GlobalTheory.CompanionTheory.LatGal.gal_mem_sub <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisPreservesTPowerSpanStatement
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_preserves_t_power_span : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (k : ℕ) (g : K.fixingSubgroup), Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (Lat.gP l g) := by
  first | exact @GlobalTheory.CompanionTheory.LatGal.span_tBdR_pow_le_comap | exact GlobalTheory.CompanionTheory.LatGal.span_tBdR_pow_le_comap | (intros; apply GlobalTheory.CompanionTheory.LatGal.span_tBdR_pow_le_comap <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearGroupUnimodularStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.general_linear_group_unimodular : PositivityTheory.RgBcC.Unimod := by
  first | exact @GlobalTheory.CompanionTheory.GLUnimod.unimod | exact GlobalTheory.CompanionTheory.GLUnimod.unimod | (intros; apply GlobalTheory.CompanionTheory.GLUnimod.unimod <;> assumption)
end

