import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2440
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCohomologyIsoPresentedCrystal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2379
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2351

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartSmoothLiftSqZero
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBLift

open MvPolynomial in

theorem standardSmoothRelDim_lift_of_sqZero {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0)
    (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (B₀ : Type) [CommRing B₀]
    [Algebra R₀ B₀] (hB₀ : Algebra.IsStandardSmoothOfRelativeDimension g R₀ B₀) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀),
      (∀ r, p (algebraMap R B r) = algebraMap R₀ B₀ (π r)) ∧ Function.Surjective p ∧
      (∀ b, p b = 0 → b ∈ I.map (algebraMap R B)) ∧ Algebra.IsStandardSmoothOfRelativeDimension g R B := by
  obtain ⟨κ, τ, _, _, P, hP⟩ := hB₀.out
  classical
  have : Fintype τ := Fintype.ofFinite τ
  have hmap : Function.Surjective (MvPolynomial.map (σ := κ) π) := MvPolynomial.map_surjective π hπ
  let v : τ → MvPolynomial κ R := fun j => Function.surjInv hmap (P.relation j)
  have hv : ∀ j, MvPolynomial.map π (v j) = P.relation j := fun j => Function.surjInv_eq hmap _
  let J : Ideal (MvPolynomial κ R) := Ideal.span (Set.range v)
  let φ : MvPolynomial κ R →+* B₀ := (aeval P.val).toRingHom.comp (MvPolynomial.map π)
  have hφ : ∀ f, φ f = aeval P.val (MvPolynomial.map π f) := fun _ => rfl
  have hJ : J ≤ RingHom.ker φ := by
    rw [Ideal.span_le]; rintro _ ⟨j, rfl⟩
    simp [RingHom.mem_ker, hφ, hv, Algebra.Presentation.aeval_val_relation]
  let p : (MvPolynomial κ R ⧸ J) →+* B₀ := Ideal.Quotient.lift J φ hJ
  have hp : ∀ f, p (Ideal.Quotient.mk J f) = φ f := fun _ => rfl
  have halg : ∀ r : R, p (algebraMap R _ r) = algebraMap R₀ B₀ (π r) := by
    intro r
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial κ R) (MvPolynomial κ R ⧸ J)]
    simp [Ideal.Quotient.algebraMap_eq, hp, hφ]
  have hsurj : Function.Surjective p := by
    intro b
    obtain ⟨g, rfl⟩ := P.aeval_val_surjective b
    obtain ⟨f, rfl⟩ := hmap g
    exact ⟨Ideal.Quotient.mk J f, rfl⟩
  have hker : ∀ b, p b = 0 → b ∈ I.map (algebraMap R (MvPolynomial κ R ⧸ J)) := by
    intro b
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
    intro h0
    rw [hp, hφ] at h0
    have hmem : MvPolynomial.map π f ∈ Ideal.span (Set.range P.relation) := by
      rw [P.span_range_relation_eq_ker]
      first
        | exact h0
        | exact RingHom.mem_ker.mpr h0
        | (rw [Algebra.Generators.ker_eq_ker_aeval_val]; exact h0)
    obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hmem
    let c' : τ → MvPolynomial κ R := fun j => Function.surjInv hmap (c j)
    have hc' : ∀ j, MvPolynomial.map π (c' j) = c j := fun j => Function.surjInv_eq hmap _
    have hg : f - ∑ j, c' j * v j ∈ RingHom.ker (MvPolynomial.map (σ := κ) π) := by
      rw [RingHom.mem_ker, map_sub, map_sum, ← hc]
      simp [hc', hv]
    rw [MvPolynomial.ker_map, hk] at hg
    have hs : ∑ j, c' j * v j ∈ J :=
      Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    have : Ideal.Quotient.mk J f = Ideal.Quotient.mk J (f - ∑ j, c' j * v j) := by
      rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.2 hs, sub_zero]
    rw [this]
    have hmm := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hg
    rwa [Ideal.map_map] at hmm
  let Q := Algebra.PreSubmersivePresentation.naive (v := v) P.map P.map_inj
  have hjac : p Q.jacobian = P.jacobian := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    have h1 : ∀ f : MvPolynomial κ R, algebraMap Q.Ring (MvPolynomial κ R ⧸ Ideal.span (Set.range v)) f =
        Ideal.Quotient.mk J f := fun _ => rfl
    rw [h1, hp, hφ, Algebra.Generators.algebraMap_apply]
    congr 1
    rw [RingHom.map_det]
    refine congrArg Matrix.det (Matrix.ext fun i j => ?_)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    show MvPolynomial.map π (pderiv (P.map i) (v j)) = pderiv (P.map i) (P.relation j)
    rw [mvPolynomial_map_pderiv_lift, hv]
  have hunit : IsUnit Q.jacobian := by
    refine isUnit_of_isUnit_map_of_sqZero_ker p hsurj (I.map (algebraMap R _)) ?_ hker _
      (by rw [hjac]; exact P.jacobian_isUnit)
    rw [← Ideal.map_pow, hI]; simp
  let Q' : Algebra.SubmersivePresentation R (MvPolynomial κ R ⧸ J) κ τ :=
    { Q with jacobian_isUnit := hunit }
  have hdim : Q'.dimension = g := hP
  exact ⟨_, inferInstance, inferInstance, p, halg, hsurj, hker, Q'.isStandardSmoothOfRelativeDimension hdim⟩

theorem isPushout_of_surjective {R C C₀ : Type} [CommRing R] [CommRing C] [CommRing C₀] (J : Ideal R)
    [Algebra (R ⧸ J) C₀] (σ : R →+* C) (p : C →+* C₀) (hp : Function.Surjective p)
    (hσ : ∀ r, p (σ r) = algebraMap (R ⧸ J) C₀ (Ideal.Quotient.mk J r))
    (hker : ∀ c, p c = 0 → c ∈ J.map σ) :
    IsPushout (CommRingCat.ofHom σ) (CommRingCat.ofHom (Ideal.Quotient.mk J)) (CommRingCat.ofHom p)
      (CommRingCat.ofHom (algebraMap (R ⧸ J) C₀)) := by
  have hinv : Function.RightInverse (Function.surjInv hp) p := Function.surjInv_eq hp
  have hle : ∀ (T : CommRingCat.{0}) (u : C →+* T) (w : R ⧸ J →+* T),
      (∀ a, u (σ a) = w (Ideal.Quotient.mk J a)) → RingHom.ker p ≤ RingHom.ker u := by
    intro T u w huw c hc
    have h : J.map σ ≤ RingHom.ker u := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker, huw, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
    exact h (hker c hc)
  have hcond : ∀ (s : PushoutCocone (CommRingCat.ofHom σ) (CommRingCat.ofHom (Ideal.Quotient.mk J))) (a : R),
      s.inl.hom (σ a) = s.inr.hom (Ideal.Quotient.mk J a) := fun s a => congr($(s.condition) a)
  refine ⟨⟨by ext a; exact hσ a⟩, ⟨PushoutCocone.IsColimit.mk _
    (fun s => CommRingCat.ofHom (p.liftOfRightInverse _ hinv ⟨s.inl.hom, hle _ _ _ (hcond s)⟩)) ?_ ?_ ?_⟩⟩
  · intro s; ext c
    exact p.liftOfRightInverse_comp_apply _ hinv _ c
  · intro s; ext a
    show p.liftOfRightInverse _ hinv _ (algebraMap (R ⧸ J) C₀ (Ideal.Quotient.mk J a)) = _
    rw [← hσ, p.liftOfRightInverse_comp_apply]
    exact hcond s a
  · intro s m h₁ _
    ext b
    obtain ⟨c, rfl⟩ := hp b
    have e : m.hom (p c) = s.inl.hom c := congr($h₁ c)
    rw [e]
    exact (p.liftOfRightInverse_comp_apply _ hinv ⟨s.inl.hom, hle _ _ _ (hcond s)⟩ c).symm

theorem exists_chart_lift : ∀ (R : Type) [CommRing R] (J : Ideal R), J ^ 2 = ⊥ → ∀ (g : ℕ) (B : Over (Sp R))
    (b : B ⟶ Over.mk (spMap (Ideal.Quotient.mk J))), SmoothOfRelativeDimension g b.left → ∀ x : B.left,
    ∃ (C : Type) (_ : CommRing C) (σ : R →+* C)
      (j : Over.mk (spMap σ) ⊗ Over.mk (spMap (Ideal.Quotient.mk J)) ⟶ B),
      SmoothOfRelativeDimension g (spMap σ) ∧ j ≫ b = snd _ _ ∧ IsOpenImmersion j.left ∧
        x ∈ Set.range j.left := by
  intro R _ J hJ g B b hsm x
  let s₀ : B.left ⟶ Sp (R ⧸ J) := b.left
  have hsm₀ : SmoothOfRelativeDimension g s₀ := hsm
  obtain ⟨U₂, hU₂, V₂, hV₂, hx₂, e₂, h₂⟩ := hsm₀.exists_isStandardSmoothOfRelativeDimension x
  obtain ⟨r, s, hxs, e, hf⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway g).2
    (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves g).away x
    ⟨⊤, isAffineOpen_top _⟩ ⟨U₂, hU₂⟩ ⟨V₂, hV₂⟩ ⟨V₂, hV₂⟩ hx₂ hx₂ e₂ h₂ trivial
  let V : B.left.affineOpens := ⟨B.left.basicOpen s, hV₂.basicOpen s⟩
  have hle : V.1 ≤ s₀ ⁻¹ᵁ ⊤ := le_top
  have htop : RingHom.IsStandardSmoothOfRelativeDimension g (s₀.appLE ⊤ V.1 hle).hom := by
    have : IsLocalization.Away r Γ(Sp (R ⧸ J), (Sp (R ⧸ J)).basicOpen r) :=
      (isAffineOpen_top _).isLocalization_basicOpen r
    have heq : s₀.appLE ⊤ V.1 hle = CommRingCat.ofHom (algebraMap Γ(Sp (R ⧸ J), ⊤)
        Γ(Sp (R ⧸ J), (Sp (R ⧸ J)).basicOpen r)) ≫ s₀.appLE _ _ e := by
      rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Scheme.Hom.map_appLE]
    rw [heq]
    exact (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway g).1 _ r _ hf
  have hC₀ : Algebra.IsStandardSmoothOfRelativeDimension g (R ⧸ J) (Sec s₀ V.1) := by
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ J))).symm.commRingCatIsoToRingEquiv htop
  obtain ⟨C, _, _, p, hpσ, hp, hker, hC⟩ := standardSmoothRelDim_lift_of_sqZero J (by rw [hJ]; rfl)
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.mk_ker) g (Sec s₀ V.1) hC₀
  let σ : R →+* C := algebraMap R C
  have hpo := isPushout_of_surjective J σ p hp hpσ hker
  have H1 := isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  let A : Over (Sp R) := Over.mk (spMap σ)
  let A' : Over (Sp R) := Over.mk (spMap (Ideal.Quotient.mk J))
  have H0 : IsPullback (fst A A').left (snd A A').left A.hom A'.hom := IsPullback.of_hasPullback _ _
  let k := H0.isoIsPullback _ _ H1
  have hk₂ : k.hom ≫ spMap (algebraMap (R ⧸ J) (Sec s₀ V.1)) = (snd A A').left :=
    H0.isoIsPullback_hom_snd _ _ H1
  have hw : (k.hom ≫ affPt s₀ V) ≫ B.hom = (A ⊗ A').hom := by
    rw [← Over.w b, ← Over.w (snd A A'), ← hk₂]
    simp only [Category.assoc]
    rw [← Category.assoc (affPt s₀ V), affPt_w]
  let j : A ⊗ A' ⟶ B := Over.homMk (k.hom ≫ affPt s₀ V) hw
  have hjl : j.left = k.hom ≫ affPt s₀ V := rfl
  refine ⟨C, inferInstance, σ, j, ?_, ?_, ?_, ?_⟩
  · exact HasRingHomProperty.Spec_iff.2 (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap g).2 hC))
  · ext1
    rw [Over.comp_left, hjl, Category.assoc]
    exact (congrArg (k.hom ≫ ·) (affPt_w s₀ V)).trans hk₂
  · rw [hjl]; infer_instance
  · have hxV : x ∈ Set.range (affPt s₀ V) := by rw [GlobalTheory.LiftSys.Coh.range_affPt]; exact hxs
    obtain ⟨z, hz⟩ := hxV
    refine ⟨k.inv z, ?_⟩
    rw [hjl, ← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc, hz]

end GlobalTheory.LBLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertFrameOfLineBundleIso
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

namespace GlobalTheory.TransportFrame

open ReciprocityTheory.ChartRestriction.G.TB.ValAt

variable {X : Scheme.{0}}

theorem pspec_eq (p q : PrimeSpectrum ℂ) : p = q :=
  PrimeSpectrum.ext ((Ideal.eq_bot_of_prime p.asIdeal).trans (Ideal.eq_bot_of_prime q.asIdeal).symm)

theorem chart_pt (L : LB X) (hL : L.IsLB) (y : Sp ℂ ⟶ X) : ∃ j, ⊤ ≤ y ⁻¹ᵁ L.U j := by
  let p0 : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  have hmem : y p0 ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  refine ⟨j, fun q _ => ?_⟩
  have : q = p0 := pspec_eq q p0
  rw [this]
  exact hj

theorem val_res_unit (x : Sp ℂ ⟶ X) {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)ˣ) :
    valAt' x V (res hVU a : Γ(X, V)) = valAt' x U (a : Γ(X, U)) :=
  ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_res x hVU h (a : Γ(X, U))

theorem val_inv_unit (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    valAt' x U ((a⁻¹ : Γ(X, U)ˣ) : Γ(X, U)) = (valAt' x U (a : Γ(X, U)))⁻¹ :=
  map_units_inv (valHom x U h) a

theorem val_unit_ne (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    valAt' x U (a : Γ(X, U)) ≠ 0 :=
  (a.isUnit.map (valHom x U h)).ne_zero

theorem val_gen {L L' : LB X} (w : LB.Iso L' L) (hw : w.IsGen) (x : Sp ℂ ⟶ X) (i i₂ : L.ι) (j j₂ : L'.ι)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L'.U j)) (h₂ : ⊤ ≤ x ⁻¹ᵁ (L.U i₂ ⊓ L'.U j₂)) :
    valAt' x (L.U i ⊓ L'.U j) (w.s (i, j)).val =
      valAt' x (L.U i ⊓ L.U i₂) (L.g i i₂).val * (valAt' x (L'.U j ⊓ L'.U j₂) (L'.g j j₂).val)⁻¹ *
        valAt' x (L.U i₂ ⊓ L'.U j₂) (w.s (i₂, j₂)).val := by
  have hW : ⊤ ≤ x ⁻¹ᵁ ((L.U i ⊓ L'.U j) ⊓ (L.U i₂ ⊓ L'.U j₂)) := fun p hp => ⟨h₁ hp, h₂ hp⟩
  have E : res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i ⊓ L'.U j from inf_le_left)
      (w.s (i, j) : Γ(X, L.U i ⊓ L'.U j)ˣ) =
      (res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i ⊓ L.U i₂ from
          le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) (L.g i i₂) *
        (res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L'.U j ⊓ L'.U j₂ from
          le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)) (L'.g j j₂))⁻¹) *
      res (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i₂ ⊓ L'.U j₂ from inf_le_right)
        (w.s (i₂, j₂) : Γ(X, L.U i₂ ⊓ L'.U j₂)ˣ) := hw (i, j) (i₂, j₂)
  have e := congrArg (fun a : Γ(X, (L.U i ⊓ L'.U j) ⊓ (L.U i₂ ⊓ L'.U j₂))ˣ =>
    valAt' x _ (a : Γ(X, (L.U i ⊓ L'.U j) ⊓ (L.U i₂ ⊓ L'.U j₂)))) E
  simp only [Units.val_mul, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_mul, val_inv_unit x _ hW, val_res_unit x _ hW] at e
  have a1 := val_res_unit x (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i ⊓ L'.U j from inf_le_left) hW
    (w.s (i, j) : Γ(X, L.U i ⊓ L'.U j)ˣ)
  have a2 := val_res_unit x (show L.U i ⊓ L'.U j ⊓ (L.U i₂ ⊓ L'.U j₂) ≤ L.U i₂ ⊓ L'.U j₂ from inf_le_right) hW
    (w.s (i₂, j₂) : Γ(X, L.U i₂ ⊓ L'.U j₂)ˣ)
  exact a1.symm.trans (e.trans (congrArg (fun t => _ * t) a2))

end GlobalTheory.TransportFrame

namespace GlobalTheory.TransportFrame

open ReciprocityTheory.ChartRestriction.G.TB.ValAt

theorem val_g_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (x : Sp ℂ ⟶ X) (i : L.ι) (h : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    valAt' x (L.U i ⊓ L.U i) (L.g i i).val = 1 := by
  have e := val_res_unit x (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) h (L.g i i)
  rw [hL.g_self i, Units.val_one, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_one x _ h] at e
  exact e.symm

variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} {L L' : LB A.left}

def chartOf (hL' : L'.IsLB) (y : Sp ℂ ⟶ A.left) : L'.ι := (chart_pt L' hL' y).choose

theorem chartOf_spec (hL' : L'.IsLB) (y : Sp ℂ ⟶ A.left) : ⊤ ≤ y ⁻¹ᵁ L'.U (chartOf hL' y) :=
  (chart_pt L' hL' y).choose_spec

def frT (u' : HolUnif A L' g) (hL' : L'.IsLB) (w : LB.Iso L' L) (i : L.ι) (z : Fin g → ℂ) : ℂ :=
  valAt' (u'.ex z).left (L.U i ⊓ L'.U (chartOf hL' (u'.ex z).left)) (w.s (i, chartOf hL' (u'.ex z).left)).val *
    u'.fr (chartOf hL' (u'.ex z).left) z

theorem frT_eq (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i : L.ι) (j : L'.ι)
    (z : Fin g → ℂ) (hi : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i) (hj : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L'.U j) :
    frT u' hL' w i z = valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z := by
  have h0 := chartOf_spec hL' (u'.ex z).left
  have hij0 : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U (chartOf hL' (u'.ex z).left)) := fun p hp => ⟨hi hp, h0 hp⟩
  have hij : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j) := fun p hp => ⟨hi hp, hj hp⟩
  have h0j : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L'.U (chartOf hL' (u'.ex z).left) ⊓ L'.U j) := fun p hp => ⟨h0 hp, hj hp⟩
  have G := val_gen w hw (u'.ex z).left i i (chartOf hL' (u'.ex z).left) j hij0 hij
  have C := u'.fr_compat (chartOf hL' (u'.ex z).left) j z h0j
  have hne := val_unit_ne (u'.ex z).left _ h0j (L'.g (chartOf hL' (u'.ex z).left) j)
  have hs := val_g_self hL (u'.ex z).left i hi
  unfold frT
  rw [G, hs, C]
  have hc := inv_mul_cancel₀ hne
  linear_combination (valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z) * hc

theorem frT_hol (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i : L.ι) :
    DifferentiableOn ℂ (frT u' hL' w i) {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i} := by
  intro z0 hz0
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z0).left
  have hT := u'.hol (L.U i ⊓ L'.U j) (w.s (i, j)).val
  have hz0' : ⊤ ≤ (u'.ex z0).left ⁻¹ᵁ L.U i := hz0
  have hz0T : z0 ∈ {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)} :=
    show ⊤ ≤ (u'.ex z0).left ⁻¹ᵁ (L.U i ⊓ L'.U j) from fun p hp => ⟨hz0' hp, hj hp⟩
  have hd : DifferentiableOn ℂ (fun z => valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z)
      {z | ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)} :=
    hT.2.mul ((u'.fr_hol j).mono fun z (hz : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)) p hp => (hz hp).2)
  have hev : frT u' hL' w i =ᶠ[nhds z0]
      fun z => valAt' (u'.ex z).left (L.U i ⊓ L'.U j) (w.s (i, j)).val * u'.fr j z :=
    Filter.eventually_of_mem (hT.1.mem_nhds hz0T) fun z (hz : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j)) =>
      frT_eq u' hL hL' w hw i j z (fun p hp => (hz hp).1) (fun p hp => (hz hp).2)
  exact (((hd z0 hz0T).differentiableAt (hT.1.mem_nhds hz0T)).congr_of_eventuallyEq hev).differentiableWithinAt

theorem frT_ne (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i : L.ι)
    (z : Fin g → ℂ) (hi : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i) : frT u' hL' w i z ≠ 0 := by
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z).left
  rw [frT_eq u' hL hL' w hw i j z hi hj]
  have hij : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L'.U j) := fun p hp => ⟨hi hp, hj hp⟩
  exact mul_ne_zero (val_unit_ne _ _ hij (w.s (i, j) : Γ(A.left, L.U i ⊓ L'.U j)ˣ)) (u'.fr_ne j z hj)

theorem frT_compat (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) (i i₂ : L.ι)
    (z : Fin g → ℂ) (h : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ (L.U i ⊓ L.U i₂)) :
    frT u' hL' w i z = valAt' (u'.ex z).left (L.U i ⊓ L.U i₂) (L.g i i₂).val * frT u' hL' w i₂ z := by
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z).left
  have hi : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i := fun p hp => (h hp).1
  have hi₂ : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i₂ := fun p hp => (h hp).2
  rw [frT_eq u' hL hL' w hw i j z hi hj, frT_eq u' hL hL' w hw i₂ j z hi₂ hj,
    val_gen w hw (u'.ex z).left i i₂ j j (fun p hp => ⟨hi hp, hj hp⟩) (fun p hp => ⟨hi₂ hp, hj hp⟩),
    val_g_self hL' (u'.ex z).left j hj]
  ring

def transport (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen) :
    HolUnif A L g where
  ex := u'.ex
  ex_add := u'.ex_add
  ex_onto := u'.ex_onto
  Λ := u'.Λ
  ker := u'.ker
  discrete := u'.discrete
  full := u'.full
  hol := u'.hol
  fr := frT u' hL' w
  fr_hol := frT_hol u' hL hL' w hw
  fr_ne := frT_ne u' hL hL' w hw
  fr_compat := frT_compat u' hL hL' w hw

theorem isFactorAH_transport (u' : HolUnif A L' g) (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' L) (hw : w.IsGen)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ' : u'.Λ → ℂ} (h : GlobalTheory.TorusRM.IsFactorAH u' Hm χ') :
    GlobalTheory.TorusRM.IsFactorAH (transport u' hL hL' w hw) Hm χ' := by
  refine ⟨h.1, h.2.1, fun (l : u'.Λ) i z hz => ?_⟩
  obtain ⟨j, hj⟩ := chart_pt L' hL' (u'.ex z).left
  have he : u'.ex (z + l) = u'.ex z := by rw [u'.ex_add, (u'.ker l).2 l.2, _root_.mul_one]
  have hz0 : ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U i := hz
  have hz' : ⊤ ≤ (u'.ex (z + l)).left ⁻¹ᵁ L.U i := he ▸ hz0
  have hj' : ⊤ ≤ (u'.ex (z + l)).left ⁻¹ᵁ L'.U j := he ▸ hj
  show frT u' hL' w i z = χ' l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * frT u' hL' w i (z + l)
  rw [frT_eq u' hL hL' w hw i j z hz0 hj, frT_eq u' hL hL' w hw i j (z + l) hz' hj', h.2.2 l j z hj, he]
  ring

theorem exists_holUnif_isFactorAH_of_lbIso : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L L' : LB A.left)
    (u' : HolUnif A L' g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ' : u'.Λ → ℂ), L.IsLB → L'.IsLB → LBIso L L' →
    GlobalTheory.TorusRM.IsFactorAH u' Hm χ' → ∃ (u : HolUnif A L g) (χ : u.Λ → ℂ), u.ex = u'.ex ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  intro A _ g L L' u' Hm χ' hL hL' hiso h
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  exact ⟨transport u' hL hL' w hw, χ', rfl, isFactorAH_transport u' hL hL' w hw h⟩

end GlobalTheory.TransportFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithBaseFiniteContainingRootOfUnity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem exists_arithBase_rootOfUnity : ∀ {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [ArithBase o₁ Ω₁] (Ω₂ : Type) [Field Ω₂] [Algebra Ω₁ Ω₂] (K : ℕ) (ζ : Ω₂ˣ), 0 < K → IsPrimitiveRoot ζ K → ∃ (o₂ : Type) (_ : CommRing o₂) (_ : Algebra o₂ Ω₂) (_ : ArithBase o₂ Ω₂) (κ : o₁ →+* o₂) (ze : o₂ˣ), κ.Finite ∧ (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) ∧ Units.map (algebraMap o₂ Ω₂ : o₂ →* Ω₂) ze = ζ := by
  intro o₁ Ω₁ _ _ _ hb Ω₂ _ _ K ζ hK hζ
  haveI := hb.ded
  haveI := hb.ft
  haveI := hb.char
  haveI hc₂ : CharZero Ω₂ := charZero_of_injective_algebraMap (algebraMap Ω₁ Ω₂).injective
  let f : o₁ →+* Ω₂ := (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)
  have hf : Function.Injective f := (algebraMap Ω₁ Ω₂).injective.comp hb.inj
  letI : Algebra o₁ Ω₂ := f.toAlgebra
  let Q := FractionRing o₁
  letI : Algebra Q Ω₂ := (IsFractionRing.lift (K := Q) hf).toAlgebra
  haveI : IsScalarTower o₁ Q Ω₂ := IsScalarTower.of_algebraMap_eq (fun x =>
    (IsFractionRing.lift_algebraMap (K := Q) hf x).symm)
  haveI : CharZero Q := (algebraMap Q Ω₂).charZero
  have hpow : (ζ : Ω₂) ^ K = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]
  have hint : IsIntegral o₁ (ζ : Ω₂) := IsIntegral.of_pow hK (by rw [hpow]; exact isIntegral_one)
  let F : IntermediateField Q Ω₂ := IntermediateField.adjoin Q {(ζ : Ω₂)}
  haveI : FiniteDimensional Q F := IntermediateField.adjoin.finiteDimensional hint.tower_top
  haveI : IsDedekindDomain (integralClosure o₁ F) := integralClosure.isDedekindDomain o₁ Q F
  haveI hfin : Module.Finite o₁ (integralClosure o₁ F) := IsIntegralClosure.finite o₁ Q F _
  let g : integralClosure o₁ F →+* Ω₂ := (algebraMap F Ω₂).comp (algebraMap (integralClosure o₁ F) F)
  have hg : Function.Injective g := (algebraMap F Ω₂).injective.comp Subtype.val_injective
  let zF : F := ⟨ζ, IntermediateField.mem_adjoin_simple_self Q _⟩
  have hzF : zF ^ K = 1 := Subtype.ext (by simpa using hpow)
  let z : integralClosure o₁ F :=
    ⟨zF, IsIntegral.of_pow hK (by rw [hzF]; exact isIntegral_one)⟩
  have hz : z ^ K = 1 := Subtype.ext (by simpa using hzF)
  refine ⟨integralClosure o₁ F, inferInstance, g.toAlgebra,
    @ArithBase.mk _ _ _ _ g.toAlgebra inferInstance ?_ hc₂ hg,
    algebraMap o₁ (integralClosure o₁ F), Units.ofPowEqOne z K hz hK.ne', ?_, ?_, ?_⟩
  · exact Algebra.FiniteType.trans (S := o₁) inferInstance inferInstance
  · exact RingHom.finite_algebraMap.mpr hfin
  · ext x
    rfl
  · ext
    rfl

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAugmentationTensorSigmaMapStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_augmentation_tensor_sigma_map : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)), ∃ σ : R₁ ⊗[R₀] B₀ →+ B, α.IsSig p σ := by
  first | exact @GlobalTheory.Obs.exists_isSig | exact GlobalTheory.Obs.exists_isSig | (intros; apply GlobalTheory.Obs.exists_isSig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRawDegenerationDataInjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseChange_raw_degenerationData_injective : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsNoetherianRing R₂] (σ : R₁ →+* R₂) (D₁ : DegPre R₁) (gam : FractionRing R₁ →+* FractionRing R₂), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R₂ _ (σ r)) → ∃ (D₂ : DegPre R₂) (β : D₂.P.A.left ⟶ D₁.P.A.left) (v : LB.Iso D₂.P.L (D₁.P.L.pull β)) (xe : D₂.X ≃+ D₁.X), IsGrpPullback D₂.P.A D₁.P.A (spMap σ) β ∧ v.IsGen ∧ (∀ x, (D₂.c x).left ≫ β = spMap σ ≫ (D₁.c (xe x)).left) ∧ GlobalTheory.PsiRing.RigCmp σ D₁ D₂ β v ∧ GlobalTheory.PsiRing.PsiCmp D₁ D₂ β v xe (spMap gam) := by
  first | exact @GlobalTheory.BaseChangeDeg.exists_baseChange | exact GlobalTheory.BaseChangeDeg.exists_baseChange | (intros; apply GlobalTheory.BaseChangeDeg.exists_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseMulSectionOfGermDvdFlatDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_secIsMul_of_germ_dvd : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Flat p → ∀ (L : LB X) (s : LB.Sec L) (q : R), q ≠ 0 → (∀ (x : X) j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t) → ∃ t : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t := by
  intro R _ _ X p hp L s q hq h
  haveI : Flat (X := X) (Y := Sp R) p := hp
  have loc : ∀ j, ∃ g : Γ(X, L.U j), s.f j = constFn p (L.U j) q * g := fun j =>
    exists_div p hq (L.U j) (s.f j) (fun x hx => h x j hx)
  choose t ht using loc
  have hg : ∀ j (x : X), x ∈ L.U j → gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * gs (𝟙 X) x (L.U j) (t j) := by
    intro j x hx
    rw [ht j, gs_mul _ _ _ hx, gs_constFn p (L.U j) (𝟙 X) x hx, Category.id_comp]
  refine ⟨⟨t, fun i j => ?_⟩, fun j => ?_⟩
  · refine fn_ext fun x hx => ?_
    have e := congrArg (gs (𝟙 X) x (L.U i ⊓ L.U j)) (s.compat i j)
    rw [gs_mul _ _ _ hx, gs_res _ _ _ hx, gs_res _ _ _ hx] at e ⊢
    rw [hg i x hx.1, hg j x hx.2, mul_left_comm] at e
    exact cst_regular p x hq e
  · exact ht j

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenLeOfAppEqOneOfIsClosedImmersionAlStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_le_of_app_eq_one_of_isClosedImmersion' : ∀ (X' Z' : Scheme.{0}) (i' : Z' ⟶ X') [IsClosedImmersion i'] (Y' : X'.Opens), IsAffineOpen Y' →
    ∀ (N : X'.Opens), (∀ z : Z', i' z ∈ Y' → i' z ∈ N) →
    ∃ b : Γ(X', Y'), (i'.app Y').hom b = 1 ∧ X'.basicOpen b ≤ N := by
  first | exact @GlobalTheory.exists_basicOpen_le_of_app_eq_one_of_isClosedImmersion | exact GlobalTheory.exists_basicOpen_le_of_app_eq_one_of_isClosedImmersion | (intros; apply GlobalTheory.exists_basicOpen_le_of_app_eq_one_of_isClosedImmersion <;> assumption)
end

