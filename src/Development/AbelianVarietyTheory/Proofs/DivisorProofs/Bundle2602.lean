import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2449
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2516
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2520
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPtCompClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2352
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2474
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemFibreOfGeometricLifting
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_mem_fibre_of_geometric_lifting :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (S P' X : Scheme.{0}) (π : S ⟶ Sp R) (h : P' ⟶ Sp R) (a : X ⟶ P') (q : X ⟶ S), Surjective π → ∀ x : P', h x = closedPoint R → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ h = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ q = s) → ∃ z : X, a z = x := by
  intro R _ _ S P' X π h a q hπ x hx H
  obtain ⟨s₀, hs₀⟩ := π.surjective (h x)
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := h) (g := π) x s₀ hs₀.symm
  let Ω : Type := AlgebraicClosure ((pullback h π).residueField w)
  let t : Sp Ω ⟶ pullback h π :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback h π).residueField w) Ω)) ≫
      (pullback h π).fromSpecResidueField w
  have ht : ∀ y, t y = w := by
    intro y
    simp only [t, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have hξ : ∀ y, (t ≫ pullback.fst h π) y = x := by
    intro y
    rw [Scheme.Hom.comp_apply, ht, hw]
  obtain ⟨p, hp, -⟩ := H Ω (t ≫ pullback.fst h π) (t ≫ pullback.snd h π)
    (by
      ext y
      constructor
      · rintro ⟨u, rfl⟩
        exact hξ u
      · rintro rfl
        exact ⟨closedPoint Ω, hξ _⟩)
    (by simp [pullback.condition])
  refine ⟨p (closedPoint Ω), ?_⟩
  have h₀ := hξ (closedPoint Ω)
  rw [← hp] at h₀
  exact (Scheme.Hom.comp_apply p a _).symm.trans h₀

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialPeriodsSymmetricExponentFormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monomialPeriods_symmetric_exponentForm : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ϖ : W, Irreducible ϖ →
    ∀ D : DegData W (maximalIdeal W), ∃ β : LinearMap.BilinForm ℤ D.toPre.X, (∀ a b, β a b = β b a) ∧
      IsMonomial D.toPre ![ϖ] ![β] := by
  first | exact @GlobalTheory.MonPeriods.exists_isMonomial_symm | exact GlobalTheory.MonPeriods.exists_isMonomial_symm | (intros; apply GlobalTheory.MonPeriods.exists_isMonomial_symm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatPosDefAddNsmulPosDefHermitianStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_posDef_add_nsmul_posDef_hermitian : ∀ (g : ℕ) (H₀ Hm : Matrix (Fin g) (Fin g) ℂ),
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) →
    ∃ n : ℕ, ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ (Hm + n • H₀).mulVec (star z)).re := by
  first | exact @GlobalTheory.posn_main | exact GlobalTheory.posn_main | (intros; apply GlobalTheory.posn_main <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalLiftOfDefectCoboundary
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_natLift_of_defect : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), L.IsLift L' n l → ∀ (κ : ∀ (T T' : C') (_ : T ⟶ T'), Ω[(OAff s₀).obj (n.G.obj T)⁄R₀] →+ L'.B T') (u : GlobForm s₀ →+ ∀ T : C', L'.B T), (∀ (T T' : C') (a : T ⟶ T'), IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) (κ T T' a)) → (∀ (r : R) w, u (π r • w) = r • u w) → (∀ w T, u w T ∈ I.map (algebraMap R (L'.B T))) → (∀ (w : GlobForm s₀) (T T' : C') (a : T ⟶ T'), κ T T' a (w.1 (n.G.obj T)) = u w T' - L'.ρ a (u w T)) → ∃ l' : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T, L.IsLift L' n l' ∧ L.IsNat L' n l' := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hpar C' _ F' L L' n l hl κ u hκ hus hum hκd
  have hext : ∀ T : C', ∃! ξ : Ω[Sec s₀ (n.G.obj T).unop.1⁄R₀] →+ L'.B T,
      (∀ b w, ξ (L.p (n.G.obj T) b • w) = l T b * ξ w) ∧
      (∀ w, ξ w ∈ I.map (algebraMap R (L'.B T))) ∧ ∀ w : GlobForm s₀, ξ (w.1 (n.G.obj T)) = u w T := fun T ↦
    exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar (n.G.obj T) (L.B (n.G.obj T)) (L'.B T) (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (l T) ((Pi.evalAddMonoidHom _ T).comp u)
      (fun r w ↦ by simp [hus]) (fun w ↦ hum w T)
  choose ξ hξ using fun T ↦ (hext T).exists
  have hψ : ∀ T : C', ∃ ψ : L.B (n.G.obj T) →ₐ[R] L'.B T,
      IsTheta I (L.p (n.G.obj T)) (l T) ψ (-ξ T) := fun T ↦
    (GlobalTheory.T.algHom_lifts_sqZero_classified_by_differentials R R₀ (L.B (n.G.obj T)) (Sec s₀ (n.G.obj T).unop.1) (L'.B T) I hI π hπ (L.p _) (L.semi _)
      (L.surj _) (L.ker _) (l T)).2 (-ξ T)
      (fun b w ↦ by rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, (hξ T).1, mul_neg])
      (fun w ↦ by rw [AddMonoidHom.neg_apply]; exact neg_mem ((hξ T).2.1 w))
  choose ψ hψ using hψ
  have hψv : ∀ T b, ψ T b = l T b + ξ T (D R₀ (Sec s₀ (n.G.obj T).unop.1) (L.p _ b)) := fun T b ↦ by
    have h := (hψ T).der b
    rw [AddMonoidHom.neg_apply] at h
    change -ξ T _ = l T b - ψ T b at h
    linear_combination h
  refine ⟨ψ, fun T b ↦ ?_, fun T T' a b ↦ ?_⟩
  · rw [hψv, map_add, hl, (L'.ker T _).2 ((hξ T).2.1 _), add_zero]
  · let α : L.B (n.G.obj T) →ₐ[R] L'.B T' := (L'.ρ a).comp (l T)
    let χ : Ω[Sec s₀ (n.G.obj T).unop.1⁄R₀] →+ L'.B T' := κ T T' a + (L'.ρ a).toAddMonoidHom.comp (ξ T) -
      (ξ T').comp (p1 (OAff s₀) (n.G.map a)).toAddMonoidHom
    have hχ : ∀ w, χ w = κ T T' a w + L'.ρ a (ξ T w) - ξ T' (p1 (OAff s₀) (n.G.map a) w) := fun _ ↦ rfl
    have hmemV : ∀ w, ξ T' w ∈ I.map (algebraMap R (L'.B T')) := (hξ T').2.1
    have hdiff : ∀ c : L.B (n.G.obj T), ∀ x ∈ I.map (algebraMap R (L'.B T')),
        l T' (L.ρ (n.G.map a) c) * x = α c * x := by
      intro c x hx
      have h1 := (hκ T T' a).der c
      have h2 : α c - l T' (L.ρ (n.G.map a) c) ∈ I.map (algebraMap R (L'.B T')) :=
        h1 ▸ (hκ T T' a).mem _
      have h3 := mul_eq_zero_of_mem_map hI h2 hx
      rw [sub_mul] at h3
      exact (sub_eq_zero.1 h3).symm
    have hu := exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar (n.G.obj T) (L.B (n.G.obj T)) (L'.B T') (L.p _)
      (L.semi _) (L.surj _) (L.ker _) α 0 (fun r w ↦ by simp) (fun w ↦ zero_mem _)
    have hχ0 : χ = 0 := by
      refine hu.unique ⟨fun b w ↦ ?_, fun w ↦ ?_, fun w ↦ ?_⟩ ⟨fun b w ↦ by simp, fun w ↦ zero_mem _, fun w ↦ rfl⟩
      · rw [hχ, hχ, (hκ T T' a).smul, (hξ T).1, oneFormsMapOfFunctorMorphism_smul, map_mul]
        rw [← L.nat (n.G.map a) b, (hξ T').1, hdiff _ _ (hmemV _)]
        simp only [α, AlgHom.coe_comp, Function.comp_apply]
        ring
      · rw [hχ]
        exact sub_mem (add_mem ((hκ T T' a).mem w) (algHom_mem_map I _ ((hξ T).2.1 w))) (hmemV _)
      · rw [hχ, hκd, (hξ T).2.2, ← w.2 (n.G.map a), (hξ T').2.2]
        simp
    have h0 : χ (D R₀ (Sec s₀ (n.G.obj T).unop.1) (L.p _ b)) = 0 := by rw [hχ0]; rfl
    rw [hχ, p1_D] at h0
    have hn : mp (OAff s₀) (n.G.map a) (L.p _ b) = L.p _ (L.ρ (n.G.map a) b) := (L.nat (n.G.map a) b).symm
    rw [hn] at h0
    have h1 := (hκ T T' a).der b
    simp only [α, AlgHom.coe_comp, Function.comp_apply] at h1
    rw [hψv, hψv, map_add]
    linear_combination h0 - h1

end GlobalTheory.LiftSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsCharacterUnitKernelAction
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

theorem exists_nhds_charUnit : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ), IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → ∀ y : (A' ⊗ T).left, ∃ V : (A' ⊗ T).left.Opens, y ∈ V ∧ ∃ e : Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ V)ˣ, ∀ (W : (A ⊗ (N ⊗ T)).left.Opens) (h₁ : W ≤ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ V)) (h₂ : W ≤ (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ V)), res h₁ (pullU (actMap i T).left _ e) = res le_top (pullTop (snd A (N ⊗ T)).left χ) * res h₂ (pullU (prMap A N T).left _ e) := by
  intro S A A' N T _ _ _ i q χ hi hq hfin hflat hsurj hk hχ y
  have hpb := GlobalTheory.T.kernelAction_isPullback_prodMap_torsor S A A' N T i q hi hq hk
  have hpb' : IsPullback (prMap A N T).left (actMap i T).left (pmap q T).left (pmap q T).left :=
    hpb.map (Over.forget S)
  obtain ⟨W, m₁₂, m₂₃, m₁₃, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_kernelAction_triple_overlap S A N T i χ hi hχ
  have hpq : pmap q T = q ▷ T := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [pmap]
  have hsq := GlobalTheory.SemiRigid.isPullback_whiskerRight q T
  have hA : IsAffineHom (pmap q T).left := by
    rw [hpq]; exact MorphismProperty.of_isPullback hsq inferInstance
  have hF : Flat (pmap q T).left := by
    rw [hpq]; exact MorphismProperty.of_isPullback hsq inferInstance
  have hS : Surjective (pmap q T).left := by
    rw [hpq]; exact MorphismProperty.of_isPullback hsq inferInstance
  exact GlobalTheory.T.locally_trivial_unit_cocycle_scheme _ _ _ _ (pmap q T).left (actMap i T).left (prMap A N T).left m₁₂ m₂₃ m₁₃ _
    hA hF hS hpb' h1 h2 h3 h4 y

end GlobalTheory.CharKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsNonzeroOfIsClosedMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_nhds_nonzero_of_isClosedMap :
    ∀ (Z Y : Scheme.{0}) (p : Z ⟶ Y), IsClosedMap p.base → ∀ (L : LB Z) (V : Y.Opens) (u : LB.Sec (L.pull (p ⁻¹ᵁ V).ι)) (y : Y), y ∈ V → (∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) = y → z ∈ nonzeroLocus u) → ∃ V₁ : Y.Opens, y ∈ V₁ ∧ V₁ ≤ V ∧ ∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) ∈ V₁ → z ∈ nonzeroLocus u := by
  intro Z Y p hp L V u y hy h
  have hO : IsOpen ((p ⁻¹ᵁ V).ι '' (nonzeroLocus u : Set (p ⁻¹ᵁ V).toScheme)) :=
    (p ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap _ (nonzeroLocus u).isOpen
  have hC : IsClosed (p.base '' ((p ⁻¹ᵁ V).ι '' (nonzeroLocus u : Set (p ⁻¹ᵁ V).toScheme))ᶜ) :=
    hp _ hO.isClosed_compl
  refine ⟨V ⊓ ⟨_, hC.isOpen_compl⟩, ⟨hy, ?_⟩, inf_le_left, ?_⟩
  · rintro ⟨c, hc, hcy⟩
    have hcV : c ∈ p ⁻¹ᵁ V := by
      change p c ∈ V
      have : p c = y := hcy
      rw [this]; exact hy
    exact hc ⟨⟨c, hcV⟩, h ⟨c, hcV⟩ hcy, rfl⟩
  · intro z hz
    have h2 : (p ⁻¹ᵁ V).ι z ∈ (p ⁻¹ᵁ V).ι '' (nonzeroLocus u : Set (p ⁻¹ᵁ V).toScheme) := by
      by_contra hn
      exact hz.2 ⟨_, hn, rfl⟩
    obtain ⟨w, hw, hwz⟩ := h2
    have : w = z := (p ⁻¹ᵁ V).ι.isOpenEmbedding.injective hwz
    subst this
    exact hw

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonvanishingExtensionNormalCompactificatio
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.ExtendNormal

open FromGeneric

theorem valR_eq_one {X : Scheme.{0}} [IsReduced X] {U : X.Opens} {K : Type} [Field K] (x : Sp K ⟶ X)
    (hx : Set.range x ⊆ U) (hd : ∀ z ∈ U, x (IsLocalRing.closedPoint K) ⤳ z) {f : Γ(X, U)} (hf : valR x U f = 1)
    {R : Type} [CommRing R] (x' : Sp R ⟶ X) (hx' : Set.range x' ⊆ U) : valR x' U f = 1 := by
  have h : ⊤ ≤ x ⁻¹ᵁ U := fun z _ => hx ⟨z, rfl⟩
  have h' : ⊤ ≤ x' ⁻¹ᵁ U := fun z _ => hx' ⟨z, rfl⟩
  have h0 : (x.appLE U ⊤ h).hom (f - 1) = 0 := by
    rw [valR, dif_pos h] at hf
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).hom).1
    rw [map_sub, map_sub, map_one, map_one, map_zero]
    exact sub_eq_zero.2 hf
  have h1 : f - 1 = 0 := by
    refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun z hz => ?_)
    have h2 : x (IsLocalRing.closedPoint K) ∈ X.basicOpen (f - 1) :=
      (hd z (X.basicOpen_le _ hz)).mem_open (X.basicOpen _).isOpen hz
    have h3 := Scheme.basicOpen_appLE x ⊤ U h (f - 1)
    rw [show (x.appLE U ⊤ h) (f - 1) = 0 from h0, Scheme.basicOpen_zero] at h3
    have h4 : IsLocalRing.closedPoint K ∈ (⊤ ⊓ x ⁻¹ᵁ X.basicOpen (f - 1) : (Sp K).Opens) := ⟨trivial, h2⟩
    rw [← h3] at h4
    exact h4.elim
  rw [sub_eq_zero.1 h1, valR, dif_pos h', map_one, map_one]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

theorem exists_frame_local {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {V : Set X}
    {τ : E →+* ℂ} {p q : ℕ} (hcov : FrameCover t π s V (HermitianCompactForm.chi c τ) p q) {R : Type} [CommRing R] [IsLocalRing R]
    (x : Sp R ⟶ X) (hx : x (IsLocalRing.closedPoint R) ∈ V) :
    ∃ (j : c.F →+* R) (v : Fin p → (epsAt (x ≫ π) ⟶ t.G)) (w : Fin q → (epsAt (x ≫ π) ⟶ t.G)),
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w := by
  obtain ⟨W, hW, j, v, w, hz, h⟩ := hcov _ hx
  have : IsOpenImmersion (show Sp Γ(X, W) ⟶ X from hW.fromSpec) := inferInstanceAs (IsOpenImmersion hW.fromSpec)
  obtain ⟨m, hm⟩ := exists_lift (show Sp Γ(X, W) ⟶ X from hW.fromSpec) x (range_subset _
    (show Sp Γ(X, W) ⟶ X from hW.fromSpec).isOpenEmbedding.isOpen_range (by
      rw [show Set.range _ = _ from hW.range_fromSpec]; exact hz))
  obtain ⟨v', w', h', -⟩ := exists_pull m h hm
  exact ⟨_, v', w', h'⟩

theorem unitAtPt_of_dvr {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {V : Set X}
    {τ : E →+* ℂ} {p q : ℕ} (hcov : FrameCover t π s V (HermitianCompactForm.chi c τ) p q) {B : Scheme.{0}} [IsIntegral B]
    [IsLocallyNoetherian B] (hB : ∀ y : B, IsIntegrallyClosed (B.presheaf.stalk y)) (io : B ⟶ X)
    (hio : ∀ y, io y ∈ V) {j₀ : c.F →+* B.functionField} {v₀ w₀}
    (h₀ : IsFrame t π s V (HermitianCompactForm.chi c τ) (p := p) (q := q) j₀ (genPt B ≫ io) v₀ w₀) {δ : B.functionField} (hδ : δ ≠ 0)
    (hdvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R B.functionField]
      [IsFractionRing R B.functionField] (j : c.F →+* R) (x : Sp R ⟶ X) v w M N,
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w →
      IsChg t π (algebraMap R B.functionField) x v w (genPt B ≫ io) v₀ w₀ M N →
      ∃ u : Rˣ, N.det * algebraMap R B.functionField u = M.det * δ) (y : B) :
    UnitAtPt t π s V (HermitianCompactForm.chi c τ) io v₀ w₀ δ y := by
  obtain ⟨j, v, w, h⟩ := exists_frame_local hcov (locPt B y ≫ io) (by rw [locPt_comp_closedPoint]; exact hio y)
  obtain ⟨-, M, N, hc⟩ := exists_chg (algebraMap (B.presheaf.stalk y) B.functionField) h h₀
    (by rw [genPt_eq y, Category.assoc])
  obtain ⟨hM, hN⟩ := chg_isUnit h h₀ hc
  have hφ : M.det * δ / N.det ≠ 0 := div_ne_zero (mul_ne_zero hM.ne_zero hδ) hN.ne_zero
  have key : ∀ z : B, z ⤳ y → IsDiscreteValuationRing (B.presheaf.stalk z) →
      ∃ u : (B.presheaf.stalk z)ˣ, algebraMap _ B.functionField (u : B.presheaf.stalk z) = M.det * δ / N.det := by
    intro z hz _
    let g : B.presheaf.stalk y →+* B.presheaf.stalk z := (B.presheaf.stalkSpecializes hz).hom
    have hg : (algebraMap (B.presheaf.stalk z) B.functionField).comp g =
        algebraMap (B.presheaf.stalk y) B.functionField :=
      congrArg CommRingCat.Hom.hom (B.presheaf.stalkSpecializes_comp ((genericPoint_spec B).specializes trivial) hz)
    obtain ⟨v', w', h', a, b⟩ := exists_pull g h rfl
    obtain ⟨u, hu⟩ := hdvr _ _ _ v' w' M N h' ⟨by
      rw [← Category.assoc, ← DetExtendZero.spMap_comp, hg]; exact hc.1, fun i => by
      simp only [a, ← Category.assoc, ← DetExtendZero.dual_comp, hg]; exact hc.2.1 i, fun i => by
      simp only [b, ← Category.assoc, ← DetExtendZero.dual_comp, hg]; exact hc.2.2 i⟩
    exact ⟨u, by rw [← hu, mul_div_cancel_left₀ _ hN.ne_zero]⟩
  obtain ⟨a, ha⟩ := GlobalTheory.Hartogs.regAt_of_forall_dvr B hB (M.det * δ / N.det) y fun z hz hz' => by
    obtain ⟨u, hu⟩ := key z hz hz'
    exact ⟨u, hu⟩
  obtain ⟨b, hb⟩ := GlobalTheory.Hartogs.regAt_of_forall_dvr B hB (M.det * δ / N.det)⁻¹ y fun z hz hz' => by
    obtain ⟨u, hu⟩ := key z hz hz'
    exact ⟨(u⁻¹ : (B.presheaf.stalk z)ˣ), by rw [← hu, map_units_inv]⟩
  have hab : a * b = 1 := IsFractionRing.injective (B.presheaf.stalk y) B.functionField (by
    rw [map_mul, map_one, ha, hb, mul_inv_cancel₀ hφ])
  refine ⟨j, v, w, M, N, Units.mkOfMulEqOne a b hab, h, hc, ?_⟩
  rw [Units.val_mkOfMulEqOne, ha, mul_div_cancel₀ _ hN.ne_zero]

theorem exists_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z : Model Xo c β') (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (σZ : RuleY Z) (σ : RuleU Xo c), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → τ (H.rt : E) = H.rt0 → SecY Z (compactOf Z U) τ σZ → NzY Z (compactOf Z U) τ σZ → SecU Xo c U τ σ → Restricts Z U τ σZ σ → ∃ σb : RuleY Y, SecY Y (compactOf Y U) τ σb ∧ NzY Y (compactOf Y U) τ σb ∧ Restricts Y U τ σb σ := by
  intro E _ _ _ H D l Xo c O _ β Y O' _ β' Z U τ σZ σ hn hcl hU hτ hσZ hZ hσ hres
  obtain ⟨V, hV, hint⟩ := GlobalTheory.T.genericFibre_componentClosure_open_isIntegral E H D l Xo c O β Y U hn hcl hU
  have := Y.jQ_open
  have : IsProper (genStr Y) := isProper_genStr Y
  have : IsLocallyNoetherian (gen Y) := LocallyOfFiniteType.isLocallyNoetherian (genStr Y)
  have : IsReduced (gen Y) := by
    have := fun y => (hn y).1
    exact isReduced_of_isReduced_stalk _
  have : IsReduced (Xo.XF c) := isReduced_of_isOpenImmersion Y.jQ
  have hB : ∀ y : V.toScheme, IsIntegrallyClosed (V.toScheme.presheaf.stalk y) := fun y =>
    haveI := (hn (V.ι y)).2
    IsIntegrallyClosed.of_equiv (asIso (V.ι.stalkMap y)).commRingCatIsoToRingEquiv
  have hcov := frameCover_gen E H D l Xo c O β Y V τ hτ
  rw [hV] at hcov
  have hio : ∀ y, V.ι y ∈ compactOf Y U := fun y => hV ▸ y.2
  have hpt : (genPt V.toScheme ≫ V.ι) (IsLocalRing.closedPoint _) = V.ι (genericPoint V.toScheme) :=
    locPt_comp_closedPoint V.ι _
  have hsp : ∀ z ∈ compactOf Y U, V.ι (genericPoint V.toScheme) ⤳ z := fun z hz =>
    (genericPoint_specializes (α := V.toScheme) (⟨z, (hV ▸ hz : z ∈ (V : Set (gen Y)))⟩ : V.toScheme)).map V.ι.continuous
  have hgen : V.ι (genericPoint V.toScheme) ∈ Y.jQ '' (U : Set (Xo.XF c)) := by
    obtain ⟨z, hz⟩ := closure_nonempty_iff.1 ⟨_, hio (genericPoint V.toScheme)⟩
    exact (hsp z (subset_closure hz)).mem_open (Y.jQ.isOpenEmbedding.isOpenMap _ U.isOpen) hz
  obtain ⟨j₀, v₀, w₀, h₀⟩ := exists_frame_local hcov (genPt V.toScheme ≫ V.ι) (by rw [hpt]; exact hio _)
  have main : ∀ (K : Type) [Field K] (xb : Sp K ⟶ gen Y) (j₀ : c.F →+* K) v₀ w₀,
      xb (IsLocalRing.closedPoint K) = V.ι (genericPoint V.toScheme) → FrY Y (compactOf Y U) τ j₀ xb v₀ w₀ →
      ∃ δ : K, δ ≠ 0 ∧ (∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra R K]
        [IsFractionRing R K] (j : c.F →+* R) (x : Sp R ⟶ gen Y) v w M N, FrY Y (compactOf Y U) τ j x v w →
        IsChg Y.t (genι Y) (algebraMap R K) x v w xb v₀ w₀ M N → ∃ u : Rˣ, N.det * algebraMap R K u = M.det * δ) ∧
        ∀ σb : RuleY Y, SecY Y (compactOf Y U) τ σb → NzY Y (compactOf Y U) τ σb → σb K xb v₀ w₀ = δ →
          Restricts Y U τ σb σ := by
    intro K _ xb j₀ v₀ w₀ hxb h₀
    obtain ⟨x, rfl⟩ : ∃ x : Sp K ⟶ Xo.XF c, x ≫ Y.jQ = xb :=
      ⟨IsOpenImmersion.lift Y.jQ xb (range_subset _ Y.jQ.isOpenEmbedding.isOpen_range
        (hxb ▸ Set.image_subset_range _ _ hgen)), IsOpenImmersion.lift_fac _ _ _⟩
    have hxb' : Y.jQ (x (IsLocalRing.closedPoint K)) = V.ι (genericPoint V.toScheme) :=
      (Scheme.Hom.comp_apply _ _ _).symm.trans hxb
    have hxU : Set.range x ⊆ U := range_subset _ U.isOpen (by
      obtain ⟨z, hz, e⟩ := hgen
      rwa [Y.jQ.isOpenEmbedding.injective (hxb'.trans e.symm)])
    obtain ⟨v, w, h, sv, sw⟩ := (frame_transfer E H D l Xo c O β Y U τ K j₀ x).2 _ v₀ w₀ hxU h₀
    refine ⟨σ K x v w, ?_, fun R _ _ _ _ _ j xR vR wR M N hR hc => ?_, fun σb hb hnz e => ?_⟩
    · obtain ⟨vz, wz, hz, a, b⟩ := (frame_transfer E H D l Xo c O' β' Z U τ K j₀ x).1 v w h
      rw [← hres K j₀ x v w vz wz h hz a b]
      exact (hZ K j₀ _ vz wz hz).ne_zero
    · obtain ⟨vb, wb, hb, a, b⟩ := exists_pull (algebraMap R K) hR hc.1
      obtain ⟨v', w', h', sv', sw'⟩ := (frame_transfer E H D l Xo c O β Y U τ K _ x).2 _ vb wb hxU hb
      obtain ⟨u, hu⟩ := GlobalTheory.T.determinantSection_unit_integral_frames_dvr E H D l Xo c O β Y O' β' Z U τ σZ σ hσZ hZ hres R K j xR x _ vR wR v' w' vb wb
        hR h' hc.1 sv' sw' a b
      have hid : x = spMap (RingHom.id K) ≫ x := by rw [DetExtendZero.spMap_id, Category.id_comp]
      refine ⟨u, ?_⟩
      rw [← hu]
      refine sec_chg (g := RingHom.id K) hσ h' h ⟨hid, fun i => ?_, fun i => ?_⟩
      · refine (isCombination_iff_of_sameVecs E H D l Xo c O β Y K K _ x x _ v' vb v v₀ hid sv' sv _ i).2 ?_
        simp only [DetExtendZero.dual_id, Category.id_comp, a]
        exact hc.2.1 i
      · refine (isCombination_iff_of_sameVecs E H D l Xo c O β Y K K _ x x _ w' wb w w₀ hid sw' sw _ i).2 ?_
        simp only [DetExtendZero.dual_id, Category.id_comp, b]
        exact hc.2.2 i
    · obtain ⟨σ₁, h1, h2, h3⟩ := GlobalTheory.T.exists_determinantLine_section_restriction E H D l Xo c O β Y U τ σb hb
      obtain ⟨f, hf⟩ := GlobalTheory.detLine_exists_ratio E H l c _ _ _ _ _ τ _ _ U σ₁ σ
        (frameCover_univ E H D l Xo c U τ hτ) h1 (h3 hnz) hσ
      have e1 : valR x U f = 1 := by
        have e2 := hf K j₀ x v w h
        rw [← e, h2 K j₀ x v w v₀ w₀ h h₀ sv sw] at e2
        exact ((h3 hnz K j₀ x v w h).mul_right_cancel ((_root_.one_mul _).trans e2)).symm
      intro R _ j x' v' w' vb wb h' hb' a b
      rw [h2 R j x' v' w' vb wb h' hb' a b, hf R j x' v' w' h',
        valR_eq_one x hxU (fun z hz => ?_) e1 x' h'.2.1, _root_.one_mul]
      rw [← Y.jQ.isOpenEmbedding.isInducing.specializes_iff, hxb']
      exact hsp _ (subset_closure ⟨z, hz, rfl⟩)
  obtain ⟨δ, hδ, hdvr, hfin⟩ := main _ _ j₀ v₀ w₀ hpt h₀
  obtain ⟨σb, h1, h2, h3⟩ := exists_section E H l c _ _ _ _ _ τ _ _ V.toScheme V.ι _ inferInstance
    (V.range_ι.trans hV) hcov j₀ v₀ w₀ δ h₀ (unitAtPt_of_dvr hcov hB V.ι hio h₀ hδ hdvr)
  exact ⟨σb, h1, h2, hfin σb h1 h2 h3⟩

end GlobalTheory.DetLine.ExtendNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroClassicalPointOfLocalHomAvoidingStatement
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_classicalPoint_of_localHom_avoiding : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ x : M.Z, ∃ s : M.O x, s ≠ 0 ∧ ∀ (p : ℕ) [Fact p.Prime] (χ : M.O x →+* OO p), IsLocalHom χ → χ s ≠ 0 → ∃ y : Sp (OO p) ⟶ M.Z, M.Cen U x y ∧ ∀ a : M.O x, M.val (gPt p ≫ y) a = ((χ a : OO p) : PadicAlgCl p) := by
  first | exact @GlobalTheory.Izumi.exists_ne_zero_forall_exists_cen | exact GlobalTheory.Izumi.exists_ne_zero_forall_exists_cen | (intros; apply GlobalTheory.Izumi.exists_ne_zero_forall_exists_cen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroExpansionTermCompleteDVRStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_expansionTerm_completeDVR : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G'), GlobalTheory.LN.Under U' U₀.toUnifPre → ∀ (σ' : U'.SecGT (𝟙_ _) 1) (f' : ∀ α, GlobalTheory.UU.SecBT D'.toPre (𝟙_ _) 1 α), U'.ExpT (𝟙_ _) 1 σ' f' → (∃ j, σ'.f j ≠ 0) → ∃ α j, (f' α).f j ≠ 0 := by
  first | exact @GlobalTheory.ExpansionNonzero.exists_term_ne_zero | exact GlobalTheory.ExpansionNonzero.exists_term_ne_zero | (intros; apply GlobalTheory.ExpansionNonzero.exists_term_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionPreUniformisedCompleteNormalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_section_preUniformised_completeNormal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), ∃ σ : U.SecGT (𝟙_ _) 1, ∃ j, σ.f j ≠ 0 := by
  first | exact @GlobalTheory.Mum.ModelSection.main | exact GlobalTheory.Mum.ModelSection.main | (intros; apply GlobalTheory.Mum.ModelSection.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationModelFiniteExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisation_model_finite_extension : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} (X₁ : Setup F W i) (o₂ Ω₂ : Type) [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [ArithBase o₂ Ω₂] [Algebra X₁.Ω₁ Ω₂] [FiniteDimensional X₁.Ω₁ Ω₂] (κ : X₁.o₁ →+* o₂), κ.Finite → (algebraMap o₂ Ω₂).comp κ = (algebraMap X₁.Ω₁ Ω₂).comp (algebraMap X₁.o₁ X₁.Ω₁) → ∃ (M : RatModel o₂ Ω₂) (q : M.Z ⟶ X₁.M.Z), GlobalTheory.IsNormalScheme M.Z ∧ IsFinite q ∧ M.pt ≫ q = spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt := by
  first | exact @GlobalTheory.Poinc.Setup.exists_model_of_finiteDimensional | exact GlobalTheory.Poinc.Setup.exists_model_of_finiteDimensional | (intros; apply GlobalTheory.Poinc.Setup.exists_model_of_finiteDimensional <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupCyclotomicAwayProjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalised_blowup_cyclotomicAway_projective : ∀ (n : ℕ) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)), IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ (J : Z.IdealSheafData) (W : Z.Opens), Dense (W : Set Z) → (∀ x ∈ J.support, x ∉ W) → ∃ (S : Scheme.{0}) (π : S ⟶ Z) (BD : EffCartierData S), IsNormBl π J ∧ IsProjOver (π ≫ z) ∧ BD.idealSheaf = J.comap π ∧ IsIso (π ∣_ W) ∧ Dense (π ⁻¹' W : Set S) := by
  first | exact @GlobalTheory.NormBlowupInt.exists_normBl | exact GlobalTheory.NormBlowupInt.exists_normBl | (intros; apply GlobalTheory.NormBlowupInt.exists_normBl <;> assumption)
end

