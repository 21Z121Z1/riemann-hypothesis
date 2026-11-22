import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2574
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2563
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2540
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertHomCompatible
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2575
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2576
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepCongruenceElementSeparatesChartBallThickFram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0231
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2634
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0833
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2577
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCohomologyComputedOnAffinePairs
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDForm.AffPair

section

variable {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) {X : Scheme.{0}} (t : X ⟶ Sp R)
  {Y : Scheme.{0}} (i : X ⟶ Y)

def smAff : ObjectProperty (IsSm κ t i).FullSubcategory := fun S ↦ IsAffineOpen S.obj.U

theorem smAff_up (S S' : (IsSm κ t i).FullSubcategory) (f : S ⟶ S') (h : smAff κ t i S) :
    smAff κ t i S' := by
  rcases S'.obj.hU with h' | h'
  · exact h'
  · have e : S'.obj.U = S.obj.U := le_antisymm f.hom.2 (h' ▸ le_top)
    change IsAffineOpen S'.obj.U
    rw [e]
    exact h

abbrev coefSm : (IsSm κ t i).FullSubcategory ⥤ CommAlgCat.{0} R := (IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t

def toIter : EE κ t i ⥤ (smAff κ t i).FullSubcategory where
  obj a := ⟨⟨a.obj, ⟨⟨a.obj.U, a.property⟩, a.obj.mem⟩⟩, a.property⟩
  map f := ⟨⟨f.hom⟩⟩

def ofIter : (smAff κ t i).FullSubcategory ⥤ EE κ t i where
  obj a := ⟨a.obj.obj, a.property⟩
  map f := ⟨f.hom.hom⟩

def mapTo : CoefMap (RingHom.id R) ((smAff κ t i).ι ⋙ coefSm κ t i) (pE κ t i ⋙ O κ t) where
  G := toIter κ t i
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def mapOf : CoefMap (RingHom.id R) (pE κ t i ⋙ O κ t) ((smAff κ t i).ι ⋙ coefSm κ t i) where
  G := ofIter κ t i
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

theorem mapTo_pull1 : Function.Bijective (mapTo κ t i).pull1 := by
  refine Function.bijective_iff_has_inverse.2 ⟨(mapOf κ t i).pull1, fun c ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := H1.mk_surjective _ c; rfl
  · obtain ⟨a, rfl⟩ := H1.mk_surjective _ c; rfl

theorem mapTo_pull2 : Function.Bijective (mapTo κ t i).pull2 := by
  refine Function.bijective_iff_has_inverse.2 ⟨(mapOf κ t i).pull2, fun c ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := H2.mk_surjective _ c; rfl
  · obtain ⟨a, rfl⟩ := H2.mk_surjective _ c; rfl

end

end GlobalTheory.PDForm.AffPair

namespace GlobalTheory.PDForm

open AffPair in

theorem crystallineCohomology_computed_on_affinePairs : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y),
    (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) →
    ((Cx.single (Coef.ofAlg (O κ t))).resMap (pE κ t i)).PullbackBijectiveDegreesOneTwo := by
  intro R _ I κ X t Y i hY
  have ha := GlobalTheory.T.crystallineCohomology_restrict_affinePointPairs_bijective R I κ X t Y i
  have hc := GlobalTheory.T.affinePointPairs_comma_acyclic_degree_le_two.1 R I κ X t Y i hY
  have hc2 := GlobalTheory.T.affinePointPairs_comma_acyclic_degree_le_two.2 R I κ X t Y i hY
  have h1 : Function.Bijective (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull1 :=
    Desc.restrict_upwardClosed_subcategory_pull1_bijective R _ (coefSm κ t i) (smAff κ t i) (smAff_up κ t i)
      (fun T ↦ (hc T).1) (fun T ↦ (hc T).2.1) fun T ↦ (hc T).2.2
  have h2 : Function.Bijective (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull2 :=
    ⟨Desc.pull_restrict_small_injective (coefSm κ t i) (smAff κ t i) (smAff_up κ t i)
      (fun T ↦ (hc T).1) (fun T ↦ (hc T).2.1) fun T ↦ (hc T).2.2,
    Desc.descent_H2_surjective (coefSm κ t i) (smAff κ t i) (smAff_up κ t i)
      (fun T ↦ (hc T).1) (fun T ↦ (hc T).2.1) (fun T ↦ (hc T).2.2) hc2⟩
  refine GlobalTheory.T.algebra_coefficients_restriction_bijective R _ _ (O κ t) (pE κ t i) ?_ ?_
  · have h := (mapTo_pull1 κ t i).comp (h1.comp ha.1)
    have e : ⇑(CoefMap.restrict (O κ t) (pE κ t i)).pull1 = (mapTo κ t i).pull1 ∘
        (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull1 ∘
        (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull1 := by
      funext c
      obtain ⟨a, rfl⟩ := H1.mk_surjective _ c; rfl
    rw [e]
    exact h
  · have h := (mapTo_pull2 κ t i).comp (h2.comp ha.2)
    have e : ⇑(CoefMap.restrict (O κ t) (pE κ t i)).pull2 = (mapTo κ t i).pull2 ∘
        (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull2 ∘
        (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull2 := by
      funext c
      obtain ⟨a, rfl⟩ := H2.mk_surjective _ c; rfl
    rw [e]
    exact h

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeLineBundleIsoOfAppellHumbertAdjoint
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

section Helpers
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AdjPullFrame

open GlobalTheory.ProdUnifSq GlobalTheory.LamPullFrame

variable {g : ℕ}

def twistLeft (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : (Fin (g + g) → ℂ) →ₗ[ℂ] (Fin (g + g) → ℂ) where
  toFun v := Fin.append (Fl (halfL g v)) (halfR g v)
  map_add' v w := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, map_add, Pi.add_apply]
  map_smul' c v := by
    funext q
    refine Fin.addCases (fun k => ?_) (fun k => ?_) q <;>
      simp only [Fin.append_left, Fin.append_right, map_smul, Pi.smul_apply, RingHom.id_apply]

theorem halfL_twistLeft (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (v : Fin (g + g) → ℂ) :
    halfL g (twistLeft Fl v) = Fl (halfL g v) := halfL_append _ _

theorem halfR_twistLeft (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (v : Fin (g + g) → ℂ) :
    halfR g (twistLeft Fl v) = halfR g v := halfR_append _ _

variable {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

theorem comp_psum {T T' : Over (Sp ℂ)} (h : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ A)) (I : Finset (Fin n)) :
    h ≫ psum A x I = psum A (fun k => h ≫ x k) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp [pzero]
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ← ih]
    simp only [padd]
    rw [← Category.assoc, comp_lift]

end GlobalTheory.AdjPullFrame

namespace GlobalTheory.AdjPullFrame

open GlobalTheory.ProdUnifSq GlobalTheory.LamPullFrame

variable {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] [IsCommMonObj A]

theorem ex_twistLeft {M : LB A.left} (u : HolUnif A M g) (f : A ⟶ A) (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hFl : ∀ z, u.ex (Fl z) = u.ex z ≫ f) (I : ULift.{0} (Finset (Fin 2))) (v : Fin (g + g) → ℂ) :
    u.ex ((sumL g I ∘ₗ twistLeft Fl) v) = (sqUnif A u).ex v ≫ psum A ![fst A A ≫ f, snd A A] I.down := by
  have e : (sqUnif A u).ex (twistLeft Fl v) = (sqUnif A u).ex v ≫ lift (fst A A ≫ f) (snd A A) := by
    change lift (u.ex (halfL g (twistLeft Fl v))) (u.ex (halfR g (twistLeft Fl v))) =
      lift (u.ex (halfL g v)) (u.ex (halfR g v)) ≫ lift (fst A A ≫ f) (snd A A)
    rw [halfL_twistLeft, halfR_twistLeft, hFl, comp_lift, lift_fst_assoc, lift_snd]
  rw [LinearMap.comp_apply, ex_sumL u u rfl I, e, Category.assoc, comp_psum]
  have hx : ∀ a b : A ⊗ A ⟶ A, (fun k => lift a b ≫ x2 A k) = ![a, b] := by
    intro a b; funext k; fin_cases k <;> simp [x2]
  rw [hx]

theorem ex_twistRight {M : LB A.left} (u : HolUnif A M g) (f : A ⟶ A) (Fl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hFl : ∀ z, u.ex (Fl z) = u.ex z ≫ f) (I : ULift.{0} (Finset (Fin 2))) (v : Fin (g + g) → ℂ) :
    u.ex ((sumL g I ∘ₗ twistMap Fl) v) = (sqUnif A u).ex v ≫ psum A ![fst A A, snd A A ≫ f] I.down := by
  have e : (sqUnif A u).ex (twistMap Fl v) = (sqUnif A u).ex v ≫ lift (fst A A) (snd A A ≫ f) := by
    change lift (u.ex (halfL g (twistMap Fl v))) (u.ex (halfR g (twistMap Fl v))) =
      lift (u.ex (halfL g v)) (u.ex (halfR g v)) ≫ lift (fst A A) (snd A A ≫ f)
    rw [halfL_twist, halfR_twist, hFl, comp_lift, lift_fst, lift_snd_assoc]
  rw [LinearMap.comp_apply, ex_sumL u u rfl I, e, Category.assoc, comp_psum]
  have hx : ∀ a b : A ⊗ A ⟶ A, (fun k => lift a b ≫ x2 A k) = ![a, b] := by
    intro a b; funext k; fin_cases k <;> simp [x2]
  rw [hx]

end GlobalTheory.AdjPullFrame

end Helpers

open GlobalTheory.LamPullFrame GlobalTheory.ProdUnifSq GlobalTheory.AdjPullFrame in

theorem GlobalTheory.AdjPullFrame.lbIso_cubeLB_of_adjoint : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (N : LB A.left), N.IsLB → Out.RelAmple A N → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ (f f' : A ⟶ A) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsMonHom f → IsMonHom f' → (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f') → (∀ z w, hermForm Hm (F z) w = hermForm Hm z (F' w)) → LBIso (cubeLB A ![fst A A ≫ f, snd A A] M) (cubeLB A ![fst A A, snd A A ≫ f'] M) := by
  intro A _ _ g hA _ N _ hN M u Hm χ hM hF f f' F F' _ _ hFe hF'e hadj
  have hp : IsProjOver A.hom := GlobalTheory.ProjSpace.isProjOver_of_relAmple hN
  obtain ⟨U1, h1ex, h1Λ, h1fr⟩ := GlobalTheory.exists_holUnif_linComb (A ⊗ A) A _ M (g + g) g (sqUnif A u) u
    (ULift.{0} (Finset (Fin 2))) (fun I => psum A ![fst A A ≫ f, snd A A] I.down)
    (fun I => sumL g I ∘ₗ twistLeft F) (fun I => (-1) ^ (2 - I.down.card)) (fun I v => ex_twistLeft u f F hFe I v)
  obtain ⟨U2, h2ex, h2Λ, h2fr⟩ := GlobalTheory.exists_holUnif_linComb (A ⊗ A) A _ M (g + g) g (sqUnif A u) u
    (ULift.{0} (Finset (Fin 2))) (fun I => psum A ![fst A A, snd A A ≫ f'] I.down)
    (fun I => sumL g I ∘ₗ twistMap F') (fun I => (-1) ^ (2 - I.down.card)) (fun I v => ex_twistRight u f' F' hF'e I v)
  let UN := GlobalTheory.SameFactor.divUnif U1 U2 (h2ex.trans h1ex.symm)
  refine GlobalTheory.HolUnifSec.hasGen_of_periodic (A ⊗ A) (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA)
    (GlobalTheory.ProjSpace.isProjOver_pullback hp hp) _
    (LB.isLB_div (LB.isLB_linComb hM _ _) (LB.isLB_linComb hM _ _)) (g + g) UN
    (fun _ => 1) (differentiable_const _) (fun _ => one_ne_zero) ?_
  intro w hw p z hz
  obtain ⟨hz2, hz1⟩ := (top_le_preimage_inf _ _ _).1 hz
  change ⊤ ≤ (U1.ex z).left ⁻¹ᵁ _ at hz1 hz2
  rw [h1ex] at hz1 hz2
  have hw' : w ∈ sqLat u.Λ := by
    have h : w ∈ U1.Λ := hw
    rw [h1Λ] at h
    exact h
  obtain ⟨hl, hr⟩ := (mem_sqLat _ _).1 hw'
  let j1 : (abelian₂ A M).ι := fun I => p.2 I
  let j2 : (abelian₂ A M).ι := fun I => p.1 I
  have hc1 : ⊤ ≤ ((sqUnif A u).ex (twistLeft F z)).left ⁻¹ᵁ (abelian₂ A M).U j1 := by
    refine (GlobalTheory.CubeValues.le_preimage_wchart _ M _ j1).2 (fun I => ?_)
    have h := (GlobalTheory.CubeValues.le_preimage_wchart ((sqUnif A u).ex z).left M
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum A ![fst A A ≫ f, snd A A] I.down).left) p.2).1 hz1 I
    rw [← Over.comp_left, ← ex_twistLeft u f F hFe I z, LinearMap.comp_apply, ex_sumL u u rfl I,
      Over.comp_left] at h
    exact h
  have hc2 : ⊤ ≤ ((sqUnif A u).ex (twistMap F' z)).left ⁻¹ᵁ (abelian₂ A M).U j2 := by
    refine (GlobalTheory.CubeValues.le_preimage_wchart _ M _ j2).2 (fun I => ?_)
    have h := (GlobalTheory.CubeValues.le_preimage_wchart ((sqUnif A u).ex z).left M
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum A ![fst A A, snd A A ≫ f'] I.down).left) p.1).1 hz2 I
    rw [← Over.comp_left, ← ex_twistRight u f' F' hF'e I z, LinearMap.comp_apply, ex_sumL u u rfl I,
      Over.comp_left] at h
    exact h
  have hwt1 : twistLeft F w ∈ sqLat u.Λ := by
    refine (mem_sqLat _ _).2 ⟨?_, by rw [halfR_twistLeft]; exact hr⟩
    rw [halfL_twistLeft, ← u.ker, hFe, (u.ker _).2 hl, MonObj.one_comp]
  have hwt2 : twistMap F' w ∈ sqLat u.Λ := by
    refine (mem_sqLat _ _).2 ⟨by rw [halfL_twist]; exact hl, ?_⟩
    rw [halfR_twist, ← u.ker, hF'e, (u.ker _).2 hr, MonObj.one_comp]
  have fac1 := lam_factor hM u u rfl hF j1 (twistLeft F z) (twistLeft F w) hwt1 hc1
  have fac2 := lam_factor hM u u rfl hF j2 (twistMap F' z) (twistMap F' w) hwt2 hc2
  rw [halfL_twistLeft, halfL_twistLeft, halfR_twistLeft, halfR_twistLeft, ← map_add] at fac1
  rw [halfL_twist, halfL_twist, halfR_twist, halfR_twist, ← map_add] at fac2
  have sw := GlobalTheory.AnyAppellHumbert.hermForm_swap hF.1
  have hE : hf Hm (F (halfL g z)) (halfR g w) + hf Hm (halfR g z) (F (halfL g w)) + hf Hm (F (halfL g w)) (halfR g w) =
      hf Hm (halfL g z) (F' (halfR g w)) + hf Hm (F' (halfR g z)) (halfL g w) + hf Hm (halfL g w) (F' (halfR g w)) := by
    have e1 : hf Hm (F (halfL g z)) (halfR g w) = hf Hm (halfL g z) (F' (halfR g w)) := hadj _ _
    have e3 : hf Hm (F (halfL g w)) (halfR g w) = hf Hm (halfL g w) (F' (halfR g w)) := hadj _ _
    have e2 : hf Hm (halfR g z) (F (halfL g w)) = hf Hm (F' (halfR g z)) (halfL g w) := by
      change hermForm Hm (halfR g z) (F (halfL g w)) = hermForm Hm (F' (halfR g z)) (halfL g w)
      rw [sw (F (halfL g w)) (halfR g z), hadj, ← sw]
    rw [e1, e2, e3]
  rw [hE] at fac1
  have n1 : (lamUnif u u rfl).fr j1 (twistLeft F (z + w)) ≠ 0 := by
    refine (lamUnif u u rfl).fr_ne _ _ ?_
    rw [lamUnif_ex, map_add, ex_add_mem (sqUnif A u) _ hwt1]
    exact hc1
  have n2 : (lamUnif u u rfl).fr j2 (twistMap F' (z + w)) ≠ 0 := by
    refine (lamUnif u u rfl).fr_ne _ _ ?_
    rw [lamUnif_ex, map_add, ex_add_mem (sqUnif A u) _ hwt2]
    exact hc2
  have hP1 : ∀ v, U1.fr p.2 v = (lamUnif u u rfl).fr j1 (twistLeft F v) := fun v => by
    refine (h1fr p.2 v).trans (Eq.trans ?_ (lamUnif_fr u u rfl j1 (twistLeft F v)).symm)
    rfl
  have hP2 : ∀ v, U2.fr p.1 v = (lamUnif u u rfl).fr j2 (twistMap F' v) := fun v => by
    refine (h2fr p.1 v).trans (Eq.trans ?_ (lamUnif_fr u u rfl j2 (twistMap F' v)).symm)
    rfl
  have hUN : ∀ v, UN.fr p v = U2.fr p.1 v * (U1.fr p.2 v)⁻¹ := fun v => rfl
  rw [hUN, hUN, hP1, hP1, hP2, hP2, fac1, fac2]
  have ne := Complex.exp_ne_zero (↑Real.pi * (hf Hm (halfL g z) (F' (halfR g w)) + hf Hm (F' (halfR g z)) (halfL g w) +
    hf Hm (halfL g w) (F' (halfR g w))))
  field_simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalStructureOfPushedPointValuesCubeFunctionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubicalStructure_of_pushed_point_values_cube_function : ∀ {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β), ∀ (L : RigLB G) (t : LB.Gen (Theta G L.L)), t.IsGen → (∀ U, Function.Injective ((lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G2 G).left ⟶ X), (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left ≫ a = (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left ≫ b → a = b) → (∀ U, Function.Injective ((cubeMapOf h).F3.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G3 G).left ⟶ X), (cubeMapOf h).F3 ≫ a = (cubeMapOf h).F3 ≫ b → a = b) → (∀ U, Function.Injective ((lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left.app U).hom) → (∀ {X : Scheme.{0}} (a b : (G4 G).left ⟶ X), (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left ≫ a = (lift (pushPt h.1.w (x4 G' 0)) (lift (pushPt h.1.w (x4 G' 1)) (lift (pushPt h.1.w (x4 G' 2)) (pushPt h.1.w (x4 G' 3))))).left ≫ b → a = b) → (∀ (T : Over S') (z : T.left) (I : (T.left ⟶ G.left) → L.L.ι), Good L.L z I → IsCub (fun a b d : T ⟶ G' => GlobalTheory.CubTransport.thV t z I (pushHom h T a) (pushHom h T b) (pushHom h T d))) → ∃ c : CubicalStr G L, c.t = t := by
  first | exact @GlobalTheory.Mum.cubicalStr_of_push_val | exact GlobalTheory.Mum.cubicalStr_of_push_val | (intros; apply GlobalTheory.Mum.cubicalStr_of_push_val <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLowerBoundBergmanFunctionOnComponentStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_lower_bound_bergmanFunction_on_component : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E) (Z : Comp Xo c) (y : FPt (U σ).X), (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ D.R.r) ∈ framesOn (U σ) Z → ∀ β : ENNReal, (∀ (x0 : Frame ((U σ).X y.1).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd ((U σ).X y.1)))), ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth ((U σ).X y.1) x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet ((U σ).X y.1) x0 FF → ∃ P ∈ ((U σ).X y.1).SS (modelWt (U σ) G y.1), P y.2.1 ≠ 0 ∧ β * ∫⁻ z in FF, ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X y.1) x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0) ≤ ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P y.2.1 ^ 2) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0 FF) → β ≤ bergOn (U σ) (D.sp.W j) (dict σ) Z G y := by
  first | exact @GlobalTheory.BergLower.le_bergOn | exact GlobalTheory.BergLower.le_bergOn | (intros; apply GlobalTheory.BergLower.le_bergOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamBasisBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_basis_base_change : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (𝔠 : FracId (FR E))
    (R : Subring ℂ) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
    (cm : OAct (orderC c) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p → ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)),
    ∃ B : Module.Basis (Fin n) ℂ (HdR X.A), ∀ (a : orderC c) (α : X.A ⟶ X.A) [IsMonHom α],
      α.left ≫ p = p ≫ (cm.act a).left → ∀ i, push (dp0 ℂ) (𝟙 _) α (B i) =
        ∑ k, (((eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) a (Pi.single i 1) k : R) : ℂ) • B k := by
  first | exact @GlobalTheory.DRLine.exists_basis_push_eq_sum | exact GlobalTheory.DRLine.exists_basis_push_eq_sum | (intros; apply GlobalTheory.DRLine.exists_basis_push_eq_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamRankEqCmDegreeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_rank_eq_cm_degree : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔠 : FracId (FR E)) (R : Type)
    [CommRing R] [IsDomain R] (X : Obj (FR E) 𝔠 (Sp R)) (n : ℕ), (HdR X.A ≃ₗ[R] (Fin n → R)) → n = Module.finrank ℚ E := by
  first | exact @GlobalTheory.DeRham.hdR_rank_eq_finrank_cm | exact GlobalTheory.DeRham.hdR_rank_eq_finrank_cm | (intros; apply GlobalTheory.DeRham.hdR_rank_eq_finrank_cm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepCongruenceElementSeparatesChartBallThickFramStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deep_congruence_element_separates_chart_ball_thick_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (M : ℕ) (x : Frame X.Ψ r), GlobalTheory.EqCovol.IsSelfDualTr X → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → 100 * ((X.Ψ.card : ℝ) * r) ^ 4 ≤ (M : ℝ) * X.firstMinimumSq x → ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → (∀ v ∈ X.Λ, ∃ w ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec v - v = M • w) → ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1 := by
  first | exact @GlobalTheory.ThickSep.deep_cong_chart_sep | exact GlobalTheory.ThickSep.deep_cong_chart_sep | (intros; apply GlobalTheory.ThickSep.deep_cong_chart_sep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformationChartPointReductionEqSpecialFibreStatement
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
open GlobalTheory.CechKS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deformationChartPoint_reduction_eq_specialFibre : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {X Z : Scheme.{0}} {h : Z ⟶ X} {y1 : Sp (DualNumber K) ⟶ X} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} (hm' : IsPullback m' A'.hom h y1) (him : i ≫ m' = m) {Ω : Z.affineOpens} {δ : Γ(Z, Ω.1) → Γ(Z, Ω.1)} {n : ℕ} {u : Fin n → (epsR K ⟶ A)} {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ} {B : Type} [CommRing B] [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l : Sp B ⟶ A'.left} (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω.1)) (hl : IsChartPt A' m m' Ω.1 δ u θ Wo g x l), spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ l = spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ x ≫ i := by
  first | exact @GlobalTheory.CechKS.chartPt_red | exact GlobalTheory.CechKS.chartPt_red | (intros; apply GlobalTheory.CechKS.chartPt_red <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformedLatticeValueEqHilbertEisensteinValueStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deformedLattice_value_eq_hilbertEisenstein_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (e : I ≃ Emb (FR E)) (θ : E) (τ : ℍ) (Λ : Set E) (L : Lat (FR E)) (n : ℕ) (k : ℕ) (z : I → ℂ) (G : ℂ), Nonempty I → Even k → (∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ)) → (∀ i, φ i θ = (τ : ℂ)) → 0 < n → (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y ∈ Λ, (n : E) * y = (x 0 : E) * θ + (x 1 : E)) → IsEisValue φ k Λ z G → IsGVal k L (fun j ↦ τ + z (e.symm j) * (1 * τ + (starRingEnd ℂ (τ : ℂ) - τ))) (fun j ↦ 1 + z (e.symm j) * 1) ((((n : ℂ) ^ Module.finrank ℚ (FR E))⁻¹) ^ k * G) := by
  first | exact @GlobalTheory.HilbFam.BrVal.isGVal_of_isEisValue | exact GlobalTheory.HilbFam.BrVal.isGVal_of_isEisValue | (intros; apply GlobalTheory.HilbFam.BrVal.isGVal_of_isEisValue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationExtensionLocalDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.SplitPowEight

def isPowGrpOfUnique {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (pr : Fin j → (G' ⟶ G))
    (hpr : ∀ u, IsMonHom (pr u))
    (hu : ∀ (T : Over S) (y : Fin j → (T ⟶ G)), ∃! x : T ⟶ G', ∀ u, x ≫ pr u = y u) : IsPowGrp G' G j :=
  ⟨pr, hpr, Fan.IsLimit.mk _ (fun s => (hu s.pt s.proj).choose) (fun s u => (hu s.pt s.proj).choose_spec.1 u)
    fun s m hm => (hu s.pt s.proj).choose_spec.2 m hm⟩

def powPullback {S S' : Scheme.{0}} (f : S' ⟶ S) {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}
    (p : IsPowGrp G' G j) : IsPowGrp ((Over.pullback f).obj G') ((Over.pullback f).obj G) j :=
  ⟨fun u => (Over.pullback f).map (p.pr u), fun u => by have := p.hom u; infer_instance,
    isLimitFanMkObjOfIsLimit (Over.pullback f) _ _ p.lim⟩

theorem exists_unif_pow8 : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ ψ : A.A.left ⟶ G.left, IsGrpPullback A.A G (jK V) ψ → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (io : V →+* W) (em : W →+* AlgebraicClosure (FractionRing V)) (D : DegData W (maximalIdeal W)) (Q : PolAV (Sp (FractionRing W))) (H : Over (Sp W)) (_ : GrpObj H) (_ : IsCommMonObj H) (U : Unif (maximalIdeal W) D Q H) (i : (Over.pullback (spMap io)).obj G ⟶ H) (r : Fin 8 → (H ⟶ (Over.pullback (spMap io)).obj G)), GlobalTheory.LN.CDvr W ∧ io.Finite ∧ Function.Injective io ∧ Function.Injective em ∧ (∀ v, em (io v) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ IsSemiAbelian H ∧ GlobalTheory.LN.ToATotal U.toUnifPre ∧ (∀ k, IsMonHom (r k)) ∧ i ≫ r 0 = 𝟙 _ ∧ ∀ (T : Over (Sp W)) (x y : T ⟶ H), (∀ k, x ≫ r k = y ≫ r k) → x = y := by
  intro V _ _ _ hV A G _ _ hG ψ hψ
  obtain ⟨hd, hc, hch⟩ := hV
  obtain ⟨gen, hgen, -⟩ := grpPullback_iso (isGrpPullback_pullback G (jK V)) hψ
  obtain ⟨G8, _, prG, hG8, hprG, huG⟩ := GlobalTheory.MBLow.exists_eighthPower_semiAbelianScheme V G hG
  have : IsCommMonObj G8 := hG8.comm
  let p8 : IsPowGrp G8 G 8 := isPowGrpOfUnique prG hprG huG
  let F := AlgebraicClosure (FractionRing V)
  have : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective V F).2 (by
    rw [IsScalarTower.algebraMap_eq V (FractionRing V) F]
    exact (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _))
  have : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := FractionRing V) (C := F)).2 inferInstance
  obtain ⟨W, hWd, hWc, hWf, hsplit⟩ := GlobalTheory.Ex.UnifModel.exists_split V F G8 hG8
  have : CharZero F := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective V F)
  have : CharZero W := RingHom.charZero (algebraMap W F)
  have hio : Function.Injective (algebraMap V W) := fun a b h =>
    FaithfulSMul.algebraMap_injective V F (congrArg Subtype.val h)
  let io : V →+* W := algebraMap V W
  let H := (Over.pullback (spMap io)).obj G8
  let pH : IsPowGrp H ((Over.pullback (spMap io)).obj G) 8 := powPullback (spMap io) p8
  have hH : IsSemiAbelian H := IsSemiAbelian.pullback _ G8 hG8
  obtain ⟨A', ψ', hψ'⟩ := GlobalTheory.UnifProperOpen.exists_polGeneric_pullback V A G gen hgen W io hio
  obtain ⟨d, -, hQ⟩ := GlobalTheory.MBLow.PowEightField.exists_eighthPower_evenUnimodular_charZero
  obtain ⟨Q, pr, inc, -, hS, hP⟩ := hQ (FractionRing W) A'
  let pQ : IsPowGrp Q.A A'.A 8 := isPowGrpOfUnique pr hP.1 hP.2.2.1
  obtain ⟨φ₀, hφ₀, -⟩ := GlobalTheory.PowFibre.exists_pow_pullback pH pQ hψ'
  obtain ⟨genH, hgenH, -⟩ := grpPullback_iso (isGrpPullback_pullback H (jK W)) hφ₀
  obtain ⟨L₁, -⟩ := GlobalTheory.abelianSchemeLaws_all
  have hE : ∃ E : SplitExt (Sp (ResidueField W)), E.IsGt ((Over.pullback (spMap (residue W))).obj H) := hsplit
  obtain ⟨s, -⟩ := GlobalTheory.ZH.exists_setting_of_hypS L₁ GlobalTheory.homExtension_semiAbelian_dvr_unconditional W hWc Q H hH hE
    hS genH hgenH
  obtain ⟨D, U, -, -, hU⟩ := GlobalTheory.uniformisation_dvr_unconditional W Q H s
  obtain ⟨i₀, hi₀, -⟩ := huG G (fun _ => 𝟙 G)
  refine ⟨W, inferInstance, inferInstance, inferInstance, io, algebraMap W F, D, Q, H, inferInstance, inferInstance, U,
    (Over.pullback (spMap io)).map i₀, pH.pr, ⟨hWd, hWc, inferInstance⟩, RingHom.finite_algebraMap.2 hWf, hio,
    Subtype.val_injective, fun v => ?_, hH, hU, pH.hom, ?_, fun T x y h => Fan.IsLimit.hom_ext pH.lim _ _ h⟩
  · exact IsScalarTower.algebraMap_apply V (FractionRing V) F v
  · show (Over.pullback (spMap io)).map i₀ ≫ (Over.pullback (spMap io)).map (prG 0) = _
    rw [← CategoryTheory.Functor.map_comp, hi₀ 0, CategoryTheory.Functor.map_id]

end GlobalTheory.SplitPowEight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationRescaleTauBimultExistsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degeneration_rescale_tau_bimult_exists : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), ∃ g : D.X → (FractionRing R)ˣ, (GlobalTheory.PolDeg.rescale D g).TauBimult := by
  first | exact @GlobalTheory.RescaleBimult.exists_rescale_tauBimult | exact GlobalTheory.RescaleBimult.exists_rescale_tauBimult | (intros; apply GlobalTheory.RescaleBimult.exists_rescale_tauBimult <;> assumption)
end

