import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2987
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinCoefficientValuationBound
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupMultiplicationDescendsProperSurjection
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GrpDescent

section Pt
variable {S X : Scheme.{0}} (G' : Over S) (f : X ⟶ S)

def ptOf {T : Over X} (a : T.left ⟶ G'.left) (ha : a ≫ G'.hom = T.hom ≫ f) : T ⟶ (Over.pullback f).obj G' :=
  Over.homMk (pullback.lift a T.hom ha) (pullback.lift_snd _ _ _)

theorem ptOf_fst {T : Over X} (a : T.left ⟶ G'.left) (ha : a ≫ G'.hom = T.hom ≫ f) :
    (ptOf G' f a ha).left ≫ pullback.fst G'.hom f = a := pullback.lift_fst _ _ _

theorem ptOf_mul [GrpObj G'] {T : Over X} (w : T.left ⟶ (G' ⊗ G').left) (hw : w ≫ (G' ⊗ G').hom = T.hom ≫ f)
    (h₁ : (w ≫ (fst G' G').left) ≫ G'.hom = T.hom ≫ f) (h₂ : (w ≫ (snd G' G').left) ≫ G'.hom = T.hom ≫ f) :
    (ptOf G' f _ h₁ * ptOf G' f _ h₂).left ≫ pullback.fst G'.hom f = w ≫ μ[G'].left := by
  let U : Over.mk (T.hom ≫ f) ⟶ G' ⊗ G' := Over.homMk w hw
  have e := (isGrpPullback_pullback G' f).2 T (ptOf G' f _ h₁) (ptOf G' f _ h₂) (U ≫ fst G' G') (U ≫ snd G' G')
    (ptOf_fst G' f _ h₁).symm (ptOf_fst G' f _ h₂).symm
  rw [← e, ← MonObj.comp_mul, Hom.mul_def, lift_fst_snd, Category.id_comp]
  rfl

end Pt

theorem mul_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom → pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β → ∃ m : G ⊗ G ⟶ G, ∀ (T : Over S) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → y₀.left = y.left ≫ β → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ β := by
  intro R _ _ _ _ S π hprop hsurj hint G' _ G β hsm hβ φ hφ hdat
  haveI := hsm
  haveI : Smooth (G ⊗ G).hom := inferInstanceAs (Smooth (pullback.fst G.hom G.hom ≫ G.hom))
  have hflat : Flat (G ⊗ G).hom := inferInstance
  let Z' : Over (Sp R) := Over.mk ((G' ⊗ G').hom ≫ π)
  let u : Z' ⟶ G := Over.homMk ((fst G' G').left ≫ β) (by
    show ((fst G' G').left ≫ β) ≫ G.hom = (G' ⊗ G').hom ≫ π
    rw [Category.assoc, hβ.w, ← Category.assoc, Over.w])
  let v : Z' ⟶ G := Over.homMk ((snd G' G').left ≫ β) (by
    show ((snd G' G').left ≫ β) ≫ G.hom = (G' ⊗ G').hom ≫ π
    rw [Category.assoc, hβ.w, ← Category.assoc, Over.w])
  let p : (G' ⊗ G').left ⟶ (G ⊗ G).left := (lift u v).left
  have hp1 : p ≫ (fst G G).left = (fst G' G').left ≫ β := by
    show (lift u v ≫ fst G G).left = _
    rw [lift_fst]; rfl
  have hp2 : p ≫ (snd G G).left = (snd G' G').left ≫ β := by
    show (lift u v ≫ snd G G).left = _
    rw [lift_snd]; rfl
  have hA : IsPullback (fst G' G').left (snd G' G').left G'.hom G'.hom := IsPullback.of_hasPullback _ _
  have hB : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  have htop : IsPullback p (snd G' G').left (snd G G).left β := by
    refine IsPullback.of_right (h₁₂ := (fst G G).left) (h₂₂ := G.hom) ?_ hp2 hB
    rw [hp1, hβ.w]
    exact hA.paste_horiz hβ
  have hpb : IsPullback p (G' ⊗ G').hom (G ⊗ G).hom π := by
    have h := htop.paste_vert hβ
    rwa [Over.w (snd G' G'), Over.w (snd G G)] at h

  have hepi : ∀ {W : Scheme.{0}} (a b : (G ⊗ G).left ⟶ W), p ≫ a = p ≫ b → a = b := by
    intro W a b hab
    obtain ⟨c, -, hc⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S _ _ W π _ p _ hprop hsurj hint hflat hpb (p ≫ a)
      (by rw [← Category.assoc, pullback.condition, Category.assoc])
    exact (hc a rfl).trans (hc b hab.symm).symm

  have heq : pullback.fst p p ≫ μ[G'].left ≫ β = pullback.snd p p ≫ μ[G'].left ≫ β := by
    set f₁ := pullback.fst p p
    set f₂ := pullback.snd p p
    have hf : f₁ ≫ p = f₂ ≫ p := pullback.condition
    have hs : (f₁ ≫ (G' ⊗ G').hom) ≫ π = (f₂ ≫ (G' ⊗ G').hom) ≫ π := by
      rw [Category.assoc, Category.assoc, ← hpb.w, ← Category.assoc, hf, Category.assoc]
    let σ := pullback.lift _ _ hs
    let T₀ : Over (pullback π π) := Over.mk σ
    have hw₁ : f₁ ≫ (G' ⊗ G').hom = T₀.hom ≫ pullback.fst π π := (pullback.lift_fst _ _ hs).symm
    have hw₂ : f₂ ≫ (G' ⊗ G').hom = T₀.hom ≫ pullback.snd π π := (pullback.lift_snd _ _ hs).symm

    have htr : ∀ (a₁ a₂ : T₀.left ⟶ G'.left) (h₁ : a₁ ≫ G'.hom = T₀.hom ≫ pullback.fst π π)
        (h₂ : a₂ ≫ G'.hom = T₀.hom ≫ pullback.snd π π), a₁ ≫ β = a₂ ≫ β →
        ptOf G' (pullback.fst π π) a₁ h₁ ≫ φ.hom = ptOf G' (pullback.snd π π) a₂ h₂ := by
      intro a₁ a₂ h₁ h₂ hb
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · apply hβ.hom_ext
        · rw [Over.comp_left, Category.assoc, Category.assoc, ← hdat, ← Category.assoc, ptOf_fst, ptOf_fst, hb]
        · rw [Category.assoc, pullback.condition, ptOf_fst, h₂, ← Category.assoc]
          exact congrArg (· ≫ pullback.snd π π) (Over.w (ptOf G' (pullback.fst π π) a₁ h₁ ≫ φ.hom))
      · exact (Over.w (ptOf G' (pullback.fst π π) a₁ h₁ ≫ φ.hom)).trans (Over.w (ptOf G' (pullback.snd π π) a₂ h₂)).symm
    have hb₁ : (f₁ ≫ (fst G' G').left) ≫ β = (f₂ ≫ (fst G' G').left) ≫ β := by
      rw [Category.assoc, Category.assoc, ← hp1, ← Category.assoc, hf, Category.assoc]
    have hb₂ : (f₁ ≫ (snd G' G').left) ≫ β = (f₂ ≫ (snd G' G').left) ≫ β := by
      rw [Category.assoc, Category.assoc, ← hp2, ← Category.assoc, hf, Category.assoc]
    have k₁ : (f₁ ≫ (fst G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.fst π π := by rw [Category.assoc, Over.w, hw₁]
    have k₂ : (f₁ ≫ (snd G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.fst π π := by rw [Category.assoc, Over.w, hw₁]
    have l₁ : (f₂ ≫ (fst G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.snd π π := by rw [Category.assoc, Over.w, hw₂]
    have l₂ : (f₂ ≫ (snd G' G').left) ≫ G'.hom = T₀.hom ≫ pullback.snd π π := by rw [Category.assoc, Over.w, hw₂]
    have e₁ := ptOf_mul G' (pullback.fst π π) (T := T₀) f₁ hw₁ k₁ k₂
    have e₂ := ptOf_mul G' (pullback.snd π π) (T := T₀) f₂ hw₂ l₁ l₂
    have hAB : (ptOf G' (pullback.fst π π) (T := T₀) _ k₁ * ptOf G' (pullback.fst π π) (T := T₀) _ k₂) ≫ φ.hom =
        ptOf G' (pullback.snd π π) (T := T₀) _ l₁ * ptOf G' (pullback.snd π π) (T := T₀) _ l₂ := by
      refine ((IsMonHom.monoidHom φ.hom T₀).map_mul _ _).trans ?_
      show (ptOf G' (pullback.fst π π) (T := T₀) _ k₁ ≫ φ.hom) * (ptOf G' (pullback.fst π π) (T := T₀) _ k₂ ≫ φ.hom) = _
      rw [htr _ _ k₁ l₁ hb₁, htr _ _ k₂ l₂ hb₂]
    rw [← Category.assoc f₁, ← e₁, ← Category.assoc f₂, ← e₂, ← hAB, Over.comp_left]
    simp only [Category.assoc]
    rw [hdat]
  obtain ⟨h₀, hh₀, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S _ _ _ π _ p _ hprop hsurj hint hflat hpb (μ[G'].left ≫ β) heq
  have hover : h₀ ≫ G.hom = (G ⊗ G).hom := by
    apply hepi
    rw [← Category.assoc, hh₀, Category.assoc, hβ.w, ← Category.assoc, Over.w μ[G'], hpb.w]
  refine ⟨Over.homMk h₀ hover, fun T x y x₀ y₀ hx hy => ?_⟩
  have hl : (lift x₀ y₀).left = (lift x y).left ≫ p := by
    apply hB.hom_ext
    · rw [Category.assoc, hp1, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, hx]
    · rw [Category.assoc, hp2, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, hy]
  rw [Over.comp_left, hl]
  change ((lift x y).left ≫ p) ≫ h₀ = _
  rw [Category.assoc, hh₀, Hom.mul_def, Over.comp_left, Category.assoc]

end GlobalTheory.GrpDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupUnitDescendsProperSurjection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem pullback_one_left_fst {S P : Scheme.{0}} (f : P ⟶ S) (G' : Over S) [GrpObj G'] :
    (η[(Over.pullback f).obj G'] : _ ⟶ _).left ≫ pullback.fst G'.hom f = f ≫ η[G'].left := by
  simp [Functor.monObjObj]
  rw [← pullback.condition_assoc]; simp
  exact pullback.lift_fst _ _ _

theorem descend_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0})
    (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R))
    (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π →
    ∀ φ : (Over.pullback (pullback.fst π π)).obj G' ≅ (Over.pullback (pullback.snd π π)).obj G', IsMonHom φ.hom →
    pullback.fst G'.hom (pullback.fst π π) ≫ β = φ.hom.left ≫ pullback.fst G'.hom (pullback.snd π π) ≫ β →
    ∃ e : 𝟙_ (Over (Sp R)) ⟶ G, ∀ (T : Over S),
      (toUnit (Over.mk (T.hom ≫ π)) ≫ e).left = (1 : T ⟶ G').left ≫ β := by
  intro R _ _ _ _ S π hP hS hI G' _ G β hβ φ hφ hc
  have sq : IsPullback π (𝟙 S) (𝟙 (Sp R)) π := IsPullback.of_id_snd
  have hfl : Flat (𝟙 (Sp R)) := inferInstance

  have heq : pullback.fst π π ≫ (η[G'].left ≫ β) = pullback.snd π π ≫ (η[G'].left ≫ β) := by
    have h1 := pullback_one_left_fst (pullback.fst π π) G'
    have h2 := pullback_one_left_fst (pullback.snd π π) G'
    have hu : (η : _ ⟶ (Over.pullback (pullback.fst π π)).obj G').left ≫ φ.hom.left =
        (η : _ ⟶ (Over.pullback (pullback.snd π π)).obj G').left := by
      rw [← Over.comp_left, IsMonHom.one_hom]
    calc pullback.fst π π ≫ (η[G'].left ≫ β)
        = (η : _ ⟶ (Over.pullback (pullback.fst π π)).obj G').left ≫ pullback.fst G'.hom (pullback.fst π π) ≫ β := by
          rw [reassoc_of% h1]
      _ = (η : _ ⟶ (Over.pullback (pullback.fst π π)).obj G').left ≫ φ.hom.left ≫
            pullback.fst G'.hom (pullback.snd π π) ≫ β := by rw [hc]
      _ = pullback.snd π π ≫ (η[G'].left ≫ β) := by rw [reassoc_of% hu, reassoc_of% h2]
  obtain ⟨h₀, hh₀, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S G.left π (𝟙 _) π (𝟙 S) hP hS hI hfl sq _ heq

  have hepi : ∀ {W : Scheme.{0}} (a b : Sp R ⟶ W), π ≫ a = π ≫ b → a = b := by
    intro W a b hab
    obtain ⟨c, -, hc'⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (Sp R) S W π (𝟙 _) π (𝟙 S) hP hS hI hfl sq (π ≫ a)
      (by rw [pullback.condition_assoc])
    exact (hc' a rfl).trans (hc' b hab.symm).symm
  have hsec : h₀ ≫ G.hom = 𝟙 (Sp R) := by
    apply hepi
    rw [reassoc_of% hh₀, hβ.w]
    simp
  refine ⟨Over.homMk h₀ (by simpa using hsec), fun T => ?_⟩
  simp [Hom.one_def]
  rw [hh₀]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieMultiplicitySquareZeroLift
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTLiftLie

theorem exists_factor_of_sq_zero {C C₀ k : Type} [CommRing C] [CommRing C₀] [Field k] (π : C →+* C₀)
    (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0) (x : Sp k ⟶ Sp C) :
    ∃ ψ : C₀ →+* k, x = spMap ψ ≫ spMap π := by
  let φ : C →+* k := (Spec.preimage x).hom
  have hx : x = spMap φ := by
    show x = Spec.map (CommRingCat.ofHom (Spec.preimage x).hom)
    simp
  have hker : RingHom.ker π ≤ RingHom.ker φ := by
    intro a ha
    have h2 : a * a ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul ha ha
    rw [hsq] at h2
    have h0 : a * a = 0 := by simpa using h2
    have : φ a * φ a = 0 := by rw [← map_mul, h0, map_zero]
    exact RingHom.mem_ker.2 (mul_self_eq_zero.1 this)
  have hc : (RingHom.liftOfSurjective π hπ ⟨φ, hker⟩).comp π = φ :=
    RingHom.liftOfRightInverse_comp _ _ _ _
  generalize RingHom.liftOfSurjective π hπ ⟨φ, hker⟩ = ψ at hc
  refine ⟨ψ, ?_⟩
  rw [hx, ← hc]
  show Spec.map (CommRingCat.ofHom (ψ.comp π)) = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom π)
  rw [← Spec.map_comp]
  rfl

theorem lieMult_of_sqZeroLift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i) (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp C) (β : R →+* k), x ≫ spMap tR = spMap β → ∀ j, LieMult (act.toF D) x (β.comp (b.t j)) D.m := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ A _ _ i h act hact k _ _ x β hx j
  obtain ⟨ψ, rfl⟩ := exists_factor_of_sq_zero π hπ hsq x
  have hact' : ∀ c, ((o₀.act.toF D).act c).left ≫ i = i ≫ ((act.toF D).act c).left :=
    fun c => hact _
  refine (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) (Sp C) (Sp C₀) A o₀.A (spMap π) i (act.toF D) (o₀.act.toF D)
    h hact' k (spMap ψ) (β.comp (b.t j)) D.m).1 ?_
  exact o₀.lieRank k (spMap ψ) β (by rw [← hx, Category.assoc]) j

end GlobalTheory.HTLiftLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieSpreadFromIdentityPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTLieSpread

theorem prod_ofFn_eq {G : Type} [Monoid G] {V : Type} [AddCommMonoid V] (T : V → G)
    (h0 : T 0 = 1) (hadd : ∀ c c', T (c + c') = T c * T c') :
    ∀ {a : ℕ} (w : Fin a → V), (List.ofFn (fun i => T (w i))).prod = T (∑ i, w i)
  | 0, w => by simp [h0]
  | a + 1, w => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ, hadd, prod_ofFn_eq T h0 hadd (fun i => w i.succ)]

theorem mat_ext {n : ℕ} {C : Type} [CommRing C] {A B : Matrix (Fin n) (Fin n) C}
    (h : ∀ v, A.mulVec v = B.mulVec v) : A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)

theorem isUnit_two_rho_sub {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) : IsUnit (2 * b.ρ - (D.tr : R)) := by
  have hsq : (2 * b.ρ - (D.tr : R)) ^ 2 = ((D.tr ^ 2 - 4 * D.nm : ℤ) : R) := by
    have := b.ρ_root; push_cast; linear_combination 4 * this
  have hd : D.tr ^ 2 - 4 * D.nm = -(((D.tr ^ 2 - 4 * D.nm).natAbs : ℕ) : ℤ) := by
    have := D.disc_neg; omega
  have hcop : ((D.tr ^ 2 - 4 * D.nm).natAbs).Coprime p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out)]
    intro h; exact D.disc_p (Int.natCast_dvd.mpr h)
  have hu := b.unit _ hcop
  rw [← isUnit_pow_iff (n := 2) two_ne_zero, hsq, hd]
  rw [Int.cast_neg, Int.cast_natCast]
  exact hu.neg

def TangentCoordinatesSmoothCommGroupLocalRing : Prop :=
  ∀ (W : Type) [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∃ (n : ℕ) (M : (G ⟶ G) → Matrix (Fin n) (Fin n) W), ∀ (R' : Type) [CommRing R'] (β : W →+* R'),
      ∃ T : (Fin n → R') → (GlobalTheory.UPel.HT.epsPtR (spMap β) ⟶ G), Function.Injective T ∧
        (∀ v : GlobalTheory.UPel.HT.epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left =
          (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) ∧
        (∀ c c', T (c + c') = T c * T c') ∧
        (∀ (s : R') c, (T (s • c)).left = spMap (epsScaleR s) ≫ (T c).left) ∧
        ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map β).mulVec c)

theorem spread_of_coord (hcoord : TangentCoordinatesSmoothCommGroupLocalRing) : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] (tR : R →+* C) (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A], Smooth A.hom → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), GlobalTheory.UPel.HT.LieAt b act tR (spMap (RingHom.id C)) → ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp C), x ≫ spMap tR = spMap β → GlobalTheory.UPel.HT.LieAt b act β x := by
  intro p _ D R _ b C _ _ tR A _ _ hsm act hlie R' _ β x hx
  obtain ⟨g0, rfl⟩ : ∃ g0 : C →+* R', spMap g0 = x := ⟨(Spec.preimage x).hom, by simp [spMap]⟩
  have hg : g0.comp tR = β := by
    have h1 : Spec.map (CommRingCat.ofHom (g0.comp tR)) = Spec.map (CommRingCat.ofHom β) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp]; exact hx
    have h2 := Spec.map_injective h1
    simpa using congrArg CommRingCat.Hom.hom h2
  have hgapp : ∀ r, g0 (tR r) = β r := fun r => by rw [← hg]; rfl
  obtain ⟨n, M, hM⟩ := hcoord C A hsm
  obtain ⟨T1, T1inj, T1rng, T1add, T1sm, T1u⟩ := hM C (RingHom.id C)
  obtain ⟨T0, T0inj, T0rng, T0add, T0sm, T0u⟩ := hM R' g0
  have T1zero : T1 0 = 1 := by
    have h := T1add 0 0; rw [add_zero] at h; exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have T0zero : T0 0 = 1 := by
    have h := T0add 0 0; rw [add_zero] at h; exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have hid : ∀ u : A ⟶ A, (M u).map (RingHom.id C) = M u := fun u => by ext; simp
  let fa : 𝓞 D.F → Matrix (Fin n) (Fin n) C := fun c => M (act.act (algebraMap (𝓞 D.F) D.O c))
  have key : ∀ (c : 𝓞 D.F) v, T1 v ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T1 ((fa c).mulVec v) := fun c v => by
    rw [T1u _ (act.hom _) v, hid]
  have f1 : fa 1 = 1 := mat_ext fun v => T1inj (by
    rw [← key, map_one, act.one, Category.comp_id, Matrix.one_mulVec])
  have fmul : ∀ c d, fa (c * d) = fa c * fa d := fun c d => mat_ext fun v => T1inj (by
    rw [← key, map_mul, act.mul, ← Category.assoc, key, key, Matrix.mulVec_mulVec])
  have fadd : ∀ c d, fa (c + d) = fa c + fa d := fun c d => mat_ext fun v => T1inj (by
    rw [← key, map_add, act.add, MonObj.comp_mul, key, key, ← T1add, Matrix.add_mulVec])
  have f0 : fa 0 = 0 := by
    have h := fadd 0 0; rw [add_zero] at h; exact add_left_cancel (h.symm.trans (add_zero _).symm)
  let f : 𝓞 D.F →+* Matrix (Fin n) (Fin n) C :=
    { toFun := fa, map_one' := f1, map_mul' := fmul, map_zero' := f0, map_add' := fadd }
  have keyf : ∀ (c : 𝓞 D.F) v, T1 v ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T1 ((f c).mulVec v) := key
  have keyg : ∀ (c : 𝓞 D.F) u, T0 u ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T0 (((f c).map g0).mulVec u) :=
    fun c u => T0u _ (act.hom _) u
  have hω : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hρ : (tR b.ρ) ^ 2 - (D.tr : C) * tR b.ρ + (D.nm : C) = 0 := by
    have := congrArg tR b.ρ_root; simpa using this
  have hunit : IsUnit (2 * tR b.ρ - (D.tr : C)) := by
    simpa [map_ofNat] using (isUnit_two_rho_sub b).map tR
  let t : Fin D.a → (𝓞 D.F →+* C) := fun i => tR.comp (b.t i)
  have ht : ∀ i, t i D.ω = tR b.ρ := fun i => by simp [t, b.t_ω]
  have hyp : ∀ v : Fin n → C, (f D.ω).mulVec v = tR b.ρ • v → ∃ w : Fin D.a → Fin n → C,
      (∀ i (c : 𝓞 D.F), (f c).mulVec (w i) = t i c • w i) ∧ v = ∑ i, w i := by
    intro v hv
    obtain ⟨w, hw, hvw⟩ := hlie (T1 v) ⟨(T1rng _).2 ⟨v, rfl⟩, by rw [keyf, hv]; exact T1sm _ _⟩
    choose w' hw' using fun i => (T1rng (w i)).1 (hw i 0).1
    refine ⟨w', fun i c => T1inj ?_, T1inj ?_⟩
    · rw [← keyf, hw' i]
      apply Over.OverMorphism.ext
      rw [T1sm, hw' i]
      exact (hw i c).2
    · rw [hvw, ← prod_ofFn_eq T1 T1zero T1add]
      simp only [hw']
  have L := GlobalTheory.eigen_decomp_base_change (𝓞 D.F) C n D.a D.ω D.tr D.nm hω f (tR b.ρ) hρ hunit t ht hyp R' g0
  intro v hv
  obtain ⟨v', rfl⟩ := (T0rng v).1 hv.1
  obtain ⟨w, hw, hvw⟩ := L v' (T0inj (by
    apply Over.OverMorphism.ext
    rw [← keyg, T0sm, hgapp]
    exact hv.2))
  refine ⟨fun i => T0 (w i), fun i c => ⟨(T0rng _).2 ⟨_, rfl⟩, ?_⟩, ?_⟩
  · rw [keyg, hw i c, T0sm]
    rw [show g0 (t i c) = β (b.t i c) from hgapp _]
  · rw [hvw, prod_ofFn_eq T0 T0zero T0add]

theorem lieAt_spread : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (C : Type) [CommRing C] [IsLocalRing C] (tR : R →+* C) (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A], Smooth A.hom → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), GlobalTheory.UPel.HT.LieAt b act tR (spMap (RingHom.id C)) → ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp C), x ≫ spMap tR = spMap β → GlobalTheory.UPel.HT.LieAt b act β x :=
  spread_of_coord GlobalTheory.T.exists_tangent_coords_base_change_smooth_comm_group

end GlobalTheory.HTLieSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDivisorOfForallCompleteDvrPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDivisor_of_forall_complete_dvr_points : ∀ (k Ω : Type) [CommRing k] [IsNoetherianRing k] [Field Ω] [CharZero Ω] [Algebra k Ω] (M : RatModel k Ω) (J J' : Type) [Fintype J] (th : J → Ω) (e : J' → Ω) (D : ℕ), 1 ≤ D → Geo.Tor.IsNormalScheme M.Z → M.HasDiv e → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (ξ : Sp V ⟶ M.Z) (emb : Ω →+* FractionRing V), jK V ≫ ξ = spMap emb ≫ M.pt → ∀ j₀, e j₀ ≠ 0 → (∀ j, emb (e j / e j₀) ∈ Set.range (algebraMap V (FractionRing V))) → (∀ b, emb (th b ^ D / e j₀) ∈ Set.range (algebraMap V (FractionRing V))) ∧ ∃ b, th b ≠ 0 ∧ emb (e j₀ / th b ^ D) ∈ Set.range (algebraMap V (FractionRing V))) → M.HasDiv th := by
  first | exact @GlobalTheory.ValCmp.hasDiv_of_forall_cDvr | exact GlobalTheory.ValCmp.hasDiv_of_forall_cDvr | (intros; apply GlobalTheory.ValCmp.hasDiv_of_forall_cDvr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFrameFormNormSqEqStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_frame_form_norm_sq_eq : ∀ (n : ℕ) (K A : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n → ℝ) (z : ReciprocityTheory.L2DbarEstimates.V n),
    GlobalTheory.HermFrame.MContDiffAt 2 K z → (∀ᶠ x in nhds z, (K x).PosDef) → (∀ a b, AnalyticAt ℂ (fun x => A x a b) z) → IsUnit (A z).det → v z = 1 →
    (∀ᶠ x in nhds z, ‖GlobalTheory.HermFrame.form (K x) (Pi.single (Sum.inl 0) 1) (fun i => A x i (Sum.inl 0))‖ ^ 2 =
      v x * (GlobalTheory.HermFrame.chg (A x) (K x) (Sum.inl 0) (Sum.inl 0)).re * (K x (Sum.inl 0) (Sum.inl 0)).re) →
    ((ofValues (GlobalTheory.HermFrame.ddc (fun x => 1 - v x) z) : Ev n) : Alt n) *
      (((ofValues (GlobalTheory.HermFrame.extTrace (fun x => GlobalTheory.HermFrame.chg (A x) (K x)) z) : Ev n) : Alt n) -
        ((ofValues (GlobalTheory.HermFrame.extTrace K z) : Ev n) : Alt n)) = 0 := by
  first | exact @GlobalTheory.LineForm.ddc_sinSq_mul_extTrace_sub | exact GlobalTheory.LineForm.ddc_sinSq_mul_extTrace_sub | (intros; apply GlobalTheory.LineForm.ddc_sinSq_mul_extTrace_sub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinCoefficientValuationBoundStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisenstein_coefficient_valuation_bound : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ [IsGalois ℚ F] (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (κ : Emb F → ℕ) (Ch : ℍ → ℂ) (M b : ℕ) (e ρ₀ ρ : ℝ), 0 ≤ e → (∀ C, -(padicValRat l (z C / 2 ^ Module.finrank ℚ F) : ℝ) ≤ e) → ¬ l ∣ M → ![0, ((M * l ^ b : ℕ) : F)] ∈ L → (∀ v ∈ L, ∀ i : Emb F, Sz l lam ρ₀ ((i (v 0) : ℝ) : ℂ)) → b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀ ≤ ρ → QAll (Sz l lam ρ) N Ch → QAll (Sz l lam (e + s * (padicValInt l (discr F) : ℝ) + 2 * s * b * Module.finrank ℚ F + (∑ i, κ i : ℕ) * ρ)) N (hfun (2 * s) L κ Ch) := by
  first | exact @GlobalTheory.HilbFam.sz_hfun_coef | exact GlobalTheory.HilbFam.sz_hfun_coef | (intros; apply GlobalTheory.HilbFam.sz_hfun_coef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetAddDirectionStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_eisenstein_jet_add_direction : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ c t v : ℂ) (κ : Emb F → ℕ), 0 < τ.im → jet (2 * s) L κ τ (c + v) t = ∑ μ ∈ Finset.Iic κ, ((∏ i, rco (2 * s) (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i)) * jet (2 * s) L μ τ c t := by
  first | exact @GlobalTheory.HilbFam.jet_add_dir_of_hasLevel | exact GlobalTheory.HilbFam.jet_add_dir_of_hasLevel | (intros; apply GlobalTheory.HilbFam.jet_add_dir_of_hasLevel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetAlgebraicQCoefficientsStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_eisenstein_jet_algebraic_q_coefficients : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (κ : Emb F → ℕ) (Ch : ℍ → ℂ), QAll (IsAlgebraic ℚ) N Ch → QAll (IsAlgebraic ℚ) N (hfun (2 * s) L κ Ch) := by
  first | exact @GlobalTheory.HilbFam.qAll_isAlgebraic_hfun | exact GlobalTheory.HilbFam.qAll_isAlgebraic_hfun | (intros; apply GlobalTheory.HilbFam.qAll_isAlgebraic_hfun <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetGaloisConjCoefficientsStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_eisenstein_jet_galois_conj_coefficients : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (g : ℂ ≃+* ℂ) (m : ℤ) (κ κ' : Emb F → ℕ) (Ch Ch' : ℍ → ℂ), IsCoprime m (N : ℤ) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ i j : Emb F, (∀ y : F, g ((i y : ℝ) : ℂ) = ((j y : ℝ) : ℂ)) → κ' j = κ i) → QConj g N Ch Ch' → QConj g N (hfun (2 * s) L κ Ch) (hfun (2 * s) (twist N L (Matrix.diagonal ![1, (m : ZMod N)])) κ' Ch') := by
  first | exact @GlobalTheory.HilbFam.qConj_hfun_twist | exact GlobalTheory.HilbFam.qConj_hfun_twist | (intros; apply GlobalTheory.HilbFam.qConj_hfun_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetSmulDirectionStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_eisenstein_jet_smul_direction : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ c t v : ℂ) (κ : Emb F → ℕ), 0 < τ.im → jet (2 * s) L κ τ (v * c) (v * t) = v ^ (∑ i, κ i) * jet (2 * s) L κ τ c t := by
  first | exact @GlobalTheory.HilbFam.jet_smul_dir_of_hasLevel | exact GlobalTheory.HilbFam.jet_smul_dir_of_hasLevel | (intros; apply GlobalTheory.HilbFam.jet_smul_dir_of_hasLevel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateMapOpenImmersionStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_map_open_immersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (P' : GlobalTheory.HTMap.FP t ξ (p ^ n)) (x0 : R →+* 𝓞_ℂ_[p]) (hu : IsUnit (x0 P'.f)) (P : PtP E p) (π : P.G.left ⟶ t.G.left) (hg : IsGrpPullback P.G t.G (spMap x0 ≫ ξ) π) (h : aH P' x0 hu hg.1 ^ (p ^ n) = 1), IsOpenImmersion (jH P' x0 hu hg.1 h).left := by
  first | exact @GlobalTheory.FinPartOpen.isOpenImmersion_jH | exact GlobalTheory.FinPartOpen.isOpenImmersion_jH | (intros; apply GlobalTheory.FinPartOpen.isOpenImmersion_jH <;> assumption)
end
end

