import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2348

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOneProdKernel
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RigDesc

theorem isPullback_one_prod {S : Scheme.{0}} (A : Over S) {V V' : Over S} (v : V ⟶ V') :
    IsPullback (lift (fst A V) (snd A V ≫ v)).left (snd A V).left (snd A V').left v.left := by
  have hT : IsPullback (fst A V).left (snd A V).left A.hom V.hom := IsPullback.of_hasPullback _ _
  have hY : IsPullback (fst A V').left (snd A V').left A.hom V'.hom := IsPullback.of_hasPullback _ _
  have m₁ : (lift (fst A V) (snd A V ≫ v)).left ≫ (fst A V').left = (fst A V).left := by
    rw [← Over.comp_left, lift_fst]
  have m₂ : (lift (fst A V) (snd A V ≫ v)).left ≫ (snd A V').left = (snd A V).left ≫ v.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hT' : IsPullback ((lift (fst A V) (snd A V ≫ v)).left ≫ (fst A V').left) (snd A V).left A.hom
      (v.left ≫ V'.hom) := by
    rw [m₁, Over.w v]; exact hT
  exact IsPullback.of_right hT' m₂ hY

theorem isPullback_one_prod_kernel {S : Scheme.{0}} (A Y Y' W : Over S) (c : Y' ⟶ Y) (w₁ w₂ : W ⟶ Y')
    (hK : IsPullback w₁.left w₂.left c.left c.left) :
    IsPullback (lift (fst A W) (snd A W ≫ w₁)).left (lift (fst A W) (snd A W ≫ w₂)).left
      (lift (fst A Y') (snd A Y' ≫ c)).left (lift (fst A Y') (snd A Y' ≫ c)).left := by
  have Hc := isPullback_one_prod A c
  have H₂ := isPullback_one_prod A w₂
  have outer := H₂.flip.paste_horiz hK
  have e₁ : (lift (fst A W) (snd A W ≫ w₁)).left ≫ (snd A Y').left = (snd A W).left ≫ w₁.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have e₂ : (lift (fst A Y') (snd A Y' ≫ c)).left ≫ (snd A Y).left = (snd A Y').left ≫ c.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  have hw : w₁ ≫ c = w₂ ≫ c := Over.OverMorphism.ext hK.w
  refine IsPullback.of_right (h₁₂ := (snd A Y').left) (h₂₂ := (snd A Y).left) ?_ ?_ Hc.flip
  · rw [e₁, e₂]; exact outer
  · rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, lift_fst, lift_fst, lift_snd_assoc,
      lift_snd_assoc, Category.assoc, Category.assoc, hw]

theorem triv_of_triv_zero_of_fpqc : ∀ (S : Scheme.{0}) (X Y Y' : Over S) [GrpObj X], IsAbelianScheme X →
    ∀ (c : Y' ⟶ Y), Flat c.left → Surjective c.left → QuasiCompact c.left → ∀ D : LB (X ⊗ Y).left, D.IsLB →
    Triv (ev D (1 : Y ⟶ X) (𝟙 Y)) → Triv (ev D (fst X Y') (snd X Y' ≫ c)) → Triv D := by
  intro S X Y Y' _ hA c hfl hsu hqc L hL h0 h1
  let F : X ⊗ Y' ⟶ X ⊗ Y := lift (fst X Y') (snd X Y' ≫ c)
  let e : Y ⟶ X ⊗ Y := lift 1 (𝟙 Y)
  let e' : Y' ⟶ X ⊗ Y' := lift 1 (𝟙 Y')
  change Triv (L.pull e.left) at h0
  change Triv (L.pull F.left) at h1
  have hEF : e' ≫ F = c ≫ e := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [e, e', F]
  have hep : e' ≫ snd X Y' = 𝟙 Y' := lift_snd _ _
  have H : IsPullback F.left (snd X Y').left (snd X Y).left c.left := isPullback_one_prod X c
  have hF₁ : Flat F.left := MorphismProperty.of_isPullback H.flip hfl
  have hF₂ : Surjective F.left := MorphismProperty.of_isPullback H.flip hsu
  have hF₃ : QuasiCompact F.left := MorphismProperty.of_isPullback H.flip hqc
  let W : Over S := Over.mk (pullback.fst c.left c.left ≫ Y'.hom)
  let w₁ : W ⟶ Y' := Over.homMk (pullback.fst c.left c.left) rfl
  let w₂ : W ⟶ Y' := Over.homMk (pullback.snd c.left c.left) (by
    show pullback.snd c.left c.left ≫ Y'.hom = pullback.fst c.left c.left ≫ Y'.hom
    rw [← Over.w c, ← Category.assoc, ← pullback.condition, Category.assoc])
  have hw : w₁ ≫ c = w₂ ≫ c := Over.OverMorphism.ext pullback.condition
  have hK : IsPullback w₁.left w₂.left c.left c.left := IsPullback.of_hasPullback c.left c.left
  let g₁ : X ⊗ W ⟶ X ⊗ Y' := lift (fst X W) (snd X W ≫ w₁)
  let g₂ : X ⊗ W ⟶ X ⊗ Y' := lift (fst X W) (snd X W ≫ w₂)
  have hKP : IsPullback g₁.left g₂.left F.left F.left := isPullback_one_prod_kernel X Y Y' W c w₁ w₂ hK
  have hg : g₁.left ≫ F.left = g₂.left ≫ F.left := hKP.w
  obtain ⟨g, hgg⟩ := h0
  obtain ⟨t, ht⟩ := h1
  have n₁ : (snd X Y' ≫ e').left ≫ F.left = (snd X Y' ≫ c).left ≫ e.left := by
    rw [← Over.comp_left, ← Over.comp_left, Category.assoc, hEF, Category.assoc]
  obtain ⟨t', ht', hv⟩ := exists_gen hL (K' := PUnit) (φ' := fun _ => F.left) (ε' := fun _ => 1)
    (fun U _ k => by
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, n₁]
      simp)
    (LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (snd X Y' ≫ e').left)))
      (LB.pullGen L _ _ g (snd X Y' ≫ c).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
      (DVR.pullGen_isGen _ _ _ _ hgg _))
  have norm : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y'.left) (z : Z) (J), Geo.Tor.Good L z J →
      val t' (r ≫ e'.left) z J = val g (r ≫ c.left) z J := by
    intro Z r z J hJ
    have a₁ : (r ≫ e'.left) ≫ (snd X Y' ≫ e').left = r ≫ e'.left := by
      rw [Category.assoc, ← Over.comp_left, ← Category.assoc e', hep, Category.id_comp]
    have a₂ : (r ≫ e'.left) ≫ (snd X Y' ≫ c).left = r ≫ c.left := by
      rw [Category.assoc, ← Over.comp_left, ← Category.assoc e', hep, Category.id_comp]
    rw [hv Z _ z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, a₁, a₂, mul_inv_cancel,
      _root_.one_mul]
  refine GlobalTheory.FlatDescent.triv_of_gen_descent L hL F.left hF₁ hF₂ hF₃ g₁.left g₂.left hKP t' ht' (fun z J hJ => ?_)
  let o : W ⟶ X ⊗ W := lift 1 (𝟙 W)
  have hg1 : o.left ≫ g₁.left = w₁.left ≫ e'.left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [o, g₁, e']
  have hg2 : o.left ≫ g₂.left = w₂.left ≫ e'.left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [o, g₂, e']
  have ho : o.left ≫ (snd X W).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
  have hwc : w₁.left ≫ c.left = w₂.left ≫ c.left := by rw [← Over.comp_left, ← Over.comp_left, hw]
  have key2 := gen_unique' hL (φ := fun _ : PUnit => g₁.left ≫ F.left) (ε := fun _ => (1 : ℤ))
    (φ' := fun _ : PUnit => g₂.left ≫ F.left) (ε' := fun _ => 1)
    (fun U _ k => by simp only [hg]) (snd X W).left o.left ho (surj_snd GlobalTheory.SemiRigid.globalFns hA W)
    (u := LB.pullGen L _ _ t' g₁.left) (u' := LB.pullGen L _ _ t' g₂.left)
    (DVR.pullGen_isGen _ _ _ _ ht' _) (DVR.pullGen_isGen _ _ _ _ ht' _)
    (fun y I hI => by rw [val_pull hI, val_pull hI, hg1, hg2, norm _ _ _ _ hI, norm _ _ _ _ hI, hwc])
    _ (𝟙 _) z J hJ
  rwa [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at key2

end GlobalTheory.RigDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutLocalizedPresentationBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

section LocalizationBaseChange

variable {R R' C' L ν σ : Type} [CommRing R] [CommRing R'] [CommRing C'] [CommRing L] (a : R →+* R')
  [Algebra R' C'] [Algebra C' L] (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R) (ξ : ν → C')

theorem localization_baseChange_ext (hsurj : Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C'))
    [IsLocalization.Away (MvPolynomial.aeval ξ (MvPolynomial.map a h)) L] {T : Type} [CommRing T]
    (w₁ w₂ : L →+* T)
    (h₁ : ∀ r : R', w₁ (algebraMap C' L (algebraMap R' C' r)) = w₂ (algebraMap C' L (algebraMap R' C' r)))
    (h₂ : ∀ i, w₁ (algebraMap C' L (ξ i)) = w₂ (algebraMap C' L (ξ i))) : w₁ = w₂ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (MvPolynomial.aeval ξ (MvPolynomial.map a h)))
  refine RingHom.ext fun c => ?_
  obtain ⟨P, rfl⟩ := hsurj c
  have e : w₁.comp ((algebraMap C' L).comp (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom) =
      w₂.comp ((algebraMap C' L).comp (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa using h₁ r
    · intro i
      simpa using h₂ i
  exact congr($e P)

theorem localization_baseChange_desc (hsurj : Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C'))
    (hker : ∀ G : MvPolynomial ν R', MvPolynomial.aeval ξ G = 0 →
      MvPolynomial.map a h * G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)))
    [IsLocalization.Away (MvPolynomial.aeval ξ (MvPolynomial.map a h)) L] {T : Type} [CommRing T]
    (u : Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) →+* T) (v : R' →+* T)
    (huv : ∀ r : R, u (algebraMap R _ r) = v (a r)) :
    ∃ w : L →+* T, (∀ G : MvPolynomial ν R, w (algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a G))) =
        u (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ G))) ∧
      ∀ r : R', w (algebraMap C' L (algebraMap R' C' r)) = v r := by
  let θ : MvPolynomial ν R' →+* T := MvPolynomial.eval₂Hom v (fun i ↦
    u (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ (MvPolynomial.X i))))
  have hθ : θ.comp (MvPolynomial.map a) = u.comp ((algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F))
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h))).comp (Ideal.Quotient.mk _)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.map_C, θ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      rw [← huv]
      rfl
    · intro i
      simp [θ]
  have hθ' : ∀ G, θ (MvPolynomial.map a G) =
      u (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ G)) :=
    fun G ↦ congr($hθ G)
  have hunit : IsUnit (θ (MvPolynomial.map a h)) := by
    rw [hθ']
    exact (IsLocalization.Away.algebraMap_isUnit _).map u
  have hspan : Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ≤ RingHom.ker θ := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, hθ', (Ideal.Quotient.eq_zero_iff_mem (a := F s) (I := Ideal.span (Set.range F))).2 (Ideal.subset_span ⟨s, rfl⟩),
      map_zero, map_zero]
  have hk : RingHom.ker (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom ≤ RingHom.ker θ := by
    intro G hG
    rw [RingHom.mem_ker] at hG
    have e := RingHom.mem_ker.1 (hspan (hker G hG))
    rw [map_mul] at e
    exact RingHom.mem_ker.2 ((hunit.mul_right_eq_zero).1 e)
  let θ' : C' →+* T := (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom.liftOfRightInverse
    (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨θ, hk⟩
  have hθ'e : ∀ P, θ' (MvPolynomial.aeval ξ P) = θ P := fun P ↦
    RingHom.liftOfRightInverse_comp_apply _ _ _ _ P
  have hu2 : IsUnit (θ' (MvPolynomial.aeval ξ (MvPolynomial.map a h))) := by
    rw [hθ'e]
    exact hunit
  refine ⟨IsLocalization.Away.lift (MvPolynomial.aeval ξ (MvPolynomial.map a h)) hu2, fun G ↦ ?_, fun r ↦ ?_⟩
  · rw [IsLocalization.Away.lift_eq, hθ'e, hθ']
  · rw [IsLocalization.Away.lift_eq, ← MvPolynomial.aeval_C (R := R') ξ r, hθ'e]
    simp [θ]

end LocalizationBaseChange

theorem isPushout_localization_baseChange : ∀ (R R' C' L ν σ : Type) [CommRing R] [CommRing R'] [CommRing C'] [CommRing L] (a : R →+* R') [Algebra R' C'] [Algebra C' L] (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R) (ξ : ν → C'), Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') → (∀ s, MvPolynomial.aeval ξ (MvPolynomial.map a (F s)) = 0) → (∀ G : MvPolynomial ν R', MvPolynomial.aeval ξ G = 0 → MvPolynomial.map a h * G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s))) → IsLocalization.Away (MvPolynomial.aeval ξ (MvPolynomial.map a h)) L → ∃ α : Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) →+* L, IsPushout (CommRingCat.ofHom (algebraMap R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)))) (CommRingCat.ofHom a) (CommRingCat.ofHom α) (CommRingCat.ofHom ((algebraMap C' L).comp (algebraMap R' C'))) ∧ ∀ G : MvPolynomial ν R, α (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ G)) = algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a G)) := by
  intro R R' C' L ν σ _ _ _ _ a _ _ F h ξ hsurj hF hker hL
  have hI : Ideal.span (Set.range F) ≤
      RingHom.ker ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom.comp (MvPolynomial.map a)) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨s, rfl⟩
    exact RingHom.mem_ker.2 (hF s)
  let β := Ideal.Quotient.lift (Ideal.span (Set.range F))
    ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C').toRingHom.comp (MvPolynomial.map a))
    (fun x hx ↦ RingHom.mem_ker.1 (hI hx))
  have hβ : ∀ G, β (Ideal.Quotient.mk _ G) = MvPolynomial.aeval ξ (MvPolynomial.map a G) := fun G ↦ rfl
  have hu : IsUnit (((algebraMap C' L).comp β) (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) := by
    rw [RingHom.comp_apply, hβ]
    exact IsLocalization.Away.algebraMap_isUnit _
  let α : Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) →+* L :=
    IsLocalization.Away.lift (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) hu
  have hα : ∀ G : MvPolynomial ν R, α (algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _
      (Ideal.Quotient.mk _ G)) = algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a G)) := fun G ↦ by
    simp only [α]
    rw [IsLocalization.Away.lift_eq, RingHom.comp_apply, hβ]
  have hR : ∀ r : R, algebraMap R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) r =
      algebraMap (MvPolynomial ν R ⧸ Ideal.span (Set.range F)) _ (Ideal.Quotient.mk _ (MvPolynomial.C r)) :=
    fun r ↦ rfl
  refine ⟨α, IsPushout.of_isColimit' ⟨?_⟩ (PushoutCocone.IsColimit.mk _
    (fun s ↦ CommRingCat.ofHom (Classical.choose (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r))))) ?_ ?_ ?_), hα⟩
  · ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [hR, hα]
    simp
  · intro s
    obtain ⟨hd1, -⟩ := Classical.choose_spec (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r)))
    apply CommRingCat.hom_ext
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    apply IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range F)) h))
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun G ↦ ?_
    simp only [RingHom.comp_apply]
    rw [hα, hd1]
  · intro s
    obtain ⟨-, hd2⟩ := Classical.choose_spec (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r)))
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    exact hd2 r
  · intro s m h₁ h₂
    obtain ⟨hd1, hd2⟩ := Classical.choose_spec (localization_baseChange_desc (L := L) a F h ξ hsurj hker s.inl.hom s.inr.hom
      (fun r ↦ congr($(s.condition) r)))
    apply CommRingCat.hom_ext
    simp only [CommRingCat.hom_ofHom]
    apply localization_baseChange_ext a h ξ hsurj
    · intro r
      rw [hd2]
      exact congr($h₂ r)
    · intro i
      have e : algebraMap C' L (ξ i) = algebraMap C' L (MvPolynomial.aeval ξ (MvPolynomial.map a (MvPolynomial.X i))) := by
        simp
      rw [e, hd1, ← hα]
      exact congr($h₁ _)

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiAffineCartierSectionGeneratingLocusAmple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.LocusQA

open GlobalTheory.Cartier.CartierDiv

variable {Y : Scheme.{0}} [IsIntegral Y] {y : Y}

theorem regAt_pow {f : Y.functionField} (hf : RegAt y f) (n : ℕ) : RegAt y (f ^ n) := by
  obtain ⟨a, rfl⟩ := hf
  exact ⟨a ^ n, map_pow _ _ _⟩

theorem unitAt_pow_iff {f : Y.functionField} (hf : RegAt y f) {n : ℕ} (hn : n ≠ 0) :
    UnitAt y (f ^ n) ↔ UnitAt y f := by
  obtain ⟨a, rfl⟩ := hf
  refine ⟨fun ⟨b, hb, e⟩ => ?_, fun ⟨b, hb, e⟩ => ⟨b ^ n, hb.pow n, by rw [map_pow, e]⟩⟩
  rw [← map_pow] at e
  obtain rfl := IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField e
  exact ⟨a, (isUnit_pow_iff hn).1 hb, rfl⟩

theorem regAt_div {f g : Y.functionField} (hf : RegAt y f) (hg : UnitAt y g) : RegAt y (f / g) := by
  rw [div_eq_mul_inv]; exact hf.mul hg.inv.regAt

theorem unitAt_div_iff {f g : Y.functionField} (hg : UnitAt y g) : UnitAt y (f / g) ↔ UnitAt y f := by
  refine ⟨fun h => ?_, fun h => by rw [div_eq_mul_inv]; exact h.mul hg.inv⟩
  have := h.mul hg
  rwa [div_mul_cancel₀ _ hg.ne_zero] at this

theorem pow_div_pow_eqn {K : Type} [Field K] (a b c : K) (hc : c ≠ 0) (m n : ℕ) :
    (a * c ^ m) ^ n / (b * c ^ n) ^ m = a ^ n / b ^ m := by
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm m n, mul_div_mul_right _ _ (pow_ne_zero _ hc)]

theorem isQuasiAffine_locus : ∀ (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (D : CartierDiv Y), AmpleDiv D → ∀ (k : ℕ), 1 ≤ k → ∀ s ∈ Sec D k, ∀ V : Y.Opens,
    (V : Set Y) = locus D k s → V.toScheme.IsQuasiAffine := by
  intro Y _ _ _ D hD k hk s hs V hV
  have memV : ∀ y, y ∈ V ↔ (k • D).GeneratesAt y s := fun y => by
    rw [← SetLike.mem_coe, hV]; rfl
  have loc : ∀ (y : Y) (e : Y.functionFieldˣ), D.IsEqn y e →
      RegAt y (s * (e : Y.functionField) ^ k) ∧ (y ∈ V ↔ UnitAt y (s * (e : Y.functionField) ^ k)) := by
    intro y e he
    have h := he.nsmul k
    have h1 := h.regularAt_iff.1 (hs y)
    have h2 := (memV y).trans h.generatesAt_iff
    rw [Units.val_pow_eq_pow_val] at h1 h2
    exact ⟨h1, h2⟩
  have stepC : ∀ k', 1 ≤ k' → ∀ u ∈ Sec D k', ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y) = locus D k' u →
      IsAffineOpen (V ⊓ U) := by
    intro k' hk' u hu U hUa hUl
    have memU : ∀ y, y ∈ U ↔ (k' • D).GeneratesAt y u := fun y => by
      rw [← SetLike.mem_coe, hUl]; rfl
    have locU : ∀ (y : Y) (e : Y.functionFieldˣ), D.IsEqn y e →
        (y ∈ U ↔ UnitAt y (u * (e : Y.functionField) ^ k')) := by
      intro y e he
      have h := he.nsmul k'
      have h2 := (memU y).trans h.generatesAt_iff
      rw [Units.val_pow_eq_pow_val] at h2
      exact h2
    by_cases hg : genericPoint Y ∈ U
    swap
    · have : U = ⊥ := eq_bot_iff.2 fun y hy => (hg (gen_mem hy)).elim
      rw [this, inf_bot_eq]
      exact isAffineOpen_bot Y
    have hreg : ∀ y ∈ U, RegAt y (s ^ k' / u ^ k) := by
      intro y hy
      obtain ⟨e, he⟩ := D.exists_isEqn y
      have hB := (locU y e he).1 hy
      rw [← pow_div_pow_eqn s u _ e.ne_zero k k']
      exact regAt_div (regAt_pow (loc y e he).1 _) ((unitAt_pow_iff hB.regAt (by omega)).2 hB)
    obtain ⟨a, ha⟩ := exists_fnOf_eq hg hreg
    have e₁ : V ⊓ U = Y.basicOpen a := by
      ext y
      refine ⟨fun ⟨hyV, hyU⟩ => ?_, fun hy => ?_⟩
      · obtain ⟨e, he⟩ := D.exists_isEqn y
        have hB := (locU y e he).1 hyU
        refine (unitAt_fnOf_iff hyU hg a).1 ?_
        rw [ha, ← pow_div_pow_eqn s u _ e.ne_zero k k', unitAt_div_iff ((unitAt_pow_iff hB.regAt (by omega)).2 hB),
          unitAt_pow_iff (loc y e he).1 (by omega)]
        exact (loc y e he).2.1 hyV
      · have hyU : y ∈ U := Y.basicOpen_le a hy
        obtain ⟨e, he⟩ := D.exists_isEqn y
        have hB := (locU y e he).1 hyU
        have h := (unitAt_fnOf_iff hyU hg a).2 hy
        rw [ha, ← pow_div_pow_eqn s u _ e.ne_zero k k', unitAt_div_iff ((unitAt_pow_iff hB.regAt (by omega)).2 hB),
          unitAt_pow_iff (loc y e he).1 (by omega)] at h
        exact ⟨(loc y e he).2.2 h, hyU⟩
    rw [e₁]
    exact hUa.basicOpen a
  have : CompactSpace V := by
    choose kk hkk u hu U hUa hUl hxU using hD
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (U y : Set Y)) (fun y => (U y).isOpen)
      (fun y _ => Set.mem_iUnion.2 ⟨y, hxU y⟩)
    have e : (V : Set Y) = ⋃ y ∈ t, ((V ⊓ U y : Y.Opens) : Set Y) := by
      refine Set.Subset.antisymm (fun z hz => ?_) (Set.iUnion₂_subset fun y _ => fun z hz => hz.1)
      obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ z))
      exact Set.mem_iUnion₂.2 ⟨y, hy, hz, hzy⟩
    have hc : IsCompact (V : Set Y) := e ▸ t.isCompact_biUnion fun y _ =>
      (stepC (kk y) (hkk y) (u y) (hu y) (U y) (hUa y) (hUl y)).isCompact
    exact isCompact_iff_compactSpace.mp hc
  have : CompactSpace V.toScheme := inferInstanceAs (CompactSpace V)
  refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen _ fun x => ?_
  obtain ⟨k', hk', u, hu, U, hUa, hUl, hxU⟩ := hD x.1
  have memU : ∀ y, y ∈ U ↔ (k' • D).GeneratesAt y u := fun y => by
    rw [← SetLike.mem_coe, hUl]; rfl
  have locU : ∀ (y : Y) (e : Y.functionFieldˣ), D.IsEqn y e →
      RegAt y (u * (e : Y.functionField) ^ k') ∧ (y ∈ U ↔ UnitAt y (u * (e : Y.functionField) ^ k')) := by
    intro y e he
    have h := he.nsmul k'
    have h1 := h.regularAt_iff.1 (hu y)
    have h2 := (memU y).trans h.generatesAt_iff
    rw [Units.val_pow_eq_pow_val] at h1 h2
    exact ⟨h1, h2⟩
  have hg : genericPoint Y ∈ V := gen_mem x.2
  have hreg : ∀ y ∈ V, RegAt y (u ^ k / s ^ k') := by
    intro y hy
    obtain ⟨e, he⟩ := D.exists_isEqn y
    have hA := (loc y e he).2.1 hy
    rw [← pow_div_pow_eqn u s _ e.ne_zero k' k]
    exact regAt_div (regAt_pow (locU y e he).1 _) ((unitAt_pow_iff hA.regAt (by omega)).2 hA)
  obtain ⟨a, ha⟩ := exists_fnOf_eq hg hreg
  have e₁ : Y.basicOpen a = V ⊓ U := by
    ext y
    refine ⟨fun hy => ?_, fun ⟨hyV, hyU⟩ => ?_⟩
    · have hyV : y ∈ V := Y.basicOpen_le a hy
      obtain ⟨e, he⟩ := D.exists_isEqn y
      have hA := (loc y e he).2.1 hyV
      have h := (unitAt_fnOf_iff hyV hg a).2 hy
      rw [ha, ← pow_div_pow_eqn u s _ e.ne_zero k' k, unitAt_div_iff ((unitAt_pow_iff hA.regAt (by omega)).2 hA),
        unitAt_pow_iff (locU y e he).1 (by omega)] at h
      exact ⟨hyV, (locU y e he).2.2 h⟩
    · obtain ⟨e, he⟩ := D.exists_isEqn y
      have hA := (loc y e he).2.1 hyV
      refine (unitAt_fnOf_iff hyV hg a).1 ?_
      rw [ha, ← pow_div_pow_eqn u s _ e.ne_zero k' k, unitAt_div_iff ((unitAt_pow_iff hA.regAt (by omega)).2 hA),
        unitAt_pow_iff (locU y e he).1 (by omega)]
      exact (locU y e he).2.1 hyU
  have him := Scheme.Opens.ι_image_basicOpen_topIso_inv (U := V) a
  rw [e₁] at him
  refine ⟨V.topIso.inv a, ?_, ?_⟩
  · rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, him]
    exact stepC k' hk' u hu U hUa hUl
  · have hm : V.ι x ∈ V.ι ''ᵁ V.toScheme.basicOpen (V.topIso.inv a) := by
      rw [him]; exact ⟨x.2, hxU⟩
    obtain ⟨z, hz, hzx⟩ := hm
    rwa [V.ι.isOpenEmbedding.injective hzx] at hz

end GlobalTheory.Desc.LocusQA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRadicalSpanProdRelativeRegularParameters
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

namespace GlobalTheory.RelParamRad

theorem prod_dvd_of_forall_dvd {R : Type} [CommMonoidWithZero R] :
    ∀ (m : ℕ) (t : Fin m → R), (∀ k, Prime (t k)) → (∀ i j, t i ∣ t j → i = j) →
      ∀ x : R, (∀ k, t k ∣ x) → ∏ k, t k ∣ x := by
  intro m
  induction m with
  | zero => intro t _ _ x _; simp
  | succ m ih =>
    intro t hp hd x hx
    obtain ⟨y, rfl⟩ := hx 0
    rw [Fin.prod_univ_succ]
    refine mul_dvd_mul_left _ (ih (fun k => t k.succ) (fun k => hp _) (fun i j h => Fin.succ_injective _ (hd _ _ h)) y
      fun k => ?_)
    refine ((hp k.succ).dvd_or_dvd (hx k.succ)).resolve_left fun h => ?_
    exact Fin.succ_ne_zero k (hd _ _ h)

theorem isRadical_span_prod : ∀ (o R : Type) [CommRing o] [CommRing R] [IsRegularLocalRing R] [IsDomain R] (b : o →+* R)
    (m : ℕ) (t : Fin m → R), IsRelParam b t → (Ideal.span {∏ k, t k}).IsRadical := by
  intro o R _ _ _ _ b m t h
  have hp : ∀ k, Prime (t k) := fun k => prime_of_not_mem_sq (h.1 k) (h.notMem_sq k)
  intro x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 hx
  rw [Ideal.mem_span_singleton] at hn ⊢
  exact prod_dvd_of_forall_dvd m t hp (fun i j hij => h.eq_of_dvd hij) x
    fun k => (hp k).dvd_of_dvd_pow ((Finset.dvd_prod_of_mem t (Finset.mem_univ k)).trans hn)

end GlobalTheory.RelParamRad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionFamilyZero
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.Pinch

def IsSecFam {X : Scheme.{0}} (L : LB X) {J : Type} (D : J → X.Opens) (k : J → L.ι)
    (hD : ∀ j, D j ≤ L.U (k j)) (e : ∀ j, Γ(X, D j)) : Prop :=
  ∀ (j j' : J) (z : X) (hz : z ∈ D j) (hz' : z ∈ D j'),
    (X.presheaf.germ (D j) z hz).hom (e j) =
      (X.presheaf.germ (L.U (k j) ⊓ L.U (k j')) z ⟨hD j hz, hD j' hz'⟩).hom (L.g (k j) (k j')).val *
        (X.presheaf.germ (D j') z hz').hom (e j')

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleFiniteFlatSubgroupSchemeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelOfLineBundle_finiteFlat_subgroupScheme : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∃ (H : Over (Sp R)) (_ : GrpObj H) (i : H ⟶ A), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Flat H.hom ∧ ∀ (T : Over (Sp R)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ i = x := by
  first | exact @GlobalTheory.kernel_finiteFlat_subgroup | exact GlobalTheory.kernel_finiteFlat_subgroup | (intros; apply GlobalTheory.kernel_finiteFlat_subgroup <;> assumption)
end

