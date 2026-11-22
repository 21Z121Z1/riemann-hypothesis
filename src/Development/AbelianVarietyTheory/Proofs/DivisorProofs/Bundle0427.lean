import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0403
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0394
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatFilteredColimitFiniteType
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.EtFFApprox

variable {J : Type} [SmallCategory J] (D0 : J ⥤ CommRingCat.{0}) (j : J) {B' : CommRingCat.{0}} (g' : D0.obj j ⟶ B')

def pmap {k k' : Under j} (φ : k ⟶ k') : pushout g' (D0.map k.hom) ⟶ pushout g' (D0.map k'.hom) :=
  pushout.desc (pushout.inl _ _) (D0.map φ.right ≫ pushout.inr _ _)
    (by rw [pushout.condition, ← Category.assoc, ← D0.map_comp, Under.w φ])

@[reassoc (attr := simp)] lemma inl_pmap {k k' : Under j} (φ : k ⟶ k') :
    pushout.inl _ _ ≫ pmap D0 j g' φ = pushout.inl _ _ := pushout.inl_desc _ _ _

@[reassoc (attr := simp)] lemma inr_pmap {k k' : Under j} (φ : k ⟶ k') :
    pushout.inr _ _ ≫ pmap D0 j g' φ = D0.map φ.right ≫ pushout.inr _ _ := pushout.inr_desc _ _ _

def arrF : Under j ⥤ Arrow CommRingCat.{0} where
  obj k := Arrow.mk (pushout.inr g' (D0.map k.hom))
  map {k k'} φ := Arrow.homMk' (D0.map φ.right) (pmap D0 j g' φ) (inr_pmap D0 j g' φ).symm
  map_id k := by
    ext : 1
    · simp
    · apply pushout.hom_ext <;> simp
  map_comp φ ψ := by
    ext : 1
    · simp
    · apply pushout.hom_ext <;> simp

@[simp] lemma arrF_obj_left (k : Under j) : ((arrF D0 j g').obj k).left = D0.obj k.right := rfl
@[simp] lemma arrF_obj_right (k : Under j) : ((arrF D0 j g').obj k).right = pushout g' (D0.map k.hom) := rfl
@[simp] lemma arrF_obj_hom (k : Under j) : ((arrF D0 j g').obj k).hom = pushout.inr g' (D0.map k.hom) := rfl
@[simp] lemma arrF_map_left {k k' : Under j} (φ : k ⟶ k') : ((arrF D0 j g').map φ).left = D0.map φ.right := rfl
@[simp] lemma arrF_map_right {k k' : Under j} (φ : k ⟶ k') : ((arrF D0 j g').map φ).right = pmap D0 j g' φ := rfl

variable {A B : CommRingCat.{0}} (ι0 : D0 ⟶ (Functor.const J).obj A) (g : A ⟶ B) (h : B' ⟶ B)
  (hnat : ∀ k : Under j, g' ≫ h = D0.map k.hom ≫ ι0.app k.right ≫ g)

def pdesc (k : Under j) : pushout g' (D0.map k.hom) ⟶ B := pushout.desc h (ι0.app k.right ≫ g) (hnat k)

def coc : arrF D0 j g' ⟶ (Functor.const (Under j)).obj (Arrow.mk g) where
  app k := Arrow.homMk (f := (arrF D0 j g').obj k) (g := Arrow.mk g) (ι0.app k.right) (pdesc D0 j g' ι0 g h hnat k)
    (pushout.inr_desc _ _ (hnat k)).symm
  naturality k k' φ := by
    ext : 1
    · simp only [Arrow.comp_left, Functor.const_obj_map, Arrow.id_left, Category.comp_id, Arrow.homMk_left, arrF_map_left]
      rw [ι0.naturality φ.right]
      simp
    · simp only [Arrow.comp_right, Functor.const_obj_map, Arrow.id_right, Category.comp_id, Arrow.homMk_right, arrF_map_right]
      apply pushout.hom_ext
      · simp [pdesc]
      · simp only [pdesc, inr_pmap_assoc, pushout.inr_desc]
        rw [ι0.naturality_assoc φ.right]
        simp

@[simp] lemma coc_app_left (k : Under j) : ((coc D0 j g' ι0 g h hnat).app k).left = ι0.app k.right := rfl
@[simp] lemma coc_app_right (k : Under j) : ((coc D0 j g' ι0 g h hnat).app k).right = pdesc D0 j g' ι0 g h hnat k := rfl

lemma snd_coc (k : Under j) : (Comma.snd (𝟭 _) (𝟭 _)).map ((coc D0 j g' ι0 g h hnat).app k) = pdesc D0 j g' ι0 g h hnat k := rfl

@[reassoc] lemma inl_pdesc (k : Under j) : pushout.inl _ _ ≫ pdesc D0 j g' ι0 g h hnat k = h := pushout.inl_desc _ _ _
@[reassoc] lemma inr_pdesc (k : Under j) : pushout.inr _ _ ≫ pdesc D0 j g' ι0 g h hnat k = ι0.app k.right ≫ g := pushout.inr_desc _ _ _

def leftOf (s : Cocone (arrF D0 j g' ⋙ Comma.snd (𝟭 _) (𝟭 _))) : Cocone (Under.forget j ⋙ D0) where
  pt := s.pt
  ι := { app := fun k => pushout.inr g' (D0.map k.hom) ≫ s.ι.app k
         naturality := fun k k' φ => by
           have hw := s.w φ
           simp only [Functor.comp_map, Comma.snd_map] at hw
           dsimp
           rw [← hw, Category.comp_id]
           simp }

@[simp] lemma leftOf_ι_app (s : Cocone (arrF D0 j g' ⋙ Comma.snd (𝟭 _) (𝟭 _))) (k : Under j) :
    (leftOf D0 j g' s).ι.app k = pushout.inr g' (D0.map k.hom) ≫ s.ι.app k := rfl

def rightIsColimit (hP : IsPushout g' (ι0.app j) h g) (hL : IsColimit ((Cocone.mk A ι0).whisker (Under.forget j))) :
    IsColimit ((Comma.snd (𝟭 _) (𝟭 _)).mapCocone (Cocone.mk (Arrow.mk g) (coc D0 j g' ι0 g h hnat))) where
  desc s := hP.desc (pushout.inl _ _ ≫ s.ι.app (Under.mk (𝟙 j))) (hL.desc (leftOf D0 j g' s)) (by
      have := hL.fac (leftOf D0 j g' s) (Under.mk (𝟙 j))
      simp only [Cocone.whisker_ι, Functor.whiskerLeft_app, Under.forget_obj, leftOf_ι_app] at this
      rw [pushout.condition_assoc]
      simp only [Under.mk_right] at this
      rw [this]
      simp)
  fac s k := by
    dsimp
    apply pushout.hom_ext
    · have hw := s.w (Under.homMk k.hom (by simp) : Under.mk (𝟙 j) ⟶ k)
      simp only [Functor.comp_map, Comma.snd_map, arrF_map_right] at hw
      rw [snd_coc, inl_pdesc_assoc, IsPushout.inl_desc, ← hw]
      exact inl_pmap_assoc D0 j g' _ _
    · have := hL.fac (leftOf D0 j g' s) k
      simp only [Cocone.whisker_ι, Functor.whiskerLeft_app, Under.forget_obj, leftOf_ι_app] at this
      rw [snd_coc, inr_pdesc_assoc, IsPushout.inr_desc, this]
  uniq s m hm := by
    apply hP.hom_ext
    · rw [IsPushout.inl_desc]
      have h1 := hm (Under.mk (𝟙 j))
      dsimp at h1
      rw [← h1, snd_coc, inl_pdesc_assoc]
    · rw [IsPushout.inr_desc]
      apply hL.hom_ext
      intro k
      have h1 := hL.fac (leftOf D0 j g' s) k
      have h2 := hm k
      dsimp at h1 h2 ⊢
      rw [h1, ← h2, snd_coc, inr_pdesc_assoc]

end GlobalTheory.EtFFApprox

open GlobalTheory.EtFFApprox in

theorem GlobalTheory.EtC.etFF_filtered_colimit_finiteType : ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ Arrow CommRingCat.{0}) (ι : D ⟶ (Functor.const J).obj (Arrow.mk g)), Nonempty (IsColimit (Cocone.mk (Arrow.mk g) ι)) ∧ ∀ j, EtFF (D.obj j).hom ∧ Algebra.FiniteType ℤ (D.obj j).left ∧ Algebra.FiniteType ℤ (D.obj j).right := by
  intro A B g hg
  obtain ⟨J, _, _, D0, ι0, ⟨hc⟩, hft⟩ := GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType A
  obtain ⟨j, B', g', h, hg', hP⟩ := GlobalTheory.T.etaleFaithfullyFlat_descends_of_isColimit J D0 (Cocone.mk A ι0) hc B g hg
  have hb := GlobalTheory.EtC.etFF_basic
  haveI := hb.1.2.1
  have hP' : IsPushout g' (ι0.app j) h g := hP
  have hL : IsColimit ((Cocone.mk A ι0).whisker (Under.forget j)) :=
    (Functor.Final.isColimitWhiskerEquiv (Under.forget j) _).symm hc
  have hnat : ∀ (k : Under j), g' ≫ h = D0.map k.hom ≫ ι0.app k.right ≫ g := by
    intro k
    rw [← Category.assoc, ι0.naturality k.hom]
    simpa using hP'.w
  refine ⟨Under j, inferInstance, inferInstance, arrF D0 j g', coc D0 j g' ι0 g h hnat, ⟨?_⟩, fun k => ?_⟩
  · exact Comma.fstSndJointlyReflectColimit hL (rightIsColimit D0 j g' ι0 g h hnat hP' hL)
  · have hk : EtFF (pushout.inr g' (D0.map k.hom)) :=
      MorphismProperty.IsStableUnderCobaseChange.of_isPushout (IsPushout.of_hasPushout g' (D0.map k.hom)).flip hg'
    exact ⟨hk, hft k.right, hb.2.2 _ _ _ hk (hft k.right)⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosureTorsorOfFractionFieldsStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_integralClosure_torsor_of_fraction_fields : (∀ (S S₁ K K₁ : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    ∀ (M : Type) [CommRing M] [Algebra K M] (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)),
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] M))) →
  ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R],
    Function.Injective (algebraMap A R) →
    ∀ (A₁ R₁ : Type) [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [Algebra A₁ R₁],
    Function.Injective (algebraMap A₁ R₁) →
    ∀ (f : A →+* A₁), Function.Injective f → ∀ (φ : R →+* R₁),
    φ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp φ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA] (q : ℕ)
      (act : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    0 < q → IsUnit (q : A) → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q act →
    ∀ (P₁ : Ideal R₁) [P₁.IsPrime],
    IsDiscreteValuationRing (Localization.AtPrime P₁) →
    IsDiscreteValuationRing (Localization.AtPrime (P₁.comap φ)) →
    ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime (P₁.comap φ)) π) →
    ∀ y : R₁, y ^ q = φ (algebraMap A R π) →
    (letI := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ (GlobalTheory.KeyOriginBC.BC β DA)).toAlgebra;
      Algebra.Etale (Localization.AtPrime P₁)
        (integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] GlobalTheory.KeyOriginBC.BC β DA))) := by
  first | (exact @GlobalTheory.KeyOriginTransport.etale_closure_of_field) | (exact GlobalTheory.KeyOriginTransport.etale_closure_of_field) | (intros; apply GlobalTheory.KeyOriginTransport.etale_closure_of_field  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMayerVietorisFreeRightEpiStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleMayerVietoris_free_right_epi : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → Epi (biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))))) := by
  first | (exact @GlobalTheory.EtC.MVEpi.mv_right_epi) | (exact GlobalTheory.EtC.MVEpi.mv_right_epi) | (intros; apply GlobalTheory.EtC.MVEpi.mv_right_epi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleModuleSheafSectionsCoprodBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleModuleSheaf_sections_coprod_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → Function.Bijective (fun (x : Sec F U) (i : ι) => Sec.res (j i) x) := by
  first | (exact @GlobalTheory.EtC.sec_coprod) | (exact GlobalTheory.EtC.sec_coprod) | (intros; apply GlobalTheory.EtC.sec_coprod  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafExtendScalarsZmodKernelLocallyMultipleStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafExtendScalars_zmod_kernel_locally_multiple : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (M : Shv (ZMod Q)) (U : Scheme.{0}) (x : Sec M U), extSh.sec (ZMod.castHom hq (ZMod q)) M U x = 0 → Loc U fun V g => ∃ y : Sec M V, Sec.res g x = q • y := by
  first | (exact @GlobalTheory.EtC.extSh_sec_eq_zero_loc) | (exact GlobalTheory.EtC.extSh_sec_eq_zero_loc) | (intros; apply GlobalTheory.EtC.extSh_sec_eq_zero_loc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafExtendScalarsZmodSectionLocallyTmulStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafExtendScalars_zmod_section_locally_tmul : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (M : Shv (ZMod Q)) (U : Scheme.{0}) (y : Sec ((extSh (ZMod.castHom hq (ZMod q))).obj M) U), Loc U fun V g => ∃ x : Sec M V, extSh.sec (ZMod.castHom hq (ZMod q)) M V x = Sec.res g y := by
  first | (exact @GlobalTheory.EtC.ExtOnto.ext_onto) | (exact GlobalTheory.EtC.ExtOnto.ext_onto) | (intros; apply GlobalTheory.EtC.ExtOnto.ext_onto  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafShortComplexExactIffLocallyStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact ↔ ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b := by
  first | (exact @GlobalTheory.EtC.exactIff) | (exact GlobalTheory.EtC.exactIff) | (intros; apply GlobalTheory.EtC.exactIff  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyLevelwiseCoproductBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceCohomology_levelwise_coproduct_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (ι : Type) (Q : ι → Spc) (a : ∀ i, Q i ⟶ E), (∀ k : SimplexCategoryᵒᵖ, Nonempty (IsColimit (Cofan.mk ((free R).obj (E.obj k)) (fun i => (free R).map ((a i).app k))))) → ∀ n : ℤ, Function.Bijective (fun (x : H R E F n) (i : ι) => pull R (a i) F n x) := by
  first | (exact @GlobalTheory.EtC.HCofan.main) | (exact GlobalTheory.EtC.HCofan.main) | (intros; apply GlobalTheory.EtC.HCofan.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlexanderWhitneyDiagonalSwapHomotopy
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.PrHomotopy

lemma deg_sub {N k : ℕ} {a b : Pr N →₀ ℤ} (ha : Pr.Deg k a) (hb : Pr.Deg k b) : Pr.Deg k (a - b) := by
  intro z hz
  rcases Finset.mem_union.1 (Finsupp.support_sub hz) with h | h
  · exact ha z h
  · exact hb z h

lemma deg_zero {N k : ℕ} : Pr.Deg k (0 : Pr N →₀ ℤ) := by
  intro z hz; simp at hz

lemma bd_sub {N : ℕ} (a b : Pr N →₀ ℤ) : Pr.bd (a - b) = Pr.bd a - Pr.bd b := by
  simp [Pr.bd, map_sub, smul_sub, Finset.sum_sub_distrib]

lemma aw_zero_eq_wa_zero : Pr.aw 0 = Pr.wa 0 := by
  simp [Pr.aw, Pr.wa]

open Classical in

noncomputable def step (N : ℕ) (c : Pr N →₀ ℤ) : Pr (N + 1) →₀ ℤ :=
  if H : ∃ e, Pr.Deg (N + 2) e ∧ Pr.d (N + 1) e = Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd c then H.choose else 0

noncomputable def hom : ∀ N, Pr N →₀ ℤ
  | 0 => 0
  | N + 1 => step N (hom N)

lemma step_spec (N : ℕ) (c : Pr N →₀ ℤ) (hc : Pr.Deg (N + 1) c)
    (hd : Pr.bd (Pr.d N c) = Pr.bd (Pr.aw N - Pr.wa N)) :
    Pr.Deg (N + 2) (step N c) ∧ Pr.d (N + 1) (step N c) = Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd c := by
  obtain ⟨-, -, -, hbdeg, -, hdbd, haw⟩ := GlobalTheory.T.prism_chain_complex_boundary_identities
  have H : ∃ e, Pr.Deg (N + 2) e ∧ Pr.d (N + 1) e = Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd c := by
    apply GlobalTheory.T.standardSimplexFacePairs_acyclic_positive_degree (N + 1) N
    · exact deg_sub (deg_sub (haw (N + 1)).1 (haw (N + 1)).2) (hbdeg _ _ _ hc)
    · obtain ⟨h1, h2⟩ := GlobalTheory.T.alexanderWhitneyDiagonal_and_swap_chain_maps N
      rw [map_sub, map_sub, h1, h2, hdbd, hd, bd_sub, sub_self]
  unfold step
  rw [dif_pos H]
  exact H.choose_spec

lemma hom_spec (N : ℕ) : Pr.Deg (N + 1) (hom N) ∧ Pr.bd (Pr.d N (hom N)) = Pr.bd (Pr.aw N - Pr.wa N) := by
  induction N with
  | zero => exact ⟨deg_zero, by simp [hom, aw_zero_eq_wa_zero]⟩
  | succ N ih =>
    obtain ⟨h1, h2⟩ := step_spec N (hom N) ih.1 ih.2
    obtain ⟨-, -, -, -, hbb, -, -⟩ := GlobalTheory.T.prism_chain_complex_boundary_identities
    refine ⟨h1, ?_⟩
    show Pr.bd (Pr.d (N + 1) (step N (hom N))) = _
    rw [h2, bd_sub, hbb, sub_zero]

end GlobalTheory.EtC.PrHomotopy

theorem GlobalTheory.EtC.pr_aw_wa_homotopy :
    ∃ h : ∀ N, Pr N →₀ ℤ, (∀ N, Pr.Deg (N + 1) (h N)) ∧ Pr.d 0 (h 0) = Pr.aw 0 - Pr.wa 0 ∧
      ∀ N, Pr.d (N + 1) (h (N + 1)) + Pr.bd (h N) = Pr.aw (N + 1) - Pr.wa (N + 1) := by
  refine ⟨PrHomotopy.hom, fun N => (PrHomotopy.hom_spec N).1, ?_, fun N => ?_⟩
  · simp [PrHomotopy.hom, PrHomotopy.aw_zero_eq_wa_zero]
  · have := (PrHomotopy.step_spec N (PrHomotopy.hom N) (PrHomotopy.hom_spec N).1 (PrHomotopy.hom_spec N).2).2
    show Pr.d (N + 1) (PrHomotopy.step N (PrHomotopy.hom N)) + _ = _
    rw [this, sub_add_cancel]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpen
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CechDR

variable {X X' : Scheme.{0}}

theorem Pair.exists_basicOpen (φ : X' ⟶ X) (W : X'.affineOpens) {x : X'} (hx : x ∈ W.1) :
    ∃ (p : Pair φ) (f : Γ(X', W.1)), p.1.1.1 = X'.basicOpen f ∧ x ∈ p.1.1.1 := by
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show φ.base x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨f, hf, hxf⟩ := W.2.exists_basicOpen_le (V := W.1 ⊓ φ ⁻¹ᵁ U) ⟨x, hx, hxU⟩ hx
  exact ⟨⟨(⟨X'.basicOpen f, W.2.basicOpen f⟩, ⟨U, hU⟩), hf.trans inf_le_right⟩, f, rfl, hxf⟩

theorem Pair.exists_le_le (φ : X' ⟶ X) (p q : Pair φ) {x : X'} (hx : x ∈ p.1.1.1 ⊓ q.1.1.1) :
    ∃ r : Pair φ, r ≤ p ∧ r ≤ q ∧ x ∈ r.1.1.1 := by
  have hy : φ.base x ∈ p.1.2.1 ⊓ q.1.2.1 := ⟨p.2 hx.1, q.2 hx.2⟩
  obtain ⟨U, hU, hxU, hUle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hy
  obtain ⟨U', hU', hxU', hU'le⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X'.isBasis_affineOpens
    (show x ∈ p.1.1.1 ⊓ q.1.1.1 ⊓ φ ⁻¹ᵁ U from ⟨hx, hxU⟩)
  refine ⟨⟨(⟨U', hU'⟩, ⟨U, hU⟩), hU'le.trans inf_le_right⟩, ?_, ?_, hxU'⟩
  · exact ⟨hU'le.trans (inf_le_left.trans inf_le_left), hUle.trans inf_le_left⟩
  · exact ⟨hU'le.trans (inf_le_left.trans inf_le_right), hUle.trans inf_le_right⟩

end GlobalTheory.CechDR

namespace GlobalTheory.CechDR
open Opposite
variable {R' : Type} [CommRing R'] {X X' : Scheme.{0}}

theorem Pair.exists_le (φ : X' ⟶ X) (W : X'.affineOpens) {x : X'} (hx : x ∈ W.1) :
    ∃ (p : Pair φ) (hp : p.1.1 ≤ W), x ∈ p.1.1.1 := by
  obtain ⟨p, f, e, hxp⟩ := Pair.exists_basicOpen φ W hx
  exact ⟨p, show p.1.1.1 ≤ W.1 from e ▸ X'.basicOpen_le f, hxp⟩

theorem sec_eq_of_pair (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (W : X'.affineOpens)
    (a b : (OAff s').obj (op W))
    (h : ∀ (p : Pair φ) (hp : p.1.1 ≤ W), mp (OAff s') (homOfLE hp).op a = mp (OAff s') (homOfLE hp).op b) :
    a = b := by
  refine TopCat.Presheaf.section_ext X'.sheaf W.1 a b fun x hx ↦ ?_
  obtain ⟨p, hp, hxp⟩ := Pair.exists_le φ W hx
  have e : (X'.presheaf.germ p.1.1.1 x hxp).hom ((X'.presheaf.map (homOfLE (show p.1.1.1 ≤ W.1 from hp)).op).hom a) =
      (X'.presheaf.germ p.1.1.1 x hxp).hom ((X'.presheaf.map (homOfLE (show p.1.1.1 ≤ W.1 from hp)).op).hom b) :=
    congrArg _ (h p hp)
  have k := X'.presheaf.germ_res (homOfLE (show p.1.1.1 ≤ W.1 from hp)) x hxp
  exact (congrArg (fun t ↦ t.hom a) k).symm.trans (e.trans (congrArg (fun t ↦ t.hom b) k))

end GlobalTheory.CechDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenFibresPreirreducibleSmoothStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_fibres_preirreducible_smooth : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Algebra.Smooth A B → ∀ (q : PrimeSpectrum B) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω], q.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A Ω) → PreirreducibleSpace (PrimeSpectrum (Ω ⊗[A] B)) → ∃ (b : B) (a : A) (I : Finset A), b ∉ q.asIdeal ∧ algebraMap A B a ∉ q.asIdeal ∧ (∀ c ∈ I, algebraMap A B c ∈ q.asIdeal) ∧ ∀ t : PrimeSpectrum A, a ∉ t.asIdeal → (∀ c ∈ I, c ∈ t.asIdeal) → IsPreirreducible {r : PrimeSpectrum B | r.asIdeal.comap (algebraMap A B) = t.asIdeal ∧ b ∉ r.asIdeal} := by
  first | exact @GlobalTheory.exists_basicOpen_fibres_preirreducible | exact GlobalTheory.exists_basicOpen_fibres_preirreducible | (intros; apply GlobalTheory.exists_basicOpen_fibres_preirreducible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBisimplicialShuffleOperatorsStatement
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bisimplicial_shuffle_operators : ∃ G : ∀ a b n : ℕ, bo a b ⟶ bo n n, G 0 0 0 = 𝟙 (bo 0 0) ∧ ∀ a b n : ℕ, a + b = n + 1 → G a b (n + 1) ≫ dD (n + 1) n = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, dT a b x.1 x.2 ≫ G x.1 x.2 n := by
  first | (exact @GlobalTheory.EZ.Shuf.exists_shuffle) | (exact GlobalTheory.EZ.Shuf.exists_shuffle) | (intros; apply GlobalTheory.EZ.Shuf.exists_shuffle  <;> assumption)
end

