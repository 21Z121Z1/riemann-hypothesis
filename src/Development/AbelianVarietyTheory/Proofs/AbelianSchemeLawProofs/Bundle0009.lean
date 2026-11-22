import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroOfDvdPowUniformiser
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sec_eq_zero_of_chart {X : Scheme.{0}} [IsIntegral X] (N : LB X) (s : LB.Sec N)
    (j : N.ι) (x : X) (hx : x ∈ N.U j) (hj : s.f j = 0) (i : N.ι) : s.f i = 0 := by
  by_cases hi : (N.U i : Set X).Nonempty
  · have hij : ((N.U i ⊓ N.U j : X.Opens) : Set X).Nonempty :=
      nonempty_preirreducible_inter (N.U i).isOpen (N.U j).isOpen hi ⟨x, hx⟩
    have : Nonempty (N.U i ⊓ N.U j : X.Opens) := hij.to_subtype
    have h := s.compat i j
    rw [hj, map_zero, mul_zero] at h
    apply map_injective_of_isIntegral X (homOfLE (inf_le_left : N.U i ⊓ N.U j ≤ N.U i))
    rw [map_zero]
    exact h
  · have : N.U i = ⊥ := by
      ext1
      simpa using Set.not_nonempty_iff_eq_empty.1 hi
    have : Subsingleton Γ(X, N.U i) := by rw [this]; infer_instance
    exact Subsingleton.elim _ _

theorem eq_zero_of_mem_pow_span {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) (x : X) (hx : x ∈ U) (a b : Γ(X, U)) (ha : x ∉ X.basicOpen a)
    (hb : ∀ e : ℕ, b ∈ Ideal.span {a} ^ e) : b = 0 := by
  apply germ_injective_of_isIntegral X x hx
  rw [map_zero]
  rw [X.mem_basicOpen a x hx] at ha
  have hI : Ideal.span {(X.presheaf.germ U x hx).hom a} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  have h := Ideal.iInf_pow_eq_bot_of_isLocalRing _ hI
  rw [← Ideal.mem_bot, ← h, Ideal.mem_iInf]
  intro e
  have := Ideal.mem_map_of_mem (X.presheaf.germ U x hx).hom (hb e)
  rwa [Ideal.map_pow, Ideal.map_span, Set.image_singleton] at this

theorem sec_eq_zero_of_dvd_pow_uniformiser :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f →
      GeometricallyIntegral f) → Semi.lemmaBSt.{0} := by
  intro H V _ _ _ G _ _ _ _ _ _ N hN s π hπ hs
  have : GeometricallyIntegral G.hom := H _ _ _ inferInstance inferInstance
  have : IsIntegral G.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  obtain ⟨x, hx⟩ := G.hom.surjective (IsLocalRing.closedPoint V)
  obtain ⟨j, hj⟩ : ∃ j, x ∈ N.U j := by
    have : x ∈ ⨆ i, N.U i := by rw [hN.cover]; trivial
    exact Opens.mem_iSup.1 this
  refine sec_eq_zero_of_chart N s j x hj ?_
  refine eq_zero_of_mem_pow_span (N.U j) x hj _ _ ?_ (hs j)
  intro h
  have h2 := ((Scheme.basicOpen_res G.left _ (homOfLE (le_top :
    N.U j ≤ G.hom ⁻¹ᵁ ⊤)).op).le h).2
  have h3 : x ∈ G.hom ⁻¹ᵁ (Spec (CommRingCat.of V)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv π) := by
    rw [Scheme.preimage_basicOpen]
    exact h2
  rw [basicOpen_eq_of_affine] at h3
  have h4 : G.hom x ∈ PrimeSpectrum.basicOpen π := h3
  rw [hx] at h4
  exact h4 ((IsLocalRing.mem_maximalIdeal π).2 hπ.not_isUnit)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SurjectiveAppOfIsAbelianScheme
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem eq_comp_section_of_local_rigidity {X T Y S : Scheme.{0}} (p : X ⟶ T) (ε : T ⟶ X)
    (g : X ⟶ Y) (π : T ⟶ S) (q : Y ⟶ S) [IsSeparated q] (he : ε ≫ p = 𝟙 T)
    (hg : g ≫ q = p ≫ π) (hp : IsOpenMap p)
    (hloc : ∀ (t : T) (y : Y), (∀ x : X, p x = t → g x = y) →
      ∃ V : T.Opens, t ∈ V ∧ (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g)
    (hconn : ∀ s : S, _root_.IsPreconnected (π ⁻¹' {s}))
    (hmeet : ∀ s : S, ∃ (t : T) (y : Y), π t = s ∧ ∀ x : X, p x = t → g x = y) :
    g = p ≫ ε ≫ g := by
  have hab : g ≫ q = (p ≫ ε ≫ g) ≫ q := by
    simp only [Category.assoc, hg, reassoc_of% he]
  have hcl := isClosedImmersion_equalizer_ι_of_isSeparated q hab
  let Z : Set X := Set.range (equalizer.ι g (p ≫ ε ≫ g))
  have hZ : IsClosed Z := (equalizer.ι g (p ≫ ε ≫ g)).isClosedEmbedding.isClosed_range
  let T₀ : Set T := (p '' Zᶜ)ᶜ
  have hT₀c : IsClosed T₀ := (hp _ hZ.isOpen_compl).isClosed_compl
  have hfib : ∀ t ∈ T₀, ∀ x : X, p x = t → g x = g (ε t) := by
    intro t ht x hx
    have hxZ : x ∈ Z := by
      by_contra h
      exact ht ⟨x, h, hx⟩
    obtain ⟨z, rfl⟩ := hxZ
    rw [← hx, ← Scheme.Hom.comp_apply, equalizer.condition]
    simp only [Scheme.Hom.comp_apply]
  have hsub : ∀ V : T.Opens, (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g → (V : Set T) ⊆ T₀ := by
    rintro V hV t ht ⟨x, hx, rfl⟩
    exact hx (range_subset_range_equalizer_ι _ hV ⟨⟨x, ht⟩, rfl⟩)
  have hT₀o : IsOpen T₀ := by
    rw [isOpen_iff_forall_mem_open]
    intro t ht
    obtain ⟨V, htV, hV⟩ := hloc t _ (hfib t ht)
    exact ⟨V, hsub V hV, V.2, htV⟩
  have hall : ∀ t : T, t ∈ T₀ := by
    intro t
    obtain ⟨t', y, ht', hy⟩ := hmeet (π t)
    obtain ⟨V, htV, hV⟩ := hloc t' y hy
    exact (hconn (π t)).subset_isClopen ⟨hT₀c, hT₀o⟩ ⟨t', ht', hsub V hV htV⟩ rfl
  refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
  obtain ⟨V, htV, hV⟩ := hloc (p x) _ (hfib _ (hall _))
  exact ⟨p ⁻¹ᵁ V, htV, hV⟩

theorem surjective_app_of_isAbelianScheme (hG : GlobalFnsSt) {S : Scheme.{0}} (A : Over S)
    [GrpObj A] (hA : IsAbelianScheme A) (V : S.Opens) :
    Function.Surjective (A.hom.app V).hom := by
  have h1 : Function.Surjective (pullback.snd A.hom V.ι).appTop.hom :=
    (hG _ _ (TLinPf.isAb_pullback V.ι A hA)).2
  have h2 : Function.Surjective (A.hom ∣_ V).appTop.hom := by
    have e : A.hom ∣_ V = (pullbackRestrictIsoRestrict A.hom V).inv ≫ pullback.snd A.hom V.ι := rfl
    rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso
      ((pullbackRestrictIsoRestrict A.hom V).inv.app ⊤)).2.comp h1
  rw [morphismRestrict_appTop] at h2
  have h3 : Function.Surjective (A.hom.app (V.ι ''ᵁ ⊤)).hom := by
    have hb : Function.Bijective (A.left.presheaf.map
        (eqToHom (image_morphismRestrict_preimage A.hom V ⊤)).op).hom := by
      rw [eqToHom_op]
      exact ConcreteCategory.bijective_of_isIso (A.left.presheaf.map (eqToHom _))
    exact (Function.Surjective.of_comp_iff' hb _).1 h2
  rwa [V.ι_image_top] at h3

theorem rigidity_of_local_rigidity : GlobalFnsSt → (∀ (X T Y : Scheme.{0}) (p : X ⟶ T) (ε : T ⟶ X) (g : X ⟶ Y), ε ≫ p = 𝟙 T → UniversallyClosed p → (∀ V : T.Opens, Function.Surjective (p.app V).hom) → ∀ (t : T) (y : Y), (∀ x : X, p x = t → g x = y) → ∃ V : T.Opens, t ∈ V ∧ (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g) → RigiditySt := by
  intro hG hR S A B _ _ hA hB f hf
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have := hB.proper
  let g : A ⊗ A ⟶ B := (fst A A ≫ f)⁻¹ * ((fst A A * snd A A) ≫ f)
  let ε : A ⟶ A ⊗ A := lift 1 (𝟙 A)
  let j : A ⟶ A ⊗ A := lift (𝟙 A) 1
  have h1 : (1 : A ⟶ A) ≫ f = 1 := by
    rw [Hom.one_def, Category.assoc, hf, Hom.one_def]
  have hε : ε ≫ g = f := by
    simp only [g, ε, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd, h1,
      inv_one, _root_.one_mul, Category.id_comp]
  have hj : j ≫ g = 1 := by
    simp only [g, j, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd,
      _root_.mul_one, inv_mul_cancel]
  have hεp : ε.left ≫ (snd A A).left = 𝟙 A.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have hsm : Smooth (snd A A).left := by
    change Smooth (pullback.snd A.hom A.hom); infer_instance
  have huc : UniversallyClosed (snd A A).left := by
    change UniversallyClosed (pullback.snd A.hom A.hom); infer_instance
  have hsurj : ∀ V : A.left.Opens, Function.Surjective ((snd A A).left.app V).hom := fun V ↦
    surjective_app_of_isAbelianScheme hG _ (TLinPf.isAb_pullback A.hom A hA) V
  have hη : (η[A] : 𝟙_ (Over S) ⟶ A).left ≫ A.hom = 𝟙 S := Over.w η[A]
  have hpb : IsPullback j.left A.hom (snd A A).left (η[A] : 𝟙_ (Over S) ⟶ A).left := by
    have hr : IsPullback (fst A A).left (snd A A).left A.hom A.hom := .of_hasPullback A.hom A.hom
    refine IsPullback.of_right ?_ ?_ hr
    · have : j.left ≫ (fst A A).left = 𝟙 A.left := by
        rw [← Over.comp_left, lift_fst, Over.id_left]
      rw [this, hη]
      exact IsPullback.of_id_fst
    · rw [← Over.comp_left, lift_snd, Hom.one_def, Over.comp_left]
      rfl
  have key : g.left = (snd A A).left ≫ ε.left ≫ g.left := by
    refine eq_comp_section_of_local_rigidity (snd A A).left ε.left g.left A.hom B.hom hεp
      ((Over.w g).trans (Over.w (snd A A)).symm) (snd A A).left.isOpenMap
      (hR _ _ _ _ _ _ hεp huc hsurj) (fun s ↦ (A.hom.isConnected_preimage_singleton s).2) ?_
    intro s
    refine ⟨(η[A] : 𝟙_ (Over S) ⟶ A).left s, (η[B] : 𝟙_ (Over S) ⟶ B).left s, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, hη]; rfl
    · intro x hx
      obtain ⟨z, rfl, rfl⟩ := Scheme.exists_preimage_of_isPullback hpb x s hx
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hj, Hom.one_def, Over.comp_left,
        Scheme.Hom.comp_apply]
      rfl
  have key' : g = snd A A ≫ f := by
    rw [← hε]
    exact Over.OverMorphism.ext key
  have hmul : (fst A A * snd A A) ≫ f = (fst A A ≫ f) * (snd A A ≫ f) := by
    rw [← key', mul_inv_cancel_left]
  refine ⟨hf, ?_⟩
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at hmul
  rw [hmul]
  congr 1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem trdeg_eq_of_locally_isStandardSmoothOfRelativeDimension {K B : Type} [Field K]
    [CommRing B] [IsDomain B] [Algebra K B] {g : ℕ}
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap K B)) :
    Algebra.trdeg K B = g := by
  obtain ⟨s, hs, hP⟩ := h
  obtain ⟨t, hts, ht⟩ : ∃ t ∈ s, t ≠ 0 := by
    by_contra! hz
    have hbot : Ideal.span s = ⊥ := Ideal.span_eq_bot.mpr hz
    exact top_ne_bot (hs.symm.trans hbot)
  have hPt := hP t hts
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at hPt
  have hle : Submonoid.powers t ≤ nonZeroDivisors B :=
    powers_le_nonZeroDivisors_of_noZeroDivisors ht
  have : IsDomain (Localization.Away t) := IsLocalization.isDomain_localization hle
  have : Algebra.IsStandardSmooth K (Localization.Away t) := hPt.isStandardSmooth
  have hdim : ringKrullDim (Localization.Away t) = g :=
    AffinePoints.ringKrullDim_eq_of_isStandardSmooth (K := K)
  obtain ⟨d, hd1, hd2⟩ := exists_ringKrullDim_eq_and_trdeg_eq K (Localization.Away t)
  have hdg : d = g := by
    rw [hdim] at hd1
    exact_mod_cast hd1.symm
  have : FaithfulSMul B (Localization.Away t) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hle)
  have : Algebra.IsAlgebraic B (Localization.Away t) :=
    IsLocalization.isAlgebraic _ (Submonoid.powers t)
  have : FaithfulSMul K B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap K B).injective
  rw [← trdeg_eq_of_isAlgebraic_top K B (Localization.Away t), hd2, hdg]

theorem trdeg_eq_of_smoothOfRelativeDimension :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (B : Type) [CommRing B] [Nontrivial B] [Algebra K B] (j : Spec (CommRingCat.of B) ⟶ X), IsOpenImmersion j → j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K B)) → Algebra.trdeg K B = g := by
  intro K _ X _ f g hf B _ _ _ j hj hjf
  have : IsIntegral (Spec (CommRingCat.of B)) := isIntegral_of_isOpenImmersion j
  have : IsDomain B := (affine_isIntegral_iff (CommRingCat.of B)).mp this
  have h0 : SmoothOfRelativeDimension (0 + g) (j ≫ f) := inferInstance
  rw [Nat.zero_add, hjf] at h0
  have hloc := (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension g)).mp h0
  exact trdeg_eq_of_locally_isStandardSmoothOfRelativeDimension hloc

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace RegularFactorial

open IsLocalRing

theorem isRegularRing_of_isLocalization {R : Type*} [CommRing R] [IsRegularRing R]
    (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S] :
    IsRegularRing S := by
  have : IsNoetherianRing S := IsLocalization.isNoetherianRing M S inferInstance
  rw [isRegularRing_iff]
  intro P hP
  have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime P) P
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (P.comap (algebraMap R S)).primeCompl
      (Localization.AtPrime (P.comap (algebraMap R S))) (Localization.AtPrime P)).toRingEquiv

end RegularFactorial

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
open IsLocalRing in
private lemma prime_of_mem_maximalIdeal_of_not_mem_sq {A : Type} [CommRing A] [IsRegularLocalRing A]
    {x : A} (hx : x ∈ maximalIdeal A) (hx2 : x ∉ maximalIdeal A ^ 2) : Prime x := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hx2 (Ideal.zero_mem _)
  haveI := _root_.ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.quotient_span_singleton hx hx2
  haveI : IsDomain (A ⧸ Ideal.span {x}) := _root_.ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
  rw [← Ideal.span_singleton_prime hx0]
  exact (Ideal.Quotient.isDomain_iff_prime _).1 inferInstance

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma isPrincipal_of_isPrincipal_map_away_prime {A : Type} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] {x : A} (hx : Prime x) {p : Ideal A} [hp : p.IsPrime] (hxp : x ∉ p)
    (h : (p.map (algebraMap A (Localization.Away x))).IsPrincipal) : p.IsPrincipal := by
  obtain ⟨f, hf⟩ := h
  have hfmem : f ∈ p.map (algebraMap A (Localization.Away x)) := by
    rw [hf]; exact Submodule.mem_span_singleton_self f
  obtain ⟨⟨a, m⟩, ham⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers x) (Localization.Away x)).1 hfmem
  have hx0 : x ≠ 0 := hx.ne_zero
  have hinj : Function.Injective (algebraMap A (Localization.Away x)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
  have hmul : ∀ y ∈ p, ∃ (s : ℕ) (c : A), x ^ s * y = (a : A) * c := by
    intro y hy
    have hy' : algebraMap A (Localization.Away x) y ∈ p.map (algebraMap A (Localization.Away x)) :=
      Ideal.mem_map_of_mem _ hy
    rw [hf] at hy'
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hy'
    obtain ⟨⟨e, k⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers x) d
    obtain ⟨j, hj⟩ := k.2
    obtain ⟨i, hi⟩ := m.2
    refine ⟨j + i, e, hinj ?_⟩
    simp only [smul_eq_mul] at hd
    have h1 := IsLocalization.mk'_spec (Localization.Away x) e k
    dsimp only at ham hj hi
    rw [map_mul, map_mul, ← hd, ← ham, pow_add, map_mul, hj, hi, ← h1]
    ring
  by_cases ha0 : (a : A) = 0
  · refine ⟨0, le_antisymm (fun y hy => ?_) ?_⟩
    · obtain ⟨s, c, hsc⟩ := hmul y hy
      rw [ha0, zero_mul] at hsc
      have hy0 : y = 0 := (mul_eq_zero.1 hsc).resolve_left (pow_ne_zero _ hx0)
      rw [hy0]; exact Submodule.zero_mem _
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact p.zero_mem
  · obtain ⟨g, hag, hxg⟩ :=
      (FiniteMultiplicity.of_not_isUnit hx.not_unit ha0).exists_eq_pow_mul_and_not_dvd
    have hxr : x ^ multiplicity x (a : A) ∉ p := fun h => hxp (hp.mem_of_pow_mem _ h)
    have hg : g ∈ p := (hp.mem_or_mem (hag ▸ a.2)).resolve_left hxr
    refine ⟨g, le_antisymm (fun y hy => ?_) ?_⟩
    · obtain ⟨s, c, hsc⟩ := hmul y hy
      rw [hag] at hsc
      obtain ⟨c', hc'⟩ := hx.pow_dvd_of_dvd_mul_left s hxg
        (⟨y, by linear_combination -hsc⟩ : x ^ s ∣ g * (x ^ multiplicity x (a : A) * c))
      have hy : y = g * c' :=
        mul_left_cancel₀ (pow_ne_zero s hx0) (by linear_combination hsc + g * hc')
      rw [hy]
      exact Submodule.mem_span_singleton.2 ⟨c', by rw [smul_eq_mul, mul_comm]⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hg

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
open IsLocalRing in
private lemma uniqueFactorizationMonoid_localization_of_height_le
    (hPD : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
      [Module.Finite R M], ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n)
    (hPrin : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] (x : R)
      (R' : Type) [CommRing R'] [Algebra R R'] [IsLocalization.Away x R'] (I : Ideal R) (n : ℕ),
      HasProjectiveDimensionLE (ModuleCat.of R I) n →
      Module.Projective R' (I.map (algebraMap R R')) → (I.map (algebraMap R R')).IsPrincipal)
    {R : Type} [CommRing R] [IsRegularRing R] (n : ℕ) :
    ∀ (Q : Ideal R) [Q.IsPrime], Q.height ≤ n → UniqueFactorizationMonoid (Localization.AtPrime Q) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Q _ hQ
  rw [UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one]
  intro p _ hph
  by_cases hm : ∃ x ∈ maximalIdeal (Localization.AtPrime Q), x ∉ maximalIdeal (Localization.AtPrime Q) ^ 2
  · obtain ⟨x, hx, hx2⟩ := hm
    have hxp := prime_of_mem_maximalIdeal_of_not_mem_sq hx hx2
    by_cases hxmem : x ∈ p
    · exact ⟨x, Ideal.eq_span_singleton_of_height_eq_one hph hxmem hxp⟩
    · refine isPrincipal_of_isPrincipal_map_away_prime hxp hxmem ?_
      obtain ⟨N, hN⟩ := hPD (Localization.AtPrime Q) p
      refine hPrin _ x (Localization.Away x) p N hN ?_
      haveI : Module.FinitePresentation (Localization.Away x)
          (p.map (algebraMap (Localization.AtPrime Q) (Localization.Away x))) :=
        Module.finitePresentation_of_finite _ _
      refine Module.projective_of_localization_maximal (fun q hq => ?_)
      haveI := hq.isPrime
      haveI hloc₁ : IsLocalization.AtPrime (Localization.AtPrime q)
          (q.comap (algebraMap (Localization.AtPrime Q) (Localization.Away x))) :=
        IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers x) _ q
      set q₁ := q.comap (algebraMap (Localization.AtPrime Q) (Localization.Away x)) with hq₁
      haveI hloc₂ : IsLocalization.AtPrime (Localization.AtPrime q) (q₁.comap (algebraMap R (Localization.AtPrime Q))) :=
        IsLocalization.isLocalization_isLocalization_atPrime_isLocalization Q.primeCompl _ q₁
      set q₂ := q₁.comap (algebraMap R (Localization.AtPrime Q)) with hq₂
      have hxq₁ : x ∉ q₁ := fun h => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ h
        (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away x) x))
      have hq₁m : q₁ ≤ maximalIdeal (Localization.AtPrime Q) :=
        IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ hq.ne_top)
      have hq₂Q : q₂ < Q := by
        refine lt_of_le_of_ne ?_ ?_
        · rw [← IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime Q) Q]
          exact Ideal.comap_mono hq₁m
        · intro h
          apply hxq₁
          have := IsLocalization.map_comap Q.primeCompl (Localization.AtPrime Q) q₁
          rw [← this]
          change x ∈ Ideal.map _ q₂
          rw [h, IsLocalization.AtPrime.map_eq_maximalIdeal]
          exact hx
      have hlt : q₂.height < n := lt_of_lt_of_le (Ideal.height_strict_mono_of_isPrime hq₂Q) hQ
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hlt)
      have hmn : m < n := by rw [← hm] at hlt; exact_mod_cast hlt
      haveI := ih m hmn q₂ hm.symm.le
      haveI : UniqueFactorizationMonoid (Localization.AtPrime q) :=
        (IsLocalization.algEquiv q₂.primeCompl (Localization.AtPrime q₂)
          (Localization.AtPrime q)).toMulEquiv.uniqueFactorizationMonoid inferInstance
      haveI : IsDomain (Localization.AtPrime q) :=
        (IsLocalization.algEquiv q₂.primeCompl (Localization.AtPrime q₂)
          (Localization.AtPrime q)).toRingEquiv.symm.injective.isDomain _
      have hJ : (p.map (algebraMap (Localization.AtPrime Q) (Localization.Away x))).map
          (algebraMap (Localization.Away x) (Localization.AtPrime q)) =
          p.map (algebraMap (Localization.AtPrime Q) (Localization.AtPrime q)) := by
        rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      have hJprin : (p.map (algebraMap (Localization.AtPrime Q) (Localization.AtPrime q))).IsPrincipal := by
        by_cases hdisj : p ≤ q₁
        · have hd : Disjoint (q₁.primeCompl : Set (Localization.AtPrime Q)) p :=
            Set.disjoint_left.2 fun a ha hap => ha (hdisj hap)
          haveI := IsLocalization.isPrime_of_isPrime_disjoint q₁.primeCompl (Localization.AtPrime q) p ‹_› hd
          exact UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
            (by rw [IsLocalization.height_map_of_disjoint q₁.primeCompl p hd, hph])
        · obtain ⟨a, hap, haq⟩ := Set.not_subset.1 hdisj
          have htop : p.map (algebraMap (Localization.AtPrime Q) (Localization.AtPrime q)) = ⊤ :=
            Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hap)
              (IsLocalization.map_units (Localization.AtPrime q) (⟨a, haq⟩ : q₁.primeCompl))
          rw [htop]
          exact ⟨1, Ideal.span_singleton_one.symm⟩
      obtain ⟨g, hg⟩ := hJprin
      haveI : Module.Free (Localization.AtPrime q)
          (p.map (algebraMap (Localization.AtPrime Q) (Localization.AtPrime q))) := by
        by_cases hg0 : g = 0
        · have hbot : p.map (algebraMap (Localization.AtPrime Q) (Localization.AtPrime q)) = ⊥ := by
            rw [hg, hg0]; exact Submodule.span_singleton_eq_bot.2 rfl
          rw [hbot]; infer_instance
        · rw [hg]; exact Module.Free.of_equiv (LinearEquiv.toSpanNonzeroSingleton _ _ g hg0)
      have heq : Submodule.localized' (Localization.AtPrime q) q.primeCompl
          (Algebra.linearMap (Localization.Away x) (Localization.AtPrime q))
          (p.map (algebraMap (Localization.AtPrime Q) (Localization.Away x))) =
          p.map (algebraMap (Localization.AtPrime Q) (Localization.AtPrime q)) := by
        rw [Ideal.localized'_eq_map, hJ]
      exact Module.Projective.of_equiv (((IsLocalizedModule.iso q.primeCompl
        (Submodule.toLocalized' (Localization.AtPrime q) q.primeCompl
          (Algebra.linearMap (Localization.Away x) (Localization.AtPrime q))
          (p.map (algebraMap (Localization.AtPrime Q) (Localization.Away x))))).extendScalarsOfIsLocalization
        q.primeCompl (Localization.AtPrime q)).trans (LinearEquiv.ofEq _ _ heq)).symm
  · push_neg at hm
    have hbot := _root_.ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.maximalIdeal_eq_bot_of_le_sq (Localization.AtPrime Q) hm
    have hp : p = ⊥ := le_bot_iff.1 (hbot ▸ IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›))
    exact absurd hph (by rw [hp, Ideal.height_bot]; exact zero_ne_one)

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
attribute [local instance] Over.cartesianMonoidalCategory in
open IsLocalRing in

theorem _root_.GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing :
    (∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
      [Module.Finite R M], ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n) →
    (∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] (x : R)
      (R' : Type) [CommRing R'] [Algebra R R'] [IsLocalization.Away x R'] (I : Ideal R) (n : ℕ),
      HasProjectiveDimensionLE (ModuleCat.of R I) n →
      Module.Projective R' (I.map (algebraMap R R')) → (I.map (algebraMap R R')).IsPrincipal) →
    ∀ (R : Type) [CommRing R] [IsRegularRing R] [IsLocalRing R] [IsDomain R],
      UniqueFactorizationMonoid R := by
  intro hPD hPrin R _ _ _ _
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (Ideal.height_ne_top (maximalIdeal.isMaximal R).ne_top)
  haveI := uniqueFactorizationMonoid_localization_of_height_le hPD hPrin n (maximalIdeal R) hn.symm.le
  exact (IsLocalization.atUnits R (maximalIdeal R).primeCompl
    (S := Localization.AtPrime (maximalIdeal R))
    (fun y hy => IsLocalRing.notMem_maximalIdeal.1 hy)).symm.toMulEquiv.uniqueFactorizationMonoid
    inferInstance

end GlobalTheory
end

