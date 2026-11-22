import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0313
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteClassesModuloInvolutionNorms
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0327

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqDiscriminantPowMulEvalJInvariant
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm (E₄ E₆) in

theorem _root_.GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT : ∀ (R : Subring ℂ) (N w : ℕ)
    (f : ℍ → ℂ), 0 < N →
    (∀ γ : SL(2, ℤ), f ∣[(12 * w : ℤ)] γ = f) → _root_.GlobalTheory.QFam.QAll (· ∈ R) N f →
    ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ ∀ τ, f τ = _root_.ReciprocityTheory.ChartRestriction.L1.DD τ ^ w * P.eval (_root_.ReciprocityTheory.ChartRestriction.L1.jT τ) := by
  intro R N w f hN hinv hq
  obtain ⟨a, ha, haR⟩ := hq
  have hmf : _root_.ReciprocityTheory.ChartRestriction.L1.IsMF (12 * w) f := _root_.GlobalTheory.QFam.isMF_of_invariant_of_hasQ N _ f a hN hinv ha
  have h1 : _root_.GlobalTheory.QFam.HasQ 1 f fun n => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f) := by
    rw [_root_.GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion]
    obtain ⟨g, hg⟩ := hmf
    have hgf : (⇑g : ℍ → ℂ) = f := funext hg
    have h := _root_.GlobalTheory.hasQExpansion_modularForm g
    rw [hgf] at h
    simpa using h
  have hN' := _root_.GlobalTheory.QFam.hasQ_mul_spread 1 N f _ one_pos hN h1
  rw [one_mul] at hN'
  have heq := _root_.GlobalTheory.QFam.HasQ.coeff_unique hN ha hN'
  have hcoeff : _root_.ReciprocityTheory.ChartRestriction.L1.CoeffIn R (UpperHalfPlane.qExpansion 1 f) := by
    intro m
    have h := haR (N * m)
    rw [heq] at h
    simpa [_root_.GlobalTheory.QFam.spread, Nat.mul_div_cancel_left _ hN] using h
  obtain ⟨P, hPR, -, hP⟩ := _root_.ReciprocityTheory.ChartRestriction.L1.qPrin R w f hmf hcoeff
  exact ⟨P, hPR, hP⟩

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoverModelOfIsColimit
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtaleCoverDescent

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in

theorem _root_.GlobalTheory.EtaleCoverDescent.exists_point_of_isPushout {R S T P : CommRingCat.{0}} {f : R ⟶ S} {g : R ⟶ T}
    {inl : S ⟶ P} {inr : T ⟶ P} (H : IsPushout f g inl inr) (x : Spec S) (y : Spec T)
    (hxy : Spec.map f x = Spec.map g y) : ∃ z : Spec P, Spec.map inl z = x := by
  have hP := isPullback_SpecMap_of_isPushout f g inl inr H
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  refine ⟨hP.isoPullback.inv w, ?_⟩
  rw [← Scheme.Hom.comp_apply, hP.isoPullback_inv_fst]
  exact hw

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
private lemma exists_etale_pushout_of_filtered_colimit (J : Type) [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (hc : IsColimit c) {B : CommRingCat.{0}}
    (g : c.pt ⟶ B) (hg : g.hom.Etale) :
    ∃ (j : J) (B' : CommRingCat.{0}) (a : D.obj j ⟶ B') (h : B' ⟶ B),
      a.hom.Etale ∧ IsPushout a (c.ι.app j) h g := by
  letI := g.hom.toAlgebra
  haveI : Algebra.Etale c.pt B := hg
  obtain ⟨j, A, _, _, hA, ⟨e⟩⟩ := _root_.GlobalTheory.EtaleDescent.exists_etale_model_of_isColimit J D c hc B
  letI : Algebra (D.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  refine ⟨j, CommRingCat.of A, CommRingCat.ofHom (algebraMap (D.obj j) A),
    CommRingCat.ofHom ((e : TensorProduct (D.obj j) c.pt A →+* B).comp
      Algebra.TensorProduct.includeRight.toRingHom), ?_, ?_⟩
  · exact RingHom.etale_algebraMap.mpr hA
  · refine (CommRingCat.isPushout_tensorProduct (D.obj j) c.pt A).flip.of_iso (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (RingEquiv.toCommRingCatIso e.toRingEquiv) ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · ext x
      rfl
    · ext x
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      exact e.commutes x

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
private lemma exists_etale_pushout_at_later_index_of_range {J : Type} [SmallCategory J]
    {D : J ⥤ CommRingCat.{0}} (c : Cocone D) {k k' : J} (f : k ⟶ k') {B B' : CommRingCat.{0}}
    {g : c.pt ⟶ B} {a : D.obj k ⟶ B'} {h : B' ⟶ B} (ha : a.hom.Etale)
    (H : IsPushout a (c.ι.app k) h g) :
    ∃ (B'' : CommRingCat.{0}) (a' : D.obj k' ⟶ B'') (h' : B'' ⟶ B),
      a'.hom.Etale ∧ IsPushout a' (c.ι.app k') h' g ∧
      ∀ p : Spec (D.obj k'), Spec.map (D.map f) p ∈ Set.range (Spec.map a) →
        p ∈ Set.range (Spec.map a') := by
  have hw : D.map f ≫ c.ι.app k' ≫ g = a ≫ h := by
    rw [H.w, ← c.w f, Category.assoc]
  refine ⟨pushout (D.map f) a, pushout.inl (D.map f) a,
    pushout.desc (c.ι.app k' ≫ g) h hw, ?_, ?_, ?_⟩
  · exact RingHom.Etale.isStableUnderBaseChange.pushout_inl RingHom.Etale.respectsIso _ _ ha
  · have top : IsPushout a (D.map f) (pushout.inr (D.map f) a) (pushout.inl (D.map f) a) :=
      (IsPushout.of_hasPushout (D.map f) a).flip
    have big : IsPushout a (D.map f ≫ c.ι.app k')
        (pushout.inr (D.map f) a ≫ pushout.desc (c.ι.app k' ≫ g) h hw) g := by
      rw [c.w f, pushout.inr_desc]
      exact H
    exact big.of_top (pushout.inl_desc _ _ _) top
  · rintro p ⟨v, hv⟩
    obtain ⟨z, hz⟩ := _root_.GlobalTheory.EtaleCoverDescent.exists_point_of_isPushout (IsPushout.of_hasPushout (D.map f) a) p v hv.symm
    exact ⟨z, hz⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in

theorem _root_.GlobalTheory.EtaleCoverDescent.exists_etale_cover_model_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (ι : Type) [Finite ι] (B : ι → CommRingCat.{0}) (g : ∀ i, c.pt ⟶ B i), (∀ i, (g i).hom.Etale) → (∀ p : Spec c.pt, ∃ i v, Spec.map (g i) v = p) → ∀ j₀ : J, ∃ (j : J) (_ : j₀ ⟶ j) (B' : ι → CommRingCat.{0}) (g' : ∀ i, D.obj j ⟶ B' i) (h : ∀ i, B' i ⟶ B i), (∀ i, (g' i).hom.Etale ∧ IsPushout (g' i) (c.ι.app j) (h i) (g i)) ∧ ∀ p : Spec (D.obj j), ∃ i v, Spec.map (g' i) v = p := by
  intro J _ _ D c hc ι _ B g hg hsurj j₀
  classical
  have := Fintype.ofFinite ι
  choose jm Bm am hm ham hHm using fun i => exists_etale_pushout_of_filtered_colimit J D c hc (g i) (hg i)
  let O : Finset J := insert j₀ (Finset.univ.image jm)
  let j1 := IsFiltered.sup O ∅
  have f0 : j₀ ⟶ j1 := IsFiltered.toSup O ∅ (Finset.mem_insert_self _ _)
  have fm : ∀ i, jm i ⟶ j1 := fun i =>
    IsFiltered.toSup O ∅ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  choose B1 a1 h1 ha1 hH1 _ using fun i => exists_etale_pushout_at_later_index_of_range c (fm i) (ham i) (hHm i)
  let W : Set (Spec (D.obj j1)) := {q | ∀ i, q ∉ Set.range (Spec.map (a1 i))}
  have hW : IsClosed W := by
    have hWe : W = (⋃ i, Set.range (Spec.map (a1 i)))ᶜ := by
      ext q
      simp [W]
    rw [hWe, isClosed_compl_iff]
    refine isOpen_iUnion fun i => ?_
    have : Etale (Spec.map (a1 i)) := by
      rw [HasRingHomProperty.Spec_iff (P := @Etale)]
      exact ha1 i
    exact (Spec.map (a1 i)).isOpenMap.isOpen_range
  have claim : ∃ (k : J) (f : j1 ⟶ k), ∀ p : Spec (D.obj k), Spec.map (D.map f) p ∉ W := by
    by_contra hcon
    push_neg at hcon
    haveI : ∀ {i i' : Jᵒᵖ} (f : i ⟶ i'), IsAffineHom ((D.op ⋙ Scheme.Spec).map f) :=
      fun f => inferInstanceAs (IsAffineHom (Spec.map (D.map f.unop)))
    obtain ⟨s, hs⟩ := exists_mem_of_isClosed_of_nonempty' (D.op ⋙ Scheme.Spec)
      (Scheme.Spec.mapCone c.op) (isLimitOfPreserves Scheme.Spec hc.op) (j := op j1)
      (fun i hij => (Spec.map (D.map hij.unop)) ⁻¹' W)
      (fun i hij => hW.preimage (Spec.map _).continuous)
      (fun i hij => hcon _ hij.unop)
      (fun i hij => (hW.preimage (Spec.map _).continuous).isCompact)
      (fun i i' hi'i hij x hx => by
        change Spec.map (D.map hij.unop) (Spec.map (D.map hi'i.unop) x) ∈ W
        rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, ← D.map_comp]
        exact hx)
    have hs1 : Spec.map (c.ι.app j1) s ∈ W := by
      have := hs (op j1) (𝟙 _)
      change Spec.map (D.map (𝟙 j1)) (Spec.map (c.ι.app j1) s) ∈ W at this
      simpa [D.map_id, Spec.map_id] using this
    obtain ⟨i, v, rfl⟩ := hsurj s
    refine hs1 i ⟨Spec.map (h1 i) v, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, (hH1 i).w, Spec.map_comp, Scheme.Hom.comp_apply]
  obtain ⟨k, f, hk⟩ := claim
  choose B2 a2 h2 ha2 hH2 hpt using fun i => exists_etale_pushout_at_later_index_of_range c f (ha1 i) (hH1 i)
  refine ⟨k, f0 ≫ f, B2, a2, h2, fun i => ⟨ha2 i, hH2 i⟩, fun p => ?_⟩
  have hp := hk p
  simp only [W, Set.mem_setOf_eq, not_forall, not_not] at hp
  obtain ⟨i, hi⟩ := hp
  obtain ⟨v, hv⟩ := hpt i p hi
  exact ⟨i, v, hv⟩

end GlobalTheory.EtaleCoverDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFactorOfIndEt
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_etale_factor_of_indEt : ∀ (A O : Type) [CommRing A] [CommRing O] [Algebra A O], IndEt A O → ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B] (φ : B →ₐ[A] O), ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.Etale A C) (ψ : B →ₐ[A] C) (χ : C →ₐ[A] O), χ.comp ψ = φ := by
  intro A O _ _ _ hO B _ _ _ φ
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := hO
  have hp : MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0}
      (CommRingCat.ofHom (algebraMap A B)) :=
    CommRingCat.isFinitelyPresentable_hom _ (RingHom.finitePresentation_algebraMap.2 inferInstance)
  obtain ⟨j, q, hq1, hq2⟩ := MorphismProperty.exists_hom_of_isFinitelyPresentable hs hp t
    (CommRingCat.ofHom φ.toRingHom) (fun j => by
      rw [(hst j).2]; ext a; simp)
  letI : Algebra A (D.obj j) := (t.app j).hom.toAlgebra
  haveI : Algebra.Etale A (D.obj j) := (hst j).1
  have h1 : ∀ a : A, q.hom (algebraMap A B a) = algebraMap A (D.obj j) a := fun a =>
    congrArg (fun f => f.hom a) hq1
  have h2 : ∀ a : A, (s.app j).hom (algebraMap A (D.obj j) a) = algebraMap A O a := fun a =>
    congrArg (fun f => f.hom a) (hst j).2
  have h3 : ∀ b : B, (s.app j).hom (q.hom b) = φ b := fun b =>
    congrArg (fun f => f.hom b) hq2
  refine ⟨D.obj j, inferInstance, inferInstance, inferInstance, ⟨q.hom, h1⟩, ⟨(s.app j).hom, h2⟩, ?_⟩
  ext b
  exact h3 b

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFaithfullyFlatPicMapAlgebraEqOne
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.PicLoc

theorem exists_away_mapAlgebra_eq_one : ∀ (A : Type) [CommRing A] (c : CommRing.Pic A) (p : Ideal A) [p.IsPrime], ∃ f ∉ p, CommRing.Pic.mapAlgebra A (Localization.Away f) c = 1 := by
  intro A _ c p _
  letI := @Module.addCommMonoidToAddCommGroup A
  haveI : Module.FinitePresentation A c := Module.finitePresentation_of_projective A c
  haveI : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl c) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl c) (Localization.AtPrime p)
  refine ⟨f, hf, ?_⟩
  rw [CommRing.Pic.mapAlgebra_apply, CommRing.Pic.mk_eq_one_iff_free]
  exact Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers f) c)

theorem exists_etale_faithfullyFlat_mapAlgebra_eq_one : ∀ (A : Type) [CommRing A] (c : CommRing.Pic A), ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.Etale A B) (_ : Module.FaithfullyFlat A B), CommRing.Pic.mapAlgebra A B c = 1 := by
  intro A _ c
  classical
  let T : Set A := {f | CommRing.Pic.mapAlgebra A (Localization.Away f) c = 1}
  have hT : Ideal.span T = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨f, hf, hf1⟩ := exists_away_mapAlgebra_eq_one A c m
    exact hf (hle (Ideal.subset_span hf1))
  obtain ⟨s, hsT, hs⟩ := (Ideal.span_eq_top_iff_finite T).mp hT
  let R : s → Type := fun i => Localization.Away (i : A)
  haveI : ∀ i, Algebra.Etale A (R i) := fun i => Algebra.Etale.of_isLocalizationAway (i : A)
  have halg : ∀ i, (Pi.evalRingHom R i).comp (algebraMap A ((i : s) → R i)) = algebraMap A (R i) :=
    fun i => RingHom.ext fun _ => rfl
  refine ⟨(i : s) → R i, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_
    obtain ⟨i, hi⟩ : ∃ i : s, (i : A) ∉ p.asIdeal := by
      by_contra h
      push Not at h
      apply p.isPrime.ne_top
      rw [eq_top_iff, ← hs, Ideal.span_le]
      intro x hx
      exact h ⟨x, hx⟩
    have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (R i))) := by
      rw [PrimeSpectrum.localization_away_comap_range (R i) (i : A)]
      exact hi
    obtain ⟨q, rfl⟩ := hp
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom R i) q, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply, halg]
  · apply GlobalTheory.PicPi.eq_one_of_forall
    intro i
    rw [← CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapRingHom_mapRingHom, halg,
      CommRing.Pic.mapRingHom_algebraMap]
    exact hsT i.2

end GlobalTheory.PicLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFaithfullyFlatRefiningEtaleSurjection
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etale_sigmaDesc_of_isOpenImmersion {ι : Type} (V : Scheme.{0}) (Y : ι → Scheme.{0})
    (u : ∀ i, Y i ⟶ V) [∀ i, IsOpenImmersion (u i)] : Etale (Sigma.desc u) := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  exact IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance

theorem etFF_preimage_of_etale_surjective (A B : CommRingCat.{0}) (k : Spec B ⟶ Spec A)
    [Etale k] [Surjective k] : EtFF (Spec.preimage k) := by
  rw [(GlobalTheory.T.etaleFaithfullyFlatRingHom_basic_properties.2.1 A B _), Spec.map_preimage]
  exact ⟨inferInstance, inferInstance⟩

theorem exists_etFF_of_isAffine (A : CommRingCat.{0}) (X V : Scheme.{0}) [IsAffine X]
    (h' : X ⟶ V) (f : V ⟶ Spec A) [Etale (h' ≫ f)] [Surjective (h' ≫ f)] :
    ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (h : Spec B ⟶ V), EtFF g ∧ h ≫ f = Spec.map g := by
  have he : Etale (X.isoSpec.inv ≫ h' ≫ f) := inferInstance
  have hs : Surjective (X.isoSpec.inv ≫ h' ≫ f) := inferInstance
  refine ⟨Γ(X, ⊤), Spec.preimage (X.isoSpec.inv ≫ h' ≫ f), X.isoSpec.inv ≫ h',
    etFF_preimage_of_etale_surjective _ _ _, ?_⟩
  rw [Spec.map_preimage, Category.assoc]

theorem exists_etFF_refine_of_etale_surjective :
    ∀ (A : CommRingCat.{0}) (V : Scheme.{0}) (f : V ⟶ Spec A), Etale f → Surjective f →
      ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (h : Spec B ⟶ V), EtFF g ∧ h ≫ f = Spec.map g := by
  intro A V f hf hs
  have hopen : ∀ x : V.affineCover.I₀, IsOpen (Set.range (V.affineCover.f x ≫ f)) := fun x =>
    (V.affineCover.f x ≫ f).isOpenMap.isOpen_range
  have hcov : Set.univ ⊆ ⋃ x : V.affineCover.I₀, Set.range (V.affineCover.f x ≫ f) := by
    intro y _
    obtain ⟨v, rfl⟩ := f.surjective y
    obtain ⟨x, hx⟩ := V.affineCover.covers v
    exact Set.mem_iUnion.mpr ⟨V.affineCover.idx v, ⟨_, by rw [Scheme.Hom.comp_apply, hx]⟩⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen hcov
  let Y : t → Scheme.{0} := fun i => V.affineCover.X i.1
  let u : ∀ i, Y i ⟶ V := fun i => V.affineCover.f i.1
  haveI : ∀ i, IsAffine (Y i) := fun i => inferInstanceAs (IsAffine (Spec _))
  haveI : ∀ i, IsOpenImmersion (u i) := fun i => inferInstanceAs (IsOpenImmersion (V.affineCover.f i.1))
  haveI : Etale (Sigma.desc u) := etale_sigmaDesc_of_isOpenImmersion V Y u
  have hcomp : Sigma.desc u ≫ f = Sigma.desc fun i => u i ≫ f := by
    ext i; simp
  haveI hsurj : Surjective (Sigma.desc u ≫ f) := by
    rw [hcomp]
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    refine Set.eq_univ_of_univ_subset (fun y hy => ?_)
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (ht hy)
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hy⟩
  exact exists_etFF_of_isAffine A (∐ Y) V (Sigma.desc u) f

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleLocalRootOfUnitOfKummer
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.KumRoots

theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  choose R hR hRQ using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => h V g (hSP V g hg)
  refine ⟨Sieve.bind S.arrows (fun V g hg => R V g hg),
    Scheme.etaleTopology.bind_covering hS (fun V g hg => hR V g hg), ?_⟩
  rintro W f ⟨V, k, g, hg, hk, rfl⟩
  exact hRQ V g hg W k hk

abbrev unitsP : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} ℤ) := Scheme.Γ ⋙ unitsF

theorem unitSec_eq {U : Scheme.{0}} (u : (Γ(U, ⊤))ˣ) :
    unitSec u = ((toSheafify Scheme.etaleTopology unitsP).app (op U)).hom (ULift.up (Additive.ofMul u)) := rfl

theorem res_unitSec {V U : Scheme.{0}} (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Sec.res g (unitSec u) = unitSec (Units.map g.appTop.hom.toMonoidHom u) := by
  have := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology unitsP).naturality g.op)
    (ULift.up (Additive.ofMul u))
  exact this.symm

theorem unitSec_pow {U : Scheme.{0}} (q : ℕ) (v : (Γ(U, ⊤))ˣ) :
    unitSec (v ^ q) = Sec.map ((q : ℤ) • 𝟙 Gm) (unitSec v) := by
  have h1 : (ULift.up (Additive.ofMul (v ^ q)) : unitsP.obj (op U)) = (q : ℤ) • ULift.up (Additive.ofMul v) := by
    apply ULift.ext
    change Additive.ofMul (v ^ q) = (q : ℤ) • Additive.ofMul v
    rw [natCast_zsmul, ofMul_pow]
  change _ = (q : ℤ) • unitSec v
  rw [unitSec_eq, unitSec_eq, h1]
  exact map_zsmul ((toSheafify Scheme.etaleTopology unitsP).app (op U)).hom (q : ℤ) _

end GlobalTheory.EtC.KumRoots

namespace GlobalTheory.EtC.KumRoots

theorem res_comp {V W U : Scheme.{0}} (g : V ⟶ U) (k : W ⟶ V) (x : Sec Gm U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  change (Gm.obj.map (k ≫ g).op).hom x = (Gm.obj.map k.op).hom ((Gm.obj.map g.op).hom x)
  rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem units_map_comp {X W U : Scheme.{0}} (k : X ⟶ W) (f : W ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map (k ≫ f).appTop.hom.toMonoidHom u =
      Units.map k.appTop.hom.toMonoidHom (Units.map f.appTop.hom.toMonoidHom u) := by
  apply Units.ext
  change (k ≫ f).appTop.hom (u : Γ(U, ⊤)) = k.appTop.hom (f.appTop.hom u)
  rw [Scheme.Hom.comp_appTop]; rfl

theorem roots : ∀ (q : ℕ) [NeZero q],
    (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b) →
    ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ,
      Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u := by
  intro q _ hyp U hq u
  refine loc_bind (hyp U hq (unitSec u)) ?_
  rintro V g ⟨c, hc⟩
  refine loc_bind (P := fun W h => ∃ v : (Γ(W, ⊤))ˣ, unitSec v = Sec.res h c)
    ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology unitsP) (U := op V) c, ?_⟩ ?_
  · rintro W h ⟨t, ht⟩
    exact ⟨Additive.toMul t.down, ht⟩
  · rintro W h ⟨v, hv⟩
    have heq : unitSec (v ^ q) = unitSec (Units.map (h ≫ g).appTop.hom.toMonoidHom u) :=
      calc unitSec (v ^ q) = Sec.map ((q : ℤ) • 𝟙 Gm) (unitSec v) := unitSec_pow q v
        _ = Sec.map ((q : ℤ) • 𝟙 Gm) (Sec.res h c) := by rw [hv]
        _ = Sec.res h (Sec.map ((q : ℤ) • 𝟙 Gm) c) :=
          ConcreteCategory.congr_hom ((((q : ℤ) • 𝟙 Gm : Gm ⟶ Gm)).hom.naturality h.op) c
        _ = Sec.res h (Sec.res g (unitSec u)) := by rw [hc]
        _ = Sec.res (h ≫ g) (unitSec u) := (res_comp g h _).symm
        _ = unitSec (Units.map (h ≫ g).appTop.hom.toMonoidHom u) := res_unitSec _ _
    rw [unitSec_eq, unitSec_eq] at heq
    refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology unitsP)
      (X := op W) _ _ heq, ?_⟩
    intro X k hk
    have hk' : Units.map k.appTop.hom.toMonoidHom (v ^ q) =
        Units.map k.appTop.hom.toMonoidHom (Units.map (h ≫ g).appTop.hom.toMonoidHom u) :=
      congrArg (fun z : ULift.{1} (Additive (Γ(X, ⊤))ˣ) => Additive.toMul z.down) hk
    refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
    rw [← map_pow, hk', Category.assoc, units_map_comp k (h ≫ g)]

end GlobalTheory.EtC.KumRoots
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitEtaleOfIndEt
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

theorem exists_filtered_colimit_etale_of_indEt : ∀ (A O : Type) [CommRing A] [CommRing O] [Algebra A O], IndEt A O → ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ Under (CommRingCat.of A)) (ι : D ⟶ (Functor.const J).obj (Under.mk (CommRingCat.ofHom (algebraMap A O)))), Nonempty (IsColimit (Cocone.mk _ ι)) ∧ ∀ j, (D.obj j).hom.hom.Etale := by
  intro A O _ _ _ h
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := h
  have : Nonempty J := IsFiltered.nonempty
  refine ⟨J, inferInstance, inferInstance, Under.lift D t,
    { app j := Under.homMk (s.app j) (by simp [hst]) },
    ⟨Under.isColimitLiftCocone _ _ _ _ (by simp [hst]) hs⟩, fun j => (hst j).1⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteClassesModuloInvolutionNormsStatement
section
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_classes_modulo_involutionNorms : ∀ (K : Type) [Field K] [NumberField K] (τ : K ≃+* K), (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ,
    ∃ M : Finset K, ∀ a : K, a ≠ 0 → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : K), b ≠ 0 ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : K) * x) ∧ IsIntegral ℤ ((d : K) * y)) →
    ∃ m ∈ M, ∃ e : K, e ≠ 0 ∧ a = e * m * τ e := by
  first | (exact @GlobalTheory.FixNormField.fixed_classes_mod_norms) | (exact GlobalTheory.FixNormField.fixed_classes_mod_norms) | (intros; apply GlobalTheory.FixNormField.fixed_classes_mod_norms  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDepthTwoHullOfEtalePuncturedSpectrumStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_depth_two_hull_of_etale_punctured_spectrum : ∀ (S : Type) [CommRing S] [IsRegularLocalRing S], 2 ≤ ringKrullDim S → ∀ (A : Type) [CommRing A] [Algebra S A] [Module.Finite S A], ReciprocityTheory.CA.ModDepthGE S A 1 → (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A)) → ∃ (A' : Type) (_ : CommRing A') (_ : Algebra S A'), Module.Finite S A' ∧ ∃ ι : A →ₐ[S] A', Function.Injective ι ∧ ReciprocityTheory.CA.ModDepthGE S A' 2 ∧ (∀ (p : Ideal S) [p.IsPrime], p ≠ maximalIdeal S → Algebra.Etale (Localization.AtPrime p) (TensorProduct S (Localization.AtPrime p) A')) ∧ ∃ k : ℕ, ∀ x ∈ maximalIdeal S ^ k, ∀ y : A', x • y ∈ ι.range := by
  first | exact @GlobalTheory.exists_finite_depth_two_hull_of_etale_off_closed_point | exact GlobalTheory.exists_finite_depth_two_hull_of_etale_off_closed_point | (intros; apply GlobalTheory.exists_finite_depth_two_hull_of_etale_off_closed_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePresentationModelOfIsColimitStatement
section
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finitePresentation_descent_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (D : Type) [CommRing D] [Algebra c.pt D], Algebra.FinitePresentation c.pt D →
    ∃ (j : J) (A : Type) (_ : CommRing A) (_ : Algebra (F.obj j) A)
      (_ : Algebra.FinitePresentation (F.obj j) A),
      letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra;
      Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) := by
  first | (exact @GlobalTheory.FpDescent.exists_finitePresentation_model_of_isColimit) | (exact GlobalTheory.FpDescent.exists_finitePresentation_model_of_isColimit) | (intros; apply GlobalTheory.FpDescent.exists_finitePresentation_model_of_isColimit  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetEqSumAddCosetIndicatorStatement
section
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_eq_sum_addCosetIndicator : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (L : AddSubgroup X), IsOpen (L : Set X) → ∀ f ∈ GlobalTheory.WeilM.SB X, (∀ Y, ∀ C ∈ L, f (Y + C) = f Y) → ∃ F : Finset X, f = ∑ y ∈ F, f y • GlobalTheory.LinSchur.cind L y := by
  first | exact @GlobalTheory.LinSchur.exists_finset_eq_sum_cind | exact GlobalTheory.LinSchur.exists_finset_eq_sum_cind | (intros; apply GlobalTheory.LinSchur.exists_finset_eq_sum_cind <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFirstMaximalMinor
section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem exists_isFirstMax : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k),
    (∃ J, minor Y J ≠ 0) → ∃ J, IsFirstMax Y J := by
  intro k _ _ _ _ a d Y ⟨J0, hJ0⟩
  classical
  obtain ⟨M, -, hM⟩ := Finset.exists_max_image Finset.univ (fun J => valuation k (minor Y J))
    ⟨J0, Finset.mem_univ _⟩
  set S := Finset.univ.filter (fun J => valuation k (minor Y J) = valuation k (minor Y M)) with hS
  obtain ⟨J, hJS, hJmin⟩ := S.exists_min_image (fun J => idx J) ⟨M, by simp [S]⟩
  have hJ : valuation k (minor Y J) = valuation k (minor Y M) := (Finset.mem_filter.1 hJS).2
  refine ⟨J, ?_, fun J' => ⟨?_, fun hlt => ?_⟩⟩
  · intro h0
    apply hJ0
    have hM0 : valuation k (minor Y M) = 0 := by rw [← hJ, h0, map_zero]
    have h1 := hM J0 (Finset.mem_univ _)
    rw [hM0] at h1
    exact (Valuation.zero_iff _).1 (le_antisymm h1 zero_le')
  · rw [hJ]; exact hM J' (Finset.mem_univ _)
  · rw [hJ]
    refine lt_of_le_of_ne (hM J' (Finset.mem_univ _)) fun heq => ?_
    have := hJmin J' (by simp [S, heq])
    exact absurd hlt (not_lt.2 this)

end GlobalTheory.RankFibreKer
end

