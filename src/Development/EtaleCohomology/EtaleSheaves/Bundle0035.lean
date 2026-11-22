import Development.EtaleCohomology.EtaleSheaves.Bundle0017
import Development.EtaleCohomology.EtaleSheaves.Bundle0022
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.EtaleCohomology.EtaleSheaves.Bundle0024
import Development.EtaleCohomology.EtaleSheaves.Bundle0011
import Development.EtaleCohomology.EtaleSheaves.Bundle0020
import Development.EtaleCohomology.EtaleSheaves.Bundle0023
import Development.EtaleCohomology.EtaleSheaves.Bundle0026

-- bundled from Development.EtaleCohomology.EtaleSheaves.KummerInduction
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf LateralTheory.E.ContStepPf

namespace LateralTheory.E.StepKPf

variable {J : Type} [SmallCategory J]

def lv (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k : J} (f : k ⟶ j0) :
    (D.obj k).Opens := (D.map f ≫ e.hom) ⁻¹ᵁ U

def lm {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) : c.pt.Opens :=
  (c.π.app j0 ≫ e.hom) ⁻¹ᵁ U

theorem lm_le {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k : J}
    (f : k ⟶ j0) : lm c e U ≤ (c.π.app k) ⁻¹ᵁ lv D e U f := by
  rw [lm, lv, ← Scheme.Hom.comp_preimage, ← Category.assoc, c.w f]

theorem lv_le (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k l : J}
    (f : k ⟶ j0) (g : l ⟶ k) : lv D e U (g ≫ f) ≤ (D.map g) ⁻¹ᵁ lv D e U f := by
  rw [lv, lv, ← Scheme.Hom.comp_preimage, ← Category.assoc, ← D.map_comp]

def rL {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k : J}
    (f : k ⟶ j0) : (lm c e U).toScheme ⟶ (lv D e U f).toScheme :=
  (c.π.app k).resLE _ _ (lm_le c e U f)

def rD (D : J ⥤ Scheme.{0}) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) {k l : J}
    (f : k ⟶ j0) (g : l ⟶ k) : (lv D e U (g ≫ f)).toScheme ⟶ (lv D e U f).toScheme :=
  (D.map g).resLE _ _ (lv_le D e U f g)

def RC (q : ℕ) {D : J ⥤ Scheme.{0}} (c : Cone D) {j0 : J} {X : Scheme.{0}} (e : D.obj j0 ≅ X) (U : X.Opens) : Prop :=
  ∀ n i : ℤ,
  (∀ x : Ht q (sch.obj (lm c e U).toScheme) n i, ∃ (k : J) (f : k ⟶ j0) (y : Ht q (sch.obj (lv D e U f).toScheme) n i), pull _ (sch.map (rL c e U f)) _ _ y = x) ∧
  ∀ (k : J) (f : k ⟶ j0) (y : Ht q (sch.obj (lv D e U f).toScheme) n i), pull _ (sch.map (rL c e U f)) _ _ y = 0 →
    ∃ (l : J) (g : l ⟶ k), pull _ (sch.map (rD D e U f g)) _ _ y = 0

def Restr : Prop := Hyp → ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ (j0 : J) (X : Scheme.{0})
  (e : D.obj j0 ≅ X) (U : X.Opens), IsCompact ((e.hom ⁻¹ᵁ U : (D.obj j0).Opens) : Set (D.obj j0)) →
  PC U.toScheme → RC q c e U

def DiagramChase₂ : Prop := Hyp → MV → ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → ∀ (j0 : J) (X : Scheme.{0}) (e : D.obj j0 ≅ X) (U V : X.Opens), U ⊔ V = ⊤ →
  RC q c e U → RC q c e V → RC q c e (U ⊓ V) →
  ∀ (n i : ℤ) (k : J) (f : k ⟶ j0) (y : Ht q (sch.obj (D.obj k)) n i), pull _ (sch.map (c.π.app k)) _ _ y = 0 →
    ∃ (l : J) (g : l ⟶ k), pull _ (sch.map (D.map g)) _ _ y = 0

theorem cpt_pre {Y X : Scheme.{0}} (e : Y ≅ X) (U : X.Opens) (hU : IsCompact (U : Set X)) :
    IsCompact ((e.hom ⁻¹ᵁ U : Y.Opens) : Set Y) :=
  (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isCompact_preimage.mpr hU

theorem StepK_of (hR : Restr) (hC : DiagramChase₂) : StepK := by
  intro h hmv X U V hU hV hUV pU pV pW q J _ _ D c hc ha hcs hqs hu j0 ⟨e⟩ n i j y hy
  have := hqs j0
  have hU' := cpt_pre e U hU
  have hV' := cpt_pre e V hV
  have hW' : IsCompact ((e.hom ⁻¹ᵁ (U ⊓ V) : (D.obj j0).Opens) : Set (D.obj j0)) := by
    rw [Scheme.Hom.preimage_inf]
    exact QuasiSeparatedSpace.inter_isCompact _ _ (e.hom ⁻¹ᵁ U).isOpen hU' (e.hom ⁻¹ᵁ V).isOpen hV'
  have rU := hR h q D c hc ha hcs hqs hu j0 X e U hU' pU
  have rV := hR h q D c hc ha hcs hqs hu j0 X e V hV' pV
  have rW := hR h q D c hc ha hcs hqs hu j0 X e (U ⊓ V) hW' pW
  let k := IsCofiltered.min j j0
  have hy' : pull _ (sch.map (c.π.app k)) _ _ (pull _ (sch.map (D.map (IsCofiltered.minToLeft j j0))) _ _ y) = 0 := by
    rw [← pull_comp, ← Functor.map_comp, c.w]; exact hy
  obtain ⟨l, g, hg⟩ := hC h hmv q D c hc j0 X e U V hUV rU rV rW n i k (IsCofiltered.minToRight j j0) _ hy'
  refine ⟨l, g ≫ IsCofiltered.minToLeft j j0, ?_⟩
  rw [D.map_comp, Functor.map_comp, pull_comp]; exact hg

end LateralTheory.E.StepKPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LEtaleLiftPf
section
noncomputable section

namespace LateralTheory.E.LEtaleLiftPf

def LChart : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (A' : Type) [CommRing A']
  [Algebra A A'] [Algebra.Etale A A'] (φ : A' →ₐ[A] A ⧸ I),
  ∃ g : A', IsUnit (φ g) ∧ Algebra.IsStandardEtale A (Localization.Away g)

theorem LEtaleLift_of (hC : LChart) : LateralTheory.E.LFactorPf.LEtaleLift := by
  intro A _ I _ A' _ _ _ φ
  obtain ⟨g, hg, hS⟩ := hC A I A' φ
  let φ' : Localization.Away g →ₐ[A] A ⧸ I := IsLocalization.Away.liftAlgHom g hg
  obtain ⟨ψ, hψ⟩ := GlobalTheory.exists_algHom_lift_of_isStandardEtale I (Ideal.Quotient.mkₐ A I)
    (Ideal.Quotient.mkₐ_surjective A I) (fun b => (Ideal.Quotient.eq_zero_iff_mem).symm) φ'
  refine ⟨ψ.comp (IsScalarTower.toAlgHom A A' _), AlgHom.ext fun a => ?_⟩
  exact congr($hψ (algebraMap A' _ a)).trans (show φ' (algebraMap A' _ a) = φ a by simp [φ'])

end LateralTheory.E.LEtaleLiftPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LZHensFinitePf
section
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.E.LZHensFinitePf

def HensIdemLift : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
  (B : Type) [CommRing B] [Algebra A B] [Module.Finite A B]
  (e : B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)), IsIdempotentElem e →
  ∃ f : B, IsIdempotentElem f ∧ Ideal.Quotient.mk _ f = e

theorem hensIdemLift : HensIdemLift := by
  intro A _ _ _ B _ _ _ e he
  exact GlobalTheory.exists_idempotent_lift_of_henselian A (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective he

theorem idem_triv_of_preconnected (R : Type) [CommRing R] [PreconnectedSpace (PrimeSpectrum R)]
    (e : R) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hc : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
  rcases isClopen_iff.mp hc with h | h
  · left
    apply he.eq_zero_of_isNilpotent
    rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
    exact SetLike.coe_injective h
  · right
    have hz : PrimeSpectrum.zeroLocus ({e} : Set R) = ∅ := by
      rw [← compl_compl (PrimeSpectrum.zeroLocus ({e} : Set R)), ← PrimeSpectrum.basicOpen_eq_zeroLocus_compl, h,
        Set.compl_univ]
    have h1 : IsNilpotent (1 - e) := by
      rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
      apply SetLike.coe_injective
      rw [PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem _ he.one_sub, sub_sub_cancel, hz]
      rfl
    exact (sub_eq_zero.mp (he.one_sub.eq_zero_of_isNilpotent h1)).symm

theorem subsingleton_of_idem (R : Type) [CommRing R] [IsArtinianRing R]
    (h : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) : Subsingleton (PrimeSpectrum R) := by
  have hp : PreconnectedSpace (PrimeSpectrum R) := by
    rw [preconnectedSpace_iff_clopen]
    intro s hs
    obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
    rcases h e he with rfl | rfl
    · left; simp
    · right; simp
  exact ⟨fun x y => hp.constant (f := id) continuous_id⟩

theorem LZHensFinite_of_lift (hL : HensIdemLift) : LateralTheory.E.LZProperCut.LZHensFinite := by
  intro A _ _ _ B _ _ _ hB
  have : ConnectedSpace (PrimeSpectrum B) := hB
  have : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  set I := (IsLocalRing.maximalIdeal A).map (algebraMap A B) with hI
  have hle : ∀ M : Ideal B, M.IsMaximal → I ≤ M := by
    intro M hM
    rw [hI, Ideal.map_le_iff_le_comap]
    have : (M.comap (algebraMap A B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    exact (IsLocalRing.eq_maximalIdeal this).ge
  have htriv : ∀ e : B ⧸ I, IsIdempotentElem e → e = 0 ∨ e = 1 := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := hL A B e he
    rcases idem_triv_of_preconnected B f hf with rfl | rfl
    · left; simp
    · right; simp
  have : Module.Finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ I) :=
    Module.Finite.of_restrictScalars_finite A _ _
  let _ : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  have : IsArtinianRing (B ⧸ I) := IsArtinianRing.of_finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ I)
  have hsub := subsingleton_of_idem (B ⧸ I) htriv
  have key : ∀ P : Ideal B, P.IsMaximal →
      P = (P.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) ∧ (P.map (Ideal.Quotient.mk I)).IsPrime := by
    intro P hP
    refine ⟨(Ideal.comap_map_mk (hle P hP)).symm, ?_⟩
    exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle P hP)
  apply IsLocalRing.of_unique_max_ideal
  obtain ⟨M, hM⟩ := Ideal.exists_maximal B
  refine ⟨M, hM, fun N hN => ?_⟩
  obtain ⟨hN1, hN2⟩ := key N hN
  obtain ⟨hM1, hM2⟩ := key M hM
  have : (⟨_, hN2⟩ : PrimeSpectrum (B ⧸ I)) = ⟨_, hM2⟩ := Subsingleton.elim _ _
  exact hN1.trans ((congrArg (fun P : PrimeSpectrum (B ⧸ I) => P.asIdeal.comap (Ideal.Quotient.mk I)) this).trans hM1.symm)

end LateralTheory.E.LZHensFinitePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafAffCoverVanishPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.E8

def LeafArtinAffine : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ), DimLE p d →
  ∀ V : X.Opens, IsAffineOpen V → ∀ (n i : ℤ), (d : ℤ) < n → Subsingleton (H (ZMod q) (sch.obj V) (tw q i) n)

def LeafMVVanish : Prop := Base → ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (A B : X.Opens) (F : Shv R) (c : ℤ),
  (∀ n : ℤ, c < n → Subsingleton (H R (sch.obj A) F n)) → (∀ n : ℤ, c < n → Subsingleton (H R (sch.obj B) F n)) →
  (∀ n : ℤ, c - 1 < n → Subsingleton (H R (sch.obj ((A ⊓ B : X.Opens) : Scheme.{0})) F n)) →
  ∀ n : ℤ, c < n → Subsingleton (H R (sch.obj ((A ⊔ B : X.Opens) : Scheme.{0})) F n)

def LeafEmptyVanish : Prop := ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (F : Shv R) (n : ℤ),
  Subsingleton (H R (sch.obj (⊥ : X.Opens)) F n)

end LateralTheory.E.E8

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCochainVanishPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafCochainVanishPf

variable {R : Type} [CommRing R]

theorem free_ext_zero (P : PSh) (G : Shv R) (φ : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.hom.app (op U)).hom (freeGen R P U x) = 0) : φ = 0 := by
  have h0 : (0 : (free R).obj P ⟶ G).hom = 0 := rfl
  refine Sheaf.hom_ext ?_
  rw [h0]
  refine sheafify_hom_ext _ _ _ G.property ?_
  ext U : 2
  refine ModuleCat.free_hom_ext (fun x => ?_)
  exact (h U.unop x.down).trans (by erw [Limits.comp_zero]; rfl)

theorem chains_isZero (E : Spc) (p : ℤ) (hp : 0 < p) : Limits.IsZero (((chains R).obj E).X p) := by
  refine HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => ?_)
  have : ComplexShape.embeddingDownNat.f i = -(i : ℤ) := rfl
  omega

theorem cochain_zero_of (E : Spc) {U V : Spc} (f : U ⟶ E) (g : V ⟶ E) (hc : Cover2 R f g) (K : Cx R) (k : ℤ)
    (γ : Cochain ((chains R).obj E) K k)
    (hU : ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx U N Y), ev γ N w h Y ((f.app _).app _ y) = 0)
    (hV : ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx V N Y), ev γ N w h Y ((g.app _).app _ y) = 0) :
    γ = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [Cochain.zero_v]
  by_cases hp : 0 < p
  · exact (chains_isZero (R := R) E p hp).eq_of_src _ _
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨(-p).toNat, by omega⟩
  have hφ : (chainsXIso R E N).inv ≫ γ.v (-(N : ℤ)) q hpq = 0 := by
    have := hc.2.2 (op (SimplexCategory.mk N))
    rw [← cancel_epi (biprod.desc ((free R).map (f.app (op (SimplexCategory.mk N))))
      ((free R).map (g.app (op (SimplexCategory.mk N))))), Limits.comp_zero]
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, Limits.comp_zero]
      refine free_ext_zero _ _ _ (fun Y y => ?_)
      have e := hU N q hpq Y y
      unfold ev at e
      rw [← LateralTheory.E.FirstChernNaturality.freeGen_nat (R := R)] at e
      exact e
    · rw [biprod.inr_desc_assoc, Limits.comp_zero]
      refine free_ext_zero _ _ _ (fun Y y => ?_)
      have e := hV N q hpq Y y
      unfold ev at e
      rw [← LateralTheory.E.FirstChernNaturality.freeGen_nat (R := R)] at e
      exact e
  rw [← Iso.hom_inv_id_assoc (chainsXIso R E N) (γ.v _ _ hpq), hφ, Limits.comp_zero]

end LateralTheory.E.LeafCochainVanishPf

theorem LateralTheory.E.LeafA6suppPf.LeafCochainVanish_of : LateralTheory.E.LeafA6suppPf.LeafCochainVanish := by
  intro R _ U V E f g hc K k γ hU hV
  exact LateralTheory.E.LeafCochainVanishPf.cochain_zero_of E f g hc K k γ hU hV
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCoordsPfNakH
section
noncomputable section

namespace LateralTheory.E.LeafCoordsPf.NakH

open scoped Pointwise
open Polynomial

theorem eval_notMem {B : Type} [CommRing B] {P : Ideal B} (hP : P.IsPrime) (p : B[X]) (hm : p.Monic)
    (hc : ∀ k, p.coeff k ∈ P ^ (p.natDegree - k)) {h : B} (hh : h ∉ P) : p.eval h ∉ P := by
  intro H
  have hsum : ∑ i ∈ Finset.range p.natDegree, p.coeff i * h ^ i ∈ P := by
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ ?_
    have hi' : p.natDegree - i ≠ 0 := by
      have := Finset.mem_range.mp hi
      omega
    exact Ideal.pow_le_self hi' (hc i)
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, one_mul] at H
  have : h ^ p.natDegree ∈ P := by
    have := P.sub_mem H hsum
    simpa using this
  exact hh (hP.mem_of_pow_mem _ this)

theorem nakH : LeafNakH := by
  intro B M _ _ _ P hP N N' hfg h hh hle
  have : Module.Finite B N' := Module.Finite.iff_fg.mpr hfg
  let Q := N' ⧸ N.comap N'.subtype
  let f : Module.End B Q := algebraMap B (Module.End B Q) h
  have hr : LinearMap.range f ≤ P • ⊤ := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨⟨n, hn⟩, rfl⟩ := Submodule.mkQ_surjective _ q
    have hhn : h • n ∈ N ⊔ P • N' := hle (Submodule.smul_mem_pointwise_smul n h N' hn)
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hhn
    have hb' : b ∈ (P • (⊤ : Submodule B N')).map N'.subtype := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top]
      exact hb
    obtain ⟨b', hb'1, hb'2⟩ := hb'
    have heq : f ((N.comap N'.subtype).mkQ ⟨n, hn⟩) = (N.comap N'.subtype).mkQ b' := by
      simp only [f, Module.algebraMap_end_apply, Submodule.mkQ_apply]
      show (Submodule.Quotient.mk (h • (⟨n, hn⟩ : N')) : N' ⧸ N.comap N'.subtype) = Submodule.Quotient.mk b'
      rw [Submodule.Quotient.eq, Submodule.mem_comap]
      simp only [Submodule.subtype_apply, SetLike.val_smul, Submodule.coe_sub, hb'2]
      convert ha using 1
      rw [← hab]
      have hb3 : (b' : M) = b := hb'2
      rw [hb3]
      abel
    rw [heq]
    have : (P • (⊤ : Submodule B N')).map (N.comap N'.subtype).mkQ ≤ P • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact this ⟨b', hb'1, rfl⟩
  obtain ⟨p, hm, -, hc, hp⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero B f P hr
  refine ⟨p.eval h, eval_notMem hP p hm hc hh, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have := LinearMap.congr_fun hp (Submodule.Quotient.mk ⟨x, hx⟩)
  rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, Module.algebraMap_end_apply, LinearMap.zero_apply,
    ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
  simpa using this

theorem LeafCoords_of_point (hPt : LeafCoordsPoint) : LateralTheory.E.LeafChartRingPf.LeafCoords :=
  LeafCoords_of hPt nakH

end LateralTheory.E.LeafCoordsPf.NakH
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCov1Of
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafCov1Pf
open LateralTheory.E.t_E6Cut LateralTheory.E.LeafExcRingPf

theorem exists_lift {B W : Type} [CommRing B] [CommRing W] (α : B →+* W) (I : Ideal B)
    (hQ : QIso α I) (p : Ideal B) [hp : p.IsPrime] (hI : I ≤ p) :
    ∃ q : Ideal W, q.IsPrime ∧ q.comap α = p := by
  let e := RingEquiv.ofBijective _ hQ
  let f : W →+* B ⧸ I := (e.symm : W ⧸ I.map α →+* B ⧸ I).comp (Ideal.Quotient.mk (I.map α))
  have hf : f.comp α = Ideal.Quotient.mk I := by
    ext b
    simp only [f, RingHom.comp_apply, RingHom.coe_coe]
    rw [RingEquiv.symm_apply_eq]
    rfl
  have hpb : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hI)
  refine ⟨(p.map (Ideal.Quotient.mk I)).comap f, Ideal.comap_isPrime _ _, ?_⟩
  rw [Ideal.comap_comap, hf, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact sup_eq_left.2 hI

theorem LeafCov1_of (_hE : LeafExc) : LeafCov1 := by
  intro B W _ _ α I hα hQ U hU T y
  have : Etale (Spec.map (CommRingCat.ofHom α)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 hα
  let A : Bool → Scheme.{0} := fun b => Bool.rec (pullback y (Spec.map (CommRingCat.ofHom α)))
    ((y ⁻¹ᵁ U : T.Opens) : Scheme.{0}) b
  let m : (b : Bool) → A b ⟶ T := fun b => Bool.rec (motive := fun b => A b ⟶ T)
    (pullback.fst y (Spec.map (CommRingCat.ofHom α))) (y ⁻¹ᵁ U).ι b
  have hcov : ∀ t, ∃ (b : Bool) (z : A b), (m b).base z = t := by
    intro t
    by_cases ht : y t ∈ U
    · exact ⟨true, ⟨t, ht⟩, rfl⟩
    · rw [hU] at ht
      push Not at ht
      obtain ⟨q, hq, hqp⟩ := exists_lift α I hQ _ ht
      let w : Spec (CommRingCat.of W) := (⟨q, hq⟩ : PrimeSpectrum W)
      have hw : Spec.map (CommRingCat.ofHom α) w = y t := PrimeSpectrum.ext hqp
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback t w hw.symm
      exact ⟨false, z, hz⟩
  have hprop : ∀ b, Etale (m b) := by
    intro b; cases b <;> dsimp [m] <;> infer_instance
  let 𝒰 : T.Cover (Scheme.precoverage @Etale) := Scheme.Cover.mkOfCovers Bool A m hcov hprop
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f, Scheme.Cover.mem_grothendieckTopology 𝒰, ?_⟩
  intro V k hk
  obtain ⟨b, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hk
  change Bool at b
  cases b
  · right
    refine ⟨h ≫ pullback.snd _ _, ?_⟩
    show (h ≫ pullback.snd y _) ≫ _ = h ≫ pullback.fst y (Spec.map (CommRingCat.ofHom α)) ≫ y
    exact (Category.assoc _ _ _).trans (congrArg (h ≫ ·) pullback.condition).symm
  · left
    refine ⟨h ≫ (y ∣_ U), ?_⟩
    show (h ≫ (y ∣_ U)) ≫ U.ι = h ≫ (y ⁻¹ᵁ U).ι ≫ y
    exact (Category.assoc _ _ _).trans (congrArg (h ≫ ·) (morphismRestrict_ι y U))

end LateralTheory.E.LeafCov1Pf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafCurveVCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafCurveVCut

def LeafFibreField : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p],
  0 < topologicalKrullDim X → ∃ (F : Type) (_ : Field F) (_ : Algebra k F) (K : Type) (_ : Field K) (_ : Algebra F K)
    (n : ℕ) (s : Finset F) (t : K) (η : Sp K ⟶ X), (n : WithBot ℕ∞) < topologicalKrullDim X ∧ s.card ≤ n ∧
    Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F ∧ Transcendental F t ∧
    FiniteDimensional (IntermediateField.adjoin F {t}) K ∧
    η ≫ p = Spec.map (CommRingCat.ofHom ((algebraMap F K).comp (algebraMap k F))) ∧ genericPoint X ∈ Set.range η

def LeafTrdegDim : Prop := ∀ (k F Ω : Type) [Field k] [Field F] [Field Ω] [Algebra k F] [Algebra F Ω] [Algebra k Ω]
  [IsScalarTower k F Ω] [Algebra.IsAlgebraic F Ω] (n : ℕ) (s : Finset F), s.card ≤ n →
    Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F →
    ∀ R : Subalgebra k Ω, R.FG → ringKrullDim R ≤ n

def LeafBaseChangeField : Prop := ∀ (F Ω K : Type) [Field F] [Field Ω] [Field K] [Algebra F Ω] [Algebra F K] (t : K),
  Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) K →
    ∃ (L : Type) (_ : Field L) (_ : Algebra Ω L) (u : L) (φ : K →+* L), Transcendental Ω u ∧
      FiniteDimensional (IntermediateField.adjoin Ω {u}) L ∧ φ.comp (algebraMap F K) = (algebraMap Ω L).comp (algebraMap F Ω)

def LeafModelCurve : Prop := ∀ (Ω L : Type) [Field Ω] [IsAlgClosed Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    ∃ (C0 : Scheme.{0}) (c0 : C0 ⟶ Sp Ω) (x : C0) (ψ : Spec (C0.presheaf.stalk x) ⟶ Sp L), IsCurve c0 ∧
      IsGenericPoint x (⊤ : Set C0) ∧ ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω L)) = C0.fromSpecStalk x ≫ c0

def LeafExtend : Prop := ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] {X C0 : Scheme.{0}} (p : X ⟶ Sp k)
  [IsProper p] (c0 : C0 ⟶ Sp Ω) (x : C0), IsCurve c0 → IsGenericPoint x (⊤ : Set C0) →
    ∀ ψ : Spec (C0.presheaf.stalk x) ⟶ X,
      ψ ≫ p = C0.fromSpecStalk x ≫ c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
      ∃ e : C0 ⟶ X, C0.fromSpecStalk x ≫ e = ψ ∧ e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))

theorem goal_of (hA : LeafFibreField) (hT : LeafTrdegDim) (hB1 : LeafBaseChangeField) (hB2 : LeafModelCurve)
    (hC : LeafExtend) : LateralTheory.E.LeafGeoVCut.LeafCurveV := by
  intro k _ _ X _ p _ hd
  obtain ⟨F, _, _, K, _, _, n, s, t, η, hn, hs, halg, ht, hfin, hη, hgen⟩ := hA k p hd
  obtain ⟨L, _, _, u, φ, hu, hufin, hφ⟩ := hB1 F (AlgebraicClosure F) K t ht hfin
  obtain ⟨C0, c0, x, ψ, hc0, hx, hψ⟩ := hB2 (AlgebraicClosure F) L u hu hufin
  have hring : CommRingCat.ofHom ((algebraMap F K).comp (algebraMap k F)) ≫ CommRingCat.ofHom φ =
      CommRingCat.ofHom (algebraMap k (AlgebraicClosure F)) ≫ CommRingCat.ofHom (algebraMap (AlgebraicClosure F) L) := by
    ext a
    have := congrArg (fun f => f (algebraMap k F a)) hφ
    simp only [RingHom.coe_comp, Function.comp_apply] at this
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply, this,
      IsScalarTower.algebraMap_apply k F (AlgebraicClosure F)]
  have hcompat : (ψ ≫ Spec.map (CommRingCat.ofHom φ) ≫ η) ≫ p =
      C0.fromSpecStalk x ≫ c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure F))) := by
    rw [Category.assoc, Category.assoc, hη, ← Spec.map_comp, hring, Spec.map_comp, ← Category.assoc, hψ,
      Category.assoc]
  obtain ⟨e, he1, he2⟩ := hC k (AlgebraicClosure F) p c0 x hc0 hx _ hcompat
  refine ⟨AlgebraicClosure F, inferInstance, inferInstance, inferInstance, C0, c0, e, hc0, he2, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hgen
    let w : Spec (C0.presheaf.stalk x) := IsLocalRing.closedPoint (C0.presheaf.stalk x)
    refine ⟨C0.fromSpecStalk x w, ?_⟩
    rw [← Scheme.Hom.comp_apply, he1, ← hz]
    simp only [Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  · intro R hR
    exact lt_of_le_of_lt (hT k F (AlgebraicClosure F) n s hs halg R hR) hn

end LateralTheory.E.LeafCurveVCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafHAWBounds
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafHtpyAWPf

abbrev HFam (R : Type) [CommRing R] (I J K : Cx R) : Type 1 :=
  ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w + 1 →
    Sec (I.X s) U →ₗ[ULift.{1} R] Sec (J.X t) U →ₗ[ULift.{1} R] Sec (K.X w) U

def IsHAW {R : Type} [CommRing R] {I J K : Cx R} (h : HFam R I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (η : Cochain ((chains R).obj E) K (k - 1)) :
    Prop :=
  ∀ (N : ℕ) (w : ℤ) (hw : -(N : ℤ) + (k - 1) = w) (U : Scheme.{0}) (x : Sx E N U), ev η N w hw U x =
    ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow • h U (-((p : ℕ) : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w (by omega)
      (ev α p _ rfl U (x.sub 0 p (by omega))) (ev β (N - p) _ rfl U (x.sub p (N - p) (by omega)))

def LeafHAWExists : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (h : HFam R I J K),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (hw : s + t = w + 1) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.res g (h U s t w hw a b) = h V s t w hw (Sec.res g a) (Sec.res g b)) →
  ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m),
    ∃ η : Cochain ((chains R).obj E) K (k - 1), IsHAW h hk α β η

def LeafHAWBounds : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ μ' : Pair I J K) (h : HFam R I J K),
  (∀ (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    μ.mul U s t w hw a b - μ'.mul U s t w hw a b =
      Sec.map (K.d (w - 1) w) (h U s t (w - 1) (by omega) a b) +
        h U (s + 1) t w (by omega) (Sec.map (I.d s (s + 1)) a) b +
        s.negOnePow • h U s (t + 1) w (by omega) a (Sec.map (J.d t (t + 1)) b)) →
  ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ γ' : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ'.IsAW hk α.1 β.1 γ'.1 →
    ∀ η : Cochain ((chains R).obj E) K (k - 1), IsHAW h hk α.1 β.1 η → δ (k - 1) k η = γ.1 - γ'.1

end LateralTheory.E.LeafHtpyAWPf
end
end

