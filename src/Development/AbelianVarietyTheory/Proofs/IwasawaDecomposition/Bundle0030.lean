import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRelativeDimOfTrdeg
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.RelDimFibCrit

theorem trdeg_residueField_of_minimal_in_fibre {R B : Type} [CommRing R] [CommRing B] (φ : R →+* B) (r : ℕ)
    (hφ : φ.IsStandardSmoothOfRelativeDimension r) (P : Ideal B) [P.IsPrime]
    (hP : ∀ P' : Ideal B, P'.IsPrime → P' ≤ P → P'.comap φ = P.comap φ → P' = P) :
    @Algebra.trdeg (P.comap φ).ResidueField P.ResidueField _ _
      (Ideal.ResidueField.map (P.comap φ) P φ rfl).toAlgebra = r := by
  obtain ⟨g, rfl, hg⟩ := hφ.exists_etale_mvPolynomial
  have hQ : ∀ Q' : Ideal (MvPolynomial (Fin r) R), Q'.IsPrime → Q' ≤ P.comap g →
      Q'.comap (MvPolynomial.C : R →+* _) = (P.comap g).comap MvPolynomial.C → Q' = P.comap g := by
    intro Q' hQ' hle hc
    letI := g.toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin r) R) B := hg
    haveI : Module.Flat (MvPolynomial (Fin r) R) B := inferInstance
    haveI : P.LiesOver (P.comap g) := ⟨rfl⟩
    obtain ⟨P', hP'le, hP'prime, hP'over⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := Q') P hle
    have hP'Q : P'.comap g = Q' := hP'over.over.symm
    have := hP P' hP'prime hP'le (by rw [← Ideal.comap_comap, hP'Q, hc, Ideal.comap_comap])
    rw [← hP'Q, this]
  have h1 := GlobalTheory.FibreMinimalPrime.trdeg_residueField_eq r (P.comap g) hQ
  have h2 := GlobalTheory.residueField_isAlgebraic_of_etale g hg P
  letI i12 := (Ideal.ResidueField.map ((P.comap g).comap MvPolynomial.C) (P.comap g)
    (MvPolynomial.C : R →+* _) rfl).toAlgebra
  letI i23 := (Ideal.ResidueField.map (P.comap g) P g rfl).toAlgebra
  letI i13 := (Ideal.ResidueField.map ((P.comap g).comap (MvPolynomial.C : R →+* _)) P
    (g.comp MvPolynomial.C) rfl).toAlgebra
  haveI : IsScalarTower ((P.comap g).comap (MvPolynomial.C : R →+* _)).ResidueField
      (P.comap g).ResidueField P.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext x
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    rw [Ideal.ResidueField.map_algebraMap _ (P.comap g) (MvPolynomial.C : R →+* _) rfl x,
      Ideal.ResidueField.map_algebraMap (P.comap g) P g rfl]
    exact Ideal.ResidueField.map_algebraMap ((P.comap g).comap (MvPolynomial.C : R →+* _)) P
      (g.comp MvPolynomial.C) rfl x
  have := trdeg_add_eq ((P.comap g).comap (MvPolynomial.C : R →+* _)).ResidueField
    (P.comap g).ResidueField (A := P.ResidueField)
  rw [h1, trdeg_eq_zero, add_zero] at this
  exact this.symm

end GlobalTheory.RelDimFibCrit

namespace GlobalTheory.RelDimFibCrit

theorem exists_minimal_in_fibre {R B : Type} [CommRing R] [CommRing B] (φ : R →+* B)
    (P : Ideal B) (hP : P.IsPrime) :
    ∃ P₀ : Ideal B, P₀.IsPrime ∧ P₀ ≤ P ∧ P₀.comap φ = P.comap φ ∧
      ∀ P' : Ideal B, P'.IsPrime → P' ≤ P₀ → P'.comap φ = P.comap φ → P' = P₀ := by
  let s : Set (Ideal B)ᵒᵈ := {Q | (OrderDual.ofDual Q).IsPrime ∧ OrderDual.ofDual Q ≤ P ∧
    (OrderDual.ofDual Q).comap φ = P.comap φ}
  obtain ⟨m, -, hm⟩ := zorn_le_nonempty₀ s (fun c hcs hc y hy => by
    have hyc : OrderDual.ofDual y ∈ OrderDual.ofDual '' c := Set.mem_image_of_mem _ hy
    refine ⟨OrderDual.toDual (sInf (OrderDual.ofDual '' c)), ⟨?_, ?_, ?_⟩, fun z hz => ?_⟩
    · refine Ideal.sInf_isPrime_of_isChain (s := OrderDual.ofDual '' c) ⟨_, hyc⟩ ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
        rcases hc ha hb (fun h => hab (congrArg _ h)) with h | h
        · exact Or.inr h
        · exact Or.inl h
      · rintro _ ⟨a, ha, rfl⟩
        exact (hcs ha).1
    · exact (sInf_le hyc).trans (hcs hy).2.1
    · apply le_antisymm
      · exact (Ideal.comap_mono (sInf_le hyc)).trans (hcs hy).2.2.le
      · intro a ha
        change φ a ∈ sInf (OrderDual.ofDual '' c)
        rw [Submodule.mem_sInf]
        rintro _ ⟨z, hz, rfl⟩
        rw [← Ideal.mem_comap, (hcs hz).2.2]
        exact ha
    · exact (sInf_le (Set.mem_image_of_mem OrderDual.ofDual hz) :
        sInf (OrderDual.ofDual '' c) ≤ OrderDual.ofDual z)) (OrderDual.toDual P) ⟨hP, le_rfl, rfl⟩
  refine ⟨OrderDual.ofDual m, hm.prop.1, hm.prop.2.1, hm.prop.2.2, fun P' h1 h2 h3 => ?_⟩
  have := hm.eq_of_ge (y := OrderDual.toDual P') ⟨h1, h2.trans hm.prop.2.1, h3⟩ h2
  exact congrArg OrderDual.ofDual this

theorem trdeg_residueFieldMap_openImmersion_square :
    ∀ {X Y X' Y' : Scheme.{0}} (g : X' ⟶ Y') (f : X ⟶ Y) (jX : X' ⟶ X) (jY : Y' ⟶ Y)
    [IsOpenImmersion jX] [IsOpenImmersion jY], g ≫ jY = jX ≫ f → ∀ x : X',
    @Algebra.trdeg (Y.residueField (f (jX x))) (X.residueField (jX x)) _ _
      (f.residueFieldMap (jX x)).hom.toAlgebra =
    @Algebra.trdeg (Y'.residueField (g x)) (X'.residueField x) _ _
      (g.residueFieldMap x).hom.toAlgebra := by
  intro X Y X' Y' g f jX jY _ _ e x
  have hpt : jY (g x) = f (jX x) := by
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  have hc := Scheme.Hom.residueFieldMap_congr e x
  rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp] at hc
  let C : Y.residueField (jY (g x)) ≅ Y.residueField (f (jX x)) := Y.residueFieldCongr hpt
  have hc' : jY.residueFieldMap (g x) ≫ g.residueFieldMap x =
      C.hom ≫ f.residueFieldMap (jX x) ≫ jX.residueFieldMap x := hc
  let eU : Y.residueField (f (jX x)) ≅ Y'.residueField (g x) :=
    C.symm ≪≫ asIso (jY.residueFieldMap (g x))
  let eV : X.residueField (jX x) ≅ X'.residueField x := asIso (jX.residueFieldMap x)
  refine GlobalTheory.trdeg_eq_of_ringEquiv_square _ _ eU.commRingCatIsoToRingEquiv
    eV.commRingCatIsoToRingEquiv ?_
  have key : C.inv ≫ jY.residueFieldMap (g x) ≫ g.residueFieldMap x =
      f.residueFieldMap (jX x) ≫ jX.residueFieldMap x := by
    rw [hc']; simp
  have key2 := congrArg CommRingCat.Hom.hom key
  simp only [CommRingCat.hom_comp] at key2
  ext y
  have key3 := congrArg (fun φ => φ y) key2
  simpa [eU, eV] using key3

open AlgebraicGeometry CategoryTheory Limits in
private lemma specMap_residueFieldMap_conj_eq_ofHom_map {R S : CommRingCat.{0}} (φ : R ⟶ S)
    (p : PrimeSpectrum S) :
    (Scheme.Spec.residueFieldIso R ((Spec.map φ) p)).inv ≫ (Spec.map φ).residueFieldMap p ≫
      (Scheme.Spec.residueFieldIso S p).hom =
      CommRingCat.ofHom (Ideal.ResidueField.map (p.asIdeal.comap φ.hom) p.asIdeal φ.hom rfl) := by
  haveI : ((Spec.map φ) p).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  have key : CommRingCat.ofHom (algebraMap R ((Spec.map φ) p).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso R ((Spec.map φ) p)).inv ≫ (Spec.map φ).residueFieldMap p ≫
      (Scheme.Spec.residueFieldIso S p).hom =
      CommRingCat.ofHom (algebraMap R ((Spec.map φ) p).asIdeal.ResidueField) ≫
      CommRingCat.ofHom (Ideal.ResidueField.map (p.asIdeal.comap φ.hom) p.asIdeal φ.hom rfl) := by
    rw [reassoc_of% Scheme.Spec.algebraMap_residueFieldIso_inv]
    erw [Scheme.residue_residueFieldMap_assoc (Spec.map φ) p]
    erw [Scheme.Spec.residue_residueFieldIso_hom]
    erw [Scheme.Hom.germ_stalkMap_assoc]
    erw [Spec.germ_stalkMapIso_hom_assoc]
    erw [Scheme.ΓSpecIso_naturality_assoc, Iso.inv_hom_id_assoc]
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    erw [Ideal.ResidueField.map_algebraMap]
    rw [← IsScalarTower.algebraMap_apply]
  ext1
  apply Ideal.ResidueField.ringHom_ext
  exact congr_arg CommRingCat.Hom.hom key

open AlgebraicGeometry CategoryTheory Limits in
private lemma residueFieldCongr_hom_hom_comp {Y : Scheme.{0}} {a b : Y} {Z : CommRingCat.{0}}
    (h : a = b) (h' : b = a) (g : Y.residueField a ⟶ Z) :
    (Y.residueFieldCongr h).hom ≫ (Y.residueFieldCongr h').hom ≫ g = g := by
  subst h
  simp [Scheme.residueFieldCongr_refl]

open AlgebraicGeometry CategoryTheory Limits in
private lemma trdeg_le_of_ringEquiv {K L K' L' : Type} [CommRing K] [CommRing L] [CommRing K']
    [CommRing L'] [Nontrivial K'] [Algebra K L] [Algebra K' L'] (e₁ : K ≃+* K') (e₂ : L ≃+* L')
    (h : (algebraMap K' L').comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap K L)) :
    Algebra.trdeg K L ≤ Algebra.trdeg K' L' :=
  ciSup_le' fun s ↦ (s.2.ringHom_of_comp_eq e₁ e₂ e₁.surjective e₂.injective h).cardinalMk_le_trdeg

open AlgebraicGeometry CategoryTheory Limits in
private lemma trdeg_eq_of_ringEquiv {K L K' L' : Type} [Field K] [CommRing L] [Field K']
    [CommRing L'] [Algebra K L] [Algebra K' L'] (e₁ : K ≃+* K') (e₂ : L ≃+* L')
    (h : (algebraMap K' L').comp e₁.toRingHom = e₂.toRingHom.comp (algebraMap K L)) :
    Algebra.trdeg K L = Algebra.trdeg K' L' := by
  refine le_antisymm (trdeg_le_of_ringEquiv e₁ e₂ h) (trdeg_le_of_ringEquiv e₁.symm e₂.symm ?_)
  ext a
  have := congr($h (e₁.symm a))
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply] at this
  simp [this]

open AlgebraicGeometry CategoryTheory Limits in

theorem _root_.GlobalTheory.RelDimFibCrit.trdeg_affine {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)
    (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (p : PrimeSpectrum Γ(X, V)) :
    @Algebra.trdeg (Y.residueField (f (hV.fromSpec p))) (X.residueField (hV.fromSpec p)) _ _
      (f.residueFieldMap (hV.fromSpec p)).hom.toAlgebra =
    @Algebra.trdeg (p.asIdeal.comap (f.appLE U V e).hom).ResidueField p.asIdeal.ResidueField _ _
      (Ideal.ResidueField.map _ p.asIdeal (f.appLE U V e).hom rfl).toAlgebra := by
  obtain ⟨p, rfl⟩ : ∃ p' : Spec Γ(X, V), p' = p := ⟨p, rfl⟩
  haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime (p : PrimeSpectrum Γ(X, V))
  set φ := f.appLE U V e
  haveI := hU.isOpenImmersion_fromSpec
  haveI := hV.isOpenImmersion_fromSpec
  have h₁ : hU.fromSpec ((Spec.map φ) p) = f (hV.fromSpec p) :=
    congr($(hU.SpecMap_appLE_fromSpec f hV e) p)
  set q : Spec Γ(Y, U) := (Spec.map φ) p
  let eL := (asIso (hV.fromSpec.residueFieldMap p) ≪≫
    Scheme.Spec.residueFieldIso _ p).commRingCatIsoToRingEquiv
  let eK := (Y.residueFieldCongr h₁.symm ≪≫ asIso (hU.fromSpec.residueFieldMap q) ≪≫
    Scheme.Spec.residueFieldIso _ q).commRingCatIsoToRingEquiv
  have hsq : (Y.residueFieldCongr h₁.symm).hom ≫ hU.fromSpec.residueFieldMap q ≫
      (Scheme.Spec.residueFieldIso _ q).hom ≫
        CommRingCat.ofHom (Ideal.ResidueField.map (p.asIdeal.comap φ.hom) p.asIdeal φ.hom rfl) =
      f.residueFieldMap (hV.fromSpec p) ≫ hV.fromSpec.residueFieldMap p ≫
        (Scheme.Spec.residueFieldIso _ p).hom := by
    erw [← specMap_residueFieldMap_conj_eq_ofHom_map]
    rw [Iso.hom_inv_id_assoc, ← Category.assoc (hU.fromSpec.residueFieldMap q),
      ← Scheme.residueFieldMap_comp, ← Category.assoc (f.residueFieldMap _),
      ← Scheme.residueFieldMap_comp,
      Scheme.Hom.residueFieldMap_congr (hU.SpecMap_appLE_fromSpec f hV e)]
    exact (congrArg _ (Category.assoc _ _ _)).trans (residueFieldCongr_hom_hom_comp _ _ _)
  refine @trdeg_eq_of_ringEquiv _ _ _ _ _ _ _ _ (RingHom.toAlgebra _) (RingHom.toAlgebra _) eK eL ?_
  ext a
  exact congr((CommRingCat.Hom.hom $hsq) a)

theorem smoothOfRelativeDimension_of_trdeg : ∀ {X S : Scheme.{0}} (f : X ⟶ S) (n : ℕ), Smooth f →
    (∀ x : X, (∀ x' : X, f x' = f x → x' ⤳ x → x' = x) →
      @Algebra.trdeg (S.residueField (f x)) (X.residueField x) _ _ (f.residueFieldMap x).hom.toAlgebra = n) →
    SmoothOfRelativeDimension n f := by
  intro X S f n hf H
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨r, hr⟩ : ∃ r, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension r := by
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := hs
    letI := (f.appLE U V e).hom.toAlgebra
    exact ⟨_, ⟨_, _, _, ‹_›, P, rfl⟩⟩
  refine ⟨U, hU, V, hV, hx, e, ?_⟩
  obtain ⟨P₀, hP₀, -, hcomap, hmin⟩ :=
    exists_minimal_in_fibre (f.appLE U V e).hom (hV.primeIdealOf ⟨x, hx⟩).asIdeal inferInstance
  let p₀ : PrimeSpectrum Γ(X, V) := ⟨P₀, hP₀⟩
  have key := trdeg_residueField_of_minimal_in_fibre (f.appLE U V e).hom r hr P₀ (fun P' h1 h2 h3 => hmin P' h1 h2 (h3.trans hcomap))
  have h3 := trdeg_affine f U hU V hV e p₀
  have hm : ∀ x' : X, f x' = f (hV.fromSpec p₀) → x' ⤳ hV.fromSpec p₀ → x' = hV.fromSpec p₀ := by
    intro x' hfx hsp
    have hx'V : x' ∈ Set.range hV.fromSpec :=
      hV.range_fromSpec ▸ hsp.mem_open V.isOpen (hV.range_fromSpec ▸ ⟨p₀, rfl⟩)
    obtain ⟨p', rfl⟩ := hx'V
    have hle : p'.asIdeal ≤ P₀ := (PrimeSpectrum.le_iff_specializes p' p₀).2
      (hV.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.1 hsp)
    have h1 : ∀ q : PrimeSpectrum Γ(X, V),
        hU.fromSpec (Spec.map (f.appLE U V e) q) = f (hV.fromSpec q) := fun q => by
      show (Spec.map (f.appLE U V e) ≫ hU.fromSpec) q = (hV.fromSpec ≫ f) q
      rw [IsAffineOpen.SpecMap_appLE_fromSpec]
    have h2 := hU.fromSpec.isOpenEmbedding.injective ((h1 p').trans (hfx.trans (h1 p₀).symm))
    have hc : p'.asIdeal.comap (f.appLE U V e).hom = P₀.comap (f.appLE U V e).hom :=
      congrArg PrimeSpectrum.asIdeal h2
    have := hmin p'.asIdeal p'.isPrime hle (hc.trans hcomap)
    exact congrArg hV.fromSpec (PrimeSpectrum.ext this)
  have hn := H _ hm
  have : (r : Cardinal) = n := key.symm.trans (h3.symm.trans hn)
  obtain rfl : r = n := by exact_mod_cast this
  exact hr

end GlobalTheory.RelDimFibCrit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricBlockTraceInverseEqTwoMul
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.FockDetDer

theorem trace_fromBlocks_diag {m n : Type} [Fintype m] [Fintype n]
    (X : Matrix m m ℂ) (Y : Matrix n n ℂ) :
    (fromBlocks X 0 0 Y).trace = X.trace + Y.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

theorem symmetric_block_trace_inverse_eq_two_mul {P Q : ℕ} (C : Matrix (Fin Q) (Fin P) ℂ) (B : Matrix (Fin P) (Fin Q) ℂ) (c : ℂ)
    (h : IsUnit (1 - c • (C * B)).det) :
    IsUnit (1 - c • ((fromBlocks 0 B Bᵀ 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (fromBlocks 0 Cᵀ C 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))).det ∧
    ((fromBlocks 0 B Bᵀ 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (fromBlocks 0 Cᵀ C 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (1 - c • ((fromBlocks 0 B Bᵀ 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (fromBlocks 0 Cᵀ C 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)))⁻¹).trace =
      2 * ((1 - c • (C * B))⁻¹ * (C * B)).trace := by
  have hTS : (fromBlocks 0 B Bᵀ 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      (fromBlocks 0 Cᵀ C 0 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) =
      fromBlocks (B * C) 0 0 (C * B)ᵀ := by
    rw [fromBlocks_multiply]; simp
  have h1 : (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) - c • fromBlocks (B * C) 0 0 (C * B)ᵀ =
      fromBlocks (1 - c • (B * C)) 0 0 (1 - c • (C * B))ᵀ := by
    rw [← fromBlocks_one]
    ext (i | i) (j | j) <;> simp [Matrix.one_apply, eq_comm]
  have hd : (1 - c • (B * C)).det = (1 - c • (C * B)).det := by
    rw [← Matrix.smul_mul, det_one_sub_mul_comm, Matrix.mul_smul]
  have h' : IsUnit (1 - c • (B * C)).det := hd ▸ h
  rw [hTS, h1]
  refine ⟨?_, ?_⟩
  · rw [det_fromBlocks_zero₂₁, det_transpose]
    exact h'.mul h
  · have hinv : (fromBlocks (1 - c • (B * C)) 0 0 (1 - c • (C * B))ᵀ)⁻¹ =
        fromBlocks (1 - c • (B * C))⁻¹ 0 0 ((1 - c • (C * B))⁻¹)ᵀ := by
      apply Matrix.inv_eq_left_inv
      rw [fromBlocks_multiply, ← transpose_mul, nonsing_inv_mul _ h', mul_nonsing_inv _ h]
      simp
    have hMB : (1 - c • (B * C))⁻¹ * B = B * (1 - c • (C * B))⁻¹ := by
      have e : B * (1 - c • (C * B)) = (1 - c • (B * C)) * B := by
        simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      calc (1 - c • (B * C))⁻¹ * B
          = (1 - c • (B * C))⁻¹ * B * ((1 - c • (C * B)) * (1 - c • (C * B))⁻¹) := by
            rw [mul_nonsing_inv _ h, Matrix.mul_one]
        _ = (1 - c • (B * C))⁻¹ * (B * (1 - c • (C * B))) * (1 - c • (C * B))⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = B * (1 - c • (C * B))⁻¹ := by
            rw [e, ← Matrix.mul_assoc, nonsing_inv_mul _ h', Matrix.one_mul]
    rw [hinv, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [trace_fromBlocks_diag, ← transpose_mul, trace_transpose, two_mul]
    congr 1
    rw [trace_mul_comm (B * C), ← Matrix.mul_assoc, hMB, Matrix.mul_assoc, trace_mul_comm B,
      Matrix.mul_assoc]

theorem hasDerivAt_det_one_sub_sq : ∀ (P Q : ℕ) (A B : Matrix (Fin P) (Fin Q) ℂ) (t : ℝ), IsUnit (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det → let S : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 Aᴴᵀ Aᴴ 0; let T : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 B Bᵀ 0; IsUnit (1 - ((t : ℂ) ^ 2) • (T * S)).det ∧ HasDerivAt (fun s : ℝ => (1 - ((s : ℂ) ^ 2) • (Aᴴ * B)).det) (-((t : ℂ) * (T * S * (1 - ((t : ℂ) ^ 2) • (T * S))⁻¹).trace) * (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det) t := by
  intro P Q A B t h S T
  obtain ⟨h1, h2⟩ := symmetric_block_trace_inverse_eq_two_mul Aᴴ B ((t : ℂ) ^ 2) h
  refine ⟨h1, ?_⟩
  have hsq : HasDerivAt (fun s : ℝ => (s : ℂ) ^ 2) (2 * (t : ℂ)) t := by
    have := (hasDerivAt_pow 2 (t : ℂ)).comp_ofReal
    simpa using this
  have hd := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun s : ℝ => 1 - ((s : ℂ) ^ 2) • (Aᴴ * B))
    (-((2 * (t : ℂ)) • (Aᴴ * B))) t (fun i j => by
      have := (hsq.mul_const ((Aᴴ * B) i j)).const_sub ((1 : Matrix (Fin Q) (Fin Q) ℂ) i j)
      simpa using this)
  refine hd.congr_deriv ?_
  have hne := h.ne_zero
  have hadj : (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).adjugate =
      (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det • (1 - ((t : ℂ) ^ 2) • (Aᴴ * B))⁻¹ := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv', smul_smul, mul_inv_cancel₀ hne, one_smul]
  simp only [S, T]
  rw [h2, hadj, Matrix.smul_mul, Matrix.mul_neg, Matrix.mul_smul, trace_smul, trace_neg, trace_smul]
  simp only [smul_eq_mul]
  ring

end GlobalTheory.FockDetDer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.CompactHowe

variable {ι : Type} {N n : ℕ}

def subst2 (h : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (Fin N × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin N × Fin n) ℂ :=
  aeval fun p => ∑ k, ∑ l, C (h k p.1 * g l p.2) * X (k, l)

def substF (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (ι × Fin N × Fin n) ℂ →ₐ[ℂ] MvPolynomial (ι × Fin N × Fin n) ℂ :=
  aeval fun p => ∑ k, ∑ l, C (h p.1 k p.2.1 * g p.1 l p.2.2) * X (p.1, k, l)

theorem subst2_X (h : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin n) (Fin n) ℂ) (p : Fin N × Fin n) :
    subst2 h g (X p) = ∑ k, ∑ l, C (h k p.1 * g l p.2) * X (k, l) := aeval_X _ _

theorem substF_X (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (p : ι × Fin N × Fin n) :
    substF h g (X p) = ∑ k, ∑ l, C (h p.1 k p.2.1 * g p.1 l p.2.2) * X (p.1, k, l) := aeval_X _ _

theorem totalDegree_aeval_le {κ : Type} (f : κ → MvPolynomial κ ℂ) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (P : MvPolynomial κ ℂ) : (aeval f P).totalDegree ≤ P.totalDegree := by
  first
  | exact @_root_.GlobalTheory.AevalTotalDegreeLinear.main
  | exact _root_.GlobalTheory.AevalTotalDegreeLinear.main
  | (apply _root_.GlobalTheory.AevalTotalDegreeLinear.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AevalTotalDegreeLinear.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AevalTotalDegreeLinear.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AevalTotalDegreeLinear.main ..)

theorem totalDegree_substF_le (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) : (substF h g P).totalDegree ≤ P.totalDegree :=
  totalDegree_aeval_le _ (fun _ => totalDegree_finsetSum_le fun _ _ => totalDegree_finsetSum_le fun _ _ =>
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])) P

theorem subst2_mul (h h' : Matrix (Fin N) (Fin N) ℂ) (g g' : Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (Fin N × Fin n) ℂ) : subst2 h g (subst2 h' g' P) = subst2 (h * h') (g * g') P := by
  have key : (subst2 h g).comp (subst2 h' g') = subst2 (h * h') (g * g') := by
    refine algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, subst2_X, subst2_X]
    simp only [map_sum, map_mul, subst2_X, algHom_C, algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun _ => Finset.univ) (t' := Finset.univ) (s' := fun _ => Finset.univ) (by simp)]
    simp only [← Finset.sum_product', Finset.univ_product_univ]
    refine Fintype.sum_equiv ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun y => (y.2.2.1, y.2.2.2, y.1, y.2.1), fun _ => rfl, fun _ => rfl⟩ _ _ fun x => ?_
    simp only [Equiv.coe_fn_mk]
    ring
  exact congrArg (fun f => f P) key

theorem subst2_one (P : MvPolynomial (Fin N × Fin n) ℂ) : subst2 1 1 P = P := by
  have key : subst2 (1 : Matrix (Fin N) (Fin N) ℂ) (1 : Matrix (Fin n) (Fin n) ℂ) = AlgHom.id ℂ _ := by
    refine algHom_ext fun p => ?_
    rw [subst2_X, Finset.sum_eq_single p.1, Finset.sum_eq_single p.2]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
    · intro k _ hk; simp [Matrix.one_apply_ne hk]
    · simp
  rw [key]; rfl

end GlobalTheory.CompactHowe

end
end

