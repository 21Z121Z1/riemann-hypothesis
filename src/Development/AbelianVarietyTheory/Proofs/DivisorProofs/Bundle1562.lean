import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurePreservingConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteCurveArithModelClosure
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CurveClosure

open TensorProduct

theorem isReduced_pullback_localization : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S] (V : Scheme.{0}) [IsReduced V] (f : V ⟶ Sp R), IsReduced (pullback f (spMap (algebraMap R S))) := by
  intro R S _ _ _ M _ V _ f
  let 𝒰 := Scheme.Pullback.openCoverOfLeft V.affineOpenCover.openCover f (spMap (algebraMap R S))
  have : ∀ i, IsReduced (𝒰.X i) := fun i => by
    have := V.affineOpenCover.map_prop i
    have h0 : IsReduced (Spec (V.affineOpenCover.X i)) :=
      isReduced_of_isOpenImmersion (V.affineOpenCover.f i)
    have h1 := (affine_isReduced_iff _).mp h0
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (V.affineOpenCover.f i ≫ f)
    change IsReduced (pullback (V.affineOpenCover.f i ≫ f) _)
    rw [← hφ]
    letI : Algebra R (V.affineOpenCover.X i) := φ.hom.toAlgebra
    have h2 : IsReduced (V.affineOpenCover.X i ⊗[R] S) :=
      isReduced_localizationPreserves (Algebra.algebraMapSubmonoid (V.affineOpenCover.X i) M) _ h1
    have h3 := (affine_isReduced_iff (.of (V.affineOpenCover.X i ⊗[R] S))).mpr h2
    exact isReduced_of_isOpenImmersion (pullbackSpecIso R (V.affineOpenCover.X i) S).hom
  exact IsReduced.of_openCover _ 𝒰

theorem exists_iso_red_of_range : ∀ (X G : Scheme.{0}) (g : G ⟶ X) [IsClosedImmersion g] [IsReduced G] (Z : Closeds X), Set.range g = (Z : Set X) → ∃ e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ G, e.hom ≫ g = redι Z := by
  intro X G g _ _ Z h
  have hker : Scheme.IdealSheafData.vanishingIdeal Z = g.ker := by
    rw [← InterModel.radical_ker g, ← Scheme.IdealSheafData.vanishingIdeal_support]
    congr 1
    ext1
    rw [Scheme.Hom.support_ker, g.isClosedEmbedding.isClosed_range.closure_eq, h]
  show ∃ e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ G,
    e.hom ≫ g = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  rw [hker]
  refine ⟨(asIso g.toImage).symm, ?_⟩
  rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq]
  exact g.toImage_imageι.symm

theorem le_dim_of_genFibre : ∀ (F : Type) [Field F] [NumberField F] (W G : Scheme.{0}) [IsIntegral W] (q : W ⟶ Sp (𝓞 F)) (g : G ⟶ W) (s : G ⟶ Sp F) (d : ℕ), IsProjOver q → CharZero Γ(W, ⊤) → IsPullback g s q (spMap (algebraMap (𝓞 F) F)) → topologicalKrullDim G = d → (((d + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim W) := by
  intro F _ _ W G _ q g s d hq _ hpb hd
  obtain ⟨N, i, _, hi⟩ := hq
  have := isProper_str (𝓞 F) N
  have : IsProper q := hi ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom (𝓞 F))) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  let t : W ⟶ Sp ℤ := q ≫ spMap (Int.castRingHom (𝓞 F))
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  haveI : IsPreimmersion g := MorphismProperty.of_isPullback hpb.flip inferInstance
  have hgen : ∀ x, t (g x) = genericPoint (Sp ℤ) := by
    intro x
    rw [genericPoint_eq_bot_of_affine]
    have e : g ≫ t = s ≫ spMap ((algebraMap (𝓞 F) F).comp (Int.castRingHom (𝓞 F))) := by
      simp only [t, ← Category.assoc, hpb.w]
      simp [spMap, Spec.map_comp]
    change (g ≫ t) x = _
    rw [e]
    refine PrimeSpectrum.ext ?_
    change Ideal.comap _ (s x).asIdeal = ⊥
    have hp : (show PrimeSpectrum F from s x).asIdeal.IsPrime := (show PrimeSpectrum F from s x).isPrime
    rw [Ideal.eq_bot_of_prime (show PrimeSpectrum F from s x).asIdeal]
    exact Ideal.comap_bot_of_injective _ (RingHom.injective_int _)
  have key := GlobalTheory.Vert.dim_add_dim_le (S := W) (T := Sp ℤ) (W := G) t.isClosedMap g.continuous
    g.isEmbedding.injective hgen
  have hZ : topologicalKrullDim (Sp ℤ) = 1 := by
    change topologicalKrullDim (PrimeSpectrum ℤ) = 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  rw [hd, hZ] at key
  exact_mod_cast key

theorem dim_le_of_genFibre : ∀ (F : Type) [Field F] [NumberField F] (W G : Scheme.{0}) [IsIntegral W] (q : W ⟶ Sp (𝓞 F)) (g : G ⟶ W) (s : G ⟶ Sp F) (d : ℕ), IsProjOver q → CharZero Γ(W, ⊤) → IsPullback g s q (spMap (algebraMap (𝓞 F) F)) → topologicalKrullDim G = d → topologicalKrullDim W ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := by
  intro F _ _ W G _ q g s d hq hc hpb hd
  obtain ⟨N, i, _, hi⟩ := hq
  have := isProper_str (𝓞 F) N
  have : IsProper q := hi ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom (𝓞 F))) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  let t : W ⟶ Sp ℤ := q ≫ spMap (Int.castRingHom (𝓞 F))
  have : Flat t := (flat_int_iff_charZero t).2 hc
  have : LocallyOfFiniteType t := inferInstance
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  obtain ⟨he, hr⟩ := isEmbedding_and_range_eq_of_isPullback q hpb

  have hfib : Set.range g = t ⁻¹' {genericPoint (Sp ℤ)} := by
    rw [hr, genericPoint_eq_bot_of_affine]
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy⟩
      change Spec.map _ (q x) = _
      rw [← hy]
      refine PrimeSpectrum.ext ?_
      change Ideal.comap _ (Ideal.comap _ (show PrimeSpectrum F from y).asIdeal) = ⊥
      have hp : (show PrimeSpectrum F from y).asIdeal.IsPrime := (show PrimeSpectrum F from y).isPrime
      rw [Ideal.eq_bot_of_prime (show PrimeSpectrum F from y).asIdeal, Ideal.comap_comap]
      exact Ideal.comap_bot_of_injective _ (RingHom.injective_int _)
    · intro h
      have h' : Ideal.comap (algebraMap ℤ (𝓞 F)) (show PrimeSpectrum (𝓞 F) from q x).asIdeal = ⊥ :=
        congrArg PrimeSpectrum.asIdeal h
      have h0 : (show PrimeSpectrum (𝓞 F) from q x).asIdeal = ⊥ := Ideal.eq_bot_of_comap_eq_bot h'
      refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F), ?_⟩
      refine PrimeSpectrum.ext ?_
      change Ideal.comap _ ⊥ = (show PrimeSpectrum (𝓞 F) from q x).asIdeal
      rw [h0]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)

  obtain ⟨A, _, _, instA, _, _, j, _, -, -, hA⟩ := exists_affine_chart_trdeg_eq t (genericPoint W)
  obtain rfl : instA = Ring.toIntAlgebra A := Subsingleton.elim _ _
  obtain ⟨d', hd'⟩ := exists_trdeg_eq_natCast ℤ (A := A)
  have hfd := topologicalKrullDim_preimage_genericPoint_eq t (d := d') (hA ▸ hd')
  rw [← hfib, topologicalKrullDim_eq_of_isEmbedding he rfl, hd] at hfd
  have hdd : d' = d := by exact_mod_cast hfd.symm
  subst hdd
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
  obtain ⟨B, _, _, _, _, _, j', _, ⟨b, rfl⟩, -, hB⟩ := exists_affine_chart_trdeg_eq t x
  refine ⟨Set.range j', j'.isOpenEmbedding.isOpen_range, ⟨b, rfl⟩, ?_⟩
  rw [topologicalKrullDim_eq_of_isEmbedding j'.isOpenEmbedding.isEmbedding rfl]
  refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim B).le.trans ?_
  have hdB : Algebra.trdeg ℤ B = d' := hB.trans (hA.symm.trans hd')
  have hZ1 : ringKrullDim ℤ ≤ 1 := by
    exact_mod_cast Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 ℤ)
  refine (IntModel.ringKrullDim_le_add (O := ℤ) ℚ).trans ?_
  rw [ringKrullDim_genericFibre_eq ℤ ℚ hdB]
  refine (add_le_add hZ1 (le_refl ((d' : ℕ) : WithBot ℕ∞))).trans_eq ?_
  push_cast
  exact add_comm _ _

theorem dim_eq_of_genFibre : ∀ (F : Type) [Field F] [NumberField F] (W G : Scheme.{0}) [IsIntegral W] (q : W ⟶ Sp (𝓞 F)) (g : G ⟶ W) (s : G ⟶ Sp F) (d : ℕ), IsProjOver q → CharZero Γ(W, ⊤) → IsPullback g s q (spMap (algebraMap (𝓞 F) F)) → topologicalKrullDim G = d → topologicalKrullDim W = (d + 1 : ℕ) :=
  fun F _ _ W G _ q g s d h₁ h₂ h₃ h₄ =>
    le_antisymm (dim_le_of_genFibre F W G q g s d h₁ h₂ h₃ h₄) (le_dim_of_genFibre F W G q g s d h₁ h₂ h₃ h₄)

theorem exists_closure_arith_surface : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (P : TrueGeo.Model Y) (Z : Closeds Y.X), IsCompleteCurve F Z → ∃ (W : Scheme.{0}) (w : W ⟶ P.X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsClosedImmersion w ∧ IsArithVar (w ≫ P.p) 1 ∧ z ≫ w = redι Z ≫ P.j ∧ IsPullback z (redι Z ≫ Y.str) (w ≫ P.p) (spMap (algebraMap (𝓞 F) F)) := by
  intro F _ _ Y P Z hZ
  let S : Closeds P.X := ⟨closure (P.j '' (Z : Set Y.X)), isClosed_closure⟩
  have hSirr : IsIrreducible (S : Set P.X) := (hZ.isIrreducible.image _ P.j.continuous.continuousOn).closure
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal S).subscheme := isIntegral_red hSirr
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := isIntegral_red hZ.isIrreducible
  set w := redι S with hw
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  haveI : IsPreimmersion P.j := MorphismProperty.of_isPullback P.pb.flip inferInstance
  have hpb1 : IsPullback (pullback.fst w P.j) (pullback.snd w P.j ≫ Y.str) (w ≫ P.p)
      (spMap (algebraMap (𝓞 F) F)) := (IsPullback.of_hasPullback w P.j).paste_vert P.pb
  haveI : IsReduced (pullback (w ≫ P.p) (spMap (algebraMap (𝓞 F) F))) :=
    isReduced_pullback_localization (𝓞 F) F (nonZeroDivisors (𝓞 F)) _ _
  haveI : IsReduced (pullback w P.j) := isReduced_of_isOpenImmersion hpb1.isoPullback.hom
  have hrange : Set.range (pullback.snd w P.j) = (Z : Set Y.X) := by
    rw [Scheme.Pullback.range_snd, hw, range_redι]
    change P.j ⁻¹' closure (P.j '' (Z : Set Y.X)) = _
    rw [← P.j.isEmbedding.isInducing.closure_eq_preimage_closure_image, Z.isClosed.closure_eq]
  obtain ⟨e, he⟩ := exists_iso_red_of_range _ _ (pullback.snd w P.j) Z hrange
  have hzw : (e.hom ≫ pullback.fst w P.j) ≫ w = redι Z ≫ P.j := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  have hpb : IsPullback (e.hom ≫ pullback.fst w P.j) (redι Z ≫ Y.str) (w ≫ P.p)
      (spMap (algebraMap (𝓞 F) F)) := by
    refine IsPullback.of_iso hpb1 e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp [← he]
    · simp
    · simp
  have hcZ : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := by
    let φ : F →+* Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) :=
      (redι Z ≫ Y.str).appTop.hom.comp (Scheme.ΓSpecIso (.of F)).inv.hom
    exact charZero_of_injective_ringHom φ.injective
  have hcW : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal S).subscheme, ⊤) :=
    (e.hom ≫ pullback.fst w P.j).appTop.hom.charZero
  have hproj : IsProjOver (w ≫ P.p) := by
    obtain ⟨N, j, _, hj⟩ := P.ar.isProjOver
    exact ⟨N, w ≫ j, inferInstance, by rw [Category.assoc, hj]⟩
  have hdZ : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = (1 : ℕ) := by
    rw [topologicalKrullDim_red, hZ.dim_eq]; rfl
  have hdim := dim_eq_of_genFibre F _ _ (w ≫ P.p) (e.hom ≫ pullback.fst w P.j) (redι Z ≫ Y.str) 1 hproj hcW hpb hdZ
  exact ⟨_, w, e.hom ≫ pullback.fst w P.j, inferInstance, P.ar.of_isClosedImmersion w hcW hdim, hzw, hpb⟩

end GlobalTheory.CurveClosure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsOffOpenFinite
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.SurfacePoints

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} [IsIntegral X]

theorem genericPoint_mem_of_lt (hX : IsArithVar p 1) {A B C : IrreducibleCloseds X} (h₁ : A < B)
    (h₂ : B < C) : genericPoint X ∈ C := by
  by_contra h
  let T : IrreducibleCloseds X := ⟨univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have h₃ : C < T := lt_of_le_not_ge (subset_univ _) fun e => h (e (mem_univ _))
  have e₁ := Order.height_add_one_le h₁
  have e₂ := Order.height_add_one_le h₂
  have e₃ := Order.height_add_one_le h₃
  have e₄ : ((Order.height T : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) :=
    (Order.height_le_krullDim T).trans hX.dim_eq.le
  have e₅ : (0 : ℕ∞) + 1 + 1 + 1 ≤ 2 :=
    (add_le_add_left ((add_le_add_left ((add_le_add_left zero_le 1).trans e₁) 1).trans e₂) 1).trans
      (e₃.trans (WithBot.coe_le_coe.1 e₄))
  exact absurd e₅ (by decide)

theorem finite_hom (hX : IsArithVar p 1) {x : X} (hx : x ≠ genericPoint X) :
    Finite (X.residueField x ⟶ CommRingCat.of ℂ) := by
  rcases isEmpty_or_nonempty (X.residueField x ⟶ CommRingCat.of ℂ) with h | ⟨⟨f⟩⟩
  · infer_instance
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint x
  have hbij : Function.Bijective (i.residueFieldMap (genericPoint Z)).hom := by
    refine ⟨RingHom.injective _, fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
    obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
    exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩
  let E := RingEquiv.ofBijective _ hbij
  have hc' : CharZero (Z.residueField (genericPoint Z)) :=
    (RingHom.charZero_iff hbij.1).1 f.hom.charZero
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have h₁ : topologicalKrullDim Z ≤ 1 := Order.krullDim_le_one_iff.2 fun B => by
    by_contra h
    obtain ⟨hA, hC⟩ := not_or.1 h
    obtain ⟨A, hA⟩ := not_isMin_iff.1 hA
    obtain ⟨C, hC⟩ := not_isMax_iff.1 hC
    have hm := IrreducibleCloseds.map_strictMono_of_isInducing i.isClosedEmbedding.isInducing
    have hg : genericPoint X ∈ closure (i '' C) := genericPoint_mem_of_lt hX (hm hA) (hm hC)
    have h₂ := (genericPoint_spec Z).image i.continuous
    exact hx ((h₂.specializes (closure_mono (image_mono (subset_univ _)) hg)).antisymm
      (genericPoint_specializes _)).eq
  obtain ⟨d, hd⟩ := hX.exists_dim_eq i
  have h₀ := hX.dim_ne_zero i hcΓ
  obtain rfl : d = 0 + 1 := by
    rw [hd] at h₀ h₁
    norm_cast at h₀ h₁
    omega
  have := SmallSecHeight.numberField (hX.of_isClosedImmersion i hcΓ hd) hc'
  refine Finite.of_injective (fun g => g.hom.comp E.symm.toRingHom) fun g g' e => ?_
  exact CommRingCat.hom_ext ((RingHom.cancel_right E.symm.surjective).1 e)

theorem finite_charZero (hX : IsArithVar p 1) {U : X.Opens} (hU : genericPoint X ∈ U) :
    {x : X | x ∉ U ∧ CharZero (X.residueField x)}.Finite := by
  classical
  have := hX.isNoetherian
  obtain ⟨S, hS, hc, hi, hZ⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  refine (hS.image fun T => if h : IsIrreducible T then h.genericPoint else genericPoint X).subset
    fun x ⟨hx, _⟩ => ?_
  obtain ⟨T, hT, hxT⟩ := mem_sUnion.1 (hZ.le hx)
  refine ⟨T, hT, ?_⟩
  simp only [dif_pos (hi T hT)]
  refine ((hi T hT).isGenericPoint_genericPoint (hc T hT)).eq ?_
  by_contra hne
  let C (w : X) : IrreducibleCloseds X :=
    ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hle : closure {x} ⊆ T := closure_minimal (singleton_subset_iff.2 hxT) (hc T hT)
  have h₂ : C x < ⟨T, hi T hT, hc T hT⟩ := lt_of_le_not_ge hle fun e => hne (hle.antisymm e)
  obtain ⟨z, hz, hz'⟩ := (isClosed_closure (s := {x})).exists_closed_singleton ⟨x, subset_closure rfl⟩
  have h₁ : C z < C x :=
    lt_of_le_not_ge (closure_minimal (singleton_subset_iff.2 hz) isClosed_closure) fun e => by
      obtain rfl : x = z := hz'.closure_subset (e (subset_closure rfl))
      have := hX.finite_residueField hz'
      exact not_finite (X.residueField x)
  exact hZ.ge (mem_sUnion.2 ⟨T, hT, genericPoint_mem_of_lt hX h₁ h₂⟩) hU

theorem finite_compl_ptsIn : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X],
    IsArithVar p 1 → ∀ U : X.Opens, genericPoint X ∈ U → ∀ σ : k →+* ℂ, (ptsIn p σ U)ᶜ.Finite := by
  intro k _ X p _ hX U hU σ
  have hF := finite_charZero hX hU
  have := hF.to_subtype
  have (x : {x : X | x ∉ U ∧ CharZero (X.residueField x)}) :
      Finite (X.residueField x.1 ⟶ CommRingCat.of ℂ) := finite_hom hX fun e => x.2.1 (e ▸ hU)
  refine ((finite_range fun s : Σ x : {x : X | x ∉ U ∧ CharZero (X.residueField x)},
    (X.residueField x.1 ⟶ CommRingCat.of ℂ) => (Scheme.SpecToEquivOfField ℂ X).symm ⟨s.1.1, s.2⟩).preimage
    Subtype.val_injective.injOn).subset fun y hy => ?_
  exact ⟨⟨⟨_, mt mem_ptsIn.2 hy, (Scheme.SpecToEquivOfField ℂ X y.1).2.hom.charZero⟩,
    (Scheme.SpecToEquivOfField ℂ X y.1).2⟩, (Scheme.SpecToEquivOfField ℂ X).symm_apply_apply y.1⟩

end GlobalTheory.SurfacePoints
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstAlongCocompactUniqueStages
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.Cusp (Cocompact constTermOn)
open GlobalTheory.AutomorphicL2Unitary (LeftInv)

namespace GlobalTheory.StdPar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

theorem ratPts_inf_subgroupOf {N P : Subgroup (GAd σ J)} (hNP : N ≤ P) :
    (ratPts σ J ⊓ P).subgroupOf N = (ratPts σ J).subgroupOf N := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, hNP x.2⟩⟩

theorem isConstTermOn_iff_ratPts_inf {N P : Subgroup (GAd σ J)} [LocallyCompactSpace N] (hNP : N ≤ P)
    (hc : Cocompact (ratPts σ J) N) {φ c : GAd σ J → ℂ} (hφ : LeftInv (ratPts σ J ⊓ P) φ) :
    IsConstTermOn σ J N φ c ↔ c = constTermOn (ratPts σ J ⊓ P) N φ := by
  have e := ratPts_inf_subgroupOf (σ := σ) (J := J) hNP
  constructor
  · intro h
    obtain ⟨μ, 𝓕, h1, h2, h3⟩ := exists_mass_one hc
    funext g
    rw [h μ 𝓕 h1 h2 h3 g, GlobalTheory.Cusp.constTermOn_eq_of_measure_eq_one (e ▸ h2) h3 hφ g]
  · rintro rfl μ 𝓕 h1 h2 h3 g
    exact GlobalTheory.Cusp.constTermOn_eq_of_measure_eq_one (e ▸ h2) h3 hφ g

theorem cocompact_ratPts_inf {N P : Subgroup (GAd σ J)} (hNP : N ≤ P) (hc : Cocompact (ratPts σ J) N) :
    Cocompact (ratPts σ J ⊓ P) N := by
  unfold Cocompact
  rw [ratPts_inf_subgroupOf hNP]
  exact hc

section Witt

variable (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
include h hJ hW

theorem locallyCompact_unip (S : Finset (Fin r)) : LocallyCompactSpace (unip σ J X S) :=
  (isClosed_unip S h hJ hW).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem cocompact_unip_std (S : Finset (Fin r)) : Cocompact (ratPts σ J) (unip σ J X S) := by
  by_cases hS0 : S = ∅
  · subst hS0
    refine ⟨{1}, isCompact_singleton, fun u => ⟨u⁻¹, ?_, by simp⟩⟩
    have hu : (u : GAd σ J) = 1 := Subgroup.mem_bot.1 (le_of_eq (unip_empty (σ := σ) (J := J) (X := X)) u.2)
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_inv, hu, inv_one]
    exact one_mem _
  obtain ⟨m, hm, hm'⟩ : ∃ m ∈ S, ∀ k ∈ S, k ≤ m := ⟨S.max' (Finset.nonempty_iff_ne_empty.2 hS0),
    S.max'_mem _, fun k hk => S.le_max' k hk⟩
  rw [GlobalTheory.ConstTrans.unip_eq_unipFlag F E σ h n J hJ r X Y hW S m hm hm']
  exact cocompact_unipFlag hJ (sigma_sigma h) (isIsoCols_of_isWittFrame hW (sigma_sigma h) hJ m.2) _

theorem conj_mem_unip_of_subset {S T : Finset (Fin r)} (hTS : T ⊆ S) {p u : GAd σ J} (hp : p ∈ unip σ J X S)
    (hu : u ∈ unip σ J X T) : p * u * p⁻¹ ∈ unip σ J X T := by
  by_cases hT0 : T = ∅
  · subst hT0
    rw [unip_empty, Subgroup.mem_bot] at hu ⊢
    simp [hu]
  obtain ⟨m, hm, hm'⟩ : ∃ m ∈ T, ∀ k ∈ T, k ≤ m := ⟨T.max' (Finset.nonempty_iff_ne_empty.2 hT0),
    T.max'_mem _, fun k hk => T.le_max' k hk⟩
  have hσ := sigma_sigma h
  have eT := GlobalTheory.ConstTrans.unip_eq_unipFlag F E σ h n J hJ r X Y hW T m hm hm'
  rw [eT] at hu ⊢
  exact conj_mem_unipFlag hJ hσ (isIsoCols_of_isWittFrame hW hσ hJ m.2) _
    (GlobalTheory.ConstTrans.unip_le_parFlag F E σ h n J hJ r X Y hW S T m hTS hm hm' hp) hu

theorem constAlong_cocompact_unique_stages :
    (∀ S : Finset (Fin r), Cocompact (ratPts σ J) (unip σ J X S) ∧
      ∃ (μ : Measure (unip σ J X S)) (𝓕 : Set (unip σ J X S)), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratPts σ J).subgroupOf (unip σ J X S)) 𝓕 μ ∧ μ 𝓕 = 1) ∧
    (∀ S T : Finset (Fin r), T ⊆ S → unip σ J X T ≤ unip σ J X S ∧ levi σ J X Y S ≤ levi σ J X Y T) ∧
    (∀ (S : Finset (Fin r)) (φ c c' : GAd σ J → ℂ), IsConstAlong σ J X S φ c → IsConstAlong σ J X S φ c' → c = c') ∧
    (∀ (S : Finset (Fin r)) (φ : GAd σ J → ℂ), (∀ γ ∈ ratPts σ J, γ ∈ unip σ J X S → ∀ g, φ (γ * g) = φ g) →
      ∃ c, IsConstAlong σ J X S φ c) ∧
    (∀ (S T : Finset (Fin r)) (φ c c' : GAd σ J → ℂ), T ⊆ S → Continuous φ →
      (∀ γ ∈ ratPts σ J, γ ∈ unip σ J X S → ∀ g, φ (γ * g) = φ g) →
      IsConstAlong σ J X T φ c → IsConstAlong σ J X S c c' → IsConstAlong σ J X S φ c') := by
  refine ⟨fun S => ?_, fun S T hTS => ⟨unip_mono_of_subset F E σ h n J hJ r X Y hW S T hTS, ?_⟩,
    fun S φ c c' h1 h2 => ?_, fun S φ hφ => ?_, fun S T φ c c' hTS hφc hφ hc hc' => ?_⟩
  · haveI := locallyCompact_unip h hJ hW S
    exact ⟨cocompact_unip_std h hJ hW S, exists_mass_one (cocompact_unip_std h hJ hW S)⟩
  · intro g hg
    simp only [levi, Subgroup.mem_iInf] at hg ⊢
    exact fun k hk => hg k (hTS hk)
  · haveI := locallyCompact_unip h hJ hW S
    exact IsConstTermOn.unique (cocompact_unip_std h hJ hW S) h1 h2
  · haveI := locallyCompact_unip h hJ hW S
    exact ⟨_, isConstTermOn_constTermOn (N := unip σ J X S) fun γ hγ g => hφ γ hγ.1 hγ.2 g⟩
  · haveI := locallyCompact_unip h hJ hW S
    haveI := locallyCompact_unip h hJ hW T
    have hle : unip σ J X T ≤ unip σ J X S := unip_mono_of_subset F E σ h n J hJ r X Y hW S T hTS
    have cS := cocompact_unip_std h hJ hW S
    have cT := cocompact_unip_std h hJ hW T
    have hfΓ : LeftInv (ratPts σ J ⊓ unip σ J X S) φ := fun γ hγ g => hφ γ hγ.1 hγ.2 g
    have hnorm : ∀ p ∈ unip σ J X S, ∀ u ∈ unip σ J X T, p * u * p⁻¹ ∈ unip σ J X T :=
      fun p hp u hu => conj_mem_unip_of_subset h hJ hW hTS hp hu
    have hc0 : c = constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X T) φ :=
      (isConstTermOn_iff_ratPts_inf hle cT hfΓ).1 hc
    subst hc0
    have hcΓ : LeftInv (ratPts σ J ⊓ unip σ J X S) (constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X T) φ) :=
      fun γ hγ g => GlobalTheory.Cusp.constTermOn_mul_left_of_normalizer hfΓ hγ
        (fun m => ⟨hnorm _ hγ.2 m, fun hm => by simpa [mul_assoc] using hnorm _ (inv_mem hγ.2) _ hm⟩) g
    have st : constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X S) φ =
        constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X S)
          (constTermOn (ratPts σ J ⊓ unip σ J X S) (unip σ J X T) φ) := funext fun x =>
      GlobalTheory.Cusp.Stages.constTermOn_stages (GAd σ J) (ratPts σ J ⊓ unip σ J X S) (unip σ J X S) (unip σ J X T) hle hnorm
        (cocompact_ratPts_inf le_rfl cS) (cocompact_ratPts_inf hle cT) φ hfΓ hφc x
    change IsConstTermOn σ J (unip σ J X S) _ c' at hc'
    change IsConstTermOn σ J (unip σ J X S) φ c'
    rw [isConstTermOn_iff_ratPts_inf le_rfl cS hcΓ] at hc'
    rw [isConstTermOn_iff_ratPts_inf le_rfl cS hfΓ, st]
    exact hc'

end Witt

end GlobalTheory.StdPar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeNonnegOfCurveDegreeNonnegOverZmod
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.CurveDevissage

theorem interNum_one_nonneg {k : Type} [Field k] {V : Scheme.{0}} [Algebra k Γ(V, ⊤)]
    (hp : IsProjOver (strHom k V)) (hd : topologicalKrullDim V ≤ 1) {N : LB V} (hN : N.IsLB)
    (h : ∀ (Z : Scheme.{0}) (i : Z ⟶ V) [IsClosedImmersion i] [IsIntegral Z] [Algebra k Γ(Z, ⊤)],
      (∀ r : k, i.appTop (algebraMap k Γ(V, ⊤) r) = algebraMap k Γ(Z, ⊤) r) →
      topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection k (N.pull i) 1)
    (F : V.Modules) (hF : QCoh.IsFiniteQC F) : 0 ≤ interNum k F ![N] := by
  have := isNoetherian_of_isProjOver hp
  have hL : ∀ i, ((![N] : Fin 1 → LB V) i).IsLB := fun i => by fin_cases i; exact hN
  refine QCoh.devissage V (fun F => 0 ≤ interNum k F ![N])
    (fun F hF => (interNum_eq_zero_of_isZero k hF hL).ge) (fun S hS h₁ h₃ p₁ p₃ => ?_)
    (fun Z hZ _ G hG => ?_) F hF
  · rw [interNum_shortExact hS hL
      (finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k V) _ hp)
      (finiteCohTwists_of_isProjOver (algebraMap_eq_strHom k V) _ hp)]
    exact add_nonneg p₁ p₃
  · have := isIntegral_red hZ
    letI := algebraΓAlong k (redι Z)
    have hi := appTop_algebraMap_along k (redι Z)
    have hpZ : IsProjOver (strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
      rw [← comp_strHom hi]
      exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
    have hM := LB.isLB_pull hN (redι Z)
    have e : (fun i => ((![N] : Fin 1 → LB V) i).pull (redι Z)) = ![N.pull (redι Z)] := by
      funext i; fin_cases i; rfl
    have e' : (fun _ : Fin 1 => N.pull (redι Z)) = ![N.pull (redι Z)] := by
      funext i; fin_cases i; rfl
    rw [interNum_pushforward_of_isClosedImmersion hi G hL, e]
    have hdZ : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤ 1 :=
      (redι Z).isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hd
    rcases hdZ.eq_or_lt with h1 | h1
    · rw [VB.interNum_one_eq_genRank_mul k _ hpZ h1 G _ hM]
      refine mul_nonneg (Nat.cast_nonneg _) ?_
      have := h _ (redι Z) hi h1
      rwa [topSelf_def, e'] at this
    · refine (interNum_eq_zero_of_isProjOver (algebraMap_eq_strHom k _) G hpZ ?_
        fun i => by fin_cases i; exact hM).ge
      rw [Fintype.card_fin]
      exact (QCoh.suppDim_le G).trans_lt h1

theorem degOfRank_nonneg : ∀ (p : ℕ) [Fact p.Prime] (V : Scheme.{0}) [Algebra (ZMod p) Γ(V, ⊤)], IsProjOver (strHom (ZMod p) V) → topologicalKrullDim V ≤ 1 → ∀ N : LB V, N.IsLB → (∀ (Z : Scheme.{0}) (i : Z ⟶ V) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod p) (N.pull i) 1) → 0 ≤ degOfRank (ZMod p) (toMod N) 1 := by
  intro p _ V _ hp hd N hN h
  have := Twist.isFiniteQC_twist (F := structureModule V) hN
  have h1 := interNum_one_nonneg hp hd hN (fun Z i _ _ _ _ hZ => h Z i hZ)
    (twist (structureModule V) N) this
  have h2 := interNum_twist_cons (ZMod p) (structureModule V) (P := ![]) hN isEmptyElim
  have h3 : chi (ZMod p) (twist (structureModule V) N) = chi (ZMod p) (toMod N) :=
    chi_congr _ (Twist.unitTwistIso N)
  have h4 : interNum (ZMod p) (twist (structureModule V) N) ![N] =
    chi (ZMod p) (twist (structureModule V) N) - chi (ZMod p) (structureModule V) :=
    h2.trans (congrArg₂ (· - ·) (interNum_of_isEmpty _ _ _) (interNum_of_isEmpty _ _ _))
  rw [degOfRank]
  push_cast
  linarith

end GlobalTheory.CurveDevissage
end
end

