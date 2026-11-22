import Development.EtaleCohomology.TateTwists.Bundle0014
import Development.EtaleCohomology.TateTwists.Bundle0007
import Development.EtaleCohomology.TateTwists.Bundle0015
import Development.EtaleCohomology.TateTwists.Bundle0019
import Development.EtaleCohomology.TateTwists.Bundle0003
import Development.EtaleCohomology.TateTwists.Bundle0002
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle0001
import Development.EtaleCohomology.TateTwists.Bundle0016
import Development.EtaleCohomology.TateTwists.Bundle0012
import Development.EtaleCohomology.TateTwists.Bundle0010
import Development.EtaleCohomology.TateTwists.EtaleInjectiveSheafSectionsInjectiveHolds
import Development.EtaleCohomology.TateTwists.Bundle0021
import Development.EtaleCohomology.TateTwists.Bundle0008

-- bundled from Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.EtaleFoundations.PrimLocExPf

noncomputable abbrev cyc (A : Type) [CommRing A] (q : ℕ) : A[X] := (cyclotomic q ℤ).map (Int.castRingHom A)

theorem cyc_monic (A : Type) [CommRing A] (q : ℕ) : (cyc A q).Monic :=
  (cyclotomic.monic q ℤ).map _

theorem cyc_cond (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    ∃ p₁ p₂ : A[X], derivative (cyc A q) * p₁ + cyc A q * p₂ = 1 := by
  obtain ⟨h, hh⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have hh' : (X ^ q - 1 : A[X]) = cyc A q * h.map (Int.castRingHom A) := by
    have := congrArg (Polynomial.map (Int.castRingHom A)) hh
    simpa [Polynomial.map_mul] using this
  set H := h.map (Int.castRingHom A)
  have hd : (C (q : A)) * X ^ (q - 1) = derivative (cyc A q) * H + cyc A q * derivative H := by
    have := congrArg derivative hh'
    rw [derivative_mul] at this
    rw [← this]; simp [derivative_X_pow]
  obtain ⟨u, hu⟩ := hq
  refine ⟨C (↑u⁻¹ : A) * X * H, C (↑u⁻¹ : A) * (X * derivative H - C (q : A) * H), ?_⟩
  have hX : X * X ^ (q - 1) = (X ^ q : A[X]) := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_neZero q)]
  have key : C (q : A) * X ^ q = X * (derivative (cyc A q) * H + cyc A q * derivative H) := by
    rw [← hd, ← hX]; ring
  have hXq : (X ^ q : A[X]) = cyc A q * H + 1 := by rw [← hh']; ring
  have hCu : C (↑u⁻¹ : A) * C (q : A) = 1 := by rw [← C_mul, ← hu, Units.inv_mul, C_1]
  calc derivative (cyc A q) * (C (↑u⁻¹ : A) * X * H) + cyc A q * (C (↑u⁻¹ : A) * (X * derivative H - C (q : A) * H))
      = C (↑u⁻¹ : A) * (X * (derivative (cyc A q) * H + cyc A q * derivative H) - C (q : A) * (cyc A q * H)) := by ring
    _ = C (↑u⁻¹ : A) * (C (q : A) * X ^ q - C (q : A) * (cyc A q * H)) := by rw [key]
    _ = C (↑u⁻¹ : A) * C (q : A) := by rw [hXq]; ring
    _ = 1 := hCu

noncomputable def pair (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    StandardEtalePair A where
  f := cyc A q
  monic_f := cyc_monic A q
  g := 1
  cond := by obtain ⟨p₁, p₂, h⟩ := cyc_cond A q hq; exact ⟨p₁, p₂, 0, by simpa using h⟩

theorem hasMap_root (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    (pair A q hq).HasMap (AdjoinRoot.root (cyc A q)) := by
  refine ⟨?_, ?_⟩
  · have : (pair A q hq).f = cyc A q := rfl
    rw [this, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  · have : (pair A q hq).g = 1 := rfl
    rw [this, map_one]; exact isUnit_one

noncomputable def equivB (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    (pair A q hq).Ring ≃ₐ[A] AdjoinRoot (cyc A q) := by
  refine AlgEquiv.ofAlgHom ((pair A q hq).lift (AdjoinRoot.root (cyc A q)) (hasMap_root A q hq))
    (AdjoinRoot.liftAlgHom (cyc A q) (Algebra.ofId A _) (pair A q hq).X
      (pair A q hq).hasMap_X.1) ?_ ?_
  · apply AdjoinRoot.algHom_ext
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id_eq]
    exact (congrArg ((pair A q hq).lift _ (hasMap_root A q hq)) (AdjoinRoot.liftAlgHom_root _ _ _ _)).trans
      (StandardEtalePair.lift_X _ _ _)
  · apply StandardEtalePair.hom_ext
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id_eq]
    exact (congrArg (AdjoinRoot.liftAlgHom (cyc A q) (Algebra.ofId A _) (pair A q hq).X
      (pair A q hq).hasMap_X.1) (StandardEtalePair.lift_X _ _ _)).trans (AdjoinRoot.liftAlgHom_root _ _ _ _)

theorem etaleB (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    Algebra.Etale A (AdjoinRoot (cyc A q)) := by
  haveI : Algebra.IsStandardEtale A (AdjoinRoot (cyc A q)) :=
    Algebra.IsStandardEtale.of_equiv (equivB A q hq)
  infer_instance

theorem surjB (A : Type) [CommRing A] (q : ℕ) [NeZero q] :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (AdjoinRoot (cyc A q)))) := by
  intro p
  haveI : Nontrivial A := ⟨⟨0, 1, fun h => p.2.ne_top (by rw [Ideal.eq_top_iff_one, ← h]; exact p.1.zero_mem)⟩⟩
  have hm := cyc_monic A q
  have hdeg : 0 < (cyc A q).natDegree := by
    show 0 < ((cyclotomic q ℤ).map (Int.castRingHom A)).natDegree
    rw [(cyclotomic.monic q ℤ).natDegree_map, natDegree_cyclotomic]; exact Nat.totient_pos.mpr (Nat.pos_of_neZero q)
  haveI : Module.Free A (AdjoinRoot (cyc A q)) := .of_basis (AdjoinRoot.powerBasis' hm).basis
  haveI : Nontrivial (AdjoinRoot (cyc A q)) := by
    have hne : (AdjoinRoot.powerBasis' hm).basis ⟨0, hdeg⟩ ≠ 0 := (AdjoinRoot.powerBasis' hm).basis.ne_zero _
    exact nontrivial_of_ne _ _ hne
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat p

end LateralTheory.EtaleFoundations.PrimLocExPf

namespace LateralTheory.EtaleFoundations.PrimLocExPf

def primMap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (q : ℕ) (ζ : Prim q R) : Prim q S :=
  ⟨φ ζ.1, by simpa using ζ.2.1.map φ, by
    have h := Polynomial.aeval_algHom_apply φ.toIntAlgHom ζ.1 (Polynomial.cyclotomic q ℤ)
    rw [ζ.2.2, map_zero] at h
    simpa using h⟩

theorem root_prim (A : Type) [CommRing A] (q : ℕ) (hq : IsUnit (q : A)) :
    IsUnit (q : AdjoinRoot (cyc A q)) ∧
      aeval (AdjoinRoot.root (cyc A q)) (cyclotomic q ℤ) = 0 := by
  refine ⟨by simpa using hq.map (algebraMap A (AdjoinRoot (cyc A q))), ?_⟩
  have : cyc A q = (cyclotomic q ℤ).map (algebraMap ℤ A) := by rw [algebraMap_int_eq]
  rw [← Polynomial.aeval_map_algebraMap A, ← this, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

theorem mono_prim (q : ℕ) {U : Scheme.{0}} : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
    Nonempty (Prim q Γ(V, ⊤)) → Nonempty (Prim q Γ(W, ⊤)) := by
  rintro V W g k ⟨ζ⟩
  exact ⟨primMap k.appTop.hom q ζ⟩

end LateralTheory.EtaleFoundations.PrimLocExPf

namespace LateralTheory.EtaleFoundations

open PrimLocExPf in
theorem etale_locally_exists_primitive_root_of_unity_of_invertible_order : EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder := by
  intro q _ U hq
  rw [etale_sheaf_section_locally_iff_of_presheaf_facts U (fun V _ => Nonempty (Prim q Γ(V, ⊤))) (mono_prim q)]
  intro y
  obtain ⟨W, hWa, hyW, -⟩ : ∃ W : U.Opens, IsAffineOpen W ∧ y ∈ W ∧ W ≤ ⊤ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens) (show y ∈ (⊤ : U.Opens) from trivial)
  have hqA : IsUnit (q : Γ(U, W)) := by
    simpa using hq.map (U.presheaf.map (homOfLE le_top).op).hom
  have hE := etaleB Γ(U, W) q hqA
  let φ : Γ(U, W) ⟶ CommRingCat.of (AdjoinRoot (cyc Γ(U, W) q)) := CommRingCat.ofHom (algebraMap _ _)
  have hφ : Etale (Spec.map φ) :=
    HasRingHomProperty.Spec_iff.mpr
      ((RingHom.etale_algebraMap (R := Γ(U, W)) (S := AdjoinRoot (cyc Γ(U, W) q))).mpr hE)
  refine ⟨_, Spec.map φ ≫ hWa.fromSpec, inferInstance, inferInstance, ?_, ?_⟩
  · have hy : y ∈ Set.range hWa.fromSpec := by rw [hWa.range_fromSpec]; exact hyW
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨r, hr⟩ := surjB Γ(U, W) q p
    exact ⟨r, congrArg hWa.fromSpec hr⟩
  · have h := root_prim Γ(U, W) q hqA
    exact ⟨primMap (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot (cyc Γ(U, W) q)))).inv.hom q
      ⟨AdjoinRoot.root _, h.1, h.2⟩⟩

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleLocallyKummerRootsOfUnitsOfInvertibleOrder
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.EtaleFoundations.PrimLocKumPf

noncomputable abbrev kpol {A : Type} [CommRing A] (q : ℕ) (u : A) : A[X] := X ^ q - C u

theorem kpol_monic {A : Type} [CommRing A] (q : ℕ) [NeZero q] (u : A) : (kpol q u).Monic :=
  monic_X_pow_sub_C u (NeZero.ne q)

theorem kpol_natDegree {A : Type} [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] (u : A) :
    (kpol q u).natDegree = q :=
  natDegree_X_pow_sub_C

theorem root_pow {A : Type} [CommRing A] (q : ℕ) (u : A) :
    AdjoinRoot.root (kpol q u) ^ q = algebraMap A (AdjoinRoot (kpol q u)) u := by
  have h := AdjoinRoot.eval₂_root (kpol q u)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [← AdjoinRoot.algebraMap_eq] at h
  exact sub_eq_zero.mp h

theorem root_isUnit {A : Type} [CommRing A] (q : ℕ) [NeZero q] (u : Aˣ) :
    IsUnit (AdjoinRoot.root (kpol q (u : A))) := by
  have h : IsUnit (AdjoinRoot.root (kpol q (u : A)) ^ q) := by
    rw [root_pow]; exact u.isUnit.map _
  exact (isUnit_pow_iff (NeZero.ne q)).mp h

theorem deriv_isUnit {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) (u : Aˣ) :
    IsUnit (AdjoinRoot.mk (kpol q (u : A)) (derivative (kpol q (u : A)))) := by
  have hd : derivative (kpol q (u : A)) = C (q : A) * X ^ (q - 1) := by
    simp [kpol, derivative_X_pow]
  rw [hd, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
  refine IsUnit.mul (hq.map _) ?_
  exact (root_isUnit q u).pow _

theorem etale_kum {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) (u : Aˣ) :
    Algebra.Etale A (AdjoinRoot (kpol q (u : A))) :=
  let P : StandardEtalePair A := ⟨kpol q (u : A), kpol_monic q _, derivative (kpol q (u : A)), 1, 0, 1, by simp⟩
  .of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit _ (Localization.Away (AdjoinRoot.mk P.f (derivative (kpol q (u : A))))) _
      (deriv_isUnit q hq u)).symm.restrictScalars A))

theorem ff_kum {A : Type} [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] (u : A) :
    Module.FaithfullyFlat A (AdjoinRoot (kpol q u)) := by
  have hf := kpol_monic q u
  have : Module.Free A (AdjoinRoot (kpol q u)) := hf.free_adjoinRoot
  have : Module.Finite A (AdjoinRoot (kpol q u)) := hf.finite_adjoinRoot
  have hr : Module.finrank A (AdjoinRoot (kpol q u)) = q := by
    rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasis' hf).basis, Fintype.card_fin]
    exact kpol_natDegree q u
  have : Nontrivial (AdjoinRoot (kpol q u)) :=
    Module.nontrivial_of_finrank_pos (R := A) (by rw [hr]; exact Nat.pos_of_neZero q)
  infer_instance

theorem mono_kum (q : ℕ) {U : Scheme.{0}} (u : (Γ(U, ⊤))ˣ) :
    ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
    (∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u) →
    ∃ v : (Γ(W, ⊤))ˣ, v ^ q = Units.map (k ≫ g).appTop.hom.toMonoidHom u := by
  rintro V W g k ⟨v, hv⟩
  refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
  rw [← map_pow, hv]
  ext
  simp <;> rfl

theorem pt (q : ℕ) [NeZero q] (U : Scheme.{0}) (hq : IsUnit (q : Γ(U, ⊤))) (u : (Γ(U, ⊤))ˣ)
    (y : U) : ∃ (V : Scheme.{0}) (g : V ⟶ U), IsAffine V ∧ Etale g ∧ y ∈ Set.range g ∧
      ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u := by
  obtain ⟨W, hW, hyW, -⟩ : ∃ W : U.Opens, IsAffineOpen W ∧ y ∈ W ∧ W ≤ ⊤ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens) (Set.mem_univ y)
  obtain ⟨z, hz⟩ : y ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hyW
  let A : CommRingCat.{0} := Γ(U, W)
  have : Nontrivial A := by
    have := z.asIdeal.ne_top_iff_one.mp z.isPrime.ne_top
    exact ⟨⟨1, 0, fun h => this (h ▸ z.asIdeal.zero_mem)⟩⟩
  let ρ : Γ(U, ⊤) →+* A := (Scheme.ΓSpecIso A).hom.hom.comp hW.fromSpec.appTop.hom
  let u₁ : Aˣ := Units.map ρ.toMonoidHom u
  have hqA : IsUnit (q : A) := by simpa using hq.map ρ
  let B : CommRingCat.{0} := CommRingCat.of (AdjoinRoot (kpol q (u₁ : A)))
  let φ : A ⟶ B := CommRingCat.ofHom (algebraMap A (AdjoinRoot (kpol q (u₁ : A))))
  have he : Algebra.Etale A (AdjoinRoot (kpol q (u₁ : A))) := etale_kum q hqA u₁
  have hff : Module.FaithfullyFlat A (AdjoinRoot (kpol q (u₁ : A))) := ff_kum q _
  have hE : Etale (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr he
  have hS : Surjective (Spec.map φ) :=
    ((flat_and_surjective_SpecMap_iff φ).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)).2
  refine ⟨Spec B, Spec.map φ ≫ hW.fromSpec, inferInstance, inferInstance, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hS.surj z
    exact ⟨w, by simp [hw, hz]⟩
  · obtain ⟨r, hr⟩ := root_isUnit q u₁
    refine ⟨Units.map (Scheme.ΓSpecIso B).inv.hom.toMonoidHom r, ?_⟩
    ext
    set w : Γ(Spec A, ⊤) := hW.fromSpec.appTop.hom (u : Γ(U, ⊤)) with hw
    have hnat : (Scheme.ΓSpecIso B).hom.hom ((Spec.map φ).appTop.hom w) =
        φ.hom ((Scheme.ΓSpecIso A).hom.hom w) := by
      rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
    simp only [Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe]
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    show ((Scheme.ΓSpecIso B).inv.hom (r : AdjoinRoot (kpol q (u₁ : A)))) ^ q =
      (Spec.map φ).appTop.hom w
    rw [← map_pow, hr, root_pow]
    change (Scheme.ΓSpecIso B).inv.hom (φ.hom ((Scheme.ΓSpecIso A).hom.hom w)) = _
    rw [← hnat, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

end LateralTheory.EtaleFoundations.PrimLocKumPf

theorem LateralTheory.EtaleFoundations.etale_locally_kummer_roots_of_units_of_invertible_order : LateralTheory.EtaleFoundations.EtaleLocallyKummerRootsOfUnits := by
  intro q _ U hq u
  rw [LateralTheory.EtaleFoundations.etale_sheaf_section_locally_iff_of_presheaf_facts U _ (LateralTheory.EtaleFoundations.PrimLocKumPf.mono_kum q u)]
  exact LateralTheory.EtaleFoundations.PrimLocKumPf.pt q U hq u
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleMayerVietorisShortExactSequenceFreeOfCompon
section
namespace LateralTheory.Fin.EtaleMayerVietorisChainsShortExact
theorem etale_mayer_vietoris_short_exact_sequence_free_of_components : LateralTheory.EtaleFoundations.EtaleFreePresheafMayerVietorisShortExact := by
  apply LateralTheory.EtaleFoundations.etale_free_presheaf_mayer_vietoris_short_exact_holds
theorem etale_mayer_vietoris_short_exact_sequence_of_components : LateralTheory.EtaleFoundations.EtaleMayerVietorisChainsShortExact := by
  apply LateralTheory.EtaleFoundations.etale_chains_mayer_vietoris_short_exact_of_free <;> first | exact etale_mayer_vietoris_short_exact_sequence_free_of_components
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleMayerVietorisChainsShortExact := etale_mayer_vietoris_short_exact_sequence_of_components
end LateralTheory.Fin.EtaleMayerVietorisChainsShortExact
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSheafRestrictScalarsFunctorExactOfAdjoints
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

lemma restr_isRightAdjoint (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) :
    (restr φ).IsRightAdjoint := by
  unfold restr
  exact (Sheaf.adjunction Scheme.etaleTopology.{0} (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1}
    ((ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom)))).isRightAdjoint

lemma restr_isLeftAdjoint (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) :
    (restr φ).IsLeftAdjoint := by
  unfold restr
  set f := ((ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom))
  have hpl : PreservesLimitsOfSize.{0, 1} (ModuleCat.coextendScalars.{1, 1, 1} f) :=
    (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} f).rightAdjoint_preservesLimits
  have : Scheme.etaleTopology.{0}.HasSheafCompose (ModuleCat.coextendScalars.{1, 1, 1} f) :=
    hasSheafCompose_of_preservesLimitsOfSize _
  have adj := Sheaf.adjunction Scheme.etaleTopology.{0} (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} f)
  have := (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).counit_isIso_of_R_fully_faithful
  have e : Sheaf.composeAndSheafify Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f) ≅
      sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f) :=
    NatIso.ofComponents (fun X => (asIso (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).counit).app
      ((sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f)).obj X)) (by
        intro X Y g
        exact (sheafificationAdjunction _ _).counit.naturality
          ((sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} f)).map g))
  exact ⟨_, ⟨adj.ofNatIsoLeft e⟩⟩

theorem etaleSheaf_restrictScalars_functor_exact_of_adjoints : EtaleSheafRestrictScalarsFunctorExact := by
  intro R S _ _ φ
  have := restr_isRightAdjoint R S φ
  have := restr_isLeftAdjoint R S φ
  exact ⟨inferInstance, inferInstance⟩

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSteenrodPrismHomotopyOfAcyclicAlexanderWhit
section
open LateralTheory.EtaleFoundations.SteenPf in

theorem LateralTheory.EtaleFoundations.etale_steenrod_prism_homotopy_of_acyclic_alexander_whitney (hA : leaf_acyc) (hAW : leaf_aw) (hWA : leaf_wa) :
    LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy :=
  LateralTheory.EtaleFoundations.etale_prism_alexander_whitney_homotopy_of_relations hA steenrod_prism_chain_differential_squared_eq_zero_of_etale prism_boundary_map_square_zero_holds hAW hWA
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTateTwistGeneratorMapInjectiveOfSectionsGlu
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section
namespace LateralTheory.EtaleFoundations.GenIsoInj

theorem ulift_smul_eq {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (r : ULift.{1} (ZMod q)) (x : M) : r • x = r.down.val • x := by
  have : r = ((r.down.val : ℕ) : ULift.{1} (ZMod q)) := by
    apply ULift.ext; simp only [ULift.down_natCast, ZMod.natCast_zmod_val]
  conv_lhs => rw [this]
  rw [Nat.cast_smul_eq_nsmul]

theorem q_smul {q : ℕ} [NeZero q] {M : Type*} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (c : ℕ) (hc : q ∣ c) (x : M) : c • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((c : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    ext; simpa using (ZMod.natCast_eq_zero_iff c q).2 hc
  rw [this, zero_smul]

theorem exists_functional {q : ℕ} [NeZero q] {M : Type 1} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    (g : M) (hg : ∀ c : ℕ, c • g = 0 → q ∣ c) :
    ∃ F : M →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q), F g = 1 := by
  letI : Module (ZMod q) M :=
    Module.compHom M (ULift.ringEquiv.symm : ZMod q ≃+* ULift.{1} (ZMod q)).toRingHom
  have hsm : ∀ (r : ZMod q) (x : M), r • x = (ULift.up r : ULift.{1} (ZMod q)) • x := fun r x => rfl
  let f : ZMod q →ₗ[ZMod q] M := LinearMap.toSpanSingleton (ZMod q) M g
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    have h1 : r.val • g = 0 := by
      have h2 : (ULift.up r : ULift.{1} (ZMod q)) • g = 0 := hr
      have h4 := ulift_smul_eq (M := M) (ULift.up r : ULift.{1} (ZMod q)) g
      exact h4.symm.trans h2
    have h3 := hg _ h1
    rw [← ZMod.natCast_zmod_val r]
    exact (ZMod.natCast_eq_zero_iff _ _).2 h3
  obtain ⟨h, hh⟩ := (KStar.Selmer.zmod_baer (N := q)).extension_property f hf LinearMap.id
  refine ⟨{ toFun := fun x => ULift.up (h x), map_add' := fun x y => by ext; simp,
             map_smul' := fun r x => ?_ }, ?_⟩
  · change ULift.up (h (r.down • x)) = r • ULift.up (h x)
    rw [h.map_smul]
    ext; simp [smul_eq_mul]
  · have := LinearMap.congr_fun hh 1
    simp only [LinearMap.comp_apply, f, LinearMap.toSpanSingleton_apply, one_smul, LinearMap.id_apply] at this
    ext; simpa using this

theorem dvd_of_tmul {q : ℕ} [NeZero q] {M N : Type 1} [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M]
    [AddCommGroup N] [Module (ULift.{1} (ZMod q)) N] (g : M) (g' : N)
    (hg : ∀ c : ℕ, c • g = 0 → q ∣ c) (hg' : ∀ c : ℕ, c • g' = 0 → q ∣ c) (c : ℕ)
    (h : c • (g ⊗ₜ[ULift.{1} (ZMod q)] g') = 0) : q ∣ c := by
  obtain ⟨F, hF⟩ := exists_functional g hg
  obtain ⟨F', hF'⟩ := exists_functional g' hg'
  let L := TensorProduct.lift ((LinearMap.mul (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))).compl₂ F' ∘ₗ F)
  have := congrArg L h
  simp only [map_nsmul, L, TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.compl₂_apply,
    LinearMap.mul_apply', hF, hF', mul_one, map_zero, nsmul_eq_mul] at this
  have h2 := congrArg ULift.down this
  simp at h2
  exact (ZMod.natCast_eq_zero_iff _ _).1 h2

end LateralTheory.EtaleFoundations.GenIsoInj

namespace LateralTheory.EtaleFoundations.GenIsoInj

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U)
    (x : Sec F U) : Sec.res (h ≫ g) x = Sec.res h (Sec.res g x) := by
  simp [Sec.res]

theorem sm_nsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ℕ) (x : Sec F U) :
    Sec.map φ (c • x) = c • Sec.map φ x := map_nsmul _ _ _
theorem sm_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero _
theorem sr_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x := map_nsmul _ _ _
theorem sr_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem sgl_smul_eq_zero {q : ℕ} {F : Shv (ZMod q)} {U : Scheme.{0}} (c : ℕ) (x : Sec F U)
    (h : c • Sec.map (sglι F) x = 0) : c • x = 0 := by
  let ψ : (sgl F).X 0 ⟶ F := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom
  have hψ : sglι F ≫ ψ = 𝟙 F := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv_hom_id
  have e : ∀ y : Sec F U, Sec.map ψ (Sec.map (sglι F) y) = y := fun y => by
    rw [TwMulPf.sec_map_comp, hψ, TwMulPf.sec_map_id]
  have h' : Sec.map (sglι F) (c • x) = Sec.map (sglι F) 0 := by
    rw [show Sec.map (sglι F) (c • x) = c • Sec.map (sglι F) x from map_nsmul _ c x, h]
    exact (map_zero _).symm
  have := congrArg (Sec.map ψ) h'
  rwa [e, e] at this

end LateralTheory.EtaleFoundations.GenIsoInj

open LateralTheory.EtaleFoundations.GenIsoInj LateralTheory.EtaleFoundations.TwMulPf in

theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_map_injective_of_sections_glue (hts : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated)
    (hlb : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) (hsg : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue) :
    LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorMapSectionsInjective := by
  classical
  intro q _ i j k T μ hμ hk φ hφ U a ha
  have nt : ∀ (l : ℤ) (W : Scheme.{0}) [Nonempty W] (ζ : Prim q Γ(W, ⊤)) (c : ℕ),
      c • Sec.map (sglι (tw q l)) (twGen l ζ) = 0 → q ∣ c :=
    fun l W _ ζ c h => (hts q l).2.2.1 W ζ c (sgl_smul_eq_zero c _ h)
  refine hlb.2.2.2.2.1 U _ (hlb.2.1 U _ _ ((hts q k).1 U a) ?_)
  rintro V g (h0 | ⟨ζ, c, hc⟩)
  · exact hlb.1 V _ fun W h => by rw [res_comp, h0, sr_zero]
  · have h1 : c • μ.mul V 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ))
        (Sec.map (sglι _) (twGen j ζ)) = 0 := by
      rw [← hφ V ζ, ← sm_nsmul, ← sm_nsmul, ← hc, ← sec_res_map, ha, sr_zero, sm_zero]
    let x : Tens (sgl (tw q i)) (sgl (tw q j)) V 0 :=
      DirectSum.lof (ULift.{1} (ZMod q)) {p : ℤ × ℤ // p.1 + p.2 = 0}
        (fun p => Sec ((sgl (tw q i)).X p.1.1) V ⊗[ULift.{1} (ZMod q)] Sec ((sgl (tw q j)).X p.1.2) V)
        ⟨(0, 0), rfl⟩ (c • (Sec.map (sglι _) (twGen i ζ) ⊗ₜ Sec.map (sglι _) (twGen j ζ)))
    have hx : μ.lift V 0 x = 0 := by
      simp only [x, Pair.lift, DirectSum.toModule_lof, map_nsmul, TensorProduct.lift.tmul]
      exact h1
    refine hlb.2.1 V _ _ (hμ.2 V 0 x hx) fun W h hW => ?_
    have hW' : c • (Sec.res h (Sec.map (sglι _) (twGen i ζ)) ⊗ₜ[ULift.{1} (ZMod q)]
        Sec.res h (Sec.map (sglι _) (twGen j ζ))) = 0 := by
      have := congrArg (DirectSum.component (ULift.{1} (ZMod q)) {p : ℤ × ℤ // p.1 + p.2 = 0}
        (fun p => Sec ((sgl (tw q i)).X p.1.1) W ⊗[ULift.{1} (ZMod q)] Sec ((sgl (tw q j)).X p.1.2) W)
        ⟨(0, 0), rfl⟩) hW
      simpa [x, Tens.res, DirectSum.component.lof_self] using this
    show Sec.res (h ≫ g) a = 0
    rw [res_comp, hc, sr_nsmul]
    by_cases hne : Nonempty W
    · rw [sec_res_map, sec_res_map, (hts q i).2.2.2.1, (hts q j).2.2.2.1] at hW'
      exact q_smul c (dvd_of_tmul _ _ (nt i W _) (nt j W _) c hW') _
    · have : IsEmpty W := not_nonempty_iff.1 hne
      exact (hsg (ZMod q) (tw q k) W).1 _ _ (hlb.2.2.2.2.2.2 W _)
end
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorComplexUniversalOfDegreewise
section
namespace LateralTheory.Fin.EtaleTensorPairUniversalProperty
theorem etale_tensor_complex_degreewise_universal : LateralTheory.EtaleFoundations.EtaleTensorDegreewiseMapExists := by
  apply LateralTheory.EtaleFoundations.etale_tensor_pairing_degreewise_universal_of_sheafification
theorem etale_tensor_complex_universal_of_degreewise : LateralTheory.EtaleFoundations.EtaleTensorPairUniversalProperty := by
  apply LateralTheory.EtaleFoundations.etale_tensor_universal_property_of_degreewise <;> first | exact etale_tensor_complex_degreewise_universal
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleTensorPairUniversalProperty := etale_tensor_complex_universal_of_degreewise
end LateralTheory.Fin.EtaleTensorPairUniversalProperty
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorProductSheafExistsOfComponents
section
namespace LateralTheory.Fin.EtaleComplexTensorPairingExists
theorem etale_tensor_product_sheaf_exists_of_components : LateralTheory.EtaleFoundations.EtaleSheafTensorComplexExists := by
  apply LateralTheory.EtaleFoundations.etale_sheaf_tensor_complex_exists
theorem etale_tensor_product_exists_of_components : LateralTheory.EtaleFoundations.EtaleComplexTensorPairingExists := by
  apply LateralTheory.EtaleFoundations.etale_tensor_complex_exists_of_sheaf_tensor_complex <;> first | exact etale_tensor_product_sheaf_exists_of_components
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleComplexTensorPairingExists := etale_tensor_product_exists_of_components
end LateralTheory.Fin.EtaleComplexTensorPairingExists
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTwistedResolutionExistsOfFlatSections
section
namespace LateralTheory.Fin.EtaleTwistResolutionUniversalExtension
theorem etale_twisted_resolution_sections_injective : LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective := by
  apply LateralTheory.EtaleFoundations.etale_injective_sheaf_sections_injective_holds
theorem etale_twisted_resolution_quasiIso_flat : LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat := by
  apply LateralTheory.EtaleFoundations.zmod_injective_module_flat_holds
theorem etale_twisted_resolution_exists_of_flat_sections : LateralTheory.EtaleFoundations.EtaleTwistResolutionUniversalExtension := by
  apply LateralTheory.EtaleFoundations.etale_tate_twist_resolution_universal_of_injective_sections_and_zmod_f <;> first | exact etale_twisted_resolution_sections_injective | exact etale_twisted_resolution_quasiIso_flat
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleTwistResolutionUniversalExtension := etale_twisted_resolution_exists_of_flat_sections
end LateralTheory.Fin.EtaleTwistResolutionUniversalExtension
end

-- bundled from Development.EtaleCohomology.TateTwists.TPaCpushHtpyPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem t_pa_cpush_htpy_of : t_pa_cpush_htpy := by
  intro R _ E I J u u' H n x
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
  show CohomologyClass.mk (zcomp α (Cocycle.ofHom u) (add_zero n)) =
    CohomologyClass.mk (zcomp α (Cocycle.ofHom u') (add_zero n))
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨α.1.comp (Cochain.ofHomotopy H) (show n + -1 = n - 1 by omega), ?_⟩
  rw [δ_comp _ _ _ (n + 1) 0 n (by omega) rfl (by omega), δ_ofHomotopy, Cocycle.δ_eq_zero]
  simp [zcomp, Cochain.comp_sub]

end LateralTheory.EtaleFoundations
end

