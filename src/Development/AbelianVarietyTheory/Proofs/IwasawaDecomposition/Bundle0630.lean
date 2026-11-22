import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0612
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelRefinementGenerating
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0614
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0616
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Principalise

theorem memIdealOfLocally {W : Scheme.{0}} (I : W.IdealSheafData) (A : W.affineOpens) (b : Γ(W, A.1))
    (h : ∀ y ∈ A.1, ∃ (B : W.affineOpens) (e : B.1 ≤ A.1), y ∈ B.1 ∧ resG W e b ∈ I.ideal B) :
    b ∈ I.ideal A := by
  have hk : ∀ B : W.affineOpens, I.ideal B = RingHom.ker (I.subschemeι.app B.1).hom := fun B => by
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
  rw [hk, RingHom.mem_ker]
  refine GlobalTheory.Cartier.ext_germ fun z hz => ?_
  obtain ⟨B, e, hzB, this⟩ := h _ hz
  rw [hk, RingHom.mem_ker, GlobalTheory.Cartier.app_resG] at this
  rw [← GlobalTheory.Cartier.germ_resG (I.subschemeι.preimage_mono e) z hzB, this, map_zero, map_zero]

theorem comapIdealTopLe {X W : Scheme.{0}} [IsAffine W] (J : X.IdealSheafData) (g : W ⟶ X)
    (U : X.affineOpens) (h : ⊤ ≤ g ⁻¹ᵁ U.1) :
    (J.comap g).ideal ⟨⊤, isAffineOpen_top W⟩ ≤ Ideal.map (g.appLE U.1 ⊤ h).hom (J.ideal U) := by
  have key : J.comap g ≤ Scheme.IdealSheafData.ofIdealTop (Ideal.map (g.appLE U.1 ⊤ h).hom (J.ideal U)) := by
    refine (GlobalTheory.Cartier.comap_le_iff _ _ _).2 fun U' a ha B hB => memIdealOfLocally _ _ _ fun y hy => ?_
    obtain ⟨t, htle, hyt⟩ := U.2.exists_basicOpen_le (V := U'.1 ⊓ U.1) ⟨g y, hB hy, h trivial⟩ (h trivial)
    obtain ⟨_, ⟨B', hB'a, rfl⟩, hyB', hB'le⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ B.1 ⊓ g ⁻¹ᵁ X.basicOpen t from ⟨hy, hyt⟩) (B.1 ⊓ g ⁻¹ᵁ X.basicOpen t).isOpen
    refine ⟨⟨B', hB'a⟩, fun x hx => (hB'le hx).1, hyB', ?_⟩
    have hDU' : X.basicOpen t ≤ U'.1 := htle.trans inf_le_left
    have h1 : resG X hDU' a ∈ J.ideal (X.affineBasicOpen t) :=
      J.ideal_le_comap_ideal (U := X.affineBasicOpen t) (V := U') hDU' ha
    rw [← J.map_ideal_basicOpen U t] at h1
    have hB'D : B' ≤ g ⁻¹ᵁ X.basicOpen t := fun x hx => (hB'le hx).2
    have e : resG W (fun x hx => (hB'le hx).1 : B' ≤ B.1) (resG W hB ((g.app U'.1).hom a)) =
        (g.appLE (X.basicOpen t) B' hB'D).hom (resG X hDU' a) := by
      show _ = resG W hB'D ((g.app (X.basicOpen t)).hom (resG X hDU' a))
      rw [GlobalTheory.Cartier.app_resG, GlobalTheory.Cartier.resG_resG, GlobalTheory.Cartier.resG_resG]
    rw [e, Scheme.IdealSheafData.ofIdealTop_ideal]
    have h2 := Ideal.mem_map_of_mem (g.appLE (X.basicOpen t) B' hB'D).hom h1
    rw [Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE] at h2
    rw [Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
    exact h2
  have := key ⟨⊤, isAffineOpen_top W⟩
  rw [Scheme.IdealSheafData.ofIdealTop_ideal] at this
  refine this.trans (le_of_eq ?_)
  convert Ideal.map_id _
  rw [show homOfLE (le_top : (⊤ : W.Opens) ≤ ⊤) = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

theorem comapIdealAffine : ∀ {X W : Scheme.{0}} (J : X.IdealSheafData) (g : W ⟶ X) (U : X.affineOpens) (A : W.affineOpens) (h : A.1 ≤ g ⁻¹ᵁ U.1), (J.comap g).ideal A = Ideal.map (g.appLE U.1 A.1 h).hom (J.ideal U) := by
  intro X W J g U A h
  apply le_antisymm
  · intro x hx
    have : IsAffine A.1.toScheme := A.2
    have hA : ⊤ ≤ A.1.ι ⁻¹ᵁ A.1 := A.1.ι_preimage_self.ge
    have h1 := (GlobalTheory.Cartier.comap_le_iff (J.comap g) A.1.ι _).1 le_rfl A x hx ⟨⊤, isAffineOpen_top _⟩ hA
    rw [← Scheme.IdealSheafData.comap_comp] at h1
    have h2 := comapIdealTopLe J (A.1.ι ≫ g) U (hA.trans (A.1.ι.preimage_mono h)) h1
    have hb : Function.Bijective (A.1.ι.appLE A.1 ⊤ hA).hom := ConcreteCategory.bijective_of_isIso _
    rw [← Ideal.comap_map_of_bijective _ hb (I := Ideal.map (g.appLE U.1 A.1 h).hom (J.ideal U)),
      Ideal.mem_comap, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
    exact h2
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact (GlobalTheory.Cartier.comap_le_iff J g _).1 le_rfl U a ha A h

theorem kerIdealAffine : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U) (I : Ideal Γ(X, U)), ∃ J : X.IdealSheafData, J.ideal ⟨U, hU⟩ = I ∧ ∀ N : ℕ, (N : Γ(X, U)) ∈ I → ∀ V : X.affineOpens, (N : Γ(X, V.1)) ∈ J.ideal V := by
  intro X _ U hU I
  have hR : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let q : Γ(X, U) →+* Γ(X, U) ⧸ I := Ideal.Quotient.mk I
  let f : Spec (CommRingCat.of (Γ(X, U) ⧸ I)) ⟶ X := Spec.map (CommRingCat.ofHom q) ≫ hU.fromSpec
  haveI : QuasiCompact f := quasiCompact_of_noetherianSpace_source f
  have hz : ⊤ ≤ f ⁻¹ᵁ U := fun _ _ => hU.range_fromSpec.subset ⟨_, rfl⟩
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have hzapp : f.appLE U ⊤ hz = hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map (CommRingCat.ofHom q)).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  have m2 : f.appLE U ⊤ hz = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop := by
    rw [hzapp]
    congr 1
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(X, U)).presheaf.map_id _
  have m3 : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop =
      CommRingCat.ofHom q ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q)).symm
  have k1 : ∀ b, (f.appLE U ⊤ hz).hom b = (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).inv.hom (q b) := by
    intro b
    rw [m2, m3]
    rfl
  refine ⟨f.ker, ?_, ?_⟩
  · ext a
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
    constructor
    · intro ha
      have h1 : (f.appLE U ⊤ hz).hom a = 0 := by
        show resG _ hz ((f.app U).hom a) = 0
        rw [ha, map_zero]
      rw [k1] at h1
      have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).hom.hom h1
      rw [Iso.inv_hom_id_apply, map_zero] at h2
      exact Ideal.Quotient.eq_zero_iff_mem.1 h2
    · intro ha
      have h1 : (f.appLE U ⊤ hz).hom a = 0 := by
        rw [k1, show q a = 0 from Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
      refine GlobalTheory.Cartier.ext_germ fun x hx => ?_
      rw [map_zero, ← GlobalTheory.Cartier.germ_resG hz x trivial]
      exact (congrArg _ h1).trans (map_zero _)
  · intro N hN V
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker, map_natCast]
    have h0 : (N : Γ(X, U) ⧸ I) = 0 := by
      rw [← map_natCast q, Ideal.Quotient.eq_zero_iff_mem]; exact hN
    have h1 : (N : Γ(Spec (CommRingCat.of (Γ(X, U) ⧸ I)), ⊤)) = 0 := by
      rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).inv.hom, h0, map_zero]
    rw [← map_natCast (resG _ (le_top : f ⁻¹ᵁ V.1 ≤ ⊤)), h1, map_zero]

theorem exists_dvd_of_span_mul_eq {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] {m : ℕ}
    (A : Fin m → R) (I' : Ideal R) {f : R} (h : Ideal.span (Set.range A) * I' = Ideal.span {f})
    (hf : f ∈ nonZeroDivisors R) : ∃ k, ∃ s ∉ P, ∀ k', A k ∣ s * A k' := by
  have hfm : f ∈ Ideal.span (Set.range A) * I' := h ▸ Ideal.mem_span_singleton_self f
  have key : ∀ x ∈ Ideal.span (Set.range A) * I', ∃ c : Fin m → R, (∀ k, c k ∈ I') ∧ x = ∑ k, A k * c k := by
    intro x hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun x y ⟨c, hc, hx⟩ ⟨d, hd, hy⟩ => ?_)
    · obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 ha
      refine ⟨fun k => d k * b, fun k => I'.mul_mem_left _ hb, ?_⟩
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by simp only [smul_eq_mul]; ring
    · refine ⟨c + d, fun k => I'.add_mem (hc k) (hd k), ?_⟩
      simp only [hx, hy, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  obtain ⟨c, hc, hfc⟩ := key f hfm
  have hAc : ∀ k k', ∃ t, A k' * c k = f * t := fun k k' => by
    have : A k' * c k ∈ Ideal.span {f} :=
      h ▸ Ideal.mul_mem_mul (Ideal.subset_span ⟨k', rfl⟩) (hc k)
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨t, by rw [← ht, mul_comm]⟩
  choose t ht using hAc
  have hsum : ∑ k, t k k = 1 := by
    refine (mul_cancel_left_mem_nonZeroDivisors hf).1 ?_
    rw [Finset.mul_sum, _root_.mul_one]
    conv_rhs => rw [hfc]
    exact Finset.sum_congr rfl fun k _ => (ht k k).symm
  obtain ⟨k, hk⟩ : ∃ k, t k k ∉ P := by
    by_contra hcon
    push_neg at hcon
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2
      (hsum ▸ Ideal.sum_mem _ fun k _ => hcon k))
  refine ⟨k, t k k, hk, fun k' => ⟨t k k', ?_⟩⟩
  refine (mul_cancel_left_mem_nonZeroDivisors hf).1 ?_
  calc f * (t k k * A k') = (f * t k k) * A k' := by ring
    _ = A k * c k * A k' := by rw [ht]
    _ = A k * (A k' * c k) := by ring
    _ = f * (A k * t k k') := by rw [ht]; ring

theorem exists_idealSheaf_principalises : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (p n : ℕ) (U : Fin n → X.Opens) (m : Fin n → ℕ) (A : ∀ j, Fin (m j) → Γ(X, U j)), (∀ j, IsAffineOpen (U j)) → (∀ j, (p : Γ(X, U j)) ∈ (Ideal.span (Set.range (A j))).radical) → ∃ J : X.IdealSheafData, (∀ x ∈ J.support, x ∉ X.basicOpen (p : Γ(X, ⊤))) ∧ ∀ (W W' : Scheme.{0}) (b : W ⟶ X) (ν : W' ⟶ W), ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap b) → ∀ (w : W') (j : Fin n), (ν ≫ b) w ∈ U j → ∃ (V : W'.Opens) (hV : V ≤ (ν ≫ b) ⁻¹ᵁ U j), w ∈ V ∧ IsAffineOpen V ∧ ∃ k, ∀ k', ((ν ≫ b).appLE (U j) V hV).hom (A j k) ∣ ((ν ≫ b).appLE (U j) V hV).hom (A j k') := by
  intro X _ p n U m A hU hp
  choose J hJU hJp using fun j => kerIdealAffine X (U j) (hU j) (Ideal.span (Set.range (A j)))
  choose N hN using fun j => hp j
  have hmem : ∀ (V : X.affineOpens) (s : Finset (Fin n)),
      ((p ^ (∑ j ∈ s, N j) : ℕ) : Γ(X, V.1)) ∈ (∏ j ∈ s, J j).ideal V := by
    intro V s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
        pow_add, Nat.cast_mul]
      refine Ideal.mul_mem_mul (hJp j _ ?_ V) ih
      rw [Nat.cast_pow]
      exact hN j
  refine ⟨∏ j, J j, fun x hx hxp => ?_, ?_⟩
  · obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have h1 := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hxV).1 hx
    rw [Scheme.mem_zeroLocus_iff] at h1
    refine h1 _ (hmem ⟨V, hV⟩ Finset.univ) ?_
    have e : ((p ^ (∑ j, N j) : ℕ) : Γ(X, V)) =
        (X.presheaf.map (homOfLE le_top).op).hom ((p : Γ(X, ⊤)) ^ (∑ j, N j)) := by
      simp
    rw [e, Scheme.basicOpen_res]
    refine ⟨hxV, ?_⟩
    have htop : x ∈ (⊤ : X.Opens) := trivial
    show x ∈ X.basicOpen _
    rw [Scheme.mem_basicOpen _ _ _ htop, map_pow]
    exact ((Scheme.mem_basicOpen _ _ _ htop).1 hxp).pow _
  · intro W W' b ν hE w j hw
    have hw0 : b (ν w) ∈ U j := hw
    obtain ⟨V₁, f, hw₁, hf, hV₁⟩ := hE (ν w)
    obtain ⟨g, hgle, hwg⟩ := V₁.2.exists_basicOpen_le (V := V₁.1 ⊓ b ⁻¹ᵁ U j) ⟨ν w, hw₁, hw0⟩ hw₁
    have hDU : (W.affineBasicOpen g).1 ≤ b ⁻¹ᵁ U j := hgle.trans inf_le_right
    have hDV : (W.affineBasicOpen g).1 ≤ V₁.1 := W.basicOpen_le g
    have hfD : (W.presheaf.map (homOfLE hDV).op).hom f ∈ nonZeroDivisors Γ(W, (W.affineBasicOpen g).1) :=
      (GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen (W.affineBasicOpen g).2).1
        (((GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen V₁.2).2 hf).resG hDV)
    have hI1 := ((∏ i, J i).comap b).map_ideal_basicOpen V₁ g
    rw [hV₁, Ideal.map_span, Set.image_singleton] at hI1
    have hI2 := comapIdealAffine (∏ i, J i) b ⟨U j, hU j⟩ (W.affineBasicOpen g) hDU
    rw [← Finset.mul_prod_erase Finset.univ J (Finset.mem_univ j), Scheme.IdealSheafData.ideal_mul,
      Pi.mul_apply, Ideal.map_mul, hJU, Ideal.map_span, ← Set.range_comp] at hI2
    rw [← Finset.mul_prod_erase Finset.univ J (Finset.mem_univ j)] at hI1
    have hwD : ν w ∈ (W.affineBasicOpen g).1 := hwg
    obtain ⟨k, s, hsP, hdiv⟩ := exists_dvd_of_span_mul_eq
      (Ideal.comap (W.presheaf.germ (W.affineBasicOpen g).1 (ν w) hwD).hom (IsLocalRing.maximalIdeal _)) _ _
      (hI2.symm.trans hI1.symm) hfD
    have hsu : ν w ∈ W.basicOpen s := by
      rw [Scheme.mem_basicOpen _ _ _ hwD]
      by_contra hc
      exact hsP ((IsLocalRing.mem_maximalIdeal _).2 hc)
    have hED : W.basicOpen s ≤ (W.affineBasicOpen g).1 := W.basicOpen_le s
    obtain ⟨_, ⟨V, hVa, rfl⟩, hwV, hVE⟩ := W'.isBasis_affineOpens.exists_subset_of_mem_open
      (show w ∈ ν ⁻¹ᵁ W.basicOpen s from hsu) (ν ⁻¹ᵁ W.basicOpen s).isOpen
    have hVE' : V ≤ ν ⁻¹ᵁ W.basicOpen s := hVE
    have hV : V ≤ (ν ≫ b) ⁻¹ᵁ U j := fun x hx => hDU (hED (hVE' hx))
    refine ⟨V, hV, hwV, hVa, k, fun k' => ?_⟩
    have key : (b.appLE (U j) _ hDU ≫ W.presheaf.map (homOfLE hED).op) ≫ ν.appLE _ V hVE' =
        (ν ≫ b).appLE (U j) V hV := by
      rw [Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE]
    have hu := W.toRingedSpace.isUnit_res_basicOpen s
    have h1 := map_dvd (W.presheaf.map (homOfLE hED).op).hom (hdiv k')
    rw [map_mul] at h1
    have h2 := hu.dvd_mul_left.1 h1
    have h3 := map_dvd (ν.appLE _ V hVE').hom h2
    rw [← key]
    simpa using h3

end GlobalTheory.Principalise
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCommonModOfIsDiag
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.LocM.MapComp

namespace GlobalTheory.LocM.CommonMod

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem exists_lift (i : Idx H p) {k : Type} [Field k] (x : Sp k ⟶ (Y i).X) (f : i.c.F →+* k)
    (hf : x ≫ (Y i).s = spMap (f.comp (i.c.V W).subtype)) (hx : Set.range x ⊆ Set.range (Y i).j) :
    ∃ y : Sp k ⟶ (Xo i.l).XF i.c, y ≫ (Y i).j = x ∧ y ≫ pullback.snd _ _ = spMap f := by
  have : IsPreimmersion (spMap (i.c.V W).subtype) :=
    IsPreimmersion.of_isLocalization (S := i.c.F) (nonZeroDivisors (i.c.V W))
  have := (Y i).jQ_open
  let z : Sp k ⟶ pullback (Y i).s (spMap (i.c.V W).subtype) :=
    pullback.lift x (spMap f) (hf.trans (sp_comp _ _).symm)
  have hz : z ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _
  have hr : Set.range z ⊆ Set.range (Y i).jQ := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hx ⟨a, rfl⟩
    refine ⟨b, (pullback.fst (Y i).s (spMap (i.c.V W).subtype)).isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hz]
    exact hb
  have e := IsOpenImmersion.lift_fac (Y i).jQ z hr
  refine ⟨IsOpenImmersion.lift (Y i).jQ z hr, ?_, ?_⟩
  · rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, ← Category.assoc, e, hz]
  · rw [← (Y i).jQ_over, ← Category.assoc, e]
    exact pullback.lift_snd _ _ _

theorem exists_lift_chart (Z : Mdl Y i₀) {k : Type} [Field k] {w : Sp k ⟶ Z.X} {a : Fin Z.m}
    {φ : Γ(Z.X, (Z.U a).1) →+* k} (h : spMap φ ≫ Z.chart a = w) :
    ∃ y : Sp k ⟶ (Xo Z.i.l).XF Z.i.c, y ≫ (Y Z.i).j = w ≫ Z.π ∧ y ≫ pullback.snd _ _ = spMap (φ.comp (Z.alg a)) := by
  refine exists_lift Z.i _ _ (by rw [Category.assoc, Z.π_s, ← h, Category.assoc, Z.affineOpenChart_comp_structure_eq_spMap]) ?_
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Hom.comp_apply]
  refine Z.cover.le (Set.mem_iUnion.2 ⟨a, ?_⟩)
  exact (Z.U a).2.range_fromSpec.le ⟨spMap φ x, by rw [← h]; exact (Scheme.Hom.comp_apply _ _ _).symm⟩

theorem flagAt_chart (Z : Mdl Y i₀) {k : Type} [Field k] {w : Sp k ⟶ Z.X} {a : Fin Z.m}
    {φ : Γ(Z.X, (Z.U a).1) →+* k} (h : spMap φ ≫ Z.chart a = w) : Z.FlagAt w ((Z.fr a).bc φ) := by
  have hf := isFrame_bc E H Dw _ _ _ _ _ _ _ φ _ _ (Z.frame a)
  rw [← Category.assoc, h] at hf
  exact ⟨a, φ, h, hf, SameFlag.refl fun τ i => (hf.1 τ i).1⟩

theorem natImg_refl (Z : Mdl Y i₀) {k : Type} [Field k] {w : Sp k ⟶ Z.X} (hw : Set.range w ⊆ Z.opn) :
    NatImg Z Z w w := by
  obtain ⟨mu, hmu, ht⟩ := exists_isTrans_id (Y := Y) Z.i
  obtain ⟨a, φ, h⟩ := Z.exists_chart w hw
  refine ⟨𝟙 _, mu, (Z.fr a).bc φ, ht, by simp, flagAt_chart Z h, ?_⟩
  simpa only [hmu, Category.comp_id] using flagAt_chart Z h

theorem flagAt_push {Z₁ Z₂ : Mdl Y i₀} (hty : ∀ σ, Z₂.ty σ ⊆ Z₁.ty σ) {k : Type} [Field k] {w₁ : Sp k ⟶ Z₁.X}
    {w₂ : Sp k ⟶ Z₂.X} {τ : (Y Z₁.i).X ⟶ (Y Z₂.i).X} (mu : SABMap (Y Z₁.i).t (Y Z₂.i).t τ)
    (e : w₂ ≫ Z₂.π = w₁ ≫ Z₁.π ≫ τ) {u v : Vecs Dw (Y Z₁.i).t k} (hu : Z₁.FlagAt w₁ u) (hv : Z₁.FlagAt w₁ v)
    (h : Z₂.FlagAt w₂ fun σ j => u σ j ≫ mu.φ) : Z₂.FlagAt w₂ fun σ j => v σ j ≫ mu.φ := by
  obtain ⟨b, ψ, hb, fu, su⟩ := h
  obtain ⟨c, k₁, k₂, k₃⟩ := flagAt_two Z₁ hu hv
  rw [← Category.assoc] at e
  have fr : IsFrame (Y Z₂.i).t (ψ.comp (Z₂.alg b)) (w₂ ≫ Z₂.π) (Dw := Dw) fun σ j => v σ j ≫ mu.φ := by
    rw [e] at fu ⊢
    exact isFrame_push mu k₁ k₂ fu
  have sf := sameFlag_push mu hty k₃
  rw [← e] at sf
  exact ⟨b, ψ, hb, fr, sameFlag_trans (tan_chart Z₂ hb) (fun σ j => (fu.1 σ j).1) (fun σ j => (fr.1 σ j).1) su sf⟩

theorem natImg_unique {Z₁ Z₂ : Mdl Y i₀} (h : LocM.Corr Z₁ Z₂) {k : Type} [Field k] {w₁ : Sp k ⟶ Z₁.X}
    {w₂ w₂' : Sp k ⟶ Z₂.X} (hf : NatImg Z₁ Z₂ w₁ w₂) (hg : NatImg Z₁ Z₂ w₁ w₂') : w₂ = w₂' := by
  obtain ⟨τ, mu, u, t, e, fu, fu'⟩ := hf
  obtain ⟨τ', mu', v, t', e', fv, fv'⟩ := hg
  obtain ⟨rfl, hmu⟩ := TransUniq.trans_unique E H Dw Xo p W Y _ _ τ τ' mu mu' h.2.1 t t'
  have fv₀ := fv
  obtain ⟨a, φ, ha, gv, -⟩ := fv₀
  obtain ⟨y, hy, -⟩ := exists_lift_chart Z₁ ha
  have ev : (fun σ j => v σ j ≫ mu'.φ : Vecs Dw (Y Z₂.i).t k) = fun σ j => v σ j ≫ mu.φ :=
    funext fun σ => funext fun j => (hmu k y _ _ _ (by rw [hy]; exact (gv.1 σ j).1.1)).symm
  rw [ev] at fv'
  have f₂ := flagAt_push h.2.2 mu e fu fv fu'
  have f₃ := f₂
  obtain ⟨b, ψ, hb, g, -⟩ := f₃
  obtain ⟨y₂, hy₂, hs⟩ := exists_lift_chart Z₂ hb
  rw [← hy₂] at g
  exact (Z₂.bij k _ y₂ hs _ g).unique ⟨hy₂.symm, f₂⟩ ⟨(e'.trans e.symm).trans hy₂.symm, fv'⟩

theorem comp_π_eq {M Z : Mdl Y i₀} {f : M.X ⟶ Z.X} (hf : IsMap M Z f) {τ : (Y M.i).X ⟶ (Y Z.i).X}
    {mu : SABMap (Y M.i).t (Y Z.i).t τ} (t : IsTrans Z.i M.i τ mu) : f ≫ Z.π = M.π ≫ τ := by
  have := M.normal
  have : IsReduced M.X := GlobalTheory.IsNormalScheme.isReduced
  have := Toroidal.isProper_toroidalModel_structureMap (Y Z.i)
  have : IsSeparated ((Y Z.i).s ≫ terminal.from _) := inferInstance
  refine ext_of_fromSpecResidueField_eq _ _ ((Y Z.i).s ≫ terminal.from _) M.opn M.dense (fun x hx => ?_)
    (terminal.hom_ext _ _)
  obtain ⟨τ', mu', -, t', e, -⟩ := hf.2 (M.X.residueField x) (M.X.fromSpecResidueField x) (by
    rintro _ ⟨a, rfl⟩
    exact (Scheme.fromSpecResidueField_apply x a).symm ▸ hx)
  obtain ⟨rfl, -⟩ := TransUniq.trans_unique E H Dw Xo p W Y _ _ τ τ' mu mu' hf.1.2.1 t t'
  exact (Category.assoc _ _ _).symm.trans e

theorem map_mem_opn {M Z : Mdl Y i₀} {f : M.X ⟶ Z.X} (hf : IsMap M Z f) {x : M.X} (hx : x ∈ M.opn) : f x ∈ Z.opn := by
  obtain ⟨_, _, _, -, -, -, h⟩ := hf.2 (M.X.residueField x) (M.X.fromSpecResidueField x) (by
    rintro _ ⟨a, rfl⟩
    exact (Scheme.fromSpecResidueField_apply x a).symm ▸ hx)
  let a : Sp (M.X.residueField x) := IsLocalRing.closedPoint _
  refine range_subset_opn Z h ⟨a, (Scheme.Hom.comp_apply _ _ a).trans ?_⟩
  exact congrArg f (Scheme.fromSpecResidueField_apply x a)

theorem mem_genO_of_mem_opn (hp : p ≠ 0) (Z : Mdl Y i₀) {x : Z.X} (hx : x ∈ Z.opn) : x ∈ Z.genO := by
  obtain ⟨a, ha⟩ := Set.mem_iUnion.1 (Z.cover.ge hx)
  have hu : IsUnit ((p : ℕ) : Γ(Z.X, (Z.U a).1)) := by
    have := (IsUnit.mk0 ((p : ℕ) : Z.i.c.F) (Nat.cast_ne_zero.2 hp)).map (Z.alg a)
    rwa [map_natCast] at this
  have h := Z.X.basicOpen_res ((p : ℕ) : Γ(Z.X, ⊤)) (homOfLE (le_top : (Z.U a).1 ≤ ⊤)).op
  rw [map_natCast, Scheme.basicOpen_of_isUnit _ hu] at h
  exact (h.le ha).2

theorem preimage_genO {M Z : Mdl Y i₀} (f : M.X ⟶ Z.X) : f ⁻¹ᵁ Z.genO = M.genO := by
  rw [Mdl.genO, Scheme.preimage_basicOpen_top, map_natCast]
  rfl

def genMap {M Z : Mdl Y i₀} (f : M.X ⟶ Z.X) : M.genO.toScheme ⟶ Z.genO.toScheme :=
  f.resLE Z.genO M.genO (preimage_genO f).ge

@[reassoc] theorem genMap_ι {M Z : Mdl Y i₀} (f : M.X ⟶ Z.X) : genMap f ≫ Z.genO.ι = M.genO.ι ≫ f :=
  Scheme.Hom.resLE_comp_ι _ _

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

end GlobalTheory.LocM.CommonMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsotropicDualLatticeVector
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem exists_isotropic_partner (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (X : Data E N) (ξ : Fin N → E) (hξΛ : ξ ∈ X.Λ) (hξ : ξ ≠ 0) (hξξ : herm X.Gm ξ ξ = 0) :
    ∃ (η : Fin N → E) (d : ℕ), 0 < d ∧ η ∈ X.Λ ∧ herm X.Gm ξ η = d ∧ herm X.Gm η η = 0 := by
  have hG := X.Gm_herm
  obtain ⟨y, hy⟩ : ∃ y, herm X.Gm ξ y ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hξ (eq_zero_of_herm X.Gm X.Gm_det ξ hno)
  have h1 : herm X.Gm ξ ((cc (herm X.Gm ξ y))⁻¹ • y) = 1 := by
    rw [herm_smul_right, cc_inv, cc_cc]; exact inv_mul_cancel₀ hy
  obtain ⟨y1, hy1⟩ : ∃ y1, y1 = (cc (herm X.Gm ξ y))⁻¹ • y := ⟨_, rfl⟩
  rw [← hy1] at h1
  have h1' : herm X.Gm y1 ξ = 1 := by
    rw [← cc_herm X.Gm hG, h1, cc_one]
  have hhc : cc (herm X.Gm y1 y1) = herm X.Gm y1 y1 := cc_herm X.Gm hG y1 y1
  have hhalf : cc (herm X.Gm y1 y1 / 2) = herm X.Gm y1 y1 / 2 := by
    rw [div_eq_mul_inv, cc_mul, cc_inv, cc_two, hhc]
  have e1 : herm X.Gm ξ (y1 - (herm X.Gm y1 y1 / 2) • ξ) = 1 := by
    rw [herm_sub_right, herm_smul_right, h1, hξξ]; ring
  have e2 : herm X.Gm (y1 - (herm X.Gm y1 y1 / 2) • ξ) (y1 - (herm X.Gm y1 y1 / 2) • ξ) = 0 := by
    rw [herm_sub_left, herm_sub_right, herm_sub_right, herm_smul_right, herm_smul_right,
      herm_smul_left, herm_smul_left, h1, h1', hξξ, hhalf]
    ring
  obtain ⟨d, hd, hdΛ⟩ := GlobalTheory.T.exists_nat_smul_mem_lattice' E N X (y1 - (herm X.Gm y1 y1 / 2) • ξ)
  refine ⟨(d : E) • (y1 - (herm X.Gm y1 y1 / 2) • ξ), d, hd, hdΛ, ?_, ?_⟩
  · rw [herm_smul_right, cc_natCast, e1, mul_one]
  · rw [herm_smul_left, herm_smul_right, e2]; ring

end GlobalTheory.UnipKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenpartsFrameFamilyOverVarietyStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieEigenparts_frame_family_over_variety : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z), j ≫ genStr Z ≫ spMap e.toRingHom = B.str → ∃ (f₀ : EigFrame Z (constF e B) (genericPt B ≫ j ≫ genι Z)) (S : Fr (ratOf B) Dw.mult 0) (A₀ : Mat Dw.mult B.Fn), Tied e B j f₀ S A₀ := by
  first | exact @GlobalTheory.ShFam.TieBase.exists_tied | exact GlobalTheory.ShFam.TieBase.exists_tied | (intros; apply GlobalTheory.ShFam.TieBase.exists_tied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenspaceFrameLocalRingBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieEigenspaceFrame_localRing_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : c.F →+* R) (x : Sp R ⟶ Z.X) (f : EigFrame Z φ x) (ψ : R →+* R'), ∃ g : EigFrame Z (ψ.comp φ) (spMap ψ ≫ x), ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ f.v τ i := by
  first | exact @GlobalTheory.CuspFrom.exists_eigFrame_baseChange | exact GlobalTheory.CuspFrom.exists_eigFrame_baseChange | (intros; apply GlobalTheory.CuspFrom.exists_eigFrame_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelRefinementGeneratingStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_refinement_generating : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : GlobalTheory.TrueGeo.Model Y) (Δ : Y.Dv) (t : Y.X → Y.Fnˣ) (V : M.X.Opens) (d n : ℕ) (s : Fin n → Y.Fn) (z : M.X), (∀ y, Δ.IsEqn y (t y)) → z ∈ V → Generates M t V d s → ∃ (N : GlobalTheory.TrueGeo.Model Y) (π : N.X ⟶ M.X) (V' : M.X.Opens), N.j ≫ π = M.j ∧ π ≫ M.p = N.p ∧ z ∈ V' ∧ V' ≤ V ∧ ∀ x ∈ π ⁻¹ᵁ V', ∃ (i : Fin n) (W : N.X.Opens), x ∈ W ∧ s i ≠ 0 ∧ ∀ k, ∃ g : Γ(N.X, W), ∀ h : genericPoint Y.X ∈ N.j ⁻¹ᵁ W, fnOf (N.j ⁻¹ᵁ W) h (N.j.app W g) * s i = s k := by
  first | exact @GlobalTheory.InvertIdeal.main | exact GlobalTheory.InvertIdeal.main | (intros; apply GlobalTheory.InvertIdeal.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalModelOverProjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_model_over_projective : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (O : Type) [CommRing O] (ε : 𝓞 F ≃+* O) (X : Scheme.{0}) (sX : X ⟶ Sp O) (ρ : Y.X ⟶ X), IsProjOver sX → ρ ≫ sX ≫ spMap ε.toRingHom = Y.str ≫ spMap (algebraMap (𝓞 F) F) → X.IsSeparated ∧ IsLocallyNoetherian X ∧ ∃ (M : GlobalTheory.TrueGeo.Model Y) (ρ' : M.X ⟶ X), IsNormalScheme M.X ∧ M.j ≫ ρ' = ρ := by
  first | exact @GlobalTheory.ModelOver.exists_normal_model | exact GlobalTheory.ModelOver.exists_normal_model | (intros; apply GlobalTheory.ModelOver.exists_normal_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtAt
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitGen

def ExtAt {X : Scheme.{0}} (L : LB X) {R : Type} [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ X)
    (e : LB.Gen (L.pull x)) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
    ∀ (ψ : R →+* V) (gam : FractionRing R →+* FractionRing V),
    (∀ r, gam (algebraMap R _ r) = algebraMap V _ (ψ r)) →
    ∀ χ : Sp V ⟶ X, spMap gam ≫ x = Out.jK V ≫ χ → ∃ e' : LB.Gen (L.pull χ), e'.IsGen ∧
      ∀ z J, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good L z J →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (L := L) (φ := fun _ : PUnit => x) (ε := fun _ => 1) e (spMap gam) z J =
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (L := L) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) e' (Out.jK V) z J

end GlobalTheory.TraitGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelAddStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fromModel_add' : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (Δ Δ' : Y.Dv) (t t' : Y.X → Y.Fnˣ) (φ φ' : PtFn Y), (∀ y, Δ.IsEqn y (t y)) → (∀ y, Δ'.IsEqn y (t' y)) → FromModel Y Δ t φ → FromModel Y Δ' t' φ' → FromModel Y (Δ + Δ') (fun y => t y * t' y) (fun v e y => φ v e y + φ' v e y) := by
  first | exact @GlobalTheory.LineNorm.Add.fromModel_add | exact GlobalTheory.LineNorm.Add.fromModel_add | (intros; apply GlobalTheory.LineNorm.Add.fromModel_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameOrbitIsotropicVectorShortStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicFrameOrbit_isotropic_vector_short : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N), IsOrbit X T M γ x → ((γ : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 → γ ≠ 1 → ∃ (ξ : Fin N → E) (c : ℝ), X.IsIso ξ ∧ 0 < c ∧ ∀ w : ℂ, T + 1 < w.im → ∀ τ, c * (w.im - T) ≤ X.tt ξ (x w) τ := by
  first | exact @GlobalTheory.orbit_unipotent_short | exact GlobalTheory.orbit_unipotent_short | (intros; apply GlobalTheory.orbit_unipotent_short <;> assumption)
end

