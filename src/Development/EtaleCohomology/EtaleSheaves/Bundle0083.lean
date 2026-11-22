import Development.EtaleCohomology.EtaleSheaves.Bundle0080
import Development.EtaleCohomology.EtaleSheaves.Bundle0081
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Development.EtaleCohomology.EtaleSheaves.Bundle0066

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSpreadSeparatedPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf

namespace LateralTheory.E.LeafSpreadSeparatedPf

theorem incl_comp {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R S R' : Subalgebra k Ω} (h : R ≤ S)
    (h' : S ≤ R') : incl h' ≫ incl h = incl (h.trans h') := by
  rw [← Spec.map_comp]; rfl

theorem sep_of_stage {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R S R' : Subalgebra k Ω} (h : R ≤ S)
    (hS : S ≤ R') (hR : R ≤ R') {D E : Scheme.{0}} (q : D ⟶ Sp R) [IsSeparated (pullback.snd q (incl h))]
    (q' : E ⟶ Sp R') (r : E ⟶ D) (hE : IsPullback r q' q (incl hR)) : IsSeparated q' := by
  have hc : r ≫ q = (q' ≫ incl hS) ≫ incl h := by
    rw [Category.assoc, incl_comp]; exact hE.w
  have outer : IsPullback (pullback.lift r (q' ≫ incl hS) hc ≫ pullback.fst q (incl h)) q' q
      (incl hS ≫ incl h) := by
    rw [pullback.lift_fst, incl_comp]; exact hE
  have sq := IsPullback.of_right outer (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (incl h))
  exact MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance

def BC {X Y Z T : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (p : X ⟶ Z) (w : f ≫ g = p) (t : T ⟶ Z) :
    pullback p t ⟶ pullback g t :=
  pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by simp [w]) (by simp)

def LeafClosedImmSpread : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Sp R),
    (LocallyOfFinitePresentation g ∧ QuasiCompact g ∧ QuasiSeparated g) →
    (LocallyOfFinitePresentation (f ≫ g) ∧ QuasiCompact (f ≫ g) ∧ QuasiSeparated (f ≫ g)) →
    IsClosedImmersion (BC f g (f ≫ g) rfl (toR R)) →
    ∃ (S : Subalgebra k Ω) (h : R ≤ S), S.FG ∧ IsClosedImmersion (BC f g (f ≫ g) rfl (incl h))

def LeafDiagBC : Prop := ∀ {D Z T : Scheme.{0}} (q : D ⟶ Z) (t : T ⟶ Z),
    IsSeparated (pullback.snd q t) ↔ IsClosedImmersion (BC (pullback.diagonal q) (pullback.snd q q ≫ q) q (by simp) t)

theorem ci_congr {X Y Z T : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (p : X ⟶ Z) (w : f ≫ g = p) (t : T ⟶ Z) :
    IsClosedImmersion (BC f g p w t) ↔ IsClosedImmersion (BC f g (f ≫ g) rfl t) := by
  subst w; rfl

theorem separated_base_change_iff_diagonal_closed_immersion_holds : LeafDiagBC := by
  intro D Z T q t
  have e1 : pullback.snd q t = (pullbackSymmetry q t).hom ≫ pullback.fst t q := by simp
  have e2 : IsSeparated (pullback.snd q t) ↔ IsSeparated (pullback.fst t q) := by
    rw [e1]; exact MorphismProperty.cancel_left_of_respectsIso (P := @IsSeparated) _ _
  rw [e2]
  have e3 : IsSeparated (pullback.fst t q) ↔ IsClosedImmersion (pullback.diagonal (pullback.fst t q)) :=
    ⟨fun h => h.isClosedImmersion_diagonal, fun h => ⟨h⟩⟩
  rw [e3, diagonal_pullback_fst, MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion),
    MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)]
  have : ((Over.pullback t).map (Over.homMk (pullback.diagonal q) : Over.mk q ⟶ Over.mk (pullback.snd q q ≫ q))).left
      = BC (pullback.diagonal q) (pullback.snd q q ≫ q) q (by simp) t := by
    apply pullback.hom_ext <;> simp only [BC, pullback.map, Category.comp_id] <;> rfl
  rw [this]

theorem of_two (hC : LeafClosedImmSpread) (hD : LeafDiagBC) :
    LateralTheory.E.LeafSpreadProperPf.LeafSpreadSeparated := by
  intro k _ Ω _ _ R hR C D c q v hf hc hv
  obtain ⟨h1, h2, h3⟩ := hf
  have s0 : IsSeparated (pullback.snd q (toR R)) := by
    rw [← hv.isoPullback_inv_snd]; infer_instance
  have ci := (ci_congr _ _ _ _ _).1 ((hD q (toR R)).1 s0)
  have hfg : pullback.diagonal q ≫ pullback.snd q q ≫ q = q := by simp
  obtain ⟨S, h, hS, ci'⟩ := hC k Ω R hR (pullback.diagonal q) (pullback.snd q q ≫ q)
    ⟨inferInstance, inferInstance, inferInstance⟩ (by rw [hfg]; exact ⟨h1, h2, h3⟩) ci
  have := (hD q (incl h)).2 ((ci_congr _ _ _ (by simp) _).2 ci')
  exact ⟨S, h, hS, fun R' hS' hRR E q' r hE => sep_of_stage h hS' hRR q q' r hE⟩

end LateralTheory.E.LeafSpreadSeparatedPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSpreadSmoothAffSmPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf LateralTheory.E.LeafPropsDescendPf.Split LateralTheory.E.LeafSpreadSmoothPf Topology

namespace LateralTheory.E.LeafSpreadSmoothAffSmPf

def LeafGenericSmooth : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D), IsAffine D →
    ∀ [LocallyOfFinitePresentation q], SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∀ x : D, q.base x ∈ Set.range (toR R).base → x ∈ q.smoothLocus

def LeafSpreadOpen : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {D : Scheme.{0}} (q : D ⟶ Sp R), IsAffine D → LocallyOfFinitePresentation q →
    ∀ U : D.Opens, (∀ x : D, q.base x ∈ Set.range (toR R).base → x ∈ U) →
    ∃ (S : Subalgebra k Ω) (h : R ≤ S), S.FG ∧
      ∀ y : (pullback q (incl h) : Scheme.{0}), (pullback.fst q (incl h)).base y ∈ U

def LeafSmoothOfLocus : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {R S : Subalgebra k Ω}
    (h : R ≤ S) {D : Scheme.{0}} (q : D ⟶ Sp R) [LocallyOfFinitePresentation q],
    (∀ y : (pullback q (incl h) : Scheme.{0}), (pullback.fst q (incl h)).base y ∈ q.smoothLocus) →
    Smooth (pullback.snd q (incl h))

theorem leafSmoothOfLocus : LeafSmoothOfLocus := by
  intro k _ Ω _ _ R S h D q _ hy
  have hU : Smooth (q.smoothLocus.ι ≫ q) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact Scheme.Opens.ι_preimage_self _
  have sq := (isPullback_morphismRestrict (pullback.fst q (incl h)) q.smoothLocus).paste_vert
    (IsPullback.of_hasPullback q (incl h))
  have hs : Smooth (((pullback.fst q (incl h)) ⁻¹ᵁ q.smoothLocus).ι ≫ pullback.snd q (incl h)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq hU
  have hL : IsZariskiLocalAtSource @Smooth := HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
    (fun _ : Unit => (pullback.fst q (incl h)) ⁻¹ᵁ q.smoothLocus) ?_ (fun _ => hs)
  exact top_le_iff.mp fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨(), hy y⟩

def LeafClosedConstructible : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {D : Scheme.{0}} (q : D ⟶ Sp R), IsAffine D → LocallyOfFinitePresentation q →
    ∀ Z : Set D, IsClosed Z → IsConstructible Z

def LeafAvoidConstructible : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ T : Set (Sp R), IsConstructible T → (∀ z ∈ T, z ∉ Set.range (toR R).base) →
    ∃ (S : Subalgebra k Ω) (h : R ≤ S), S.FG ∧ ∀ w : (Sp S : Scheme.{0}), (incl h).base w ∉ T

theorem leafClosedConstructible : LeafClosedConstructible := by
  intro k _ Ω _ _ R hR D q hD hlfp Z hZ
  have : IsNoetherianRing R := isNoetherianRing_of_fg hR
  have : IsNoetherianRing (CommRingCat.of R) := this
  have : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherian D := ⟨⟩
  have hc : IsConstructible (Zᶜ) := (TopologicalSpace.NoetherianSpace.isCompact _).isConstructible hZ.isOpen_compl
  simpa using hc

def LeafGenericNbhd : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ T : Set (Sp R), IsConstructible T → (∀ z ∈ T, z ∉ Set.range (toR R).base) →
    ∃ f : R, f ≠ 0 ∧ ∀ z ∈ T, f ∈ (show PrimeSpectrum R from z).asIdeal

theorem leafInvert (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (hR : R.FG)
    (f : R) (hf : f ≠ 0) : ∃ (S : Subalgebra k Ω) (h : R ≤ S), S.FG ∧
      ∀ w : (Sp S : Scheme.{0}), f ∉ (show PrimeSpectrum R from (incl h).base w).asIdeal := by
  have hf0 : (f : Ω) ≠ 0 := fun e => hf (Subtype.ext e)
  refine ⟨R ⊔ Algebra.adjoin k {(f : Ω)⁻¹}, le_sup_left, hR.sup ⟨{(f : Ω)⁻¹}, by simp⟩, fun w hw => ?_⟩
  have hi : (f : Ω)⁻¹ ∈ R ⊔ Algebra.adjoin k {(f : Ω)⁻¹} :=
    (le_sup_right : Algebra.adjoin k {(f : Ω)⁻¹} ≤ _) (Algebra.subset_adjoin rfl)
  have hu : IsUnit (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ Algebra.adjoin k {(f : Ω)⁻¹}) f) := by
    refine IsUnit.of_mul_eq_one (⟨_, hi⟩ : ↥(R ⊔ Algebra.adjoin k {(f : Ω)⁻¹})) ?_
    apply Subtype.ext
    simp [hf0]
  have hw' : Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ Algebra.adjoin k {(f : Ω)⁻¹}) f ∈ w.asIdeal := hw
  exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hw' hu)

theorem leafGenericNbhd : LeafGenericNbhd := by
  classical
  intro k _ Ω _ _ R hR T hT hgen
  let η : PrimeSpectrum R := ⟨⊥, Ideal.bot_prime⟩
  have hη : (show Sp R from η) ∈ Set.range (toR R).base := by
    refine ⟨(show Sp Ω from (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum Ω)), ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R Ω) ⊥ = ⊥
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective
  obtain ⟨C, hC⟩ := (PrimeSpectrum.exists_constructibleSetData_iff (R := R) (s := T)).mpr hT
  have hne : ∀ c ∈ C, ∃ a : R, a ≠ 0 ∧ ∀ z ∈ c.toSet, a ∈ z.asIdeal := by
    intro c hc
    by_cases h0 : c.f = 0
    · refine ⟨1, one_ne_zero, fun z hz => absurd ?_ hz.2⟩
      simp [h0, PrimeSpectrum.mem_zeroLocus]
    · by_cases hg : ∃ i, c.g i ≠ 0
      · obtain ⟨i, hi⟩ := hg
        exact ⟨c.g i, hi, fun z hz => hz.1 ⟨i, rfl⟩⟩
      · simp only [not_exists, not_not] at hg
        exfalso
        have hηc : η ∈ c.toSet := by
          refine ⟨?_, ?_⟩
          · rintro _ ⟨i, rfl⟩
            simp [η, hg i]
          · intro h
            exact h0 (by simpa [η, PrimeSpectrum.mem_zeroLocus] using h)
        have hηT : η ∈ T := by
          rw [← hC]
          simp only [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion]
          exact Set.mem_iUnion₂.mpr ⟨c, hc, hηc⟩
        exact hgen _ hηT hη
  choose! a ha using hne
  refine ⟨∏ c ∈ C, a c, Finset.prod_ne_zero_iff.mpr (fun c hc => (ha c hc).1), fun z hz => ?_⟩
  rw [← hC] at hz
  simp only [PrimeSpectrum.ConstructibleSetData.toSet] at hz
  obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp hz
  rw [← Finset.mul_prod_erase C a hc]
  exact Ideal.mul_mem_right _ _ ((ha c hc).2 z hzc)

theorem leafAvoidConstructible_of (hN : LeafGenericNbhd) : LeafAvoidConstructible := by
  intro k _ Ω _ _ R hR T hT hgen
  obtain ⟨f, hf, hfT⟩ := hN k Ω R hR T hT hgen
  obtain ⟨S, h, hS, hw⟩ := leafInvert k Ω R hR f hf
  exact ⟨S, h, hS, fun w hwT => hw w (hfT _ hwT)⟩

theorem leafSpreadOpen_of (hC : LeafClosedConstructible) (hA : LeafAvoidConstructible) : LeafSpreadOpen := by
  intro k _ Ω _ _ R hR D q hD hlfp U hU
  have : QuasiCompact q := inferInstance
  have hT := q.isConstructible_image (hC k Ω R hR q hD hlfp ((U : Set D)ᶜ) U.isOpen.isClosed_compl)
  obtain ⟨S, h, hS, hw⟩ := hA k Ω R hR _ hT (by
    rintro z ⟨x, hx, rfl⟩ hz
    exact hx (hU x hz))
  refine ⟨S, h, hS, fun y => ?_⟩
  by_contra hy
  apply hw ((pullback.snd q (incl h)).base y)
  refine ⟨(pullback.fst q (incl h)).base y, hy, ?_⟩
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]

theorem LeafSpreadSmoothAffSm_of_cut (hG : LeafGenericSmooth) (hO : LeafSpreadOpen) (hL : LeafSmoothOfLocus) :
    LeafSpreadSmoothAffSm := by
  intro k _ Ω _ _ R hR C D c q v hD hlfp hs hv
  obtain ⟨S, h, hS, hy⟩ := hO k Ω R hR q hD hlfp q.smoothLocus (hG k Ω R hR c q v hD hs hv)
  exact ⟨S, h, hS, hL k Ω h q hy⟩

def LeafStalkDescend : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D), IsAffine D →
    ∀ [LocallyOfFinitePresentation q], SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) → ∀ y : C, v.base y ∈ q.smoothLocus

theorem leafGenericSmooth_of (hS : LeafStalkDescend) : LeafGenericSmooth := by
  intro k _ Ω _ _ R hR C D c q v hD _ hs hv x ⟨w, hw⟩
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback x w hw.symm
  have := hS k Ω R hR c q v hD hs hv (hv.isoPullback.inv.base z)
  rwa [← Scheme.Hom.comp_apply, hv.isoPullback_inv_fst, hz1] at this

theorem LeafSpreadSmoothAffSm_of (hD : LeafStalkDescend) :
    LeafSpreadSmoothAffSm :=
  LeafSpreadSmoothAffSm_of_cut (leafGenericSmooth_of hD) (leafSpreadOpen_of leafClosedConstructible (leafAvoidConstructible_of leafGenericNbhd))
    leafSmoothOfLocus

end LateralTheory.E.LeafSpreadSmoothAffSmPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PowQEqOne
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocGenPfA

theorem pow_q_eq_one {q : ℕ} {B : Type} [CommRing B] (x : B)
    (hx : Polynomial.aeval x (Polynomial.cyclotomic q ℤ) = 0) : x ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (Polynomial.aeval x) hp
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, hx, zero_mul] at this
  exact sub_eq_zero.1 this

theorem local_eq {q : ℕ} [NeZero q] {B : Type} [CommRing B] [IsLocalRing B] (hq : IsUnit (q : B)) {x y : B}
    (hx : x ^ q = 1) (hy : y ^ q = 1) (hr : IsLocalRing.residue B x = IsLocalRing.residue B y) : x = y := by
  have hg := geom_sum₂_mul x y q
  rw [hx, hy, sub_self] at hg
  have hyu : IsUnit y := IsUnit.of_pow_eq_one hy (NeZero.ne q)
  have hres : IsLocalRing.residue B (∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)) =
      IsLocalRing.residue B ((q : B) * y ^ (q - 1)) := by
    rw [map_sum, map_mul, map_pow, map_natCast]
    rw [Finset.sum_congr rfl (g := fun _ => IsLocalRing.residue B y ^ (q - 1))]
    · simp
    · intro i hi
      rw [map_mul, map_pow, map_pow, hr, ← pow_add]
      congr 1; have := Finset.mem_range.1 hi; omega
  have hu' : IsUnit (∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)) := by
    have h1 : IsUnit (IsLocalRing.residue B ((q : B) * y ^ (q - 1))) := (hq.mul (hyu.pow _)).map _
    rw [← hres] at h1
    exact (isUnit_map_iff (IsLocalRing.residue B) _).1 h1
  exact sub_eq_zero.1 ((IsUnit.mul_right_eq_zero hu').1 hg)

theorem res_root {q : ℕ} {B : Type} [CommRing B] [IsLocalRing B] (z : B)
    (hz : Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0) :
    Polynomial.IsRoot (Polynomial.cyclotomic q (IsLocalRing.ResidueField B)) (IsLocalRing.residue B z) := by
  have h := Polynomial.aeval_algHom_apply (IsLocalRing.residue B).toIntAlgHom z (Polynomial.cyclotomic q ℤ)
  rw [hz, map_zero] at h
  rw [← Polynomial.map_cyclotomic_int, Polynomial.IsRoot.def, Polynomial.eval_map]
  rw [Polynomial.aeval_def, algebraMap_int_eq] at h
  exact h

theorem local_pow {q : ℕ} [NeZero q] {B : Type} [CommRing B] [IsLocalRing B] (hq : IsUnit (q : B)) {ζ ξ : B}
    (hζ : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) (hξ : Polynomial.aeval ξ (Polynomial.cyclotomic q ℤ) = 0) :
    ∃ a : (ZMod q)ˣ, ξ = ζ ^ (a : ZMod q).val := by
  have : NeZero ((q : ℕ) : IsLocalRing.ResidueField B) :=
    ⟨by simpa [map_natCast] using (hq.map (IsLocalRing.residue B)).ne_zero⟩
  have root : ∀ z : B, Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 →
      IsPrimitiveRoot (IsLocalRing.residue B z) q := fun z hz =>
    Polynomial.isRoot_cyclotomic_iff.1 (res_root z hz)
  obtain ⟨i, hi, hpow⟩ := (root ζ hζ).eq_pow_of_pow_eq_one ((root ξ hξ).pow_eq_one)
  have hc : i.Coprime q :=
    ((root ζ hζ).pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (hpow ▸ root ξ hξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  have hval : ((ZMod.unitOfCoprime i hc : (ZMod q)ˣ) : ZMod q).val = i := by
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  rw [hval]
  refine local_eq hq (pow_q_eq_one ξ hξ) ?_ ?_
  · rw [← pow_mul, mul_comm, pow_mul, pow_q_eq_one ζ hζ, one_pow]
  · rw [map_pow]; exact hpow.symm

end LateralTheory.E.LeafTw0LocGenPfA
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SpreadingOutQuasiFiniteness
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.SpreadingOutQuasiFiniteness

def LeafSpreadSmooth1 : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D),
    (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) → SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ D), IsPullback r q' q (incl hR) → SmoothOfRelativeDimension 1 q'

def LeafSpreadLQFMap : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {CA CB A B : Scheme.{0}} (cB : CB ⟶ Sp Ω) (γ : CA ⟶ CB) (qB : B ⟶ Sp R) (g : A ⟶ B) (vA : CA ⟶ A)
    (vB : CB ⟶ B), (LocallyOfFinitePresentation qB ∧ QuasiCompact qB ∧ QuasiSeparated qB) →
    (LocallyOfFinitePresentation (g ≫ qB) ∧ QuasiCompact (g ≫ qB) ∧ QuasiSeparated (g ≫ qB)) →
    IsPullback vB cB qB (toR R) → IsPullback vA (γ ≫ cB) (g ≫ qB) (toR R) → γ ≫ vB = vA ≫ g →
    LocallyQuasiFinite γ →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (EA EB : Scheme.{0})
      (qB' : EB ⟶ Sp R') (h : EA ⟶ EB) (rA : EA ⟶ A) (rB : EB ⟶ B), IsPullback rB qB' qB (incl hR) →
      IsPullback rA (h ≫ qB') (g ≫ qB) (incl hR) → h ≫ rB = rA ≫ g → LocallyQuasiFinite h

def LeafSpreadLQFGraph : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type)
    [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG → ∀ {C0 D0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (q : D0 ⟶ Sp R)
    (v0 : C0 ⟶ D0) (f : D0 ⟶ X) (e : C0 ⟶ X) (he : e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hf : f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R))),
    (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) → IsPullback v0 c0 q (toR R) → v0 ≫ f = e →
    LocallyQuasiFinite (pullback.lift c0 e he.symm) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E0 : Scheme.{0})
      (q' : E0 ⟶ Sp R') (r : E0 ⟶ D0), IsPullback r q' q (incl hR) →
      ∀ (hf' : (r ≫ f) ≫ p = q' ≫ Spec.map (CommRingCat.ofHom (algebraMap k R'))),
        LocallyQuasiFinite (pullback.lift q' (r ≫ f) hf'.symm)

def LeafBaseChangePreR : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R R' : Subalgebra k Ω)
    (hR : R ≤ R') {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}}
    (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
    LateralTheory.E.LeafDescendChainPf.PreChain R c0 γ1 γ2 q d1 d2 v0 v1 v2 →
    ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1) (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1)
      (w2 : C2 ⟶ E2) (r0 : E0 ⟶ D0) (r1 : E1 ⟶ D1) (r2 : E2 ⟶ D2),
      (IsPullback w0 c0 q' (toR R') ∧ IsPullback w1 (γ1 ≫ c0) (e1 ≫ q') (toR R') ∧
        IsPullback w2 (γ2 ≫ γ1 ≫ c0) (e2 ≫ e1 ≫ q') (toR R') ∧ γ1 ≫ w0 = w1 ≫ e1 ∧ γ2 ≫ w1 = w2 ≫ e2) ∧
      IsPullback r0 q' q (incl hR) ∧ IsPullback r1 (e1 ≫ q') (d1 ≫ q) (incl hR) ∧
      IsPullback r2 (e2 ≫ e1 ≫ q') (d2 ≫ d1 ≫ q) (incl hR) ∧
      w0 ≫ r0 = v0 ∧ e1 ≫ r0 = r1 ≫ d1 ∧ e2 ≫ r1 = r2 ≫ d2

theorem incl_toK {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R') :
    incl hR ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k R')) := by
  rw [← Spec.map_comp]; rfl

theorem LeafSpreadQF_of (hSep : LateralTheory.E.LeafSpreadProperPf.LeafSpreadSeparated) (hSm : LeafSpreadSmooth1)
    (hG : LeafSpreadLQFGraph) (hM : LeafSpreadLQFMap) (hB : LeafBaseChangePreR) :
    LateralTheory.E.QuasiFiniteDescent.LeafSpreadQF := by
  intro k _ X p _ Ω _ _ R hR C0 C1 C2 c0 γ1 γ2 e he hc0 h1 h2 qf0 qf1 qf2 D0 D1 D2 q d1 d2 f v0 v1 v2 hf hpre hve
  obtain ⟨f0, f1, f2, p0, p1, p2, m1, m2⟩ := id hpre
  obtain ⟨S0, a0, g0, H0⟩ := hSep k Ω R hR c0 q v0 f0 hc0.2.1.toIsSeparated p0
  obtain ⟨S1, a1, g1, H1⟩ := hSep k Ω R hR (γ1 ≫ c0) (d1 ≫ q) v1 f1 h1.2.1.toIsSeparated p1
  obtain ⟨S2, a2, g2, H2⟩ := hSep k Ω R hR (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) v2 f2 h2.2.1.toIsSeparated p2
  obtain ⟨T0, b0, k0, K0⟩ := hSm k Ω R hR c0 q v0 f0 hc0.2.2 p0
  obtain ⟨T1, b1, k1, K1⟩ := hSm k Ω R hR (γ1 ≫ c0) (d1 ≫ q) v1 f1 h1.2.2 p1
  obtain ⟨T2, b2, k2, K2⟩ := hSm k Ω R hR (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) v2 f2 h2.2.2 p2
  obtain ⟨G, aG, gG, HG⟩ := hG k p Ω R hR c0 q v0 f e he hf f0 p0 hve qf0
  obtain ⟨M1, aM1, gM1, HM1⟩ := hM k Ω R hR c0 γ1 q d1 v1 v0 f0 f1 p0 p1 m1 qf1
  obtain ⟨M2, aM2, gM2, HM2⟩ := hM k Ω R hR (γ1 ≫ c0) γ2 (d1 ≫ q) d2 v2 v1 f1 f2 p1 p2 m2 qf2
  let T := S0 ⊔ S1 ⊔ S2 ⊔ T0 ⊔ T1 ⊔ T2 ⊔ G ⊔ M1 ⊔ M2
  have gT : T.FG := ((((((((g0.sup g1).sup g2).sup k0).sup k1).sup k2).sup gG).sup gM1).sup gM2)
  have lS0 : S0 ≤ T := (((((((le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have literatureStatementsS1 : S1 ≤ T := (((((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have logSupBoundLevelFree : S2 ≤ T := ((((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lT0 : T0 ≤ T := (((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lT1 : T1 ≤ T := ((((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lT2 : T2 ≤ T := (((le_sup_right).trans le_sup_left).trans le_sup_left).trans le_sup_left
  have lG : G ≤ T := ((le_sup_right).trans le_sup_left).trans le_sup_left
  have familyMassFirstBound : M1 ≤ T := (le_sup_right).trans le_sup_left
  have familyMassSecondBound : M2 ≤ T := le_sup_right
  have hRT : R ≤ T := a0.trans lS0
  obtain ⟨E0, E1, E2, q', e1, e2, w0, w1, w2, r0, r1, r2, ⟨P0, P1, P2, c1, c2⟩, Q0, Q1, Q2, n0, n1, n2⟩ :=
    hB k Ω R T hRT c0 γ1 γ2 q d1 d2 v0 v1 v2 hpre
  have hf' : (r0 ≫ f) ≫ p = q' ≫ Spec.map (CommRingCat.ofHom (algebraMap k T)) := by
    rw [Category.assoc, hf, ← Category.assoc, Q0.w, Category.assoc, incl_toK]
  haveI := f0.2.1; haveI := f1.2.1; haveI := f2.2.1
  refine ⟨T, gT, E0, E1, E2, q', e1, e2, r0 ≫ f, w0, w1, w2, hf', ?_⟩
  exact ⟨H0 T lS0 hRT E0 q' r0 Q0, MorphismProperty.of_isPullback (P := @QuasiCompact) Q0 inferInstance,
    K0 T lT0 hRT E0 q' r0 Q0,
    H1 T literatureStatementsS1 hRT E1 (e1 ≫ q') r1 Q1, MorphismProperty.of_isPullback (P := @QuasiCompact) Q1 inferInstance,
    K1 T lT1 hRT E1 (e1 ≫ q') r1 Q1,
    H2 T logSupBoundLevelFree hRT E2 (e2 ≫ e1 ≫ q') r2 Q2, MorphismProperty.of_isPullback (P := @QuasiCompact) Q2 inferInstance,
    K2 T lT2 hRT E2 (e2 ≫ e1 ≫ q') r2 Q2,
    HG T lG hRT E0 q' r0 Q0 hf', HM1 T familyMassFirstBound hRT E1 E0 q' e1 r1 r0 Q0 Q1 n1,
    HM2 T familyMassSecondBound hRT E2 E1 (e1 ≫ q') e2 r2 r1 Q1 Q2 n2, P0, P1, P2, c1, c2,
    by rw [← Category.assoc, n0, hve]⟩

end LateralTheory.E.SpreadingOutQuasiFiniteness

end
end

