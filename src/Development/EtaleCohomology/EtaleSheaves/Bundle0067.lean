import Development.EtaleCohomology.EtaleSheaves.Bundle0058
import Development.EtaleCohomology.EtaleSheaves.Bundle0054
import Development.EtaleCohomology.EtaleSheaves.Bundle0059
import Development.EtaleCohomology.EtaleSheaves.Bundle0039
import Development.EtaleCohomology.EtaleSheaves.Bundle0056

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafVanWPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafVanWPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafVan0Pf

section Cone
variable {C : Type*} [Category C] [Preadditive C] {K L M : CochainComplex C ℤ} (φ : K ⟶ L) [HomologicalComplex.HasHomotopyCofiber φ]

theorem desc_δ {n m : ℤ} (α : Cochain K M m) (β : Cochain L M n) (h : m + 1 = n) (n' : ℤ) (hn' : n + 1 = n') :
    δ n n' (mappingCone.descCochain φ α β h) =
      mappingCone.descCochain φ (δ m n α + n'.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (δ n n' β) hn' := by
  rw [mappingCone.δ_descCochain φ α β h n' hn']; rfl

theorem desc_eq_zero {n m : ℤ} {α : Cochain K M m} {β : Cochain L M n} {h : m + 1 = n}
    (H : mappingCone.descCochain φ α β h = 0) : α = 0 ∧ β = 0 := by
  constructor
  · have := mappingCone.inl_descCochain φ α β h
    rw [H, Cochain.comp_zero] at this; exact this.symm
  · have := mappingCone.inr_descCochain φ α β h
    rw [H, Cochain.comp_zero] at this; exact this.symm

theorem units_mul_self' (u : ℤˣ) : u * u = 1 := Int.units_mul_self u

theorem cone_zero
    (hinj : ∀ (n : ℤ) (x : Cocycle L M n),
      CohomologyClass.mk (zcomp (Cocycle.ofHom φ) x (zero_add n)) = 0 → CohomologyClass.mk x = 0)
    (hsurj : ∀ (n : ℤ) (y : Cocycle K M n), ∃ x : Cocycle L M n,
      CohomologyClass.mk (zcomp (Cocycle.ofHom φ) x (zero_add n)) = CohomologyClass.mk y)
    (n : ℤ) (z : Cocycle (mappingCone φ) M n) : CohomologyClass.mk z = 0 := by
  set a : Cochain K M (n - 1) := (mappingCone.inl φ).comp z.1 (by omega) with ha
  set b : Cochain L M n := (Cochain.ofHom (mappingCone.inr φ)).comp z.1 (zero_add n) with hb
  have hz : z.1 = mappingCone.descCochain φ a b (by omega) := by
    rw [mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
    simp [ha, hb]
  have h0 := Cocycle.δ_eq_zero z (n + 1)
  rw [hz, desc_δ φ a b _ (n + 1) rfl] at h0
  obtain ⟨h1, h2⟩ := desc_eq_zero φ h0
  have hda : δ (n - 1) n a = -((n + 1).negOnePow • (Cochain.ofHom φ).comp b (zero_add n)) := eq_neg_of_add_eq_zero_left h1
  let bc : Cocycle L M n := Cocycle.mk b (n + 1) rfl h2
  have hb0 : CohomologyClass.mk bc = 0 := by
    apply hinj
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨-((n + 1).negOnePow • a), ?_⟩
    rw [δ_neg, δ_units_smul, hda, smul_neg, neg_neg, smul_smul, units_mul_self', one_smul]
    simp [zcomp, bc]
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hb0
  obtain ⟨γ, hγ⟩ := hb0
  change δ (n - 1) n γ = b at hγ
  set a' : Cochain K M (n - 1) := a - n.negOnePow • (Cochain.ofHom φ).comp γ (zero_add _) with ha'
  let w : Cochain (mappingCone φ) M (n - 1) := mappingCone.descCochain φ (0 : Cochain K M (n - 1 - 1)) γ (by omega)
  have hw : δ (n - 1) n w = mappingCone.descCochain φ (n.negOnePow • (Cochain.ofHom φ).comp γ (zero_add _)) b (by omega) := by
    simp only [w]; rw [desc_δ φ _ γ _ n (by omega), hγ, δ_zero, zero_add]
  have hda' : δ (n - 1) n a' = 0 := by
    have e : mappingCone.descCochain φ a' (0 : Cochain L M n) (by omega) = z.1 - δ (n - 1) n w := by
      rw [hz, hw, mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
      simp [ha']
    have e2 := congrArg (δ n (n + 1)) e
    rw [δ_sub, δ_δ, sub_zero, Cocycle.δ_eq_zero, desc_δ φ _ _ _ (n + 1) rfl] at e2
    have := (desc_eq_zero φ e2).1
    simpa using this
  obtain ⟨x, hx⟩ := hsurj (n - 1) (Cocycle.mk a' n (by omega) hda')
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1 - 1) (by omega)] at hx
  obtain ⟨γ', hγ'⟩ := hx
  change δ (n - 1 - 1) (n - 1) γ' = (Cochain.ofHom φ).comp x.1 (zero_add _) - a' at hγ'
  have hdx := Cocycle.δ_eq_zero x n
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨w + n.negOnePow • mappingCone.descCochain φ (0 : Cochain K M (n - 1 - 1)) x.1 (by omega) -
    mappingCone.descCochain φ γ' (0 : Cochain L M (n - 1)) (by omega), ?_⟩
  rw [δ_sub, δ_add, δ_units_smul, hw, desc_δ φ _ _ _ n (by omega), desc_δ φ _ _ _ n (by omega), hγ', hdx]
  change _ = z.1
  rw [hz, mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
  constructor
  · simp only [mappingCone.inl_descCochain, Cochain.comp_add, Cochain.comp_sub, Cochain.comp_units_smul, δ_zero, zero_add,
      Cochain.comp_zero, smul_zero, add_zero, smul_smul, units_mul_self', one_smul, ha']
    abel
  · simp
end Cone

section Geo
variable {R : Type} [CommRing R] (F : Shv R)

theorem hrel_sub {U E : Spc} (f : U ⟶ E) (h : Eqv R f F) (n : ℤ) : Subsingleton (Hrel R f F n) := by
  have hinj : ∀ (n : ℤ) (x : Cocycle ((chains R).obj E) (res R F) n),
      CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) x (zero_add n)) = 0 → CohomologyClass.mk x = 0 := by
    intro n x hx
    apply (h n).1
    change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) x (zero_add n)) = pull R f F n 0
    rw [map_zero]; exact hx
  have hsurj : ∀ (n : ℤ) (y : Cocycle ((chains R).obj U) (res R F) n), ∃ x : Cocycle ((chains R).obj E) (res R F) n,
      CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) x (zero_add n)) = CohomologyClass.mk y := by
    intro n y
    obtain ⟨c, hc⟩ := (h n).2 (CohomologyClass.mk y)
    obtain ⟨x, rfl⟩ := c.mk_surjective
    exact ⟨x, hc⟩
  refine ⟨fun y y' => ?_⟩
  obtain ⟨z, rfl⟩ := y.mk_surjective
  obtain ⟨z', rfl⟩ := y'.mk_surjective
  change CohomologyClass.mk z = CohomologyClass.mk z'
  rw [cone_zero _ hinj hsurj n z, cone_zero _ hinj hsurj n z']

theorem eqv_of_iso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] : Eqv R (sch.map f) F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (sch.map (inv f)) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  · rw [← pull_comp, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]

theorem eqv_of_square {P Q X Y : Scheme.{0}} (a : P ⟶ X) (f : X ⟶ Y) (h : P ⟶ Q) (c : Q ⟶ Y) (w : a ≫ f = h ≫ c)
    (ha : Eqv R (sch.map a) F) (hh : Eqv R (sch.map h) F) (hc : Eqv R (sch.map c) F) : Eqv R (sch.map f) F := by
  intro n
  have key : ∀ y, pull R (sch.map a) F n (pull R (sch.map f) F n y) = pull R (sch.map h) F n (pull R (sch.map c) F n y) := by
    intro y; rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, w]
  constructor
  · intro y y' e
    apply (hc n).1; apply (hh n).1
    rw [← key, ← key, e]
  · intro x
    obtain ⟨u, hu⟩ := (hh n).2 (pull R (sch.map a) F n x)
    obtain ⟨v, rfl⟩ := (hc n).2 u
    refine ⟨v, (ha n).1 ?_⟩
    rw [key, hu]
end Geo

theorem commGroup_inv_eq_conj_twist_identity {B W S X T : Scheme.{0}} (pA : X ⟶ S) (s : S ⟶ B) (ι : W ⟶ B) [Mono ι] (r : T ⟶ S) (w : T ⟶ W)
    (hw : w ≫ ι = r ≫ s) (hc : (pullback.fst (pullback.fst (pA ≫ s) ι ≫ pA) r ≫ pullback.fst (pA ≫ s) ι) ≫ pA =
      pullback.snd (pullback.fst (pA ≫ s) ι ≫ pA) r ≫ r) :
    IsIso (pullback.lift (pullback.fst (pullback.fst (pA ≫ s) ι ≫ pA) r ≫ pullback.fst (pA ≫ s) ι)
      (pullback.snd (pullback.fst (pA ≫ s) ι ≫ pA) r) hc) := by
  have c1 : pullback.fst pA r ≫ pA ≫ s = (pullback.snd pA r ≫ w) ≫ ι := by
    simp only [Category.assoc, hw]; exact pullback.condition_assoc s
  have c2 : pullback.lift (pullback.fst pA r) (pullback.snd pA r ≫ w) c1 ≫ pullback.fst (pA ≫ s) ι ≫ pA =
      pullback.snd pA r ≫ r := by
    rw [← Category.assoc, pullback.lift_fst, pullback.condition]
  refine ⟨⟨pullback.lift (pullback.lift (pullback.fst pA r) (pullback.snd pA r ≫ w) c1) (pullback.snd pA r) c2, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
      · rw [← cancel_mono ι]
        simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc, hw]
        have e3 : pullback.fst (pA ≫ s) ι ≫ pA ≫ s = pullback.snd (pA ≫ s) ι ≫ ι := pullback.condition
        have e4 := pullback.condition_assoc (f := pullback.fst (pA ≫ s) ι ≫ pA) (g := r) s
        simp only [Category.assoc] at e4
        rw [← e3]
        first | exact e4 | exact e4.symm
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
  · apply pullback.hom_ext
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]

theorem closed_eq {A : Type} [CommRing A] [IsLocalRing A] (x : Sp A) (hx : ∀ z : Sp A, z ⤳ x) :
    x = IsLocalRing.closedPoint A :=
  ((IsLocalRing.specializes_closedPoint x).antisymm (hx _)).eq

theorem LeafVanW_of : LeafVanW := by
  intro hH q _ k _ hq i B W Y b ι _ p hp A _ s hA hx m
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hE2, -⟩ := hH
  obtain ⟨hHen, hsep⟩ := hA
  haveI : IsProper p := hp
  have hqA : IsUnit (q : A) := by
    have := hq.map (Spec.preimage (s ≫ b)).hom
    simpa using this

  obtain ⟨x, hx1, w0, hw0⟩ := hx
  have hxc := closed_eq x hx1
  have hrpt : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) =
      IsLocalRing.closedPoint A := IsLocalRing.comap_closedPoint (IsLocalRing.residue A)
  haveI : Surjective (pullback.fst (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) ι) := by
    constructor
    intro t
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) (g := ι)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) w0 (by
        have := congrArg s hrpt
        rw [← hxc, ← hw0] at this
        exact this)
    exact ⟨z, hz.trans (Subsingleton.elim _ _)⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.fst (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) ι)
  have hw : (inv (pullback.fst (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) ι) ≫ pullback.snd _ _) ≫ ι =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

  have e1 := hE2 q A ⟨hHen, hsep⟩ hqA (pullback.snd p s) i
  have e2 := hE2 q A ⟨hHen, hsep⟩ hqA (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s) i
  have hc : (pullback.fst (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫
      pullback.fst (pullback.snd p s ≫ s) ι) ≫ pullback.snd p s =
      pullback.snd (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) := by
    rw [Category.assoc, pullback.condition]
  haveI := commGroup_inv_eq_conj_twist_identity (pullback.snd p s) s ι _ _ hw hc
  have heqv : Eqv (ZMod q) (sch.map (prS p ι s)) (tw q i) :=
    eqv_of_square _ _ _ _ _ (pullback.lift_fst _ _ _).symm e2 (eqv_of_iso _ (pullback.lift (pullback.fst (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ pullback.fst (pullback.snd p s ≫ s) ι) _ hc)) e1
  exact hrel_sub _ _ heqv m

end LateralTheory.E.LeafVanWPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocPowPf
section
noncomputable section
open Polynomial IsLocalRing

namespace LateralTheory.E.LocPowPf

theorem pow_eq_one_of_aeval {q : ℕ} {A : Type} [CommRing A] (ξ : A) (h : aeval ξ (cyclotomic q ℤ) = 0) : ξ ^ q = 1 := by
  obtain ⟨p, hp⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (aeval ξ) hp
  rw [map_mul, h, zero_mul, map_sub, map_pow, aeval_X, map_one] at this
  exact sub_eq_zero.1 this

theorem prim_res {q : ℕ} {A : Type} [CommRing A] [IsLocalRing A] (ξ : GlobalTheory.EtC.Prim q A) :
    IsPrimitiveRoot (residue A ξ.1) q := by
  have hu : IsUnit ((q : ResidueField A)) := by simpa using ξ.2.1.map (residue A)
  have : NeZero (q : ResidueField A) := ⟨hu.ne_zero⟩
  obtain ⟨x, -, hx⟩ := ξ
  change IsPrimitiveRoot (residue A x) q
  rw [← isRoot_cyclotomic_iff, IsRoot, ← map_cyclotomic_int, eval_map]
  change aeval ((residue A).toIntAlgHom x) (cyclotomic q ℤ) = 0
  rw [aeval_algHom_apply, hx, map_zero]

theorem LocPow_of : LateralTheory.E.AugBijPf.LocPow := by
  intro q A _ _ ξ ζ
  have hq : IsUnit (q : A) := ξ.2.1
  have hz := prim_res ζ
  have hx := prim_res ξ
  have : NeZero q := ⟨by rintro rfl; simp at hq⟩
  obtain ⟨i, hi, he⟩ := hz.eq_pow_of_pow_eq_one hx.pow_eq_one
  have hcop : i.Coprime q := (hz.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (he ▸ hx)
  refine ⟨ZMod.unitOfCoprime i hcop, ?_⟩
  have hval : ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val = i := by
    simp [ZMod.unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  rw [hval]
  set η := ζ.1 ^ i with hη
  have h1 : ξ.1 ^ q = 1 := pow_eq_one_of_aeval ξ.1 ξ.2.2
  have h2 : η ^ q = 1 := by rw [hη, ← pow_mul, mul_comm, pow_mul, pow_eq_one_of_aeval ζ.1 ζ.2.2, one_pow]
  have hres : residue A ξ.1 = residue A η := by rw [hη, map_pow]; exact he.symm
  have hηu : residue A η ≠ 0 := hres ▸ hx.ne_zero (NeZero.ne q)
  have hS : IsUnit (∑ j ∈ Finset.range q, ξ.1 ^ j * η ^ (q - 1 - j)) := by
    rw [← residue_ne_zero_iff_isUnit, map_sum]
    simp only [map_mul, map_pow, hres]
    rw [geom_sum₂_self]
    exact mul_ne_zero (by simpa using (hq.map (residue A)).ne_zero) (pow_ne_zero _ hηu)
  have key := (Commute.all ξ.1 η).geom_sum₂_mul q
  rw [h1, h2, sub_self] at key
  exact sub_eq_zero.1 ((hS.mul_right_eq_zero).1 key)

end LateralTheory.E.LocPowPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocSecPfB
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LocSecPfB

def HomSec : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}),
  ∃ e : ∀ G : Shv R, ((free R).obj (yoneda.obj X) ⟶ G) ≃+ Sec G X,
    ∀ {G G' : Shv R} (φ : G ⟶ G') (f : (free R).obj (yoneda.obj X) ⟶ G), e G' (f ≫ φ) = Sec.map φ (e G f)

def ClassSec : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0})
  (e : ∀ G : Shv R, ((free R).obj (yoneda.obj X) ⟶ G) ≃+ Sec G X),
  (∀ {G G' : Shv R} (φ : G ⟶ G') (f : (free R).obj (yoneda.obj X) ⟶ G), e G' (f ≫ φ) = Sec.map φ (e G f)) →
  ∀ (F : Shv R) (n : ℤ),
  Nonempty (CohomologyClass (LateralTheory.E.LocSecPf.pt R X) (res R F) n ≃+ (LateralTheory.E.LeafLocPf.secCx F X).homology n)

theorem locSecB_of (h1 : HomSec) (h2 : ClassSec) : LateralTheory.E.LocSecPf.LocSecB := by
  intro R _ X F n
  obtain ⟨e, he⟩ := h1 R X
  exact h2 R X e he F n

theorem LocSec_of (h1 : HomSec) (h2 : ClassSec) : LateralTheory.E.LeafLocPf.LocSec :=
  LateralTheory.E.LocSecPf.LocSec_of LateralTheory.E.LocSecPfA.locSecA (locSecB_of h1 h2)

end LateralTheory.E.LocSecPfB
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.MulRightMem
section
noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.LZIdemPowProof

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

theorem mul_left_mem (S : Subalgebra A K) (I : Ideal A) {s y : K} (hs : s ∈ S)
    (hy : y ∈ I • Subalgebra.toSubmodule S) : s * y ∈ I • Subalgebra.toSubmodule S := by
  refine Submodule.smul_induction_on hy (fun r hr n hn => ?_) (fun x y hx hy => ?_)
  · rw [mul_smul_comm]
    exact Submodule.smul_mem_smul hr (S.mul_mem hs hn)
  · rw [mul_add]; exact add_mem hx hy

theorem mul_right_mem (S : Subalgebra A K) (I : Ideal A) {s y : K} (hs : s ∈ S)
    (hy : y ∈ I • Subalgebra.toSubmodule S) : y * s ∈ I • Subalgebra.toSubmodule S := by
  rw [mul_comm]; exact mul_left_mem S I hs hy

theorem mul_mem_mul (S : Subalgebra A K) (I J : Ideal A) {x y : K}
    (hx : x ∈ I • Subalgebra.toSubmodule S) (hy : y ∈ J • Subalgebra.toSubmodule S) :
    x * y ∈ (I * J) • Subalgebra.toSubmodule S := by
  refine Submodule.smul_induction_on hx (fun r hr n hn => ?_) (fun a b ha hb => ?_)
  · rw [smul_mul_assoc, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hr (mul_left_mem S J hn hy)
  · rw [add_mul]; exact add_mem ha hb

theorem lift_pow (S : Subalgebra A K) (x : K) (hx : x ∈ S) (hp : x * x - x ∈ mS S) (n : ℕ) :
    ∃ y ∈ S, y - x ∈ mS S ∧
      y * y - y ∈ (IsLocalRing.maximalIdeal A ^ (2 ^ n)) • Subalgebra.toSubmodule S := by
  induction n with
  | zero => exact ⟨x, hx, by simp, by simpa [mS] using hp⟩
  | succ n ih =>
    obtain ⟨y, hy, hyx, hyy⟩ := ih
    have hle : IsLocalRing.maximalIdeal A ^ (2 ^ n) ≤ IsLocalRing.maximalIdeal A :=
      Ideal.pow_le_self (by positivity)
    have h2y : y + y - 1 ∈ S := S.sub_mem (S.add_mem hy hy) S.one_mem
    have hpS : y * y - y ∈ S := S.sub_mem (S.mul_mem hy hy) hy
    refine ⟨y - (y + y - 1) * (y * y - y), S.sub_mem hy (S.mul_mem h2y hpS), ?_, ?_⟩
    · rw [show y - (y + y - 1) * (y * y - y) - x = (y - x) - (y + y - 1) * (y * y - y) by ring]
      exact sub_mem hyx (Submodule.smul_mono_left hle (mul_left_mem S _ h2y hyy))
    · have h4 : (y * y - y) + (y * y - y) + (y * y - y) + (y * y - y) - 1 - 1 - 1 ∈ S :=
        S.sub_mem (S.sub_mem (S.sub_mem (S.add_mem (S.add_mem (S.add_mem hpS hpS) hpS) hpS)
          S.one_mem) S.one_mem) S.one_mem
      have hsq := mul_mem_mul S _ _ hyy hyy
      rw [← pow_add, ← two_mul, ← pow_succ'] at hsq
      have := mul_right_mem S _ h4 hsq
      convert this using 1
      ring

theorem LZIdemPow_of : LateralTheory.E.LZIdemSumNoetherian.LZIdemPow := by
  intro A _ _ K _ _ B C t hc e f hp k
  obtain ⟨he, hf, hee, hff, hef⟩ := hp
  obtain ⟨b, hb, hbe, hbb⟩ := lift_pow B e he hee (k + 1)
  obtain ⟨c, hcC, hcf, hcc⟩ := lift_pow C f hf hff (k + 1)
  have hBD : B ≤ AdjoinInv B t := fun x hx => Algebra.subset_adjoin (Or.inl hx)
  have hCD : C ≤ AdjoinInv B t := by
    intro x hx; rw [hc.glue]; exact Algebra.subset_adjoin (Or.inl hx)
  have hbD : b ∈ AdjoinInv B t := hBD hb
  have hcD : c ∈ AdjoinInv B t := hCD hcC
  have hmono : ∀ (I : Ideal A) (S : Subalgebra A K), S ≤ AdjoinInv B t → ∀ x,
      x ∈ I • Subalgebra.toSubmodule S → x ∈ I • Subalgebra.toSubmodule (AdjoinInv B t) :=
    fun I S h x hx => Submodule.smul_mono (le_refl I) (fun y hy => h hy) hx
  have hpow : IsLocalRing.maximalIdeal A ^ (2 ^ (k + 1)) ≤ IsLocalRing.maximalIdeal A ^ (k + 1) :=
    Ideal.pow_le_pow_right (Nat.lt_two_pow_self).le
  have hp : b * b - b ∈ (IsLocalRing.maximalIdeal A ^ (k + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) :=
    Submodule.smul_mono_left hpow (hmono _ B hBD _ hbb)
  have hq : c * c - c ∈ (IsLocalRing.maximalIdeal A ^ (k + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) :=
    Submodule.smul_mono_left hpow (hmono _ C hCD _ hcc)
  have hd1 : b - c ∈ (IsLocalRing.maximalIdeal A ^ 1) • Subalgebra.toSubmodule (AdjoinInv B t) := by
    rw [pow_one, show b - c = (b - e) + (e - f) - (c - f) by ring]
    exact sub_mem (add_mem (hmono _ B hBD _ hbe) hef) (hmono _ C hCD _ hcf)
  have hcube : (b - c) * (b - c) * (b - c) - (b - c) ∈
      (IsLocalRing.maximalIdeal A ^ (k + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) := by
    rw [show (b - c) * (b - c) * (b - c) - (b - c) = (b * b - b) - (c * c - c) - (c + c) * (b * b - b)
      + (b + b) * (c * c - c) + (b - c) * (b * b - b) + (b - c) * (c * c - c) by ring]
    have hbc : b - c ∈ AdjoinInv B t := (AdjoinInv B t).sub_mem hbD hcD
    refine add_mem (add_mem (add_mem (sub_mem (sub_mem hp hq) ?_) ?_) ?_) ?_
    · exact mul_left_mem _ _ ((AdjoinInv B t).add_mem hcD hcD) hp
    · exact mul_left_mem _ _ ((AdjoinInv B t).add_mem hbD hbD) hq
    · exact mul_left_mem _ _ hbc hp
    · exact mul_left_mem _ _ hbc hq
  have key : ∀ j, j + 1 ≤ k + 1 →
      b - c ∈ (IsLocalRing.maximalIdeal A ^ (j + 1)) • Subalgebra.toSubmodule (AdjoinInv B t) := by
    intro j
    induction j with
    | zero => intro _; simpa using hd1
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have h3 := mul_mem_mul _ _ _ (mul_mem_mul _ _ _ h1 h1) h1
      rw [← pow_add, ← pow_add] at h3
      have h3' := Submodule.smul_mono_left (Ideal.pow_le_pow_right (show j + 1 + 1 ≤ j + 1 + (j + 1) + (j + 1) by omega)) h3
      have hc' := Submodule.smul_mono_left (Ideal.pow_le_pow_right hj) hcube
      rw [show b - c = (b - c) * (b - c) * (b - c) - ((b - c) * (b - c) * (b - c) - (b - c)) by ring]
      exact sub_mem h3' hc'
  refine ⟨b, hb, c, hcC, ?_, hcf, ?_⟩
  · rw [← neg_sub]; exact neg_mem hbe
  · exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) (key k le_rfl)

end LateralTheory.E.LZIdemPowProof
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PairExtensionOfTensorUniversal
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafPairExtPf2
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafPairExtPf LateralTheory.E.LeafTwPairExistsPf

def pre {R : Type} [CommRing R] {I' I J K : Cx R} (μ : Pair I J K) (f : I' ⟶ I) : Pair I' J K where
  mul U s t w h := (μ.mul U s t w h).comp ((f.f s).hom.app (op U)).hom
  nat g s t w h a b := by
    change Sec.res g (μ.mul _ s t w h (Sec.map (f.f s) a) b) = μ.mul _ s t w h (Sec.map (f.f s) (Sec.res g a)) (Sec.res g b)
    rw [μ.nat, res_map]
  leibniz U s t w h a b := by
    change Sec.map (K.d w (w + 1)) (μ.mul U s t w h (Sec.map (f.f s) a) b) =
      μ.mul U (s + 1) t (w + 1) _ (Sec.map (f.f (s + 1)) (Sec.map (I'.d s (s + 1)) a)) b +
      s.negOnePow • μ.mul U s (t + 1) (w + 1) _ (Sec.map (f.f s) a) (Sec.map (J.d t (t + 1)) b)
    rw [μ.leibniz, map_map, map_map, f.comm]

def LeafTensUP : Prop := ∀ (R : Type) [CommRing R] {I J T K : Cx R} (τ : Pair I J T), τ.IsTensor → ∀ μ : Pair I J K,
  ∃ u : T ⟶ K, ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map (u.f w) (τ.mul U s t w h a b) = μ.mul U s t w h a b

def LeafExtTens : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {S T : Cx (ZMod q)} (σ : Pair (sgl (tw q 0)) (res _ (tw q i)) S)
  (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map ((resAug (tw q 0)).f s) a) b) →
  ∀ u : S ⟶ res _ (tw q i), ∃ g : T ⟶ res _ (tw q i), ι ≫ g = u

theorem LeafExtAlongAug_of (hup : LeafTensUP) (hext : LeafExtTens) : LeafExtAlongAug := by
  intro q _ i lam
  let σ := LateralTheory.E.LeafTwTensExPf.tau (sgl (tw q 0)) (res _ (tw q i))
  let τ := LateralTheory.E.LeafTwTensExPf.tau (res _ (tw q 0)) (res _ (tw q i))
  have hσ : σ.IsTensor := LateralTheory.E.LeafTwTensExPf.tau_isTensor _ _
  have hτ : τ.IsTensor := LateralTheory.E.LeafTwTensExPf.tau_isTensor _ _
  obtain ⟨u, hu⟩ := hup _ σ hσ lam
  obtain ⟨ι, hι⟩ := hup _ σ hσ (pre τ (resAug (tw q 0)))
  obtain ⟨g, hg⟩ := hext q i σ τ hσ hτ ι hι u
  refine ⟨post τ g, fun U t x b => ?_⟩
  have e : Sec.map (ι.f t) (σ.mul U 0 t t (zero_add t) x b) =
      τ.mul U 0 t t (zero_add t) (Sec.map ((resAug (tw q 0)).f 0) x) b := hι U 0 t t (zero_add t) x b
  rw [post_mul, ← e, map_map, ← HomologicalComplex.comp_f, hg, hu]

end LateralTheory.E.LeafPairExtPf2
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PropertyDescent
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf

namespace LateralTheory.E.LeafPropsDescendPf

def LeafSpreadOne : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D),
    (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) → IsProper c →
    SmoothOfRelativeDimension 1 c → IsPullback v c q (toR R) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ D), IsPullback r q' q (incl hR) → IsProper q' ∧ SmoothOfRelativeDimension 1 q'

def LeafBaseChangePre : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R R' : Subalgebra k Ω)
    (hR : R ≤ R') {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}}
    (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
    PreChain R c0 γ1 γ2 q d1 d2 v0 v1 v2 →
    ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1) (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1)
      (w2 : C2 ⟶ E2) (r0 : E0 ⟶ D0) (r1 : E1 ⟶ D1) (r2 : E2 ⟶ D2),
      (IsPullback w0 c0 q' (toR R') ∧ IsPullback w1 (γ1 ≫ c0) (e1 ≫ q') (toR R') ∧
        IsPullback w2 (γ2 ≫ γ1 ≫ c0) (e2 ≫ e1 ≫ q') (toR R') ∧ γ1 ≫ w0 = w1 ≫ e1 ∧ γ2 ≫ w1 = w2 ≫ e2) ∧
      IsPullback r0 q' q (incl hR) ∧ IsPullback r1 (e1 ≫ q') (d1 ≫ q) (incl hR) ∧
      IsPullback r2 (e2 ≫ e1 ≫ q') (d2 ≫ d1 ≫ q) (incl hR)

theorem LeafPropsDescend_of (hS : LeafSpreadOne) (hB : LeafBaseChangePre) : LeafPropsDescend := by
  intro k _ Ω _ _ R hR C0 C1 C2 c0 γ1 γ2 hc0 h1 h2 D0 D1 D2 q d1 d2 v0 v1 v2 hpre
  obtain ⟨f0, f1, f2, p0, p1, p2, -, -⟩ := id hpre
  obtain ⟨S0, hS0, fS0, H0⟩ := hS k Ω R hR c0 q v0 f0 hc0.2.1 hc0.2.2 p0
  obtain ⟨S1, hS1, quaternionDoubleCosetIndicator, H1⟩ := hS k Ω R hR (γ1 ≫ c0) (d1 ≫ q) v1 f1 h1.2.1 h1.2.2 p1
  obtain ⟨S2, hS2, fS2, H2⟩ := hS k Ω R hR (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) v2 f2 h2.2.1 h2.2.2 p2
  have l0 : S0 ≤ S0 ⊔ S1 ⊔ S2 := le_sup_left.trans le_sup_left
  have l1 : S1 ≤ S0 ⊔ S1 ⊔ S2 := le_sup_right.trans le_sup_left
  have l2 : S2 ≤ S0 ⊔ S1 ⊔ S2 := le_sup_right
  have hRR : R ≤ S0 ⊔ S1 ⊔ S2 := hS0.trans l0
  obtain ⟨E0, E1, E2, q', e1, e2, w0, w1, w2, r0, r1, r2, ⟨P0, P1, P2, c1, c2⟩, Q0, Q1, Q2⟩ :=
    hB k Ω R _ hRR c0 γ1 γ2 q d1 d2 v0 v1 v2 hpre
  obtain ⟨pr0, sm0⟩ := H0 _ l0 hRR E0 q' r0 Q0
  obtain ⟨pr1, sm1⟩ := H1 _ l1 hRR E1 (e1 ≫ q') r1 Q1
  obtain ⟨pr2, sm2⟩ := H2 _ l2 hRR E2 (e2 ≫ e1 ≫ q') r2 Q2
  exact ⟨_, (fS0.sup quaternionDoubleCosetIndicator).sup fS2, E0, E1, E2, q', e1, e2, w0, w1, w2,
    pr0, sm0, pr1, sm1, pr2, sm2, P0, P1, P2, c1, c2⟩

end LateralTheory.E.LeafPropsDescendPf

end
end

