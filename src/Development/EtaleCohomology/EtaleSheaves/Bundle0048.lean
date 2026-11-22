import Development.EtaleCohomology.EtaleSheaves.Bundle0037
import Development.EtaleCohomology.EtaleSheaves.Bundle0035
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.EtaleCohomology.EtaleSheaves.Bundle0036
import Development.EtaleCohomology.EtaleSheaves.Bundle0033

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafDescendVCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafDescendVCut

abbrev toR {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) : Sp Ω ⟶ Sp R :=
  Spec.map (CommRingCat.ofHom (algebraMap R Ω))

abbrev incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (h : R ≤ R') : Sp R' ⟶ Sp R :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)

def Chain {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) {C0 C1 C2 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0)
    (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2) : Prop :=
  IsProper q ∧ SmoothOfRelativeDimension 1 q ∧ IsProper (d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d1 ≫ q) ∧
  IsProper (d2 ≫ d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) ∧
  IsPullback v0 c0 q (toR R) ∧ IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (toR R) ∧
  IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (toR R) ∧ γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2

def LeafDescendChain : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {C0 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω), IsCurve c0 → ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1),
    IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2), Chain R c0 γ1 γ2 q d1 d2 v0 v1 v2

def LeafDescendMap : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type)
    [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG → ∀ {C0 D0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (q : D0 ⟶ Sp R)
    (v0 : C0 ⟶ D0), IsProper q → IsPullback v0 c0 q (toR R) → ∀ (e : C0 ⟶ X),
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
    ∃ (R' : Subalgebra k Ω) (hR : R ≤ R'), R'.FG ∧ ∀ (E0 : Scheme.{0}) (q' : E0 ⟶ Sp R') (r : E0 ⟶ D0)
      (w0 : C0 ⟶ E0), IsPullback r q' q (incl hR) → IsPullback w0 c0 q' (toR R') → w0 ≫ r = v0 →
      ∃ f : E0 ⟶ X, w0 ≫ f = e ∧ f ≫ p = q' ≫ Spec.map (CommRingCat.ofHom (algebraMap k R'))

def LeafBaseChange : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R R' : Subalgebra k Ω)
    (hR : R ≤ R') {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}}
    (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
    Chain R c0 γ1 γ2 q d1 d2 v0 v1 v2 →
    ∃ (E0 E1 E2 : Scheme.{0}) (q' : E0 ⟶ Sp R') (e1 : E1 ⟶ E0) (e2 : E2 ⟶ E1) (w0 : C0 ⟶ E0) (w1 : C1 ⟶ E1)
      (w2 : C2 ⟶ E2) (r : E0 ⟶ D0), Chain R' c0 γ1 γ2 q' e1 e2 w0 w1 w2 ∧ IsPullback r q' q (incl hR) ∧
      w0 ≫ r = v0

def LeafIrred : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {C0 D0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (q : D0 ⟶ Sp R) (v0 : C0 ⟶ D0), IsCurve c0 →
    SmoothOfRelativeDimension 1 q → IsPullback v0 c0 q (toR R) → IrreducibleSpace D0

def LeafDimBound : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω), R.FG →
    ∀ {D0 : Scheme.{0}} (q : D0 ⟶ Sp R), SmoothOfRelativeDimension 1 q →
    topologicalKrullDim D0 ≤ ringKrullDim R + 1

theorem goal_of (hA : LeafDescendChain) (hB : LeafDescendMap) (hC : LeafBaseChange) (hI : LeafIrred)
    (hD : LeafDimBound) : LateralTheory.E.LeafSpreadVCut.LeafDescendV := by
  intro k _ X p _ Ω _ _ C0 c0 e hc0 he C1 C2 γ1 γ2 h1 h2
  obtain ⟨R, hR, D0, D1, D2, q, d1, d2, v0, v1, v2, hch⟩ := hA k Ω c0 hc0 C1 C2 γ1 γ2 h1 h2
  obtain ⟨R', hRR', hR', hM⟩ := hB k p Ω R hR c0 q v0 hch.1 hch.2.2.2.2.2.2.1 e he
  obtain ⟨E0, E1, E2, q', e1, e2, w0, w1, w2, r, hch', hr, hw⟩ :=
    hC k Ω R R' hRR' c0 γ1 γ2 q d1 d2 v0 v1 v2 hch
  obtain ⟨f, hf1, hf2⟩ := hM E0 q' r w0 hr hch'.2.2.2.2.2.2.1 hw
  obtain ⟨pq, sq, pq1, sq1, pq2, sq2, P0, P1, P2, c1, c2⟩ := hch'
  exact ⟨R', hR', E0, E1, E2, q', e1, e2, f, w0, w1, w2, pq, sq, pq1, sq1, pq2, sq2, hf2,
    hI k Ω R' hR' c0 q' w0 hc0 sq P0, hD k Ω R' hR' q' sq, P0, P1, P2, c1, c2, hf1⟩

end LateralTheory.E.LeafDescendVCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafExtendCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafExtendCut

def LeafStalkValuation : Prop := ∀ (Ω : Type) [Field Ω] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp Ω) (x y : C)
  (hx : IsGenericPoint x (⊤ : Set C)), IsCurve c → y ≠ x →
    ValuationRing (C.presheaf.stalk y) ∧
      (letI := (C.presheaf.stalkSpecializes (hx.specializes (Set.mem_univ y))).hom.toAlgebra
       IsFractionRing (C.presheaf.stalk y) (C.presheaf.stalk x))

def LeafLocalExtend : Prop := ∀ {C X S : Scheme.{0}} [IsIntegral C] (sC : C ⟶ S) (p : X ⟶ S) [IsProper p] (x y : C),
  IsGenericPoint x (⊤ : Set C) → ∀ (h : x ⤳ y), ValuationRing (C.presheaf.stalk y) →
    (letI := (C.presheaf.stalkSpecializes h).hom.toAlgebra
     IsFractionRing (C.presheaf.stalk y) (C.presheaf.stalk x)) →
    ∀ ψ : Spec (C.presheaf.stalk x) ⟶ X, ψ ≫ p = C.fromSpecStalk x ≫ sC →
      ∃ (U : C.Opens) (_ : y ∈ U) (hxU : x ∈ U) (f : U.toScheme ⟶ X),
        U.fromSpecStalkOfMem x hxU ≫ f = ψ ∧ f ≫ p = U.ι ≫ sC

def LeafGlueExtend : Prop := ∀ {C X S : Scheme.{0}} [IsIntegral C] (sC : C ⟶ S) (p : X ⟶ S) [IsSeparated p] (x : C),
  IsGenericPoint x (⊤ : Set C) → ∀ ψ : Spec (C.presheaf.stalk x) ⟶ X,
    (∀ y : C, ∃ (U : C.Opens) (_ : y ∈ U) (hxU : x ∈ U) (f : U.toScheme ⟶ X),
        U.fromSpecStalkOfMem x hxU ≫ f = ψ ∧ f ≫ p = U.ι ≫ sC) →
      ∃ e : C ⟶ X, C.fromSpecStalk x ≫ e = ψ ∧ e ≫ p = sC

theorem goal_of (h1 : LeafStalkValuation) (h2 : LeafLocalExtend) (h3 : LeafGlueExtend) :
    LateralTheory.E.LeafCurveVCut.LeafExtend := by
  intro k Ω _ _ _ X C0 p _ c0 x hc hx ψ hψ
  have : IsIntegral C0 := hc.1
  refine h3 (c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p x hx ψ ?_
  intro y
  by_cases hyx : y = x
  · subst hyx
    obtain ⟨U, hxU, f, hf1, hf2⟩ := spread_out_of_isGermInjective'
      (c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p ψ hψ
    exact ⟨U, hxU, hxU, f, hf1.symm, hf2⟩
  · obtain ⟨hv, hfr⟩ := h1 Ω c0 x y hx hc hyx
    exact h2 (c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p x y hx _ hv hfr ψ hψ

end LateralTheory.E.LeafExtendCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafFibreFieldPf
section
open AlgebraicGeometry CategoryTheory Topology

namespace LateralTheory.E.LeafFibreFieldPf

open Cardinal IntermediateField in
theorem alg_part (k K : Type) [Field k] [Field K] [Algebra k K] (S : Finset K)
    (hgen : IntermediateField.adjoin k (S : Set K) = ⊤) (d : ℕ) (hd : Algebra.trdeg k K = d + 1) :
    ∃ (F : IntermediateField k K) (s : Finset F) (t : K), s.card ≤ d ∧
      Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F ∧ Transcendental F t ∧
      FiniteDimensional (IntermediateField.adjoin F {t}) K := by
  classical
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis k K
  have hcard : #B = ((d + 1 : ℕ) : Cardinal) := by
    rw [hB.cardinalMk_eq_trdeg, hd]; push_cast; rfl
  obtain ⟨T, hTB, hTc⟩ := Cardinal.mk_set_eq_nat_iff_finset.mp hcard
  obtain ⟨a, haT⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  set T' := T.erase a with hT'
  let F : IntermediateField k K := IntermediateField.adjoin k (T' : Set K)
  let sF : Finset F := T'.attach.image fun x => ⟨x.1, IntermediateField.subset_adjoin k _ x.2⟩
  have hsF : (F.val '' (sF : Set F)) = (T' : Set K) := by
    ext y; simp [sF]; intro h; exact IntermediateField.subset_adjoin k _ (Finset.mem_coe.mpr h)
  refine ⟨F, sF, a, ?_, ?_, ?_, ?_⟩
  · refine (Finset.card_image_le).trans ?_
    rw [Finset.card_attach, Finset.card_erase_of_mem haT, hTc]; simp
  · have hmem : ∀ y : F, y ∈ IntermediateField.adjoin k (sF : Set F) := by
      intro y
      have : (y : K) ∈ (IntermediateField.adjoin k (sF : Set F)).map F.val := by
        rw [IntermediateField.adjoin_map, hsF]; exact y.2
      rw [← SetLike.mem_coe, IntermediateField.coe_map] at this
      obtain ⟨z, hz, hzy⟩ := this
      have : z = y := Subtype.ext hzy
      exact this ▸ hz
    exact ⟨fun y => by
      have := isAlgebraic_algebraMap (R := IntermediateField.adjoin k (sF : Set F)) (A := F) ⟨y, hmem y⟩
      exact this⟩
  · have hind := hB.1
    have hnot : (⟨a, hTB ▸ haT⟩ : B) ∉ {i : B | (i : K) ≠ a} := by simp
    have htr := hind.transcendental_adjoin hnot
    have himg : (Subtype.val '' {i : B | (i : K) ≠ a}) = (T' : Set K) := by
      ext y; simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_right,
        exists_eq_right, hT', Finset.coe_erase, Set.mem_diff, Set.mem_singleton_iff, ← hTB]
      tauto
    rw [himg, ← IntermediateField.transcendental_adjoin_iff] at htr
    exact htr
  ·
    set L := IntermediateField.adjoin F {a} with hL
    have hBT : (B : Set K) = (T : Set K) := hTB.symm
    have halgB := hB.isAlgebraic_field
    rw [Subtype.range_coe] at halgB
    set E := IntermediateField.adjoin k B with hE
    have hEL : ∀ x ∈ E, x ∈ L := by
      intro x hx
      have hle : E ≤ L.restrictScalars k := by
        rw [hE, IntermediateField.adjoin_le_iff]
        intro b hb
        rw [← hTB] at hb
        by_cases hba : b = a
        · subst hba; exact IntermediateField.mem_adjoin_simple_self F b
        · have hbF : b ∈ F := IntermediateField.subset_adjoin k _ (by simp [hT', hba, hb])
          exact (IntermediateField.algebraMap_mem L (⟨b, hbF⟩ : F))
      exact hle hx
    let g : E →+* L :=
      { toFun := fun x => ⟨x.1, hEL x.1 x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
        map_zero' := rfl, map_add' := fun _ _ => rfl }
    let _ : Algebra E L := g.toAlgebra
    have : IsScalarTower E L K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hint : ∀ x : K, IsIntegral L x := fun x =>
      ((halgB.isAlgebraic x).extendScalars g.injective).isIntegral
    have hfd := IntermediateField.finiteDimensional_adjoin (K := L) (S := (S : Set K)) (fun x _ => hint x)
    have htop : IntermediateField.adjoin L (S : Set K) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ IntermediateField.adjoin k (S : Set K) := hgen ▸ trivial
      let M : IntermediateField k K :=
        { carrier := (IntermediateField.adjoin L (S : Set K) : Set K)
          mul_mem' := fun ha hb => (IntermediateField.adjoin L (S : Set K)).mul_mem ha hb
          add_mem' := fun ha hb => (IntermediateField.adjoin L (S : Set K)).add_mem ha hb
          inv_mem' := fun _ hx => (IntermediateField.adjoin L (S : Set K)).inv_mem hx
          algebraMap_mem' := fun c => by
            have h1 := IntermediateField.algebraMap_mem (IntermediateField.adjoin L (S : Set K))
              (⟨algebraMap F K (algebraMap k F c), IntermediateField.algebraMap_mem L _⟩ : L)
            rw [IsScalarTower.algebraMap_apply k F K]
            exact h1 }
      have hle : IntermediateField.adjoin k (S : Set K) ≤ M := by
        rw [IntermediateField.adjoin_le_iff]
        intro y hy
        show y ∈ (IntermediateField.adjoin L (S : Set K) : Set K)
        exact IntermediateField.subset_adjoin L _ hy
      exact (hle hx : x ∈ (IntermediateField.adjoin L (S : Set K) : Set K))
    rw [htop] at hfd
    exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := L) (E := K)).toLinearEquiv

theorem gen_top (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ S : Finset (FractionRing A), IntermediateField.adjoin k (S : Set (FractionRing A)) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := (‹Algebra.FiniteType k A›).out
  refine ⟨s.image (algebraMap A (FractionRing A)), ?_⟩
  have hA : ∀ a : A, algebraMap A (FractionRing A) a ∈
      IntermediateField.adjoin k ((s.image (algebraMap A (FractionRing A)) : Finset _) : Set (FractionRing A)) := by
    intro a
    have ha : a ∈ Algebra.adjoin k (s : Set A) := hs ▸ Algebra.mem_top
    have h1 : algebraMap A (FractionRing A) a ∈ (Algebra.adjoin k (s : Set A)).map (IsScalarTower.toAlgHom k A (FractionRing A)) :=
      Subalgebra.mem_map.mpr ⟨a, ha, rfl⟩
    rw [AlgHom.map_adjoin] at h1
    refine IntermediateField.algebra_adjoin_le_adjoin k _ ?_
    simpa [Finset.coe_image] using h1
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  exact div_mem (hA a) (hA b)

theorem dimX_eq (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] (e : ℕ)
    (he : letI := (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom.toAlgebra
      Algebra.trdeg k X.functionField = e) :
    topologicalKrullDim X = e := by
  have h := GlobalTheory.topologicalKrullDim_eq_of_forall_exists_isOpen (Z := (Set.univ : Set X))
    ⟨genericPoint X, trivial⟩ (d := (e : WithBot ℕ∞)) (fun x _ => by
      obtain ⟨A, _, _, _, _, _, j, _, hx, -, htr⟩ := GlobalTheory.exists_affine_chart_trdeg_eq p x
      refine ⟨Set.range j, j.isOpenEmbedding.isOpen_range, hx, ?_⟩
      rw [Set.inter_univ, GlobalTheory.topologicalKrullDim_eq_of_isEmbedding j.isOpenEmbedding.isEmbedding rfl]
      have hA := GlobalTheory.ringKrullDim_eq_of_trdeg_eq k A (htr.trans he)
      rw [← hA]
      exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A)
  rw [← h]
  exact (GlobalTheory.topologicalKrullDim_eq_of_isEmbedding (e := (id : X → X)) IsEmbedding.id (Set.range_id)).symm

theorem LeafFibreField_of : LateralTheory.E.LeafCurveVCut.LeafFibreField := by
  intro k _ X _ p _ hd
  letI := (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom.toAlgebra
  obtain ⟨A, _, _, _, _, _, j, _, hx, hj, htr⟩ := GlobalTheory.exists_affine_chart_trdeg_eq p (genericPoint X)
  obtain ⟨e, -, he2⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k A
  have hdim := dimX_eq k p e (htr.symm.trans he2)
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := by
    cases e with
    | zero => rw [hdim] at hd; simp at hd
    | succ d => exact ⟨d, rfl⟩
  have : Algebra.IsAlgebraic A (FractionRing A) := IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  have htrK : Algebra.trdeg k (FractionRing A) = d + 1 := by
    rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top k A (FractionRing A), he2]; push_cast; rfl
  obtain ⟨S, hS⟩ := gen_top k A
  obtain ⟨F, s, t, hs, halg, ht, hfin⟩ := alg_part k (FractionRing A) S hS d htrK
  refine ⟨F, inferInstance, inferInstance, FractionRing A, inferInstance, inferInstance, d, s, t,
    Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫ j, ?_, hs, halg, ht, hfin, ?_, ?_⟩
  · rw [hdim]; exact_mod_cast Nat.lt_succ_self d
  · rw [Category.assoc, hj, ← Spec.map_comp]
    congr 1
  · obtain ⟨q, hq⟩ := hx
    obtain ⟨pt⟩ : Nonempty (Spec (.of (FractionRing A))) := inferInstance
    refine ⟨pt, ?_⟩
    have hz : (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) pt ⤳ q := by
      refine (PrimeSpectrum.le_iff_specializes _ _).mp ?_
      show Ideal.comap (algebraMap A (FractionRing A)) pt.asIdeal ≤ q.asIdeal
      have hbot : pt.asIdeal = ⊥ := by
        rcases Ideal.eq_bot_or_top pt.asIdeal with h | h
        · exact h
        · exact absurd h pt.isPrime.ne_top
      intro a ha
      rw [Ideal.mem_comap, hbot, Ideal.mem_bot] at ha
      rw [(IsFractionRing.injective A (FractionRing A)) (ha.trans (map_zero _).symm)]
      exact zero_mem _
    have h1 := hz.map j.continuous
    rw [hq] at h1
    have h2 := (genericPoint_spec X).specializes
      (Set.mem_univ (j ((Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) pt)))
    rw [Scheme.Hom.comp_apply]
    exact (h1.antisymm h2).eq

end LateralTheory.E.LeafFibreFieldPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafLocStalkPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafLocStalkPf

def RelZS (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {U E : Spc} (u : U ⟶ E) : Prop :=
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull R u F m)) ∧ Function.Injective (pull R u F n)

def StalkH (q : ℕ) [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (i : ℤ) : Prop :=
  ∀ (A : Type) [CommRing A] (s : Sp A ⟶ X), SH A → IsUnit (q : A) →
    Eqv _ (pullback.snd (cechAug f) (sch.map s)) (tw q i)

def QAll (q : ℕ) [NeZero q] (n : ℤ) : Prop :=
  ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f], IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ, StalkH q f i →
    RelZS (ZMod q) (tw q i) n (cechAug f)

def LocSurj : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ m < n, QAll q m) →
  ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f], IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ, StalkH q f i →
    ∀ m : ℤ, m + 1 = n → Function.Surjective (pull (ZMod q) (cechAug f) (tw q i) m)

def LocInj : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ m < n, QAll q m) →
  ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f], IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ, StalkH q f i →
    Function.Injective (pull (ZMod q) (cechAug f) (tw q i) n)

def LeafLocStalk : Prop := Hyps → ∀ (q : ℕ) [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f], IsUnit (q : Γ(X, ⊤)) →
  ∀ i : ℤ, (∀ (A : Type) [CommRing A] (s : Sp A ⟶ X), SH A → IsUnit (q : A) →
    Eqv _ (pullback.snd (cechAug f) (sch.map s)) (tw q i)) → Eqv _ (cechAug f) (tw q i)

end LateralTheory.E.LeafLocStalkPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafMapWPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2 LateralTheory.E.LeafGeomPf LateralTheory.E.HalfDegreeVanishing

namespace LateralTheory.E.LeafMapWPf

variable {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b))

theorem pvm_res {n : ℕ} {X Y : Scheme.{0}} (k : Y ⟶ X) (x : Sx (PB (bsumOf V W)) n X) {i j : Fin (n + 1)} (f : i ⟶ j) :
    (((pv V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x)).map f).1.2 : Scheme.Γ.obj (op Y)) =
      Scheme.Γ.map k.op (((pv V W x).map f).1.2 : Scheme.Γ.obj (op X)) := by
  have h := ConcreteCategory.congr_hom (((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).naturality k.op) x
  have h2 := congrArg (fun p => (p.1.2 : Scheme.Γ.obj (op Y))) (Functor.congr_hom h f)
  refine h2.trans ?_
  have h3 := congrArg (fun p => (p.2 : Scheme.Γ.obj (op Y))) (um_hom_val (Functor.congr_obj h i) (Functor.congr_obj h j) (((ConcreteCategory.hom
      (((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).app (op X) ≫
        ((PGL (a + b)).obj (op (SimplexCategory.mk n))).map k.op)) x).map f))
  exact h3.trans rfl

theorem pvm_simp {n m : ℕ} {X : Scheme.{0}} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (x : Sx (PB (bsumOf V W)) n X)
    {i j : Fin (m + 1)} (f : i ⟶ j) :
    (((pv V W ((((PB (bsumOf V W)).map θ.op).app (op X)) x)).map f).1.2 : Scheme.Γ.obj (op X)) =
      (((((PGL (a + b)).map θ.op).app (op X)) (pv V W x) : Fin (m + 1) ⥤ Um (a + b) (Scheme.Γ.obj (op X))).map f).1.2 := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app ((pullback.snd (bsumOf V W) (PGL.pr (a + b))).naturality θ.op) (op X)) x
  have h2 := congrArg (fun p => (p.1.2 : Scheme.Γ.obj (op X))) (Functor.congr_hom h f)
  refine h2.trans ?_
  have h3 := congrArg (fun p => (p.2 : Scheme.Γ.obj (op X))) (um_hom_val (Functor.congr_obj h i) (Functor.congr_obj h j) (((ConcreteCategory.hom
      (((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).app (op X) ≫
        (((PGL (a + b)).map θ.op).app (op X)))) x).map f))
  exact h3.trans rfl

theorem pe_simp {n m : ℕ} {X : Scheme.{0}} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (x : Sx (PB (bsumOf V W)) n X) :
    pe V W ((((PB (bsumOf V W)).map θ.op).app (op X)) x) = ((E.map θ.op).app (op X)) (pe V W x) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app ((pullback.fst (bsumOf V W) (PGL.pr (a + b))).naturality θ.op) (op X)) x

theorem pw_simp {n m : ℕ} {X : Scheme.{0}} (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (e : Sx E n X)
    {i j : Fin (m + 1)} (f : i ⟶ j) :
    (show GL (Fin b) (Scheme.Γ.obj (op X)) from (pw W (((E.map θ.op).app (op X)) e)).map f) =
      (show GL (Fin b) (Scheme.Γ.obj (op X)) from
        ((((ofCat (glCat b)).map θ.op).app (op X)) (pw W e) : Fin (m + 1) ⥤ SingleObj (GL (Fin b) (Scheme.Γ.obj (op X)))).map f) :=
  eq_of_heq (Functor.hcongr_hom (ConcreteCategory.congr_hom (NatTrans.congr_app (W.naturality θ.op) (op X)) e) f)

def gX (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}ᵒᵖ) (x : ((U2 V W).obj n).obj X) : ((PGL b).obj n).obj X :=
  show Fin (n.unop.len + 1) ⥤ Um b (Scheme.Γ.obj (op X.unop)) from gfun V W x.1 x.2

theorem gX_nat_X (n : SimplexCategoryᵒᵖ) {X Y : Scheme.{0}ᵒᵖ} (k : X ⟶ Y) (x : ((U2 V W).obj n).obj X) :
    gX V W n Y (((U2 V W).obj n).map k x) = ((PGL b).obj n).map k (gX V W n X x) := by
  apply um_functor_ext
  · intro i
    show wb (a := a) ((pv V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n.unop.len))).map k.unop.op x.1)).obj i).1 = _
    rw [pv_res]; rfl
  · intro i j f
    apply Prod.ext
    · show (show GL (Fin b) _ from (pw W (pe V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n.unop.len))).map k.unop.op x.1))).map f) = _
      rw [pe_res, pw_res]; rfl
    · apply Units.ext
      exact pvm_res V W k.unop x.1 f

theorem gX_nat_n {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (X : Scheme.{0}ᵒᵖ) (x : ((U2 V W).obj n).obj X) :
    gX V W m X ((((U2 V W).map θ).app X) x) = (((PGL b).map θ).app X) (gX V W n X x) := by
  apply um_functor_ext
  · intro i
    show wb (a := a) ((pv V W ((((PB (bsumOf V W)).map θ.unop.op).app (op X.unop)) x.1)).obj i).1 = _
    rw [pv_simp]; rfl
  · intro i j f
    apply Prod.ext
    · show (show GL (Fin b) _ from (pw W (pe V W ((((PB (bsumOf V W)).map θ.unop.op).app (op X.unop)) x.1))).map f) = _
      rw [pe_simp, pw_simp]; rfl
    · apply Units.ext
      exact (pvm_simp V W θ.unop x.1 f).trans rfl

def gmap : U2 V W ⟶ PGL b where
  app n :=
    { app := fun X => TypeCat.ofHom (gX V W n X)
      naturality := fun X Y k => by
        ext x
        exact gX_nat_X V W n k x }
  naturality n m θ := by
    ext X x
    exact gX_nat_n V W θ X x

theorem gmap_pr : gmap V W ≫ PGL.pr b = f2 V W ≫ PB.pr _ ≫ W := by
  ext n X x
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j f => ?_)
  erw [Category.id_comp, Category.comp_id]
  rfl

theorem gmap_line : gmap V W ≫ PGL.line b = f2 V W ≫ pullback.snd (bsumOf V W) (PGL.pr (a + b)) ≫ PGL.line (a + b) := by
  ext n X x
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun i j f => ?_)
  erw [Category.id_comp, Category.comp_id]
  rfl

theorem LeafMapW_of : LateralTheory.E.HalfDegreeVanishing.LeafMapW := fun V W => ⟨gmap V W, gmap_pr V W, gmap_line V W⟩

end LateralTheory.E.LeafMapWPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafModelCurveCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafModelCurveCut

def ExistsNormalProperCurveModel : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    ∃ (C0 : Scheme.{0}) (c0 : C0 ⟶ Sp Ω) (x : C0) (ψ : Spec (C0.presheaf.stalk x) ⟶ Sp L),
      IsIntegral C0 ∧ IsProper c0 ∧ (∀ y : C0, IsIntegrallyClosed (C0.presheaf.stalk y)) ∧
      topologicalKrullDim C0 = 1 ∧ IsGenericPoint x (⊤ : Set C0) ∧
      ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω L)) = C0.fromSpecStalk x ≫ c0

def LeafSmoothOfNormal : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω),
  IsIntegral C → LocallyOfFiniteType c → (∀ y : C, IsIntegrallyClosed (C.presheaf.stalk y)) →
    topologicalKrullDim C = 1 → SmoothOfRelativeDimension 1 c

theorem goal_of (hN : ExistsNormalProperCurveModel) (hS : LeafSmoothOfNormal) : LateralTheory.E.LeafCurveVCut.LeafModelCurve := by
  intro Ω L _ _ _ _ u hu hfin
  obtain ⟨C0, c0, x, ψ, hint, hprop, hnorm, hdim, hx, hψ⟩ := hN Ω L u hu hfin
  refine ⟨C0, c0, x, ψ, ⟨hint, hprop, ?_⟩, hx, hψ⟩
  have := hprop
  exact hS Ω c0 hint inferInstance hnorm hdim

end LateralTheory.E.LeafModelCurveCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafPolyEtPf
section
noncomputable section
open TensorProduct

namespace LateralTheory.E.LeafPolyEtPf

theorem LeafPolyEt_of : LateralTheory.E.LeafRoofEtPPf.LeafPolyEt := by
  intro d C B D _ _ _ _ φ hφ
  letI : Algebra C B := (φ.comp MvPolynomial.C).toAlgebra
  let P := MvPolynomial (Fin d) C
  letI : Algebra P B := φ.toAlgebra
  haveI : IsScalarTower C P B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.Etale P B := by rw [← RingHom.etale_algebraMap]; exact hφ
  let e2 : MvPolynomial (Fin d) D ≃+* P ⊗[C] D :=
    (MvPolynomial.algebraTensorAlgEquiv (σ := Fin d) C D).symm.toRingEquiv.trans (Algebra.TensorProduct.comm C D P).toRingEquiv
  let e1 : (P ⊗[C] D) ⊗[P] B ≃ₐ[P] B ⊗[C] D :=
    (Algebra.TensorProduct.comm P (P ⊗[C] D) B).trans (Algebra.TensorProduct.cancelBaseChange C P P B D)
  have hg : (algebraMap (P ⊗[C] D) ((P ⊗[C] D) ⊗[P] B)).Etale :=
    RingHom.etale_algebraMap.mpr inferInstance
  have key : MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeRight : D →ₐ[C] B ⊗[C] D).toRingHom
      (fun j => φ (MvPolynomial.X j) ⊗ₜ[C] (1:D)) =
      (e1.toRingEquiv.toRingHom.comp (algebraMap (P ⊗[C] D) ((P ⊗[C] D) ⊗[P] B))).comp
        e2.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [e1, e2, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.coe_trans, AlgEquiv.coe_ringEquiv]
      rw [show (MvPolynomial.C r : MvPolynomial (Fin d) D) = MvPolynomial.monomial 0 r from rfl,
        MvPolynomial.algebraTensorAlgEquiv_symm_monomial]
      simp only [MvPolynomial.monomial_zero', MvPolynomial.C_1]
      show _ = (Algebra.TensorProduct.cancelBaseChange C P P B D)
        ((Algebra.TensorProduct.comm P (P ⊗[C] D) B) (((1 : P) ⊗ₜ[C] r) ⊗ₜ[P] (1 : B)))
      simp
    · intro j
      simp [e1, e2]
      rw [Algebra.smul_def, mul_one]; rfl
  rw [key]
  have hc := RingHom.Etale.stableUnderComposition
  exact hc _ _ (RingHom.Etale.of_bijective e2.bijective) (hc _ _ hg (RingHom.Etale.of_bijective e1.bijective))

end LateralTheory.E.LeafPolyEtPf
end
end

