import Development.EtaleCohomology.EtaleSheaves.Bundle0083

-- bundled from Development.EtaleCohomology.EtaleSheaves.SpreadingOutLocallyQuasiFinite
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.SpreadingOutLocallyQuasiFinite

def LeafQFAtBaseChange : Prop := ∀ {EA EB A B : Scheme.{0}} (h : EA ⟶ EB) (g : A ⟶ B) (rA : EA ⟶ A) (rB : EB ⟶ B),
    IsPullback rA h g rB → LocallyOfFiniteType g → ∀ x : EA, g.QuasiFiniteAt (rA x) → h.QuasiFiniteAt x

def LeafQFAtDescend : Prop := ∀ {CA CB A B : Scheme.{0}} (γ : CA ⟶ CB) (g : A ⟶ B) (vA : CA ⟶ A) (vB : CB ⟶ B),
    IsPullback vA γ g vB → LocallyOfFiniteType g → ∀ x : CA, γ.QuasiFiniteAt x → g.QuasiFiniteAt (vA x)

def LeafOpenSpread : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C A : Scheme.{0}} (c : C ⟶ Sp Ω) (p : A ⟶ Sp R) (v : C ⟶ A) (U : A.Opens),
    (LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ QuasiSeparated p) → IsPullback v c p (toR R) →
    (∀ x : C, v x ∈ U) →
    ∃ (S : Subalgebra k Ω), R ≤ S ∧ S.FG ∧ ∀ (R' : Subalgebra k Ω), S ≤ R' → ∀ (hR : R ≤ R') (E : Scheme.{0})
      (q' : E ⟶ Sp R') (r : E ⟶ A), IsPullback r q' p (incl hR) → ∀ z : E, r z ∈ U

theorem quasi_finite_at_base_change_of_finite_type : LeafQFAtBaseChange := by
  intro EA EB A B h g rA rB sq hg x hx
  let U := g.quasiFiniteLocus
  have sq2 : IsPullback (rA ∣_ U) ((rA ⁻¹ᵁ U).ι ≫ h) (U.ι ≫ g) rB :=
    (isPullback_morphismRestrict rA U).paste_vert sq
  have : LocallyQuasiFinite ((rA ⁻¹ᵁ U).ι ≫ h) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) sq2 inferInstance
  have hxV : x ∈ rA ⁻¹ᵁ U := hx
  have := ((rA ⁻¹ᵁ U).ι ≫ h).quasiFiniteAt ⟨x, hxV⟩
  have h2 := (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion (f := (rA ⁻¹ᵁ U).ι) (g := h)
    (x := ⟨x, hxV⟩)).mp this
  simpa using h2

theorem LeafSpreadLQFMap_of (hBC : LeafQFAtBaseChange) (hD : LeafQFAtDescend) (hO : LeafOpenSpread) :
    LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap := by
  intro k _ Ω _ _ R hR CA CB A B cB γ qB g vA vB hB hA pB pA hw hγ
  have : LocallyOfFinitePresentation (g ≫ qB) := hA.1
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g qB
  have sqC : IsPullback vA γ g vB := IsPullback.of_bot pA hw.symm pB
  have hU : ∀ x : CA, vA x ∈ g.quasiFiniteLocus := fun x =>
    hD γ g vA vB sqC inferInstance x (γ.quasiFiniteAt x)
  obtain ⟨S, hRS, hS, H⟩ := hO k Ω R hR (γ ≫ cB) (g ≫ qB) vA g.quasiFiniteLocus hA pA hU
  refine ⟨S, hRS, hS, ?_⟩
  intro R' hSR' hRR' EA EB qB' h rA rB QB QA hc
  have sqE : IsPullback rA h g rB := IsPullback.of_bot QA hc.symm QB
  have : LocallyOfFiniteType h :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sqE inferInstance
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  refine top_le_iff.mp fun z _ => ?_
  exact hBC h g rA rB sqE inferInstance z (H R' hSR' hRR' EA (h ≫ qB') rA QA z)

end LateralTheory.E.SpreadingOutLocallyQuasiFinite

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SpreadingOutQuasiFinitenessBaseChange
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.SpreadingOutQuasiFinitenessBaseChange

theorem toR_incl {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R') :
    toR R' ≫ incl hR = toR R := by
  rw [← Spec.map_comp]; rfl

theorem sq {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {R R' : Subalgebra k Ω} (hR : R ≤ R')
    {C D : Scheme.{0}} {c : C ⟶ Sp Ω} {q : D ⟶ Sp R} {v : C ⟶ D} (hv : IsPullback v c q (toR R)) :
    IsPullback (pullback.lift v (c ≫ toR R') (by rw [Category.assoc, toR_incl]; exact hv.w)) c
      (pullback.snd q (incl hR)) (toR R') := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (incl hR))
  rw [pullback.lift_fst, toR_incl]; exact hv

theorem spread_chain_base_change_to_larger_subalgebra : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafBaseChangePreR := by
  intro k _ Ω _ _ R R' hR C0 C1 C2 c0 γ1 γ2 D0 D1 D2 q d1 d2 v0 v1 v2 hpre
  obtain ⟨-, -, -, p0, p1, p2, m1, m2⟩ := hpre
  let e1 : pullback (d1 ≫ q) (incl hR) ⟶ pullback q (incl hR) :=
    pullback.lift (pullback.fst _ _ ≫ d1) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)
  let e2 : pullback (d2 ≫ d1 ≫ q) (incl hR) ⟶ pullback (d1 ≫ q) (incl hR) :=
    pullback.lift (pullback.fst _ _ ≫ d2) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition)
  have t1 : e1 ≫ pullback.snd q (incl hR) = pullback.snd _ _ := pullback.lift_snd _ _ _
  have t2 : e2 ≫ pullback.snd (d1 ≫ q) (incl hR) = pullback.snd _ _ := pullback.lift_snd _ _ _
  have t12 : e2 ≫ e1 ≫ pullback.snd q (incl hR) = pullback.snd _ _ := by rw [t1, t2]
  have P0 := sq hR p0
  have P1 := sq hR p1
  have P2 := sq hR p2
  refine ⟨_, _, _, pullback.snd q (incl hR), e1, e2, _, pullback.lift v1 ((γ1 ≫ c0) ≫ toR R') (by rw [Category.assoc, toR_incl]; exact p1.w), pullback.lift v2 ((γ2 ≫ γ1 ≫ c0) ≫ toR R') (by rw [Category.assoc, toR_incl]; exact p2.w), pullback.fst _ _, pullback.fst _ _, pullback.fst _ _,
    ⟨P0, ?_, ?_, ?_, ?_⟩, IsPullback.of_hasPullback _ _, ?_, ?_, pullback.lift_fst _ _ _,
    pullback.lift_fst _ _ _, pullback.lift_fst _ _ _⟩
  · rw [t1]; exact P1
  · rw [t12]; exact P2
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, e1, pullback.lift_fst_assoc]; exact m1
    · simp only [Category.assoc, pullback.lift_snd, e1]
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, e2, pullback.lift_fst_assoc]; exact m2
    · simp only [Category.assoc, pullback.lift_snd, e2]
  · rw [t1]; exact IsPullback.of_hasPullback _ _
  · rw [t12]; exact IsPullback.of_hasPullback _ _

theorem LeafSpreadQF_of (hSep : LateralTheory.E.LeafSpreadProperPf.LeafSpreadSeparated)
    (hSm : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadSmooth1) (hG : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFGraph)
    (hM : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap) : LateralTheory.E.QuasiFiniteDescent.LeafSpreadQF :=
  LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadQF_of hSep hSm hG hM spread_chain_base_change_to_larger_subalgebra

end LateralTheory.E.SpreadingOutQuasiFinitenessBaseChange

end
end

