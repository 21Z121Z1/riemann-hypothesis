import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0158
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0154

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ThetaDescent

def gen {o K : Type} [CommRing o] [Field K] (β : o →+* K) (s : Finset K) : Subfield K :=
  Subfield.closure (Set.range β ∪ s)

theorem gen_mono {o K : Type} [CommRing o] [Field K] (β : o →+* K) {s s' : Finset K} (h : s ⊆ s') :
    gen β s ≤ gen β s' :=
  Subfield.closure_mono (Set.union_subset_union_right _ (Finset.coe_subset.2 h))

theorem subset_gen {o K : Type} [CommRing o] [Field K] (β : o →+* K) {s s' : Finset K} (h : s ⊆ s') :
    (s : Set K) ⊆ gen β s' :=
  fun _ hx => Subfield.subset_closure (Or.inr (h hx))

theorem mem_gen {o K : Type} [CommRing o] [Field K] (β : o →+* K) (s : Finset K) (a : o) : β a ∈ gen β s :=
  Subfield.subset_closure (Or.inl ⟨a, rfl⟩)

theorem countable_gen {o K : Type} [CommRing o] [Field K] (β : o →+* K) (s : Finset K) [Countable o] :
    Countable (gen β s) := by
  have hc : (Set.range β ∪ (s : Set K)).Countable := (Set.countable_range β).union s.countable_toSet
  rw [← Cardinal.mk_le_aleph0_iff]
  refine (Subfield.cardinalMk_closure_le_max _).trans ?_
  exact max_le (Cardinal.mk_le_aleph0_iff.2 hc.to_subtype) le_rfl

theorem spMap_subtype {K : Type} [Field K] {K₀ K₁ : Subfield K} (h : K₀ ≤ K₁) :
    spMap K₁.subtype ≫ spMap (Subfield.inclusion h) = spMap K₀.subtype := by
  rw [← Spec.map_comp]; rfl

theorem isProper_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    IsProper f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have := isProper_str R N
  infer_instance

theorem descends_of
    (hproj : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∃ s : Finset K, ∀ K₁ : Subfield K, K₀ ≤ K₁ → (s : Set K) ⊆ K₁ → ∃ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ : X ⟶ X₁), IsProjOver p₁ ∧ IsPullback φ p p₁ (spMap K₁.subtype))
    (hmor : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) (Z : Scheme.{0}) (q : Z ⟶ Sp K₀) [QuasiCompact p₀] [QuasiSeparated p₀] [LocallyOfFinitePresentation q] (I : Type) [Finite I] (f : I → (X ⟶ Z)), IsPullback φ p p₀ (spMap K₀.subtype) → (∀ j, f j ≫ q = φ ≫ p₀) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁), IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype → ∃ f₁ : I → (X₁ ⟶ Z), ∀ j, ψ ≫ f₁ j = f j ∧ f₁ j ≫ q = φ₁ ≫ p₀)
    (hgrp : ∀ (K : Type) [Field K] (K₀ : Subfield K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ A₀.left) [QuasiCompact A₀.hom] [QuasiSeparated A₀.hom] [LocallyOfFinitePresentation A₀.hom], IsPullback φ A.hom A₀.hom (spMap K₀.subtype) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (A₁ : Over (Sp K₁)) (φ₁ : A₁.left ⟶ A₀.left) (ψ : A.left ⟶ A₁.left), IsPullback φ₁ A₁.hom A₀.hom (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ A₁.hom = A.hom ≫ spMap K₁.subtype → ∃ _ : GrpObj A₁, IsGrpPullback A A₁ (spMap K₁.subtype) ψ)
    (hlb : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) [QuasiCompact p₀] [QuasiSeparated p₀] (L : LB X), L.IsLB → IsPullback φ p p₀ (spMap K₀.subtype) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁), IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype → ∃ L₁ : LB X₁, L₁.IsLB ∧ LBIso L (L₁.pull ψ))
    (hobj : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (β₀ : o →+* K₀) (β : o →+* K) (t : TObj g k J b (spMap β)) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : t.A.left ⟶ A₀.left) (L₀ : LB A₀.left) (pt₀ : Fin (2 * g) → (Out.baseOver (Sp K₀) ⟶ A₀)) (act₀ : J → (A₀ ⟶ A₀)), i.comp β₀ = β → IsGrpPullback t.A A₀ (spMap i) φ → L₀.IsLB → LBIso t.L (L₀.pull φ) → (∀ a, (t.pt a).left ≫ φ = spMap i ≫ (pt₀ a).left) → (∀ j, (t.act j).left ≫ φ = φ ≫ (act₀ j).left) → ∃ t₀ : TObj g k J b (spMap β₀), TMap t t₀ (spMap i)) :
    ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) [Finite J] (K : Type) [Field K] (β : o →+* K) (t : TObj g k J b (spMap β)), ∃ (K₀ : Subfield K) (β₀ : o →+* K₀) (t₀ : TObj g k J b (spMap β₀)), K₀.subtype.comp β₀ = β ∧ (Countable o → Countable K₀) ∧ (∃ s : Finset K, K₀ = Subfield.closure (Set.range β ∪ s)) ∧ TMap t t₀ (spMap K₀.subtype) := by
  intro o _ g k J b _ K _ β t
  classical
  obtain ⟨s₀, H₀⟩ := hproj K (gen β ∅) t.A.left t.A.hom (GlobalTheory.ProjSpace.isProjOver_of_relAmple t.ample)
  obtain ⟨X₀, p₀, φ, hp₀, sq⟩ := H₀ (gen β s₀) (gen_mono β (Finset.empty_subset _)) (subset_gen β le_rfl)
  have : IsProper p₀ := isProper_of_isProjOver hp₀
  have : LocallyOfFinitePresentation p₀ := inferInstance
  have : QuasiCompact (Over.mk p₀).hom := inferInstanceAs (QuasiCompact p₀)
  have : QuasiSeparated (Over.mk p₀).hom := inferInstanceAs (QuasiSeparated p₀)
  have : LocallyOfFinitePresentation (Over.mk p₀).hom := inferInstanceAs (LocallyOfFinitePresentation p₀)
  obtain ⟨s₁, H₁⟩ := hgrp K (gen β s₀) (Over.mk p₀) t.A φ sq
  obtain ⟨s₂, H₂⟩ := hlb K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ t.L t.isLB sq
  obtain ⟨s₃, H₃⟩ := hmor K (gen β s₀) X₀ t.A.left p₀ t.A.hom φ X₀ p₀ J (fun j => (t.act j).left ≫ φ) sq
    (fun j => by rw [Category.assoc, sq.w, ← Category.assoc, Over.w])
  obtain ⟨s₄, H₄⟩ := hmor K (gen β s₀) (Sp (gen β s₀)) (Sp K) (𝟙 _) (𝟙 _) (spMap (gen β s₀).subtype) X₀ p₀
    (Fin (2 * g)) (fun a => (t.pt a).left ≫ φ) (IsPullback.of_vert_isIso ⟨by simp⟩)
    (fun a => by
      have e : (t.pt a).left ≫ t.A.hom = 𝟙 _ := Over.w (t.pt a)
      rw [Category.assoc, sq.w, ← Category.assoc, e]; simp)
  let s : Finset K := s₀ ∪ s₁ ∪ s₂ ∪ s₃ ∪ s₄
  have h : gen β s₀ ≤ gen β s := gen_mono β (fun x hx => by simp [s, hx])
  let inc := spMap (Subfield.inclusion h)
  let A₁ : Over (Sp (gen β s)) := Over.mk (pullback.snd p₀ inc)
  let φ₁ : A₁.left ⟶ X₀ := pullback.fst p₀ inc
  have sq₁ : IsPullback φ₁ A₁.hom p₀ inc := IsPullback.of_hasPullback p₀ inc
  let ψ : t.A.left ⟶ A₁.left := sq₁.lift φ (t.A.hom ≫ spMap (gen β s).subtype)
    (by rw [Category.assoc, spMap_subtype h, sq.w])
  have hψ₁ : ψ ≫ φ₁ = φ := sq₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = t.A.hom ≫ spMap (gen β s).subtype := sq₁.lift_snd _ _ _
  obtain ⟨gr₁, hG⟩ := H₁ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁ φ₁ ψ sq₁ hψ₁ hψ₂
  obtain ⟨L₁, hL₁, hL⟩ := H₂ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨f₁, hf₁⟩ := H₃ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) A₁.left A₁.hom φ₁ ψ
    sq₁ hψ₁ hψ₂
  obtain ⟨x₁, hx₁⟩ := H₄ (gen β s) h (subset_gen β (fun x hx => by simp [s, hx])) (Sp (gen β s)) (𝟙 _) inc
    (spMap (gen β s).subtype) (IsPullback.of_vert_isIso ⟨by simp [inc]⟩) (spMap_subtype h) (by simp)
  let act₁ : J → (A₁ ⟶ A₁) := fun j =>
    Over.homMk (sq₁.lift (f₁ j) A₁.hom (by rw [(hf₁ j).2, sq₁.w])) (sq₁.lift_snd _ _ _)
  let pt₁ : Fin (2 * g) → (Out.baseOver (Sp (gen β s)) ⟶ A₁) := fun a =>
    Over.homMk (sq₁.lift (x₁ a) (𝟙 _) (by rw [(hx₁ a).2]; simp)) (sq₁.lift_snd _ _ _)
  let β₁ : o →+* gen β s := β.codRestrict _ (mem_gen β s)
  have hβ : (gen β s).subtype.comp β₁ = β := rfl
  obtain ⟨t₀, ht₀⟩ := hobj o g k J b (gen β s) K (gen β s).subtype β₁ β t A₁ ψ L₁ pt₁ act₁ hβ hG hL₁ hL
    (fun a => by
      have e : (t.pt a).left ≫ t.A.hom = 𝟙 _ := Over.w (t.pt a)
      have e₁ : (pt₁ a).left ≫ φ₁ = x₁ a := sq₁.lift_fst _ _ _
      have e₂ : (pt₁ a).left ≫ A₁.hom = 𝟙 _ := sq₁.lift_snd _ _ _
      apply sq₁.hom_ext
      · rw [Category.assoc, hψ₁]
        exact ((hx₁ a).1.symm.trans (congrArg _ e₁.symm)).trans (Category.assoc _ _ _).symm
      · rw [Category.assoc, hψ₂, ← Category.assoc, e]
        refine (Category.id_comp _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        exact ((congrArg _ e₂).trans (Category.comp_id _)).symm)
    (fun j => by
      have e₁ : (act₁ j).left ≫ φ₁ = f₁ j := sq₁.lift_fst _ _ _
      apply sq₁.hom_ext
      · rw [Category.assoc, hψ₁, Category.assoc, e₁, (hf₁ j).1]
      · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hψ₂])
  exact ⟨gen β s, β₁, t₀, hβ, fun _ => countable_gen β s, ⟨s, rfl⟩, ht₀⟩

theorem descends_to_fg_subfield :
    ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) [Finite J] (K : Type) [Field K] (β : o →+* K) (t : TObj g k J b (spMap β)), ∃ (K₀ : Subfield K) (β₀ : o →+* K₀) (t₀ : TObj g k J b (spMap β₀)), K₀.subtype.comp β₀ = β ∧ (Countable o → Countable K₀) ∧ (∃ s : Finset K, K₀ = Subfield.closure (Set.range β ∪ s)) ∧ TMap t t₀ (spMap K₀.subtype) :=
  descends_of (@GlobalTheory.T.exists_finset_isProjOver_descends_to_subfield) (@GlobalTheory.T.exists_descent_of_morphisms_to_subfield) (@GlobalTheory.grpObj_descends_to_large_subfield) (@GlobalTheory.T.exists_lineBundle_descent_to_subfield) (@GlobalTheory.exists_thetaObj_of_descended_data)

end GlobalTheory.ThetaDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelShapePrimitivityPullbackDescent
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ShapePull

section Bundles

variable {X X' Y Y' : Scheme.{0}}

theorem iso_linComb_pull {L : LB X} {L' : LB X'} {F : X' ⟶ X} (H : LBIso L' (L.pull F)) {K : Type} [Fintype K]
    (ψ' : K → (Y' ⟶ X')) (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (e : ∀ k, ψ' k ≫ F = h ≫ ψ k) :
    LBIso (LB.LinComb L' ψ' ε) ((LB.LinComb L ψ ε).pull h) := by
  obtain ⟨w, hw⟩ := H
  exact LBIso.chartPull (chartPullId _) (chartPullOut L ψ ε h _ e) (iso_linComb ((isGen_iff w).1 hw) ψ' ε)

theorem iso_up {M N : LB Y} {M' N' : LB Y'} {h : Y' ⟶ Y} (hM : M.IsLB) (hN : N.IsLB) (hM' : M'.IsLB) (hN' : N'.IsLB)
    (a : LBIso M' (M.pull h)) (b : LBIso N' (N.pull h)) (H : LBIso M N) : LBIso M' N' :=
  LBIso.trans hM' (pull_isLB hM h) hN' a (LBIso.trans (pull_isLB hM h) (pull_isLB hN h) hN'
    (H.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M h h rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull N h h rfl)) b.symm)

end Bundles

section Field

variable {K : Type} [Field K] {S' : Scheme.{0}} (f : S' ⟶ Sp K)

theorem exists_point [Nonempty S'] :
    ∃ (K' : Type) (_ : Field K') (i : K →+* K') (x : Sp K' ⟶ S'), x ≫ f = spMap i := by
  obtain ⟨y⟩ := ‹Nonempty S'›
  obtain ⟨i, hi⟩ := Spec.map_surjective (S'.fromSpecResidueField y ≫ f)
  exact ⟨S'.residueField y, inferInstance, i.hom, S'.fromSpecResidueField y, hi.symm⟩

variable {f}

theorem epi_of_isPullback [Nonempty S'] {X₀ X : Scheme.{0}} {p₀ : X₀ ⟶ Sp K} {p : X ⟶ S'} {h : X ⟶ X₀}
    (H : IsPullback h p p₀ f) : Epi h := by
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have a : Flat f := inferInstance
  have b : Surjective f := inferInstance
  have : Flat h := MorphismProperty.of_isPullback (P := @Flat) H.flip a
  have : Surjective h := MorphismProperty.of_isPullback (P := @Surjective) H.flip b
  exact Flat.epi_of_flat_of_surjective h

theorem iso_down [Nonempty S'] {X₀ X : Scheme.{0}} {p₀ : X₀ ⟶ Sp K} {p : X ⟶ S'} {h : X ⟶ X₀}
    (H : IsPullback h p p₀ f) (h₁ : Smooth p₀) (h₂ : IsProper p₀) (h₃ : GeometricallyConnected p₀)
    {M N : LB X₀} {M' N' : LB X} (hM : M.IsLB) (hN : N.IsLB) (hM' : M'.IsLB) (hN' : N'.IsLB)
    (a : LBIso M' (M.pull h)) (b : LBIso N' (N.pull h)) (c : LBIso M' N') : LBIso M N := by
  obtain ⟨K', _, i, x, hx⟩ := exists_point f
  have P : IsPullback (pullback.fst p x ≫ h) (pullback.snd p x) p₀ (spMap i) :=
    hx ▸ (IsPullback.of_hasPullback p x).paste_horiz H
  have d : LBIso (M.pull h) (N.pull h) := LBIso.trans (pull_isLB hM h) hM' (pull_isLB hN h) a.symm
    (LBIso.trans hM' hN' (pull_isLB hN h) c b)
  exact (GlobalTheory.T.lineBundle_trivial_iso_descend_field K K' i X₀ _ p₀ _ _ h₁ h₂ h₃ P).2 M N hM hN (d.chartPull
    (chartPullSame M _ _ _ (pullback.fst p x) fun _ => rfl) (chartPullSame N _ _ _ (pullback.fst p x) fun _ => rfl))

theorem relAmple_down [Nonempty S'] {A : Over (Sp K)} [GrpObj A] (hA : IsAbelianScheme A) {A' : Over S'}
    {φ : A'.left ⟶ A.left} (H : IsPullback φ A'.hom A.hom f) {M : LB A.left} {M' : LB A'.left} (hM : M.IsLB)
    (hM' : M'.IsLB) (a : LBIso M' (M.pull φ)) (c : Out.RelAmple A' M') : Out.RelAmple A M := by
  obtain ⟨K', _, i, x, hx⟩ := exists_point f
  have : IsProper A'.hom := MorphismProperty.of_isPullback (P := @IsProper) H hA.proper
  have P : IsPullback (pullback.fst A.hom (spMap i)) (pullback.snd A.hom (spMap i)) A.hom (x ≫ f) :=
    hx ▸ IsPullback.of_hasPullback A.hom (spMap i)
  let ψ : pullback A.hom (spMap i) ⟶ A'.left := H.lift (pullback.fst _ _) (pullback.snd _ _ ≫ x)
    (P.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ φ = pullback.fst _ _ := H.lift_fst _ _ _
  have Q : IsPullback ψ (pullback.snd A.hom (spMap i)) A'.hom x :=
    IsPullback.of_right (hψ ▸ P) (H.lift_snd _ _ _) H
  exact GlobalTheory.T.relAmple_of_fieldExtension_baseChange K K' i A ((Over.pullback (spMap i)).obj A) (pullback.fst _ _) M (M'.pull ψ) hA
    (isGrpPullback_pullback A _) hM (pull_isLB hM' ψ)
    (a.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M' ψ ψ rfl) (chartPullSame M _ _ _ ψ fun _ => hψ.symm))
    (AmpleBaseChange.relAmple_of_isPullback hM' c Q)

end Field

section Group

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
  (h : IsGrpPullback G' G f φ)

section Points

variable {T : Over S} {T' : Over S'} (U : Over.mk (T'.hom ≫ f) ⟶ T)

theorem eq_up {x' y' : T' ⟶ G'} {x y : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x) (hy : pushPt h.1.w y' = U ≫ y)
    (e : x = y) : x' = y' :=
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) (hx.trans (e ▸ hy.symm))) (by rw [Over.w, Over.w]))

theorem eq_down (hU : Epi U.left) {x' y' : T' ⟶ G'} {x y : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x)
    (hy : pushPt h.1.w y' = U ≫ y) (e : x' = y') : x = y :=
  Over.OverMorphism.ext ((cancel_epi U.left).1 (congrArg (fun q => q.left) (hx.symm.trans (e ▸ hy))))

theorem push_mul {x' y' : T' ⟶ G'} {x y : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x) (hy : pushPt h.1.w y' = U ≫ y) :
    pushPt h.1.w (x' * y') = U ≫ (x * y) :=
  (map_mul (pushHom h T') x' y').trans ((congrArg₂ (· * ·) hx hy).trans (MonObj.comp_mul U x y).symm)

theorem push_linComb {n : ℕ} {x' : Fin n → (T' ⟶ G')} {x : Fin n → (T ⟶ G)} (hx : ∀ i, pushPt h.1.w (x' i) = U ≫ x i)
    (a : Fin n → ℕ) : pushPt h.1.w (Out.linComb x' a) = U ≫ Out.linComb x a := by
  refine (map_list_prod (pushHom h T') _).trans (Eq.trans ?_ (map_list_prod (preHom (G := G) U) _).symm)
  rw [List.map_ofFn, List.map_ofFn]
  refine congrArg (fun z => (List.ofFn z).prod) (funext fun i => ?_)
  exact (map_pow (pushHom h T') _ _).trans ((congrArg (· ^ a i) (hx i)).trans (map_pow (preHom (G := G) U) _ _).symm)

theorem push_comp {x' : T' ⟶ G'} {x : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x) {a' : G' ⟶ G'} {a : G ⟶ G}
    (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w (x' ≫ a') = U ≫ x ≫ a := by
  rw [← Category.assoc, ← hx]
  refine Over.OverMorphism.ext ?_
  show (x'.left ≫ _) ≫ _ = (x'.left ≫ _) ≫ _
  rw [Category.assoc, ha, Category.assoc]

theorem iso_cubeLB_pull [IsCommMonObj G] [IsCommMonObj G'] {L : LB G.left} {L' : LB G'.left}
    (H : LBIso L' (L.pull φ)) {a' b' : T' ⟶ G'} {a b : T ⟶ G} (ha : pushPt h.1.w a' = U ≫ a)
    (hb : pushPt h.1.w b' = U ≫ b) : LBIso (cubeLB G' ![a', b'] L') ((cubeLB G ![a, b] L).pull U.left) :=
  iso_linComb_pull H _ _ _ U.left fun I => psum_push h _ _ U (fun i => by
    fin_cases i
    exacts [ha, hb]) I.down

end Points

def sqMap : Over.mk ((G' ⊗ G').hom ≫ f) ⟶ G ⊗ G := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))

theorem push_fst : pushPt h.1.w (fst G' G') = sqMap h ≫ fst G G := (lift_fst _ _).symm

theorem push_snd : pushPt h.1.w (snd G' G') = sqMap h ≫ snd G G := (lift_snd _ _).symm

theorem isPullback_sqMap : IsPullback (sqMap h).left (G' ⊗ G').hom (G ⊗ G).hom f := by
  have e₁ : (sqMap h).left ≫ (fst G G).left = (fst G' G').left ≫ φ := congrArg (fun q => q.left) (push_fst h).symm
  have e₂ : (sqMap h).left ≫ (snd G G).left = (snd G' G').left ≫ φ := congrArg (fun q => q.left) (push_snd h).symm
  have A : IsPullback (snd G G).left (fst G G).left G.hom G.hom := (IsPullback.of_hasPullback G.hom G.hom).flip
  have A' : IsPullback (snd G' G').left (fst G' G').left G'.hom G'.hom := (IsPullback.of_hasPullback G'.hom G'.hom).flip
  have B := A'.paste_horiz h.1
  rw [← e₂, ← h.1.w] at B
  have C := (IsPullback.of_right B e₁ A).paste_vert h.1
  rwa [Over.w, Over.w] at C

def selfMap : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w

theorem push_id : pushPt h.1.w (𝟙 G') = selfMap h ≫ 𝟙 G :=
  Over.OverMorphism.ext ((Category.id_comp _).trans (Category.comp_id _).symm)

theorem push_end {a' : G' ⟶ G'} {a : G ⟶ G} (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w a' = selfMap h ≫ a :=
  Over.OverMorphism.ext ha

end Group

def baseMap {S S' : Scheme.{0}} (f : S' ⟶ S) : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S :=
  Over.homMk f ((Category.comp_id _).trans (Category.id_comp _).symm)

end GlobalTheory.ShapePull

namespace GlobalTheory

open ShapePull

theorem shape_prim_pull_and_descend :
    ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) Mat κ (w w' : J) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s) (t' : TObj g k J b s'), TMap t' t f → (t.Shape Mat κ → t'.Shape Mat κ) ∧ (t.Prim w w' → t'.Prim w w') ∧ ∀ (K : Type) [Field K] (e : S = Sp K), IsAffine S' → Nonempty S' → (t'.Shape Mat κ → t.Shape Mat κ) ∧ (IsIntegral S' → t'.Prim w w' → t.Prim w w') := by
  intro o _ g k J b Mat κ w w' S S' s s' f t t' ⟨φ, h, hL, hpt, hact⟩
  letI := t.ab.comm
  letI := t'.ab.comm
  have lb : ∀ {X Y : Scheme.{0}} {L : LB X} (_ : L.IsLB) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ),
      (LB.LinComb L ψ ε).IsLB := fun hL _ _ _ _ => DVR.linComb_isLB _ hL _ _
  have pt : ∀ i, pushPt h.1.w (t'.pt i) = baseMap f ≫ t.pt i := fun i => Over.OverMorphism.ext (hpt i)
  have p₁ := fun i j => push_comp h _ (pt i) (hact j)
  have p₂ : ∀ a, pushPt h.1.w (t'.lab a) = baseMap f ≫ t.lab a := fun a => push_linComb h _ pt _
  have i₁ : ∀ j, LBIso (LB.LinComb t'.L (K := Fin 2) ![𝟙 t'.A.left, (t'.act j).left] ![(κ : ℤ), -1])
      ((LB.LinComb t.L (K := Fin 2) ![𝟙 t.A.left, (t.act j).left] ![(κ : ℤ), -1]).pull φ) := fun j =>
    iso_linComb_pull hL _ _ _ φ fun i => by
      fin_cases i
      exacts [(Category.id_comp _).trans (Category.comp_id _).symm, hact j]
  have p₃ := push_mul h _ (push_end h (hact w)) (push_end h (hact w'))
  have i₂ := iso_cubeLB_pull h _ hL (push_comp h _ (push_fst h) (hact w)) (push_snd h)
  have i₃ := iso_cubeLB_pull h _ hL (push_fst h) (push_comp h _ (push_snd h) (hact w'))
  have i₄ := iso_cubeLB_pull h _ hL (push_id h) (push_end h (hact w))
  refine ⟨fun H j => ⟨fun i => eq_up h _ (p₁ i j) (p₂ _) ((H j).1 i), ?_⟩, fun H => ⟨eq_up h _ p₃ (push_id h) H.1,
    iso_up (lb t.isLB _ _) (lb t.isLB _ _) (lb t'.isLB _ _) (lb t'.isLB _ _) i₂ i₃ H.2.1,
    iso_up t.isLB (lb t.isLB _ _) t'.isLB (lb t'.isLB _ _) hL i₄ H.2.2⟩, ?_⟩
  · exact (pol_pull S S' t.A t'.A f φ _ _ (lb t.isLB _ _) (lb t'.isLB _ _) t.ab h (i₁ j)).2.1 (H j).2
  rintro K _ rfl - _
  have hf : Epi f := epi_of_isPullback (IsPullback.id_vert f)
  have hφ : Epi φ := epi_of_isPullback h.1
  have := t.ab.smooth
  have := t.ab.proper
  have := t.ab.geomConnected
  have pr : IsProper (t.A ⊗ t.A).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  exact ⟨fun H j => ⟨fun i => eq_down h _ hf (p₁ i j) (p₂ _) ((H j).1 i),
      relAmple_down t.ab h.1 (lb t.isLB _ _) (lb t'.isLB _ _) (i₁ j) (H j).2⟩,
    fun _ H => ⟨eq_down h _ hφ p₃ (push_id h) H.1,
      iso_down (isPullback_sqMap h) (smooth_tensorObj_hom _ _) pr (geometricallyConnected_tensorObj_hom _ _)
        (lb t.isLB _ _) (lb t.isLB _ _) (lb t'.isLB _ _) (lb t'.isLB _ _) i₂ i₃ H.2.1,
      iso_down h.1 ‹_› ‹_› ‹_› t.isLB (lb t.isLB _ _) t'.isLB (lb t'.isLB _ _) hL i₄ H.2.2⟩⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TransitionFramesPushOpenImmersionImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ModelSum

theorem appIso_inv_topIso_inv {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (W' : Z'.Opens) (W : Z.Opens)
    (hle : W ≤ f ''ᵁ W') (v : W'.toScheme ⟶ W.toScheme) (hv : v ≫ W.ι = W'.ι ≫ f) :
    (f.appIso W').inv ≫ Z.presheaf.map (homOfLE hle).op ≫ W.topIso.inv ≫ v.appTop = W'.topIso.inv := by
  have e : W.topIso.inv = W.ι.appLE W ⊤ (by simp) := (Scheme.Opens.ι_appLE W W ⊤ _).symm
  have e' : W'.topIso.inv = W'.ι.appLE W' ⊤ (by simp) := (Scheme.Opens.ι_appLE W' W' ⊤ _).symm
  have e₂ : v.appTop = v.appLE ⊤ ⊤ (le_top (a := ⊤) |>.trans (Scheme.Hom.preimage_top v).ge) := (Scheme.Hom.appLE_eq_app v).symm
  rw [Iso.inv_comp_eq, Scheme.Hom.appIso_hom', e, e', e₂, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.map_appLE]
  simp only [hv]

theorem exists_iso_image {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (W' : Z'.Opens) (W : Z.Opens)
    (h : W = f ''ᵁ W') : ∃ v : W'.toScheme ≅ W.toScheme, v.hom ≫ W.ι = W'.ι ≫ f := by
  subst h
  exact ⟨f.isoImage W', Scheme.Hom.isoImage_hom_ι f W'⟩

theorem appTop_hom_inv {X Y : Scheme.{0}} (v : X ≅ Y) (a : Γ(X, ⊤)) :
    v.hom.appTop.hom (v.inv.appTop.hom a) = a := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, v.hom_inv_id, Scheme.Hom.id_appTop]; rfl

theorem appTop_inv_hom {X Y : Scheme.{0}} (v : X ≅ Y) (a : Γ(Y, ⊤)) :
    v.inv.appTop.hom (v.hom.appTop.hom a) = a := appTop_hom_inv v.symm a

theorem exists_transport {Z Z' : Scheme.{0}} {G : Over Z} {G' : Over Z'} {f : Z' ⟶ Z} {φ : G'.left ⟶ G.left}
    {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) (hφ : IsPullback φ G'.hom G.hom f)
    (hw : LBIso L' (L.pull φ)) (N : ℕ) :
    ∃ e : ∀ {X' X : Scheme.{0}} (a' : X' ⟶ Z') (a : X ⟶ Z) (u : X' ≅ X), u.hom ≫ a = a' ≫ f →
      LB.Sec (Out.LPow G' L' (N : ℤ) (Over.mk a')) → LB.Sec (Out.LPow G L (N : ℤ) (Over.mk a)),
    (∀ {X₁' X₂' X₁ X₂ : Scheme.{0}} {a₁' : X₁' ⟶ Z'} {a₂' : X₂' ⟶ Z'} {a₁ : X₁ ⟶ Z} {a₂ : X₂ ⟶ Z}
      (u₁ : X₁' ≅ X₁) (u₂ : X₂' ≅ X₂) (h₁ : u₁.hom ≫ a₁ = a₁' ≫ f) (h₂ : u₂.hom ≫ a₂ = a₂' ≫ f)
      (k' : X₂' ⟶ X₁') (k : X₂ ⟶ X₁) (hk' : k' ≫ a₁' = a₂') (hk : k ≫ a₁ = a₂), k' ≫ u₁.hom = u₂.hom ≫ k →
      ∀ (n : ℕ) (b : Fin n → LB.Sec (Out.LPow G' L' (N : ℤ) (Over.mk a₁'))) (c' : Fin n → Γ(X₂', ⊤))
        (c : Fin n → Γ(X₂, ⊤)), (∀ i, u₂.hom.appTop.hom (c i) = c' i) →
        ∀ s : LB.Sec (Out.LPow G' L' (N : ℤ) (Over.mk a₂')),
        Lin G' L' N (Over.homMk k' hk' : Over.mk a₂' ⟶ Over.mk a₁') b c' s →
          Lin G L N (Over.homMk k hk : Over.mk a₂ ⟶ Over.mk a₁) (fun i => e a₁' a₁ u₁ h₁ (b i)) c (e a₂' a₂ u₂ h₂ s)) ∧
    ∀ {X₁' X₁ Y : Scheme.{0}} {a₁' : X₁' ⟶ Z'} {a₁ : X₁ ⟶ Z} (u₁ : X₁' ≅ X₁) (h₁ : u₁.hom ≫ a₁ = a₁' ≫ f)
      (χ : Y ⟶ X₁) (n : ℕ) (b : Fin n → LB.Sec (Out.LPow G' L' (N : ℤ) (Over.mk a₁'))),
      BasisAlong G' L' N (Over.homMk (χ ≫ u₁.inv) rfl : Over.mk ((χ ≫ u₁.inv) ≫ a₁') ⟶ Over.mk a₁') b →
        BasisAlong G L N (Over.homMk χ rfl : Over.mk (χ ≫ a₁) ⟶ Over.mk a₁) (fun i => e a₁' a₁ u₁ h₁ (b i)) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_sectionPower_transport_cartesian_square Z Z' G G' f φ L L' hL hL' hφ hw N
  refine ⟨fun a' a u h => e (Over.mk a') (Over.mk a) u h, ?_, ?_⟩
  · intro X₁' X₂' X₁ X₂ a₁' a₂' a₁ a₂ u₁ u₂ h₁ h₂ k' k hk' hk hc n b c' c hcc s H
    obtain rfl : c' = fun i => u₂.hom.appTop.hom (c i) := funext fun i => (hcc i).symm
    exact (he (Over.mk a₁') (Over.mk a₂') (Over.mk a₁) (Over.mk a₂) u₁ u₂ h₁ h₂ (Over.homMk k' hk') (Over.homMk k hk)
      hc n b c s).1 H
  · intro X₁' X₁ Y a₁' a₁ u₁ h₁ χ n b B σ
    have hc' : (Iso.refl Y).hom ≫ χ ≫ a₁ = ((χ ≫ u₁.inv) ≫ a₁') ≫ f := by
      simp [← h₁]
    have hk : (χ ≫ u₁.inv) ≫ u₁.hom = (Iso.refl Y).hom ≫ χ := by simp
    have hid : ∀ a : Γ(Y, ⊤), (Iso.refl Y).hom.appTop.hom a = a := fun a => by simp
    obtain ⟨σ', rfl⟩ := (e (Over.mk ((χ ≫ u₁.inv) ≫ a₁')) (Over.mk (χ ≫ a₁)) (Iso.refl Y) hc').surjective σ
    refine (existsUnique_congr fun c => ?_).1 (B σ')
    refine Iff.trans ?_ (he (Over.mk a₁') (Over.mk ((χ ≫ u₁.inv) ≫ a₁')) (Over.mk a₁)
      (Over.mk (χ ≫ a₁)) u₁ (Iso.refl Y) h₁ hc' (Over.homMk (χ ≫ u₁.inv) rfl) (Over.homMk χ rfl) hk n b c σ')
    exact iff_of_eq (congrArg (fun c => Lin G' L' N _ b c σ') (funext fun k => (hid (c k)).symm))

theorem unit_rel_push {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (W' : Z'.Opens) (W : Z.Opens)
    (hle : W ≤ f ''ᵁ W') (v : W'.toScheme ≅ W.toScheme) (hv : v.hom ≫ W.ι = W'.ι ≫ f) {n : ℕ} (r s : ℤ)
    (g : Γ(Z', W')) (c : Γ(W'.toScheme, ⊤)ˣ) (M : GL (Fin n) Γ(W'.toScheme, ⊤))
    (hg : W'.topIso.inv.hom g = (c ^ r * Matrix.GeneralLinearGroup.det M ^ s).val) :
    W.topIso.inv.hom ((Z.presheaf.map (homOfLE hle).op).hom ((f.appIso W').inv.hom g)) =
      (Units.map v.inv.appTop.hom.toMonoidHom c ^ r *
        Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map v.inv.appTop.hom M) ^ s).val := by
  have E : v.hom.appTop.hom (W.topIso.inv.hom ((Z.presheaf.map (homOfLE hle).op).hom ((f.appIso W').inv.hom g))) =
      W'.topIso.inv.hom g := congrArg (fun k => k.hom g) (appIso_inv_topIso_inv f W' W hle v.hom hv)
  have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map v.inv.appTop.hom M) =
      Units.map v.inv.appTop.hom.toMonoidHom (Matrix.GeneralLinearGroup.det M) :=
    Units.ext (RingHom.map_det v.inv.appTop.hom M.val).symm
  rw [hd, ← map_zpow, ← map_zpow, ← map_mul]
  exact (appTop_inv_hom v _).symm.trans (congrArg v.inv.appTop.hom (E.trans hg))

theorem hasFrames_pushLB : ∀ (Z Z' : Scheme.{0}) (G : Over Z) (G' : Over Z') (f : Z' ⟶ Z) [IsOpenImmersion f] (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsPullback φ G'.hom G.hom f → LBIso L' (L.pull φ) → f ⁻¹' abLocus G ⊆ abLocus G' → ∀ (N : ℕ) (A : LB Z') (n : ℕ) (r s : ℤ), HasFrames G' L' N A n r s → HasFrames G L N (pushLB f A) n r s := by
  intro Z Z' G G' f _ φ L L' hL hL' hφ hw hab N A n r s ⟨th, b, h₁, h₂⟩
  obtain ⟨e₁, he₁, hb₁⟩ := exists_transport hL hL' hφ hw 1
  obtain ⟨eN, heN, hbN⟩ := exists_transport hL hL' hφ hw N
  choose u hu using fun i : A.ι => exists_iso_image f (A.U i) (f ''ᵁ A.U i) rfl
  refine ⟨fun i => e₁ (A.U i).ι (f ''ᵁ A.U i).ι (u i) (hu i) (th i),
    fun i k => eN (A.U i).ι (f ''ᵁ A.U i).ι (u i) (hu i) (b i k), fun (i j : A.ι) => ?_,
    fun (i : A.ι) W _ _ _ hW (χ : Sp W ⟶ (f ''ᵁ A.U i).toScheme) hχ => ?_⟩
  · obtain ⟨c, M, ⟨t, ht, ht'⟩, hb, hg⟩ := h₁ i j
    obtain ⟨v, hv⟩ := exists_iso_image f (A.U i ⊓ A.U j) (f ''ᵁ A.U i ⊓ f ''ᵁ A.U j)
      (le_antisymm (image_inf_le f _ _) (le_inf (f.image_mono inf_le_left) (f.image_mono inf_le_right)))
    have ki : Z'.homOfLE (inf_le_left : A.U i ⊓ A.U j ≤ A.U i) ≫ (u i).hom =
        v.hom ≫ Z.homOfLE (inf_le_left : f ''ᵁ A.U i ⊓ f ''ᵁ A.U j ≤ _) := by
      rw [← cancel_mono (f ''ᵁ A.U i).ι, Category.assoc, Category.assoc, hu, Scheme.homOfLE_ι, hv, Scheme.homOfLE_ι_assoc]
    have kj : Z'.homOfLE (inf_le_right : A.U i ⊓ A.U j ≤ A.U j) ≫ (u j).hom =
        v.hom ≫ Z.homOfLE (inf_le_right : f ''ᵁ A.U i ⊓ f ''ᵁ A.U j ≤ _) := by
      rw [← cancel_mono (f ''ᵁ A.U j).ι, Category.assoc, Category.assoc, hu, Scheme.homOfLE_ι, hv, Scheme.homOfLE_ι_assoc]
    refine ⟨Units.map v.inv.appTop.hom.toMonoidHom c, Matrix.GeneralLinearGroup.map v.inv.appTop.hom M,
      ⟨e₁ (A.U i ⊓ A.U j).ι (f ''ᵁ A.U i ⊓ f ''ᵁ A.U j).ι v hv t, ?_, ?_⟩, fun k => ?_, ?_⟩
    · exact he₁ (u i) v (hu i) hv _ _ _ (Scheme.homOfLE_ι _ _) ki 1 (fun _ => th i) (fun _ => 1) (fun _ => 1)
        (fun _ => map_one _) t ht
    · exact he₁ (u j) v (hu j) hv _ _ _ (Scheme.homOfLE_ι _ _) kj 1 (fun _ => th j) (fun _ => c.val)
        (fun _ => v.inv.appTop.hom c.val) (fun _ => appTop_hom_inv v _) t ht'
    · obtain ⟨t, ht, ht'⟩ := hb k
      refine ⟨eN (A.U i ⊓ A.U j).ι (f ''ᵁ A.U i ⊓ f ''ᵁ A.U j).ι v hv t, ?_, ?_⟩
      · exact heN (u i) v (hu i) hv _ _ _ (Scheme.homOfLE_ι _ _) ki 1 (fun _ => b i k) (fun _ => 1) (fun _ => 1)
          (fun _ => map_one _) t ht
      · exact heN (u j) v (hu j) hv _ _ _ (Scheme.homOfLE_ι _ _) kj n (b j) (fun k' => M.val k k')
          (fun k' => v.inv.appTop.hom (M.val k k')) (fun _ => appTop_hom_inv v _) t ht'
    · exact unit_rel_push f (A.U i ⊓ A.U j) _ (image_inf_le f _ _) v hv r s _ c M hg
  · have hc : ((Out.jK W ≫ (χ ≫ (u i).inv) ≫ (A.U i).ι) ≫ f) = Out.jK W ≫ χ ≫ (f ''ᵁ A.U i).ι := by
      simp only [Category.assoc]; rw [← hu i, Iso.inv_hom_id_assoc]
    obtain ⟨B₁, BN⟩ := h₂ i W hW (χ ≫ (u i).inv) (by
      rintro _ ⟨x, rfl⟩
      refine hab (hχ ⟨x, ?_⟩)
      exact (congrArg (fun k => k x) hc).symm.trans (Scheme.Hom.comp_apply _ _ _))
    exact ⟨hb₁ (u i) (hu i) χ 1 (fun _ => th i) B₁, hbN (u i) (hu i) χ n (b i) BN⟩

end GlobalTheory.ModelSum

end
end

