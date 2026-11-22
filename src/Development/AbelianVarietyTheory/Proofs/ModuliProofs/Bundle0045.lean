import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0018
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.OActDescendOfGenerators
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ActDescent

variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j] in
theorem _root_.GlobalTheory.ActDescent.over_hom_ext {X Y : Over S} {X' : Scheme.{0}} {φ : X' ⟶ X.left} {p : X' ⟶ U}
    (h : IsPullback φ p X.hom j) {f g : X ⟶ Y} (hfg : φ ≫ f.left = φ ≫ g.left) : f = g := by
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) h.flip ‹Flat j›
  have : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹Surjective j›
  have := Flat.epi_of_flat_of_surjective φ
  exact Over.OverMorphism.ext ((cancel_epi φ).mp hfg)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j] in
omit [Flat j] [Surjective j] in
theorem _root_.GlobalTheory.ActDescent.pullback_map_left_fst {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback j).map a).left ≫ pullback.fst Y.hom j = pullback.fst X.hom j ≫ a.left := by
  exact pullback.lift_fst _ _ _

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j] in
variable (j) in
theorem _root_.GlobalTheory.ActDescent.pullback_map_injective (X Y : Over S) :
    Function.Injective ((Over.pullback j).map : (X ⟶ Y) → _) := by
  intro a b hab
  apply _root_.GlobalTheory.ActDescent.over_hom_ext (IsPullback.of_hasPullback X.hom j)
  rw [← _root_.GlobalTheory.ActDescent.pullback_map_left_fst, ← _root_.GlobalTheory.ActDescent.pullback_map_left_fst, hab]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j] in
private theorem mul_comp_of_descends_monHom {G H : Over S} [GrpObj G] [GrpObj H]
    {G' H' : Over U} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hG : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G j φ) (hH : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback H' H j ψ) (f' : G' ⟶ H') [IsMonHom f'] (f : G ⟶ H)
    (hf : f'.left ≫ ψ = φ ≫ f.left) (T : Over S) (x y : T ⟶ G) :
    (x * y) ≫ f = x ≫ f * y ≫ f := by
  have hT : IsPullback (pullback.fst T.hom j) (pullback.snd T.hom j) T.hom j :=
    IsPullback.of_hasPullback _ _
  apply _root_.GlobalTheory.ActDescent.over_hom_ext hT
  let T' : Over U := (Over.pullback j).obj T
  let ρ : Over.mk (T'.hom ≫ j) ⟶ T :=
    Over.homMk (pullback.fst T.hom j) (by simp [T', pullback.condition])
  let up : (T ⟶ G) → (T' ⟶ G') := fun z => Over.homMk
    (hG.1.lift (pullback.fst T.hom j ≫ z.left) T'.hom (by simp [T', pullback.condition]))
    (hG.1.lift_snd _ _ _)
  have hup : ∀ z : T ⟶ G, (up z).left ≫ φ = pullback.fst T.hom j ≫ z.left :=
    fun z => hG.1.lift_fst _ _ _
  have hpush : ∀ z : T ⟶ G, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hG T' (up z) = ρ ≫ z :=
    fun z => Over.OverMorphism.ext (by exact hup z)
  have hpushH : ∀ z : T ⟶ G, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hH T' (up z ≫ f') = ρ ≫ z ≫ f := by
    intro z
    ext1
    change ((up z).left ≫ f'.left) ≫ ψ = pullback.fst T.hom j ≫ z.left ≫ f.left
    rw [Category.assoc, hf, ← Category.assoc, hup, Category.assoc]
  change (ρ ≫ (x * y) ≫ f).left = (ρ ≫ (x ≫ f * y ≫ f)).left
  rw [MonObj.comp_mul ρ (x ≫ f), ← hpushH x, ← hpushH y, ← map_mul, ← MonObj.mul_comp,
    ← Category.assoc, MonObj.comp_mul ρ x y, ← hpush x, ← hpush y, ← map_mul]
  change ((up x * up y).left ≫ φ) ≫ f.left = ((up x * up y) ≫ f').left ≫ ψ
  rw [Over.comp_left, Category.assoc, Category.assoc, hf]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j] in

theorem _root_.GlobalTheory.ActDescent.isMonHom_descend {G H : Over S} [GrpObj G] [GrpObj H]
    {G' H' : Over U} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hG : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G j φ) (hH : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback H' H j ψ) (f' : G' ⟶ H') [IsMonHom f'] (f : G ⟶ H)
    (hf : f'.left ≫ ψ = φ ≫ f.left) : IsMonHom f := by
  have key := mul_comp_of_descends_monHom hG hH f' f hf
  refine ⟨?_, ?_⟩
  · have h1 : (1 : 𝟙_ (Over S) ⟶ G) ≫ f = 1 := by
      have h := key (𝟙_ (Over S)) 1 1
      rw [_root_.one_mul] at h
      exact mul_eq_left.mp h.symm
    simpa [Hom.one_def] using h1
  · have h := key _ (fst G G) (snd G G)
    simpa [Hom.mul_def] using h

omit [Flat j] [Surjective j] in

theorem exists_descend {O : Type} [CommRing O] {G : Over S} [GrpObj G] {G' : Over U} [GrpObj G']
    {φ : G'.left ⟶ G.left} (hG : IsGrpPullback G' G j φ) (i : OAct O G') {s : Set O}
    (hs : Subring.closure s = ⊤) (hi : ∀ x ∈ s, ∃ f : G ⟶ G, (i.act x).left ≫ φ = φ ≫ f.left) (c : O) :
    ∃ f : G ⟶ G, (i.act c).left ≫ φ = φ ≫ f.left := by
  let φ₀ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ hG.1.w
  let ρ := pushHom hG G'
  have key : ∀ (x : G' ⟶ G') (f : G ⟶ G), x.left ≫ φ = φ ≫ f.left ↔ ρ x = φ₀ ≫ f := fun x f =>
    ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (fun z => z.left) h⟩
  have h0 : i.act 0 = 1 := by
    have := i.add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hneg : ∀ x, i.act (-x) = (i.act x)⁻¹ := fun x =>
    eq_inv_of_mul_eq_one_left (by rw [← i.add, neg_add_cancel, h0])
  have hc : c ∈ Subring.closure s := hs ▸ Subring.mem_top c
  induction hc using Subring.closure_induction with
  | mem x hx => exact hi x hx
  | zero => exact ⟨1, (key _ _).2 (by rw [h0, map_one, MonObj.comp_one])⟩
  | one => exact ⟨𝟙 _, by rw [i.one, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, hf⟩ := hx
    obtain ⟨g, hg⟩ := hy
    exact ⟨f * g, (key _ _).2 (by rw [i.add, map_mul, MonObj.comp_mul, (key _ _).1 hf, (key _ _).1 hg])⟩
  | neg x _ hx =>
    obtain ⟨f, hf⟩ := hx
    exact ⟨f⁻¹, (key _ _).2 (by rw [hneg, map_inv, GrpObj.comp_inv, (key _ _).1 hf])⟩
  | mul x y _ _ hx hy =>
    obtain ⟨f, hf⟩ := hx
    obtain ⟨g, hg⟩ := hy
    exact ⟨f ≫ g, by
      rw [i.mul, Over.comp_left, Over.comp_left, Category.assoc, hg, ← Category.assoc, hf, Category.assoc]⟩

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j] in

theorem _root_.GlobalTheory.ActDescent.exists_oAct {O : Type} [CommRing O] {G : Over S} [GrpObj G]
    {G' : Over U} [GrpObj G'] {φ : G'.left ⟶ G.left} (hG : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G j φ)
    (i : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G') (hi : ∀ x, ∃ f : G ⟶ G, (i.act x).left ≫ φ = φ ≫ f.left) :
    ∃ a : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G, ∀ x, (i.act x).left ≫ φ = φ ≫ (a.act x).left := by
  choose g hg using hi
  have hpb := hG.1
  have hmon : ∀ x, IsMonHom (g x) := fun x =>
    haveI := i.hom x
    _root_.GlobalTheory.ActDescent.isMonHom_descend hG hG (i.act x) (g x) (hg x)
  refine ⟨⟨g, hmon, ?_, ?_, ?_⟩, hg⟩
  · apply _root_.GlobalTheory.ActDescent.over_hom_ext hpb
    rw [← hg, i.one]
    simp
  · intro a b
    apply _root_.GlobalTheory.ActDescent.over_hom_ext hpb
    rw [← hg, i.mul, Over.comp_left, Over.comp_left, Category.assoc, hg, ← Category.assoc, hg,
      Category.assoc]
  · intro a b
    apply _root_.GlobalTheory.ActDescent.over_hom_ext hpb
    let ρ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ hpb.w
    have hpush : ∀ c, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hG G' (i.act c) = ρ ≫ g c :=
      fun c => Over.OverMorphism.ext (by exact hg c)
    change (ρ ≫ g (a + b)).left = (ρ ≫ (g a * g b)).left
    rw [MonObj.comp_mul, ← hpush, ← hpush, ← hpush, ← map_mul, i.add]

end GlobalTheory.ActDescent

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
variable {U S : Scheme.{0}} {j : U ⟶ S} [Flat j] [Surjective j] in

theorem _root_.GlobalTheory.oAct_descend_of_generators : ∀ (O : Type) [CommRing O] (J : Type) (a : J → O) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K₀)) (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A₀] [GrpObj A] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O A) (act₀ : J → (A₀ ⟶ A₀)), Subring.closure (Set.range a) = ⊤ → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A A₀ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap i) φ → (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left) → ∃ r : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O A₀, (∀ j, r.act (a j) = act₀ j) ∧ ∀ c, (act.act c).left ≫ φ = φ ≫ (r.act c).left := by
  intro O _ J a K₀ K _ _ i A₀ A _ _ _ φ act act₀ hgen hG hact
  haveI : Flat (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap i) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap; infer_instance
  haveI : Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap i) := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap; infer_instance
  let ρ : Over.mk (A.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap i) ⟶ A₀ := Over.homMk φ hG.1.w
  have hiff : ∀ (z : A ⟶ A) (g : A₀ ⟶ A₀), z.left ≫ φ = φ ≫ g.left →
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hG A z = ρ ≫ g := fun z g h => Over.OverMorphism.ext (by exact h)
  have hback : ∀ (z : A ⟶ A) (g : A₀ ⟶ A₀), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hG A z = ρ ≫ g →
      z.left ≫ φ = φ ≫ g.left := fun z g h => by
    have h' := congrArg (fun m => m.left) h
    exact h'
  have h0 : act.act 0 = 1 := by
    have h := act.add 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hD : ∀ c, ∃ g : A₀ ⟶ A₀, (act.act c).left ≫ φ = φ ≫ g.left := by
    intro c
    have hc : c ∈ Subring.closure (Set.range a) := hgen ▸ Subring.mem_top c
    induction hc using Subring.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨act₀ k, hact k⟩
    | zero =>
      refine ⟨1, hback _ _ ?_⟩
      rw [h0, map_one, MonObj.comp_one]
    | one =>
      exact ⟨𝟙 _, by simp [act.one]⟩
    | add x y _ _ hx hy =>
      obtain ⟨g, hg⟩ := hx
      obtain ⟨g', hg'⟩ := hy
      refine ⟨g * g', hback _ _ ?_⟩
      rw [act.add, map_mul, hiff _ _ hg, hiff _ _ hg', MonObj.comp_mul]
    | neg x _ hx =>
      obtain ⟨g, hg⟩ := hx
      have hneg : act.act (-x) = (act.act x)⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        rw [← act.add, add_neg_cancel, h0]
      refine ⟨g⁻¹, hback _ _ ?_⟩
      rw [hneg, map_inv, hiff _ _ hg, GrpObj.comp_inv]
    | mul x y _ _ hx hy =>
      obtain ⟨g, hg⟩ := hx
      obtain ⟨g', hg'⟩ := hy
      refine ⟨g ≫ g', ?_⟩
      rw [act.mul, Over.comp_left, Over.comp_left, Category.assoc, hg', ← Category.assoc, hg,
        Category.assoc]
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.ActDescent.exists_oAct hG act hD
  refine ⟨r, fun k => ?_, hr⟩
  apply _root_.GlobalTheory.ActDescent.over_hom_ext hG.1
  rw [← hr, hact]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.QuotientDescendGrpObj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

namespace QuotientDescent

variable {X X' : Scheme.{0}} {π : X ⟶ X'} {G : Over X} {G' : Over X'} {φ : G.left ⟶ G'.left}

noncomputable def up (H : IsPullback φ G.hom G'.hom π) {T : Over X'} (z : T ⟶ G') :
    (Over.pullback π).obj T ⟶ G :=
  Over.homMk (H.lift (pullback.fst T.hom π ≫ z.left) (pullback.snd T.hom π)
    (by rw [Category.assoc, Over.w, pullback.condition])) (H.lift_snd ..)

theorem up_left (H : IsPullback φ G.hom G'.hom π) {T : Over X'} (z : T ⟶ G') :
    (up H z).left ≫ φ = pullback.fst T.hom π ≫ z.left := H.lift_fst ..

theorem hom_ext (H : IsPullback φ G.hom G'.hom π) {T : Over X} {x y : T ⟶ G}
    (h : x.left ≫ φ = y.left ≫ φ) : x = y :=
  Over.OverMorphism.ext (H.hom_ext h ((Over.w x).trans (Over.w y).symm))

theorem up_comp (H : IsPullback φ G.hom G'.hom π) {T T' : Over X'} (u : T' ⟶ T) (z : T ⟶ G') :
    up H (u ≫ z) = (Over.pullback π).map u ≫ up H z := by
  refine hom_ext H ?_
  have A : ((Over.pullback π).map u).left ≫ pullback.fst T.hom π = pullback.fst T'.hom π ≫ u.left :=
    pullback.lift_fst _ _ _
  rw [up_left, Over.comp_left, Over.comp_left, Category.assoc, up_left, ← Category.assoc,
    ← Category.assoc, A]

variable {Γ : Type} [Group Γ] [Finite Γ] {ρ : Γ →* Aut X} {τ : Γ →* Aut G.left}

theorem up_injective (hq : IsAffineQuotient ρ π) (H : IsPullback φ G.hom G'.hom π) {T : Over X'}
    (hT : Flat T.hom) : Function.Injective (up H : (T ⟶ G') → _) := fun x y e ↦ by
  have Hp := (IsPullback.of_hasPullback T.hom π).flip
  obtain ⟨σ, hσ⟩ := exists_action_of_isPullback ρ hq.comp_eq Hp
  have hq' := hq.of_isPullback Hp (fun g ↦ (hσ g).2) (fun g ↦ (hσ g).1)
  refine Over.OverMorphism.ext (hq'.hom_ext ?_)
  rw [← up_left H, ← up_left H, e]

def Equivariant (ρ : Γ →* Aut X) (τ : Γ →* Aut G.left) {T : Over X'}
    (w : (Over.pullback π).obj T ⟶ G) : Prop :=
  ∀ g (s : pullback T.hom π ⟶ pullback T.hom π), s ≫ pullback.fst T.hom π = pullback.fst T.hom π →
    s ≫ pullback.snd T.hom π = pullback.snd T.hom π ≫ (ρ g).hom →
    s ≫ w.left = w.left ≫ (τ g).hom

theorem Equivariant.exists_up (hq : IsAffineQuotient ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hτ : ∀ g, (τ g).hom ≫ φ = φ) {T : Over X'} (hT : Flat T.hom)
    {w : (Over.pullback π).obj T ⟶ G} (hw : Equivariant ρ τ w) : ∃ z : T ⟶ G', up H z = w := by
  have Hp := (IsPullback.of_hasPullback T.hom π).flip
  obtain ⟨σ, hσ⟩ := exists_action_of_isPullback ρ hq.comp_eq Hp
  have hq' := hq.of_isPullback Hp (fun g ↦ (hσ g).2) (fun g ↦ (hσ g).1)
  obtain ⟨z, hz⟩ := hq'.exists_comp_eq (w.left ≫ φ) fun g ↦ by
    rw [← Category.assoc, hw g _ (hσ g).1 (hσ g).2, Category.assoc, hτ]
  refine ⟨Over.homMk z (hq'.hom_ext ?_), hom_ext H ((up_left H _).trans hz)⟩
  rw [reassoc_of% hz, H.w, pullback.condition]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ π) (Over.w w))

omit [Finite Γ] in
theorem equivariant_up (H : IsPullback φ G.hom G'.hom π) (hτ : ∀ g, (τ g).hom ≫ φ = φ)
    (hτ' : ∀ g, (τ g).hom ≫ G.hom = G.hom ≫ (ρ g).hom) {T : Over X'} (z : T ⟶ G') :
    Equivariant ρ τ (up H z) := fun g s h₁ h₂ ↦ by
  have e : (up H z).left ≫ G.hom = pullback.snd T.hom π := Over.w _
  refine H.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, hτ, up_left, reassoc_of% h₁]
  · rw [Category.assoc, Category.assoc, hτ', e, h₂, reassoc_of% e]

noncomputable def equivariantSubgroup [GrpObj G] (hτ : ∀ g, IsGrpPullback G G (ρ g).hom (τ g).hom)
    (T : Over X') : Subgroup ((Over.pullback π).obj T ⟶ G) :=
  ⨅ (g : Γ) (s : pullback T.hom π ⟶ pullback T.hom π)
    (_ : s ≫ pullback.fst T.hom π = pullback.fst T.hom π)
    (h : s ≫ pullback.snd T.hom π = pullback.snd T.hom π ≫ (ρ g).hom),
    (preHom (Over.homMk s h)).eqLocus (pushHom (hτ g) ((Over.pullback π).obj T))

omit [Finite Γ] in
theorem mem_equivariantSubgroup [GrpObj G] (hτ : ∀ g, IsGrpPullback G G (ρ g).hom (τ g).hom)
    {T : Over X'} {w : (Over.pullback π).obj T ⟶ G} :
    w ∈ equivariantSubgroup hτ T ↔ Equivariant ρ τ w := by
  simp only [equivariantSubgroup, Subgroup.mem_iInf]
  exact ⟨fun h g s h₁ h₂ ↦ congrArg (fun z ↦ z.left) (h g s h₁ h₂),
    fun h g s h₁ h₂ ↦ Over.OverMorphism.ext (h g s h₁ h₂)⟩

end QuotientDescent

open QuotientDescent

theorem quotient_descend_grpObj :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (O : Type) [CommRing O] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) [GrpObj G] [IsCommMonObj G] (G' : Over X') (φ : G.left ⟶ G'.left) (τ : Γ →* Aut G.left) (a : OAct O G), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsPullback φ G.hom G'.hom π → Flat G'.hom → (∀ g, (τ g).hom ≫ φ = φ ∧ IsGrpPullback G G (ρ g).hom (τ g).hom ∧ ∀ c, (a.act c).left ≫ (τ g).hom = (τ g).hom ≫ (a.act c).left) → ∃ (_ : GrpObj G') (_ : IsCommMonObj G') (a' : OAct O G'), IsGrpPullback G G' π φ ∧ ∀ c, (a.act c).left ≫ φ = φ ≫ (a'.act c).left := by
  intro Γ _ _ O _ X X' ρ π G _ _ G' φ τ a ⟨h₁, h₂, h₃⟩ H hG' hτ
  have hq : IsAffineQuotient ρ π :=
    ⟨h₂, h₁, fun V ↦ (h₃ V).1, fun V s hs ↦ (h₃ V).2 s fun g _ ↦ (hs g).2⟩
  have hp (g) := (hτ g).2.1
  have f₀ : Flat (𝟙_ (Over X')).hom := inferInstanceAs (Flat (𝟙 X'))
  have f₂ {A B : Over X'} (hA : Flat A.hom) (hB : Flat B.hom) : Flat (A ⊗ B).hom :=
    inferInstanceAs (Flat (pullback.fst A.hom B.hom ≫ A.hom))
  have inj {T : Over X'} (hT : Flat T.hom) {x y : T ⟶ G'} (e : up H x = up H y) : x = y :=
    up_injective hq H hT e
  have ex {T : Over X'} (hT : Flat T.hom) {w : (Over.pullback π).obj T ⟶ G}
      (hw : w ∈ equivariantSubgroup hp T) : ∃ z : T ⟶ G', up H z = w :=
    ((mem_equivariantSubgroup hp).mp hw).exists_up hq H (fun g ↦ (hτ g).1) hT
  have mem {T : Over X'} (z : T ⟶ G') : up H z ∈ equivariantSubgroup hp T :=
    (mem_equivariantSubgroup hp).mpr (equivariant_up H (fun g ↦ (hτ g).1) (fun g ↦ (hp g).1.w) z)
  obtain ⟨m, hm⟩ := ex (f₂ hG' hG') (mul_mem (mem (fst G' G')) (mem (snd G' G')))
  obtain ⟨e, he⟩ := ex f₀ (one_mem _)
  obtain ⟨i, hi⟩ := ex hG' (inv_mem (mem (𝟙 G')))
  have hb (c : O) : ∃ z : G' ⟶ G', up H z = up H (𝟙 G') ≫ a.act c :=
    ex hG' ((mem_equivariantSubgroup hp).mpr fun g s k₁ k₂ ↦ by
      rw [Over.comp_left, Category.assoc, (hτ g).2.2,
        reassoc_of% ((mem_equivariantSubgroup hp).mp (mem (𝟙 G')) g s k₁ k₂)])
  choose b hb using hb
  have hm' {T : Over X'} (u : T ⟶ G' ⊗ G') :
      up H (u ≫ m) = up H (u ≫ fst _ _) * up H (u ≫ snd _ _) := by
    rw [up_comp, hm, MonObj.comp_mul, ← up_comp, ← up_comp]
  have he' {T : Over X'} (u : T ⟶ 𝟙_ _) : up H (u ≫ e) = 1 := by
    rw [up_comp, he, MonObj.comp_one]
  have hb' {T : Over X'} (u : T ⟶ G') (c : O) : up H (u ≫ b c) = up H u ≫ a.act c := by
    rw [up_comp, hb, ← Category.assoc, ← up_comp, Category.comp_id]
  letI : GrpObj G' :=
    { one := e
      mul := m
      one_mul := inj (f₂ f₀ hG') (by
        rw [hm', whiskerRight_fst, he', _root_.one_mul, whiskerRight_snd, leftUnitor_hom])
      mul_one := inj (f₂ hG' f₀) (by
        rw [hm', whiskerLeft_snd, he', _root_.mul_one, whiskerLeft_fst, rightUnitor_hom])
      mul_assoc := inj (f₂ (f₂ hG' hG') hG') (by
        rw [← Category.assoc, hm' (m ▷ G'), hm' (_ ≫ G' ◁ m), whiskerRight_fst, whiskerRight_snd,
          Category.assoc, Category.assoc, whiskerLeft_fst, whiskerLeft_snd, hm' (fst _ _),
          ← Category.assoc _ _ m, hm', Category.assoc, Category.assoc, associator_hom_fst,
          associator_hom_snd_fst, associator_hom_snd_snd, _root_.mul_assoc])
      inv := i
      left_inv := inj hG' (by rw [hm', he', lift_fst, lift_snd, hi, inv_mul_cancel])
      right_inv := inj hG' (by rw [hm', he', lift_fst, lift_snd, hi, mul_inv_cancel]) }
  have hmul {T : Over X'} (x y : T ⟶ G') : up H (x * y) = up H x * up H y := by
    rw [Hom.mul_def]
    exact (hm' _).trans (by rw [lift_fst, lift_snd])
  have : IsCommMonObj G' := ⟨inj (f₂ hG' hG') (by
    refine (hm' _).trans (Eq.trans ?_ hm.symm)
    rw [braiding_hom_fst, braiding_hom_snd, mul_comm])⟩
  let a' : OAct O G' :=
    { act := b
      hom c := by
        have := a.hom c
        refine ⟨inj f₀ ?_, inj (f₂ hG' hG') ?_⟩
        · rw [hb']
          change up H e ≫ _ = up H e
          rw [he, MonObj.one_comp]
        · rw [hb']
          change up H m ≫ _ = up H (_ ≫ m)
          rw [hm', hm, tensorHom_fst, tensorHom_snd, hb', hb', MonObj.mul_comp]
      one := inj hG' (by rw [hb, a.one, Category.comp_id])
      mul c d := inj hG' (by rw [hb', hb, hb, a.mul, Category.assoc])
      add c d := inj hG' (by rw [hmul, hb, hb, hb, a.add, MonObj.comp_mul]) }
  have sec {T : Over X} : ∃ s : T ⟶ (Over.pullback π).obj (Over.mk (T.hom ≫ π)),
      s.left ≫ pullback.fst _ π = 𝟙 T.left :=
    ⟨Over.homMk (pullback.lift (𝟙 T.left) T.hom (Category.id_comp _)) (pullback.lift_snd ..),
      pullback.lift_fst ..⟩
  refine ⟨inferInstance, this, a', ⟨H, fun T x y x₀ y₀ hx hy ↦ ?_⟩, fun c ↦ ?_⟩
  · obtain ⟨s, hs⟩ := sec (T := T)
    have k (z : Over.mk (T.hom ≫ π) ⟶ G') : (s ≫ up H z).left ≫ φ = z.left := by
      rw [Over.comp_left, Category.assoc, up_left, reassoc_of% hs]
    rw [← k, hmul, MonObj.comp_mul, QuotientDescent.hom_ext H ((k x₀).trans hx),
      QuotientDescent.hom_ext H ((k y₀).trans hy)]
  · obtain ⟨s, hs⟩ := sec (T := G)
    have k (z : Over.mk (G.hom ≫ π) ⟶ G') : (s ≫ up H z).left ≫ φ = z.left := by
      rw [Over.comp_left, Category.assoc, up_left, reassoc_of% hs]
    let u : Over.mk (G.hom ≫ π) ⟶ G' := Over.homMk φ H.w
    have hu : s ≫ up H u = 𝟙 G := QuotientDescent.hom_ext H ((k u).trans (Category.id_comp _).symm)
    have := k (u ≫ b c)
    rwa [hb', reassoc_of% hu] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SubsingletonSpDualNumber
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.DualRigidity

theorem eq_comp_section_of_const {X T Y : Scheme.{0}} (p : X ⟶ T) (ε : T ⟶ X) (g : X ⟶ Y)
    (h : ε ≫ p = 𝟙 T) (hs : Function.Surjective p.appTop.hom) (y : Y) (hy : ∀ x : X, g x = y) :
    g = p ≫ ε ≫ g := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  haveI : IsAffine W := hW
  have hr : Set.range g ⊆ Set.range (Scheme.Opens.ι W) := by
    rintro _ ⟨x, rfl⟩
    rw [hy x, Scheme.Opens.range_ι]
    exact hyW
  have key := GlobalTheory.eq_comp_section_of_surjective_appTop p ε (IsOpenImmersion.lift (Scheme.Opens.ι W) g hr) h hs
  have := congrArg (· ≫ Scheme.Opens.ι W) key
  simpa only [Category.assoc, IsOpenImmersion.lift_fac] using this

theorem subsingleton_sp_dualNumber : Subsingleton (Sp (DualNumber ℂ)) := by
  have h : ∀ p : PrimeSpectrum (DualNumber ℂ),
      p.asIdeal = IsLocalRing.maximalIdeal (DualNumber ℂ) := by
    intro p
    refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_
    have hn : IsNilpotent x := by
      rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst]
      have : ¬ IsUnit x.fst := fun hu => hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)
      have h0 : x.fst = 0 := by simpa using this
      rw [h0]; exact IsNilpotent.zero
    obtain ⟨n, hn⟩ := hn
    exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext ((h p).trans (h q).symm)⟩

theorem rigidity_dualNumber : Out.Laws → Out.Laws2 → ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (A' G' : Over (Sp (DualNumber ℂ))) [GrpObj A'] [GrpObj G'] (j : A₀.left ⟶ A'.left) (a b : A' ⟶ G'), IsAbelianScheme A' → IsPullback j A₀.hom A'.hom (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → j ≫ a.left = j ≫ b.left → η[A'] ≫ a = η[A'] ≫ b → a = b := by
  intro hL _ A₀ _ A' G' _ _ j a b hA hj hab hη
  haveI := subsingleton_sp_dualNumber
  let c : A' ⟶ G' := a * b⁻¹
  let j' : Over.mk (j ≫ A'.hom) ⟶ A' := Over.homMk j rfl
  have h1 : j' ≫ a = j' ≫ b := Over.OverMorphism.ext hab
  have h2 : j' ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]
  have h3 : η[A'] ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]
  obtain ⟨t₀⟩ : Nonempty (Sp ℂ) := inferInstance
  let t : Sp (DualNumber ℂ) := spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom t₀
  have hc : ∀ x : A'.left, c.left x = (η[G'] : 𝟙_ (Over (Sp (DualNumber ℂ))) ⟶ G').left t := by
    intro x
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hj x t₀ (Subsingleton.elim _ _)
    have e : j ≫ c.left = (j' ≫ c).left := rfl
    rw [← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    congr 1
    exact Subsingleton.elim (α := Sp (DualNumber ℂ)) _ _
  have hη' : (η[A'] : 𝟙_ (Over (Sp (DualNumber ℂ))) ⟶ A').left ≫ A'.hom = 𝟙 _ := Over.w η[A']
  have key := eq_comp_section_of_const A'.hom _ c.left hη' (hL.globalFns _ A' hA).2 _ hc
  have key' : c = toUnit A' ≫ η[A'] ≫ c := Over.OverMorphism.ext key
  rw [h3, MonObj.comp_one] at key'
  exact mul_inv_eq_one.1 key'

end GlobalTheory.DualRigidity
end

