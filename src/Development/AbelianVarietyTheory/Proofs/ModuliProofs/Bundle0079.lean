import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0037
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullbackFlatOfTame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.TameDescent

theorem specMap_fromSpec_comp_eq_iff {X : Scheme.{0}} (t : X ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (h : U ≤ t ⁻¹ᵁ U) {k : CommRingCat.{0}} (a : Γ(X, U) ⟶ k) :
    (Spec.map a ≫ hU.fromSpec) ≫ t = Spec.map a ≫ hU.fromSpec ↔
      ∀ b, a.hom ((t.appLE U U h).hom b - b) = 0 := by
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec t hU hU h, ← Category.assoc,
    cancel_mono, ← Spec.map_comp, Spec.map_injective.eq_iff]
  simp only [map_sub, sub_eq_zero]
  exact ⟨fun e b => congr(($e).hom b), fun e => CommRingCat.hom_ext (RingHom.ext e)⟩

theorem appLE_sub_mem_map {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p] (t : Y ⟶ Y) {U : X.Opens}
    {W : Y.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (e : W ≤ p ⁻¹ᵁ U)
    (h : W ≤ t ⁻¹ᵁ W) {k : Type} [Field k] (a : Γ(X, U) →+* k)
    (ht : pullback.fst p (Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec) ≫ t =
      pullback.fst p (Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec)) (c : Γ(Y, W)) :
    (t.appLE W W h).hom c - c ∈ (RingHom.ker a).map (p.appLE U W e).hom := by
  let := a.toAlgebra
  let := (p.appLE U W e).hom.toAlgebra
  have : Module.Flat Γ(X, U) Γ(Y, W) := p.flat_appLE hU hW e
  refine mem_map_ker_of_one_tmul_eq_zero_of_flat Γ(X, U) Γ(Y, W) k _ ?_
  let r : Γ(Y, W) ⟶ CommRingCat.of (k ⊗[Γ(X, U)] Γ(Y, W)) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom
  let l : CommRingCat.of k ⟶ CommRingCat.of (k ⊗[Γ(X, U)] Γ(Y, W)) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  have w : (Spec.map r ≫ hW.fromSpec) ≫ p =
      Spec.map l ≫ Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec := by
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec p hU hW e,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    exact (CommRingCat.isPushout_tensorProduct Γ(X, U) k Γ(Y, W)).w.symm
  refine (specMap_fromSpec_comp_eq_iff t hW h r).1 ?_ c
  rw [← pullback.lift_fst _ _ w, Category.assoc, ht]

theorem isPullback_specMap_app {X X' : Scheme.{0}} (π : X ⟶ X') [IsAffineHom π] {V : X'.Opens}
    (hV : IsAffineOpen V) :
    IsPullback (Spec.map (π.app V)) (hV.preimage π).fromSpec hV.fromSpec π :=
  IsOpenImmersion.isPullback _ _ _ _
    (by rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec]) (by simp)

theorem isPullback_of_isPushout_app {X X' Y Y' : Scheme.{0}} (π : X ⟶ X') (φ : Y ⟶ Y')
    (p : Y ⟶ X) (p' : Y' ⟶ X') [IsAffineHom π] [IsAffineHom φ] (w : φ ≫ p' = p ≫ π)
    (H : ∀ (V : X'.Opens) (W : Y'.Opens), IsAffineOpen V → IsAffineOpen W →
      ∀ (e : W ≤ p' ⁻¹ᵁ V) (e' : φ ⁻¹ᵁ W ≤ p ⁻¹ᵁ π ⁻¹ᵁ V),
      IsPushout (p'.appLE V W e) (π.app V) (φ.app W) (p.appLE _ _ e')) :
    IsPullback φ p p' π := by
  have h : ∀ y : Y', ∃ (V : X'.Opens) (W : Y'.Opens), IsAffineOpen V ∧ IsAffineOpen W ∧
      y ∈ W ∧ W ≤ p' ⁻¹ᵁ V := fun y => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p' y)) isOpen_univ
    obtain ⟨_, ⟨W, hW, rfl⟩, hy, hle⟩ := Y'.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ p' ⁻¹ᵁ V from hx) (p' ⁻¹ᵁ V).isOpen
    exact ⟨V, W, hV, hW, hy, hle⟩
  choose V W hV hW hy hle using h
  let 𝒰 : Y'.OpenCover := Scheme.Cover.mkOfCovers Y' (fun y => Spec Γ(Y', W y))
    (fun y => (hW y).fromSpec) (fun y => ⟨y, by
      have : y ∈ Set.range (hW y).fromSpec := by
        rw [IsAffineOpen.range_fromSpec]; exact hy y
      exact this⟩)
  refine Scheme.isPullback_of_openCover φ p p' π 𝒰 fun y => ?_
  have e' : φ ⁻¹ᵁ W y ≤ p ⁻¹ᵁ π ⁻¹ᵁ V y := by
    rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage]
    exact φ.preimage_mono (hle y)
  have H1 := isPullback_specMap_app φ (hW y)
  have H2 := (isPullback_SpecMap_of_isPushout _ _ _ _
    (H _ _ (hV y) (hW y) (hle y) e')).paste_vert (isPullback_specMap_app π (hV y)).flip.flip
  rw [IsAffineOpen.SpecMap_appLE_fromSpec p _ ((hW y).preimage φ),
    IsAffineOpen.SpecMap_appLE_fromSpec p' _ (hW y)] at H2
  refine H2.of_iso H1.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ((Category.comp_id _).trans (Category.id_comp _).symm)
    (by simp)
  · exact (Category.comp_id _).trans (H1.flip.isoPullback_hom_snd).symm
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc]
    congr 1
    exact (H1.flip.isoPullback_hom_fst).symm

theorem isPushout_and_flat {Γ : Type} [Group Γ] [Finite Γ] {X X' Y Y' : Scheme.{0}}
    [IsLocallyNoetherian Y'] (ρ : Γ →* Aut X) (τ : Γ →* Aut Y) (π : X ⟶ X') (φ : Y ⟶ Y')
    (p : Y ⟶ X) (p' : Y' ⟶ X') [IsFinite π] [IsFinite φ] [Flat p]
    (hπ : ∀ g, (ρ g).hom ≫ π = π)
    (hπ' : ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V),
      (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (π.app V).hom)
    (hφ : ∀ g, (τ g).hom ≫ φ = φ)
    (hφ' : ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V),
      (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).hom.appLE _ _ h).hom f = f) →
        f ∈ Set.range (φ.app V).hom)
    (w : φ ≫ p' = p ≫ π) (hp : ∀ g, (τ g).hom ≫ p = p ≫ (ρ g).hom)
    (htame : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X),
      (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0)
    (hfix : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x →
      pullback.fst p x ≫ (τ g).hom = pullback.fst p x)
    (V : X'.Opens) (W : Y'.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (e : W ≤ p' ⁻¹ᵁ V) (e' : φ ⁻¹ᵁ W ≤ p ⁻¹ᵁ π ⁻¹ᵁ V) :
    IsPushout (p'.appLE V W e) (π.app V) (φ.app W) (p.appLE _ _ e') ∧
      (p'.appLE V W e).hom.Flat := by
  have hU : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  have hU' : IsAffineOpen (φ ⁻¹ᵁ W) := hW.preimage φ
  have hst := preimage_le_of_invariant ρ π hπ V
  have hst' := preimage_le_of_invariant τ φ hφ W
  let := sectionsAction ρ _ hst
  let := sectionsAction τ _ hst'
  let := (π.app V).hom.toAlgebra
  let := (φ.app W).hom.toAlgebra
  let := (p'.appLE V W e).hom.toAlgebra
  let := (p.appLE _ _ e').hom.toAlgebra
  let := (p'.appLE V W e ≫ φ.app W).hom.toAlgebra
  have sq : p'.appLE V W e ≫ φ.app W = π.app V ≫ p.appLE _ _ e' := by
    simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, w]
  have : IsScalarTower Γ(X', V) Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(X', V) Γ(X, π ⁻¹ᵁ V) Γ(Y, φ ⁻¹ᵁ W) :=
    .of_algebraMap_eq' congr(($sq).hom)
  have : SMulCommClass Γ Γ(X', V) Γ(X, π ⁻¹ᵁ V) := ⟨fun g a s ↦ by
    have hfix : g • algebraMap Γ(X', V) Γ(X, π ⁻¹ᵁ V) a = algebraMap _ _ a :=
      (isInvariantSection_app ρ π hπ V a g⁻¹).2
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have : SMulCommClass Γ Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) := ⟨fun g a s ↦ by
    have hfix : g • algebraMap Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) a = algebraMap _ _ a :=
      (isInvariantSection_app τ φ hφ W a g⁻¹).2
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have : Algebra.IsInvariant Γ(X', V) Γ(X, π ⁻¹ᵁ V) Γ := ⟨fun s hs ↦
    (hπ' V).2 s fun g _ ↦ by simpa only [inv_inv] using
      (show (ρ g⁻¹⁻¹).hom.appLE _ _ (hst _) s = s from hs g⁻¹)⟩
  have : Algebra.IsInvariant Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) Γ := ⟨fun s hs ↦
    (hφ' W).2 s fun g _ ↦ by simpa only [inv_inv] using
      (show (τ g⁻¹⁻¹).hom.appLE _ _ (hst' _) s = s from hs g⁻¹)⟩
  have heq : ∀ (g : Γ) (b : Γ(X, π ⁻¹ᵁ V)), g • algebraMap _ Γ(Y, φ ⁻¹ᵁ W) b =
      algebraMap _ Γ(Y, φ ⁻¹ᵁ W) (g • b) := fun g b => by
    change (τ g⁻¹).hom.appLE _ _ (hst' _) (p.appLE _ _ e' b) =
      p.appLE _ _ e' ((ρ g⁻¹).hom.appLE _ _ (hst _) b)
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, hp]
  have hflat : Module.Flat Γ(X, π ⁻¹ᵁ V) Γ(Y, φ ⁻¹ᵁ W) := p.flat_appLE hU hU' e'
  have key : ∀ q : Ideal Γ(X, π ⁻¹ᵁ V), q.IsPrime → ((Nat.card (q.inertia Γ) : Γ(X, π ⁻¹ᵁ V)) ∉ q) ∧
      ∀ g ∈ q.inertia Γ, ∀ c : Γ(Y, φ ⁻¹ᵁ W), g • c - c ∈ q.map (algebraMap _ Γ(Y, φ ⁻¹ᵁ W)) := by
    intro q hq
    let k := AlgebraicClosure q.ResidueField
    let a : Γ(X, π ⁻¹ᵁ V) →+* k := (algebraMap q.ResidueField k).comp (algebraMap _ _)
    have ha : ∀ b, a b = 0 ↔ b ∈ q := fun b => by
      simp [a]
    have hker : RingHom.ker a = q := Ideal.ext ha
    let x : Sp k ⟶ X := Spec.map (CommRingCat.ofHom a) ≫ hU.fromSpec
    have hx : ∀ g, x ≫ (ρ g⁻¹).hom = x ↔ g ∈ q.inertia Γ := fun g =>
      (specMap_fromSpec_comp_eq_iff _ hU (hst _) _).trans (forall_congr' fun b => ha _)
    refine ⟨fun h => htame k x ?_, fun g hg c => ?_⟩
    · rw [← Nat.card_congr ((Equiv.inv Γ).subtypeEquiv (p := fun g => g ∈ q.inertia Γ)
        (q := fun g => x ≫ (ρ g).hom = x) fun g => (hx g).symm), ← map_natCast a]
      exact (ha _).2 h
    · rw [← hker]
      exact appLE_sub_mem_map p _ hU hU' e' (hst' _) a (hfix k x _ ((hx g).2 hg)) c
  have hpo : Algebra.IsPushout Γ(X', V) Γ(X, π ⁻¹ᵁ V) Γ(Y', W) Γ(Y, φ ⁻¹ᵁ W) :=
    GlobalTheory.T.invariant_tower_isPushout Γ _ _ _ _ (hπ' V).1 (hφ' W).1 heq
      (IsLocallyNoetherian.component_noetherian ⟨W, hW⟩) (π.finite_app V hV) (φ.finite_app W hW)
      hflat (fun q hq => (key q hq).1) (fun q hq => (key q hq).2)
  refine ⟨CommRingCat.isPushout_iff_isPushout.2 hpo.symm, ?_⟩
  exact flat_of_tame_descent Γ _ _ _ _ (hπ' V).1 (hφ' W).1 heq hpo hflat
    (exists_finsum_smul_eq_one_of_tame Γ _ fun q hq => (key q hq).1)

theorem isPullback_flat_of_tame :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' Y Y' : Scheme.{0}) [IsLocallyNoetherian X'] (ρ : Γ →* Aut X) (τ : Γ →* Aut Y) (π : X ⟶ X') (φ : Y ⟶ Y') (p : Y ⟶ X) (p' : Y' ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (IsAffineHom φ ∧ (∀ g, (τ g).hom ≫ φ = φ) ∧ ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V), (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (φ.app V).hom) → φ ≫ p' = p ≫ π → (∀ g, (τ g).hom ≫ p = p ≫ (ρ g).hom) → IsFinite π → Flat p → LocallyOfFiniteType p → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x → pullback.fst p x ≫ (τ g).hom = pullback.fst p x) → IsPullback φ p p' π ∧ Flat p' ∧ LocallyOfFiniteType p' := by
  intro Γ _ _ X X' Y Y' _ ρ τ π φ p p' hπ hφ w hp _ _ _ htame hfix
  obtain ⟨_, _, -⟩ := GlobalTheory.T.quotient_isFinite_and_descends_finiteness_properties Γ Y Y' τ φ hφ X' p' (by rw [w]; infer_instance)
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian p'
  have H := isPushout_and_flat ρ τ π φ p p' hπ.2.1 hπ.2.2 hφ.2.1 hφ.2.2 w hp htame hfix
  refine ⟨isPullback_of_isPushout_app π φ p p' w fun V W hV hW e e' => (H V W hV hW e e').1,
    ⟨fun {V} hV {W} hW e => (H V W hV hW e ?_).2⟩, inferInstance⟩
  rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage]
  exact φ.preimage_mono e

end GlobalTheory.TameDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.OActSpreadFromDenseFibresAbelianScheme
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ActSpread

variable {O : Type} [CommRing O] {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem act_zero {T : Scheme.{0}} {G : Over T} [GrpObj G] (i : OAct O G) : i.act 0 = 1 := by
  have h : i.act 0 * i.act 0 = i.act 0 * 1 := by rw [← i.add, add_zero, _root_.mul_one]
  exact mul_left_cancel h

theorem act_neg {T : Scheme.{0}} {G : Over T} [GrpObj G] (i : OAct O G) (x : O) : i.act (-x) = (i.act x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← i.add, neg_add_cancel, act_zero]

section
variable {T : Scheme.{0}} {x : T ⟶ S} {G : Over T} [GrpObj G] {φ : G.left ⟶ A.left}

theorem compat_iff (hG : IsGrpPullback G A x φ) (u : G ⟶ G) (f : A ⟶ A) :
    u.left ≫ φ = φ ≫ f.left ↔
      pushHom hG G u = (Over.homMk φ hG.1.w : Over.mk (G.hom ≫ x) ⟶ A) ≫ f := by
  have hp : (pushHom hG G u).left = u.left ≫ φ := by
    rfl
  constructor
  · intro h
    ext1
    rw [hp, h]
    simp
  · intro h
    have h' := congrArg Over.Hom.left h
    rw [hp] at h'
    simpa using h'

theorem compat_one (hG : IsGrpPullback G A x φ) : (1 : G ⟶ G).left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
  rw [compat_iff hG, map_one]
  simp

theorem compat_mul (hG : IsGrpPullback G A x φ) {u v : G ⟶ G} {f g : A ⟶ A}
    (hf : u.left ≫ φ = φ ≫ f.left) (hg : v.left ≫ φ = φ ≫ g.left) : (u * v).left ≫ φ = φ ≫ (f * g).left := by
  rw [compat_iff hG] at hf hg ⊢
  rw [map_mul, hf, hg, comp_mul]

theorem compat_inv (hG : IsGrpPullback G A x φ) {u : G ⟶ G} {f : A ⟶ A}
    (hf : u.left ≫ φ = φ ≫ f.left) : (u⁻¹).left ≫ φ = φ ≫ (f⁻¹).left := by
  rw [compat_iff hG] at hf ⊢
  rw [map_inv, hf, GrpObj.comp_inv]

omit [GrpObj A] [GrpObj G] in
theorem compat_comp {u v : G ⟶ G} {f g : A ⟶ A}
    (hf : u.left ≫ φ = φ ≫ f.left) (hg : v.left ≫ φ = φ ≫ g.left) : (u ≫ v).left ≫ φ = φ ≫ (f ≫ g).left := by
  simp only [Over.comp_left, Category.assoc, hg]
  rw [reassoc_of% hf]

omit [GrpObj A] [GrpObj G] in
theorem compat_id : (𝟙 G : G ⟶ G).left ≫ φ = φ ≫ (𝟙 A : A ⟶ A).left := by
  simp

end

theorem exists_universal [IsCommMonObj A] {J : Type} (a : J → O) (act₀ : J → (A ⟶ A))
    (hcl : Subring.closure (Set.range a) = ⊤) (hh : ∀ j, IsMonHom (act₀ j)) (c : O) :
    ∃ f : A ⟶ A, IsMonHom f ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (G : Over T) [GrpObj G] (φ : G.left ⟶ A.left)
      (act : OAct O G), IsGrpPullback G A x φ → (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left) →
      (act.act c).left ≫ φ = φ ≫ f.left := by
  have m1 : IsMonHom (1 : A ⟶ A) := by
    rw [Hom.one_def]; infer_instance
  have m2 : ∀ f g : A ⟶ A, IsMonHom f → IsMonHom g → IsMonHom (f * g) := fun f g _ _ => by
    rw [Hom.mul_def]; infer_instance
  have hc : c ∈ Subring.closure (Set.range a) := hcl ▸ Subring.mem_top c
  induction hc using Subring.closure_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact ⟨act₀ j, hh j, fun _ _ _ _ _ _ _ h => h j⟩
  | zero =>
    refine ⟨1, m1, fun _ _ _ _ _ act hG _ => ?_⟩
    rw [act_zero]
    exact compat_one hG
  | one =>
    refine ⟨𝟙 A, inferInstance, fun _ _ _ _ _ act _ _ => ?_⟩
    rw [act.one]
    exact compat_id
  | add y z _ _ hy hz =>
    obtain ⟨f, hf, Hf⟩ := hy
    obtain ⟨g, hg, Hg⟩ := hz
    refine ⟨f * g, m2 f g hf hg, fun T x G _ φ act hG h => ?_⟩
    rw [act.add]
    exact compat_mul hG (Hf T x G φ act hG h) (Hg T x G φ act hG h)
  | neg y _ hy =>
    obtain ⟨f, hf, Hf⟩ := hy
    refine ⟨f⁻¹, inferInstance, fun T x G _ φ act hG h => ?_⟩
    rw [act_neg]
    exact compat_inv hG (Hf T x G φ act hG h)
  | mul y z _ _ hy hz =>
    obtain ⟨f, hf, Hf⟩ := hy
    obtain ⟨g, hg, Hg⟩ := hz
    refine ⟨f ≫ g, inferInstance, fun T x G _ φ act hG h => ?_⟩
    rw [act.mul]
    exact compat_comp (Hf T x G φ act hG h) (Hg T x G φ act hG h)

omit [GrpObj A] in

theorem ext_of_dense [IsReduced S] [Smooth A.hom] [IsSeparated A.hom] (f g : A ⟶ A) (D : Set S) (hD : Dense D)
    (H : ∀ p ∈ D, ∃ (T P : Scheme.{0}) (x : T ⟶ S) (q : P ⟶ T) (φ : P ⟶ A.left), p ∈ Set.range x ∧
      IsPullback φ q A.hom x ∧ φ ≫ f.left = φ ≫ g.left) : f = g := by
  have hred : IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  have hw : f.left ≫ A.hom = g.left ≫ A.hom := by rw [Over.w f, Over.w g]
  obtain ⟨-, -, H3⟩ := GlobalTheory.dense_fibres_ext A.left S A.hom D hD
  have hin : ∀ y : A.left, A.hom y ∈ D → pullback.lift f.left g.left hw y ∈ Set.range (pullback.diagonal A.hom) := by
    intro y hy
    obtain ⟨T, P, x, q, φ, ⟨t, ht⟩, hpb, hφ⟩ := H _ hy
    have key : φ ≫ pullback.lift f.left g.left hw = (φ ≫ f.left) ≫ pullback.diagonal A.hom := by
      apply pullback.hom_ext <;>
        simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
          pullback.diagonal_snd, Category.comp_id, hφ]
    have hy' : y ∈ Set.range (pullback.fst A.hom x) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨t, ht⟩
    obtain ⟨z, hz⟩ := hy'
    have hinv : hpb.isoPullback.inv ≫ φ = pullback.fst A.hom x := by
      exact hpb.isoPullback_inv_fst
    refine ⟨(φ ≫ f.left) (hpb.isoPullback.inv z), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← key, Scheme.Hom.comp_apply, ← hz, ← hinv, Scheme.Hom.comp_apply]
  obtain ⟨e, he⟩ := H3 _ _ (pullback.diagonal A.hom) (pullback.lift f.left g.left hw) hin
  have e1 := congrArg (· ≫ pullback.fst A.hom A.hom) he
  have e2 := congrArg (· ≫ pullback.snd A.hom A.hom) he
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
    pullback.lift_fst, pullback.lift_snd] at e1 e2
  ext1
  rw [← e1, ← e2]

end GlobalTheory.ActSpread

namespace GlobalTheory

open ActSpread in

theorem oAct_spread_of_dense_fibres : ∀ (O : Type) [CommRing O] (J : Type) (a : J → O) (S : Scheme.{0}) [IsReduced S] (A : Over S) [GrpObj A] (act₀ : J → (A ⟶ A)), Subring.closure (Set.range a) = ⊤ → IsAbelianScheme A → (∀ j, IsMonHom (act₀ j)) → Dense {p : S | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ S) (G : Over (Sp K)) (_ : GrpObj G) (φ : G.left ⟶ A.left) (act : OAct O G), p ∈ Set.range x ∧ IsGrpPullback G A x φ ∧ ∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left} → ∃ r : OAct O A, (∀ j, r.act (a j) = act₀ j) ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (G : Over T) [GrpObj G] (φ : G.left ⟶ A.left) (act : OAct O G), IsGrpPullback G A x φ → (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left) → ∀ c, (act.act c).left ≫ φ = φ ≫ (r.act c).left := by
  intro O _ J a S _ A _ act₀ hcl hab hh hD
  obtain ⟨hcomm, hsm, hpr, -⟩ := hab
  choose F hF HF using fun c => ActSpread.exists_universal a act₀ hcl hh c
  have ext : ∀ f g : A ⟶ A, (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (G : Over (Sp K)) [GrpObj G]
      (φ : G.left ⟶ A.left) (act : OAct O G), IsGrpPullback G A x φ →
      (∀ j, (act.act (a j)).left ≫ φ = φ ≫ (act₀ j).left) → φ ≫ f.left = φ ≫ g.left) → f = g := by
    intro f g H
    refine ActSpread.ext_of_dense f g _ hD ?_
    rintro p ⟨K, _, x, G, _, φ, act, hp, hG, hc⟩
    exact ⟨Sp K, G.left, x, G.hom, φ, hp, hG.1, H K x G φ act hG hc⟩
  refine ⟨⟨F, hF, ?_, ?_, ?_⟩, ?_, fun T x G _ φ act hG hc c => HF c T x G φ act hG hc⟩
  · refine ext _ _ fun K _ x G _ φ act hG hc => ?_
    rw [← HF 1 _ x G φ act hG hc, act.one]
    exact ActSpread.compat_id
  · intro b c
    refine ext _ _ fun K _ x G _ φ act hG hc => ?_
    rw [← HF (b * c) _ x G φ act hG hc, act.mul]
    exact ActSpread.compat_comp (HF b _ x G φ act hG hc) (HF c _ x G φ act hG hc)
  · intro b c
    refine ext _ _ fun K _ x G _ φ act hG hc => ?_
    rw [← HF (b + c) _ x G φ act hG hc, act.add]
    exact ActSpread.compat_mul hG (HF b _ x G φ act hG hc) (HF c _ x G φ act hG hc)
  · intro j
    refine ext _ _ fun K _ x G _ φ act hG hc => ?_
    rw [← HF (a j) _ x G φ act hG hc]
    exact hc j

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionBasisGeometricFibresOfOpenCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionBasis_geometric_fibres_of_open_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (g k : ℕ) (P : Fin (2 * g) → (Out.baseOver S ⟶ A)) (Q : ∀ i, Fin (2 * g) → (Out.baseOver (U i).toScheme ⟶ G i)), (∀ i l, (Q i l).left ≫ ψ i = (U i).ι ≫ (P l).left) → (∀ i (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ (U i).toScheme) (y : Over.mk x ⟶ G i), y ^ k = 1 → ∃! c : Ix g k, Out.linComb (fun l => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (U i).toScheme) ≫ Q i l) (fun l => (c l).val) = y) → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ k = 1 → ∃! c : Ix g k, Out.linComb (fun l => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ P l) (fun l => (c l).val) = y := by
  first | exact @GlobalTheory.CoverGlue.torsionBasis_of_cover | exact GlobalTheory.CoverGlue.torsionBasis_of_cover | (intros; apply GlobalTheory.CoverGlue.torsionBasis_of_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.UnramifiedQuasiFiniteOfTangent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.TangentCriterion

noncomputable def dualOfDerivation {A B K : Type} [CommRing A] [CommRing B] [Field K] [Algebra A B]
    [Algebra B K] [Algebra A K] (D : Derivation A B K) : B →+* DualNumber K where
  toFun b := TrivSqZeroExt.inl (algebraMap B K b) + TrivSqZeroExt.inr (D b)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        DualNumber.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        add_zero, Derivation.leibniz, Algebra.smul_def]
      ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

theorem formallyUnramified_of_tangent {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B]
    (h : ∀ (K : Type) [Field K] (g : B →+* DualNumber K),
      g.comp (algebraMap A B) = (((algebraMap K (DualNumber K)).comp
        (TrivSqZeroExt.fstHom K K K).toRingHom).comp g).comp (algebraMap A B) →
      g = ((algebraMap K (DualNumber K)).comp (TrivSqZeroExt.fstHom K K K).toRingHom).comp g) :
    Algebra.FormallyUnramified A B := by
  refine ⟨?_⟩
  by_contra hn
  rw [not_subsingleton_iff_nontrivial] at hn
  obtain ⟨N, hN, -⟩ : ∃ N : Submodule B Ω[B⁄A], IsCoatom N ∧ ⊥ ≤ N :=
    (eq_top_or_exists_le_coatom (⊥ : Submodule B Ω[B⁄A])).resolve_left bot_ne_top
  have hs : IsSimpleModule B (Ω[B⁄A] ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
  letI := Ideal.Quotient.field m
  let φ : Ω[B⁄A] →ₗ[B] (B ⧸ m) := e.toLinearMap ∘ₗ N.mkQ
  let D : Derivation A B (B ⧸ m) := φ.compDer (KaehlerDifferential.D A B)
  have hD := h (B ⧸ m) (dualOfDerivation D) (by
    ext a <;> simp [dualOfDerivation, TrivSqZeroExt.algebraMap_eq_inl])
  have h0 : ∀ b, φ (KaehlerDifferential.D A B b) = 0 := fun b => by
    have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun hD b)
    simpa [dualOfDerivation, TrivSqZeroExt.algebraMap_eq_inl, D] using this
  have hφ : φ = 0 := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation A B)
    rintro _ ⟨b, rfl⟩
    exact h0 b
  have hsurj : Function.Surjective φ := e.surjective.comp N.mkQ_surjective
  obtain ⟨w, hw⟩ := hsurj 1
  rw [hφ] at hw
  exact zero_ne_one hw

theorem unramified_quasiFinite_of_tangent : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y), LocallyOfFiniteType f → (∀ (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ X), x ≫ f = constPt x ≫ f → x = constPt x) → FormallyUnramified f ∧ LocallyQuasiFinite f := by
  intro X Y f hf h
  have key : ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V)
      (e : V ≤ f ⁻¹ᵁ U), (f.appLE U V e).hom.FormallyUnramified := by
    intro U hU V hV e
    have hft := f.finiteType_appLE hU hV e
    letI := (f.appLE U V e).hom.toAlgebra
    haveI : Algebra.FiniteType Γ(Y, U) Γ(X, V) := hft
    refine formallyUnramified_of_tangent (A := Γ(Y, U)) (B := Γ(X, V)) fun K _ g hg => ?_
    have hc : constPt (Spec.map (CommRingCat.ofHom g) ≫ hV.fromSpec) =
        Spec.map (CommRingCat.ofHom (((algebraMap K (DualNumber K)).comp
          (TrivSqZeroExt.fstHom K K K).toRingHom).comp g)) ≫ hV.fromSpec := by
      simp only [constPt, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have := h K (Spec.map (CommRingCat.ofHom g) ≫ hV.fromSpec) (by
      rw [hc]
      simp only [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV e, ← Spec.map_comp_assoc]
      congr 2
      exact CommRingCat.hom_ext hg)
    rw [hc, cancel_mono, Spec.map_inj] at this
    exact congrArg CommRingCat.Hom.hom this
  refine ⟨⟨key⟩, ⟨fun {U} hU {V} hV e => ?_⟩⟩
  have h1 := key hU hV e
  have hft := f.finiteType_appLE hU hV e
  letI := (f.appLE U V e).hom.toAlgebra
  haveI : Algebra.FiniteType Γ(Y, U) Γ(X, V) := hft
  haveI : Algebra.FormallyUnramified Γ(Y, U) Γ(X, V) := h1
  exact (inferInstance : Algebra.QuasiFinite Γ(Y, U) Γ(X, V))

end GlobalTheory.TangentCriterion
end

