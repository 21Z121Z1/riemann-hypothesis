import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0108
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0107
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0106
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {R : Type} [CommRing R] [IsLocalRing R]
  {z : Sp R ⟶ X}

theorem val_spec {a : Ω} {r : R} (h : ValAt ξ z a r) : ∃ hz : genPt ξ ⤳ centre z, a ∈ regAt ξ ⟨centre z, hz⟩ := by
  obtain ⟨hz, s, hs, -⟩ := h
  exact ⟨hz, s, hs⟩

theorem val_exists {a : Ω} {hz : genPt ξ ⤳ centre z} (h : a ∈ regAt ξ ⟨centre z, hz⟩) : ∃ r : R, ValAt ξ z a r := by
  obtain ⟨s, hs⟩ := h
  exact ⟨_, hz, s, hs, rfl⟩

theorem val_unique (hξ : IsCptGen ξ) {a : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a r') : r = r' := by
  obtain ⟨hz, s, hs, rfl⟩ := h
  obtain ⟨hz', s', hs', rfl⟩ := h'
  have : s = s' := hξ.inj ⟨centre z, hz⟩ (hs.trans hs'.symm)
  rw [this]

theorem val_mul {a b : Ω} {r s : R} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨hz, t, ht, rfl⟩ := h
  obtain ⟨hz', t', ht', rfl⟩ := h'
  exact ⟨hz, t * t', by rw [map_mul, ht]; rw [← ht'], map_mul _ _ _⟩

theorem val_add {a b : Ω} {r s : R} (h : ValAt ξ z a r) (h' : ValAt ξ z b s) : ValAt ξ z (a + b) (r + s) := by
  obtain ⟨hz, t, ht, rfl⟩ := h
  obtain ⟨hz', t', ht', rfl⟩ := h'
  exact ⟨hz, t + t', by rw [map_add, ht]; rw [← ht'], map_add _ _ _⟩

theorem val_nat (hz : genPt ξ ⤳ centre z) (n : ℕ) : ValAt ξ z (n : Ω) (n : R) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_natCast _ n, map_natCast _ n⟩

theorem val_one (hz : genPt ξ ⤳ centre z) : ValAt ξ z (1 : Ω) (1 : R) := by
  simpa using val_nat (ξ := ξ) (z := z) hz 1

theorem val_zero (hz : genPt ξ ⤳ centre z) : ValAt ξ z (0 : Ω) (0 : R) := by
  simpa using val_nat (ξ := ξ) (z := z) hz 0

theorem val_inv {a : Ω} {r : Rˣ} (h : ValAt ξ z a r) : ValAt ξ z a⁻¹ (↑r⁻¹ : R) := by
  obtain ⟨hz, s, hs, hr⟩ := h
  have hu : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' z).map_nonunit s (hr ▸ r.isUnit)
  obtain ⟨u, rfl⟩ := hu
  refine ⟨hz, ↑u⁻¹, ?_, ?_⟩
  · rw [← hs, map_units_inv]
  · have : (Units.map (Scheme.stalkClosedPointTo z).hom.toMonoidHom u) = r := Units.ext hr
    rw [← this]
    exact congrArg Units.val (map_inv (Units.map (Scheme.stalkClosedPointTo z).hom.toMonoidHom) u)

theorem val_ne_zero (hξ : IsCptGen ξ) [Nontrivial R] {a : Ω} {r : Rˣ} (h : ValAt ξ z a r) : a ≠ 0 := by
  rintro rfl
  obtain ⟨hz, -⟩ := val_spec h
  have := val_unique hξ h (val_zero hz)
  exact r.ne_zero this

theorem val_inv₀ {F : Type} [Field F] {z : Sp F ⟶ X} {a : Ω} {r : F} (hr : r ≠ 0) (h : ValAt ξ z a r) :
    ValAt ξ z a⁻¹ r⁻¹ := by
  have := val_inv (r := Units.mk0 r hr) h
  simpa using this

theorem val_zpow {F : Type} [Field F] {z : Sp F ⟶ X} {a : Ω} {r : F} (hr : r ≠ 0) (h : ValAt ξ z a r) (n : ℤ) :
    ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨hz, -⟩ := val_spec h
  have hp : ∀ k : ℕ, ∀ {b : Ω} {s : F}, ValAt ξ z b s → ValAt ξ z (b ^ k) (s ^ k) := by
    intro k b s hb
    induction k with
    | zero => simpa using val_one hz
    | succ k ih => rw [pow_succ, pow_succ]; exact val_mul ih hb
  rcases n with k | k
  · simpa using hp k h
  · simpa [zpow_negSucc] using val_inv₀ (pow_ne_zero _ hr) (hp (k + 1) h)

theorem in_chart {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {z : Sp ℂ ⟶ X} {w : (Σ k, J k) → ℂ}
    {c : (k : K) → J k} (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre z, hz⟩ := by
  have h1 := fun k => hw.2 k (c k) (isUnit_iff_ne_zero.2 (hc k))
  refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => (h1 k).1, fun c' => ?_⟩
  simp only
  rw [← Finset.prod_div_distrib]
  refine prod_mem fun k _ => ?_
  obtain ⟨r, hr, -⟩ := (h1 k).2 (c' k)
  obtain ⟨hz', s, hs, -⟩ := hr
  exact ⟨s, hs⟩

theorem coordsAt_smul {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} {z : Sp ℂ ⟶ X} {w : (Σ k, J k) → ℂ}
    (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (hw : CoordsAt ξ y z w) : CoordsAt ξ y z (fun p => c p.1 * w p) := by
  refine ⟨fun k => ?_, fun k c' hu => ?_⟩
  · obtain ⟨c', h'⟩ := hw.1 k
    exact ⟨c', (isUnit_iff_ne_zero.2 (hc k)).mul h'⟩
  · have hu' : IsUnit (w ⟨k, c'⟩) := isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hu.ne_zero)
    obtain ⟨h1, h2⟩ := hw.2 k c' hu'
    refine ⟨h1, fun i => ?_⟩
    obtain ⟨r, hr, hr'⟩ := h2 i
    refine ⟨r, hr, ?_⟩
    show c k * w ⟨k, i⟩ = r * (c k * w ⟨k, c'⟩)
    rw [hr']; ring

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualNumberPointsGlue
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.Chart (dAway dAway_ext dAway_lift isUnit_dAway Ld toL fromL toL_comp fromL_comp fromL_toL)

namespace GlobalTheory.CompanionTheory.Ar.LieFinGlue

variable {R : Type} [CommRing R]

theorem dualMap_algebraMap_eq_dAway (s : R) : dualMap (algebraMap R (Localization.Away s)) = dAway s := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]

theorem dualMap_comp_dualMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (p : B →+* C) (q : A →+* B) :
    (dualMap p).comp (dualMap q) = dualMap (p.comp q) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem span_range_inl {J : Type} (f : J → R) (hf : Ideal.span (Set.range f) = ⊤) :
    Ideal.span (Set.range fun k => (TrivSqZeroExt.inl (f k) : DualNumber R)) = ⊤ := by
  have := congrArg (Ideal.map (TrivSqZeroExt.inlHom R R)) hf
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  exact this

theorem spMap_algebraMap_eq (s : R) :
    spMap (algebraMap (DualNumber R) (Ld s)) = spMap (toL s) ≫ spMap (dAway s) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, toL_comp]

theorem sep_base {X : Scheme.{0}} {J : Type} (f : J → R) (hf : Ideal.span (Set.range f) = ⊤)
    (a b : Sp R ⟶ X)
    (h : ∀ i, spMap (algebraMap R (Localization.Away (f i))) ≫ a =
      spMap (algebraMap R (Localization.Away (f i))) ≫ b) : a = b :=
  Scheme.Cover.hom_ext (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of R) _ hf).openCover _ _
    fun (k : J) => h k

theorem sep_dual {X : Scheme.{0}} {J : Type} (f : J → R) (hf : Ideal.span (Set.range f) = ⊤)
    (a b : Sp (DualNumber R) ⟶ X)
    (h : ∀ i, spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ a =
      spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ b) : a = b := by
  refine Scheme.Cover.hom_ext
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber R)) _ (span_range_inl f hf)).openCover
    _ _ fun (k : J) => ?_
  have hk := h k
  rw [dualMap_algebraMap_eq_dAway] at hk
  show spMap (algebraMap (DualNumber R) (Ld (f k))) ≫ a = spMap (algebraMap (DualNumber R) (Ld (f k))) ≫ b
  rw [spMap_algebraMap_eq, Category.assoc, Category.assoc, hk]

theorem compat_of_pair {X : Scheme.{0}} {J : Type} (f : J → R)
    (w : ∀ i, Sp (DualNumber (Localization.Away (f i))) ⟶ X)
    (hw : ∀ i j (a : Localization.Away (f i) →+* Localization.Away (f i * f j))
      (b : Localization.Away (f j) →+* Localization.Away (f i * f j)),
      a.comp (algebraMap R _) = algebraMap R _ → b.comp (algebraMap R _) = algebraMap R _ →
      spMap (dualMap a) ≫ w i = spMap (dualMap b) ≫ w j)
    (i j : J) (T : CommRingCat.{0}) (α : DualNumber (Localization.Away (f i)) →+* T)
    (β : DualNumber (Localization.Away (f j)) →+* T) (h : α.comp (dAway (f i)) = β.comp (dAway (f j))) :
    Spec.map (CommRingCat.ofHom α) ≫ w i = Spec.map (CommRingCat.ofHom β) ≫ w j := by
  have hi : IsUnit ((α.comp (dAway (f i))) (TrivSqZeroExt.inl (f i))) := (isUnit_dAway (f i)).map α
  have hj : IsUnit ((α.comp (dAway (f i))) (TrivSqZeroExt.inl (f j))) := by
    rw [h]
    exact (isUnit_dAway (f j)).map β
  have hij : IsUnit ((α.comp (dAway (f i))) (TrivSqZeroExt.inl (f i * f j))) := by
    rw [TrivSqZeroExt.inl_mul, map_mul]
    exact hi.mul hj
  obtain ⟨χ, hχ⟩ := dAway_lift (f i * f j) (α.comp (dAway (f i))) hij
  have hu : IsUnit (algebraMap R (Localization.Away (f i * f j)) (f i * f j)) :=
    IsLocalization.Away.algebraMap_isUnit (f i * f j)
  rw [map_mul] at hu
  have ui : IsUnit (algebraMap R (Localization.Away (f i * f j)) (f i)) := isUnit_of_mul_isUnit_left hu
  have uj : IsUnit (algebraMap R (Localization.Away (f i * f j)) (f j)) := isUnit_of_mul_isUnit_right hu
  let a : Localization.Away (f i) →+* Localization.Away (f i * f j) := IsLocalization.Away.lift (f i) ui
  let b : Localization.Away (f j) →+* Localization.Away (f i * f j) := IsLocalization.Away.lift (f j) uj
  have ha : a.comp (algebraMap R _) = algebraMap R _ := IsLocalization.Away.lift_comp _ ui
  have hb : b.comp (algebraMap R _) = algebraMap R _ := IsLocalization.Away.lift_comp _ uj
  have hα : χ.comp (dualMap a) = α := dAway_ext (f i) (by
    rw [RingHom.comp_assoc, ← dualMap_algebraMap_eq_dAway (f i), dualMap_comp_dualMap, ha,
      dualMap_algebraMap_eq_dAway, hχ, dualMap_algebraMap_eq_dAway])
  have hβ : χ.comp (dualMap b) = β := dAway_ext (f j) (by
    rw [RingHom.comp_assoc, ← dualMap_algebraMap_eq_dAway (f j), dualMap_comp_dualMap, hb,
      dualMap_algebraMap_eq_dAway, hχ, dualMap_algebraMap_eq_dAway, h])
  have e := hw i j a b ha hb
  rw [← hα, ← hβ, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, Category.assoc,
    Category.assoc]
  exact congrArg (Spec.map (CommRingCat.ofHom χ) ≫ ·) e

set_option backward.isDefEq.respectTransparency false in

theorem glue_of_compat {X : Scheme.{0}} {J : Type} (f : J → R) (hf : Ideal.span (Set.range f) = ⊤)
    (w : ∀ i, Sp (DualNumber (Localization.Away (f i))) ⟶ X)
    (hc : ∀ k l (T : CommRingCat.{0}) (α : DualNumber (Localization.Away (f k)) →+* T)
      (β : DualNumber (Localization.Away (f l)) →+* T), α.comp (dAway (f k)) = β.comp (dAway (f l)) →
      Spec.map (CommRingCat.ofHom α) ≫ w k = Spec.map (CommRingCat.ofHom β) ≫ w l) :
    ∃ v : Sp (DualNumber R) ⟶ X, ∀ i, spMap (dAway (f i)) ≫ v = w i := by
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber R)) _
    (span_range_inl f hf)).openCover
  let g : ∀ k, 𝒰.X k ⟶ X := fun k => Spec.map (CommRingCat.ofHom (toL (f k))) ≫ w k
  have hg : ∀ k l, pullback.fst (𝒰.f k) (𝒰.f l) ≫ g k = pullback.snd (𝒰.f k) (𝒰.f l) ≫ g l := by
    refine fun (k : J) (l : J) => Scheme.Cover.hom_ext (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.openCover _ _
      fun (i : (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.I₀) => ?_
    let a : Spec ((pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i) ⟶ pullback (𝒰.f k) (𝒰.f l) :=
      (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.f i
    let A : CommRingCat.of (Ld (f k)) ⟶ (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i :=
      Spec.preimage (a ≫ pullback.fst (𝒰.f k) (𝒰.f l))
    let B : CommRingCat.of (Ld (f l)) ⟶ (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i :=
      Spec.preimage (a ≫ pullback.snd (𝒰.f k) (𝒰.f l))
    have ea : Spec.map A = a ≫ pullback.fst (𝒰.f k) (𝒰.f l) := Spec.map_preimage _
    have eb : Spec.map B = a ≫ pullback.snd (𝒰.f k) (𝒰.f l) := Spec.map_preimage _
    have e1 : Spec.map (CommRingCat.ofHom (algebraMap (DualNumber R) (Ld (f k))) ≫ A) =
        Spec.map (CommRingCat.ofHom (algebraMap (DualNumber R) (Ld (f l))) ≫ B) := by
      rw [Spec.map_comp, Spec.map_comp, ea, eb, Category.assoc, Category.assoc]
      exact congrArg (a ≫ ·) pullback.condition
    have key : A.hom.comp (algebraMap (DualNumber R) (Ld (f k))) =
        B.hom.comp (algebraMap (DualNumber R) (Ld (f l))) :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    have hkey : (A.hom.comp (toL (f k))).comp (dAway (f k)) = (B.hom.comp (toL (f l))).comp (dAway (f l)) := by
      rw [RingHom.comp_assoc, RingHom.comp_assoc, toL_comp, toL_comp]
      exact key
    have h := hc k l _ (A.hom.comp (toL (f k))) (B.hom.comp (toL (f l))) hkey
    show a ≫ pullback.fst (𝒰.f k) (𝒰.f l) ≫ Spec.map (CommRingCat.ofHom (toL (f k))) ≫ w k =
      a ≫ pullback.snd (𝒰.f k) (𝒰.f l) ≫ Spec.map (CommRingCat.ofHom (toL (f l))) ≫ w l
    rw [← Category.assoc a, ← Category.assoc a, ← ea, ← eb, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp]
    exact h
  refine ⟨𝒰.glueMorphisms g hg, fun k => ?_⟩
  have hι : 𝒰.f k ≫ 𝒰.glueMorphisms g hg = g k := Scheme.Cover.ι_glueMorphisms 𝒰 g hg k
  have e : spMap (dAway (f k)) = Spec.map (CommRingCat.ofHom (fromL (f k))) ≫ 𝒰.f k := by
    show _ = _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (DualNumber R) (Ld (f k))))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, fromL_comp]
  rw [e, Category.assoc, hι]
  show Spec.map (CommRingCat.ofHom (fromL (f k))) ≫ Spec.map (CommRingCat.ofHom (toL (f k))) ≫ w k = _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fromL_toL, CommRingCat.ofHom_id, Spec.map_id,
    Category.id_comp]

theorem dual_glue : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] (J : Type) [Finite J] (f : J → R),
    Ideal.span (Set.range f) = ⊤ →
  (∀ a b : Sp R ⟶ X, (∀ i, spMap (algebraMap R (Localization.Away (f i))) ≫ a = spMap (algebraMap R (Localization.Away (f i))) ≫ b) → a = b) ∧
  (∀ a b : Sp (DualNumber R) ⟶ X,
    (∀ i, spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ a = spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ b) → a = b) ∧
  ∀ w : ∀ i, Sp (DualNumber (Localization.Away (f i))) ⟶ X,
    (∀ i j (a : Localization.Away (f i) →+* Localization.Away (f i * f j)) (b : Localization.Away (f j) →+* Localization.Away (f i * f j)),
      a.comp (algebraMap R _) = algebraMap R _ → b.comp (algebraMap R _) = algebraMap R _ →
      spMap (dualMap a) ≫ w i = spMap (dualMap b) ≫ w j) →
    ∃ v : Sp (DualNumber R) ⟶ X, ∀ i, spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ v = w i := by
  intro X R _ J _ f hf
  refine ⟨sep_base f hf, sep_dual f hf, fun w hw => ?_⟩
  obtain ⟨v, hv⟩ := glue_of_compat f hf w (compat_of_pair f w hw)
  exact ⟨v, fun i => by rw [dualMap_algebraMap_eq_dAway]; exact hv i⟩

end GlobalTheory.CompanionTheory.Ar.LieFinGlue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsConstStalk
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Flat.KonstReg

theorem exists_const_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : Cpt 𝔐.ξ), (∀ n : ℕ, n ≠ 0 → IsUnit ((n : 𝔐.X.presheaf.stalk p.1))) → ∃ g₀ : c.F →+* 𝔐.X.presheaf.stalk p.1, (genMap 𝔐.ξ p).comp g₀ = 𝔐.cst := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 p hunit
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  letI : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra
  have hs : 𝔐.ξ ≫ (𝔐.f ≫ Y.s) = Spec.map (CommRingCat.ofHom (algebraMap (𝓞 c.F) Ω)) := 𝔐.cst_over
  let h : 𝓞 c.F →+* 𝔐.X.presheaf.stalk p.1 :=
    (𝔐.X.presheaf.germ ⊤ p.1 trivial).hom.comp
      ((𝔐.f ≫ Y.s).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (𝓞 c.F))).inv.hom)
  have hgen : ∀ o : 𝓞 c.F, genMap 𝔐.ξ p (h o) = 𝔐.cst (algebraMap (𝓞 c.F) c.F o) :=
    fun o => Flat.ConstReg.genMap_germ_const 𝔐.ξ (𝔐.f ≫ Y.s) hs p o
  have hu : ∀ o : 𝓞 c.F, o ≠ 0 → IsUnit (h o) := by
    intro o ho
    have hI : (Ideal.span {o}).comap (algebraMap ℤ (𝓞 c.F)) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ho (Ideal.mem_span_singleton_self o) (Algebra.IsIntegral.isIntegral o)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hn
    have hnat : IsUnit ((n.natAbs : ℕ) : 𝔐.X.presheaf.stalk p.1) := hunit _ (Int.natAbs_ne_zero.mpr hn0)
    have hint : IsUnit (h (algebraMap ℤ (𝓞 c.F) n)) := by
      rw [eq_intCast (algebraMap ℤ (𝓞 c.F)), map_intCast]
      rcases Int.natAbs_eq n with hn' | hn'
      · rw [hn']
        simpa using hnat
      · rw [hn']
        simpa using hnat
    exact isUnit_of_dvd_unit (map_dvd h hn) hint
  refine ⟨IsLocalization.lift (M := nonZeroDivisors (𝓞 c.F)) (S := c.F)
    (fun z => hu z.1 (nonZeroDivisors.ne_zero z.2)), ?_⟩
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F))
  ext o
  simp only [RingHom.comp_apply, IsLocalization.lift_eq]
  exact hgen o

end GlobalTheory.CompanionTheory.Ar.Flat.KonstReg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsHodgeLatticeGermSystemStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hodge_lattice_germ_system : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)), IsCptGen ξ → M.IsActOf t.act.act ρ → (∀ q : Cpt ξ, HFree (S.g q).B r) → ∃ 𝓗 : HodgeLat M.lat ρ H.bar r, S.Gives 𝓗 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.germ_gives_hodgeLat | exact GlobalTheory.CompanionTheory.Ar.Flat.germ_gives_hodgeLat | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.germ_gives_hodgeLat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueRationalStatementStatement
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_rational_statement : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat | exact GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat | (intros; apply GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankFiniteFlatTorsionSubschemeEqCardPoints
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LabelCount

open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

theorem emb_ext {τ τ' : E →+* ℂ} (h : ∀ a : 𝓞 E, τ (a : E) = τ' (a : E)) : τ = τ' :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)

theorem rt0_ne_zero (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have h2 := H.sqrt_neg_disc_sq
  rw [h] at h2
  simp at h2
  exact H.d_prime.ne_zero h2

theorem rt0_ne_neg (H : Host E) : H.rt0 ≠ -H.rt0 := by
  intro h
  have h2 : (2 : ℂ) * H.rt0 = 0 := by linear_combination h
  exact rt0_ne_zero H ((mul_eq_zero.mp h2).resolve_left two_ne_zero)

theorem labelEmb_injective (c : Coeff l) : Function.Injective (labelEmb (H := H) c) := by
  have val : ∀ {s t : CMType H ⊕ CMType H}, labelEmb c s = labelEmb c t → ∀ a : 𝓞 E,
      ((labelEmb c s a : c.F) : ℂ) = ((labelEmb c t a : c.F) : ℂ) := fun h a => by rw [h]
  rintro (τ | τ) (τ' | τ') h
  · refine congrArg Sum.inl (Subtype.ext (emb_ext fun a => val h a))
  · exact absurd ((HodgeCptTest.labelEmb_inl_rt c τ).symm.trans
      ((val h H.rt).trans (HodgeCptTest.labelEmb_inr_rt c τ'))) (rt0_ne_neg H)
  · exact absurd ((HodgeCptTest.labelEmb_inl_rt c τ').symm.trans
      ((val h H.rt).symm.trans (HodgeCptTest.labelEmb_inr_rt c τ))) (rt0_ne_neg H)
  · refine congrArg Sum.inr (Subtype.ext (emb_ext fun a => ?_))
    have := val h (H.bar.symm a)
    simpa [labelEmb] using this

def labelCx (H : Host E) : CMType H ⊕ CMType H → (E →+* ℂ) :=
  Sum.elim (fun τ => τ.1) (fun τ => (starRingEnd ℂ).comp τ.1)

theorem labelCx_bijective (H : Host E) : Function.Bijective (labelCx H) := by
  constructor
  · rintro (τ | τ) (τ' | τ') h
    · exact congrArg Sum.inl (Subtype.ext h)
    · have h1 := RingHom.congr_fun h (H.rt : E)
      simp only [labelCx, Sum.elim_inl, Sum.elim_inr, RingHom.comp_apply, τ.2, τ'.2,
        HodgeCptTest.imaginary_root_conj] at h1
      exact absurd h1 (rt0_ne_neg H)
    · have h1 := RingHom.congr_fun h (H.rt : E)
      simp only [labelCx, Sum.elim_inl, Sum.elim_inr, RingHom.comp_apply, τ.2, τ'.2,
        HodgeCptTest.imaginary_root_conj] at h1
      exact absurd h1.symm (rt0_ne_neg H)
    · refine congrArg Sum.inr (Subtype.ext (RingHom.ext fun x => ?_))
      exact (starRingEnd ℂ).injective (RingHom.congr_fun h x)
  · intro σ
    have hsq : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
      simpa using this
    have hrt : σ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
      rw [H.sqrt_neg_disc_sq, ← map_pow, hsq]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hrt with hp | hm
    · exact ⟨.inl ⟨σ, hp⟩, rfl⟩
    · have ht : ((starRingEnd ℂ).comp σ) (H.rt : E) = H.rt0 := by
        simp [hm, HodgeCptTest.imaginary_root_conj]
      refine ⟨.inr ⟨(starRingEnd ℂ).comp σ, ht⟩, RingHom.ext fun x => ?_⟩
      simp [labelCx]

theorem labels_injective_card : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H)
    (c : Coeff l) [Fintype (CMType H)] (Ω : Type) [Field Ω] (cst : c.F →+* Ω),
    Function.Injective (fun s : CMType H ⊕ CMType H => cst.comp (labelEmb c s)) ∧
      Fintype.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
  intro E _ _ _ H l c _ Ω _ cst
  refine ⟨fun s t h => labelEmb_injective c (RingHom.ext fun a => cst.injective (RingHom.congr_fun h a)), ?_⟩
  rw [Fintype.card_of_bijective (labelCx_bijective H), NumberField.Embeddings.card]

end GlobalTheory.CompanionTheory.Ar.LabelCount
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusGeneratorCorrespondenceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_generator_correspondence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G), homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → ∀ (κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ p, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((p : ℤ) * cε 2 I)))), LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (1 : t.G ⟶ t.G) (𝟙 t.G)).left) (LB.oneGen t.PP.L) → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1) → ∀ C : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] ![(p : ℤ), -(p : ℤ)]), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Ym t.G x p) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val C r z J = (val κ (r ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J)⁻¹ * val τ (r ≫ (fst (Tm x p) t.G).left) z J ^ p) → ∀ (j : t.PP.L.ι) (h : pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j ≤ secZ t.G x p ⁻¹ᵁ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j)), ((secZ t.G x p).appLE _ _ h).hom (C.s fun _ => j).val = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.Pf.red_one | exact GlobalTheory.CompanionTheory.Ar.Coc.Pf.red_one | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.Pf.red_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermJetUnitOnChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_jet_unit_on_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ) (j₀ : t.PP.L.ι), ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ → ∃ e₀ : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ, (jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m) e₀ = 1 ∧ ∀ (z : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p)) (J : (Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → (∀ ψ : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀) → val (g.e (p + m + 1)) (homAt x (jq w p m)).left z J = gm (𝟙 _) z ⊤ (unitΓ e₀) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.Pf.frame_test_unit | exact GlobalTheory.CompanionTheory.Ar.Coc.Pf.frame_test_unit | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.Pf.frame_test_unit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermTorsionLiftCompat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Coc.TestPair

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ) (y : Tm x p ⟶ t.G), y = homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p → rQ t.G x p (g.x m) ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left = (homAt x (jq w p m)).left ≫ (lift (jptG t x d g.x (p + m + 1) (0 : Fin 2)) (jptG t x d g.x (p + m + 1) (1 : Fin 2))).left := by
  intro E _ _ _ H _ X0 t k _ p _ _ x d g w m y hy
  subst hy
  obtain ⟨h0, h1⟩ := GlobalTheory.CompanionTheory.Ar.Coc.JetPts.main E H X0 t k p x d g w m
  unfold rQ
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  rw [comp_lift, comp_lift, lift_fst_assoc, lift_snd, h0, h1]

end GlobalTheory.CompanionTheory.Ar.Coc.TestPair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GradedDegreeFormulaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_degree_formula : ∀ (L : Type) [Field L] [NumberField L] (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (r : ℕ) (A : SatFlag B r) (i : Fin r) (f : Fin i → B.carrier) (s : B.carrier), (∀ a, f a ∈ A.F i.castSucc) → LinearIndependent (𝓞 L) f → s ∈ A.F i.succ → s ∉ A.F i.castSucc → A.grDeg i = (Module.finrank ℚ L : ℝ)⁻¹ * (Real.log (Nat.card (A.F i.succ ⧸ (A.F i.castSucc ⊔ Submodule.span (𝓞 L) {s}).comap (A.F i.succ).subtype)) - (1 / 2) * ∑ σ : L →+* ℂ, (Real.log ‖B.gramDet σ (Fin.snoc f s : Fin (i + 1) → B.carrier)‖ - Real.log ‖B.gramDet σ f‖)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GrLine.grDeg_eq | exact GlobalTheory.CompanionTheory.Ar.GrLine.grDeg_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.GrLine.grDeg_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompRootModelPrimesStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_root_model_primes : GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement → HodgeLatticeFlagBound → TrivFlagOnHodge → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S S₀ : Finset ℕ) [Fintype (CMType H)] [DecidableEq (CMType H)] (M : RootModel (CMType H) (D.p + D.q)) [DecidableEq M.K] (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (R : SecondRoots M), Fl.TwoLevels S₀ R.pairs → (∀ p ∈ S, p ∉ S₀ → HT.HTFree 𝔐 p ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ NumberField.discr E) → ∀ φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H), (∀ p ∈ S, p ∉ S₀ → IsFrobLabels c p (φ p)) → R.pairs.IsVertOff M.P ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) ∧ R.LocalAtPlaces D.p ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.linked_two_levels | exact GlobalTheory.CompanionTheory.Ar.Num.linked_two_levels | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.linked_two_levels <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsLiftStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.join_model_points_lift : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (Q : (L : Type) → [Field L] → ((Σ k, R.ι k) → L) → Prop), (∀ f : MRing R.ι, (∃ a, IsMultiHomog f a) → f ∉ R.P → ∃ (L : Type) (_ : Field L) (_ : NumberField L), ∃ w ∈ ptsOver L R.P, aeval w f ≠ 0 ∧ Q L w) → ∀ f : MRing M.ι, (∃ a, IsMultiHomog f a) → f ∉ M.P → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (L' : Type) (_ : Field L') (_ : NumberField L') (e : L →+* L') (w : (Σ k, R.ι k) → L), ∃ z ∈ ptsOver L' (mCoordIdeal (joinOf M R i)), w ∈ ptsOver L R.P ∧ Q L w ∧ (fun p => z (joinInr M.ι R.ι p)) = (fun p => e (w p)) ∧ aeval (fun p => z (joinInl M.ι R.ι p)) f ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoverDense.preimage_dense | exact GlobalTheory.CompanionTheory.Ar.CoverDense.preimage_dense | (intros; apply GlobalTheory.CompanionTheory.Ar.CoverDense.preimage_dense <;> assumption)
end

