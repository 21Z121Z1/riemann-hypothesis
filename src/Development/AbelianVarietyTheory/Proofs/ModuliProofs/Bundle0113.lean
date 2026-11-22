import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0019
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SemicharacterSqEqOneOfSymmetric
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegelDescent

section Points

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem isPullback_square (hA : IsPullback φ G'.hom G.hom f) (φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left)
    (h : IsSquare φ φ₂) : IsPullback φ₂ (G' ⊗ G').hom (G ⊗ G).hom f := by
  have w₁ : (fst G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have w₂ : (snd G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have v₁ : (fst G' G').left ≫ G'.hom = (G' ⊗ G').hom := Over.w _
  have v₂ : (snd G' G').left ≫ G'.hom = (G' ⊗ G').hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst G G).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd G G).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst G G).left = _ ≫ (fst G G).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd G G).left = _ ≫ (snd G G).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ G'.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst G' G').left = _
      refine hA.hom_ext ?_ ?_
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd G' G').left = _
      refine hA.hom_ext ?_ ?_
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

theorem lift_square {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h : IsSquare φ φ₂) {T : Over S'} {T₀ : Over S}
    {τ : T.left ⟶ T₀.left} {a b : T ⟶ G'} {a₀ b₀ : T₀ ⟶ G} (ha : a.left ≫ φ = τ ≫ a₀.left)
    (hb : b.left ≫ φ = τ ≫ b₀.left) : (lift a b).left ≫ φ₂ = τ ≫ (lift a₀ b₀).left := by
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ (fst G G).left = (_ ≫ _) ≫ (fst G G).left
    rw [Category.assoc, h.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
      lift_fst, ha]
  · change (_ ≫ _) ≫ (snd G G).left = (_ ≫ _) ≫ (snd G G).left
    rw [Category.assoc, h.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
      lift_snd, hb]

variable [GrpObj G] [GrpObj G']

theorem exists_liftHom (h : IsGrpPullback G' G f φ) (T : Over S') (T₀ : Over S) (τ : T.left ⟶ T₀.left)
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) :
    ∃ ρ : (T₀ ⟶ G) →* (T ⟶ G'), ∀ x₀ x, ρ x₀ = x ↔ x.left ≫ φ = τ ≫ x₀.left := by
  let r : (T₀ ⟶ G) → (T ⟶ G') := fun x₀ => Over.homMk
    (h.1.lift (τ ≫ x₀.left) T.hom (by rw [Category.assoc, Over.w, hτ])) (h.1.lift_snd _ _ _)
  have hr : ∀ x₀, (r x₀).left ≫ φ = τ ≫ x₀.left := fun x₀ => h.1.lift_fst _ _ _
  have key : ∀ x₀ x, r x₀ = x ↔ x.left ≫ φ = τ ≫ x₀.left := fun x₀ x =>
    ⟨fun e => e ▸ hr x₀, fun e => Over.OverMorphism.ext
      (h.1.hom_ext ((hr x₀).trans e.symm) (by rw [Over.w, Over.w]))⟩
  let U : Over.mk (T.hom ≫ f) ⟶ T₀ := Over.homMk τ hτ
  refine ⟨MonoidHom.mk' r fun a b => (key _ _).2 ?_, key⟩
  rw [← h.2 T (r a) (r b) (U ≫ a) (U ≫ b) (hr a).symm (hr b).symm, ← MonObj.comp_mul]
  rfl

theorem one_comp (h : IsGrpPullback G' G f φ) (T : Over S') (T₀ : Over S) (τ : T.left ⟶ T₀.left)
    (hτ : τ ≫ T₀.hom = T.hom ≫ f) : (1 : T ⟶ G').left ≫ φ = τ ≫ (1 : T₀ ⟶ G).left := by
  obtain ⟨ρ, hρ⟩ := exists_liftHom h T T₀ τ hτ
  exact (hρ _ _).1 (map_one ρ)

omit [GrpObj G'] in

theorem weilIs_congr {X : Scheme.{0}} {a b : X ⟶ S} (e : a = b) (L : LB G.left) (k : ℤ)
    (x y : Over.mk a ⟶ G) (x' y' : Over.mk b ⟶ G) (hx : x.left = x'.left) (hy : y.left = y'.left)
    (c : Γ(X, ⊤)ˣ) (H : Out.WeilIs G L k x y c) : Out.WeilIs G L k x' y' c := by
  subst e
  rw [← Over.OverMorphism.ext hx, ← Over.OverMorphism.ext hy]
  exact H

end Points

section Bundles

variable {X X₀ Y Y₀ : Scheme.{0}}

theorem lbIso_square {P : LB X} {P₀ : LB X₀} (hP : P.IsLB) (hP₀ : P₀.IsLB) {F : X ⟶ X₀} (hw : LBIso P (P₀.pull F))
    {a : Y ⟶ X} {a₀ : Y₀ ⟶ X₀} {ψ : Y ⟶ Y₀} (e : a ≫ F = ψ ≫ a₀) : LBIso (P.pull a) ((P₀.pull a₀).pull ψ) :=
  LBIso.trans (pull_isLB hP _) (pull_isLB hP₀ (ψ ≫ a₀)) (pull_isLB (pull_isLB hP₀ _) _)
    (LBIso.chartPull (chartPullPull P a a rfl) (chartPullSame P₀ _ _ _ a fun _ => e.symm) hw)
    (LBIso.chartPull (chartPullSame P₀ _ _ _ ψ fun _ => rfl) (chartPullPull _ ψ ψ rfl)
      (PolBaseChange.lbIso_refl (pull_isLB hP₀ a₀)))

theorem exists_gen_of_lbIso {L N : LB X} (hL : L.IsLB) (hN : N.IsLB) (H : LBIso L N)
    (h : ∃ t : L.Gen, t.IsGen) : ∃ t : N.Gen, t.IsGen :=
  (CechPic.iso_triv_iff N).1 (LBIso.trans (LB.isLB_triv X) hL hN ((CechPic.iso_triv_iff L).2 h) H)

end Bundles

theorem prod_zpow_single {I H : Type} [Fintype I] [DecidableEq I] [CommGroup H] (l : (I → ℤ) → H)
    (hl : ∀ a b, l (a + b) = l a * l b) (a : I → ℤ) : ∏ u, l (Pi.single u 1) ^ a u = l a := by
  let F : (I → ℤ) →+ Additive H := AddMonoidHom.mk' (fun a => Additive.ofMul (l a)) fun a b => by
    rw [hl, ofMul_mul]
  have e : a = ∑ u, a u • (Pi.single u 1 : I → ℤ) := by
    ext v
    simp [Finset.sum_apply, Pi.single_apply]
  have : F a = ∑ u, a u • F (Pi.single u 1) := by
    conv_lhs => rw [e]
    simp only [map_sum, map_zsmul]
  apply Additive.ofMul.injective
  rw [ofMul_prod]
  simp only [ofMul_zpow]
  exact this.symm

end GlobalTheory.SiegelDescent

namespace GlobalTheory

open SiegelDescent

theorem exists_siegPre_of_descended_data : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (s₀ : Sp K₀ ⟶ Sp o) (s : Sp K ⟶ Sp o) (c : SiegPre h M ζ s) (A₀ : Over (Sp K₀)) [GrpObj A₀] (φ : c.A.left ⟶ A₀.left) (φ₂ : (G2 c.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : Fin h ⊕ Fin h → (𝟙_ (Over (Sp K₀)) ⟶ A₀)), s = spMap i ≫ s₀ → IsGrpPullback c.A A₀ (spMap i) φ → IsSquare φ φ₂ → P₀.IsLB → LBIso c.P (P₀.pull φ₂) → (∀ u, (c.lev (Pi.single u 1)).left ≫ φ = spMap i ≫ (lev₀ u).left) → ∃ c₀ : SiegPre h M ζ s₀, SiegPB c c₀ (spMap i) := by
  intro h M o _ ζ K₀ K _ _ i s₀ s c A₀ _ φ φ₂ P₀ lev₀ hs hp sq hP₀ hw hlev
  have ab : IsAbelianScheme A₀ := (T.abelian_scheme_descent_smooth_dimension K₀ K i A₀ c.A φ hp c.ab).1
  haveI := ab.comm
  haveI := ab.smooth
  haveI := ab.proper
  haveI := ab.geomConnected
  have epi : ∀ (F F' : Type) [Field F] [Field F'] (j : F →+* F'), Epi (spMap j) := fun F F' _ _ j =>
    ((_root_.GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff F F' j).1 _ _ (𝟙 _) (𝟙 _) (spMap j) (IsPullback.of_vert_isIso ⟨by simp⟩)).1
  have hφ : φ ≫ A₀.hom = c.A.hom ≫ spMap i := hp.1.w
  have one := one_comp hp c.A A₀ φ hφ
  have idφ : (𝟙 c.A : c.A ⟶ c.A).left ≫ φ = φ ≫ (𝟙 A₀ : A₀ ⟶ A₀).left := by simp
  have gen := (T.lineBundle_trivial_iso_descend_field K₀ K i _ _ A₀.hom c.A.hom φ inferInstance inferInstance inferInstance hp.1).1
  have rig : ∀ (a : c.A ⟶ c.A ⊗ c.A) (a₀ : A₀ ⟶ A₀ ⊗ A₀), a.left ≫ φ₂ = φ ≫ a₀.left →
      (∃ t : (c.P.pull a.left).Gen, t.IsGen) → ∃ t : (P₀.pull a₀.left).Gen, t.IsGen := fun a a₀ e ht =>
    gen _ (pull_isLB hP₀ _) (exists_gen_of_lbIso (pull_isLB c.isLB _) (pull_isLB (pull_isLB hP₀ _) _)
      (lbIso_square c.isLB hP₀ hw e) ht)
  have symm : LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) := by
    have h₁ : Smooth (A₀ ⊗ A₀).hom := by rw [Over.tensorObj_hom]; infer_instance
    have h₂ : IsProper (A₀ ⊗ A₀).hom := by rw [Over.tensorObj_hom]; infer_instance
    have h₃ : GeometricallyConnected (A₀ ⊗ A₀).hom := by
      rw [Over.tensorObj_hom]; exact GeometricallyConnected.comp _ _
    refine (T.lineBundle_trivial_iso_descend_field K₀ K i _ _ (A₀ ⊗ A₀).hom (c.A ⊗ c.A).hom φ₂ h₁ h₂ h₃ (isPullback_square hp.1 φ₂ sq)).2 _ _ hP₀
      (pull_isLB hP₀ _) ?_
    exact LBIso.trans (pull_isLB hP₀ _) c.isLB (pull_isLB (pull_isLB hP₀ _) _) hw.symm
      (LBIso.trans c.isLB (pull_isLB c.isLB _) (pull_isLB (pull_isLB hP₀ _) _) c.symm
        (lbIso_square c.isLB hP₀ hw (lift_square sq sq.2.symm sq.1.symm)))
  have diag : LBIso (c.P.pull (lift (𝟙 c.A) (𝟙 c.A)).left) ((P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left).pull φ) :=
    lbIso_square c.isLB hP₀ hw (lift_square sq idφ idφ)

  obtain ⟨ρ, hρ⟩ := exists_liftHom hp (𝟙_ _) (𝟙_ _) (spMap i)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  let lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp K₀)) ⟶ A₀) := fun a => ∏ u, lev₀ u ^ a u
  have ρlev : ∀ a, ρ (lev a) = c.lev a := fun a => by
    rw [← prod_zpow_single c.lev c.lev_add a]
    refine (map_prod ρ _ _).trans (Finset.prod_congr rfl fun u _ => ?_)
    rw [map_zpow, (hρ _ _).2 (hlev u)]
  have hlev' : ∀ a, (c.lev a).left ≫ φ = spMap i ≫ (lev a).left := fun a => (hρ _ _).1 (ρlev a)
  have ρinj : Function.Injective ρ := fun x y e => by
    haveI := epi _ _ i
    exact Over.OverMorphism.ext ((cancel_epi (spMap i)).1
      (((hρ x _).1 rfl).symm.trans ((hρ y _).1 e.symm)))
  refine ⟨{ A := A₀, ab := ab, P := P₀, isLB := hP₀
            rig₁ := rig _ _ (lift_square sq one idφ) c.rig₁
            rig₂ := rig _ _ (lift_square sq idφ one) c.rig₂
            symm := symm, lev := lev
            lev_add := fun a b => ρinj (by rw [map_mul, ρlev, ρlev, ρlev, c.lev_add])
            lev_tors := fun a => ρinj (by rw [map_pow, ρlev, c.lev_tors, map_one])
            geom := ?_ }, φ, φ₂, hp, sq, hw, hlev'⟩
  intro k _ _ x β z hx hz
  obtain ⟨i', rfl⟩ : ∃ i' : K₀ →+* k, x = spMap i' := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
  obtain ⟨Ω, _, _, j, j', hj⟩ := exists_algClosed_join_of_two_field_extensions K₀ K k i i'
  have e : spMap j' ≫ spMap i' = spMap j ≫ spMap i := by rw [← spMap_comp, ← spMap_comp, hj]
  obtain ⟨g₁, g₂, g₃⟩ := c.geom Ω (spMap j) (j'.comp β) (Units.map j'.toMonoidHom z)
    (by rw [hs, ← Category.assoc, ← e, Category.assoc, hx, spMap_comp]) (congrArg j' hz)
  obtain ⟨σ, hσ⟩ := exists_liftHom hp (Over.mk (spMap j)) (Over.mk (spMap i')) (spMap j') e
  have σinj : Function.Injective σ := fun x y e => by
    haveI := epi _ _ j'
    exact Over.OverMorphism.ext ((cancel_epi (spMap j')).1
      (((hσ x _).1 rfl).symm.trans ((hσ y _).1 e.symm)))
  have pt : ∀ a, (toUnit (Over.mk (spMap j)) ≫ c.lev a).left ≫ φ =
      spMap j' ≫ (toUnit (Over.mk (spMap i')) ≫ lev a).left := fun a => by
    change (spMap j ≫ (c.lev a).left) ≫ φ = spMap j' ≫ spMap i' ≫ (lev a).left
    rw [Category.assoc, hlev', reassoc_of% e]
  have σlev : ∀ a, σ (toUnit _ ≫ lev a) = toUnit _ ≫ c.lev a := fun a => (hσ _ _).2 (pt a)
  refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
  · rw [← g₁ a, ← σlev, map_eq_one_iff σ σinj]
  · obtain ⟨a, ha⟩ := g₂ (σ g) (by rw [← map_pow, hg, map_one])
    exact ⟨a, σinj ((σlev a).trans ha)⟩
  · have hD := pull_isLB hP₀ (lift (𝟙 A₀) (𝟙 A₀)).left
    refine (T.weilPairing_fieldExtension_iff _ A₀ k Ω j' (spMap i') _ _ _ _ _ ab hD).1 ?_
    have H := (weilIs_grpPullback_of_comm _ _ A₀ c.A (spMap i) φ _ _ hD (pull_isLB c.isLB _) hp diag _ _ _ _
      (pushPt hφ _) (pushPt hφ _) _ rfl rfl).1 (g₃ a b)
    rw [map_zpow]
    exact weilIs_congr e.symm _ _ _ _ _ _ (pt a) (pt b) _ H

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHalfChar
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.PTheta
open scoped BigOperators Real

namespace GlobalTheory.ThetaPoint

open CanTh

theorem exists_linearEquiv_lift (hmul : Out.MulNSt) (P : Out.PolAV (Sp ℂ)) {L : LB P.A.left} {d g : ℕ}
    (u : HolUnif P.A L d) (a : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (hadd : ∀ z w, a (z + w) = a z * a w)
    (hon : Function.Surjective a) (hol : IsHolTo Set.univ fun z => (a z).left) (hker : {z | a z = 1}.Countable) :
    ∃ F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin d → ℂ), ∀ z, u.ex (F z) = a z := by
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  obtain ⟨u₀, -, hlift⟩ := AbelianExp.exists_holUnif hmul hval (holFamily_lift hval)
    (isTopologicalGroup_complexPoints hval) (PointsCompact.compactSpace_points_polAV hval hvalaff)
    (HolChart.exists_holomorphic_chart hval hvalaff exists_holomorphic_section_of_etale) P
  have cnt : ∀ {L : LB P.A.left} {d : ℕ} (u : HolUnif P.A L d), (u.Λ : Set (Fin d → ℂ)).Countable := fun u =>
    countable_of_isDiscrete_finiteDimensional (isDiscrete_iff_discreteTopology.2 u.discrete)
  have key : ∀ (n : ℕ) (a : (Fin n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), (∀ z w, a (z + w) = a z * a w) →
      Function.Surjective a → (IsHolTo Set.univ fun z => (a z).left) → {z | a z = 1}.Countable →
      ∃ F : (Fin n → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ), ∀ z, u₀.ex (F z) = a z := by
    intro n a hadd hon hol hker
    have h0 : a 0 = 1 := by
      have := hadd 0 0
      rw [add_zero] at this
      exact mul_eq_left.1 this.symm
    obtain ⟨G, hG0, hGa, hGe⟩ := hlift n a hol h0
    have hF := EndoLinear.fderiv_lifts u₀.ex u₀.ex_add u₀.Λ u₀.ker u₀.discrete a hadd G hG0
      hGa.differentiableAt hGe
    have hi : Function.Injective (fderiv ℂ G 0) :=
      realLinear_injective_of_countable_ker ((fderiv ℂ G 0).restrictScalars ℝ).toLinearMap
        (hker.mono fun x (hx : fderiv ℂ G 0 x = 0) => by
          change a x = 1
          rw [← hF, hx, CubeValues.ex_zero])
    have hs : Function.Surjective (fderiv ℂ G 0) :=
      realLinear_surjective_of_mod_countable ((fderiv ℂ G 0).restrictScalars ℝ).toLinearMap (cnt u₀) fun y => by
        obtain ⟨x, hx⟩ := hon (u₀.ex y)
        refine ⟨x, (u₀.ker _).1 ?_⟩
        have := u₀.ex_add (y - fderiv ℂ G 0 x) (fderiv ℂ G 0 x)
        rw [sub_add_cancel, hF, hx] at this
        exact mul_eq_right.1 this.symm
    exact ⟨LinearEquiv.ofBijective (fderiv ℂ G 0).toLinearMap ⟨hi, hs⟩, hF⟩
  obtain ⟨F₁, h₁⟩ := key g a hadd hon hol hker
  obtain ⟨F₀, h₀⟩ := key d u.ex u.ex_add u.ex_onto (fun U f => by simpa using u.hol U f)
    ((cnt u).mono fun z hz => (u.ker z).1 hz)
  exact ⟨F₁.trans F₀.symm, fun z => by rw [← h₀, ← h₁]; simp⟩

theorem isHolTo_fibre {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {S X Z : Scheme.{0}} {p : Z ⟶ X}
    {q : Z ⟶ Sp ℂ} {s : X ⟶ S} {y : Sp ℂ ⟶ S} (H : IsPullback p q s y) (c : V → (Sp ℂ ⟶ Z))
    (hq : ∀ w, c w ≫ q = 𝟙 _) (ha : IsHolTo Set.univ fun w => c w ≫ p) : IsHolTo Set.univ c := by
  intro U f
  refine holFamily_of_affine valAt'_rules Set.univ Z c (fun w₀ _ => ?_) U f
  obtain ⟨US, hUS, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤)
    (x := y (default : PrimeSpectrum ℂ)) trivial
  have hyU : ⊤ ≤ y ⁻¹ᵁ US := (top_le_preimage_iff_mem y US).2 hy
  have hs : (c w₀ ≫ p) (default : PrimeSpectrum ℂ) ∈ s ⁻¹ᵁ US := by
    rw [← top_le_preimage_iff_mem, ← top_le_preimage_comp, Category.assoc, H.w, ← Category.assoc, hq,
      Category.id_comp]
    exact hyU
  obtain ⟨U₁, hU₁, hx₁, hle⟩ := exists_isAffineOpen_mem_and_subset hs
  have hle : U₁ ≤ s ⁻¹ᵁ US := hle
  set W : Z.Opens := p ⁻¹ᵁ U₁ ⊓ q ⁻¹ᵁ ⊤ with hW
  have hiff : ∀ w, ⊤ ≤ c w ⁻¹ᵁ W ↔ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ U₁ := fun w => by
    rw [hW, top_le_preimage_inf, top_le_preimage_comp]
    exact ⟨fun h => h.1, fun h => ⟨h, fun _ _ => trivial⟩⟩
  have hV : IsAffineOpen W := by
    have : IsAffine _ := isAffineOpen_top (Sp ℂ)
    have : IsAffine _ := hU₁
    have : IsAffine _ := hUS
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := US) (UT := ⊤) (UX := U₁) hyU hle hW).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := US) (UT := ⊤) (UX := U₁) hyU hle hW).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ hUS (isAffineOpen_top _) hU₁)
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  refine ⟨W, hV, (hiff w₀).2 ((top_le_preimage_iff_mem _ _).2 hx₁), ?_, fun g => ?_⟩
  · simpa only [hiff] using (ha U₁ 0).1
  · have hg : g ∈ Subring.closure _ := hgen.ge (Subring.mem_top g)
    induction hg using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · refine ((ha U₁ t).2.mono fun w hw => ⟨hw.1, (hiff w).1 hw.2⟩).congr fun w hw => ?_
        exact valAt'_appLE (c w) p U₁ W _ t hw.2
      · refine (differentiableOn_const (valAt' (𝟙 (Sp ℂ)) ⊤ t)).congr fun w hw => ?_
        exact (valAt'_appLE (c w) q ⊤ W _ t hw.2).trans (by rw [hq])
    | zero => simpa only [valAt'_zero] using differentiableOn_const (0 : ℂ)
    | one => exact (differentiableOn_const (1 : ℂ)).congr fun w hw => valAt'_one _ hw.2
    | add x y _ _ hx hy => simpa only [valAt'_add] using hx.fun_add hy
    | neg x _ hx => simpa only [valAt'_neg] using hx.fun_neg
    | mul x y _ _ hx hy => simpa only [valAt'_mul] using hx.fun_mul hy

section Frame

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}

def IsHolFrame (L : LB X) (x : V → (Sp ℂ ⟶ X)) (fr : L.ι → V → ℂ) : Prop :=
  (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ x z ⁻¹ᵁ L.U j}) ∧ (∀ j z, ⊤ ≤ x z ⁻¹ᵁ L.U j → fr j z ≠ 0) ∧
    ∀ j j' z, ⊤ ≤ x z ⁻¹ᵁ (L.U j ⊓ L.U j') → fr j z = valAt' (x z) (L.U j ⊓ L.U j') (L.g j j').val * fr j' z

def IsSecFn (L : LB X) (x : V → (Sp ℂ ⟶ X)) (fr : L.ι → V → ℂ) (θ : V → ℂ) : Prop :=
  ∃ s : L.Sec, ∀ j z, ⊤ ≤ x z ⁻¹ᵁ L.U j → valAt' (x z) (L.U j) (s.f j) = θ z * fr j z

theorem exists_frame_ratio {L : LB X} (hL : L.IsLB) {x : V → (Sp ℂ ⟶ X)}
    (ho : ∀ j, IsOpen {z | ⊤ ≤ x z ⁻¹ᵁ L.U j}) {fr fr' : L.ι → V → ℂ} (h : IsHolFrame L x fr)
    (h' : IsHolFrame L x fr') : ∃ r : V → ℂ, Differentiable ℂ r ∧ (∀ z, r z ≠ 0) ∧
      ∀ j z, ⊤ ≤ x z ⁻¹ᵁ L.U j → fr' j z = r z * fr j z := by
  have hc : ∀ z, ∃ j, ⊤ ≤ x z ⁻¹ᵁ L.U j := fun z => by
    have h : x z (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    exact ⟨i, (top_le_preimage_iff_mem _ _).2 hi⟩
  choose ch hch using hc
  have key : ∀ j z, ⊤ ≤ x z ⁻¹ᵁ L.U j → fr' (ch z) z * (fr (ch z) z)⁻¹ = fr' j z * (fr j z)⁻¹ := fun j z hj => by
    have k := (top_le_preimage_inf _ _ _).2 ⟨hch z, hj⟩
    have n := valAt'_unit_ne_zero _ k (L.g _ _)
    have n' := h.2.1 j z hj
    rw [h.2.2 _ _ _ k, h'.2.2 _ _ _ k]
    field_simp
  refine ⟨fun z => fr' (ch z) z * (fr (ch z) z)⁻¹, fun z => ?_,
    fun z => mul_ne_zero (h'.2.1 _ _ (hch z)) (inv_ne_zero (h.2.1 _ _ (hch z))), fun j z hj => ?_⟩
  · exact ((((h'.1 (ch z)).mul ((h.1 (ch z)).inv (h.2.1 _))).congr fun w hw => key _ w hw).differentiableAt
      ((ho _).mem_nhds (hch z)))
  · simp only [key j z hj]
    rw [inv_mul_cancel_right₀ (h.2.1 j z hj)]

end Frame

theorem exists_unique_half_char (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g)
    {Hm : Matrix (Fin P.g) (Fin P.g) ℂ} {χ : u.Λ → ℂ} {Ef : LinearMap.BilinForm ℤ u.Λ} (hAH : u.IsAH Hm χ)
    (hsec : ∀ θ, u.IsThetaFn Hm χ 1 θ → ∃ s, u.IsFnPow 1 s θ)
    (hE : ∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) (hbij : Function.Bijective Ef) {g : ℕ}
    (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ)) (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef)
    (hform : ∀ z w, hermForm Hm (F z) (F w) = hermForm (imInv τ) (k z) (k w))
    (hΛ : ∀ z, F z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, k z = (fun i => (m i : ℂ)) + τ *ᵥ fun i => (n i : ℂ)) :
    ∃ a b : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧
      (∃ fr, IsHolFrame P.L (fun z => (u.ex (F z)).left) fr ∧ (∀ j, fr j 0 = u.fr j 0) ∧
        IsSecFn P.L (fun z => (u.ex (F z)).left) fr fun z => theta a b (k z) τ) ∧
      ∀ a' b' : Fin g → ℝ, (∀ i, a' i = 0 ∨ a' i = 1 / 2) → (∀ i, b' i = 0 ∨ b' i = 1 / 2) →
        ∀ fr, IsHolFrame P.L (fun z => (u.ex (F z)).left) fr →
          (IsSecFn P.L (fun z => (u.ex (F z)).left) fr fun z => theta a' b' (k z) τ) → a' = a ∧ b' = b := by
  have dl : ∀ {m n : ℕ} (T : (Fin m → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)), Differentiable ℂ fun z => T z := fun T =>
    (LinearMap.toContinuousLinearMap T.toLinearMap).differentiable
  have ch := SymmetricSemicharacter.exists_chart u valAt'_rules P.isLB
  have per : ∀ (l : u.Λ) z, u.ex (z + l) = u.ex z := fun l z => CubeValues.ex_add_period u z l l.2
  obtain ⟨a, b, ha, hb, hlaw⟩ := exists_half_char u.Λ Hm χ (k.symm.trans F) hs hp
    (fun z w => by simp [hform]) (fun z => by simp [hΛ])
    (semicharacter_sq_eq_one_of_symmetric P u Hm χ hAH) (fun l m z => by
      obtain ⟨i, hi⟩ := ch z
      have h1 := hAH.2.2.2 (l + m) i z hi
      have h2 := hAH.2.2.2 m i z hi
      have h3 := hAH.2.2.2 l i (z + m) (by rwa [per])
      have e : z + m + l = z + (l + m : u.Λ) := by rw [Submodule.coe_add]; abel
      rw [h3, h1, e] at h2
      refine mul_right_cancel₀ (u.fr_ne i (z + (l + m : u.Λ)) (by rwa [per])) (h2.trans ?_)
      simp only [hermForm]
      ring)
  have hth : u.IsThetaFn Hm χ 1 fun v => canTh τ a b ((k.symm.trans F).symm v) :=
    ⟨(differentiable_canTh hp a b).comp (dl _), fun l z => by rw [pow_one]; exact hlaw l z⟩
  let Q : (Fin g → ℂ) → ℂ := fun ζ => cexp (π / 2 * (ζ ⬝ᵥ imInv τ *ᵥ ζ))
  have hQ : Differentiable ℂ Q := by
    simp only [Q, dotProduct, mulVec]
    fun_prop
  have hfr : IsHolFrame P.L (fun z => (u.ex (F z)).left) fun j z => u.fr j (F z) :=
    ⟨fun j => (u.fr_hol j).comp (dl F).differentiableOn fun _ hz => hz, fun j z hz => u.fr_ne j _ hz,
      fun j j' z hz => u.fr_compat j j' _ hz⟩
  refine ⟨a, b, ha, hb, ⟨fun j z => Q (k z) * u.fr j (F z),
    ⟨fun j => (hQ.comp (dl k)).differentiableOn.mul (hfr.1 j),
      fun j z hz => mul_ne_zero (Complex.exp_ne_zero _) (hfr.2.1 j z hz),
      fun j j' z hz => (congrArg (Q (k z) * ·) (hfr.2.2 j j' z hz)).trans (mul_left_comm _ _ _)⟩,
    fun j => by simp [Q], ?_⟩, fun a' b' ha' hb' fr h ⟨s, hs'⟩ => ?_⟩
  · obtain ⟨s, hs⟩ := hsec _ hth
    refine ⟨secOfPowOne s, fun j z hz => ?_⟩
    refine (valAt'_res _ (powChart_eq (fun _ => j)).ge (powFn s fun _ => j) hz).trans ((hs (fun _ => j) (F z)
      (top_le_preimage_mono _ (powChart_eq (fun _ => j)).ge hz)).trans ?_)
    simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, canTh, thetaChar_eq_theta, pow_one, Q]
    ring
  · obtain ⟨r, hr, hr0, hrf⟩ := exists_frame_ratio P.isLB
      (fun j => (u.hol _ 0).1.preimage (dl F).continuous) hfr h
    let θ : (Fin P.g → ℂ) → ℂ := fun v => theta a' b' (k (F.symm v)) τ * r (F.symm v)
    have hd : Differentiable ℂ fun z => theta a' b' z τ := by
      simpa only [← thetaChar_eq_theta] using differentiable_thetaChar (mem_thetaDomain hp) a' b'
    have hv : ∀ j v, ⊤ ≤ (u.ex v).left ⁻¹ᵁ P.L.U j → valAt' (u.ex v).left (P.L.U j) (s.f j) = θ v * u.fr j v := by
      intro j v hj
      obtain ⟨z, rfl⟩ := F.surjective v
      refine (hs' j z hj).trans ?_
      rw [hrf j z hj]
      simp only [θ, LinearEquiv.symm_apply_apply, _root_.mul_assoc]
    have hθ : u.IsThetaFn Hm χ 1 θ := by
      refine ⟨(hd.comp ((dl k).comp (dl F.symm))).mul (hr.comp (dl F.symm)), fun l z => ?_⟩
      obtain ⟨j, hj⟩ := ch z
      have hj' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ P.L.U j := by rwa [per]
      have e := hv j _ hj'
      rw [per, hv j z hj, hAH.2.2.2 l j z hj] at e
      refine mul_right_cancel₀ (u.fr_ne j _ hj') (e.symm.trans ?_)
      simp only [hermForm]
      ring
    have hne : (fun v => canTh τ a b ((k.symm.trans F).symm v)) ≠ 0 := fun h0 =>
      canTh_ne_zero hs hp a b (funext fun z => by simpa using congrFun h0 ((k.symm.trans F) z))
    have hdep : ¬ LinearIndependent ℂ ![fun v => canTh τ a b ((k.symm.trans F).symm v), θ] := fun hli => by
      have := card_le_pow_of_linearIndependent_theta_principal SiegelNormalForm.exists_normal_form
        (ClassicalTheta.card_le_pow_of_linearIndependent fourierCoeff_unitCube_translate_of_entire_periodic
          (entire_periodic_eq_zero_of_fourierCoeff_eq_zero fourierCoeff_unitCube_translate_of_entire_periodic))
        P.g u.Λ u.discrete u.full Hm χ Ef hAH.1 hAH.2.1 hAH.2.2.1 hE hbij 1 le_rfl 2 _
        (fun i => by fin_cases i; exacts [hth, hθ]) hli
      simp at this
    rw [LinearIndependent.pair_iff' hne] at hdep
    push Not at hdep
    obtain ⟨c, hc⟩ := hdep
    have hcz : ∀ z, theta a' b' z τ = c * Q z * (r (k.symm z))⁻¹ * theta a b z τ := fun z => by
      have e := congrFun hc (F (k.symm z))
      simp only [θ, Pi.smul_apply, smul_eq_mul, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
        LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply, canTh,
        thetaChar_eq_theta] at e
      rw [mul_right_comm, eq_mul_inv_iff_mul_eq₀ (hr0 _), ← e, _root_.mul_assoc]
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact theta_ne_zero (τ := τ) ⟨hs, hp⟩ a' b' (funext fun z => by simp [hcz])
    exact half_char_unique hs hp ha hb ha' hb'
      (((differentiable_const c).mul hQ).mul ((hr.comp (dl k.symm)).inv fun z => hr0 _))
      (fun z => mul_ne_zero (mul_ne_zero hc0 (Complex.exp_ne_zero _)) (inv_ne_zero (hr0 _))) hcz

end GlobalTheory.ThetaPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalPolarisationVolumeFormSymmetricAmpleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), Vol P.A.hom P.L P.g 1 ∧ FormIs P P.L (𝟙 P.A) ∧ SymB P.L ∧ MapDeg (𝟙 P.A.left) 1 ∧ (∃ (m : ℕ) (th : Fin (m + 1) → (lbPow P.L 4).Sec), VAmp P.A.hom (lbPow P.L 4) th) ∧ ∀ k : ℕ, (k : K) ≠ 0 → ∃ pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A), TorsBasis P.A k pt ∧ (k ≠ 1 → ActsBy pt (𝟙 P.A) (1 : Matrix _ _ (ZMod k))) := by
  first | exact @GlobalTheory.principal_polarisation_numerics | exact GlobalTheory.principal_polarisation_numerics | (intros; apply GlobalTheory.principal_polarisation_numerics <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLevelPullback_id_comp_cancel : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (s'' : S'' ⟶ Sp o) (t : TObj g k J b s) (t' : TObj g k J b s') (t'' : TObj g k J b s''), TMap t t (𝟙 S) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S'), TMap t' t f → (TMap t'' t' f' ↔ TMap t'' t (f' ≫ f)) := by
  first | exact @GlobalTheory.ZM.tmap_id_comp_cancel | exact GlobalTheory.ZM.tmap_id_comp_cancel | (intros; apply GlobalTheory.ZM.tmap_id_comp_cancel <;> assumption)
end

