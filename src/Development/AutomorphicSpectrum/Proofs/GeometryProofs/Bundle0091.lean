import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0087
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaMultiplierNormalForm
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0015
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieMove

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {R : Type} [CommRing R] {x : Sp R ⟶ S'}

theorem fst_comp_alg : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]
  exact Spec.map_id _

theorem epsMul_comp_alg (c : R) : Spec.map (CommRingCat.ofHom (epsMul c)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e : (epsMul c).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) := by
    ext r <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]

def pushEps (h : IsGrpPullback G' G f φ) (p : epsAt x ⟶ G') : epsAt (x ≫ f) ⟶ G :=
  Over.homMk (p.left ≫ φ) (by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w p]
    exact Category.assoc _ _ _)

def liftEps (h : IsGrpPullback G' G f φ) (v : epsAt (x ≫ f) ⟶ G) : epsAt x ⟶ G' :=
  Over.homMk (h.1.lift v.left (epsAt x).hom ((Over.w v).trans (Category.assoc _ _ _).symm)) (h.1.lift_snd _ _ _)

theorem pushEps_left (h : IsGrpPullback G' G f φ) (p : epsAt x ⟶ G') : (pushEps h p).left = p.left ≫ φ := rfl

theorem liftEps_left (h : IsGrpPullback G' G f φ) (v : epsAt (x ≫ f) ⟶ G) : (liftEps h v).left ≫ φ = v.left :=
  h.1.lift_fst _ _ _

theorem push_lift (h : IsGrpPullback G' G f φ) (v : epsAt (x ≫ f) ⟶ G) : pushEps h (liftEps h v) = v :=
  Over.OverMorphism.ext (liftEps_left h v)

theorem pushEps_inj (h : IsGrpPullback G' G f φ) : Function.Injective (pushEps (x := x) h) := fun p q e =>
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w p).trans (Over.w q).symm))

theorem pushEps_mul (h : IsGrpPullback G' G f φ) (p q : epsAt x ⟶ G') :
    pushEps h (p * q) = pushEps h p * pushEps h q := by
  let U : epsAt (x ≫ f) ⟶ Over.mk ((epsAt x).hom ≫ f) := Over.homMk (𝟙 _) (by simp)
  let V : Over.mk ((epsAt x).hom ≫ f) ⟶ epsAt (x ≫ f) := Over.homMk (𝟙 _) (by simp)
  have UV : U ≫ V = 𝟙 _ := Over.OverMorphism.ext (by simp [U, V])
  have e := h.2 (epsAt x) p q (V ≫ pushEps h p) (V ≫ pushEps h q) (by simp [V, pushEps_left])
    (by simp [V, pushEps_left])
  have e' : U ≫ ((V ≫ pushEps h p) * (V ≫ pushEps h q)) = pushEps h p * pushEps h q := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, UV, Category.id_comp, Category.id_comp]
  rw [← e']
  apply Over.OverMorphism.ext
  rw [pushEps_left, ← e]
  simp [U]

theorem one_left (h : IsGrpPullback G' G f φ) :
    (1 : Over.mk x ⟶ G').left ≫ φ = (1 : Over.mk (x ≫ f) ⟶ G).left :=
  congrArg (fun z => z.left) (map_one (pushHom h (Over.mk x)))

theorem tan_iff (h : IsGrpPullback G' G f φ) (p : epsAt x ⟶ G') :
    IsTanAt G' x p ↔ IsTanAt G (x ≫ f) (pushEps h p) := by
  constructor
  · intro t
    show _ ≫ p.left ≫ φ = _
    rw [← Category.assoc, t, one_left h]
  · intro t
    refine h.1.hom_ext ?_ ?_
    · rw [Category.assoc, one_left h]
      exact t
    · have w := Over.w p
      have w₁ := Over.w (1 : Over.mk x ⟶ G')
      rw [Category.assoc, w, w₁]
      show _ ≫ Spec.map _ ≫ x = x
      rw [← Category.assoc, fst_comp_alg, Category.id_comp]

def pullModel {L : Type} [AddCommGroup L] [Module R L] (h : IsGrpPullback G' G f φ) (M : LieModel G (x ≫ f) L) :
    LieModel G' x L where
  pt e := liftEps h (M.pt e)
  tan e := (tan_iff h _).2 (by rw [push_lift]; exact M.tan e)
  inj a b e := M.inj ((push_lift h _).symm.trans ((congrArg (pushEps h) e).trans (push_lift h _)))
  onto v t := by
    obtain ⟨e, he⟩ := M.onto _ ((tan_iff h v).1 t)
    exact ⟨e, pushEps_inj h (by rw [push_lift, he])⟩
  add a b := pushEps_inj h (by rw [pushEps_mul, push_lift, push_lift, push_lift, M.add])
  smul c e := by
    refine h.1.hom_ext ?_ ?_
    · rw [liftEps_left, Category.assoc, liftEps_left, M.smul]
    · have w := fun v => Over.w (liftEps (x := x) h v)
      rw [Category.assoc, w, w]
      show Spec.map _ ≫ x = _ ≫ Spec.map _ ≫ x
      rw [← Category.assoc, epsMul_comp_alg]

def pushModel {L : Type} [AddCommGroup L] [Module R L] (h : IsGrpPullback G' G f φ) (M : LieModel G' x L) :
    LieModel G (x ≫ f) L where
  pt e := pushEps h (M.pt e)
  tan e := (tan_iff h _).1 (M.tan e)
  inj a b e := M.inj (pushEps_inj h e)
  onto v t := by
    obtain ⟨e, he⟩ := M.onto (liftEps h v) ((tan_iff h _).2 (by rw [push_lift]; exact t))
    exact ⟨e, by rw [he, push_lift]⟩
  add a b := by rw [M.add, pushEps_mul]
  smul c e := by
    show (M.pt (c • e)).left ≫ φ = _ ≫ (M.pt e).left ≫ φ
    rw [M.smul, Category.assoc]

theorem models_correspond (h : IsGrpPullback G' G f φ) (L : Type) [AddCommGroup L] [Module R L] :
    (∀ M : LieModel G (x ≫ f) L, ∃ M' : LieModel G' x L, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left) ∧
      ∀ M' : LieModel G' x L, ∃ M : LieModel G (x ≫ f) L, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left :=
  ⟨fun M => ⟨pullModel h M, fun _ => liftEps_left h _⟩, fun M' => ⟨pushModel h M', fun _ => rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar.LieMove

theorem GlobalTheory.CompanionTheory.Ar.LieMove.main : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (x : Sp R ⟶ X) (G : Over X) [GrpObj G]
    (G₀ : Over (Sp R)) [GrpObj G₀] (ψ : G₀.left ⟶ G.left) (L : Type) [AddCommGroup L] [Module R L],
    IsGrpPullback G₀ G x ψ → (∀ M : LieModel G x L, ∃ M₀ : LieModel G₀ (𝟙 _) L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left) ∧
      ∀ M₀ : LieModel G₀ (𝟙 _) L, ∃ M : LieModel G x L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left := by
  intro R _ X x G _ G₀ _ ψ L _ _ h
  have key : ∀ y : Sp R ⟶ X, 𝟙 _ ≫ x = y →
      (∀ M : LieModel G y L, ∃ M₀ : LieModel G₀ (𝟙 _) L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left) ∧
        ∀ M₀ : LieModel G₀ (𝟙 _) L, ∃ M : LieModel G y L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left := by
    rintro _ rfl
    exact GlobalTheory.CompanionTheory.Ar.LieMove.models_correspond h L
  exact key x (Category.id_comp x)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreRefineLineBundlesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segre_refine_line_bundles : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : Type) [Finite A] (Λ : A → Lat M.ξ Ω), (∀ p : Cpt M.ξ, ∃ c₀, InChart M.ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c₀ p) → (∀ a, (Λ a).IsVB 1 ⊤) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (deg : A → K' → ℤ), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) ∧ CoordTie o M.ξ (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) ∧ ∀ a, (Λ a).IsDegOn Set.univ y' (deg a) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ExtraBlocks.exists_blocks_of_lines | exact GlobalTheory.CompanionTheory.Ar.ExtraBlocks.exists_blocks_of_lines | (intros; apply GlobalTheory.CompanionTheory.Ar.ExtraBlocks.exists_blocks_of_lines <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StandardSmoothChartOfNonzeroStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_smooth_chart_of_nonzero : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ) (hb : IsMultiHomog β b) (hβ : β ∉ mCoordIdeal y) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)) (hs : s ≠ 0) [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s)], ∃ (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ) (g₀ : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)), Gz.IsHomogeneous (d + 1) ∧ (X c₀ : MvPolynomial _ ℤ) ∣ Gz ∧ (g₀ : Ω) = aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) Gz ∧ g₀ ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀) ∧ ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 → eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncRes.exists_segre_form | exact GlobalTheory.CompanionTheory.Ar.SncRes.exists_segre_form | (intros; apply GlobalTheory.CompanionTheory.Ar.SncRes.exists_segre_form <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaMultiplierNormalFormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_multiplier_normal_form : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (Lr : RigLB A) (_ : CubicalStr A Lr) (g : ℕ) (u₀ : HolUnif A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ : LB A.left) g), ∃ (u : HolUnif A Lr.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.ex = u₀.ex ∧ Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Lr.L.U i → u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_appellHumbert_frame_of_cubical | exact GlobalTheory.CompanionTheory.Ar.exists_appellHumbert_frame_of_cubical | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_appellHumbert_frame_of_cubical <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorBC

private theorem mul_left_congr_of_base_eq {S W : Scheme.{0}} {G : Over S} [GrpObj G] {f f' : W ⟶ S} (h : f = f')
    (y₀ z₀ : Over.mk f ⟶ G) (y₁ z₁ : Over.mk f' ⟶ G) (hy : y₁.left = y₀.left) (hz : z₁.left = z₀.left) :
    (y₁ * z₁).left = (y₀ * z₀).left := by
  subst h
  have e1 : y₁ = y₀ := Over.OverMorphism.ext hy
  have e2 : z₁ = z₀ := Over.OverMorphism.ext hz
  rw [e1, e2]

private theorem pow_eq_one_congr_of_left_eq {S W : Scheme.{0}} {G : Over S} [GrpObj G] {f f' : W ⟶ S} (h : f = f')
    (g₀ : Over.mk f ⟶ G) (g₁ : Over.mk f' ⟶ G) (hg : g₁.left = g₀.left) (N : ℕ) :
    g₁ ^ N = 1 ↔ g₀ ^ N = 1 := by
  subst h
  have e : g₁ = g₀ := Over.OverMorphism.ext hg
  rw [e]

theorem isTorsionAlong_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R') (Γ' : BT.QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ φ F → Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom φ) ≫ x) N (F ≫ i) := by
  intro R _ _ T _ Γ S G _ x N i hT R' _ _ φ Γ' F hB
  have hw : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom φ) := hB.cart.w
  have hassoc : ∀ {Y : Scheme.{0}} (h : Y ⟶ Spec (CommRingCat.of R')),
      h ≫ (Spec.map (CommRingCat.ofHom φ) ≫ x) = (h ≫ Spec.map (CommRingCat.ofHom φ)) ≫ x :=
    fun _ => (Category.assoc _ _ _).symm
  have lift1 : ∀ (Y : Over (Spec (CommRingCat.of R'))) (y : Y ⟶ Γ'.G),
      (y.left ≫ F) ≫ Γ.G.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ) := by
    intro Y y
    rw [Category.assoc, hw, ← Category.assoc, Over.w y]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, hT.isOver, ← Category.assoc, hw, Category.assoc]
  · intro Y y z y₀ z₀ hy hz
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    let y' : Y' ⟶ Γ.G := Over.homMk (y.left ≫ F) (lift1 Y y)
    let z' : Y' ⟶ Γ.G := Over.homMk (z.left ≫ F) (lift1 Y z)
    let y₁ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk y₀.left ((Over.w y₀).trans (hassoc Y.hom))
    let z₁ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk z₀.left ((Over.w z₀).trans (hassoc Y.hom))
    have hm := hT.mul Y' y' z' y₁ z₁
      (by show y₀.left = (y.left ≫ F) ≫ i; rw [Category.assoc]; exact hy)
      (by show z₀.left = (z.left ≫ F) ≫ i; rw [Category.assoc]; exact hz)
    have hF := hB.mul Y y z y' z' rfl rfl
    rw [← mul_left_congr_of_base_eq (hassoc Y.hom) y₀ z₀ y₁ z₁ rfl rfl, hm, hF, Category.assoc]
  · intro Y y z h
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    have e := hT.inj Y' (Over.homMk (y.left ≫ F) (lift1 Y y) : Y' ⟶ Γ.G)
      (Over.homMk (z.left ≫ F) (lift1 Y z) : Y' ⟶ Γ.G)
      (by show (y.left ≫ F) ≫ i = (z.left ≫ F) ≫ i; rw [Category.assoc, Category.assoc]; exact h)
    have e2 : y.left ≫ F = z.left ≫ F := congrArg (fun m => m.left) e
    apply Over.OverMorphism.ext
    exact hB.cart.hom_ext e2 ((Over.w y).trans (Over.w z).symm)
  · intro Y g
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    let g₁ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk g.left ((Over.w g).trans (hassoc Y.hom))
    rw [← pow_eq_one_congr_of_left_eq (hassoc Y.hom) g g₁ rfl N, hT.kernel Y' g₁]
    constructor
    · rintro ⟨y', hy'⟩
      refine ⟨Over.homMk (hB.cart.lift y'.left Y.hom (Over.w y')) (hB.cart.lift_snd _ _ _), ?_⟩
      show hB.cart.lift y'.left Y.hom (Over.w y') ≫ F ≫ i = g.left
      rw [← Category.assoc, hB.cart.lift_fst]
      exact hy'
    · rintro ⟨y, hy⟩
      refine ⟨(Over.homMk (y.left ≫ F) (lift1 Y y) : Y' ⟶ Γ.G), ?_⟩
      show (y.left ≫ F) ≫ i = g.left
      rw [Category.assoc]
      exact hy

end GlobalTheory.CompanionTheory.Ar.TorBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongGroupPullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TorPull

theorem pow_eq_one_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x : Over.mk a ⟶ G) (x' : Over.mk b ⟶ G) (hx : x.left = x'.left) (N : ℕ) :
    x ^ N = 1 ↔ x' ^ N = 1 := by
  subst h
  rw [Over.OverMorphism.ext hx]

theorem pushHom_injective {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    Function.Injective (pushHom h T) := by
  intro x y e
  apply Over.OverMorphism.ext
  apply h.1.hom_ext
  · exact congrArg (fun z => z.left) e
  · rw [Over.w, Over.w]

theorem exists_lift_isTorsionAlong : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (x' : Sp R ⟶ S') (y : Sp R ⟶ S) (N : ℕ) (i₁ : Γ.G.left ⟶ G.left), IsGrpPullback G' G f φ → x' ≫ f = y → Γ.IsTorsionAlong G y N i₁ → ∃ i' : Γ.G.left ⟶ G'.left, i' ≫ φ = i₁ ∧ Γ.IsTorsionAlong G' x' N i' := by
  intro R _ _ T _ Γ S S' G G' _ _ f φ x' y N i₁ h e hT
  subst e
  have hw : i₁ ≫ G.hom = (Γ.G.hom ≫ x') ≫ f := by rw [hT.isOver, Category.assoc]
  have hfst : h.1.lift i₁ (Γ.G.hom ≫ x') hw ≫ φ = i₁ := h.1.lift_fst _ _ _
  have hsnd : h.1.lift i₁ (Γ.G.hom ≫ x') hw ≫ G'.hom = Γ.G.hom ≫ x' := h.1.lift_snd _ _ _
  generalize h.1.lift i₁ (Γ.G.hom ≫ x') hw = i' at hfst hsnd

  have mk : ∀ (Y : Over (Spec (CommRingCat.of R))) (g : Over.mk (Y.hom ≫ x') ⟶ G'),
      (g.left ≫ φ) ≫ G.hom = Y.hom ≫ x' ≫ f := fun Y g => by
    have w₁ : g.left ≫ G'.hom = Y.hom ≫ x' := Over.w g
    rw [Category.assoc, h.1.w, ← Category.assoc, w₁, Category.assoc]
  refine ⟨i', hfst, ⟨hsnd, ?_, ?_, ?_⟩⟩
  · intro Y a b a₀ b₀ ha hb
    have ea : (Over.homMk (a₀.left ≫ φ) (mk Y a₀) : Over.mk (Y.hom ≫ x' ≫ f) ⟶ G).left = a.left ≫ i₁ := by
      simp [ha, ← hfst]
    have eb : (Over.homMk (b₀.left ≫ φ) (mk Y b₀) : Over.mk (Y.hom ≫ x' ≫ f) ⟶ G).left = b.left ≫ i₁ := by
      simp [hb, ← hfst]
    have e₁ := hT.mul Y a b _ _ ea eb
    have e₂ := h.2 (Over.mk (Y.hom ≫ x')) a₀ b₀ (pushPt h.1.w a₀) (pushPt h.1.w b₀) rfl rfl
    have e₃ := mul_left_congr (Category.assoc Y.hom x' f) (pushPt h.1.w a₀) (pushPt h.1.w b₀)
      (Over.homMk (a₀.left ≫ φ) (mk Y a₀)) (Over.homMk (b₀.left ≫ φ) (mk Y b₀)) rfl rfl
    apply h.1.hom_ext
    · rw [← e₂, e₃, e₁, Category.assoc, hfst]
    · have w₁ : (a₀ * b₀).left ≫ G'.hom = Y.hom ≫ x' := Over.w (a₀ * b₀)
      have w₂ : (a * b).left ≫ Γ.G.hom = Y.hom := Over.w (a * b)
      rw [w₁, Category.assoc, hsnd, ← Category.assoc, w₂]
  · intro Y a b e
    apply hT.inj Y a b
    rw [← hfst, ← Category.assoc, ← Category.assoc, e]
  · intro Y g
    let g₁ : Over.mk (Y.hom ≫ x' ≫ f) ⟶ G := Over.homMk (g.left ≫ φ) (mk Y g)
    have hp : g ^ N = 1 ↔ g₁ ^ N = 1 := by
      rw [← pow_eq_one_congr (Category.assoc Y.hom x' f) (pushHom h (Over.mk (Y.hom ≫ x')) g) g₁ rfl N,
        ← map_pow, ← map_one (pushHom h (Over.mk (Y.hom ≫ x')))]
      exact (pushHom_injective h _).eq_iff.symm
    rw [hp, hT.kernel Y g₁]
    refine exists_congr fun a => ?_
    constructor
    · intro e
      apply h.1.hom_ext
      · rw [Category.assoc, hfst]; exact e
      · have w₁ : g.left ≫ G'.hom = Y.hom ≫ x' := Over.w g
        have w₂ : a.left ≫ Γ.G.hom = Y.hom := Over.w a
        rw [w₁, Category.assoc, hsnd, ← Category.assoc, w₂]
    · intro e
      show a.left ≫ i₁ = g.left ≫ φ
      rw [← e, ← hfst, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.TorPull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongOrderDivides
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled

theorem pow_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ t : T, t ^ N = 1 := by
  intro R _ _ T _ Γ S G _ x N i h t
  let lift : (genPt R ⟶ Γ.G) → (Over.mk ((genPt R).hom ≫ x) ⟶ G) := fun y =>
    Over.homMk (y.left ≫ i) (by
      have w := Over.w y
      simp only [Over.mk_hom, Category.assoc, h.isOver]
      rw [← Category.assoc, w]
      rfl)
  have lift_left : ∀ y, (lift y).left = y.left ≫ i := fun y => rfl
  have lift_mul : ∀ y z, lift (y * z) = lift y * lift z := fun y z => by
    ext1
    rw [h.mul (genPt R) y z (lift y) (lift z) rfl rfl]
    rfl
  have lift_one : lift 1 = 1 := by
    have e : lift 1 * lift 1 = lift 1 := by rw [← lift_mul, _root_.mul_one]
    exact mul_eq_left.mp e
  let L : (genPt R ⟶ Γ.G) →* (Over.mk ((genPt R).hom ≫ x) ⟶ G) :=
    { toFun := lift, map_one' := lift_one, map_mul' := lift_mul }
  have hk : lift (Γ.pt t) ^ N = 1 := (h.kernel (genPt R) (lift (Γ.pt t))).2 ⟨Γ.pt t, rfl⟩
  have hL : L (Γ.pt t ^ N) = L 1 := by
    rw [map_pow, map_one]
    exact hk
  have hy : Γ.pt t ^ N = 1 := h.inj (genPt R) _ _ (by
    have := congrArg (fun g : Over.mk ((genPt R).hom ≫ x) ⟶ G => g.left) hL
    exact this)
  have hp : Γ.pt (t ^ N) = Γ.pt 1 := by rw [map_pow, map_one, hy]
  let c : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  exact Γ.pt_inj (t ^ N) 1 c c (by rw [hp])

end GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongUniqueUpToIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.TorIso

variable {R : Type} [CommRing R] [IsDomain R] {T₁ T₂ : Type} [CommGroup T₁] [CommGroup T₂]
  {Γ₁ : BT.QFGroup R T₁} {Γ₂ : BT.QFGroup R T₂} {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {N : ℕ}
  {i₁ : Γ₁.G.left ⟶ G.left} {i₂ : Γ₂.G.left ⟶ G.left}

theorem exists_hom (h₁ : Γ₁.IsTorsionAlong G x N i₁) (h₂ : Γ₂.IsTorsionAlong G x N i₂) :
    ∃ ψ : Γ₁.G ⟶ Γ₂.G, ψ.left ≫ i₂ = i₁ := by
  let g : Over.mk (Γ₁.G.hom ≫ x) ⟶ G := Over.homMk i₁ h₁.isOver
  have hg : g ^ N = 1 := (h₁.kernel Γ₁.G g).2 ⟨𝟙 _, by simp [g]⟩
  obtain ⟨y, hy⟩ := (h₂.kernel Γ₁.G g).1 hg
  exact ⟨y, hy⟩

theorem hom_mul (h₁ : Γ₁.IsTorsionAlong G x N i₁) (h₂ : Γ₂.IsTorsionAlong G x N i₂) (ψ : Γ₁.G ⟶ Γ₂.G)
    (hψ : ψ.left ≫ i₂ = i₁) {Y : Over (Spec (CommRingCat.of R))} (y z : Y ⟶ Γ₁.G) :
    (y * z) ≫ ψ = (y ≫ ψ) * (z ≫ ψ) := by
  have w : ∀ u : Y ⟶ Γ₁.G, (u.left ≫ i₁) ≫ G.hom = (Over.mk (Y.hom ≫ x)).hom := fun u => by
    have := Over.w u
    simp only [Category.assoc, h₁.isOver, Over.mk_hom]
    rw [← Category.assoc, this]
  let y₀ : Over.mk (Y.hom ≫ x) ⟶ G := Over.homMk (y.left ≫ i₁) (w y)
  let z₀ : Over.mk (Y.hom ≫ x) ⟶ G := Over.homMk (z.left ≫ i₁) (w z)
  have e₁ := h₁.mul Y y z y₀ z₀ rfl rfl
  have e₂ := h₂.mul Y (y ≫ ψ) (z ≫ ψ) y₀ z₀ (by simp [y₀, hψ]) (by simp [z₀, hψ])
  apply h₂.inj
  rw [Over.comp_left, Category.assoc, hψ, ← e₁, e₂]

theorem exists_pt (ψ : Γ₁.G ⟶ Γ₂.G) (t : T₁) : ∃ t', Γ₁.pt t ≫ ψ = Γ₂.pt t' := by
  obtain ⟨t', ht⟩ := BT.QFGroup.exists_eq_comp_pt R T₂ Γ₂ (FractionRing R) (RingHom.id _)
    ((Γ₁.pt t).left ≫ ψ.left) (by
      rw [Category.assoc, Over.w ψ, Over.w (Γ₁.pt t), RingHom.id_comp]
      rfl)
  refine ⟨t', Over.OverMorphism.ext ?_⟩
  rw [Over.comp_left, ht]
  have : CommRingCat.ofHom (RingHom.id (FractionRing R)) = 𝟙 _ := rfl
  rw [this, Spec.map_id, Category.id_comp]

theorem pt_injective (Γ : BT.QFGroup R T₁) : Function.Injective Γ.pt := fun a b h => by
  let o : Spec (CommRingCat.of (FractionRing R)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  exact Γ.pt_inj a b o o (by rw [h])

theorem valAt_comp {B : Type} [CommRing B] {X Y : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ Y) (g : Y ⟶ X)
    (s : Γ(X, ⊤)) : BT.valAt (y ≫ g) ⊤ le_top s = BT.valAt y ⊤ le_top (g.appTop s) := by
  unfold BT.valAt
  congr 1

theorem exists_mulEquiv_isHT : ∀ (R : Type) [CommRing R] [IsDomain R] (T₁ T₂ : Type) [CommGroup T₁] [CommGroup T₂] (Γ₁ : BT.QFGroup R T₁) (Γ₂ : BT.QFGroup R T₂) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i₁ : Γ₁.G.left ⟶ G.left) (i₂ : Γ₂.G.left ⟶ G.left), Γ₁.IsTorsionAlong G x N i₁ → Γ₂.IsTorsionAlong G x N i₂ → ∃ b : T₁ ≃* T₂, ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T₁ →* Rˣ) (w : Module.Dual R L), Γ₁.IsHT i₁ M N χ w → Γ₂.IsHT i₂ M N (χ.comp b.symm.toMonoidHom) w := by
  intro R _ _ T₁ T₂ _ _ Γ₁ Γ₂ S G _ x N i₁ i₂ h₁ h₂
  obtain ⟨ψ, hψ⟩ := exists_hom h₁ h₂
  obtain ⟨ψ', hψ'⟩ := exists_hom h₂ h₁
  have c₁ : ψ ≫ ψ' = 𝟙 _ := h₁.inj _ _ _ (by simp [hψ, hψ'])
  have c₂ : ψ' ≫ ψ = 𝟙 _ := h₂.inj _ _ _ (by simp [hψ, hψ'])
  choose f hf using exists_pt (Γ₁ := Γ₁) (Γ₂ := Γ₂) ψ
  choose f' hf' using exists_pt (Γ₁ := Γ₂) (Γ₂ := Γ₁) ψ'
  have fmul : ∀ a c, f (a * c) = f a * f c := fun a c => pt_injective Γ₂ (by
    rw [← hf, map_mul, map_mul, hom_mul h₁ h₂ ψ hψ, hf, hf])
  let b : T₁ ≃* T₂ :=
    { toFun := f
      invFun := f'
      left_inv := fun t => pt_injective Γ₁ (by rw [← hf', ← hf, Category.assoc, c₁, Category.comp_id])
      right_inv := fun t => pt_injective Γ₂ (by rw [← hf, ← hf', Category.assoc, c₂, Category.comp_id])
      map_mul' := fmul }
  refine ⟨b, ?_⟩
  rintro L _ _ M χ w ⟨s, hs, hv⟩
  refine ⟨ψ'.left.appTop s, fun t => ?_, fun e => ?_⟩
  · have e₁ : (Γ₂.pt t).left ≫ ψ'.left = (Γ₁.pt (f' t)).left := congrArg (fun z => z.left) (hf' t)
    refine (valAt_comp _ _ s).symm.trans ?_
    rw [e₁]
    exact hs (f' t)
  · obtain ⟨v, v₁, v₂, v₃⟩ := hv e
    have e₁ : ψ.left ≫ ψ'.left = 𝟙 _ := congrArg (fun z => z.left) c₁
    refine ⟨v ≫ ψ.left, ?_, ?_, ?_⟩
    · rw [Category.assoc, Over.w ψ, v₁]
    · rw [Category.assoc, hψ, v₂]
    · refine (valAt_comp _ _ s).symm.trans ?_
      rw [Category.assoc, e₁, Category.comp_id]
      exact v₃

end GlobalTheory.CompanionTheory.Ar.BT.TorIso
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionSubgroupBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_subgroup_base_change : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R'] (T : Type) [CommGroup T] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (x' : Spec (CommRingCat.of R') ⟶ S), Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ x = x' → ∀ (N : ℕ) (i : Γ.G.left ⟶ G.left) (i' : Γ'.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Γ'.IsTorsionAlong G x' N i' → ∀ (a : FractionRing R →+* FractionRing R'), a.comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp (algebraMap R R') → (∀ t, Spec.map (CommRingCat.ofHom a) ≫ (Γ.pt t).left ≫ i = (Γ'.pt t).left ≫ i') → ∃ F : Γ'.G.left ⟶ Γ.G.left, F ≫ i = i' ∧ Γ'.IsBaseChange Γ (algebraMap R R') F := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.BaseChange.torsion_isBaseChange | exact GlobalTheory.CompanionTheory.Ar.BT.BaseChange.torsion_isBaseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.BaseChange.torsion_isBaseChange <;> assumption)
end

