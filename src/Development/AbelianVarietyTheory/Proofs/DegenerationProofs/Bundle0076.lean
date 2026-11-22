import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothTorusQuotientOfGoodOpenCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToFSurjectiveFractionRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOfRefine
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gs_sec_compat {Y Z : Scheme.{0}} {M : LB Y} (φ : M.Sec) (r : Z ⟶ Y) (z : Z) {l l' : M.ι}
    (hl : r z ∈ M.U l) (hl' : r z ∈ M.U l') :
    gs r z (M.U l) (φ.f l) = (gm r z (M.U l ⊓ M.U l') (M.g l l')).val * gs r z (M.U l') (φ.f l') := by
  have hm : r z ∈ M.U l ⊓ M.U l' := ⟨hl, hl'⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (φ.compat l l')).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem exists_sec_of_refine : ∀ (Y : Scheme.{0}) (M A : LB Y), M.IsLB → A.IsLB →
    ∀ (c : ChartPull M A (𝟙 Y)) (φ : M.Sec), ∃ s : A.Sec, ∀ (l : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      r z ∈ M.U l → gs r z (M.U l) (φ.f l) = gs r z (A.U (c.idx l)) (s.f (c.idx l)) := by
  intro Y M A hM hA c φ
  have cle : ∀ l (y : Y), y ∈ M.U l → y ∈ A.U (c.idx l) := fun l y hy => c.le l hy
  have glue : ∀ i : A.ι, ∃ a : Γ(Y, A.U i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (l : M.ι),
      r z ∈ A.U i → r z ∈ M.U l →
      gs r z _ a = (gm r z (A.U i ⊓ A.U (c.idx l)) (A.g i (c.idx l))).val * gs r z (M.U l) (φ.f l) := by
    intro i
    let W : M.ι → Y.Opens := fun l => A.U i ⊓ M.U l
    have hW : ∀ l, W l ≤ A.U i ⊓ A.U (c.idx l) := fun l y hy => ⟨hy.1, cle l y hy.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ l, Γ(Y, W l), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) l, r z ∈ W l →
        gs r z (W l) (u l) =
          (gm r z (A.U i ⊓ A.U (c.idx l)) (A.g i (c.idx l))).val * gs r z (M.U l) (φ.f l) :=
      ⟨fun l => (Y.presheaf.map (homOfLE (hW l)).op).hom (A.g i (c.idx l)).val *
          (Y.presheaf.map (homOfLE (inf_le_right : W l ≤ M.U l)).op).hom (φ.f l), fun Z r z l hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans (gs_unit r z _ (hW l hz) _))
          (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W (A.U i)
      (fun l => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨l, hl⟩ := exists_chart hM y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, hy, hl⟩) u
      (fun l l' => fn_ext (V := W l ⊓ W l') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hu _ _ y l hy.1, hu _ _ y l' hy.2, gs_sec_compat φ (𝟙 Y) y hy.1.2 hy.2.2, c.g y l l' hy.1.2 hy.2.2,
          ← _root_.mul_assoc, ← Units.val_mul,
          gm_cocycle hA (𝟙 Y) y hy.1.1 (cle l y hy.1.2) (cle l' y hy.2.2)])
    refine ⟨a, fun Z r z l h₁ h₂ => ?_⟩
    have hz : r z ∈ W l := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z (W l)) (ha l)).trans (hu Z r z l hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun l Z r z hl => ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hM y
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      (gs_unit (𝟙 Y) y _ hy _) (gs_res (𝟙 Y) y _ hy _))).symm)
    rw [ha j _ (𝟙 Y) y l hy.1 hl, ha j' _ (𝟙 Y) y l hy.2 hl,
      ← gm_cocycle hA (𝟙 Y) y hy.1 hy.2 (cle l y hl), Units.val_mul, _root_.mul_assoc]
  · have m := cle l _ hl
    refine Eq.symm ((ha _ Z r z l m hl).trans ?_)
    rw [gm_self hA r z m, Units.val_one, _root_.one_mul]

end GlobalTheory.ZH.UFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOfUnitAt
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.TwistNoBasePoint

section
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits GlobalTheory.NoBasePoint

theorem exists_sec_of_unitAt {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    {φ : I → (Y ⟶ X)} {ε : I → ℤ} {y : Y} (h : UnitAt L φ ε y) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), y ∈ nonzeroLocus s := by
  obtain ⟨s, hs⟩ := h
  choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ y)
  exact ⟨s, (mem_nonzeroLocus s y).2 ⟨fun i => J (𝟙 _ ≫ φ i), Good.mem hJ φ (𝟙 _), hs J hJ⟩⟩

theorem unitAt_twist (hL : Laws) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K))
    (x : baseOver (Sp K) ⟶ P.A) (p : (baseOver (Sp K)).left) (m : ℕ) (b : baseOver (Sp K) ⟶ P.A) :
    UnitAt P.L ![(translPt P.A b).left, (snd (baseOver (Sp K)) P.A).left] ![1, (m : ℤ) + 1]
      ((ptSecT P.A x).left p) := by
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom := geometricallyIntegral_of_smooth _
  let t : Spec (CommRingCat.of K) ⟶ Sp K := 𝟙 _
  have : IsIntegral (Over.mk t ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ (IsPullback.of_hasPullback t P.A.hom).flip
  have : Subsingleton (Over.mk t).left := ⟨spec_pt_eq (k := K)⟩
  have : Nontrivial Γ((Over.mk t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have h1 : Module.finrank Γ((Over.mk t).left, ⊤) (SecM P.A P.L (1 : ℕ) (Over.mk t)) = 1 ^ P.g :=
    hL.globalSectionsRank K P 1 le_rfl
  rw [one_pow] at h1
  have : Nontrivial (SecM P.A P.L (1 : ℕ) (Over.mk t)) := Module.nontrivial_of_finrank_pos (h1 ▸ Nat.one_pos)
  obtain ⟨f, hf⟩ := exists_ne (0 : SecM P.A P.L (1 : ℕ) (Over.mk t))
  let θ : LB.Sec (LPow P.A P.L 1 (Over.mk t)) := SecM.toSec P.A f
  obtain ⟨k, hk⟩ : ∃ k, θ.f k ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Subtype.ext (funext h))
  have hD : (((Over.mk t ⊗ P.A).left.basicOpen (θ.f k) : (Over.mk t ⊗ P.A).left.Opens) :
      Set (Over.mk t ⊗ P.A).left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hk ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
  let y : (Over.mk t ⊗ P.A).left := (ptSecT P.A x).left p
  have good : ∀ a : Over.mk t ⟶ P.A, (ptSecT P.A (a * x)).left p ∈ (Over.mk t ⊗ P.A).left.basicOpen (θ.f k) →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y := fun a ha =>
    unitAt_transl P.isLB θ k a y (by
      rw [← ptSecT_translT] at ha
      exact ha)
  have step : ∀ (m : ℤ) (b a : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, m] y →
      UnitAt P.L (K := Fin 1) (fun _ => (translPt P.A a).left) (fun _ => 1) y →
      UnitAt P.L ![(translPt P.A (b * a)).left, (snd (Over.mk t) P.A).left] ![1, m + 1] y := by
    intro m b a hb ha
    obtain ⟨V, hV, c, hc⟩ := hL.square _ P (Over.mk t) b a p
    refine UnitAt.congr P.isLB (formEq_of_add fun U _ hh => ?_)
      ((hb.mul ha).mul (unitAt_of_local P.isLB _ _ p V hV c hc y))
    simp [Fin.sum_univ_succ]
    module
  have main : ∀ (m : ℕ) (b : Over.mk t ⟶ P.A),
      UnitAt P.L ![(translPt P.A b).left, (snd (Over.mk t) P.A).left] ![1, (m : ℤ) + 1] y := by
    intro m
    induction m with
    | zero =>
      intro b
      obtain ⟨a, h₁, h₂⟩ := exists_two_points t _ hD x (b * x)
      have := step 0 a (a⁻¹ * b) (UnitAt.congr P.isLB (formEq_of_add fun U _ hh => by simp) (good a (h₁ p)))
        (good _ (by rw [_root_.mul_assoc]; exact h₂ p))
      rwa [mul_inv_cancel_left] at this
    | succ m ih =>
      intro b
      obtain ⟨a, h₁, -⟩ := exists_two_points t _ hD x x
      have := step _ _ a (ih (b * a⁻¹)) (good a (h₁ p))
      rwa [inv_mul_cancel_right] at this
  exact main m b

end

theorem exists_sec_twist :
    Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (n : ℕ), 4 ≤ n → ∀ c x : Out.baseOver (Sp k) ⟶ P.A, ∃ s : LB.Sec (Out.twistLB P.A P.L n c), ⊤ ≤ (Out.ptSecT P.A x).left ⁻¹ᵁ Out.nonzeroLocus s) := by
  intro hL _ k _ _ P n hn c x
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  let p : (Out.baseOver (Sp k)).left := IsLocalRing.closedPoint k
  have h : H1.SquareUnits.UnitAt P.L (K := Fin 2)
      ![(snd (Out.baseOver (Sp k)) P.A).left, (Out.translPt P.A c).left] ![((m + 2 : ℕ) : ℤ) - 1, 1]
      ((Out.ptSecT P.A x).left p) := by
    refine H1.SquareUnits.UnitAt.congr P.isLB (H1.SquareUnits.formEq_of_add fun U _ hh => ?_) (unitAt_twist hL k P x p m c)
    simp [Fin.sum_univ_succ]
    module
  obtain ⟨s, hs⟩ := exists_sec_of_unitAt P.isLB h
  refine ⟨s, fun q _ => ?_⟩
  obtain rfl : q = p := Subsingleton.elim (α := PrimeSpectrum k) _ _
  exact hs

end GlobalTheory.TwistNoBasePoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothTorusQuotientOfGoodOpenCoverStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_torus_quotient_of_goodOpen_cover : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → (∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen i V) → ∃ (B : Over (Sp k)) (_ : GrpObj B) (q : G ⟶ B), IsQuot i q ∧ ∀ g, SmoothOfRelativeDimension g G.hom → ∃ a, SmoothOfRelativeDimension a B.hom ∧ g = a + Module.finrank ℤ X := by
  first | exact @GlobalTheory.TorusQuotientGlue.main | exact GlobalTheory.TorusQuotientGlue.main | (intros; apply GlobalTheory.TorusQuotientGlue.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialFibreProjectionAbelianPartStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_specialFibre_projection_abelianPart : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegPre V) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (g : GtCoord (IsLocalRing.maximalIdeal V) D 0 G) (κ : Type) [Field κ] [IsAlgClosed κ] (f : V →+* κ), IsLocalHom f → ∃ π : (Over.mk (spMap f) ⟶ G) →* (Over.mk (spMap f) ⟶ D.P.A), (∀ x, ∃ y : Sp κ ⟶ (thickObj V (IsLocalRing.maximalIdeal V) 0 G).left, y ≫ (fstG (IsLocalRing.maximalIdeal V) 0 G).left = x.left ∧ y ≫ g.pG.left = (π x).left) ∧ ∀ n : ℕ, 1 ≤ n → ∀ b, b ^ n = 1 → ∃ x, x ^ n = 1 ∧ π x = b := by
  first | exact @GlobalTheory.SpecialPoints.exists_projection | exact GlobalTheory.SpecialPoints.exists_projection | (intros; apply GlobalTheory.SpecialPoints.exists_projection <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymLiftGlobalStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symLift_of_pow_eq_one : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ), Odd k → IsUnit (k : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ P.A), x ^ k = 1 → ∃ θ : ThetaGrp P.A P.L k T, SymLift P.A P.L k k x θ := by
  first | exact @GlobalTheory.exists_symLift_global | exact GlobalTheory.exists_symLift_global | (intros; apply GlobalTheory.exists_symLift_global <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionLiftSpecialFibreOfGenericRationalStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_torsion_lift_specialFibre_of_generic_rational : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (W C : Type) [CommRing W] [IsLocalRing W] [Field C] (α : V →+* W) (β : W →+* C) (ga : FractionRing V →+* C), IsLocalHom α → Function.Injective β → β.comp α = ga.comp (algebraMap V (FractionRing V)) → ∀ (X : Scheme.{0}) (y : Sp W ⟶ X) (x : Sp (FractionRing V) ⟶ X), spMap β ≫ y = spMap ga ≫ x → ∃ h : Sp V ⟶ X, spMap α ≫ h = y ∧ jK V ≫ h = x) → UnramExtSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] (C : Type) [Field C] [IsAlgClosed C] (ga : FractionRing V →+* C) (m : ℕ), IsUnit (m : V) → (∀ y : Over.mk (spMap ga ≫ jK V) ⟶ G, y ^ m = 1 → ∃ x : Sp (FractionRing V) ⟶ G.left, spMap ga ≫ x = y.left) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (f : V →+* κ), IsLocalHom f → ∀ x : Over.mk (spMap f) ⟶ G, x ^ m = 1 → ∃ h : baseOver (Sp V) ⟶ G, h ^ m = 1 ∧ spMap f ≫ h.left = x.left := by
  first | exact @GlobalTheory.exists_torsion_lift_of_generic_rational | exact GlobalTheory.exists_torsion_lift_of_generic_rational | (intros; apply GlobalTheory.exists_torsion_lift_of_generic_rational <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTwistedSectionThetaTranslateCoefStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistedSection_thetaTranslate_coef : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (th : SecBT D (𝟙_ _) 1 0), (∀ g : SecBT D (𝟙_ _) 1 0, ∃ b : R, Mult D th g b) → ∀ (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), u.IsGen → ∀ g : SecBT D (𝟙_ _) 1 χ, ∃ b : R, Coef D χ u th g b := by
  first | exact @GlobalTheory.PsiCoef.exists_coef | exact GlobalTheory.PsiCoef.exists_coef | (intros; apply GlobalTheory.PsiCoef.exists_coef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisedModelStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformised_model' : GlobalTheory.Published.SemistableReductionSt → ThmUSt → PolBaseChangeSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), ∃ u : ρ.UTest p y₀, ∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p)) := by
  first | exact @GlobalTheory.exists_uniformised_model | exact GlobalTheory.exists_uniformised_model | (intros; apply GlobalTheory.exists_uniformised_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCarries
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ParTranslate
open GlobalTheory.UT GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar GlobalTheory.ThetaTranslate ReciprocityTheory.ChartRestriction.G.DVR

theorem toStk_onto {F : Type} [Field F] (z : Sp F) : Function.Surjective (toStk z) := fun a => by
  obtain ⟨U, hU, f, rfl⟩ := (Sp F).presheaf.exists_germ_eq a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => (Subsingleton.elim (α := PrimeSpectrum F) z y) ▸ hU
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 f
  exact ⟨x, rfl⟩

theorem isAdd_comm {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {g g' g'' : GtPtF D F} (h : g.IsAdd g' g'') : g'.IsAdd g g'' := by
  rw [isAdd_iff] at h ⊢
  refine ⟨h.1.trans (mul_comm _ _), fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  rw [C.s12, h.2 χ y J hJ, mul_comm]

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
  (w : W0 U)

abbrev Carries (t : SecA A F k) (σ : U.SecGF F k) : Prop :=
  GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w
    (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k
    (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) σ

theorem exists_carries (hw : w.IsGen) (σ : U.SecGF F k) : ∃ t, Carries U F k w t σ := by
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n ≫ U.genF F = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have hn' : U.genF F ≫ n = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  obtain ⟨-, i₂⟩ := isoRelM_bijective (k := k) (m := (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left)
    (g₁ := (snd (TFK (R := R) F) A.A).left) (h₁ := (U.genF F).left) A.isLB U.LG.isLB hw
    (congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)) n.left
    (congrArg (fun q => q.left) hn) (congrArg (fun q => q.left) hn')
  exact (i₂ σ).exists

theorem exists_unit_carries (a : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (l : U.LG.L.ι)
    (hl : ⊤ ≤ (show Sp F ⟶ G.left from a.left ≫ pullback.fst G.hom (jK R)) ⁻¹ᵁ U.LG.L.U l) (y : Sp F)
    (J : (Sp F ⟶ A.A.left) → A.L.ι) (hJ : Good A.L y J) :
    ∃ c : ((Sp F).presheaf.stalk y)ˣ, ∀ t σ, Carries U F k w t σ →
      toStk y (valF (show Sp F ⟶ _ from (lift (𝟙 (TFK (R := R) F)) a).left) _ (σ.f (fun _ => l))) =
        c.val * secVal t (show Sp F ⟶ _ from (ptSecT A.A (a ≫ U.gen.hom)).left) y J := by
  let r : Sp F ⟶ (UnifPre.GF (G := G) F).left := (lift (𝟙 (TFK (R := R) F)) a).left
  let r' : Sp F ⟶ (TFK (R := R) F ⊗ A.A).left := (ptSecT A.A (a ≫ U.gen.hom)).left
  have e₀ : r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = a.left :=
    congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R) F)) a)
  have e₁ : r ≫ (U.genF F).left = r' := by
    have : lift (𝟙 (TFK (R := R) F)) a ≫ U.genF F = ptSecT A.A (a ≫ U.gen.hom) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [ptSecT]
    exact congrArg (fun q => q.left) this
  have e₂ : r' ≫ (snd (TFK (R := R) F) A.A).left =
      (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ U.gen.hom.left := by
    rw [e₀]
    exact congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R) F)) (a ≫ U.gen.hom))
  have m₂ : ((r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R)) y ∈
      U.LG.L.U l := by
    rw [e₀]
    exact (top_le_iff_mem _ _ y).1 hl
  have m₁ : ((r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ U.gen.hom.left) y ∈
      A.L.U (J (r' ≫ (snd (TFK (R := R) F) A.A).left)) := by
    rw [← e₂]
    exact hJ _
  refine ⟨isoVal w (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) y l
    (J (r' ≫ (snd (TFK (R := R) F) A.A).left)) ^ (k : ℤ), fun t σ h => ?_⟩
  have H := (isoRelM_iff w _ k _ h.1 _ h.2.1 t σ).1 h (Sp F) r y l _ m₂ m₁
  rw [Category.comp_id, e₁] at H
  exact (toStk_valF_gs r _ y (mem_wchart.2 fun _ => m₂) _).trans H

theorem exists_const_actVal (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F))
    (a a' : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (h : a' ≫ U.gen.hom = θ.pt * (a ≫ U.gen.hom))
    (l l' : U.LG.L.ι)
    (hl : ⊤ ≤ (show Sp F ⟶ G.left from a.left ≫ pullback.fst G.hom (jK R)) ⁻¹ᵁ U.LG.L.U l)
    (hl' : ⊤ ≤ (show Sp F ⟶ G.left from a'.left ≫ pullback.fst G.hom (jK R)) ⁻¹ᵁ U.LG.L.U l') :
    ∃ c : F, c ≠ 0 ∧ ∀ t t' σ σ', Carries U F k w t σ → Carries U F k w t' σ' → ActVal θ t t' →
      valF (show Sp F ⟶ _ from (lift (𝟙 (TFK (R := R) F)) a).left) _ (σ'.f (fun _ => l)) =
        c * valF (show Sp F ⟶ _ from (lift (𝟙 (TFK (R := R) F)) a').left) _ (σ.f (fun _ => l')) := by
  let y : Sp F := IsLocalRing.closedPoint F
  obtain ⟨J, hJ⟩ := GlobalTheory.UT.CoefBasic.exists_good' A.isLB y
  obtain ⟨c, hc⟩ := exists_unit_carries U F k w a l hl y J hJ
  obtain ⟨c', hc'⟩ := exists_unit_carries U F k w a' l' hl' y J hJ
  let r : Sp F ⟶ (TFK (R := R) F ⊗ A.A).left := (ptSecT A.A (a ≫ U.gen.hom)).left
  have e : r ≫ (translT A.A θ.pt).left = (ptSecT A.A (a' ≫ U.gen.hom)).left := by
    rw [h]
    exact congrArg (fun q => q.left) (ptSecT_translT (a ≫ U.gen.hom) θ.pt)
  obtain ⟨d, hd⟩ := toStk_onto y (c * thetaVal θ r y J * c'⁻¹).val
  refine ⟨d, fun h0 => ?_, fun t t' σ σ' h₁ h₂ h₃ => (toStk y).injective ?_⟩
  · have : Nontrivial ((Sp F).presheaf.stalk y) := inferInstance
    rw [h0, map_zero] at hd
    exact Units.ne_zero _ hd.symm
  · have a₁ := h₃ (Sp F) r y J hJ
    rw [e] at a₁
    rw [map_mul, hd, hc t' σ' h₂, hc' t σ h₁, Units.val_mul, Units.val_mul, _root_.mul_assoc,
      Units.inv_mul_cancel_left, _root_.mul_assoc]
    exact congrArg _ a₁

end

theorem parAt_translate : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) k) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (a a' : u.PtC) (g g' : GtPtF u.D.toPre (PadicAlgCl p)), 1 ≤ k → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk x → a' ≫ u.U.gen.hom = x * (a ≫ u.U.gen.hom) → GtPtF.IsAdd pk.g g g' → u.ParAt k a g → u.ParAt k a' g' := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u k pk x a a' g g' hk hx ha hg hpar w' hw' l' hl'
  have hG := hL.1.globalFns
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  obtain ⟨w₀, hw₀⟩ := u.U.toUnifPre.ext
  obtain ⟨v, hv⟩ := exists_normalisation (D := u.D.toPre) (F := PadicAlgCl p) k pk.g.b
  obtain ⟨ω₀, h₀⟩ := exists_normalisation (D := u.D.toPre) (F := PadicAlgCl p) k g.b
  obtain ⟨ω₁, h₁, -, hco⟩ := CoefPhi.coef_phi hL u.V _ hA u.D (PadicAlgCl p) k hk pk v hv g g' (isAdd_comm hg) ω₀ h₀
  replace hco := hco 1 k le_rfl (mul_one k).symm pk (one_smul _ _).symm rfl v ω₀ ω₁
    ⟨hv, fun _ _ _ => (pow_one _).symm⟩ ⟨h₀, fun _ _ _ => (pow_one _).symm⟩ ⟨h₁, fun _ _ _ => (pow_one _).symm⟩
  obtain ⟨c₁, hc₁, -, hfr⟩ := ((CoefBasic.coef_basic u.V u.D.toPre (PadicAlgCl p) k g').2.2 ω₁ h₁).2.2.1 w' hw'
  obtain ⟨θ, rfl, hθ⟩ := exists_theta_actVal u.U (PadicAlgCl p) hG hL.1.kerPow hk pk x hx w₀ hw₀ v hv
  obtain ⟨l, hl⟩ := exists_chart u.U.LG.isLB (u.toG a (IsLocalRing.closedPoint (PadicAlgCl p)))
  replace hl := (top_le_iff_mem _ _ _).2 hl
  obtain ⟨κ, hκ, hsum⟩ := hpar ω₀ h₀ l hl
  obtain ⟨c₂, hc₂, hval⟩ := exists_const_actVal u.U.toUnifPre (PadicAlgCl p) k w₀ θ a a' ha l l' hl hl'
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG u.U (PadicAlgCl p) hk w₀ hw₀
  refine ⟨c₁ * (κ * c₂), mul_ne_zero hc₁ (mul_ne_zero hκ hc₂), fun σ s hs => ?_⟩
  obtain ⟨t, ht⟩ := exists_carries u.U.toUnifPre (PadicAlgCl p) k w₀ hw₀ σ
  obtain ⟨t', ht'⟩ := exists_actVal u.A.isLB θ t
  have hE : u.U.toUnifPre.ExpandsF (PadicAlgCl p) k w₀ t' (e t') := (he _ _).2 rfl
  have hΦ := (hθ t t' s (e t') ⟨σ, ht, hs⟩ hE).2 ht'
  obtain ⟨σ', hσ', hs'⟩ := hE
  have H := hsum σ' _ hs'
  rw [hval t t' σ σ' ht hσ' ht', ← (Equiv.addRight pk.y).hasSum_iff] at H
  have H' := H.mul_left c₁
  rw [_root_.mul_assoc, _root_.mul_assoc]
  refine (congrArg (HasSum · _) (funext fun χ => ?_)).mp H'
  exact (congrArg (c₁ * ·) (hco s _ hΦ χ)).trans (hfr s χ).symm

end GlobalTheory.ZH.ParTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExpansionCoefMemAdicPowStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansionCoef_mem_adic_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (σ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (th : SecBT D (𝟙_ _) 1 0), U.ExpT (𝟙_ _) 1 σ f → FibNZ (𝟙_ _ ⊗ D.P.A).hom th → ∀ e : ℕ, ∃ s : Finset D.X, ∀ χ ∉ s, ∀ (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (b : R), Coef D χ u th (f χ) b → b ∈ I ^ (e + 1) := by
  first | exact @GlobalTheory.PsiRing.coef_mem_pow | exact GlobalTheory.PsiRing.coef_mem_pow | (intros; apply GlobalTheory.PsiRing.coef_mem_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ForallTermNeZeroOfPsiRelationStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forall_term_ne_zero_of_psiRelation : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (f : ∀ α, SecBT D (𝟙_ _) 1 α), PsiRel D (𝟙_ _) f → (∃ α j, (f α).f j ≠ 0) → ∀ α, ∃ j, (f α).f j ≠ 0 := by
  first | exact @GlobalTheory.forall_ne_zero_of_psiRel | exact GlobalTheory.forall_ne_zero_of_psiRel | (intros; apply GlobalTheory.forall_ne_zero_of_psiRel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfSection
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.NeutralPart

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in

theorem _root_.GlobalTheory.SS.NeutralPart.geometricallyConnected_of_section {X S : Scheme.{0}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [QuasiCompact f] (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
    (h : ∀ s : S, _root_.IsConnected (f ⁻¹' {s})) : GeometricallyConnected f := by
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro s
  haveI : ConnectedSpace (f ⁻¹' {s}) := isConnected_iff_connectedSpace.mp (h s)
  haveI : ConnectedSpace (f.fiber s) :=
    (f.fiberHomeo s).symm.surjective.connectedSpace (f.fiberHomeo s).symm.continuous
  haveI : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    instLocallyOfFiniteTypeSndScheme f (S.fromSpecResidueField s)
  exact _root_.GlobalTheory.RatPointConn.of_section (k := S.residueField s)
    (f.fiberToSpecResidueField s)
    (pullback.lift (S.fromSpecResidueField s ≫ e) (𝟙 _) (by simp [he]))
    (pullback.lift_snd _ _ _)

end GlobalTheory.SS.NeutralPart
end

