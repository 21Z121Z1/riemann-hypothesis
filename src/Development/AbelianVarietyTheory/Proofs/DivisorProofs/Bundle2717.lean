import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2610
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2548
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2611
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectFibrePowerAtSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowChart.Compare

open TopologicalSpace

section Comp

variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}

theorem gm_self_of_pgen (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w) {Y : Scheme.{0}} (f : Y ⟶ X')
    (y : Y) {j : L.ι} {i : L'.ι} (hj : F (f y) ∈ L.U j) (hi : f y ∈ L'.U i) :
    gm (f ≫ F) y (L.U j ⊓ L.U j) (L.g j j) = 1 := by
  have c := hw Y f y j j i i hj hj hi hi
  rw [gm_self hL' f y hi, inv_one, _root_.mul_one] at c
  exact mul_eq_right.1 c.symm

theorem indep_comp' (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w) (hw' : PGen w')
    (hL' : L'.IsLB) (hL'' : L''.IsLB) {Y : Scheme.{0}} (f : Y ⟶ X'') (y : Y) (j : L.ι) (i i' : L'.ι) (k : L''.ι)
    (hj : F (F' (f y)) ∈ L.U j) (hi : F' (f y) ∈ L'.U i) (hi' : F' (f y) ∈ L'.U i') (hk : f y ∈ L''.U k) :
    gw w (f ≫ F') y j i * gw w' f y i k = gw w (f ≫ F') y j i' * gw w' f y i' k := by
  have a := hw Y (f ≫ F') y j j i i' hj hj hi hi'
  have b := hw' Y f y i i' k k hi hi' hk hk
  rw [gm_self_of_pgen hL' w hw (f ≫ F') y hj hi] at a
  rw [gm_self hL'' f y hk] at b
  rw [a, b]
  generalize gm (f ≫ F') y _ (L'.g i i') = B
  generalize gw w (f ≫ F') y j i' = C
  generalize gw w' f y i' k = D
  rw [_root_.one_mul, inv_one, _root_.mul_one, _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]

theorem exists_comp' (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (hw : PGen w)
    (hw' : PGen w') (hL'' : L''.IsLB) :
    ∃ w'' : LB.Iso L'' (L.pull (F' ≫ F)), Tri w w' w'' := by
  have glue : ∀ (j : L.ι) (k : L''.ι), ∃ s : Γ(X'', (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k)ˣ,
      ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (i : L'.ι), F (F' (f y)) ∈ L.U j → F' (f y) ∈ L'.U i → f y ∈ L''.U k →
        gm f y _ s = gw w (f ≫ F') y j i * gw w' f y i k := by
    intro j k
    obtain ⟨W, hW⟩ : ∃ W : L'.ι → X''.Opens, ∀ i x, x ∈ W i ↔ F (F' x) ∈ L.U j ∧ F' x ∈ L'.U i ∧ x ∈ L''.U k :=
      ⟨fun i => F' ⁻¹ᵁ (F ⁻¹ᵁ L.U j) ⊓ (F' ⁻¹ᵁ L'.U i ⊓ L''.U k), fun _ _ => Iff.rfl⟩
    have l₀ : ∀ i, W i ≤ (L.pull (F' ≫ F)).U (fun _ => j) ⊓ L''.U k := fun i x hx =>
      ⟨mem_pull₂.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.2⟩
    have l₁ : ∀ i, W i ≤ F' ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U i) := fun i x hx =>
      ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull.2 ((hW i x).1 hx).1, ((hW i x).1 hx).2.1⟩
    have l₂ : ∀ i, W i ≤ (L'.pull F').U (fun _ => i) ⊓ L''.U k := fun i x hx =>
      ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.mem_pull.2 ((hW i x).1 hx).2.1, ((hW i x).1 hx).2.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(X'', W i)ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (i : L'.ι), f y ∈ W i →
        gm f y (W i) (u i) = gw w (f ≫ F') y j i * gw w' f y i k :=
      ⟨fun i => res (l₁ i) (pullU F' _ (w.s (fun _ => j, i))) * res (l₂ i) (w'.s (fun _ => i, k)), fun Y f y i hy =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res f y (l₁ i) hy _).trans (gm_pull f F' y _ (l₁ i hy) _)) (gm_res f y (l₂ i) hy _))⟩
    obtain ⟨s, hs⟩ := glue_unit _ W l₀ (fun x hx => by
        obtain ⟨i, hi⟩ := exists_chart hL' (F' x)
        exact Opens.mem_iSup.2 ⟨i, (hW i x).2 ⟨mem_pull₂.1 hx.1, hi, hx.2⟩⟩) u (fun i i' x hx => by
        have h₁ := (hW i x).1 hx.1
        have h₂ := (hW i' x).1 hx.2
        exact (hu _ (𝟙 X'') x i hx.1).trans ((indep_comp' w w' hw hw' hL' hL'' (𝟙 X'') x j i i' k h₁.1 h₁.2.1
          h₂.2.1 h₁.2.2).trans (hu _ (𝟙 X'') x i' hx.2).symm))
    refine ⟨s, fun Y f y i hj hi hk => ?_⟩
    have hy := (hW i (f y)).2 ⟨hj, hi, hk⟩
    exact (gm_res f y (l₀ i) hy s).symm.trans ((congrArg (gm f y (W i)) (hs i)).trans (hu Y f y i hy))
  choose s hs using glue
  exact ⟨⟨fun p => s (p.1 PUnit.unit) p.2⟩, fun Y f y j i k hj hi hk => hs j k Y f y i hj hi hk⟩

end Comp

end GlobalTheory.LowChart.Compare

namespace GlobalTheory.LowChart

theorem exists_siegAt_of_siegPB : ∀ {o : Type} [CommRing o] {ζ : o} {h n : ℕ} (F : SFam h n ζ) {S S₀ : Scheme.{0}} (g : S ⟶ S₀) (s' : S ⟶ Sp o) (x : S ⟶ F.X), x ≫ F.s = s' → ∀ (c : SiegPre h n ζ s'), SiegPB c F.univ x → ∀ (A₀ : Over S₀) [GrpObj A₀] [IsCommMonObj A₀] (Q : LB (G2 A₀).left) (β : c.A.left ⟶ A₀.left) (β₂ : (G2 c.A).left ⟶ (G2 A₀).left), IsGrpPullback c.A A₀ g β → IsSquare β β₂ → LBIso c.P (Q.pull β₂) → ∀ (r : ℕ) (d : Fin r → (𝟙_ (Over S) ⟶ c.A)), ∃ (v : S ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = s') (β₁ : (GlobalTheory.LowChart.siegAt F v s' hs).A.left ⟶ A₀.left) (β₁₂ : (G2 (GlobalTheory.LowChart.siegAt F v s' hs).A).left ⟶ (G2 A₀).left), IsGrpPullback (GlobalTheory.LowChart.siegAt F v s' hs).A A₀ g β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso (GlobalTheory.LowChart.siegAt F v s' hs).P (Q.pull β₁₂) ∧ ∀ a, (GlobalTheory.LowChart.cAt F v s' hs a).left ≫ β₁ = (∏ i, d i ^ a i).left ≫ β := by
  intro o _ ζ h n F S S₀ g s' x hx c hc A₀ _ _ Q β β₂ hβ hβ₂ hQ r d
  obtain ⟨φ, φ₂, hφ, hφ₂, hP, -⟩ := hc
  have hp : ∀ i, ((d i).left ≫ φ) ≫ F.univ.A.hom = x := fun i => by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w (d i)]
    exact Category.id_comp _
  obtain ⟨v, hv, hvc⟩ : ∃ v : S ⟶ (powA F r).left, v ≫ (powA F r).hom = x ∧
      ∀ i, v ≫ (coord F i).left = (d i).left ≫ φ :=
    ⟨lift x (fun i => (d i).left ≫ φ) hp, lift_hom _ _ _, fun i => lift_coord _ _ _ i⟩
  have hs : v ≫ toO F r = s' := by
    rw [toO, ← Category.assoc, hv, hx]
  refine ⟨v, hs, ?_⟩
  have hpb : IsGrpPullback (siegAt F v s' hs).A F.univ.A x (Pdiv.PullbackComparison.pφ (v ≫ (powA F r).hom) F.univ.A) :=
    (Pdiv.PullbackComparison.isGrpPullback _ _).congr hv rfl
  obtain ⟨e, he, heφ⟩ := grpPullback_iso hpb hφ
  haveI := he
  let C := siegAt F v s' hs
  let θ₂ : (G2 C.A).left ⟶ (G2 c.A).left := (CartesianMonoidalCategory.lift (fst C.A C.A ≫ e.hom) (snd C.A C.A ≫ e.hom)).left
  have hθf : θ₂ ≫ (fst c.A c.A).left = (fst C.A C.A).left ≫ e.hom.left := by
    rw [← Over.comp_left, CartesianMonoidalCategory.lift_fst, Over.comp_left]
  have hθs : θ₂ ≫ (snd c.A c.A).left = (snd C.A C.A).left ≫ e.hom.left := by
    rw [← Over.comp_left, CartesianMonoidalCategory.lift_snd, Over.comp_left]
  refine ⟨e.hom.left ≫ β, θ₂ ≫ β₂, ((isGrpPullback_of_iso e).comp hβ).congr (Category.id_comp g) rfl,
    ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, hβ₂.1, ← Category.assoc, hθf, Category.assoc]
  · rw [Category.assoc, hβ₂.2, ← Category.assoc, hθs, Category.assoc]
  · have hθ₂ : Pdiv.PullbackComparison.pφ₂ (v ≫ (powA F r).hom) F.univ.A = θ₂ ≫ φ₂ :=
      have e1 : (θ₂ ≫ φ₂) ≫ (fst F.univ.A F.univ.A).left =
          (fst C.A C.A).left ≫ Pdiv.PullbackComparison.pφ (v ≫ (powA F r).hom) F.univ.A := by
        rw [Category.assoc, hφ₂.1, ← Category.assoc, hθf, Category.assoc, heφ]
      have e2 : (θ₂ ≫ φ₂) ≫ (snd F.univ.A F.univ.A).left =
          (snd C.A C.A).left ≫ Pdiv.PullbackComparison.pφ (v ≫ (powA F r).hom) F.univ.A := by
        rw [Category.assoc, hφ₂.2, ← Category.assoc, hθs, Category.assoc, heφ]
      Pdiv.PullbackComparison.adelic_GL2_ext_of_local_components (G := F.univ.A) _ _
        ((Pdiv.PullbackComparison.pφ₂_fst _ _).trans e1.symm) ((Pdiv.PullbackComparison.pφ₂_snd _ _).trans e2.symm)
    have w1 : LBIso C.P (c.P.pull θ₂) :=
      LBIso.chartPull (chartPullSame F.univ.P (fun _ : PUnit.{1} => Pdiv.PullbackComparison.pφ₂ (v ≫ (powA F r).hom) F.univ.A)
        (fun _ => φ₂) (fun _ => 1) θ₂ (fun _ => hθ₂)) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P θ₂ θ₂ rfl) (LBIso.symm hP)
    obtain ⟨w, hw⟩ := hQ
    obtain ⟨w', hw'⟩ := w1
    have pw := (isGen_iff w).1 hw
    have pw' := (isGen_iff w').1 hw'
    obtain ⟨w'', T⟩ := Compare.exists_comp' c.isLB w w' pw pw' C.isLB
    exact ⟨w'', (isGen_iff w'').2 (T.pgen_comp c.isLB pw pw')⟩
  · have hpt : ∀ i, ptAt F v s' hs i ≫ e.hom = d i := fun i =>
      Over.OverMorphism.ext (hφ.1.hom_ext
        (by rw [Over.comp_left, Category.assoc, heφ, ptAt_left, hvc])
        (by rw [Over.comp_left, Category.assoc, Over.w e.hom, Over.w (ptAt F v s' hs i), Over.w (d i)]))
    let ψ : (𝟙_ (Over S) ⟶ C.A) →* (𝟙_ (Over S) ⟶ c.A) :=
      MonoidHom.mk' (· ≫ e.hom) fun a b => MonObj.mul_comp a b e.hom
    intro a
    have key : cAt F v s' hs a ≫ e.hom = ∏ i, d i ^ a i := by
      show ψ (cAt F v s' hs a) = _
      rw [cAt, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_zpow]
      exact congrArg (· ^ a i) (hpt i)
    rw [← Category.assoc, ← Over.comp_left, key]

end GlobalTheory.LowChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothProjectiveModel
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.BirModel

theorem exists_smooth_projective_model : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k]
    (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (s : Y ⟶ X) (_ : IsDominant s), SmoothOfRelativeDimension n (s ≫ p) ∧
      IsProjOver (s ≫ p) ∧ Function.Bijective (functionFieldMap s) := by
  intro hP k _ _ X _ p n hp hdim
  obtain ⟨Y, s, U, hY, hsm, hpr, hU, hiso⟩ := GlobalTheory.WeakRes.weak_resolution hP k X p n hp hdim
  have hdom : IsDominant s := GlobalTheory.T.isDominant_of_isIso_restrict' X Y s U hU hiso
  exact ⟨Y, hY, s, hdom, hsm, hpr, GlobalTheory.T.functionFieldMap_bijective_of_isIso_restrict' X Y s U hU hiso⟩

end GlobalTheory.BirModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSolveMvPowerSeriesMatrixIdentityConst
section
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory

open Matrix

theorem powerSeries_matrix_solve : ∀ (n : ℕ) (R : Type) [CommRing R] (J : Fin n → Fin n → MvPowerSeries (Fin n) R), (∀ i j, MvPowerSeries.constantCoeff (J i j) = if i = j then 1 else 0) → ∀ b : Fin n → MvPowerSeries (Fin n) R, ∃ G : Fin n → MvPowerSeries (Fin n) R, ∀ i, ∑ j, G j * J i j = b i := by
  intro n R _ J hJ b
  let M : Matrix (Fin n) (Fin n) (MvPowerSeries (Fin n) R) := Matrix.of J
  have hM : (MvPowerSeries.constantCoeff (σ := Fin n) (R := R)).mapMatrix M = 1 := by
    ext i j
    simp [M, Matrix.one_apply, hJ]
  have hdet : IsUnit M.det := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, hM, Matrix.det_one]
    exact isUnit_one
  refine ⟨M⁻¹ *ᵥ b, fun i => ?_⟩
  have h := congrFun (Matrix.mulVec_mulVec b M M⁻¹) i
  rw [Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at h
  rw [← h]
  simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecializationClosedInAffineNeighbourhoodStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_specialization_closed_in_affine_neighbourhood : ∀ (Y : Scheme.{0}) (x : Y), ∃ V : Y.Opens, IsAffineOpen V ∧ ∃ y ∈ V, x ⤳ y ∧ ∀ V₂ : Y.Opens, V₂ ≤ V → IsAffineOpen V₂ → y ∈ V₂ → (∀ y₁ ∈ V₂, y ⤳ y₁ → y₁ = y) ∧ ∃ M : Ideal Γ(Y, V₂), M.IsMaximal ∧ ∀ a : Γ(Y, V₂), a ∈ M ↔ y ∉ Y.basicOpen a := by
  first | exact @GlobalTheory.ClosedPt.exists_closed_point | exact GlobalTheory.ClosedPt.exists_closed_point | (intros; apply GlobalTheory.ClosedPt.exists_closed_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadPolarisedAbelianVarietyFinitelyManyPStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spread_polarisedAbelianVariety_finitely_many_points : ∀ (F Ω : Type) [Field F] [Field Ω] (em : F →+* Ω) (A : PolAV (Sp Ω)) (I : Type) [Finite I] (y : I → (baseOver (Sp Ω) ⟶ A.A)), ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : Algebra F T) (jT : T →+* Ω) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left) (y₀ : I → (baseOver (Sp T) ⟶ P.A)), Algebra.FiniteType F T ∧ Function.Injective jT ∧ jT.comp (algebraMap F T) = em ∧ IsGrpPullback A.A P.A (spMap jT) φ ∧ LBIso A.L (P.L.pull φ) ∧ ∀ i, (y i).left ≫ φ = spMap jT ≫ (y₀ i).left := by
  first | exact @GlobalTheory.SpreadPolAV.exists_spread | exact GlobalTheory.SpreadPolAV.exists_spread | (intros; apply GlobalTheory.SpreadPolAV.exists_spread <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquare
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.Descent

variable {R : Type} [CommRing R]

theorem descend {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (ψ : D →ₐ[R] D')
    (hψ : (ψ : D →+* D').FaithfullyFlat) (s : D')
    (hs : ∀ (E : Type) [CommRing E] [Algebra R E] (α β : D' →ₐ[R] E), α.comp ψ = β.comp ψ → α s = β s) :
    ∃ k, ψ k = s := by
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  haveI : IsScalarTower R D D' := IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm
  refine (Algebra.IsEffective.of_faithfullyFlat D D' s).1 ?_
  have h := hs (D' ⊗[D] D') ((Algebra.TensorProduct.includeLeft : D' →ₐ[D] D' ⊗[D] D').restrictScalars R)
    ((Algebra.TensorProduct.includeRight : D' →ₐ[D] D' ⊗[D] D').restrictScalars R) (by
      ext d
      exact ((Algebra.TensorProduct.includeLeft : D' →ₐ[D] D' ⊗[D] D').commutes d).trans
        ((Algebra.TensorProduct.includeRight : D' →ₐ[D] D' ⊗[D] D').commutes d).symm)
  simpa [sub_eq_zero] using h

theorem exists_square {D D' D₂ : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing D₂]
    [Algebra R D₂] (ψ : D →ₐ[R] D') (hψ : (ψ : D →+* D').FaithfullyFlat) (ψ₂ : D →ₐ[R] D₂) :
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra R E) (α : D' →ₐ[R] E) (β : D₂ →ₐ[R] E),
      α.comp ψ = β.comp ψ₂ ∧ Function.Injective β := by
  letI : Algebra D D' := (ψ : D →+* D').toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  haveI : IsScalarTower R D D' := IsScalarTower.of_algebraMap_eq fun r ↦ (ψ.commutes r).symm
  letI : Algebra D D₂ := (ψ₂ : D →+* D₂).toAlgebra
  haveI : IsScalarTower R D D₂ := IsScalarTower.of_algebraMap_eq fun r ↦ (ψ₂.commutes r).symm
  refine ⟨D₂ ⊗[D] D', inferInstance, inferInstance,
    (Algebra.TensorProduct.includeRight : D' →ₐ[D] D₂ ⊗[D] D').restrictScalars R,
    (Algebra.TensorProduct.includeLeft : D₂ →ₐ[D] D₂ ⊗[D] D').restrictScalars R, ?_, ?_⟩
  · ext d
    exact ((Algebra.TensorProduct.includeRight : D' →ₐ[D] D₂ ⊗[D] D').commutes d).trans
        ((Algebra.TensorProduct.includeLeft : D₂ →ₐ[D] D₂ ⊗[D] D').commutes d).symm
  · exact FaithfulSMul.algebraMap_injective D₂ (D₂ ⊗[D] D')

variable {A : Over (Sp R)} [GrpObj A]

def sig (p : ℕ) (f : Fn1 A) (g : Fn2 A) {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (ψ : D →ₐ[R] D') (x : Pt A D) (z : Pt A D') : D' :=
  chi p g D' z + f R D' (Algebra.ofId R D') 1 - f D D' ψ x

theorem sig_nat {p : ℕ} (hp : (p : R) = 0) {f : Fn1 A} {g : Fn2 A} (hf : IsCoc (whole A) f) (hfg : IsAdd f g)
    {D D' D'' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing D''] [Algebra R D'']
    (ψ : D →ₐ[R] D') (θ : D' →ₐ[R] D'') (x : Pt A D) (z : Pt A D') (hz : z ^ p = spOver ψ ≫ x) :
    θ (sig p f g ψ x z) = sig p f g (θ.comp ψ) x (spOver θ ≫ z) := by
  have h1 := GlobalTheory.T.sumTwoPointFunction_multiples_natural_charP p R hp A f g hfg D' D'' θ z
  have h2 := hf D D' D'' ψ θ x (sm_whole _)
  have h3 := hf R D' D'' (Algebra.ofId R D') θ 1 (sm_whole _)
  have e : θ.comp (Algebra.ofId R D') = Algebra.ofId R D'' := Subsingleton.elim _ _
  rw [e, MonObj.comp_one] at h3
  rw [hz] at h1
  simp only [sig, map_add, map_sub]
  linear_combination -h1 + h2 - h3

theorem chi_indep [IsCommMonObj A] {p : ℕ} (hp : (p : R) = 0) {g : Fn2 A} (hg : IsSymCoc g)
    (h0 : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), x ^ p = 1 → chi p g D x = 0)
    {D : Type} [CommRing D] [Algebra R D] (z z' : Pt A D) (h : z ^ p = z' ^ p) : chi p g D z = chi p g D z' := by
  obtain ⟨t, rfl⟩ : ∃ t, z = z' * t := ⟨z'⁻¹ * z, by simp⟩
  have ht : t ^ p = 1 := by rwa [mul_pow, mul_eq_left] at h
  have h1 := GlobalTheory.T.symmetric_two_cocycle_sum_pow_mul (Pt A D) D (g D) (hg D).1 (hg D).2 p z' t
  have h2 := (hg D).2 (z' ^ p) 1 1
  have h3 := h0 D t ht
  have h4 : (p : D) = 0 := by rw [← map_natCast (algebraMap R D), hp, map_zero]
  rw [ht, nsmul_eq_mul, h4] at h1
  simp only [_root_.mul_one] at h2
  simp only [chi] at h3 ⊢
  linear_combination h1 - h2 + h3

theorem pow_comp {p : ℕ} {D D' D'' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing D'']
    [Algebra R D''] (ψ : D →ₐ[R] D') (θ : D' →ₐ[R] D'') (x : Pt A D) (z : Pt A D') (hz : z ^ p = spOver ψ ≫ x) :
    (spOver θ ≫ z) ^ p = spOver (θ.comp ψ) ≫ x := by
  rw [← MonObj.comp_pow, hz, ← Category.assoc, spOver_comp]

theorem exists_isCob (p : ℕ) (R : Type) [CommRing R] (hp : (p : R) = 0) (A : Over (Sp R)) [GrpObj A]
    [IsCommMonObj A] (f : Fn1 A) (g : Fn2 A) (hf : IsCoc (whole A) f) (hfg : IsAdd f g) (hg : IsSymCoc g)
    (h0 : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), x ^ p = 1 → chi p g D x = 0)
    (hr : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), ∃ (D' : Type) (_ : CommRing D') (_ : Algebra R D')
      (ψ : D →ₐ[R] D') (z : Pt A D'), (ψ : D →+* D').FaithfullyFlat ∧ z ^ p = spOver ψ ≫ x) :
    ∃ k : Fn0 A, IsCob (whole A) f k := by
  have key : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), ∃ k : D,
      ∀ (D₂ : Type) [CommRing D₂] [Algebra R D₂] (ψ₂ : D →ₐ[R] D₂) (z₂ : Pt A D₂), z₂ ^ p = spOver ψ₂ ≫ x →
        ψ₂ k = sig p f g ψ₂ x z₂ := by
    intro D _ _ x
    obtain ⟨D', _, _, ψ, z, hψ, hz⟩ := hr D x
    have cmp : ∀ (D₂ : Type) [CommRing D₂] [Algebra R D₂] (ψ₂ : D →ₐ[R] D₂) (z₂ : Pt A D₂),
        z₂ ^ p = spOver ψ₂ ≫ x → ∀ (E : Type) [CommRing E] [Algebra R E] (α : D' →ₐ[R] E) (β : D₂ →ₐ[R] E),
        α.comp ψ = β.comp ψ₂ → α (sig p f g ψ x z) = β (sig p f g ψ₂ x z₂) := by
      intro D₂ _ _ ψ₂ z₂ hz₂ E _ _ α β e
      rw [sig_nat hp hf hfg ψ α x z hz, sig_nat hp hf hfg ψ₂ β x z₂ hz₂, sig, sig, e,
        chi_indep hp hg h0 (spOver α ≫ z) (spOver β ≫ z₂)
          (by rw [pow_comp ψ α x z hz, pow_comp ψ₂ β x z₂ hz₂, e])]
    obtain ⟨k, hk⟩ := descend ψ hψ (sig p f g ψ x z) (fun E _ _ α β e ↦ cmp D' ψ z hz E α β e)
    refine ⟨k, fun D₂ _ _ ψ₂ z₂ hz₂ ↦ ?_⟩
    obtain ⟨E, _, _, α, β, e, hβ⟩ := exists_square ψ hψ ψ₂
    apply hβ
    rw [← cmp D₂ ψ₂ z₂ hz₂ E α β e, ← hk]
    exact (DFunLike.congr_fun e k).symm
  choose k hk using key
  refine ⟨k, fun D _ _ D₁ _ _ φ x _ ↦ ?_⟩
  obtain ⟨D', _, _, ψ, z, hψ, hz⟩ := hr D₁ (spOver φ ≫ x)
  have hi : Function.Injective ψ := hψ.injective
  apply hi
  have h1 := hk D₁ (spOver φ ≫ x) D' ψ z hz
  have h2 := hk D x D' (ψ.comp φ) z (by rw [hz, ← Category.assoc, spOver_comp])
  have h3 := hf D D₁ D' φ ψ x (sm_whole _)
  simp only [sig, AlgHom.comp_apply] at h1 h2
  rw [map_sub]
  linear_combination h2 - h1 - h3

end GlobalTheory.PtExt.Descent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentOfDefectKilledStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareBundle_descent_of_defect_killed : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (M : LB X), M.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ) (D : Γ(Triple f, ⊤)ˣ) (u : Γ(pullback f f, ⊤)ˣ), DescCompat f M φ → Defect f M φ D → KillsSq f D u → ∃ (M₂ : LB X) (ψ : ∀ i j, Γ(pullback f f, chart f M₂ i j)ˣ), M₂.IsLB ∧ LBIso (lbPow M 2) M₂ ∧ DescCompat f M₂ ψ ∧ DescCocycle f M₂ ψ := by
  first | exact @GlobalTheory.SqDatum.exists_sq_descent | exact GlobalTheory.SqDatum.exists_sq_descent | (intros; apply GlobalTheory.SqDatum.exists_sq_descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkLiftFiniteCoverNormalLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stalk_lift_finite_cover_normal_local : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsIntegrallyClosed V₁ → ∀ (X Z : Scheme.{0}) (π : X ⟶ Z), IsFinite π → ∀ (f : Sp V₁ ⟶ Z) (yM : Sp (FractionRing V₁) ⟶ X), yM ≫ π = jK V₁ ≫ f → ∃ (z₁ : X) (ev : X.presheaf.stalk z₁ →+* V₁), IsLocalHom ev ∧ spMap ev ≫ X.fromSpecStalk z₁ ≫ π = f ∧ jK V₁ ≫ spMap ev ≫ X.fromSpecStalk z₁ = yM := by
  first | exact @GlobalTheory.FiniteLift.exists_stalk_lift | exact GlobalTheory.FiniteLift.exists_stalk_lift | (intros; apply GlobalTheory.FiniteLift.exists_stalk_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardSmoothRetractOfSmoothStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardSmooth_retract_of_smooth : ∀ (R₀ B₀ : Type) [CommRing R₀] [CommRing B₀] [Algebra R₀ B₀], Algebra.Smooth R₀ B₀ → ∃ (C₀ : Type) (_ : CommRing C₀) (_ : Algebra R₀ C₀) (i : B₀ →ₐ[R₀] C₀) (r : C₀ →ₐ[R₀] B₀), Algebra.IsStandardSmooth R₀ C₀ ∧ ∀ x, r (i x) = x := by
  first | exact @GlobalTheory.SmoothRetract.exists_retract_isStandardSmooth | exact GlobalTheory.SmoothRetract.exists_retract_isStandardSmooth | (intros; apply GlobalTheory.SmoothRetract.exists_retract_isStandardSmooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricDataComparePolarisedUpToFunctionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_data_compare_polarised_up_to_function : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [IsNoetherianRing R'] (Q : Data R) (ρ : R →+* R') (P : PolAV (Sp R')) (β : P.A.left ⟶ Q.B.left) (β₂ : (G2 P.A).left ⟶ (G2 Q.B).left), Function.Injective ρ → IsGrpPullback P.A Q.B (spMap ρ) β → IsSquare β β₂ → (letI := P.isAb.comm; LBIso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂)) → ∃ (D : DegPre R') (e : D.X ≃+ Q.X) (f : D.X → D.X → (FractionRing R')ˣ), Half Q ρ D e f := by
  first | exact @GlobalTheory.HalfEx.half_exists | exact GlobalTheory.HalfEx.half_exists | (intros; apply GlobalTheory.HalfEx.half_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelGeometricPointHarrisTaylorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplectic_level_geometric_point_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N M e : ℕ),
  3 ≤ M → Odd M → M.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S),
    ∃ (t₁ : Sp K ⟶ Sp (cycAway M))
      (lv : (Fin (Module.finrank ℤ D.La / 2) ⊕ Fin (Module.finrank ℤ D.La / 2) → ℤ) → (Over.mk x ⟶ o.A)),
      SympCond o (Module.finrank ℤ D.La / 2) M (Over.mk x) t₁ lv := by
  first | (exact @GlobalTheory.HTSympCover.exists_sympCond_geom) | (exact GlobalTheory.HTSympCover.exists_sympCond_geom) | (intros; apply GlobalTheory.HTSympCover.exists_sympCond_geom  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorOfOriginDerivationStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangentVector_of_originDerivation : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (D : G.left.presheaf.stalk (origin G) → R), (∀ x y, D (x + y) = D x + D y) → (∀ x y, D (x * y) = evO G x * D y + evO G y * D x) → (∀ r, D (constO G r) = 0) → ∃ v : TanM (𝟙 (Sp R)) G, ∀ f, tanDer G v f = D f := by
  first | exact @GlobalTheory.CoordsOrigin.exists_tan_of_derivation | exact GlobalTheory.CoordsOrigin.exists_tan_of_derivation | (intros; apply GlobalTheory.CoordsOrigin.exists_tan_of_derivation <;> assumption)
end

