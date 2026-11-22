import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictionPoincareBundle
import Formalism.LocalToGlobal.ProjectiveLattices.TensPtsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedSubstepClosure
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0597
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbPartActIsAdj
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)
open GlobalTheory.Vert GlobalTheory.LocM
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.LocM

open ReciprocityTheory.ChartRestriction.G.Out (RosatiAdj rosatiφ rosatiε)
open GlobalTheory.CechPic

theorem abPartAct_isAdj (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (t : SAB H (Sp R)) (U : PELUnif I t) :
    GlobalTheory.HermTensor.IsAdj (abPartAct U) U.D.toPre.P.L := by
  intro c
  have hr : RosatiAdj U.D.toPre.P.A U.D.toPre.P.L ((abPartAct U).act c) ((abPartAct U).act (star c)) := by
    have h : RosatiAdj U.D.toPre.P.A U.D.toPre.P.L ((abPartAct U).act c) ((abPartAct U).act (H.bar c)) := by
      letI := H.starRing
      exact U.oD.onB.rosati c
    rw [← bar_eq_star H]
    exact h
  obtain ⟨V, hV, g, hg⟩ := hr (IsLocalRing.closedPoint R)
  obtain rfl : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hV
  have hL : U.D.toPre.P.L.IsLB := U.D.toPre.P.isLB
  have hgen : ∃ u : LB.Gen (LB.LinComb U.D.toPre.P.L
      (rosatiφ U.D.toPre.P.A ((abPartAct U).act c) ((abPartAct U).act (star c))) rosatiε), u.IsGen := by
    have e : rosatiφ U.D.toPre.P.A ((abPartAct U).act c) ((abPartAct U).act (star c)) = fun i =>
        (U.D.toPre.P.A ⊗ U.D.toPre.P.A).left.topIso.inv ≫ ((U.D.toPre.P.A ⊗ U.D.toPre.P.A).hom ⁻¹ᵁ ⊤).ι ≫
          rosatiφ U.D.toPre.P.A ((abPartAct U).act c) ((abPartAct U).act (star c)) i :=
      funext fun i => ((U.D.toPre.P.A ⊗ U.D.toPre.P.A).left.topIso.inv_hom_id_assoc _).symm
    rw [e]
    exact ⟨_, ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hg _⟩
  obtain ⟨u, hu⟩ := hgen
  have h0 := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨u, hu⟩
  rw [cls_linComb hL, Fin.sum_univ_six] at h0
  refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1 ?_
  refine (cls_cube_two hL _ _ _).trans (Eq.trans ?_ (cls_cube_two hL _ _ _).symm)
  have pm : ∀ a b : U.D.toPre.P.A ⊗ U.D.toPre.P.A ⟶ U.D.toPre.P.A, padd U.D.toPre.P.A a b = a * b := fun _ _ => rfl
  simp only [rosatiφ, rosatiε, lam, pm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons,
    one_smul, neg_smul, Fin.isValue] at h0 ⊢
  rw [← sub_eq_zero, ← h0]
  abel

end GlobalTheory.LocM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedClosureLocalSystemStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_closure_local_system : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty) (σ : E →+* ℂ) (k r : ℕ) (D : Adapted A σ k) (hk : k < Dw.mult σ) (Sb : D.C.Sub A.ch r) (Cl : Sb.Closure (π ≫ (Y i).s)) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas (Y i) (Cl.f ≫ π) ty') (Z : Mdl Y i₀) (g : Z.X ⟶ X), StepRel D hk Cl.L A' → HasDR Z → MapsTo Z A g → LocMaps Z A' := by
  first | exact @GlobalTheory.DRFlag.locMaps_closure_of_hasDR | exact GlobalTheory.DRFlag.locMaps_closure_of_hasDR | (intros; apply GlobalTheory.DRFlag.locMaps_closure_of_hasDR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedLinearPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_linear_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ) (D : Adapted A σ k) (hk : k < Dw.mult σ) (X' : Scheme.{0}) (f : X' ⟶ X) (L : D.C.Line f) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas M (f ≫ π) ty'), StepRel D hk L A' → IntStep A' σ (k + 1) := by
  first | exact @GlobalTheory.DRFlag.StepInt.intStep_succ | exact GlobalTheory.DRFlag.StepInt.intStep_succ | (intros; apply GlobalTheory.DRFlag.StepInt.intStep_succ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedNextStepTypeStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_next_step_type : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k r : ℕ) (D : Adapted A σ k) (hj : k + r + 1 ≤ Dw.mult σ), (k + r + 1 ∈ ty σ ∨ k + r + 1 = Dw.mult σ) → ∀ α : A.ch.ι → D.C.A, (∀ a, ⊤ ≤ A.ch.χ a ⁻¹ᵁ D.C.B (α a)) → ∃ Sb : D.C.Sub A.ch r, IsFrSub D Sb hj := by
  first | exact @GlobalTheory.DRFlag.FrSub.exists_isFrSub | exact GlobalTheory.DRFlag.FrSub.exists_isFrSub | (intros; apply GlobalTheory.DRFlag.FrSub.exists_isFrSub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedSubstepClosureStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_substep_closure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k r : ℕ) (D : Adapted A σ k) (hj : k + r + 1 ≤ Dw.mult σ) (hk : k < Dw.mult σ) (Sb : D.C.Sub A.ch r) (Cl : Sb.Closure (π ≫ M.s)) (ty' : (E →+* ℂ) → Finset ℕ), IsFrSub D Sb hj → (k + r + 1 ∈ ty σ ∨ k + r + 1 = Dw.mult σ) → (∀ e ∈ ty σ, e ≤ k ∨ k + r + 1 ≤ e) → ty' σ = insert (k + 1) (ty σ) → (∀ σ', σ' ≠ σ → ty' σ' = ty σ') → ∃ A' : Atlas M (Cl.f ≫ π) ty', StepRel D hk Cl.L A' := by
  first | exact @GlobalTheory.DRFlag.StepAtlas.exists_stepAtlas | exact GlobalTheory.DRFlag.StepAtlas.exists_stepAtlas | (intros; apply GlobalTheory.DRFlag.StepAtlas.exists_stepAtlas <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmEqChernRootsMulRootDiscr
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.AntisymmChern

theorem antisymm_eq_chernRoots_mul_rootDiscr : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ), ∃ R : MvPolynomial (ι × ℕ) ℝ, antisymm Q = chernRoots m R * rootDiscr m := by
  intro ι _ m Q
  classical
  obtain ⟨S, hS⟩ : rootDiscr m ∣ antisymm Q := GlobalTheory.T.flagRelativeTangentTopChern_dvd_of_differences_dvd ι m (antisymm Q) fun τ i j hij =>
    GlobalTheory.T.X_sub_X_dvd_of_rename_swap_eq_neg (⟨τ, i⟩ : Root m) ⟨τ, j⟩ (by simp [hij.ne]) _ (GlobalTheory.T.weylAntisymmetrization_rename_swap_neg ι m Q τ i j hij.ne)
  have hsym : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S := by
    intro w
    have h1 := GlobalTheory.T.weylAntisymmetrization_rename_block_perm_sign ι m Q w
    rw [hS, map_mul, GlobalTheory.T.flagRelativeTangentTopChern_rename_block_perm ι m w, smul_mul_assoc] at h1
    have hs : ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) ≠ 0 := Units.ne_zero _
    exact mul_left_cancel₀ (GlobalTheory.T.flagRelativeTangentTopChern_ne_zero ι m) (smul_right_injective _ hs h1)
  obtain ⟨R, hR⟩ := GlobalTheory.T.symmetric_poly_chern_roots ι m S hsym
  exact ⟨R, by rw [hS, hR, mul_comm]⟩

end GlobalTheory.AntisymmChern
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AppLEEqIffStalk
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyAtBC

theorem appLE_eq_iff_stalk {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    {V : X.Opens} (hV : ∀ y, F y ∈ V) (s : ∀ j, Γ(X, V ⊓ L.U j)) (s' : L'.Sec) :
    (∀ (j : (L.pull F).ι) (i : L'.ι) (hle : (L.pull F).U j ⊓ L'.U i ≤ F ⁻¹ᵁ (V ⊓ L.U (j PUnit.unit))),
      (F.appLE _ _ hle).hom (s (j PUnit.unit)) =
        (show Γ(X', (L.pull F).U j ⊓ L'.U i) from (w.s (j, i)).val) * resG _ inf_le_right (s'.f i)) ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (s j) = (gw w r z j k).val * gs r z _ (s'.f k) := by
  constructor
  · intro h Z r z j k hj hk
    have hy : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have hle : (L.pull F).U (fun _ => j) ⊓ L'.U k ≤ F ⁻¹ᵁ (V ⊓ L.U j) := fun y hy => ⟨hV y, mem_pull.1 hy.1⟩
    refine (gs_appLE F _ _ hle r z hy _).symm.trans ((congrArg (gs r z _) (h (fun _ => j) k hle)).trans ?_)
    rw [gs_mul _ z _ hy, gs_res _ z _ hy]
    exact congrArg (· * _) (gs_unit _ z _ hy _)
  · intro h j i hle
    refine fn_ext fun y hy => ?_
    refine (gs_appLE F _ _ hle (𝟙 _) y hy _).trans ((h _ (𝟙 _) y _ i (mem_pull.1 hy.1) hy.2).trans ?_)
    rw [gs_mul _ y _ hy, gs_res _ y _ hy]
    exact congrArg (· * _) (gs_unit _ y _ hy _).symm

theorem mem_of_comm {X X' T T' : Scheme.{0}} {F : X' ⟶ X} {π : X ⟶ T} {π' : X' ⟶ T'} {z : T' ⟶ T}
    (e : F ≫ π = π' ≫ z) {U : T.Opens} (hz : ⊤ ≤ z ⁻¹ᵁ U) (y : X') : F y ∈ π ⁻¹ᵁ U := by
  show π (F y) ∈ U
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  exact hz (Set.mem_univ _)

theorem spMap_comp₀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap (f'.comp f) = spMap f' ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {M : GChart Y} {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {z : Sp R ⟶ Y.X} {hz : ⊤ ≤ z ⁻¹ᵁ M.U}
  {x : KeyIn R} {x' : KeyIn R'}

theorem keyAt_of_keyPB (h : KeyAt M z hz x) (h' : KeyPB x' x f) :
    KeyAt M (spMap f ≫ z) (le_preimage_comp _ hz) x' := by
  obtain ⟨φ, he, w, hg, hp, hw, hr, hs, hv⟩ := h
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := h'
  have g := (isGen_iff w).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp x.P.isLB w w' g g' Y.t.PP.isLB x'.P.isLB
  have he'' : eSec x'.P.A ≫ φ' ≫ φ = (spMap f ≫ z) ≫ eSec Y.t.G := by
    rw [← Category.assoc, he', Category.assoc, he, Category.assoc]
  have hF : F' = dualMap f := KeyCancel.dualNumber_ringHom_ext
    (fun a => by
      rw [hF']
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [hε']
      ext <;> simp [dualMap])
  have hq := hp'.comp hp
  refine ⟨φ' ≫ φ, he'', w'', hg'.trans hg, hq, (isGen_iff w'').2 (T.pgen_comp x.P.isLB g g'), ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec Y.t.G) _ x.rig Y.t.PP.rig z _
      (rigPull_le φ z he Y.t.PP.L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _
      (rigPull_le φ' (spMap f) he' x.P.L) (fun _ => rfl)).1 hr'
    exact (maps_iff w'' _ (fun _ => eSec Y.t.G) _ x'.rig Y.t.PP.rig (spMap f ≫ z) _
      (rigPull_le (φ' ≫ φ) (spMap f ≫ z) he'' Y.t.PP.L) (fun _ => rfl)).2
      (T.pmaps_comp x.P.isLB (fun _ => he') r₀ r₁)
  · refine (appLE_eq_iff_stalk w'' (mem_of_comm hq.1.w (le_preimage_comp _ hz)) M.θ x'.th).2
      fun Z q y j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart x.P.isLB (φ' (q y))
    have a := (appLE_eq_iff_stalk w (mem_of_comm hp.1.w hz) M.θ x.th).1 hs Z (q ≫ φ') y j i hj hi
    have b := (KeyCancel.appLE_eq_iff_stalk w' x.th x'.th).1 hs' Z q y i k hi hk
    rw [T Z q y j i k hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [← Category.assoc, hv', Category.assoc, hv, FlagMod.ev_spMap f z M.U hz, FlagMod.dualMap_comp, spMap_comp₀,
      hF, Category.assoc]
    rfl

theorem keyPB_of_keyAt (h : KeyAt M z hz x) (h' : KeyAt M (spMap f ≫ z) (le_preimage_comp _ hz) x') :
    KeyPB x' x f := by
  obtain ⟨φ, he, w, hg, hc, hw, hr, hs, hv⟩ := h
  obtain ⟨φ'', he'', w'', hg'', hc'', hw'', hr'', hs'', hv''⟩ := h'
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x'.P.A.left ⟶ x.P.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ x.P.A.hom = x'.P.A.hom ≫ spMap f :=
    ⟨hp.lift φ'' (x'.P.A.hom ≫ spMap f) (by rw [hc''.1.w, Category.assoc]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x'.P.A ≫ φ' = spMap f ≫ eSec x.P.A := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', Category.assoc, Category.assoc, he]
    · have a₁ : eSec x'.P.A ≫ x'.P.A.hom = 𝟙 _ := Over.w η[x'.P.A]
      have a₂ : eSec x.P.A ≫ x.P.A.hom = 𝟙 _ := Over.w η[x.P.A]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel Y.t.PP.isLB w w'' g g'' x.P.isLB x'.P.isLB
  have r := (maps_iff w _ (fun _ => eSec Y.t.G) _ x.rig Y.t.PP.rig z _ (rigPull_le φ z he Y.t.PP.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec Y.t.G) _ x'.rig Y.t.PP.rig (spMap f ≫ z) _
    (rigPull_le (φ' ≫ φ) (spMap f ≫ z) he'' Y.t.PP.L) (fun _ => rfl)).1 hr''
  refine ⟨φ', he', w', hg''.trans hg.symm, dualMap f, hc.cancel hc'' hw0,
    (isGen_iff w').2 (T.pgen_cancel Y.t.PP.isLB g g''),
    (maps_iff w' _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _ (rigPull_le φ' (spMap f) he' x.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel Y.t.PP.isLB (fun _ => he') r r''),
    (KeyCancel.appLE_eq_iff_stalk w' x.th x'.th).2 fun Z q y i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart Y.t.PP.isLB (φ (φ' (q y)))
    have a := (appLE_eq_iff_stalk w (mem_of_comm hp.w hz) M.θ x.th).1 hs Z (q ≫ φ') y j i hj hi
    have b := (appLE_eq_iff_stalk w'' (mem_of_comm hc''.1.w (le_preimage_comp _ hz)) M.θ x'.th).1 hs'' Z q y j k hj hk
    rw [T Z q y j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [dualMap]
  · apply hp.hom_ext
    · rw [Category.assoc, hv'', Category.assoc, hv, FlagMod.ev_spMap f z M.U hz, FlagMod.dualMap_comp, spMap_comp₀,
        Category.assoc]
      rfl
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.KeyAtBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AppLESpMapFromSpec
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb

namespace GlobalTheory.FlagEmb.CellOpen

variable {O : Type} [CommRing O] {X P : Scheme.{0}} {N : ℕ} {k : Type} [Field k]

theorem top_le_of_mem {W : (Sp k).Opens} {x : Sp k} (hx : x ∈ W) : ⊤ ≤ W := fun y _ => by
  have : y = x := Subsingleton.elim (α := PrimeSpectrum k) y x
  exact this ▸ hx

theorem mem_basicOpen_fnOn (x : Sp k) (a : k) : x ∈ (Sp k).basicOpen (fnOn ⊤ a) ↔ a ≠ 0 := by
  rw [basicOpen_fnOn, top_inf_eq, mem_spOpen]
  have : x.asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal (Subsingleton.elim (α := PrimeSpectrum k) x ⊥)
  rw [this, Ideal.mem_bot]

theorem appLE_spMap_fromSpec {U : X.Opens} (hU : IsAffineOpen U) {A : Type} [CommRing A] (φ : Γ(X, U) →+* A)
    {x : Sp A ⟶ X} (hx : x = spMap φ ≫ hU.fromSpec) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    (x.appLE U ⊤ h).hom a = fnOn ⊤ (φ a) := by
  subst hx
  have e := appLE_appLE (spMap φ) hU.fromSpec hU.fromSpec_preimage_self.ge (le_rfl : ⊤ ≤ spMap φ ⁻¹ᵁ ⊤) a
  refine e.symm.trans ?_
  rw [fromSpec_appLE_self]
  have e2 := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (R := Γ(X, U)) (S := .of A) (CommRingCat.ofHom φ))
  refine Eq.trans ?_ (congrArg (resG (Sp A) (le_top : (⊤ : (Sp A).Opens) ≤ ⊤)) e2.symm)
  rfl

def sec (p0 : P ⟶ X) (g : P ⟶ PSpace O N) (U : X.Opens) (a : Fin (N + 1) → Γ(X, U)) (r : Fin (N + 1)) :
    Γ(P, p0 ⁻¹ᵁ U ⊓ g ⁻¹ᵁ chart O N r) :=
  ∑ q, (p0.appLE U _ inf_le_left).hom (a q) * pullRatio g _ r inf_le_right q

theorem appLE_sec (p0 : P ⟶ X) (g : P ⟶ PSpace O N) {U : X.Opens} (hU : IsAffineOpen U) (a : Fin (N + 1) → Γ(X, U))
    (r : Fin (N + 1)) (z : Sp k ⟶ P) (φ : Γ(X, U) →+* k) (hφ : z ≫ p0 = spMap φ ≫ hU.fromSpec) (b : O →+* k)
    (v : Fin (N + 1) → k) (hv) (hz : z ≫ g = pt b v hv) (h : ⊤ ≤ z ⁻¹ᵁ (p0 ⁻¹ᵁ U ⊓ g ⁻¹ᵁ chart O N r)) :
    v r ≠ 0 ∧ (z.appLE _ ⊤ h).hom (sec p0 g U a r) = fnOn ⊤ ((∑ q, φ (a q) * v q) / v r) := by
  have h2 : ⊤ ≤ pt b v hv ⁻¹ᵁ chart O N r := hz ▸ h.trans (z.preimage_mono inf_le_right)
  have hr : v r ≠ 0 := by
    have := h2 (Set.mem_univ (IsLocalRing.closedPoint k))
    rw [pt_preimage_chart] at this
    intro e
    exact (mem_spOpen.1 this) (e ▸ zero_mem _)
  refine ⟨hr, ((IsUnit.mk0 _ hr).map (fnOn ⊤)).mul_right_cancel ?_⟩
  rw [← map_mul, div_mul_cancel₀ _ hr, sec, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, map_mul, appLE_appLE, appLE_spMap_fromSpec hU φ hφ, appLE_pullRatio, pullRatio_of_eq hz _ h2, mul_assoc,
    pullRatio_pt_top_mul _ _ _ _ _ (IsUnit.mk0 _ hr)]

def linOpen (p0 : P ⟶ X) (g : P ⟶ PSpace O N) (U : X.Opens) (a : Fin (N + 1) → Γ(X, U)) : P.Opens :=
  ⨆ r, P.basicOpen (sec p0 g U a r)

theorem mem_linOpen_iff (p0 : P ⟶ X) (g : P ⟶ PSpace O N) {U : X.Opens} (hU : IsAffineOpen U)
    (a : Fin (N + 1) → Γ(X, U)) (z : Sp k ⟶ P) (φ : Γ(X, U) →+* k) (hφ : z ≫ p0 = spMap φ ≫ hU.fromSpec) (b : O →+* k)
    (v : Fin (N + 1) → k) (hv) (hz : z ≫ g = pt b v hv) (x : Sp k) :
    z x ∈ linOpen p0 g U a ↔ ∑ q, φ (a q) * v q ≠ 0 := by
  have key : ∀ r (h : ⊤ ≤ z ⁻¹ᵁ (p0 ⁻¹ᵁ U ⊓ g ⁻¹ᵁ chart O N r)),
      z x ∈ P.basicOpen (sec p0 g U a r) ↔ ∑ q, φ (a q) * v q ≠ 0 := fun r h => by
    obtain ⟨hr, e⟩ := appLE_sec p0 g hU a r z φ hφ b v hv hz h
    have e2 := Scheme.basicOpen_appLE z ⊤ _ h (sec p0 g U a r)
    rw [top_inf_eq] at e2
    refine (iff_of_eq (congrArg (x ∈ ·) e2)).symm.trans ?_
    refine (iff_of_eq (congrArg (fun t => x ∈ (Sp k).basicOpen t) e)).trans ?_
    rw [mem_basicOpen_fnOn, div_ne_zero_iff, and_iff_left hr]
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := Opens.mem_iSup.1 hx
    exact (key r (top_le_of_mem (x := x) (P.basicOpen_le _ hr))).1 hr
  · intro hx
    obtain ⟨r, hr⟩ := exists_mem_chart O N (g (z x))
    refine Opens.mem_iSup.2 ⟨r, (key r (top_le_of_mem (x := x) ⟨?_, hr⟩)).2 hx⟩
    change x ∈ (z ≫ p0) ⁻¹ᵁ U
    rw [hφ, Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
    trivial

theorem exists_isCellOpen (O : Type) [CommRing O] (X P : Scheme.{0}) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ)
    (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (U : X.affineOpens)
    (D : Let m → Fin (M + 1) → Γ(X, U.1)) (w : Pm m) : ∃ W : P.Opens, IsCellOpen p0 p U D w W := by
  let F : (Σ τ : T, Fin (m τ + 1)) → P.Opens := fun i =>
    linOpen p0 (p (stdEn i.1 i.2 (Nat.le_of_lt_succ i.2.2))) U.1 (lform D (wLet w ∘ std i.1 i.2 (Nat.le_of_lt_succ i.2.2)))
  refine ⟨p0 ⁻¹ᵁ U.1 ⊓ ⟨⋂ i, (F i : Set P), isOpen_iInter_of_finite fun i => (F i).2⟩, fun k _ z => ⟨fun h => ?_, ?_⟩⟩
  · have h1 : Set.range (z ≫ p0) ⊆ Set.range U.2.fromSpec := by
      rw [U.2.range_fromSpec]
      rintro _ ⟨x, rfl⟩
      exact (h ⟨x, rfl⟩).1
    have hi : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
    let l := IsOpenImmersion.lift U.2.fromSpec (z ≫ p0) h1
    have hφ : z ≫ p0 = spMap (Spec.preimage l).hom ≫ U.2.fromSpec :=
      (IsOpenImmersion.lift_fac _ _ h1).symm.trans (congrArg (· ≫ _) (Spec.map_preimage l).symm)
    refine ⟨(Spec.preimage l).hom, hφ, fun τ j hj b v hv hz => ?_⟩
    refine (mem_linOpen_iff p0 _ U.2 _ z _ hφ b v hv hz (IsLocalRing.closedPoint k)).1 ?_
    exact Set.mem_iInter.1 (h ⟨_, rfl⟩).2 ⟨τ, j, Nat.lt_succ_of_le hj⟩
  · rintro ⟨φ, hφ, H⟩ _ ⟨x, rfl⟩
    refine ⟨?_, Set.mem_iInter.2 fun i => ?_⟩
    · change x ∈ (z ≫ p0) ⁻¹ᵁ U.1
      rw [hφ, Scheme.Hom.comp_preimage, U.2.fromSpec_preimage_self]
      trivial
    · let y := z ≫ p (stdEn i.1 i.2 (Nat.le_of_lt_succ i.2.2))
      obtain ⟨v, hv, e⟩ := exists_eq_pt (Spec.preimage (y ≫ PSpace.str _ _)).hom y (Spec.map_preimage _).symm
      exact (mem_linOpen_iff p0 _ U.2 _ z φ hφ _ v hv e x).2 (H _ _ _ _ v hv e)

end GlobalTheory.FlagEmb.CellOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasLocalRingPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atlas_local_ring_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (i : Idx H p) (X : Scheme.{0}) (π : X ⟶ (Y i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y i) π ty) (Z : Mdl Y i₀) (R K k : Type) [CommRing R] [IsLocalRing R] [Field K] [Field k] (φ : R →+* K) (ψ : R →+* k) (z : Sp R ⟶ Z.X) (z' : Sp R ⟶ X), i.c.F ≤ Z.i.c.F → (∀ σ, ty σ ⊆ Z.ty σ) → Function.Injective φ → z (IsLocalRing.closedPoint R) ∈ Z.opn → NatTo Z A (spMap φ ≫ z) (spMap φ ≫ z') → NatTo Z A (spMap ψ ≫ z) (spMap ψ ≫ z') := by
  first | exact @GlobalTheory.DRFlag.Spez.natTo_specialise | exact GlobalTheory.DRFlag.Spez.natTo_specialise | (intros; apply GlobalTheory.DRFlag.Spez.natTo_specialise <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasPullbackPreservesStepStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atlas_pullback_preserves_step : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ) (X' : Scheme.{0}) (f : X' ⟶ X) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas M (f ≫ π) ty'), (∀ (K : Type) [Field K] (w : Sp K ⟶ X') (u : Vecs Dw M.t K), A'.FlagAt w u → A.FlagAt (w ≫ f) u) → IntStep A σ k → IntStep A' σ k := by
  first | exact @GlobalTheory.DRFlag.IntStep.pull | exact GlobalTheory.DRFlag.IntStep.pull | (intros; apply GlobalTheory.DRFlag.IntStep.pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryArcLiftNotConvergesSymmetricDomainStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_arc_lift_not_converges_symmetric_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsBdArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsLift U k y T xx → ∀ x₀ ∈ (U.X k).dom, ∀ x' : ℂ → Frame (U.X k).Ψ N, Tendsto x' imTop (𝓝 x₀) → ¬ ∀ᶠ w in imTop, x' w ∈ (U.X k).dom ∧ SamePos (U.X k) (xx w) (x' w) := by
  first | exact @GlobalTheory.ShFam.BdArc.Leave.lift_not_converges | exact GlobalTheory.ShFam.BdArc.Leave.lift_not_converges | (intros; apply GlobalTheory.ShFam.BdArc.Leave.lift_not_converges <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryExtensionIndependentOfModelStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundaryExtension_independent_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Z' : Model Xo c β') (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K), (algebraMap V K).comp φ = algebraMap c.F K → BdExt Z' φ y → BdExt Z φ y := by
  first | exact @GlobalTheory.CuspFrom.bdExt_of_bdExt | exact GlobalTheory.CuspFrom.bdExt_of_bdExt | (intros; apply GlobalTheory.CuspFrom.bdExt_of_bdExt <;> assumption)
end

