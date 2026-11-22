import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUOfIntegralTorsionPoint
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0082
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCommonField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0081

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OLinearMatrixOfUnifPow
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace PowMatrixLinear

section General

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]

theorem comp_prod {X Y M : C} [MonObj M] [IsCommMonObj M] {J : Type*} (s : Finset J) (f : X ⟶ Y)
    (g : J → (Y ⟶ M)) : f ≫ ∏ l ∈ s, g l = ∏ l ∈ s, f ≫ g l :=
  map_prod (MonoidHom.mk ⟨fun x : Y ⟶ M => f ≫ x, MonObj.comp_one f⟩
    (fun a b => MonObj.comp_mul f a b)) g s

theorem prod_comp {X M N : C} [MonObj M] [IsCommMonObj M] [MonObj N] [IsCommMonObj N] {J : Type*}
    (s : Finset J) (g : J → (X ⟶ M)) (f : M ⟶ N) [IsMonHom f] :
    (∏ l ∈ s, g l) ≫ f = ∏ l ∈ s, g l ≫ f :=
  map_prod (IsMonHom.monoidHom f X) g s

theorem row_comm {M N M' N' : C} [MonObj M] [IsCommMonObj M] [MonObj N] [IsCommMonObj N]
    {j : ℕ} (p : Fin j → (M' ⟶ M)) (r : Fin j → (N' ⟶ N)) (q : M ⟶ N) (hq : IsMonHom q)
    (q' : M' ⟶ N') (hpr : ∀ l, q' ≫ r l = p l ≫ q) (a : Fin j → (M ⟶ M)) (b : Fin j → (N ⟶ N))
    (hab : ∀ l, a l ≫ q = q ≫ b l) (m : M' ⟶ M') (n : N' ⟶ N') (i : Fin j)
    (hm : m ≫ p i = ∏ l, p l ≫ a l) (hn : n ≫ r i = ∏ l, r l ≫ b l) :
    (m ≫ q') ≫ r i = (q' ≫ n) ≫ r i := by
  rw [Category.assoc, Category.assoc, hpr, hn, ← Category.assoc, hm, prod_comp, comp_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Category.assoc, hab, ← Category.assoc, ← hpr, Category.assoc]

end General

theorem pullback_row {S S' : Scheme.{0}} (f : S' ⟶ S) {G G' : Over S} [GrpObj G] [IsCommMonObj G]
    {j : ℕ} (p : Fin j → (G' ⟶ G)) (a : Fin j → (G ⟶ G)) (m : G' ⟶ G') (i : Fin j)
    (h : m ≫ p i = ∏ l, p l ≫ a l) :
    (Over.pullback f).map m ≫ (Over.pullback f).map (p i) =
      ∏ l, (Over.pullback f).map (p l) ≫ (Over.pullback f).map (a l) := by
  rw [← Functor.map_comp, h]
  refine (map_prod ((Over.pullback f).homMonoidHom (X := G') (M := G)) _ _).trans ?_
  exact Finset.prod_congr rfl fun l _ => (Over.pullback f).map_comp (p l) (a l)

theorem pullback_hom_ext {S S' : Scheme.{0}} (f : S' ⟶ S) {G' G : Over S} [GrpObj G']
    [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j) {Z : Over S'} {a b : Z ⟶ (Over.pullback f).obj G'}
    (h : ∀ i, a ≫ (Over.pullback f).map (p.pr i) = b ≫ (Over.pullback f).map (p.pr i)) : a = b :=
  (isLimitOfPreserves (Over.pullback f) p.lim).hom_ext fun i => h i.as

theorem torusEndOf_iff {S : Scheme.{0}} {X : Type} [AddCommGroup X] (h : X → X)
    (t : splitTorus S X ⟶ splitTorus S X) : TorusEndOf X h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem appTop_comp {S : Scheme.{0}} {A B C : Over S} (a : A ⟶ B) (b : B ⟶ C)
    (r : Γ(C.left, ⊤)) :
    (a ≫ b).left.appTop.hom r = a.left.appTop.hom (b.left.appTop.hom r) := by
  rw [Over.comp_left, Scheme.Hom.comp_appTop]; rfl

local instance splitTorus_isCommMonObj (S : Scheme.{0}) (X : Type) [AddCommGroup X] :
    IsCommMonObj (splitTorus S X) :=
  inferInstanceAs (IsCommMonObj ((Over.pullback (toZ S)).obj (splitTorusAff ZU X)))

theorem exists_torus_matrix {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']
    {j : ℕ} (xe : X' ≃+ (Fin j → X)) (pr : Fin j → (splitTorus S X' ⟶ splitTorus S X))
    (hpr : ∀ (i : Fin j) (χ : X), (pr i).left.appTop.hom (charUnit S X χ).val =
      (charUnit S X' (xe.symm (Pi.single i χ))).val)
    (h : Fin j → Fin j → X → X) (h' : X' →+ X')
    (hh : ∀ s χ l, xe (h' (xe.symm (Pi.single s χ))) l = h s l χ)
    (t : Fin j → Fin j → (splitTorus S X ⟶ splitTorus S X))
    (ht : ∀ s l, TorusEndOf X (h s l) (t s l)) :
    ∃ t' : splitTorus S X' ⟶ splitTorus S X', TorusEndOf X' h' t' ∧
      ∀ s, t' ≫ pr s = ∏ l, pr l ≫ t s l := by
  let E' := splitTorusPointsEquiv S X' (splitTorus S X')
  let E := splitTorusPointsEquiv S X (splitTorus S X')
  have hu : ∀ x, (E' (𝟙 _) (Multiplicative.ofAdd x)).val = (charUnit S X' x).val := fun x => by
    rw [splitTorusPointsEquiv_val]
    simp
  obtain ⟨t', ht'⟩ := E'.surjective ((E' (𝟙 _)).comp (AddMonoidHom.toMultiplicative h'))
  have key : ∀ x, t'.left.appTop.hom (charUnit S X' x).val = (charUnit S X' (h' x)).val := by
    intro x
    rw [← splitTorusPointsEquiv_val, ← hu]
    exact congrArg (fun φ => (φ (Multiplicative.ofAdd x)).val) ht'
  refine ⟨t', (torusEndOf_iff _ _).2 key, fun s => E.injective ?_⟩
  rw [map_prod]
  refine MonoidHom.ext fun χ => Units.ext ?_
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  have e : h' (xe.symm (Pi.single s χ)) = ∑ l, xe.symm (Pi.single l (h s l χ)) := by
    apply xe.injective
    rw [← map_sum, xe.apply_symm_apply, Finset.univ_sum_single]
    funext l
    exact hh s χ l
  rw [MonoidHom.finset_prod_apply, Units.coe_prod, splitTorusPointsEquiv_val, appTop_comp, hpr, key,
    e, ← hu, ofAdd_sum, map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [hu, splitTorusPointsEquiv_val, appTop_comp, (torusEndOf_iff _ _).1 (ht s l), hpr]

end PowMatrixLinear

attribute [local instance] PowMatrixLinear.splitTorus_isCommMonObj in
open PowMatrixLinear in

theorem oLinear_matrix_of_unifPow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) (_ : UnifPowOf2 pD pA pG U' U) (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] [Module (Matrix (Fin j) (Fin j) O) D'.toPre.X] (ιD : D.OAct O) (ιA : A.OAct O) (ιG : RingAct G O) (ιD' : D'.OAct (Matrix (Fin j) (Fin j) O)) (ιA' : A'.OAct (Matrix (Fin j) (Fin j) O)) (ιG' : RingAct G' (Matrix (Fin j) (Fin j) O)), U.OLinear O ιD ιA ιG → (∀ (m : (Matrix (Fin j) (Fin j) O)) (x : D'.toPre.X) (i : Fin j), pD.xe (m • x) i = ∑ l, m i l • pD.xe x l) → (∀ (m : (Matrix (Fin j) (Fin j) O)) (i : Fin j), ιD'.onB.act m ≫ pD.pw.pr i = ∏ l, pD.pw.pr l ≫ ιD.onB.act (m i l)) → (∀ (m : (Matrix (Fin j) (Fin j) O)) (i : Fin j), ιA'.act m ≫ pA.pr i = ∏ l, pA.pr l ≫ ιA.act (m i l)) → (∀ (m : (Matrix (Fin j) (Fin j) O)) (i : Fin j), ιG'.act m ≫ pG.pr i = ∏ l, pG.pr l ≫ ιG.act (m i l)) → U'.OLinear (Matrix (Fin j) (Fin j) O) ιD' ιA' ιG' := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U P O _ _ _ _ ιD ιA ιG ιD' ιA' ιG'
    hU hxe hD hA hG
  refine ⟨fun m => ?_, fun e m => ?_, fun e m => ?_⟩
  · refine Fan.IsLimit.hom_ext pA.lim _ _ fun i => ?_
    exact row_comm _ pA.pr U.gen.hom U.gen_hom U'.gen.hom P.gen_pr _ _ (fun l => hU.ext (m i l))
      _ _ i (pullback_row _ _ _ _ i (hG m i)) (hA m i)
  · refine pullback_hom_ext (thick R I e) pD.pw fun i => ?_
    exact row_comm _ _ (U.gt e).q (U.gt e).q_hom (U'.gt e).q (P.q_pr e) _ _
      (fun l => hU.q_lin e (m i l)) _ _ i (pullback_row _ _ _ _ i (hG m i))
      (pullback_row _ _ _ _ i (hD m i))
  · choose pr hi hc using GlobalTheory.PowTorusProj.exists_torus_proj R I j D D' A A' G G' pD pA pG U' U P e
    choose t ht hti using hU.i_lin e
    obtain ⟨t', h₁, h₂⟩ := exists_torus_matrix pD.xe pr hc (fun s l χ => star (m s l) • χ)
      (DistribSMul.toAddMonoidHom _ (star m)) (fun s χ l => by
        change pD.xe (star m • _) l = _
        rw [hxe, pD.xe.apply_symm_apply, Finset.sum_eq_single s]
        · rw [Pi.single_eq_same, Matrix.star_apply]
        · intro k _ hk
          rw [Pi.single_eq_of_ne hk, smul_zero]
        · intro h
          exact absurd (Finset.mem_univ s) h)
      (fun s l => t (m s l)) (fun s l => ht (m s l))
    refine ⟨t', h₁, pullback_hom_ext (thick R I e) pG fun s => ?_⟩
    exact (row_comm pr _ (U.gt e).i (U.gt e).i_hom (U'.gt e).i hi _ _
      (fun l => (hti (m s l)).symm) _ _ s (h₂ s) (pullback_row _ _ _ _ s (hG m s))).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiTendstoZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psi_tendsto_zero : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → (∃ j, (f 0).f j ≠ 0) → PsiRel D (𝟙_ _) f → ∀ n : ℕ, {χ : D.X | ¬ D.PsiIn χ (IsLocalRing.maximalIdeal V ^ n)}.Finite) := by
  intro V _ _ _ hV D A G _ _ U θ f hθ h0 hR n
  haveI := hV.1
  obtain ⟨ga, a, hS⟩ := exists_psiScal V D
  obtain ⟨m, hm⟩ := exists_order_translates V hV D 1 (f 0) h0
  obtain ⟨s, hs⟩ := LevelVanishing.main V hV D A G U 1 θ f hθ.1 (m + n)
  refine s.finite_toSet.subset fun χ hχ => ?_
  by_contra hn
  apply hχ
  have hne : IsLocalRing.maximalIdeal V ^ n ≠ ⊥ := pow_ne_zero n (IsDiscreteValuationRing.not_a_field V)
  refine (psiIn_iff_scalar_mem V D ga a hS χ _ hne).2 ?_
  obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors V) (a χ).val
  obtain ⟨z, J, hJ, hz⟩ := hm χ
  have hq : (q : V) ≠ 0 := nonZeroDivisors.coe_ne_zero q
  have e := PsiInt.psiRel_integral V D ga a f hS hR χ p q (by rw [mul_comm]; exact hpq) (𝟙_ _ ⊗ D.P.A) (snd _ _) z J hJ
  have e₁ : lift (toUnit (𝟙_ _ ⊗ D.P.A)) (snd (𝟙_ _) D.P.A) = 𝟙 _ := by
    ext1
    · exact toUnit_unique _ _
    · simp
  have e₂ : toUnit (𝟙_ _ ⊗ D.P.A) = fst (𝟙_ _) D.P.A := toUnit_unique _ _
  haveI : Flat D.P.A.hom := by
    haveI := D.P.isAb.smooth
    infer_instance
  haveI : Flat (𝟙_ _ ⊗ D.P.A).hom := by
    have h : (𝟙_ _ ⊗ D.P.A).hom = (λ_ D.P.A).hom.left ≫ D.P.A.hom := (Over.w _).symm
    haveI : IsIso (λ_ D.P.A).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (λ_ D.P.A).hom))
    rw [h]
    infer_instance
  let io := (((𝟙_ _ ⊗ D.P.A).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙_ _ ⊗ D.P.A).hom.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom))
  have hio : ∀ v : V, gs (𝟙 _) z ⊤ (scal (𝟙_ _ ⊗ D.P.A).hom v) = io v := fun v => gs_eq _ _ ⊤ trivial _
  have hio' : ∀ v : V, cst (𝟙_ _ ⊗ D.P.A).hom z v = io v := fun v => gs_eq _ _ ⊤ trivial _
  rw [hio, hio, e₁] at e
  have hf := hs χ hn z J hJ
  have hf' := Ideal.map_mono (f := io) (Ideal.pow_le_pow_right (Nat.le_succ (m + n))) hf
  obtain ⟨r, hr, hp⟩ := exists_mem_pow_of_ratio_of_torsionFree V _ io
    (fun v hv x hx => by
      have := cst_regular (𝟙_ _ ⊗ D.P.A).hom z hv
      rw [hio'] at this
      exact this (hx.trans (mul_zero _).symm))
    _ _ p q m n hq e hf' (fun h => hz (by
      rw [← e₂]
      exact (Ideal.unit_mul_mem_iff_mem _ (Units.isUnit _)).1 h))
  refine ⟨r, hr, ?_⟩
  have hq' : algebraMap V (FractionRing V) q ≠ 0 := (IsLocalization.map_units _ q).ne_zero
  apply mul_right_cancel₀ hq'
  rw [← map_mul, ← hp]
  exact hpq.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUOfIntegralTorsionPointStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qkToAkU_of_integral_torsion_point : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Unif I D A G) (k : ℕ), 1 ≤ k → ∀ (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), x ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (p : QkPt D.toPre F k) (xF : TFK (R := R) F ⟶ A.A), p.y = 0 → GtPt.IsPullF F (toUnit (TF (R := R) F)).left gp p.g → xF.left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = (toUnit (TF (R := R) F) ≫ x).left → QkToAkU U.toUnifPre F k p xF := by
  first | exact @GlobalTheory.qkToAkU_of_integral_torsion | exact GlobalTheory.qkToAkU_of_integral_torsion | (intros; apply GlobalTheory.qkToAkU_of_integral_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointBalancedPowerLiftStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.rosati_adjoint_balanced_power_lift : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j), D.TauBimult → ∀ (f g : D.P.A ⟶ D.P.A) [IsMonHom f] [IsMonHom g] (a b : D.X → D.X), (∀ y, D.c (a y) = D.c y ≫ f) → (∀ y, D.c (b y) = D.c y ≫ g) → RosatiAdj D.P.A D.P.L f g → D.TauBal f g a b → ∀ (f' g' : D'.P.A ⟶ D'.P.A) (i l : Fin j), (∀ s, f' ≫ pD.pw.pr s = if s = i then pD.pw.pr l ≫ f else 1) → (∀ s, g' ≫ pD.pw.pr s = if s = l then pD.pw.pr i ≫ g else 1) → D'.TauBal f' g' (fun y => pD.xe.symm (Pi.single i (a (pD.xe y l)))) (fun y => pD.xe.symm (Pi.single l (b (pD.xe y i)))) := by
  first | exact @GlobalTheory.TauBalElem.tauBal_elem | exact GlobalTheory.TauBalElem.tauBal_elem | (intros; apply GlobalTheory.TauBalElem.tauBal_elem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaPowersExpansionSupportSubgroup
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_mul_pow_sec {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Y ⟶ X) (k l : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (k : ℤ))))
    (t : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => (l : ℤ)))) :
    ∃ u : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => ((k + l : ℕ) : ℤ))),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval u r z J = sval s r z J * sval t r z J := by
  obtain ⟨u, hu⟩ := exists_sec hL (φ' := fun _ : Fin 1 => p) (ε' := fun _ => ((k + l : ℕ) : ℤ))
    (fun U _ h => by simp [Fintype.prod_sum_type, zpow_add]) (H1.SectionArithmetic.mulSec s t)
  exact ⟨u, fun Z r z J hJ => (hu Z r z J hJ).trans (H1.SectionArithmetic.sval_mulSec s t r z hJ)⟩

theorem exists_pow_exp_supp : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (Λ : AddSubgroup D.X) (θ : U.SecGT (𝟙_ _) 1) f, U.ExpT (𝟙_ _) 1 θ f → (∀ α ∉ Λ, ∀ j, (f α).f j = 0) → ∀ l : ℕ, 1 ≤ l → ∃ (σ : U.SecGT (𝟙_ _) l) (g : ∀ α, SecBT D (𝟙_ _) l α), U.ExpT (𝟙_ _) l σ g ∧ (∀ α ∉ Λ, ∀ j, (g α).f j = 0) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ r z J = sval θ r z J ^ l) := by
  intro h₁ h₂ V _ _ _ hV D A G _ _ U Λ θ f hθ hf l hl
  induction l, hl using Nat.le_induction with
  | base => exact ⟨θ, f, hθ, hf, fun Z r z J _ => (pow_one _).symm⟩
  | succ l hl ih =>
    obtain ⟨σ, g, hσ, hg, hv⟩ := ih
    obtain ⟨u, hu⟩ := exists_mul_pow_sec U.P.L.isLB _ l 1 σ θ
    obtain ⟨g', hg'⟩ := GlobalTheory.BaseExpansionExists.main h₁ h₂ V hV D A G U (l + 1) (Nat.le_add_left 1 l) u
    exact ⟨u, g', hg', GlobalTheory.T.product_support_in_subgroup_theta V hV D A G U Λ l 1 σ θ u g f g' hσ hθ hg' hu hg hf,
      fun Z r z J hJ => by rw [hu Z r z J hJ, hv Z r z J hJ, pow_succ]⟩

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisedArcIsoMatchesLevelPoints
section
noncomputable section

namespace GlobalTheory.ArcLevel

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem epi_spMap {K k : Type} [Field K] [Field k] (β : K →+* k) : Epi (spMap β) := by
  have : Flat (spMap β) := inferInstance
  have : Surjective (spMap β) := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_genPt {R : Type} [CommRing R] [IsDomain R] {G : Over (Sp R)} {A : Over (Sp (FractionRing R))}
    (gen : (Over.pullback (jK R)).obj G ≅ A) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (g : Sp F ⟶ G.left) (hg : g ≫ G.hom = jFK (R := R) F ≫ jK R) :
    ∃ x : TFK (R := R) F ⟶ A, x.left ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) = g := by
  let z : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G :=
    Over.homMk (pullback.lift g (jFK (R := R) F) hg) (pullback.lift_snd _ _ _)
  refine ⟨z ≫ gen.hom, ?_⟩
  have hgi : gen.hom.left ≫ gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  show (z.left ≫ gen.hom.left) ≫ _ = _
  rw [Category.assoc, ← Category.assoc gen.hom.left, hgi, Category.id_comp]
  exact pullback.lift_fst _ _ _

theorem genRel_of_heq {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ φ' : B ⟶ B₀} (h : φ' = φ)
    {w : LB.Iso M (M₀.pull φ)} {w' : LB.Iso M (M₀.pull φ')} (hw : HEq w' w)
    {K : Type} [Fintype K] {pt : K → (Sp F ⟶ B)} {pt₀ : K → (Sp F ⟶ B₀)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb M pt ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} {x : F} (H : GenRel w t t₀ x) :
    GenRel w' t t₀ x := by
  subst h
  obtain rfl := eq_of_heq hw
  exact H

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_conj_part (v : D.La) : ∃ v' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
    ∀ {S : Scheme.{0}} {B : Type} [CommRing B] {b : Base l B} {s : S ⟶ Sp B} (o : Obj D l b s),
      o.eta v = o.eta v' := by
  have h : v ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]; trivial
  obtain ⟨v₁, h₁, v₂, h₂, rfl⟩ := Submodule.mem_sup.1 h
  exact ⟨v₂, h₂, fun o => by rw [o.eta_add, o.eta_ker _ h₁, _root_.one_mul]⟩

variable {Xo : Moduli D l} {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF}

theorem witData {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {χ : Sp (PowerSeries k) ⟶ Y.X}
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) :
    WitData a W.P.D W.P.oD W.φ W.he W.w W.e := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  exact ⟨s1, s2, s3, s4, s5, fun F _ _ _ _ uF h₁ h₂ => (s6 F uF h₁ h₂).1⟩

set_option maxHeartbeats 1600000 in

theorem level_core (hL : Laws) (hL2 : Laws2) (h5 : Laws5) {O O' : Type} [CommRing O] [CommRing O']
    {β : O →+* c.F} {β' : O' →+* c.F} {Y : Model Xo c β} {Y' : Model Xo c β'}
    {χ : Sp (PowerSeries k) ⟶ Y.X} {χ' : Sp (PowerSeries k) ⟶ Y'.X}
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ')
    (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre)
    (hφ : (hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ)
    (hxe : ∀ x, hD.xe (W.e x) = W'.e x)
    (w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫
      pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)))
    (hw₁ : HEq w₁ W.w) (T : Tri W'.w hD.w w₁) (ψ : W.t.G ≅ W'.t.G)
    (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G) (hbc : IsMonHom bc.hom)
    (hψ : bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left)
    (hPU : IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U)
    (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c) (hy : y ≫ Y.j = jK (PowerSeries k) ≫ χ)
    (hy' : y' ≫ Y'.j = jK (PowerSeries k) ≫ χ') (n : ℕ) (p₀ : QkPt a.D₀ (FractionRing k) n)
    (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G)
    (hσ : (n = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨
      (n = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        HEq p₀ (a.eta v) ∧ σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v))
    (g : Sp (FractionRing (PowerSeries k)) ⟶ W.t.G.left) (hg : g ≫ W.t.G.hom = jK (PowerSeries k))
    (hgm : g ≫ W.m.φ = y ≫ σ.left ≫ Y.m.φ) : g ≫ ψ.hom.left ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ := by
  have hG : GlobalFnsSt := globalFns_holds
  have hR := admissibleBase_powerSeries k
  obtain ⟨F, _, _, _, _, hF⟩ := ArcTransport.exists_commonField k
  have hn : 1 ≤ n := by
    rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact l.A_pos
    · exact le_trans (by norm_num) l.three_le
  have hn' : n ∣ l.M' := by
    rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Nat.dvd_lcm_right _ _
    · exact Nat.dvd_lcm_left _ _
  obtain ⟨q₀, e1, -⟩ := TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing k) F) (RingHom.comp_id _) p₀
  obtain ⟨q, e2, e3⟩ := ArcTransport.exists_transport (witData W) hF rfl hG hn' q₀
  have hF' : ∀ r : PowerSeries k, algebraMap (FractionRing (PowerSeries k)) F (algebraMap _ _ r) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap _ _ ((RingHom.id _) r)) := fun _ => rfl
  obtain ⟨q', hq₁, hq₂⟩ := qkPullExists hG _ _ (RingHom.id _) W'.P.D.toPre W.P.D.toPre hD F hF' n q

  have hc : (y' ≫ σ'.left ≫ Y'.m.φ) ≫ Y'.t.G.hom = jK (PowerSeries k) ≫ χ' := by
    have a₁ : Y'.m.φ ≫ Y'.t.G.hom = Y'.oF.t.G.hom ≫ Y'.j := Y'.m.cart.1.w
    have a₂ : σ'.left ≫ Y'.oF.t.G.hom = 𝟙 _ := Over.w σ'
    rw [Category.assoc, Category.assoc, a₁, reassoc_of% a₂, hy']
  let g' : Sp (FractionRing (PowerSeries k)) ⟶ W'.t.G.left := W'.m.cart.1.lift _ _ hc
  have hg' : g' ≫ W'.t.G.hom = jK (PowerSeries k) := W'.m.cart.1.lift_snd _ _ _
  have hgm' : g' ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ := W'.m.cart.1.lift_fst _ _ _
  have hih : ψ.inv.left ≫ ψ.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  obtain ⟨x, hx⟩ := exists_genPt W.P.U.gen (jFK (R := PowerSeries k) F ≫ g) (by rw [Category.assoc, hg])
  obtain ⟨x', hx'⟩ := exists_genPt W'.P.U.gen (jFK (R := PowerSeries k) F ≫ g') (by rw [Category.assoc, hg'])
  obtain ⟨x'', hx''⟩ := exists_genPt W.P.U.gen (jFK (R := PowerSeries k) F ≫ g' ≫ ψ.inv.left)
    (by rw [Category.assoc, Category.assoc, Over.w, hg'])
  have t₁ : QkToAkU W.P.U.toUnifPre F n q x := by
    refine (W.spec.2.2.2.2.2 F _ hF rfl).2 (jFK (R := PowerSeries k) F ≫ y) (by rw [Category.assoc, hy]) n p₀ σ ?_
      q₀ q x e1 e2 e3 ?_
    · rcases hσ with ⟨h, v, h₁, h₂, -⟩ | ⟨h, v, hv, h₁, h₂, -⟩
      · exact Or.inl ⟨h, v, h₁, h₂⟩
      · exact Or.inr ⟨h, v, hv, h₁, h₂⟩
    · rw [reassoc_of% hx, hgm, Category.assoc]
  have t₂ : QkToAkU W'.P.U.toUnifPre F n q' x' := by
    refine (W'.spec.2.2.2.2.2 F _ hF rfl).2 (jFK (R := PowerSeries k) F ≫ y') (by rw [Category.assoc, hy']) n p₀ σ' ?_
      q₀ q' x' e1 ?_ (fun z => ?_) ?_
    · rcases hσ with ⟨h, v, h₁, -, h₂⟩ | ⟨h, v, hv, h₁, -, h₂⟩
      · exact Or.inl ⟨h, v, h₁, h₂⟩
      · exact Or.inr ⟨h, v, hv, h₁, h₂⟩
    · have : hD.xe q.y = q'.y := by rw [hq₁, AddEquiv.apply_symm_apply]
      rw [← this, e2]; exact hxe _
    · obtain ⟨hψ', hm⟩ := hq₂.2 (W.e z)
      have pm := (maps_iff hD.w _ _ _ (q.g.s (W.e z)) (q'.g.s (hD.xe (W.e z))) (𝟙 _) _
        (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ') (fun _ => rfl)).1 hm
      have k' := (genRel_transfer T W'.P.D.toPre.P.isLB W.P.D.toPre.P.isLB hψ' pm _ _).2
        (genRel_of_heq hφ hw₁ (e3 z))
      rw [hxe z] at k'
      exact k'
    · rw [reassoc_of% hx', hgm', Category.assoc]
  have t₃ : QkToAkU W.P.U.toUnifPre F n q x'' :=
    h5.qkBaseChange _ _ _ _ hR hR (RingHom.id _) W'.P.D W'.P.A W'.t.G W'.P.U W.t.G bc hbc W.P.A W.P.D hD W.P.U
      hPU F hF' n hn q' x' q x'' hq₁ hq₂ (by rw [hψ, reassoc_of% hx'', hih, Category.comp_id, hx']) t₂
  have hxx := TorsionImage.qkToAkU_unique hL hL2 _ _ hR W.P.D W.P.A W.t.G W.t.semi W.P.U F n hn q x x'' t₁ t₃
  have := epi_spMap (algebraMap (FractionRing (PowerSeries k)) F)
  have hgg : g = g' ≫ ψ.inv.left :=
    (cancel_epi (spMap (algebraMap (FractionRing (PowerSeries k)) F))).1 (hx.symm.trans (hxx ▸ hx''))
  rw [hgg, Category.assoc, reassoc_of% hih, hgm']

theorem level_match : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ') (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre), ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ ∧ (∀ x, hD.xe (W.e x) = W'.e x) ∧ ∃ w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)), HEq w₁ W.w ∧ Tri W'.w hD.w w₁) → ∀ (ψ : W.t.G ≅ W'.t.G) (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G), IsMonHom ψ.hom → IsMonHom bc.hom → bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left → IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U → (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) → ∀ (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c), y ≫ Y.j = jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = jK (PowerSeries k) ≫ χ' → y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → (∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G), ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) → ∀ g : Sp (FractionRing (PowerSeries k)) ⟶ W.t.G.left, g ≫ W.t.G.hom = jK (PowerSeries k) → g ≫ W.m.φ = y ≫ σ.left ≫ Y.m.φ → g ≫ ψ.hom.left ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ) := by
  intro hL hL2 h5 E _ _ _ H D l Xo c k _ bF a O O' _ _ β β' Y Y' χ χ' W W' hD ⟨hφ, hxe, w₁, hw₁, T⟩ ψ bc _ hbc hψ hPU _
    y y' hy hy' _ _ σ σ' hσ g hg hgm
  rcases hσ with ⟨v, h₁, h₂⟩ | ⟨v, h₁, h₂⟩
  · exact level_core hL hL2 h5 W W' hD hφ hxe w₁ hw₁ T ψ bc hbc hψ hPU y y' hy hy' l.A (a.etaA v) σ σ'
      (Or.inl ⟨rfl, v, HEq.rfl, h₁, h₂⟩) g hg hgm
  · obtain ⟨v', hv', e⟩ := exists_conj_part (l := l) v
    exact level_core hL hL2 h5 W W' hD hφ hxe w₁ hw₁ T ψ bc hbc hψ hPU y y' hy hy' l.M (a.eta v') σ σ'
      (Or.inr ⟨rfl, v', hv', HEq.rfl, h₁.trans (e _), h₂.trans (e _)⟩) g hg hgm

end GlobalTheory.ArcLevel
end
end

