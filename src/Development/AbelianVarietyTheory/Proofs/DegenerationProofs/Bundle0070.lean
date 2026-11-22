import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TauBimultOfBaseChange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section

namespace GlobalTheory

namespace TauDescent

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {β : D'.P.A.left ⟶ D.P.A.left}

theorem cub_of_grpPullback (hG : GlobalFnsSt) (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β)
    (v : LB.Iso D'.P.L (D.P.L.pull β)) (hvg : v.IsGen) {T' : Over (Sp R')} {z : T'.left} {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') (x x' y : T' ⟶ D'.P.A) :
    val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
        ((lift x (lift x' y)).left ≫ (cubeMapOf gp).F3) z J =
      (∏ I : thK.{0}, gw v ((lift x (lift x' y)).left ≫ thφ D'.P.A (x3 D'.P.A) I) z
        (J (((lift x (lift x' y)).left ≫ thφ D'.P.A (x3 D'.P.A) I) ≫ β))
        (J' ((lift x (lift x' y)).left ≫ thφ D'.P.A (x3 D'.P.A) I)) ^ thε I) * cubV D'.cub z J' x x' y := by
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff v).1 hvg) D.P.isLB D'.P.isLB (φ' := thφ D'.P.A (x3 D'.P.A))
    (ε := thε) D'.cub.t D'.cub.isGen
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 D'.P.A).left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val t r z J = (∏ I : thK.{0}, gw v (r ≫ thφ D'.P.A (x3 D'.P.A) I) z
        (J ((r ≫ thφ D'.P.A (x3 D'.P.A) I) ≫ β)) (J' (r ≫ thφ D'.P.A (x3 D'.P.A) I)) ^ thε I) *
        val (L := D'.P.L) (φ := thφ D'.P.A (x3 D'.P.A)) (ε := thε) D'.cub.t r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl)
    rw [Category.assoc]
  let e : 𝟙_ (Over (Sp R')) ⟶ G3 D'.P.A := lift 1 (lift 1 1)
  have sj : Function.Surjective
      ((snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2)
  have he : e.left ≫ (snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := gen_unique' D.P.isLB (φ := fun I => (cubeMapOf gp).F3 ≫ thφ D.P.A (x3 D.P.A) I) (ε := thε)
    (fun V _ k => Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ thε I) ((cubeMapOf gp).psum_comm I.down))
    _ e.left he sj (pullGen_isGen _ _ _ _ D.cub.isGen (cubeMapOf gp).F3) ht (fun y I hI => by
      choose I' hI' using fun χ : (𝟙_ (Over (Sp R'))).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ y)
      have C' : IsCub (cubV D'.cub y I') := isCub_cubV D'.cub hI'
      have p := prod_cub (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) 1 1
        (fun q => gw v q y (I (q ≫ β)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine Eq.trans ?_ ((hv' _ e.left y I I' hI hI').trans (congrArg₂ (· * ·) p (C'.face 1 1))).symm
      have o : pushPt gp.1.w (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) = 1 := map_one (pushHom gp _)
      have q : e.left ≫ (cubeMapOf gp).F3 =
          (lift (pushPt gp.1.w (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A)) (lift (pushPt gp.1.w 1)
            (pushPt gp.1.w 1))).left := hom_ext_triple _ fun i => by
        rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
        fin_cases i <;> simp [e, x3, pushPt, cubeMapOf]
      refine (val_pull hI _ _ _).trans ?_
      rw [q, o]
      refine ((isCub_cubV D.cub (T := Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ)) hI).face 1 1).trans ?_
      simp) _ (lift x (lift x' y)).left z J hJ
  exact (val_pull hJ _ _ _).symm.trans (key.trans (hv' _ _ z J J' hJ hJ'))

set_option maxHeartbeats 1000000 in
theorem tauBimult_down (hG : GlobalFnsSt) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X)
    (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β) (hvg : v.IsGen)
    (hc : ∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) (hρ : RigCmp φ D D' β v)
    (gam : (TK R').left ⟶ (TK R).left) (hgam : gam ≫ jK R = jK R' ≫ spMap φ) (hψ : PsiCmp D D' β v xe gam)
    (hB : D'.TauBimult) : D.TauBimult := by
  intro a a' b
  obtain ⟨a, rfl⟩ := xe.surjective a
  obtain ⟨a', rfl⟩ := xe.surjective a'
  obtain ⟨b, rfl⟩ := xe.surjective b
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨y⟩ : Nonempty (TK R').left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R')))
  have red : IsReduced (TK R).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (FractionRing R))))
  have sub : Subsingleton (TK R).left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  refine TauPull.corr_of_dense D.P.isLB gam y (fun V hV => ?_) fun J hJ => ?_
  · obtain ⟨x, hx⟩ := hV
    rw [Subsingleton.elim (gam y) x]; exact hx
  choose J' hJ₀ using fun χ : (TK R').left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ y)
  have hJ' : Good D'.P.L y J' := hJ₀
  let T : Over (Spec (CommRingCat.of R)) := Over.mk ((TK R').hom ≫ spMap φ)
  let κ : T ⟶ TK R := Over.homMk gam hgam
  let B : (TK R' ⟶ D'.P.A) → (T ⟶ D.P.A) := fun x => pushPt gp.1.w x
  have βc : ∀ χ, B (cP D' _ χ) = cP D _ (xe χ) := fun χ => Over.OverMorphism.ext (by
    show ((TK R').hom ≫ (D'.c χ).left) ≫ β = ((TK R').hom ≫ spMap φ) ≫ (D.c (xe χ)).left
    rw [Category.assoc, hc, Category.assoc])
  let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ := fun x => gw v x.left y (J (x.left ≫ β)) (J' x.left)
  let θ : (T ⟶ D.P.A) → (T ⟶ D.P.A) → (T ⟶ D.P.A) → ((TK R').left.presheaf.stalk y)ˣ := th D (T := T) y J
  have cub : ∀ a b c : TK R' ⟶ D'.P.A, θ (B a) (B b) (B c) =
        Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ *
          th D' y J' a b c := by
    intro a b c
    have e := cub_of_grpPullback hG gp v hvg (T' := TK R') hJ hJ' a b c
    have q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 = (lift (B a) (lift (B b) (B c))).left :=
      hom_ext_triple _ fun i => by
        rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
        fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => gw v q y (J (q ≫ β)) (J' q))) rfl)
  have vψ : ∀ χ, val (D.psi (xe χ)) gam y J = (Ω (cP D' _ χ))⁻¹ * val (D'.psi χ) (𝟙 _) y J' := fun χ => by
    have h₁ : D'.xK χ ≫ β = gam ≫ D.xK (xe χ) := by
      show (jK R' ≫ (D'.c χ).left) ≫ β = gam ≫ jK R ≫ (D.c (xe χ)).left
      rw [Category.assoc, hc, ← Category.assoc, ← hgam, Category.assoc]
    have e := CubTransport.val_pmaps (fun _ => h₁) (hψ χ) (𝟙 _) hJ hJ'
    rw [Fintype.prod_unique, zpow_neg_one, Category.id_comp, Category.id_comp] at e
    exact e
  have vρ : val D.rigK gam y J = Ω 1 * val D'.rigK (𝟙 _) y J' := by
    have h₁ : eSec D'.P.A ≫ β = spMap φ ≫ eSec D.P.A := by
      have o := congrArg (fun q => q.left) (map_one (pushHom gp (𝟙_ (Over (Sp R')))))
      have o' : (toUnit (𝟙_ (Over (Sp R'))) ≫ η[D'.P.A]).left ≫ β =
          ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ) ≫ eSec D.P.A := o
      rw [toUnit_unit, Category.id_comp] at o'
      exact o'.trans (congrArg (· ≫ eSec D.P.A) (Category.id_comp _))
    have e := CubTransport.val_pmaps (fun _ => h₁) hρ (TK R').hom hJ hJ'
    rw [Fintype.prod_unique, zpow_one] at e
    have b₁ : gam ≫ (toUnit (TK R)).left = (TK R').hom ≫ spMap φ := hgam
    have b₂ : 𝟙 _ ≫ (toUnit (TK R')).left = (TK R').hom := Category.id_comp _
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
    rw [b₁, b₂]
    exact e
  have key := (val_mul hJ' _ _ _).symm.trans ((val_corr hJ' (hB a a' b) (𝟙 _)).trans (val_mul hJ' _ _ _))
  replace key := (congrArg₂ (· * ·) rfl
    (val_cub D'.cub (𝟙 (TK R')) hJ' (cP D' _ a) (cP D' _ a') (cP D' _ b))).symm.trans key
  rw [Category.id_comp, Category.id_comp, Category.id_comp, TauPull.val_tau _ hJ', TauPull.val_tau _ hJ',
    TauPull.val_tau _ hJ'] at key
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  have cb : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift (cP D (TK R) (xe a)) (lift (cP D (TK R) (xe a')) (cP D (TK R) (xe b)))).left) gam y J =
      θ (cP D T (xe a)) (cP D T (xe a')) (cP D T (xe b)) := by
    refine (val_cub D.cub κ hJ (cP D _ (xe a)) (cP D _ (xe a')) (cP D _ (xe b))).trans ?_
    rw [comp_cP, comp_cP, comp_cP]
  refine (congrArg₂ (· * ·) rfl cb).trans ?_
  rw [← βc, ← βc, ← βc, cub, TauPull.val_tau _ hJ, TauPull.val_tau _ hJ, TauPull.val_tau _ hJ, ← map_add, ← map_add,
    ← map_add, ← map_add, vψ, vψ, vψ, vψ, vψ, vψ, vψ, vρ, cPoint_add, cPoint_add, cPoint_add, cPoint_add]
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

end TauDescent

theorem tauBimult_of_baseChange : GlobalFnsSt → ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D'.TauBimult → D.TauBimult :=
  fun hG _ _ _ _ _ _ _ _ _ _ v xe gp hv hc hρ gam hgam hψ hB =>
    TauDescent.tauBimult_down hG v xe gp hv hc hρ gam hgam hψ hB

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationChartValueFormsCorrespondStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_chart_value_forms_correspond : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → (∀ U₀ : UnifPre I D A G, ∃ U : PreU I D.toPre A G, Under U U₀) ∧ (∀ U : PreU I D.toPre A G, ∃ U₀ : UnifPre I D A G, Under U U₀) ∧ ∀ (U : PreU I D.toPre A G) (U₀ : UnifPre I D A G), Under U U₀ → ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D.toPre (𝟙_ _) k α) (σ₀ : H0 U₀.LG.L k) (f₀ : ∀ α, D.toPre.SecB k α), (∀ σ₁ : H0 U.P.L.L k, HEq σ₁ σ₀ → ∀ z J, Good U.P.L.L z J → sval σ (𝟙 _) z J = sval σ₁ (snd (𝟙_ _) G).left z J) → (∀ α z J, Good D.toPre.P.L z J → sval (f α) (𝟙 _) z J = sval (f₀ α) (snd (𝟙_ _) D.toPre.P.A).left z J) → (U.ExpT (𝟙_ _) k σ f ↔ ∀ e, U₀.ExpandsAt e k σ₀ f₀) := by
  first | exact @GlobalTheory.LN.PreForm.under_exists_and_expands | exact GlobalTheory.LN.PreForm.under_exists_and_expands | (intros; apply GlobalTheory.LN.PreForm.under_exists_and_expands <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelLabelledTorsionPointsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_model_labelled_torsion_points : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) ∧ (∀ a b, x (a + b) = x a * x b) ∧ Function.Injective x ∧ ∀ z : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, z ^ (S.r * S.N) = 1 → ∃ a, z = x a := by
  first | exact @GlobalTheory.ZH.utest_torsion_points | exact GlobalTheory.ZH.utest_torsion_points | (intros; apply GlobalTheory.ZH.utest_torsion_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniversalBasisMoveBaseChange
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnivBasisMove

open GlobalTheory.ThetaReal GlobalTheory.ThetaPtMove GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)} {a : ℤ}

def Rel (w : LB.Iso L₁ (L₀.pull φ)) (s : SecM A L₁ a T) (s₀ : SecM G L₀ a T₀) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
    ThetaAct.sv s₀ (r ≫ psi hp τ hτ) z J =
      (wVal w z J J' (r ≫ (snd T A).left) ^ a).val * ThetaAct.sv s r z J'

theorem exists_rel (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (s₀ : SecM G L₀ a T₀) :
    ∃ s, Rel hp τ hτ w s s₀ := by
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ (SecM.toSec G s₀)
  exact ⟨SecM.ofSec A s, hs⟩

theorem exists_rel_up [IsIso τ] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (s : SecM A L₁ a T) :
    ∃ s₀, Rel hp τ hτ w s s₀ := by
  obtain ⟨s₀, hs⟩ := exists_secRel_up hp τ hτ hw hL₀ hL₁ (SecM.toSec A s)
  exact ⟨SecM.ofSec G s₀, hs⟩

variable {hp τ hτ}

theorem Rel.unique_down (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {s s' : SecM A L₁ a T} {s₀ : SecM G L₀ a T₀}
    (h : Rel hp τ hτ w s s₀) (h' : Rel hp τ hτ w s' s₀) : s = s' :=
  ThetaAct.sv_ext hL₁ fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    exact (Units.mul_right_inj _).1 ((h _ _ _ _ _ hJ hJ').symm.trans (h' _ _ _ _ _ hJ hJ'))

theorem Rel.unique_up [IsIso τ] (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {s : SecM A L₁ a T} {s₀ s₀' : SecM G L₀ a T₀}
    (h : Rel hp τ hτ w s s₀) (h' : Rel hp τ hτ w s s₀') : s₀ = s₀' :=
  ThetaAct.sv_ext hL₀ fun y J hJ => by
    obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    obtain ⟨χ, -, h₂⟩ := WeilPull.exists_psi_inv hp τ hτ
    have h₂' : χ ≫ psi hp τ hτ = 𝟙 _ := h₂
    have q := (h _ χ y _ _ hJ hJ').trans (h' _ χ y _ _ hJ hJ').symm
    rwa [h₂'] at q

theorem Rel.add {s t : SecM A L₁ a T} {s₀ t₀ : SecM G L₀ a T₀}
    (h : Rel hp τ hτ w s s₀) (h' : Rel hp τ hτ w t t₀) : Rel hp τ hτ w (s + t) (s₀ + t₀) :=
  fun Z r z J J' hJ hJ' => by
    rw [ThetaAct.sv_add _ _ _ _ hJ, ThetaAct.sv_add _ _ _ _ hJ', h _ _ _ _ _ hJ hJ', h' _ _ _ _ _ hJ hJ', mul_add]

theorem Rel.smul {s : SecM A L₁ a T} {s₀ : SecM G L₀ a T₀} (c : Γ(T₀.left, ⊤))
    (h : Rel hp τ hτ w s s₀) : Rel hp τ hτ w (τ.appTop.hom c • s) (c • s₀) :=
  fun Z r z J J' hJ hJ' => by
    rw [ThetaAct.sv_smul _ _ _ _ hJ, ThetaAct.sv_smul _ _ _ _ hJ', h _ _ _ _ _ hJ hJ', mul_left_comm,
      Category.assoc, psi_fst', ← Category.assoc]
    exact congrArg (fun x => _ * (x * _)) (gs_pull _ τ z ⊤ trivial c).symm

theorem Rel.pull {s : SecM A L₁ a T} {s₀ : SecM G L₀ a T₀} (h : Rel hp τ hτ w s s₀)
    {T' : Over S'} {T₀' : Over S} (σ : T'.left ⟶ T₀'.left) (hσ : σ ≫ T₀'.hom = T'.hom ≫ f)
    (u : T' ⟶ T) (u₀ : T₀' ⟶ T₀) (hu : σ ≫ u₀.left = u.left ≫ τ) :
    Rel hp σ hσ w (VVRank.pullM A L₁ a u s) (VVRank.pullM G L₀ a u₀ s₀) :=
  fun Z r z J J' hJ hJ' => by
    have e : psi hp σ hσ ≫ (u₀ ▷ G).left = (u ▷ A).left ≫ psi hp τ hτ := by
      refine psi_ext ?_ ?_
      · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc, psi_fst',
          Category.assoc, Category.assoc, psi_fst', hu, ← Category.assoc (u ▷ A).left, ← Over.comp_left,
          whiskerRight_fst, Over.comp_left, Category.assoc]
      · rw [Category.assoc, VVRank.whisker_snd_left, psi_snd', Category.assoc, psi_snd', ← Category.assoc,
          VVRank.whisker_snd_left]
    have q := h _ (r ≫ (u ▷ A).left) z _ _ hJ hJ'
    rw [Category.assoc, Category.assoc, ← e, VVRank.whisker_snd_left, ← Category.assoc] at q
    exact (VVRank.sv_pullS G a u₀ (SecM.toSec G s₀) _ z hJ).trans
      (q.trans (congrArg _ (VVRank.sv_pullS A a u (SecM.toSec A s) _ z hJ').symm))

theorem exists_linearEquiv (hp : IsGrpPullback A G f φ) (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB)
    (a : ℤ) (T : Over S') :
    ∃ E : SecM G L₀ a (Over.mk (T.hom ≫ f)) ≃ₗ[Γ(T.left, ⊤)] SecM A L₁ a T,
      ∀ x, Rel hp (T₀ := Over.mk (T.hom ≫ f)) (𝟙 T.left) (Category.id_comp _) w (E x) x := by
  have : IsIso (C := Scheme.{0}) (X := T.left) (Y := (Over.mk (T.hom ≫ f)).left) (𝟙 T.left) := IsIso.id _
  choose D hD using exists_rel hp (T := T) (T₀ := Over.mk (T.hom ≫ f)) (𝟙 T.left) (Category.id_comp _) (a := a)
    hw hL₀ hL₁
  let l : SecM G L₀ a (Over.mk (T.hom ≫ f)) →ₗ[Γ(T.left, ⊤)] SecM A L₁ a T :=
    { toFun := D
      map_add' := fun x y => (hD _).unique_down hL₀ hL₁ ((hD x).add (hD y))
      map_smul' := fun c x => (hD _).unique_down hL₀ hL₁ (Rel.smul (T₀ := Over.mk (T.hom ≫ f)) (τ := 𝟙 T.left) c (hD x)) }
  refine ⟨LinearEquiv.ofBijective l ⟨fun x y e => ?_, fun s => ?_⟩, hD⟩
  · have e' : D x = D y := e
    exact (hD x).unique_up hL₀ hL₁ (e' ▸ hD y)
  · obtain ⟨s₀, hs⟩ := exists_rel_up hp (T := T) (T₀ := Over.mk (T.hom ≫ f)) (𝟙 T.left) (Category.id_comp _)
      hw hL₀ hL₁ s
    exact ⟨s₀, (hD s₀).unique_down hL₀ hL₁ hs⟩

theorem univBasis_move : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (P : PolAV S) (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → ∀ (n : ℤ) (κ : Type) [Fintype κ] (T₀ : Over S) (τ : S' ⟶ T₀.left), τ ≫ T₀.hom = f → ∀ b₀ : κ → SecM P.A P.L n T₀, UnivBasis P n b₀ → ∃ b : κ → SecM P'.A P'.L n (baseOver S'), UnivBasis P' n b := by
  intro S S' f P P' φ hp hw n κ _ T₀ τ hτ b₀ hb₀
  obtain ⟨w, hw⟩ := hw
  have hτ' : τ ≫ T₀.hom = (baseOver S').hom ≫ f := hτ.trans (Category.id_comp _).symm
  choose b hb using fun i => exists_rel hp (T := baseOver S') τ hτ' hw P.isLB P'.isLB (b₀ i)
  refine ⟨b, fun T hT h => ?_⟩
  have hh : h.left = T.hom := (Category.comp_id _).symm.trans (Over.w h)
  let h₀ : Over.mk (T.hom ≫ f) ⟶ T₀ := Over.homMk (T.hom ≫ τ) (by
    change (T.hom ≫ τ) ≫ T₀.hom = T.hom ≫ f
    rw [Category.assoc, hτ])
  have : IsAffine (Over.mk (T.hom ≫ f)).left := hT
  obtain ⟨c, hc⟩ := hb₀ _ h₀
  obtain ⟨E, hE⟩ := exists_linearEquiv hp hw P.isLB P'.isLB n T
  refine ⟨Module.Basis.map (R := Γ(T.left, ⊤)) c E, fun i => ?_⟩
  refine (hE (c i)).unique_down P.isLB P'.isLB ?_
  rw [hc]
  exact (hb i).pull _ _ h h₀ ((Category.id_comp _).trans (congrArg (· ≫ τ) hh.symm))

end GlobalTheory.UnivBasisMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValUnitNeZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ZH.FrameNorm
open CrdCalc

section Reg
variable {K C : Type} [Field K] [Field C] {Y : Scheme.{0}} {q : Y ⟶ Sp K} {σ : K →+* C}

variable (q σ) in

def Reg (W : Y.Opens) (F : (Sp C ⟶ Y) → C) : Prop :=
  ∃ r : Γ(Y, W), ∀ x : Sp C ⟶ Y, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → F x = valR x W r

variable {W : Y.Opens} {F G : (Sp C ⟶ Y) → C}

theorem Reg.mul (hF : Reg q σ W F) (hG : Reg q σ W G) : Reg q σ W fun x => F x * G x := by
  obtain ⟨r, hr⟩ := hF
  obtain ⟨s, hs⟩ := hG
  exact ⟨r * s, fun x hx hW => by rw [valR_mul x W hW, ← hr x hx hW, ← hs x hx hW]⟩

theorem Reg.pow (hF : Reg q σ W F) (n : ℕ) : Reg q σ W fun x => F x ^ n := by
  obtain ⟨r, hr⟩ := hF
  exact ⟨r ^ n, fun x hx hW => by
    beta_reduce
    rw [hr x hx hW, valR_eq x W hW, valR_eq x W hW, map_pow]⟩

theorem Reg.sum {I : Type} [Fintype I] {F : I → (Sp C ⟶ Y) → C} (hF : ∀ i, Reg q σ W (F i)) :
    Reg q σ W fun x => ∑ i, F i x := by
  choose r hr using hF
  refine ⟨∑ i, r i, fun x hx hW => ?_⟩
  rw [valR_eq x W hW, map_sum]
  exact Finset.sum_congr rfl fun i _ => (hr i x hx hW).trans (valR_eq x W hW _)

theorem Reg.const (a : K) : Reg q σ W fun _ => σ a :=
  ⟨constFn q W a, fun x hx hW => (GlobalTheory.Points.valR_constFn_of_over q σ x hx W hW a).symm⟩

theorem Reg.pull {X : Scheme.{0}} (g : Y ⟶ X) {U : X.Opens} (h : W ≤ g ⁻¹ᵁ U) (s : Γ(X, U)) :
    Reg q σ W fun x => valR (x ≫ g) U s :=
  ⟨(g.appLE U W h).hom s, fun x _ hW => (GlobalTheory.Points.valR_appLE x g h hW s).symm⟩

theorem Reg.inv_unit {X : Scheme.{0}} (g : Y ⟶ X) {U : X.Opens} (h : W ≤ g ⁻¹ᵁ U) (s : Γ(X, U)ˣ) :
    Reg q σ W fun x => (valR (x ≫ g) U s.val)⁻¹ := by
  refine ⟨(g.appLE U W h).hom (s⁻¹).val, fun x _ hW => ?_⟩
  have hU : ⊤ ≤ (x ≫ g) ⁻¹ᵁ U := fun _ hz => h (hW hz)
  rw [GlobalTheory.Points.valR_appLE x g h hW]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← valR_mul _ U hU, Units.mul_inv, valR_eq _ U hU, map_one]

theorem Reg.inv_basicOpen {X : Scheme.{0}} (g : Y ⟶ X) {U : X.Opens} (s : Γ(X, U))
    (h : W ≤ g ⁻¹ᵁ X.basicOpen s) : Reg q σ W fun x => (valR (x ≫ g) U s)⁻¹ := by
  obtain ⟨r, hr⟩ := Reg.inv_unit (q := q) (σ := σ) g h (X.toRingedSpace.isUnit_res_basicOpen s).unit
  refine ⟨r, fun x hx hW => ?_⟩
  rw [← hr x hx hW]
  exact congrArg _ (valR_res (x ≫ g) (X.basicOpen_le s) (fun _ hz => h (hW hz)) s).symm

end Reg

section Val
variable {C : Type} [Field C] {X Y : Scheme.{0}}

theorem val_unit_ne_zero (x : Sp C ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)ˣ) :
    valR x U s.val ≠ 0 := by
  rw [valR_eq x U h]
  exact (s.isUnit.map _).ne_zero

theorem val_zpow (x : Sp C ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)ˣ) (n : ℤ) :
    valR x U (s ^ n).val = valR x U s.val ^ n := by
  rw [valR_eq x U h, valR_eq x U h, ← MonoidHom.coe_coe, ← Units.coe_map, map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

theorem val_res_pull (x : Sp C ⟶ Y) (g : Y ⟶ X) {U : X.Opens} {W : Y.Opens} (e : W ≤ g ⁻¹ᵁ U)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (s : Γ(X, U)ˣ) : valR x W (res e (pullU g U s)).val = valR (x ≫ g) U s.val :=
  GlobalTheory.Points.valR_appLE x g e h s.val

def tv (L : LB X) (x : Sp C ⟶ X) (i j : L.ι) : C := valR x (L.U i ⊓ L.U j) (L.g i j).val

theorem tv_ne_zero (L : LB X) {x : Sp C ⟶ X} {i j : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    tv L x i j ≠ 0 := val_unit_ne_zero x (U := L.U i ⊓ L.U j) (fun _ hz => ⟨hi hz, hj hz⟩) _

theorem tv_self {L : LB X} (hL : L.IsLB) {x : Sp C ⟶ X} {i : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) :
    tv L x i i = 1 := by
  have e := congrArg (fun u : Γ(X, L.U i)ˣ => valR x (L.U i) u.val) (hL.g_self i)
  refine (valR_res x (le_inf le_rfl le_rfl) hi _).symm.trans (e.trans ?_)
  rw [valR_eq x _ hi, Units.val_one, map_one]

theorem le_wchart {L : LB X} {I : Type} [Fintype I] {φ : I → (Y ⟶ X)} {x : Sp C ⟶ Y} {j : I → L.ι}
    (h : ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k)) : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j :=
  fun _ hz => Set.mem_iInter.2 fun k => h k hz

theorem tv_linComb (L : LB X) {I : Type} [Fintype I] (φ : I → (Y ⟶ X)) (ε : I → ℤ) {x : Sp C ⟶ Y}
    {j j' : I → L.ι} (h : ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k)) (h' : ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j' k)) :
    tv (LB.LinComb L φ ε) x j j' = ∏ k, tv L (x ≫ φ k) (j k) (j' k) ^ ε k := by
  have hh : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := fun _ hz => ⟨le_wchart h hz, le_wchart h' hz⟩
  have A : ∀ u : I → Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ,
      valR x _ (∏ k, u k ^ ε k).val = ∏ k, valR x _ (u k).val ^ ε k := fun u => by
    rw [valR_eq x _ hh, Units.coe_prod, map_prod]
    exact Finset.prod_congr rfl fun k _ => (valR_eq x _ hh _).symm.trans (val_zpow x hh _ _)
  refine (A _).trans (Finset.prod_congr rfl fun k _ => ?_)
  exact congrArg (· ^ ε k) (val_res_pull x (φ k) (U := L.U (j k) ⊓ L.U (j' k)) _ hh (L.g (j k) (j' k)))

theorem sec_val {L : LB X} (s : L.Sec) {x : Sp C ⟶ X} {i j : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i)
    (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) : valR x (L.U i) (s.f i) = tv L x i j * valR x (L.U j) (s.f j) := by
  have hh : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) := fun y hy => ⟨hi hy, hj hy⟩
  have e := congrArg (valR x (L.U i ⊓ L.U j)) (s.compat i j)
  rw [valR_mul x _ hh] at e
  exact (valR_res x inf_le_left hh _).symm.trans (e.trans (congrArg _ (valR_res x inf_le_right hh _)))

theorem gen_val {L : LB X} {t : L.Gen} (ht : t.IsGen) {x : Sp C ⟶ X} {i j : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i)
    (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) : valR x (L.U i) (t.s i).val = tv L x i j * valR x (L.U j) (t.s j).val :=
  sec_val ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩ hi hj

end Val

structure IsoVal {K C : Type} [Field K] [Field C] {X H Y : Scheme.{0}} (q : Y ⟶ Sp K) (σ : K →+* C)
    (L : LB X) (M : LB H) (ψ : Y ⟶ X) (j : Y ⟶ H) (ω : (Sp C ⟶ Y) → M.ι → L.ι → C) : Prop where
  ne : ∀ x l m, ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m → ω x l m ≠ 0
  left : ∀ x l l' m, ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l' → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m →
    ω x l m = tv M (x ≫ j) l l' * ω x l' m
  right : ∀ x l m m', ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m' →
    ω x l m * tv L (x ≫ ψ) m m' = ω x l m'
  reg : ∀ (g : Y ⟶ Y) (W : Y.Opens) l m, W ≤ (g ≫ j) ⁻¹ᵁ M.U l → W ≤ (g ≫ ψ) ⁻¹ᵁ L.U m →
    Reg q σ W (fun x => ω (x ≫ g) l m) ∧ Reg q σ W (fun x => (ω (x ≫ g) l m)⁻¹)

theorem exists_isoVal {K C : Type} [Field K] [Field C] {X H Y : Scheme.{0}} (q : Y ⟶ Sp K) (σ : K →+* C)
    {L : LB X} {M : LB H} (hL : L.IsLB) (hM : M.IsLB) {ψ : Y ⟶ X} {j : Y ⟶ H}
    (h : LBIso (L.pull ψ) (M.pull j)) : ∃ ω, IsoVal q σ L M ψ j ω := by
  obtain ⟨w, hw⟩ := h
  have mem : ∀ {x : Sp C ⟶ Y} {l m}, ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m →
      ⊤ ≤ x ⁻¹ᵁ (LB.div (M.pull j) (L.pull ψ)).U (fun _ => l, fun _ => m) := fun hl hm _ hz =>
    ⟨Set.mem_iInter.2 fun _ => hl hz, Set.mem_iInter.2 fun _ => hm hz⟩
  have key : ∀ (x : Sp C ⟶ Y) l l' m m', ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l → ⊤ ≤ (x ≫ j) ⁻¹ᵁ M.U l' →
      ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m → ⊤ ≤ (x ≫ ψ) ⁻¹ᵁ L.U m' →
      valR x _ (w.s (fun _ => l, fun _ => m)).val =
        tv M (x ≫ j) l l' * (tv L (x ≫ ψ) m m')⁻¹ * valR x _ (w.s (fun _ => l', fun _ => m')).val := by
    intro x l l' m m' hl hl' hm hm'
    refine (gen_val hw (mem hl hm) (mem hl' hm')).trans (congrArg (· * _) ?_)
    have hh : ⊤ ≤ x ⁻¹ᵁ ((LB.div (M.pull j) (L.pull ψ)).U (fun _ => l, fun _ => m) ⊓
        (LB.div (M.pull j) (L.pull ψ)).U (fun _ => l', fun _ => m')) :=
      fun _ hz => ⟨mem hl hm hz, mem hl' hm' hz⟩
    refine (valR_mul x _ hh _ _).trans (congrArg₂ (· * ·) ?_ ?_)
    · refine (valR_res x _ hh _).trans ((tv_linComb M _ _ (fun _ => hl) (fun _ => hl')).trans ?_)
      simp
    · rw [← zpow_neg_one, ← zpow_neg_one]
      refine (val_zpow x hh _ _).trans (congrArg (· ^ (-1 : ℤ)) ?_)
      refine (valR_res x _ hh _).trans ((tv_linComb L _ _ (fun _ => hm) (fun _ => hm')).trans ?_)
      simp
  refine ⟨fun x l m => valR x _ (w.s (fun _ => l, fun _ => m)).val,
    fun x l m hl hm => val_unit_ne_zero x (mem hl hm) _, fun x l l' m hl hl' hm => ?_,
    fun x l m m' hl hm hm' => ?_, fun g W l m hl hm => ?_⟩
  · rw [key x l l' m m hl hl' hm hm, tv_self hL hm, inv_one, _root_.mul_one]
  · rw [key x l l m m' hl hl hm hm', tv_self hM hl, _root_.one_mul, mul_right_comm,
      inv_mul_cancel₀ (tv_ne_zero L hm hm'), _root_.one_mul]
  · have e : W ≤ g ⁻¹ᵁ (LB.div (M.pull j) (L.pull ψ)).U (fun _ => l, fun _ => m) := fun _ hz =>
      ⟨Set.mem_iInter.2 fun _ => hl hz, Set.mem_iInter.2 fun _ => hm hz⟩
    exact ⟨Reg.pull g e _, Reg.inv_unit g e _⟩

end GlobalTheory.ZH.FrameNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSumDivThetaConstDotProductMemStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
theorem _root_.GlobalTheory.T.weightSum_div_thetaConst_dotProduct_mem : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.admitted M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) → (∀ z : M.Z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) → ∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N) (k : _) (i : S.J) (z : M.Z), S.supI M ξ ⊆ S.supI M z → ∀ x₀ ∈ S.supI M z, ∀ v ∈ EE.E z, S.FF _ c k / S.th x₀ * ((fun j => algebraMap o Ω (S.proj _ c i j)) ⬝ᵥ v) ∈ M.O z := by
  first | exact @GlobalTheory.ZH.DualSection.ff_div_th_mul_dotProduct_mem | exact GlobalTheory.ZH.DualSection.ff_div_th_mul_dotProduct_mem | (intros; apply GlobalTheory.ZH.DualSection.ff_div_th_mul_dotProduct_mem <;> assumption)
end

