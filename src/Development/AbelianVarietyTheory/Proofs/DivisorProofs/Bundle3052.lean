import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2987
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2984

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarChainRuleHolomorphicPullback
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CxForm.PullChain

variable {n : ℕ}

theorem repr_algebraMap (t : ℂ) (S : Finset (Fin (n + n))) :
    (bas n).repr (algebraMap ℂ (Alt n) t) S = if S = ∅ then t else 0 := by
  rw [Algebra.algebraMap_eq_smul_one, ← bas_empty, map_smul, Module.Basis.repr_self]
  by_cases h : S = ∅ <;> simp [Finsupp.single_apply, h, eq_comm]

theorem delAt_dbarAt_algebraMap (g : V n → ℂ) (v : V n) :
    delAt (fun x => algebraMap ℂ (Alt n) (g x)) v = ∑ a, del g v (coordVec a) • dz a ∧
    dbarAt (fun x => algebraMap ℂ (Alt n) (g x)) v = ∑ a, dbar g v (coordVec a) • dzb a := by
  have h : (fun x => algebraMap ℂ (Alt n) (g x)) = fun x => g x • bas n ∅ := by
    funext x; rw [Algebra.algebraMap_eq_smul_one, bas_empty]
  rw [h]
  constructor
  · unfold delAt
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_smul (T := fun f => del f v (coordVec a)) (by simp) g, bas_empty, mul_smul_comm, mul_one]
  · unfold dbarAt
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_smul (T := fun f => dbar f v (coordVec a)) (by simp) g, bas_empty, mul_smul_comm, mul_one]

theorem differentiableAt_repr_algebraMap {g : V n → ℂ} {v : V n} (hg : DifferentiableAt ℝ g v)
    (S : Finset (Fin (n + n))) : DifferentiableAt ℝ (fun x => (bas n).repr (algebraMap ℂ (Alt n) (g x)) S) v := by
  simp only [repr_algebraMap]
  split_ifs
  exacts [hg, differentiableAt_const _]

theorem delAt_dbarAt_pull_comp (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (β : V n → Alt n) (v : V m)
    (hU : IsOpen U) (hv : v ∈ U) (hτ : DifferentiableOn ℂ τ U)
    (hβ : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (β y) S) (τ v)) :
    delAt (fun x => pull (fderiv ℂ τ x) (β (τ x))) v = pull (fderiv ℂ τ v) (delAt β (τ v)) ∧
    dbarAt (fun x => pull (fderiv ℂ τ x) (β (τ x))) v = pull (fderiv ℂ τ v) (dbarAt β (τ v)) := by
  have hτv : DifferentiableAt ℂ τ v := hτ.differentiableAt (hU.mem_nhds hv)
  have hg : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (β (τ x)) S) v :=
    fun S => (hβ S).comp v (hτv.restrictScalars ℝ)
  have hPd : ∀ S T, DifferentiableAt ℝ (fun x => (bas m).repr (pull (fderiv ℂ τ x) (bas n S)) T) v :=
    fun S T => ((GlobalTheory.T.contDiffOn_repr_pullbackComplexForm_fderiv m n τ U (bas n S) hU hτ T).contDiffAt (hU.mem_nhds hv)).differentiableAt (by simp)
  have hA : ∀ S T, DifferentiableAt ℝ
      (fun x => (bas m).repr (algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S)) T) v :=
    fun S T => differentiableAt_repr_algebraMap (hg S) T
  have hprod : ∀ S T, DifferentiableAt ℝ (fun x => (bas m).repr
      (algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S) * pull (fderiv ℂ τ x) (bas n S)) T) v :=
    fun S => (GlobalTheory.T.contDiffOn_coefficients_complexForm_mul m m (fun x => algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S))
      (fun x => pull (fderiv ℂ τ x) (bas n S))).2 v (hA S) (hPd S)
  have hexp : (fun x => pull (fderiv ℂ τ x) (β (τ x))) = fun x => ∑ S,
      algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S) * pull (fderiv ℂ τ x) (bas n S) := by
    funext x
    conv_lhs => rw [← (bas n).sum_repr (β (τ x))]
    simp only [map_sum, map_smul, Algebra.smul_def, map_mul, AlgHom.commutes]
  have hsum := (GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local m v).2.2.1 (Finset (Fin (n + n))) Finset.univ
    (fun S x => algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S) * pull (fderiv ℂ τ x) (bas n S))
    (fun S _ => hprod S)
  have hL := fun S => GlobalTheory.T.delOperatorAt_dbarOperatorAt_leibniz_of_commute m (fun x => algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S))
    (fun x => pull (fderiv ℂ τ x) (bas n S)) v (algebraMap ℂ (Alt m) ((bas n).repr (β (τ v)) S)) (hA S) (hPd S)
  have hcl := fun S => GlobalTheory.T.delOperator_dbarOperator_pullback_constantForm_holomorphic m n τ U (bas n S) hU hτ v hv
  have hch := fun S => GlobalTheory.T.wirtingerDerivs_comp_holomorphic_pullback_dz m n τ (fun y => (bas n).repr (β y) S) v hτv (hβ S)
  have hfun := fun S => delAt_dbarAt_algebraMap (fun x => (bas n).repr (β (τ x)) S) v
  rw [hexp]
  constructor
  · rw [hsum.1]
    have key : ∀ S, delAt (fun x => algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S) * pull (fderiv ℂ τ x) (bas n S)) v =
        pull (fderiv ℂ τ v) ((∑ a, del (fun y => (bas n).repr (β y) S) (τ v) (coordVec a) • dz a) * bas n S) := by
      intro S
      rw [(hL S).1 (fun a => (Algebra.commutes _ _).symm), (hcl S).1, mul_zero, add_zero, (hfun S).1, (hch S).1,
        map_mul]
    simp only [key, ← map_sum]
    congr 1
    unfold delAt coefwise
    simp only [Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_smul_comm]
    exact Finset.sum_comm
  · rw [hsum.2]
    have key : ∀ S, dbarAt (fun x => algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S) * pull (fderiv ℂ τ x) (bas n S)) v =
        pull (fderiv ℂ τ v) ((∑ a, dbar (fun y => (bas n).repr (β y) S) (τ v) (coordVec a) • dzb a) * bas n S) := by
      intro S
      rw [(hL S).2 (fun a => (Algebra.commutes _ _).symm), (hcl S).2, mul_zero, add_zero, (hfun S).2, (hch S).2,
        map_mul]
    simp only [key, ← map_sum]
    congr 1
    unfold dbarAt coefwise
    simp only [Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_smul_comm]
    exact Finset.sum_comm

end GlobalTheory.CxForm.PullChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarLeibnizEvenFormMul
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm.HolAtlas

theorem del_dbar_even_mul (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (w : A.Pt → Ev n) (β : A.Fld)
    (hw : A.IsForm (GlobalTheory.LineForm.fld A w)) (hβ : A.IsForm β) :
    A.del (GlobalTheory.LineForm.fld A w * β) = A.del (GlobalTheory.LineForm.fld A w) * β + GlobalTheory.LineForm.fld A w * A.del β ∧
    A.dbar (GlobalTheory.LineForm.fld A w * β) = A.dbar (GlobalTheory.LineForm.fld A w) * β + GlobalTheory.LineForm.fld A w * A.dbar β := by
  have hloc : ∀ i, A.loc (GlobalTheory.LineForm.fld A w * β) i =
      fun v => A.loc (GlobalTheory.LineForm.fld A w) i v * A.loc β i v := by
    intro i
    funext v
    unfold HolAtlas.loc
    split_ifs
    · rfl
    · simp
  have hd : ∀ α : A.Fld, A.IsForm α → ∀ (x : A.Pt) (S),
      DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd := fun α hα x S =>
    ((hα.smooth x.1.1 S).contDiffAt ((A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt (by simp)
  have key := fun x : A.Pt => GlobalTheory.T.delOperatorAt_dbarOperatorAt_leibniz_of_commute n (A.loc (GlobalTheory.LineForm.fld A w) x.1.1) (A.loc β x.1.1) x.crd
    (GlobalTheory.LineForm.fld A w x) (hd _ hw x) (hd _ hβ x)
  have hc : ∀ (x : A.Pt) (b : Alt n), b * A.loc (GlobalTheory.LineForm.fld A w) x.1.1 x.crd = GlobalTheory.LineForm.fld A w x * b := by
    intro x b
    rw [A.loc_crd]
    exact Subalgebra.mem_center_iff.1 (w x).2 b
  constructor
  · funext x
    have := (key x).1 fun a => hc x _
    rw [A.loc_crd β x] at this
    simp only [HolAtlas.del, Pi.add_apply, Pi.mul_apply, hloc]
    exact this
  · funext x
    have := (key x).2 fun a => hc x _
    rw [A.loc_crd β x] at this
    simp only [HolAtlas.dbar, Pi.add_apply, Pi.mul_apply, hloc]
    exact this

end GlobalTheory.CxForm.HolAtlas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedChartTransitionsCocycle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.MumDescent.cocycle : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → ∀ (V : J → J → U.left.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ U.left), (∀ (i j : J) (a : ↥(pullback U.hom π)), pullback.fst U.hom π a ∈ V i j ↔ e i a ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ (V i j).toScheme), a ≫ e i = b ≫ e j → v ≫ (V i j).ι = a ≫ pullback.fst _ _ → v ≫ τ i j = b ≫ pullback.fst _ _) → ∀ (i j k : J) (T : Scheme.{0}) (x : T ⟶ (V i j).toScheme) (y : T ⟶ (V i k).toScheme) (w : T ⟶ (V j k).toScheme), x ≫ (V i j).ι = y ≫ (V i k).ι → x ≫ τ i j = w ≫ (V j k).ι → w ≫ τ j k = y ≫ τ i k := by
  intro R _ _ _ _ S X π hπp hπs hS U hU J e he V τ hV hτ i j k T x y w hxy hw
  set pP := pullback.fst U.hom π with hpP

  set O : U.left.Opens := V i j ⊓ V i k with hO
  let m₁ : O.toScheme ⟶ (V i j).toScheme := U.left.homOfLE inf_le_left
  let m₂ : O.toScheme ⟶ (V i k).toScheme := U.left.homOfLE inf_le_right
  have hm₁ : m₁ ≫ (V i j).ι = O.ι := Scheme.homOfLE_ι _ _
  have hm₂ : m₂ ≫ (V i k).ι = O.ι := Scheme.homOfLE_ι _ _

  let FinalForm : (pullback U.hom π).Opens := pP ⁻¹ᵁ O
  let p' : FinalForm.toScheme ⟶ O.toScheme := pP ∣_ O
  have hp' : p' ≫ O.ι = FinalForm.ι ≫ pP := morphismRestrict_ι _ _
  have hsq : IsPullback p' (FinalForm.ι ≫ pullback.snd U.hom π) (O.ι ≫ U.hom) π :=
    (isPullback_morphismRestrict pP O).paste_vert (IsPullback.of_hasPullback U.hom π)
  have hp'surj : Surjective p' := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hπs
  have hZ : ∀ (l : J) (z : FinalForm.toScheme), (FinalForm.ι ≫ e i) z ∈ Set.range (e l) ↔ pP (FinalForm.ι z) ∈ V i l := by
    intro l z; rw [hV]; rfl
  have hZO : ∀ z : FinalForm.toScheme, pP (FinalForm.ι z) ∈ O := by
    intro z
    have : (FinalForm.ι ≫ pP) z ∈ O := by
      rw [← hp']; exact (Scheme.Opens.range_ι O).subset ⟨p' z, rfl⟩
    exact this
  have rj : Set.range (FinalForm.ι ≫ e i) ⊆ Set.range (e j) := by
    rintro _ ⟨z, rfl⟩; exact (hZ j z).2 (hZO z).1
  have rk : Set.range (FinalForm.ι ≫ e i) ⊆ Set.range (e k) := by
    rintro _ ⟨z, rfl⟩; exact (hZ k z).2 (hZO z).2
  let b := IsOpenImmersion.lift (e j) (FinalForm.ι ≫ e i) rj
  let c := IsOpenImmersion.lift (e k) (FinalForm.ι ≫ e i) rk
  have hb : b ≫ e j = FinalForm.ι ≫ e i := IsOpenImmersion.lift_fac _ _ _
  have hc : c ≫ e k = FinalForm.ι ≫ e i := IsOpenImmersion.lift_fac _ _ _

  have h1 : p' ≫ m₁ ≫ τ i j = b ≫ pP :=
    hτ i j _ FinalForm.ι b (p' ≫ m₁) hb.symm (by rw [Category.assoc, hm₁, hp'])
  have h2 : p' ≫ m₂ ≫ τ i k = c ≫ pP :=
    hτ i k _ FinalForm.ι c (p' ≫ m₂) hc.symm (by rw [Category.assoc, hm₂, hp'])

  have rw₀ : Set.range (m₁ ≫ τ i j) ⊆ Set.range (V j k).ι := by
    rintro _ ⟨o, rfl⟩
    obtain ⟨z, rfl⟩ := hp'surj.surj o
    have e1 : (p' ≫ m₁ ≫ τ i j) z = (b ≫ pP) z := by rw [h1]
    have e2 : (b ≫ e j) z = (c ≫ e k) z := by rw [hb, hc]
    simp only [Scheme.Hom.comp_apply] at e1 e2
    rw [Scheme.Opens.range_ι]
    show (m₁ ≫ τ i j) (p' z) ∈ V j k
    simp only [Scheme.Hom.comp_apply]
    rw [e1, hV, e2]
    exact ⟨_, rfl⟩
  let w₀ := IsOpenImmersion.lift (V j k).ι (m₁ ≫ τ i j) rw₀
  have hw₀ : w₀ ≫ (V j k).ι = m₁ ≫ τ i j := IsOpenImmersion.lift_fac _ _ _
  have h3 : p' ≫ w₀ ≫ τ j k = c ≫ pP :=
    hτ j k _ b c (p' ≫ w₀) (hb.trans hc.symm) (by rw [Category.assoc, hw₀, h1])
  haveI := hU
  have heq : pullback.fst p' p' ≫ c ≫ pP = pullback.snd p' p' ≫ c ≫ pP := by
    rw [← h2, pullback.condition_assoc]
  obtain ⟨h₀, -, huniq⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S O.toScheme FinalForm.toScheme U.left π (O.ι ≫ U.hom) p'
    (FinalForm.ι ≫ pullback.snd U.hom π) hπp hπs hS inferInstance hsq (c ≫ pP) heq
  have E : w₀ ≫ τ j k = m₂ ≫ τ i k := (huniq _ h3).trans (huniq _ h2).symm

  have rt : Set.range (x ≫ (V i j).ι) ⊆ Set.range O.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · rw [← Scheme.Opens.range_ι (V i j)]; exact ⟨x s, rfl⟩
    · rw [hxy, ← Scheme.Opens.range_ι (V i k)]; exact ⟨y s, rfl⟩
  let t := IsOpenImmersion.lift O.ι (x ≫ (V i j).ι) rt
  have ht : t ≫ O.ι = x ≫ (V i j).ι := IsOpenImmersion.lift_fac _ _ _
  have tx : t ≫ m₁ = x := (cancel_mono (V i j).ι).1 (by rw [Category.assoc, hm₁, ht])
  have ty : t ≫ m₂ = y := (cancel_mono (V i k).ι).1 (by rw [Category.assoc, hm₂, ht, hxy])
  have tw : w = t ≫ w₀ := (cancel_mono (V j k).ι).1 (by rw [← hw, Category.assoc, hw₀, ← Category.assoc, tx])
  rw [tw, Category.assoc, E, ← Category.assoc, ty]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedCommGroupOfPullbackProperSurjection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescGrp

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {S : Scheme.{0}}
  {π : S ⟶ Sp R}

theorem ext_of_pts (hP : IsProper π) (hS : Surjective π) (hI : IsIntegral S) {Y W : Over (Sp R)} (hY : Flat Y.hom)
    (f₁ f₂ : Y ⟶ W) (h : ∀ (T : Over S) (P : Over.mk (T.hom ≫ π) ⟶ Y), P ≫ f₁ = P ≫ f₂) : f₁ = f₂ := by
  have hpb : IsPullback (pullback.fst Y.hom π) (pullback.snd Y.hom π) Y.hom π := IsPullback.of_hasPullback _ _
  have key : pullback.fst Y.hom π ≫ f₁.left = pullback.fst Y.hom π ≫ f₂.left := by
    have := h (Over.mk (pullback.snd Y.hom π)) (Over.homMk (pullback.fst Y.hom π) pullback.condition)
    simpa using congrArg CommaMorphism.left this
  obtain ⟨h₀, _, hu⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S Y.left (pullback Y.hom π) W.left π Y.hom (pullback.fst Y.hom π)
    (pullback.snd Y.hom π) hP hS hI hY hpb (pullback.fst Y.hom π ≫ f₁.left)
    (by rw [← Category.assoc, ← Category.assoc, pullback.condition])
  ext
  exact (hu _ rfl).trans (hu _ key.symm).symm

variable {G' : Over S} {G : Over (Sp R)} {β : G'.left ⟶ G.left}

def dn (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (x : T ⟶ G') : Over.mk (T.hom ≫ π) ⟶ G :=
  Over.homMk (x.left ≫ β) (by
    change x.left ≫ β ≫ G.hom = T.hom ≫ π
    rw [hpb.w, ← Category.assoc, Over.w x])

def up (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (a : Over.mk (T.hom ≫ π) ⟶ G) : T ⟶ G' :=
  Over.homMk (hpb.lift a.left T.hom (by simpa using Over.w a)) (hpb.lift_snd _ _ _)

theorem dn_up (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (a : Over.mk (T.hom ≫ π) ⟶ G) :
    dn hpb (up hpb a) = a := by
  ext; simp [dn, up]

theorem up_dn (hpb : IsPullback β G'.hom G.hom π) {T : Over S} (x : T ⟶ G') : up hpb (dn hpb x) = x := by
  ext; apply hpb.hom_ext <;> simp [dn, up]

end GlobalTheory.Mum.DescGrp

end

namespace GlobalTheory.Mum.DescGrp

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {S : Scheme.{0}}
  {π : S ⟶ Sp R} {G' : Over S} [GrpObj G'] {G : Over (Sp R)} {β : G'.left ⟶ G.left}

theorem pt_mul (hpb : IsPullback β G'.hom G.hom π) (m : G ⊗ G ⟶ G)
    (hm : ∀ (T : Over S) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β →
      y₀.left = y.left ≫ β → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ β)
    (T : Over S) (a b : Over.mk (T.hom ≫ π) ⟶ G) : lift a b ≫ m = dn hpb (up hpb a * up hpb b) := by
  ext
  rw [hm T (up hpb a) (up hpb b) a b (by simp [up]) (by simp [up])]
  rfl

theorem pt_one (hpb : IsPullback β G'.hom G.hom π) (e : 𝟙_ (Over (Sp R)) ⟶ G)
    (he : ∀ (T : Over S), (toUnit (Over.mk (T.hom ≫ π)) ≫ e).left = (1 : T ⟶ G').left ≫ β) (T : Over S) :
    toUnit (Over.mk (T.hom ≫ π)) ≫ e = dn hpb 1 := by
  ext; rw [he]; rfl

theorem pt_inv (hpb : IsPullback β G'.hom G.hom π) (i : G ⟶ G)
    (hi : ∀ (T : Over S) (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β →
      (x₀ ≫ i).left = x⁻¹.left ≫ β) (T : Over S) (a : Over.mk (T.hom ≫ π) ⟶ G) :
    a ≫ i = dn hpb (up hpb a)⁻¹ := by
  ext; rw [hi T (up hpb a) a (by simp [up])]; rfl

section shapes
variable {G : Over (Sp R)} {T : Over (Sp R)}

theorem sh_assocL (P : T ⟶ (G ⊗ G) ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ (m ▷ G) ≫ m = lift (lift (P ≫ fst _ _ ≫ fst _ _) (P ≫ fst _ _ ≫ snd _ _) ≫ m) (P ≫ snd _ _) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_assocR (P : T ⟶ (G ⊗ G) ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ (α_ G G G).hom ≫ (G ◁ m) ≫ m =
      lift (P ≫ fst _ _ ≫ fst _ _) (lift (P ≫ fst _ _ ≫ snd _ _) (P ≫ snd _ _) ≫ m) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_oneL (P : T ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ (λ_ G).inv ≫ (e ▷ G) ≫ m = lift (toUnit T ≫ e) P ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_oneR (P : T ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ (ρ_ G).inv ≫ (G ◁ e) ≫ m = lift P (toUnit T ≫ e) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_comm (P : T ⟶ G ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ (β_ G G).hom ≫ m = lift (P ≫ snd _ _) (P ≫ fst _ _) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_id (P : T ⟶ G ⊗ G) (m : G ⊗ G ⟶ G) :
    P ≫ m = lift (P ≫ fst _ _) (P ≫ snd _ _) ≫ m := by
  rw [← comp_lift, lift_fst_snd, Category.comp_id]
theorem sh_invL (P : T ⟶ G) (i : G ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ lift i (𝟙 G) ≫ m = lift (P ≫ i) P ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_invR (P : T ⟶ G) (i : G ⟶ G) (m : G ⊗ G ⟶ G) :
    P ≫ lift (𝟙 G) i ≫ m = lift P (P ≫ i) ≫ m := by
  simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp <;> (simp only [← Category.assoc]; congr 1; apply CartesianMonoidalCategory.hom_ext <;> simp)
theorem sh_unit (P : T ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) : P ≫ toUnit G ≫ e = toUnit T ≫ e := by
  rw [← Category.assoc, comp_toUnit]
end shapes

theorem flat_prod2 (G : Over (Sp R)) [Flat G.hom] : Flat (G ⊗ G).hom :=
  inferInstanceAs (Flat (pullback.fst G.hom G.hom ≫ G.hom))
theorem flat_prod3 (G : Over (Sp R)) [Flat G.hom] : Flat ((G ⊗ G) ⊗ G).hom := by
  have := flat_prod2 G
  exact inferInstanceAs (Flat (pullback.fst (G ⊗ G).hom G.hom ≫ (G ⊗ G).hom))

end GlobalTheory.Mum.DescGrp

open GlobalTheory.Mum.DescGrp in

theorem GlobalTheory.Mum.descGrpObj_of_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'] (G : Over (Sp R)) (β : G'.left ⟶ G.left), Smooth G.hom → IsPullback β G'.hom G.hom π → ∀ (m : G ⊗ G ⟶ G) (e : 𝟙_ (Over (Sp R)) ⟶ G) (i : G ⟶ G), (∀ (T : Over S) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → y₀.left = y.left ≫ β → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ β) → (∀ (T : Over S), (toUnit (Over.mk (T.hom ≫ π)) ≫ e).left = (1 : T ⟶ G').left ≫ β) → (∀ (T : Over S) (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ π) ⟶ G), x₀.left = x.left ≫ β → (x₀ ≫ i).left = x⁻¹.left ≫ β) → ∃ (_ : GrpObj G) (_ : IsCommMonObj G), IsGrpPullback G' G π β := by
  intro R _ _ _ _ S π hP hS hI G' _ _ G β hsm hpb m e i hm he hi
  haveI : Smooth G.hom := hsm
  have f1 : Flat G.hom := inferInstance
  have f2 : Flat (G ⊗ G).hom := flat_prod2 G
  have f3 : Flat ((G ⊗ G) ⊗ G).hom := flat_prod3 G
  have hM := pt_mul hpb m hm
  have hE := pt_one hpb e he
  have hI' := pt_inv hpb i hi
  have a1 : e ▷ G ≫ m = (λ_ G).hom := by
    rw [← cancel_epi (λ_ G).inv, Iso.inv_hom_id]
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_oneL, Category.comp_id, hE, hM, up_dn, _root_.one_mul, dn_up]
  have a2 : G ◁ e ≫ m = (ρ_ G).hom := by
    rw [← cancel_epi (ρ_ G).inv, Iso.inv_hom_id]
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_oneR, Category.comp_id, hE, hM, up_dn, _root_.mul_one, dn_up]
  have a3 : m ▷ G ≫ m = (α_ G G G).hom ≫ G ◁ m ≫ m := by
    refine ext_of_pts hP hS hI f3 _ _ (fun T P => ?_)
    rw [sh_assocL, sh_assocR]
    simp only [hM, up_dn, _root_.mul_assoc]
  have a4 : lift i (𝟙 G) ≫ m = toUnit G ≫ e := by
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_invL, sh_unit, hE, hI', hM, up_dn, _root_.inv_mul_cancel]
  have a5 : lift (𝟙 G) i ≫ m = toUnit G ≫ e := by
    refine ext_of_pts hP hS hI f1 _ _ (fun T P => ?_)
    rw [sh_invR, sh_unit, hE, hI', hM, up_dn, _root_.mul_inv_cancel]
  have a6 : (β_ G G).hom ≫ m = m := by
    refine ext_of_pts hP hS hI f2 _ _ (fun T P => ?_)
    rw [sh_comm, sh_id P m, hM, hM]
    letI : CommMonoid (T ⟶ G') := Hom.commMonoid
    rw [_root_.mul_comm]
  letI inst : GrpObj G :=
    { one := e, mul := m, inv := i, one_mul := a1, mul_one := a2, mul_assoc := a3, left_inv := a4,
      right_inv := a5 }
  exact ⟨inst, ⟨a6⟩, hpb, fun T x y x₀ y₀ hx hy => by
    rw [Hom.mul_def]; exact hm T x y x₀ y₀ hx hy⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentTransitionDiagonalInclusionOverBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

set_option maxHeartbeats 1000000 in

theorem descend_transition_diag_over : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R) (f : X ⟶ S), IsProper π → Surjective π → IsIntegral S → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → (∀ j, e j ≫ f = pullback.snd _ _) → ∀ (V : J → J → U.left.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ U.left), (∀ (i j : J) (a : ↥(pullback U.hom π)), pullback.fst U.hom π a ∈ V i j ↔ e i a ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ (V i j).toScheme), a ≫ e i = b ≫ e j → v ≫ (V i j).ι = a ≫ pullback.fst _ _ → v ≫ τ i j = b ≫ pullback.fst _ _) → (∀ i, τ i i = (V i i).ι) ∧ (∀ i j, τ i j ≫ U.hom = (V i j).ι ≫ U.hom) := by
  intro R _ _ _ _ S X π f hprop hsurj hint U hU J e he hef V τ hV hτ

  have hsq : ∀ O : U.left.Opens, IsPullback (pullback.fst U.hom π ∣_ O)
      ((pullback.fst U.hom π ⁻¹ᵁ O).ι ≫ pullback.snd U.hom π) (O.ι ≫ U.hom) π := fun O =>
    (IsPullback.paste_horiz (isPullback_morphismRestrict (pullback.fst U.hom π) O).flip
      (IsPullback.of_hasPullback U.hom π).flip).flip
  have huniq : ∀ (O : U.left.Opens) (W : Scheme.{0}) (g₁ g₂ : O.toScheme ⟶ W),
      (pullback.fst U.hom π ∣_ O) ≫ g₁ = (pullback.fst U.hom π ∣_ O) ≫ g₂ → g₁ = g₂ :=
    fun O W g₁ g₂ h => GlobalTheory.MorDescent.uniq R S O.toScheme _ π (O.ι ≫ U.hom) _ _ hprop hsurj hint
      inferInstance (hsq O) W g₁ g₂ h
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · apply huniq (V i i)
    have := hτ i i _ (pullback.fst U.hom π ⁻¹ᵁ V i i).ι (pullback.fst U.hom π ⁻¹ᵁ V i i).ι
      (pullback.fst U.hom π ∣_ V i i) rfl (morphismRestrict_ι _ _)
    rw [this, morphismRestrict_ι]
  · apply huniq (V i j)
    set Z := pullback.fst U.hom π ⁻¹ᵁ V i j
    have hr : Set.range (Z.ι ≫ e i) ⊆ Set.range (e j) := by
      rintro _ ⟨z, rfl⟩
      have hz : pullback.fst U.hom π (Z.ι z) ∈ V i j := by
        have h0 : Z.ι z = z.1 := Scheme.Opens.ι_apply _ _
        rw [h0]; exact z.2
      exact (hV i j (Z.ι z)).1 hz
    set b := IsOpenImmersion.lift (e j) (Z.ι ≫ e i) hr
    have hb : b ≫ e j = Z.ι ≫ e i := IsOpenImmersion.lift_fac _ _ _
    have h1 := hτ i j _ Z.ι b (pullback.fst U.hom π ∣_ V i j) hb.symm (morphismRestrict_ι _ _)
    have hbs : b ≫ pullback.snd U.hom π = Z.ι ≫ pullback.snd U.hom π := by
      calc b ≫ pullback.snd U.hom π = b ≫ e j ≫ f := by rw [hef]
        _ = Z.ι ≫ e i ≫ f := by rw [← Category.assoc, hb, Category.assoc]
        _ = Z.ι ≫ pullback.snd U.hom π := by rw [hef]
    rw [← Category.assoc, h1, Category.assoc, pullback.condition, ← Category.assoc, hbs,
      Category.assoc, ← pullback.condition, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSchurBilinearEntry
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory

theorem det_schur_bilinear_entry (B : Type) [Fintype B] [DecidableEq B]
    (Q : Matrix (Option B) (Option B) ℂ) (z z' : B → ℂ) (q : ℂ)
    (hq : q = ∑ a, ∑ b, Option.elim a 1 z * Q a b * Option.elim b 1 z') (hq0 : q ≠ 0) :
    (Matrix.of fun a b : B => Q (some a) (some b) / q - (∑ c, Q (some a) c * Option.elim c 1 z') *
      (∑ c, Option.elim c 1 z * Q c (some b)) / q ^ 2).det = Q.det / q ^ (Fintype.card B + 1) := by
  classical
  let e : Option B ≃ B ⊕ Unit := Equiv.optionEquivSumPUnit B
  let R := Matrix.reindex e e Q
  have hR : R.det = Q.det := Matrix.det_reindex_self e Q
  let Pz : Matrix (B ⊕ Unit) (B ⊕ Unit) ℂ := Matrix.fromBlocks 1 0 (Matrix.of fun _ b => z b) 1
  let Pz' : Matrix (B ⊕ Unit) (B ⊕ Unit) ℂ := Matrix.fromBlocks 1 0 (Matrix.of fun _ b => z' b) 1
  have hPz : Pz.det = 1 := by simp [Pz, Matrix.det_fromBlocks_zero₁₂]
  have hPz' : Pz'.det = 1 := by simp [Pz', Matrix.det_fromBlocks_zero₁₂]
  let u : B → ℂ := fun a => ∑ c, Q (some a) c * Option.elim c 1 z'
  let v : B → ℂ := fun b => ∑ c, Option.elim c 1 z * Q c (some b)
  let D : Matrix Unit Unit ℂ := Matrix.of fun _ _ => q
  let M : Matrix (B ⊕ Unit) (B ⊕ Unit) ℂ :=
    Matrix.fromBlocks (Matrix.of fun a b => Q (some a) (some b)) (Matrix.of fun a _ => u a)
      (Matrix.of fun _ b => v b) D
  have hM : M = Pz * R * Pz'ᵀ := by
    ext i j
    rcases i with a | ⟨⟩ <;> rcases j with b | ⟨⟩ <;>
      simp [M, Pz, Pz', R, e, u, v, D, hq, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_option,
        Matrix.one_apply, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc, add_comm]
    all_goals
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hdet : M.det = Q.det := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hPz, hPz', hR]; ring
  letI : Invertible D := ⟨Matrix.of fun _ _ => q⁻¹, by ext; simp [D, Matrix.mul_apply, hq0],
    by ext; simp [D, Matrix.mul_apply, hq0]⟩
  rw [Matrix.det_fromBlocks₂₂] at hdet
  have hD : D.det = q := by simp [D, Matrix.det_unique]
  rw [hD] at hdet
  have hS : (Matrix.of fun a b : B => Q (some a) (some b) / q - (∑ c, Q (some a) c * Option.elim c 1 z') *
      (∑ c, Option.elim c 1 z * Q c (some b)) / q ^ 2) =
      q⁻¹ • ((Matrix.of fun a b => Q (some a) (some b)) - (Matrix.of fun a (_ : Unit) => u a) * ⅟D *
        (Matrix.of fun (_ : Unit) b => v b)) := by
    ext a b
    simp [u, v, D, Matrix.mul_apply, invOf_eq_inv]
    field_simp
  rw [hS, Matrix.det_smul, ← hdet, pow_succ, inv_pow]
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesDescendAlongProperMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCoordinates_descend_along_proper_map : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∃ V : U.left.Opens, x ∈ V ∧ Etale (V.ι ≫ τ) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ b) (V.ι ≫ U.hom) π := by
  first | exact @GlobalTheory.Mum.etale_coord_descend | exact GlobalTheory.Mum.etale_coord_descend | (intros; apply GlobalTheory.Mum.etale_coord_descend <;> assumption)
end

