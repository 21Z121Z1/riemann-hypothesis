import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0070
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0008
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilEqIffHermFormEqComplex
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0034
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0013
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0040
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0046
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaValueComplexPointEqClassicalTheta

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ComponentEqOfMatchedLatticesMarkingsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_eq_of_matched_lattices_markings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → ∀ (W : UW U) (k k' : U.Comp), SameSp (U.X k) (U.X k') → ∀ ga : GL (Fin r) E, IsUn (U.X k) ga → mapL ga (U.X k).Λ = (U.X k').Λ → (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ (U.X k').Λ, (ga : Matrix (Fin r) (Fin r) E) *ᵥ W.mark k a = W.mark k' a + l.M • u) → k = k' := by
  first | exact @GlobalTheory.Dict.comp_eq_of_matched | exact GlobalTheory.Dict.comp_eq_of_matched | (intros; apply GlobalTheory.Dict.comp_eq_of_matched <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormFrameReadingsLinearIndependent
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.Dict

theorem readings_independent :
    ∀ (D : D7) (T : Top D), LawsM T.toCore → ∀ j, InR D j → ∀ a n, JInjRd T j a n := by
  intro D T hM j hj a n

  have hA := GlobalTheory.FramedBaseChange.bcEx_all _ _ _ _ (T.Q.Xo j) T.Q.c T.σ₀
  have hF := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ (T.Q.Xo j) T.Q.c).2.2.2.1
  exact jInjRd_of_wt T hM hj a n hA hF

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSabMapOfIsAH
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Dict.SameFibre

open GlobalTheory.AnVal
open GlobalTheory.UnifPoint

theorem discrete_of_im_int {g : ℕ} (Λ : AddSubgroup (Fin g → ℂ)) (M : Matrix (Fin g) (Fin g) ℂ)
    (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (pos : ∀ z, z ≠ 0 → 0 < (hermForm M z z).re)
    (hi : ∀ a ∈ Λ, ∀ b ∈ Λ, ∃ k : ℤ, (hermForm M a b).im = k) : DiscreteTopology Λ := by
  obtain ⟨s, hs', hsp, hli⟩ := exists_linearIndependent ℝ (Λ : Set (Fin g → ℂ))
  have : Finite s := hli.finite
  choose k hk using hi
  let f : Λ → (s → ℤ) := fun a b => k a a.2 b (hs' b.2)
  have hf : ∀ a b, ((f a b : ℤ) : ℝ) = (hermForm M a b).im := fun a b => (hk _ _ _ _).symm
  refine DiscreteTopology.of_continuous_injective (f := f) (continuous_pi fun b => ?_) fun a a' h => ?_
  · refine Int.isClosedEmbedding_coe_real.isEmbedding.continuous_iff.2 ?_
    have : (Int.cast ∘ fun a => f a b : Λ → ℝ) = fun a : Λ => (hermForm M a b).im := funext fun a => hf a b
    rw [this]
    unfold hermForm
    fun_prop
  · have h0 : ∀ w, (hermForm M (a - a') w).im = 0 := fun w => by
      have hw : w ∈ Submodule.span ℝ s := by rw [hsp, hs]; trivial
      induction hw using Submodule.span_induction with
      | mem w hw =>
        have := hf a ⟨w, hw⟩
        rw [h, hf] at this
        simp only [hermForm, sub_dotProduct, Complex.sub_im] at this ⊢
        rw [this, sub_self]
      | zero => simp [hermForm]
      | add x y _ _ hx hy =>
        simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at hx hy ⊢
        rw [hx, hy, add_zero]
      | smul r x _ hx =>
        rw [← Complex.coe_smul]
        simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
          Complex.star_def, Complex.conj_ofReal, Complex.im_ofReal_mul] at hx ⊢
        rw [hx, mul_zero]
    by_contra hne
    have h1 := pos (a - a') (sub_ne_zero.2 fun e => hne (Subtype.ext e))
    have h2 := h0 (Complex.I • ((a : Fin g → ℂ) - a'))
    simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
      Complex.star_def, Complex.conj_I, neg_mul, Complex.neg_im, Complex.I_mul_im, neg_eq_zero] at h1 h2
    exact h1.ne' h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}

theorem exists_holUnif {S : Scheme.{0}} {t : SAB H S} {y : Sp ℂ ⟶ S} {t₁ : SAB H (Sp ℂ)} (m : SABMap t₁ t y)
    (Φ : AnFr t.G t.PP y g) (pos : ∀ z, z ≠ 0 → 0 < (hermForm Φ.Hm z z).re) :
    ∃ (u : HolUnif t₁.G t₁.PP.L g) (χ : u.Λ → ℂ), (∀ z, z ∈ u.Λ ↔ z ∈ Φ.lat) ∧
      (∀ z, (u.ex z).left ≫ m.φ = (Φ.e z).left) ∧ u.IsAH Φ.Hm χ := by
  obtain ⟨w, hw, -⟩ := m.lin
  obtain ⟨w', hw'⟩ := LBIso.symm ⟨w, hw⟩
  have hL := t₁.PP.isLB
  have hM := pull_isLB t.PP.isLB m.φ
  let u₁ := OrthoMetric.fibreUnif m.cart Φ.e Φ.lat Φ.fr Φ.e_add Φ.e_onto Φ.e_ker
    (discrete_of_im_int Φ.lat Φ.Hm Φ.span pos fun a ha b hb => Φ.herm_im_int ha hb) Φ.span
    (fun U f => by simpa only [Set.mem_univ, true_and] using Φ.hol U f) Φ.fr_hol Φ.fr_ne Φ.fr_g
  have hA₁ : u₁.IsAH Φ.Hm fun a => Φ.χ a :=
    ⟨Φ.herm, pos, fun a => Φ.χ_norm a a.2, fun a j z hj =>
      Φ.fr_per a a.2 _ z ((OrthoMetric.lift_le m.cart _ j).1 hj)⟩
  exact ⟨ArchMetricCompare.carry u₁ hM hL hw', _, fun _ => Iff.rfl, fun z => OrthoMetric.liftPt_comp m.cart _,
    ArchMetricCompare.carry_isAH hM hL hw' hA₁⟩

theorem exists_sabMap_of_isAH {D : Datum H} {l : Geo.Tor.Level H} {b : Base l ℂ} {s : Sp ℂ ⟶ Sp ℂ}
    (o₁ o₂ : Obj D l b s) (u₁ : HolUnif o₁.t.G o₁.t.PP.L g) (u₂ : HolUnif o₂.t.G o₂.t.PP.L g)
    {M₁ M₂ : Matrix (Fin g) (Fin g) ℂ} {χ₁ : u₁.Λ → ℂ} {χ₂ : u₂.Λ → ℂ} (h₁ : u₁.IsAH M₁ χ₁) (h₂ : u₂.IsAH M₂ χ₂)
    (hΛ : ∀ z, z ∈ u₁.Λ ↔ z ∈ u₂.Λ) (hM : ∀ z w, hermForm M₁ z w = hermForm M₂ z w)
    (F : 𝓞 E → (Fin g → ℂ) → (Fin g → ℂ)) (a₁ : ∀ a z, u₁.ex (F a z) = u₁.ex z ≫ o₁.t.act.act a)
    (a₂ : ∀ a z, u₂.ex (F a z) = u₂.ex z ≫ o₂.t.act.act a) :
    ∃ m : SABMap o₁.t o₂.t (𝟙 _), ∀ z, (u₁.ex z).left ≫ m.φ = (u₂.ex z).left := by
  have hT := thetaUnifAV_all
  have hL : Out.Laws := firstFiveLaws.1
  have p₁ := obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ o₁
  have p₂ := obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ o₂
  obtain ⟨E₁, e₁, -, g₁, -, -, w₁⟩ := AHWeil.tangent_and_weil_of_isAH hT (objPol o₁ p₁) g u₁ M₁ χ₁ h₁
  obtain ⟨E₂, e₂, -, g₂, -, -, w₂⟩ := AHWeil.tangent_and_weil_of_isAH hT (objPol o₂ p₂) g u₂ M₂ χ₂ h₂
  obtain ⟨α, hα, hα'⟩ : ∃ α : o₁.t.G ⟶ o₂.t.G, IsMonHom α ∧ ∀ z, u₂.ex z = u₁.ex z ≫ α :=
    exists_isMonHom_of_map_lattice hT hL (objPol o₁ p₁) (objPol o₂ p₂) g u₁ u₂ LinearMap.id g₁.symm g₂.symm
      fun z hz => (hΛ z).1 hz
  obtain ⟨β, -, hβ'⟩ : ∃ β : o₂.t.G ⟶ o₁.t.G, IsMonHom β ∧ ∀ z, u₁.ex z = u₂.ex z ≫ β :=
    exists_isMonHom_of_map_lattice hT hL (objPol o₂ p₂) (objPol o₁ p₁) g u₂ u₁ LinearMap.id g₂.symm g₁.symm
      fun z hz => (hΛ z).2 hz
  have := p₁.1.smooth
  have := p₂.1.smooth
  have := p₁.1.proper
  have := p₂.1.proper
  have : IsReduced o₁.t.G.left := isReduced_of_smooth_complex _ o₁.t.G.hom inferInstance
  have : IsReduced o₂.t.G.left := isReduced_of_smooth_complex _ o₂.t.G.hom inferInstance
  let ψ : o₁.t.G ≅ o₂.t.G :=
    { hom := α
      inv := β
      hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u₁.ex_onto x
        rw [← Category.assoc, ← hα', ← hβ', Category.comp_id]
      inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u₂.ex_onto x
        rw [← Category.assoc, ← hβ', ← hα', Category.comp_id] }
  have hact : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a := fun a =>
    ComplexPoints.over_hom_ext_of_complexPoints fun x => by
      obtain ⟨z, rfl⟩ := u₁.ex_onto x
      rw [← Category.assoc, ← Category.assoc, ← a₁, ← hα', ← hα', ← a₂]
  have hlam := lam_iso_of_weil_pairings hL ℂ (objPol o₁ p₁) (objPol o₂ p₂) α 2 1 hα Nat.prime_two inferInstance
    fun k x y c hk _ hx hy hw => by
      obtain ⟨a, rfl⟩ := CM.HermWeil.exists_eq_ex_div u₁ hk x hx
      obtain ⟨a', rfl⟩ := CM.HermWeil.exists_eq_ex_div u₁ hk y hy
      have w := w₁ k a a' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
      obtain rfl := weilIs_unique_fieldPoint _ _ _ o₁.t.PP.isLB ℂ (𝟙 _) k _ _ _ _ hw w
      have w' := w₂ k ⟨a, (hΛ _).1 a.2⟩ ⟨a', (hΛ _).1 a'.2⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
      have e : E₂ ⟨a, (hΛ _).1 a.2⟩ ⟨a', (hΛ _).1 a'.2⟩ = E₁ a a' := by
        have h := e₁ a a'
        rw [hM, ← e₂ ⟨a, (hΛ _).1 a.2⟩ ⟨a', (hΛ _).1 a'.2⟩] at h
        exact_mod_cast h.symm
      rw [hα', hα', e] at w'
      rw [pow_one]
      exact w'
  have : IsMonHom ψ.hom := hα
  exact ⟨⟨CubeMap.ofHom α, isGrpPullback_of_iso ψ, rfl, fun a => congrArg (fun z => z.left) (hact a),
    HeckePoint.isPullCubical_of_iso hL.globalFns p₁.1 α o₁.t.cub o₂.t.cub
      (HeckePoint.iso_of_lam o₁.t o₂.t α hact hlam)⟩,
    fun z => congrArg (fun q => q.left) (hα' z).symm⟩

end GlobalTheory.Dict.SameFibre

open GlobalTheory.Dict.SameFibre GlobalTheory.UnifPoint GlobalTheory.AnVal in

theorem GlobalTheory.Dict.anFib_point_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ], l.A = 1 → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x L y'), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → A.Marked mk → A'.Marked mk → y'.x = y.x := by
  intro E _ _ _ H Dw l Xo c _ hA r g X bas idx e x L y y' A A' hs hx hL mk _ hm hm'
  obtain ⟨Φ, k₁, -, l₁, m₁, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  obtain ⟨Φ', k₂, -, l₂, m₂, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y' A' hs hx hL
  obtain ⟨-, pos, -⟩ := hx_laws E r X g bas idx 0 hs Even.zero x hx
  let σ : KA l →+* ℂ := (algebraMap c.F ℂ).comp (IntermediateField.inclusion c.le).toRingHom
  have hy : y.x ≫ Xo.s = 𝟙 _ ≫ spMap σ := y.x_over.trans (Category.id_comp _).symm
  have hy' : y'.x ≫ Xo.s = 𝟙 _ ≫ spMap σ := y'.x_over.trans (Category.id_comp _).symm
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H Dw l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) y.x rfl rfl hy Xo.univ
  obtain ⟨o₂, ⟨n₂⟩⟩ := obj_pull E H Dw l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) y'.x rfl rfl hy' Xo.univ
  obtain ⟨u₁, χ₁, b₁, f₁, h₁⟩ := exists_holUnif n₁.toSABMap Φ.toAnFr fun z hz => by rw [m₁]; exact pos z hz
  obtain ⟨u₂, χ₂, b₂, f₂, h₂⟩ := exists_holUnif n₂.toSABMap Φ'.toAnFr fun z hz => by rw [m₂]; exact pos z hz
  obtain ⟨m, hm₀⟩ := exists_sabMap_of_isAH o₁ o₂ u₁ u₂ h₁ h₂ (fun z => by rw [b₁, b₂, l₁, l₂])
    (fun z w => by rw [m₁, m₂]) (fun a => tyAct (fun j => rowType X (idx j)) a)
    (fun a z => OrthoMetric.pt_ext n₁.cart (by
      rw [f₁, Φ.lin, Over.comp_left, Over.comp_left, Category.assoc, n₁.act, ← Category.assoc, f₁]))
    (fun a z => OrthoMetric.pt_ext n₂.cart (by
      rw [f₂, Φ'.lin, Over.comp_left, Over.comp_left, Category.assoc, n₂.act, ← Category.assoc, f₂]))
  obtain ⟨k⟩ := exists_objMap o₁ o₂ m
    (fun a ha => by
      have c₁ : o₁.eta a = u₁.ex _ := OrthoMetric.pt_ext n₁.cart
        ((n₁.eta a).trans ((congrArg (fun q => q.left) ((hm a ha).trans (k₁ _).symm)).trans (f₁ _).symm))
      have c₂ : o₂.eta a = u₂.ex _ := OrthoMetric.pt_ext n₂.cart
        ((n₂.eta a).trans ((congrArg (fun q => q.left) ((hm' a ha).trans (k₂ _).symm)).trans (f₂ _).symm))
      rw [c₁, c₂, hm₀])
    (fun a => by
      have c₁ := o₁.etaA_ker a
      have c₂ := o₂.etaA_ker a
      rw [hA, one_smul] at c₁ c₂
      rw [c₁, c₂, ← CM.HermWeil.ex_zero u₁, ← CM.HermWeil.ex_zero u₂, hm₀])
  obtain ⟨k', -⟩ := ((ObjMaps.id_comp_cancel E H Dw l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2 y'.x (𝟙 _) n₂).1 k
  rw [Category.id_comp] at k'
  exact (moduli_rep_of_base ObjMaps.id_comp_cancel E H Dw l Xo ℂ (baseOfEmb σ) σ _ (𝟙 _) o₁ inferInstance
    rfl rfl).unique ⟨hy', ⟨k'⟩⟩ ⟨hy, ⟨n₁⟩⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTrivialAtLevelUnitaryTransportSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerOntoStd

open GlobalTheory.AdelTranslate GlobalTheory.AdLat GlobalTheory.UnRep

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem glue_map (c : E ≃ₐ[F] E) (e : FiniteAdeleRing (𝓞 F) F) (γ : Matrix (Fin n) (Fin n) E) :
    (glue e γ).map (sg (FiniteAdeleRing (𝓞 F) F) c) = glue e (γ.map c) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [glue, fm, sg]
  · simp [glue, fm, sg, Matrix.one_apply_ne h]

theorem mul_glue_sub_one {e α : FiniteAdeleRing (𝓞 F) F} (h : α * e = 0) (γ : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    (α ⊗ₜ[F] (1 : E) : RA F E) * (glue e γ - 1) i j = 0 := by
  have h0 : (α ⊗ₜ[F] (1 : E) : RA F E) * (e ⊗ₜ[F] (1 : E)) = 0 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, h, TensorProduct.zero_tmul]
  simp only [glue, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (fm F γ i j - (1 : Matrix (Fin n) (Fin n) (RA F E)) i j) * h0

theorem mul_idem_eq_zero {k M : ℕ} (hk : k.Coprime M) {v : HeightOneSpectrum (𝓞 F)} (hv : (M : 𝓞 F) ∈ v.asIdeal)
    {α : FiniteAdeleRing (𝓞 F) F} (hα : ∀ v', v' ≠ v → α v' = 0) : α * idem F k = 0 := by
  refine DFunLike.ext _ _ fun w => ?_
  change α w * idem F k w = 0
  by_cases h : w = v
  · subst h
    rw [idem_apply, if_neg, mul_zero]
    intro hk'
    obtain ⟨a, b, hab⟩ : IsCoprime (k : 𝓞 F) (M : 𝓞 F) := Nat.Coprime.cast hk
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ add_mem (w.asIdeal.mul_mem_left a hk') (w.asIdeal.mul_mem_left b hv)))
  · rw [hα w h, zero_mul]

end General

theorem finPart_cA (D : D7) (x : AE D) :
    finPart D (cA D x) = sg (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (GlobalTheory.Member.cF D) (finPart D x) :=
  GlobalTheory.UnitarySplit.map_sig (sndA D.host.F) D.sp.cm.sig x

set_option maxHeartbeats 1000000 in

theorem exists_trivAt_isMov : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ M : ℕ, 0 < M → ∀ Λ ∈ Vset D.host.E S.rank M, ∃ h ∈ GfC S, TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h ∧ IsMov (fmtC S h) (stdL D.host.E S.rank) Λ := by
  rintro D S T C M - Λ ⟨-, hU', k, hk0, hkM, h1, h2⟩
  have hU : (⟨Λ⟩ : GenLat D.host.E S.rank).Unimod := (GlobalTheory.Dict.GenLatCmp.unimod_iff Λ).2 hU'
  have h₁ : ∀ x ∈ Λ, k • x ∈ stdL D.host.E S.rank := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul D.host.E]; exact h1 x hx
  have h₂ : ∀ x ∈ stdL D.host.E S.rank, k • x ∈ Λ := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul D.host.E]; exact h2 x hx
  obtain ⟨k', γ, hk', hγ, h₃, h₄⟩ := GlobalTheory.AdaptUnitary.exists_unitary_adapted D.host.E (hostOfRecord D) S.rank ⟨Λ⟩ k hU hk0
    (by rw [GlobalTheory.Dict.GenLatCmp.std_eq, span_smul_le_iff]; exact h₂) k hk0
  rw [GlobalTheory.Dict.GenLatCmp.std_eq] at h₃ h₄
  set c := GlobalTheory.Member.cF D with hc
  have c2 : ∀ x, c (c x) = x := fun x => star_star x
  set δ : Matrix (Fin S.rank) (Fin S.rank) D.host.E := (γ.map c)ᵀ with hδ
  have hδγ : δ * γ = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply, ← hγ i j]
    rfl
  have hγδ : γ * δ = 1 := mul_eq_one_comm.1 hδγ
  have hδc : γᵀ.map c = δ := rfl
  have h₅ : ∀ x ∈ stdL D.host.E S.rank, k' • δ *ᵥ x ∈ Λ := fun x hx => by
    obtain ⟨w, hw, e⟩ := h₄ x hx
    rwa [← Nat.cast_smul_eq_nsmul D.host.E, ← Matrix.mulVec_smul, e, Matrix.mulVec_mulVec, hδγ, Matrix.one_mulVec]
  have h₆ : ∀ x ∈ Λ, k' • γ *ᵥ x ∈ stdL D.host.E S.rank := fun x hx => by
    rw [← Nat.cast_smul_eq_nsmul D.host.E]
    exact h₃ x hx
  have he := idem_mul (F := D.host.F) k
  have t1 : γᵀ * δᵀ = 1 := by rw [← Matrix.transpose_mul, hδγ, Matrix.transpose_one]
  have t2 : δᵀ * γᵀ = 1 := by rw [← Matrix.transpose_mul, hγδ, Matrix.transpose_one]
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D S
  obtain ⟨h, hh, eh⟩ := lift ⟨glue (idem _ k) γᵀ, glue (idem _ k) δᵀ, glue_mul he t1, glue_mul he t2⟩ (by
    rw [C.m.gS, Matrix.transpose_one]
    refine isUnA_of c ?_
    change ((glue (idem _ k) γᵀ).map _)ᵀ * glue (idem _ k) γᵀ = 1
    rw [glue_map_sg, hδc]
    exact glue_mul he t2)
  have e1 : fmt S h = glue (idem _ k) γᵀ := congrArg Units.val eh
  have e2 : fmtC S h = glue (idem _ k) δ := by
    rw [← hδc, ← glue_map, ← e1]
    ext i j
    exact finPart_cA D _
  refine ⟨h, hh, ?_, ?_⟩
  · rintro v hv ε ⟨α, rfl, -, hα⟩ i j
    have hM : (M : 𝓞 D.host.F) ∈ v.asIdeal := hv (Ideal.mem_span_singleton_self _)
    apply GlobalTheory.UnitarySplit.parts_inj D
    · rw [map_mul, map_zero]
      have : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
        change ((0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
        exact TensorProduct.zero_tmul _ _
      rw [this, zero_mul]
    · rw [map_mul, map_zero]
      have : finPart D ((mt S h - 1) i j) = (fmt S h - 1) i j := by
        rw [Matrix.sub_apply, Matrix.sub_apply, (finPart D).map_sub]
        congr 1
        by_cases hij : i = j
        · subst hij
          rw [Matrix.one_apply_eq, Matrix.one_apply_eq, (finPart D).map_one]
        · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, (finPart D).map_zero]
      rw [this, e1]
      exact mul_glue_sub_one (mul_idem_eq_zero hkM hM hα) _ i j
  · rw [e2]
    intro u
    constructor
    · intro hu
      refine ⟨_, glue_mem_hat (F := D.host.F) hk' h₆ h₁ u hu, ?_⟩
      rw [Matrix.mulVec_mulVec, glue_mul he hδγ, Matrix.one_mulVec]
    · rintro ⟨z, hz, ez⟩
      rw [ez]
      exact glue_mem_hat (F := D.host.F) hk' h₅ h₂ z hz

end GlobalTheory.KerOntoStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IteratedFDerivSmulAll
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ShortPt

theorem iteratedFDeriv_smul_all {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (a : ℂ) (F : W → ℂ) (k : ℕ) :
    iteratedFDeriv ℂ k (a • F) = a • iteratedFDeriv ℂ k F := by
  induction k with
  | zero => ext x m; simp
  | succ k ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, ih, fderiv_const_smul_field]
    funext x
    simp only [Function.comp_apply, Pi.smul_apply, map_smul]

theorem theta_smul₂ {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} (X : Data E r)
    (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (a : ℂ) (φ : TF n g)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (x : Frame X.Ψ r) :
    thP X hr bas idx (a • φ) P x = a * thP X hr bas idx φ P x := by
  have h : thA X bas idx (a • φ) x = a • thA X bas idx φ x := by
    funext z
    simp only [thA, SW.thS, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc a, tsum_mul_left]
    ring
  unfold thP I2.polyDeriv
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_smul_all]
  simp only [Pi.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem finite_levQ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
    (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have hp := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at hp
    have := l.three_le
    omega
  haveI : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  haveI := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem vset_one {E : Type} [Field E] [NumberField E] [IsCMField E] {n M : ℕ} {Λ : Lt E n}
    (h : Λ ∈ Vset E n M) : Λ ∈ Vset E n 1 := by
  obtain ⟨h1, h2, s, hs, -, h3⟩ := h
  exact ⟨h1, h2, s, hs, Nat.coprime_one_right s, h3⟩

theorem shortRule_value : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → (∀ y₂ : FrPt d.Xo₂ d.c₂ ℂ, ‖evR d.Xo₂ d.c₂ d.cδ y₂‖ = 1) → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ (r g q0 : ℕ) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ) (Dc : Dic Dw c (algebraMap c.F ℂ) X g q0 n a) (D : SW.Level X) (hn : r ≤ n), Even n → r = Dw.p + Dw.q → LevTie d (algebraMap c.F ℂ) ph D hn → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X Dc.bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ x0 : Fin n → Dw.La, ∃ u : Lt E n → ℕ → ℂ, (∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → u Λ N ≠ 0) ∧ ∀ L ∈ D.lats, ∀ mk δ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → IsDual X l (algebraMap c.F ℂ (zetaM c)) L mk δ → IsBaseClassLevelAdapted d D hn x0 δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ X.dom, IsUnitFr X x → ∀ (y : FrPt Xo c ℂ) (A : AnFib X Dc.bas Dc.idx Dc.e x L y) (θ : (Fin g → ℂ) → ℂ), A.Marked mk → A.Reads 1 y.s θ → MeanOne X Dc.bas Dc.idx x L θ → ∃ κ : ℂ, ‖κ‖ = ρ ∧ ∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ f : Rul Xo c, IsShortRule Xo c d (⟨Λ⟩ : GenLat E n) N x0 P f → evR Xo c f y = κ * u Λ N * thP X Dc.hr Dc.bas Dc.idx (phiF Dc.bas D (Mfr l) hn v₀ L Λ) (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)) x := by
  intro hCI E _ _ _ H Dw l Xo c n d _ _ hcomp hlev hnab hcδ ph ψ x₀ hpin r g q0 X a Dc D hn hev hr htie v₀ hv₀ x0
  obtain ⟨_, hnab⟩ := hnab
  obtain ⟨ρ₁, s, hρ₁, hg⟩ := GlobalTheory.Dict.GPhi.gphi_eq_smul_phiF E H Dw l Xo c n d hcomp hlev ph ψ x₀ hpin r g X Dc.bas Dc.idx D hn
    Dc.sympl hev hr htie v₀ hv₀ x0
  have hwi : IsIntegral ℤ (H.w0 : E) := htie.w ▸ D.w_int
  have hwt : (H.w0 : E) + cc (H.w0 : E) = 1 := htie.w ▸ D.w_tr
  have hΛ0 : SelfD X X.Λ := (GlobalTheory.SW.level_laws E r X g Dc.bas Dc.idx n Dc.sympl hev D hn).1.1
  refine ⟨fun Λ N => algebraMap d.c₂.F ℂ ((d.eF (betaH (Dw := Dw) c (⟨Λ⟩ : GenLat E n)))⁻¹ *
      (((⟨Λ⟩ : GenLat E n).mIdx N r : d.c₂.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw d.l₂) : d.c₂.F))⁻¹ *
      ((⟨Λ⟩ : GenLat E n).zCard N r : d.c₂.F)) * (((if 0 < s Λ then s Λ else 1 : ℝ)) : ℂ), ?_, ?_⟩
  · intro Λ hΛ N hN
    obtain ⟨-, -, -, hz, hm, -⟩ := GlobalTheory.Dict.ZLat.exists_reps_sum E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt
      X.Λ hΛ0 Λ (vset_one hΛ) N hN.1 (hN.2.2.trans inf_le_left)
    haveI := finite_levQ Dw d.l₂
    have hb : betaH (Dw := Dw) c (⟨Λ⟩ : GenLat E n) ≠ 0 := by
      unfold betaH
      split_ifs with h
      · exact h.choose_spec.1
      · exact one_ne_zero
    have hc : 0 < Nat.card (Fin n → LevQ Dw d.l₂) := Nat.card_pos
    refine mul_ne_zero ((_root_.map_ne_zero _).2 ?_) ?_
    · refine mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero ?_) (inv_ne_zero ?_)) (inv_ne_zero ?_)) ?_
      · exact (_root_.map_ne_zero _).2 hb
      · exact Nat.cast_ne_zero.2 hm.ne'
      · exact Nat.cast_ne_zero.2 hc.ne'
      · exact Nat.cast_ne_zero.2 hz.ne'
    · rw [Complex.ofReal_ne_zero]
      split_ifs with h
      · exact h.ne'
      · exact one_ne_zero
  intro L hL mk δ hmk hδ hx0
  have hLs : SelfD X L := hL.1
  obtain ⟨v, hv⟩ := (GlobalTheory.SW.TensVac.vacua E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt L hLs 1 _
    (Base.stdL_mem_Vset (E := E) n 1)).1
  obtain ⟨ρ₀, hρ₀, hnorm⟩ := GlobalTheory.Dict.VacNorm.norm_factor_eq E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt L hLs v hv
  refine ⟨ρ₀ * ρ₁, mul_pos hρ₀ hρ₁, ?_⟩
  intro x hx hux y A θ hA hθ hmean
  obtain ⟨y₂, hy₂⟩ := hlev.2.2.2.2.2.2.1 ℂ hcomp y
  obtain ⟨A₂, hA₂, mk₂, hmk₂, hA₂m, hover⟩ := GlobalTheory.Dict.Lift.anFib_lift E H Dw l Xo c n d hcomp hlev r g X Dc.bas Dc.idx Dc.e x L y A
    Dc.sympl hx hLs y₂ hy₂ mk hA
  have hth := GlobalTheory.Dict.isTheta1_of_reads_generator E H Dw l Xo c r g X Dc.bas Dc.idx Dc.e x L y A Dc.sympl hx hLs θ hθ
  obtain ⟨κ₀, hκ₀⟩ := GlobalTheory.Dict.VacProd.prod_eq_mul_thA E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt L hLs v hv x hx θ hth
  obtain ⟨t, ht, hgt⟩ := hg L hL mk mk₂ δ v hmk hmk₂ hover hδ hx0 hv
  refine ⟨evR d.Xo₂ d.c₂ d.cδ y₂ * κ₀ * t, ?_, ?_⟩
  · rw [norm_mul, norm_mul, hcδ y₂, hnorm x hx hux θ κ₀ hth hmean hκ₀, ht, _root_.one_mul]
  intro Λ hΛ N hN P hP f hf
  obtain ⟨hs, hgt⟩ := hgt Λ hΛ
  have hM : d.l₂.M ≠ 0 := by have := d.l₂.three_le; omega
  obtain ⟨Y, hY⟩ := (GlobalTheory.Dict.DualMark.dual_marking E H Dw d.l₂ r X L mk₂ _ hLs hmk₂ (Complex.isPrimitiveRoot_exp _ hM)).2.2.2.2 n N
    hN.1.pos
  obtain ⟨v0, hv0, hfv⟩ := hf ℂ hcomp y y₂ hy₂
  have hval := GlobalTheory.Dict.shortValAt_eq_thP hCI E H Dw d.l₂ d.Xo₂ d.c₂ r g X Dc.bas Dc.idx Dc.e x L y₂ A₂ Dc.sympl hx hLs q0 n Dc.hr
    Dc.eL hr hev Dc.dir_eq d.nab₂ hnab θ v κ₀ (hA₂ θ hθ) hv hκ₀ mk₂ hmk₂ hA₂m Λ hΛ N hN Y hY a _
    ((GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a P hP) _ _ v0 hv0
  have hmap : MvPolynomial.map (algebraMap d.c₂.F ℂ) (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) =
      MvPolynomial.map (algebraMap c.F ℂ) P := by
    rw [MvPolynomial.map_map]
    congr 2
    exact RingHom.ext hcomp
  rw [hgt N hN Y hY, theta_smul₂, hmap] at hval
  beta_reduce
  rw [hfv, hval, if_pos hs]
  ring

end GlobalTheory.Dict.ShortPt
end

