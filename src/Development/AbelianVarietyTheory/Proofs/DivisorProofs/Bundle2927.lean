import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2743
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2822
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0044
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0175
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0178
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2824
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2825
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0084
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2853
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1836
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomMumfordGeneratorAdditiveCubicalStructures
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

namespace GlobalTheory.HomMumAdd

variable {S : Scheme.{0}}

theorem prod_mumford {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} (x y : T ⟶ G) {U : Type} [CommGroup U]
    (h : (T.left ⟶ G.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h ((lift x y).left ≫ (psum G (x2 G) I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ G).left := by
  have e : ∀ I : ULift.{0} (Finset (Fin 2)), (lift x y).left ≫ (psum G (x2 G) I.down).left =
      (psum G ![x, y] I.down).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) (x2 G) I.down).trans
      (congrArg (fun q => psum G q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => h (psum G ![x, y] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    (fun I => congrArg (fun q => h q ^ ((-1 : ℤ) ^ (2 - I.down.card))) (e I))).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have p₀ : psum G ![x, y] ∅ = 1 := rfl
  have p₁ : psum G ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y] {1} = y := _root_.mul_one y
  have p₄ : psum G ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  rw [p₀, p₁, p₂, p₄]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₄ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₄]
  simp only [zpow_neg, zpow_one]
  ac_rfl

variable {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂]

theorem prod_pair (a b : H₁ ⟶ H₂) {T : Over S} (x y : T ⟶ H₁) {U : Type} [CommGroup U]
    (h : (T.left ⟶ H₁.left ⨿ H₂.left) → U) :
    ∏ I : MK, h ((lift x y).left ≫ mφ H₁ H₂ a b I) ^ mε I =
      (h (((x ≫ a) * (y ≫ b)).left ≫ coprod.inr) * (h ((x ≫ a).left ≫ coprod.inr))⁻¹ *
        (h ((y ≫ b).left ≫ coprod.inr))⁻¹ * h ((1 : T ⟶ H₂).left ≫ coprod.inr)) *
      (h ((x * y).left ≫ coprod.inl) * (h (x.left ≫ coprod.inl))⁻¹ * (h (y.left ≫ coprod.inl))⁻¹ *
        h ((1 : T ⟶ H₁).left ≫ coprod.inl))⁻¹ := by
  refine prod_sum₂ _ ?_ ?_
  · refine Eq.trans (Finset.prod_congr rfl fun I _ => ?_)
      (prod_mumford (x ≫ a) (y ≫ b) fun q => h (q ≫ coprod.inr))
    have e : lift x y ≫ lift (fst H₁ H₁ ≫ a) (snd H₁ H₁ ≫ b) = lift (x ≫ a) (y ≫ b) := by
      rw [comp_lift, lift_fst_assoc, lift_snd_assoc]
    refine congrArg (fun q => h q ^ ((-1 : ℤ) ^ (2 - I.down.card))) ?_
    rw [← e, Over.comp_left, Category.assoc, Category.assoc]
    rfl
  · refine Eq.trans ?_ (congrArg (·⁻¹) (prod_mumford x y fun q => h (q ≫ coprod.inl)))
    refine Eq.trans (Finset.prod_congr rfl fun I _ => ?_) (Finset.prod_inv_distrib _)
    refine (zpow_neg _ _).trans (congrArg (fun q => (h q ^ ((-1 : ℤ) ^ (2 - I.down.card)))⁻¹) ?_)
    exact (Category.assoc _ _ _).symm

theorem pair_add_of_surj : ∀ {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] {L₁ : RigLB H₁} {L₂ : RigLB H₂} (c₁ : CubicalStr H₁ L₁) (c₂ : CubicalStr H₂ L₂), (join L₁.L L₂.L).IsLB → Function.Surjective (H₁ ⊗ H₁ ⊗ H₁).hom.appTop.hom → ∀ (a b : H₁ ⟶ H₂) [IsMonHom a] [IsMonHom b] (u : LB.Gen (LB.LinComb (join L₁.L L₂.L) (mφ H₁ H₂ a b) mε)), IsNrm u → ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ H₁.left ⨿ H₂.left) → (join L₁.L L₂.L).ι), Good (join L₁.L L₂.L) z J → ∀ x x' y : T ⟶ H₁, val u (lift (x * x') y).left z J * cubV c₁ z (rl J) x x' y = cubV c₂ z (rr J) (x ≫ a) (x' ≫ a) (y ≫ b) * (val u (lift x y).left z J * val u (lift x' y).left z J) ∧ val u (lift y (x * x')).left z J * cubV c₁ z (rl J) y x x' = cubV c₂ z (rr J) (y ≫ a) (x ≫ b) (x' ≫ b) * (val u (lift y x).left z J * val u (lift y x').left z J) := by
  intro S H₁ H₂ _ _ _ _ L₁ L₂ c₁ c₂ hL sj f g _ _ u hu T z J hJ x x' y
  let p₀ := x3 H₁ 0
  let p₁ := x3 H₁ 1
  let p₂ := x3 H₁ 2
  have mf : ∀ {T : Over S} (a b : T ⟶ H₁), (a * b) ≫ f = (a ≫ f) * (b ≫ f) := fun a b => MonObj.mul_comp a b f
  have mg : ∀ {T : Over S} (a b : T ⟶ H₁), (a * b) ≫ g = (a ≫ g) * (b ≫ g) := fun a b => MonObj.mul_comp a b g
  have P₁ := isPart_inl L₁.L L₂.L
  have P₂ := isPart_inr L₁.L L₂.L
  have vp : ∀ {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J}, Good (join L₁.L L₂.L) z J → ∀ a b : T ⟶ H₁,
      val (LB.pullGen (join L₁.L L₂.L) _ _ u (lift a b).left) ρ.left z J = val u (lift (ρ ≫ a) (ρ ≫ b)).left z J :=
    fun ρ z J hJ a b => by rw [val_pull hJ, ← Over.comp_left, comp_lift]
  let e : 𝟙_ (Over S) ⟶ G3 H₁ := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have he : e.left ≫ (H₁ ⊗ H₁ ⊗ H₁).hom = 𝟙 _ := Over.w e
  let ρ : T ⟶ G3 H₁ := lift x (lift x' y)
  have r₀ : ρ ≫ p₀ = x := by simp [ρ, p₀, x3]
  have r₁ : ρ ≫ p₁ = x' := by simp [ρ, p₁, x3]
  have r₂ : ρ ≫ p₂ = y := by simp [ρ, p₂, x3]
  have gen : ∀ (a b a₁ b₁ a₂ b₂ k₁ k₂ k₃ : G3 H₁ ⟶ H₁) (l₁ l₂ l₃ : G3 H₁ ⟶ H₂),
      (∀ (V : Type) [CommGroup V] (k : (G3 H₁ ⟶ H₁) → V) (l : (G3 H₁ ⟶ H₂) → V),
        (l (l₁ * l₂ * l₃) * (l (l₁ * l₂))⁻¹ * (l (l₁ * l₃))⁻¹ * (l (l₂ * l₃))⁻¹ * l l₁ * l l₂ * l l₃ * (l 1)⁻¹) *
          (((l ((a₁ ≫ f) * (b₁ ≫ g)) * (l (a₁ ≫ f))⁻¹ * (l (b₁ ≫ g))⁻¹ * l 1) *
              (k (a₁ * b₁) * (k a₁)⁻¹ * (k b₁)⁻¹ * k 1)⁻¹) *
            ((l ((a₂ ≫ f) * (b₂ ≫ g)) * (l (a₂ ≫ f))⁻¹ * (l (b₂ ≫ g))⁻¹ * l 1) *
              (k (a₂ * b₂) * (k a₂)⁻¹ * (k b₂)⁻¹ * k 1)⁻¹)) =
        ((l ((a ≫ f) * (b ≫ g)) * (l (a ≫ f))⁻¹ * (l (b ≫ g))⁻¹ * l 1) *
              (k (a * b) * (k a)⁻¹ * (k b)⁻¹ * k 1)⁻¹) *
          (k (k₁ * k₂ * k₃) * (k (k₁ * k₂))⁻¹ * (k (k₁ * k₃))⁻¹ * (k (k₂ * k₃))⁻¹ * k k₁ * k k₂ * k k₃ * (k 1)⁻¹)) →
      e ≫ a = 1 → e ≫ b = 1 → e ≫ a₁ = 1 → e ≫ b₁ = 1 → e ≫ a₂ = 1 → e ≫ b₂ = 1 → e ≫ k₁ = 1 → e ≫ l₁ = 1 →
      val u (lift (ρ ≫ a) (ρ ≫ b)).left z J * cubV c₁ z (rl J) (ρ ≫ k₁) (ρ ≫ k₂) (ρ ≫ k₃) =
        cubV c₂ z (rr J) (ρ ≫ l₁) (ρ ≫ l₂) (ρ ≫ l₃) *
          (val u (lift (ρ ≫ a₁) (ρ ≫ b₁)).left z J * val u (lift (ρ ≫ a₂) (ρ ≫ b₂)).left z J) := by
    intro a b a₁ b₁ a₂ b₂ k₁ k₂ k₃ l₁ l₂ l₃ hF ha hb ha₁ hb₁ ha₂ hb₂ hk hl
    have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 H₁) {z : T'.left} {J}, Good (join L₁.L L₂.L) z J →
        val (LB.mulGen (join L₁.L L₂.L) _ _ _ _ (LB.pullGen (join L₁.L L₂.L) _ _ u (lift a b).left)
          (P₁.gen (LB.pullGen L₁.L (thφ H₁ (x3 H₁)) thε c₁.t (lift k₁ (lift k₂ k₃)).left))) σ.left z J =
          val u (lift (σ ≫ a) (σ ≫ b)).left z J * cubV c₁ z (rl J) (σ ≫ k₁) (σ ≫ k₂) (σ ≫ k₃) ∧
        val (LB.mulGen (join L₁.L L₂.L) _ _ _ _
          (P₂.gen (LB.pullGen L₂.L (thφ H₂ (x3 H₂)) thε c₂.t (lift l₁ (lift l₂ l₃)).left))
          (LB.mulGen (join L₁.L L₂.L) _ _ _ _ (LB.pullGen (join L₁.L L₂.L) _ _ u (lift a₁ b₁).left)
            (LB.pullGen (join L₁.L L₂.L) _ _ u (lift a₂ b₂).left)))
          σ.left z J = cubV c₂ z (rr J) (σ ≫ l₁) (σ ≫ l₂) (σ ≫ l₃) *
            (val u (lift (σ ≫ a₁) (σ ≫ b₁)).left z J * val u (lift (σ ≫ a₂) (σ ≫ b₂)).left z J) := fun σ z J hJ =>
      ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _)
          ((P₁.val_gen _ _ z hJ).trans (val_cub c₁ σ (P₁.good hJ) _ _ _))),
        (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((P₂.val_gen _ _ z hJ).trans (val_cub c₂ σ (P₂.good hJ) _ _ _))
          ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (vp σ hJ _ _))))⟩
    refine (ev ρ hJ).1.symm.trans (Eq.trans (gen_unique' hL (fun V _ k => ?_) _ e.left he sj
      (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu.1 _) (P₁.gen_isGen (pullGen_isGen _ _ _ _ c₁.isGen _)))
      (mulGen_isGen _ _ _ _ _ _ _ (P₂.gen_isGen (pullGen_isGen _ _ _ _ c₂.isGen _)) (mulGen_isGen _ _ _ _ _ _ _
        (pullGen_isGen _ _ _ _ hu.1 _) (pullGen_isGen _ _ _ _ hu.1 _))) (fun y I hI => ?_) _ ρ.left z J hJ) (ev ρ hJ).2)
    · exact (prod_sum₂ (K := thK) (K' := MK ⊕ MK) (U := V) _ (prod_cub l₁ l₂ l₃ fun q => k (q ≫ coprod.inr))
        (prod_sum₂ (K := MK) (K' := MK) (U := V) _ (prod_pair f g a₁ b₁ k) (prod_pair f g a₂ b₂ k))).trans
        ((hF V (fun q => k (q.left ≫ coprod.inl)) (fun q => k (q.left ≫ coprod.inr))).trans
          (prod_sum₂ (K := MK) (K' := thK) (U := V) _ (prod_pair f g a b k)
          (prod_cub k₁ k₂ k₃ fun q => k (q ≫ coprod.inl))).symm)
    · have C₁ : IsCub (cubV c₁ y (rl I)) := isCub_cubV c₁ (P₁.good hI)
      have C₂ : IsCub (cubV c₂ y (rr I)) := isCub_cubV c₂ (P₂.good hI)
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [ha, hb, ha₁, hb₁, ha₂, hb₂, hk, hl, hu.2 y I hI, C₁.face, C₂.face]
      simp
  have o₁ : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
  have s₁ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
  constructor
  · have := gen (p₀ * p₁) p₂ p₀ p₂ p₁ p₂ p₀ p₁ p₂ (p₀ ≫ f) (p₁ ≫ f) (p₂ ≫ g) (fun V _ k l => by
      rw [mf]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) o₁ e₂ e₀ e₂ e₁ e₂ e₀ (by rw [← Category.assoc, e₀, MonObj.one_comp])
    rwa [s₁, ← Category.assoc ρ p₂, ← Category.assoc ρ p₀, ← Category.assoc ρ p₁, r₀, r₁, r₂] at this
  · have := gen p₂ (p₀ * p₁) p₂ p₀ p₂ p₁ p₂ p₀ p₁ (p₂ ≫ f) (p₀ ≫ g) (p₁ ≫ g) (fun V _ k l => by
      rw [mg, _root_.mul_assoc p₂, _root_.mul_assoc (p₂ ≫ f)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) e₂ o₁ e₂ e₀ e₂ e₁ e₂ (by rw [← Category.assoc, e₂, MonObj.one_comp])
    rwa [s₁, ← Category.assoc ρ p₂, ← Category.assoc ρ p₀, ← Category.assoc ρ p₁, r₀, r₁, r₂] at this

end GlobalTheory.HomMumAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IInfThetaRuleLeLocalValueCharZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.PowGerm GlobalTheory.PtTie GlobalTheory.RefSum
open GlobalTheory.ThetaLeast

namespace GlobalTheory.JetsLevelZero

theorem iInf_thRule_le_nuLocOf_charZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G), P.TorsionIso → CharZero (IsLocalRing.ResidueField T.V) → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (r : ℕ) (Φ M0 : ℝ), GlobalTheory.PtTie.ShortBasis Q r Φ M0 → ∀ (α : 𝓞 E) (q : ℕ), α * star α = ((q : ℕ) : 𝓞 E) → q ∣ l.M → l.Mb ≤ Ideal.span {star α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ), 1 ≤ n → 0 < e → 4 * DF Dw a + 4 ≤ q → (DF Dw a : ℝ) * M0 < q → ∀ P₁ ∈ harmA (Dw := Dw) c a n, (⨅ (f : Rul Xo c) (_ : ∃ x : Fin n → Dw.La, IsThRule Xo c nab x P₁ f), nval T.V e (evI y f)) ≤ GlobalTheory.FactorDepth.nuLocOf C e l.M (MvPolynomial.map io P₁) + (((DF Dw a : ℝ) ^ 2 * Φ / q / e : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab T io y C hTr P hP hchar ϖ hϖ Q hQ r Φ M0 hSB α q hα hqM hMb a n e hn he h4 hM0 P₁ hP₁
  obtain ⟨hΦ, b, hb, hb'⟩ := hSB
  have hth : ThValTot Xo c nab :=
    GlobalTheory.thValTot_of_chartIndep GlobalTheory.firstFiveLaws.1 GlobalTheory.chartIndependence_unconditional E H Dw l Xo c nab hnab
  letI := io.toAlgebra
  obtain ⟨F, _, _, _, _, _, _, v, hv, hvx⟩ : ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : CharZero F)
      (_ : Algebra T.Fr F) (_ : Algebra T.V F) (_ : IsScalarTower T.V T.Fr F) (v : AddValuation F (WithTop ℚ)),
      ValOver ϖ F v ∧ ∀ x : T.Fr, x ≠ 0 → v (algebraMap T.Fr F x) = (((vV T.V x : ℤ) : ℚ) : WithTop ℚ) := by
    obtain ⟨v, hv⟩ := GlobalTheory.ValClosure.exists_valuation_closure T.V ϖ hϖ
    exact ⟨AlgebraicClosure T.Fr, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, v, hv⟩
  obtain ⟨TI⟩ := GlobalTheory.T.nonempty_tateIsometry_integralFramedPoint_chart E H Dw l Xo c T io y C P F
  obtain ⟨D', A', G', _, _, pD, pA, pG, U', PU, _, oD', hx, hact, hθ⟩ :=
    (GlobalTheory.T.exists_productData_copies_trivialisation_valuation E H Dw l Xo c T io y C P ϖ hϖ).2 n
  have hq0 : 0 < q := by omega
  obtain ⟨θ, θα, hθ1, hθ2, hθ3⟩ := hθ F v hv Q hQ α q hq0 hα
  have hcop : ∃ u u' : 𝓞 E, u * α + u' * star α = 1 := by
    have h1 := l.coprime
    have h2 : l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ Ideal.span {α} := by
      refine (Ideal.map_mono hMb).trans ?_
      rw [Ideal.map_span, Set.image_singleton]
      have h3 : (H.bar : 𝓞 E →+* 𝓞 E) (star α) = α := star_star α
      rw [h3]
    have h4' : Ideal.span {star α} ⊔ Ideal.span {α} = ⊤ := top_le_iff.1 (h1 ▸ sup_le_sup hMb h2)
    rw [sup_comm, ← Ideal.span_insert, Ideal.eq_top_iff_one, Ideal.mem_span_pair] at h4'
    exact h4'
  have hu : IsUnit ((q : ℕ) : T.V) := by
    refine (IsLocalRing.residue_ne_zero_iff_isUnit _).1 ?_
    rw [map_natCast]
    exact Nat.cast_ne_zero.2 hq0.ne'
  have hdeg1 : P₁.totalDegree ≤ DF Dw a := by
    have key : ∀ m ∈ P₁.support, (m.sum fun _ e => e) = DF Dw a := by
      intro m hm
      rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, DF]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => hP₁.1.2.2 m hm τ i
    exact Finset.sup_le fun m' hm' => (key m' hm').le
  unfold nuLocOf
  refine le_iInf_add_coe fun f => le_iInf_add_coe fun hf => ?_
  obtain ⟨f', hf', hff'⟩ := GlobalTheory.T.harmonic_value_integral_germ_frame_power_charZero E H Dw l Xo c T io y C hchar a n l.M q P₁ hP₁ f hf
  set Pp : MvPolynomial (LtN Dw n) T.Fr := MvPolynomial.map io P₁ with hPp
  set x0 := nabValN C.ch.B T.Fr C.ch.h H.w0 l.M f (fun ℓ : LtN Dw n => ℓ.2.2)
    (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) Pp with hx0def
  by_cases hx0 : x0 = 0
  · rw [hx0, nval_zero, EReal.top_add_coe]; exact le_top
  have hx0' : x0 = nabValN C.ch.B T.Fr C.ch.h H.w0 q f' (fun ℓ : LtN Dw n => ℓ.2.2)
      (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) Pp := hff'
  have hmap : (∑ _i : Fin 1, algebraMap T.Fr F (algebraMap T.V T.Fr 1) •
      MvPolynomial.map ((algebraMap T.Fr F).comp io) P₁) = MvPolynomial.map (algebraMap T.Fr F) Pp := by
    rw [Fin.sum_univ_one, map_one, map_one, one_smul, hPp, MvPolynomial.map_map]
  have hdeg : (MvPolynomial.map (algebraMap T.Fr F) Pp).totalDegree ≤ DF Dw a :=
    (Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans
      ((Finset.sup_mono (MvPolynomial.support_map_subset _ _)).trans hdeg1)
  have hval := nabValN_algebraMap T.Fr F _ _ C.ch.B C.ch.h (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.cc_h C.ch.gauge) H.w0 q n f'
    (LtN Dw n) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) Pp
  obtain ⟨i, p, w, ζ, x, t₀, t, σ', h, ρ, h1, h2, h3, h4', h5, h6, h7, h8, h9, hρ, hle⟩ :=
    GlobalTheory.JetsLevelZero.rPoint_any E H Dw l Xo c T io y C hTr P hP ϖ hϖ Q hQ F v hv TI Φ M0 r b hΦ hb hb' n D' A' G' pD pA pG U' PU
      oD' hx hact hn α q (DF Dw a) hα hcop hu h4 hM0 θ θα hθ1 hθ2 hθ3 (Fin 1)
      (fun _ => MvPolynomial.map ((algebraMap T.Fr F).comp io) P₁)
      (fun _ => algebraMap T.Fr F (algebraMap T.V T.Fr 1)) (fun _ => val_algebraMap_nonneg T v hvx _)
      (by rw [hmap]; exact hdeg) f' hf' ((vV T.V x0 : ℤ) : ℚ)
      (by rw [hmap, Nat.one_mul, hval, ← hx0']; exact hvx x0 hx0)
  obtain ⟨xx, u, hu0, hrel⟩ := GlobalTheory.T.harmonicValue_translate_divisor_level_integral_chart E H Dw l Xo c nab hnab T io y C hTr P hP hchar ϖ hϖ Q hQ
    F v hv n D' A' G' pD pA pG U' PU oD' hx hact α q hqM hα hMb θ θα hθ2 hθ3 p w ζ x t₀ t σ' h
    h1 h2 h3 h4' h6 h7 h8 h9 h5 a P₁ hP₁
  obtain ⟨g, hg, -⟩ := existsUnique_thRule Xo c nab hth xx hP₁
  have hgv := hrel g hg
  rw [hgv] at hρ
  have hε' : 0 ≤ v u := hu0
  exact (iInf₂_le g ⟨xx, hg⟩).trans (nval_le_of_val T v hvx hx0 hε' hρ hle e)

end GlobalTheory.JetsLevelZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealFromPlaceShiftStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_from_place_shift : PlaceShiftSt → IdealSt := by
  first | exact @GlobalTheory.CMIdeal.idealSt_of_placeShiftSt | exact GlobalTheory.CMIdeal.idealSt_of_placeShiftSt | (intros; apply GlobalTheory.CMIdeal.idealSt_of_placeShiftSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqOfReductionAgreeOnAffineOpenStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheaf_eq_of_reduction_agree_on_affineOpen : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0}) [IsLocallyNoetherian W] (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) (U : W.Opens), IsProper π → IsIso (π ∣_ U) → ∀ (K : W.IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∀ t : ℕ → W.IdealSheafData, IsSystem f I t → ∀ V : W.affineOpens, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData), Reduces (π ≫ f) I T' (fun e => (t e).comap π) → Reduces f I T'' (fun e => t e ⊔ K ^ k) → ∀ e, ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V = (t e).ideal V := by
  first | exact @GlobalTheory.FormalAlg.ideal_eq_of_reduces_affine | exact GlobalTheory.FormalAlg.ideal_eq_of_reduces_affine | (intros; apply GlobalTheory.FormalAlg.ideal_eq_of_reduces_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealValConjInv
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

noncomputable section

namespace GlobalTheory.CMTorsion

theorem tan_mapHom_conj (W₀ W₁ : WeierstrassCurve ℂ) (g : ℂ →+* ℂ) (h : W₀.map g = W₁) (c : ℂ) :
    tan W₁ (g c) ≫ mapHom W₀ g h = spMap (Chart.dualMapR g) ≫ tan W₀ c := by
  unfold tan
  rw [GlobalTheory.WeierstrassCurve.ptHom_mapHom, GlobalTheory.WeierstrassCurve.SpecMap_ptHom]
  apply GlobalTheory.WeierstrassCurve.ptHom_congr
  · ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · funext i
    fin_cases i
    · show g c • DualNumber.eps = Chart.dualMapR g (c • DualNumber.eps)
      ext <;> simp [Chart.dualMapR]
    · show (-1 : DualNumber ℂ) = Chart.dualMapR g (-1)
      simp
    · show (0 : DualNumber ℂ) = Chart.dualMapR g 0
      simp

end GlobalTheory.CMTorsion

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageBasePointRationalFractionField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatBase

theorem nsmul_b' {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {k : ℕ} {g h : GtPtF D F} (H : GtPtF.IsNsmul k g h) : h.b = g.b ^ k := by
  obtain ⟨gs, h0, hs, rfl⟩ := H
  have : ∀ i : Fin (k + 1), (gs i).b = g.b ^ (i : ℕ) := fun i => by
    induction i using Fin.induction with
    | zero => rw [Fin.val_zero, pow_zero]; exact h0.1
    | succ i ih => rw [(hs i).1, ih, Fin.val_succ, pow_succ]; rfl
  exact this _

theorem pow_comp' {S : Scheme.{0}} {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem ratBase : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (p₀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → ∃ b : TF (R := R) (FractionRing R) ⟶ D'.toPre.P.A, p.g.b.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ b.left := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n _ hn _ ζ _ Q e hD hT D' F p₀ p hy hg
  haveI := F.inc_hom
  haveI := F.pr_hom
  set L := AlgebraicClosure (FractionRing R)
  set a := F.xp p₀.y
  let b₀ : TF (R := R) L ⟶ Q.B := p₀.g.b ≫ F.pr
  have hpb : p.g.b = b₀ ≫ F.inc := by rw [hg.1, ← F.pr_inc, Category.assoc]
  obtain ⟨h, h1, h2⟩ := p₀.eq
  have hn1 : p₀.g.b ^ n = toUnit _ ≫ D'.toPre.c p₀.y := (nsmul_b' h1).symm.trans h2.1
  have hcpr : D'.toPre.c p₀.y ≫ F.pr = Q.c a := by
    have h3 : D'.toPre.c p₀.y ≫ F.pr ≫ F.inc = Q.c a ≫ F.inc := by
      rw [F.pr_inc, ← F.o.c_lin, ← F.xi_xp, F.c_xi]
    have h4 := congrArg (· ≫ F.pr) h3
    simpa only [Category.assoc, F.inc_pr, Category.comp_id] using h4
  have hb₀ : b₀ ^ n = toUnit _ ≫ Q.c a := by
    rw [← pow_comp', hn1, Category.assoc, hcpr]
  obtain ⟨β, β₂, w, hpb', hsq, hw, hc, htau⟩ := hD

  have hcomm : (spMap iw ≫ (T.c₀ (e a)).left) ≫ T.B.hom = 𝟙 (Sp R) ≫ spMap iw := by
    rw [Category.assoc, Over.w (T.c₀ (e a))]; simp
  let d : 𝟙_ (Over (Sp R)) ⟶ Q.B := Over.homMk (hpb'.1.lift _ _ hcomm) (by simpa using hpb'.1.lift_snd _ _ hcomm)
  have hd : d.left ≫ β = spMap iw ≫ (T.c₀ (e a)).left := hpb'.1.lift_fst _ _ hcomm
  have hdn : d ^ n = Q.c a := by
    refine Over.OverMorphism.ext (hpb'.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [GlobalTheory.FrameMove.pow_comm hpb' hd n, hc a]
    congr 2
    have key : ∀ k : ℕ, T.c₀ ((k : ℤ) • e a) = T.c₀ (e a) ^ k := fun k => by
      induction k with
      | zero => rw [Nat.cast_zero, zero_smul, pow_zero, T.c₀_zero]
      | succ k ih => rw [Nat.cast_succ, add_smul, one_smul, T.c₀_add, ih, pow_succ]
    exact (key n).symm

  let κ := algebraMap (FractionRing R) L
  let x : TF (R := R) L ⟶ Q.B := b₀ * (toUnit _ ≫ d)⁻¹
  have hx : x ^ n = 1 := by
    simp only [x]
    rw [mul_pow, inv_pow, hb₀, ← GlobalTheory.FrameMove.comp_pow, hdn, mul_inv_cancel]
  obtain ⟨x₀, hx₀⟩ := hT L κ x hx
  let ρ : TF (R := R) L ⟶ TK R := Over.homMk (spMap κ) rfl
  have hxρ : x = ρ ≫ x₀ := Over.OverMorphism.ext hx₀
  have hb₀' : b₀ = ρ ≫ (x₀ * (toUnit _ ≫ d)) := by
    rw [MonObj.comp_mul, ← hxρ, ← Category.assoc, toUnit_unique (ρ ≫ toUnit _) (toUnit _)]
    simp only [x, inv_mul_cancel_right]
  let σ : TF (R := R) (FractionRing R) ⟶ TK R := Over.homMk (jFK (R := R) (FractionRing R)) rfl
  refine ⟨σ ≫ (x₀ * (toUnit _ ≫ d)) ≫ F.inc, ?_⟩
  rw [hpb, hb₀']
  simp only [Over.comp_left]

  have hj : jFK (R := R) (FractionRing R) = 𝟙 _ := by
    simp only [jFK, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hσ : σ.left = 𝟙 _ := hj
  rw [hσ, Category.id_comp, Category.assoc]
  rfl

end GlobalTheory.Mum.RatBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageDegreePositiveStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.image_degree_positive : Hypotheses2 → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → ∃ (X : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral X) (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s := by
  first | exact @GlobalTheory.ImageModel.exists_isModelOf | exact GlobalTheory.ImageModel.exists_isModelOf | (intros; apply GlobalTheory.ImageModel.exists_isModelOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteScaleThetaBoundRight
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsAtRealTBClose

theorem rowsB_of_decay : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (B : RealTB Rc P Dcf Spf Zscf S), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → B.Q.Rl.toRealDat.ExAt → RowsB B := by
  intro hDec D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hn hEx
  have hUnif := GlobalTheory.T.indefinite_scale_theta_bound_left hDec D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hn
  have hIo := GlobalTheory.T.ioExt_of_weakCharacterisation_of_orthonormal_frames D _ _ _ _ P.A3 _ B.Q.Rl (faceT P Dcf Spf Zscf) B.Q.charW hEx B.Q.stdV
  exact GlobalTheory.RowsAtRealTB.rowsB_of_clauses D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hn hEx hUnif hIo

end GlobalTheory.RowsAtRealTBClose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtBasicOpenOfIntegralMulChartValueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralAt_basicOpen_of_integral_mul_chartValue : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → ∀ (x : X) (d : Γ(X, W)), x ∈ X.basicOpen d → (α.app W).hom.IsIntegralElem ((α.app W).hom d * chartVal L α s j W hW) → IntAt L α s x := by
  first | exact @GlobalTheory.Mum.intAt_of_integral_mul_basicOpen | exact GlobalTheory.Mum.intAt_of_integral_mul_basicOpen | (intros; apply GlobalTheory.Mum.intAt_of_integral_mul_basicOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralElementAffineSectionGeneratedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_element_affine_section_generated : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (W : G.left.Opens) (U : M.S.Opens) (hWU : W ≤ G.hom ⁻¹ᵁ U), IsAffineOpen W → IsAffineOpen U → ∀ f : Γ(Y, α ⁻¹ᵁ W), (α.app W).hom.IsIntegralElem f → ∃ (n : ℕ) (c : Fin n → Γ(G.left, W)) (b : Fin n → Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)), (∀ m, (M.gp.app U).hom.IsIntegralElem (b m)) ∧ f = ∑ m, (α.app W).hom (c m) * (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen G.hom α t M.gp hpb.w W U hWU)).hom (b m) := by
  first | exact @GlobalTheory.Mum.eq_sum_of_isIntegral_genericChart | exact GlobalTheory.Mum.eq_sum_of_isIntegral_genericChart | (intros; apply GlobalTheory.Mum.eq_sum_of_isIntegral_genericChart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelConjugateEmbeddingStatement
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_conjugate_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (τ : E →+* ℂ) (A : Type) [CommRing A] [IsDomain A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ) → Fin g → A) (U₂ h₂ : Fin (Dw.mult (conjEmb τ)) → Fin g → A), IsTanBasis Y.t ξ e → (∀ (S : Type) [CommRing S] (φ : A →+* S), EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧ EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) → IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) → ∀ (T : CDVR) (α : A →+* T.V) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (yy : Sp T.Fr ⟶ Xo'.XF c'), yy ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp α) ≫ ξ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) → ∃ (w₁ : Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left)) (w₂ : Fin (Dw.mult (conjEmb τ)) → (Sp (DualNumber T.Fr) ⟶ Y.oF.t.G.left)) (g₁ : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.Fr) (g₂ : Matrix (Fin (Dw.mult (conjEmb τ))) (Fin (Dw.mult (conjEmb τ))) T.Fr), (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t ((algebraMap T.V T.Fr).comp α) e) (fun b => (algebraMap T.V T.Fr).comp α (U₁ i b)) (w₁ i ≫ Y.m.φ)) ∧ (∀ i, IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t ((algebraMap T.V T.Fr).comp α) e) (fun b => (algebraMap T.V T.Fr).comp α (U₂ i b)) (w₂ i ≫ Y.m.φ)) ∧ (letI := io.toAlgebra; (∀ i, IsCombAt y₀.1.x (y₀.1.u τ) (g₁ i) (w₁ i ≫ ν.φ)) ∧ (∀ i, IsCombAt y₀.1.x (y₀.1.u (conjEmb τ)) (g₂ i) (w₂ i ≫ ν.φ))) ∧ (∃ u : T.Vˣ, algebraMap T.V T.Fr u = g₁.det) ∧ ∃ u : T.Vˣ, algebraMap T.V T.Fr u = g₂.det := by
  first | exact @GlobalTheory.FlatModel.frames_changeOfBasis_det_isUnit | exact GlobalTheory.FlatModel.frames_changeOfBasis_det_isUnit | (intros; apply GlobalTheory.FlatModel.frames_changeOfBasis_det_isUnit <;> assumption)
end

