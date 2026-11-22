import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0593
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullDegEquivApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0723
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0725
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDPMorphismOfIsStd
section
set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem PDPoly.isDPMorphism_of_isStd :
    ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J)),
      Q.IsStd δ η → ∀ (C : Type) [CommRing C] (J'' : Ideal C) (δ'' : DividedPowers J'') (F : Q.P →+* C) (c : C),
        c ∈ J'' → IsDPMorphism δ δ'' (F.comp (algebraMap B Q.P)) → (∀ n, F (Q.e n) = δ''.dpow n c) →
          IsDPMorphism η δ'' F := by
  intro B _ J δ Q η hQ C _ J'' δ'' F c hc hF he
  have hS : Q.ext J = Ideal.span (algebraMap B Q.P '' J ∪ Set.range fun n : ℕ ↦ Q.e (n + 1)) := by
    rw [Ideal.span_union, ← Ideal.map_span, Ideal.span_eq]; rfl
  refine IsDPMorphism.on_span η δ'' hS ?_ ?_
  · rintro s (⟨a, ha, rfl⟩ | ⟨k, rfl⟩)
    · exact hF.1 (Ideal.mem_map_of_mem _ ha)
    · rw [he]; exact δ''.dpow_mem k.succ_ne_zero hc
  · rintro n s (⟨a, ha, rfl⟩ | ⟨k, rfl⟩)
    · rw [hQ.dp.2 a ha]
      exact (hF.2 a ha).symm
    · have h1 := Q.e_one_mem_ext J
      show F (η.dpow n (Q.e (k + 1))) = δ''.dpow n (F (Q.e (k + 1)))
      have h2 : η.dpow n (Q.e (k + 1)) = (n.uniformBell (k + 1) : Q.P) * Q.e (n * (k + 1)) := by
        rw [← hQ.var (k + 1), η.dpow_comp k.succ_ne_zero h1, hQ.var]
      rw [h2, map_mul, map_natCast, he, he, δ''.dpow_comp k.succ_ne_zero hc]

end GlobalTheory.PDA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackCompSpreadToSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GrpMulSpread

attribute [local instance] Over.cartesianMonoidalCategory

theorem isPullback_pullbackMap {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (cart : IsPullback F G'.hom G.hom f) :
    IsPullback (pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm)
      (G' ⊗ G').hom (G ⊗ G).hom f := by
  have p : IsPullback (pullback.snd G.hom G.hom) (pullback.fst G.hom G.hom) G.hom G.hom :=
    (IsPullback.of_hasPullback G.hom G.hom).flip
  have p' : IsPullback (pullback.snd G'.hom G'.hom) (pullback.fst G'.hom G'.hom) G'.hom G'.hom :=
    (IsPullback.of_hasPullback G'.hom G'.hom).flip
  have c₁ : pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm ≫ pullback.fst G.hom G.hom =
      pullback.fst G'.hom G'.hom ≫ F := pullback.lift_fst _ _ _
  have c₂ : pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm ≫ pullback.snd G.hom G.hom =
      pullback.snd G'.hom G'.hom ≫ F := pullback.lift_snd _ _ _
  have q : IsPullback (pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm ≫
      pullback.snd G.hom G.hom) (pullback.fst G'.hom G'.hom) G.hom (F ≫ G.hom) := by
    rw [c₂, cart.w]
    exact p'.paste_horiz cart
  exact (IsPullback.of_right q c₁ p).paste_vert cart

theorem pullbackMap_comp {S₁ S₀ Y : Scheme.{0}} {A₁ : Over S₁} {D : Over S₀} {U : Over Y} {k : S₁ ⟶ S₀}
    {h₀ : S₀ ⟶ Y} {φ : A₁.left ⟶ D.left} {ψ : D.left ⟶ U.left} (hφ : IsPullback φ A₁.hom D.hom k)
    (cart : IsPullback ψ D.hom U.hom h₀) :
    pullback.map A₁.hom A₁.hom D.hom D.hom φ φ k hφ.w.symm hφ.w.symm ≫
        pullback.map D.hom D.hom U.hom U.hom ψ ψ h₀ cart.w.symm cart.w.symm =
      pullback.map A₁.hom A₁.hom U.hom U.hom (φ ≫ ψ) (φ ≫ ψ) (k ≫ h₀)
        (hφ.paste_horiz cart).w.symm (hφ.paste_horiz cart).w.symm := by
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

theorem isGrpPullback_comp_spread_to_subring :
    ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → IsGrpPullback e.A d₀.A (spMap R₀.subtype) j → IsGrpPullback e.A u.A (spMap R₀.subtype ≫ h₀) (j ≫ ψ) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] (φ₁ : A₁.left ⟶ d₀.A.left), IsGrpPullback A₁ d₀.A (spMap (Subring.inclusion hle)) φ₁ → IsGrpPullback A₁ u.A (spMap (Subring.inclusion hle) ≫ h₀) (φ₁ ≫ ψ) := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ ψ sE e j cart hj hjψ
  haveI := d₀.ab.proper
  haveI := u.ab.smooth
  haveI hqc : QuasiCompact (pullback.fst d₀.A.hom d₀.A.hom ≫ d₀.A.hom) := inferInstance
  haveI hlft : LocallyOfFiniteType (pullback.snd u.A.hom h₀) := inferInstance
  set f₀ : pullback d₀.A.hom d₀.A.hom ⟶ Sp R₀ := pullback.fst d₀.A.hom d₀.A.hom ≫ d₀.A.hom with hf₀
  have hμd : (μ[d₀.A]).left ≫ d₀.A.hom = f₀ := Over.w μ[d₀.A]
  have hμu : (μ[u.A]).left ≫ u.A.hom = pullback.fst u.A.hom u.A.hom ≫ u.A.hom := Over.w μ[u.A]
  set mψ := pullback.map d₀.A.hom d₀.A.hom u.A.hom u.A.hom ψ ψ h₀ cart.w.symm cart.w.symm with hmψ
  have w₁ : ((μ[d₀.A]).left ≫ ψ) ≫ u.A.hom = f₀ ≫ h₀ := by
    rw [Category.assoc, cart.w, ← Category.assoc, hμd]
  have w₂ : (mψ ≫ (μ[u.A]).left) ≫ u.A.hom = f₀ ≫ h₀ := by
    rw [Category.assoc, hμu, ← Category.assoc, hmψ, pullback.lift_fst, Category.assoc, cart.w, hf₀,
      Category.assoc]
  let a : pullback d₀.A.hom d₀.A.hom ⟶ pullback u.A.hom h₀ := pullback.lift _ _ w₁
  let b : pullback d₀.A.hom d₀.A.hom ⟶ pullback u.A.hom h₀ := pullback.lift _ _ w₂
  have key : ∀ {S₁ : Scheme.{0}} {A₁ : Over S₁} [GrpObj A₁] {k : S₁ ⟶ Sp R₀} {φ : A₁.left ⟶ d₀.A.left}
      (hφ : IsPullback φ A₁.hom d₀.A.hom k),
      pullback.map A₁.hom A₁.hom d₀.A.hom d₀.A.hom φ φ k hφ.w.symm hφ.w.symm ≫ mψ =
        pullback.map A₁.hom A₁.hom u.A.hom u.A.hom (φ ≫ ψ) (φ ≫ ψ) (k ≫ h₀)
          (hφ.paste_horiz cart).w.symm (hφ.paste_horiz cart).w.symm := by
    intro S₁ A₁ _ k φ hφ
    exact pullbackMap_comp hφ cart
  have hab : pullback.map e.A.hom e.A.hom d₀.A.hom d₀.A.hom j j (spMap R₀.subtype) hj.1.w.symm hj.1.w.symm ≫ a =
      pullback.map e.A.hom e.A.hom d₀.A.hom d₀.A.hom j j (spMap R₀.subtype) hj.1.w.symm hj.1.w.symm ≫ b := by
    have m₁ := (GlobalTheory.PullDegCompare.isGrpPullback_iff hj.1).1 hj
    have m₂ := (GlobalTheory.PullDegCompare.isGrpPullback_iff hjψ.1).1 hjψ
    apply pullback.hom_ext
    · simp only [a, b, Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, ← m₁, Category.assoc, m₂]
      exact (congrArg (· ≫ (μ[u.A]).left) (key hj.1).symm).trans (Category.assoc _ _ _)
    · simp only [a, b, Category.assoc, pullback.lift_snd]
  obtain ⟨F, hF⟩ := GlobalTheory.morphisms_eq_spread_to_subring S R₀ (pullback e.A.hom e.A.hom)
    (pullback d₀.A.hom d₀.A.hom) (pullback u.A.hom h₀) (e.A ⊗ e.A).hom f₀ (pullback.snd u.A.hom h₀)
    (pullback.map e.A.hom e.A.hom d₀.A.hom d₀.A.hom j j (spMap R₀.subtype) hj.1.w.symm hj.1.w.symm) a b
    (isPullback_pullbackMap hj.1) (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) hab
  refine ⟨F, fun R₁ hle hFs A₁ _ φ₁ hφ ↦ ?_⟩
  have cart₁ := hφ.1.paste_horiz cart
  refine (GlobalTheory.PullDegCompare.isGrpPullback_iff cart₁).2 ?_
  have H := hF R₁ hle hFs (pullback A₁.hom A₁.hom) (A₁ ⊗ A₁).hom
    (pullback.map A₁.hom A₁.hom d₀.A.hom d₀.A.hom φ₁ φ₁ _ hφ.1.w.symm hφ.1.w.symm)
    (isPullback_pullbackMap hφ.1)
  have H' := congrArg (· ≫ pullback.fst u.A.hom h₀) H
  simp only [a, b, Category.assoc, pullback.lift_fst] at H'
  have m := (GlobalTheory.PullDegCompare.isGrpPullback_iff hφ.1).1 hφ
  rw [← Category.assoc, m, Category.assoc, H']
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (μ[u.A]).left) (key hφ.1))

end GlobalTheory.GrpMulSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionNonrealMultiplierStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_weierstrassP_torsion_nonreal_multiplier : ∀ (L : PeriodPair) (β Ω : ℂ) (M : ℕ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L → 0 < M → (∀ P, (M : ℂ) * P ∈ L.lattice → IsIntegral ℤ (12 * (M : ℂ) ^ 2 * L.weierstrassP P / Ω ^ 2) ∧ IsIntegral ℤ ((M : ℂ) ^ 3 * L.derivWeierstrassP P / Ω ^ 3)) ∧ ∀ P Q, P ∉ L.lattice → Q ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → (M : ℂ) * Q ∈ L.lattice → IsIntegral ℤ ((M : ℂ) ^ 2 * (L.weierstrassP P - L.weierstrassP Q) / Ω ^ 2) := by
  first | exact @GlobalTheory.WpFam.LatTorsVal.main | exact GlobalTheory.WpFam.LatTorsVal.main | (intros; apply GlobalTheory.WpFam.LatTorsVal.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfFlatPullbackReduction
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

open CategoryTheory.Limits
open scoped TensorProduct

namespace GlobalTheory.NilThickIso

theorem appTop_spMap_eq {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀) :
    (spMap π).appTop = (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom π ≫
      (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv := by
  rw [← Scheme.ΓSpecIso_naturality_assoc]; simp

theorem surjective_appTop_spMap {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) : Function.Surjective (spMap π).appTop := by
  rw [appTop_spMap_eq]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp]
  exact ((ConcreteCategory.bijective_of_isIso _).2.comp hπ).comp
    (ConcreteCategory.bijective_of_isIso _).2

theorem isNilpotent_ker_appTop_spMap {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hn : IsNilpotent (RingHom.ker π)) : IsNilpotent (RingHom.ker (spMap π).appTop.hom) := by
  obtain ⟨n, hn⟩ := hn
  refine ⟨n, ?_⟩
  rw [appTop_spMap_eq]
  simp only [CommRingCat.hom_comp]
  set e := (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
  have hk : RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom.comp
      (CommRingCat.ofHom π).hom).comp e) = (RingHom.ker π).comap e := by
    ext x
    simp only [RingHom.mem_ker, RingHom.comp_apply, Ideal.mem_comap]
    constructor
    · intro h
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R₀)).hom.hom h
      simpa using this
    · intro h; simp [h]
  rw [hk, Ideal.zero_eq_bot, ← le_bot_iff]
  refine (Ideal.le_comap_pow _ n).trans ?_
  rw [hn, Ideal.zero_eq_bot]
  intro x hx
  simp only [Ideal.mem_comap, Ideal.mem_bot] at hx ⊢
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
    (by rw [map_zero]; exact hx)

theorem surjective_of_sub_mem_map {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    [Algebra A C] (φ : B →ₐ[A] C) (I : Ideal A) (hI : IsNilpotent I)
    (h : ∀ c : C, ∃ b : B, c - φ b ∈ I.map (algebraMap A C)) : Function.Surjective φ := by
  obtain ⟨n, hn⟩ := hI
  let N : Submodule A C := LinearMap.range φ.toLinearMap
  have h1 : (⊤ : Submodule A C) ≤ N ⊔ I • ⊤ := by
    intro c _
    obtain ⟨b, hb⟩ := h c
    have hm : c - φ b ∈ I • (⊤ : Submodule A C) := by
      rw [Ideal.smul_top_eq_map]; exact hb
    have := Submodule.add_mem_sup (LinearMap.mem_range_self φ.toLinearMap b) hm
    simpa using this
  have h2 : ∀ k : ℕ, (⊤ : Submodule A C) ≤ N ⊔ I ^ k • ⊤ := by
    intro k
    induction k with
    | zero => exact le_sup_of_le_right (by rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul])
    | succ k ih =>
      calc ⊤ ≤ N ⊔ I ^ k • ⊤ := ih
        _ ≤ N ⊔ I ^ k • (N ⊔ I • ⊤) := sup_le_sup_left (Submodule.smul_mono le_rfl h1) _
        _ = N ⊔ (I ^ k • N ⊔ I ^ (k + 1) • ⊤) := by
          rw [Submodule.smul_sup, pow_succ, Submodule.mul_smul]
        _ ≤ N ⊔ I ^ (k + 1) • ⊤ := by
          rw [← sup_assoc]
          exact sup_le_sup_right (sup_le le_rfl Submodule.smul_le_right) _
  have h3 := h2 n
  rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at h3
  intro c
  obtain ⟨b, hb⟩ := h3 (Submodule.mem_top (x := c))
  exact ⟨b, hb⟩

theorem injective_of_flat_of_ker_le_map {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Module.Flat A C] (φ : B →ₐ[A] C) (I : Ideal A) (hI : IsNilpotent I)
    (hs : Function.Surjective φ) (h : ∀ b : B, φ b = 0 → b ∈ I.map (algebraMap A B)) :
    Function.Injective φ := by
  obtain ⟨n, hn⟩ := hI
  set K := LinearMap.ker φ.toLinearMap with hKdef
  let mB : I ⊗[A] B →ₗ[A] B := (TensorProduct.lid A B).toLinearMap ∘ₗ I.subtype.rTensor B
  let mC : I ⊗[A] C →ₗ[A] C := (TensorProduct.lid A C).toLinearMap ∘ₗ I.subtype.rTensor C
  have hmC : Function.Injective mC := (TensorProduct.lid A C).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have hcomm : ∀ t, φ (mB t) = mC (φ.toLinearMap.lTensor I t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [mB, mC]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hex := lTensor_exact I (LinearMap.exact_subtype_ker_map φ.toLinearMap) hs
  have hrange : ∀ b ∈ I • (⊤ : Submodule A B), ∃ t, mB t = b := by
    intro b hb
    refine Submodule.smul_induction_on (p := fun b ↦ ∃ t, mB t = b) hb ?_ ?_
    · intro a ha x _
      exact ⟨⟨a, ha⟩ ⊗ₜ x, by simp [mB]⟩
    · rintro x y ⟨t, rfl⟩ ⟨s, rfl⟩
      exact ⟨t + s, map_add _ _ _⟩
  have hK : ∀ s : I ⊗[A] K, mB (K.subtype.lTensor I s) ∈ I • K := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [mB, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
        LinearEquiv.coe_coe, TensorProduct.lid_tmul, Submodule.subtype_apply]
      exact Submodule.smul_mem_smul a.2 x.2
    | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
  have hle : K ≤ I • K := by
    intro k hk
    have hk' : k ∈ I • (⊤ : Submodule A B) := by rw [Ideal.smul_top_eq_map]; exact h k hk
    obtain ⟨t, rfl⟩ := hrange k hk'
    have h0 : φ.toLinearMap.lTensor I t = 0 := hmC (by rw [← hcomm, map_zero]; exact hk)
    obtain ⟨s, rfl⟩ := (hex t).mp h0
    exact hK s
  have hle' : ∀ k : ℕ, K ≤ I ^ k • K := by
    intro k
    induction k with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    | succ k ih =>
      calc K ≤ I ^ k • K := ih
        _ ≤ I ^ k • (I • K) := Submodule.smul_mono le_rfl hle
        _ = I ^ (k + 1) • K := by rw [pow_succ, Submodule.mul_smul]
  have h3 := hle' n
  rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul] at h3
  rw [injective_iff_map_eq_zero]
  intro b hb
  exact (Submodule.mem_bot A).mp (h3 hb)

theorem ring_step {A A₀ B C B₀ C₀ : CommRingCat.{0}} (ψ : A ⟶ A₀) (β : A ⟶ B) (ρ : A ⟶ C)
    (φ : B ⟶ C) (πB : B ⟶ B₀) (πC : C ⟶ C₀) (β₀ : A₀ ⟶ B₀) (ρ₀ : A₀ ⟶ C₀) (φ₀ : B₀ ⟶ C₀)
    (hψ : Function.Surjective ψ) (hn : IsNilpotent (RingHom.ker ψ.hom))
    (hB : IsPushout β ψ πB β₀) (hC : IsPushout ρ ψ πC ρ₀) (hflat : ρ.hom.Flat)
    (w : β ≫ φ = ρ) (w₀ : φ ≫ πC = πB ≫ φ₀) (hφ₀ : IsIso φ₀) : IsIso φ := by
  have hkB := GlobalTheory.PrimeSection.ker_eq_map_of_isPushout hB hψ
  have hkC := GlobalTheory.PrimeSection.ker_eq_map_of_isPushout hC hψ
  have hπB : Function.Surjective πB := by
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout hB, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · exact ⟨y, rfl⟩
    · obtain ⟨a, rfl⟩ := hψ y
      exact ⟨β a, congr($(hB.w).hom a)⟩
  have hφ₀ := ConcreteCategory.bijective_of_isIso φ₀
  have hw₀ (b : B) : πC (φ b) = φ₀ (πB b) := congr($(w₀).hom b)
  algebraize [β.hom, ρ.hom]
  let φA : B →ₐ[A] C := { φ.hom with commutes' := fun a ↦ congr($(w).hom a) }
  have hs : Function.Surjective φA := by
    refine surjective_of_sub_mem_map φA (RingHom.ker ψ.hom) hn fun c ↦ ?_
    obtain ⟨y, hy⟩ := hφ₀.2 (πC c)
    obtain ⟨b, rfl⟩ := hπB y
    refine ⟨b, ?_⟩
    have h0 : πC (c - φ b) = 0 := by rw [map_sub, hw₀, hy, sub_self]
    have h1 : c - φ b ∈ RingHom.ker πC.hom := h0
    rw [hkC] at h1
    exact h1
  have hi : Function.Injective φA := by
    refine injective_of_flat_of_ker_le_map φA (RingHom.ker ψ.hom) hn hs fun b hb ↦ ?_
    have h0 : πB b = 0 := hφ₀.1 (by rw [← hw₀, show φ b = 0 from hb, map_zero, map_zero])
    rw [← RingHom.mem_ker, hkB] at h0
    exact h0
  exact (ConcreteCategory.isIso_iff_bijective φ).mpr ⟨hi, hs⟩

theorem affine_case (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π)) {X Y X₀ Y₀ : Scheme.{0}}
    (p : X ⟶ Sp R) (q : Y ⟶ Sp R) (p₀ : X₀ ⟶ Sp R₀) (q₀ : Y₀ ⟶ Sp R₀) (i : X₀ ⟶ X) (j : Y₀ ⟶ Y)
    (hX : IsPullback i p₀ p (spMap π)) (hY : IsPullback j q₀ q (spMap π)) [Flat p] [IsAffine Y]
    (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀) (w : f ≫ q = p) (w₀ : i ≫ f = f₀ ≫ j) [IsIso f₀] : IsIso f := by
  have : IsAffine Y₀ := IsAffine.of_isPullback hY
  have : IsAffine X₀ := IsAffine.of_isIso f₀
  have : IsAffine X := GlobalTheory.AffineThickening.isAffine_of_isPullback_of_isNilpotent (RingHom.ker π) hn
    (CommRingCat.ofHom π) hπ rfl hX this
  have hψ := surjective_appTop_spMap π hπ
  have hψn := isNilpotent_ker_appTop_spMap π hn
  have hfl : (p.appTop).hom.Flat := HasRingHomProperty.iff_of_isAffine.mp ‹Flat p›
  have key : IsIso f.appTop := ring_step (spMap π).appTop q.appTop p.appTop f.appTop j.appTop i.appTop
    q₀.appTop p₀.appTop f₀.appTop hψ hψn (isPushout_appTop_of_isPullback hY)
    (isPushout_appTop_of_isPullback hX) hfl (by rw [← w]; simp) (by
      rw [← Scheme.Hom.comp_appTop, w₀, Scheme.Hom.comp_appTop]) ⟨⟨(inv f₀).appTop, by rw [← Scheme.Hom.comp_appTop]; simp, by rw [← Scheme.Hom.comp_appTop]; simp⟩⟩
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _) (arrowIsoSpecΓOfIsAffine f)).mpr
    (inferInstanceAs (IsIso (Spec.map (f.appTop))))

theorem general (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π)) {X Y X₀ Y₀ : Scheme.{0}}
    (p : X ⟶ Sp R) (q : Y ⟶ Sp R) (p₀ : X₀ ⟶ Sp R₀) (q₀ : Y₀ ⟶ Sp R₀) (i : X₀ ⟶ X) (j : Y₀ ⟶ Y)
    (hX : IsPullback i p₀ p (spMap π)) (hY : IsPullback j q₀ q (spMap π)) [Flat p]
    (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀) (w : f ≫ q = p) (w₀ : i ≫ f = f₀ ≫ j) [IsIso f₀] : IsIso f := by
  refine IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme)
    Y.affineCover (fun k ↦ ?_)
  change IsIso (pullback.snd f (Y.affineCover.f k))
  set u := Y.affineCover.f k
  have hU : IsPullback (pullback.snd j u) (pullback.fst j u ≫ q₀) (u ≫ q) (spMap π) :=
    (IsPullback.of_hasPullback j u).flip.paste_vert hY
  have hX' : IsPullback (pullback.snd i (pullback.fst f u)) (pullback.fst i (pullback.fst f u) ≫ p₀)
      (pullback.fst f u ≫ p) (spMap π) :=
    (IsPullback.of_hasPullback i (pullback.fst f u)).flip.paste_vert hX
  have hP : IsPullback (pullback.fst i (pullback.fst f u))
      (pullback.snd i (pullback.fst f u) ≫ pullback.snd f u) (i ≫ f) u :=
    (IsPullback.of_hasPullback i (pullback.fst f u)).paste_vert (IsPullback.of_hasPullback f u)
  have hP' : IsPullback (pullback.fst i (pullback.fst f u) ≫ f₀)
      (pullback.snd i (pullback.fst f u) ≫ pullback.snd f u) j u :=
    IsPullback.of_iso hP (Iso.refl _) (asIso f₀) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [w₀]) (by simp)
  exact affine_case R R₀ π hπ hn (pullback.fst f u ≫ p) (u ≫ q) _ _ _ _ hX' hU (pullback.snd f u)
    hP'.isoPullback.hom (by rw [← w, pullback.condition_assoc]) (by simp)

theorem isIso_of_flat_of_isIso_reduction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X Y : Over (Sp R)) (X₀ Y₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left) (j : Y₀.left ⟶ Y.left),
    IsPullback i X₀.hom X.hom (spMap π) → IsPullback j Y₀.hom Y.hom (spMap π) → Flat X.hom →
    ∀ (f : X ⟶ Y) (f₀ : X₀ ⟶ Y₀), i ≫ f.left = f₀.left ≫ j → IsIso f₀ → IsIso f := by
  intro R R₀ _ _ π hπ hn X Y X₀ Y₀ i j hX hY hfl f f₀ w₀ hf₀
  have : IsIso f₀.left := (Over.forget _).map_isIso f₀
  have : IsIso f.left := general R R₀ π hπ hn X.hom Y.hom X₀.hom Y₀.hom i j hX hY f.left f₀.left
    (Over.w f) w₀
  have : IsIso ((Over.forget _).map f) := this
  exact isIso_of_reflects_iso f (Over.forget _)

end GlobalTheory.NilThickIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNarrowRayClassLFunctionMulPrimeWideIndicatorStatement
section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNarrowRayClassLFunction_mul_prime_wideIndicator : ∀ {F : Type} [Field F] [NumberField F] (𝔪 𝔭 : Ideal (𝓞 F)), 𝔭.IsMaximal → 𝔭 ≠ ⊥ → 𝔭 ⊔ 𝔪 = ⊤ →
    ∀ (C : ClassGroup (𝓞 F)) (Z Z' : ℂ → ℂ), IsRayL 𝔪 (wideInd C) Z → IsRayL 𝔪 (wideInd (C * (cls 𝔭)⁻¹)) Z' →
    IsRayL (𝔪 * 𝔭) (wideInd C) (fun s => Z s - ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s) := by
  first | exact @GlobalTheory.isRayL_mul_prime_wideInd | exact GlobalTheory.isRayL_mul_prime_wideInd | (intros; apply GlobalTheory.isRayL_mul_prime_wideInd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNarrowRayClassLFunctionTopWideIndicatorIffStatement
section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNarrowRayClassLFunction_top_wideIndicator_iff : ∀ {F : Type} [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ), IsRayL (⊤ : Ideal (𝓞 F)) (wideInd C) Z ↔ IsClassZeta C Z := by
  first | exact @GlobalTheory.ZetaDenom.isRayL_top_wideInd_iff | exact GlobalTheory.ZetaDenom.isRayL_top_wideInd_iff | (intros; apply GlobalTheory.ZetaDenom.isRayL_top_wideInd_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfNilpotentDividedPowersIdealStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNilpotent_of_nilpotentDividedPowers_ideal : ∀ {D : Type} [CommRing D] [Algebra ℂ D] {J : Ideal D} (dl : DividedPowers J), IsNilDP dl → IsNilpotent J := by
  first | exact @GlobalTheory.AnPer.isNilpotent_of_isDPNilpotent | exact GlobalTheory.AnPer.isNilpotent_of_isDPNilpotent | (intros; apply GlobalTheory.AnPer.isNilpotent_of_isDPNilpotent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParameterTaylorExpansionHomApplyOfParamOnlyStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isParameterTaylorExpansionHom_apply_of_param_only : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (h : Hol W) (f : (I → ℂ) → ℂ), (∀ p ∈ W, h.fn p = f p.1) → ρ h = taylor N t f ⊗ₜ[ℂ] 1 := by
  first | exact @GlobalTheory.AnPer.isTay_apply_of_fn_eq_param | exact GlobalTheory.AnPer.isTay_apply_of_fn_eq_param | (intros; apply GlobalTheory.AnPer.isTay_apply_of_fn_eq_param <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsParameterTaylorExpansionHomFibreDerivationStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isParameterTaylorExpansionHom_fibreDerivation : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (a : Fin g) (h : Hol W), ρ (dw a h) = LinearMap.lTensor R (dw a).toLinearMap (ρ h) := by
  first | exact @GlobalTheory.AnPer.isTay_dw_lTensor | exact GlobalTheory.AnPer.isTay_dw_lTensor | (intros; apply GlobalTheory.AnPer.isTay_dw_lTensor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperGeometricallyConnectedSmoothNilpotentLif
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NilLift

theorem surjective_spMap_of_isNilpotent_ker {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π)) : Surjective (spMap π) := by
  refine ⟨fun (x : PrimeSpectrum R) ↦ ?_⟩
  have : x ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [range_comap_of_surjective _ _ hπ]
    obtain ⟨n, hn⟩ := hn
    intro a ha
    apply x.isPrime.mem_of_pow_mem n
    have : a ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at this
    rw [show a ^ n = 0 from this]
    exact zero_mem _
  exact this

theorem isProper_and_geometricallyConnected_of_smooth_lift :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    IsProper X₀.hom → GeometricallyConnected X₀.hom → IsProper X.hom ∧ GeometricallyConnected X.hom := by
  intro R R₀ _ _ π hπ hn X X₀ i hsq hsm hp hgc
  have hs : Surjective (spMap π) := surjective_spMap_of_isNilpotent_ker π hπ hn
  have hc : IsClosedImmersion (spMap π) := .spec_of_surjective _ hπ
  have : Surjective i := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hs
  have : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip hc
  have : IsProper (i ≫ X.hom) := by rw [hsq.w]; infer_instance
  have : UniversallyClosed X.hom := UniversallyClosed.of_comp_surjective i X.hom
  have : IsSeparated X.hom := GlobalTheory.NilProper.isSeparated_of_comp_surjective i X.hom
  have : LocallyOfFiniteType X.hom := inferInstance
  refine ⟨{}, ⟨fun K _ y Z fst snd hz ↦ ?_⟩⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  have hφ : RingHom.ker π ≤ RingHom.ker φ.hom := by
    intro a ha
    obtain ⟨n, hn⟩ := hn
    have : a ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at this
    have h0 : IsNilpotent a := ⟨n, this⟩
    exact (h0.map φ.hom).eq_zero
  let ψ : R₀ →+* K := RingHom.liftOfSurjective π hπ ⟨φ.hom, hφ⟩
  have hψ : ∀ a, ψ (π a) = φ.hom a := fun a ↦
    RingHom.liftOfRightInverse_comp_apply π _ _ ⟨φ.hom, hφ⟩ a
  let y' : Spec (CommRingCat.of K) ⟶ Sp R₀ := Spec.map (CommRingCat.ofHom ψ)
  have hy : y' ≫ spMap π = Spec.map φ := by
    simp only [y', spMap, ← Spec.map_comp]
    congr 1
    ext a
    exact hψ a
  rw [← hy] at hz
  let p : Z ⟶ X₀.left := hsq.lift fst (snd ≫ y') (by rw [hz.w, Category.assoc])
  refine hgc.geometrically_connectedSpace y' p snd ?_
  exact IsPullback.of_right (by rw [hsq.lift_fst]; exact hz) (hsq.lift_snd _ _ _) hsq

end GlobalTheory.NilLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesEvalTruncSubstEqSumStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_eval_trunc_subst_eq_sum : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (σ τ : Type) [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] (z : σ → B) (u : τ → MvPowerSeries σ B), (∀ j, constantCoeff (u j) = 0) → ∀ (g : MvPowerSeries τ Q) (n : σ →₀ ℕ) (S : Finset (τ →₀ ℕ)), (∀ α : τ →₀ ℕ, α.degree ≤ n.degree → α ∈ S) → MvPolynomial.eval (fun i => algebraMap B Q (z i)) (trunc' Q n (subst (up Q u) g)) = ∑ α ∈ S, coeff α g * algebraMap B Q (MvPolynomial.eval z (trunc' B n (α.prod fun j e => u j ^ e))) := by
  first | exact @GlobalTheory.DivSub.eval_trunc'_subst_eq_sum | exact GlobalTheory.DivSub.eval_trunc'_subst_eq_sum | (intros; apply GlobalTheory.DivSub.eval_trunc'_subst_eq_sum <;> assumption)
end

