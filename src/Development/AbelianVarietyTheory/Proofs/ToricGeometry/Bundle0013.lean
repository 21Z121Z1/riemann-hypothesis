import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.EqZeroOfForallAlgHomComplex
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

theorem eq_zero_of_forall_algHom_complex {A : Type*} [CommRing A] [Algebra ℂ A] [_root_.IsReduced A]
    [Algebra.FiniteType ℂ A] (a : A) (h : ∀ e : A →ₐ[ℂ] ℂ, e a = 0) : a = 0 := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℂ)
  have hrad : (⊥ : Ideal A).IsRadical := by
    rw [Ideal.isRadical_bot_iff]; infer_instance
  have hj : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out inferInstance hrad
  rw [← Ideal.mem_bot, ← hj, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ m)
  have hb : Function.Bijective (algebraMap ℂ (A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let i : ℂ ≃ₐ[ℂ] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId ℂ (A ⧸ m)) hb
  have := h ((i.symm : (A ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m))
  rw [AlgHom.comp_apply] at this
  have h2 : Ideal.Quotient.mkₐ ℂ m a = 0 := by
    apply i.symm.injective
    rw [map_zero]; exact this
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

theorem eq_of_valAt'_eq :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) →
    (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) →
    (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') := by
  intro hval haff X hred hft U f f' h
  refine TopCat.Sheaf.eq_of_locally_eq' X.left.sheaf
    (fun V : {V : X.left.Opens // IsAffineOpen V ∧ V ≤ U} => V.1) U (fun V => homOfLE V.2.2) ?_ f f' ?_
  · intro p hp
    obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVU⟩ :=
      X.left.isBasis_affineOpens.exists_subset_of_mem_open hp U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, hVU⟩, hpV⟩
  · rintro ⟨V, hV, hVU⟩
    change resG X.left hVU f = resG X.left hVU f'
    let c : ℂ →+* Γ(X.left, V) :=
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ V (fun _ _ => trivial)).hom
    have hc : c.FiniteType := by
      have h1 : (X.hom.appLE ⊤ V (fun _ _ => trivial)).hom.FiniteType :=
        HasRingHomProperty.appLE @LocallyOfFiniteType X.hom hft ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _
      exact h1.comp (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
    letI : Algebra ℂ Γ(X.left, V) := c.toAlgebra
    haveI : Algebra.FiniteType ℂ Γ(X.left, V) := hc
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_algHom_complex
    intro e
    obtain ⟨x, ⟨hxV, hx⟩, -⟩ := haff X V hV e.toRingHom (fun a => e.commutes a)
    have hres := (hval X.left x.left).2.2.1 U V hVU
    have hxU : ⊤ ≤ x.left ⁻¹ᵁ U := fun p hp => hVU (hxV hp)
    have e1 : e (resG X.left hVU f) = valAt' x.left U f := (hx _).symm.trans (hres f hxV)
    have e2 : e (resG X.left hVU f') = valAt' x.left U f' := (hx _).symm.trans (hres f' hxV)
    rw [map_sub, e1, e2, h x hxU, sub_self]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsAppellHumbertFrameIsRig
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

namespace OriginFrame

def ValRules : Prop :=
  ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)

theorem rigVal_ne_zero (hv : ValRules) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (s : Γ(X, U)ˣ) : valAt' x U s.val ≠ 0 := by
  intro h0
  obtain ⟨e, he⟩ := (hv X x).2.1 U h
  have key := congrArg e s.val_inv
  rw [map_mul, map_one, ← he, h0, zero_mul] at key
  exact zero_ne_one key

theorem rigChart_iff {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (L : LB X) (j : (L.pull x).ι) :
    ⊤ ≤ (L.pull x).U j ↔ ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit) := by
  delta LB.pull LB.LinComb LB.wchart
  constructor
  · intro h p _
    exact Set.mem_iInter.mp (h trivial) PUnit.unit
  · intro h p hp
    exact Set.mem_iInter.mpr (fun k => by cases k; exact h hp)

theorem rigVal_compat (hv : ValRules) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (L : LB X)
    (rig : LB.Gen (L.pull x)) (hr : rig.IsGen) (j j' : (L.pull x).ι)
    (hj : ⊤ ≤ (L.pull x).U j) (hj' : ⊤ ≤ (L.pull x).U j') :
    valAt' (𝟙 (Sp ℂ)) ((L.pull x).U j) (rig.s j).val =
      valAt' x (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) (L.g (j PUnit.unit) (j' PUnit.unit)).val *
        valAt' (𝟙 (Sp ℂ)) ((L.pull x).U j') (rig.s j').val := by
  unfold LB.Gen.IsGen at hr
  obtain ⟨hle, hg⟩ : ∃ hle : (L.pull x).U j ⊓ (L.pull x).U j' ≤ x ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)),
      (L.pull x).g j j' = res hle (pullU x _ (L.g (j PUnit.unit) (j' PUnit.unit))) := by
    delta LB.pull LB.LinComb
    dsimp only
    rw [Fintype.prod_unique, zpow_one]
    exact ⟨_, rfl⟩
  have hJ : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ ((L.pull x).U j ⊓ (L.pull x).U j') := by
    exact le_inf hj hj'
  obtain ⟨e, he⟩ := (hv (Sp ℂ) (𝟙 _)).2.1 _ hJ
  have hrj := congrArg (fun u => e (Units.val u)) (hr j j')
  rw [hg] at hrj
  rw [Units.val_mul, map_mul] at hrj
  simp only [← he] at hrj
  have eres : ∀ {U W : (Sp ℂ).Opens} (hh : W ≤ U) (u : (Γ(Sp ℂ, U))ˣ),
      ((res hh u : (Γ(Sp ℂ, W))ˣ) : Γ(Sp ℂ, W)) = resG (Sp ℂ) hh (u : Γ(Sp ℂ, U)) := fun _ _ => rfl
  have epu : ∀ (W : X.Opens) (u : (Γ(X, W))ˣ),
      ((pullU x W u : (Γ(Sp ℂ, x ⁻¹ᵁ W))ˣ) : Γ(Sp ℂ, x ⁻¹ᵁ W)) = (x.app W).hom (u : Γ(X, W)) := fun _ _ => rfl
  have r3 := fun U h f => (hv (Sp ℂ) (𝟙 (Sp ℂ))).2.2.1 U ((L.pull x).U j ⊓ (L.pull x).U j') h f hJ
  simp only [eres, epu, r3] at hrj
  rw [(hv (Sp ℂ) (𝟙 _)).2.2.2.1 X x, Category.id_comp] at hrj
  exact hrj

end OriginFrame

open OriginFrame in

theorem exists_appellHumbert_frame_isRig :
    Out.CubeSt → (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default
        : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X,
        U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X,
        U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ
        : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫
        φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X,
        U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U
        : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (A : Over (Sp
        ℂ)) [GrpObj A] [IsCommMonObj A] (L₀ L : LB A.left) (g : ℕ) (u
        : HolUnif A L₀ g), L.IsLB → ∀ t : LB.Gen (Theta A L), t.IsGen → ∀ (W : L.ι → Set (Fin g →
        ℂ)) (c : L.ι → L.ι → (Fin g → ℂ) → ℂ), W = (fun (i : L.ι) => {z : Fin g → ℂ | ⊤ ≤ (u.ex
        z).left ⁻¹ᵁ L.U i}) → c = (fun (i j : L.ι) (z : Fin g → ℂ) => valAt' (u.ex z).left (L.U i ⊓
        L.U j) (L.g i j).val) → ((∀ i, IsOpen (W i)) ∧ (∀ z, ∃ i, z ∈ W i) ∧
        (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) ∧ (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0)
        ∧ (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) ∧
        (∀ i z, ∀ l ∈ u.Λ, z + l ∈ W i ↔ z ∈ W i) ∧ (∀ i j z, ∀ l ∈ u.Λ, c i j (z +
        l) = c i j z)) ∧ ∃ T : (Finset (Fin 3) → L.ι) → (Fin 3 → Fin g →
        ℂ) → ℂ, (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j
        I))}) ∧ (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j
        I)) → T j x ≠ 0) ∧ (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j
        I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j
        I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) ∧ (∀ j x (l
        : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ u.Λ) → T j (x + l) = T j x)) → (∀ (g : ℕ) {J : Type} (W
        : J → Set (Fin g → ℂ)) (c : J → J → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W
        i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W
        j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T
        : (Finset (Fin 3) → J) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x
        | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j'
        I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 -
        I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g →
        ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g →
        ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z +
        l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x) → ∃ (r
        : ℝ) (fr : J → (Fin g → ℂ) → ℂ) (κ : ℂ), 0 < r ∧ ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩
        Metric.ball 0 r)) ∧ (∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0) ∧
        (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)) ∧ ∀ᶠ x in 𝓝 (0
        : Fin 3 → Fin g → ℂ), ∀ j, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j
        I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 -
        I.card))) → (∀ (g : ℕ) {J : Type} (W : J → Set (Fin g → ℂ)) (c : J → J → (Fin g →
        ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i
        ∩ W
        j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T
        : (Finset (Fin 3) → J) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x
        | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j'
        I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 -
        I.card))) * T j' x) → (∃ (r : ℝ) (fr : J → (Fin g → ℂ) → ℂ) (κ
        : ℂ), 0 < r ∧ ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Metric.ball 0 r)) ∧
        (∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0) ∧
        (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)) ∧ ∀ᶠ x in 𝓝 (0
        : Fin 3 → Fin g → ℂ), ∀ j, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j
        I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 -
        I.card))) → ∃ (fr : J → (Fin g → ℂ) → ℂ) (κ : ℂ), ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩
        Set.univ)) ∧ (∀ i z, z ∈ W i → z ∈ Set.univ → fr i z ≠ 0) ∧
        (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Set.univ → fr i z = c i j z * fr j z)) ∧ ∀ j x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j
        I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) → (∀ (g : ℕ) {J : Type} (W : J → Set (Fin g →
        ℂ)) (c : J → J → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W
        i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W
        j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T
        : (Finset (Fin 3) → J) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x
        | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j'
        I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 -
        I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g →
        ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g →
        ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z +
        l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x +
        l) = T j x) → ∀ (fr : J → (Fin g → ℂ) → ℂ) (κ : ℂ), ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩
        Set.univ)) ∧ (∀ i z, z ∈ W i → z ∈ Set.univ → fr i z ≠ 0) ∧
        (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Set.univ → fr i z = c i j z * fr j z)) → (∀ j x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j
        I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) → ∃ (a : Λ → ℂ) (B : Λ →+ ((Fin g → ℂ) →ₗ[ℂ]
        ℂ)), (∀ l, a l ≠ 0) ∧ (∀ l m : Λ, a (l + m) = a l * a m * cexp (B l m)) ∧ ∀ (l
        : Λ) i z, z ∈ W i → fr i z = a l * cexp (B l z) * fr i (z + l)) → (∀ (g : ℕ) (Λ
        : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g →
        ℂ)) = ⊤ → ∀ (a : Λ → ℂ) (B : Λ →+ ((Fin g → ℂ) →ₗ[ℂ] ℂ)), (∀ l, a l ≠ 0) → (∀ l m : Λ, a (l
        + m) = a l * a m * cexp (B l m)) → ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ Λ) (Q : (Fin g →
        ℂ) → ℂ), Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ
        Hm.mulVec (star (m : Fin g → ℂ))).im) ∧ Differentiable ℂ Q ∧ Q 0 = 0 ∧ ∀ (l
        : Λ) z, a l * cexp (B l z) * cexp (Q z - Q (z + l)) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec
        (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin g → ℂ)))))) → (∀ (P : Out.PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec
        P.A))), rig.IsGen → ∀ u₀ : HolUnif P.A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩
        : LB P.A.left) P.g, ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ
        : u.Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ u.Λ), u.ex = u₀.ex ∧ u.IsRig rig ∧ Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef
        l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l
        : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ
        Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin P.g → ℂ))))) * u.fr i (z + l)) := by
  intro hCube hV hFrame hLoc hGlob hFact hNorm P rig hrig u₀
  have hLB : P.L.IsLB := P.7
  obtain ⟨cs⟩ := (hCube (Sp ℂ) P ⟨P.L, rig, hLB, hrig⟩ rfl).1
  obtain ⟨W, hW⟩ : ∃ W : P.L.ι → Set (Fin P.g → ℂ),
      W = fun i => {z | ⊤ ≤ (u₀.ex z).left ⁻¹ᵁ P.L.U i} := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : P.L.ι → P.L.ι → (Fin P.g → ℂ) → ℂ,
      c = fun i j z => valAt' (u₀.ex z).left (P.L.U i ⊓ P.L.U j) (P.L.g i j).val := ⟨_, rfl⟩
  have memW : ∀ i z, z ∈ W i ↔ ⊤ ≤ (u₀.ex z).left ⁻¹ᵁ P.L.U i := by
    intro i z
    rw [hW]
    exact Iff.rfl
  obtain ⟨⟨hWo, hWc, hcd, hcn, hcc, hWp, hcp⟩, T, hT1, hT2, hT3, hT4⟩ :=
    hFrame P.A _ P.L P.g u₀ hLB cs.t cs.2 W c hW hc
  have hloc := hLoc P.g W c hWo hWc hcd hcn hcc T hT1 hT2 hT3 u₀.Λ u₀.discrete u₀.full hWp hcp hT4
  obtain ⟨fr, κ, ⟨hfrd, hfrn, hfrc⟩, hTfr⟩ := hGlob P.g W c hWo hWc hcd hcn hcc T hT1 hT2 hT3 hloc
  obtain ⟨a, B, ha, hab, hfa⟩ :=
    hFact P.g W c hWo hWc hcd hcn hcc T hT1 hT2 hT3 u₀.Λ u₀.discrete u₀.full hWp hcp hT4 fr κ
      ⟨hfrd, hfrn, hfrc⟩ hTfr
  obtain ⟨Hm, χ, Ef, Q, hH, hχ, hEf, hQd, _, hQ⟩ := hNorm P.g u₀.Λ u₀.discrete u₀.full a B ha hab

  have hex0 : u₀.ex 0 = 1 := (u₀.ker 0).2 (Submodule.zero_mem _)
  have he0 : (u₀.ex 0).left = eSec P.A := by
    simp only [hex0, CategoryTheory.Hom.one_def, toUnit_unit, Category.id_comp]
    rfl
  obtain ⟨i₀, h₀⟩ := hWc 0
  have hjj : ⊤ ≤ (P.L.pull (eSec P.A)).U (fun _ => i₀ : PUnit.{1} → P.L.ι) :=
    (OriginFrame.rigChart_iff (eSec P.A) P.L (fun _ => i₀ : PUnit.{1} → P.L.ι)).2 (by rw [← he0]; exact (memW _ _).1 h₀)
  have hjj' : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ (P.L.pull (eSec P.A)).U (fun _ => i₀ : PUnit.{1} → P.L.ι) := by
    exact hjj
  have hvne := OriginFrame.rigVal_ne_zero hV (𝟙 (Sp ℂ)) _ hjj' (rig.s (fun _ => i₀ : PUnit.{1} → P.L.ι))
  clear hFrame hLoc hGlob hFact hNorm hCube hT1 hT2 hT3 hT4 hloc hTfr hcd hcn hcc hWp hcp hWo hWc hab
  have hF : fr i₀ 0 * Complex.exp (Q 0) ≠ 0 := mul_ne_zero (hfrn i₀ 0 h₀ trivial) (Complex.exp_ne_zero _)
  have hlam : valAt' (𝟙 (Sp ℂ)) ((P.L.pull (eSec P.A)).U (fun _ => i₀ : PUnit.{1} → P.L.ι)) (rig.s (fun _ => i₀ : PUnit.{1} → P.L.ι)).val /
      (fr i₀ 0 * Complex.exp (Q 0)) ≠ 0 := div_ne_zero hvne hF
  refine ⟨{
      ex := u₀.ex
      ex_add := u₀.ex_add
      ex_onto := u₀.ex_onto
      Λ := u₀.Λ
      ker := u₀.ker
      discrete := u₀.discrete
      full := u₀.full
      hol := u₀.hol
      fr := fun i z => valAt' (𝟙 (Sp ℂ)) ((P.L.pull (eSec P.A)).U (fun _ => i₀ : PUnit.{1} → P.L.ι)) (rig.s (fun _ => i₀ : PUnit.{1} → P.L.ι)).val /
        (fr i₀ 0 * Complex.exp (Q 0)) * (fr i z * Complex.exp (Q z))
      fr_hol := ?_
      fr_ne := ?_
      fr_compat := ?_ }, Hm, χ, Ef, rfl, ?_, hH, hχ, hEf, ?_⟩
  · intro i
    refine (((hfrd i).mono fun z hz => ⟨(memW i z).2 hz, trivial⟩).mul
      hQd.cexp.differentiableOn).const_mul _
  · intro i z hz
    exact mul_ne_zero hlam (mul_ne_zero (hfrn i z ((memW i z).2 hz) trivial) (Complex.exp_ne_zero _))
  · intro i j z hz
    have hp := ((hV _ (u₀.ex z).left).1 _).1 hz
    have hzi : z ∈ W i := (memW i z).2 (((hV _ _).1 _).2 hp.1)
    have hzj : z ∈ W j := (memW j z).2 (((hV _ _).1 _).2 hp.2)
    have h1 := hfrc i j z hzi hzj trivial
    rw [hc] at h1
    dsimp only at h1 ⊢
    rw [h1]
    ring
  · intro j hj
    have hj0 : 0 ∈ W (j PUnit.unit) :=
      (memW _ _).2 (by rw [he0]; exact (OriginFrame.rigChart_iff (eSec P.A) P.L j).1 hj)
    have hcomp := OriginFrame.rigVal_compat hV (eSec P.A) P.L rig hrig j (fun _ => i₀ : PUnit.{1} → P.L.ι) hj hjj
    have hfc := hfrc (j PUnit.unit) i₀ 0 hj0 h₀ trivial
    rw [hc] at hfc
    dsimp only at hfc ⊢
    rw [hcomp, hfc, he0, div_mul_eq_mul_div, div_eq_iff hF]
    ring
  · intro l i z hz
    have hzW : z ∈ W i := (memW i z).2 hz
    dsimp only at hz ⊢
    have hE := Complex.exp_ne_zero (Q (z + l))
    rw [← hQ l z, hfa l i z hzW, Complex.exp_sub]
    field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.PowSec

section Transport

variable {X Y : Scheme.{0}} (L : LB X) (σ : Y ⟶ X) (ρ : X ⟶ Y) (e : ρ ≫ σ = 𝟙 X) (n : ℤ)

include e in
theorem chart_eq (j : PUnit → L.ι) :
    LB.wchart L (fun _ : PUnit => 𝟙 X) j = ρ ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit) := by
  ext y
  have h : σ (ρ y) = y := by rw [← Scheme.Hom.comp_apply, e]; rfl
  constructor
  · intro hy
    refine Set.mem_iInter.2 fun _ => ?_
    have := Set.mem_iInter.1 hy PUnit.unit
    show σ (ρ y) ∈ L.U (j PUnit.unit)
    rw [h]; exact this
  · intro hy
    refine Set.mem_iInter.2 fun _ => ?_
    have : σ (ρ y) ∈ L.U (j PUnit.unit) := Set.mem_iInter.1 hy 0
    rw [h] at this; exact this

theorem appLE_congr {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (h₁ : V ≤ f ⁻¹ᵁ U) (h₂ : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V h₁ = g.appLE U V h₂ := by subst h; rfl

def down (b : (LB.LinComb L (K := Fin 1) (fun _ => σ) (fun _ => n)).Sec) :
    (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => n)).Sec where
  f j := (ρ.appLE _ _ (chart_eq L σ ρ e j).le).hom (b.f (fun _ => j PUnit.unit))
  compat i j := by
    have hle : LB.wchart L (fun _ : PUnit => 𝟙 X) i ⊓ LB.wchart L (fun _ : PUnit => 𝟙 X) j ≤
      ρ ⁻¹ᵁ (LB.wchart L (fun _ : Fin 1 => σ) (fun _ => i PUnit.unit) ⊓
        LB.wchart L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit)) :=
      inf_le_inf (chart_eq L σ ρ e i).le (chart_eq L σ ρ e j).le
    have := congrArg (ρ.appLE _ _ hle).hom (b.compat (fun _ => i PUnit.unit) (fun _ => j PUnit.unit))
    replace this := this.trans (map_mul _ _ _)
    refine Eq.trans ?_ (this.trans (congrArg₂ (· * ·) ?_ ?_))
    · exact (congrArg (fun φ => φ.hom (b.f fun _ => i PUnit.unit))
        ((Scheme.Hom.appLE_map ρ _ _).trans (Scheme.Hom.map_appLE ρ hle _).symm) :)
    · simp only [LB.LinComb, Fintype.prod_unique]
      refine (congrArg Units.val ((map_zpow (Units.map (ρ.appLE _ _ hle).hom.toMonoidHom) _ n).trans
        (congrArg (· ^ n) (Units.ext ?_))) :)
      have h1 : (σ.app (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ≫ Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : Fin 1 => σ) (fun _ => i PUnit.unit) 0))
          (inf_le_right.trans (LB.wchart_le L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit) 0)))).op) ≫ ρ.appLE _ _ hle =
          (𝟙 X : X ⟶ X).app (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ≫ X.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => 𝟙 X) i PUnit.unit))
          (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => 𝟙 X) j PUnit.unit)))).op :=
        (Scheme.Hom.appLE_comp_appLE ρ σ _ _ _ _ hle).trans (appLE_congr e _ _ _ _)
      exact congrArg (fun φ => φ.hom (L.g (i PUnit.unit) (j PUnit.unit)).val) h1
    · exact (congrArg (fun φ => φ.hom (b.f fun _ => j PUnit.unit))
        ((Scheme.Hom.map_appLE ρ hle _).trans (Scheme.Hom.appLE_map ρ _ _).symm) :)

theorem appLE_injective [IsIso ρ] (U : Y.Opens) (V : X.Opens) (h : V = ρ ⁻¹ᵁ U) :
    Function.Injective (ρ.appLE U V h.le).hom := by
  subst h
  rw [Scheme.Hom.appLE_eq_app]
  exact (ConcreteCategory.bijective_of_isIso (ρ.app U)).1

end Transport

attribute [local instance] Over.cartesianMonoidalCategory

open Out in

theorem exists_indep_sections (H : Out.GlobalSectionsRankAlgClosed) (P : Out.PolAV (Sp ℂ)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ s : Fin (n ^ P.g) → (lbPow P.L n).Sec, ∀ a : Fin (n ^ P.g) → ℂ,
      (∀ j, ∑ i, constFn P.A.hom _ (a i) * (s i).f j = 0) → a = 0 := by
  have hr := H ℂ P n hn
  let T : Over (Sp ℂ) := baseOver (Sp ℂ)
  let c : Γ(T.left, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
  haveI : Nontrivial Γ(T.left, ⊤) := c.symm.injective.nontrivial
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_finrank (R := Γ(T.left, ⊤)) (M := SecM P.A P.L n T) hr.ge
  let ρ : P.A ⟶ T ⊗ P.A := lift (Over.homMk P.A.hom (Category.comp_id _)) (𝟙 _)
  have ρ₂ : ρ.left ≫ (snd T P.A).left = 𝟙 _ := congrArg (fun q => q.left) (lift_snd _ _ : ρ ≫ _ = _)
  have ρ₁ : ρ.left ≫ (fst T P.A).left = P.A.hom := congrArg (fun q => q.left) (lift_fst _ _ : ρ ≫ _ = _)
  have ρ₃ : (snd T P.A).left ≫ ρ.left = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans (pullback.condition.symm.trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  haveI : IsIso ρ.left := ⟨_, ρ₂, ρ₃⟩
  refine ⟨fun i => down P.L (snd T P.A).left ρ.left ρ₂ n (SecM.toSec P.A (b i)), fun a ha => ?_⟩
  have h0 : ∑ i, c.symm (a i) • b i = 0 := by
    refine Subtype.ext (funext fun j => ?_)
    obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    refine appLE_injective ρ.left _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)) ?_
    refine Eq.trans ?_ ((ha (fun _ => k)).trans (map_zero _).symm)
    rw [Submodule.coe_sum]
    refine (congrArg _ (Finset.sum_apply _ _ _)).trans ?_
    refine (map_sum (ρ.left.appLE _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)).le).hom _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
    refine (map_mul _ (liftHom P.A _ (c.symm (a i))) ((b i).1 fun _ => k)).trans (congrArg₂ (· * ·) ?_ rfl)
    have h1 := (Scheme.Hom.appLE_comp_appLE ρ.left (fst T P.A).left ⊤ _ _ (fun _ _ => trivial)
      (chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)).le).trans (appLE_congr ρ₁ ⊤ _ _ (fun _ _ => trivial))
    exact congrArg (fun φ => φ.hom (c.symm (a i))) h1
  funext i
  exact c.symm.injective ((Fintype.linearIndependent_iff.1 hb _ h0 i).trans (map_zero _).symm)

end GlobalTheory.PowSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.AffinePointValues

lemma appLE_specMap_fromSpec {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R : CommRingCat.{0}}
    (f : Γ(Y, V) ⟶ R) (e) :
    (Spec.map f ≫ hV.fromSpec).appLE V ⊤ e ≫ (Scheme.ΓSpecIso R).hom = f := by

  apply Spec.map_injective
  rw [← cancel_mono hV.fromSpec, Spec.map_comp, Category.assoc,
    IsAffineOpen.SpecMap_appLE_fromSpec _ hV (isAffineOpen_top _) e,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

lemma specMap_appLE_fromSpec {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R : CommRingCat.{0}}
    (x : Spec R ⟶ Y) (hx : ⊤ ≤ x ⁻¹ᵁ V) :
    Spec.map (x.appLE V ⊤ hx ≫ (Scheme.ΓSpecIso R).hom) ≫ hV.fromSpec = x := by
  rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec x hV (isAffineOpen_top _) hx,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

lemma fromSpec_comp {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R : CommRingCat.{0}}
    (s : Y ⟶ Spec R) (h) :
    hV.fromSpec ≫ s = Spec.map ((Scheme.ΓSpecIso R).inv ≫ s.appLE ⊤ V h) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top _) hV h,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, Spec.map_comp]

end GlobalTheory.AffinePointValues

namespace GlobalTheory

open AffinePointValues in

theorem existsUnique_point_of_ringHom :
    (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) := by
  intro X U hU e he
  let φ : Γ(X.left, U) ⟶ CommRingCat.of ℂ := CommRingCat.ofHom e

  have hconst : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ U (fun _ _ => trivial) ≫ φ =
      𝟙 _ := by
    ext a
    exact he a
  have hw : (Spec.map φ ≫ hU.fromSpec) ≫ X.hom = (𝟙_ (Over (Sp ℂ))).hom := by
    rw [Category.assoc, fromSpec_comp hU X.hom (fun _ _ => trivial), ← Spec.map_comp,
      Category.assoc, hconst, Spec.map_id]
    rfl
  have hpre : ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ U := by
    intro p _
    show hU.fromSpec.base ((Spec.map φ).base p) ∈ U
    have h : (Spec.map φ).base p ∈ hU.fromSpec ⁻¹ᵁ U := by
      rw [IsAffineOpen.fromSpec_preimage_self]; trivial
    exact h
  refine ⟨Over.homMk (Spec.map φ ≫ hU.fromSpec) hw, ⟨hpre, fun f => ?_⟩, ?_⟩
  · show valAt' (Spec.map φ ≫ hU.fromSpec) U f = e f
    rw [valAt', dif_pos hpre]
    exact congrArg (fun g => g.hom f) (appLE_specMap_fromSpec hU φ hpre)
  · rintro y ⟨hy, hv⟩
    apply Over.OverMorphism.ext
    have h1 : y.left.appLE U ⊤ hy ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = φ := by
      ext f
      have := hv f
      rw [valAt', dif_pos hy] at this
      exact this
    rw [← specMap_appLE_fromSpec hU y.left hy, h1]
    rfl

end GlobalTheory
end
end

