import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0057

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankSymmCommutantKroneckerLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.SymmCommutant

open Matrix in

theorem entry_of_commute {K : Type} [Field K] {h : ℕ}
    (Ψ : Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K)
    (H : ∀ v : Fin 8, Matrix.kronecker (Matrix.single (0 : Fin 8) v (1 : K))
        (1 : Matrix (Fin h) (Fin h) K) * Ψ =
      Ψ * Matrix.kronecker (Matrix.single (0 : Fin 8) v (1 : K)) (1 : Matrix (Fin h) (Fin h) K))
    (v b : Fin 8) (i j : Fin h) :
    Ψ (v, i) (b, j) = if v = b then Ψ (0, i) (0, j) else 0 := by
  have := congrFun (congrFun (H v) (0, i)) (b, j)
  simpa [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.single_apply, Matrix.one_apply, ite_and] using this

open Matrix in
theorem core {K : Type} [Field K] {h : ℕ} (A B : Matrix (Fin 8) (Fin 8) K)
    (hA : A.IsSymm) (hBA : B * A = 1)
    (Θ : Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K) (hΘ : Θ.IsSymm)
    (H : ∀ v : Fin 8, Matrix.kronecker (Matrix.single (0 : Fin 8) v (1 : K))
        (1 : Matrix (Fin h) (Fin h) K) * Θ =
      Θ * (Matrix.kronecker (B * (Matrix.single (0 : Fin 8) v (1 : K)).transpose * A)
        (1 : Matrix (Fin h) (Fin h) K)).transpose) :
    (∀ a b i j, Θ (a, i) (b, j) =
      B a b * (Θ * Matrix.kronecker A (1 : Matrix (Fin h) (Fin h) K)) (0, i) (0, j)) ∧
    ∀ i j, (Θ * Matrix.kronecker A (1 : Matrix (Fin h) (Fin h) K)) (0, i) (0, j) =
      (Θ * Matrix.kronecker A (1 : Matrix (Fin h) (Fin h) K)) (0, j) (0, i) := by
  have hAB : A * B = 1 := mul_eq_one_comm.mp hBA
  have hBtA : Bᵀ * A = 1 := by
    have : (Aᵀ * B)ᵀ = 1 := by rw [hA.eq, hAB, Matrix.transpose_one]
    simpa [Matrix.transpose_mul] using this
  have kmul : ∀ X Y : Matrix (Fin 8) (Fin 8) K,
      Matrix.kronecker X (1 : Matrix (Fin h) (Fin h) K) *
        Matrix.kronecker Y (1 : Matrix (Fin h) (Fin h) K) =
      Matrix.kronecker (X * Y) (1 : Matrix (Fin h) (Fin h) K) := by
    intro X Y
    simp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  have ktr : ∀ X : Matrix (Fin 8) (Fin 8) K,
      (Matrix.kronecker X (1 : Matrix (Fin h) (Fin h) K))ᵀ =
      Matrix.kronecker Xᵀ (1 : Matrix (Fin h) (Fin h) K) := by
    intro X
    simp only [Matrix.kronecker]
    rw [← Matrix.kroneckerMap_transpose, Matrix.transpose_one]
  set Ψ := Θ * Matrix.kronecker A (1 : Matrix (Fin h) (Fin h) K) with hΨ
  have hc : ∀ v : Fin 8, Matrix.kronecker (Matrix.single (0 : Fin 8) v (1 : K))
        (1 : Matrix (Fin h) (Fin h) K) * Ψ =
      Ψ * Matrix.kronecker (Matrix.single (0 : Fin 8) v (1 : K))
        (1 : Matrix (Fin h) (Fin h) K) := by
    intro v
    rw [hΨ, ← Matrix.mul_assoc, H v, ktr, Matrix.mul_assoc, Matrix.mul_assoc Θ, kmul, kmul]
    congr 2
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hA.eq,
      Matrix.mul_assoc, Matrix.mul_assoc, hBtA, Matrix.mul_one]
  have he := entry_of_commute Ψ hc
  have hΘΨ : Θ = Ψ * Matrix.kronecker B (1 : Matrix (Fin h) (Fin h) K) := by
    rw [hΨ, Matrix.mul_assoc, kmul, hAB]
    simp [Matrix.kronecker]
  have h1 : ∀ a b i j, Θ (a, i) (b, j) = B a b * Ψ (0, i) (0, j) := by
    intro a b i j
    have := congrFun (congrFun hΘΨ (a, i)) (b, j)
    rw [this, Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [he a]
    simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply, mul_comm]
  refine ⟨h1, fun i j => ?_⟩
  have h00 : ∑ b, A 0 b * B b 0 = 1 := by
    have := congrFun (congrFun hAB 0) 0
    simpa [Matrix.mul_apply] using this
  calc Ψ (0, i) (0, j) = ∑ b, Θ (0, i) (b, j) * A b 0 := by
        rw [hΨ, Matrix.mul_apply, Fintype.sum_prod_type]
        simp [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply]
    _ = ∑ b, (A 0 b * B b 0) * Ψ (0, j) (0, i) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← hΘ.apply (0, i) (b, j), h1, hA.apply b 0]
        ring
    _ = Ψ (0, j) (0, i) := by rw [← Finset.sum_mul, h00, _root_.one_mul]

end GlobalTheory.ZM.SymmCommutant

namespace GlobalTheory.ZM

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private lemma entry_eq_sum_of_mul_eq_mul_kronecker (K : Type) [Field K] (h : ℕ)
    (Ei Em : Matrix (Fin 8) (Fin 8) ℤ) (Θ : Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K)
    (hΘ : ∀ u v : Fin 8, Matrix.kronecker ((Matrix.single u v (1 : ℤ)).map (Int.cast : ℤ → K))
      (1 : Matrix (Fin h) (Fin h) K) * Θ = Θ * (Matrix.kronecker ((Ei * (Matrix.single u v
      (1 : ℤ)).transpose * Em).map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K)).transpose)
    (v c : Fin 8) (i j : Fin h) :
    Θ (v, i) (c, j) = (Ei c v : K) * ∑ d, Θ (0, i) (d, j) * (Em 0 d : K) := by
  have hX : ∀ u v : Fin 8, (Ei * (Matrix.single u v (1 : ℤ)).transpose * Em).map
      (Int.cast : ℤ → K) = Matrix.of fun c d => (Ei c v : K) * (Em u d : K) := by
    intro u v; ext c d
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.transpose_apply, Finset.sum_ite_eq',
      Finset.sum_ite_eq, ite_and]
  have hA : ∀ u v : Fin 8, (Matrix.single u v (1 : ℤ)).map (Int.cast : ℤ → K) =
      Matrix.single u v (1 : K) := by
    intro u v; ext a b
    simp only [Matrix.map_apply, Matrix.single_apply]
    split_ifs <;> simp
  have e := congrFun (congrFun (hΘ 0 v) (0, i)) (c, j)
  rw [hA, hX] at e
  simp only [Matrix.mul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.transpose_apply,
    Matrix.of_apply, Fintype.sum_prod_type, Matrix.single_apply, Matrix.one_apply] at e
  simpa [Finset.mul_sum, _root_.mul_comm, _root_.mul_left_comm, _root_.mul_assoc] using e

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

theorem _root_.GlobalTheory.ZM.finrank_symm_commutant_le : ∀ (K : Type) [Field K] (h : ℕ) (Em Ei : Matrix (Fin 8) (Fin 8) ℤ) (V : Submodule K (Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K)), Em.IsSymm → Ei * Em = 1 → (∀ Θ ∈ V, Θ.IsSymm ∧ ∀ u v : Fin 8, Matrix.kronecker ((Matrix.single u v (1 : ℤ)).map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K) * Θ = Θ * (Matrix.kronecker ((Ei * (Matrix.single u v (1 : ℤ)).transpose * Em).map (Int.cast : ℤ → K)) (1 : Matrix (Fin h) (Fin h) K)).transpose) → Module.finrank K V ≤ h * (h + 1) / 2 := by
  intro K _ h Em Ei V hEm hEiEm hV
  let B : Matrix (Fin 8 × Fin h) (Fin 8 × Fin h) K → Fin h → Fin h → K :=
    fun Θ i j => ∑ d, Θ (0, i) (d, j) * (Em 0 d : K)
  have key : ∀ Θ ∈ V, ∀ v c i j, Θ (v, i) (c, j) = (Ei c v : K) * B Θ i j :=
    fun Θ hΘ v c i j => entry_eq_sum_of_mul_eq_mul_kronecker K h Ei Em Θ (hV Θ hΘ).2 v c i j
  have hsum : ∑ d, (Ei 0 d : K) * (Em 0 d : K) = 1 := by
    have e := congrFun (congrFun hEiEm 0) 0
    simp only [Matrix.mul_apply, Matrix.one_apply_eq] at e
    have e' : ∑ d, Ei 0 d * Em 0 d = 1 := by
      rw [← e]; exact Finset.sum_congr rfl fun d _ => by rw [hEm.apply 0 d]
    have e'' := congrArg (Int.cast : ℤ → K) e'
    push_cast at e''
    exact e''
  have symmB : ∀ Θ ∈ V, ∀ i j, B Θ i j = B Θ j i := by
    intro Θ hΘ i j
    calc B Θ i j = ∑ d, (Ei 0 d : K) * B Θ j i * (Em 0 d : K) :=
          Finset.sum_congr rfl fun d _ => by
            rw [← key Θ hΘ d 0 j i, (hV Θ hΘ).1.apply (0, i) (d, j)]
      _ = B Θ j i * ∑ d, (Ei 0 d : K) * (Em 0 d : K) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by ring
      _ = B Θ j i := by rw [hsum, _root_.mul_one]
  let L : V →ₗ[K] (Sym2 (Fin h) → K) :=
    { toFun := fun Θ s => B Θ (Quot.out s).1 (Quot.out s).2
      map_add' := by
        intro x y; funext s
        simp [B, Finset.sum_add_distrib, add_mul]
      map_smul' := by
        intro r x; funext s
        simp [B, Finset.mul_sum, _root_.mul_assoc] }
  have inj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro Θ hΘ0
    have hB : ∀ i j, B Θ i j = 0 := by
      intro i j
      have hs := congrFun hΘ0 s(i, j)
      have hout : s((Quot.out s(i, j)).1, (Quot.out s(i, j)).2) = s(i, j) := Quot.out_eq _
      rcases Sym2.eq_iff.1 hout with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : B Θ (Quot.out s(i, j)).1 (Quot.out s(i, j)).2 = 0 := hs
        rwa [h1, h2] at this
      · have : B Θ (Quot.out s(i, j)).1 (Quot.out s(i, j)).2 = 0 := hs
        rw [h1, h2] at this
        rwa [symmB Θ Θ.2] at this
    apply Subtype.ext
    ext ⟨v, i⟩ ⟨c, j⟩
    rw [key Θ Θ.2, hB]
    simp
  calc Module.finrank K V ≤ Module.finrank K (Sym2 (Fin h) → K) :=
        LinearMap.finrank_le_finrank_of_injective inj
    _ = h * (h + 1) / 2 := by
        rw [Module.finrank_fintype_fun_eq_card, Sym2.card, Fintype.card_fin, Nat.choose_two_right,
          Nat.add_sub_cancel, mul_comm]

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.IsGaloisCover

theorem exists_algClosed_point (T : Scheme.{0}) (p : T) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (j : Sp K ⟶ T), p ∈ Set.range j := by
  let k := T.residueField p
  let K := AlgebraicClosure k
  let i : Spec (CommRingCat.of K) ⟶ Spec k := Spec.map (CommRingCat.ofHom (algebraMap k K))
  refine ⟨K, inferInstance, inferInstance, i ≫ T.fromSpecResidueField p, ?_⟩
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  refine ⟨z, ?_⟩
  have hz : (T.fromSpecResidueField p) (i z) ∈ Set.range (T.fromSpecResidueField p) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecResidueField] at hz
  rw [Scheme.Hom.comp_apply]
  exact Set.mem_singleton_iff.mp hz

variable {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)}

theorem exists_local_geom (h : IsGaloisCover Ga ρ π) {T : Scheme.{0}} (x x' : T ⟶ X) (hx : x ≫ π = x' ≫ π) (p : T) :
    ∃ (V : T.Opens) (a : Ga), p ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x' := by
  have := h.etale
  let D := pullback.diagonal π
  let m : Ga → (T ⟶ pullback π π) := fun a =>
    pullback.lift (x ≫ ρ a) x' (by rw [Category.assoc, h.inv a, hx])
  obtain ⟨K, _, _, j, z, hz⟩ := exists_algClosed_point T p
  obtain ⟨a, ha, -⟩ := h.fibre K (j ≫ x) (j ≫ x') (by simp only [Category.assoc, hx])
  have hm1 : m a ≫ pullback.fst π π = x ≫ ρ a := pullback.lift_fst _ _ _
  have hm2 : m a ≫ pullback.snd π π = x' := pullback.lift_snd _ _ _
  have hjm : j ≫ m a = j ≫ x' ≫ D := by
    apply pullback.hom_ext
    · rw [Category.assoc, hm1, Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id]
      simpa only [Category.assoc] using ha
    · rw [Category.assoc, hm2, Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id]
  let V : T.Opens := (m a) ⁻¹ᵁ D.opensRange
  have hpV : p ∈ V := by
    show (m a) p ∈ Set.range D
    rw [← hz]
    refine ⟨x' (j z), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hjm]
  have hsub : Set.range (V.ι ≫ m a) ⊆ Set.range D := by
    rintro _ ⟨w, rfl⟩
    have hw : V.ι w ∈ (V : Set T) := by
      rw [← Scheme.Opens.range_ι V]
      exact ⟨w, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hw
  let l := IsOpenImmersion.lift D (V.ι ≫ m a) hsub
  have hl : l ≫ D = V.ι ≫ m a := IsOpenImmersion.lift_fac _ _ _
  refine ⟨V, a, hpV, ?_⟩
  have e1 : V.ι ≫ x ≫ ρ a = l := by
    have h1 : l ≫ D ≫ pullback.fst π π = l := by rw [pullback.diagonal_fst, Category.comp_id]
    rw [← h1, ← Category.assoc l, hl, Category.assoc, hm1]
  have e2 : V.ι ≫ x' = l := by
    have h2 : l ≫ D ≫ pullback.snd π π = l := by rw [pullback.diagonal_snd, Category.comp_id]
    rw [← h2, ← Category.assoc l, hl, Category.assoc, hm2]
  rw [e1, e2]

theorem existsUnique_desc (h : IsGaloisCover Ga ρ π) {Z : Scheme.{0}} (f : X ⟶ Z) (hf : ∀ a, ρ a ≫ f = f) :
    ∃! f' : Y ⟶ Z, π ≫ f' = f := by
  have := h.fin
  have := h.etale
  have := h.onto
  have key : ∀ {W : Scheme.{0}} (g₁ g₂ : W ⟶ X), g₁ ≫ π = g₂ ≫ π → g₁ ≫ f = g₂ ≫ f := by
    intro W g₁ g₂ hg
    apply Scheme.hom_ext_of_forall
    intro p
    obtain ⟨V, a, hp, hV⟩ := h.exists_local_geom g₁ g₂ hg p
    refine ⟨V, hp, ?_⟩
    calc V.ι ≫ g₁ ≫ f = V.ι ≫ g₁ ≫ ρ a ≫ f := by rw [hf]
      _ = (V.ι ≫ g₁ ≫ ρ a) ≫ f := by simp only [Category.assoc]
      _ = V.ι ≫ g₂ ≫ f := by rw [hV, Category.assoc]
  refine ⟨EffectiveEpi.desc π f key, EffectiveEpi.fac π f key, ?_⟩
  intro f' hf'
  apply (cancel_epi π).1
  rw [hf', EffectiveEpi.fac]

variable {X' Y' : Scheme.{0}} {π' : X' ⟶ Y'} {ρ' : Ga → (X' ⟶ X')} {u : X' ⟶ X} {v : Y' ⟶ Y}

private theorem existsUnique_act_of_isPullback_isGaloisCover (h : IsGaloisCover Ga ρ π) (hp : IsPullback u π' π v)
    (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a) (hπ : ∀ a, ρ' a ≫ π' = π') (K : Type) [Field K] [IsAlgClosed K]
    (y y' : Sp K ⟶ X') (hy : y ≫ π' = y' ≫ π') : ∃! a, y ≫ ρ' a = y' := by
  have hyu : (y ≫ u) ≫ π = (y' ≫ u) ≫ π := by
    simp only [Category.assoc, hp.w, reassoc_of% hy]
  obtain ⟨a, ha, hauniq⟩ := h.fibre K (y ≫ u) (y' ≫ u) hyu
  refine ⟨a, ?_, ?_⟩
  · apply hp.hom_ext
    · rw [Category.assoc, hu, ← Category.assoc, ha]
    · rw [Category.assoc, hπ, hy]
  · intro b hb
    apply hauniq
    rw [Category.assoc, ← hu, ← Category.assoc, hb]

theorem isPullback (h : IsGaloisCover Ga ρ π) (h' : IsGaloisCover Ga ρ' π') (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a)
    (w : u ≫ π = π' ≫ v) : IsPullback u π' π v := by
  have := h.fin
  have := h.etale
  have := h.onto
  have := h'.fin
  have := h'.etale
  let ρP : Ga → (pullback π v ⟶ pullback π v) := fun a =>
    pullback.map π v π v (ρ a) (𝟙 Y') (𝟙 Y) (by rw [Category.comp_id, h.inv]) (by rw [Category.comp_id, Category.id_comp])
  have huP : ∀ a, ρP a ≫ pullback.fst π v = pullback.fst π v ≫ ρ a := fun a => pullback.lift_fst _ _ _
  have hπP : ∀ a, ρP a ≫ pullback.snd π v = pullback.snd π v := fun a => by
    rw [← Category.comp_id (pullback.snd π v)]
    exact pullback.lift_snd _ _ _
  let φ : X' ⟶ pullback π v := pullback.lift u π' w
  have hφ1 : φ ≫ pullback.fst π v = u := pullback.lift_fst _ _ _
  have hφ2 : φ ≫ pullback.snd π v = π' := pullback.lift_snd _ _ _
  have hφeq : ∀ a, φ ≫ ρP a = ρ' a ≫ φ := fun a => by
    apply pullback.hom_ext
    · simp only [Category.assoc, huP, hφ1, reassoc_of% hφ1, hu]
    · simp only [Category.assoc, hπP, hφ2, h'.inv]
  have hmono : Mono φ := by
    constructor
    intro T g₁ g₂ hg
    have hg1 : g₁ ≫ u = g₂ ≫ u := by rw [← hφ1, reassoc_of% hg]
    have hg2 : g₁ ≫ π' = g₂ ≫ π' := by rw [← hφ2, reassoc_of% hg]
    apply Scheme.hom_ext_of_forall
    intro p
    obtain ⟨V, a, hp, hV⟩ := h'.exists_local_geom g₁ g₂ hg2 p
    refine ⟨V, hp, ?_⟩
    have e : V.ι ≫ g₁ ≫ u ≫ ρ a = V.ι ≫ g₁ ≫ u := by
      rw [← hu, hg1]
      simpa only [Category.assoc] using congrArg (· ≫ u) hV
    obtain ⟨K, _, _, j, -⟩ := exists_algClosed_point V.toScheme ⟨p, hp⟩
    have ha : (j ≫ V.ι ≫ g₁ ≫ u) ≫ ρ a = j ≫ V.ι ≫ g₁ ≫ u := by
      simp only [Category.assoc] at e ⊢
      rw [e]
    have h1 : (j ≫ V.ι ≫ g₁ ≫ u) ≫ ρ 1 = j ≫ V.ι ≫ g₁ ≫ u := by
      rw [h.one, Category.comp_id]
    have ha1 : a = 1 := (h.fibre K _ _ rfl).unique ha h1
    rw [← hV, ha1, h'.one, Category.comp_id]
  have hsurj : Surjective φ := by
    constructor
    intro q
    obtain ⟨y, hy⟩ := h'.onto.surj (pullback.snd π v q)
    obtain ⟨r, hr1, hr2⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd π v)
      (g := pullback.snd π v) (φ y) q (by rw [← Scheme.Hom.comp_apply, hφ2, hy])
    obtain ⟨K, _, _, j, z, hz⟩ := exists_algClosed_point _ r
    obtain ⟨a, ha, -⟩ := existsUnique_act_of_isPullback_isGaloisCover h (IsPullback.of_hasPullback π v) huP hπP K
      (j ≫ pullback.fst _ _) (j ≫ pullback.snd _ _)
      (by simp only [Category.assoc, pullback.condition])
    refine ⟨ρ' a y, ?_⟩
    have hz' := congrArg (fun m : Sp K ⟶ _ => m z) ha
    simp only [Scheme.Hom.comp_apply, hz, hr1, hr2] at hz'
    rw [← Scheme.Hom.comp_apply, ← hφeq, Scheme.Hom.comp_apply]
    exact hz'
  have : Etale φ := by
    have : Etale (φ ≫ pullback.snd π v) := by rw [hφ2]; exact h'.etale
    exact Etale.of_comp (f := φ) (pullback.snd π v)
  have : QuasiCompact φ := by
    have : QuasiCompact (φ ≫ pullback.snd π v) := by rw [hφ2]; infer_instance
    exact MorphismProperty.of_postcomp (W := @QuasiCompact) (W' := @QuasiSeparated) φ
      (pullback.snd π v) inferInstance this
  have : IsIso φ := Flat.isIso_of_surjective_of_mono φ
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso φ) hφ1 hφ2

theorem of_isPullback (h : IsGaloisCover Ga ρ π) (hp : IsPullback u π' π v) (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a)
    (hπ : ∀ a, ρ' a ≫ π' = π') : IsGaloisCover Ga ρ' π' where
  finite := h.finite
  one := by
    apply hp.hom_ext
    · rw [hu 1, h.one, Category.id_comp, Category.comp_id]
    · rw [hπ 1, Category.id_comp]
  mul := by
    intro a c
    apply hp.hom_ext
    · rw [hu, h.mul, Category.assoc, hu c, reassoc_of% (hu a)]
    · rw [hπ, Category.assoc, hπ c, hπ a]
  inv := hπ
  fin := by
    have := h.fin
    exact MorphismProperty.of_isPullback hp h.fin
  etale := by
    have := h.etale
    exact MorphismProperty.of_isPullback hp h.etale
  onto := by
    have := h.onto
    exact MorphismProperty.of_isPullback hp h.onto
  fibre := by
    intro K _ _ y y' hy
    have hyu : (y ≫ u) ≫ π = (y' ≫ u) ≫ π := by
      simp only [Category.assoc, hp.w]
      simp only [← Category.assoc, hy]
    obtain ⟨a, ha, hauniq⟩ := h.fibre K (y ≫ u) (y' ≫ u) hyu
    refine ⟨a, ?_, ?_⟩
    · apply hp.hom_ext
      · rw [Category.assoc, hu, ← Category.assoc, ha]
      · rw [Category.assoc, hπ, hy]
    · intro b hb
      apply hauniq
      rw [Category.assoc, ← hu, ← Category.assoc, hb]

end GlobalTheory.ZM.IsGaloisCover

namespace GlobalTheory.ZM

theorem galoisCover_descent : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → (∀ (Z : Scheme.{0}) (f : X ⟶ Z), (∀ a, ρ a ≫ f = f) → ∃! f' : Y ⟶ Z, π ≫ f' = f) ∧ (∀ (T : Scheme.{0}) (x x' : T ⟶ X), x ≫ π = x' ≫ π → ∀ p : T, ∃ (V : T.Opens) (a : Ga), p ∈ V ∧ V.ι ≫ x ≫ ρ a = V.ι ≫ x') ∧ ∀ (X' Y' : Scheme.{0}) (π' : X' ⟶ Y') (ρ' : Ga → (X' ⟶ X')) (u : X' ⟶ X) (v : Y' ⟶ Y), (∀ a, ρ' a ≫ u = u ≫ ρ a) → u ≫ π = π' ≫ v → (IsGaloisCover Ga ρ' π' → IsPullback u π' π v) ∧ (IsPullback u π' π v → (∀ a, ρ' a ≫ π' = π') → IsGaloisCover Ga ρ' π') := by
  intro X Y π Ga _ ρ h
  refine ⟨fun Z f hf => h.existsUnique_desc f hf, fun T x x' hx p => h.exists_local_geom x x' hx p, ?_⟩
  intro X' Y' π' ρ' u v hu w
  exact ⟨fun h' => h.isPullback h' hu w, fun hp hπ => h.of_isPullback hp hu hπ⟩

end GlobalTheory.ZM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeAndRelDimOfOpenCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem of_isPullback_cover (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    {S X : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {Z : I → Scheme.{0}} {p : X ⟶ S}
    {q : ∀ i, Z i ⟶ (U i).toScheme} {ψ : ∀ i, Z i ⟶ X} (h : ∀ i, IsPullback (ψ i) (q i) p (U i).ι)
    (hq : ∀ i, Q (q i)) : Q p := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun i => ?_
  have hr := (isPullback_morphismRestrict p (U i)).flip
  rw [← IsPullback.isoIsPullback_hom_snd _ _ hr (h i)]
  exact (MorphismProperty.cancel_left_of_respectsIso Q _ _).2 (hq i)

theorem isCommMonObj_of_cover {S : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {A : Over S}
    [GrpObj A] {G : ∀ i, Over (U i).toScheme} [∀ i, GrpObj (G i)] {ψ : ∀ i, (G i).left ⟶ A.left}
    (h : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (hc : ∀ i, IsCommMonObj (G i)) : IsCommMonObj A := by
  refine (isCommMonObj_iff_isMulCommutative A).2 fun T => ⟨⟨fun x y => ?_⟩⟩
  refine over_ext hU fun i T' r => ?_
  have := hc i
  rw [MonObj.comp_mul, MonObj.comp_mul]
  obtain ⟨a, ha⟩ := exists_lift (h i).1 (r ≫ x)
  obtain ⟨b, hb⟩ := exists_lift (h i).1 (r ≫ y)
  ext1
  rw [(h i).2 T' a b _ _ ha hb, (h i).2 T' b a _ _ hb ha, mul_comm a b]

theorem isAbelianScheme_and_relDim_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ((∀ i, IsAbelianScheme (G i)) → IsAbelianScheme A) ∧ ∀ g : ℕ, (∀ i, SmoothOfRelativeDimension g (G i).hom) → SmoothOfRelativeDimension g A.hom := by
  intro S I U A _ G _ ψ hU h
  refine ⟨fun hab => ?_, fun g hg => ?_⟩
  · constructor
    · exact isCommMonObj_of_cover hU h fun i => (hab i).comm
    · exact @of_isPullback_cover @Smooth (HasRingHomProperty.instIsZariskiLocalAtTarget @Smooth) _ _ _ _ hU _ _ _ _
        (fun i => (h i).1) fun i => (hab i).smooth
    · exact of_isPullback_cover @IsProper hU (fun i => (h i).1) fun i => (hab i).proper
    · refine ⟨?_⟩
      exact of_isPullback_cover (geometrically (ConnectedSpace ·)) hU (fun i => (h i).1)
        fun i => (hab i).geomConnected.geometrically_connectedSpace
  · exact @of_isPullback_cover (@SmoothOfRelativeDimension g)
      (HasRingHomProperty.instIsZariskiLocalAtTarget (@SmoothOfRelativeDimension g)) _ _ _ _ hU _ _ _ _
      (fun i => (h i).1) hg

end GlobalTheory.CoverGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.projective_representation_pullback_coordinates : ∀ (R R' σ : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (I : Ideal (MvPolynomial σ R)) (Z Z' : Scheme.{0}) (s : Z ⟶ Sp R) (s' : Z' ⟶ Sp R') (π : Z' ⟶ Z) (M : LB Z) (th : σ → M.Sec), ProjRep I s M th → IsPullback π s' s (spMap φ) → ∃ th' : σ → (M.pull π).Sec, ProjRep (I.map (MvPolynomial.map φ)) s' (M.pull π) th' ∧ ∀ (T : Type) [CommRing T] (x : Sp T ⟶ Z') (v : σ → T), SecCoord (M.pull π) th' x v ↔ SecCoord M th (x ≫ π) v := by
  first | exact @GlobalTheory.ZM.RepBC.projRep_baseChange | exact GlobalTheory.ZM.RepBC.projRep_baseChange | (intros; apply GlobalTheory.ZM.RepBC.projRep_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinateVectorExistsLocallyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionCoordinateVector_exists_locally : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec), M.IsLB → (∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X), ∃ v, SecCoord M th x v) ∧ (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (p : Sp R), ∃ f : R, f ∉ p.asIdeal ∧ ∃ v, SecCoord M th (spMap (algebraMap R (Localization.Away f)) ≫ x) v) ∧ ∀ p : X, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (v : I → R), IsOpenImmersion x ∧ p ∈ Set.range x ∧ SecCoord M th x v := by
  first | exact @GlobalTheory.ZM.LocalCoord.secCoord_local | exact GlobalTheory.ZM.LocalCoord.secCoord_local | (intros; apply GlobalTheory.ZM.LocalCoord.secCoord_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGenericFibreOfAffineOpensStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.smooth_genericFibre_of_affine_opens : ∀ (o : Type) [CommRing o] [IsDomain o] (X : Scheme.{0}) (s : X ⟶ Sp o) (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ X), IsOpenImmersion x → x ≫ s = spMap (algebraMap o R) → SmoothOfRelativeDimension d (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R)))) → SmoothOfRelativeDimension d (pullback.snd s (spMap (algebraMap o (FractionRing o)))) := by
  first | exact @GlobalTheory.smoothOfRelativeDimension_genericFibre_of_affine | exact GlobalTheory.smoothOfRelativeDimension_genericFibre_of_affine | (intros; apply GlobalTheory.smoothOfRelativeDimension_genericFibre_of_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGenericFibreOfIndependentAndTangentBoundStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.smooth_genericFibre_of_independent_and_tangent_bound : ∀ (o : Type) [CommRing o] [IsDomain o] (em : o →+* ℂ) (R : Type) [CommRing R] [Algebra o R] (d : ℕ), Function.Injective em → Algebra.FiniteType o R → (∀ (K : Type) [Field K] [Algebra o K] (φ : R →ₐ[o] K), RingHom.ker φ ∈ minimalPrimes R → (∀ z : K, ∃ a b, z = φ a / φ b) → ∃ y : Fin d → K, AlgebraicIndependent o y) → (∀ [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ], algebraMap o ℂ = em → Module.finrank ℂ (Derivation o R ℂ) ≤ d) → SmoothOfRelativeDimension d (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R))) := by
  first | exact @GlobalTheory.smoothOfRelativeDimension_genericFibre_of_independent_of_finrank_derivation_le | exact GlobalTheory.smoothOfRelativeDimension_genericFibre_of_independent_of_finrank_derivation_le | (intros; apply GlobalTheory.smoothOfRelativeDimension_genericFibre_of_independent_of_finrank_derivation_le <;> assumption)
end

