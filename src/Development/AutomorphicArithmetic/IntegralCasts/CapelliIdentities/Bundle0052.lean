import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OneLeftCongr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
private noncomputable def UpperTheory.specMapOverOfAlgHom {S : Scheme.{0}} {R : Type} [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S) {A B : Type} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ x) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ x) :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ ≫ x = Spec.map _ ≫ x
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact f.comp_algebraMap)

open AlgebraicGeometry CategoryTheory in
private theorem UpperTheory.specMapAlg_comp {S : Scheme.{0}} {R : Type} [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S) {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    UpperTheory.specMapOverOfAlgHom x g ≫ UpperTheory.specMapOverOfAlgHom x f = UpperTheory.specMapOverOfAlgHom x (g.comp f) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

open AlgebraicGeometry CategoryTheory in
private theorem UpperTheory.specMap_id {S : Scheme.{0}} {R : Type} [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S) {A : Type} [CommRing A] [Algebra R A] :
    UpperTheory.specMapOverOfAlgHom x (AlgHom.id R A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  exact Spec.map_id _

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
private theorem UpperTheory.grpObj_one_left_congr {S : Scheme.{0}} (G : Over S) [GrpObj G]
    {X : Scheme.{0}} {x y : X ⟶ S} (h : x = y) :
    (1 : Over.mk x ⟶ G).left = (1 : Over.mk y ⟶ G).left := by
  subst h
  rfl

theorem UpperTheory.tangent_left_one :
    open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
        ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S)
          (v w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x) ⟶ G),
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ v.left = (1 : Over.mk x ⟶ G).left →
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ w.left = (1 : Over.mk x ⟶ G).left →
            ∃ u : Spec (CommRingCat.of (TrivSqZeroExt R (R × R))) ⟶ G.left,
              Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R (R × R)).toRingHom) ≫ u = (1 : Over.mk x ⟶ G).left ∧
              Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom) ≫ u = v.left ∧
              Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd R R R)).toRingHom) ≫ u = w.left ∧
              Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R R R + LinearMap.snd R R R)).toRingHom) ≫ u
                = (v * w).left := by
  open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
  · intro S G _ R _ x v w hv hw
    have hx : Spec.map (CommRingCat.ofHom (algebraMap R R)) ≫ x = x := by
      have : Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 _ := Spec.map_id _
      rw [this, Category.id_comp]
    have h1 := UpperTheory.grpObj_one_left_congr G hx
    have hv' : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.fstHom R R R) ≫ v = 1 :=
      Over.OverMorphism.ext (hv.trans h1.symm)
    have hw' : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.fstHom R R R) ≫ w = 1 :=
      Over.OverMorphism.ext (hw.trans h1.symm)
    have e0 : (TrivSqZeroExt.map (0 : R →ₗ[R] R)) =
        (Algebra.ofId R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R) := by
      apply AlgHom.ext
      intro a
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    have hv0 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (0 : R →ₗ[R] R)) ≫ v = 1 := by
      rw [e0, ← UpperTheory.specMapAlg_comp, Category.assoc, hv', MonObj.comp_one]
    have hw0 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (0 : R →ₗ[R] R)) ≫ w = 1 := by
      rw [e0, ← UpperTheory.specMapAlg_comp, Category.assoc, hw', MonObj.comp_one]
    let U : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R (R × R)))) ≫ x) ⟶ G :=
      (UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.inl R R R)) ≫ v) *
        (UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.inr R R R)) ≫ w)
    have key : ∀ f : (R × R) →ₗ[R] R, UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map f) ≫ U =
        (UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (f ∘ₗ LinearMap.inl R R R)) ≫ v) *
          (UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (f ∘ₗ LinearMap.inr R R R)) ≫ w) := by
      intro f
      simp only [U, MonObj.comp_mul, ← Category.assoc, UpperTheory.specMapAlg_comp,
        TrivSqZeroExt.map_comp_map]
    have k0 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.fstHom R R (R × R)) ≫ U = 1 := by
      simp only [U, MonObj.comp_mul, ← Category.assoc, UpperTheory.specMapAlg_comp,
        TrivSqZeroExt.fstHom_comp_map]
      rw [hv', hw', _root_.mul_one]
    have k1 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.fst R R R)) ≫ U = v := by
      rw [key, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, hw0, TrivSqZeroExt.map_id,
        UpperTheory.specMap_id, Category.id_comp, _root_.mul_one]
    have k2 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.snd R R R)) ≫ U = w := by
      rw [key, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, hv0, TrivSqZeroExt.map_id,
        UpperTheory.specMap_id, Category.id_comp, _root_.one_mul]
    have k3 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.fst R R R + LinearMap.snd R R R)) ≫ U
        = v * w := by
      rw [key, LinearMap.add_comp, LinearMap.add_comp, LinearMap.fst_comp_inl,
        LinearMap.fst_comp_inr, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, add_zero, zero_add,
        TrivSqZeroExt.map_id, UpperTheory.specMap_id, Category.id_comp, Category.id_comp]
    exact ⟨U.left, (congrArg CommaMorphism.left k0).trans h1, congrArg CommaMorphism.left k1,
      congrArg CommaMorphism.left k2, congrArg CommaMorphism.left k3⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OrbitFinite
section
theorem UpperTheory.Reformulated.B.Qf32.orbit_finite :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] {G : Type}
    [inst_2 : Group G] [inst_3 : TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (K : Subgroup G),
    IsCompact (↑K : Set G) →
      ∀ (w : V),
        IsOpen {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) w = w} →
          {x : V | ∃ k ∈ K, ((ρ : G → V →ₗ[ℂ] V) k : V → V) w = x}.Finite := by
  intro V _ _ G _ _ _ ρ K hK w hw
  have hloc : IsLocallyConstant (fun g : G => ρ g w) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro k
    refine ⟨(fun g : G => k⁻¹ * g) ⁻¹' {g : G | ρ g w = w},
      hw.preimage (continuous_const.mul continuous_id), by simp, ?_⟩
    intro g hg
    have hg' : ρ (k⁻¹ * g) w = w := hg
    calc ρ g w = ρ (k * (k⁻¹ * g)) w := by rw [mul_inv_cancel_left]
      _ = ρ k (ρ (k⁻¹ * g) w) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ k w := by rw [hg']
  haveI : CompactSpace (K : Set G) := isCompact_iff_compactSpace.mp hK
  have hfin := (hloc.comp_continuous
    (continuous_subtype_val (p := fun g : G => g ∈ (K : Set G)))).range_finite
  refine hfin.subset ?_
  rintro x ⟨k, hk, rfl⟩
  exact ⟨⟨k, hk⟩, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OrderedFlagDiagonal
section
namespace UpperTheory.Reformulated.B.OrderedFlagDiagonal
abbrev M4 (R : Type) : Type := Matrix (Fin 4) (Fin 4) R

variable {K : Type} [Field K]

theorem ordFlag_diag (c : Fin 4 → K) (hc : Function.Injective c) (X : M4 K)
    (hX : X.charpoly = ∏ j, (Polynomial.X - Polynomial.C (c j))) :
    ∃ P : (M4 K)ˣ, X * (P : M4 K) = (P : M4 K) * Matrix.diagonal c := by
  have hev : ∀ j, Module.End.HasEigenvalue (Matrix.toLin' X) (c j) := by
    intro j
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hX,
      Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
  choose v hv using fun j => (hev j).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' X) c hc v hv
  have hU : IsUnit (Matrix.of fun i j => v j i : Matrix (Fin 4) (Fin 4) K) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hli
  obtain ⟨P, hP⟩ := hU
  refine ⟨P, ?_⟩
  rw [hP]
  ext i j
  have h := congrFun (hv j).apply_eq_smul i
  rw [Matrix.toLin'_apply] at h
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h

end UpperTheory.Reformulated.B.OrderedFlagDiagonal
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PairCases
section
theorem UpperTheory.Reformulated.B.PairCases.pair_cases :
    ∀ {a b c d : @Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)},
      @Eq (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
          (@Insert.insert (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))
            (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
            (@Multiset.instInsert (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))) a
            (@Singleton.singleton (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))
              (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
              (@Multiset.instSingleton (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))) b))
          (@Insert.insert (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))
            (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
            (@Multiset.instInsert (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))) c
            (@Singleton.singleton (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))
              (Multiset (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)))
              (@Multiset.instSingleton (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring))) d)) →
        Or
          (And (@Eq (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)) a c)
            (@Eq (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)) b d))
          (And (@Eq (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)) a d)
            (@Eq (@Units Complex (@Semiring.toMonoid Complex Complex.instSemiring)) b c)) := by
  intro a b c d h
  rw [Multiset.insert_eq_cons, Multiset.insert_eq_cons] at h
  rcases Multiset.cons_eq_cons.mp h with ⟨h1, h2⟩ | ⟨_, cs, h2, h3⟩
  · exact Or.inl ⟨h1, Multiset.singleton_inj.mp h2⟩
  · exact Or.inr ⟨(Multiset.singleton_eq_cons_iff _ |>.mp h3).1.symm,
      (Multiset.singleton_eq_cons_iff _ |>.mp h2).1⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PairedCharacterCondition
section
noncomputable def UpperTheory.Reformulated.B.PairedCharacterCondition.TrScale :
    Prop :=
    ∀ (K : Type) [inst : Field K] [NumberField K] (V : Type) [inst_2 : AddCommGroup V] [inst_3 : _root_.Module K V]
      [inst_4 : _root_.Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
      (M : Submodule (NumberField.RingOfIntegers K) V),
      Submodule.span K (↑M : Set V) = ⊤ → ∀ (f : V), ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ (↑m : K) • f ∈ M

theorem UpperTheory.Reformulated.B.PairedCharacterCondition.tr_scale :
    UpperTheory.Reformulated.B.PairedCharacterCondition.TrScale := by
  intro K _ _ V _ _ _ _ M hM f
  have key : ∀ (c : K), IsIntegral ℤ c → ∀ x ∈ M, c • x ∈ M := by
    intro c hc x hx
    obtain ⟨r, rfl⟩ : ∃ r : NumberField.RingOfIntegers K, algebraMap _ K r = c := ⟨⟨c, hc⟩, rfl⟩
    rw [algebraMap_smul]
    exact M.smul_mem r hx
  have hint : ∀ n : ℤ, IsIntegral ℤ (n : K) := fun n => isIntegral_algebraMap (R := ℤ) (x := n)
  have hf : f ∈ Submodule.span K (↑M : Set V) := hM ▸ Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : ((a * b : ℤ) : K) • (x + y) = (b : K) • ((a : K) • x) + (a : K) • ((b : K) • y) := by
      rw [smul_add, smul_smul, smul_smul, Int.cast_mul, mul_comm (b : K)]
    rw [e]
    exact M.add_mem (key _ (hint b) _ hx) (key _ (hint a) _ hy)
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    have halg : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨b, hb, hc⟩ := halg.exists_integral_multiple
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have e : ((a * b : ℤ) : K) • (c • x) = (b • c) • ((a : K) • x) := by
      rw [smul_smul, smul_smul, Int.cast_mul, zsmul_eq_mul]
      congr 1
      ring
    rw [e]
    exact key _ hc _ hx
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ParabolicUnipotentGL
section
noncomputable def UpperTheory.Reformulated.B.ParabolicUnipotentGL.IsGlRep.{u_1} :
    {n : ℕ} →
      {M : Type u_1} → [inst : AddCommGroup M] → [inst_1 : _root_.Module ℂ M] → (Fin n → Fin n → Module.End ℂ M) → Prop :=
    fun {n : ℕ} {M : Type u_1} [AddCommGroup M] [_root_.Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) ↦
      ∀ (a b c d : Fin n),
        E a b * E c d - E c d * E a b =
          (if b = c then E a d else (0 : Module.End ℂ M)) - if d = a then E c b else (0 : Module.End ℂ M)

noncomputable def UpperTheory.Reformulated.B.ParabolicUnipotentGL.U :
    {n : ℕ} →
      {V : Type} →
        [inst : AddCommGroup V] →
          [inst_1 : _root_.Module ℂ V] → (Fin n → Fin n → Module.End ℂ V) → ℕ → Submodule ℂ (Module.End ℂ V) :=
    fun {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) ↦
      Submodule.span ℂ
        {x : Module.End ℂ V |
          ∃ (l : List (Fin n × Fin n)), l.length ≤ k ∧ x = (List.map (fun (p : Fin n × Fin n) ↦ E p.1 p.2) l).prod}

namespace UpperTheory.Reformulated.B.ParabolicUnipotentGL

section helpers

variable {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)

private abbrev P (l : List (Fin n × Fin n)) : Module.End ℂ V :=
  (List.map (fun (p : Fin n × Fin n) ↦ E p.1 p.2) l).prod

private theorem U_mono {j k : ℕ} (h : j ≤ k) : U E j ≤ U E k := by
  apply Submodule.span_mono
  rintro x ⟨l, hl, rfl⟩
  exact ⟨l, hl.trans h, rfl⟩

private theorem monomial_mem_filtration_of_length_le (l : List (Fin n × Fin n)) {k : ℕ} (h : l.length ≤ k) : P E l ∈ U E k :=
  Submodule.subset_span ⟨l, h, rfl⟩

private theorem gen_mem (a b : Fin n) : E a b ∈ U E 1 := by
  have := monomial_mem_filtration_of_length_le E [(a, b)] (k := 1) (by simp)
  simpa [P] using this

private theorem mul_mem_U {j k : ℕ} {x y : Module.End ℂ V} (hx : x ∈ U E j) (hy : y ∈ U E k) :
    x * y ∈ U E (j + k) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hx
      obtain ⟨m, hm, rfl⟩ := hy
      refine Submodule.subset_span ⟨l ++ m, ?_, ?_⟩
      · simp only [List.length_append]; omega
      · simp
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha

private theorem gen_comm_mem (hE : IsGlRep E) (a b c d : Fin n) :
    E a b * E c d - E c d * E a b ∈ U E 1 := by
  rw [hE a b c d]
  refine sub_mem ?_ ?_
  · split_ifs
    · exact gen_mem E _ _
    · exact zero_mem _
  · split_ifs
    · exact gen_mem E _ _
    · exact zero_mem _

private theorem gen_comm_P (hE : IsGlRep E) (a b : Fin n) (l : List (Fin n × Fin n)) :
    E a b * P E l - P E l * E a b ∈ U E l.length := by
  induction l with
  | nil => simp [P]
  | cons p t ih =>
    have e : E a b * P E (p :: t) - P E (p :: t) * E a b
        = (E a b * E p.1 p.2 - E p.1 p.2 * E a b) * P E t
          + E p.1 p.2 * (E a b * P E t - P E t * E a b) := by
      simp only [P, List.map_cons, List.prod_cons]
      noncomm_ring
    rw [e, List.length_cons, add_comm t.length 1]
    exact add_mem (mul_mem_U E (gen_comm_mem E hE _ _ _ _) (monomial_mem_filtration_of_length_le E t le_rfl))
      (mul_mem_U E (gen_mem E _ _) ih)

private theorem monomial_commutator_mem_filtration (hE : IsGlRep E) (l : List (Fin n × Fin n)) (q : Fin n × Fin n)
    (m : List (Fin n × Fin n)) :
    P E l * P E (q :: m) - P E (q :: m) * P E l ∈ U E (l.length + m.length) := by
  induction l with
  | nil => simp [P]
  | cons p t ih =>
    have e : P E (p :: t) * P E (q :: m) - P E (q :: m) * P E (p :: t)
        = E p.1 p.2 * (P E t * P E (q :: m) - P E (q :: m) * P E t)
          + (E p.1 p.2 * P E (q :: m) - P E (q :: m) * E p.1 p.2) * P E t := by
      generalize P E (q :: m) = y
      simp only [P, List.map_cons, List.prod_cons]
      noncomm_ring
    rw [e]
    refine add_mem ?_ ?_
    · exact U_mono E (by simp only [List.length_cons]; omega) (mul_mem_U E (gen_mem E _ _) ih)
    · exact U_mono E (by simp only [List.length_cons]; omega)
        (mul_mem_U E (gen_comm_P E hE _ _ (q :: m)) (monomial_mem_filtration_of_length_le E t le_rfl))

end helpers

end UpperTheory.Reformulated.B.ParabolicUnipotentGL

theorem UpperTheory.Reformulated.B.ParabolicUnipotentGL.main :
    ∀ {n : ℕ} {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
      UpperTheory.Reformulated.B.ParabolicUnipotentGL.IsGlRep E →
        ∀ {j k : ℕ} {x y : Module.End ℂ V},
          x ∈ UpperTheory.Reformulated.B.ParabolicUnipotentGL.U E j →
            y ∈ UpperTheory.Reformulated.B.ParabolicUnipotentGL.U E k → x * y - y * x ∈ UpperTheory.Reformulated.B.ParabolicUnipotentGL.U E (j + k - (1 : ℕ)) := by
  intro n V _ _ E hE j k x y hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hx
      obtain ⟨m, hm, rfl⟩ := hy
      cases m with
      | nil => simp
      | cons q t =>
        simp only [List.length_cons] at hm
        exact UpperTheory.Reformulated.B.ParabolicUnipotentGL.U_mono E (by omega) (UpperTheory.Reformulated.B.ParabolicUnipotentGL.monomial_commutator_mem_filtration E hE l q t)
    | zero => simp
    | add a b _ _ ha hb =>
      have e : x * (a + b) - (a + b) * x = (x * a - a * x) + (x * b - b * x) := by noncomm_ring
      rw [e]; exact add_mem ha hb
    | smul c a _ ha =>
      have e : x * (c • a) - (c • a) * x = c • (x * a - a * x) := by
        rw [mul_smul_comm, smul_mul_assoc, smul_sub]
      rw [e]; exact Submodule.smul_mem _ c ha
  | zero => simp
  | add a b _ _ ha hb =>
    have e : (a + b) * y - y * (a + b) = (a * y - y * a) + (b * y - y * b) := by noncomm_ring
    rw [e]; exact add_mem ha hb
  | smul c a _ ha =>
    have e : (c • a) * y - y * (c • a) = c • (a * y - y * a) := by
      rw [mul_smul_comm, smul_mul_assoc, smul_sub]
    rw [e]; exact Submodule.smul_mem _ c ha
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PartialDerivMonomialLaplace
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Gs1.Wt :
    ℕ → Type :=
    fun (n : ℕ) ↦ Fin n → ℝ

@[reducible] noncomputable def UpperTheory.Reformulated.B.Gs1.FR :
    ℕ → Type :=
    fun (n : ℕ) ↦ AddMonoidAlgebra ℂ (UpperTheory.Reformulated.B.Gs1.Wt n)

theorem UpperTheory.Reformulated.B.Gs1.aux3 :
    ∀ {n : ℕ} (a : Fin n) (f : UpperTheory.Reformulated.B.Gs1.FR n) (x : UpperTheory.Reformulated.B.Gs1.Wt n),
      (↑(x a) : ℂ) * (f.coeff : UpperTheory.Reformulated.B.Gs1.Wt n → ℂ) x ≠ (0 : ℂ) → x ∈ f.coeff.support := by
  intro n a f x h
  exact Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul h)

noncomputable def UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace :
    {n : ℕ} → Fin n → UpperTheory.Reformulated.B.Gs1.FR n → UpperTheory.Reformulated.B.Gs1.FR n :=
    fun {n : ℕ} (a : Fin n) (f : UpperTheory.Reformulated.B.Gs1.FR n) ↦
      AddMonoidAlgebra.ofCoeff
        (Finsupp.onFinset f.coeff.support
          (fun (x : UpperTheory.Reformulated.B.Gs1.Wt n) ↦ (↑(x a) : ℂ) * (f.coeff : UpperTheory.Reformulated.B.Gs1.Wt n → ℂ) x)
          (UpperTheory.Reformulated.B.Gs1.aux3 a f))

theorem UpperTheory.Reformulated.B.Gs1.aux5 :
    ∀ {n : ℕ} (a : Fin n) (f g : UpperTheory.Reformulated.B.Gs1.FR n),
      UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a (f + g) = UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a f + UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a g := by
  intro n a f g
  ext x
  simp [UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace, mul_add]

theorem UpperTheory.Reformulated.B.Gs1.aux6 :
    ∀ {n : ℕ} (a : Fin n) (c : ℂ) (f : UpperTheory.Reformulated.B.Gs1.FR n),
      UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a (c • f) = (RingHom.id ℂ : ℂ → ℂ) c • UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a f := by
  intro n a c f
  ext x
  simp [UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace, mul_left_comm]

noncomputable def UpperTheory.Reformulated.B.Gs1.lapD :
    {n : ℕ} → Fin n → UpperTheory.Reformulated.B.Gs1.FR n →ₗ[ℂ] UpperTheory.Reformulated.B.Gs1.FR n :=
    fun {n : ℕ} (a : Fin n) ↦
      { toFun := UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a, map_add' := UpperTheory.Reformulated.B.Gs1.aux5 a, map_smul' := UpperTheory.Reformulated.B.Gs1.aux6 a :
        UpperTheory.Reformulated.B.Gs1.FR n →ₗ[ℂ] UpperTheory.Reformulated.B.Gs1.FR n }

private theorem UpperTheory.Reformulated.B.Gs1.lapD_single {n : ℕ} (a : Fin n) (x : UpperTheory.Reformulated.B.Gs1.Wt n) (c : ℂ) :
    UpperTheory.Reformulated.B.Gs1.lapD a (AddMonoidAlgebra.single x c) =
      AddMonoidAlgebra.single x ((x a : ℂ) * c) := by
  classical
  change UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace a _ = _
  ext y
  by_cases h : x = y
  · subst h
    simp [UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace]
  · simp [UpperTheory.Reformulated.B.Gs1.partialDerivMonomialLaplace, Finsupp.single_apply, h]

theorem UpperTheory.Reformulated.B.Gs1.lapD_mul :
    ∀ {n : ℕ} (a : Fin n) (f g : UpperTheory.Reformulated.B.Gs1.FR n),
      (UpperTheory.Reformulated.B.Gs1.lapD a : UpperTheory.Reformulated.B.Gs1.FR n → UpperTheory.Reformulated.B.Gs1.FR n) (f * g) =
        (UpperTheory.Reformulated.B.Gs1.lapD a : UpperTheory.Reformulated.B.Gs1.FR n → UpperTheory.Reformulated.B.Gs1.FR n) f * g +
          f * (UpperTheory.Reformulated.B.Gs1.lapD a : UpperTheory.Reformulated.B.Gs1.FR n → UpperTheory.Reformulated.B.Gs1.FR n) g := by
  intro n a f g
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ =>
    rw [add_mul, map_add, map_add, h₁, h₂, add_mul, add_mul]
    abel
  | single x c =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ =>
      rw [mul_add, map_add, map_add, h₁, h₂, mul_add, mul_add]
      abel
    | single y d =>
      simp only [AddMonoidAlgebra.single_mul_single, UpperTheory.Reformulated.B.Gs1.lapD_single]
      rw [← AddMonoidAlgebra.single_add]
      congr 1
      simp only [Pi.add_apply, Complex.ofReal_add]
      ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PartialFiltrationCoeff
section
theorem UpperTheory.Reformulated.B.PartialFiltrationCoeff.part_filt_coeff :
    ∀ {O σ : Type} [inst : CommRing O]
    [inst_1 : IsLocalRing O] (M : ℕ),
    ∀ f ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ O) ^ M,
      ∀ (n : σ →₀ ℕ),
        (MvPowerSeries.coeff n : MvPowerSeries σ O → O) f ∈
          IsLocalRing.maximalIdeal O ^ (M - (Finsupp.degree : (σ →₀ ℕ) → ℕ) n) := by
  intro O σ _ _ M
  classical
  induction M with
  | zero =>
    intro f _ n
    simp
  | succ M ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro a ha b hb n
      rw [MvPowerSeries.coeff_mul]
      refine Ideal.sum_mem _ ?_
      rintro ⟨p, q⟩ hpq
      have hsum : p + q = n := by simpa using hpq
      have hdeg : Finsupp.degree p + Finsupp.degree q = Finsupp.degree n := by
        rw [← hsum, map_add]
      have hp := ih a ha p
      by_cases hq : q = 0
      · subst hq
        have hb0 : MvPowerSeries.coeff (0 : σ →₀ ℕ) b ∈ IsLocalRing.maximalIdeal O := by
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hb ⊢
          intro hu
          exact hb (MvPowerSeries.isUnit_iff_constantCoeff.mpr (by simpa using hu))
        have hmul := Ideal.mul_mem_mul hp hb0
        rw [← pow_succ] at hmul
        exact Ideal.pow_le_pow_right (by omega) hmul
      · have hq' : Finsupp.degree q ≠ 0 := fun h => hq ((Finsupp.degree_eq_zero_iff q).mp h)
        exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (by omega) hp)
    · intro x y hx hy n
      rw [map_add]
      exact Ideal.add_mem _ (hx n) (hy n)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.QuotientBasisFiniteDimensional
section
theorem UpperTheory.Reformulated.B.QuotientBasisFiniteDimensional.qb_fd :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {ι : Type} [Finite ι]
    (f : ι → PadicAlgCl l),
    ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] ↥K ∧ ∀ (i : ι), f i ∈ K := by
  intro l _ ι _ f
  refine ⟨IntermediateField.adjoin ℚ_[l] (Set.range f), ?_, fun i =>
    IntermediateField.subset_adjoin ℚ_[l] (Set.range f) ⟨i, rfl⟩⟩
  haveI : Finite (Set.range f) := (Set.finite_range f).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ =>
    Algebra.IsIntegral.isIntegral x
end

