import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsHasProjectiveDimensionLEOfResidueField
section
open CategoryTheory IsLocalRing

namespace GlobalTheory

universe u

theorem projectiveDimension_quotient_maximalIdeal_ne_top (R : Type u) [CommRing R]
    [IsRegularLocalRing R] :
    projectiveDimension (ModuleCat.of R (R ⧸ maximalIdeal R)) ≠ ⊤ := by
  obtain ⟨xs, h, hd⟩ := exists_ofList_eq_maximalIdeal_length_eq R
  have hreg := isRegular_of_ofList_eq_maximalIdeal h hd.le
  have key := ModuleCat.projectiveDimension_quotient_eq_length.{u} xs hreg
  rw [projectiveDimension_eq_of_iso (Shrink.linearEquiv R _).toModuleIso, h] at key
  rw [key]
  exact ne_of_beq_false rfl

theorem exists_hasProjectiveDimensionLE_of_residueField (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hk : projectiveDimension (ModuleCat.of R (R ⧸ maximalIdeal R)) ≠ ⊤)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n := by
  suffices H : ∀ (I : Ideal R) (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N],
      I ≤ Module.annihilator R N → ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R N) n from
    H ⊥ M bot_le
  intro I
  induction I using IsNoetherian.induction with
  | hgt I ih =>
  intro N _ _ hN
  induction hN using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
  | subsingleton N =>
    intro _
    have := (ModuleCat.isZero_of_subsingleton (ModuleCat.of R N)).hasProjectiveDimensionLT_zero
    exact ⟨0, hasProjectiveDimensionLT_of_ge _ 0 _ (Nat.zero_le _)⟩
  | quotient N p f =>
    intro hI
    rw [f.annihilator_eq, Ideal.annihilator_quotient] at hI
    rw [← projectiveDimension_ne_top_iff, projectiveDimension_eq_of_iso f.toModuleIso]
    by_cases hp : p.asIdeal = maximalIdeal R
    · rw [hp]
      exact hk
    have hlt : p.asIdeal < maximalIdeal R := lt_of_le_of_ne (le_maximalIdeal p.2.ne_top) hp
    obtain ⟨x, hx, hxp⟩ := SetLike.exists_of_lt hlt
    have hreg : IsSMulRegular (R ⧸ p.asIdeal) x := by
      intro a b hab
      have hx0 : Ideal.Quotient.mk p.asIdeal x ≠ 0 := by
        rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      refine mul_left_cancel₀ hx0 ?_
      simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hab
    have hJ : I < p.asIdeal ⊔ Ideal.span {x} := by
      refine lt_of_le_of_lt hI (lt_of_le_of_ne le_sup_left fun e => hxp ?_)
      rw [e]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
    have hq := ih _ hJ (QuotSMulTop x (R ⧸ p.asIdeal)) (sup_le
      (Ideal.annihilator_quotient.ge.trans
        (LinearMap.annihilator_le_of_surjective _ (Submodule.mkQ_surjective _)))
      ((Ideal.span_singleton_le_iff_mem _).mpr (QuotSMulTop.mem_annihilator _ x)))
    rw [← projectiveDimension_ne_top_iff] at hq
    have key := ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular
      (ModuleCat.of R (R ⧸ p.asIdeal)) x hreg hx
    intro htop
    apply hq
    rw [htop] at key
    exact key.trans rfl
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    intro hI
    obtain ⟨a, ha⟩ := h₁ (hI.trans (f.annihilator_le_of_injective hf))
    obtain ⟨b, hb⟩ := h₃ (hI.trans (g.annihilator_le_of_surjective hg))
    have hS : (ModuleCat.shortComplexOfCompEqZero f g hfg.linearMap_comp_eq_zero).ShortExact :=
      ModuleCat.shortComplex_shortExact _ hfg hf hg
    exact ⟨a + b, hS.hasProjectiveDimensionLT_X₂ _
      (hasProjectiveDimensionLT_of_ge (ModuleCat.of R N₁) (a + 1) _ (by omega))
      (hasProjectiveDimensionLT_of_ge (ModuleCat.of R N₃) (b + 1) _ (by omega))⟩

theorem exists_hasProjectiveDimensionLE_of_isRegularLocalRing :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
      [Module.Finite R M], ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n :=
  fun R _ _ M _ _ _ => exists_hasProjectiveDimensionLE_of_residueField R
    (projectiveDimension_quotient_maximalIdeal_ne_top R) M

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsMulEqSmulOneOfMulVecInjective
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_mul_eq_smul_one_of_mulVec_injective {R K : Type} [CommRing R] [Field K]
    (g : R →+* K) {m l : Type} [Fintype m] [Fintype l] [DecidableEq l] (M : Matrix m l R)
    (hM : ∀ x : l → K, (M.map g).mulVec x = 0 → x = 0) :
    ∃ (r : R) (T : Matrix l m R), g r ≠ 0 ∧ T * M = r • (1 : Matrix l l R) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K (fun i : m => (M.map g) i)
  have : Fintype κ := Fintype.ofInjective a ha
  have h1 : Fintype.card κ ≤ Fintype.card l := by
    have := hli.fintype_card_le_finrank
    simpa using this
  have h2 : Fintype.card l ≤ Fintype.card κ := by
    have hinj : Function.Injective (Matrix.mulVecLin ((M.map g).submatrix a id)) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      apply hM
      funext i
      have hi : (M.map g) i ∈ Submodule.span K (Set.range ((fun i : m => (M.map g) i) ∘ a)) := by
        rw [hspan]; exact Submodule.subset_span ⟨i, rfl⟩
      have key : ∀ y ∈ Submodule.span K (Set.range ((fun i : m => (M.map g) i) ∘ a)),
          y ⬝ᵥ x = 0 := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨k, rfl⟩ := hy
          exact congrFun hx k
        | zero => simp
        | add y z _ _ hy hz => rw [add_dotProduct, hy, hz, add_zero]
        | smul c y _ hy => rw [smul_dotProduct, hy, smul_zero]
      exact key _ hi
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this
  let e : l ≃ κ := Fintype.equivOfCardEq (le_antisymm h2 h1)
  let N : Matrix l l R := M.submatrix (a ∘ e) id
  have hN : IsUnit (N.map g) := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact hli.comp e e.injective
  refine ⟨N.det, N.adjugate * (1 : Matrix m m R).submatrix (a ∘ e) id, ?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det] at hN
    have : g N.det = (N.map g).det := by rw [RingHom.map_det]; rfl
    rw [this]; exact hN.ne_zero
  · rw [Matrix.mul_assoc]
    have : (1 : Matrix m m R).submatrix (a ∘ e) id * M = N := by
      ext i j
      simp [N, Matrix.mul_apply, Matrix.one_apply]
    rw [this, Matrix.adjugate_mul]

theorem exists_kernel_certificate {R K : Type} [CommRing R] [Field K] (g : R →+* K)
    {a b c : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a]
    (D₀ : Matrix b a R) (D₁ : Matrix c b R) (h0 : D₁ * D₀ = 0)
    (hex : ∀ w : b → K, (D₁.map g).mulVec w = 0 → ∃ v, (D₀.map g).mulVec v = w) :
    ∃ (r : R) (n : ℕ) (B : Matrix a (Fin n) R) (C : Matrix (Fin n) a R) (H : Matrix a b R),
      g r ≠ 0 ∧ D₀ * B = 0 ∧ C * B = r • (1 : Matrix (Fin n) (Fin n) R) ∧
        B * C + H * D₀ = r • (1 : Matrix a a R) := by
  classical
  obtain ⟨κ, s, hs, hspan, hli⟩ := exists_linearIndependent' K (fun j : a => (D₀.map g).col j)
  have : Fintype κ := Fintype.ofInjective s hs
  let S : Matrix a κ R := (1 : Matrix a a R).submatrix id s
  have hDS : D₀ * S = D₀.submatrix id s := by
    ext i j
    simp [S, Matrix.mul_apply, Matrix.one_apply]
  have hsum : ∀ x : κ → K, ((D₀ * S).map g).mulVec x =
      ∑ k, x k • ((fun j : a => (D₀.map g).col j) ∘ s) k := by
    intro x
    funext i
    simp [hDS, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  obtain ⟨r₀, T₀, hr₀, hT₀⟩ := exists_mul_eq_smul_one_of_mulVec_injective g (D₀ * S) (by
    intro x hx
    rw [hsum] at hx
    funext k
    exact Fintype.linearIndependent_iff.1 hli x hx k)
  obtain ⟨r₁, T₁, hr₁, hT₁⟩ := exists_mul_eq_smul_one_of_mulVec_injective g
    (Matrix.fromRows T₀ D₁) (by
    intro w hw
    have hw1 : (T₀.map g).mulVec w = 0 := by
      funext k; exact congrFun hw (Sum.inl k)
    have hw2 : (D₁.map g).mulVec w = 0 := by
      funext k; exact congrFun hw (Sum.inr k)
    obtain ⟨v, hv⟩ := hex w hw2
    have hmem : w ∈ Submodule.span K (Set.range ((fun j : a => (D₀.map g).col j) ∘ s)) := by
      rw [hspan, ← hv]
      have : (D₀.map g).mulVec v = ∑ j, v j • (D₀.map g).col j := by
        funext i
        simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
      rw [this]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
    rw [← hsum] at hu
    rw [← hu, Matrix.mulVec_mulVec, ← Matrix.map_mul, hT₀] at hw1
    have hu0 : u = 0 := by
      funext k
      have := congrFun hw1 k
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite g] at this
      rcases this with h | h
      · exact absurd h hr₀
      · exact h
    rw [← hu, hu0, Matrix.mulVec_zero])
  let Q : Matrix a a R := r₀ • (1 : Matrix a a R) - S * T₀ * D₀
  have hQS : Q * S = 0 := by
    simp only [Q, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hT₀,
      Matrix.mul_smul, Matrix.mul_one, sub_self]
  have hDQ : r₁ • (D₀ * Q) = 0 := by
    have h1 : T₀ * (D₀ * Q) = 0 := by
      have : T₀ * (D₀ * (S * T₀ * D₀)) = (T₀ * (D₀ * S)) * (T₀ * D₀) := by
        simp only [Matrix.mul_assoc]
      simp only [Q, Matrix.mul_sub, this, hT₀, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul, sub_self]
    have h2 : D₁ * (D₀ * Q) = 0 := by rw [← Matrix.mul_assoc, h0, Matrix.zero_mul]
    have h3 : Matrix.fromRows T₀ D₁ * (D₀ * Q) = 0 := by
      rw [Matrix.fromRows_mul, h1, h2, Matrix.fromRows_zero]
    calc r₁ • (D₀ * Q) = (T₁ * Matrix.fromRows T₀ D₁) * (D₀ * Q) := by
          rw [hT₁, Matrix.smul_mul, Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, h3, Matrix.mul_zero]
  let t := {j : a // j ∉ Set.range s}
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  let f : Fin (Fintype.card t) → a := fun i => (e i).1
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hfs : ∀ i k, f i ≠ s k := fun i k h => (e i).2 ⟨k, h.symm⟩
  let E : Matrix a (Fin (Fintype.card t)) R := (1 : Matrix a a R).submatrix id f
  have hEE : E.transpose * E = 1 := by
    ext i j
    simp [E, Matrix.mul_apply, Matrix.one_apply, hf.eq_iff]
  have hES : E.transpose * S = 0 := by
    ext i j
    simp [E, S, Matrix.mul_apply, Matrix.one_apply, hfs]
  have hQE : Q * E * E.transpose = Q := by
    ext i j
    have hQE' : Q * E = Q.submatrix id f := by
      ext i j
      simp [E, Matrix.mul_apply, Matrix.one_apply]
    rw [hQE']
    by_cases hj : j ∈ Set.range s
    · obtain ⟨k, rfl⟩ := hj
      have : Q i (s k) = (Q * S) i k := by
        simp [S, Matrix.mul_apply, Matrix.one_apply]
      rw [this, hQS]
      simp [E, Matrix.mul_apply, Matrix.one_apply, hfs]
    · obtain ⟨k, hk⟩ : ∃ k, f k = j := ⟨e.symm ⟨j, hj⟩, by simp [f]⟩
      subst hk
      simp [E, Matrix.mul_apply, Matrix.one_apply, hf.eq_iff]
  refine ⟨r₁ * r₀, _, r₁ • (Q * E), E.transpose, r₁ • (S * T₀), ?_, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hr₁ hr₀
  · rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.smul_mul, hDQ, Matrix.zero_mul]
  · have : E.transpose * (S * T₀ * D₀ * E) = (E.transpose * S) * (T₀ * D₀ * E) := by
      simp only [Matrix.mul_assoc]
    simp only [Q, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, this, hES, Matrix.zero_mul,
      sub_zero, Matrix.smul_mul, Matrix.one_mul, hEE, smul_smul]
  · rw [Matrix.smul_mul, Matrix.smul_mul, hQE, ← smul_add, mul_smul]
    simp only [Q, sub_add_cancel]

theorem exists_matrix_basis_ker_of_exact_at_point :
    ∀ (R K : Type) [CommRing R] [Field K] (g₀ : R →+* K) (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) R) (D₁ : Matrix (Fin c) (Fin b) R), D₁ * D₀ = 0 → (∀ w : Fin b → K, (D₁.map g₀).mulVec w = 0 → ∃ v, (D₀.map g₀).mulVec v = w) → ∃ (r : R) (n : ℕ) (B : Matrix (Fin a) (Fin n) R), g₀ r ≠ 0 ∧ D₀ * B = 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g r) → ∀ v : Fin a → R', (D₀.map g).mulVec v = 0 → ∃! z : Fin n → R', (B.map g).mulVec z = v := by
  intro R K _ _ g₀ a b c D₀ D₁ h0 hex
  obtain ⟨r, n, B, C, H, hr, hB, hCB, hBC⟩ := exists_kernel_certificate g₀ D₀ D₁ h0 hex
  refine ⟨r, n, B, hr, hB, ?_⟩
  intro R' _ g hu v hv
  obtain ⟨u, hu⟩ := hu
  have hone : ∀ (m : ℕ) (x : Fin m → R'),
      ((r • (1 : Matrix (Fin m) (Fin m) R)).map g).mulVec x = g r • x := by
    intro m x
    funext k
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite g]
  have h1 : ∀ z : Fin n → R', (C.map g).mulVec ((B.map g).mulVec z) = (u : R') • z := by
    intro z
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hCB, hone, hu]
  have h2 : (B.map g).mulVec ((C.map g).mulVec v) = (u : R') • v := by
    rw [hu, ← hone, ← hBC, Matrix.map_add _ (map_add g), Matrix.add_mulVec, Matrix.map_mul,
      Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero,
      add_zero]
  refine ⟨((u⁻¹ : R'ˣ) : R') • (C.map g).mulVec v, ?_, ?_⟩
  · show (B.map g).mulVec _ = v
    rw [Matrix.mulVec_smul, h2, smul_smul, Units.inv_mul, one_smul]
  · intro z hz
    rw [← hz, h1, smul_smul, Units.inv_mul, one_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsNoetherianModelOfSmooth
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothDescent

open TensorProduct

theorem exists_common_model (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B]
    [Algebra R C] [Algebra.Smooth R B] [Algebra.Smooth R C] :
    ∃ (A B₁ C₁ : Type) (_ : CommRing A) (_ : Algebra A R) (_ : CommRing B₁) (_ : CommRing C₁)
      (_ : Algebra A B₁) (_ : Algebra A C₁), IsNoetherianRing A ∧ Algebra.Smooth A B₁ ∧
      Algebra.Smooth A C₁ ∧ Nonempty (R ⊗[A] B₁ ≃ₐ[R] B) ∧ Nonempty (R ⊗[A] C₁ ≃ₐ[R] C) := by
  obtain ⟨A₁, B₁, _, _, hA₁, _, ⟨eB⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ R B
  obtain ⟨A₂, C₁, _, _, hA₂, _, ⟨eC⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ R C
  let A : Subalgebra ℤ R := A₁ ⊔ A₂
  let : Algebra A₁ A := (Subalgebra.inclusion (le_sup_left : A₁ ≤ A)).toRingHom.toAlgebra
  let : Algebra A₂ A := (Subalgebra.inclusion (le_sup_right : A₂ ≤ A)).toRingHom.toAlgebra
  have : IsScalarTower A₁ A R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A₂ A R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType ℤ A := (Subalgebra.fg_iff_finiteType A).mp (hA₁.sup hA₂)
  exact ⟨A, A ⊗[A₁] B₁, A ⊗[A₂] C₁, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, Algebra.FiniteType.isNoetherianRing ℤ A, inferInstance,
    inferInstance, ⟨(Algebra.TensorProduct.cancelBaseChange A₁ A R R B₁).trans eB.symm⟩,
    ⟨(Algebra.TensorProduct.cancelBaseChange A₂ A R R C₁).trans eC.symm⟩⟩

variable {A R B₁ C₁ : Type} [CommRing A] [CommRing R] [CommRing B₁] [CommRing C₁] [Algebra A R]
  [Algebra A B₁] [Algebra A C₁]

noncomputable abbrev incl (C₁ : Type) [CommRing C₁] [Algebra A C₁] (S : Subalgebra A R) :
    S ⊗[A] C₁ →ₐ[A] R ⊗[A] C₁ :=
  Algebra.TensorProduct.map S.val (AlgHom.id A C₁)

theorem range_incl_mono {S T : Subalgebra A R} (h : S ≤ T) :
    (incl C₁ S).range ≤ (incl C₁ T).range := by
  have e : incl C₁ S = (incl C₁ T).comp
      (Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id A C₁)) :=
    Algebra.TensorProduct.ext' fun _ _ => rfl
  rw [e]
  exact AlgHom.range_comp_le_range _ _

theorem exists_fg_mem_range_incl (x : R ⊗[A] C₁) :
    ∃ S : Subalgebra A R, S.FG ∧ x ∈ (incl C₁ S).range := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨⊥, Subalgebra.fg_bot, zero_mem _⟩
  | tmul r c =>
    exact ⟨Algebra.adjoin A {r}, ⟨{r}, by simp⟩,
      (AlgHom.mem_range _).mpr ⟨⟨r, Algebra.subset_adjoin rfl⟩ ⊗ₜ c, rfl⟩⟩
  | add x y hx hy =>
    obtain ⟨S, hS, hxS⟩ := hx
    obtain ⟨T, hT, hyT⟩ := hy
    exact ⟨S ⊔ T, hS.sup hT,
      add_mem (range_incl_mono le_sup_left hxS) (range_incl_mono le_sup_right hyT)⟩

theorem exists_fg_subset_range_incl (t : Finset (R ⊗[A] C₁)) :
    ∃ S : Subalgebra A R, S.FG ∧ (t : Set (R ⊗[A] C₁)) ⊆ (incl C₁ S).range := by
  classical
  refine Finset.induction_on t ⟨⊥, Subalgebra.fg_bot, by simp⟩ ?_
  intro a t _ ih
  obtain ⟨S, hS, hSt⟩ := ih
  obtain ⟨T, hT, haT⟩ := exists_fg_mem_range_incl (C₁ := C₁) a
  refine ⟨S ⊔ T, hS.sup hT, ?_⟩
  rw [Finset.coe_insert, Set.insert_subset_iff]
  exact ⟨range_incl_mono le_sup_right haT,
    hSt.trans (SetLike.coe_subset_coe.mpr (range_incl_mono le_sup_left))⟩

theorem exists_fg_range_le [Algebra.FiniteType A B₁] (φ : B₁ →ₐ[A] R ⊗[A] C₁) :
    ∃ S : Subalgebra A R, S.FG ∧ φ.range ≤ (incl C₁ S).range := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A B₁).FG)
  obtain ⟨S, hS, hsub⟩ := exists_fg_subset_range_incl (C₁ := C₁) (s.image φ)
  refine ⟨S, hS, ?_⟩
  rw [← Algebra.map_top, ← hs, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
  rwa [Finset.coe_image] at hsub

theorem incl_injective [Module.Flat A C₁] (S : Subalgebra A R) :
    Function.Injective (incl C₁ S) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := C₁) S.val.toLinearMap
    Subtype.val_injective

theorem exists_lift {D E : Type} [CommRing D] [CommRing E] [Algebra A D] [Algebra A E]
    (φ : B₁ →ₐ[A] E) (i : D →ₐ[A] E) (hi : Function.Injective i) (h : φ.range ≤ i.range) :
    ∃ ψ : B₁ →ₐ[A] D, ∀ b, i (ψ b) = φ b := by
  let e := AlgEquiv.ofInjective i hi
  let φ' := φ.codRestrict i.range fun b => h (AlgHom.mem_range_self φ b)
  refine ⟨e.symm.toAlgHom.comp φ', fun b => ?_⟩
  have h1 : ((e (e.symm (φ' b)) : i.range) : E) = (φ' b : E) := by rw [e.apply_symm_apply]
  exact h1

theorem cancel_one_tmul (S : Subalgebra A R) (x : S ⊗[A] C₁) :
    Algebra.TensorProduct.cancelBaseChange A S R R C₁ (1 ⊗ₜ x) = incl C₁ S x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s c => simp [Algebra.TensorProduct.cancelBaseChange_tmul, incl, Algebra.smul_def]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add, hx, hy, map_add]

theorem incl_tmul (S : Subalgebra A R) (s : S) (c : C₁) :
    incl C₁ S (s ⊗ₜ c) = (s : R) • ((1 : R) ⊗ₜ[A] c) := by
  simp [incl, TensorProduct.smul_tmul']

theorem incl_smul (S : Subalgebra A R) (s : S) (x : S ⊗[A] C₁) :
    incl C₁ S (s • x) = (s : R) • incl C₁ S x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s' c => simp [incl, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

noncomputable def extend (S : Subalgebra A R) {D : Type} [CommRing D] [Algebra A D] [Algebra S D]
    [IsScalarTower A S D] (ψ : B₁ →ₐ[A] D) : S ⊗[A] B₁ →ₐ[S] D :=
  Algebra.TensorProduct.lift (Algebra.ofId S D) ψ fun _ _ => Commute.all _ _

theorem extend_tmul (S : Subalgebra A R) {D : Type} [CommRing D] [Algebra A D] [Algebra S D]
    [IsScalarTower A S D] (ψ : B₁ →ₐ[A] D) (s : S) (b : B₁) :
    extend S ψ (s ⊗ₜ b) = s • ψ b := by
  simp [extend, Algebra.smul_def]

theorem incl_extend (S : Subalgebra A R) (F : R ⊗[A] B₁ →ₐ[R] R ⊗[A] C₁)
    (ψ : B₁ →ₐ[A] S ⊗[A] C₁) (h : ∀ b, incl C₁ S (ψ b) = F (1 ⊗ₜ b)) (x : S ⊗[A] B₁) :
    incl C₁ S (extend S ψ x) = F (incl B₁ S x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s b => rw [extend_tmul, incl_smul, h, incl_tmul, map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem val_extend (S : Subalgebra A R) (F : R ⊗[A] B₁ →ₐ[R] R)
    (ψ : B₁ →ₐ[A] S) (h : ∀ b, S.val (ψ b) = F (1 ⊗ₜ b)) (x : S ⊗[A] B₁) :
    S.val (extend S ψ x) = F (incl B₁ S x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s b =>
    rw [extend_tmul, smul_eq_mul, map_mul, h, incl_tmul, map_smul, smul_eq_mul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end GlobalTheory.SmoothDescent

namespace GlobalTheory

open TensorProduct SmoothDescent

theorem exists_noetherian_model_of_smooth :
    ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra.Smooth R B] [Algebra.Smooth R C] (f g : B →ₐ[R] C) (r : B →ₐ[R] R), ∃ (R₀ B₀ C₀ : Type) (_ : CommRing R₀) (_ : IsNoetherianRing R₀) (_ : Algebra R₀ R) (_ : CommRing B₀) (_ : CommRing C₀) (_ : Algebra R₀ B₀) (_ : Algebra R₀ C₀) (f₀ g₀ : B₀ →ₐ[R₀] C₀) (r₀ : B₀ →ₐ[R₀] R₀) (β' : TensorProduct R₀ R B₀ ≃ₐ[R] B) (δ' : TensorProduct R₀ R C₀ ≃ₐ[R] C), Module.Flat R₀ B₀ ∧ Module.Flat R₀ C₀ ∧ ∀ b : B₀, f (β' (1 ⊗ₜ b)) = δ' (1 ⊗ₜ f₀ b) ∧ g (β' (1 ⊗ₜ b)) = δ' (1 ⊗ₜ g₀ b) ∧ r (β' (1 ⊗ₜ b)) = algebraMap R₀ R (r₀ b) := by
  intro R B C _ _ _ _ _ _ _ f g r
  obtain ⟨A, B₁, C₁, _, _, _, _, _, _, hA, hB, hC, ⟨eB⟩, ⟨eC⟩⟩ := exists_common_model R B C
  let F : R ⊗[A] B₁ →ₐ[R] R ⊗[A] C₁ := (eC.symm.toAlgHom.comp f).comp eB.toAlgHom
  let G : R ⊗[A] B₁ →ₐ[R] R ⊗[A] C₁ := (eC.symm.toAlgHom.comp g).comp eB.toAlgHom
  let ρ : R ⊗[A] B₁ →ₐ[R] R := r.comp eB.toAlgHom
  let j : B₁ →ₐ[A] R ⊗[A] B₁ := Algebra.TensorProduct.includeRight
  let φF : B₁ →ₐ[A] R ⊗[A] C₁ := (F.restrictScalars A).comp j
  let φG : B₁ →ₐ[A] R ⊗[A] C₁ := (G.restrictScalars A).comp j
  let φr : B₁ →ₐ[A] R := (ρ.restrictScalars A).comp j
  obtain ⟨S₁, hS₁, h₁⟩ := exists_fg_range_le (C₁ := C₁) φF
  obtain ⟨S₂, hS₂, h₂⟩ := exists_fg_range_le (C₁ := C₁) φG
  have h₃ : φr.range.FG := by
    rw [← Algebra.map_top]
    exact Subalgebra.FG.map φr Algebra.FiniteType.out
  let S : Subalgebra A R := S₁ ⊔ S₂ ⊔ φr.range
  have : Algebra.FiniteType A S := (Subalgebra.fg_iff_finiteType S).mp ((hS₁.sup hS₂).sup h₃)
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing A S
  have hF : φF.range ≤ (incl C₁ S).range :=
    h₁.trans (range_incl_mono (le_sup_left.trans le_sup_left))
  have hG : φG.range ≤ (incl C₁ S).range :=
    h₂.trans (range_incl_mono (le_sup_right.trans le_sup_left))
  have hr : φr.range ≤ S.val.range := by
    rw [Subalgebra.range_val]
    exact le_sup_right
  obtain ⟨ψF, hψF⟩ := exists_lift φF (incl C₁ S) (incl_injective S) hF
  obtain ⟨ψG, hψG⟩ := exists_lift φG (incl C₁ S) (incl_injective S) hG
  obtain ⟨ψr, hψr⟩ := exists_lift φr S.val Subtype.val_injective hr
  refine ⟨S, S ⊗[A] B₁, S ⊗[A] C₁, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, extend S ψF, extend S ψG, extend S ψr,
    (Algebra.TensorProduct.cancelBaseChange A S R R B₁).trans eB,
    (Algebra.TensorProduct.cancelBaseChange A S R R C₁).trans eC, inferInstance, inferInstance,
    fun b => ⟨?_, ?_, ?_⟩⟩
  · rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, cancel_one_tmul, cancel_one_tmul,
      incl_extend S F ψF hψF]
    simp [F]
  · rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, cancel_one_tmul, cancel_one_tmul,
      incl_extend S G ψG hψG]
    simp [G]
  · rw [AlgEquiv.trans_apply, cancel_one_tmul]
    change _ = S.val (extend S ψr b)
    rw [val_extend S ρ ψr hψr]
    simp [ρ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem forall_geometricallyIntegral_of_smooth_of_geometricallyConnected :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f →
      GeometricallyIntegral f :=
  fun _ _ f _ _ ↦ geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres f

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem formallyUnramified_mulA (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ)
    (hn : IsUnit (n : Γ(S, ⊤))) : FormallyUnramified (mulA G n).left := by
  have h : mulN G n = mulA G n :=
    (Category.id_comp _).symm.trans (MulUnramified.comp_mulN G (𝟙 G) n)
  rw [← h]
  exact formallyUnramified_mulN S G n hn

end GlobalTheory
end

