import Mathlib
import Formalism.LocalRingCardinality.DataLevel
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0006
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.HermitianLattices.StatementLat
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMemProjEqOnFinset
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory

theorem exists_mem_proj_eq_on_finset {G ι : Type} [Group G] {Gv : ι → Type}
    [∀ v, Group (Gv v)] (π : ∀ v, G →* Gv v) (H : Subgroup G) (Kv : ∀ v, Subgroup (Gv v))
    (hH : ∀ v, ∀ h ∈ Kv v, ∃ g ∈ H, π v g = h ∧ ∀ w, w ≠ v → π w g = 1)
    (h : ∀ v, Gv v) (hh : ∀ v, h v ∈ Kv v) (T : Finset ι) :
    ∃ g ∈ H, (∀ v ∈ T, π v g = h v) ∧ ∀ v, v ∉ T → π v g = 1 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, H.one_mem, by simp, by simp⟩
  | insert a T ha ih =>
    obtain ⟨g, hg, h1, h2⟩ := ih
    obtain ⟨g', hg', h3, h4⟩ := hH a (h a) (hh a)
    refine ⟨g' * g, H.mul_mem hg' hg, ?_, ?_⟩
    · intro v hv
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [map_mul, h3, h2 _ ha, mul_one]
      · have hne : v ≠ a := fun e => ha (e ▸ hv)
        rw [map_mul, h4 v hne, h1 v hv, one_mul]
    · intro v hv
      rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, h4 v hv.1, h2 v hv.2, one_mul]

theorem index_pi_univ_dep {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)]
    (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem relIndex_eq_prod_local :
    ∀ (G ι : Type) [Group G] (Gv : ι → Type) [∀ v, Group (Gv v)] (π : ∀ v, G →* Gv v)
      (H K U : Subgroup G) (Kv Uv : ∀ v, Subgroup (Gv v)) (S : Finset ι),
      (∀ v, ∀ h ∈ Kv v, ∃ g ∈ H, π v g = h ∧ ∀ w, w ≠ v → π w g = 1) →
      (∀ g, g ∈ K ↔ g ∈ H ∧ ∀ v, π v g ∈ Kv v) →
      (∀ g, g ∈ U ↔ g ∈ H ∧ ∀ v, π v g ∈ Uv v) →
      (∀ v, v ∉ S → Kv v ≤ Uv v) →
      U.relIndex K = ∏ v ∈ S, (Uv v).relIndex (Kv v) := by
  intro G ι _ Gv _ π H K U Kv Uv S hH hK hU hS
  classical
  let f : K →* (∀ v : S, Kv v) :=
    { toFun := fun g v => ⟨π v g, ((hK g).1 g.2).2 v⟩
      map_one' := by
        funext v
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        funext v
        apply Subtype.ext
        simp }
  have hf : Function.Surjective f := by
    intro x
    let h : ∀ v, Gv v := fun v => if hv : v ∈ S then (x ⟨v, hv⟩ : Gv v) else 1
    have hh : ∀ v, h v ∈ Kv v := by
      intro v
      by_cases hv : v ∈ S
      · simp only [h, dif_pos hv]; exact (x ⟨v, hv⟩).2
      · simp only [h, dif_neg hv]; exact (Kv v).one_mem
    obtain ⟨g, hg, h1, h2⟩ := exists_mem_proj_eq_on_finset π H Kv hH h hh S
    have hgK : g ∈ K := by
      refine (hK g).2 ⟨hg, fun v => ?_⟩
      by_cases hv : v ∈ S
      · rw [h1 v hv]; exact hh v
      · rw [h2 v hv]; exact (Kv v).one_mem
    refine ⟨⟨g, hgK⟩, ?_⟩
    funext v
    apply Subtype.ext
    change π v g = _
    rw [h1 v v.2]
    simp only [h, dif_pos v.2]
  have hc : U.subgroupOf K =
      (Subgroup.pi Set.univ fun v : S => (Uv v).subgroupOf (Kv v)).comap f := by
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, hU]
    constructor
    · rintro ⟨-, h⟩ v -
      exact Subgroup.mem_subgroupOf.2 (h v)
    · intro h
      refine ⟨((hK g).1 g.2).1, fun v => ?_⟩
      by_cases hv : v ∈ S
      · exact Subgroup.mem_subgroupOf.1 (h ⟨v, hv⟩ (Set.mem_univ _))
      · exact hS v hv (((hK g).1 g.2).2 v)
  rw [Subgroup.relIndex, hc, Subgroup.index_comap_of_surjective _ hf, index_pi_univ_dep]
  exact Finset.prod_coe_sort S (fun v => (Uv v).relIndex (Kv v))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsUnitriGlEquiv
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.UniIndexPrime

theorem diag_mul {k : ℕ} {A : Type} [CommRing A] {x y : Matrix (Fin k) (Fin k) A}
    (hx : ∀ i j, j < i → x i j = 0) (hy : ∀ i j, j < i → y i j = 0) (i : Fin k) :
    (x * y) i i = x i i * y i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hx i j h, zero_mul]
  · rw [hy j i h, mul_zero]

def uniSub (k : ℕ) (A : Type) [CommRing A] : Subgroup (GL (Fin k) A) where
  carrier := upperUni k A
  one_mem' := fun i j => ⟨fun h => by simp [Matrix.one_apply_ne h.ne'], by simp⟩
  mul_mem' := by
    intro x y hx hy i j
    have bx : BlockTriangular (x : Matrix (Fin k) (Fin k) A) id := fun a b h => (hx a b).1 h
    have by' : BlockTriangular (y : Matrix (Fin k) (Fin k) A) id := fun a b h => (hy a b).1 h
    refine ⟨fun h => (bx.mul by') h, ?_⟩
    rw [Units.val_mul, diag_mul (fun a b h => (hx a b).1 h) (fun a b h => (hy a b).1 h),
      (hx i i).2, (hy i i).2, one_mul]
  inv_mem' := by
    intro x hx i j
    have bx : BlockTriangular (x : Matrix (Fin k) (Fin k) A) id := fun a b h => (hx a b).1 h
    letI : Invertible (x : Matrix (Fin k) (Fin k) A) := x.invertible
    have bi : BlockTriangular ((x⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) id := by
      rw [Matrix.coe_units_inv]
      exact blockTriangular_inv_of_blockTriangular bx
    refine ⟨fun h => bi h, ?_⟩
    have h := diag_mul (fun a b h => (hx a b).1 h) (fun a b h => bi (show id b < id a from h)) i
    rw [Units.mul_inv, (hx i i).2, one_mul] at h
    simpa using h.symm

theorem closure_eq (k : ℕ) (A : Type) [CommRing A] :
    Subgroup.closure (upperUni k A) = uniSub k A := Subgroup.closure_eq (uniSub k A)

theorem mem_uniSub {k : ℕ} {A : Type} [CommRing A] (x : GL (Fin k) A) :
    x ∈ uniSub k A ↔ IsUnitri (x : Matrix (Fin k) (Fin k) A) :=
  ⟨fun h => ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2⟩,
    fun h i j => ⟨h.1 i j, h.2 i⟩⟩

def glEquiv (k : ℕ) {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) :
    GL (Fin k) A ≃* GL (Fin k) B :=
  Units.mapEquiv (e.mapMatrix (m := Fin k)).toMulEquiv

theorem glEquiv_apply (k : ℕ) {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (x : GL (Fin k) A) (i j : Fin k) :
    (glEquiv k e x : Matrix (Fin k) (Fin k) B) i j = e ((x : Matrix (Fin k) (Fin k) A) i j) := rfl

theorem isUnitri_glEquiv (k : ℕ) {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (x : GL (Fin k) A) :
    IsUnitri (x : Matrix (Fin k) (Fin k) A) ↔
      IsUnitri (glEquiv k e x : Matrix (Fin k) (Fin k) B) := by
  simp only [IsUnitri, glEquiv_apply, EmbeddingLike.map_eq_zero_iff, EmbeddingLike.map_eq_one_iff]

theorem index_upperUni : ∀ (κ : Type) [CommRing κ] (g k : ℕ), g.Prime → Nat.card κ = g →
    (((Subgroup.closure (upperUni k κ)).index : ℕ) : ℝ) = idxColLoc g k := by
  intro κ _ g k hg hc
  haveI : Finite κ := Nat.finite_of_card_ne_zero (hc ▸ hg.ne_zero)
  letI : Fintype κ := Fintype.ofFinite κ
  have e : ZMod g ≃+* κ := ZMod.ringEquivOfPrime κ hg (by rw [← Nat.card_eq_fintype_card, hc])
  have h1 : Nat.card (GL (Fin k) (ZMod g)) = Nat.card (GL (Fin k) κ) :=
    Nat.card_congr (glEquiv k e).toEquiv
  have h2 : Nat.card {A : GL (Fin k) (ZMod g) // IsUnitri (A : Matrix (Fin k) (Fin k) (ZMod g))} =
      Nat.card (uniSub k κ) :=
    Nat.card_congr ((glEquiv k e).toEquiv.subtypeEquiv fun x =>
      (isUnitri_glEquiv k e x).trans (mem_uniSub _).symm)
  have h3 : (Nat.card (uniSub k κ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := uniSub k κ)).ne'
  rw [closure_eq, idxColLoc, idxLoc, h1, h2, eq_div_iff h3]
  exact_mod_cast (uniSub k κ).index_mul_card

end GlobalTheory.UniIndexPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitStabGLIffMemRange
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory

theorem stabGL_iff_conj_stdLat {A : Type} [CommRing A] (S : Subring A) {n : Type} [Fintype n]
    [DecidableEq n] (b : GL n A) (Λ : Submodule S (n → A))
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ S) (g : GL n A) :
    g ∈ stabGL Λ ↔ b⁻¹ * g * b ∈ stabGL (stdLat (n := n) (A := A) S) := by
  have key : ∀ x : n → A, x ∈ Λ ↔ (b⁻¹).1 *ᵥ x ∈ stdLat (n := n) (A := A) S := fun x => by
    rw [hΛ, Formalism.UG.P.afsplit_mem_stdLat]
  constructor
  · intro hg y
    have h := hg (b.1 *ᵥ y)
    rw [key, key] at h
    simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Units.val_mul,
      Matrix.mul_assoc] using h
  · intro hg x
    have h := hg ((b⁻¹).1 *ᵥ x)
    rw [key, key]
    simpa only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.mul_one, Units.val_mul,
      Matrix.mul_assoc] using h

theorem conj_mem_UJ_one {A : Type} [CommRing A] (τ : A →+* A) {n : Type} [Fintype n]
    [DecidableEq n] (J : Matrix n n A) (b : GL n A) (hb : cT τ b.1 * J * b.1 = 1)
    (g : GL n A) (hg : g ∈ UJ τ J) : b⁻¹ * g * b ∈ UJ τ (1 : Matrix n n A) := by
  have hg' : cT τ g.1 * J * g.1 = J := hg
  have cm : ∀ M N : Matrix n n A, cT τ (M * N) = cT τ N * cT τ M := fun M N => by
    simp only [cT, Matrix.map_mul, Matrix.transpose_mul]
  have c1 : cT τ (1 : Matrix n n A) = 1 := by
    simp only [cT, Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.transpose_one]
  have hJ : cT τ (b⁻¹).1 * (b⁻¹).1 = J := by
    calc cT τ (b⁻¹).1 * (b⁻¹).1 = cT τ (b⁻¹).1 * (cT τ b.1 * J * b.1) * (b⁻¹).1 := by
          rw [hb, Matrix.mul_one]
      _ = cT τ (b.1 * (b⁻¹).1) * J * (b.1 * (b⁻¹).1) := by
          rw [cm]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, c1, Matrix.one_mul, Matrix.mul_one]
  change cT τ (b⁻¹ * g * b).1 * 1 * (b⁻¹ * g * b).1 = 1
  calc cT τ (b⁻¹ * g * b).1 * 1 * (b⁻¹ * g * b).1
      = cT τ b.1 * (cT τ g.1 * (cT τ (b⁻¹).1 * (b⁻¹).1) * g.1) * b.1 := by
        simp only [Units.val_mul, cm, Matrix.mul_one, Matrix.mul_assoc]
    _ = 1 := by rw [hJ, hg', hb]

theorem split_stabGL_iff_mem_range :
    ∀ (A K : Type) [CommRing A] [Field K] (O : ValuationSubring K) (S : Subring A) (τ : A →+* A) (φ : A ≃+* K × K), (∀ x, φ (τ x) = swapR K (φ x)) → (∀ x, x ∈ S ↔ (φ x).1 ∈ O ∧ (φ x).2 ∈ O) → ∀ (n : Type) [Fintype n] [DecidableEq n] (J : Matrix n n A) (b : GL n A) (Λ : Submodule S (n → A)), cT τ b.1 * J * b.1 = 1 → (∀ x, x ∈ Λ ↔ ∀ i, ((b⁻¹).1 *ᵥ x) i ∈ S) → ∀ g ∈ UJ τ J, g ∈ stabGL Λ ↔ (bc ((RingHom.fst K K).comp φ.toRingHom) b)⁻¹ * bc ((RingHom.fst K K).comp φ.toRingHom) g * bc ((RingHom.fst K K).comp φ.toRingHom) b ∈ (bc (n := n) (algebraMap O K)).range := by
  intro A K _ _ O S τ φ hτ hS n _ _ J b Λ hb hΛ g hg
  have hU := conj_mem_UJ_one τ J b hb g hg
  rw [stabGL_iff_conj_stdLat S b Λ hΛ g, ← map_inv, ← map_mul, ← map_mul]
  generalize b⁻¹ * g * b = h at hU
  have hinj : Function.Injective (algebraMap O K) := Subtype.val_injective
  have hOr : ∀ x : K, x ∈ Set.range (algebraMap O K) ↔ x ∈ O :=
    fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  rw [Formalism.UG.P.afsplit_stab_iff, Formalism.UG.P.levelvsplit_mem_range_iff _ hinj, ← map_inv,
    Formalism.UG.P.levelvsplit_coe_bc, Formalism.UG.P.levelvsplit_coe_bc]
  simp only [hOr, hS]
  have main : ∀ k : GL n A, k ∈ UJ τ (1 : Matrix n n A) → ∀ i j,
      (φ (k.1 i j)).2 = (φ ((k⁻¹).1 j i)).1 := by
    intro k hk i j
    have rel := Formalism.UG.P.levelvsplit_unitary τ φ hτ _ k hk
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at rel
    have hk1 : k.1.map ((RingHom.fst K K).comp φ.toRingHom) *
        (k⁻¹).1.map ((RingHom.fst K K).comp φ.toRingHom) = 1 := by
      rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have s := Formalism.UG.P.levelvsplit_solve 1 1 _ _ _ (Matrix.mul_one _) hk1 rel
    rw [Matrix.one_mul, Matrix.mul_one] at s
    exact congrFun (congrFun s i) j
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => (h1 i j).1, fun i j => (h2 i j).1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ⟨h1 i j, ?_⟩, fun i j => ⟨h2 i j, ?_⟩⟩
    · rw [main h hU]; exact h2 j i
    · rw [main h⁻¹ (inv_mem hU), inv_inv]; exact h1 j i

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitVectorPerpAllIff
section
noncomputable section

namespace GlobalTheory.UnitVectorPerpCompare

open NumberField Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem perp_eq (W : HSpace E) (x : W.V) : UnitVectorOrthogonal.perp W x = SelfDualLatticeComplements.perp W x := rfl

theorem perpLat_eq (W : HSpace E) (L : Submodule (𝓞 E) W.V) (x : W.V) :
    UnitVectorOrthogonal.perpLat W L x = L ⊓ (SelfDualLatticeComplements.perp W x).restrictScalars (𝓞 E) := rfl

theorem selfDual_iff (W : HSpace E) (L : Submodule (𝓞 E) W.V) :
    UnitVectorOrthogonal.IsSelfDualLat W L ↔ SelfDualLatticeComplements.IsSelfDualLattice W L := Iff.rfl

theorem ofKind_iff (W : HSpace E) (M P Q : ℕ) :
    UnitVectorOrthogonal.OfKind W M P Q ↔ SelfDualLatticeComplements.OfKind W M P Q :=
  ⟨fun ⟨a, b, c⟩ => ⟨b, a, c⟩, fun ⟨a, b, c⟩ => ⟨b, a, c⟩⟩

theorem hasComplement_iff (W : HSpace E) (x : W.V) (M' P' Q' : ℕ) :
    UnitVectorOrthogonal.HasComplement W x M' P' Q' ↔ SelfDualLatticeComplements.HasComplement W x M' P' Q' := by
  constructor
  · rintro ⟨L, hL, hx, hs, W', ι, hk, hi, hr, hm⟩
    exact ⟨L, W', ι, (selfDual_iff W L).1 hL, hx, (ofKind_iff _ _ _ _).1 hk, hi, hr, hm, hs⟩
  · rintro ⟨L, W', ι, hL, hx, hk, hi, hr, hm, hs⟩
    exact ⟨L, (selfDual_iff W L).2 hL, hx, hs, W', ι, (ofKind_iff _ _ _ _).2 hk, hi, hr, hm⟩

omit [NumberField E] [StarRing E] in

theorem forall_step_iff (P Q : ℕ) (C : E → ℕ → ℕ → Prop) :
    (∀ (β : E) (P' Q' : ℕ), SelfDualLatticeComplements.Step β P Q P' Q' → C β P' Q') ↔
      (1 ≤ P → C 1 (P - 1) Q) ∧ (1 ≤ Q → C (-1) P (Q - 1)) := by
  constructor
  · intro h
    exact ⟨fun hP => h _ _ _ (Or.inl ⟨rfl, hP, rfl, rfl⟩),
      fun hQ => h _ _ _ (Or.inr ⟨rfl, hQ, rfl, rfl⟩)⟩
  · rintro ⟨h1, h2⟩ β P' Q' (⟨rfl, hP, rfl, rfl⟩ | ⟨rfl, hQ, rfl, rfl⟩)
    · exact h1 hP
    · exact h2 hQ

theorem conclusion_iff (W : HSpace E) (M P Q : ℕ) :
    ((1 ≤ P → ∃ x : W.V, W.hD x x = 1 ∧ UnitVectorOrthogonal.HasComplement W x (M - 1) (P - 1) Q) ∧
      (1 ≤ Q → ∃ x : W.V, W.hD x x = -1 ∧ UnitVectorOrthogonal.HasComplement W x (M - 1) P (Q - 1))) ↔
    ∀ (β : E) (P' Q' : ℕ), SelfDualLatticeComplements.Step β P Q P' Q' →
      ∃ x : W.V, W.hD x x = β ∧ SelfDualLatticeComplements.HasComplement W x (M - 1) P' Q' := by
  rw [forall_step_iff P Q
    (fun β P' Q' => ∃ x : W.V, W.hD x x = β ∧ SelfDualLatticeComplements.HasComplement W x (M - 1) P' Q')]
  simp only [hasComplement_iff]

theorem conclusionAll_iff (W : HSpace E) (M P Q : ℕ) :
    ((1 ≤ P → (∃ x : W.V, W.hD x x = 1) ∧
        ∀ x : W.V, W.hD x x = 1 → UnitVectorOrthogonal.HasComplement W x (M - 1) (P - 1) Q) ∧
      (1 ≤ Q → (∃ x : W.V, W.hD x x = -1) ∧
        ∀ x : W.V, W.hD x x = -1 → UnitVectorOrthogonal.HasComplement W x (M - 1) P (Q - 1))) ↔
    ∀ (β : E) (P' Q' : ℕ), SelfDualLatticeComplements.Step β P Q P' Q' →
      (∃ x : W.V, W.hD x x = β) ∧
        ∀ x : W.V, W.hD x x = β → SelfDualLatticeComplements.HasComplement W x (M - 1) P' Q' := by
  rw [forall_step_iff P Q
    (fun β P' Q' => (∃ x : W.V, W.hD x x = β) ∧
        ∀ x : W.V, W.hD x x = β → SelfDualLatticeComplements.HasComplement W x (M - 1) P' Q')]
  simp only [hasComplement_iff]

theorem over_iff : UnitVectorOrthogonal.UnitVectorPerpOver E ↔ SelfDualLatticeComplements.ExistsPerpOver E := by
  refine forall_congr' fun W => forall_congr' fun M => forall_congr' fun P =>
    forall_congr' fun Q => imp_congr (ofKind_iff W M P Q) (imp_congr Iff.rfl ?_)
  exact conclusion_iff W M P Q

theorem overAll_iff : UnitVectorOrthogonal.UnitVectorPerpEveryOver E ↔ SelfDualLatticeComplements.ForallPerpOver E := by
  refine forall_congr' fun W => forall_congr' fun M => forall_congr' fun P =>
    forall_congr' fun Q => imp_congr (ofKind_iff W M P Q) (imp_congr Iff.rfl ?_)
  exact conclusionAll_iff W M P Q

end General

theorem unitVectorPerp_iff (D : D7) : UnitVectorOrthogonal.UnitVectorPerp D ↔ SelfDualLatticeComplements.UnitVectorPerp D :=
  @over_iff D.host.E _ _ D.host.cmStar

theorem unitVectorPerpAll_iff (D : D7) :
    UnitVectorOrthogonal.UnitVectorPerpEvery D ↔ SelfDualLatticeComplements.UnitVectorPerpAll D :=
  @overAll_iff D.host.E _ _ D.host.cmStar

end GlobalTheory.UnitVectorPerpCompare

end
end

