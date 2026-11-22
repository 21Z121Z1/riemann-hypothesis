import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStabilizerIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumRegroupFibreBijStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_eq_finsum_finsum_of_fibre_bij : ∀ {α ι : Type} {κ : ι → Type} (U : α → ℂ) (W : (i : ι) → κ i → ℂ) (π : α → ι) (Φ : (i : ι) → α → κ i), (Function.support U).Finite → (∀ a, U a ≠ 0 → W (π a) (Φ (π a) a) = U a) → (∀ a a', U a ≠ 0 → U a' ≠ 0 → π a' = π a → Φ (π a) a = Φ (π a) a' → a = a') → (∀ i c, W i c ≠ 0 → ∃ a, π a = i ∧ U a ≠ 0 ∧ Φ i a = c) → ∑ᶠ a, U a = ∑ᶠ i, ∑ᶠ c, W i c := by
  first | (exact @GlobalTheory.finsum_regroup_fibre_bij) | (exact GlobalTheory.finsum_regroup_fibre_bij) | (intros; apply GlobalTheory.finsum_regroup_fibre_bij  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumRestrictedProductCountStatement
section
open Filter
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_restricted_product_count : ∀ (I R : Type) (D : I → Type) (S : Set I) (B : ∀ i, D i → ℂ) (ℓ : R → ∀ i, D i) (A : Set R) (k m : ℕ), (∀ i, Nonempty (D i)) → (∀ i ∈ S, (Function.support (B i)).Finite) → (∀ᶠ i in cofinite, ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0) → (∀ c ∈ A, ∀ᶠ i in cofinite, B i (ℓ c i) = 1) → (∀ e : ∀ i, D i, (∀ i ∈ S, B i (e i) ≠ 0) → Nat.card {c : R // c ∈ A ∧ ∀ i ∈ S, ℓ c i = e i} * 2 ^ k = 2 ^ m) → (∑ᶠ c : R, if c ∈ A then ∏ᶠ i ∈ S, B i (ℓ c i) else 0) * (2 : ℂ) ^ k = (2 : ℂ) ^ m * ∏ᶠ i ∈ S, ∑ᶠ d, B i d := by
  first | exact @GlobalTheory.finsum_finprod_mul_two_pow_eq | exact GlobalTheory.finsum_finprod_mul_two_pow_eq | (intros; apply GlobalTheory.finsum_finprod_mul_two_pow_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumStabilizerWeightedPairOrbitsConjClass
section
open scoped Classical

namespace GlobalTheory.MassConj

theorem exists_out_mk_eq_smul {H α : Type} [Group H] [MulAction H α] (a : α) :
    ∃ g : H, Quotient.out (Quotient.mk (MulAction.orbitRel H α) a :
      MulAction.orbitRel.Quotient H α) = g • a := by
  have h := Quotient.mk_out (s := MulAction.orbitRel H α) a
  change MulAction.orbitRel H α _ _ at h
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  exact ⟨g, hg.symm⟩

theorem finsum_pairOrbit_fibre (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G)
    (Φ : Γ → X → ℂ)
    (hΦ : ∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) (γ₀ : Γ) :
    ∑ᶠ O : {O : MulAction.orbitRel.Quotient Γ (ConjPair Γ X) //
        ConjClasses.mk (Quotient.out O).elt = ConjClasses.mk γ₀},
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out O.1)) : ℂ)) *
          Φ (Quotient.out O.1).elt (Quotient.out O.1).pt =
      ∑ᶠ b : MulAction.orbitRel.Quotient (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ γ₀ (Quotient.out b) := by
  set C : Subgroup G := Γ ⊓ Subgroup.centralizer {(γ₀ : G)} with hC
  have memC : ∀ δ : Γ, δ * γ₀ = γ₀ * δ → (δ : G) ∈ C := by
    intro δ h
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    refine ⟨δ.2, ?_⟩
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have := congrArg (fun z : Γ => (z : G)) h
    simpa using this.symm
  have commC : ∀ c : C, (⟨c, c.2.1⟩ : Γ) * γ₀ = γ₀ * ⟨c, c.2.1⟩ := by
    intro c
    have h2 := (Subgroup.mem_inf.mp c.2).2
    rw [Subgroup.mem_centralizer_iff] at h2
    have h := h2 γ₀ (Set.mem_singleton _)
    ext
    simp [h]
  let f : MulAction.orbitRel.Quotient C X →
      {O : MulAction.orbitRel.Quotient Γ (ConjPair Γ X) //
        ConjClasses.mk (Quotient.out O).elt = ConjClasses.mk γ₀} :=
    fun b => ⟨Quotient.mk _ ⟨γ₀, Quotient.out b⟩, by
      obtain ⟨δ, hδ⟩ := exists_out_mk_eq_smul (H := Γ) (ConjPair.mk γ₀ (Quotient.out b))
      rw [hδ, smul_elt, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
      exact ⟨δ⁻¹, by group⟩⟩
  have inj : Function.Injective f := by
    intro b b' hbb
    have h1 := congrArg Subtype.val hbb
    simp only [f] at h1
    have h2 := Quotient.exact h1
    change MulAction.orbitRel Γ _ _ _ at h2
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h2
    obtain ⟨δ, hδ⟩ := h2
    have he := congrArg ConjPair.elt hδ
    have hp := congrArg ConjPair.pt hδ
    simp only [smul_elt, smul_pt] at he hp
    have hcomm : δ * γ₀ = γ₀ * δ := by
      calc δ * γ₀ = δ * γ₀ * δ⁻¹ * δ := by group
        _ = γ₀ * δ := by rw [he]
    rw [← Quotient.out_eq b, ← Quotient.out_eq b']
    apply Quotient.sound
    change MulAction.orbitRel C X _ _
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨⟨δ, memC δ hcomm⟩, hp⟩
  have surj : Function.Surjective f := by
    rintro ⟨O, hO⟩
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at hO
    obtain ⟨δ, hδ⟩ := hO
    obtain ⟨c, hc⟩ := exists_out_mk_eq_smul (H := C) (δ • (Quotient.out O).pt)
    refine ⟨Quotient.mk _ (δ • (Quotient.out O).pt), ?_⟩
    apply Subtype.ext
    simp only [f]
    conv_rhs => rw [← Quotient.out_eq O]
    apply Quotient.sound
    change MulAction.orbitRel Γ _ _ _
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨(⟨c, c.2.1⟩ : Γ) * δ, ?_⟩
    rw [hc, mul_smul]
    ext
    · simp only [smul_elt]
      rw [hδ, commC c]
      group
    · simp only [smul_pt]
      rfl
  have term : ∀ b : MulAction.orbitRel.Quotient C X,
      (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out (f b).1)) : ℂ)) *
          Φ (Quotient.out (f b).1).elt (Quotient.out (f b).1).pt =
        (1 / (Nat.card (MulAction.stabilizer C (Quotient.out b)) : ℂ)) * Φ γ₀ (Quotient.out b) := by
    intro b
    obtain ⟨δ, hδ⟩ := exists_out_mk_eq_smul (H := Γ) (ConjPair.mk γ₀ (Quotient.out b))
    have hfb : (f b).1 = Quotient.mk _ (ConjPair.mk γ₀ (Quotient.out b)) := rfl
    rw [hfb, hδ, smul_elt, smul_pt]
    have hcard1 : Nat.card (MulAction.stabilizer Γ (δ • ConjPair.mk γ₀ (Quotient.out b))) =
        Nat.card (MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b))) :=
      Nat.card_congr (MulAction.stabilizerEquivStabilizer rfl).toEquiv.symm
    have h_to : ∀ s : MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X),
        ((s : Γ) : G) ∈ C := fun s =>
      memC s.1 ((GlobalTheory.MassConj.mem_stabilizer_iff _ _).mp s.2).1
    have h_to' : ∀ s : MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X),
        (⟨((s : Γ) : G), h_to s⟩ : C) ∈ MulAction.stabilizer C (Quotient.out b) := by
      intro s
      rw [MulAction.mem_stabilizer_iff]
      exact ((GlobalTheory.MassConj.mem_stabilizer_iff _ _).mp s.2).2
    have h_inv : ∀ t : MulAction.stabilizer C (Quotient.out b),
        (⟨((t : C) : G), (t : C).2.1⟩ : Γ) ∈
          MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X) := by
      intro t
      rw [GlobalTheory.MassConj.mem_stabilizer_iff]
      exact ⟨commC t.1, MulAction.mem_stabilizer_iff.mp t.2⟩
    have hcard2 : Nat.card (MulAction.stabilizer Γ (ConjPair.mk γ₀ (Quotient.out b) : ConjPair Γ X)) =
        Nat.card (MulAction.stabilizer C (Quotient.out b)) :=
      Nat.card_congr
        { toFun := fun s => ⟨⟨((s : Γ) : G), h_to s⟩, h_to' s⟩
          invFun := fun t => ⟨⟨((t : C) : G), (t : C).2.1⟩, h_inv t⟩
          left_inv := fun s => rfl
          right_inv := fun t => rfl }
    have hphi : Φ (δ * γ₀ * δ⁻¹) (δ • Quotient.out b) = Φ γ₀ (Quotient.out b) :=
      hΦ δ γ₀ (Quotient.out b)
    rw [hcard1, hcard2, hphi]
  refine (finsum_comp_equiv (Equiv.ofBijective f ⟨inj, surj⟩)).symm.trans ?_
  exact finsum_congr term

end GlobalTheory.MassConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiveElementaryInequalitiesEventuallyStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_rpow_log_inequalities : ∀ eps : ℝ, 0 < eps → eps < 1 → ∀ᶠ x : ℝ in Filter.atTop, x ^ (eps / 4) + x ^ (eps / 3) + 1 + 3 * Real.log x ≤ x ^ eps / 5 ∧ 11 ≤ x ^ (eps / 5) ∧ 8 * Real.log x ^ 2 < x ^ 2 ∧ 2 * x ^ (eps / 5 + eps / 100) ≤ Real.sqrt (x * x ^ (-(eps / 8))) ∧ 44 ≤ Real.sqrt (x * x ^ (-(eps / 8))) := by
  first | exact @GlobalTheory.five_elementary_inequalities_eventually | exact GlobalTheory.five_elementary_inequalities_eventually | (intros; apply GlobalTheory.five_elementary_inequalities_eventually <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitsFinitelyManyNormsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_units_finitely_many_norms : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) →
    ∃ S : Finset L, ∀ ε : Lˣ, IsIntegral ℤ (ε : L) → IsIntegral ℤ ((ε⁻¹ : Lˣ) : L) → c ε = ε →
      ∃ f ∈ S, ∃ η : Lˣ, IsIntegral ℤ (η : L) ∧ IsIntegral ℤ ((η⁻¹ : Lˣ) : L) ∧ (ε : L) = f * ((η : L) * c η) := by
  first | exact @GlobalTheory.units_fixed_eq_mul_mul_conj | exact GlobalTheory.units_fixed_eq_mul_mul_conj | (intros; apply GlobalTheory.units_fixed_eq_mul_mul_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedVectorsIrreducibleSubrepDecompositionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_vectors_irreducible_subrep_decomposition : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Set G) (F : Submodule ℂ V), (∀ v, v ∈ F ↔ ∀ k ∈ K, ρ k v = v) → ∀ 𝒜 : Set (Submodule ℂ V), (∀ P ∈ 𝒜, P ≠ ⊥ ∧ (∀ g, ∀ v ∈ P, ρ g v ∈ P) ∧ ∀ W : Submodule ℂ V, W ≤ P → (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = P) → FiniteDimensional ℂ ((⨆ P ∈ 𝒜, P ⊓ F : Submodule ℂ V)) → ∃ (ι : Type) (_ : Fintype ι) (π : ι → Submodule ℂ V), (∀ i, π i ∈ 𝒜 ∧ π i ⊓ F ≠ ⊥) ∧ iSupIndep (fun i => π i ⊓ F) ∧ (⨆ i, π i ⊓ F) = (⨆ P ∈ 𝒜, P ⊓ F) ∧ ∀ P ∈ 𝒜, P ⊓ F ≠ ⊥ → ∃ i, ∃ T : V →ₗ[ℂ] V, (∀ v ∈ P, T v ∈ π i) ∧ (∀ v ∈ P, T v = 0 → v = 0) ∧ ∀ g, ∀ v ∈ P, T (ρ g v) = ρ g (T v) := by
  first | exact @GlobalTheory.AbsDec.fixed_decomposition | exact GlobalTheory.AbsDec.fixed_decomposition | (intros; apply GlobalTheory.AbsDec.fixed_decomposition <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLocalRingPointedEtaleNeighbourhood
section
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem EtNbhd.flat_B : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R), Module.Flat R i.B := by
  intro R _ _ i
  haveI : Module.Flat i.A i.B := IsLocalization.flat i.B i.q.primeCompl
  exact Module.Flat.trans R i.A i.B

end GlobalTheory.Henselisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLocalizationMembership
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_localization_membership : ∀ (B D : Type) [CommRing B] [CommRing D] [Algebra B D] [Module.Flat B D] (Q : Ideal D) [Q.IsPrime] (f b : B), algebraMap B (Localization.AtPrime Q) b ∈ Ideal.span {algebraMap B (Localization.AtPrime Q) f} → ∃ s : B, s ∉ Q.comap (algebraMap B D) ∧ s * b ∈ Ideal.span {f} := by
  first | (exact @GlobalTheory.localFlat_dvd_descends) | (exact GlobalTheory.localFlat_dvd_descends) | (intros; apply GlobalTheory.localFlat_dvd_descends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfForallFinsetSubsetFlatStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_forall_finset_subset_flat_submodule : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], (∀ s : Finset M, ∃ N : Submodule R M, (↑s : Set M) ⊆ ↑N ∧ Module.Flat R ↥N) → Module.Flat R M := by
  first | exact @GlobalTheory.flat_of_forall_finset_subset_flat | exact GlobalTheory.flat_of_forall_finset_subset_flat | (intros; apply GlobalTheory.flat_of_forall_finset_subset_flat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatQuotientSmulTopOfSurjectiveFlatStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_quotient_smul_top_of_surjective_flat : ∀ (P R₁ B B₁ : Type) [CommRing P] [CommRing R₁] [CommRing B] [CommRing B₁] [Algebra P B] (f₁ : P →+* R₁) (a₁ : R₁ →+* B₁) (c₁ : B →+* B₁), Function.Surjective f₁ → Function.Surjective c₁ → c₁.comp (algebraMap P B) = a₁.comp f₁ → RingHom.ker c₁ = (RingHom.ker f₁).map (algebraMap P B) → a₁.Flat → Module.Flat (P ⧸ RingHom.ker f₁) (B ⧸ (RingHom.ker f₁ • ⊤ : Submodule P B)) := by
  first | exact @GlobalTheory.flat_quot_smul_top_of_surj_flat | exact GlobalTheory.flat_quot_smul_top_of_surj_flat | (intros; apply GlobalTheory.flat_quot_smul_top_of_surj_flat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSubschemeOfQuotientFlatAffineStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_subscheme_of_quotient_flat_affine : ∀ (V : Type) [CommRing V] (X : Scheme.{0}) [IsAffine X] (p : X ⟶ Spec (CommRingCat.of V)) (J : X.IdealSheafData), ((Ideal.Quotient.mk (J.ideal ⟨⊤, isAffineOpen_top X⟩)).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).Flat → Flat (J.subschemeι ≫ p) := by
  first | (exact @GlobalTheory.closedSub_flat_of_quotient_flat) | (exact GlobalTheory.closedSub_flat_of_quotient_flat) | (intros; apply GlobalTheory.closedSub_flat_of_quotient_flat  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormMulTransposeMulFormInvMem
section
noncomputable section

open Matrix

namespace GlobalTheory.ZarhinFam

def quat (d : ℕ) : Matrix (Fin 4) (Fin 4) ℤ :=
  Classical.choose (GlobalTheory.exists_int_matrix_transpose_mul_eq_smul_one (d - 1))

theorem quat_transpose_mul (d : ℕ) :
    (quat d)ᵀ * quat d = ((d - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) :=
  (Classical.choose_spec (GlobalTheory.exists_int_matrix_transpose_mul_eq_smul_one (d - 1))).1

theorem quat_mul_transpose (d : ℕ) :
    quat d * (quat d)ᵀ = ((d - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) :=
  (Classical.choose_spec (GlobalTheory.exists_int_matrix_transpose_mul_eq_smul_one (d - 1))).2

def form (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  fromBlocks 1 (quat d)ᵀ (quat d) ((d : ℤ) • 1)

def formInv (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  fromBlocks ((d : ℤ) • 1) (-(quat d)ᵀ) (-(quat d)) 1

theorem form_transpose (d : ℕ) : (form d)ᵀ = form d := by
  simp [form, fromBlocks_transpose]

theorem form_mul_formInv {d : ℕ} (hd : 0 < d) : form d * formInv d = 1 := by
  have h1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [form, formInv, fromBlocks_multiply, ← fromBlocks_one]
  congr 1
  · rw [Matrix.mul_neg, quat_transpose_mul, h1]; simp [sub_smul]
  · simp
  · simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_neg, smul_neg, add_neg_cancel]
  · rw [Matrix.mul_neg, quat_mul_transpose, h1]; simp [sub_smul]

theorem formInv_mul_form {d : ℕ} (hd : 0 < d) : formInv d * form d = 1 :=
  mul_eq_one_comm.mp (form_mul_formInv hd)

def ord (d : ℕ) : Subring (Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) where
  carrier := {N | ∀ i j, (d : ℤ) ∣ N (Sum.inr i) (Sum.inl j)}
  mul_mem' {N N'} hN hN' i j := by
    simp only [Set.mem_setOf_eq] at hN hN'
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    exact dvd_add (Finset.dvd_sum fun k _ => (hN i k).mul_right _)
      (Finset.dvd_sum fun k _ => (hN' k j).mul_left _)
  one_mem' i j := by simp
  add_mem' {N N'} hN hN' i j := by
    simp only [Set.mem_setOf_eq] at hN hN'
    exact dvd_add (hN i j) (hN' i j)
  zero_mem' i j := by simp
  neg_mem' {N} hN i j := by
    simp only [Set.mem_setOf_eq] at hN
    simpa using hN i j

theorem mem_ord {d : ℕ} {N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ} :
    N ∈ ord d ↔ ∀ i j, (d : ℤ) ∣ N (Sum.inr i) (Sum.inl j) := Iff.rfl

theorem form_mul_transpose_mul_formInv_mem {d : ℕ} {N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ}
    (hN : N ∈ ord d) : form d * Nᵀ * formInv d ∈ ord d := by
  intro i j
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have key : ∀ i j, ((N (Sum.inr i) (Sum.inl j) : ℤ) : ZMod d) = 0 := fun i j =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hN i j)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, form, formInv, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, transpose_apply, Int.cast_add, Int.cast_sum, Int.cast_mul,
    Matrix.smul_apply, Matrix.neg_apply, Int.cast_neg, smul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul,
    mul_zero, key, Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul]
  simp

def barM (d : ℕ) (N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  form d * Nᵀ * formInv d

def bar (d : ℕ) (N : ord d) : ord d := ⟨barM d N, form_mul_transpose_mul_formInv_mem N.2⟩

@[simp] theorem bar_coe (d : ℕ) (N : ord d) :
    ((bar d N : ord d) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) =
      form d * (N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ)ᵀ * formInv d :=
  rfl

theorem bar_add (d : ℕ) (a b : ord d) : bar d (a + b) = bar d a + bar d b := by
  ext1
  simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem formInv_transpose (d : ℕ) : (formInv d)ᵀ = formInv d := by
  simp [formInv, fromBlocks_transpose]

theorem bar_bar {d : ℕ} (hd : 0 < d) (a : ord d) : bar d (bar d a) = a := by
  ext1
  simp only [bar_coe, Matrix.transpose_mul, Matrix.transpose_transpose, form_transpose, formInv_transpose]
  calc form d * (formInv d * ((a : Matrix _ _ ℤ) * form d)) * formInv d
      = (form d * formInv d) * (a : Matrix _ _ ℤ) * (form d * formInv d) := by simp only [Matrix.mul_assoc]
    _ = (a : Matrix _ _ ℤ) := by rw [form_mul_formInv hd, Matrix.one_mul, Matrix.mul_one]

def idem (d : ℕ) : ord d :=
  ⟨single (Sum.inl 0) (Sum.inl 0) 1, fun i j => by simp [single]⟩

theorem idem_mul_self (d : ℕ) : idem d * idem d = idem d := by
  ext1
  simp [idem]

end GlobalTheory.ZarhinFam
end
end

