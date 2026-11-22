import Mathlib

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaSuppBc
section
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.mem_support_baseChange :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
      (Q : PrimeSpectrum B), Q ∈ Module.support B (TensorProduct R B M) ↔
        PrimeSpectrum.comap (algebraMap R B) Q ∈ Module.support R M := by
  intro R B _ _ _ M _ _ _ Q
  let p := PrimeSpectrum.comap (algebraMap R B) Q
  let φ := Ideal.ResidueField.mapₐ p.asIdeal Q.asIdeal (Algebra.ofId R B) rfl
  letI : Algebra p.asIdeal.ResidueField Q.asIdeal.ResidueField := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R p.asIdeal.ResidueField Q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R B Q.asIdeal.ResidueField
      Q.asIdeal.ResidueField M).nontrivial_congr,
    ← (TensorProduct.AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField
      Q.asIdeal.ResidueField Q.asIdeal.ResidueField M).nontrivial_congr]
  exact Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right _ _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CardEqPowLength
section
open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.simple_module_equiv_residue_field {A X : Type} [CommRing A] [IsLocalRing A] [AddCommGroup X] [Module A X] [IsSimpleModule A X] : Nonempty (X ≃ ResidueField A) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp (inferInstance : IsSimpleModule A X)
  have : I = maximalIdeal A := IsLocalRing.eq_maximalIdeal hI
  subst this
  exact ⟨e.toEquiv⟩

private theorem UpperTheory.V.AlgebraTools.card_finite_length_module {A : Type} [CommRing A] [IsLocalRing A] [Finite (ResidueField A)] {X : Type} [AddCommGroup X] [Module A X] (h : IsFiniteLength A X) :
    Finite X ∧ Nat.card X = Nat.card (ResidueField A) ^ (Module.length A X).toNat := by
  induction h with
  | @of_subsingleton M _ _ _ =>
    refine ⟨Finite.of_subsingleton, ?_⟩
    rw [Module.length_eq_zero]
    simp [Nat.card_eq_one_iff_unique]
  | @of_simple_quotient M _ _ N _ hN ih =>
    obtain ⟨hfin, hcard⟩ := ih
    obtain ⟨e⟩ := UpperTheory.V.AlgebraTools.simple_module_equiv_residue_field (A := A) (X := M ⧸ N)
    have hq : Nat.card (M ⧸ N) = Nat.card (ResidueField A) := Nat.card_congr e
    have hNt : Module.length A N ≠ ⊤ := Module.length_ne_top_iff.mpr hN
    have hlen : Module.length A M = Module.length A N + 1 := by
      rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), Module.length_eq_one A (M ⧸ N)]
    have hc : Nat.card M = Nat.card (M ⧸ N) * Nat.card N :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup
    have hq0 : Nat.card (ResidueField A) ≠ 0 := Nat.card_pos.ne'
    have hM : Nat.card M = Nat.card (ResidueField A) ^ ((Module.length A N).toNat + 1) := by
      rw [hc, hq, hcard, pow_succ, mul_comm]
    refine ⟨Nat.finite_of_card_ne_zero (by rw [hM]; exact pow_ne_zero _ hq0), ?_⟩
    rw [hM, hlen, ENat.toNat_add hNt ENat.one_ne_top]
    simp

theorem UpperTheory.V.AlgebraTools.card_eq_pow_length :
    ∀ {A X : Type} [CommRing A] [IsLocalRing A] [Finite (ResidueField A)] [AddCommGroup X] [Module A X], (Finite X ↔ Module.length A X ≠ ⊤) ∧ (Finite X → Nat.card X = Nat.card (ResidueField A) ^ (Module.length A X).toNat) := by
  intro A X _ _ _ _ _
  have key : Finite X → Module.length A X ≠ ⊤ := fun h => by
    haveI := h
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, isArtinian_of_finite⟩)
  refine ⟨⟨key, fun h => (UpperTheory.V.AlgebraTools.card_finite_length_module (Module.length_ne_top_iff.mp h)).1⟩, fun h => ?_⟩
  exact (UpperTheory.V.AlgebraTools.card_finite_length_module (Module.length_ne_top_iff.mp (key h))).2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CoiConjSingle
section
open Polynomial Matrix IsLocalRing TensorProduct

private theorem UpperTheory.V.AlgebraTools.exists_unit_entry {R : Type} [CommRing R] [IsLocalRing R] {ι : Type}
    [Fintype ι] [DecidableEq ι] (e : Matrix ι ι R) (he : IsIdempotentElem e) (h0 : e ≠ 0) :
    ∃ a b, IsUnit (e a b) := by
  classical
  by_contra h
  push_neg at h
  have hm : ∀ a b, e a b ∈ maximalIdeal R := fun a b => (mem_maximalIdeal _).2 (h a b)
  have hmap : (1 - e).map (residue R) = 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp [(residue_eq_zero_iff _).2 (hm a a)]
    · simp [Matrix.one_apply_ne hab, (residue_eq_zero_iff _).2 (hm a b)]
  have hdet : IsUnit (1 - e).det := by
    have h1 : residue R (1 - e).det = 1 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, det_one]
    exact (isUnit_map_iff (residue R) _).1 (h1 ▸ isUnit_one)
  have hu : IsUnit (1 - e) := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  apply h0
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
  exact hu.mul_right_eq_zero.1 h2

theorem UpperTheory.V.AlgebraTools.coi_conj_single :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → Matrix ι ι R), CompleteOrthogonalIdempotents f → (∀ i, f i ≠ 0) → ∃ g : GL ι R, ∀ i, (g : Matrix ι ι R) * f i * ((g⁻¹ : GL ι R) : Matrix ι ι R) = single i i 1 := by
  intro R _ _ ι _ _ f hf h0
  classical
  have hc : ∀ i, ∃ a b, IsUnit (f i a b) := fun i =>
    UpperTheory.V.AlgebraTools.exists_unit_entry (f i) (hf.idem i) (h0 i)
  choose a b hu using hc
  set P : Matrix ι ι R := Matrix.of fun k j => f j k (b j) with hP
  set Q : Matrix ι ι R := Matrix.of fun i k => ((hu i).unit⁻¹ : Rˣ) * f i (a i) k with hQ
  have hent : ∀ (M : Matrix ι ι R) (j k : ι),
      (Q * M * P) j k = ((hu j).unit⁻¹ : Rˣ) * (f j * M * f k) (a j) (b k) := by
    intro M j k
    simp only [hP, hQ, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  have hidem : ∀ i, f i * f i = f i := fun i => (hf.idem i).eq
  have hort : ∀ i j, i ≠ j → f i * f j = 0 := fun i j hij => hf.ortho hij
  have hQP : Q * P = 1 := by
    ext j k
    have h1 := hent 1 j k
    simp only [Matrix.mul_one] at h1
    rw [h1]
    by_cases hjk : j = k
    · subst hjk
      rw [hidem, Matrix.one_apply_eq, IsUnit.val_inv_mul]
    · rw [hort j k hjk, Matrix.one_apply_ne hjk, Matrix.zero_apply, mul_zero]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  refine ⟨⟨Q, P, hQP, hPQ⟩, fun i => ?_⟩
  change Q * f i * P = single i i 1
  ext j k
  rw [hent, Matrix.single_apply]
  by_cases hji : i = j
  · subst hji
    by_cases hik : i = k
    · subst hik
      rw [hidem, hidem, IsUnit.val_inv_mul, if_pos ⟨rfl, rfl⟩]
    · rw [hidem, hort i k hik, Matrix.zero_apply, mul_zero, if_neg (fun h => hik h.2)]
  · rw [hort j i (Ne.symm hji), zero_mul, Matrix.zero_apply, mul_zero, if_neg (fun h => hji h.1)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ComapPowLe
section
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.comap_pow_le :
    ∀ {A M M' : Type} [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] [Module.Finite A M'] (I : Ideal A) (f : M →ₗ[A] M'), ∃ c : ℕ, ∀ m : ℕ, (I ^ (m + c) • (⊤ : Submodule A M')).comap f ≤ LinearMap.ker f ⊔ I ^ m • (⊤ : Submodule A M) := by
  intro A M M' _ _ _ _ _ _ _ I f
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
  refine ⟨k, fun m x hx => ?_⟩
  have h1 : f x ∈ I ^ (m + k) • (⊤ : Submodule A M') ⊓ LinearMap.range f :=
    ⟨hx, LinearMap.mem_range_self f x⟩
  rw [hk (m + k) (Nat.le_add_left k m), Nat.add_sub_cancel] at h1
  have h2 : f x ∈ I ^ m • LinearMap.range f :=
    Submodule.smul_mono le_rfl inf_le_right h1
  rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at h2
  have h3 : x ∈ ((I ^ m • (⊤ : Submodule A M)).map f).comap f := h2
  rw [Submodule.comap_map_eq, sup_comm] at h3
  exact h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CotInd
section
open IsLocalRing

namespace UpperTheory.V.AlgebraTools

structure CotInd (R : Type) [CommRing R] [IsLocalRing R] {κ : Type} [Fintype κ] (x : κ → R) : Prop where
  mem : ∀ k, x k ∈ maximalIdeal R
  indep : ∀ a : κ → R, ∑ k, a k * x k ∈ maximalIdeal R ^ 2 → ∀ k, a k ∈ maximalIdeal R

theorem cotInd_iff (R : Type) [CommRing R] [IsLocalRing R] {κ : Type} [Fintype κ] (x : κ → R) :
    CotInd R x ↔ ∃ h : ∀ k, x k ∈ maximalIdeal R,
      LinearIndependent (ResidueField R)
        (fun k => ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R)) := by
  have key : ∀ (h : ∀ k, x k ∈ maximalIdeal R) (a : κ → R),
      (∑ k, residue R (a k) • ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R) = 0) ↔
        ∑ k, a k * x k ∈ maximalIdeal R ^ 2 := by
    intro h a
    have h1 : ∑ k, residue R (a k) • ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R)
        = (maximalIdeal R).toCotangent (∑ k, a k • (⟨x k, h k⟩ : maximalIdeal R)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul]
      exact algebraMap_smul (ResidueField R) (a k) _
    rw [h1, Ideal.toCotangent_eq_zero]
    simp
  constructor
  · rintro ⟨h, hi⟩
    refine ⟨h, Fintype.linearIndependent_iff.2 fun g hg k => ?_⟩
    choose a ha using fun k => residue_surjective (g k)
    rw [← ha k, residue_eq_zero_iff]
    refine hi a ((key h a).1 ?_) k
    simpa [ha] using hg
  · rintro ⟨h, hi⟩
    refine ⟨h, fun a ha k => ?_⟩
    have := Fintype.linearIndependent_iff.1 hi (fun k => residue R (a k)) ((key h a).2 ha) k
    exact (residue_eq_zero_iff _).1 this

theorem CotInd.comp {R : Type} [CommRing R] [IsLocalRing R] {κ ι : Type} [Fintype κ] [Fintype ι]
    {x : κ → R} (h : CotInd R x) (e : ι → κ) (he : Function.Injective e) : CotInd R (x ∘ e) := by
  obtain ⟨h1, h2⟩ := (cotInd_iff R x).1 h
  exact (cotInd_iff R _).2 ⟨fun i => h1 (e i), h2.comp e he⟩

end UpperTheory.V.AlgebraTools
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DensityProd
section
open Polynomial Matrix IsLocalRing TensorProduct

private theorem sum_matrix_single_diag_one_eq_one {F : Type} [Field F] {n : Type} [Fintype n] [DecidableEq n] :
    ∑ i : n, Matrix.single i i (1 : F) = 1 := by
  ext u v
  by_cases h : u = v
  · subst h
    simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
  · simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, h]
    have he : (Finset.univ.filter fun w : n => w = u ∧ w = v) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro w - ⟨rfl, rfl⟩
      exact h rfl
    rw [he]
    simp

private theorem intertwiner_of_ker {F : Type} [Field F] {σ : Type} (d : σ → Type)
    [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)]
    (S : Subalgebra F (∀ s, Matrix (d s) (d s) F)) (s t : σ)
    (ht : ∀ B : Matrix (d t) (d t) F, ∃ x ∈ S, x t = B)
    (hk : ∀ x ∈ S, x t = 0 → x s = 0) :
    ∃ V : Matrix (d s) (d t) F, V ≠ 0 ∧ ∀ x ∈ S, x s * V = V * x t := by
  have key : ∀ x ∈ S, ∀ y ∈ S, x t = y t → x s = y s := by
    intro x hx y hy h
    have := hk (x - y) (S.sub_mem hx hy) (by rw [Pi.sub_apply, h, sub_self])
    rw [Pi.sub_apply, sub_eq_zero] at this
    exact this
  obtain ⟨i0⟩ := (inferInstance : Nonempty (d t))
  choose xx hxS hxt using fun j => ht (Matrix.single j i0 (1 : F))
  choose z hzS hzt using fun j => ht (Matrix.single i0 j (1 : F))
  have hne : xx i0 s ≠ 0 := by
    intro h0
    have hx0 : ∀ j, xx j s = 0 := by
      intro j
      have := key (xx j * xx i0) (S.mul_mem (hxS j) (hxS i0)) (xx j) (hxS j)
        (by rw [Pi.mul_apply, hxt, hxt, Matrix.single_mul_single_same, one_mul])
      rw [← this, Pi.mul_apply, h0, mul_zero]
    have h1 := key (∑ j, xx j * z j) (Subalgebra.sum_mem _ fun j _ => S.mul_mem (hxS j) (hzS j)) 1 S.one_mem
      (by
        rw [Finset.sum_apply]
        simp only [Pi.mul_apply, hxt, hzt, Matrix.single_mul_single_same, one_mul, Pi.one_apply]
        exact sum_matrix_single_diag_one_eq_one)
    rw [Finset.sum_apply] at h1
    simp only [Pi.mul_apply, hx0, zero_mul, Finset.sum_const_zero, Pi.one_apply] at h1
    exact zero_ne_one h1
  obtain ⟨a, b, hab⟩ : ∃ a b, xx i0 s a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (Matrix.ext h)
  refine ⟨Matrix.of fun u j => xx j s u b, ?_, ?_⟩
  · intro hV
    apply hab
    have := congrFun (congrFun hV a) i0
    simpa using this
  · intro x hx
    ext u k
    have e := key (x * xx k) (S.mul_mem hx (hxS k)) (∑ j, x t j k • xx j)
      (Subalgebra.sum_mem _ fun j _ => S.smul_mem (hxS j) _) (by
        rw [Pi.mul_apply, hxt, Finset.sum_apply]
        simp only [Pi.smul_apply, hxt]
        ext p q
        by_cases hq : i0 = q <;> simp [Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply, hq])
    have e2 := congrFun (congrFun e u) b
    simp only [Pi.mul_apply, Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply] at e2
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [e2]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem separate {F : Type} [Field F] {σ : Type} (d : σ → Type)
    [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)]
    (S : Subalgebra F (∀ s, Matrix (d s) (d s) F)) (s t : σ)
    (hs : ∀ B : Matrix (d s) (d s) F, ∃ x ∈ S, x s = B)
    (hk : ∃ x ∈ S, x t = 0 ∧ x s ≠ 0) : ∃ x ∈ S, x t = 0 ∧ x s = 1 := by
  obtain ⟨x, hxS, hxt, hxs⟩ := hk
  obtain ⟨a, b, hab⟩ : ∃ a b, x s a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hxs (Matrix.ext h)
  choose p hpS hps using fun i => hs (Matrix.single i a (x s a b)⁻¹)
  choose q hqS hqs using fun i => hs (Matrix.single b i (1 : F))
  refine ⟨∑ i, p i * x * q i, ?_, ?_, ?_⟩
  · exact Subalgebra.sum_mem _ fun i _ => S.mul_mem (S.mul_mem (hpS i) hxS) (hqS i)
  · rw [Finset.sum_apply]
    simp [Pi.mul_apply, hxt]
  · rw [Finset.sum_apply]
    simp only [Pi.mul_apply, hps, hqs, Matrix.single_mul_mul_single, inv_mul_cancel₀ hab, one_mul]
    ext u v
    by_cases h : u = v
    · subst h
      simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
    · simp [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, h]
      have he : (Finset.univ.filter fun w : d s => w = u ∧ w = v) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro w - ⟨rfl, rfl⟩
        exact h rfl
      rw [he]
      simp

theorem UpperTheory.V.AlgebraTools.density_prod :
    ∀ {F Γ : Type} [Field F] [Monoid Γ] {σ : Type} [Fintype σ] [DecidableEq σ] (d : σ → Type) [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)] (ρ : ∀ s, Γ →* Matrix (d s) (d s) F), (∀ s, Submodule.span F (Set.range (ρ s)) = ⊤) → (∀ s t, s ≠ t → ∀ V : Matrix (d s) (d t) F, (∀ g, ρ s g * V = V * ρ t g) → V = 0) → Submodule.span F (Set.range fun g => (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F)) = ⊤ := by
  intro F Γ _ _ σ _ _ d _ _ _ ρ hspan hint
  let φ : Γ →* ((s : σ) → Matrix (d s) (d s) F) :=
    { toFun := fun g s => ρ s g
      map_one' := funext fun s => map_one (ρ s)
      map_mul' := fun g h => funext fun s => map_mul (ρ s) g h }
  obtain ⟨S, hSdef⟩ : ∃ S : Subalgebra F ((s : σ) → Matrix (d s) (d s) F),
      S = Algebra.adjoin F (Set.range fun g => (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F)) := ⟨_, rfl⟩
  have hmem : ∀ g, (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F) ∈ S := by
    intro g
    rw [hSdef]
    exact Algebra.subset_adjoin ⟨g, rfl⟩
  have hsurj : ∀ s (B : Matrix (d s) (d s) F), ∃ x ∈ S, x s = B := by
    intro s B
    have hB : B ∈ Submodule.span F (Set.range (ρ s)) := by
      rw [hspan s]
      exact Submodule.mem_top
    induction hB using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      exact ⟨_, hmem g, rfl⟩
    | zero => exact ⟨0, S.zero_mem, rfl⟩
    | add y z _ _ hy hz =>
      obtain ⟨x1, h1, e1⟩ := hy
      obtain ⟨x2, h2, e2⟩ := hz
      exact ⟨x1 + x2, S.add_mem h1 h2, by rw [Pi.add_apply, e1, e2]⟩
    | smul c y _ hy =>
      obtain ⟨x1, h1, e1⟩ := hy
      exact ⟨c • x1, S.smul_mem h1 c, by rw [Pi.smul_apply, e1]⟩
  have hsep : ∀ s t, s ≠ t → ∃ x ∈ S, x t = 0 ∧ x s = 1 := by
    intro s t hst
    apply separate d S s t (hsurj s)
    by_contra hno
    push_neg at hno
    obtain ⟨V, hV0, hV⟩ := intertwiner_of_ker d S s t (hsurj t) hno
    exact hV0 (hint s t hst V fun g => hV _ (hmem g))
  have he : ∀ s, ∃ e ∈ S, e s = 1 ∧ ∀ t, t ≠ s → e t = 0 := by
    intro s
    have hT : ∀ T : Finset σ, s ∉ T → ∃ e ∈ S, e s = 1 ∧ ∀ t ∈ T, e t = 0 := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        intro _
        exact ⟨1, S.one_mem, rfl, by simp⟩
      | @insert t T htT ih =>
        intro hs
        rw [Finset.mem_insert, not_or] at hs
        obtain ⟨e, heS, hes, het⟩ := ih hs.2
        obtain ⟨y, hyS, hyt, hys⟩ := hsep s t hs.1
        refine ⟨e * y, S.mul_mem heS hyS, by rw [Pi.mul_apply, hes, hys, one_mul], ?_⟩
        intro u hu
        rw [Finset.mem_insert] at hu
        rcases hu with rfl | hu
        · rw [Pi.mul_apply, hyt, mul_zero]
        · rw [Pi.mul_apply, het u hu, zero_mul]
    obtain ⟨e, heS, hes, het⟩ := hT (Finset.univ.erase s) (by simp)
    exact ⟨e, heS, hes, fun t ht => het t (by simp [ht])⟩
  have htop : S = ⊤ := by
    rw [eq_top_iff]
    intro Y _
    choose e heS hes het using he
    choose zz hzS hzs using fun s => hsurj s (Y s)
    have hY : Y = ∑ s, zz s * e s := by
      funext u
      rw [Finset.sum_apply, Finset.sum_eq_single u]
      · rw [Pi.mul_apply, hzs, hes, mul_one]
      · intro b _ hb
        rw [Pi.mul_apply, het b u hb.symm, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ u) h
    rw [hY]
    exact Subalgebra.sum_mem _ fun s _ => S.mul_mem (hzS s) (heS s)
  have h2 : Submodule.span F (Set.range fun g => (fun s => ρ s g : ∀ s, Matrix (d s) (d s) F)) =
      Subalgebra.toSubmodule S := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact hmem g
    · rw [hSdef, Algebra.adjoin_eq_span, Submodule.span_le]
      intro x hx
      have hx' : x ∈ MonoidHom.mrange φ :=
        (Submonoid.closure_le.mpr (by rintro _ ⟨g, rfl⟩; exact MonoidHom.mem_mrange.mpr ⟨g, rfl⟩)) hx
      obtain ⟨g, rfl⟩ := MonoidHom.mem_mrange.mp hx'
      exact Submodule.subset_span ⟨g, rfl⟩
  rw [h2, htop]
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DerInner
section
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.der_inner :
    ∀ {K E : Type} [CommRing K] [Ring E] [Algebra K E] {σ : Type} [Fintype σ] [DecidableEq σ] (d : σ → Type) [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)] (j : (∀ s, Matrix (d s) (d s) K) →ₐ[K] E) (D : (∀ s, Matrix (d s) (d s) K) →ₗ[K] E), (∀ x y, D (x * y) = D x * j y + j x * D y) → ∃ Y : E, ∀ x, D x = Y * j x - j x * Y := by
  intro K E _ _ _ σ _ _ d _ _ _ j D hD
  let i0 : ∀ s, d s := fun s => Classical.arbitrary (d s)
  let u : ∀ s, d s → d s → (∀ s, Matrix (d s) (d s) K) :=
    fun s p q => Pi.single s (Matrix.single p q (1 : K))
  have hsame : ∀ s (p q r w : d s), u s p q * u s r w = if q = r then u s p w else 0 := by
    intro s p q r w
    simp only [u, ← Pi.single_mul]
    split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, one_mul]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, Pi.single_zero]
  have hne : ∀ s t (p q : d s) (r w : d t), s ≠ t → u s p q * u t r w = 0 := by
    intro s t p q r w h
    funext x
    simp only [u, Pi.mul_apply, Pi.zero_apply]
    by_cases hx : x = s
    · subst hx
      rw [Pi.single_eq_of_ne h, mul_zero]
    · rw [Pi.single_eq_of_ne hx, zero_mul]
  have hone : ∑ s, ∑ k, u s k k = 1 := by
    funext x
    rw [Finset.sum_apply, Finset.sum_eq_single x]
    · rw [Finset.sum_apply]
      ext a b
      simp only [u, Pi.single_eq_same, Matrix.sum_apply, Matrix.single_apply, Pi.one_apply,
        Matrix.one_apply]
      by_cases hab : a = b
      · subst hab
        simp
      · rw [Finset.sum_eq_zero fun k _ => if_neg fun h => hab (h.1.symm.trans h.2)]
        simp [hab]
    · intro s _ hs
      rw [Finset.sum_apply]
      exact Finset.sum_eq_zero fun k _ => Pi.single_eq_of_ne (Ne.symm hs) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  let a : E := ∑ s, ∑ k, j (u s k (i0 s)) * D (u s (i0 s) k)
  have key : ∀ t (p q : d t), D (u t p q) = j (u t p q) * a - a * j (u t p q) := by
    intro t p q
    have h1 : j (u t p q) * a = j (u t p (i0 t)) * D (u t (i0 t) q) := by
      simp only [a, Finset.mul_sum, ← mul_assoc, ← map_mul]
      rw [Finset.sum_eq_single t]
      · rw [Finset.sum_eq_single q]
        · rw [hsame, if_pos rfl]
        · intro k _ hk
          rw [hsame, if_neg (Ne.symm hk), map_zero, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · intro s _ hs
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hne t s _ _ _ _ (Ne.symm hs), map_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hS1 : ∑ s, ∑ k, j (u s k (i0 s)) * D (u s (i0 s) k * u t p q)
        = j (u t p (i0 t)) * D (u t (i0 t) q) := by
      rw [Finset.sum_eq_single t]
      · rw [Finset.sum_eq_single p]
        · rw [hsame, if_pos rfl]
        · intro k _ hk
          rw [hsame, if_neg hk, map_zero, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
      · intro s _ hs
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hne s t _ _ _ _ hs, map_zero, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hS2 : ∑ s, ∑ k, j (u s k (i0 s)) * j (u s (i0 s) k) = 1 := by
      simp only [← map_mul, hsame, eq_self_iff_true, if_true]
      simp only [← map_sum]
      rw [hone, map_one]
    have e : a * j (u t p q) = ∑ s, ∑ k, (j (u s k (i0 s)) * D (u s (i0 s) k * u t p q)
        - j (u s k (i0 s)) * j (u s (i0 s) k) * D (u t p q)) := by
      simp only [a, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
      rw [hD]
      noncomm_ring
    rw [h1, e]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, hS1, hS2, one_mul]
    abel
  refine ⟨-a, fun x => ?_⟩
  have hlin : D = (LinearMap.mulRight K a).comp j.toLinearMap
      - (LinearMap.mulLeft K a).comp j.toLinearMap := by
    refine (Pi.basis fun s => Matrix.stdBasis K (d s) (d s)).ext fun ji => ?_
    obtain ⟨t, p, q⟩ := ji
    rw [Pi.basis_apply, Matrix.stdBasis_eq_single]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
      LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]
    exact key t p q
  have hx := LinearMap.congr_fun hlin x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
    LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply] at hx
  rw [hx]
  noncomm_ring
end

