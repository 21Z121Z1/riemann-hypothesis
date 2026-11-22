import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationFamilyCotangentBasis
section
open IsLocalRing

namespace GlobalTheory.CoordsAlg

noncomputable def cotFun {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A)
    (f : I →ₗ[R] R) (hf : ∀ x : I, (x : A) ∈ I ^ 2 → f x = 0) : Module.Dual R I.Cotangent :=
  ((I • ⊤ : Submodule A I).restrictScalars R).liftQ f (fun x hx => by
      refine LinearMap.mem_ker.mpr (hf x ?_)
      rw [← Ideal.toCotangent_eq_zero]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hx) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R (I • ⊤ : Submodule A I)).symm.toLinearMap

theorem cotFun_toCotangent {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A)
    (f : I →ₗ[R] R) (hf : ∀ x : I, (x : A) ∈ I ^ 2 → f x = 0) (x : I) :
    cotFun I f hf (I.toCotangent x) = f x := rfl

theorem coords_of_derivation_basis : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra R A] (e : A →+* R), (∀ r, e (algebraMap R A r) = r) → Module.Free R (RingHom.ker e).Cotangent → Module.Finite R (RingHom.ker e).Cotangent → ∀ (n : ℕ) (dv : Fin n → A → R), (∀ a x y, dv a (x + y) = dv a x + dv a y) → (∀ a x y, dv a (x * y) = e x * dv a y + e y * dv a x) → (∀ a r, dv a (algebraMap R A r) = 0) → (∀ D : A → R, (∀ x y, D (x + y) = D x + D y) → (∀ x y, D (x * y) = e x * D y + e y * D x) → (∀ r, D (algebraMap R A r) = 0) → ∃! c : Fin n → R, ∀ x, D x = ∑ a, c a * dv a x) → ∃ z : Fin n → A, (∀ i, e (z i) = 0) ∧ (∀ a i, dv a (z i) = if a = i then 1 else 0) ∧ maximalIdeal A = (maximalIdeal R).map (algebraMap R A) ⊔ Ideal.span (Set.range z) := by
  intro R A _ _ _ _ _ _ e he hfree hfin n dv hadd hmul halg huniq
  set I := RingHom.ker e with hIdef
  let dH : Fin n → A →+ R := fun a => AddMonoidHom.mk' (dv a) (hadd a)
  have hdH : ∀ a x, dv a x = dH a x := fun _ _ => rfl
  have hsmul : ∀ a r x, dv a (algebraMap R A r * x) = r * dv a x := by
    intro a r x; rw [hmul, he, halg]; ring
  have hI2 : ∀ a x, x ∈ I ^ 2 → dv a x = 0 := by
    intro a x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro u hu v hv
      rw [hmul, (RingHom.mem_ker).1 hu, (RingHom.mem_ker).1 hv]; ring
    · intro u v hu hv; rw [hadd, hu, hv, add_zero]
  have hdec : ∀ x : A, x - algebraMap R A (e x) ∈ I := fun x => by
    simp [I, RingHom.mem_ker, he]
  let fa : Fin n → (I →ₗ[R] R) := fun a =>
    { toFun := fun x => dv a x
      map_add' := fun x y => hadd a x y
      map_smul' := fun r x => by
        simp only [Submodule.coe_smul_of_tower, Algebra.smul_def, RingHom.id_apply, smul_eq_mul]
        exact hsmul a r x }
  let ℓ : Fin n → Module.Dual R I.Cotangent := fun a => cotFun I (fa a) (fun x hx => hI2 a x hx)
  have hℓ : ∀ a (x : I), ℓ a (I.toCotangent x) = dv a x := fun _ _ => rfl
  let Ψ : (Fin n → R) →ₗ[R] Module.Dual R I.Cotangent :=
    ∑ a, (LinearMap.proj a : (Fin n → R) →ₗ[R] R).smulRight (ℓ a)
  have hΨ : ∀ c (x : I), Ψ c (I.toCotangent x) = ∑ a, c a * dv a x := by
    intro c x
    simp [Ψ, LinearMap.sum_apply, hℓ]

  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h0 : ∀ x : A, ∑ a, c a * dv a x = 0 := by
      intro x
      have hx := hΨ c ⟨_, hdec x⟩
      rw [hc] at hx
      have : ∀ a, dv a (x - algebraMap R A (e x)) = dv a x := by
        intro a; rw [hdH, map_sub, ← hdH, ← hdH, halg, sub_zero]
      simp only [this] at hx
      exact hx.symm
    obtain ⟨c0, -, hc0⟩ := huniq (fun _ => 0) (fun _ _ => by simp) (fun _ _ => by simp)
      (fun _ => rfl)
    have h1 : c = c0 := hc0 c (fun x => (h0 x).symm)
    have h2 : (0 : Fin n → R) = c0 := hc0 0 (fun x => by simp)
    rw [h1, ← h2]
  have hΨsurj : Function.Surjective Ψ := by
    intro φ
    let D : A → R := fun x => φ (I.toCotangent ⟨_, hdec x⟩)
    have Dadd : ∀ x y, D (x + y) = D x + D y := by
      intro x y
      simp only [D, ← map_add]
      congr 2
      ext; simp; ring
    have Dalg : ∀ r, D (algebraMap R A r) = 0 := by
      intro r
      simp only [D]
      have : (⟨_, hdec (algebraMap R A r)⟩ : I) = 0 := by ext; simp [he]
      rw [this, map_zero, map_zero]
    have Dmul : ∀ x y, D (x * y) = e x * D y + e y * D x := by
      intro x y
      have hsq : (x - algebraMap R A (e x)) * (y - algebraMap R A (e y)) ∈ I ^ 2 := by
        rw [pow_two]; exact Ideal.mul_mem_mul (hdec x) (hdec y)
      have key : (⟨_, hdec (x * y)⟩ : I) = e x • (⟨_, hdec y⟩ : I) + e y • (⟨_, hdec x⟩ : I) +
          ⟨_, Ideal.pow_le_self two_ne_zero hsq⟩ := by
        ext
        simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, Algebra.smul_def, map_mul]
        ring
      have hw0 : I.toCotangent ⟨(x - algebraMap R A (e x)) * (y - algebraMap R A (e y)),
          Ideal.pow_le_self two_ne_zero hsq⟩ = 0 := (I.toCotangent_eq_zero _).2 hsq
      simp only [D]
      rw [key]
      simp only [map_add, LinearMap.map_smul_of_tower, hw0,
        map_zero, add_zero, map_smul, smul_eq_mul]
    obtain ⟨c, hc, -⟩ := huniq D Dadd Dmul Dalg
    refine ⟨c, ?_⟩
    ext w
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective w
    rw [hΨ, ← hc]
    simp only [D]
    congr 2
    ext
    simp [(RingHom.mem_ker).1 x.2]
  let Ψe : (Fin n → R) ≃ₗ[R] Module.Dual R I.Cotangent :=
    LinearEquiv.ofBijective Ψ ⟨hΨinj, hΨsurj⟩
  have hΨsingle : ∀ a, Ψ (Pi.single a 1) = ℓ a := by
    intro a
    ext w
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective w
    rw [hΨ, hℓ]
    simp [Pi.single_apply]
  let w : Fin n → I.Cotangent := fun i =>
    (Module.evalEquiv R I.Cotangent).symm
      ((LinearMap.proj i : (Fin n → R) →ₗ[R] R) ∘ₗ Ψe.symm.toLinearMap)
  have hw : ∀ a i, ℓ a (w i) = if a = i then 1 else 0 := by
    intro a i
    simp only [w, Module.apply_evalEquiv_symm_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.proj_apply]
    have : Ψe.symm (ℓ a) = Pi.single a 1 := by
      rw [LinearEquiv.symm_apply_eq]; exact (hΨsingle a).symm
    rw [this]
    by_cases h : a = i
    · subst h; simp
    · simp [h, Pi.single_apply, Ne.symm h]
  choose y hy using fun i => I.toCotangent_surjective (w i)
  have hzI : ∀ i, (y i : A) ∈ I := fun i => (y i).2
  have hdz : ∀ a i, dv a (y i : A) = if a = i then 1 else 0 := by
    intro a i; rw [← hℓ, hy, hw]
  have hImax : I ≤ maximalIdeal A := by
    intro x hx
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map e
    rw [(RingHom.mem_ker).1 hx] at this
    exact not_isUnit_zero this
  have hnak : I ≤ Ideal.span (Set.range fun i => (y i : A)) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal A)
      (IsNoetherian.noetherian I) ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · intro x hx
      set s := ∑ a, algebraMap R A (dv a x) * (y a : A) with hs
      have hsI : s ∈ Ideal.span (Set.range fun i => (y i : A)) :=
        Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a, rfl⟩)
      have hsI' : s ∈ I := Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hzI a)
      have hr : x - s ∈ I := I.sub_mem hx hsI'
      have hdr : ∀ b, dv b (x - s) = 0 := by
        intro b
        rw [hdH, map_sub, hs, map_sum]
        simp only [← hdH, hsmul, hdz]
        simp
      have hcot : I.toCotangent ⟨x - s, hr⟩ = 0 := by
        refine (Module.forall_dual_apply_eq_zero_iff R _).1 fun φ => ?_
        obtain ⟨c, rfl⟩ := hΨsurj φ
        rw [hΨ]; simp [hdr]
      have hsq : x - s ∈ I ^ 2 := (I.toCotangent_eq_zero _).1 hcot
      have hxs : x = s + (x - s) := by ring
      rw [hxs]
      refine Submodule.add_mem_sup hsI ?_
      rw [pow_two] at hsq
      exact Submodule.smul_mono_left hImax hsq
  refine ⟨fun i => (y i : A), fun i => (RingHom.mem_ker).1 (y i).2, hdz, ?_⟩
  have hmapR : (maximalIdeal R).map (algebraMap R A) ≤ maximalIdeal A := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map e
    rw [he] at this
    exact (mem_maximalIdeal r).1 hr this
  apply le_antisymm
  · intro x hx
    have hex : e x ∈ maximalIdeal R := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h1 : algebraMap R A (e x) ∈ maximalIdeal A := by
        have := (maximalIdeal A).sub_mem hx (hImax (hdec x))
        simpa using this
      exact (mem_maximalIdeal _).1 h1 (hu.map _)
    have hxe : x = algebraMap R A (e x) + (x - algebraMap R A (e x)) := by ring
    rw [hxe]
    exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ hex) (hnak (hdec x))
  · refine sup_le hmapR ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hImax (hzI i)

end GlobalTheory.CoordsAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockChangeOfBasisViaTwoFamiliesImplicit
section
namespace GlobalTheory.Div.BlockChangeDet

open Matrix

theorem det_blockDiagonal'_eq_prod {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
    {κ : ι → Type} [∀ c, Fintype (κ c)] [∀ c, DecidableEq (κ c)]
    (M : ∀ c, Matrix (κ c) (κ c) R) :
    (Matrix.blockDiagonal' M).det = ∏ c, (M c).det := by
  classical
  set f := Fintype.equivFin ι
  let b : (Σ c, κ c) → Fin (Fintype.card ι) := fun p => f p.1
  have hb : (Matrix.blockDiagonal' M).BlockTriangular b := by
    rintro ⟨c, i⟩ ⟨c', j⟩ h
    exact Matrix.blockDiagonal'_apply_ne M i j (fun hc => by subst hc; exact lt_irrefl _ h)
  rw [hb.det_fintype]
  symm
  refine Fintype.prod_equiv f _ _ (fun c => ?_)
  let e : κ c ≃ {p : (Σ c, κ c) // b p = f c} :=
    { toFun := fun i => ⟨⟨c, i⟩, rfl⟩
      invFun := fun p => cast (congrArg κ (f.injective p.2)) p.1.2
      left_inv := fun i => rfl
      right_inv := by
        rintro ⟨⟨c', i⟩, h⟩
        have hc : c' = c := f.injective h
        subst hc
        rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext i j
  exact (Matrix.blockDiagonal'_apply_eq M c i j).symm

theorem det_block_change (F : Type) [Field F] {N : Type} [AddCommGroup N] [Module F N]
    {κ : Type} [Fintype κ]
    (m : κ → ℕ) {n : ℕ} (e : (Σ b, Fin (m b)) ≃ Fin n) (ℓ : (Σ b, Fin (m b)) → N)
    (hℓ : ∀ x : N, ∃! a : (Σ b, Fin (m b)) → F, x = ∑ k, a k • ℓ k) (nu mu : Fin n → N)
    (U A : Matrix (Fin n) (Fin n) F) (C : (Σ b, Fin (m b)) → Fin n → F)
    (g : ∀ b, Matrix (Fin (m b)) (Fin (m b)) F)
    (hU : ∀ σ, ℓ σ = ∑ k, U (e σ) k • nu k) (hA : ∀ k, mu k = ∑ l, A k l • nu l)
    (hg : ∀ b i, ∑ j, g b i j • ℓ ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k) :
    U.det ≠ 0 ∧ (∏ b, (g b).det) * U.det = (Matrix.of fun i k => C (e.symm i) k).det * A.det := by
  classical

  have hli : LinearIndependent F ℓ := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have h0 : (0 : N) = ∑ k, (0 : (Σ b, Fin (m b)) → F) k • ℓ k := by simp
    have := (hℓ 0).unique ha.symm h0
    intro i
    exact congrFun this i
  have hsp : ⊤ ≤ Submodule.span F (Set.range ℓ) := by
    intro x _
    obtain ⟨a, ha, -⟩ := hℓ x
    rw [ha]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  have hfr : Module.finrank F N = n := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Fintype.card_congr e, Fintype.card_fin]
  have hspnu : ⊤ ≤ Submodule.span F (Set.range nu) := by
    refine le_trans hsp (Submodule.span_le.mpr ?_)
    rintro _ ⟨σ, rfl⟩
    rw [hU σ]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  have hlinu : LinearIndependent F nu :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspnu (by simp [hfr])
  have uniq : ∀ a c : Fin n → F, ∑ k, a k • nu k = ∑ k, c k • nu k → a = c := by
    intro a c h
    have := Fintype.linearIndependent_iff.mp hlinu (a - c)
      (by simp [sub_smul, Finset.sum_sub_distrib, h])
    funext k
    exact sub_eq_zero.mp (this k)

  have hdet : U.det ≠ 0 := by
    have hrows : LinearIndependent F (fun i => U i) := by
      rw [Fintype.linearIndependent_iff]
      intro a ha
      have hli' : LinearIndependent F (ℓ ∘ e.symm) := hli.comp e.symm e.symm.injective
      refine Fintype.linearIndependent_iff.mp hli' a ?_
      have hcol : ∀ k, ∑ i, a i * U i k = 0 := by
        intro k
        have := congrFun ha k
        simpa [Finset.sum_apply] using this
      calc ∑ i, a i • (ℓ ∘ e.symm) i
          = ∑ i, a i • ∑ k, U i k • nu k := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            simp [Function.comp, hU]
        _ = ∑ k, (∑ i, a i * U i k) • nu k := by
            simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
            exact Finset.sum_comm
        _ = 0 := by simp [hcol]
    have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
    exact (Matrix.isUnit_iff_isUnit_det U |>.mp hu).ne_zero
  refine ⟨hdet, ?_⟩

  have hent : ∀ σ k, ∑ τ, blockDiagonal' g σ τ * U (e τ) k = ∑ l, C σ l * A l k := by
    rintro ⟨b, i⟩
    have h1 : ∑ τ, blockDiagonal' g ⟨b, i⟩ τ • ℓ τ = ∑ j, g b i j • ℓ ⟨b, j⟩ := by
      rw [Fintype.sum_sigma]
      rw [Finset.sum_eq_single b]
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [blockDiagonal'_apply_eq]
      · intro b' _ hb'
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [blockDiagonal'_apply_ne g i j (Ne.symm hb'), zero_smul]
      · intro h; exact absurd (Finset.mem_univ b) h
    have h2 : ∑ k, (∑ τ, blockDiagonal' g ⟨b, i⟩ τ * U (e τ) k) • nu k
        = ∑ τ, blockDiagonal' g ⟨b, i⟩ τ • ℓ τ := by
      simp only [hU, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have h3 : ∑ k, (∑ l, C ⟨b, i⟩ l * A l k) • nu k = ∑ l, C ⟨b, i⟩ l • mu l := by
      simp only [hA, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have := uniq (fun k => ∑ τ, blockDiagonal' g ⟨b, i⟩ τ * U (e τ) k)
      (fun k => ∑ l, C ⟨b, i⟩ l * A l k) (by rw [h2, h1, hg b i, ← h3])
    intro k
    exact congrFun this k
  have key : Matrix.reindex e e (blockDiagonal' g) * U
      = (Matrix.of fun i k => C (e.symm i) k) * A := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
    rw [← hent (e.symm i) k]
    exact Fintype.sum_equiv e.symm _ _ (fun x => by simp)
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self, det_blockDiagonal'_eq_prod] at this
  exact this

theorem det_block_change' : ∀ {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N] {κ : Type} [Fintype κ]
    (m : κ → ℕ) {n : ℕ} (e : (Σ b, Fin (m b)) ≃ Fin n) (ℓ : (Σ b, Fin (m b)) → N),
    (∀ x : N, ∃! a : (Σ b, Fin (m b)) → F, x = ∑ k, a k • ℓ k) → ∀ (nu mu : Fin n → N)
    (U A : Matrix (Fin n) (Fin n) F) (C : (Σ b, Fin (m b)) → Fin n → F)
    (g : ∀ b, Matrix (Fin (m b)) (Fin (m b)) F),
    (∀ σ, ℓ σ = ∑ k, U (e σ) k • nu k) → (∀ k, mu k = ∑ l, A k l • nu l) →
    (∀ b i, ∑ j, g b i j • ℓ ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k) →
    U.det ≠ 0 ∧ (∏ b, (g b).det) * U.det = (Matrix.of fun i k => C (e.symm i) k).det * A.det := by
  intro F _ N _ _ κ _ m n e ℓ hℓ nu mu U A C g hU hA hg
  exact det_block_change F m e ℓ hℓ nu mu U A C g hU hA hg

end GlobalTheory.Div.BlockChangeDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMulExpand
section
namespace GlobalTheory.DeterminantProductExpansion

theorem det_mul_expand {R : Type} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R) (B : Matrix (Fin N) (Fin i) R) :
    Matrix.det (A * B) = ∑ f : Fin i → Fin N, (∏ a : Fin i, A a (f a)) * Matrix.det (Matrix.submatrix B f id) := by
  let g : Fin i → Fin N → (Fin i → R) := fun a k => A a k • (fun j => B k j)
  have hrow : (A * B : Matrix (Fin i) (Fin i) R) = Matrix.of (fun a => ∑ k : Fin N, g a k) := by
    ext a j
    simp [g, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : Matrix.det (A * B) =
      (Matrix.detRowAlternating : (Fin i → R) [⋀^Fin i]→ₗ[R] R).toMultilinearMap (fun a => ∑ k : Fin N, g a k) := by
    rw [hrow]; rfl
  rw [h1, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  simp only [g]
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

theorem main : ∀ {R : Type} [inst : CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R) (B : Matrix (Fin N) (Fin i) R), Matrix.det (A * B) = ∑ f : Fin i → Fin N, (∏ a : Fin i, A a (f a)) * Matrix.det (Matrix.submatrix B f id) :=
  fun A B => det_mul_expand A B

end GlobalTheory.DeterminantProductExpansion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMulExpandAlt
section
namespace GlobalTheory.DeterminantExpansion

theorem det_mul_expand {V : Type} [inst : CommRing V] {m g : ℕ}
    (M : Matrix (Fin m) (Fin g) V) (C : Matrix (Fin g) (Fin m) V) :
    Matrix.det (M * C) =
      ∑ J : Fin m → Fin g, (∏ i : Fin m, M i (J i)) * Matrix.det (Matrix.submatrix C J id) := by
  classical
  have h : (M * C : Matrix (Fin m) (Fin m) V) = fun i => ∑ k : Fin g, M i k • C k := by
    ext i j
    simp [Matrix.mul_apply, Finset.sum_apply]
  let f : MultilinearMap V (fun _ : Fin m => Fin m → V) V :=
    (Matrix.detRowAlternating : (Fin m → V) [⋀^Fin m]→ₗ[V] V).toMultilinearMap
  have hf : ∀ A : Matrix (Fin m) (Fin m) V, Matrix.det A = f A := fun A => rfl
  rw [hf, h, f.map_sum (fun i k => M i k • C k)]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [f.map_smul_univ (fun i => M i (J i)) (fun i => C (J i)), hf, smul_eq_mul]
  rfl

end GlobalTheory.DeterminantExpansion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNearOneMatrixNormBounds
section
open Matrix Polynomial

namespace GlobalTheory

theorem norm_multiset_prod_near_one (s : Multiset ℂ) (hs : ∀ μ ∈ s, ‖μ - 1‖ ≤ 1 / 2) :
    (1 / 2 : ℝ) ^ Multiset.card s ≤ ‖s.prod‖ ∧ ‖s.prod‖ ≤ (3 / 2 : ℝ) ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self a s)
    obtain ⟨h1, h2⟩ := ih (fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ))
    have hlo : (1 / 2 : ℝ) ≤ ‖a‖ := by
      have := norm_sub_norm_le (1 : ℂ) (1 - a)
      rw [norm_one, sub_sub_cancel, norm_sub_rev] at this
      linarith
    have hhi : ‖a‖ ≤ 3 / 2 := by
      have := norm_add_le (a - 1) 1
      rw [sub_add_cancel, norm_one] at this
      linarith
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ, pow_succ]
    constructor
    · rw [mul_comm ((1 / 2 : ℝ) ^ _)]
      exact mul_le_mul hlo h1 (by positivity) (norm_nonneg _)
    · rw [mul_comm ((3 / 2 : ℝ) ^ _)]
      exact mul_le_mul hhi h2 (norm_nonneg _) (by norm_num)

theorem det_near_one_bounds (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ)
    (hA : ∀ i j, ‖A i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ ε) (hn : (n : ℝ) * ε ≤ 1 / 2) :
    (1 / 2 : ℝ) ^ n ≤ ‖A.det‖ ∧ ‖A.det‖ ≤ 2 ^ n := by
  have hroot : ∀ μ ∈ A.charpoly.roots, ‖μ - 1‖ ≤ 1 / 2 := by
    intro μ hμ
    have hr : A.charpoly.IsRoot μ := isRoot_of_mem_roots hμ
    have hev : Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']; exact hr
    obtain ⟨k, hk⟩ := eigenvalue_mem_ball hev
    rw [Metric.mem_closedBall, dist_eq_norm] at hk
    have hdiag : ‖A k k - 1‖ ≤ ε := by simpa using hA k k
    have h1n : 1 ≤ n := Fin.pos k
    have hoff : ∑ j ∈ Finset.univ.erase k, ‖A k j‖ ≤ ((n : ℝ) - 1) * ε := by
      have hle : ∀ j ∈ Finset.univ.erase k, ‖A k j‖ ≤ ε := by
        intro j hj
        have hjk : k ≠ j := (Finset.ne_of_mem_erase hj).symm
        simpa [Matrix.one_apply_ne hjk] using hA k j
      calc _ ≤ ∑ _j ∈ Finset.univ.erase k, ε := Finset.sum_le_sum hle
        _ = ((n : ℝ) - 1) * ε := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub h1n, Nat.cast_one]
    calc ‖μ - 1‖ = ‖(μ - A k k) + (A k k - 1)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖μ - A k k‖ + ‖A k k - 1‖ := norm_add_le _ _
      _ ≤ ((n : ℝ) - 1) * ε + ε := add_le_add (hk.trans hoff) hdiag
      _ = n * ε := by ring
      _ ≤ 1 / 2 := hn
  have hcard : Multiset.card A.charpoly.roots = n := by
    rw [(splits_iff_card_roots).mp (IsAlgClosed.splits _), Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  obtain ⟨h1, h2⟩ := norm_multiset_prod_near_one _ hroot
  rw [hcard, ← Matrix.det_eq_prod_roots_charpoly] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) n

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagKey
section
namespace GlobalTheory.DiagonalKeyIdentity

open Matrix

theorem diag_key {A : Type} [CommRing A] {q : ℕ} (a b : Fin q → A)
    (h : ∀ i, a i + b i + a i * b i = 0) :
    diagonal a + diagonal b + diagonal a * diagonal b = (0 : Matrix (Fin q) (Fin q) A) := by
  rw [diagonal_mul_diagonal, diagonal_add, diagonal_add, ← diagonal_zero]
  congr 1
  funext i
  exact h i

theorem main : ∀ {A : Type} [inst : CommRing A] {n q : ℕ} (J : Matrix (Fin n) (Fin n) A) (X Xc Y Yc : Matrix (Fin n) (Fin q) A) (a b : Fin q → A), Matrix.transpose X * J * Xc = (0 : Matrix (Fin q) (Fin q) A) → Matrix.transpose X * J * Yc = (1 : Matrix (Fin q) (Fin q) A) → Matrix.transpose Y * J * Xc = (1 : Matrix (Fin q) (Fin q) A) → Matrix.transpose Y * J * Yc = (0 : Matrix (Fin q) (Fin q) A) → (∀ (i : Fin q), a i + b i + a i * b i = (0 : A)) → ((1 : Matrix (Fin n) (Fin n) A) + J * Yc * Matrix.diagonal a * Matrix.transpose X + J * Xc * Matrix.diagonal b * Matrix.transpose Y) * J * ((1 : Matrix (Fin n) (Fin n) A) + Xc * Matrix.diagonal a * (Matrix.transpose Y * J) + Yc * Matrix.diagonal b * (Matrix.transpose X * J)) = J := by
  intro A _ n q J X Xc Y Yc a b h1 h2 h3 h4 hab
  have k1 := diag_key a b hab
  have k2 : diagonal b + diagonal a + diagonal b * diagonal a = (0 : Matrix (Fin q) (Fin q) A) := by
    apply diag_key b a; intro i; rw [add_comm (b i), mul_comm (b i)]; exact hab i
  have g1 : ∀ {m : ℕ} (Z : Matrix (Fin q) (Fin m) A), Xᵀ * (J * (Xc * Z)) = 0 := by
    intro m Z; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.zero_mul]
  have g2 : ∀ {m : ℕ} (Z : Matrix (Fin q) (Fin m) A), Xᵀ * (J * (Yc * Z)) = Z := by
    intro m Z; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have g3 : ∀ {m : ℕ} (Z : Matrix (Fin q) (Fin m) A), Yᵀ * (J * (Xc * Z)) = Z := by
    intro m Z; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h3, Matrix.one_mul]
  have g4 : ∀ {m : ℕ} (Z : Matrix (Fin q) (Fin m) A), Yᵀ * (J * (Yc * Z)) = 0 := by
    intro m Z; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h4, Matrix.zero_mul]
  calc _ = J + J * (Xc * ((diagonal b + diagonal a + diagonal b * diagonal a) * (Yᵀ * J)))
        + J * (Yc * ((diagonal a + diagonal b + diagonal a * diagonal b) * (Xᵀ * J))) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_one,
            Matrix.one_mul, g1, g2, g3, g4, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
          abel
    _ = J := by rw [k1, k2]; simp

end GlobalTheory.DiagonalKeyIdentity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagMulOfLower
section
namespace GlobalTheory.DiagonalTimesLowerTriangular

theorem diag_mul_of_lower {K : Type} [CommRing K] {s : ℕ} {a b : Matrix (Fin s) (Fin s) K}
    (ha : ∀ (i j : Fin s), i < j → a i j = (0 : K))
    (hb : ∀ (i j : Fin s), i < j → b i j = (0 : K)) :
    ∀ (i : Fin s), (a * b) i i = a i i * b i i := by
  intro i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i ?_ ?_
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hb k i h, mul_zero]
    · rw [ha i k h, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem main : ∀ {K : Type} [inst : CommRing K] {s : ℕ} {a b : Matrix (Fin s) (Fin s) K}, (∀ (i j : Fin s), i < j → a i j = (0 : K)) → (∀ (i j : Fin s), i < j → b i j = (0 : K)) → ∀ (i : Fin s), (a * b) i i = a i i * b i i :=
  fun ha hb => diag_mul_of_lower ha hb

end GlobalTheory.DiagonalTimesLowerTriangular
end

