import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrDualb
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_dualb :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Ideal C) (κ : Type) [Fintype κ] (ε : κ → C), maximalIdeal C * K = ⊥ → K = Ideal.span (Set.range ε) → (∀ c : κ → O, ∑ u, c u • ε u = 0 → ∀ u, c u ∈ maximalIdeal O) → ∃ co : κ → K →ₗ[O] ResidueField O, ∀ y : K, ∃ a : κ → O, (∀ u, residue O (a u) = co u y) ∧ (y : C) = ∑ u, a u • ε u := by
  intro O _ _ C _ _ _ K κ _ ε hK hspan hind
  have hε : ∀ u, ε u ∈ K := fun u => by
    rw [hspan]; exact Ideal.subset_span ⟨u, rfl⟩
  have hex : ∀ y : K, ∃ a : κ → O, (y : C) = ∑ u, a u • ε u := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ Ideal.span (Set.range ε) := hspan ▸ hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hy'
    choose a ha using fun u => IsCO.res_surj (O := O) (c u)
    refine ⟨a, ?_⟩
    show y = _
    rw [← hc]
    refine Finset.sum_congr rfl fun u _ => ?_
    have h0 : (c u - algebraMap O C (a u)) * ε u ∈ maximalIdeal C * K :=
      Ideal.mul_mem_mul (ha u) (hε u)
    rw [hK, Ideal.mem_bot, sub_mul, sub_eq_zero] at h0
    rw [h0, Algebra.smul_def]
  have huniq : ∀ a b : κ → O, ∑ u, a u • ε u = ∑ u, b u • ε u →
      ∀ u, residue O (a u) = residue O (b u) := by
    intro a b hab u
    have h := hind (fun u => a u - b u) (by
      simp only [sub_smul, Finset.sum_sub_distrib, hab, sub_self]) u
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact h
  choose a ha using hex
  refine ⟨fun u =>
    { toFun := fun y => residue O (a y u)
      map_add' := fun x y => ?_
      map_smul' := fun c x => ?_ }, fun y => ⟨a y, fun u => rfl, ha y⟩⟩
  · rw [← map_add]
    refine huniq (a (x + y)) (fun u => a x u + a y u) ?_ u
    simp only [add_smul, Finset.sum_add_distrib]
    rw [← ha, ← ha, ← ha]
    rfl
  · have h := huniq (a (c • x)) (fun u => c * a x u) (by
      simp only [mul_smul, ← Finset.smul_sum]
      rw [← ha, ← ha]
      rfl) u
    rw [h, RingHom.id_apply, map_mul, Algebra.smul_def]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrGood
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem two_ne {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (h : l ≠ 2) : (2 : k) ≠ 0 := by
  intro h2
  have h3 : ((2 : ℕ) : k) = 0 := by simpa using h2
  rw [CharP.cast_eq_zero_iff k l] at h3
  exact h ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h3)

private theorem sq_facts {k : Type} [Field k] {t : kˣ} (h : t ^ 2 ≠ 1) :
    (t : k) ≠ (t : k)⁻¹ ∧ (t : k) ≠ 1 ∧ (t : k)⁻¹ ≠ 1 := by
  have h0 : (t : k) ≠ 0 := t.ne_zero
  have h1 : (t : k) ≠ 1 := fun e => h (by ext; simp [e])
  refine ⟨fun e => h ?_, h1, fun e => h1 (inv_eq_one.1 e)⟩
  ext
  rw [Units.val_pow_eq_pow_val, sq, Units.val_one]
  nth_rewrite 2 [e]
  exact mul_inv_cancel₀ h0

private theorem pow_inj {k : Type} [Field k] {t : kˣ} (h : t ^ 2 ≠ 1) {n : ℕ} (hn : n = 2 ∨ n = 3)
    (i j : Fin n) (hij : i ≠ j) : ((t ^ w n i : kˣ) : k) ≠ ((t ^ w n j : kˣ) : k) := by
  obtain ⟨a, b, c⟩ := sq_facts h
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [w, a, b, c, a.symm, b.symm, c.symm]

private theorem diff_inj {k : Type} [Field k] (h2 : (2 : k) ≠ 0) {t : kˣ} (h : t ^ 2 ≠ 1) {n : ℕ}
    (hn : n = 2 ∨ n = 3) (i j : Fin n) (hij : i ≠ j) :
    ((t ^ w n i : kˣ) : k) - ((t⁻¹ ^ w n i : kˣ) : k) ≠ ((t ^ w n j : kˣ) : k) - ((t⁻¹ ^ w n j : kˣ) : k) := by
  obtain ⟨a, -, -⟩ := sq_facts h
  have b : (t : k) - (t : k)⁻¹ ≠ 0 := sub_ne_zero.2 a
  have c : (t : k)⁻¹ - (t : k) ≠ 0 := sub_ne_zero.2 a.symm
  have d : (t : k) - (t : k)⁻¹ ≠ (t : k)⁻¹ - (t : k) := fun e =>
    mul_ne_zero h2 b (by linear_combination e)
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [w, b, c, d, b.symm, c.symm, d.symm]

theorem UpperTheory.V.Fr.pr_good :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (K : Type) [Field K] (φ : k →+* K) (ρ : NRep F n K), ρ.IsBar φ → ρ.Good ∧ lieT K n ≠ 0 ∧ thetaLie (lieT K n) = lieT K n := by
  intro l _ k _ _ F C₀ n hF hn K _ φ ρ hρ
  have h2 : (2 : k) ≠ 0 := two_ne hF.l_odd
  have hs : F.Ψ (F.star F.g0) = (F.Ψ F.g0)⁻¹ := by
    have e : ((F.star F.g0 : F.G0) : F.Γ) = F.c * (F.g0 : F.Γ)⁻¹ * F.c⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, map_inv, hF.Ψ_c]
    simp
  refine ⟨⟨?_, fun i j hij => ?_, fun v => ?_⟩, ?_, ?_⟩
  · have := (map_ne_zero φ).2 h2
    rwa [map_ofNat] at this
  · rw [Matrix.sub_apply, Matrix.sub_apply, hρ.1, hρ.1, hρ.1, hρ.1, hs, ← map_sub, ← map_sub]
    exact fun e => diff_inj h2 hF.baseSubgroup_spec hn i j hij (φ.injective e)
  · obtain ⟨s, hs⟩ := hF.f3 v
    refine ⟨s, fun i j hij e => pow_inj hs hn i j hij (φ.injective ?_)⟩
    rw [← hρ.2, ← hρ.2, e]
  · intro e
    rcases hn with rfl | rfl
    · have := congrFun (congrFun e 0) 0
      simp [lieT, w] at this
    · have := congrFun (congrFun e 0) 0
      simp [lieT, w] at this
  · rcases hn with rfl | rfl
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [thetaLie, lieT, w, Matrix.mul_apply, Fin.sum_univ_two, Jmat, Matrix.diagonal, Fin.rev] <;> norm_num
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [thetaLie, lieT, w, Matrix.mul_apply, Fin.sum_univ_three, Jmat, Matrix.diagonal, Fin.rev] <;> norm_num
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrMu
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_mu :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C'' : Type) [CommRing C''] [Algebra O C''] [IsCO O C''] (K : Ideal C') (q : C' →ₐ[O] C'') (u : K →ₗ[O] ResidueField O), maximalIdeal C' * K = ⊥ → K ≤ maximalIdeal C' → Function.Surjective q → (∀ y : K, u y = 0 → q y = 0) → ∃ μ : ResidueField O →+ C'', IsSq O μ ∧ (∀ y : K, μ (u y) = q y) ∧ ∀ c, ∃ y : K, μ c = q y := by
  intro O _ _ C' _ _ _ C'' _ _ _ K q u hmK hKm hq hker
  classical
  have hwd : ∀ y y' : K, u y = u y' → q y = q y' := by
    intro y y' h
    have h0 : u (y - y') = 0 := by rw [map_sub, h, sub_self]
    have h1 := hker _ h0
    rw [Submodule.coe_sub, map_sub, sub_eq_zero] at h1
    exact h1
  have hmem : ∀ y : K, q y ∈ maximalIdeal C'' := by
    intro y
    rw [← res_eq_zero_iff O C'', res_map, res_eq_zero_iff]
    exact hKm y.2
  by_cases hu : ∀ y, u y = 0
  · refine ⟨0, ⟨fun a c => by simp, fun c => by simp⟩, fun y => ?_, fun c => ⟨0, by simp⟩⟩
    show (0 : C'') = q y
    exact (hker y (hu y)).symm
  · push_neg at hu
    obtain ⟨y0, hy0⟩ := hu
    have hsurj : Function.Surjective u := by
      intro c
      obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (c * (u y0)⁻¹)
      refine ⟨o • y0, ?_⟩
      rw [map_smul, Algebra.smul_def]
      show residue O o * u y0 = c
      rw [ho, mul_assoc, inv_mul_cancel₀ hy0, mul_one]
    let s := Function.surjInv hsurj
    have hs : ∀ c, u (s c) = c := Function.surjInv_eq hsurj
    let μ : ResidueField O →+ C'' :=
      { toFun := fun c => q (s c)
        map_zero' := by
          show q (s 0 : C') = 0
          rw [hwd (s 0) 0 (by rw [hs, map_zero])]
          simp
        map_add' := by
          intro c d
          show q (s (c + d) : C') = q (s c : C') + q (s d : C')
          rw [hwd (s (c + d)) (s c + s d) (by rw [hs, map_add, hs, hs]), Submodule.coe_add, map_add] }
    have hμ : ∀ c, μ c = q (s c) := fun c => rfl
    refine ⟨μ, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro a c
      obtain ⟨b, rfl⟩ := hq a
      obtain ⟨o, ho⟩ := IsCO.res_surj (O := O) b
      have hby : b * (s c : C') = o • (s c : C') := by
        have hz : (b - algebraMap O C' o) * (s c : C') = 0 := by
          have hin : (b - algebraMap O C' o) * (s c : C') ∈ maximalIdeal C' * K :=
            Ideal.mul_mem_mul ho (s c).2
          rw [hmK] at hin
          simpa using hin
        rw [Algebra.smul_def]
        linear_combination hz
      have hres : res O C' b = algebraMap O (ResidueField O) o := by
        rw [← AlgHom.commutes (res O C') o, ← sub_eq_zero, ← map_sub, res_eq_zero_iff]
        exact ho
      have hw := hwd (s (res O C'' (q b) * c)) (o • s c)
        (by rw [hs, res_map, hres, map_smul, hs, Algebra.smul_def])
      rw [hμ, hμ, hw, Submodule.coe_smul_of_tower, ← hby, map_mul]
    · intro c
      rw [hμ]
      exact hmem _
    · intro y
      rw [hμ]
      exact hwd _ _ (hs _)
    · intro c
      exact ⟨s c, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrNorm1
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_norm1 :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] (p : C' →ₐ[O] C) (n : ℕ) (x : GG n C'), maximalIdeal C' * RingHom.ker p = ⊥ → RingHom.ker p ≤ maximalIdeal C' → (2 : ResidueField O) ≠ 0 → x * x = 1 → x.right = -1 → x.mat.map p = 1 → ∃ h : GL (Fin n) C', (h : Matrix (Fin n) (Fin n) C').map p = 1 ∧ (GG.ofGL h * x * (GG.ofGL h)⁻¹).mat = 1 := by
  intro O _ _ C' _ _ _ C _ _ p n x hmI hle h2R hxx hr hmap
  have hgt : x.left * theta x.left = 1 := by
    have hl := congrArg SemidirectProduct.left hxx
    simpa [SemidirectProduct.mul_left, hr] using hl
  have hθ : ∀ u : GL (Fin n) C', ((theta u⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') =
      Jmat C' n * (u : Matrix (Fin n) (Fin n) C')ᵀ * Jmat C' n := by
    intro u
    rw [show theta u⁻¹ = (theta u)⁻¹ from map_inv (thetaAut n C') u, theta_inv_val]
  have hgg : (x.left : Matrix (Fin n) (Fin n) C') =
      Jmat C' n * (x.left : Matrix (Fin n) (Fin n) C')ᵀ * Jmat C' n := by
    have h1 : (theta x.left)⁻¹ = x.left := inv_eq_of_mul_eq_one_left hgt
    rw [← theta_inv_val x.left, h1]
  have hsq : ∀ a b : C', a ∈ RingHom.ker p → b ∈ RingHom.ker p → a * b = 0 := by
    intro a b ha hb
    have hab : a * b ∈ maximalIdeal C' * RingHom.ker p := Ideal.mul_mem_mul (hle ha) hb
    rw [hmI] at hab
    exact (Ideal.mem_bot).mp hab
  have hp1 : ∀ i j : Fin n,
      p ((1 : Matrix (Fin n) (Fin n) C') i j) = (1 : Matrix (Fin n) (Fin n) C) i j := by
    intro i j
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  set X : Matrix (Fin n) (Fin n) C' := (x.left : Matrix (Fin n) (Fin n) C') - 1 with hXdef
  have hX : ∀ i j, X i j ∈ RingHom.ker p := by
    intro i j
    have hgij : p ((x.left : Matrix (Fin n) (Fin n) C') i j) = (1 : Matrix (Fin n) (Fin n) C) i j :=
      congrFun (congrFun hmap i) j
    rw [RingHom.mem_ker, hXdef, Matrix.sub_apply, map_sub, hp1, hgij, sub_self]
  have hXX : X * X = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun k _ => hsq _ _ (hX i k) (hX k j)
  have hXJ : Jmat C' n * Xᵀ * Jmat C' n = X := by
    rw [hXdef, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Jmat_mul_Jmat, ← hgg]
  have hO : IsUnit (2 : O) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, map_ofNat]
    exact h2R
  have h2 : IsUnit (2 : C') := by
    have h2' := hO.map (algebraMap O C')
    rwa [map_ofNat] at h2'
  have hc2 : (↑h2.unit⁻¹ : C') * 2 = 1 := h2.val_inv_mul
  set Y : Matrix (Fin n) (Fin n) C' := (↑h2.unit⁻¹ : C') • X with hYdef
  have hYX : Y * X = 0 := by rw [hYdef, Matrix.smul_mul, hXX, smul_zero]
  have hXY : X * Y = 0 := by rw [hYdef, Matrix.mul_smul, hXX, smul_zero]
  have hYY : Y * Y = 0 := by rw [hYdef, Matrix.mul_smul, hYX, smul_zero]
  have hY2 : Y + Y = X := by rw [hYdef, ← add_smul, ← mul_two, hc2, one_smul]
  have e1 : (1 - Y) * (1 + Y) = 1 := by
    rw [sub_mul, one_mul, mul_add, mul_one, hYY, add_zero, add_sub_cancel_right]
  have e2 : (1 + Y) * (1 - Y) = 1 := by
    rw [add_mul, one_mul, mul_sub, mul_one, hYY, sub_zero, sub_add_cancel]
  have hpY : ∀ i j, p (Y i j) = 0 := by
    intro i j
    rw [hYdef, Matrix.smul_apply, smul_eq_mul, map_mul, (RingHom.mem_ker).mp (hX i j), mul_zero]
  obtain ⟨U, hU⟩ : ∃ U : GL (Fin n) C', (U : Matrix (Fin n) (Fin n) C') = 1 - Y :=
    ⟨⟨1 - Y, 1 + Y, e1, e2⟩, rfl⟩
  have hJ : Jmat C' n * (1 - Y)ᵀ * Jmat C' n = 1 - Y := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Jmat_mul_Jmat, hYdef, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, hXJ]
  have hg1 : (x.left : Matrix (Fin n) (Fin n) C') = 1 + X := by rw [hXdef, add_sub_cancel]
  have key : (1 - Y) * (1 + X) * (1 - Y) =
      1 + X - (Y + Y) - Y * X - X * Y + Y * Y + Y * X * Y := by noncomm_ring
  refine ⟨U, ?_, ?_⟩
  · ext i j
    show p ((U : Matrix (Fin n) (Fin n) C') i j) = (1 : Matrix (Fin n) (Fin n) C) i j
    rw [hU, Matrix.sub_apply, map_sub, hp1, hpY, sub_zero]
  · simp [GG.mat, SemidirectProduct.mul_left, hr]
    rw [hθ, hU, hJ, hg1, key, hYX, hXY, hYY, hY2, zero_mul]
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrOfbox
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private def diagHom {H C : Type} [Group H] [CommRing C] {n : ℕ} (m : H →* Matrix (Fin n) (Fin n) C)
    (h : ∀ s, UpT (m s)) (i : Fin n) : H →* C where
  toFun s := m s i i
  map_one' := by simp
  map_mul' s t := by
    rw [map_mul, Matrix.mul_apply, Finset.sum_eq_single i]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h' | h'
      · rw [h s i b h', zero_mul]
      · rw [h t b i h', mul_zero]
    · simp

private def conjHom {H R : Type} [Group H] [Monoid R] (u : Rˣ) (m : H →* R) : H →* R where
  toFun s := (u : R) * m s * ((u⁻¹ : Rˣ) : R)
  map_one' := by simp
  map_mul' s t := by simp [mul_assoc]

private theorem cont_conj {X C : Type} [TopologicalSpace X] [CommRing C] {n : ℕ} (I : Ideal C)
    (m : X → Matrix (Fin n) (Fin n) C) (hm : ∀ i j, AdicCont I fun s => m s i j) (a b : Matrix (Fin n) (Fin n) C)
    (i j : Fin n) : AdicCont I fun s => (a * m s * b) i j := by
  intro N
  have e : (fun s => Ideal.Quotient.mk (I ^ N) ((a * m s * b) i j)) = ∑ q, ∑ p, fun s => Ideal.Quotient.mk (I ^ N) (a i p) * Ideal.Quotient.mk (I ^ N) (m s p q) * Ideal.Quotient.mk (I ^ N) (b q j) := by
    funext s
    simp only [Matrix.mul_apply, Finset.sum_mul, map_sum, map_mul, Finset.sum_apply]
  rw [e]
  refine Finset.sum_induction _ IsLocallyConstant (fun _ _ hf hg => hf.add hg) (IsLocallyConstant.const 0) (fun q _ => ?_)
  refine Finset.sum_induction _ IsLocallyConstant (fun _ _ hf hg => hf.add hg) (IsLocallyConstant.const 0) (fun p _ => ?_)
  exact ((IsLocallyConstant.const _).mul (hm p q N)).mul (IsLocallyConstant.const _)

theorem UpperTheory.V.Fr.pr_ofbox :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (C : Type) [CommRing C] (I : Ideal C) (B : Box F n C), (B.r F.c).mat = 1 → (∀ i j, i ≠ j → ((B.r F.g0).mat - (B.r (F.star F.g0)).mat) i j = 0) → B.Cont I → ∃ ρ : NRep F n C, B.Of ρ ∧ ρ.Cont I := by
  intro l _ k _ _ F C₀ n hF C _ I B hc hdg hcont
  let rr : F.G0 →* Matrix (Fin n) (Fin n) C := (Units.coeHom _).comp (glPart F.del B.r B.nu)
  let m : ∀ v, F.Gv v →* Matrix (Fin n) (Fin n) C := fun v => conjHom (B.g v) (rr.comp (F.loc0 v))
  have hup : ∀ v s, UpT (m v s) := fun v s => B.tri v s
  let ψ : (v : F.V) → Fin n → F.Gv v →* Cˣ := fun v i => (diagHom (m v) (hup v) i).toHomUnits
  have hpol : ∀ g : F.G0, rr (F.star g) = Jmat C n * (rr g)ᵀ * Jmat C n := by
    intro g
    have hcc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hF.c_sq
    have hs : ((F.star g : F.G0) : F.Γ) = F.c * (↑g)⁻¹ * F.c := by
      show ((F.conj g⁻¹ : F.G0) : F.Γ) = _
      rw [Frame.conj, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply, hcc]
      rfl
    have hPl : (B.r F.c).left = 1 := Units.ext hc
    have hPr : (B.r F.c).right = -1 := by rw [B.nu, hF.del_c]
    have hX : (B.r (↑g)⁻¹).left = (glPart F.del B.r B.nu g)⁻¹ := by
      rw [← map_inv]
      rfl
    show ((B.r ↑(F.star g)).left : Matrix (Fin n) (Fin n) C) = _
    rw [hs, map_mul, map_mul, SemidirectProduct.mul_left, SemidirectProduct.mul_left]
    simp only [hPl, hPr, map_one, mul_one, one_mul, sgnAct_neg_one, hX, theta_val, inv_inv]
    rfl
  have hord : ∀ v (g : Fin n → F.Gv v), ordProd (fun s => rr (F.loc0 v s)) (fun i s => ((ψ v i s : Cˣ) : C)) g = 0 := by
    intro v g
    have hf : UpperTheory.V.W.HasFlag (rr.comp (F.loc0 v)).toHomUnits (ψ v) := ⟨B.g v, fun s => ⟨fun i j hij => hup v s i j hij, fun i => rfl⟩⟩
    exact (ord_of_flag (rr.comp (F.loc0 v)) (ψ v) hf).1 g
  refine ⟨⟨rr, ψ, hpol, fun i j hij => hdg i j hij, hord⟩, ⟨hc, fun s => rfl, fun v i s => rfl⟩, ?_, ?_⟩
  · intro i j N
    exact (hcont i j N).comp_continuous continuous_subtype_val
  · intro v i
    exact cont_conj I (fun s => (B.r (F.loc v s)).mat) (fun p q N => (hcont p q N).comp_continuous (continuous_subtype_val.comp (hF.loc_cont v))) ↑(B.g v) ↑(B.g v)⁻¹ i i
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrOpen
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_open :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (B : Box F n R), B.Cont (maximalIdeal R) → IsOpen ((B.bar O).r.ker : Set F.Γ) ∧ IsOpen ((B.bar O).ad.ker : Set F.Γ) ∧ IsLocallyConstant fun s => ((B.bar O).r s).mat := by
  intro l _ k _ _ F C₀ n hF O _ _ R _ _ _ B hB
  have hent : ∀ i j, IsLocallyConstant fun s => ((B.bar O).r s).mat i j := fun i j => by
    have hk : ∀ a ∈ maximalIdeal R ^ 1, (res O R : R →+* ResidueField O) a = 0 := fun a ha => by
      rw [pow_one] at ha
      exact (res_eq_zero_iff O R a).2 ha
    exact (hB i j 1).comp (Ideal.Quotient.lift _ (res O R : R →+* ResidueField O) hk)
  have hmat : IsLocallyConstant fun s => ((B.bar O).r s).mat := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have h : ∀ᶠ y in nhds x, ∀ i j, ((B.bar O).r y).mat i j = ((B.bar O).r x).mat i j :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hent i j).eventually_eq x
    exact h.mono fun y hy => Matrix.ext hy
  have hr : IsOpen ((B.bar O).r.ker : Set F.Γ) := by
    have e : ((B.bar O).r.ker : Set F.Γ) =
        {s | ((B.bar O).r s).mat = 1} ∩ (F.del.ker : Set F.Γ) := by
      ext s
      constructor
      · intro hs
        have hs' : (B.bar O).r s = 1 := hs
        refine ⟨?_, ?_⟩
        · show ((B.bar O).r s).mat = 1
          rw [hs']
          rfl
        · show F.del s = 1
          rw [← (B.bar O).nu s, hs']
          rfl
      · rintro ⟨h1, h2⟩
        show (B.bar O).r s = 1
        refine SemidirectProduct.ext (Units.ext h1) ?_
        rw [(B.bar O).nu s]
        exact h2
    rw [e]
    exact (hmat.isOpen_fiber 1).inter hF.del_open
  refine ⟨hr, Subgroup.isOpen_mono (fun s hs => ?_) hr, hmat⟩
  have hs' : (B.bar O).r s = 1 := hs
  show GG.ad n _ ((B.bar O).r s) = 1
  rw [hs', map_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrSqz
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_sqz :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (n : ℕ) (μ : ResidueField O →+ C), IsSq O μ → ∃ e : Matrix (Fin n) (Fin n) (ResidueField O) → GL (Fin n) C, (∀ X, (e X : Matrix (Fin n) (Fin n) C) = 1 + X.map μ) ∧ (∀ X Y, e (X + Y) = e X * e Y) ∧ (∀ X, (e X)⁻¹ = e (-X)) ∧ (∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) (ResidueField O)), A * X.map μ = (A.map (res O C) * X).map μ ∧ X.map μ * A = (X * A.map (res O C)).map μ) ∧ ∀ (x : GG n C) (X : Matrix (Fin n) (Fin n) (ResidueField O)), x * GG.ofGL (e X) = GG.ofGL (e ((GG.map (res O C : C →+* ResidueField O) x).adFun X)) * x := by
  intro O _ _ C _ _ _ n μ hμ
  have hsq : ∀ c d, μ c * μ d = 0 := by
    intro c d
    have h := hμ.mul (μ c) d
    rw [(res_eq_zero_iff O C _).2 (hμ.mem c), zero_mul, map_zero] at h
    exact h.symm
  have hL : ∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) (ResidueField O)),
      A * X.map μ = (A.map (res O C) * X).map μ := by
    intro A X
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, hμ.mul]
  have hR : ∀ (A : Matrix (Fin n) (Fin n) C) (X : Matrix (Fin n) (Fin n) (ResidueField O)),
      X.map μ * A = (X * A.map (res O C)).map μ := by
    intro A X
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (X i k), hμ.mul, mul_comm]
  have hsqM : ∀ X Y : Matrix (Fin n) (Fin n) (ResidueField O), X.map μ * Y.map μ = 0 := by
    intro X Y
    ext i j
    simp [Matrix.mul_apply, hsq]
  have hadd : ∀ X Y : Matrix (Fin n) (Fin n) (ResidueField O), (X + Y).map μ = X.map μ + Y.map μ := by
    intro X Y
    ext i j
    simp
  have hzero : (0 : Matrix (Fin n) (Fin n) (ResidueField O)).map μ = 0 := by
    ext i j
    simp
  have hu : ∀ X Y : Matrix (Fin n) (Fin n) (ResidueField O),
      (1 + X.map μ) * (1 + Y.map μ) = 1 + (X + Y).map μ := by
    intro X Y
    rw [hadd, show (1 + X.map μ) * (1 + Y.map μ) = 1 + (X.map μ + Y.map μ) + X.map μ * Y.map μ by
      noncomm_ring, hsqM, add_zero]
  let e : Matrix (Fin n) (Fin n) (ResidueField O) → GL (Fin n) C := fun X =>
    ⟨1 + X.map μ, 1 + (-X).map μ, by rw [hu, add_neg_cancel, hzero, add_zero],
      by rw [hu, neg_add_cancel, hzero, add_zero]⟩
  have he : ∀ X, (e X : Matrix (Fin n) (Fin n) C) = 1 + X.map μ := fun X => rfl
  have hemul : ∀ X Y, e (X + Y) = e X * e Y := by
    intro X Y
    apply Units.ext
    rw [Units.val_mul, he, he, he, hu]
  have heinv : ∀ X, (e X)⁻¹ = e (-X) := fun X => Units.ext rfl
  have hconj : ∀ (g : GL (Fin n) C) (h : GL (Fin n) (ResidueField O))
      (Y : Matrix (Fin n) (Fin n) (ResidueField O)),
      (g : Matrix (Fin n) (Fin n) C).map (res O C) = (h : Matrix (Fin n) (Fin n) (ResidueField O)) →
      g * e Y = e ((h : Matrix (Fin n) (Fin n) (ResidueField O)) * Y *
        (↑h⁻¹ : Matrix (Fin n) (Fin n) (ResidueField O))) * g := by
    intro g h Y hh
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, he, he, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul, hL, hR, hh, Matrix.mul_assoc ((h : Matrix (Fin n) (Fin n) (ResidueField O)) * Y),
      Units.inv_mul, Matrix.mul_one]
  have hJ : (Jmat C n).map (res O C) = Jmat (ResidueField O) n :=
    Jmat_map (res O C : C →+* ResidueField O) n
  have htheta : ∀ Y, theta (e Y) = e (thetaLie Y) := by
    intro Y
    apply Units.ext
    rw [theta_val, heinv, he, he, Matrix.transpose_add, Matrix.transpose_one, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, Jmat_mul_Jmat, ← Matrix.transpose_map, hL, hJ, hR, hJ]
    rw [show thetaLie Y = Jmat (ResidueField O) n * (-Y)ᵀ * Jmat (ResidueField O) n by
      simp [thetaLie, Matrix.transpose_neg]]
  refine ⟨e, he, hemul, heinv, fun A X => ⟨hL A X, hR A X⟩, ?_⟩
  intro x X
  obtain ⟨g, s⟩ := x
  have hh : (g : Matrix (Fin n) (Fin n) C).map (res O C) =
      ((GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG n C)).left :
        Matrix (Fin n) (Fin n) (ResidueField O)) := rfl
  have had : GG.adFun (GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG n C)) X =
      ((GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG n C)).left :
        Matrix (Fin n) (Fin n) (ResidueField O)) *
        (if s = 1 then X else thetaLie X) *
        (↑(GG.map (res O C : C →+* ResidueField O) (⟨g, s⟩ : GG n C)).left⁻¹ :
          Matrix (Fin n) (Fin n) (ResidueField O)) := rfl
  rw [had]
  refine SemidirectProduct.ext ?_ ?_
  · simp only [GG.ofGL, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply]
    rcases Int.units_eq_one_or s with rfl | rfl
    · rw [sgnAct_one, if_pos rfl]
      exact hconj _ _ X hh
    · rw [sgnAct_neg_one, if_neg (by decide), htheta]
      exact hconj _ _ _ hh
  · simp only [GG.ofGL, SemidirectProduct.mul_right, SemidirectProduct.right_inl, mul_one, one_mul]
end

