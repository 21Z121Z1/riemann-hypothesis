import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Descend
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem gen {Γ Γb M R κ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group Γb]
    [TopologicalSpace Γb] [Monoid M] [CommRing R] (I : Ideal R) [IsHausdorff I R] (N : Set Γ) (π : Γ →* Γb)
    (hq : Topology.IsQuotientMap π) (hk : π.ker = (Subgroup.normalClosure N).topologicalClosure)
    (e : κ → M → R) (he : ∀ x y, (∀ k, e k x = e k y) → x = y) (r : Γ →* M) (hN : ∀ g ∈ N, r g = 1)
    (hc : ∀ k, AdicCont I fun g => e k (r g)) :
    ∃ rb : Γb →* M, rb.comp π = r ∧ ∀ k, AdicCont I fun g => e k (rb g) := by
  have hcl : IsClosed (r.ker : Set Γ) := by
    have : (r.ker : Set Γ) = ⋂ k, ⋂ n : ℕ,
        {g | Ideal.Quotient.mk (I ^ n) (e k (r g)) = Ideal.Quotient.mk (I ^ n) (e k 1)} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
      refine ⟨fun h k n => by rw [h], fun h => he _ _ fun k => ?_⟩
      rw [← sub_eq_zero]
      refine IsHausdorff.haus (I := I) inferInstance _ fun n => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
      exact h k n
    rw [this]
    exact isClosed_iInter fun k => isClosed_iInter fun n => (hc k n).isClosed_fiber _
  have hle : π.ker ≤ r.ker := by
    rw [hk]
    exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun g hg => hN g hg) hcl
  have hle' : π.ker ≤ r.toHomUnits.ker := fun g hg => Units.ext (hle hg)
  have hs := hq.surjective
  let φ := π.liftOfRightInverse (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨r.toHomUnits, hle'⟩
  have hφ : ∀ g, ((Units.coeHom M).comp φ) (π g) = r g := fun g =>
    congrArg Units.val (π.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv hs) ⟨r.toHomUnits, hle'⟩ g)
  refine ⟨(Units.coeHom M).comp φ, MonoidHom.ext hφ, fun k n s => ?_⟩
  rw [← hq.isOpen_preimage]
  have := hc k n s
  simp only [← hφ] at this
  exact this

theorem UpperTheory.V.Ws.X1.descend :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (Φ : Fr O Γ) , ∀ {Γb : Type} [Group Γb] [TopologicalSpace Γb] [IsTopologicalGroup Γb] [T2Space Γb] (π : Γ →* Γb), Φ.Quo π → ∀ {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R], (∀ (r : Γ →* M4 R), (∀ g ∈ Φ.N, r g = 1) → (∀ i j, AdicCont I fun g => r g i j) → ∃ rb : Γb →* M4 R, rb.comp π = r ∧ ∀ i j, AdicCont I fun g => rb g i j) ∧ ∀ (ν : Γ →* Rˣ), (∀ g ∈ Φ.N, ν g = 1) → AdicCont I (fun g => (ν g : R)) → ∃ νb : Γb →* Rˣ, νb.comp π = ν ∧ AdicCont I fun g => (νb g : R) := by
  intro O Γ _ _ _ _ _ Φ Γb _ _ _ _ π hπ R _ I _
  have hq : Topology.IsQuotientMap π := hπ.cont.isClosedMap.isQuotientMap hπ.cont hπ.onto
  refine ⟨fun r hN hc => ?_, fun ν hN hc => ?_⟩
  · obtain ⟨rb, h1, h2⟩ := gen I Φ.N π hq hπ.ker (fun (k : Fin 4 × Fin 4) (x : M4 R) => x k.1 k.2)
      (fun x y h => Matrix.ext fun i j => h (i, j)) r hN fun k => hc k.1 k.2
    exact ⟨rb, h1, fun i j => h2 (i, j)⟩
  · obtain ⟨rb, h1, h2⟩ := gen I Φ.N π hq hπ.ker (fun (_ : Unit) (x : Rˣ) => (x : R))
      (fun x y h => Units.ext (h ())) ν hN fun _ => hc
    exact ⟨rb, h1, h2 ()⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.DiagLift
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.X1.exists_symplectic_diagonalizing_lift {A R : Type} [CommRing A] [CommRing R] (f : A →+* R)
    (hsq : ∀ a b, f a = 0 → f b = 0 → a * b = 0) (ν : A) (X : M4 A) (hν : IsUnit ν) (hX : IsGSp ν X)
    (hd : ∀ i j, i ≠ j → f (X i j) = 0) (hu : ∀ i j, i ≠ j → IsUnit (X i i - X j j)) :
    ∃ u : M4 A, IsGSp 1 u ∧ u.map f = 1 ∧ (adj u * X * u).IsDiag := by
  obtain ⟨hmul, -, hadd, -, hone, hmap, -⟩ := grp A
  have mz : ∀ M M' : M4 A, M.map f = 0 → M'.map f = 0 → M * M' = 0 := by
    intro M M' h h'
    ext i j
    rw [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun k _ => hsq _ _ (congrFun (congrFun h i) k) (congrFun (congrFun h' k) j)
  set D : M4 A := Matrix.diagonal fun i => X i i with hD
  set E : M4 A := X - D with hE
  have hXE : X = D + E := by rw [hE]; abel
  have Eii : ∀ i, E i i = 0 := fun i => by simp [hE, hD]
  have Eij : ∀ i j, i ≠ j → E i j = X i j := fun i j h => by simp [hE, hD, Matrix.diagonal_apply_ne _ h]
  have Ef : E.map f = 0 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Eii]
    · simp [Eij i j h, hd i j h]
  have aEf : (adj E).map f = 0 := by
    rw [← hmap, Ef]; ext i j; simp [adj_apply]
  have aD : adj D = Matrix.diagonal fun i => X i.rev i.rev := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, hD, Matrix.diagonal_apply]
  have key : adj D * D + (adj D * E + adj E * D) = ν • (1 : M4 A) := by
    have h : adj (D + E) * (D + E) = ν • (1 : M4 A) := by rw [← hXE]; exact hX
    rw [hadd, add_mul, mul_add, mul_add, mz _ _ aEf Ef] at h
    rw [← h]; abel
  have k1 : ∀ i, X i.rev i.rev * X i i = ν := fun i => by
    have h := congrFun (congrFun key i) i
    rw [aD, hD] at h
    simpa [Matrix.diagonal_mul_diagonal, adj_apply, Eii] using h
  have k2 : ∀ i j, i ≠ j → X i.rev i.rev * E i j + adj E i j * X j j = 0 := fun i j hij => by
    have h := congrFun (congrFun key i) j
    rw [aD, hD] at h
    simpa [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij] using h
  set N : M4 A := Matrix.of fun i j => -(E i j * Ring.inverse (X i i - X j j)) with hN
  have Nf : N.map f = 0 := by
    ext i j
    have h : f (E i j) = 0 := congrFun (congrFun Ef i) j
    simp [hN, h]
  have N1 : ∀ i j, i ≠ j → N i j * (X i i - X j j) = -E i j := fun i j h => by
    rw [hN, Matrix.of_apply, neg_mul, mul_assoc, Ring.inverse_mul_cancel _ (hu i j h), mul_one]
  have aN : adj N = -N := by
    ext i j
    by_cases h : i = j
    · subst h; simp [adj_apply, hN, Eii]
    · have h' : j.rev ≠ i.rev := fun e => h (Fin.rev_injective e).symm
      have uj : IsUnit (X j j) := isUnit_of_mul_isUnit_right (by rw [k1 j]; exact hν)
      have e1 := N1 i j h
      have e2 : adj N i j * (X j.rev j.rev - X i.rev i.rev) = -adj E i j := by
        rw [adj_apply, adj_apply, smul_mul_assoc, N1 _ _ h', smul_neg]
      refine ((hu _ _ h').mul uj).mul_left_inj.mp ?_
      rw [Matrix.neg_apply]
      linear_combination X j j * e2 - k2 i j h + X i.rev i.rev * e1 + N i j * k1 j - N i j * k1 i
  have au : adj (1 + N) = 1 - N := by rw [hadd, hone, aN, sub_eq_add_neg]
  refine ⟨1 + N, ?_, ?_, ?_⟩
  · unfold IsGSp
    rw [au, one_smul, sub_mul, mul_add N, mz _ _ Nf Nf]
    simp
  · rw [Matrix.map_add _ (map_add f), Nf, add_zero, Matrix.map_one _ (map_zero f) (map_one f)]
  · have NDf : (N * D).map f = 0 := by rw [Matrix.map_mul, Nf, zero_mul]
    have e : adj (1 + N) * X * (1 + N) = D + (E + D * N - N * D) := by
      have : (1 - N) * (D + E) * (1 + N) = D + (E + D * N - N * D) + (E * N - N * D * N - N * E - N * E * N) := by
        noncomm_ring
      rw [au]
      conv_lhs => rw [hXE]
      rw [this, mz _ _ Ef Nf, mz _ _ NDf Nf, mz _ _ Nf Ef]
      simp
    intro i j h
    rw [e, hD]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Matrix.diagonal_apply_ne _ h]
    linear_combination N1 i j h

theorem UpperTheory.V.Ws.X1.diagLift :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (ν : A) (X : M4 A), IsUnit ν → IsGSp ν X → (X.map p).IsDiag → (∀ i j, i ≠ j → IsUnit (X i i - X j j)) → ∃ u : M4 A, IsGSp 1 u ∧ u.map p = 1 ∧ (adj u * X * u).IsDiag := by
  intro Λ _ _ _ _ A R _ _ _ _ _ _ p _ hk ν X hν hX hd hu
  have hle : RingHom.ker p ≤ maximalIdeal A := le_maximalIdeal (RingHom.ker_ne_top p)
  refine UpperTheory.V.Ws.X1.exists_symplectic_diagonalizing_lift (p : A →+* R) (fun a b ha hb => ?_) ν X hν hX (fun i j h => hd h) hu
  have h : a * b ∈ maximalIdeal A * RingHom.ker p := Ideal.mul_mem_mul (hle ha) hb
  rwa [hk] at h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.DualZero
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1

private theorem tri_zero {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (ht : Fin 4 → ℤ)
    (hinj : Function.Injective ht) (hb : ∀ i j, ht i - ht j < 4) (hr : ∀ g i j, ht i < ht j → r g i j = 0)
    (ω : Γ → k) (hω : ∀ i j, ∃ g, r g i i * r g⁻¹ j j ≠ ω g) (F : M4 k →ₗ[k] k)
    (hF : ∀ g Y, F (r g * Y * r g⁻¹) = ω g * F Y) : F = 0 := by
  have hexp : ∀ Y : M4 k, F Y = ∑ a, ∑ b, Y a b * F (Matrix.single a b 1) := by
    intro Y
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [show Matrix.single a b (Y a b) = Y a b • Matrix.single a b (1 : k) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  have hent : ∀ (A B : M4 k) (i j a b : Fin 4), (A * (Matrix.single i j 1 : M4 k) * B : M4 k) a b = A a i * B j b := by
    intro A B i j a b
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_mul]
  have main : ∀ n : ℕ, ∀ i j, 4 - (n : ℤ) ≤ ht i - ht j → F (Matrix.single i j 1) = 0 := by
    intro n
    induction n with
    | zero =>
      intro i j hij
      exfalso
      have := hb i j
      push_cast at hij
      omega
    | succ n ih =>
      intro i j hij
      by_cases hlt : 4 - (n : ℤ) ≤ ht i - ht j
      · exact ih i j hlt
      obtain ⟨g, hg⟩ := hω i j
      have hsum := hF g (Matrix.single i j 1)
      rw [hexp (r g * Matrix.single i j 1 * r g⁻¹)] at hsum
      simp only [hent] at hsum
      have inner : ∑ b, r g i i * r g⁻¹ j b * F (Matrix.single i b 1)
          = r g i i * r g⁻¹ j j * F (Matrix.single i j 1) := by
        refine Finset.sum_eq_single j (fun b _ hbj => ?_) (fun h => absurd (Finset.mem_univ _) h)
        by_cases hjb : ht j < ht b
        · rw [hr g⁻¹ j b hjb]
          ring
        · have hne : ht b ≠ ht j := fun e => hbj (hinj e)
          rw [ih i b (by push_cast at hij hlt ⊢; omega)]
          ring
      have outer : ∑ a, ∑ b, r g a i * r g⁻¹ j b * F (Matrix.single a b 1)
          = ∑ b, r g i i * r g⁻¹ j b * F (Matrix.single i b 1) := by
        refine Finset.sum_eq_single i (fun a _ hai => ?_) (fun h => absurd (Finset.mem_univ _) h)
        apply Finset.sum_eq_zero
        intro b _
        by_cases hia : ht a < ht i
        · rw [hr g a i hia]
          ring
        by_cases hjb : ht j < ht b
        · rw [hr g⁻¹ j b hjb]
          ring
        have hne : ht a ≠ ht i := fun e => hai (hinj e)
        rw [ih a b (by push_cast at hij hlt ⊢; omega)]
        ring
      rw [outer, inner] at hsum
      have e : (r g i i * r g⁻¹ j j - ω g) * F (Matrix.single i j 1) = 0 := by
        rw [sub_mul, hsum, sub_self]
      exact (mul_eq_zero.mp e).resolve_left (sub_ne_zero.mpr hg)
  apply LinearMap.ext
  intro Y
  rw [hexp Y, LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  rw [main 8 a b (by have := hb b a; push_cast; omega), mul_zero]

private theorem adj_conj {Γ k : Type} [Group Γ] [CommRing k] {r : Γ →* M4 k} (h : ∀ g, ∃ ν, IsGSp ν (r g)) (g : Γ)
    (X : M4 k) : adj (r g * X * r g⁻¹) = r g * adj X * r g⁻¹ := by
  obtain ⟨ν, hν⟩ := h g
  obtain ⟨μ, hμ⟩ := h g⁻¹
  have G := grp k
  have e1 : r g * r g⁻¹ = 1 := by rw [← r.map_mul, mul_inv_cancel, r.map_one]
  have e2 : r g⁻¹ * r g = 1 := by rw [← r.map_mul, inv_mul_cancel, r.map_one]
  have a1 : adj (r g) = ν • r g⁻¹ := G.2.2.2.2.2.2.1 ν _ _ hν e1
  have a2 : adj (r g⁻¹) = μ • r g := G.2.2.2.2.2.2.1 μ _ _ hμ e2
  have hprod := G.2.2.2.2.2.2.2.1 ν μ _ _ hν hμ
  rw [e1] at hprod
  have e : adj (1 : M4 k) * 1 = (ν * μ) • (1 : M4 k) := hprod
  rw [G.2.2.2.2.1, Matrix.mul_one] at e
  have e00 := congrFun (congrFun e 0) 0
  simp at e00
  have hμν : μ * ν = 1 := by rw [mul_comm]; exact e00.symm
  rw [G.1, G.1, a1, a2, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, smul_smul, hμν, one_smul, Matrix.mul_assoc]

private theorem rt_wt {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ)
    (hm : ∀ i g, Φ.χ i g * Φ.χ i.rev g = Φ.ν g) (i j : Fin 4) (g : Γ) :
    Φ.rt (wt i j) g = Φ.χ i g * Φ.χ j g⁻¹ := by
  have hd : Φ.χ 3 g = Φ.ν g * (Φ.χ 0 g)⁻¹ := eq_mul_inv_of_mul_eq (by rw [mul_comm]; exact hm 0 g)
  have hc : Φ.χ 2 g = Φ.ν g * (Φ.χ 1 g)⁻¹ := eq_mul_inv_of_mul_eq (by rw [mul_comm]; exact hm 1 g)
  rw [map_inv]
  fin_cases i <;> fin_cases j <;> simp [Fr.rt, wt, lamW, muW, hc, hd] <;>
    (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]; abel)

end UpperTheory.V.Ws.X1

theorem UpperTheory.V.Ws.X1.dualZero :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k), Φ.Ok a → ∀ (c : PD Φ.ι Γ k), Φ.Res a c → ∀ (h : ∀ g, ∃ x, IsGSp x (c.r g)) (ω : Γ → k), (∀ w, ∃ g, a (Φ.rt w g) ≠ ω g) → ∀ f : sp4 k →ₗ[k] k, (∀ g X, f (adSp c.r h g X) = ω g * f X) → f = 0 := by
  intro O Γ _ _ _ Φ k _ a hok c hres h ω hωw f hf
  have G := grp k
  have adj_add := G.2.2.1
  have adj_smul := G.2.2.2.1
  have adj_adj := G.2.1
  let AdjL : M4 k →ₗ[k] M4 k := { toFun := adj, map_add' := adj_add, map_smul' := adj_smul }
  have h2 : (2 : k) ≠ 0 := hok.two.ne_zero
  set t : k := (2 : k)⁻¹ with htdef
  have hsub : ∀ Y : M4 k, adj (Y - adj Y) = adj Y - Y := by
    intro Y
    have e := map_sub AdjL Y (adj Y)
    simp only [AdjL, LinearMap.coe_mk, AddHom.coe_mk] at e
    rw [e, adj_adj]
  let π : M4 k →ₗ[k] sp4 k := LinearMap.codRestrict (sp4 k) (t • (LinearMap.id - AdjL)) (fun Y => by
    show adj (t • (Y - adj Y)) = -(t • (Y - adj Y))
    rw [adj_smul, hsub, ← smul_neg, neg_sub])
  have hπ : ∀ Y, ((π Y : sp4 k) : M4 k) = t • (Y - adj Y) := fun Y => rfl
  let F : M4 k →ₗ[k] k := f ∘ₗ π
  have hFc : ∀ g Y, F (c.r g * Y * c.r g⁻¹) = ω g * F Y := by
    intro g Y
    have e : π (c.r g * Y * c.r g⁻¹) = adSp c.r h g (π Y) := by
      apply Subtype.ext
      rw [adSp_val, hπ, hπ, adj_conj h g Y]
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
    show f (π _) = ω g * f (π Y)
    rw [e, hf]
  have hfix : ∀ X : sp4 k, π X = X := by
    intro X
    apply Subtype.ext
    rw [hπ]
    have hX : adj (X : M4 k) = -(X : M4 k) := X.2
    rw [hX, sub_neg_eq_add, ← two_smul k (X : M4 k), smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hω' : ∀ i j, ∃ g, c.r g i i * c.r g⁻¹ j j ≠ ω g := by
    intro i j
    obtain ⟨g, hg⟩ := hωw (wt i j)
    refine ⟨g, ?_⟩
    rw [hres.diag, hres.diag]
    rw [rt_wt Φ hok.mul i j g, Units.val_mul, map_mul] at hg
    exact hg
  have key : ∀ ht : Fin 4 → ℤ, Function.Injective ht → (∀ i j, ht i - ht j < 4) →
      (∀ g i j, ht i < ht j → c.r g i j = 0) → f = 0 := by
    intro ht hi hb hr
    have hF0 := tri_zero c.r ht hi hb hr ω hω' F hFc
    apply LinearMap.ext
    intro X
    have e : F X = 0 := by rw [hF0]; rfl
    calc f X = f (π X) := by rw [hfix X]
      _ = F X := rfl
      _ = 0 := e
  rcases hres.shape with ⟨hS, _⟩ | hS
  · refine key ![-3, -1, -2, 0] (by decide) (by decide) ?_
    intro g i j hlt
    apply hS g i j
    · fin_cases i <;> fin_cases j <;> simp at hlt ⊢
    · fin_cases i <;> fin_cases j <;> simp [nP, wt, lamW, muW, wAl, wBe, wPs, wTh] at hlt ⊢
  · refine key ![-3, -2, -1, 0] (by decide) (by decide) ?_
    intro g i j hlt
    apply hS g i j
    · fin_cases i <;> fin_cases j <;> simp at hlt ⊢
    · fin_cases i <;> fin_cases j <;> simp [nM, wt, lamW, muW, wAl, wBe, wPs, wTh] at hlt ⊢
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ExistsStrictHenselianAbsolutelyClosedLocalRing
section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem exists_strictHenselian_absolutely_closed_local_ring {k A : Type} [CommRing k] [CommRing A] (π : A → k) (μ : k → A)
    (h1 : ∀ c d, μ (c + d) = μ c + μ d) (h2 : ∀ (a : A) c, μ (π a * c) = a * μ c) :
    ∃ T : M4 k →+ M4 A, (∀ Y, Y.map μ = T Y) ∧
      (∀ (M : M4 A) Y, M * T Y = T (M.map π * Y)) ∧
      (∀ (M : M4 A) Y, T Y * M = T (Y * M.map π)) ∧ (∀ Y, adj (T Y) = T (adj Y)) ∧
      ∀ Y, IsUp Y → IsUp (T Y) := by
  let m : k →+ A := AddMonoidHom.mk' μ h1
  have h3 : ∀ (a : A) c, m (π a * c) = a * m c := h2
  refine ⟨m.mapMatrix, fun Y => rfl, fun M Y => ?_, fun M Y => ?_, fun Y => ?_, fun Y hY i j h => ?_⟩
  · ext a b
    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum, h3]
  · ext a b
    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm (Y a c), h3, mul_comm]
  · ext a b
    simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, adj_apply, map_zsmul]
  · simp only [AddMonoidHom.mapMatrix_apply, Matrix.map_apply, hY i j h, map_zero]

private theorem isUp_mul {k : Type} [CommRing k] {X Y : M4 k} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : c < i
  · rw [hX i c hc, zero_mul]
  · rw [hY c j (lt_of_lt_of_le h (not_lt.1 hc)), mul_zero]

private theorem isUp_add {k : Type} [CommRing k] {X Y : M4 k} (hX : IsUp X) (hY : IsUp Y) : IsUp (X + Y) := by
  intro i j h
  rw [Matrix.add_apply, hX i j h, hY i j h, add_zero]

private theorem alg_id {S : Type} [Ring S] (a n B g y : S) (h : n * a = 1) :
    a * (B * g - (g * y - y * g)) * n + (a * (g * (y * n)) + a * -y * g * n) = a * B * n * (a * g * n) := by
  have : a * B * n * (a * g * n) = a * B * (n * a) * g * n := by simp only [mul_assoc]
  rw [this, h]
  noncomm_ring

private theorem rb_lc {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {Γ : Type} [TopologicalSpace Γ]
    {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (r : Γ → M4 R) (rb : Γ → M4 (ResidueField Λ))
    (hc : ∀ i j, AdicCont (maximalIdeal R) fun g => r g i j) (hr : ∀ g, (r g).map (res Λ R) = rb g) :
    IsLocallyConstant rb := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  have : ∀ a b, ∀ᶠ t in nhds s, rb t a b = rb s a b := fun a b => by
    filter_upwards [(hc a b 1).eventually_eq s] with t ht
    rw [Ideal.Quotient.eq, pow_one, ← res_eq_zero_iff Λ, map_sub, sub_eq_zero] at ht
    rw [← hr, ← hr]
    exact ht
  filter_upwards [Filter.eventually_all.2 fun a => Filter.eventually_all.2 (this a)] with t ht
  ext a b
  exact ht a b

theorem UpperTheory.V.Ws.X1.obCor :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {Γ V : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Gv : V → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →* Γ), (∀ v, Continuous (loc v)) → ∀ {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (ν : Γ →* Λˣ) (r : Γ →* M4 R) (n : V → M4 R), AdicCont (maximalIdeal Λ) (fun g => (ν g : Λ)) → WP loc (fun g => algebraMap Λ R (ν g)) r n → (∀ i j, AdicCont (maximalIdeal R) fun g => r g i j) → ∀ (rb : Γ →* M4 (ResidueField Λ)) (nb : V → M4 (ResidueField Λ)) (hb : ∀ g, ∃ x, IsGSp x (rb g)), (∀ g, (r g).map (res Λ R) = rb g) → (∀ v, (n v).map (res Λ R) = nb v) → ∀ (D : SL loc ν r n p) (μ : ResidueField Λ → A), (∀ c d, μ (c + d) = μ c + μ d) → (∀ (a : A) c, μ (res Λ A a * c) = a * μ c) → (∀ c, p (μ c) = 0) → ∀ x ∈ Fr.continuousCoboundaries2 loc (adSp rb hb) (fun v => bor (nb v)), (∀ s t, D.om s t = ((x.1 (s, t)).1 * rb (s * t)).map μ) → (∀ v s, D.de v s = ((x.2 v s).1 * rb (loc v s)).map μ) → WLift loc ν r n p := by
  intro Λ _ _ _ _ Γ V _ _ _ Gv _ _ _ loc hloc A R _ _ _ _ _ _ p hp hs ν r n hν hW hc rb nb hb hr hn D μ m1 m2 m3
    x hx x1 x2
  obtain ⟨T, T0, Tl, Tr, Ta, Tu⟩ := exists_strictHenselian_absolutely_closed_local_ring (res Λ A) μ m1 m2
  simp only [T0, SL.om, SL.de] at x1 x2
  have lc := rb_lc r rb hc hr
  obtain ⟨h, y, b1, b3, b4⟩ := hx
  obtain ⟨class_group_mod_eq_torsion, -, gA3, -, -, gA6, -⟩ := grp A
  obtain ⟨gR1, -, -, -, -, gR6, -⟩ := grp R
  obtain ⟨gk1, -⟩ := grp (ResidueField Λ)
  have aA : ∀ X : M4 A, (adj X).map (res Λ A) = adj (X.map (res Λ A)) := fun X =>
    (gA6 _ (res Λ A : A →+* ResidueField Λ) X).symm
  have aR : ∀ X : M4 R, (adj X).map (res Λ R) = adj (X.map (res Λ R)) := fun X =>
    (gR6 _ (res Λ R : R →+* ResidueField Λ) X).symm
  have mR : ∀ X Y : M4 R, (X * Y).map (res Λ R) = X.map (res Λ R) * Y.map (res Λ R) := fun X Y =>
    Matrix.map_mul (f := (res Λ R : R →+* ResidueField Λ))
  have Tp : ∀ Y, (T Y).map p = 0 := fun Y => by
    rw [← T0]; ext a b; exact m3 _
  have Tres : ∀ Y, (T Y).map (res Λ A) = 0 := fun Y => by
    rw [← T0]; ext a b
    show res Λ A (μ _) = 0
    rw [← res_map p, m3, map_zero]
  have TT : ∀ Y Y', T Y * T Y' = 0 := fun Y Y' => by rw [Tl, Tres, zero_mul, map_zero]
  have rtres : ∀ s, (D.rt s).map (res Λ A) = rb s := fun s => by
    ext a b
    rw [Matrix.map_apply, ← res_map p, ← hr, ← D.rt_map, Matrix.map_apply, Matrix.map_apply]
  have ntres : ∀ v, (D.nt v).map (res Λ A) = nb v := fun s => by
    ext a b
    rw [Matrix.map_apply, ← res_map p, ← hn, ← D.nt_map, Matrix.map_apply, Matrix.map_apply]
  have pert : ∀ (c : A) (g : M4 A) (Y : M4 (ResidueField Λ)), IsGSp c g → Y ∈ sp4 (ResidueField Λ) →
      IsGSp c (g + T (Y * g.map (res Λ A))) := fun c g Y hg hY => by
    have hY' : adj Y = -Y := hY
    unfold IsGSp at *
    rw [gA3, Ta, gk1, hY', add_mul, mul_add, mul_add, TT, Tl, Tr, hg, aA]
    simp only [mul_neg, neg_mul, map_neg, mul_assoc]
    abel
  have inv1 : ∀ s, rb s * rb s⁻¹ = 1 := fun s => by rw [← map_mul, mul_inv_cancel, map_one]
  have inv2 : ∀ s, rb s⁻¹ * rb s = 1 := fun s => by rw [← map_mul, inv_mul_cancel, map_one]
  set f : Γ → M4 A := fun s => D.rt s - T ((h s).1 * rb s) with hf
  have fH : ∀ s, IsGSp (algebraMap Λ A (ν s)) (f s) := fun s => by
    have := pert _ _ _ (D.rt_mult s) (-h s).2
    rw [rtres, Submodule.coe_neg, neg_mul, map_neg, ← sub_eq_add_neg] at this
    exact this
  have fmul : ∀ s t, f (s * t) = f s * f t := fun s t => by
    have e := x1 s t
    rw [b3, sub_eq_iff_eq_add] at e
    have e' : ((dOne (adSp rb hb) h (s, t)).1 : M4 _) * rb (s * t) =
        (h s).1 * rb s * rb t + rb s * ((h t).1 * rb t) - (h (s * t)).1 * rb (s * t) := by
      show ((h s).1 + rb s * (h t).1 * rb s⁻¹ - (h (s * t)).1) * rb (s * t) = _
      rw [sub_mul, add_mul, map_mul, mul_assoc (rb s * (h t).1), ← mul_assoc (rb s⁻¹), inv2, one_mul]
      simp only [mul_assoc]
    rw [hf]
    simp only
    rw [sub_mul, mul_sub, mul_sub, TT, Tl, Tr, rtres, rtres, e, e', map_sub, map_add]
    abel
  have fone : f 1 = 1 := by
    have hu : adj (f 1) * f 1 = 1 := by
      have := fH 1
      unfold IsGSp at this
      rw [this]; simp
    have := fmul 1 1
    rw [mul_one] at this
    calc f 1 = adj (f 1) * f 1 * f 1 := by rw [hu, one_mul]
      _ = 1 := by rw [mul_assoc, ← this, hu]
  have fp : ∀ s, (f s).map p = r s := fun s => by
    rw [hf]
    simp only
    rw [Matrix.map_sub _ (map_sub p), Tp, D.rt_map, sub_zero]
  have fres : ∀ s, (f s).map (res Λ A) = rb s := fun s => by
    ext a b
    rw [Matrix.map_apply, ← res_map p, ← hr, ← fp, Matrix.map_apply, Matrix.map_apply]
  refine ⟨{ toFun := f, map_one' := fone, map_mul' := fmul }, fun v => D.nt v + T ((y v).1 * nb v),
    ⟨fH, fun v => ?_, fun v s => ?_⟩, fun a b N => ?_, fp, fun v => ?_⟩
  · have := pert _ _ _ (D.nt_sp v) (y v).2
    rwa [ntres] at this
  · have n1 : adj (D.nt v) * D.nt v = 1 := by
      have := D.nt_sp v
      unfold IsGSp at this
      rw [this, one_smul]
    have n2 : adj (nb v) * nb v = 1 := by
      rw [← ntres, ← aA]
      have := congrArg (fun X : M4 A => X.map (res Λ A : A →+* ResidueField Λ)) n1
      simp only [Matrix.map_mul] at this
      rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this
    have n3 : nb v * adj (nb v) = 1 := mul_eq_one_comm.1 n2
    have u1 : IsUp (adj (nb v) * rb (loc v s) * nb v) := fun i j hij => by
      rw [← hn, ← hr, ← aR, ← mR, ← mR, Matrix.map_apply, hW.flag v s i j hij, map_zero]
    have u2 : IsUp (adj (nb v) * ((x.2 v s).1 - ((h (loc v s)).1 - (rb (loc v s) * (y v).1 * rb (loc v s)⁻¹ - (y v).1)))
      * nb v) := b4 v s
    set B := (x.2 v s).1 - ((h (loc v s)).1 - (rb (loc v s) * (y v).1 * rb (loc v s)⁻¹ - (y v).1)) with hB
    have e := x2 v s
    rw [sub_eq_iff_eq_add] at e
    have hy : adj (y v).1 = -(y v).1 := (y v).2
    have e1 : f (loc v s) = D.nt v * D.t v s * adj (D.nt v) +
        T (B * rb (loc v s) - (rb (loc v s) * (y v).1 - (y v).1 * rb (loc v s))) := by
      have : B * rb (loc v s) - (rb (loc v s) * (y v).1 - (y v).1 * rb (loc v s)) =
          (x.2 v s).1 * rb (loc v s) - (h (loc v s)).1 * rb (loc v s) := by
        rw [hB, sub_mul, sub_mul, sub_mul, mul_assoc _ _ (rb (loc v s)), inv2, mul_one]
        abel
      rw [this, map_sub, hf]
      simp only
      rw [e]
      abel
    have e2 : adj (D.nt v) * f (loc v s) * D.nt v = D.t v s +
        T (adj (nb v) * (B * rb (loc v s) - (rb (loc v s) * (y v).1 - (y v).1 * rb (loc v s))) * nb v) := by
      rw [e1, mul_add, add_mul, Tl, Tr, aA, ntres]
      congr 1
      rw [← mul_assoc, ← mul_assoc, n1, one_mul, mul_assoc, n1, mul_one]
    have key : adj (D.nt v + T ((y v).1 * nb v)) * f (loc v s) * (D.nt v + T ((y v).1 * nb v)) =
        D.t v s + T ((adj (nb v) * B * nb v) * (adj (nb v) * rb (loc v s) * nb v)) := by
      rw [gA3, Ta, gk1, hy, add_mul, add_mul, mul_add, mul_add, e2, Tr (f _), TT, Tr (D.nt v),
        mul_assoc (adj (D.nt v)), Tl, Tl, fres, aA, ntres, add_zero, add_assoc, add_assoc, ← map_add, ← map_add]
      exact congrArg (fun Z => D.t v s + T Z) (alg_id _ _ _ _ _ n3)
    show IsUp (adj (D.nt v + T ((y v).1 * nb v)) * f (loc v s) * (D.nt v + T ((y v).1 * nb v)))
    rw [key]
    exact isUp_add (D.t_up v s) (Tu _ (isUp_mul u2 u1))
  · have c1 := D.rt_cont a b N
    have c2 : IsLocallyConstant fun s => Ideal.Quotient.mk (maximalIdeal A ^ N) (T ((h s).1 * rb s) a b) :=
      ((b1.comp Subtype.val).mul lc).comp fun Y => Ideal.Quotient.mk (maximalIdeal A ^ N) (T Y a b)
    have c3 := c1.sub c2
    convert c3 using 2 with s
    exact map_sub _ _ _
  · show (D.nt v + T _).map p = _
    rw [Matrix.map_add _ (map_add p), Tp, add_zero, D.nt_map]
end

