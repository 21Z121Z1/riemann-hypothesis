import Mathlib

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIntegralClosurePreimageOfIsIntegral
section
open Polynomial in
theorem UpperTheory.exists_integralClosure_preimage_of_isIntegral :
    ∀ (R E k : Type) [CommRing R] [Field E] [IsAlgClosed E] [Algebra R E] [CommRing k] [IsDomain k] (ψ : integralClosure R E →+* k) (x : k), IsIntegral ℤ x → ∃ y, ψ y = x := by
  intro R E k _ _ _ _ _ _ ψ x hx
  classical
  obtain ⟨p, hpm, hpx⟩ := hx
  set q : E[X] := p.map (algebraMap ℤ E) with hq
  have hqm : q.Monic := hpm.map _
  have hqs : q.Splits := IsAlgClosed.splits q
  let lift : E → integralClosure R E := fun a => if h : IsIntegral R a then ⟨a, h⟩ else 0
  have hlift : ∀ a ∈ q.roots, ((lift a : integralClosure R E) : E) = a := by
    intro a ha
    have hr : q.IsRoot a := (mem_roots hqm.ne_zero).1 ha
    have hi : IsIntegral ℤ a := ⟨p, hpm, by
      rw [eval₂_eq_eval_map]
      exact hr⟩
    have hiR : IsIntegral R a := hi.tower_top
    simp [lift, hiR]
  have hfac : p.map (algebraMap ℤ (integralClosure R E)) = (q.roots.map fun a => X - C (lift a)).prod := by
    apply Polynomial.map_injective (algebraMap (integralClosure R E) E) Subtype.val_injective
    rw [Polynomial.map_map, Polynomial.map_multiset_prod, Multiset.map_map]
    have e : (algebraMap (integralClosure R E) E).comp (algebraMap ℤ (integralClosure R E)) = algebraMap ℤ E :=
      RingHom.ext_int _ _
    rw [e, ← hq]
    conv_lhs => rw [hqs.eq_prod_roots_of_monic hqm]
    congr 1
    apply Multiset.map_congr rfl
    intro a ha
    simp only [Function.comp_apply, Polynomial.map_sub, map_X, map_C]
    congr 2
    exact (hlift a ha).symm
  have hk : p.map (algebraMap ℤ k) = (q.roots.map fun a => X - C (ψ (lift a))).prod := by
    have e : ψ.comp (algebraMap ℤ (integralClosure R E)) = algebraMap ℤ k := RingHom.ext_int _ _
    rw [← e, ← Polynomial.map_map, hfac, Polynomial.map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp
  have h0 : (p.map (algebraMap ℤ k)).eval x = 0 := by
    rw [eval_map]
    exact hpx
  rw [hk, eval_multiset_prod, Multiset.map_map, Multiset.prod_eq_zero_iff] at h0
  obtain ⟨a, _, ha⟩ := Multiset.mem_map.1 h0
  refine ⟨lift a, ?_⟩
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C] at ha
  exact (sub_eq_zero.1 ha).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIntegralRepDetectingInvariantSubspace
section
open Matrix

namespace UpperTheory.V

private def transl (R : Type) [CommRing R] {G : Type} [Group G] (g : G) : (G → R) →ₗ[R] (G → R) where
  toFun x := fun h => x (g⁻¹ * h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end UpperTheory.V

private theorem UpperTheory.sum_B_smul_pi_sum_smul_eq_sum_smul {G N : Type} [Group G] [Fintype G] [AddCommGroup N] [Module ℂ N]
    (π : Representation ℂ G N) {m : ℕ} (u : Fin m → G → ℂ) (B : G → Matrix (Fin m) (Fin m) ℂ)
    (hR : ∀ g i h, u i (g * h) = ∑ j, B g j i * u j h) (v : N) (g : G) (i : Fin m) :
    ∑ j, B g j i • π g (∑ h, u j h • π h v) = ∑ h, u i h • π h v := by
  have hπ : ∀ (a b : G) (y : N), π a (π b y) = π (a * b) y := fun a b y => by
    rw [map_mul]
    rfl
  calc _ = ∑ h, u i (g * h) • π (g * h) v := by
        simp_rw [map_sum, map_smul, hπ, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun h _ => ?_)
        rw [← Finset.sum_smul, hR]
    _ = _ := Equiv.sum_comp (Equiv.mulLeft g) (fun h => u i h • π h v)

private theorem UpperTheory.sum_smul_pi_average_eq_card_smul_of_dual {G N : Type} [Group G] [Fintype G] [AddCommGroup N] [Module ℂ N]
    (π : Representation ℂ G N) {m : ℕ} (u : Fin m → G → ℂ) (B : G → Matrix (Fin m) (Fin m) ℂ)
    (hR : ∀ g i h, u i (g * h) = ∑ j, B g j i * u j h) (c : Fin m → G → ℂ)
    (hc : ∀ k j, ∑ h, c k h * u j h = if k = j then 1 else 0) (F : Fin m → N)
    (hF : ∀ g i, ∑ j, B g j i • π g (F j) = F i) (i : Fin m) :
    ∑ h, u i h • π h (∑ g, ∑ k, c k g⁻¹ • π g (F k)) = (Fintype.card G : ℂ) • F i := by
  have hπ : ∀ (a b : G) (y : N), π a (π b y) = π (a * b) y := fun a b y => by
    rw [map_mul]
    rfl
  have hinner : ∀ g k, ∑ h, u i h * c k (g⁻¹ * h) = B g k i := by
    intro g k
    rw [← Equiv.sum_comp (Equiv.mulLeft g)]
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
    simp_rw [hR, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    have hc' : ∀ j, ∑ h, u j h * c k h = if k = j then 1 else 0 := fun j => by
      rw [← hc k j]
      exact Finset.sum_congr rfl (fun h _ => mul_comm _ _)
    simp [hc']
  calc ∑ h, u i h • π h (∑ g, ∑ k, c k g⁻¹ • π g (F k))
      = ∑ h, ∑ g, ∑ k, (u i h * c k (g⁻¹ * h)) • π g (F k) := by
        refine Finset.sum_congr rfl (fun h _ => ?_)
        rw [← Equiv.sum_comp (Equiv.mulLeft h⁻¹)]
        simp only [Equiv.coe_mulLeft, map_sum, map_smul, hπ, Finset.smul_sum, smul_smul,
          _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
    _ = ∑ g, ∑ k, (∑ h, u i h * c k (g⁻¹ * h)) • π g (F k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_smul]
    _ = (Fintype.card G : ℂ) • F i := by
        simp_rw [hinner, hF]
        rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

private theorem UpperTheory.exists_dual_family_of_linearIndependent' (O : Type) [CommRing O] [IsDomain O] [Algebra O ℂ] [FaithfulSMul O ℂ]
    {G : Type} [Fintype G] {m : ℕ} (u : Fin m → G → O) (hu : LinearIndependent O u) :
    ∃ c : Fin m → G → ℂ, ∀ k j, ∑ h, c k h * algebraMap O ℂ (u j h) = if k = j then 1 else 0 := by
  classical
  letI : Algebra (FractionRing O) ℂ := FractionRing.liftAlgebra O ℂ
  haveI : IsScalarTower O (FractionRing O) ℂ := FractionRing.isScalarTower_liftAlgebra O ℂ
  let w : Fin m → G → FractionRing O := fun j h => algebraMap O (FractionRing O) (u j h)
  have hw : LinearIndependent (FractionRing O) w := by
    rw [← LinearIndependent.iff_fractionRing O (FractionRing O)]
    have hinj : Function.Injective
        (LinearMap.compLeft (Algebra.linearMap O (FractionRing O)) G) := by
      intro x y hxy
      funext h
      exact IsFractionRing.injective O (FractionRing O) (congrFun hxy h)
    exact hu.map' _ (LinearMap.ker_eq_bot.2 hinj)
  let f : (Fin m → FractionRing O) →ₗ[FractionRing O] (G → FractionRing O) :=
    { toFun := fun x => ∑ j, x j • w j
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.smul_sum, smul_smul] }
  have hf : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    funext j
    exact Fintype.linearIndependent_iff.1 hw x hx j
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective f hf
  have hPw : ∀ j, P (w j) = fun k => if j = k then 1 else 0 := by
    intro j
    have h1 : f (fun k => if j = k then 1 else 0) = w j := by
      simp [f, ite_smul, Finset.sum_ite_eq]
    rw [← h1, ← LinearMap.comp_apply, hP, LinearMap.id_apply]
  refine ⟨fun k h => algebraMap (FractionRing O) ℂ (P (fun h' => if h = h' then 1 else 0) k), ?_⟩
  intro k j
  have hsum : ∑ h, w j h • (fun h' => if h = h' then (1 : FractionRing O) else 0) = w j :=
    (pi_eq_sum_univ (w j)).symm
  have h2 : ∑ h, P (fun h' => if h = h' then 1 else 0) k * w j h = if k = j then 1 else 0 := by
    have := congrFun (congrArg P hsum) k
    rw [map_sum, hPw] at this
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [eq_comm] at this
    simp only [mul_comm]
    rw [← this]
    simp [eq_comm]
  simp only [IsScalarTower.algebraMap_apply O (FractionRing O) ℂ, ← map_mul, ← map_sum]
  rw [show (∑ h, P (fun h' => if h = h' then 1 else 0) k * algebraMap O (FractionRing O) (u j h))
    = if k = j then 1 else 0 from h2]
  split_ifs <;> simp

theorem UpperTheory.exists_integral_rep_detecting_invariant_subspace :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O ℂ] [FaithfulSMul O ℂ] (G : Type) [Group G] [Fintype G] (I : Submodule ℂ (G → ℂ)), (∀ g, ∀ x ∈ I, (fun h => x (g⁻¹ * h)) ∈ I) → I ≤ Submodule.span ℂ {x | x ∈ I ∧ ∀ g, x g ∈ (algebraMap O ℂ).range} → ∃ (m : ℕ) (τ : G →* GL (Fin m) O), ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ G N), (∃ F : Fin m → N, F ≠ 0 ∧ ∀ g i, ∑ j, algebraMap O ℂ (τ g i j) • π g (F j) = F i) ↔ ∃ x ∈ I, ∃ v, ∑ g, x g • π g v ≠ 0 := by
  intro O _ _ _ _ _ G _ _ I hI hspan
  classical
  let ι : (G → O) →ₗ[O] (G → ℂ) := LinearMap.compLeft (Algebra.linearMap O ℂ) G
  let Λ : Submodule O (G → O) := (I.restrictScalars O).comap ι
  obtain ⟨m, b⟩ := Submodule.basisOfPid (Pi.basisFun O G) Λ
  let T : G → (G → O) →ₗ[O] (G → O) := fun g => LinearMap.funLeft O O (fun h => g⁻¹ * h)
  have hT : ∀ g, ∀ y ∈ Λ, T g y ∈ Λ := by
    intro g y hy
    exact hI g _ hy
  let A : G → Matrix (Fin m) (Fin m) O := fun g => LinearMap.toMatrix b b ((T g).restrict (hT g))
  have hA1 : A 1 = 1 := by
    have e : (T 1).restrict (hT 1) = LinearMap.id := by
      refine LinearMap.ext fun y => Subtype.ext (funext fun h => ?_)
      simp [T, LinearMap.funLeft_apply, LinearMap.restrict_apply]
    simp only [A, e, LinearMap.toMatrix_id]
  have hAmul : ∀ g g', A (g * g') = A g * A g' := by
    intro g g'
    have e : (T (g * g')).restrict (hT _) = ((T g).restrict (hT g)).comp ((T g').restrict (hT g')) := by
      refine LinearMap.ext fun y => Subtype.ext (funext fun h => ?_)
      simp [T, LinearMap.funLeft_apply, LinearMap.restrict_apply, _root_.mul_inv_rev, mul_assoc]
    simp only [A, e]
    exact LinearMap.toMatrix_comp b b b _ _
  let τ0 : G →* Matrix (Fin m) (Fin m) O :=
    { toFun := fun g => (A g⁻¹)ᵀ
      map_one' := by simp [hA1]
      map_mul' := by
        intro g g'
        simp only [_root_.mul_inv_rev, hAmul, Matrix.transpose_mul] }
  have hRO : ∀ g i h, (b i : G → O) (g * h) = ∑ j, A g⁻¹ j i * (b j : G → O) h := by
    intro g i h
    have e := b.sum_repr ((T g⁻¹).restrict (hT g⁻¹) (b i))
    have e2 := congrArg (fun z : Λ => (z : G → O) h) e
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at e2
    have e3 : (((T g⁻¹).restrict (hT g⁻¹) (b i) : Λ) : G → O) h = (b i : G → O) (g * h) := by
      simp [T, LinearMap.funLeft_apply, LinearMap.restrict_apply]
    rw [← e3, ← e2]
    simp only [A, LinearMap.toMatrix_apply]
  let u' : Fin m → G → ℂ := fun j h => algebraMap O ℂ ((b j : G → O) h)
  let B : G → Matrix (Fin m) (Fin m) ℂ := fun g j i => algebraMap O ℂ (A g⁻¹ j i)
  have hR : ∀ g i h, u' i (g * h) = ∑ j, B g j i * u' j h := by
    intro g i h
    simp only [u', B, hRO, map_sum, map_mul]
  have hsp : I ≤ Submodule.span ℂ (Set.range u') := by
    refine hspan.trans (Submodule.span_le.2 ?_)
    rintro x ⟨hxI, hxO⟩
    simp only [RingHom.mem_range] at hxO
    choose y hy using hxO
    have hyΛ : y ∈ Λ := by
      show ι y ∈ I
      convert hxI using 1
      funext g
      exact hy g
    have e := b.sum_repr ⟨y, hyΛ⟩
    have hx : x = ∑ j, algebraMap O ℂ (b.repr ⟨y, hyΛ⟩ j) • u' j := by
      funext g
      have e2 := congrArg (fun z : Λ => (z : G → O) g) e
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at e2
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, u']
      rw [← hy g, ← e2, map_sum]
      simp [map_mul]
    rw [hx]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have hli : LinearIndependent O (fun j => (b j : G → O)) :=
    b.linearIndependent.map' Λ.subtype (Submodule.ker_subtype _)
  obtain ⟨c, hc⟩ := UpperTheory.exists_dual_family_of_linearIndependent' O (fun j => (b j : G → O)) hli
  refine ⟨m, τ0.toHomUnits, ?_⟩
  intro N _ _ π
  constructor
  · rintro ⟨F, hF0, hF⟩
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hF0
    refine ⟨u' k, (b k).2, ∑ g, ∑ k, c k g⁻¹ • π g (F k), ?_⟩
    rw [UpperTheory.sum_smul_pi_average_eq_card_smul_of_dual π u' B hR c hc F (fun g i => hF g i) k]
    exact smul_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero) hk
  · rintro ⟨x, hx, v, hv⟩
    refine ⟨fun j => ∑ h, u' j h • π h v, ?_, fun g i => UpperTheory.sum_B_smul_pi_sum_smul_eq_sum_smul π u' B hR v g i⟩
    intro hF0
    apply hv
    let Φ : (G → ℂ) →ₗ[ℂ] N :=
      { toFun := fun y => ∑ g, y g • π g v
        map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
        map_smul' := by intros; simp [Finset.smul_sum, smul_smul] }
    have hker : Submodule.span ℂ (Set.range u') ≤ LinearMap.ker Φ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      show Φ (u' j) = 0
      exact congrFun hF0 j
    exact hker (hsp hx)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsLinearPreimageOfSuccessiveApproximation
section
theorem UpperTheory.exists_linear_preimage_of_successive_approximation :
    ∀ (A M ι : Type) [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι] (I : Ideal A) [IsAdicComplete I A] (V : ℕ → Submodule A M) (σ : (ι → A) →ₗ[A] M), Antitone V → (∀ k, (I ^ k • ⊤ : Submodule A M) ≤ V k) → (∀ f, (∀ k, f ∈ V k) → f = 0) → (∀ j, ∀ f ∈ V j, ∃ a : ι → A, (∀ i, a i ∈ I ^ j) ∧ f - σ a ∈ V (j + 1)) → ∀ j, ∀ f ∈ V j, ∃ a : ι → A, (∀ i, a i ∈ I ^ j) ∧ σ a = f := by
  intro A M ι _ _ _ _ I _ V σ hV hI hsep hstep j f hf
  classical
  let a' : ℕ → M → ι → A := fun k g => if h : g ∈ V k then (hstep k g h).choose else 0
  have ha' : ∀ k g, g ∈ V k → (∀ i, a' k g i ∈ I ^ k) ∧ g - σ (a' k g) ∈ V (k + 1) := by
    intro k g h
    simp only [a', dif_pos h]
    exact (hstep k g h).choose_spec
  let r : ℕ → M := fun n => Nat.rec f (fun n g => g - σ (a' (j + n) g)) n
  have hrs : ∀ n, r (n + 1) = r n - σ (a' (j + n) (r n)) := fun n => rfl
  have hr : ∀ n, r n ∈ V (j + n) := by
    intro n
    induction n with
    | zero => exact hf
    | succ n ih =>
      rw [hrs, ← add_assoc]
      exact (ha' _ _ ih).2
  let b : ℕ → ι → A := fun n => a' (j + n) (r n)
  have hb : ∀ n i, b n i ∈ I ^ (j + n) := fun n => (ha' _ _ (hr n)).1
  have hrsum : ∀ N, r N = f - σ (∑ n ∈ Finset.range N, b n) := by
    intro N
    induction N with
    | zero => simp [r]
    | succ N ih =>
      show r N - σ (b N) = f - σ (∑ n ∈ Finset.range (N + 1), b n)
      rw [ih, Finset.sum_range_succ, map_add]
      abel
  have hlim : ∀ i, ∃ L : A, ∀ n,
      (∑ k ∈ Finset.range n, b k i) ≡ L [SMOD (I ^ n • ⊤ : Submodule A A)] := by
    intro i
    refine IsPrecomplete.prec (inferInstance : IsPrecomplete I A) ?_
    intro m n hmn
    rw [SModEq.sub_mem, ← neg_sub, Submodule.neg_mem_iff, ← Finset.sum_Ico_eq_sub _ hmn]
    refine Submodule.sum_mem _ (fun k hk => ?_)
    have hmk : m ≤ j + k := by
      have := (Finset.mem_Ico.mp hk).1
      omega
    simpa using Submodule.smul_mem_smul (Ideal.pow_le_pow_right hmk (hb k i))
      (Submodule.mem_top : (1 : A) ∈ (⊤ : Submodule A A))
  choose L hL using hlim
  refine ⟨L, fun i => ?_, ?_⟩
  · have h1 := SModEq.sub_mem.mp (hL i j)
    have h2 : (∑ k ∈ Finset.range j, b k i) ∈ I ^ j :=
      Submodule.sum_mem _ (fun k _ => Ideal.pow_le_pow_right (by omega) (hb k i))
    have h1' : (∑ k ∈ Finset.range j, b k i) - L i ∈ I ^ j := by
      simpa [smul_eq_mul, Ideal.mul_top] using h1
    simpa using Submodule.sub_mem _ h2 h1'
  · have h0 : f - σ L = 0 := by
      apply hsep
      intro N
      have hv : ∀ i, ((∑ n ∈ Finset.range N, b n) - L) i ∈ I ^ N := by
        intro i
        have := SModEq.sub_mem.mp (hL i N)
        simpa [Finset.sum_apply, smul_eq_mul, Ideal.mul_top] using this
      have hσ : σ ((∑ n ∈ Finset.range N, b n) - L) ∈ (I ^ N • ⊤ : Submodule A M) := by
        set v := (∑ n ∈ Finset.range N, b n) - L
        rw [pi_eq_sum_univ v, map_sum]
        refine Submodule.sum_mem _ (fun i _ => ?_)
        rw [map_smul]
        exact Submodule.smul_mem_smul (hv i) Submodule.mem_top
      have e : f - σ L = r N + σ ((∑ n ∈ Finset.range N, b n) - L) := by
        rw [hrsum, map_sub]
        abel
      rw [e]
      exact Submodule.add_mem _ (hV (by omega : N ≤ j + N) (hr N)) (hI N hσ)
    exact (sub_eq_zero.mp h0).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsOrdinaryProjectorOfEventuallyPeriodic
section
private theorem UpperTheory.pow_preserves_submodule {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (n : ℕ) :
    ∀ f ∈ U, (T ^ n) f ∈ U := by
  induction n with
  | zero =>
    intro f hf
    simpa using hf
  | succ n ih =>
    intro f hf
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (hT f hf)

private theorem UpperTheory.periodic_difference_shift {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (f : M) (a q : ℕ)
    (h : (T ^ (a + q)) f - (T ^ a) f ∈ U) (m : ℕ) (hm : a ≤ m) :
    (T ^ (m + q)) f - (T ^ m) f ∈ U := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
  have h' := UpperTheory.pow_preserves_submodule U T hT r _ h
  have e : (T ^ r) ((T ^ (a + q)) f - (T ^ a) f) = (T ^ (a + r + q)) f - (T ^ (a + r)) f := by
    rw [show a + r + q = r + (a + q) by ring, show a + r = r + a by ring,
      pow_add T r (a + q), pow_add T r a, Module.End.mul_apply, Module.End.mul_apply, map_sub]
  rw [e] at h'
  exact h'

private theorem UpperTheory.periodic_difference_mul_period {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (f : M) (a q : ℕ)
    (h : (T ^ (a + q)) f - (T ^ a) f ∈ U) (m : ℕ) (hm : a ≤ m) (c : ℕ) :
    (T ^ (m + q * c)) f - (T ^ m) f ∈ U := by
  induction c with
  | zero => simp
  | succ c ih =>
    have h2 := UpperTheory.periodic_difference_shift U T hT f a q h (m + q * c) (by omega)
    have e : m + q * (c + 1) = m + q * c + q := by ring
    rw [e]
    have hs := U.add_mem h2 ih
    rw [sub_add_sub_cancel] at hs
    exact hs

private theorem UpperTheory.factorial_powers_cauchy {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Submodule A M) (T : Module.End A M) (hT : ∀ f ∈ U, T f ∈ U) (f : M) (a p : ℕ)
    (h : (T ^ (a + (p + 1))) f - (T ^ a) f ∈ U) :
    ∃ J : ℕ, ∀ i j, J ≤ i → J ≤ j → (T ^ i.factorial) f - (T ^ j.factorial) f ∈ U := by
  obtain ⟨N, hN⟩ : ∃ N, N = a * (p + 1) := ⟨_, rfl⟩
  have haN : a ≤ N := by
    rw [hN]
    exact Nat.le_mul_of_pos_right a (Nat.succ_pos p)
  have hbase : ∀ i, N + (p + 1) ≤ i → (T ^ i.factorial) f - (T ^ N) f ∈ U := by
    intro i hi
    obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.succ_pos p) (show p + 1 ≤ i by omega)
    have hi' : N ≤ i.factorial := le_trans (by omega) (Nat.self_le_factorial i)
    have hak : a ≤ k := by
      rw [hk, hN, mul_comm] at hi'
      exact Nat.le_of_mul_le_mul_left hi' (Nat.succ_pos p)
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hak
    have e : i.factorial = N + (p + 1) * c := by
      rw [hk, hN, Nat.succ_eq_add_one]
      ring
    rw [e]
    exact UpperTheory.periodic_difference_mul_period U T hT f a (p + 1) h N haN c
  refine ⟨N + (p + 1), fun i j hi hj => ?_⟩
  have hs := U.sub_mem (hbase i hi) (hbase j hj)
  rwa [sub_sub_sub_cancel_right] at hs

theorem UpperTheory.exists_ordinaryProjector_of_eventually_periodic :
    ∀ (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (V : ℕ → Submodule A M) (T : Module.End A M), Antitone V → (∀ k, ∀ f ∈ V k, T f ∈ V k) → (∀ f, (∀ k, f ∈ V k) → f = 0) → (∀ a : ℕ → M, (∀ k, a (k + 1) - a k ∈ V k) → ∃ L, ∀ k, L - a k ∈ V k) → (∀ f k, ∃ a p : ℕ, (T ^ (a + (p + 1))) f - (T ^ a) f ∈ V k) → ∃ e : Module.End A M, ∀ f k, (∃ J : ℕ, ∀ j, J ≤ j → (T ^ j.factorial) f - e f ∈ V k) ∧ (∃ n : ℕ, (T ^ (n + 1)) (e f) - e f ∈ V k) ∧ (f ∈ V k → e f ∈ V k) ∧ ((∃ n : ℕ, (T ^ (n + 1)) f - f ∈ V k) → e f - f ∈ V k) := by
  intro A M _ _ _ V T hV hT hsep hcomp hper
  have hJ : ∀ f k, ∃ J : ℕ, ∀ i j, J ≤ i → J ≤ j →
      (T ^ i.factorial) f - (T ^ j.factorial) f ∈ V k := by
    intro f k
    obtain ⟨a, p, h⟩ := hper f k
    exact UpperTheory.factorial_powers_cauchy (V k) T (hT k) f a p h
  choose J hJ using hJ
  let Nm : M → ℕ → ℕ := fun f k => ∑ i ∈ Finset.range (k + 1), J f i
  have hNmJ : ∀ f k, J f k ≤ Nm f k := fun f k =>
    Finset.single_le_sum (f := J f) (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ k)
  have hNmmono : ∀ f k, Nm f k ≤ Nm f (k + 1) := fun f k => by
    simp only [Nm]
    rw [Finset.sum_range_succ _ (k + 1)]
    omega
  have hseq : ∀ f k, (T ^ (Nm f (k + 1)).factorial) f - (T ^ (Nm f k).factorial) f ∈ V k :=
    fun f k => hJ f k _ _ (le_trans (hNmJ f k) (hNmmono f k)) (hNmJ f k)
  have hlim : ∀ f, ∃ L, ∀ k, L - (T ^ (Nm f k).factorial) f ∈ V k := fun f =>
    hcomp (fun k => (T ^ (Nm f k).factorial) f) (hseq f)
  choose L hL using hlim
  let P : M → M → Prop := fun f x => ∀ k, ∃ J : ℕ, ∀ j, J ≤ j → (T ^ j.factorial) f - x ∈ V k
  have hPL : ∀ f, P f (L f) := by
    intro f k
    refine ⟨Nm f k, fun j hj => ?_⟩
    have h1 := hJ f k j (Nm f k) (le_trans (hNmJ f k) hj) (hNmJ f k)
    have hs := (V k).sub_mem h1 (hL f k)
    rwa [sub_sub_sub_cancel_right] at hs
  have huniq : ∀ f x y, P f x → P f y → x = y := by
    intro f x y hx hy
    have hxy : x - y = 0 := by
      apply hsep
      intro k
      obtain ⟨J1, h1⟩ := hx k
      obtain ⟨J2, h2⟩ := hy k
      have hs := (V k).sub_mem (h2 (max J1 J2) (le_max_right _ _)) (h1 (max J1 J2) (le_max_left _ _))
      rwa [sub_sub_sub_cancel_left] at hs
    exact sub_eq_zero.mp hxy
  have hPadd : ∀ f g x y, P f x → P g y → P (f + g) (x + y) := by
    intro f g x y hx hy k
    obtain ⟨J1, h1⟩ := hx k
    obtain ⟨J2, h2⟩ := hy k
    refine ⟨max J1 J2, fun j hj => ?_⟩
    have hs := (V k).add_mem (h1 j (le_trans (le_max_left _ _) hj))
      (h2 j (le_trans (le_max_right _ _) hj))
    rw [map_add]
    convert hs using 1
    abel
  have hPsmul : ∀ (c : A) f x, P f x → P (c • f) (c • x) := by
    intro c f x hx k
    obtain ⟨J1, h1⟩ := hx k
    refine ⟨J1, fun j hj => ?_⟩
    have hs := (V k).smul_mem c (h1 j hj)
    rwa [smul_sub, ← map_smul] at hs
  let e : Module.End A M :=
    { toFun := L
      map_add' := fun f g => huniq (f + g) _ _ (hPL _) (hPadd f g _ _ (hPL f) (hPL g))
      map_smul' := fun c f => huniq (c • f) _ _ (hPL _) (hPsmul c f _ (hPL f)) }
  refine ⟨e, fun f k => ⟨hPL f k, ?_, ?_, ?_⟩⟩
  · obtain ⟨a, p, h⟩ := hper f k
    obtain ⟨J1, h1⟩ := hPL f k
    refine ⟨p, ?_⟩
    show (T ^ (p + 1)) (L f) - L f ∈ V k
    obtain ⟨j, hjdef⟩ : ∃ j, j = max J1 a := ⟨_, rfl⟩
    have hja : a ≤ j.factorial := le_trans (by omega) (Nat.self_le_factorial _)
    have hA := h1 j (by omega)
    have hB := UpperTheory.periodic_difference_shift (V k) T (hT k) f a (p + 1) h j.factorial hja
    have hC := UpperTheory.pow_preserves_submodule (V k) T (hT k) (p + 1) _ hA
    have eq : (T ^ (p + 1)) ((T ^ j.factorial) f) = (T ^ (j.factorial + (p + 1))) f := by
      rw [add_comm j.factorial (p + 1), pow_add T (p + 1) j.factorial, Module.End.mul_apply]
    have hsum := (V k).add_mem ((V k).add_mem ((V k).neg_mem hC) hB) hA
    rw [map_sub, eq] at hsum
    convert hsum using 1
    abel
  · intro hf
    obtain ⟨J1, h1⟩ := hPL f k
    have hA := h1 J1 le_rfl
    have hB := UpperTheory.pow_preserves_submodule (V k) T (hT k) J1.factorial f hf
    show L f ∈ V k
    have hs := (V k).sub_mem hB hA
    rwa [sub_sub_cancel] at hs
  · rintro ⟨n, hn⟩
    have h0 : (T ^ (0 + (n + 1))) f - (T ^ 0) f ∈ V k := by simpa using hn
    obtain ⟨J1, h1⟩ := hPL f k
    obtain ⟨N, hN⟩ : ∃ N, N = max J1 (n + 1) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.succ_pos n) (show n + 1 ≤ N by omega)
    have hB := UpperTheory.periodic_difference_mul_period (V k) T (hT k) f 0 (n + 1) h0 0 le_rfl c
    rw [zero_add, pow_zero, ← hc] at hB
    have hA := h1 N (by omega)
    show L f - f ∈ V k
    have hs := (V k).sub_mem hB hA
    rw [sub_sub_sub_cancel_left] at hs
    simpa using hs
end

