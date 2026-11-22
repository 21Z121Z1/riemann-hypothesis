import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle0001

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PStepFormulaA
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace PStepFormula

theorem qdet_map {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) : f (qdet E u) = qdet (fun a b => f (E a b)) u := by
  simp only [qdet, qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def, Tm,
    map_add, apply_ite f, AlgHom.commutes, map_zero]

theorem glRel_map {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    {E : Fin n → Fin n → A} (h : GlRel E) : GlRel (fun a b => f (E a b)) := by
  intro a b c d
  have := congrArg f (h a b c d)
  simpa only [map_sub, map_mul, apply_ite f, map_zero] using this

section
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem conj_eq (e : V ≃ₗ[ℂ] W) {T : Module.End ℂ V} {T' : Module.End ℂ W}
    (h : ∀ x, e (T x) = T' (e x)) : e.conjAlgEquiv ℂ T = T' := by
  ext x
  simp [LinearEquiv.conjAlgEquiv_apply, h]
end

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem liftA_apply {P : Type} (B : Module.End ℂ M) : liftA n M P B = lift B := rfl

theorem lift_PiJ {m : ℕ} {P : Type} (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) :
    (lift (PiJ m E u) : Module.End ℂ (TV n (TV n M (Fin m)) P)) =
      (List.ofFn fun i => algebraMap ℂ _ u + lift (xJ E i)).prod := by
  rw [← liftA_apply]
  simp only [PiJ, map_list_prod, List.map_ofFn, Function.comp_def, map_add, AlgHom.commutes, liftA_apply]

theorem PiJ_one (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) :
    (PiJ 1 E u : Module.End ℂ (TV n M (Fin 1))) = algebraMap ℂ _ u + Om E 0 := by
  have : (Finset.univ.filter fun i : Fin 1 => i < 0) = ∅ := by
    ext i; simp
  simp [PiJ, xJ]

theorem app_upd_r {α : Type} {m k : ℕ} (I : Fin m → α) (J : Fin k → α) (j : Fin k) (a : α) :
    Function.update (Fin.append I J) (Fin.natAdd m j) a = Fin.append I (Function.update J j a) := by
  funext x
  refine Fin.addCases (fun i => ?_) (fun i => ?_) x
  · rw [Fin.append_left, Function.update_of_ne, Fin.append_left]
    intro h; have := congrArg Fin.val h; simp at this; omega
  · by_cases h : i = j
    · subst h; simp
    · rw [Function.update_of_ne, Fin.append_right, Fin.append_right, Function.update_of_ne h]
      intro h'; exact h (Fin.ext (by have := congrArg Fin.val h'; simp at this; omega))

theorem app_upd_l {α : Type} {m k : ℕ} (I : Fin m → α) (J : Fin k → α) (i : Fin m) (a : α) :
    Function.update (Fin.append I J) (Fin.castAdd k i) a = Fin.append (Function.update I i a) J := by
  funext x
  refine Fin.addCases (fun i' => ?_) (fun j => ?_) x
  · by_cases h : i' = i
    · subst h; simp
    · rw [Function.update_of_ne, Fin.append_left, Fin.append_left, Function.update_of_ne h]
      intro h'; exact h (Fin.ext (by have := congrArg Fin.val h'; simp at this; omega))
  · rw [Fin.append_right, Function.update_of_ne, Fin.append_right]
    intro h; have := congrArg Fin.val h; simp at this; omega

theorem curF_Om_r {m k : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (j : Fin k) (f : TV n M (Fin (m + k))) :
    curF n M m k (Om E (Fin.natAdd m j) f) = Om (fun a b => lift (E a b)) j (curF n M m k f) := by
  funext J I
  simp only [curF_apply, Om_apply, Fin.append_right, app_upd_r]
  rw [Finset.sum_apply]
  simp [curF_apply]

theorem curF_Om_l {m k : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (i : Fin m) (f : TV n M (Fin (m + k))) :
    curF n M m k (Om E (Fin.castAdd k i) f) = lift (Om E i) (curF n M m k f) := by
  funext J I
  simp only [curF_apply, Om_apply, Fin.append_left, app_upd_l, lift_apply]

theorem eq_zero_of_eq_neg' {X : Type} [AddCommGroup X] [Module ℂ X] {x : X} (h : x = -x) : x = 0 := by
  have h2 : (2 : ℂ) • x = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel x
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem alt_swap {X : Type} [AddCommGroup X] [Module ℂ X] (g : TV n X (Fin n)) (J : Fin n → Fin n) (a b : Fin n)
    (h : a ≠ b) : alt Finset.univ g (J ∘ Equiv.swap a b) = -alt Finset.univ g J := by
  rw [alt_apply, alt_apply, ← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv (Equiv.mulLeft (Equiv.swap a b)) _ _ fun σ => ?_
  have h1 : J ∘ ⇑(Equiv.swap a b * σ) = (J ∘ Equiv.swap a b) ∘ σ := by
    funext x; simp
  simp only [Equiv.coe_mulLeft, h1, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap h]
  push_cast
  rw [neg_one_mul, neg_smul, neg_neg]

theorem sum_swap {X : Type} [AddCommGroup X] [Module ℂ X] (h : (Fin n → Fin n) → (Fin 1 → Fin n) → X)
    (hanti : ∀ J a b, a ≠ b → h (J ∘ Equiv.swap a b) = -h J) (J : Fin n → Fin n) (I : Fin 1 → Fin n) :
    ∑ j, h (Function.update J j (I 0)) (Function.update I 0 (J j)) = h J I := by
  classical
  have hz : ∀ K : Fin n → Fin n, ∀ a b, a ≠ b → K a = K b → h K = 0 := by
    intro K a b hab hK
    have hc : K ∘ Equiv.swap a b = K := by
      funext x
      simp only [Function.comp_apply, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, hK]
      · rw [h2, hK]
      · rfl
    have := hanti K a b hab
    rw [hc] at this
    funext I
    exact eq_zero_of_eq_neg' (congrFun this I)
  by_cases hJ : Function.Injective J
  · obtain ⟨p, hp⟩ := (Finite.injective_iff_surjective.mp hJ) (I 0)
    rw [Finset.sum_eq_single p]
    · rw [← hp, Function.update_eq_self, hp, Function.update_eq_self]
    · intro j _ hj
      rw [hz (Function.update J j (I 0)) j p hj (by simp [Function.update_of_ne (Ne.symm hj), hp]), Pi.zero_apply]
    · simp
  · obtain ⟨a, b, hab, hne⟩ : ∃ a b, J a = J b ∧ a ≠ b := by
      simp only [Function.Injective, not_forall] at hJ
      obtain ⟨a, b, h1, h2⟩ := hJ
      exact ⟨a, b, h1, h2⟩
    rw [hz J a b hne hab, Pi.zero_apply, Fintype.sum_eq_add a b hne]
    · have hc : Function.update J b (I 0) = Function.update J a (I 0) ∘ Equiv.swap a b := by
        funext x
        simp only [Function.comp_apply, Equiv.swap_apply_def]
        by_cases h1 : x = a
        · subst h1
          rw [if_pos rfl, Function.update_of_ne hne, Function.update_of_ne (Ne.symm hne), hab]
        · rw [if_neg h1]
          by_cases h2 : x = b
          · subst h2
            rw [if_pos rfl, Function.update_self, Function.update_self]
          · rw [if_neg h2, Function.update_of_ne h2, Function.update_of_ne h1]
      rw [hc, hanti _ a b hne, hab]
      simp
    · rintro c ⟨hca, hcb⟩
      rw [hz _ a b hne (by simp [Function.update_of_ne (Ne.symm hca), Function.update_of_ne (Ne.symm hcb), hab]),
        Pi.zero_apply]

def rot (n : ℕ) : Equiv.Perm (Fin (1 + n)) where
  toFun k := if h : (k : ℕ) < n then ⟨k + 1, by omega⟩ else ⟨0, by omega⟩
  invFun k := if h : (k : ℕ) = 0 then ⟨n, by omega⟩ else ⟨k - 1, by omega⟩
  left_inv k := by
    apply Fin.ext; by_cases h : (k : ℕ) < n <;> simp [h] <;> omega
  right_inv k := by
    apply Fin.ext
    by_cases h : (k : ℕ) = 0
    · simp [h]
    · have h' : (k : ℕ) - 1 < n := by omega
      simp [h, h']; omega

theorem rot_nat (i : Fin n) (h : (i : ℕ) < 1 + n) : rot n ⟨i, h⟩ = Fin.natAdd 1 i := by
  apply Fin.ext; simp [rot, i.2]; omega

theorem rot_last (k : Fin (1 + n)) (h : (k : ℕ) = n) : rot n k = Fin.castAdd n 0 := by
  apply Fin.ext; simp [rot, h]

theorem sum_lt_cast {X : Type} [AddCommMonoid X] (k : Fin (1 + n)) (hk : (k : ℕ) ≤ n) (f : Fin (1 + n) → X) :
    ∑ i ∈ Finset.univ.filter (· < k), f i =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), f ⟨i, by omega⟩ := by
  refine Finset.sum_bij' (fun a ha => ⟨a, ?_⟩) (fun b _ => ⟨b, by omega⟩) ?_ ?_ ?_ ?_ ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at ha; omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact hb
  · intro a ha; rfl
  · intro b hb; rfl
  · intro a ha; rfl

theorem app_swap (I : Fin 1 → Fin n) (J : Fin n → Fin n) (j : Fin n) :
    Fin.append I J ∘ Equiv.swap (Fin.natAdd 1 j) (Fin.castAdd n 0) =
      Fin.append (Function.update I 0 (J j)) (Function.update J j (I 0)) := by
  funext x
  refine Fin.addCases (fun i => ?_) (fun i => ?_) x
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [Equiv.swap_apply_right, Fin.append_left, Fin.append_right]
  · by_cases h : i = j
    · subst h; simp [Fin.append_left, Fin.append_right]
    · have h1 : Fin.natAdd 1 i ≠ Fin.natAdd 1 j := fun h' => h (Fin.ext (by
        have := congrArg Fin.val h'; simp at this; omega))
      have h2 : Fin.natAdd 1 i ≠ Fin.castAdd n 0 := fun h' => by
        have := congrArg Fin.val h'; simp at this
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.append_right, Fin.append_right,
        Function.update_of_ne h]

theorem conj_xJ {N : ℕ} (hT : TensorGl) (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E)
    (σ : Equiv.Perm (Fin N)) (k : Fin N) :
    (pm σ * xJ E k * pm σ⁻¹ : Module.End ℂ (TV n M (Fin N))) =
      Om E (σ k) + ∑ i ∈ Finset.univ.filter (· < k), pm (Equiv.swap (σ i) (σ k)) := by
  have h4 := (hT n M (Fin N) E hE Finset.univ).2.2.2
  have hinv : (pm σ * pm σ⁻¹ : Module.End ℂ (TV n M (Fin N))) = 1 := by rw [← pm_mul, mul_inv_cancel, pm_one]
  rw [xJ, mul_add, add_mul, h4, mul_assoc, hinv, mul_one, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pm_mul, ← pm_mul, Equiv.swap_apply_apply]

theorem ext_of_alt {W : Type} [AddCommGroup W] [Module ℂ W] {X Y : Module.End ℂ W}
    (h : (lift X : Module.End ℂ (TV n W (Fin n))) * alt Finset.univ = lift Y * alt Finset.univ) : X = Y := by
  classical
  ext w
  let g : TV n W (Fin n) := fun J => if J = id then w else 0
  have hg : alt Finset.univ g id = w := by
    rw [alt_apply, Finset.sum_eq_single 1]
    · simp [g]
    · intro σ _ hσ
      have hs : (id ∘ ⇑σ) ≠ id := fun h' => hσ (Equiv.ext fun x => congrFun h' x)
      simp only [g, if_neg hs, smul_zero]
    · simp
  have := congrArg (fun T : Module.End ℂ (TV n W (Fin n)) => T g id) h
  simpa only [Module.End.mul_apply, lift_apply, hg] using this

end PStepFormula

end PositivityTheory.Rg.Cz

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGKA
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TGK

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

def Aop (K : P → Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (TV n M P) :=
  LinearMap.pi fun I => ∑ J : P → Fin n, (∏ q, K q (I q) (J q)) • LinearMap.proj J

def mAt (p : P) (A : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (TV n M P) :=
  LinearMap.pi fun I => ∑ j, A (I p) j • LinearMap.proj (Function.update I p j)

theorem Aop_apply (K : P → Matrix (Fin n) (Fin n) ℂ) (f : TV n M P) (I : P → Fin n) :
    Aop K f I = ∑ J, (∏ q, K q (I q) (J q)) • f J := by
  simp only [Aop, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply]

theorem mAt_apply (p : P) (A : Matrix (Fin n) (Fin n) ℂ) (f : TV n M P) (I : P → Fin n) :
    mAt p A f I = ∑ j, A (I p) j • f (Function.update I p j) := by
  simp only [mAt, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply]

theorem actT_eq {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M)
    (γ : Γ) : actT lab κ ρ γ = lift (ρ γ) * Aop (fun q => κ (lab q) γ) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [actT_apply, Module.End.mul_apply, lift_apply, Aop_apply, map_sum]
  simp only [map_smul]

theorem lift_comm_Aop (B : Module.End ℂ M) (K : P → Matrix (Fin n) (Fin n) ℂ) : Commute (lift B) (Aop K) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, lift_apply, Aop_apply, map_sum, map_smul]

theorem lift_comm_mAt (B : Module.End ℂ M) (p : P) (A : Matrix (Fin n) (Fin n) ℂ) :
    Commute (lift B) (mAt p A : Module.End ℂ (TV n M P)) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, lift_apply, mAt_apply, map_sum, map_smul]

theorem prod_one_apply (I J : P → Fin n) :
    ∏ q, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q) = if I = J then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · obtain ⟨q, hq⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ q) (Matrix.one_apply_ne hq)

theorem Aop_one : (Aop (fun _ : P => (1 : Matrix (Fin n) (Fin n) ℂ)) : Module.End ℂ (TV n M P)) = 1 := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Aop_apply, prod_one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Module.End.one_apply]

theorem Aop_mul (K L : P → Matrix (Fin n) (Fin n) ℂ) :
    (Aop (fun q => K q * L q) : Module.End ℂ (TV n M P)) = Aop K * Aop L := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [Module.End.mul_apply, Aop_apply, Aop_apply]
  simp_rw [Aop_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J' _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp_rw [Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem eAt_eq (p : P) (a b : Fin n) :
    (eAt p a b : Module.End ℂ (TV n M P)) = mAt p (Matrix.single a b 1) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [eAt_apply, mAt_apply]
  simp only [Matrix.single_apply]
  rcases eq_or_ne (I p) a with h | h
  · simp [h]
  · simp [h, Ne.symm h]

def mAtL (p : P) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (TV n M P) where
  toFun := mAt p
  map_add' A B := by
    refine LinearMap.ext fun f => funext fun I => ?_
    simp only [LinearMap.add_apply, Pi.add_apply, mAt_apply, Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c A := by
    refine LinearMap.ext fun f => funext fun I => ?_
    simp only [LinearMap.smul_apply, Pi.smul_apply, mAt_apply, Matrix.smul_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum, RingHom.id_apply]

theorem prod_split (p : P) (g : P → ℂ) : ∏ q, g q = g p * ∏ q ∈ Finset.univ.erase p, g q :=
  (Finset.mul_prod_erase _ g (Finset.mem_univ p)).symm

theorem mAt_mul_Aop (p : P) (A : Matrix (Fin n) (Fin n) ℂ) (K : P → Matrix (Fin n) (Fin n) ℂ) :
    (mAt p A * Aop K : Module.End ℂ (TV n M P)) = Aop (Function.update K p (A * K p)) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [Module.End.mul_apply, mAt_apply, Aop_apply]
  simp_rw [Aop_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rw [prod_split p (fun q => Function.update K p (A * K p) q (I q) (J q))]
  simp only [Function.update_self, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [prod_split p (fun q => K q (Function.update I p j q) (J q))]
  simp only [Function.update_self]
  rw [mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun q hq => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hq), Function.update_of_ne (Finset.ne_of_mem_erase hq)]

theorem Aop_mul_mAt (p : P) (A : Matrix (Fin n) (Fin n) ℂ) (K : P → Matrix (Fin n) (Fin n) ℂ) :
    (Aop K * mAt p A : Module.End ℂ (TV n M P)) = Aop (Function.update K p (K p * A)) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  rw [Module.End.mul_apply, Aop_apply, Aop_apply]
  simp_rw [mAt_apply, Finset.smul_sum, smul_smul]
  let φ : (P → Fin n) × Fin n → (P → Fin n) × Fin n := fun x => (Function.update x.1 p x.2, x.1 p)
  have hφ : Function.Involutive φ := fun x => by
    simp only [φ, Function.update_idem, Function.update_self, Function.update_eq_self]
  let H : (P → Fin n) × Fin n → M := fun x =>
    ((∏ q, K q (I q) (Function.update x.1 p x.2 q)) * A x.2 (x.1 p)) • f x.1
  calc ∑ J : P → Fin n, ∑ j, ((∏ q, K q (I q) (J q)) * A (J p) j) • f (Function.update J p j)
      = ∑ x : (P → Fin n) × Fin n, H (φ x) := by
        rw [← Fintype.sum_prod_type']
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [H, φ, Function.update_idem, Function.update_self, Function.update_eq_self]
    _ = ∑ x : (P → Fin n) × Fin n, H x := Equiv.sum_comp (hφ.toPerm φ) H
    _ = _ := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun J _ => ?_
        simp only [H]
        rw [← Finset.sum_smul]
        congr 1
        rw [prod_split p (fun q => Function.update K p (K p * A) q (I q) (J q))]
        simp only [Function.update_self, Matrix.mul_apply, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [prod_split p (fun q => K q (I q) (Function.update J p i q))]
        simp only [Function.update_self]
        have hr : ∏ q ∈ Finset.univ.erase p, K q (I q) (Function.update J p i q) =
            ∏ q ∈ Finset.univ.erase p, Function.update K p (K p * A) q (I q) (J q) :=
          Finset.prod_congr rfl fun q hq => by
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hq), Function.update_of_ne (Finset.ne_of_mem_erase hq)]
        rw [hr]
        ring

theorem pm_Aop (σ : Equiv.Perm P) (K : P → Matrix (Fin n) (Fin n) ℂ) (hK : ∀ q, K (σ q) = K q) :
    (pm σ * Aop K : Module.End ℂ (TV n M P)) = Aop K * pm σ := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, pm_apply, Aop_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl (Fin n)) : (P → Fin n) ≃ (P → Fin n)) _ _ fun J => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_def, id, Equiv.symm_apply_apply]
  congr 1
  conv_rhs => rw [← Equiv.prod_comp σ]
  simp [hK]

theorem eAt_comm (p q : P) (h : p ≠ q) (a b c d : Fin n) :
    Commute (eAt p a b : Module.End ℂ (TV n M P)) (eAt q c d) := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, eAt_apply, Function.update_of_ne h, Function.update_of_ne h.symm,
    Function.update_comm h b d I]
  split_ifs <;> rfl

theorem tE_comm {ι : Type} [DecidableEq ι] (E : ι → Fin n → Fin n → Module.End ℂ M)
    (hcomm : ∀ τ τ', τ ≠ τ' → ∀ a b c d, Commute (E τ a b) (E τ' c d)) (lab : P → ι) (τ τ' : ι) (h : τ ≠ τ')
    (a b c d : Fin n) : Commute (tE (fib lab τ) (E τ) a b) (tE (fib lab τ') (E τ') c d) := by
  unfold tE
  refine Commute.add_left (Commute.add_right ?_ ?_) (Commute.add_right ?_ ?_)
  · exact (hcomm τ τ' h a b c d).map (liftA n M P)
  · exact Commute.sum_right _ _ _ fun p _ => lift_comm_eAt _ _ _ _
  · exact Commute.sum_left _ _ _ fun p _ => (lift_comm_eAt _ _ _ _).symm
  · refine Commute.sum_left _ _ _ fun p hp => Commute.sum_right _ _ _ fun q hq => eAt_comm p q ?_ _ _ _ _
    rintro rfl
    simp only [fib, Finset.mem_filter] at hp hq
    exact h (hp.2.symm.trans hq.2)

theorem actT_one {ι Γ : Type} [Group Γ] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (hκ : ∀ τ, κ τ 1 = 1) (hρ : ρ 1 = 1) : actT lab κ ρ 1 = 1 := by
  rw [actT_eq]
  simp only [hκ, hρ, Aop_one, mul_one]
  rfl

theorem actT_mul {ι Γ : Type} [Group Γ] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (hκ : ∀ τ γ δ, κ τ (γ * δ) = κ τ γ * κ τ δ) (hρ : ∀ γ δ, ρ (γ * δ) = ρ γ * ρ δ)
    (γ δ : Γ) : actT lab κ ρ (γ * δ) = actT lab κ ρ γ * actT lab κ ρ δ := by
  simp only [actT_eq, hκ, hρ, Aop_mul, lift_mul, mul_assoc]
  congr 1
  rw [← mul_assoc, (lift_comm_Aop _ _).eq, mul_assoc]

theorem conj_single (U : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ∑ c, ∑ d, (U c a * star (U d b)) • Matrix.single c d (1 : ℂ) = U * Matrix.single a b 1 * Uᴴ := by
  ext i j
  simp [Matrix.sum_apply, Matrix.single_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, ite_and,
    Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]

theorem tE_sum (S : Finset P) (E : Fin n → Fin n → Module.End ℂ M) (k : Fin n → Fin n → ℂ) :
    ∑ c, ∑ d, k c d • tE S E c d =
      lift (∑ c, ∑ d, k c d • E c d) + ∑ p ∈ S, mAt p (∑ c, ∑ d, k c d • Matrix.single c d (1 : ℂ)) := by
  simp only [tE, smul_add, Finset.sum_add_distrib, Finset.smul_sum, eAt_eq]
  congr 1
  · refine LinearMap.ext fun f => funext fun I => ?_
    simp [LinearMap.sum_apply, Finset.sum_apply]
  · have : ∀ p, (mAt p (∑ c, ∑ d, k c d • Matrix.single c d (1 : ℂ)) : Module.End ℂ (TV n M P)) =
        ∑ c, ∑ d, k c d • mAt p (Matrix.single c d 1) := fun p => by
      rw [show (mAt p : _ → Module.End ℂ (TV n M P)) = mAtL p from rfl]
      simp only [map_sum, map_smul]
    simp only [this]
    conv_lhs => arg 2; ext c; rw [Finset.sum_comm]
    rw [Finset.sum_comm]

theorem actT_ad {ι Γ : Type} [DecidableEq ι] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M)
    (hu : ∀ τ γ, κ τ γ * (κ τ γ)ᴴ = 1)
    (had : ∀ γ τ a b, ρ γ * E τ a b = (∑ c, ∑ d, (κ τ γ c a * star (κ τ γ d b)) • E τ c d) * ρ γ)
    (γ : Γ) (τ : ι) (a b : Fin n) :
    actT lab κ ρ γ * tE (fib lab τ) (E τ) a b =
      (∑ c, ∑ d, (κ τ γ c a * star (κ τ γ d b)) • tE (fib lab τ) (E τ) c d) * actT lab κ ρ γ := by
  rw [actT_eq, tE_sum]
  unfold tE
  simp only [eAt_eq]
  rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · rw [mul_assoc, ← (lift_comm_Aop _ _).eq, ← mul_assoc, ← lift_mul, had, lift_mul, mul_assoc]
  · refine Finset.sum_congr rfl fun p hp => ?_
    simp only [fib, Finset.mem_filter] at hp
    rw [mul_assoc, Aop_mul_mAt, ← mul_assoc (mAt _ _), ← (lift_comm_mAt _ _ _).eq, mul_assoc, mAt_mul_Aop]
    congr 2
    simp only [hp.2]
    rw [conj_single (κ τ γ) a b, mul_assoc, mul_eq_one_comm.mp (hu τ γ), mul_one]

theorem pm_actT {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M)
    (σ : Equiv.Perm P) (hσ : ∀ p, lab (σ p) = lab p) (γ : Γ) : Commute (pm σ) (actT lab κ ρ γ) := by
  rw [actT_eq]
  refine Commute.mul_right (lift_comm_pm _ _).symm ?_
  exact pm_Aop σ _ fun q => by simp only [hσ]

end PositivityTheory.Rg.Cz.TGK

end
end

