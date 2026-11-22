import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEqNsmulOfForallAddChar
section
set_option autoImplicit false

namespace GlobalTheory

namespace ConjIdeal

theorem exists_eq_nsmul_of_forall_zmod {X : Type*} [AddCommGroup X] [Module.Free ℤ X] (M : ℕ) (v : X)
    (h : ∀ t : X →+ ZMod M, t v = 0) : ∃ z : X, v = M • z := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  have hd : ∀ i, (M : ℤ) ∣ b.repr v i := fun i => by
    have := h ((Int.castAddHom (ZMod M)).comp (b.coord i).toAddMonoidHom)
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using this
  refine ⟨b.repr.symm ((b.repr v).mapRange (fun n => n / (M : ℤ)) (by simp)), ?_⟩
  apply b.repr.injective
  ext i
  simp [Int.mul_ediv_cancel' (hd i)]

theorem exists_eq_nsmul_of_forall_addChar {X : Type*} [AddCommGroup X] [Module.Free ℤ X] {M : ℕ}
    (hM : M ≠ 0) {C : Type*} [CommMonoid C] {ζ : C} (hζ : IsPrimitiveRoot ζ M) (v : X)
    (h : ∀ t : AddChar X C, (∀ x, t x ^ M = 1) → t v = 1) : ∃ z : X, v = M • z := by
  haveI : NeZero M := ⟨hM⟩
  refine exists_eq_nsmul_of_forall_zmod M v fun t => ?_
  have h1 := h ((AddChar.zmodChar M hζ.pow_eq_one).compAddMonoidHom t) fun x => by
    rw [← AddChar.map_nsmul_eq_pow]
    simp
  rw [AddChar.compAddMonoidHom_apply, AddChar.zmodChar_apply, hζ.pow_eq_one_iff_dvd] at h1
  rw [← ZMod.val_eq_zero]
  exact Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _)

variable {O : Type*} [CommRing O]

theorem dvd_of_dvd_conj (bar : O ≃+* O) (hbar : ∀ a, bar (bar a) = a) (I : Ideal O)
    (hsup : I ⊔ I.map bar = ⊤) (M : ℕ) {X Y : Type*} [AddCommGroup X] [Module O X] [AddCommGroup Y]
    [Module O Y] (d : X →ₗ[O] Y)
    (h₁ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, d (x • y) = M • z)
    (h₂ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, bar x • d y = M • z) (y : X) : ∃ z : Y, d y = M • z := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hsup)
  obtain ⟨z₁, hz₁⟩ := h₁ j hj y
  obtain ⟨z₂, hz₂⟩ := h₂ (bar i) (Ideal.mem_map_of_mem bar hi) y
  rw [hbar] at hz₂
  refine ⟨z₂ + z₁, ?_⟩
  rw [smul_add, ← hz₁, ← hz₂, map_smul, ← add_smul, hij, one_smul]

theorem dvd_of_zmod (bar : O ≃+* O) (hbar : ∀ a, bar (bar a) = a) (I : Ideal O)
    (hsup : I ⊔ I.map bar = ⊤) (M : ℕ) {X Y : Type*} [AddCommGroup X] [Module O X] [AddCommGroup Y]
    [Module O Y] [Module.Free ℤ Y] (d : X →ₗ[O] Y)
    (h₁ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, d (x • y) = M • z)
    (h₂ : ∀ t : Y →+ ZMod M, ∀ x ∈ I.map bar, ∀ y, t (bar x • d y) = 0) (y : X) :
    ∃ z : Y, d y = M • z :=
  dvd_of_dvd_conj bar hbar I hsup M d h₁
    (fun x hx y => exists_eq_nsmul_of_forall_zmod M _ fun t => h₂ t x hx y) y

theorem dvd_of_addChar (bar : O ≃+* O) (hbar : ∀ a, bar (bar a) = a) (I : Ideal O)
    (hsup : I ⊔ I.map bar = ⊤) {M : ℕ} (hM : M ≠ 0) {C : Type*} [CommMonoid C] {ζ : C}
    (hζ : IsPrimitiveRoot ζ M) {X Y : Type*} [AddCommGroup X] [Module O X] [AddCommGroup Y]
    [Module O Y] [Module.Free ℤ Y] (d : X →ₗ[O] Y)
    (h₁ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, d (x • y) = M • z)
    (h₂ : ∀ t : AddChar Y C, (∀ v, t v ^ M = 1) → ∀ x ∈ I.map bar, ∀ y, t (bar x • d y) = 1) (y : X) :
    ∃ z : Y, d y = M • z :=
  dvd_of_dvd_conj bar hbar I hsup M d h₁
    (fun x hx y => exists_eq_nsmul_of_forall_addChar hM hζ _ fun t ht => h₂ t ht x hx y) y

theorem trans_symm_congr_one (bar : O ≃+* O) (hbar : ∀ a, bar (bar a) = a) (I : Ideal O)
    (hsup : I ⊔ I.map bar = ⊤) {M : ℕ} (hM : M ≠ 0) {C : Type*} [CommMonoid C] {ζ : C}
    (hζ : IsPrimitiveRoot ζ M) {X Y : Type*} [AddCommGroup X] [Module O X] [AddCommGroup Y]
    [Module O Y] [Module.Free ℤ X] (e₁ e₂ : X ≃ₗ[O] Y)
    (h₁ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, e₂ (x • y) = e₁ (x • y) + M • z)
    (h₂ : ∀ t : AddChar X C, (∀ v, t v ^ M = 1) → ∀ x ∈ I.map bar, ∀ χ : Y,
      t (bar x • e₁.symm χ) = t (bar x • e₂.symm χ)) (y : X) :
    ∃ z : X, e₁.trans e₂.symm y = y + M • z := by
  obtain ⟨z, hz⟩ := dvd_of_addChar bar hbar I hsup hM hζ
    ((e₁.trans e₂.symm).toLinearMap - LinearMap.id) (fun x hx y => by
      obtain ⟨z, hz⟩ := h₁ x hx y
      refine ⟨-e₂.symm z, ?_⟩
      have h : e₁ (x • y) = e₂ (x • y) - M • z := by rw [hz]; abel
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearMap.id_apply]
      rw [h, map_sub, map_nsmul, e₂.symm_apply_apply, smul_neg]
      abel) (fun t ht x hx y => by
      have h := h₂ t ht x hx (e₁ y)
      rw [e₁.symm_apply_apply] at h
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearMap.id_apply]
      rw [smul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, ← h, ← AddChar.map_add_eq_mul,
        add_neg_cancel, AddChar.map_zero_eq_one]) y
  refine ⟨z, ?_⟩
  rw [← hz]
  simp

theorem fix_torsion_of_fix_conj (bar : O ≃+* O) (I : Ideal O) (hsup : I ⊔ I.map bar = ⊤) (M : ℕ)
    (hIJ : I * I.map bar ≤ Ideal.span {(M : O)}) {G A : Type*} [CommGroup G] [CommGroup A]
    (act : O → G →* G) (act_one : ∀ x, act 1 x = x)
    (act_add : ∀ a b x, act (a + b) x = act a x * act b x)
    (act_mul : ∀ a b x, act (a * b) x = act a (act b x))
    (e : G → G → A)
    (e_mul : ∀ x x' y, x ^ M = 1 → x' ^ M = 1 → y ^ M = 1 → e (x * x') y = e x y * e x' y)
    (e_nondeg : ∀ x, x ^ M = 1 → (∀ y, y ^ M = 1 → e x y = 1) → x = 1)
    (e_adj : ∀ a x y, x ^ M = 1 → y ^ M = 1 → e (act a x) y = e x (act (bar a) y))
    (θ : G →* G) (θ_act : ∀ a x, x ^ M = 1 → θ (act a x) = act a (θ x))
    (θ_iso : ∀ x y, x ^ M = 1 → y ^ M = 1 → e (θ x) (θ y) = e x y)
    (θ_fix : ∀ a ∈ I.map bar, ∀ y, y ^ M = 1 → θ (act a y) = act a y)
    (x : G) (hx : x ^ M = 1) : θ x = x := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hsup)
  have tors : ∀ (f : G →* G) y, y ^ M = 1 → f y ^ M = 1 := fun f y hy => by
    rw [← map_pow, hy, map_one]
  have act_zero : ∀ y, act 0 y = 1 := fun y => by
    have := act_add 0 0 y
    rw [add_zero] at this
    exact left_eq_mul.mp this
  have act_nat : ∀ (n : ℕ) y, act (n : O) y = y ^ n := fun n y => by
    induction n with
    | zero => simpa using act_zero y
    | succ n ih => rw [Nat.cast_succ, act_add, ih, act_one, pow_succ]
  have e_one : ∀ y, y ^ M = 1 → e 1 y = 1 := fun y hy => by
    have := e_mul 1 1 y (one_pow _) (one_pow _) hy
    rw [mul_one] at this
    exact left_eq_mul.mp this
  have e_one' : ∀ y, y ^ M = 1 → e y 1 = 1 := fun y hy => by
    have := e_adj 0 y 1 hy (one_pow _)
    rw [act_zero, map_one, e_one 1 (one_pow _)] at this
    exact this.symm
  have split : ∀ w y, w ^ M = 1 → y ^ M = 1 → e w y = e w (act i y) * e w (act j y) := fun w y hw hy => by
    have h1 : w = act (bar.symm i) w * act (bar.symm j) w := by
      rw [← act_add, ← map_add, hij, map_one, act_one]
    conv_lhs => rw [h1]
    rw [e_mul _ _ _ (tors _ _ hw) (tors _ _ hw) hy, e_adj _ _ _ hw hy, e_adj _ _ _ hw hy,
      bar.apply_symm_apply, bar.apply_symm_apply]
  have hm : (θ x * x⁻¹) ^ M = 1 := by rw [mul_pow, tors θ x hx, inv_pow, hx, inv_one, mul_one]
  have hu : act i x ^ M = 1 := tors _ _ hx
  have hw : θ (act i x) = act i (θ x * x⁻¹) * act i x := by
    rw [← map_mul, θ_act _ _ hx, inv_mul_cancel_right]
  have key : act i (θ x * x⁻¹) = 1 := by
    refine e_nondeg _ (tors _ _ hm) fun y hy => ?_
    rw [split _ _ (tors _ _ hm) hy]
    have hA : e (act i (θ x * x⁻¹)) (act i y) = 1 := by
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
        (hIJ (Ideal.mul_mem_mul hi (Ideal.mem_map_of_mem bar hi)))
      rw [e_adj _ _ _ hm (tors _ _ hy), ← act_mul, mul_comm (bar i), ← hc, act_mul, act_nat, hy,
        map_one, e_one' _ hm]
    have hB : e (act i (θ x * x⁻¹)) (act j y) = 1 := by
      have hv : act j y ^ M = 1 := tors _ _ hy
      have h := θ_iso _ _ hu hv
      rw [θ_fix j hj y hy, hw, e_mul _ _ _ (tors _ _ hm) hu hv] at h
      exact mul_eq_right.mp h
    rw [hA, hB, mul_one]
  have hx' : x = act i x * act j x := by rw [← act_add, hij, act_one]
  conv_lhs => rw [hx']
  rw [map_mul, hw, key, one_mul, θ_fix j hj x hx, ← hx']

theorem fix_torsion_of_fix_conj_rel (bar : O ≃+* O) (I : Ideal O) (hsup : I ⊔ I.map bar = ⊤) (M : ℕ)
    (hIJ : I * I.map bar ≤ Ideal.span {(M : O)}) {G A : Type*} [CommGroup G] [CommGroup A]
    (act : O → G →* G) (act_one : ∀ x, act 1 x = x)
    (act_add : ∀ a b x, act (a + b) x = act a x * act b x)
    (act_mul : ∀ a b x, act (a * b) x = act a (act b x))
    (R : G → G → A → Prop)
    (R_ex : ∀ x y, x ^ M = 1 → y ^ M = 1 → ∃! c, R x y c)
    (R_mul : ∀ x x' y c c', x ^ M = 1 → x' ^ M = 1 → y ^ M = 1 → R x y c → R x' y c' →
      R (x * x') y (c * c'))
    (R_nondeg : ∀ x, x ^ M = 1 → (∀ y, y ^ M = 1 → R x y 1) → x = 1)
    (R_adj : ∀ a x y c, x ^ M = 1 → y ^ M = 1 → R x (act (bar a) y) c → R (act a x) y c)
    (θ : G →* G) (θ_act : ∀ a x, x ^ M = 1 → θ (act a x) = act a (θ x))
    (θ_iso : ∀ x y c, x ^ M = 1 → y ^ M = 1 → R x y c → R (θ x) (θ y) c)
    (θ_fix : ∀ a ∈ I.map bar, ∀ y, y ^ M = 1 → θ (act a y) = act a y)
    (x : G) (hx : x ^ M = 1) : θ x = x := by
  classical
  have tors : ∀ (f : G →* G) y, y ^ M = 1 → f y ^ M = 1 := fun f y hy => by
    rw [← map_pow, hy, map_one]
  let e : G → G → A := fun x y => if h : ∃ c, R x y c then h.choose else 1
  have he : ∀ x y, x ^ M = 1 → y ^ M = 1 → R x y (e x y) := fun x y hx hy => by
    have h : ∃ c, R x y c := (R_ex x y hx hy).exists
    simp only [e, dif_pos h]
    exact h.choose_spec
  have hu : ∀ x y c, x ^ M = 1 → y ^ M = 1 → R x y c → e x y = c := fun x y c hx hy h =>
    (R_ex x y hx hy).unique (he x y hx hy) h
  refine fix_torsion_of_fix_conj bar I hsup M hIJ act act_one act_add act_mul e ?_ ?_ ?_ θ θ_act ?_
    θ_fix x hx
  · intro x x' y hx hx' hy
    exact hu _ _ _ (by rw [mul_pow, hx, hx', mul_one]) hy
      (R_mul _ _ _ _ _ hx hx' hy (he _ _ hx hy) (he _ _ hx' hy))
  · intro x hx h
    exact R_nondeg x hx fun y hy => h y hy ▸ he x y hx hy
  · intro a x y hx hy
    exact hu _ _ _ (tors _ _ hx) hy (R_adj _ _ _ _ hx hy (he _ _ hx (tors _ _ hy)))
  · intro x y hx hy
    exact hu _ _ _ (tors _ _ hx) (tors _ _ hy) (θ_iso _ _ _ hx hy (he _ _ hx hy))

theorem eq_id_of_fix_conj_mul (bar : O ≃+* O) (I : Ideal O) (hsup : I ⊔ I.map bar = ⊤) (M : ℕ)
    (hIJ : I * I.map bar ≤ Ideal.span {(M : O)}) {N A : Type*} [CommGroup N] [CommGroup A]
    (hN : ∀ x : N, x ^ M = 1) (act : O → N →* N) (act_one : ∀ x, act 1 x = x)
    (act_add : ∀ a b x, act (a + b) x = act a x * act b x)
    (act_mul : ∀ a b x, act (a * b) x = act a (act b x))
    (e : N → N → A) (e_mul : ∀ x x' y, e (x * x') y = e x y * e x' y)
    (e_nondeg : ∀ x, (∀ y, e x y = 1) → x = 1)
    (e_adj : ∀ a x y, e (act a x) y = e x (act (bar a) y))
    (θ : N →* N) (θ_act : ∀ a x, θ (act a x) = act a (θ x))
    (θ_iso : ∀ x y, e (θ x) (θ y) = e x y)
    (θ_fix : ∀ a ∈ I.map bar, ∀ y, θ (act a y) = act a y) : θ = MonoidHom.id N :=
  MonoidHom.ext fun x => fix_torsion_of_fix_conj bar I hsup M hIJ act act_one act_add act_mul e
    (fun x x' y _ _ _ => e_mul x x' y) (fun x _ h => e_nondeg x fun y => h y (hN y))
    (fun a x y _ _ => e_adj a x y) θ (fun a x _ => θ_act a x) (fun x y _ _ => θ_iso x y)
    (fun a ha y _ => θ_fix a ha y) x (hN x)

theorem eq_id_of_fix_conj (bar : O ≃+* O) (I : Ideal O) (hsup : I ⊔ I.map bar = ⊤) (M : ℕ)
    (hIJ : I * I.map bar ≤ Ideal.span {(M : O)}) {N A : Type*} [AddCommGroup N] [Module O N]
    [AddCommGroup A] (hN : ∀ x : N, M • x = 0)
    (e : N → N → A) (e_add : ∀ x x' y, e (x + x') y = e x y + e x' y)
    (e_nondeg : ∀ x, (∀ y, e x y = 0) → x = 0)
    (e_adj : ∀ (a : O) x y, e (a • x) y = e x (bar a • y))
    (θ : N →ₗ[O] N) (θ_iso : ∀ x y, e (θ x) (θ y) = e x y)
    (θ_fix : ∀ a ∈ I.map bar, ∀ y, θ (a • y) = a • y) : θ = LinearMap.id := by
  have h := eq_id_of_fix_conj_mul bar I hsup M hIJ (N := Multiplicative N) (A := Multiplicative A)
    (fun x => hN x.toAdd)
    (fun a => AddMonoidHom.toMultiplicative (DistribSMul.toAddMonoidHom N a))
    (fun x => one_smul O x.toAdd) (fun a b x => add_smul a b x.toAdd)
    (fun a b x => mul_smul a b x.toAdd)
    (fun x y => Multiplicative.ofAdd (e x.toAdd y.toAdd)) (fun x x' y => e_add _ _ _)
    (fun x h => e_nondeg x.toAdd fun y => h (Multiplicative.ofAdd y)) (fun a x y => e_adj a _ _)
    (AddMonoidHom.toMultiplicative θ.toAddMonoidHom) (fun a x => θ.map_smul a x.toAdd)
    (fun x y => θ_iso _ _) (fun a ha y => θ_fix a ha _)
  ext x
  exact DFunLike.congr_fun h (Multiplicative.ofAdd x)

theorem level_rigidity (bar : O ≃+* O) (hbar : ∀ a, bar (bar a) = a) (I : Ideal O)
    (hsup : I ⊔ I.map bar = ⊤) (M : ℕ) (hIJ : I * I.map bar = Ideal.span {(M : O)}) :
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Free ℤ X] (d : X →ₗ[O] X),
      (∀ x ∈ I.map bar, ∀ y, ∃ z : X, d (x • y) = M • z) →
      (∀ t : X →+ ZMod M, ∀ x ∈ I.map bar, ∀ y, t (bar x • d y) = 0) →
      ∀ y, ∃ z : X, d y = M • z) ∧
    (∀ (N A : Type) [AddCommGroup N] [Module O N] [AddCommGroup A], (∀ x : N, M • x = 0) →
      ∀ e : N →+ N →+ A, (∀ x, e x = 0 → x = 0) → (∀ (a : O) x y, e (a • x) y = e x (bar a • y)) →
      ∀ θ : N ≃ₗ[O] N, (∀ x y, e (θ x) (θ y) = e x y) → (∀ a ∈ I.map bar, ∀ y, θ (a • y) = a • y) →
      θ = LinearEquiv.refl O N) := by
  refine ⟨fun X _ _ _ d h₁ h₂ y => dvd_of_zmod bar hbar I hsup M d h₁ h₂ y,
    fun N A _ _ _ hN e hnd hadj θ hiso hfix => ?_⟩
  have h := eq_id_of_fix_conj bar I hsup M hIJ.le hN (fun x y => e x y)
    (fun x x' y => by simp) (fun x h => hnd x (AddMonoidHom.ext h)) hadj θ.toLinearMap hiso hfix
  exact LinearEquiv.toLinearMap_injective h

end ConjIdeal

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionOfIsPushout
section
noncomputable section

namespace GlobalTheory.FieldBaseChange

variable {K F : Type} [Field K] [Field F] [Algebra K F]

section Basic

variable {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module F W]

def IsCoord (a : V →ₛₗ[algebraMap K F] W) (ℓ : F →ₗ[K] K) (Λ : W →+ V) : Prop :=
  ∀ c v, Λ (c • a v) = ℓ c • v

structure IsExtension (a : V →ₛₗ[algebraMap K F] W) : Prop where
  span : Submodule.span F (Set.range a) = ⊤
  coord : ∀ ℓ : F →ₗ[K] K, ∃ Λ, IsCoord a ℓ Λ

private theorem semilinear_range_span_induction {a : V →ₛₗ[algebraMap K F] W}
    (h : Submodule.span F (Set.range a) = ⊤) (p : W → Prop) (h0 : p 0)
    (hadd : ∀ x y, p x → p y → p (x + y)) (hb : ∀ (c : F) v, p (c • a v)) (x : W) : p x := by
  have key : ∀ y ∈ Submodule.span F (Set.range a), ∀ c : F, p (c • y) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      exact fun c => hb c v
    | zero => intro c; rw [smul_zero]; exact h0
    | add y z _ _ hy hz => intro c; rw [smul_add]; exact hadd _ _ (hy c) (hz c)
    | smul d y _ hy => intro c; rw [smul_smul]; exact hy (c * d)
  have hx : x ∈ Submodule.span F (Set.range a) := by rw [h]; exact Submodule.mem_top
  simpa using key x hx 1

theorem addHom_ext {a : V →ₛₗ[algebraMap K F] W} (h : Submodule.span F (Set.range a) = ⊤)
    {M : Type} [AddCommGroup M] {f g : W →+ M} (e : ∀ (c : F) v, f (c • a v) = g (c • a v)) (x : W) :
    f x = g x := by
  exact semilinear_range_span_induction h (fun x => f x = g x) (by simp)
    (fun x y hx hy => by simp only [map_add, hx, hy]) e x

theorem IsCoord.natural {V' W' : Type} [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module F W']
    {a : V →ₛₗ[algebraMap K F] W} {a' : V' →ₛₗ[algebraMap K F] W'}
    (h : Submodule.span F (Set.range a) = ⊤) {ℓ : F →ₗ[K] K} {Λ : W →+ V} {Λ' : W' →+ V'}
    (hΛ : IsCoord a ℓ Λ) (hΛ' : IsCoord a' ℓ Λ') (θ : V →ₗ[K] V') (θ' : W →ₗ[F] W')
    (hθ : ∀ v, θ' (a v) = a' (θ v)) (x : W) : Λ' (θ' x) = θ (Λ x) := by
  have key := addHom_ext h (f := Λ'.comp θ'.toAddMonoidHom) (g := θ.toAddMonoidHom.comp Λ)
    (fun c v => by
      show Λ' (θ' (c • a v)) = θ (Λ (c • a v))
      rw [map_smul, hθ, hΛ' c (θ v), hΛ c v, map_smul]) x
  exact key

theorem exists_expansion {ι : Type} (b : Module.Basis ι K F) {a : V →ₛₗ[algebraMap K F] W}
    (h : Submodule.span F (Set.range a) = ⊤) {Λ : ι → W →+ V} (hΛ : ∀ i, IsCoord a (b.coord i) (Λ i))
    (x : W) : ∃ S : Finset ι, (∀ i ∉ S, Λ i x = 0) ∧
      ∀ S' : Finset ι, S ⊆ S' → x = ∑ i ∈ S', b i • a (Λ i x) := by
  classical
  refine semilinear_range_span_induction h
    (fun x => ∃ S : Finset ι, (∀ i ∉ S, Λ i x = 0) ∧
      ∀ S' : Finset ι, S ⊆ S' → x = ∑ i ∈ S', b i • a (Λ i x)) ?_ ?_ ?_ x
  · exact ⟨∅, fun i _ => map_zero _, fun S' _ => by simp⟩
  · rintro x y ⟨S₁, h₁, h₁'⟩ ⟨S₂, h₂, h₂'⟩
    refine ⟨S₁ ∪ S₂, fun i hi => ?_, fun S' hS' => ?_⟩
    · rw [Finset.mem_union, not_or] at hi
      rw [map_add, h₁ i hi.1, h₂ i hi.2, add_zero]
    · simp only [map_add, smul_add, Finset.sum_add_distrib]
      rw [← h₁' S' (Finset.union_subset_left hS'), ← h₂' S' (Finset.union_subset_right hS')]
  · intro c v
    refine ⟨(b.repr c).support, fun i hi => ?_, fun S' hS' => ?_⟩
    · rw [hΛ i c v, Module.Basis.coord_apply, Finsupp.notMem_support_iff.mp hi, zero_smul]
    · have hterm : ∀ i, b i • a (Λ i (c • a v)) = (b.repr c i • b i) • a v := by
        intro i
        rw [hΛ i c v, Module.Basis.coord_apply, LinearMap.map_smulₛₗ, smul_smul,
          Algebra.smul_def (b.repr c i) (b i), mul_comm (b i)]
      rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_smul]
      congr 1
      conv_lhs => rw [← b.linearCombination_repr c]
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ hS' (fun i r => r • b i) (fun i _ => zero_smul _ _)]

theorem IsExtension.eq_of_coord {a : V →ₛₗ[algebraMap K F] W} (h : IsExtension a) {x y : W}
    (e : ∀ ℓ Λ, IsCoord a ℓ Λ → Λ x = Λ y) : x = y := by
  classical
  let β := Module.Free.chooseBasis K F
  choose Λ hΛ using fun i => h.coord (β.coord i)
  obtain ⟨S₁, -, h₁⟩ := exists_expansion β h.span hΛ x
  obtain ⟨S₂, -, h₂⟩ := exists_expansion β h.span hΛ y
  rw [h₁ (S₁ ∪ S₂) Finset.subset_union_left, h₂ (S₁ ∪ S₂) Finset.subset_union_right]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [e _ _ (hΛ i)]

theorem IsExtension.exists_sum {a : V →ₛₗ[algebraMap K F] W} (h : IsExtension a) (x : W) :
    ∃ (n : ℕ) (c : Fin n → F) (v : Fin n → V), x = ∑ i, c i • a (v i) := by
  refine semilinear_range_span_induction h.span
    (fun x => ∃ (n : ℕ) (c : Fin n → F) (v : Fin n → V), x = ∑ i, c i • a (v i)) ?_ ?_ ?_ x
  · exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  · rintro x y ⟨n, c, v, rfl⟩ ⟨m, c', v', rfl⟩
    refine ⟨n + m, Fin.append c c', Fin.append v v', ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  · intro c v
    exact ⟨1, fun _ => c, fun _ => v, by simp⟩

theorem IsExtension.of_proj {J : Type} {P Q : J → Type} [∀ j, AddCommGroup (P j)] [∀ j, Module K (P j)]
    [∀ j, AddCommGroup (Q j)] [∀ j, Module F (Q j)] (a : V →ₛₗ[algebraMap K F] W)
    (b : ∀ j, P j →ₛₗ[algebraMap K F] Q j) (hb : ∀ j, IsExtension (b j))
    (π : ∀ j, V →ₗ[K] P j) (π' : ∀ j, W →ₗ[F] Q j) (comm : ∀ j v, π' j (a v) = b j (π j v))
    (inj' : ∀ x, (∀ j, π' j x = 0) → x = 0) (T : Finset J) (inj : ∀ v, (∀ j ∈ T, π j v = 0) → v = 0)
    (desc : ∀ (ℓ : F →ₗ[K] K) (Λ : ∀ j, Q j →+ P j), (∀ j, IsCoord (b j) ℓ (Λ j)) →
      ∀ x, ∃ v, ∀ j, π j v = Λ j (π' j x)) : IsExtension a := by
  classical
  have hcoord : ∀ ℓ : F →ₗ[K] K, ∃ Λ, IsCoord a ℓ Λ := by
    intro ℓ
    choose Λj hΛj using fun j => (hb j).coord ℓ
    choose f hf using desc ℓ Λj hΛj
    have uniq : ∀ v v' : V, (∀ j, π j v = π j v') → v = v' := fun v v' e =>
      sub_eq_zero.mp (inj _ (fun j _ => by rw [map_sub, e j, sub_self]))
    refine ⟨{ toFun := f
              map_zero' := uniq _ _ (fun j => by simp [hf])
              map_add' := fun x y => uniq _ _ (fun j => by simp [hf]) }, fun c v => ?_⟩
    refine uniq _ _ (fun j => ?_)
    show π j (f (c • a v)) = π j (ℓ c • v)
    rw [hf, map_smul, comm, hΛj j c (π j v), map_smul]
  refine ⟨?_, hcoord⟩
  let β := Module.Free.chooseBasis K F
  choose Λj hΛj using fun j i => (hb j).coord (β.coord i)
  rw [eq_top_iff]
  intro x _
  choose v hv using fun i => desc (β.coord i) (fun j => Λj j i) (fun j => hΛj j i) x
  choose S hS hS' using fun j => exists_expansion β (hb j).span (fun i => hΛj j i) (π' j x)
  have hv0 : ∀ i ∉ T.biUnion S, v i = 0 := fun i hi => inj _ (fun j hj => by
    rw [hv i j]
    exact hS j i (fun h => hi (Finset.mem_biUnion.mpr ⟨j, hj, h⟩)))
  have hx : x = ∑ i ∈ T.biUnion S, β i • a (v i) := by
    refine (sub_eq_zero.mp (inj' _ (fun j => ?_)))
    rw [map_sub, sub_eq_zero, map_sum]
    simp only [map_smul, comm, hv]
    conv_lhs => rw [hS' j (T.biUnion S ∪ S j) Finset.subset_union_right]
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro i _ hi
    rw [← hv i j, hv0 i hi, map_zero, map_zero, smul_zero]
  rw [hx]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨v i, rfl⟩))

theorem isExtension_of_isPushout {A B : Type} [CommRing A] [CommRing B] [Algebra K A] [Algebra F B]
    [Algebra K B] [Algebra A B] [IsScalarTower K A B] [IsScalarTower K F B] [H : Algebra.IsPushout K F A B]
    (a : A →ₛₗ[algebraMap K F] B) (ha : ∀ x, a x = algebraMap A B x) : IsExtension a := by
  have hb : ∀ (c : F) (v : A), H.out.equiv (c ⊗ₜ v) = c • a v := by
    intro c v
    rw [IsBaseChange.equiv_tmul, ha]
    rfl
  refine ⟨?_, fun ℓ => ?_⟩
  · rw [eq_top_iff]
    rintro y -
    obtain ⟨t, rfl⟩ := H.out.equiv.surjective y
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul c v => rw [hb]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, rfl⟩)
    | add s t hs ht => rw [map_add]; exact Submodule.add_mem _ hs ht
  · refine ⟨(TensorProduct.lid K A).toLinearMap.toAddMonoidHom.comp
      ((TensorProduct.map ℓ LinearMap.id).toAddMonoidHom.comp
        H.out.equiv.symm.toLinearMap.toAddMonoidHom), fun c v => ?_⟩
    show TensorProduct.lid K A (TensorProduct.map ℓ LinearMap.id (H.out.equiv.symm (c • a v))) = ℓ c • v
    rw [← hb, LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, TensorProduct.lid_tmul,
      LinearMap.id_apply]

end Basic

section Graph

variable {R : Type} [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]
  {V₀ V V' W W' : Type} [AddCommGroup V₀] [Module R V₀] [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module F V'] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module F W']
  {J : Type} {P₀ P P' : J → Type} [∀ j, AddCommGroup (P₀ j)] [∀ j, Module R (P₀ j)]
  [∀ j, AddCommGroup (P j)] [∀ j, Module K (P j)] [∀ j, AddCommGroup (P' j)] [∀ j, Module F (P' j)]

theorem graph_bijective (X : Submodule R (V₀ × ∀ j, P₀ j))
    (ρ : V₀ →ₛₗ[algebraMap R K] V) (ρ' : ∀ j, P₀ j →ₛₗ[algebraMap R K] P j)
    (a : V →ₛₗ[algebraMap K F] V') (ha : IsExtension a)
    (b : ∀ j, P j →ₛₗ[algebraMap K F] P' j) (hb : ∀ j, IsExtension (b j))
    (d : W →ₛₗ[algebraMap K F] W') (hd : IsExtension d)
    (π : ∀ j, W →ₗ[K] P j) (π' : ∀ j, W' →ₗ[F] P' j) (comm : ∀ j w, π' j (d w) = b j (π j w))
    (E : V → W → Prop)
    (hE : ∀ v w, E v w ↔ ∃ r : R, r ≠ 0 ∧ ∃ x ∈ X, ρ x.1 = algebraMap R K r • v ∧
      ∀ j, ρ' j (x.2 j) = algebraMap R K r • π j w)
    (bij : (∀ v, ∃! w, E v w) ∧ ∀ w, ∃! v, E v w)
    (E' : V' → W' → Prop)
    (hE' : ∀ v w, E' v w ↔ ∃ (n : ℕ) (c : Fin n → F) (x : Fin n → V₀ × ∀ j, P₀ j), (∀ i, x i ∈ X) ∧
      v = ∑ i, c i • a (ρ (x i).1) ∧ ∀ j, π' j w = ∑ i, c i • b j (ρ' j ((x i).2 j))) :
    (∀ v, ∃! w, E' v w) ∧ ∀ w, ∃! v, E' v w := by
  classical
  have key : ∀ v w, E' v w → ∀ (ℓ : F →ₗ[K] K) (Λa : V' →+ V) (Λd : W' →+ W),
      IsCoord a ℓ Λa → IsCoord d ℓ Λd → E (Λa v) (Λd w) := by
    intro v w hvw ℓ Λa Λd hΛa hΛd
    obtain ⟨n, c, x, hx, rfl, hw⟩ := (hE' v w).mp hvw
    choose Λb hΛb using fun j => (hb j).coord ℓ
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
      (fun i => ℓ (c i))
    choose s hs using fun i => RingHom.mem_rangeS.mp (ht i)
    have hcoef : ∀ i, algebraMap R K (s i) = algebraMap R K (t : R) * ℓ (c i) := by
      intro i; rw [hs i, Algebra.smul_def]
    rw [hE]
    refine ⟨t, nonZeroDivisors.ne_zero t.2, ∑ i, s i • x i,
      Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hx i)), ?_, fun j => ?_⟩
    · rw [Prod.fst_sum, map_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Prod.smul_fst, LinearMap.map_smulₛₗ, hΛa (c i) _, hcoef i, smul_smul]
    · have hnat := IsCoord.natural hd.span hΛd (hΛb j) (π j) (π' j) (comm j) w
      rw [← hnat, hw j, map_sum, Prod.snd_sum, Finset.sum_apply, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Prod.smul_snd, Pi.smul_apply, LinearMap.map_smulₛₗ, hΛb j (c i) _, hcoef i, smul_smul]
  have hne : ∀ r : R, r ≠ 0 → algebraMap K F (algebraMap R K r) ≠ 0 := fun r hr =>
    (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr)
  have hcancel : ∀ (c : F) (r : R), r ≠ 0 →
      (c * (algebraMap K F (algebraMap R K r))⁻¹) * algebraMap K F (algebraMap R K r) = c :=
    fun c r hr => by rw [mul_assoc, inv_mul_cancel₀ (hne r hr), mul_one]
  refine ⟨fun v => ?_, fun w => ?_⟩
  · obtain ⟨n, c, u, rfl⟩ := ha.exists_sum v
    choose φ hφ using fun i => (bij.1 (u i)).exists
    choose r hr y hy hy₁ hy₂ using fun i => (hE _ _).mp (hφ i)
    have h₀ : E' (∑ i, c i • a (u i)) (∑ i, c i • d (φ i)) := by
      rw [hE']
      refine ⟨n, fun i => c i * (algebraMap K F (algebraMap R K (r i)))⁻¹, y, hy, ?_, fun j => ?_⟩
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hy₁, LinearMap.map_smulₛₗ, smul_smul, hcancel _ _ (hr i)]
      · rw [map_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_smul, comm, hy₂, LinearMap.map_smulₛₗ, smul_smul, hcancel _ _ (hr i)]
    refine ⟨_, h₀, fun w' hw' => hd.eq_of_coord (fun ℓ Λd hΛd => ?_)⟩
    obtain ⟨Λa, hΛa⟩ := ha.coord ℓ
    exact (bij.1 _).unique (key _ _ hw' ℓ Λa Λd hΛa hΛd) (key _ _ h₀ ℓ Λa Λd hΛa hΛd)
  · obtain ⟨n, c, u, rfl⟩ := hd.exists_sum w
    choose φ hφ using fun i => (bij.2 (u i)).exists
    choose r hr y hy hy₁ hy₂ using fun i => (hE _ _).mp (hφ i)
    have h₀ : E' (∑ i, c i • a (φ i)) (∑ i, c i • d (u i)) := by
      rw [hE']
      refine ⟨n, fun i => c i * (algebraMap K F (algebraMap R K (r i)))⁻¹, y, hy, ?_, fun j => ?_⟩
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hy₁, LinearMap.map_smulₛₗ, smul_smul, hcancel _ _ (hr i)]
      · rw [map_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_smul, comm, hy₂, LinearMap.map_smulₛₗ, smul_smul, hcancel _ _ (hr i)]
    refine ⟨_, h₀, fun v' hv' => ha.eq_of_coord (fun ℓ Λa hΛa => ?_)⟩
    obtain ⟨Λd, hΛd⟩ := hd.coord ℓ
    exact (bij.2 _).unique (key _ _ hv' ℓ Λa Λd hΛa hΛd) (key _ _ h₀ ℓ Λa Λd hΛa hΛd)

end Graph

end GlobalTheory.FieldBaseChange
end
end

