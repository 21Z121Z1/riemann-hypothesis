import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0006
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0002

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzGenCpt
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace DiscreteGroups.sglob.DzType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem exists_scale (X : Finset k) :
    ∃ t : kˣ, valuation k (t : k) ≤ 1 ∧ ∀ x ∈ X, valuation k ((t : k) * x) ≤ 1 := by
  classical
  have hne : ∀ x : k, ¬ valuation k x ≤ 1 → x ≠ 0 := fun x h h0 => h (by simp [h0])
  let f : k → kˣ := fun x => if h : valuation k x ≤ 1 then 1 else (Units.mk0 x (hne x h))⁻¹
  have hf1 : ∀ x, valuation k ((f x : kˣ) : k) ≤ 1 := by
    intro x
    by_cases h : valuation k x ≤ 1
    · simp [f, h]
    · simp only [f, dif_neg h, Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀]
      push Not at h
      exact inv_le_one_of_one_le₀ h.le
  have hf2 : ∀ x, valuation k ((f x : kˣ) * x) ≤ 1 := by
    intro x
    by_cases h : valuation k x ≤ 1
    · simpa [f, h] using h
    · simp only [f, dif_neg h, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [inv_mul_cancel₀ (hne x h), map_one]
  refine ⟨∏ x ∈ X, f x, ?_, fun y hy => ?_⟩
  · rw [Units.coe_prod, map_prod]
    exact Finset.prod_le_one' fun x _ => hf1 x
  · rw [Units.coe_prod, ← Finset.mul_prod_erase X (fun x => ((f x : kˣ) : k)) hy, mul_assoc, mul_comm, mul_assoc,
      map_mul]
    have h1 : valuation k (∏ x ∈ X.erase y, ((f x : kˣ) : k)) ≤ 1 := by
      rw [map_prod]; exact Finset.prod_le_one' fun x _ => hf1 x
    calc valuation k (∏ x ∈ X.erase y, ((f x : kˣ) : k)) * valuation k (y * (f y : k))
        ≤ 1 * 1 := by gcongr; rw [mul_comm]; exact hf2 y
      _ = 1 := one_mul 1

theorem isClosed_unipB : IsClosed (unipB k (Fin m) : Set (GL (Fin m) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : ∀ i j : Fin m, Continuous fun g : GL (Fin m) k => (g : Matrix (Fin m) (Fin m) k) i j :=
    fun i j => (Units.continuous_val (M := Matrix (Fin m) (Fin m) k)).matrix_elem i j
  have e : (unipB k (Fin m) : Set (GL (Fin m) k)) =
      (⋂ i : Fin m, ⋂ j : Fin m, {g : GL (Fin m) k | j < i → (g : Matrix (Fin m) (Fin m) k) i j = 0}) ∩
        ⋂ i : Fin m, {g : GL (Fin m) k | (g : Matrix (Fin m) (Fin m) k) i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [e]
  refine (isClosed_iInter fun i => isClosed_iInter fun j => ?_).inter (isClosed_iInter fun i => isClosed_eq (hc i i) continuous_const)
  by_cases hji : j < i
  · simpa [hji] using isClosed_eq (hc i j) continuous_const
  · simp [hji]

theorem diag_conj_apply (t : Fin m → kˣ) (g : GL (Fin m) k) (i j : Fin m) :
    ((diagT k (Fin m) t * g * (diagT k (Fin m) t)⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) i j =
      (t i : k) * (g : Matrix (Fin m) (Fin m) k) i j * ((t j)⁻¹ : kˣ) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp

theorem diag_conj_mem_unipB (t : Fin m → kˣ) {g : GL (Fin m) k} (hg : g ∈ unipB k (Fin m)) :
    diagT k (Fin m) t * g * (diagT k (Fin m) t)⁻¹ ∈ unipB k (Fin m) := by
  refine (mem_unipB _).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [diag_conj_apply, ((mem_unipB _).1 hg).1 i j hij]; simp
  · rw [diag_conj_apply, ((mem_unipB _).1 hg).2 i]; simp

theorem exists_compact_unip (F : Finset (GL (Fin m) k)) (hF : ∀ u ∈ F, u ∈ unipB k (Fin m)) :
    ∃ C : Subgroup (GL (Fin m) k), IsCompact (C : Set (GL (Fin m) k)) ∧ C ≤ unipB k (Fin m) ∧ ∀ u ∈ F, u ∈ C := by
  classical
  obtain ⟨t, ht1, ht⟩ := exists_scale ((F ×ˢ (Finset.univ ×ˢ Finset.univ)).image
    fun x : GL (Fin m) k × Fin m × Fin m => (x.1 : Matrix (Fin m) (Fin m) k) x.2.1 x.2.2)
  let d : GL (Fin m) k := diagT k (Fin m) fun i => t ^ (i : ℕ)
  let C : Subgroup (GL (Fin m) k) := (unipB k (Fin m) ⊓ KO k (Fin m)).map (MulAut.conj d).toMonoidHom
  refine ⟨C, ?_, ?_, fun u hu => ?_⟩
  · rw [Subgroup.coe_map, Subgroup.coe_inf]
    refine (GlobalTheory.SplitFlip.isCompact_KO.inter_left isClosed_unipB).image ?_
    exact (continuous_const.mul continuous_id).mul continuous_const
  · rintro _ ⟨g, hg, rfl⟩
    exact diag_conj_mem_unipB _ hg.1
  · have e : diagT k (Fin m) (fun i => (t ^ (i : ℕ))⁻¹) = d⁻¹ := by rw [← map_inv]; rfl
    have hU : d⁻¹ * u * d ∈ unipB k (Fin m) := by
      have := diag_conj_mem_unipB (fun i => (t ^ (i : ℕ))⁻¹) (hF u hu)
      rwa [e, inv_inv] at this
    have hent : ∀ i j, ((d⁻¹ * u * d : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) i j =
        ((t : k) ^ (i : ℕ))⁻¹ * (u : Matrix (Fin m) (Fin m) k) i j * (t : k) ^ (j : ℕ) := by
      intro i j
      have e2 : d⁻¹ * u * d = diagT k (Fin m) (fun i => (t ^ (i : ℕ))⁻¹) * u *
          (diagT k (Fin m) (fun i => (t ^ (i : ℕ))⁻¹))⁻¹ := by rw [e, inv_inv]
      rw [e2, diag_conj_apply]
      simp
    refine ⟨d⁻¹ * u * d, ⟨hU, mem_KO_of_unip hU fun i j => ?_⟩, ?_⟩
    · rw [hent]
      rcases lt_trichotomy i j with hij | rfl | hij
      · obtain ⟨c, hc⟩ : ∃ c : ℕ, (j : ℕ) = i + (c + 1) := ⟨j - i - 1, by rw [Fin.lt_def] at hij; omega⟩
        have ht0 : (t : k) ^ (i : ℕ) ≠ 0 := pow_ne_zero _ t.ne_zero
        have e3 : ((t : k) ^ (i : ℕ))⁻¹ * (u : Matrix (Fin m) (Fin m) k) i j * (t : k) ^ (j : ℕ) =
            (t : k) ^ c * ((t : k) * (u : Matrix (Fin m) (Fin m) k) i j) := by
          rw [hc, pow_add, pow_succ]
          calc ((t : k) ^ (i : ℕ))⁻¹ * (u : Matrix (Fin m) (Fin m) k) i j * ((t : k) ^ (i : ℕ) * ((t : k) ^ c * t))
              = (((t : k) ^ (i : ℕ))⁻¹ * (t : k) ^ (i : ℕ)) * ((t : k) ^ c * ((t : k) * (u : Matrix (Fin m) (Fin m) k) i j)) := by ring
            _ = _ := by rw [inv_mul_cancel₀ ht0, one_mul]
        rw [e3, map_mul, map_pow]
        exact mul_le_one' (pow_le_one' ht1 c) (ht _ (Finset.mem_image.2 ⟨(u, i, j), by simp [hu], rfl⟩))
      · rw [((mem_unipB _).1 (hF u hu)).2 i, mul_one, inv_mul_cancel₀ (pow_ne_zero _ t.ne_zero), map_one]
      · rw [((mem_unipB _).1 (hF u hu)).1 i j hij]; simp
    · simp [MulAut.conj_apply, d, mul_assoc]

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzGenVec
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.SplitWeil ValuativeRel Matrix

namespace DiscreteGroups.sglob.DzType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

@[simp] theorem blk_eOne (i : Fin m) : blk (eOne m) i = i := rfl

@[simp] theorem eOne_mk (a : Fin m) (i : Fin 1) : eOne m ⟨a, i⟩ = a := rfl

def dl (p : parab k (eOne m)) : ℂˣ := deltaHalf k (fun _ : Fin m => Fin 1) (leviProj k (eOne m) p)

theorem dl_mul (p q : parab k (eOne m)) : dl (p * q) = dl p * dl q := by
  simp [dl, map_mul]

theorem dl_one : dl (1 : parab k (eOne m)) = 1 := by simp [dl]

theorem dl_eq_one {q : parab k (eOne m)} (hq : ∀ a, valuation k (((q : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a) = 1) :
    dl q = 1 := by
  rw [dl, deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => Units.ext ?_
  rw [val_absPow, Units.val_one]
  have hd : ((GeneralLinearGroup.det (leviProj k (eOne m) q a) : kˣ) : k) =
      ((q : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a := by
    simp only [GeneralLinearGroup.val_det_apply, det_unique]
    rfl
  rw [nabs_eq_one k (by rw [hd]; exact hq a)]
  simp

variable (S : Subgroup (GL (Fin m) k))

def InCell (g : GL (Fin m) k) : Prop := ∃ p : parab k (eOne m), ∃ y ∈ S, g = (p : GL (Fin m) k) * wRev k m * y

open Classical in

def cellFun (g : GL (Fin m) k) : ℂ := if h : InCell S g then (dl h.choose : ℂ) else 0

variable {S}

theorem cellFun_eq (hS4 : ∀ y ∈ S, ∀ a, valuation k (((y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) a a) = 1)
    (p : parab k (eOne m)) {y : GL (Fin m) k} (hy : y ∈ S) :
    cellFun S ((p : GL (Fin m) k) * wRev k m * y) = dl p := by
  have h : InCell S ((p : GL (Fin m) k) * wRev k m * y) := ⟨p, y, hy, rfl⟩
  rw [cellFun, dif_pos h]
  obtain ⟨y', hy', e⟩ := h.choose_spec
  set p' := h.choose
  let q : parab k (eOne m) := p'⁻¹ * p
  have hq : ((q : GL (Fin m) k)) = wRev k m * (y' * y⁻¹) * (wRev k m)⁻¹ := by
    have e2 : (p : GL (Fin m) k) = p' * (wRev k m * (y' * y⁻¹) * (wRev k m)⁻¹) :=
      calc (p : GL (Fin m) k) = p * wRev k m * y * y⁻¹ * (wRev k m)⁻¹ := by group
        _ = p' * wRev k m * y' * y⁻¹ * (wRev k m)⁻¹ := by rw [e]
        _ = p' * (wRev k m * (y' * y⁻¹) * (wRev k m)⁻¹) := by group
    simp only [q, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e2]
    group
  have hs : y' * y⁻¹ ∈ S := S.mul_mem hy' (S.inv_mem hy)
  have h1 : dl q = 1 := dl_eq_one fun a => by
    rw [hq, wRev_inv, wRev_conj_apply]
    exact hS4 _ hs _
  have : p = p' * q := by simp [q]
  rw [this, dl_mul, h1, mul_one]

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzPinA
section
noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace DiscreteGroups.sglob.DzPin

theorem pow_eq_pow_of_modEq {M : Type*} [Monoid M] {x : M} {N a b : ℕ} (h : x ^ N = 1)
    (hab : a ≡ b [MOD N]) : x ^ a = x ^ b := by
  have e1 : ∀ c : ℕ, x ^ c = x ^ (c % N) := by
    intro c
    conv_lhs => rw [← Nat.mod_add_div c N, pow_add, pow_mul, h, one_pow, mul_one]
  rw [e1 a, e1 b, show a % N = b % N from hab]

theorem modEq_twist {N t u k b e : ℕ} (htu : t * u ≡ 1 [MOD N]) :
    t * ((u * k + b * e) % N) ≡ k + e * (t * b) [MOD N] := by
  have h1 : t * ((u * k + b * e) % N) ≡ t * (u * k + b * e) [MOD N] :=
    (Nat.mod_modEq _ _).mul_left t
  have h2 : t * (u * k + b * e) = t * u * k + e * (t * b) := by ring
  have h3 : t * u * k + e * (t * b) ≡ 1 * k + e * (t * b) [MOD N] :=
    (htu.mul_right k).add_right _
  rw [one_mul] at h3
  rw [h2] at h1
  exact h1.trans h3

theorem modEq_twist0 {N t u k : ℕ} (htu : t * u ≡ 1 [MOD N]) : t * (u * k % N) ≡ k [MOD N] := by
  have h := modEq_twist (b := 0) (e := 0) (k := k) htu
  simpa using h

theorem exists_eq_pow_of_injective {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    (Ω θ : G →* ℂˣ) (hΩ : Function.Injective Ω) : ∃ k : ℕ, θ = Ω ^ k := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := G)
  have hord : orderOf γ = Fintype.card G :=
    (orderOf_eq_card_of_forall_mem_zpowers hγ).trans Nat.card_eq_fintype_card
  have : NeZero (Fintype.card G) := ⟨Fintype.card_ne_zero⟩
  have h1 : IsPrimitiveRoot γ (Fintype.card G) := hord ▸ IsPrimitiveRoot.orderOf γ
  have hprim : IsPrimitiveRoot ((Ω γ : ℂˣ) : ℂ) (Fintype.card G) :=
    (h1.map_of_injective hΩ).map_of_injective (f := Units.coeHom ℂ) Units.val_injective
  have hθ : ((θ γ : ℂˣ) : ℂ) ^ Fintype.card G = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one hθ
  refine ⟨k, MonoidHom.ext fun z => Units.ext ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, γ ^ j = z := by
    have hz := hγ z
    rw [← mem_powers_iff_mem_zpowers] at hz
    exact hz
  rw [MonoidHom.pow_apply, map_pow, map_pow, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, ← hk, ← pow_mul, ← pow_mul, mul_comm]

theorem dsum_eq_of_pow_eq {p f : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Fintype k]
    [Algebra (ZMod p) k] {A : Type*} [CommRing A] [IsDedekindDomain A] {Q : HeightOneSpectrum A}
    (D : Stick.GSDatum p f k A Q) {a₁ a₂ a₃ a₄ r : ℕ} (h₁ : a₁ < p ^ f - 1) (h₂ : a₂ < p ^ f - 1)
    (h₃ : a₃ < p ^ f - 1) (h₄ : a₄ < p ^ f - 1) (hr : 0 < r)
    (h : (D.g a₁ * D.g a₂) ^ r = (D.g a₃ * D.g a₄) ^ r) :
    Stick.dsum p a₁ + Stick.dsum p a₂ = Stick.dsum p a₃ + Stick.dsum p a₄ := by
  have hv := congrArg Q.intValuation h
  simp only [map_pow, map_mul, D.val_g h₁, D.val_g h₂, D.val_g h₃, D.val_g h₄, ← pow_add,
    ← pow_mul] at hv
  have h0 : 0 < Q.intValuation (D.ζ - 1) := zero_lt_iff.2 D.val_ζ_sub_one_ne_zero
  have h1 : Q.intValuation (D.ζ - 1) < 1 := (Q.intValuation_lt_one_iff_mem _).2 D.ζ_sub_one_mem
  have := (pow_right_strictAnti₀ h0 h1).injective hv
  exact Nat.eq_of_mul_eq_mul_right hr this

theorem addChar_apply_eq_pow {g : ℕ} [Fact g.Prime] (ψ₀ : AddChar (ZMod g) Circle) (y : ZMod g) :
    ((ψ₀ y : Circle) : ℂ) = ((ψ₀ 1 : Circle) : ℂ) ^ y.val := by
  have h : y = y.val • (1 : ZMod g) := by rw [nsmul_one, ZMod.natCast_zmod_val]
  conv_lhs => rw [h, AddChar.map_nsmul_eq_pow]
  rw [Circle.coe_pow]

theorem sum_units_eq {K : Type*} [Field K] [Fintype K] [DecidableEq K] (F : K → ℂ) (hF : F 0 = 0) :
    ∑ u : Kˣ, F u = ∑ x : K, F x := by
  rw [← Finset.sum_erase Finset.univ hF,
    Finset.sum_subtype (Finset.univ.erase (0 : K)) (p := fun x => x ≠ 0) (by simp) F]
  exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)

theorem gs_eq {g : ℕ} [Fact g.Prime] (ψ₀ : AddChar (ZMod g) Circle) {K : Type*} [Field K]
    [Fintype K] [Algebra (ZMod g) K] {A : Type*} [CommRing A] (Φ : A →+* ℂ) (ω : MulChar K A)
    (ζ : A) (hζ : ζ ^ g = 1) (hΦζ : Φ ζ = ((ψ₀ 1 : Circle) : ℂ)) (η : Kˣ →* ℂˣ) (a : ℕ)
    (hη : ∀ z : Kˣ, ((η z : ℂˣ) : ℂ) = Φ (ω z) ^ a) :
    (∑ᶠ z : Kˣ, (((η⁻¹) z : ℂˣ) : ℂ) * ((ψ₀ (Algebra.trace (ZMod g) K (z : K)) : Circle) : ℂ)) =
      Φ (gaussSum (ω ^ a)⁻¹ (Stick.psi g K ζ hζ)) := by
  classical
  rw [finsum_eq_sum_of_fintype, gaussSum, map_sum]
  rw [← sum_units_eq (fun x => Φ ((ω ^ a)⁻¹ x * Stick.psi g K ζ hζ x))
    (by rw [MulChar.map_zero, zero_mul, map_zero])]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [map_mul, Stick.psi_apply, map_pow, hΦζ, ← addChar_apply_eq_pow, MulChar.inv_apply',
    ← Units.val_inv_eq_inv_val, MulChar.pow_apply_coe, map_pow, ← hη, MonoidHom.inv_apply,
    ← map_inv]

end DiscreteGroups.sglob.DzPin
end
end

