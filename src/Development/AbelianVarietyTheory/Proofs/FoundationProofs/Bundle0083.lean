import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0067
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixPrimeDetCosetRepresentatives
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem exists_right_div_upperTriangular_prime_det (q : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (k : ℕ)
    (h1 : (q : ℤ) ∣ m 0 1 - m 0 0 * k) (h2 : (q : ℤ) ∣ m 1 1 - m 1 0 * k) :
    ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨c, hc⟩ := h2
  refine ⟨!![m 0 0, a; m 1 0, c], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination -ha | linear_combination ha | linear_combination -hc

theorem cosetPrimeDet : ∀ (q : ℕ), q.Prime → ∀ m : Matrix (Fin 2) (Fin 2) ℤ, m.det = q →
    (∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![(q : ℤ), 0; 0, 1] = m) ∨
    ∃ k : ℕ, k < q ∧ ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := by
  intro q hq m hdet
  have := Fact.mk hq
  have : NeZero q := ⟨hq.ne_zero⟩
  rw [Matrix.det_fin_two] at hdet
  have hd : ((m 0 0 : ℤ) : ZMod q) * (m 1 1 : ℤ) - ((m 0 1 : ℤ) : ZMod q) * (m 1 0 : ℤ) = 0 := by
    have : ((m 0 0 * m 1 1 - m 0 1 * m 1 0 : ℤ) : ZMod q) = 0 := by
      rw [hdet]; simp
    push_cast at this
    exact this

  have dv : ∀ x : ℤ, (x : ZMod q) = 0 → (q : ℤ) ∣ x := fun x hx =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd x q).mp hx

  have fin : ∀ t : ZMod q, ((m 0 1 : ℤ) : ZMod q) - (m 0 0 : ℤ) * t = 0 →
      ((m 1 1 : ℤ) : ZMod q) - (m 1 0 : ℤ) * t = 0 →
      ∃ k : ℕ, k < q ∧ ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := by
    intro t ht1 ht2
    refine ⟨t.val, ZMod.val_lt t, exists_right_div_upperTriangular_prime_det q m t.val (dv _ ?_) (dv _ ?_)⟩
    · push_cast; rw [ZMod.natCast_zmod_val]; exact ht1
    · push_cast; rw [ZMod.natCast_zmod_val]; exact ht2
  by_cases ha : ((m 0 0 : ℤ) : ZMod q) = 0
  · by_cases hc : ((m 1 0 : ℤ) : ZMod q) = 0
    ·
      left
      obtain ⟨x, hx⟩ := dv _ ha
      obtain ⟨y, hy⟩ := dv _ hc
      refine ⟨!![x, m 0 1; y, m 1 1], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | linear_combination -hx | linear_combination hx | linear_combination -hy
    · right
      have h01 : ((m 0 1 : ℤ) : ZMod q) = 0 := by
        have : ((m 0 1 : ℤ) : ZMod q) * (m 1 0 : ℤ) = 0 := by
          linear_combination -hd + ((m 1 1 : ℤ) : ZMod q) * ha
        exact (mul_eq_zero.mp this).resolve_right hc
      have hinv := mul_inv_cancel₀ hc
      refine fin (((m 1 1 : ℤ) : ZMod q) * ((m 1 0 : ℤ) : ZMod q)⁻¹) ?_ ?_
      · rw [ha, h01]; ring
      · linear_combination -((m 1 1 : ℤ) : ZMod q) * hinv
  · right
    have hinv := mul_inv_cancel₀ ha
    refine fin (((m 0 1 : ℤ) : ZMod q) * ((m 0 0 : ℤ) : ZMod q)⁻¹) ?_ ?_
    · linear_combination -((m 0 1 : ℤ) : ZMod q) * hinv
    · linear_combination ((m 0 0 : ℤ) : ZMod q)⁻¹ * hd - ((m 1 1 : ℤ) : ZMod q) * hinv

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelSuccReduce
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem exp_pow_reduce (l n v : ℕ) (hl : l ≠ 0) :
    Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / ((l : ℂ) ^ (n + 1))) ^ l =
      Complex.exp (2 * Real.pi * Complex.I * ((v % l ^ n : ℕ) : ℂ) / ((l : ℂ) ^ n)) := by
  rw [← Complex.exp_nat_mul]
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  have hv : (v : ℂ) = ((v % l ^ n : ℕ) : ℂ) + (l : ℂ) ^ n * ((v / l ^ n : ℕ) : ℂ) := by
    exact_mod_cast (Nat.mod_add_div v (l ^ n)).symm
  have e : (l : ℂ) * (2 * Real.pi * Complex.I * (v : ℂ) / ((l : ℂ) ^ (n + 1))) =
      2 * Real.pi * Complex.I * ((v % l ^ n : ℕ) : ℂ) / ((l : ℂ) ^ n) +
        ((v / l ^ n : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hv]; field_simp; ring
  rw [e, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem kum_succ_reduce : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ (n + 1))), Kum X l (n + 1) x χ →
      Kum X l n x (fun δ => ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) (χ δ)) := by
  intro Ω _ _ ε X l _ n x χ ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab⟩, hrel⟩
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hl0⟩
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl0⟩
  refine ⟨f, fun z => a z ^ l, fun z => b z ^ l, M, hM, ?_, ⟨ha.pow l, hb.pow l, ?_, ?_⟩, ?_⟩
  · have h := AdicCompletion.transitionMap_comp_eval_apply (idl l) (X.Kl l) (Nat.le_succ n) x
    change x.val n = _
    rw [← h]
    change AdicCompletion.transitionMap (idl l) (X.Kl l) (Nat.le_succ n) (AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x) = _
    rw [hx]
    rfl
  · intro h
    apply hb0
    rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq] at h ⊢
    exact h.mono fun z hz => (pow_eq_zero_iff hl0).1 hz
  · have e1 : ((fun z => b z ^ l : ℂ → ℂ) : Mero) = (b : Mero) ^ l := Filter.Germ.coe_pow b l
    have e2 : ((fun z => a z ^ l : ℂ → ℂ) : Mero) = (a : Mero) ^ l := Filter.Germ.coe_pow a l
    rw [e1, e2, ← pow_mul, ← pow_mul, ← pow_succ', hab]
  · intro δ hδ z hz
    have h1 := congrArg (fun t : ℂ => t ^ l) (hrel δ hδ z hz)
    simp only [mul_pow] at h1
    rw [exp_pow_reduce l n _ hl0] at h1
    have hv : (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) (χ δ)).val = (χ δ).val % l ^ n := by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
    rw [hv]
    simpa only [mul_pow, mul_assoc] using h1

end GlobalTheory.KZ.H3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePr
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_mono (χ : kˣ →* ℂˣ) (x y : k) (h : valuation k y ≤ valuation k x) (hx : Triv χ x) :
    Triv χ y := fun u hu hle => hx u hu (hle.trans h)

theorem triv_add (χ : kˣ →* ℂˣ) (x y : k) (hx : Triv χ x) (hy : Triv χ y) : Triv χ (x + y) := by
  intro u hu hle
  rcases le_total (valuation k x) (valuation k y) with h | h
  · exact hy u hu (hle.trans ((Valuation.map_add _ x y).trans (max_le h le_rfl)))
  · exact hx u hu (hle.trans ((Valuation.map_add _ x y).trans (max_le le_rfl h)))

theorem triv_zero (χ : kˣ →* ℂˣ) : Triv χ 0 := by
  intro u _ hle
  have : (u : k) - 1 = 0 := by simpa using hle
  have hu : u = 1 := Units.ext (by simpa [sub_eq_zero] using this)
  simp [hu]

theorem triv_neg (χ : kˣ →* ℂˣ) (x : k) (hx : Triv χ x) : Triv χ (-x) :=
  triv_mono χ x (-x) (by rw [Valuation.map_neg]) hx

theorem triv_mul (χ η : kˣ →* ℂˣ) (x : k) (h1 : Triv χ x) (h2 : Triv η x) : Triv (χ * η) x := by
  intro u hu hle
  simp [h1 u hu hle, h2 u hu hle]

theorem triv_inv (χ : kˣ →* ℂˣ) (x : k) (h : Triv χ x) : Triv χ⁻¹ x := by
  intro u hu hle
  simp [h u hu hle]

def trivSubgroup (χ : kˣ →* ℂˣ) : AddSubgroup k where
  carrier := {x | Triv χ x}
  add_mem' := fun {a b} ha hb => triv_add χ a b ha hb
  zero_mem' := triv_zero χ
  neg_mem' := fun {a} ha => triv_neg χ a ha

theorem triv_mem_nhds (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : {x : k | Triv χ x} ∈ nhds (0 : k) := by
  have hemb : Topology.IsEmbedding (Units.val : kˣ → k) := Units.isEmbedding_val₀
  obtain ⟨U, hUo, hU⟩ := hemb.isOpen_iff.mp hχ
  have h1 : (1 : k) ∈ U := by
    have : (1 : kˣ) ∈ (Units.val ⁻¹' U) := by rw [hU]; simp
    simpa using this
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_iff' (R := k)).mp (hUo.mem_nhds h1)
  rw [IsValuativeTopology.mem_nhds_zero_iff]
  refine ⟨γ, fun x hx u _ hle => ?_⟩
  have hmem : (u : k) ∈ U := hγ (lt_of_le_of_lt hle hx)
  have : u ∈ (Units.val ⁻¹' U) := hmem
  rw [hU] at this
  simpa using this

theorem triv_isOpen_isClosed (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    IsOpen {x : k | Triv χ x} ∧ IsClosed {x : k | Triv χ x} := by
  have ho : IsOpen ((trivSubgroup χ : AddSubgroup k) : Set k) :=
    AddSubgroup.isOpen_of_mem_nhds _ (triv_mem_nhds χ hχ)
  exact ⟨ho, AddSubgroup.isClosed_of_isOpen _ ho⟩

theorem ev_of_val (χ : kˣ →* ℂˣ) (x : k) (h : valuation k x = 1) :
    ev χ x = (χ (Units.mk0 x (fun h0 => by simp [h0] at h)) : ℂ) := by
  simp [ev, h]

theorem ev_mul (χ : kˣ →* ℂˣ) (x y : k) (hx : valuation k x = 1) (hy : valuation k y = 1) :
    ev χ (x * y) = ev χ x * ev χ y := by
  have hxy : valuation k (x * y) = 1 := by simp [hx, hy]
  rw [ev_of_val χ _ hxy, ev_of_val χ _ hx, ev_of_val χ _ hy, ← Units.val_mul, ← map_mul]
  congr 3
  ext
  simp

theorem ev_congr (χ : kˣ →* ℂˣ) (x y : k) (hx : valuation k x = 1) (hy : valuation k y = 1)
    (h : Triv χ (x - y)) : ev χ x = ev χ y := by
  have hx0 : x ≠ 0 := fun h0 => by simp [h0] at hx
  have hy0 : y ≠ 0 := fun h0 => by simp [h0] at hy
  set u : kˣ := Units.mk0 x hx0 / Units.mk0 y hy0 with hu
  have huv : (u : k) = x / y := by simp [hu]
  have hu1 : valuation k (u : k) = 1 := by rw [huv, map_div₀, hx, hy, div_one]
  have hsub : (u : k) - 1 = (x - y) / y := by rw [huv]; field_simp
  have hle : valuation k ((u : k) - 1) ≤ valuation k (x - y) := by
    rw [hsub, map_div₀, hy, div_one]
  have hχu : χ u = 1 := h u hu1 hle
  have hxe : Units.mk0 x hx0 = u * Units.mk0 y hy0 := by rw [hu]; simp
  rw [ev_of_val χ _ hx, ev_of_val χ _ hy, hxe, map_mul, hχu, one_mul]

theorem ev_of_triv_one (χ : kˣ →* ℂˣ) (x : k) (h : Triv χ 1) : ev χ x = 1 := by
  by_cases hx : valuation k x = 1
  · rw [ev_of_val χ _ hx]
    have hx0 : x ≠ 0 := fun h0 => by simp [h0] at hx
    have hle : valuation k ((Units.mk0 x hx0 : k) - 1) ≤ valuation k (1 : k) := by
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> simp [hx]
    rw [h _ (by simpa using hx) hle]
    simp
  · simp [ev, hx]

end

theorem triv_ev_props : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ (χ : kˣ →* ℂˣ) (x y : k), valuation k y ≤ valuation k x → Triv χ x → Triv χ y) ∧ (∀ (χ : kˣ →* ℂˣ) (x y : k), Triv χ x → Triv χ y → Triv χ (x + y)) ∧ (∀ χ : kˣ →* ℂˣ, Triv χ 0) ∧ (∀ (χ η : kˣ →* ℂˣ) (x : k), Triv χ x → Triv η x → Triv (χ * η) x) ∧ (∀ (χ : kˣ →* ℂˣ) (x : k), Triv χ x → Triv χ⁻¹ x) ∧ (∀ χ : kˣ →* ℂˣ, IsSmoothChar χ → IsOpen {x : k | Triv χ x} ∧ IsClosed {x : k | Triv χ x}) ∧ (∀ (χ : kˣ →* ℂˣ) (x y : k), valuation k x = 1 → valuation k y = 1 → ev χ (x * y) = ev χ x * ev χ y) ∧ (∀ (χ : kˣ →* ℂˣ) (x y : k), valuation k x = 1 → valuation k y = 1 → Triv χ (x - y) → ev χ x = ev χ y) ∧ (∀ (χ : kˣ →* ℂˣ) (x : k), Triv χ 1 → ev χ x = 1) := by
  intro k _ _ _ _
  exact ⟨fun χ x y h hx => triv_mono χ x y h hx, fun χ x y => triv_add χ x y, triv_zero,
    fun χ η x => triv_mul χ η x, fun χ x => triv_inv χ x, fun χ hχ => triv_isOpen_isClosed χ hχ,
    fun χ x y => ev_mul χ x y, fun χ x y => ev_congr χ x y, fun χ x => ev_of_triv_one χ x⟩

end GlobalTheory.PsType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Klm
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Tower.klm (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) : X.Kl l →ₗ[ℤ_[l]] X.Kl l :=
  LinearMap.baseChange ℤ_[l] (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom)))

def Tower.Lev (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (M : ℕ) : Submodule ℤ_[l] (X.Kl l) :=
  Submodule.span ℤ_[l] {x | ∃ f : X.Kˣ, (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (f : X.K) = f) ∧
    x = (1 : ℤ_[l]) ⊗ₜ Additive.ofMul f}

end GlobalTheory.KZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KmapSubMemOfASet
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.GalCont

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem exp_inj (X : Tower Ω ε) : Function.Injective X.exp :=
  X.exp.toRingHom.injective

theorem gal_eq_of_coeff (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K)
    (h : ∀ r, s ((X.exp f).coeff r) = (X.exp f).coeff r) : X.gal s f = f := by
  apply exp_inj X
  ext r
  rw [X.gal_exp]
  exact h r

theorem coeff_alg (c : Ω) (r : ℚ) :
    ((algebraMap Ω (HahnSeries ℚ Ω)) c).coeff r = if r = 0 then c else 0 := by
  rw [HahnSeries.algebraMap_apply']
  simp [PowerSeries.algebraMap_apply, HahnSeries.coeff_single, eq_comm]

theorem gal_algebraMap (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) (hc : s c = c) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K c := by
  apply gal_eq_of_coeff
  intro r
  rw [AlgHom.commutes, coeff_alg]
  split_ifs
  · exact hc
  · exact map_zero s

theorem gal_j (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) : X.gal s X.jK = X.jK := by
  apply gal_eq_of_coeff
  intro r
  obtain ⟨n, hn⟩ := X.j_exp.2.2 r
  rw [hn, map_intCast]

def fixSet (X : Tower Ω ε) : Set X.K :=
  {f | ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) → X.gal s f = f}

def fixField (X : Tower Ω ε) : IntermediateField Ω X.K where
  carrier := fixSet X
  mul_mem' := by
    classical
    rintro a b ⟨E, hE⟩ ⟨F, hF⟩
    refine ⟨E ∪ F, fun s hs => ?_⟩
    rw [map_mul, hE s (fun x hx => hs x (Finset.mem_union_left _ hx)),
      hF s (fun x hx => hs x (Finset.mem_union_right _ hx))]
  add_mem' := by
    classical
    rintro a b ⟨E, hE⟩ ⟨F, hF⟩
    refine ⟨E ∪ F, fun s hs => ?_⟩
    rw [map_add, hE s (fun x hx => hs x (Finset.mem_union_left _ hx)),
      hF s (fun x hx => hs x (Finset.mem_union_right _ hx))]
  algebraMap_mem' c := ⟨{c}, fun s hs => gal_algebraMap X s c (hs c (Finset.mem_singleton_self c))⟩
  inv_mem' := by
    rintro a ⟨E, hE⟩
    exact ⟨E, fun s hs => by rw [map_inv₀, hE s hs]⟩

theorem adjoin_le_fix (X : Tower Ω ε) : IntermediateField.adjoin Ω {X.jK} ≤ fixField X := by
  rw [IntermediateField.adjoin_simple_le_iff]
  exact ⟨∅, fun s _ => gal_j X s⟩

theorem fix_fin (X : Tower Ω ε) (f : X.K) :
    ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) → X.gal s f = f := by
  classical
  obtain ⟨p, hp0, hpf⟩ := X.alg_j f
  obtain ⟨q, hq⟩ : ∃ q : Polynomial X.K, q = p.map (algebraMap (IntermediateField.adjoin Ω {X.jK}) X.K) := ⟨_, rfl⟩
  have hq0 : q ≠ 0 := hq ▸ (Polynomial.map_ne_zero_iff (algebraMap (IntermediateField.adjoin Ω {X.jK}) X.K).injective).2 hp0
  have hqf : q.eval f = 0 := by
    rw [hq, Polynomial.eval_map_algebraMap]; exact hpf
  have hcoef : ∀ i, ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) →
      X.gal s (q.coeff i) = q.coeff i := by
    intro i
    rw [hq, Polynomial.coeff_map]
    exact adjoin_le_fix X (p.coeff i).2
  choose Ec hEc using hcoef
  have hex : ∀ g : X.K, g ≠ f → ∃ r, (X.exp g).coeff r ≠ (X.exp f).coeff r := by
    intro g hg
    by_contra h
    push_neg at h
    exact hg (exp_inj X (HahnSeries.ext (funext h)))
  choose rr hrr using hex
  let E1 : Finset Ω := q.support.biUnion Ec
  let E2 : Finset Ω := q.roots.toFinset.image
    (fun g => if h : g = f then 0 else (X.exp f).coeff (rr g h))
  refine ⟨E1 ∪ E2, fun s hs => ?_⟩
  have hmap : q.map (X.gal s).toRingHom = q := by
    ext i
    rw [Polynomial.coeff_map]
    by_cases hi : i ∈ q.support
    · exact hEc i s (fun x hx => hs x (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨i, hi, hx⟩)))
    · rw [Polynomial.notMem_support_iff.1 hi, map_zero]
  have hroot : X.gal s f ∈ q.roots := by
    rw [Polynomial.mem_roots hq0, Polynomial.IsRoot.def]
    have := Polynomial.eval₂_hom (X.gal s).toRingHom f (p := q)
    rw [← Polynomial.eval_map, hmap] at this
    simpa [hqf] using this
  by_contra hne
  have hmem : (X.exp f).coeff (rr _ hne) ∈ E2 :=
    Finset.mem_image.2 ⟨X.gal s f, Multiset.mem_toFinset.2 hroot, by rw [dif_neg hne]⟩
  apply hrr _ hne
  rw [X.gal_exp]
  exact hs _ (Finset.mem_union_right _ hmem)

theorem kmap_sub_mem_of_ASet (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (a : X.Khat l) (ha : a ∈ X.ASet l)
    (n : ℕ) : ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) →
      X.kmap l (X.gal s) a - a ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  obtain ⟨f, -, hf⟩ := ha n
  obtain ⟨E, hE⟩ := fix_fin X (f : X.K)
  refine ⟨E, fun s hs => ?_⟩
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _), LinearMap.mem_ker,
    map_sub, sub_eq_zero]
  rw [AdicCompletion.eval_apply, AdicCompletion.eval_apply]
  change (AdicCompletion.map _ _ a).val n = a.val n
  rw [AdicCompletion.map_val_apply, ← AdicCompletion.eval_apply, hf]
  rw [Tower.cls, LinearMap.reduceModIdeal_apply, LinearMap.baseChange_tmul]
  have hu : Units.map (X.gal s).toMonoidHom f = f := Units.ext (hE s hs)
  congr 2

theorem cyc_sub_one_mem [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) :
    ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) →
      ((cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) - 1) ∈ (idl l) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨∅, fun _ _ => by simp⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero⟩
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  refine ⟨{ζ}, fun s hs => ?_⟩
  have h1 := cyclotomicCharacter.spec l (n := n) s.toRingEquiv ζ hζ.pow_eq_one
  have hsz : s.toRingEquiv ζ = ζ := hs ζ (Finset.mem_singleton_self ζ)
  rw [hsz] at h1
  set v := (cyclotomicCharacter Ω l s.toRingEquiv).val.toZModPow n with hv
  have h2 : v = 1 := by
    have hlt : 1 < l ^ n := Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt
    have hval : v.val = 1 := hζ.pow_inj (ZMod.val_lt v) hlt (by rw [pow_one]; exact h1.symm)
    rw [← ZMod.natCast_zmod_val v, hval, Nat.cast_one]
  rw [idl, Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, ← hv, h2,
    map_one, sub_self]

theorem kmap_sub_mem_A (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (c : X.Khat l) (hc : c ∈ X.A l) (n : ℕ) :
    ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) →
      X.kmap l (X.gal s) c - c ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  classical
  induction hc using Submodule.span_induction with
  | mem a ha => exact kmap_sub_mem_of_ASet X l a ha n
  | zero => exact ⟨∅, fun s _ => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨E, hE⟩ := ha
    obtain ⟨F, hF⟩ := hb
    refine ⟨E ∪ F, fun s hs => ?_⟩
    have := Submodule.add_mem _ (hE s fun x hx => hs x (Finset.mem_union_left _ hx))
      (hF s fun x hx => hs x (Finset.mem_union_right _ hx))
    rw [map_add]
    convert this using 1
    abel
  | smul r a _ ha =>
    obtain ⟨E, hE⟩ := ha
    refine ⟨E, fun s hs => ?_⟩
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ r (hE s hs)

theorem galB_sub_mem_of_Pol [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (l w : ℕ) [Fact l.Prime] (b : X.Fn l)
    (hb : b ∈ X.Pol l w) (n : ℕ) :
    ∃ E : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E, s x = x) →
      ∀ u, (X.galB l s b - b) u ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  classical
  obtain ⟨c, hcA, hbc⟩ := hb
  choose Ec hEc using fun i => kmap_sub_mem_A X l (c i) (hcA i) n
  obtain ⟨Ez, hEz⟩ := cyc_sub_one_mem (Ω := Ω) l n
  refine ⟨Ez ∪ Finset.univ.biUnion Ec, fun s hs u => ?_⟩
  have hχ := hEz s (fun x hx => hs x (Finset.mem_union_left _ hx))
  have hk : ∀ i, X.kmap l (X.gal s) (c i) - c i ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) :=
    fun i => hEc i s (fun x hx => hs x (Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hx⟩)))
  set χ := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hχdef
  have hgal : X.galB l s b u = X.kmap l (X.gal s) (b ![u 0, χ * u 1]) := rfl
  rw [Pi.sub_apply, hgal, hbc, hbc, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  simp only [map_smul, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hpow : χ ^ (w - (i : ℕ)) - 1 ∈ (idl l) ^ n := by
    obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow χ 1 (w - (i : ℕ))
    rw [one_pow] at hd
    rw [hd]
    exact Ideal.mul_mem_right _ _ hχ
  have heq : (u 0 ^ (i : ℕ) * (χ * u 1) ^ (w - (i : ℕ))) • X.kmap l (X.gal s) (c i) -
      (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i =
      (u 0 ^ (i : ℕ) * (χ * u 1) ^ (w - (i : ℕ))) • (X.kmap l (X.gal s) (c i) - c i) +
      ((u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) * (χ ^ (w - (i : ℕ)) - 1)) • c i := by
    rw [mul_pow]
    module
  rw [heq]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hk i))
    (Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ hpow) Submodule.mem_top)

theorem galB_cont : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ b ∈ X.B N l w, ∀ n : ℕ,
    ∃ E0 : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s x = x) → ∀ u,
      (X.galB l s b - b) u ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l)) := by
  intro Ω _ _ _ ε X _ _ N l w _ _ _ _ _ b hb n
  classical
  induction hb using Submodule.span_induction with
  | mem b hb => exact galB_sub_mem_of_Pol X l w b hb.1 n
  | zero => exact ⟨∅, fun s _ u => by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨E, hE⟩ := ha
    obtain ⟨F, hF⟩ := hb
    refine ⟨E ∪ F, fun s hs u => ?_⟩
    have := Submodule.add_mem _ (hE s (fun x hx => hs x (Finset.mem_union_left _ hx)) u)
      (hF s (fun x hx => hs x (Finset.mem_union_right _ hx)) u)
    rw [map_add]
    convert this using 1
    simp only [LinearMap.sub_apply, Pi.add_apply, Pi.sub_apply]
    abel
  | smul r a _ ha =>
    obtain ⟨E, hE⟩ := ha
    refine ⟨E, fun s hs u => ?_⟩
    have := Submodule.smul_mem _ r (hE s hs u)
    rw [map_smul]
    convert this using 1
    simp only [LinearMap.sub_apply, Pi.smul_apply, Pi.sub_apply, smul_sub]

end GlobalTheory.KZ.GalCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainCharacterGaloisInvariantClassStatement
section
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_cochain_character_galoisInvariant_class : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 →
  α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b → ∀ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η →
  (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) →
  ∃ θ : Ω, θ ≠ 0 ∧ θ ^ N ∈ IntermediateField.adjoin K {α, β} ∧
    (∀ g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup, η g = kum ζ θ g) ∧
    ∀ s : Ω ≃ₐ[K] Ω, ∃ u ∈ IntermediateField.adjoin K {α, β}, u ≠ 0 ∧ s (θ ^ N) = θ ^ N * u ^ N := by
  first | exact @GlobalTheory.eta_kummer_galoisInvariant | exact GlobalTheory.eta_kummer_galoisInvariant | (intros; apply GlobalTheory.eta_kummer_galoisInvariant <;> assumption)
end

