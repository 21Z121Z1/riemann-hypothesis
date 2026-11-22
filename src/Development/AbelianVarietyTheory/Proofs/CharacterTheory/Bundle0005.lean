import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsPermOfSumMinEqPositiveFamily
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory

theorem sum_min_succ_eq_add_card {d : ℕ} (e : Fin d → ℕ) (j : ℕ) :
    ∑ i, min (j + 1) (e i) = ∑ i, min j (e i) + (Finset.univ.filter (fun i => j < e i)).card := by
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> omega

theorem card_gt_eq_card_eq_add_card_gt {d : ℕ} (e : Fin d → ℕ) (j : ℕ) :
    (Finset.univ.filter (fun i => j < e i)).card =
      (Finset.univ.filter (fun i => e i = j + 1)).card +
        (Finset.univ.filter (fun i => j + 1 < e i)).card := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> omega

theorem exists_equiv_of_sum_min_eq : ∀ (d d' : ℕ) (e : Fin d → ℕ) (e' : Fin d' → ℕ),
    (∀ i, 0 < e i) → (∀ i, 0 < e' i) → (∀ j : ℕ, ∑ i, min j (e i) = ∑ i, min j (e' i)) →
    ∃ σ : Fin d ≃ Fin d', ∀ i, e' (σ i) = e i := by
  intro d d' e e' he he' h
  have h1 : ∀ j, (Finset.univ.filter (fun i => j < e i)).card =
      (Finset.univ.filter (fun i => j < e' i)).card := by
    intro j
    have a := sum_min_succ_eq_add_card e j
    have b := sum_min_succ_eq_add_card e' j
    have c := h j
    have c' := h (j + 1)
    omega
  have h2 : ∀ j, Fintype.card {i // e i = j} = Fintype.card {i // e' i = j} := by
    intro j
    rw [Fintype.card_subtype, Fintype.card_subtype]
    rcases j with _ | j
    · rw [Finset.filter_false_of_mem (fun i _ => (he i).ne'),
        Finset.filter_false_of_mem (fun i _ => (he' i).ne')]
      simp
    · have a := card_gt_eq_card_eq_add_card_gt e j
      have b := card_gt_eq_card_eq_add_card_gt e' j
      have c := h1 j
      have c' := h1 (j + 1)
      omega
  exact ⟨Equiv.ofFiberEquiv (f := e) (g := e') (fun j => Fintype.equivOfCardEq (h2 j)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsStandardUnipotentRadicalBijOnNilradical
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL.UnipNilRad

variable {F : Type} [Field F]

def lowSub (F : Type) [Field F] (d a : ℕ) : Submodule F (Fin d → F) :=
  LinearMap.ker (LinearMap.funLeft F F (Subtype.val : {i : Fin d // a ≤ i.val} → Fin d))

def unip {d : ℕ} (A : Submodule F (Fin d → F)) : Subgroup (GL (Fin d) F) where
  carrier := {u | Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1 ∈ nilRad A}
  one_mem' := by
    refine ⟨fun x => ?_, fun x _ => ?_⟩ <;> simp
  mul_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · have := A.add_mem (hu1 (Matrix.toLin' (v : Matrix (Fin d) (Fin d) F) x)) (hv1 x)
      simpa [Matrix.toLin'_mul] using this
    · have h1 := hu2 x hx
      have h2 := hv2 x hx
      simp only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1 h2 ⊢
      rw [Units.val_mul, Matrix.toLin'_mul, LinearMap.comp_apply, h2, h1]
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    have e1 : ∀ x, Matrix.toLin' (u : Matrix (Fin d) (Fin d) F)
        (Matrix.toLin' ((u⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) x) = x := fun x => by
      rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.toLin'_one, LinearMap.id_apply]
    have e2 : ∀ x, Matrix.toLin' ((u⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F)
        (Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) x) = x := fun x => by
      rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.toLin'_one, LinearMap.id_apply]
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · have := A.neg_mem (hu1 (Matrix.toLin' ((u⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) x))
      rw [LinearMap.sub_apply, e1, neg_sub] at this
      exact this
    · have h1 := hu2 x hx
      simp only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1 ⊢
      conv_lhs => rw [← h1]
      exact e2 x

open Polynomial in
variable {F : Type} [Field F] in
private lemma card_fin_le_val_eq_sub (d a : ℕ) : Fintype.card {i : Fin d // a ≤ i.val} = d - a := by
  rw [Fintype.card_subtype, ← Finset.card_map Fin.valEmbedding, ← Nat.card_Ico a d]
  congr 1
  ext n
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply, Finset.mem_Ico]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨hi, i.isLt⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨n, h2⟩, h1, rfl⟩

open Polynomial in
variable {F : Type} [Field F] in
private lemma finrank_lowSub_of_le {d a : ℕ} (had : a ≤ d) :
    Module.finrank F (_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a) = a := by
  have hs := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.funLeft F F (Subtype.val : {i : Fin d // a ≤ i.val} → Fin d))
  rw [LinearMap.range_eq_top.mpr
    (LinearMap.funLeft_surjective_of_injective _ _ _ Subtype.val_injective),
    finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    card_fin_le_val_eq_sub, Fintype.card_fin] at hs
  rw [_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub]
  omega

open Polynomial in
variable {F : Type} [Field F] in
private lemma mem_lowSub_iff_apply_eq_zero {d a : ℕ} (v : Fin d → F) :
    v ∈ _root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a ↔ ∀ i : Fin d, a ≤ i.val → v i = 0 := by
  rw [_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub, LinearMap.mem_ker]
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i.1 i.2

open Polynomial in
variable {F : Type} [Field F] in
private lemma toLin'_mem_nilRad_lowSub_iff {d a : ℕ} (N : Matrix (Fin d) (Fin d) F) :
    Matrix.toLin' N ∈ _root_.GlobalTheory.CuspGL.nilRad (_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a) ↔
      ∀ i j : Fin d, N i j = 0 ∨ (i.val < a ∧ a ≤ j.val) := by
  show ((∀ x, Matrix.toLin' N x ∈ _) ∧ ∀ x ∈ _, Matrix.toLin' N x = 0) ↔ _
  simp only [Matrix.toLin'_apply, mem_lowSub_iff_apply_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩ i j
    by_cases hi : a ≤ i.val
    · left
      have := h1 (Pi.single j 1) i hi
      simpa [Matrix.mulVec_single_one] using this
    by_cases hj : a ≤ j.val
    · exact Or.inr ⟨by omega, hj⟩
    · left
      have hx : ∀ k : Fin d, a ≤ k.val → (Pi.single j (1 : F) : Fin d → F) k = 0 := by
        intro k hk
        have : k ≠ j := fun h => hj (h ▸ hk)
        simp [Pi.single_apply, this]
      have := congrFun (h2 _ hx) i
      simpa [Matrix.mulVec_single_one] using this
  · intro h
    refine ⟨fun x i hi => ?_, fun x hx => ?_⟩
    · rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases h i j with h0 | ⟨hlt, _⟩
      · simp [h0]
      · omega
    · funext i
      rw [Matrix.mulVec, dotProduct, Pi.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases h i j with h0 | ⟨_, hj⟩
      · simp [h0]
      · simp [hx j hj]

open Polynomial in
variable {F : Type} [Field F] in

theorem _root_.GlobalTheory.CuspGL.UnipNilRad.exists_unip_bijOn_nilRad :
    ∀ (F : Type) [Field F] [Finite F] (d a : ℕ), a ≤ d → ∃ (A : Submodule F (Fin d → F)) (H : Subgroup (GL (Fin d) F)), Module.finrank F A = a ∧ (H : Set (GL (Fin d) F)) = {u : GL (Fin d) F | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)} ∧ Set.BijOn (fun u : GL (Fin d) F => Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1) (H : Set (GL (Fin d) F)) (_root_.GlobalTheory.CuspGL.nilRad A) := by
  intro F _ _ d a had
  refine ⟨_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a,
    _root_.GlobalTheory.CuspGL.UnipNilRad.unip (_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a),
    finrank_lowSub_of_le had, ?_, ?_⟩
  · ext u
    show Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1 ∈
      _root_.GlobalTheory.CuspGL.nilRad (_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a) ↔ _
    have hsub : Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1 =
        Matrix.toLin' ((u : Matrix (Fin d) (Fin d) F) - 1) := by
      rw [map_sub, Matrix.toLin'_one]
      rfl
    rw [hsub, toLin'_mem_nilRad_lowSub_iff, Set.mem_setOf_eq]
    simp only [Matrix.sub_apply, Matrix.one_apply, sub_eq_zero]
  · refine ⟨fun u hu => hu, fun u _ v _ h => ?_, fun f hf => ?_⟩
    · exact Units.ext (Matrix.toLin'.injective (sub_left_injective h))
    · set N := LinearMap.toMatrix' f with hNdef
      have hNf : Matrix.toLin' N = f := Matrix.toLin'_toMatrix' f
      have hN : N * N = 0 := by
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun x => ?_
        rw [Matrix.toLin'_mul, LinearMap.comp_apply, hNf, map_zero, LinearMap.zero_apply]
        exact hf.2 _ (hf.1 x)
      let u : GL (Fin d) F := ⟨1 + N, 1 - N, by noncomm_ring; rw [hN]; simp,
        by noncomm_ring; rw [hN]; simp⟩
      have hu : Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1 = f := by
        show Matrix.toLin' (1 + N) - 1 = f
        rw [map_add, Matrix.toLin'_one, hNf]
        exact add_sub_cancel_left (1 : Module.End F (Fin d → F)) f
      refine ⟨u, ?_, hu⟩
      show Matrix.toLin' (u : Matrix (Fin d) (Fin d) F) - 1 ∈
        _root_.GlobalTheory.CuspGL.nilRad (_root_.GlobalTheory.CuspGL.UnipNilRad.lowSub F d a)
      rw [hu]
      exact hf

end GlobalTheory.CuspGL.UnipNilRad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsTeichmullerMapAlgebraicClosureFiniteField
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL.TeichEmb

open Polynomial IntermediateField in
private theorem exists_pow_eq_one_algebraicClosure_of_finite (F : Type) [Field F] [Finite F]
    (x : AlgebraicClosure F) (hx : x ≠ 0) : ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  have hfin : FiniteDimensional F F⟮x⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have : Finite F⟮x⟯ := Module.finite_of_finite F
  have hne : (⟨x, IntermediateField.mem_adjoin_simple_self F x⟩ : F⟮x⟯) ≠ 0 := by
    intro h; exact hx (congrArg Subtype.val h)
  obtain ⟨n, hn, hpow⟩ :=
    isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite (Units.mk0 _ hne))
  refine ⟨n, hn, ?_⟩
  have := congrArg (fun u : (F⟮x⟯)ˣ => ((u : F⟮x⟯) : AlgebraicClosure F)) hpow
  simpa using this

open Polynomial IntermediateField in

theorem _root_.GlobalTheory.CuspGL.TeichEmb.exists_teichmuller :
    ∀ (F : Type) [Field F] [Finite F], ∃ θ : AlgebraicClosure F →* ℂ,
      ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y := by
  intro F _ _
  set p := ringChar F
  have : Fact p.Prime :=
    ⟨(CharP.char_is_prime_or_zero F p).resolve_right (CharP.char_ne_zero_of_finite F p)⟩
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have : PerfectRing (AlgebraicClosure F) p := inferInstance
  let W := WittVector p (AlgebraicClosure F)
  have : IsDomain W := inferInstance
  letI : Algebra (ZMod p) (AlgebraicClosure F) := ZMod.algebra _ p
  have hW : CharZero W := by
    let f : ℤ_[p] →+* W := (WittVector.map (algebraMap (ZMod p) (AlgebraicClosure F))).comp
      (WittVector.equiv p).symm.toRingHom
    have hf : Function.Injective f :=
      (WittVector.map_injective _ (algebraMap (ZMod p) (AlgebraicClosure F)).injective).comp
        (WittVector.equiv p).symm.injective
    exact (RingHom.charZero_iff hf).mp inferInstance
  let Ω := AlgebraicClosure (FractionRing W)
  have : CharZero (FractionRing W) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective W (FractionRing W))
  have : CharZero Ω := inferInstance
  let g : W →+* Ω := (algebraMap (FractionRing W) Ω).comp (algebraMap W (FractionRing W))
  have hg : Function.Injective g :=
    (algebraMap (FractionRing W) Ω).injective.comp (IsFractionRing.injective W (FractionRing W))
  let ι : AlgebraicClosure F →* Ω := (g : W →* Ω).comp (WittVector.teichmuller p)
  have hι : Function.Injective ι := by
    intro x y h
    have h1 : WittVector.teichmuller p x = WittVector.teichmuller p y := hg h
    simpa using congrArg (fun w : W => w.coeff 0) h1
  have hmem : ∀ x, ι x ∈ algebraicClosure ℚ Ω := by
    intro x
    rw [mem_algebraicClosure_iff]
    by_cases hx : x = 0
    · subst hx
      have : ι 0 = 0 := by
        show g (WittVector.teichmuller p 0) = 0
        rw [WittVector.teichmuller_zero, map_zero]
      rw [this]; exact isAlgebraic_zero
    · obtain ⟨n, hn, hpow⟩ := exists_pow_eq_one_algebraicClosure_of_finite F x hx
      refine (IsIntegral.of_pow hn ?_).isAlgebraic
      rw [← map_pow, hpow, map_one]; exact isIntegral_one
  have : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ Ω) := algebraicClosure.isAlgebraic ℚ Ω
  let φ : algebraicClosure ℚ Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  refine ⟨{ toFun := fun x => φ ⟨ι x, hmem x⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · exact (congrArg φ (Subtype.ext (map_one ι) : (⟨ι 1, hmem 1⟩ : algebraicClosure ℚ Ω) = 1)).trans
      (map_one φ)
  · intro x y
    rw [← map_mul]; exact congrArg φ (Subtype.ext (map_mul ι x y))
  · intro x y _ _ h
    exact hι (congrArg Subtype.val (φ.injective h))

end GlobalTheory.CuspGL.TeichEmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsWeightIdempotentStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weight_idempotent_of_eigenvector : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module L V] (ρ : Representation L G V) (B T : Subgroup G) (lam : B →* Lˣ) (v : V), B.Normal → v ≠ 0 → (∀ b : B, ρ b v = (lam b : L) • v) → (∀ g : G, g ∈ T ↔ ∀ b b' : B, (b' : G) = g⁻¹ * b * g → lam b' = lam b) → ∃ e : Module.End L V, e ≠ 0 ∧ e * e = e ∧ (∀ b : B, ρ b * e = (lam b : L) • e) ∧ (∀ t ∈ T, ρ t * e = e * ρ t) ∧ ∀ g ∉ T, e * ρ g * e = 0 := by
  first | exact @GlobalTheory.exists_weight_idempotent | exact GlobalTheory.exists_weight_idempotent | (intros; apply GlobalTheory.exists_weight_idempotent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExponentRegularOfNatDegreeMinpolyGeneratorPow
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem exponent_regular_of_natDegree_minpoly_pow : ∀ (F : Type) [Field F] [Finite F] (d k : ℕ) (ζ : AlgebraicClosure F), 0 < d → orderOf ζ = Nat.card F ^ d - 1 → (minpoly F (ζ ^ k)).natDegree = d → ∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1] := by
  intro F _ _ d k ζ _ hord hdeg i hi hid hmod
  have h1 : ζ ^ (Nat.card F ^ d - 1) = 1 := by
    rw [← hord]; exact pow_orderOf_eq_one ζ
  have h2 : (ζ ^ k) ^ (Nat.card F ^ i) = ζ ^ k := by
    rw [← pow_mul]; exact pow_eq_pow_of_modEq hmod h1
  have hint : IsIntegral F (ζ ^ k) := Algebra.IsIntegral.isIntegral _
  have hdvd : minpoly F (ζ ^ k) ∣ (X ^ (Nat.card F ^ i) - X : F[X]) := by
    apply minpoly.dvd
    simp only [map_sub, map_pow, aeval_X, h2, sub_self]
  have h3 := (minpoly.irreducible hint).natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdvd
  rw [hdeg] at h3
  exact absurd (Nat.le_of_dvd hi h3) (not_le.mpr hid)

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingAddNatPosSymm
section
open GlobalTheory.BI
namespace GlobalTheory.BI

private theorem character_pairing_eq_finrank_hom (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K]
    (G : Type) [Group G] [Finite G] {n m : ℕ} (ρ : Representation K G (Fin n → K))
    (σ : Representation K G (Fin m → K)) :
    pair (fun g => algebraMap K L (σ.character g)) (fun g => algebraMap K L (ρ.character g))
      = (Module.finrank K (Representation.IntertwiningMap ρ σ) : L) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hK := congrArg (algebraMap K L)
    (Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ)
  rw [map_natCast] at hK
  rw [← hK]
  simp only [pair, finsum_eq_sum_of_fintype, map_mul, map_inv₀, map_natCast, map_sum]

theorem pair_add_nat_pos_symm : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G], (∀ a b c : G → L, pair (a + b) c = pair a c + pair b c) ∧ (∀ a b : G → L, IsChar K L a → IsChar K L b → ∃ n : ℕ, pair a b = (n : L)) ∧ (∀ φ : G → L, IsIrrChar K L φ → ∃ n : ℕ, 0 < n ∧ pair φ φ = (n : L)) ∧ ∀ a b : G → L, pair a b = pair b a := by
  intro K L _ _ _ _ _ G _ _
  classical
  have : Fintype G := Fintype.ofFinite G
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c
    simp only [pair, finsum_eq_sum_of_fintype, Pi.add_apply, add_mul, Finset.sum_add_distrib,
      mul_add]
  · rintro a b ⟨n, ρ, hρ⟩ ⟨m, σ, hσ⟩
    refine ⟨Module.finrank K (Representation.IntertwiningMap σ ρ), ?_⟩
    rw [show a = fun g => algebraMap K L (ρ.character g) from funext hρ,
      show b = fun g => algebraMap K L (σ.character g) from funext hσ]
    exact character_pairing_eq_finrank_hom K L G σ ρ
  · rintro φ ⟨n, ρ, hirr, hρ⟩
    refine ⟨Module.finrank K (Representation.IntertwiningMap ρ ρ), ?_, ?_⟩
    · have : IsSimpleModule (MonoidAlgebra K G) ρ.asModule :=
        (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
      have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra K G) _
      obtain ⟨v, hv⟩ : ∃ v : Fin n → K, v ≠ 0 := exists_ne (0 : ρ.asModule)
      have : Nontrivial (Representation.IntertwiningMap ρ ρ) :=
        ⟨⟨Representation.IntertwiningMap.id ρ, 0, fun h => hv (by
          have hv0 := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) h
          rwa [Representation.IntertwiningMap.id_apply, Representation.IntertwiningMap.coe_zero,
            Pi.zero_apply] at hv0)⟩⟩
      have : Module.Finite K (Representation.IntertwiningMap ρ ρ) :=
        Module.Finite.equiv (Representation.invariantsEquivIntertwiningMap ρ ρ)
      exact Module.finrank_pos
    · rw [show φ = fun g => algebraMap K L (ρ.character g) from funext hρ]
      exact character_pairing_eq_finrank_hom K L G ρ ρ
  · intro a b
    simp only [pair, finsum_eq_sum_of_fintype]
    congr 1
    exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => by simp [mul_comm])
end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingCharacterEqFinrankInte
section
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem _root_.GlobalTheory.BI.pair_character_eq_finrank : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ρ : Representation K G V) (σ : Representation K G W), _root_.GlobalTheory.BI.pair (fun g => algebraMap K L (σ.character g)) (fun g => algebraMap K L (ρ.character g)) = (Module.finrank K (Representation.IntertwiningMap ρ σ) : L) := by
  intro K L _ _ _ _ _ G _ _ V _ _ _ W _ _ _ ρ σ
  classical
  haveI := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have h := congrArg (algebraMap K L)
    (Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ)
  unfold _root_.GlobalTheory.BI.pair
  rw [finsum_eq_sum_of_fintype]
  simpa only [map_mul, map_sum, map_inv₀, map_natCast] using h

end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingEqZeroOfDistinctIrredu
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

theorem pair_eq_zero_of_isIrrChar_ne : ∀ (G : Type) [Group G] [Finite G] (a b : G → ℂ),
    IsIrrChar ℂ ℂ a → IsIrrChar ℂ ℂ b → a ≠ b → pair a b = 0 := by
  intro G _ _ a b ha hb hab
  obtain ⟨n, ρ, hρ, ha⟩ := ha
  obtain ⟨m, σ, hσ, hb⟩ := hb
  have := hρ
  have := hσ
  have := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have ha' : a = ρ.character := funext fun g => by simp [ha]
  have hb' : b = σ.character := funext fun g => by simp [hb]
  have hne : ¬ Nonempty (Representation.Equiv σ ρ) := by
    rintro ⟨φ⟩
    exact hab (by rw [ha', hb', Representation.char_iso φ])
  have h := Representation.char_orthonormal ρ σ
  rw [if_neg hne] at h
  unfold pair
  rw [finsum_eq_sum_of_fintype, ha', hb']
  simpa using h
end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingSelfIrreducibleAlgClos
section
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem pair_self_of_isIrrChar_algClosed (L : Type) [Field L] [CharZero L] [IsAlgClosed L] (G : Type) [Group G] [Finite G]
    (χ : G → L) (h : IsIrrChar L L χ) : pair χ χ = 1 := by
  classical
  obtain ⟨n, ρ, hρ, hχ⟩ := h
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : L) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : ρ.IsIrreducible := hρ

  have key := ρ.card_inv_mul_sum_char_mul_char_eq_finrank ρ
  rw [Representation.IsIrreducible.finrank_intertwiningMap_self] at key
  unfold pair
  rw [finsum_eq_sum_of_fintype]
  simp only [hχ, Algebra.algebraMap_self, RingHom.id_apply]
  simpa using key
end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IndMulClassFunEqIndMulRestrict
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.BI

theorem ind_mul_classFun_eq_ind_mul_restrict :
    ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (ψ : H → ℂ) (φ : G → ℂ),
      (∀ g x : G, φ (x⁻¹ * g * x) = φ g) → ind H ψ * φ = ind H (fun h => ψ h * φ h) := by
  intro G _ _ H ψ φ hφ
  funext g
  have key : ∀ x : G, ext0 H (fun h => ψ h * φ h) (x⁻¹ * g * x) = ext0 H ψ (x⁻¹ * g * x) * φ g := by
    intro x
    rw [← hφ g x]
    unfold ext0
    split_ifs <;> simp
  simp only [Pi.mul_apply, ind]
  simp_rw [key]
  rw [mul_assoc, finsum_mul]

end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleIdempotentEqOneAndCharacterEqWeightAlStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_eq_one_and_character_eq_of_isIrreducible : ∀ (L : Type) [Field L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (ρ : Representation L G V), ρ.IsIrreducible → (∀ e : Module.End L V, e ≠ 0 → e * e = e → (∀ g, ρ g * e = e * ρ g) → e = 1) ∧ (∀ (lam : G →* Lˣ) (v : V), v ≠ 0 → (∀ g, ρ g v = (lam g : L) • v) → ∀ g, ρ.character g = (lam g : L)) := by
  first | exact @GlobalTheory.irreducible_idempotent_eq_one_and_character_eq_weight | exact GlobalTheory.irreducible_idempotent_eq_one_and_character_eq_weight | (intros; apply GlobalTheory.irreducible_idempotent_eq_one_and_character_eq_weight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsAbelianByPrimePowerGroupSubgroup
section
namespace GlobalTheory.BI

theorem _root_.GlobalTheory.BI.AbByP.subgroup :
    ∀ (G : Type) [Group G] (T : Subgroup G),
      _root_.GlobalTheory.BI.AbByP G → _root_.GlobalTheory.BI.AbByP T := by
  intro G _ T h
  unfold _root_.GlobalTheory.BI.AbByP at h ⊢
  obtain ⟨p, hp, A, hA, hcomm, hpow⟩ := h
  haveI := hA
  refine ⟨p, hp, A.subgroupOf T, Subgroup.normal_subgroupOf, ?_, ?_⟩
  · intro a ha b hb
    exact Subtype.ext (hcomm _ ha _ hb)
  · intro g
    obtain ⟨n, hn⟩ := hpow g
    exact ⟨n, by simpa [Subgroup.mem_subgroupOf] using hn⟩

end GlobalTheory.BI
end

