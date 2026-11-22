import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0030
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0022
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0005
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0535
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0575
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0335
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrAlphaDeterminantOrder
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0576
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0580
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0205

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CliffordSemidirectPrimeIndexIrreducibleCharacter
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem clifford_prime_index : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ),
    (Nat.card Γ).Prime → s ≠ 1 → ∀ χ : G ⋊[φ] Γ → ℂ, IsIrrChar ℂ ℂ χ →
      (∀ δ, χ (inl δ * inr s) = 0) ∨ (IsIrrChar ℂ ℂ (fun g => χ (inl g)) ∧
        ∑ᶠ g, χ (inl g * inr s) * star (χ (inl g * inr s)) = (Nat.card G : ℂ)) := by
  intro G Γ _ _ _ _ φ s hl hs χ hχ
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  haveI := Fintype.ofFinite (G ⋊[φ] Γ)
  have hH : Nat.card (G ⋊[φ] Γ) = Nat.card G * Nat.card Γ := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
  have hHne : (Nat.card (G ⋊[φ] Γ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hord : orderOf s = Nat.card Γ := by
    rcases (Nat.dvd_prime hl).1 (orderOf_dvd_natCard s) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hs
    · exact h
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    have htop : Subgroup.zpowers s = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord])
    intro t
    rw [htop]
    trivial
  have hl0 : Nat.card Γ ≠ 0 := hl.ne_zero
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (Nat.card Γ : ℂ))) (Nat.card Γ) :=
    Complex.isPrimitiveRoot_exp _ hl0
  obtain ⟨η, hη1, hηs, hF⟩ := GlobalTheory.Shin.CosetFourier.fourier_coset_sums G Γ φ s hgen _ hζ
  set ζ := Complex.exp (2 * Real.pi * Complex.I / (Nat.card Γ : ℂ)) with hζdef
  have hχchar : IsChar ℂ ℂ χ := by
    obtain ⟨n, ρ, -, h⟩ := hχ
    exact ⟨n, ρ, h⟩
  have hVR := virt_mul_comap_conj_ind_linear (G ⋊[φ] Γ)
  have hnorm : ∑ᶠ x, χ x * star (χ x) = (Nat.card (G ⋊[φ] Γ) : ℂ) := by
    obtain ⟨n, ρ, hρ, h⟩ := hχ
    haveI := hρ
    haveI : Invertible (Nat.card (G ⋊[φ] Γ) : ℂ) := invertibleOfNonzero hHne
    have ho := Representation.char_orthonormal ρ ρ
    rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at ho
    have hc : χ = ρ.character := funext fun g => by simpa using h g
    rw [finsum_eq_sum_of_fintype]
    have hst : ∀ x, star (χ x) = χ x⁻¹ := star_virt_eq_inv _ χ (isChar_mem_virt_complex hχchar)
    simp_rw [hst]
    rw [hc]
    exact ((inv_mul_eq_one₀ hHne).1 (by simpa using ho)).symm
  have hηstar : ∀ x, (η x : ℂ) * star (η x : ℂ) = 1 := by
    intro x
    have h := star_virt_eq_inv _ (fun x => (η x : ℂ)) (hVR.2.2.2.2 η) x
    rw [h, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hψchar : ∀ a : ℕ, IsChar ℂ ℂ (fun x => χ x * (η x : ℂ) ^ a) := by
    intro a
    have h := isChar_mul_complex hχchar (isChar_monoidHom_complex (η ^ a))
    convert h using 1
    funext x
    simp [Pi.mul_apply]
  have hψnorm : ∀ a : ℕ, ∑ᶠ x, (fun x => χ x * (η x : ℂ) ^ a) x * star ((fun x => χ x * (η x : ℂ) ^ a) x) =
      (Nat.card (G ⋊[φ] Γ) : ℂ) := by
    intro a
    rw [← hnorm]
    congr 1
    funext x
    simp only
    rw [star_mul, star_pow]
    calc χ x * (η x : ℂ) ^ a * (star (η x : ℂ) ^ a * star (χ x))
        = χ x * star (χ x) * ((η x : ℂ) * star (η x : ℂ)) ^ a := by ring
      _ = χ x * star (χ x) := by rw [hηstar, one_pow, mul_one]
  have hψirr : ∀ a : ℕ, IsIrrChar ℂ ℂ (fun x => χ x * (η x : ℂ) ^ a) := fun a =>
    ((irr_of_norm_one _ _ (isChar_mem_virt_complex (hψchar a)) (hψnorm a)).2 (hψchar a)).1
  by_cases hcase : ∃ a, 0 < a ∧ a < Nat.card Γ ∧ (fun x => χ x * (η x : ℂ) ^ a) = χ
  · left
    obtain ⟨a, ha0, hal, he⟩ := hcase
    intro δ
    have h1 := congrFun he (inl δ * inr s)
    have hv : (η (inl δ * inr s) : ℂ) = ζ := by rw [map_mul, hη1, one_mul, hηs]
    rw [hv] at h1
    have hζa : ζ ^ a ≠ 1 := hζ.pow_ne_one_of_pos_of_lt ha0.ne' hal
    have h2 : χ (inl δ * inr s) * (ζ ^ a - 1) = 0 := by rw [mul_sub, h1, mul_one, sub_self]
    exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hζa)
  · right
    push_neg at hcase
    have hNa : ∀ a ∈ Finset.range (Nat.card Γ), a ≠ 0 →
        ∑ᶠ x, χ x * star (χ x * (η x : ℂ) ^ a) = 0 := by
      intro a ha ha0
      have hne := hcase a (Nat.pos_of_ne_zero ha0) (Finset.mem_range.1 ha)
      have hp := pair_eq_zero_of_isIrrChar_ne _ χ _ hχ (hψirr a) (Ne.symm hne)
      unfold pair at hp
      have hs0 := (mul_eq_zero.1 hp).resolve_left (inv_ne_zero hHne)
      rw [← hs0]
      congr 1
      funext x
      have h := star_virt_eq_inv _ _ (isChar_mem_virt_complex (hψchar a)) x
      rw [h]
    have hN0 : ∑ᶠ x, χ x * star (χ x * (η x : ℂ) ^ 0) = (Nat.card (G ⋊[φ] Γ) : ℂ) := by
      simpa using hnorm
    have h0mem : 0 ∈ Finset.range (Nat.card Γ) := Finset.mem_range.2 (Nat.pos_of_ne_zero hl0)
    obtain ⟨hA, hB⟩ := hF χ χ
    rw [Finset.sum_eq_single 0 (fun a ha ha0 => hNa a ha ha0) (fun h => absurd h0mem h), hN0, hH] at hA
    rw [Finset.sum_eq_single 0 (fun a ha ha0 => by rw [hNa a ha ha0, mul_zero]) (fun h => absurd h0mem h),
      pow_zero, one_mul, hN0, hH] at hB
    have hlc : (Nat.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hl0
    push_cast at hA hB
    have hSG : ∑ᶠ g, χ (inl g) * star (χ (inl g)) = (Nat.card G : ℂ) :=
      mul_left_cancel₀ hlc (by rw [hA, mul_comm])
    refine ⟨?_, mul_left_cancel₀ hlc (by rw [hB, mul_comm])⟩
    have hrchar : IsChar ℂ ℂ (fun g => χ (inl g)) := by
      obtain ⟨n, ρ, h⟩ := hχchar
      exact ⟨n, ρ.comp SemidirectProduct.inl, fun g => h _⟩
    exact ((irr_of_norm_one G _ (isChar_mem_virt_complex hrchar) hSG).2 hrchar).1

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoindEigenEqBotOfRootInUnipotentRadical
section
open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL.MackeyRadical

theorem exists_elem {F : Type} [Field F] {r : ℕ} {i j : Fin r} (h : i ≠ j) (t : F) :
    ∃ g : GL (Fin r) F, ∀ k l, (g : Matrix (Fin r) (Fin r) F) k l =
      (1 : Matrix (Fin r) (Fin r) F) k l + if i = k ∧ j = l then t else 0 := by
  refine ⟨⟨Matrix.transvection i j t, Matrix.transvection i j (-t), ?_, ?_⟩, fun k l => ?_⟩
  · rw [Matrix.transvection_mul_transvection_same _ _ h, add_neg_cancel, Matrix.transvection_zero]
  · rw [Matrix.transvection_mul_transvection_same _ _ h, neg_add_cancel, Matrix.transvection_zero]
  · simp [Matrix.transvection, Matrix.single]

theorem eig_eq_bot_of_radical : ∀ (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ (j : ℕ) (w : Equiv.Perm (Fin r)) (x : GL (Fin r) F), (∀ (g : GL (Fin r) F) (a c : Fin r), ((x⁻¹ * g * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a c = (g : Matrix (Fin r) (Fin r) F) (w a) (w c)) → ψ ≠ 1 → ∀ a c : Fin r, cutEdge j a c → b (w a) < b (w c) → eig σ {p | x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r} (fun p => ψ (edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x))) = ⊥ := by
  intro F _ ψ r V _ _ b σ hσ j w x hx hψ a c hac hb
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ (DFunLike.ext _ _ fun t => by simpa using h t)
  have hne : w a ≠ w c := fun h => by rw [h] at hb; exact lt_irrefl _ hb
  have hlt : a.val < c.val := by have := hac.1; omega
  obtain ⟨g, hg⟩ := exists_elem hne t
  have hgb : g ∈ blockTri (κ := F) b := by
    refine mem_blockTri.2 fun k l hkl => ?_
    have hkl' : k ≠ l := fun h => by rw [h] at hkl; exact lt_irrefl _ hkl
    rw [hg, Matrix.one_apply_ne hkl', if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm hb hkl
  have h1 : σ ⟨g, hgb⟩ = 1 := by
    refine hσ.infl _ fun k l hkl => ?_
    show (g : Matrix (Fin r) (Fin r) F) k l = _
    rw [hg, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact hb.ne hkl
  have hc : ∀ k l, ((x⁻¹ * g * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k l =
      (1 : Matrix (Fin r) (Fin r) F) k l + if a = k ∧ c = l then t else 0 := by
    intro k l
    rw [hx, hg]
    simp [Matrix.one_apply]
  have hu : x⁻¹ * g * x ∈ unip F r := by
    refine ⟨mem_blockTri.2 fun k l hkl => ?_, fun k => ?_⟩
    · have hkl' : k ≠ l := fun h => by rw [h] at hkl; exact lt_irrefl _ hkl
      rw [hc, Matrix.one_apply_ne hkl', if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hlt hkl
    · rw [hc, Matrix.one_apply_eq, if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      exact lt_irrefl _ hlt
  have hs : edgeSum (cutEdge j) (x⁻¹ * g * x) = t := by
    unfold edgeSum
    have key : ∀ k l : Fin r, (if cutEdge j k l then ((x⁻¹ * g * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k l else 0) =
        if l = c then (if k = a then t else 0) else 0 := by
      intro k l
      by_cases h : cutEdge j k l
      · have hkl : k ≠ l := fun e => by have := h.1; rw [e] at this; omega
        rw [if_pos h, hc, Matrix.one_apply_ne hkl, zero_add]
        by_cases h1 : l = c <;> by_cases h2 : k = a <;> simp [h1, h2, @eq_comm _ a k, @eq_comm _ c l]
      · rw [if_neg h]
        by_cases h1 : l = c <;> by_cases h2 : k = a <;> simp [h1, h2]
        subst h1 h2
        exact absurd hac h
    simp only [key]
    simp
  refine eq_bot_iff.2 fun v hv => ?_
  simp only [eig, Submodule.mem_iInf, LinearMap.mem_ker] at hv
  have := hv ⟨g, hgb⟩ hu
  simp only [h1, hs, LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply, LinearMap.id_apply] at this
  have h2 : (1 - ψ t) • v = 0 := by rw [sub_smul, one_smul]; exact this
  rcases smul_eq_zero.1 h2 with h | h
  · exact absurd (sub_eq_zero.1 h).symm ht
  · exact h

end GlobalTheory.FinGL.MackeyRadical
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoindEigenSortingPermEqLeviWhittaker
section
noncomputable section

namespace GlobalTheory.FinGL.SortWh

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem mem_eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G) (χ : G → ℂ)
    (v : V) : v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

variable {F : Type} [Field F] {r : ℕ}

def bd (b : Fin r → ℕ) (M : Matrix (Fin r) (Fin r) F) : Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i k => if b i = b k then M i k else 0

theorem bd_apply (b : Fin r → ℕ) (M : Matrix (Fin r) (Fin r) F) (i k : Fin r) :
    bd b M i k = if b i = b k then M i k else 0 := rfl

theorem bd_one (b : Fin r → ℕ) : bd b (1 : Matrix (Fin r) (Fin r) F) = 1 := by
  ext i k
  rw [bd_apply]
  split_ifs with h
  · rfl
  · rw [Matrix.one_apply_ne]
    rintro rfl
    exact h rfl

theorem bd_bd (b : Fin r → ℕ) (M : Matrix (Fin r) (Fin r) F) : bd b (bd b M) = bd b M := by
  ext i k
  simp only [bd_apply]
  split_ifs <;> rfl

theorem bd_mul (b : Fin r → ℕ) {M N : Matrix (Fin r) (Fin r) F} (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) :
    bd b (M * N) = bd b M * bd b N := by
  ext i k
  simp only [bd_apply, Matrix.mul_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun l _ => ?_
    rcases lt_trichotomy (b l) (b i) with h1 | h1 | h1
    · rw [hM h1]; simp
    · rw [if_pos h1.symm, if_pos (h1.trans h)]
    · rw [hN (show b k < b l by omega)]; simp
  · refine (Finset.sum_eq_zero fun l _ => ?_).symm
    by_cases h1 : b i = b l
    · rw [if_neg (show ¬ b l = b k by omega), mul_zero]
    · rw [if_neg h1, zero_mul]

theorem bd_tri (b : Fin r → ℕ) (M : Matrix (Fin r) (Fin r) F) : (bd b M).BlockTriangular b := by
  intro i k h
  rw [bd_apply, if_neg (by omega)]

def levi (b : Fin r → ℕ) (p : blockTri (κ := F) b) : blockTri (κ := F) b :=
  ⟨⟨bd b ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F), bd b (((p⁻¹ : blockTri (κ := F) b) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F),
    by rw [← bd_mul b p.2 (p⁻¹).2, ← Units.val_mul]; simp [bd_one],
    by rw [← bd_mul b (p⁻¹).2 p.2, ← Units.val_mul]; simp [bd_one]⟩, bd_tri b _⟩

theorem levi_apply (b : Fin r → ℕ) (p : blockTri (κ := F) b) (i k : Fin r) :
    ((levi b p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k =
      if b i = b k then ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k else 0 := rfl

theorem sigma_levi {V : Type} [AddCommGroup V] [Module ℂ V] {b : Fin r → ℕ}
    {σ : Representation ℂ (blockTri (κ := F) b) V} (hσ : IsCuspDatum b σ) (p : blockTri (κ := F) b) :
    σ (levi b p) = σ p := by
  have h : σ (p⁻¹ * levi b p) = 1 := by
    refine hσ.infl _ fun i k hik => ?_
    have h1 : bd b ((((p⁻¹ * levi b p : blockTri (κ := F) b)) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = 1 := by
      rw [Subgroup.coe_mul, Units.val_mul, bd_mul b (p⁻¹).2 (levi b p).2]
      have : bd b ((levi b p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
          bd b ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := bd_bd b _
      rw [this, ← bd_mul b (p⁻¹).2 p.2, ← Units.val_mul]
      simp [bd_one]
    have h2 := congrFun (congrFun h1 i) k
    rwa [bd_apply, if_pos hik] at h2
  have : levi b p = p * (p⁻¹ * levi b p) := by group
  rw [this, map_mul, h, mul_one]

theorem edgeSum_levi (b : Fin r → ℕ) (p : blockTri (κ := F) b) :
    edgeSum (blkEdge b) (levi b p : GL (Fin r) F) = edgeSum (blkEdge b) (p : GL (Fin r) F) := by
  unfold edgeSum
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · rw [levi_apply, if_pos h.2]
  · rfl

section Perm

variable {b : Fin r → ℕ} {j : ℕ} {w : Equiv.Perm (Fin r)}

theorem lt_iff (h1 : ∀ a c : Fin r, a < c → b (w a) = b (w c) → w a < w c) {a c : Fin r} (h : b (w a) = b (w c)) :
    a < c ↔ w a < w c := by
  refine ⟨fun hac => h1 a c hac h, fun hw => ?_⟩
  rcases lt_trichotomy a c with h' | h' | h'
  · exact h'
  · subst h'; exact absurd hw (lt_irrefl _)
  · exact absurd (h1 c a h' h.symm) (not_lt.2 hw.le)

theorem edge_iff (hb : Monotone b) (h1 : ∀ a c : Fin r, a < c → b (w a) = b (w c) → w a < w c)
    (h2 : ∀ a e c : Fin r, a ≤ e → e ≤ c → b (w a) = b (w c) → b (w e) = b (w a))
    (h4 : ∀ a c : Fin r, a.val < j → j ≤ c.val → b (w a) ≠ b (w c)) {a c : Fin r} (h : b (w a) = b (w c)) :
    blkEdge b (w a) (w c) ↔ cutEdge j a c := by
  constructor
  · rintro ⟨e1, -⟩
    have hac : a < c := (lt_iff h1 h).2 (by rw [Fin.lt_def]; omega)
    have hac' : a.val < c.val := hac
    have hc : c.val = a.val + 1 := by
      by_contra hne
      let e : Fin r := ⟨a.val + 1, by have := c.2; omega⟩
      have hae : a < e := by rw [Fin.lt_def]; simp [e]
      have hec : e < c := by rw [Fin.lt_def]; simp only [e]; omega
      have hbe := h2 a e c hae.le hec.le h
      have k1 : (w a).val < (w e).val := h1 a e hae hbe.symm
      have k2 : (w e).val < (w c).val := h1 e c hec (hbe.trans h)
      omega
    refine ⟨hc, fun hj => h4 a c (by omega) (by omega) h⟩
  · rintro ⟨e1, -⟩
    refine ⟨?_, h⟩
    have hac : a < c := by rw [Fin.lt_def]; omega
    have hw : (w a).val < (w c).val := h1 a c hac h
    by_contra hne
    let i : Fin r := ⟨(w a).val + 1, by have := (w c).2; omega⟩
    have hai : w a < i := by rw [Fin.lt_def]; simp [i]
    have hic : i < w c := by rw [Fin.lt_def]; simp only [i]; omega
    obtain ⟨e, he⟩ := w.surjective i
    have k1 : b (w a) ≤ b i := hb hai.le
    have k2 : b i ≤ b (w c) := hb hic.le
    rw [← he] at hai hic k1 k2
    have l1 : a.val < e.val := (lt_iff h1 (by omega)).2 hai
    have l2 : e.val < c.val := (lt_iff h1 (by omega)).2 hic
    omega

end Perm

theorem eig_conj_eq_leviWh : ∀ (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ (j : ℕ) (w : Equiv.Perm (Fin r)) (x : GL (Fin r) F), (∀ (g : GL (Fin r) F) (a c : Fin r), ((x⁻¹ * g * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a c = (g : Matrix (Fin r) (Fin r) F) (w a) (w c)) → (∀ a c : Fin r, a < c → b (w a) = b (w c) → w a < w c) → (∀ a e c : Fin r, a ≤ e → e ≤ c → b (w a) = b (w c) → b (w e) = b (w a)) → (∀ a c : Fin r, cutEdge j a c → b (w c) ≤ b (w a)) → (∀ a c : Fin r, a.val < j → j ≤ c.val → b (w a) ≠ b (w c)) → eig σ {p | x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r} (fun p => ψ (edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x))) = eig σ {p | (p : GL (Fin r) F) ∈ unip F r} (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) := by
  intro F _ ψ r V _ _ b σ hσ j w x hx h1 h2 h3 h4
  have hsum : ∀ p : blockTri (κ := F) b, edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x) =
      edgeSum (blkEdge b) (p : GL (Fin r) F) := by
    intro p
    unfold edgeSum
    rw [← Equiv.sum_comp w (fun i => ∑ k, if blkEdge b i k then ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k else 0)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Equiv.sum_comp w (fun k => if blkEdge b (w a) k then ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (w a) k else 0)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hx]
    by_cases h : b (w a) = b (w c)
    · simp only [edge_iff hσ.mono h1 h2 h4 h]
    · rw [if_neg (show ¬ blkEdge b (w a) (w c) from fun h' => h h'.2)]
      split_ifs with hc
      · exact p.2 (lt_of_le_of_ne (h3 a c hc) (Ne.symm h))
      · rfl
  ext v
  rw [mem_eig, mem_eig]
  constructor
  · intro H p hp
    have hp' : (p : GL (Fin r) F) ∈ unip F r := hp
    have hm : x⁻¹ * (levi b p : GL (Fin r) F) * x ∈ unip F r := by
      refine ⟨mem_blockTri.2 fun a c hac => ?_, fun a => ?_⟩
      · rw [hx, levi_apply]
        split_ifs with h
        · exact unip_lower hp' (h1 c a hac h.symm)
        · rfl
      · rw [hx, levi_apply, if_pos rfl, unip_diag hp']
    have := H (levi b p) hm
    rw [sigma_levi hσ, hsum, edgeSum_levi] at this
    exact this
  · intro H p hp
    have hp' : x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r := hp
    have hm : (levi b p : GL (Fin r) F) ∈ unip F r := by
      refine ⟨mem_blockTri.2 fun i k hik => ?_, fun i => ?_⟩
      · obtain ⟨a, rfl⟩ := w.surjective i
        obtain ⟨c, rfl⟩ := w.surjective k
        rw [levi_apply]
        split_ifs with h
        · rw [← hx]
          exact unip_lower hp' ((lt_iff h1 h.symm).2 hik)
        · rfl
      · obtain ⟨a, rfl⟩ := w.surjective i
        rw [levi_apply, if_pos rfl, ← hx, unip_diag hp']
    have := H (levi b p) hm
    rw [sigma_levi hσ, edgeSum_levi] at this
    rw [hsum]
    exact this

end GlobalTheory.FinGL.SortWh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousConeDescendsEtaleSurjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem contCone_of_etale_surjective : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G) (W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W), Etale f → Surjective f → ∀ (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative], P f → (∀ (Z : Scheme.{0}) (π : Z ⟶ V), P π → ContCone R F ((bc (sch.map (π ≫ f ≫ r))).mapCone c)) → ContCone R F ((bc (sch.map r)).mapCone c) := by
  intro R _ F S I _ _ G c W V r f hE hS P _ _ hf hZ
  have hstep : ContCone R F ((bc (cechAug f ≫ sch.map r)).mapCone c) := by
    refine GlobalTheory.T.cohomologyContinuous_base_change_of_levels R F S (cech f) (cechAug f ≫ sch.map r) I G c (fun k => ?_)
    obtain ⟨Z, π, e, hP, he⟩ := GlobalTheory.EtC.cech_level_representable P V W f hf k
    refine ⟨Z, π ≫ f ≫ r, e, ?_, hZ Z π hP⟩
    rw [NatTrans.comp_app, ← Category.assoc, he]
    change yoneda.map (π ≫ f) ≫ yoneda.map r = _
    rw [← yoneda.map_comp, Category.assoc]
  refine (ContCone.iff_of_eqv R F I _ _ ((bc (cechAug f ≫ sch.map r)).mapCone c) ((bc (sch.map r)).mapCone c)
    (Functor.whiskerLeft G (bcMap (cechAug f) (sch.map r))) ((bcMap (cechAug f) (sch.map r)).app c.pt) (fun i => ?_)
    (fun i => GlobalTheory.T.etaleCohomologyEquivalence_baseChange_cechAugmentation R F S W V r f hE hS (G.obj i)) (GlobalTheory.T.etaleCohomologyEquivalence_baseChange_cechAugmentation R F S W V r f hE hS c.pt)).mp hstep
  exact ((bcMap (cechAug f) (sch.map r)).naturality (c.π.app i))

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrAlphaDeterminantOrderStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_alpha_determinant_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (α : Λ), Algebra.adjoin ℤ_[p] {α} = ⊤ → ∀ (a b h : ℕ), h = Module.finrank ℤ_[p] Λ * (a + b) → ∀ (D : Datum ε h Λ) (τ : Λ →+* O) (z : Fin (a + b) → eig C (actH D) τ), IsBasisOf C (lieSub C D τ) (fun i => bC C D (z (Fin.castAdd b i))) → IsBasisOf C (filQuot C D τ) (fun i => (z (Fin.natAdd a i) : Fin h → C)) → ∃ c : C, v c = ∏ᶠ σ : {σ : Λ →+* O // σ ≠ τ}, v (algebraMap O C (τ α) - algebraMap O C (σ.1 α)) ^ D.lieRank σ.1 ∧ (Submodule.span O {exteriorPower.ιMulti C (a + b) z} : Set (detLine C (actH D) τ (a + b))) = (fun w => c • w) '' (detLattice C (actH D) τ (a + b) : Set (detLine C (actH D) τ (a + b))) := by
  first | exact @GlobalTheory.DetInv.span_wedge_lie_fil_eq_smul_detLattice | exact GlobalTheory.DetInv.span_wedge_lie_fil_eq_smul_detLattice | (intros; apply GlobalTheory.DetInv.span_wedge_lie_fil_eq_smul_detLattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigCongr
section
noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open Formalism.L2.DIV Module

variable {F : Type} [Field F] {r : ℕ}

def colSet (F : Type) [Field F] (b : Fin r → ℕ) (k : ℕ) : Set (blockTri (κ := F) b) :=
  {p | (p : GL (Fin r) F) ∈ unip F r ∧ ∀ i j : Fin r, j.val < k →
    ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j}

def colChar (ψ : AddChar F ℂ) (b : Fin r → ℕ) (k : Fin r) (l : Fin r → F) (p : blockTri (κ := F) b) : ℂ :=
  ψ (∑ i, l i * ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k +
    edgeSum (fun i j => blkEdge b i j ∧ k < j) (p : GL (Fin r) F))

theorem mem_eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G)
    (χ : G → ℂ) (v : V) : v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem eig_congr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G)
    (χ χ' : G → ℂ) (h : ∀ g ∈ S, χ g = χ' g) : eig τ S χ = eig τ S χ' := by
  ext v
  simp only [mem_eig]
  exact forall₂_congr fun g hg => by rw [h g hg]

end GlobalTheory.FinGL.LeviWh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCocycleCoboundaryIffStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_cocycle_coboundary_iff : ∀ (R : Type) [CommRing R] (F : Shv R) (A : Type) [CommRing A], ∃ γ : ∀ (B : Type) [CommRing B] [Algebra A B], Z1 F A B →+ H R (sp A) F 1, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.FaithfullyFlat A B], (∀ u : Z1 F A B, γ B u = 0 ↔ ∃ v : (onRings F).obj (CommRingCat.of B), (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) = ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)).hom v - ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom)).hom v) ∧ (∀ x : H R (sp A) F 1, pull R (spMap (algebraMap A B)) F 1 x = 0 → ∃ u, γ B u = x) ∧ (∀ u, pull R (spMap (algebraMap A B)) F 1 (γ B u) = 0) ∧ ∀ (B' : Type) [CommRing B'] [Algebra A B'] [Algebra.Etale A B'] [Module.FaithfullyFlat A B'] (φ : B →ₐ[A] B') (u : Z1 F A B) (u' : Z1 F A B'), (u' : (onRings F).obj (CommRingCat.of (B' ⊗[A] B'))) = ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map φ φ).toRingHom)).hom u → γ B' u' = γ B u := by
  first | (exact @GlobalTheory.CechOne.cech1) | (exact GlobalTheory.CechOne.cech1) | (intros; apply GlobalTheory.CechOne.cech1  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientRingInvarianceStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_coefficientRing_invariance : GlobalTheory.EtC.A8 := by
  first
  | exact @GlobalTheory.EtC.a8
  | exact GlobalTheory.EtC.a8
  | (intros; apply GlobalTheory.EtC.a8 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingToHenselisationInjectiveOfNbhd
section
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem Hens.of_injective_of_nbhd (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) :
    Function.Injective (Hens.of i) := by
  have : IsDirected (EtNbhd R) (· ≤ ·) := GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected R
  have : DirectedSystem (fun j : EtNbhd R => j.B) (fun _ _ h => ⇑(EtNbhd.trans h)) :=
    ⟨fun j x => (GlobalTheory.T.pointedEtaleNbhd_transitionMap_directedSystem R).1 j x,
      fun k j l hlj hjk x => (GlobalTheory.T.pointedEtaleNbhd_transitionMap_directedSystem R).2 l j k hlj hjk x⟩
  exact Ring.DirectLimit.of_injective (G := fun j : EtNbhd R => j.B) (fun _ _ h => EtNbhd.trans h)
    (fun _ _ h => (GlobalTheory.T.etaleNbhdLocalRingTransitionMap_isLocalHom_injective R _ _ h).2) i

end GlobalTheory.Henselisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescOfFlatOfSchemeTheoreticallyDominantBasStatement
section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_desc_of_flat_of_schemeTheoreticallyDominant_base : ∀ {S S' U U' X Y Y' YU Y'' : Scheme.{0}} (f : S' ⟶ S) (j : U ⟶ S) (f' : U' ⟶ U) (j' : U' ⟶ S') [Flat f] [Surjective f] [QuasiCompact f] [QuasiCompact j] [IsSchemeTheoreticallyDominant j], IsPullback j' f' f j → ∀ (x : X ⟶ S) [IsSeparated x] (y : Y ⟶ S) [Flat y] (y' : Y' ⟶ S') (π : Y' ⟶ Y), IsPullback π y' y f → ∀ (yU : YU ⟶ U) (ιY : YU ⟶ Y), IsPullback ιY yU y j → ∀ (y'' : Y'' ⟶ U') (c : Y'' ⟶ Y') (cU : Y'' ⟶ YU), IsPullback c y'' y' j' → IsPullback cU y'' yU f' → cU ≫ ιY = c ≫ π → ∀ (h' : Y' ⟶ X) (hU : YU ⟶ X), h' ≫ x = y' ≫ f → c ≫ h' = cU ≫ hU → ∃ h : Y ⟶ X, π ≫ h = h' ∧ ιY ≫ h = hU ∧ h ≫ x = y := by
  first | exact @GlobalTheory.exists_desc_of_flat_of_schemeTheoreticallyDominant | exact GlobalTheory.exists_desc_of_flat_of_schemeTheoreticallyDominant | (intros; apply GlobalTheory.exists_desc_of_flat_of_schemeTheoreticallyDominant <;> assumption)
end

