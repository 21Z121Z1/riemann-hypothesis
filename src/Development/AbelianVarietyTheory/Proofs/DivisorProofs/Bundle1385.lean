import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0242
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointShapeForcedLambda
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ShapeForced
open Formalism.BasicNotions.TH

theorem getD_replicate_append (m k : ℕ) (u w : ℚ) (i : ℕ) :
    (List.replicate m u ++ List.replicate k w).getD i 0 = if i < m then u else if i < m + k then w else 0 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h1 : i < m
  · rw [List.getElem?_append_left (by simpa using h1)]; simp [h1]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_replicate, h1, if_false, List.getElem?_replicate]
    by_cases h2 : i < m + k
    · simp [h2, show i - m < k by omega]
    · simp [h2, show ¬ i - m < k by omega]

theorem all_eq_of_getD {L : List ℚ} {n : ℕ} {v : ℚ} (hn : L.length = n) (h : ∀ i < n, L.getD i 0 = v) :
    ∀ x ∈ L, x = v := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have := h i (hn ▸ hi)
  rwa [List.getD_eq_getElem _ _ hi] at this

theorem pad_length (a b : List ℤ) (k : ℕ) : (pad a k b).length = a.length + k + b.length := by
  simp [pad]; omega

theorem forced (a b : List ℤ) (n : ℕ) (v : ℚ) (hlen : a.length + b.length ≤ n)
    (h : ∀ i < n, (pad a (n - a.length - b.length) b).getD i 0 = v) :
    (∀ x ∈ a, (x : ℚ) = v) ∧ (∀ x ∈ b, (x : ℚ) = v) ∧ (0 < n - a.length - b.length → (0 : ℚ) = v) := by
  have hall := all_eq_of_getD (by rw [pad_length]; omega) h
  refine ⟨fun x hx => hall _ ?_, fun x hx => hall _ ?_, fun hk => hall _ ?_⟩
  · simp only [pad, List.map_append, List.mem_append, List.mem_map]; exact Or.inl (Or.inl ⟨x, hx, rfl⟩)
  · simp only [pad, List.map_append, List.mem_append, List.mem_map]; exact Or.inr ⟨x, hx, rfl⟩
  · simp only [pad, List.map_append, List.mem_append, List.mem_map]
    exact Or.inl (Or.inr ⟨0, List.mem_replicate.mpr ⟨by omega, rfl⟩, by simp⟩)

theorem cast_pos_of {l : List ℤ} {v : ℚ} (hv : 0 < v) (hl : ∀ x ∈ l, x < 0) (he : ∀ x ∈ l, (x : ℚ) = v) : l = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  have h1 := he x hx
  have h2 : (x : ℚ) < 0 := by exact_mod_cast hl x hx
  linarith

theorem cast_neg_of {l : List ℤ} {v : ℚ} (hv : v < 0) (hl : ∀ x ∈ l, 0 < x) (he : ∀ x ∈ l, (x : ℚ) = v) : l = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  have h1 := he x hx
  have h2 : (0 : ℚ) < x := by exact_mod_cast hl x hx
  linarith

theorem map_rep {l : List ℤ} {n : ℕ} {v : ℚ} (hn : l.length = n) (he : ∀ x ∈ l, (x : ℚ) = v) :
    l.map (fun x : ℤ => (x : ℚ)) = List.replicate n v := by
  rw [List.eq_replicate_iff]
  refine ⟨by simp [hn], ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact he x hx

end GlobalTheory.ShapeForced

open Formalism.BasicNotions.TH GlobalTheory.ShapeForced in
theorem GlobalTheory.RealLift.jointShape_halfKappa : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → (∀ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P Q R S (fun _ => (κ : ℚ) / 2) μ' → μ' = GlobalTheory.RealLift.lam P Q R S κ) ∧ ∀ μ' : Formalism.BasicNotions.TH.Ix R S → ℚ, Formalism.BasicNotions.TH.JointShape P' Q' R S (fun _ => -((κ : ℚ) / 2)) μ' → (fun c => μ' c + (κ : ℚ) / 2) = GlobalTheory.RealLift.lam P Q R S κ := by
  intro P Q P' Q' R S κ hN
  obtain ⟨hR, hS, hSP, hSQ', -, -, hlt⟩ := hN
  have hltQ : (R : ℚ) + S < κ := by exact_mod_cast hlt
  constructor
  · rintro μ' ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, hab, hcd, had, hcb, h1, h2⟩
    have pA : 0 < (κ : ℚ) / 2 - cPair R S := by unfold cPair; linarith
    have pC : 0 < (κ : ℚ) / 2 + cPair R S := by unfold cPair; linarith
    have hA : ∀ i < P, (pad a (P - a.length - b.length) b).getD i 0 = (κ : ℚ) / 2 - cPair R S := by
      intro i hi
      have := congrFun h1 (.inl ⟨i, hi⟩)
      simpa [shiftNu, ofBlocks] using this.symm
    have hC : ∀ j < Q, (pad c (Q - c.length - d.length) d).getD j 0 = (κ : ℚ) / 2 + cPair R S := by
      intro j hj
      have := congrFun h1 (.inr ⟨j, hj⟩)
      simpa [shiftNu, ofBlocks] using this.symm
    obtain ⟨haA, hbA, hkA⟩ := forced a b P _ hab hA
    obtain ⟨hcC, hdC, hkC⟩ := forced c d Q _ hcd hC
    have hb0 := cast_pos_of pA hb hbA
    have hd0 := cast_pos_of pC hd hdC
    subst hb0 hd0
    have hal : a.length = P := by
      by_contra hne
      have := hkA (by simp; omega)
      linarith
    have hcl : c.length = Q := by
      by_contra hne
      have := hkC (by simp; omega)
      linarith
    have hamap := map_rep hal haA
    have hcmap := map_rep hcl hcC
    funext x
    have := congrFun h2 x
    rcases x with ⟨i, hi⟩ | ⟨j, hj⟩
    · simp only [shiftNu, ofBlocks, pad, List.map_append, List.map_replicate, hamap, List.map_nil, List.append_nil,
        getD_replicate_append, Int.cast_zero] at this
      simp only [GlobalTheory.RealLift.lam]
      split_ifs at this ⊢ <;> first | linarith | omega
    · simp only [shiftNu, ofBlocks, pad, List.map_append, List.map_replicate, hcmap, List.map_nil, List.append_nil,
        getD_replicate_append, Int.cast_zero] at this
      simp only [GlobalTheory.RealLift.lam]
      split_ifs at this ⊢ <;> first | linarith | omega
  · rintro μ' ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, hab, hcd, had, hcb, h1, h2⟩
    have pB : -((κ : ℚ) / 2) - cPair R S < 0 := by unfold cPair; linarith
    have pD : -((κ : ℚ) / 2) + cPair R S < 0 := by unfold cPair; linarith
    have hB : ∀ i < P', (pad a (P' - a.length - b.length) b).getD i 0 = -((κ : ℚ) / 2) - cPair R S := by
      intro i hi
      have := congrFun h1 (.inl ⟨i, hi⟩)
      simpa [shiftNu, ofBlocks] using this.symm
    have hD : ∀ j < Q', (pad c (Q' - c.length - d.length) d).getD j 0 = -((κ : ℚ) / 2) + cPair R S := by
      intro j hj
      have := congrFun h1 (.inr ⟨j, hj⟩)
      simpa [shiftNu, ofBlocks] using this.symm
    obtain ⟨haB, hbB, hkB⟩ := forced a b P' _ hab hB
    obtain ⟨hcD, hdD, hkD⟩ := forced c d Q' _ hcd hD
    have ha0 := cast_neg_of pB ha haB
    have hc0 := cast_neg_of pD hc hcD
    subst ha0 hc0
    have hbl : b.length = P' := by
      by_contra hne
      have := hkB (by simp at hab ⊢; omega)
      linarith
    have hdl : d.length = Q' := by
      by_contra hne
      have := hkD (by simp at hcd ⊢; omega)
      linarith
    have hbmap := map_rep hbl hbB
    have hdmap := map_rep hdl hdD
    funext x
    have := congrFun h2 x
    rcases x with ⟨i, hi⟩ | ⟨j, hj⟩
    · simp only [shiftNu, ofBlocks, pad, List.map_append, List.map_replicate, hdmap, List.map_nil, List.nil_append,
        List.length_nil, getD_replicate_append, Int.cast_zero] at this
      simp only [GlobalTheory.RealLift.lam]
      subst hR hS
      unfold cPair at this ⊢
      push_cast at this ⊢
      split_ifs at this ⊢ <;> first | linarith | omega
    · simp only [shiftNu, ofBlocks, pad, List.map_append, List.map_replicate, hbmap, List.map_nil, List.nil_append,
        List.length_nil, getD_replicate_append, Int.cast_zero] at this
      simp only [GlobalTheory.RealLift.lam]
      subst hR hS
      unfold cPair at this ⊢
      push_cast at this ⊢
      rw [hbl] at this
      by_cases hjQ : j < Q
      · rw [if_pos (by omega)] at this
        rw [if_pos hjQ]
        linarith
      · rw [if_neg (by omega), if_pos (by omega)] at this
        rw [if_neg hjQ]
        linarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaSignMultiplicative
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.KapSignMul

variable {K : Type} [Field K]

theorem ordL_mul [Valued K (WithZero (Multiplicative ℤ))] {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hxy' : Valued.v (x * y) ≠ 0 := (Valuation.ne_zero_iff _).2 (mul_ne_zero hx hy)
  unfold ordL
  rw [dif_neg hx', dif_neg hy', dif_neg hxy']
  have : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, Valuation.map_mul]
  rw [this, toAdd_mul]
  ring

theorem sign_norm [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    {d : K} (hd : d ≠ 0) (x : K) : (-1 : ℂ) ^ ordL (σ d * d * x) = (-1 : ℂ) ^ ordL x := by
  by_cases hx : x = 0
  · simp [hx]
  have hσd : σ d ≠ 0 := (map_ne_zero σ).2 hd
  have hσo : ordL (σ d) = ordL d := by
    unfold ordL
    simp only [hσ]
  rw [ordL_mul (mul_ne_zero hσd hd) hx, ordL_mul hσd hd, hσo, zpow_add₀ (by norm_num), ← two_mul,
    (even_two_mul (ordL d)).neg_one_zpow, one_mul]

theorem li_coe {n : ℕ} {W : Submodule K (Fin n → K)} {ι : Type} (b : Module.Basis ι K W) :
    LinearIndependent K (fun i => (b i : Fin n → K)) :=
  b.linearIndependent.map' W.subtype W.ker_subtype

theorem span_coe {n : ℕ} {W : Submodule K (Fin n → K)} {ι : Type} (b : Module.Basis ι K W) :
    Submodule.span K (Set.range fun i => (b i : Fin n → K)) = W := by
  have : (Set.range fun i => (b i : Fin n → K)) = W.subtype '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem gram_change (σ : K →+* K) {n : ℕ} (W : Submodule K (Fin n → K)) {ι ι' : Type} [Fintype ι] [Fintype ι']
    [DecidableEq ι] [DecidableEq ι'] (u : ι → Fin n → K) (u' : ι' → Fin n → K) (hu : LinearIndependent K u)
    (hsu : Submodule.span K (Set.range u) = W) (hu' : LinearIndependent K u')
    (hsu' : Submodule.span K (Set.range u') = W) :
    ∃ d : K, d ≠ 0 ∧ (Matrix.of fun i j => ∑ k, σ (u' i k) * u' j k).det =
      σ d * d * (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det :=
  GlobalTheory.T.gram_det_change_of_basis' σ W u u' hu hsu hu' hsu'

theorem csr_orth (σ : K →+* K) {n : ℕ} (γ : Matrix (Fin n) (Fin n) K) (hγ : (γ.map σ)ᵀ * γ = 1) (Q : K[X])
    (hQ : C (σ (Q.coeff 0)) * Q = (Q.map σ).reverse) (x z : Fin n → K) (hx : aeval γ Q *ᵥ x = 0) :
    ∑ k, σ ((aeval γ Q *ᵥ z) k) * x k = 0 :=
  GlobalTheory.T.ker_aeval_orthogonal_range_unitary_selfReciprocal σ γ hγ Q hQ x z hx

theorem gram_ne_zero (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : ι → Fin n → K) (hu : LinearIndependent K u)
    (hsu : Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' A))
    (horth : ∀ x z, A *ᵥ x = 0 → ∑ k, σ ((A *ᵥ z) k) * x k = 0)
    (hdec : ∀ v, ∃ z y, A *ᵥ y = 0 ∧ v = A *ᵥ z + y) :
    (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det ≠ 0 :=
  GlobalTheory.T.gram_det_ne_zero_of_ker_orth' σ A u hu hsu horth hdec

theorem conj_ker (σ : K →+* K) {n : ℕ} (γ g : GL (Fin n) K) (hg : ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ * g = 1)
    (Q : K[X]) {ι : Type} (u : ι → Fin n → K) (hu : LinearIndependent K u)
    (hsu : Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) Q))) :
    LinearIndependent K (fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) ∧
      Submodule.span K (Set.range fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) =
        LinearMap.ker (Matrix.toLin' (aeval (γ : Matrix (Fin n) (Fin n) K) Q)) ∧
      (Matrix.of fun i j => ∑ k, σ (((g : Matrix (Fin n) (Fin n) K) *ᵥ u i) k) * ((g : Matrix (Fin n) (Fin n) K) *ᵥ u j) k) =
        Matrix.of fun i j => ∑ k, σ (u i k) * u j k :=
  GlobalTheory.T.unitary_conj_maps_ker_aeval_basis_and_gram σ γ g hg Q u hu hsu

end GlobalTheory.KapSignMul

namespace GlobalTheory.KapSignMul

variable {K : Type} [Field K]

theorem dec_of_dvd {n : ℕ} (γ : Matrix (Fin n) (Fin n) K) (Q : K[X]) (hsep : γ.charpoly.Separable)
    (hQ : Q ∣ γ.charpoly) : ∀ v, ∃ z y, aeval γ Q *ᵥ y = 0 ∧ v = aeval γ Q *ᵥ z + y := by
  obtain ⟨R, hR⟩ := hQ
  have hcop : IsCoprime Q R := Polynomial.Separable.isCoprime (by rw [← hR]; exact hsep)
  obtain ⟨a, c, hac⟩ := hcop
  intro v
  refine ⟨aeval γ a *ᵥ v, aeval γ (c * R) *ᵥ v, ?_, ?_⟩
  · rw [mulVec_mulVec, ← map_mul, show Q * (c * R) = c * (Q * R) by ring, ← hR, map_mul, aeval_self_charpoly,
      mul_zero, zero_mulVec]
  · rw [mulVec_mulVec, ← map_mul, ← add_mulVec, ← map_add, show Q * a + c * R = a * Q + c * R by ring, hac, map_one,
      one_mulVec]

theorem mem_im_of_coprime {n : ℕ} (γ : Matrix (Fin n) (Fin n) K) {Q₁ Q₂ : K[X]} (hcop : IsCoprime Q₁ Q₂)
    {y : Fin n → K} (hy : aeval γ Q₂ *ᵥ y = 0) : ∃ z, y = aeval γ Q₁ *ᵥ z := by
  obtain ⟨a, c, hac⟩ := hcop
  refine ⟨aeval γ a *ᵥ y, ?_⟩
  have : y = aeval γ (a * Q₁ + c * Q₂) *ᵥ y := by rw [hac, map_one, one_mulVec]
  rw [mulVec_mulVec, ← map_mul, mul_comm Q₁ a]
  conv_lhs => rw [this]
  rw [map_add, add_mulVec, map_mul (aeval γ) c, ← mulVec_mulVec, hy, mulVec_zero, add_zero]

theorem ker_toLin' {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (P : K[X]) :
    LinearMap.ker (Matrix.toLin' (aeval M P)) = LinearMap.ker (aeval (Matrix.toLin' M) P) := by
  congr 1
  exact (aeval_algHom_apply (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] _).toAlgHom M P).symm

theorem mem_UL {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E} (hs : ¬ IsSplitAt w) (γ : UL n w) :
    (((γ.1 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map (cj w))ᵀ * (γ.1 : GLw n w) = 1 := by
  have := γ.2
  simp only [UL, if_neg hs] at this
  simpa [UJ, cT] using this

theorem mul_sign [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (hM : (M.map σ)ᵀ * M = 1) {Q₁ Q₂ : K[X]} (hsep : M.charpoly.Separable)
    (hdvd : Q₁ * Q₂ ∣ M.charpoly) (hcop : IsCoprime Q₁ Q₂) (hQ₁ : C (σ (Q₁.coeff 0)) * Q₁ = (Q₁.map σ).reverse)
    (hQ₂ : C (σ (Q₂.coeff 0)) * Q₂ = (Q₂.map σ).reverse) {ι₁ ι₂ ι : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι]
    [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι]
    (b₁ : Module.Basis ι₁ K (LinearMap.ker (Matrix.toLin' (aeval M Q₁))))
    (b₂ : Module.Basis ι₂ K (LinearMap.ker (Matrix.toLin' (aeval M Q₂))))
    (b : Module.Basis ι K (LinearMap.ker (Matrix.toLin' (aeval M (Q₁ * Q₂))))) :
    (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b i : Fin n → K) k) * (b j : Fin n → K) k).det =
      (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b₁ i : Fin n → K) k) * (b₁ j : Fin n → K) k).det *
      (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b₂ i : Fin n → K) k) * (b₂ j : Fin n → K) k).det := by
  have hsup : LinearMap.ker (Matrix.toLin' (aeval M Q₁)) ⊔ LinearMap.ker (Matrix.toLin' (aeval M Q₂)) =
      LinearMap.ker (Matrix.toLin' (aeval M (Q₁ * Q₂))) := by
    simp only [ker_toLin']
    exact sup_ker_aeval_eq_ker_aeval_mul_of_coprime _ hcop
  have hdis : Disjoint (LinearMap.ker (Matrix.toLin' (aeval M Q₁))) (LinearMap.ker (Matrix.toLin' (aeval M Q₂))) := by
    simp only [ker_toLin']
    exact disjoint_ker_aeval_of_isCoprime _ hcop
  have hli : LinearIndependent K (Sum.elim (fun i => (b₁ i : Fin n → K)) (fun i => (b₂ i : Fin n → K))) :=
    (li_coe b₁).sum_type (li_coe b₂) (by rw [span_coe, span_coe]; exact hdis)
  have hsp : Submodule.span K (Set.range (Sum.elim (fun i => (b₁ i : Fin n → K)) (fun i => (b₂ i : Fin n → K)))) =
      LinearMap.ker (Matrix.toLin' (aeval M (Q₁ * Q₂))) := by
    rw [Set.Sum.elim_range, Submodule.span_union, span_coe, span_coe, hsup]
  obtain ⟨d, hd, hdet⟩ := gram_change σ _ _ (fun i => (b i : Fin n → K)) hli hsp (li_coe b) (span_coe b)
  have hblk : (Matrix.of fun i j => ∑ k, σ ((Sum.elim (fun i => (b₁ i : Fin n → K)) (fun i => (b₂ i : Fin n → K)) i) k) *
      (Sum.elim (fun i => (b₁ i : Fin n → K)) (fun i => (b₂ i : Fin n → K)) j) k) =
      fromBlocks (Matrix.of fun i j => ∑ k, σ ((b₁ i : Fin n → K) k) * (b₁ j : Fin n → K) k)
        (Matrix.of fun i j => ∑ k, σ ((b₁ i : Fin n → K) k) * (b₂ j : Fin n → K) k) 0
        (Matrix.of fun i j => ∑ k, σ ((b₂ i : Fin n → K) k) * (b₂ j : Fin n → K) k) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · simp only [fromBlocks_apply₂₁, Matrix.zero_apply, of_apply, Sum.elim_inr, Sum.elim_inl]
      have hy : aeval M Q₂ *ᵥ (b₂ i : Fin n → K) = 0 := by
        have := (b₂ i).2; rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
      have hx : aeval M Q₁ *ᵥ (b₁ j : Fin n → K) = 0 := by
        have := (b₁ j).2; rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
      obtain ⟨z, hz⟩ := mem_im_of_coprime M hcop hy
      rw [hz]
      exact csr_orth σ M hM Q₁ hQ₁ _ z hx
    · rfl
  rw [hblk, det_fromBlocks_zero₂₁] at hdet
  have h1 := gram_ne_zero σ (aeval M Q₁) _ (li_coe b₁) (span_coe b₁)
    (fun x z hx => csr_orth σ M hM Q₁ hQ₁ x z hx) (dec_of_dvd M Q₁ hsep (dvd_trans (dvd_mul_right _ _) hdvd))
  have h2 := gram_ne_zero σ (aeval M Q₂) _ (li_coe b₂) (span_coe b₂)
    (fun x z hx => csr_orth σ M hM Q₂ hQ₂ x z hx) (dec_of_dvd M Q₂ hsep (dvd_trans (dvd_mul_left _ _) hdvd))
  rw [hdet, sign_norm σ hσ hd, ordL_mul h1 h2, zpow_add₀ (by norm_num)]

theorem conj_sign [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    {n : ℕ} (γ g : GL (Fin n) K) (hg : ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ * g = 1) (Q : K[X])
    {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (b' : Module.Basis ι' K (LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) Q))))
    (b : Module.Basis ι K (LinearMap.ker (Matrix.toLin' (aeval (γ : Matrix (Fin n) (Fin n) K) Q)))) :
    (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b' i : Fin n → K) k) * (b' j : Fin n → K) k).det =
      (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b i : Fin n → K) k) * (b j : Fin n → K) k).det := by
  obtain ⟨hli, hsp, hgr⟩ := conj_ker σ γ g hg Q _ (li_coe b') (span_coe b')
  obtain ⟨d, hd, hdet⟩ := gram_change σ _ _ _ (li_coe b) (span_coe b) hli hsp
  rw [hgr] at hdet
  rw [hdet, sign_norm σ hσ hd]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (w : Pl E) (Q₁ Q₂ Q₃ : (w.adicCompletion E)[X]) (γ g : UL n w), γ.1.val.charpoly.Separable → Q₁ * Q₂ ∣ γ.1.val.charpoly → IsCoprime Q₁ Q₂ → IsCsr w Q₁ → IsCsr w Q₂ → kapSign n w (Q₁ * Q₂) γ.1 = kapSign n w Q₁ γ.1 * kapSign n w Q₂ γ.1 ∧ kapSign n w Q₃ (g⁻¹ * γ * g).1 = kapSign n w Q₃ γ.1 ∧ (kapSign n w Q₃ γ.1 = 1 ∨ kapSign n w Q₃ γ.1 = -1) := by
  intro E _ _ _ hU n _ w Q₁ Q₂ Q₃ γ g hsep hdvd hcop hc1 hc2
  by_cases hs : IsSplitAt w
  · simp [kapSign, hs]
  have hv := (GlobalTheory.ConjAtPlace.main E hU w).2.2.1
  have hQ₁ : C (cj w (Q₁.coeff 0)) * Q₁ = (Q₁.map (cj w)).reverse := hc1.resolve_left hs
  have hQ₂ : C (cj w (Q₂.coeff 0)) * Q₂ = (Q₂.map (cj w)).reverse := hc2.resolve_left hs
  refine ⟨?_, ?_, ?_⟩
  · simp only [kapSign, if_neg hs]
    exact mul_sign (cj w) hv _ (mem_UL hs γ) hsep hdvd hcop hQ₁ hQ₂ _ _ _
  · simp only [kapSign, if_neg hs]
    have hg' : ((g⁻¹ * γ * g : UL n w) : GLw n w) = (g : GLw n w)⁻¹ * γ * g := by simp
    rw [hg']
    exact conj_sign (cj w) hv γ.1 g.1 (mem_UL hs g) Q₃ _ _
  · simp only [kapSign, if_neg hs]
    rcases Int.even_or_odd (ordL (Matrix.of fun i j => ∑ k, cj w ((Module.finBasis (w.adicCompletion E)
      (LinearMap.ker (Matrix.toLin' (aeval γ.1.val Q₃))) i).1 k) * (Module.finBasis (w.adicCompletion E)
      (LinearMap.ker (Matrix.toLin' (aeval γ.1.val Q₃))) j).1 k).det) with h | h
    · exact Or.inl h.neg_one_zpow
    · exact Or.inr h.neg_one_zpow

end GlobalTheory.KapSignMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesLeft
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

open scoped TensorProduct
open Matrix
namespace GlobalTheory.AdelMatLat

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsLattice E) (v : Fin n → E) : ∃ d : ℤ, d ≠ 0 ∧ d • v ∈ L := by
  have hv : v ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, h₁, hx⟩ := hx
    obtain ⟨d₂, h₂, hy⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero h₁ h₂, ?_⟩
    have : (d₁ * d₂) • (x + y) = d₂ • (d₁ • x) + d₁ • (d₂ • y) := by
      rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
    rw [this]
    exact add_mem (zsmul_mem hx _) (zsmul_mem hy _)
  | smul e x _ hx =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨m, hm, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
    let o : 𝓞 E := ⟨m • e, (hint e (Finset.mem_singleton_self e) :)⟩
    refine ⟨m * d, mul_ne_zero hm hd, ?_⟩
    have : (m * d) • (e • x) = o • (d • x) := by
      have ho : algebraMap (𝓞 E) E o = m • e := rfl
      rw [← algebraMap_smul E o (d • x), ho, smul_assoc, smul_comm e d x, mul_smul]
    rw [this]
    exact L.smul_mem o hx

theorem exists_int_mulVec_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsLattice E) (N : Matrix (Fin n) (Fin n) E) : ∃ D : ℤ, D ≠ 0 ∧ ∀ x ∈ L, D • (N *ᵥ x) ∈ L := by
  obtain ⟨s, hs⟩ := hL.fg
  choose d hd hdm using fun g : Fin n → E => exists_int_smul_mem L hL (N *ᵥ g)
  refine ⟨∏ g ∈ s, d g, Finset.prod_ne_zero_iff.2 fun g _ => hd g, ?_⟩
  let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) := ((∏ g ∈ s, d g) • N.mulVecLin).restrictScalars (𝓞 E)
  have hf : ∀ x, f x = (∏ g ∈ s, d g) • (N *ᵥ x) := fun x => rfl
  have hle : Submodule.span (𝓞 E) (s : Set (Fin n → E)) ≤ L.comap f := by
    rw [Submodule.span_le]
    intro g hg
    simp only [SetLike.mem_coe, Submodule.mem_comap, hf]
    classical
    rw [← Finset.mul_prod_erase s d hg, mul_comm, mul_smul]
    exact zsmul_mem (hdm g) _
  intro x hx
  rw [← hs] at hx
  have := hle hx
  rwa [Submodule.mem_comap, hf] at this

theorem incM_zsmul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m k : Type}
    (D : ℤ) (V : Matrix m k E) : incM F (D • V) = (algebraMap F (AF F) (D : F)) • incM F V := by
  ext i j
  simp only [incM, Matrix.map_apply, Matrix.smul_apply, map_zsmul, algebraMap_smul, Int.cast_smul_eq_zsmul]

theorem smul_incM_mul_stable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (c : AF F) (N : Matrix (Fin n) (Fin n) E) (D : ℤ) (hD0 : D ≠ 0)
    (hD : ∀ x ∈ X.L, D • (N *ᵥ x) ∈ X.L) (w : Pl F)
    (hw : evFin F w (c * algebraMap F (AF F) (D : F)⁻¹) ∈ w.adicCompletionIntegers F) :
    ∀ γ ∈ latAtV X Y w, (c • incM F N) * γ ∈ latAtV X Y w := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hint, x, hx, y, hy, rfl⟩ := hz
    have hDF : (D : F) ≠ 0 := Int.cast_ne_zero.2 hD0
    have heq : (c • incM F N) * (a • incM F (Matrix.vecMulVec x y)) =
        ((c * algebraMap F (AF F) (D : F)⁻¹) * a) • incM F (Matrix.vecMulVec (D • (N *ᵥ x)) y) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_vecMulVec, incM_zsmul, smul_smul,
        ← Matrix.mul_vecMulVec]
      have hm : incM F (N * Matrix.vecMulVec x y) = incM F N * incM F (Matrix.vecMulVec x y) := by
        simp only [incM, Matrix.map_mul]
      rw [hm]
      congr 1
      rw [mul_right_comm, mul_assoc c, ← map_mul, inv_mul_cancel₀ hDF, map_one, mul_one]
    rw [heq]
    refine AddSubgroup.subset_closure ⟨_, ?_, ?_, _, hD x hx, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]
      exact mul_mem hw hint
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

theorem finite_not_integral {F : Type} [Field F] [NumberField F] (c : AF F) :
    {w : Pl F | evFin F w c ∉ w.adicCompletionIntegers F}.Finite :=
  Filter.eventually_cofinite.1 c.2.2

theorem finite_bad_smul_incM {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (hX : X.L.IsLattice E) (c : AF F) (N : Matrix (Fin n) (Fin n) E) :
    {w : Pl F | ¬ ∀ γ ∈ latAtV X Y w, (c • incM F N) * γ ∈ latAtV X Y w}.Finite := by
  obtain ⟨D, hD0, hD⟩ := exists_int_mulVec_mem X.L hX N
  refine (finite_not_integral (c * algebraMap F (AF F) (D : F)⁻¹)).subset ?_
  intro w hw hint
  exact hw (smul_incM_mul_stable X Y c N D hD0 hD w hint)

theorem almost_all_stable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : Spc F E n) (Y : Spc F E d), X.L.IsLattice E → ∀ M : Matrix (Fin n) (Fin n) (AE F E),
    Set.Finite {w : Pl F | ¬ ∀ γ ∈ latAtV X Y w, M * γ ∈ latAtV X Y w} := by
  intro F E _ _ _ _ _ n d X Y hX M
  let bad : Matrix (Fin n) (Fin n) (AE F E) → Set (Pl F) :=
    fun M => {w | ¬ ∀ γ ∈ latAtV X Y w, M * γ ∈ latAtV X Y w}
  have hadd : ∀ M M', (bad M).Finite → (bad M').Finite → (bad (M + M')).Finite := by
    intro M M' h h'
    refine (h.union h').subset fun w hw => ?_
    by_contra hc
    simp only [Set.mem_union, not_or, bad, Set.mem_setOf_eq, not_not] at hc hw
    exact hw fun γ hγ => by rw [Matrix.add_mul]; exact add_mem (hc.1 γ hγ) (hc.2 γ hγ)
  have hzero : (bad 0).Finite := by
    refine Set.finite_empty.subset fun w hw => hw fun γ _ => ?_
    rw [Matrix.zero_mul]; exact zero_mem _
  have hsingle : ∀ i j (t : AE F E), (bad (Matrix.single i j t)).Finite := by
    intro i j t
    induction t using TensorProduct.induction_on with
    | zero => rw [Matrix.single_zero]; exact hzero
    | tmul a e =>
      have h : Matrix.single i j (a ⊗ₜ[F] e) = a • incM F (Matrix.single i j e) := by
        ext k l
        simp only [incM, Matrix.map_apply, Matrix.smul_apply, Matrix.single_apply]
        split_ifs <;> simp [inclR, TensorProduct.smul_tmul']
      rw [h]
      exact finite_bad_smul_incM X Y hX a _
    | add t t' ht ht' => rw [Matrix.single_add]; exact hadd _ _ ht ht'
  show (bad M).Finite
  rw [Matrix.matrix_eq_sum_single M]
  exact Finset.sum_induction _ (fun M => (bad M).Finite) hadd hzero fun i _ =>
    Finset.sum_induction _ (fun M => (bad M).Finite) hadd hzero fun j _ => hsingle i j _

end GlobalTheory.AdelMatLat

end
end

