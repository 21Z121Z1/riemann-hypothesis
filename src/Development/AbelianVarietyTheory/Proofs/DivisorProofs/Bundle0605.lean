import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0586
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Numeric
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Formalism.PieriBlockIdeals.PieriColumnMinors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0594
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviWhittakerColumnCharacterEigenVecMulNeBot
section
noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open GlobalTheory.FinGL Formalism.L2.DIV Module

section Mat

variable {F : Type} [Field F] {r : ℕ} {k : Fin r} {H U : Matrix (Fin r) (Fin r) F}

theorem corner_row (hH : ∀ i j, H i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k)
    (N : Matrix (Fin r) (Fin r) F) {i : Fin r} (hi : ¬ i < k) (j : Fin r) : (H * N) i j = N i j := by
  have : (H * N) i j = ((1 : Matrix (Fin r) (Fin r) F) * N) i j := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    have : H i m = (1 : Matrix (Fin r) (Fin r) F) i m := by
      by_contra hne
      exact hi (hH i m hne).1
    rw [this]
  rw [this, one_mul]

theorem corner_nil_mul (hH : ∀ i j, H i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k)
    (hU : ∀ i j : Fin r, j.val < k.val → U i j = (1 : Matrix (Fin r) (Fin r) F) i j) :
    (U - 1) * H = U - 1 := by
  conv_rhs => rw [← mul_one (U - 1)]
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : m < k
  · rw [Matrix.sub_apply, hU i m hm, sub_self, zero_mul, zero_mul]
  · have : H m j = (1 : Matrix (Fin r) (Fin r) F) m j := by
      by_contra hne
      exact hm (hH m j hne).1
    rw [this]

end Mat

variable {F : Type} [Field F] {r : ℕ}

theorem corner_conj_val {k : Fin r} (h u : GL (Fin r) F)
    (hH : ∀ i j, (h : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k)
    (hU : ∀ i j : Fin r, j.val < k.val → (u : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) :
    ((h * u * h⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      1 + (h : Matrix (Fin r) (Fin r) F) * ((u : Matrix (Fin r) (Fin r) F) - 1) := by
  rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul, add_mul, mul_assoc, corner_nil_mul hH hU, Units.val_mul,
    mul_sub, one_mul, mul_one, add_sub_cancel]

theorem corner_conj {k : Fin r} (h u : GL (Fin r) F)
    (hH : ∀ i j, (h : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k)
    (hU : ∀ i j : Fin r, j.val < k.val → (u : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) :
    (∀ i j : Fin r, ¬ i < k → ((h * u * h⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
      (u : Matrix (Fin r) (Fin r) F) i j) ∧
    (∀ i j : Fin r, j.val < k.val → ((h * u * h⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
      (1 : Matrix (Fin r) (Fin r) F) i j) ∧
    (∀ i : Fin r, ((h * u * h⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k =
      ((h : Matrix (Fin r) (Fin r) F) * (u : Matrix (Fin r) (Fin r) F)) i k) := by
  rw [corner_conj_val h u hH hU]
  refine ⟨fun i j hi => ?_, fun i j hj => ?_, fun i => ?_⟩
  · rw [Matrix.add_apply, corner_row hH _ hi, Matrix.sub_apply, add_sub_cancel]
  · rw [Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero, add_zero]
    intro m _
    rw [Matrix.sub_apply, hU m j hj, sub_self, mul_zero]
  · have : (h : Matrix (Fin r) (Fin r) F) i k = (1 : Matrix (Fin r) (Fin r) F) i k := by
      by_contra hne
      exact lt_irrefl _ (hH i k hne).2
    rw [mul_sub, mul_one, Matrix.add_apply, Matrix.sub_apply, this, add_sub_cancel]

theorem eig_colChar_vecMul_ne_bot (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (k : Fin r) (l : Fin r → F)
    (h : blockTri (κ := F) b)
    (hH : ∀ i j, ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j →
      i < k ∧ j < k)
    (hne : eig σ (colSet F b k.val) (colChar ψ b k l) ≠ ⊥) :
    eig σ (colSet F b k.val)
      (colChar ψ b k (Matrix.vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F))) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff] at hne ⊢
  obtain ⟨v, hv, hv0⟩ := hne
  rw [mem_eig] at hv
  refine ⟨σ h⁻¹ v, ?_, fun h0 => hv0 ?_⟩
  · rw [mem_eig]
    rintro u ⟨hu, hU⟩
    obtain ⟨c1, c2, c3⟩ := corner_conj (h : GL (Fin r) F) (u : GL (Fin r) F) hH hU
    have hc : ((h * u * h⁻¹ : blockTri (κ := F) b) : GL (Fin r) F) =
        (h : GL (Fin r) F) * (u : GL (Fin r) F) * (h : GL (Fin r) F)⁻¹ := rfl
    have hmem : h * u * h⁻¹ ∈ colSet F b k.val := by
      refine ⟨?_, ?_⟩
      · rw [hc]
        refine ⟨fun i j hij => ?_, fun i => ?_⟩
        · have hij' : j < i := hij
          by_cases hj : j < k
          · rw [c2 i j hj, Matrix.one_apply_ne (ne_of_gt hij')]
          · rw [c1 i j (fun hi => hj (hij'.trans hi)), unip_lower hu hij']
        · by_cases hi : i < k
          · rw [c2 i i hi, Matrix.one_apply_eq]
          · rw [c1 i i hi, unip_diag hu]
      · rw [hc]; exact c2
    have hχ : colChar ψ b k l (h * u * h⁻¹) =
        colChar ψ b k (Matrix.vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) u := by
      unfold colChar
      rw [hc]
      congr 2
      · simp only [c3]
        have := congrFun (Matrix.vecMul_vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)
          ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) k
        exact this.symm
      · unfold edgeSum
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        split_ifs with hij
        · refine c1 i j fun hi => ?_
          have h1 : j.val = i.val + 1 := hij.1.1
          have h2 : k.val < j.val := hij.2
          have h3 : i.val < k.val := hi
          omega
        · rfl
    have e : σ u (σ h⁻¹ v) = σ h⁻¹ (σ (h * u * h⁻¹) v) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [e, hv _ hmem, map_smul, hχ]
  · have : σ h (σ h⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← this, h0, map_zero]

end GlobalTheory.FinGL.LeviWh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultSharpOfPlaceBound
section
noncomputable section

namespace GlobalTheory.FinGL.MultSharpPf

open GlobalTheory.FinGL Formalism.L2.DIV Module NumberField GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity

def PlaceBound : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ →
    ∀ ρ k : ℕ, 1 ≤ k → ρ + k + 1 ≤ r → r ≤ Fintype.card F →
      (Fintype.card F : ℝ) ^ k * (1 - 1 / (Fintype.card F : ℝ)) ≤ (nPos ψ (parInd b σ) ρ k : ℝ) ∧
      (nPos ψ (parInd b σ) ρ k : ℝ) ≤ (Fintype.card F : ℝ) ^ k * (1 + (2 * (r : ℝ) - 1) / (Fintype.card F : ℝ))

theorem mem_eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G) (χ : G → ℂ)
    (v : V) : v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem card_mul_finrank_eig {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : Representation ℂ G V) (P : Subgroup G) [Fintype P] (ψ : G → ℂ) (h1 : ψ 1 = 1)
    (hm : ∀ x ∈ P, ∀ y ∈ P, ψ (x * y) = ψ x * ψ y) :
    (Fintype.card P : ℂ) * (finrank ℂ (eig τ (P : Set G) ψ) : ℂ) =
      ∑ h : P, LinearMap.trace ℂ V (τ h) * (ψ h)⁻¹ := by
  have hc : (Fintype.card P : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h0 : ∀ x ∈ P, ψ x ≠ 0 := fun x hx e => by
    have := hm x hx x⁻¹ (P.inv_mem hx)
    rw [mul_inv_cancel, h1, e, zero_mul] at this
    exact one_ne_zero this
  set e : V →ₗ[ℂ] V := (Fintype.card P : ℂ)⁻¹ • ∑ h : P, (ψ h)⁻¹ • (τ h : V →ₗ[ℂ] V) with he
  have hp : LinearMap.IsProj (eig τ (P : Set G) ψ) e := by
    constructor
    · intro v
      rw [mem_eig]
      intro g hg
      have hg' : g ∈ P := hg
      simp only [he, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply, map_smul, map_sum]
      rw [smul_comm (ψ g)]
      congr 1
      rw [Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg'⟩ : P)) _ _ fun x => ?_
      simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
      rw [hm g hg' x x.2, smul_smul, mul_inv, ← mul_assoc, mul_inv_cancel₀ (h0 g hg'), one_mul]
    · intro v hv
      rw [mem_eig] at hv
      simp only [he, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]
      rw [Finset.sum_congr rfl (g := fun _ => v) fun x _ => by
        rw [hv x x.2, smul_smul, inv_mul_cancel₀ (h0 x x.2), one_smul]]
      rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [← hp.trace, he, map_smul, map_sum, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

variable {E : Type} [Field E] [NumberField E]

def piEquiv {Pg : Finset (Pl E)} {r : ℕ} (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) :
    (Subgroup.pi Set.univ Hl : Subgroup (G0 Pg r)) ≃ ∀ PP : ↥Pg, Hl PP where
  toFun x PP := LevelP.prj Hl PP x
  invFun y := ⟨fun PP => y PP, fun PP _ => (y PP).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem levelMult_ofLocal {K : Type} [Field K] (s : K →+* ℂ) {Pg : Finset (Pl E)} {r : ℕ}
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) [∀ PP, Fintype (Hl PP)] (cl : ∀ PP : ↥Pg, Hl PP →* Kˣ)
    (χ : G0 Pg r → K) (θ : ∀ PP : ↥Pg, GL (Fin r) (kP PP.1) → ℂ) (hχ : ∀ x, s (χ x) = ∏ PP : ↥Pg, θ PP (x PP))
    (n : ↥Pg → ℕ)
    (hn : ∀ PP, (Fintype.card (Hl PP) : ℂ) * (n PP : ℂ) = ∑ h : Hl PP, θ PP h * (s (cl PP h : K))⁻¹) :
    levelMult (LevelP.ofLocal Hl cl) χ = ((∏ PP, n PP : ℕ) : K) := by
  classical
  apply s.injective
  unfold levelMult
  rw [map_mul, map_inv₀, map_natCast, map_natCast, map_sum]
  have hcard : Nat.card (LevelP.ofLocal Hl cl).H = ∏ PP, Fintype.card (Hl PP) := by
    rw [← Fintype.card_pi, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (piEquiv Hl)
  have hne : (∏ PP, (Fintype.card (Hl PP) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun PP _ => by exact_mod_cast Fintype.card_ne_zero
  rw [hcard, Nat.cast_prod, Nat.cast_prod, inv_mul_eq_iff_eq_mul₀ hne, ← Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun PP _ => hn PP, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine @Fintype.sum_equiv _ _ _ (_) _ _ (piEquiv Hl) _ _ fun x => ?_
  rw [map_mul, hχ, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Units.val_inv_eq_inv_val, map_inv₀]
  congr 2
  show s ((((∏ PP : ↥Pg, (cl PP).comp (LevelP.prj Hl PP)) x : Kˣ)) : K) = _
  rw [MonoidHom.finset_prod_apply, Units.coe_prod, map_prod]
  rfl

theorem edgeSum_sup_eq {κ : Type} [CommRing κ] {r k : ℕ} {g : GL (Fin r) κ} (hg : g ∈ unipCol κ r 0 k) :
    edgeSum supEdge g = edgeSum (symEdge 0 k) g := by
  unfold edgeSum
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : supEdge i j <;> by_cases h2 : symEdge 0 k i j
  · rw [if_pos h1, if_pos h2]
  · rw [if_pos h1, if_neg h2]
    unfold supEdge at h1
    unfold symEdge at h2
    exact hg.2 i j (Nat.zero_le _) (by omega) (by omega)
  · unfold supEdge at h1
    unfold symEdge at h2
    omega
  · rw [if_neg h1, if_neg h2]

theorem addCharHom_sym {κ : Type} [CommRing κ] {K : Type} [CommRing K] {r ρ k : ℕ} (ψ : AddChar κ K) (h : unipSym κ r ρ k) :
    (addCharHom ψ (symHom κ r ρ k) h : K) = ψ (edgeSum (symEdge ρ k) (h : GL (Fin r) κ)) := rfl

theorem addCharHom_first {κ : Type} [CommRing κ] {K : Type} [CommRing K] {r k : ℕ} (ψ : AddChar κ K) (h : unipCol κ r 0 k) :
    ((addCharHom ψ (supHom κ r)).comp (Subgroup.inclusion (unipCol_le r 0 k)) h : K) =
      ψ (edgeSum (symEdge 0 k) (h : GL (Fin r) κ)) := by
  rw [← edgeSum_sup_eq h.2]
  rfl

theorem place (H : PlaceBound) {κ : Type} [Field κ] [Finite κ] {K : Type} [Field K] (s : K →+* ℂ) (ψ : AddChar κ K)
    (hψ : ψ ≠ 1) {r ρ k : ℕ} (hk : 1 ≤ k) (hr : ρ + k + 1 ≤ r) (hq : r ≤ Nat.card κ) (θ : GL (Fin r) κ → ℂ)
    (hθ : IsCuspProdChar θ) [Fintype (unipSym κ r ρ k)] :
    ∃ n : ℕ, (Fintype.card (unipSym κ r ρ k) : ℂ) * (n : ℂ) =
        ∑ h : unipSym κ r ρ k, θ h * (s (ψ (edgeSum (symEdge ρ k) (h : GL (Fin r) κ))))⁻¹ ∧
      (Nat.card κ : ℝ) ^ k * (1 - 1 / (Nat.card κ : ℝ)) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ (Nat.card κ : ℝ) ^ k * (1 + (2 * (r : ℝ) - 1) / (Nat.card κ : ℝ)) := by
  obtain ⟨d, b, σ, hσ, hθ⟩ := hθ
  letI : Fintype κ := Fintype.ofFinite κ
  set φ : AddChar κ ℂ := s.toMonoidHom.compAddChar ψ with hφ
  have hφa : ∀ x, φ x = s (ψ x) := fun _ => rfl
  have hφ1 : φ ≠ 1 := fun e => hψ (by
    ext x
    apply s.injective
    rw [← hφa, e]; simp)
  rw [Nat.card_eq_fintype_card] at hq ⊢
  refine ⟨nPos φ (parInd b σ) ρ k, ?_, H κ φ hφ1 r _ b σ hσ ρ k hk hr hq⟩
  unfold nPos
  rw [card_mul_finrank_eig (parInd b σ) (unipSym κ r ρ k) (fun g => φ (edgeSum (symEdge ρ k) g))]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [hθ]; rfl
  · have := (symHom κ r ρ k).map_one
    have h2 : edgeSum (symEdge ρ k) (1 : GL (Fin r) κ) = 0 := this
    simp only [h2, AddChar.map_zero_eq_one]
  · intro x hx y hy
    have := (symHom κ r ρ k).map_mul ⟨x, hx⟩ ⟨y, hy⟩
    have h2 : edgeSum (symEdge ρ k) (x * y) = edgeSum (symEdge ρ k) x + edgeSum (symEdge ρ k) y := this
    simp only [h2, AddChar.map_add_eq_mul]

theorem places (H : PlaceBound) {K : Type} [Field K] (s : K →+* ℂ) (Pg : Finset (Pl E)) (f g r ρ k c : ℕ) (hc : c = ρ + k)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) K) (hf : Pg.card = 2 * f) (hk : 1 ≤ k) (hr : ρ + k + 1 ≤ r) (hg : 0 < g)
    (hfg : 4 * f * r ≤ g) (hq : ∀ PP ∈ Pg, g ≤ Nat.card (kP PP)) (hψ : IsGenericPsi Pg ψ)
    (cl : ∀ PP : ↥Pg, unipCol (kP PP.1) r ρ c →* Kˣ)
    (hcl : ∀ PP h, (cl PP h : K) = ψ PP.1 (edgeSum (symEdge ρ k) (h : GL (Fin r) (kP PP.1))))
    (χ : G0 Pg r → K) (hχ : IsProdCuspChar s Pg r χ) :
    MultNear (LevelP.ofLocal (fun PP => unipCol (kP PP.1) r ρ c) cl) χ (nbar Pg k) (8 * f * r / g) := by
  subst hc
  obtain ⟨θ, hθ, hχ⟩ := hχ
  have hfin : ∀ PP : ↥Pg, Finite (kP PP.1) := fun PP => finite_kP PP.1
  letI : ∀ PP : ↥Pg, Fintype (unipCol (kP PP.1) r ρ (ρ + k)) := fun PP => Fintype.ofFinite _
  have hrq : ∀ PP : ↥Pg, r ≤ Nat.card (kP PP.1) := fun PP => by
    have h1 : 0 < Pg.card := Finset.card_pos.2 ⟨PP.1, PP.2⟩
    have h2 : 1 ≤ 4 * f := by omega
    exact le_trans (le_trans (Nat.le_mul_of_pos_left r h2) hfg) (hq PP.1 PP.2)
  have hloc := fun PP : ↥Pg => @place H (kP PP.1) (Ideal.Quotient.field PP.1.asIdeal) (hfin PP) K _ s (ψ PP.1)
    (hψ PP.1 PP.2) r ρ k hk hr (hrq PP) (θ PP) (hθ PP) (this PP)
  choose n hn hb using hloc
  refine ⟨∏ PP, n PP, levelMult_ofLocal s _ cl χ θ hχ n fun PP => ?_, ?_⟩
  · simp only [hcl]
    exact hn PP
  · have := Formalism.BranchingDeterminantCap.multiplicity_product ↥Pg (fun PP => (Nat.card (kP PP.1) : ℝ)) (fun PP => (n PP : ℝ)) k f r g
      (by rw [Fintype.card_coe, hf]; push_cast; rfl) (by exact_mod_cast (by omega : 1 ≤ r)) (by exact_mod_cast hg)
      (fun PP => by exact_mod_cast hq PP.1 PP.2) (by exact_mod_cast hfg) hb
    have e : (nbar Pg k : ℝ) = ∏ PP : ↥Pg, (Nat.card (kP PP.1) : ℝ) ^ k := by
      unfold nbar
      rw [← Finset.prod_coe_sort Pg]; push_cast; rfl
    rw [e, Nat.cast_prod, abs_le]
    constructor <;> linarith [this.1, this.2]

theorem multSharp_of_placeBound (H : PlaceBound) : MultSharp := by
  intro E _ _ K _ _ s Pg f g r ρ k ψ hf hk hr hg hfg hq hψ χ hχ
  constructor
  · unfold PsharpSym
    exact places H s Pg f g r ρ k (ρ + k) rfl ψ hf hk (by omega) hg hfg hq hψ
      (fun PP => addCharHom (ψ PP.1) (symHom (kP PP.1) r ρ k)) (fun PP h => addCharHom_sym _ h) χ hχ
  · unfold Psharp
    exact places H s Pg f g r 0 k k (Nat.zero_add k).symm ψ hf hk (by omega) hg hfg hq hψ
      (fun PP => (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (Subgroup.inclusion (unipCol_le r 0 k)))
      (fun PP h => addCharHom_first _ h) χ hχ

end GlobalTheory.FinGL.MultSharpPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
section
open MvPolynomial Formalism.GradedWeylDivisibility TensorProduct

noncomputable section

namespace GlobalTheory.LeviCut

def GlRel (N : ℕ) {A : Type} [Ring A] (e : ℕ → ℕ → A) : Prop :=
  ∀ a b c d : ℕ, a < N → b < N → c < N → d < N →
    e a b * e c d - e c d * e a b = (if b = c then e a d else 0) - (if d = a then e c b else 0)

def coef (j k : ℕ) : ℚ := (-1) ^ k * (j.factorial : ℚ) / ((k.factorial : ℚ) * ((k + j + 1).factorial : ℚ))

def proj {A : Type} [Ring A] [Algebra ℚ A] (K j : ℕ) (X Y : A) : A :=
  ∑ k ∈ Finset.range (K + 1), coef j k • (Y ^ k * X ^ k)

def rootP {A : Type} [Ring A] [Algebra ℚ A] (D : ℕ → ℕ → A) (K i j : ℕ) : A :=
  proj K (j - i - 1) (D i j) (D j i)

def rowP {A : Type} [Ring A] [Algebra ℚ A] (D : ℕ → ℕ → A) (K i s n : ℕ) : A :=
  ((List.range' s n).map (rootP D K i)).prod

def gridP {A : Type} [Ring A] [Algebra ℚ A] (D : ℕ → ℕ → A) (K a b t : ℕ) : A :=
  ((List.range t).reverse.map fun i => rowP D K i a b).prod

def adj {A : Type} [Ring A] [Algebra ℚ A] (x : A) : Module.End ℚ A :=
  LinearMap.mulLeft ℚ x - LinearMap.mulRight ℚ x

def IsWt (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) (μ : ℕ → ℤ) (x : V) : Prop :=
  ∀ c < N, e c c x = (μ c : ℚ) • x

def Bdd (N K : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) : Prop :=
  ∀ a < N, ∀ b < N, ∀ (n : ℤ) (x : V), e a a x - e b b x = (n : ℚ) • x → (K : ℤ) < n → x = 0

def Dom (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) (lam : ℕ → ℤ) : Prop :=
  ∀ (μ : ℕ → ℤ) (x : V), IsWt N e μ x → x ≠ 0 →
    (∀ k ≤ N, ∑ c ∈ Finset.range k, μ c ≤ ∑ c ∈ Finset.range k, lam c) ∧
      ∑ c ∈ Finset.range N, μ c = ∑ c ∈ Finset.range N, lam c

def WtSpan (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V) : Prop :=
  Submodule.span ℚ {x : V | ∃ μ : ℕ → ℤ, IsWt N e μ x} = ⊤

def DivStable (N : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (e : ℕ → ℕ → Module.End ℚ V)
    (L : Submodule ℤ V) : Prop :=
  ∀ i < N, ∀ j < N, i ≠ j → ∀ k : ℕ, ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • (e i j ^ k) x ∈ L

def RankOne : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (N K : ℕ) (D : ℕ → ℕ → Module.End ℚ W), GlRel N D → Bdd N (2 * K) D →
    ∀ o q : ℕ, o < N → q < N → o ≠ q → ∀ T : W, D o o T = 0 → D q q T = 0 →
      D o q (proj K 0 (D o q) (D q o) T) = 0 ∧ (D o q T = 0 → D q o T = 0)

def RankTwo : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (N K : ℕ) (D : ℕ → ℕ → Module.End ℚ W), GlRel N D → Bdd N (2 * K) D →
    ∀ o p q : ℕ, o < N → p < N → q < N → o ≠ p → o ≠ q → p ≠ q → ∀ (j : ℕ) (T : W),
      D o o T = 0 → D p p T = 0 → D q q T = 0 → D p q T = 0 →
      D p q (proj K j (D o p) (D p o) (proj K (j + 1) (D o q) (D q o) T)) = 0

def GridInv : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℚ W] (a b K : ℕ) (D : ℕ → ℕ → Module.End ℚ W), GlRel (a + b) D →
    Bdd (a + b) (2 * K) D → ∀ T : W, (∀ c < a + b, ∀ d < a + b, (c < a ↔ d < a) → D c d T = 0) →
      ∀ c < a + b, ∀ d < a + b, D c d (gridP D K a b a T) = 0

def AdjBdd : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (N K : ℕ) (e : ℕ → ℕ → Module.End ℚ V), GlRel N e → Bdd N K e →
    WtSpan N e → GlRel N (fun a b => adj (e a b)) ∧ Bdd N (2 * K) (fun a b => adj (e a b))

def StepScalar : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (E F H T : Module.End ℚ V) (v : V) (φ : V →ₗ[ℚ] ℚ) (n K j : ℕ),
    E * F - F * E = H → H * F - F * H = -(F + F) → E v = 0 → H v = (n : ℚ) • v → n ≤ K → (∀ x, φ (F x) = 0) →
    (∀ k : ℕ, 0 < k → T ((F ^ k) v) = 0) →
      φ (proj K j (adj E) (adj F) T v) * ((n : ℚ) + j + 1) = φ (T v)

def GridScalar : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (a b K : ℕ) (e : ℕ → ℕ → Module.End ℚ V) (lam : ℕ → ℤ) (v : V)
    (φ : V →ₗ[ℚ] ℚ) (T : Module.End ℚ V), GlRel (a + b) e → Dom (a + b) e lam → IsWt (a + b) e lam v →
    (∀ i j : ℕ, i < j → j < a + b → e i j v = 0 ∧ (∀ x, φ (e j i x) = 0) ∧ lam j ≤ lam i ∧ lam i ≤ lam j + K) →
    (∀ (μ : ℕ → ℤ) (x : V), IsWt (a + b) e μ x → ∑ c ∈ Finset.range a, μ c < ∑ c ∈ Finset.range a, lam c → T x = 0) →
      φ (gridP (fun c d => adj (e c d)) K a b a T v) *
        ((∏ i ∈ Finset.range a, ∏ j ∈ Finset.Ico a (a + b), (lam i - lam j + (j : ℤ) - (i : ℤ)) : ℤ) : ℚ) = φ (T v)

def GridInt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (a b K w Λ : ℕ) (e : ℕ → ℕ → Module.End ℚ V) (L M : Submodule ℤ V),
    DivStable (a + b) e L → DivStable (a + b) e M → K + (a + b) ≤ w + 1 →
    (∀ j k : ℕ, j + k + 1 ≤ w → (j + k + 1).factorial ∣ Λ * (j.factorial * k.factorial)) →
    ∀ (c : ℕ) (T : Module.End ℚ V), (∀ x ∈ L, (c : ℤ) • T x ∈ M) →
      ∀ x ∈ L, ((c * Λ ^ (a * b) : ℕ) : ℤ) • gridP (fun c d => adj (e c d)) K a b a T x ∈ M

def BetaDen : Prop :=
  ∀ l w : ℕ, l.Prime → ∃ m : ℕ, ¬ l ∣ m ∧
    ∀ j k : ℕ, j + k + 1 ≤ w → (j + k + 1).factorial ∣ (m * l ^ Nat.log l w) * (j.factorial * k.factorial)

def eV (N : ℕ) (ν : Fin N → ℕ) (a b : ℕ) : Module.End ℚ (dualWeyl ℚ N N ν) :=
  if h : a < N ∧ b < N then
    LinearMap.restrict (Formalism.CohomologicalDescent.LR.der N N ⟨a, h.1⟩ ⟨b, h.2⟩ : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ))
      (fun f hf => Formalism.CohomologicalDescent.LR.der_mem ν _ _ f hf)
  else 0

def latV (N : ℕ) (ν : Fin N → ℕ) (M : Submodule ℤ (MvPolynomial (Fin N × Fin N) ℤ)) : Submodule ℤ (dualWeyl ℚ N N ν) :=
  (M.map (intQ N N)).comap ((dualWeyl ℚ N N ν).subtype.restrictScalars ℤ)

def wtZ {N : ℕ} (ν : Fin N → ℕ) (c : ℕ) : ℤ := if h : c < N then (ν ⟨c, h⟩ : ℤ) else 0

def resVarT (R : Type) [CommRing R] (p q : ℕ) (v : Fin (p + q) × Fin (p + q)) :
    MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R :=
  Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R)
    (fun a => Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R)
      (fun s => X (a, s) ⊗ₜ[R] 1) (fun _ => 0) v.2)
    (fun b => Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R)
      (fun _ => 0) (fun t => 1 ⊗ₜ[R] X (b, t)) v.2) v.1

def resT (R : Type) [CommRing R] (p q : ℕ) : MvPolynomial (Fin (p + q) × Fin (p + q)) R →ₐ[R]
    MvPolynomial (Fin p × Fin p) R ⊗[R] MvPolynomial (Fin q × Fin q) R :=
  aeval (resVarT R p q)

def NablaGl : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν →
    GlRel N (eV N ν) ∧ WtSpan N (eV N ν) ∧ Dom N (eV N ν) (wtZ ν) ∧
      DivStable N (eV N ν) (latV N ν (dualWeyl ℤ N N ν)) ∧ DivStable N (eV N ν) (latV N ν (weyl ℤ N N le_rfl ν))

def NablaBdd : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ K : ℕ, (∀ i j, ν i ≤ ν j + K) → Bdd N K (eV N ν)

def NablaSchur : Prop :=
  ∀ (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν) (S : Module.End ℚ (dualWeyl ℚ N N ν)),
    (∀ c < N, ∀ d < N, eV N ν c d * S = S * eV N ν c d) →
    fockQ (hw ℚ le_rfl ν) (S ⟨hw ℚ le_rfl ν, hwMem ℚ N N le_rfl ν hν⟩ : dualWeyl ℚ N N ν) =
      fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) → S = 1

def SubstMem : Prop :=
  ∀ (R : Type) [CommRing R] (k N : ℕ) (τ : Fin k → Fin N), StrictMono τ →
    ∀ ψ : Fin N × Fin N → MvPolynomial (Fin k × Fin k) R,
      (∀ a s, ψ (τ a, τ s) = X (a, s)) → (∀ x s, x ∉ Set.range τ → ψ (x, τ s) = 0) →
      (∀ x y, y ∉ Set.range τ → ∃ c : R, ψ (x, y) = C c) →
      ∀ (ν : Fin N → ℕ), ∀ f ∈ dualWeyl R N N ν, aeval ψ f ∈ dualWeyl R k k (fun s => ν (τ s))

def ResLat : Prop :=
  ∀ (p q : ℕ) (ν : Fin (p + q) → ℕ), ∀ f ∈ dualWeyl ℤ (p + q) (p + q) ν,
    resT ℚ p q (intQ (p + q) (p + q) f) ∈ Submodule.span ℤ
      {z | ∃ f₁ ∈ dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)), ∃ f₂ ∈ dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j)),
        z = intQ p p f₁ ⊗ₜ[ℚ] intQ q q f₂}

def ResHw : Prop :=
  ∀ (p q : ℕ) (ν : Fin (p + q) → ℕ), Antitone ν →
    resT ℚ p q (hw ℚ le_rfl ν) =
      hw ℚ le_rfl (fun i => ν (Fin.castAdd q i)) ⊗ₜ[ℚ] hw ℚ le_rfl (fun j => ν (Fin.natAdd p j))

def ResDer : Prop :=
  ∀ (p q : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ),
    (∀ c d : Fin p, resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.castAdd q c) (Fin.castAdd q d) f) =
      LinearMap.rTensor _ (Formalism.CohomologicalDescent.LR.der p p c d : Module.End ℚ (MvPolynomial (Fin p × Fin p) ℚ)) (resT ℚ p q f)) ∧
    (∀ c d : Fin q, resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.natAdd p c) (Fin.natAdd p d) f) =
      LinearMap.lTensor _ (Formalism.CohomologicalDescent.LR.der q q c d : Module.End ℚ (MvPolynomial (Fin q × Fin q) ℚ)) (resT ℚ p q f)) ∧
    ∀ (ν : Fin (p + q) → ℕ) (t : ℚ), IsWeightedHomogeneous (colW (p + q) (p + q)) f ν →
      ∑ c : Fin p, Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.castAdd q c) (Fin.castAdd q c) f = t • f →
      t ≠ ∑ c : Fin p, (ν (Fin.castAdd q c) : ℚ) → resT ℚ p q f = 0

def LeviProj : Prop :=
  ∀ (p q : ℕ) (ν : Fin (p + q) → ℕ) (hν : Antitone ν) (c₁ c₂ : ℕ),
    (∀ x ∈ dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)), (c₁ : ℤ) • x ∈ weyl ℤ p p le_rfl (fun i => ν (Fin.castAdd q i))) →
    (∀ x ∈ dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j)), (c₂ : ℤ) • x ∈ weyl ℤ q q le_rfl (fun j => ν (Fin.natAdd p j))) →
    ∃ T : Module.End ℚ (dualWeyl ℚ (p + q) (p + q) ν),
      (∀ c < p + q, ∀ d < p + q, (c < p ↔ d < p) → eV (p + q) ν c d * T = T * eV (p + q) ν c d) ∧
      (∀ x ∈ latV (p + q) ν (dualWeyl ℤ (p + q) (p + q) ν),
        ((c₁ * c₂ : ℕ) : ℤ) • T x ∈ latV (p + q) ν (weyl ℤ (p + q) (p + q) le_rfl ν)) ∧
      (∀ (μ : ℕ → ℤ) (x : dualWeyl ℚ (p + q) (p + q) ν), IsWt (p + q) (eV (p + q) ν) μ x →
        ∑ c ∈ Finset.range p, μ c < ∑ c ∈ Finset.range p, wtZ ν c → T x = 0) ∧
      fockQ (hw ℚ le_rfl ν) (T ⟨hw ℚ le_rfl ν, hwMem ℚ (p + q) (p + q) le_rfl ν hν⟩ : dualWeyl ℚ (p + q) (p + q) ν) =
        fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν)

end GlobalTheory.LeviCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionIsAlgebraicWeierstrassTorsionStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansion_isAlgebraic_weierstrassTorsion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), QAll (IsAlgebraic ℚ) N (wp N x) ∧ QAll (IsAlgebraic ℚ) N (wpd N x) ∧ (x ≠ 0 → QAll (IsAlgebraic ℚ) N (wB N x)) := by
  first | exact @GlobalTheory.WpFam.qAll_isAlgebraic_torsion | exact GlobalTheory.WpFam.qAll_isAlgebraic_torsion | (intros; apply GlobalTheory.WpFam.qAll_isAlgebraic_torsion <;> assumption)
end

