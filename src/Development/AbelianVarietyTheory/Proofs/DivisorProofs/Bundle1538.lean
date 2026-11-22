import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0769
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1524
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionTwistedCoinvariantRank
section
open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv.Recentre

variable {k : Type} [Field k] [ValuativeRel k]

theorem vecMul_bound {r : ℕ} (E : Matrix (Fin r) (Fin r) k) (δ b : ValueGroupWithZero k)
    (hδ : δ < 1) (hE : ∀ l l', valuation k (E l l') ≤ δ) (s w : Fin r → k)
    (hw : ∀ l, valuation k (w l) ≤ b) (hs : s ᵥ* (1 + E) = w) : ∀ l, valuation k (s l) ≤ b := by
  rcases isEmpty_or_nonempty (Fin r) with hr | hr
  · intro l; exact isEmptyElim l
  obtain ⟨l₀, -, hl₀⟩ := Finset.exists_max_image Finset.univ (fun l => valuation k (s l)) Finset.univ_nonempty
  have key : s l₀ = w l₀ - ∑ l, s l * E l l₀ := by
    have := congrFun hs l₀
    simp only [Matrix.vecMul_add, Matrix.vecMul_one, Pi.add_apply] at this
    rw [← this]; simp [Matrix.vecMul, dotProduct]
  have hsum : valuation k (∑ l, s l * E l l₀) ≤ valuation k (s l₀) * δ := by
    apply Valuation.map_sum_le
    intro l _
    rw [map_mul]
    exact mul_le_mul' (hl₀ l (Finset.mem_univ _)) (hE l l₀)
  have hμ : valuation k (s l₀) ≤ max b (valuation k (s l₀) * δ) := by
    calc valuation k (s l₀) = valuation k (w l₀ - ∑ l, s l * E l l₀) := by rw [← key]
      _ ≤ max (valuation k (w l₀)) (valuation k (∑ l, s l * E l l₀)) := Valuation.map_sub _ _ _
      _ ≤ max b (valuation k (s l₀) * δ) := max_le_max (hw l₀) hsum
  have hμb : valuation k (s l₀) ≤ b := by
    rcases le_max_iff.1 hμ with h | h
    · exact h
    · by_cases h0 : valuation k (s l₀) = 0
      · rw [h0]; exact zero_le'
      · exfalso
        have h2 := mul_le_mul_left h (valuation k (s l₀))⁻¹
        rw [mul_inv_cancel₀ h0, mul_comm (valuation k (s l₀)) δ, mul_assoc, mul_inv_cancel₀ h0, mul_one] at h2
        exact absurd hδ (not_lt.2 h2)
  exact fun l => (hl₀ l (Finset.mem_univ _)).trans hμb

end GlobalTheory.RankCoinv.Recentre

theorem GlobalTheory.RankCoinv.boxFn_mem_lowRank_sup_twistSpan_of_small_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, valuation k (C i₀ j) ≤ valuation k ((ϖ ^ (c + 1) : kˣ) : k)) → GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν1 hνϖ i₀ r c m C H Q hHi₀ hH hcm hHC hQ hHCQ hCi₀
  classical
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hv0 : valuation k (ϖ : k) ≠ 0 := by simp
  have vpow : ∀ n : ℕ, valuation k (((ϖ ^ n : kˣ)) : k) = valuation k (ϖ : k) ^ n := by intro n; simp
  have vinv : valuation k ((((ϖ ^ c)⁻¹ : kˣ)) : k) = (valuation k (ϖ : k) ^ c)⁻¹ := by simp
  by_cases hex : ∃ X₂ ∈ GlobalTheory.RankCoinv.box ϖ C (fun _ => m), X₂.rank ≤ r
  swap
  · apply Submodule.mem_sup_left
    refine ⟨GlobalTheory.RankCoinv.boxFn_mem_SB _ _ _, fun Y hY => ?_⟩
    unfold GlobalTheory.RankCoinv.boxFn
    apply Set.indicator_of_notMem
    intro hYb; exact hex ⟨Y, hYb, Nat.lt_succ_iff.1 hY⟩
  obtain ⟨X₂, hX₂, hrk⟩ := hex
  set u := valuation k (ϖ : k) with hu
  have hQ' : ∀ j l, valuation k (Q j l) ≤ 1 := fun j l => (Valuation.mem_integer_iff _ _).1 (hQ j l)
  have hD : ∀ i j, valuation k ((X₂ - C) i j) ≤ u ^ m := fun i j => by
    rw [Matrix.sub_apply, ← vpow]; exact hX₂ i j
  have hHb : ∀ l i, valuation k (H l i) ≤ (u ^ c)⁻¹ := fun l i => (hH l i).trans_eq vinv
  have hHD : ∀ l j, valuation k ((H * (X₂ - C)) l j) ≤ (u ^ c)⁻¹ * u ^ m := fun l j => by
    rw [Matrix.mul_apply]; apply Valuation.map_sum_le; intro i _; rw [map_mul]
    exact mul_le_mul' (hHb l i) (hD i j)
  have hE : ∀ l l', valuation k ((H * (X₂ - C) * Q) l l') ≤ (u ^ c)⁻¹ * u ^ m := fun l l' => by
    rw [Matrix.mul_apply]; apply Valuation.map_sum_le; intro j _; rw [map_mul]
    calc _ ≤ (u ^ c)⁻¹ * u ^ m * 1 := mul_le_mul' (hHD l j) (hQ' j l')
      _ = _ := mul_one _
  have hm1 : u ^ m ≤ u ^ (c + 1) := pow_le_pow_right_of_le_one' hlt.le hcm
  have hδ : (u ^ c)⁻¹ * u ^ m < 1 := by
    calc (u ^ c)⁻¹ * u ^ m ≤ (u ^ c)⁻¹ * u ^ (c + 1) := mul_le_mul' le_rfl hm1
      _ = u := by rw [pow_succ, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hv0), one_mul]
      _ < 1 := hlt
  have hM : H * X₂ * Q = 1 + H * (X₂ - C) * Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hHCQ]; abel
  have hunit : IsUnit (H * X₂ * Q) := by
    rw [← Matrix.vecMul_injective_iff_isUnit]
    intro a a' haa
    have h0 : (a - a') ᵥ* (1 + H * (X₂ - C) * Q) = 0 := by
      rw [← hM, Matrix.sub_vecMul]; exact sub_eq_zero.2 haa
    funext l
    have h1 := GlobalTheory.RankCoinv.Recentre.vecMul_bound _ _ 0 hδ hE (a - a') 0 (fun _ => by simp) h0 l
    have h2 : (a - a') l = 0 := (Valuation.zero_iff _).1 (le_antisymm h1 zero_le')
    exact sub_eq_zero.1 h2
  obtain ⟨s, hs⟩ := GlobalTheory.T.rows_in_span_of_rank_normal_form k A D r X₂ H Q hrk hunit i₀
  have hsw : s ᵥ* (1 + H * (X₂ - C) * Q) = X₂ i₀ ᵥ* Q := by
    rw [← hM, ← Matrix.vecMul_vecMul, ← hs]
  have hX₂i₀ : ∀ j, valuation k (X₂ i₀ j) ≤ u ^ (c + 1) := fun j => by
    have h1 : valuation k (X₂ i₀ j - C i₀ j) ≤ u ^ (c + 1) := ((hX₂ i₀ j).trans_eq (vpow m)).trans hm1
    have h2 : valuation k (C i₀ j) ≤ u ^ (c + 1) := (hCi₀ j).trans_eq (vpow _)
    calc valuation k (X₂ i₀ j) = valuation k ((X₂ i₀ j - C i₀ j) + C i₀ j) := by rw [sub_add_cancel]
      _ ≤ _ := Valuation.map_add_le _ h1 h2
  have hw : ∀ l, valuation k ((X₂ i₀ ᵥ* Q) l) ≤ u ^ (c + 1) := fun l => by
    simp only [Matrix.vecMul, dotProduct]
    apply Valuation.map_sum_le; intro j _; rw [map_mul]
    calc _ ≤ u ^ (c + 1) * 1 := mul_le_mul' (hX₂i₀ j) (hQ' j l)
      _ = _ := mul_one _
  have hsb := GlobalTheory.RankCoinv.Recentre.vecMul_bound _ _ _ hδ hE s _ hw hsw
  have hsmall : ∀ j, valuation k ((s ᵥ* (H * (X₂ - C))) j) ≤ u ^ m := fun j => by
    simp only [Matrix.vecMul, dotProduct]
    apply Valuation.map_sum_le; intro l _; rw [map_mul]
    calc _ ≤ u ^ (c + 1) * ((u ^ c)⁻¹ * u ^ m) := mul_le_mul' (hsb l) (hHD l j)
      _ = u * u ^ m := by
        rw [pow_succ, mul_comm (u ^ c) u, mul_assoc, ← mul_assoc (u ^ c), mul_inv_cancel₀ (pow_ne_zero _ hv0), one_mul]
      _ ≤ 1 * u ^ m := mul_le_mul_left hlt.le _
      _ = u ^ m := one_mul _
  set C' := Matrix.updateRow C i₀ 0 with hC'
  have hHC' : H * C' = H * C := by
    ext l j
    simp only [Matrix.mul_apply, C', Matrix.updateRow_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · subst h; simp [hHi₀]
    · rfl
  have hcore := GlobalTheory.T.box_function_twisted_coinvariant k A D ϖ hϖ ν β hν1 hνϖ i₀ r c m C' H Q hHi₀ hH hcm
    (by rw [hHC']; exact hHC) hQ (by rw [hHC']; exact hHCQ) (fun j => by simp [C'])
  have hstep := GlobalTheory.T.box_function_action_bounded_matrix k A D ϖ ν β i₀ r c m C' H s hHi₀ hH
    (fun l => (hsb l).trans (by rw [vpow]; exact pow_le_pow_right_of_le_one' hlt.le (Nat.le_succ c)))
  have e1 : s ᵥ* (H * C) = X₂ i₀ - s ᵥ* (H * (X₂ - C)) := by
    rw [Matrix.mul_sub, Matrix.vecMul_sub, ← hs, sub_sub_cancel]
  have hC'' : Matrix.updateRow C' i₀ (C' i₀ + s ᵥ* (H * C')) =
      Matrix.updateRow C i₀ (X₂ i₀ - s ᵥ* (H * (X₂ - C))) := by
    rw [hHC', e1]
    ext i j
    by_cases hi : i = i₀
    · subst hi
      rw [Matrix.updateRow_self, Matrix.updateRow_self, hC', Matrix.updateRow_self, zero_add]
    · rw [Matrix.updateRow_ne hi, Matrix.updateRow_ne hi, hC', Matrix.updateRow_ne hi]
  have hmem : Matrix.updateRow C' i₀ (C' i₀ + s ᵥ* (H * C')) ∈ GlobalTheory.RankCoinv.box ϖ C (fun _ => m) := by
    rw [hC'']
    intro i j
    by_cases hi : i = i₀
    · subst hi
      rw [Matrix.updateRow_self]
      calc valuation k ((X₂ i - s ᵥ* (H * (X₂ - C))) j - C i j)
          = valuation k ((X₂ i j - C i j) - (s ᵥ* (H * (X₂ - C))) j) := by
            congr 1; rw [Pi.sub_apply]; ring
        _ ≤ max (valuation k (X₂ i j - C i j)) (valuation k ((s ᵥ* (H * (X₂ - C))) j)) :=
            Valuation.map_sub _ _ _
        _ ≤ u ^ m := max_le ((hX₂ i j).trans_eq (vpow m)) (hsmall j)
        _ = _ := (vpow m).symm
    · rw [Matrix.updateRow_ne hi]; simp
  rw [GlobalTheory.RankCoinv.boxFn_eq_of_mem hmem] at hstep
  rw [← sub_add_cancel (GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m)) (GlobalTheory.RankCoinv.boxFn ϖ C' (fun _ => m))]
  exact Submodule.add_mem _ (Submodule.mem_sup_right hstep) hcore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyNrmLConj
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.UnitProd

private theorem equivalence_twisted_conj {G : Type} [Group G] (θ : G →* G) :
    Equivalence (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) where
  refl x := ⟨1, by simp⟩
  symm := by
    rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by rw [map_inv]; group⟩
  trans := by
    rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by rw [map_mul]; group⟩

theorem rep_mk {G : Type} [Group G] (θ : G →* G) (x : G) :
    ∃ g, TwCl.rep (θ := θ) (Quot.mk _ x) = g⁻¹ * x * θ g := by
  unfold TwCl.rep
  have h := Quot.eqvGen_exact (Quot.out_eq (Quot.mk (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) x))
  rw [Equivalence.eqvGen_iff (equivalence_twisted_conj θ)] at h
  exact (equivalence_twisted_conj θ).symm h

theorem mk_rep {G : Type} [Group G] {θ : G →* G} (c : TwCl θ) : (Quot.mk _ c.rep : TwCl θ) = c := by
  unfold TwCl.rep
  exact Quot.out_eq c

noncomputable def clsEquiv {G G' : Type} [Group G] [Group G'] (θ : G →* G) (θ' : G' →* G') :
    TwCl θ × TwCl θ' ≃ TwCl (θ.prodMap θ') where
  toFun p := Quot.mk _ (p.1.rep, p.2.rep)
  invFun c := (Quot.mk _ c.rep.1, Quot.mk _ c.rep.2)
  left_inv p := by
    obtain ⟨g, hg⟩ := rep_mk (θ.prodMap θ') (p.1.rep, p.2.rep)
    refine Prod.ext ?_ ?_
    · refine Eq.trans (Quot.sound ⟨g.1, ?_⟩).symm (mk_rep p.1)
      exact congrArg Prod.fst hg
    · refine Eq.trans (Quot.sound ⟨g.2, ?_⟩).symm (mk_rep p.2)
      exact congrArg Prod.snd hg
  right_inv c := by
    obtain ⟨g, hg⟩ := rep_mk θ c.rep.1
    obtain ⟨g', hg'⟩ := rep_mk θ' c.rep.2
    refine Eq.trans (Quot.sound ⟨(g, g'), ?_⟩).symm (mk_rep c)
    refine Prod.ext ?_ ?_
    · simp [hg]
    · simp [hg']

theorem ind_conj {G : Type} [Group G] (θ : G →* G) (K : Subgroup G) (hK : ∀ k ∈ K, θ k ∈ K) (δ x k : G) (hk : k ∈ K) :
    (x * k)⁻¹ * δ * θ (x * k) ∈ K ↔ x⁻¹ * δ * θ x ∈ K := by

  have e : (x * k)⁻¹ * δ * θ (x * k) = k⁻¹ * (x⁻¹ * δ * θ x) * θ k := by
    rw [map_mul]; group
  rw [e, K.mul_mem_cancel_right (hK k hk), K.mul_mem_cancel_left (K.inv_mem hk)]

theorem index_ne {G : Type} [Group G] (θ : G →* G) (K : Subgroup G) (hK : ∀ k ∈ K, θ k ∈ K) (δ x : G) :
    (rStab fun k : K => (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0 := by

  have htop : rStab (fun k : K => (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * δ * θ (x * k))) = ⊤ := by
    ext k
    simp only [Subgroup.mem_top, iff_true]
    rw [GlobalTheory.TwOrbConj.mem_rStab]
    intro y
    simp only [Subgroup.coe_mul, ← mul_assoc]
    rw [Set.indicator_apply, Set.indicator_apply]
    simp only [SetLike.mem_coe, ind_conj θ K hK δ (x * y) k k.2, Pi.one_apply]
  rw [htop, Subgroup.index_top]
  exact one_ne_zero

theorem clSum_prod {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G'] (θ : G →* G) (θ' : G' →* G') (K : Subgroup G)
    (K' : Subgroup G') (S : Set G) (S' : Set G') (hK : ∀ k ∈ K, θ k ∈ K) (hK' : ∀ k ∈ K', θ' k ∈ K')
    (hS : ∀ g y, g⁻¹ * y * θ g ∈ S ↔ y ∈ S) (hS' : ∀ g y, g⁻¹ * y * θ' g ∈ S' ↔ y ∈ S')
    (hf : {c : TwCl θ | c.rep ∈ S}.Finite) (hf' : {c : TwCl θ' | c.rep ∈ S'}.Finite)
    (hd : ∀ y ∈ S, {q : DoubleCoset.Quotient (twCent θ y : Set G) (K : Set G) |
      (Quotient.out q)⁻¹ * y * θ (Quotient.out q) ∈ K}.Finite)
    (hd' : ∀ y ∈ S', {q : DoubleCoset.Quotient (twCent θ' y : Set G') (K' : Set G') |
      (Quotient.out q)⁻¹ * y * θ' (Quotient.out q) ∈ K'}.Finite) :
    clSum (θ.prodMap θ') (K.prod K') {y | y.1 ∈ S ∧ y.2 ∈ S'} 1 (((K.prod K' : Subgroup _) : Set _).indicator 1) =
      clSum θ K S 1 ((K : Set G).indicator 1) * clSum θ' K' S' 1 ((K' : Set G').indicator 1) := by
  unfold clSum
  simp only [Pi.one_apply, one_mul]

  have hKK : ∀ k ∈ K.prod K', (θ.prodMap θ') k ∈ K.prod K' := fun k hk =>
    Subgroup.mem_prod.mpr ⟨hK _ (Subgroup.mem_prod.mp hk).1, hK' _ (Subgroup.mem_prod.mp hk).2⟩
  have hind : (((K.prod K' : Subgroup _) : Set (G × G')).indicator (1 : G × G' → ℂ)) =
      fun y => (K : Set G).indicator 1 y.1 * (K' : Set G').indicator 1 y.2 := by
    funext y
    by_cases h1 : y.1 ∈ K <;> by_cases h2 : y.2 ∈ K' <;>
      simp [Subgroup.mem_prod, h1, h2]
  have hfin : ∀ {H : Type} [Group H] (φ : H →* H) (L : Subgroup H) (hL : ∀ k ∈ L, φ k ∈ L) (T : Set H)
      (hT : ∀ y ∈ T, {q : DoubleCoset.Quotient (twCent φ y : Set H) (L : Set H) |
        (Quotient.out q)⁻¹ * y * φ (Quotient.out q) ∈ L}.Finite) (y : H), y ∈ T →
      {q : DoubleCoset.Quotient (twCent φ y : Set H) (L : Set H) |
        ∃ k ∈ L, (L : Set H).indicator (1 : H → ℂ) ((Quotient.out q * k)⁻¹ * y * φ (Quotient.out q * k)) ≠ 0}.Finite := by
    intro H _ φ L hL T hT y hy
    refine (hT y hy).subset ?_
    rintro q ⟨k, hk, hne⟩
    by_contra hq
    apply hne
    rw [Set.indicator_apply, if_neg]
    rw [SetLike.mem_coe, ind_conj φ L hL _ _ k hk]
    exact hq
  have hprod : ∀ p : TwCl θ × TwCl θ',
      (if (clsEquiv θ θ' p).rep ∈ {y : G × G' | y.1 ∈ S ∧ y.2 ∈ S'} then
        twOrb (θ.prodMap θ') (K.prod K') (clsEquiv θ θ' p).rep (((K.prod K' : Subgroup _) : Set _).indicator 1)
        else 0) =
      (if p.1.rep ∈ S then twOrb θ K p.1.rep ((K : Set G).indicator 1) else 0) *
      (if p.2.rep ∈ S' then twOrb θ' K' p.2.rep ((K' : Set G').indicator 1) else 0) := by
    intro p
    obtain ⟨g, hg⟩ := rep_mk (θ.prodMap θ') (p.1.rep, p.2.rep)
    have e : (clsEquiv θ θ' p).rep = g⁻¹ * (p.1.rep, p.2.rep) * (θ.prodMap θ') g := hg
    have hmem : g⁻¹ * (p.1.rep, p.2.rep) * (θ.prodMap θ') g ∈ {y : G × G' | y.1 ∈ S ∧ y.2 ∈ S'} ↔
        p.1.rep ∈ S ∧ p.2.rep ∈ S' := by
      show g.1⁻¹ * p.1.rep * θ g.1 ∈ S ∧ g.2⁻¹ * p.2.rep * θ' g.2 ∈ S' ↔ _
      rw [hS, hS']
    rw [e, GlobalTheory.TwOrbConj.twOrb_twConj (G × G') (θ.prodMap θ') (K.prod K') (p.1.rep, p.2.rep) g _
      (fun x => index_ne (θ.prodMap θ') (K.prod K') hKK _ x)]
    by_cases h1 : p.1.rep ∈ S <;> by_cases h2 : p.2.rep ∈ S'
    · simp only [hmem, h1, h2, and_self, if_true]
      rw [hind]
      exact GlobalTheory.T.twistedOrbitalIntegral_productGroup G G' θ θ' K K' _ _ _ _ (fun x => index_ne θ K hK _ x) (fun x => index_ne θ' K' hK' _ x)
        (hfin θ K hK S hd _ h1) (hfin θ' K' hK' S' hd' _ h2)
    · rw [if_neg fun h => h2 (hmem.mp h).2, if_neg h2, mul_zero]
    · rw [if_neg fun h => h1 (hmem.mp h).1, if_neg h1, zero_mul]
    · rw [if_neg fun h => h1 (hmem.mp h).1, if_neg h1, zero_mul]
  have hs1 : (Function.support fun c : TwCl θ =>
      if c.rep ∈ S then twOrb θ K c.rep ((K : Set G).indicator 1) else 0).Finite := by
    refine hf.subset fun c hc => ?_
    by_contra h
    apply hc
    change ¬ c.rep ∈ S at h
    simp [h]
  have hs2 : (Function.support fun c : TwCl θ' =>
      if c.rep ∈ S' then twOrb θ' K' c.rep ((K' : Set G').indicator 1) else 0).Finite := by
    refine hf'.subset fun c hc => ?_
    by_contra h
    apply hc
    change ¬ c.rep ∈ S' at h
    simp [h]
  rw [← finsum_comp_equiv (clsEquiv θ θ')]
  refine (finsum_congr hprod).trans ?_
  rw [finsum_curry _ ((hs1.prod hs2).subset fun p hp => ⟨left_ne_zero_of_mul hp, right_ne_zero_of_mul hp⟩),
    finsum_mul]
  refine finsum_congr fun c => ?_
  rw [mul_finsum]

theorem charpoly_nrmL_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (hE : Unr E) (n : ℕ) (w : Pl E)
    (g y : GLw n w) : (nrmL n w (g⁻¹ * y * thL n w g)).val.charpoly = (nrmL n w y).val.charpoly := by
  rw [GlobalTheory.BCT.ThBasic.nrmL_twist hE, Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' _ _

theorem stTw2_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (w : Pl E), ¬ IsSplitAt w → ∀ Q₁ Q₂ : (w.adicCompletion E)[X], Q₁.Separable → Q₂.Separable → stTw2 a b w Q₁ Q₂ ((((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) : Subgroup _) : Set _).indicator 1) = stTw a w Q₁ ((GlobalTheory.LFun.KGL w a : Set (GLw a w)).indicator 1) * stTw b w Q₂ ((GlobalTheory.LFun.KGL w b : Set (GLw b w)).indicator 1) := by
  intro E _ _ _ hE a b w hw Q₁ Q₂ h₁ h₂
  unfold stTw2 stTw
  have hL : ∀ m : ℕ, IsLevel (thL m w) (GlobalTheory.LFun.KGL w m) (GlobalTheory.LFun.KGL w m) := by
    intro m
    unfold IsLevel
    exact ⟨(GlobalTheory.BCT.ThBasic.twist_basic E hE m w).2.2.2.2.1, le_rfl,
      fun k hk => GlobalTheory.BCT.ThBasic.thL_mem_KGL hE m w k hk⟩
  have hS : ∀ (m : ℕ) (Q : (w.adicCompletion E)[X]) (g y : GLw m w),
      g⁻¹ * y * thL m w g ∈ {y : GLw m w | (nrmL m w y).val.charpoly = Q} ↔
        y ∈ {y : GLw m w | (nrmL m w y).val.charpoly = Q} := by
    intro m Q g y
    show _ = Q ↔ _ = Q
    rw [charpoly_nrmL_conj hE]
  have hd : ∀ (m : ℕ) (Q : (w.adicCompletion E)[X]), Q.Separable →
      ∀ y ∈ {y : GLw m w | (nrmL m w y).val.charpoly = Q},
        {q : DoubleCoset.Quotient (twCent (thL m w) y : Set (GLw m w)) (GlobalTheory.LFun.KGL w m : Set (GLw m w)) |
          (Quotient.out q)⁻¹ * y * thL m w (Quotient.out q) ∈ GlobalTheory.LFun.KGL w m}.Finite := by
    intro m Q hQ y hy
    have hy' : (nrmL m w y).val.charpoly = Q := hy
    exact (GlobalTheory.T.regularTwistedOrbit_local_finiteness E hE m w y (hy' ▸ hQ) _ (hL m)).2 _ (GlobalTheory.BCT.ThBasic.twist_basic E hE m w).2.2.2.2.2.1
  exact clSum_prod (thL a w) (thL b w) _ _ _ _ (GlobalTheory.BCT.ThBasic.thL_mem_KGL hE a w)
    (GlobalTheory.BCT.ThBasic.thL_mem_KGL hE b w) (hS a Q₁) (hS b Q₂) (GlobalTheory.BCT.ClsFin.classes_finite E hE a w Q₁ h₁).1
    (GlobalTheory.BCT.ClsFin.classes_finite E hE b w Q₂ h₂).1 (hd a Q₁ h₁) (hd b Q₂ h₂)

end GlobalTheory.BCT.UnitProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBallExtendByZeroInvariant
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ChartBallExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def InOrbit (X : Data E r) (x : Frame X.Ψ r) (R : ℝ) (y : Frame X.Ψ r) : Prop :=
  ∃ z : V (nd X), ‖z‖ ≤ R ∧ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul (cpt X x z) b)

open Classical in

noncomputable def ext (X : Data E r) (x : Frame X.Ψ r) (R : ℝ) (η : V (nd X) → ℝ) (y : Frame X.Ψ r) : ℝ :=
  if h : InOrbit X x R y then η h.choose else 0

theorem uniq (X : Data E r) {x : Frame X.Ψ r} {R : ℝ} (ho : IsOrth X x)
    (hinj : ∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ R → ‖z'‖ ≤ R → ∀ b ∈ Bor X.Ψ r,
      lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1)
    {γ γ' : GL (Fin r) E} (hγ : γ ∈ X.Γ) (hγ' : γ' ∈ X.Γ) {b b' : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) {z z' : V (nd X)} (hz : ‖z‖ ≤ R) (hz' : ‖z'‖ ≤ R)
    (h : lact γ (rmul (cpt X x z) b) = lact γ' (rmul (cpt X x z') b')) : z = z' := by
  have h1 : lact (γ'⁻¹ * γ) (rmul (cpt X x z) b) = rmul (cpt X x z') b' := by
    rw [← IW.lact_lact, h, IW.lact_lact, inv_mul_cancel, IW.lact_one]
  have h2 : lact (γ'⁻¹ * γ) (cpt X x z) = rmul (cpt X x z') (IW.bmul X b' (IW.binv X b)) := by
    rw [← IW.rmul_rmul, ← h1, IW.lact_rmul, IW.rmul_binv X _ hb]
  have h3 := hinj _ (X.Γ.mul_mem (X.Γ.inv_mem hγ') hγ) z z' hz hz' _
    (IW.bmul_mem X hb' (IW.binv_mem X hb)) h2
  rw [h3, IW.lact_one] at h1
  exact (KU.cpt_inj X ho hb hb' h1).1

theorem ext_val (X : Data E r) {x : Frame X.Ψ r} {R : ℝ} (ho : IsOrth X x)
    (hinj : ∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ R → ‖z'‖ ≤ R → ∀ b ∈ Bor X.Ψ r,
      lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1)
    (η : V (nd X) → ℝ) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    {z : V (nd X)} (hz : ‖z‖ ≤ R) : ext X x R η (lact γ (rmul (cpt X x z) b)) = η z := by
  have hP : InOrbit X x R (lact γ (rmul (cpt X x z) b)) := ⟨z, hz, γ, hγ, b, hb, rfl⟩
  unfold ext
  rw [dif_pos hP]
  obtain ⟨hz', γ', hγ', b', hb', he⟩ := hP.choose_spec
  rw [uniq X ho hinj hγ' hγ hb' hb hz' hz he.symm]

theorem ext_zero (X : Data E r) {x : Frame X.Ψ r} {R : ℝ} (η : V (nd X) → ℝ) {y : Frame X.Ψ r}
    (hy : ¬ InOrbit X x R y) : ext X x R η y = 0 := by
  unfold ext
  rw [dif_neg hy]

end GlobalTheory.ChartBallExt

open GlobalTheory.ChartBallExt in

theorem GlobalTheory.chartBall_extend_by_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (R : ℝ), IsOrth X x → (∀ z : V (nd X), ‖z‖ ≤ R → z ∈ OmF X x) → (∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ R → ‖z'‖ ≤ R → ∀ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1) → ∀ η : V (nd X) → ℝ, ∃ ψ : Frame X.Ψ r → ℝ, (∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ z : V (nd X), ‖z‖ ≤ R → ψ (lact γ (rmul (cpt X x z) b)) = η z) ∧ (∀ y, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ R ∧ y = lact γ (rmul (cpt X x z) b)) → ψ y = 0) ∧ (∀ γ ∈ X.Γ, ∀ y, ψ (lact γ y) = ψ y) ∧ (∀ y, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y) := by
  intro E _ _ _ r X x R ho _ hinj η
  refine ⟨ext X x R η, ?_, ?_, ?_, ?_⟩
  · intro γ hγ b hb z hz
    exact ext_val X ho hinj η hγ hb hz
  · intro y hy
    refine ext_zero X η ?_
    rintro ⟨z, hz, γ, hγ, b, hb, e⟩
    exact hy ⟨γ, hγ, b, hb, z, hz, e⟩
  · intro γ hγ y
    by_cases hy : InOrbit X x R y
    · obtain ⟨z, hz, γ0, hγ0, b, hb, rfl⟩ := hy
      rw [IW.lact_lact, ext_val X ho hinj η (X.Γ.mul_mem hγ hγ0) hb hz, ext_val X ho hinj η hγ0 hb hz]
    · have hy' : ¬ InOrbit X x R (lact γ y) := by
        rintro ⟨z, hz, γ0, hγ0, b, hb, e⟩
        refine hy ⟨z, hz, γ⁻¹ * γ0, X.Γ.mul_mem (X.Γ.inv_mem hγ) hγ0, b, hb, ?_⟩
        rw [← IW.lact_lact, ← e, IW.lact_lact, inv_mul_cancel, IW.lact_one]
      rw [ext_zero X η hy, ext_zero X η hy']
  · intro y b hb
    by_cases hy : InOrbit X x R y
    · obtain ⟨z, hz, γ0, hγ0, b0, hb0, rfl⟩ := hy
      rw [← IW.lact_rmul, IW.rmul_rmul, ext_val X ho hinj η hγ0 (IW.bmul_mem X hb0 hb) hz,
        ext_val X ho hinj η hγ0 hb0 hz]
    · have hy' : ¬ InOrbit X x R (rmul y b) := by
        rintro ⟨z, hz, γ0, hγ0, b0, hb0, e⟩
        refine hy ⟨z, hz, γ0, hγ0, IW.bmul X b0 (IW.binv X b), IW.bmul_mem X hb0 (IW.binv_mem X hb), ?_⟩
        rw [← IW.rmul_rmul, IW.lact_rmul, ← e, IW.rmul_binv X y hb]
      rw [ext_zero X η hy, ext_zero X η hy']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBallWeightPotentialDensityBounds
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.WeightSizes

theorem chart_ball_sizes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) (z : V (nd X)), IsOrth X x → ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → z ∈ OmF X x ∧ |phla X la (cpt X x z)| ≤ ∑ τ, ∑ a, |(la τ a : ℝ)| ∧ |rhF X x z| ≤ (X.Ψ.card : ℝ) ∧ |Real.log (densF X x z)| ≤ (X.Ψ.card : ℝ) * r ∧ 0 < densF X x z := by
  intro E _ _ _ r X la x z hx hz
  have h : (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100 := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · norm_num
    · have hr' : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
      calc (r : ℝ) ^ 2 * ‖z‖ ≤ (r : ℝ) ^ 2 * (1 / (100 * (r : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hz hr'.le
        _ = 1 / 100 := by field_simp
  obtain ⟨hdom, hd⟩ := GlobalTheory.dmin_rmul_near_one X x hx (nmat X z) (norm_nonneg z) (by linarith)
    (fun τ a b => GlobalTheory.ChartNearOne.nmat_entry_le X z τ a b)
  change cpt X x z ∈ X.dom at hdom
  have hL : ∀ τ i, |IW.Lm X (cpt X x z) τ i| ≤ 9 / 100 := fun τ i => by
    have h9 := (hd τ i).2
    change |Real.log ‖dmin X.Gm (cpt X x z) τ i‖| ≤ _ at h9
    unfold IW.Lm
    linarith
  have hz' : z ∈ OmF X x := hdom
  refine ⟨hz', ?_, ?_, ?_, ?_⟩
  · rw [IW.phla_eq X hdom la]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    have h1 : |IW.Lm X (cpt X x z) τ i.succ - IW.Lm X (cpt X x z) τ i.castSucc| ≤ 1 := by
      have ha := abs_le.1 (hL τ i.succ)
      have hb := abs_le.1 (hL τ i.castSucc)
      rw [abs_le]
      constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
    calc |(la τ i : ℝ)| * _ ≤ |(la τ i : ℝ)| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = _ := mul_one _
  · unfold rhF
    rw [abs_neg]
    have hs : ∑ τ : X.Ψ, |Real.log ‖dmin X.Gm (cpt X x z) τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖| ≤
        ∑ _τ : X.Ψ, (1 : ℝ) := Finset.sum_le_sum fun τ _ => by
      have h9 := hL τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
      unfold IW.Lm at h9
      linarith
    refine (Finset.abs_sum_le_sum_abs _ _).trans (hs.trans ?_)
    simp
  · rw [IW.log_densF_eq X x hz']
    have hs : ∑ τ : X.Ψ, ∑ i : Fin r, |(-2) * IW.Lm X (cpt X x z) τ i.castSucc| ≤
        ∑ _τ : X.Ψ, ∑ _i : Fin r, (1 : ℝ) := Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => by
      have h9 := hL τ i.castSucc
      rw [abs_mul]
      norm_num
      linarith
    refine (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun τ _ => Finset.abs_sum_le_sum_abs _ _).trans (hs.trans ?_))
    simp
  · unfold densF
    exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
      zpow_pos (norm_pos_iff.2 (IW.dmin_ne_zero X hdom τ _)) _

end GlobalTheory.WeightSizes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortGeneratorsOfShortSpanningFamilyStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_short_generators_of_short_spanning_family : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (s : Set V) (A : ℝ), L.FG → (∀ σ x, 0 ≤ N σ x) → (∀ σ (a : K) x, N σ (a • x) = ‖σ a‖ * N σ x) → (∀ σ x y, N σ (x + y) ≤ N σ x + N σ y) → s ⊆ L → Submodule.span K s = ⊤ → (∀ y ∈ s, ∀ σ, N σ y ≤ A) → ∃ (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), GlobalTheory.CompHt.IsShortGen N L w abelian₂ ∧ abelian₂ ≤ max 1 ((Module.finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) * |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) * A) ∧ n ≤ 2 * Module.finrank ℚ K * Formalism.HN.rkK L := by
  first | exact @GlobalTheory.exists_isShortGen_of_short_span | exact GlobalTheory.exists_isShortGen_of_short_span | (intros; apply GlobalTheory.exists_isShortGen_of_short_span <;> assumption)
end

