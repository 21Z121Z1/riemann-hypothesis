import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import GroundTheory.AutomorphicForms.Bundle0020
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0329
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RadicalSubspaceFacts
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.RadicalForm

variable {K : Type} [Field K] {n : ℕ}

noncomputable def cols (S : Submodule K (Fin n → K)) : Fin (Module.finrank K S) → (Fin n → K) :=
  fun j => (Module.finBasis K S j : Fin n → K)

theorem cols_li (S : Submodule K (Fin n → K)) : LinearIndependent K (cols S) :=
  (Module.finBasis K S).linearIndependent.map' S.subtype S.ker_subtype

theorem cols_span (S : Submodule K (Fin n → K)) : Submodule.span K (Set.range (cols S)) = S := by
  have h : Set.range (cols S) = S.subtype '' Set.range (Module.finBasis K S) := by
    rw [← Set.range_comp]; rfl
  rw [h, Submodule.span_image, (Module.finBasis K S).span_eq, Submodule.map_top,
    Submodule.range_subtype]

def form (σ : K →+* K) (D : Matrix (Fin n) (Fin n) K) (u v : Fin n → K) : K :=
  (fun i => σ (u i)) ⬝ᵥ (D *ᵥ v)

theorem form_add_left (σ : K →+* K) (D : Matrix (Fin n) (Fin n) K) (u u' v : Fin n → K) :
    form σ D (u + u') v = form σ D u v + form σ D u' v := by
  simp [form, dotProduct, add_mul, Finset.sum_add_distrib]

theorem form_smul_left (σ : K →+* K) (D : Matrix (Fin n) (Fin n) K) (c : K) (u v : Fin n → K) :
    form σ D (c • u) v = σ c * form σ D u v := by
  simp [form, dotProduct, Finset.mul_sum, mul_assoc]

theorem form_zero_left (σ : K →+* K) (D : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    form σ D 0 v = 0 := by
  simp [form, dotProduct]

theorem mem_perpD (σ : K →+* K) (d : GL (Fin n) K) (W : Submodule K (Fin n → K)) (v : Fin n → K) :
    v ∈ perpD σ d W ↔ ∀ x ∈ W, form σ (d⁻¹).val x v = 0 := by
  have h1 : d.val * (d⁻¹).val = 1 := Units.mul_inv d
  have h2 : (d⁻¹).val * d.val = 1 := Units.inv_mul d
  constructor
  · rintro ⟨y, hy, rfl⟩ x hx
    have hy' : ∀ x ∈ W, ∑ i, σ (x i) * y i = 0 := hy
    have h3 : (d⁻¹).val *ᵥ (Matrix.toLin' d.val y) = y := by
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    simp only [form, h3]
    exact hy' x hx
  · intro h
    refine ⟨(d⁻¹).val *ᵥ v, fun x hx => h x hx, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem form_swap (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (D γ : Matrix (Fin n) (Fin n) K)
    (hγ : D * γ = (D.map σ)ᵀ) (u v : Fin n → K) :
    form σ D u (γ *ᵥ v) = σ (form σ D v u) := by
  simp only [form, Matrix.mulVec_mulVec, hγ]
  simp only [dotProduct, mulVec, map_sum, map_mul, hσ, transpose_apply, map_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem entry {κ κ' : Type} [Fintype κ] [Fintype κ'] (σ : K →+* K)
    (D : Matrix (Fin n) (Fin n) K) (M : Matrix (Fin n) κ K) (N : Matrix (Fin n) κ' K) (i j) :
    ((M.map σ)ᵀ * D * N) i j = form σ D (fun k => M k i) (fun k => N k j) := by
  rw [Matrix.mul_assoc]; rfl

theorem entry_mulVec {κ κ' : Type} [Fintype κ] [Fintype κ'] (σ : K →+* K)
    (D : Matrix (Fin n) (Fin n) K) (M : Matrix (Fin n) κ K) (N : Matrix (Fin n) κ' K)
    (c : κ' → K) (i) :
    (((M.map σ)ᵀ * D * N) *ᵥ c) i = form σ D (fun k => M k i) (N *ᵥ c) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]; rfl

theorem exists_adapted (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x) (d : GL (Fin n) K)
    (γ : Matrix (Fin n) (Fin n) K) (hγ : (d⁻¹).val * γ = ((d⁻¹).val.map σ)ᵀ)
    (W : Submodule K (Fin n → K)) (hW : W.map (Matrix.toLin' γ) = W) :
    ∃ (a b : ℕ) (B : Matrix (Fin n) (Fin a) K) (A : Matrix (Fin n) (Fin b) K),
      LinearIndependent K (fromCols B A)ᵀ ∧
      Submodule.span K (Set.range Bᵀ) = W ⊓ perpD σ d W ∧
      Submodule.span K (Set.range (fromCols B A)ᵀ) = W ∧
      ((fromCols B A).map σ)ᵀ * (d⁻¹).val * B = 0 ∧ (B.map σ)ᵀ * (d⁻¹).val * fromCols B A = 0 ∧
      ((A.map σ)ᵀ * (d⁻¹).val * A).det ≠ 0 := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (W ⊓ perpD σ d W)
  have hC : (W ⊓ perpD σ d W) ⊔ (Q ⊓ W) = W := by
    rw [← sup_inf_assoc_of_le Q (inf_le_left : W ⊓ perpD σ d W ≤ W), hQ.sup_eq_top, top_inf_eq]
  have hdis : Disjoint (W ⊓ perpD σ d W) (Q ⊓ W) := hQ.disjoint.mono_right inf_le_left
  obtain ⟨a, u, hu, hus⟩ : ∃ (a : ℕ) (u : Fin a → Fin n → K), LinearIndependent K u ∧
      Submodule.span K (Set.range u) = W ⊓ perpD σ d W := ⟨_, _, cols_li _, cols_span _⟩
  obtain ⟨b, v, hv, hvs⟩ : ∃ (b : ℕ) (v : Fin b → Fin n → K), LinearIndependent K v ∧
      Submodule.span K (Set.range v) = Q ⊓ W := ⟨_, _, cols_li _, cols_span _⟩
  have hum : ∀ j, u j ∈ W ⊓ perpD σ d W := fun j => hus ▸ Submodule.subset_span ⟨j, rfl⟩
  have hvm : ∀ j, v j ∈ Q ⊓ W := fun j => hvs ▸ Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin a) K, Bᵀ = u := ⟨(Matrix.of u)ᵀ, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin b) K, Aᵀ = v := ⟨(Matrix.of v)ᵀ, rfl⟩
  have hT : ((fromCols B A)ᵀ : _ → _ → K) = Sum.elim u v := by
    subst hB hA
    funext s k
    rcases s with j | j <;> rfl
  have hspan : Submodule.span K (Set.range (fromCols B A)ᵀ) = W := by
    rw [hT, Set.Sum.elim_range, Submodule.span_union, hus, hvs, hC]
  have hli : LinearIndependent K (fromCols B A)ᵀ := by
    rw [hT]
    exact hu.sum_type hv (by rw [hus, hvs]; exact hdis)
  have hFW : ∀ s, (fun k => fromCols B A k s) ∈ W := fun s => by
    have : (fun k => fromCols B A k s) ∈ Submodule.span K (Set.range (fromCols B A)ᵀ) :=
      Submodule.subset_span ⟨s, rfl⟩
    rwa [hspan] at this
  have hr : ∀ w ∈ W ⊓ perpD σ d W, ∀ x ∈ W, form σ (d⁻¹).val x w = 0 := fun w hw x hx =>
    (mem_perpD σ d W w).1 hw.2 x hx
  have hl : ∀ w ∈ W ⊓ perpD σ d W, ∀ x ∈ W, form σ (d⁻¹).val w x = 0 := fun w hw x hx => by
    rw [← hW] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    rw [Matrix.toLin'_apply, form_swap σ hσ _ γ hγ, hr w hw x' hx', map_zero]
  have hBc : ∀ j, (fun k => B k j) = u j := fun j => congrFun hB j
  have hAc : ∀ j, (fun k => A k j) = v j := fun j => congrFun hA j
  refine ⟨_, _, B, A, hli, by rw [hB]; exact hus, hspan, ?_, ?_, ?_⟩
  · ext i j
    rw [entry, hBc]
    exact hr _ (hum j) _ (hFW i)
  · ext i j
    rw [entry, hBc]
    exact hl _ (hum i) _ (hFW j)
  · intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hAv : A *ᵥ c = ∑ j, c j • v j := by
      rw [Matrix.mulVec_eq_sum, hA]
      exact Finset.sum_congr rfl fun j _ => op_smul_eq_smul _ _
    have hyC : A *ᵥ c ∈ Q ⊓ W := by
      rw [hAv]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvm j)
    have hyW : A *ᵥ c ∈ W := hyC.2
    have hcol : ∀ s, form σ (d⁻¹).val (fun k => fromCols B A k s) (A *ᵥ c) = 0 := by
      rintro (j | j)
      · have h := hl _ (hum j) _ hyW
        rw [← hBc j] at h
        exact h
      · have := congrFun hc j
        rw [entry_mulVec] at this
        exact this
    have hperp : A *ᵥ c ∈ perpD σ d W := by
      rw [mem_perpD]
      intro x hx
      rw [← hspan] at hx
      induction hx using Submodule.span_induction with
      | mem x h =>
        obtain ⟨s, rfl⟩ := h
        exact hcol s
      | zero => exact form_zero_left _ _ _
      | add x y _ _ hx hy => rw [form_add_left, hx, hy, add_zero]
      | smul a x _ hx => rw [form_smul_left, hx, mul_zero]
    have hy0 : A *ᵥ c = 0 := by
      have := hdis.le_bot (show A *ᵥ c ∈ _ from ⟨⟨hyW, hperp⟩, hyC⟩)
      simpa using this
    apply hc0
    have hsum : ∑ j, c j • v j = 0 := by rw [← hAv, hy0]
    funext j
    exact Fintype.linearIndependent_iff.1 hv c hsum j

theorem radical : Radical := by
  intro E _ _ _ n d W hW
  have hσ : ∀ x, conjE E (conjE E x) = x := fun x => NumberField.IsCMField.complexConj_apply_apply E x
  refine exists_adapted (conjE E) hσ d (nrm d).val ?_ W hW
  have h2 : (d⁻¹).val * d.val = 1 := Units.inv_mul d
  rw [nrm, Units.val_mul, ← mul_assoc, h2, one_mul, thetaR_val]

end GlobalTheory.CompanionTheory.RadicalForm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RefinedBlockOrderCompat
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.CellChar

section Finite

variable {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β']
  {c : α → β' → Type} [∀ i j, Fintype (c i j)]

theorem prod_row (i : α) (S : β' → Prop) [DecidablePred S] {G : Type} [CommMonoid G] (a : G) :
    ∏ q : (Σ i, Σ j, c i j), (if q.1 = i ∧ S q.2.1 then a else 1) =
      a ^ (∑ b with S b, Fintype.card (c i b)) := by
  rw [Fintype.prod_sigma, Finset.prod_eq_single i]
  · rw [Fintype.prod_sigma]
    calc _ = ∏ j, (if S j then a ^ Fintype.card (c i j) else 1) :=
          Finset.prod_congr rfl fun j _ => by split_ifs with h <;> simp [h]
      _ = ∏ j with S j, a ^ Fintype.card (c i j) := (Finset.prod_filter _ _).symm
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
  · intro b _ hb
    exact Finset.prod_eq_one fun q _ => by simp [hb]
  · simp

theorem prod_rel {G : Type} [CommGroupWithZero G] (v : (Σ i, Σ j, c i j) → G) (hv : ∀ q, v q ≠ 0) :
    ∏ p : (Σ i, Σ j, c i j), ∏ q : (Σ i, Σ j, c i j),
        (if q.1 = p.1 ∧ p.2.1 < q.2.1 then v p / v q else 1) =
      ∏ i, ∏ j, (∏ t, v ⟨i, j, t⟩) ^ modExp (c i) j := by
  have h1 : ∀ p q : (Σ i, Σ j, c i j), (if q.1 = p.1 ∧ p.2.1 < q.2.1 then v p / v q else 1) =
      (if q.1 = p.1 ∧ p.2.1 < q.2.1 then v p else 1) *
        (if q.1 = p.1 ∧ p.2.1 < q.2.1 then (v q)⁻¹ else 1) := by
    intro p q
    split_ifs
    · rw [div_eq_mul_inv]
    · simp
  simp_rw [h1, Finset.prod_mul_distrib]
  have h3 : (∏ p : (Σ i, Σ j, c i j), ∏ q : (Σ i, Σ j, c i j),
        if q.1 = p.1 ∧ p.2.1 < q.2.1 then (v q)⁻¹ else 1) =
      ∏ p : (Σ i, Σ j, c i j), ∏ q : (Σ i, Σ j, c i j),
        if p.1 = q.1 ∧ q.2.1 < p.2.1 then (v p)⁻¹ else 1 := Finset.prod_comm
  rw [h3, ← Finset.prod_mul_distrib]
  have h2 : ∀ p : (Σ i, Σ j, c i j),
      (∏ q : (Σ i, Σ j, c i j), if q.1 = p.1 ∧ p.2.1 < q.2.1 then v p else 1) *
        (∏ q : (Σ i, Σ j, c i j), if p.1 = q.1 ∧ q.2.1 < p.2.1 then (v p)⁻¹ else 1) =
      v p ^ modExp (c p.1) p.2.1 := by
    intro p
    simp_rw [eq_comm (a := p.1)]
    rw [prod_row p.1 (fun b => p.2.1 < b), prod_row p.1 (fun b => b < p.2.1), modExp,
      zpow_sub₀ (hv p), inv_pow, div_eq_mul_inv, ← zpow_natCast, ← zpow_natCast]
    push_cast
    rfl
  rw [Finset.prod_congr rfl fun p _ => h2 p, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact Finset.prod_zpow (fun t => v ⟨i, j, t⟩) Finset.univ (modExp (c i) j)

theorem prod_pairs {N : ℕ} {m : α → Type} (e : (Σ i, m i) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i)
    (β δ : Fin N → ℕ) (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y)
    (hδ : ∀ i j j' (t : c i j) (t' : c i j'),
      δ (e ⟨i, f i ⟨j, t⟩⟩) < δ (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j')
    {G : Type} [CommGroupWithZero G] (u : Fin N → G) (hu : ∀ x, u x ≠ 0) :
    ∏ s : {ij : Fin N × Fin N // β ij.1 = β ij.2 ∧ δ ij.1 < δ ij.2}, u s.1.1 / u s.1.2 =
      ∏ i, ∏ j, (∏ t : c i j, u (e ⟨i, f i ⟨j, t⟩⟩)) ^ modExp (c i) j := by
  classical
  let ε : (Σ i, Σ j, c i j) ≃ Fin N := (Equiv.sigmaCongrRight f).trans e
  have hε : ∀ i j t, ε ⟨i, j, t⟩ = e ⟨i, f i ⟨j, t⟩⟩ := fun _ _ _ => rfl
  have hβe : ∀ x y, β x = β y ↔ blk e x = blk e y := fun x y => by
    constructor
    · intro h
      by_contra hne
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact absurd ((hβ x y).2 h') (by omega)
      · exact absurd ((hβ y x).2 h') (by omega)
    · intro h
      by_contra hne
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact absurd ((hβ x y).1 h') (by simp [h])
      · exact absurd ((hβ y x).1 h') (by simp [h])
  have hR : ∀ p q : (Σ i, Σ j, c i j),
      (β (ε p) = β (ε q) ∧ δ (ε p) < δ (ε q)) ↔ (q.1 = p.1 ∧ p.2.1 < q.2.1) := by
    rintro ⟨i, j, t⟩ ⟨i', j', t'⟩
    rw [hε, hε, hβe, blk_apply, blk_apply]
    constructor
    · rintro ⟨rfl, hd⟩
      exact ⟨rfl, (hδ _ _ _ _ _).1 hd⟩
    · rintro ⟨h1, h2⟩
      obtain rfl : i' = i := h1
      exact ⟨rfl, (hδ _ _ _ _ _).2 h2⟩
  refine Eq.trans ?_ (prod_rel (c := c) (fun p => u (ε p)) fun _ => hu _)
  rw [← Finset.prod_subtype (Finset.univ.filter fun ij : Fin N × Fin N =>
    β ij.1 = β ij.2 ∧ δ ij.1 < δ ij.2) (by simp) (fun ij => u ij.1 / u ij.2), Finset.prod_filter,
    Fintype.prod_prod_type]
  refine (Equiv.prod_comp ε _).symm.trans (Finset.prod_congr rfl fun p _ => ?_)
  refine (Equiv.prod_comp ε _).symm.trans (Finset.prod_congr rfl fun q _ => ?_)
  simp only [hR]

end Finite

end GlobalTheory.CompanionTheory.CellChar

namespace GlobalTheory.CompanionTheory.CellChar

open ValuativeRel GroundTheory.Automorphic.GLnLocal

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {k} in

theorem valuation_det_eq_one {n : Type} [Fintype n] [DecidableEq n] (A : GL n k)
    (h1 : ∀ a b, (A : Matrix n n k) a b ∈ (valuation k).integer)
    (h2 : ∀ a b, ((A⁻¹ : GL n k) : Matrix n n k) a b ∈ (valuation k).integer) :
    valuation k ((Matrix.GeneralLinearGroup.det A : kˣ) : k) = 1 := by
  have hdet : ∀ M : Matrix n n k, (∀ a b, M a b ∈ (valuation k).integer) →
      M.det ∈ (valuation k).integer := fun M hM => by
    rw [Matrix.det_apply']
    exact Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _)
      (Subring.prod_mem _ fun i _ => hM _ _)
  have a1 : valuation k ((Matrix.GeneralLinearGroup.det A : kˣ) : k) ≤ 1 := hdet _ h1
  have a2 : valuation k (((Matrix.GeneralLinearGroup.det A)⁻¹ : kˣ) : k) ≤ 1 := by
    rw [← map_inv]
    exact hdet _ h2
  rw [Units.val_inv_eq_inv_val, map_inv₀] at a2
  exact le_antisymm a1 ((inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 (Units.ne_zero _)))).1 a2)

variable {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ}
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]

theorem relDeltaHalf_eq_one_of_integral (e : (Σ i, m i) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i)
    (x : Levi k m) (hx : x ∈ relParab k f) (hint : leviEmb k e x ∈ integralGL k N) :
    relDeltaHalf k c (relProj k f ⟨x, hx⟩) = 1 := by
  obtain ⟨h1, h2⟩ := (mem_integralGL_iff k N).1 hint
  rw [relDeltaHalf_apply]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun j _ => ?_
  refine isUnram_absPow k _ _ (valuation_det_eq_one _ (fun a b => ?_) fun a b => ?_)
  · have := h1 (e ⟨i, f i ⟨j, a⟩⟩) (e ⟨i, f i ⟨j, b⟩⟩)
    rw [leviEmb_apply_same] at this
    exact this
  · have := h2 (e ⟨i, f i ⟨j, a⟩⟩) (e ⟨i, f i ⟨j, b⟩⟩)
    rw [← map_inv, leviEmb_apply_same] at this
    have e1 : ((relProj k f ⟨x, hx⟩ i j)⁻¹ : GL (c i j) k) = relProj k f (⟨x, hx⟩⁻¹) i j := by
      rw [map_inv]
      rfl
    rw [e1]
    exact this

theorem nabs_det_diag (e : (Σ i, m i) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i)
    (x : Levi k m) (hx : x ∈ relParab k f) (μ : Fin N → ℤ)
    (hd : leviEmb k e x = GroundTheory.Automorphic.Cartan.diagPow k N μ) (i : α) (j : β') :
    GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det (relProj k f ⟨x, hx⟩ i j)) =
      ∏ t : c i j, ((GroundTheory.Automorphic.Measures.modulus
        ((uniformizer k : k) ^ μ (e ⟨i, f i ⟨j, t⟩⟩)) : NNReal) : ℝ) := by
  have hent : ((relProj k f ⟨x, hx⟩ i j : GL (c i j) k) : Matrix (c i j) (c i j) k) =
      Matrix.diagonal fun t => (uniformizer k : k) ^ μ (e ⟨i, f i ⟨j, t⟩⟩) := by
    ext a b
    have h0 : ((relProj k f ⟨x, hx⟩ i j : GL (c i j) k) : Matrix (c i j) (c i j) k) a b =
        (leviEmb k e x : Matrix (Fin N) (Fin N) k) (e ⟨i, f i ⟨j, a⟩⟩) (e ⟨i, f i ⟨j, b⟩⟩) := by
      rw [leviEmb_apply_same]
      rfl
    rw [h0, hd, GroundTheory.Automorphic.Cartan.coe_diagPow]
    by_cases hab : a = b
    · subst hab
      simp
    · have hne : e ⟨i, f i ⟨j, a⟩⟩ ≠ e ⟨i, f i ⟨j, b⟩⟩ := fun h => hab (by simpa using h)
      rw [Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hab]
  have hdet : ((Matrix.GeneralLinearGroup.det (relProj k f ⟨x, hx⟩ i j) : kˣ) : k) =
      ∏ t, (uniformizer k : k) ^ μ (e ⟨i, f i ⟨j, t⟩⟩) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hent, Matrix.det_diagonal]
  rw [GlobalTheory.SplitWeil.nabs, ← GroundTheory.Automorphic.Measures.modulus_units, hdet, map_prod, NNReal.coe_prod]

theorem relDeltaHalf_diag (e : (Σ i, m i) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i)
    (x : Levi k m) (hx : x ∈ relParab k f) (μ : Fin N → ℤ)
    (hd : leviEmb k e x = GroundTheory.Automorphic.Cartan.diagPow k N μ) :
    ((relDeltaHalf k c (relProj k f ⟨x, hx⟩) : ℂˣ) : ℂ) =
      ((√(∏ i, ∏ j, (∏ t : c i j, ((GroundTheory.Automorphic.Measures.modulus
        ((uniformizer k : k) ^ μ (e ⟨i, f i ⟨j, t⟩⟩)) : NNReal) : ℝ)) ^ modExp (c i) j) : ℝ) : ℂ) := by
  have h1 : ∀ i, GlobalTheory.SmGL.modulus k (c i) (relProj k f ⟨x, hx⟩ i) =
      ∏ j, (∏ t : c i j, ((GroundTheory.Automorphic.Measures.modulus
        ((uniformizer k : k) ^ μ (e ⟨i, f i ⟨j, t⟩⟩)) : NNReal) : ℝ)) ^ modExp (c i) j := fun i => by
    rw [GlobalTheory.SmGL.modulus]
    exact Finset.prod_congr rfl fun j _ => by rw [nabs_det_diag k e f x hx μ hd i j]
  simp_rw [← h1]
  rw [relDeltaHalf_apply, Units.coe_prod,
    Real.sqrt_prod _ fun i _ => (GlobalTheory.SmGL.modulus_pos k _).le, Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun i _ => val_deltaHalf k _

theorem normLeviParSqrtModular_diag (e : (Σ i, m i) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i)
    (β δ : Fin N → ℕ) (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y)
    (hδ : ∀ i j j' (t : c i j) (t' : c i j'),
      δ (e ⟨i, f i ⟨j, t⟩⟩) < δ (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j')
    (x : Levi k m) (hx : x ∈ relParab k f) (μ : Fin N → ℤ)
    (hd : leviEmb k e x = GroundTheory.Automorphic.Cartan.diagPow k N μ) :
    normLeviParSqrtModular k β δ ⟨GroundTheory.Automorphic.Cartan.diagPow k N μ,
      GroundTheory.Automorphic.Parabolic.diagPow_mem_leviPar μ⟩ =
      ((relDeltaHalf k c (relProj k f ⟨x, hx⟩) : ℂˣ) : ℂ) := by
  rw [relDeltaHalf_diag k e f x hx μ hd]
  show ((NNReal.sqrt (MeasureTheory.Measure.modularCharacter _) : ℝ) : ℂ) = _
  rw [GroundTheory.Automorphic.Parabolic.modularCharacter_leviPar_diagPow,
    prod_pairs e f β δ hβ hδ (fun y => GroundTheory.Automorphic.Measures.modulus
      ((uniformizer k : k) ^ μ y)) fun y => GroundTheory.Automorphic.Measures.modulus_ne_zero
        (zpow_ne_zero _ (GroundTheory.Automorphic.Cartan.uniformizer_ne_zero k)),
    Real.coe_sqrt]
  push_cast
  rfl

end Local

theorem normLeviParSqrtModular_eq_relDeltaHalf : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {c : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (e : (Σ i, m i) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i) (β δ : Fin N → ℕ) (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (hδ : ∀ i j j' (t : c i j) (t' : c i j'), δ (e ⟨i, f i ⟨j, t⟩⟩) < δ (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j') (hmem : ∀ x : Levi k m, x ∈ relParab k f ↔ leviEmb k e x ∈ blockUpper k N δ) (φ : Levi k m ≃* levi k N β) (hφ : ∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) (x : Levi k m) (hx : x ∈ relParab k f) (h : ((φ x : levi k N β) : GL (Fin N) k) ∈ leviPar k N β δ), normLeviParSqrtModular k β δ ⟨_, h⟩ = ((relDeltaHalf k c (relProj k f ⟨x, hx⟩) : ℂˣ) : ℂ) := by
  intro k _ _ _ _ α β' _ _ _ _ N m _ _ c _ _ e f β δ hβ hδ hmem φ hφ x hx h
  have hinv : ∀ y : levi k N β, leviEmb k e (φ.symm y) = (y : GL (Fin N) k) := fun y => by
    rw [← hφ, φ.apply_symm_apply]
  let Θ : leviPar k N β δ →* relParab k f :=
    { toFun := fun l => ⟨φ.symm ⟨l.1, l.2.1⟩, (hmem _).2 (by rw [hinv]; exact l.2.2)⟩
      map_one' := Subtype.ext (map_one φ.symm)
      map_mul' := fun a b => Subtype.ext (map_mul φ.symm ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩) }
  let ψ : leviPar k N β δ →* ℂ :=
    (Units.coeHom ℂ).comp ((relDeltaHalf k c).comp ((relProj k f).comp Θ))
  obtain ⟨μ, hμ⟩ := GroundTheory.Automorphic.Parabolic.exists_diagPow_eq (F := k) (γ := β) (δ := δ) ⟨_, h⟩
  have e1 := hμ (normLeviParSqrtModular k β δ) fun l hl =>
    GroundTheory.Automorphic.Parabolic.normLeviParSqrtModular_eq_one hl
  have e2 := hμ ψ fun l hl => by
    show ((relDeltaHalf k c (relProj k f (Θ l)) : ℂˣ) : ℂ) = 1
    rw [show Θ l = ⟨(Θ l).1, (Θ l).2⟩ from rfl,
      relDeltaHalf_eq_one_of_integral k e f _ _ (by
        show leviEmb k e (φ.symm ⟨l.1, l.2.1⟩) ∈ _
        rw [hinv]
        exact hl)]
    rfl
  have e3 : ψ ⟨_, h⟩ = ((relDeltaHalf k c (relProj k f ⟨x, hx⟩) : ℂˣ) : ℂ) := by
    have h3 : Θ ⟨_, h⟩ = ⟨x, hx⟩ := Subtype.ext (φ.symm_apply_apply x)
    show ((relDeltaHalf k c (relProj k f (Θ ⟨_, h⟩)) : ℂˣ) : ℂ) = _
    rw [h3]
  rw [e1, ← e3, e2]
  exact normLeviParSqrtModular_diag k e f β δ hβ hδ _ (Θ _).2 μ (hinv _)

end GlobalTheory.CompanionTheory.CellChar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreVanishingFirstCohomology
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

theorem serre_vanishing_coh_one : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {F : X.Modules}, IsCoherent F → ∃ n₂ : ℤ, ∀ n, n₂ ≤ n → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ F H n) 1) := by
  intro A _ _ X _ _ H hH F hF
  letI : Algebra A ↑(X.presheaf.obj (Opposite.op ⊤)) :=
    ((X ↘ Spec (.of A)).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom).toAlgebra
  obtain ⟨hq, hfin⟩ := hF
  haveI : GlobalTheory.QCoh.IsFiniteQC F := GlobalTheory.QCoh.IsFiniteQC.mk hq hfin
  haveI : IsProper ((X ↘ Spec (.of A)) : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A) := ‹IsProper (X ↘ Spec (.of A))›
  have hev := GlobalTheory.IsAmpleLB.eventually_subsingleton_coh_twistZ (R := A)
    (f := ((X ↘ Spec (.of A)) : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A)) (fun _ => rfl) F hH
  obtain ⟨n₂, hn⟩ := Filter.eventually_atTop.1 hev
  exact ⟨n₂, fun n hn' => hn n hn' 1 Nat.one_pos⟩

end GlobalTheory.CompanionTheory.GE.Step
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedComplexCohomologyStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shifted_complex_cohomology : ∀ {K : Type} [Field K] (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) (n : ℕ), (n < k → Subsingleton ((Sh ς k C).H n)) ∧ ∀ (m : ℕ) (h : m + k = n), ∃ e : C.H m ≃ₗ[K] (Sh ς k C).H n, ∀ (y : (Sh ς k C).X n) (hy : (Sh ς k C).d n y = 0) (hy' : C.d m (y ⟨m, h⟩) = 0), e (C.cls (y ⟨m, h⟩) hy') = (Sh ς k C).cls y hy := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.ShiftCoh.main | exact GlobalTheory.CompanionTheory.KunGlue.ShiftCoh.main | (intros; apply GlobalTheory.CompanionTheory.KunGlue.ShiftCoh.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedSystemDescendsStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shifted_system_descends : ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] (ς : ℤˣ) (k : ℕ) (A : Sy.{1} K ι), A.Desc → (shSy ς k A).Desc := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.ShDesc.sh_desc | exact GlobalTheory.CompanionTheory.KunGlue.ShDesc.sh_desc | (intros; apply GlobalTheory.CompanionTheory.KunGlue.ShDesc.sh_desc <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeFinitePlaces
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.Dblock.SzFinProof

theorem finite_one_lt_norm_cW {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (a : Ad E) :
    {w : HeightOneSpectrum (𝓞 E) | 1 < ‖cW w a‖}.Finite := by
  delta PositivityTheory.Rg.BcB.cW GlobalTheory.CuspRep.pLoc GlobalTheory.CuspRep.pFin
  have h := RestrictedProduct.eventually _ _ (RingHom.snd (InfiniteAdeleRing E) (Af E) a)
  refine (Filter.eventually_cofinite.mp h).subset ?_
  intro w hw
  simp only [Set.mem_ofPred_eq, RingHom.comp_apply, RestrictedProduct.evalRingHom_apply] at hw ⊢
  intro hmem
  exact absurd hw (not_lt.mpr (Valued.toNormedField.norm_le_one_iff.mpr
    ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hmem)))

theorem szFin : SzFin := by
  intro E _ _ _ ι κ _ _ A
  refine (Set.Finite.biUnion (s := (Set.univ : Set (ι × κ))) Set.finite_univ
    fun p _ => finite_one_lt_norm_cW (A p.1 p.2)).subset ?_
  intro w hw
  change 1 < ⨆ p : ι × κ, ‖(A.map (PositivityTheory.Rg.BcB.cW w)) p.1 p.2‖ at hw
  rcases isEmpty_or_nonempty (ι × κ) with hι | hι
  · rw [Real.iSup_of_isEmpty] at hw
    exact absurd hw (by norm_num)
  · obtain ⟨p, hp⟩ := exists_lt_of_lt_ciSup hw
    exact Set.mem_biUnion (Set.mem_univ p) hp

end GlobalTheory.CompanionTheory.Dblock.SzFinProof
end

