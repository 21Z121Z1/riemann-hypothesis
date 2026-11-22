import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0047
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0033
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0048
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstVertexParahoricLevelChainTwist
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

noncomputable section
namespace GlobalTheory.TwistVertex

section Plain
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem toBlocks₁₁_eq_one {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) : u.val.toBlocks₁₁ = 1 := by
  ext i j
  have := RootEx.Model.mem_N_iff.1 hu (.inl i) (.inl j) le_rfl
  simpa [toBlocks₁₁, Matrix.one_apply] using this

theorem val_embX (g : GL n k) : (embX c g).val = fromBlocks g.val 0 0 1 := rfl

end Plain

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section General
variable {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem embX_mem_KO {g : GL n k} (hg : g ∈ KO k n) : embX c g ∈ KO k (n ⊕ Fin c) := by
  obtain ⟨h1, h2⟩ := mem_KO.1 hg
  refine mem_KO.2 ⟨?_, ?_⟩
  · rw [val_embX]; exact intM_fromBlocks.2 ⟨h1, intM_zero, intM_zero, intM_one⟩
  · rw [← map_inv, val_embX]; exact intM_fromBlocks.2 ⟨h2, intM_zero, intM_zero, intM_one⟩

theorem mem_KO_of_mul_embX {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) {g : GL n k}
    (h : u * embX c g ∈ KO k (n ⊕ Fin c)) : g ∈ KO k n := by
  obtain ⟨h1, h2⟩ := mem_KO.1 h
  have e1 : (u * embX c g).val.toBlocks₁₁ = g.val := by
    rw [Units.val_mul, mul_toBlocks₁₁, toBlocks₁₁_eq_one hu, val_embX]; simp
  have e2 : ((u * embX c g)⁻¹).val.toBlocks₁₁ = (g⁻¹).val := by
    rw [_root_.mul_inv_rev, ← map_inv, Units.val_mul, mul_toBlocks₁₁, toBlocks₁₁_eq_one (inv_mem hu), val_embX]; simp
  exact mem_KO.2 ⟨e1 ▸ fun i j => h1 _ _, e2 ▸ fun i j => h2 _ _⟩

theorem simpleSum_mem {u : GL (n ⊕ Fin c) k} (hu : u ∈ KO k (n ⊕ Fin c)) : simpleSum u ∈ 𝒪[k] := by
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  split_ifs
  · exact intM_of_mem_KO hu _ _
  · exact zero_mem _

end General

section Empty
variable {r e n : Type*} [Fintype r] [DecidableEq r] [Fintype e] [DecidableEq e] [IsEmpty e]
  [Fintype n] [DecidableEq n] {c : ℕ} {δ : kˣ →* ℂˣ} {hδ : IsTame δ}

theorem mem_level_iff (o : r ⊕ e ≃ n ⊕ Fin c) (x : GL (n ⊕ Fin c) k) :
    x ∈ ((parahoric r e δ hδ).toLevel.map (plainFrame o).conj).J ↔ x ∈ KO k (n ⊕ Fin c) := by
  have e0 : ∀ y : GL (n ⊕ Fin c) k, ((plainFrame (k := k) o).conj.symm y).val = y.val.submatrix o o := by
    intro y
    have : (plainFrame (k := k) o).conj.symm y = (reGL o).symm y := by
      rw [MulEquiv.symm_apply_eq, LatFrame.conj_apply]; simp [plainFrame]
    rw [this, reGL_symm_val]
  rw [Level.mem_map, mem_parahoric, mem_KO, mem_KO, ← map_inv, e0, e0]
  refine ⟨fun ⟨⟨h1, h2⟩, _⟩ => ⟨fun i j => ?_, fun i j => ?_⟩,
    fun ⟨h1, h2⟩ => ⟨⟨fun i j => h1 _ _, fun i j => h2 _ _⟩, fun i => isEmptyElim i⟩⟩
  · simpa using h1 (o.symm i) (o.symm j)
  · have := h2 (o.symm i) (o.symm j)
    rwa [submatrix_apply, o.apply_symm_apply, o.apply_symm_apply] at this

theorem level_lam (o : r ⊕ e ≃ n ⊕ Fin c)
    (x : ((parahoric r e δ hδ).toLevel.map (plainFrame o).conj).J) :
    ((parahoric r e δ hδ).toLevel.map (plainFrame o).conj).lam x = 1 := by
  rw [Level.map_lam, parahoric_lam _ 1 (by ext i; exact isEmptyElim i), map_one, map_one]

end Empty

theorem firstVertex_twist : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ (s : ℕ) (t : Type) [Fintype t] [DecidableEq t] (κ : Type) [Fintype κ] [DecidableEq κ] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (c : ℕ) (H : 0 + c = s + 1), (prX (Cgrp ((twistChain s t κ δ hδ η).lev 0 c H).J 1) : Set (GL (XIx κ t 0) k)) = KO k (XIx κ t 0) ∧ (∀ γ ∈ KO k (XIx κ t 0), ∃ hm : embX c γ ∈ ((twistChain s t κ δ hδ η).lev 0 c H).J, (((twistChain s t κ δ hδ η).lev 0 c H).lam ⟨_, hm⟩ : ℂ) = 1) ∧ ∀ u ∈ N k (XIx κ t 0) c 1, ∀ hm : u ∈ ((twistChain s t κ δ hδ η).lev 0 c H).J, (((twistChain s t κ δ hδ η).lev 0 c H).lam ⟨u, hm⟩ : ℂ) = ψ (simpleSum u) := by
  intro k _ _ _ _ ψ hψ s t _ _ κ _ _ δ hδ η c H
  have hJ : ∀ x, x ∈ ((twistChain s t κ δ hδ η).lev 0 c H).J ↔ x ∈ KO k (XIx κ t 0 ⊕ Fin c) :=
    fun x => mem_level_iff (hδ := hδ) (stdOrd κ t 0 c H) x
  have hl : ∀ x, ((twistChain s t κ δ hδ η).lev 0 c H).lam x = 1 :=
    fun x => level_lam (hδ := hδ) (stdOrd κ t 0 c H) x
  refine ⟨?_, fun γ hγ => ⟨(hJ _).2 (embX_mem_KO hγ), by rw [hl]; rfl⟩, fun u _ hm => ?_⟩
  · ext g
    simp only [SetLike.mem_coe, mem_prX, mem_Cgrp, hJ, inv_one, one_mul, mul_one]
    refine ⟨fun ⟨u, hu, _, h⟩ => mem_KO_of_mul_embX hu h, fun hg => ⟨1, one_mem _, ?_, ?_⟩⟩
    · rw [one_mul]; exact (le_sup_left : (embX c).range ≤ R k _ c 1) ⟨g, rfl⟩
    · rw [one_mul]; exact embX_mem_KO hg
  · rw [hl, hψ.eq_one (show _ ∈ cball (1 : kˣ) from simpleSum_mem ((hJ u).1 hm))]; rfl

end GlobalTheory.TwistVertex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorMovedTensorFinsetSumLinear
section
open MeasureTheory GlobalTheory.FunObj

namespace GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx

theorem flatTensor_moved_sum {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : GlobalTheory.SplitFlip.Grid k) (hs : 1 ≤ G.s)
    (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (hψ : Continuous ψ) (ϖ : kˣ) (e : ℕ) (keep : Bool)
    (g : G.VertexGroup) {ι : Type} (S : Finset ι) (x : ι → ℂ) (T : ι → G.Args → ℂ)
    (hT : ∀ i ∈ S, G.IsTensor ϖ e (GlobalTheory.SplitFlip.oppositePath G.m) (T i)) (X : ColArgs G) (Y : RowArgs G) :
    flatTensor hs ψ ν (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y =
      ∑ i ∈ S, x i * flatTensor hs ψ ν (moved G keep g (T i)) X Y := by
  classical
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hint : ∀ i ∈ S, Integrable (flatIntegrand hs ψ (moved G keep g (T i)) X Y) (varsVol G ν) := by
    intro i hi
    unfold varsVol
    exact (continuous_flatIntegrand hs hψ (hT i hi) keep g X Y).integrable_of_hasCompactSupport
      (hasCompactSupport_flatIntegrand hs ψ (hT i hi) keep g X Y)
  have h : ∀ v, flatIntegrand hs ψ (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y v =
      ∑ i ∈ S, x i * flatIntegrand hs ψ (moved G keep g (T i)) X Y v := by
    intro v
    simp only [flatIntegrand, moved, GlobalTheory.SplitFlip.Grid.pathAct, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [flatTensor, h]
  rw [integral_finset_sum _ fun i hi => (hint i hi).const_mul _]
  simp only [integral_const_mul]

end GlobalTheory.FunObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericLevelOfFrameBlockAndCharacter
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.GenericShape

theorem superSum_one {F : Type} [Field F] {κ : ℕ} : superSum Fin.val (1 : Matrix (Fin κ) (Fin κ) F) = 0 := by
  refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => ?_
  split_ifs with e
  · rw [Matrix.one_apply_ne]; rintro rfl; omega
  · rfl

open MeasureTheory ValuativeRel Matrix Topology in
private lemma map_residue_apply {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {a : Type} [Fintype a] [DecidableEq a] (M : GL a 𝒪[k]) (i j : a) :
    ((GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) M : GL a 𝓀[k]) : Matrix a a 𝓀[k]) i j =
      IsLocalRing.residue 𝒪[k] ((M : Matrix a a 𝒪[k]) i j) := by
  simp

open MeasureTheory ValuativeRel Matrix Topology in
private lemma reduces_of_corner_lemma {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {κ l : ℕ} {g : GL (Fin κ ⊕ Fin l) k} {γ : GL (Fin κ) k}
    {g₀ : GL (Fin κ ⊕ Fin l) 𝒪[k]} (hg : GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀ = g)
    (hγ : (g : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k).toBlocks₁₁ = γ)
    (hres : ∀ r s : Fin κ, s ≤ r → IsLocalRing.residue 𝒪[k]
      ((g₀ : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) 𝒪[k]) (Sum.inl r) (Sum.inl s)) =
        (1 : Matrix (Fin κ) (Fin κ) 𝓀[k]) r s) :
    ∃ gb, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.Reduces γ gb ∧
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUpperUnip Fin.val (gb : Matrix (Fin κ) (Fin κ) 𝓀[k]) := by
  subst hg
  set A : Matrix (Fin κ) (Fin κ) 𝒪[k] :=
    (g₀ : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) 𝒪[k]).toBlocks₁₁ with hA
  have hB : ∀ r s, s ≤ r → IsLocalRing.residue 𝒪[k] (A r s) = (1 : Matrix (Fin κ) (Fin κ) 𝓀[k]) r s :=
    hres
  have hdet : IsUnit A.det := by
    apply IsLocalRing.notMem_maximalIdeal.1
    intro hm
    rw [← IsLocalRing.residue_eq_zero_iff, RingHom.map_det, Matrix.det_of_upperTriangular] at hm
    · have hp : ∏ i, (IsLocalRing.residue 𝒪[k]).mapMatrix A i i = 1 :=
        Finset.prod_eq_one fun i _ => by simp [RingHom.mapMatrix_apply, hB i i le_rfl]
      rw [hp] at hm
      exact one_ne_zero hm
    · intro i j hij
      have hij' : j < i := hij
      simp [RingHom.mapMatrix_apply, hB i j hij'.le, Matrix.one_apply_ne (ne_of_lt hij').symm]
  let γ₀ : GL (Fin κ) 𝒪[k] := A.nonsingInvUnit hdet
  refine ⟨GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) γ₀, ⟨γ₀, ?_, rfl⟩, ?_⟩
  · ext i j
    rw [← hγ]
    rfl
  · intro r s hsr
    rw [map_residue_apply]
    exact hres r s hsr

open MeasureTheory ValuativeRel Matrix Topology in
private lemma toBlocks₁₁_mul_embX_of_mem_N {k : Type*} [Field k] {κ l p : ℕ}
    {u : GL (Fin κ ⊕ Fin l) k} (hu : u ∈ _root_.GlobalTheory.RootEx.N k (Fin κ) l p)
    (γ : GL (Fin κ) k) :
    ((u * _root_.GlobalTheory.RootEx.embX l γ : GL (Fin κ ⊕ Fin l) k) :
      Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k).toBlocks₁₁ = γ := by
  rw [Units.val_mul, _root_.GlobalTheory.StepData.mul_toBlocks₁₁, _root_.GlobalTheory.RootEx.Radical.toBlocks₁₁_of_mem hu,
    _root_.GlobalTheory.RootEx.Radical.embX_val]
  simp

open MeasureTheory ValuativeRel Matrix Topology in
private lemma one_apply_inl_inl {F a b : Type*} [Zero F] [One F] [DecidableEq a] [DecidableEq b]
    (r s : a) : (1 : Matrix (a ⊕ b) (a ⊕ b) F) (Sum.inl r) (Sum.inl s) = (1 : Matrix a a F) r s := by
  by_cases h : r = s <;> simp [Matrix.one_apply, h]

open MeasureTheory ValuativeRel Matrix Topology in
private lemma reduces_embX_of_reduces {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {κ l : ℕ} {γ : GL (Fin κ) k}
    {gb : GL (Fin κ) 𝓀[k]} (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.Reduces γ gb) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.Reduces (_root_.GlobalTheory.RootEx.embX l γ)
      (_root_.GlobalTheory.RootEx.embX l gb) := by
  obtain ⟨γ₀, h₁, h₂⟩ := h
  subst h₁ h₂
  let g₀ : GL (Fin κ ⊕ Fin l) 𝒪[k] :=
    ⟨fromBlocks (γ₀ : Matrix (Fin κ) (Fin κ) 𝒪[k]) 0 0 1,
      fromBlocks ((γ₀⁻¹ : GL (Fin κ) 𝒪[k]) : Matrix (Fin κ) (Fin κ) 𝒪[k]) 0 0 1,
      by rw [fromBlocks_multiply]; simp, by rw [fromBlocks_multiply]; simp⟩
  refine ⟨g₀, ?_, ?_⟩ <;> ext i j <;> rcases i with i | i <;> rcases j with j | j <;>
    simp [g₀, _root_.GlobalTheory.RootEx.Radical.embX_val, Matrix.one_apply, apply_ite]

open MeasureTheory ValuativeRel Matrix Topology in
private lemma one_apply_inr_inr {F a b : Type*} [Zero F] [One F] [DecidableEq a] [DecidableEq b]
    (r s : b) : (1 : Matrix (a ⊕ b) (a ⊕ b) F) (Sum.inr r) (Sum.inr s) = (1 : Matrix b b F) r s := by
  by_cases h : r = s <;> simp [Matrix.one_apply, h]

open MeasureTheory ValuativeRel Matrix Topology in
private lemma superSum_framePos_embX {k : Type} [Field k] {κ l : ℕ} (γ : GL (Fin κ) k) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ l)
        ((_root_.GlobalTheory.RootEx.embX l γ : GL (Fin κ ⊕ Fin l) k) :
          Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val (γ : Matrix (Fin κ) (Fin κ) k) := by
  have hl : ∀ i : Fin κ, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ l (Sum.inl i) = i := fun i => by
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos]
  have hr : ∀ i : Fin l, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ l (Sum.inr i) = κ + i := fun i => by
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos]
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum
  simp only [Fintype.sum_sum_type, _root_.GlobalTheory.RootEx.Radical.embX_val, hl, hr,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply,
    ite_self, Finset.sum_const_zero, add_zero, zero_add]
  have h : ∑ i : Fin l, ∑ j : Fin l,
      (if κ + (j : ℕ) = κ + i + 1 then (1 : Matrix (Fin l) (Fin l) k) i j else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hij
    · exact Matrix.one_apply_ne fun h => by subst h; omega
    · rfl
  linear_combination h

open MeasureTheory ValuativeRel Matrix Topology in
private lemma superSum_framePos_eq_simpleSum_of_mem_N {k : Type} [Field k] {κ l : ℕ}
    {u : GL (Fin κ ⊕ Fin l) k} (hu : u ∈ _root_.GlobalTheory.RootEx.N k (Fin κ) l 1) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ l)
        (u : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) =
      _root_.GlobalTheory.RootEx.simpleSum u := by
  rw [_root_.GlobalTheory.RootEx.Model.mem_N_iff] at hu
  unfold _root_.GlobalTheory.RootEx.InN at hu
  have hl : ∀ i : Fin κ, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ l (Sum.inl i) = i := fun i => by
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos]
  have hr : ∀ i : Fin l, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos κ l (Sum.inr i) = κ + i := fun i => by
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos]
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum _root_.GlobalTheory.RootEx.simpleSum
  simp only [Fintype.sum_sum_type, hl, hr]
  have h₁ : ∑ i : Fin κ, ∑ j : Fin κ, (if (j : ℕ) = i + 1 then
      (u : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) (Sum.inl i) (Sum.inl j) else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hij
    · rw [hu _ _ (by simp [_root_.GlobalTheory.RootEx.lev])]
      exact Matrix.one_apply_ne fun h => by
        have := congrArg (fun x : Fin κ ⊕ Fin l => Sum.elim (fun a : Fin κ => (a : ℕ)) (fun _ => 0) x) h
        simp at this
        omega
    · rfl
  have h₂ : ∑ i : Fin κ, ∑ j : Fin l, (if κ + (j : ℕ) = i + 1 then
      (u : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) (Sum.inl i) (Sum.inr j) else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hij
    · rw [hu _ _ (by simp [_root_.GlobalTheory.RootEx.lev]; omega)]
      simp
    · rfl
  have h₃ : ∑ i : Fin l, ∑ j : Fin κ, (if (j : ℕ) = κ + i + 1 then
      (u : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) (Sum.inr i) (Sum.inl j) else 0) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg (by omega)]
  have h₄ : ∀ i j : Fin l, (κ + (j : ℕ) = κ + i + 1) ↔ ((j : ℕ) = i + 1) := fun i j => by omega
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [h₄]
  linear_combination h₁ + h₂ + h₃

open MeasureTheory ValuativeRel Matrix Topology in

theorem _root_.GlobalTheory.GenericShape.generic_shape : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (ϖ : kˣ) (κ l : ℕ) (P : _root_.GlobalTheory.StepData.TypeDatum k (Fin κ ⊕ Fin l)), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsGenericLevel ψ ϖ P → ((∀ u ∈ _root_.GlobalTheory.RootEx.N k (Fin κ) l 1, ∀ γ : GL (Fin κ) k, u * _root_.GlobalTheory.RootEx.embX l γ ∈ P.J → ∃ gb, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.Reduces γ gb ∧ _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUpperUnip Fin.val gb.val) ∧ (∀ (γ : GL (Fin κ) k) (gb : GL (Fin κ) 𝓀[k]), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.Reduces γ gb → _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUpperUnip Fin.val gb.val → ∃ hm : _root_.GlobalTheory.RootEx.embX l γ ∈ P.J, (P.lam ⟨_, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.superSum Fin.val γ.val)) ∧ ∀ u ∈ _root_.GlobalTheory.RootEx.N k (Fin κ) l 1, ∀ hm : u ∈ P.J, (P.lam ⟨u, hm⟩ : ℂ) = ψ ((ϖ⁻¹ : kˣ) * _root_.GlobalTheory.RootEx.simpleSum u)) := by
  intro k _ _ _ _ ψ ϖ κ l P h
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsGenericLevel at h
  obtain ⟨hJ, hlam⟩ := h
  refine ⟨fun u hu γ hm => ?_, fun γ gb hred hup => ?_, fun u hu hm => ?_⟩
  · obtain ⟨gb', ⟨g₀, hg₀, hres₀⟩, hup'⟩ := (hJ _).1 hm
    refine reduces_of_corner_lemma hg₀ (toBlocks₁₁_mul_embX_of_mem_N hu γ) fun r s hsr => ?_
    rw [← map_residue_apply, hres₀]
    exact (hup' (Sum.inl r) (Sum.inl s) (by simpa [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos] using hsr)).trans
      (one_apply_inl_inl r s)
  · have hm : _root_.GlobalTheory.RootEx.embX l γ ∈ P.J := by
      refine (hJ _).2 ⟨_root_.GlobalTheory.RootEx.embX l gb, reduces_embX_of_reduces hred, ?_⟩
      intro r s hrs
      rcases r with r | r <;> rcases s with s | s
      · have h' : (s : ℕ) ≤ r := by simpa [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos] using hrs
        rw [_root_.GlobalTheory.RootEx.Radical.embX_val, fromBlocks_apply₁₁]
        exact (hup r s h').trans (one_apply_inl_inl r s).symm
      · have h' : κ + (s : ℕ) ≤ r := by simpa [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos] using hrs
        omega
      · rw [_root_.GlobalTheory.RootEx.Radical.embX_val, fromBlocks_apply₂₁]
        simp [Matrix.one_apply]
      · rw [_root_.GlobalTheory.RootEx.Radical.embX_val, fromBlocks_apply₂₂]
        exact (one_apply_inr_inr r s).symm
    refine ⟨hm, ?_⟩
    rw [hlam ⟨_, hm⟩]
    simp only [superSum_framePos_embX]
  · rw [hlam ⟨u, hm⟩, superSum_framePos_eq_simpleSum_of_mem_N hu]

end GlobalTheory.GenericShape
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarCompactOpenRatioEqZpowOfTopNilpotent
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.VolPow

open MeasureTheory ValuativeRel Matrix Topology in
open scoped Pointwise in
private lemma finiteIndex_and_index_subgroupOf_eq_pow {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (q : ℕ) (hq : q.Prime)
    (hpow : ∀ u : G, ∀ U ∈ 𝓝 (1 : G), ∃ m : ℕ, u ^ (q ^ m) ∈ U) {H K : Subgroup G}
    (hH : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO H) (hK : IsOpen (K : Set G)) :
    (K.subgroupOf H).FiniteIndex ∧ ∃ b : ℕ, (K.subgroupOf H).index = q ^ b := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH.2
  set K' := K.subgroupOf H
  have hK' : IsOpen (K' : Set H) := hK.preimage continuous_subtype_val
  haveI : Finite (H ⧸ K') := Subgroup.quotient_finite_of_isOpen K' hK'
  haveI : K'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set N := K'.normalCore
  have hNo : IsOpen (N : Set H) :=
    N.isOpen_of_isClosed_of_finiteIndex (K'.normalCore_isClosed (K'.isClosed_of_isOpen hK'))
  haveI : Finite (H ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  have hp : IsPGroup q (H ⧸ N) := by
    intro x
    induction x using QuotientGroup.induction_on with | H u => ?_
    have hU : (Subtype.val '' (N : Set H)) ∈ 𝓝 (1 : G) :=
      (hH.1.isOpenMap_subtype_val _ hNo).mem_nhds ⟨1, N.one_mem, rfl⟩
    obtain ⟨m, hm⟩ := hpow (u : G) _ hU
    obtain ⟨v, hv, hvu⟩ := hm
    refine ⟨m, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have e : v = u ^ (q ^ m) := Subtype.ext (by rw [hvu]; simp)
    rwa [← e]
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hp
  have hdvd : K'.index ∣ q ^ a := by
    rw [← ha]
    exact Subgroup.index_dvd_of_le (Subgroup.normalCore_le K')
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hq).1 hdvd
  exact ⟨inferInstance, b, hb⟩

open MeasureTheory ValuativeRel Matrix Topology in
open scoped Pointwise in
private lemma measure_eq_index_subgroupOf_mul_measure {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsMulLeftInvariant] {H K : Subgroup G} (hKH : K ≤ H) (hK : IsOpen (K : Set G))
    [(K.subgroupOf H).FiniteIndex] :
    μ H = ((K.subgroupOf H).index : ENNReal) * μ K := by
  classical
  set K' := K.subgroupOf H
  letI : Fintype (H ⧸ K') := Subgroup.fintypeQuotientOfFiniteIndex
  have hcover : (H : Set G) = ⋃ c : H ⧸ K', ((Quotient.out c : H) : G) • (K : Set G) := by
    ext g
    constructor
    · intro hg
      refine Set.mem_iUnion.2 ⟨(QuotientGroup.mk (⟨g, hg⟩ : H) : H ⧸ K'), ?_⟩
      obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul K' (⟨g, hg⟩ : H)
      refine Set.mem_smul_set.2 ⟨((y⁻¹ : K') : H), ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.1 (y⁻¹).2
      · rw [smul_eq_mul, hy]
        simp
    · intro hg
      obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hg
      obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hc
      exact H.mul_mem (Quotient.out c).2 (hKH hy)
  have hdisj : Pairwise (fun c d : H ⧸ K' => Disjoint (((Quotient.out c : H) : G) • (K : Set G))
      (((Quotient.out d : H) : G) • (K : Set G))) := by
    intro c d hcd
    rw [Set.disjoint_left]
    rintro g hgc hgd
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hgc
    obtain ⟨z, hz, hzy⟩ := Set.mem_smul_set.1 hgd
    apply hcd
    rw [← Quotient.out_eq c, ← Quotient.out_eq d]
    apply (QuotientGroup.eq (s := K')).2
    rw [Subgroup.mem_subgroupOf]
    have e : (((Quotient.out c : H)⁻¹ * Quotient.out d : H) : G) = y * z⁻¹ := by
      simp only [smul_eq_mul] at hzy
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, hzy]
      group
    rw [e]
    exact K.mul_mem hy (K.inv_mem hz)
  rw [hcover, measure_iUnion hdisj (fun c => (hK.smul _).measurableSet), tsum_fintype]
  simp only [measure_smul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Subgroup.index,
    Nat.card_eq_fintype_card]

open MeasureTheory ValuativeRel Matrix Topology in
open scoped Pointwise in

theorem _root_.GlobalTheory.VolPow.vol_div_eq_zpow : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (q : ℕ), q.Prime → (∀ u : G, ∀ U ∈ 𝓝 (1 : G), ∃ m : ℕ, u ^ (q ^ m) ∈ U) → ∀ H₁ H₂ : Subgroup G, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO H₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO H₂ → ∃ z : ℤ, (μ H₁).toReal / (μ H₂).toReal = (q : ℝ) ^ z := by
  intro G _ _ _ _ _ μ _ q hq hpow H₁ H₂ h₁ h₂
  have hK : IsOpen ((H₁ ⊓ H₂ : Subgroup G) : Set G) := h₁.1.inter h₂.1
  obtain ⟨hf₁, b₁, hb₁⟩ := finiteIndex_and_index_subgroupOf_eq_pow q hq hpow (K := H₁ ⊓ H₂) h₁ hK
  obtain ⟨hf₂, b₂, hb₂⟩ := finiteIndex_and_index_subgroupOf_eq_pow q hq hpow (K := H₁ ⊓ H₂) h₂ hK
  have e₁ := measure_eq_index_subgroupOf_mul_measure μ (H := H₁) inf_le_left hK
  have e₂ := measure_eq_index_subgroupOf_mul_measure μ (H := H₂) inf_le_right hK
  have hcpt : IsCompact ((H₁ ⊓ H₂ : Subgroup G) : Set G) :=
    h₁.2.of_isClosed_subset ((H₁ ⊓ H₂).isClosed_of_isOpen hK)
      (fun x hx => (inf_le_left : H₁ ⊓ H₂ ≤ H₁) hx)
  have hpos : 0 < (μ (H₁ ⊓ H₂ : Subgroup G)).toReal :=
    ENNReal.toReal_pos (hK.measure_ne_zero μ ⟨1, (H₁ ⊓ H₂).one_mem⟩) hcpt.measure_lt_top.ne
  refine ⟨(b₁ : ℤ) - b₂, ?_⟩
  rw [e₁, e₂, hb₁, hb₂, ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_natCast]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  rw [zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
  field_simp
  push_cast
  ring

end GlobalTheory.VolPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMeasurePiChangeConstant
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical

namespace GlobalTheory.IdealChain

theorem pi_nnreal_smul {ι X : Type} [Fintype ι] [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (c : NNReal) :
    (Measure.pi fun _ : ι => c • μ) = (c ^ Fintype.card ι) • Measure.pi fun _ : ι => μ := by
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.pi_pi]
  simp only [Measure.coe_nnreal_smul_apply, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ENNReal.coe_pow]

theorem integral_scale_change_haar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ι : Type) [Fintype ι] (ν νs : Measure k) (d : ι → kˣ), ν.IsAddHaarMeasure → νs.IsAddHaarMeasure → ∃ C : ℝ, (0 < C ∧ (IsHalfPow k (ν (𝒪[k] : Set k)).toReal → IsHalfPow k (νs (𝒪[k] : Set k)).toReal → IsHalfPow k C)) ∧ ∀ F : (ι → k) → ℂ, ∫ e, F e ∂(Measure.pi fun _ => ν) = C * ∫ e, F (fun i => (d i : k) * e i) ∂(Measure.pi fun _ => νs) := by
  intro k _ _ _ _ _ _ ι _ ν νs d hν hνs
  classical
  have := secondCountable k
  have := t2Space k
  obtain ⟨a, ha0, ha⟩ : ∃ a : NNReal, 0 < a ∧ ν = a • νs :=
    ⟨_, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν νs, Measure.isAddLeftInvariant_eq_smul ν νs⟩
  let g : GL ι k := ⟨Matrix.diagonal fun i => (d i : k), Matrix.diagonal fun i => ((d i)⁻¹ : kˣ),
    by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩
  have hpos := nabs_pos' (Matrix.GeneralLinearGroup.det g)
  refine ⟨(a : ℝ) ^ Fintype.card ι * nabs k (Matrix.GeneralLinearGroup.det g),
    ⟨mul_pos (pow_pos ha0 _) hpos, fun h1 h2 => isHalfPow_mul (isHalfPow_pow ?_ _) (isHalfPow_nabs _)⟩, fun F => ?_⟩
  · have h3 : (νs (𝒪[k] : Set k)).toReal ≠ 0 := by
      obtain ⟨e, he⟩ := h2
      rw [he]
      exact (Real.rpow_pos_of_pos resCard_pos _).ne'
    have h4 : (a : ℝ) = (ν (𝒪[k] : Set k)).toReal * ((νs (𝒪[k] : Set k)).toReal)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ h3, ha, Measure.coe_nnreal_smul_apply, ENNReal.toReal_mul, ENNReal.coe_toReal]
    rw [h4]
    exact isHalfPow_mul h1 (isHalfPow_inv h2)
  · have h := integral_comp_mulVec_eq_smul νs g F
    have h2 : ∀ x : ι → k, g.val.mulVec x = fun i => (d i : k) * x i := by
      intro x; funext i; simp [g, Matrix.mulVec_diagonal]
    simp only [h2] at h
    have h5 : (Measure.pi fun _ : ι => ν) = (a ^ Fintype.card ι) • Measure.pi fun _ : ι => νs := by
      rw [← pi_nnreal_smul, ← ha]
    rw [h, h5, integral_smul_nnreal_measure]
    have : (nabs k (Matrix.GeneralLinearGroup.det g) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [Complex.real_smul, NNReal.smul_def, Complex.real_smul]
    push_cast
    field_simp

end GlobalTheory.IdealChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonicStatement
section
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monic_poly_eq_qdet : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), ∃ c : ℕ → A, c n = 1 ∧ ∀ u : ℂ, qdet E u = ∑ i ∈ range (n + 1), u ^ i • c i := by
  first | exact @GlobalTheory.qdet_polyMap_monic | exact GlobalTheory.qdet_polyMap_monic | (intros; apply GlobalTheory.qdet_polyMap_monic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatSweepSmoothlyInducedStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_sweep_smoothly_induced : ∀ (G X Y W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [AddCommGroup W] [Module ℂ W] (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) → Continuous (fun p : X × G => r p.1 p.2) → ∀ (j : Y → X), IsClosedEmbedding j → ∀ (P : Subgroup G) (K : Set G), IsCompact K → (∀ x, ∃ y, ∃ c ∈ K, x = r (j y) c) → ∀ (s : Y → P → Y), (∀ y (p : P), r (j y) p = j (s y p)) → (∀ y y' g, r (j y) g = j y' → g ∈ P) → ∀ (χ : G →* ℂˣ), IsSmoothChar χ → ∀ (σ : Representation ℂ P W) (ev : W ≃ₗ[ℂ] SB Y), (∀ (p : P) w y, (ev (σ p w)).1 y = (χ p : ℂ) * (ev w).1 (s y p)) → ∃ E : SB X ≃ₗ[ℂ] smoothPart (ind P σ), ∀ Φ g y, (ev ((E Φ).1.1 g)).1 y = (χ g : ℂ) * Φ.1 (r (j y) g) := by
  first | exact @GlobalTheory.SBInduced.sb_induced | exact GlobalTheory.SBInduced.sb_induced | (intros; apply GlobalTheory.SBInduced.sb_induced <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracedQminorComatrixTruncatedInverseStatement
section
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traced_qminor_comatrix_truncated_inverse : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A), GlRel E → ∀ (u : ℂ) (N : ℕ), algebraMap ℂ A ((u - m) ^ (N + 1)) * ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u + algebraMap ℂ A ((-1) ^ N) * ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor E (Fin.succAbove j) (Fin.succAbove i) u * epow E (N + 1) j i = qdet E u * ∑ k ∈ range (N + 1), algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * etr E k := by
  first | exact @GlobalTheory.TracedComatrix.traced_comatrix | exact GlobalTheory.TracedComatrix.traced_comatrix | (intros; apply GlobalTheory.TracedComatrix.traced_comatrix <;> assumption)
end

