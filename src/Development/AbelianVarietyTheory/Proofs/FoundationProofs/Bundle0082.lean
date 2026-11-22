import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0065
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0067
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlSqSubMemOldformsGamma1
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem GlobalTheory.HeckeFamilyMatrices.ulSq_old : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (f : CuspForm (Lev N l) (k : ℤ)),
  (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 (N * l) → ⇑f ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f) →
  ∃ f₁ f₂ : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ),
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₁ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₁) ∧
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₂ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₂) ∧
    UlF (k : ℤ) l (UlF (k : ℤ) l ⇑f) - (χ l * (l : ℂ) ^ (k - 2)) • ⇑f = ⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1) := by
  intro N l k hN hl hlN hk χ f hf
  have hN0 : 0 < N := by omega
  have hl0 : 0 < l := hl.pos
  obtain ⟨u, v, huv⟩ : IsCoprime (l : ℤ) (N : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN)
  have h : (l : ℤ) * u - N * (-v) = 1 := by linear_combination huv
  haveI : NeZero N := ⟨hN0.ne'⟩
  haveI : NeZero l := ⟨hl0.ne'⟩
  haveI : (Lev N l).FiniteIndex := by unfold Lev; infer_instance
  set W := wOld N l (-v) u with hW
  set D := dg (l : ℤ) 1 with hD
  have hWdet : 0 < W.det := by
    rw [hW, wOld, Matrix.det_fin_two_of]; nlinarith
  have hDdet : 0 < D.det := by
    rw [hD, dg, Matrix.det_fin_two_of]; simpa using hl0
  set F : ℍ → ℂ := ⇑f with hFdef
  have hF : ChiInv (k : ℤ) N (N * l) χ F := hf
  have cF : CuspAll (k : ℤ) F := GlobalTheory.T.cuspForm_isCuspidalAtAllCuspsSL2 (Lev N l) k f
  set G := F ∣[(k : ℤ)] toGL W with hGdef
  have hG : ChiInv (k : ℤ) N (N * l) χ G := GlobalTheory.T.nebentypus_slash_oldformLevelRaisingMatrix N l k (-v) u h χ F hl0 hF
  have cG : CuspAll (k : ℤ) G := GlobalTheory.T.isCuspidalAtAllCuspsSL2_slash_intMatrix k W F hWdet cF
  have cTr : ∀ H, CuspAll (k : ℤ) H → CuspAll (k : ℤ) (trOld k N l (-v) u h H) := by
    intro H hH
    unfold trOld
    refine cuspAll_add hH ?_
    induction (Finset.range l) using Finset.induction_on with
    | empty => simpa using cuspAll_smul 0 hH
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      refine cuspAll_add ?_ ih
      rw [slash_SL_eq]
      exact GlobalTheory.T.isCuspidalAtAllCuspsSL2_slash_intMatrix k _ H (by simp [mat]) hH
  set A := trOld k N l (-v) u h F with hAdef
  set B := trOld k N l (-v) u h G with hBdef
  have hA : ChiInv (k : ℤ) N N χ A := GlobalTheory.T.nebentypus_oldformTraceToGammaOne N l k (-v) u h χ F hN0 hl hF
  have hB : ChiInv (k : ℤ) N N χ B := GlobalTheory.T.nebentypus_oldformTraceToGammaOne N l k (-v) u h χ G hN0 hl hG
  have cA : CuspAll (k : ℤ) A := cTr F cF
  have cB : CuspAll (k : ℤ) B := cTr G cG
  set C := B ∣[(k : ℤ)] toGL D with hCdef
  have hC : ChiInv (k : ℤ) N (N * l) χ C := GlobalTheory.T.nebentypus_slash_intDiagTwoMatrix_levelRaise N l k χ B hl0 hB
  have cC : CuspAll (k : ℤ) C := GlobalTheory.T.isCuspidalAtAllCuspsSL2_slash_intMatrix k D B hDdet cB
  have hTC : ChiInv (k : ℤ) N N χ (trOld k N l (-v) u h C) := GlobalTheory.T.nebentypus_oldformTraceToGammaOne N l k (-v) u h χ C hN0 hl hC
  have cTC : CuspAll (k : ℤ) (trOld k N l (-v) u h C) := cTr C cC
  set c₁ : ℂ := χ (l : ZMod N) with hc₁
  set p : ℂ := (l : ℂ) ^ ((k : ℤ) - 2) with hp
  have h₁ : ChiInv (k : ℤ) N N χ (c₁ ^ 2 • trOld k N l (-v) u h C + (-(c₁ * p)) • A) :=
    chiInv_add (chiInv_smul _ hTC) (chiInv_smul _ hA)
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.T.exists_cuspForm_gammaOne_of_nebentypus_cuspidal N k χ (c₁ ^ 2 • trOld k N l (-v) u h C + (-(c₁ * p)) • A) hN0
    (cuspAll_add (cuspAll_smul _ cTC) (cuspAll_smul _ cA)) h₁
  obtain ⟨f₂, hf₂⟩ := GlobalTheory.T.exists_cuspForm_gammaOne_of_nebentypus_cuspidal N k χ (-(c₁ ^ 2) • B) hN0 (cuspAll_smul _ cB) (chiInv_smul _ hB)
  refine ⟨f₁, f₂, fun γ hγ => ?_, fun γ hγ => ?_, ?_⟩
  · rw [hf₁]; exact h₁ γ hγ
  · rw [hf₂]; exact chiInv_smul _ hB γ hγ
  rw [hf₁, hf₂]
  have e1 := GlobalTheory.T.oldformTraceToGammaOne_eq_heckeUl_levelRaising N l k (-v) u h F hl0
  have e2 := GlobalTheory.T.oldformTraceToGammaOne_eq_heckeUl_levelRaising N l k (-v) u h G hl0
  have e3 := GlobalTheory.T.oldformLevelRaising_slash_slash_nebentypus N l k (-v) u h χ F hl0 hF
  have e4 := GlobalTheory.T.heckeUl_eq_nebentypus_oldformTrace_sub_diag N l k (-v) u h χ B hl0 hB
  rw [← hAdef, ← hGdef] at e1
  rw [← hBdef, e3] at e2
  rw [← hCdef] at e4
  have cb : c₁ * χ (u : ZMod N) = 1 := by
    rw [hc₁, ← map_mul]
    have h2 := congrArg (Int.cast : ℤ → ZMod N) h
    push_cast at h2
    rw [ZMod.natCast_self] at h2
    rw [show ((l : ZMod N) * (u : ZMod N)) = 1 by linear_combination h2, map_one]
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
  have pp : p * (l : ℂ) ^ (2 - (k : ℤ)) = 1 := by
    rw [hp, ← zpow_add₀ hl']; simp
  have hUG : UlF k l G = p • (A - F) := by
    rw [e1, add_sub_cancel_left, smul_smul, pp, one_smul]
  have hUF : UlF k l F = c₁ • (B - G) := by
    have key : c₁ * (l : ℂ) ^ (2 - (k : ℤ)) * ((l : ℂ) ^ ((k : ℤ) - 2) * χ (u : ZMod N)) = 1 := by
      rw [← hp]
      calc c₁ * (l : ℂ) ^ (2 - (k : ℤ)) * (p * χ (u : ZMod N))
          = (p * (l : ℂ) ^ (2 - (k : ℤ))) * (c₁ * χ (u : ZMod N)) := by ring
        _ = 1 := by rw [pp, cb, one_mul]
    rw [e2, add_sub_cancel_left, ulF_smul k l hl0, smul_smul, smul_smul, key, one_smul]
  have hpk : (l : ℂ) ^ (k - 2) = p := by
    rw [hp, show ((k : ℤ) - 2) = ((k - 2 : ℕ) : ℤ) by omega, zpow_natCast]
  rw [hpk, hUF, ulF_smul k l hl0, ulF_sub k l hl0, e4, hUG, smul_slash_toGL k D hDdet, ← hCdef]
  funext τ
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergSumCompOfAdjacentOfInfEqStatement
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergSum_comp_of_adjacent_of_inf_eq : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → Adj A B → idx A C ≠ 0 → A ⊓ C = B ⊓ C → ∀ v, Fixes W A v → sumOp W B C (sumOp W A B v) = lam (idx A B) • sumOp W A C v := by
  first | exact @GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq | exact GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq | (intros; apply GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomogeneousLiftCompatible
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem homogeneous_lift_compatible : ∀ (l : ℕ) [Fact l.Prime] (w : ℕ) (p : (n : ℕ) → MvPolynomial (Fin 2) (ZMod (l ^ n))), (∀ n, (p n).IsHomogeneous w) → (∀ n, MvPolynomial.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n))) (p (n + 1)) = p n) → ∃ q : MvPolynomial (Fin 2) ℤ_[l], q.IsHomogeneous w ∧ (∀ n, MvPolynomial.map (PadicInt.toZModPow n) q = p n) ∧ ∀ q' : MvPolynomial (Fin 2) ℤ_[l], (∀ n, MvPolynomial.map (PadicInt.toZModPow n) q' = p n) → q' = q := by
  intro l _ w p hhom hcomp
  have hc1 : ∀ (m : Fin 2 →₀ ℕ) (n : ℕ),
      ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) ((p (n + 1)).coeff m) = (p n).coeff m := by
    intro m n
    rw [← hcomp n, MvPolynomial.coeff_map]
  have hc : ∀ (m : Fin 2 →₀ ℕ) (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂),
      ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k₁)) ((p k₂).coeff m) = (p k₁).coeff m := by
    intro m k₁ k₂ hk
    induction k₂, hk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [← ih, ← hc1 m k]
      show _ = ((ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k₁))).comp
        (ZMod.castHom (pow_dvd_pow l (Nat.le_succ k)) (ZMod (l ^ k)))) _
      rw [ZMod.castHom_comp]

  let f : ∀ k, MvPolynomial (Fin 2 →₀ ℕ) ℤ →+* ZMod (l ^ k) := fun k =>
    MvPolynomial.eval₂Hom (Int.castRingHom _) (fun m => (p k).coeff m)
  have hf : ∀ k₁ k₂ (hk : k₁ ≤ k₂),
      (ZMod.castHom (pow_dvd_pow l hk) (ZMod (l ^ k₁))).comp (f k₂) = f k₁ := by
    intro k₁ k₂ hk
    apply MvPolynomial.ringHom_ext
    · intro r; simp [f]
    · intro m
      simp only [f, RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact hc m k₁ k₂ hk
  let g := PadicInt.lift hf
  let c : (Fin 2 →₀ ℕ) → ℤ_[l] := fun m => g (MvPolynomial.X m)
  have hcn : ∀ m n, PadicInt.toZModPow n (c m) = (p n).coeff m := by
    intro m n
    have := congrArg (fun φ => φ (MvPolynomial.X m)) (PadicInt.lift_spec hf n)
    simpa [c, g, f] using this
  have hdeg : ∀ m, c m ≠ 0 → m.degree = w := by
    intro m hm
    by_contra hne
    apply hm
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [hcn, map_zero]
    by_contra h0
    apply hne
    rw [Finsupp.degree_eq_weight_one]
    exact hhom n h0
  have hfin : (Function.support c).Finite :=
    (Finsupp.finite_of_degree_le w).subset fun m hm => le_of_eq (hdeg m hm)
  let q : MvPolynomial (Fin 2) ℤ_[l] := ∑ m ∈ hfin.toFinset, MvPolynomial.monomial m (c m)
  have hq : ∀ m, q.coeff m = c m := by
    intro m
    simp only [q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at h
      exact h.symm
  refine ⟨q, ?_, ?_, ?_⟩
  · intro m hm
    rw [hq] at hm
    have h := hdeg m hm
    rw [Finsupp.degree_eq_weight_one] at h
    exact h
  · intro n
    ext m
    rw [MvPolynomial.coeff_map, hq, hcn]
  · intro q' hq'
    ext m
    rw [hq]
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [hcn, ← hq' n, MvPolynomial.coeff_map]

end GlobalTheory.KZ.H3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomogeneousPolyCoeffEqZero
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory

theorem homogeneous_poly_coeff_eq_zero (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    (htf : ∀ (c : ℤ_[l]) (x : M), c ≠ 0 → c • x = 0 → x = 0) (w : ℕ) (c : Fin (w + 1) → M)
    (hv : ∀ u : Fin 2 → ℤ_[l], ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i = 0) :
    c = 0 := by
  set V : Matrix (Fin (w + 1)) (Fin (w + 1)) ℤ_[l] := Matrix.vandermonde (fun t : Fin (w + 1) => ((t : ℕ) : ℤ_[l])) with hVdef
  have hrow : ∀ t : Fin (w + 1), ∑ i, V t i • c i = 0 := by
    intro t
    have := hv ![((t : ℕ) : ℤ_[l]), 1]
    simpa [hVdef, Matrix.vandermonde_apply] using this
  have hdet : V.det ≠ 0 := by
    rw [hVdef, Matrix.det_vandermonde_ne_zero_iff]
    intro a b hab
    apply Fin.ext
    have hab' : ((a : ℕ) : ℤ_[l]) = ((b : ℕ) : ℤ_[l]) := hab
    exact_mod_cast hab'
  have key : ∀ j, V.det • c j = 0 := by
    intro j
    have h1 : ∑ t, V.adjugate j t • ∑ i, V t i • c i = 0 := by simp [hrow]
    have h2 : ∑ t, V.adjugate j t • ∑ i, V t i • c i = ∑ i, (V.adjugate * V) j i • c i := by
      simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
      rw [Finset.sum_comm]
    rw [h2, Matrix.adjugate_mul] at h1
    simpa [Matrix.smul_apply, Matrix.one_apply, ite_smul, Finset.sum_ite_eq] using h1
  funext j
  exact htf _ _ hdet (key j)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ.BettiB

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def BtN (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (n : ℕ) (b : X.Fn l)
    (c : Gam N l → MvPolynomial (Fin 2) (ZMod (l ^ n))) : Prop :=
  ∀ u : Fin 2 → ℤ_[l], ∃ χ : SL(2, ℤ) → ZMod (l ^ n), H3.Kum X l n (b u) χ ∧ ∃ M : ℕ, 0 < M ∧
    ∀ δ : Gam N l, (δ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M →
      MvPolynomial.eval (fun i => PadicInt.toZModPow n (u i)) (c δ) = χ δ

def BtZ (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (b : X.Fn l) (c : Gam N l → MvPolynomial (Fin 2) ℤ_[l]) : Prop :=
  ∀ n : ℕ, BtN X N l n b (fun δ => MvPolynomial.map (PadicInt.toZModPow n) (c δ))

def Z1 (N l w : ℕ) [Fact l.Prime] : Submodule ℤ_[l] (Gam N l → MvPolynomial (Fin 2) ℤ_[l]) where
  carrier := {c | (∀ γ, (c γ).IsHomogeneous w) ∧
    ∀ γ δ : Gam N l, c (γ * δ) = slP ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (c γ) + c δ}
  add_mem' := by
    rintro c c' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun γ => (h1 γ).add (h1' γ), fun γ δ => ?_⟩
    simp only [Pi.add_apply, h2, h2', map_add]; abel
  zero_mem' := ⟨fun γ => MvPolynomial.isHomogeneous_zero _ _ _, fun γ δ => by simp⟩
  smul_mem' := by
    rintro r c ⟨h1, h2⟩
    refine ⟨fun γ => ?_, fun γ δ => ?_⟩
    · simpa [MvPolynomial.smul_eq_C_mul] using (MvPolynomial.isHomogeneous_C _ r).mul (h1 γ)
    · simp only [Pi.smul_apply, h2, map_smul, smul_add]

theorem hs_codiscrete_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  rw [Filter.neBot_iff]
  intro h
  have hmem : (∅ : Set ℂ) ∈ Filter.codiscreteWithin Hs := by rw [h]; exact Filter.mem_bot
  rw [mem_codiscreteWithin] at hmem
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have hd := hmem Complex.I hI
  simp only [Set.diff_empty] at hd
  have hopen : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im
  have hle : nhdsWithin Complex.I {Complex.I}ᶜ ≤ Filter.principal Hs :=
    le_trans nhdsWithin_le_nhds (Filter.le_principal_iff.2 (hopen.mem_nhds hI))
  have hbot : nhdsWithin Complex.I {Complex.I}ᶜ = ⊥ := by
    have := hd.mono_right hle
    exact disjoint_self.1 this
  exact (NormedField.nhdsNE_neBot Complex.I).ne hbot

theorem btZ_zero (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] : BtZ X N l 0 0 := by
  intro n u
  refine ⟨0, ⟨1, fun _ => 1, fun _ => 1, 1, one_pos, ?_, ?_, ?_⟩, 1, one_pos, fun δ _ => by simp⟩
  · simp [Tower.cls]
  · apply H3.isRoot_one
    haveI := hs_codiscrete_neBot
    exact one_ne_zero
  · intro δ _ z _; simp

end GlobalTheory.KZ.BettiB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntMatrixActionMemHomogeneousPolyFunctions
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.PolAct

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

def homF (A : Submodule R M) (w : ℕ) : Submodule R ((Fin 2 → R) → M) where
  carrier := {b | ∃ c : Fin (w + 1) → M, (∀ i, c i ∈ A) ∧
    ∀ u, b u = ∑ i : Fin (w + 1), (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i}
  zero_mem' := ⟨0, fun _ => A.zero_mem, fun u => by simp⟩
  add_mem' := by
    rintro a b ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    exact ⟨c + d, fun i => A.add_mem (hc i) (hd i), fun u => by
      simp [ha, hb, Finset.sum_add_distrib]⟩
  smul_mem' := by
    rintro r b ⟨c, hc, hb⟩
    exact ⟨r • c, fun i => A.smul_mem r (hc i), fun u => by
      simp only [Pi.smul_apply, hb, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _⟩

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma const_mem_homF_zero {A : Submodule R M} {x : M} (hx : x ∈ A) :
    (fun _ : Fin 2 → R => x) ∈ _root_.GlobalTheory.KZ.PolAct.homF A 0 :=
  ⟨fun _ => x, fun _ => hx, fun u => by simp⟩

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma coord_zero_smul_mem_homF_succ {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) :
    (fun u => u 0 • b u) ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + 1) := by
  obtain ⟨c, hc, hbu⟩ := hb
  refine ⟨Fin.cons 0 c, fun i => ?_, fun u => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp [A.zero_mem]
    · simp [hc]
  · dsimp only
    rw [hbu, Finset.smul_sum]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_zero, zero_add, Fin.val_succ,
      Nat.add_sub_add_right, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma coord_one_smul_mem_homF_succ {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) :
    (fun u => u 1 • b u) ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + 1) := by
  obtain ⟨c, hc, hbu⟩ := hb
  refine ⟨fun j => if h : (j : ℕ) < n + 1 then c ⟨j, h⟩ else 0, fun j => ?_, fun u => ?_⟩
  · dsimp only
    split_ifs
    · exact hc _
    · exact A.zero_mem
  · dsimp only
    rw [hbu, Finset.smul_sum]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_self_iff_false,
      dif_neg, not_false_eq_true, smul_zero, add_zero, Fin.eta, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : n + 1 - (i : ℕ) = n - (i : ℕ) + 1 := Nat.sub_add_comm (Nat.lt_succ_iff.mp i.isLt)
    rw [hi, pow_succ]
    congr 1
    ring

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma linear_form_smul_mem_homF_succ {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) (α β : R) :
    (fun u => (α * u 0 + β * u 1) • b u) ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + 1) := by
  have h := (_root_.GlobalTheory.KZ.PolAct.homF A (n + 1)).add_mem
    ((_root_.GlobalTheory.KZ.PolAct.homF A (n + 1)).smul_mem α
      (coord_zero_smul_mem_homF_succ hb))
    ((_root_.GlobalTheory.KZ.PolAct.homF A (n + 1)).smul_mem β
      (coord_one_smul_mem_homF_succ hb))
  convert h using 1
  funext u
  simp [add_smul, mul_smul]

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in
private lemma linear_form_pow_smul_mem_homF_add {A : Submodule R M} {n : ℕ}
    {b : (Fin 2 → R) → M} (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A n) (α β : R) :
    ∀ k : ℕ, (fun u => (α * u 0 + β * u 1) ^ k • b u) ∈
      _root_.GlobalTheory.KZ.PolAct.homF A (n + k) := by
  intro k
  induction k with
  | zero => simpa using hb
  | succ k ih =>
    have h := linear_form_smul_mem_homF_succ ih α β
    show _ ∈ _root_.GlobalTheory.KZ.PolAct.homF A (n + k + 1)
    convert h using 1
    funext u
    simp only [pow_succ', mul_smul]

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in

theorem _root_.GlobalTheory.KZ.PolAct.subst_mem {A : Submodule R M} {w : ℕ} (φ : M →ₗ[R] M)
    (hφ : ∀ a ∈ A, φ a ∈ A)
    (m : Matrix (Fin 2) (Fin 2) R) {b : (Fin 2 → R) → M}
    (hb : b ∈ _root_.GlobalTheory.KZ.PolAct.homF A w) :
    (fun u => φ (b (m *ᵥ u))) ∈ _root_.GlobalTheory.KZ.PolAct.homF A w := by
  obtain ⟨c, hc, hbu⟩ := hb
  have hterm : ∀ i : Fin (w + 1), (fun u : Fin 2 → R =>
      ((m 0 0 * u 0 + m 0 1 * u 1) ^ (i : ℕ) * (m 1 0 * u 0 + m 1 1 * u 1) ^ (w - (i : ℕ))) •
        φ (c i)) ∈ _root_.GlobalTheory.KZ.PolAct.homF A w := by
    intro i
    have h0 := const_mem_homF_zero (hφ _ (hc i))
    have h1 := linear_form_pow_smul_mem_homF_add h0 (m 1 0) (m 1 1) (w - i)
    have h2 := linear_form_pow_smul_mem_homF_add h1 (m 0 0) (m 0 1) i
    have hdeg : 0 + (w - (i : ℕ)) + i = w := by
      have := i.isLt
      omega
    rw [hdeg] at h2
    convert h2 using 1
    funext u
    simp only [mul_smul]
  have hsum := Submodule.sum_mem (_root_.GlobalTheory.KZ.PolAct.homF A w)
    (t := Finset.univ) (fun i _ => hterm i)
  convert hsum using 1
  funext u
  simp [hbu, map_sum, map_smul, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Finset.sum_apply]

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] in

theorem _root_.GlobalTheory.KZ.PolAct.act_mem_pol {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε) (l w : ℕ) [Fact l.Prime]
    (m : Matrix (Fin 2) (Fin 2) ℤ)
    (h : ∀ a ∈ X.A l, X.kmap l
      (X.sl (_root_.GlobalTheory.KZ.toGQ m)).toRingEquiv a ∈ X.A l) :
    ∀ b ∈ X.Pol l w,
      X.act l m b ∈
        X.Pol l w := by
  intro b hb
  exact _root_.GlobalTheory.KZ.PolAct.subst_mem (A := X.A l) (w := w) _ h _ hb

end GlobalTheory.KZ.PolAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiamondMatrixChosenDiamondMatrixGamma1Gamma0
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

private lemma exists_isDiam_of_coprime (N l d : ℕ) (hNl : Nat.Coprime N l) (hd : Nat.Coprime d N) :
    ∃ γ : SL(2, ℤ), IsDiam N l d γ := by
  obtain ⟨k, hkN, hkl⟩ := Nat.chineseRemainder hNl d 1
  have hk1 : Nat.Coprime k N := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hkN]
    exact hd
  have hk2 : Nat.Coprime k l := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hkl]
    simp
  have hk : Nat.Coprime k (N * l) := Nat.Coprime.mul_right hk1 hk2
  have hg : Int.gcd (k : ℤ) ((N * l : ℕ) : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hk
  have hb := Int.gcd_eq_gcd_ab (k : ℤ) ((N * l : ℕ) : ℤ)
  rw [hg] at hb
  have hdet : (!![Int.gcdA (k : ℤ) ((N * l : ℕ) : ℤ), -Int.gcdB (k : ℤ) ((N * l : ℕ) : ℤ);
      ((N * l : ℕ) : ℤ), (k : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    push_cast at hb ⊢
    linarith
  refine ⟨(⟨_, hdet⟩ : SL(2, ℤ)), Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    simp
  · refine CongruenceSubgroup.Gamma0_mem.2 ?_
    simp
  · simp only [en]
    simp
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hkN

theorem isDiam_sgD_of_prime : ∀ (N l d : ℕ), l.Prime → 0 < N → Nat.Coprime N l → Nat.Coprime d N →
    IsDiam N l d (sgD N l d) := by
  intro N l d _ _ hNl hd
  exact Classical.epsilon_spec (exists_isDiam_of_coprime N l d hNl hd)

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemMonicSquarefreeUnitConstPolysIffMonicSquarefrStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_monicSquarefreeUnitConstPolys_iff_monic_squarefree : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ) (f : (ZMod g)[X]), f ∈ sqSet g N ↔ f.Monic ∧ f.natDegree = N ∧ Squarefree f ∧ f.coeff 0 ≠ 0 := by
  first | exact @GlobalTheory.BadShare.mem_sqSet_iff | exact GlobalTheory.BadShare.mem_sqSet_iff | (intros; apply GlobalTheory.BadShare.mem_sqSet_iff <;> assumption)
end

