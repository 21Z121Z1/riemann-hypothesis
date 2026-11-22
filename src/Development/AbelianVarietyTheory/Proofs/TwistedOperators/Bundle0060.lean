import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0041
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZpowMulMemPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0055
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0056
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0042
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0057

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsQuotIntCosetFn
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.CosetQuotInt

open MeasureTheory ValuativeRel Matrix Topology in

theorem _root_.GlobalTheory.CosetQuotInt.isQuotInt_cosetFn (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k)
    [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ)
    (J : Subgroup (GL (n ⊕ Fin c) k)) (hJ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO J)
    (h : GL (n ⊕ Fin c) k)
    (m : Measure (GL n k)) (v : ℝ) (hv : v ≠ 0)
    (hvol : ∀ u₀ ∈ _root_.GlobalTheory.RootEx.N k n c 1, ∀ g₀ : GL n k, ∫ g,
      (∫ u : _root_.GlobalTheory.RootEx.N k n c 1,
      (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ))
        (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
          (u₀ * _root_.GlobalTheory.RootEx.embX c g₀))
          ∂(_root_.GlobalTheory.RootEx.volN ν n c 1)) ∂m
          = ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR c g₀ * v : ℝ) : ℂ))
    (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f : GL (n ⊕ Fin c) k → ℂ)
    (hf : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCosetFn J h f) :
    _root_.GlobalTheory.RootEx.IsQuotInt ν m μG 1 f ((((μG J).toReal / v : ℝ) : ℂ) * f h) := by
  classical
  haveI : BorelSpace (GL (n ⊕ Fin c) k) :=
    (_root_.GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν).1
  haveI : SecondCountableTopology (GL (n ⊕ Fin c) k) :=
    (_root_.GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν).2.2.1
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO at hJ
  obtain ⟨hJo, hJc⟩ := hJ
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCosetFn at hf
  obtain ⟨hleft, hright, hsupp⟩ := hf
  have hv' : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hv
  have hembP : ∀ g : GL n k,
      _root_.GlobalTheory.RootEx.embX c g ∈ _root_.GlobalTheory.RootEx.R k n c 1 := by
    intro g
    unfold _root_.GlobalTheory.RootEx.R
    exact Subgroup.mem_sup_left ⟨g, rfl⟩
  have hNP : ∀ u ∈ _root_.GlobalTheory.RootEx.N k n c 1,
      u ∈ _root_.GlobalTheory.RootEx.R k n c 1 := by
    intro u hu
    unfold _root_.GlobalTheory.RootEx.R
    exact Subgroup.mem_sup_right hu
  obtain ⟨F, hFdef⟩ : ∃ F : GL (n ⊕ Fin c) k → ℂ,
      ∀ x, F x = if h⁻¹ * x ∈ J then f h / (v : ℂ) else 0 := ⟨_, fun _ => rfl⟩
  unfold _root_.GlobalTheory.RootEx.IsQuotInt
  refine ⟨F, ?_, fun x => ?_, ?_⟩
  · have hSB := _root_.GlobalTheory.QuotInt.sb_of_quot J hJo hJc
      {(h : GL (n ⊕ Fin c) k ⧸ J)}
      (fun q => if q = (h : GL (n ⊕ Fin c) k ⧸ J) then f h / (v : ℂ) else 0)
      (fun q hq => by
        simp only [Finset.mem_singleton] at hq
        simp [hq])
    have hFq : F = fun y : GL (n ⊕ Fin c) k => (fun q : GL (n ⊕ Fin c) k ⧸ J =>
        if q = (h : GL (n ⊕ Fin c) k ⧸ J) then f h / (v : ℂ) else 0) (y : GL (n ⊕ Fin c) k ⧸ J) := by
      funext y
      rw [hFdef]
      dsimp only
      by_cases hy : h⁻¹ * y ∈ J
      · rw [if_pos hy, if_pos (QuotientGroup.eq.2 hy).symm]
      · rw [if_neg hy, if_neg (fun (he : (y : GL (n ⊕ Fin c) k ⧸ J) = h) =>
          hy (QuotientGroup.eq.1 he.symm))]
    rw [hFq]
    exact hSB
  · by_cases hx : DoubleCoset.mk (_root_.GlobalTheory.RootEx.R k n c 1) J h =
        DoubleCoset.mk (_root_.GlobalTheory.RootEx.R k n c 1) J x
    · obtain ⟨p, hp, j, hj, rfl⟩ := (DoubleCoset.eq _ _ _ _).1 hx
      obtain ⟨x₀, u', hu', rfl⟩ := _root_.GlobalTheory.RootEx.VolN.exists_of_mem_R hp
      obtain ⟨u₀, hu₀, hpeq⟩ : ∃ u₀ ∈ _root_.GlobalTheory.RootEx.N k n c 1,
          _root_.GlobalTheory.RootEx.embX c x₀ * u' = u₀ * _root_.GlobalTheory.RootEx.embX c x₀ :=
        ⟨_, _root_.GlobalTheory.RootEx.Radical.conj_mem x₀ hu', by group⟩
      rw [hpeq, hright _ j hj, hleft u₀ hu₀ x₀ h]
      have hpt : ∀ (g : GL n k) (u : _root_.GlobalTheory.RootEx.N k n c 1),
          F (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
            (u₀ * _root_.GlobalTheory.RootEx.embX c x₀ * h * j)) =
          f h / (v : ℂ) * (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator
            (fun _ => (1 : ℂ)) (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀)) := by
        intro g u
        have hyP : _root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
            (u₀ * _root_.GlobalTheory.RootEx.embX c x₀) ∈ _root_.GlobalTheory.RootEx.R k n c 1 :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (hembP g) (hNP _ u.2))
            (Subgroup.mul_mem _ (hNP _ hu₀) (hembP x₀))
        have hiff : h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀ * h * j)) ∈ J ↔
            h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀)) * h ∈ J := by
          have heq : h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀ * h * j)) =
              h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
              (u₀ * _root_.GlobalTheory.RootEx.embX c x₀)) * h * j := by group
          rw [heq, J.mul_mem_cancel_right hj]
        rw [hFdef]
        by_cases hin : h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) *
            (u₀ * _root_.GlobalTheory.RootEx.embX c x₀)) * h ∈ J
        · rw [if_pos (hiff.2 hin), Set.indicator_of_mem
            (show _ ∈ _root_.GlobalTheory.StepData.Cgrp J h from
              _root_.GlobalTheory.StepData.mem_Cgrp.2 ⟨hyP, hin⟩), mul_one]
        · rw [if_neg (fun h' => hin (hiff.1 h')), Set.indicator_of_notMem
            (show _ ∉ _root_.GlobalTheory.StepData.Cgrp J h from
              fun h' => hin (_root_.GlobalTheory.StepData.mem_Cgrp.1 h').2), mul_zero]
      simp_rw [hpt, integral_const_mul]
      rw [hvol u₀ hu₀ x₀]
      unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR
      rw [Complex.ofReal_mul, div_mul_eq_mul_div, eq_div_iff hv']
      ring
    · have hfx : f x = 0 := hsupp x (fun he => hx he.symm)
      rw [hfx]
      have hpt : ∀ (g : GL n k) (u : _root_.GlobalTheory.RootEx.N k n c 1),
          F (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) * x) = 0 := by
        intro g u
        rw [hFdef, if_neg]
        intro hmem
        apply hx
        refine (DoubleCoset.eq _ _ _ _).2 ⟨(_root_.GlobalTheory.RootEx.embX c g *
          (u : GL (n ⊕ Fin c) k))⁻¹, Subgroup.inv_mem _ (Subgroup.mul_mem _ (hembP g)
            (hNP _ u.2)), h⁻¹ * (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) * x),
          hmem, by group⟩
      simp_rw [hpt, integral_zero]
  · have hFind : F = ((fun y => h⁻¹ * y) ⁻¹' (J : Set (GL (n ⊕ Fin c) k))).indicator
        (fun _ => f h / (v : ℂ)) := by
      funext y
      rw [hFdef]
      by_cases hy : h⁻¹ * y ∈ J
      · rw [if_pos hy, Set.indicator_of_mem (show y ∈ (fun y => h⁻¹ * y) ⁻¹' (J : Set _) from hy)]
      · rw [if_neg hy,
          Set.indicator_of_notMem (show y ∉ (fun y => h⁻¹ * y) ⁻¹' (J : Set _) from hy)]
    rw [hFind, integral_indicator_const _
      (hJo.measurableSet.preimage (measurable_const_mul h⁻¹)), measureReal_def,
      measure_preimage_mul, Complex.real_smul]
    push_cast
    ring

end GlobalTheory.CosetQuotInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeBounds
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.LatClass

variable {k : Type} [Field k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

omit [Fintype n] [DecidableEq n] [DecidableEq n'] in
theorem aff_low (x₀ : Matrix n n' k) (y) (w : n' → k) (s : k) :
    affPt (c := c + 1) 1 x₀ y *ᵥ Sum.elim w (Pi.single 0 s) = Sum.elim (x₀ *ᵥ w) (Pi.single 0 s) := by
  ext (r | l)
  · simp [mulVec, dotProduct, Fintype.sum_sum_type, affPt, basePt, Free, Pi.single_apply]
  · simp [mulVec, dotProduct, Fintype.sum_sum_type, affPt, basePt, Free, Pi.single_apply]

omit [Fintype n] [DecidableEq n] [DecidableEq n'] in
theorem aff_row (x₀ : Matrix n n' k) (y) (w : n' → k) (i : Fin (c + 1)) (s : k) (l : Fin c) :
    (affPt (c := c) 1 x₀ y *ᵥ Sum.elim w (Pi.single i s)) (.inr l) = affPt 1 x₀ y (.inr l) (.inr i) * s := by
  have : ∀ r, affPt (c := c) 1 x₀ y (.inr l) (.inl r) = 0 := fun r => by simp [affPt, basePt, Free]
  simp [mulVec, dotProduct, Fintype.sum_sum_type, this, Pi.single_apply]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem aff_diag (x₀ : Matrix n n' k) (y) (i l : Fin c) (h : i ≤ l) :
    affPt (c := c) 1 x₀ y (.inr l) (.inr i.castSucc) = if l = i then 1 else 0 := by
  have : ¬ l < i := not_lt.2 h
  simp [affPt, basePt, Free, this, Fin.ext_iff]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  {ϖ : kˣ} {ψ : AddChar k Circle} {ν : Measure k}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k] [DecidableEq n]
  [DecidableEq n'] in
theorem exists_supp {p : ℕ} {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {x₀ : Matrix n n' k}
    (h : opE ψ ν p Ψ x₀ ≠ 0) : ∃ y, Ψ (affPt p x₀ y) ≠ 0 := by
  by_contra H
  push Not at H
  exact h (by simp [opE, H])

theorem bounds (hϖ : valuation k (ϖ : k) = uniformizer k) (hψ : HasConductor ψ 1) [ν.IsAddHaarMeasure]
    {g' : GL n' k} {e' : Fin (c + 1 + 1) → ℤ} {z' : n' → k} {h : GL (n ⊕ Fin (c + 1)) k}
    {Ψ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ}
    (hs : ∀ x, Ψ x ≠ 0 → MapsLat x (latOf (nfBasis ϖ g' e' z')) (latOf h))
    (hp : ∀ x y, MapsLat y (latOf (nfBasis ϖ g' e' z')) (latOf h) → Ψ (x + (ϖ : k) • y) = Ψ x)
    {x₀ : Matrix n n' k} (h0 : opE ψ ν 1 Ψ x₀ ≠ 0) (i : Fin (c + 1)) {a : ℤ}
    (ha : topCoord (latOf h) i = powInt ϖ a) : e' i.succ - 1 ≤ a ∧ a ≤ e' i.castSucc := by
  constructor
  · obtain ⟨v, hv, hv0, hvi⟩ : (ϖ : k) ^ a ∈ topCoord (latOf h) i := ha ▸ (zpow_mem_pow hϖ).2 le_rfl
    have key : -((ϖ : k) * ((ϖ : k) ^ (-e' i.succ) * (ϖ : k) ^ a)) ∈ 𝒪[k] := by
      refine Unram.mem_of_psi hψ fun t ht => ?_
      let y : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k :=
        Matrix.of fun r s => if s = .inr i.succ then t * (ϖ : k) ^ (-e' i.succ) * v r else 0
      have hy : MapsLat y (latOf (nfBasis ϖ g' e' z')) (latOf h) := fun w hw => by
        have : y *ᵥ w = (t * ((ϖ : k) ^ (-e' i.succ) * w (.inr i.succ))) • v := by
          ext r; simp [y, mulVec, dotProduct]; ring
        rw [this]
        refine smul_mem_lat (mul_mem ht ?_) hv
        rw [← mem_pow_zero (ϖ := ϖ), zpow_mul_mem_pow]
        simpa using (mem_nf.1 hw).2 i.succ
      have := Unram.psi_ch_eq_one ψ ν Ψ x₀ h0 ((ϖ : k) • y) (fun r s hf => ?_) fun x => hp x y hy
      · convert this using 2
        simp [ch, y, hvi]; ring
      · simp only [y, Matrix.smul_apply, Matrix.of_apply]
        split_ifs with e
        · subst e
          rcases r with r | r
          · simp [Free] at hf
          · rw [hv0 r (by simp only [Free, Fin.val_succ] at hf; rw [Fin.lt_def]; omega)]; simp
        · simp
    rw [neg_mem_iff, ← mem_pow_zero (ϖ := ϖ), ← zpow_add₀ ϖ.ne_zero, ← zpow_one_add₀ ϖ.ne_zero,
      zpow_mem_pow hϖ] at key
    omega
  · obtain ⟨y, hy⟩ := exists_supp h0
    have := hs _ hy _ (col_mem_nf i.castSucc ((zpow_mem_pow hϖ).2 le_rfl))
    rw [← zpow_mem_pow hϖ, ← ha]
    refine ⟨_, this, fun l hl => ?_, ?_⟩
    · rw [aff_row, aff_diag _ _ _ _ hl.le, if_neg hl.ne', zero_mul]
    · rw [aff_row, aff_diag _ _ _ _ le_rfl, if_pos rfl, one_mul]

omit [BorelSpace k] in
theorem first_mem (hϖ : valuation k (ϖ : k) = uniformizer k)
    {g' : GL n' k} {e' : Fin (c + 1 + 1) → ℤ} {z' : n' → k} {h : GL (n ⊕ Fin (c + 1)) k}
    {Ψ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ}
    (hs : ∀ x, Ψ x ≠ 0 → MapsLat x (latOf (nfBasis ϖ g' e' z')) (latOf h))
    {x₀ : Matrix n n' k} (h0 : opE ψ ν 1 Ψ x₀ ≠ 0) :
    ((ϖ ^ e' 0 : kˣ) : k) • (Sum.elim (x₀ *ᵥ z') (Pi.single 0 1) : n ⊕ Fin (c + 1) → k) ∈ latOf h ∧
      ∀ w ∈ latOf g', (Sum.elim (x₀ *ᵥ w) 0 : n ⊕ Fin (c + 1) → k) ∈ latOf h := by
  obtain ⟨y, hy⟩ := exists_supp h0
  constructor
  · have := hs _ hy _ (col_mem_nf 0 ((zpow_mem_pow hϖ).2 le_rfl))
    rw [aff_low] at this
    convert this using 1
    ext (r | l)
    · simp [mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
    · simp [Pi.single_apply]
  · intro w hw
    have := hs _ hy (Sum.elim w (Pi.single 0 0)) (mem_nf.2 ⟨by simpa using hw, fun i => by simpa using zero_mem_pow⟩)
    rw [aff_low] at this
    simpa using this

theorem step_normal (H : NormalFormModN k) (hϖ : valuation k (ϖ : k) = uniformizer k) (hψ : HasConductor ψ 1)
    [ν.IsAddHaarMeasure] {j : ℕ} {e' : Fin (c + 1 + 1) → ℤ} {z' : n' → k}
    (he' : ∀ i, -(j : ℤ) ≤ e' i ∧ e' i ≤ 0) (hz' : ∀ i, z' i ∈ 𝒪[k]) {h : GL (n ⊕ Fin (c + 1)) k}
    {Ψ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ}
    (hs : ∀ x, Ψ x ≠ 0 → MapsLat x (latOf (nfBasis ϖ 1 e' z')) (latOf h))
    (hp : ∀ x y, MapsLat y (latOf (nfBasis ϖ 1 e' z')) (latOf h) → Ψ (x + (ϖ : k) • y) = Ψ x)
    {x₀ : Matrix n n' k} (h0 : opE ψ ν 1 Ψ x₀ ≠ 0) :
    ∃ r ∈ R k n (c + 1) 1, ∃ (e : Fin (c + 1) → ℤ) (z : n → k),
      (∀ i, -((j + 1 : ℕ) : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (∀ i, z i ∈ 𝒪[k]) ∧
        latOf (r * h) = latOf (normalBasis ϖ e z) := by
  obtain ⟨u, hu, g, e, z, hl, hm⟩ := H ϖ hϖ n (c + 1) h
  have ht : ∀ i, topCoord (latOf h) i = powInt ϖ (e i) := fun i => by
    rw [← topCoord_R (Subgroup.mem_sup_right hu) h i, hl, topCoord_nf]
  refine ⟨embX _ g⁻¹ * u, mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right hu), e,
    (g⁻¹).val *ᵥ z, fun i => ?_, ?_, ?_⟩
  · have := bounds hϖ hψ hs hp h0 i (ht i)
    have := he' i.succ
    have := he' i.castSucc
    push_cast
    omega
  · obtain ⟨h1, h2⟩ := first_mem hϖ hs h0
    have h3 := (hm _).1 (h2 z' (mem_latOf_one.2 hz'))
    rw [← mulVec_mem_latOf u, N_fix hu _ (fun l hl => by simp [Fin.ext_iff, hl.ne']), hl] at h1
    have h4 := smul_mem_lat (t := (ϖ : k) ^ (-e' 0))
      (mem_pow_zero.1 ((zpow_mem_pow hϖ).2 (by have := he' 0; omega))) (mem_nf.1 h1).1
    have h5 := sub_mem h3 h4
    change z ∈ latOf g
    convert h5 using 1
    have : (ϖ : k) ^ e' 0 ≠ 0 := zpow_ne_zero _ ϖ.ne_zero
    ext r
    simp
    field_simp
    ring
  · rw [mul_assoc, latOf_mul_congr _ hl, embX_mul_nf, inv_mul_cancel, nfBasis_one]

end GlobalTheory.LatClass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairwiseDisjointParahoricTorusDoubleCosetAntitonStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairwise_disjoint_parahoricTorusDoubleCoset_antitone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k → ∀ (r l t : ℕ),
    Pairwise (Function.onFun Disjoint fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
      (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k))) := by
  first | exact @GlobalTheory.CellDisjoint.dcell_pairwise_disjoint | exact GlobalTheory.CellDisjoint.dcell_pairwise_disjoint | (intros; apply GlobalTheory.CellDisjoint.dcell_pairwise_disjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicHaarVolumeConjIntersectionEqMulStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicHaarVolume_conjIntersection_eq_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k), IsOpen (prX (Cgrp J h) : Set (GL n k)) → ∀ m : Measure (GL n k), volR ν m (Cgrp J h) = volN ν n c 1 ((Cgrp J h).subgroupOf (N k n c 1)) * m (prX (Cgrp J h)) := by
  first | exact @GlobalTheory.CosetVolProd.volR_Cgrp | exact GlobalTheory.CosetVolProd.volR_Cgrp | (intros; apply GlobalTheory.CosetVolProd.volR_Cgrp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricDatumEigenvectorTwoBlockParahoricStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricDatum_eigenvector_twoBlockParahoric : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (ξ μ₀ : kˣ →* ℂˣ), IsTame ξ → IsUnram μ₀ →
    ∀ j ∈ parahoric k A D, ∀ d : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
    om (μ₀ * ξ) j (1 : GL (A ⊕ E) k) (datum ξ : Matrix (A ⊕ E) (A ⊕ D) k → ℂ) = fun x => (ξ d : ℂ) * datum ξ x := by
  first | exact @GlobalTheory.DatumEigen.om_datum | exact GlobalTheory.DatumEigen.om_datum | (intros; apply GlobalTheory.DatumEigen.om_datum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricDatumTorusIntegrandEqIndicatorStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricDatum_torus_integrand_eq_indicator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
    ∀ (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (ξ : kˣ →* ℂˣ), IsUnitaryChar ξ → ∀ (e : D → ℤ) (x : Matrix (A ⊕ E) (A ⊕ D) k),
    datum ξ (x * (mtor ϖ e : GL (A ⊕ D) k).val) * starRingEnd ℂ (datum ξ x) =
      Set.indicator {y : Matrix (A ⊕ E) (A ⊕ D) k | InSupp (y * (mtor ϖ (fun i => -max 0 (-e i)) : GL (A ⊕ D) k).val)}
        (fun _ => (1 : ℂ)) x := by
  first | exact @GlobalTheory.TorusIntegrand.integrand | exact GlobalTheory.TorusIntegrand.integrand | (intros; apply GlobalTheory.TorusIntegrand.integrand <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalSeriesSubquotientOfCharactersStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_series_subquotient_of_characters : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (χ : Fin N → kˣ →* ℂˣ), IsSubquotient (prinSeries χ) (multiProd (Equiv.sigmaUnique (Fin N) fun _ => Fin 1) fun i => detRep (Fin 1) (χ i)) := by
  first | exact @GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd | exact GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd | (intros; apply GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProperTriple
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx.ProperTriple

open MeasureTheory ValuativeRel Matrix in
private lemma unipotent_block_entries_eq_one_zero {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    {c ρ : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ _root_.GlobalTheory.RootEx.N k n c (ρ + 1)) :
    (∀ t t' : n, (u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl t) (Sum.inl t') =
      (1 : Matrix n n k) t t') ∧
    (∀ (t : n) (i : Fin c), (i : ℕ) + 1 = ρ + 1 →
      (u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl t) (Sum.inr i) = 0) ∧
    (∀ (t : n) (i : Fin c), (i : ℕ) + 1 = ρ + 1 →
      (u : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inl t) = 0) := by
  have h := _root_.GlobalTheory.RootEx.Model.mem_N_iff.1 hu
  unfold _root_.GlobalTheory.RootEx.InN _root_.GlobalTheory.RootEx.lev at h
  refine ⟨fun t t' => ?_, fun t i hi => ?_, fun t i hi => ?_⟩
  · rw [h _ _ (by simp)]
    simp [Matrix.one_apply]
  · rw [h _ _ (by simp [hi])]
    simp
  · rw [h _ _ (by simp [hi])]
    simp

open MeasureTheory ValuativeRel Matrix in
private lemma recover_colE_vec_from_embX_product {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    {c ρ : ℕ} (hρc : ρ < c) (x : GL n k) (u : _root_.GlobalTheory.RootEx.N k n c (ρ + 1))
    (β : n → k) (r : n) :
    ∑ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
        _root_.GlobalTheory.RootEx.colE c (ρ + 1) β)⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl r) (Sum.inl s) *
      (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
        _root_.GlobalTheory.RootEx.colE c (ρ + 1) β) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩) = β r := by
  obtain ⟨hll, hlr, -⟩ := unipotent_block_entries_eq_one_zero u.2
  obtain ⟨hll', -, hrl'⟩ := unipotent_block_entries_eq_one_zero (inv_mem u.2)
  have h1 : ∀ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
      _root_.GlobalTheory.RootEx.colE c (ρ + 1) β) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩) = ((x : Matrix n n k) *ᵥ β) s := by
    intro s
    rw [Units.val_mul, Units.val_mul, _root_.GlobalTheory.RootEx.Radical.embX_val,
      _root_.GlobalTheory.RootEx.ExchangeSupport.colE_val]
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hll, hlr, _root_.GlobalTheory.RootEx.ExchangeSupport.colM,
      Matrix.mulVec, dotProduct, Matrix.one_apply]
  have h2 : ∀ s, (↑(_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k) *
      _root_.GlobalTheory.RootEx.colE c (ρ + 1) β)⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
        (Sum.inl r) (Sum.inl s) = (↑x⁻¹ : Matrix n n k) r s := by
    intro s
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← map_inv,
      _root_.GlobalTheory.RootEx.Radical.embX_val, _root_.GlobalTheory.RootEx.ExchangeSupport.colE_inv_val]
    simp only [Matrix.coe_units_inv] at hll' hrl' ⊢
    have hz : ∀ i : Fin c, (i : ℕ) = ρ →
        ∑ a, ((u : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)⁻¹ (Sum.inr i) (Sum.inl a) *
          (↑x : Matrix n n k)⁻¹ a s = 0 :=
      fun i hi => Finset.sum_eq_zero fun a _ => by rw [hrl' a i (by omega), zero_mul]
    simp +contextual [Matrix.mul_apply, Fintype.sum_sum_type, hll', _root_.GlobalTheory.RootEx.ExchangeSupport.colM,
      Matrix.one_apply, hz]
  simp_rw [h1, h2]
  change ((↑x⁻¹ : Matrix n n k) *ᵥ ((x : Matrix n n k) *ᵥ β)) r = β r
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

open MeasureTheory ValuativeRel Matrix in

theorem _root_.GlobalTheory.RootEx.ProperTriple.proper_triple : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ)
    (_ : ρ < c) (C : Set (GL (n ⊕ Fin c) k)) (_ : IsCompact C),
    ∃ D : Set (GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1) × (n → k)), IsCompact D ∧
      ∀ z : GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1) × (n → k),
        _root_.GlobalTheory.RootEx.embX c z.1 * (z.2.1 : GL (n ⊕ Fin c) k) *
          _root_.GlobalTheory.RootEx.colE c (ρ + 1) z.2.2 ∈ C → z ∈ D := by
  intro k _ _ _ _ n _ _ c ρ _ hρc C hC
  let F : GL (n ⊕ Fin c) k → (n → k) := fun g r =>
    ∑ s, (↑g⁻¹ : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl r) (Sum.inl s) *
      (g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl s) (Sum.inr ⟨ρ, hρc⟩)
  have hF : Continuous F := by
    refine continuous_pi fun r => continuous_finset_sum _ fun s _ => ?_
    exact (Units.continuous_coe_inv.matrix_elem _ _).mul (Units.continuous_val.matrix_elem _ _)
  have hK : IsCompact (F '' C) := hC.image hF
  have hC' : IsCompact ((fun q : GL (n ⊕ Fin c) k × (n → k) =>
      q.1 * (_root_.GlobalTheory.RootEx.colE c (ρ + 1) q.2)⁻¹) '' (C ×ˢ (F '' C))) :=
    (hC.prod hK).image (continuous_fst.mul
      (_root_.GlobalTheory.RootEx.ExchangeSupport.continuous_colE.comp continuous_snd).inv)
  obtain ⟨D₀, hD₀, hD₀C⟩ := _root_.GlobalTheory.QuotInt.compact_preimage
    (_root_.GlobalTheory.RootEx.VolN.isClosed_N (k := k) (n := n) (c := c) (ρ + 1)) hC'
  refine ⟨(fun q : (GL n k × _root_.GlobalTheory.RootEx.N k n c (ρ + 1)) × (n → k) =>
    (q.1.1, q.1.2, q.2)) '' (D₀ ×ˢ (F '' C)), (hD₀.prod hK).image (by fun_prop), ?_⟩
  intro z hz
  have hβ : z.2.2 ∈ F '' C := ⟨_, hz, funext (recover_colE_vec_from_embX_product hρc z.1 z.2.1 z.2.2)⟩
  have hz' : (z.1, z.2.1) ∈ D₀ := hD₀C _ ⟨(_, z.2.2), ⟨hz, hβ⟩, by simp⟩
  exact ⟨((z.1, z.2.1), z.2.2), ⟨hz', hβ⟩, rfl⟩

end GlobalTheory.RootEx.ProperTriple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexConjUniformizerPowerDiagonalGLReindexStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_conj_uniformizerPowerDiagonalGL_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ)
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (σ : n ≃ n') (e : n → ℤ),
    ((KO k n').map (MulAut.conj (torusElt k n' ϖ (e ∘ σ.symm))).toMonoidHom).relIndex (KO k n') =
      ((KO k n).map (MulAut.conj (torusElt k n ϖ e)).toMonoidHom).relIndex (KO k n) := by
  first | exact @GlobalTheory.ReindexTorus.relIndex_conj_torusElt_reindex | exact GlobalTheory.ReindexTorus.relIndex_conj_torusElt_reindex | (intros; apply GlobalTheory.ReindexTorus.relIndex_conj_torusElt_reindex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMulMatrixVolumeOpenSubgroupIntegralGLStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_mul_matrixVolume_open_subgroup_integralGL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (n : Type) [Fintype n] [DecidableEq n] (H L : Subgroup (GL n k)),
    H ≤ L → L ≤ KO k n → IsOpen (H : Set (GL n k)) →
    0 < (volM ν n n (Units.val '' (H : Set (GL n k)))).toReal ∧
    (H.relIndex L : ℝ) * (volM ν n n (Units.val '' (H : Set (GL n k)))).toReal =
      (volM ν n n (Units.val '' (L : Set (GL n k)))).toReal := by
  first | exact @GlobalTheory.IndexVolume.relIndex_mul_volM | exact GlobalTheory.IndexVolume.relIndex_mul_volM | (intros; apply GlobalTheory.IndexVolume.relIndex_mul_volM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentExistsResidueCardPowMemNhdsStatement
section
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootExchangeUnipotent_exists_residueCardPow_mem_nhds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), (resCard k).Prime → ∀ u ∈ N k n c p, ∀ U ∈ 𝓝 (1 : GL (n ⊕ Fin c) k), ∃ m : ℕ, u ^ (resCard k ^ m) ∈ U := by
  first | exact @GlobalTheory.RootEx.UnipPow.exists_pow_mem_nhds | exact GlobalTheory.RootEx.UnipPow.exists_pow_mem_nhds | (intros; apply GlobalTheory.RootEx.UnipPow.exists_pow_mem_nhds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwoBlockParahoricLowerBlockDetTameCharacterStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoBlockParahoric_lowerBlock_det_tameCharacter : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ), IsTame ξ →
  ∀ j ∈ parahoric k A D, (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det ≠ 0 ∧
    ∀ d d' : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
      (d' : k) = ((j⁻¹ : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det → (ξ d : ℂ) * ξ d' = 1 := by
  first | exact @GlobalTheory.ParahoricLowerBlock.lower_block_tame | exact GlobalTheory.ParahoricLowerBlock.lower_block_tame | (intros; apply GlobalTheory.ParahoricLowerBlock.lower_block_tame <;> assumption)
end

