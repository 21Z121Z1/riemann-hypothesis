import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL4.Bundle0014
import Formalism.LocalToGlobal.GlobalTheory.GL4.Bundle0004
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0006

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.PColSlopeEq
section
open Module NumberField

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions.flipTwoThree

def TSpanEqVV : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), TSpan K lam = VV K lam

def ZBasisStd : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), ∃ (Z : ZBasis lam) (μs : ι → ℝ), Nonempty Z.J0 ∧
    (∀ τ, MuStd (lam τ).natW (μs τ)) ∧ -Real.log (gramZ lam Z).det / (Fintype.card Z.J0 : ℝ) = ∑ τ, μs τ

def QSlope (D : D7) : Prop :=
  ∀ u (CV : ColVal D u) c τ, (CV.Q c τ).mu = -Real.log (Tu D u) / D.R.k

theorem wsum_eq_colAbs (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : ((wsum ((D.fm u).lam 0 τ) : ℤ) : ℝ) = colAbs D u τ := by
  have hk : D.R.N 0 = D.R.k := by simp only [Ranks.N]; omega
  rw [colAbs, wsum, Int.cast_sum]
  simp_rw [Formalism.MainNotions.flipTwoThree.weight_eq_lamCol]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((lamCol D u τ i : ℚ) : ℝ)) (D.R.N 0), hk]

theorem colSlopeEq_of (h1 : TSpanEqVV) (h2 : ZBasisStd) (D : D7) (h3 : QSlope D) : ColSlopeEq D := by
  intro u CV
  obtain ⟨Z, μs, hne, hμ, hdet⟩ := h2 D.what₂.Tau (D.R.N 0) ((D.fm u).lam 0)
  refine ⟨μs, hμ, ?_⟩
  haveI : Nonempty Z.J0 := hne
  haveI := CV.ne
  have hm := col_mu CV (h1 D.what₂.LL D.what₂.Tau (D.R.N 0) ((D.fm u).lam 0)) Z
  have key : ∑ c, ∑ τ, ((wsum ((D.fm u).lam 0 τ) * (Fintype.card Z.J0 : ℤ) : ℤ) : ℝ) * (CV.Q c τ).mu =
      ∑ _c : (D.mem u).C.cls 0, ∑ τ, colAbs D u τ * (Fintype.card Z.J0 : ℝ) *
        (-Real.log (Tu D u) / D.R.k) := by
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun τ _ => ?_
    rw [h3 u CV c τ, ← wsum_eq_colAbs]
    push_cast
    ring
  have e2 : ∑ τ, colAbs D u τ * (Fintype.card Z.J0 : ℝ) * (-Real.log (Tu D u) / D.R.k) =
      -((Fintype.card Z.J0 : ℝ) * ∑ τ, colAbs D u τ / D.R.k * Real.log (Tu D u)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  rw [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, e2] at hm
  have hN : (0 : ℝ) < Fintype.card Z.J0 := by exact_mod_cast Fintype.card_pos
  have hC : (0 : ℝ) < Fintype.card ((D.mem u).C.cls 0) := by exact_mod_cast Fintype.card_pos
  rw [← hdet]
  apply mul_left_cancel₀ (mul_ne_zero hN.ne' hC.ne')
  have hN' : (Fintype.card Z.J0 : ℝ) ≠ 0 := hN.ne'
  have e3 : (Fintype.card Z.J0 : ℝ) * Fintype.card ((D.mem u).C.cls 0) *
      (-Real.log (gramZ ((D.fm u).lam 0) Z).det / Fintype.card Z.J0) =
      -(Fintype.card ((D.mem u).C.cls 0) * Real.log (gramZ ((D.fm u).lam 0) Z).det) := by
    field_simp
  rw [hm, mul_add, e3]
  ring

theorem Link5F_of_three (h1 : TSpanEqVV) (h2 : ZBasisStd) (h3 : ∀ D, QSlope D) : Link5F := by
  unfold Link5F
  intro eps Fm _ _ _
  exact Formalism.MainNotions.flipTwoThree.familySlopeLower_of_open Fm
    ⟨0, fun x _ _ i => Formalism.MainNotions.flipTwoThree.lower_slope_of_column_slope _ (colSlopeEq_of h1 h2 _ (h3 _))⟩

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.PShortSpan
section
noncomputable section

open NumberField

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

section ShortSpan

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def ShortSpan (S : HSpace E) (q : ℕ) (ρ : ℝ) : Prop :=
  ∀ L : Submodule (𝓞 E) S.V, Submodule.IsLattice E L → LatT S q L →
    Submodule.span E {x | x ∈ L ∧ meanAbs (S.hT x x) ≤ ρ} = ⊤

theorem shortFrame_of_span (S : HSpace E) (q : ℕ) (ρ : ℝ) (h : ShortSpan S q ρ) : ShortFrame S q ρ := by
  intro L hL hq
  set s : Set S.V := {x | x ∈ L ∧ meanAbs (S.hT x x) ≤ ρ} with hs
  obtain ⟨t, hts, htsp, hti⟩ := exists_linearIndependent E s
  have htop : ⊤ ≤ Submodule.span E (Set.range ((↑) : t → S.V)) := by
    rw [Subtype.range_coe, htsp, hs, h L hL hq]
  let B : Module.Basis t E S.V := Module.Basis.mk hti htop
  let b : Module.Basis (Fin S.rank) E S.V := B.reindex (B.indexEquiv S.frame)
  have hb : ∀ c, b c ∈ s := fun c ↦ by
    simp only [b, Module.Basis.reindex_apply, B, Module.Basis.mk_apply]
    exact hts (Subtype.prop _)
  exact ⟨b, fun c ↦ (hb c).1, fun c ↦ (hb c).2⟩

end ShortSpan

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

