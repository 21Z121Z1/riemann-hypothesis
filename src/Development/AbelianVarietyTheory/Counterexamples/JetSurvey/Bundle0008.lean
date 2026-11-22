import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcWitnessExistence.DataXOfModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0049
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0018

-- bundled from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.LatticeAndConstantUnique
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.ModelLatticeCheck

def Fits {D : D7} (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (k : (T.U j σ).Comp) (Xx : DataX D.host.E D.R.r) : Prop :=
  Xx.toData = (T.U j σ).X k ∧ Xx.g = T.Q.l.M ∧
    Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u}

theorem comp_nonempty {D : D7} (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) : Nonempty (T.U j σ).Comp :=
  ⟨(T.dict j σ 1).1⟩

theorem le_of_span_le {E : Type} [Field E] [NumberField E] {r : ℕ}
    (A : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hA : A ≠ 0) (L₁ L₂ : Submodule (𝓞 E) (Fin r → E))
    (h : Submodule.span (𝓞 E) {v | ∃ a ∈ A, ∃ u ∈ L₁, v = a • u} ≤
      Submodule.span (𝓞 E) {v | ∃ a ∈ A, ∃ u ∈ L₂, v = a • u}) : L₁ ≤ L₂ := by
  intro u hu
  have key : ∀ b ∈ A⁻¹, ∀ x ∈ Submodule.span (𝓞 E) {v | ∃ a ∈ A, ∃ u ∈ L₂, v = a • u}, b • x ∈ L₂ := by
    intro b hb x hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, w, hw, rfl⟩ := hv
      have : b * a ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
        rw [← inv_mul_cancel₀ hA]; exact FractionalIdeal.mul_mem_mul hb ha
      obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).1 this
      rw [smul_smul, ← hz, algebraMap_smul]
      exact L₂.smul_mem z hw
    | zero => simp
    | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
    | smul c v _ hv => rw [smul_comm]; exact L₂.smul_mem c hv
  have h1 : (1 : E) ∈ A⁻¹ * A := by
    rw [inv_mul_cancel₀ hA]; exact FractionalIdeal.one_mem_one _
  have : ∀ c ∈ A⁻¹ * A, c • u ∈ L₂ := by
    intro c hc
    refine FractionalIdeal.mul_induction_on hc (C := fun c => c • u ∈ L₂) ?_ ?_
    · intro b hb a ha
      rw [mul_smul]
      exact key b hb _ (h (Submodule.subset_span ⟨a, ha, u, hu, rfl⟩))
    · intro x y hx hy
      rw [add_smul]; exact add_mem hx hy
  simpa using this 1 h1

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  intro h
  have h1 := GlobalTheory.LatticeData.absNorm_ccK_mem D
  rw [h, FractionalIdeal.mem_zero_iff] at h1
  exact D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))

theorem lattice_and_constant_unique {D : D7} (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (k : (T.U j σ).Comp)
    (X Y : DataX D.host.E D.R.r) (hX : Fits T j σ k X) (hY : Fits T j σ k Y) : X.L' = Y.L' ∧ X.k0 = Y.k0 := by
  have e : X.toData = Y.toData := hX.1.trans hY.1.symm
  have eΛ : X.Λ = Y.Λ := congrArg Data.Λ e
  refine ⟨le_antisymm (le_of_span_le _ (AA_ne_zero D) _ _ ?_) (le_of_span_le _ (AA_ne_zero D) _ _ ?_), ?_⟩
  · rw [← hX.2.2, ← hY.2.2, eΛ]
  · rw [← hX.2.2, ← hY.2.2, eΛ]
  · obtain ⟨τ⟩ : Nonempty X.Ψ := by
      obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
      by_cases e : τ ∈ X.Ψ
      · exact ⟨⟨τ, e⟩⟩
      · exact ⟨⟨_, not_not.1 (fun e' => e ((X.cmType τ).2 e'))⟩⟩
    have h1 := X.ξ0_abs τ
    have h2 := Y.ξ0_abs ⟨τ.1, (congrArg Data.Ψ e : X.Ψ = Y.Ψ) ▸ τ.2⟩
    rw [show X.ξ0 = Y.ξ0 from congrArg Data.ξ0 e] at h1
    simp only at h2
    linarith

theorem indices_unbounded {D : D7} (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (k : (T.U j σ).Comp)
    (X : DataX D.host.E D.R.r) (hX : Fits T j σ k X) (B : ℕ) :
    ∃ Y : DataX D.host.E D.R.r, Fits T j σ k Y ∧ B < Y.NA ∧ B < Y.NC := by
  refine ⟨{ X with
    NA := (B + 1) * X.NA
    NC := (B + 1) * X.NC
    NA_pos := Nat.mul_pos (by omega) X.NA_pos
    NC_pos := Nat.mul_pos (by omega) X.NC_pos
    NA_sub := fun x hx => ?_
    NC_sub := fun x hx => ?_ }, hX, ?_, ?_⟩
  · rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem (X.NA_sub x hx) _
  · rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem (X.NC_sub x hx) _
  · have := X.NA_pos
    show B < (B + 1) * X.NA
    nlinarith
  · have := X.NC_pos
    show B < (B + 1) * X.NC
    nlinarith

theorem holds_by_value (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (k : (T.U j σ).Comp) :
    ∃ X : DataX D.host.E D.R.r, Fits T j σ k X ∧ X.k0 = 2 * xiR D ∧ X.NA = Ideal.absNorm D.host.𝔟 ∧
      X.NC = Ideal.absNorm D.host.ccK := by
  obtain ⟨Xx, h1, h2, h3, h4, -⟩ :=
    GlobalTheory.LatticeData.exists_dataX_of_hasPrinc D T h j hj σ hσ (GlobalTheory.PrincCore.hasPrinc_core D T h j hj σ hσ) k
  refine ⟨{ Xx with
    NA := Ideal.absNorm D.host.𝔟
    NC := Ideal.absNorm D.host.ccK
    NA_pos := Nat.pos_of_ne_zero fun e => GlobalTheory.LatticeData.halfDifferent_ne_bot D (Ideal.absNorm_eq_zero_iff.1 e)
    NC_pos := Nat.pos_of_ne_zero fun e => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
    NA_sub := fun x hx => ?_
    NC_sub := fun x hx => ?_ }, ⟨h1, h2, h3⟩, h4, rfl, rfl⟩
  · rw [h3] at hx
    induction hx using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hv
      obtain ⟨z, hz⟩ := GlobalTheory.LatticeData.absNorm_mul_mem_one D ha
      rw [smul_smul, ← hz, algebraMap_smul]
      exact Xx.L'.smul_mem z hu
    | zero => simp
    | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
    | smul c v _ hv => rw [smul_comm]; exact Xx.L'.smul_mem c hv
  · rw [h3]
    exact Submodule.subset_span ⟨_, GlobalTheory.LatticeData.absNorm_ccK_mem D, x, hx, rfl⟩

theorem log_absNorm_le (D : D7) :
    Real.log (Ideal.absNorm D.host.𝔟 : ℕ) ≤ (fdeg D.host.E : ℝ) * Real.log (ReciprocityTheory.ChartRestriction.G.FD.rdE D.host.E) := by
  have hfr := ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.finrank_E D
  have hsq := ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.absNorm_bb_sq_le D
  have hN : 0 < Ideal.absNorm D.host.𝔟 :=
    Nat.pos_of_ne_zero fun e => GlobalTheory.LatticeData.halfDifferent_ne_bot D (Ideal.absNorm_eq_zero_iff.1 e)
  have hf0 : 0 < D.R.f := by
    have : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    omega
  have hfd : fdeg D.host.E = D.R.f := by unfold fdeg; omega
  have hd : 0 < dE D.host.E := by
    unfold dE; exact abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast hf0
  have e : (fdeg D.host.E : ℝ) * Real.log (ReciprocityTheory.ChartRestriction.G.FD.rdE D.host.E) = Real.log (dE D.host.E) / 2 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.rdE
    rw [Real.log_rpow hd, hfd, hfr]
    push_cast
    field_simp
  have hle : ((Ideal.absNorm D.host.𝔟 : ℕ) : ℝ) ^ 2 ≤ dE D.host.E := by
    have : ((Ideal.absNorm D.host.𝔟 : ℕ) : ℝ) ^ 2 ≤ ((discr D.host.E).natAbs : ℝ) := by exact_mod_cast hsq
    rw [Nat.cast_natAbs, Int.cast_abs] at this
    exact this
  have hNR : (0 : ℝ) < (Ideal.absNorm D.host.𝔟 : ℕ) := by exact_mod_cast hN
  have := Real.log_le_log (by positivity) hle
  rw [Real.log_pow] at this
  rw [e]
  push_cast at this
  linarith

theorem holds_without_rows (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (k : (T.U j σ).Comp) :
    ∃ X : DataX D.host.E D.R.r, Fits T j σ k X ∧ X.k0 = 2 * xiR D ∧
      Real.log X.NA ≤ (fdeg D.host.E : ℝ) * Real.log (ReciprocityTheory.ChartRestriction.G.FD.rdE D.host.E) ∧
      X.NC = Ideal.absNorm D.host.ccK := by
  obtain ⟨X, hF, hk, hA, hC⟩ := holds_by_value D T h j hj σ hσ k
  exact ⟨X, hF, hk, by rw [hA]; exact log_absNorm_le D, hC⟩

theorem intersectionNumber_baseChange (D : D7) (T : Top D) (j : ℕ) : Formalism.L2.Pj.QAt.DataXOfModelSt T j := by
  intro h _ hj large₂ w hrows _ σ hσ k
  obtain ⟨X, ⟨h1, h2, h3⟩, -, hA, hC⟩ := holds_by_value D T.toCore h j hj σ hσ k
  refine ⟨X, h1, h2, ?_, ?_, h3⟩
  · rw [hA]; exact log_absNorm_le D
  · rw [hC]; exact hrows.2.2.2.1

theorem indices_bounded {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r) (a b : ℝ)
    (hA : Real.log X.NA ≤ a) (hC : Real.log X.NC ≤ b) : (X.NA : ℝ) ≤ Real.exp a ∧ (X.NC : ℝ) ≤ Real.exp b :=
  ⟨(Real.log_le_iff_le_exp (by exact_mod_cast X.NA_pos)).1 hA,
    (Real.log_le_iff_le_exp (by exact_mod_cast X.NC_pos)).1 hC⟩

end GlobalTheory.ModelLatticeCheck
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.JetSurvey.OrientationExclusive
section
noncomputable section

namespace GlobalTheory.DepthBoundProbe

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem choose_two_add (p q : ℕ) : (p + q).choose 2 = p * q + p.choose 2 + q.choose 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← add_assoc, Nat.choose_succ_succ' (p + q) 1, Nat.choose_succ_succ' q 1, ih]
    simp only [Nat.choose_one_right]
    ring

theorem dimY_eq (Tp : ParamsT D L P) {j : ℕ} (hj : InR D j) : WeightFamilies.dimY D j = Tp.Dp := by
  rw [Tp.Dp_eq]
  unfold WeightFamilies.dimY
  congr 1
  have hr : D.R.r = (D.R.sigW j).1 + (D.R.sigW j).2 := by
    have := hj.1; have := hj.2
    simp only [Ranks.sigW, Ranks.r]; omega
  rw [hr, choose_two_add, Nat.choose_two_right, Nat.choose_two_right]

theorem kappa_last (Tp : ParamsT D L P) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).1) (hi : i.1 + 1 = (D.R.sigW j).1) :
    2 * (Tp.TO : ℤ) ^ 2 ≤ ((kaR Tp hK j).aP τ i : ℤ) := by
  have h1 := hj.1
  have h2 := hj.2
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have e1 := kaWt_big D hK (even_nV Tp) j h1 h2 τ i
  have e2 := (hK j h1 h2 τ).1 i
  have hc := P.e_centred τ ⟨j - 1, by omega⟩
  have h0 := Tp.heightBound_ge_order_sq
  have hi1 : ¬ (i.1 < D.R.k - 1) := by omega
  have hb : i.1 - (D.R.k - 1) < D.R.m := by omega
  have hidx : (⟨i.1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨j - 1, by omega⟩ := Fin.ext (by show i.1 - (D.R.k - 1) = j - 1; omega)
  have hcast : ((i.1 : ℕ) : ℚ) = (D.R.k : ℚ) + j - 1 - 1 := by
    have : i.1 + 2 = D.R.k + j := by omega
    have : ((i.1 : ℕ) : ℚ) + 2 = (D.R.k : ℚ) + j := by exact_mod_cast this
    linarith
  rw [DV.aPlusQ_eq, hcast] at e2
  unfold DV.sigPar DV.eQ at e2
  rw [dif_neg hi1, dif_pos hb, dif_pos ⟨h1, h2⟩, hidx] at e2
  have ht : 5 ≤ D.R.t := by
    have a1 := Tp.split; have a2 := Tp.nP_eq; have a3 := Tp.TO_nW; have a4 := Tp.nW_40
    have : 1 * Tp.nWn ≤ Tp.TO * Tp.nWn := Nat.mul_le_mul_right _ (by have := Tp.TO_40; omega)
    have : Tp.TO * 40 ≤ Tp.TO * Tp.nWn := Nat.mul_le_mul_left _ a4
    omega
  have ht' : (5 : ℝ) ≤ D.R.t := by exact_mod_cast ht
  have e3 : ((D.what₂.kaBig j τ i : ℤ) : ℝ) =
      ((((D.hc τ).e ⟨j - 1, by omega⟩ - (D.hc τ).b ⟨j - 1, by omega⟩ : ℚ)) : ℝ) - ((D.R.t : ℝ) + 1) / 2 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) e2
    push_cast at this ⊢
    linarith
  have h4 := (abs_le.1 hc).1
  have : (2 * (Tp.TO : ℝ) ^ 2) ≤ ((D.what₂.kaBig j τ i : ℤ) : ℝ) := by rw [e3]; linarith
  unfold kaR
  rw [e1]
  exact_mod_cast this

theorem lR_lastPos (Tp : ParamsT D L P) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) : (lR Tp hK j).LastPos := by
  intro τ i hi
  have hn : ¬ i.1 + 1 < (D.R.sigW j).1 := by omega
  have hk := kappa_last Tp hK hj τ i hi
  show 1 ≤ ofGaps (lGapP D (kaR Tp hK j) Tp.TO Tp.nWn τ) i
  rw [ofGaps_last _ _ hn]
  unfold lGapP
  rw [if_neg hn]
  have hp : (0 : ℤ) < (WeightAlgebra.Tp D j Tp.TO : ℤ) := by unfold WeightAlgebra.Tp; push_cast; omega
  rw [Int.fdiv_eq_ediv_of_nonneg _ hp.le]
  have h1 : ((Tp.Dp : ℤ) + 2) * Tp.nWn + 2 * D.R.r ≤ Tp.TO := by exact_mod_cast Tp.TO_nW
  have h40 : 40 * ((Tp.Dp : ℤ) + 2) ≤ Tp.TO := by exact_mod_cast Tp.TO_40
  have : (1 : ℤ) ≤ (((kaR Tp hK j).aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * Tp.nWn - 2 * D.R.r) / (WeightAlgebra.Tp D j Tp.TO : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hp]
    unfold WeightAlgebra.Tp
    rw [dimY_eq Tp hj]
    push_cast
    nlinarith
  omega

theorem one_le_DF (Tp : ParamsT D L P) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) (τ : D.what₂.Tau) :
    1 ≤ WeightAlgebra.DF (lR Tp hK j) := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have h1 := lR_lastPos Tp hK hj τ ⟨(D.R.sigW j).1 - 1, by omega⟩ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
  unfold WeightAlgebra.DF WeightAlgebra.degP
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ => (∑ i, (lR Tp hK j).aP τ i) + ∑ i, (lR Tp hK j).aM τ i)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ))
  exact le_trans (le_trans h1 (Finset.single_le_sum (f := fun i => (lR Tp hK j).aP τ i) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ _))) (Nat.le_add_right _ _)

end GlobalTheory.DepthBoundProbe
end
end

