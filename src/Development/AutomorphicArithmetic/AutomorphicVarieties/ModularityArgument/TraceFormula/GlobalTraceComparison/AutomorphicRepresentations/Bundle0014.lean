import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0007
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0008
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiClosT

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTailInt
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped ENNReal

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section Meas

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem continuous_ac' : Continuous (ac E n) :=
  (GlobalTheory.OneRep.SplitTwist.continuous_splitCentre.comp (continuous_id.div_const _)).prodMk continuous_const

private theorem measurable_reduced_size : Measurable (r0 : H E n 0 → ℝ) := by
  have hc : Continuous fun x : H E n 0 => (ac E n (-ldet x) * x).1 :=
    continuous_fst.comp ((continuous_ac'.comp continuous_ldet.neg).mul continuous_id)
  haveI := borelSpace_H (E := E) (n := n)
  letI : MeasurableSpace (GA E n) := borel _
  haveI : BorelSpace (GA E n) := ⟨rfl⟩
  exact (redBasic E n).2.2.comp hc.measurable

private theorem measurable_cnt {Ω : Set (H E n 0)} (hΩ : IsCompact Ω) :
    Measurable (cnt (ratH E n 0) Ω) := by
  haveI := borelSpace_H (E := E) (n := n)
  haveI : Countable (ratH E n 0) := DiscreteGroups.T1.G.Dcy.countable_ratH'
  have hm : MeasurableSet Ω := hΩ.measurableSet
  refine Measurable.ennreal_tsum fun γ => ?_
  have hc : Continuous fun x : H E n 0 => x⁻¹ * (γ : H E n 0) * x :=
    (continuous_inv.mul continuous_const).mul continuous_id
  exact (measurable_one.indicator hm).comp hc.measurable

end Meas

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.tailInt_of_bounds :
    GFac → GBound → Supp → DomInt → TailInt := by
  intro hF hB hS hD E _ _ _ n ι _ s
  haveI := borelSpace_H (E := E) (n := n)
  obtain ⟨p, hp⟩ := hF E n ι s
  obtain ⟨Ω, hΩ, hC⟩ := hB E n ι s
  choose Cb hCb0 hCb using fun b => hC (p.x b)
  choose Nb hNb using fun b => hD E n s.pos s.D s.π s.fix (p.w b) (p.mem b) Ω hΩ
  refine ⟨Finset.univ.sup Nb, fun L hL => ?_⟩
  choose Db hDb0 hDb using fun b => hNb b L hL
  refine ⟨∑ b, Cb b * Db b, Finset.sum_nonneg fun b _ => mul_nonneg (hCb0 b) (hDb0 b),
    fun m R ρ hR hφ A hA => ?_⟩
  set S : Set (H E n 0) := {x | |ldet x| ≤ R ∧ ρ ≤ r0 x} with hSdef
  have hSm : MeasurableSet S :=
    ((isClosed_le (continuous_abs.comp continuous_ldet) continuous_const).measurableSet).inter
      (measurableSet_le measurable_const measurable_reduced_size)
  set f : p.B → H E n 0 → ℝ≥0∞ := fun b =>
    S.indicator (fun x => ‖(p.w b).1 x.1‖ₑ * cnt (ratH E n 0) Ω x) with hf
  have hfm : ∀ b, Measurable (f b) := fun b => by
    refine Measurable.indicator ?_ hSm
    refine Measurable.mul ?_ (measurable_cnt hΩ)
    exact (((continuous_of_mem s.π (p.mem b)).comp continuous_fst).enorm).measurable
  have hpt : ∀ x, A.indicator (fun x => ‖m.G x x‖ₑ) x ≤
      ∑ b, ENNReal.ofReal (Cb b * ‖m.U‖) * f b x := by
    intro x
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA]
      by_cases hx : |ldet x| ≤ R
      · have hxS : x ∈ S := ⟨hx, hA x hxA hx⟩
        rw [hp m x x]
        refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [enorm_mul, hf]
        simp only [Set.indicator_of_mem hxS]
        calc ‖(p.w b).1 x.1‖ₑ * ‖m.G (ac E n (ldet x) * p.x b) x‖ₑ
            ≤ ‖(p.w b).1 x.1‖ₑ * (ENNReal.ofReal (Cb b * ‖m.U‖) * cnt (ratH E n 0) Ω x) := by
              gcongr; exact hCb b m _ x
          _ = _ := by ring
      · have h0 : m.G x x = 0 := by
          refine hS E n ι s m R hφ x x ?_
          have h1 : R < |ldet x| := not_le.mp hx
          have h2 : |ldet x + ldet x| = 2 * |ldet x| := by
            rw [← two_mul, abs_mul, abs_two]
          rw [h2]
          have := abs_nonneg (ldet x)
          linarith
        simp [h0]
    · rw [Set.indicator_of_notMem hxA]
      exact zero_le
  have h1R : (1 : ℝ) ≤ 1 + R := by linarith
  have hT : ∀ b, ENNReal.ofReal (Cb b * ‖m.U‖) * ∫⁻ x, f b x ∂s.D.ν ≤
      ENNReal.ofReal (Cb b * Db b * ‖m.U‖ * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) := by
    intro b
    have hpow : (1 + R) ^ Nb b ≤ (1 + R) ^ (Finset.univ.sup Nb) :=
      pow_le_pow_right₀ h1R (Finset.le_sup (Finset.mem_univ b))
    have h2 : ∫⁻ x, f b x ∂s.D.ν ≤
        ENNReal.ofReal (Db b * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) := by
      refine (hDb b R ρ hR).trans (ENNReal.ofReal_le_ofReal ?_)
      have := hDb0 b
      have he := (Real.exp_pos (-(L * ρ))).le
      gcongr
    calc _ ≤ ENNReal.ofReal (Cb b * ‖m.U‖) *
          ENNReal.ofReal (Db b * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (hCb0 b) (norm_nonneg _))]
        congr 1
        ring
  calc ∫⁻ x, A.indicator (fun x => ‖m.G x x‖ₑ) x ∂s.D.ν
      ≤ ∫⁻ x, ∑ b, ENNReal.ofReal (Cb b * ‖m.U‖) * f b x ∂s.D.ν := lintegral_mono hpt
    _ = ∑ b, ENNReal.ofReal (Cb b * ‖m.U‖) * ∫⁻ x, f b x ∂s.D.ν := by
        rw [lintegral_finset_sum _ fun b _ => (hfm b).const_mul _]
        exact Finset.sum_congr rfl fun b _ => lintegral_const_mul _ (hfm b)
    _ ≤ ∑ b, ENNReal.ofReal (Cb b * Db b * ‖m.U‖ * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) :=
        Finset.sum_le_sum fun b _ => hT b
    _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · congr 1
          simp only [Finset.sum_mul]
        · intro b _
          have := mul_nonneg (hCb0 b) (hDb0 b)
          have he := (Real.exp_pos (-(L * ρ))).le
          have hp1 : 0 ≤ (1 + R) ^ (Finset.univ.sup Nb) := by positivity
          positivity

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTailOf
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

section SlopeTestRemainingChoices

open NumberField MeasureTheory GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped ENNReal

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem mem_cut_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {τ : ℝ} (hτ : 0 ≤ τ)
    (x : GA E 0) : x ∈ cutSet E 0 τ := by
  have key : ∀ (k : ℕ), k = 0 → ∀ M : Matrix (Fin 0) (Fin k) E, degM x M = 0 := by
    intro k hk M
    subst hk
    exact degM_zero x M
  have hr : ∀ W : Submodule E (Fin 0 → E), Module.finrank E W = 0 := fun W =>
    Module.finrank_zero_of_subsingleton
  refine ⟨fun W => ?_, ?_⟩
  · rw [deg, key _ (hr W), hr W]
    simp [prof]
  · rw [deg, key _ (hr ⊤)]
    simpa using hτ

private theorem tail_num (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) (N k : ℕ) (ρ : ℝ) (hρ : 1 + (k : ℝ) ≤ ρ) :
    (1 + c * ρ) ^ N * Real.exp (-((1 + max 0 (-Real.log ε)) * ρ)) ≤
      ((1 + c) ^ N * (N.factorial * Real.exp 1)) * ε ^ k := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hρ0 : 0 ≤ ρ := by linarith
  set l := max 0 (-Real.log ε) with hl
  have hl0 : 0 ≤ l := le_max_left _ _
  have hl1 : -Real.log ε ≤ l := le_max_right _ _
  have h1 : 1 + c * ρ ≤ (1 + c) * (1 + ρ) := by nlinarith
  have h2 : (1 + ρ) ^ N ≤ N.factorial * Real.exp (1 + ρ) := by
    have := Real.pow_div_factorial_le_exp (1 + ρ) (by linarith) N
    rwa [div_le_iff₀' (by positivity)] at this
  have h3 : Real.exp (-(l * ρ)) ≤ ε ^ k := by
    have e : ε ^ k = Real.exp (k * Real.log ε) := by
      rw [mul_comm, Real.exp_mul, Real.exp_log hε, Real.rpow_natCast]
    rw [e]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg hl0 (by linarith : (0 : ℝ) ≤ ρ - k), mul_le_mul_of_nonneg_right hl1 hk]
  have h4 : Real.exp (-((1 + l) * ρ)) = Real.exp (-ρ) * Real.exp (-(l * ρ)) := by
    rw [← Real.exp_add]
    ring_nf
  have h5 : Real.exp (1 + ρ) * Real.exp (-ρ) = Real.exp 1 := by
    rw [← Real.exp_add]
    ring_nf
  calc (1 + c * ρ) ^ N * Real.exp (-((1 + l) * ρ))
      ≤ ((1 + c) * (1 + ρ)) ^ N * Real.exp (-((1 + l) * ρ)) := by
        refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h1 N) (Real.exp_pos _).le
    _ = (1 + c) ^ N * ((1 + ρ) ^ N * Real.exp (-ρ)) * Real.exp (-(l * ρ)) := by
        rw [h4, mul_pow]
        ring
    _ ≤ (1 + c) ^ N * (N.factorial * Real.exp 1) * ε ^ k := by
        have h6 : (1 + ρ) ^ N * Real.exp (-ρ) ≤ N.factorial * Real.exp 1 := by
          calc (1 + ρ) ^ N * Real.exp (-ρ) ≤ (N.factorial * Real.exp (1 + ρ)) * Real.exp (-ρ) :=
                mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
            _ = N.factorial * Real.exp 1 := by rw [mul_assoc, h5]
        exact mul_le_mul (mul_le_mul_of_nonneg_left h6 (by positivity)) h3 (Real.exp_pos _).le (by positivity)

private theorem diff_le {X : Type*} [MeasurableSpace X] (ν : Measure X) (f g : X → ℂ) (A : Set X)
    (hA : MeasurableSet A) (hf : Integrable f ν) (h : ∀ x, g x = f x - A.indicator f x) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∫⁻ x, A.indicator (fun x => ‖f x‖ₑ) x ∂ν ≤ ENNReal.ofReal B) :
    ‖∫ x, g x ∂ν - ∫ x, f x ∂ν‖ ≤ B := by
  have e : ∫ x, g x ∂ν - ∫ x, f x ∂ν = -∫ x, A.indicator f x ∂ν := by
    simp only [h]
    rw [integral_sub hf (hf.indicator hA)]
    ring
  rw [e, norm_neg]
  have h1 : ‖∫ x, A.indicator f x ∂ν‖ₑ ≤ ENNReal.ofReal B := by
    refine (enorm_integral_le_lintegral_enorm _).trans (le_trans (le_of_eq ?_) hb)
    refine lintegral_congr fun x => ?_
    exact enorm_indicator_eq_indicator_enorm ..
  rw [← ofReal_norm] at h1
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp h1

private theorem tail_main : UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.Sizes → UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.InCut → UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.TailInt →
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.DiagInt → DiscreteGroups.T1.G.CutTail2 := by
  intro hS hI hT hD E _ _ _ n hn D π hπ ι _ Φ₁ Φ₂ T₁ T₂ M k₁ k₂ r₀ r₁ ε a1 a2 hfin b1 b2 hv hr₀ hr₁ hε
  let s : Su E n ι := ⟨D, π, Φ₁, Φ₂, T₁, T₂, M, k₁, k₂, hn, hπ, a1, a2, hfin, b1, b2, hv⟩
  obtain ⟨c, hc, hsz⟩ := hS E n hn
  obtain ⟨c', hc', hcut⟩ := hI E n
  obtain ⟨N, hN⟩ := hT E n ι s
  obtain ⟨Ct, hCt, hbd⟩ := hN (1 + max 0 (-Real.log ε)) (by positivity)
  refine ⟨(c' + 1) * (2 + c + c ^ 2), fun C' hC' =>
    ⟨Ct * ((1 + c) ^ N * (N.factorial * Real.exp 1)), fun k U Uπ Φ t o pp ht => ?_⟩⟩
  let m : Mid s := ⟨U, Uπ, Φ, t, o, pp⟩
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (1 + k) * (1 + r₀ + r₁) := ⟨_, rfl⟩
  have hρk : 1 + (k : ℝ) ≤ ρ := by rw [hρdef]; nlinarith [mul_nonneg hk hr₀, mul_nonneg hk hr₁]
  have hρ1 : 1 ≤ ρ := by linarith
  have hρr : 1 + (r₀ + k * r₁) ≤ ρ := by rw [hρdef]; nlinarith [mul_nonneg hk hr₀, mul_nonneg hk hr₁]
  have hC'0 : 0 ≤ C' := le_trans (by positivity) hC'
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = C' * ρ := ⟨_, rfl⟩
  have hτ0 : 0 ≤ τ := by rw [hτdef]; positivity
  have hR0 : 0 ≤ c * ρ := by positivity
  have hsupp : ∀ z, m.φ z ≠ 0 → |ldet z| ≤ c * ρ := fun z hz => by
    have h1 := (ht.toIsTest2.size z hz).1
    refine (hsz z).2.1.trans (mul_le_mul_of_nonneg_left ?_ hc)
    linarith
  let A : Set (H E n 0) := {x | x.1 ∉ cutSet E n τ}
  have hAm : MeasurableSet A := by
    have ho : IsOpen A := ((mahler_holds E n τ).1.preimage continuous_fst).isOpen_compl
    haveI : BorelSpace (H E n 0) := ⟨rfl⟩
    exact ho.measurableSet
  have hAρ : ∀ x ∈ A, |ldet x| ≤ c * ρ → ρ ≤ r0 x := fun x hx hl => by
    by_contra hlt
    refine hx (hcut τ x.1 ?_)
    have h1 := (hsz x).1
    have h2 : redSize x.1 ≤ ρ + c * (1 + c * ρ) := h1.trans (add_le_add (not_le.mp hlt).le
      (mul_le_mul_of_nonneg_left (by linarith) hc))
    have h3 : 1 + redSize x.1 ≤ (2 + c + c ^ 2) * ρ := by nlinarith [mul_nonneg hc (by linarith : (0 : ℝ) ≤ ρ - 1)]
    have hq : 0 ≤ (2 + c + c ^ 2) * ρ := by positivity
    calc c' * (1 + redSize x.1) ≤ c' * ((2 + c + c ^ 2) * ρ) := mul_le_mul_of_nonneg_left h3 hc'
      _ ≤ (c' + 1) * ((2 + c + c ^ 2) * ρ) := mul_le_mul_of_nonneg_right (by linarith) hq
      _ = ((c' + 1) * (2 + c + c ^ 2)) * ρ := by ring
      _ ≤ C' * ρ := mul_le_mul_of_nonneg_right hC' (by linarith)
      _ = τ := hτdef.symm
  have hb := hbd m (c * ρ) ρ hR0 hsupp A hAρ
  have hB : 0 ≤ Ct * ‖U‖ * (1 + c * ρ) ^ N * Real.exp (-((1 + max 0 (-Real.log ε)) * ρ)) := by positivity
  have hmain := diff_le D.ν (lInt0 D k₁ k₂ Uπ) (lInt D k₁ k₂ τ Uπ) A hAm (hD E n ι s m) (fun x => by
      have h2 : chiT τ x.2 = (1 : ℂ) := Set.indicator_of_mem (mem_cut_zero hτ0 x.2) _
      by_cases hx : x.1 ∈ cutSet E n τ
      · have h1 : chiT τ x.1 = (1 : ℂ) := Set.indicator_of_mem hx _
        have h3 : x ∉ A := fun h => h hx
        simp [lInt, lInt0, h1, h2, h3]
      · have h1 : chiT τ x.1 = (0 : ℂ) := Set.indicator_of_notMem hx _
        have h3 : x ∈ A := hx
        simp [lInt, lInt0, h1, h2, h3]) _ hB hb
  rw [← hρdef, ← hτdef]
  refine hmain.trans ?_
  have hn' := tail_num c ε hc hε N k ρ hρk
  calc Ct * ‖U‖ * (1 + c * ρ) ^ N * Real.exp (-((1 + max 0 (-Real.log ε)) * ρ))
      = Ct * ‖U‖ * ((1 + c * ρ) ^ N * Real.exp (-((1 + max 0 (-Real.log ε)) * ρ))) := by ring
    _ ≤ Ct * ‖U‖ * (((1 + c) ^ N * (N.factorial * Real.exp 1)) * ε ^ k) :=
        mul_le_mul_of_nonneg_left hn' (by positivity)
    _ = Ct * ((1 + c) ^ N * (N.factorial * Real.exp 1)) * ‖U‖ * ε ^ k := by ring

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.tailOf_pf :
    Basic → Sizes → InCut → TailInt → DiagInt → DiscreteGroups.T1.G.CutTail2 := fun _ => tail_main
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PartEq
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open scoped Classical ENNReal

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]

private theorem row_int (D : Dom E n 0) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) (w : Lp ℂ 2 D.ν) (x : H E n 0) :
    Integrable (fun y => kerH φ x y * (w : H E n 0 → ℂ) y) D.ν :=
  MemLp.integrable_mul ((kernel_rows_columns_square_integrable (ctx ratProper_holds D) φ hφ).2 x) (Lp.memLp w)

private theorem ker_trM (D : Dom E n 0) {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ) (M : Matrix ι ι ℂ)
    (x y : H E n 0) : kerH (trM Φ M) x y = ∑ i, ∑ j, kerH (Φ i j) x y * M j i := by
  have h := (kerLin (ctx ratProper_holds D) (ι × ι) (fun p => Φ p.1 p.2) (fun p => M p.2 p.1)
    (fun p => hΦ p.1 p.2)).2 x y
  have e : trM Φ M = fun z => ∑ p : ι × ι, Φ p.1 p.2 z * M p.2 p.1 := by
    funext z
    simp only [trM, Fintype.sum_prod_type]
  rw [e]
  refine Eq.trans h ?_
  exact Fintype.sum_prod_type _

private theorem part_eq {D : Dom E n 0} {π : CuspSub E n} {U Uπ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D}
    (h : IsPiPart D π U Uπ) (f : Hs (ι := ι) D) : Uπ f = U ((piSp D π ι).starProjection f) := by
  have h1 : Uπ ((piSp D π ι).starProjection f) = U ((piSp D π ι).starProjection f) :=
    h.1 _ (Submodule.starProjection_apply_mem _ _)
  have h2 : Uπ (f - (piSp D π ι).starProjection f) = 0 :=
    h.2 _ (Submodule.sub_starProjection_mem_orthogonal _)
  rw [map_sub, sub_eq_zero] at h2
  rw [h2, h1]

private theorem vec_int {D : Dom E n 0} (w : Lp ℂ 2 D.ν) (c : ι → ℂ) (j : ι) {φ : H E n 0 → ℂ} (hφ : IsTestH φ)
    (x : H E n 0) :
    ∫ y, kerH φ x y * ((vecM w c) j : H E n 0 → ℂ) y ∂D.ν = c j * ∫ y, kerH φ x y * (w : H E n 0 → ℂ) y ∂D.ν := by
  have e : ((vecM w c) j : H E n 0 → ℂ) =ᵐ[D.ν] fun y => c j * (w : H E n 0 → ℂ) y := by
    have : (vecM w c) j = c j • w := rfl
    rw [this]
    filter_upwards [Lp.coeFn_smul (c j) w] with y hy
    simpa using hy
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [e] with y hy
  rw [hy]; ring

end SlopeTestRemainingChoices

theorem ker_pf :
    Weak → PointRep → PComm → PDiag → Ker := by
  intro hW hPR hPC hPD E _ _ _ n ι _ s m v x
  set w := P0 s.D s.π v with hw
  let u : ι → Hs (ι := ι) s.D := fun i => ContinuousLinearMap.adjoint m.Uπ (s.k₁ x i)
  have hG : ∀ y, (v : H E n 0 → ℂ) y * m.G x (th y) =
      ∑ i, (v : H E n 0 → ℂ) y * inner ℂ (u i) (s.k₂ (th y) i) := by
    intro y
    simp only [Mid.G, Gk, Finset.mul_sum, u, ContinuousLinearMap.adjoint_inner_left]
  have hI : ∀ i, Integrable (fun y => (v : H E n 0 → ℂ) y * inner ℂ (u i) (s.k₂ (th y) i)) s.D.ν :=
    fun i => (hW E n ι s v (u i) i).1
  have hterm : ∀ i, ∫ y, (v : H E n 0 → ℂ) y * inner ℂ (u i) (s.k₂ (th y) i) ∂s.D.ν =
      ∑ j, s.M j i * ∫ y, kerH (m.Φ i j) x y * (w : H E n 0 → ℂ) y ∂s.D.ν := by
    intro i
    rw [(hW E n ι s v (u i) i).2]
    have e1 : inner ℂ (u i) (s.T₂ (vecM v fun l => s.M l i)) =
        inner ℂ (s.k₁ x i) (m.U (s.T₂ (vecM w fun l => s.M l i))) := by
      simp only [u, ContinuousLinearMap.adjoint_inner_left]
      rw [part_eq m.pp, hPC E n s.pos s.D s.π s.fix ι s.Φ₂ s.T₂ s.t₂ s.o₂, hPD E n s.D s.π ι]
    rw [e1, hPR E n ι s m.Φ (s.T₁ * m.U * s.T₂) m.t m.o (m.U (s.T₂ (vecM w fun l => s.M l i)))
      (vecM w fun l => s.M l i) rfl x i]
    exact Finset.sum_congr rfl fun j _ => vec_int w _ j (m.t i j) x
  refine ⟨?_, ?_⟩
  · simp only [hG]
    exact integrable_finset_sum _ fun i _ => hI i
  · simp only [hG]
    rw [integral_finset_sum _ fun i _ => hI i]
    simp only [hterm]
    have e2 : ∀ y, kerH m.φ x y * (w : H E n 0 → ℂ) y =
        ∑ i, ∑ j, s.M j i * (kerH (m.Φ i j) x y * (w : H E n 0 → ℂ) y) := by
      intro y
      rw [Mid.φ, ker_trM s.D m.t, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [e2]
    have hr : ∀ i j, Integrable (fun y => kerH (m.Φ i j) x y * (w : H E n 0 → ℂ) y) s.D.ν :=
      fun i j => row_int s.D (m.t i j) w x
    rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (hr i j).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => (hr i j).const_mul _]
    exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PositionPairFunctionsEq
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem tst_trM (D : Dom E n 0) {ι : Type} [Fintype ι] {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ)
    (M : Matrix ι ι ℂ) : PositivityTheory.Rg.BcB.E1.Tst (G := (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D).G) (trM Φ M) := by
  have h := (PositivityTheory.Rg.BcB.E1.kerLin (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D) (ι × ι)
    (fun p => Φ p.1 p.2) (fun p => M p.2 p.1) (fun p => hΦ p.1 p.2)).1
  have e : trM Φ M = fun y => ∑ p : ι × ι, Φ p.1 p.2 y * M p.2 p.1 := by
    funext y
    rw [Fintype.sum_prod_type]
    rfl
  rw [e]
  exact h

private theorem cusp_projection_self (D : Dom E n 0) (π : CuspSub E n) {ψ : Sm E n} (hψ : ψ ∈ π.V) {w : ℝ → ℂ}
    (hw : Continuous w) (hws : HasCompactSupport w) (v : Lp ℂ 2 D.ν)
    (hv : (v : H E n 0 → ℂ) =ᵐ[D.ν] fun x => ψ.1 x.1 * w (ldet x)) : P0 D π v = v := by
  have hvec : IsPiVec D π (vecM v fun _ : Unit => (1 : ℂ)) := fun _ => ⟨ψ, hψ, w, hw, hws, by
    have e : (vecM v fun _ : Unit => (1 : ℂ)) () = v := one_smul ℂ v
    simpa [e] using hv⟩
  have hmem : (vecM v fun _ : Unit => (1 : ℂ)) ∈ piSp D π Unit :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span hvec)
  unfold P0
  rw [Submodule.starProjection_eq_self_iff.2 hmem]
  exact one_smul ℂ v

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.rep_pf :
    Basic → ThetaInt → KInv → PDiag → Ker → Rep := by
  intro hB hTI hK _ hKer E _ _ _ n ι _ s m ψ hψ u hu hus x₀
  obtain ⟨-, bMul, -, -, -, -, bThL, bThTh, bThMul, bRat, -, -⟩ := hB E n s.pos
  obtain ⟨ψ₁, hψ₁, hψe⟩ := s.fix.2 ψ hψ
  have hw : Continuous fun t : ℝ => u (-t) := hu.comp continuous_neg
  have hws : HasCompactSupport fun t : ℝ => u (-t) := hus.comp_homeomorph (Homeomorph.neg ℝ)
  set f : H E n 0 → ℂ := fun x => ψ₁.1 x.1 * u (-ldet x) with hf
  have hmem : MemLp f 2 s.D.ν := (DiscreteGroups.T1.G.Dcy.piVecEx_holds E n s.pos s.D s.π s.fix ψ₁ hψ₁ _ hw hws).1
  set v : Lp ℂ 2 s.D.ν := hmem.toLp f with hvdef
  have hv : (v : H E n 0 → ℂ) =ᵐ[s.D.ν] f := hmem.coeFn_toLp
  have hP : P0 s.D s.π v = v := cusp_projection_self s.D s.π hψ₁ hw hws v hv
  obtain ⟨kI, kE⟩ := hKer E n ι s m v x₀
  rw [hP] at kE
  have hψinv : ∀ (γ : ratH E n 0) (y : H E n 0), ψ₁.1 ((γ : H E n 0) * y).1 = ψ₁.1 y.1 := by
    intro γ y
    obtain ⟨⟨γ₁, γ₂⟩, hγ⟩ := γ.2
    have h1 : (γ : H E n 0).1 = ratGL E n γ₁ := by rw [← hγ]; rfl
    rw [Prod.fst_mul, h1]
    exact (s.π.cusp ψ₁ hψ₁).1.left γ₁ y.1
  have hfinv : ∀ (γ : ratH E n 0) (y : H E n 0), f ((γ : H E n 0) * y) = f y := by
    intro γ y
    simp only [hf]
    rw [hψinv γ y, bMul, (bRat γ).1, zero_add]
  have hGinv : ∀ (γ : ratH E n 0) (y : H E n 0), m.G x₀ (th ((γ : H E n 0) * y)) = m.G x₀ (th y) := by
    intro γ y
    have h2 := hK E n ι s |>.2 ⟨th (γ : H E n 0), (bRat γ).2⟩ (th y)
    simp only [Mid.G, Gk]
    rw [bThMul, h2]
  set F : H E n 0 → ℂ := fun y => f y * m.G x₀ (th y) with hF
  have hFinv : Inv F := fun γ y => by
    simp only [hF]
    rw [hfinv, hGinv]
  have hFint : Integrable F s.D.ν := kI.congr (hv.mono fun y hy => by simp only [hF, hy])
  obtain ⟨tI, tE⟩ := hTI E n s.D F hFinv hFint
  have hFth : ∀ x, F (th x) = ψ.1 x.1 * m.G x₀ x * u (ldet x) := by
    intro x
    have h1 : ψ₁.1 (th x).1 = ψ.1 x.1 := by
      have e : thetaA E n (th x).1 = x.1 := congrArg Prod.fst (bThTh x)
      rw [hψe, e]
    simp only [hF, hf]
    rw [h1, bThL, neg_neg, bThTh]
    ring
  refine ⟨tI.congr (Filter.Eventually.of_forall hFth), ?_⟩
  have hμl : s.D.μ.IsMulLeftInvariant := s.D.haar.1
  haveI hmm : MeasurableMul (H E n 0) :=
    (inferInstance : MeasurableMul (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds s.D).G)
  have hun := (DiscreteGroups.T1.G.unfold (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds s.D)
    PositivityTheory.Rg.BcB.E1.kerBasic PositivityTheory.Rg.BcB.E1.kernel_rows_columns_square_integrable (tst_trM s.D m.t s.M) (f := f) hfinv hmem x₀).2
  have hun' : ∫ y, kerH m.φ x₀ y * f y ∂s.D.ν = ∫ y, m.φ (x₀⁻¹ * y) * f y ∂s.D.μ := hun
  calc ∫ x, ψ.1 x.1 * m.G x₀ x * u (ldet x) ∂s.D.ν
      = ∫ x, F (th x) ∂s.D.ν := integral_congr_ae (Filter.Eventually.of_forall fun x => (hFth x).symm)
    _ = ∫ x, F x ∂s.D.ν := tE
    _ = ∫ y, (v : H E n 0 → ℂ) y * m.G x₀ (th y) ∂s.D.ν :=
        integral_congr_ae (hv.mono fun y hy => by simp only [hF, hy])
    _ = ∫ y, kerH m.φ x₀ y * (v : H E n 0 → ℂ) y ∂s.D.ν := kE
    _ = ∫ y, kerH m.φ x₀ y * f y ∂s.D.ν := integral_congr_ae (hv.mono fun y hy => by simp only [hy])
    _ = ∫ y, m.φ (x₀⁻¹ * y) * f y ∂s.D.μ := hun'
    _ = ∫ z, m.φ (x₀⁻¹ * (x₀ * z)) * f (x₀ * z) ∂s.D.μ :=
        (integral_mul_left_eq_self (fun y => m.φ (x₀⁻¹ * y) * f y) x₀).symm
    _ = ∫ z, m.φ z * ψ.1 (thetaA E n (x₀.1 * z.1)) * u (-(ldet x₀ + ldet z)) ∂s.D.μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [hf]
        rw [inv_mul_cancel_left, bMul, Prod.fst_mul, hψe]
        ring

end
end

