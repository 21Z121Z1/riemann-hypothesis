import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BiadditivePadicLinear.Cont2
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.Bundle0002

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BiadditivePadicLinear.BiaddZpLinOf
section
noncomputable section

open Classical

namespace PI.BiaddZpLinW

open PI.BiaddZpLin

theorem t0 : ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g h f' g' : MvPowerSeries σ ℂ_[p]),
    Simeq f f ∧ (Simeq f g → Simeq g f) ∧ (Simeq f g → Simeq g h → Simeq f h) ∧
    (Simeq f g → Simeq f' g' → Simeq (f + f') (g + g')) :=
  PI.BeDiagZp.simeq_equivalence_additive

theorem t1 : ∀ (p : ℕ) [Fact p.Prime] (σ τ : Type) [Finite σ] (f g : MvPowerSeries σ ℂ_[p])
    (s : σ → MvPowerSeries τ ℂ_[p]),
    (∀ i, MvPowerSeries.constantCoeff (s i) = 0) → (∀ i, IntegralMv (s i)) →
    Simeq f g → Simeq (MvPowerSeries.subst s f) (MvPowerSeries.subst s g) :=
  PI.BeDiagZp.power_series_diagonal_linear

theorem t2 : ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.constantCoeff l = 0 →
    ∀ (σ τ : Type) [Finite σ] (s : σ → MvPowerSeries τ ℂ_[p]),
    (∀ i, MvPowerSeries.constantCoeff (s i) = 0) →
    (∀ i, MvPowerSeries.subst s (Xv i : MvPowerSeries σ ℂ_[p]) = s i) ∧
    (∀ (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]),
      MvPowerSeries.subst s (MvPowerSeries.C c * a) = MvPowerSeries.C c * MvPowerSeries.subst s a) ∧
    (∀ a b : MvPowerSeries σ ℂ_[p],
      MvPowerSeries.subst s (a + b) = MvPowerSeries.subst s a + MvPowerSeries.subst s b) ∧
    ∀ a b : MvPowerSeries σ ℂ_[p], MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst s a) = 0 ∧
      MvPowerSeries.subst s (add l ex a b) = add l ex (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) ∧
      (∀ c, MvPowerSeries.subst s (mulBy l ex c a) = mulBy l ex c (MvPowerSeries.subst s a)) ∧
      MvPowerSeries.subst s (phAt ph a) = phAt ph (MvPowerSeries.subst s a) ∧
      MvPowerSeries.subst s (be l ex ph a b) = be l ex ph (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) :=
  PI.BeDiagZp.OpsW.substOps_holds

theorem t3 : ∀ (p : ℕ) [Fact p.Prime] (l ex : PowerSeries ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    PowerSeries.constantCoeff l = 0 ∧
    ∀ (σ : Type) (a b : MvPowerSeries σ ℂ_[p]),
      MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
      MvPowerSeries.constantCoeff (add l ex a b) = 0 ∧
      (∀ c, MvPowerSeries.constantCoeff (mulBy l ex c a) = 0) ∧
      add l ex a b = add l ex b a ∧
      add l ex a a = mulBy l ex 2 a ∧
      (∀ c d, add l ex (mulBy l ex c a) (mulBy l ex d a) = mulBy l ex (c + d) a) ∧
      (∀ c, add l ex (mulBy l ex c a) a = mulBy l ex (c + 1) a) ∧
      mulBy l ex 1 a = a ∧
      mulBy l ex 0 a = 0 :=
  PI.BeDiagZp.IdentW.ident_holds

theorem t5 : ∀ (p : ℕ) [Fact p.Prime] (σ τ : Type) [Finite σ] (f : MvPowerSeries σ ℂ_[p])
    (s : σ → MvPowerSeries τ ℂ_[p]),
    (∀ i, MvPowerSeries.constantCoeff (s i) = 0) → (∀ i, IntegralMv (s i)) →
    IntegralMv f → IntegralMv (MvPowerSeries.subst s f) :=
  PI.BeDiagZp.intSubst_holds

variable {p : ℕ} [Fact p.Prime]

theorem simeq_congr {σ : Type} {f g f' g' : MvPowerSeries σ ℂ_[p]} (e : f - g = f' - g')
    (h : Simeq f g) : Simeq f' g' := by
  unfold Simeq at *
  rw [← e]
  exact h

theorem intX {σ : Type} (i : σ) : IntegralMv (Xv i : MvPowerSeries σ ℂ_[p]) := by
  intro n
  simp only [IsIntP, Xv, MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem int0 {σ : Type} : IntegralMv (0 : MvPowerSeries σ ℂ_[p]) := by
  intro n
  simp [IsIntP]

theorem ccX {σ : Type} (i : σ) : MvPowerSeries.constantCoeff (Xv i : MvPowerSeries σ ℂ_[p]) = 0 := by
  simp [Xv]

theorem natCase (l ex ph : PowerSeries ℂ_[p]) (hex : PowerSeries.constantCoeff ex = 0)
    (hlex : PowerSeries.subst ex l = PowerSeries.X)
    (hgrp : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    (hbi : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2))) (n : ℕ) :
    IntegralMv (mulBy l ex (n : ℂ_[p]) (Xv 0) : MvPowerSeries (Fin 2) ℂ_[p]) ∧
    Simeq (be l ex ph (mulBy l ex (n : ℂ_[p]) (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (MvPowerSeries.C (n : ℂ_[p]) * be l ex ph (Xv 0) (Xv 1)) := by
  obtain ⟨hl0, hI⟩ := t3 p l ex hex hlex
  have symm' : ∀ {σ : Type} {f g : MvPowerSeries σ ℂ_[p]}, Simeq f g → Simeq g f :=
    fun {σ} {f g} h => (t0 p σ f g g g g).2.1 h
  have trans' : ∀ {σ : Type} {f g k : MvPowerSeries σ ℂ_[p]}, Simeq f g → Simeq g k → Simeq f k :=
    fun {σ} {f g k} a b => (t0 p σ f g k f f).2.2.1 a b
  have add' : ∀ {σ : Type} {f g f' g' : MvPowerSeries σ ℂ_[p]}, Simeq f g → Simeq f' g' →
      Simeq (f + f') (g + g') :=
    fun {σ} {f g f' g'} a b => (t0 p σ f g f f' g').2.2.2 a b
  have rfl' : ∀ {σ : Type} (f : MvPowerSeries σ ℂ_[p]), Simeq f f := fun f => (t0 p _ f f f f f).1
  have cA : ∀ {σ : Type} (a b : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff b = 0 → MvPowerSeries.constantCoeff (add l ex a b) = 0 :=
    fun a b ha hb => (hI _ a b ha hb).1
  have cM : ∀ {σ : Type} (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff (mulBy l ex c a) = 0 :=
    fun c a ha => (hI _ a a ha ha).2.1 c
  have comm : ∀ {σ : Type} (a b : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff b = 0 → add l ex a b = add l ex b a :=
    fun a b ha hb => (hI _ a b ha hb).2.2.1
  have addM : ∀ {σ : Type} (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      ∀ c d, add l ex (mulBy l ex c a) (mulBy l ex d a) = mulBy l ex (c + d) a :=
    fun a ha => (hI _ a a ha ha).2.2.2.2.1
  have addS : ∀ {σ : Type} (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      ∀ c, add l ex (mulBy l ex c a) a = mulBy l ex (c + 1) a :=
    fun a ha => (hI _ a a ha ha).2.2.2.2.2.1
  have mul1 : ∀ {σ : Type} (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      mulBy l ex 1 a = a :=
    fun a ha => (hI _ a a ha ha).2.2.2.2.2.2.1
  have mul0 : ∀ {σ : Type} (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      mulBy l ex 0 a = 0 :=
    fun a ha => (hI _ a a ha ha).2.2.2.2.2.2.2
  have addZ : ∀ {σ : Type} (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      add l ex a 0 = a := by
    intro σ a ha
    have e := addM a ha 1 0
    rw [mul1 a ha, mul0 a ha, add_zero, mul1 a ha] at e
    exact e

  have K2 : ∀ a b c : MvPowerSeries (Fin 2) ℂ_[p], MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff b = 0 → MvPowerSeries.constantCoeff c = 0 →
      IntegralMv a → IntegralMv b → IntegralMv c →
      Simeq (be l ex ph (add l ex a b) c) (be l ex ph a c + be l ex ph b c) := by
    intro a b c ha hb hc ia ib ic
    have hs : ∀ i, MvPowerSeries.constantCoeff (![a, b, c] i) = 0 := by
      intro i; fin_cases i <;> simpa
    have is : ∀ i, IntegralMv (![a, b, c] i) := by
      intro i; fin_cases i <;> simpa
    have H := t1 p (Fin 3) (Fin 2) _ _ ![a, b, c] hs is hbi
    obtain ⟨hsX, -, hsA, hr⟩ := t2 p l ex ph hex hl0 (Fin 3) (Fin 2) ![a, b, c] hs
    have e1 := (hr _ _ (cA _ _ (ccX (0 : Fin 3)) (ccX (1 : Fin 3))) (ccX (2 : Fin 3))).2.2.2.2
    have e2 := (hr _ _ (ccX (0 : Fin 3)) (ccX (1 : Fin 3))).2.1
    have e3 := (hr _ _ (ccX (0 : Fin 3)) (ccX (2 : Fin 3))).2.2.2.2
    have e4 := (hr _ _ (ccX (1 : Fin 3)) (ccX (2 : Fin 3))).2.2.2.2
    simp only [hsA, e1, e2, e3, e4, hsX] at H
    simpa using H
  have c0 : MvPowerSeries.constantCoeff (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := ccX 0
  have c1 : MvPowerSeries.constantCoeff (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := ccX 1
  induction n with
  | zero =>
    rw [Nat.cast_zero, mul0 _ c0]
    refine ⟨int0, ?_⟩
    have H := symm' (K2 0 0 0 (map_zero _) (map_zero _) (map_zero _) int0 int0 int0)
    have z00 : add l ex (0 : MvPowerSeries (Fin 2) ℂ_[p]) 0 = 0 := addZ 0 (map_zero _)
    have z01 : add l ex (0 : MvPowerSeries (Fin 2) ℂ_[p]) (Xv 1) = Xv 1 := by
      rw [comm _ _ (map_zero _) c1, addZ _ c1]
    refine simeq_congr ?_ H
    rw [map_zero, zero_mul, sub_zero]
    simp only [be, z00, z01]
    abel
  | succ n ih =>
    obtain ⟨iN, hN⟩ := ih
    have cN := cM (n : ℂ_[p]) _ c0
    have eS : mulBy l ex ((n + 1 : ℕ) : ℂ_[p]) (Xv 0) =
        add l ex (mulBy l ex (n : ℂ_[p]) (Xv 0)) (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) := by
      rw [addS _ c0, Nat.cast_succ]
    rw [eS]
    refine ⟨?_, ?_⟩
    · have hs : ∀ i, MvPowerSeries.constantCoeff
          (![mulBy l ex (n : ℂ_[p]) (Xv 0), (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p])] i) = 0 := by
        intro i; fin_cases i <;> simpa
      have is : ∀ i, IntegralMv
          (![mulBy l ex (n : ℂ_[p]) (Xv 0), (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p])] i) := by
        intro i; fin_cases i
        · simpa using iN
        · simpa using (intX 0 : IntegralMv (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]))
      have H := t5 p (Fin 2) (Fin 2) _ _ hs is hgrp
      obtain ⟨hsX, -, -, hr⟩ := t2 p l ex ph hex hl0 (Fin 2) (Fin 2) _ hs
      rw [(hr _ _ (ccX (0 : Fin 2)) (ccX (1 : Fin 2))).2.1, hsX, hsX] at H
      simpa using H
    · have H := K2 _ _ _ cN c0 c1 iN (intX 0) (intX 1)
      have H2 := trans' H (add' hN (rfl' (be l ex ph (Xv 0) (Xv 1))))
      have e : MvPowerSeries.C (n : ℂ_[p]) * be l ex ph (Xv 0) (Xv 1) + be l ex ph (Xv 0) (Xv 1) =
          (MvPowerSeries.C ((n + 1 : ℕ) : ℂ_[p]) * be l ex ph (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) := by
        rw [Nat.cast_succ, map_add, map_one, add_mul, one_mul]
      rw [e] at H2
      exact H2

theorem biaddZpLin_of (hC : Cont2) : PI.BiaddZpLin.Target := by
  intro p _ l ex ph hex hlex hgrp hbi n
  exact hC p l ex ph hex (t3 p l ex hex hlex).1 (fun k => (natCase l ex ph hex hlex hgrp hbi k).2) n

end PI.BiaddZpLinW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BiadditivePadicLinear.BiadditiveContinuousPadic
section
noncomputable section

open Classical

namespace PI.BiaddZpLinW

open PI.BiaddZpLin PI.BeDiagZp.ContPf

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime]

theorem cc_expMv' {σ : Type} {G : ℂ_[p] → MvPowerSeries σ ℂ_[p]} (hG : CC G) :
    CC fun c => expMv (G c) := by
  intro e
  show Continuous fun c => ∑ n ∈ Finset.range ((e.sum fun _ k => k) + 1),
    MvPowerSeries.coeff e (G c ^ n) / (n.factorial : ℂ_[p])
  exact continuous_finsetSum _ fun n _ => (cc_pow hG n e).div_const _

theorem zc_continuous' : Continuous (zc : ℤ_[p] → ℂ_[p]) := by
  unfold zc
  exact (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val

theorem zc_natCast' (n : ℕ) : zc (n : ℤ_[p]) = (n : ℂ_[p]) := by
  simp [zc]

end SlopeTestRemainingChoices

theorem biadditive_continuous_padic : Cont2 := by
  intro p _ l ex ph hex hl hN n
  let a : MvPowerSeries (Fin 2) ℂ_[p] := Xv 0
  let b : MvPowerSeries (Fin 2) ℂ_[p] := Xv 1
  have ha : MvPowerSeries.constantCoeff a = 0 := by simp [a, Xv]
  have hb : MvPowerSeries.constantCoeff b = 0 := by simp [b, Xv]
  have hla : MvPowerSeries.constantCoeff (PowerSeries.subst a l) = 0 := constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution a ha l hl
  have hlb : MvPowerSeries.constantCoeff (PowerSeries.subst b l) = 0 := constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution b hb l hl
  have hM0 : ∀ c : ℂ_[p], MvPowerSeries.constantCoeff (mulBy l ex c a) = 0 := by
    intro c
    apply constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ _ ex hex
    simp [hla]
  have hM : CC fun c : ℂ_[p] => mulBy l ex c a := by
    apply cc_subst ex (fun c => by simp [hla]) (cc_mul cc_C (cc_const _))
  have hI0 : ∀ c : ℂ_[p], MvPowerSeries.constantCoeff
      (PowerSeries.subst (mulBy l ex c a) l + PowerSeries.subst b l) = 0 := by
    intro c
    simp [hlb, constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ (hM0 c) l hl]
  have hA0 : ∀ c : ℂ_[p], MvPowerSeries.constantCoeff (add l ex (mulBy l ex c a) b) = 0 := by
    intro c
    exact constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ (hI0 c) ex hex
  have hA : CC fun c : ℂ_[p] => add l ex (mulBy l ex c a) b := by
    apply cc_subst ex hI0
    exact cc_add (cc_subst l hM0 hM) (cc_const _)
  have hB : CC fun c : ℂ_[p] => be l ex ph (mulBy l ex c a) b := by
    unfold be phAt
    exact cc_sub (cc_sub (cc_subst ph hA0 hA) (cc_subst ph hM0 hM)) (cc_const _)
  have hF : CC fun c : ℂ_[p] =>
      be l ex ph (mulBy l ex c a) b - MvPowerSeries.C c * be l ex ph a b :=
    cc_sub hB (cc_mul cc_C (cc_const _))
  have hE := cc_expMv' hF
  have hcl : IsClosed {c : ℂ_[p] | Simeq (be l ex ph (mulBy l ex c a) b)
      (MvPowerSeries.C c * be l ex ph a b)} := by
    simp only [Simeq, IntegralMv, IsIntP, Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter (isClosed_eq ?_ continuous_const)
      (isClosed_iInter fun α => isClosed_le (continuous_norm.comp (hE α)) continuous_const)
    exact (hF 0).congr fun c => MvPowerSeries.coeff_zero_eq_constantCoeff_apply _
  have hcl' := hcl.preimage zc_continuous'
  refine PadicInt.denseRange_natCast.induction_on n hcl' ?_
  intro k
  show Simeq _ _
  rw [zc_natCast']
  exact hN k

end PI.BiaddZpLinW
end
end

