import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0113
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0115
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftDerivativeCurves
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvScal
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Polynomial

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvScal

noncomputable section

theorem pl_monic (s : Finset ℕ) (f : ℕ → ℂ) : (∏ i ∈ s, (X + C (f i))).Monic :=
  monic_prod_of_monic _ _ (fun i _ => monic_X_add_C (f i))

theorem pl_natDegree (s : Finset ℕ) (f : ℕ → ℂ) : (∏ i ∈ s, (X + C (f i))).natDegree = s.card := by
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C (f i))]
  simp [natDegree_X_add_C]

theorem pl_top (s : Finset ℕ) (f : ℕ → ℂ) : (∏ i ∈ s, (X + C (f i))).coeff s.card = 1 := by
  have h := (pl_monic s f).coeff_natDegree
  rwa [pl_natDegree] at h

theorem pl_next (s : Finset ℕ) (f : ℕ → ℂ) (hs : 0 < s.card) :
    (∏ i ∈ s, (X + C (f i))).coeff (s.card - 1) = ∑ i ∈ s, f i := by
  have h := nextCoeff_of_natDegree_pos (p := ∏ i ∈ s, (X + C (f i))) (by rw [pl_natDegree]; exact hs)
  rw [pl_natDegree] at h
  rw [← h, Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C (f i))]
  simp [nextCoeff_X_add_C]

theorem pl_high (s : Finset ℕ) (f : ℕ → ℂ) {j : ℕ} (hj : s.card < j) : (∏ i ∈ s, (X + C (f i))).coeff j = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rw [pl_natDegree]; exact hj)

theorem top2 (p : ℂ[X]) (N : ℕ) (h : p.natDegree < N + 2) (u : ℂ) :
    p.eval u = u ^ (N + 1) * p.coeff (N + 1) + u ^ N * p.coeff N + ∑ i ∈ Finset.range N, u ^ i * p.coeff i := by
  rw [eval_eq_sum_range' h, Finset.sum_range_succ, Finset.sum_range_succ]
  have : ∀ i, p.coeff i * u ^ i = u ^ i * p.coeff i := fun i => mul_comm _ _
  simp only [this]
  ring

theorem card_Icc_one (n : ℕ) : (Finset.Icc 1 n).card = n := by simp

theorem xC_leading_terms_alt (P : M.Par) (m : ℕ) (hm : P.k = m + 2) (ρ : M.Ty P) :
    ∃ c : ℕ → ℂ, ∀ u : ℂ, M.xC P ρ u = u ^ (P.k - 1) + (absTy P ρ : ℂ) * u ^ (P.k - 2) +
        ∑ i ∈ Finset.range (P.k - 2), u ^ i * c i := by
  have h1 : P.k - 1 = m + 1 := by omega
  have h2 : P.k - 2 = m := by omega
  let f : ℕ → ℂ := fun i => ((M.rho P ρ i : ℝ) : ℂ)
  refine ⟨fun i => (∏ i ∈ Finset.Icc 1 (m + 1), (X + C (f i))).coeff i, fun u => ?_⟩
  have hx : M.xC P ρ u = (∏ i ∈ Finset.Icc 1 (m + 1), (X + C (f i))).eval u := by
    rw [eval_prod]; unfold M.xC; rw [h1]; simp [f]
  rw [hx, top2 _ m (by rw [pl_natDegree, card_Icc_one]; omega) u, h1, h2]
  have ht := pl_top (Finset.Icc 1 (m + 1)) f
  have hn := pl_next (Finset.Icc 1 (m + 1)) f (by rw [card_Icc_one]; omega)
  rw [card_Icc_one] at ht hn
  rw [Nat.add_sub_cancel] at hn
  rw [ht, hn]
  have ha : (absTy P ρ : ℂ) = ∑ i ∈ Finset.Icc 1 (m + 1), f i := by
    simp only [absTy, h1, f]; push_cast; rfl
  rw [ha]; ring

theorem part_ex (P : M.Par) (m : ℕ) (hm : P.k = m + 2) (ρ : M.Ty P) (ex : Finset ℕ)
    (hex : ∃ l ∈ ex, l ∈ Finset.Icc 1 (P.k - 1)) :
    ∃ c : ℕ → ℂ, ∀ u : ℂ, M.xEx P ex ρ u = ∑ i ∈ Finset.range (P.k - 1), u ^ i * c i := by
  have h1 : P.k - 1 = m + 1 := by omega
  let f : ℕ → ℂ := fun i => ((M.rho P ρ i : ℝ) : ℂ)
  let s := Finset.Icc 1 (m + 1) \ ex
  have hs : s.card < m + 1 := by
    obtain ⟨l, hl, hlI⟩ := hex
    rw [h1] at hlI
    have hss : s ⊂ Finset.Icc 1 (m + 1) :=
      (Finset.ssubset_iff_of_subset Finset.sdiff_subset).2 ⟨l, hlI, by simp [s, hl]⟩
    have := Finset.card_lt_card hss
    rwa [card_Icc_one] at this
  refine ⟨fun i => (∏ i ∈ s, (X + C (f i))).coeff i, fun u => ?_⟩
  have hx : M.xEx P ex ρ u = (∏ i ∈ s, (X + C (f i))).eval u := by
    rw [eval_prod]; unfold M.xEx; rw [h1]; simp [f, s]
  rw [hx, eval_eq_sum_range' (by rw [pl_natDegree]; omega) u, h1]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem part_w (P : M.Par) (m : ℕ) (hm : P.k = m + 2) (ρ : M.Ty P) :
    ∃ c : ℕ → ℂ, ∀ u : ℂ, M.wC P ρ u = u ^ (P.k + 1) * (-(P.TT : ℂ)) +
        u ^ P.k * ((P.TT : ℂ) * ((absTy P ρ : ℂ) - 1 - sumU P)) + ∑ i ∈ Finset.range P.k, u ^ i * c i := by
  have h1 : P.k - 1 = m + 1 := by omega
  let fx : ℕ → ℂ := fun i => ((M.rho P ρ i : ℝ) : ℂ) + 1
  let xp := ∏ i ∈ Finset.Icc 1 (m + 1), (X + C (fx i))
  have hxp : M.coordinatePolynomial P ρ = xp := by unfold M.coordinatePolynomial; rw [h1]
  have xmon : xp.Monic := pl_monic _ _
  have xdeg : xp.natDegree = m + 1 := by rw [pl_natDegree, card_Icc_one]
  have xtop : xp.coeff (m + 1) = 1 := by
    have := pl_top (Finset.Icc 1 (m + 1)) fx; rwa [card_Icc_one] at this
  have xnext : xp.coeff m = ∑ i ∈ Finset.Icc 1 (m + 1), fx i := by
    have := pl_next (Finset.Icc 1 (m + 1)) fx (by rw [card_Icc_one]; omega)
    rwa [card_Icc_one, Nat.add_sub_cancel] at this
  have xhigh : xp.coeff (m + 2) = 0 := pl_high _ _ (by rw [card_Icc_one]; omega)
  let fa : ℕ → ℂ := fun i => 1 / 2 + (P.u i : ℂ)
  let fb : ℕ → ℂ := fun i => 1 / 2 + (P.u' i : ℂ)
  let pa := ∏ i ∈ Finset.Icc 1 (m + 2), (X + C (fa i))
  let pb := ∏ i ∈ Finset.Icc 1 (m + 2), (X + C (fb i))
  have hT : (-((P.T : ℂ) * (P.T' : ℂ))) = -(P.TT : ℂ) := by simp [M.Par.TT]
  have hq : M.qP P = C (-(P.TT : ℂ)) * (pa * pb) := by
    unfold M.qP; rw [hm, Finset.prod_mul_distrib, hT]
  have abmon : (pa * pb).Monic := (pl_monic _ _).mul (pl_monic _ _)
  have abdeg : (pa * pb).natDegree = 2 * m + 4 := by
    rw [(pl_monic _ _).natDegree_mul (pl_monic _ _), pl_natDegree, pl_natDegree, card_Icc_one]; ring
  have abtop : (pa * pb).coeff (2 * m + 4) = 1 := by rw [← abdeg]; exact abmon.coeff_natDegree
  have abnext : (pa * pb).coeff (2 * m + 3) =
      ∑ i ∈ Finset.Icc 1 (m + 2), fa i + ∑ i ∈ Finset.Icc 1 (m + 2), fb i := by
    have h := nextCoeff_of_natDegree_pos (p := pa * pb) (by rw [abdeg]; omega)
    rw [abdeg, show 2 * m + 4 - 1 = 2 * m + 3 by omega] at h
    rw [← h, (pl_monic _ _).nextCoeff_mul (pl_monic _ _),
      Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C (fa i)),
      Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C (fb i))]
    simp only [nextCoeff_X_add_C]
  let NS : ℂ[X] := ∑ l ∈ Finset.Icc 1 (m + 1), C ((M.Nrm P l ρ : ℝ) : ℂ) *
    ((∏ j ∈ (Finset.Icc 1 (m + 1)).erase l, (X + C ((M.rho P ρ j : ℝ) : ℂ))) *
      ∏ j ∈ (Finset.Icc 1 (m + 1)).erase l, (X + C (((M.rho P ρ j : ℝ) : ℂ) + 1)))
  have hw : M.wNum P ρ = M.qP P + NS := by unfold M.wNum; rw [h1]
  have nsdeg : NS.natDegree ≤ 2 * m + 2 := by
    apply natDegree_sum_le_of_forall_le
    intro l hl
    refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
    have hc : ((Finset.Icc 1 (m + 1)).erase l).card = m := by
      rw [Finset.card_erase_of_mem hl, card_Icc_one]; omega
    have e1 := pl_natDegree ((Finset.Icc 1 (m + 1)).erase l) (fun j => ((M.rho P ρ j : ℝ) : ℂ))
    have e2 := pl_natDegree ((Finset.Icc 1 (m + 1)).erase l) (fun j => ((M.rho P ρ j : ℝ) : ℂ) + 1)
    rw [e1, e2, hc]; omega
  let c0 : ℂ := (P.TT : ℂ) * ((absTy P ρ : ℂ) - 1 - sumU P)
  let Q0 : ℂ[X] := C (-(P.TT : ℂ)) * X ^ (m + 3) + C c0 * X ^ (m + 2)
  let G : ℂ[X] := M.wNum P ρ - xp * Q0
  have e_xQ : xp * Q0 = C (-(P.TT : ℂ)) * (xp * X ^ (m + 3)) + C c0 * (xp * X ^ (m + 2)) := by
    simp only [Q0]; ring
  have c4a : (xp * X ^ (m + 3)).coeff (2 * m + 4) = 1 := by
    rw [show 2 * m + 4 = (m + 1) + (m + 3) by ring, coeff_mul_X_pow, xtop]
  have c4b : (xp * X ^ (m + 2)).coeff (2 * m + 4) = 0 := by
    rw [show 2 * m + 4 = (m + 2) + (m + 2) by ring, coeff_mul_X_pow, xhigh]
  have c3a : (xp * X ^ (m + 3)).coeff (2 * m + 3) = xp.coeff m := by
    rw [show 2 * m + 3 = m + (m + 3) by ring, coeff_mul_X_pow]
  have c3b : (xp * X ^ (m + 2)).coeff (2 * m + 3) = 1 := by
    rw [show 2 * m + 3 = (m + 1) + (m + 2) by ring, coeff_mul_X_pow, xtop]
  have Q0deg : (xp * Q0).natDegree ≤ 2 * m + 4 := by
    refine natDegree_mul_le.trans ?_
    rw [xdeg]
    have : Q0.natDegree ≤ m + 3 := (natDegree_add_le _ _).trans
      (max_le (natDegree_C_mul_X_pow_le _ _) ((natDegree_C_mul_X_pow_le _ _).trans (by omega)))
    omega
  have qdeg : (M.qP P).natDegree ≤ 2 * m + 4 := by
    rw [hq]; exact (natDegree_C_mul_le _ _).trans abdeg.le
  have hA : (absTy P ρ : ℂ) = ∑ i ∈ Finset.Icc 1 (m + 1), ((M.rho P ρ i : ℝ) : ℂ) := by
    simp only [absTy, h1]; push_cast; rfl
  have hS : sumU P = ∑ i ∈ Finset.Icc 1 (m + 2), (P.u i : ℂ) + ∑ i ∈ Finset.Icc 1 (m + 2), (P.u' i : ℂ) := by
    simp only [sumU, hm, Finset.sum_add_distrib]
  have Gdeg : G.natDegree ≤ 2 * m + 2 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    simp only [G, hw, coeff_sub, coeff_add]
    rw [coeff_eq_zero_of_natDegree_lt (p := NS) (by omega), add_zero]
    rcases (show N = 2 * m + 3 ∨ N = 2 * m + 4 ∨ 2 * m + 4 < N by omega) with h | h | h
    · subst h
      rw [e_xQ, coeff_add, coeff_C_mul, coeff_C_mul, c3a, c3b, xnext, hq, coeff_C_mul, abnext]
      simp only [fa, fb, fx, c0, hA, hS, Finset.sum_add_distrib, Finset.sum_const, card_Icc_one, nsmul_eq_mul]
      push_cast
      ring
    · subst h
      rw [e_xQ, coeff_add, coeff_C_mul, coeff_C_mul, c4a, c4b, hq, coeff_C_mul, abtop]; ring
    · rw [coeff_eq_zero_of_natDegree_lt (by omega : (M.qP P).natDegree < N),
        coeff_eq_zero_of_natDegree_lt (by omega : (xp * Q0).natDegree < N)]; ring
  have hG := modByMonic_add_div G xp
  have hdiv : M.wNum P ρ /ₘ xp = Q0 + G /ₘ xp := by
    refine (div_modByMonic_unique (Q0 + G /ₘ xp) (G %ₘ xp) xmon ⟨?_, degree_modByMonic_lt _ xmon⟩).1
    calc G %ₘ xp + xp * (Q0 + G /ₘ xp) = xp * Q0 + (G %ₘ xp + xp * (G /ₘ xp)) := by ring
      _ = xp * Q0 + G := by rw [hG]
      _ = M.wNum P ρ := by simp only [G]; ring
  have Gq : (G /ₘ xp).natDegree < m + 2 := by rw [natDegree_divByMonic _ xmon, xdeg]; omega
  refine ⟨fun i => (G /ₘ xp).coeff i, fun u => ?_⟩
  unfold M.wC
  rw [hxp, hdiv, eval_add, eval_eq_sum_range' Gq u, hm]
  simp only [Q0, c0, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  have : ∀ i, (G /ₘ xp).coeff i * u ^ i = u ^ i * (G /ₘ xp).coeff i := fun i => mul_comm _ _
  simp only [this]
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvScal

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem curvature_scalar_holds : GTCCurvScal := by
  intro P hk ρ
  obtain ⟨m, hm⟩ : ∃ m, P.k = m + 2 := ⟨P.k - 2, by omega⟩
  exact ⟨CurvScal.part_w P m hm ρ, CurvScal.xC_leading_terms_alt P m hm ρ, fun ex hex => CurvScal.part_ex P m hm ρ ex hex⟩

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTAsmA
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTA

noncomputable section

open Classical

def Ann {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) : Set ℂ := {ζ | Tz k r z * Tz k r z' < Complex.normSq ζ}

theorem ann_open {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (Ann z z') :=
  isOpen_lt continuous_const Complex.continuous_normSq

theorem exists_pr {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) :
    ∃ Pr : V →ₗ[ℂ] V, (∀ x, Pr x ∈ S) ∧ ∀ x ∈ S, Pr x = x := by
  obtain ⟨q, hq⟩ := S.exists_isCompl
  refine ⟨S.subtype ∘ₗ S.linearProjOfIsCompl q hq, fun x => (S.linearProjOfIsCompl q hq x).2, fun x hx => ?_⟩
  exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hq ⟨x, hx⟩)

def e2 : Fin 2 → ℂ := ![1, Complex.I]

def crd : Fin 2 → (ℂ →L[ℝ] ℝ) := ![Complex.reCLM, Complex.imCLM]

theorem sum_crd (v : ℂ) : ∑ t : Fin 2, crd t v • e2 t = v := by
  simp only [Fin.sum_univ_two, crd, e2, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.reCLM_apply, Complex.imCLM_apply, Complex.real_smul, mul_one]
  exact Complex.re_add_im v

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ml_expand {j : ℕ} (m : ContinuousMultilinearMap ℝ (fun _ : Fin j => ℂ) E) (v : ℂ) :
    m (fun _ => v) = ∑ s : Fin j → Fin 2, (∏ i, crd (s i) v) • m (fun i => e2 (s i)) := by
  have h : (fun _ : Fin j => v) = fun _ => ∑ t : Fin 2, crd t v • e2 t := funext fun _ => (sum_crd v).symm
  rw [h, m.map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact m.map_smul_univ (fun i => crd (s i) v) (fun i => e2 (s i))

end

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def fibS (z z' : Fin (2 * r + k + 1) → ℂ) (μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (ζ : ℂ) : Submodule ℂ (Wq →L[ℂ] Wp) where
  carrier := NF.Fib k r z z' μs π π' ζ
  add_mem' := by
    intro X X' hX hX' p hp
    rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hX p hp, hX' p hp]
  zero_mem' := by
    intro p _
    simp
  smul_mem' := by
    intro s X hX p hp
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hX p hp]

theorem radR_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (Φ : Q.Fn k r E) {q : (Fin r → ℂ) × ℂ}
    (hq : q ∈ NF.QR k r z z') : NF.radR k r z z' μs Φ q = Φ q.1 (NF.muZ k r μs q.2) := by
  unfold NF.radR
  rw [Set.indicator_of_mem hq]

theorem radR_add {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (Φ Ψ : Q.Fn k r E) :
    NF.radR k r z z' μs (Φ + Ψ) = NF.radR k r z z' μs Φ + NF.radR k r z z' μs Ψ := by
  funext q
  unfold NF.radR
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [hq]

theorem radR_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (Φ Ψ : Q.Fn k r E) :
    NF.radR k r z z' μs (Φ - Ψ) = NF.radR k r z z' μs Φ - NF.radR k r z z' μs Ψ := by
  funext q
  unfold NF.radR
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [hq]

theorem radR_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (s : ℂ) (Φ : Q.Fn k r E) :
    NF.radR k r z z' μs (s • Φ) = s • NF.radR k r z z' μs Φ := by
  funext q
  unfold NF.radR
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [hq]

theorem radR_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z z' : Fin (2 * r + k + 1) → ℂ}
    {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} :
    NF.radR k r z z' μs (0 : Q.Fn k r E) = 0 := by
  funext q
  unfold NF.radR
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [hq]

end

end

noncomputable section

open Classical

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * r + k + 1) → ℂ} {μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
  {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}
  {Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)}

def phiP (z z' : Fin (2 * r + k + 1) → ℂ) (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)) (p : ℂ → (Wq →L[ℂ] Wp)) :
    (Fin r → ℂ) × ℂ → (Wq →L[ℂ] Wp) :=
  (NF.QR k r z z').indicator fun q => Pr (p q.2)

def Gd (z z' : Fin (2 * r + k + 1) → ℂ) (μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)) : Prop :=
  NF.RadBase k r z z' μs π π' ∧ ∀ x, ∀ ζ ∈ Ann z z', Pr x ∈ NF.Fib k r z z' μs π π' ζ

theorem pr_contDiff (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp)) : ContDiff ℝ ∞ (fun x => Pr x) :=
  (LinearMap.toContinuousLinearMap (Pr.restrictScalars ℝ)).contDiff

theorem phiP_mem (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) :
    phiP z z' Pr p ∈ NF.RadSec k r z z' μs π π' := by
  refine ⟨?_, fun q hq => ?_, fun q hq => ?_⟩
  · refine ((pr_contDiff Pr).comp (hp.comp contDiff_snd)).contDiffOn.congr fun q hq => ?_
    simp only [phiP, Set.indicator_of_mem hq, Function.comp]
  · simp only [phiP, Set.indicator_of_mem hq]
    exact hG.2 _ _ hq.2
  · simp only [phiP, Set.indicator_of_notMem hq]

def PhiP (z z' : Fin (2 * r + k + 1) → ℂ) (μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp))
    (p : ℂ → (Wq →L[ℂ] Wp)) : Q.RadSp k r z z' π π' :=
  if h : Gd z z' μs π π' Pr ∧ ContDiff ℝ ∞ p then
    ⟨Classical.choose (Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq k r z z' μs π π' h.1.1 (phiP z z' Pr p)
      (phiP_mem h.1 h.2)),
     (Classical.choose_spec (Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq k r z z' μs π π' h.1.1 (phiP z z' Pr p)
      (phiP_mem h.1 h.2))).1⟩
  else 0

theorem radR_PhiP (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) :
    NF.radR k r z z' μs ((PhiP z z' μs π π' Pr p : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) =
      phiP z z' Pr p := by
  unfold PhiP
  rw [dif_pos ⟨hG, hp⟩]
  exact (Classical.choose_spec (Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq k r z z' μs π π' hG.1 (phiP z z' Pr p)
      (phiP_mem hG hp))).2

theorem eq_of_radR (hG : Gd z z' μs π π' Pr) {Φ Ψ : Q.RadSp k r z z' π π'}
    (h : NF.radR k r z z' μs (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) = NF.radR k r z z' μs (Ψ : Q.Fn k r (Wq →L[ℂ] Wp))) :
    Φ = Ψ :=
  Subtype.ext (Formalism.FourierDecayAlt.P.radical_reduction_injective Wp Wq k r z z' μs π π' hG.1 Φ Φ.2 Ψ Ψ.2 h)

theorem PhiP_add (hG : Gd z z' μs π π' Pr) {p p' : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p)
    (hp' : ContDiff ℝ ∞ p') :
    PhiP z z' μs π π' Pr (fun ζ => p ζ + p' ζ) = PhiP z z' μs π π' Pr p + PhiP z z' μs π π' Pr p' := by
  refine eq_of_radR hG ?_
  rw [radR_PhiP hG (hp.add hp'), Submodule.coe_add, radR_add, radR_PhiP hG hp, radR_PhiP hG hp']
  funext q
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [phiP, hq]

theorem PhiP_smul (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) (s : ℂ) :
    PhiP z z' μs π π' Pr (fun ζ => s • p ζ) = s • PhiP z z' μs π π' Pr p := by
  refine eq_of_radR hG ?_
  rw [radR_PhiP hG (hp.const_smul s), Submodule.coe_smul, radR_smul, radR_PhiP hG hp]
  funext q
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [phiP, hq]

theorem PhiP_zero (hG : Gd z z' μs π π' Pr) : PhiP z z' μs π π' Pr (fun _ => 0) = 0 := by
  refine eq_of_radR hG ?_
  rw [radR_PhiP hG contDiff_const, Submodule.coe_zero, radR_zero]
  funext q
  by_cases hq : q ∈ NF.QR k r z z' <;> simp [phiP, hq]

def VV (z z' : Fin (2 * r + k + 1) → ℂ) (μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (Pr : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp))
    (T : Module.End ℂ (Q.RadSp k r z z' π π')) (c0 : Fin r → ℂ) (p : ℂ → (Wq →L[ℂ] Wp)) (ζ : ℂ) : Wq →L[ℂ] Wp :=
  NF.radR k r z z' μs ((T (PhiP z z' μs π π' Pr p) : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) (c0, ζ)

variable {T : Module.End ℂ (Q.RadSp k r z z' π π')} {c0 : Fin r → ℂ}

theorem VV_add (hG : Gd z z' μs π π' Pr) {p p' : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p)
    (hp' : ContDiff ℝ ∞ p') (ζ : ℂ) :
    VV z z' μs π π' Pr T c0 (fun ζ => p ζ + p' ζ) ζ = VV z z' μs π π' Pr T c0 p ζ + VV z z' μs π π' Pr T c0 p' ζ := by
  unfold VV
  rw [PhiP_add hG hp hp', map_add, Submodule.coe_add, radR_add]
  rfl

theorem VV_smul (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) (s : ℂ) (ζ : ℂ) :
    VV z z' μs π π' Pr T c0 (fun ζ => s • p ζ) ζ = s • VV z z' μs π π' Pr T c0 p ζ := by
  unfold VV
  rw [PhiP_smul hG hp, map_smul, Submodule.coe_smul, radR_smul]
  rfl

theorem VV_smulR (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hp : ContDiff ℝ ∞ p) (s : ℝ) (ζ : ℂ) :
    VV z z' μs π π' Pr T c0 (fun ζ => s • p ζ) ζ = s • VV z z' μs π π' Pr T c0 p ζ := by
  have h := VV_smul (T := T) (c0 := c0) hG hp (s : ℂ) ζ
  simp only [Complex.coe_smul] at h
  exact h

theorem VV_zero (hG : Gd z z' μs π π' Pr) (ζ : ℂ) : VV z z' μs π π' Pr T c0 (fun _ => 0) ζ = 0 := by
  unfold VV
  rw [PhiP_zero hG, map_zero, Submodule.coe_zero, radR_zero]
  rfl

theorem VV_sum (hG : Gd z z' μs π π' Pr) {ι : Type} (s : Finset ι) (p : ι → ℂ → (Wq →L[ℂ] Wp))
    (hp : ∀ i, ContDiff ℝ ∞ (p i)) (ζ : ℂ) :
    VV z z' μs π π' Pr T c0 (fun ζ => ∑ i ∈ s, p i ζ) ζ = ∑ i ∈ s, VV z z' μs π π' Pr T c0 (p i) ζ := by
  induction s using Finset.induction_on with
  | empty => simpa using VV_zero (T := T) (c0 := c0) hG ζ
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [VV_add hG (hp i) (ContDiff.sum fun j _ => hp j), ih]

theorem VV_smooth (hG : Gd z z' μs π π' Pr) {p : ℂ → (Wq →L[ℂ] Wp)} (hc0 : c0 ∈ OmX r) :
    ContDiffOn ℝ ∞ (VV z z' μs π π' Pr T c0 p) (Ann z z') := by
  have hm := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq k r z z' μs π π' hG.1
    ((T (PhiP z z' μs π π' Pr p) : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp))
    (T (PhiP z z' μs π π' Pr p)).2
  exact hm.1.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun ζ hζ => ⟨hc0, hζ⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.RadTA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPLeftCov
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

theorem rdV_leftCov {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z))
    {D : Set (Q.Mx k r)} {F : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hF : ∀ h ∈ UWset k r z, ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, F (h * g) = (π h).comp (F g))
    {μ : Q.Mx k r} (hμ : μ ∈ Q.Glev k r (Fin.last r) ∩ D) {X : Q.Mx k r} (hX : P.QrD.InLieW k r z X) :
    RdV (μ⁻¹ * X * μ) F μ = (P.QrD.dOp π X).comp (F μ) := by
  have hU : μᴴ * Hpk k r * μ = Hpk k r := hμ.1.1
  have hdet : IsUnit μ.det := by
    apply Matrix.isUnit_det_of_left_inverse (B := Hpk k r * μᴴ * Hpk k r)
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc μᴴ, hU, Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  have hμu : IsUnit μ := (Matrix.isUnit_iff_isUnit_det μ).mpr hdet
  have key : ∀ t : ℝ, F (μ * NormedSpace.exp ((t : ℂ) • (μ⁻¹ * X * μ))) =
      (π (NormedSpace.exp ((t : ℂ) • X))).comp (F μ) := by
    intro t
    rw [show (t : ℂ) • (μ⁻¹ * X * μ) = μ⁻¹ * ((t : ℂ) • X) * μ by rw [Matrix.mul_smul, Matrix.smul_mul],
      Matrix.exp_conj' μ _ hμu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
    exact hF _ (Formalism.FourierDecayAlt.P.QrD.exp_uw hX t) μ hμ
  unfold Formalism.REAL.RdV
  simp only [key]
  let L : (Wp →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
    ((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip (F μ)).restrictScalars ℝ
  have hL : ∀ A, L A = A.comp (F μ) := fun A => rfl
  have hd : HasDerivAt (fun t : ℝ => L (π (NormedSpace.exp ((t : ℂ) • X)))) (L (P.QrD.dOp π X)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 (Formalism.FourierDecayAlt.P.QrD.dOp_hasDeriv hπ hc hX)
  simp only [hL] at hd
  exact hd.deriv

theorem left_covariance_holds : LeftCov := by
  intro k r z Wp Wq _ _ _ _ _ _ π hπ hc _ D F _ _ _ hF μ hμ B hB
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [P.LeftDerivativeCurves.hpart1_conj hμ.1.1]
    exact P.LeftDerivativeCurves.lie_conj hμ.1 hB.1.1
  · rw [P.LeftDerivativeCurves.hpart2_conj hμ.1.1]
    exact P.LeftDerivativeCurves.lie_conj hμ.1 hB.2.1
  · unfold Rc P.QrD.ecOp
    rw [P.LeftDerivativeCurves.hpart1_conj hμ.1.1, P.LeftDerivativeCurves.hpart2_conj hμ.1.1, rdV_leftCov hπ hc hF hμ hB.1,
      rdV_leftCov hπ hc hF hμ hB.2]
    ext v
    simp

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPRcComm
section
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_coefficient_commutation : RcComm := by
  intro k r E _ _ D f _ hf Z₁ Z₂ h₁ h₂ g hg
  exact Qx5.RZ_comm hf hg h₁ h₂

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

