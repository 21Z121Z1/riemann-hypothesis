import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0073
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TLPlanAsm
section
namespace Formalism.FourierDecayAlt.TL

open Finset MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

noncomputable section

open Classical

theorem act_e1Vec {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ}
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
    (M : Wd.SlopeTestRemainingChoices S (Q.Pr (Q.RadSp k r z z' π π'))) (Φ : Q.RadSp k r z z' π π') (e : Wd.Ix S) :
    P5.act M (Top.firstStateVector Φ) e = (M e e1).1 Φ := by
  unfold P5.act Top.firstStateVector
  rw [Finset.sum_eq_single (fun _ => 0)]
  · simp only [if_true]
    rfl
  · intro b _ hb
    rw [if_neg hb, map_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem topLiftOfParts : TopLiftOfParts := by
  intro hW hC hId hF hCap hA hX
  refine ⟨11, by norm_num, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 h1 h2 hD
  obtain ⟨hAH, hcst, hpoly⟩ := hA Wp Wq P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 hD
  obtain ⟨cm, c0, ca, cs, cmul⟩ := hC Wp Wq P Bs
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := hF Wp Wq P Bs X L hD.2.2.1
  have hx := hX Wp Wq P Bs X μ L st l0 hD
  have hS : LiftSys L st (2 * P.r + P.k + 1) (Lifts P Bs) :=
    { mono := fun h h' => cm _ _ _ _ _ h h'
      zero := c0
      add := ca _ _ _ _
      smul := fun z => cs _ _ _ z
      one := f1
      mul := cmul _ _ _ _ _ _
      fns := ⟨f2, f3, f4, f5, f6, f7, f8⟩
      x := fun Y _ => hx Y
      xi := fun Y hY _ => by
        obtain ⟨p, hp⟩ := hpoly Y hY
        rw [hp]
        have hpow : ∀ n : ℕ, Lifts P Bs 0 0 (st.x Y ^ n) := fun n => by
          induction n with
          | zero => rw [pow_zero]; exact f1
          | succ n ih => rw [pow_succ]; simpa using cmul _ _ _ _ _ _ ih (hx Y)
        refine Polynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)
        · rw [map_add]; exact ca _ _ _ _ hp hq
        · rw [Polynomial.aeval_monomial, ← Algebra.smul_def]; exact cs _ _ _ a (hpow n)
      cap := fun Y hY => by rw [← hcst Y hY]; exact hCap Wp Wq P Bs X μ L st l0 hD Y }
  have key : ∀ w : List C.Letter, KB.CutWord P l0 w → ∀ e : Wd.Ix (Fin w.length),
      Lifts P Bs (w.length * (2 * P.r + P.k + 1)) (11 * w.length * (P.r + 1) * (2 * P.r + P.k + 1))
        (((Fr.ofWord L st (D.positionted w)).F * P5.bTall L (D.positionted w)) e e1) := by
    intro w hw e
    have hok := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of P Bs.z Bs.z' Bs.π Bs.π' st l0 hD.1.1 h1 h2 hD.2.2.2.2.1 hD.2.2.2.2.2.1 w hw.1 hw.2
    have := hW _ (Fin w.length) P.r (2 * P.r + P.k + 1) L st (Lifts P Bs) (D.positionted w) hAH hS (by omega) hok.1 e
    have hl : (D.positionted w).length = w.length := by simp [D.positionted]
    rw [hl] at this
    exact this
  choose nf fib Dop hfib hIn hRad using key
  obtain ⟨D1, hD1, hD1'⟩ := hId P.k P.r Wp Wq Bs
  refine ⟨⟨fun w e F => if hw : w ≠ [] ∧ KB.CutWord P l0 w then B.opApply (Dop w hw.2 e) F else F,
    fun e F => by simp⟩, ?_, ?_⟩
  · intro w hw F hF Φ hΦ e
    rw [act_e1Vec]
    by_cases hn : w = []
    · subst hn
      have h1' : D.positionted ([] : List C.Letter) = [] := by simp [D.positionted]
      have h2' : P5.bTall L ([] : List (Wd.Letter ℂ (Fin ([] : List C.Letter).length))) = 1 := by
        simp [P5.bTall, P5.bTl, Wd.bT]
      simp only [ne_eq, not_true_eq_false, false_and, dite_false]
      rw [h1', h2', mul_one]
      have h3 : (Fr.ofWord L st ([] : List (Wd.Letter ℂ (Fin ([] : List C.Letter).length)))).F e e1 = 1 := by
        change (1 : Wd.SlopeTestRemainingChoices (Fin 0) _) e e1 = 1
        rw [Matrix.one_apply, if_pos (funext fun i => i.elim0)]
      rw [h3]
      exact hΦ
    · simp only [dif_pos (And.intro hn hw)]
      exact hRad w hw e F hF Φ hΦ
  · intro w hw e
    by_cases hn : w = []
    · subst hn
      refine ⟨0, fun j => j.elim0, 0, 0, D1, fun j => j.elim0, hD1, by simp, by simp, fun F g _ => ?_⟩
      simp only [ne_eq, not_true_eq_false, false_and, dite_false]
      rw [hD1']
    · refine ⟨nf w hw e, fib w hw e, _, _, Dop w hw e, hfib w hw e, hIn w hw e, ?_, ?_, fun F g _ => ?_⟩
      · push_cast; nlinarith [show (0 : ℝ) ≤ (w.length : ℝ) * (2 * P.r + P.k + 1) by positivity]
      · push_cast; exact le_of_eq (by ring)
      · simp only [dif_pos (And.intro hn hw)]

theorem isData_update {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : Q.ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Q.Pr (Q.RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Q.Pr (Q.RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hD : P5.IsData P z z' π π' X μ L st l0) (Y0 : ℂ) (hY : Y0 ∉ st.inv) (E : Q.Pr (Q.RadSp P.k P.r z z' π π'))
    (hE : ∀ g ∈ zfns L, Commute E g) :
    P5.IsData P z z' π π' X μ L { st with ee := Function.update st.ee Y0 E } l0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hD
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_⟩
  exact
    { start := h8.start
      lowerLeftEntry_commute := h8.lowerLeftEntry_commute
      x_xi := h8.x_xi
      x_commute := h8.x_commute
      x_fn := h8.x_fn
      x_nab := h8.x_nab
      x_star := h8.x_star
      ee_fn := by
        intro Y g hg
        by_cases hY0 : Y = Y0
        · simpa [Function.update_apply, hY0] using hE g hg
        · simpa [Function.update_apply, hY0] using h8.ee_fn Y g hg
      tau := h8.tau
      low := by
        intro Y hYi
        have hne : Y ≠ Y0 := fun h => hY (h ▸ hYi)
        simpa [Function.update_apply, hne] using h8.low Y hYi }

theorem p_pow_comm {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r) (l : Fin r) (m : ℕ) :
    ∀ g ∈ zfns L, Commute (L.p l ^ m) g := by
  intro g hg
  have h1 : Commute (L.p l) g := by
    simp only [Fr.zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact L.p_ζ l
    · exact L.p_ζi l
    · exact L.p_ζb l
    · exact L.p_ζbi l
    · exact L.p_GG l
    · exact L.p_GGi l
  exact h1.pow_left m

def P0 : M.Par := ⟨2, 1, 1, 1, fun i => if i = 0 then -2 else if i = 1 then 1 / 2 else -1 / 2,
  fun i => if i = 0 then 2 else if i = 1 then 1 / 2 else -1 / 2⟩

theorem base_parameters_ok : P0.OK := by
  refine ⟨by simp [P0], by simp [P0], by simp [P0], ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simp [P0, Finset.mem_Icc, Set.mem_Icc] at hi
      omega
    rcases hi' with rfl | rfl
    · exact ⟨0, by simp [P0]⟩
    · exact ⟨-1, by norm_num [P0]⟩
  · intro i hi
    have hi' : i = 1 ∨ i = 2 := by
      simp [P0, Finset.mem_Icc, Set.mem_Icc] at hi
      omega
    rcases hi' with rfl | rfl
    · exact ⟨0, by norm_num [P0]⟩
    · exact ⟨-1, by norm_num [P0]⟩
  · intro i hi
    have hi' : i = 1 := by
      simp [P0, Finset.mem_Icc, Set.mem_Icc] at hi
      omega
    subst hi'
    norm_num [P0, M.Par.lo, M.Par.hi]

theorem base_parameters_truncation_word : KB.CutWord P0 0 [(true, 0)] ∧ (0 : ℂ) ∉ {Y : ℂ | ∀ ρ : M.Ty P0, M.xC P0 ρ Y ≠ 0} := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a
    simp [I.OnCut, P0]
  · intro a b hab
    exfalso
    apply hab
    apply Fin.ext
    have ha := a.isLt
    have hb := b.isLt
    change _ < 1 at ha hb
    omega
  · simp only [Set.mem_setOf_eq, not_forall, not_not]
    refine ⟨fun _ => 0, ?_⟩
    unfold M.xC
    apply Finset.prod_eq_zero (i := 1)
    · simp [P0]
    · simp [M.rho, P0, M.Par.lo]
      norm_num

end

end Formalism.FourierDecayAlt.TL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.UwClosedSubgroup
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem castM_inv' {a b : ℕ} (h : a = b) (g : B.Mat k a) : D.castM h g⁻¹ = (D.castM h g)⁻¹ := by
  subst h
  simp [D.castM]

private theorem castV_rfl' {a : ℕ} (h : a = a) (v : Fin (2 * a + k + 1) → ℂ) : D.castV h v = v := by
  funext i
  rfl

theorem psi_castM {a b : ℕ} (h : a = b) (v : Fin (2 * a + k + 1) → ℂ) (c : ℂ) (g : B.Mat k a) :
    psi k b (D.castV h v) c (D.castM h g) = psi k a v c g := by
  subst h
  simp [D.castM, castV_rfl']

theorem castM_UH {a b : ℕ} (h : a = b) {g : B.Mat k a} (hg : g ∈ UH (Hpk k a)) : D.castM h g ∈ UH (Hpk k b) := by
  subst h
  simpa [D.castM] using hg

theorem castM_N {a b : ℕ} (h : a = b) {g : B.Mat k a} (hg : g ∈ Nset k a) : D.castM h g ∈ Nset k b := by
  subst h
  simpa [D.castM] using hg

theorem castM_UWv {a b : ℕ} (h : a = b) {v : Fin (2 * a + k + 1) → ℂ} {g : B.Mat k a} (hg : g ∈ UWset k a v) :
    D.castM h g ∈ UWset k b (D.castV h v) := by
  subst h
  simpa [D.castM, castV_rfl'] using hg

theorem castM_inj {a b : ℕ} (h : a = b) {g g' : B.Mat k a} (e : D.castM h g = D.castM h g') : g = g' := by
  subst h
  simpa [D.castM] using e

theorem castM_cont {a b : ℕ} (h : a = b) : Continuous (D.castM (k := k) h) := by
  subst h
  have e : (D.castM (k := k) (rfl : a = a)) = fun g => g := by
    funext g
    simp [D.castM]
  rw [e]
  exact continuous_id

theorem inWb_castV {a b : ℕ} (h : a = b) {v : Fin (2 * a + k + 1) → ℂ} (hv : inWb k a v) : inWb k b (D.castV h v) := by
  subst h
  rw [castV_rfl']
  exact hv

theorem uw_closedSubgroup (r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : B2.IsClosedSubgroup (UWset k r z) :=
  ⟨Dx2.Rad.one_UW z, fun _ ha _ hb => WeylGroupFacts.uw_mul ha hb, fun _ ha => WeylGroupFacts.uw_inv ha,
    fun _ ha => HermitianFormFactor.UH_unit (Ux3.hpk_det k r) ha.1, B6.isClosed_UWset k r z⟩

def levA (ρ : ℕ) (x : Mt k ρ) : Mt k (ρ + 1) :=
  Matrix.of.symm (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (Matrix.of x)))

private theorem continuous_ιLev_apply (ρ : ℕ) (p q : Fin (2 * (1 + ρ) + k + 1)) :
    Continuous fun x : Mt k ρ => ιLev k 1 ρ (Matrix.of x) p q := by
  simp only [Formalism.QuantumDeterminants.ιLev]
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * ρ + k + 1 + 1
  · by_cases hq : 1 ≤ q.val ∧ q.val < 2 * ρ + k + 1 + 1
    · simp only [dif_pos hp, dif_pos hq, Matrix.of_apply]
      exact (continuous_apply _).comp (continuous_apply _)
    · simp only [dif_pos hp, dif_neg hq]
      exact continuous_const
  · simp only [dif_neg hp]
    exact continuous_const

theorem levA_cont (ρ : ℕ) : Continuous (levA (k := k) ρ) := by
  apply continuous_pi
  intro p
  apply continuous_pi
  intro q
  simp only [levA, Matrix.of_symm_apply, D.castM, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact continuous_ιLev_apply ρ _ _

private theorem castM_mul_hermitian_curvature {a b : ℕ} (h : a = b) (g g' : B.Mat k a) :
    D.castM h (g * g') = D.castM h g * D.castM h g' := by
  subst h
  simp [D.castM]

theorem lev_mul' (ρ : ℕ) (a b : B.Mat k ρ) :
    D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (a * b)) =
      D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a) * D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ b) := by
  have hL := PI.QnLevBasicsW.level_group_homomorphism
  unfold Formalism.QuantumDeterminants.LevHom at hL
  rw [(hL k 1 ρ).2 a b]
  exact castM_mul_hermitian_curvature _ _ _

theorem castM_back {a b : ℕ} (h : a = b) (g : B.Mat k b) : D.castM h (D.castM h.symm g) = g := by
  subst h
  simp [D.castM]

theorem castV_back {a b : ℕ} (h : a = b) (v : Fin (2 * b + k + 1) → ℂ) : D.castV h (D.castV h.symm v) = v := by
  subst h
  rw [castV_rfl', castV_rfl']

theorem levA_apply (ρ : ℕ) (x : Mt k ρ) :
    (Matrix.of (levA ρ x) : B.Mat k (ρ + 1)) = D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (Matrix.of x)) := rfl

theorem lev_onto {ρ : ℕ} (z0 : Fin (2 * ρ + k + 1) → ℂ) (a : B.Mat k (ρ + 1))
    (ha : a ∈ UWset k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0))) :
    ∃ a0 ∈ UWset k ρ z0, D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0) = a := by
  have ha' : D.castM (Nat.add_comm 1 ρ).symm a ∈ UWset k (1 + ρ) (liftVec k 1 ρ z0) := by
    have := castM_UWv (Nat.add_comm 1 ρ).symm ha
    have e : D.castV (Nat.add_comm 1 ρ).symm (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) = liftVec k 1 ρ z0 := by
      have := castV_back (k := k) (Nat.add_comm 1 ρ).symm (liftVec k 1 ρ z0)
      simpa using this
    rwa [e] at this
  obtain ⟨y, hy, hy'⟩ := JCTx5.uw_onto (k := k) (i := 1) (r' := ρ) z0 _ ha'
  exact ⟨y, hy, by rw [hy']; exact castM_back _ a⟩

theorem muW_lev {ρ : ℕ} (z0 : Fin (2 * ρ + k + 1) → ℂ)
    (μ0 : Measure (Mt k ρ)) (μ1 : Measure (Mt k (ρ + 1)))
    (h0 : B.IsHaarOn (UWset k ρ z0) μ0)
    (h1 : B.IsHaarOn (UWset k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0))) μ1)
    (n0 : μ0 Set.univ = 1) (n1 : μ1 Set.univ = 1) :
    μ1 = μ0.map (levA ρ) := by
  set U1 := UWset k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) with hU1
  have hm : Measurable (levA (k := k) ρ) := (levA_cont ρ).measurable
  have hmem : ∀ y ∈ UWset k ρ z0, (Matrix.of (levA ρ y) : B.Mat k (ρ + 1)) ∈ U1 := fun y hy =>
    castM_UWv _ (Dx2.Tower.lev_UW 1 ρ z0 (Matrix.of y) hy)
  set ν := μ0.map (levA (k := k) ρ) with hν
  have hνu : ν Set.univ = 1 := by rw [hν, Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, n0]
  have hconc : ν U1ᶜ = 0 := by
    have hcl : IsClosed {x : Mt k (ρ + 1) | Matrix.of x ∈ U1} := B7.isClosed_UW _
    show ν {x : Mt k (ρ + 1) | Matrix.of x ∈ U1}ᶜ = 0
    rw [hν, Measure.map_apply hm hcl.measurableSet.compl]
    apply measure_mono_null _ h0.conc
    intro y hy hyU
    exact hy (hmem y hyU)
  have hleft : ∀ a ∈ U1, ν.map (lmulM a) = ν := by
    intro a ha
    obtain ⟨a0, ha0, rfl⟩ := lev_onto z0 a ha
    have hl : Measurable (lmulM (k := k) (r := ρ + 1) (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0))) :=
      B2x5.measurable_lmulM _
    have hl0 : Measurable (lmulM (k := k) (r := ρ) a0) := B2x5.measurable_lmulM _
    have e : lmulM (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0)) ∘ levA (k := k) ρ = levA ρ ∘ lmulM a0 := by
      funext x
      show (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ a0) * D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (Matrix.of x)) :
          B.Mat k (ρ + 1)) = D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ (a0 * Matrix.of x))
      rw [lev_mul']
    rw [hν, Measure.map_map hl hm, e, ← Measure.map_map hm hl0, h0.left a0 ha0]
  have hfin : ∀ K : Set (Mt k (ρ + 1)), IsCompact K → ν K < ⊤ := by
    intro K _
    calc ν K ≤ ν Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := hνu
      _ < ⊤ := ENNReal.one_lt_top
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k (ρ + 1) U1 μ1 ν (uw_closedSubgroup (ρ + 1) _) h1 hconc hleft hfin
  have hc1 : (c : ENNReal) = 1 := by
    have := congrArg (fun μ : Measure (Mt k (ρ + 1)) => μ Set.univ) hc
    simp only [Measure.smul_apply, n1, hνu, smul_eq_mul, mul_one, ENNReal.smul_def] at this
    exact this.symm
  have hc1' : c = 1 := by exact_mod_cast hc1
  rw [hc, hc1', one_smul]

def Qm (ρ : ℕ) (p : Mt k (1 + ρ) × Mt k ρ) : Mt k (ρ + 1) :=
  Matrix.of.symm (D.castM (Nat.add_comm 1 ρ) (Matrix.of p.1 * ιLev k 1 ρ (Matrix.of p.2)))

theorem Qm_cont (ρ : ℕ) : Continuous (Qm (k := k) ρ) := by
  have hI : Continuous fun p : Mt k (1 + ρ) × Mt k ρ => ιLev k 1 ρ (Matrix.of p.2) :=
    continuous_pi fun a => continuous_pi fun b => (continuous_ιLev_apply ρ a b).comp continuous_snd
  have h1 : Continuous fun p : Mt k (1 + ρ) × Mt k ρ => (Matrix.of p.1 : B.Mat k (1 + ρ)) := continuous_fst
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [Qm, Matrix.of_symm_apply, D.castM, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact (continuous_apply _).comp ((continuous_apply _).comp (h1.matrix_mul hI))

theorem sf_heis (ρ : ℕ) : SigmaFinite (B2.μHeis k ρ) :=
  Dx2.MN.sigma_of_haar (Formalism.FourierDecayAlt.P.heisenberg_haar_measure k ρ)

theorem sf_muN (ρ : ℕ) : SigmaFinite (D.muN k ρ) := Dx2.MN.sigma_of_haar (Dx2.MN.haar ρ)

theorem muN_succ' (ρ : ℕ) : D.muN k (ρ + 1) = ((B2.μHeis k ρ).prod (D.muN k ρ)).map (Qm ρ) := by
  have := sf_heis (k := k) ρ
  have := sf_muN (k := k) ρ
  have hl : Measurable (B2.levM k ρ) := (B2x2.levM_cont k ρ).measurable
  have hmu : Measurable (B2.mulM : Mt k (1 + ρ) × Mt k (1 + ρ) → Mt k (1 + ρ)) := B2x2.mulM_cont.measurable
  have hc : Measurable (Dx2.MN.castMt (k := k) (Nat.add_comm 1 ρ)) := (Dx2.MN.castMt_cont _).measurable
  have e1 : (B2.μHeis k ρ).prod ((D.muN k ρ).map (B2.levM k ρ)) =
      ((B2.μHeis k ρ).prod (D.muN k ρ)).map (Prod.map id (B2.levM k ρ)) := by
    rw [← Measure.map_prod_map _ _ measurable_id hl, Measure.map_id]
  rw [Dx2.MN.muN_succ, e1, Measure.map_map hmu (measurable_id.prodMap hl), Measure.map_map hc (hmu.comp (measurable_id.prodMap hl))]
  rfl

end Formalism.FourierDecayAlt.P.PBH
end
end

