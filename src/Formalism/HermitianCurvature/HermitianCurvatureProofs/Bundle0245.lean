import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0160
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0238
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0214
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0053
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteTransposedRMatrix
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0036
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0235
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.GramSchmidtFramesLocal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.LocBCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.XiHermitianCofactorDet
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.HmSelfRe

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PTieUL
section
open Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTieUL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.PTieB Formalism.FourierDecayAlt.P.PTieL

theorem lev_indU {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π')
    (X : ActualOps P.k P.r T.base.z T.base.z' T.base.π T.base.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π'))) (l0 : ℕ)
    (hD : P5.IsData P T.base.z T.base.z' T.base.π T.base.π' X μ L st l0) :
    ∀ (j : ℕ) (hj : j ≤ P.r),
    ∃ (Xj : ActualOps (JC.parLev P j).k (JC.parLev P j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
      (μj : Measure (Mt P.k (P.r - j)))
      (Lj : R.LevelData (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) (P.r - j))
      (stj : Fr.Start (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))) (κ : ℝ),
      0 < κ ∧ P5.IsData (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Xj μj Lj stj l0 ∧
      KB.ZetaNorm (T.bs j) μj ∧
      ∀ c : Fin P.r → ℂ, (∀ l : Fin P.r, l.val < j → c l ≠ 0) →
      ∃ Tj : RadSp P.k P.r T.base.z T.base.z' T.base.π T.base.π' →ₗ[ℂ]
        RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π',
      (∀ Φ c'' g, (Tj Φ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c'' g =
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) (P5.glue ⟨j, by omega⟩ c (PTie.shiftCf ⟨j, by omega⟩ c''))
          (D.castM (by omega) (ιLev P.k j (P.r - j) g))) ∧
      (∀ Φ Ψ c'', P5.pairAt μj (Tj Φ) (Tj Ψ) c'' =
        (κ : ℂ) * P5.pairAt μ Φ Ψ (P5.glue ⟨j, by omega⟩ c (PTie.shiftCf ⟨j, by omega⟩ c''))) ∧
      (∀ l : Fin (P.r - j), Rel Tj (L.p ⟨l.val + j, by omega⟩) (Lj.p l) ∧
        Rel Tj (L.c ⟨l.val + j, by omega⟩) (Lj.c l) ∧ Rel Tj (L.ci ⟨l.val + j, by omega⟩) (Lj.ci l)) ∧
      ∀ (n : ℕ) (hn : n + j ≤ P.r) (Y : ℂ),
        MRel Tj (P5.QQi L st ⟨n + j, by omega⟩ Y) (P5.QQi Lj stj ⟨n, by omega⟩ Y)
  | 0, _ => by
    obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k (P.r - 0) Wp Wq (T.bs 0)
    have h1 : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hD.2.1
    obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, μ = a • μ0 := by
      have hU := Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed P.k P.r
      have h1' := h1
      have h0 : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ0 := hμ0.1
      rw [glev_last_eq] at h1' h0
      exact Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar P.k P.r _ μ0 μ hU h0 h1'.conc h1'.left h1'.finite_compact
    have ha0 : (a : ℝ) ≠ 0 := by
      intro h
      apply h1.ne_zero
      rw [ha, show a = 0 from by exact_mod_cast h, zero_smul]
    refine ⟨X, μ0, L, st, (a : ℝ)⁻¹, inv_pos.2 (lt_of_le_of_ne a.2 (Ne.symm ha0)),
      ⟨JCTx5.isPlace_lev P T ⟨0, by omega⟩ hP, hμ0.1, hD.2.2⟩, hμ0, fun c _ => ⟨LinearMap.id,
      fun Φ c'' g => ?_, fun Φ Ψ c'' => ?_, fun l => ⟨rel_id _, rel_id _, rel_id _⟩, fun n hn Y => mrel_id _⟩⟩
    · rw [glue_zero', castM_iota0]; rfl
    · rw [glue_zero', ha, pairAt_smul, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ ha0, Complex.ofReal_one,
        one_mul]
      rfl
  | j + 1, hj => by
    obtain ⟨Xj, μj, Lj, stj, κ, hκ, hDj, hZj, hall⟩ := lev_indU P T hP X μ L st l0 hD j (by omega)
    have hj' : j + 1 ≤ P.r := hj
    have hPl := JCTx5.isPlace_lev P T ⟨j + 1, by omega⟩ hP
    obtain ⟨Xs⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
    obtain ⟨Ls, sts, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl Xs l0
    obtain ⟨μs, hμs⟩ := Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k (P.r - (j + 1)) Wp Wq (T.bs (j + 1))
    have hDs : P5.IsData (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π
        (T.bs (j + 1)).π' Xs μs Ls sts l0 := ⟨hPl, hμs.1, h1, h2, h3, h4, h5, h6⟩
    refine ⟨Xs, μs, Ls, sts, κ, hκ, hDs, hμs, fun c hc => ?_⟩
    obtain ⟨Tj, hform, hpair, hsite, hqq⟩ := hall c (fun l hl => hc l (by omega))
    have hn : P.r - j = 1 + (P.r - (j + 1)) := by omega
    have hcj : c ⟨j, by omega⟩ ≠ 0 := hc ⟨j, by omega⟩ (by simp)
    obtain ⟨T', hf', hs', hq', hp'⟩ := step_cast (k := P.k) (n := P.r - j) (ρ := P.r - (j + 1)) hn
      (levTower_bs_z_eq_castV_liftVec T j hj') (levTower_bs_z'_eq_castV_liftVec T j hj') (T.bs (j + 1)).z_mem (T.bs (j + 1)).z'_mem (tower_π T j hj')
      (tower_π' T j hj') Xj Xs Lj stj Ls sts (M.sgn (JC.parLev P j) l0) μj μs hDj.2.2.1 hDs.2.2.1
      hDj.2.2.2.1 hDs.2.2.2.1 hZj.1 hμs.1 hZj.2 hμs.2 (c ⟨j, by omega⟩) hcj
    refine ⟨T' ∘ₗ Tj, fun Φ c'' g => ?_, fun Φ Ψ c'' => ?_, fun l => ?_, fun n hn' Y => ?_⟩
    · rw [LinearMap.comp_apply, hf', hform, glue_step j hj' c c'' hn,
        lift_lift_M j (P.r - (j + 1)) (P.r - j) P.r hn.symm (by omega) (by omega)]
    · rw [LinearMap.comp_apply, LinearMap.comp_apply, hp', hpair, glue_step j hj' c c'' hn]
    · have e : (⟨l.val + 1 + j, by omega⟩ : Fin P.r) = ⟨l.val + (j + 1), by omega⟩ :=
        Fin.ext (show l.val + 1 + j = l.val + (j + 1) by omega)
      obtain ⟨a1, a2, a3⟩ := hsite ⟨l.val + 1, by omega⟩
      obtain ⟨b1, b2, b3⟩ := hs' l
      rw [← e]
      exact ⟨rel_comp a1 b1, rel_comp a2 b2, rel_comp a3 b3⟩
    · have e : (⟨n + 1 + j, by omega⟩ : Fin (P.r + 1)) = ⟨n + (j + 1), by omega⟩ :=
        Fin.ext (show n + 1 + j = n + (j + 1) by omega)
      have a := hqq (n + 1) (by omega) Y
      have b := hq' n (by omega) Y
      rw [← e]
      exact mrel_comp a b

theorem levTransportU : Formalism.FourierDecayAlt.P.PTie.LevTransportU := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 Bs hD hz hz' hπ hπ' i
  obtain ⟨T, h1, h2, h3, h4, hN⟩ := Formalism.FourierDecayAlt.P.exists_normalized_tower P.k P.r Wp Wq Bs
  have e1 : T.base.z = z := h1.trans hz
  have e2 : T.base.z' = z' := h2.trans hz'
  have e3 : T.base.π = π := h3.trans hπ
  have e4 : T.base.π' = π' := h4.trans hπ'
  subst e1 e2 e3 e4
  obtain ⟨Xi, μi, Li, sti, κ, hκ, hDi, -, hall⟩ := lev_indU P T hD.1 X μ L st l0 hD i.val (by omega)
  refine ⟨T, hN, rfl, rfl, rfl, rfl, T.bs i, Xi, μi, Li, sti, κ, rfl, hκ, hDi, fun c hc => ?_⟩
  obtain ⟨Ti, hform, hpair, hsite, hqq⟩ := hall c hc
  refine ⟨Ti, ⟨hform, ⟨κ, hκ, hpair⟩, fun n hn Y => hqq n hn Y,
    fun S _ _ w => ⟨fun l => ?_, fun n hn => ?_, fun hw => ?_⟩⟩, hpair⟩
  · obtain ⟨a1, a2, a3⟩ := hsite l
    exact arel_bT (σ := P5.site L ⟨l.val + i, by omega⟩) (σ' := P5.site Li l) a1 a2 a3 w
  · exact arel_RRw (fun Y => hqq n hn Y) w
  · obtain ⟨⟨hA1, hA2, hA3, hA4⟩, hw2, hw3⟩ := hw
    have hq : sti.q = st.q := hDi.2.2.2.2.1.trans hD.2.2.2.2.1.symm
    have hinv : sti.inv = st.inv := hDi.2.2.2.2.2.1.trans hD.2.2.2.2.2.1.symm
    refine ⟨⟨hA1, hA2, fun l hl => ?_, hA4⟩, hw2, hw3⟩
    rw [hq, hinv]
    exact hA3 l hl

end Formalism.FourierDecayAlt.P.PTieUL

namespace Formalism.FourierDecayAlt.P

theorem level_transport_unitary : Formalism.FourierDecayAlt.P.PTie.LevTransportU := PTieUL.levTransportU

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SendsToAlgMulAlg
section
open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section Pr

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem pr_fst_mul (x y : Pr V) : (x * y).1 = x.1 * y.1 := rfl

theorem pr_fst_algebraMap (a : ℂ) : (algebraMap ℂ (Pr V) a).1 = algebraMap ℂ (Module.End ℂ V) a := rfl

def sendsTo (U : Submodule ℂ V) (v : V) : Submodule ℂ (Pr V) where
  carrier := {x | x.1 v ∈ U}
  zero_mem' := by show (0 : Module.End ℂ V) v ∈ U; simp
  add_mem' := by
    intro x y hx hy
    show (x.1 + y.1) v ∈ U
    rw [LinearMap.add_apply]; exact U.add_mem hx hy
  smul_mem' := by
    intro a x hx
    show (a • x.1) v ∈ U
    rw [LinearMap.smul_apply]; exact U.smul_mem a hx

theorem sendsTo_alg_mul_alg (U : Submodule ℂ V) (v : V) {x : Pr V} (hx : x ∈ sendsTo U v) (a b : ℂ) :
    algebraMap ℂ (Pr V) a * x * algebraMap ℂ (Pr V) b ∈ sendsTo U v := by
  show (algebraMap ℂ (Pr V) a * x * algebraMap ℂ (Pr V) b).1 v ∈ U
  rw [pr_fst_mul, pr_fst_mul, pr_fst_algebraMap, pr_fst_algebraMap, Module.End.mul_apply, Module.End.mul_apply,
    Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  exact U.smul_mem a (U.smul_mem b hx)

end Pr

section Num

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {S : Type} [Fintype S] [DecidableEq S]

theorem UUw_mem {𝒜 : StarSubalgebra ℂ A} (s : ℂ) :
    ∀ w : List (Letter ℂ S), (UUw s w : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 := by
  intro w
  induction w with
  | nil => exact (entSub 𝒜).one_mem
  | cons l w ih =>
    rw [UUw]
    refine (entSub 𝒜).mul_mem (Formalism.FourierDecayAlt.P5.HerA.ins_mem _ fun i j => ?_) ih
    show io ((Formalism.YangianSpanCharacter.T.Um (if l.plus then s else star s) : M2 A) i j) ∈ entSub 𝒜
    apply Formalism.FourierDecayAlt.P5.HerA.io_mem
    fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.Um, 𝒜.algebraMap_mem]

theorem star_entSub {𝒜 : StarSubalgebra ℂ A} {M : SlopeTestRemainingChoices S A} (hM : M ∈ entSub 𝒜) : star M ∈ entSub 𝒜 := by
  intro i j
  rw [Matrix.star_apply]
  exact star_mem (hM j i)

theorem mem_bot_alg {x : A} (hx : x ∈ (⊥ : StarSubalgebra ℂ A)) : ∃ a : ℂ, x = algebraMap ℂ A a := by
  rw [StarSubalgebra.mem_bot] at hx
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, ha.symm⟩

end Num

section Wave

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)}

theorem QQi_castSucc' (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l : Fin P.r) (Y : ℂ) :
    QQi L st l.castSucc Y = (Ts (site L l) (star Y))ᴴ * QQi L st l.succ Y * Ts (site L l) Y := by
  have h : ∀ Y' : ℂ, tprod L Y' l.val = tprod L Y' (l.val + 1) * Ts (site L l) Y' := fun Y' => by
    rw [tprod, dif_pos l.isLt]
  unfold QQi
  rw [Fin.val_castSucc, Fin.val_succ, h, h, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem diag_comm {A : Type*} [Ring A] {f : A} {M : Matrix (Fin 2) (Fin 2) A} (h : ∀ i j, Commute f (M i j)) :
    Matrix.diagonal (fun _ => f) * M = M * Matrix.diagonal (fun _ => f) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact (h i j).eq

theorem commute_inv_of {A : Type*} [Ring A] {f fi x : A} (h1 : f * fi = 1) (h2 : fi * f = 1) (h : Commute f x) :
    Commute fi x := by
  show fi * x = x * fi
  calc fi * x = fi * x * (f * fi) := by rw [h1, mul_one]
    _ = fi * (f * x) * fi := by rw [h.eq]; simp only [mul_assoc]
    _ = x * fi := by rw [← mul_assoc, h2, one_mul]

theorem waveQQ_castSucc (X : ActualOps P.k P.r z z' π π') (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (hAL : IsActualLevel X L) (l : Fin P.r) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (hW' : multiplicationOperator Wv' (fun c _ => fsv (-s) (c l)))
    (hC : ∀ Y a b, Commute (mkP Wv Wv') (QQi L st l.succ Y a b)) :
    WaveQQ (QQi L st l.castSucc) (mkP Wv Wv') (mkP Wv' Wv) s := by
  intro Y
  obtain ⟨⟨h1, h2, h3⟩, hc, hci, hp⟩ :=
    Formalism.FourierDecayAlt.P5.waveSiteAll Wp Wq P z z' π π' X L hAL l s Wv Wv' hW hW'
  have hT : ∀ Y' : ℂ, Ts (site L l) Y' * Matrix.diagonal (fun _ => mkP Wv Wv') =
      Matrix.diagonal (fun _ => mkP Wv Wv') * Ts (site L l) Y' * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s := by
    intro Y'
    obtain ⟨-, hUiU, hE⟩ := Formalism.YangianSpanCharacter.Final.T_PlaneWave ℂ (Pr (RadSp P.k P.r z z' π π')) (site L l).p (site L l).c
      (site L l).ci (mkP Wv Wv') s Y' hc hci hp
    calc Ts (site L l) Y' * Matrix.diagonal (fun _ => mkP Wv Wv')
        = Ts (site L l) Y' * Matrix.diagonal (fun _ => mkP Wv Wv') * (Formalism.YangianSpanCharacter.T.Uinv (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s) := by
          rw [hUiU, Matrix.mul_one]
      _ = (Ts (site L l) Y' * Matrix.diagonal (fun _ => mkP Wv Wv') * Formalism.YangianSpanCharacter.T.Uinv (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s) * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun _ => mkP Wv Wv') * Ts (site L l) Y' * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s := by
          unfold Ts; rw [hE]
  have hDf : (Matrix.diagonal (fun _ : Fin 2 => mkP Wv Wv'))ᴴ = Matrix.diagonal (fun _ => mkP Wv' Wv) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
  have ha := congrArg Matrix.conjTranspose (hT (star Y))
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hDf] at ha
  have hci' : ∀ a b, Commute (mkP Wv' Wv) (QQi L st l.succ Y a b) := fun a b =>
    commute_inv_of h1 h2 (hC Y a b)
  have hb : Matrix.diagonal (fun _ => mkP Wv' Wv) * QQi L st l.succ Y * Matrix.diagonal (fun _ => mkP Wv Wv') =
      QQi L st l.succ Y := by
    rw [diag_comm hci', Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, h2]
    rw [show (Matrix.diagonal fun _ : Fin 2 => (1 : Pr (RadSp P.k P.r z z' π π'))) = 1 from Matrix.diagonal_one,
      Matrix.mul_one]
  rw [QQi_castSucc']
  calc Matrix.diagonal (fun _ => mkP Wv' Wv) *
        ((Ts (site L l) (star Y))ᴴ * QQi L st l.succ Y * Ts (site L l) Y) * Matrix.diagonal (fun _ => mkP Wv Wv')
      = (Matrix.diagonal (fun _ => mkP Wv' Wv) * (Ts (site L l) (star Y))ᴴ) * QQi L st l.succ Y *
          (Ts (site L l) Y * Matrix.diagonal (fun _ => mkP Wv Wv')) := by simp only [Matrix.mul_assoc]
    _ = ((Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s)ᴴ * ((Ts (site L l) (star Y))ᴴ * Matrix.diagonal (fun _ => mkP Wv' Wv))) *
          QQi L st l.succ Y * (Matrix.diagonal (fun _ => mkP Wv Wv') * Ts (site L l) Y * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s) := by
        rw [ha, hT Y]
    _ = (Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s)ᴴ * (Ts (site L l) (star Y))ᴴ *
          (Matrix.diagonal (fun _ => mkP Wv' Wv) * QQi L st l.succ Y * Matrix.diagonal (fun _ => mkP Wv Wv')) *
          Ts (site L l) Y * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hb]; simp only [Matrix.mul_assoc]

end Wave

section WordWave

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {S : Type} [Fintype S] [DecidableEq S]

theorem rr_io_wave (QQ : ℂ → M2 A) (f fi : A) (s : ℂ) (w : List (Letter ℂ S)) (hW : IsWave f fi)
    (hQ : WaveQQ QQ f fi s) (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) :
    RRw QQ w * io f = io f * (star (UUw s w) * RRw QQ w * UUw s w) := by
  obtain ⟨hVVi, -, hRR, -⟩ := Formalism.FourierDecayAlt.P.plane_wave_word_identity ℂ A S QQ f fi s w hW hQ hw
  obtain ⟨h1, h2, h3⟩ := hW
  have hsfi : star fi = f := by rw [← h3, star_star]
  have e1 : (io fi : SlopeTestRemainingChoices S A) * io f = 1 := by
    rw [← Formalism.FourierDecayAlt.P.Wd11.io_mul, h2, Formalism.FourierDecayAlt.P.Wd11.io_one]
  have hUU : UUiw s w * UUw s w = (1 : SlopeTestRemainingChoices S A) := by
    have hv : io f * UUiw s w * (UUw s w * io fi) = (1 : SlopeTestRemainingChoices S A) := by
      have := hVVi; unfold Vw Viw at this; simpa only [mul_assoc] using this
    calc UUiw s w * UUw s w = (io fi * io f) * (UUiw s w * UUw s w) * (io fi * io f) := by
          rw [e1, one_mul, mul_one]
      _ = io fi * (io f * UUiw s w * (UUw s w * io fi)) * io f := by simp only [mul_assoc]
      _ = 1 := by rw [hv, mul_one, e1]
  have hsVi : star (Viw fi s w) = io f * star (UUw s w) := by
    unfold Viw
    rw [star_mul, Formalism.FourierDecayAlt.P.Wd11.io_star, hsfi]
  have hsVV : star (Viw fi s w) * star (Vw f s w) = 1 := by
    rw [← star_mul, hVVi, star_one]
  have key : RRw QQ w * Vw f s w = star (Viw fi s w) * RRw QQ w := by
    calc RRw QQ w * Vw f s w = (star (Viw fi s w) * star (Vw f s w)) * RRw QQ w * Vw f s w := by
          rw [hsVV, one_mul]
      _ = star (Viw fi s w) * (star (Vw f s w) * RRw QQ w * Vw f s w) := by simp only [mul_assoc]
      _ = star (Viw fi s w) * RRw QQ w := by rw [hRR]
  calc RRw QQ w * io f = RRw QQ w * io f * (UUiw s w * UUw s w) := by rw [hUU, mul_one]
    _ = (RRw QQ w * Vw f s w) * UUw s w := by unfold Vw; simp only [mul_assoc]
    _ = io f * (star (UUw s w) * RRw QQ w * UUw s w) := by rw [key, hsVi]; simp only [mul_assoc]

theorem io_apply_mul (x : A) (M : SlopeTestRemainingChoices S A) (a b : Ix S) : ((io x : SlopeTestRemainingChoices S A) * M) a b = x * M a b := by
  simp [io, Matrix.diagonal_mul]

theorem mul_io_apply (x : A) (M : SlopeTestRemainingChoices S A) (a b : Ix S) : (M * (io x : SlopeTestRemainingChoices S A)) a b = M a b * x := by
  simp [io, Matrix.mul_diagonal]

end WordWave

end Formalism.FourierDecayAlt.P5.HerD
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothHermitianRankTwo
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.QuantumDeterminants PI.UnitaryGroupMassFormula.GsFr
open scoped Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace S1

variable {k r : ℕ}

lemma smooth_hermitian_rank_two {s : Set (B.Mat k r)} {p q : B.Mat k r → Fin (2 * r + k + 1) → ℂ}
    (hp : Sm p s) (hq : Sm q s) : Sm (fun x => Rk k r (p x) (q x)) s := by
  unfold Sm Rk at *
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  simp only [Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Pi.star_apply]
  have hs : ∀ l, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => star (q x l)) s := fun l => by
    have h := Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_pi.mp hq l)
    simpa [Function.comp_def] using h
  exact (contDiffOn_pi.mp hp i).mul (ContDiffOn.sum fun l _ => (hs l).mul contDiffOn_const)

lemma s_unitH {s : Set (B.Mat k r)} {v : B.Mat k r → Fin (2 * r + k + 1) → ℂ} (hv : Sm v s)
    (hp : ∀ x ∈ s, 0 < (Formalism.QuantumDeterminants.herm (Hpk k r) (v x) (v x)).re) : Sm (fun x => unitH k r (v x)) s := by
  unfold Sm unitH Formalism.QuantumDeterminants.herm at *
  have hvi : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => v x i) s := fun i => contDiffOn_pi.mp hv i
  have hsi : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => star (v x i)) s := fun i => by
    have h := Complex.conjCLE.contDiff.comp_contDiffOn (hvi i)
    simpa [Function.comp_def] using h
  have hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => star (v x) ⬝ᵥ Hpk k r *ᵥ v x) s := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    exact ContDiffOn.sum fun i _ => (hsi i).mul (ContDiffOn.sum fun j _ => contDiffOn_const.mul (hvi j))
  have hre : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (star (v x) ⬝ᵥ Hpk k r *ᵥ v x).re) s := by
    have h := Complex.reCLM.contDiff.comp_contDiffOn hh
    simpa [Function.comp_def] using h
  have hsq := hre.sqrt fun x hx => (hp x hx).ne'
  have hinv := hsq.inv fun x hx => (Real.sqrt_pos.mpr (hp x hx)).ne'
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (((Real.sqrt (star (v x) ⬝ᵥ Hpk k r *ᵥ v x).re)⁻¹ : ℝ) : ℂ)) s := by
    have h := Complex.ofRealCLM.contDiff.comp_contDiffOn hinv
    simpa [Function.comp_def] using h
  exact hc.smul hv

end S1

open S1 in
theorem geometry_smoothness_holds : GeomSmooth := by
  intro k r z z' _hk hz hz'
  let fd : B.Mat k r → ℂ := fun g => (Zhat k r z z' g).det
  let f1 : B.Mat k r → ℝ := fun g =>
    (Formalism.QuantumDeterminants.herm (Hpk k r) (omW k r z z' g) (omW k r z z' g)).re
  let f2 : B.Mat k r → ℝ := fun g =>
    (Formalism.QuantumDeterminants.herm (Hpk k r) (omS k r z z' g) (omS k r z z' g)).re
  have hid : Sm (fun g : B.Mat k r => g) Set.univ := contDiffOn_id
  have cd : Continuous fd := (contDiffOn_univ.1 (s_det (s_Zhat z z' hid))).continuous
  have c1 : Continuous f1 :=
    (contDiffOn_univ.1 (s_re (s_herm _ (s_omW z z' hid) (s_omW z z' hid)))).continuous
  have c2 : Continuous f2 :=
    (contDiffOn_univ.1 (s_re (s_herm _ (s_omS (s := Set.univ) z z') (s_omS z z')))).continuous
  let U : Set (B.Mat k r) := (fd ⁻¹' {0}ᶜ ∩ {g | 0 < f1 g}) ∩ {g | 0 < f2 g}
  have hU : IsOpen U :=
    ((isOpen_compl_singleton.preimage cd).inter (isOpen_lt continuous_const c1)).inter
      (isOpen_lt continuous_const c2)
  have hmem : ∀ g ∈ posG k r z z', g ∈ U := by
    intro g hg
    obtain ⟨hgV, hG⟩ := hg
    refine ⟨⟨det_ne_of_G hz hz' hG, ?_⟩, ?_⟩
    · have hm : omW k r z z' g ∈ Wsp k r z := prW_mem hz _
      exact posV hz hm.1 hm.2 (omW_ne hz hz' hgV hG)
    · have hm : omS k r z z' g ∈ Wsp k r z' := prW_mem hz' _
      have hω : omS k r z z' g ≠ 0 := by rw [← omS_eq z z' hgV]; exact omW'_ne hz hz' hgV hG
      exact posV hz' hm.1 hm.2 hω
  have sU : Sm (fun g : B.Mat k r => g) U := contDiffOn_id
  have hd0 : ∀ g ∈ U, (Zhat k r z z' g).det ≠ 0 := fun g hg => hg.1.1
  have hnu : Sm (fun g => nuG z z' g) U := s_unitH (s_omW z z' sU) fun g hg => hg.1.2
  have hnuS : Sm (fun g => unitH k r (omS k r z z' g)) U := s_unitH (s_omS z z') fun g hg => hg.2
  have hdi : Sm (fun g => -((Zhat k r z z' g).det)⁻¹) U := ((s_det (s_Zhat z z' sU)).inv hd0).neg
  have hL : Sm (fun g => Lm k r z z' g) U := by
    unfold Lm
    exact contDiffOn_const.add (ContDiffOn.sum fun c _ => ContDiffOn.sum fun a _ =>
      s_msmul (hdi.mul (s_adj (s_Zhat z z' sU) c a)) (s_mmul contDiffOn_const sU))
  have hP : Sm (fun g => Phi k r z z' g) U := by
    unfold Phi
    exact s_mmul (s_mmul contDiffOn_const sU) hL
  have hio : Sm (fun g => Phi k r z z' g *
      (Pm k r z' - Rk k r (unitH k r (omS k r z z' g)) (unitH k r (omS k r z z' g)) * Pm k r z')) U :=
    s_mmul hP (contDiffOn_const.sub (s_mmul (smooth_hermitian_rank_two hnuS hnuS) contDiffOn_const))
  refine ⟨fun g₀ hg₀ => ⟨U, fun g => nuG z z' g, hU, hmem g₀ hg₀, hnu, fun g _ _ => rfl⟩,
    fun g₀ hg₀ => ⟨U, fun g => unitH k r (omS k r z z' g), hU, hmem g₀ hg₀, hnuS, fun g _ hgV => ?_⟩,
    fun g₀ hg₀ => ⟨U, _, hU, hmem g₀ hg₀, hio, fun g _ hgV => ?_⟩⟩
  · show unitH k r (omW' k r z z' g) = _
    rw [omS_eq z z' hgV]
  · show Phi k r z z' g * (Pm k r z' - Rk k r (unitH k r (omW' k r z z' g)) (unitH k r (omW' k r z z' g)) *
      Pm k r z') = _
    rw [omS_eq z z' hgV]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

