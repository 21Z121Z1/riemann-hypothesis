import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0140
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0117
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0135
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjugateBlockSingleLastColumn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SubMulRight
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankZeroApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0120
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0137
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0139
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0054
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HerAnalyticFOfCls
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

section Gen

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
variable {𝒜 : StarSubalgebra ℂ A}

theorem Ts_mem (σ : Site A) (hp : σ.p ∈ 𝒜) (hc : σ.c ∈ 𝒜) (hci : σ.ci ∈ 𝒜) (Y : ℂ) (i j : Fin 2) :
    Ts σ Y i j ∈ 𝒜 := by
  unfold Ts Formalism.YangianSpanCharacter.T.Tm
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  · exact add_mem (algebraMap_mem 𝒜 Y) hp
  · exact neg_mem hc
  · exact hci
  · exact zero_mem 𝒜

theorem bT_mem (σ : Site A) (hp : σ.p ∈ 𝒜) (hc : σ.c ∈ 𝒜) (hci : σ.ci ∈ 𝒜) (w : List (Letter ℂ S)) :
    bT σ w ∈ entSub 𝒜 := by
  induction w with
  | nil => exact (entSub 𝒜).one_mem
  | cons l w ih =>
    rw [bT]
    refine (entSub 𝒜).mul_mem (ins_mem _ fun i j => ?_) ih
    show io ((if l.plus then Ts σ l.pt else (Ts σ l.pt).map star) i j) ∈ entSub 𝒜
    apply io_mem
    split_ifs
    · exact Ts_mem σ hp hc hci l.pt i j
    · exact (star_mem (Ts_mem σ hp hc hci l.pt i j) : star _ ∈ 𝒜)

end Gen

section Lev

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem intOn_of_last {μ : Measure (Mt k r)} {U : Submodule ℂ (RadSp k r z z' π π')}
    (hI : IntLevOn μ (Fin.last r) U) : IntOn μ U := by
  intro c hc Φ hΦ Ψ hΨ
  obtain ⟨h1, -⟩ := hI c hc Φ hΦ Ψ hΨ
  have h2 := h1 (Classical.arbitrary _)
  rwa [glue_last_level] at h2

end Lev

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem herAnalyticF_of_cls (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0)
    (U : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (hKU : ∀ i, K i ≤ U i)
    (hI : ∀ i, IntLevOn μ i (U i))
    (hQ : ∀ i, ∀ Y : ℂ, star Y = Y → ∀ a b, st.QQ Y a b ∈ presAlg (U i))
    (hS : ∀ (i : Fin (P.r + 1)) (l : Fin P.r), i.val ≤ l.val →
      L.p l ∈ presAlg (U i) ∧ L.c l ∈ presAlg (U i) ∧ L.ci l ∈ presAlg (U i))
    (hfn : ∀ j, ∀ Φ ∈ U (Fin.last P.r), X.fn j Φ ∈ U (Fin.last P.r))
    (hT : ∀ Y : ℂ, star Y = Y → ∀ a b, X.QQ Y a b ∈ adjAlg μ (U (Fin.last P.r)) (intOn_of_last (hI _)))
    (hSA : ∀ (l : Fin P.r) (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r),
      L.p l ∈ adjLev μ l.castSucc (U l.castSucc) (hI _) c hc ∧ L.c l ∈ adjLev μ l.castSucc (U l.castSucc) (hI _) c hc ∧
        L.ci l ∈ adjLev μ l.castSucc (U l.castSucc) (hI _) c hc)
    (hPh : ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r) (x y : Ix S → RadSp P.k P.r z z' π π'),
      InK (K l.castSucc) x → InK (K l.castSucc) y → ∀ c ∈ OmX P.r,
      ∃ φ : ℂ → ℂ, Continuous φ ∧ (∀ t, t ≠ 0 → φ t = ph L st μ l w x y c t) ∧
        ∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C * (1 + ‖t‖) ^ (-4 : ℤ)) :
    HerAnalyticF S P z z' π π' μ L st l0 K := by
  refine ⟨?_, ?_, ?_⟩
  · exact adjTop_of_tAdj P z z' π π' X μ L st K l0 hD (U (Fin.last P.r)) (intOn_of_last (hI _)) (hKU _) hfn hT
  · refine stepDens_of P z z' π π' μ L st K l0 (fun l => U l.castSucc) (fun l => hKU _) (fun l => hI _)
      (fun w hw l => siteStep_actual P z z' π π' X μ L st l0 w hD hw l)
      ?_ ?_ hPh
    · intro w _ l c hc a b
      obtain ⟨hp, hcc, hci⟩ := hSA l c hc
      exact bT_mem (site L l) hp hcc hci w a b
    · intro w hw l a b
      refine rrw_mem (QQi L st l.succ) (QQi_mem L st (presAlg (U l.castSucc)) l.succ (hQ _) ?_) w hw.1.2.1 a b
      intro l' hl'
      exact hS l.castSucc l' (by simp only [Fin.val_succ] at hl'; simp only [Fin.val_castSucc]; omega)
  · exact formInt_of_cls P z z' π π' μ L st K l0 U hKU hI hQ hS

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Imports
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def Kr (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (x : B.Mat k r) : Wq →L[ℂ] Wp :=
  ∫ p : Mt k r × Mt k r, star (psi k r Bs.z' cStd (Matrix.of p.2)) •
    (F (x * Matrix.of p.2 * Matrix.of p.1)).comp (Bs.π' (Matrix.of p.1)⁻¹) ∂(Bs.μW'.prod Bs.μN)

end Formalism.FourierDecayAlt.P.PBG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerCoordinateProd
section
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section cut

variable {j : ℕ}

def blkU (M : Matrix (Fin (j + 1)) (Fin (j + 1)) ℂ) : Matrix (Fin j) (Fin j) ℂ := M.submatrix Fin.castSucc Fin.castSucc

def x0c (w0 : Equiv.Perm (Fin j)) (W : Matrix (Fin j) (Fin j) ℂ) : C2.Lstidx w0 → ℂ :=
  ((StabilizerDisintegration.UC.eSp w0).symm (StabilizerDisintegration.utc W)).1

def boxC : Set ℂ := Complex.equivRealProd ⁻¹' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)

def chiL (w0 : Equiv.Perm (Fin j)) (x : C2.Lstidx w0 → ℂ) : ℝ :=
  (Set.univ.pi fun _ : C2.Lstidx w0 => boxC).indicator (fun _ => (1 : ℝ)) x

theorem boxR_meas : MeasurableSet (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc

theorem boxC_meas : MeasurableSet boxC := (Complex.measurable_re.prodMk Complex.measurable_im) boxR_meas

theorem boxC_vol : volume boxC = 1 := by
  have h := (Complex.volume_preserving_equiv_real_prod.measure_preimage boxR_meas.nullMeasurableSet)
  change volume (Complex.measurableEquivRealProd ⁻¹' _) = 1
  rw [h, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
  simp

theorem chiL_meas (w0 : Equiv.Perm (Fin j)) : Measurable (chiL w0) := measurable_const.indicator (MeasurableSet.univ_pi fun _ => boxC_meas)

theorem chiL_nonneg (w0 : Equiv.Perm (Fin j)) (x : C2.Lstidx w0 → ℂ) : 0 ≤ chiL w0 x := by
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

theorem chiL_int (w0 : Equiv.Perm (Fin j)) : ∫ x, chiL w0 x = 1 := by
  unfold chiL
  rw [integral_indicator_const _ (MeasurableSet.univ_pi fun _ => boxC_meas), Measure.real,
    volume_pi_pi]
  simp [boxC_vol]

end cut

section low

variable {r : ℕ} (w : Equiv.Perm (Fin (r + 1))) (w0 : Equiv.Perm (Fin r))

theorem w_last (hw : ∀ a : Fin r, w.symm a.castSucc = (w0.symm a).castSucc) :
    w.symm (Fin.last r) = Fin.last r := by
  by_contra h
  obtain ⟨b, hb⟩ := Fin.exists_castSucc_eq.2 h
  have h2 : w.symm (w0 b).castSucc = b.castSucc := by rw [hw, Equiv.symm_apply_apply]
  rw [hb] at h2
  exact (Fin.castSucc_lt_last (w0 b)).ne (w.symm.injective h2)

theorem w_last' (hw : ∀ a : Fin r, w.symm a.castSucc = (w0.symm a).castSucc) : w (Fin.last r) = Fin.last r := by
  exact ((Equiv.symm_apply_eq w).1 (w_last w w0 hw)).symm

variable (hw : ∀ a : Fin r, w.symm a.castSucc = (w0.symm a).castSucc)
include hw

theorem lst_ne_last (q : C2.Lstidx w) : q.1.1 ≠ Fin.last r ∧ q.1.2 ≠ Fin.last r := by
  refine ⟨fun h => ?_, ne_of_lt (lt_of_lt_of_le q.2.1 (Fin.le_last _))⟩
  have h2 := q.2.2
  rw [h, w_last w w0 hw] at h2
  exact absurd h2 (not_lt.2 (Fin.le_last _))

def eL : C2.Lstidx w0 ≃ C2.Lstidx w where
  toFun q := ⟨(q.1.1.castSucc, q.1.2.castSucc), Fin.castSucc_lt_castSucc_iff.2 q.2.1, by
    rw [hw, hw]; exact Fin.castSucc_lt_castSucc_iff.2 q.2.2⟩
  invFun q := ⟨((q.1.1).castPred (lst_ne_last w w0 hw q).1, (q.1.2).castPred (lst_ne_last w w0 hw q).2), by
    refine ⟨?_, ?_⟩
    · rw [← Fin.castSucc_lt_castSucc_iff]; simpa using q.2.1
    · have ha : ((q.1.1).castPred (lst_ne_last w w0 hw q).1).castSucc = q.1.1 := Fin.castSucc_castPred _ _
      have hb : ((q.1.2).castPred (lst_ne_last w w0 hw q).2).castSucc = q.1.2 := Fin.castSucc_castPred _ _
      have h2 : w.symm ((q.1.1).castPred (lst_ne_last w w0 hw q).1).castSucc <
          w.symm ((q.1.2).castPred (lst_ne_last w w0 hw q).2).castSucc := by rw [ha, hb]; exact q.2.2
      rw [hw, hw] at h2
      exact Fin.castSucc_lt_castSucc_iff.1 h2⟩
  left_inv q := by ext <;> simp
  right_inv q := by ext <;> simp

theorem low_blk (x : C2.Lstidx w → ℂ) : blkU (Dx2.Rad.low w x) = Dx2.Rad.low w0 (x ∘ eL w w0 hw) := by
  ext i j
  rw [← StabilizerDisintegration.UC.lowS_eq_low, ← StabilizerDisintegration.UC.lowS_eq_low]
  simp only [blkU, Matrix.submatrix_apply, StabilizerDisintegration.lowS, C2.lowOf, Matrix.add_apply, Matrix.of_apply,
    Function.comp_apply]
  rw [← (eL w w0 hw).sum_comp (fun q => if q.1 = (i.castSucc, j.castSucc) then x q else 0)]
  congr 1
  · simp [Matrix.one_apply]
  · refine Finset.sum_congr rfl fun q _ => ?_
    have he : ((eL w w0 hw) q).1 = (q.1.1.castSucc, q.1.2.castSucc) := rfl
    simp only [he, Prod.ext_iff, Fin.castSucc_inj]

theorem low_last_row (x : C2.Lstidx w → ℂ) (a : Fin r) : Dx2.Rad.low w x (Fin.last r) a.castSucc = 0 := by
  rw [← StabilizerDisintegration.UC.lowS_eq_low]
  simp only [StabilizerDisintegration.lowS, C2.lowOf, Matrix.add_apply, Matrix.of_apply]
  rw [Matrix.one_apply_ne (Fin.castSucc_lt_last a).ne', zero_add]
  exact Finset.sum_eq_zero fun q _ => if_neg fun h => (lst_ne_last w w0 hw q).1 (congrArg Prod.fst h)

omit hw in
theorem blkU_mul (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hA : ∀ a : Fin r, A a.castSucc (Fin.last r) = 0) :
    blkU (A * B) = blkU A * blkU B := by
  ext i j
  simp only [blkU, Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_castSucc, hA, zero_mul, add_zero]

omit hw in
theorem blkU_ct (A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : blkU Aᴴ = (blkU A)ᴴ := by
  ext i j
  rfl

omit hw in
theorem blkU_UT {A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hA : A ∈ C2.UTset (r + 1)) : blkU A ∈ C2.UTset r := ⟨fun i j h => hA.1 _ _ (Fin.castSucc_lt_castSucc_iff.2 h), fun i => hA.2 _⟩

end low

section normcut

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def theta0 (z : Fin (2 * r + k + 1) → ℂ) (w0 : Equiv.Perm (Fin r)) (p : B.SS k r) : ℝ :=
  chiL w0 (x0c w0 (blkU (C2.uMap k r z (Matrix.of p.1.2))))

theorem theta0_meas (z : Fin (2 * r + k + 1) → ℂ) (w0 : Equiv.Perm (Fin r)) : Measurable (theta0 (k := k) z w0) := by
  have hU : Measurable fun p : B.SS k r => StabilizerDisintegration.utc (blkU (C2.uMap k r z (Matrix.of p.1.2))) := by
    refine measurable_pi_lambda _ fun q => ?_
    have hc : Continuous fun p : B.SS k r =>
        C2.uMap k r z (Matrix.of p.1.2) q.1.1.castSucc q.1.2.castSucc := by
      simp only [C2.uMap, Formalism.QuantumDeterminants.herm, Fin.coe_castSucc, Fin.is_lt, dif_pos, dotProduct,
        Matrix.mulVec, Matrix.of_apply]
      fun_prop
    exact hc.measurable
  unfold theta0 x0c
  exact (chiL_meas w0).comp (measurable_fst.comp ((StabilizerDisintegration.UC.eSp w0).symm.measurable.comp hU))

theorem lower_coordinate_prod (w0 : Equiv.Perm (Fin r)) (x a : C2.Lstidx w0 → ℂ) (y : C2.LPidx w0 → ℂ) :
    x0c w0 ((StabilizerDisintegration.lowS w0 x)ᴴ * ((StabilizerDisintegration.lowS w0 a)ᴴ * (StabilizerDisintegration.lowP w0 y)ᴴ)) =
      StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 a * StabilizerDisintegration.lowS w0 x) := by
  have hL := ((StabilizerDisintegration.UC.lstLeft r w0 (fun _ => 1) (fun _ => one_ne_zero) a).2 x)
  have hM : (StabilizerDisintegration.lowS w0 x)ᴴ * ((StabilizerDisintegration.lowS w0 a)ᴴ * (StabilizerDisintegration.lowP w0 y)ᴴ) =
      (StabilizerDisintegration.lowS w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 a * StabilizerDisintegration.lowS w0 x)))ᴴ * (StabilizerDisintegration.lowP w0 y)ᴴ := by
    rw [← hL, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hE : StabilizerDisintegration.utc ((StabilizerDisintegration.lowS w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 a * StabilizerDisintegration.lowS w0 x)))ᴴ *
      (StabilizerDisintegration.lowP w0 y)ᴴ) = StabilizerDisintegration.UC.eSp w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 a * StabilizerDisintegration.lowS w0 x), y) := rfl
  unfold x0c
  rw [hM, hE, MeasurableEquiv.symm_apply_apply]

theorem theta0_normCut (S : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
    {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
    (hZ : Zhat k r S.z S.z' γ = C2.monoP w d) (w0 : Equiv.Perm (Fin r))
    (hw : ∀ a : Fin r, w.symm a.castSucc = (w0.symm a).castSucc) :
    D.IsNormCut S γ (D.muR S γ w) (theta0 S.z w0) := by
  have hB : w (Fin.last r) = Fin.last r := w_last' w w0 hw
  have hG : Dx2.Rad.Good S γ w d :=
    ⟨Dx2.Rad.ex_degen S hγ hd hZ hB, Dx2.Rad.inj_degen S hγ hd hZ hB, fun ρ hρ => Dx2.Rad.lst_gen S hγ hd hZ hρ⟩
  refine ⟨theta0_meas S.z w0, fun p => chiL_nonneg w0 _, fun p hp => ?_⟩
  have hmuR : D.muR S γ w = (volume : Measure (C2.Lstidx w → ℂ)).map
      (fun x => (Matrix.of.symm (Dx2.Rad.rhoF S γ w x) : Mt k r)) := rfl
  have hact : Measurable fun x : Mt k r => theta0 S.z w0 (C6.actR γ (Matrix.of x) p) := by
    refine (theta0_meas S.z w0).comp ?_
    unfold C6.actR
    refine Measurable.prodMk (Measurable.prodMk measurable_const ?_) (Measurable.prodMk measurable_const ?_)
    · refine (continuous_pi fun i => continuous_pi fun l => ?_).measurable
      simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
      fun_prop
    · refine (continuous_pi fun i => continuous_pi fun l => ?_).measurable
      simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
      fun_prop
  rw [hmuR, integral_map (Dx2.Rad.rhoF_meas S hγ hd hG).aemeasurable hact.aestronglyMeasurable]

  have hn : Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset k r := hp.2.1
  have hUT : blkU (C2.uMap k r S.z (Matrix.of p.1.2)) ∈ C2.UTset r :=
    blkU_UT ((Formalism.FourierDecayAlt.P.unipotent_map_frame k r S.z ⟨S.z_mem, S.T_pos⟩).1 _ (Dx2.Rad.N_sub_S S.z hn)).2.1
  set pa := (StabilizerDisintegration.UC.eSp w0).symm (StabilizerDisintegration.utc (blkU (C2.uMap k r S.z (Matrix.of p.1.2)))) with hpa
  have hsplit : blkU (C2.uMap k r S.z (Matrix.of p.1.2)) = (StabilizerDisintegration.lowS w0 pa.1)ᴴ * (StabilizerDisintegration.lowP w0 pa.2)ᴴ := by
    rw [← StabilizerDisintegration.UC.upper_fSp, ← StabilizerDisintegration.UC.upper_utc hUT]
    congr 1
    show _ = StabilizerDisintegration.UC.eSp w0 pa
    rw [hpa, (StabilizerDisintegration.UC.eSp w0).apply_symm_apply]
  have hpt : ∀ x : C2.Lstidx w → ℂ, theta0 S.z w0 (C6.actR γ (Matrix.of (Matrix.of.symm (Dx2.Rad.rhoF S γ w x))) p) =
      chiL w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 pa.1 * StabilizerDisintegration.lowS w0 (x ∘ eL w w0 hw))) := by
    intro x
    obtain ⟨hρR, hρu⟩ := Dx2.Rad.rhoF_spec S hγ hd hG x
    unfold theta0
    simp only [C6.actR, Equiv.apply_symm_apply]
    rw [Dx2.Rad.uMap_mul S hρR.1 hn, hρu,
      blkU_mul _ _ (fun a => by rw [Matrix.conjTranspose_apply, low_last_row w w0 hw, star_zero]),
      blkU_ct, low_blk w w0 hw, hsplit, ← StabilizerDisintegration.UC.lowS_eq_low, lower_coordinate_prod]
  simp_rw [hpt]
  have hmp1 := (MeasureTheory.measurePreserving_piCongrLeft (fun _ : C2.Lstidx w => (volume : Measure ℂ))
    (eL w w0 hw)).symm
  have hmp2 := (StabilizerDisintegration.lstLeft r w0 (fun _ => 1) (fun _ => one_ne_zero) pa.1).1
  have e1 : ∫ x : C2.Lstidx w → ℂ, chiL w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 pa.1 * StabilizerDisintegration.lowS w0 (x ∘ eL w w0 hw))) =
      ∫ x' : C2.Lstidx w0 → ℂ, chiL w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 pa.1 * StabilizerDisintegration.lowS w0 x')) := by
    have h := hmp1.integral_comp (MeasurableEquiv.measurableEmbedding _)
      (fun y : C2.Lstidx w0 → ℂ => chiL w0 (StabilizerDisintegration.lsc w0 (StabilizerDisintegration.lowS w0 pa.1 * StabilizerDisintegration.lowS w0 y)))
    exact h
  rw [e1, ← integral_map hmp2.measurable.aemeasurable (chiL_meas w0).aestronglyMeasurable, hmp2.map_eq,
    chiL_int]

end normcut

end Formalism.FourierDecayAlt.P.PBM
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurableEmbeddingLevM
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k ρ : ℕ}

def projM (y : Mt k (1 + ρ)) : Mt k ρ := fun a b => y ⟨a.val + 1, by omega⟩ ⟨b.val + 1, by omega⟩

theorem projM_levM (x : Mt k ρ) : projM (B2.levM k ρ x) = x := by
  funext a b
  simp only [projM, B2.levM, ιLev, Matrix.of_apply]
  rw [dif_pos ⟨by omega, by omega⟩, dif_pos ⟨by omega, by omega⟩]
  rfl

theorem continuous_levM : Continuous (B2.levM k ρ) := by
  exact Formalism.FourierDecayAlt.P.LongWeylElement.levM_cont k ρ

theorem continuous_projM : Continuous (projM (k := k) (ρ := ρ)) := by
  unfold projM
  fun_prop

theorem measurableEmbedding_levM : MeasurableEmbedding (B2.levM k ρ) := by
  refine MeasurableEmbedding.of_measurable_inverse continuous_levM.measurable ?_
    continuous_projM.measurable (fun x => projM_levM x)
  have hr : Set.range (B2.levM k ρ) = {y | B2.levM k ρ (projM y) = y} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      simp only [Set.mem_setOf_eq, projM_levM]
    · intro hy
      exact ⟨projM y, hy⟩
  rw [hr]
  exact (isClosed_eq (continuous_levM.comp continuous_projM) continuous_id).measurableSet

theorem zWeight_fin (T T' R : ℝ) :
    ∫⁻ ζ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal (B2.zWeight k T T' ζ) < ⊤ := by
  have hC : ∀ ζ ∈ Metric.closedBall (0 : ℂ) R,
      ENNReal.ofReal (B2.zWeight k T T' ζ) ≤ ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) := by
    intro ζ hζ
    apply ENNReal.ofReal_le_ofReal
    have hn : ‖ζ‖ ≤ R := by simpa using hζ
    have hns : Complex.normSq ζ ≤ R ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    simp only [B2.zWeight]
    split_ifs with h
    · apply pow_le_pow_left₀ (by linarith)
      linarith [neg_abs_le (T * T')]
    · positivity
  calc ∫⁻ ζ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal (B2.zWeight k T T' ζ)
      ≤ ∫⁻ _ in Metric.closedBall (0 : ℂ) R, ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) :=
        setLIntegral_mono' measurableSet_closedBall hC
    _ = ENNReal.ofReal ((R ^ 2 + |T * T'|) ^ (k - 1)) * MeasureTheory.volume (Metric.closedBall (0 : ℂ) R) :=
        setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top

section pair

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}

theorem pairAt_tr {t : ℂ} (ht : t ≠ 0) {μ : Measure (Mt k (1 + ρ))} {μs : Measure (Mt k ρ)}
    (hmap : μs.map (B2.levM k ρ) = μ) (Φ Ψ : RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (c : Fin ρ → ℂ) :
    P5.pairAt μs (trL ht z z' π π' Φ) (trL ht z z' π π' Ψ) c = P5.pairAt μ Φ Ψ (consC t c) := by
  subst hmap
  simp only [P5.pairAt]
  rw [measurableEmbedding_levM.integral_map]
  rfl

end pair

def RadTransport : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k ρ : ℕ)
    (z z' : Fin (2 * ρ + k + 1) → ℂ) (π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)) (π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq))
    (X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))
    (L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ))
    (st : Fr.Start (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')))
    (Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ)
    (sts : Fr.Start (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))))
    (s : ℂ) (μ : Measure (Mt k (1 + ρ))) (μs : Measure (Mt k ρ)),
    inWb k ρ z → inWb k ρ z' → IsActualLevel X L → IsActualLevel Xs Ls →
    (∀ Y, st.QQ Y = s • X.QQ Y) → (∀ Y, sts.QQ Y = s • Xs.QQ Y) →
    B.IsHaarOn (Glev k (1 + ρ) (Fin.last (1 + ρ))) μ → B.IsHaarOn (Glev k ρ (Fin.last ρ)) μs →
    (∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (Matrix.of x)) ∂μ =
        ∫⁻ ζ, ENNReal.ofReal (B2.zWeight k (Tz k ρ z) (Tz k ρ z') ζ) * ψ ζ) →
    (∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k ρ z z' (Fin.last ρ) (Matrix.of x)) ∂μs =
        ∫⁻ ζ, ENNReal.ofReal (B2.zWeight k (Tz k ρ z) (Tz k ρ z') ζ) * ψ ζ) →
    ∀ t : ℂ, t ≠ 0 →
      ∃ T : RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π' →ₗ[ℂ]
          RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)),
        (∀ Φ c g, (T Φ : Fn k ρ (Wq →L[ℂ] Wp)) c g =
          (Φ : Fn k (1 + ρ) (Wq →L[ℂ] Wp)) (consC t c) (ιLev k 1 ρ g)) ∧
        (∀ (Y : ℂ) (a b : Fin 2) Φ,
          ((P5.QQi Ls sts 0 Y) a b).1 (T Φ) = T (((P5.QQi L st 1 Y) a b).1 Φ) ∧
          ((P5.QQi Ls sts 0 Y) a b).2.unop (T Φ) = T (((P5.QQi L st 1 Y) a b).2.unop Φ)) ∧
        ∀ Φ Ψ c, P5.pairAt μs (T Φ) (T Ψ) c = P5.pairAt μ Φ Ψ (consC t c)

end Formalism.FourierDecayAlt.P.PBH

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmPActualOfAnalytic
section
noncomputable section

namespace Formalism.FourierDecayAlt.P5

theorem thmPActualOfAnalytic (hE : HerAnalyticEAll) : ThmPActual :=
  thmPActualOfE Formalism.FourierDecayAlt.P.actual_zeta_smooth_alt hE

theorem thmPActualOfHerC (hAn : HerAnalyticCAll) : ThmPActual :=
  thmPActualOfZ Formalism.FourierDecayAlt.P.actual_zeta_smooth_alt hAn

theorem thmPActualOfCore (hF : HerAnalyticFAll) : ThmPActual :=
  thmPActualOfCoreMZ Formalism.FourierDecayAlt.P.actual_zeta_smooth_alt topDensMeasAll hF

end Formalism.FourierDecayAlt.P5
end
end

