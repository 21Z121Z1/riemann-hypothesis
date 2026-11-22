import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0172
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermPartsCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0139
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0258
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0257

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PtSizeToStd
section
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory NumberField

noncomputable section

theorem ptSize_toStd (r : ℕ) (g : ℝ) : ∀ (b : ℕ) (P : C.LPt), D.ptSize (D.toStd r g b P) = D.ptSize P
  | _, [] => rfl
  | b, (s, t) :: rest => by
    simp only [D.toStd, D.ptSize, List.map_cons, List.sum_cons] at *
    have := ptSize_toStd r g (b + s) rest
    simp only [D.ptSize] at this
    rw [this]

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def lamP (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (i : ℕ) (P : C.LPt) : ℝ :=
  √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G P) /
    (D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) P *
      √(D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i * S.sizeAt v a))

end defs

def GNSetC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (i : ℕ)
    (hi : i ≤ S.G.r) (a : List C.Letter) (P Q : C.LPt) (hP : D.IsLocPt P i) (hQ : D.IsLocPt Q i),
    KB.gN (PBL.setC S p F) v ε i a P Q =
      ((lamP S v a i P * lamP S v a i Q : ℝ) : ℂ) *
        D.formLev (p v).T (M.sgn (D.parOf S v) (p v).l0) ⟨i, by have e : (D.parOf S v).r = S.G.r := rfl; omega⟩ a
          (KB.slv (p v).T (F v ε) i hi a (D.toStd S.G.r (S.g : ℝ) 1 P) (by
            rw [← hP.2]; exact FormNormSumIdentities.ptSize_toStd S.G.r (S.g : ℝ) 1 P))
          (KB.slv (p v).T (F v ε) i hi a (D.toStd S.G.r (S.g : ℝ) 1 Q) (by
            rw [← hQ.2]; exact FormNormSumIdentities.ptSize_toStd S.G.r (S.g : ℝ) 1 Q))

def GermConst : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (b s : ℕ), 0 < S.G.g1 → 0 < S.G.g2 →
    1 ≤ b → 2 ≤ s → b + s - 1 ≤ S.G.r → ∀ h : C.LPt, D.ptSize h = b - 1 →
    ∃ μ₀ : ℝ, ∀ x D z : ℂ, x ≠ 0 → D ≠ 0 → z ^ s = D →
      (‖x‖ ^ (s - 1) * (√(KB.dlB S (b + s - 1) 1))⁻¹ * lamP S v a (b + s - 1) (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)]) *
          kapB (s - 2) =
        μ₀ * ((‖GermFibreKernels.fs S.G.r (S.g : ℝ) b (s - 1) x⁻¹‖ ^ (s - 1))⁻¹ *
          ‖GermFibreKernels.fs S.G.r (S.g : ℝ) b (s - 1) x⁻¹‖ ^ ((s - 1) * (U.Mlev S.G.k (S.G.r - (b + s - 1)) + (s - 2))) *
          ‖GermFibreKernels.fs S.G.r (S.g : ℝ) (b + s - 1) 1 (x ^ (s - 1) * D)‖ ^ (U.Mlev S.G.k (S.G.r - (b + s - 1)) - 2))) ∧
      ((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ * (√(KB.dlB S b s))⁻¹ * lamP S v a (b + s - 1) (h ++ [(s, z)]) *
          Real.pi ^ (s * (s - 1) / 2) =
        μ₀ * (‖GermFibreKernels.fs S.G.r (S.g : ℝ) (b + s - 1) 1 (x ^ (s - 1) * D) *
            GermFibreKernels.fs S.G.r (S.g : ℝ) b (s - 1) x⁻¹ ^ (s - 1)‖ ^ (U.Mlev S.G.k (S.G.r - (b + s - 1)) - 2) *
          ((s : ℝ)⁻¹ * ‖GermFibreKernels.fs S.G.r (S.g : ℝ) b s z‖ ^ ((s - 1) ^ 2)))

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPCompactOfStepDensity
section
open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

def DerivCombInt (f : ℂ → ℂ) (I : ℂ) : Prop :=
  ∃ (n K : ℕ) (C : ℝ) (Dd : Fin K → ℂ → ℂ) (j : Fin K → ℕ) (v : ∀ i, Fin (j i) → ℂ) (a : Fin K → ℂ),
    (∀ i, j i ≤ n) ∧ (∀ i, DecayData n C (Dd i)) ∧
    (∀ t, t ≠ 0 → f t = ∑ i, a i * iteratedFDeriv ℝ (j i) (Dd i) t (v i)) ∧
    ∑ i, a i * (if j i = 0 then ∫ t, Dd i t else 0) = I

theorem iteratedFDeriv_apply_of_eq_zero (m : ℕ) (u : Fin m → ℂ) (G : ℂ → ℂ) (hm : m = 0) (t : ℂ) :
    iteratedFDeriv ℝ m G t u = G t := by
  subst hm
  simp

theorem ae_ne_zero_C : ∀ᵐ t : ℂ, t ≠ 0 := by
  rw [ae_iff]
  have hset : {a : ℂ | ¬a ≠ 0} = {0} := by
    ext a
    simp
  rw [hset]
  exact measure_singleton 0

theorem ext_of_derivCombInt {f : ℂ → ℂ} {I : ℂ} (hf : DerivCombInt f I) :
    ∃ φ : ℂ → ℂ, Continuous φ ∧ (∀ t, t ≠ 0 → φ t = f t) ∧
      (∃ C' : ℝ, ∀ t, ‖φ t‖ ≤ C' * (1 + ‖t‖) ^ (-4 : ℤ)) ∧ ∫ t, φ t = I := by
  obtain ⟨n, K, C, Dd, j, v, a, hjn, hdat, hf, hI⟩ := hf
  have hc := fun i => Fou.smooth_extension_of_fourier_decay (Dd i) n C (hdat i).1 (hdat i).2.1 (hdat i).2.2.1 (hdat i).2.2.2.1 (hdat i).2.2.2.2
  choose D' hD'c hD'e hD'i hdec hder using hc
  choose Cd hCd using hdec
  refine ⟨fun t => ∑ i, a i * iteratedFDeriv ℝ (j i) (D' i) t (v i), ?_, fun t ht => ?_, ?_, ?_⟩
  · refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
    exact (continuous_eval_const (v i)).comp ((hD'c i).continuous_iteratedFDeriv (by exact_mod_cast hjn i))
  · rw [hf t ht]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    have hev : D' i =ᶠ[𝓝[Set.univ] t] Dd i := by
      rw [nhdsWithin_univ]
      filter_upwards [isOpen_compl_singleton.mem_nhds ht] with u hu
      exact hD'e i u hu
    have := hev.iteratedFDerivWithin_eq (hD'e i t ht) (j i) (𝕜 := ℝ)
    rwa [iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at this
  · refine ⟨∑ i, ‖a i‖ * (Cd i * ∏ k, ‖v i k‖), fun t => ?_⟩
    have hpow : (1 + ‖t‖) ^ (-(4 : ℝ)) = (1 + ‖t‖) ^ (-4 : ℤ) := by
      rw [← Real.rpow_intCast]; norm_num
    have hp0 : 0 ≤ (1 + ‖t‖) ^ (-4 : ℤ) := by positivity
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul]
    have h1 := (iteratedFDeriv ℝ (j i) (D' i) t).le_opNorm (v i)
    have h2 := hCd i (j i) (hjn i) t
    rw [hpow] at h2
    have hv0 : 0 ≤ ∏ k, ‖v i k‖ := Finset.prod_nonneg fun k _ => norm_nonneg _
    calc ‖a i‖ * ‖iteratedFDeriv ℝ (j i) (D' i) t (v i)‖
        ≤ ‖a i‖ * ((Cd i * (1 + ‖t‖) ^ (-4 : ℤ)) * ∏ k, ‖v i k‖) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right h2 hv0)) (norm_nonneg _)
      _ = ‖a i‖ * (Cd i * ∏ k, ‖v i k‖) * (1 + ‖t‖) ^ (-4 : ℤ) := by ring
  · have hterm : ∀ i, Integrable (fun t => a i * iteratedFDeriv ℝ (j i) (D' i) t (v i)) ∧
        ∫ t, a i * iteratedFDeriv ℝ (j i) (D' i) t (v i) = a i * (if j i = 0 then ∫ t, Dd i t else 0) := by
      intro i
      by_cases h0 : j i = 0
      · have e : (fun t => a i * iteratedFDeriv ℝ (j i) (D' i) t (v i)) = fun t => a i * D' i t := by
          funext t; rw [iteratedFDeriv_apply_of_eq_zero (j i) (v i) (D' i) h0 t]
        have hInt : Integrable (D' i) :=
          (hdat i).1.congr (ae_ne_zero_C.mono fun t ht => (hD'e i t ht).symm)
        rw [e, if_pos h0]
        exact ⟨hInt.const_mul _, by rw [integral_const_mul, hD'i i]⟩
      · have hj1 : 1 ≤ j i := Nat.one_le_iff_ne_zero.mpr h0
        obtain ⟨hIi, hzero⟩ := hder i (j i) hj1 (hjn i)
        have hIv : Integrable (fun t => iteratedFDeriv ℝ (j i) (D' i) t (v i)) :=
          (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (j i) => ℂ) ℂ (v i)).integrable_comp hIi
        have hz : ∫ t, iteratedFDeriv ℝ (j i) (D' i) t (v i) = 0 := by
          have := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (j i) => ℂ) ℂ (v i)).integral_comp_comm hIi
          simp only [ContinuousMultilinearMap.apply_apply] at this
          rw [this, hzero]
          simp
        rw [if_neg h0]
        exact ⟨hIv.const_mul _, by rw [integral_const_mul, hz, mul_zero]⟩
    rw [integral_finsetSum _ fun i _ => (hterm i).1]
    rw [← hI]
    exact Finset.sum_congr rfl fun i _ => (hterm i).2

theorem derivCombInt_congr {f g : ℂ → ℂ} {I : ℂ} (c : ℂ) (hf : DerivCombInt f I) (h : ∀ t, t ≠ 0 → g t = c * f t) :
    DerivCombInt g (c * I) := by
  obtain ⟨n, K, C, Dd, j, v, a, hj, hD, hfa, hI⟩ := hf
  refine ⟨n, K, C, Dd, j, v, fun i => c * a i, hj, hD, ?_, ?_⟩
  · intro t ht
    rw [h t ht, hfa t ht, Finset.mul_sum]
    simp only [mul_assoc]
  · rw [← hI, Finset.mul_sum]
    simp only [mul_assoc]

section Gen

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem stepDens_of_exp (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (h : ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r) (x y : Ix S → RadSp P.k P.r z z' π π'),
      InK (K l.castSucc) x → InK (K l.castSucc) y → ∀ c ∈ OmX P.r,
      DerivCombInt (ph L st μ l w x y c) (RRform L st μ l.castSucc w x y c)) :
    StepDens (S := S) P z z' π π' μ L st K l0 := by
  unfold StepDens
  intro w hw l x y hx hy c hc
  exact ext_of_derivCombInt (h w hw l x y hx hy c hc)

end Gen

def StepExp0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r), l.val = 0 →
    ∀ (x y : Ix S → RadSp P.k P.r z z' π π'),
      InK (herKc S P z z' π π' L st l0 D l.castSucc) x → InK (herKc S P z z' π π' L st l0 D l.castSucc) y →
      ∀ c ∈ OmX P.r, DerivCombInt (ph L st μ l w x y c) (RRform L st μ l.castSucc w x y c)

theorem stepDensCptAll_of_levT (hT : Formalism.FourierDecayAlt.P.PTie.LevTransportHer) (h0 : StepExp0) : StepDensCptAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ'
  refine stepDens_of_exp P z z' π π' μ L st _ l0 fun w hw l x y hx hy c hc => ?_
  obtain ⟨Di, Xi, μi, Li, sti, T, hDi, ⟨-, ⟨κ, hκ, hpair⟩, -, hwT⟩, hHer⟩ :=
    hT Wp Wq P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l.castSucc c (fun p _ => hc p)
  obtain ⟨hbT, hRR, hWO⟩ := hwT S w
  have hpos : 0 < P.r - (l.castSucc : Fin (P.r + 1)).val := by simp only [Fin.val_castSucc]; omega
  set l' : Fin (P.r - (l.castSucc : Fin (P.r + 1)).val) := ⟨0, hpos⟩ with hl'
  have hl'v : l'.val = 0 := by rw [hl']
  have e0 : ∀ h : l'.val + (l.castSucc : Fin (P.r + 1)).val < P.r,
      (⟨l'.val + (l.castSucc : Fin (P.r + 1)).val, h⟩ : Fin P.r) = l := fun h => by
    apply Fin.ext
    show l'.val + (l.castSucc : Fin (P.r + 1)).val = l.val
    rw [hl'v, Fin.val_castSucc, zero_add]
  have e1 : ∀ h : 1 + (l.castSucc : Fin (P.r + 1)).val < P.r + 1,
      (⟨1 + (l.castSucc : Fin (P.r + 1)).val, h⟩ : Fin (P.r + 1)) = l.succ := fun h => by
    apply Fin.ext
    show 1 + (l.castSucc : Fin (P.r + 1)).val = l.succ.val
    rw [Fin.val_castSucc, Fin.val_succ, add_comm]
  have e2 : ∀ h : 1 < P.r - (l.castSucc : Fin (P.r + 1)).val + 1,
      (⟨1, h⟩ : Fin (P.r - (l.castSucc : Fin (P.r + 1)).val + 1)) = l'.succ := fun h => by
    apply Fin.ext
    show 1 = l'.succ.val
    rw [Fin.val_succ, hl'v]
  have hb : Formalism.FourierDecayAlt.P.PBH.ARel T (bTl L l w) (bTl Li l' w) := by
    have := hbT l'
    simp only [e0] at this
    exact this
  have hR1 : Formalism.FourierDecayAlt.P.PBH.ARel T (RRi L st l.succ w) (RRi Li sti l'.succ w) := by
    have := hRR 1 (by simp only [Fin.val_castSucc]; omega)
    simp only [e1, e2] at this
    exact this
  have hM := Formalism.FourierDecayAlt.P.PBH.arel_mul hR1 hb
  have hSM := Formalism.FourierDecayAlt.P.PBH.arel_mul (arel_star hb) hM
  have hl0 : l'.castSucc = 0 := Fin.ext rfl
  have hx' : InK (herKc S (JC.parLev P (l.castSucc : Fin (P.r + 1))) Di.z Di.z' Di.π Di.π' Li sti l0 Di l'.castSucc)
      (fun a => T (x a)) := by
    rw [hl0]; exact fun a => hHer S (x a) (hx a)
  have hy' : InK (herKc S (JC.parLev P (l.castSucc : Fin (P.r + 1))) Di.z Di.z' Di.π Di.π' Li sti l0 Di l'.castSucc)
      (fun a => T (y a)) := by
    rw [hl0]; exact fun a => hHer S (y a) (hy a)
  have hc0 : shiftV l.castSucc c ∈ OmX (P.r - (l.castSucc : Fin (P.r + 1)).val) := fun m => hc _

  have e3 : ∀ h : 0 + (l.castSucc : Fin (P.r + 1)).val < P.r + 1,
      (⟨0 + (l.castSucc : Fin (P.r + 1)).val, h⟩ : Fin (P.r + 1)) = l.castSucc := fun h => by
    apply Fin.ext
    show 0 + (l.castSucc : Fin (P.r + 1)).val = (l.castSucc : Fin (P.r + 1)).val
    rw [zero_add]
  have e4 : ∀ h : 0 < P.r - (l.castSucc : Fin (P.r + 1)).val + 1,
      (⟨0, h⟩ : Fin (P.r - (l.castSucc : Fin (P.r + 1)).val + 1)) = l'.castSucc := fun h => by
    apply Fin.ext
    show 0 = l'.castSucc.val
    rw [Fin.val_castSucc, hl'v]
  have hR0 : Formalism.FourierDecayAlt.P.PBH.ARel T (RRi L st l.castSucc w) (RRi Li sti l'.castSucc w) := by
    have := hRR 0 (by simp only [Fin.val_castSucc]; omega)
    simp only [e3, e4] at this
    exact this
  have hD0 := h0 Wp Wq S (JC.parLev P (l.castSucc : Fin (P.r + 1))) Di.z Di.z' Di.π Di.π' Xi μi Li sti
    l0 Di hDi h1 h2 rfl rfl rfl rfl w (hWO hw) l' rfl _ _ hx' hy' _ hc0
  have hjl0 : l'.castSucc.val + (l.castSucc : Fin (P.r + 1)).val = (l.castSucc : Fin (P.r + 1)).val := by
    simp only [Fin.val_castSucc, hl'v]; omega
  have hRRf : RRform L st μ l.castSucc w x y c =
      (κ : ℂ)⁻¹ * RRform Li sti μi l'.castSucc w (fun a => T (x a)) (fun a => T (y a)) (shiftV l.castSucc c) := by
    unfold RRform
    rw [form_tr μ l.castSucc l.castSucc l'.castSucc hjl0 c c (fun _ _ => rfl) μi T κ hκ hpair]
    have eX0 : (fun a => T (act (RRi L st l.castSucc w) x a)) = act (RRi Li sti l'.castSucc w) (fun b => T (x b)) := by
      funext a; exact act_tr T hR0 x a
    rw [eX0]
  rw [hRRf]
  refine derivCombInt_congr ((κ : ℂ)⁻¹) hD0 fun t _ => ?_
  have hjl1 : l'.succ.val + (l.castSucc : Fin (P.r + 1)).val = l.succ.val := by
    simp only [Fin.val_succ, Fin.val_castSucc, hl'v]; omega
  have hupd : ∀ p : Fin P.r, p.val < (l.castSucc : Fin (P.r + 1)).val → Function.update c l t p = c p := by
    intro p hp
    rw [Function.update_of_ne]
    intro h; rw [h] at hp; simp at hp
  have eX : (fun a => T (act (RRi L st l.succ w) (act (bTl L l w) x) a)) =
      act (RRi Li sti l'.succ w) (act (bTl Li l' w) (fun b => T (x b))) := by
    funext a
    rw [act_tr T hR1 (act (bTl L l w) x) a]
    congr 1
    funext b
    exact act_tr T hb x b
  have eY : (fun a => T (act (bTl L l w) y a)) = act (bTl Li l' w) (fun b => T (y b)) := by
    funext a
    exact act_tr T hb y a
  unfold ph RRform
  rw [form_tr μ l.castSucc l.succ l'.succ hjl1 c (Function.update c l t) hupd μi T κ hκ hpair, eX, eY, mul_left_comm]
  congr 3
  funext m
  simp only [shiftV, Function.update]
  split_ifs with hA hB hB
  · subst hB
    first | (simp only [eq_rec_constant]; done) | (simp only [eq_rec_constant]; rfl) | rfl | simp
  · exfalso
    apply hB
    apply Fin.ext
    have := congrArg Fin.val hA
    change m.val + (l.castSucc : Fin (P.r + 1)).val = l.val at this
    have hcs := Fin.val_castSucc l
    rw [hl'v]
    omega
  · exfalso
    apply hA
    apply Fin.ext
    have := congrArg Fin.val hB
    rw [hl'v] at this
    change m.val + (l.castSucc : Fin (P.r + 1)).val = l.val
    have hcs := Fin.val_castSucc l
    omega
  · rfl

theorem theorem_P_compact_of_step_density (hT : Formalism.FourierDecayAlt.P.PTie.LevTransportHer) (h0 : StepExp0) : ThmPActualCpt :=
  thmPActualCpt_of_outer (stepDensCptAll_of_levT hT h0) (formIntOuterCpt_of_levT hT)

end Formalism.FourierDecayAlt.P5.HerD
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopLocalBuiltPlaces
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem topLocB : TopLocB := by
  intro hDT hVT hTR Cb Cc E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hC hB
  refine ⟨fun s hs2 hsr v => lamTop_thr hC hB s hs2 hsr v, fun F hF (v : Fin S.f) => ?_⟩
  have hB' := hB
  obtain ⟨hg1, hg2, -, -, -, -, -, -, -, -, hGo, hGr, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -⟩ := hv v
  have hCI := PBCut.cutInside_of_built hB
  intro s hs2 hsr a ha haN
  have hsr' : s ≤ S.G.r + 1 := hsr
  have ha' : D.AdmAt S v a := ha
  have haN' : a.length + C.Kst ≤ S.Ntop := haN
  set d := S.G.r + 1 - s with hd
  have hds : d + s = S.G.r + 1 := by omega
  have hd2 : d ≤ 2 * S.G.r := by omega
  obtain ⟨-, grid, hinj, hbnd, hmem, hwords, hprob, -⟩ :=
    Formalism.FourierDecayAlt.P.new_letters_admissible E Wp Wq S hGo hGr hCI v a C.Kst d ha' haN' hd2
  refine ⟨PBD.pushU grid (fun ys => KB.plusW ys a), PBD.pushTh grid (fun ys => KB.plusW ys a), hprob, ?_⟩
  intro ε hε t Y ht hY
  have hY' : ∀ P ∈ Y, D.ptSize P = d := fun P hP => by rw [hd]; exact hY P hP
  set Λ : ℝ := ∑ n : Fin C.Kst → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| with hΛ
  set C0 : ℝ := Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) * (Real.sqrt (S.T * S.T'))⁻¹
    with hC0
  set τ : ℂ := ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) : ℝ) : ℂ) *
    Complex.I ^ (s - 1) * t with hτ
  set c : ℂ := (((-1 : ℂ) ^ (s - 1) / τ) ^ C.Kst)⁻¹ with hc
  obtain ⟨hg, hk⟩ := glob_posT hB
  have hC0nn : 0 ≤ C0 := mul_nonneg (mul_nonneg (Real.exp_pos 1).le (supA_nonneg S hg hk v false))
    (inv_nonneg.2 (Real.sqrt_nonneg _))
  have hPn : ∀ n : Fin C.Kst → Fin (d + 1), 0 < ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod := by
    intro n
    refine List.prod_pos fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨b, rfl⟩ := List.mem_ofFn.1 hy
    exact abs_pos.2 ((hGo v).2.2.2.2.2 _ (Or.inl ⟨_, hmem b (n b)⟩)).2.2.1

  have hK1 := top_kernel (H := HV S v) (α := C.LPt) (Ea := Wd.Ix (Fin a.length)) (R := M.Ty (D.parOf S v))
    (N := Fin C.Kst → Fin (d + 1)) (Ew := fun n => Wd.Ix (Fin (KB.plusW (List.ofFn fun b => grid b (n b)) a).length))
    Y (fun n => KB.firstSt (List.ofFn fun b => grid b (n b))) (fun n => firstSt_inj _)
    (fun e ρ => vecT S p F v ε s t a e ρ)
    (fun n e' ρ => vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ)
    (fun e ρ => del2 S p v a e ρ) (fun n e' ρ => del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ)
    (fun e ρ => second_defect_nonneg S p v a e ρ) (fun n e' ρ => second_defect_nonneg S p v _ e' ρ)
    (fun n => ∏ b, F7.lagCo (grid b) (n b))
    (fun n => ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod) hPn c C0 C.Kst hC0nn
    (fun P hP e ρ => vecT_deg hDT hB F v ε (hF v ε hε) s hs2 t ht d hds a e ρ grid hinj
      (fun n => (hwords n).2.2.1) P (hY' P hP))
    (fun n e ρ => by
      have h := second_defect_plus_word_le S p v a e ρ C0 hC0nn (List.ofFn fun b => grid b (n b))
        (rhyp_nodes hTR hB hC v a ha' haN' grid hmem n (hwords n).2.2.1 e ρ)
      rwa [List.length_ofFn] at h)

  change Loe Y (fun P Q => KB.gN (setC S p F) v ε (S.G.r + 1) a (P ++ [(s, t)]) (Q ++ [(s, t)]))
    (fun P Q => (((‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) : ℝ) : ℂ) *
      KB.mix (setC S p F) v ε (S.G.r + 1) (PBD.pushU grid fun ys => KB.plusW ys a)
        (PBD.pushTh grid fun ys => KB.plusW ys a) (P ++ [(s, t)]) (Q ++ [(s, t)]))
  have hsz : ∀ P ∈ Y, D.ptSize P + s = S.G.r + 1 := fun P hP => by rw [hY' P hP]; omega
  have hgpos := g_pos_of_built hB
  have hrd := PBD.rd_pos' E
  have hΓ : 0 < ΓS S (S.G.r + 1) := PBD.gamLev_pos _ _ _ _ (by unfold D.kapG; positivity) (by unfold D.deG; positivity) _
  have hsa : 0 < S.sizeAt v a := sizeAt_pos S hGo v a ha'
  set ka : ℝ := 1 / (ΓS S (S.G.r + 1) * S.sizeAt v a) with hka
  have hka0 : 0 ≤ ka := by positivity
  have hΛpos : 0 < Λ := lam_sum_pos grid hinj

  have h1 := loe_diag (omT S s t) (loe_smul ka hka0 hK1)
  have h1' : Loe Y (fun P Q => KB.gN (setC S p F) v ε (S.G.r + 1) a (P ++ [(s, t)]) (Q ++ [(s, t)]))
      (fun P Q => (((‖c‖ ^ 2 * Λ * C0 ^ C.Kst) * Λ : ℝ) : ℂ) * ∑ n : Fin C.Kst → Fin (d + 1),
        ((|∏ b, F7.lagCo (grid b) (n b)| / Λ : ℝ) : ℂ) * ((omT S s t P : ℂ) * (omT S s t Q : ℂ) *
          (((ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod : ℝ) : ℂ) *
            ∑ e', ∑ ρ, (del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ : ℂ) *
              gramH (vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ) P Q))) := by
    refine loe_congr (fun P hP Q hQ => ?_) (fun P _ Q _ => ?_) h1
    · rw [gN_top hVT hB F v ε s hs2 t a P Q (hsz P hP) (hsz Q hQ)]
      ring
    · exact mix_alg _ _ _ _ _ _ _ _ hΛpos.ne' fun n => (hPn n).ne'

  have hmixY : ∀ P ∈ Y, ∀ Q ∈ Y, KB.mix (setC S p F) v ε (S.G.r + 1) (PBD.pushU grid fun ys => KB.plusW ys a)
      (PBD.pushTh grid fun ys => KB.plusW ys a) (P ++ [(s, t)]) (Q ++ [(s, t)]) =
      ∑ n : Fin C.Kst → Fin (d + 1),
        ((|∏ b, F7.lagCo (grid b) (n b)| / Λ : ℝ) : ℂ) * ((omT S s t P : ℂ) * (omT S s t Q : ℂ) *
          (((ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod : ℝ) : ℂ) *
            ∑ e', ∑ ρ, (del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ : ℂ) *
              gramH (vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ) P Q)) := by
    intro P hP Q hQ
    refine (mix_pushT (setC S p F) v ε (S.G.r + 1) grid (fun ys => KB.plusW ys a) _ _).trans ?_
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [thGrid_eq, ← hΛ, gN_top hVT hB F v ε s hs2 t _ P Q (hsz P hP) (hsz Q hQ), sizeAt_plusW]
    have hk : 1 / (ΓS S (S.G.r + 1) * (((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod *
        S.sizeAt v a)) = ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod := by
      rw [hka]; have := (hPn n).ne'; field_simp
    rw [hk]
    ring
  have hpsdY := psd_mixω Y (omT S s t) (fun n : Fin C.Kst → Fin (d + 1) => |∏ b, F7.lagCo (grid b) (n b)| / Λ)
    (fun n => ka / ((List.ofFn fun b => grid b (n b)).map fun y => |S.P v y|).prod)
    (fun n => div_nonneg (abs_nonneg _) hΛpos.le) (fun n => div_nonneg hka0 (hPn n).le)
    (fun n P Q => ∑ e', ∑ ρ, (del2 S p v (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ : ℂ) *
      gramH (vecT S p F v ε s t (KB.plusW (List.ofFn fun b => grid b (n b)) a) e' ρ) P Q)
    (fun n => psd_dsum Y _ (fun e' ρ => second_defect_nonneg S p v _ e' ρ) _)
  have hX : 0 ≤ (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) - ‖c‖ ^ 2 * Λ * C0 ^ C.Kst * Λ := by
    have hlv : 0 < ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) :=
      zpow_pos (by positivity) _
    set lv : ℝ := ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r ((1 + d : ℕ) : ℤ) (s : ℤ) with hlvdef
    have hτn : ‖τ‖ = lv * ‖t‖ := by
      rw [hτ, norm_mul, norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hlv.le]
    have hcn : ‖c‖ = ‖τ‖ ^ C.Kst := by
      rw [hc, norm_inv, norm_pow, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div, inv_pow, inv_inv]
    set B : ℝ := (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ d with hBdef
    have hΛB : Λ ≤ B ^ C.Kst := lam_sum_le grid B hbnd
    have hlenpos := lenI_posT hB (Fin.pos v)
    have hB0 : 0 ≤ B := by
      rw [hBdef, len_eq_lenI']; exact pow_nonneg (div_nonneg (by positivity) hlenpos.le) _

    have hA0 : 0 ≤ (2 * Real.pi / S.G.g) ^ (-(2 * S6.nuBlock S.G.r ((S.G.r + 2 - s : ℕ) : ℤ)
        ((S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ)))) * Real.exp 1 *
        (28 * S.G.N / S.G.lenI) ^ (2 * (S.G.r + 2 - s - 1)) * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) *
        (√(S.T * S.T'))⁻¹ := by
      have : 0 ≤ S.G.N := by unfold Sz.Glob.N; positivity
      have := supA_nonneg S hg hk v false
      positivity
    have hlam2 : lamTop S (S.G.r + 2 - s) v ^ 2 = lv ^ 2 * B ^ 2 * C0 := by
      unfold lamTop
      rw [Real.sq_sqrt hA0]
      have e1 : ((S.G.r + 2 - s : ℕ) : ℤ) = ((1 + d : ℕ) : ℤ) := by rw [hd]; push_cast; omega
      have e2 : (S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ) = (s : ℤ) := by push_cast; omega
      have e3 : (S.g : ℝ) = S.G.g := by unfold C.HidaSetting.g Sz.Glob.g; push_cast; ring
      have e4 : S.G.r + 2 - s - 1 = d := by omega
      rw [e2, e1, e4, hlvdef, zpow_sq_eq _ (by positivity), inv_div, e3, hBdef, ← pow_mul, ntop_eq_N'',
        len_eq_lenI', hC0, mul_comm d 2]
      ring
    have hfin : ‖c‖ ^ 2 * Λ * C0 ^ C.Kst * Λ ≤ (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) := by
      have e5 : (‖t‖ * lamTop S (S.G.r + 2 - s) v) ^ (2 * C.Kst) = (‖t‖ ^ 2 * (lv ^ 2 * B ^ 2 * C0)) ^ C.Kst := by
        rw [pow_mul, mul_pow (‖t‖) (lamTop S (S.G.r + 2 - s) v) 2, hlam2]
      rw [e5, hcn, hτn]
      have hΛ0 : 0 ≤ Λ := hΛpos.le
      have hsq : Λ * Λ ≤ B ^ C.Kst * B ^ C.Kst := mul_le_mul hΛB hΛB hΛ0 (pow_nonneg hB0 _)
      calc ((lv * ‖t‖) ^ C.Kst) ^ 2 * Λ * C0 ^ C.Kst * Λ = ((lv * ‖t‖) ^ C.Kst) ^ 2 * C0 ^ C.Kst * (Λ * Λ) := by ring
        _ ≤ ((lv * ‖t‖) ^ C.Kst) ^ 2 * C0 ^ C.Kst * (B ^ C.Kst * B ^ C.Kst) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = (‖t‖ ^ 2 * (lv ^ 2 * B ^ 2 * C0)) ^ C.Kst := by ring
    linarith
  have h3 := loe_scale hpsdY hX
  exact loe_trans h1' (loe_congr (fun _ _ _ _ => rfl) (fun P hP Q hQ => by rw [hmixY P hP Q hQ]) h3)

end

end Formalism.FourierDecayAlt.P.PBL

theorem Formalism.FourierDecayAlt.P.top_local_built_places : Formalism.FourierDecayAlt.P.PBL.TopLocB := Formalism.FourierDecayAlt.P.PBL.topLocB
end

