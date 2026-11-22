import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0052
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0054
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJD
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

def GlobCoef {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq) (d : ℝ) : Prop :=
  ∀ Tm ∈ Θ, B.CkOn ⊤ (B.GV k r) Tm.coef ∧ B.CkOn ⊤ (B.GV k r) Tm.coefAdj ∧
    ∀ m : ℕ, ∃ Cb : ℝ, ∀ u w : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) →
      u.length + w.length ≤ m → ∀ g ∈ B.GV k r,
        ‖B.dLR u w Tm.coef g‖ ≤ Cb * B.gN g ^ d ∧ ‖B.dLR u w Tm.coefAdj g‖ ≤ Cb * B.gN g ^ d

def nDim (k r : ℕ) : ℝ := ((2 * r + k + 1 : ℕ) : ℝ)

def bddHat (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) : Set (MA.A P (MA.DQ P)) :=
  {x | ∃ b ∈ Submonoid.closure (MA.bddSet P L), ∃ X ∈ MA.hatSet P L, x = b * X}

def JDHatBdd : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 ≤ P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ X ∈ MA.hatSet P L, ∀ b ∈ Submonoid.closure (MA.bddSet P L), X * b ∈ Submodule.span ℂ (bddHat P L)

def JDHatOp : Prop :=
  ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
      (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r),
      IsFrame S T v e → IsGauge S T v e → MA.IsModelLevel (D.parOf S v) (MA.DQ (D.parOf S v)) L →
      ∀ X ∈ MA.hatSet (D.parOf S v) L,
        ∃ ts : List (MA.A (D.parOf S v) (MA.DQ (D.parOf S v)) × B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))),
          (∀ t ∈ ts, t.1 ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) ∧ B.SmoothCoef (B.GPos (T v).base) t.2 ∧
            B.Commutes (T v).base (B.GPos (T v).base) t.2 ∧
            GlobCoef t.2 (Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r) ∧ (B.opOrder t.2 : ℝ) ≤ Cc * nDim S.G.k S.G.r) ∧
          ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
            MA.actA (D.parOf S v) X (trJ S T v e J) =
              (ts.map fun t => MA.actA (D.parOf S v) t.1 (trJ S T v e (B.opApply t.2 J))).sum

def JDJComm : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (d A : ℝ), 0 ≤ d →
      B.SmoothCoef (B.GPos (T v).base) Θ → B.Commutes (T v).base (B.GPos (T v).base) Θ → GlobCoef Θ d →
      Cc * ((S.G.r : ℝ) + 1) * nDim S.G.k S.G.r ^ 2 + 6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) + d ≤ A →
      ∀ F : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), B.CkOn ⊤ (B.GV S.G.k S.G.r) F →
        (∀ m : ℕ, B.InCC A m F) → B.JF (T v).base F ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
        B.JF (T v).base (B.opApply Θ F) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) ∧
          ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
            B.opApply Θ (B.JF (T v).base F) (B.gq (T v).base x) = B.JF (T v).base (B.opApply Θ F) (B.gq (T v).base x)

def JDCCLower : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Θ : B.DiffOp k r Wp Wq) (d A : ℝ),
    0 ≤ d → GlobCoef Θ d → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F → (∀ m : ℕ, B.InCC A m F) →
      B.CkOn ⊤ (B.GV k r) (B.opApply Θ F) ∧ ∀ m : ℕ, B.InCC (A - d) m (B.opApply Θ F)

def TransferSquareIntegrable : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e →
      ∀ A : ℝ, Cc * ((S.G.r : ℝ) + 1) ^ 2 * nDim S.G.k S.G.r ≤ A →
      ∀ F : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), B.CkOn ⊤ (B.GV S.G.k S.G.r) F →
        (∀ m : ℕ, B.InCC A m F) → B.JF (T v).base F ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
        ∀ π, MeasureTheory.Integrable
          (fun q => ‖MA.evQ (D.parOf S v) (trJ S T v e (B.JF (T v).base F) π) q‖ ^ 2) (MA.mu0 (D.parOf S v).r (D.parOf S v).TT)

def BoundedOperatorsSquareIntegrable : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ b ∈ Submonoid.closure (MA.bddSet P L), ∀ u : M.Ty P → MA.SmQ P.r P.TT,
      (∀ π, MeasureTheory.Integrable (fun q => ‖MA.evQ P (u π) q‖ ^ 2) (MA.mu0 P.r P.TT)) →
      ∀ π, MeasureTheory.Integrable (fun q => ‖MA.evQ P (MA.actA P b u π) q‖ ^ 2) (MA.mu0 P.r P.TT)

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLam
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

section cfg

variable (c : Sz.Cfg)

theorem cfg_v_sub (i : ℕ) : c.v i - c.v (i + 1) = 4 * c.Del := by
  simp only [Sz.Cfg.v]
  push_cast
  ring

theorem cfg_v_ge_vlast (hok : c.Ok) (i : ℕ) (hi : i + 1 ≤ c.k) : c.vlast ≤ c.v i := by
  have hD := hok.hDel
  have hi' : (i : ℝ) + 1 ≤ (c.k : ℝ) := by exact_mod_cast hi
  simp only [Sz.Cfg.v]
  push_cast
  nlinarith

theorem cfg_v_lt (hok : c.Ok) {i j : ℕ} (hij : i < j) : c.v j < c.v i := by
  have hD := hok.hDel
  have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
  simp only [Sz.Cfg.v]
  push_cast
  nlinarith

theorem cfg_b_lt (hok : c.Ok) : ∀ {j j' : ℕ}, 1 ≤ j → j < j' → j' ≤ c.m → c.b j < c.b j' := by
  intro j j' hj hjj' hj'm
  induction j' with
  | zero => omega
  | succ n ih =>
    have hg := hok.hgap n (by omega) (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjj' with h | h
    · have := ih h (by omega)
      linarith
    · subst h
      linarith

theorem cfg_b_ge_one (hok : c.Ok) {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ c.m) : 1 ≤ c.b j := by
  rcases Nat.lt_or_ge 1 j with h | h
  · have := cfg_b_lt c hok (le_refl 1) h hjm
    linarith [hok.hb1]
  · have e : j = 1 := by omega
    subst e
    exact hok.hb1

theorem cfg_interlaces (r : ℕ) (hm : c.m = 2 * r + 2) (hk : 2 ≤ c.k) (hok : c.Ok) (de : ℕ → ℝ)
    (hde : ∀ i, de i = 0 ∨ de i = 1) :
    C7.LamInterlaces c.k r (c.u de) (fun s : Fin (c.k + 2 * r + 1) => c.lam ((s : ℕ) + 1)) := by
  have hk4 := hok.hk
  have hD := hok.hDel
  have hv0 := hok.hv0
  have hb1 := hok.hb1
  have ha := hok.ha
  have hkR : (4 : ℝ) ≤ c.k := by exact_mod_cast hk4
  have hlamv : ∀ s : ℕ, s < c.k → c.lam s = c.v s := fun s hs => by
    rw [Sz.Cfg.lam, if_pos hs]
  have hlamb : ∀ s : ℕ, ¬ s < c.k → c.lam s = -c.b (s + 1 - c.k) := fun s hs => by
    rw [Sz.Cfg.lam, if_neg hs]
  have hu1 : c.u de 1 = c.a := by rw [Sz.Cfg.u, if_pos rfl]
  have huk : c.u de c.k = c.ulast := by rw [Sz.Cfg.u, if_neg (by omega), if_pos rfl]
  have hum : ∀ j : ℕ, j ≠ 1 → j ≠ c.k → c.u de j = c.v (j - 1) - 1 / 2 - de (j - 1) * c.Del :=
    fun j h1 h2 => by rw [Sz.Cfg.u, if_neg h1, if_neg h2]
  have hde0 : ∀ j, 0 ≤ de j * c.Del ∧ de j * c.Del ≤ c.Del := fun j => by
    rcases hde j with h | h <;> simp [h] <;> linarith
  have hul : c.ulast = if c.top then -c.bp else c.vlast - 1 / 2 := rfl
  have hvk : c.v (c.k - 1) = c.vlast := by
    simp only [Sz.Cfg.v]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  refine ⟨?_, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · intro s t hst
    have hst' : (s : ℕ) < t := hst
    have ht := t.isLt
    show c.lam ((t : ℕ) + 1) < c.lam ((s : ℕ) + 1)
    by_cases h1 : (t : ℕ) + 1 < c.k
    · rw [hlamv _ h1, hlamv _ (by omega)]
      exact cfg_v_lt c hok (by omega)
    · rw [hlamb _ h1]
      by_cases h2 : (s : ℕ) + 1 < c.k
      · rw [hlamv _ h2]
        have := cfg_b_ge_one c hok (j := (t : ℕ) + 1 + 1 - c.k) (by omega) (by omega)
        have := cfg_v_ge_vlast c hok ((s : ℕ) + 1) (by omega)
        linarith
      · rw [hlamb _ h2]
        have := cfg_b_lt c hok (j := (s : ℕ) + 1 + 1 - c.k) (j' := (t : ℕ) + 1 + 1 - c.k)
          (by omega) (by omega) (by omega)
        linarith
  · show c.lam ((i : ℕ) + 1) < c.u de ((i : ℕ) + 1)
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | h0
    · rw [h0, zero_add, hlamv 1 (by omega), hu1]
      have : 0 < 4 * (c.k : ℝ) * c.Del := by
        have := mul_le_mul hkR hD zero_le_one (by linarith)
        linarith
      linarith
    · by_cases h2 : (i : ℕ) + 1 < c.k
      · rw [hlamv _ h2, hum _ (by omega) (by omega), Nat.add_sub_cancel]
        have := cfg_v_sub c (i : ℕ)
        have := hde0 (i : ℕ)
        linarith
      · have e : (i : ℕ) + 1 = c.k := by omega
        rw [hlamb _ h2, e, Nat.add_sub_cancel_left, huk, hul]
        split_ifs with htp
        · have := (hok.htop htp).2
          linarith
        · linarith
  · show c.u de ((i : ℕ) + 2) < c.lam ((i : ℕ) + 1)
    rw [hlamv _ (by omega)]
    by_cases h2 : (i : ℕ) + 2 = c.k
    · have e : (i : ℕ) + 1 = c.k - 1 := by omega
      rw [h2, huk, hul, e, hvk]
      split_ifs with htp
      · have := (hok.htop htp).1
        linarith
      · linarith
    · have e : (i : ℕ) + 2 - 1 = (i : ℕ) + 1 := by omega
      rw [hum _ (by omega) h2, e]
      have := hde0 ((i : ℕ) + 1)
      linarith

end cfg

theorem eigenvalue_configuration_interlaces : LamCfgInterlaces := by
  intro E _ _ _ Wp Wq _ _ _ _ S hk hok hw hw' v
  exact ⟨cfg_interlaces (S.G.place (S.pl v)) S.G.r rfl hk (hok v) S.de hw.1,
    cfg_interlaces (S.G.place (S.pl v)) S.G.r rfl hk (hok v) S.de' hw'.1⟩

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DiscreteSeriesFormOneReduction
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.DDSmoothness

open Formalism.FourierDecayAlt.ThreeDimData

theorem smooth_K_finite_form_one_side : AtFormOneOfSteps := by
  intro hSch hBC hNI hBB hSh hKF hZ hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  obtain ⟨hBC1, -, -, -⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hσ hG
  have hw0n : w0 ≠ 0 := by
    obtain ⟨P, -, hn1, -⟩ := hw0
    intro h0; rw [h0, norm_zero] at hn1; exact zero_ne_one hn1
  have hdeg : ∀ x : H, x ≠ 0 → PI.BesselPeriodGGP.fdegH μG σ x = d := fun x hx => fdeg_eq hd hSd hx
  have hmu := muSof_facts hW hN
  have hae := ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  have hKs : ∀ v : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v →
      v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := fun v hv => hIn.2.2.1 k r ε lam H σ hlam hσ v hv
  by_cases hnz : ∃ x ∈ DDsp σ w0, ∃ y ∈ DDsp σ w0, be z c π σ μW μN x y ≠ 0
  · obtain ⟨l, hl, hx1, hid⟩ := hSh hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    have hK := hKF hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS l hl hx1 hid
    refine ⟨l, hl, fun x hx v hv => ⟨hBC1 x hx v (Or.inr hv), hK v hv x hx⟩, ?_⟩
    intro x hx hx0 v hv
    have hNv := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v (Or.inr hv) (l v)).1
    rw [hK v hv v (hKs v hv)] at hNv
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] at hNv
    rw [hdeg w0 hw0n] at hNv
    rw [hdeg x hx0]
    refine l2_norm_scaling _ _ (l v) _ _ (by positivity) hNv (hae.mono fun g hg => ?_)
    rw [hK v hv _ (PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε lam H σ hσ x hx _ hg)]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  · push_neg at hnz
    have h0 := hZ hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    refine ⟨fun _ => 0, bessel_zero, fun x hx v hv => ⟨hBC1 x hx v (Or.inr hv), ?_⟩,
      fun x _ _ v _ => by simp⟩
    show be z c π σ μW μN x v = _
    rw [h0 v hv x hx]
    ext ξ; simp

end Formalism.FourierDecayAlt.P.DDSmoothness

namespace Formalism.FourierDecayAlt.P

theorem discrete_series_form_one_reduction : Formalism.FourierDecayAlt.ThreeDimData.DDFormOneOfSteps := DDSmoothness.discrete_form_one_side

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.JacobianAeNonzero
section
open Matrix Formalism.FourierDecayAlt MeasureTheory
open scoped ENNReal

namespace Formalism.FourierDecayAlt.P

namespace RootChangeOfVariables

lemma jac (c : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ : ℂ →L[ℝ] ℂ).det = Complex.normSq c := by
  have e : ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ : ℂ →L[ℝ] ℂ).toLinearMap =
      (LinearMap.mulLeft ℂ c).restrictScalars ℝ := by
    ext x; simp [mul_comm]
  rw [ContinuousLinearMap.det, e, LinearMap.det_restrictScalars, LinearMap.det_mulLeft,
    Algebra.norm_complex_apply]

lemma ae_ne_zero : ∀ᵐ D : ℂ, D ∈ {D : ℂ | D ≠ 0} := by
  rw [ae_iff]
  have : {a : ℂ | ¬ a ∈ {D : ℂ | D ≠ 0}} = {0} := by ext a; simp
  rw [this, measure_singleton]

end RootChangeOfVariables

open RootChangeOfVariables

theorem rootCOV_statement : C2.RootCOV := by
  intro s φ hs hφ
  have hs0 : s ≠ 0 := by omega
  haveI : NeZero s := ⟨hs0⟩

  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℂ → ℂ, ρ = fun D => D ^ ((s : ℂ)⁻¹) := ⟨_, rfl⟩
  have hρn : ∀ D, ρ D ^ s = D := fun D => by rw [hρ]; exact Complex.cpow_nat_inv_pow D hs0
  have hρm : Measurable ρ := by rw [hρ]; exact measurable_id.pow_const _
  set S : Set ℂ := {z | z ^ s ≠ 0 ∧ ρ (z ^ s) = z} with hS
  have hSm : MeasurableSet S := by
    apply MeasurableSet.inter
    · exact (measurableSet_singleton (0 : ℂ)).compl.preimage (measurable_id.pow_const s)
    · exact measurableSet_eq_fun (hρm.comp (measurable_id.pow_const s)) measurable_id
  have hS0 : ∀ z ∈ S, z ≠ 0 := fun z hz e => hz.1 (by rw [e]; exact zero_pow hs0)

  obtain ⟨wt, hwt⟩ : ∃ wt : ℂ → ℝ≥0∞, wt = fun z => ENNReal.ofReal (((s : ℕ) : ℝ) ^ 2 * ‖z‖ ^ (2 * (s - 1))) :=
    ⟨_, rfl⟩
  have hwtm : Measurable wt := by
    rw [hwt]; exact Measurable.ennreal_ofReal (measurable_const.mul ((continuous_norm.pow _).measurable))

  have hL : ∀ ψ : ℂ → ℝ≥0∞, ∫⁻ D, ψ (ρ D) = ∫⁻ z in S, wt z * ψ z := by
    intro ψ
    have himg : (fun z : ℂ => z ^ s) '' S = {D : ℂ | D ≠ 0} := by
      ext D; constructor
      · rintro ⟨z, hz, rfl⟩; exact hz.1
      · intro hD
        refine ⟨ρ D, ⟨?_, ?_⟩, hρn D⟩
        · rw [hρn]; exact hD
        · rw [hρn]
    have hinj : Set.InjOn (fun z : ℂ => z ^ s) S := by
      intro z1 h1 z2 h2 e
      rw [← h1.2, ← h2.2]; simp only at e; rw [e]
    have hder : ∀ z ∈ S, HasFDerivWithinAt (fun z : ℂ => z ^ s)
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ((s : ℂ) * z ^ (s - 1))).restrictScalars ℝ) S z :=
      fun z _ => ((hasDerivAt_pow s z).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    have step1 : ∫⁻ D, ψ (ρ D) = ∫⁻ D in {D : ℂ | D ≠ 0}, ψ (ρ D) := by
      rw [Measure.restrict_eq_self_of_ae_mem ae_ne_zero]
    rw [step1, ← himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm hder hinj]
    apply setLIntegral_congr_fun hSm
    intro z hz
    dsimp only
    rw [jac, hz.2, hwt]
    congr 2
    rw [abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_mul, map_pow, Complex.normSq_natCast,
      Complex.normSq_eq_norm_sq, ← pow_mul, sq]

  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / s) with hζ
  have hprim : IsPrimitiveRoot ζ s := Complex.isPrimitiveRoot_exp s hs0
  have hζn : ∀ j, ‖ζ ^ j‖ = 1 := fun j => by rw [norm_pow, hprim.norm'_eq_one hs0, one_pow]
  have hζ0 : ∀ j, ζ ^ j ≠ 0 := fun j h => by have := hζn j; rw [h, norm_zero] at this; exact zero_ne_one this
  have hrot : ∀ (j : ℕ) (G : ℂ → ℝ≥0∞), ∫⁻ z in S, G (ζ ^ j * z) = ∫⁻ y in (fun z => ζ ^ j * z) '' S, G y := by
    intro j G
    have hder : ∀ z ∈ S, HasFDerivWithinAt (fun z : ℂ => ζ ^ j * z)
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (ζ ^ j * 1)).restrictScalars ℝ) S z :=
      fun z _ => (((hasDerivAt_id z).const_mul (ζ ^ j)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    have hinj : Set.InjOn (fun z : ℂ => ζ ^ j * z) S := fun z1 _ z2 _ e => mul_left_cancel₀ (hζ0 j) e
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm hder hinj]
    apply setLIntegral_congr_fun hSm
    intro z _
    dsimp only
    rw [jac, mul_one, Complex.normSq_eq_norm_sq, hζn, one_pow, abs_one, ENNReal.ofReal_one, one_mul]

  have hroots : ∀ D, ((Polynomial.nthRoots s D).map φ).sum = ∑ j ∈ Finset.range s, φ (ζ ^ j * ρ D) := by
    intro D
    rw [hprim.nthRoots_eq (hρn D), Multiset.map_map]
    rfl
  simp only [hroots]
  have hmeas : ∀ j ∈ Finset.range s, Measurable (fun D => φ (ζ ^ j * ρ D)) :=
    fun j _ => hφ.comp (measurable_const.mul hρm)
  rw [lintegral_finset_sum _ hmeas]
  have hterm : ∀ j ∈ Finset.range s, ∫⁻ D, φ (ζ ^ j * ρ D) =
      ∫⁻ y in (fun z => ζ ^ j * z) '' S, wt y * φ y := by
    intro j _
    rw [hL (fun z => φ (ζ ^ j * z)), ← hrot j (fun y => wt y * φ y)]
    apply setLIntegral_congr_fun hSm
    intro z _
    simp only [hwt, norm_mul, hζn, one_mul]
  rw [Finset.sum_congr rfl hterm]
  have hTm : ∀ j, MeasurableSet ((fun z => ζ ^ j * z) '' S) := fun j =>
    (MeasurableEquiv.mulLeft₀ (ζ ^ j) (hζ0 j)).measurableSet_image.mpr hSm
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range s)) (fun j => (fun z => ζ ^ j * z) '' S) := by
    intro j hj j' hj' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro y ⟨z, hz, rfl⟩ ⟨z', hz', e⟩
    have h1 : ∀ i : ℕ, (ζ ^ i) ^ s = 1 := fun i => by
      rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    have hpow : z' ^ s = z ^ s := by
      have := congrArg (fun t => t ^ s) e
      simp only [mul_pow, h1, one_mul] at this
      exact this
    have hzz : z' = z := by rw [← hz'.2, ← hz.2, hpow]
    rw [hzz] at e
    have := mul_right_cancel₀ (hS0 z hz) e
    exact hne (hprim.pow_inj (Finset.mem_range.mp hj') (Finset.mem_range.mp hj) this).symm
  rw [← lintegral_biUnion_finset hdisj (fun j _ => hTm j)]
  have hunion : (⋃ j ∈ Finset.range s, (fun z => ζ ^ j * z) '' S) = {y : ℂ | y ≠ 0} := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨j, _, z, hz, rfl⟩
      exact mul_ne_zero (hζ0 j) (hS0 z hz)
    · intro hy
      set z0 := ρ (y ^ s) with hz0
      have hz0n : z0 ^ s = y ^ s := hρn _
      have hz0S : z0 ∈ S := ⟨by rw [hz0n]; exact pow_ne_zero s hy, by rw [hz0n]⟩
      have hz00 := hS0 z0 hz0S
      have h1 : (y / z0) ^ s = 1 := by rw [div_pow, hz0n, div_self (pow_ne_zero s hy)]
      obtain ⟨j, hj, hjeq⟩ := hprim.eq_pow_of_pow_eq_one h1
      exact ⟨j, hj, z0, hz0S, by rw [hjeq]; field_simp⟩
  rw [hunion, Measure.restrict_eq_self_of_ae_mem ae_ne_zero, hwt]

theorem slice_density_independent : C2.SliceDensityIndependent := fourth_weight_density_of_parts rootCOV_statement linear_change_of_variables_bis

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelSystemAdmissibleSize
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Finset

noncomputable section

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem prod_lamCfg (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (Y : ℝ) : ∏ s, (Y + lamCfg S v s) = S.P v Y := by
  show ∏ s : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1),
      (Y + (S.G.place (S.pl v)).lam ((s : ℕ) + 1)) = (S.G.place (S.pl v)).P Y
  have hm : (S.G.place (S.pl v)).k + (S.G.place (S.pl v)).m - 1 =
      (D.parOf S v).k + 2 * (D.parOf S v).r + 1 := by
    show S.G.k + (2 * S.G.r + 2) - 1 = S.G.k + 2 * S.G.r + 1
    omega
  rw [Sz.Cfg.P, hm]
  have e1 : ∏ s : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1),
      (Y + (S.G.place (S.pl v)).lam ((s : ℕ) + 1)) =
      ∏ i ∈ Finset.range ((D.parOf S v).k + 2 * (D.parOf S v).r + 1),
        (Y + (S.G.place (S.pl v)).lam (i + 1)) :=
    Fin.prod_univ_eq_prod_range (fun i => Y + (S.G.place (S.pl v)).lam (i + 1)) _
  rw [e1, Finset.range_eq_Ico, Finset.prod_Ico_add' (fun i => Y + (S.G.place (S.pl v)).lam i), zero_add]
  rfl

theorem level_system_admissible_size (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (hA : D.AdmAt S v a)
    (hI : ∀ x ∈ a, x.2 ∈ Set.Icc (S.cutLo v) (S.cutHi v)) (l : ℕ)
    (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
    (j : M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT) (c : LE.Cut) (Lb : ℝ) :
    (MA.sysQ (D.parOf S v) l L j (lamCfg S v) (S.cutLo v) (S.cutHi v) Lb c S.Ntop).admitted a ∧
      (MA.sysQ (D.parOf S v) l L j (lamCfg S v) (S.cutLo v) (S.cutHi v) Lb c S.Ntop).size a = S.sizeAt v a := by
  obtain ⟨w, rfl⟩ := hA
  refine ⟨⟨fun x hx => hI x hx, ?_⟩, ?_⟩
  · rw [List.pairwise_iff_getElem]
    intro i i' hi hi' hii
    have := w.2.1.2 v i i' hi hi' (Nat.ne_of_lt hii) 0 (by norm_num) (by norm_num)
    simpa using this
  · show ((w.1 v).map fun x => |∏ s, (x.2 + lamCfg S v s)|).prod = _
    rw [C.HidaSetting.sizeAt]
    simp only [prod_lamCfg]

end defs

end

end Formalism.FourierDecayAlt.P.CutMP
end

