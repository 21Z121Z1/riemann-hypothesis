import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenFibreExists
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0143
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0069
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0023
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0007

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Automorphic GroundTheory.Heights₂.Heights.FiniteCovolume

section Pure

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

abbrev Sg (j j' : ℕ) : Type := Fin j ⊕ Fin j'

def sgI (j j' : ℕ) : Matrix (Sg j j') (Sg j j') ℂ := fromBlocks 1 0 0 (-1)

def IsSgU (u : Matrix (Sg j j') (Sg j j') ℂ) : Prop := uᴴ * sgI j j' * u = sgI j j'

def moebW (u : Matrix (Sg j j') (Sg j j') ℂ) (W : Matrix (Fin j') (Fin j) ℂ) : Matrix (Fin j') (Fin j) ℂ :=
  (u.toBlocks₂₁ + u.toBlocks₂₂ * W) * (u.toBlocks₁₁ + u.toBlocks₁₂ * W)⁻¹

def ballPt (q : Ψ × Fin j × Fin j' ≃ Fin n) (W : Ψ → Matrix (Fin j') (Fin j) ℂ) : Fin n → ℂ :=
  fun k => W (q.symm k).1 (q.symm k).2.2 (q.symm k).2.1

def moebBall (q : Ψ × Fin j × Fin j' ≃ Fin n) (u : Ψ → Matrix (Sg j j') (Sg j j') ℂ) (t : Fin n → ℂ) : Fin n → ℂ :=
  ballPt q fun τ => moebW (u τ) (ballMat q t τ)ᵀ

end Pure

section Arch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ]

omit [IsCMField E] in

theorem intEmb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  have hc : (RingHom.ker s).comap (algebraMap ℤ (𝓞 E)) = ⊥ := by
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)
  exact (RingHom.injective_iff_ker_eq_bot s).2 (Ideal.eq_bot_of_comap_eq_bot hc)

def embOf (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (intEmb_injective s)

structure LatEmb (F : UnivFam E Ψ j j' n g Λ) where

  h : HermitianForm (maximalRealSubfield E) E (Fin (j + j') → E)

  e : Λ →+ (Fin (j + j') → E)
  e_inj : Function.Injective e
  e_smul : ∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x

  Dn : ℕ
  integral : IsDIntegral h Dn e.range
  orth : ∀ x y, h.toSesq (e x) (e y) = 0 ↔ ∀ a : 𝓞 E, F.form (a • x) y = 0

  xi : E

  c : ℝ
  c_pos : 0 < c

  eps : Ψ → ℝ
  eps_sq : ∀ τ, eps τ ^ 2 = 1
  xi_eq : ∀ τ, embOf (F.σ τ) xi = Complex.I * ((c * eps τ : ℝ) : ℂ)
  form_eq : ∀ x y, ((F.form x y : ℤ) : ℚ) = Algebra.trace ℚ E (xi * h.toSesq (e y) (e x))

  lam : Module.Basis (Fin (2 * g)) ℤ Λ

  bas : Module.Basis (Fin (2 * g)) ℝ (Ψ → Fin (j + j') → ℂ)
  bas_eq : ∀ k τ i, bas k τ i = embOf (F.σ τ) (e (lam k) i)

def plc (F : UnivFam E Ψ j j' n g Λ) (τ : Ψ) : InfinitePlace E := InfinitePlace.mk (embOf (F.σ τ))

open Classical in

def tauMat (F : UnivFam E Ψ j j' n g Λ) (a : InfinitePlace E → GL (Fin (j + j')) ℂ) (τ : Ψ) :
    Matrix (Fin (j + j')) (Fin (j + j')) ℂ :=
  if (plc F τ).embedding = embOf (F.σ τ) then (a (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ)
  else (a (plc F τ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ).map (starRingEnd ℂ)

namespace LatEmb

variable {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)

def vec (x : Λ) : Ψ → Fin (j + j') → ℂ := fun τ i => embOf (F.σ τ) (C.e x i)

def gr (τ : Ψ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ :=
  (gram C.h.toSesq (Pi.basisFun E (Fin (j + j')))).map (embOf (F.σ τ))

def sgr (τ : Ψ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ := ((C.eps τ : ℝ) : ℂ) • C.gr τ

def Fm (y y' : Ψ → Fin (j + j') → ℂ) : ℝ :=
  ∑ τ, 2 * (embOf (F.σ τ) C.xi * (star (y' τ) ⬝ᵥ (C.gr τ *ᵥ y τ))).re

def cinv (A : Matrix (Fin (j + j')) (Sg j j') ℂ) (τ : Ψ) : Matrix (Sg j j') (Fin (j + j')) ℂ :=
  sgI j j' * Aᴴ * C.sgr τ

def perExt (R : RiemLat E g Λ) : (Ψ → Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
  C.bas.constr ℝ fun k => R.P (C.lam k)

open Classical in

def pPart (R : RiemLat E g Λ) (τ : Ψ) (y : Fin (j + j') → ℂ) : Fin g → ℂ :=
  (1 / 2 : ℂ) • (C.perExt R (Pi.single τ y) - Complex.I • C.perExt R (Pi.single τ (Complex.I • y)))

open Classical in

def pBar (R : RiemLat E g Λ) (τ : Ψ) (y : Fin (j + j') → ℂ) : Fin g → ℂ :=
  (1 / 2 : ℂ) • (C.perExt R (Pi.single τ y) + Complex.I • C.perExt R (Pi.single τ (Complex.I • y)))

structure IsAdapted (R : RiemLat E g Λ) (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) : Prop where
  unit : ∀ τ, (A τ)ᴴ * C.sgr τ * A τ = sgI j j'
  ker : ∀ τ (v : Fin j → ℂ), C.pPart R τ (A τ *ᵥ Sum.elim v 0) = 0
  kerBar : ∀ τ (v : Fin j' → ℂ), C.pBar R τ (A τ *ᵥ Sum.elim 0 v) = 0

abbrev Arch : Subgroup (InfinitePlace E → GL (Fin (j + j')) ℂ) := archUnitary C.h (Pi.basisFun E (Fin (j + j')))

def tm (a : C.Arch) (τ : Ψ) : Matrix (Fin (j + j')) (Fin (j + j')) ℂ :=
  tauMat F (a : InfinitePlace E → GL (Fin (j + j')) ℂ) τ

end LatEmb

end Arch

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionDifferenceTelescopingIntegral
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Tele

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

open Classical in

def ratioWt (A B : HermLine ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  if ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 then Real.log (A.h z) - Real.log (B.h z) else 0

theorem ratioWt_of_mem {A B : HermLine ι} {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ratioWt A B z = Real.log (A.h z) - Real.log (B.h z) := if_pos hz

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem smul_mem_iff (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    (∀ k, ∃ i, (fun p : Σ k, ι k => c p.1 * z p) ⟨k, i⟩ ≠ 0) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  simp [hc]

theorem ratioWt_smul {A B : HermLine ι} (hab : A.a = B.a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ)
    (hc : ∀ k, c k ≠ 0) : ratioWt A B (fun p => c p.1 * z p) = ratioWt A B z := by
  by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
  · rw [ratioWt_of_mem hz, ratioWt_of_mem ((smul_mem_iff c z hc).2 hz), A.smul c z hc, B.smul c z hc, hab]
    have h0 : (∏ k, ‖c k‖ ^ B.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
    rw [Real.log_mul h0 (A.pos z hz).ne', Real.log_mul h0 (B.pos z hz).ne']
    ring
  · have hz' := fun h => hz ((smul_mem_iff c z hc).1 h)
    simp only [ratioWt, if_neg hz, if_neg hz']

theorem ratioWt_smooth {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    SmoothFn (ratioWt A B) := by
  have h : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Real.log (A.h z) - Real.log (B.h z))
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (ContDiffOn.log hA fun z hz => (A.pos z hz).ne').sub (ContDiffOn.log hB fun z hz => (B.pos z hz).ne')
  exact h.congr fun z hz => ratioWt_of_mem hz

def wtLine {A B : HermLine ι} (hab : A.a = B.a) : HermLine ι :=
  HermLine.ofWeight (ratioWt A B) fun c z hc => ratioWt_smul hab c z hc

theorem wtLine_a {A B : HermLine ι} (hab : A.a = B.a) : (wtLine hab).a = 0 := rfl

theorem wtLine_h {A B : HermLine ι} (hab : A.a = B.a) (z : (Σ k, ι k) → ℂ) :
    (wtLine hab).h z = Real.exp (-ratioWt A B z) := rfl

theorem wtLine_smooth {A B : HermLine ι} (hab : A.a = B.a) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (wtLine hab) :=
  Real.contDiff_exp.comp_contDiffOn (ratioWt_smooth hA hB).neg

theorem logNormRat_wtLine {A B : HermLine ι} (hab : A.a = B.a) :
    logNormRat (wtLine hab) 1 1 = ratioWt A B := by
  funext z
  simp [logNormRat, wtLine_h]

theorem tensor_wtLine_h {A B : HermLine ι} (hab : A.a = B.a) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : (A.tensor (wtLine hab)).h z = B.h z := by
  change A.h z * Real.exp (-ratioWt A B z) = B.h z
  rw [ratioWt_of_mem hz, neg_sub, Real.exp_sub, Real.exp_log (B.pos z hz), Real.exp_log (A.pos z hz)]
  field_simp [(A.pos z hz).ne']

theorem snoc_smooth {n : ℕ} {L : Fin n → HermLine ι} {B : HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    (hB : IsSmoothHerm B) (j : Fin (n + 1)) :
    IsSmoothHerm ((Fin.snoc L B : Fin (n + 1) → HermLine ι) j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last]
    exact hB
  · rw [Fin.snoc_castSucc]
    exact hL i

theorem position_metric (hML : MetricLocalStatement) (II : IntersectionSystem) (hII : IsIntersectionSystem II)
    {P : Ideal (MRing ι)} {D : ℕ} (hP : IsArithVar P (D + 1)) (L : Fin D → HermLine ι)
    (hL : ∀ j, IsSmoothHerm (L j)) (A B : HermLine ι) (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (hab : A.a = B.a) :
    II K ι P (D + 1) (Fin.snoc L B) = II K ι P (D + 1) (Fin.snoc L A) - ptsIntegral P (pot L) (ratioWt A B) := by
  have hT : IsSmoothHerm (A.tensor (wtLine hab)) := ContDiffOn.mul hA (wtLine_smooth hab hA hB)
  have mc : II K ι P (D + 1) (Fin.snoc L (A.tensor (wtLine hab))) =
      II K ι P (D + 1) (Fin.snoc L A) - ptsIntegral P (pot L) (ratioWt A B) :=
    Known.metricChange K ι (II K ι) (hII K ι) P D L A (ratioWt A B) (fun c z hc => ratioWt_smul hab c z hc)
      hP hL hA (ratioWt_smooth hA hB)
  rw [← mc]
  refine hML K ι (II K ι) (hII K ι) P (D + 1) _ _ hP (snoc_smooth hL hB) (snoc_smooth hL hT) ?_ ?_
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last, Fin.snoc_last]
      change B.a = A.a + 0
      rw [add_zero, hab]
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
  · intro j z hz
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last, Fin.snoc_last]
      exact (tensor_wtLine_h hab hz.1).symm
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]

theorem position_integral (hE : ResExistsStatement) {P J : Ideal (MRing ι)} {D : ℕ} (R : AnLogRes P J D) {X : Type}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (π : R.X → X)
    (hπ : HoloMap R.A A π) (dg : ℕ) (br : Set X) (hP : IsArithVar P (D + 1))
    (hdeg : IsDegreeOff A R.A π dg br) (L : Fin D → HermLine ι) (Φ : Fin D → LocPot X)
    (hL : ∀ j, IsSmoothHerm (L j)) (hΦ : ∀ j, IsPotential A (Φ j))
    (hS : ∀ j, SamePot R.A Set.univ (potOf R (L j)) ((Φ j).pullback π hπ.1))
    (B₁ B₂ : HermLine ι) (h₁ : IsSmoothHerm B₁) (h₂ : IsSmoothHerm B₂) (hab : B₁.a = B₂.a)
    (v : X → ℝ) (hv : Continuous v)
    (hlog : ∀ x, Real.log (B₁.h (R.lift x x)) - Real.log (B₂.h (R.lift x x)) = v (π x)) :
    ptsIntegral P (pot L) (ratioWt B₁ B₂) = dg * mInt A Φ v := by
  have h1P : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  have hm : IsMultiHomog (1 : MRing ι) (fun _ => 0) := ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_one
  have hrat : IsRatSectionOn P (wtLine hab) 1 1 := by
    refine ⟨fun _ => 0, fun _ => 0, hm, hm, h1P, h1P, fun k => ?_⟩
    change ((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = 0
    simp
  have hnull : IsNull R.A (∅ : Set R.X) := fun j => by simp
  have hlift : ∀ x ∉ (∅ : Set R.X), logNormRat (wtLine hab) 1 1 (R.lift x x) = v (π x) := by
    intro x _
    rw [logNormRat_wtLine, ratioWt_of_mem (R.mem x x (R.mem_U x)).1, hlog x]
  have hb := GlobalTheory.T.intersection_number_pullback_degree_alt hE K ι P J D R X A π hπ dg br hP hdeg L Φ hL hΦ hS (wtLine hab) 1 1 v ∅
    (wtLine_smooth hab h₁ h₂) hrat hnull hlift (mIntegrableCont A Φ hΦ v hv)
  rwa [logNormRat_wtLine] at hb

def toEnd {D : ℕ} (r : Fin (D + 1)) : Equiv.Perm (Fin (D + 1)) :=
  (finSuccEquiv' r).trans finSuccEquivLast.symm

theorem toEnd_self {D : ℕ} (r : Fin (D + 1)) : toEnd r r = Fin.last D := by
  simp [toEnd]

theorem toEnd_succAbove {D : ℕ} (r : Fin (D + 1)) (i : Fin D) : toEnd r (r.succAbove i) = i.castSucc := by
  simp [toEnd]

end GlobalTheory.CompanionTheory.Ar.PB.Tele

namespace GlobalTheory.CompanionTheory.Ar.PB

open Tele in

theorem num_sub_num : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (t t' : ℝ) (w : Fin (D + 1) → σ), 0 < t → t ≤ S.t₀ → 0 < t' → t' ≤ S.t₀ → Re.num II t w - Re.num II t' w = ∑ r : Fin (D + 1), mInt S.A (fun i => S.potT (w (r.succAbove i)) (if r.succAbove i < r then t else t')) (fun x => S.phT (w r) t x - S.phT (w r) t' x) := by
  intro hIn II hII K _ ι _ D σ _ S P Re t t' w ht ht0 ht' ht'0
  have hF := hII.1
  have hP := Re.arith
  have hpot := (GlobalTheory.T.realisation_potential_degree_compatibility hIn.resExists K ι D σ S P Re).1
  have hbasic := (anSys_open_basics D σ S).2.2.2.1
  have hsc : ∀ (b : Prop) [Decidable b], 0 < (if b then t else t') ∧ (if b then t else t') ≤ S.t₀ := by
    intro b _
    split_ifs
    exacts [⟨ht, ht0⟩, ⟨ht', ht'0⟩]
  let Wd : ℕ → Fin (D + 1) → HermLine ι := fun m j => Re.line (w j) (if (j : ℕ) < m then t else t')
  have hdeg : (Re.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Re.deg_pos.ne'
  have step : ∀ r : Fin (D + 1), II K ι P (D + 1) (Wd (r + 1)) - II K ι P (D + 1) (Wd r) =
      Re.deg * mInt S.A (fun i => S.potT (w (r.succAbove i)) (if r.succAbove i < r then t else t'))
        (fun x => S.phT (w r) t x - S.phT (w r) t' x) := by
    intro r
    let L : Fin D → HermLine ι := fun i => Re.line (w (r.succAbove i)) (if r.succAbove i < r then t else t')
    have hL : ∀ i, IsSmoothHerm (L i) := fun i => Re.line_smooth _ _ (hsc _).1 (hsc _).2
    have hsm : ∀ B : HermLine ι, IsSmoothHerm B → ∀ j : Fin (D + 1),
        IsSmoothHerm ((Fin.snoc L B : Fin (D + 1) → HermLine ι) j) := fun B hB j => snoc_smooth hL hB j
    have e1 : Wd (r + 1) = (Fin.snoc L (Re.line (w r) t) : Fin (D + 1) → HermLine ι) ∘ toEnd r := by
      funext j
      rcases Fin.eq_self_or_eq_succAbove r j with rfl | ⟨i, rfl⟩
      · rw [Function.comp_apply, toEnd_self, Fin.snoc_last]
        exact congrArg (Re.line (w _)) (if_pos (Nat.lt_succ_self _))
      · have hne : ((r.succAbove i : Fin (D + 1)) : ℕ) ≠ r := fun h => Fin.succAbove_ne r i (Fin.ext h)
        have hiff : ((r.succAbove i : Fin (D + 1)) : ℕ) < r + 1 ↔ r.succAbove i < r := by
          rw [Fin.lt_def]
          omega
        rw [Function.comp_apply, toEnd_succAbove, Fin.snoc_castSucc]
        exact congrArg (Re.line (w (r.succAbove i))) (if_congr hiff rfl rfl)
    have e0 : Wd r = (Fin.snoc L (Re.line (w r) t') : Fin (D + 1) → HermLine ι) ∘ toEnd r := by
      funext j
      rcases Fin.eq_self_or_eq_succAbove r j with rfl | ⟨i, rfl⟩
      · rw [Function.comp_apply, toEnd_self, Fin.snoc_last]
        exact congrArg (Re.line (w _)) (if_neg (lt_irrefl _))
      · rw [Function.comp_apply, toEnd_succAbove, Fin.snoc_castSucc]
        exact congrArg (Re.line (w (r.succAbove i))) (if_congr Fin.lt_def.symm rfl rfl)
    rw [e1, e0, (hF K ι).1 P (D + 1) _ (toEnd r) hP fun j => hsm _ (Re.line_smooth _ _ ht ht0) _,
      (hF K ι).1 P (D + 1) _ (toEnd r) hP fun j => hsm _ (Re.line_smooth _ _ ht' ht'0) _]
    have hab : (Re.line (w r) t).a = (Re.line (w r) t').a := (Re.line_deg _ _).trans (Re.line_deg _ _).symm
    have hsl := position_metric hIn.metricLocal II hF hP L hL _ _ (Re.line_smooth (w r) t ht ht0)
      (Re.line_smooth (w r) t' ht' ht'0) hab
    rw [hsl, sub_sub_cancel]
    refine position_integral hIn.resExists Re.R S.A Re.π Re.holo Re.deg Re.br hP Re.degree L _ hL
      (fun i => hbasic _ _ (hsc _).1 (hsc _).2) (fun i => hpot _ _ (hsc _).1 (hsc _).2) _ _
      (Re.line_smooth _ _ ht ht0) (Re.line_smooth _ _ ht' ht'0) hab _ ?_ ?_
    · exact (ReciprocityTheory.AnForm.M.PLC.continuous_of_smooth S.A ((S.reg (w r)).2.2 t ht ht0).1).sub
        (ReciprocityTheory.AnForm.M.PLC.continuous_of_smooth S.A ((S.reg (w r)).2.2 t' ht' ht'0).1)
    · intro x
      rw [Re.line_eq _ _ ht ht0, Re.line_eq _ _ ht' ht'0]
      ring
  have tel : II K ι P (D + 1) (Wd (D + 1)) - II K ι P (D + 1) (Wd 0) =
      ∑ r : Fin (D + 1), (II K ι P (D + 1) (Wd (r + 1)) - II K ι P (D + 1) (Wd r)) := by
    rw [Fin.sum_univ_eq_sum_range (fun m => II K ι P (D + 1) (Wd (m + 1)) - II K ι P (D + 1) (Wd m)) (D + 1)]
    exact (Finset.sum_range_sub (fun m => II K ι P (D + 1) (Wd m)) (D + 1)).symm
  have hWt : Wd (D + 1) = fun j => Re.line (w j) t := by
    funext j
    simp [Wd, j.is_lt]
  have hWt' : Wd 0 = fun j => Re.line (w j) t' := by
    funext j
    simp [Wd]
  simp only [Realis.num]
  rw [← sub_div, ← hWt, ← hWt', tel, Finset.sum_congr rfl fun r _ => step r, ← Finset.mul_sum,
    mul_div_cancel_left₀ _ hdeg]

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityChangeOfVariables
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem maDensity_const_eq_normSq_jacobian_mul :
    ∀ (n : ℕ) (φ ψ : (Fin n → ℂ) → ℝ) (A : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ)
      (t : Fin n → ℂ), AnalyticAt ℂ A t → AnalyticAt ℂ G t → ContDiffAt ℝ 2 φ (A t) →
      (∀ᶠ t' in 𝓝 t, ψ t' = φ (A t') + (G t').re) →
      maDensity (fun (_ : Fin n) => ψ) t =
        ‖LinearMap.det ((fderiv ℂ A t : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))‖ ^ 2 * maDensity (fun (_ : Fin n) => φ) (A t) := by
  intro n φ ψ A G t hA hG hφ hψ
  have h := GroundTheory.Heights₂.Heights.ChartEnergySwapHessian.maDensity_comp_holo
    (fun (_ : Fin n) => ψ) (fun (_ : Fin n) => φ) A G t (fun _ => hφ) hA.contDiffAt hG.contDiffAt
    (fun _ => hψ)
  rw [h, LinearMap.det_toMatrix', Complex.normSq_eq_norm_sq]

end GlobalTheory.CompanionTheory.Ar.Cusp
end

