import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0089
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0087
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeRegularEntries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0047
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0091
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0081
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesAtPoint
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.An

section Loc

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E} {z : E}

def LocAn (S : Set E) (z : E) (φ : E → ℂ) : Prop :=
  ∃ f : E → ℂ, AnalyticAt ℂ f z ∧ ∀ᶠ w in 𝓝[S] z, φ w = f w

theorem LocAn.of_analyticAt {φ : E → ℂ} (h : AnalyticAt ℂ φ z) : LocAn S z φ :=
  ⟨φ, h, Eventually.of_forall fun _ => rfl⟩

theorem LocAn.const (c : ℂ) : LocAn S z fun _ => c := .of_analyticAt analyticAt_const

theorem LocAn.add {φ ψ : E → ℂ} (h : LocAn S z φ) (h' : LocAn S z ψ) : LocAn S z fun w => φ w + ψ w := by
  obtain ⟨f, hf, e⟩ := h
  obtain ⟨g, hg, e'⟩ := h'
  refine ⟨fun w => f w + g w, hf.add hg, ?_⟩
  filter_upwards [e, e'] with w a b
  rw [a, b]

theorem LocAn.mul {φ ψ : E → ℂ} (h : LocAn S z φ) (h' : LocAn S z ψ) : LocAn S z fun w => φ w * ψ w := by
  obtain ⟨f, hf, e⟩ := h
  obtain ⟨g, hg, e'⟩ := h'
  refine ⟨fun w => f w * g w, hf.mul hg, ?_⟩
  filter_upwards [e, e'] with w a b
  rw [a, b]

theorem LocAn.sum {σ : Type} (s : Finset σ) {φ : σ → E → ℂ} (h : ∀ i ∈ s, LocAn S z (φ i)) :
    LocAn S z fun w => ∑ i ∈ s, φ i w := by
  induction s using Finset.induction_on with
  | empty => simpa using LocAn.const (S := S) (z := z) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem LocAn.prod {σ : Type} (s : Finset σ) {φ : σ → E → ℂ} (h : ∀ i ∈ s, LocAn S z (φ i)) :
    LocAn S z fun w => ∏ i ∈ s, φ i w := by
  induction s using Finset.induction_on with
  | empty => simpa using LocAn.const (S := S) (z := z) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem LocAn.det {n : ℕ} {A : E → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, LocAn S z fun w => A w a b) :
    LocAn S z fun w => (A w).det := by
  simp only [Matrix.det_apply']
  exact LocAn.sum _ fun σ _ => (LocAn.const _).mul (LocAn.prod _ fun i _ => h _ _)

theorem LocAn.minor {N : ℕ} {A : E → Matrix (Fin N) (Fin N) ℂ} (h : ∀ a b, LocAn S z fun w => A w a b)
    (I J : Finset (Fin N)) : LocAn S z fun w => minorIJ (A w) I J := by
  unfold minorIJ
  split_ifs with e
  · exact LocAn.det fun a b => h _ _
  · exact LocAn.const 0

end Loc

section Val

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E} {z : E}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem eval_eq_zero_of_mem {b : (Σ k, ι k) → ℂ} {f : MRing ι} (hf : f ∈ mCoordIdeal b) :
    eval b (map (Int.castRingHom ℂ) f) = 0 := by
  have h0 : mConeMap b f = 0 := hf
  have e : ∀ f : MRing ι, eval (fun _ => (1 : ℂ)) (mConeMap b f) = eval b (map (Int.castRingHom ℂ) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp [map_add, hp, hq]
    | mul_X p q hp =>
      have e1 : eval (fun _ => (1 : ℂ)) (mConeMap b (X q)) = b q := by simp [mConeMap]
      rw [map_mul, map_mul, hp, e1, map_mul, map_mul, map_X, eval_X]
  rw [← e, h0, map_zero]

theorem notMem_of_eval_ne_zero {b : (Σ k, ι k) → ℂ} {f : MRing ι} (hf : eval b (map (Int.castRingHom ℂ) f) ≠ 0) :
    f ∉ mCoordIdeal b := fun h => hf (eval_eq_zero_of_mem h)

theorem coord_ne_zero_of_notMem {b : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal b) :
    b q ≠ 0 := fun e => h (by
  show mConeMap b (X q) = 0
  rw [mConeMap, aeval_X, e, map_zero, zero_mul])

theorem analyticAt_eval {σ : Type} {b : E → σ → ℂ} (hb : ∀ q, AnalyticAt ℂ (fun w => b w q) z)
    (p : MvPolynomial σ ℤ) : AnalyticAt ℂ (fun w => eval (b w) (map (Int.castRingHom ℂ) p)) z := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq =>
    have e : (fun w => eval (b w) (map (Int.castRingHom ℂ) (p + q))) = fun w =>
        eval (b w) (map (Int.castRingHom ℂ) p) + eval (b w) (map (Int.castRingHom ℂ) q) := by
      funext w; rw [map_add, map_add]
    rw [e]; exact hp.add hq
  | mul_X p q hp =>
    have e : (fun w => eval (b w) (map (Int.castRingHom ℂ) (p * X q))) = fun w =>
        eval (b w) (map (Int.castRingHom ℂ) p) * b w q := by
      funext w; rw [map_mul, map_mul, map_X, eval_X]
    rw [e]; exact hp.mul (hb q)

theorem regAt_eventually {x : (Σ k, ι k) → Ω} {b : E → (Σ k, ι k) → ℂ} (hb : ∀ q, AnalyticAt ℂ (fun w => b w q) z)
    {s : Ω} (hs : RegAt x (mCoordIdeal (b z)) s) : ∀ᶠ w in 𝓝 z, RegAt x (mCoordIdeal (b w)) s := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  filter_upwards [(analyticAt_eval hb h).continuousAt.eventually_ne (ValRing.eval_ne_zero_of_notMem hh hn)] with w hw
  exact ⟨d, g, h, hg, hh, notMem_of_eval_ne_zero hw, heq⟩

theorem locAn_valAt {x : (Σ k, ι k) → Ω} {b : E → (Σ k, ι k) → ℂ} (hb : ∀ q, AnalyticAt ℂ (fun w => b w q) z)
    (hpt : ∀ w ∈ S, b w ∈ mcPts (mCoordIdeal x)) (hz : z ∈ S) {s : Ω} (hs : RegAt x (mCoordIdeal (b z)) s) :
    LocAn S z fun w => valAt x s (b w) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  have h0 := ValRing.eval_ne_zero_of_notMem hh hn
  have hx := ValRing.aeval_ne_zero_of_notMem (hpt z hz) hh hn
  refine ⟨fun w => eval (b w) (map (Int.castRingHom ℂ) g) / eval (b w) (map (Int.castRingHom ℂ) h),
    (analyticAt_eval hb g).div (analyticAt_eval hb h) h0, ?_⟩
  filter_upwards [nhdsWithin_le_nhds ((analyticAt_eval hb h).continuousAt.eventually_ne h0), self_mem_nhdsWithin]
    with w hw hwS
  exact valAt_eq (hpt w hwS) ⟨d, g, h, hg, hh, hx, heq, hw, rfl⟩

end Val

section Good

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : E}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Finite Ψ] {N j : ℕ}

theorem goodAt_eventually (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk)
    {b : E → (Σ k, baseIdx ι M.blk k) → ℂ} (hb : ∀ q, AnalyticAt ℂ (fun w => b w q) z)
    (hg : M.GoodAt F (mCoordIdeal (b z))) : ∀ᶠ w in 𝓝 z, M.GoodAt F (mCoordIdeal (b w)) := by
  obtain ⟨h1, h2, h3⟩ := hg
  have A : ∀ᶠ w in 𝓝 z, ∀ k, (X ⟨k, F.c k⟩ : MRing (baseIdx ι M.blk)) ∉ mCoordIdeal (b w) := by
    refine eventually_all.2 fun k => ?_
    filter_upwards [(hb ⟨k, F.c k⟩).continuousAt.eventually_ne (coord_ne_zero_of_notMem (h1 k))] with w hw
    refine notMem_of_eval_ne_zero ?_
    simpa using hw
  have B : ∀ᶠ w in 𝓝 z, ∀ q I, RegAt M.x (mCoordIdeal (b w)) (F.u q I) ∧ RegAt M.x (mCoordIdeal (b w)) (F.u' I q) :=
    eventually_all.2 fun q => eventually_all.2 fun I =>
      (regAt_eventually hb (h2 q I).1).and (regAt_eventually hb (h2 q I).2)
  have C : ∀ᶠ w in 𝓝 z, ∀ p, M.blk p = none → F.υ p ≠ 0 ∧ RegAt M.x (mCoordIdeal (b w)) (F.υ p) ∧
      RegAt M.x (mCoordIdeal (b w)) (F.υ p)⁻¹ := by
    refine eventually_all.2 fun p => ?_
    by_cases hp : M.blk p = none
    · filter_upwards [regAt_eventually hb (h3 p hp).2.1, regAt_eventually hb (h3 p hp).2.2] with w a c
      exact fun _ => ⟨(h3 p hp).1, a, c⟩
    · exact Eventually.of_forall fun _ h => absurd h hp
  filter_upwards [A, B, C] with w a c d
  exact ⟨a, c, d⟩

end Good

section Img

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

theorem analyticAt_coord (z : (Σ k, ι' k) → ℂ) (q : Σ k, ι' k) :
    AnalyticAt ℂ (fun w : (Σ k, ι' k) → ℂ => w q) z :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι' k) => ℂ) q).analyticAt z

theorem locAn_img {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    {z : (Σ k, ι' k) → ℂ} {F' : FrameData ι' Ψ N M'.Ω M'.blk} {F : FrameData ι Ψ N M.Ω M.blk}
    (hz : z ∈ mcPts (mCoordIdeal y'))
    (hp1 : ∀ w ∈ mcPts (mCoordIdeal y'), basePart M'.blk w ∈ mcPts (mCoordIdeal M'.x))
    (hp2 : ∀ w ∈ mcPts (mCoordIdeal y'), basePart M'.blk w ∘ Cv.v ∈ mcPts (mCoordIdeal M.x))
    (hF' : M'.IsFrame F') (hF : M.IsFrame F)
    (hg' : M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)))
    (hg : M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v))) (q : Σ k, ι k) :
    LocAn (mcPts (mCoordIdeal y')) z fun w => img Cv F' F w q := by
  have hb : ∀ q, AnalyticAt ℂ (fun w => basePart M'.blk w q) z := fun q => analyticAt_coord z _
  have hbv : ∀ q, AnalyticAt ℂ (fun w => (basePart M'.blk w ∘ Cv.v) q) z := fun q => hb _
  obtain ⟨k, m⟩ := q
  by_cases hk : ∀ p, M.blk p ≠ some k
  · refine .of_analyticAt ?_
    have e : (fun w => img Cv F' F w ⟨k, m⟩) = fun w => basePart M'.blk w (Cv.v ⟨⟨k, hk⟩, m⟩) := by
      funext w
      exact congrFun (img_base Cv F' F w) ⟨⟨k, hk⟩, m⟩
    rw [e]
    exact hb _
  · obtain ⟨p, hp⟩ : ∃ p, M.blk p = some k := by simpa using hk
    obtain ⟨k', hp'⟩ := exists_blk_cover M' hp
    simp only [img_step Cv F' F _ hp hp' m]
    unfold stepCoord
    refine LocAn.sum _ fun I _ => (locAn_valAt hbv hp2 hz (hg.2.1 _ I).1).mul (LocAn.sum _ fun I' _ => ?_)
    by_cases hI : IsStepRows N j p.2 I'
    · simp only [if_pos hI]
      refine (LocAn.minor (fun a c => ?_) I I').mul
        (LocAn.sum _ fun m' _ => (locAn_valAt hb hp1 hz (hg'.2.1 _ I').2).mul (.of_analyticAt (analyticAt_coord z _)))
      exact locAn_valAt hb hp1 hz (Cv.agree _ (hp1 z hz) F' F hF' hF hg' hg p.1 a c).1
    · simp only [if_neg hI]
      exact LocAn.const 0

end Img

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), z ∈ mcPts (mCoordIdeal y') → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v)) → ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y'), M'.GoodAt F' (mCoordIdeal (basePart M'.blk z')) ∧ M.GoodAt F (mCoordIdeal (basePart M'.blk z' ∘ Cv.v)) ∧ f z' = CovMap.LocImg.img Cv F' F z' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z F' F hz hF' hF hg' hg
  have hp1 := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').1
  have hp2 : ∀ w ∈ mcPts (mCoordIdeal y'), basePart M'.blk w ∘ Cv.v ∈ mcPts (mCoordIdeal M.x) := fun w hw =>
    (GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ (hp1 w hw)).1
  have hb : ∀ q, AnalyticAt ℂ (fun w => basePart M'.blk w q) z := fun q => analyticAt_coord z _
  have hbv : ∀ q, AnalyticAt ℂ (fun w => (basePart M'.blk w ∘ Cv.v) q) z := fun q => hb _
  choose f hf hev using locAn_img Cv hz hp1 hp2 hF' hF hg' hg
  have e1 : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ (fun w q => f q w) w :=
    (analyticAt_pi_iff.2 hf).eventually_analyticAt
  have e2 : ∀ᶠ w in 𝓝 z, w ∈ mcPts (mCoordIdeal y') → ∀ q, img Cv F' F w q = f q w :=
    eventually_nhdsWithin_iff.1 (eventually_all.2 hev)
  obtain ⟨V, hV, hVo, hzV⟩ := eventually_nhds_iff.1
    (e1.and (e2.and ((goodAt_eventually M' F' hb hg').and (goodAt_eventually M F hbv hg))))
  refine ⟨V, fun w q => f q w, hVo, hzV, fun w hw => (hV w hw).1, fun w hw => ?_⟩
  obtain ⟨-, a, c, d⟩ := hV w hw.1
  exact ⟨c, d, funext fun q => (a hw.2 q).symm⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.An
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesPullback
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.StepExpr

section Minors

variable {R S : Type} [CommRing R] [CommRing S] {N : ℕ}

theorem minor_map (f : R →+* S) (A : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (A.map f) I J = f (minorIJ A I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]; rfl
  · rw [map_zero]

theorem minor_one_self (I : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) R) I I = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem detFac_one' (j : ℕ) (i : Fin N) : detFac j i (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  simp [detFac, minor_one_self]

theorem stepCols_ne_empty (j : ℕ) (i : Fin N) : stepCols N j i ≠ ∅ := by
  have hi := i.2
  apply Finset.Nonempty.ne_empty
  by_cases h : (i : ℕ) + 1 ≤ j
  · exact ⟨⟨N - j, by omega⟩, by simp [stepCols, h]; omega⟩
  · exact ⟨⟨0, by omega⟩, by simp [stepCols, h]; omega⟩

theorem detFac_ne_zero' {E : Type} [Field E] {j : ℕ} (hj : j ≤ N) (i : Fin N) {T : Matrix (Fin N) (Fin N) E}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) : detFac j i T ≠ 0 := by
  have h := ((GlobalTheory.T.block_diagonal_minor_vanishing E N j i hj).2.2.2 T T⁻¹ hT (hT.inv (isUnit_iff_ne_zero.2 hd))).2
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd), detFac_one'] at h
  intro h0
  rw [h0, zero_mul] at h
  exact one_ne_zero h

theorem det_map_ne {A B : Type} [Field A] [Field B] (f : A →+* B) {T : Matrix (Fin N) (Fin N) A} (hd : T.det ≠ 0) :
    (T.map f).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero f).2 hd

theorem inv_map' {A B : Type} [Field A] [Field B] (f : A →+* B) {T : Matrix (Fin N) (Fin N) A} (hd : T.det ≠ 0) :
    (T⁻¹).map f = (T.map f)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd)]
  exact Matrix.map_one _ (map_zero f) (map_one f)

end Minors

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem flag_in_frame_blockDiag {E : Type} [Field E] {T g : Matrix (Fin N) (Fin N) E}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) (hg : IsBlockDiag j g) : IsBlockDiag j (T⁻¹ * g) :=
  (hT.inv (isUnit_iff_ne_zero.2 hd)).mul hg

theorem read_minor (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (hF : M.IsFrame F)
    (p : Ψ × Fin N) (k : K) (hk : M.blk p = some k) (I' : Finset (Fin N)) (hI' : IsStepRows N j p.2 I') :
    detFac j p.2 ((F.T p.1).map (algebraMap M.Ω Φ)) *
        ∑ m : ι k, algebraMap M.Ω Φ (F.u' I' ⟨k, m⟩) * y ⟨k, m⟩ =
      algebraMap M.Ω Φ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') *
        minorIJ (((F.T p.1).map (algebraMap M.Ω Φ))⁻¹ * M.g p.1) I' (stepCols N j p.2) := by
  set α : M.Ω →+* Φ := algebraMap M.Ω Φ with hα
  set T := (F.T p.1).map α with hTdef
  have hdet : T.det ≠ 0 := det_map_ne α (hF.1 p.1).2
  have hTb : IsBlockDiag j T := (hF.1 p.1).1.map α
  set h := T⁻¹ * M.g p.1 with hh
  have hb : IsBlockDiag j h := flag_in_frame_blockDiag hTb hdet (M.g_block p.1)
  have hTh : T * h = M.g p.1 := by
    rw [hh, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hdet)]
  have hy : ∀ m : ι k, detFac j p.2 T * y ⟨k, m⟩ =
      α (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * ∑ I, α (F.u ⟨k, m⟩ I) * minorIJ h I (stepCols N j p.2) := fun m => by
    have := GlobalTheory.T.block_minor_sum_frame_identity K ι Φ y Ψ N j M Φ α F hF p k hk m h hb
    rw [← hTdef, hTh] at this
    rw [M.y_step p k hk m]
    exact this
  have hv : ∀ I, ¬ IsStepRows N j p.2 I → minorIJ h I (stepCols N j p.2) = 0 := fun I hI =>
    ((GlobalTheory.T.block_diagonal_minor_vanishing Φ N j p.2 M.j_le).2.1 h I hb hI).resolve_right (stepCols_ne_empty j p.2)
  calc detFac j p.2 T * ∑ m : ι k, α (F.u' I' ⟨k, m⟩) * y ⟨k, m⟩
      = ∑ m : ι k, α (F.u' I' ⟨k, m⟩) * (detFac j p.2 T * y ⟨k, m⟩) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
    _ = α (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * ∑ I, (∑ m : ι k, α (F.u' I' ⟨k, m⟩) * α (F.u ⟨k, m⟩ I)) *
          minorIJ h I (stepCols N j p.2) := by
        simp only [hy, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun m _ => by ring
    _ = _ := by
        congr 1
        have hs : ∀ I, IsStepRows N j p.2 I → ∑ m : ι k, α (F.u' I' ⟨k, m⟩) * α (F.u ⟨k, m⟩ I) = if I' = I then 1 else 0 := fun I hI => by
          have := hF.2.2.1 p k hk I' I hI' hI
          simp only [← map_mul, ← map_sum, this]
          split_ifs <;> simp
        rw [Finset.sum_eq_single I' (fun I _ hne => ?_) (by simp), hs I' hI', if_pos rfl, one_mul]
        by_cases hI : IsStepRows N j p.2 I
        · rw [hs I hI, if_neg (Ne.symm hne), zero_mul]
        · rw [hv I hI, mul_zero]

theorem transPt_eq_smul_sum : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), M'.IsFrame F' → M.IsFrame F → (∀ k, M'.x ⟨k, F'.c k⟩ ≠ 0) → (∀ k, M.x ⟨k, F.c k⟩ ≠ 0) → ∀ (p : Ψ × Fin N) (k : K) (k' : K'), M.blk p = some k → M'.blk p = some k' → ∃ c : Φ', c ≠ 0 ∧ ∀ m : ι k, transPt Cv ⟨k, m⟩ = c * ∑ m' : ι' k', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) * y' ⟨k', m'⟩ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv F' F hF' hF hc' hc p k k' hk hk'
  set α : M'.Ω →+* Φ' := algebraMap M'.Ω Φ' with hα
  set ρ : M.Ω →+* Φ' := α.comp Cv.φ with hρ
  set T' := (F'.T p.1).map α with hT'
  set T := (F.T p.1).map ρ with hT
  have hdetφ : ((F.T p.1).map Cv.φ).det ≠ 0 := det_map_ne Cv.φ (hF.1 p.1).2
  have hdet' : T'.det ≠ 0 := det_map_ne α (hF'.1 p.1).2
  have hdet : T.det ≠ 0 := det_map_ne ρ (hF.1 p.1).2
  have hTb' : IsBlockDiag j T' := (hF'.1 p.1).1.map α
  have hTb : IsBlockDiag j T := (hF.1 p.1).1.map ρ
  set h' := T'⁻¹ * M'.g p.1 with hh'
  set h₀ := T⁻¹ * M'.g p.1 with hh₀
  have hb' : IsBlockDiag j h' := flag_in_frame_blockDiag hTb' hdet' (M'.g_block p.1)
  have hb₀ : IsBlockDiag j h₀ := flag_in_frame_blockDiag hTb hdet (M'.g_block p.1)
  have hTh₀ : T * h₀ = M'.g p.1 := by
    rw [hh₀, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hdet)]
  have hμ' : α (∏ k'', M'.x ⟨k'', F'.c k''⟩ ^ M'.b p k'') ≠ 0 :=
    (map_ne_zero α).2 (Finset.prod_ne_zero_iff.2 fun k'' _ => zpow_ne_zero _ (hc' k''))
  have hμ : ρ (∏ k'', M.x ⟨k'', F.c k''⟩ ^ M.b p k'') ≠ 0 :=
    (map_ne_zero ρ).2 (Finset.prod_ne_zero_iff.2 fun k'' _ => zpow_ne_zero _ (hc k''))
  have hd' : detFac j p.2 T' ≠ 0 := detFac_ne_zero' M'.j_le p.2 hTb' hdet'
  have hd : detFac j p.2 T ≠ 0 := detFac_ne_zero' M.j_le p.2 hTb hdet
  set μ' := α (∏ k'', M'.x ⟨k'', F'.c k''⟩ ^ M'.b p k'') with hμ'def
  set μ := ρ (∏ k'', M.x ⟨k'', F.c k''⟩ ^ M.b p k'') with hμdef
  set d' := detFac j p.2 T' with hd'def
  set d := detFac j p.2 T with hddef
  have hread : ∀ I', IsStepRows N j p.2 I' → minorIJ h' I' (stepCols N j p.2) =
      d' / μ' * ∑ m' : ι' k', α (F'.u' I' ⟨k', m'⟩) * y' ⟨k', m'⟩ := fun I' hI' => by
    have := read_minor M' F' hF' p k' hk' I' hI'
    rw [div_mul_eq_mul_div, eq_div_iff hμ', mul_comm]
    exact this.symm
  have hv : ∀ I, ¬ IsStepRows N j p.2 I → minorIJ h' I (stepCols N j p.2) = 0 := fun I hI =>
    ((GlobalTheory.T.block_diagonal_minor_vanishing Φ' N j p.2 M'.j_le).2.1 h' I hb' hI).resolve_right (stepCols_ne_empty j p.2)
  have hmat : h₀ = (trMat Cv F' F p.1).map α * h' := by
    have e : ((F.T p.1).map Cv.φ).map α = T := Matrix.ext fun _ _ => rfl
    rw [trMat, Matrix.map_mul, inv_map' α hdetφ, e, ← hT', hh', Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hdet')]
  have e3 : ∀ I, minorIJ h₀ I (stepCols N j p.2) =
      ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2),
        α (minorIJ (trMat Cv F' F p.1) I I') * minorIJ h' I' (stepCols N j p.2) := fun I => by
    rw [hmat, (GlobalTheory.T.block_diagonal_minor_vanishing Φ' N j p.2 M'.j_le).1]
    simp only [minor_map]
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun I' _ hI' => ?_).symm
    rw [hv I' (by simpa using hI'), mul_zero]
  have e1 : ∀ m : ι k, d * transPt Cv ⟨k, m⟩ =
      μ * ∑ I, α (Cv.φ (F.u ⟨k, m⟩ I)) * minorIJ h₀ I (stepCols N j p.2) := fun m => by
    have := GlobalTheory.T.block_minor_sum_frame_identity K ι Φ y Ψ N j M Φ' ρ F hF p k hk m h₀ hb₀
    rw [← hT, hTh₀] at this
    rw [transPt_step Cv p k hk m]
    exact this
  refine ⟨μ / d * (d' / μ'), mul_ne_zero (div_ne_zero hμ hd) (div_ne_zero hd' hμ'), fun m => ?_⟩
  have htr : transPt Cv ⟨k, m⟩ = μ / d * ∑ I, α (Cv.φ (F.u ⟨k, m⟩ I)) * minorIJ h₀ I (stepCols N j p.2) := by
    rw [div_mul_eq_mul_div, eq_div_iff hd, mul_comm]
    exact e1 m
  have hR : ∑ m' : ι' k', α (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) * y' ⟨k', m'⟩ =
      ∑ I, ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2),
        α (Cv.φ (F.u ⟨k, m⟩ I)) * α (minorIJ (trMat Cv F' F p.1) I I') *
          ∑ m' : ι' k', α (F'.u' I' ⟨k', m'⟩) * y' ⟨k', m'⟩ := by
    simp only [coE, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m' _ => by ring
  rw [htr, mul_assoc, hR]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [e3 I, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I' hI' => ?_
  rw [hread I' (Finset.mem_filter.1 hI').2]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.StepExpr
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeRegularEntriesStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_change_regular_entries : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal M.x) → M.IsFrame F₁ → M.IsFrame F₂ → M.GoodAt F₁ (mCoordIdeal zb) → M.GoodAt F₂ (mCoordIdeal zb) → ∀ (τ : Ψ) (r s : Fin N), RegAt M.x (mCoordIdeal zb) (((F₁.T τ)⁻¹ * F₂.T τ) r s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.FrameReg.change_regular | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.FrameReg.change_regular | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.FrameReg.change_regular <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfProjectionAndFibreDim
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim : PFCoordStatement → FibreDimStatement → GenDegStatement := by
  first | exact @PositivityTheory.HtPt.Aig.genDeg | exact PositivityTheory.HtPt.Aig.genDeg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetImEqZeroStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_det_im_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (u : Fin m → Fin g → ℂ), (R.gram u).det.im = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.GramReal.gram_det_im_zero | exact GlobalTheory.CompanionTheory.Ar.Cusp.GramReal.gram_det_im_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.GramReal.gram_det_im_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetMulNormSqDetStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_det_mul_normSq_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (u f : Fin m → Fin g → ℂ) (T : Matrix (Fin m) (Fin m) ℂ), (∀ i, f i = ∑ j, T j i • u j) → (R.gram f).det = ((‖T.det‖ ^ 2 : ℝ) : ℂ) * (R.gram u).det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange.gram_det_change | exact GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange.gram_det_change | (intros; apply GlobalTheory.CompanionTheory.Ar.RiemannLimit.GramChange.gram_det_change <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetPosOfSemidefiniteTransversalStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_det_pos_of_semidefinite_transversal : ∀ (g : ℕ) (Hb : Matrix (Fin g) (Fin g) ℂ) (U : Submodule ℂ (Fin g → ℂ)) (k : ℕ) (q : Fin k → Fin g → ℂ), Hb.IsHermitian → (∀ v : Fin g → ℂ, 0 ≤ (v ⬝ᵥ Hb *ᵥ star v).re ∧ ((v ⬝ᵥ Hb *ᵥ star v).re = 0 → v ∈ U)) → (∀ l : Fin k → ℂ, ∑ c, l c • q c ∈ U → l = 0) → 0 < (Matrix.of fun c c' => q c' ⬝ᵥ Hb *ᵥ star (q c)).det.re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef.gram_det_re_pos | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef.gram_det_re_pos | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef.gram_det_re_pos <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HilbertSamuelG7OfMoriwakiStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_samuel_G7_of_moriwaki : MoriwakiHSStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.G7.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.smallGenerated_count_upper_of_moriwakiHS | exact GlobalTheory.CompanionTheory.Ar.Giv.smallGenerated_count_upper_of_moriwakiHS | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.smallGenerated_count_upper_of_moriwakiHS <;> assumption)
end

