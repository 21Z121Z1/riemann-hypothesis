import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0052
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0134
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0054
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0109
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0058
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0140
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0087
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0061
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0050
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0135
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0064
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0065
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFourth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasureLimitStatementHolds
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0025
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0141
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0032
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0099
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0120
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0138
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0055
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeHeightLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0100
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionSixth
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.DensW

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fst_orbit {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (fstPt k₀ z) (fstPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (some k), fun k => hc _, rfl⟩

theorem snd_orbit {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (sndPt k₀ z) (sndPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => if k = k₀ then c none else c (some k), fun k => by dsimp only; split_ifs <;> exact hc _, ?_⟩
  funext ⟨k, m⟩
  by_cases e : k = k₀
  · subst e
    simp [sndPt, v₁_self]
  · simp [sndPt, v₁_ne (p := ⟨k, m⟩) e, e]

theorem same_block {N j : ℕ} {a b ca cb : Fin N} (hj : j ≤ N) (hb : (b : ℕ) = a + 1)
    (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ)) (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) :
    ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) := by
  have := b.2
  have := cb.2
  unfold lastCol at hca
  split_ifs at hca <;> omega

theorem blockDiag_transv {N j : ℕ} {ca cb : Fin N} (h : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t) := by
  intro r s hrs
  have hne : r ≠ s := fun e => hrs (by rw [e])
  rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, Matrix.single_apply]
  split_ifs with e
  · obtain ⟨rfl, rfl⟩ := e
    exact absurd h hrs
  · rfl

theorem lowerUni_transv {N : ℕ} {ca cb : Fin N} (h : ca < cb) (t : ℂ) :
    IsLowerUni (1 + Matrix.single cb ca t) := by
  refine ⟨fun r => ?_, fun r s hrs => ?_⟩
  · rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply, if_neg, add_zero]
    rintro ⟨rfl, e⟩
    exact h.ne e
  · rw [Matrix.add_apply, Matrix.one_apply_ne hrs.ne, zero_add, Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact absurd h (not_lt.2 hrs.le)

theorem minor_analytic {m N : ℕ} {V : Set (Fin m → ℂ)} {A : (Fin m → ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hA : ∀ r s, AnalyticOnNhd ℂ (fun u => A u r s) V) (I J : Finset (Fin N)) :
    AnalyticOnNhd ℂ (fun u => minorIJ (A u) I J) V := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e, Matrix.det_apply]
    refine Finset.analyticOnNhd_fun_sum _ fun σ _ => ?_
    simp only [Units.smul_def, zsmul_eq_mul]
    exact analyticOnNhd_const.mul (Finset.analyticOnNhd_fun_prod _ fun i _ => hA _ _)
  · simp only [dif_neg e]
    exact analyticOnNhd_const

theorem mul_analytic {m N : ℕ} {V : Set (Fin m → ℂ)} {A : (Fin m → ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hA : ∀ r s, AnalyticOnNhd ℂ (fun u => A u r s) V) (C : Matrix (Fin N) (Fin N) ℂ) (r s : Fin N) :
    AnalyticOnNhd ℂ (fun u => (A u * C) r s) V := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticOnNhd_fun_sum _ fun i _ => (hA r i).mul analyticOnNhd_const

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem wVec_some (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (t : ℂ) (k : K) (m : ι k) :
    wVec M F b h τ a k₀ ca cb t ⟨some k, m⟩ = flagPt M F b h ⟨k, m⟩ := rfl

theorem plk_ne_zero (M : FlagModel y Ψ N j) {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) {b : BM.Rb.X} (hb : b ∈ BM.O l)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (hh : ∀ τ', IsBlockDiag j (h τ'))
    (hm : ∀ (τ' : Ψ) (i : Fin N), IsProperStep N j i → minorIJ (h τ') (stepCols N j i) (stepCols N j i) ≠ 0)
    (p : Ψ × Fin N) : plk M (BM.F l) (bvec BM l b) (flagPt M (BM.F l) (bvec BM l b) h) p ≠ 0 := by
  have hg := bvec_good K ι Φ y Ψ N j M n BM l b hb
  cases hp : M.blk p with
  | none => simp [plk, hp]
  | some k =>
    rw [plk_flagPt K ι Φ y Ψ N j M (BM.F l) _ h p k (BM.isFrame l) hg.1 hg.2.1 hh hp]
    refine hm _ _ ?_
    by_contra hn
    rw [(M.blk_none p).2 hn] at hp
    cases hp

theorem not_mem_top (z : (Σ k, ι k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing ι)) := fun h => by
  have := h.2 1 trivial
  simp at this

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.DensW

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_w : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∀ (l : Fin BM.q) (x : RW.X), FA.pr (q 0 x) ∈ BM.O l → ∀ V, IsOpen V → x ∈ V → ∃ x' ∈ V, FA.pr (q 0 x') ∈ BM.O l \ bdry BM.s ∧ ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x'))) (fstPt k₀ (RW.lift x' x')) p ≠ 0 ∧ FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x'))) (sndPt k₀ (RW.lift x' x')) p ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hab hblk hca hcb RW q _ h0 _ _ l x hx V hV hxV
  have harith : IsArithVar (mCoordIdeal y) (d + 2) := FA.Re.arith
  have hsb := FC.DensW.same_block M.j_le hb hab hca hcb
  have hlt : ca < cb := Fin.lt_def.2 (by omega)
  have hbase : ∀ w : RW.X, SameOrbit (basePart M.blk (fstPt k₀ (RW.lift w w)))
      (BM.Rb.lift (FA.pr (q 0 w)) (FA.pr (q 0 w))) := by
    intro w
    obtain ⟨x₀, hx₀⟩ := (FC.re_pi_bijective K ι Φ y Ψ N j M n d BM FA).2 (q 0 w)
    have e1 := h0 w x₀ hx₀
    have e2 := FA.pr_eq x₀
    rw [hx₀] at e2
    exact orbit_trans (orbit_symm (FibreCount.basePart_orbit M.blk e1)) e2
  obtain ⟨h₀, t, hh₀, ho⟩ := GlobalTheory.T.flag_adjacent_arith_variety_second K ι Φ y Ψ N j M n BM d τ a b k₀ ca cb hb hab hblk hca hcb harith l _ hx _
    (RW.mem x x (RW.mem_U x)) (hbase x)
  have hT : ∀ τ', IsLowerUni ((Function.update (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) τ
      (1 + Matrix.single cb ca t)) τ') := by
    intro τ'
    by_cases e : τ' = τ
    · subst e
      rw [Function.update_self]
      exact FC.DensW.lowerUni_transv hlt t
    · rw [Function.update_of_ne e]
      exact ⟨fun r => Matrix.one_apply_eq r, fun r s h => Matrix.one_apply_ne h.ne⟩
  have han : ∀ (m : ℕ) (V : Set (Fin m → ℂ)) (bp : (Fin m → ℂ) → BM.Rb.X) (hh : Ψ → (Fin m → ℂ) → Matrix (Fin N) (Fin N) ℂ),
      IsOpen V → ContinuousOn bp V → (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) →
      (∀ u ∈ V, bp u ∈ BM.O l) → (∀ τ' r s, AnalyticOnNhd ℂ (fun u => hh τ' u r s) V) →
      (∀ u ∈ V, ∀ τ', IsBlockDiag j (hh τ' u) ∧ (hh τ' u).det ≠ 0) →
      ∀ q, AnalyticOnNhd ℂ (fun u => FC.wVec M (BM.F l) (FC.bvec BM l (bp u)) (fun τ' => hh τ' u) τ a k₀ ca cb t q) V := by
    intro m V bp hh hV hc hch hO hhan _ qq
    obtain ⟨hbv, hval⟩ := GlobalTheory.T.base_chart_holomorphic_composition K ι Φ y Ψ N j M n BM l m V bp hV hc hch hO
    have hreg : ∀ qq I, AnalyticOnNhd ℂ (fun u => valAt M.x ((BM.F l).u qq I) (FC.bvec BM l (bp u))) V := fun qq I =>
      hval _ fun c hcO => ((FC.bvec_good K ι Φ y Ψ N j M n BM l c hcO).2.1.2.1 qq I).1
    obtain ⟨o, mm⟩ := qq
    cases o with
    | none =>
      exact Finset.analyticOnNhd_fun_sum _ fun I _ => (hreg _ I).mul
        (FC.DensW.minor_analytic (FC.DensW.mul_analytic (hhan τ) _) _ _)
    | some k =>
      by_cases hk : ∀ p, M.blk p ≠ some k
      · have e : ∀ u, FC.wVec M (BM.F l) (FC.bvec BM l (bp u)) (fun τ' => hh τ' u) τ a k₀ ca cb t ⟨some k, mm⟩ =
            FC.bvec BM l (bp u) ⟨⟨k, hk⟩, mm⟩ := fun u => (FC.DensW.wVec_some M (BM.F l) _ _ τ a k₀ ca cb t k mm).trans (dif_pos hk)
        simp only [e]
        exact hbv _
      · obtain ⟨p, hp⟩ := not_forall.1 hk
        have hp' : M.blk p = some k := not_not.1 hp
        have e : ∀ u, FC.wVec M (BM.F l) (FC.bvec BM l (bp u)) (fun τ' => hh τ' u) τ a k₀ ca cb t ⟨some k, mm⟩ =
            ∑ I, valAt M.x ((BM.F l).u ⟨k, mm⟩ I) (FC.bvec BM l (bp u)) * minorIJ (hh p.1 u) I (stepCols N j p.2) :=
          fun u => (FC.DensW.wVec_some M (BM.F l) _ _ τ a k₀ ca cb t k mm).trans (FC.flagPt_step M (BM.F l) (FC.bvec BM l (bp u)) (fun τ' => hh τ' u) hp' mm)
        simp only [e]
        exact Finset.analyticOnNhd_fun_sum _ fun I _ => (hreg _ I).mul (FC.DensW.minor_analytic (hhan p.1) _ _)
  obtain ⟨x', hx'V, b', hb', h', hh', ho', hmin⟩ := GlobalTheory.T.base_metric_vector_log_resolution K ι Φ y Ψ N j M n BM (Option K)
    (fun o => ι (o.getD k₀)) _ ⊤ (d + 2) RW rfl l
    (fun c h => FC.wVec M (BM.F l) (FC.bvec BM l c) h τ a k₀ ca cb t) _ hT han
    (fun c hc h hh => GlobalTheory.T.flag_adjacent_arith_variety_first K ι Φ y Ψ N j M n BM d τ a b k₀ ca cb hb hab hblk hca hcb harith l c hc h t hh)
    x _ hx h₀ hh₀ ho V hV hxV
  have hw := GlobalTheory.T.flag_adjacent_plucker_orbit K ι Φ y Ψ N j M τ a b k₀ ca cb hb hab hblk hca hcb (BM.F l) (FC.bvec BM l b') h' t
  have hb'O : b' ∈ BM.O l := hb'.1
  have hg := FC.bvec_good K ι Φ y Ψ N j M n BM l b' hb'O
  have o₀ := FC.DensW.fst_orbit ho'
  have o₁ := FC.DensW.snd_orbit ho'
  rw [hw.1] at o₀
  rw [hw.2] at o₁
  have hpr : FA.pr (q 0 x') = b' := by
    refine BM.Rb.inj _ _ (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.DensW.not_mem_top _) (orbit_trans (orbit_symm (hbase x')) ?_)
    have o₂ := FibreCount.basePart_orbit M.blk o₀
    rw [FC.basePart_flagPt] at o₂
    exact orbit_trans o₂ hg.2.2.2
  refine ⟨x', hx'V, by rw [hpr]; exact hb', fun p => ?_⟩
  rw [hpr]
  refine ⟨(FC.plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p o₀).2
    (FC.DensW.plk_ne_zero M BM l hb'O h' (fun τ' => (hh' τ').1) (fun τ' i hi => (hmin τ' i hi).1) p),
    (FC.plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p o₁).2
    (FC.DensW.plk_ne_zero M BM l hb'O _ (fun τ' => ?_) (fun τ' i hi => ?_) p)⟩
  · by_cases e : τ' = τ
    · subst e
      rw [Function.update_self]
      exact (hh' τ').1.mul (FC.DensW.blockDiag_transv hsb t)
    · rw [Function.update_of_ne e]
      exact (hh' τ').1
  · have hm := (hmin τ' i hi).2
    by_cases e : τ' = τ
    · subst e
      rw [Function.update_self] at hm ⊢
      exact hm
    · rw [Function.update_of_ne e] at hm ⊢
      rwa [Matrix.mul_one] at hm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDenseGoodPoints
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.DensR

variable {K : Type} {ι : K → Type}

theorem orbit_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp [hc p.1]

theorem orbit_trans {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') :
    SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext p
  simp [mul_assoc]

theorem orbit_basePart {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem analytic_minorIJ {m N : ℕ} {V : Set (Fin m → ℂ)} {h : (Fin m → ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hh : ∀ r s, AnalyticOnNhd ℂ (fun u => h u r s) V) (I J : Finset (Fin N)) :
    AnalyticOnNhd ℂ (fun u => minorIJ (h u) I J) V := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e, Matrix.det_apply', Matrix.submatrix_apply]
    refine Finset.analyticOnNhd_fun_sum _ fun σ _ => ?_
    exact analyticOnNhd_const.mul (Finset.analyticOnNhd_fun_prod _ fun i _ => hh _ _)
  · simp only [dif_neg e]
    exact analyticOnNhd_const

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.DensR

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

open DensR in

theorem dens_r : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (l : Fin BM.q) (x : FA.Re.R.X), FA.pr (FA.Re.π x) ∈ BM.O l → ∀ V, IsOpen V → x ∈ V → ∃ x' ∈ V, FA.pr (FA.Re.π x') ∈ BM.O l \ bdry BM.s ∧ ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x'))) (FA.Re.R.lift x' x') p ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA l x hx V hV hxV
  have hlift : FA.Re.R.lift x x ∈ mcPts (mCoordIdeal y) := FA.Re.R.mem x x (FA.Re.R.mem_U x)
  obtain ⟨h₀, hh₀, hso₀⟩ := GlobalTheory.T.exists_flag_point_in_orbit K ι Φ y Ψ N j M n BM l (FA.pr (FA.Re.π x)) hx _ hlift (FA.pr_eq x)
  have hgood := GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good K ι Φ y Ψ N j M n BM l
  have han : ∀ (m : ℕ) (V : Set (Fin m → ℂ)) (bp : (Fin m → ℂ) → BM.Rb.X)
      (hh : Ψ → (Fin m → ℂ) → Matrix (Fin N) (Fin N) ℂ), IsOpen V → ContinuousOn bp V →
      (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) →
      (∀ u ∈ V, bp u ∈ BM.O l) → (∀ τ' r s, AnalyticOnNhd ℂ (fun u => hh τ' u r s) V) →
      (∀ u ∈ V, ∀ τ', IsBlockDiag j (hh τ' u) ∧ (hh τ' u).det ≠ 0) →
      ∀ q, AnalyticOnNhd ℂ (fun u => FC.flagPt M (BM.F l) (FC.bvec BM l (bp u)) (fun τ' => hh τ' u) q) V := by
    intro m V bp hh hV hc ha hm hhan _ q
    have hval := GlobalTheory.T.base_chart_holomorphic_composition K ι Φ y Ψ N j M n BM l m V bp hV hc ha hm
    by_cases hk : ∀ p, M.blk p ≠ some q.1
    · simp only [FC.flagPt, dif_pos hk]
      exact hval.1 _
    · simp only [FC.flagPt, dif_neg hk]
      refine Finset.analyticOnNhd_fun_sum _ fun I _ => ?_
      refine (hval.2 _ fun b hb => ((hgood b hb).2.1.2.1 q I).1).mul ?_
      exact analytic_minorIJ (fun r s => hhan _ r s) _ _
  obtain ⟨x', hx'V, b', hb', h', hh', hso', hmin⟩ :=
    GlobalTheory.T.base_metric_vector_log_resolution K ι Φ y Ψ N j M n BM K ι (mCoordIdeal y) FA.Re.J (d + 1) FA.Re.R FA.J_top l
      (fun b h => FC.flagPt M (BM.F l) (FC.bvec BM l b) h) (fun _ => 1)
      (fun _ => ⟨fun a => by simp, fun a b hab => Matrix.one_apply_ne hab.ne⟩) han
      (fun b hb h hh => GlobalTheory.T.flag_point_in_multiprojective_points K ι Φ y Ψ N j M n BM l b hb h hh)
      x _ hx h₀ hh₀ hso₀ V hV hxV
  have hg' := hgood b' hb'.1
  have hpr : FA.pr (FA.Re.π x') = b' := by
    refine BM.Rb.inj _ _ (fun hc => by simpa using hc.2 1 Submodule.mem_top) ?_
    refine orbit_trans (orbit_symm (FA.pr_eq x')) (orbit_trans (orbit_basePart M.blk hso') ?_)
    rw [FC.basePart_flagPt]
    exact hg'.2.2.2
  refine ⟨x', hx'V, hpr ▸ hb', fun p => ?_⟩
  rw [hpr]
  rw [GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p hso']
  cases hp : M.blk p with
  | none => simp [FC.plk, hp]
  | some k =>
    have hprop : IsProperStep N j p.2 := by
      by_contra hc
      have := (M.blk_none p).2 hc
      simp [hp] at this
    rw [GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_flagPt K ι Φ y Ψ N j M (BM.F l) _ h' p k (BM.isFrame l) hg'.1 hg'.2.1
      (fun τ' => (hh' τ').1) hp]
    exact (hmin p.1 p.2 hprop).1

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticPluckerColumnSwap
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_Lca_of_plk_ne
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type)
    [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d)
    (τ : Ψ) (ca cb : Fin N) (hab : ca < cb) (hblk : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) (l : Fin BM.q)
    (x₀ : FA.Re.R.X) (hO : FA.pr (FA.Re.π x₀) ∈ BM.O l)
    (hplk : ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x₀))) (FA.Re.R.lift x₀ x₀) p ≠ 0) :
    ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), SameOrbit (FA.Re.R.lift x₀ x₀)
      (FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x₀))) (FC.Lca τ ca cb c a)) := by
  have hz : FA.Re.R.lift x₀ x₀ ∈ mcPts (mCoordIdeal y) := FA.Re.R.mem x₀ x₀ (FA.Re.R.mem_U x₀)
  obtain ⟨h, hh, horb⟩ := GlobalTheory.T.exists_flag_point_in_orbit K ι Φ y Ψ N j M n BM l _ hO _ hz (FA.pr_eq x₀)
  obtain ⟨hbm, hbg, -, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good K ι Φ y Ψ N j M n BM l _ hO
  have hmin : ∀ τ' (i : Fin N), IsProperStep N j i →
      minorIJ (h τ') (stepCols N j i) (stepCols N j i) ≠ 0 := by
    intro τ' i hi
    obtain ⟨k, hk⟩ : ∃ k, M.blk (τ', i) = some k :=
      Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
    have h1 := (GlobalTheory.T.plucker_nonvanishing_orbit_invariant K ι Φ y Ψ N j M (BM.F l) _ _ _ (τ', i) horb).1 (hplk (τ', i))
    rwa [GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_flagPt K ι Φ y Ψ N j M (BM.F l) _ h (τ', i) k (BM.isFrame l) hbm hbg
      (fun τ'' => (hh τ'').1) hk] at h1
  choose B hBd hBt hBdet hBL using fun τ' =>
    GlobalTheory.CompanionTheory.Ar.PB.WSq.BigCell.exists_upper_of_minors N j (h τ') M.j_le (hh τ').1 (hh τ').2 (hmin τ')
  obtain ⟨-, -, hlc, -, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam.lc_main Ψ N j τ ca cb hab hblk
  have hL : ∀ τ', IsBlockDiag j (h τ' * B τ') ∧ IsLowerUni (h τ' * B τ') := by
    intro τ'
    refine ⟨fun r s hrs => ?_, hBL τ'⟩
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : ((r : ℕ) < N - j ↔ (t : ℕ) < N - j)
    · rw [hBd τ' t s (fun e => hrs (ht.trans e)), mul_zero]
    · rw [(hh τ').1 r t ht, zero_mul]
  obtain ⟨c, a, e⟩ := hlc _ hL
  refine ⟨c, a, ?_⟩
  rw [e]
  exact orbit_trans horb (orbit_symm
    (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.sameOrbit_flagPt_mul K ι Φ y Ψ N j M (BM.F l) _ h B fun τ' => ⟨hBd τ', hBt τ', hBdet τ'⟩))
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalIntegrability
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.ChartRead

theorem chart_reads : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ w ∈ pD ε V, pPhi M F keep v bl h ε w ∈ pO M Rb keep v F kb V r h ∧ pRho M Rb keep v F kb r h ε (pPhi M F keep v bl h ε w) = w := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hc w hw
  obtain ⟨hflag, hbase, hread⟩ := GlobalTheory.T.frameData_local_resolution_open K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc w hw
  obtain ⟨z, hz, hzv, -⟩ := GlobalTheory.T.frameData_local_degree_estimate K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc w hw
  obtain ⟨hκ, -, hF, hBC, hr, -, hh⟩ := hc
  have hwV : pB ε w ∈ V := hw
  obtain ⟨hzb, -, hG, horb⟩ := hBC.2.2.2.2 _ hwV
  have hV : pB ε w ∈ (Rb.A.chart kb).target := hBC.2.1 hwV
  have hr1 : r (bl (pB ε w)) = (Rb.A.chart kb).symm (pB ε w) :=
    Rb.inj _ _ (fun hc => by simpa using hc.2 1 Submodule.mem_top) (orbit_trans (hr _ hzb) (orbit_symm horb))
  set φ := pPhi M F keep v bl h ε w with hφ
  have hMm : φ ∈ mcPts (mCoordIdeal (y ∘ v)) := by
    rw [← hzv]
    exact CPts.comp_mem_mcPts hκ (RingHom.id Φ) (x := y ∘ v) rfl hz
  have hL : ∀ τ, IsLowerUni (pMat keep (pL ε w) τ) := fun τ => WMan.Read.lowMat_lowerUni _ τ
  have hminor : ∀ (p : Ψ × Fin N) (k : K), keep p → M.blk p = some k → ∀ J : Finset (Fin N),
      twMinor M F (bl (pB ε w)) p.2 k (h p.1)⁻¹ (upV v φ) J =
        minorIJ (pMat keep (pL ε w) p.1) J (stepCols N j p.2) := fun p k hp hk J => by
    have := WMan.Read.twMinor_eq M hF hzb hG hk (hflag p.1).1 (hread p k hp hk) (h p.1)⁻¹ J
    rwa [show pH keep h ε p.1 w = h p.1 * pMat keep (pL ε w) p.1 from rfl,
      Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.2 (hh p.1).2)] at this
  refine ⟨⟨hMm, ?_, ?_, ?_⟩, ?_⟩
  · rw [hbase, hr1]
    exact (Rb.A.chart kb).map_target hV
  · rw [hbase, hr1, (Rb.A.chart kb).right_inv hV]
    exact hwV
  · intro p k hp hk
    rw [hbase, hminor p k hp hk, WMan.Read.minor_self_of_lowerUni (hL p.1)]
    exact one_ne_zero
  · funext i
    obtain ⟨s, rfl⟩ := ε.surjective i
    unfold pRho
    rw [Equiv.symm_apply_apply]
    rcases s with l | q
    · show Rb.A.chart kb (r (pBase M v φ)) l = w (ε (Sum.inl l))
      rw [hbase, hr1, (Rb.A.chart kb).right_inv hV]
      rfl
    · show pRead M F keep (pBase M v φ) h (upV v φ) q.1.1.1 q.1.1.2.1 q.1.1.2.2 = w (ε (Sum.inr q))
      obtain ⟨hkeep, hpr, hbS, haS, hent⟩ := GlobalTheory.T.pMat_stepCols_entry Ψ N j keep q M.j_le
      obtain ⟨hval, hzero⟩ := hent (pL ε w)
      obtain ⟨k, hk⟩ : ∃ k, M.blk (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) = some k := by
        rcases e' : M.blk (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) with _ | k
        · exact absurd hpr ((M.blk_none _).1 e')
        · exact ⟨k, rfl⟩
      obtain ⟨hsgn, hsgn0⟩ := GlobalTheory.T.minorIJ_lowerUni_swap N (pMat keep (pL ε w) q.1.1.1)
        (stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2)) q.1.1.2.1 q.1.1.2.2 (hL _) haS hbS q.1.2.1 hzero
      have e1 := hminor _ k hkeep hk
      rw [hbase]
      unfold pRead
      rw [hk]
      show twMinor M F (bl (pB ε w)) (pStep j keep q.1.1.1 q.1.1.2.2) k (h q.1.1.1)⁻¹ (upV v φ) _ /
        (_ * twMinor M F (bl (pB ε w)) (pStep j keep q.1.1.1 q.1.1.2.2) k (h q.1.1.1)⁻¹ (upV v φ) _) = _
      rw [e1, e1, hsgn, WMan.Read.minor_self_of_lowerUni (hL _), mul_one, mul_div_cancel_left₀ _ hsgn0, hval]
      rfl

end GlobalTheory.CompanionTheory.Ar.PB.PFl.ChartRead
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasureLimitStatementHoldsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_limit_statement_holds : GroundTheory.Heights₂.Heights.LowerBoundFree.MuMeasureLimit.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit | exact GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.muMeasureLimit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralLimitOnModelStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_integral_limit_on_model : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData M.atlas) (Θ : LocPot M.Xc) (Pp : Fin n → LocPot M.Xc) (f : Fin n → M.Xc → ℝ) (fT : Fin n → ℝ → M.Xc → ℝ) (G : M.Xc → ℝ) (GT : ℝ → M.Xc → ℝ) (C : ℝ) (L : ℝ → Fin n → HermLine ι) (g : ℝ → ((Σ k, ι k) → ℂ) → ℝ), IsArithVar P (n + 1) → IsPotential M.atlas Θ → IsPosPot M.atlas Θ → (∀ i, IsPotential M.atlas (Pp i)) → (∀ i, M.atlas.SmoothOn R.Yo (f i)) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, M.atlas.Smooth (fT i t) ∧ IsPsh M.atlas (Pp i + LocPot.ofFun (fT i t) + Θ) ∧ ∀ x ∈ R.Yo, |fT i t x| ≤ C + C * Real.log (R.r x) ∧ fT i t x ≤ C) → (∀ i, ∀ j, ∀ K' ⊆ (M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' R.Yo, IsCompact K' → TendstoUniformlyOn (fun t => fT i t ∘ (M.atlas.chart j).symm) (f i ∘ (M.atlas.chart j).symm) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fT i t ∘ (M.atlas.chart j).symm)) (fderiv ℝ (f i ∘ (M.atlas.chart j).symm)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (fT i t ∘ (M.atlas.chart j).symm))) (fderiv ℝ (fderiv ℝ (f i ∘ (M.atlas.chart j).symm))) (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), M.atlas.Smooth (GT t) ∧ ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x)) → (∀ K' ⊆ R.Yo, IsCompact K' → TendstoUniformlyOn GT G (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i x, ∀ y₀ ∈ (Pp i + LocPot.ofFun (fT i t)).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Pp i + LocPot.ofFun (fT i t)).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts P ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G' : M.Xc → ℂ, M.atlas.HoloOn U G' ∧ ∀ y' ∈ U, (Pp i + LocPot.ofFun (fT i t)).φ x y' - Real.log ((L t i).h (s y')) = (G' y').re) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ mcPts P, g t z = GT t (M.proj z)) → ∃ l : ℝ, Tendsto (fun t => ptsIntegral P (pot (L t)) (g t)) (𝓝[>] 0) (𝓝 l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.tendsto_ptsIntegral_of_chart_conv | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.tendsto_ptsIntegral_of_chart_conv | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.tendsto_ptsIntegral_of_chart_conv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelPointsIntegrableStatementHoldsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_points_integrable_statement_holds : GroundTheory.Heights₂.Heights.LowerBoundFree.ModelPtsIntegrable.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.modelPtsIntegrable | exact GlobalTheory.CompanionTheory.Ar.Giv.modelPtsIntegrable | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.modelPtsIntegrable <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PtsIntegralLogNormRatEqBaseStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_number_pullback_degree_alt : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P J D) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (π : R.X → X) (hπ : HoloMap R.A A π) (dg : ℕ) (br : Set X), IsArithVar P (D + 1) → IsDegreeOff A R.A π dg br → ∀ (L : Fin D → HermLine ι) (Φ : Fin D → LocPot X), (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPotential A (Φ j)) → (∀ j, SamePot R.A Set.univ (potOf R (L j)) ((Φ j).pullback π hπ.1)) → ∀ (Am : HermLine ι) (f g : MRing ι) (u : X → ℝ) (N : Set R.X), IsSmoothHerm Am → IsRatSectionOn P Am f g → IsNull R.A N → (∀ x ∉ N, logNormRat Am f g (R.lift x x) = u (π x)) → MIntegrable A Φ u → ptsIntegral P (pot L) (logNormRat Am f g) = dg * mInt A Φ u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.ptsIntegral_logNormRat_eq_base | exact GlobalTheory.CompanionTheory.Ar.PB.ptsIntegral_logNormRat_eq_base | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.ptsIntegral_logNormRat_eq_base <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeHeightLimitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularized_hodge_height_limit : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (B : ℕ) (Nb Bm : HermLine J) (Pn : ReciprocityTheory.AnForm.M.LocPot M.Xc) (i : ℕ) (f G₀ : M.Xc → ℝ) (g : ((Σ k, J k) → ℂ) → ℝ), ReciprocityTheory.AnForm.M.IsPotential M.atlas Pn → (∀ x, ∀ y₀ ∈ (Pn).U x ∩ Set.univ, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Pn).U x ∩ Set.univ ∧ ∃ s : M.Xc → (Σ k, J k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (mCoordIdeal D.y) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Pn).φ x y' - (fun z => Real.log (Nb.h z)) (s y') = (G y').re) → M.atlas.SmoothOn S.R.Yo f → (∀ z ∈ mcPts (mCoordIdeal D.y), M.proj z ∈ S.R.Yo → Real.log (Bm.h z) = Real.log (S.ref.h z) + f (M.proj z) + ∑ p ∈ D.SB B, Real.log (D.vertFactor p z)) → (∀ z ∈ mcPts (mCoordIdeal D.y), M.proj z ∈ S.R.Yo → g z = G₀ (M.proj z)) → (∀ j, MeasureTheory.AEStronglyMeasurable (G₀ ∘ (M.atlas.chart j).symm) (MeasureTheory.volume.restrict (M.atlas.chart j).target)) → ReciprocityTheory.AnForm.M.MIntegrable M.atlas (positionPot S.R.th Pn f i) G₀ → ptsIntegral (mCoordIdeal D.y) (pot fun j : Fin D.n => if (j : ℕ) < i then Bm else Nb) g = ReciprocityTheory.AnForm.M.mInt M.atlas (positionPot S.R.th Pn f i) G₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_word_eq_mInt | exact GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_word_eq_mInt | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.ptsIntegral_word_eq_mInt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedLeviLowerBoundEventuallyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularized_levi_lower_bound_eventually : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w), S'.IsTied → ∀ δ > (0 : ℝ), ∀ᶠ t' in 𝓝[>] (0 : ℝ), ∀ a, ∀ t : Fin D.n → ℂ, ‖t‖ ≤ 1 / 2 → ∀ v, -(δ * ‖v‖ ^ 2) ≤ levi (fun s : Fin D.n → ℂ => Real.log (S'.ref.h ((D.chart a).γ s)) + S'.bregWeight t' (M.proj ((D.chart a).γ s))) t v := by
  first | exact @GlobalTheory.CompanionTheory.Relay.regularized_levi_lower_bound_eventually | exact GlobalTheory.CompanionTheory.Relay.regularized_levi_lower_bound_eventually | (intros; apply GlobalTheory.CompanionTheory.Relay.regularized_levi_lower_bound_eventually <;> assumption)
end

