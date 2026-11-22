import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.SplitModelToPlaceModel
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperSection
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrLenRestrict
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0051
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0019

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.GramAtLocalLog
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open scoped Matrix ComplexOrder

namespace MuFrameNormLocal

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem valAt_eq_complexPoint_reading {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) :
    LowerBoundFree.valAt y s z = IndefiniteRowSideFullHecke.LowerBoundFree.valAt y s z := by
  classical
  by_cases h : ∃ v, IsValueAt y s z v
  · obtain ⟨v, hv⟩ := h
    rw [LowerBoundFree.valAt_eq hz hv,
      IndefiniteRowSideFullHecke.LowerBoundFree.valAt_eq hz (HermMetricEq.isValueAt_iff.1 hv)]
  · have h' : ¬ IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y s z := fun ⟨v, hv⟩ =>
      h ⟨v, HermMetricEq.isValueAt_iff.2 hv⟩
    rw [LowerBoundFree.valAt, dif_neg h, IndefiniteRowSideFullHecke.LowerBoundFree.valAt, dif_neg h']

theorem regularAt_of_isUnitOn {y : (Σ k, ι k) → Ω} {c : (k : K) → ι k} {f u : Ω}
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (hd : InFrameDomain y c f z)
    (hu : IsUnitOn y c f u) :
    IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y u z ∧ IndefiniteRowSideFullHecke.LowerBoundFree.valAt y u z ≠ 0 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv, hv0⟩ := hd.2
    exact hv0 (isValueAt_unique hz hv
      (HermMetricEq.isValueAt_iff.2 IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_zero))
  have hfi := HermMetricEq.regularAt_inv hf0 hd.2
  have hloc : ∀ s : Ω, (∃ n : ℕ, f ^ n * s ∈ chartRing ℤ (segreCoord y) c) →
      IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y s z := by
    rintro s ⟨n, hn⟩
    have h1 := (HermMetricEq.regularAt_pow hfi n).mul
      (IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hz hd.1 hn)
    rwa [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hf0, one_pow, one_mul] at h1
  have h1 := hloc u hu.2.1
  have h2 := hloc u⁻¹ hu.2.2
  refine ⟨h1, fun h0 => ?_⟩
  have hm := (h1.isValueAt hz).mul (h2.isValueAt hz)
  rw [mul_inv_cancel₀ hu.1, h0, zero_mul] at hm
  exact one_ne_zero (IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.unique hz IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_one hm)

end Values

section Gram

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ} {y : (Σ k, ι k) → Ω}
  {W : ChartBundle ℤ (segreCoord y) N E} {Xo : Set ((Σ k, ι k) → ℂ)}
  {P : Ideal (MRing ι)} {n nc : ℕ} {Bd : Set ((Σ k, ι k) → ℂ)} {χ : Fin nc → SncChart P n Bd}

theorem gramAt_eq_of_frame (hA : HermMetric y W Xo χ) (hXo : Xo ⊆ mcPts (mCoordIdeal y))
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ Xo) {l : Fin hA.m}
    (hd : InFrameDomain y (hA.chart l) (hA.fr l) z) {b : Fin N → E}
    {S : Matrix (Fin N) (Fin N) Ω} (hS : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y (S p q) z)
    (hb : ∀ q, b q = ∑ p, S p q • hA.b l p) :
    LowerBoundFree.gramAt hA b z = (HermMetricEq.valM y S z)ᴴ * hA.gram l z * HermMetricEq.valM y S z := by
  rw [← hA.gramMatrix_change_of_frame hXo hz hd hS hb]
  have hv : ∀ s : Ω, LowerBoundFree.valAt y s z = IndefiniteRowSideFullHecke.LowerBoundFree.valAt y s z :=
    fun s => valAt_eq_complexPoint_reading (hXo hz)
  unfold LowerBoundFree.gramAt HermMetric.gramMatrixInFamily HermMetricEq.valM
  simp only [hv]

end Gram

section LogBounds

variable {X : Type*} {F : Filter X} {Q : X → Prop} {L : X → ℝ}

end LogBounds

section Local

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

end Local

end MuFrameNormLocal

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDiagFibreFubini
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace DiagonalFibreFubini

def wordCoef (i : ℕ) : ℕ → Fin 2 → ℝ := fun n =>
  if n = 0 then ![1, -1] else if n = 1 then ![0, 1] else if n < 2 + 2 * i then ![1, 0] else ![0, 1]

def topCoef : ℕ → Fin 2 → ℝ := fun n => if n = 0 then ![1, 0] else ![0, 1]

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem cons_pot_word (D k i : ℕ) (hik : i < k) (X₀ X₁ A₀ : HermLine ι) :
    (Fin.cons (α := fun _ => ((Σ k, ι k) → ℂ) → ℝ) (fun z => Real.log (X₀.h z) - Real.log (X₁.h z))
        (pot (word D k i X₀ X₁ A₀)) : Fin (D + 1) → ((Σ k, ι k) → ℂ) → ℝ) =
      wwLinPot X₀ X₁ A₀ k (wordCoef i) := by
  funext j z
  refine Fin.cases ?_ (fun j => ?_) j
  · have h0 : (0 : ℕ) < 2 * k := by omega
    simp [wwLinPot, wordCoef, h0]
    ring
  · simp only [Fin.cons_succ, pot, word, wwLinPot, wordCoef, Fin.val_succ]
    split_ifs <;> first | contradiction | omega | simp

theorem linProd_word (k i : ℕ) (hik : i < k) :
    wwLinProd k (wordCoef i) = (X 0 - X 1) * X 0 ^ (2 * i) * X 1 ^ (2 * k - 1 - 2 * i) := by
  obtain ⟨r, hr⟩ : ∃ r, 2 * k = 2 + 2 * i + r := ⟨2 * k - 2 - 2 * i, by omega⟩
  rw [wwLinProd, hr, Finset.prod_range_add, Finset.prod_range_add]
  have h1 : ∏ x ∈ Finset.range 2, (C (wordCoef i x 0) * X 0 + C (wordCoef i x 1) * X 1 : MvPolynomial (Fin 2) ℝ) =
      (X 0 - X 1) * X 1 := by
    simp [Finset.prod_range_succ, wordCoef]
    ring
  have h2 : ∏ x ∈ Finset.range (2 * i),
      (C (wordCoef i (2 + x) 0) * X 0 + C (wordCoef i (2 + x) 1) * X 1 : MvPolynomial (Fin 2) ℝ) = X 0 ^ (2 * i) := by
    rw [← Finset.card_range (2 * i), ← Finset.prod_const]
    refine Finset.prod_congr (by rw [Finset.card_range]) fun x hx => ?_
    have hx' : x < 2 * i := Finset.mem_range.1 hx
    simp [wordCoef, show 2 + x ≠ 1 by omega, show 2 + x < 2 + 2 * i by omega]
  have h3 : ∏ x ∈ Finset.range r,
      (C (wordCoef i (2 + 2 * i + x) 0) * X 0 + C (wordCoef i (2 + 2 * i + x) 1) * X 1 : MvPolynomial (Fin 2) ℝ) =
        X 1 ^ r := by
    rw [← Finset.card_range r, ← Finset.prod_const]
    refine Finset.prod_congr (by rw [Finset.card_range]) fun x _ => ?_
    simp [wordCoef, show 2 + 2 * i + x ≠ 1 by omega,
      show ¬ 2 + 2 * i + x < 2 + 2 * i by omega]
  rw [h1, h2, h3, show 2 + 2 * i + r - 1 - 2 * i = r + 1 by omega, pow_succ]
  ring

theorem cons_pot_top (D k : ℕ) (hk : 1 ≤ k) (X₀ X₁ A₀ : HermLine ι) :
    pot (Fin.cons X₀ (mix (2 * k - 1) X₁ A₀ : Fin D → HermLine ι) : Fin (D + 1) → HermLine ι) =
      wwLinPot X₀ X₁ A₀ k topCoef := by
  funext j z
  refine Fin.cases ?_ (fun j => ?_) j
  · have h0 : (0 : ℕ) < 2 * k := by omega
    simp [pot, wwLinPot, topCoef, h0]
  · simp only [pot, Fin.cons_succ, mix, wwLinPot, topCoef, Fin.val_succ]
    split_ifs <;> first | contradiction | omega | simp

theorem linProd_top (k : ℕ) (hk : 1 ≤ k) : wwLinProd k topCoef = X 0 * X 1 ^ (2 * k - 1) := by
  obtain ⟨r, hr⟩ : ∃ r, 2 * k = 1 + r := ⟨2 * k - 1, by omega⟩
  rw [wwLinProd, hr, Finset.prod_range_add, show 1 + r - 1 = r by omega]
  have h1 : ∏ x ∈ Finset.range 1, (C (topCoef x 0) * X 0 + C (topCoef x 1) * X 1 : MvPolynomial (Fin 2) ℝ) = X 0 := by
    simp [topCoef]
  have h2 : ∏ x ∈ Finset.range r, (C (topCoef (1 + x) 0) * X 0 + C (topCoef (1 + x) 1) * X 1 : MvPolynomial (Fin 2) ℝ) =
      X 1 ^ r := by
    rw [← Finset.card_range r, ← Finset.prod_const]
    refine Finset.prod_congr (by rw [Finset.card_range]) fun x _ => ?_
    simp [topCoef]
  rw [h1, h2]

theorem pderiv_top (N : ℕ) :
    pderiv 0 (pderiv 1 (X 0 * X 1 ^ (N + 1) : MvPolynomial (Fin 2) ℝ)) = C ((N + 1 : ℕ) : ℝ) * X 1 ^ N := by
  simp [Derivation.leibniz, Derivation.leibniz_pow]

def sndHom : (S2 → ℝ) →+* (S2 × S2 → ℝ) :=
  RingHom.pi fun p => Pi.evalRingHom (fun _ : S2 => ℝ) p.2

theorem dotPoly_snd : dotPoly (Prod.snd : S2 × S2 → S2) = map sndHom (dotPoly (id : S2 → S2)) := by
  simp only [dotPoly, map_sum, map_mul, map_X, map_C]
  rfl

theorem moment_top (k : ℕ) (hk : 1 ≤ k) :
    wwFibreMoment (fun _ => 1) (X 0 * X 1 ^ (2 * k - 1)) = -pushMomentPoly k := by
  have := FibreLocal.isProbabilityMeasure_sphere
  obtain ⟨N, hN⟩ : ∃ N, 2 * k - 1 = N + 1 := ⟨2 * k - 2, by omega⟩
  have hN2 : 2 * k - 2 = N := by omega
  have hc : ((N + 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
    have h2 : ((N + 1 + 1 : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ) := by rw [show N + 1 + 1 = 2 * k by omega]
    push_cast at h2 ⊢
    linarith
  rw [wwFibreMoment, hN, pderiv_top, pushMomentPoly, hN2]
  ext m
  rw [DiagFibreMoment.coeff_momentPoly, coeff_neg, coeff_smul, DiagFibreMoment.coeff_momentPoly]
  have hpt : ∀ p : S2 × S2,
      coeff m (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd]
        (C ((N + 1 : ℕ) : ℝ) * X 1 ^ N : MvPolynomial (Fin 2) ℝ)) p =
        ((N + 1 : ℕ) : ℝ) * coeff m (dotPoly (id : S2 → S2) ^ N) p.2 := by
    intro p
    rw [map_mul, aeval_C, map_pow, aeval_X, Matrix.cons_val_one, Matrix.cons_val_fin_one, dotPoly_snd, ← map_pow,
      MvPolynomial.algebraMap_apply, coeff_C_mul, coeff_map]
    rfl
  simp_rw [hpt]
  have hsnd := integral_fun_snd (μ := sphereMeasure) (ν := sphereMeasure)
    (fun y : S2 => (1 : ℝ) * (((N + 1 : ℕ) : ℝ) * coeff m (dotPoly (id : S2 → S2) ^ N) y))
  rw [hsnd, probReal_univ, one_smul]
  simp only [one_mul, smul_eq_mul]
  rw [integral_const_mul, hc]
  ring

end DiagonalFibreFubini

open DiagonalFibreFubini in

theorem DiagFibreFubini.proof (h : WWFibrePoly.Statement) : DiagFibreFubini.Statement := by
  intro D S X A X₀ X₁ A₀ hX hA hAb p0 p1 pA k hk hkD
  obtain ⟨Λ, hΛ⟩ := h D S X A X₀ X₁ A₀ hX hA hAb p0 p1 pA k hk hkD
  refine ⟨Λ, fun i hi => ?_, ?_⟩
  · rw [diagInt, cons_pot_word D k i hi, (hΛ _).1, linProd_word k i hi]
    rfl
  · rw [cons_pot_top D k hk, (hΛ _).2, linProd_top k hk, moment_top k hk, map_neg]
    ring

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumEventual
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace InterNumEventual

def ind {n : ℕ} (T : Finset (Fin n)) : Fin n → ℕ := fun i => if i ∈ T then 1 else 0

theorem sum_sign_prod_ind {n : ℕ} (e : Fin n → ℕ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) * ∏ i, ((ind T i : ℕ) : ℚ) ^ e i =
      ∏ i, (1 - (0 : ℚ) ^ e i) := by
  have h1 : ∏ i, (1 - (0 : ℚ) ^ e i) = ∏ i ∈ Finset.univ, (1 + -(0 : ℚ) ^ e i) := by
    simp only [sub_eq_add_neg]
  rw [h1, Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_const_one, one_mul, Finset.prod_neg, Finset.card_univ_sdiff, Fintype.card_fin,
    ← Finset.prod_mul_prod_compl T, Finset.compl_eq_univ_sdiff]
  congr 1
  rw [Finset.prod_eq_one (fun i hi => by simp [ind, hi]), one_mul]
  exact Finset.prod_congr rfl fun i hi => by
    rw [Finset.mem_sdiff] at hi
    simp [ind, hi.2]

theorem mixed_eval {n : ℕ} (Q : MvPolynomial (Fin (n + 1)) ℚ) (hQ : Q.totalDegree ≤ n) (c : ℚ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) *
        eval (Fin.snoc (α := fun _ => ℚ) (fun j => ((ind T j : ℕ) : ℚ)) c) Q =
      ∑ d ∈ Q.support, Q.coeff d * ∏ i : Fin n, (1 - (0 : ℚ) ^ d i.castSucc) := by
  simp only [MvPolynomial.eval_eq', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  trans ∑ T : Finset (Fin n), Q.coeff d * c ^ d (Fin.last n) *
      ((-1 : ℚ) ^ (n - T.card) * ∏ i : Fin n, ((ind T i : ℕ) : ℚ) ^ d i.castSucc)
  · refine Finset.sum_congr rfl fun T _ => ?_
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring
  rw [← Finset.mul_sum, sum_sign_prod_ind]
  by_cases h0 : ∃ i : Fin n, d i.castSucc = 0
  · obtain ⟨i, hi⟩ := h0
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, pow_zero, sub_self])]
    ring
  · push Not at h0
    have hdeg := (le_totalDegree hd).trans hQ
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_castSucc] at hdeg
    have hge : n ≤ ∑ i : Fin n, d i.castSucc := by
      calc n = ∑ _i : Fin n, 1 := by simp
        _ ≤ ∑ i : Fin n, d i.castSucc :=
          Finset.sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.mpr (h0 i)
    rw [show d (Fin.last n) = 0 by omega, pow_zero, mul_one]

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem foldl_twist_sub {n : ℕ} (L : Fin n → SubSystem k x Ω) (I : Chart x) :
    ∀ (l : List (Fin n)) (F : SubSystem k x Ω),
      (l.foldl (fun F i => F.twist (L i)) F).sub I = F.sub I * (l.map fun i => (L i).sub I).prod
  | [], F => by simp
  | a :: l, F => by
    rw [List.foldl_cons, foldl_twist_sub L I l, SubSystem.twist_sub_eq_mul_of_line, List.map_cons,
      List.prod_cons]
    ring

theorem tensorSub_sub {n : ℕ} (L : Fin n → SubSystem k x Ω) (T : Finset (Fin n)) (I : Chart x) :
    (tensorSub L T).sub I = (twistSys k x 0).sub I * ∏ i, (L i).sub I ^ ind T i := by
  unfold tensorSub
  rw [foldl_twist_sub, Fin.prod_univ_def]
  congr 1
  induction List.finRange n with
  | nil => simp
  | cons a l ih => by_cases ha : a ∈ T <;> simp [ha, ind, ih]

theorem tensorSub_eq_twistPows {n : ℕ} (L : Fin n → SubSystem k x Ω) (T : Finset (Fin n)) :
    tensorSub L T = (twistSys k x 0).twistPows n L (ind T) :=
  SubSystem.ext_sub fun I => by rw [tensorSub_sub, SnapperSections.twistPows_sub]

end InterNumEventual

open InterNumEventual in

theorem InterNumEventual.proof (hH : SnapperHyperplane.Statement.{u, w})
    (hS : SnapperSection.Statement.{u, w}) : InterNumEventual.Statement.{u, w} := by
  have hR : RestrLenEuler.Statement.{u, w} := RestrLenEuler.proof
  intro k _ Ω _ _ N x n pp L hW
  have := hW.isPrime
  obtain ⟨Q, hQ, hev⟩ := pieceChar_isNumPolyLT hH hS SnapperDiffPoly.proof L (n + 1) pp hW.isPrime hW.homog
    hW.le hW.dim.le 0
  have hQn : Q.totalDegree ≤ n := by
    rcases hQ with h | h
    · rw [h, totalDegree_zero]; exact Nat.zero_le _
    · omega
  have hall : ∀ᶠ c : ℕ in atTop, ∀ T : Finset (Fin n),
      restrLen pp ((tensorSub (fun i => (L i).toSubSystem) T).twist (twistSys k x (c : ℤ))) =
        pieceChar k pp 0 L (ind T) c := by
    refine Filter.eventually_all.mpr fun T => ?_
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (hR k Ω N x pp hW.homog hW.le n L (ind T))] with c hc
    rw [tensorSub_eq_twistPows]
    exact hc
  have hval : ∀ c : ℕ, (∀ T : Finset (Fin n),
      restrLen pp ((tensorSub (fun i => (L i).toSubSystem) T).twist (twistSys k x (c : ℤ))) =
        pieceChar k pp 0 L (ind T) c) →
      (interSum pp (fun i => (L i).toSubSystem) c : ℚ) =
        ∑ d ∈ Q.support, Q.coeff d * ∏ i : Fin n, (1 - (0 : ℚ) ^ d i.castSucc) := by
    intro c hc
    rw [← mixed_eval Q hQn (c : ℚ)]
    unfold interSum
    push_cast
    refine Finset.sum_congr rfl fun T _ => ?_
    have hT := hev (ind T) (c : ℤ)
    simp only at hT
    rw [hc T, hT, Int.cast_natCast]
  obtain ⟨c₀, hc₀⟩ := hall.exists
  refine ⟨interSum pp (fun i => (L i).toSubSystem) c₀, hall.mono fun c hc => ?_⟩
  exact_mod_cast (hval c hc).trans (hval c₀ hc₀).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumTieX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

theorem InterNumTie.proof (hRL : RestrLenRestrict.Statement.{u, w}) : InterNumTie.Statement.{u, w} := by
  intro k _ Ω _ _ N x e pp b hsub
  classical
  obtain ⟨j, hjp⟩ := hsub.relevant
  have hj : x j ≠ 0 := fun h0 => hjp (hsub.le ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0)))
  obtain ⟨hcp, hpt⟩ := PrimeFiltration.Point.full k Ω N x pp hsub.isPrime hsub.homog hsub.le j hj hjp
  have := hcp
  let A := chartRing k x (singleChart hj)
  let Ip : Ideal A := chartPrime pp hj
  let ψ : A →ₐ[k] Ip.ResidueField := IsScalarTower.toAlgHom k A Ip.ResidueField
  have hker : RingHom.ker ψ = Ip := Ideal.ker_algebraMap_residueField Ip
  let y : Fin (N + 1) → Ip.ResidueField := fun i => ψ (ratio hj i)
  have hxy : ∀ i, y i ≠ 0 → x i ≠ 0 := by
    intro i h hx
    apply h
    have h0 : ratio (S := k) hj i = 0 := Subtype.ext (by change x i / x j = 0; rw [hx, zero_div])
    change ψ (ratio hj i) = 0
    rw [h0, map_zero]
  have hpy : primeOf (S := k) y = pp := hpt _ ψ hker
  have hxy' : primeOf (S := k) x ≤ primeOf (S := k) y := hpy ▸ hsub.le
  have hsubW : IsSubvar y pp e := ⟨hsub.isPrime, hsub.homog, le_of_eq hpy, hsub.relevant, hsub.dim⟩
  have hyj : y j ≠ 0 := fun h0 => hjp (hpy ▸ (mem_primeOf_of_isHomogeneous y (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0))
  have hy0 : y ≠ 0 := fun h => hyj (congrFun h j)
  set I := pp.comap (oneBlock (S := k) (N := N)) with hI_def
  have hI : I = primeOfOne (S := k) y := by rw [primeOfOne, hpy]
  have hIp : NumbersDVR.IsMultiProjPrime I := hI ▸ isMultiProjPrime_primeOfOne y hy0
  have hIdim : FieldNumbers.relDim I = ((e : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, hI, HilbertPositive.ringKrullDim_primeOfOne, hpy,
      hsub.dim]
    simp
  let H : ℤ → ℤ := fun m => NumbersDVR.hilbFn I (fun _ : Unit => m)
  let R : ℤ → ℤ := fun m => restrLen pp (twistSys k x m)
  have hY : ∀ᶠ n : ℕ in atTop, restrLen pp (twistSys k y (n : ℤ)) = H n := by
    filter_upwards [TwistSections.full k _ N y hy0] with n hn
    rw [← hpy, SectionsOverLocalization.restrLen_primeOf_eq_finrank y hyj, hn, HilbertPositive.finrank_piece_eq_hilbFn, ← hI]
  obtain ⟨r₀, hr₀⟩ := RestrictTwist.full.1 k Ω N x _ y hxy hxy' 0
  have hXY := hRL k Ω N x _ y hxy hxy' pp e hsubW (twistBundle k x 0) (twistBundle k y 0) r₀ hr₀
  have hRH : ∀ᶠ n : ℕ in atTop, R n = H n := by
    filter_upwards [hY, hXY] with n h1 h2
    have e1 : (twistBundle k y 0).toSubSystem = twistSys k y 0 := rfl
    have e2 : (twistBundle k x 0).toSubSystem = twistSys k x 0 := rfl
    rw [e1, e2, twistSys_zero_twist, twistSys_zero_twist] at h2
    rw [← h1, h2]
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hRH
  have hRH' : ∀ m : ℤ, (n₀ : ℤ) ≤ m → R m = H m := by
    intro m hm
    have h := hn₀ m.toNat (by omega)
    rwa [Int.toNat_of_nonneg (by omega)] at h
  let bs : Fin e → Unit → ℤ := fun i _ => b i
  have hMD := (FieldNumbers.MixedDiffConst.full k Unit (fun _ => Fin (N + 1)) I hIp.multiHomog hIp.relevant e
    hIdim).1 bs
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp hMD
  set B : ℤ := ∑ i, b i with hB
  have hev : ∀ᶠ c : ℕ in atTop, interSum pp (fun i => twistSys k x (b i)) c = NumbersDVR.intNum k I bs := by
    filter_upwards [eventually_ge_atTop (m₀ () - B).toNat,
      eventually_all.mpr fun T : Finset (Fin e) => eventually_ge_atTop ((n₀ : ℤ) - ∑ i ∈ T, b i).toNat]
      with c hc1 hc2
    rw [SectionsOverLocalization.interSum_twistSys, ← hm₀ (fun _ => (c : ℤ) + B)
      (fun u => by cases u; change m₀ () ≤ (c : ℤ) + B; omega), SectionsOverLocalization.mixedDiff_eq_sum]
    refine Fintype.sum_bijective compl compl_involutive.bijective _ _ fun T => ?_
    have hsum : (∑ i ∈ Tᶜ, bs i) = fun _ : Unit => ∑ i ∈ Tᶜ, b i := by
      funext u
      rw [Finset.sum_apply]
    have hc : (n₀ : ℤ) ≤ ∑ i ∈ T, b i + c := by have := hc2 T; omega
    have hsplit := Finset.sum_add_sum_compl T b
    have hcard : Tᶜ.card = e - T.card := by rw [Finset.card_compl, Fintype.card_fin]
    rw [show restrLen pp (twistSys k x (∑ i ∈ T, b i + c)) = H (∑ i ∈ T, b i + c) from hRH' _ hc, hsum, hcard]
    change (-1) ^ (e - T.card) * H (∑ i ∈ T, b i + c) =
      (-1) ^ (e - T.card) * NumbersDVR.hilbFn I ((fun _ : Unit => (c : ℤ) + B) - fun _ => ∑ i ∈ Tᶜ, b i)
    have hfun : ((fun _ : Unit => (c : ℤ) + B) - fun _ => ∑ i ∈ Tᶜ, b i) =
        fun _ : Unit => ∑ i ∈ T, b i + c := by
      funext u
      simp only [Pi.sub_apply]
      omega
    rw [hfun]
  unfold interNum
  exact (tendsto_const_nhds.congr' (hev.mono fun c h => h.symm)).limUnder_eq

theorem InterNumTie.of_restrictQuot (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w}) :
    InterNumTie.Statement.{u, w} :=
  InterNumTie.proof (RestrLenRestrict.proof
    (SurjectiveClosed.proof Extension.full.{u, w, w} IdealTwistFamily.proof
      (TildeVanish.proof SerreVanish.full.{u, w})) hRQ)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StatementsAmpleVNefOnFibres
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def AmpleVNefOnFibres.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ),
    (∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (fibreIdeal ℓ y) a) → NefOnFibres (mCoordIdeal y) a

end

end GroundTheory.Heights₂.Heights.Targets
end

