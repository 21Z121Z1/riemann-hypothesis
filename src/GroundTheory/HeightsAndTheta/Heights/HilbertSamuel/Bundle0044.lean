import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def ShiftSectionBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (m : ℕ),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1) : ℝ) ≤
          (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => (m : ℤ)) 1) : ℝ) ∧
        (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => (m : ℤ)) 1) : ℝ) ≤
          (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1) : ℝ) + C * (n : ℝ) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftVolumeBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

def ShiftVolumeBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, 1 ≤ q →
      arVolP (IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) (q : ℤ) 1))
          (chartLat y (HermLine.zcomb A (fsH ι) (q : ℤ) 1).a) 1 D ≤
        C * ((q : ℝ) + 1) * (genDeg (mCoordIdeal y) D (HermLine.zcomb A (fsH ι) (q : ℤ) 1).a : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionsSeparated
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def SmallSectionsSeparated.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℕ, ∃ (Z : Finset ((Σ k, ι k) → ℂ)) (ev : chartLatNm y A.a τ →+ (Z → ℂ)),
      (∀ z ∈ Z, z ∈ mcPts (mCoordIdeal y)) ∧
      (∀ (s : chartLatNm y A.a τ) (z : Z), ∃ (dg dh : K → ℕ) (g h : MRing ι),
        IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + τ * A.a k) ∧
        aeval y g = (s : Ω) * aeval y h ∧ eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) h) ≠ 0 ∧
        ev s z * eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) h) =
          eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) g)) ∧
      ∀ s t : chartLatNm y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) →
        IsSmallH (mCoordIdeal y) y A τ (t : Ω) → s ≠ t →
        ∃ z : Z, Real.exp (-(C * ((τ : ℝ) + 1))) * A.h z ^ τ ≤ ‖ev s z - ev t z‖

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSpanStepHomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SpanStepHomog.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    ∃ (m r : ℕ) (t : Fin r → Ω), (∀ l, t l ∈ chartLat y a m) ∧
      ∀ (n : ℕ), ∀ s ∈ chartLat y a n, ∀ j, w j ≠ 0 →
        ∃ D : ℕ, s * w j ^ D ∈ gradedSpan w (fun _ => m) t (n + D)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSpanStepLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SpanStepLocal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    ∀ j, w j ≠ 0 → ∃ (r : ℕ) (b : Fin r → Ω), (∀ l, ∃ n : ℕ, b l * w j ^ n ∈ chartLat y a n) ∧
      ∀ (g : Ω) (n : ℕ), g * w j ^ n ∈ chartLat y a n →
        ∃ c : Fin r → Ω, (∀ l, c l ∈ Algebra.adjoin ℤ (Set.range fun i => w i / w j)) ∧ g = ∑ l, c l * b l

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistIntersection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

def TwistIntersection.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ) (A B : HermLine ι) (II : IntersectionSystem)
    (Λ : (F →+* ℂ) → ℝ),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (A.a = fun k => (a k : ℤ)) → IsSmoothHerm A → B.a = 0 → IsSmoothHerm B → (∀ sg, 0 < Λ sg) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z → B.h =ᶠ[𝓝 z] fun _ => Λ sg) →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A.tensor B) =
      II K ι (mCoordIdeal y) (D + 1) (fun _ => A) +
        ((D + 1 : ℕ) : ℝ) * genDeg (mCoordIdeal y) D A.a *
          ((∑ sg, Real.log (Λ sg)) / Fintype.card (F →+* ℂ))

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.TwoBlockModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

section TwoBlock

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def twoBlockIdeal (x x' : Ix κ → Ω) : Ideal (MRing (FinTwoTypeFamily κ)) :=
  mCoordIdeal (ι := FinTwoTypeFamily κ) (pair x x')

def blockLine (m : ConeMetric ℂ (Ix κ)) (k₀ : Fin 2) : HermLine (FinTwoTypeFamily κ) where
  a := Pi.single k₀ 1
  h z := m.ρ fun p : Ix κ => z ⟨k₀, p.2⟩
  pos z hz := m.pos _ fun h0 => by
    obtain ⟨i, hi⟩ := hz k₀
    exact hi (congrFun h0 ⟨(), i⟩)
  smul c z _ := by
    have e : (fun p : Ix κ => c k₀ * z ⟨k₀, p.2⟩) = c k₀ • fun p : Ix κ => z ⟨k₀, p.2⟩ := rfl
    show m.ρ (fun p : Ix κ => c k₀ * z ⟨k₀, p.2⟩) = _
    rw [e, m.smul, Finset.prod_eq_single k₀ (fun k _ hk => by simp [hk]) (by simp)]
    simp

def twoBlockList (m m' : ConeMetric ℂ (Ix κ)) (D i : ℕ) : Fin (D + 1) → HermLine (FinTwoTypeFamily κ) :=
  fun j => if (j : ℕ) < i then blockLine m 0 else blockLine m' 1

def twoBlockCoeff (I : AllFam) (x x' : Ix κ → Ω) (m m' : ConeMetric ℂ (Ix κ)) (D i : ℕ) : ℝ :=
  I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (twoBlockList m m' D i) -
    I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (twoBlockList m m' D (i + 1))

def twoBlockStep (x x' : Ix κ → Ω) (a b : ℕ) : ℝ :=
  Real.log ((sec ℤ x (a + 1) * sec ℤ x' b).toAddSubgroup.relIndex (sec ℤ x a * sec ℤ x' (b + 1)).toAddSubgroup)

theorem twoBlockList_zero (m m' : ConeMetric ℂ (Ix κ)) (D : ℕ) :
    twoBlockList m m' D 0 = fun _ => blockLine m' 1 := by
  funext j
  simp [twoBlockList]

theorem twoBlockList_last (m m' : ConeMetric ℂ (Ix κ)) (D : ℕ) :
    twoBlockList m m' D (D + 1) = fun _ => blockLine m 0 := by
  funext j
  simp [twoBlockList, j.2]

theorem sum_twoBlockCoeff (I : AllFam) (x x' : Ix κ → Ω) (m m' : ConeMetric ℂ (Ix κ)) (D : ℕ) :
    ∑ i ∈ Finset.range (D + 1), twoBlockCoeff I x x' m m' D i =
      I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (fun _ => blockLine m' 1) -
        I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (fun _ => blockLine m 0) := by
  unfold twoBlockCoeff
  rw [Finset.sum_range_sub', twoBlockList_zero, twoBlockList_last]

end TwoBlock

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.WhittakerFunctional
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem G5.fderiv_fderiv_eq_of_add_const {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → ℝ} {y : E}
    (b : ℝ) (h : ∀ᶠ y' in 𝓝 y, f y' = g y' + b) : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [h.eventually_nhds] with y' hy'
  have hfg : f =ᶠ[𝓝 y'] fun x => g x + b := hy'
  rw [hfg.fderiv_eq, fderiv_add_const]

theorem G5.ptsIntegral_eq_of_add_const {e : ℕ} (P : Ideal (MRing ι)) (φ ψ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (h : ∀ j, ∃ b : ℝ, ∀ z ∈ mcPts P, φ j z = ψ j z + b) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ g = ptsIntegral P ψ g := by
  have hs : ∀ Ψ y w, sheetDensity P Ψ φ g y w = sheetDensity P Ψ ψ g y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs with hγ
    · congr 1
      have hH : ∀ j, cxHessian (fun y' => φ j (hγ.choose y')) y = cxHessian (fun y' => ψ j (hγ.choose y')) y := by
        intro j
        obtain ⟨b, hb⟩ := h j
        have hev : ∀ᶠ y' in 𝓝 y, φ j (hγ.choose y') = ψ j (hγ.choose y') + b :=
          hγ.choose_spec.2.mono fun y' hy' => hb _ hy'.2.1
        unfold cxHessian
        rw [G5.fderiv_fderiv_eq_of_add_const b hev]
      simp only [maDensity, hH]
    · rfl
  unfold ptsIntegral ptsIntegralAt
  simp only [hs]

theorem G5.ptsIntegral_const {e : ℕ} (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun _ => c) = c * ptsIntegral P φ (fun _ => 1) := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum_mem]
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs <;> ring
  · simp

theorem G5.isSmoothHerm_constLine (c : ℝ) : IsSmoothHerm (constLine (ι := ι) c) := by
  show ContDiffOn ℝ _ (fun _ => Real.exp (-c)) _
  exact contDiffOn_const

theorem G5.log_tensor_constLine (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((A.tensor (constLine c)).h z) = Real.log (A.h z) + -c := by
  show Real.log (A.h z * Real.exp (-c)) = _
  rw [Real.log_mul (A.pos z hz).ne' (Real.exp_pos _).ne', Real.log_exp]

theorem G5.top_tensor_constLine (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ)
    (hP : IsArithVar P (D + 1)) (hA : IsSmoothHerm A) :
    I P (D + 1) (fun _ => A.tensor (constLine c)) =
      I P (D + 1) (fun _ => A) - ((D + 1 : ℕ) : ℝ) * c * geomDeg P A D := by
  set A' := A.tensor (constLine (ι := ι) c) with hA'def
  have hA' : IsSmoothHerm A' := hA.mul (G5.isSmoothHerm_constLine c)
  let L : ℕ → Fin (D + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun k j => if (j : ℕ) < k then A' else A
  have hL2 : ∀ k j, L k j = A ∨ L k j = A' := fun k j => by
    by_cases h : (j : ℕ) < k
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  have hLs : ∀ k j, IsSmoothHerm (L k j) := fun k j => (hL2 k j).elim (fun h => h ▸ hA) (fun h => h ▸ hA')

  have hint : ∀ M : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (∀ j, M j = A ∨ M j = A') →
      ptsIntegral P (pot M) (fun _ => c) = c * geomDeg P A D := by
    intro M hM
    rw [G5.ptsIntegral_const]
    congr 1
    refine G5.ptsIntegral_eq_of_add_const P _ _ (fun j => ?_) _
    rcases hM j with h | h
    · exact ⟨0, fun z _ => by simp [pot, h]⟩
    · exact ⟨-c, fun z hz => by simp only [pot, h]; exact G5.log_tensor_constLine A c z hz.1⟩
  have step : ∀ k, k ≤ D + 1 → I P (D + 1) (L k) = I P (D + 1) (fun _ => A) - (k : ℝ) * c * geomDeg P A D := by
    intro k
    induction k with
    | zero =>
      intro _
      have : L 0 = fun _ => A := by funext j; simp [L]
      rw [this]; simp
    | succ k ih =>
      intro hk
      have hkD : k < D + 1 := by omega
      set i : Fin (D + 1) := ⟨k, hkD⟩
      set σ := Equiv.swap i (Fin.last D)
      set M : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun j => L (k + 1) (σ (Fin.castSucc j))
      have hne : ∀ j : Fin D, σ (Fin.castSucc j) ≠ i := by
        intro j hj
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at hj
        exact (Fin.castSucc_lt_last j).ne hj
      have hMk : ∀ j : Fin D, L k (σ (Fin.castSucc j)) = M j := by
        intro j
        have h1 : ((σ (Fin.castSucc j) : Fin (D + 1)) : ℕ) ≠ k := fun h => hne j (Fin.ext h)
        simp only [M, L]
        by_cases h2 : ((σ (Fin.castSucc j) : Fin (D + 1)) : ℕ) < k
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]
      have hσi : σ (Fin.last D) = i := Equiv.swap_apply_right _ _
      have e1 : L (k + 1) ∘ σ = Fin.snoc M A' := by
        funext x
        refine Fin.lastCases ?_ (fun j => ?_) x
        · simp only [Function.comp_apply, Fin.snoc_last, hσi, L, i]
          exact if_pos (Nat.lt_succ_self k)
        · simp only [Function.comp_apply, Fin.snoc_castSucc, M]
      have e0 : L k ∘ σ = Fin.snoc M A := by
        funext x
        refine Fin.lastCases ?_ (fun j => ?_) x
        · simp only [Function.comp_apply, Fin.snoc_last, hσi, L, i]
          exact if_neg (lt_irrefl k)
        · simp only [Function.comp_apply, Fin.snoc_castSucc]
          exact hMk j
      have hM : ∀ j, M j = A ∨ M j = A' := fun j => hL2 _ _
      have hMs : ∀ j, IsSmoothHerm (M j) := fun j => hLs _ _
      have hmc := metricChange K ι I hI P D M A (fun _ => c) (fun _ _ _ => rfl) hP hMs hA contDiffOn_const
      have s1 := hI.1 P (D + 1) (L (k + 1)) σ hP (hLs _)
      have s0 := hI.1 P (D + 1) (L k) σ hP (hLs _)
      rw [e1] at s1
      rw [e0] at s0
      have hsnoc : I P (D + 1) (Fin.snoc M A') =
          I P (D + 1) (Fin.snoc M A) - ptsIntegral P (pot M) (fun _ => c) := hmc
      rw [← s1, hsnoc, s0, ih (by omega), hint M hM]
      push_cast
      ring
  have hall : L (D + 1) = fun _ => A' := by
    funext j
    exact if_pos j.isLt
  have := step (D + 1) le_rfl
  rw [hall] at this
  rw [this]

theorem G5.proof (hK : ArithKleiman.Statement) (hF : CurvePointsFinite.Statement)
    (hPts : GroundTheory.Heights₂.Heights.PtsIntegralPoints.Statement) : G5.Statement := by
  intro K _ ι _ P P0 D A e II hII hP hP0 hsemi hnef hconj hW
  set A' := A.tensor (constLine (ι := ι) e) with hA'def
  have hA : IsSmoothHerm A := hsemi.1
  have hA' : IsSmoothHerm A' := hA.mul (G5.isSmoothHerm_constLine e)
  have hU : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have hsemi' : IsSemipositiveRel P0 P A' := by
    refine ⟨hA', fun z hz w hw => ?_⟩
    have hev : ∀ᶠ z' in 𝓝 z, Real.log (A'.h z') = Real.log (A.h z') + -e :=
      (show ∀ᶠ z' in 𝓝 z, ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0 from hU.mem_nhds hz.1).mono fun z' hz' => G5.log_tensor_constLine A e z' hz'
    have : leviForm (fun z => Real.log (A'.h z)) z w = leviForm (fun z => Real.log (A.h z)) z w := by
      unfold leviForm
      rw [G5.fderiv_fderiv_eq_of_add_const (-e) hev]
    rw [this]
    exact hsemi.2 z hz w hw
  have ha : A'.a = A.a := by
    show A.a + 0 = A.a
    rw [add_zero]
  have hnef' : NefOnFibres P A'.a := ha ▸ hnef
  have hconj' : IsConjInvariantH A' := fun z => by
    show A.h _ * Real.exp (-e) = A.h z * Real.exp (-e)
    rw [hconj z]
  have hW' : ∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![A'] := by
    intro W hW1 hPW
    have hsn : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (Fin.snoc (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) B : Fin 1 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = ![B] := by
      intro B
      funext j
      fin_cases j
      rfl
    have hmc := metricChange K ι (II K ι) (hII K ι) W 0 ![] A (fun _ => e) (fun _ _ _ => rfl) hW1
      (fun j => j.elim0) hA contDiffOn_const
    rw [hsn, hsn] at hmc
    have : Nonempty K := hW1.1
    have : Finite (GroundTheory.Heights₂.Heights.projPts W) := hF K ι W hW1
    have hpot : pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = Fin.elim0 := Subsingleton.elim _ _
    have hpts := hPts K ι W (fun _ => e) inferInstance (fun _ _ _ _ => rfl)
    have hcount : ptsIntegral W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)) (fun _ => e) = e * degC W := by
      rw [hpot, hpts]
      letI := Fintype.ofFinite (GroundTheory.Heights₂.Heights.projPts W)
      rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        GroundTheory.Heights₂.Heights.degC_eq_card_projPts, Nat.card_eq_fintype_card]
      ring
    have hA'W : II K ι W 1 ![A'] = II K ι W 1 ![A] - e * degC W := by
      rw [← hcount]
      exact hmc
    rw [hA'W]
    linarith [hW W hW1 hPW]
  have hkl := hK K ι P P0 D A' II hII hP hP0 hsemi' hnef' hconj' hW'
  have htop := G5.top_tensor_constLine (II K ι) (hII K ι) P D A e hP hA
  rw [← hA'def] at htop
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

