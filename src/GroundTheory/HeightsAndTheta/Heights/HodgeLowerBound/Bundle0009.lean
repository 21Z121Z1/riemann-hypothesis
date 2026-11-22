import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PlueckerCoordinates.IsHodgeFibrePt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PlueckerCoordinates.FlagLine
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.FlagLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.IsMultiHomogChartMonomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

section Homog

variable {κ : Type} [Fintype κ] {ι : κ → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_C (c : ℤ) : IsMultiHomog (C c : MRing ι) 0 := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_C] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm

theorem isMultiHomog_prod {σ : Type} (s : Finset σ) (f : σ → MRing ι) (d : σ → κ → ℕ)
    (h : ∀ a ∈ s, IsMultiHomog (f a) (d a)) : IsMultiHomog (∏ a ∈ s, f a) (∑ a ∈ s, d a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ProjLine.isMultiHomog_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact ProjLine.mhMul (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem isMultiHomog_chartMonomial (c : ∀ k, ι k) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι)) (fun _ => 1) := by
  classical
  have h := isMultiHomog_prod (Finset.univ : Finset κ) (fun k => (X ⟨k, c k⟩ : MRing ι))
    (fun k => fun k1 => if k1 = k then 1 else 0) (fun k _ => ProjLine.isMultiHomog_X ⟨k, c k⟩)
  have hs : (∑ k : κ, (fun k1 : κ => if k1 = k then 1 else 0 : κ → ℕ)) = fun _ => 1 := by
    funext k1
    simp [Finset.sum_apply]
  rwa [hs] at h

end Homog

section Values

variable {κ : Type} [Fintype κ] {ι : κ → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem mem_mCoordIdeal_of_aeval {f : MRing ι} {d : κ → ℕ} (hf : IsMultiHomog f d)
    (h0 : aeval y f = 0) : f ∈ mCoordIdeal y := by
  rw [mCoordIdeal, RingHom.mem_ker, ConeTrdeg.mConeMap_of_isMultiHomog y hf, h0, map_zero, zero_mul]

theorem IsValueAt.unique {a : Ω} {v v' : ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    (h : IsValueAt y a z v) (h' : IsValueAt y a z v') : v = v' := by
  obtain ⟨d, g, h1, hg, hh, hy, hyg, hz1, hzg⟩ := h
  obtain ⟨d', g', h1', hg', hh', hy', hyg', hz1', hzg'⟩ := h'
  have hm : IsMultiHomog (g * h1' - g' * h1) (d + d') := by
    rw [sub_eq_add_neg]
    refine ProjLine.mhAdd (ProjLine.mhMul hg hh') (ProjLine.mhNeg ?_)
    rw [add_comm]
    exact ProjLine.mhMul hg' hh
  have h0 : aeval y (g * h1' - g' * h1) = 0 := by
    rw [map_sub, map_mul, map_mul, hyg, hyg']
    ring
  have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval hm h0)
  rw [map_sub, map_mul, map_mul, eval_sub, eval_mul, eval_mul, hzg, hzg', sub_eq_zero] at hz0
  have hne : eval z (map (Int.castRingHom ℂ) h1) * eval z (map (Int.castRingHom ℂ) h1') ≠ 0 :=
    mul_ne_zero hz1 hz1'
  apply mul_right_cancel₀ hne
  linear_combination hz0

theorem valAt_eq {a : Ω} {v : ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (h : IsValueAt y a z v) :
    valAt y a z = v := by
  have hr : RegularAt y a z := ⟨v, h⟩
  rw [valAt, dif_pos hr]
  exact IsValueAt.unique hz hr.choose_spec h

theorem RegularAt.isValueAt {a : Ω} (hz : z ∈ mcPts (mCoordIdeal y)) (h : RegularAt y a z) :
    IsValueAt y a z (valAt y a z) := by
  obtain ⟨v, hv⟩ := h
  rwa [valAt_eq hz hv]

theorem IsValueAt.mul {a b : Ω} {v w : ℂ} (ha : IsValueAt y a z v) (hb : IsValueAt y b z w) :
    IsValueAt y (a * b) z (v * w) := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  obtain ⟨d', g', h', hg', hh', hy', hyg', hz', hzg'⟩ := hb
  refine ⟨d + d', g * g', h * h', ProjLine.mhMul hg hg', ProjLine.mhMul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [map_mul]
    exact mul_ne_zero hy hy'
  · simp only [map_mul]
    rw [hyg, hyg']
    ring
  · rw [map_mul, eval_mul]
    exact mul_ne_zero hz hz'
  · simp only [map_mul, eval_mul]
    rw [hzg, hzg']
    ring

theorem IsValueAt.add {a b : Ω} {v w : ℂ} (ha : IsValueAt y a z v) (hb : IsValueAt y b z w) :
    IsValueAt y (a + b) z (v + w) := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  obtain ⟨d', g', h', hg', hh', hy', hyg', hz', hzg'⟩ := hb
  have hd : IsMultiHomog (g' * h) (d + d') := by
    rw [add_comm]
    exact ProjLine.mhMul hg' hh
  refine ⟨d + d', g * h' + g' * h, h * h', ProjLine.mhAdd (ProjLine.mhMul hg hh') hd,
    ProjLine.mhMul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [map_mul]
    exact mul_ne_zero hy hy'
  · simp only [map_add, map_mul]
    rw [hyg, hyg']
    ring
  · rw [map_mul, eval_mul]
    exact mul_ne_zero hz hz'
  · simp only [map_add, map_mul, eval_add, eval_mul]
    rw [hzg, hzg']
    ring

theorem IsValueAt.neg {a : Ω} {v : ℂ} (ha : IsValueAt y a z v) : IsValueAt y (-a) z (-v) := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  refine ⟨d, -g, h, ProjLine.mhNeg hg, hh, hy, ?_, hz, ?_⟩
  · rw [map_neg, hyg]
    ring
  · rw [map_neg, eval_neg, hzg]
    ring

theorem isValueAt_intCast (n : ℤ) : IsValueAt y (n : Ω) z (n : ℂ) := by
  refine ⟨0, C n, 1, isMultiHomog_C n, ProjLine.isMultiHomog_one, by simp, by simp, by simp, by simp⟩

theorem isValueAt_one : IsValueAt y (1 : Ω) z 1 := by
  simpa using isValueAt_intCast (y := y) (z := z) 1

theorem isValueAt_zero : IsValueAt y (0 : Ω) z 0 := by
  simpa using isValueAt_intCast (y := y) (z := z) 0

theorem IsValueAt.sum {σ : Type} (s : Finset σ) {a : σ → Ω} {v : σ → ℂ}
    (h : ∀ i ∈ s, IsValueAt y (a i) z (v i)) : IsValueAt y (∑ i ∈ s, a i) z (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isValueAt_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem RegularAt.mul {a b : Ω} (ha : RegularAt y a z) (hb : RegularAt y b z) : RegularAt y (a * b) z :=
  ⟨_, ha.choose_spec.mul hb.choose_spec⟩

theorem RegularAt.add {a b : Ω} (ha : RegularAt y a z) (hb : RegularAt y b z) : RegularAt y (a + b) z :=
  ⟨_, ha.choose_spec.add hb.choose_spec⟩

theorem RegularAt.sum {σ : Type} (s : Finset σ) {a : σ → Ω} (h : ∀ i ∈ s, RegularAt y (a i) z) :
    RegularAt y (∑ i ∈ s, a i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simpa using isValueAt_zero⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

omit [Fintype κ] [∀ k, Fintype (ι k)] in

theorem eval_conj (f : MRing ι) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => starRingEnd ℂ (z p)) (map (Int.castRingHom ℂ) f) =
      starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by
  rw [eval_map, eval_map, eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

theorem IsValueAt.conj {a : Ω} {v : ℂ} (ha : IsValueAt y a z v) :
    IsValueAt y a (fun p => starRingEnd ℂ (z p)) (starRingEnd ℂ v) := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  refine ⟨d, g, h, hg, hh, hy, hyg, ?_, ?_⟩
  · rw [eval_conj]
    exact (map_ne_zero _).2 hz
  · rw [eval_conj, eval_conj, hzg, map_mul]

theorem IsValueAt.smul {a : Ω} {v : ℂ} (s : κ → ℂ) (hs : ∀ k, s k ≠ 0) (ha : IsValueAt y a z v) :
    IsValueAt y a (fun p => s p.1 * z p) v := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hzg⟩ := ha
  refine ⟨d, g, h, hg, hh, hy, hyg, ?_, ?_⟩
  · rw [eval_smul_homog h d hh]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hs k)) hz
  · rw [eval_smul_homog h d hh, eval_smul_homog g d hg, hzg]
    ring

theorem regularAt_of_mem_chartRing (hz : z ∈ mcPts (mCoordIdeal y)) {c : ∀ k, ι k}
    (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) {a : Ω} (ha : a ∈ chartRing ℤ (NumbersDVR.segreVec y) c) :
    RegularAt y a z := by
  have hden : NumbersDVR.segreVec y c ≠ 0 := by
    intro h0
    have hm := mem_mCoordIdeal_of_aeval (y := y) (isMultiHomog_chartMonomial c)
      (by simpa [NumbersDVR.segreVec] using h0)
    have := hz.2 _ hm
    simp only [map_prod, map_X, eval_prod, eval_X] at this
    exact Finset.prod_ne_zero_iff.2 (fun k _ => hc k) this
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨c', rfl⟩ := hx
    have hz0 : eval z (map (Int.castRingHom ℂ) (∏ k, (X ⟨k, c k⟩ : MRing ι))) ≠ 0 := by
      simp only [map_prod, map_X, eval_prod, eval_X]
      exact Finset.prod_ne_zero_iff.2 fun k _ => hc k
    refine ⟨eval z (map (Int.castRingHom ℂ) (∏ k, (X ⟨k, c' k⟩ : MRing ι))) /
      eval z (map (Int.castRingHom ℂ) (∏ k, (X ⟨k, c k⟩ : MRing ι))), fun _ => 1,
      ∏ k, (X ⟨k, c' k⟩ : MRing ι), ∏ k, (X ⟨k, c k⟩ : MRing ι), isMultiHomog_chartMonomial c',
      isMultiHomog_chartMonomial c, ?_, ?_, hz0, ?_⟩
    · simpa [NumbersDVR.segreVec] using hden
    · simp only [map_prod, aeval_X]
      show NumbersDVR.segreVec y c' = NumbersDVR.segreVec y c' / NumbersDVR.segreVec y c *
        NumbersDVR.segreVec y c
      rw [div_mul_cancel₀ _ hden]
    · rw [div_mul_cancel₀ _ hz0]
  | algebraMap r =>
    exact ⟨r, by simpa using isValueAt_intCast (y := y) (z := z) r⟩
  | add a b _ _ ha hb => exact ha.add hb
  | mul a b _ _ ha hb => exact ha.mul hb

end Values

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassPush
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

def FlagGrassPush.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N j : ℕ) (cf : ℚ),
    IsIntersectionSystem II → 2 ≤ N → 1 ≤ j → j ≤ N - 1 →
    -hFl Ψ N II (FA Ψ N j cf) *
        geomDeg (grassIdeal (Fintype.card Ψ) j (N - j))
          (GroundTheory.Heights₂.Heights.fsMulti (plBlocks (Fintype.card Ψ) j (N - j))) (dimN Ψ N j) =
      (Jint Ψ N j cf : ℝ) *
        II (Fin (Fintype.card Ψ)) (plBlocks (Fintype.card Ψ) j (N - j)) (grassIdeal (Fintype.card Ψ) j (N - j))
          (dimN Ψ N j + 1) (fun _ => GroundTheory.Heights₂.Heights.fsMulti (plBlocks (Fintype.card Ψ) j (N - j)))

example (cf : ℚ) : Nonempty Unit ∧ 2 ≤ 2 ∧ 1 ≤ 1 ∧ 1 ≤ 2 - 1 ∧ dimN Unit 2 1 = 1 ∧
    FA Unit 2 1 cf = C cf * X ((), 1) ^ 2 ∧ Jint Unit 2 1 cf = -cf ∧ Fintype.card (PlIdx 1 (2 - 1)) = 2 := by
  refine ⟨⟨()⟩, le_rfl, le_rfl, le_rfl, rfl, FA_line cf, Jint_line cf, ?_⟩
  decide

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuModelDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.HilbertSamuel

def MuModelDegree.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (P : PlueckerData D)
    (H : HodgeData D.toComponentData), (∀ τ, H.F τ = D.F τ) →
    geomDeg (PXmu P) (muRefLine P) D.toComponentData.n =
      (genDeg (mCoordIdeal D.y) D.toComponentData.n H.aMu : ℝ)

namespace LineFlag

noncomputable def HL : HodgeData DL.toComponentData := Line.lineHodge Line.zeroSystem fun _ _ => le_rfl

end LineFlag

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuModelPointSteps
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

def IsHodgeFrame (D : ComponentDataHodge II Ψ K ι Ω E) (τ : Ψ) (b : Fin D.N → E τ) : Prop :=
  ∃ (c : (k : K) → ι k) (f : Ω), IsFrameOver D.y (D.W τ) c f b ∧
    Submodule.span Ω (b '' {i | (i : ℕ) < D.j}) = D.F τ

theorem exists_hodgeFrame (D : ComponentDataHodge II Ψ K ι Ω E) :
    ∃ b : ∀ τ, Fin D.N → E τ, ∀ τ, IsHodgeFrame D τ (b τ) := by
  have hy : ∀ k, ∃ i, D.y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := D.arith.2.1.2.2 k
    refine ⟨i, fun h => hi ?_⟩
    show mConeMap D.y (X ⟨k, i⟩) = 0
    simp [mConeMap, h]
  choose c hc using hy
  have hseg : segreCoord D.y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have : ∀ τ, ∃ b : Fin D.N → E τ, IsHodgeFrame D τ b := by
    intro τ
    obtain ⟨m, f, a, -, -, hsum, hfr⟩ := D.hodge τ c hseg
    obtain ⟨l, hl⟩ : ∃ l, f l ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      simp [h] at hsum
    obtain ⟨b, hb, hspan⟩ := hfr l hl
    exact ⟨b, c, f l, hb, hspan⟩
  choose b hb using this
  exact ⟨b, hb⟩

variable [DecidableEq Ψ] {D : ComponentDataHodge II Ψ K ι Ω E}

def muPointOf (P : PlueckerData D) (b : ∀ τ, Fin D.N → E τ) : (Σ k : MuBlocks D, ιMu P k) → Ω
  | ⟨Sum.inl k, i⟩ => D.y ⟨k, i⟩
  | ⟨Sum.inr (Sum.inl τ), m⟩ => P.gen τ (jIdx D) m (b τ ∘ Fin.castLE (jIdx D).isLt)
  | ⟨Sum.inr (Sum.inr τ), m⟩ => P.gen τ (lastIdx D) m (b τ ∘ Fin.castLE (lastIdx D).isLt)

def MuPointVanish.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (P : PlueckerData D)
    (b : ∀ τ, Fin D.N → E τ), (∀ τ, IsHodgeFrame D τ (b τ)) →
    ∀ G ∈ mCoordIdeal (muPointOf P b), ∀ u ∈ muPts P, eval u (map (Int.castRingHom ℂ) G) = 0

def MuPointDense.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (P : PlueckerData D)
    (b : ∀ τ, Fin D.N → E τ), (∀ τ, IsHodgeFrame D τ (b τ)) →
    PXmu P ≤ mCoordIdeal (muPointOf P b)

theorem MuPointVanish.objects_line :
    Nonempty (PlueckerData LineFlag.DL) ∧ ∃ b : Unit → Fin LineFlag.DL.N → (Fin 2 → _), ∀ τ, IsHodgeFrame LineFlag.DL τ (b τ) :=
  ⟨⟨LineFlag.PL⟩, exists_hodgeFrame _⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPlueckerArith
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def ComponentData.flagDim {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) : ℕ :=
  Fintype.card Ψ * (D.N * (D.N - 1) / 2)

def PlueckerArith.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D),
    IsArithVar Pl.PY (D.n + 1 + D.flagDim)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsZhangLowerX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo

def ZhangLowerX.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (n : ℕ)
    (A : HermLine ι) (e : ℝ) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar P (n + 1) → P0 ≤ P → IsSemipositiveRel P0 P A →
    NefOnFibres P A.a → IsConjInvariantH A →
    (∀ W, IsArithVar W 1 → P ≤ W → e ≤ IndefiniteRowSideFullHecke.HeightsSet.height (II K ι) A W) →
    ((n + 1 : ℕ) : ℝ) * e * geomDeg P A n ≤ II K ι P (n + 1) (fun _ => A)

theorem ZhangLowerX.hyps_inhabited :
    IsArithVar (mCoordIdeal (ι := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.GlobalTheory (Fin 2)) HilbertSamuel.ProjLine.y) (1 + 1) ∧
      ⊥ ≤ mCoordIdeal (ι := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.GlobalTheory (Fin 2)) HilbertSamuel.ProjLine.y ∧
      IsSemipositiveRel ⊥ (mCoordIdeal (ι := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.GlobalTheory (Fin 2)) HilbertSamuel.ProjLine.y)
        HilbertSamuel.ProjLine.fsLine1 ∧
      NefOnFibres (mCoordIdeal (ι := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.GlobalTheory (Fin 2)) HilbertSamuel.ProjLine.y)
        HilbertSamuel.ProjLine.fsLine1.a ∧
      IsConjInvariantH HilbertSamuel.ProjLine.fsLine1 :=
  HilbertSamuel.G5.hyps_inhabited

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.VarMapInjective
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace FlagModelAlt

section Defs

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

def stepTw {N : ℕ} (i : Fin (N - 1)) : Fin N := Fin.castLE (Nat.sub_le N 1) i

@[simp] theorem stepTw_val {N : ℕ} (i : Fin (N - 1)) : ((stepTw i : Fin N) : ℕ) = i := rfl

structure Match {D : ComponentDataHodge II Ψ K ι Ω E} (Pl : PlueckerData D.toComponentData)
    (P : IndefiniteRowSideFullHecke.LowerBoundFree.PlueckerData D) : Prop where
  twist : ∀ τ i, Pl.bdeg τ i = P.b
  M_eq : ∀ τ i, Pl.M τ i = P.M τ (stepTw i)
  gen_eq : ∀ τ (i : Fin (D.N - 1)) m (v : Fin ((i : ℕ) + 1) → E τ),
    Pl.gen τ i m (exteriorPower.ιMulti Ω _ v) = P.gen τ (stepTw i) (Fin.cast (M_eq τ i) m) v

variable {D : ComponentDataHodge II Ψ K ι Ω E} {Pl : PlueckerData D.toComponentData}
  {P : IndefiniteRowSideFullHecke.LowerBoundFree.PlueckerData D}

def varMap (h : Match Pl P) : (Σ k, Pl.ιY k) → (Σ k, IndefiniteRowSideFullHecke.LowerBoundFree.ιY P k)
  | ⟨Sum.inl k, t⟩ => ⟨Sum.inl k, (t : ι k)⟩
  | ⟨Sum.inr q, m⟩ => ⟨Sum.inr (q.1, stepTw q.2), Fin.cast (h.M_eq q.1 q.2) m⟩

def forget (h : Match Pl P) : MRing Pl.ιY →ₐ[ℤ] MRing (IndefiniteRowSideFullHecke.LowerBoundFree.ιY P) :=
  rename (varMap h)

end Defs

section Inhabitant

open Line IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag

abbrev linePlData : PlueckerData lineDataHodgeZero.toComponentData := linePl zeroSystem fun _ _ => le_rfl

end Inhabitant

end FlagModelAlt

def FlagModelAlt.Statement : Prop :=
  ∀ {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (Pl : PlueckerData D.toComponentData)
    (P : IndefiniteRowSideFullHecke.LowerBoundFree.PlueckerData D) (h : FlagModelAlt.Match Pl P),
    Pl.PY = (IndefiniteRowSideFullHecke.LowerBoundFree.PY P).comap (FlagModelAlt.forget h)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

