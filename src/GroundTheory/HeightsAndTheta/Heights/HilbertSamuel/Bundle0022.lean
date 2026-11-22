import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0044
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FrechetDerivEvaluation
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.MeasurableResPtHsmProjLine
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

def ResChiSymMeasure.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
    Measurable (resPt d) → ∀ n : ℕ,
      resChi d n = chi d.x d.m (IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure (resPt d) d.dV) n

def ResolutionL2SymmetricMeasure.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
    Measurable (resPt d) → ∀ (n : ℕ) (f : MvPolynomial (Ix κ) ℤ), f.IsHomogeneous n →
      resolutionSectionL2Norm d n f = IndefiniteRowSideFullHecke.HilbertSamuel.secNorm d.x d.m (IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure (resPt d) d.dV) n
        (aeval d.x f)

namespace ProjLine

attribute [local instance] projectiveLineMeasurableSpace

theorem measurable_resPt_hsmProjLine : Measurable (resPt hsmProjLine) := by
  show Measurable fun x : OnePoint ℂ => ProjectiveLineResolution.lift x x
  refine measurable_of_continuousOn_compl_singleton OnePoint.infty ?_
  have hc : ContinuousOn crd0 ({OnePoint.infty}ᶜ : Set (OnePoint ℂ)) := by
    rw [OnePoint.compl_infty]
    exact continuousOn_finiteCoord
  have hv : ContinuousOn (fun x : OnePoint ℂ => ProjectiveLineResolution.vec 1 (crd0 x)) {OnePoint.infty}ᶜ := by
    refine continuousOn_pi.2 fun q => ?_
    obtain ⟨⟨⟩, i⟩ := q
    fin_cases i
    · exact continuousOn_const
    · exact hc
  refine hv.congr fun x hx => ?_
  have hx' : x ≠ OnePoint.infty := hx
  simp [ProjectiveLineResolution.lift, hx']

theorem ResChiSymMeasure.hyps_inhabited :
    ∃ d : HSMDatum 1 FnField (Fin 2), Measurable (resPt d) :=
  ⟨hsmProjLine, measurable_resPt_hsmProjLine⟩

end ProjLine

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDegreePositive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

namespace DegreePositive

variable {F : Type} [Field F] {ι₀ : Type} [Fintype ι₀]

theorem ringKrullDim_of_mem_minimalPrimes (q W : Ideal (MRing (fun _ : Unit => ι₀) F)) [q.IsPrime]
    (x : MRing (fun _ : Unit => ι₀) F) (hx : x ∉ q) (e : ℕ)
    (hdim : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) = ((e + 1 : ℕ) : WithBot ℕ∞))
    (hmin : W ∈ (q ⊔ Ideal.span {x}).minimalPrimes) :
    ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = ((e : ℕ) : WithBot ℕ∞) := by
  have hWprime : W.IsPrime := hmin.1.1
  have hIW : q ≤ W := le_sup_left.trans hmin.1.2
  have hxW : x ∈ W := (le_sup_right.trans hmin.1.2) (Ideal.mem_span_singleton_self _)
  set B := MRing (fun _ : Unit => ι₀) F ⧸ q
  have _ : Algebra.FiniteType F B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F q) (Ideal.Quotient.mkₐ_surjective F q)
  set W' : Ideal B := W.map (Ideal.Quotient.mk q)
  have hW'prime : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := by
    intro h
    apply hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk q x ∈ W' := Ideal.mem_map_of_mem _ hxW
    rw [h, Ideal.mem_bot] at this
    exact this
  have hht : W'.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot] at hform hdrop
  change ringKrullDim B = _ at hdim
  rw [hdim] at hform hdrop
  obtain ⟨y, hy⟩ : ∃ y : ℕ∞, ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = y := by
    cases h : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) with
    | bot =>
      have := ringKrullDim_nonneg_of_nontrivial (R := MRing (fun _ : Unit => ι₀) F ⧸ W)
      rw [h] at this
      exact absurd this (by simp)
    | coe y => exact ⟨y, rfl⟩
  rw [hy] at hform hdrop ⊢
  have h1 : y + 1 ≤ ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast hdrop
  have h2 : W'.height + y = ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast hform
  have hyle : y ≤ e := by
    have : y + 1 ≤ (e : ℕ∞) + 1 := by exact_mod_cast h1
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℕ∞) = y := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top
    (ENat.natCast_ne_top e) hyle)
  have h3 : ((e + 1 : ℕ) : ℕ∞) ≤ 1 + m := by rw [← h2]; gcongr
  have h4 : e + 1 ≤ 1 + m := by exact_mod_cast h3
  have h5 : m ≤ e := by exact_mod_cast hyle
  have : m = e := by omega
  subst this
  rfl

omit [Fintype ι₀] in

theorem isRelevant_of_ringKrullDim (W : Ideal (MRing (fun _ : Unit => ι₀) F)) [W.IsPrime] (e : ℕ)
    (hW : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    IsRelevant W := by
  intro k
  by_contra h
  simp only [not_exists, not_not] at h
  have hX : ∀ v : (Σ _ : Unit, ι₀), (X v : MRing (fun _ : Unit => ι₀) F) ∈ W := by
    rintro ⟨⟨⟩, i⟩
    cases k
    exact h i
  have hsurj : Function.Surjective (algebraMap F (MRing (fun _ : Unit => ι₀) F ⧸ W)) := by
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction p using MvPolynomial.induction_on with
    | C a =>
      exact ⟨a, by rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]⟩
    | add p r hp hr =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hr
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | mul_X p v _ =>
      refine ⟨0, ?_⟩
      rw [map_zero, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (hX v), mul_zero]
  have hle := ringKrullDim_le_of_surjective _ hsurj
  rw [hW, ringKrullDim_eq_zero_of_field] at hle
  have : e + 1 ≤ 0 := by exact_mod_cast hle
  omega

set_option synthInstance.maxHeartbeats 400000 in

theorem hilbFn_pos (q : Ideal (MRing (fun _ : Unit => ι₀) F)) (hq : IsMultiProjPrime q) (n : ℕ) :
    0 < hilbFn q (fun _ => (n : ℤ)) := by
  obtain ⟨i, hi⟩ := hq.relevant ()
  have hqp := hq.isPrime
  obtain ⟨hfin, heq⟩ :=
    GroundTheory.Heights₂.Heights.FieldNumbers.GradedFinite.full F Unit (fun _ => ι₀) q (fun _ => n)
  have heq' : hilbFn q (fun _ => (n : ℤ)) =
      (Module.finrank F (gradedPiece q (fun _ : Unit => n)) : ℤ) := heq
  rw [heq']
  have hmem : Ideal.Quotient.mk q ((X ⟨(), i⟩ : MRing (fun _ : Unit => ι₀) F) ^ n) ∈
      gradedPiece q (fun _ : Unit => n) := by
    refine ⟨(X ⟨(), i⟩ : MRing (fun _ : Unit => ι₀) F) ^ n, ?_, rfl⟩
    change _ ∈ weightedHomogeneousSubmodule F (blockWeight (fun _ : Unit => ι₀)) (fun _ : Unit => n)
    rw [mem_weightedHomogeneousSubmodule]
    have hp := (isWeightedHomogeneous_X F (blockWeight (fun _ : Unit => ι₀)) ⟨(), i⟩).pow n
    convert hp using 1
    funext k
    cases k
    simp [blockWeight]
  have hne : Ideal.Quotient.mk q ((X ⟨(), i⟩ : MRing (fun _ : Unit => ι₀) F) ^ n) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => hi (hqp.mem_of_pow_mem n h)
  have := hfin
  have : Nontrivial (gradedPiece q (fun _ : Unit => n)) :=
    ⟨⟨⟨_, hmem⟩, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < Module.finrank F (gradedPiece q (fun _ : Unit => n)) := Module.finrank_pos
  exact_mod_cast hpos

omit [Fintype ι₀] in

theorem le_ker_constantCoeff (q : Ideal (MRing (fun _ : Unit => ι₀) F)) (hq : IsMultiProjPrime q) :
    q ≤ RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F) := by
  intro p hp
  rw [RingHom.mem_ker]
  by_contra h
  have h0 := hq.multiHomog p hp 0
  rw [weightedHomogeneousComponent_zero p (fun v => by
    obtain ⟨⟨⟩, _⟩ := v
    intro h'
    have := congrFun h' ()
    simp [blockWeight] at this)] at h0
  have hu : IsUnit (C (coeff 0 p) : MRing (fun _ : Unit => ι₀) F) :=
    (isUnit_iff_ne_zero.mpr (by rwa [← constantCoeff_eq])).map C
  exact hq.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 hu)

theorem pos (D : ℕ) : ∀ q : Ideal (MRing (fun _ : Unit => ι₀) F), IsMultiProjPrime q →
    ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) = ((D + 1 : ℕ) : WithBot ℕ∞) →
    0 < intNum F q (fun _ : Fin D => fun _ => (1 : ℤ)) := by
  induction D with
  | zero =>
    intro q hq hd
    obtain ⟨a₀, ha⟩ := HilbertDimZero.proof F Unit (fun _ => ι₀) q hq
      (by rw [Fintype.card_unit]; exact hd)
    have h := ha (fun _ => a₀) (fun _ => le_rfl)
    have e : (fun _ : Fin 0 => fun _ : Unit => (1 : ℤ)) = (![] : Fin 0 → Unit → ℤ) :=
      funext fun j => j.elim0
    rw [e, ← h]
    exact hilbFn_pos q hq a₀
  | succ D ih =>
    intro q hq hd
    have hqp : q.IsPrime := hq.isPrime
    obtain ⟨i, hX⟩ := hq.relevant ()
    set x : MRing (fun _ : Unit => ι₀) F := X ⟨(), i⟩ with hxdef
    have hx : IsMultiHomog x (blockWeight (fun _ : Unit => ι₀) ⟨(), i⟩) :=
      isWeightedHomogeneous_X F _ _
    have hlt : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) <
        ((D + 2 + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
      rw [hd, Fintype.card_unit]
      exact_mod_cast (by omega : D + 1 + 1 < D + 2 + 1)
    have hcut := CutByForm.full F Unit (fun _ => ι₀) D q hqp hq.multiHomog hlt x _ hx hX
      (fun _ : Fin D => fun _ : Unit => (1 : ℤ))
    have e1 : Matrix.vecCons (fun k => ((blockWeight (fun _ : Unit => ι₀) ⟨(), i⟩ k : ℕ) : ℤ))
        (fun _ : Fin D => fun _ : Unit => (1 : ℤ)) = fun _ : Fin (D + 1) => fun _ : Unit => (1 : ℤ) := by
      funext j k
      cases k
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [blockWeight]
    rw [e1] at hcut
    rw [hcut, cycEval]
    set J := q ⊔ Ideal.span {x} with hJdef
    have hJh : IsMultiHomogIdeal J := isMultiHomogIdeal_sup_span_of_form hq.multiHomog hx

    have hterm : ∀ W, divCycle q x W ≠ 0 →
        0 < divCycle q x W ∧ 0 < intNum F W (fun _ : Fin D => fun _ : Unit => (1 : ℤ)) := by
      intro W hW
      unfold divCycle at hW ⊢
      by_cases hc : W ∈ J.minimalPrimes ∧ IsRelevant W
      · rw [dif_pos hc] at hW ⊢
        have hWp : W.IsPrime := hc.1.1.1
        have hWd := ringKrullDim_of_mem_minimalPrimes q W x hX (D + 1) hd hc.1
        have hWq : IsMultiProjPrime W :=
          ⟨hWp, MinimalPrimeMultiHomog.full F Unit (fun _ => ι₀) J W hJh hc.1, hc.2⟩
        exact ⟨lt_of_le_of_ne (by positivity) (Ne.symm hW), ih W hWq hWd⟩
      · rw [dif_neg hc] at hW
        exact absurd rfl hW
    have hfin := DivCycleFiniteSupport.full F Unit (fun _ => ι₀) q x
    rw [finsum_eq_sum_of_support_subset _
      ((Function.support_mul_subset_left _ _).trans hfin.coe_toFinset.symm.subset)]
    refine Finset.sum_pos' (fun W _ => ?_) ?_
    · by_cases hW : divCycle q x W = 0
      · rw [hW, zero_mul]
      · exact (mul_pos (hterm W hW).1 (hterm W hW).2).le

    have hJm : J ≤ RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F) := by
      refine sup_le (le_ker_constantCoeff q hq) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]
      change constantCoeff x = 0
      rw [hxdef, constantCoeff_X]
    have hmax : (RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F)).IsPrime :=
      (RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, by simp⟩).isPrime
    obtain ⟨W, hmin, -⟩ := Ideal.exists_minimalPrimes_le hJm
    have hWp : W.IsPrime := hmin.1.1
    have hWd := ringKrullDim_of_mem_minimalPrimes q W x hX (D + 1) hd hmin
    have hrel := isRelevant_of_ringKrullDim W D hWd
    have hne : divCycle q x W ≠ 0 := by
      unfold divCycle
      rw [dif_pos ⟨hmin, hrel⟩]
      have htop := length_localizedQuot_ne_top J W hmin
      have hzero : multAt J W ≠ 0 := by
        unfold multAt
        rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
        intro hs
        obtain ⟨r, hr, hr1⟩ := hs (1 : MRing (fun _ : Unit => ι₀) F ⧸ J)
        rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hr1
        exact hr (hmin.1.2 hr1)
      have : (multAt J W).toNat ≠ 0 := by
        rw [Ne, ENat.toNat_eq_zero]
        exact not_or.mpr ⟨hzero, htop⟩
      exact_mod_cast this
    refine ⟨W, hfin.mem_toFinset.mpr hne, mul_pos (hterm W hne).1 (hterm W hne).2⟩

end DegreePositive

theorem DegreePositive.proof : DegreePositive.Statement := by
  intro F _ ι₀ _ q D hq hd
  exact DegreePositive.pos D q hq hd

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

namespace NefOnGenericOfSemipos

theorem hasFDerivAt_eval {σ : Type*} [Fintype σ] (g : MvPolynomial σ ℂ) (z : σ → ℂ) :
    HasFDerivAt (fun x : σ → ℂ => eval x g)
      (∑ i, eval z (pderiv i g) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i) z :=
  _root_.UpperTheory.Reformulated.B.FrechetDerivEvaluation.hasFDerivAt_eval g z

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem maDensity_nonneg {P P0 W : Ideal (MRing ι)} {A : HermLine ι} (hP0 : P0 ≤ P) (hPW : P ≤ W)
    (hs : IsSemipositiveRel P0 P A) {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (1 + 1) → ℂ)}
    {y : Fin 1 → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin 1 → ℂ) → (Σ k, ι k) → ℂ}
    (h : IsSheet W Ψ y w γ) :
    0 ≤ maDensity (fun _ y' => Real.log (A.h (γ y'))) y := by
  have hA : AnalyticAt ℂ γ y := sheet_analyticAt osgood h
  have hz : γ y ∈ mcPts W := h.2.self_of_nhds.2.1
  have hne : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := hz.1
  have hzP : γ y ∈ mcPts P := ⟨hz.1, fun f hf => hz.2 f (hPW hf)⟩
  have hφ : ContDiffAt ℝ 2 (fun z => Real.log (A.h z)) (γ y) :=
    ((hs.1.contDiffAt (isOpen_blockNonzero.mem_nhds hne)).of_le
      (WithTop.coe_le_coe.mpr le_top)).log (A.pos _ hne).ne'
  have htan : IsConeTangent (Int.castRingHom ℂ) P0 (γ y) (fderiv ℂ γ y (Pi.single 0 1)) := by
    intro f hf
    have h0 : (fun y' => eval (γ y') (map (Int.castRingHom ℂ) f)) =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
      filter_upwards [h.2] with y' hy'
      exact hy'.2.1.2 f (hPW (hP0 hf))
    have hd := (hasFDerivAt_eval (map (Int.castRingHom ℂ) f) (γ y)).comp y
      hA.differentiableAt.hasFDerivAt
    have h00 := (hasFDerivAt_const (𝕜 := ℂ) (0 : ℂ) y).congr_of_eventuallyEq h0
    have := congrArg (fun L => L (Pi.single 0 1)) (hd.unique h00)
    simpa using this
  have hlevi : 0 ≤ ReciprocityTheory.AnForm.levi (fun z => Real.log (A.h z)) (γ y)
      (fderiv ℂ γ y (Pi.single 0 1)) := hs.2 (γ y) hzP _ htan
  have key := ReciprocityTheory.AnForm.levi_comp (Pi.single 0 1) hA hφ
  rw [← key] at hlevi
  unfold ReciprocityTheory.AnForm.levi at hlevi
  simp only [Function.comp_def] at hlevi
  rw [maDensity_one]
  apply div_nonneg _ (by positivity)
  linarith

theorem geomDeg_one_nonneg {P P0 W : Ideal (MRing ι)} {A : HermLine ι} (hP0 : P0 ≤ P)
    (hs : IsSemipositiveRel P0 P A) (hPW : P ≤ W) : 0 ≤ geomDeg W A 1 := by
  classical
  unfold geomDeg ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    refine MeasureTheory.integral_nonneg fun y => ?_
    refine finsum_nonneg fun w => finsum_nonneg fun _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · simpa only [one_mul] using maDensity_nonneg hP0 hPW hs hγ.choose_spec
    · exact le_rfl
  · exact le_rfl

end NefOnGenericOfSemipos

theorem NefOnGenericOfSemipos.proof : NefOnGenericOfSemipos.Statement :=
  fun _ _ _ _ _ _ _ hP0 hs _ _ hPW => NefOnGenericOfSemipos.geomDeg_one_nonneg hP0 hs hPW

theorem ArithmeticVolumeBig.of_moriwakiBig_only (hM : MoriwakiBigStatement) : ArithmeticVolumeBig.Statement :=
  ArithmeticVolumeBig.of_moriwakiBig NefOnGenericOfSemipos.proof hM

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountMonoLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter

noncomputable section

theorem chartLat_le_chartLatNm {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) :
    chartLat y a τ ≤ chartLatNm y a τ := by
  intro s hs c hc
  have h := hs c hc
  rw [mem_integralClosure_iff]
  exact isIntegral_algebraMap (R := chartRingZ y c) (A := Ω) (x := ⟨_, h⟩)

theorem smallSectionCount_mono_lattice {Ω : Type*} [CommRing Ω] (P : ℕ → Ω → Prop) {La La' : ℕ → AddSubgroup Ω}
    (τ : ℕ) (hle : La τ ≤ La' τ) (hfin : {s : La' τ | P τ (s : Ω)}.Finite) :
    smallSectionCount P La τ ≤ smallSectionCount P La' τ := by
  unfold smallSectionCount
  have : Finite {s : La' τ // P τ (s : Ω)} := hfin.to_subtype
  have hc : Nat.card {s : La τ // P τ (s : Ω)} ≤ Nat.card {s : La' τ // P τ (s : Ω)} := by
    refine Nat.card_le_card_of_injective
      (fun s => (⟨⟨(s.1 : Ω), hle s.1.2⟩, s.2⟩ : {s : La' τ // P τ (s : Ω)})) ?_
    intro s t hst
    exact Subtype.ext (Subtype.ext (congrArg (fun u : {s : La' τ // P τ (s : Ω)} => ((u.1 : La' τ) : Ω)) hst))
  rcases Nat.eq_zero_or_pos (Nat.card {s : La τ // P τ (s : Ω)}) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hc)

theorem ArithmeticVolumeBigRefined.proof (hG6p : ArithmeticVolumeBig.Statement) (hPk : PackingStatement) :
    ArithmeticVolumeBigRefined.Statement := by
  intro K _ ι _ Ω _ y D A P0 II hD hII har hb hP0 hs hnef hc
  refine (hG6p K ι Ω y D A P0 II hD hII har hb hP0 hs hnef hc).trans ?_
  obtain ⟨hfin, C, hC⟩ := hPk K ι Ω y D A (chartLatNm y A.a) har hb hs.1 (fun _ => le_rfl)
  unfold arVolP
  simp only [one_mul]
  have hden : ∀ k : ℕ, 0 ≤ ((k : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := fun k => by positivity
  refine limsup_le_limsup (Eventually.of_forall fun k => div_le_div_of_nonneg_right
      (smallSectionCount_mono_lattice _ k (chartLat_le_chartLatNm y A.a k) (hfin k)) (hden k)) ?_ ?_
  · exact isCoboundedUnder_le_of_le atTop (fun k => div_nonneg (Real.log_natCast_nonneg _) (hden k))
  · refine isBoundedUnder_of_eventually_le (a := |C| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ))
      (eventually_atTop.2 ⟨1, fun k hk => ?_⟩)
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hF : (0 : ℝ) < (D + 1).factorial := by positivity
    have hkp : (0 : ℝ) < (k : ℝ) ^ (D + 1) := by positivity
    rw [div_le_iff₀ (by positivity)]
    have h2 : C * ((k : ℝ) + 1) ^ (D + 1) ≤ |C| * (2 * (k : ℝ)) ^ (D + 1) :=
      calc C * ((k : ℝ) + 1) ^ (D + 1) ≤ |C| * ((k : ℝ) + 1) ^ (D + 1) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ |C| * (2 * (k : ℝ)) ^ (D + 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) (abs_nonneg C)
    calc smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) k
        ≤ |C| * (2 * (k : ℝ)) ^ (D + 1) := (hC k).trans h2
      _ = |C| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ) * ((k : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
          rw [mul_pow]; field_simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAnResToAnalyticRes
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory
open scoped Manifold ContDiff

noncomputable section

def AnResToAnalyticRes.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
    ∃ (M : Type) (_ : TopologicalSpace M) (_ : T2Space M) (_ : CompactSpace M)
      (_ : ChartedSpace (Fin D → ℂ) M) (_ : IsManifold 𝓘(ℂ, Fin D → ℂ) ∞ M)
      (_ : MeasurableSpace M) (_ : BorelSpace M) (f : M → Ix κ → ℂ) (dV : Measure M),
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.IsAnalyticRes (coordIdeal ℤ d.x) D f ∧
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.IsSmoothVolume D dV ∧
      (∀ n : ℕ, chi d.x d.m (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure f dV) n = resChi d n) ∧
      ∀ (n : ℕ) (g : MvPolynomial (Ix κ) ℤ), g.IsHomogeneous n →
        l2Norm d.m (Int.castRingHom ℂ) (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure f dV) n g =
          resolutionSectionL2Norm d n g

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArithKleiman
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def ArithKleiman.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (D : ℕ)
    (A : HermLine ι) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar P (D + 1) → P0 ≤ P → IsSemipositiveRel P0 P A →
    NefOnFibres P A.a → IsConjInvariantH A →
    (∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![A]) →
    0 ≤ II K ι P (D + 1) (fun _ => A)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCurvePointsFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def CurvePointsFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι)),
    IsArithVar W 1 → Finite (GroundTheory.Heights₂.Heights.projPts W)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

