import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0043
import GroundTheory.ArithmeticGeometry.ToricVarieties.Dimension
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0025

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLocalSheets
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj mcPts fibre segre)
open Matrix

namespace ConeLocalSheets

variable {n e : ℕ}

def homogenize (c : MvPolynomial (Fin e) ℂ) : MvPolynomial (Fin (e + 1)) ℂ :=
  ∑ m ∈ c.support, C (coeff m c) * (X 0 ^ (c.totalDegree - m.degree) * rename Fin.succ (monomial m 1))

theorem homogenize_isHomogeneous (c : MvPolynomial (Fin e) ℂ) :
    (homogenize c).IsHomogeneous c.totalDegree := by
  refine IsHomogeneous.sum _ _ _ fun m hm => ?_
  have hle : m.degree ≤ c.totalDegree := le_totalDegree hm
  have h := (isHomogeneous_X_pow (R := ℂ) (0 : Fin (e + 1)) (c.totalDegree - m.degree)).mul
    ((isHomogeneous_monomial (σ := Fin e) (R := ℂ) (d := m) 1 rfl).rename_isHomogeneous (f := Fin.succ))
  rw [Nat.sub_add_cancel hle] at h
  exact h.C_mul _

theorem eval_homogenize (c : MvPolynomial (Fin e) ℂ) (x : Fin e → ℂ) :
    eval (Fin.cons 1 x : Fin (e + 1) → ℂ) (homogenize c) = eval x c := by
  have hcs : (Fin.cons 1 x : Fin (e + 1) → ℂ) ∘ Fin.succ = x := funext fun i => Fin.cons_succ _ _ _
  conv_rhs => rw [c.as_sum]
  simp only [homogenize, map_sum, map_mul, eval_C, map_pow, eval_X, Fin.cons_zero, one_pow, one_mul,
    eval_rename, hcs, eval_monomial]

theorem homogenize_ne_zero {c : MvPolynomial (Fin e) ℂ} (hc : c ≠ 0) : homogenize c ≠ 0 := by
  intro h
  apply hc
  apply MvPolynomial.funext
  intro x
  have := congrArg (eval (Fin.cons 1 x : Fin (e + 1) → ℂ)) h
  rw [eval_homogenize, map_zero] at this
  simpa using this

def lift (z : Fin n → ℂ) : (Σ k, PBlk n k) → ℂ := fun p => z p.2

theorem lift_injective : Function.Injective (lift : (Fin n → ℂ) → (Σ k, PBlk n k) → ℂ) :=
  fun _ _ h => funext fun i => congrFun h ⟨(), i⟩

theorem segre_lift (z : Fin n → ℂ) : segre (lift z) = fun i => z (i ()) := by
  funext i
  simp [segre, lift]

def lin (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
  Ψ ∘ₗ LinearMap.funLeft ℂ ℂ (fun i : Unit → Fin n => i ())

theorem mat_mulVec (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (z : Fin n → ℂ) :
    LinearMap.toMatrix' (lin Ψ) *ᵥ z = Ψ (segre (lift z)) := by
  rw [LinearMap.toMatrix'_mulVec, segre_lift]
  rfl

def chartIdeal (P : Ideal (MRing (PBlk n))) (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.map ((rename (fun p : Σ k, PBlk n k => p.2)).toRingHom.comp (map (Int.castRingHom ℂ))) P ⊔
    Ideal.span {∑ j, C (LinearMap.toMatrix' (lin Ψ) 0 j) * X j - 1}

def tailMat (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Matrix (Fin e) (Fin n) ℂ :=
  (LinearMap.toMatrix' (lin Ψ)).submatrix Fin.succ id

theorem mem_zeroSet_chartIdeal {P : Ideal (MRing (PBlk n))}
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {z : Fin n → ℂ} :
    z ∈ ComplexSets.zeroSet (chartIdeal P Ψ) ↔
      (∀ f ∈ P, eval (lift z) (map (Int.castRingHom ℂ) f) = 0) ∧ Ψ (segre (lift z)) 0 = 1 := by
  have key : ∀ J : Ideal (MvPolynomial (Fin n) ℂ),
      z ∈ ComplexSets.zeroSet J ↔ J ≤ RingHom.ker (eval z) := fun J => by
    simp [ComplexSets.zeroSet, SetLike.le_def, RingHom.mem_ker]
  rw [key, chartIdeal, sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.span_le, Set.singleton_subset_iff,
    ← mat_mulVec]
  refine and_congr ?_ ?_
  · simp only [SetLike.le_def, Ideal.mem_comap, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, eval_rename]
    rfl
  · simp [RingHom.mem_ker, Matrix.mulVec, dotProduct, sub_eq_zero]

theorem eq_cons {v : Fin (e + 1) → ℂ} {y : Fin e → ℂ} (h0 : v 0 = 1) (hs : ∀ i, v i.succ = y i) :
    v = Fin.cons 1 y := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [h0]
  · simp [hs]

theorem tailMat_mulVec (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (z : Fin n → ℂ)
    (i : Fin e) : (tailMat Ψ *ᵥ z) i = Ψ (segre (lift z)) i.succ := by
  rw [← mat_mulVec]
  simp [tailMat, Matrix.mulVec, dotProduct]

theorem of_mem_fibre {P : Ideal (MRing (PBlk n))}
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ} {z : Fin n → ℂ}
    (hz : z ∈ ComplexSets.fibre (chartIdeal P Ψ) (tailMat Ψ) y) :
    lift z ∈ mcPts P ∧ Ψ (segre (lift z)) = Fin.cons 1 y := by
  obtain ⟨hZ, hA⟩ := hz
  obtain ⟨hP, h0⟩ := mem_zeroSet_chartIdeal.mp hZ
  refine ⟨⟨fun k => ?_, hP⟩, eq_cons h0 fun i => by rw [← tailMat_mulVec, hA]⟩
  by_contra hne
  push Not at hne
  have hz0 : z = 0 := funext fun i => hne i
  rw [hz0, ← mat_mulVec, Matrix.mulVec_zero] at h0
  exact zero_ne_one h0

theorem to_mem_fibre {P : Ideal (MRing (PBlk n))}
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w : ((k : Unit) → PBlk n k) → ℂ} (hw : w ∈ fibre P Ψ y) :
    ∃ z ∈ ComplexSets.fibre (chartIdeal P Ψ) (tailMat Ψ) y, segre (lift z) = w := by
  obtain ⟨z, hz, rfl, hΨ⟩ := hw
  have hl : lift (fun i => z ⟨(), i⟩) = z := by
    funext p
    obtain ⟨u, i⟩ := p
    rfl
  refine ⟨fun i => z ⟨(), i⟩, ⟨mem_zeroSet_chartIdeal.mpr ⟨?_, ?_⟩, ?_⟩, by rw [hl]⟩
  · rw [hl]
    exact hz.2
  · rw [hl, hΨ]
    rfl
  · funext i
    rw [tailMat_mulVec, hl, hΨ]
    rfl

theorem fibre_finite {P : Ideal (MRing (PBlk n))}
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hP : IsArithVar P (e + 1))
    (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (ComplexSets.fibre (chartIdeal P Ψ) (tailMat Ψ) y).Finite := by
  have hinj : Function.Injective fun z : Fin n → ℂ => segre (lift z) := by
    intro a b h
    funext i
    simpa [segre_lift] using congrFun h (fun _ => i)
  refine ((ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite Unit (PBlk n) P e Ψ hP hΨ y).preimage hinj.injOn).subset ?_
  intro z hz
  have h := of_mem_fibre hz
  exact ⟨lift z, h.1, rfl, h.2⟩

end ConeLocalSheets

theorem ConeLocalSheets.proof (hQ : QuasiFiniteSheets.Statement) : ConeLocalSheets.Statement := by
  intro n e P Ψ hP hΨ
  obtain ⟨c, hc0, hc⟩ := hQ n e (ConeLocalSheets.chartIdeal P Ψ) (ConeLocalSheets.tailMat Ψ)
    (ConeLocalSheets.fibre_finite hP hΨ)
  refine ⟨ConeLocalSheets.homogenize c, c.totalDegree, ConeLocalSheets.homogenize_ne_zero hc0,
    ConeLocalSheets.homogenize_isHomogeneous c, fun x hx => ?_⟩
  rw [ConeLocalSheets.eval_homogenize] at hx
  obtain ⟨U, N, s, hU, hxU, hs, hsy⟩ := hc x hx
  refine ⟨U, N, fun j y => ConeLocalSheets.lift (s j y), hU, hxU, fun j => ?_, fun y hy => ?_⟩
  · rw [differentiableOn_pi]
    intro p
    exact differentiableOn_pi.mp (hs j) p.2
  · obtain ⟨hval, hinj, hfib⟩ := hsy y hy
    refine ⟨fun j => ConeLocalSheets.of_mem_fibre (hval j),
      fun j k h => hinj (ConeLocalSheets.lift_injective h), ?_⟩
    intro w hw
    obtain ⟨z, hz, rfl⟩ := ConeLocalSheets.to_mem_fibre hw
    obtain ⟨j, hj⟩ := hfib hz
    exact ⟨j, by simp only [hj]⟩

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeProjHyperplaneDim
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre mcPts psiPoly)

namespace ConeProjHyperplaneDim

def coneForm {n e : ℕ} (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (j : Fin (e + 1)) :
    MvPolynomial (Fin n) ℂ :=
  rename (fun p : Σ k : Unit, PBlk n k => p.2) (psiPoly Ψ j)

theorem coneForm_zero {n e : ℕ} (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    coneForm Ψ 0 = coneFirstForm Ψ := rfl

theorem eval_coneForm {n e : ℕ} (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (j : Fin (e + 1)) (z : Fin n → ℂ) :
    eval z (coneForm Ψ j) = Ψ (segre fun p : Σ k, PBlk n k => z p.2) j := by
  rw [coneForm, eval_rename]
  exact ReciprocityTheory.ChartRestriction.G.Geo.eval_psiPoly Ψ j _

theorem segre_one_block {n : ℕ} (x : Fin n → ℂ) :
    segre (fun p : Σ k, PBlk n k => x p.2) = fun f => x (f ()) := by
  funext f
  simp [segre]

theorem cone_rel {n e : ℕ} {P : Ideal (MRing (PBlk n))}
    {Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hP : IsArithVar P (e + 1))
    (hΨ : IsGoodProj P Ψ) (i : Fin n) :
    ∃ r : ℕ, 0 < r ∧ ∃ H : Fin (e + 1) → MvPolynomial (Fin n) ℂ,
      (∀ j, (H j).totalDegree ≤ r - 1) ∧
      X i ^ r - ∑ j, coneForm Ψ j * H j ∈ (complexFibreIdeal P).radical := by
  classical
  obtain ⟨r, hr, G, hG, hrel⟩ := ReciprocityTheory.ChartRestriction.G.Geo.segre_rel hP.2.1.2.1 Ψ hΨ (fun _ => i)
  refine ⟨r, hr, fun j => rename (fun f : (k : Unit) → PBlk n k => f ()) (G j),
    fun j => (totalDegree_rename_le _ _).trans (hG j), ?_⟩
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), mem_vanishingIdeal_iff]
  intro x hx
  have hae : ∀ p : MvPolynomial (Fin n) ℂ, aeval x p = eval x p := fun _ => rfl
  rw [hae]
  have hxP : ∀ q ∈ complexFibreIdeal P, eval x q = 0 := fun q hq => by
    rw [← hae]
    exact hx q hq
  simp only [map_sub, map_pow, eval_X, map_sum, map_mul, eval_coneForm, eval_rename,
    segre_one_block]
  by_cases hx0 : ∃ i0, x i0 ≠ 0
  · obtain ⟨i0, hi0⟩ := hx0
    have hzm : (fun p : Σ k, PBlk n k => x p.2) ∈ mcPts P :=
      ⟨fun _ => ⟨i0, hi0⟩, forall_eval_of_complexFibreIdeal hxP⟩
    have h := hrel _ hzm
    rw [segre_one_block] at h
    rw [sub_eq_zero]
    exact h
  · push Not at hx0
    have hx' : x = 0 := funext hx0
    subst hx'
    have h0 : (fun _ : (k : Unit) → PBlk n k => (0 : ℂ)) = 0 := rfl
    simp only [Pi.zero_apply] at *
    simp [h0, zero_pow hr.ne']

theorem krullDim_le_of_rel {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (L : Fin m → MvPolynomial (Fin n) ℂ) (r : Fin n → ℕ) (hr : ∀ i, 0 < r i)
    (H : Fin n → Fin m → MvPolynomial (Fin n) ℂ) (hH : ∀ i j, (H i j).totalDegree ≤ r i - 1)
    (hrel : ∀ i, X i ^ r i - ∑ j, L j * H i j ∈ I) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) ≤ ((m : ℕ) : WithBot ℕ∞) := by
  classical
  let φ : MvPolynomial (Fin m) ℂ →+* (MvPolynomial (Fin n) ℂ ⧸ I) :=
    (Ideal.Quotient.mk I).comp (aeval L).toRingHom
  let instA : Algebra (MvPolynomial (Fin m) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := φ.toAlgebra
  let instM : Module (MvPolynomial (Fin m) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := instA.toModule
  have hsmul : ∀ (s : MvPolynomial (Fin m) ℂ) (p : MvPolynomial (Fin n) ℂ),
      s • Ideal.Quotient.mk I p = Ideal.Quotient.mk I (aeval L s * p) := by
    intro s p
    rw [Algebra.smul_def]
    rfl
  set M := Submodule.span (MvPolynomial (Fin m) ℂ)
    (((Fintype.piFinset fun i => Finset.range (r i)).image
      (fun α => Ideal.Quotient.mk I (monomial (Finsupp.equivFunOnFinite.symm α) 1))) :
        Set (MvPolynomial (Fin n) ℂ ⧸ I)) with hM
  have hdeg : ∀ N, ∀ β : Fin n →₀ ℕ, (β.sum fun _ e => e) = N →
      Ideal.Quotient.mk I (monomial β 1) ∈ M := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro β hβ
      have hpoly : ∀ q : MvPolynomial (Fin n) ℂ, q.totalDegree < N →
          Ideal.Quotient.mk I q ∈ M := by
        intro q hq
        rw [q.as_sum, map_sum]
        refine Submodule.sum_mem _ fun d hd => ?_
        have hd' : (d.sum fun _ e => e) < N := lt_of_le_of_lt (le_totalDegree hd) hq
        have h1 := ih _ hd' d rfl
        have : Ideal.Quotient.mk I (monomial d (coeff d q)) =
            (C (coeff d q) : MvPolynomial (Fin m) ℂ) • Ideal.Quotient.mk I (monomial d 1) := by
          rw [hsmul, aeval_C, algebraMap_eq, C_mul_monomial, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ h1
      by_cases hsmall : ∀ i, β i < r i
      · apply Submodule.subset_span
        refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨Finsupp.equivFunOnFinite β, ?_, ?_⟩)
        · exact Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr (hsmall i)
        · simp
      · push Not at hsmall
        obtain ⟨i, hi⟩ := hsmall
        set β' := β - Finsupp.single i (r i) with hβ'
        have hβeq : β = β' + Finsupp.single i (r i) := by
          ext i'
          simp only [hβ', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
          by_cases h : i' = i
          · subst h; simp; omega
          · simp [Ne.symm h]
        have hmk : Ideal.Quotient.mk I (monomial β 1) =
            ∑ j, (X j : MvPolynomial (Fin m) ℂ) •
              Ideal.Quotient.mk I (monomial β' 1 * H i j) := by
          have h1 : monomial β (1 : ℂ) = monomial β' 1 * X i ^ r i := by
            rw [hβeq, X_pow_eq_monomial, monomial_mul, one_mul]
          have h2 : Ideal.Quotient.mk I (X i ^ r i) =
              Ideal.Quotient.mk I (∑ j, L j * H i j) :=
            Ideal.Quotient.eq.mpr (hrel i)
          rw [h1, map_mul, h2, ← map_mul, Finset.mul_sum, map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hsmul, aeval_X]
          congr 1
          ring
        rw [hmk]
        refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hpoly _ ?_)
        have hβsum : (β.sum fun _ e => e) = (β'.sum fun _ e => e) + r i := by
          rw [hβeq, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
            Finsupp.sum_single_index rfl]
        calc (monomial β' 1 * H i j).totalDegree
            ≤ (monomial β' (1 : ℂ)).totalDegree + (H i j).totalDegree := totalDegree_mul _ _
          _ ≤ (β'.sum fun _ e => e) + (r i - 1) := by
            rw [totalDegree_monomial _ one_ne_zero]
            exact Nat.add_le_add_left (hH i j) _
          _ < N := by have := hr i; omega
  have : Module.Finite (MvPolynomial (Fin m) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := by
    refine ⟨⟨(Fintype.piFinset fun i => Finset.range (r i)).image
      (fun α => Ideal.Quotient.mk I (monomial (Finsupp.equivFunOnFinite.symm α) 1)), ?_⟩⟩
    rw [← hM, eq_top_iff]
    rintro x -
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [p.as_sum, map_sum]
    refine Submodule.sum_mem _ fun d _ => ?_
    have : Ideal.Quotient.mk I (monomial d (coeff d p)) =
        (C (coeff d p) : MvPolynomial (Fin m) ℂ) • Ideal.Quotient.mk I (monomial d 1) := by
      rw [hsmul, aeval_C, algebraMap_eq, C_mul_monomial, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (hdeg _ d rfl)
  have : Algebra.IsIntegral (MvPolynomial (Fin m) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    Algebra.IsIntegral.of_finite _ _
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) ≤ ringKrullDim (MvPolynomial (Fin m) ℂ) :=
        GroundTheory.Arith.Toric.ringKrullDim_le_of_isIntegral
    _ = ((m : ℕ) : WithBot ℕ∞) := by
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
          Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]

theorem proof : ConeProjHyperplaneDim.Statement := by
  intro n e P Ψ hP hΨ
  classical
  set J := complexFibreIdeal P ⊔ Ideal.span {coneFirstForm Ψ} with hJ
  have hrad : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) =
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J.radical) := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]
  rw [hrad]
  choose r hr H hH hrelP using fun i => cone_rel hP hΨ i
  have h0 : coneForm Ψ 0 ∈ J.radical := by
    rw [coneForm_zero]
    exact Ideal.le_radical (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  refine krullDim_le_of_rel J.radical (fun j : Fin e => coneForm Ψ j.succ) r hr
    (fun i j => H i j.succ) (fun i j => hH i j.succ) (fun i => ?_)
  have h1 : X i ^ r i - ∑ j, coneForm Ψ j * H i j ∈ J.radical :=
    Ideal.radical_mono le_sup_left (hrelP i)
  rw [Fin.sum_univ_succ] at h1
  have heq : X i ^ r i - ∑ j : Fin e, coneForm Ψ j.succ * H i j.succ =
      (X i ^ r i - (coneForm Ψ 0 * H i 0 + ∑ j : Fin e, coneForm Ψ j.succ * H i j.succ)) +
        coneForm Ψ 0 * H i 0 := by ring
  rw [heq]
  exact add_mem h1 (Ideal.mul_mem_right _ _ h0)

end ConeProjHyperplaneDim

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeProjHyperplaneNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

theorem ConeProjHyperplaneNull.proof (hNull : NullSmaller.Statement)
    (hDim : ConeProjHyperplaneDim.Statement) : ConeProjHyperplaneNull.Statement := by
  intro n e P Ψ hP hΨ
  set J : Ideal (MvPolynomial (Fin n) ℂ) := complexFibreIdeal P ⊔ Ideal.span {coneFirstForm Ψ} with hJ

  have hlt : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) < ((e + 1 : ℕ) : WithBot ℕ∞) :=
    (hDim n e P Ψ hP hΨ).trans_lt (by exact_mod_cast Nat.lt_succ_self e)

  refine measure_mono_null (fun z hz => ?_) (hNull n (e + 1) J hlt)
  intro q hq
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hq
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  rw [map_add, map_mul, hz.1 a ha, eval_coneFirstForm, hz.2, mul_zero, add_zero]

end GroundTheory.Heights₂.Heights
end
end

