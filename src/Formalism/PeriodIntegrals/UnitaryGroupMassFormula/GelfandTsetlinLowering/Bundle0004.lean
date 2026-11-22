import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ConstructionB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitPowerNormScale.NormUnitsZpowSq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Bundle0003
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0005
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.AdjBase
section
noncomputable section

namespace PI.WGL.Adj

open Formalism.BasicNotions MvPolynomial

theorem fockF_eq_sum_of_subset {σ : Type} (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    Formalism.REAL.fockF f g =
      ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold Formalism.REAL.fockF
  refine Finset.sum_subset hS ?_
  intro m _ hm
  simp only [MvPolynomial.mem_support_iff, not_not] at hm
  simp [hm]

theorem fockF_add_left {σ : Type} [DecidableEq σ] (f f' g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (f + f') g = Formalism.REAL.fockF f g + Formalism.REAL.fockF f' g := by
  rw [fockF_eq_sum_of_subset (f + f') g _ MvPolynomial.support_add,
    fockF_eq_sum_of_subset f g _ Finset.subset_union_left,
    fockF_eq_sum_of_subset f' g _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]; ring

theorem fockF_add_right {σ : Type} (f g g' : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF f (g + g') = Formalism.REAL.fockF f g + Formalism.REAL.fockF f g' := by
  unfold Formalism.REAL.fockF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, star_add]; ring

theorem den_pos {N : ℕ} (lam : DomWeight N) :
    0 < (Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).re ∧
      (Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).im = 0 :=
  Formalism.GradedWeylDivisibility.fockPos _ _ (Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl lam.natW)

theorem den_eq {N : ℕ} (lam : DomWeight N) :
    Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam) =
      (((Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [(den_pos lam).2])

theorem nf_eq {N : ℕ} (lam : DomWeight N) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f g = Formalism.REAL.fockF f g /
      (((Formalism.REAL.fockF (extremal ℂ N lam) (extremal ℂ N lam)).re : ℝ) : ℂ) := by
  unfold normFock; rw [← den_eq]

theorem nf_herm {N : ℕ} (lam : DomWeight N) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam g f = star (normFock lam f g) := by
  rw [nf_eq, nf_eq, Formalism.GradedWeylDivisibility.fockHerm, star_div₀, Complex.star_def, Complex.conj_ofReal]

theorem nf_add_left {N : ℕ} (lam : DomWeight N) (f f' g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (f + f') g = normFock lam f g + normFock lam f' g := by
  unfold normFock; rw [fockF_add_left, add_div]

theorem nf_add_right {N : ℕ} (lam : DomWeight N) (f g g' : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f (g + g') = normFock lam f g + normFock lam f g' := by
  unfold normFock; rw [fockF_add_right, add_div]

theorem nf_smul_left {N : ℕ} (lam : DomWeight N) (c : ℂ) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (c • f) g = c * normFock lam f g := by
  unfold normFock; rw [PI.WHw.bC_smul_left, mul_div_assoc]

theorem nf_smul_right {N : ℕ} (lam : DomWeight N) (c : ℂ) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f (c • g) = star c * normFock lam f g := by
  unfold normFock; rw [PI.WHw.bC_smul_right, mul_div_assoc]

def nfL {N : ℕ} (lam : DomWeight N) (g : MvPolynomial (Fin N × Fin N) ℂ) :
    MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] ℂ where
  toFun f := normFock lam f g
  map_add' f f' := nf_add_left lam f f' g
  map_smul' c f := by simp [nf_smul_left]

theorem nfL_apply {N : ℕ} (lam : DomWeight N) (g f : MvPolynomial (Fin N × Fin N) ℂ) :
    nfL lam g f = normFock lam f g := rfl

theorem nf_sum_smul_left {N : ℕ} (lam : DomWeight N) {ι : Type} (S : Finset ι) (a : ι → ℂ)
    (v : ι → MvPolynomial (Fin N × Fin N) ℂ) (g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (∑ k ∈ S, a k • v k) g = ∑ k ∈ S, a k * normFock lam (v k) g := by
  rw [← nfL_apply, map_sum]
  simp [nfL_apply]

theorem nf_sum_smul_right {N : ℕ} (lam : DomWeight N) {ι : Type} (S : Finset ι) (a : ι → ℂ)
    (v : ι → MvPolynomial (Fin N × Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f (∑ k ∈ S, a k • v k) = ∑ k ∈ S, star (a k) * normFock lam f (v k) := by
  rw [nf_herm, nf_sum_smul_left, star_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul', ← nf_herm]

theorem nf_sub_right {N : ℕ} (lam : DomWeight N) (f g g' : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f (g - g') = normFock lam f g - normFock lam f g' := by
  rw [nf_herm, ← nfL_apply, map_sub, star_sub, nfL_apply, nfL_apply, ← nf_herm, ← nf_herm]

theorem nf_zero_right {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f 0 = 0 := by
  have := nf_smul_right lam 0 f 0
  simpa using this

theorem nf_self_im {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    (normFock lam f f).im = 0 := by
  rw [nf_eq, Complex.div_ofReal_im]
  by_cases hf : f = 0
  · subst hf; simp [Formalism.REAL.fockF]
  · rw [(Formalism.GradedWeylDivisibility.fockPos _ f hf).2, zero_div]

theorem nf_self_re_pos {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) (hf : f ≠ 0) :
    0 < (normFock lam f f).re := by
  rw [nf_eq, Complex.div_ofReal_re]
  exact div_pos (Formalism.GradedWeylDivisibility.fockPos _ f hf).1 (den_pos lam).1

theorem nf_self_re_nonneg {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    0 ≤ (normFock lam f f).re := by
  by_cases hf : f = 0
  · subst hf; rw [nf_zero_right]; simp
  · exact (nf_self_re_pos lam f hf).le

theorem nf_self_eq_zero {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (h : normFock lam f f = 0) : f = 0 := by
  by_contra hf
  have := nf_self_re_pos lam f hf
  rw [h] at this; simp at this

theorem nf_self_eq_re {N : ℕ} (lam : DomWeight N) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam f f = (((normFock lam f f).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [nf_self_im])

theorem nf_extremal {N : ℕ} (lam : DomWeight N) :
    normFock lam (extremal ℂ N lam) (extremal ℂ N lam) = 1 := by
  unfold normFock
  refine div_self ?_
  intro h0
  have := (den_pos lam).1
  rw [h0] at this; simp at this

def nfCore {N : ℕ} (lam : DomWeight N) : InnerProductSpace.Core ℂ (MvPolynomial (Fin N × Fin N) ℂ) where
  inner x y := normFock lam y x
  conj_inner_symm x y := by
    show starRingEnd ℂ (normFock lam x y) = normFock lam y x
    rw [starRingEnd_apply, ← nf_herm]
  re_inner_nonneg x := nf_self_re_nonneg lam x
  add_left x y z := nf_add_right lam z x y
  smul_left x y r := by
    show normFock lam y (r • x) = starRingEnd ℂ r * normFock lam y x
    rw [nf_smul_right, starRingEnd_apply]
  definite x hx := nf_self_eq_zero lam x hx

theorem nf_cauchy_schwarz {N : ℕ} (lam : DomWeight N) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    ‖normFock lam y x‖ * ‖normFock lam x y‖ ≤ (normFock lam x x).re * (normFock lam y y).re := by
  letI : PreInnerProductSpace.Core ℂ (MvPolynomial (Fin N × Fin N) ℂ) := (nfCore lam).toCore
  exact InnerProductSpace.Core.inner_mul_inner_self_le x y

def frameCore (n : ℕ) (sg : DomWeight n) : InnerProductSpace.Core ℂ (nablaSq ℂ n sg) where
  inner x y := normFock sg (y : MvPolynomial (Fin n × Fin n) ℂ) x
  conj_inner_symm x y := by
    show starRingEnd ℂ (normFock sg (x : MvPolynomial (Fin n × Fin n) ℂ) y) = normFock sg (y : MvPolynomial (Fin n × Fin n) ℂ) x
    rw [starRingEnd_apply, ← nf_herm]
  re_inner_nonneg x := nf_self_re_nonneg sg x
  add_left x y z := by
    show normFock sg (z : MvPolynomial (Fin n × Fin n) ℂ) ((x + y : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ) = _
    rw [Submodule.coe_add, nf_add_right]
  smul_left x y r := by
    show normFock sg (y : MvPolynomial (Fin n × Fin n) ℂ) ((r • x : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ) = _
    rw [Submodule.coe_smul, nf_smul_right, starRingEnd_apply]
  definite x hx := by
    have := nf_self_eq_zero sg (x : MvPolynomial (Fin n × Fin n) ℂ) hx
    exact Subtype.ext this

theorem exists_frame (n : ℕ) (sg : DomWeight n) :
    ∃ (d : ℕ) (b : Fin d → MvPolynomial (Fin n × Fin n) ℂ), (∀ k, b k ∈ nablaSq ℂ n sg) ∧
      ∀ s ∈ nablaSq ℂ n sg, s = ∑ k, normFock sg s (b k) • b k := by
  letI : NormedAddCommGroup (nablaSq ℂ n sg) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ (frameCore n sg)
  letI : InnerProductSpace ℂ (nablaSq ℂ n sg) := InnerProductSpace.ofCore (frameCore n sg).toCore
  haveI : FiniteDimensional ℂ (nablaSq ℂ n sg) := PI.WHw.bC_fd n n sg.natW
  let b := stdOrthonormalBasis ℂ (nablaSq ℂ n sg)
  refine ⟨Module.finrank ℂ (nablaSq ℂ n sg), fun k => (b k : MvPolynomial (Fin n × Fin n) ℂ),
    fun k => (b k).2, fun s hs => ?_⟩
  have h1 := congrArg Subtype.val (b.sum_repr' ⟨s, hs⟩)
  rw [Submodule.coe_sum] at h1
  exact h1.symm

end PI.WGL.Adj
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.CapelliShift
section
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem glRel_shift {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) (c : ℂ) :
    Formalism.REAL.GlRel (fun a b => E a b + if a = b then algebraMap ℂ A c else 0) := by
  have key : ∀ (p : Prop) [Decidable p] (y : A),
      (if p then algebraMap ℂ A c else 0) * y = y * (if p then algebraMap ℂ A c else 0) := by
    intro p _ y
    split_ifs
    · exact Algebra.commutes c y
    · simp
  intro i j k l
  simp only
  have h1 := key (i = j) (E k l)
  have h2 := key (k = l) (E i j)
  have h3 := key (i = j) (if k = l then algebraMap ℂ A c else 0)
  calc (E i j + if i = j then algebraMap ℂ A c else 0) * (E k l + if k = l then algebraMap ℂ A c else 0) -
        (E k l + if k = l then algebraMap ℂ A c else 0) * (E i j + if i = j then algebraMap ℂ A c else 0)
      = (E i j * E k l - E k l * E i j)
        + ((if i = j then algebraMap ℂ A c else 0) * E k l - E k l * (if i = j then algebraMap ℂ A c else 0))
        - ((if k = l then algebraMap ℂ A c else 0) * E i j - E i j * (if k = l then algebraMap ℂ A c else 0))
        + ((if i = j then algebraMap ℂ A c else 0) * (if k = l then algebraMap ℂ A c else 0)
          - (if k = l then algebraMap ℂ A c else 0) * (if i = j then algebraMap ℂ A c else 0)) := by
        noncomm_ring
    _ = E i j * E k l - E k l * E i j := by rw [h1, h2, h3]; abel
    _ = (if j = k then E i l else 0) - (if l = i then E k j else 0) := hE i j k l
    _ = _ := by
        by_cases hjk : j = k <;> by_cases hli : l = i
        · subst hjk; subst hli; simp
        · have hil : ¬ i = l := fun h => hli h.symm
          simp [hjk, hli, hil]
        · have hkj : ¬ k = j := fun h => hjk h.symm
          simp [hjk, hli, hkj]
        · simp [hjk, hli]

def capE {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (a b : Fin n) :
    Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
  pol ℂ (Fin.castLE (by omega) a) (Fin.castLE (by omega) b) +
    if a = b then algebraMap ℂ _ (lam.detShift : ℂ) else 0

theorem capE_glRel {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) : Formalism.REAL.GlRel (capE h lam) := by
  have hP := pol_glRel N N
  have hR : Formalism.REAL.GlRel (fun a b : Fin n =>
      (pol ℂ (Fin.castLE (by omega : n ≤ N) a) (Fin.castLE (by omega : n ≤ N) b) :
        Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ))) := by
    intro i j k l
    have := hP (Fin.castLE (by omega) i) (Fin.castLE (by omega) j) (Fin.castLE (by omega) k)
      (Fin.castLE (by omega) l)
    simp only [Fin.castLE_inj] at this
    exact this
  exact glRel_shift _ hR _

theorem capE_apply {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (a b : Fin n) (x : MvPolynomial (Fin N × Fin N) ℂ) :
    capE h lam a b x = pol ℂ (Fin.castLE (by omega) a) (Fin.castLE (by omega) b) x +
      if a = b then (lam.detShift : ℂ) • x else 0 := by
  unfold capE
  split_ifs
  · rw [LinearMap.add_apply, Module.algebraMap_end_apply]
  · simp

end PI.WGL
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTupleD
section
noncomputable section

namespace PI.WGL.LTD

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC

theorem sum_ite_val {n : ℕ} (f : Fin n → ℕ) (j : ℕ) :
    (∑ i : Fin n, if i.1 = j then f i else 0) = if h : j < n then f ⟨j, h⟩ else 0 := by
  split_ifs with hj
  · rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro i _ hi; rw [if_neg]; intro h'; exact hi (Fin.ext h')
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · apply Finset.sum_eq_zero; intro i _; rw [if_neg]; intro h'; exact hj (h' ▸ i.2)

theorem natW_sg_val {n : ℕ} (sg : DomWeight n) (i : Fin n) :
    ((sg.natW i : ℕ) : ℤ) = sg.w i - sg.w ⟨n - 1, by have := i.2; omega⟩ := by
  have hle : i ≤ ⟨n - 1, by have := i.2; omega⟩ := by rw [Fin.le_def]; simp; have := i.2; omega
  have := sg.anti hle
  simp only [DomWeight.natW, DomWeight.detShift, dif_pos (show 0 < n by have := i.2; omega)]
  rw [Int.toNat_of_nonneg (by omega)]

theorem card_lt_sz {n K : ℕ} (sg : DomWeight n) (sz : Fin K → ℕ) (hshape : shapeDeg sz = sg.natW)
    (t : Fin n) : (Finset.univ.filter fun k => t.1 < sz k).card = sg.natW t := by
  rw [← hshape]; rfl

theorem sz_lt {n K : ℕ} (sg : DomWeight n) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (hshape : shapeDeg sz = sg.natW) (k : Fin K) : sz k < n ∨ sz k = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · right; have := hsz k; omega
  · left
    have h1 := card_lt_sz sg sz hshape ⟨n - 1, by omega⟩
    have h0 : sg.natW ⟨n - 1, by omega⟩ = 0 := by
      simp [DomWeight.natW, DomWeight.detShift, dif_pos hn]
    rw [h0, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1
    have hk := h1 (Finset.mem_univ k)
    simp only [not_lt] at hk
    have := hsz k
    omega

theorem card_eq_sz {n K : ℕ} (sg : DomWeight n) (sz : Fin K → ℕ) (hshape : shapeDeg sz = sg.natW)
    (i : ℕ) (hi : i + 1 < n) :
    (Finset.univ.filter fun k => sz k = i + 1).card = sg.natW ⟨i, by omega⟩ - sg.natW ⟨i + 1, hi⟩ := by
  have h1 := card_lt_sz sg sz hshape ⟨i, by omega⟩
  have h2 := card_lt_sz sg sz hshape ⟨i + 1, hi⟩
  simp only at h1 h2
  rw [← h1, ← h2]
  have : (Finset.univ.filter fun k => i < sz k) =
      (Finset.univ.filter fun k => i + 1 < sz k) ∪ (Finset.univ.filter fun k => sz k = i + 1) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; omega
  rw [this, Finset.card_union_of_disjoint]
  · omega
  · rw [Finset.disjoint_filter]; intro k _ h1 h2; omega

theorem goodL_exists {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    {K : ℕ} (sz : Fin K → ℕ) (hshape : shapeDeg sz = sg.natW) :
    ∃ L : Finset (Fin K), GoodL h lam sg sz L := by
  classical
  have hB : ∀ i : Fin n, (if i.1 = 0 then 0 else (bb h lam sg i).toNat) ≤
      (Finset.univ.filter fun k => sz k = i.1).card := by
    intro i
    split_ifs with hi0
    · exact Nat.zero_le _
    · obtain ⟨iv, hiv⟩ := i
      obtain ⟨j, rfl⟩ : ∃ j, iv = j + 1 := ⟨iv - 1, by simp at hi0; omega⟩
      have hc := card_eq_sz sg sz hshape j hiv
      simp only at hc ⊢
      rw [hc]
      have e1 := natW_sg_val sg ⟨j, by omega⟩
      have e2 := natW_sg_val sg ⟨j + 1, hiv⟩
      have hb := (hI ⟨j + 1, hiv⟩).1
      have ha := (hI ⟨j, by omega⟩).2
      unfold bb
      simp only at hb ha e1 e2 ⊢
      omega
  choose T hT using fun i : Fin n => Finset.exists_subset_card_eq (hB i)
  refine ⟨Finset.univ.biUnion T, ?_, ?_⟩
  · intro k hk
    obtain ⟨i, _, hki⟩ := Finset.mem_biUnion.mp hk
    have hs := (hT i).1 hki
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    by_cases hi0 : i.1 = 0
    · have hc := (hT i).2
      rw [if_pos hi0, Finset.card_eq_zero] at hc
      rw [hc] at hki; exact absurd hki (Finset.notMem_empty k)
    · omega
  · intro i
    rw [← (hT i).2]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨j, hkj⟩, hsk⟩
      have hs := (hT j).1 hkj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      have : j = i := Fin.ext (by omega)
      subst this; exact hkj
    · intro hki
      have hs := (hT i).1 hki
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      exact ⟨⟨i, hki⟩, hs⟩

end PI.WGL.LTD
end
end

