import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle0002
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PolyExpBound

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.FformSmulRight
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.Core

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

def cw (c : ℝ) (s : Fin m × Fin n × Bool →₀ ℕ) : ℂ :=
  if ∀ a i, s (a, i, false) = s (a, i, true) then
    ∏ a, ∏ i, (((s (a, i, false)).factorial : ℂ) * (2 * c : ℂ) ^ (s (a, i, false))) else 0

theorem contr_eq_sum (c : ℝ) (p : PX m n) (S : Finset (Fin m × Fin n × Bool →₀ ℕ)) (hS : p.support ⊆ S) :
    contr c p = ∑ s ∈ S, p.coeff s * cw c s := by
  unfold contr cw
  rw [← Finset.sum_subset hS]
  · refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  · intro s _ hs
    rw [MvPolynomial.notMem_support_iff.mp hs]
    simp

theorem contr_add (c : ℝ) (p q : PX m n) : contr c (p + q) = contr c p + contr c q := by
  classical
  rw [contr_eq_sum c (p + q) (p.support ∪ q.support) support_add,
    contr_eq_sum c p (p.support ∪ q.support) Finset.subset_union_left,
    contr_eq_sum c q (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_add, add_mul]

theorem contr_smul (c : ℝ) (r : ℂ) (p : PX m n) : contr c (r • p) = r * contr c p := by
  classical
  rw [contr_eq_sum c (r • p) p.support (support_smul), contr_eq_sum c p p.support le_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_smul, smul_eq_mul, mul_assoc]

def contrL (c : ℝ) : PX m n →ₗ[ℂ] ℂ where
  toFun := contr c
  map_add' := contr_add c
  map_smul' := contr_smul c

theorem fform_eq_sum (c : ℝ) (p q : PX m n) (S : Finset (Fin m × Fin n × Bool →₀ ℕ)) (hS : p.support ∪ q.support ⊆ S) :
    fform c p q = ∑ s ∈ S, star (p.coeff s) * q.coeff s * (wt c s : ℂ) := by
  unfold fform
  rw [← Finset.sum_subset hS]
  intro s _ hs
  have h1 : p.coeff s = 0 := MvPolynomial.notMem_support_iff.mp fun h => hs (Finset.mem_union_left _ h)
  simp [h1]

theorem fform_add_right (c : ℝ) (p q₁ q₂ : PX m n) : fform c p (q₁ + q₂) = fform c p q₁ + fform c p q₂ := by
  classical
  set S := p.support ∪ q₁.support ∪ q₂.support
  rw [fform_eq_sum c p (q₁ + q₂) S (Finset.union_subset (by intro x hx; simp [S, hx]) (fun x hx => by
      have := support_add hx; simp only [S, Finset.mem_union] at this ⊢; tauto)),
    fform_eq_sum c p q₁ S (Finset.union_subset (by intro x hx; simp [S, hx]) (by intro x hx; simp [S, hx])),
    fform_eq_sum c p q₂ S (Finset.union_subset (by intro x hx; simp [S, hx]) (by intro x hx; simp [S, hx])),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_add]; ring

theorem fform_smul_right (c : ℝ) (p q : PX m n) (r : ℂ) : fform c p (r • q) = r * fform c p q := by
  classical
  rw [fform_eq_sum c p (r • q) (p.support ∪ q.support) (Finset.union_subset Finset.subset_union_left
      (support_smul.trans Finset.subset_union_right)),
    fform_eq_sum c p q (p.support ∪ q.support) le_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_smul, smul_eq_mul]; ring

end PositivityTheory.Rg.Sw.LC.Core
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.MomLin
section
noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

theorem momLin : MomLin := by
  intro m n c hc P Q r
  have hP := NullS.integrable_pg c hc P
  have hQ := NullS.integrable_pg c hc Q
  constructor
  · unfold mom
    rw [← integral_add hP hQ]
    congr 1
    funext x
    simp only [evX, map_add, add_mul]
  · unfold mom
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [evX, MvPolynomial.smul_eval, mul_assoc]

end PositivityTheory.Rg.Sw.LC
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullOperatorEvaluation
section
noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC.NullS

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

theorem mom_add (c : ℝ) (hc : 0 < c) (P Q : PX m n) : mom c (P + Q) = mom c P + mom c Q := by
  unfold mom
  rw [← integral_add (integrable_pg c hc P) (integrable_pg c hc Q)]
  congr 1
  funext x
  simp only [evX, map_add, add_mul]

theorem mom_C_mul (c : ℝ) (a : ℂ) (P : PX m n) : mom c (C a * P) = a * mom c P := by
  unfold mom
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [evX, map_mul, eval_C, mul_assoc]

theorem mom_sub (c : ℝ) (hc : 0 < c) (P Q : PX m n) : mom c (P - Q) = mom c P - mom c Q := by
  unfold mom
  rw [← integral_sub (integrable_pg c hc P) (integrable_pg c hc Q)]
  congr 1
  funext x
  simp only [evX, map_sub, sub_mul]

theorem mom_sum (c : ℝ) (hc : 0 < c) {ι : Type*} (s : Finset ι) (f : ι → PX m n) :
    mom c (∑ i ∈ s, f i) = ∑ i ∈ s, mom c (f i) := by
  unfold mom
  rw [← integral_finset_sum s (fun i _ => integrable_pg c hc (f i))]
  congr 1
  funext x
  simp only [evX, map_sum, Finset.sum_mul]

theorem pderiv_Sg (c : ℝ) (k : Fin m × Fin n × Bool) :
    pderiv k (Sg c : PX m n) = C (-(c : ℂ)) * X (k.1, k.2.1, !k.2.2) := by
  obtain ⟨a, i, b⟩ := k
  cases b <;> simp [Sg, pderiv_X, Pi.single_apply, Finset.mul_sum, mul_comm, ite_and,
    Finset.sum_ite_eq', Finset.sum_ite_eq]

def Qv (c : ℝ) (P : PX m n) (v : Fin m → Fin n → ℂ) : PX m n :=
  ∑ k, C (crd k v) * (pderiv k P + P * pderiv k (Sg c))

theorem hasFDerivAt_pg (c : ℝ) (P : PX m n) (x : Fin m → Fin n → ℂ) :
    HasFDerivAt (fun y => evX P y * gs c y) (evX P x • (gs c x • dP (Sg c) x) + gs c x • dP P x) x := by
  have hg : HasFDerivAt (fun y : Fin m → Fin n → ℂ => gs c y) (gs c x • dP (Sg c) x) x := by
    have h := (hasFDerivAt_evX (Sg c) x).cexp
    have he : (fun y : Fin m → Fin n → ℂ => gs c y) = fun y => Complex.exp (evX (Sg c) y) :=
      funext (gs_eq c)
    rw [he, gs_eq]
    exact h
  exact (hasFDerivAt_evX P x).mul hg

theorem fderiv_pg (c : ℝ) (P : PX m n) (x v : Fin m → Fin n → ℂ) :
    fderiv ℝ (fun y => evX P y * gs c y) x v = evX (Qv c P v) x * gs c x := by
  rw [(hasFDerivAt_pg c P x).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, dP,
    ContinuousLinearMap.sum_apply, smul_eq_mul, Qv, evX, map_sum, map_add, map_mul, eval_C]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

theorem integral_fderiv_pg (c : ℝ) (hc : 0 < c) (P : PX m n) (v : Fin m → Fin n → ℂ) :
    mom c (Qv c P v) = 0 := by
  unfold mom
  have e : (fun x => evX (Qv c P v) x * gs c x) =
      fun x => (1 : ℂ) * fderiv ℝ (fun y => evX P y * gs c y) x v := by
    funext x
    rw [fderiv_pg, one_mul]
  rw [e, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable]
  · simp
  · simp
  · simpa [fderiv_pg] using integrable_pg c hc (Qv c P v)
  · simpa using integrable_pg c hc P
  · intro x _
    exact differentiableAt_const _
  · intro x _
    exact (hasFDerivAt_pg c P x).differentiableAt

def ev1 (k : Fin m × Fin n × Bool) (z : ℂ) : Fin m → Fin n → ℂ := fun a i => if a = k.1 ∧ i = k.2.1 then z else 0

theorem null_operator_evaluation (c : ℝ) (P : PX m n) (k : Fin m × Fin n × Bool) (z : ℂ) :
    Qv c P (ev1 k z) = C z * (pderiv (k.1, k.2.1, false) P + P * pderiv (k.1, k.2.1, false) (Sg c)) +
      C (star z) * (pderiv (k.1, k.2.1, true) P + P * pderiv (k.1, k.2.1, true) (Sg c)) := by
  obtain ⟨a, i, b⟩ := k
  unfold Qv
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a, Fintype.sum_prod_type, Finset.sum_eq_single i,
    Fintype.sum_bool]
  · simp [crd_apply, ev1, add_comm]
  · intro j _ hj
    simp [crd_apply, ev1, hj]
  · simp
  · intro j _ hj
    simp [crd_apply, ev1, hj]
  · simp

theorem mom_dPhi (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (P : PX m n) :
    mom c (pderiv k P - C (c : ℂ) * X (k.1, k.2.1, !k.2.2) * P) = 0 := by
  obtain ⟨a, i, b⟩ := k
  have h1 := integral_fderiv_pg c hc P (ev1 (a, i, b) 1)
  have h2 := integral_fderiv_pg c hc P (ev1 (a, i, b) Complex.I)
  rw [null_operator_evaluation, mom_add c hc, mom_C_mul, mom_C_mul] at h1 h2
  simp only [star_one, one_mul, Complex.star_def, Complex.conj_I] at h1 h2
  have hu : mom c (pderiv (a, i, false) P + P * pderiv (a, i, false) (Sg c)) = 0 := by
    have h3 : 2 * Complex.I * mom c (pderiv (a, i, false) P + P * pderiv (a, i, false) (Sg c)) = 0 := by
      linear_combination h2 + Complex.I * h1
    simpa [Complex.I_ne_zero] using h3
  have hw : mom c (pderiv (a, i, true) P + P * pderiv (a, i, true) (Sg c)) = 0 := by
    linear_combination h1 - hu
  have key : pderiv (a, i, b) P - C (c : ℂ) * X (a, i, !b) * P =
      pderiv (a, i, b) P + P * pderiv (a, i, b) (Sg c) := by
    rw [pderiv_Sg, map_neg]
    ring
  rw [key]
  cases b
  · exact hu
  · exact hw

end PositivityTheory.Rg.Sw.LC.NullS
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.SupPerp
section
noncomputable section

namespace PositivityTheory.Rg.Sw.LC

namespace CoreA

variable {V : Type} [AddCommGroup V] [Module ℂ V] {φ : V → V → ℂ}

namespace PosH

variable (h : PosH φ)
include h

theorem sup_perp [FiniteDimensional ℂ V] (W : Submodule ℂ V) : W ⊔ h.perp W = ⊤ := by
  classical
  let b := Module.finBasis ℂ W
  let L : V →ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    { toFun := fun v k => φ (b k : V) v
      map_add' := fun v w => by funext k; exact h.add _ v w
      map_smul' := fun r v => by funext k; simp [h.smul] }
  have hker : LinearMap.ker L ≤ h.perp W := by
    intro v hv w hw
    have hv' : ∀ k, φ (b k : V) v = 0 := fun k => congrFun (LinearMap.mem_ker.1 hv) k
    have hw' : w = ∑ k, (b.repr ⟨w, hw⟩ k) • (b k : V) := by
      have h2 : ((∑ k, b.repr ⟨w, hw⟩ k • b k : W) : V) = w := by rw [b.sum_repr]
      rw [Submodule.coe_sum] at h2
      simp only [Submodule.coe_smul] at h2
      exact h2.symm
    rw [hw', h.sum_left]
    simp [hv']
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hr : Module.finrank ℂ (LinearMap.range L) ≤ Module.finrank ℂ W := by
    calc Module.finrank ℂ (LinearMap.range L) ≤ Module.finrank ℂ (Fin (Module.finrank ℂ W) → ℂ) :=
          Submodule.finrank_le _
      _ = Module.finrank ℂ W := by simp
  have hk : Module.finrank ℂ (LinearMap.ker L) ≤ Module.finrank ℂ (h.perp W) := Submodule.finrank_mono hker
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W (h.perp W)
  rw [h.inf_perp, finrank_bot] at hsum
  apply Submodule.eq_top_of_finrank_eq
  apply le_antisymm (Submodule.finrank_le _)
  omega

end PosH

end CoreA

open CoreA in
theorem semiFam : SemiFam := by
  intro V _ _ _ φ hadd hsmul hherm hpos ι T hT
  have h : PosH φ := ⟨hadd, hsmul, hherm, hpos⟩
  refine ⟨fun v => ?_, fun v hv hvW => ?_⟩
  · have hv : v ∈ (⨆ i, LinearMap.range (T i)) ⊔ h.perp (⨆ i, LinearMap.range (T i)) := by
      rw [h.sup_perp]; trivial
    obtain ⟨w, hw, v₀, hv₀, hvw⟩ := Submodule.mem_sup.1 hv
    refine ⟨v₀, w, by rw [← hvw, add_comm], fun i => ?_, hw⟩
    obtain ⟨j, hj⟩ := hT i
    apply h.definite
    have hmem : T j (T i v₀) ∈ ⨆ i, LinearMap.range (T i) :=
      Submodule.mem_iSup_of_mem j (LinearMap.mem_range_self _ _)
    rw [hj, hherm (T j (T i v₀)) v₀, hv₀ _ hmem, star_zero]
  · apply h.definite
    refine Submodule.iSup_induction (motive := fun w => φ w v = 0) _ hvW ?_ (h.zero_left v) ?_
    · intro j w hw
      obtain ⟨u, rfl⟩ := hw
      obtain ⟨j', hj'⟩ := hT j
      rw [hj', hv j', h.zero_right]
    · intro x y hx hy
      rw [h.add_left, hx, hy, add_zero]

end PositivityTheory.Rg.Sw.LC
end
end

