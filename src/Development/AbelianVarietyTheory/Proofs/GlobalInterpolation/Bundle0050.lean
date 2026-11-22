import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Mathlib
import Formalism.GradedWeylDivisibility.FinalD

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceEPowerHighestWeightValueGeneratingSeries
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem hcRow_succ (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) (i : Fin N) (k : ℕ) :
    ∑ l, (hcMat R μ ^ (k+1)) i l =
      shift R μ i * ∑ l, (hcMat R μ ^ k) i l - ∑ j ∈ Finset.univ.filter (fun j => i < j), ∑ l, (hcMat R μ ^ k) j l := by
  rw [pow_succ']
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hpt : ∀ j : Fin N, hcMat R μ i j * ∑ l, (hcMat R μ ^ k) j l =
      (if j = i then shift R μ i * ∑ l, (hcMat R μ ^ k) j l else 0) +
      (if i < j then -∑ l, (hcMat R μ ^ k) j l else 0) := by
    intro j
    simp only [hcMat, Matrix.of_apply]
    by_cases h1 : j = i
    · subst h1; simp
    · by_cases h2 : i < j
      · simp [h1, h2]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib, Finset.sum_ite_eq' , ← Finset.sum_filter,
    Finset.sum_neg_distrib]
  simp [sub_eq_add_neg]

end GlobalTheory.Alc

namespace GlobalTheory.Alc

def hcRowSeries (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (i : Fin N) : PowerSeries R :=
  PowerSeries.mk fun k => ∑ l, (hcMat R μ ^ k) i l

theorem hcRowSeries_eq (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) (i : Fin N) :
    (1 - PowerSeries.C (shift R μ i) * PowerSeries.X) * hcRowSeries R μ i =
      1 - PowerSeries.X * ∑ j ∈ Finset.univ.filter (fun j => i < j), hcRowSeries R μ j := by
  ext n
  cases n with
  | zero => simp [hcRowSeries, sub_mul, mul_assoc, Matrix.one_apply]
  | succ k =>
    simp [hcRowSeries, sub_mul, mul_assoc, PowerSeries.coeff_succ_X_mul, map_sum, hcRow_succ]

end GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem hcTelescope (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) :
    ∀ d, d ≤ N →
      (1 - PowerSeries.X * ∑ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), hcRowSeries R μ j) *
        ∏ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), (1 - PowerSeries.C (shift R μ j) * PowerSeries.X) =
      ∏ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), (1 - PowerSeries.C (shift R μ j + 1) * PowerSeries.X) := by
  intro d
  induction d with
  | zero =>
    intro _
    have : Finset.univ.filter (fun j : Fin N => N - 0 ≤ j.val) = ∅ := by
      ext j; simp
    rw [this]; simp
  | succ d ih =>
    intro hd
    set i : Fin N := ⟨N - d - 1, by omega⟩ with hi
    have hS : Finset.univ.filter (fun j : Fin N => N - (d+1) ≤ j.val) =
        insert i (Finset.univ.filter (fun j : Fin N => N - d ≤ j.val)) := by
      ext j; simp [hi, Fin.ext_iff]; omega
    have hnot : i ∉ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val) := by
      simp [hi]; omega
    have hgt : Finset.univ.filter (fun j : Fin N => i < j) = Finset.univ.filter (fun j : Fin N => N - d ≤ j.val) := by
      ext j; simp [hi, Fin.lt_iff_val_lt_val]; omega
    have h := hcRowSeries_eq R N μ i
    rw [hgt] at h
    have IH := ih (by omega)
    rw [hS, Finset.sum_insert hnot, Finset.prod_insert hnot, Finset.prod_insert hnot]
    rw [map_add, map_one]
    linear_combination (1 - PowerSeries.C (shift R μ i) * PowerSeries.X - PowerSeries.X) * IH
      - PowerSeries.X * (∏ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), (1 - PowerSeries.C (shift R μ j) * PowerSeries.X)) * h

theorem hcVal_generating (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) :
    (1 - PowerSeries.X * PowerSeries.mk (hcVal R μ)) * ∏ i, (1 - PowerSeries.C (shift R μ i) * PowerSeries.X) =
      ∏ i, (1 - PowerSeries.C (shift R μ i + 1) * PowerSeries.X) := by
  have h := hcTelescope R N μ N le_rfl
  have hU : Finset.univ.filter (fun j : Fin N => N - N ≤ j.val) = Finset.univ := by
    ext j; simp
  have hmk : PowerSeries.mk (hcVal R μ) = ∑ j, hcRowSeries R μ j := by
    ext n; simp [hcVal, hcRowSeries, map_sum]
  rw [hU] at h
  rw [hmk]
  exact h

end GlobalTheory.Alc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedHomogeneousComponentMemOfGLSchemeSubmodu
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

abbrev Laurent (k : Type) [Field k] (N : ℕ) : Type := AddMonoidAlgebra k (Fin N → ℤ)

def laurentVar (k : Type) [Field k] (N : ℕ) (a : Fin N) : (Laurent k N)ˣ where
  val := AddMonoidAlgebra.single (Pi.single a 1) 1
  inv := AddMonoidAlgebra.single (-Pi.single a 1) 1
  val_inv := by simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]
  inv_val := by simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]

theorem prod_laurentVar_pow (k : Type) [Field k] (N : ℕ) (d : Fin N → ℕ) :
    (∏ a, ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N) ^ d a) =
      AddMonoidAlgebra.single (fun a => (d a : ℤ)) 1 := by
  have h : ∀ s : Finset (Fin N), (∏ a ∈ s, ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N) ^ d a) =
      AddMonoidAlgebra.single (∑ a ∈ s, d a • (Pi.single a 1 : Fin N → ℤ)) 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [AddMonoidAlgebra.one_def]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
      simp [laurentVar, AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single]
  rw [h]
  congr 1
  funext b
  simp [Finset.sum_apply, Pi.single_apply]

theorem exists_coeff_of_mem_span {k : Type} [Field k] {N : ℕ} {σ : Type}
    (M : Submodule k (MvPolynomial σ k)) (x : MvPolynomial σ (Laurent k N))
    (hx : x ∈ Submodule.span (Laurent k N)
      (map (algebraMap k (Laurent k N)) '' (M : Set (MvPolynomial σ k)))) :
    ∀ ν : Fin N → ℤ, ∃ h ∈ M, ∀ m, coeff m h = (coeff m x : Laurent k N).coeff ν := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h, hh, rfl⟩ := hy
    intro ν
    by_cases hν : ν = 0
    · refine ⟨h, hh, fun m => ?_⟩
      subst hν
      simp [coeff_map, AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.coeff_single]
    · refine ⟨0, zero_mem _, fun m => ?_⟩
      simp [coeff_map, AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hν]
  | zero =>
    intro ν
    exact ⟨0, zero_mem _, fun m => by simp⟩
  | add y z _ _ hy hz =>
    intro ν
    obtain ⟨a, ha, ha'⟩ := hy ν
    obtain ⟨b, hb, hb'⟩ := hz ν
    exact ⟨a + b, add_mem ha hb, fun m => by simp [ha', hb']⟩
  | smul c y _ hy =>
    induction c using AddMonoidAlgebra.induction_linear with
    | zero =>
      intro ν
      exact ⟨0, zero_mem _, fun m => by simp⟩
    | add c₁ c₂ h₁ h₂ =>
      intro ν
      obtain ⟨a, ha, ha'⟩ := h₁ ν
      obtain ⟨b, hb, hb'⟩ := h₂ ν
      refine ⟨a + b, add_mem ha hb, fun m => ?_⟩
      rw [add_smul]
      simp [ha', hb']
    | single u r =>
      intro ν
      obtain ⟨a, ha, ha'⟩ := hy (-u + ν)
      refine ⟨r • a, Submodule.smul_mem _ _ ha, fun m => ?_⟩
      rw [coeff_smul, coeff_smul, smul_eq_mul, smul_eq_mul, ha']
      exact (AddMonoidAlgebra.coeff_single_mul_apply _ _ _ _).symm

theorem weightedHomogeneousComponent_mem_of_isGLSubmodule (k : Type) [Field k] (N : ℕ) (lam : DomWeight N)
    (M : Submodule k (MvPolynomial (Fin N × Fin N) k)) (hM : GlobalTheory.Published.IsGLSubmodule k N lam M)
    (μ : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) k) (hf : f ∈ M) :
    weightedHomogeneousComponent (rowW N N) μ f ∈ M := by
  have h1 := hM (Laurent k N) (diagGL (Laurent k N) N (laurentVar k N)) f hf
  have hdiag : ((diagGL (Laurent k N) N (laurentVar k N) : GL (Fin N) (Laurent k N)) :
      Matrix (Fin N) (Fin N) (Laurent k N)).transpose =
      Matrix.diagonal fun a => ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N) := by
    show (Matrix.diagonal fun a => ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N)).transpose = _
    exact Matrix.diagonal_transpose _
  have h2 : rowAct (Laurent k N) (n := N)
      (Matrix.diagonal fun a => ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N))
      (map (algebraMap k (Laurent k N)) f) ∈ Submodule.span (Laurent k N)
        (map (algebraMap k (Laurent k N)) '' (M : Set (MvPolynomial (Fin N × Fin N) k))) := by
    let u : (Laurent k N)ˣ :=
      Matrix.GeneralLinearGroup.det (diagGL (Laurent k N) N (laurentVar k N)) ^ lam.detShift
    have h3 := Submodule.smul_mem _ ((u⁻¹ : (Laurent k N)ˣ) : Laurent k N) h1
    have e3 : sqAct (Laurent k N) N lam (diagGL (Laurent k N) N (laurentVar k N))
        (map (algebraMap k (Laurent k N)) f) = (u : Laurent k N) • rowAct (Laurent k N) (n := N)
          (Matrix.diagonal fun a => ((laurentVar k N a : (Laurent k N)ˣ) : Laurent k N))
          (map (algebraMap k (Laurent k N)) f) := by
      unfold sqAct detPow
      rw [hdiag]
    rw [e3, smul_smul, Units.inv_mul, one_smul] at h3
    exact h3
  obtain ⟨h, hh, hc⟩ := exists_coeff_of_mem_span M _ h2 (fun a => (μ a : ℤ))
  have e : weightedHomogeneousComponent (rowW N N) μ f = h := by
    ext m
    rw [hc, coeff_weightedHomogeneousComponent, ldrow_coeff_rowAct_diag, coeff_map,
      prod_laurentVar_pow, AddMonoidAlgebra.coe_algebraMap]
    have hw : Finsupp.weight (rowW N N) m = μ ↔ (fun a => (rowDeg m a : ℤ)) = fun a => (μ a : ℤ) := by
      constructor
      · intro hw
        funext a
        rw [← ldrow_weight_rowW, hw]
      · intro hw
        funext a
        have := congrFun hw a
        rw [ldrow_weight_rowW]
        exact_mod_cast this
    simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hw]
  rw [e]
  exact hh

end GlobalTheory.Alc
end
end

