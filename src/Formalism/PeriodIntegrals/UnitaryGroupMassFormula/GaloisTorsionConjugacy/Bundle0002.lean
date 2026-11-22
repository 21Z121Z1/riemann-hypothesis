import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.AddLaw
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.WpOnto

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.IncAdjInclusion
section
noncomputable section

namespace PI.GalTorsConj.W

open Polynomial

def incAdj (M M₁ : IntermediateField ℚ ℂ) : M₁ →+* IntermediateField.adjoin M (M₁ : Set ℂ) where
  toFun x := ⟨x, IntermediateField.subset_adjoin M _ x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem incAdj_inclusion (M M₁ : IntermediateField ℚ ℂ) (h : M ≤ M₁) (x : M) :
    incAdj M M₁ (IntermediateField.inclusion h x) = algebraMap M _ x := Subtype.ext rfl

theorem extRho : ExtRho := by
  intro M M₁ h halg ρ
  letI iA : Algebra M M₁ := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI hA : Algebra.IsAlgebraic M M₁ := by
    refine ⟨fun x => ?_⟩
    let f : M₁ →ₐ[M] ℂ :=
      { toRingHom := (M₁.val : M₁ →+* ℂ)
        commutes' := fun _ => rfl }
    exact (isAlgebraic_algHom_iff f M₁.val.injective).mp (halg x x.2)
  letI iC : Algebra M ℂ := ρ.toRingHom.toAlgebra
  let φ : M₁ →ₐ[M] ℂ := IsAlgClosed.lift
  refine ⟨{ toRingHom := φ.toRingHom, commutes' := φ.toRingHom.map_rat_algebraMap }, fun x => ?_⟩
  exact φ.commutes x

theorem descent : Descent := by
  classical
  intro M M₁ h halg x hx
  by_contra hxM
  have hint : IsIntegral M (x : ℂ) := (halg x x.2).isIntegral
  have hsep : (minpoly M (x : ℂ)).Separable := (minpoly.irreducible hint).separable
  have hdeg : 2 ≤ (minpoly M (x : ℂ)).natDegree := by
    have h1 : (minpoly M (x : ℂ)).natDegree ≠ 1 := by
      intro h1
      apply hxM
      obtain ⟨m, hm⟩ := minpoly.natDegree_eq_one_iff.mp h1
      rw [← hm]
      exact m.2
    have h0 : 0 < (minpoly M (x : ℂ)).natDegree := minpoly.natDegree_pos hint
    omega
  have hc : Fintype.card ((minpoly M (x : ℂ)).rootSet ℂ) = (minpoly M (x : ℂ)).natDegree :=
    Polynomial.card_rootSet_eq_natDegree hsep (IsAlgClosed.splits _)
  have hxr : (x : ℂ) ∈ (minpoly M (x : ℂ)).rootSet ℂ :=
    Polynomial.mem_rootSet.mpr ⟨minpoly.ne_zero hint, minpoly.aeval M (x : ℂ)⟩
  have h2 : 1 < Fintype.card ((minpoly M (x : ℂ)).rootSet ℂ) := by omega
  obtain ⟨⟨y, hyr⟩, hyx'⟩ := Fintype.exists_ne_of_one_lt_card h2 (⟨(x : ℂ), hxr⟩ :
    (minpoly M (x : ℂ)).rootSet ℂ)
  have hyx : y ≠ (x : ℂ) := fun e => hyx' (Subtype.ext e)
  have hy : y ∈ (minpoly M (x : ℂ)).aroots ℂ :=
    Polynomial.mem_aroots.mpr ⟨minpoly.ne_zero hint, (Polynomial.mem_rootSet.mp hyr).2⟩
  let K : IntermediateField M ℂ := IntermediateField.adjoin M {(x : ℂ)}
  let τ : K →ₐ[M] ℂ := (IntermediateField.algHomAdjoinIntegralEquiv M hint).symm ⟨y, hy⟩
  have hτ : τ (IntermediateField.AdjoinSimple.gen M (x : ℂ)) = y :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen M hint ⟨y, hy⟩
  let M' : IntermediateField ℚ ℂ := K.restrictScalars ℚ
  have hMM' : M ≤ M' := fun m hm => (IntermediateField.mem_restrictScalars ℚ).mpr (K.algebraMap_mem ⟨m, hm⟩)
  have hM'1 : M' ≤ M₁ := by
    intro z hz
    have hz' : z ∈ K := (IntermediateField.mem_restrictScalars ℚ).mp hz
    have hle : K ≤ IntermediateField.extendScalars h :=
      IntermediateField.adjoin_simple_le_iff.mpr ((IntermediateField.mem_extendScalars h).mpr x.2)
    exact (IntermediateField.mem_extendScalars h).mp (hle hz')
  have halg' : ∀ z ∈ M₁, IsAlgebraic M' z := by
    intro z hz
    letI : Algebra M M' := (IntermediateField.inclusion hMM').toRingHom.toAlgebra
    haveI : IsScalarTower M M' ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    exact (halg z hz).tower_top M'
  let f : M' →+* ℂ := τ.toRingHom
  let ρ : M' →ₐ[ℚ] ℂ := { toRingHom := f, commutes' := f.map_rat_algebraMap }
  obtain ⟨ρ₁, hρ₁⟩ := extRho M' M₁ hM'1 halg' ρ
  have hfix : ∀ m : M, ρ₁ (IntermediateField.inclusion h m) = (m : ℂ) := by
    intro m
    have e : IntermediateField.inclusion h m =
        IntermediateField.inclusion hM'1 (IntermediateField.inclusion hMM' m) := rfl
    rw [e, hρ₁]
    exact τ.commutes m
  have memx : (x : ℂ) ∈ M' :=
    (IntermediateField.mem_restrictScalars ℚ).mpr (IntermediateField.mem_adjoin_simple_self M (x : ℂ))
  apply hyx
  calc y = τ (IntermediateField.AdjoinSimple.gen M (x : ℂ)) := hτ.symm
    _ = ρ ⟨(x : ℂ), memx⟩ := rfl
    _ = ρ₁ (IntermediateField.inclusion hM'1 ⟨(x : ℂ), memx⟩) := (hρ₁ _).symm
    _ = ρ₁ x := rfl
    _ = x := hx ρ₁ hfix

end PI.GalTorsConj.W

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.MulMain
section
noncomputable section

namespace PI.GalTorsConj.W

open Formalism.L2.Th1.F

def Cj1 (M₁ : IntermediateField ℚ ℂ) (ρ₁ : M₁ →ₐ[ℚ] ℂ) (x x' : ℂ) : Prop :=
  ∃ hx : x ∈ M₁, ρ₁ ⟨x, hx⟩ = x'

section cj1

variable {M₁ : IntermediateField ℚ ℂ} {ρ₁ : M₁ →ₐ[ℚ] ℂ}

theorem conj_add_alt {x x' y y' : ℂ} (h : Cj1 M₁ ρ₁ x x') (k : Cj1 M₁ ρ₁ y y') :
    Cj1 M₁ ρ₁ (x + y) (x' + y') := by
  obtain ⟨hx, rfl⟩ := h
  obtain ⟨hy, rfl⟩ := k
  refine ⟨M₁.add_mem hx hy, ?_⟩
  rw [← map_add]
  rfl

theorem conj_sub_alt {x x' y y' : ℂ} (h : Cj1 M₁ ρ₁ x x') (k : Cj1 M₁ ρ₁ y y') :
    Cj1 M₁ ρ₁ (x - y) (x' - y') := by
  obtain ⟨hx, rfl⟩ := h
  obtain ⟨hy, rfl⟩ := k
  refine ⟨M₁.sub_mem hx hy, ?_⟩
  rw [← map_sub]
  rfl

theorem conj_mul_alt {x x' y y' : ℂ} (h : Cj1 M₁ ρ₁ x x') (k : Cj1 M₁ ρ₁ y y') :
    Cj1 M₁ ρ₁ (x * y) (x' * y') := by
  obtain ⟨hx, rfl⟩ := h
  obtain ⟨hy, rfl⟩ := k
  refine ⟨M₁.mul_mem hx hy, ?_⟩
  rw [← map_mul]
  rfl

theorem conj_pow_alt {x x' : ℂ} (h : Cj1 M₁ ρ₁ x x') (n : ℕ) : Cj1 M₁ ρ₁ (x ^ n) (x' ^ n) := by
  obtain ⟨hx, rfl⟩ := h
  refine ⟨pow_mem hx n, ?_⟩
  rw [← map_pow]
  rfl

theorem conj_natCast_alt (n : ℕ) : Cj1 M₁ ρ₁ (n : ℂ) (n : ℂ) :=
  ⟨IntermediateField.natCast_mem M₁ n, by
    rw [show (⟨(n : ℂ), IntermediateField.natCast_mem M₁ n⟩ : M₁) = (n : M₁) from
      Subtype.ext (by simp), map_natCast]⟩

theorem conj_sum_alt {ι : Type*} (s : Finset ι) (f f' : ι → ℂ) (h : ∀ i ∈ s, Cj1 M₁ ρ₁ (f i) (f' i)) :
    Cj1 M₁ ρ₁ (∑ i ∈ s, f i) (∑ i ∈ s, f' i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨M₁.zero_mem, map_zero ρ₁⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact conj_add_alt (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem conj_unique_alt {x a b : ℂ} (h : Cj1 M₁ ρ₁ x a) (k : Cj1 M₁ ρ₁ x b) : a = b := by
  obtain ⟨hx, rfl⟩ := h
  obtain ⟨hx', rfl⟩ := k
  rfl

theorem conj_eq_alt {x y a b : ℂ} (h : Cj1 M₁ ρ₁ x a) (k : Cj1 M₁ ρ₁ y b) (e : x = y) : a = b := by
  subst e
  exact conj_unique_alt h k

theorem conj_weierstrassP {L L' : PeriodPair} {t t' : ℂ} (h : St L L' M₁ ρ₁ t t') (ht : t ∉ L.lattice) :
    Cj1 M₁ ρ₁ (L.weierstrassP t) (L'.weierstrassP t') ∧
      Cj1 M₁ ρ₁ (L.derivWeierstrassP t) (L'.derivWeierstrassP t') := by
  rcases h with ⟨a, -⟩ | ⟨-, -, hx, hy, e1, e2⟩
  · exact absurd a ht
  · exact ⟨⟨hx, e1.symm⟩, ⟨hy, e2.symm⟩⟩

end cj1

theorem tors_of_ker {L : PeriodPair} {c P : ℂ} (hc0 : c ≠ 0) (hc : MulStable L c)
    (hP : c * P ∈ L.lattice) : ∃ m : ℕ, 0 < m ∧ (m : ℂ) * P ∈ L.lattice := by
  obtain ⟨t, n, ht, hn, -⟩ := mulStableIntegral L c hc
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have h1 : (n : ℂ) = (Complex.normSq c : ℂ) := by rw [← hn, Complex.mul_conj]
    have h2 : (n : ℝ) = Complex.normSq c := by exact_mod_cast h1
    rw [h2]
    exact Complex.normSq_pos.mpr hc0
  have hn0' : 0 < n := by exact_mod_cast hn0
  refine ⟨n.toNat, by omega, ?_⟩
  have e : ((n.toNat : ℕ) : ℂ) * P = (t : ℤ) • (c * P) - c * (c * P) := by
    have : ((n.toNat : ℕ) : ℂ) = (n : ℂ) := by
      have : ((n.toNat : ℤ)) = n := Int.toNat_of_nonneg hn0'.le
      exact_mod_cast this
    rw [this, ← hn, zsmul_eq_mul]
    have hconj : (starRingEnd ℂ) c = (t : ℂ) - c := by rw [← ht]; ring
    rw [hconj]
    ring
  rw [e]
  exact L.lattice.sub_mem (L.lattice.smul_mem _ hP) (hc _ hP)

theorem mul_notMem {L : PeriodPair} {c z : ℂ} {S : Finset ℂ} (hS : IsKerReps L c S)
    (hz : z ∉ L.lattice) (hzP : ∀ P ∈ S, z + P ∉ L.lattice) :
    c * z ∉ L.lattice := by
  intro hcz
  obtain ⟨Q, hQ, hzQ⟩ := hS.2.2 z hcz hz
  have h1 : c * (-Q) ∈ L.lattice := by
    rw [mul_neg]; exact L.lattice.neg_mem (hS.1 Q hQ).1
  have h2 : -Q ∉ L.lattice := fun h => (hS.1 Q hQ).2 (by simpa using L.lattice.neg_mem h)
  obtain ⟨P, hP, hQP⟩ := hS.2.2 (-Q) h1 h2
  apply hzP P hP
  have := L.lattice.sub_mem hzQ hQP
  rwa [show z - Q - (-Q - P) = z + P by ring] at this

theorem isOpen_veluU (L : PeriodPair) (S : Finset ℂ) : IsOpen (veluU L S) := by
  have e : veluU L S = {z | z ∉ L.lattice} ∩ ⋂ P ∈ S, {z | z + P ∉ L.lattice} := by
    ext z; simp [veluU]
  rw [e]
  refine IsOpen.inter L.isClosed_lattice.isOpen_compl (isOpen_biInter_finset fun P _ => ?_)
  exact L.isClosed_lattice.isOpen_compl.preimage (continuous_id.add continuous_const)

theorem continuousOn_veluF (L : PeriodPair) (S : Finset ℂ) :
    ContinuousOn (veluF L S) (veluU L S) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have h0 : ContinuousAt L.weierstrassP z := (L.analyticOnNhd_weierstrassP z hz.1).continuousAt
  have hs : ContinuousAt (fun z => ∑ P ∈ S, (L.weierstrassP (z + P) - L.weierstrassP P)) z := by
    have : ∀ P ∈ S, ContinuousAt (fun z => L.weierstrassP (z + P) - L.weierstrassP P) z := by
      intro P hP
      have h1 : ContinuousAt L.weierstrassP (z + P) :=
        (L.analyticOnNhd_weierstrassP _ (hz.2 P hP)).continuousAt
      have h2 : ContinuousAt (fun z => L.weierstrassP (z + P)) z :=
        ContinuousAt.comp (g := L.weierstrassP) (f := fun x => x + P) (x := z) h1
          (continuous_add_const P).continuousAt
      exact h2.sub continuousAt_const
    exact tendsto_finsetSum S this
  exact h0.add hs

theorem continuousOn_veluD (L : PeriodPair) (S : Finset ℂ) :
    ContinuousOn (veluD L S) (veluU L S) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have h0 : ContinuousAt L.derivWeierstrassP z :=
    (L.analyticOnNhd_derivWeierstrassP z hz.1).continuousAt
  have hs : ContinuousAt (fun z => ∑ P ∈ S, L.derivWeierstrassP (z + P)) z := by
    have : ∀ P ∈ S, ContinuousAt (fun z => L.derivWeierstrassP (z + P)) z := by
      intro P hP
      have h1 : ContinuousAt L.derivWeierstrassP (z + P) :=
        (L.analyticOnNhd_derivWeierstrassP _ (hz.2 P hP)).continuousAt
      exact ContinuousAt.comp (g := L.derivWeierstrassP) (f := fun x => x + P) (x := z) h1
        (continuous_add_const P).continuousAt
    exact tendsto_finsetSum S this
  exact h0.add hs

end PI.GalTorsConj.W

end
end

