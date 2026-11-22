import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0241
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0236
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0242
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0247
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0244

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSSRepTraceNondegenerateStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_of_isSSRep : ∀ (Γ K : Type) [Group Γ] [Field K] [CharZero K] (a : ℕ) (ρ : Γ →* GL (Fin a) K), IsSSRep ρ → (∀ x ∈ Submodule.span K (Set.range fun g => ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)), (∀ g, (x * ((ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).trace = 0) → x = 0) := by
  first | exact @GlobalTheory.isSSRep_trace_nondegenerate | exact GlobalTheory.isSSRep_trace_nondegenerate | (intros; apply GlobalTheory.isSSRep_trace_nondegenerate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KTypesUnitaryLowestWeightInCone
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.LowestCone

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

lemma mem_wt {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} :
    v ∈ wtSub act μ ↔ ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  simp [wtSub, Submodule.mem_iInf, sub_eq_zero]

lemma mem_hw {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} :
    v ∈ hwSub act μ ↔ v ∈ wtSub act μ ∧ ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp [hwSub, Submodule.mem_iInf]

lemma Eab_mul (a b c d : Ix p q) :
    (Eab a b : Mat p q) * Eab c d = (if b = c then (1 : ℂ) else 0) • Eab a d := by
  split_ifs with h
  · subst h; simp [Eab]
  · simp [Eab, Matrix.single_mul_single_of_ne, h]

lemma lie_Eab {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (a b c d : Ix p q) (y : V) :
    act (Eab a b) (act (Eab c d) y) = act (Eab c d) (act (Eab a b) y) +
      ((if b = c then (1 : ℂ) else 0) • act (Eab a d) y -
        (if d = a then (1 : ℂ) else 0) • act (Eab c b) y) := by
  have := congrArg (fun f => f y) (hL (Eab a b) (Eab c d))
  simp only [Eab_mul, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.mul_apply] at this
  rw [this]; abel

lemma wt_shift {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (a b : Ix p q)
    {ν : Ix p q → ℚ} {y : V} (hy : y ∈ wtSub act ν) :
    act (Eab a b) y ∈ wtSub act
      (fun c => ν c + ((if c = a then 1 else 0) - (if c = b then 1 else 0))) := by
  rw [mem_wt] at hy ⊢
  intro c
  rw [lie_Eab hL, hy, map_smul]
  by_cases h1 : c = a <;> by_cases h2 : c = b
  · subst h1; subst h2; simp
  · subst h1; simp [h2, Ne.symm h2, add_smul]
  · subst h2; simp [h1, sub_eq_add_neg, add_smul]
  · simp [h1, h2, Ne.symm h2]

def InCone (ν μ : Ix p q → ℚ) : Prop :=
  ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → ∃ i j, a = Sum.inl i ∧ b = Sum.inr j) ∧
    μ = fun c => ν c + ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0))

lemma inCone_self (μ : Ix p q → ℚ) : InCone μ μ :=
  ⟨fun _ _ => 0, by simp, by simp⟩

lemma inCone_step {ν μ : Ix p q → ℚ} (h : InCone ν μ) (i : Fin p) (j : Fin q) :
    InCone (fun c => ν c + ((if c = Sum.inr j then 1 else 0) - (if c = Sum.inl i then 1 else 0))) μ := by
  obtain ⟨m, hm, rfl⟩ := h
  refine ⟨fun a b => m a b + if a = Sum.inl i then (if b = Sum.inr j then 1 else 0) else 0, ?_, ?_⟩
  · intro a b hab
    by_cases h0 : m a b = 0
    · by_cases h1 : a = Sum.inl i
      · by_cases h2 : b = Sum.inr j
        · exact ⟨i, j, h1, h2⟩
        · simp [h0, h2] at hab
      · simp [h0, h1] at hab
    · exact hm a b h0
  · funext c
    have key : ∑ a : Ix p q, ∑ b : Ix p q,
        (((if a = Sum.inl i then (if b = Sum.inr j then 1 else 0) else 0 : ℕ)) : ℚ) *
          ((if c = a then 1 else 0) - (if c = b then 1 else 0)) =
        (if c = Sum.inl i then 1 else 0) - (if c = Sum.inr j then 1 else 0) := by
      rw [Finset.sum_eq_single (Sum.inl i), Finset.sum_eq_single (Sum.inr j)]
      · simp
      · intro b _ hb; simp [hb]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib, key]
    ring

lemma act_mem {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (N : Submodule ℂ V) (y : V)
    (h : ∀ a b, act (Eab a b) y ∈ N) (Z : Mat p q) : act Z y ∈ N := by
  rw [Matrix.matrix_eq_sum_single Z]
  simp only [map_sum, LinearMap.sum_apply]
  refine N.sum_mem fun a _ => N.sum_mem fun b _ => ?_
  have : (Matrix.single a b (Z a b) : Mat p q) = Z a b • Eab a b := by
    rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, LinearMap.smul_apply]
  exact N.smul_mem _ (h a b)

lemma exists_down {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) {μ : Ix p q → ℚ} {v : V}
    (hv : v ∈ hwSub act μ) : ∃ D : Submodule ℂ V, v ∈ D ∧
      (∀ i j, ∀ x ∈ D, act (Eab (Sum.inr j) (Sum.inl i)) x ∈ D) ∧
      (∀ a b, posC a b → ∀ x ∈ D, act (Eab a b) x ∈ D) ∧
      D ≤ ⨆ ν : {ν // InCone ν μ}, wtSub act ν.1 := by
  rw [mem_hw] at hv
  set S : Set (Submodule ℂ V) :=
    {N | v ∈ N ∧ ∀ i j, ∀ x ∈ N, act (Eab (Sum.inr j) (Sum.inl i)) x ∈ N} with hS
  have hG : sInf S ∈ S := by
    refine ⟨Submodule.mem_sInf.2 fun M hM => hM.1, fun a b y hy => ?_⟩
    exact Submodule.mem_sInf.2 fun M hM => hM.2 a b y (Submodule.mem_sInf.1 hy M hM)
  refine ⟨sInf S, hG.1, hG.2, fun a b hab x hx => ?_, sInf_le ⟨?_, fun i j x hx => ?_⟩⟩
  · have hG' : (sInf S ⊓ (sInf S).comap (act (Eab a b))) ∈ S := by
      refine ⟨⟨hG.1, ?_⟩, fun i j y hy => ⟨hG.2 i j y hy.1, ?_⟩⟩
      · show act (Eab a b) v ∈ sInf S
        rw [hv.2 a b hab]; exact Submodule.zero_mem _
      · show act (Eab a b) (act _ y) ∈ sInf S
        rw [lie_Eab hL]
        refine Submodule.add_mem _ (hG.2 i j _ hy.2) ?_
        rcases a with a | a <;> rcases b with b | b
        · refine Submodule.sub_mem _ (by simp) (Submodule.smul_mem _ _ (hG.2 _ _ _ hy.1))
        · exact absurd hab (by simp [posC])
        · exact absurd hab (by simp [posC])
        · refine Submodule.sub_mem _ (Submodule.smul_mem _ _ (hG.2 _ _ _ hy.1)) (by simp)
    exact (sInf_le hG' hx).2
  · exact Submodule.mem_iSup_of_mem (⟨μ, inCone_self μ⟩ : {ν // InCone ν μ}) hv.1
  · refine Submodule.iSup_induction _ (motive := fun x => act (Eab (Sum.inr j) (Sum.inl i)) x ∈
      ⨆ ν : {ν // InCone ν μ}, wtSub act ν.1) hx ?_ (by simp) ?_
    · intro ν y hy
      exact Submodule.mem_iSup_of_mem (⟨_, inCone_step ν.2 i j⟩ : {ν // InCone ν μ})
        (wt_shift hL _ _ hy)
    · intro y z hy hz
      rw [map_add]; exact Submodule.add_mem _ hy hz

lemma wt_orth {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (E : V →ₗ[ℂ] H)
    (hadj : ∀ Z x y, inner ℂ (E (act Z x)) (E y) = inner ℂ (E x) (E (act (adjZ Z) y)))
    {ν Λ : Ix p q → ℚ} (hne : ν ≠ Λ) {x e : V} (hx : x ∈ wtSub act ν) (he : e ∈ wtSub act Λ) :
    inner ℂ (E x) (E e) = 0 := by
  obtain ⟨c, hc⟩ := Function.ne_iff.1 hne
  have h := hadj (Eab c c) x e
  rw [GlobalTheory.FockTensor.adjZ_Eab, GlobalTheory.FockTensor.sgnIx_mul_self, one_smul, mem_wt.1 hx, mem_wt.1 he,
    map_smul, map_smul, inner_smul_left, inner_smul_right, map_ratCast, ← sub_eq_zero,
    ← sub_mul] at h
  refine (mul_eq_zero.1 h).resolve_left fun h0 => hc ?_
  exact_mod_cast sub_eq_zero.1 h0

theorem cone : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), Function.Injective E → (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∀ (Λ : Ix p q → ℚ) (e : M.V), e ∈ hwSub M.act Λ → KilledByLower M.act e → genSub M.act {e} = ⊤ → ∀ (μ : Ix p q → ℚ) (v : M.V), IsHW M.act μ v → ∃ m : Ix p q → Ix p q → ℕ, (∀ a b, m a b ≠ 0 → ∃ i j, a = Sum.inl i ∧ b = Sum.inr j) ∧ μ = fun c => Λ c + ∑ a, ∑ b, (m a b : ℚ) * ((if c = a then 1 else 0) - (if c = b then 1 else 0)) := by
  intro p q M H _ _ E hE hadj Λ e he hlow hgen μ v hv
  by_contra hcone
  change ¬ InCone Λ μ at hcone
  obtain ⟨D, hvD, hDm, hDp, hDle⟩ := exists_down M.lie hv.2
  rw [mem_hw] at he
  let C : Submodule ℂ M.V := ((D.map E)ᗮ).comap E
  have hC : ∀ x, x ∈ C ↔ ∀ d ∈ D, inner ℂ (E d) (E x) = 0 := by
    intro x
    simp only [C, Submodule.mem_comap, Submodule.mem_orthogonal]
    constructor
    · intro h d hd; exact h _ ⟨d, hd, rfl⟩
    · rintro h _ ⟨d, hd, rfl⟩; exact h d hd
  have hstab : ∀ a b, (∀ d ∈ D, M.act (Eab a b) d ∈ D) → ∀ x ∈ C, M.act (Eab b a) x ∈ C := by
    intro a b h x hx
    rw [hC] at hx ⊢
    intro d hd
    have := hadj (adjZ (Eab b a)) d x
    rw [GlobalTheory.FockTensor.adjZ_adjZ] at this
    rw [← this, GlobalTheory.FockTensor.adjZ_Eab, map_smul, LinearMap.smul_apply]
    exact hx _ (D.smul_mem _ (h d hd))
  have heC : e ∈ C := by
    rw [hC]
    intro d hd
    refine Submodule.iSup_induction _ (motive := fun x => inner ℂ (E x) (E e) = 0) (hDle hd) ?_
      (by simp) ?_
    · intro ν y hy
      exact wt_orth E hadj (fun h : ν.1 = Λ => hcone (h ▸ ν.2)) hy he.1
    · intro y z hy hz
      rw [map_add, inner_add_left, hy, hz, add_zero]
  let r : Ix p q → ℕ := Sum.elim (fun i => q + i.1) (fun j => j.1)
  have hr : Function.Injective r := by
    rintro (a | a) (b | b) h <;> simp only [r, Sum.elim_inl, Sum.elim_inr] at h
    · congr 1; ext; omega
    · have := b.2; omega
    · have := a.2; omega
    · congr 1; ext; omega
  have hcase : ∀ a b, r a < r b → posC a b ∨ ∃ i j, a = Sum.inr j ∧ b = Sum.inl i := by
    rintro (a | a) (b | b) h <;> simp only [r, Sum.elim_inl, Sum.elim_inr] at h
    · left; show a < b; rw [Fin.lt_def]; omega
    · have := b.2; omega
    · exact Or.inr ⟨_, _, rfl, rfl⟩
    · left; exact h
  obtain ⟨U, heU, hU, hUmin, -⟩ := GlobalTheory.ExtremalGen.exists_generated p q M.V M.act M.lie (fun _ _ => True)
    ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩ r hr Λ e he.1 (by
      intro a b _ h
      rcases hcase a b h with h | ⟨i, j, rfl, rfl⟩
      · exact he.2 a b h
      · exact hlow i j)
  have hUC : U ≤ C := hUmin C heC (by
    intro a b _ h
    refine hstab a b ?_
    rcases hcase a b h with h | ⟨i, j, rfl, rfl⟩
    · exact hDp a b h
    · exact hDm i j)
  have hgU : genSub M.act {e} ≤ U :=
    sInf_le ⟨by simpa using heU, fun Z y hy => act_mem U y (fun a b => hU a b trivial y hy) Z⟩
  have hvC : v ∈ C := hUC (hgU (hgen ▸ Submodule.mem_top))
  have h0 := (hC v).1 hvC v hvD
  rw [inner_self_eq_zero] at h0
  exact hv.1 (hE (by rw [h0, map_zero]))

end GlobalTheory.LowestCone
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeCovolumePosAndSelfDualStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCovolume_pos_and_selfDual : ∀ (L : PeriodPair) (Λ : AddSubgroup ℂ), (∀ z : ℂ, z ∈ Λ ↔ z ∈ L.lattice) → 0 < area Λ ∧ ∀ z : ℂ, z ∈ Λ ↔ ∀ w ∈ Λ, ∃ m : ℤ, (z * (starRingEnd ℂ) w).im / area Λ = m := by
  first | exact @GlobalTheory.PlaneLattice.area_pos_and_selfDual | exact GlobalTheory.PlaneLattice.area_pos_and_selfDual | (intros; apply GlobalTheory.PlaneLattice.area_pos_and_selfDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionaryStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeInvariants_periodPair_dictionary : ∀ (L : PeriodPair) (Λ : AddSubgroup ℂ), (∀ z, z ∈ Λ ↔ z ∈ L.lattice) → g2 Λ = L.g₂ ∧ g3 Λ = L.g₃ ∧ TaylorLogMetric.discr Λ ≠ 0 ∧ area Λ = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| ∧ (∀ z, z ∉ Λ → wpF Λ z = L.weierstrassP z ∧ wpD Λ z = L.derivWeierstrassP z) ∧ (∀ (Λ' : AddSubgroup ℂ), g2 Λ' = g2 Λ → g3 Λ' = g3 Λ → Λ' = Λ) ∧ ∀ a b : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 → ∃ (L' : PeriodPair), L'.g₂ = a ∧ L'.g₃ = b := by
  first | exact @GlobalTheory.LatticeInvariants.invariants_dictionary | exact GlobalTheory.LatticeInvariants.invariants_dictionary | (intros; apply GlobalTheory.LatticeInvariants.invariants_dictionary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelNFunctionGaloisConjQExpansionStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelN_function_galois_conj_qExpansion : ∀ (g : ℂ ≃+* ℂ) (E : Subring ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (w : ℕ) (f : ℍ → ℂ), (∀ x ∈ E, g x ∈ E) → ZetaAct g N d → Lv E N w f → ∃ f' : ℍ → ℂ, Lv E N w f' ∧ ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d → QConj g N (fun τ => DD τ ^ w * f (γ • τ)) (fun τ => DD τ ^ w * f' (γ' • τ)) := by
  first | exact @GlobalTheory.FN.lv_galois_conj | exact GlobalTheory.FN.lv_galois_conj | (intros; apply GlobalTheory.FN.lv_galois_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LineDerivListCompForm
section
open Filter Topology

namespace GlobalTheory.ProdThetaConj

theorem exists_ringHom_extend (R K : Type) [Field R] [Countable R] [Field K]
    (hK : Cardinal.mk K ≤ Cardinal.mk ℂ) (i : R →+* K) (j : R →+* ℂ) :
    ∃ s : K →+* ℂ, ∀ x, s (i x) = j x := by
  letI : Algebra R K := i.toAlgebra
  letI : Algebra R ℂ := j.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R ℂ
  have hC : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have hct := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht
    Cardinal.mk_le_aleph0 hC
  have hle : Cardinal.mk s ≤ Cardinal.mk t :=
    le_trans (Cardinal.mk_set_le s) (hct ▸ hK)
  obtain ⟨e⟩ := (Cardinal.le_def _ _).1 hle
  have hw : AlgebraicIndependent R (((↑) : t → ℂ) ∘ e) := ht.1.comp e e.injective
  let S := Algebra.adjoin R (Set.range ((↑) : s → K))
  let φ : S →ₐ[R] ℂ :=
    (MvPolynomial.aeval (((↑) : t → ℂ) ∘ e)).comp hs.1.aevalEquiv.symm.toAlgHom
  have hφ : Function.Injective φ :=
    (algebraicIndependent_iff_injective_aeval.1 hw).comp hs.1.aevalEquiv.symm.injective
  let _ : Algebra S ℂ := φ.toRingHom.toAlgebra
  have : IsScalarTower R S ℂ := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have : FaithfulSMul S ℂ := (faithfulSMul_iff_algebraMap_injective S ℂ).2 hφ
  have : Algebra.IsAlgebraic S K := hs.isAlgebraic
  let ψ : K →ₐ[R] ℂ := (IsAlgClosed.lift : K →ₐ[S] ℂ).restrictScalars R
  exact ⟨ψ.toRingHom, fun x => ψ.commutes x⟩

section General

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
theorem summable_prod_half_pow : Summable fun α : σ →₀ ℕ => ∏ j, (1 / 2 : ℝ) ^ α j := by
  have h : Summable fun α : σ → ℕ => ∏ j, (1 / 2 : ℝ) ^ α j := by
    classical
    refine summable_of_sum_le (c := ∏ _j : σ, (2 : ℝ)) (fun α => by positivity) fun u => ?_
    let n : ℕ := u.sup fun α => Finset.univ.sup α
    have hsub : u ⊆ Fintype.piFinset fun _ : σ => Finset.range (n + 1) := by
      intro α hα
      rw [Fintype.mem_piFinset]
      intro j
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact (Finset.le_sup (f := α) (Finset.mem_univ j)).trans
        (Finset.le_sup (f := fun α => Finset.univ.sup α) hα)
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
    rw [← Finset.prod_univ_sum (fun _ : σ => Finset.range (n + 1)) (fun _ k => (1 / 2 : ℝ) ^ k)]
    exact Finset.prod_le_prod (fun _ _ => by positivity) fun _ _ => sum_geometric_two_le _
  exact h.comp_injective (i := fun α : σ →₀ ℕ => (α : σ → ℕ)) DFunLike.coe_injective

theorem tsum_of_entire {f : (σ → ℂ) → ℂ} (hf : Differentiable ℂ f) (c : (σ →₀ ℕ) → ℂ)
    (hc : ∀ α, (∏ j, ((α j).factorial : ℂ)) * c α = pderivIter α f 0)
    (hc' : ∀ α, c α = MvPowerSeries.coeff α (GlobalTheory.taylor f)) (z : σ → ℂ) :
    ∑' α : σ →₀ ℕ, c α * ∏ j, z j ^ α j = f z := by
  have hb : ∀ R : ℝ, 0 < R → ∃ u : (σ →₀ ℕ) → ℝ, Summable u ∧ ∀ α, ∀ w ∈ Metric.ball (0 : σ → ℂ) R,
      ‖c α * ∏ j, w j ^ α j‖ ≤ u α := by
    intro R hR
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : σ → ℂ) (2 * R)).exists_bound_of_continuousOn
      hf.continuous.continuousOn
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Metric.mem_closedBall_self (by positivity)))
    refine ⟨fun α => C * ∏ j, (1 / 2 : ℝ) ^ α j, summable_prod_half_pow.mul_left C, fun α w hw => ?_⟩
    have h1 := norm_pderivIter_le_of_differentiable (F := f) (a := 0) (r := fun _ => 2 * R) (M := C) α
      (fun _ => by positivity) (fun _ _ => by positivity) hf (fun y hy => hC y (by
        rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
        intro k
        simpa using (hy k).le))
    rw [← hc, norm_mul, norm_prod, mul_div_assoc] at h1
    simp only [Complex.norm_natCast] at h1
    have h2 := le_of_mul_le_mul_left h1 (Finset.prod_pos fun k _ => by
      exact_mod_cast Nat.factorial_pos _)
    rw [norm_mul, norm_prod]
    calc ‖c α‖ * ∏ j, ‖w j ^ α j‖ ≤ (C / ∏ k, (2 * R) ^ α k) * ∏ j, R ^ α j := by
          refine mul_le_mul h2 (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => ?_)
            (by positivity) (by positivity)
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _)
            ((norm_le_pi_norm w j).trans (mem_ball_zero_iff.1 hw).le) _
      _ = C * ∏ j, (1 / 2 : ℝ) ^ α j := by
          rw [div_mul_eq_mul_div, mul_div_assoc, ← Finset.prod_div_distrib]
          congr 1
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [← div_pow]
          congr 1
          field_simp
  have hsum : ∀ w : σ → ℂ, Summable fun α : σ →₀ ℕ => c α * ∏ j, w j ^ α j := fun w => by
    obtain ⟨u, hu, h⟩ := hb (‖w‖ + 1) (by positivity)
    exact Summable.of_norm_bounded hu fun α => h α w (by simp)
  have hd : DifferentiableOn ℂ (fun w : σ → ℂ => ∑' α : σ →₀ ℕ, c α * ∏ j, w j ^ α j) Set.univ := by
    refine SCV.differentiableOn_tsum_of_locally_normal isOpen_univ (fun α => ?_) fun x _ => ?_
    · apply Differentiable.differentiableOn
      fun_prop
    · obtain ⟨u, hu, h⟩ := hb (‖x‖ + 1) (by positivity)
      exact ⟨_, Metric.isOpen_ball.mem_nhds (by simp), u, hu, h⟩
  have han := SCV.analyticOnNhd_of_differentiableOn isOpen_univ hd 0 (Set.mem_univ _)
  have hfa := SCV.analyticOnNhd_of_differentiable hf Set.univ 0 (Set.mem_univ _)
  have heq := (taylor_eq_iff han hfa).1 (by
    ext α
    rw [← hc']
    exact ConjSeries.coeff_taylor_of_hasSum _ han (Eventually.of_forall fun w => (hsum w).hasSum) α
      (Nat.lt_succ_self _))
  exact SCV.eqOn_of_eventuallyEq isOpen_univ isPreconnected_univ hd hf.differentiableOn
    (Set.mem_univ 0) heq (Set.mem_univ z)

end General

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped BigOperators

theorem tsum_taylor_mono (D : D7) {N N' : ℕ} {F : VC D N N' → ℂ} (hF : Differentiable ℂ F)
    (z : VC D N N') : ∑' α, Formalism.MainNotions.TaylorLogMetric.taylor D F α * mono D α z = F z := by
  let L := LinearMap.toContinuousLinearMap (GaussCauchy.curry D N N')
  have hc : coordV D = fun k => L (Pi.single k 1) := by
    funext k
    exact (GaussCauchy.curry_single D N N' k).symm
  have han := SCV.analyticOnNhd_of_differentiable hF Set.univ 0 (Set.mem_univ _)
  have h := tsum_of_entire (f := fun w => F (L w)) (hF.comp L.differentiable)
    (Formalism.MainNotions.TaylorLogMetric.taylor D F) (fun α => by
      have := GaussCauchy.factorial_mul_taylor D N N' F hF α
      rwa [Finsupp.prod_fintype _ _ (by simp)] at this)
    (fun α => by rw [ConjSeries.taylor_eq_coeff, hc, ← taylor_comp_clm L han])
    (fun k => z k.1 k.2.1 k.2.2)
  refine Eq.trans ?_ h
  refine tsum_congr fun α => ?_
  rw [mono, Finsupp.prod_fintype _ _ (by simp)]

theorem exists_endo_eq_cj (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) {S : Set ℂ} (hS : S.Countable) :
    ∃ s : ℂ →+* ℂ, ∀ x ∈ S, x ∈ M → cj M ρ x = s x := by
  let R := IntermediateField.adjoin ℚ (S ∩ (M : Set ℂ))
  have hle : R ≤ M := IntermediateField.adjoin_le_iff.2 Set.inter_subset_right
  have : Countable R := by
    have h1 : (S ∩ (M : Set ℂ)).Countable := hS.mono Set.inter_subset_left
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (IntermediateField.cardinalMk_adjoin_le ℚ _).trans ?_
    simp only [sup_le_iff, le_refl, and_true]
    exact ⟨Cardinal.mk_le_aleph0, Cardinal.le_aleph0_iff_set_countable.2 h1⟩
  obtain ⟨s, hs⟩ := exists_ringHom_extend R ℂ le_rfl R.val.toRingHom
    (ρ.comp (IntermediateField.inclusion hle)).toRingHom
  refine ⟨s, fun x hx hM => ?_⟩
  have := hs ⟨x, IntermediateField.subset_adjoin ℚ _ ⟨hx, hM⟩⟩
  simp only [cj, TaylorLogMetric.liftM, dif_pos hM]
  exact this.symm

def ConjPair (D : D7) {N N' : ℕ} (s : ℂ →+* ℂ) (F F' : VC D N N' → ℂ) : Prop :=
  Differentiable ℂ F ∧ Differentiable ℂ F' ∧
    MvPowerSeries.map s (taylorDir (coordV D) F) = taylorDir (coordV D) F'

variable {D : D7} {N N' : ℕ} {s : ℂ →+* ℂ}

theorem an0 {F : VC D N N' → ℂ} (h : Differentiable ℂ F) : AnalyticAt ℂ F 0 :=
  SCV.analyticOnNhd_of_differentiable h Set.univ 0 (Set.mem_univ _)

theorem ConjPair.taylor_eq {F F' : VC D N N' → ℂ} (h : ConjPair D s F F') (α : Mono D N N') :
    s (Formalism.MainNotions.TaylorLogMetric.taylor D F α) = Formalism.MainNotions.TaylorLogMetric.taylor D F' α := by
  rw [ConjSeries.taylor_eq_coeff, ConjSeries.taylor_eq_coeff, ← h.2.2, MvPowerSeries.coeff_map]

theorem ConjPair.fnConj_eq {F F' : VC D N N' → ℂ} (h : ConjPair D s F F')
    {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}
    (hs : ∀ α, cj M ρ (Formalism.MainNotions.TaylorLogMetric.taylor D F α) = s (Formalism.MainNotions.TaylorLogMetric.taylor D F α)) :
    fnConj D M ρ F = F' := by
  funext z
  rw [← tsum_taylor_mono D h.2.1 z, fnConj]
  refine tsum_congr fun α => ?_
  rw [← h.taylor_eq, ← hs, cj]

theorem taylor_const_mul {F : VC D N N' → ℂ} (h : Differentiable ℂ F) (a : ℂ) (α : Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun z => a * F z) α = a * Formalism.MainNotions.TaylorLogMetric.taylor D F α := by
  rw [ConjSeries.taylor_eq_coeff, ConjSeries.taylor_eq_coeff]
  have := taylorDir_smul (coordV D) a (an0 h)
  rw [show (fun z => a * F z) = a • F from rfl, this, MvPowerSeries.coeff_smul]

theorem ConjPair.const_mul {F F' : VC D N N' → ℂ} (h : ConjPair D s F F') (a : ℂ) :
    ConjPair D s (fun z => a * F z) (fun z => s a * F' z) := by
  refine ⟨h.1.const_mul a, h.2.1.const_mul _, ?_⟩
  ext α
  rw [MvPowerSeries.coeff_map, ← ConjSeries.taylor_eq_coeff, ← ConjSeries.taylor_eq_coeff,
    taylor_const_mul h.1, taylor_const_mul h.2.1, map_mul, h.taylor_eq]

theorem ConjPair.sum {κ : Type*} [Fintype κ] {F F' : κ → VC D N N' → ℂ}
    (h : ∀ i, ConjPair D s (F i) (F' i)) :
    ConjPair D s (fun z => ∑ i, F i z) (fun z => ∑ i, F' i z) := by
  refine ⟨Differentiable.fun_sum fun i _ => (h i).1, Differentiable.fun_sum fun i _ => (h i).2.1, ?_⟩
  rw [taylorDir_sum _ _ fun i _ => an0 (h i).1, taylorDir_sum _ _ fun i _ => an0 (h i).2.1, map_sum]
  exact Finset.sum_congr rfl fun i _ => (h i).2.2

theorem ConjPair.prod {κ : Type*} [Fintype κ] {F F' : κ → VC D N N' → ℂ}
    (h : ∀ i, ConjPair D s (F i) (F' i)) :
    ConjPair D s (fun z => ∏ i, F i z) (fun z => ∏ i, F' i z) := by
  have hp : ∀ G : κ → VC D N N' → ℂ, (∀ i, Differentiable ℂ (G i)) →
      Differentiable ℂ fun z => ∏ i, G i z := fun G hG z =>
    (HasFDerivAt.finsetProd (u := Finset.univ) fun i _ => (hG i z).hasFDerivAt).differentiableAt
  refine ⟨hp _ fun i => (h i).1, hp _ fun i => (h i).2.1, ?_⟩
  rw [taylorDir_prod _ _ fun i _ => an0 (h i).1, taylorDir_prod _ _ fun i _ => an0 (h i).2.1, map_prod]
  exact Finset.prod_congr rfl fun i _ => (h i).2.2

theorem lineDerivList_comp_form {κ : Type*} (u : κ → VC D N N') (ℓ : VC D N N' →ₗ[ℂ] ℂ) (g : ℂ → ℂ)
    (l : List κ) : lineDerivList ℂ (l.map u) (fun z => g (ℓ z)) 0 =
      (l.map fun k => ℓ (u k)).prod * iteratedDeriv l.length g 0 := by
  rw [lineDerivList_comp_linearMap, List.map_map]
  have h1 := lineDerivList_map_smul (fun k => ℓ (u k)) (fun _ => (1 : ℂ)) l g
  have h2 := lineDerivList_replicate l.length (1 : ℂ) g 0 (0 : ℂ)
  simp only [smul_eq_mul, mul_one, List.map_const', zero_add] at h1 h2
  simp only [map_zero, Function.comp_def, h1, h2]

theorem ConjPair.comp_form {g g' : ℂ → ℂ} (hg : Differentiable ℂ g) (hg' : Differentiable ℂ g')
    (hc : ∀ n, s (coef1 g n) = coef1 g' n) (ℓ ℓ' : VC D N N' →ₗ[ℂ] ℂ)
    (hℓ : ∀ k, s (ℓ (coordV D k)) = ℓ' (coordV D k)) :
    ConjPair D s (fun z => g (ℓ z)) (fun z => g' (ℓ' z)) := by
  have h1 : Differentiable ℂ fun z => g (ℓ z) :=
    hg.comp (LinearMap.toContinuousLinearMap ℓ).differentiable
  have h2 : Differentiable ℂ fun z => g' (ℓ' z) :=
    hg'.comp (LinearMap.toContinuousLinearMap ℓ').differentiable
  refine ⟨h1, h2, ?_⟩
  ext α
  have hd : ∀ n, s (iteratedDeriv n g 0) = iteratedDeriv n g' 0 := fun n => by
    have := hc n
    rw [coef1, coef1, map_div₀, map_natCast] at this
    exact (div_left_inj' (by exact_mod_cast n.factorial_ne_zero)).1 this
  rw [MvPowerSeries.coeff_map,
    coeff_taylorDir_eq_lineDerivList _ (an0 h1) (Multiset.coe_toList _),
    coeff_taylorDir_eq_lineDerivList _ (an0 h2) (Multiset.coe_toList _),
    lineDerivList_comp_form, lineDerivList_comp_form, map_mul, map_mul, map_inv₀, map_natCast, hd,
    map_list_prod, List.map_map]
  simp only [Function.comp_def, hℓ]

end GlobalTheory.ProdThetaConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalBasisLatticeIndexCoprimeStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBasisLattice_index_coprime : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (p : ℕ), p.Prime → (La D (tor0 D cc δ) L L').FG → LocBasis D p (YYl D L L') b → Nat.Coprime (((LaB D (tor0 D cc δ) b).addSubgroupOf (La D (tor0 D cc δ) L L')).index) p := by
  first | exact @GlobalTheory.NormSum.LocIndex.index_coprime | exact GlobalTheory.NormSum.LocIndex.index_coprime | (intros; apply GlobalTheory.NormSum.LocIndex.index_coprime <;> assumption)
end

