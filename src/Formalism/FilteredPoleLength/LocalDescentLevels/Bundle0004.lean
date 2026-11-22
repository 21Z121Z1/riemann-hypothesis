import Formalism.FilteredPoleLength.ReducedBasisBounds.Bundle0002
import Formalism.LogFactorialIndices.LogProductFormula
import Lemmata.MiscLemmasO.Imports

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.ExistsSmulMemOfMemSpan
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

theorem exists_smul_mem_of_mem_span_alt (O K V : Type) [CommRing O] [IsDomain O]
    [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (M : Submodule O V) (v : V) (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ c : O, c ≠ 0 ∧ c • v ∈ M := by
  first | exact Bl.SecondBlockLemmaP.goal1 .. | (apply Bl.SecondBlockLemmaP.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaP.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaP.goal1 <;> assumption) | (intros; apply @Bl.SecondBlockLemmaP.goal1 <;> assumption) | (apply @Bl.SecondBlockLemmaP.goal1 <;> first | assumption | infer_instance) | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M v hv | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M v | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V ‹_› | exact @Bl.SecondBlockLemmaP.goal1 O K V | exact @Bl.SecondBlockLemmaP.goal1 O K | exact @Bl.SecondBlockLemmaP.goal1 O

theorem exists_adapted_basis_alt (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [FiniteDimensional K V]
    (M : Submodule O V) (V' : Submodule K V) (hM : Formalism.LatticeIndexTer.IsLat O K V M) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (s : Set (Fin (finrank K V))),
      M ≤ Submodule.span O (Set.range b) ∧ (∀ i ∈ s, b i ∈ M ∧ b i ∈ V') ∧
        V' ≤ Submodule.span K (b '' s) := by
  obtain ⟨b0, hb0⟩ := Formalism.LatticeIndexTer.latBasis O K V M hM
  have hli0 : LinearIndependent O b0 :=
    (LinearIndependent.iff_fractionRing O K).mpr b0.linearIndependent
  let bO : Basis (Fin (finrank K V)) O M :=
    (Basis.span hli0).map (LinearEquiv.ofEq _ _ hb0.symm)
  obtain ⟨n, bM, bN, f, a, snf⟩ :=
    Submodule.smithNormalForm bO ((V'.restrictScalars O).comap M.subtype)
  have hliO : LinearIndependent O (fun i => (bM i : V)) :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hliK : LinearIndependent K (fun i => (bM i : V)) :=
    (LinearIndependent.iff_fractionRing O K).mp hliO
  have hspanO : M ≤ Submodule.span O (Set.range (fun i => (bM i : V))) := by
    intro m hm
    have h1 : (⟨m, hm⟩ : M) ∈ Submodule.span O (Set.range bM) := by
      rw [bM.span_eq]; trivial
    have h2 := Submodule.mem_map_of_mem (f := M.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  have hspanK : ⊤ ≤ Submodule.span K (Set.range (fun i => (bM i : V))) := by
    rw [← hM.2]
    apply Submodule.span_le.mpr
    intro m hm
    exact Submodule.span_le_restrictScalars O K _ (hspanO hm)
  let b : Basis (Fin (finrank K V)) K V := Basis.mk hliK hspanK
  have hb : ∀ i, b i = (bM i : V) := fun i => by simp [b]
  have hrange : Set.range b = Set.range (fun i => (bM i : V)) := by
    ext x; simp [hb]
  refine ⟨b, Set.range f, ?_, ?_, ?_⟩
  · rw [hrange]; exact hspanO
  · rintro _ ⟨k, rfl⟩
    rw [hb]
    refine ⟨(bM (f k)).2, ?_⟩
    have hmem : ((bN k : M) : V) ∈ V' := (bN k).2
    rw [snf k] at hmem
    have ha : a k ≠ 0 := by
      intro h0
      have : (bN k : M) = 0 := by rw [snf k, h0, zero_smul]
      exact bN.ne_zero k (Subtype.ext this)
    have haK : algebraMap O K (a k) ≠ 0 := by
      simpa using (IsFractionRing.injective O K).ne ha
    have h3 : algebraMap O K (a k) • ((bM (f k) : M) : V) ∈ V' := by
      rw [algebraMap_smul]; simpa using hmem
    exact (V'.smul_mem_iff haK).mp h3
  · intro v hv
    have hv' : v ∈ Submodule.span K (M : Set V) := by rw [hM.2]; trivial
    obtain ⟨c, hc, hcv⟩ := exists_smul_mem_of_mem_span_alt O K V M v hv'
    have hcK : algebraMap O K c ≠ 0 := by
      simpa using (IsFractionRing.injective O K).ne hc
    have hcV : c • v ∈ V' := by
      rw [← algebraMap_smul K c]; exact V'.smul_mem _ hv
    let w : ((V'.restrictScalars O).comap M.subtype : Submodule O M) := ⟨⟨c • v, hcv⟩, hcV⟩
    have hw : w ∈ Submodule.span O (Set.range bN) := by rw [bN.span_eq]; trivial
    have key : ∀ u ∈ Submodule.span O (Set.range bN),
        ((u : M) : V) ∈ Submodule.span K (b '' Set.range f) := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        rw [snf k]
        have : ((a k • bM (f k) : M) : V) = algebraMap O K (a k) • b (f k) := by
          rw [hb, algebraMap_smul]; rfl
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f k, ⟨k, rfl⟩, rfl⟩)
      | zero => simp
      | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        have : (((r • x : _) : M) : V) = algebraMap O K r • ((x : M) : V) := by
          rw [algebraMap_smul]; rfl
        rw [this]
        exact Submodule.smul_mem _ _ hx
    have h4 : algebraMap O K c • v ∈ Submodule.span K (b '' Set.range f) := by
      rw [algebraMap_smul]; exact key w hw
    exact (Submodule.smul_mem_iff _ hcK).mp h4

theorem inter_baseChange_lattice : SpanImageInf := by
  intro O O' K K' V V₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj M V' hM
  obtain ⟨b, s, hMb, hs, hV'⟩ := exists_adapted_basis_alt O K V M V' hM
  let b' : Basis (Fin (finrank K V)) K' V₁ := hj.basis b
  have hb' : ∀ i, b' i = j (b i) := fun i => hj.basis_apply b i
  have hjO : ∀ (o : O) (v : V), j (o • v) = algebraMap O O' o • j v := by
    intro o v
    rw [← algebraMap_smul K o v, map_smul, ← algebraMap_smul K' (algebraMap O K o) (j v),
      ← algebraMap_smul K' (algebraMap O O' o) (j v), ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  have hjK : ∀ (k : K) (v : V), j (k • v) = algebraMap K K' k • j v := by
    intro k v
    rw [map_smul, algebraMap_smul]
  have hO : ∀ y ∈ Submodule.span O (Set.range b), j y ∈ Submodule.span O' (Set.range b') := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, hb' i⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [hjO]; exact Submodule.smul_mem _ _ hy
  have hK : ∀ y ∈ Submodule.span K (b '' s), j y ∈ Submodule.span K' (b' '' s) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, hi, hb' i⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [hjK]; exact Submodule.smul_mem _ _ hy
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    have h1 : x ∈ Submodule.span O' (Set.range b') := by
      refine (Submodule.span_le.mpr ?_) hx1
      rintro _ ⟨m, hm, rfl⟩
      exact hO m (hMb hm)
    have h2 : x ∈ Submodule.span K' (b' '' s) := by
      refine (Submodule.span_le.mpr ?_) hx2
      rintro _ ⟨m, hm, rfl⟩
      exact hK m (hV' hm)
    rw [b'.mem_span_iff_repr_mem O'] at h1
    rw [b'.mem_span_image] at h2
    rw [← b'.sum_repr x]
    refine Submodule.sum_mem _ ?_
    intro i _
    by_cases hi : i ∈ s
    · obtain ⟨c, hc⟩ := h1 i
      rw [← hc, algebraMap_smul, hb']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b i, hs i hi, rfl⟩)
    · have : b'.repr x i = 0 := by
        by_contra h0
        exact hi (h2 (by simpa using h0))
      rw [this, zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨m, ⟨hm1, hm2⟩, rfl⟩
    exact ⟨Submodule.subset_span ⟨m, hm1, rfl⟩, Submodule.subset_span ⟨m, hm2, rfl⟩⟩

end Formalism.LatticeBaseChangeAlt
end
end

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.LatticeDescent
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

namespace LatticeDescentAlt

variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

theorem span_inf_eq (M : Submodule O V) (hM : Formalism.LatticeIndexTer.IsLat O K V M) (V' : Submodule K V) :
    Submodule.span K ((M ⊓ V'.restrictScalars O : Submodule O V) : Set V) = V' := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact hx.2
  · intro v hv
    obtain ⟨d, hd, hdv⟩ := Formalism.LatticeIndexTer.LatticeIndexLength.exists_smul_mem_of_span (K := K) M hM.2 v
    have hd' : (algebraMap O K d) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hd
    have hmem : d • v ∈ (M ⊓ V'.restrictScalars O : Submodule O V) := by
      refine ⟨hdv, ?_⟩
      show d • v ∈ V'
      rw [← algebraMap_smul K d v]
      exact V'.smul_mem _ hv
    have hsp := Submodule.subset_span (R := K) hmem
    have : v = (algebraMap O K d)⁻¹ • (d • v) := by
      rw [← algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hsp

theorem fg_inf (M : Submodule O V) (hM : Formalism.LatticeIndexTer.IsLat O K V M) (N : Submodule O V) :
    (M ⊓ N).FG := by
  have : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hM.1
  have h := IsNoetherian.noetherian (N.comap M.subtype)
  have := h.map M.subtype
  rwa [Submodule.map_comap_subtype] at this

end LatticeDescentAlt

theorem localStepDescent_of (h2 : FinrankSpanImage) (h3 : SpanImageInf) (h4 : RelIndexSpanImage) :
    LocalStepDescent := by
  intro O O' K K' V V₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj ϖ hϖ hϖ' M Θ V'
    hM hΘ d Y Z e h
  rw [h3 O O' K K' V V₁ j hj M V' hM, h3 O O' K K' V V₁ j hj Θ V' hΘ,
    h2 O O' K K' V V₁ j hj V',
    h4 O O' K K' V V₁ j hj ϖ hϖ hϖ' _ _ (LatticeDescentAlt.fg_inf M hM _) (LatticeDescentAlt.fg_inf Θ hΘ _)
      (by rw [LatticeDescentAlt.span_inf_eq M hM V', LatticeDescentAlt.span_inf_eq Θ hΘ V'])] at h
  exact h

end Formalism.LatticeBaseChangeAlt
end
end

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.ReductionQuotient
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

namespace BasisReduction

open Formalism.LatticeIndexTer.subgroupData

variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]

abbrev q (A B : Submodule O X) : ℕ∞ := Module.length O (↥A ⧸ B.comap A.subtype)

theorem q_congr (A : Submodule O X) {B B' : Submodule O X} (h : A ⊓ B = A ⊓ B') :
    q A B = q A B' := by
  have e : B.comap A.subtype = B'.comap A.subtype := by
    ext x
    simp only [Submodule.mem_comap, Submodule.coe_subtype]
    constructor
    · intro hx
      have : (x : X) ∈ A ⊓ B' := h ▸ Submodule.mem_inf.mpr ⟨x.2, hx⟩
      exact this.2
    · intro hx
      have : (x : X) ∈ A ⊓ B := h.symm ▸ Submodule.mem_inf.mpr ⟨x.2, hx⟩
      exact this.2
  unfold q
  rw [e]

theorem q_chain {A B C : Submodule O X} (hAB : A ≤ B) (hBC : B ≤ C) :
    q C A = q C B + q B A := by
  rw [add_comm]
  exact length_chain' hAB hBC

theorem q_sup (A B : Submodule O X) : q (A ⊔ B) B = q A B := by
  have h := (LinearMap.quotientInfEquivSupQuotient A B).length_eq
  have h2 : q A (A ⊓ B) = q A B := q_congr A (by simp)
  exact h.symm.trans h2

theorem q_zero {A B : Submodule O X} (h : A ≤ B) : q A B = 0 := qlen_eq_zero h

theorem len_comap_le {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (f : M →ₗ[O] M') (p : Submodule O M') :
    Module.length O (M ⧸ p.comap f) ≤ Module.length O (M' ⧸ p) := by
  apply Module.length_le_of_injective (Submodule.mapQ (p.comap f) p f le_rfl)
  intro x y hxy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [Submodule.mapQ_apply] at hxy
  rw [Submodule.Quotient.eq] at hxy ⊢
  simpa using hxy

theorem q_top (N : Submodule O X) : q ⊤ N = Module.length O (X ⧸ N) := by
  apply le_antisymm
  · exact len_comap_le _ _
  · have h := len_comap_le (Submodule.topEquiv (R := O) (M := X)).symm.toLinearMap
      (N.comap (⊤ : Submodule O X).subtype)
    refine le_trans (le_of_eq ?_) h
    congr 2

end BasisReduction

open BasisReduction

theorem filteredLength : FilteredLength := by
  intro O A _ _ _ n F h0 hn hF N
  have key : ∀ k, Module.length O (A ⧸ N) =
      ∑ j ∈ Finset.range k, q (F j) (F (j + 1) ⊔ (N ⊓ F j)) + q (F k) N := by
    intro k
    induction k with
    | zero => simp [h0, q_top]
    | succ k ih =>
      rw [ih, Finset.sum_range_succ, add_assoc]
      congr 1
      have hB : F (k + 1) ⊔ (N ⊓ F k) ≤ F k := sup_le (hF k) inf_le_right
      calc q (F k) N = q (F k) (N ⊓ F k) := q_congr _ (by rw [inf_comm N, ← inf_assoc, inf_idem])
        _ = q (F k) (F (k + 1) ⊔ (N ⊓ F k)) + q (F (k + 1) ⊔ (N ⊓ F k)) (N ⊓ F k) :=
            q_chain le_sup_right hB
        _ = q (F k) (F (k + 1) ⊔ (N ⊓ F k)) + q (F (k + 1)) (N ⊓ F k) := by rw [q_sup]
        _ = q (F k) (F (k + 1) ⊔ (N ⊓ F k)) + q (F (k + 1)) N := by
            rw [q_congr (F (k + 1)) (B := N ⊓ F k) (B' := N)]
            rw [inf_comm N, ← inf_assoc, inf_eq_left.mpr (hF k)]
  rw [key n, hn, q_zero bot_le, add_zero]

end Formalism.LatticeBaseChangeAlt
end
end

