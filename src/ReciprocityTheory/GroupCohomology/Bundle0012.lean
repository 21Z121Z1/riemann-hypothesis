import ReciprocityTheory.GroupCohomology.Bundle0004
import ReciprocityTheory.GroupCohomology.Bundle0003
import ReciprocityTheory.GroupCohomology.ConnNatHolds
import ReciprocityTheory.GroupCohomology.PairHomFCoeOfId
import ReciprocityTheory.GroupCohomology.Bundle0007
import ReciprocityTheory.GroupCohomology.InfRes
import ReciprocityTheory.GroupCohomology.Bundle0008
import ReciprocityTheory.GroupCohomology.Shapiro
import ReciprocityTheory.GroupCohomology.Bundle0005
import ReciprocityTheory.GroupCohomology.Bundle0011
import ReciprocityTheory.GroupCohomology.Bundle0009
import ReciprocityTheory.GroupCohomology.Bundle0006
import ReciprocityTheory.GroupCohomology.Bundle0001

-- bundled from ReciprocityTheory.GroupCohomology.InfIso
section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function Topology

noncomputable section

universe u

namespace InflationIsomorphism

variable {R : Type u} [CommRing R]

theorem H_comm {A B A' B' : Cx R} (i : Hom A B) (i' : Hom A' B') (α : Hom A A') (β : Hom B B')
    (h : ∀ n x, β.f n (i.f n x) = i'.f n (α.f n x)) (n : ℕ) (z : A.H n) :
    β.H n (i.H n z) = i'.H n (α.H n z) := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  simp only [InflationRestrictionInvariants.H_mk]
  congr 1
  exact Subtype.ext (h n x)

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [LocallyCompactSpace G] {N : Subgroup G} [N.Normal]

theorem admissible_character_inv (hN : IsClosed (N : Set G)) (hW : ∀ W : Subgroup N, IsOpen (W : Set N) → IsUnit (W.index : R))
    (M : TRep R G) [DiscreteTopology M.V] {Q : TRep R (G ⧸ N)} {P : Pair Q M} (hP : IsInvRep M N Q P)
    {QC : TRep R (G ⧸ N)} {PC : Pair QC (CG M)} (hC : IsInvRep (CG M) N QC PC)
    {QQ : TRep R (G ⧸ N)} {PQ : Pair QQ (QG M)} (hQ : IsInvRep (QG M) N QQ PQ) :
    admitted (invPair hP hC (iCG M) (iCG_equiv M))
      (invPair hC hQ (pLin M) (pLin_equiv M)) := by
  have := inv_disc hP
  have := inv_disc hC
  have := inv_disc hQ
  refine ⟨rfl, rfl, emb_disc _ fun a b h => ?_, fun c => ?_, ?_⟩
  · have h' := congrArg PC.u h
    rw [invPair_u, invPair_u] at h'
    exact hP.2.1.injective (iCG_inj M h')
  · constructor
    · intro hc
      have h1 := congrArg PQ.u hc
      rw [invPair_u, map_zero, pLin_eq_zero] at h1
      obtain ⟨m, hm⟩ := h1
      have hmN : ∀ g ∈ N, M.rho g m = m := fun g hg => iCG_inj M (by
        rw [iCG_equiv, hm, inv_mem hC c g hg])
      obtain ⟨q, rfl⟩ := (hP.2.2 m).2 hmN
      refine ⟨q, hC.2.1.injective ?_⟩
      rw [invPair_u, hm]
    · rintro ⟨q, rfl⟩
      apply hQ.2.1.injective
      rw [invPair_u, invPair_u, map_zero, pLin_eq_zero]
      exact ⟨_, rfl⟩
  · have hs : Surjective (invPair hC hQ (pLin M) (pLin_equiv M)).u := by
      intro y
      obtain ⟨c, hcN, hc⟩ := inv_lift (R := R) N hN hW (CG M) (QG M) (pLin M)
        (pLin_equiv M) (pLin_surj M) (PQ.u y) (inv_mem hQ y)
      obtain ⟨c', rfl⟩ := (hC.2.2 c).2 hcN
      exact ⟨c', hQ.2.1.injective (by rw [invPair_u, hc])⟩
    exact ⟨surjInv hs, continuous_of_discreteTopology, surjInv_eq hs⟩

theorem main (hN : IsClosed (N : Set G)) (hW : ∀ W : Subgroup N, IsOpen (W : Set N) → IsUnit (W.index : R))
    (n : ℕ) : ∀ (M : TRep R G) [DiscreteTopology M.V] (Q : TRep R (G ⧸ N)) (P : Pair Q M),
    IsInvRep M N Q P → Bijective (P.hom.H n) := by
  induction n with
  | zero => exact fun M _ Q P hP => deg0 M Q P hP
  | succ n ih =>
  intro M _ Q P hP
  have hC := InflationRestrictionInvariants.invariants_isInvRep (CG M) N
  have hQ := InflationRestrictionInvariants.invariants_isInvRep (QG M) N
  have hadm := admissible_character_inv hN hW M hP hC hQ
  have hs := admissibility_holds R (G ⧸ N) _ _ _ _ _ hadm
  have hs' := admissibility_holds R G _ _ _ _ _ (admissible_compact_discrete M)
  obtain ⟨⟨δ, hδ, hL⟩, -⟩ := lES_holds R _ _ _ _ _ hs
  obtain ⟨⟨δ', hδ', hL'⟩, -⟩ := lES_holds R _ _ _ _ _ hs'
  have c1 := invPair_comm hP hC (iCG M) (iCG_equiv M) continuous_of_discreteTopology
  have c2 := invPair_comm hC hQ (pLin M) (pLin_equiv M)
    (pLin_cont M)
  have hnat := connNat_holds R _ _ _ _ _ _ _ _ _ _ P.hom _ _ δ δ' hs hs' c1 c2 hδ hδ'
  have hβ := ih (CG M) _ _ hC
  have hγ := ih (QG M) _ _ hQ
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
    obtain ⟨x, rfl⟩ := ((hL.exA n) y).1 (QC_acyc M hC n _)
    rw [← hnat] at hy
    obtain ⟨c, hc⟩ := ((hL'.exC n) _).1 hy
    obtain ⟨c', rfl⟩ := hβ.2 c
    rw [← H_comm _ (pP M).hom _ _ c2 n c'] at hc
    rw [← hγ.1 hc]
    exact ((hL.exC n) _).2 ⟨c', rfl⟩
  · intro y
    obtain ⟨x, rfl⟩ := ((hL'.exA n) y).1 (CG_acyc M n _)
    obtain ⟨x', rfl⟩ := hγ.2 x
    exact ⟨δ n x', (hnat n x').symm⟩

end InflationIsomorphism

end

end ReciprocityTheory.Coh
end

-- bundled from ReciprocityTheory.GroupCohomology.LengthKerEqCoker
section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Function

universe u

namespace ProcyclicCohomology

theorem length_ker_eq_coker {R : Type u} [CommRing R] {V : Type u} [AddCommGroup V] [Module R V]
    (f : V →ₗ[R] V) (h : IsFiniteLength R V) :
    Module.length R (LinearMap.ker f) = Module.length R (V ⧸ LinearMap.range f) := by
  have h1 : Module.length R V = Module.length R (LinearMap.ker f) + Module.length R (LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict (Submodule.injective_subtype _)
      f.surjective_rangeRestrict
      (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
  have h2 : Module.length R V = Module.length R (LinearMap.range f) + Module.length R (V ⧸ LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
      (Submodule.injective_subtype _) (LinearMap.range f).mkQ_surjective (LinearMap.exact_subtype_mkQ _)
  have hVt : Module.length R V ≠ ⊤ := Module.length_ne_top_iff.2 h
  have hL : Module.length R (LinearMap.range f) ≠ ⊤ := fun h' => hVt (by rw [h1, h', add_top])
  rw [h1, add_comm (Module.length R (LinearMap.range f))] at h2
  exact (WithTop.add_right_cancel hL h2)

end ProcyclicCohomology

theorem zHat_holds : ZHatStatement.{u} := by
  intro R _ G _ _ _ _ _ _ s hG M _ htor
  have hs := hG.1
  have hidx := hG.2
  have hc := ProcyclicCohomology.comm_of_dense hs
  have hA := ProcyclicCohomology.model_comparison_degree_zero_bijective M hc hs hidx htor
  have hH2 : ∀ (M' : TRep R G) [DiscreteTopology M'.V], (∀ m : M'.V, ∃ k : ℕ, 0 < k ∧ k • m = 0) →
      Subsingleton (M'.H 2) := by
    intro M' _ ht
    obtain ⟨-, -, -, e2, -⟩ := low_holds R G M'
    have := ProcyclicCohomology.subsingleton_H2_of_procyclic_of_torsion M' hc hs hidx ht
    exact e2.toEquiv.subsingleton
  have hB : ∀ n, 1 < n → Subsingleton (M.H n) := fun n hn =>
    shift_holds R G 2 hH2 M htor n hn
  refine ⟨hA, hB, fun hM => ?_⟩
  obtain ⟨-, ⟨e0, -⟩, ⟨e1, -⟩, -⟩ := low_holds R G M
  obtain ⟨eA, -⟩ := hA
  set f := M.rho s - LinearMap.id
  have hH0 : H0 M.rho = LinearMap.ker f := by
    ext m
    rw [mem_riemannRochSpace_iff_regularAt_everywhere, LinearMap.mem_ker]
    constructor
    · intro h; simp [f, h s]
    · intro h g
      have h' : M.rho s m = m := by
        have := h
        simp only [f, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
        exact this
      have := ProcyclicCohomology.cocycle_eq_of_apply M hs 0 (Z1 M.rho).zero_mem m (by simp [h']) g
      rw [Pi.zero_apply, eq_comm, sub_eq_zero] at this
      exact this
  have fl0 : IsFiniteLength R (M.H 0) :=
    (hM.of_injective (Submodule.injective_subtype (H0 M.rho))).of_injective e0.injective
  have fl1 : IsFiniteLength R (M.H 1) :=
    (hM.of_surjective (Submodule.mkQ_surjective (LinearMap.range f))).of_injective
      (e1.trans eA).injective
  have hfl : ∀ n, IsFiniteLength R (M.H n) := by
    intro n
    rcases n with _ | _ | n
    · exact fl0
    · exact fl1
    · have := hB (n + 2) (by omega); exact .of_subsingleton
  refine ⟨⟨hfl, hB⟩, ?_⟩
  have l0 : Module.length R (M.H 0) = Module.length R (LinearMap.ker f) := by
    rw [e0.length_eq, hH0]
  have l1 : Module.length R (M.H 1) = Module.length R (M.V ⧸ LinearMap.range f) :=
    (e1.trans eA).length_eq
  have l01 : Module.length R (M.H 0) = Module.length R (M.H 1) := by
    rw [l0, l1, ProcyclicCohomology.length_ker_eq_coker f hM]
  simp only [Cx.chi, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, one_mul,
    neg_one_mul, zero_add]
  rw [show Module.length R (M.coch.H 0) = Module.length R (M.coch.H 1) from l01]
  ring

end ReciprocityTheory.Coh
end

