import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PairSeqVerticalCycleIsBoundaryOfSlicesExact
section
open GlobalTheory.SeqCx

namespace GlobalTheory.SeqCx.ColDecomp

lemma inj_pair {V W : Type} (l : List V) : Function.Injective (fun w : List W => (l, w)) := by
  intro u v h
  exact (Prod.mk.inj h).2

open Classical in
lemma sum_apply_pair {V W : Type} (T : Finset (List V)) (g : List V → List W →₀ ℤ) (l : List V) (w : List W) :
    (∑ l' ∈ T, Finsupp.mapDomain (fun w => (l', w)) (g l')) (l, w) = if l ∈ T then g l w else 0 := by
  rw [Finsupp.finset_sum_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single l]
    · exact Finsupp.mapDomain_apply (inj_pair l) _ _
    · intro l' _ hne
      apply Finsupp.mapDomain_notin_range
      rintro ⟨w', hw'⟩
      exact hne (congrArg Prod.fst hw')
    · intro hl
      exact absurd h hl
  · apply Finset.sum_eq_zero
    intro l' hl'
    apply Finsupp.mapDomain_notin_range
    rintro ⟨w', hw'⟩
    obtain rfl : l' = l := congrArg Prod.fst hw'
    exact h hl'

lemma vbd_mapDomain {V W : Type} (l : List V) (c : List W →₀ ℤ) :
    vbd V W (Finsupp.mapDomain (fun w => (l, w)) c) = Finsupp.mapDomain (fun w => (l, w)) (bd W c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add, map_add, hf, hg, map_add, Finsupp.mapDomain_add]
  | single w k =>
    rw [Finsupp.mapDomain_single]
    simp only [vbd, bd, Finsupp.linearCombination_single]
    rw [one_smul, Finsupp.mapDomain_smul]

end GlobalTheory.SeqCx.ColDecomp

open GlobalTheory.SeqCx.ColDecomp in

theorem GlobalTheory.SeqCx.vertical_exact_of_columns : ∀ (V W : Type) (D : Set (List V × List W)) (a b : ℕ), (∀ l : List V, l.length = a → (∃ w, (l, w) ∈ D) → ExactAt {w | (l, w) ∈ D} b) → ∀ x ∈ chains2 D a b, vbd V W x = 0 → ∃ y ∈ chains2 D a (b + 1), vbd V W y = x := by
  classical
  intro V W D a b hex x hx hvx
  set T : Finset (List V) := x.support.image Prod.fst with hT
  set g : List V → List W →₀ ℤ := fun l => x.curry l with hg
  have hgapp : ∀ l w, g l w = x (l, w) := fun l w => Finsupp.curry_apply x l w
  have hsupp : ∀ z ∈ x.support, z ∈ D ∧ z.1.length = a ∧ z.2.length = b := fun z hz => hx hz
  have hdec : x = ∑ l ∈ T, Finsupp.mapDomain (fun w => (l, w)) (g l) := by
    ext ⟨l, w⟩
    rw [sum_apply_pair]
    split_ifs with h
    · rw [hgapp]
    · by_contra hne
      exact h (Finset.mem_image.2 ⟨(l, w), Finsupp.mem_support_iff.2 hne, rfl⟩)
  have hvdec : vbd V W x = ∑ l ∈ T, Finsupp.mapDomain (fun w => (l, w)) (bd W (g l)) := by
    conv_lhs => rw [hdec]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun l _ => vbd_mapDomain l (g l))
  have hcyc : ∀ l ∈ T, bd W (g l) = 0 := by
    intro l hl
    ext w
    have := congrArg (fun f => f (l, w)) hvdec
    simp only [hvx, sum_apply_pair, if_pos hl] at this
    simpa using this.symm
  have hchain : ∀ l ∈ T, g l ∈ chains {w | (l, w) ∈ D} b := by
    intro l hl
    rw [chains, Finsupp.mem_supported]
    intro w hw
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hgapp] at hw
    have := hsupp (l, w) (Finsupp.mem_support_iff.2 hw)
    exact ⟨this.1, this.2.2⟩
  have hpre : ∀ l ∈ T, l.length = a ∧ ∃ w, (l, w) ∈ D := by
    intro l hl
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hl
    have := hsupp z hz
    exact ⟨this.2.1, z.2, this.1⟩
  have hy : ∀ l ∈ T, ∃ y ∈ chains {w | (l, w) ∈ D} (b + 1), bd W y = g l := by
    intro l hl
    exact hex l (hpre l hl).1 (hpre l hl).2 (g l) (hchain l hl) (hcyc l hl)
  choose! y hymem hybd using hy
  refine ⟨∑ l ∈ T, Finsupp.mapDomain (fun w => (l, w)) (y l), ?_, ?_⟩
  · refine Submodule.sum_mem _ (fun l hl => ?_)
    rw [chains2, Finsupp.mem_supported]
    intro z hz
    have hz' := Finsupp.mapDomain_support (Finset.mem_coe.1 hz)
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz'
    have hyl := hymem l hl
    rw [chains, Finsupp.mem_supported] at hyl
    have := hyl (Finset.mem_coe.2 hw)
    exact ⟨this.1, (hpre l hl).1, this.2⟩
  · rw [map_sum, hdec]
    exact Finset.sum_congr rfl (fun l hl => by rw [vbd_mapDomain, hybd l hl])

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.pairSeqVerticalCycle_is_boundary_of_slices_exact : ∀ (V W : Type) (D : Set (List V × List W)) (a b : ℕ), (∀ l : List V, l.length = a → (∃ w, (l, w) ∈ D) → ExactAt {w | (l, w) ∈ D} b) → ∀ x ∈ chains2 D a b, vbd V W x = 0 → ∃ y ∈ chains2 D a (b + 1), vbd V W y = x := by
  first
  | exact @GlobalTheory.SeqCx.vertical_exact_of_columns
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SubClosedAndPermAndLinearEquivInvariantUniM
section
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.UniSeqBasic

theorem perm_lift {α β : Type} (f : α → β) {l l' : List β} (h : l.Perm l') :
    ∀ γ : List α, γ.map f = l → ∃ γ' : List α, γ.Perm γ' ∧ γ'.map f = l' := by
  induction h with
  | nil => intro γ hγ; exact ⟨γ, List.Perm.refl _, hγ⟩
  | cons x _ ih =>
    intro γ hγ
    rcases γ with _ | ⟨a, γ⟩
    · simp at hγ
    · simp only [List.map_cons, List.cons.injEq] at hγ
      obtain ⟨γ', h1, h2⟩ := ih γ hγ.2
      exact ⟨a :: γ', h1.cons a, by simp [h2, hγ.1]⟩
  | swap x y l =>
    intro γ hγ
    rcases γ with _ | ⟨a, _ | ⟨b, γ⟩⟩
    · simp at hγ
    · simp at hγ
    · simp only [List.map_cons, List.cons.injEq] at hγ
      exact ⟨b :: a :: γ, List.Perm.swap _ _ _, by simp [hγ.1, hγ.2.1, hγ.2.2]⟩
  | trans _ _ ih1 ih2 =>
    intro γ hγ
    obtain ⟨γ1, p1, e1⟩ := ih1 γ hγ
    obtain ⟨γ2, p2, e2⟩ := ih2 γ1 e1
    exact ⟨γ2, p1.trans p2, e2⟩

def Orth (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (a b : M × (M →ₗ[R] R)) : Prop := a.2 b.1 = 0 ∧ b.2 a.1 = 0

theorem orth_symm (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] :
    Symmetric (Orth R M) := fun _ _ h => ⟨h.2, h.1⟩

theorem mem_uniM_iff (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (l : List M) :
    l ∈ uniM R M ↔ ∃ γ : List (M × (M →ₗ[R] R)), γ.map Prod.fst = l ∧
      (∀ p ∈ γ, p.2 p.1 = 1) ∧ γ.Pairwise (Orth R M) := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨(List.finRange l.length).map (fun i => (l.get i, f i)), ?_, ?_, ?_⟩
    · apply List.ext_getElem <;> simp
    · intro p hp
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      simpa using hf i i
    · rw [List.pairwise_map]
      refine (List.pairwise_lt_finRange l.length).imp fun {i j} hij => ?_
      have hne : i ≠ j := ne_of_lt hij
      exact ⟨by simpa [hne] using hf i j, by simpa [hne.symm] using hf j i⟩
  · rintro ⟨γ, rfl, hone, hpw⟩
    refine ⟨fun i => (γ[i.1]'(by simpa using i.2)).2, fun i j => ?_⟩
    have hi : i.1 < γ.length := by simpa using i.2
    have hj : j.1 < γ.length := by simpa using j.2
    rw [List.pairwise_iff_getElem] at hpw
    simp only [List.get_eq_getElem, List.getElem_map]
    split_ifs with hij
    · subst hij
      exact hone _ (List.getElem_mem _)
    · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
      · exact (hpw _ _ hi hj h).1
      · exact (hpw _ _ hj hi h).2

theorem main : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], SubClosed (uniM R M) ∧ (∀ l l' : List M, l.Perm l' → l ∈ uniM R M → l' ∈ uniM R M) ∧ ∀ (ψ : M ≃ₗ[R] M) (l : List M), l.map ψ ∈ uniM R M ↔ l ∈ uniM R M := by
  intro R M _ _ _
  have key : ∀ (ψ : M ≃ₗ[R] M) (l : List M), l ∈ uniM R M → l.map ψ ∈ uniM R M := by
    intro ψ l hl
    obtain ⟨γ, rfl, hone, hpw⟩ := (mem_uniM_iff R M l).mp hl
    refine (mem_uniM_iff R M _).mpr
      ⟨γ.map (fun p => (ψ p.1, p.2 ∘ₗ (ψ.symm : M →ₗ[R] M))), ?_, ?_, ?_⟩
    · simp [List.map_map, Function.comp_def]
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      simpa using hone q hq
    · rw [List.pairwise_map]
      refine hpw.imp fun {a b} h => ?_
      simpa [Orth] using h
  refine ⟨?_, ?_, ?_⟩
  · intro l hl l' hsub
    obtain ⟨γ, rfl, hone, hpw⟩ := (mem_uniM_iff R M l).mp hl
    obtain ⟨γ', hγ', rfl⟩ := List.sublist_map_iff.mp hsub
    exact (mem_uniM_iff R M _).mpr ⟨γ', rfl, fun p hp => hone p (hγ'.subset hp), hpw.sublist hγ'⟩
  · intro l l' hperm hl
    obtain ⟨γ, hγ, hone, hpw⟩ := (mem_uniM_iff R M l).mp hl
    obtain ⟨γ', hp, hm⟩ := perm_lift Prod.fst hperm γ hγ
    exact (mem_uniM_iff R M _).mpr
      ⟨γ', hm, fun p hq => hone p (hp.symm.subset hq), hpw.perm hp (fun {_ _} h => orth_symm R M h)⟩
  · intro ψ l
    constructor
    · intro h
      have := key ψ.symm _ h
      simpa [List.map_map, Function.comp_def] using this
    · exact key ψ l

end GlobalTheory.UniSeqBasic

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.subClosed_and_perm_and_linearEquiv_invariant_uniM : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], SubClosed (uniM R M) ∧ (∀ l l' : List M, l.Perm l' → l ∈ uniM R M → l' ∈ uniM R M) ∧ ∀ (ψ : M ≃ₗ[R] M) (l : List M), l.map ψ ∈ uniM R M ↔ l ∈ uniM R M := by
  first
  | exact @GlobalTheory.UniSeqBasic.main
  | exact @GlobalTheory.UniSeqBasic.mem_uniM_iff
  | exact @GlobalTheory.UniSeqBasic.orth_symm
  | exact @GlobalTheory.UniSeqBasic.perm_lift
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SurjectiveHMapZeroOfStaircase
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.Staircase

theorem main : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 1 ≤ p → p + q = i → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Surjective (hMap (d 0) i).hom := by
  intro k G _ _ i C d hd hd0 hexC hexH
  have ses : ∀ (W X Y : Rep.{0, 0, 0} k G) (u : W ⟶ X) (v : X ⟶ Y) (huv : u ≫ v = 0),
      Function.Exact u.hom v.hom →
      (ShortComplex.mk (kernel.ι u) (kernel.lift v u huv)
        (by rw [← cancel_mono (kernel.ι v)]; simp)).ShortExact := by
    intro W X Y u v huv hex
    have hS' : (ShortComplex.mk (kernel.ι u) u (kernel.condition u)).Exact :=
      ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel u)
    let φ : ShortComplex.mk (kernel.ι u) (kernel.lift v u huv)
        (by rw [← cancel_mono (kernel.ι v)]; simp) ⟶
        ShortComplex.mk (kernel.ι u) u (kernel.condition u) :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι v, comm₁₂ := by simp, comm₂₃ := by simp }
    have hinj : Function.Injective (kernel.ι v).hom := (Rep.mono_iff_injective _).mp inferInstance
    refine { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hS',
             mono_f := inferInstance, epi_g := ?_ }
    rw [Rep.epi_iff_surjective]
    intro z
    have hz : v.hom ((kernel.ι v).hom z) = 0 := by
      have h := congrArg (fun f => f.hom z) (kernel.condition v)
      simpa using h
    obtain ⟨y, hy⟩ := (hex _).mp hz
    refine ⟨y, hinj ?_⟩
    have h := congrArg (fun f => f.hom y) (kernel.lift_ι v u huv)
    exact h.trans hy
  have epi0 : ∀ (X Y : Rep.{0, 0, 0} k G) (f : X ⟶ Y), Function.Surjective f.hom →
      Function.Surjective (hMap f 0).hom := by
    intro X Y f hf
    haveI : Epi f := (Rep.epi_iff_surjective f).mpr hf
    exact (ModuleCat.epi_iff_surjective _).mp (groupHomology.epi_map_0_of_epi f)
  have liftSurj : ∀ p, p + 1 ≤ i →
      Function.Surjective (kernel.lift (d p) (d (p + 1)) (hd p)).hom := by
    intro p hp
    exact (Rep.epi_iff_surjective _).mp (ses _ _ _ (d (p + 1)) (d p) (hd p) (hexC p hp)).epi_g
  have R : ∀ q p, p + 1 + q = i →
      Function.Surjective (hMap (kernel.lift (d p) (d (p + 1)) (hd p)) q).hom := by
    intro q
    induction q with
    | zero =>
      intro p hp
      exact epi0 _ _ _ (liftSurj p (by omega))
    | succ q ih =>
      intro p hp
      have hab : d (p + 3) ≫ kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1)) = 0 := by
        rw [← cancel_mono (kernel.ι (d (p + 1)))]
        simp [hd]
      have hbι : kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1)) ≫ kernel.ι (d (p + 1)) =
          d (p + 2) := kernel.lift_ι _ _ _
      have hE : Function.Exact (hMap (d (p + 3)) q).hom
          (hMap (kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1)) ≫ kernel.ι (d (p + 1))) q).hom := by
        rw [hbι]
        exact hexH (p + 2) q (by omega) (by omega)
      exact homStab_step k G (C (p + 4)) (C (p + 3)) (kernel (d (p + 1))) (C (p + 2)) (kernel (d p))
        (d (p + 3)) (kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1))) (kernel.ι (d (p + 1)))
        (kernel.lift (d p) (d (p + 1)) (hd p)) _
        (ses _ _ _ (d (p + 1)) (d p) (hd p) (hexC p (by omega))) hab q (ih (p + 1) (by omega)) hE
  cases i with
  | zero => exact epi0 _ _ _ hd0
  | succ q =>
    have ses0 : (ShortComplex.mk (kernel.ι (d 0)) (d 0) (kernel.condition _)).ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (d 0))
        mono_f := inferInstance
        epi_g := (Rep.epi_iff_surjective _).mpr hd0 }
    have hab : d 2 ≫ kernel.lift (d 0) (d 1) (hd 0) = 0 := by
      rw [← cancel_mono (kernel.ι (d 0))]
      simp [hd]
    have hbι : kernel.lift (d 0) (d 1) (hd 0) ≫ kernel.ι (d 0) = d 1 := kernel.lift_ι _ _ _
    have hE : Function.Exact (hMap (d 2) q).hom
        (hMap (kernel.lift (d 0) (d 1) (hd 0) ≫ kernel.ι (d 0)) q).hom := by
      rw [hbι]
      exact hexH 1 q (by omega) (by omega)
    exact homStab_step k G (C 3) (C 2) (kernel (d 0)) (C 1) (C 0) (d 2)
      (kernel.lift (d 0) (d 1) (hd 0)) (kernel.ι (d 0)) (d 0) _ ses0 hab q (R q 0 (by omega)) hE

end GlobalTheory.HomStab.Staircase

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.surjective_hMap_zero_of_staircase : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 1 ≤ p → p + q = i → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Surjective (hMap (d 0) i).hom := by
  first
  | exact @GlobalTheory.HomStab.Staircase.main
end
end

