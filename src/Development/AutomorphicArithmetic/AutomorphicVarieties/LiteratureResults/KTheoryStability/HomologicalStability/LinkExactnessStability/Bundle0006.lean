import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.InnerAutActsTriviallyGroupHomology
section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

def conjActHom {k G : Type} [CommRing k] [Group G] (g : G) (A : Rep k G) :
    A ⟶ Rep.res (MulAut.conj g).toMonoidHom A :=
  Rep.ofHom ⟨A.ρ g, fun h => LinearMap.ext fun a => by
    change A.ρ g (A.ρ h a) = A.ρ (g * h * g⁻¹) (A.ρ g a)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]⟩

theorem conjActHom_hom_apply {k G : Type} [CommRing k] [Group G] (g : G) (A : Rep k G) (a : A) :
    (conjActHom g A).hom a = A.ρ g a := rfl

theorem conj_map_eq_id_zero (k G : Type) [CommRing k] [Group G] (g : G) (A : Rep k G)
    (u : A ⟶ Rep.res (MulAut.conj g).toMonoidHom A) (hu : ∀ a, u.hom a = A.ρ g a) :
    groupHomology.map (MulAut.conj g).toMonoidHom u 0 = 𝟙 _ := by
  rw [← cancel_epi (groupHomology.H0π A), groupHomology.H0π_comp_map, Category.comp_id]
  ext a
  have hv : (groupHomology.H0π A).hom (A.ρ g a) = (groupHomology.H0π A).hom a := by
    rw [← groupHomology.coinvariantsMk_comp_H0Iso_inv]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    congr 1
    exact Representation.Coinvariants.mk_self_apply _ _ _
  rw [← hv, ← hu]
  rfl

theorem conj_map_eq_id : ∀ (k G : Type) [CommRing k] [Group G] (g : G) (n : ℕ) (A : Rep k G)
    (u : A ⟶ Rep.res (MulAut.conj g).toMonoidHom A), (∀ a, u.hom a = A.ρ g a) →
    groupHomology.map (MulAut.conj g).toMonoidHom u n = 𝟙 _ := by
  intro k G _ _ g n
  induction n with
  | zero => exact conj_map_eq_id_zero k G g
  | succ n ih =>
    intro A u hu
    obtain ⟨ι, K, i, e, h, hS⟩ := exists_free_shortExact k G A
    have hP : IsZero (groupHomology (Rep.free k G ι) (n + 1)) :=
      GlobalTheory.T.projective_rep_groupHomology_pos_vanishes k G (Rep.free k G ι) inferInstance n
    have hmono := groupHomology.mono_δ_of_isZero hS n hP
    have hnat := (GlobalTheory.T.groupHomology_longExact_maps_natural_of_res k G G (MulAut.conj g).toMonoidHom _ _ hS hS
      (conjActHom g K) (conjActHom g (Rep.free k G ι)) u
      (fun a => by
        change (Rep.free k G ι).ρ g (i.hom a) = i.hom (K.ρ g a)
        exact (Rep.hom_comm_apply i g a).symm)
      (fun a => by
        change u.hom (e.hom a) = e.hom ((Rep.free k G ι).ρ g a)
        rw [hu]
        exact (Rep.hom_comm_apply e g a).symm) n).1
    rw [ih K (conjActHom g K) (fun _ => rfl), Category.comp_id] at hnat
    rw [← cancel_mono (groupHomology.δ hS (n + 1) n rfl), Category.id_comp]
    exact hnat.symm

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.innerAut_acts_trivially_groupHomology : ∀ (k G : Type) [CommRing k] [Group G] (g : G) (n : ℕ) (A : Rep k G) (u : A ⟶ Rep.res (MulAut.conj g).toMonoidHom A), (∀ a, u.hom a = A.ρ g a) → groupHomology.map (MulAut.conj g).toMonoidHom u n = 𝟙 _ := by
  first
  | exact @GlobalTheory.HomStab.conj_map_eq_id
  | exact @GlobalTheory.HomStab.conj_map_eq_id_zero
  | exact @GlobalTheory.HomStab.conjActHom_hom_apply
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PairNilHbdVbdEqZeroOfCycle
section
namespace GlobalTheory.SeqCx

theorem cycle_pair_empty (V W : Type) (D : Set (List V × List W)) (p : ℕ) (c : List V →₀ ℤ)
    (hc : c ∈ chains {l | (l, ([] : List W)) ∈ D} p) (hb : bd V c = 0) :
    Finsupp.mapDomain (fun l => (l, ([] : List W))) c ∈ chains2 D p 0 ∧
      hbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 ∧
      vbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 := by
  have hlin : ∀ d : List V →₀ ℤ, Finsupp.mapDomain (fun l => (l, ([] : List W))) d
      = Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W))) d := fun d => rfl
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [chains2, Finsupp.mem_supported]
    rw [chains, Finsupp.mem_supported] at hc
    intro z hz
    have hz' := Finsupp.mapDomain_support hz
    rw [Finset.mem_image] at hz'
    obtain ⟨l, hl, rfl⟩ := hz'
    have := hc (Finset.mem_coe.mpr hl)
    exact ⟨this.1, this.2, rfl⟩
  · have key : (hbd V W).comp (Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W))))
        = (Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W)))).comp (bd V) := by
      apply Finsupp.lhom_ext'
      intro l
      apply LinearMap.ext_ring
      simp [hbd, Finsupp.mapDomain_single]
    have := LinearMap.congr_fun key c
    simp only [LinearMap.comp_apply] at this
    rw [hlin, this, hb, map_zero]
  · have key : (vbd V W).comp (Finsupp.lmapDomain ℤ ℤ (fun l => (l, ([] : List W)))) = 0 := by
      apply Finsupp.lhom_ext'
      intro l
      apply LinearMap.ext_ring
      simp [vbd, bd, Finsupp.mapDomain_single]
    have := LinearMap.congr_fun key c
    simpa [LinearMap.comp_apply] using this

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.pair_nil_hbd_vbd_eq_zero_of_cycle : ∀ (V W : Type) (D : Set (List V × List W)) (p : ℕ) (c : List V →₀ ℤ), c ∈ chains {l | (l, ([] : List W)) ∈ D} p → bd V c = 0 → Finsupp.mapDomain (fun l => (l, ([] : List W))) c ∈ chains2 D p 0 ∧ hbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 ∧ vbd V W (Finsupp.mapDomain (fun l => (l, ([] : List W))) c) = 0 := by
  first
  | exact @GlobalTheory.SeqCx.cycle_pair_empty
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PairSeqBoundariesLowerBidegreeOfSubClosed
section
noncomputable section

namespace GlobalTheory.SeqCx

open Finsupp

theorem map_supported_mem {α β : Type} {S : Set α}
    (f : (α →₀ ℤ) →ₗ[ℤ] (β →₀ ℤ)) (P : Submodule ℤ (β →₀ ℤ)) (h : ∀ z ∈ S, f (Finsupp.single z 1) ∈ P) :
    ∀ x ∈ Finsupp.supported ℤ ℤ S, f x ∈ P := by
  intro x hx
  rw [← Finsupp.sum_single x, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun a ha => ?_
  rw [← Finsupp.smul_single_one, map_zsmul]
  exact P.smul_mem _ (h a (hx ha))

theorem hbd_single (V W : Type) (z : List V × List W) :
    hbd V W (Finsupp.single z 1) =
      ∑ i ∈ Finset.range z.1.length, (-1 : ℤ) ^ i • Finsupp.single (z.1.eraseIdx i, z.2) (1 : ℤ) := by
  simp only [hbd, bd, Finsupp.linearCombination_single, one_smul, Finsupp.mapDomain_finset_sum,
    Finsupp.mapDomain_smul, Finsupp.mapDomain_single]

theorem vbd_single (V W : Type) (z : List V × List W) :
    vbd V W (Finsupp.single z 1) =
      ∑ i ∈ Finset.range z.2.length, (-1 : ℤ) ^ i • Finsupp.single (z.1, z.2.eraseIdx i) (1 : ℤ) := by
  simp only [vbd, bd, Finsupp.linearCombination_single, one_smul, Finsupp.mapDomain_finset_sum,
    Finsupp.mapDomain_smul, Finsupp.mapDomain_single]

theorem bd_chains2 : ∀ (V W : Type) (D : Set (List V × List W)), SubClosed2 D →
    (∀ a b, ∀ x ∈ chains2 D (a + 1) b, hbd V W x ∈ chains2 D a b) ∧
    (∀ a b, ∀ x ∈ chains2 D a (b + 1), vbd V W x ∈ chains2 D a b) ∧
    (∀ b, ∀ x ∈ chains2 D 0 b, hbd V W x = 0) := by
  intro V W D hD
  refine ⟨fun a b => ?_, fun a b => ?_, fun b => ?_⟩
  · refine map_supported_mem (hbd V W) _ ?_
    rintro z ⟨hz, h1, h2⟩
    rw [hbd_single]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
    refine Finsupp.single_mem_supported ℤ _ ?_
    have hi' : i < z.1.length := Finset.mem_range.mp hi
    refine ⟨hD z hz _ _ (List.eraseIdx_sublist _ _) (List.Sublist.refl _), ?_, h2⟩
    rw [List.length_eraseIdx_of_lt hi', h1]
    rfl
  · refine map_supported_mem (vbd V W) _ ?_
    rintro z ⟨hz, h1, h2⟩
    rw [vbd_single]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
    refine Finsupp.single_mem_supported ℤ _ ?_
    have hi' : i < z.2.length := Finset.mem_range.mp hi
    refine ⟨hD z hz _ _ (List.Sublist.refl _) (List.eraseIdx_sublist _ _), h1, ?_⟩
    rw [List.length_eraseIdx_of_lt hi', h2]
    rfl
  · intro x hx
    have := map_supported_mem (hbd V W) (⊥ : Submodule ℤ _) ?_ x hx
    · simpa using this
    rintro z ⟨_, h1, _⟩
    rw [hbd_single, h1]
    simp

end GlobalTheory.SeqCx

end

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.pairSeqBoundaries_lower_bidegree_of_subClosed : ∀ (V W : Type) (D : Set (List V × List W)), SubClosed2 D → (∀ a b, ∀ x ∈ chains2 D (a + 1) b, hbd V W x ∈ chains2 D a b) ∧ (∀ a b, ∀ x ∈ chains2 D a (b + 1), vbd V W x ∈ chains2 D a b) ∧ (∀ b, ∀ x ∈ chains2 D 0 b, hbd V W x = 0) := by
  first
  | exact @GlobalTheory.SeqCx.bd_chains2
  | exact @GlobalTheory.SeqCx.vbd_single
  | exact @GlobalTheory.SeqCx.hbd_single
  | exact @GlobalTheory.SeqCx.map_supported_mem
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PairSeqDoubleComplexBoundaryRelations
section
open GlobalTheory.SeqCx

namespace GlobalTheory.SeqCx.DblBd

theorem single_eq_smul {α : Type} (a : α) (r : ℤ) :
    Finsupp.single a r = r • Finsupp.single a (1 : ℤ) := by
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

theorem hbd_single (V W : Type) (z : List V × List W) :
    hbd V W (Finsupp.single z 1) =
      ∑ i ∈ Finset.range z.1.length, (-1 : ℤ) ^ i • Finsupp.single (z.1.eraseIdx i, z.2) (1 : ℤ) := by
  simp [hbd, bd, Finsupp.linearCombination_single, Finsupp.mapDomain_finset_sum,
    Finsupp.mapDomain_smul, Finsupp.mapDomain_single]

theorem vbd_single (V W : Type) (z : List V × List W) :
    vbd V W (Finsupp.single z 1) =
      ∑ j ∈ Finset.range z.2.length, (-1 : ℤ) ^ j • Finsupp.single (z.1, z.2.eraseIdx j) (1 : ℤ) := by
  simp [vbd, bd, Finsupp.linearCombination_single, Finsupp.mapDomain_finset_sum,
    Finsupp.mapDomain_smul, Finsupp.mapDomain_single]

theorem hbd_mapDomain (V W : Type) (w : List W) (c : List V →₀ ℤ) :
    hbd V W (Finsupp.mapDomain (fun x => (x, w)) c) = Finsupp.mapDomain (fun x => (x, w)) (bd V c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add, hf, hg, map_add, Finsupp.mapDomain_add]
  | single l r =>
    rw [Finsupp.mapDomain_single, single_eq_smul, map_zsmul, single_eq_smul l r, map_zsmul,
      Finsupp.mapDomain_smul]
    simp [hbd, Finsupp.linearCombination_single]

theorem vbd_mapDomain (V W : Type) (x : List V) (c : List W →₀ ℤ) :
    vbd V W (Finsupp.mapDomain (fun w => (x, w)) c) = Finsupp.mapDomain (fun w => (x, w)) (bd W c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add, hf, hg, map_add, Finsupp.mapDomain_add]
  | single l r =>
    rw [Finsupp.mapDomain_single, single_eq_smul, map_zsmul, single_eq_smul l r, map_zsmul,
      Finsupp.mapDomain_smul]
    simp [vbd, Finsupp.linearCombination_single]

theorem hbd_hbd (V W : Type) (x : List V × List W →₀ ℤ) : hbd V W (hbd V W x) = 0 := by
  have h : hbd V W ∘ₗ hbd V W = 0 := by
    apply Finsupp.lhom_ext
    intro z r
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [single_eq_smul, map_zsmul, map_zsmul]
    have e : hbd V W (Finsupp.single z 1) =
        Finsupp.mapDomain (fun x => (x, z.2)) (bd V (Finsupp.single z.1 1)) := by
      simp [hbd, Finsupp.linearCombination_single]
    rw [e, hbd_mapDomain, bd_bd, Finsupp.mapDomain_zero, smul_zero]
  exact congrArg (fun f => f x) h

theorem vbd_vbd (V W : Type) (x : List V × List W →₀ ℤ) : vbd V W (vbd V W x) = 0 := by
  have h : vbd V W ∘ₗ vbd V W = 0 := by
    apply Finsupp.lhom_ext
    intro z r
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [single_eq_smul, map_zsmul, map_zsmul]
    have e : vbd V W (Finsupp.single z 1) =
        Finsupp.mapDomain (fun w => (z.1, w)) (bd W (Finsupp.single z.2 1)) := by
      simp [vbd, Finsupp.linearCombination_single]
    rw [e, vbd_mapDomain, bd_bd, Finsupp.mapDomain_zero, smul_zero]
  exact congrArg (fun f => f x) h

theorem hbd_vbd (V W : Type) (x : List V × List W →₀ ℤ) : hbd V W (vbd V W x) = vbd V W (hbd V W x) := by
  have h : hbd V W ∘ₗ vbd V W = vbd V W ∘ₗ hbd V W := by
    apply Finsupp.lhom_ext
    intro z r
    simp only [LinearMap.comp_apply]
    rw [single_eq_smul, map_zsmul, map_zsmul, map_zsmul, map_zsmul]
    congr 1
    rw [vbd_single, hbd_single, map_sum, map_sum]
    simp only [map_zsmul, hbd_single, vbd_single, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  exact congrArg (fun f => f x) h

end GlobalTheory.SeqCx.DblBd

namespace GlobalTheory.SeqCx

theorem dbl_bd : ∀ (V W : Type), (∀ x, hbd V W (hbd V W x) = 0) ∧ (∀ x, vbd V W (vbd V W x) = 0) ∧
    (∀ x, hbd V W (vbd V W x) = vbd V W (hbd V W x)) :=
  fun V W => ⟨DblBd.hbd_hbd V W, DblBd.vbd_vbd V W, DblBd.hbd_vbd V W⟩

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.pairSeqDoubleComplex_boundary_relations : ∀ (V W : Type), (∀ x, hbd V W (hbd V W x) = 0) ∧ (∀ x, vbd V W (vbd V W x) = 0) ∧ (∀ x, hbd V W (vbd V W x) = vbd V W (hbd V W x)) := by
  first
  | exact @GlobalTheory.SeqCx.dbl_bd
  | exact @GlobalTheory.SeqCx.DblBd.hbd_vbd
  | exact @GlobalTheory.SeqCx.DblBd.vbd_vbd
  | exact @GlobalTheory.SeqCx.DblBd.hbd_hbd
  | exact @GlobalTheory.SeqCx.DblBd.vbd_mapDomain
  | exact @GlobalTheory.SeqCx.DblBd.hbd_mapDomain
  | exact @GlobalTheory.SeqCx.DblBd.vbd_single
  | exact @GlobalTheory.SeqCx.DblBd.hbd_single
  | exact @GlobalTheory.SeqCx.DblBd.single_eq_smul
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PairSeqHorizontalCycleIsBoundaryOfSlicesExact
section
noncomputable section

open Classical

namespace GlobalTheory.SeqCx

namespace DblRow

variable {V W : Type}

theorem pair_injective (w : List W) : Function.Injective (fun l : List V => (l, w)) :=
  fun _ _ h => (Prod.mk.inj h).1

def proj (w : List W) (x : List V × List W →₀ ℤ) : List V →₀ ℤ :=
  Finsupp.comapDomain (fun l : List V => (l, w)) x (pair_injective w).injOn

theorem proj_apply (w : List W) (x : List V × List W →₀ ℤ) (l : List V) :
    proj w x l = x (l, w) := rfl

def incl (w : List W) : (List V →₀ ℤ) →ₗ[ℤ] (List V × List W →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun l : List V => (l, w))

theorem incl_apply (w w' : List W) (z : List V →₀ ℤ) (l : List V) :
    incl w z (l, w') = if w = w' then z l else 0 := by
  by_cases h : w = w'
  · subst h
    rw [if_pos rfl]
    exact Finsupp.mapDomain_apply (pair_injective w) z l
  · rw [if_neg h]
    apply Finsupp.mapDomain_notin_range
    rintro ⟨l', hl'⟩
    exact h (congrArg Prod.snd hl')

theorem hbd_incl (w : List W) (z : List V →₀ ℤ) : hbd V W (incl w z) = incl w (bd V z) := by
  have : (hbd V W).comp (incl w) = (incl w).comp (bd V) := by
    apply Finsupp.lhom_ext
    intro l c
    simp only [LinearMap.comp_apply]
    rw [show Finsupp.single l c = c • Finsupp.single l (1 : ℤ) by simp, map_smul, map_smul, map_smul,
      map_smul]
    congr 1
    simp only [incl, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hbd,
      Finsupp.linearCombination_single, one_smul]
  exact LinearMap.congr_fun this z

theorem decomp (x : List V × List W →₀ ℤ) :
    x = ∑ w ∈ x.support.image Prod.snd, incl w (proj w x) := by
  ext ⟨l, w'⟩
  rw [Finsupp.finset_sum_apply]
  simp only [incl_apply, proj_apply]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · symm
    by_contra hne
    exact h (Finset.mem_image.2 ⟨(l, w'), Finsupp.mem_support_iff.2 (Ne.symm hne), rfl⟩)

end DblRow

open DblRow

theorem dblRow_exact : ∀ (V W : Type) (D : Set (List V × List W)) (a b : ℕ),
    (∀ w : List W, w.length = b → (∃ l, (l, w) ∈ D) → ExactAt {l | (l, w) ∈ D} a) →
    ∀ x ∈ chains2 D a b, hbd V W x = 0 → ∃ y ∈ chains2 D (a + 1) b, hbd V W y = x := by
  intro V W D a b hex x hx h0
  have hsupp : ∀ z ∈ x.support, z ∈ D ∧ z.1.length = a ∧ z.2.length = b := fun z hz => hx hz
  set T := x.support.image Prod.snd with hT
  have h1 : hbd V W x = ∑ w ∈ T, incl w (bd V (proj w x)) := by
    conv_lhs => rw [decomp x]
    rw [map_sum]
    simp only [hbd_incl]
    rfl
  have hbd0 : ∀ w ∈ T, bd V (proj w x) = 0 := by
    intro w hw
    ext l
    have := congrArg (fun z => z (l, w)) h1
    simp only [h0, Finsupp.coe_zero, Pi.zero_apply, Finsupp.finset_sum_apply, incl_apply] at this
    rw [Finset.sum_ite_eq', if_pos hw] at this
    simpa using this.symm
  have hslice : ∀ w ∈ T, ∃ y ∈ chains {l | (l, w) ∈ D} (a + 1), bd V y = proj w x := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨hzD, -, hzb⟩ := hsupp z hz
    refine hex z.2 hzb ⟨z.1, hzD⟩ (proj z.2 x) ?_ (hbd0 z.2 hw)
    intro l hl
    have hl' : (l, z.2) ∈ x.support := by
      have hl2 := Finset.mem_coe.1 hl
      rw [Finsupp.mem_support_iff] at hl2 ⊢
      exact hl2
    obtain ⟨h2, h3, -⟩ := hsupp _ hl'
    exact ⟨h2, h3⟩
  choose! yw hyw hywb using hslice
  refine ⟨∑ w ∈ T, incl w (yw w), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun w hw => ?_
    intro z hz
    have hz' := Finsupp.mapDomain_support hz
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hz'
    obtain ⟨h2, h3⟩ := hyw w hw hl
    obtain ⟨z0, hz0, rfl⟩ := Finset.mem_image.1 hw
    exact ⟨h2, h3, (hsupp z0 hz0).2.2⟩
  · rw [map_sum]
    simp only [hbd_incl]
    conv_rhs => rw [decomp x]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hywb w hw]

end GlobalTheory.SeqCx

end

section
open GlobalTheory.SeqCx
theorem _root_.GlobalTheory.T.pairSeqHorizontalCycle_is_boundary_of_slices_exact : ∀ (V W : Type) (D : Set (List V × List W)) (a b : ℕ), (∀ w : List W, w.length = b → (∃ l, (l, w) ∈ D) → ExactAt {l | (l, w) ∈ D} a) → ∀ x ∈ chains2 D a b, hbd V W x = 0 → ∃ y ∈ chains2 D (a + 1) b, hbd V W y = x := by
  first
  | exact @GlobalTheory.SeqCx.dblRow_exact
  | exact @GlobalTheory.SeqCx.DblRow.decomp
  | exact @GlobalTheory.SeqCx.DblRow.hbd_incl
  | exact @GlobalTheory.SeqCx.DblRow.incl_apply
  | exact @GlobalTheory.SeqCx.DblRow.proj_apply
  | exact @GlobalTheory.SeqCx.DblRow.pair_injective
end
end

