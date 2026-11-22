import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PRCupTop
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open GlobalTheory.W1.Lef
open scoped TensorProduct

set_option autoImplicit false

namespace UpperTheory.Gal.productCup_of_system.RCT

private theorem wd_one {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (c : Finset ι → E) (s : Finset ι) :
    wd (fun _ : ι => (1 : Module.End ℂ E)) c s = deltaL ℂ ι E c s := by
  show _ = ∑ i ∈ s, GlobalTheory.cubeSign s i • c (s.erase i)
  simp [wd, Units.smul_def]

private theorem card_filters {n : ℕ} (i : Fin n) :
    (Finset.univ.filter (· ≤ i)).card + (Finset.univ.filter (i ≤ ·)).card = n + 1 := by
  have h1 : (Finset.univ.filter (· ≤ i)) ∪ (Finset.univ.filter (i ≤ ·)) = Finset.univ := by
    ext j; simp [le_total]
  have h2 : (Finset.univ.filter (· ≤ i)) ∩ (Finset.univ.filter (i ≤ ·)) = {i} := by
    ext j; simp [le_antisymm_iff]
  have := Finset.card_union_add_card_inter (Finset.univ.filter (· ≤ i)) (Finset.univ.filter (i ≤ ·))
  rw [h1, h2] at this
  simp at this
  omega

variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]

private theorem muP_tmul (τ : DR ℂ K →ₗ[K] K) (w' w'' w : DR ℂ K) :
    muP F K τ (w' ⊗ₜ w'') w = (Algebra.trace F K (τ (w' * w))) ⊗ₜ w'' := by
  simp [muP]

private theorem res_tmul (ρ : F →ₗ[ℂ] ℂ) (f : F) (w : DR ℂ K) : resP (DR ℂ K) ρ (f ⊗ₜ w) = ρ f • w := by
  simp [resP]

private noncomputable def bil (τ : DR ℂ K →ₗ[K] K) (ρ : F →ₗ[ℂ] ℂ) :
    DR ℂ K ⊗[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ K :=
  (muP F K τ).compr₂ (resP (DR ℂ K) ρ)

private theorem bil_tmul (τ : DR ℂ K →ₗ[K] K) (ρ : F →ₗ[ℂ] ℂ) (w' w'' w : DR ℂ K) :
    bil τ ρ (w' ⊗ₜ w'') w = ρ (Algebra.trace F K (τ (w' * w))) • w'' := by
  simp [bil, muP_tmul, res_tmul]

variable {d : ℕ} {x : Fin (d + 1) → Fˣ}

private theorem bil_mem (τ : DR ℂ K →ₗ[K] K) (ρ : F →ₗ[ℂ] ℂ) {a : ℕ} {I J : Finset (Fin (d + 1))}
    {e : DR ℂ K ⊗[ℂ] DR ℂ K} (he : e ∈ MZ F K (xv x) a I J) (v : DR ℂ K) :
    bil τ ρ e v ∈ omB ℂ K (rB ℂ K (xv x) J) a := by
  have h : MZ F K (xv x) a I J ≤ (omB ℂ K (rB ℂ K (xv x) J) a).comap ((bil τ ρ).flip v) :=
    Submodule.map₂_le.2 fun m _ n hn => by
      show bil τ ρ (m ⊗ₜ n) v ∈ omB ℂ K (rB ℂ K (xv x) J) a
      rw [bil_tmul]
      exact Submodule.smul_mem _ _ hn
  exact h he

private theorem bil_face (hc : IsFinCover ℂ K (xv x)) {τ : DR ℂ K →ₗ[K] K} (hτ : IsTop ℂ K (xv x) τ)
    {ρ : F →ₗ[ℂ] ℂ} (hρ : IsRes ℂ (xv x) ρ) {a : ℕ} (had : a ≤ d) (i : Fin (d + 1))
    (hne : (Finset.univ.erase i).Nonempty) (J : Finset (Fin (d + 1)))
    {e : DR ℂ K ⊗[ℂ] DR ℂ K} (he : e ∈ MZ F K (xv x) a (Finset.univ.erase i) J)
    {v : DR ℂ K} (hv : v ∈ omB ℂ K (rB ℂ K (xv x) (Finset.univ.erase i)) a) :
    bil τ ρ e v = 0 := by
  have hdeg : v ∈ ⋀[K]^a Ω[K⁄ℂ] := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties ℂ K _ a 0).2.1 v hv).2.2.1
  have h : MZ F K (xv x) a (Finset.univ.erase i) J ≤ LinearMap.ker ((bil τ ρ).flip v) :=
    Submodule.map₂_le.2 fun m hm n _ => by
      show bil τ ρ (m ⊗ₜ n) v = 0
      rw [bil_tmul]
      have hmem := (GlobalTheory.T.twistedDual_regularForms_finiteCover ℂ F K d (xv x) hc τ hτ (Finset.univ.erase i) hne (d - a) a
        (by omega) v hdeg).2 hv m hm
      rw [GlobalTheory.T.residue_functional_vanishes_on_omega_forms ℂ F d (xv x) hc.pd ρ hρ i _ hne (Finset.notMem_erase i _) _ hmem, zero_smul]
  exact h he

private theorem top_zero (hc : IsFinCover ℂ K (xv x)) {τ : DR ℂ K →ₗ[K] K} (hτ : IsTop ℂ K (xv x) τ)
    {ρ : F →ₗ[ℂ] ℂ} (hρ : IsRes ℂ (xv x) ρ) {a p : ℕ} (had : a ≤ d)
    (monoM : ∀ I I' J J' : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty → I ⊆ I' → J ⊆ J' →
      MZ F K (xv x) a I J ≤ MZ F K (xv x) a I' J')
    (monoB : ∀ s t : Finset (Fin (d + 1)), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) a ≤ omB ℂ K (rB ℂ K (xv x) t) a)
    (α : Finset (Fin (d + 1)) → DR ℂ K) (hα : α ∈ (omCx (rB ℂ K (xv x)) a).Z p)
    (J : Finset (Fin (d + 1))) (u : Finset (Fin (d + 1)) → DR ℂ K ⊗[ℂ] DR ℂ K)
    (hJ : J.Nonempty)
    (hu : u ∈ (cech fun I => MZ F K (xv x) a I J).C ((d : ℤ) - p - 1)) :
    ∑ i, bil τ ρ (deltaL ℂ _ _ u (Finset.univ.filter (· ≤ i))) (α (Finset.univ.filter (i ≤ ·))) = 0 := by
  obtain ⟨hαC, hαZ⟩ := Submodule.mem_inf.1 hα
  have hαZ' : deltaL ℂ _ _ α = 0 := LinearMap.mem_ker.1 hαZ
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => ?_
  have adj := GlobalTheory.T.cechDifferential_adjoint_cupProductPairing ℂ d _ _ (fun I => MZ F K (xv x) a I J)
    (fun I => omB ℂ K (rB ℂ K (xv x) I) a) ((bil τ ρ).compr₂ φ)
    (fun s t hs hst => monoM s t J J hs hJ hst subset_rfl) monoB
    (fun i hne e he v hv => by
      show φ (bil τ ρ e v) = 0
      rw [bil_face hc hτ hρ had i hne J he hv, map_zero])
  obtain ⟨ε, hε⟩ := adj ((d : ℤ) - p - 1)
  have h1 := hε u hu α (by
    have : (d : ℤ) - ((d : ℤ) - p - 1) - 1 = p := by ring
    rw [this]; exact hαC)
  have h2 : (cech fun I => omB ℂ K (rB ℂ K (xv x) I) a).D α = 0 := hαZ'
  rw [h2, map_zero, smul_zero] at h1
  have h3 : cupPair ((bil τ ρ).compr₂ φ) ((cech fun I => MZ F K (xv x) a I J).D u) α =
      φ (∑ i, bil τ ρ (deltaL ℂ _ _ u (Finset.univ.filter (· ≤ i))) (α (Finset.univ.filter (i ≤ ·)))) := by
    simp [cupPair, cech, map_sum]
  rw [← h3]; exact h1

end UpperTheory.Gal.productCup_of_system.RCT

open UpperTheory.Gal.productCup_of_system.RCT in
theorem UpperTheory.Gal.productCup_of_system.rCupTop_of :
    WdUni → GoodZ → RCupTop := by
  intro hW hG F K _ _ _ _ _ _ d x hc τ hτ ρ hρ a p had t ht α hα
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 ht
  have hgood := hG F K d x hc a
  have monoM : ∀ I I' J J' : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty → I ⊆ I' → J ⊆ J' →
      MZ F K (xv x) a I J ≤ MZ F K (xv x) a I' J' := hgood.1.monoM
  have monoB := hgood.2.2
  have hU := fun I J => hW (Fin (d + 1)) (Fin (d + 1)) (DR ℂ K ⊗[ℂ] DR ℂ K) (fun _ => 1) y I J
  have hs : ∀ s, y s ∈ (if (s.card : ℤ) = ((d : ℤ) + 2 - 1) then mixF (sysZ K x a).M s else ⊥ :
      Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K)) := fun s => (Submodule.mem_pi.1 hy) s (Set.mem_univ _)
  have hy0 : ∀ I J : Finset (Fin (d + 1)), ¬ (I.Nonempty ∧ J.Nonempty ∧ I.card + J.card = d + 1) →
      y (uni I J) = 0 := by
    intro I J hn
    obtain ⟨e1, e2, e3, -⟩ := (hU I J).2
    have h := hs (uni I J)
    rw [e3] at h
    by_cases hcd : (((I.card + J.card : ℕ)) : ℤ) = (d : ℤ) + 2 - 1
    · rw [if_pos hcd, mixF, e1, e2, if_neg (fun hh => hn ⟨hh.1, hh.2, by omega⟩)] at h
      exact (Submodule.mem_bot ℂ).1 h
    · rw [if_neg hcd] at h
      exact (Submodule.mem_bot ℂ).1 h
  have hy1 : ∀ I J : Finset (Fin (d + 1)), y (uni I J) ∈ MZ F K (xv x) a I J := by
    intro I J
    by_cases hn : I.Nonempty ∧ J.Nonempty ∧ I.card + J.card = d + 1
    · obtain ⟨e1, e2, e3, -⟩ := (hU I J).2
      have h := hs (uni I J)
      rw [e3, if_pos (by omega), mixF, e1, e2, if_pos ⟨hn.1, hn.2.1⟩] at h
      exact h
    · rw [hy0 I J hn]; exact Submodule.zero_mem _
  have hα0 : ∀ s : Finset (Fin (d + 1)), s.card ≠ p + 1 → α s = 0 := by
    intro s hsc
    have h : α s ∈ (if s.Nonempty ∧ (s.card : ℤ) = (p : ℤ) + 1 then omB ℂ K (rB ℂ K (xv x) s) a else ⊥ :
        Submodule ℂ (DR ℂ K)) := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hα).1) s (Set.mem_univ _)
    rw [if_neg (fun hh => hsc (by omega))] at h
    exact (Submodule.mem_bot ℂ).1 h
  refine Submodule.mem_map.2 ⟨fun J' => ∑ i, ((-1 : ℤ) ^ (Finset.univ.filter (· ≤ i)).card) •
    bil τ ρ (y (uni (Finset.univ.filter (· ≤ i)) J')) (α (Finset.univ.filter (i ≤ ·))), ?_, ?_⟩
  · refine Submodule.mem_pi.2 fun J' _ => ?_
    show _ ∈ (if J'.Nonempty ∧ (J'.card : ℤ) = (p : ℤ) - 1 + 1 then omB ℂ K (rB ℂ K (xv x) J') a else ⊥ :
      Submodule ℂ (DR ℂ K))
    split_ifs with hJ
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (bil_mem τ ρ (hy1 _ _) _)
    · refine (Submodule.mem_bot ℂ).2 (Finset.sum_eq_zero fun i _ => ?_)
      have hcf := card_filters i
      by_cases h2 : (Finset.univ.filter (i ≤ ·)).card = p + 1
      · rw [hy0 _ J' ?_, map_zero, LinearMap.zero_apply, smul_zero]
        rintro ⟨-, hJn, hcard⟩
        exact hJ ⟨hJn, by omega⟩
      · rw [hα0 _ h2, map_zero, smul_zero]
  · funext J
    have hD : ∀ i, (sysZ K x a).mix.D y (uni (Finset.univ.filter (· ≤ i)) J) =
        deltaL ℂ _ _ (fun b' => y (uni b' J)) (Finset.univ.filter (· ≤ i)) +
        ((-1 : ℤ) ^ (Finset.univ.filter (· ≤ i)).card) •
          deltaL ℂ _ _ (fun L' => y (uni (Finset.univ.filter (· ≤ i)) L')) J := by
      intro i
      have h := (hU (Finset.univ.filter (· ≤ i)) J).1
      refine Eq.trans h ?_
      rw [wd_one, wd_one]
    have hI : ∑ i, bil τ ρ (deltaL ℂ _ _ (fun b' => y (uni b' J)) (Finset.univ.filter (· ≤ i)))
        (α (Finset.univ.filter (i ≤ ·))) = 0 := by
      by_cases hJ : J.Nonempty ∧ J.card = p + 1
      · refine top_zero hc hτ hρ had monoM monoB α hα J _ hJ.1 ?_
        refine Submodule.mem_pi.2 fun s _ => ?_
        show _ ∈ (if s.Nonempty ∧ (s.card : ℤ) = (d : ℤ) - p - 1 + 1 then MZ F K (xv x) a s J else ⊥ :
          Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K))
        split_ifs with hsc
        · exact hy1 s J
        · exact (Submodule.mem_bot ℂ).2 (hy0 s J fun hh => hsc ⟨hh.1, by omega⟩)
      · refine Finset.sum_eq_zero fun i _ => ?_
        have hcf := card_filters i
        by_cases h2 : (Finset.univ.filter (i ≤ ·)).card = p + 1
        · have hz : deltaL ℂ _ _ (fun b' => y (uni b' J)) (Finset.univ.filter (· ≤ i)) = 0 := by
            show ∑ s ∈ Finset.univ.filter (· ≤ i), GlobalTheory.cubeSign (Finset.univ.filter (· ≤ i)) s •
              y (uni ((Finset.univ.filter (· ≤ i)).erase s) J) = 0
            refine Finset.sum_eq_zero fun s hs' => ?_
            rw [hy0 _ J ?_, smul_zero]
            rintro ⟨-, hJn, hcard⟩
            rw [Finset.card_erase_of_mem hs'] at hcard
            have := Finset.card_pos.2 ⟨s, hs'⟩
            exact hJ ⟨hJn, by omega⟩
          rw [hz, map_zero, LinearMap.zero_apply]
        · rw [hα0 _ h2, map_zero]
    have hB : ∀ i, bil τ ρ (((-1 : ℤ) ^ (Finset.univ.filter (· ≤ i)).card) •
          deltaL ℂ _ _ (fun L' => y (uni (Finset.univ.filter (· ≤ i)) L')) J) (α (Finset.univ.filter (i ≤ ·))) =
        ∑ j ∈ J, GlobalTheory.cubeSign J j • (((-1 : ℤ) ^ (Finset.univ.filter (· ≤ i)).card) •
          bil τ ρ (y (uni (Finset.univ.filter (· ≤ i)) (J.erase j))) (α (Finset.univ.filter (i ≤ ·)))) := by
      intro i
      show (bil τ ρ).flip _ (((-1 : ℤ) ^ (Finset.univ.filter (· ≤ i)).card) •
        ∑ j ∈ J, GlobalTheory.cubeSign J j • y (uni (Finset.univ.filter (· ≤ i)) (J.erase j))) = _
      simp only [Units.smul_def, map_zsmul, map_sum, LinearMap.flip_apply, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    show ∑ j ∈ J, GlobalTheory.cubeSign J j • ∑ i, ((-1 : ℤ) ^ (Finset.univ.filter (· ≤ i)).card) •
        bil τ ρ (y (uni (Finset.univ.filter (· ≤ i)) (J.erase j))) (α (Finset.univ.filter (i ≤ ·))) =
      resP (DR ℂ K) ρ (∑ i, muP F K τ ((sysZ K x a).mix.D y (uni (Finset.univ.filter (· ≤ i)) J))
        (α (Finset.univ.filter (i ≤ ·))))
    have hR : resP (DR ℂ K) ρ (∑ i, muP F K τ ((sysZ K x a).mix.D y (uni (Finset.univ.filter (· ≤ i)) J))
        (α (Finset.univ.filter (i ≤ ·)))) =
        ∑ i, bil τ ρ ((sysZ K x a).mix.D y (uni (Finset.univ.filter (· ≤ i)) J))
          (α (Finset.univ.filter (i ≤ ·))) := map_sum _ _ _
    rw [hR]
    simp only [hD, map_add, LinearMap.add_apply, Finset.sum_add_distrib, hI, zero_add, hB]
    rw [Finset.sum_comm]
    simp only [Finset.smul_sum]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PRegLat
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section
variable {F V V' : Type} [Field F] [Algebra ℂ F] [AddCommGroup V] [Module F V] [Module ℂ V]
  [IsScalarTower ℂ F V] [AddCommGroup V'] [Module F V'] [Module ℂ V'] [IsScalarTower ℂ F V']

private lemma actF_tmul (a b : F) (v : V) (v' : V') :
    actF F V V' (a ⊗ₜ b) (v ⊗ₜ v') = (a • v) ⊗ₜ (b • v') := by
  simp [actF, Module.endTensorEndAlgHom_apply]

private noncomputable def Ph (ψ : V →ₗ[F] F) (ψ' : V' →ₗ[F] F) : V ⊗[ℂ] V' →ₗ[ℂ] F ⊗[ℂ] F :=
  TensorProduct.map (ψ.restrictScalars ℂ) (ψ'.restrictScalars ℂ)

private lemma Ph_tmul (ψ : V →ₗ[F] F) (ψ' : V' →ₗ[F] F) (a : V) (b : V') :
    Ph ψ ψ' (a ⊗ₜ b) = ψ a ⊗ₜ ψ' b := rfl

private lemma Ph_act (ψ : V →ₗ[F] F) (ψ' : V' →ₗ[F] F) (s : F ⊗[ℂ] F) (t : V ⊗[ℂ] V') :
    Ph ψ ψ' (actF F V V' s t) = s * Ph ψ ψ' t := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, add_mul, ha, hb]
  | tmul a b =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add c e hc he => simp only [map_add, mul_add, hc, he]
    | tmul c e => simp [actF_tmul, Ph_tmul]

private lemma Ph_lmul (ψ : V →ₗ[F] F) (ψ' : V' →ₗ[F] F) (t : V ⊗[ℂ] V') :
    Algebra.TensorProduct.lmul' ℂ (Ph ψ ψ' t) = ψ' (ctrF V' ψ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add c e hc he => simp only [map_add, hc, he]
  | tmul c e => simp [Ph_tmul, ctrF]

variable {A A' : Subalgebra ℂ F} {M : Submodule ℂ V} {M' : Submodule ℂ V'}

private lemma Ph_mem {ψ : V →ₗ[F] F} {ψ' : V' →ₗ[F] F} (h : ∀ m ∈ M, ψ m ∈ A) (h' : ∀ m ∈ M', ψ' m ∈ A')
    {t : V ⊗[ℂ] V'} (ht : t ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') :
    Ph ψ ψ' t ∈ (Algebra.TensorProduct.map A.val A'.val).range := by
  have key : Submodule.map₂ (TensorProduct.mk ℂ V V') M M' ≤
      (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range).comap (Ph ψ ψ') := by
    refine Submodule.map₂_le.2 fun m hm m' hm' => ?_
    exact ⟨(⟨ψ m, h m hm⟩ : A) ⊗ₜ (⟨ψ' m', h' m' hm'⟩ : A'), by simp [Ph_tmul]⟩
  exact key ht

private lemma act_mem (hA : ∀ a ∈ A, ∀ m ∈ M, a • m ∈ M) (hA' : ∀ a ∈ A', ∀ m ∈ M', a • m ∈ M')
    {v : V} {v' : V'} (hv : v ∈ M) (hv' : v' ∈ M') {s : F ⊗[ℂ] F}
    (hs : s ∈ (Algebra.TensorProduct.map A.val A'.val).range) :
    actF F V V' s (v ⊗ₜ v') ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M' := by
  obtain ⟨r, rfl⟩ := hs
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a a' =>
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      Subalgebra.coe_val, actF_tmul]
    exact Submodule.apply_mem_map₂ _ (hA _ a.2 _ hv) (hA' _ a'.2 _ hv')
  | add x y hx hy =>
    rw [map_add, map_add, LinearMap.add_apply]
    exact add_mem hx hy

private lemma decomp {n n' : ℕ} {v : Fin n → V} {φ : Fin n → V →ₗ[F] F} {v' : Fin n' → V'}
    {φ' : Fin n' → V' →ₗ[F] F} (h : ∀ m ∈ M, m = ∑ k, φ k m • v k) (h' : ∀ m ∈ M', m = ∑ k, φ' k m • v' k)
    {t : V ⊗[ℂ] V'} (ht : t ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') :
    t = ∑ k, ∑ l, actF F V V' (Ph (φ k) (φ' l) t) (v k ⊗ₜ v' l) := by
  rw [Submodule.map₂_eq_span_image2] at ht
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨a, ha, b, hb, rfl⟩ := ht
    simp only [TensorProduct.mk_apply, Ph_tmul, actF_tmul]
    conv_lhs => rw [h a ha, h' b hb]
    simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum]
    rw [Finset.sum_comm]
  | zero => simp
  | add a b _ _ ha hb =>
    conv_lhs => rw [ha, hb]
    simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib]
  | smul c a _ ha =>
    conv_lhs => rw [ha]
    simp only [map_smul, LinearMap.smul_apply, Finset.smul_sum]

private lemma Ph_sm {ψ : V →ₗ[F] F} {ψ' : V' →ₗ[F] F} (h : ∀ m ∈ M, ψ m ∈ A) (h' : ∀ m ∈ M', ψ' m ∈ A')
    {T : Set (F ⊗[ℂ] F)} {t : V ⊗[ℂ] V'}
    (ht : t ∈ sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') T) :
    Ph ψ ψ' t ∈ sm (Algebra.lmul ℂ (F ⊗[ℂ] F))
      (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range) T := by
  have hle : sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ V V') M M') T ≤
      (sm (Algebra.lmul ℂ (F ⊗[ℂ] F))
        (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range) T).comap (Ph ψ ψ') := by
    unfold sm
    refine iSup₂_le fun r hr => ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [Submodule.mem_comap, Ph_act]
    exact Submodule.mem_iSup_of_mem r (Submodule.mem_iSup_of_mem hr ⟨_, Ph_mem h h' hu, by simp⟩)
  exact hle ht

private lemma act_sm (hA : ∀ a ∈ A, ∀ m ∈ M, a • m ∈ M) (hA' : ∀ a ∈ A', ∀ m ∈ M', a • m ∈ M')
    {v : V} {v' : V'} (hv : v ∈ M) (hv' : v' ∈ M') {T : Set (F ⊗[ℂ] F)} {s : F ⊗[ℂ] F}
    (hs : s ∈ sm (Algebra.lmul ℂ (F ⊗[ℂ] F))
      (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range) T) :
    actF F V V' s (v ⊗ₜ v') ∈ sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') T := by
  let L : (F ⊗[ℂ] F) →ₗ[ℂ] V ⊗[ℂ] V' :=
    (LinearMap.applyₗ (v ⊗ₜ v')) ∘ₗ (actF F V V').toLinearMap
  have hle : sm (Algebra.lmul ℂ (F ⊗[ℂ] F))
      (Subalgebra.toSubmodule (Algebra.TensorProduct.map A.val A'.val).range) T ≤
      (sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ V V') M M') T).comap L := by
    unfold sm
    refine iSup₂_le fun r hr => ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [Submodule.mem_comap]
    refine Submodule.mem_iSup_of_mem r (Submodule.mem_iSup_of_mem hr
      ⟨actF F V V' u (v ⊗ₜ v'), act_mem hA hA' hv hv' hu, ?_⟩)
    simp [L, Module.End.mul_apply]
  exact hle hs

end

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.regLat_of :
    Reg0 → Ker0 → RegLat := by
  intro h0 hK F _ _ d x hx V V' _ _ _ _ _ _ _ _ I J M M' hL hL' j hjI hjJ
  obtain ⟨hA, n, v, φ, hv, hφ, hdec⟩ := hL
  obtain ⟨hA', n', v', φ', hv', hφ', hdec'⟩ := hL'
  have back : ∀ (T : Set (F ⊗[ℂ] F)) (t : V ⊗[ℂ] V'), t ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) M M' →
      (∀ k l, Ph (φ k) (φ' l) t ∈ sm (Algebra.lmul ℂ (F ⊗[ℂ] F)) (Subalgebra.toSubmodule (R0 x I J)) T) →
      t ∈ sm (actF F V V') (Submodule.map₂ (TensorProduct.mk ℂ _ _) M M') T := by
    intro T t ht h
    rw [decomp hdec hdec' ht]
    exact Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun l _ =>
      act_sm hA hA' (hv k) (hv' l) (h k l)
  refine ⟨?_, ?_⟩
  · intro k m hm hk
    refine back _ m hm fun a b => ?_
    refine h0 F d x hx I J j hjI hjJ k _ (Ph_mem (hφ a) (hφ' b) hm) ?_
    have := Ph_sm (ψ := φ a) (ψ' := φ' b) (fun m hm => hφ a m hm) (fun m hm => hφ' b m hm) hk
    rw [Ph_act] at this
    exact this
  · intro m hm hψ
    refine back _ m hm fun a b => ?_
    refine hK F d x hx I J j hjI hjJ _ (Ph_mem (hφ a) (hφ' b) hm) ?_
    rw [Ph_lmul, hψ, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.RatioMemRB
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma omB_smul_mem {K : Type} [Field K] [Algebra ℂ K] (B : Subalgebra ℂ K) (q : ℕ) {b : K} (hb : b ∈ B)
    {y : DR ℂ K} (hy : y ∈ omB ℂ K B q) : b • y ∈ omB ℂ K B q := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b', hb', v, hv, rfl⟩ := hz
    apply Submodule.subset_span
    exact ⟨b * b', B.mul_mem hb hb', v, hv, by rw [smul_smul]⟩
  | zero => simp
  | add u w _ _ hu hw =>
    rw [smul_add]
    exact Submodule.add_mem _ hu hw
  | smul c u _ hu =>
    rw [smul_comm]
    exact Submodule.smul_mem _ c hu

private lemma ratio_mem_rB {F : Type} (K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K]
    [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) (i j : Fin (d + 1)) :
    algebraMap F K (x j / x i) ∈ rB ℂ K x {i} := by
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  have h : x j / x i ∈ rA ℂ x {i} := Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩
  exact isIntegral_algebraMap (x := (⟨x j / x i, h⟩ : rA ℂ x {i}))

private lemma omG_ratio {F : Type} [Field F] {d : ℕ} (x : Fin (d + 1) → Fˣ) (i j : Fin (d + 1)) (N : ℕ) :
    ((x j : F) / x i) ^ (N + d + 1) * ((x i : F) / x j) ^ N * omG x j = omG x i := by
  have hi : (x i : F) ≠ 0 := (x i).ne_zero
  have hj : (x j : F) ≠ 0 := (x j).ne_zero
  have h : omG x j = omG x i * ((x i : F) / x j) ^ (d + 1) := by
    simp only [omG]
    rw [show ((x i : F) / x j) ^ (d + 1) = ∏ _l : Fin (d + 1), ((x i : F) / x j) by simp [div_pow],
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    field_simp
  rw [h, ← inv_div (x j : F) (x i : F)]
  have ha : (x j : F) / x i ≠ 0 := div_ne_zero hj hi
  generalize (x j : F) / x i = a at ha ⊢
  rw [inv_pow, inv_pow]
  field_simp
  ring

private lemma pair_prod {F : Type} [Field F] {d : ℕ} (x : Fin (d + 1) → Fˣ) (i j : Fin (d + 1)) :
    (∏ l ∈ ({i, j} : Finset (Fin (d + 1))), (x l : F) / x i) = (x j : F) / x i := by
  by_cases h : i = j
  · subst h
    simp
  · rw [Finset.prod_pair h, div_self (x i).ne_zero, one_mul]

private theorem key_lemma' {K : Type} [Field K] [Algebra ℂ K] (s t : K) (y z : DR ℂ K) :
    actZ K (s ⊗ₜ[ℂ] t) (y ⊗ₜ[ℂ] z) = (s • y) ⊗ₜ[ℂ] (t • z) := by
  simp [actZ, Module.endTensorEndAlgHom, Module.endTensorEndAlgHom_apply]

private lemma key {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]
    {d : ℕ} (x : Fin (d + 1) → Fˣ) (hc : IsFinCover ℂ K (xv x))
    (hmono : ∀ (q : ℕ) (s t : Finset (Fin (d + 1))), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) q ≤ omB ℂ K (rB ℂ K (xv x) t) q) (a : ℕ) (i j : Fin (d + 1))
    (m : DR ℂ K ⊗[ℂ] DR ℂ K) (hm : m ∈ MZ F K (xv x) a {j} {j}) :
    ∃ N0 : ℕ, ∀ N, N0 ≤ N → actZ K ((algebraMap F K ((x j : F) / x i) ^ (N + d + 1)) ⊗ₜ[ℂ]
      (algebraMap F K ((x i : F) / x j) ^ N)) m ∈ MZ F K (xv x) a {i} {j} := by
  have hu : algebraMap F K ((x j : F) / x i) ∈ rB ℂ K (xv x) {i} := ratio_mem_rB K (xv x) i j
  have hv : algebraMap F K ((x i : F) / x j) ∈ rB ℂ K (xv x) {j} := ratio_mem_rB K (xv x) j i
  have gen : ∀ y ∈ omB ℂ K (rB ℂ K (xv x) {j}) (d - a), ∀ z ∈ omB ℂ K (rB ℂ K (xv x) {j}) a,
      ∃ N0 : ℕ, ∀ N, N0 ≤ N → actZ K ((algebraMap F K ((x j : F) / x i) ^ (N + d + 1)) ⊗ₜ[ℂ]
        (algebraMap F K ((x i : F) / x j) ^ N)) (TensorProduct.mk ℂ (DR ℂ K) (DR ℂ K) y z) ∈
          MZ F K (xv x) a {i} {j} := by
    intro y hy z hz
    have hy' : y ∈ omB ℂ K (rB ℂ K (xv x) {i, j}) (d - a) :=
      hmono (d - a) {j} {i, j} (Finset.singleton_nonempty j)
        (Finset.singleton_subset_iff.mpr (by simp)) hy
    obtain ⟨N1, hN1⟩ := (GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul ℂ F K d (xv x) hc {i, j} i (by simp) (d - a) y).mp hy'
    have hN1' : algebraMap F K ((x j : F) / x i) ^ N1 • y ∈ omB ℂ K (rB ℂ K (xv x) {i}) (d - a) := by
      rw [← pair_prod x i j]
      exact hN1
    refine ⟨N1, fun N hN => ?_⟩
    rw [TensorProduct.mk_apply, key_lemma']
    have h1 : algebraMap F K ((x j : F) / x i) ^ (N + d + 1) • y ∈
        omB ℂ K (rB ℂ K (xv x) {i}) (d - a) := by
      have e : N + d + 1 = (N + d + 1 - N1) + N1 := by omega
      rw [e, pow_add, ← smul_smul]
      exact omB_smul_mem _ _ (pow_mem hu _) hN1'
    have h2 : algebraMap F K ((x i : F) / x j) ^ N • z ∈ omB ℂ K (rB ℂ K (xv x) {j}) a :=
      omB_smul_mem _ _ (pow_mem hv _) hz
    exact Submodule.apply_mem_map₂ _ h1 h2
  unfold MZ at hm
  rw [Submodule.map₂_eq_span_image2] at hm
  induction hm using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨y, hy, z, hz, rfl⟩ := hw
    exact gen y hy z hz
  | zero => exact ⟨0, fun N _ => by simp⟩
  | add w w' _ _ h1 h2 =>
    obtain ⟨N1, h1⟩ := h1
    obtain ⟨N2, h2⟩ := h2
    exact ⟨max N1 N2, fun N hN => by
      rw [map_add]
      exact Submodule.add_mem _ (h1 N (le_of_max_le_left hN)) (h2 N (le_of_max_le_right hN))⟩
  | smul c w _ h =>
    obtain ⟨N1, h⟩ := h
    exact ⟨N1, fun N hN => by
      rw [map_smul]
      exact Submodule.smul_mem _ c (h N hN)⟩

theorem UpperTheory.Gal.productCup_of_system.idIJ_of :
    IdJ → ActsLin → GoodZ → IdIJ := by
  intro hJ hL hG F K _ _ _ _ _ _ d x hc τ hτ a ha i j
  obtain ⟨m, hm, hact⟩ := hJ F K d x hc τ hτ a ha j
  have hmono : ∀ (q : ℕ) (s t : Finset (Fin (d + 1))), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) q ≤ omB ℂ K (rB ℂ K (xv x) t) q :=
    fun q => (hG F K d x hc q).2.2
  obtain ⟨N0, hN0⟩ := key x hc hmono a i j m hm
  refine ⟨_, hN0 N0 le_rfl, ?_⟩
  have h2 := (hL F K d x hc τ hτ a).2.1 m _
    ((algebraMap F K ((x j : F) / x i) ^ (N0 + d + 1)) ⊗ₜ[ℂ] (algebraMap F K ((x i : F) / x j) ^ N0)) hact
  rw [Algebra.TensorProduct.lmul'_apply_tmul, ← map_pow, ← map_pow, ← map_mul, ← map_mul,
    omG_ratio] at h2
  simpa only [map_pow] using h2
end

