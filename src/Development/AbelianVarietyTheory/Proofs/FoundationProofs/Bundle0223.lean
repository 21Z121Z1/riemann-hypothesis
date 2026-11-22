import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.LocalToGlobal.Columns.PolyFn
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.SharpRestriction.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0220
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankIntertwiningMapDirectSum
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.IntertwinerSum

open Representation

variable {k G ι U W : Type} [Field k] [Group G] [Fintype ι] {V : ι → Type}
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [AddCommGroup U] [Module k U]
  [AddCommGroup W] [Module k W]

theorem finite_intertwiningMap [FiniteDimensional k U] [FiniteDimensional k W]
    (τ : Representation k G U) (σ : Representation k G W) :
    FiniteDimensional k (τ.IntertwiningMap σ) :=
  FiniteDimensional.of_injective
    ({ toFun := fun f => f.toLinearMap
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : τ.IntertwiningMap σ →ₗ[k] (U →ₗ[k] W))
    (IntertwiningMap.toLinearMap_injective τ σ)

theorem equivs_of_biproduct (ρ : ∀ i, Representation k G (V i)) (τ : Representation k G U)
    (σ : Representation k G W) (p : ∀ i, σ.IntertwiningMap (ρ i))
    (j : ∀ i, (ρ i).IntertwiningMap σ) (hsum : ∀ w, ∑ i, j i (p i w) = w)
    (hdiag : ∀ i x, p i (j i x) = x) (hoff : ∀ i i', i' ≠ i → ∀ x, p i (j i' x) = 0) :
    Nonempty (τ.IntertwiningMap σ ≃ₗ[k] ∀ i, τ.IntertwiningMap (ρ i)) ∧
      Nonempty (σ.IntertwiningMap τ ≃ₗ[k] ∀ i, (ρ i).IntertwiningMap τ) := by
  classical
  refine ⟨⟨{ toFun := fun f i => (p i).comp f
             map_add' := fun f g => ?_
             map_smul' := fun c f => ?_
             invFun := fun f => ∑ i, (j i).comp (f i)
             left_inv := fun f => ?_
             right_inv := fun f => ?_ }⟩,
          ⟨{ toFun := fun f i => f.comp (j i)
             map_add' := fun f g => rfl
             map_smul' := fun c f => rfl
             invFun := fun f => ∑ i, (f i).comp (p i)
             left_inv := fun f => ?_
             right_inv := fun f => ?_ }⟩⟩
  · funext i
    exact DFunLike.ext _ _ fun u => map_add (p i) (f u) (g u)
  · funext i
    exact DFunLike.ext _ _ fun u => map_smul (p i) c (f u)
  · refine DFunLike.ext _ _ fun u => ?_
    rw [IntertwiningMap.sum_apply]
    exact hsum (f u)
  · funext i
    refine DFunLike.ext _ _ fun u => ?_
    rw [IntertwiningMap.comp_apply, IntertwiningMap.sum_apply, map_sum]
    simp only [IntertwiningMap.comp_apply]
    rw [Finset.sum_eq_single i (fun i' _ h => hoff i i' h _) (by simp)]
    exact hdiag i _
  · refine DFunLike.ext _ _ fun w => ?_
    rw [IntertwiningMap.sum_apply]
    simp only [IntertwiningMap.comp_apply]
    rw [← map_sum, hsum]
  · funext i
    refine DFunLike.ext _ _ fun x => ?_
    rw [IntertwiningMap.comp_apply, IntertwiningMap.sum_apply]
    simp only [IntertwiningMap.comp_apply]
    rw [Finset.sum_eq_single i (fun i' _ h => by rw [hoff i' i h.symm, map_zero]) (by simp), hdiag]

theorem finrank_intertwiningMap_directSum :
    ∀ (k G ι U W : Type) [Field k] [Group G] [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] [AddCommGroup U] [Module k U] [FiniteDimensional k U] [AddCommGroup W] [Module k W] (ρ : ∀ i, Representation k G (V i)) (τ : Representation k G U) (σ : Representation k G W), Nonempty ((Representation.directSum ρ).Equiv σ) → Module.finrank k (τ.IntertwiningMap σ) = ∑ i, Module.finrank k (τ.IntertwiningMap (ρ i)) ∧ Module.finrank k (σ.IntertwiningMap τ) = ∑ i, Module.finrank k ((ρ i).IntertwiningMap τ) := by
  intro k G ι U W _ _ _ V _ _ _ _ _ _ _ _ ρ τ σ ⟨e⟩
  classical
  let p₀ : ∀ i, (Representation.directSum ρ).IntertwiningMap (ρ i) := fun i =>
    { toLinearMap := DirectSum.component k ι V i
      isIntertwining' := fun g => by
        refine LinearMap.ext fun x => ?_
        rfl }
  let j₀ : ∀ i, (ρ i).IntertwiningMap (Representation.directSum ρ) := fun i =>
    { toLinearMap := DirectSum.lof k ι V i
      isIntertwining' := fun g => by
        refine LinearMap.ext fun x => ?_
        simp [Representation.directSum] }
  have hse : ∀ x, e.symm.toIntertwiningMap (e.toIntertwiningMap x) = x :=
    fun x => e.toLinearEquiv.symm_apply_apply x
  have hes : ∀ x, e.toIntertwiningMap (e.symm.toIntertwiningMap x) = x :=
    fun x => e.toLinearEquiv.apply_symm_apply x
  obtain ⟨⟨a⟩, ⟨b⟩⟩ := equivs_of_biproduct ρ τ σ
    (fun i => (p₀ i).comp e.symm.toIntertwiningMap) (fun i => e.toIntertwiningMap.comp (j₀ i))
    (fun w => by
      simp only [IntertwiningMap.comp_apply]
      rw [← map_sum]
      have : ∀ x : ⨁ i, V i, ∑ i, j₀ i (p₀ i x) = x := fun x => DirectSum.sum_univ_of x
      rw [this, hes])
    (fun i x => by
      simp only [IntertwiningMap.comp_apply]
      rw [hse]
      exact DirectSum.component.lof_self k i x)
    (fun i i' h x => by
      simp only [IntertwiningMap.comp_apply]
      rw [hse]
      exact DirectSum.of_eq_of_ne i' i x h.symm)
  have := fun i => finite_intertwiningMap τ (ρ i)
  have := fun i => finite_intertwiningMap (ρ i) τ
  exact ⟨a.finrank_eq.trans (Module.finrank_pi_fintype k), b.finrank_eq.trans (Module.finrank_pi_fintype k)⟩

end GlobalTheory.IntertwinerSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelPrimeSplitsCompletelyInCmField
section
noncomputable section

namespace GlobalTheory.ColClassCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.SplitColumnClasses

section Descent

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {p : ℕ}

theorem unram_card_of_split (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E)
    (v : Ideal (𝓞 F)) [hv : v.IsPrime] (hpv : (p : 𝓞 F) ∈ v) :
    (p : 𝓞 F) ∉ v ^ 2 ∧ Nat.card (𝓞 F ⧸ v) = p := by
  obtain ⟨P, hP, hPl⟩ := (inferInstance : Nonempty (v.primesOver (𝓞 E)))
  have hgP : (p : 𝓞 E) ∈ P := by
    simpa using (Ideal.mem_of_liesOver P v (p : 𝓞 F)).1 hpv
  obtain ⟨hP2, hP3⟩ := GlobalTheory.LocSplit.split_prime hp h P hgP
  refine ⟨fun h2 => hP2 ?_, ?_⟩
  · have := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) h2
    rw [Ideal.map_pow, map_natCast] at this
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hPl.over.le) 2 this
  · haveI : Fact p.Prime := ⟨hp⟩
    haveI : Nontrivial (𝓞 F ⧸ v) := Ideal.Quotient.nontrivial_iff.2 hv.ne_top
    have h0 : ((p : ℕ) : 𝓞 F ⧸ v) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk v), Ideal.Quotient.eq_zero_iff_mem]
      exact hpv
    haveI : CharP (𝓞 F ⧸ v) p := (CharP.charP_iff_prime_eq_zero hp).2 h0
    have hb : Function.Bijective (ZMod.castHom (dvd_refl p) (𝓞 F ⧸ v)) := by
      refine ⟨RingHom.injective _, fun x => ?_⟩
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨m, hm⟩ := hP3 (algebraMap (𝓞 F) (𝓞 E) x)
      refine ⟨(m : ZMod p), ?_⟩
      rw [map_intCast, ← map_intCast (Ideal.Quotient.mk v), eq_comm, Ideal.Quotient.eq,
        Ideal.mem_of_liesOver P v]
      simpa using hm
    rw [← Nat.card_eq_of_bijective _ hb, Nat.card_zmod]

theorem ncard_primesOver_of_split (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 F)).ncard = Module.finrank ℚ F := by
  classical
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp'.ne_zero).mpr hp'
  have hne : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by simpa using hp.ne_zero
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  have hs := Ideal.sum_ramification_inertia (𝓞 F) ℚ F (p := Ideal.span {(p : ℤ)}) hne
  rw [← hs, ← IsDedekindDomain.coe_primesOverFinset hne, Set.ncard_coe_finset, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff hne] at hq
  haveI := hq.1
  haveI := hq.2
  have hpq : (p : 𝓞 F) ∈ q := by
    simpa using (Ideal.mem_of_liesOver q (Ideal.span {(p : ℤ)}) (p : ℤ)).1 (Ideal.mem_span_singleton_self _)
  obtain ⟨h2, hc⟩ := unram_card_of_split (E := E) hp h q hpq
  have he : (Ideal.span {(p : ℤ)}).ramificationIdx' q = 1 := by
    by_contra hne1
    refine h2 ?_
    have := (Ideal.ramificationIdx'_ne_one_iff (by
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]; simpa using hpq)).1 hne1
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem] at this
    simpa using this
  have hf : (Ideal.span {(p : ℤ)}).inertiaDeg' q = 1 := by
    have h1 := Ideal.absNorm_eq_pow_inertiaDeg' q hp
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hc] at h1
    exact (Nat.pow_right_injective hp.two_le (by simpa using h1)).symm
  rw [he, hf]

end Descent

theorem finrank_F (D : D7) : Module.finrank ℚ D.host.F = D.R.f := by
  letI := D.host.cmStar
  have h1 := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  rw [D.sp.cm.deg2, finrank_host D] at h1
  omega

theorem splitsF_of_splitsCompletely (D : D7) {p : ℕ} (h : SplitsCompletely D.host.E p) : SplitsF D p := by
  obtain ⟨hp, h⟩ := h
  rw [GlobalTheory.HostSplit.ncard_placesOver _ hp] at h
  refine ⟨?_, fun v hv => ?_⟩
  · have h1 := ncard_primesOver_of_split (F := D.host.F) hp h
    rw [← GlobalTheory.HostSplit.ncard_placesOver _ hp, finrank_F] at h1
    rw [← h1, ← Nat.card_coe_set_eq]
    rfl
  · haveI := v.isPrime
    exact (unram_card_of_split hp h v.asIdeal hv).2

theorem levelPrime_mod (D : D7) (u : D.what₂.Word) :
    (D.mem u).A.T % (D.host.QS * D.host.q * D.host.d) = 1 := by
  obtain ⟨π, -, hn, hm⟩ := D.T_norm u
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hm
  have hq8 : D.host.q % 8 = 3 := D.host.hyp.2.2.1
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hn0 : 1 ≤ D.host.QS := D.host.QS_pos
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = D.host.QS * D.host.q * D.host.d := ⟨_, rfl⟩
  have hM1 : 1 < M := by
    have h1 : 1 * 3 * 7 ≤ D.host.QS * D.host.q * D.host.d :=
      Nat.mul_le_mul (Nat.mul_le_mul hn0 (by omega)) (by omega)
    omega
  rw [← hM] at ha ⊢
  obtain ⟨G, hG⟩ : ∃ G : ℕ, G = (D.host.g 0 * D.host.g 1) ^ 2 := ⟨_, rfl⟩
  rw [← hG] at ha
  set y : D.host.E := (a : D.host.E) * G with hy
  have hyi : IsIntegral ℤ y := (RingOfIntegers.isIntegral_coe a).mul (isIntegral_natCast G)
  have hπ : (π : D.host.E) = 1 + M * y := by
    have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) ha
    simp only [map_mul, map_sub, map_one, map_natCast] at this
    rw [hy]
    push_cast at this ⊢
    linear_combination -this
  have hci : IsIntegral ℤ (D.conjF y) := hyi.map (D.conjF.toRingHom.toIntAlgHom)
  rw [← D.conjF_eq, hπ, map_add, map_mul, map_one, map_natCast] at hn
  set z : D.host.E := y + D.conjF y + M * (y * D.conjF y) with hz
  have hzi : IsIntegral ℤ z :=
    (hyi.add hci).add ((isIntegral_natCast (R := ℤ) (B := D.host.E) M).mul (hyi.mul hci))
  have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have h4 : z = algebraMap ℚ D.host.E ((((D.mem u).A.T : ℚ) - 1) / M) := by
    have hM0' : (M : D.host.E) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
    rw [map_div₀, map_sub, map_one, map_natCast, map_natCast, eq_div_iff hM0', hz]
    linear_combination hn
  rw [h4, isIntegral_algebraMap_iff (algebraMap ℚ D.host.E).injective] at hzi
  obtain ⟨n, hn'⟩ := IsIntegrallyClosed.isIntegral_iff.1 hzi
  have h5 : (((D.mem u).A.T : ℤ) : ℚ) = ((1 + M * n : ℤ) : ℚ) := by
    have : (n : ℚ) = (((D.mem u).A.T : ℚ) - 1) / M := by simpa using hn'
    push_cast
    rw [this]
    field_simp
    ring
  have h6 : ((D.mem u).A.T : ℤ) = 1 + M * n := by exact_mod_cast h5
  have h7 : (((D.mem u).A.T % M : ℕ) : ℤ) = 1 := by
    rw [Int.natCast_mod, h6, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hM1)
  exact_mod_cast h7

theorem levelPrime_splitsCompletely_in_cmField (D : D7) (u : D.what₂.Word) : SplitsCompletely D.host.E (D.mem u).A.T :=
  ⟨(D.mem u).A.T_prime,
    (GlobalTheory.HostSplit.split_of_one_mod D.R D.host _ (D.mem u).A.T_prime (levelPrime_mod D u)).1⟩

theorem split_g_iff (D : D7) (i : Fin 2) :
    SplitsF D (D.host.g i) ↔ SplitsCompletely D.host.E (D.host.g i) :=
  ⟨fun _ => splitsCompletely_g D i, splitsF_of_splitsCompletely D⟩

theorem split_T_iff (D : D7) (u : D.what₂.Word) :
    SplitsF D (D.mem u).A.T ↔ SplitsCompletely D.host.E (D.mem u).A.T :=
  ⟨fun _ => levelPrime_splitsCompletely_in_cmField D u, splitsF_of_splitsCompletely D⟩

def BothBig (D : D7) : Prop := ∀ i : Fin 2, 2 * D.R.f * D.R.k + 1 < D.host.g i

theorem gBig_iff (D : D7) : GBig D ↔ ∃ i : Fin 2, 2 * D.R.f * D.R.k + 1 < D.host.g i :=
  exists_congr fun _ => by omega

theorem gBig_of_bothBig {D : D7} (h : BothBig D) : GBig D := (gBig_iff D).2 ⟨0, h 0⟩

theorem bothBig_all (D : D7) : BothBig D := by
  intro i
  have hc := D.ntypes.g_cond i
  have hg := (D.host.g_prime i).two_le
  have h3 : D.host.QS * D.host.q * D.host.d ≤ D.host.g i := by
    by_contra h
    rw [Nat.mod_eq_of_lt (by omega)] at hc
    omega
  obtain ⟨hq, hd⟩ := D.host.qd_big
  have hn : 1 ≤ D.host.QS := D.host.QS_pos
  have hf : D.R.f ≤ D.R.k := D.R.f_le_k
  have hm := D.R.two_le_m
  have ht := D.R.rank_add_five_le
  have hr : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
  have h4 : D.R.f * D.R.k ≤ D.R.t * D.R.r := Nat.mul_le_mul (by omega) hr
  have h5 : D.host.q ≤ D.host.QS * D.host.q * D.host.d :=
    calc D.host.q = 1 * D.host.q * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ hn) (by omega)
  rw [mul_assoc] at hq ⊢
  omega

theorem gBig_iff_bothBig (D : D7) : GBig D ↔ BothBig D :=
  ⟨fun _ => bothBig_all D, gBig_of_bothBig⟩

theorem classCount_iff (D : D7) (L : LevelData D) (u : D.what₂.Word) :
    ClassCount D L u ↔
      (Nat.card ((D.mem u).C.cls 0) : ℝ) =
        massI D D.R.k * idxPi D (D.host.g 0) (D.host.g 1) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f := by
  unfold ClassCount
  rw [card_colClassSet]

def ColumnClassNumberAt (D : D7) (L : LevelData D) : Prop :=
  ∀ u : D.what₂.Word, (∀ i : Fin 2, 2 * D.R.f * D.R.k + 1 < D.host.g i) →
    (∀ i : Fin 2, SplitsCompletely D.host.E (D.host.g i)) →
    SplitsCompletely D.host.E (D.mem u).A.T → ClassCount D L u

theorem first_iff (D : D7) (L : LevelData D) :
    ClassNumberFormula₂ D L ↔ ∀ u : D.what₂.Word, (∃ i : Fin 2, 2 * D.R.f * D.R.k + 1 < D.host.g i) →
      (∀ i : Fin 2, SplitsCompletely D.host.E (D.host.g i)) →
      SplitsCompletely D.host.E (D.mem u).A.T → ClassCount D L u := by
  unfold ClassNumberFormula₂
  simp only [gBig_iff, split_g_iff, split_T_iff, classCount_iff]
  exact ⟨fun h u h1 h2 h3 => h h1 h2 u h3, fun h h1 h2 u h3 => h u h1 h2 h3⟩

theorem at_iff (D : D7) (L : LevelData D) : ColumnClassNumberAt D L ↔ (BothBig D → ClassNumberFormula₂ D L) := by
  rw [first_iff]
  exact ⟨fun h hb u _ h2 h3 => h u hb h2 h3, fun h u hb h2 h3 => h hb u ⟨0, hb 0⟩ h2 h3⟩

theorem iff_of_size {D : D7} (hs : GBig D → BothBig D) (L : LevelData D) :
    ClassNumberFormula₂ D L ↔ ColumnClassNumberAt D L := by
  rw [at_iff]
  exact ⟨fun h _ => h, fun h hg => h (hs hg) hg⟩

theorem full_at (D : D7) (L : LevelData D) : ClassNumberFormula₂ D L ↔ ColumnClassNumberAt D L :=
  iff_of_size (gBig_iff_bothBig D).1 L

theorem full : ColumnClassNumber ↔ ∀ (D : D7) (L : LevelData D), ClassNumberFormula₂ D L :=
  forall_congr' fun D => forall_congr' fun L => (full_at D L).symm

end GlobalTheory.ColClassCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyDirectSumEquivOfFinrankLe
section
open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory

theorem directSum_eq_zero_of_toModule_eq_zero {k G ι W : Type} [Field k] [Group G] [DecidableEq ι]
    {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [AddCommGroup W] [Module k W] (ρ : ∀ i, Representation k G (V i)) (σ : Representation k G W)
    (hirr : ∀ i, (ρ i).IsIrreducible)
    (hdis : ∀ i j, i ≠ j → ∀ φ : (ρ i).IntertwiningMap (ρ j), φ = 0)
    (Φ : (Representation.directSum ρ).IntertwiningMap σ)
    (hΦ : ∀ i (v : V i), Φ (DirectSum.lof k ι V i v) = 0 → v = 0) (s : Finset ι) :
    ∀ x : ⨁ i, V i, (∀ j, j ∉ s → x j = 0) → Φ x = 0 → x = 0 := by
  have hρ : ∀ g (x : ⨁ i, V i) j, (Representation.directSum ρ g x) j = ρ j g (x j) := by
    intro g x j
    rfl
  induction s using Finset.induction_on with
  | empty =>
    intro x hx _
    ext j
    exact hx j (Finset.notMem_empty j)
  | insert i t hi ih =>
    let K : Submodule k (⨁ i, V i) :=
      { carrier := {x | (∀ j, j ∉ insert i t → x j = 0) ∧ Φ x = 0}
        add_mem' := fun {a b} ha hb => ⟨fun j hj => by
          rw [DirectSum.add_apply, ha.1 j hj, hb.1 j hj, add_zero],
          by rw [map_add, ha.2, hb.2, add_zero]⟩
        zero_mem' := ⟨fun j _ => rfl, map_zero Φ⟩
        smul_mem' := fun c a ha => ⟨fun j hj => by
          rw [DirectSum.smul_apply, ha.1 j hj, smul_zero],
          by rw [map_smul, ha.2, smul_zero]⟩ }
    have hK : ∀ g x, x ∈ K → Representation.directSum ρ g x ∈ K := by
      intro g x hx
      refine ⟨fun j hj => ?_, ?_⟩
      · rw [hρ, hx.1 j hj, map_zero]
      · rw [Φ.isIntertwining, hx.2, map_zero]
    have hz : ∀ x ∈ K, x i = 0 → x = 0 := by
      intro x hx h0
      refine ih x (fun j hj => ?_) hx.2
      by_cases hji : j = i
      · subst hji; exact h0
      · exact hx.1 j (by simp [hji, hj])
    let p : K →ₗ[k] V i := DirectSum.component k ι V i ∘ₗ K.subtype
    have hp : ∀ x : K, p x = x.1 i := fun x => rfl
    have hinj : Function.Injective p := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      exact Subtype.ext (hz x.1 x.2 hx)
    let R : Subrepresentation (ρ i) :=
      { toSubmodule := LinearMap.range p
        apply_mem_toSubmodule := by
          rintro g _ ⟨x, rfl⟩
          exact ⟨⟨_, hK g x.1 x.2⟩, rfl⟩ }
    intro x hx1 hx2
    have hx : x ∈ K := ⟨hx1, hx2⟩
    have := hirr i
    rcases eq_bot_or_eq_top R with hR | hR
    · apply hz x hx
      have : x i ∈ R.toSubmodule := ⟨⟨x, hx⟩, rfl⟩
      rw [hR] at this
      exact this
    · have hsurj : Function.Surjective p := by
        intro v
        have : v ∈ R.toSubmodule := by rw [hR]; trivial
        exact this
      let e := LinearEquiv.ofBijective p ⟨hinj, hsurj⟩
      have he : ∀ y : K, e.symm (y.1 i) = y := fun y => e.symm_apply_apply y
      have hoff : ∀ j, j ≠ i → x j = 0 := by
        intro j hj
        let ψ : (ρ i).IntertwiningMap (ρ j) :=
          LinearMap.intertwiningMap_of_isIntertwiningMap (ρ i) (ρ j)
            (DirectSum.component k ι V j ∘ₗ K.subtype ∘ₗ e.symm.toLinearMap) (by
              intro g v
              obtain ⟨y, rfl⟩ := hsurj v
              have h1 := he ⟨_, hK g y.1 y.2⟩
              have h2 := he y
              change ((e.symm (ρ i g (y.1 i)) : K) : ⨁ i, V i) j
                = ρ j g (((e.symm (y.1 i) : K) : ⨁ i, V i) j)
              rw [h2, ← hρ, h1]
              rfl)
        have h0 : ψ = 0 := hdis i j (Ne.symm hj) ψ
        have h3 : ψ (x i) = x j := by
          change ((e.symm (x i) : K) : ⨁ i, V i) j = x j
          rw [he ⟨x, hx⟩]
        rw [← h3, h0]
        rfl
      have hxe : x = DirectSum.lof k ι V i (x i) := by
        ext j
        by_cases hj : j = i
        · subst hj
          simp [DirectSum.lof_eq_of]
        · rw [hoff j hj, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hj]
      apply hz x hx
      apply hΦ
      rw [← hxe]
      exact hx2

theorem nonempty_directSum_equiv_of_finrank_le : ∀ (k G ι W : Type) [Field k] [Group G] [Finite ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] [AddCommGroup W] [Module k W] [FiniteDimensional k W] (ρ : ∀ i, Representation k G (V i)) (σ : Representation k G W), (∀ i, (ρ i).IsIrreducible) → (∀ i j, i ≠ j → ∀ φ : (ρ i).IntertwiningMap (ρ j), φ = 0) → (∀ i, ∃ φ : (ρ i).IntertwiningMap σ, φ ≠ 0) → Module.finrank k W ≤ Module.finrank k (⨁ i, V i) → Nonempty ((Representation.directSum ρ).Equiv σ) := by
  intro k G ι W _ _ _ V _ _ _ _ _ _ ρ σ hirr hdis hex hle
  classical
  have := Fintype.ofFinite ι
  choose φ hφ using hex
  let Φ : (Representation.directSum ρ).IntertwiningMap σ :=
    ⟨DirectSum.toModule k ι W (fun i => (φ i).toLinearMap), fun g => by
      ext i v
      simp [(φ i).isIntertwining]⟩
  have hinj : Function.Injective Φ.toLinearMap := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine directSum_eq_zero_of_toModule_eq_zero ρ σ hirr hdis Φ ?_ Finset.univ x
      (fun j hj => absurd (Finset.mem_univ j) hj) hx
    intro i v hv
    have := hirr i
    have hi := (Representation.IsIrreducible.injective_or_eq_zero (φ i)).resolve_right (hφ i)
    have h1 : Φ (DirectSum.lof k ι V i v) = φ i v :=
      DirectSum.toModule_lof k (φ := fun i => (φ i).toLinearMap) i v
    apply hi
    rw [← h1, hv, map_zero]
  have heq : Module.finrank k (⨁ i, V i) = Module.finrank k W :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective hinj) hle
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hinj
  exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective Φ.toLinearMap ⟨hinj, hsurj⟩)
    Φ.isIntertwining'⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitAtScaledArgumentTwoVariableExpansionStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelUnitAtScaledArgument_twoVariableExpansion : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (L N c : ℕ) (A₁ a₂ g : ℤ), 1 ≤ L → a₂ ≡ N * g [ZMOD (p : ℤ) ^ L] → (N : ℤ) ∣ a₂ → 0 < N → Nat.Coprime N p → 1 < c → Nat.Coprime c (6 * N * p) → ¬ (((N * p ^ L : ℕ) : ℤ) ∣ A₁) →
  ∃ θ : ℤ → ℤ → ℤ,
    (∀ r : ℤ, ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → θ k r = 0) ∧
    (∃ r0 : ℤ, ∀ k r : ℤ, r < r0 → θ k r = 0) ∧
    (∀ k r : ℤ, θ k r ≠ 0 → (p : ℤ) ^ L ∣ r - A₁ * k) ∧
    (∀ r : ℤ, (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = ∑ᶠ k : ℤ, (θ k r : Ω) * zt ε p L ^ (g * k)) ∧
    (∀ r : ℤ, ∑ᶠ k : ℤ, ((k * θ k r : ℤ) : Ω) * zt ε p L ^ (g * k) =
      -∑ᶠ i : ℤ, (if 0 ≤ i then smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ i.toNat else 0) *
        (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff (((r - i : ℤ) : ℚ) / (p : ℚ) ^ L)) ∧
    (∀ n : ℕ, smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ n ∈ Subring.closure {zt ε p L}) ∧
    (∃ r m : ℤ, (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = zt ε p L ^ m ∨
      (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = -(zt ε p L ^ m)) := by
  first | exact @GlobalTheory.SiegTwo.sgN_two_variable | exact GlobalTheory.SiegTwo.sgN_two_variable | (intros; apply GlobalTheory.SiegTwo.sgN_two_variable ; all_goals assumption)
end

