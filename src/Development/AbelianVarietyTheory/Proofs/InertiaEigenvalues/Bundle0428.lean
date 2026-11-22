import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Formalism.LocalRingCardinality.HostCls
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0078
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0399
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.BurnsideField

open scoped MonoidAlgebra

theorem span_range_eq_top_of_isAlgClosed {G K V : Type} [Group G] [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (τ : Representation K G V)
    (h : τ.IsIrreducible) : Submodule.span K (Set.range τ) = ⊤ := by
  classical
  have hscal : ∀ φ : Module.End K[G] τ.asModule, ∃ c : K, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed
      (A := K[G]) (V := τ.asModule) K).2 φ
    exact ⟨c, fun m => by rw [← hc]; rfl⟩
  have hsurj : Function.Surjective τ.asAlgebraHom := by
    intro f
    let F : Module.End (Module.End K[G] τ.asModule) τ.asModule :=
      { toFun := fun m => τ.asModuleEquiv.symm (f (τ.asModuleEquiv m))
        map_add' := fun x y => by simp
        map_smul' := fun φ m => by
          obtain ⟨c, hc⟩ := hscal φ
          simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
    let b := Module.finBasis K V
    obtain ⟨r, hr⟩ := jacobson_density F
      (Finset.univ.image fun i => τ.asModuleEquiv.symm (b i))
    refine ⟨r, b.ext fun i => ?_⟩
    have := congrArg τ.asModuleEquiv (hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    exact this.symm
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨r, rfl⟩ := hsurj f
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | single g c =>
    rw [Representation.asAlgebraHom_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

theorem span_mat_eq_top_of_isIrrSub {Γ K : Type} [Group Γ] [Field K] [IsAlgClosed K] {r : ℕ}
    (σ : Γ →* GL (Fin r) K) (h : IsIrrSub σ ⊤) : Submodule.span K (Set.range (mat σ)) = ⊤ := by
  classical
  let τ : Representation K Γ (Fin r → K) :=
    { toFun := fun g => Matrix.toLin' (mat σ g)
      map_one' := by simp [mat]; rfl
      map_mul' := fun g g' => by simp [mat, Matrix.toLin'_mul]; rfl }
  have hτ : ∀ g v, τ g v = (mat σ g).mulVec v := fun g v => Matrix.toLin'_apply _ _
  have hirr : τ.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation τ) := by
      refine ⟨⊥, ⊤, fun hbt => h.1 ?_⟩
      exact (congrArg Subrepresentation.toSubmodule hbt).symm
    refine ⟨fun W => ?_⟩
    rcases h.2.2 W.toSubmodule le_top (fun g v hv => by
      have := W.apply_mem_toSubmodule g hv
      rwa [hτ] at this) with h1 | h1
    · exact Or.inl (Subrepresentation.toSubmodule_injective h1)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h1)
  have hs := span_range_eq_top_of_isAlgClosed τ hirr
  have hm : Set.range (mat σ) = (LinearMap.toMatrix' (R := K) (m := Fin r) (n := Fin r)) '' Set.range τ := by
    rw [← Set.range_comp]
    congr 1
    funext g
    exact (LinearMap.toMatrix'_toLin' (mat σ g)).symm
  rw [hm]
  have := Submodule.map_span (LinearMap.toMatrix' (R := K) (m := Fin r) (n := Fin r)).toLinearMap
    (Set.range τ)
  rw [hs, Submodule.map_top, LinearEquiv.range] at this
  exact this.symm

theorem span_eq_top_of_span_map {Γ k K : Type} [Field k] [Field K] [Algebra k K] {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) k)
    (h : Submodule.span K (Set.range fun g => (M g).map (algebraMap k K)) = ⊤) :
    Submodule.span k (Set.range M) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let F : Matrix (Fin r) (Fin r) K →ₗ[K] K :=
    { toFun := fun X => ∑ i, ∑ j, X i j * algebraMap k K (f (Matrix.single i j 1))
      map_add' := fun X Y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c X => by simp [Finset.mul_sum, mul_assoc] }
  have hF : ∀ X : Matrix (Fin r) (Fin r) k, F (X.map (algebraMap k K)) = algebraMap k K (f X) := by
    intro X
    conv_rhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum]
    change ∑ i, ∑ j, algebraMap k K (X i j) * algebraMap k K (f (Matrix.single i j 1)) = _
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : k) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul, map_mul]
  have hker : (⊤ : Submodule K (Matrix (Fin r) (Fin r) K)) ≤ LinearMap.ker F := by
    rw [← h, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    have : f (M g) = 0 := hf (Submodule.subset_span ⟨g, rfl⟩)
    simp only [SetLike.mem_coe, LinearMap.mem_ker, hF, this, map_zero]
  apply hf0
  refine LinearMap.ext fun X => ?_
  have h1 : F (X.map (algebraMap k K)) = 0 := hker trivial
  rw [hF] at h1
  exact (algebraMap k K).injective (by rw [h1]; simp)

theorem span_mat_eq_top_of_absIrrSub :
    ∀ {Γ k : Type} [Group Γ] [Field k] {r : ℕ} (ρ : Γ →* GL (Fin r) k), AbsIrrSub ρ ⊤ → Submodule.span k (Set.range (mat ρ)) = ⊤ := by
  intro Γ k _ _ r ρ h
  classical
  have htop : Submodule.span (AlgebraicClosure k)
      ((fun v : Fin r → k => (algebraMap k (AlgebraicClosure k)) ∘ v) ''
      ((⊤ : Submodule k (Fin r → k)) : Set (Fin r → k))) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun (AlgebraicClosure k) (Fin r)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, trivial, ?_⟩
    ext x
    by_cases hx : x = j
    · subst hx; simp
    · simp [hx]
  unfold AbsIrrSub at h
  rw [htop] at h
  have h2 := span_mat_eq_top_of_isIrrSub _ h
  have h3 : mat (mapRep (algebraMap k (AlgebraicClosure k)) ρ) =
      fun g => (mat ρ g).map (algebraMap k (AlgebraicClosure k)) := by
    funext g
    ext p q
    simp [mat, mapRep]
  rw [h3] at h2
  exact span_eq_top_of_span_map (mat ρ) h2

end GlobalTheory.BurnsideField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepresentationDensityOfIsInternalConstituent
section
noncomputable section

namespace GlobalTheory.BlockDensity

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

variable {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V]

def spanAlg (ρ : Representation K Γ V) : Subalgebra K (Module.End K V) :=
  (Submodule.span K (Set.range ρ)).toSubalgebra (Submodule.subset_span ⟨1, map_one ρ⟩) (by
    intro a b ha hb
    have : Submodule.span K (Set.range ρ) * Submodule.span K (Set.range ρ) ≤
        Submodule.span K (Set.range ρ) := by
      rw [Submodule.span_mul_span]
      apply Submodule.span_mono
      rintro _ ⟨_, ⟨g, rfl⟩, _, ⟨h, rfl⟩, rfl⟩
      exact ⟨g * h, map_mul ρ g h⟩
    exact this (Submodule.mul_mem_mul ha hb))

variable {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] in
private theorem apply_mem_of_mem_span_of_invariant {F U : Type} [Field F] [AddCommGroup U]
    [Module F U] (S : Set (Module.End F U)) (W : Submodule F U)
    (hS : ∀ T ∈ S, ∀ w ∈ W, T w ∈ W) {T : Module.End F U} (hT : T ∈ Submodule.span F S) :
    ∀ w ∈ W, T w ∈ W := by
  induction hT using Submodule.span_induction with
  | mem T h => exact hS T h
  | zero => intro w _; simp
  | add T T' _ _ h h' => intro w hw; simpa using W.add_mem (h w hw) (h' w hw)
  | smul c T _ h => intro w hw; simpa using W.smul_mem c (h w hw)

variable {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] in
theorem _root_.GlobalTheory.BlockDensity.stable_span (ρ : Representation K Γ V) (W : Submodule K V)
    (hs : _root_.Formalism.MainNotions.N.Stable ρ W) :
    ∀ t ∈ Submodule.span K (Set.range ρ), ∀ v ∈ W, t v ∈ W := by
  intro t ht
  refine apply_mem_of_mem_span_of_invariant (Set.range ρ) W ?_ ht
  rintro _ ⟨g, rfl⟩
  exact hs g

def toSub (ρ : Representation K Γ V) (W : Submodule K V) (hs : Stable ρ W) : Submodule (spanAlg ρ) V where
  carrier := W
  add_mem' := W.add_mem
  zero_mem' := W.zero_mem
  smul_mem' := fun c _ hv => stable_span ρ W hs c.1 c.2 _ hv

variable {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] in
private theorem exists_end_apply_eq_of_ne_zero {F U : Type} [Field F] [AddCommGroup U]
    [Module F U] {w : U} (hw : w ≠ 0) (u : U) : ∃ T : Module.End F U, T w = u := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual F U, φ w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw ((Module.forall_dual_apply_eq_zero_iff F w).mp h)
  exact ⟨(φ w)⁻¹ • φ.smulRight u, by simp [smul_smul, inv_mul_cancel₀ hφ]⟩

variable {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] in
private theorem invariant_trivial_of_span_endomorphisms_full {F U : Type} [Field F] [AddCommGroup U]
    [Module F U] (S : Set (Module.End F U)) (hS : Submodule.span F S = ⊤) (W : Submodule F U)
    (hW : ∀ T ∈ S, ∀ w ∈ W, T w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  rcases eq_or_ne W ⊥ with h | h
  · exact Or.inl h
  right
  obtain ⟨w, hwW, hw⟩ := (Submodule.ne_bot_iff W).mp h
  rw [Submodule.eq_top_iff']
  intro u
  obtain ⟨T, rfl⟩ := exists_end_apply_eq_of_ne_zero (F := F) hw u
  exact apply_mem_of_mem_span_of_invariant S W hW (by rw [hS]; exact Submodule.mem_top) w hwW

variable {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] in
private theorem commute_of_mem_span_of_forall_commute {F U : Type} [Field F] [AddCommGroup U]
    [Module F U] (S : Set (Module.End F U)) (ψ : Module.End F U)
    (hS : ∀ T ∈ S, T * ψ = ψ * T) {T : Module.End F U} (hT : T ∈ Submodule.span F S) :
    T * ψ = ψ * T := by
  induction hT using Submodule.span_induction with
  | mem T h => exact hS T h
  | zero => simp
  | add T T' _ _ h h' => rw [add_mul, mul_add, h, h']
  | smul c T _ h => rw [smul_mul_assoc, mul_smul_comm, h]

variable {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] in
theorem _root_.GlobalTheory.BlockDensity.density : ∀ {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K Γ V) (ι : Type) [Fintype ι] [DecidableEq ι] (Vs : ι → Submodule K V)
    (hs : ∀ j, _root_.Formalism.MainNotions.N.Stable ρ (Vs j)), DirectSum.IsInternal Vs →
    (∀ j, Submodule.span K (Set.range fun g => (ρ g).restrict (hs j g)) = ⊤) →
    (∀ j j', j ≠ j' → ∀ e : Vs j ≃ₗ[K] Vs j',
      ¬ ∀ g v, e ((ρ g).restrict (hs j g) v) = (ρ g).restrict (hs j' g) (e v)) →
    ∀ f : V →ₗ[K] V, (∀ j, ∀ v ∈ Vs j, f v ∈ Vs j) → f ∈ Submodule.span K (Set.range ρ) := by
  intro K Γ V _ _ _ _ _ ρ ι _ _ Vs hs hint hfull hdistinct f hf
  let p : ∀ k, V →ₗ[K] Vs k := fun k => (DirectSum.component K ι (fun i => Vs i) k).comp
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap Vs) hint).symm.toLinearMap
  have hp_self : ∀ i (y : V) (hy : y ∈ Vs i), p i y = ⟨y, hy⟩ := fun i y hy =>
    hint.ofBijective_coeLinearMap_of_mem hy
  have hp_ne : ∀ i k, i ≠ k → ∀ y ∈ Vs i, p k y = 0 := fun i k hik y hy =>
    hint.ofBijective_coeLinearMap_of_mem_ne hik hy
  have htop : ∀ y : V, y ∈ ⨆ i, Vs i := fun y => by
    rw [hint.submodule_iSup_eq_top]; exact Submodule.mem_top
  have hsum : ∀ y : V, ∑ k, (p k y : V) = y := by
    intro y
    refine Submodule.iSup_induction Vs (motive := fun y => ∑ k, (p k y : V) = y) (htop y)
      ?_ (by simp) ?_
    · intro i y hy
      rw [Finset.sum_eq_single i]
      · rw [hp_self i y hy]
      · intro k _ hk
        rw [hp_ne i k (Ne.symm hk) y hy]
        rfl
      · simp
    · intro x y hx hy
      simp only [map_add, Submodule.coe_add, Finset.sum_add_distrib, hx, hy]
  have hp_rho : ∀ k g y, p k (ρ g y) = (ρ g).restrict (hs k g) (p k y) := by
    intro k g y
    refine Submodule.iSup_induction Vs
      (motive := fun y => p k (ρ g y) = (ρ g).restrict (hs k g) (p k y)) (htop y) ?_ (by simp) ?_
    · intro i y hy
      by_cases hik : i = k
      · subst hik
        rw [hp_self i _ (hs i g y hy), hp_self i y hy]
        rfl
      · rw [hp_ne i k hik _ (hs i g y hy), hp_ne i k hik y hy, map_zero]
    · intro x y hx hy
      simp only [map_add, hx, hy]
  have hcomm : ∀ φ : Module.End (_root_.GlobalTheory.BlockDensity.spanAlg ρ) V, ∀ v, f (φ v) = φ (f v) := by
    intro φ
    have hφρ : ∀ g v, φ (ρ g v) = ρ g (φ v) := fun g v =>
      φ.map_smul (⟨ρ g, Submodule.subset_span ⟨g, rfl⟩⟩ : _root_.GlobalTheory.BlockDensity.spanAlg ρ) v
    let ψ : ∀ j k, Vs j →ₗ[K] Vs k := fun j k =>
      (p k).comp ((φ.restrictScalars K).comp (Vs j).subtype)
    have hψ : ∀ j k g x, ψ j k ((ρ g).restrict (hs j g) x) = (ρ g).restrict (hs k g) (ψ j k x) := by
      intro j k g x
      show p k (φ (ρ g x)) = _
      rw [hφρ, hp_rho]
      rfl
    have hzero : ∀ j k, j ≠ k → ψ j k = 0 := by
      intro j k hjk
      by_contra hne
      have hker := invariant_trivial_of_span_endomorphisms_full _ (hfull j) (LinearMap.ker (ψ j k)) (by
        rintro _ ⟨g, rfl⟩ w hw
        rw [LinearMap.mem_ker] at hw ⊢
        rw [hψ, hw, map_zero])
      have hran := invariant_trivial_of_span_endomorphisms_full _ (hfull k) (LinearMap.range (ψ j k)) (by
        rintro _ ⟨g, rfl⟩ _ ⟨x, rfl⟩
        exact ⟨(ρ g).restrict (hs j g) x, hψ j k g x⟩)
      rcases hker with hker | hker
      · rcases hran with hran | hran
        · exact hne (LinearMap.range_eq_bot.mp hran)
        · exact hdistinct j k hjk (LinearEquiv.ofBijective (ψ j k)
            ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hran⟩) fun g v => hψ j k g v
      · exact hne (LinearMap.ker_eq_top.mp hker)
    have hφv : ∀ j v (hv : v ∈ Vs j), φ v = (ψ j j ⟨v, hv⟩ : V) := by
      intro j v hv
      rw [← hsum (φ v), Finset.sum_eq_single j]
      · rfl
      · intro k _ hkj
        show ((ψ j k ⟨v, hv⟩ : Vs k) : V) = 0
        rw [hzero j k (Ne.symm hkj)]
        rfl
      · simp
    have hcj : ∀ j, f.restrict (hf j) * ψ j j = ψ j j * f.restrict (hf j) := by
      intro j
      refine commute_of_mem_span_of_forall_commute _ (ψ j j) ?_ (by rw [hfull j]; exact Submodule.mem_top)
      rintro _ ⟨g, rfl⟩
      ext x
      exact congrArg Subtype.val (hψ j j g x).symm
    intro v
    refine Submodule.iSup_induction Vs (motive := fun v => f (φ v) = φ (f v)) (htop v) ?_
      (by simp) ?_
    · intro j v hv
      rw [hφv j v hv, hφv j (f v) (hf j v hv)]
      exact congrArg Subtype.val (LinearMap.congr_fun (hcj j) ⟨v, hv⟩)
    · intro x y hx hy
      simp only [map_add, hx, hy]
  have hlift : ∀ j (E : Module.End K (Vs j)), ∃ a ∈ Submodule.span K (Set.range ρ),
      ∀ x : Vs j, a x = E x := by
    intro j E
    have hE : E ∈ Submodule.span K (Set.range fun g => (ρ g).restrict (hs j g)) := by
      rw [hfull j]; exact Submodule.mem_top
    induction hE using Submodule.span_induction with
    | mem E h =>
      obtain ⟨g, rfl⟩ := h
      exact ⟨ρ g, Submodule.subset_span ⟨g, rfl⟩, fun x => rfl⟩
    | zero => exact ⟨0, zero_mem _, fun x => by simp⟩
    | add E E' _ _ h h' =>
      obtain ⟨a, ha, hax⟩ := h
      obtain ⟨b, hb, hbx⟩ := h'
      exact ⟨a + b, add_mem ha hb, fun x => by simp [hax, hbx]⟩
    | smul c E _ h =>
      obtain ⟨a, ha, hax⟩ := h
      exact ⟨c • a, Submodule.smul_mem _ c ha, fun x => by simp [hax]⟩
  haveI : IsSemisimpleModule (_root_.GlobalTheory.BlockDensity.spanAlg ρ) V := by
    rw [← sSup_simples_eq_top_iff_isSemisimpleModule, eq_top_iff]
    intro v _
    refine Submodule.iSup_induction Vs (motive := fun v => v ∈ sSup {m : Submodule
      (_root_.GlobalTheory.BlockDensity.spanAlg ρ) V | IsSimpleModule (_root_.GlobalTheory.BlockDensity.spanAlg ρ) m})
      (htop v) ?_ (zero_mem _) (fun _ _ => add_mem)
    intro j v hv
    rcases eq_or_ne v 0 with rfl | hv0
    · exact zero_mem _
    have hvT : v ∈ _root_.GlobalTheory.BlockDensity.toSub ρ (Vs j) (hs j) := hv
    refine Submodule.mem_sSup_of_mem ?_ hvT
    rw [Set.mem_setOf_eq, isSimpleModule_iff_isAtom]
    refine ⟨fun h => hv0 ((Submodule.mem_bot _).mp (h ▸ hvT)), fun N hN => ?_⟩
    by_contra hN0
    obtain ⟨w, hwN, hw0⟩ := (Submodule.ne_bot_iff N).mp hN0
    apply hN.2
    intro u hu
    have hwj : w ∈ Vs j := hN.le hwN
    obtain ⟨E, hE⟩ := exists_end_apply_eq_of_ne_zero (F := K)
      (show (⟨w, hwj⟩ : Vs j) ≠ 0 from fun h => hw0 (congrArg Subtype.val h)) (⟨u, hu⟩ : Vs j)
    obtain ⟨a, ha, hax⟩ := hlift j E
    have hu' : u = (⟨a, ha⟩ : _root_.GlobalTheory.BlockDensity.spanAlg ρ) • w := by
      show u = a w
      rw [hax ⟨w, hwj⟩, hE]
    rw [hu']
    exact N.smul_mem _ hwN
  let f' : Module.End (Module.End (_root_.GlobalTheory.BlockDensity.spanAlg ρ) V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => hcomm φ v }
  classical
  obtain ⟨r, hr⟩ := jacobson_density f' (Finset.univ.image (Module.finBasis K V))
  have hfr : f = (r : Module.End K V) := (Module.finBasis K V).ext fun i =>
    hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [hfr]
  exact r.2

end GlobalTheory.BlockDensity
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimeImpliesPlacesSplit
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.SplitPlaces

variable {R : Ranks} (H : Host R)

theorem sqrt_sq : (H.sqd) ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem conj_sqrt : H.conj (H.sqd) = -H.sqd :=
  by apply _root_.UpperTheory.Reformulated.B.Rc9.conj_sqrt <;> assumption

theorem exists_conjPl (l : ℕ) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E l) :
    ∃ w' ∈ placesOver H.E l, IsConjPl H w w' := by
  let c : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv
  refine ⟨HeightOneSpectrum.comap (c.symm : 𝓞 H.E →+* 𝓞 H.E) c.symm.surjective w, ?_, ?_⟩
  · show (c.symm : 𝓞 H.E →+* 𝓞 H.E) (l : 𝓞 H.E) ∈ w.asIdeal
    rw [map_natCast]
    exact hw
  · intro x y hxy
    have : y = c x := by
      apply RingOfIntegers.ext
      rw [hxy]; rfl
    subst this
    show _ ↔ c.symm (c x) ∈ w.asIdeal
    rw [c.symm_apply_apply]

theorem not_isConjPl_self {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (hld : l ≠ H.d)
    (hj : jacobiSym (-(H.d : ℤ)) l = 1) (w : HeightOneSpectrum (𝓞 H.E)) (hw : w ∈ placesOver H.E l) :
    ¬ IsConjPl H w w := by
  intro h
  have : Fact l.Prime := ⟨hl⟩
  obtain ⟨m, hm⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective m
  have hdvd : (l : ℤ) ∣ n * n + H.d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hm ⊢
    rw [← hm]; ring
  have hint : IsIntegral ℤ (H.sqd) := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [sqrt_sq]
    exact (isIntegral_natCast _).neg
  let b : 𝓞 H.E := ⟨H.sqd, hint⟩
  have hb : b ^ 2 = -(H.d : 𝓞 H.E) := by
    apply RingOfIntegers.ext
    have e : ((b : 𝓞 H.E) : H.E) = H.sqd := rfl
    simp only [map_neg, map_pow, map_natCast, e]
    exact sqrt_sq H
  have hiff : b - n ∈ w.asIdeal ↔ b + n ∈ w.asIdeal := by
    rw [h (b - n) (-(b + n)) ?_, neg_mem_iff]
    have e : ((b : 𝓞 H.E) : H.E) = H.sqd := rfl
    simp only [map_neg, map_add, map_sub, map_intCast, e, conj_sqrt]
    ring
  have hprod : (b - n) * (b + n) ∈ w.asIdeal := by
    obtain ⟨k, hk⟩ := hdvd
    have hk' : ((n * n + H.d : ℤ) : 𝓞 H.E) = ((l * k : ℤ) : 𝓞 H.E) := by rw [hk]
    push_cast at hk'
    have : (b - n) * (b + n) = (l : 𝓞 H.E) * (-k) := by
      linear_combination hb - hk'
    rw [this]
    exact w.asIdeal.mul_mem_right _ hw
  have hboth : b - n ∈ w.asIdeal ∧ b + n ∈ w.asIdeal := by
    rcases w.isPrime.mem_or_mem hprod with h1 | h1
    exacts [⟨h1, hiff.mp h1⟩, ⟨hiff.mpr h1, h1⟩]
  have h2n : ((2 * n : ℤ) : 𝓞 H.E) ∈ w.asIdeal := by
    have := w.asIdeal.sub_mem hboth.2 hboth.1
    convert this using 1
    push_cast; ring
  have hlo := GlobalTheory.HubLoc.liesOver_of_mem hl hw
  have hl2n : (l : ℤ) ∣ 2 * n := by
    rw [← Ideal.mem_span_singleton, hlo.over, Ideal.under_def, Ideal.mem_comap]
    simpa using h2n
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  rcases hp.dvd_or_dvd hl2n with h1 | h1
  · have h3 : l ∣ 2 := by exact_mod_cast h1
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h3)
  · have h3 : (l : ℤ) ∣ H.d := (dvd_add_right (h1.mul_right n)).mp hdvd
    have h4 : l ∣ H.d := by exact_mod_cast h3
    exact hld ((Nat.prime_dvd_prime_iff_eq hl H.hyp.2.1).mp h4)

theorem placesSplit : ∀ {R : Ranks} (H : Host R) (l : ℕ), SplitRowPrime H l → PlacesSplit H l := by
  intro R H l ⟨hl, h5, _, hd, _, hc⟩ w hw
  have hl2 : l ≠ 2 := by omega
  obtain ⟨hN, hj⟩ := (primeClass_eq_splitK_iff' (H := H.toHostRaw) hl).1 hc
  refine ⟨GlobalTheory.HubLoc.ramIdx_eq_one H hl hN w hw, exists_conjPl H l w hw, ?_⟩
  rintro w' h rfl
  exact not_isConjPl_self H hl hl2 hd hj _ hw h

end GlobalTheory.SplitPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StructureUnramifiedAdjoinSqrtNegPrimeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.structure_unramified_adjoin_sqrt_neg_prime : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K : FinExt l) (M : IntermediateField ℚ_[l] (Om l)) (y : Om l), M ≤ MaximalUnramifiedExtension l → y ^ 2 = -(l : Om l) → y ∉ MaximalUnramifiedExtension l → y ∈ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} → K.1 = M ⊔ IntermediateField.adjoin ℚ_[l] {y} → K.1 = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y} ∧ K.1 ≤ Ks K 1 ∧ Module.finrank ↥(K0 K) ↥K.1 = 2 ∧ Module.finrank ℚ_[l] ↥(Ks K 1) = (l - 1) / 2 * Module.finrank ℚ_[l] ↥K.1 := by
  first | exact @GlobalTheory.SqrtNegL.structure_sqrt_neg | exact GlobalTheory.SqrtNegL.structure_sqrt_neg | (intros; apply GlobalTheory.SqrtNegL.structure_sqrt_neg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualityDegreeOneContinuousCocyclesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateDuality_degreeOne_continuous_cocycles : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∃ β : ↥(continuousCocycles A.ρ) →ₗ[LL] ↥(continuousCocycles A'.ρ) →ₗ[LL] LL, (∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL A'.ρ m a.1 b.1)) ∧ (∀ a, (∀ b, β a b = 0) ↔ a.1 ∈ B1 A.ρ) ∧ ∀ b, (∀ a, β a b = 0) ↔ b.1 ∈ B1 A'.ρ := by
  first | exact @GlobalTheory.tateDuality_degreeOne_cocycles | exact GlobalTheory.tateDuality_degreeOne_cocycles | (intros; apply GlobalTheory.tateDuality_degreeOne_cocycles <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaAinfPeriodPowNeZeroStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_ainf_period_pow_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (n : ℕ), ((Per.θD l).comp (aDp l)) (τ ^ n) ≠ 0 := by
  first | exact @GlobalTheory.ThetaPer.thetaD_aDp_pow_ne_zero | exact GlobalTheory.ThetaPer.thetaD_aDp_pow_ne_zero | (intros; apply GlobalTheory.ThetaPer.thetaD_aDp_pow_ne_zero <;> assumption)
end

