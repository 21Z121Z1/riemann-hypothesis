import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0083
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0195
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0196
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0197

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubrepClosureAnalyticVectors
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.AnalyticClosure
open GlobalTheory.FockTensor

variable {p q : ℕ} {T : GrpData p q}

def restrictRep (πU : URep T) (K : Submodule ℂ πU.H) (hK : IsClosed (K : Set πU.H))
    (hinv : ∀ g, ∀ x ∈ K, πU.π g x ∈ K) : URep T :=
  haveI : CompleteSpace K := hK.completeSpace_coe
  { H := K
    π :=
      { toFun := fun g => ((πU.π g).comp K.subtypeL).codRestrict K (fun x => hinv g x x.2)
        map_one' := by ext x; simp
        map_mul' := fun a b => by ext x; simp; rfl }
    isom := fun g x => πU.isom g x
    cont := fun x => (πU.cont x).subtype_mk _ }

theorem inner_orbit_eq_zero (πU : URep T) {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (E : V →ₗ[ℂ] πU.H) {Y : Mat p q} (hY : Y ∈ upq p q)
    (hd : ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E x)) (E (A x)) 0)
    (y : V) {C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hb : ∀ k : ℕ, ‖E ((A ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ))
    (w : πU.H) (hw : ∀ v, inner ℂ w (E v) = 0) (t : ℝ) :
    inner ℂ w (πU.π (T.expt (t • Y)) (E y)) = 0 := by
  have key := GlobalTheory.FactorialJet.eq_zero_of_factorial_bound ℂ
    (fun k t => inner ℂ w (πU.π (T.expt (t • Y)) (E ((A ^ k) y)))) (‖w‖ * C) ρ
    (mul_nonneg (norm_nonneg _) hC) hρ ?_ ?_ ?_ 0 t
  · simpa using key
  · intro k s
    have h1 := hasDerivAt_orbit πU hY (hd ((A ^ k) y)) s
    have h2 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1
    rw [pow_succ', Module.End.mul_apply]
    exact h2
  · intro k s
    refine (norm_inner_le_norm _ _).trans ?_
    rw [πU.isom, mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [← mul_assoc]
    exact hb k
  · intro k
    simp [T.expt_zero, hw]

theorem orbit_mem_closure (πU : URep T) {V : Type} [AddCommGroup V] [Module ℂ V]
    (A : Module.End ℂ V) (E : V →ₗ[ℂ] πU.H) {Y : Mat p q} (hY : Y ∈ upq p q)
    (hd : ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E x)) (E (A x)) 0)
    (hb : ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧
      ∀ k : ℕ, ‖E ((A ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ))
    (t : ℝ) (x : πU.H) (hx : x ∈ (LinearMap.range E).topologicalClosure) :
    πU.π (T.expt (t • Y)) x ∈ (LinearMap.range E).topologicalClosure := by
  have h0 : ∀ y, πU.π (T.expt (t • Y)) (E y) ∈ (LinearMap.range E).topologicalClosure := by
    intro y
    obtain ⟨C, ρ, hC, hρ, h⟩ := hb y
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro w hw
    refine inner_orbit_eq_zero πU A E hY hd y hC hρ h w (fun v => ?_) t
    exact (Submodule.mem_orthogonal' _ _).1 hw _ (LinearMap.mem_range_self _ v)
  have hcl : IsClosed ((πU.π (T.expt (t • Y))) ⁻¹'
      ((LinearMap.range E).topologicalClosure : Set πU.H)) :=
    (Submodule.isClosed_topologicalClosure _).preimage (ContinuousLinearMap.continuous _)
  have hsub : ((LinearMap.range E : Submodule ℂ πU.H) : Set πU.H) ⊆
      (πU.π (T.expt (t • Y))) ⁻¹' ((LinearMap.range E).topologicalClosure : Set πU.H) := by
    rintro _ ⟨y, rfl⟩
    exact h0 y
  exact closure_minimal hsub hcl hx

theorem exists_subrep_closure : ∀ (p q : ℕ) (T : GrpData p q), Subgroup.closure (T.expt '' upq p q) = ⊤ → ∀ (πU : URep T) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (E : V →ₗ[ℂ] πU.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E x)) (E (act Y x)) 0) → (∀ Y ∈ upq p q, ∀ y, ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ∀ k : ℕ, ‖E ((act Y ^ k) y)‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → ∃ (σ : URep T) (j : V →ₗ[ℂ] σ.H) (J : σ.H →ₗᵢ[ℂ] πU.H), Dense (Set.range j) ∧ (∀ x, J (j x) = E x) ∧ (∀ g y, J (σ.π g y) = πU.π g (J y)) ∧ (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (act Y x)) 0) := by
  intro p q T hgen πU V _ _ act E hd hb
  have hinv : ∀ g : T.G, ∀ x ∈ (LinearMap.range E).topologicalClosure,
      πU.π g x ∈ (LinearMap.range E).topologicalClosure := by
    intro g
    have hg : g ∈ Subgroup.closure (T.expt '' upq p q) := by rw [hgen]; trivial
    induction hg using Subgroup.closure_induction'' with
    | mem g hg =>
      obtain ⟨Y, hY, rfl⟩ := hg
      intro x hx
      simpa using orbit_mem_closure πU (act Y) E hY (hd Y hY) (hb Y hY) 1 x hx
    | inv_mem g hg =>
      obtain ⟨Y, hY, rfl⟩ := hg
      intro x hx
      have he : (T.expt Y)⁻¹ = T.expt ((-1 : ℝ) • Y) := by
        have := T.expt_add Y hY 1 (-1)
        rw [add_neg_cancel, zero_smul, one_smul, T.expt_zero] at this
        exact inv_eq_of_mul_eq_one_right this.symm
      rw [he]
      exact orbit_mem_closure πU (act Y) E hY (hd Y hY) (hb Y hY) (-1) x hx
    | one => intro x hx; simpa using hx
    | mul a b _ _ ha hb' =>
      intro x hx
      rw [map_mul, ContinuousLinearMap.mul_apply]
      exact ha _ (hb' x hx)
  set K := (LinearMap.range E).topologicalClosure with hKdef
  have hK : IsClosed (K : Set πU.H) := Submodule.isClosed_topologicalClosure _
  have hmem : ∀ x, E x ∈ K := fun x =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x)
  refine ⟨restrictRep πU K hK hinv, E.codRestrict K hmem, K.subtypeₗᵢ, ?_, fun x => rfl,
    fun g y => rfl, ?_⟩
  · show Dense (Set.range (E.codRestrict K hmem : V → K))
    rw [Subtype.dense_iff]
    intro x hx
    have : (Subtype.val '' Set.range (E.codRestrict K hmem : V → K)) =
        ((LinearMap.range E : Submodule ℂ πU.H) : Set πU.H) := by
      rw [← Set.range_comp, LinearMap.coe_range]; rfl
    exact this ▸ (hx : x ∈ closure ((LinearMap.range E : Submodule ℂ πU.H) : Set πU.H))
  · intro Y hY x
    have h := hd Y hY x
    rw [hasDerivAt_iff_isLittleO_nhds_zero, ← Asymptotics.isLittleO_norm_left] at h ⊢
    exact h

end GlobalTheory.AnalyticClosure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinsumDosetIndSmul
section
namespace GlobalTheory.DoubleCosetIndicatorSum

theorem mul_mem_doubleCoset {G : Type} [Group G] {K : Subgroup G} {a g k : G}
    (hg : g ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G)) (hk : k ∈ K) :
    g * k ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G) := by
  obtain ⟨h, hh, k', hk', rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
  exact DoubleCoset.mem_doubleCoset.2 ⟨h, hh, k' * k, K.mul_mem hk' hk, mul_assoc _ _ _⟩

private theorem dosetInd_smul_eq_sum_filter {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {K : Subgroup G} {x : V} (hx : x ∈ GlobalTheory.PRep.fixed ρ K) {a : G} {R : Finset G}
    (hR : ∀ γ ∈ R, γ ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G))
    (hU : ∀ g ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G), ∃! γ : G, γ ∈ R ∧ γ⁻¹ * g ∈ K)
    [DecidableEq (G ⧸ K)] (c : G ⧸ K) :
    Formalism.UG.dosetInd ℂ K a (Quotient.out c) • ρ (Quotient.out c) x =
      ∑ γ ∈ R.filter (fun γ : G => (γ : G ⧸ K) = c), ρ γ x := by
  have hfix : ∀ k ∈ K, ρ k x = x := GlobalTheory.LGrp.mem_fixed.1 hx

  have hmk : ∀ γ : G, ((γ : G ⧸ K) = c ↔ γ⁻¹ * Quotient.out c ∈ K) := by
    intro γ
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  by_cases hc : Quotient.out c ∈ DoubleCoset.doubleCoset a (K : Set G) (K : Set G)
  ·
    rw [Formalism.UG.P.dosetInd_of_mem ℂ K a _ hc, one_smul]
    obtain ⟨γ₀, ⟨hγ₀R, hγ₀K⟩, huniq⟩ := hU _ hc
    have hfil : R.filter (fun γ : G => (γ : G ⧸ K) = c) = {γ₀} := by
      ext γ
      simp only [Finset.mem_filter, Finset.mem_singleton, hmk]
      constructor
      · rintro ⟨hγR, hγK⟩
        exact huniq γ ⟨hγR, hγK⟩
      · rintro rfl
        exact ⟨hγ₀R, hγ₀K⟩
    rw [hfil, Finset.sum_singleton]
    calc ρ (Quotient.out c) x = ρ (γ₀ * (γ₀⁻¹ * Quotient.out c)) x := by rw [mul_inv_cancel_left]
      _ = ρ γ₀ (ρ (γ₀⁻¹ * Quotient.out c) x) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ γ₀ x := by rw [hfix _ hγ₀K]
  ·
    rw [Formalism.UG.P.dosetInd_of_not_mem ℂ K a _ hc, zero_smul]
    refine (Finset.sum_eq_zero fun γ hγ => ?_).symm
    rw [Finset.mem_filter, hmk] at hγ
    refine absurd ?_ hc
    have h := mul_mem_doubleCoset (hR γ hγ.1) hγ.2
    rwa [mul_inv_cancel_left] at h

theorem main : (let d1 : {G V : Type} → [inst : Group G] → [inst_1 : AddCommGroup V] → [inst_2 : Module ℂ V] → Representation ℂ G V → Subgroup G → (G → ℂ) → V → V := @(fun {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (h : G → ℂ) (x : V) ↦ ∑ᶠ (c : G ⧸ K), h (Quotient.out c) • ((ρ : G → V →ₗ[ℂ] V) (Quotient.out c) : V → V) x); ∀ {G V : Type} [inst : Group G] [inst_1 : AddCommGroup V] [inst_2 : Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G} {x : V}, x ∈ GlobalTheory.PRep.fixed ρ K → ∀ {a : G} {R : Finset G}, (∀ γ ∈ R, γ ∈ DoubleCoset.doubleCoset a (↑K : Set G) (↑K : Set G)) → (∀ g ∈ DoubleCoset.doubleCoset a (↑K : Set G) (↑K : Set G), ∃! γ : G, γ ∈ R ∧ γ⁻¹ * g ∈ K) → d1 ρ K (Formalism.UG.dosetInd ℂ K a) x = ∑ γ ∈ R, ((ρ : G → V →ₗ[ℂ] V) γ : V → V) x) := by
  intro d1 G V _ _ _ ρ K x hx a R hR hU
  classical
  show ∑ᶠ c : G ⧸ K, Formalism.UG.dosetInd ℂ K a (Quotient.out c) • ρ (Quotient.out c) x = ∑ γ ∈ R, ρ γ x
  rw [finsum_congr (dosetInd_smul_eq_sum_filter hx hR hU)]
  rw [finsum_eq_sum_of_support_subset (s := R.image fun γ : G => (γ : G ⧸ K))]
  · exact Finset.sum_fiberwise_of_maps_to (fun γ hγ => Finset.mem_image_of_mem _ hγ) _
  · intro c hc
    obtain ⟨γ, hγ, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Function.mem_support.1 hc)
    rw [Finset.mem_filter] at hγ
    exact Finset.mem_image.2 ⟨γ, hγ.1, hγ.2⟩

end GlobalTheory.DoubleCosetIndicatorSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockTensorIntertwinerUniqueAndRange
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockUniq

theorem genSub_le {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) (N : Submodule ℂ V)
    (h1 : S ⊆ N) (h2 : ∀ Z, ∀ y ∈ N, act Z y ∈ N) : genSub act S ≤ N :=
  sInf_le ⟨h1, h2⟩

theorem subset_genSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) : S ⊆ genSub act S := by
  intro x hx
  simp only [genSub, SetLike.mem_coe, Submodule.mem_sInf]
  exact fun N hN => hN.1 hx

theorem genSub_stable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (S : Set V) (Z : Mat p q) (y : V)
    (hy : y ∈ genSub act S) : act Z y ∈ genSub act S := by
  simp only [genSub, Submodule.mem_sInf] at hy ⊢
  exact fun N hN => hN.2 Z y (hy N hN)

theorem intertwiner_unique_and_range : ∀ (p q n : ℕ) (T0 : GrpData (p * n + q * 0) (p * 0 + q * n)) (T1 : GrpData p q) (T2 : GrpData n 0) (F : FockData T0 T1 T2) (M₁ : GKMod p q) (W : Submodule ℂ M₁.V) (M : GKMod n 0) (I : M₁.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (e₀ : W) (v₀ : M.V), genSub M₁.act (W : Set M₁.V) = ⊤ → KStable M₁.act W → (∀ N : Submodule ℂ M₁.V, N ≤ W → KStable M₁.act N → N = ⊥ ∨ N = W) → IrrGK M → e₀ ≠ 0 → v₀ ≠ 0 → IsGIntw F M₁ M I → (∀ io', IsKIntw F M₁ W M io' → io' (e₀ ⊗ₜ v₀) = I ((e₀ : M₁.V) ⊗ₜ v₀) → io' = I ∘ₗ TensorProduct.map W.subtype LinearMap.id) ∧ (∀ I', IsGIntw F M₁ M I' → (∀ (e : W) (v : M.V), I' ((e : M₁.V) ⊗ₜ v) = I ((e : M₁.V) ⊗ₜ v)) → I' = I) ∧ ∀ v : M.V, Set.range (fun x : M₁.V => I (x ⊗ₜ v)) = (genSub F.act1 (Set.range fun e : W => I ((e : M₁.V) ⊗ₜ v)) : Set (Pol p q n 0)) := by
  intro p q n T0 T1 T2 F M₁ W M I e₀ v₀ hgen hK hirr hM he hv hI
  refine ⟨?_, ?_, ?_⟩
  · intro io hio h0
    have h1 : ∀ v, io (e₀ ⊗ₜ v) = I ((e₀ : M₁.V) ⊗ₜ v) := by
      let N : Submodule ℂ M.V := LinearMap.eqLocus (io ∘ₗ TensorProduct.mk ℂ W M.V e₀)
        (I ∘ₗ TensorProduct.mk ℂ M₁.V M.V e₀)
      have hN : ∀ v, v ∈ N ↔ io (e₀ ⊗ₜ v) = I ((e₀ : M₁.V) ⊗ₜ v) := fun v => Iff.rfl
      rcases hM.2 N (fun Z y hy => by
        rw [hN] at hy ⊢
        rw [← hio.2, ← hI.2, hy]) with h | h
      · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (hN v₀).2 h0)) hv
      · intro v
        exact (hN v).1 (h ▸ Submodule.mem_top)
    refine TensorProduct.ext' fun e v => ?_
    let N : Submodule ℂ W := LinearMap.eqLocus (io ∘ₗ (TensorProduct.mk ℂ W M.V).flip v)
        (I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v ∘ₗ W.subtype)
    have hN : ∀ e, e ∈ N ↔ io (e ⊗ₜ v) = I ((e : M₁.V) ⊗ₜ v) := fun v => Iff.rfl
    have hst : KStable M₁.act (N.map W.subtype) := by
      rintro Z hZ _ ⟨w, hw, rfl⟩
      refine ⟨⟨M₁.act Z w, hK Z hZ w w.2⟩, ?_, rfl⟩
      have hw' := (hN w).1 hw
      refine (hN _).2 ?_
      rw [← hio.1 Z hZ w _ v rfl, hw', hI.1]
    have h0' : (e₀ : M₁.V) ∈ N.map W.subtype := ⟨e₀, (hN e₀).2 (h1 v), rfl⟩
    rcases hirr _ (Submodule.map_subtype_le W N) hst with h | h
    · rw [h, Submodule.mem_bot] at h0'
      exact absurd (Subtype.ext h0') he
    · have : (e : M₁.V) ∈ N.map W.subtype := by rw [h]; exact e.2
      obtain ⟨e', he', hee⟩ := this
      have : e' = e := Subtype.ext hee
      subst this
      simpa using (hN e').1 he'
  · intro I' hI' hW
    refine TensorProduct.ext' fun x v => ?_
    let N : Submodule ℂ M₁.V := LinearMap.eqLocus (I' ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v)
        (I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v)
    have hN : ∀ e, e ∈ N ↔ I' (e ⊗ₜ v) = I (e ⊗ₜ v) := fun v => Iff.rfl
    have := genSub_le M₁.act (W : Set M₁.V) N (fun w hw => (hN w).2 (hW ⟨w, hw⟩ v))
      (fun Z y hy => by
        rw [hN] at hy ⊢
        rw [← hI'.1, ← hI.1, hy])
    rw [hgen] at this
    exact (hN x).1 (this Submodule.mem_top)
  · intro v
    let f : M₁.V →ₗ[ℂ] Pol p q n 0 := I ∘ₗ (TensorProduct.mk ℂ M₁.V M.V).flip v
    have hf : ∀ x, f x = I (x ⊗ₜ v) := fun x => rfl
    apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      have := genSub_le M₁.act (W : Set M₁.V)
        ((genSub F.act1 (Set.range fun e : W => I ((e : M₁.V) ⊗ₜ v))).comap f)
        (fun w hw => subset_genSub F.act1 _ ⟨⟨w, hw⟩, rfl⟩)
        (fun Z y hy => by
          rw [Submodule.mem_comap, hf] at hy ⊢
          rw [← hI.1]
          exact genSub_stable _ _ _ _ hy)
      rw [hgen] at this
      exact this (Submodule.mem_top : x ∈ ⊤)
    · have := genSub_le F.act1 (Set.range fun e : W => I ((e : M₁.V) ⊗ₜ v)) (LinearMap.range f)
        (by rintro _ ⟨e, rfl⟩; exact ⟨e, rfl⟩)
        (by rintro Z _ ⟨x, rfl⟩; exact ⟨M₁.act Z x, by rw [hf, hf, hI.1]⟩)
      intro y hy
      obtain ⟨x, hx⟩ := this hy
      exact ⟨x, hx⟩

end GlobalTheory.FockUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricH1ZetaSubOneKillsStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_h1_zeta_sub_one_kills : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k j : ℕ), 1 ≤ j → ∀ c : Gal p Ω → Ω, IntegralLocallyConstCochainModPow k (Ggeo p Ω ⊓ ⨅ n, Gn T n) c →
  (∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong p k (c (g * h)) (c g + g (c h))) →
  Cob1 k (Ggeo p Ω ⊓ ⨅ n, Gn T n) (fun g => (T.ζ j - 1) * c g) := by
  first | exact @GlobalTheory.K5.TateGeo.h1_killed_by_zeta_sub_one_geo | exact GlobalTheory.K5.TateGeo.h1_killed_by_zeta_sub_one_geo | (intros; apply GlobalTheory.K5.TateGeo.h1_killed_by_zeta_sub_one_geo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeRootsNePrimePowMulRootOfUnityStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeRoots_ne_prime_pow_mul_rootOfUnity : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (α β ζ : ℂ), 1 ≤ e → 0 < N → ¬ l ∣ N → Prim (2 * e + 1) N χ g → α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (2 * e) → ‖ι.symm α‖ = 1 → (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) → α ≠ ζ ∧ β ≠ l * ζ ∧ ∀ j : ℕ, 1 ≤ j → α ≠ (l : ℂ) ^ j * ζ := by
  first | exact @GlobalTheory.FactorsAtL.factors_ne_zero | exact GlobalTheory.FactorsAtL.factors_ne_zero | (intros; apply GlobalTheory.FactorsAtL.factors_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTqSemisimpleCuspFormsGamma1
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.SemisimpleLevelOne

lemma lev_one (N : ℕ) : GlobalTheory.Hk.lev N 1 = CongruenceSubgroup.Gamma1 N := by
  ext γ
  simp only [GlobalTheory.Hk.lev, Subgroup.mem_inf, CongruenceSubgroup.Gamma0_mem, and_iff_left_iff_imp]
  intro _
  exact Subsingleton.elim _ _

theorem tq_semisimple : ∀ (N k q : ℕ) (σ : SL(2, ℤ)), 5 ≤ N → 3 ≤ k → q.Prime → ¬ q ∣ N →
    IsDiam N 1 (q : ZMod N) σ →
    ∀ (f : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ)) (c : ℂ) (n : ℕ),
      (fun F => TqF (k : ℤ) q σ F - c • F)^[n] ⇑f = 0 → TqF (k : ℤ) q σ ⇑f = c • ⇑f := by
  intro N k q σ hN _ hq hqN hσ f c n h
  obtain ⟨-, -, hT, hD, -⟩ := GlobalTheory.SlashUpperTriangularMatrices.bridge
  have hT' : TqF (k : ℤ) q σ = GlobalTheory.Hk.heckeT (k : ℤ) q σ := funext fun F => hT _ _ _ F hq.pos
  have hσ' : GlobalTheory.Hk.IsDia N 1 (q : ℤ) σ := (hD N 1 (q : ℤ) σ).1 (by simpa using hσ)
  rw [hT'] at h ⊢
  let g : CuspForm (GlobalTheory.Hk.lev N 1) (k : ℤ) := f.copy ⇑f rfl (by rw [lev_one])
  exact GlobalTheory.T.heckeTOperatorExplicit_semisimple_cuspForms N 1 q (k : ℤ) σ c n (by omega) one_pos hq (by simpa using hqN) hσ' g h

end GlobalTheory.HeckeFamilyMatrices.SemisimpleLevelOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InvariantInnerFormsProportionalWeightLine
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockForm

theorem act_of_mem_wtSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {x : V} (h : x ∈ wtSub act μ)
    (a : Ix p q) : act (Eab a a) x = ((μ a : ℚ) : ℂ) • x := by
  have := (Submodule.mem_iInf _).1 h a
  simpa [LinearMap.mem_ker, sub_eq_zero] using this

theorem form_eq_zero {p q : ℕ} (M : GKMod p q) (D : M.V → M.V → ℂ)
    (hadd₁ : ∀ x x' y, D (x + x') y = D x y + D x' y)
    (hsmul₁ : ∀ (c : ℂ) x y, D (c • x) y = star c * D x y)
    (hadd₂ : ∀ x y y', D x (y + y') = D x y + D x y')
    (hsmul₂ : ∀ (c : ℂ) x y, D x (c • y) = c * D x y)
    (hinv : ∀ Z x y, D (M.act Z x) y = D x (M.act (adjZ Z) y))
    (μ : Ix p q → ℚ) (v : M.V) (hv : v ∈ wtSub M.act μ)
    (hline : ∀ x ∈ wtSub M.act μ, ∃ c : ℂ, x = c • v) (hgen : genSub M.act {v} = ⊤)
    (hvv : D v v = 0) : ∀ x y, D x y = 0 := by
  have hv0 : ∀ y, D v y = 0 := by
    intro y
    refine Submodule.iSup_induction (motive := fun y => D v y = 0) _ (M.wts y) ?_ ?_ ?_
    · intro ν y hy
      by_cases hν : ν = μ
      · subst hν
        obtain ⟨c, rfl⟩ := hline y hy
        rw [hsmul₂, hvv, mul_zero]
      · obtain ⟨a, ha⟩ := Function.ne_iff.1 hν
        have h := hinv (Eab a a) v y
        rw [GlobalTheory.FockTensor.adjZ_Eab, GlobalTheory.FockTensor.sgnIx_mul_self, one_smul,
          act_of_mem_wtSub hv, act_of_mem_wtSub hy, hsmul₁, hsmul₂] at h
        have hs : star ((μ a : ℚ) : ℂ) = ((μ a : ℚ) : ℂ) := by simp
        rw [hs] at h
        have hne : ((μ a : ℚ) : ℂ) - ((ν a : ℚ) : ℂ) ≠ 0 := by
          rw [sub_ne_zero]; exact_mod_cast ha.symm
        have : (((μ a : ℚ) : ℂ) - ((ν a : ℚ) : ℂ)) * D v y = 0 := by linear_combination h
        exact (mul_eq_zero.1 this).resolve_left hne
    · have := hsmul₂ 0 v 0
      simpa using this
    · intro y y' h h'
      rw [hadd₂, h, h', add_zero]
  let N : Submodule ℂ M.V :=
    { carrier := {x | ∀ y, D x y = 0}
      add_mem' := fun {x x'} h h' y => by rw [hadd₁, h y, h' y, add_zero]
      zero_mem' := fun y => by simpa using hsmul₁ 0 0 y
      smul_mem' := fun c x h y => by rw [hsmul₁, h y, mul_zero] }
  have hN : genSub M.act {v} ≤ N := by
    apply sInf_le
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Set.mem_singleton_iff.1 hx]
      exact hv0
    · intro Z x hx y
      rw [hinv]
      exact hx _
  intro x y
  exact hN (hgen ▸ Submodule.mem_top) y

theorem inner_eq_mul : ∀ (p q : ℕ) (M : GKMod p q) (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (j : M.V →ₗ[ℂ] H₁) (E₁ E₂ : M.V →ₗ[ℂ] H₂), (∀ Z x y, inner ℂ (j (M.act Z x)) (j y) = inner ℂ (j x) (j (M.act (adjZ Z) y))) → (∀ Z x y, inner ℂ (E₁ (M.act Z x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (M.act (adjZ Z) y))) → ∀ (μ : Ix p q → ℚ) (v : M.V), v ∈ wtSub M.act μ → (∀ x ∈ wtSub M.act μ, ∃ c : ℂ, x = c • v) → genSub M.act {v} = ⊤ → ‖j v‖ = 1 → ∀ x y, inner ℂ (E₁ x) (E₂ y) = inner ℂ (E₁ v) (E₂ v) * inner ℂ (j x) (j y) := by
  intro p q M H₁ _ _ H₂ _ _ j E₁ E₂ hj hE μ v hv hline hgen hnorm x y
  have := form_eq_zero M
    (fun x y => inner ℂ (E₁ x) (E₂ y) - inner ℂ (E₁ v) (E₂ v) * inner ℂ (j x) (j y))
    (fun x x' y => by simp only [map_add, inner_add_left]; ring)
    (fun c x y => by simp only [map_smul, inner_smul_left, starRingEnd_apply]; ring)
    (fun x y y' => by simp only [map_add, inner_add_right]; ring)
    (fun c x y => by simp only [map_smul, inner_smul_right]; ring)
    (fun Z x y => by simp only [hj, hE])
    μ v hv hline hgen (by simp [inner_self_eq_norm_sq_to_K, hnorm]) x y
  exact sub_eq_zero.1 this

end GlobalTheory.FockForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKilledByLowerNilradicalActBlockDiagonal
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.KilledByLowerStable

theorem act_eq_zero_of_lower {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (x : V) (hx : KilledByLower act x) (Y : Mat p q)
    (h1 : ∀ (a : Fin p) (j : Ix p q), Y (Sum.inl a) j = 0)
    (h2 : ∀ (i : Ix p q) (b : Fin q), Y i (Sum.inr b) = 0) : act Y x = 0 := by
  have hY : Y = ∑ i, ∑ j, Y i j • Eab i j := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [Eab, Matrix.smul_single]
  rw [hY]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rcases i with a | b
  · rw [h1, zero_smul]
  · rcases j with a | b'
    · rw [hx a b, smul_zero]
    · rw [h2, zero_smul]

theorem killedByLower_act : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ Z : Mat p q, IsKC Z →
    ∀ x : V, KilledByLower act x → KilledByLower act (act Z x) := by
  intro p q V _ _ act hact Z hZ x hx a b
  have h := congrArg (fun f : Module.End ℂ V => f x) (hact (Eab (Sum.inr b) (Sum.inl a)) Z)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [hx a b, map_zero, sub_zero] at h
  rw [← h]
  apply act_eq_zero_of_lower act x hx
  · intro a' j
    have h0 : Z (Sum.inl a') (Sum.inr b) = 0 := hZ _ _ (by simp [sameBlock])
    by_cases hj : j = Sum.inl a
    · subst hj
      simp [Eab, h0]
    · simp [Eab, hj]
  · intro i b'
    have h0 : Z (Sum.inl a) (Sum.inr b') = 0 := hZ _ _ (by simp [sameBlock])
    by_cases hi : i = Sum.inr b
    · subst hi
      simp [Eab, h0]
    · simp [Eab, hi]

end GlobalTheory.KilledByLowerStable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeTOfPrimeNotDvdStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd : ∀ (k L N q : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 1 ≤ k → N ∣ L → q.Prime → ¬ q ∣ L → MF k L (ch ε) a → MF k L (ch ε) (To k (ch ε q) q a) := by
  first | exact @GlobalTheory.EisM.To_MF | exact GlobalTheory.EisM.To_MF | (intros; apply GlobalTheory.EisM.To_MF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeUAndDepletionStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → l.Prime → l ∣ L → (∀ d, χ (d + L) = χ d) → MF k L χ a → MF k L χ (Uo l a) ∧ MF k (L * l) χ (dep l a) := by
  first | exact @GlobalTheory.depletion_mf | exact GlobalTheory.depletion_mf | (intros; apply GlobalTheory.depletion_mf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesNeZeroReGeOneOfPositivityStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lseries_ne_zero_re_ge_one_of_positivity : ∀ (M : ℕ) (b ω : ℕ → ℂ) (C : ℝ) (Λ : ℂ → ℂ), 0 < M → b 1 = 1 → b 0 = 0 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime M → b n = 0) → (∀ p r : ℕ, p.Prime → ¬ p ∣ M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → (∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → (∀ s : ℝ, 0 < s → s ≤ 1 → s * ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) ≤ C) → (∀ p : ℕ, p.Prime → ¬ p ∣ M → (p : ZMod M) = -1 → (b p).re = 0) → Differentiable ℂ Λ → (∀ s : ℝ, 0 < s → LSeries b ((1 + s : ℝ) : ℂ) = Λ ((1 + s : ℝ) : ℂ)) → ∀ w : ℝ, 1 ≤ w → Λ w ≠ 0 := by
  first | exact @GlobalTheory.EisM.lseries_ne_zero_edge | exact GlobalTheory.EisM.lseries_ne_zero_edge | (intros; apply GlobalTheory.EisM.lseries_ne_zero_edge <;> assumption)
end

