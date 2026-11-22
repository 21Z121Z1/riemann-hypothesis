import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicFrobeniusSystemContinuationOpenDisc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokEquivOfExact
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.MatKerCokernel

section
variable {R : Type} [CommRing R] {a : ℕ}

abbrev Cok (Φ : Matrix (Fin a) (Fin a) R) : Type :=
  (Fin a → R) ⧸ LinearMap.range Φ.transpose.mulVecLin

def univ (Φ : Matrix (Fin a) (Fin a) R) (c : Fin a) : Cok Φ :=
  (LinearMap.range Φ.transpose.mulVecLin).mkQ (Pi.single c 1)

theorem matAct_apply' {B : Type} [AddCommGroup B] [Module R B] (Φ : Matrix (Fin a) (Fin a) R)
    (u : Fin a → B) (i : Fin a) : matAct Φ u i = ∑ j, Φ i j • u j := rfl

theorem mk_eq_sum (Φ : Matrix (Fin a) (Fin a) R) (y : Fin a → R) :
    (LinearMap.range Φ.transpose.mulVecLin).mkQ y = ∑ c, y c • univ Φ c := by
  have hy : y = ∑ c, y c • (Pi.single c 1 : Fin a → R) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hy]
  simp only [map_sum, map_smul, univ]

theorem univ_ker (Φ : Matrix (Fin a) (Fin a) R) : matAct Φ (univ Φ) = 0 := by
  funext i
  rw [matAct_apply', Pi.zero_apply]
  have h := mk_eq_sum Φ (fun j => Φ i j)
  beta_reduce at h
  rw [← h, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  refine ⟨Pi.single i 1, ?_⟩
  ext j
  simp

theorem map_ker {B B' : Type} [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
    (Φ : Matrix (Fin a) (Fin a) R) (f : B →ₗ[R] B') (u : Fin a → B) (hu : matAct Φ u = 0) :
    matAct Φ (fun c => f (u c)) = 0 := by
  funext i
  have h := congrFun hu i
  rw [matAct_apply', Pi.zero_apply] at h
  rw [matAct_apply', Pi.zero_apply]
  calc ∑ j, Φ i j • f (u j) = f (∑ j, Φ i j • u j) := by
        rw [map_sum]
        simp only [map_smul]
    _ = 0 := by rw [h, map_zero]

theorem exists_lift {B : Type} [AddCommGroup B] [Module R B]
    (Φ : Matrix (Fin a) (Fin a) R) (b : Fin a → B) (hb : matAct Φ b = 0) :
    ∃ f : Cok Φ →ₗ[R] B, ∀ c, f (univ Φ c) = b c := by
  obtain ⟨g, hg⟩ : ∃ g : (Fin a → R) →ₗ[R] B, ∀ y, g y = ∑ c, y c • b c :=
    ⟨∑ c, (LinearMap.proj c).smulRight (b c), fun y => by simp [LinearMap.sum_apply]⟩
  have key : ∀ j, ∑ c, Φ j c • b c = 0 := fun j => by
    have h := congrFun hb j
    rw [matAct_apply', Pi.zero_apply] at h
    exact h
  have hle : LinearMap.range Φ.transpose.mulVecLin ≤ LinearMap.ker g := by
    rintro _ ⟨z, rfl⟩
    rw [LinearMap.mem_ker, hg]
    calc ∑ c, (Φ.transpose.mulVecLin z) c • b c
        = ∑ c, ∑ j, z j • Φ j c • b c := by
          refine Finset.sum_congr rfl fun c _ => ?_
          simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
            Finset.sum_smul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_comm, mul_smul]
      _ = ∑ j, z j • ∑ c, Φ j c • b c := by
          rw [Finset.sum_comm]
          simp only [Finset.smul_sum]
      _ = 0 := by simp [key]
  refine ⟨(LinearMap.range Φ.transpose.mulVecLin).liftQ g hle, fun c => ?_⟩
  rw [univ, Submodule.mkQ_apply, Submodule.liftQ_apply, hg]
  simp [Pi.single_apply]

theorem hom_ext {B : Type} [AddCommGroup B] [Module R B]
    (Φ : Matrix (Fin a) (Fin a) R) (f g : Cok Φ →ₗ[R] B)
    (h : ∀ c, f (univ Φ c) = g (univ Φ c)) : f = g := by
  apply Submodule.linearMap_qext
  refine LinearMap.ext fun y => ?_
  simp only [LinearMap.comp_apply, mk_eq_sum, map_sum, map_smul, h]

end

theorem cok_equiv_of_exact : ∀ (R : Type) [CommRing R] (a a' k : ℕ) (Φ : Matrix (Fin a) (Fin a) R) (Φ' : Matrix (Fin a') (Fin a') R) (x : R) (rel : ∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B], (Fin a → B) → (Fin a' → B) → Prop) (t : ∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B], (Fin a' → B) → Fin k → B), (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u u' : Fin a → B) (w : Fin a' → B), matAct Φ u = 0 → matAct Φ u' = 0 → rel B u w → rel B u' w → u = u') → (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u : Fin a → B) (w w' : Fin a' → B), matAct Φ' w = 0 → matAct Φ' w' = 0 → rel B u w → rel B u w' → w = w') → (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (u : Fin a → B), matAct Φ u = 0 → ∃ w : Fin a' → B, matAct Φ' w = 0 ∧ rel B u w ∧ t B w = 0) → (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (w : Fin a' → B), matAct Φ' w = 0 → t B w = 0 → ∃ u : Fin a → B, matAct Φ u = 0 ∧ rel B u w) → (∀ (B : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] (w : Fin a' → B), matAct Φ' w = 0 → ∀ j, x • t B w j = 0) → (∀ (B B' : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] [AddCommGroup B'] [Module R B'] [TopologicalSpace B'] [DiscreteTopology B'] (f : B →ₗ[R] B') (u : Fin a → B) (w : Fin a' → B), matAct Φ u = 0 → matAct Φ' w = 0 → rel B u w → rel B' (fun c => f (u c)) (fun c => f (w c))) → (∀ (B B' : Type) [AddCommGroup B] [Module R B] [TopologicalSpace B] [DiscreteTopology B] [AddCommGroup B'] [Module R B'] [TopologicalSpace B'] [DiscreteTopology B'] (f : B →ₗ[R] B') (w : Fin a' → B), matAct Φ' w = 0 → t B' (fun c => f (w c)) = fun j => f (t B w j)) → ∃ v : Fin k → ((Fin a' → R) ⧸ LinearMap.range Φ'.transpose.mulVecLin), (∀ j, x • v j = 0) ∧ Nonempty ((((Fin a' → R) ⧸ LinearMap.range Φ'.transpose.mulVecLin) ⧸ Submodule.span R (Set.range v)) ≃ₗ[R] ((Fin a → R) ⧸ LinearMap.range Φ.transpose.mulVecLin)) := by
  intro R _ a a' k Φ Φ' x rel t H1 H2 H3 H4 H5 H6 H7

  let _ : TopologicalSpace (Cok Φ) := ⊥
  have : DiscreteTopology (Cok Φ) := ⟨rfl⟩
  let _ : TopologicalSpace (Cok Φ') := ⊥
  have : DiscreteTopology (Cok Φ') := ⟨rfl⟩

  obtain ⟨v, hv⟩ : ∃ v : Fin k → Cok Φ', v = t (Cok Φ') (univ Φ') := ⟨_, rfl⟩
  refine ⟨v, fun j => by rw [hv]; exact H5 _ _ (univ_ker Φ') j, ?_⟩
  obtain ⟨S, hS⟩ : ∃ S : Submodule R (Cok Φ'), S = Submodule.span R (Set.range v) := ⟨_, rfl⟩
  rw [← hS]
  let _ : TopologicalSpace (Cok Φ' ⧸ S) := ⊥
  have : DiscreteTopology (Cok Φ' ⧸ S) := ⟨rfl⟩

  have hw0 : matAct Φ' (fun c => S.mkQ (univ Φ' c)) = 0 := map_ker Φ' S.mkQ (univ Φ') (univ_ker Φ')
  have ht0 : t (Cok Φ' ⧸ S) (fun c => S.mkQ (univ Φ' c)) = 0 := by
    rw [H7 (Cok Φ') (Cok Φ' ⧸ S) S.mkQ (univ Φ') (univ_ker Φ'), ← hv]
    funext j
    simp only [Submodule.mkQ_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
    rw [hS]
    exact Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨u0, hu0, hr0⟩ := H4 _ _ hw0 ht0
  obtain ⟨φ, hφ⟩ := exists_lift Φ u0 hu0

  obtain ⟨w1, hw1, hr1, ht1⟩ := H3 (Cok Φ) (univ Φ) (univ_ker Φ)
  obtain ⟨ψ0, hψ0⟩ := exists_lift Φ' w1 hw1
  have hψ0v : S ≤ LinearMap.ker ψ0 := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hv]
    have h := H7 (Cok Φ') (Cok Φ) ψ0 (univ Φ') (univ_ker Φ')
    rw [show (fun c => ψ0 (univ Φ' c)) = w1 from funext hψ0, ht1] at h
    exact (congrFun h j).symm
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (Cok Φ' ⧸ S) →ₗ[R] Cok Φ, ∀ c, ψ (S.mkQ (univ Φ' c)) = w1 c :=
    ⟨S.liftQ ψ0 hψ0v, fun c => by rw [Submodule.mkQ_apply, Submodule.liftQ_apply, hψ0]⟩

  have e1 : ψ.comp φ = LinearMap.id := by
    apply hom_ext Φ
    intro c
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hφ]
    have hk : matAct Φ (fun c => ψ (u0 c)) = 0 := map_ker Φ ψ u0 hu0
    have hr := H6 (Cok Φ' ⧸ S) (Cok Φ) ψ u0 (fun c => S.mkQ (univ Φ' c)) hu0 hw0 hr0
    simp only [hψ] at hr
    exact congrFun (H1 (Cok Φ) _ _ w1 hk (univ_ker Φ) hr hr1) c
  have e2 : φ.comp ψ = LinearMap.id := by
    apply Submodule.linearMap_qext
    apply hom_ext Φ'
    intro c
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hψ]
    have hk : matAct Φ' (fun c => φ (w1 c)) = 0 := map_ker Φ' φ w1 hw1
    have hr := H6 (Cok Φ) (Cok Φ' ⧸ S) φ (univ Φ) w1 (univ_ker Φ) hw1 hr1
    simp only [hφ] at hr
    exact congrFun (H2 _ u0 _ _ hk hw0 hr hr0) c
  exact ⟨LinearEquiv.ofLinearMap ψ φ e1 e2⟩

end GlobalTheory.MatKerCokernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcreteProjectorEqOrthogonalProjection
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin Formalism.DivisionValues

noncomputable section

namespace GlobalTheory.EtaJoin

section Gen

variable {K : Type} [Field K] [StarRing K] {n d : ℕ}

theorem hform_eq_dot (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    hform H x y = star x ⬝ᵥ H.mulVec y := by
  simp only [hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, RingHom.id_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [starRingEnd_apply, Pi.star_apply]; ring

theorem hform_orthProj (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K)
    (h : IsOrthProj H E Pr) (u : Fin d → K) (x : Fin n → K) :
    hform H (E.mulVec u) (x - E.mulVec (Pr.mulVec x)) = 0 := by
  have e : x - E.mulVec (Pr.mulVec x) = (1 - E * Pr).mulVec x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
  rw [hform_eq_dot, e, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    h.2, Matrix.zero_mulVec, dotProduct_zero]

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (J : (Fin n → K) →ₛₗ[σ] W)

theorem semi_expand (y : Fin n → K) : J y = ∑ i, σ (y i) • J (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (y i) : Fin n → K) = y i • Pi.single i 1 := by
    ext k; by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  rw [this, LinearMap.map_smulₛₗ]

theorem semi_injective (hli : LinearIndependent ℂ fun i => J (Pi.single i 1)) : Function.Injective J := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  rw [semi_expand σ J y] at hy
  have h0 := (Fintype.linearIndependent_iff.1 hli) (fun i => σ (y i)) hy
  funext i
  exact σ.injective (by rw [h0 i]; simp)

theorem semi_mulVec_mem (E : Matrix (Fin n) (Fin d) K) (c : Fin d → K) :
    J (E.mulVec c) ∈ Submodule.span ℂ (Set.range fun k => J (E.mulVec (Pi.single k 1))) := by
  have e : E.mulVec c = ∑ k, c k • E.mulVec (Pi.single k 1) := by
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Matrix.mulVec_smul]
    congr 1
    ext a; by_cases ha : a = k
    · subst ha; simp
    · simp [Pi.single_apply, ha]
  rw [e, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end Gen

end GlobalTheory.EtaJoin

namespace GlobalTheory.EtaJoin

section Gen2

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n d : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {σ : K →+* ℂ} {V : Type} [AddCommGroup V] [Module K V]

theorem tied_orthProj (e : (Fin n → K) ≃ₗ[K] V) (jV : V →ₛₗ[σ] W) (H Eop : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W)
    (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K) (hP : IsOrthProj H E Pr)
    (hF : FormsTie σ (jV.comp e.toLinearMap) H Eop op) (Z : Submodule ℂ W)
    (hZ : Z = Submodule.span ℂ (Set.range fun k => jV (e (E.mulVec (Pi.single k 1))))) :
    Function.Injective (e.toLinearMap ∘ₗ E.mulVecLin) ∧ Z.comap jV = LinearMap.range (e.toLinearMap ∘ₗ E.mulVecLin) ∧
      ∀ x, e x - (e.toLinearMap ∘ₗ E.mulVecLin) (Pr.mulVec x) ∈ (Zᗮ).comap jV := by
  have hin : ∀ x y, inner ℂ (jV (e x)) (jV (e y)) = σ (hform H x y) := hF.inner
  have hJinj : Function.Injective fun x => jV (e x) := fun a b h => semi_injective σ (jV.comp e.toLinearMap) hF.li h
  have hgen : ∀ c, jV (e (E.mulVec c)) ∈ Z := by
    intro c; rw [hZ]; exact semi_mulVec_mem σ (jV.comp e.toLinearMap) E c
  have horth : ∀ x, jV (e (x - E.mulVec (Pr.mulVec x))) ∈ Zᗮ := by
    intro x
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [hZ] at hu
    induction hu using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k, rfl⟩ := hv
      show inner ℂ (jV (e (E.mulVec (Pi.single k 1)))) _ = 0
      rw [hin, hform_orthProj _ _ _ hP, map_zero]
    | zero => exact inner_zero_left _
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  have hEinj : Function.Injective E.mulVec := by
    intro a b hab
    have := congrArg Pr.mulVec hab
    simp only [Matrix.mulVec_mulVec, hP.1, Matrix.one_mulVec] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · exact e.injective.comp hEinj
  · ext y
    constructor
    · intro hy
      rw [Submodule.mem_comap] at hy
      obtain ⟨x, rfl⟩ := e.surjective y
      have hw1 : jV (e (x - E.mulVec (Pr.mulVec x))) ∈ Z := by
        rw [map_sub, map_sub]; exact Submodule.sub_mem _ hy (hgen _)
      have hw0 : jV (e (x - E.mulVec (Pr.mulVec x))) = 0 :=
        inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 (horth x) _ hw1)
      have hw : x = E.mulVec (Pr.mulVec x) := by
        refine sub_eq_zero.1 (hJinj ?_)
        simp only [map_zero]; exact hw0
      exact ⟨Pr.mulVec x, by simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe]; rw [← hw]⟩
    · rintro ⟨c, rfl⟩
      exact hgen c
  · intro x
    rw [Submodule.mem_comap]
    have e1 : e x - (e.toLinearMap ∘ₗ E.mulVecLin) (Pr.mulVec x) = e (x - E.mulVec (Pr.mulVec x)) := by
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe, map_sub]
    rw [e1]; exact horth x

end Gen2

theorem concreteProj_orth : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1)))) → Function.Injective ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1)) = LinearMap.range ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ∀ x, eMt i t x - ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ((lPrj D A P ψ Zs i t).mulVec x) ∈ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk i t hF hZ
  have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.fam.v0 s := ⟨hOk.conj, fun χ hχ => hOk.irr χ hχ, hOk.lifts i t⟩
  have hP : IsOrthProj (lH D A P ψ i t) (lZ0 D A P ψ Zs i t) (lPrj D A P ψ Zs i t) :=
    BlockDat.lf_l_proj (Z := Zs.Zl i t) hB
  exact tied_orthProj (eMt i t) (D.what₂.jMt (tup t) ((i : ℕ) + 1)) _ _ _ _ _ hP hF _ hZ

end GlobalTheory.EtaJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorExponentAtPlaces
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.ExpCond

theorem not_mem_sq_of_not_dvd_discr {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E)
    (w : HeightOneSpectrum (𝓞 E)) (hv : (p : 𝓞 E) ∈ w.asIdeal) : (p : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  intro h2
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hvZ : ((p : ℤ) : 𝓞 E) ∈ w.asIdeal := by simpa using hv
  have hun : Algebra.IsUnramifiedAt ℤ w.asIdeal :=
    (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hpZ).mp hd w.asIdeal w.isPrime hvZ
  have hunder : w.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    symm
    refine (PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible).eq_of_le
      (Ideal.IsPrime.under ℤ w.asIdeal).ne_top ?_
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_comap.mpr (by simpa using hv)
  let := Localization.AtPrime.algebraOfLiesOver (w.asIdeal.under ℤ) w.asIdeal
  have hloc := ((Algebra.isUnramifiedAt_iff_map_eq ℤ (w.asIdeal.under ℤ) w.asIdeal).mp hun).2
  have h1 := (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff w.ne_bot Ideal.map_comap_le).mpr hloc
  refine (Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le).mpr ?_ h1
  have hunder' : Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal = Ideal.span {(p : ℤ)} := hunder
  rw [hunder', Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
  simpa using h2

variable {E : Type} [Field E] [NumberField E]

theorem mem_below (w : HeightOneSpectrum (𝓞 E)) (p : ℕ) : (p : OF E) ∈ (below w).asIdeal ↔ (p : 𝓞 E) ∈ w.asIdeal := by
  show (p : OF E) ∈ Ideal.comap (algebraMap (OF E) (𝓞 E)) w.asIdeal ↔ _
  rw [Ideal.mem_comap, map_natCast]

theorem emult_zero (w : HeightOneSpectrum (𝓞 E)) {p : ℕ} (h : (p : 𝓞 E) ∉ w.asIdeal) :
    emultiplicity (below w).asIdeal (Ideal.span {(p : OF E)}) = 0 := by
  rw [emultiplicity_eq_zero, Ideal.dvd_span_singleton, mem_below]
  exact h

theorem emult_one (w : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E) (h : (p : 𝓞 E) ∈ w.asIdeal) :
    emultiplicity (below w).asIdeal (Ideal.span {(p : OF E)}) = 1 := by
  have hle : Ideal.map (algebraMap (OF E) (𝓞 E)) (below w).asIdeal ≤ w.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr (fun x hx => hx)
  have hdvd : (below w).asIdeal ^ 1 ∣ Ideal.span {(p : OF E)} := by
    rw [pow_one, Ideal.dvd_span_singleton, mem_below]
    exact h
  have hndvd : ¬ (below w).asIdeal ^ (1 + 1) ∣ Ideal.span {(p : OF E)} := by
    intro h2
    rw [Ideal.dvd_span_singleton] at h2
    have hm := Ideal.mem_map_of_mem (algebraMap (OF E) (𝓞 E)) h2
    rw [Ideal.map_pow, map_natCast] at hm
    have hsq : (Ideal.map (algebraMap (OF E) (𝓞 E)) (below w).asIdeal) ^ (1 + 1) ≤ w.asIdeal ^ 2 := by
      rw [show (1 + 1 : ℕ) = 2 from rfl, pow_two, pow_two]
      exact Ideal.mul_mono hle hle
    exact not_mem_sq_of_not_dvd_discr hp hd w h (hsq hm)
  have := (emultiplicity_eq_coe (n := 1)).mpr ⟨hdvd, hndvd⟩
  simpa using this

theorem not_mem_of_ne (w : HeightOneSpectrum (𝓞 E)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h : (p : 𝓞 E) ∈ w.asIdeal) : (q : 𝓞 E) ∉ w.asIdeal := by
  intro hq'
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)
  obtain ⟨u, v, huv⟩ := hc
  have e : (u : 𝓞 E) * (p : 𝓞 E) + (v : 𝓞 E) * (q : 𝓞 E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 E) huv
    push_cast at this
    exact this
  have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
    rw [← e]
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h) (w.asIdeal.mul_mem_left _ hq')
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem emult_cond (v v0 : HeightOneSpectrum (OF E)) (a b c d : ℕ) :
    emultiplicity v.asIdeal (Ideal.span {((a * b * c * d : ℕ) : OF E)} ^ 2 * v0.asIdeal) =
      2 * (emultiplicity v.asIdeal (Ideal.span {(a : OF E)}) + emultiplicity v.asIdeal (Ideal.span {(b : OF E)}) +
        emultiplicity v.asIdeal (Ideal.span {(c : OF E)}) + emultiplicity v.asIdeal (Ideal.span {(d : OF E)})) +
        emultiplicity v.asIdeal v0.asIdeal := by
  have hv := v.prime
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton,
    ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
    emultiplicity_mul hv, emultiplicity_pow hv, emultiplicity_mul hv, emultiplicity_mul hv,
    emultiplicity_mul hv]
  push_cast
  ring

theorem emult_ne {v v0 : HeightOneSpectrum (OF E)} (h : v ≠ v0) : emultiplicity v.asIdeal v0.asIdeal = 0 := by
  rw [emultiplicity_eq_zero, Ideal.dvd_iff_le]
  intro hle
  apply h
  exact HeightOneSpectrum.ext ((v0.isMaximal.eq_of_le v.isPrime.ne_top hle).symm)

theorem emult_self (v : HeightOneSpectrum (OF E)) : emultiplicity v.asIdeal v.asIdeal = 1 := by
  simpa using emultiplicity_pow_self_of_prime v.prime 1

end GlobalTheory.LamTie.ExpCond

namespace GlobalTheory.LamTie

open ExpCond

theorem expIn_cond0 : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), PlacesOk H q0 w0 →
    ∀ w : HeightOneSpectrum (𝓞 H.E), (Over4 H w → expIn (cond0 H w0) (below w) = 2) ∧
      (below w = below w0 → ¬ Over4 H w ∧ expIn (cond0 H w0) (below w) = 1) ∧
      (¬ Over4 H w → below w ≠ below w0 → expIn (cond0 H w0) (below w) = 0) := by
  intro R H q0 w0 hP w
  obtain ⟨hw0, hdist, hspl⟩ := hP
  have hq0 : (q0 : 𝓞 H.E) ∈ w0.asIdeal := hw0
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, not_or, or_false] at hdist
  have pr : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime := fun p hp => (hspl p hp).1
  have dc : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ¬ (p : ℤ) ∣ discr H.E := fun p hp => (hspl p hp).2.2.1
  have uniq : ∀ x ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ∀ y ∈ [H.g 0, H.g 1, H.pde, H.pde', q0],
      (x : 𝓞 H.E) ∈ w.asIdeal → (y : 𝓞 H.E) ∈ w.asIdeal → x = y := by
    intro x hx y hy mx my
    by_contra hxy
    exact not_mem_of_ne w (pr x hx) (pr y hy) hxy mx my
  have key : emultiplicity (below w).asIdeal (cond0 H w0) =
      2 * (emultiplicity (below w).asIdeal (Ideal.span {(H.g 0 : OF H.E)}) +
        emultiplicity (below w).asIdeal (Ideal.span {(H.g 1 : OF H.E)}) +
        emultiplicity (below w).asIdeal (Ideal.span {(H.pde : OF H.E)}) +
        emultiplicity (below w).asIdeal (Ideal.span {(H.pde' : OF H.E)})) +
      emultiplicity (below w).asIdeal (below w0).asIdeal :=
    emult_cond (below w) (below w0) (H.g 0) (H.g 1) H.pde H.pde'
  have qw : below w = below w0 → (q0 : 𝓞 H.E) ∈ w.asIdeal := fun heq =>
    (mem_below w q0).mp (heq ▸ (mem_below w0 q0).mpr hq0)
  have toExp : ∀ n : ℕ, emultiplicity (below w).asIdeal (cond0 H w0) = n → expIn (cond0 H w0) (below w) = n :=
    fun n h => multiplicity_eq_of_emultiplicity_eq_some h
  have m0 : (H.g 0 : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 0 : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have m1 : (H.g 1 : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 1 : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have m2 : (H.pde : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have m3 : (H.pde' : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde' : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have n0 : (H.g 0 : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 0 : OF H.E)}) = 0 :=
    emult_zero w
  have n1 : (H.g 1 : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 1 : OF H.E)}) = 0 :=
    emult_zero w
  have n2 : (H.pde : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde : OF H.E)}) = 0 :=
    emult_zero w
  have n3 : (H.pde' : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde' : OF H.E)}) = 0 :=
    emult_zero w
  have u := fun x (hx : x ∈ [H.g 0, H.g 1, H.pde, H.pde', q0]) y (hy : y ∈ [H.g 0, H.g 1, H.pde, H.pde', q0])
    (hne : x ≠ y) (mx : (x : 𝓞 H.E) ∈ w.asIdeal) (my : (y : 𝓞 H.E) ∈ w.asIdeal) => hne (uniq x hx y hy mx my)
  refine ⟨fun hO => ?_, fun heq => ?_, fun hO hne => ?_⟩
  · have hne : below w ≠ below w0 := by
      intro heq
      have hq := qw heq
      rcases hO with ⟨k, hk⟩ | hk | hk
      · fin_cases k
        · have hk : (H.g 0 : 𝓞 H.E) ∈ w.asIdeal := hk
          exact u _ (by simp) _ (by simp) (by omega) hk hq
        · have hk : (H.g 1 : 𝓞 H.E) ∈ w.asIdeal := hk
          exact u _ (by simp) _ (by simp) (by omega) hk hq
      · exact u _ (by simp) _ (by simp) (by omega) hk hq
      · exact u _ (by simp) _ (by simp) (by omega) hk hq
    apply toExp
    rw [key, emult_ne hne]
    rcases hO with ⟨k, hk⟩ | hk | hk
    · fin_cases k
      · have hk : (H.g 0 : 𝓞 H.E) ∈ w.asIdeal := hk
        rw [m0 hk, n1 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n2 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n3 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
        norm_num
      · have hk : (H.g 1 : 𝓞 H.E) ∈ w.asIdeal := hk
        rw [m1 hk, n0 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n2 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n3 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
        norm_num
    · have hk : (H.pde : 𝓞 H.E) ∈ w.asIdeal := hk
      rw [m2 hk, n0 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n1 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n3 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
      norm_num
    · have hk : (H.pde' : 𝓞 H.E) ∈ w.asIdeal := hk
      rw [m3 hk, n0 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n1 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n2 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
      norm_num
  · have hq := qw heq
    have a0 : (H.g 0 : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    have a1 : (H.g 1 : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    have a2 : (H.pde : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    have a3 : (H.pde' : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    refine ⟨?_, ?_⟩
    · rintro (⟨k, hk⟩ | hk | hk)
      · fin_cases k
        · exact a0 hk
        · exact a1 hk
      · exact a2 hk
      · exact a3 hk
    · apply toExp
      rw [key, n0 a0, n1 a1, n2 a2, n3 a3, heq, emult_self]
      norm_num
  · have a0 : (H.g 0 : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inl ⟨0, h⟩)
    have a1 : (H.g 1 : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inl ⟨1, h⟩)
    have a2 : (H.pde : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inr (Or.inl h))
    have a3 : (H.pde' : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inr (Or.inr h))
    apply toExp
    rw [key, n0 a0, n1 a1, n2 a2, n3 a3, emult_ne hne]
    norm_num

end GlobalTheory.LamTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicFrobeniusSystemContinuationOpenDiscStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicFrobenius_system_continuation_open_disc : ∀ (l : ℕ) [Fact l.Prime], ∀ (LL : FinExt l) (s r n M : ℕ) [NeZero n], 1 ≤ s → ∀ (t τ : PowerSeries ↥LL.1), PowerSeries.constantCoeff t = 0 → (1 + PowerSeries.X) * PowerSeries.derivative ↥LL.1 t = 1 → XX l ↥LL.1 s * τ = t → ∀ (U : ZMod n → Matrix (Fin r) (Fin r) (PowerSeries ↥LL.1)) (Pm : ZMod n → Matrix (Fin r) (Fin r) (PowerSeries ↥(OL LL))) (Cm : ZMod n → Matrix (Fin r) (Fin r) ↥LL.1) (ρ : ℝ), 0 < ρ → (∀ i, QQ l ↥LL.1 s ^ M • U i = (Pm i).map (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1)) * (U (i - 1)).map (phi l ↥LL.1) * (Cm i).map PowerSeries.C) → (∀ i a b, (∀ r : ℝ, 0 < r → r < ρ → Filter.Tendsto (fun k : ℕ => ‖((PowerSeries.coeff k (U i a b) : ↥LL.1) : Om l)‖ * r ^ k) Filter.atTop (nhds 0))) → ∀ i a b, (∀ r : ℝ, 0 < r → r < 1 → Filter.Tendsto (fun k : ℕ => ‖((PowerSeries.coeff k (τ ^ M * U i a b) : ↥LL.1) : Om l)‖ * r ^ k) Filter.atTop (nhds 0)) := by
  first | exact @GlobalTheory.Cyc.continuation_to_open_disc | exact GlobalTheory.Cyc.continuation_to_open_disc | (intros; apply GlobalTheory.Cyc.continuation_to_open_disc <;> assumption)
end

