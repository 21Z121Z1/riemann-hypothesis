import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0526
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.PExpbSt

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirSignatureMemCenter
section
noncomputable section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.CasFamily

theorem sum_squares_eq {A : Type} [Ring A] [Algebra ℂ A] {a : ℕ} (X Y : Fin a → Fin a → A) :
    ∑ i, ∑ j, ((X i j + X j i) * (X i j + X j i) - (X i j - X j i) * (X i j - X j i) +
        ((Y i j - Y j i) * (Y i j - Y j i) - (Y i j + Y j i) * (Y i j + Y j i))) =
      (8 : ℂ) • (Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j - Complex.I • Y i j)) +
        Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j + Complex.I • Y i j))) := by
  have h1 : ∀ i j, (X i j + X j i) * (X i j + X j i) - (X i j - X j i) * (X i j - X j i) +
      ((Y i j - Y j i) * (Y i j - Y j i) - (Y i j + Y j i) * (Y i j + Y j i)) =
      (2 : ℂ) • (X i j * X j i) + (2 : ℂ) • (X j i * X i j) -
        ((2 : ℂ) • (Y i j * Y j i) + (2 : ℂ) • (Y j i * Y i j)) := by
    intro i j
    simp only [add_mul, mul_add, sub_mul, mul_sub]
    match_scalars <;> ring
  have h2 : ∀ i j, ((1 / 2 : ℂ) • (X i j - Complex.I • Y i j)) * ((1 / 2 : ℂ) • (X j i - Complex.I • Y j i)) +
      ((1 / 2 : ℂ) • (X i j + Complex.I • Y i j)) * ((1 / 2 : ℂ) • (X j i + Complex.I • Y j i)) =
      (1 / 2 : ℂ) • (X i j * X j i) - (1 / 2 : ℂ) • (Y i j * Y j i) := by
    intro i j
    simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, sub_mul, mul_sub, smul_add, smul_sub, smul_smul]
    match_scalars <;> ring_nf <;> simp <;> norm_num
  have hX : ∑ i, ∑ j, X j i * X i j = ∑ i, ∑ j, X i j * X j i := Finset.sum_comm
  have hY : ∑ i, ∑ j, Y j i * Y i j = ∑ i, ∑ j, Y i j * Y j i := Finset.sum_comm
  have hc : Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j - Complex.I • Y i j)) +
      Formalism.REAL.Cas (fun i j => (1 / 2 : ℂ) • (X i j + Complex.I • Y i j)) =
      ∑ i, ∑ j, ((1 / 2 : ℂ) • (X i j * X j i) - (1 / 2 : ℂ) • (Y i j * Y j i)) := by
    simp only [Formalism.REAL.Cas, ← Finset.sum_add_distrib, h2]
  rw [hc]
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum, hX, hY]
  match_scalars <;> norm_num

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def sgl (i j : Fin a) : Cinf E →ₗ[ℝ] Lie E a :=
  (Matrix.singleLinearMap ℝ i j : Cinf E →ₗ[ℝ] Matrix (Fin a) (Fin a) (Cinf E))

def eW (w : InfinitePlace E) : Cinf E := atEmb w.embedding 1

def fW (w : InfinitePlace E) : Cinf E := atEmb w.embedding Complex.I

omit [NumberField E] [IsTotallyComplex E] in
open Classical in
theorem atEmb_embedding_apply (w v : InfinitePlace E) (z : ℂ) :
    atEmb w.embedding z v = if v = w then z else 0 := by
  unfold atEmb
  rw [InfinitePlace.mk_embedding, if_pos rfl, Pi.single_apply]

omit [NumberField E] [IsTotallyComplex E] in
theorem star_atEmb (w : InfinitePlace E) (z : ℂ) :
    star (atEmb w.embedding z) = atEmb w.embedding (starRingEnd ℂ z) := by
  classical
  funext v
  rw [Pi.star_apply, atEmb_embedding_apply, atEmb_embedding_apply]
  split_ifs <;> simp

omit [NumberField E] [IsTotallyComplex E] in
theorem star_eW (w : InfinitePlace E) : star (eW w) = eW w := by
  simp [eW, star_atEmb]

omit [NumberField E] [IsTotallyComplex E] in
theorem star_fW (w : InfinitePlace E) : star (fW w) = -fW w := by
  classical
  funext v
  simp only [fW, star_atEmb, Pi.neg_apply, atEmb_embedding_apply]
  split_ifs <;> simp

omit [IsTotallyComplex E] in
theorem sum_atEmb (x : Cinf E) : x = ∑ w, ((x w).re • eW w + (x w).im • fW w) := by
  classical
  have e : ∀ w, (x w).re • eW w + (x w).im • fW w = atEmb w.embedding (x w) := fun w =>
    (atEmb_eq _ _).symm
  simp only [e]
  funext v
  simp [Finset.sum_apply, atEmb_embedding_apply]

def famZ : InfinitePlace E × Fin a × Fin a × Bool × Bool → Lie E a
  | (w, i, j, false, false) => sgl i j (eW w) + sgl j i (eW w)
  | (w, i, j, false, true) => sgl i j (eW w) - sgl j i (eW w)
  | (w, i, j, true, false) => sgl i j (fW w) - sgl j i (fW w)
  | (w, i, j, true, true) => sgl i j (fW w) + sgl j i (fW w)

theorem span_famZ : Submodule.span ℝ (Set.range (famZ (E := E) (a := a))) = ⊤ := by
  set S := Submodule.span ℝ (Set.range (famZ (E := E) (a := a))) with hS
  have hz : ∀ k, famZ (E := E) (a := a) k ∈ S := fun k => Submodule.subset_span ⟨k, rfl⟩
  have hE : ∀ w i j, sgl (E := E) (a := a) i j (eW w) ∈ S := fun w i j => by
    have e : sgl (E := E) (a := a) i j (eW w) =
        (1 / 2 : ℝ) • (famZ (w, i, j, false, false) + famZ (w, i, j, false, true)) := by
      change _ = (1 / 2 : ℝ) • ((sgl i j (eW w) + sgl j i (eW w)) + (sgl i j (eW w) - sgl j i (eW w)))
      module
    rw [e]
    exact S.smul_mem _ (S.add_mem (hz _) (hz _))
  have hF : ∀ w i j, sgl (E := E) (a := a) i j (fW w) ∈ S := fun w i j => by
    have e : sgl (E := E) (a := a) i j (fW w) =
        (1 / 2 : ℝ) • (famZ (w, i, j, true, false) + famZ (w, i, j, true, true)) := by
      change _ = (1 / 2 : ℝ) • ((sgl i j (fW w) - sgl j i (fW w)) + (sgl i j (fW w) + sgl j i (fW w)))
      module
    rw [e]
    exact S.smul_mem _ (S.add_mem (hz _) (hz _))
  have hx : ∀ i j (x : Cinf E), sgl (a := a) i j x ∈ S := fun i j x => by
    rw [sum_atEmb x, map_sum]
    refine S.sum_mem fun w _ => ?_
    rw [map_add, map_smul, map_smul]
    exact S.add_mem (S.smul_mem _ (hE w i j)) (S.smul_mem _ (hF w i j))
  refine eq_top_iff.2 fun L _ => ?_
  have e : L = ∑ i, ∑ j, sgl i j (L i j) := Matrix.matrix_eq_sum_single (Matrix.of L)
  rw [e]
  exact S.sum_mem fun i _ => S.sum_mem fun j _ => hx i j _

theorem conjTranspose_sgl (i j : Fin a) (x : Cinf E) :
    (Matrix.of (sgl i j x))ᴴ = Matrix.of (sgl j i (star x)) :=
  Matrix.conjTranspose_single i j x

theorem skew_famZ (k : InfinitePlace E × Fin a × Fin a × Bool × Bool) (hk : k.2.2.2.2 = true) :
    (Matrix.of (famZ k))ᴴ = -(Matrix.of (famZ k)) := by
  obtain ⟨w, i, j, b, c⟩ := k
  obtain rfl : c = true := hk
  cases b
  · change (Matrix.of (sgl i j (eW w)) - Matrix.of (sgl j i (eW w)))ᴴ =
      -(Matrix.of (sgl i j (eW w)) - Matrix.of (sgl j i (eW w)))
    rw [Matrix.conjTranspose_sub, conjTranspose_sgl, conjTranspose_sgl, star_eW, neg_sub]
  · change (Matrix.of (sgl i j (fW w)) + Matrix.of (sgl j i (fW w)))ᴴ =
      -(Matrix.of (sgl i j (fW w)) + Matrix.of (sgl j i (fW w)))
    have hn : ∀ i j : Fin a, Matrix.of (sgl i j (-fW w)) = -Matrix.of (sgl i j (fW w)) := fun i j => by
      rw [map_neg]; rfl
    rw [Matrix.conjTranspose_add, conjTranspose_sgl, conjTranspose_sgl, star_fW, hn, hn, neg_add, add_comm]

theorem Eop_embedding (w : InfinitePlace E) (i j : Fin a) :
    Eop w.embedding i j = (1 / 2 : ℂ) • (lieS E a i j (eW w) - Complex.I • lieS E a i j (fW w)) := rfl

theorem Eop_conjugate (w : InfinitePlace E) (i j : Fin a) :
    Eop (ComplexEmbedding.conjugate w.embedding) i j =
      (1 / 2 : ℂ) • (lieS E a i j (eW w) + Complex.I • lieS E a i j (fW w)) := by
  have h : atEmb w.embedding (-Complex.I) = -fW w := by
    rw [atEmb_eq]; simp [fW]
  rw [Eop, atEmb_conj, atEmb_conj, map_one, Complex.conj_I, h, map_neg, smul_neg, sub_neg_eq_add]
  rfl

theorem sum_famZ [DecidableEq (InfinitePlace E)] :
    ∑ k ∈ (Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true)ᶜ,
        lie E a (famZ k) * lie E a (famZ k) -
      ∑ k ∈ Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true,
        lie E a (famZ k) * lie E a (famZ k) =
    ∑ w : InfinitePlace E, (8 : ℂ) • (Formalism.REAL.Cas (Eop (a := a) w.embedding) +
      Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate w.embedding))) := by
  have e : ∀ f : InfinitePlace E × Fin a × Fin a × Bool × Bool → Module.End ℂ (Sm E a),
      ∑ k ∈ (Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true)ᶜ, f k -
        ∑ k ∈ Finset.univ.filter fun k : InfinitePlace E × Fin a × Fin a × Bool × Bool => k.2.2.2.2 = true, f k =
      ∑ k, if k.2.2.2.2 = true then -f k else f k := fun f => by
    rw [Finset.compl_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : k.2.2.2.2 = true <;> simp [h]
  rw [e]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h := sum_squares_eq (fun i j : Fin a => lieS E a i j (eW w)) (fun i j => lieS E a i j (fW w))
  have c1 : Formalism.REAL.Cas (Eop (a := a) w.embedding) = Formalism.REAL.Cas (fun i j : Fin a =>
      (1 / 2 : ℂ) • (lieS E a i j (eW w) - Complex.I • lieS E a i j (fW w))) := rfl
  have c2 : Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate w.embedding)) = Formalism.REAL.Cas (fun i j : Fin a =>
      (1 / 2 : ℂ) • (lieS E a i j (eW w) + Complex.I • lieS E a i j (fW w))) :=
    congrArg _ (funext fun i => funext fun j => Eop_conjugate w i j)
  rw [c1, c2, ← h]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have f1 : lie E a (famZ (w, i, j, false, false)) = lieS E a i j (eW w) + lieS E a j i (eW w) := map_add _ _ _
  have f2 : lie E a (famZ (w, i, j, false, true)) = lieS E a i j (eW w) - lieS E a j i (eW w) := map_sub _ _ _
  have f3 : lie E a (famZ (w, i, j, true, false)) = lieS E a i j (fW w) - lieS E a j i (fW w) := map_sub _ _ _
  have f4 : lie E a (famZ (w, i, j, true, true)) = lieS E a i j (fW w) + lieS E a j i (fW w) := map_add _ _ _
  simp only [if_true, Bool.false_eq_true, if_false, f1, f2, f3, f4]
  abel

theorem exists_family : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Z : ι → GlobalTheory.CuspRep.Lie E a) (K : Finset ι), Submodule.span ℝ (Set.range Z) = ⊤ ∧ (∀ κ ∈ K, (Matrix.of (Z κ))ᴴ = -(Matrix.of (Z κ))) ∧ (∑ i ∈ Kᶜ, lie E a (Z i) * lie E a (Z i) - ∑ κ ∈ K, lie E a (Z κ) * lie E a (Z κ)) ∈ Zalg E a := by
  intro E _ _ _ a
  have : DecidableEq (InfinitePlace E) := Classical.decEq _
  refine ⟨InfinitePlace E × Fin a × Fin a × Bool × Bool, inferInstance, inferInstance, famZ,
    Finset.univ.filter fun k => k.2.2.2.2 = true, span_famZ, fun κ hκ => skew_famZ κ (Finset.mem_filter.1 hκ).2, ?_⟩
  rw [sum_famZ]
  exact Subalgebra.sum_mem _ fun w _ => Subalgebra.smul_mem _
    (Subalgebra.add_mem _ (GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg E a _) (GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg E a _)) _

end GlobalTheory.CompanionTheory.CasFamily
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterCommutesOneParameterFlow
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep.Flow

section Abstract

variable {A : Type} [Ring A] [Algebra ℂ A]

def HD (f f' : ℝ → A) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (p p' : ι → ℝ → ℂ) (C : ι → A),
    (∀ i s, HasDerivAt (p i) (p' i s) s) ∧ (∀ s, f s = ∑ i, p i s • C i) ∧ ∀ s, f' s = ∑ i, p' i s • C i

theorem HD.congr {f f' g g' : ℝ → A} (h : HD f f') (e : ∀ s, g s = f s) (e' : ∀ s, g' s = f' s) : HD g g' := by
  obtain ⟨ι, i, p, p', C, h1, h2, h3⟩ := h
  exact ⟨ι, i, p, p', C, h1, fun s => (e s).trans (h2 s), fun s => (e' s).trans (h3 s)⟩

theorem HD.const (C : A) : HD (fun _ => C) (fun _ => 0) :=
  ⟨Unit, inferInstance, fun _ _ => 1, fun _ _ => 0, fun _ => C, fun _ s => hasDerivAt_const s 1, by simp, by simp⟩

theorem HD.add {f f' g g' : ℝ → A} (h : HD f f') (k : HD g g') :
    HD (fun s => f s + g s) (fun s => f' s + g' s) := by
  obtain ⟨ι, _, p, p', C, h1, h2, h3⟩ := h
  obtain ⟨κ, _, q, q', D, k1, k2, k3⟩ := k
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim p q, Sum.elim p' q', Sum.elim C D, ?_, ?_, ?_⟩
  · rintro (i | j) s
    · exact h1 i s
    · exact k1 j s
  · intro s; simp [h2, k2]
  · intro s; simp [h3, k3]

theorem HD.mul {f f' g g' : ℝ → A} (h : HD f f') (k : HD g g') :
    HD (fun s => f s * g s) (fun s => f' s * g s + f s * g' s) := by
  obtain ⟨ι, _, p, p', C, h1, h2, h3⟩ := h
  obtain ⟨κ, _, q, q', D, k1, k2, k3⟩ := k
  refine ⟨ι × κ, inferInstance, fun x s => p x.1 s * q x.2 s,
    fun x s => p' x.1 s * q x.2 s + p x.1 s * q' x.2 s, fun x => C x.1 * D x.2, ?_, ?_, ?_⟩
  · intro x s; exact (h1 x.1 s).mul (k1 x.2 s)
  · intro s
    simp only [h2, k2, Finset.sum_mul_sum, Fintype.sum_prod_type, smul_mul_smul_comm]
  · intro s
    simp only [h2, h3, k2, k3, Finset.sum_mul_sum, Fintype.sum_prod_type, smul_mul_smul_comm, add_smul,
      Finset.sum_add_distrib]

theorem HD.const_of_zero {f : ℝ → A} (h : HD f (fun _ => 0)) (l : A →ₗ[ℂ] ℂ) (s t : ℝ) : l (f s) = l (f t) := by
  obtain ⟨ι, _, p, p', C, h1, h2, h3⟩ := h
  have hd : ∀ s, HasDerivAt (fun s => l (f s)) 0 s := by
    intro s
    have h4 : HasDerivAt (fun s => ∑ i, p i s * l (C i)) (∑ i, p' i s * l (C i)) s :=
      HasDerivAt.fun_sum fun i _ => (h1 i s).mul_const _
    have e1 : (fun s => l (f s)) = fun s => ∑ i, p i s * l (C i) := by
      funext s; simp [h2, map_sum]
    have e2 : ∑ i, p' i s * l (C i) = 0 := by
      have := congrArg l (h3 s)
      simpa [map_sum] using this.symm
    rw [e1]
    rwa [e2] at h4
  exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) s t

theorem hd_adjoin (R Q : ℝ → A) (hRQ : ∀ s, R s * Q s = 1) (hQR : ∀ s, Q s * R s = 1) (L : A) (G : Set A)
    (hG : ∀ B ∈ G, HD (fun s => R s * B * Q s) (fun s => R s * (L * B - B * L) * Q s)) :
    ∀ B ∈ Algebra.adjoin ℂ G, HD (fun s => R s * B * Q s) (fun s => R s * (L * B - B * L) * Q s) := by
  have hmul : ∀ s x y, R s * x * Q s * (R s * y * Q s) = R s * (x * y) * Q s := by
    intro s x y
    calc R s * x * Q s * (R s * y * Q s) = R s * x * (Q s * R s) * y * Q s := by simp only [mul_assoc]
      _ = R s * (x * y) * Q s := by rw [hQR]; simp only [mul_assoc, mul_one]
  intro B hB
  induction hB using Algebra.adjoin_induction with
  | mem x hx => exact hG x hx
  | algebraMap r =>
    refine (HD.const (algebraMap ℂ A r)).congr (fun s => ?_) (fun s => ?_)
    · rw [← Algebra.commutes, mul_assoc, hRQ, mul_one]
    · rw [Algebra.commutes, sub_self]; simp
  | add x y _ _ hx hy =>
    refine (hx.add hy).congr (fun s => ?_) (fun s => ?_)
    · noncomm_ring
    · noncomm_ring
  | mul x y _ _ hx hy =>
    refine (hx.mul hy).congr (fun s => ?_) (fun s => ?_)
    · rw [hmul]
    · rw [hmul, hmul, ← add_mul, ← mul_add]
      congr 2
      noncomm_ring

end Abstract

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem Zalg_le : Zalg E a ≤ Algebra.adjoin ℂ (Set.range (lie E a)) := by
  set S := Algebra.adjoin ℂ (Set.range (lie E a)) with hSdef
  have hL : ∀ X, lie E a X ∈ S := fun X => Algebra.subset_adjoin ⟨X, rfl⟩
  have hS : ∀ i j x, lieS E a i j x ∈ S := fun i j x => by rw [lieS_apply]; exact hL _
  have hE : ∀ (τ : E →+* ℂ) i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hS _ _ _) (S.smul_mem (hS _ _ _) _)) _
  refine Algebra.adjoin_le ?_
  rintro _ ⟨τ, u, rfl⟩
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem hd_lie {F F' : ℝ → Lie E a} (h : ∀ s, HasDerivAt F (F' s) s) :
    HD (fun s => lie E a (F s)) (fun s => lie E a (F' s)) := by
  classical
  let b := Module.finBasis ℝ (Lie E a)
  have hsum : ∀ X : Lie E a, lie E a X = ∑ m, ((b.repr X m : ℝ) : ℂ) • lie E a (b m) := by
    intro X
    conv_lhs => rw [← b.sum_repr X]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul]
    exact (algebraMap_smul ℂ _ _).symm
  refine ⟨_, inferInstance, fun m s => ((b.repr (F s) m : ℝ) : ℂ), fun m s => ((b.repr (F' s) m : ℝ) : ℂ),
    fun m => lie E a (b m), fun m s => ?_, fun s => hsum _, fun s => hsum _⟩
  have hl := (LinearMap.toContinuousLinearMap (b.coord m)).hasFDerivAt.comp_hasDerivAt s (h s)
  exact hl.ofReal_comp

theorem hasDerivAt_matMul {u v : ℝ → Lie E a} {u' v' : Lie E a} {s : ℝ} (hu : HasDerivAt u u' s)
    (hv : HasDerivAt v v' s) :
    HasDerivAt (fun t => toL (Matrix.of (u t) * Matrix.of (v t)))
      (toL (Matrix.of u' * Matrix.of (v s) + Matrix.of (u s) * Matrix.of v')) s := by
  rw [hasDerivAt_pi] at hu hv ⊢
  intro i
  rw [hasDerivAt_pi]
  intro j
  have hu' := fun k => (hasDerivAt_pi.1 (hu i)) k
  have hv' := fun k => (hasDerivAt_pi.1 (hv k)) j
  have := HasDerivAt.fun_sum (u := Finset.univ) fun k (_ : k ∈ Finset.univ) => (hu' k).mul (hv' k)
  simpa [Matrix.mul_apply, Finset.sum_add_distrib] using this

theorem zalg_comm_rt_curve : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ (g : GL (Fin a) (Cinf E)) (X : Lie E a), rt E a (infGL E a g) * lie E a X = lie E a (toL (g.val * Matrix.of X * (g⁻¹).val)) * rt E a (infGL E a g)) → ∀ z : Module.End ℂ (Sm E a), z ∈ Zalg E a → (∀ X : Lie E a, z * lie E a X = lie E a X * z) → ∀ (c : ℝ → GL (Fin a) (Cinf E)) (Y : Lie E a), c 0 = 1 → (∀ s, HasDerivAt (fun t => toL (c t).val) (toL ((c s).val * Matrix.of Y)) s) → (∀ s, HasDerivAt (fun t => toL ((c t)⁻¹).val) (toL (-(Matrix.of Y * ((c s)⁻¹).val))) s) → z * rt E a (infGL E a (c 1)) = rt E a (infGL E a (c 1)) * z := by
  intro E _ _ _ a hconj z hz hcomm c Y h0 hc hci
  let R : ℝ → Module.End ℂ (Sm E a) := fun s => rt E a (infGL E a (c s))
  let Q : ℝ → Module.End ℂ (Sm E a) := fun s => rt E a (infGL E a (c s)⁻¹)
  have hRQ : ∀ s, R s * Q s = 1 := fun s => by
    change rt E a _ * rt E a _ = 1
    rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
  have hQR : ∀ s, Q s * R s = 1 := fun s => by
    change rt E a _ * rt E a _ = 1
    rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
  have hconj' : ∀ s X, R s * lie E a X * Q s =
      lie E a (toL ((c s).val * Matrix.of X * ((c s)⁻¹).val)) := by
    intro s X
    change rt E a (infGL E a (c s)) * lie E a X * Q s = _
    rw [hconj (c s) X, mul_assoc]
    rw [show rt E a (infGL E a (c s)) * Q s = 1 from hRQ s, mul_one]
  have hG : ∀ B ∈ Set.range (lie E a), HD (fun s => R s * B * Q s)
      (fun s => R s * (lie E a Y * B - B * lie E a Y) * Q s) := by
    rintro _ ⟨X, rfl⟩
    let W : Lie E a := toL (Matrix.of Y * Matrix.of X - Matrix.of X * Matrix.of Y)
    have hW : lie E a Y * lie E a X - lie E a X * lie E a Y = lie E a W := by
      rw [lie_comm]
      exact (map_sub (lie E a) _ _).symm
    refine (hd_lie (F := fun s => toL ((c s).val * Matrix.of X * ((c s)⁻¹).val))
      (F' := fun s => toL ((c s).val * Matrix.of W * ((c s)⁻¹).val)) fun s => ?_).congr
      (fun s => hconj' s X) (fun s => by rw [hW]; exact hconj' s W)
    have h1 := hasDerivAt_matMul (hc s) (hasDerivAt_const s X)
    have h2 := hasDerivAt_matMul h1 (hci s)
    refine HasDerivAt.congr_deriv h2 ?_
    change toL (((c s).val * Matrix.of Y * Matrix.of X + (c s).val * 0) * ((c s)⁻¹).val +
      ((c s).val * Matrix.of X) * (-(Matrix.of Y * ((c s)⁻¹).val))) =
      toL ((c s).val * (Matrix.of Y * Matrix.of X - Matrix.of X * Matrix.of Y) * ((c s)⁻¹).val)
    congr 1
    noncomm_ring
  have h := hd_adjoin R Q hRQ hQR (lie E a Y) _ hG z (Zalg_le hz)
  have h' : HD (fun s => R s * z * Q s) (fun _ => 0) :=
    h.congr (fun _ => rfl) fun s => by rw [hcomm Y, sub_self, mul_zero, zero_mul]
  let l : Sm E a → GA E a → (Module.End ℂ (Sm E a) →ₗ[ℂ] ℂ) := fun φ x =>
    { toFun := fun B => (B φ).1 x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have e1 : R 1 * z * Q 1 = R 0 * z * Q 0 :=
    LinearMap.ext fun φ => Subtype.ext <| funext fun x => h'.const_of_zero (l φ x) 1 0
  have hR0 : R 0 = 1 := by
    change rt E a (infGL E a (c 0)) = 1
    rw [h0, map_one, map_one]
  have hQ0 : Q 0 = 1 := by
    change rt E a (infGL E a (c 0)⁻¹) = 1
    rw [h0, inv_one, map_one, map_one]
  rw [hR0, hQ0, one_mul, mul_one] at e1
  change z * R 1 = R 1 * z
  calc z * R 1 = R 1 * z * Q 1 * R 1 := by rw [e1]
    _ = R 1 * z * (Q 1 * R 1) := by simp only [mul_assoc]
    _ = R 1 * z := by rw [hQR, mul_one]

end GlobalTheory.CompanionTheory.SmoothRep.Flow
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterTracePairingEqInnerPsi
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Phase

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R S : Type} [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]

theorem repr_tmap (f : R →ₐ[F] S) {ι : Type} (b : Module.Basis ι F E) (z : R ⊗[F] E) (k : ι) :
    (Algebra.TensorProduct.basis S b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply, Algebra.smul_def]
  | add x y hx hy => simp [map_add, hx, hy]

theorem trace_tmap [Module.Finite F E] (f : R →ₐ[F] S) (z : R ⊗[F] E) :
    f (Algebra.trace R (R ⊗[F] E) z) =
      Algebra.trace S (S ⊗[F] E) (Algebra.TensorProduct.map f (AlgHom.id F E) z) := by
  classical
  let b := Module.Free.chooseBasis F E
  rw [Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis R b),
    Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis S b)]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← repr_tmap, map_mul]
  simp only [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq]

theorem tmap_sigR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (sigR R σ z) =
      sigR S σ (Algebra.TensorProduct.map f (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tmap_inclR (f : R →ₐ[F] S) (e : E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (inclR R e) = inclR S e := by
  simp [inclR]

theorem tmap_gramR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    (gramR R σ J X).map (Algebra.TensorProduct.map f (AlgHom.id F E)) =
      gramR S σ J (fun a i => Algebra.TensorProduct.map f (AlgHom.id F E) (X a i)) := by
  ext a c
  simp only [Matrix.map_apply, gramR, hR, Formalism.UG.hform, JR, map_sum, map_mul, tmap_sigR, tmap_inclR]

theorem tmap_phase [Module.Finite F E] (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (X : Fin n → Fin M → R ⊗[F] E) :
    f (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (Matrix.trace (B * gramR R σ J X))) =
      algebraMap F S (1 / 2) * Algebra.trace S (S ⊗[F] E)
        (Matrix.trace (B.map (Algebra.TensorProduct.map f (AlgHom.id F E)) *
          gramR S σ J (fun a i => Algebra.TensorProduct.map f (AlgHom.id F E) (X a i)))) := by
  rw [map_mul, AlgHom.commutes, trace_tmap, ← tmap_gramR]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul]

end Gen

theorem adelic_phase_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ)
  (b : HermR (AF F) σ n) (X : Fin n → Fin M → AF F ⊗[F] E),
  ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X))) =
    psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
      (Matrix.trace (((hermInf σ b : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) *
        gramR (Ainf F) σ J (projInf X)))) *
    psiFin F ψ (algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
      (Matrix.trace (((hermFin σ b : HermR (Af F) σ n) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) *
        gramR (Af F) σ J (projFin X)))) := by
  intro F E _ _ _ _ _ σ _ M J n ψ b X
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h1 := tmap_phase (fstA F) σ J (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) X
  have h2 := tmap_phase (sndA F) σ J (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) X
  have key : ∀ T : AF F, ψ T = psiInf F ψ (fstA F T) * psiFin F ψ (sndA F T) := by
    intro T
    simp only [psiInf, psiFin]
    rw [← AddChar.map_add_eq_mul]
    congr 1
    exact (Prod.fst_add_snd T).symm
  rw [key, h1, h2]
  rfl

end GlobalTheory.CompanionTheory.SiegelND.Integ.Phase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalDecompositionOfCompactStatement
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_decomposition_of_compact : (∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ), Continuous f → HasCompactSupport f → IsCompactOperator (repOp (Rcusp μ) μ f)) → GlobalTheory.Published.CuspDiscreteDecompositionGL := by
  first | exact @GlobalTheory.CompanionTheory.CuspGL.cuspDiscreteDecompositionGL_of_compact | exact GlobalTheory.CompanionTheory.CuspGL.cuspDiscreteDecompositionGL_of_compact | (intros; apply GlobalTheory.CompanionTheory.CuspGL.cuspDiscreteDecompositionGL_of_compact <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MkFiberStatement
section
open PositivityTheory.Rg.BcB.F.Tail.BS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_hecke_jacHk : JacHk := by
  first | exact @GlobalTheory.CompanionTheory.IwJac.jacHk | exact GlobalTheory.CompanionTheory.IwJac.jacHk | (intros; apply GlobalTheory.CompanionTheory.IwJac.jacHk <;> assumption)
end

