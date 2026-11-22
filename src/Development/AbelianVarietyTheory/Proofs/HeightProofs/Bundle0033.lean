import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0027
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPComplexMultiplicationCongruenceModPr
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.NormThetaFunctionPeriodicRealVariables
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockCompare.ThetaPeriod

variable {D : D7}

def mulRat (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) : AF D.host.F →+ WA V W where
  toFun a := Matrix.of fun i j => a ⊗ₜ[D.host.F] γ i j
  map_zero' := by ext i j; exact TensorProduct.zero_tmul _ _
  map_add' x y := by ext i j; exact TensorProduct.add_tmul _ _ _

theorem continuous_mulRat (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) :
    Continuous (mulRat V W γ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have e : (fun a : AF D.host.F => mulRat V W γ a i j) =
      fun a => a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] γ i j : AE D) := by
    funext a
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]; rfl
  rw [e]
  have : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  exact Continuous.smul (M := AF D.host.F) (X := AE D) (f := fun a : AF D.host.F => a) continuous_id continuous_const

theorem mulRat_one (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) :
    mulRat V W γ 1 = ratW V W γ := by
  ext i j; rfl

theorem ratW_nsmul (V W : HSp D) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (N : ℕ) :
    ratW V W (N • γ) = N • ratW V W γ := by
  ext i j
  exact (incA D).toAddMonoidHom.map_nsmul N (γ i j)

theorem norm_periodic (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (h : Chart θ σ)
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    (hU : ∀ U : AddSubgroup (AF D.host.F), IsOpen (U : Set (AF D.host.F)) →
      ∃ N : ℕ, 0 < N ∧ pairA D.host.F 0 (N : Af D.host.F) ∈ U)
    (V W : HSp D) (f : WA V W → ℂ) (hf : IsThetaFun ψ V W f) (γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E) :
    ∃ N : ℕ, 0 < N ∧ ∀ w, ‖f (w + iotaW σ V W ((N : ℝ) • piW θ V W (ratW V W γ)))‖ = ‖f w‖ := by
  obtain ⟨U, hUo, hUf⟩ := hf.level
  obtain ⟨N, hN, hmem⟩ := hU (U.comap (mulRat V W γ)) (hUo.preimage (continuous_mulRat V W γ))
  refine ⟨N, hN, fun w => ?_⟩
  set u : WA V W := mulRat V W γ (pairA D.host.F 0 (N : Af D.host.F)) with hu
  set r : WA V W := mulRat V W γ (pairA D.host.F (N : Ainf D.host.F) 0) with hr
  have hu0 : u.map (infPart D) = 0 := by
    ext i j
    exact TensorProduct.zero_tmul _ (γ i j)
  have hr0 : IsRealW V W r := by
    ext i j
    exact TensorProduct.zero_tmul _ (γ i j)
  have hsum : r + u = N • ratW V W γ := by
    rw [hr, hu, ← AddMonoidHom.map_add, ← mulRat_one, ← AddMonoidHom.map_nsmul]
    congr 1
    refine Prod.ext ?_ ?_
    · show (N : Ainf D.host.F) + 0 = N • (1 : Ainf D.host.F)
      rw [add_zero, nsmul_one]
    · show 0 + (N : Af D.host.F) = N • (1 : Af D.host.F)
      rw [zero_add, nsmul_one]
  have hpu : piW θ V W u = 0 := by
    funext τ i j
    have : infPart D (u i j) = 0 := congrFun (congrFun hu0 i) j
    show θ τ (infPart D (u i j)) = 0
    rw [this, RingHom.map_zero]
  have hi : iotaW σ V W ((N : ℝ) • piW θ V W (ratW V W γ)) = r := by
    rw [Nat.cast_smul_eq_nsmul, ← AddMonoidHom.map_nsmul, ← hsum, AddMonoidHom.map_add, hpu, add_zero,
      h.iota_pi hr0]
  have h1 : ∀ x, ‖f (x + u)‖ = ‖f x‖ := fun x => by
    have := congrFun (hUf u hmem hu0) x
    rw [← this, Heisenberg₂, norm_mul, hψ, one_mul]
  have h2 := congrArg norm (hf.quasi (N • γ) w)
  rw [norm_mul, hψ, one_mul, ratW_nsmul, ← hsum] at h2
  rw [hi, ← h1, ← h2, add_assoc, add_comm]

end GlobalTheory.FockCompare.ThetaPeriod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.RealAdeleExtAndStandardCharacterFormula
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem pair_fst_of_snd {F : Type} [Field F] [NumberField F] (a : AF F) (h : sndA F a = 0) :
    pairA F (fstA F a) 0 = a := Prod.ext rfl h.symm

theorem half_tmul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (θ : Ainf F ⊗[F] E →+* ℂ)
    (a : AF F) :
    θ (fstA F (algebraMap F (AF F) (1 / 2) * a) ⊗ₜ[F] (1 : E)) = θ (fstA F a ⊗ₜ[F] (1 : E)) / 2 := by
  have h2 : algebraMap F (AF F) (1 / 2) * a + algebraMap F (AF F) (1 / 2) * a = a := by
    rw [← add_mul, ← RingHom.map_add, add_halves, RingHom.map_one, one_mul]
  conv_rhs => rw [← h2, map_add, TensorProduct.add_tmul, RingHom.map_add]
  ring

theorem valTau_coe {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (a : AF D.host.F) :
    ((valTau θ τ a : ℝ) : ℂ) = θ τ (fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E)) := by
  have h := conj_tmul_one hθ τ (fstA D.host.F a)
  exact Complex.conj_eq_iff_re.1 h

theorem real_adele_ext_and_char : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ a : AF D.host.F, sndA D.host.F a = 0 → ((∀ τ, valTau θ τ a = 0) → a = 0) ∧ ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) * a) = Complex.exp (-(Real.pi * Complex.I) * ((∑ τ, valTau θ τ a : ℝ) : ℂ)) := by
  intro D θ σ h a ha
  refine ⟨fun h0 => ?_, fun ψ hψ => ?_⟩
  · have h1 : (a ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) = 0 := by
      refine h.ext _ ?_ fun τ => ?_
      · have e : finPart D (a ⊗ₜ[D.host.F] (1 : D.host.E)) = sndA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
        rw [e, ha, TensorProduct.zero_tmul]
      · have e : infPart D (a ⊗ₜ[D.host.F] (1 : D.host.E)) = fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
        rw [e, ← valTau_coe h.inf, h0, Complex.ofReal_zero]
    have hinj := Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F) (A := AF D.host.F)
      (B := D.host.E) (algebraMap D.host.F D.host.E).injective
    apply hinj
    rw [map_zero]
    exact h1
  · have hc := hψ.2.2 θ h.inf (fstA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2) * a))
    rw [psiInf, pair_fst_of_snd _ (by rw [map_mul, ha, mul_zero])] at hc
    rw [hc]
    congr 1
    have e : ∀ ρ, θ ρ (fstA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2) * a) ⊗ₜ[D.host.F] (1 : D.host.E))
        = ((valTau θ ρ a : ℝ) : ℂ) / 2 := fun ρ => by
      rw [valTau_coe h.inf]
      exact half_tmul (θ ρ) a
    rw [Finset.sum_congr rfl fun ρ _ => e ρ, ← Finset.sum_div, Complex.ofReal_sum]
    push_cast
    ring

end GlobalTheory.FockCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.SignInvolutionDiagonalIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SignBasis

section General

variable {E M ι : Type} [Field E] [StarRing E] [AddCommGroup M] [Module E M] [Fintype ι] [DecidableEq ι]

theorem form_eq_sum (h : M →ₗ⋆[E] M →ₗ[E] E) (b : Module.Basis ι E M) (hb : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (x y : M) : h x y = ∑ i, star (b.repr x i) * b.repr y i * h (b i) (b i) := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  rw [map_sum h, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Finset.sum_eq_single i]
  · rw [LinearMap.map_smulₛₗ h, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, starRingEnd_apply]; ring
  · intro j _ hj
    rw [LinearMap.map_smulₛₗ h, LinearMap.smul_apply, map_smul, hb i j hj.symm]; simp
  · simp

theorem re_form_eq_sum (h : M →ₗ⋆[E] M →ₗ[E] E) (b : Module.Basis ι E M) (hb : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (t : E →+* ℂ) (ht : ∀ a, t (star a) = starRingEnd ℂ (t a)) (x : M) :
    (t (h x x)).re = ∑ i, Complex.normSq (t (b.repr x i)) * (t (h (b i) (b i))).re := by
  rw [form_eq_sum h b hb, map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, ht, ← Complex.normSq_eq_conj_mul_self, Complex.re_ofReal_mul]

theorem re_ne_zero (h : M →ₗ⋆[E] M →ₗ[E] E) (hs : h.IsSymm) (hn : h.Nondegenerate) (b : Module.Basis ι E M)
    (hb : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (t : E →+* ℂ) (ht : ∀ a, t (star a) = starRingEnd ℂ (t a)) (i : ι) : (t (h (b i) (b i))).re ≠ 0 := by
  intro h0
  have h1 : starRingEnd ℂ (t (h (b i) (b i))) = t (h (b i) (b i)) := by
    rw [← ht]; exact congrArg t (hs.eq _ _)
  have h2 := Complex.conj_eq_iff_im.1 h1
  have h3 : h (b i) (b i) = 0 := t.injective (by rw [map_zero]; exact Complex.ext h0 h2)
  refine b.ne_zero i (hn.1 _ fun y => ?_)
  rw [form_eq_sum h b hb]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : i = j
  · rw [← hj, h3, mul_zero]
  · simp [Finsupp.single_apply, hj]

def coordSub (b : Module.Basis ι E M) (p : ι → Prop) : Submodule E M where
  carrier := {x | ∀ i, ¬ p i → b.repr x i = 0}
  zero_mem' := fun i _ => by simp
  add_mem' := fun {x y} hx hy i hi => by simp [hx i hi, hy i hi]
  smul_mem' := fun c x hx i hi => by simp [hx i hi]

theorem isCompl_coordSub (b : Module.Basis ι E M) (p : ι → Prop) :
    IsCompl (coordSub b p) (coordSub b fun i => ¬ p i) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    refine b.ext_elem fun i => ?_
    rw [map_zero, Finsupp.zero_apply]
    by_cases hi : p i
    · exact hx' i (not_not.2 hi)
    · exact hx i hi
  · rw [codisjoint_iff, eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hi : p i
    · refine Submodule.mem_sup_left (S := coordSub b p) fun j hj => ?_
      have : i ≠ j := fun e => hj (e ▸ hi)
      simp [Finsupp.single_apply, this]
    · refine Submodule.mem_sup_right (T := coordSub b fun i => ¬ p i) fun j hj => ?_
      have : i ≠ j := fun e => hj (e ▸ hi)
      simp [Finsupp.single_apply, this]

theorem sum_pos_of_coord (b : Module.Basis ι E M) (t : E →+* ℂ) (p : ι → Prop) (d : ι → ℝ) (hd : ∀ i, p i → 0 < d i)
    (x : M) (hx : x ∈ coordSub b p) (h0 : x ≠ 0) : 0 < ∑ i, Complex.normSq (t (b.repr x i)) * d i := by
  obtain ⟨j, hj⟩ : ∃ j, b.repr x j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (b.ext_elem fun i => by simp [hc i])
  refine Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
  · by_cases hi : p i
    · exact mul_nonneg (Complex.normSq_nonneg _) (hd i hi).le
    · rw [hx i hi]; simp
  · refine mul_pos (Complex.normSq_pos.2 ((map_ne_zero t).2 hj)) (hd j ?_)
    by_contra hc
    exact hj (hx j hc)

theorem apply_eq_smul (b : Module.Basis ι E M) (p : ι → Prop) (s : Module.End E M) (c : E)
    (hs : ∀ i, p i → s (b i) = c • b i) (x : M) (hx : x ∈ coordSub b p) : s x = c • x := by
  conv_lhs => rw [← b.sum_repr x]
  conv_rhs => rw [← b.sum_repr x]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : p i
  · rw [map_smul, hs i hi, smul_comm]
  · rw [hx i hi]; simp

omit [StarRing E] in
theorem mem_of_fixed [CharZero E] {P N : Submodule E M} (hc : IsCompl P N) (s : Module.End E M)
    (hP : ∀ x ∈ P, s x = x) (hN : ∀ x ∈ N, s x = -x) (x : M) (hx : s x = x) : x ∈ P := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top : x ∈ P ⊔ N)
  rw [map_add, hP y hy, hN z hz, add_right_inj] at hx
  have : (2 : E) • z = 0 := by rw [two_smul]; nth_rewrite 1 [← hx]; exact neg_add_cancel z
  rw [(smul_eq_zero.1 this).resolve_left two_ne_zero, add_zero]
  exact hy

end General

theorem signInv_diag_iff : ∀ (D : D7) (V : HSp D) (b : Module.Basis (Fin V.rank) D.host.E V.V), (∀ i j, i ≠ j → V.hT (b i) (b j) = 0) → ∀ (τ : D.what₂.Tau) (s : Module.End D.host.E V.V), (IsSignInv V τ s ∧ ∀ i, s (b i) = b i ∨ s (b i) = -b i) ↔ ∀ i, s (b i) = if 0 < (tauE D τ (V.hT (b i) (b i))).re then b i else -b i := by
  intro D V b hb τ s
  have ht := tauE_star (D := D) τ
  have hne := re_ne_zero V.hT V.herm V.nondeg b hb (tauE D τ) ht
  constructor
  · rintro ⟨⟨P, N, hd, hP, hN⟩, hs⟩ i
    rcases hs i with h | h
    · rw [if_pos (hd.pos _ (mem_of_fixed hd.compl s hP hN _ h) (b.ne_zero i)), h]
    · have : b i ∈ N := mem_of_fixed hd.compl.symm (-s) (fun x hx => by rw [LinearMap.neg_apply, hN x hx, neg_neg])
        (fun x hx => by rw [LinearMap.neg_apply, hP x hx]) _ (by rw [LinearMap.neg_apply, h, neg_neg])
      rw [if_neg (hd.neg _ this (b.ne_zero i)).not_gt, h]
  · intro hs
    refine ⟨⟨coordSub b fun i => 0 < (tauE D τ (V.hT (b i) (b i))).re,
      coordSub b fun i => ¬ 0 < (tauE D τ (V.hT (b i) (b i))).re,
      ⟨isCompl_coordSub b _, fun x hx y hy => ?_, fun x hx h0 => ?_, fun x hx h0 => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩,
      fun i => ?_⟩
    · rw [form_eq_sum V.hT b hb]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : 0 < (tauE D τ (V.hT (b i) (b i))).re
      · rw [hy i (not_not.2 hi), mul_zero, zero_mul]
      · rw [hx i hi, star_zero, zero_mul, zero_mul]
    · rw [re_form_eq_sum V.hT b hb _ ht]
      exact sum_pos_of_coord b _ _ _ (fun i hi => hi) x hx h0
    · rw [re_form_eq_sum V.hT b hb _ ht]
      have := sum_pos_of_coord b (tauE D τ) _ (fun i => -(tauE D τ (V.hT (b i) (b i))).re)
        (fun i hi => neg_pos.2 (lt_of_le_of_ne (not_lt.1 hi) (hne i))) x hx h0
      simp only [mul_neg, Finset.sum_neg_distrib] at this
      exact neg_pos.1 this
    · have := apply_eq_smul b _ s 1 (fun i hi => by rw [hs i, if_pos hi, one_smul]) x hx
      rwa [one_smul] at this
    · have := apply_eq_smul b _ s (-1) (fun i hi => by rw [hs i, if_neg hi, neg_one_smul]) x hx
      rwa [neg_one_smul] at this
    · rw [hs i]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl

end GlobalTheory.SignBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.SpanRealProjectionRationalPointsEqTop
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockCompare

variable {D : D7}

theorem span_tauE_eq_top {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ) :
    Submodule.span ℝ (Set.range fun e : D.host.E => fun τ : D.what₂.Tau => tauE D τ e) = ⊤ := by
  set S := Submodule.span ℝ (Set.range fun e : D.host.E => fun τ : D.what₂.Tau => tauE D τ e) with hS
  have hθ := h.inf
  have hcl : IsClosed (S : Set (D.what₂.Tau → ℂ)) := S.closed_of_finiteDimensional
  have key : ∀ y : Ainf D.host.F ⊗[D.host.F] D.host.E, (fun τ => θ τ y) ∈ S := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero =>
      have : (fun τ => θ τ 0) = 0 := by funext τ; exact RingHom.map_zero _
      rw [this]; exact S.zero_mem
    | add a b ha hb =>
      have : (fun τ => θ τ (a + b)) = (fun τ => θ τ a) + fun τ => θ τ b := by
        funext τ; exact RingHom.map_add _ _ _
      rw [this]; exact S.add_mem ha hb
    | tmul a x =>
      have e : ∀ (a : Ainf D.host.F) τ, θ τ (a ⊗ₜ[D.host.F] x) =
          θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D τ x := by
        intro a τ
        rw [← (hθ τ).1, ← RingHom.map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      have hc : Continuous fun a : Ainf D.host.F => fun τ => θ τ (a ⊗ₜ[D.host.F] x) := by
        refine continuous_pi fun τ => ?_
        simp only [e]
        exact (hθ τ).2.mul continuous_const
      refine DenseRange.induction_on (NumberField.InfiniteAdeleRing.denseRange_algebraMap D.host.F) a
        (hcl.preimage hc) fun f => ?_
      have e1 : (algebraMap D.host.F (Ainf D.host.F) f) ⊗ₜ[D.host.F] (1 : D.host.E) =
          (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E f) := by
        exact (Algebra.TensorProduct.includeLeft (R := D.host.F) (S := D.host.F) (A := Ainf D.host.F)
          (B := D.host.E)).commutes f |>.trans
          ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Ainf D.host.F) (B := D.host.E)).commutes f).symm
      refine Submodule.subset_span ⟨algebraMap D.host.F D.host.E f * x, ?_⟩
      funext τ
      show tauE D τ _ = θ τ ((algebraMap D.host.F (Ainf D.host.F) f) ⊗ₜ[D.host.F] x)
      rw [e, e1, (hθ τ).1, RingHom.map_mul]
  rw [eq_top_iff]
  intro z _
  have := key (infPart D (σ z))
  rwa [show (fun τ => θ τ (infPart D (σ z))) = z from funext fun τ => h.comp z τ] at this

theorem span_piW_ratW_eq_top (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (h : Chart θ σ) (V W : HSp D) :
    Submodule.span ℝ (Set.range fun γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E =>
      piW θ V W (ratW V W γ)) = ⊤ := by
  classical
  set T := Submodule.span ℝ (Set.range fun γ : Matrix (Fin V.rank) (Fin W.rank) D.host.E =>
      piW θ V W (ratW V W γ)) with hT
  let L : Fin V.rank → Fin W.rank → (D.what₂.Tau → ℂ) →ₗ[ℝ] RW V W := fun i j =>
    { toFun := fun z τ k l => if i = k ∧ j = l then z τ else 0
      map_add' := fun x y => by funext τ k l; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c x => by funext τ k l; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
  have hL : ∀ i j z, L i j z ∈ T := by
    intro i j z
    have hz : z ∈ Submodule.comap (L i j) T := by
      refine (Submodule.span_le.2 ?_ : _ ≤ Submodule.comap (L i j) T) ((span_tauE_eq_top h).ge Submodule.mem_top)
      rintro _ ⟨e, rfl⟩
      refine Submodule.subset_span ⟨Matrix.single i j e, ?_⟩
      funext τ k l
      show θ τ (infPart D (incA D (Matrix.single i j e k l))) = if i = k ∧ j = l then tauE D τ e else 0
      rw [comp_incA h.inf, Matrix.single_apply]
      split_ifs
      · rfl
      · exact RingHom.map_zero _
    exact hz
  rw [eq_top_iff]
  intro z _
  have : z = ∑ i, ∑ j, L i j fun τ => z τ i j := by
    funext τ k l
    simp only [Finset.sum_apply]
    show z τ k l = ∑ i, ∑ j, if i = k ∧ j = l then z τ i j else 0
    simp [ite_and]
  rw [this]
  exact T.sum_mem fun i _ => T.sum_mem fun j _ => hL i j _

end GlobalTheory.FockCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.StdCharIffInt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.DualPairCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Gen
variable {R : Type} [CommRing R] {a b : ℕ}

def leftMul (J Ji : Matrix (Fin a) (Fin a) R) (h1 : Ji * J = 1) :
    Matrix (Fin a) (Fin b) R ≃ₗ[R] Matrix (Fin a) (Fin b) R where
  toFun x := Jiᵀ * x
  invFun y := Jᵀ * y
  map_add' := Matrix.mul_add _
  map_smul' c x := Matrix.mul_smul _ c x
  left_inv x := by
    change Jᵀ * (Jiᵀ * x) = x
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, h1, Matrix.transpose_one, Matrix.one_mul]
  right_inv x := by
    change Jiᵀ * (Jᵀ * x) = x
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, mul_eq_one_comm.1 h1, Matrix.transpose_one, Matrix.one_mul]

theorem gen_supp (f : R) (g : Matrix (Fin a) (Fin a) R) :
    (∀ i j, f * (g - 1) i j = (g - 1) i j) ↔ (1 - f) • g = (1 - f) • (1 : Matrix (Fin a) (Fin a) R) := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  constructor <;> intro h <;> linear_combination -h

theorem gen_cont [TopologicalSpace R] [IsTopologicalRing R] (J Ji : Matrix (Fin a) (Fin a) R) (h1 : Ji * J = 1) :
    Continuous (leftMul (b := b) J Ji h1) ∧ Continuous (leftMul (b := b) J Ji h1).symm :=
  ⟨continuous_const.matrix_mul continuous_id, continuous_const.matrix_mul continuous_id⟩

end Gen

open GlobalTheory.IndefiniteRowSideFullHecke

theorem suppAt_iff' (e : AE D) (V : HSp D) (g : GA D V) : SuppAt e V g ↔ HeisenbergWeilMatrices.IsAt (e + HeisenbergWeilMatrices.cj D e) g :=
  gen_supp _ _

theorem suppAt_iff {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} (he : HeisenbergWeilMatrices.IsSplitIdem D v e) (V : HSp D)
    (g : GA D V) : SuppAt e V g ↔ HeisenbergWeilMatrices.IsAt (HeisenbergWeilMatrices.idemFin D v) g := by
  rw [suppAt_iff', he.sum]

end GlobalTheory.DualPairCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.TorusWeightVectorIffCartanWeightVectorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusWeightVector_iff_cartanWeightVector : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ (μ : Fin n → ℝ) (v : R.HK.V), IsWtOn (Formalism.REAL.Kset ε) σ μ (R.ι v) ↔ ∀ a, R.HK.act (Eab a a) v = ((μ (e a) : ℝ) : ℂ) • v := by
  first | exact @GlobalTheory.RealPar.TorusWt.isWtOn_iff | exact GlobalTheory.RealPar.TorusWt.isWtOn_iff | (intros; apply GlobalTheory.RealPar.TorusWt.isWtOn_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPComplexMultiplicationCongruenceModPrStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_complexMultiplication_congruence_mod_prime : ∀ (L : PeriodPair) (W : ValuationSubring ℂ) (α : ℂ) (p : ℕ), (2 : ℂ)⁻¹ ∈ W → (3 : ℂ)⁻¹ ∈ W → L.g₂ ∈ W → L.g₃ ∈ W → (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)⁻¹ ∈ W → p.Prime → (p : ℂ) ∈ W.nonunits → α ∈ W.nonunits → (∀ l ∈ L.lattice, α * l ∈ L.lattice) → ‖α‖ ^ 2 = p → ∃ a : ℂ, a ∈ W ∧ a⁻¹ ∈ W ∧ a ≠ 0 ∧ L.g₂ - a ^ 2 * L.g₂ ^ p ∈ W.nonunits ∧ L.g₃ - a ^ 3 * L.g₃ ^ p ∈ W.nonunits ∧ ∀ (m : ℕ) (t : ℂ), Odd m → (m : ℂ)⁻¹ ∈ W → (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP (α * t) - a * L.weierstrassP t ^ p ∈ W.nonunits := by
  first | exact @GlobalTheory.EisensteinCongruence.weierstrassP_mul_congr_pow | exact GlobalTheory.EisensteinCongruence.weierstrassP_mul_congr_pow | (intros; apply GlobalTheory.EisensteinCongruence.weierstrassP_mul_congr_pow <;> assumption)
end

