import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0136
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0084
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0576
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0514
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaUnitaryGroupEveryResidueOfLie
section
noncomputable section

namespace GlobalTheory.UnitLemma.OrbitAll

open GlobalTheory.UnitLemma.Orbit

open GlobalTheory.UnitLemma Polynomial

variable {K : UQ}

theorem isIso_stSum_eq {B C : InvAlg K} {φ : B.A ≃ₐ[K.E] C.A} (h : IsIso φ) : C.stSum = B.stSum := by
  unfold InvAlg.stSum
  rw [h.finsum_eq C.N fun x u => (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K C x u).1]
  exact finsum_congr fun k => h.N_eq _

theorem isIso_kapSum_eq {B₁ B₂ C₁ C₂ : InvAlg K} {φ₁ : B₁.A ≃ₐ[K.E] C₁.A} {φ₂ : B₂.A ≃ₐ[K.E] C₂.A}
    (h₁ : IsIso φ₁) (h₂ : IsIso φ₂) : InvAlg.kapSum C₁ C₂ = InvAlg.kapSum B₁ B₂ := by
  unfold InvAlg.kapSum
  refine ((h₁.prod h₂).finsum_eq (fun x => K.eta (C₁.gramDet x.1) * (C₁.prod C₂).N x) fun x u => ?_).trans ?_
  · have e1 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K (C₁.prod C₂) x u).1
    have e2 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K C₁ x.1 (Units.map (MonoidHom.fst C₁.A C₂.A) u)).2
    exact congrArg₂ (· * ·) e2 e1
  · exact finsum_congr fun k => congrArg₂ (· * ·) (h₁.eta_eq _) ((h₁.prod h₂).N_eq _)

theorem isIso_identity {B₁ B₂ C₁ C₂ : InvAlg K} {φ₁ : B₁.A ≃ₐ[K.E] C₁.A} {φ₂ : B₂.A ≃ₐ[K.E] C₂.A}
    (h₁ : IsIso φ₁) (h₂ : IsIso φ₂) (h : InvAlg.Identity C₁ C₂) : InvAlg.Identity B₁ B₂ := by
  unfold InvAlg.Identity at h ⊢
  rwa [isIso_kapSum_eq h₁ h₂, isIso_stSum_eq h₁, isIso_stSum_eq h₂, h₁.charpoly_eq_of_isIso, h₂.charpoly_eq_of_isIso] at h

theorem prod_aeval (B₁ B₂ : InvAlg K) (f : K.O[X]) :
    aeval (B₁.prod B₂).g f = ((aeval B₁.g f, aeval B₂.g f) : B₁.A × B₂.A) :=
  Prod.ext (aeval_algHom_apply (AlgHom.fst K.O B₁.A B₂.A) (B₁.g, B₂.g) f).symm
    (aeval_algHom_apply (AlgHom.snd K.O B₁.A B₂.A) (B₁.g, B₂.g) f).symm

theorem prod_integral (B₁ B₂ : InvAlg K) (h₁ : IsIntegral K.O B₁.g) (h₂ : IsIntegral K.O B₂.g) :
    IsIntegral K.O (B₁.prod B₂).g :=
  IsIntegral.pair (x := (B₁.g, B₂.g)) h₁ h₂

theorem eq_one_of_finrank_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e)
    (h : Module.finrank K.E (cut B e he).A = 0) : e = 1 := by
  have : Subsingleton (B.A ⧸ Ideal.span {e}) := (Module.finrank_zero_iff (R := K.E) (M := (cut B e he).A)).1 h
  have h1 : (1 : B.A) ∈ Ideal.span {e} := Ideal.Quotient.eq_zero_iff_mem.1 (Subsingleton.elim _ _)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
  linear_combination (e - 1) * -ha + a * hi.eq

theorem finrank_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e) :
    Module.finrank K.E B.A = Module.finrank K.E (cut B e he).A +
      Module.finrank K.E (cut B (1 - e) (one_sub_fixed B he)).A := by
  rw [(AlgEquiv.prodQuotientOfIsIdempotentElem K.E hi hi.one_sub (by simp)
    (by simp [hi])).toLinearEquiv.finrank_eq, Module.finrank_prod]
  rfl

theorem charpoly_eq_mul_charpoly_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e) :
    B.P = (cut B e he).P * (cut B (1 - e) (one_sub_fixed B he)).P := by
  rw [← prod_P, (isIso_cut B hi he).charpoly_eq_of_isIso]

theorem one_orbit (B : InvAlg K) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g)
    (h : ∀ e ∈ Algebra.adjoin K.O ({B.g} : Set B.A), e * e = e → B.σ e = e → e = 0 ∨ e = 1) :
    (∃ e ∈ Algebra.adjoin K.O ({B.g} : Set B.A), e * e = e ∧ e + B.σ e = 1) ∨
      IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A)) := by
  rcases subsingleton_or_nontrivial B.A with hs | hs
  · exact Or.inl ⟨0, zero_mem _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  by_cases hid : ∀ e : Algebra.adjoin K.O ({B.g} : Set B.A), e * e = e → e = 0 ∨ e = 1
  · have : Module.Finite K.O (Algebra.adjoin K.O ({B.g} : Set B.A)) :=
      Module.Finite.iff_fg.2 hi.fg_adjoin_singleton
    exact Or.inr (isLocalRing_of_idem (R := K.O) _ hid)
  push Not at hid
  obtain ⟨⟨e, he⟩, hee, h0, h1⟩ := hid
  have hee : e * e = e := congrArg Subtype.val hee
  have h0 : e ≠ 0 := fun h => h0 (Subtype.ext h)
  have h1 : e ≠ 1 := fun h => h1 (Subtype.ext h)
  have he' := adjoin_stable B hu hi he
  have hee' : B.σ e * B.σ e = B.σ e := by rw [← map_mul, hee]
  have hm : e * B.σ e = 0 := by
    refine (h _ (mul_mem he he') ?_ ?_).resolve_right fun h2 => h1 ?_
    · linear_combination B.σ e * B.σ e * hee + e * hee'
    · rw [map_mul, B.σ_σ, mul_comm]
    · linear_combination (1 - e) * h2 + B.σ e * hee
  refine Or.inl ⟨e, he, hee, (h _ (add_mem he he') ?_ ?_).resolve_left fun h2 => h0 ?_⟩
  · linear_combination hee + hee' + 2 * hm
  · rw [map_add, B.σ_σ, add_comm]
  · linear_combination e * h2 - hee - hm

theorem identity_integral (hL : UnitLemmaLie) (n : ℕ) : ∀ B₁ B₂ : InvAlg K,
    Module.finrank K.E B₁.A + Module.finrank K.E B₂.A = n → B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 →
    (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → InvAlg.Identity B₁ B₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B₁ B₂ hn u₁ u₂ hs i₁ i₂
  by_cases h : ∀ e ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
      e * e = e → (B₁.prod B₂).σ e = e → e = 0 ∨ e = 1
  · rcases one_orbit (B₁.prod B₂) (Prod.ext u₁ u₂) (prod_integral _ _ i₁ i₂) h with h | h
    · exact GlobalTheory.T.involutive_algebra_product_identity K B₁ B₂ u₁ u₂ hs i₁ i₂ h
    · exact GlobalTheory.T.unitLemma_local_anyResidueChar_of_lieAlgebra hL K B₁ B₂ u₁ u₂ hs i₁ i₂ h
  push Not at h
  obtain ⟨e, he, hee, hσ, h0, h1⟩ := h
  rw [Algebra.adjoin_singleton_eq_range_aeval] at he
  obtain ⟨f, hf⟩ := he
  have hf : ((aeval B₁.g f, aeval B₂.g f) : B₁.A × B₂.A) = e := (prod_aeval B₁ B₂ f).symm.trans hf
  obtain ⟨e₁, e₂⟩ := e
  obtain ⟨f₁, f₂⟩ := Prod.ext_iff.1 hf
  have j₁ : IsIdempotentElem e₁ := congrArg Prod.fst hee
  have j₂ : IsIdempotentElem e₂ := congrArg Prod.snd hee
  have s₁ : B₁.σ e₁ = e₁ := congrArg Prod.fst hσ
  have s₂ : B₂.σ e₂ = e₂ := congrArg Prod.snd hσ
  dsimp only at f₁ f₂
  have r₁ := finrank_cut B₁ j₁ s₁
  have r₂ := finrank_cut B₂ j₂ s₂
  have p₁ : Module.finrank K.E (cut B₁ e₁ s₁).A + Module.finrank K.E (cut B₂ e₂ s₂).A ≠ 0 := fun hz =>
    h1 (Prod.ext (eq_one_of_finrank_cut B₁ j₁ s₁ (Nat.add_eq_zero_iff.1 hz).1)
      (eq_one_of_finrank_cut B₂ j₂ s₂ (Nat.add_eq_zero_iff.1 hz).2))
  have p₂ : Module.finrank K.E (cut B₁ (1 - e₁) (one_sub_fixed B₁ s₁)).A +
      Module.finrank K.E (cut B₂ (1 - e₂) (one_sub_fixed B₂ s₂)).A ≠ 0 := fun hz =>
    h0 (Prod.ext
      (sub_eq_self.1 (eq_one_of_finrank_cut B₁ j₁.one_sub (one_sub_fixed B₁ s₁) (Nat.add_eq_zero_iff.1 hz).1))
      (sub_eq_self.1 (eq_one_of_finrank_cut B₂ j₂.one_sub (one_sub_fixed B₂ s₂) (Nat.add_eq_zero_iff.1 hz).2)))
  rw [charpoly_eq_mul_charpoly_cut B₁ j₁ s₁, charpoly_eq_mul_charpoly_cut B₂ j₂ s₂, mul_mul_mul_comm] at hs
  refine isIso_identity (isIso_cut B₁ j₁ s₁) (isIso_cut B₂ j₂ s₂) ?_
  refine GlobalTheory.T.involutiveAlg_identity_prod_of_unit_resultant K _ _ _ _ hs (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂) (cut_integral _ _ _ i₁)
    (cut_integral _ _ _ i₂) ?_ ?_ ?_
  · rw [← prod_P, ← prod_P] at hs ⊢
    refine val_resultant _ _ hs.of_mul_left hs.of_mul_right
      (prod_integral _ _ (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂))
      (prod_integral _ _ (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂)) f ?_ ?_
    · rw [prod_aeval, cut_aeval, cut_aeval, f₁, f₂]
      exact Prod.ext (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))
        (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))
    · rw [prod_aeval, cut_aeval, cut_aeval, f₁, f₂]
      exact Prod.ext (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self (1 - e₁))).symm
        (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self (1 - e₂))).symm
  · exact ih _ (by omega) _ _ rfl (cut_unitary _ _ _ u₁) (cut_unitary _ _ _ u₂) hs.of_mul_left
      (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂)
  · exact ih _ (by omega) _ _ rfl (cut_unitary _ _ _ u₁) (cut_unitary _ _ _ u₂) hs.of_mul_right
      (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂)

theorem identity_of_lie : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 →
    B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by
  intro hL K B₁ B₂ u₁ u₂ hs
  by_cases hi : IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g
  · exact identity_integral hL _ B₁ B₂ rfl u₁ u₂ hs hi.1 hi.2
  · obtain ⟨h1, h2⟩ := GlobalTheory.T.kappaSum_zero_and_stableSum_mul_zero_of_not_integral K B₁ B₂ hi
    unfold InvAlg.Identity
    rw [h1, h2, mul_zero]

end GlobalTheory.UnitLemma.OrbitAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalGlobalChar

open Filter Topology GlobalTheory.IdemSupport

section Adele

variable {F : Type} [Field F] [NumberField F]

open Classical in

def ind (S : Finset (HeightOneSpectrum (𝓞 F))) : Af F :=
  ⟨fun u => if u ∈ S then 1 else 0, Eventually.of_forall fun u => by
    by_cases h : u ∈ S
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

open Classical in
theorem ev_ind (S : Finset (HeightOneSpectrum (𝓞 F))) (u : HeightOneSpectrum (𝓞 F)) :
    evalV F u (ind S) = if u ∈ S then 1 else 0 := rfl

theorem fin_ext {a b : Af F} (h : ∀ u, evalV F u a = evalV F u b) : a = b := Subtype.ext (funext h)

theorem tendsto_ind_mul (α : Af F) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => ind S * α) atTop (𝓝 α) := by
  classical
  let T : Set (HeightOneSpectrum (𝓞 F)) := {u | α u ∈ (u.adicCompletionIntegers F : Set (u.adicCompletion F))}
  have hT : cofinite ≤ 𝓟 T := le_principal_iff.2 α.2
  let f : Finset (HeightOneSpectrum (𝓞 F)) → RestrictedProduct
      (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (𝓟 T) :=
    fun S => ⟨fun u => if u ∈ S then α u else 0, fun u hu => by
      by_cases h : u ∈ S
      · simp only [Set.mem_setOf_eq, h, if_true]; exact hu
      · simp only [Set.mem_setOf_eq, h, if_false]; exact zero_mem _⟩
  let a : RestrictedProduct
      (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (𝓟 T) := ⟨fun u => α u, fun u hu => hu⟩
  have hf : Tendsto f atTop (𝓝 a) := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro u
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ({u} : Finset _)] with S hS
    exact (if_pos (hS (Finset.mem_singleton_self u))).symm
  have h2 := ((RestrictedProduct.continuous_inclusion hT).tendsto a).comp hf
  refine Tendsto.congr (fun S => fin_ext fun u => ?_) h2
  rw [map_mul, ev_ind]
  change (if u ∈ S then α u else 0) = _
  split_ifs
  · exact (one_mul _).symm
  · exact (zero_mul _).symm

def eps (S : Finset (HeightOneSpectrum (𝓞 F))) : AF F := pairA F 1 (ind S)

theorem tendsto_eps_mul (a : AF F) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => eps S * a) atTop (𝓝 a) := by
  have := (tendsto_const_nhds (x := a.1)).prodMk_nhds (tendsto_ind_mul a.2)
  refine Tendsto.congr (f₁ := fun S => ((a.1, ind S * a.2) : Ainf F × Af F)) (fun S => ?_) this
  exact Prod.ext (one_mul _).symm rfl

theorem ind_mul_self (S : Finset (HeightOneSpectrum (𝓞 F))) : ind S * ind S = ind S :=
  fin_ext fun u => by rw [map_mul, ev_ind]; split_ifs <;> simp

theorem eps_mul_self (S : Finset (HeightOneSpectrum (𝓞 F))) : eps S * eps S = eps S :=
  Prod.ext (one_mul _) (ind_mul_self S)

theorem pl_mul_self (v : HeightOneSpectrum (𝓞 F)) :
    pairA F 0 (ind {v}) * pairA F 0 (ind {v}) = pairA F 0 (ind {v}) :=
  Prod.ext (mul_zero _) (ind_mul_self _)

theorem eps_cons (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    eps (S.cons v hv) * pairA F 0 (ind {v}) = pairA F 0 (ind {v}) ∧
    eps (S.cons v hv) * (1 - pairA F 0 (ind {v})) = eps S := by
  refine ⟨Prod.ext (mul_zero _) (fin_ext fun u => ?_), Prod.ext ?_ (fin_ext fun u => ?_)⟩
  · change evalV F u (ind (S.cons v hv) * ind {v}) = evalV F u (ind {v})
    rw [map_mul, ev_ind, ev_ind]
    by_cases h : u = v <;> simp [h]
  · change (1 : Ainf F) * (1 - 0) = 1
    simp
  · change evalV F u (ind (S.cons v hv) * (1 - ind {v})) = evalV F u (ind S)
    rw [map_mul, map_sub, map_one, ev_ind, ev_ind, ev_ind]
    by_cases h : u = v
    · subst h; simp [hv]
    · have hm : u ∈ S.cons v hv ↔ u ∈ S := by rw [Finset.mem_cons]; exact or_iff_right h
      by_cases h' : u ∈ S
      · rw [if_pos (hm.2 h'), if_pos h', if_neg (by simpa using h)]; simp
      · rw [if_neg (fun x => h' (hm.1 x)), if_neg h', zero_mul]

variable {E : Type} [Field E] [Algebra F E]

theorem tendsto_eps_tens (x : AF F ⊗[F] E) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => algebraMap (AF F) (AF F ⊗[F] E) (eps S) * x)
      atTop (𝓝 x) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := IsModuleTopology.toContinuousSMul (AF F) _
  induction x using TensorProduct.induction_on with
  | zero => simpa only [mul_zero] using tendsto_const_nhds
  | tmul a e =>
    have h := (tendsto_eps_mul a).smul_const ((1 : AF F) ⊗ₜ[F] e)
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at h
    refine h.congr fun S => ?_
    rw [← Algebra.smul_def, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simpa only [mul_add] using hx.add hy

theorem tendsto_mix {n : ℕ} (M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => algebraMap (AF F) (AF F ⊗[F] E) (eps S) • M +
      (1 - algebraMap (AF F) (AF F ⊗[F] E) (eps S)) • (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) atTop (𝓝 M) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h := (tendsto_eps_tens ((M - 1) i j)).add_const ((1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j)
  rw [Matrix.sub_apply, sub_add_cancel] at h
  refine h.congr fun S => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end Adele

theorem tendsto_HA {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {ι : Type} {l : Filter ι}
    {p : ι → HA R σ J} {g : HA R σ J}
    (h1 : Tendsto (fun i => (HA.mat R σ J (p i)).1) l (𝓝 (HA.mat R σ J g).1))
    (h2 : Tendsto (fun i => (HA.mat R σ J (p i)⁻¹).1) l (𝓝 (HA.mat R σ J g⁻¹).1)) : Tendsto p l (𝓝 g) := by
  refine (IsEmbedding.subtypeVal.tendsto_nhds_iff).2 ?_
  refine (Units.isEmbedding_embedProduct.tendsto_nhds_iff).2 ?_
  exact h1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h2)

variable {D : D7}

theorem mem_GinfC (V : HSp D) {g : GA D V} (hg : SuppPl (eps ∅) V g) : g ∈ GinfC V := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hf : finPart D (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (eps ∅)) = 0 := by
    have h0 : ind (∅ : Finset (HeightOneSpectrum (𝓞 D.host.F))) = 0 := fin_ext fun u => by
      rw [ev_ind, map_zero, if_neg (Finset.notMem_empty u)]
    change ind ∅ ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [h0, TensorProduct.zero_tmul]
  have h := congrArg (finPart D) (hg i j)
  rw [map_mul, hf, zero_mul, Matrix.sub_apply, map_sub, eq_comm, sub_eq_zero] at h
  change finPart D (Formalism.L2.Theta.mt V g i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem isPlaceIdem (v : HeightOneSpectrum (𝓞 D.host.F)) : IsPlaceIdem D v (pairA D.host.F 0 (ind {v})) :=
  ⟨ind {v}, rfl, by rw [ev_ind, if_pos (Finset.mem_singleton_self v)],
    fun w hw => by rw [ev_ind, if_neg (by simpa using hw)]⟩

theorem alg_idem {a : AF D.host.F} (h : a * a = a) :
    algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) a * algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) a =
      algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) a := by rw [← map_mul, h]

theorem triv_eps (V : HSp D) (ν : GA D V →* Circle) (hinf : ∀ g ∈ GinfC V, ν g = 1)
    (hpl : ∀ v g, SuppPl (pairA D.host.F 0 (ind {v})) V g → ν g = 1) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∀ g, SuppPl (eps S) V g → ν g = 1 := by
  induction S using Finset.cons_induction with
  | empty => exact fun g hg => hinf g (mem_GinfC V hg)
  | cons v S hv ih =>
    intro g hg
    obtain ⟨h1, h2⟩ := eps_cons S v hv
    have h1' := congrArg (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)) h1
    have h2' := congrArg (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)) h2
    rw [map_mul] at h1' h2'
    rw [map_sub, map_one] at h2'
    obtain ⟨g₁, g₂, s₁, s₂, e⟩ := exists_split V (alg_idem (pl_mul_self v)) (cA_algebraMap _) g
    have t₁ : g₁ ∈ suppGroup V (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (eps (S.cons v hv))) := fun i j => by
      rw [← s₁ i j, ← mul_assoc, h1']
    have t : g ∈ suppGroup V (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (eps (S.cons v hv))) := hg
    have t₂ : g₂ ∈ suppGroup V (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (eps (S.cons v hv))) := by
      have := mul_mem (inv_mem t₁) t
      rwa [e, inv_mul_cancel_left] at this
    have u₂ : SuppPl (eps S) V g₂ := fun i j => by
      rw [← h2', mul_assoc, s₂ i j, t₂ i j]
    rw [e, map_mul, hpl v g₁ s₁, ih g₂ u₂, mul_one]

theorem exists_approx (V : HSp D) (g : GA D V) :
    ∃ p : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V, (∀ S, SuppPl (eps S) V (p S)) ∧ Tendsto p atTop (𝓝 g) := by
  choose p hp using fun S : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
    exists_piece V (alg_idem (eps_mul_self S)) (cA_algebraMap _) g
  choose q hq using fun S : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
    exists_piece V (alg_idem (eps_mul_self S)) (cA_algebraMap _) g⁻¹
  have hpq : ∀ S, (p S)⁻¹ = q S := fun S => by
    refine inv_eq_of_mul_eq_one_right (mt_inj V ?_)
    rw [mt_mul, hp, hq, mix_mul (alg_idem (eps_mul_self S)), ← mt_mul, mul_inv_cancel, mt_one, one_mul, mix_self]
  refine ⟨p, fun S => (suppF_iff V _ (p S)).2 (smul_mix (alg_idem (eps_mul_self S)) (hp S)), ?_⟩
  have a1 : Tendsto (fun S => Formalism.L2.Theta.mt V (p S)) atTop (𝓝 (Formalism.L2.Theta.mt V g)) :=
    (tendsto_mix _).congr fun S => (hp S).symm
  have a2 : Tendsto (fun S => Formalism.L2.Theta.mt V (p S)⁻¹) atTop (𝓝 (Formalism.L2.Theta.mt V g⁻¹)) :=
    (tendsto_mix _).congr fun S => by rw [hpq, hq]
  exact tendsto_HA _ _ _ a1 a2

theorem eq_one_of_local : ∀ (D : D7) (V : HSp D) (ν : GA D V →* Circle), Continuous ν → (∀ g ∈ GinfC V, ν g = 1) → (∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ν g = 1) → (∀ v ε, NonSplitAt D v ε → ∀ g, SuppPl ε V g → ν g = 1) → ∀ g, ν g = 1 := by
  intro D V ν hν hinf hs hn g
  have hpl : ∀ v g, SuppPl (pairA D.host.F 0 (ind {v})) V g → ν g = 1 := fun v g hg => by
    by_cases h : ∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)
        (pairA D.host.F 0 (ind {v}))
    · obtain ⟨e, he, h⟩ := h
      exact hs e he g fun i j => by rw [h]; exact hg i j
    · exact hn v _ ⟨isPlaceIdem v, h⟩ g hg
  obtain ⟨p, hp', hlim⟩ := exists_approx V g
  have hp : ∀ S, ν (p S) = 1 := fun S => triv_eps V ν hinf hpl S _ (hp' S)
  have h1 := (hν.tendsto g).comp hlim
  exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr fun S => (hp S).symm)

end GlobalTheory.LocalGlobalChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationStrictHenselianEqConstMulUnit
section
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

theorem units_of_divConst (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [Algebra T O]
    (h : DivConst T O)
    (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ) :
    ∃ (c d : T) (w : Oˣ), c ≠ 0 ∧ d ≠ 0 ∧
      (u : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) *
          algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))
            (algebraMap T O d) =
        algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))
            (algebraMap T O c) *
          algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (w : O) := by
  by_cases hL : Subsingleton (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))
  · exact ⟨1, 1, 1, one_ne_zero, one_ne_zero, Subsingleton.elim _ _⟩
  rw [not_subsingleton_iff_nontrivial] at hL
  obtain ⟨⟨b, s₁⟩, hb⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  obtain ⟨⟨c, s₂⟩, hc⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) ((u⁻¹ : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ) : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))))
  obtain ⟨t₁, ht₁, hs₁⟩ := s₁.2
  obtain ⟨t₂, ht₂, hs₂⟩ := s₂.2
  have h1 : algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (b * c) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) ((s₁ : O) * (s₂ : O)) := by
    have hu : (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) * ((u⁻¹ : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ) : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) = 1 := u.mul_inv
    rw [← hb, ← hc, ← IsLocalization.mk'_mul] at hu
    have := IsLocalization.mk'_spec (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (b * c) (s₁ * s₂)
    rw [hu, one_mul] at this
    rw [← this]; rfl
  obtain ⟨m, hm⟩ := (IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))).1 h1
  obtain ⟨t₀, ht₀, hm₀⟩ := m.2
  have hmem : t₀ * t₁ * t₂ ∈ nonZeroDivisors T :=
    mul_mem (mul_mem ht₀ ht₁) ht₂
  have hne : t₀ * t₁ * t₂ ≠ 0 := nonZeroDivisors.ne_zero hmem
  obtain ⟨a, w, hbw⟩ := h b ((m : O) * c) (t₀ * t₁ * t₂) hne (by
    rw [map_mul, map_mul, hm₀, hs₁, hs₂]
    calc b * ((m : O) * c) = (m : O) * (b * c) := by ring
      _ = (m : O) * ((s₁ : O) * (s₂ : O)) := hm
      _ = (m : O) * (s₁ : O) * (s₂ : O) := by ring)
  have key : (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (s₁ : O) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) b := by
    rw [← hb]; exact IsLocalization.mk'_spec (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) b s₁
  refine ⟨a, t₁, w, ?_, nonZeroDivisors.ne_zero ht₁, ?_⟩
  · intro ha
    have h0 : (u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (s₁ : O) = 0 := by
      rw [key, hbw, ha]; simp
    exact (u.isUnit.mul (IsLocalization.map_units (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) s₁)).ne_zero h0
  · rw [hs₁, key, hbw, map_mul]

theorem main_of_divConstAll (hAll : DivConstAll) : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)], (∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, ∃ (c d : T) (w : Oˣ), c ≠ 0 ∧ d ≠ 0 ∧ (u : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O d) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O c) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (w : O) := by
  intro T O _ _ _ _ _ _ _ _ _ hroot hO u
  obtain ⟨P, hP, φ, hφ, hsh⟩ :=
    GlobalTheory.StrictHensUnion.isStrictHenselisation_of_directed_union T O hO
  exact units_of_divConst T O (hAll T O hroot P φ hφ hsh) u

end GlobalTheory.VertUnits

namespace GlobalTheory.VertUnits

theorem units_eq_const_mul_unit : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)], (∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, ∃ (c d : T) (w : Oˣ), c ≠ 0 ∧ d ≠ 0 ∧ (u : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O d) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O c) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (w : O) :=
  main_of_divConstAll (GlobalTheory.T.divisorsOfConstantsAllPrimes_of_closedFibre (divConstLocal_of
    (GlobalTheory.T.divisorsOfConstantsClosedPoints_of_origin GlobalTheory.T.div_const_origin) (GlobalTheory.T.divisorsOfConstants_genericFibre_of_closedPoints (GlobalTheory.T.divisorsOfConstantsClosedPoints_of_origin GlobalTheory.T.div_const_origin))))

end GlobalTheory.VertUnits
end

