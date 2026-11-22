import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0576
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0373
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0399
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0136
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0084
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0206
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0208
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0574
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0575
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0088
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0585
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0586
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0569

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopBasisDiscRegular
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem topBasis_disc_regular : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → Function.Injective (toDisc l (s X) bk.ρ₀) ∧ toDisc l (s X) bk.ρ₀ (s bk.E) ∈ nonZeroDivisors (Disc l (s X) bk.ρ₀) ∧ (l : A) ∈ nonZeroDivisors A ∧ ∀ F : bk.DS bk.ρ₀ →+* Disc l (s X) bk.ρ₀, IsDiscMap s F → Function.Injective F := by
  intro l _ K bk A _ s ι TB
  obtain ⟨h0, h1, -, -⟩ := GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius l K bk A s
  refine ⟨(GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk A s ι TB bk.ρ₀ h0 h1).1, ?_, ?_, ?_⟩
  · rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    have hn := (GlobalTheory.T.eisenstein_div_closedDisc_of_topBasis l K bk A s ι TB bk.ρ₀ le_rfl h1).1 y
    rw [mul_comm, hy, norm_zero] at hn
    have hp : (0 : ℝ) < (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree := pow_pos (by exact_mod_cast h0) _
    exact norm_eq_zero.1 ((mul_eq_zero.1 hn.symm).resolve_left hp.ne')
  · have hH : IsHausdorff bk.J bk.S := bk.complete.toIsHausdorff
    have hF := GlobalTheory.T.topologicalBasis_basic_facts bk.S A s bk.J ι TB hH
    have hW : ((l : ℕ) : Wq l bk.a) ≠ 0 := by
      intro h
      have h2 := congrArg (fun w : Wq l bk.a => w.coeff 1) h
      simp only [WittVector.coeff_p_one, WittVector.zero_coeff] at h2
      exact one_ne_zero h2
    have hS : ((l : ℕ) : bk.S) ≠ 0 := by
      intro h
      have h2 := congrArg (PowerSeries.constantCoeff) h
      rw [map_natCast, map_zero] at h2
      exact hW h2
    have := hF.2.2.2.2 _ (mem_nonZeroDivisors_of_ne_zero hS)
    rwa [map_natCast] at this
  · intro F hF
    obtain ⟨_, -, -, -, -, -, -, -, hnorm⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB bk.ρ₀ h0 h1 F hF
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h := hnorm x
    rw [hx, norm_zero] at h
    exact norm_eq_zero.1 h.symm

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaUnitaryGroupOddResidueOfLie
section
noncomputable section

namespace GlobalTheory.UnitLemma.Orbit

open GlobalTheory.UnitLemma Polynomial

variable {K : UQ}

theorem IsIso.stSum_eq {B C : InvAlg K} {φ : B.A ≃ₐ[K.E] C.A} (h : IsIso φ) : C.stSum = B.stSum := by
  unfold InvAlg.stSum
  rw [h.finsum_eq C.N fun x u => (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K C x u).1]
  exact finsum_congr fun k => h.N_eq _

theorem IsIso.kapSum_eq {B₁ B₂ C₁ C₂ : InvAlg K} {φ₁ : B₁.A ≃ₐ[K.E] C₁.A} {φ₂ : B₂.A ≃ₐ[K.E] C₂.A}
    (h₁ : IsIso φ₁) (h₂ : IsIso φ₂) : InvAlg.kapSum C₁ C₂ = InvAlg.kapSum B₁ B₂ := by
  unfold InvAlg.kapSum
  refine ((h₁.prod h₂).finsum_eq (fun x => K.eta (C₁.gramDet x.1) * (C₁.prod C₂).N x) fun x u => ?_).trans ?_
  · have e1 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K (C₁.prod C₂) x u).1
    have e2 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K C₁ x.1 (Units.map (MonoidHom.fst C₁.A C₂.A) u)).2
    exact congrArg₂ (· * ·) e2 e1
  · exact finsum_congr fun k => congrArg₂ (· * ·) (h₁.eta_eq _) ((h₁.prod h₂).N_eq _)

theorem IsIso.identity {B₁ B₂ C₁ C₂ : InvAlg K} {φ₁ : B₁.A ≃ₐ[K.E] C₁.A} {φ₂ : B₂.A ≃ₐ[K.E] C₂.A}
    (h₁ : IsIso φ₁) (h₂ : IsIso φ₂) (h : InvAlg.Identity C₁ C₂) : InvAlg.Identity B₁ B₂ := by
  unfold InvAlg.Identity at h ⊢
  rwa [h₁.kapSum_eq h₂, h₁.stSum_eq, h₂.stSum_eq, h₁.charpoly_eq_of_isIso, h₂.charpoly_eq_of_isIso] at h

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

theorem identity_integral (hL : UnitLemmaLie) (hK : K.Odd) (n : ℕ) : ∀ B₁ B₂ : InvAlg K,
    Module.finrank K.E B₁.A + Module.finrank K.E B₂.A = n → B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 →
    (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → InvAlg.Identity B₁ B₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B₁ B₂ hn u₁ u₂ hs i₁ i₂
  by_cases h : ∀ e ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
      e * e = e → (B₁.prod B₂).σ e = e → e = 0 ∨ e = 1
  · rcases one_orbit (B₁.prod B₂) (Prod.ext u₁ u₂) (prod_integral _ _ i₁ i₂) h with h | h
    · exact GlobalTheory.T.involutive_algebra_product_identity K B₁ B₂ u₁ u₂ hs i₁ i₂ h
    · exact GlobalTheory.T.unitLemma_local_oddResidue_of_lieAlgebra hL K hK B₁ B₂ u₁ u₂ hs i₁ i₂ h
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
  refine (isIso_cut B₁ j₁ s₁).identity (isIso_cut B₂ j₂ s₂) ?_
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

theorem unitLemmaGroup_of_lie : UnitLemmaLie → UnitLemmaGroup := by
  intro hL K hK B₁ B₂ u₁ u₂ hs
  by_cases hi : IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g
  · exact identity_integral hL hK _ B₁ B₂ rfl u₁ u₂ hs hi.1 hi.2
  · obtain ⟨h1, h2⟩ := GlobalTheory.T.kappaSum_zero_and_stableSum_mul_zero_of_not_integral K B₁ B₂ hi
    unfold InvAlg.Identity
    rw [h1, h2, mul_zero]

end GlobalTheory.UnitLemma.Orbit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValueMemFiltrationZeroTame
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.ValueFil

section Rings

variable {l : ℕ} [Fact l.Prime]

theorem toB_tmul_pt {O : Type} [CommRing O] [Algebra ℤ_[l] O] (o : O) (w : Per.Ainf l) :
    toB l O (o ⊗ₜ[ℤ_[l]] w) = o ⊗ₜ[ℤ_[l]] Per.aB l w := by
  rw [GlobalTheory.RingIface.aB_alg]
  rfl

theorem core_ι_aB (C : GlobalTheory.MemLoc.Core l) (w : Per.Ainf l) :
    C.ι (Per.aB l w) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l w) := by
  rw [GlobalTheory.RingIface.aB_alg, C.ι_j, GlobalTheory.MemLoc.LogEx.algebraMap_acris, C.j_cris.on0, Subalgebra.coe_algebraMap]
  rfl

theorem one_mem_filZero : (1 : Per.BdR l) ∈ Per.FilD l 0 :=
  (GlobalTheory.MemLoc.filD_laws l).2.1

theorem alg_mem_filZero (u : Per.BdRp l) : algebraMap (Per.BdRp l) (Per.BdR l) u ∈ Per.FilD l 0 := by
  rw [← mul_one (algebraMap (Per.BdRp l) (Per.BdR l) u), ← Algebra.smul_def]
  exact Submodule.smul_mem _ u one_mem_filZero

theorem isUnit_aDp_of_theta {x : Per.Ainf l} (hx : (Per.θ l x : ℂ_[l]) ≠ 0) :
    IsUnit (GlobalTheory.MemLoc.aDp l x) :=
  (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]; exact hx)

theorem ι_mem_filZero_of_mul (C : GlobalTheory.MemLoc.Core l) {d : Per.Bcris l} {x : Per.Ainf l} {n : ℕ}
    (hd : d * Per.aB l x ^ n = 1) (hx : IsUnit (GlobalTheory.MemLoc.aDp l x)) : C.ι d ∈ Per.FilD l 0 := by
  obtain ⟨v, hv⟩ := hx
  have h1 : C.ι d * algebraMap (Per.BdRp l) (Per.BdR l) ((v : Per.BdRp l) ^ n) = 1 := by
    rw [map_pow, hv, ← core_ι_aB, ← map_pow, ← map_mul, hd, map_one]
  have h2 : C.ι d = algebraMap (Per.BdRp l) (Per.BdR l) (((v⁻¹ : (Per.BdRp l)ˣ) : Per.BdRp l) ^ n) := by
    calc C.ι d = C.ι d * algebraMap (Per.BdRp l) (Per.BdR l)
          ((v : Per.BdRp l) ^ n * ((v⁻¹ : (Per.BdRp l)ˣ) : Per.BdRp l) ^ n) := by
          rw [← mul_pow, Units.mul_inv, one_pow, map_one, mul_one]
      _ = _ := by rw [map_mul, ← mul_assoc, h1, one_mul]
  rw [h2]
  exact alg_mem_filZero _

theorem theta_σA_ne_zero (g : Per.Gq l) {x : Per.Ainf l} (hx : (Per.θ l x : ℂ_[l]) ≠ 0) :
    (Per.θ l (Per.σA g x) : ℂ_[l]) ≠ 0 := by
  intro h
  apply hx
  have h' : Per.σC g (Per.θ l x : ℂ_[l]) = 0 := by
    rw [← (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, ← (GlobalTheory.MemLoc.thetaD_props l).2.2.2.2,
      (GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.1, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
    exact h
  rw [← norm_eq_zero, ← GlobalTheory.RingBasics.norm_σC g, h', norm_zero]

end Rings

section Tensor

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
  {G : Type} [Group G] [TopologicalSpace G]

theorem TWincl_smul {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) : TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s x =>
    simp only [TWincl, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem TWact_smul {R : Type} [CommRing R] [Algebra O R] (f : R →ₐ[O] R) (T : LocLat G ℚ_[l] K O) (g : G)
    (r : R) (z : TW R T) : TWact f T g (r • z) = f r • TWact f T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s x =>
    simp only [TWact, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem TWact_TWincl (h : GQ l) (T : LocLat G ℚ_[l] K O) (g : G) (z : TW (OA l O) T) :
    TWact (galOB O h) T g (TWincl (toB l O) T z) = TWincl (toB l O) T (TWact (galOA O h) T g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c x =>
    simp only [TWact, TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply]
    congr 1
    rw [toB, AlgHom.comp_apply, AlgHom.comp_apply, galOB_toOB, galOCr_toOCr]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem smul_TWincl_mem (C : GlobalTheory.MemLoc.Core l) (T : LocLat G ℚ_[l] K O) {d : Per.Bcris l}
    (hd : C.ι d ∈ Per.FilD l 0) (z : TW (OA l O) T) :
    ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • TWincl (toB l O) T z ∈ Submodule.span O {w : TW (OB l O) T |
      ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | tmul c x =>
    change ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • (toB l O c ⊗ₜ[O] x) ∈ _
    rw [smul_tmul', smul_eq_mul]
    induction c using TensorProduct.induction_on with
    | zero => rw [map_zero, mul_zero, zero_tmul]; exact zero_mem _
    | tmul o w =>
      have e : ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) * toB l O (o ⊗ₜ w) =
          o • ((1 : O) ⊗ₜ[ℤ_[l]] (d * Per.aB l w) : OB l O) := by
        rw [toB_tmul_pt, Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e, ← smul_tmul']
      refine Submodule.smul_mem _ o (Submodule.subset_span ⟨d * Per.aB l w, x, ?_, rfl⟩)
      rw [map_mul, core_ι_aB, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hd
    | add c c' hc hc' => rw [map_add, mul_add, add_tmul]; exact add_mem hc hc'
  | add z z' hz hz' => rw [map_add, smul_add]; exact add_mem hz hz'

end Tensor

end GlobalTheory.BKGal.ValueFil

open GlobalTheory.BKGal.ValueFil in

theorem GlobalTheory.BKGal.value_mem_filtration_zero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (m₀ : ι → OW l O), phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩ → ∃ b₁, IsCrisVal t ϖ D.toPhiMod R.jB m₀ b₁ ∧ ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g b₁ - b₁ ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R y hyY hy m₀ h1

  obtain ⟨ζ, ε, h0, -, hz1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => hz1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have hδl : ((frobeniusEquiv (Per.Fl l) l).symm ε) ^ l = ε := by
    rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  have hEps : IsEps ε := ⟨he, _, hδl, hE.2⟩
  set δ := (frobeniusEquiv (Per.Fl l) l).symm ε with hδ

  obtain ⟨hMA, -⟩ := GlobalTheory.T.breuilKisin_mu_pow_smul_frobenius_mem_ainf l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hEps hδl
    ⟨y, hy⟩ hyY.1 m₀ h1
  obtain ⟨-, hK2, hK3, -⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hEps hδl
  obtain ⟨z, hz⟩ := hK2 _ hMA

  have hLA : ∀ (c : OA l O) {v : ι → OW l O}, v ∈ LA t ϖ D.toPhiMod → inclO l O c • v ∈ LA t ϖ D.toPhiMod := by
    rintro c _ ⟨d, rfl⟩
    exact ⟨fun i => c * d i, inclL_smul_coord t ϖ D.toPhiMod c d⟩
  have hT : ∀ z' : TW (OA l O) T, inclO l O (1 ⊗ₜ (muOf ε ^ H)) • R.I.j.symm (TWincl (inclO l O) T z') ∈
      LA t ϖ D.toPhiMod := by
    intro z'
    induction z' using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, smul_zero]; exact zero_mem _
    | tmul c x =>
      have e1 : TWincl (inclO l O) T (c ⊗ₜ[O] x) = inclO l O c • ((1 : OW l O) ⊗ₜ[O] x) := by
        rw [smul_tmul', smul_eq_mul, mul_one]; rfl
      rw [e1, map_smul, smul_comm]
      exact hLA c (hK3 x)
    | add c c' hc hc' => rw [map_add, map_add, smul_add]; exact add_mem hc hc'
  obtain ⟨cc, hcc⟩ := hT z
  rw [← hz, LinearEquiv.symm_apply_apply] at hcc

  have hB := R.cmp cc ((1 ⊗ₜ (muOf ε ^ H) : OA l O) • z) (by
    rw [hcc, map_smul, hz, TWincl_smul])
  rw [TWincl_smul] at hB

  have hμu : IsUnit (Per.aB l (muOf ε)) := by
    rw [GlobalTheory.RingIface.aB_alg]
    exact GlobalTheory.MemLoc.TFil.isUnit_mu hE
  have hνu : IsUnit (Per.aB l (muOf δ)) := by
    have e2 : Per.aB l (muOf ε) = Per.aB l (GlobalTheory.MemLoc.xi ε) * Per.aB l (muOf δ) := by
      rw [← map_mul]
      exact congrArg (Per.aB l) (GlobalTheory.MemLoc.TFil.mu_eq ε)
    rw [e2] at hμu
    exact isUnit_of_mul_isUnit_right hμu
  have hθν : (Per.θ l (muOf δ) : ℂ_[l]) ≠ 0 := by
    change (Per.θ l (Per.tm δ - 1) : ℂ_[l]) ≠ 0
    rw [map_sub, map_one, WittVector.fontaineTheta_teichmuller]
    intro h
    apply hE.2
    rw [← sub_eq_zero]
    exact Subtype.ext h
  set n := η + (H + η) with hn
  set d : Per.Bcris l := ((hνu.unit⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) ^ n with hd
  have hdn : d * Per.aB l (muOf δ) ^ n = 1 := by
    rw [hd, ← mul_pow, IsUnit.val_inv_mul, one_pow]
  have hm : ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ H * (muOf δ ^ η * muOf δ ^ (H + η))) : OA l O) =
      (1 ⊗ₜ (muOf ε ^ H)) * ((1 ⊗ₜ (muOf δ ^ η)) * (1 ⊗ₜ (muOf δ ^ (H + η)))) := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  refine ⟨((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • TWincl (toB l O) T z,
    ⟨(1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ H * (muOf δ ^ η * muOf δ ^ (H + η))), cc, ?_, ?_, ?_⟩, ?_⟩
  · have hu : IsUnit (Per.aB l (muOf ε ^ H * (muOf δ ^ η * muOf δ ^ (H + η)))) := by
      rw [map_mul, map_mul, map_pow, map_pow, map_pow]
      exact (hμu.pow H).mul ((hνu.pow _).mul (hνu.pow _))
    have := hu.map (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
    rw [Algebra.TensorProduct.includeRight_apply] at this
    rw [toB_tmul_pt]
    exact this
  · rw [hcc, hm, map_mul, map_mul, mul_smul, mul_smul]
  · rw [hB, smul_smul]
    congr 1
    rw [toB_tmul_pt, toB_tmul_pt, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    have hdn' : d * Per.aB l (muOf δ) ^ (η + (H + η)) = 1 := hdn
    rw [map_mul, map_mul, map_pow, map_pow, map_pow]
    linear_combination (Per.aB l (muOf ε) ^ H) * hdn'
  · intro g _ C
    refine sub_mem ?_ (smul_TWincl_mem C T (ι_mem_filZero_of_mul C hdn (isUnit_aDp_of_theta hθν)) z)
    change TWact (galOB O (sQ l g)) T g (((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • TWincl (toB l O) T z) ∈ _
    rw [TWact_smul, TWact_TWincl]
    have hg : Per.σB (sQ l g) d * Per.aB l (Per.σA (sQ l g) (muOf δ)) ^ n = 1 := by
      rw [← (GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.2.1, ← map_pow, ← map_mul, hdn, map_one]
    exact smul_TWincl_mem C T (ι_mem_filZero_of_mul C hg
      (isUnit_aDp_of_theta (theta_σA_ne_zero (sQ l g) hθν))) _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNInvQPowGammaStableStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachN_invQPow_gamma_stable : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; let u : ↥LL.1 := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)); ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ k : ℕ, (∀ x : W.DD T, W.Q ^ k • x ∈ W.N T → W.Q ^ k • W.γ T x ∈ W.N T) ∧ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ w : PowerSeries ↥LL.1, PowerSeries.constantCoeff w = u ^ (-(k : ℤ)) ∧ ∀ (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T) (hγ : W.Q ^ k • W.γ T x ∈ W.N T) (j : ℤ), ex C h T i ζ ⟨W.Q ^ k • W.γ T x, hγ⟩ j = conv w (fun m => u ^ m • ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ m) j := by
  first | exact @GlobalTheory.NL.GamQ.gam_Q_pow | exact GlobalTheory.NL.GamQ.gam_Q_pow | (intros; apply GlobalTheory.NL.GamQ.gam_Q_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionPosOfCuspidalCharacterStatement
section
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerDimension_pos_of_cuspidal_character : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → ∃ m : ℕ, 0 < m ∧ wh ψ χ = m := by
  first | exact @GlobalTheory.GLq.wh_cusp_pos | exact GlobalTheory.GLq.wh_cusp_pos | (intros; apply GlobalTheory.GLq.wh_cusp_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittCompletedTiltColumnsOfRightInverseModPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittCompletedTilt_columns_of_right_inverse_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (d d' n : ℕ) (Q : Matrix (Fin d) (Fin d') (WCb l)) (S : Matrix (Fin d') (Fin d) (WCb l)) (U Uinv : Matrix (Fin d') (Fin d') (WCb l)) (J : Finset (Fin d')), 1 ≤ n → (∀ i j, (l : WCb l) ^ n ∣ (Q * S - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → Uinv * U = 1 → U * Uinv = 1 → (∀ j ∉ J, ∀ i, (l : WCb l) ^ n ∣ (Q * U) i j) → (∀ v : Fin d' → WCb l, (∀ i, (l : WCb l) ^ n ∣ (Q *ᵥ v) i) → ∀ j ∈ J, (l : WCb l) ∣ (Uinv *ᵥ v) j) → ∃ e : Fin d ≃ J, IsUnit (Q * U.submatrix id (fun k => (e k : Fin d'))) ∧ ∀ i j, (l : WCb l) ^ n ∣ (Q - (Q * U.submatrix id (fun k => (e k : Fin d'))) * Uinv.submatrix (fun k => (e k : Fin d')) id) i j := by
  first | exact @GlobalTheory.CardJ.exists_cols_of_rightInv_WCb | exact GlobalTheory.CardJ.exists_cols_of_rightInv_WCb | (intros; apply GlobalTheory.CardJ.exists_cols_of_rightInv_WCb; all_goals assumption)
end

