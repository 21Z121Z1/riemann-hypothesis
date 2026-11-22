import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PsiCondAll
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormCoprimeOfSup
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0122
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0302
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepValueEqTrilinearTensorValueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStepValue_eq_trilinearTensorValue : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (T₁ : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.B.V S.J.W → ℂ)) (T₂ : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.J.W S.B'.V → ℂ)), (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ → ∀ (U₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) →ₗ[ℂ] (WO S.B.V₀ S.J.W₀ → ℂ)) (U₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) →ₗ[ℂ] (WO S.J.W₀ S.B'.V₀ → ℂ)), (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) Φ.1 → flatBF S.s₁ (T₁ Φ) = U₁ Ψ) → (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) Φ.1 → flatFB S.s₂ (T₂ Φ) = U₂ Ψ) → (∀ Ψ₁ Ψ₂, ∃ Ξ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k), Ξ.1 = GlobalTheory.LocFlat.contr Q.ψk Q.ν Ψ₁.1 Ψ₂.1 ∧ GlobalTheory.Unf.contr S.l S.J.W₀ S.vL (U₁ Ψ₁) (U₂ Ψ₂) = Λ Ξ) → ∀ (T : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] GlobalTheory.TriStep.space Q →ₗ[ℂ] ℂ), (∀ Ξ f, T Ξ f = GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f.1) → ∀ Φ₁ Φ₂ (f : GlobalTheory.TriStep.space Q), HasTensorVal (fun Ψ Φ₀ => app (((GlobalTheory.LocFlat.CFac.prodSBBil _ _).compr₂ T) Ψ) (opEFJ Q.ψk Q.ν (σ + 1) Φ₀.1 Φ₂.1) f) (fl Q.ψk Q.ν Q.μ₁ (σ + 1) Φ₁.1) (S.val c₁ c₂ (T₁ Φ₁) (T₂ Φ₂) φ f.1 1 1 1) := by
  first | exact @GlobalTheory.TriStep.val_eq_tensorVal | exact GlobalTheory.TriStep.val_eq_tensorVal | (intros; apply GlobalTheory.TriStep.val_eq_tensorVal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdditiveCharNeOneAtEachPrime
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FiniteCharNontrivial

theorem trace_eq_tau (I : AutInst) (x : I.E) :
    Algebra.trace ℚ I.E x = Algebra.trace ℚ I.F (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x) := by
  have h1 : Algebra.trace ℚ I.E (star x) = Algebra.trace ℚ I.E x :=
    Algebra.trace_eq_of_algEquiv ((starRingAut : I.E ≃+* I.E).equivRatAlgEquiv _ _) x
  have h2 : Algebra.trace ℚ I.E (algebraMap I.F I.E (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x)) =
      2 * Algebra.trace ℚ I.F (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x) := by
    rw [← Algebra.trace_trace (S := I.F), Algebra.trace_algebraMap, I.cm.deg2, map_nsmul, nsmul_eq_mul]
    norm_num
  rw [PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, map_add, h1] at h2
  linarith

theorem exists_away {E : Type} [Field E] [NumberField E] (g : 𝓞 E) (hg : g ≠ 0)
    (Q : HeightOneSpectrum (𝓞 E)) :
    ∃ j : 𝓞 E, j ∉ Q.asIdeal ∧ ∀ Q' : HeightOneSpectrum (𝓞 E), g ∈ Q'.asIdeal → Q' ≠ Q → j ∈ Q'.asIdeal := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ Ideal.span {g}}.Finite :=
    Ideal.finite_factors (by simpa using hg)
  have hch : ∀ v : HeightOneSpectrum (𝓞 E), ∃ a : 𝓞 E, a ∉ Q.asIdeal ∧ (v ≠ Q → a ∈ v.asIdeal) := by
    intro v
    by_cases hv : v = Q
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 Q.isPrime.ne_top, fun h => (h hv).elim⟩
    · have hn : ¬ v.asIdeal ≤ Q.asIdeal := fun hle =>
        hv (HeightOneSpectrum.ext (v.isMaximal.eq_of_le Q.isPrime.ne_top hle))
      obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.1 hn
      exact ⟨a, ha', fun _ => ha⟩
  choose a ha ha' using hch
  refine ⟨∏ v ∈ hfin.toFinset, a v, ?_, ?_⟩
  · have := Q.isPrime
    intro h
    obtain ⟨v, -, hv⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact ha v hv
  · intro Q' hQ' hne
    have hm : Q' ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
      exact hQ'
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a hm) (ha' Q' hne)

theorem core (I : AutInst) (psiEf : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F → ℂ)
    (hrat : ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) * psiEinf I x = 1)
    (g : ℕ) (hg : g ≠ 0) (Q : HeightOneSpectrum (𝓞 I.E)) (hgQ : ((g : ℕ) : 𝓞 I.E) ∈ Q.asIdeal)
    (hun : Algebra.IsUnramifiedAt ℤ Q.asIdeal) (j : 𝓞 I.E) (hj : j ∉ Q.asIdeal) :
    ∃ z : 𝓞 I.E, psiEf (divN I g (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)
      (algebraMap (𝓞 I.E) I.E (j * z)))) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hgE : (g : I.E) ≠ 0 := Nat.cast_ne_zero.2 hg
  have htr : ∀ z : 𝓞 I.E, ∃ n : ℤ, Algebra.trace ℚ I.E
      ((g : I.E)⁻¹ * algebraMap (𝓞 I.E) I.E j * algebraMap (𝓞 I.E) I.E z) = n := by
    intro z
    have e : divN I g (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (algebraMap (𝓞 I.E) I.E (j * z))) =
        Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)
          ((g : I.E)⁻¹ * algebraMap (𝓞 I.E) I.E j * algebraMap (𝓞 I.E) I.E z) := by
      have e1 : algebraMap I.F (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ((g : I.F)⁻¹) =
          Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) ((g : I.E)⁻¹) := by
        rw [Algebra.TensorProduct.algebraMap_apply, map_inv₀, map_natCast]
        rfl
      rw [divN, e1, ← RingHom.map_mul, RingHom.map_mul (algebraMap (𝓞 I.E) I.E), mul_assoc]
    have h1 := hcon z
    rw [e] at h1
    have h2 := hrat ((g : I.E)⁻¹ * algebraMap (𝓞 I.E) I.E j * algebraMap (𝓞 I.E) I.E z)
    rw [h1, one_mul] at h2
    rw [trace_eq_tau]
    exact PsiCondAllPf.trace_of_psi I _ h2
  obtain ⟨d, hd, hdQ⟩ := PsiCondAllPf.exists_diff_not_mem Q hun
  obtain ⟨c, hc⟩ := PsiCondAllPf.mul_diff_int _ htr d hd
  have hcg : (g : 𝓞 I.E) * c = j * d := by
    apply RingOfIntegers.coe_injective
    rw [RingHom.map_mul, RingHom.map_mul, hc, map_natCast]
    field_simp
  have hm : j * d ∈ Q.asIdeal := hcg ▸ Ideal.mul_mem_right _ _ hgQ
  rcases Q.isPrime.mem_or_mem hm with h | h
  exacts [hj h, hdQ h]

theorem exists_psi_ne_one : ∀ (D : D7) (psiEf : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F → ℂ), (∀ x y, psiEf (x + y) = psiEf x * psiEf y) → (∀ x ∈ IntAf (instOf D).F (instOf D).E, psiEf x = 1) → (∀ x : (instOf D).E, psiEf (Formalism.UG.inclE (F := (instOf D).F) (Formalism.MainNotions.S.Af (instOf D).F) x) * psiEinf (instOf D) x = 1) → ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ Q' : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q'.asIdeal → Q' ≠ Q → resS D.host.F Q' s = 0) ∧ psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) ≠ 1 := by
  intro D psiEf _ _ hrat Q hQ
  have hg : D.host.g 0 * D.host.g 1 ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
    have hQ' := hQ
    rw [Nat.cast_mul] at hQ'
    rcases Q.isPrime.mem_or_mem hQ' with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  have hun : Algebra.IsUnramifiedAt ℤ Q.asIdeal :=
    PsiCondAllPf.unram_of (D.host.g i) (D.host.g_prime i) Q hi
      (Formalism.L2.SG.Pf.TypedLoc.tower_ef D.host.E D.host.E (D.host.g_prime i) (D.nd.g_split i) Q hi).1
  obtain ⟨j, hj, hj'⟩ := exists_away ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) (Nat.cast_ne_zero.2 hg) Q
  obtain ⟨z, hz⟩ := core (instOf D) psiEf hrat _ hg Q hQ hun j hj
  let z' : 𝓞 D.host.E := z
  refine ⟨oToS D.host.F D.host.E (j * z'), fun Q' h1 h2 => ?_, hz⟩
  rw [resS_oToS, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (hj' Q' h1 h2)

end GlobalTheory.FiniteCharNontrivial
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralAdelePrescribedResiduesAndConj
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConjResidueSurj
open GlobalTheory.IdemSupport

theorem sigInt_oToS {D : D7} (a : 𝓞 D.host.E) :
    sigInt (instOf D) (oToS D.host.F D.host.E a) = oToS D.host.F D.host.E (cO D a) :=
  Subtype.ext (Formalism.L2.SG.Pf.unitaryCongruence.sigA_inclE (instOf D) (a : D.host.E))

theorem exists_res_and_conj (D : D7) (Pg : Finset (Pl D.host.E))
    (h : ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP')
    (u u' : ∀ PP : Pl D.host.E, kP PP) :
    ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP ∈ Pg,
      resS D.host.F PP s = u PP ∧ resS D.host.F PP (sigInt (instOf D) s) = u' PP := by
  classical
  choose a ha using fun PP : Pl D.host.E => Ideal.Quotient.mk_surjective (I := PP.asIdeal) (u PP)
  choose a' ha' using fun PP : Pl D.host.E => Ideal.Quotient.mk_surjective (I := PP.asIdeal) (u' PP)
  have hout : ∀ PP ∈ Pg, cP PP ∉ Pg := fun PP hPP h' =>
    h PP hPP _ h' ((isConjPl_iff _ _).2 rfl)
  let T : Finset (Pl D.host.E) := Pg ∪ Pg.image cP
  let x : Pl D.host.E → 𝓞 D.host.E := fun Q => if Q ∈ Pg then a Q else cO D (a' (cP Q))
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun Q : Pl D.host.E => Q.asIdeal) (fun _ => 1) (fun Q _ => Q.prime)
    (fun Q _ Q' _ hne e => hne (HeightOneSpectrum.ext e)) (fun Q => x Q.1)
  refine ⟨oToS D.host.F D.host.E y, fun PP hPP => ⟨?_, ?_⟩⟩
  · have h1 := hy PP (Finset.mem_union_left _ hPP)
    rw [pow_one] at h1
    have h2 : x PP = a PP := if_pos hPP
    rw [resS_oToS, ← ha PP, ← h2]
    exact Ideal.Quotient.eq.2 h1
  · have h1 := hy (cP PP) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hPP))
    rw [pow_one] at h1
    have h2 : x (cP PP) = cO D (a' PP) := by
      have : x (cP PP) = cO D (a' (cP (cP PP))) := if_neg (hout PP hPP)
      rw [this, GlobalTheory.StdFrames.cP_cP]
    have h3 : y - cO D (a' PP) ∈ (cP PP).asIdeal := h2 ▸ h1
    rw [mem_cP, map_sub, cO_cO] at h3
    rw [sigInt_oToS, resS_oToS, ← ha' PP]
    exact Ideal.Quotient.eq.2 h3

end GlobalTheory.ConjResidueSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeFrameLiftingSpanningVectorsMod
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftFrameMod

section Alg

variable {R : Type} [CommRing R] {n : ℕ}

theorem det_one_sub_smul (c : R) (X : Matrix (Fin n) (Fin n) R) :
    ∃ a : R, (1 - c • X).det = 1 - c * a := by
  have h : Ideal.Quotient.mk (Ideal.span {c}) (1 - c • X).det = 1 := by
    rw [RingHom.map_det]
    have : (Ideal.Quotient.mk (Ideal.span {c})).mapMatrix (1 - c • X) = 1 := by
      ext i j
      simp [Matrix.one_apply, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self c)]
    rw [this, Matrix.det_one]
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {c})), Ideal.Quotient.eq] at h
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨-a, by linear_combination -ha⟩

theorem isUnit_mix {e g : R} (he : e * e = e) (hu : ∀ a : R, IsUnit (1 - e * g * a))
    (M C X : Matrix (Fin n) (Fin n) R) (h : M * C = 1 - g • X) :
    IsUnit (e • M + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) := by
  have h1 : (e • M + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) * (e • C + (1 - e) • 1) = 1 - (e * g) • X := by
    rw [GlobalTheory.IdemSupport.mix_mul he, h, Matrix.one_mul, smul_sub, smul_smul, sub_add_eq_add_sub,
      GlobalTheory.IdemSupport.mix_self]
  obtain ⟨a, ha⟩ := det_one_sub_smul (e * g) X
  rw [Matrix.isUnit_iff_isUnit_det]
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, ha] at h2
  exact isUnit_of_mul_isUnit_left (h2 ▸ hu a : IsUnit _)

theorem exists_lift {A : Type} [CommRing A] (S : Subring A) (g : ℕ) {e t : S} (he : e * e = e) (ht : 1 - e = g * t)
    (hu : ∀ a : S, IsUnit (1 - e * g * a)) (Λ : Submodule S (Fin n → A)) (β₀ : GL (Fin n) A)
    (hβ : ∀ x, x ∈ Λ ↔ ∀ i, ((β₀⁻¹).val *ᵥ x) i ∈ S) (b : Fin n → Fin n → A) (hb : ∀ j, b j ∈ Λ)
    (hs : ∀ y ∈ Λ, y ∈ Submodule.span S (Set.range b) ⊔ Submodule.span S {y | ∃ x ∈ Λ, y = (g : A) • x}) :
    ∃ β : GL (Fin n) A, (∀ x, x ∈ Λ ↔ ∀ i, ((β⁻¹).val *ᵥ x) i ∈ S) ∧
      ∀ j, ∃ x ∈ Λ, (fun i => β.val i j) - b j = (g : A) • x := by
  have hback : ∀ v : Fin n → A, (β₀⁻¹).val *ᵥ (β₀.val *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  have hback' : ∀ v : Fin n → A, β₀.val *ᵥ ((β₀⁻¹).val *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  have hint : ∀ v : Fin n → S, β₀.val *ᵥ (fun i => (v i : A)) ∈ Λ := fun v => (hβ _).2 fun i => by
    rw [hback]; exact (v i).2
  let M : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨((β₀⁻¹).val *ᵥ b j) i, (hβ _).1 (hb j) i⟩
  have hg : ∀ z ∈ Submodule.span S {y | ∃ x ∈ Λ, y = (g : A) • x}, ∃ x ∈ Λ, z = (g : A) • x := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hy
      exact ⟨x + y, add_mem hx hy, (smul_add _ _ _).symm⟩
    | smul a x _ hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      exact ⟨a • x, Λ.smul_mem a hx, smul_comm _ _ _⟩
  have hcol : ∀ k : Fin n, ∃ c r : Fin n → S, ∀ i, (M *ᵥ c) i = (1 : Matrix (Fin n) (Fin n) S) i k - g * r i := by
    intro k
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hs _ (hint fun i => (1 : Matrix (Fin n) (Fin n) S) i k))
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hy
    obtain ⟨x, hx, rfl⟩ := hg z hz
    refine ⟨c, fun i => ⟨_, (hβ x).1 hx i⟩, fun i => Subtype.ext ?_⟩
    have h1 := congrArg (fun v => ((β₀⁻¹).val *ᵥ v) i) hyz
    simp only [hback, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec_sum,
      Finset.sum_apply] at h1
    have h2 : (((M *ᵥ c) i : S) : A) = ∑ j, c j • ((β₀⁻¹).val *ᵥ b j) i := by
      change S.subtype (∑ j, M i j * c j) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [h2, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, SubringClass.coe_natCast, ← h1, add_sub_cancel_right]
  choose c r hcr using hcol
  obtain ⟨U, hU⟩ := isUnit_mix he hu M (Matrix.of fun i k => c k i) (Matrix.of fun i k => r k i) (by
    ext i k
    exact congrArg Subtype.val (hcr k i))
  have hmv : ∀ (V : GL (Fin n) S) (v : Fin n → A), (∀ i, v i ∈ S) →
      ∀ i, ((GeneralLinearGroup.map S.subtype V).val *ᵥ v) i ∈ S := fun V v hv i => by
    change ∑ j, (V.val i j : A) * v j ∈ S
    exact sum_mem fun j _ => mul_mem (V.val i j).2 (hv j)
  refine ⟨β₀ * GeneralLinearGroup.map S.subtype U, fun x => ?_, fun j => ?_⟩
  · rw [hβ, _root_.mul_inv_rev, Units.val_mul, ← mulVec_mulVec, ← map_inv]
    refine ⟨hmv _ _, fun h => ?_⟩
    have := hmv U _ h
    rwa [mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mulVec] at this
  · refine ⟨_, hint fun i => t * ((1 : Matrix (Fin n) (Fin n) S) i j - M i j), ?_⟩
    have h1 : (fun i => (β₀ * GeneralLinearGroup.map S.subtype U).val i j) =
        β₀.val *ᵥ fun i => (U.val i j : A) := rfl
    rw [h1, ← hback' (b j), ← mulVec_sub, ← mulVec_smul]
    congr 1
    funext i
    have h2 : U.val i j - M i j = g * (t * ((1 : Matrix (Fin n) (Fin n) S) i j - M i j)) := by
      rw [hU, ← mul_assoc, ← ht]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have h3 := congrArg Subtype.val h2
    rw [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, SubringClass.coe_natCast] at h3
    exact h3

end Alg

open GlobalTheory.StdFrames GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices

theorem valued_natCast_lt_one_iff {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E)) (N : ℕ) :
    Valued.v (N : Q.adicCompletion E) < 1 ↔ (N : 𝓞 E) ∈ Q.asIdeal := by
  rw [← Q.valuation_lt_one_iff_mem (K := E) (N : 𝓞 E), ← Formalism.UG.P.levelaf_valued_algebraMap]
  simp

theorem exists_inv_of_valued {D : D7} (z : Ef D) (h : ∀ Q : Pl D.host.E, Valued.v (cpt Q z) = 1) :
    ∃ y ∈ OA D, z * y = 1 := by
  have hi : ∀ Q : Pl D.host.E, (cpt Q z)⁻¹ ∈ Q.adicCompletionIntegers D.host.E := fun Q => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h, inv_one]
  obtain ⟨y, hy⟩ := GlobalTheory.AdeleBaseChange.map_surjective (toAd_spec D)
    (⟨fun Q => (cpt Q z)⁻¹, Filter.Eventually.of_forall hi⟩ : FiniteAdeleRing (𝓞 D.host.E) D.host.E)
  have h1 : ∀ Q : Pl D.host.E, cpt Q y = (cpt Q z)⁻¹ := fun Q => by
    change toAd D y Q = _
    rw [hy]
    rfl
  refine ⟨y, (mem_OA_iff y).2 fun Q => h1 Q ▸ hi Q, cpt_ext fun Q => ?_⟩
  rw [RingHom.map_mul, RingHom.map_one, h1, mul_inv_cancel₀]
  intro h0
  have := h Q
  rw [h0, Valuation.map_zero] at this
  exact zero_ne_one this

theorem coe_one_sub {A : Type} [CommRing A] (S : Subring A) (g : ℕ) (e a : S) :
    ((1 - e * g * a : S) : A) = 1 - e * g * a := by
  push_cast
  rfl

theorem one_sub_eq {A : Type} [CommRing A] (S : Subring A) {g : ℕ} {c e : A} (hc : (g : A) * c = 1) (he : e ∈ S)
    (ht : c * (1 - e) ∈ S) : (1 - ⟨e, he⟩ : S) = g * ⟨_, ht⟩ := by
  refine Subtype.ext ?_
  push_cast
  rw [← mul_assoc, hc, one_mul]

section Val

variable {A K Γ : Type} [CommRing A] [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (φ : A →+* K)

theorem val_quot_le {g : ℕ} {c e : A} (hc : (g : A) * c = 1) (h : φ e = 1 ∨ φ e = 0 ∧ v (g : K) = 1) :
    v (φ (c * (1 - e))) ≤ 1 := by
  rcases h with h | ⟨h, h1⟩
  · simp [h]
  · have h2 := congrArg (fun x => v (φ x)) hc
    simp only [map_mul, map_natCast, map_one, h1, one_mul] at h2
    simp [h, h2]

theorem val_one_sub {g : ℕ} {a e : A} (ha : v (φ a) ≤ 1) (h : φ e = 1 ∧ v (g : K) < 1 ∨ φ e = 0) :
    v (φ (1 - e * g * a)) = 1 := by
  rcases h with ⟨h, h1⟩ | h
  · rw [map_sub, map_one, map_mul, map_mul, map_natCast, h, one_mul]
    refine Valuation.map_one_sub_of_lt _ ?_
    rw [map_mul]
    exact (mul_le_of_le_one_right' ha).trans_lt h1
  · simp [h]

end Val

theorem quot_mem {D : D7} {g : ℕ} {c e : Ef D} (hc : (g : Ef D) * c = 1)
    (he1 : ∀ Q : Pl D.host.E, (g : 𝓞 D.host.E) ∈ Q.asIdeal → cpt Q e = 1)
    (he0 : ∀ Q : Pl D.host.E, (g : 𝓞 D.host.E) ∉ Q.asIdeal → cpt Q e = 0) : c * (1 - e) ∈ OA D :=
  (mem_OA_iff _).2 fun Q => by
    refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (val_quot_le Valued.v (cpt Q) hc ?_)
    by_cases hQ : (g : 𝓞 D.host.E) ∈ Q.asIdeal
    · exact Or.inl (he1 Q hQ)
    · exact Or.inr ⟨he0 Q hQ, le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1
        (natCast_mem (Q.adicCompletionIntegers D.host.E) g))
        (not_lt.1 fun h => hQ ((valued_natCast_lt_one_iff Q g).1 h))⟩

theorem valued_one_sub {D : D7} {g : ℕ} {a e : Ef D} (ha : a ∈ OA D)
    (he1 : ∀ Q : Pl D.host.E, (g : 𝓞 D.host.E) ∈ Q.asIdeal → cpt Q e = 1)
    (he0 : ∀ Q : Pl D.host.E, (g : 𝓞 D.host.E) ∉ Q.asIdeal → cpt Q e = 0) (Q : Pl D.host.E) :
    Valued.v (cpt Q (1 - e * g * a)) = 1 := by
  refine val_one_sub Valued.v (cpt Q)
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((mem_OA_iff _).1 ha Q)) ?_
  by_cases hQ : (g : 𝓞 D.host.E) ∈ Q.asIdeal
  · exact Or.inl ⟨he1 Q hQ, (valued_natCast_lt_one_iff Q g).2 hQ⟩
  · exact Or.inr (he0 Q hQ)

theorem exists_idem_over (D : D7) {g : ℕ} (hg : g ≠ 0) :
    ∃ e c : Ef D, e * e = e ∧ e ∈ OA D ∧ (g : Ef D) * c = 1 ∧ c * (1 - e) ∈ OA D ∧
      ∀ a ∈ OA D, ∃ y ∈ OA D, (1 - e * g * a) * y = 1 := by
  obtain ⟨e, he, heO, he1, he0⟩ := exists_idem {Q : Pl D.host.E | (g : 𝓞 D.host.E) ∈ Q.asIdeal}
  obtain ⟨c, hc⟩ : ∃ c : Ef D, (g : Ef D) * c = 1 := by
    refine ⟨algebraMap D.host.E (Ef D) (g : D.host.E)⁻¹, ?_⟩
    rw [← map_natCast (algebraMap D.host.E (Ef D)), ← RingHom.map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hg),
      RingHom.map_one]
  exact ⟨e, c, he, heO, hc, quot_mem hc he1 he0, fun a ha => exists_inv_of_valued _ (valued_one_sub ha he1 he0)⟩

theorem idem_subring {A : Type} [CommRing A] (S : Subring A) {g : ℕ}
    (h : ∃ e c : A, e * e = e ∧ e ∈ S ∧ (g : A) * c = 1 ∧ c * (1 - e) ∈ S ∧
      ∀ a ∈ S, ∃ y ∈ S, (1 - e * g * a) * y = 1) :
    ∃ e t : S, e * e = e ∧ 1 - e = g * t ∧ ∀ a : S, IsUnit (1 - e * g * a) := by
  obtain ⟨e, c, he, heS, hc, ht, hu⟩ := h
  refine ⟨⟨e, heS⟩, ⟨_, ht⟩, Subtype.ext he, one_sub_eq S hc heS ht, fun a => ?_⟩
  obtain ⟨y, hy, h⟩ := hu a a.2
  refine IsUnit.of_mul_eq_one ⟨y, hy⟩ (Subtype.ext ?_)
  rw [MulMemClass.coe_mul, coe_one_sub]
  exact h

theorem hatL_eq_Lf (I : AutInst) : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext x
  exact ⟨fun ⟨y, hy, h⟩ => ⟨⟨y, hy⟩, h⟩, fun ⟨y, h⟩ => ⟨y.1, y.2, h⟩⟩

theorem exists_isLiftFrame : ∀ (D : D7) (g : ℕ), g ≠ 0 → ∀ b : ℕ → VA (instOf D), (∀ j, b j ∈ (instOf D).Lf) →
    (∀ y ∈ (instOf D).Lf, InMod (instOf D) g (Set.range fun j : Fin (instOf D).n => b j.val) y) →
    ∃ β, IsLiftFrame (instOf D) g b β := by
  intro D g hg b hb hs
  obtain ⟨e, t, he, ht, hu⟩ := idem_subring (IntAf (instOf D).F (instOf D).E) (g := g) (exists_idem_over D hg)
  generalize instOf D = I at *
  obtain ⟨β₀, h₀⟩ := GlobalTheory.latticeFrame.exists_frame I.F I.E I.n I.L ⟨I.L_fg, I.L_span⟩
  obtain ⟨β, h1, h2⟩ := exists_lift (IntAf I.F I.E) g he ht hu I.Lf β₀ (fun x => hatL_eq_Lf I ▸ h₀ x)
    (fun j => b j.val) (fun j => hb j.val) hs
  exact ⟨β, fun x => (hatL_eq_Lf I).symm ▸ h1 x, fun j => Submodule.subset_span (h2 j)⟩

end GlobalTheory.LiftFrameMod

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocPlOff
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocMod ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SeeSaw.LocPlInhab
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

theorem exists_latInd (q : GlobalTheory.FinPl.SplitPt D k) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y)
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') :
    ∃ Φ₀ : SB (Matrix Y Y' k), Φ₀.1 0 = 1 ∧
      Φ₀.1 = Set.indicator {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} (fun _ => 1) := by
  obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem q
  have h1 : {x | (ofSplit q).up FS FT x ∈ latO S T (M : Set _) (M' : Set _) (· = q.v)} =
      (((latO S T M M' fun _ => True).comap (Witness.upH (ofSplit q) FS FT) : AddSubgroup _) : Set (Matrix Y Y' k)) := by
    ext x
    refine ⟨fun h => GlobalTheory.PlaceModel.latO_le_top _ h, fun h => ?_⟩
    have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε q.split.1 heε h).1
    have h3 : q.e • (Witness.upH (ofSplit q) FS FT) x = (ofSplit q).up FS FT x :=
      (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (Witness.up_half (ofSplit q) FS FT x))
    rwa [h3] at h2
  rw [h1]
  have ho := Witness.lat_open (ofSplit q) FS FT hS hT
  have hk := Witness.lat_compact (ofSplit q) FS FT hS hT
  generalize ((latO S T _ _ fun _ => True).comap (Witness.upH (ofSplit q) FS FT) : AddSubgroup _) = A at ho hk
  have hcl : IsClopen (A : Set (Matrix Y Y' k)) := ⟨A.isClosed_of_isOpen ho, ho⟩
  exact ⟨⟨(A : Set (Matrix Y Y' k)).indicator 1, (LocallyConstant.charFn ℂ hcl).isLocallyConstant,
      HasCompactSupport.intro hk fun x hx => Set.indicator_of_notMem hx _⟩, Set.indicator_of_mem A.zero_mem _, rfl⟩

theorem exists_locPl {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (q : GlobalTheory.FinPl.SplitPt D k) (hq : q.UnitAA)
    (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (Φ : SB (Matrix Y Y' k))
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') :
    ∃ L : LocPl ψ S T M M', L.q.v = q.v ∧ L.q.e = q.e ∧
      ∀ x, prodDat (fun _ : Fin 1 => L) ((ofSplit q).up FS FT x) = Φ.1 x := by
  obtain ⟨O, hO, h0⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  obtain ⟨Φ₀, h1, h2⟩ := exists_latInd q FS FT hS hT
  obtain ⟨e, e1, e2⟩ := GlobalTheory.LocComb.exists_comb D k (ofSplit q) Y Y' S T FS FT ψ hψ O Φ (by rintro rfl; simp at h0)
  obtain ⟨o, o1, o2⟩ := GlobalTheory.LocComb.exists_comb D k (ofSplit q) Y Y' S T FS FT ψ hψ Φ₀ O (by rintro rfl; simp at h1)
  refine ⟨⟨k, q, hq, Y, Y', FS, FT, Φ, e, ⟨e1, fun Tm hT a b ha hb => ?_⟩, o, o1, fun Tm hT a b hb ha => ?_⟩, rfl, rfl, fun x => ?_⟩
  · obtain rfl : a = O := Subtype.ext (ha.trans hO.symm)
    obtain rfl : b = Φ := Subtype.ext hb
    exact e2 Tm hT
  · obtain rfl : b = O := Subtype.ext (hb.trans hO.symm)
    obtain rfl : a = Φ₀ := Subtype.ext (ha.trans h2.symm)
    exact o2 Tm hT
  · unfold prodDat
    rw [Fin.sum_univ_one, Fin.prod_univ_one]
    exact (if_pos (Witness.up_half (ofSplit q) FS FT x)).trans (congrArg Φ.1 (Witness.down_up (ofSplit q) FS FT x))

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem exists_locPl_off {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (hS : IsSelfDualC S M) (hT : IsSelfDualC T M') (Z : Finset (GlobalTheory.FinPl.Pl D)) :
    ∃ L : LocPl ψ S T M M', L.q.v ∉ Z ∧ ∃ x, prodDat (fun _ : Fin 1 => L) x = 1 := by
  obtain ⟨v, p, hv, hP⟩ := GlobalTheory.FinPl.PlacesTest.exists_one_place D Z
  obtain ⟨O, -, h0⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Fv D.host.F v) (Y := Fin T.rank) (Y' := Fin S.rank)
  obtain ⟨L, h1, -, h2⟩ := exists_locPl hψ p (hP.unit ()) (Frame.ofGL 1) (Frame.ofGL 1) O hS hT
  have hpv : v = p.v := by obtain ⟨_, h⟩ := (hP.mem v).1 rfl; first | exact h | exact h.symm
  exact ⟨L, by rw [h1, ← hpv]; exact hv, _, (h2 0).trans h0⟩

end GlobalTheory.SeeSaw.LocPlInhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitWeightRealCenterActionFockMonomialStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_weight_real_center_action_fock_monomial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ k : KerDat S T, k.Is ψ θ x y → ∃ wt : (FVar D T.rank S.rank →₀ ℕ) → GA D S → ℂ, (∀ α, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ‖wt α z‖ = 1 ∧ ∀ c : WO S T →₀ ℂ, IsFinComb c → k.om (z, 1) (pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T c k.vac) (MvPolynomial.monomial α 1)) = wt α z • pureTensorO ψ θ S T x.s y.s x.B y.B (comb ψ S T c k.vac) (MvPolynomial.monomial α 1)) ∧ ∀ χ : GA D S → ℂ, {α | ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → wt α z = χ z}.Finite := by
  first | exact @GlobalTheory.CenFockWt.central_wt | exact GlobalTheory.CenFockWt.central_wt | (intros; apply GlobalTheory.CenFockWt.central_wt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteElementsActFockVectorsThroughDatumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteElements_act_fockVectors_through_datum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T) (k : KerDat S T), x.Is → y.Is → k.Is ψ θ x y → ∀ P, IsThetaFunO ψ S T (k.pt ψ θ x y P) ∧ ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ p : ℂ, k.om (g, h) (comb ψ S T k.c k.vac) = p • comb ψ S T k.c k.vac → k.om (g, h) (k.pt ψ θ x y P) = p • k.pt ψ θ x y P := by
  first | exact @GlobalTheory.FockFin.pt_finite | exact GlobalTheory.FockFin.pt_finite | (intros; apply GlobalTheory.FockFin.pt_finite <;> assumption)
end

