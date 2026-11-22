import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NablaSqEndomorphismEqSumGLOperators
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0377
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0376
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsGal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0312
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0041
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0373
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0047
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0018
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0055
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0324
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0378
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NablaSqEndomorphismEqSumGLOperatorsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nablaSq_endomorphism_eq_sum_GL_operators : ∀ (k : Type) [Field k] [CharZero k] (N : ℕ) (lam : DomWeight N),
    (∀ M : Submodule k (MvPolynomial (Fin N × Fin N) k), M ≤ nablaSq k N lam →
      (∀ g : GL (Fin N) k, ∀ f ∈ M, sqAct k N lam g f ∈ M) → M = ⊥ ∨ M = nablaSq k N lam) →
    ∀ φ : nablaSq k N lam →ₗ[k] nablaSq k N lam, ∃ (s : Finset (GL (Fin N) k)) (c : GL (Fin N) k → k),
      ∀ f : nablaSq k N lam, (φ f : MvPolynomial (Fin N × Fin N) k) = ∑ g ∈ s, c g • sqAct k N lam g f := by
  first | exact @GlobalTheory.NablaDensity.endo_eq_sum_sqAct | exact GlobalTheory.NablaDensity.endo_eq_sum_sqAct | (intros; apply GlobalTheory.NablaDensity.endo_eq_sum_sqAct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NablaSqUpperEigenvectorWeightEqHighestStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nablaSq_upperEigenvector_weight_eq_highest : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam0 : DomWeight n) (mu : Fin n → ℤ)
    (f : MvPolynomial (Fin n × Fin n) K), f ∈ nablaSq K n lam0 → f ≠ 0 →
    (∀ B : GL (Fin n) K, (B : Matrix (Fin n) (Fin n) K).BlockTriangular id →
      sqAct K n lam0 B f = (∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a) • f) → mu = lam0.w := by
  first | exact @GlobalTheory.HwEigen.mu_eq_of_upper_eigen | exact GlobalTheory.HwEigen.mu_eq_of_upper_eigen | (intros; apply GlobalTheory.HwEigen.mu_eq_of_upper_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormVZpowDegEq
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EpsInduction

section Norm

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω] {A : ValuationSubring Ω}

theorem pow_mul_pow_eq [IsAlgClosed Ω] {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') {σ : G K Ω} {σ' : G L Ω}
    (hσ : ∀ z, σ z = σ' z) {a b c e : ℕ} (H : ActsAs A q σ a b) (H' : ActsAs A q' σ' c e) :
    q ^ a * q' ^ e = q' ^ c * q ^ b := by
  have key : ∀ x, A.valuation x ≤ 1 → A.valuation (x ^ (q ^ a * q' ^ e) - x ^ (q' ^ c * q ^ b)) < 1 := by
    intro x hx
    have hy := val_apply_le_one H.1 hx
    have h1 := cong_pow (val_pow_le_one hy _) (val_pow_le_one hx _) (H.2 x hx) (q' ^ e)
    have h2 := H'.2 x hx
    rw [← hσ] at h2
    have h3 := cong_pow (val_pow_le_one hy _) (val_pow_le_one hx _) h2 (q ^ b)
    rw [← pow_mul, ← pow_mul] at h1 h3
    rw [mul_comm (q' ^ e)] at h3
    exact cong_trans (cong_symm h1) h3
  rcases lt_trichotomy (q ^ a * q' ^ e) (q' ^ c * q ^ b) with hlt | heq | hlt
  · obtain ⟨x, hx, hx'⟩ := exists_not_cong_pow (A := A) (by positivity) hlt
    exact absurd (cong_symm (key x hx)) hx'
  · exact heq
  · obtain ⟨x, hx, hx'⟩ := exists_not_cong_pow (A := A) (by positivity) hlt
    exact absurd (key x hx) hx'

end Norm

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L]
  [Algebra L Ω] [IsAlgClosure L Ω] {A : ValuationSubring Ω}
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A v} {h' : IsPlaceOver A v'}

theorem normV_zpow_deg_eq {σ : Weil h} {σ' : Weil h'} (hσ : ∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) :
    ((normV v : ℕ) : ℝ) ^ deg σ = ((normV v' : ℕ) : ℝ) ^ deg σ' := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨a, b, H⟩ := σ.2
  obtain ⟨c, e, H'⟩ := σ'.2
  have hq : 0 < normV v := zero_lt_one.trans (one_lt_normV v)
  have hq' : 0 < normV v' := zero_lt_one.trans (one_lt_normV v')
  have key := pow_mul_pow_eq hq hq' hσ H H'
  have hr : (0 : ℝ) < (normV v : ℕ) := by exact_mod_cast hq
  have hr' : (0 : ℝ) < (normV v' : ℕ) := by exact_mod_cast hq'
  rw [deg_eq H, deg_eq H', zpow_sub₀ hr.ne', zpow_sub₀ hr'.ne', div_eq_div_iff (by positivity) (by positivity),
    zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast]
  exact_mod_cast key

theorem normV_cpow_deg_eq (s : ℝ) {σ : Weil h} {σ' : Weil h'} (hσ : ∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) :
    (((normV v : ℕ) : ℂ) ^ (s : ℂ)) ^ deg σ = (((normV v' : ℕ) : ℂ) ^ (s : ℂ)) ^ deg σ' := by
  have key : ∀ (q : ℕ) (k : ℤ), ((q : ℂ) ^ (s : ℂ)) ^ k = ((((q : ℝ) ^ k) ^ s : ℝ) : ℂ) := fun q k => by
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    rw [← Real.rpow_intCast, ← Real.rpow_mul hq, mul_comm, Real.rpow_mul hq, Real.rpow_intCast, Complex.ofReal_zpow,
      Complex.ofReal_cpow hq, Complex.ofReal_natCast]
  rw [key, key, normV_zpow_deg_eq hσ]

def forgetN {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) : WDRep h V where
  ρ := a.ρ
  N := 0
  smooth := a.smooth
  semisimple := a.semisimple
  nilpotent := IsNilpotent.zero
  comm σ := by simp

end GlobalTheory.EpsInduction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormGaloisEquivariance
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

theorem laws_cast {D : D7} {T : CoreJ D} (L : LawsJ T) {j : ℕ} (hj : InR D j) {σ : T.Q.c.F →+* ℂ}
    (hσ : GoodEmb T.Q.c σ) {W : HSp D} (hV : T.V j σ = W) (hr : W.rank = D.R.r) :
    (∀ k, ModelW W hr ((T.U j σ).X k)) ∧
    (∀ h, (castDict hV (T.dict j σ) h).2 ∈ ((T.U j σ).X (castDict hV (T.dict j σ) h).1).dom) ∧
    (∀ h, IsUnitFr ((T.U j σ).X (castDict hV (T.dict j σ) h).1) (castDict hV (T.dict j σ) h).2) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw j).mult τ))
      (F : ReciprocityTheory.ChartRestriction.G.Geo.Tor.FamilyUnif (T.Q.Xo j) (σ.comp (IntermediateField.inclusion T.Q.c.le).toRingHom)
        (fun i => relab T.Q.c σ (e i).1))
      (ik : (T.U j σ).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((T.U j σ).X k).Λ)
      (th : ∀ k, ((T.U j σ).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧
        DictLat (T.U j σ) W hr (castDict hV (T.dict j σ))
          (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota j) e F ik φ th (T.x₀ j σ) := by
  subst hV
  obtain ⟨_, hm⟩ := L.modelW j hj σ hσ
  obtain ⟨_, _, -, hd⟩ := L.dictU j hj σ hσ
  obtain ⟨_, g, e, F, ik, φ, th, -, -, h1, h2⟩ := L.adPin j hj σ hσ
  exact ⟨hm, hd.2.2.2.1, (L.muUnit j hj σ hσ).2.2.2, g, e, F, ik, φ, th, h1, h2⟩

theorem exists_type_equiv {D : D7} (Q : Par D) (hp : Q.PinHost) (Ψ : Finset (D.host.E →+* ℂ))
    (hΨ : ∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ τ (Q.H.rt : D.host.E) = Q.H.rt0) :
    ∃ eT : D.what₂.Tau ≃ Ψ, ∀ ρ, (eT ρ).1 = tauE D ρ := by
  refine ⟨Equiv.ofBijective (fun ρ => ⟨tauE D ρ, (hΨ _).2 (hp.2.2.2 ρ)⟩) ⟨fun a b h => ?_, fun τ => ?_⟩, fun _ => rfl⟩
  · exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 (congrArg Subtype.val h)))
  · obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi Q hp τ.1 ((hΨ _).1 τ.2)
    exact ⟨t, Subtype.ext ht.symm⟩

end GlobalTheory.OneMapRef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotMeasureEqSmul
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ReadingNorm

theorem weylDimU_eq {p : ℕ} (lam a : Fin p → ℤ) (h : ∀ i j, lam i - lam j = a i - a j) :
    ((weylDimU lam : ℚ) : ℝ) = Formalism.L2.Geo.weylDim a := by
  unfold weylDimU Formalism.L2.Geo.weylDim
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun j _ => ?_
  have : ((lam i : ℝ) - lam j) = a i - a j := by exact_mod_cast h i j
  rw [this]

theorem sq_eq_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x : H) :
    ((‖x‖ ^ 2 : ℝ) : ℂ) = inner ℂ x x := by
  rw [Complex.ofReal_pow, inner_self_eq_norm_sq_to_K]
  rfl

variable {D : D7}

theorem lab_emb (ρ : D.what₂.Tau) : lab D.what₂.embLL ρ = ρ := by
  have hE : ∀ τ, labE D.what₂.embLL τ = tauE D τ := fun τ => by
    ext x
    exact DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)
  have h : ∃ τ, labE D.what₂.embLL τ = tauE D ρ ∨ labE D.what₂.embLL τ = (starRingEnd ℂ).comp (tauE D ρ) :=
    ⟨ρ, Or.inl (hE ρ)⟩
  unfold lab
  rw [dif_pos h]
  have hs := h.choose_spec
  generalize h.choose = τ at hs
  rw [hE] at hs
  rcases hs with hs | hs
  · have h1 : D.host.sigmaOf (D.eTau τ).1 = D.host.sigmaOf (D.eTau ρ).1 := by
      exact AlgEquiv.ext fun x => D.host.φ₀.injective (DFunLike.congr_fun hs x)
    apply D.eTau.injective
    apply Subtype.ext
    exact (by unfold Host.sigmaOf at h1; exact (EquivLike.injective _) h1)
  · exfalso
    have a := xi_zero_im_pos D τ
    have b := xi_zero_im_pos D ρ
    rw [hs] at a
    simp at a
    linarith

theorem dimK_eq (hK : DV.KapDef D) (i : Fin D.R.m) (τ : D.what₂.Tau) (s : ℕ × ℕ) (hs : s = D.R.sigW ((i : ℕ) + 1)) :
    ((dimK s.1 s.2 (Formalism.L2.NTheta.kapW (D.hc τ) s.1 s.2) : ℚ) : ℝ) =
      Formalism.L2.Geo.weylDim (D.what₂.kaBig ((i : ℕ) + 1) τ) * Formalism.L2.Geo.weylDim (D.what₂.kaSmall ((i : ℕ) + 1) τ) := by
  subst hs
  have hi := i.2
  have hk := D.R.m_add_three_le_k
  have hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := by
    simp only [Ranks.sigW]; omega
  have hq : i + 1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m := by
    simp only [Ranks.sigW]; omega
  have hodd : Odd ((D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2) := by
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by omega⟩
  obtain ⟨h1, h2⟩ := hK _ (inR i).1 (inR i).2 τ
  have hc := Formalism.L2.NTheta.kapW_cast (D.hc τ) _ _ hodd
  unfold dimK
  rw [Rat.cast_mul, weylDimU_eq _ (D.what₂.kaBig ((i : ℕ) + 1) τ), weylDimU_eq _ (D.what₂.kaSmall ((i : ℕ) + 1) τ)]
  · intro a b
    have e : ∀ c : Fin (D.R.sigW ((i : ℕ) + 1)).2, DV.aMinusQ D ((i : ℕ) + 1) τ c =
        -Formalism.L2.NTheta.lamAt (D.hc τ) ((D.R.sigW ((i : ℕ) + 1)).1 + c) - DV.eQ D ((i : ℕ) + 1) τ -
          ((D.R.t : ℚ) + 1 + 2 * (c : ℕ)) / 2 := fun c => by
      have := c.2
      unfold DV.aMinusQ Formalism.L2.NTheta.lamAt
      rw [dif_pos (by omega), dif_neg (by omega), dif_pos (by omega), neg_neg]
      congr 4
      omega
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_sub, Int.cast_sub, hc, hc, h2, h2, e, e]
    simp only [Formalism.L2.NTheta.kapQ, Sum.elim_inr]
    ring
  · intro a b
    have e : ∀ n, DV.sigPar D τ n = Formalism.L2.NTheta.lamAt (D.hc τ) n := fun n => by
      unfold DV.sigPar Formalism.L2.NTheta.lamAt
      rfl
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_sub, Int.cast_sub, hc, hc, h1, h1, DV.aPlusQ_eq, DV.aPlusQ_eq, e, e]
    simp only [Formalism.L2.NTheta.kapQ, Sum.elim_inl]
    ring

theorem prod_dimK (hK : DV.KapDef D) (i : Fin D.R.m) :
    (∏ ρ, ((dimK _ _ (kapAt (Wc D i) D.what₂.embLL ρ) : ℚ) : ℂ)) = (Formalism.L2.Geo.dimKap D ((i : ℕ) + 1) : ℝ) := by
  unfold Formalism.L2.Geo.dimKap
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [← dimK_eq hK i ρ _ (D.sp.W_sigval _ (inR i).1 (inR i).2 (tauE D ρ)), Complex.ofReal_ratCast, kapAt, lab_emb]

theorem quotMeasure_eq_smul (V : HSp D) (hs : V.SigOK) {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) : GlobalTheory.AutomorphicL2Unitary.autMeasure V ν = ν 𝓕 • muQ1 V := by
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D V hs
  have hp := GlobalTheory.AutomorphicL2Unitary.isVolPair_volPair hP
  have := hp.1.1
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  have e := Measure.isMulLeftInvariant_eq_smul ν (volPair V).1
  set c := Measure.haarScalarFactor ν (volPair V).1
  have e1 : GlobalTheory.AutomorphicL2Unitary.autMeasure V ν = (c : ENNReal) • muQ V := by
    rw [GlobalTheory.AutomorphicL2Unitary.muQ_eq hP, ← GlobalTheory.AutomorphicL2Unitary.quotMeasure_smul]
    exact congrArg _ e
  have e2 : ν 𝓕 = c * muQ V Set.univ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕]
    exact congrArg (fun m : Measure (AutQ V) => m Set.univ) e1
  rw [e1, e2, muQ1, if_pos (show _ ∧ _ from hV), smul_smul, mul_assoc, ENNReal.mul_inv_cancel hV.1 hV.2, mul_one]

theorem integral_star_mul (V : HSp D) (hs : V.SigOK) {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (φ : GA D V → ℂ) (hφ : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g)
    (ψ : AutQ V → ℂ) (hψ : MemLp ψ 2 (muQ1 V)) (c : ℝ) (h : ∀ q, ‖φ q.out‖ = c * ‖ψ q‖) :
    ∫ g in 𝓕, star (φ g) * φ g ∂ν = (((ν 𝓕).toReal * (c * ‖hψ.toLp ψ‖) ^ 2 : ℝ) : ℂ) := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ := hφ
  have e1 := GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕
    (fun q => star (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) φ q) * GlobalTheory.AutomorphicL2Unitary.descend (GQ V) φ q)
  simp only [hL.descend_mk] at e1
  have e2 : ((‖hψ.toLp ψ‖ ^ 2 : ℝ) : ℂ) = ∫ q, ((‖ψ q‖ ^ 2 : ℝ) : ℂ) ∂muQ1 V := by
    rw [sq_eq_inner, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hψ.coeFn_toLp] with q hq
    rw [hq, sq_eq_inner]
  rw [← e1, show GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) ν = _ from quotMeasure_eq_smul V hs hν h𝓕, integral_smul_measure, mul_pow,
    Complex.ofReal_mul, Complex.ofReal_mul, e2, ← integral_const_mul, Complex.real_smul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  show star (φ q.out) * φ q.out = ((c ^ 2 : ℝ) : ℂ) * ((‖ψ q‖ ^ 2 : ℝ) : ℂ)
  rw [← Complex.ofReal_mul, ← mul_pow, ← h, Complex.ofReal_pow]
  exact Complex.conj_mul' _

theorem norm_phiJ (T : CoreJ D) (hL : LawsJ T) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j)
    {σ : T.Q.c.F →+* ℂ} (hg : GoodEmb T.Q.c σ) (f : T.cuspA j (wtA w) w.n) :
    ∀ g, ‖T.phiJ j σ (wtA w) (f : T.R j) g‖ = lieFac (T.Q.Dw j) (xiR D) (wtA w) *
      ‖adel (T.V j σ) (T.dict j σ) (T.mu j σ) (rdU (T.U j σ) f) g‖ := by
  intro g
  rw [CoreJ.phiJ_apply, norm_mul, hL.cUnit j hj σ hg, one_mul, Core.phiAd, Pi.smul_apply, norm_smul,
    Complex.norm_real, Real.norm_of_nonneg (lieFac_pos _ _ _).le]

theorem jFn_apply (T : CoreJ D) {j : ℕ} (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ) (f : T.cuspA j (wtA w) w.n) :
    ∀ q : AutQ (T.V j σ), jFn (T.V j σ) σ (rdC (T.U j) σ (wtA w) w.n) (T.dict j σ) (T.mu j σ) f q =
      adel (T.V j σ) (T.dict j σ) (T.mu j σ) (rdU (T.U j σ) f) q.out := by
  intro q
  rfl

theorem integral_phiC (T : CoreJ D) (hL : LawsJ T) (h : LawsCore T.toCore) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j)
    {σ σ' : T.Q.c.F →+* ℂ} (hσ : σ = goodOf T.Q.c σ') {W : HSp D} (hV : T.V j σ = W) (hs : W.SigOK)
    {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν)
    (f : T.cuspA j (wtA w) w.n) (hφ : ∀ γ ∈ GQ W, ∀ g, phiC T hV (wtA w) (f : T.R j) (γ * g) = phiC T hV (wtA w) (f : T.R j) g) :
    ∫ g in 𝓕, star (phiC T hV (wtA w) (f : T.R j) g) * phiC T hV (wtA w) (f : T.R j) g ∂ν =
      (((ν 𝓕).toReal * h.Nl j w σ' (f : T.R j) ^ 2 : ℝ) : ℂ) := by
  have hg : GoodEmb T.Q.c σ := hσ ▸ goodEmb_goodOf _ σ'
  have hm := h.cuspidalL2Subspace j hj σ hg _ _ (dom_wtA w)
  have e : h.Nl j w σ' (f : T.R j) = lieFac (T.Q.Dw j) (xiR D) (wtA w) * ‖(hm f).toLp _‖ := by
    subst hσ
    rw [LawsCore.Nl, dif_pos hj, l2C, dif_pos f.2]
    rfl
  rw [e]
  clear e hσ
  subst hV
  have e2 : phiC T rfl (wtA w) (f : T.R j) = T.phiJ j σ (wtA w) (f : T.R j) := rfl
  rw [e2] at hφ ⊢
  exact integral_star_mul (T.V j σ) hs hν h𝓕 _ hφ _ (hm f) _ fun q =>
    (norm_phiJ T hL hj w hg f q.out).trans (congrArg (_ * ‖·‖) (jFn_apply T w σ f q).symm)

theorem normSq_eq {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}
    (H : HMod (MMap M)) {N : ℂ} (h : ∀ x y, inner ℂ x y = N * ipM M μ 𝓕 (H.e x) (H.e y)) (v : M.Vec)
    (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (x : H.H) :
    ((‖x‖ ^ 2 : ℝ) : ℂ) = N * ∫ g in 𝓕, star (H.e x v g) * H.e x v g ∂μ := by
  by_cases hx : x = 0
  · subst hx
    simp
  have h1 : ∃ c, IsMultIP M μ 𝓕 (H.e x) (H.e x) c := by
    by_contra hc
    apply inner_self_ne_zero (𝕜 := ℂ).2 hx
    rw [h, ipM, dif_neg hc, mul_zero]
  rw [(ipM_spec _ _ _ _ _ h1 v v).2, sq_eq_inner, h]
  simp [inner_self_eq_norm_sq_to_K, hv]

theorem norm_jTop : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (h : LawsCore T.toCore), DV.KapDef D → PreChar R → TieIn T R κ v₀ → JEvExists T R κ v₀ → ∀ (i : Fin D.R.m) (f : Cu T κ i), ‖jTop T R κ v₀ i (sg0 D A) f‖ = Real.sqrt ((R.νW i (R.fdW i)).toReal * Formalism.L2.Geo.dimKap D ((i : ℕ) + 1)) * h.Nl ((i : ℕ) + 1) (κ i) T.σ₀ (f : T.R ((i : ℕ) + 1)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ h hK hR ht hj i f
  have hpin : T.Q.PinField := ht.laws.pins.2.2.1
  have e0 : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hg := base_embedding_good T R ht.alg hpin
  have hV := ht.laws.spaceW _ (inR i) _ hg
  have hσ : res T (sg0 D A) = goodOf T.Q.c T.σ₀ := by
    rw [goodOf, if_pos T.good_σ₀, e0, res_embLL T ht.alg hpin]
  have hev := jTop_good T R κ v₀ hg hV (hj i _ hg hV) f
  obtain ⟨-, hr, hip⟩ := hR.models.HW i (sg0 D A)
  have hm : (R.HW i (sg0 D A)).e (jTop T R κ v₀ i (sg0 D A) f) ∈ R.Wall i (sg0 D A) := hr ▸ ⟨_, rfl⟩
  have ha := ((GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hm).aut (v₀ i (sg0 D A))
  have h1 := normSq_eq (R.HW i (sg0 D A)) hip (v₀ i _) (ht.hv₀ i _).norm (jTop T R κ v₀ i (sg0 D A) f)
  unfold evAt at hev
  rw [hev] at ha h1
  rw [integral_phiC T ht.laws h (inR i) (κ i) hσ hV (D.sp.W_sig _) (hR.models.νW i).1.1 (hR.models.νW i).2 f ha.left,
    show (∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ)) = _ from e0 ▸ prod_dimK hK i, ← Complex.ofReal_mul,
    Complex.ofReal_inj] at h1
  have hN := (h.hNl _ (inR i) (κ i) T.σ₀).nonneg _ f.2
  rw [← Real.sqrt_sq hN, ← Real.sqrt_mul' _ (sq_nonneg _), ← Real.sqrt_sq (norm_nonneg (jTop T R κ v₀ i (sg0 D A) f)), h1]
  congr 1
  ring

end GlobalTheory.ReadingNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularOfValuationBoundedAtPoints
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.RegCrit

theorem isUnit_eval_iff {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (t : Sp R ⟶ X) {W : X.Opens}
    (h : ⊤ ≤ t ⁻¹ᵁ W) (g : Γ(X, W)) :
    IsUnit ((t.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom g) ↔
      t (IsLocalRing.closedPoint R) ∈ X.basicOpen g := by
  have hU : t (IsLocalRing.closedPoint R) ∈ W := h trivial
  have e : X.presheaf.germ W _ hU ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of R) t =
      t.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  rw [← e, X.mem_basicOpen g _ hU]
  exact isUnit_map_iff (Scheme.stalkClosedPointTo (R := CommRingCat.of R) t).hom _

theorem isUnit_of_one_le {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (c : e.O)
    (hc : 1 ≤ e.w c) : IsUnit c := by
  have h0 : (c : AlgebraicClosure F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact absurd hc (by norm_num)
  have h1 : (c : AlgebraicClosure F)⁻¹ ∈ e.O := by
    rw [e.mem_O, map_inv₀]
    exact inv_le_one_of_one_le₀ hc
  exact IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ h0))

theorem regAt_of_integral_values : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (N : TrueGeo.Model Y), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.X → haveI := N.ar.isIntegral; ∀ (U : N.X.Opens) (f : N.X.functionField), (∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ N.X), spMap e.O.subtype ≫ yt = y.1 ≫ N.j → ⊤ ≤ yt ⁻¹ᵁ U → e.w (valAt (y.1 ≫ N.j) f) ≤ 1) → ∀ x ∈ U, RegAt x f := by
  intro F _ _ Y N hN
  haveI := N.ar.isIntegral
  intro U f hf x hx
  have : IsProper N.p := by
    obtain ⟨n, c, hc, h⟩ := N.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  have : IsLocallyNoetherian N.X := LocallyOfFiniteType.isLocallyNoetherian N.p
  by_contra hreg
  obtain ⟨z, hz, hzero⟩ := GlobalTheory.T.exists_zero_of_inv_of_not_regular_normal N.X hN x f hreg
  have hf0 : f ≠ 0 := fun h => hreg (h ▸ regAt_zero x)
  have hzU : z ∈ U := hz.mem_open U.isOpen hx
  obtain ⟨W₀, hzW, g₀, hg₀⟩ := hzero.regAt.exists_fnOf
  have hzW' : z ∈ W₀ ⊓ U := ⟨hzW, hzU⟩
  obtain ⟨g, hg⟩ : ∃ g : Γ(N.X, W₀ ⊓ U), ∀ h, fnOf _ h g = f⁻¹ :=
    ⟨resG N.X inf_le_left g₀, fun h => (fnOf_resG _ h _).trans hg₀⟩
  have hg0 : g ≠ 0 := fun h => inv_ne_zero hf0 (by rw [← hg (gen_mem hzW'), h, map_zero])
  have hzg : z ∉ N.X.basicOpen g := fun h =>
    (zeroAt_iff.1 hzero).2 (hg (gen_mem hzW') ▸ (unitAt_fnOf_iff hzW' _ g).2 h)
  obtain ⟨v, e, y, yt, hc, hW, hn, hu⟩ := GlobalTheory.T.exists_ext_point_specializing_outside_basicOpen F Y N _ z g hzW' hg0 hzg
  have hle := hf v e y yt hc fun p hp => (hW hp).2
  have hu' : below (y.1 ≫ N.j) ∈ N.X.basicOpen g := hu
  have hb : below (y.1 ≫ N.j) ∈ W₀ ⊓ U := N.X.basicOpen_le g hu'
  have ht : ⊤ ≤ (y.1 ≫ N.j) ⁻¹ᵁ (W₀ ⊓ U) := fun p _ => by
    change (y.1 ≫ N.j) p ∈ W₀ ⊓ U
    rw [← hc]
    exact hW (x := spMap e.O.subtype p) trivial
  have hunit : UnitAt (below (y.1 ≫ N.j)) f⁻¹ := hg (gen_mem hb) ▸ (unitAt_fnOf_iff hb _ g).2 hu'
  have hfu : UnitAt (below (y.1 ≫ N.j)) f := inv_inv f ▸ hunit.inv
  have hmul := OfModel.valAt_mul (y.1 ≫ N.j) hfu.regAt hunit.regAt
  have hone : valAt (y.1 ≫ N.j) (1 : N.X.functionField) = 1 := by
    have := OfModel.valAt_algebraMap (y.1 ≫ N.j) 1
    rwa [map_one, map_one] at this
  have hev := OfModel.eval_pull e.O.subtype (𝟙 N.X) (y.1 ≫ N.j) yt (hc.trans (Category.comp_id _).symm)
    (U := W₀ ⊓ U) (W := W₀ ⊓ U) le_rfl ht hW g
  have hid : ((𝟙 N.X : N.X ⟶ N.X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl).hom g = g := by
    have : (𝟙 N.X : N.X ⟶ N.X).appLE (W₀ ⊓ U) (W₀ ⊓ U) le_rfl = 𝟙 _ :=
      (Category.id_comp _).trans (N.X.presheaf.map_id _)
    rw [this]
    rfl
  rw [hid] at hev
  rw [mul_inv_cancel₀ hf0, hone, ← hg (gen_mem hb), OfModel.valAt_fnOf _ hb ht, hev] at hmul
  refine hn ((isUnit_eval_iff yt hW g).1 (isUnit_of_one_le e _ ?_))
  have h₁ := congrArg e.w hmul
  rw [map_one, map_mul] at h₁
  exact h₁.le.trans (mul_le_of_le_one_left (e.w.nonneg _) hle)

end GlobalTheory.TrueGeo.RegCrit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SatakeParametersInertPlaceIndependentOfModelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satakeParameters_inertPlace_independent_of_model : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n), π.Iso π' → ∀ v w, NG.OverPl w v → ∀ (Dv Dv' : InertDatum L n v w) α, NG.SatAt π Dv α → NG.SatAt π' Dv' α := by
  first | exact @GlobalTheory.SatInd.satAt_indep | exact GlobalTheory.SatInd.satAt_indep | (intros; apply GlobalTheory.SatInd.satAt_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurLemmaEquivariantPairBoundedFunctionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schurLemma_equivariant_pair_boundedFunctions_alt : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (act : Formalism.REAL.UJ ε → X → X), Continuous (Function.uncurry act) → ∀ (a a' : H →ₗ[ℂ] (X → ℂ)), (∀ w ∈ smSub G (trRep σ P), Continuous (a w) ∧ (∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a (σ (umat g) w) x = a w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a)) → (∀ w ∈ smSub G (trRep σ P), Continuous (a' w) ∧ (∃ C : ℝ, ∀ x, ‖a' w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a' (σ (umat g) w) x = a' w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a')) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a (σ g u) x) * a (σ g w) x ∂ν = ∫ x, star (a u x) * a w x ∂ν) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a' (σ g u) x) * a' (σ g w) x ∂ν = ∫ x, star (a' u x) * a' w x ∂ν) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a (σ g u) x) * a' (σ g w) x ∂ν = ∫ x, star (a u x) * a' w x ∂ν) → ∃ c : ℂ, ∀ w ∈ smSub G (trRep σ P), ∀ w' ∈ smSub G (trRep σ P), ∫ x, star (a w x) * a' w' x ∂ν = c * ⟪w, w'⟫_ℂ := by
  first | exact @GlobalTheory.SmVec.schurLemma_equivariant_pair_boundedFunctions | exact GlobalTheory.SmVec.schurLemma_equivariant_pair_boundedFunctions | (intros; apply GlobalTheory.SmVec.schurLemma_equivariant_pair_boundedFunctions <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurLemmaThetaFunctionsFromMatrixCoefficientsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_lemma_thetaFunctions_from_matrixCoefficients : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : Module.End ℂ (WO S T → ℂ)), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (M f)) → (∀ w f, IsThetaFunO ψ S T f → M (heisO ψ S T w f) = heisO ψ S T w (M f)) → (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, IsThetaFunO ψ S T f → M f = c • f := by
  first | exact @GlobalTheory.Mem.Lift.schur_theta | exact GlobalTheory.Mem.Lift.schur_theta | (intros; apply GlobalTheory.Mem.Lift.schur_theta <;> assumption)
end

