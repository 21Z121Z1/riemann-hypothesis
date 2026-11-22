import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0319
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0317
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0318
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvariantFormBoundedCongruence
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0012
import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0320
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1988
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0662
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0287
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0641
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetRepresentativesCongrAtTwistPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocQCoset

open GlobalTheory.TopInv

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ}

theorem core (q : E) (hq : q ≠ 0) (hqi : IntAt P q) (M Dd : ℕ) (hD : 2 * M ≤ Dd) (y0 V₀ V₁ : Sp E n) (g k : Sp E n →ₗ[E] Sp E n)
    (hgI : ∀ x : Sp E n, (∀ l, IntAt P (x l)) → ∀ l, IntAt P (g x l))
    (hkI : ∀ x : Sp E n, (∀ l, IntAt P (x l)) → ∀ l, IntAt P (k x l))
    (hkD : ∀ w : Sp E n, (∀ l, IntAt P (w l)) → ∀ l, IntAt P ((q ^ Dd)⁻¹ * (k w - w) l))
    (hgy : ∀ l, IntAt P ((q ^ M)⁻¹ * (g y0 - y0) l)) (hy0 : ∀ l, IntAt P (q ^ M * y0 l))
    (h0 : ∀ l, IntAt P ((q ^ M)⁻¹ * (V₀ - y0) l)) (h1 : ∀ l, IntAt P ((q ^ M)⁻¹ * (V₁ - y0) l)) :
    ∀ l, IntAt P ((q ^ M)⁻¹ * (g (k V₁) - V₀) l) := by
  have hqpow : ∀ m : ℕ, IntAt P (q ^ m) := fun m => mem_intS.1 ((intS P).pow_mem (mem_intS.2 hqi) m)
  obtain ⟨s, hs⟩ : ∃ s, Dd = 2 * M + s := ⟨Dd - 2 * M, by omega⟩

  have hA : ∀ l, IntAt P ((q ^ M)⁻¹ * (k y0 - y0) l) := by
    intro l
    have h := hkD ((q ^ M) • y0) (fun l => by simpa [smul_eq_mul] using hy0 l) l
    have e : (q ^ M)⁻¹ * (k y0 - y0) l = q ^ s * ((q ^ Dd)⁻¹ * (k ((q ^ M) • y0) - (q ^ M) • y0) l) := by
      simp only [map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hs, pow_add, pow_mul]
      field_simp
      ring
    rw [e]
    exact mem_intS.1 ((intS P).mul_mem (mem_intS.2 (hqpow s)) (mem_intS.2 h))

  have hB : ∀ l, IntAt P ((q ^ M)⁻¹ * (k V₁ - k y0) l) := by
    intro l
    have h := hkI ((q ^ M)⁻¹ • (V₁ - y0)) (fun l => by simpa [smul_eq_mul] using h1 l) l
    rwa [map_smul, map_sub, Pi.smul_apply, smul_eq_mul] at h
  have hC : ∀ l, IntAt P ((q ^ M)⁻¹ * (k V₁ - y0) l) := by
    intro l
    have e : (q ^ M)⁻¹ * (k V₁ - y0) l = (q ^ M)⁻¹ * (k V₁ - k y0) l + (q ^ M)⁻¹ * (k y0 - y0) l := by
      simp only [Pi.sub_apply]; ring
    rw [e]; exact (hB l).add (hA l)
  have hE : ∀ l, IntAt P ((q ^ M)⁻¹ * (g (k V₁) - g y0) l) := by
    intro l
    have h := hgI ((q ^ M)⁻¹ • (k V₁ - y0)) (fun l => by simpa [smul_eq_mul] using hC l) l
    rwa [map_smul, map_sub, Pi.smul_apply, smul_eq_mul] at h
  intro l
  have e : (q ^ M)⁻¹ * (g (k V₁) - V₀) l =
      (q ^ M)⁻¹ * (g (k V₁) - g y0) l + (q ^ M)⁻¹ * (g y0 - y0) l + (-1 : E) * ((q ^ M)⁻¹ * (V₀ - y0) l) := by
    simp only [Pi.sub_apply]; ring
  rw [e]
  exact mem_intS.1 ((intS P).add_mem ((intS P).add_mem (mem_intS.2 (hE l)) (mem_intS.2 (hgy l)))
    ((intS P).mul_mem ((intS P).neg_mem (intS P).one_mem) (mem_intS.2 (h0 l))))

end GlobalTheory.LocQCoset

namespace GlobalTheory.LocQCoset

open GlobalTheory.TopInv

theorem coset_agree : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ), P.1 ∉ t.Pr.vGs →
  ∀ (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1)) (g k : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1))),
    g ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    SameCoset t.sel (t.tup μ) (t.cst μ) P (g (y0At A (t.m2 + 1) hi β P)) (y0At A (t.m2 + 1) hi β P) →
    k ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    (∀ w ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (k w - w) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) →
    (∀ w, frsF t.sel (t.tup μ) p₁ P w = frsF t.sel (t.tup μ) p P (g (k w))) →
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ • ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p))) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie hi β P hPG p p₁ g k hg hgy hk hkD hF
  have hok := t.idx_ok μ
  have hq := qOf_ne (E := t.X.E) P.1
  have hqi : IntAt P.1 ((qOf P.1 : ℕ) : t.X.E) := intAt_nat (P := P.1) _
  have memS : ∀ x : Sp t.X.E (D.R.N (t.m2 + 1)), x ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ↔ ∀ l, IntAt P.1 (x l) :=
    fun x => mem_localization_standardLattice P.1 x
  have rep : ∀ p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1),
      SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p' P).symm (repY (cosetOf A (t.m2 + 1) hi β p')))
        (y0At A (t.m2 + 1) hi β P) := by
    intro p'
    obtain ⟨r, hr⟩ := GlobalTheory.T.exists_vector_prescribed_cosets_badPrimes_frames t.sel (t.tup μ) (t.cst μ) (frsF t.sel (t.tup μ) p') (fun P => y0At A (t.m2 + 1) hi β P)
    have hrep : repY (cosetOf A (t.m2 + 1) hi β p') ∈ cosetOf A (t.m2 + 1) hi β p' :=
      Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) hi β p') ⟨r, hr⟩
    exact hrep P
  have unf : ∀ y y' : Sp t.X.E (D.R.N (t.m2 + 1)), SameCoset t.sel (t.tup μ) (t.cst μ) P y y' →
      ∀ l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ (t.cst μ).M)⁻¹ * (y - y') l) := by
    intro y y' h
    unfold SameCoset at h
    simpa only [if_neg hPG] using h
  have bnd : ∀ y : Sp t.X.E (D.R.N (t.m2 + 1)), SameCoset t.sel (t.tup μ) (t.cst μ) P y (y0At A (t.m2 + 1) hi β P) →
      ∀ l, IntAt P.1 (((qOf P.1 : ℕ) : t.X.E) ^ (t.cst μ).M * y l) :=
    fun y h => (GlobalTheory.T.chartBaseCoset_bounded_typePrimes_and_twist A dtU a hP hTie hi β P y h).2 hPG
  refine ⟨(memS _).2 fun l => ?_, (memS _).2 fun l => ?_, (memS _).2 fun l => ?_⟩
  · simpa only [Pi.smul_apply, smul_eq_mul] using bnd _ (rep p) l
  · simpa only [Pi.smul_apply, smul_eq_mul] using bnd _ (rep p₁) l
  · have hW : (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) =
        g (k ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)))) := by
      apply (frsF t.sel (t.tup μ) p P).injective
      rw [LinearEquiv.apply_symm_apply, ← hF, LinearEquiv.apply_symm_apply]
    have hgI : ∀ x : Sp t.X.E (D.R.N (t.m2 + 1)), (∀ l, IntAt P.1 (x l)) → ∀ l, IntAt P.1 (g.toLinearMap x l) :=
      fun x hx => (memS _).1 ((hg x).2 ((memS x).2 hx))
    have hkI : ∀ x : Sp t.X.E (D.R.N (t.m2 + 1)), (∀ l, IntAt P.1 (x l)) → ∀ l, IntAt P.1 (k.toLinearMap x l) :=
      fun x hx => (memS _).1 ((hk x).2 ((memS x).2 hx))
    have hkD' : ∀ w : Sp t.X.E (D.R.N (t.m2 + 1)), (∀ l, IntAt P.1 (w l)) →
        ∀ l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ (t.cst μ).D P)⁻¹ * (k.toLinearMap w - w) l) := by
      intro w hw l
      simpa only [Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe] using (memS _).1 (hkD w ((memS w).2 hw)) l
    have hrefl : SameCoset t.sel (t.tup μ) (t.cst μ) P (y0At A (t.m2 + 1) hi β P) (y0At A (t.m2 + 1) hi β P) := by
      unfold SameCoset
      intro l
      rw [sub_self, Pi.zero_apply, mul_zero]
      simpa using intAt_nat (E := t.X.E) (P := P.1) 0
    have hy0 := bnd _ hrefl
    have := core _ hq hqi (t.cst μ).M ((t.cst μ).D P) (hok.depthQ P hPG) (y0At A (t.m2 + 1) hi β P) _ _
      g.toLinearMap k.toLinearMap hgI hkI hkD' (unf _ _ hgy) hy0 (unf _ _ (rep p)) (unf _ _ (rep p₁)) l
    rw [hW]
    simpa only [Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe] using this

end GlobalTheory.LocQCoset

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformizerBlockEqDiagonalPowMulIntegralGLStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagUniformizerBlock_eq_diagonal_pow_mul_integralGL : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n k : ℕ)
    (ϖ π : v.adicCompletion F), Valued.v ϖ = WithZero.exp (-1 : ℤ) → Valued.v π = WithZero.exp (-1 : ℤ) →
    ∃ T ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), Formalism.UG.diagJ n ϖ k =
      Matrix.diagonal (fun i : Fin n => π ^ ((List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0).getD i.1 0)) *
        (T : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  first | exact @GlobalTheory.DiagUnifFactor.main | exact GlobalTheory.DiagUnifFactor.main | (intros; apply GlobalTheory.DiagUnifFactor.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DoubleCosetSupportAtSplitStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_coset_support_at_split : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc) (Q Q' : D.naut.AV i) (sp : SplitPlace D.host.E), (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ Ds : Set (GAf D.host.E D.R.nV), (∀ x ∈ Ds, TrivOutside {sp.v} x) → (∀ x ∈ Ds, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) → {c : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J | ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c}.Finite → (∀ σ σ', IsLocS (P.H.av.S i Q) sp σ → IsLocS (P.H.av.S i Q') sp σ' → GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls σ') → ∀ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F ≠ 0 → ∀ F' ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q'), F' ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F' ≠ 0 → ∀ c c' : ℂ, NG.heckeD (P.M.loc i).J Ds F = c • F → NG.heckeD (P.M.loc i).J Ds F' = c' • F' → c = c' := by
  first | exact @GlobalTheory.LocEigAgree.main | exact GlobalTheory.LocEigAgree.main | (intros; apply GlobalTheory.LocEigAgree.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralSectionSplitPlaceComponentMapStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralSection_splitPlace_componentMap : ∀ (D : D7) (sp : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E),
    ∃ sec : sp.v.adicCompletion (maximalRealSubfield D.host.E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (∀ t, sp.proj (GlobalTheory.NJoin.tensCast hF (sec t)) = t) ∧
      (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E), sec t ∈ Formalism.L2.Theta.intAE D) ∧
      (∀ x ∈ Formalism.L2.Theta.intAE D,
        sp.proj (GlobalTheory.NJoin.tensCast hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) ∧
      ∀ x : D.host.E, sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D x))) = sp.i x := by
  first | exact @GlobalTheory.SplitComp.proj_tensCast_section | exact GlobalTheory.SplitComp.proj_tensCast_section | (intros; apply GlobalTheory.SplitComp.proj_tensCast_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRealSubfieldUniformizerAtSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realSubfield_uniformizer_at_splitPlace : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L),
    ∃ y : 𝓞 L, y ∈ s.w.asIdeal ∧ y ∉ s.w.asIdeal ^ 2 ∧ Formalism.AUTREP.IsUnif L s.v (s.i (y : L)) := by
  first | exact @GlobalTheory.realUnif_split | exact GlobalTheory.realUnif_split | (intros; apply GlobalTheory.realUnif_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvariantFormBoundedCongruenceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_form_bounded_congruence : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp), GlobalTheory.NJoin.Agree X P.M P.rep → ∀ i, ∃ (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* ℂˣ) (T : Finset (GAf D.host.E D.R.nV)) (β : (P.M.loc i).wt.W →ₗ⋆[ℂ] (P.M.loc i).wt.W →ₗ[ℂ] ℂ) (c : ℝ), GlobalTheory.CoefDuty.IsInvForm (P.M.loc i).wt β ∧ GlobalTheory.CoefDuty.IsBounded J ∧ (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) ∧ GlobalTheory.CoefDuty.IsClassReps J T ∧ 0 < c ∧ (∀ x, (P.M.loc i).real x ∈ NG.TypeSp (P.M.loc i).wt.ρ J χ) ∧ ∀ x y, inner ℂ x y = (c : ℂ) * GlobalTheory.CoefDuty.classSum (P.M.loc i).wt β J T ((P.M.loc i).real x) ((P.M.loc i).real y) := by
  first | exact @GlobalTheory.VFormCls.main | exact GlobalTheory.VFormCls.main | (intros; apply GlobalTheory.VFormCls.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumConditionsAtStandardKernelComparisonStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelDatumConditions_at_standardKernelComparison : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ (D : D7) (O : Obj D) (t : KerEntTied O.ex), StdTie D O t → 3 ≤ D.host.splitBound → 5 ≤ O.K.dl1 → 4 ≤ O.K.dl2 → (∀ Ee : OrbitPlaces.Ent D, OrbitPlaces.Shape D O.L O.Gx Ee ∧ ∀ u, ∀ j < D.R.m, ∀ s ∈ D.host.TT, Ee.row u j (false, s) 0 - Ee.row u j (false, s) 1 ≤ 2 * O.L.sc.a) → GlobalTheory.Pdv.At O.ex t.ent := by
  first | exact @GlobalTheory.PdvTie.at_of_stdTie | exact GlobalTheory.PdvTie.at_of_stdTie | (intros; apply GlobalTheory.PdvTie.at_of_stdTie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumEquivariantRationalUnitaryStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepDatum_equivariant_rationalUnitary : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m), t.m2 < i → ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG t.X.E (D.R.N (i + 1)) t.Pr.vGs × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  first | exact @GlobalTheory.TopRat.xiPt_top_smul | exact GlobalTheory.TopRat.xiPt_top_smul | (intros; apply GlobalTheory.TopRat.xiPt_top_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumFixedCongruentFrameChangeTwistPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepDatum_fixed_congruentFrameChange_twistPrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) {m2 : ℕ}, R.m = m2 + 2 → cst.Ok → ∀ (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs →
  2 * cst.M ≤ cst.D P →
  ∀ (κ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1)))
    (κ' : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))),
  κ ∈ GLint X.E (R.N (m2 + 1)) P.1 →
  (∀ w ∈ stdAt X.E (R.N (m2 + 1)) P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E (R.N (m2 + 1)) P.1) →
  κ' ∈ GLint X.E (R.N (m2 + 1 + 1)) P.1 →
  (∀ w ∈ stdAt X.E (R.N (m2 + 1 + 1)) P.1, ((qOf P.1 : X.E) ^ (2 * cst.M))⁻¹ • (κ' w - w) ∈ stdAt X.E (R.N (m2 + 1 + 1)) P.1) →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y'' : Sp X.E (R.N (m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y'' l)) →
  topDat Ch sel mu cst (m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat Ch sel mu cst (m2 + 1) P y y'' := by
  first | exact @GlobalTheory.TopFrameQM.topDat_frames_qM | exact GlobalTheory.TopFrameQM.topDat_frames_qM | (intros; apply GlobalTheory.TopFrameQM.topDat_frames_qM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalIsometryStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrimeFunctionals_move_rationalIsometry : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → ∀ (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal),
        IsOver v (seamP t.seam P.1) →
        FunMoved t.seam ((St i hi).K β).lev P v h (iotaOf A i hi β P v h) (ratA D.host.F (A.crd i hi) * x₁.1) ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1) := by
  first | exact @GlobalTheory.TwV.funMoved_ptAd_rat | exact GlobalTheory.TwV.funMoved_ptAd_rat | (intros; apply GlobalTheory.TwV.funMoved_ptAd_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LiftedCharactersAgreeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lifted_characters_agree : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (X.R.toLevCh.mu (X.tupT (D.nd.mu i))) X.R.eta (j.1 + 1)).1 (P.tp.tup (D.nd.mu i) j) ∧ Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (X.R.toLevCh.mu (X.tupT (D.nd.mu i))) X.R.eta (j.1 + 1)).2 (P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹) := by
  first | exact @GlobalTheory.WeilDatumChars.weil_chars | exact GlobalTheory.WeilDatumChars.weil_chars | (intros; apply GlobalTheory.WeilDatumChars.weil_chars <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentsOfSmoothCharacters
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SphUnr

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ms_eq_singleton {Δ : Segment k} (h1 : Δ.len = 1) : Δ.ms = {Δ.first} := by
  obtain ⟨z, hz⟩ := Multiset.card_eq_one.1 ((Segment.card_ms Δ).trans h1)
  have h3 : z = Δ.first := by
    have hm : z ∈ Δ.ms := by rw [hz]; exact Multiset.mem_singleton_self z
    obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hm)
    obtain rfl : a = 0 := by omega
    simp
  rw [hz, h3]

open scoped Classical in

noncomputable def valAt (ϖ : kˣ) (y : IrrGL k) : ℂˣ :=
  if h : ∃ (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ), y = IrrGL.ofChar μ hμ then h.choose ϖ else 1

end Local

section Sph

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

end Sph

section Glob

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

end Glob

end GlobalTheory.SphUnr

namespace GlobalTheory.SphUnr

end GlobalTheory.SphUnr
end
end

