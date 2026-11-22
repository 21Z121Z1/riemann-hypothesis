import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0771
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0800
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0795
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0119
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0654
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0667
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0751
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0803
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2977
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0760
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateBlockUpperOfEigenfunctionUnipotentType
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0736
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0766
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0796
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0733
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0779
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0524
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RSideA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicReadingDefiniteFormsGivenCoefficient
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0797
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleFormEqMulPointClassValue
section
noncomputable section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.GrassTop

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def S (H : Host E) (Dw : Datum H) : Submodule ℝ (MvPolynomial ((E →+* ℂ) × ℕ) ℝ) where
  carrier := {P | ∃ β : ℝ, ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ, GlobalTheory.Schubert.admitted H Dw Θ →
    Θ P = β * Θ (GlobalTheory.LieBase.pointPoly H Dw)}
  zero_mem' := ⟨0, fun Θ _ => by simp⟩
  add_mem' := by
    rintro a b ⟨β, hβ⟩ ⟨β', hβ'⟩
    exact ⟨β + β', fun Θ h => by rw [map_add, hβ Θ h, hβ' Θ h]; ring⟩
  smul_mem' := by
    rintro c a ⟨β, hβ⟩
    exact ⟨c * β, fun Θ h => by rw [map_smul, hβ Θ h, smul_eq_mul]; ring⟩

theorem prod_update {H : Host E} (g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ) (σ : GlobalTheory.AllWt.Psi H)
    (h : MvPolynomial (Bool × ℕ) ℝ) :
    ∏ τ, ren τ (Function.update g σ h τ) = ren σ h * ∏ τ ∈ Finset.univ.erase σ, ren τ (g τ) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun τ hτ => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ)]

theorem prod_ren_mem (H : Host E) (Dw : Datum H) (s : Finset (GlobalTheory.AllWt.Psi H)) :
    ∀ g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ, (∀ τ ∉ s, g τ ∈ basis Dw.p Dw.q) →
      ∏ τ, ren τ (g τ) ∈ S H Dw := by
  induction s using Finset.induction_on with
  | empty =>
    intro g hg
    exact ⟨_, GlobalTheory.T.admissibleChernForm_prod_grassmannianBasisCopies E H Dw g fun τ => hg τ (Finset.notMem_empty τ)⟩
  | insert σ s hσ ih =>
    intro g hg
    have key : ∀ h ∈ (J Dw.p Dw.q).restrictScalars ℝ ⊔ Submodule.span ℝ (basis Dw.p Dw.q),
        ren σ h * ∏ τ ∈ Finset.univ.erase σ, ren τ (g τ) ∈ S H Dw := by
      intro h hh
      obtain ⟨j, hj, b, hb, rfl⟩ := Submodule.mem_sup.1 hh
      rw [map_add, add_mul]
      refine add_mem ⟨0, fun Θ hΘ => ?_⟩ ?_
      · rw [zero_mul, mul_comm]
        exact GlobalTheory.T.adm_apply_mul_ren_eq_zero_of_mem_J E H Dw Θ hΘ σ j hj _
      · clear hh
        induction hb using Submodule.span_induction with
        | mem b hb =>
          rw [← prod_update]
          refine ih _ fun τ hτ => ?_
          by_cases e : τ = σ
          · subst e; rw [Function.update_self]; exact hb
          · rw [Function.update_of_ne e]; exact hg τ (by simp [e, hτ])
        | zero => simp
        | add x y _ _ hx hy => rw [map_add, add_mul]; exact add_mem hx hy
        | smul c x _ hx => rw [map_smul, smul_mul_assoc]; exact Submodule.smul_mem _ c hx
    have := key (g σ) (GlobalTheory.T.mem_grassmannianRelationIdeal_sup_monomialSpan _ _ _)
    rwa [← prod_update, Function.update_eq_self] at this

theorem var_eq {H : Host E} (x : (E →+* ℂ) × ℕ) : ∃ σ : GlobalTheory.AllWt.Psi H, ∃ y, x = renVar σ y := by
  by_cases h : x.1 (H.rt : E) = H.rt0
  · exact ⟨⟨x.1, h⟩, (true, x.2), by simp [renVar]⟩
  · refine ⟨⟨conjEmb x.1, GlobalTheory.AllWt.conj_mem h⟩, (false, x.2), ?_⟩
    simp [renVar, GlobalTheory.AllWt.conjEmb_conjEmb]

theorem mul_prod_ren_mem (H : Host E) (Dw : Datum H) (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) :
    ∀ g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ, P * ∏ τ, ren τ (g τ) ∈ S H Dw := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro g
    rw [C_mul']
    exact Submodule.smul_mem _ a (prod_ren_mem H Dw Finset.univ g (by simp))
  | add a b ha hb => intro g; rw [add_mul]; exact add_mem (ha g) (hb g)
  | mul_X P x ih =>
    intro g
    obtain ⟨σ, y, rfl⟩ := var_eq (H := H) x
    have e : X (renVar σ y) * ∏ τ, ren τ (g τ) = ∏ τ, ren τ (Function.update g σ (X y * g σ) τ) := by
      rw [prod_update, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ σ), map_mul, ren, rename_X]
      ring
    rw [mul_assoc, e]
    exact ih _

end GlobalTheory.GrassTop

theorem GlobalTheory.GrassTop.span_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), ∃ β : ℝ, ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ,
      GlobalTheory.Schubert.admitted H Dw Θ → Θ P = β * Θ (GlobalTheory.LieBase.pointPoly H Dw) := by
  intro E _ _ _ H Dw P
  have := GlobalTheory.GrassTop.mul_prod_ren_mem H Dw P (fun _ => 1)
  simp only [map_one, Finset.prod_const_one, mul_one] at this
  exact this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryFormNonlocalDvr
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitQuot

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), IsCN R → P.TorsionIso →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ ϖ : V, Irreducible ϖ →
    ∀ ψ : R →+* V, Function.Injective ψ → ¬ IsLocalHom ψ →
    ∀ be ∈ levelForms H 1 P.D.toPre.X, FormAt P.D.toPre ψ ϖ be →
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V'),
      CDvr V' ∧ Function.Injective f ∧ IsLocalHom f ∧ Irreducible (f ϖ) ∧
      ∃ (t' : SAB H (Sp V')) (_ : SABMap t' t (spMap (f.comp ψ))) (P' : PELUnif (maximalIdeal V') t')
        (be' : LinearMap.BilinForm ℤ P'.D.toPre.X) (ρ : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X),
        be' ∈ levelForms H 1 P'.D.toPre.X ∧ Function.Surjective ρ ∧ (∀ a b, be' (ρ a) (ρ b) = be a b) ∧
        IsMonomial P'.D.toPre ![f ϖ] ![be'] := by
  intro E _ _ _ H R _ _ _ t P hR hT V _ _ _ hV ϖ hϖ ψ hψ hnl be hbe hF
  obtain ⟨PP', cub, sym, adj, prim, mV, -⟩ := sabPull CubePf.cubePull (spMap ψ) t
  have j : Function.Injective ((algebraMap V (FractionRing V)).comp ψ) := (IsFractionRing.injective V _).comp hψ
  let gK : FractionRing R →+* FractionRing V := IsFractionRing.lift j
  have e : spMap gK ≫ jK R = jK V ≫ spMap ψ :=
    (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).symm
  have hp := GlobalTheory.DatUniq.polAt_pull mV (GlobalTheory.DatUniq.polAt_of_unif P) (jK V) (spMap gK) e
  obtain ⟨V', _, _, _, f, hV', hf, hfl, hfϖ, t', m', ⟨P'⟩⟩ := GlobalTheory.T.exists_unramified_uniformisation_polarisedTriple E H V hV ϖ hϖ _ hp
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ mV m'
  have hsp : spMap f ≫ spMap ψ = spMap (f.comp ψ) := GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl
  have n' : SABMap t' t (spMap (f.comp ψ)) := hsp ▸ n
  obtain ⟨ρ, hρs, hρ⟩ := GlobalTheory.T.boundary_form_base_change_dvr E H R t P hR hT V' hV' (f.comp ψ) (hf.comp hψ)
    (fun hl => hnl ⟨fun a ha => hl.map_nonunit a (ha.map f)⟩) t' n' P'
  obtain ⟨hd, hc, hz⟩ := hV'
  obtain ⟨be', hbe', hmon, -⟩ := exists_periodForm P' hfϖ
  refine ⟨V', inferInstance, inferInstance, inferInstance, f, ⟨hd, hc, hz⟩, hf, hfl, hfϖ, t', n', P', be', ρ, hbe',
    hρs, ?_, hmon⟩
  have hdiag : ∀ y, be' (ρ y) (ρ y) = be y y := by
    intro y
    obtain ⟨r, k, hr, hk, ha⟩ := hF y
    obtain ⟨u, m, hm, hc⟩ := hmon (ρ y)
    have h1 := hρ y r _ hr hc
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, RingHom.comp_apply] at h1
    have h2 : Associated ((f ϖ) ^ k) ((f ϖ) ^ (m 0)) := by
      have h3 : Associated (f (ψ r)) ((f ϖ) ^ k) := by
        rw [← map_pow]; exact ha.map f
      exact h3.symm.trans (h1.trans (associated_unit_mul_left _ _ u.isUnit))
    have h4 := BalancedTrait.pow_eq_of_associated hfϖ h2
    have h5 := hm 0
    simp only [Matrix.cons_val_zero] at h5
    rw [h5, hk, h4]
  intro a b
  have s1 := BalancedTrait.two_mul_apply be (mem_levelForms.1 hbe).1 a b
  have s2 := BalancedTrait.two_mul_apply be' (mem_levelForms.1 hbe').1 (ρ a) (ρ b)
  rw [← map_add, hdiag, hdiag, hdiag] at s2
  omega

end GlobalTheory.TraitQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedDomainModelMetricContDiffAtAndIsUnit
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx
open scoped Matrix

namespace GlobalTheory.ModelMetricReg

open scoped ComplexOrder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_det {m : Type*} [Fintype m] [DecidableEq m] {k : WithTop ℕ∞}
    {F : E → Matrix m m ℂ} (hF : ∀ a b, ContDiff ℝ k (fun x => F x a b)) :
    ContDiff ℝ k (fun x => (F x).det) := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum (fun σ _ => ?_)
  exact contDiff_const.mul (contDiff_prod (fun i _ => hF _ _))

theorem contDiff_adjugate_apply {m : Type*} [Fintype m] [DecidableEq m] {k : WithTop ℕ∞}
    {F : E → Matrix m m ℂ} (hF : ∀ a b, ContDiff ℝ k (fun x => F x a b)) (i j : m) :
    ContDiff ℝ k (fun x => (F x).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  refine contDiff_det (fun a b => ?_)
  by_cases hab : a = j
  · subst hab; simp only [Matrix.updateRow_self]; exact contDiff_const
  · simp only [Matrix.updateRow_ne hab]; exact hF a b

theorem det_one_sub_mul_conjTranspose_ne_zero {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ)
    (hz : (1 - zᴴ * z).PosDef) : (1 - z * zᴴ).det ≠ 0 := by
  rw [Matrix.det_one_sub_mul_comm]
  exact hz.det_pos.ne'

end GlobalTheory.ModelMetricReg

namespace GlobalTheory.ModelMetricReg

open scoped ComplexOrder

theorem contDiff_hP_entry (ι : Type) [Fintype ι] (p q n : ℕ)
    (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι) (a b : Fin p) :
    ContDiff ℝ 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => hP (unflat (GlobalTheory.UnifDens.flatL h w) τ) a b) := by
  have hz : ∀ c : ι × Fin p × Fin q,
      ContDiff ℝ 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => GlobalTheory.UnifDens.flatL h w c) := by
    intro c
    have hL : ContDiff ℝ 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => GlobalTheory.UnifDens.flatL h w) :=
      ((GlobalTheory.UnifDens.flatL h).contDiff).restrict_scalars ℝ
    exact (contDiff_apply ℝ ℂ c).comp hL
  simp only [hP, Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, unflat,
    Matrix.of_apply]
  refine contDiff_const.sub (ContDiff.sum (fun k _ => ?_))
  have hs : ContDiff ℝ 2 (fun w : ReciprocityTheory.L2DbarEstimates.V n => star (GlobalTheory.UnifDens.flatL h w (τ, b, k))) := by
    have := (Complex.conjCLE.contDiff (n := 2)).comp (hz (τ, b, k))
    convert this using 2
    simp [Function.comp, Complex.conjCLE_apply, Complex.star_def]
  exact (hz (τ, a, k)).mul hs

theorem invT_contDiffAt_and_isUnit : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.UnifDens.flatL h v ∈ DomFlat ι p q → ∀ τ : ι, MContDiffAt 2 (fun w => ((hP (unflat (GlobalTheory.UnifDens.flatL h w) τ))⁻¹)ᵀ) v ∧ IsUnit (((hP (unflat (GlobalTheory.UnifDens.flatL h v) τ))⁻¹)ᵀ).det := by
  intro ι _ p q n h v hv τ
  have hpos : (1 - (unflat (GlobalTheory.UnifDens.flatL h v) τ)ᴴ * unflat (GlobalTheory.UnifDens.flatL h v) τ).PosDef :=
    hv τ
  have hne : (hP (unflat (GlobalTheory.UnifDens.flatL h v) τ)).det ≠ 0 :=
    det_one_sub_mul_conjTranspose_ne_zero _ hpos
  refine ⟨fun a b => ?_, ?_⟩
  · have hE := contDiff_hP_entry ι p q n h τ
    have hdet := contDiff_det (F := fun w : ReciprocityTheory.L2DbarEstimates.V n => hP (unflat (GlobalTheory.UnifDens.flatL h w) τ)) hE
    have hadj := contDiff_adjugate_apply (F := fun w : ReciprocityTheory.L2DbarEstimates.V n => hP (unflat (GlobalTheory.UnifDens.flatL h w) τ)) hE b a
    simp only [Matrix.transpose_apply, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
      Ring.inverse_eq_inv']
    exact (hdet.contDiffAt.inv hne).mul hadj.contDiffAt
  · rw [Matrix.det_transpose, Matrix.det_nonsing_inv]
    rw [Ring.inverse_eq_inv']
    exact (inv_ne_zero hne).isUnit

end GlobalTheory.ModelMetricReg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellWeightOfAdmissibleTwistStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_weight_of_admissible_twist : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → CellWt (D := Dof x) (mtAt (D := Dof x) l.mt.M v j) l.b.Bs.exp b hA j e := by
  first | exact @GlobalTheory.LevCmp.cellWt_all | exact GlobalTheory.LevCmp.cellWt_all | (intros; apply GlobalTheory.LevCmp.cellWt_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernDensityFrameIndepChartJacobianFactor
section
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped Matrix
open scoped ComplexOrder

namespace GlobalTheory.GoodMetric

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ} {E : Fr (ratOf X) m 0}
  {O : X.X.Opens} {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ}

theorem IsMetricOn.mContDiffAt_chart (hM : IsMetricOn E O H) {y : CxPts X.str σ} (hy : y ∈ ptsIn X.str σ O)
    (c : AlgChart X.str σ X.dim) (hc : y ∈ c.e.source) {A : Mat m X.Fn} (hA : A ∈ E.S (under y)) (τ : ι) :
    MContDiffAt 2 (fun u => H A (c.e.symm u) τ) (c.e y) := by
  intro a b
  have hy'' : c.e.symm (c.e y) = y := c.e.left_inv hc
  have hsm := hM.smooth y hy A hA
  have hre := GlobalTheory.ChernWeilLine.cInfAt_eventually (hsm τ a b).1
  have him := GlobalTheory.ChernWeilLine.cInfAt_eventually (hsm τ a b).2
  have hn : ∀ {f : CxPts X.str σ → ℝ}, (∀ᶠ z in 𝓝 y, CInfAt f z) → ContDiffAt ℝ 2 (f ∘ c.e.symm) (c.e y) := by
    intro f hf
    have hs : c.e.target ∩ c.e.symm ⁻¹' {z | CInfAt f z} ∈ 𝓝 (c.e y) := by
      refine Filter.inter_mem (c.e.open_target.mem_nhds (c.e.map_source hc)) ?_
      exact (c.e.continuousAt_symm (c.e.map_source hc)).preimage_mem_nhds (hy''.symm ▸ hf)
    exact ((contDiffOn_chart (fun z hz => hz) c).contDiffAt hs).of_le (by norm_cast)
  have h1 := (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hn hre)).add
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hn him)).mul (contDiffAt_const (c := Complex.I)))
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  simp only [Function.comp_apply, Complex.ofRealCLM_apply]
  exact (Complex.re_add_im _).symm

theorem IsMetricOn.isUnit_det_chart (hM : IsMetricOn E O H) {y : CxPts X.str σ} (hy : y ∈ ptsIn X.str σ O)
    (c : AlgChart X.str σ X.dim) (hc : y ∈ c.e.source) {A : Mat m X.Fn} (hA : A ∈ E.S (under y)) (τ : ι) :
    IsUnit (H A (c.e.symm (c.e y)) τ).det := by
  rw [c.e.left_inv hc]
  exact (Matrix.isUnit_iff_isUnit_det _).1 (hM.posDef y hy A hA τ).isUnit

theorem IsMetricOn.chernTop_frame [Finite ι] (hM : IsMetricOn E O H) (R : MvPolynomial (ι × ℕ) ℝ) {y : CxPts X.str σ}
    (hy : y ∈ ptsIn X.str σ O) (c : AlgChart X.str σ X.dim) (hc : y ∈ c.e.source) {A A' : Mat m X.Fn}
    (hA : A ∈ E.S (under y)) (hA' : A' ∈ E.S (under y)) :
    chernTop R (fun v => H A (c.e.symm v)) (c.e y) = chernTop R (fun v => H A' (c.e.symm v)) (c.e y) := by
  have hP : Par 0 ((ratOf X).O (under y)).toSubring (A * A'⁻¹) := (Fr.mem_iff hA').1 hA
  refine GlobalTheory.PointChern.chernTop_changeFrame R _ _ (fun w => (A * A'⁻¹).map (ratVal · (c.e.symm w))) (fun _ => 1) _
    (fun _ => one_pos) (fun τ i j => GlobalTheory.FrameLift.analyticAt_ratVal c hc (mem_O_ratOf.1 ((hP τ).1 i j)))
    (fun τ => ?_) (hM.mContDiffAt_chart hy c hc hA') (hM.isUnit_det_chart hy c hc hA') ?_
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
    simp only [c.e.left_inv hc]
    exact ((hP.map_of (ratVal · y) ψ hψ).det_ne τ).isUnit
  · have hO : ∀ᶠ z in 𝓝 y, z ∈ ptsIn X.str σ O := (isOpen_ptsIn O).mem_nhds hy
    filter_upwards [(c.e.tendsto_symm hc).eventually
      (hO.and ((GlobalTheory.FrameLift.eventually_mem hA).and (GlobalTheory.FrameLift.eventually_mem hA')))] with w hw τ
    rw [Complex.ofReal_one, one_smul]
    exact hM.trans _ hw.1 A' hw.2.2 A hw.2.1 τ

theorem IsMetricOn.chernTop_chart (hM : IsMetricOn E O H) (R : MvPolynomial (ι × ℕ) ℝ) {y : CxPts X.str σ}
    (hy : y ∈ ptsIn X.str σ O) (c c' : AlgChart X.str σ X.dim) (hc : y ∈ c.e.source) (hc' : y ∈ c'.e.source)
    {A : Mat m X.Fn} (hA : A ∈ E.S (under y)) :
    chernTop R (fun v => H A (c.e.symm v)) (c.e y) =
      ‖transDet c.e c'.e y‖ ^ 2 * chernTop R (fun v => H A (c'.e.symm v)) (c'.e y) := by
  let K : V X.dim → Mat m ℂ := fun v => H A (c'.e.symm v)
  have ho := isOpen_over c.e c'.e.open_source
  have hm := mem_over c.e hc hc'
  have hφ : AnalyticAt ℂ (c'.e ∘ c.e.symm) (c.e y) :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (c.holo_trans c') (ho.mem_nhds hm)
  have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hc)
  have hK2 : ∀ τ, MContDiffAt 2 (fun u => K u τ) (c'.e y) := hM.mContDiffAt_chart hy c' hc' hA
  have hKu : ∀ τ, IsUnit (K (c'.e y) τ).det := hM.isUnit_det_chart hy c' hc' hA
  have key := GlobalTheory.ChernPull.chernTop_comp R K (c'.e ∘ c.e.symm) (c.e y) hφ (e₂ ▸ hK2) (e₂ ▸ hKu)
  have hg : (fun v => H A (c.e.symm v)) =ᶠ[𝓝 (c.e y)] fun w => K ((c'.e ∘ c.e.symm) w) := by
    filter_upwards [ho.mem_nhds hm] with w hw
    simp only [K, Function.comp_apply, c'.e.left_inv hw.2]
  rw [GlobalTheory.ChernWeilLine.chernTop_congr R hg, key, e₂, transDet, Complex.sq_norm]

end GlobalTheory.GoodMetric

theorem GlobalTheory.GoodMetric.chernTop_frame_chart_trans : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} [Finite ι] {m : ι → ℕ} (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricOn E O H → ∀ (R : MvPolynomial (ι × ℕ) ℝ) {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → ∀ (c c' : AlgChart X.str σ X.dim), y ∈ c.e.source → y ∈ c'.e.source → ∀ {A A' : Mat m X.Fn}, A ∈ E.S (under y) → A' ∈ E.S (under y) → chernTop R (fun v => H A (c.e.symm v)) (c.e y) = ‖transDet c.e c'.e y‖ ^ 2 * chernTop R (fun v => H A' (c'.e.symm v)) (c'.e y) := by
  intro F _ σ X ι _ m E O H hM R y hy c c' hc hc' A A' hA hA'
  rw [hM.chernTop_frame R hy c hc hA hA', hM.chernTop_chart R hy c c' hc hc' hA']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityBoundedDomainInvariantStatement
section
open Formalism.DegreeFormula

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPolyTopDensity_bounded_domain_invariant : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (v : ReciprocityTheory.L2DbarEstimates.V n), GlobalTheory.UnifDens.flatL h v ∈ Formalism.DegreeFormula.DomFlat ι p q → GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) v = GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 * ∏ i, ((Formalism.DegreeFormula.hQ (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h v) i)).det.re) ^ (-((p + q : ℕ) : ℤ)) := by
  first | exact @GlobalTheory.DomDensInv.chernTop_model_moeb | exact GlobalTheory.DomDensInv.chernTop_model_moeb | (intros; apply GlobalTheory.DomDensInv.chernTop_model_moeb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateBlockUpperOfEigenfunctionUnipotentTypeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_blockUpper_of_eigenfunction_unipotentType : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {n r t : ℕ}, n = r + t → 2 ≤ r →
    ∀ (s : ReciprocityTheory.Aut.SplitPlace E) {k : Type} [Field k] (φ : GlobalTheory.CenFrame.Os s →+* k), GlobalTheory.CenFrame.IsResidue s φ →
    (∃ c : k, c ≠ 0 ∧ c ≠ 1) → ∀ (f : Formalism.AUTREP.GAf E n → ℂ), f ≠ 0 →
    ∀ (J : Subgroup (Formalism.AUTREP.GAf E n)) (χ : J →* ℂˣ)
    (ψ₀ : AddChar (s.v.adicCompletion (NumberField.maximalRealSubfield E)) ℂ)
    (ξ : (s.v.adicCompletion (NumberField.maximalRealSubfield E))ˣ →* ℂˣ),
    Formalism.L2.NG.IsPsi0 s ψ₀ → Formalism.L2.NG.LevelUni J χ s r ψ₀ ξ →
    (∀ κ (h : κ ∈ J) g, f (g * κ) = ((χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) →
    ∀ (b : GL (Fin n) k),
    (∀ κ ∈ ReciprocityTheory.Aut.Umax E n, ReciprocityTheory.Aut.TrivOutside {s.v} κ → ∀ y : GL (Fin n) (GlobalTheory.CenFrame.Os s),
        GlobalTheory.CenFrame.IsCompOf s κ y →
      ((∀ i j : Fin n, (r ≤ i.val → j.val < r → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < r → j.val < i.val → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < r → i = j → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 1)) →
        ∃ c : ℂ, ∀ g, f (g * κ) = c * f g) ∧
      (Matrix.GeneralLinearGroup.map φ y = 1 → ∀ g, f (g * κ) = f g)) →
    b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  first | exact @GlobalTheory.CenFrameGen.block_upper_of_eigen | exact GlobalTheory.CenFrameGen.block_upper_of_eigen | (intros; apply GlobalTheory.CenFrameGen.block_upper_of_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.E0ReadThirdLocalOfCoeffStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.e0_read_third_local_of_coeff : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → GlobalTheory.NRows.HypothesesX → AllSt fun _ _ _ T w P x => ∀ (l : LC hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), GlobalTheory.CoefDuty.Built l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → ∀ (hC : m.z.R.C = cfL L (cfOf x)) (Xd : DivX (withLoc L)) (E : EigIdx (withLoc L) Xd) (labPi : E.Pi → (famR (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) m.z.Xg m.z.tr).A.fam.base.Ix) hb htup hg hf, GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector (GlobalTheory.HeightCounting.Up.RealOfReading.realOfRead m.z.R.toRealDat m.z.F.lv2 r.Y (tpL L l.c.tp) hC Xd E labPi hb htup hg hf) := by
  first | exact @GlobalTheory.HeightCounting.Up.ThirdTied.e0_read_third_local | exact GlobalTheory.HeightCounting.Up.ThirdTied.e0_read_third_local | (intros; apply GlobalTheory.HeightCounting.Up.ThirdTied.e0_read_third_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseCoefficientSpacesIsometricMapsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enlargedBase_coefficientSpaces_isometric_maps : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std → ∃ (cV' : ∀ i', CoefA (Vc (w'.st Z').toD7 i')) (c0L' : ∀ i' : Fin (w'.st Z').toD7.R.m, VV (w'.st Z').toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc (w'.st Z').toD7 i').rank ((i' : ℕ) + 1) τ) →ₛₗ[(w'.st Z').toD7.what₂.embLL] (cV' i').W),
    (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → HEq (cV' i').W (z.R.cV i).W ∧ HEq (cV' i').ρ (z.R.cV i).ρ ∧ HEq (cV' i').nW (z.R.cV i).nW ∧ HEq (cV' i').iW (z.R.cV i).iW) ∧ (∀ i', (cV' i').Is) ∧
    (∀ i', Bridge.CoefMapTie (Vc (w'.st Z').toD7 i') (cV' i').coef (c0L' i') (rhoVr (labLL (w'.st Z').toD7) _)) ∧
    (∀ i' x y, inner ℂ (c0L' i' x) (c0L' i' y) = (w'.st Z').toD7.what₂.embLL (pairVr (labLL (w'.st Z').toD7) _
      (if (w'.st Z').toD7.sp.Vneg ((i' : ℕ) + 1) then -(Vc (w'.st Z').toD7 i').gram else (Vc (w'.st Z').toD7 i').gram) x y)) ∧
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ (ok : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).Ok) (φ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).EqFun)
      (h : Bridge.Gf (Vc (w.st Z).toD7 i)) (v' : VV (w'.st Z').toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc (w'.st Z').toD7 i').rank ((i' : ℕ) + 1) τ)),
      HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (φ.1 (LiftBrg.ptL (w.st Z) w.I (usedOf w.I T Wt) i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) 1 1 h)).1) →
      HEq (c0L' i' v') (z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok φ :))) h) := by
  first | exact @GlobalTheory.Mem.RsCoef.rs_coef | exact GlobalTheory.Mem.RsCoef.rs_coef | (intros; apply GlobalTheory.Mem.RsCoef.rs_coef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicReadingDefiniteFormsGivenCoefficientStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicReading_definiteForms_given_coefficients : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → (∀ i, L.βV i = 1) → Seed.FrmC.StdLat X.toD7.sp.X' → (∀ i, Seed.FrmC.StdLat (Vc X.toD7 i)) → ∀ θ : InfFam X.toD7, IsInfFam θ → ∀ MX : DSModel X.toD7.sp.X' (parB (Ptw X.toD7) X.toD7.R.m), ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (c0L : ∀ i : Fin X.toD7.R.m, VV X.toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[X.toD7.what₂.embLL] (cV i).W), (∀ i, (cV i).Is) → (∀ i, Bridge.CoefMapTie (Vc X.toD7 i) (cV i).coef (c0L i) (rhoVr (labLL X.toD7) _)) → (∀ i x y, inner ℂ (c0L i x) (c0L i y) = X.toD7.what₂.embLL (pairVr (labLL X.toD7) _ (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) x y)) → ∃ (cX : CoefA X.toD7.sp.X') (pl : PlS X.B px → Pl X.toD7.host.E) (Sb : Finset (Pl X.toD7.host.E)) (Bd : Seed.BType (famR X I hX U Xg tr) L cX cV pl) (plI : PlI X.B px → Pl X.toD7.host.E) (SF : Finset (HeightOneSpectrum (𝓞 X.toD7.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ), cX.Is ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧ Seed.BrgL (famR X I hX U Xg tr) L eG cX cV pl Sb Bd plI SF ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => Bd.jR t φ) ∧ (∀ i, BrgStdV X I hX U Xg tr L i (cV i) fun t φ => Bd.jL i t φ) ∧ ∀ i : Fin X.toD7.R.m, ∀ (t : TupU I U) (φ : (Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) (h : Bridge.Gf (Vc X.toD7 i)) v', HEq v' (φ.1 (LiftBrg.ptL X I U i t 1 1 h)) → Bd.jL i t ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1)) φ :))) h = c0L i v' := by
  first | exact @GlobalTheory.Mem.R3.BrgAt.exists_brgL_at | exact GlobalTheory.Mem.R3.BrgAt.exists_brgL_at | (intros; apply GlobalTheory.Mem.R3.BrgAt.exists_brgL_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticFlagDomainFrameLiftAlgebraicChartStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_flagDomain_frame_lift_algebraicChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (k' : U.Comp) (s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)), AnalyticAt ℂ s (c'.e y) ∧ ∀ᶠ w in 𝓝 (c'.e y), ∃ hs : s w ∈ (U.X k').dom, cxPt T.Z (U.un k' ⟨s w, hs⟩) = cxOf e σ hj (c'.e.symm w) := by
  first | exact @GlobalTheory.LieBase.exists_analytic_frame_lift | exact GlobalTheory.LieBase.exists_analytic_frame_lift | (intros; apply GlobalTheory.LieBase.exists_analytic_frame_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exponential_chart_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb c σ → 1 ≤ Dw.p + Dw.q → ∀ x₀ : CxPts (genStr T.Z) σ, ∃ (n g r a : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ), x₀ ∈ e.source ∧ e x₀ = 0 ∧ IsLogChart a e ex lam ρ := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.exists_isLogChart | exact GlobalTheory.ShFam.Hor.LogCh.exists_isLogChart | (intros; apply GlobalTheory.ShFam.Hor.LogCh.exists_isLogChart <;> assumption)
end

