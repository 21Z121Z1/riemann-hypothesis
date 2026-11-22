import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0633
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0465
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0744
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDictionaryCmFieldAutomorphic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0755
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0260
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupFiniteDimensionalRepContainsHighestW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0071
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0668
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0773
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0771
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0237
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointPairingUnfoldingDownwardLiftStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_pairing_unfolding_downward_lift : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (y : (R.HW i (sg0 D A)).H) (u : (R.HV i t).H), ∫ g in R.fdW i, star (val R i v y g) * R.thF i t u (fun ρ => v ρ) g ∂(R.νW i) = ∫ h in R.fdV i t, ⟪upVec R i t v b y h, R.extV i t u h⟫_ℂ ∂(R.νV i t) := by
  first | exact @GlobalTheory.AdjUnfold.integral_val_thF_eq | exact GlobalTheory.AdjUnfold.integral_val_thF_eq | (intros; apply GlobalTheory.AdjUnfold.integral_val_thF_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleJOfParams
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

namespace GlobalTheory.AdmJointAssembly

theorem main : ∀ (D : D7) (L : SizeData₂ D), SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → WeightParam D →
    BlockCharParam D → AdmissibleParameterJ.AdmPar L → AdmissibleParameterJ.AdmJ L := by
  intro D L h0 h1 h2 h5 hW hB hP
  have hG := GlobalTheory.T.admG2_pair_of_admissible D h0 h1 h2 h5
  exact ⟨hG.1, GlobalTheory.CrysWD.crysIffWD D, hG.2, GlobalTheory.T.admissible_dictionary_of_params GlobalTheory.Published.cheb_holds D h2 hW hB, GlobalTheory.T.hodgeTateJumpsReading_rowAdm D, hP⟩

end GlobalTheory.AdmJointAssembly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightAgreesUnderModularFormDictionary
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Matrix Topology Pointwise

noncomputable section

namespace GlobalTheory.WeightDict

theorem exists_pair_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB0 : B ≠ 0) (hB : ∀ γ x y, B (ρ γ x) (σ γ y) = B x y) {x : V} (hx : x ≠ 0)
    {y : W} (hy : y ≠ 0) : ∃ γ, B (ρ γ x) y ≠ 0 := by
  by_contra hc
  push Not at hc
  let K : Subrepresentation ρ :=
    { toSubmodule :=
        { carrier := {w | ∀ γ, B (ρ γ w) y = 0}
          add_mem' := fun {a b} ha hb γ => by rw [map_add, map_add, LinearMap.add_apply, ha γ, hb γ, add_zero]
          zero_mem' := fun γ => by simp
          smul_mem' := fun c a ha γ => by rw [map_smul, map_smul, LinearMap.smul_apply, ha γ, smul_zero] }
      apply_mem_toSubmodule := fun g w hw γ => by
        have := hw (γ * g)
        rwa [map_mul] at this }
  let K' : Subrepresentation σ :=
    { toSubmodule := LinearMap.ker B.flip
      apply_mem_toSubmodule := fun g z hz => by
        rw [LinearMap.mem_ker] at hz ⊢
        ext w
        have h1 := hB g (ρ g⁻¹ w) z
        rw [Representation.self_inv_apply] at h1
        exact h1.trans (LinearMap.congr_fun hz _) }
  rcases hρ.eq_bot_or_eq_top K with h | h
  · have h1 : K.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h
    have h2 : x ∈ K.toSubmodule := hc
    rw [h1] at h2
    exact hx h2
  · have h1 : K.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule h
    have hyK : y ∈ K'.toSubmodule := by
      change B.flip y = 0
      ext w
      have h2 : w ∈ K.toSubmodule := by rw [h1]; exact Submodule.mem_top
      have h3 : B (ρ 1 w) y = 0 := h2 1
      rw [map_one] at h3
      exact h3
    rcases hσ.eq_bot_or_eq_top K' with h' | h'
    · have h3 : K'.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h'
      rw [h3] at hyK
      exact hy hyK
    · have h3 : LinearMap.ker B.flip = ⊤ := congrArg Subrepresentation.toSubmodule h'
      refine hB0 (LinearMap.ext fun w => LinearMap.ext fun z => ?_)
      have h4 : z ∈ LinearMap.ker B.flip := by rw [h3]; exact Submodule.mem_top
      exact LinearMap.congr_fun (LinearMap.mem_ker.1 h4) w

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem coord_conjugate (τ : L →+* ℂ) (z : Cinf L) :
    coord (ComplexEmbedding.conjugate τ) z = starRingEnd ℂ (coord τ z) := by
  have hm : InfinitePlace.mk (ComplexEmbedding.conjugate τ) = InfinitePlace.mk τ := InfinitePlace.mk_conjugate_eq τ
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h)
  rw [GlobalTheory.EmbUnitary.coord_eq, GlobalTheory.EmbUnitary.coord_eq, hm]
  unfold GlobalTheory.EmbUnitary.twist
  rw [hm]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [if_pos h, if_neg (by rw [h]; exact hne.symm)]
    rfl
  · rw [if_pos h, if_neg (by rw [h]; exact hne)]
    simp

theorem polyMat_embU {ι : Type} (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (τ : L →+* ℂ)
    (x : embU n τ) : GlobalTheory.WeightRealExt.polyMat P (x : UA L n) = GlobalTheory.AlgWtHW.evM P (NG.evPt τ (cEmb τ (x : UA L n))) := by
  ext i j
  change MvPolynomial.eval _ _ = MvPolynomial.eval _ _
  congr 2
  funext p
  obtain ⟨σ, s, t⟩ := p
  change (cEmb σ (x : UA L n)).val s t = _
  unfold NG.evPt
  dsimp only
  split_ifs with h1 h2 h3
  · rw [h1]
  · rw [h2]
    have hu := Matrix.mem_unitaryGroup_iff.1 (GlobalTheory.EmbUnitary.cEmb_mem τ (x : UA L n))
    rw [Units.inv_eq_of_mul_eq_one_right hu]
    exact coord_conjugate τ _
  all_goals
    have hk : InfinitePlace.mk σ ≠ InfinitePlace.mk τ := fun h => by
      rcases InfinitePlace.mk_eq_iff.1 h with h | h
      · exact h1 h
      · exact h2 (by rw [← h]; ext z; simp)
    have h4 := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 x.2).2 σ) hk)
    rw [h4]
    simp [Matrix.one_apply, h3]

theorem pair_ext {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GQ L n) W} (a : NG.AlgWt L n)
    (R : UA L n →* Module.End ℂ W) (hfin : ∀ k ∈ finU L n, R k = 1)
    (hrat : ∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ →
      (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → R γ = ρ γQ)
    (hcont : ∀ (v : W) (μ : Module.Dual ℂ W), Continuous fun g : UA L n => μ (R g v))
    (B : W →ₗ[ℂ] a.W →ₗ[ℂ] ℂ) (hB : ∀ γ x y, B (ρ γ x) (a.ρ γ y) = B x y)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (hP : GlobalTheory.AlgWtHW.Agrees a b P)
    (w : W) (c : ι → ℂ) (g : UA L n) :
    B (R g⁻¹ w) (b.equivFun.symm c) = B w (b.equivFun.symm (GlobalTheory.WeightRealExt.polyMat P g *ᵥ c)) := by
  have h1 : Continuous fun g : UA L n => B (R g⁻¹ w) (b.equivFun.symm c) :=
    (hcont w (B.flip (b.equivFun.symm c))).comp continuous_inv
  have h2 : Continuous fun g : UA L n => B w (b.equivFun.symm (GlobalTheory.WeightRealExt.polyMat P g *ᵥ c)) :=
    (LinearMap.continuous_of_finiteDimensional (B w ∘ₗ b.equivFun.symm.toLinearMap)).comp
      ((GlobalTheory.WeightRealExt.continuous_polyMat P).matrix_mulVec continuous_const)
  refine congrFun (Continuous.ext_on GlobalTheory.WeightRealExt.dense_rat_fin h1 h2 fun z hz => ?_) g
  obtain ⟨γ, hγ, k, hk, rfl⟩ := Set.mem_mul.1 hz
  obtain ⟨γ₀, hγ₀⟩ := GlobalTheory.WeightRealExt.exists_unitaryRationalMatrix_of_mem_definiteUnitaryRational hγ
  have hR : R γ = ρ (GlobalTheory.WeightRealExt.ratPt γ₀) := hrat γ _ γ₀.1 hγ₀ rfl
  have hM : GlobalTheory.WeightRealExt.polyMat P (γ * k) = LinearMap.toMatrix b b (a.ρ (GlobalTheory.WeightRealExt.ratPt γ₀)) := by
    have hk' : cInf k = 1 := hk
    rw [GlobalTheory.WeightRealExt.polyMat_congr P (g := γ * k) (h := γ) (by rw [map_mul, hk', mul_one]),
      GlobalTheory.WeightRealExt.polyMat_rat P γ γ₀.1 hγ₀]
    exact (hP _ γ₀.1 rfl).symm
  have e1 : b.equivFun.symm (GlobalTheory.WeightRealExt.polyMat P (γ * k) *ᵥ c) =
      a.ρ (GlobalTheory.WeightRealExt.ratPt γ₀) (b.equivFun.symm c) := by
    rw [hM, LinearEquiv.symm_apply_eq]
    have := LinearMap.toMatrix_mulVec_repr b b (a.ρ (GlobalTheory.WeightRealExt.ratPt γ₀)) (b.equivFun.symm c)
    rw [← b.equivFun_apply, ← b.equivFun_apply, LinearEquiv.apply_symm_apply] at this
    exact this
  have e2 : ρ (GlobalTheory.WeightRealExt.ratPt γ₀) (R (γ * k)⁻¹ w) = w := by
    rw [_root_.mul_inv_rev, map_mul, hfin _ ((finU L n).inv_mem hk), one_mul, ← hR, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
  change B (R (γ * k)⁻¹ w) _ = B w _
  rw [e1, ← hB (GlobalTheory.WeightRealExt.ratPt γ₀), e2]

theorem phi_mem {F : FinIso L n} {π : NG.AutRep L n} {U : Submodule ℂ (UA L n → ℂ)} (hU : Dict F π U)
    (R : UA L n →* Module.End ℂ π.W) (hfin : ∀ k ∈ finU L n, R k = 1)
    (hrat : ∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ →
      (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → R γ = π.ρ γQ)
    (hcont : ∀ (v : π.W) (μ : Module.Dual ℂ π.W), Continuous fun g : UA L n => μ (R g v))
    {f : GAf L n → π.W} (hf : f ∈ π.S) (μ : Module.Dual ℂ π.W) : GlobalTheory.FormDictEx.phi F R f μ ∈ U := by
  haveI : FiniteDimensional ℂ π.W := π.alg.1
  have hmem : (fun x => μ (f x)) ∈ U.map (LinearMap.funLeft ℂ ℂ F.j) := by
    rw [hU.2]
    exact Submodule.subset_span ⟨f, hf, μ, rfl⟩
  obtain ⟨u, hu, hue⟩ := hmem
  have ha : GlobalTheory.FormDictEx.phi F R f μ ∈ GlobalTheory.DefU.autU L n :=
    GlobalTheory.FormDictEx.isAutFormU_phi F π.ρ R hfin hrat hcont (π.irrS.1.le hf) μ
  have hu' : u ∈ GlobalTheory.DefU.autU L n := hU.1.aut u hu
  have h0 := GlobalTheory.DefiniteDense.eq_zero_of_finU L n _ ((GlobalTheory.DefU.autU L n).sub_mem ha hu') fun y hy => by
    obtain ⟨x, rfl⟩ := F.onto y hy
    rw [Pi.sub_apply, GlobalTheory.FormDictEx.phi_j F R hfin, sub_eq_zero]
    exact (congrFun hue x).symm
  rw [sub_eq_zero.1 h0]
  exact hu

theorem weight_agree : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n)
    (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (a : NG.AlgWt L n), π.toAlgWt.IsDual a → ∀ τ : L →+* ℂ,
      ∃ lam, HasWeightAt U τ lam ∧ a.HWAt τ lam.w := by
  intro L _ _ _ n F π U hU a hdual τ
  obtain ⟨B, hB0, hB⟩ := hdual
  obtain ⟨R, hfin, hrat, hcont⟩ := GlobalTheory.WeightRealExt.exists_extension L n π.toAlgWt
  obtain ⟨_, ι, _, _, b, P, hP⟩ := a.alg
  obtain ⟨e, he⟩ := GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup L n τ
  have hΦ := GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP τ
  set Φ : GL (Fin n) ℂ → Matrix ι ι ℂ := fun A => GlobalTheory.AlgWtHW.evM P (NG.evPt τ A) with hΦd
  have hΦx : ∀ x : embU n τ, Φ (cEmb τ (x : UA L n)) = GlobalTheory.WeightRealExt.polyMat P (x : UA L n) := fun x =>
    (polyMat_embU P τ x).symm
  let σ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) (ι → ℂ) :=
    { toFun := fun u => Matrix.mulVecLin (Φ (GlobalTheory.Branching.unitaryIncl n u))
      map_one' := by
        rw [map_one, hΦ.one, Matrix.mulVecLin_one]
        rfl
      map_mul' := fun u u' => by
        rw [map_mul, hΦ.mul, Matrix.mulVecLin_mul]
        rfl }
  have hσc : ∀ (l : Module.Dual ℂ (ι → ℂ)) (v : ι → ℂ), Continuous fun u => l (σ u v) := by
    intro l v
    have h1 : ∀ u, σ u v = GlobalTheory.WeightRealExt.polyMat P (e.symm u : UA L n) *ᵥ v := fun u => by
      rw [← hΦx, ← he, e.apply_symm_apply]
      rfl
    simp only [h1]
    exact (LinearMap.continuous_of_finiteDimensional l).comp
      (((GlobalTheory.WeightRealExt.continuous_polyMat P).comp (continuous_subtype_val.comp e.symm.continuous)).matrix_mulVec
        continuous_const)
  haveI : Nontrivial a.W := by
    by_contra hs
    rw [not_nontrivial_iff_subsingleton] at hs
    exact hB0 (LinearMap.ext fun w => LinearMap.ext fun z => by rw [Subsingleton.elim z 0, map_zero, map_zero])
  haveI : Nontrivial (ι → ℂ) := b.equivFun.symm.toEquiv.nontrivial
  obtain ⟨lam, M₀, hM₀⟩ := GlobalTheory.UnitaryContainsType.exists_smallRep_intertwining n (ι → ℂ) σ hσc
  let M : nablaSq ℂ n lam →ₗ[ℂ] (ι → ℂ) := M₀.toLinearMap
  have hM := GlobalTheory.T.dualWeylModule_intertwines_GL_of_unitaryGroup n lam ι Φ hΦ M fun u v => Representation.IntertwiningMap.isIntertwining _ _ M₀ u v
  have hirr := GlobalTheory.DefU.isIrreducible_sqRep n lam
  have hinj : ∀ v, v ≠ 0 → M v ≠ 0 := by
    intro v hv hMv
    let K : Subrepresentation (GlobalTheory.Branching.sqRep ℂ n lam) :=
      { toSubmodule := LinearMap.ker M
        apply_mem_toSubmodule := fun g z hz => by
          rw [LinearMap.mem_ker] at hz ⊢
          rw [hM, hz, Matrix.mulVec_zero] }
    rcases hirr.eq_bot_or_eq_top K with h | h
    · have h1 : LinearMap.ker M = ⊥ := congrArg Subrepresentation.toSubmodule h
      exact hv (by rw [← Submodule.mem_bot ℂ, ← h1]; exact hMv)
    · have h1 : LinearMap.ker M = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact hM₀ (Representation.IntertwiningMap.ext (LinearMap.ker_eq_top.1 h1))
  obtain ⟨v₀, hv₀, hw⟩ := GlobalTheory.T.exists_highest_weight_vector_dualWeylModule_upper n lam
  refine ⟨lam, ?_, ι, inferInstance, inferInstance, b, P, hP, M v₀, hinj v₀ hv₀, fun A hA => ?_⟩
  · obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.irrS.2.1
    obtain ⟨x₀, hx₀⟩ : ∃ x, f x ≠ 0 := by
      by_contra h
      push Not at h
      exact hf0 (funext h)
    refine ⟨hirr, GlobalTheory.FormDictEx.phiR F R f ∘ₗ B.flip ∘ₗ b.equivFun.symm.toLinearMap ∘ₗ M, fun h0 => ?_,
      fun v => phi_mem hU R hfin hrat hcont hf (B.flip (b.equivFun.symm (M v))), fun x v => ?_⟩
    · obtain ⟨γ, hγ⟩ := exists_pair_ne_zero π.irr a.irr B hB0 hB hx₀
        ((LinearEquiv.map_ne_zero_iff b.equivFun.symm).2 (hinj v₀ hv₀))
      apply hγ
      have h1 := congrFun (LinearMap.congr_fun h0 v₀) (F.j ((γ : GAf L n) * x₀))
      change GlobalTheory.FormDictEx.phi F R f (B.flip (b.equivFun.symm (M v₀))) _ = 0 at h1
      rw [GlobalTheory.FormDictEx.phi_j F R hfin, (π.irrS.1.le hf).1] at h1
      exact h1
    · change GlobalTheory.FormDictEx.phi F R f (B.flip (b.equivFun.symm (M (GlobalTheory.Branching.sqRep ℂ n lam (cEmb τ (x : UA L n)) v)))) =
        RU L n (x : UA L n) (GlobalTheory.FormDictEx.phi F R f (B.flip (b.equivFun.symm (M v))))
      rw [GlobalTheory.FormDictEx.RU_phi, GlobalTheory.FormDictEx.fy_inf F (Subgroup.mem_inf.1 x.2).1, GlobalTheory.FormDictEx.rt_one, hM, hΦx]
      congr 1
      exact LinearMap.ext fun w => (pair_ext a R hfin hrat hcont B hB b P hP w (M v) x).symm
  · have h1 := hM A v₀
    rw [hw A hA, map_smul] at h1
    exact h1.symm

end GlobalTheory.WeightDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CasimirEigenOrthogonal
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

noncomputable section

namespace GlobalTheory.CapOrth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} {μ : Measure (GA E N)}
  {W : Submodule ℂ (Sm E N)} (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1)

open Classical in

def cls (x : Sm E N) : L2 (latticeGL E N) μ := if hx : x ∈ W then toL2ₗ μ W h ⟨x, hx⟩ else 0

theorem cls_mk {x : Sm E N} (hx : x ∈ W) : cls h x = toL2ₗ μ W h ⟨x, hx⟩ := dif_pos hx

theorem cls_add {x y : Sm E N} (hx : x ∈ W) (hy : y ∈ W) : cls h (x + y) = cls h x + cls h y := by
  rw [cls_mk h (W.add_mem hx hy), cls_mk h hx, cls_mk h hy, ← map_add]; rfl

theorem cls_smul (c : ℂ) {x : Sm E N} (hx : x ∈ W) : cls h (c • x) = c • cls h x := by
  rw [cls_mk h (W.smul_mem c hx), cls_mk h hx, ← map_smul]; rfl

theorem cls_sub {x y : Sm E N} (hx : x ∈ W) (hy : y ∈ W) : cls h (x - y) = cls h x - cls h y := by
  rw [cls_mk h (W.sub_mem hx hy), cls_mk h hx, cls_mk h hy, ← map_sub]; rfl

variable (J : Submodule ℂ (Sm E N))

def adjAlg : Subalgebra ℂ (Module.End ℂ (Sm E N)) where
  carrier := {z | (∀ φ ∈ W, z φ ∈ W) ∧ (∀ φ ∈ J, z φ ∈ J) ∧ ∃ z' : Module.End ℂ (Sm E N),
    (∀ φ ∈ W, z' φ ∈ W) ∧ (∀ φ ∈ J, z' φ ∈ J) ∧
      ∀ φ ∈ W, ∀ ψ ∈ W, inner ℂ (cls h (z φ)) (cls h ψ) = inner ℂ (cls h φ) (cls h (z' ψ))}
  mul_mem' := by
    rintro x y ⟨hx, hxJ, x', hx', hx'J, ex⟩ ⟨hy, hyJ, y', hy', hy'J, ey⟩
    refine ⟨fun φ hφ => hx _ (hy φ hφ), fun φ hφ => hxJ _ (hyJ φ hφ), y' * x', fun φ hφ => hy' _ (hx' φ hφ),
      fun φ hφ => hy'J _ (hx'J φ hφ), fun φ hφ ψ hψ => ?_⟩
    exact (ex _ (hy φ hφ) ψ hψ).trans (ey φ hφ _ (hx' ψ hψ))
  add_mem' := by
    rintro x y ⟨hx, hxJ, x', hx', hx'J, ex⟩ ⟨hy, hyJ, y', hy', hy'J, ey⟩
    refine ⟨fun φ hφ => W.add_mem (hx φ hφ) (hy φ hφ), fun φ hφ => J.add_mem (hxJ φ hφ) (hyJ φ hφ), x' + y',
      fun φ hφ => W.add_mem (hx' φ hφ) (hy' φ hφ), fun φ hφ => J.add_mem (hx'J φ hφ) (hy'J φ hφ), fun φ hφ ψ hψ => ?_⟩
    rw [LinearMap.add_apply, LinearMap.add_apply, cls_add h (hx φ hφ) (hy φ hφ), cls_add h (hx' ψ hψ) (hy' ψ hψ),
      inner_add_left, inner_add_right, ex φ hφ ψ hψ, ey φ hφ ψ hψ]
  algebraMap_mem' := by
    intro c
    refine ⟨fun φ hφ => ?_, fun φ hφ => ?_, algebraMap ℂ _ (starRingEnd ℂ c), fun φ hφ => ?_, fun φ hφ => ?_,
      fun φ hφ ψ hψ => ?_⟩
    · rw [Module.algebraMap_end_apply]; exact W.smul_mem _ hφ
    · rw [Module.algebraMap_end_apply]; exact J.smul_mem _ hφ
    · rw [Module.algebraMap_end_apply]; exact W.smul_mem _ hφ
    · rw [Module.algebraMap_end_apply]; exact J.smul_mem _ hφ
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, cls_smul h _ hφ, cls_smul h _ hψ,
        inner_smul_left, inner_smul_right]

variable [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

end GlobalTheory.CapOrth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTypeVector
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

open Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.PrimeDegreeVariant GlobalTheory.TypeLeaf

namespace GlobalTheory.GoodFree

theorem good_of_vector_row : ∀ (D : D7) (Rw : GlobalTheory.HeightCounting.RowSide D) (L : ∀ k, LabelDatum (D.host.g k)) (rc : GlobalTheory.SerSys.Corr D) (cp : GlobalTheory.GoodTypes.Comp D), LabTie D L → LabParam D L rc → (∀ k v, IsClassMap D.naut.lpDim (rc k v)) → GlobalTheory.GoodTypes.SeriesConj D → (∀ σ k v, IrrSm (cp σ k v) ∧ Rw.locR σ (D.naut.plGw k v) = rc k v D.R.r (cp σ k v)) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (σ : D.what₂.FT), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) → ∀ x : V, x ≠ 0 → (∀ a, ρ.asAlgebraHom a x ∈ W) → ρ.asAlgebraHom D.ntypes.e0 x = x → D.nd.goodRow σ := by
  intro D Rw L rc cp hT hLP hCl hC hP V _ _ ρ W σ hW x hx hxW he
  obtain ⟨t, a, ht, h0, hfix⟩ := GlobalTheory.GoodTypes.exists_good D ρ hx he
  have key : ∀ k v, GlobalTheory.SeriesSupportTest.dualFun D k (t k v) = D.nd.lab k σ v := by
    intro k v
    have hl : IsLabel D k (t k v) := (ht k).1.1 v
    have h1 := hfix k v
    rw [GlobalTheory.GoodTypes.act_atPlace] at h1
    have h2 := (hW k v).act_ne _ (D.ntypes.eSer k (dualLab D k (t k v))) (fun y => by
      rw [← GlobalTheory.GoodTypes.labAct_conj D k hl, ← hC k _ hl, Finsupp.mapRange_apply]; rfl) (hxW a) h0 h1
    obtain ⟨p1, p3⟩ := hP σ k v
    have q1 := ((hCl k v) _ _ p1).1
    rw [(hT k).2] at h2
    have h3 := hLP k v D.R.r (cp σ k v) p1 _ h2
    rw [(hT k).1] at h3
    simp only [] at h3
    rw [← p3] at h3 q1
    rw [D.ntypes.inertiaCharpoly_type k v _ (by rw [← Rw.lab_eq, q1, (D.nd.lab_monic k σ v).2]), ← Rw.lab_eq] at h3
    rw [GlobalTheory.SeriesSupportTest.dualFun, if_pos hl]
    exact GlobalTheory.GoodTypes.eq_of_teich _ (GlobalTheory.Compare.TeichmullerRoots.teich_injective _ (D.ntypes.teichC_inj k))
      (GlobalTheory.SeriesSupportTest.label_dual D k hl).1 (D.nd.lab_monic k σ v).1 h3.symm
  have hd := GlobalTheory.SeriesSupportTest.good_dualFun D t ht
  simp only [key] at hd
  exact hd

end GlobalTheory.GoodFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubledLagrangianEqIffSiegelParabolicCosetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledLagrangian_eq_iff_siegelParabolic_coset : ∀ (D : D7) (W : HSp D) (γ γ' : GA D (GlobalTheory.Doubling.dblSp W)) (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) (g₀' : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E), Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D) → Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ' = g₀'.map (incA D) → ∀ (Y Y' : Lag W), IsLagFrame W Y (frameOf W g₀) → IsLagFrame W Y' (frameOf W g₀') → (Y = Y' ↔ γ' * γ⁻¹ ∈ GlobalTheory.Doubling.siegel W) := by
  first | exact @GlobalTheory.SWLagSame.sameClass | exact GlobalTheory.SWLagSame.sameClass | (intros; apply GlobalTheory.SWLagSame.sameClass <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaIntegralSobolevContinuousStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.downward_theta_integral_sobolev_continuous : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) (ε : ℝ), 0 < ε → ∃ (d : ℕ) (δ : ENNReal), 0 < δ ∧ ∀ P, GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P) < δ → ‖downInt R i t y f l g - downInt R i t y (R.ptP i t P) l g‖ < ε := by
  first | exact @GlobalTheory.DownLift.Sobolev₂.downInt_sobolev_cont | exact GlobalTheory.DownLift.Sobolev₂.downInt_sobolev_cont | (intros; apply GlobalTheory.DownLift.Sobolev₂.downInt_sobolev_cont <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmptyPiTensorIsSubquotientJacquetModuleDegreeZer
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory

theorem piTensor_isSubquotient_jac_degZero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ), N = 0 → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (π : Representation ℂ (GL (Fin N) k) V) (d : Fin 0 → ℕ) (X : Fin 0 → Type) [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (e : (Σ a, Fin (d a)) ≃ Fin N),
    IsSubquotient (piTensor ρ) (jac e π) := by
  intro k _ _ _ _ N hN V _ _ _ π d X _ _ ρ e
  subst hN
  have hK : twKer π (unipRad k e) 1 = ⊥ := by
    refine le_bot_iff.1 (Submodule.span_le.2 ?_)
    rintro w ⟨n, v, rfl⟩
    have h1 : (n : GL (Fin 0) k) = 1 := Subsingleton.elim _ _
    simp [h1]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hx : (Submodule.Quotient.mk v : Jacquet π (unipRad k e)) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero, hK, Submodule.mem_bot]; exact hv
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (Jacquet π (unipRad k e)),
      φ (Submodule.Quotient.mk v) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
  let L : Jacquet π (unipRad k e) →ₗ[ℂ] PiTensorProduct ℂ X :=
    (PiTensorProduct.isEmptyEquiv (Fin 0)).symm.toLinearMap ∘ₗ φ
  refine IsSubquotient.of_surjective ⟨L, fun g => ?_⟩ ?_
  · have hg : g = 1 := Subsingleton.elim _ _
    subst hg
    rw [map_one, map_one]
    rfl
  · have hsurj : Function.Surjective φ := fun c =>
      ⟨(c / φ (Submodule.Quotient.mk v)) • Submodule.Quotient.mk v, by simp [hφ]⟩
    exact (PiTensorProduct.isEmptyEquiv (Fin 0)).symm.surjective.comp hsurj

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDictionaryCmFieldAutomorphicStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dictionary_cm_field_automorphic : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n), ∃ U, Dict F π U := by
  first | exact @GlobalTheory.FormDictEx.exists_dict | exact GlobalTheory.FormDictEx.exists_dict | (intros; apply GlobalTheory.FormDictEx.exists_dict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDoubledLagrangianOfRationalUnitaryFrameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_doubledLagrangian_of_rational_unitary_frame : ∀ (D : D7) (W : HSp D) (γ : GA D (GlobalTheory.Doubling.dblSp W)) (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E), Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D) → ∃ Y : Lag W, IsLagFrame W Y (frameOf W g₀) := by
  first | exact @GlobalTheory.SWLagTerms.LagrangianFrames.exists_lag_isLagFrame_frameOf | exact GlobalTheory.SWLagTerms.LagrangianFrames.exists_lag_isLagFrame_frameOf | (intros; apply GlobalTheory.SWLagTerms.LagrangianFrames.exists_lag_isLagFrame_frameOf <;> assumption)
end

