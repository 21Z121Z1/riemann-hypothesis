import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3427
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3419
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0016
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3428
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3382
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2348
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3429
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaAtClosedPoint
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2383

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallThetaKernelTranslateIntegrableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_theta_kernel_translate_integrable : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → Big fun ch => ∀ i j t (M : Vol ch.G), M.Is t → ∀ Θ Θ', IsMatched ch.S.B t ch.rm i j Θ Θ' → ∀ g g₁,
    ∃ z, zdeg z ≠ 0 ∧ IntegrableOn (translates z (kerSmall ch.W Θ' g g₁)) (M.fd _) (M.ν _) := by
  first | exact @GlobalTheory.SmallConv.exists_translates_integrableOn | exact GlobalTheory.SmallConv.exists_translates_integrableOn | (intros; apply GlobalTheory.SmallConv.exists_translates_integrableOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecHomExtOfLocalizationAtPrimes
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SpecLocalExt

theorem hom_ext_of_localizationAtPrime : ∀ (A : Type) [CommRing A] (X : Scheme.{0}) (a b : Sp A ⟶ X), (∀ (P : Ideal A) [P.IsPrime], spMap (algebraMap A (Localization.AtPrime P)) ≫ a = spMap (algebraMap A (Localization.AtPrime P)) ≫ b) → a = b := by
  intro A _ X a b h
  refine GlobalTheory.hom_ext_of_isLocalRing fun B _ _ φ => ?_
  let P : Ideal A := (IsLocalRing.maximalIdeal B).comap φ
  haveI : P.IsPrime := Ideal.comap_isPrime φ (IsLocalRing.maximalIdeal B)
  have hu : ∀ y : P.primeCompl, IsUnit (φ y) := fun y => by
    by_contra hy
    exact y.2 ((IsLocalRing.mem_maximalIdeal _).2 hy)
  let ψ : Localization.AtPrime P →+* B := IsLocalization.lift hu
  have e : φ = ψ.comp (algebraMap A (Localization.AtPrime P)) := (IsLocalization.lift_comp hu).symm
  have h' := h P
  simp only [spMap] at h'
  rw [e, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc, h']

end GlobalTheory.SpecLocalExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongerPublishedHypothesesImply
section
open GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.CovTop

theorem Hypotheses2.toClassicalTheorems : Hypotheses2 → Hypotheses₂ := fun h => h.toClassicalTheoremsOf GlobalTheory.T.toroidalFlagProportionality_of_goodChernWeil

end GlobalTheory.CovTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubOfScaledSectionValuesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_of_scaled_section_values : ∀ {R Ω : Type} [CommRing R] [IsDomain R] [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (p : Y ⟶ Sp R) (L : LB Y) (x : Sp Ω ⟶ Y) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)), x ≫ p = spMap φ → ∀ (k : ℕ) (s s' : FractionRing Ω), GlobalTheory.HeatSym.VS φ L x g k s → GlobalTheory.HeatSym.VS φ L x g k s' → GlobalTheory.HeatSym.VS φ L x g k (s - s') := by
  first | exact @GlobalTheory.HeatSym.VS.sub | exact GlobalTheory.HeatSym.VS.sub | (intros; apply GlobalTheory.HeatSym.VS.sub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMulHodgeFilEqZeroOfDeRhamCoboundaryStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_mul_hodgeFil_eq_zero_of_deRham_coboundary : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ y ∈ Fil B, ∀ (D : Type) [CommRing D] [Algebra R D] (J : Type) [Fintype J] (d : J → D) (β : J → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (hβ : ∀ i, CatCoh.H1.mk _ (β i) ∈ primDR B), (∃ k, IsCob (whole _) (sumMul d fun i ↦ fv (β i)) k) → ∑ i, d i * algebraMap R D (y ⟨_, hβ i⟩) = 0 := by
  first | exact @GlobalTheory.PtExt.sum_mul_eq_zero_of_isCob | exact GlobalTheory.PtExt.sum_mul_eq_zero_of_isCob | (intros; apply GlobalTheory.PtExt.sum_mul_eq_zero_of_isCob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBalancedTensorsFiniteProjectiveRankDim
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.BalProj

theorem balanced_finite_projective_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → Module.Finite Γ(Y.X, U.1) (balanced H.bar A) ∧ Module.Projective Γ(Y.X, U.1) (balanced H.bar A) ∧ ∀ m : Ideal Γ(Y.X, U.1), m.IsMaximal → Module.finrank (Γ(Y.X, U.1) ⧸ m) ((Γ(Y.X, U.1) ⧸ m) ⊗[Γ(Y.X, U.1)] (balanced H.bar A)) = Dw.dim := by
  intro E _ _ _ H Dw l Xo c Y h1 hsm hsnc U n v A hv hb hA
  obtain ⟨h1A, haddA, hmulA⟩ := GlobalTheory.T.tangentBasis_actionMatrices_ringHom H Y.t Γ(Y.X, U.1) (chart U) n v A hv hb hA
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.balancedSymmetricLieTensors_finite_projective_rank H c.F c.conj Γ(Y.X, U.1) (GlobalTheory.BalProj.fnHom Y.s U.1) n A h1A haddA hmulA
  refine ⟨hfin, hproj, fun m hm => ?_⟩
  have key : ∀ τ : E →+* ℂ, GlobalTheory.BalProj.eigRank (algebraMap Γ(Y.X, U.1) m.ResidueField) A
      (GlobalTheory.BalProj.embR c.F c.conj (GlobalTheory.BalProj.fnHom Y.s U.1) τ) = if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q := by
    intro τ
    set e : ℕ := if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q with he
    let f : PrimeSpectrum Γ(Y.X, U.1) → ℕ := fun 𝔭 => GlobalTheory.BalProj.eigRank (algebraMap Γ(Y.X, U.1) 𝔭.asIdeal.ResidueField) A
      (GlobalTheory.BalProj.embR c.F c.conj (GlobalTheory.BalProj.fnHom Y.s U.1) τ)
    have hop : ∀ N, IsOpen {𝔭 | f 𝔭 = N} := fun N =>
      GlobalTheory.T.isOpen_eigenRank_levelSet_integersAction c.F c.conj Γ(Y.X, U.1) (GlobalTheory.BalProj.fnHom Y.s U.1) n A h1A haddA hmulA τ N
    have hcl : IsClosed {𝔭 | f 𝔭 = e} := by
      rw [← isOpen_compl_iff]
      have : {𝔭 | f 𝔭 = e}ᶜ = ⋃ N ∈ {N : ℕ | N ≠ e}, {𝔭 | f 𝔭 = N} := by
        ext 𝔭; simp
      rw [this]
      exact isOpen_biUnion fun N _ => hop N
    have hsub : (chart U).base ⁻¹' (interior Y : Set Y.X) ⊆ {𝔭 | f 𝔭 = e} := fun 𝔭 h𝔭 =>
      GlobalTheory.T.eigenRank_interior_eq_signature E H Dw l Xo c Y h1 hsm hsnc U n v A hv hb hA 𝔭 h𝔭 τ
    have hall : {𝔭 | f 𝔭 = e} = Set.univ :=
      Set.eq_univ_of_univ_subset ((GlobalTheory.T.dense_affineChart_preimage_interior E H Dw l Xo c Y U).closure_eq ▸ (closure_mono hsub).trans hcl.closure_subset)
    have := hall ▸ Set.mem_univ (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(Y.X, U.1))
    exact this
  have h2 := hrk m
  simp_rw [key] at h2
  rw [GlobalTheory.T.cmType_signature_sum_eq_twice_dimension E H Dw.p Dw.q] at h2
  unfold Datum.dim
  omega

end GlobalTheory.BalProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCoefficientsUniqueAffineOpenStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_coefficients_unique_affine_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (cf cf' : Fin n → Γ(X, W.1)) (w : Sp (DualNumber Γ(X, W.1)) ⟶ t.G.left), IsCombAtG t (chart W) (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) cf w → IsCombAtG t (chart W) (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) cf' w → cf = cf' := by
  first | exact @GlobalTheory.KSAgree.TanLocUnique.comb_unique_basicOpen | exact GlobalTheory.KSAgree.TanLocUnique.comb_unique_basicOpen | (intros; apply GlobalTheory.KSAgree.TanLocUnique.comb_unique_basicOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentKillingWeightZeroMapsToAbelianPartUnit
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HeatMod.TorField

open TrivSqZeroExt (inl inr)

theorem residue_eq_zero_of_sq {B : Type} [CommRing B] [IsLocalRing B] (x : B) (h : x * x = 0) :
    IsLocalRing.residue B x = 0 :=
  (IsLocalRing.residue_eq_zero_iff x).2 ((IsLocalRing.mem_maximalIdeal x).2 (mem_nonunits_iff.2 fun hu => by
    have := hu.mul hu
    rw [h] at this
    exact not_isUnit_zero this))

theorem lieExp_comp_q_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (u : Fin n → (epsR R ⟶ Y.H)), (∀ a, IsTangent (u a)) → (∀ a, (u a).left = (tv (v a)).left) → ∀ (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ e : Fin n → R, (∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0) → ∀ (B : Type) [CommRing B] [IsLocalRing B] (ψ : DualNumber R →+* B), spMap ψ ≫ (GlobalTheory.SqZero.lieExp u (fun a => (TrivSqZeroExt.inr (e a) : DualNumber R)) (fun _ => TrivSqZeroExt.inr_mul_inr _ _ _) ≫ Y.q).left = spMap ψ ≫ (1 : epsR R ⟶ Q.P.A).left := by
  intro R _ _ Q O _ _ _ oa Y n v u ht hu dd hd e hw B _ _ ψ
  letI : Algebra R B := (ψ.comp (TrivSqZeroExt.inlHom R R)).toAlgebra
  let ψ' : DualNumber R →ₐ[R] B := { ψ with commutes' := fun r => rfl }
  have hqm : IsMonHom Y.q := Y.q_linear.isMonHom
  let c : Fin n → DualNumber R := fun a => inr (e a)
  have hc : ∀ a, c a * c a = 0 := fun _ => TrivSqZeroExt.inr_mul_inr _ _ _
  let p : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (DualNumber R) ⟶ Y.H := GlobalTheory.SqZero.lieExp u c hc
  let z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ Y.H := 1
  let t : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ Y.H := ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ' ≫ p
  have hψ : (ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ').left = spMap ψ := ReciprocityTheory.ChartRestriction.G.Chart.spMap_left ψ'
  have e1 : spMap ψ ≫ (p ≫ Y.q).left = t.left ≫ Y.q.left := by
    rw [← hψ]; rfl
  have e2 : spMap ψ ≫ (1 : epsR R ⟶ Q.P.A).left = z.left ≫ Y.q.left := by
    rw [← hψ, ← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [ReciprocityTheory.ChartRestriction.G.Chart.comp_one', MonObj.one_comp]
  show spMap ψ ≫ (p ≫ Y.q).left = _
  rw [e1, e2]

  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.hom_ext_of_local (R := CommRingCat.of B) ?_ ?_
  · letI : Algebra R (IsLocalRing.ResidueField B) :=
      ((IsLocalRing.residue B).comp (algebraMap R B)).toAlgebra
    let r : B →ₐ[R] IsLocalRing.ResidueField B := { IsLocalRing.residue B with commutes' := fun _ => rfl }
    have htan : IsTangent p :=
      GlobalTheory.Reg.isTangent_of_isLieComb ht ((GlobalTheory.SqZero.isLieComb_iff_lieExp e p).2 rfl)
    have hrc : r.comp ψ' = (Algebra.ofId R (IsLocalRing.ResidueField B)).comp (ReciprocityTheory.ChartRestriction.G.Chart.fstD R) :=
      DualNumber.algHom_ext (by
        have : r (ψ' DualNumber.eps) = 0 := residue_eq_zero_of_sq _ (by
          rw [← map_mul, DualNumber.eps_mul_eps, map_zero])
        rw [AlgHom.comp_apply, this, AlgHom.comp_apply]
        simp [ReciprocityTheory.ChartRestriction.G.Chart.fstD])
    have hr : ReciprocityTheory.ChartRestriction.G.Chart.spMap r ≫ t = ReciprocityTheory.ChartRestriction.G.Chart.spMap r ≫ z := by
      rw [ReciprocityTheory.ChartRestriction.G.Chart.comp_one']
      show ReciprocityTheory.ChartRestriction.G.Chart.spMap r ≫ ReciprocityTheory.ChartRestriction.G.Chart.spMap ψ' ≫ p = 1
      rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hrc, ← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp,
        Category.assoc, show ReciprocityTheory.ChartRestriction.G.Chart.spMap (ReciprocityTheory.ChartRestriction.G.Chart.fstD R) ≫ p = 1 from
          (ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff p).2 htan, ReciprocityTheory.ChartRestriction.G.Chart.comp_one']
    have H : (ReciprocityTheory.ChartRestriction.G.Chart.spMap r).left ≫ t.left ≫ Y.q.left =
        (ReciprocityTheory.ChartRestriction.G.Chart.spMap r).left ≫ z.left ≫ Y.q.left := by
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (fun f => Over.Hom.left f ≫ Y.q.left) hr
    rw [ReciprocityTheory.ChartRestriction.G.Chart.spMap_left] at H
    have hcp : (Spec.map (CommRingCat.ofHom r.toRingHom)).base (IsLocalRing.closedPoint (IsLocalRing.ResidueField B)) =
        IsLocalRing.closedPoint (CommRingCat.of B) := IsLocalRing.comap_closedPoint (IsLocalRing.residue B)
    rw [← hcp]
    exact congrArg (fun f => f (IsLocalRing.closedPoint (IsLocalRing.ResidueField B))) H
  · intro U h₁ h₂
    have H : ∀ g, valR (t.left ≫ Y.q.left) U g = valR (z.left ≫ Y.q.left) U g := by
      intro g
      have hz : ⊤ ≤ z.left ⁻¹ᵁ (Y.q.left ⁻¹ᵁ U) := h₂
      let e' : Fin n → B := fun a => ψ' (c a)
      have he' : ∀ i j, e' i * e' j = 0 := fun i j => by
        simp only [e', ← map_mul, c, TrivSqZeroExt.inr_mul_inr, map_zero]
      obtain ⟨b₁, b₂⟩ := valR_prod hu ht hd e' he' z (Y.q.left ⁻¹ᵁ U) hz Finset.univ
      have ht' : t = (∏ i ∈ Finset.univ, (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo R (e' i) (he' i i)) ≫ u i :
          ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ Y.H)) * z := by
        rw [_root_.mul_one]
        exact GlobalTheory.SqZero.comp_lieExp u ψ' c hc
      rw [← ht'] at b₁ b₂
      have hF : pbT Y.q.left g (Y.q.left ⁻¹ᵁ U) = (Y.q.left.appLE U (Y.q.left ⁻¹ᵁ U) le_rfl).hom g :=
        GlobalTheory.KS.pbT_of_le _ le_rfl g
      have hwF := hw U _ (isWt_pbT Y U g (Y.q.left ⁻¹ᵁ U) le_rfl)
      rw [← GlobalTheory.Points.valR_appLE t.left Y.q.left le_rfl b₁ g, ← GlobalTheory.Points.valR_appLE z.left Y.q.left le_rfl hz g,
        ← hF, b₂]
      have hz' : z.left ≫ Y.H.hom = spMap (algebraMap R B) := Over.w z
      have key : ∀ i, e' i = ψ (inr 1) * algebraMap R B (e i) := fun i => by
        show ψ (inr (e i)) = ψ (inr 1) * ψ (inl (e i))
        rw [← map_mul]
        congr 1
        ext <;> simp
      have hv := congrArg (valR z.left (Y.q.left ⁻¹ᵁ U)) hwF
      rw [GlobalTheory.ZH.CrdCalc.valR_eq _ _ hz, map_sum, GlobalTheory.ZH.CrdCalc.valR_eq _ _ hz, map_zero] at hv
      simp only [← GlobalTheory.ZH.CrdCalc.valR_eq _ _ hz, WtAlg.valR_mul'' _ _ hz,
        GlobalTheory.Points.valR_constFn_of_over _ _ _ hz' _ hz] at hv
      simp only [key, _root_.mul_assoc, ← Finset.mul_sum, hv, mul_zero, add_zero]
    ext g
    have := H g
    rw [GlobalTheory.ZH.CrdCalc.valR_eq _ _ h₁, GlobalTheory.ZH.CrdCalc.valR_eq _ _ h₂] at this
    exact (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.injective this

end GlobalTheory.HeatMod.TorField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyValuesDetOmegaDeltaLocalUnitsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyValues_detOmega_delta_local_units : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ →
  ∀ (S : Scheme.{0}) [IsIntegral S] (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    ∃ f : (VB.det (LieVB.omega G) g).ι → δ.ι → S.presheaf.stalk (genericPoint S),
      (∀ c i, ∀ x ∈ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i, ∃ (V : S.Opens) (_ : V ≤ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i)
        (_ : x ∈ V) (u : Γ(S, V)ˣ), ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f c i) ∧
      (∀ c c' i i' (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
        (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i'),
        f c i * S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) ^ 8 =
          S.presheaf.germ _ (genericPoint S) h1
            ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) ^ 4 * f c' i') := by
  first | exact @GlobalTheory.KeyValsPf.keyVals | exact GlobalTheory.KeyValsPf.keyVals | (intros; apply GlobalTheory.KeyValsPf.keyVals <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToUnitTKLeft
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DDataGens

theorem toUnit_TK_left (R : Type) [CommRing R] [IsDomain R] : (toUnit (TK R)).left = jK R := by
  have := Over.w (toUnit (TK R))
  simpa using this

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → (∀ y, PsiUnitOn D y Set.univ) →
    ∃ τ₀ : GlobalTheory.UChart.Gens D, ∀ a b, (τ₀ a b).IsGen ∧ ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J → val (D.tau a b) (𝟙 _) z J = val (τ₀ a b) (toUnit (TK R)).left z J := by
  intro R _ _ D hB hU
  choose t ht hc using fun y => (GlobalTheory.ArcPull.psiUnitOn_univ_iff D y).1 (hU y)
  have key : ∀ a b, ∃ g : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(D.c (a + b)).left, (D.c a).left, (D.c b).left, (D.c 0).left] ![-1, 1, 1, -1]), g.IsGen ∧
      ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        val g (toUnit (TK R)).left z J = val (t (a + b)) (toUnit (TK R)).left z J *
          (val (t a) (toUnit (TK R)).left z J)⁻¹ * (val (t b) (toUnit (TK R)).left z J)⁻¹ *
          val (t 0) (toUnit (TK R)).left z J := by
    intro a b
    let T := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (t (a + b))
      (LB.invGen D.P.L _ _ (t a))) (LB.invGen D.P.L _ _ (t b))) (t 0)
    have hT : T.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (ht _) (DVR.invGen_isGen _ _ _ _ (ht _)))
      (DVR.invGen_isGen _ _ _ _ (ht _))) (ht _)
    obtain ⟨g, hg, hv⟩ := exists_gen D.P.isLB
      (φ' := ![(D.c (a + b)).left, (D.c a).left, (D.c b).left, (D.c 0).left]) (ε' := ![-1, 1, 1, -1])
      (by
        intro U _ h
        simp [Fintype.prod_sum_type, Fin.prod_univ_four]) T hT
    refine ⟨g, hg, fun z J hJ => ?_⟩
    rw [hv _ _ z J hJ]
    simp only [T, val_mul hJ, val_inv]
  choose τ₀ hτ hv using key
  refine ⟨τ₀, fun a b => ⟨hτ a b, fun z J hJ => ?_⟩⟩
  have hp : ∀ y, val (t y) (toUnit (TK R)).left z J = val (D.psi y) (𝟙 _) z J := fun y => by
    rw [← val_corr hJ (hc y) (𝟙 _), val_pull hJ, Category.id_comp, toUnit_TK_left]
  have vρ : val D.rigK (𝟙 _) z J = val D.rig (jK R) z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp, toUnit_TK_left]
  rw [hv a b z J hJ, hp, hp, hp, hp, GlobalTheory.PsiZero.val_psi_zero hB hJ]
  simp only [DegPre.tau, val_mul hJ, val_inv, vρ]

end GlobalTheory.DDataGens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorActsOnFourierTermsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D), IsBasic Y h → ∀ (k : ℕ) (α : Dd.toPre.X) (σ : Dd.toPre.SecB k α), ∃ σ', TActs Y h k α σ σ' := by
  first | exact @GlobalTheory.Heat.heat_acts_on_terms | exact GlobalTheory.Heat.heat_acts_on_terms | (intros; apply GlobalTheory.Heat.heat_acts_on_terms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}

def UValThru (Xo : Moduli D l) (c : Coeff l) {S T : Scheme.{0}} (i : Xo.XF c ⟶ T) (π : S ⟶ T) (A : Set S)
    (φ : InvFun (𝓞 E)) (J : S.IdealSheafData) (d : ℕ) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ →
    ∀ (χ : Sp W ⟶ S) (y : Sp (FractionRing W) ⟶ Xo.XF c), y ≫ i = jK W ≫ χ ≫ π → χ (closedPoint W) ∈ A →
    ∀ (t : SAB H (Sp W)) (tK : SAB H (Sp (FractionRing W))), Nonempty (SABMap tK t (jK W)) →
      Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∀ P : PELUnif (maximalIdeal W) t,
      ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] →
        ∃ n : ℕ, (n : ℝ) = d * φ.evalZ be ∧ idlAlong J χ = Ideal.span {ϖ ^ n}

variable {Xo : Moduli D l} {c : Coeff l}

theorem uValThru_top_of_disjoint {S : Scheme.{0}} {i : Xo.XF c ⟶ S} {A : Set S} (hA : IsOpen A)
    (hd : A ∩ Set.range i = ∅) (φ : InvFun (𝓞 E)) (d : ℕ) : UValThru Xo c i (𝟙 S) A φ ⊤ d := by
  intro W _ _ _ _ ϖ _ χ y hy hA' _ _ _ _ _ _ _ _
  exfalso
  let g : Sp (FractionRing W) := closedPoint (FractionRing W)
  have hsp : (jK W) g ⤳ closedPoint W := IsLocalRing.specializes_closedPoint _
  have hmem : χ ((jK W) g) ∈ A := (hsp.map χ.continuous).mem_open hA hA'
  have hrange : χ ((jK W) g) ∈ Set.range i := ⟨y g, by
    have := congrArg (fun f => f.base g) hy
    simpa using this⟩
  have : χ ((jK W) g) ∈ A ∩ Set.range i := ⟨hmem, hrange⟩
  rw [hd] at this
  exact this

theorem exists_uValOn_of_pieces {S : Scheme.{0}} (i : Xo.XF c ⟶ S) (φ : InvFun (𝓞 E)) {ι : Type} [Fintype ι]
    (A : ι → Set S) (J : ι → S.IdealSheafData) (d : ι → ℕ) (huniq : ∀ x, ∃! k, x ∈ A k) (hd : ∀ k, 1 ≤ d k)
    (hsupp : ∀ k, ∀ x ∈ (J k).support, x ∈ A k ∧ x ∉ Set.range i)
    (hv : ∀ k, UValThru Xo c i (𝟙 S) (A k) φ (J k) (d k)) :
    ∃ (d' : ℕ) (J' : S.IdealSheafData), 1 ≤ d' ∧ (∀ x ∈ J'.support, x ∉ Set.range i) ∧ UValOn Xo c i φ J' d' := by
  have hdvd : ∀ k, d k ∣ ∏ k, d k := fun k => Finset.dvd_prod_of_mem (s := Finset.univ) d (Finset.mem_univ k)
  have htop : ∀ k x, x ∉ A k → FinalTheorems.stalkId (J k) x = ⊤ := fun k x hx =>
    GlobalTheory.Vanishing.stalkId_eq_top (J k) fun hs => hx (hsupp k x hs).1
  refine ⟨∏ k, d k, ∏ k, J k ^ ((∏ k, d k) / d k), ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun k _ => by have := hd k; omega)
  · intro x hx
    obtain ⟨k, hk, -⟩ := huniq x
    by_cases hs : x ∈ (J k).support
    · exact (hsupp k x hs).2
    · exfalso
      refine (mem_support_iff_stalkId _ x).1 hx ?_
      rw [stalkId_prodPow, ← Ideal.one_eq_top]
      refine Finset.prod_eq_one fun k' _ => ?_
      by_cases e : k' = k
      · subst e; rw [GlobalTheory.Vanishing.stalkId_eq_top (J k') hs, ← Ideal.one_eq_top, one_pow]
      · rw [htop k' x fun h => e ((huniq x).unique h hk), ← Ideal.one_eq_top, one_pow]
  · intro W _ _ _ hW ϖ hϖ χ y hy t tK h1 h2 P be hbe hmono
    obtain ⟨k, hk, -⟩ := huniq (χ (closedPoint W))
    obtain ⟨a, ha, hJ⟩ := hv k W hW ϖ hϖ χ y (by rw [Category.comp_id]; exact hy) hk t tK h1 h2 P be hbe hmono
    refine ⟨(∏ k, d k) / d k * a, ?_, ?_⟩
    · have hd0 : (d k : ℝ) ≠ 0 := by have := hd k; positivity
      rw [Nat.cast_mul, Nat.cast_div (hdvd k) hd0, ha]
      field_simp
    · unfold idlAlong at hJ ⊢
      rw [stalkId_prodPow, Finset.prod_eq_single k, Ideal.map_pow, hJ, Ideal.span_singleton_pow, ← pow_mul, mul_comm]
      · intro k' _ e
        rw [htop k' _ fun h => e ((huniq _).unique h hk), ← Ideal.one_eq_top, one_pow]
      · intro h; exact absurd (Finset.mem_univ k) h

end GlobalTheory.UPoinc
end
end

