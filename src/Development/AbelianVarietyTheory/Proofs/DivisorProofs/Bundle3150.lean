import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3105
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3123
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2367
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1972
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2221
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3109
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2055
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2974
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2661
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3106
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3107
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationThetaSeriesAlgebraicOverFractionFielStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationThetaSeries_algebraic_over_fractionField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (m : ℕ), Odd m → IsUnit (m : R) → ∀ (Ix : Type) (p : Ix → QkPt D.toPre (Kb R) (m ^ 2)), ∃ v : Ix → Kb R, ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : Ix → QkPt D.toPre C (m ^ 2)) (q : Ix → N.QT (m ^ 2)), (∀ i, QkExt em.toRingHom (p i) (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx m (q i) := by
  first | exact @GlobalTheory.Mum.ThetaSer.theta_series_algebraic | exact GlobalTheory.Mum.ThetaSer.theta_series_algebraic | (intros; apply GlobalTheory.Mum.ThetaSer.theta_series_algebraic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarCommPullbackOfSmoothDelDbar
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.HolAtlas

variable {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' : ℕ} (A : HolAtlas M n) (A' : HolAtlas M' n')

theorem loc_pullback_eq {f : M' → M} {α : A.Fld} (hf : A.IsHolo A' f) (hα : A.IsForm α) (j : A'.ι) (i : A.ι) :
    IsOpen ((A'.e j).target ∩ (A'.e j).symm ⁻¹' (f ⁻¹' (A.e i).source)) ∧
    ∀ v ∈ (A'.e j).target ∩ (A'.e j).symm ⁻¹' (f ⁻¹' (A.e i).source),
      A'.loc (A.pullback A' f α) j v =
        pull (fderiv ℂ (A.e i ∘ f ∘ (A'.e j).symm) v) (A.loc α i ((A.e i ∘ f ∘ (A'.e j).symm) v)) := by
  refine ⟨(A'.e j).continuousOn_symm.isOpen_inter_preimage (A'.e j).open_target
    ((A.e i).open_source.preimage hf.1), fun v hv => ?_⟩
  have hs : (A'.e j).symm v ∈ (A'.e j).source := (A'.e j).map_target hv.1
  have hτ : (A.e i ∘ f ∘ (A'.e j).symm) v ∈ (A.e i).target := (A.e i).map_source hv.2
  rw [HolAtlas.loc, dif_pos hv.1, HolAtlas.loc, dif_pos hτ,
    GlobalTheory.T.holAtlas_pullback_eq_chart_expression M M' n n' A A' f α hf hα ⟨(j, (A'.e j).symm v), hs⟩ i hv.2]
  have hc : (A'.e j) ((A'.e j).symm v) = v := (A'.e j).right_inv hv.1
  simp only [Pt.crd, Pt.ch, Pt.pt, hc]
  congr 2
  exact Subtype.ext (Prod.ext rfl ((A.e i).left_inv hv.2).symm)

theorem pullback_del_dbar (f : M' → M) (α : A.Fld) (hf : A.IsHolo A' f) (hα : A.IsForm α) :
    A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧
      A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α) := by
  have key : ∀ x : A'.Pt, A'.del (A.pullback A' f α) x = A.pullback A' f (A.del α) x ∧
      A'.dbar (A.pullback A' f α) x = A.pullback A' f (A.dbar α) x := by
    intro x
    have hi : f x.pt ∈ (A.e (A.cover (f x.pt)).choose).source := (A.cover (f x.pt)).choose_spec
    obtain ⟨hU, hloc⟩ := loc_pullback_eq A A' hf hα x.1.1 (A.cover (f x.pt)).choose
    have hx : x.crd ∈ (A'.e x.1.1).target ∩ (A'.e x.1.1).symm ⁻¹' (f ⁻¹' (A.e (A.cover (f x.pt)).choose).source) := by
      refine ⟨(A'.e x.1.1).map_source x.2, ?_⟩
      show (A'.e x.1.1).symm (A'.e x.1.1 x.1.2) ∈ f ⁻¹' (A.e (A.cover (f x.pt)).choose).source
      rw [(A'.e x.1.1).left_inv x.2]
      exact hi
    have hτx : (A.e (A.cover (f x.pt)).choose ∘ f ∘ (A'.e x.1.1).symm) x.crd =
        A.e (A.cover (f x.pt)).choose (f x.pt) := by
      show A.e _ (f ((A'.e x.1.1).symm (A'.e x.1.1 x.1.2))) = _
      rw [(A'.e x.1.1).left_inv x.2]
    have hdiff : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α (A.cover (f x.pt)).choose y) S)
        ((A.e (A.cover (f x.pt)).choose ∘ f ∘ (A'.e x.1.1).symm) x.crd) := by
      intro S
      rw [hτx]
      exact ((hα.smooth _ S).differentiableOn (by simp)).differentiableAt
        ((A.e _).open_target.mem_nhds ((A.e _).map_source hi))
    have hc := GlobalTheory.T.del_dbar_chainRule_holomorphicPullback n' n _ _ (A.loc α (A.cover (f x.pt)).choose) x.crd hU hx (hf.2 x.1.1 _) hdiff
    have hl := (GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local n' x.crd).2.2.2.1 _ _ (Filter.eventually_of_mem (hU.mem_nhds hx) hloc)
    rw [hτx] at hc
    exact ⟨(hl.1.trans hc.1 : _), (hl.2.trans hc.2 : _)⟩
  exact ⟨funext fun x => (key x).1, funext fun x => (key x).2⟩

end GlobalTheory.CxForm.HolAtlas

theorem GlobalTheory.CxForm.HolAtlas.del_dbar_comm_pullback : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ)
    (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α → A.IsForm (A.del α) → A.IsForm (A.dbar α) →
    A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧ A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α) :=
  fun _ _ _ _ _ _ A A' f α hf hα _ _ => HolAtlas.pullback_del_dbar A A' f α hf hα
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleSwapSymmetricStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descended_birigidified_bundle_swap_symmetric : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) := by
  first | exact @GlobalTheory.DescSymm.lbIso_swap | exact GlobalTheory.DescSymm.lbIso_swap | (intros; apply GlobalTheory.DescSymm.lbIso_swap; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleTrivialOnAxesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descended_birigidified_bundle_trivial_on_axes : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → (∃ t : (P₀.pull (lift (1 : A₀ ⟶ A₀) (𝟙 A₀)).left).Gen, t.IsGen) ∧ (∃ t : (P₀.pull (lift (𝟙 A₀) (1 : A₀ ⟶ A₀)).left).Gen, t.IsGen) := by
  first | exact @GlobalTheory.DescGalRig.exists_gen_lift_of_descent | exact GlobalTheory.DescGalRig.exists_gen_lift_of_descent | (intros; apply GlobalTheory.DescGalRig.exists_gen_lift_of_descent; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedPolarisationKernelKilledSameIntegerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descended_polarisation_kernel_killed_same_integer : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (e : ℕ), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∀ (T : Over X) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1) → ∀ (T : Over Y) (x : T ⟶ A₀), (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | (exact @GlobalTheory.DescPolKer.pow_eq_one_of_descent) | (exact GlobalTheory.DescPolKer.pow_eq_one_of_descent) | (intros; apply GlobalTheory.DescPolKer.pow_eq_one_of_descent  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfNondeg
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilBridge
open GlobalTheory.WeilSchrodinger

theorem det_ne_zero_of_nondeg (D : D7) {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E)
    (h : (sesq D G).Nondegenerate) : G.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hv
  apply h.2 v
  intro x
  have e : ∀ i, ∑ j, G i j * v j = 0 := fun i => by
    have := congrFun hGv i
    simpa [Matrix.mulVec, dotProduct] using this
  simp only [sesq, Matrix.toLinearMapₛₗ₂'_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun j _ => mul_comm (v j) (G i j), e i, mul_zero]

theorem exists_isTransport (D : D7) (B : Base D.host.F D.host.E) (hB : B.IsGood D.sp.cm.sig)
    (S T : HSp D) (X : Spc D.host.F D.host.E T.rank) (Y : Spc D.host.F D.host.E S.rank) (r s r' s' : ℕ)
    (hX : X.IsHerm D.sp.cm.sig B r s) (hY : Y.IsSkew D.sp.cm.sig B r' s')
    (eA : X.J = T.gramᵀ)
    (eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • incM D.host.F Y.J = incM D.host.F (D.host.xi0 • S.gram⁻¹))
    (Mo : Model D.sp.cm.sig X Y) (hMo : Mo.IsGood B.ψ) (χX χW : Chr D.host.F D.host.E)
    (hcX : GlobalTheory.LFun.IsHecke D.host.F D.host.E χX) (hcW : GlobalTheory.LFun.IsHecke D.host.F D.host.E χW)
    (rX : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χX T.rank)
    (rW : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χW S.rank)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig X Y) (hom : Mo.IsWeil B.ψ χX χW om) :
    ∃ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
      Formalism.IndefR.Datum.IsWeilDatumO B.ψ S T χW χX ω ∧ IsTransport B.ψ Mo.co ω om := by
  have hψ : IsStdChar D B.ψ (-1) := GlobalTheory.T.isStdChar_neg_one_of_standardTraceAdelicAddChar D B.ψ hB.std
  have rS := GlobalTheory.T.restrictsToQuadraticSignPow_idelic_restriction D χW S.rank rW
  have rT := GlobalTheory.T.restrictsToQuadraticSignPow_idelic_restriction D χX T.rank rX
  obtain ⟨ω, hω⟩ := GlobalTheory.weilRepresentationUnitaryPair D B.ψ S T χW χX hψ hcW hcX rS rT
  obtain ⟨om₀, hom₀⟩ := GlobalTheory.T.exists_weilDatum_transport_adelicSchwartz_thetaTransform D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB
    (Fin T.rank × Fin S.rank) Mo.co hMo.rat ω hω
  have h2 := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h3 := GlobalTheory.T.transportedWeilDatum_keeps_admissible_forms D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h4 := GlobalTheory.T.transportedWeilDatum_isUnitary_adelicSchwartz D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h5 := GlobalTheory.T.continuous_transported_weilDatum_adelicSchwartz D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h6 := GlobalTheory.T.exists_doubledWeil_blockEmbedding_acts_on_first_boxFactor D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have h7 := GlobalTheory.T.exists_doubled_schrodingerModel_transposed_siegelRule D B.ψ hψ S T χW χX hcW hcX rS rT X.J Y.J (-1) eA eB _ Mo.co hMo.rat ω hω om₀ hom₀
  have hsp : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) B.ψ Mo.co
      (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) om₀ := ⟨⟨h2.1, h2.2, h3⟩, h4, h5⟩
  have hw₀ : Mo.IsWeil B.ψ χX χW om₀ :=
    ⟨⟨isUSplitting_inr hsp, h6⟩, ⟨transD _ Mo.co, transD_e Mo.co, isUSplitting_inl hsp, h7⟩, h5⟩
  obtain ⟨h1X, h2X, -⟩ := GlobalTheory.T.hermitianSelfDualLatticeSpace_form_hermitian_nondeg_unimodular D B hB T.rank X r s hX
  obtain ⟨hdY, -⟩ := GlobalTheory.T.skewHermitian_neg_traceZero_inv_hermitian_unimodular D B hB S.rank Y r' s' hY
  have hdX : X.J.det ≠ 0 := by
    have := det_ne_zero_of_nondeg D X.Jᵀ h2X
    rwa [Matrix.det_transpose] at this
  have huniq := GlobalTheory.T.adelicWeilRep_schrodingerModel_unique D.host.F D.host.E D.sp.cm.sig hB.cm T.rank S.rank X Y Mo B.ψ χX χW hB.std hX.herm hdX
    hY.skew hdY.ne_zero om om₀ hom hw₀
  refine ⟨ω, hω, fun a b g h ha hb Φ hΦ => ?_⟩
  rw [huniq (a, b) Φ hΦ]
  exact hom₀ a b g h ha hb Φ hΦ

theorem thetaTr_zero (D : D7) {W : Type} [AddCommGroup W] [Module (AF D.host.F) W] {Bf : W → W → AF D.host.F}
    {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux Bf κ) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (κ → AF D.host.F) → ℂ) :
    thetaTr D.host.F d ψ Φ 0 = GlobalTheory.WeilM.thetaSum D.host.F Φ := by
  have : GlobalTheory.WeilM.schr ψ (0 : (κ → AF D.host.F) × (κ → AF D.host.F)) Φ = Φ := by
    funext x
    simp [GlobalTheory.WeilM.schr]
  simp [thetaTr, GlobalTheory.WeilM.Darboux.rho, this]

theorem exists_theta_eq (D : D7) (B : Base D.host.F D.host.E) (hB : B.IsGood D.sp.cm.sig)
    (S T : HSp D) (X : Spc D.host.F D.host.E T.rank) (Y : Spc D.host.F D.host.E S.rank) (r s r' s' : ℕ)
    (hX : X.IsHerm D.sp.cm.sig B r s) (hY : Y.IsSkew D.sp.cm.sig B r' s')
    (eA : X.J = T.gramᵀ)
    (eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • incM D.host.F Y.J = incM D.host.F (D.host.xi0 • S.gram⁻¹))
    (Mo : Model D.sp.cm.sig X Y) (hMo : Mo.IsGood B.ψ) (χX χW : Chr D.host.F D.host.E)
    (hcX : GlobalTheory.LFun.IsHecke D.host.F D.host.E χX) (hcW : GlobalTheory.LFun.IsHecke D.host.F D.host.E χW)
    (rX : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χX T.rank)
    (rW : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χW S.rank)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig X Y) (hom : Mo.IsWeil B.ψ χX χW om) :
    ∃ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
      Formalism.IndefR.Datum.IsWeilDatumO B.ψ S T χW χX ω ∧ IsTransport B.ψ Mo.co ω om ∧
      ∀ (a : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig X.J) (b : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Y.J) (g : GA D S) (h : GA D T),
        mt T h = a.1.1 → mt S g = (b⁻¹).1.1ᵀ → ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin T.rank × Fin S.rank),
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ a b = ω (g, h) (thetaTr D.host.F Mo.co B.ψ Φ) 0 := by
  obtain ⟨ω, hω, htr⟩ := exists_isTransport D B hB S T X Y r s r' s' hX hY eA eB Mo hMo χX χW hcX hcW rX rW om hom
  refine ⟨ω, hω, htr, fun a b g h ha hb Φ hΦ => ?_⟩
  rw [← (htr a b g h ha hb Φ hΦ).2, thetaTr_zero]
  rfl

end GlobalTheory.WeilBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFormTwoSmulAndKerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diag_form_two_smul_and_ker_alt : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ)) (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q → (∀ z, e z = 1 ↔ z ∈ Q.range) → (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) → ∃ E₁ : LinearMap.BilinForm ℤ La, EF = (2 : ℤ) • E₁ ∧ ∀ (k : ℕ) (a : La), 0 < k → ((∀ y, (k : ℤ) ∣ E₁ a y) ↔ ∃ t : (P.pull (lift (snd A (Over.mk (𝟙 (Sp ℂ))) ≫ e ((k : ℂ)⁻¹ • Q a)) (fst A (Over.mk (𝟙 (Sp ℂ))))).left).Gen, t.IsGen) := by
  first | exact @GlobalTheory.SymBirig.diag_form_two_smul_and_ker | exact GlobalTheory.SymBirig.diag_form_two_smul_and_ker | (intros; apply GlobalTheory.SymBirig.diag_form_two_smul_and_ker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalAppellHumbertRealMult
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRiem

theorem riemannForm_eq_two_trace : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ (e j (a : F) : ℂ) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (h : Fin (Module.finrank ℚ F) → ℝ) (χ : u.Λ → ℂ), u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ →
    ∃ P : u.Λ → u.Λ → F, (∀ l l' : u.Λ, P l l' = -P l' l) ∧ (∀ l₁ l₂ l' : u.Λ, P (l₁ + l₂) l' = P l₁ l' + P l₂ l') ∧
      (∀ (a : 𝓞 F) (l l' al : u.Λ), (al : Fin (Module.finrank ℚ F) → ℂ) = (fun j ↦ (e j (a : F) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) →
        P al l' = (a : F) * P l l') ∧
      (∀ l l' : u.Λ, (∑ j, (h j : ℂ) * ((l : Fin (Module.finrank ℚ F) → ℂ) j * starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im =
        2 * ((Algebra.trace ℚ F ((c : F) * P l l') : ℚ) : ℝ)) ∧
      (∀ l l' : u.Λ, P l l' ∈ dualLat 𝔠) ∧
      (∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 F) {t | ∃ l l' : u.Λ, t = P l l'}) := by
  intro F _ _ _ 𝔠 X c hc u e hu h χ hAH
  have hΛa : ∀ (a : 𝓞 F) (l : Fin (Module.finrank ℚ F) → ℂ), l ∈ u.Λ →
      (fun j ↦ (e j (a : F) : ℂ) * l j) ∈ u.Λ := by
    intro a l hl
    rw [← u.ker, hu, (u.ker l).2 hl]
    haveI := X.rm.hom a
    simp
  have hpos : ∀ j, 0 < h j := by
    intro j
    have := hAH.2.1 (Pi.single j 1) (by simp)
    simpa [Matrix.mulVec_diagonal, dotProduct, Pi.single_apply] using this
  obtain ⟨P, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.lattice_real_multiplication_integral F 𝔠 c hc u.Λ e h hΛa (GlobalTheory.T.appell_humbert_diagonal_real F 𝔠 X c hc u e hu h χ hAH)
  exact ⟨P, h1, h2, h3, h4, h5, GlobalTheory.T.lattice_real_multiplication_span F 𝔠 c hc u.Λ e h hΛa u.discrete u.full hpos P h1 h2 h3 h4 h5
    (fun x hx a ha => GlobalTheory.T.appell_humbert_diagonal_real_dual F 𝔠 X c hc u e hu h χ hAH x hx a ha)⟩

end GlobalTheory.TorusRiem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyAddOrdGtNegOneLogResolution
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Discrepancy.CoeffPlaces

variable {Z : Scheme.{0}} [IsIntegral Z]

theorem supp_neg_le' (D : CartierDiv Z) : (-D).supp ≤ D.supp := fun x hx h =>
  hx (by simpa using h.neg)

theorem supp_nsmul_le' (D : CartierDiv Z) (r : ℕ) : (r • D).supp ≤ D.supp := by
  induction r with
  | zero => rw [zero_smul, CartierDiv.supp_eq_bot_iff.2 rfl]; exact bot_le
  | succ r ih => rw [succ_nsmul]; exact (CartierDiv.supp_add_le _ _).trans (sup_le ih le_rfl)

variable [IsLocallyNoetherian Z]

theorem mult_zero'' (z : Z) : (0 : CartierDiv Z).mult z = 0 := by
  have h₀ := CartierDiv.mult_add (0 : CartierDiv Z) 0 z
  rw [add_zero] at h₀
  omega

theorem mult_nsmul''' (E : CartierDiv Z) (r : ℕ) (z : Z) : (r • E).mult z = r * E.mult z := by
  induction r with
  | zero => rw [zero_nsmul, mult_zero'']; simp
  | succ r ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem mult_sub'' (D E : CartierDiv Z) (z : Z) : (D - E).mult z = D.mult z - E.mult z := by
  have h := CartierDiv.mult_add (D - E) E z
  rw [sub_add_cancel] at h
  omega

theorem ord_nonneg_of_regAt' {f : Z.functionField} {z : Z} (hf : RegAt z f) (h0 : f ≠ 0) :
    0 ≤ Scheme.ord f z := by
  by_cases hz : Order.coheight z = 1
  · obtain ⟨a, rfl⟩ := hf
    have ha : a ≠ 0 := fun h => h0 (by rw [h, map_zero])
    rw [ord_algebraMap hz ha]
    exact Nat.cast_nonneg _
  · exact (Scheme.ord_eq_zero_of_coheight_neq_one hz _).ge

theorem regAt_functionFieldMap' {X : Scheme.{0}} [IsIntegral X] (q : Z ⟶ X) [IsDominant q] (y : Z)
    {f : X.functionField} (h : RegAt (q y) f) : RegAt y (functionFieldMap q f) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨q.stalkMap y a, (functionFieldMap_algebraMap q y a).symm⟩

end GlobalTheory.Discrepancy.CoeffPlaces

open GlobalTheory.Discrepancy.CoeffPlaces in

theorem GlobalTheory.Discrepancy.neg_one_lt_discrep_add_ord_of_logRes : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (g f : X.functionFieldˣ) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (y : X) (σ : Y), η ≠ 0 → 0 < m → IsLogRes p n η m (CartierDiv.principal g) s K B → (∀ y', s y' ∈ (CartierDiv.principal f).supp → y' ∈ B) → RegAt y (f : X.functionField) → Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) σ = 1 → (pullCart s (CartierDiv.principal g) - m • K).mult σ = m → (∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s (CartierDiv.principal g) - m • K).mult v < m) → ∀ E : DivOver p, E.Through y → -1 < discrep E η m g + E.ord f := by
  intro X _ _ p n hproj _ η m g f Y _ _ s _ K B y σ hη hm hres hfB hfy hσ1 hσm hlt E hE
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hproj
  haveI : IsProper (s ≫ p) := GlobalTheory.CommonModel.isProper_of_isProjOver hres.proj
  haveI : IsProper s := IsProper.of_comp s p
  haveI := hres.smooth
  obtain ⟨E', hE'E⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational ℂ X Y p s hres.bir E
  obtain ⟨y', rfl, hE'⟩ := GlobalTheory.T.divisor_center_proper_lift ℂ X Y p s hres.bir inferInstance E' E hE'E _ hE
  have hη' : EtaleKlt.ratPull p s n η ≠ 0 := fun h0 =>
    hη ((GlobalTheory.T.rationalTopFormPullback_bijective_birational ℂ X Y p s hres.bir n).1 (h0.trans (map_zero _).symm))
  set F := pullCart s (CartierDiv.principal f) with hFdef
  set G := pullCart s (CartierDiv.principal g) with hGdef
  have hFsupp : F.supp ≤ B := fun v hv => hfB v ((GlobalTheory.T.cartierDivisorPullback_support_and_effective X Y s _).1 v hv)
  have e : G - m • F - m • K = (G - m • K) + -(m • F) := by abel
  have hsupp : (G - m • F - m • K).supp ≤ B := by
    rw [e]
    exact (CartierDiv.supp_add_le _ _).trans
      (sup_le hres.supp ((supp_neg_le' _).trans ((supp_nsmul_le' _ _).trans hFsupp)))
  have hFm (w : Y) : F.mult w = Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) w :=
    (isEqn_pullCart s (CartierDiv.isEqn_principal f (s w))).mult_eq
  have hEqn : (G - m • F).IsEqn y' (fnPull s g / fnPull s f ^ m) :=
    (isEqn_pullCart s (CartierDiv.isEqn_principal g (s y'))).sub
      ((isEqn_pullCart s (CartierDiv.isEqn_principal f (s y'))).nsmul m)
  have hmul (w : Y) : (G - m • F - m • K).mult w = (G - m • K).mult w - m * F.mult w := by
    rw [mult_sub'', mult_sub'', mult_sub'', mult_nsmul''', mult_nsmul''']; ring
  have hlt' : ∀ w, w ⤳ y' → (G - m • F - m • K).mult w < m := by
    intro w hw
    rw [hmul, hFm]
    by_cases hwσ : w = σ
    · subst hwσ
      rw [hσm, hσ1]
      simp only [mul_one, sub_self]
      exact_mod_cast hm
    · have hsw : s w ⤳ s y' := hw.map s.continuous
      have h0 : 0 ≤ Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) w :=
        ord_nonneg_of_regAt' (regAt_functionFieldMap' s w (regAt_of_specializes hsw hfy))
          (Units.ne_zero _)
      have h1 := hlt w hwσ hsw
      have h2 : (0 : ℤ) ≤ m * Scheme.ord ((fnPull s f : Y.functionFieldˣ) : Y.functionField) w :=
        mul_nonneg (Int.natCast_nonneg m) h0
      linarith
  have hcrit := (GlobalTheory.T.klt_of_snc_coefficients ℂ Y (s ≫ p) n (EtaleKlt.ratPull p s n η) hη' K (G - m • F) m B hm
    hres.div hres.snc hsupp y' _ hEqn E' hE').1 hlt'
  have hd : discrep E' (EtaleKlt.ratPull p s n η) m (fnPull s g / fnPull s f ^ m) =
      discrep E η m g + E.ord f := by
    simp only [discrep]
    rw [GlobalTheory.T.form_order_birational_pullback ℂ X Y p s hres.bir E' E hE'E n η hη, div_eq_mul_inv (fnPull s g), E'.ord_mul, E'.ord_inv,
      E'.ord_pow, GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p s hres.bir E' E hE'E g,
      GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p s hres.bir E' E hE'E f]
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    push_cast
    field_simp
    ring
  rw [← hd]
  exact hcrit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionPointCharactersGaloisFixedOfRationalBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisionPoint_characters_galoisFixed_of_rational_basePoint : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p₀ p : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → (∃ b : TF (R := R) (FractionRing R) ⟶ D'.toPre.P.A, p.g.b.left = spMap (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫ b.left) → ∀ χ : D'.toPre.X, LB.Gen.Corr D'.toPre.P.L _ _ _ _ (p.g.s χ) (LB.pullGen D'.toPre.P.L _ _ (p.g.s χ) (spMap σ.toAlgHom.toRingHom)) := by
  first | exact @GlobalTheory.Mum.RatChar.charFixed | exact GlobalTheory.Mum.RatChar.charFixed | (intros; apply GlobalTheory.Mum.RatChar.charFixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorProofsFactStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisorProofs_fact : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)),
    ∃ (c₀ : 𝔠.elt) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 ∧
      (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 (FR E)), n.Coprime l ∧ n • c = t • c₀) ∧
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ((2 : R) • ψ₀) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (Submodule.map eH.toLinearMap (Fil X₀.A)) (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) ∧
      ∀ i (g : Fin n → R), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) = Submodule.span R {g} →
        ∃ r : Rˣ, ∀ x, ψ₀ (eH.symm g) x = (r : R) * e i (hL.toLie X₀.rm x) := by
  first | exact @GlobalTheory.LatModel.cmLattice_of_model | exact GlobalTheory.LatModel.cmLattice_of_model | (intros; apply GlobalTheory.LatModel.cmLattice_of_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChartProductAtClosedPointClosedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_open_nbhd_isPullback_at_closedPoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (E : Emb M.π G') (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), IsSeparated b → LocallyOfFiniteType b → IsProper a → (∀ V : P'.Opens, Function.Bijective (a.app V).hom) → a ≫ b = X.ι ≫ E.f → Function.Bijective M.π.appTop.hom → Surjective M.π → ∀ x : P', IsClosed ({x} : Set P') → (b ≫ PSpace.str R E.N) x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X.toScheme), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ X.ι ≫ E.H.ι ≫ G'.hom = p' ≫ X.ι ≫ E.H.ι ≫ G'.hom → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ M.S), Set.range ξ = {x} → ξ ≫ b ≫ PSpace.str R E.N = s ≫ M.π → ∃ p : Sp Ω ⟶ X.toScheme, p ≫ a = ξ ∧ p ≫ X.ι ≫ E.H.ι ≫ G'.hom = s) → ∃ V : P'.Opens, x ∈ V ∧ Smooth (V.ι ≫ b ≫ PSpace.str R E.N) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (V.ι ≫ b ≫ PSpace.str R E.N) M.π := by
  first | exact @GlobalTheory.Mum.etale_chart_at_closed_point | exact GlobalTheory.Mum.etale_chart_at_closed_point | (intros; apply GlobalTheory.Mum.etale_chart_at_closed_point <;> assumption)
end

