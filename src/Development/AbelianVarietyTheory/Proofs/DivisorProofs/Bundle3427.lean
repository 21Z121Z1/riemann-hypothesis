import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3396
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3400
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3410
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValidGaugeImpliesValid
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3406
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3378
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3407
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2600
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3393
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2689
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3408
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1736
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1732
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudExtensionInvariantFieldCoeffsUnique
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
open GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.HxUniq

open GlobalTheory.KS (rsT_self eq_of_rsT_eq)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem evalPt_lieExp_comb {m : ℕ} (u : Fin m → TanM (𝟙 (Sp R)) G) (dd : Fin m → Fld G.left)
    (hd : ∀ i, IsInv G (u i) (dd i)) (B : Type) [CommRing B] [Algebra R B] (e : Fin m → B)
    (he : ∀ i j, e i * e j = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens)
    (h : ⊤ ≤ z.left ⁻¹ᵁ O) :
    ∃ h' : ⊤ ≤ (GlobalTheory.SqZero.lieExp (fun i => GlobalTheory.VertCoeffRing.tvE (u i)) e (fun i => he i i) * z).left ⁻¹ᵁ O, ∀ f,
      evalPt _ O h' f = evalPt z.left O h f + ∑ i, e i * evalPt z.left O h (dd i O f) := by
  induction m with
  | zero =>
    have : GlobalTheory.SqZero.lieExp (fun i => GlobalTheory.VertCoeffRing.tvE (u i)) e (fun i => he i i) * z = z := by
      simp [GlobalTheory.SqZero.lieExp]
    rw [this]
    exact ⟨h, fun f => by simp⟩
  | succ m ih =>
    obtain ⟨h₁, H₁⟩ := ih (fun i => u i.succ) (fun i => dd i.succ) (fun i => hd i.succ) (fun i => e i.succ)
      (fun i j => he _ _)
    obtain ⟨h₂, H₂⟩ := GlobalTheory.VertCoeffRing.evalPt_tvE_mul (hd 0) (e 0) (he 0 0) _ O h₁
    have : GlobalTheory.SqZero.lieExp (fun i => GlobalTheory.VertCoeffRing.tvE (u i)) e (fun i => he i i) * z =
        (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo R (e 0) (he 0 0)) ≫ GlobalTheory.VertCoeffRing.tvE (u 0)) *
          (GlobalTheory.SqZero.lieExp (fun i => GlobalTheory.VertCoeffRing.tvE (u i.succ)) (fun i => e i.succ)
            (fun i => he i.succ i.succ) * z) := by
      rw [GlobalTheory.SqZero.lieExp, GlobalTheory.SqZero.lieExp, Fin.prod_univ_succ, _root_.mul_assoc]
    rw [this]
    refine ⟨h₂, fun f => ?_⟩
    rw [H₂, H₁, H₁, Fin.sum_univ_succ, mul_add, Finset.mul_sum]
    simp only [← _root_.mul_assoc, he, zero_mul, Finset.sum_const_zero]
    ring

theorem coeff_eq_zero [Smooth G.hom] {n : ℕ} (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G))
    (dd : Fin n → Fld G.left) (hd : ∀ a, IsInv G (v a) (dd a)) (W : G.left.Opens) (c : Fin n → Γ(G.left, W))
    (hc : ∀ Wo : G.left.Opens, Wo ≤ W → ∀ f, ∑ a, rsT (c a) Wo * dd a Wo f = 0) (a : Fin n) : c a = 0 := by
  let J := {V : G.left.Opens // IsAffineOpen V ∧ V ≤ W}
  have hcov : W ≤ ⨆ k : J, k.1 := by
    intro x hx
    obtain ⟨V, hV, hxV, hVW⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (G.left.isBasis_affineOpens)) hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV, hVW⟩, hxV⟩
  refine eq_of_rsT_eq (fun k : J => k.1) (fun k => k.2.2) hcov _ _ fun k => ?_
  rw [GlobalTheory.KS.rsT_zero]
  obtain ⟨V, hV, hVW⟩ := k
  have hu := GlobalTheory.VertCoeffRing.existsUnique_coeff_affine_ring (fun a => GlobalTheory.VertCoeffRing.tvE (v a))
    (GlobalTheory.VertCoeffRing.isLieBasis_tvE v) dd
    (fun B _ _ e he z O h => evalPt_lieExp_comb (fun a => v a) dd hd B e he z O h) V V hV hV le_rfl
    (fun _ => 0) (fun _ _ => by simp) (fun _ _ => by simp) (fun _ => rfl)
  have h1 : ∀ f, (fun _ => (0 : Γ(G.left, V))) f = ∑ a, (fun a => rsT (c a) V) a * rsT (dd a V f) V := by
    intro f
    simp only [rsT_self]
    exact (hc V hVW f).symm
  have h0 : ∀ f, (fun _ => (0 : Γ(G.left, V))) f = ∑ a, (fun _ => (0 : Γ(G.left, V))) a * rsT (dd a V f) V := by
    intro f; simp
  exact congrFun (hu.unique h1 h0) a

end GlobalTheory.HxUniq

theorem GlobalTheory.HxUniq.raynaud_coeff_eq_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (W : Y.H.left.Opens) (c : Fin n → Γ(Y.H.left, W)), (∀ Wo : Y.H.left.Opens, Wo ≤ W → ∀ f, ∑ a, rsT (c a) Wo * dd a Wo f = 0) → ∀ a, c a = 0 := by
  intro R _ _ Q O _ _ _ oa Y n v dd hd W c hc a
  have : Smooth Y.H.hom := (GlobalTheory.isSemiAbelian_of_isGt _ _ _ Y.isGt).smooth
  exact GlobalTheory.HxUniq.coeff_eq_zero v dd hd W c hc a
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudFourierTermChartRestrictionIsWeightStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.raynaudFourierTerm_chartRestriction_isWeight : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (k : ℕ) (α : Q.X) (σ : Q.SecB k α) (τ : SecM Y.q.left Q.P.L k), IsTerm Y k α σ τ → ∀ (j : Q.P.L.ι) (W : Y.H.left.Opens), (∃ V : Q.P.A.left.Opens, W = Y.q.left ⁻¹ᵁ V) → W ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j → IsWt Y α W (rsT (τ.f fun _ => j) W) := by
  first | exact @GlobalTheory.HeatMod.isWt_fourierTerm | exact GlobalTheory.HeatMod.isWt_fourierTerm | (intros; apply GlobalTheory.HeatMod.isWt_fourierTerm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealDataWeightVectorFamilyCoreStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_data_weight_vector_family_core : Hypotheses3 → GlobalTheory.Published.RegularisedSiegelWeilFirstTerm → GlobalTheory.Published.HeckeLPartialContinuation → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), ∀ (L : SizeData₂ D), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' D L) → TiesB R F → TiesG T R κ v₀ O → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → PrimRows3 R F ∧ A3.fam3.TypesSep3 ∧ ∃ tr, R.TrISem F tr ∧ GlobalTheory.Hk3.TrISepWith A3 tr := by
  first | exact @GlobalTheory.Closing3.primRows3_typesSep3 | exact GlobalTheory.Closing3.primRows3_typesSep3 | (intros; apply GlobalTheory.Closing3.primRows3_typesSep3 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularBaseRankTwoMetricFamilyStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_base_rank_two_metric_family : ArCalc → ∃ G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ, Homog G ∧
    ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) →
    ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2), IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q) (Φ : MvPolynomial (Fin 5) ℝ →ₗ[ℝ] ℝ) (Ψ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ),
      IsArFun (fam5 π w H flB fl A) (d + 1) Φ →
      IsGeoFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Ψ →
      ∀ a b : ℤ, Φ (onLine d a b - onBase d a b) = Ψ (G (d + 1) a b) := by
  first | exact @GlobalTheory.CovTest.SwapLine.core_exists | exact GlobalTheory.CovTest.SwapLine.core_exists | (intros; apply GlobalTheory.CovTest.SwapLine.core_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentingSchemeOfFiniteSurjectiveLift
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.Assemble

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem fam_ev {U Y : Over S} {M : LB (A ⊗ U).left} (h : Fam A M) (u : Y ⟶ U) :
    Fam A (ev M (fst A Y) (snd A Y ≫ u)) := by
  have hN : (ev M (fst A Y) (snd A Y ≫ u)).IsLB := pull_isLB h.isLB _
  refine ⟨hN, (isAdditive_iff hN).2 fun Z a a' t ↦ ?_⟩
  simp only [evc_ev h.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.add Z a a' _

omit [GrpObj A] in

theorem same_comp {T U Y Z : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    {y : Y ⟶ T} {u : Y ⟶ U} (h : Same A N M y u) (z : Z ⟶ Y) :
    evc hN (fst A Z) (snd A Z ≫ z ≫ y) = evc hM (fst A Z) (snd A Z ≫ z ≫ u) := by
  have e := congrArg (CechPic.pull (lift (fst A Z) (snd A Z ≫ z)).left) ((same_iff hN hM y u).1 h)
  simpa only [pull_evc, lift_fst, lift_snd_assoc, Category.assoc] using e

theorem exists_lift {S' : Over S} [IsFinite S'.hom] [Surjective S'.hom] {K : Type} [Field K] [IsAlgClosed K]
    (s : Sp K ⟶ S) : Nonempty (Over.mk s ⟶ S') := by
  obtain ⟨t, ht⟩ := exists_lift_pt S'.hom s
  exact ⟨Over.homMk t ht⟩

theorem fibInj {B S' U : Over S} [IsFinite S'.hom] [Surjective S'.hom] {b : B ⟶ S'} {P : LB (A ⊗ B).left}
    (hP : Rep A b P) {M : LB (A ⊗ U).left} (hM : Fam A M) {j : U ⊗ S' ⟶ B} (hj : j ≫ b = snd U S')
    [IsOpenImmersion j.left] (h : Same A M P (fst U S') j) : FibInj A M := by
  intro K _ _ s Y y u u' huu
  obtain ⟨t⟩ := exists_lift (S' := S') s
  have : Mono j := (Over.forget S).mono_of_mono_map (show Mono j.left from inferInstance)
  have k : ∀ v : Y ⟶ U, evc hM.isLB (fst A Y) (snd A Y ≫ v) =
      evc hP.fam.isLB (fst A Y) (snd A Y ≫ lift v (y ≫ t) ≫ j) := fun v ↦ by
    simpa only [lift_fst] using same_comp hM.isLB hP.fam.isLB h (lift v (y ≫ t))
  have hN := fam_ev hM u
  have e : lift u (y ≫ t) ≫ j = lift u' (y ≫ t) ≫ j := by
    refine (hP.univ Y (y ≫ t) _ hN).unique ⟨by rw [Category.assoc, hj, lift_snd], ?_⟩
      ⟨by rw [Category.assoc, hj, lift_snd], ?_⟩
    · exact (cls_eq_iff hN.isLB (pull_isLB hP.fam.isLB _)).1 (k u)
    · exact (cls_eq_iff hN.isLB (pull_isLB hP.fam.isLB _)).1
        (((same_iff hM.isLB hM.isLB u u').1 huu).trans (k u'))
  have e' := congrArg (· ≫ fst U S') ((cancel_mono j).1 e)
  simpa only [lift_fst] using e'

theorem exists_point {B S' U : Over S} {P : LB (A ⊗ B).left} (hP : P.IsLB) {M : LB (A ⊗ U).left} (hM : M.IsLB)
    {j : U ⊗ S' ⟶ B} [IsOpenImmersion j.left] (h : Same A M P (fst U S') j) {K : Type} [Field K]
    {s : Sp K ⟶ S} {N : LB (A ⊗ Over.mk s).left} (hN : N.IsLB) (x : Over.mk s ⟶ B)
    (hx : LBIso N (ev P (fst A _) (snd A _ ≫ x))) (hr : x.left (default : PrimeSpectrum K) ∈ Set.range j.left) :
    ∃ u : Over.mk s ⟶ U, Same A N M (𝟙 _) u := by
  have hr' : Set.range x.left ⊆ Set.range j.left := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim (α := PrimeSpectrum K) z default]
  have fac := IsOpenImmersion.lift_fac j.left x.left hr'
  let v : Over.mk s ⟶ U ⊗ S' := Over.homMk (IsOpenImmersion.lift j.left x.left hr') (by
    rw [← Over.w j, ← Category.assoc, fac]; exact Over.w x)
  have hv : v ≫ j = x := Over.OverMorphism.ext fac
  refine ⟨v ≫ fst U S', (same_id_iff hN hM _).2 ((cls_eq_iff hN (pull_isLB hM _)).1 ?_)⟩
  rw [(cls_eq_iff hN (pull_isLB hP _)).2 hx, cls_ev hP, cls_ev hM, same_comp hM hP h v, hv]

theorem isPullback_prod (X Y : Over S) : IsPullback (fst X Y) (snd X Y) (toUnit X) (toUnit Y) :=
  ⟨⟨toUnit_unique _ _⟩, ⟨PullbackCone.IsLimit.mk _ (fun c ↦ lift c.fst c.snd) (fun _ ↦ lift_fst _ _)
    (fun _ ↦ lift_snd _ _) fun c m h₁ h₂ ↦ by ext <;> simp [h₁, h₂]⟩⟩

theorem toUnit_left (X : Over S) : (toUnit X).left = X.hom :=
  (Category.comp_id _).symm.trans (Over.w (toUnit X))

end GlobalTheory.DualCon.Assemble

namespace GlobalTheory.DualCon
open Assemble

theorem hasRep_of_liftAt (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (B S' : Over (Sp R)) (b : B ⟶ S')
    (P : LB (A ⊗ B).left) (hf : IsFinite S'.hom) (hs : Surjective S'.hom) (hP : Rep A b P)
    (hb : GlobalTheory.DualCon.Good g b.left) (hl : ∀ x : B.left, LiftAt A g b P x) : HasRep A g (𝟙_ _) := by
  choose U M j hM hU hj ho hx h using hl
  have hc : ∀ x, IsChart A (M x) := fun x ↦
    GlobalTheory.T.openChart_of_smoothFamily_geomFibreInjective R A g hA hg (U x) (M x) (hU x) (hM x) (fibInj hP (hM x) (hj x) (h x))
  obtain ⟨B₀, P₀, i, hP₀, hi, hcov, -⟩ := GlobalTheory.T.glue_openCharts_additiveFamilies_representing (Sp R) A hA B.left U M hc (by
    intro K _ _ s N hN
    obtain ⟨t⟩ := exists_lift (S' := S') s
    obtain ⟨x, ⟨-, hxN⟩, -⟩ := hP.univ _ t N hN
    exact ⟨_, exists_point hP.fam.isLB (hM _).isLB (h _) hN.isLB x hxN (hx _)⟩)
  have hsm : SmoothOfRelativeDimension g B₀.hom := by
    have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension g)
      (Scheme.Cover.mkOfCovers B.left (fun x ↦ (U x).left) (fun x ↦ (i x).left) hcov hi) fun x ↦ ?_
    have e : (i x).left ≫ B₀.hom = (U x).hom := Over.w _
    exact (congrArg (@SmoothOfRelativeDimension g _ _) e).mpr (hU x)
  have hpb := isPullback_prod B₀ S'
  obtain ⟨e, he, -⟩ := rep_unique (Sp R) A B (B₀ ⊗ S') S' b P _ _ hP
    (GlobalTheory.T.rep_ev_of_isPullback (Sp R) A B₀ _ S' _ _ P₀ _ _ _ hP₀ hpb)
  have hpb' : IsPullback (e.hom ≫ fst B₀ S') b (toUnit B₀) (toUnit S') :=
    hpb.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp [← he]) (by simp) (by simp)
  refine ⟨B₀, toUnit B₀, P₀, hP₀, GlobalTheory.T.properSmoothGeomConnected_descend_finite_surjective _ _ _ _ _ _ _ _ g (hpb'.map (Over.forget _)) ?_ ?_ ?_ hb⟩
  · exact (congrArg (@IsFinite _ _) (toUnit_left S')).mpr hf
  · exact (congrArg (@Surjective _ _) (toUnit_left S')).mpr hs
  · exact (congrArg (@SmoothOfRelativeDimension g _ _) (toUnit_left B₀)).mpr hsm

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataUniformiseFiniteExtension
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem samePol_unif_finExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ : DegData R (maximalIdeal R)), ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ : DegData R' (maximalIdeal R')) (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (U₁ : Unif (maximalIdeal R') D₁ A₁ G₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G U.LG.L).pull β₂) := by
  intro R _ _ _ hR D₀ D A G _ _ hG U hS
  have := hR.2
  obtain ⟨a, P, A₂, gen₂, -, hPa, hEv, hgen, hgenL, hcmp⟩ := GlobalTheory.T.exists_orderTwo_section_evenTranslate_samePolarisedData R hR D₀ D A G hG U hS
  obtain ⟨D₂, U₂, hLG, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocal_evenOnTorus R hR G P hG hEv A₂ gen₂ hgen hgenL
  obtain ⟨R', _, _, _, ρ, D₁, hfin, hloc, ⟨hD₀⟩, hmove⟩ := hcmp D₂ U₂ hLG
  obtain ⟨hL, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨D', hD', A', U', hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL.polBaseChange h4.unifBaseChange h5.psiOnExists
    hR.1 hfin.1 ρ hfin.2.1 (map_maximalIdeal_le ρ) hG U₂
  obtain ⟨hiso⟩ := hmove D' ⟨hD'⟩
  have hG₁ : IsSemiAbelian ((Over.pullback (specOf ρ)).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨U₁, hU₁, -⟩ := (GlobalTheory.T.uniformisation_transfer_isPullDeg_id R' (maximalIdeal R') hfin.1 D₁ D' ⟨hiso⟩ A' _ hG₁).1 U'
  have hb : (Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ) =
      pullback.fst G.hom (specOf ρ) := Category.id_comp _
  have hpb : IsGrpPullback ((Over.pullback (specOf ρ)).obj G) G (spMap ρ)
      ((Iso.refl ((Over.pullback (specOf ρ)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ρ)) := by
    refine (isGrpPullback_pullback G (spMap ρ)).congr ?_ hb.symm
    rfl
  obtain ⟨β₂, hsq, hlam⟩ := GlobalTheory.T.exists_mumfordBundle_pullback_grpPullback (Sp R) (Sp R') (spMap ρ) G _ _ hpb
  have hLU : (abelian₂ G U.LG.L).IsLB := DVR.linComb_isLB _ U.LG.isLB _ _
  have h2 : LBIso (abelian₂ G U₂.LG.L) (abelian₂ G U.LG.L) := by
    rw [hLG]
    exact GlobalTheory.T.mumfordBundle_translate_iso_cubical (Sp R) G U.LG U.cubG a P.L.L P.L.isLB hPa
  have h3 : LBIso (abelian₂ G U₂.LG.L) ((abelian₂ G U.LG.L).pull (𝟙 _)) :=
    LBIso.trans (DVR.linComb_isLB _ U₂.LG.isLB _ _) hLU (pull_isLB hLU _) h2
      ⟨GlobalTheory.PolDeg.Wit.idPull _, GlobalTheory.PolDeg.Wit.idPull_isGen hLU⟩
  have h4' := hlam U₂.LG.L U'.LG.L _ (abelian₂ G U.LG.L) (𝟙 _) U₂.LG.isLB U'.LG.isLB hLU
    ⟨hP.lg.choose, hP.lg.choose_spec.1⟩ h3
  rw [Category.comp_id] at h4'
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, D₁, _, inferInstance, inferInstance, _, β₂, A', U₁, hfin,
    ⟨hD₀⟩, hpb, hsq, ?_⟩
  rw [hU₁]
  exact h4'

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondOrderSymbolBracketRescaleByUnitPowStatement
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
theorem _root_.GlobalTheory.T.secondOrderSymbol_bracket_rescale_by_unit_pow : ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (n : ℕ) (δ₀ : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Λ : Matrix (Fin n) (Fin n) (FractionRing Ω)) (q b c : FractionRing Ω) (k : ℕ), q ≠ 0 → (k : FractionRing Ω) * (q ^ k * b) * ((q ^ k * b) * δ₀ (q ^ k * c) - (q ^ k * c) * δ₀ (q ^ k * b)) - ∑ a, ∑ e, Λ a e * δL a (q ^ k * b) * ((q ^ k * b) * δL e (q ^ k * c) - (q ^ k * c) * δL e (q ^ k * b)) = q ^ (3 * k) * ((k : FractionRing Ω) * b * (b * (δ₀ c - ∑ a, ∑ e, Λ a e * δL a q / q * δL e c) - c * (δ₀ b - ∑ a, ∑ e, Λ a e * δL a q / q * δL e b)) - ∑ a, ∑ e, Λ a e * δL a b * (b * δL e c - c * δL e b)) := by
  first | exact @GlobalTheory.Heat.bracket_symbol_rescale_twist | exact GlobalTheory.Heat.bracket_symbol_rescale_twist | (intros; apply GlobalTheory.Heat.bracket_symbol_rescale_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPowerValueChartChangeByTransitionPowStatement
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
theorem _root_.GlobalTheory.T.sectionPowerValue_chart_change_by_transition_pow : ∀ (X : Scheme.{0}) (L : LB X) (k : ℕ) (σ : SecM (𝟙 X) L k) (F : Type) [Field F] (ξ : Sp F ⟶ X) (j j' : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j → ⊤ ≤ ξ ⁻¹ᵁ L.U j' → valR ξ _ (σ.f fun _ => j) = valR ξ (L.U j ⊓ L.U j') (L.g j j').val ^ k * valR ξ _ (σ.f fun _ => j') := by
  first | exact @GlobalTheory.SecValLC.secM_valR_transition | exact GlobalTheory.SecValLC.secM_valR_transition | (intros; apply GlobalTheory.SecValLC.secM_valR_transition <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsDescendAlongFlatMapToLocalDomainStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_descend_along_flat_map_to_localDomain : ∀ (X : Scheme.{0}) (U : X.affineOpens) (W : X.Opens) (hWU : W ≤ U.1), IsCompact (W : Set X) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ρ : Γ(X, U.1) →+* R), ρ.Flat → ∀ mm : Ideal Γ(X, U.1), (maximalIdeal R).comap ρ = mm → ∀ (h : Γ(X, U.1)) (hh : X.basicOpen h ≤ W), ρ h ≠ 0 → ∀ (J : Type) [Finite J] (θ : J → Γ(X, W)), (∀ i (s : Γ(X, U.1)) (N : ℕ), (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom s = (X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom (h ^ N) * (X.presheaf.map (homOfLE hh).op).hom (θ i) → ρ h ^ N ∣ ρ s) → ∃ g ∉ mm, ∀ i, ∃ s : Γ(X, U.1), (X.presheaf.map (homOfLE hWU).op).hom s = (X.presheaf.map (homOfLE hWU).op).hom g * θ i := by
  first | exact @GlobalTheory.LocRegDesc.descent | exact GlobalTheory.LocRegDesc.descent | (intros; apply GlobalTheory.LocRegDesc.descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianIsAbelianSchemeLocalizationAbelianLocStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_isAbelianScheme_localization_abelianLocus : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (p : Sp R) [p.asIdeal.IsPrime], p ∈ abLocus G₁ → IsAbelianScheme ((Over.pullback (spMap (algebraMap R (Localization.AtPrime p.asIdeal)))).obj G₁) := by
  first | exact @GlobalTheory.AbLocusAtPrime.isAbelianScheme_localization | exact GlobalTheory.AbLocusAtPrime.isAbelianScheme_localization | (intros; apply GlobalTheory.AbLocusAtPrime.isAbelianScheme_localization <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelIntegralToroidalOfPolarisedChartsForFanStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelIntegralToroidal_of_polarisedChartsForFan : GlobalTheory.Published.SiegelToroidalPolCharts → GlobalTheory.Published.SiegelToroidalIntegral := by
  first | exact @GlobalTheory.siegelToroidalIntegral_of_polCharts | exact GlobalTheory.siegelToroidalIntegral_of_polCharts | (intros; apply GlobalTheory.siegelToroidalIntegral_of_polCharts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallThetaKernelTranslateIntegrable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallConv

theorem splitBound_ge : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ _ => 11 ≤ D.host.splitBound := by
  exact ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS _ _ _ => hS.size.2.1.eleven_le⟩⟩

theorem standing : Big fun ch => ∀ t, SquareStanding ch.G t := by
  obtain ⟨CF0, hH⟩ := splitBound_ge.and GlobalTheory.T.test_places_prime_to_level
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc t => ?_⟩
  obtain ⟨h11, hW⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hch hsc
  refine ⟨h11, fun w hw => ?_⟩
  classical
  unfold locPl at hw
  rcases Finset.mem_union.1 hw with hw | hw
  · exact hW w hw
  · intro hmem
    have h1 := (hS.core.lev.Q_off t w hw).1
    have h2 := hS.guard.2 t w hw
    push_cast at hmem h1 h2
    rcases w.isPrime.mem_or_mem hmem with h | h
    · exact h1 (Ideal.mul_mem_right _ _ h)
    · exact h2 (Ideal.mul_mem_left _ _ h)

theorem exists_translates_integrableOn : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence →
    GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → Big fun ch => ∀ i j t (M : Vol ch.G), M.Is t → ∀ Θ Θ',
      IsMatched ch.S.B t ch.rm i j Θ Θ' → ∀ g g₁,
    ∃ z, zdeg z ≠ 0 ∧ IntegrableOn (translates z (kerSmall ch.W Θ' g g₁)) (M.fd _) (M.ν _) := by
  intro _ hK _ _ _
  obtain ⟨CF0, hH⟩ := standing
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  have hst := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hch hsc
  intro i j t M hM Θ Θ' hΘ g g₁
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  obtain ⟨e, Bs, Γ', X, om, om', h, hTr, hv⟩ := GlobalTheory.T.squareThetaTripleHypotheses_of_standing hL ch.W t i j (hst t) M hM
  obtain ⟨z, Φ, a, C₀, hz, hΦ, hid⟩ :=
    GlobalTheory.T.translatedKernel_le_thetaFunction_routeBigVertex hL ch.W ch.S.B ch.rm t i j M hM Θ Θ' hΘ g₁ e Bs Γ' X om om' h hTr hv
  have dec := (hK.1 D.host.F D.host.E D.sp.cm.sig Bs _ _ Γ' X om om' hTr).1
  obtain ⟨C, k, hC⟩ := (dec.2 Φ hΦ).1 0
  have hbd : ∀ u, ‖translates z (kerSmall ch.W Θ' g g₁) u‖ ≤
      |C₀| * |C| * (2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁) ^ k := by
    intro u
    obtain ⟨γ, hγ, hle⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight _ g
    have e1 : translates z (kerSmall ch.W Θ' g g₁) u = translates z (kerSmall ch.W Θ' (γ * g) g₁) u := by
      simp only [translates, GlobalTheory.ZConvLeft.kerSmall_rat_left hL ch.W ch.S.B ch.rm t i j Θ Θ' hΘ g₁ γ hγ]
    rw [e1]
    have h1 := hC (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))
    rw [pow_zero, mul_one] at h1
    have h2 := GlobalTheory.BlockHeight.ht_blkU_le _ _ e h.JWW (γ * g) g₁
    have h3 : (0 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) := NNReal.coe_nonneg _
    have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ≤
        2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁ :=
      h2.trans (mul_le_mul_of_nonneg_right hle (GlobalTheory.Grow.height_pos _ _).le)
    calc _ ≤ C₀ * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ := hid _ _
      _ ≤ |C₀| * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self C₀) (norm_nonneg _)
      _ ≤ |C₀| * (|C| * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h3 k)))
            (abs_nonneg C₀)
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h4 k) (mul_nonneg (abs_nonneg C₀) (abs_nonneg C))
  have hWl := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  haveI : IsFiniteMeasure ((M.ν (.grid i j)).restrict (M.fd (.grid i j))) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hWl.1 hWl.2).ne
  have hcont := GlobalTheory.SmallRoute.continuous_translates_kerSmall hL ch.W ch.S.B ch.rm t i j Θ Θ' hΘ g₁ z
  exact ⟨z, hz, Integrable.of_bound ((hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable) _
    (.of_forall hbd)⟩

end GlobalTheory.SmallConv

end
end

