import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2348
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1695
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeMeasureUnitaryDetOneFactorNearIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleRationalPointsFiniteClosedStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelOfLineBundle_rationalPoints_finite_closed : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∃ S : Finset A.left, (∀ s ∈ S, IsClosed ({s} : Set A.left)) ∧ ∀ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A, GlobalTheory.CechPic.lam (cls L hL) (toUnit A ≫ x) (𝟙 A) = 0 → x.left (IsLocalRing.closedPoint K) ∈ S := by
  first | exact @GlobalTheory.KLFinite.kl_finite | exact GlobalTheory.KLFinite.kl_finite | (intros; apply GlobalTheory.KLFinite.kl_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerConditionRestrictBasicOpenOfAffineStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_condition_restrict_basicOpen_of_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (DW : Derivation ℤ Γ(X, W.1) Γ(X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)), (∀ r, DW ((X.presheaf.map (homOfLE hW).op).hom r) = (X.presheaf.map (homOfLE hW).op).hom (D r)) → GlobalTheory.LogKS.IsKS t V U v D Θ → GlobalTheory.LogKS.IsKS t V W (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) DW ((X.presheaf.map (homOfLE hW).op).hom.mapMatrix Θ) := by
  first | exact @GlobalTheory.LogKSLoc.isKS_basicOpen | exact GlobalTheory.LogKSLoc.isKS_basicOpen | (intros; apply GlobalTheory.LogKSLoc.isKS_basicOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixExistsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodaira_spencer_matrix_exists : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∃ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M := by
  first | exact @GlobalTheory.KSExist.ksExist | exact GlobalTheory.KSExist.ksExist | (intros; apply GlobalTheory.KSExist.ksExist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowOfKodairaSpencerValueHodgeFil
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSRowsFil

theorem isKSRow_of_isKSValue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsAbelianScheme A → ∀ (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → GlobalTheory.DeRham.HdR A) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (θ : Matrix (Fin n) (Fin n) K) (s : K), (∀ σ k, IsTangent (ub σ k)) → (∀ a b, (e.symm a).1 ≠ conjEmb (e.symm b).1 → θ a b = 0) → (∀ f ∈ GlobalTheory.DeRham.Fil A, ∀ w, IsLieComb (fun a => s * ∑ b, θ a b * ψ f (hb (e.symm b))) (fun a => ub (e.symm a).1 (e.symm a).2) w → GlobalTheory.DeRham.IsKSValue h f w) → ∀ (τ : E →+* ℂ) (a₀ : Fin (Dw.mult (conjEmb τ))), (∃ w, GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ, a₀⟩ w) → ∃ w, IsLieComb (fun b => s * θ (e ⟨τ, b⟩) (e ⟨conjEmb τ, a₀⟩)) (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ, a₀⟩ w := by
  intro E _ _ _ H Dw K _ A _ A' _ i h hA ψ ub hb n e θ s htan hθ hKS τ a₀ hrow
  obtain ⟨w₀, f, hfF, hf, -⟩ := hrow
  haveI : IsCommMonObj A := hA.comm
  have hcc : ∀ σ : E →+* ℂ, conjEmb (conjEmb σ) = σ := fun σ ↦ RingHom.ext fun x ↦ Complex.conj_conj _
  have hc : ∀ a, s * ∑ b, θ a b * ψ f (hb (e.symm b)) = s * θ a (e ⟨conjEmb τ, a₀⟩) := by
    intro a
    congr 1
    rw [Finset.sum_eq_single (e ⟨conjEmb τ, a₀⟩)]
    · rw [hf, Equiv.symm_apply_apply, if_pos rfl, mul_one]
    · intro b _ hb'
      rw [hf, if_neg, mul_zero]
      intro hq
      exact hb' (by rw [← hq, Equiv.apply_symm_apply])
    · intro hn; exact absurd (Finset.mem_univ _) hn
  refine ⟨GlobalTheory.SqZero.tanExp (ub τ) (fun b ↦ s * θ (e ⟨τ, b⟩) (e ⟨conjEmb τ, a₀⟩)),
    (GlobalTheory.LieComb.isLieComb_iff_tanExp _ _).2 rfl, f, hfF, hf, hKS f hfF _ ?_⟩
  rw [GlobalTheory.LieComb.isLieComb_iff_tanExp]
  symm
  simp only [GlobalTheory.SqZero.tanExp, GlobalTheory.SqZero.lieExp, hc]
  rw [Fintype.prod_equiv e.symm _ (fun p : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) ↦
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo K (TrivSqZeroExt.inr (s * θ (e p) (e ⟨conjEmb τ, a₀⟩)) : DualNumber K)
        (TrivSqZeroExt.inr_mul_inr _ _ _)) ≫ ub p.1 p.2) (fun a ↦ by simp only [Equiv.apply_symm_apply]),
    Fintype.prod_sigma, Finset.prod_eq_single τ]
  · intro σ _ hσ
    refine Finset.prod_eq_one fun k _ ↦ GlobalTheory.SqZero.epsTo_zero_comp ((ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff _).2 (htan σ k)) _ ?_ _
    rw [hθ _ _ (by simpa [hcc] using hσ), mul_zero, TrivSqZeroExt.inr_zero]
  · intro hn; exact absurd (Finset.mem_univ _) hn

end GlobalTheory.KSRowsFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamTrivOfMemKL
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem lam_triv_of_memKL : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left,
    L.IsLB → ∀ (T : Over S) (x : T ⟶ A), GlobalTheory.MemKL A L x → Triv (ev (abelian₂ A L) (fst A T) (snd A T ≫ x)) := by
  intro S A _ hA L hL T x hx
  haveI := hA.comm
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e : ∀ (Y : Over S) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun Y a b ↦ by
    rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd]
  rw [triv_ev_iff hP]
  obtain ⟨M, hM, hc⟩ := cls_surj (evc hP (fst A T) (snd A T ≫ x))
  rw [← hc]
  have key : ∀ {X : Scheme.{0}} (f : X ⟶ (A ⊗ T).left),
      Triv (M.pull f) ↔ CechPic.pull f (evc hP (fst A T) (snd A T ≫ x)) = 0 := by
    intro X f
    rw [← hc, ← cls_pull hM f (pull_isLB hM f)]
    exact (cls_eq_zero_iff (pull_isLB hM f)).symm
  refine (cls_eq_zero_iff hM).2 (GlobalTheory.CubeGlue.triv_of_locally_triv hM (snd A T).left (lift 1 (𝟙 T)).left ?_
    (surj_restrict_snd hA T) ?_ ?_)
  · rw [← Over.comp_left, lift_snd, Over.id_left]
  · rw [key, pull_evc, e, lift_fst, lift_snd_assoc, Category.id_comp, lam_one_left]
  · intro p
    obtain ⟨V, hV, hTV⟩ := hx p
    obtain ⟨W, hW, hw⟩ := exists_pull_eq_zero
      (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p
    refine ⟨V ⊓ W, ⟨hV, hW⟩, ?_⟩
    let U := (snd A T).left ⁻¹ᵁ (V ⊓ W)
    let Y : Over S := Over.mk (U.ι ≫ (A ⊗ T).hom)
    let i : Y ⟶ A ⊗ T := Over.homMk U.ι rfl
    show Triv (M.pull i.left)
    rw [key, pull_evc, e]
    have ht : ∀ z, (i ≫ snd A T).left z ∈ V := fun z ↦ z.2.1
    have h1 := pull_mul_eq hL hTV (i ≫ snd A T) ht (i ≫ fst A T)
    have h2 : CechPic.pull (i ≫ snd A T).left
        (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) = 0 :=
      pull_eq_zero_of_mem W (i ≫ snd A T).left (fun z ↦ z.2.2) hw
    rw [map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      Category.assoc] at h2
    rw [lam, mul_comm (i ≫ fst A T), ← Category.assoc i (snd A T) x, h1, Category.assoc, sub_self, zero_sub,
      neg_add_eq_zero]
    exact (sub_eq_zero.1 h2)

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDataTateSpanStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_data_tate_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (V : Type) [CommRing V]
    (β : V →+* 𝓞_ℂ_[p]) (σ : 𝓞 E →+* V) (J : Type) [DecidableEq J] (N : ℕ) (a : Fin N → Dw.La)
    (T S : J → Fin N → V) (tι : Dw.La →+ P.T), LatData Dw σ a T S → (∀ (o : 𝓞 E) b, tι (o • b) = P.actT o (tι b)) →
    Submodule.span ℤ_[p] (Set.range tι) = ⊤ →
    P.eigV (β.comp σ) ≤ Submodule.span ℂ_[p] (Set.range fun i => ∑ m, (β (T i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] tι (a m)) := by
  first | exact @GlobalTheory.FlatModel.EigSpan.eigV_le_span | exact GlobalTheory.FlatModel.EigSpan.eigV_le_span | (intros; apply GlobalTheory.FlatModel.EigSpan.eigV_le_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoDetConormalProd
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HodgeProd

open GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.Twist (resM resM_resM app_resM)

section Split

variable {S : Scheme.{0}} {F F₁ F₂ : S.Modules} {p₁ : F₁ ⟶ F} {p₂ : F₂ ⟶ F} {i₁ : F ⟶ F₁}
    {i₂ : F ⟶ F₂} (h : i₁ ≫ p₁ + i₂ ≫ p₂ = 𝟙 _) (h₁ : p₁ ≫ i₁ = 𝟙 _) (h₂ : p₂ ≫ i₂ = 𝟙 _) (h₃ : p₁ ≫ i₂ = 0)
    (h₄ : p₂ ≫ i₁ = 0) {U V : S.Opens} {n m : ℕ} {e₁ : Fin n → Γ(F₁, U)} {e₂ : Fin m → Γ(F₂, U)}
    (he₁ : VB.IsFrame e₁) (he₂ : VB.IsFrame e₂)

include h h₁ h₂ h₃ h₄ in

theorem repr_left (hV : V ≤ U) (y : Γ(F, V)) (i : Fin n) :
    ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr y (Fin.castAdd m i) =
      (he₁.basis hV).repr (i₁.app V y) i := by
  have key : (Finsupp.lapply (Fin.castAdd m i)).comp
      ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr.toLinearMap =
      (Finsupp.lapply i).comp ((he₁.basis hV).repr.toLinearMap.comp (QCoh.appLinear i₁ V)) := by
    refine ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).ext fun k => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_left, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₁]
      change _ = ((he₁.basis hV).repr ((resM F₁ hV) (e₁ j))) i
      rw [← IsFrame.basis_apply he₁ hV, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
      simp [Fin.castAdd_inj]
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_right, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₄]
      change _ = ((he₁.basis hV).repr 0) i
      rw [map_zero, Finsupp.single_apply]
      simp only [Finsupp.coe_zero, Pi.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false]
      intro e
      have := congrArg Fin.val e
      simp at this
      omega
  exact LinearMap.congr_fun key y

include h h₁ h₂ h₃ h₄ in

theorem repr_right (hV : V ≤ U) (y : Γ(F, V)) (i : Fin m) :
    ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr y (Fin.natAdd n i) =
      (he₂.basis hV).repr (i₂.app V y) i := by
  have key : (Finsupp.lapply (Fin.natAdd n i)).comp
      ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).repr.toLinearMap =
      (Finsupp.lapply i).comp ((he₂.basis hV).repr.toLinearMap.comp (QCoh.appLinear i₂ V)) := by
    refine ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).ext fun k => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_left, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₃]
      change _ = ((he₂.basis hV).repr 0) i
      rw [map_zero, Finsupp.single_apply]
      simp only [Finsupp.coe_zero, Pi.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false]
      intro e
      have := congrArg Fin.val e
      simp at this
      omega
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply]
      rw [IsFrame.basis_apply, Fin.append_right, ← app_resM, QCoh.coe_appLinear, QCoh.app_app, h₂]
      change _ = ((he₂.basis hV).repr ((resM F₂ hV) (e₂ j))) i
      rw [← IsFrame.basis_apply he₂ hV, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
      simp [Fin.natAdd_inj]
  exact LinearMap.congr_fun key y

include h h₁ h₂ h₃ h₄ in

theorem detUnit_append {U' : S.Opens} {e₁' : Fin n → Γ(F₁, U')} {e₂' : Fin m → Γ(F₂, U')}
    (he₁' : VB.IsFrame e₁') (he₂' : VB.IsFrame e₂') (hV : V ≤ U) (hV' : V ≤ U') :
    (GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).detUnit
                 (GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁' he₂') hV hV' =
      he₁.detUnit he₁' hV hV' * he₂.detUnit he₂' hV hV' := by
  refine Units.ext ?_
  rw [Units.val_mul, IsFrame.val_detUnit, IsFrame.val_detUnit, IsFrame.val_detUnit, Module.Basis.det_apply,
    Module.Basis.det_apply, Module.Basis.det_apply]
  have hM : ((GlobalTheory.TorusCot.isFrame_append h h₁ h₂ h₃ h₄ he₁ he₂).basis hV).toMatrix
      (fun k => resM F hV' (Fin.append (fun i => p₁.app U' (e₁' i)) (fun j => p₂.app U' (e₂' j)) k)) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks
        ((he₁.basis hV).toMatrix fun i => resM F₁ hV' (e₁' i)) 0 0
        ((he₂.basis hV).toMatrix fun i => resM F₂ hV' (e₂' i))) := by
    ext k l
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) l
    all_goals
      simp only [Module.Basis.toMatrix_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Fin.append_left,
        Fin.append_right, Matrix.zero_apply]
    · rw [repr_left h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₁]; rfl
    · rw [repr_left h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₄]
      change ((he₁.basis hV).repr 0) i = 0
      simp
    · rw [repr_right h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₃]
      change ((he₂.basis hV).repr 0) i = 0
      simp
    · rw [repr_right h h₁ h₂ h₃ h₄ he₁ he₂, ← app_resM, QCoh.app_app, h₂]; rfl
  rw [hM, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

end Split

section Prod

open GlobalTheory.Conormal

variable {S : Scheme.{0}} (G H : Over S) [GrpObj G] [GrpObj H]

theorem lbIso_det_conormal_prod [QuasiSeparated G.hom] [QuasiSeparated H.hom] (g h : ℕ)
    (hG : IsVB (omega G) g) (hH : IsVB (omega H) h) (t : 𝟙_ (Over S) ⟶ G ⊗ H) (ht : t = lift η[G] η[H]) :
    LBIso (VB.det (conormal (sec t)) (g + h)) (CechPic.tens (VB.det (omega G) g) (VB.det (omega H) h)) := by
  subst ht
  have i₁ : η[G] ≫ lift (𝟙 G) (toUnit G ≫ η[H]) = lift η[G] η[H] := by simp
  have i₂ : η[H] ≫ lift (toUnit H ≫ η[G]) (𝟙 H) = lift η[G] η[H] := by simp
  have p₁ := lift_fst η[G] η[H]
  have p₂ := lift_snd η[G] η[H]
  have c₁ : η[H] ≫ toUnit H ≫ η[G] = η[G] := by simp
  have c₂ : η[G] ≫ toUnit G ≫ η[H] = η[H] := by simp
  have H₀ := cotMap_prod i₁ i₂ p₁ p₂
  have H₁ := (cotMap_comp p₁ i₁ (lift_fst _ _) (Category.comp_id _)).trans (cotMap_id rfl _)
  have H₂ := (cotMap_comp p₂ i₂ (lift_snd _ _) (Category.comp_id _)).trans (cotMap_id rfl _)
  have H₃ := (cotMap_comp p₁ i₂ (lift_fst _ _) c₁).trans (cotMap_eq_zero rfl _)
  have H₄ := (cotMap_comp p₂ i₁ (lift_snd _ _) c₂).trans (cotMap_eq_zero rfl _)
  let L := CechPic.tens (VB.det (omega G) g) (VB.det (omega H) h)
  have hL : L.IsLB := CechPic.isLB_tens hG.isLB_det hH.isLB_det
  have he : ∀ p : L.ι, IsFrame (Fin.append
      (fun i => (cotMap (fst G H) p₁).app (L.U p) (resM (omega G) inf_le_left (p.1.e i)))
      (fun j => (cotMap (snd G H) p₂).app (L.U p) (resM (omega H) inf_le_right (p.2.e j)))) := fun p =>
    GlobalTheory.TorusCot.isFrame_append H₀ H₁ H₂ H₃ H₄ (p.1.isFrame.res inf_le_left) (p.2.isFrame.res inf_le_right)
  refine LBIso.symm (lbIso_det_of_frames hL _ he fun p q => ?_).2
  refine Eq.trans ?_ (detUnit_append H₀ H₁ H₂ H₃ H₄ (p.1.isFrame.res inf_le_left) (p.2.isFrame.res inf_le_right)
    (q.1.isFrame.res inf_le_left) (q.2.isFrame.res inf_le_right) inf_le_left inf_le_right).symm
  exact congrArg₂ (· * ·) ((IsFrame.res_detUnit _ _ _ _ _).trans (IsFrame.detUnit_res _ _ _ _ _ _).symm)
    ((IsFrame.res_detUnit _ _ _ _ _).trans (IsFrame.detUnit_res _ _ _ _ _ _).symm)

end Prod

end GlobalTheory.HodgeProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeMeasureUnitaryDetOneFactorNearIdentityStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_measure_unitaryDetOneFactor_near_identity : ∀ (p q : ℕ) (a₀ : Fin p ⊕ Fin q) (m : Measure (UpqT p q)), IsMinf m → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ENNReal.ofReal (ε ^ ((p + q) ^ 2 - 1) / ((p + q : ℕ) : ℝ) ^ (p + q - 1)) ≤ m {u | (∀ a b, ‖(sMat a₀ u - 1) a b‖ < ε) ∧ 0 < (UpqT.mat u).det.im} := by
  first | exact @GlobalTheory.CovTop.VolLow.OneMeasure.le_measure_sMat_near | exact GlobalTheory.CovTop.VolLow.OneMeasure.le_measure_sMat_near | (intros; apply GlobalTheory.CovTop.VolLow.OneMeasure.le_measure_sMat_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadingTermUniqueSupportedBalancedCone
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem leadingTerm_unique : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (d : ℕ) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X →
    ∀ (r m : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (a : Fin m → X), IsCone bar φ γ → Supports bar φ d γ a →
    ∀ (β : LinearMap.BilinForm ℤ X) (k : ℕ) (c : Fin r → ℕ), 0 < k → (∀ j, 0 < c j) → k • β = ∑ j, c j • γ j →
    (∀ x, x ≠ 0 → 0 < β x x) → ∀ (e : X ≃ₗ[O] X) (N : ℕ), 3 ≤ N → (∀ x, CongMod N (e x) x) →
    d * φ.evalZ β = (∑ i, β (e (a i)) (e (a i)) : ℤ) → ∀ x, e x = x := by
  intro O _ bar φ d X _ _ _ _ _ _ hF r m γ a hγ hS β k c hk hc hβ hpos e N hN he hd
  have hkβ : ∀ y z, (k : ℤ) * β y z = ∑ j, (c j : ℤ) * γ j y z := fun y z => by
    have := LinearMap.congr_fun₂ hβ y z
    simpa [LinearMap.sum_apply, nsmul_eq_mul] using this
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  have hbal : β ∈ balForms bar X := by
    refine ⟨fun y z => mul_left_cancel₀ hk0 ?_, fun o y z => mul_left_cancel₀ hk0 ?_⟩
    · rw [hkβ, hkβ]; exact Finset.sum_congr rfl fun j _ => by rw [(hγ.mem j).1]
    · rw [hkβ, hkβ]; exact Finset.sum_congr rfl fun j _ => by rw [(hγ.mem j).2]
  have hbal' : pull e.toLinearMap β ∈ balForms bar X := pull_mem _ hbal
  have hnn' : ∀ y, 0 ≤ pull e.toLinearMap β y y := fun y => by
    rw [pull_apply]
    by_cases h0 : e.toLinearMap y = 0
    · rw [h0]; simp
    · exact (hpos _ h0).le
  obtain ⟨k', c', hk', hβ'⟩ := hS.only _ hbal' hnn' (by rw [evalZ_pull φ e.surjective]; exact hd)
  have hsum : ∑ j, (k' * c j) • pull e.toLinearMap (γ j) = ∑ j, (k * c' j) • γ j := by
    refine LinearMap.ext₂ fun y z => ?_
    have h1 := hkβ (e y) (e z)
    have h2 := LinearMap.congr_fun₂ hβ' y z
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, pull_apply, nsmul_eq_mul, LinearEquiv.coe_coe] at h1 h2 ⊢
    have e1 : ∑ j, ((k' * c j : ℕ) : ℤ) * γ j (e y) (e z) = k' * ∑ j, (c j : ℤ) * γ j (e y) (e z) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by push_cast; ring
    have e2 : ∑ j, ((k * c' j : ℕ) : ℤ) * γ j y z = k * ∑ j, (c' j : ℤ) * γ j y z := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by push_cast; ring
    rw [e1, e2, ← h1, ← h2]; ring
  have hγe : IsCone bar φ fun j => pull e.toLinearMap (γ j) := hγ.pull_equiv e
  choose σ hσ using GlobalTheory.T.smoothCone_face_of_interior_common_point O bar φ X hF r r _ γ hγe hγ (fun j => k' * c j) (fun j => k * c' j)
    (fun j => Nat.mul_pos hk' (hc j)) hsum
  have hσinj : Function.Injective σ := fun i j hij => hγe.injective (by simp only [hσ, hij])
  let σe := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσinj)
  have hG : ∀ y z, (∑ j, γ j) (e y) (e z) = (∑ j, γ j) y z := by
    intro y z
    simp only [LinearMap.sum_apply]
    calc ∑ j, γ j (e y) (e z) = ∑ j, γ (σe j) y z :=
          Finset.sum_congr rfl fun j _ => LinearMap.congr_fun₂ (hσ j) y z
      _ = ∑ j, γ j y z := σe.sum_comp (fun j => γ j y z)
  have hGpos : ∀ x, x ≠ 0 → 0 < (∑ j, γ j) x x := by
    intro x hx
    have h2 : 0 < (k : ℤ) * β x x := mul_pos (by exact_mod_cast hk) (hpos x hx)
    rw [hkβ] at h2
    obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt (show ∑ j : Fin r, (0 : ℤ) < _ by simpa using h2)
    have hj' : 0 < γ j x x := pos_of_mul_pos_right hj (by positivity)
    simp only [LinearMap.sum_apply]
    exact hj'.trans_le (Finset.single_le_sum (fun i _ => hγ.nonneg i x) (Finset.mem_univ j))
  have key := GlobalTheory.T.isometry_eq_refl_of_congr_mod_ge_three X (∑ j, γ j) hGpos e.toAddEquiv.toIntLinearEquiv (fun y z => hG y z) N hN he
  intro x
  simpa using LinearEquiv.congr_fun key x

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelAutomorphismUnipotentFixesComplexPointEqOneStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAutomorphism_unipotent_fixes_complexPoint_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ γ : LevelAut Dw l, UnipAt I γ → ∀ y : FrPt Xo c ℂ, ptF (move Xo c γ y) = ptF y → γ = 1 := by
  first | exact @GlobalTheory.UnipFree.free | exact GlobalTheory.UnipFree.free | (intros; apply GlobalTheory.UnipFree.free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComplexModelsComponentsIsometriesDegreStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCover_complexModels_components_isometries_degree : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∃ (π : (U₂ σ₂).Comp → (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : (U₂ σ₂).Comp → GL (Fin D.R.r) D.host.E) (N : ℕ), 0 < N ∧ (∀ k₂, ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ∧ (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) ∧ ((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom ≤ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ∧ (((U₂ σ₂).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ ≠ 0) ∧ (∀ k, ∑ᶠ k₂ : {k₂ // π k₂ = k}, (((U₂ σ₂).X k₂.1).Γ.map (MulAut.conj (δ k₂.1)).toMonoidHom).relIndex ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ = N) ∧ ∃ t : (U₂ σ₂).Comp → ℂ, (∀ k₂, ‖t k₂‖ = 1) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ sec Xo c a n, ∀ g ∈ sec d.Xo₂ d.c₂ a n, Pull d f g → ∀ k₂ (x : Frame ((U₂ σ₂).X k₂).Ψ D.R.r) (x' : Frame ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ D.R.r), x ∈ ((U₂ σ₂).X k₂).dom → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ ((U₂ σ₂).X k₂).Ψ) (h₁ : τ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ), mat x' ⟨τ, h₁⟩ = (δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat x ⟨τ, h₂⟩) → Even n → rdU (U₂ σ₂) g k₂ x = t k₂ ^ n * rdU (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) f (π k₂) x' := by
  first | exact @GlobalTheory.LevModel.levCover_model | exact GlobalTheory.LevModel.levCover_model | (intros; apply GlobalTheory.LevModel.levCover_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMeasureFinitePartPreimageStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_measure_finite_part_preimage : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (m : ∀ ρ, Measure (Upq V ρ)) (rp : GA D V →* (∀ ρ, Upq V ρ)) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) (μ : Measure (GA D V)), V.SigOK → IsInfFam θ → IsFrames V A → (∀ ρ, IsMinf (m ρ)) → Continuous rp → IsRealPart V θ A rp → IsOpen {h : GA D V | finE V h ∈ K} → IsMeasLev V K μ → ∀ g ∈ GfC V, ∀ B : Set (∀ ρ, Upq V ρ), MeasurableSet B → μ {h | finE V (g⁻¹ * h) ∈ K ∧ rp h ∈ B} = Measure.pi m B := by
  first | exact @GlobalTheory.CovTop.VolPush.meas_translate_eq | exact GlobalTheory.CovTop.VolPush.meas_translate_eq | (intros; apply GlobalTheory.CovTop.VolPush.meas_translate_eq <;> assumption)
end

