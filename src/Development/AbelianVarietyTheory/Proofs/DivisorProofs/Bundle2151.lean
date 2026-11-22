import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0043
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0018
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1340
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0267
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2094
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefMapNormEquivariantBasisOfFive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0131
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreIsoUniversalGroupFramedPoint
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
noncomputable section

namespace GlobalTheory.PtDeg

open Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem fibre_iso_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (v : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ v → ∀ (σ : K →+* ℂ) (φ : K →ₐ[c.F] CAt (σ.comp (algebraMap c.F K))), (∀ a, toC (φ a) = σ a) → ∀ (z : FrPt Xo c (CAt (σ.comp (algebraMap c.F K)))), FrMap φ y z → ∀ (Q : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ F.P₀.A.left) (v' : Fin F.P₀.g → (epsR ℂ ⟶ Q.A)), GlobalTheory.IsPolFibre σ F.P₀ Q ψ → (∀ i, GlobalTheory.IsVecOver σ ψ (F.v i) (v' i)) → ∀ (T : GlobalTheory.CM.PAT H (Sp ℂ)) (m : SABMap T.t Xo.univ.t z.x), ∃ f : Q.A ⟶ T.pol.A, IsMonHom f ∧ LBIso (lbPow (T.pol.L.pull f.left) 1) (lbPow Q.L 1) ∧ ∀ i (q : epsR ℂ ⟶ Q.A), IsLieComb (fun k => σ (v i k)) v' q → ∀ w' : epsR ℂ ⟶ T.pol.A, w'.left ≫ m.φ = z.u ρ i → q ≫ f = w' := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ v hFC σ φ hφ z hz Q ψ v' hQ hv' T m

  have hφσ : (φ.toRingHom : K →+* ℂ) = σ := RingHom.ext hφ
  have hbase : z.x = spMap σ ≫ y.x := by rw [hz.1, hφσ]; rfl

  have hcomp := hQ.2.1.comp F.fib.2.1
  have w0 : (ψ ≫ F.φ) ≫ B.t.G.hom = (Q.A.hom ≫ spMap σ) ≫ spMap (algebraMap (𝓞 K) K) := by
    rw [hcomp.1.w, Category.assoc]
  let χ₀ : Q.A.left ⟶ t₀.G.left := m2.cart.1.lift (ψ ≫ F.φ) (Q.A.hom ≫ spMap σ) w0
  have hχ₀2 : χ₀ ≫ m2.φ = ψ ≫ F.φ := m2.cart.1.lift_fst _ _ w0
  have hχ₀b : χ₀ ≫ t₀.G.hom = Q.A.hom ≫ spMap σ := m2.cart.1.lift_snd _ _ w0
  have hχ₀ : IsGrpPullback Q.A t₀.G (spMap σ) χ₀ := m2.cart.cancel (by rw [hχ₀2]; exact hcomp) hχ₀b
  have hχ := hχ₀.comp m1.cart
  have w1 : (χ₀ ≫ m1.φ) ≫ Xo.univ.t.G.hom = Q.A.hom ≫ z.x := by rw [hχ.1.w, hbase]
  let fl : Q.A.left ⟶ T.t.G.left := m.cart.1.lift (χ₀ ≫ m1.φ) Q.A.hom w1
  have hfl : fl ≫ m.φ = χ₀ ≫ m1.φ := m.cart.1.lift_fst _ _ w1
  have hflb : fl ≫ T.t.G.hom = Q.A.hom := m.cart.1.lift_snd _ _ w1
  let f : Q.A ⟶ T.pol.A := Over.homMk fl hflb
  refine ⟨f, ?_, ?_, ?_⟩
  ·
    refine GlobalTheory.DivisibleHom.isMonHom_of_mul_points f fun S x y => ?_
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · have e1 := hχ.2 S x y (pushPt hχ.1.w x) (pushPt hχ.1.w y) rfl rfl
      have e2 := m.cart.2 S (x ≫ f) (y ≫ f) (pushPt m.cart.1.w (x ≫ f)) (pushPt m.cart.1.w (y ≫ f)) rfl rfl
      rw [Over.comp_left, Category.assoc]
      change _ ≫ fl ≫ m.φ = _
      rw [hfl, ← e1, ← e2]
      refine mul_left_congr (by rw [hbase]) _ _ _ _ ?_ ?_
      · show x.left ≫ χ₀ ≫ m1.φ = (x.left ≫ fl) ≫ m.φ
        rw [Category.assoc, hfl]
      · show y.left ≫ χ₀ ≫ m1.φ = (y.left ≫ fl) ≫ m.φ
        rw [Category.assoc, hfl]
    · exact (Over.w ((x * y) ≫ f)).trans (Over.w ((x ≫ f) * (y ≫ f))).symm
  ·
    obtain ⟨wT, hwT, -⟩ := m.lin
    obtain ⟨w1', hw1', -⟩ := m1.lin
    obtain ⟨w2', hw2', -⟩ := m2.lin
    have hT : LBIso T.t.PP.L (Xo.univ.t.PP.L.pull m.φ) := ⟨wT, hwT⟩
    have h1 : LBIso t₀.PP.L (Xo.univ.t.PP.L.pull m1.φ) := ⟨w1', hw1'⟩
    have h2 : LBIso t₀.PP.L (B.t.PP.L.pull m2.φ) := ⟨w2', hw2'⟩
    have hT2 := GlobalTheory.CM.EllComp.lbIso_pull_comp hT.symm fl
    rw [hfl] at hT2
    have h3 := GlobalTheory.CM.EllComp.lbIso_pull_comp h1.symm χ₀
    have h4 := GlobalTheory.CM.EllComp.lbIso_pull_comp h2.symm χ₀
    rw [hχ₀2] at h4
    have h5 : LBIso (B.t.PP.L.pull (ψ ≫ F.φ)) (F.P₀.L.pull ψ) := GlobalTheory.CM.EllComp.lbIso_pull_comp F.fib.2.2 ψ
    have e45 := LBIso.trans (pull_isLB B.t.PP.isLB _) (pull_isLB F.P₀.isLB ψ) Q.isLB h5 hQ.2.2
    have e345 := LBIso.trans (pull_isLB t₀.PP.isLB χ₀) (pull_isLB B.t.PP.isLB _) Q.isLB h4.symm e45
    have e2345 := LBIso.trans (pull_isLB Xo.univ.t.PP.isLB _) (pull_isLB t₀.PP.isLB χ₀) Q.isLB h3 e345
    have main : LBIso (T.t.PP.L.pull fl) Q.L :=
      LBIso.trans (pull_isLB T.t.PP.isLB fl) (pull_isLB Xo.univ.t.PP.isLB _) Q.isLB hT2.symm e2345
    exact GlobalTheory.lbIso_lbPow main 1
  ·
    intro i q hq w' hw'
    obtain ⟨u, w, hu1, hu2, hw⟩ := hFC i
    haveI := GlobalTheory.ShFam.OpenReg.mono_spMap_algebraMap (𝓞 K) K
    have hFw : F.φ ≫ B.t.G.hom = F.P₀.A.hom ≫ spMap (algebraMap (𝓞 K) K) := F.fib.2.1.1.w
    have hu3 : u ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) := by
      rw [← cancel_mono (spMap (algebraMap (𝓞 K) K))]
      calc (u ≫ t₀.G.hom) ≫ spMap (algebraMap (𝓞 K) K) = (u ≫ m2.φ) ≫ B.t.G.hom := by
            rw [Category.assoc, Category.assoc, m2.cart.1.w]
        _ = (w.left ≫ F.P₀.A.hom) ≫ spMap (algebraMap (𝓞 K) K) := by
            rw [hu2, Category.assoc, hFw, Category.assoc]
        _ = spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap (𝓞 K) K) := by rw [Over.w w]; rfl
    obtain ⟨q', hq', -⟩ := GlobalTheory.existsUnique_isVecOver hQ.2.1.1 w
    have hq'c : IsLieComb (fun k => σ (v i k)) v' q' :=
      GlobalTheory.ArcQ.NormalForm.isLieComb_baseChange hQ.2.1 (fun k => hv' k) hq' hw
    have hqq : q = q' := by
      obtain ⟨a, ha, rfl⟩ := hq
      obtain ⟨b, hb, rfl⟩ := hq'c
      have hab : a = b := funext fun k => Over.OverMorphism.ext ((ha k).trans (hb k).symm)
      rw [hab]
    subst hqq
    have key : q.left ≫ χ₀ = spMap (dualMap σ) ≫ u := by
      apply m2.cart.1.hom_ext
      · rw [Category.assoc, hχ₀2, Category.assoc, hu2, ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ F.φ) hq'
      · rw [Category.assoc, hχ₀b, Category.assoc, hu3, ← Category.assoc, Over.w q]
        show spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ = _
        rw [GlobalTheory.spMap_comp_spMap, GlobalTheory.spMap_comp_spMap]
        congr 1
        ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [hw', hz.2.1, ← hu1, hφσ]
      change (q.left ≫ fl) ≫ m.φ = _
      rw [Category.assoc, hfl, ← Category.assoc, key, Category.assoc]
      rfl
    · exact (Over.w (q ≫ f)).trans (Over.w w').symm

end GlobalTheory.PtDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceOnSelfDualLatticeOfDatumImageStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_on_selfDual_lattice_of_datum_image : ∀ {D : D7} (V : HSp D) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}, IsSDFrame V β Λ 1 → ∀ {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)}, LatEmb V ι → ∀ (K : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) (t : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) (M : ℕ), (∀ a : La, ∃ w ∈ latGHat V 1, t • (K *ᵥ finVec V (ι a) - finVec V (ι a)) = M • w) → ∀ x ∈ Λ, ∃ y ∈ latHat V, t • (K *ᵥ finVec V x - finVec V x) = M • y := by
  first | exact @GlobalTheory.LevelLatticeCong.cong_on_sdLattice | exact GlobalTheory.LevelLatticeCong.cong_on_sdLattice | (intros; apply GlobalTheory.LevelLatticeCong.cong_on_sdLattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatesOfRationalThetaLiftFromCharacterisatio
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne GlobalTheory.GalLift.Assembly

namespace GlobalTheory.ConjRatLiftFive

set_option maxHeartbeats 1000000 in

theorem oneMapConj5 : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Core5 R F → ∀ (fw : FWTie T R κw v₀) (i : Fin D.R.m), ∀ (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), OMPins T R κw v₀ O i → ∀ h, RepsAt (O i) (v₀ i (sg0 D A)) h → ∀ gramR c0R c0L, Comparison₂ R gramR c0R c0L → CoefficientBaseChange R i (O i).jL (inC (O i).c') (c0L i) (O i).c0' → ∀ (σ : D.what₂.LL →+* ℂ), OverK σ → ∀ (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (μ' η' : (AE D)ˣ →* Circle), ChiAt R i σ μ' → IsEtaConj σ R.eta η' → ∀ (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), IsConjForms R i σ (c0L i) c c₁ H j → ∀ (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))), LiftData R i σ μ' η' c H ω f₀ f B io thP → ∃ (u : GA D (Wc D i) → ℂ) (z : G) (κ : ℂ), PhaseFun R i u ∧ z ∈ Subgroup.center G ∧ ‖κ‖ = 1 ∧ EquivBy (O i) κw σ hV u ∧ ∀ x₀ (n : ℕ) (a : Fin n → D.what₂.LL) (fs : Fin n → Cu T κw i), IsClassSum (O i) κw h x₀ a fs → ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (fun ρ => (v ρ : (R.MW i σ).sm ρ)) = v₀ i σ → ∀ g, κ * thP ((c.ext ∘ₗ H.e).rangeRestrict (j x₀)) (PiTensorProduct.tprod ℂ v) g = ∑ k, σ (a k) * (u g * phiC T hV (wtA (κw i)) (actG (O i) z (fs k : T.R ((i : ℕ) + 1))) g) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR tie i O hO h hh gramR c0R c0L _ hc σ hσ hV μ' η' hμ hη c c₁ H j hj ω f₀ f B io thP hL
  refine hh.elim fun J' hJ => (exists_ext (O i) hO.1 hO.2 σ).elim fun σ' hσ' => ?_
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) f := by
    have h1 := hL.2.1.theta 1
    have e : (1 : PolF D (Wc D i).rank (Vc D i).rank) = MvPolynomial.basisMonomials _ ℂ 0 := by
      rw [MvPolynomial.coe_basisMonomials]; rfl
    rw [e, ptAt, pureTensorO, pureTensorL, Module.Basis.constr_basis] at h1
    simpa [opPow] using h1
  exact oneMap_of_ext_ofFive hR tie (O i) hO.2 hJ.1 hc hσ' (GlobalTheory.GalOne.Facts.factsAt_ofFive T R F κ v₀ hR tie i (O i) hO.2 σ σ' hσ' hσ).1 hV hj
    ⟨hσ, hμ, hη, hL.1, hL.2.1.vec, hth⟩ hL

section Main

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem base_lift5 (hR : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (i : Fin D.R.m) (hE : fw.Evaluates) (hI : EvInj T R v₀)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ) (hP : OMPins T R κw v₀ O i)
    (hO : (O i).OneMapOf (κw i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph)
    (h : (O i).Cl' () → GA D (Vc D i)) (hh : RepsAt (O i) (v₀ i (sg0 D A)) h) :
    ∃ (act : G → Cu T κw i → Cu T κw i) (z : G) (ze : D.what₂.LL),
      (∀ g f, (act g f : T.R ((i : ℕ) + 1)) = actG (O i) g (f : T.R ((i : ℕ) + 1))) ∧ z ∈ Subgroup.center G ∧
      (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x₀, ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → Cu T κw i),
        IsClassSum (O i) κw h x₀ a f ∧ IsRatLift R i ph x₀ (ratOf fw i act z ze a f) := by
  choose act hact hj using (GlobalTheory.T.conjugateLift_unique_and_baseDatum).2.2.2.1 T R F κw v₀ hR fw i hE hI O hO.1
  have hq1 := (GlobalTheory.T.conjugateLift_unique_and_baseDatum).2.2.2.2 T R F κw v₀ hR fw i hE hI O ph hP hO h hh
  obtain ⟨z, hz, ze, hze, hx⟩ := hq1
  refine ⟨act, z, ze, hact, hz, hze, fun x₀ => ?_⟩
  have hq2 := hx x₀
  obtain ⟨n, a, f, hc, he⟩ := hq2
  refine ⟨n, a, f, hc, ?_⟩
  have hs : ∀ b, D.what₂.embLL b = sg0 D A b := fun b => by rw [sign_at_base_place_eq_embedding R]
  have h1 := he (fun k => act z (f k)) (fun k => hact z (f k))
  have h2 := read_sum (sg0 D A) ((R.FW i).j (sg0 D A)) (crdF fw i) act (R.FW i).chi (R.gW i (sg0 D A))
    (fun g f => by rw [← hs]; exact hj g f) (fun g => (idemOf A.X).coeff g) (fun k => ze * a k) (fun k => act z (f k))
  refine h2.trans (Eq.trans ?_ h1.symm)
  simp only [hs]
  rfl

set_option maxHeartbeats 800000 in

theorem conj_lift5 (hR : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (i : Fin D.R.m) (hE : fw.Evaluates)
    (hI : EvInj T R v₀) (hinj : Function.Injective ((R.FW i).j (sg0 D A)))
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ) (hP : OMPins T R κw v₀ O i)
    (hO : (O i).OneMapOf (κw i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph)
    {gramR c0R c0L} (hT : Comparison₂ R gramR c0R c0L) (hC : CoefficientBaseChange R i (O i).jL (inC (O i).c') (c0L i) (O i).c0')
    (σ : D.what₂.LL →+* ℂ) (hσ : OverK σ) {μ' η' : (AE D)ˣ →* Circle} (hμ : ChiAt R i σ μ') (hη : IsEtaConj σ R.eta η')
    {c : CoefA (Vc D i)} {c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W} {H : HMod (Bridge.Gf (Vc D i) → c.W)}
    {j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H} (hF : IsConjForms R i σ (c0L i) c c₁ H j) {ω f₀ f B io thP}
    (hL : LiftData R i σ μ' η' c H ω f₀ f B io thP) :
    ∃ (th : H.H →ₗ[ℂ] (R.HW i σ).H) (u : GA D (Wc D i) → ℂ) (U : (R.HW i σ).H ≃ₗᵢ[ℂ] (R.HW i σ).H) (z : G) (κ : ℂ),
      IsProjOf R i σ thP th ∧ IsCompPhase R i σ u U ∧ z ∈ Subgroup.center G ∧ ‖κ‖ = 1 ∧
      ∀ x y, IsRatLift R i ph x y → U ((R.FW i).j σ y) = κ • R.gW i σ z (th (j x)) := by
  refine (exists_reps hP).elim fun h hh => ?_
  have hg : GoodEmb T.Q.c (res T σ) := (GlobalTheory.GalLift.overK_iff_good_ofFive T R F κw v₀ hR fw i σ).1 hσ
  have hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i := fw.laws.toLawsM.spaceW _ (inR i) _ hg
  have hq3 := base_lift5 hR fw i hE hI O ph hP hO h hh
  obtain ⟨act, z₀, ze, hact, hz₀, ⟨m, hm, hze⟩, hx⟩ := hq3
  have hq4 := oneMapConj5 T R F κw v₀ hR fw i O hP h hh gramR c0R c0L hT hC σ hσ hV
    μ' η' hμ hη c c₁ H j hF ω f₀ f B io thP hL
  obtain ⟨u, z, κ, hu, hz, hκ, hEq, hid⟩ := hq4
  have hq5 := (GlobalTheory.T.centralShift_phase_conjReadings_fiveClauses).2.1 R F hR i σ u hu
  obtain ⟨U, hU⟩ := hq5
  have hq6 := (GlobalTheory.T.conjugateLift_unique_and_baseDatum).2.2.1 R F hR i
  obtain ⟨hlift, htr⟩ := hq6
  have hq7 := htr σ
  obtain ⟨htr, hW⟩ := hq7
  let J : (Fin (R.nW i) → D.what₂.LL) →ₛₗ[σ] (R.HW i σ).H := U.toLinearEquiv.toLinearMap.comp ((R.FW i).j σ)
  let ev : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) := evL (R.HW i σ).e (v₀ i σ)
  have hev : Function.Injective ev := hI i σ hg
  have hJ : ∀ (f : Cu T κw i) g, ev (J (crdF fw i f)) g =
      u g * phiC T hV (wtA (κw i)) (f : T.R ((i : ℕ) + 1)) g := fun f g =>
    (hU.2.2.2.2 _ _ _).trans (congrArg (u g * ·) (congrFun (hE i σ hg hV f) g))
  have hJa : ∀ z (f : Cu T κw i) g, ev (J (crdF fw i (act z f))) g =
      u g * phiC T hV (wtA (κw i)) (actG (O i) z (f : T.R ((i : ℕ) + 1))) g := fun z f g =>
    (hJ (act z f) g).trans (congrArg (fun w => u g * phiC T hV (wtA (κw i)) w g) (hact z f))
  have hJe : ∀ g f, J (crdF fw i (act g f)) = σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) • R.gW i σ g (J (crdF fw i f)) := by
    intro g f
    have hk := hlift g
    obtain ⟨k, hk⟩ := hk
    refine hev (Eq.trans (funext fun x => ?_) (ev.map_smul _ _).symm)
    exact (hJa g f x).trans ((hEq g k hk f x).trans (congrArg (σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) * ·)
      ((hJ f (x * k)).symm.trans (htr g k hk _ _ x).symm)))
  let v : ∀ ρ, lowT (R.MW i σ) ρ := fun ρ => ⟨v₀ i σ ρ, ((fw.hv₀ i σ).1 ρ).2.1⟩
  have hS : ∀ x₀ (n : ℕ) (a : Fin n → D.what₂.LL) (fs : Fin n → Cu T κw i), IsClassSum (O i) κw h x₀ a fs →
      κ • thP ((c.ext ∘ₗ H.e).rangeRestrict (j x₀)) (PiTensorProduct.tprod ℂ v) =
        ∑ k, σ (a k) • ev (J (crdF fw i (act z (fs k)))) := by
    intro x₀ n a fs hc
    funext g
    refine (hid x₀ n a fs hc v rfl g).trans (Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (Finset.sum_apply g Finset.univ fun k => σ (a k) • ev (J (crdF fw i (act z (fs k))))).symm)
    exact congrArg (σ (a k) * ·) (hJa z (fs k) g).symm
  have hex : ∀ x, ∃ t : (R.HW i σ).H, (R.HW i σ).e t (fun ρ => v ρ) =
      thP ((c.ext ∘ₗ H.e).rangeRestrict (j x)) (PiTensorProduct.tprod ℂ v) := fun x => by
    have h1 := hx x
    obtain ⟨n, a, fs, hc, -⟩ := h1
    exact exists_ev ev hκ _ _ _ (hS x n a fs hc)
  have h2 := (GlobalTheory.T.conjugateLift_of_characterisationClauses).2.2.2.2.2 R F hR i gramR c0R c0L hT σ hσ μ' η' c c₁ H j hF ω f₀ f B io thP hL v (fw.hv₀ i σ).1 hex
  obtain ⟨th, hth⟩ := h2
  refine ⟨th, u, U, z₀ * z⁻¹, σ ze * σ (((R.FW i).chi z₀ : D.what₂.LLˣ) : D.what₂.LL) *
    (σ (((R.FW i).chi z : D.what₂.LLˣ) : D.what₂.LL))⁻¹ * κ, hth, hU, mul_mem hz₀ (inv_mem hz), ?_, fun x y hy => ?_⟩
  · rw [norm_mul, norm_mul, norm_mul, norm_inv, norm_chi, norm_chi, hκ,
      norm_of_pow hm (a := σ ze) (by rw [← map_pow, hze, map_one])]
    norm_num
  · have h1 := hx x
    obtain ⟨n, a, fs, hc, hy'⟩ := h1
    have hyy : y = ratOf fw i act z₀ ze a fs := hinj (Eq.trans hy (Eq.symm hy'))
    refine (congrArg J hyy).trans ?_
    exact conj_abstract σ J (crdF fw i) act (R.FW i).chi (R.gW i σ) hJe (fun g => (idemOf A.X).coeff g) ev hev (R.eWf i σ)
      (fun y => hW y (v₀ i σ)) hz₀ hz ze κ a fs _ (hS x n a fs hc) (th (j x)) (hth (j x) v)

theorem hypConj5 (hR : GlobalTheory.Core5 R F) (i : Fin D.R.m) {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) {μ' η' : (AE D)ˣ →* Circle}
    (hμ : ChiAt R i σ μ') (hη : IsEtaConj σ R.eta η') : HypConj R i σ μ' η' :=
  (GlobalTheory.GalLift.hypConj_of_chars_ofFive R F hR i σ ((GlobalTheory.GalLift.labels_overK σ).1 hσ).1 ((GlobalTheory.GalLift.labels_overK σ).1 hσ).2).2 μ' η' hμ hη
    (GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj_ofFive R F hR i σ hσ η' hη).1 (GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj_ofFive R F hR i σ hσ η' hη).2

theorem lift_unique5 (hR : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (hI : EvInj T R v₀) (i : Fin D.R.m) {gramR c0R c0L}
    (hT : Comparison₂ R gramR c0R c0L) {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) {μ' η' c c₁ H j th μ'' η'' c' c₁' H' j' th'}
    (h : IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th) (h' : IsConjDatum R i σ (c0L i) μ'' η'' c' c₁' H' j' th') :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ x, th' (j' x) = κ • th (j x) := by
  have e1 : μ'' = μ' := (GlobalTheory.ConjCharUnique.conjChar_unique_ofFive R F hR i σ).1 _ _ h'.1 h.1
  have e2 : η'' = η' := (GlobalTheory.ConjCharUnique.conjChar_unique_ofFive R F hR i σ).2 _ _ h'.2.1 h.2.1
  subst e1 e2
  have h1 := (isConjLift_iff R i σ _ _ _ _ _).1 h.2.2.2
  obtain ⟨ω, f₀, f, B, io, thP, hL, hp⟩ := h1
  have h2 := (isConjLift_iff R i σ _ _ _ _ _).1 h'.2.2.2
  obtain ⟨ω', f₀', f', B', io', thP', hL', hp'⟩ := h2
  have h3 := (GlobalTheory.T.conjugateLift_unique_and_baseDatum).1 R F hR i gramR c0R c0L hT σ hσ _ _ c c₁ H j c' c₁' H' j' h.2.2.1 h'.2.2.1 ω f₀ f B io thP
    ω' f₀' f' B' io' thP' hL hL'
  obtain ⟨κ, hκ, he⟩ := h3
  have hg : GoodEmb T.Q.c (res T σ) := (GlobalTheory.GalLift.overK_iff_good_ofFive T R F κw v₀ hR fw i σ).1 hσ
  let v : ∀ ρ, lowT (R.MW i σ) ρ := fun ρ => ⟨v₀ i σ ρ, ((fw.hv₀ i σ).1 ρ).2.1⟩
  let ev : (R.HW i σ).H →ₗ[ℂ] (GA D (Wc D i) → ℂ) := evL (R.HW i σ).e (v₀ i σ)
  have hev : Function.Injective ev := hI i σ hg
  refine ⟨κ, hκ, fun x => hev (Eq.trans ?_ (ev.map_smul _ _).symm)⟩
  exact (hp' (j' x) v).trans ((congrArg (R.eWf i σ) (he x _)).trans
    (((R.eWf i σ).map_smul _ _).trans (congrArg (κ • ·) (hp (j x) v).symm)))

theorem conjugateRationalLift_at_embedding_of_datum (hR : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (hI : EvInj T R v₀) (i : Fin D.R.m) {gramR c0R c0L}
    (hT : Comparison₂ R gramR c0R c0L) {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) (ph : ℂ) {μ' η' c c₁ H j th}
    (h : IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th) {u U} (hU : IsCompPhase R i σ u U) (hu : σ = sg0 D A → ∀ h, u h = 1)
    {z : G} (hz : z ∈ Subgroup.center G) {κ : ℂ} (hκ : ‖κ‖ = 1)
    (he : ∀ x y, IsRatLift R i ph x y → U ((R.FW i).j σ y) = κ • R.gW i σ z (th (j x))) : ConjAt R i σ ph (c0L i) := by
  have h1 := (GlobalTheory.T.centralShift_phase_conjReadings_fiveClauses).1 R F hR i σ z hz
  obtain ⟨ζ, hζ⟩ := h1
  refine ⟨(GlobalTheory.GalLift.hypConj_of_chars_ofFive R F hR i σ ((GlobalTheory.GalLift.labels_overK σ).1 hσ).1 ((GlobalTheory.GalLift.labels_overK σ).1 hσ).2).1, ⟨_, _, _, _, _, _, _, h⟩,
    u, U, z, ζ, hU, hu, hζ, fun μ'' η'' c' c₁' H' j' th' h' => ⟨hypConj5 hR i hσ h'.1 h'.2.1, ?_⟩⟩
  have h2 := lift_unique5 hR fw hI i hT hσ h h'
  obtain ⟨κ', hκ', e⟩ := h2
  refine ⟨κ * κ'⁻¹, by rw [norm_mul, norm_inv, hκ, hκ']; norm_num, fun x y hy => ?_⟩
  exact (he x y hy).trans (smul_inv_of (R.gW i σ z) hκ' (e x))

theorem conjAt_base5 (hR : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (hI : EvInj T R v₀) (i : Fin D.R.m) {gramR c0R c0L}
    (hT : Comparison₂ R gramR c0R c0L) {ph : ℂ} (hph : ‖ph‖ = 1) : ConjAt R i (sg0 D A) ph (c0L i) := by
  have hσ : OverK (sg0 D A) := fun x _ => congrArg (fun s : D.what₂.LL →+* ℂ => s (D.embE x)) (sign_at_base_place_eq_embedding R)
  have h1 := (GlobalTheory.T.conjugateLift_unique_and_baseDatum).2.1 T R F κw v₀ hR fw i gramR c0R c0L hT ((GlobalTheory.T.conjugateCharacters_embeddings_of_characterisation).2.1 R F hR i)
  obtain ⟨c₁, j, hd, hj⟩ := h1
  refine conjugateRationalLift_at_embedding_of_datum hR fw hI i hT hσ ph hd (u := fun _ => 1) (U := LinearIsometryEquiv.refl ℂ _)
    ⟨fun _ => norm_one, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun y v h => (one_mul _).symm⟩
    (fun _ _ => rfl) (one_mem _) hph fun x y hy => ?_
  refine Eq.trans hy (congrArg (ph • ·) ?_)
  exact (congrArg (R.thG i A.μ0) (hj x).symm).trans (LinearMap.congr_fun (map_one (R.gW i (sg0 D A))) _).symm

theorem conjugateRationalLift_at_nonBaseEmbedding (hR : GlobalTheory.Core5 R F) (fw : FWTie T R κw v₀) (i : Fin D.R.m) (hE : fw.Evaluates)
    (hI : EvInj T R v₀) (hinj : Function.Injective ((R.FW i).j (sg0 D A)))
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : ℂ) (hP : OMPins T R κw v₀ O i)
    (hO : (O i).OneMapOf (κw i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph)
    {gramR c0R c0L} (hT : Comparison₂ R gramR c0R c0L) {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) (hne : σ ≠ sg0 D A) :
    ConjAt R i σ ph (c0L i) := by
  have h0 := hP.2.lift.c0
  obtain ⟨gramR', c0R', c0L', hT', hC⟩ := h0
  have hg : GoodEmb T.Q.c (res T σ) := (GlobalTheory.GalLift.overK_iff_good_ofFive T R F κw v₀ hR fw i σ).1 hσ
  have hμ := fw.chiR i σ hg
  have h1 := (GlobalTheory.T.conjugateCharacters_embeddings_of_characterisation).2.2.1 R F hR i ((GlobalTheory.T.conjugateCharacters_embeddings_of_characterisation).2.1 R F hR i) σ hσ
  obtain ⟨η', hη⟩ := h1
  have hH := hypConj5 hR i hσ hμ hη
  have h2 := (GlobalTheory.T.conjugateLift_of_characterisationClauses).1 R F hR i gramR' c0R' c0L' hT' σ hσ
  obtain ⟨c, c₁, hc⟩ := h2
  have h3 := (GlobalTheory.T.conjugateLift_of_characterisationClauses).2.1 R F hR i gramR' c0R' c0L' hT' σ c c₁ hc
  obtain ⟨H, j, hF⟩ := h3
  have h4 := (GlobalTheory.T.conjugateCharacters_embeddings_of_characterisation).2.2.2.2.2.2.1 R F hR i σ _ η' hμ hη hH
  obtain ⟨ω, hω⟩ := h4
  have h5 := (GlobalTheory.T.conjugateLift_of_characterisationClauses).2.2.2.1 R F hR i σ hσ
  obtain ⟨f₀, f, B, hv⟩ := h5
  have h6 := GlobalTheory.MovedWeights.exists_io_conj_ofFive R F hR i σ hσ _ η' hμ hH c c₁ hc ω f₀ f B hω hv
  obtain ⟨io, hio⟩ := h6
  have h7 := (GlobalTheory.T.conjugateLift_of_characterisationClauses).2.2.2.2.1 R F hR i σ _ η' _ c c₁ H j hF ω f₀ f B io hω hv
  obtain ⟨thP, hth⟩ := h7
  have hL : LiftData R i σ _ η' c H ω f₀ f B io thP := ⟨hω, hv, hio, hth⟩
  have h8 := conj_lift5 hR fw i hE hI hinj O ph hP hO hT' hC σ hσ hμ hη hF hL
  obtain ⟨th, u, U, z, κ, hp, hU, hz, hκ, he⟩ := h8
  have h9 := (GlobalTheory.T.conjugateLift_of_characterisationClauses).2.2.1 R F hR i gramR c0R c0L hT gramR' c0R' c0L' hT' σ c c₁ H j hF
  obtain ⟨c₁', hF'⟩ := h9
  exact conjugateRationalLift_at_embedding_of_datum hR fw hI i hT hσ ph ⟨hμ, hη, hF', (isConjLift_iff R i σ _ _ _ _ _).2 ⟨ω, f₀, f, B, io, thP, hL, hp⟩⟩ hU
    (fun h => absurd h hne) hz hκ he

end Main

theorem conjRatLift5 : GlobalTheory.LowRow.ConjRatLift5 := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ O ph hR _ fw hb _ hLU hP i hO
  have hJ' := GlobalTheory.ConjReading.jEvExists_and_jEvBar T R κw v₀ O hR.lev hR.models fw hP
  have hI : EvInj T R v₀ := GlobalTheory.EvalAtUnitVectorFinal.evInj_of_isModels_of_tie T R κw v₀ hR.models fw
  have hE : fw.Evaluates := fw.evaluates hJ'.1
  have hinj : Function.Injective ((R.FW i).j (sg0 D A)) := GlobalTheory.GalOne.inj_of_indep _ (hLU i (sg0 D A)).1
  refine ⟨fun x => ?_, fun gramR c0R c0L hT σ hσ => ?_, fun σ hσ => ⟨(GlobalTheory.GalLift.labels_overK σ).2 hσ, ?_⟩⟩
  · obtain ⟨h, hh⟩ := exists_reps (hP i)
    obtain ⟨act, z, ze, -, -, -, hx⟩ := base_lift5 hR fw i hE hI O ph (hP i) hO h hh
    obtain ⟨n, a, f, -, hy⟩ := hx x
    exact ⟨_, hy, fun y hy' => hinj (Eq.trans hy' (Eq.symm hy))⟩
  · by_cases hs : σ = sg0 D A
    · subst hs
      exact conjAt_base5 hR fw hI i hT hO.2.1.2.2.2.2.1
    · exact conjugateRationalLift_at_nonBaseEmbedding hR fw i hE hI hinj O ph (hP i) hO hT hσ hs
  · exact (GlobalTheory.T.centralShift_phase_conjReadings_fiveClauses).2.2 T R F κw v₀ hR fw i hJ'.1 hJ'.2 hb σ fun hg =>
      hσ ((GlobalTheory.GalLift.overK_iff_good_ofFive T R F κw v₀ hR fw i σ).2 hg)

end GlobalTheory.ConjRatLiftFive

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportedWeilOperatorGroupVariable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.WeilCont

theorem continuous_transport_apply : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ z : κ → AF D.host.F, Continuous fun p => om p Φ z := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ _ co hco ω hω om htr Φ hΦ z
  have hth := GlobalTheory.T.thetaTransform_transportedWeil_continuous D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr Φ hΦ
  refine continuous_iff_continuousAt.2 fun p0 => ?_
  obtain ⟨N, hN, m, g, y, hg, hy, hf⟩ :=
    GlobalTheory.T.exists_local_finiteDim_finiteParts_weilOperators D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr Φ hΦ p0
  let f : _ → Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ :=
    fun p => if h : p ∈ N then Classical.choose (hf p h) else 0
  have hfe : ∀ p ∈ N, om p Φ = ∑ i, GlobalTheory.WeilM.pureA D.host.F (f p i) (g i) := fun p hp => by
    simp only [f, dif_pos hp]
    exact Classical.choose_spec (hf p hp)
  have hslice : ∀ p ∈ N, ∀ i v, f p i v = om p Φ (GlobalTheory.WeilCont.adeleJoin D.host.F v (y i)) := by
    intro p hp i v
    rw [hfe p hp, Finset.sum_apply, Finset.sum_eq_single i]
    · rw [GlobalTheory.WeilCont.pureA_adeleJoin, hy, if_pos rfl, mul_one]
    · intro j _ hji
      rw [GlobalTheory.WeilCont.pureA_adeleJoin, hy, if_neg hji, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hbd : ∀ k : ℕ, ∃ C : ℝ, ∀ᶠ p in nhds p0, ∀ i v, ‖v‖ ^ k * ‖f p i v‖ ≤ C := by
    intro k
    choose C hC using fun i =>
      GlobalTheory.T.weilOperator_archimedeanSlice_schwartzSeminorm_bounded D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr Φ hΦ (y i) p0 k 0
    refine ⟨∑ i, |C i|, ?_⟩
    filter_upwards [Filter.eventually_all.2 hC, hN] with p hp hpN i v
    have h1 := hp i v
    rw [norm_iteratedFDeriv_zero] at h1
    rw [hslice p hpN i v]
    exact h1.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))
  obtain ⟨M, hM, hMb⟩ := GlobalTheory.T.exists_summableMajorant_adelicSchwartz_locallyUniform D.host.F κ (fun p => om p Φ) p0 m g f hg
    (Filter.eventually_of_mem hN fun p hp => hfe p hp) hbd z
  let e : (κ → D.host.F) → AddChar (κ → AF D.host.F) ℂ := fun a =>
    ψ.compAddMonoidHom (AddMonoidHom.mk' (fun y => (fun i => algebraMap D.host.F (AF D.host.F) (a i)) ⬝ᵥ y)
      (fun y y' => dotProduct_add _ y y'))
  have he : ∀ a y, e a y = ψ ((fun i => algebraMap D.host.F (AF D.host.F) (a i)) ⬝ᵥ y) := fun a y => rfl
  have hform : ∀ p y', GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (om p Φ) (co.e.symm (z, y')) =
      ψ (⅟(2 : AF D.host.F) * (z ⬝ᵥ y')) * ∑' a, e a y' * om p Φ (fun j => algebraMap D.host.F (AF D.host.F) (a j) + z j) := by
    intro p y'
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr,
      LinearEquiv.apply_symm_apply, he]
    rw [← tsum_mul_left]
    refine tsum_congr fun a => ?_
    simp only [AddChar.map_add_eq_mul, Pi.add_def]
    ring
  have h0 : ∀ y, e 0 y = 1 := fun y => by
    rw [he]
    simp
  have hne : ∀ a : κ → D.host.F, a ≠ 0 → ∃ y, e a y ≠ 1 := by
    intro a ha
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
    obtain ⟨x0, hx0⟩ := hψ.1.2.2.2
    refine ⟨Pi.single i (algebraMap D.host.F (AF D.host.F) (a i)⁻¹ * x0), ?_⟩
    rw [he, dotProduct_single, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
    exact hx0
  have hψinv : ∀ t : AF D.host.F, ψ (-t) * ψ t = 1 := fun t => by
    simpa using (AddChar.map_add_eq_mul ψ (-t) t).symm
  have hc : ∀ y', ContinuousAt (fun p => ∑' a, e a y' * om p Φ (fun j => algebraMap D.host.F (AF D.host.F) (a j) + z j)) p0 := by
    intro y'
    have h2 : ∀ p, ψ (-(⅟(2 : AF D.host.F) * (z ⬝ᵥ y'))) *
          GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (om p Φ) (co.e.symm (z, y')) =
        ∑' a, e a y' * om p Φ (fun j => algebraMap D.host.F (AF D.host.F) (a j) + z j) := by
      intro p
      simp only [hform, ← mul_assoc, hψinv, one_mul]
    exact ((continuous_const.mul (hth _)).continuousAt).congr (Filter.Eventually.of_forall h2)
  have hL := GlobalTheory.T.continuousAt_coeff_zero_of_continuousAt_char_series e (fun a y => hψ.1.2.1 _) h0 hne _ p0 M hM hMb hc
  simpa using hL

end GlobalTheory.WeilCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorFittedIdentityStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.denominator_fitted_identity : SetAt → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → DenSum → Den @Comparison₂ := by
  first | exact @GlobalTheory.BigTop.Fun.den_tie | exact GlobalTheory.BigTop.Fun.den_tie | (intros; apply GlobalTheory.BigTop.Fun.den_tie <;> assumption)
end

