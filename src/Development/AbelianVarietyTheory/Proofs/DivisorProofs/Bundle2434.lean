import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimPreservedOfEqualLocalRelDims
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalHypothesisInHalfGeometry
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.UnframePt.inGeo_geoHalf : GlobalTheory.Published.CuspRapidDecay → ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x)
    (i : Fm.Ix x) (p : Pt Fm x hx i), p.Rows → More p → ∀ (t : (Fm.D x i).ntw.Tw) (j : Fin (Fm.D x i).R.m),
    RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j → InGeo (geoHalf p) := by
  intro hDec eps Fm x hx i p hR _hM t j h0
  have hJ : JEvExists p.T p.R.toRealDat p.κ p.v₀ :=
    GlobalTheory.ConjReading.jEvExists p.T p.R.toRealDat p.κ p.v₀ p.O h0.core.lev h0.core.models p.fw p.pins
  exact
    { jEvExists := hJ
      jEvBar := hR.jEvBar
      evInj := hR.evInj
      jUnif := GlobalTheory.ReadingSpan.jUnif hDec _ _ _ _ _ p.T p.R.toRealDat p.κ p.v₀ h0.core.lev h0.core.models h0.tieIn
        hR.ties.pb hJ hR.jEvBar hR.evInj h0.size
      geoAct := hR.geoAct
      latFull := GlobalTheory.IntCuspLat.latFull_of_tie p.fw
      dimMatch := p.fw.dimMatch }

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTensorVanishingLocal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem affine_restrictions_zero_of_minimalPrimes_over :
    ∀ (M : Scheme.{0}) (V W : M.Opens) (hW : IsAffineOpen W) (K : Type) [Field K],
    IsReduced (Γ(M, W) ⊗[ℤ] K) →
    (∀ q (hq : q ∈ minimalPrimes (Γ(M, W) ⊗[ℤ] K)),
      hW.fromSpec (PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := Γ(M, W)) (B := K)) ⟨q, hq.1.1⟩) ∈ V) →
    ∀ (h : Γ(M, W) ⊗[ℤ] K),
    (∀ (W' : M.Opens), IsAffineOpen W' → ∀ hW' : W' ≤ W ⊓ V,
      LinearMap.rTensor K (M.presheaf.map (homOfLE (hW'.trans inf_le_left)).op).hom.toAddMonoidHom.toIntLinearMap h = 0) →
    h = 0 := by
  intro M V W hW K _ hred hV h hh
  have key : ∀ q ∈ minimalPrimes (Γ(M, W) ⊗[ℤ] K), h ∈ q := by
    intro q hq
    haveI : q.IsPrime := hq.1.1
    set p : PrimeSpectrum Γ(M, W) := PrimeSpectrum.comap (Algebra.TensorProduct.includeLeftRingHom
      (R := ℤ) (A := Γ(M, W)) (B := K)) ⟨q, hq.1.1⟩ with hp
    have hxW : hW.fromSpec p ∈ W := by
      have h1 : hW.fromSpec p ∈ Set.range hW.fromSpec := ⟨p, rfl⟩
      rwa [hW.range_fromSpec] at h1
    have hxV : hW.fromSpec p ∈ V := hV q hq
    obtain ⟨f, hfle, hxf⟩ := hW.exists_basicOpen_le (V := W ⊓ V) ⟨hW.fromSpec p, hxW, hxV⟩ hxW
    have hfp : f ⊗ₜ[ℤ] (1 : K) ∉ q := by
      have h1 : p ∈ hW.fromSpec ⁻¹ᵁ M.basicOpen f := hxf
      rw [hW.fromSpec_preimage_basicOpen] at h1
      exact h1
    have h0 := hh (M.basicOpen f) (hW.basicOpen f) hfle
    let φ : Γ(M, W) →+* Γ(M, M.basicOpen f) :=
      (M.presheaf.map (homOfLE (hfle.trans inf_le_left)).op).hom
    letI : Algebra Γ(M, W) Γ(M, M.basicOpen f) := φ.toAlgebra
    haveI : IsLocalization.Away f Γ(M, M.basicOpen f) := hW.isLocalization_basicOpen f
    let g0 : Γ(M, W) →+* Localization.AtPrime q :=
      (algebraMap (Γ(M, W) ⊗[ℤ] K) (Localization.AtPrime q)).comp
        Algebra.TensorProduct.includeLeftRingHom
    have hu : IsUnit (g0 f) :=
      IsLocalization.map_units (M := q.primeCompl) (Localization.AtPrime q) ⟨f ⊗ₜ[ℤ] (1 : K), hfp⟩
    let g1 : Γ(M, M.basicOpen f) →+* Localization.AtPrime q := IsLocalization.Away.lift f hu
    let g2 : K →+* Localization.AtPrime q :=
      (algebraMap (Γ(M, W) ⊗[ℤ] K) (Localization.AtPrime q)).comp
        Algebra.TensorProduct.includeRight.toRingHom
    let G : Γ(M, M.basicOpen f) ⊗[ℤ] K →ₐ[ℤ] Localization.AtPrime q :=
      Algebra.TensorProduct.lift (⟨g1, fun n => by simp⟩ : Γ(M, M.basicOpen f) →ₐ[ℤ] Localization.AtPrime q)
        (⟨g2, fun n => by simp⟩ : K →ₐ[ℤ] Localization.AtPrime q) (fun _ _ => Commute.all _ _)
    have hG : ∀ z : Γ(M, W) ⊗[ℤ] K,
        G (LinearMap.rTensor K φ.toAddMonoidHom.toIntLinearMap z) =
          algebraMap (Γ(M, W) ⊗[ℤ] K) (Localization.AtPrime q) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a k =>
        rw [LinearMap.rTensor_tmul]
        have e1 : g1 (φ a) = g0 a := IsLocalization.Away.lift_eq f hu a
        change g1 (φ a) * g2 k = _
        rw [e1]
        simp only [g0, g2, RingHom.comp_apply, ← map_mul]
        congr 1
        simp
      | add x y hx hy => simp only [map_add, hx, hy]
    have hz : algebraMap (Γ(M, W) ⊗[ℤ] K) (Localization.AtPrime q) h = 0 := by
      rw [← hG h]
      change G (LinearMap.rTensor K φ.toAddMonoidHom.toIntLinearMap h) = 0
      rw [h0, map_zero]
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ h).1 hz
    have hmq : (m : Γ(M, W) ⊗[ℤ] K) * h ∈ q := by rw [hm]; exact q.zero_mem
    exact (‹q.IsPrime›.mem_or_mem hmq).resolve_left m.2
  have hrad : h ∈ (⊥ : Ideal (Γ(M, W) ⊗[ℤ] K)).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact Submodule.mem_sInf.mpr key
  obtain ⟨n, hn⟩ := hrad
  exact IsNilpotent.eq_zero ⟨n, Ideal.mem_bot.mp hn⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedHomAlgebraMap
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential Opposite MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InvForm

variable {R : Type} [CommRing R]

section Val

variable {B D : Type} [CommRing B] [Algebra R B] [CommRing D] [Algebra R D]

abbrev redHom (φ : B →ₐ[R] DualNumber D) : B →+* D :=
  (TrivSqZeroExt.fstHom R D D).toRingHom.comp φ.toRingHom

theorem redHom_algebraMap (φ : B →ₐ[R] DualNumber D) (r : R) :
    redHom φ (algebraMap R B r) = algebraMap R D r := by
  simp [redHom, TrivSqZeroExt.algebraMap_eq_inl']

def dVal (φ : B →ₐ[R] DualNumber D) : Ω[B⁄R] →ₗ[R] D :=
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  let d : Derivation R B D :=
    { toFun := fun b ↦ (φ b).snd
      map_add' := fun a b ↦ by simp
      map_smul' := fun r b ↦ by
        rw [map_smul, TrivSqZeroExt.snd_smul]
        rfl
      map_one_eq_zero' := by simp
      leibniz' := fun a b ↦ by
        change (φ (a * b)).snd = (φ a).fst * (φ b).snd + (φ b).fst * (φ a).snd
        rw [map_mul, TrivSqZeroExt.snd_mul]
        simp [MulOpposite.smul_eq_mul_unop]
        ring }
  d.liftKaehlerDifferential.restrictScalars R

theorem dVal_D (φ : B →ₐ[R] DualNumber D) (b : B) : dVal φ (KaehlerDifferential.D R B b) = (φ b).snd := by
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  exact Derivation.liftKaehlerDifferential_comp_D _ b

end Val

variable (A : Over (Sp R)) [GrpObj A]

def IsInv (w : GlobForm A.hom) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (U V : A.left.affineOpens)
    (φ : Sec A.hom U.1 →ₐ[R] DualNumber D) (ψ : Sec A.hom V.1 →ₐ[R] DualNumber D)
    (p q : Over.mk (spMap (algebraMap R (DualNumber D))) ⟶ A) (q₀ : Sp D ⟶ A.left),
    p.left = spMap (φ : Sec A.hom U.1 →+* DualNumber D) ≫ affPt A.hom U →
    q.left = spMap (algebraMap D (DualNumber D)) ≫ q₀ →
    (p * q).left = spMap (ψ : Sec A.hom V.1 →+* DualNumber D) ≫ affPt A.hom V →
    dVal φ (w.1 (op U)) = dVal ψ (w.1 (op V))

def InvForm : Submodule R (GlobForm A.hom) where
  carrier := {w | IsInv A w}
  add_mem' {w w'} hw hw' D _ _ U V φ ψ p q q₀ hp hq hpq := by
    change dVal φ (w.1 (op U) + w'.1 (op U)) = dVal ψ (w.1 (op V) + w'.1 (op V))
    rw [map_add, map_add, hw D U V φ ψ p q q₀ hp hq hpq, hw' D U V φ ψ p q q₀ hp hq hpq]
  zero_mem' D _ _ U V φ ψ p q q₀ _ _ _ := by
    change dVal φ 0 = dVal ψ 0
    rw [map_zero, map_zero]
  smul_mem' r w hw D _ _ U V φ ψ p q q₀ hp hq hpq := by
    change dVal φ (r • w.1 (op U)) = dVal ψ (r • w.1 (op V))
    rw [map_smul, map_smul, hw D U V φ ψ p q q₀ hp hq hpq]

end GlobalTheory.InvForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedEquationPullbackEtaleOverAffineSpaceStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedEquation_pullback_unitLocus_divides_vanishing : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X] (q : Y ⟶ X) (ι : Type) [Finite ι] (Vo : X.Opens) (U U' : X.affineOpens) (hU' : U'.1 ≤ U.1) (W : Y.Opens), IsAffineOpen W → ∀ (hWU : W ≤ q ⁻¹ᵁ U.1) (N : ι → Γ(Y, W)), (MvPolynomial.eval₂Hom (q.appLE U.1 W hWU).hom N).Etale → ∀ (δ : Γ(X, U.1)), (Scheme.IdealSheafData.vanishingIdeal Vo.compl).ideal U' = Ideal.span {resG X hU' δ} → (∀ (z : Y) (hz : z ∈ W), q z ∈ U'.1 → (IsUnit (ger z hz ((q.appLE U.1 W hWU).hom δ)) ↔ q z ∈ Vo)) ∧ ∀ (W' : Y.Opens) (hW' : W' ≤ W), W' ≤ q ⁻¹ᵁ U'.1 → ∀ f : Γ(Y, W'), (∀ (z : Y) (hz : z ∈ W'), q z ∉ Vo → ger z hz f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk z)) → ∀ (z : Y) (hz : z ∈ W'), ger z (hW' hz) ((q.appLE U.1 W hWU).hom δ) ∣ ger z hz f := by
  first | exact @GlobalTheory.EtaleReducedEq.reducedEq_pullback_etale | exact GlobalTheory.EtaleReducedEq.reducedEq_pullback_etale | (intros; apply GlobalTheory.EtaleReducedEq.reducedEq_pullback_etale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceTupleLiftsSpanAllTuplesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceTuple_lifts_span_all_tuples : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → OMPins T R κ v₀ O i → OneMapRow0 T R κ v₀ O i → QGuard R → GlobalTheory.OneMapTuples.LiftsSpan R i (v₀ i (sg0 D A)) := by
  first | exact @GlobalTheory.LiftSpanClauses.liftsSpan_all_clauses | exact GlobalTheory.LiftSpanClauses.liftsSpan_all_clauses | (intros; apply GlobalTheory.LiftSpanClauses.liftsSpan_all_clauses <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataRescaleCoboundary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

theorem rescale_tau_val {R' : Type} [CommRing R'] [IsDomain R'] (D : DegPre R') (g : D.X → (FractionRing R')ˣ)
    (a b : D.X) {z : (TK R').left} {J : ((TK R').left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) :
    val ((rescale D g).tau a b) (𝟙 _) z J =
      gm (𝟙 (TK R').left) z ⊤ (unitOn (g (a + b))) * (gm (𝟙 (TK R').left) z ⊤ (unitOn (g a)))⁻¹ *
        (gm (𝟙 (TK R').left) z ⊤ (unitOn (g b)))⁻¹ * val (D.tau a b) (𝟙 _) z J := by
  have hJ' : Good (rescale D g).P.L z J := hJ
  unfold DegPre.tau
  simp only [val_mul hJ', val_mul hJ, val_inv]
  erw [val_inv, val_inv, val_inv]
  have e1 : ∀ χ, val ((rescale D g).psi χ) (𝟙 _) z J = gm (𝟙 (TK R').left) z ⊤ (unitOn (g χ)) * val (D.psi χ) (𝟙 _) z J :=
    fun χ => GlobalTheory.UU.val_scaleGen _ _ _ hJ
  have e2 : val (rescale D g).rigK (𝟙 _) z J = val D.rigK (𝟙 _) z J := rfl
  erw [e1 (a + b), e1 a, e1 b, e2]
  simp only [mul_inv]
  ac_rfl

theorem half_rescale : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (f f' : D.X → D.X → (FractionRing R')ˣ) (g : D.X → (FractionRing R')ˣ), Half Q ρ D e f → (∀ a b, f a b = g (a + b) * (g a)⁻¹ * (g b)⁻¹ * f' a b) → Half Q ρ (rescale D g) e f' := by
  intro R _ _ R' _ _ Q ρ D e f f' g h hf
  obtain ⟨β, β₂, w, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  refine ⟨β, β₂, w, h₁, h₂, h₃, h₄, h₅, fun κ hκ a b z J J' hJ hJ' => ?_⟩
  have H := h₆ κ hκ a b z J J' hJ hJ'
  have E := rescale_tau_val D g a b hJ'
  have key : ∀ x y : D.X, gm (𝟙 (TK R').left) z ⊤ (unitOn (f x y)) = gm (𝟙 (TK R').left) z ⊤ (unitOn (g (x + y))) *
      (gm (𝟙 (TK R').left) z ⊤ (unitOn (g x)))⁻¹ * (gm (𝟙 (TK R').left) z ⊤ (unitOn (g y)))⁻¹ *
        gm (𝟙 (TK R').left) z ⊤ (unitOn (f' x y)) := fun x y => by
    rw [hf x y]; simp only [unitOn, map_mul, map_inv]
  erw [E]
  refine Eq.trans ?_ H
  erw [key a b]
  ac_rfl

end GlobalTheory.PolDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAndUnitPreservedByFunctionFieldCompatible
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Desc.StalkMap

variable {X : Scheme.{0}}

theorem top_le_fromSpecStalk (x : X) (U : X.Opens) (hx : x ∈ U) : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
  intro z _
  have hz : X.fromSpecStalk x z ⤳ x := by
    have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact hz.mem_open U.2 hx

theorem appLE_fromSpecStalk (x : X) (U : X.Opens) (hx : x ∈ U) :
    (X.fromSpecStalk x).appLE U ⊤ (top_le_fromSpecStalk x U hx) =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp]
  have e : ((homOfLE le_top).op ≫ (homOfLE (top_le_fromSpecStalk x U hx)).op :
      Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id, Category.comp_id]

def val {R : Type} [CommRing R] (g : Sp R ⟶ X) (V : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V) : Γ(X, V) →+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (g.appLE V ⊤ h).hom

theorem val_congr {R : Type} [CommRing R] {g g' : Sp R ⟶ X} (e : g = g') (V : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V)
    (h' : ⊤ ≤ g' ⁻¹ᵁ V) (u : Γ(X, V)) : val g V h u = val g' V h' u := by
  subst e; rfl

theorem val_gp [IsIntegral X] (V : X.Opens) (hV : genericPoint X ∈ V) (h : ⊤ ≤ gp X ⁻¹ᵁ V) (u : Γ(X, V)) :
    val (gp X) V h u = GlobalTheory.Cartier.fnOf V hV u := by
  have : (gp X).appLE V ⊤ h = X.presheaf.germ V _ hV ≫ (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).inv :=
    appLE_fromSpecStalk (genericPoint X) V hV
  unfold val
  rw [RingHom.comp_apply, this]
  exact (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).inv_hom_id_apply _

end GlobalTheory.Desc.StalkMap

namespace GlobalTheory.Desc.StalkMap

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem val_appLE (g : Sp R ⟶ X) (φ : X ⟶ X') (V : X'.Opens) (W : X.Opens) (e : W ≤ φ ⁻¹ᵁ V)
    (h : ⊤ ≤ g ⁻¹ᵁ W) (h' : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ V) (u : Γ(X', V)) :
    val g W h ((φ.appLE V W e).hom u) = val (g ≫ φ) V h' u :=
  congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (CommRingCat.Hom.hom q u))
    (Scheme.Hom.appLE_comp_appLE g φ V W ⊤ e h)

theorem val_top (g : Sp R ⟶ X) (h : ⊤ ≤ g ⁻¹ᵁ ⊤) (u : Γ(X, ⊤)) :
    val g ⊤ h u = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (g.appTop.hom u) := by
  have : g.appLE ⊤ ⊤ h = g.appTop := Scheme.Hom.appLE_eq_app g
  exact congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (CommRingCat.Hom.hom q u)) this

theorem val_spMap (σ : R →+* R') (g : Sp R ⟶ X) (V : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V)
    (h' : ⊤ ≤ (spMap σ ≫ g) ⁻¹ᵁ V) (u : Γ(X, V)) : val (spMap σ ≫ g) V h' u = σ (val g V h u) := by
  refine (val_appLE (spMap σ) g V ⊤ h le_top h' u).symm.trans ((val_top (spMap σ) le_top _).trans ?_)
  exact congrArg (fun q => CommRingCat.Hom.hom q ((g.appLE V ⊤ h).hom u))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ))

theorem fnOf_app_eq {Y P : Scheme.{0}} [IsIntegral Y] [IsIntegral P] (m : Y ⟶ P)
    (φ : P.functionField →+* Y.functionField) (hm : gp Y ≫ m = spMap φ ≫ gp P) {W : P.Opens}
    (hY : genericPoint Y ∈ m ⁻¹ᵁ W) (hP : genericPoint P ∈ W) (s : Γ(P, W)) :
    GlobalTheory.Cartier.fnOf (m ⁻¹ᵁ W) hY ((m.app W).hom s) = φ (GlobalTheory.Cartier.fnOf W hP s) := by
  have h1 : ⊤ ≤ gp Y ⁻¹ᵁ (m ⁻¹ᵁ W) := top_le_fromSpecStalk _ _ hY
  have h2 : ⊤ ≤ gp P ⁻¹ᵁ W := top_le_fromSpecStalk _ _ hP
  have h3 : ⊤ ≤ (gp Y ≫ m) ⁻¹ᵁ W := h1
  have h4 : ⊤ ≤ (spMap φ ≫ gp P) ⁻¹ᵁ W := hm ▸ h3
  rw [← val_gp _ hY h1, ← val_gp _ hP h2, ← val_spMap φ (gp P) W h2 h4,
    ← val_congr hm W h3 h4, ← val_appLE (gp Y) m W (m ⁻¹ᵁ W) le_rfl h1 h3, Scheme.Hom.app_eq_appLE]

end GlobalTheory.Desc.StalkMap

open GlobalTheory.Desc.StalkMap in

theorem GlobalTheory.Desc.regAt_map_of_gp : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [IsIntegral P] (m : Y ⟶ P)
    (φ : P.functionField →+* Y.functionField), gp Y ≫ m = spMap φ ≫ gp P → ∀ (y : Y) (v : P.functionField),
    RegAt (m y) v → RegAt y (φ v) ∧ (UnitAt y (φ v) ↔ UnitAt (m y) v) := by
  intro Y P _ _ m φ hm y v hv
  obtain ⟨W, hW, s, rfl⟩ := hv.exists_fnOf
  have hy : y ∈ m ⁻¹ᵁ W := hW
  have hY : genericPoint Y ∈ m ⁻¹ᵁ W := gen_mem hy
  rw [← fnOf_app_eq m φ hm hY (gen_mem hW) s]
  refine ⟨regAt_fnOf hy hY _, ?_⟩
  rw [unitAt_fnOf_iff hy hY, unitAt_fnOf_iff hW (gen_mem hW), ← Scheme.preimage_basicOpen]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtPointFunctionFieldMapOfGenericPointComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.RegPull

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem germ_gp (V : Y.Opens) (hY : genericPoint Y ∈ V) (h : gp Y (closedPoint _) ∈ V) :
    Y.presheaf.germ V (gp Y (closedPoint _)) h ≫ Scheme.stalkClosedPointTo (gp Y) =
      Y.presheaf.germ V (genericPoint Y) hY := by
  have hC : ∀ G : Spec (Y.presheaf.stalk (genericPoint Y)) ⟶ Y,
      G = Spec.map (𝟙 _) ≫ Y.fromSpecStalk (genericPoint Y) → ∀ h,
      Y.presheaf.germ V (G (closedPoint _)) h ≫ Scheme.stalkClosedPointTo G =
        Y.presheaf.germ V (genericPoint Y) hY ≫ 𝟙 _ := by
    rintro G rfl h
    exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (𝟙 _) V h
  have e : gp Y = Spec.map (𝟙 _) ≫ Y.fromSpecStalk (genericPoint Y) := by
    rw [Spec.map_id, Category.id_comp]; rfl
  exact (hC (gp Y) e h).trans (Category.comp_id _)

theorem fnOf_map (π : Y ⟶ X) (θ : X.functionField →+* Y.functionField)
    (e : gp Y ≫ π = spMap θ ≫ gp X) (U : X.Opens) (hX : genericPoint X ∈ U)
    (hY : genericPoint Y ∈ π ⁻¹ᵁ U) (s : Γ(X, U)) :
    θ (fnOf U hX s) = fnOf (π ⁻¹ᵁ U) hY (π.app U s) := by
  have hA : ∀ F : Sp Y.functionField ⟶ X, F = spMap θ ≫ gp X → ∀ hU,
      X.presheaf.germ U (F (closedPoint _)) hU ≫ Scheme.stalkClosedPointTo F =
        X.presheaf.germ U (genericPoint X) hX ≫ CommRingCat.ofHom θ := by
    rintro F rfl hU
    exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk (CommRingCat.ofHom θ) U hU
  have hg : gp Y (closedPoint _) = genericPoint Y := Scheme.fromSpecStalk_closedPoint
  have hV : gp Y (closedPoint _) ∈ π ⁻¹ᵁ U := by rw [hg]; exact hY
  have hB : ∀ F : Sp Y.functionField ⟶ X, F = gp Y ≫ π → ∀ hU,
      X.presheaf.germ U (F (closedPoint _)) hU ≫ Scheme.stalkClosedPointTo F =
        π.app U ≫ Y.presheaf.germ (π ⁻¹ᵁ U) (genericPoint Y) hY := by
    rintro F rfl hU
    rw [Scheme.stalkClosedPointTo_comp]
    refine (Scheme.Hom.germ_stalkMap_assoc π U (gp Y (closedPoint _)) hV _).trans ?_
    exact congrArg (π.app U ≫ ·) (germ_gp (π ⁻¹ᵁ U) hY hV)
  have := (hA _ e hV).symm.trans (hB _ rfl hV)
  exact congrArg (fun g => g.hom s) this

theorem regAt_map (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    (θ : X.functionField →+* Y.functionField) (hθ : PFF (𝟙 _) π θ) (y : Y) (u : X.functionField)
    (hu : RegAt (π y) u) : RegAt y (θ u) := by
  obtain ⟨l, hl, e⟩ := hθ
  rw [Category.comp_id] at hl
  subst hl
  obtain ⟨U, hx, s, rfl⟩ := hu.exists_fnOf
  have hy : y ∈ π ⁻¹ᵁ U := hx
  rw [fnOf_map π θ e U _ (gen_mem hy) s]
  exact regAt_fnOf hy _ _

end GlobalTheory.Desc.RegPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfGenericPrincipal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericAmpleDvr

theorem triv_theta {S : Scheme.{0}} [IsLocallyNoetherian S] {A : Over S} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) : AbLaw.Triv (Theta A L) :=
  CubeNoeth.triv_of_faces allSixLaws.1.globalFns hA hL (thφ A (x3 A)) thε
    (fun r i b h => AbLaw.CubeGen.trivAt_of_formal hL r (AbLaw.CubeGen.prod_face r i b h))
    (fun r b h => AbLaw.CubeGen.prod_face r 0 b h)

theorem relAmple_of_generic_principal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (G : Over (Sp V)) [GrpObj G] (A : Over (Sp (FractionRing V))) [GrpObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (LA : LB A.left) (ψ : LB.Iso LA (L.pull φ)), IsAbelianScheme G → IsAbelianScheme A → L.IsLB → LA.IsLB → IsGrpPullback A G (jK V) φ → ψ.IsGen → RelAmple A LA → KTriv A LA → RelAmple G L := by
  intro V _ _ _ _ _ G _ A _ φ L LA ψ hG _ hL hLA h hψ ha hk
  have := hG.comm
  have hr : Rigidified G L := DVR.exists_gen_of_isLB_local (V := V) _ (pull_isLB hL _)
  obtain ⟨M, rfl, ⟨c⟩⟩ := Moduli.cubicalStr_of_triv_theta allSixLaws.1 _ G hG L hL hr (triv_theta hG hL)
  exact GoodPol.relAmple_of_generic allSixLaws.1 hG c h hLA ⟨ψ, hψ⟩ ha hk

end GlobalTheory.GenericAmpleDvr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimPreservedOfEqualLocalRelDimsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relDimPreserved_of_equal_local_relDims : ∀ (S : Scheme.{0}) (A B : Over S), Surjective A.hom → ∀ (Ix : Type) (V : Ix → S.Opens) (g : Ix → ℕ), (∀ s : S, ∃ i, s ∈ V i) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd A.hom (V i).ι)) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd B.hom (V i).ι)) → DimLe A B := by
  first | exact @GlobalTheory.DualCon.dimLe_of_local | exact GlobalTheory.DualCon.dimLe_of_local | (intros; apply GlobalTheory.DualCon.dimLe_of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentingAdditiveFamiliesIsDualCommStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representing_additiveFamilies_isDual_comm : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] (P : LB (A ⊗ B).left), Rep A (toUnit B) P → ∃ _ : GrpObj B, IsCommMonObj B ∧ IsDual A B P ∧ IsAdditive (swap P) := by
  first | exact @GlobalTheory.DualCon.rep_isDual | exact GlobalTheory.DualCon.rep_isDual | (intros; apply GlobalTheory.DualCon.rep_isDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsAdditiveLineBundleFamiliesUniqueIsoStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representsAdditiveLineBundleFamilies_unique_iso : ∀ (S : Scheme.{0}) (A B B' S' : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (b' : B' ⟶ S') (P' : LB (A ⊗ B').left), Rep A b P → Rep A b' P' → ∃ e : B ≅ B', e.hom ≫ b' = b ∧ Same A P P' (𝟙 B) e.hom := by
  first | exact @GlobalTheory.DualCon.rep_unique | exact GlobalTheory.DualCon.rep_unique | (intros; apply GlobalTheory.DualCon.rep_unique <;> assumption)
end

