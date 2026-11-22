import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3679
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3680
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3675
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointLogKodairaSpencerFrameChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3626
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3370
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3477
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3661
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.Torsor
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2430
import Development.AutomorphicArithmetic.CommutativeAlgebra.AlgHTDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3419
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0731
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0802
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjCorrespondenceTargetFiniteEtal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3673

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantAtStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_triangle_constant_at : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall → GlobalTheory.SqTop.LNe →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ),
      IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      c0 t ≠ 0 ∧ c0 μ₀ ≠ 0 ∧ ∃ γ : D.what₂.LL, D.what₂.embLL γ * c0 μ₀ = c0 t := by
  first | exact @GlobalTheory.BotRatio.bottomConst_ratio | exact GlobalTheory.BotRatio.bottomConst_ratio | (intros; apply GlobalTheory.BotRatio.bottomConst_ratio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalFamilyThroughDegeneratingFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_canonical_family_through_degenerating_family : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V), Nontrivial C.P.D.toPre.X → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C₁ : MonoFam Xo c φ (ChartRing k m e)) (θ : ChartRing k m e →+* V), Nonempty (Canon C₁) ∧ (∃ hm : C₁.m = m, ∀ i, C₁.s i = bdParam k m e (Fin.cast hm i)) ∧ IsLocalHom θ ∧ Through C C₁ θ := by
  first | exact @GlobalTheory.UCanon.exists_canon_through | exact GlobalTheory.UCanon.exists_canon_through | (intros; apply GlobalTheory.UCanon.exists_canon_through <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalMumfordFamilyMonomialPeriodsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_canonical_mumford_family_monomial_periods : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ Q : Data R, Q.IsPos (maximalIdeal R) → ∀ (m : ℕ) (t : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ Q.X), Q.IsMonomialTau t β → (∀ i, t i ≠ 0) → (∀ i y z, β i y z = β i z y) → (∀ i y, 0 ≤ β i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (P : LB (G2 G).left), IsMumPol Q G P ∧ CanonOn Q (PrimeSpectrum.basicOpen (∏ i, t i)) G P := by
  first | exact @GlobalTheory.Mum.exists_canonOn_of_isMonomialTau | exact GlobalTheory.Mum.exists_canonOn_of_isMonomialTau | (intros; apply GlobalTheory.Mum.exists_canonOn_of_isMonomialTau <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorOfStageTriangle
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StageFactor

open MeasureTheory

variable {D : D7} {T : Type} {A A' WW : HSp D}

theorem ker_add_smul (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (t : T)
    (P Q : PolF D WW.rank A.rank) (c : ℂ) (h : GA D WW) :
    X.ker ψ θ t (P + c • Q) h = fun g => X.ker ψ θ t P h g + c * X.ker ψ θ t Q h g := by
  funext g
  simp [Tri.ker, thetaKO, map_add, map_smul]

def linI (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (t : T)
    (hint : ∀ P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m) : PolF D WW.rank A.rank →ₗ[ℂ] (GA D WW → ℂ) where
  toFun P := X.I ψ θ t P
  map_add' P Q := by
    funext h
    have e := ker_add_smul X ψ θ t P Q 1 h
    simp only [one_smul, one_mul] at e
    simp only [Tri.I, Pi.add_apply, e]
    exact integral_add (hint P h) (hint Q h)
  map_smul' c Q := by
    funext h
    have e := ker_add_smul X ψ θ t 0 Q c h
    simp only [zero_add] at e
    have e0 : X.ker ψ θ t 0 h = 0 := by funext g; simp [Tri.ker, thetaKO]
    simp only [Tri.I, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, e, e0, Pi.zero_apply, zero_add]
    exact integral_const_mul c _

theorem linI_apply (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (t : T)
    (hint : ∀ P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m) (P : PolF D WW.rank A.rank) :
    linI X ψ θ t hint P = X.I ψ θ t P := rfl

theorem factor_of_parts (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (hint : ∀ t P h, IntegrableOn (X.ker ψ θ t P h) X.fd X.m)
    (hker : ∀ t t' P, X.I ψ θ t P = 0 → X.I ψ θ t' P = 0)
    (lam : T → ℂ) (s : PolF D WW.rank A'.rank →ₗ[ℂ] PolF D WW.rank A.rank) (hlam : ∀ t, lam t ≠ 0)
    (hs : ∀ t P', (∀ h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m') → X.I ψ θ t (s P') = lam t • X.I' ψ θ t P')
    (hconv : ∃ P', (∀ t h, IntegrableOn (X.ker' ψ θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' ψ θ t P' ≠ 0) :
    Factor X ψ θ lam := by
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₀⟩⟩
  · refine ⟨hlam, ModuleCat.of ℂ ℂ, MvPolynomial.lcoeff ℂ 0, MvPolynomial.lcoeff ℂ 0, fun _ => 0,
      fun z => ⟨MvPolynomial.C z, by simp⟩, fun t => hT.elim t, fun t => hT.elim t, fun t => hT.elim t,
      fun t => hT.elim t, 1, by simp, fun t => hT.elim t⟩
  · let K : Submodule ℂ (PolF D WW.rank A.rank) := LinearMap.ker (linI X ψ θ t₀ (hint t₀))
    have hK : ∀ t, LinearMap.ker (linI X ψ θ t (hint t)) = K := fun t => by
      ext P
      simp only [K, LinearMap.mem_ker, linI_apply]
      exact ⟨hker t t₀ P, hker t₀ t P⟩
    let Jb : T → ((PolF D WW.rank A.rank ⧸ K) →ₗ[ℂ] (GA D WW → ℂ)) := fun t =>
      K.liftQ (linI X ψ θ t (hint t)) (hK t).ge
    have hJb : ∀ t, Function.Injective (Jb t) := fun t => by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ (hK t).le
    refine ⟨hlam, ModuleCat.of ℂ (PolF D WW.rank A.rank ⧸ K), K.mkQ, K.mkQ ∘ₗ s, fun t => (lam t)⁻¹ • Jb t,
      K.mkQ_surjective, fun t => ?_, hint, fun t P => ?_, fun t P' hP' => ?_, ?_⟩
    · intro x y hxy
      exact hJb t (smul_right_injective _ (inv_ne_zero (hlam t)) hxy)
    · show X.I ψ θ t P = lam t • ((lam t)⁻¹ • Jb t (K.mkQ P))
      rw [smul_smul, mul_inv_cancel₀ (hlam t), one_smul]
      rfl
    · show X.I' ψ θ t P' = (lam t)⁻¹ • Jb t (K.mkQ (s P'))
      have : Jb t (K.mkQ (s P')) = X.I ψ θ t (s P') := rfl
      rw [this, hs t P' hP', smul_smul, inv_mul_cancel₀ (hlam t), one_smul]
    · obtain ⟨P', hc, hne⟩ := hconv
      refine ⟨P', fun h0 => hne t₀ ?_, hc⟩
      have h1 : s P' ∈ K := (Submodule.Quotient.mk_eq_zero K).1 h0
      have h2 : X.I ψ θ t₀ (s P') = 0 := h1
      rw [hs t₀ P' (hc t₀)] at h2
      exact (smul_eq_zero.1 h2).resolve_left (hlam t₀)

end GlobalTheory.StageFactor

open GlobalTheory.StageFactor

theorem GlobalTheory.StageFactor.factor_stage : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ lam : T → ℂ, Factor X W.ψ W.θ lam := by
  intro hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.T.stage_triangle_kernel_integrable hP hK hL) (GlobalTheory.T.stage_triangle_integral_vanishing hP hK hL))
    (GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.T.exists_stage_triangle_transfer hP hK hL) (GlobalTheory.T.exists_stage_triangle_polynomial hP hK hL))
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hL G W S hW hN i j p q A A' WW X hX => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h C hC D large₂ a b r T Lc μ hL G
  obtain ⟨lam, s, hlam, hs⟩ := h3 W S hW hN i j p q A A' WW X hX
  exact ⟨lam, factor_of_parts X W.ψ W.θ (h1 W S hW hN i j p q A A' WW X hX) (h2 W S hW hN i j p q A A' WW X hX) lam s hlam hs
    (h4 W S hW hN i j p q A A' WW X hX)⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerRegularFramedAffine
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

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KReg

theorem exists_res_eq {X : Scheme.{0}} (U W : X.affineOpens) (V : X.Opens) (hW : W.1 = U.1 ⊓ V) (θ : Γ(X, W.1))
    (h : ∀ m : Ideal Γ(X, U.1), m.IsMaximal → (∃ x ∈ U.1, (∀ f ∈ m, x ∉ X.basicOpen f) ∧ x ∉ V) →
      ∃ g ∉ m, ∃ s : Γ(X, U.1), (X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom s =
        (X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom g * θ) :
    ∃ s : Γ(X, U.1), (X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom s = θ := by
  have hWU : W.1 ≤ U.1 := hW.le.trans inf_le_left
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = (X.presheaf.map (homOfLE hWU).op).hom := ⟨_, rfl⟩
  have hres : ∀ {A B C : X.Opens} (h1 : B ≤ A) (h2 : C ≤ B) (h3 : C ≤ A) (z : Γ(X, A)),
      (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom z) =
        (X.presheaf.map (homOfLE h3).op).hom z := fun h1 h2 h3 z => by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  let J : Ideal Γ(X, U.1) :=
    { carrier := {g | ∃ s : Γ(X, U.1), ρ s = ρ g * θ}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := fun {g g'} ⟨s, hs⟩ ⟨s', hs'⟩ => ⟨s + s', by rw [map_add, map_add, hs, hs', add_mul]⟩
      smul_mem' := fun r g ⟨s, hs⟩ => ⟨r * s, by rw [smul_eq_mul, map_mul, map_mul, hs, _root_.mul_assoc]⟩ }
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hne
    let p : PrimeSpectrum Γ(X, U.1) := ⟨m, hm.isPrime⟩
    have hxU : U.2.fromSpec p ∈ U.1 := by
      have : U.2.fromSpec p ∈ Set.range U.2.fromSpec := ⟨p, rfl⟩
      rwa [U.2.range_fromSpec] at this
    have hxf : ∀ f, U.2.fromSpec p ∈ X.basicOpen f ↔ f ∉ m := fun f => by
      change p ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen f ↔ _
      rw [U.2.fromSpec_preimage_basicOpen]; rfl
    by_cases hxV : U.2.fromSpec p ∈ V
    · obtain ⟨g, hgW, hxg⟩ := U.2.exists_basicOpen_le (V := W.1) ⟨U.2.fromSpec p, hW ▸ ⟨hxU, hxV⟩⟩ hxU
      have hgm : g ∉ m := (hxf g).1 hxg
      apply hgm
      haveI := U.2.isLocalization_basicOpen g
      obtain ⟨⟨s, ⟨_, N, rfl⟩⟩, hs⟩ := IsLocalization.surj (Submonoid.powers g)
        ((X.presheaf.map (homOfLE hgW).op).hom θ)
      have hbo : X.basicOpen (ρ g) ≤ X.basicOpen g := by
        rw [hρ, Scheme.basicOpen_res]; exact inf_le_right
      have e3 : ∀ z, (X.presheaf.map (homOfLE hgW).op).hom (ρ z) =
          algebraMap Γ(X, U.1) Γ(X, X.basicOpen g) z := fun z => by
        rw [hρ]; exact hres hWU hgW (hgW.trans hWU) z
      have hz : (X.presheaf.map (homOfLE hgW).op).hom (ρ g ^ N * θ - ρ s) = 0 := by
        rw [map_sub, map_mul, map_pow, e3, e3, ← map_pow, mul_comm, hs, sub_self]
      have hz' : (X.presheaf.map (homOfLE (X.basicOpen_le (ρ g))).op).hom (ρ g ^ N * θ - ρ s) = 0 := by
        have := congrArg (X.presheaf.map (homOfLE hbo).op).hom hz
        rwa [map_zero, hres hgW hbo (X.basicOpen_le (ρ g))] at this
      obtain ⟨M, hM⟩ := AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X
        W.2.isCompact (ρ g ^ N * θ - ρ s) (ρ g) hz'
      refine hm.isPrime.mem_of_pow_mem (M + N) (hJm ⟨g ^ M * s, ?_⟩)
      rw [map_mul, map_pow, map_pow, pow_add]
      linear_combination (-1 : Γ(X, W.1)) * hM
    · obtain ⟨g, hgm, s, hs⟩ := h m hm ⟨_, hxU, fun f hf hx => (hxf f).1 hx hf, hxV⟩
      exact hgm (hJm ⟨s, hρ ▸ hs⟩)
  obtain ⟨s, hs⟩ : (1 : Γ(X, U.1)) ∈ J := hJ ▸ Submodule.mem_top
  exact ⟨s, by rw [← hρ, hs, map_one, _root_.one_mul]⟩

theorem exists_der_res {X : Scheme.{0}} (U W : X.affineOpens) (hW : W.1 ≤ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) :
    ∃ DW : Derivation ℤ Γ(X, W.1) Γ(X, W.1), ∀ r, DW ((X.presheaf.map (homOfLE hW).op).hom r) =
      (X.presheaf.map (homOfLE hW).op).hom (D r) := by
  set ρ := (X.presheaf.map (homOfLE hW).op).hom with hρ
  letI : Algebra Γ(X, U.1) Γ(X, W.1) := ρ.toAlgebra
  have h1 : IsOpenImmersion (chart W) := W.2.isOpenImmersion_fromSpec
  have e : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Γ(X, W.1))) ≫ chart U = chart W :=
    GlobalTheory.LogKSDiv.GenChange.chart_res U W hW
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Γ(X, W.1))) ≫ chart U) := e ▸ h1
  have : IsOpenImmersion (chart U) := U.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Γ(X, W.1)))) :=
    IsOpenImmersion.of_comp _ (chart U)
  have hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Γ(X, W.1)))) := inferInstance
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at hs
  have : Algebra.Smooth Γ(X, U.1) Γ(X, W.1) := RingHom.smooth_algebraMap.1 hs
  let g : Γ(X, U.1) →+* DualNumber Γ(X, W.1) :=
    { toFun := fun r => TrivSqZeroExt.inl (ρ r) + TrivSqZeroExt.inr (ρ (D r))
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun a b => by ext <;> simp <;> ring
      map_mul' := fun a b => by ext <;> simp [Derivation.leibniz] <;> ring }
  letI : Algebra Γ(X, U.1) (DualNumber Γ(X, W.1)) := g.toAlgebra
  let π : DualNumber Γ(X, W.1) →ₐ[Γ(X, U.1)] Γ(X, W.1) :=
    { (TrivSqZeroExt.fstHom Γ(X, W.1) Γ(X, W.1) Γ(X, W.1)).toRingHom with
      commutes' := fun r => by simp [g, RingHom.algebraMap_toAlgebra] }
  have hsur : Function.Surjective π := fun s => ⟨TrivSqZeroExt.inl s, rfl⟩
  have hk : IsNilpotent (RingHom.ker (π : DualNumber Γ(X, W.1) →+* Γ(X, W.1))) := by
    refine ⟨2, ?_⟩
    rw [Submodule.zero_eq_bot, eq_bot_iff, pow_two]
    refine Submodule.mul_le.2 fun a ha b hb => ?_
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    rw [Submodule.mem_bot]
    ext <;> simp [ha', hb']
  let l := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id Γ(X, U.1) Γ(X, W.1)) π hsur hk
  have hl1 : ∀ s, (l s).fst = s := fun s =>
    AlgHom.congr_fun (Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id Γ(X, U.1) Γ(X, W.1)) π hsur hk) s
  have hl2 : ∀ r, l (ρ r) = g r := fun r => l.commutes r
  refine ⟨Derivation.mk' (AddMonoidHom.toIntLinearMap
    { toFun := fun s => (l s).snd, map_zero' := by simp, map_add' := fun x y => by rw [map_add]; rfl }) fun a b => ?_,
    fun r => ?_⟩
  · change (l (a * b)).snd = a • (l b).snd + b • (l a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hl1, hl1]
    simp [smul_eq_mul, mul_comm]
  · change (l (ρ r)).snd = _
    rw [hl2]
    simp [g]

theorem exists_isKS_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U, ∃ Θ, IsKS Y.t (interior Y) U v D.1 Θ := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm hsnc hrig U n v A hv hb hA D
  obtain ⟨W, hW⟩ : ∃ W : Y.X.affineOpens, W.1 = U.1 ⊓ interior Y := ⟨⟨_, GlobalTheory.AffOff.isAffineOpen_inf_interior E H Dw l Xo c Y hsnc U⟩, rfl⟩
  have hWU : W.1 ≤ U.1 := hW.le.trans inf_le_left
  obtain ⟨DW, hDW⟩ := exists_der_res U W hWU D.1
  obtain ⟨hv', hb'⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange Y.t (Y.X.presheaf.map (homOfLE hWU).op).hom
    (chart U) n v hv hb
  rw [GlobalTheory.LogKSDiv.GenChange.chart_res U W hWU] at hv' hb'
  obtain ⟨ΘW, hΘW⟩ := GlobalTheory.T.exists_kodairaSpencer_interior_affine_open E H Dw l Xo c Y W (hW.le.trans inf_le_right) n _ hv' hb' DW
  have key := fun (m : Ideal Γ(Y.X, U.1)) (hm : m.IsMaximal) hx =>
    GlobalTheory.T.kodairaSpencer_regular_near_rigid_boundary_point E H Dw l Xo c Y hpq hsm hsnc hrig U W hW n v hv hb D DW ΘW hDW hΘW m hm hx
  choose Θ hΘ using fun a b => exists_res_eq U W (interior Y) hW (ΘW a b) fun m hm hx =>
    (key m hm hx).imp fun g hg => ⟨hg.1, hg.2 a b⟩
  refine ⟨Θ, GlobalTheory.LogKSUp.isKS_of_inf E H Y.X Y.t (interior Y) U W hW n v D.1 DW Θ hDW ?_⟩
  convert hΘW using 1
  ext a b
  exact hΘ a b

end GlobalTheory.KReg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryFourierSystemTraitsFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

namespace GlobalTheory.USep

set_option maxHeartbeats 1000000 in

theorem exists_system_with_traits_and_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ pullback C.z (spMap C.b), Cm.y ≫ C.iF = jK V ≫ ξ → ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (M : Scheme.{0}) (_ : IsIntegral M) (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] ((n ^ j) ^ 2) (M.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) (U : M.Opens), (U : Set M).Nonempty ∧ j₀ ≤ j ∧ IsCov C g z₁ ζ ∧ GlobalTheory.GSep.HasTraitsOn ζ Φ.pre U ∧ IsMember ζ Φ Cm ξ y ρ e h := by
  intro E _ _ _ H Dw hpq l Xo c C φ V _ _ _ Cm hV ξ hξ n hn hodd j₀
  obtain ⟨j, X₁, π, z₁, ζ, hdom, U, Φ, y, ρ, e, h, c₀, hj, hcov, hU, hT, hM, hunit, hm1, hE, hCS⟩ :=
    GlobalTheory.T.exists_unitary_fourier_system_traits_chart E H Dw hpq l Xo c C φ V Cm hV ξ hξ n hn hodd (max j₀ 1)
  obtain ⟨-, -, hIC, -⟩ := GlobalTheory.T.modelStalk_normal_noetherian_fractionRing X₁ z₁
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hN : 3 ≤ (n ^ j) ^ 2 := by
    have h3 : 3 ≤ n := by
      rcases hodd with ⟨k, hk⟩
      have := hn.two_le
      omega
    have h2 : 3 ≤ n ^ j := le_trans h3 (Nat.le_self_pow (by omega) n)
    nlinarith
  have hLam : Φ.abelian₂ := GlobalTheory.T.fourierTermSystem_lam_of_exact_class_sums (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) (by norm_num) hN hE
  have hFour : Φ.Four ((n ^ j) ^ 2) := GlobalTheory.T.fourierTermSystem_four_of_galois_class_sums (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) hCS
  let v : ∀ y', (Φ.V y')ˣ := fun y' => (hunit y').unit⁻¹
  have happ : ∀ e' : ℕ, ∃ a : X₁.M.Z.presheaf.stalk z₁, ∀ y', Φ.ev y' a - ((v y')⁻¹ : (Φ.V y')ˣ) ∈
      (maximalIdeal (X₁.M.Z.presheaf.stalk z₁) ^ e').map (Φ.ev y') := by
    intro e'
    obtain ⟨a, ha⟩ := GlobalTheory.T.fourierTermSystem_indexZero_coefficient_approx (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) hN hE hLam hFour
      (fun y₁ y₂ h₁ h₂ => (hm1 y₁ h₁).trans (hm1 y₂ h₂).symm) c₀ e'
    refine ⟨a, fun y' => ?_⟩
    simpa [v] using ha y'
  have hFour' : (Φ.rescale v).Four ((n ^ j) ^ 2) := GlobalTheory.T.fourierTermSystem_four_rescale_approximated_units (𝓞 E) _ _ 1 _ _ Φ ((n ^ j) ^ 2) hFour v happ
  have hLam' : (Φ.rescale v).abelian₂ := hLam
  refine ⟨j, X₁.M.Z, inferInstance, π, z₁, ζ, (Φ.rescale v).toVSys ((n ^ j) ^ 2) hLam' hFour', y, ρ, e, h, U, hU,
    le_trans (le_max_left _ _) hj, hcov, hT, ?_⟩
  obtain ⟨h1, h2, h3, h4, D, p, hT0⟩ := hM
  refine ⟨h1, h2, h3, h4, D, p, ?_⟩
  have h0 : Φ.term y (fun _ => e.symm 0) c₀ * ((v y : (Φ.V y)ˣ) : Φ.V y) = 1 := by
    have hz : (fun _ : Fin 1 => e.symm 0) = 0 := by
      funext a; simp
    rw [hz]
    simp [VPre.term, mono, qW, v]
  have := GlobalTheory.T.isThetaTerms_of_mul_index_zero_term_eq_one (Φ.V y) D ((n ^ j) ^ 2) _ Φ.Q p.xe.symm
    (fun mu c => Φ.term y (fun _ => e.symm mu) c) (v y) c₀ hT0 h0
  refine cast (congrArg (fun T => GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) p.xe.symm T) ?_) this
  funext mu c
  show Φ.u y (fun _ => e.symm mu) c * mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu) * ((v y : (Φ.V y)ˣ) : Φ.V y) =
    Φ.u y (fun _ => e.symm mu) c * ((v y : (Φ.V y)ˣ) : Φ.V y) * mono !![(1 : ℤ)] (Φ.t y) (Φ.δ y) (fun _ => e.symm mu)
  exact mul_right_comm _ _ _

end GlobalTheory.USep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinTrickFamilySiegelKernelKilled
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem GlobalTheory.UPel.HT.exists_zarhin_data_siegKerBy : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (O : Type) (_ : Ring O) (bar : O → O) (r : ℕ) (eO : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ) (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), (∀ a b, bar (a + b) = bar a + bar b) ∧ Submodule.span ℤ (Set.range eO) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d₀ ∧ ∑ i, ∑ j, W i j • (eO j * bar (eO i)) = (d₀ : O) ∧ e * e = e ∧ (∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P bar act ∧ ZRel e jl o κ c z act) ∧ ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z₁ z₂ : SiegPre (8 * h) M (zetaAway M) t) (act₁ : O → (z₁.A ⟶ z₁.A)) (act₂ : O → (z₂.A ⟶ z₂.A)), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z₁.Principal → z₂.Principal → IsRAct z₁.A act₁ → IsRAct z₂.A act₂ → Adj z₁.A z₁.P bar act₁ → Adj z₂.A z₂.P bar act₂ → ZRel e jl o κ c z₁ act₁ → ZRel e jl o κ c z₂ act₂ → ActPB z₁ act₁ z₂ act₂ (𝟙 S) := by
  intro h M d hh hM hMo hd hcop
  obtain ⟨r, eO, W, d₀, hspan, hW, hd₀, hid⟩ := GlobalTheory.T.exists_zarhin_order_spanning_family_posDef_matrix d hd
  obtain ⟨jl, n, o, κ, hex⟩ := GlobalTheory.T.exists_principal_zarhin_object_of_siegKerBy h M d hh hM hMo hd hcop
  exact ⟨GlobalTheory.ZarhinFam.ord d, inferInstance, GlobalTheory.ZarhinFam.bar d, r, eO, W, d₀, GlobalTheory.ZarhinFam.idem d, jl, n, o, κ,
    GlobalTheory.ZarhinFam.bar_add d, hspan, hW, hd₀, hid, GlobalTheory.ZarhinFam.idem_mul_self d, hex,
    fun S t c z₁ z₂ act₁ act₂ => GlobalTheory.T.zarhinTrick_principal_objects_iso_unique h M d hh hM hMo hd hcop jl n o κ S t c z₁ z₂ act₁ act₂⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsGluedFirstOrderDeformationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
theorem _root_.GlobalTheory.T.harrisTaylor_exists_glued_firstOrder_deformation : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f j x)) → ∃ (o : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t)) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)), ∀ x ∈ Fil o₀.A, GlobalTheory.FODef.IsFilLiftV m.cart x (LinearMap.pi fun j => f j x) := by
  first | exact @GlobalTheory.HTGlue.exists_glue | exact GlobalTheory.HTGlue.exists_glue | exact @GlobalTheory.HTGlue.isFilLiftV_of_eq | exact GlobalTheory.HTGlue.isFilLiftV_of_eq | exact @GlobalTheory.HTGlue.exists_obj_of_summand | exact GlobalTheory.HTGlue.exists_obj_of_summand
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFormallySmoothSquareZeroLiftStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_formally_smooth_squareZero_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (A₁ A₀ : Type) [CommRing A₁] [CommRing A₀] [IsLocalRing A₁] [IsArtinianRing A₁] (π : A₁ →+* A₀) (β : R →+* A₁), Function.Surjective π → RingHom.ker π * RingHom.ker π = ⊥ → ∀ o : Obj b N (spMap (π.comp β)), ∃ o' : Obj b N (spMap β), Nonempty (ObjMap o o' (spMap π)) := by
  first | (exact @GlobalTheory.UPel.HT.obj_lift_sqZero) | (exact GlobalTheory.UPel.HT.obj_lift_sqZero) | (intros; apply GlobalTheory.UPel.HT.obj_lift_sqZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiesPrincipalAlgClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_family_classifies_principal_algClosed : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ f : Sp K ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.SiegelFieldClass.classifies_algClosed | exact GlobalTheory.SiegelFieldClass.classifies_algClosed | (intros; apply GlobalTheory.SiegelFieldClass.classifies_algClosed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareRatioInEmbeddingRangeStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_ratio_in_embedding_range : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → SetAt → (Closed FamHyp fun Fm _ => EvPt Fm fun x _ i _ => |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) → GlobalTheory.RowClaim.ConstK → LNe → TriEx → Tower → (AtPt fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ i j t, GlobalTheory.RowTest.sqRatio ch i j t ∈ Set.range D.what₂.embLL) := by
  first | exact @GlobalTheory.BigTop.Fun.sqRatio_atPt | exact GlobalTheory.BigTop.Fun.sqRatio_atPt | (intros; apply GlobalTheory.BigTop.Fun.sqRatio_atPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkNormalOfSmooth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.crystallineComparison

noncomputable section

namespace GlobalTheory.ESOrdM

theorem stalk_normal_of_smooth (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (X : Scheme.{0})
    (f : X ⟶ Sp R) [Smooth f] (x : X) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  refine GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f (fun y => ?_) x
  haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y
  let _ : Algebra R ((Sp R).presheaf.stalk y) := StructureSheaf.stalkAlgebra R y
  have h : IsLocalization.AtPrime ((Sp R).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R y
  have hle : y.asIdeal.primeCompl ≤ nonZeroDivisors R := y.asIdeal.primeCompl_le_nonZeroDivisors
  have hd : IsDomain ((Sp R).presheaf.stalk y) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  exact ⟨hd, isIntegrallyClosed_of_isLocalization _ _ hle⟩

end GlobalTheory.ESOrdM
end
end

