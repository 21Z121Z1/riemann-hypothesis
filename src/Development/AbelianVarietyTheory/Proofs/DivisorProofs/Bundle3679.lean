import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionKilledByIdealCharZero
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3617
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3613
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3457
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3667
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3173
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryFourierSystemTraitsChart
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3671
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3658
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3664
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3659
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3662
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3673
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3678

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotRatio

theorem gBig_of_two {Q₁ Q₂ Q₃ : GlobalTheory.SqTop.GP} (h₁ : GlobalTheory.SqTop.GBig Q₁) (h₂ : GlobalTheory.SqTop.GBig Q₂)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b) : GlobalTheory.SqTop.GBig Q₃ := by
  obtain ⟨a₁, h₁⟩ := h₁
  obtain ⟨a₂, h₂⟩ := h₂
  refine ⟨max a₁ a₂, fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, h₁⟩ := h₁ ε CF (le_of_max_le_left hCF)
  obtain ⟨C₂, x₂, h₂⟩ := h₂ ε CF (le_of_max_le_right hCF)
  exact ⟨max C₁ C₂, max x₁ x₂, fun C hC D large₂ he hx r T Lc μ hLc G =>
    H G μ C _ _ (h₁ C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) r T Lc μ hLc G)
      (h₂ C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) r T Lc μ hLc G)⟩

theorem bottomConst_ratio : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall → GlobalTheory.SqTop.LNe →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ),
      IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      c0 t ≠ 0 ∧ c0 μ₀ ≠ 0 ∧ ∃ γ : D.what₂.LL, D.what₂.embLL γ * c0 μ₀ = c0 t := by
  intro hPr hK hM _ _ hL
  refine GlobalTheory.BotRatio.gBig_of_two (GlobalTheory.T.bottom_triangle_constant_ratio hPr hK hM hL) (GlobalTheory.T.bottom_constant_of_bottom_pair hPr hK hM) fun {D T Lc sc} G μ₀ C x b ha hb => ?_
  intro W S hψ hN i j t A A' WW X c0 hX hc
  obtain ⟨B, B', WW₁, Y, hY, hS⟩ := hN.bottom i j ⟨A, A', WW, X, hX⟩
  have hr := hS.rationalSums (fun t => (hY.integrable t).1) fun t => (hY.integrable t).2
  obtain ⟨u, hu⟩ := hb W S hψ hN i j B B' WW₁ Y A A' WW X c0 hY hX hc
  obtain ⟨lam, hl⟩ := ha W hψ i j B B' WW₁ Y hY
  have hR := GlobalTheory.ConstRatio.ratIn_of_definite hY.is (GlobalTheory.ConstRatio.posDef_of_std hY.std)
    (GlobalTheory.ConstRatio.posDef_of_std hY.std') (GlobalTheory.ConstRatio.posDef_of_std hY.stdW) hl hr μ₀
  obtain ⟨κ, hκ, e⟩ := hl.eq_mul hu
  have h1 : GlobalTheory.ConstRatio.RatIn D.what₂.embLL μ₀ fun t => D.what₂.embLL (u t) * c0 t := by
    rw [show (fun t => D.what₂.embLL (u t) * c0 t) = fun t => κ * lam t from funext e]
    exact (GlobalTheory.ConstRatio.ratIn_const hκ).mul hR
  have h2 : GlobalTheory.ConstRatio.RatIn D.what₂.embLL μ₀ c0 :=
    GlobalTheory.ConstRatio.RatIn.of_mul h1 (GlobalTheory.ConstRatio.ratIn_of_unit fun t => ⟨u t, rfl⟩) fun t => mul_comm _ _
  obtain ⟨h3, y, hy⟩ := h2 t
  refine ⟨h3, (h2 μ₀).1, y, ?_⟩
  rw [hy, div_mul_cancel₀ _ (h2 μ₀).1]

end GlobalTheory.BotRatio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionKilledByIdealCharZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.card_torsion_killed_by_ideal_char_zero : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w : Ideal (𝓞 D.F)), w ≠ ⊥ → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] [CharZero κ] (x : Sp κ ⟶ S), Nat.card {g : Over.mk x ⟶ o.A // KilledBy o w g} = Ideal.absNorm w ^ (D.m * D.n) := by
  first | exact @GlobalTheory.UPel.HT.ES.CharZeroCount.card_killedBy_charZero | exact GlobalTheory.UPel.HT.ES.CharZeroCount.card_killedBy_charZero | (intros; apply GlobalTheory.UPel.HT.ES.CharZeroCount.card_killedBy_charZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionKilledByPrimeAtEtalePlaceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_torsion_killed_by_prime_at_etale_place : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)), IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), Nat.card {g : Over.mk x ⟶ o.A // ∀ c ∈ w0, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1} = Nat.card (𝓞 D.F ⧸ w0) ^ (D.m * D.n) := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.GeoCard.card_ker_place) | (exact GlobalTheory.UPel.HT.EtLev.GeoCard.card_ker_place) | (intros; apply GlobalTheory.UPel.HT.EtLev.GeoCard.card_ker_place  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationConstantOfLogKodairaSpencerMemStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degeneration_constant_of_logKodairaSpencer_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → ∀ x : Y.X, x ∉ interior Y → x ∈ U.1 → (∀ f ∈ m, x ∉ Y.X.basicOpen f) → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → ∀ (k : Type) [Field k] (m' d : ℕ) (ξ : Sp (ChartRing k m' d) ⟶ gen Y) (x' : gen Y), ξ (closedPoint _) = x' → genι Y x' = x → ∀ (t : SAB H (Sp (ChartRing k m' d))) (P : PELUnif (maximalIdeal (ChartRing k m' d)) t) (gam : Fin m' → levelForms H l.M' P.D.toPre.X), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (FinalTheorems.stalkId (genBdIdeal Y) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom = Ideal.span {∏ i, bdParam k m' d i} → (∀ p : Sp (ChartRing k m' d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m' d i ∈ p.asIdeal) → Nonempty (SABMap t Y.t (ξ ≫ genι Y)) → IsMonomial P.D.toPre (bdParam k m' d) (fun i => gam i) → IsPartOfBasis gam → ∀ (hU : ⊤ ≤ (ξ ≫ genι Y) ⁻¹ᵁ U.1) (DR : Derivation ℤ (ChartRing k m' d) (ChartRing k m' d)) (a : Fin m' → (ChartRing k m' d)), (∀ r, DR (valR (ξ ≫ genι Y) U.1 r) = valR (ξ ≫ genι Y) U.1 (D.1 r)) → (∀ i, DR (bdParam k m' d i) = a i * bdParam k m' d i) → ∀ ρ : ChartRing k m' d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (DR r))) → ∃ c₀ : ℚ, c₀ ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m' d) (fun i => gam i) ρ (fun i => (c₀ : k) * MvPowerSeries.constantCoeff (a i)) := by
  first | exact @GlobalTheory.ChartConst.isConstAlong_of_ks_mem | exact GlobalTheory.ChartConst.isConstAlong_of_ks_mem | (intros; apply GlobalTheory.ChartConst.isConstAlong_of_ks_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalFamilyThroughDegeneratingFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem injective_of_flat_of_isDomain {A R : Type} [CommRing A] [IsDomain A] [CommRing R] [Nontrivial R] (ψ : A →+* R)
    (h : ψ.Flat) : Function.Injective ψ := by
  letI := ψ.toAlgebra
  haveI : Module.Flat A R := h
  refine (injective_iff_map_eq_zero ψ).2 fun a ha => ?_
  by_contra h0
  have hr := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) (mem_nonZeroDivisors_of_ne_zero h0)
  have h1 : a • (1 : R) = a • (0 : R) := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_zero, _root_.mul_one]; exact ha
  exact one_ne_zero (hr h1)

theorem exists_canon_through : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V), Nontrivial C.P.D.toPre.X → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C₁ : MonoFam Xo c φ (ChartRing k m e)) (θ : ChartRing k m e →+* V), Nonempty (Canon C₁) ∧ (∃ hm : C₁.m = m, ∀ i, C₁.s i = bdParam k m e (Fin.cast hm i)) ∧ IsLocalHom θ ∧ Through C C₁ θ := by
  intro E _ _ _ H Dw l Xo c φ V _ _ _ hV hk C hn
  obtain ⟨D', L, θ₀, N, ε, e, s, hp, hq, hθ₀, hb, hδ, hs, hu, hdiv⟩ := GlobalTheory.T.degeneratingFamily_data_from_base_algClosed_residue Xo c φ V hV hk C hn
  have hC₀ : (MvPolynomial.eval₂Hom θ₀ s).comp MvPolynomial.C = θ₀ := RingHom.ext fun a => MvPolynomial.eval₂Hom_C _ _ _
  have hsm : ∀ i, s (.inl i) ∈ maximalIdeal V := fun i => by
    obtain ⟨u, hu⟩ := (hs i).symm
    rw [← hu]; exact Ideal.mul_mem_right _ _ (C.s_mem i)
  have hs0 : ∀ i, s (.inl i) ≠ 0 := fun i h => C.s_ne_zero i ((hs i).eq_zero_iff.1 h)
  obtain ⟨k, _, e', ψ, θ, hcompl, hθ, hθψ, hψ, hbd⟩ := GlobalTheory.T.exists_toricChartRing_factorisation_localHom L.W ⟨L.b.comp (algebraMap ℚ c.F)⟩ C.m N V hV.1.2.2.2
    (MvPolynomial.eval₂Hom θ₀ s) (by rw [hC₀]; exact hθ₀) (fun i => by rw [MvPolynomial.eval₂Hom_X']; exact hsm i)
  have hθX : ∀ j, θ (ψ (MvPolynomial.X j)) = s j := fun j => by
    rw [← RingHom.comp_apply, hθψ, MvPolynomial.eval₂Hom_X']
  have hθC : θ.comp (ψ.comp MvPolynomial.C) = θ₀ := by rw [← RingHom.comp_assoc, hθψ, hC₀]
  have hinj : Function.Injective (ψ.comp MvPolynomial.C) :=
    (injective_of_flat_of_isDomain ψ hcompl.2.2.1).comp (MvPolynomial.C_injective _ _)
  let b₁ : c.F →+* ChartRing k C.m e' := (ψ.comp MvPolynomial.C).comp L.b
  have hR : GlobalTheory.Mum.Base (ChartRing k C.m e') :=
    ⟨GlobalTheory.MumfordChart.admissibleBase_chartRing k C.m e', (b₁.charZero_iff b₁.injective).1 inferInstance⟩
  have htor : ∀ j, IsUnit (ψ (MvPolynomial.X (.inr j))) := fun j => hθ.map_nonunit _ (by rw [hθX]; exact hu j)
  have hmem : ∀ i, ψ (MvPolynomial.X (.inl i)) ∈ maximalIdeal (ChartRing k C.m e') := fun i hi =>
    hsm i (by rw [← hθX]; exact hi.map θ)
  have hne : ∀ i, θ (ψ (MvPolynomial.X (.inl i))) ≠ 0 := fun i => by rw [hθX]; exact hs0 i
  have hval : ∀ i y, (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) y y = C.δ i (e.symm y) (e.symm y) := fun i y => by
    rw [hδ i]
    show _ = (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) (e (e.symm y)) (e (e.symm y))
    rw [e.apply_symm_apply]
  have hnn : ∀ i y, 0 ≤ (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) y y := fun i y => by
    rw [hval]; exact C.cone.nonneg i _
  have hpos : ∀ y, y ≠ 0 → 0 < ∑ i, (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) y y := fun y hy => by
    obtain ⟨i, hi⟩ := C.mono.exists_pos (maximalIdeal.isMaximal V).ne_top (y := e.symm y) (by simpa using hy)
    refine Finset.sum_pos' (fun j _ => hnn j y) ⟨i, Finset.mem_univ _, ?_⟩
    rw [hval]
    exact pos_of_mul_pos_left (by rw [mul_comm]; exact hi) (Int.natCast_nonneg l.M')
  obtain ⟨t₁, P₁, e₁, hdiv₁, hmono⟩ := GlobalTheory.T.mumford_family_from_regular_base_coordinates L (ChartRing k C.m e') hR (ψ.comp MvPolynomial.C) hinj C.m N
    (fun j => ψ (MvPolynomial.X j)) (fun j => (ε j : LinearMap.BilinForm ℤ L.D.X)) (fun j => (ε j).2)
    (fun i => ⟨hmem i, fun h => hne i (by rw [h, map_zero])⟩) htor hnn hpos e.injective.nontrivial
  obtain ⟨y₁, yo, κ, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.classified_on_open_of_specialises_to_classified Xo c φ D' L (ChartRing k C.m e') V hR hV C.toFam t₁ P₁
    (ψ.comp MvPolynomial.C) θ hθ (by rw [← RingHom.comp_assoc, hθC, hb]) C.m N (fun j => ψ (MvPolynomial.X j))
    (fun j => (ε j : LinearMap.BilinForm ℤ L.D.X)) e₁ e (fun j => (ε j).2) hne htor hdiv₁
    (by rw [hθC, funext hθX]; exact hdiv)
  have hrk : Module.finrank (𝓞 E) P₁.D.toPre.X = Module.finrank (𝓞 E) C.P.D.toPre.X := (e₁.trans e.symm).finrank_eq
  have hcone : IsCone H.bar φ fun i => pull e₁.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) := by
    have h := C.cone.pull_equiv (e₁.trans e.symm)
    have he : (fun i => pull (e₁.trans e.symm).toLinearMap (C.δ i)) =
        fun i => pull e₁.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) := by
      funext i
      rw [hδ i]
      refine LinearMap.ext₂ fun a b => ?_
      show (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) (e (e.symm (e₁ a))) (e (e.symm (e₁ b))) = _
      rw [e.apply_symm_apply, e.apply_symm_apply]
      rfl
    rwa [he] at h
  let C₁ : MonoFam Xo c φ (ChartRing k C.m e') :=
    ⟨⟨b₁, t₁, P₁, y₁, h₁, h₂⟩, C.m, fun i => ψ (MvPolynomial.X (.inl i)), hmem,
      fun i => pull e₁.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X), hcone, hrk.le.trans C.rank, hmono⟩
  exact ⟨k, _, C.m, e', C₁, θ, ⟨⟨D', by rw [← hp, ← hrk], by rw [← hq, ← hrk], L, N, ε, e₁, fun _ => rfl, ψ, hcompl, hψ,
    rfl, fun _ => rfl, htor, hdiv₁⟩⟩, ⟨rfl, hbd⟩, hθ, yo, κ, h₃, h₄, h₅⟩

end GlobalTheory.UCanon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCanonicalMumfordFamilyMonomialPeriods
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_canonOn_of_isMonomialTau : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ Q : Data R, Q.IsPos (maximalIdeal R) → ∀ (m : ℕ) (t : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ Q.X), Q.IsMonomialTau t β → (∀ i, t i ≠ 0) → (∀ i y z, β i y z = β i z y) → (∀ i y, 0 ≤ β i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (P : LB (G2 G).left), IsMumPol Q G P ∧ CanonOn Q (PrimeSpectrum.basicOpen (∏ i, t i)) G P := by
  intro R _ _ _ hR Q hQ m t β hm ht hs h0 h1
  have hpd : ((GlobalTheory.W8 + GlobalTheory.W8.transpose).map (Int.cast : ℤ → ℝ)).PosDef := by
    rw [GlobalTheory.w8_add_transpose_eq_e8]; exact GlobalTheory.e8_posDef
  have hdet : IsUnit (GlobalTheory.W8 + GlobalTheory.W8.transpose).det := by
    rw [GlobalTheory.w8_add_transpose_eq_e8, GlobalTheory.e8_det_eq_one]; exact isUnit_one
  obtain ⟨D', pr, xe, w, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.exists_degData_tensor_posDef_unimodular_form R hR Q hQ GlobalTheory.W8 hpd hdet
  obtain ⟨F⟩ := GlobalTheory.T.nonempty_of_tensorData_posDef_unimodular R hR Q D' GlobalTheory.W8 hpd hdet (by norm_num) pr xe w h₁ h₂ h₃ h₄ h₅
  obtain ⟨β', hβ', -⟩ := GlobalTheory.T.polarisedDegeneration_tensorPower_monomial R Q D'.toPre GlobalTheory.W8 pr xe hpd ⟨h₁, h₂, h₃, w, h₄, h₅⟩ m t β hm ht hs h0 h1
  have hB : Base R := ⟨⟨hR.1, inferInstance, hR.2.1, hR.2.2.1⟩, hR.2.2.2⟩
  obtain ⟨G', iG, cG, A', hsa, ⟨U'⟩⟩ := GlobalTheory.T.hasSemiAbelianUniformisation_complete_normal_base R hB D'
  obtain ⟨oA, oG, hlin⟩ := GlobalTheory.T.exists_ringAction_extension_to_uniformised_semiAbelian R hB D' A' G' hsa U' F.O F.o
  have hidem : oG.act F.e ≫ oG.act F.e = oG.act F.e := by rw [← oG.map_mul, F.idem]
  obtain ⟨G, iG2, cutoffSecondDeriv, inc, pr', hsaG, hinc, hpr, e₁, e₂⟩ :=
    GlobalTheory.Mum.IdemImage.isSemiAbelian_image (Sp R) G' hsa (oG.act F.e) (oG.hom F.e) hidem
  have hL : (abelian₂ G' U'.LG.L).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ U'.LG.isLB _ _
  have hC : CanonOn Q (PrimeSpectrum.basicOpen (∏ i, t i)) G _ := ⟨pull_isLB hL _, D', F, A', G', iG, cG, U', oA, oG, inc, pr',
    fun y => hβ'.psiUnitOn y fun p hp => hp, hsa, hlin, hinc, hpr, e₁, e₂, ⟨idIso _, idIso_isGen (pull_isLB hL _)⟩⟩
  exact ⟨G, iG2, cutoffSecondDeriv, _, ⟨hR, hQ, hsaG, GlobalTheory.T.canonicalFamily_bundle_birigid_symmetric R hR Q G _ hC.canon, GlobalTheory.T.canonical_mumford_family_uniformises_refinements R hR Q G _ hsaG hC.canon⟩, hC⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryFourierSystemTraitsChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_fourier_system_traits_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ pullback C.z (spMap C.b), Cm.y ≫ C.iF = jK V ≫ ξ → ∀ n : ℕ, n.Prime → Odd n → ∀ j₀ : ℕ, ∃ (j : ℕ) (X₁ : GlobalTheory.GSep.GSet) (π : X₁.M.Z ⟶ C.Z) (z₁ : X₁.M.Z) (ζ : Sp (X₁.M.Z.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (_ : IsDomain (X₁.M.Z.presheaf.stalk z₁)) (U : X₁.M.Z.Opens) (Φ : VPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) (c₀ : Φ.Q), j₀ ≤ j ∧ IsCov C π z₁ ζ ∧ (U : Set X₁.M.Z).Nonempty ∧ GlobalTheory.GSep.HasTraitsOn ζ Φ U ∧ GlobalTheory.GSep.IsMemberP ζ Φ ((n ^ j) ^ 2) Cm ξ y ρ e h ∧ (∀ y', IsUnit (Φ.u y' 0 c₀)) ∧ (∀ y', Φ.m y' ≠ 1 → y' = y) ∧ Φ.Exact ((n ^ j) ^ 2) ∧ Φ.ClassSums ((n ^ j) ^ 2) := by
  first | exact @GlobalTheory.GSep.exists_vPre_traitsOn_chart | exact GlobalTheory.GSep.exists_vPre_traitsOn_chart | (intros; apply GlobalTheory.GSep.exists_vPre_traitsOn_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinObjectStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principal_zarhin_object_of_siegKerBy : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act ∧ ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z act := by
  first | (exact @GlobalTheory.ZarhinFam.exists_zarhin_object) | (exact GlobalTheory.ZarhinFam.exists_zarhin_object) | (intros; apply GlobalTheory.ZarhinFam.exists_zarhin_object  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsGluedFirstOrderDeformation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem GlobalTheory.HTGlue.isFilLift_coords {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] {A' : Over (Sp (DualNumber k))}
    [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i)
    {x y : HdR A} (hx : IsFilLift h x y) :
    ∃ e ∈ liftFil (divided₂ (GlobalTheory.FODef.sqZero k k)) h,
      ∀ c, e ((GlobalTheory.FODef.constMorV k k A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (y c) := hx

theorem GlobalTheory.HTGlue.exists_obj_of_summand (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (hNp : N.Coprime p) (C C₀ : Type) [CommRing C] [IsLocalRing C]
    [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀) (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = 0)
    (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)) (E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A))
    (hEc : ∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M)
    (hEf : ∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y)
    (hEs : ∀ (c : D.O), ∀ d ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ E)
    (hEi : ∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C,
      GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ E, ∀ y ∈ E, φ x y = 0)
    (hEl : ∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω);
      push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ E →
      ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c);
        push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ E) ∧
        d - ∑ i, w i ∈ E)
    (s : Sp C ⟶ Sp R) (hs : s = spMap tR) :
    ∃ (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), liftFil (divided₂ hsq) m.cart = E := by
  subst hs
  obtain ⟨A, _, i, h, act, hA, hE, hact⟩ := GlobalTheory.T.harrisTaylor_exists_lift_orderAction_hodge_summand p D R b N C C₀ π hπ hsq tR o₀ E hEc hEf hEs
  haveI : IsCommMonObj A := hA.comm
  subst hE
  obtain ⟨P, φ₂, hP, r1, r2, hsym, hamp, hker, hros, hsq2, hpol⟩ :=
    GlobalTheory.T.harrisTaylor_exists_polarisation_bundle_lift p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hEi
  obtain ⟨eta, e1, e2, e3, e4, e5⟩ :=
    GlobalTheory.T.harrisTaylor_primeToP_level_lift_squareZero p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hNp P φ₂ hP hsq2 hpol
  exact ⟨{ A := A
           ab := hA
           act := act
           P := P
           isLB := hP
           rig₁ := r1
           rig₂ := r2
           symm := hsym
           ample := hamp
           kerP := hker
           rosati := hros
           lie := fun R' _ β x hx v hv => GlobalTheory.T.harrisTaylor_lift_lie_of_hodge_summand_lie p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hEl R' β x hx v hv
           lieRank := fun k _ _ x β hx j => GlobalTheory.T.harrisTaylor_lieMultiplicity_squareZeroLift p D R b N C C₀ π hπ hsq tR o₀ A i h act hact k x β hx j
           eta := eta
           eta_add := e1
           eta_lin := e2
           eta_ker := e3
           geom := e4 },
    { φ := i
      φ₂ := φ₂
      cart := h
      sq := hsq2
      act := hact
      pol := hpol
      eta := e5 }, rfl⟩

theorem GlobalTheory.HTGlue.isFilLiftV_of_eq {k : Type} [Field k] {d : ℕ} {A₀ : Over (Sp k)} [GrpObj A₀] (hA : IsAbelianScheme A₀)
    {A : Over (Sp (TrivSqZeroExt k (Fin d → k)))} [GrpObj A] {i : A₀.left ⟶ A.left}
    (h : IsGrpPullback A₀ A (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom) i)
    (f : Fin d → (HdR A₀ →ₗ[k] HdR A₀))
    (hh : liftFil (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) h = GlobalTheory.HTGlue.glueFil A₀ f) {x : HdR A₀}
    (hx : x ∈ Fil A₀) : GlobalTheory.FODef.IsFilLiftV h x (LinearMap.pi fun j => f j x) := by
  obtain ⟨e, he, hc⟩ := GlobalTheory.HTGlue.exists_mem_glueFil A₀ hA f hx
  exact ⟨e, hh ▸ he, hc⟩

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.HTGlue.exists_glue : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∀ (d : ℕ) (f : Fin d → (HdR o₀.A →ₗ[k] HdR o₀.A)), (∀ j, ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f j x)) → ∃ (o : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ t)) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)), ∀ x ∈ Fil o₀.A, GlobalTheory.FODef.IsFilLiftV m.cart x (LinearMap.pi fun j => f j x) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ d f hdef
  rcases Nat.eq_zero_or_pos d with rfl | hd
  ·

    obtain ⟨tk, ht⟩ : ∃ tk : R →+* k, t = spMap tk := ⟨(Spec.preimage t).hom, by simp [spMap]⟩
    obtain ⟨φ, hφ⟩ := GlobalTheory.UPel.HT.CorrForm.exists_isCorrForm_obj p D R b N hN hNp k t o₀
    exact GlobalTheory.UPel.HT.exists_sqZero_lift_realising_ks p D R b N hN hNp k t o₀ tk ht φ hφ 0 f (fun j => j.elim0)
  haveI : IsArtinianRing (TrivSqZeroExt k (Fin d → k)) := GlobalTheory.HTGlue.isArtinianRing_tsze k d
  haveI : Module.Finite k (DualNumber k) :=
    Module.Finite.of_surjective ((Algebra.linearMap k (DualNumber k)).coprod (TrivSqZeroExt.inrHom k k))
      (fun x => ⟨(x.fst, x.snd), by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]⟩)
  haveI : IsArtinianRing (DualNumber k) := IsArtinianRing.of_finite k _
  obtain ⟨tk, ht⟩ : ∃ tk : R →+* k, t = spMap tk := ⟨(Spec.preimage t).hom, by simp [spMap]⟩
  set tR : R →+* TrivSqZeroExt k (Fin d → k) := (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp tk with htR
  have hs : t = spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
    all_goals (congr 1 <;> ext x <;> simp [tR])
  subst hs
  choose o' m' hm' using hdef
  have hsε : spMap (algebraMap k (DualNumber k)) ≫
      (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR) =
      spMap ((algebraMap k (TrivSqZeroExt k k)).comp tk) := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
  have hs₀ : spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap ((algebraMap k (TrivSqZeroExt k k)).comp tk) := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
    all_goals (congr 1 <;> ext x <;> simp)
  have hsurε : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, by simp⟩
  have n1 := fun j => GlobalTheory.T.harrisTaylor_lift_hodge_summand_admissible_stable p D R b N (DualNumber k) k (TrivSqZeroExt.fstHom k k k).toRingHom hsurε (GlobalTheory.FODef.sqZero k k) ((algebraMap k (TrivSqZeroExt k k)).comp tk) (spMap (algebraMap k (DualNumber k)) ≫ (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR)) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR) o₀ (o' j) (m' j) hsε hs₀
  have n2 := fun j => GlobalTheory.T.harrisTaylor_lift_hodge_summand_isotropic p D R b N (DualNumber k) k (TrivSqZeroExt.fstHom k k k).toRingHom hsurε (GlobalTheory.FODef.sqZero k k) ((algebraMap k (TrivSqZeroExt k k)).comp tk) (spMap (algebraMap k (DualNumber k)) ≫ (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR)) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR) o₀ (o' j) (m' j) hsε hs₀
  have n3 := fun j => GlobalTheory.T.harrisTaylor_lift_hodge_summand_crystalline_lie p D R b N (DualNumber k) k (TrivSqZeroExt.fstHom k k k).toRingHom hsurε (GlobalTheory.FODef.sqZero k k) ((algebraMap k (TrivSqZeroExt k k)).comp tk) (spMap (algebraMap k (DualNumber k)) ≫ (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR)) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR) o₀ (o' j) (m' j) hsε hs₀
  have hmem : ∀ j, ∀ x ∈ Fil o₀.A, ∃ e ∈ liftFil (divided₂ (GlobalTheory.FODef.sqZero k k)) (m' j).cart,
      ∀ c, e ((GlobalTheory.FODef.constMorV k k o₀.A).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f j x c) :=
    fun j x hx => GlobalTheory.HTGlue.isFilLift_coords (m' j).cart (hm' j x hx)
  have hab := o₀.ab
  have htk : spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR = spMap tk := ht
  have g1 := GlobalTheory.T.exists_isCompl_crystalGluedHodgeGraphFiltration p D R b N k tk _ o₀ htk d f
  have g2 := GlobalTheory.T.mem_hodgeFiltration_iff_reduction_gluedFiltration p D R b N k tk _ o₀ htk d f
  have g3 := GlobalTheory.T.crystalGluedHodgeGraph_order_stable_of_directions p D R b N k tk _ o₀ htk d f _ (fun j => (n1 j).1) (fun j => (n1 j).2.1) hmem (fun j => (n1 j).2.2)
  have g4 := GlobalTheory.T.crystalGluedHodgeGraph_isotropic_of_directions p D R b N k tk _ o₀ htk d f _ (fun j => (n1 j).1) (fun j => (n1 j).2.1) hmem (fun j => (n1 j).2.2) n2
  have g5 := GlobalTheory.T.crystalGluedHodgeGraph_lie_condition_of_directions p D R b N k tk _ o₀ htk d hd f _ (fun j => (n1 j).1) (fun j => (n1 j).2.1) hmem (fun j => (n1 j).2.2) n3
  have hsurC : Function.Surjective (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, by simp⟩
  have hst : spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫
      (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ spMap tR) = spMap tR := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
  obtain ⟨o, m, hm⟩ := GlobalTheory.HTGlue.exists_obj_of_summand p D R b N hNp _ k _ hsurC (GlobalTheory.FODef.sqZero k (Fin d → k))
    tR o₀ (GlobalTheory.HTGlue.glueFil o₀.A f) g1 g2 g3 g4 g5 _ hst
  exact ⟨o, m, fun x hx => GlobalTheory.HTGlue.isFilLiftV_of_eq hab m.cart f hm hx⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderDeformationsBasisCountStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_firstOrder_deformations_basis_count : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∃ f : Fin (D.a * (D.n - 1)) → (HdR o₀.A →ₗ[k] HdR o₀.A), (∀ j, ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f j x)) ∧ ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∃! c : Fin (D.a * (D.n - 1)) → k, ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (∑ j, c j • f j x) := by
  first | (exact @GlobalTheory.HTCount.count) | (exact GlobalTheory.HTCount.count) | (intros; apply GlobalTheory.HTCount.count  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFormallySmoothSquareZeroLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem GlobalTheory.UPel.HT.obj_lift_sqZero : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (A₁ A₀ : Type) [CommRing A₁] [CommRing A₀] [IsLocalRing A₁] [IsArtinianRing A₁] (π : A₁ →+* A₀) (β : R →+* A₁), Function.Surjective π → RingHom.ker π * RingHom.ker π = ⊥ → ∀ o : Obj b N (spMap (π.comp β)), ∃ o' : Obj b N (spMap β), Nonempty (ObjMap o o' (spMap π)) := by
  intro p _ D R _ b N _ hN A₁ A₀ _ _ _ _ π β hπ hk o
  have hc : spMap (π.comp β) = spMap π ≫ spMap β := by
    simp only [spMap, Sp, CommRingCat.ofHom_comp, Spec.map_comp]
  have hk2 : RingHom.ker π ^ 2 = ⊥ := by rw [pow_two]; exact hk
  revert o
  rw [hc]
  intro o
  first
  | exact GlobalTheory.T.harrisTaylor_exists_lift_squareZero_artinian p D R b N hN A₁ A₀ π hπ hk2 (spMap β) o
  | exact GlobalTheory.T.harrisTaylor_exists_lift_squareZero_artinian p D R b N A₁ A₀ π hπ hk2 (spMap β) o
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRegularNearRigidBoundaryPointStatement
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
theorem _root_.GlobalTheory.T.kodairaSpencer_regular_near_rigid_boundary_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U W : Y.X.affineOpens) (hW : W.1 = U.1 ⊓ interior Y) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (DW : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, W.1)), (∀ r, DW ((Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom r) = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom (D.1 r)) → IsKS Y.t (interior Y) W (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) DW Θ → ∀ (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → (∃ x ∈ U.1, (∀ f ∈ m, x ∉ Y.X.basicOpen f) ∧ x ∉ interior Y) → ∃ g ∉ m, ∀ a b, ∃ s : Γ(Y.X, U.1), (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom s = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom g * Θ a b := by
  first | exact @GlobalTheory.LocRegRig.isKS_regular_at_boundary | exact GlobalTheory.LocRegRig.isKS_regular_at_boundary | (intros; apply GlobalTheory.LocRegRig.isKS_regular_at_boundary <;> assumption)
end

