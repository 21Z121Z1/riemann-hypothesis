import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0727
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0723
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0729
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0714
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0647
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0715
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0724
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0119
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRowsReadingTransportLaterHeckeGaloisStage
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.CopyRead

private theorem pin_of {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok}
    {Wt : Set B.places.Pl} {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀} {o : q.Over} {m : Moved o} {s : Side0 o}
    (r : ReadPk m s) (Y : Read m.z.R.toRealDat m.z.F.lv2 s.p0) (e : r.Y = Y)
    (h8 : ∀ π, (Formalism.IndefR.principalLevelFrame.rowRepR m.z.R.θ (Y.eFT π)).Iso (m.t.rep π))
    (h9 : ∀ x, HEq (Y.Ish.jE x).1 ((m.t.ch true).jE x)) (h10 : ∀ x, HEq (Y.Iz.jE x).1 ((m.t.ch false).jE x))
    (h11 : ∀ i x, HEq (Y.mj.eW i x) (m.t.lf.eW i x)) (h12 : ∀ μ h i x, HEq (Y.IL.jMt μ h i x).1 (m.t.lf.jMt μ i x)) : r.Pin := by
  subst e
  exact ⟨h8, h9, h10, h11, h12⟩

private theorem read_pinned {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z₀ : w.Lt} {hX : B.fields.Ok}
    {Wt : Set B.places.Pl} {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀} {o : q.Over} (hF : o.Fits) (m : Moved o) (s : Side0 o)
    (hs : GoodSideLattices.Good m s) : ∃ r : ReadPk m s, r.Pin := by
  have k := read_of_fits B f T w Z₀ hX Wt z₀ q o hF m s
  obtain ⟨Y, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := k
  have k2 := GoodSideLattices.read_of_good hF m s hs Y h9 h10
  obtain ⟨Z⟩ := k2
  exact ⟨⟨Y, Z, h1, h2, h3, h4, h5, h6, h7⟩, pin_of _ Y rfl h8 h9 h10 h11 h12⟩

set_option maxHeartbeats 2000000 in

theorem read_copyN : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)), GrpTrue N f → GrpAt (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.I → (∀ eR, StdIso (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.px eR → CenIs P.q.p N eR) → ∀ (m : Moved (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)), m.Copy → m.Coh → ∀ (sg : SameGrp (B := B) (C := w.C) x.o.Z (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) (s : Side0 (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)), s.RR = x.s.RR → HEq s.jEE x.s.jEE → (∀ μ (c : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).nd))) (c0 : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd))), (∀ g, (c0 : MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd)).coeff g = (c : MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).nd)).coeff (sg.iso g)) → s.cen μ c = x.s.cen μ c0) → ∃ r : ReadPk m s, r.Pin ∧ HEq (repOf r.Y) (repOf x.r.Y)  := by
  intro K B f T w P x N hG hGA hCen m hc hco _ s hRR hj _
  have hF : RowPk.Over.Fits (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over) := ⟨x.fits.div, hG, hGA, hCen⟩
  have k := read_pinned hF m s (good_copy x N m hc hco s hRR hj)
  exact k.imp fun r hp => ⟨hp, repOf_heq x.coh x.r x.pin hco r hp⟩

end GlobalTheory.Mem.R3.Rw.CopyRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicEigenvectorCoordinatesHolomorphicUniforStatement
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_eigenvector_coordinates_holomorphic_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (d : ℕ) (u₀ : V d) (R : Type) [CommRing R] (φR : c.F →+* R) (xR : Sp R ⟶ Z.X) (fR : EigFrame Z φR xR) (ev : V d → (R →+* ℂ)) (k : U.Comp) (G : V d → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ (Dw.p + Dw.q)) (τ : E →+* ℂ), (∀ t, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => ev u t) u) → (∀ τ' a b, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u) → (∀ᶠ u in 𝓝 u₀, (ev u).comp φR = σ) → (∀ᶠ u in 𝓝 u₀, ∃ h : G u ∈ (U.X k).dom, (cxPt Z (U.un k ⟨G u, h⟩)).1 ≫ genι Z = spMap (ev u) ≫ xR) → ∃ M : V d → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ, (∀ a b, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => M u a b) u) ∧ ∀ᶠ u in 𝓝 u₀, ∃ h : G u ∈ (U.X k).dom, ∀ i, IsCombAtG Z.t ((cxPt Z (U.un k ⟨G u, h⟩)).1 ≫ genι Z) ((cxFrame Z (U.un k ⟨G u, h⟩)).v τ) (fun b => M u b i) (spMap (dualMap (ev u)) ≫ fR.v τ i) := by
  first | exact @GlobalTheory.HolCoordEv.coords_holomorphic | exact GlobalTheory.HolCoordEv.coords_holomorphic | (intros; apply GlobalTheory.HolCoordEv.coords_holomorphic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPsiCoordinatesOfTauUnitsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.associated_psi_coordinates_of_tau_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t)
    (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (g : R →+* W) (hg : Function.Injective g)
    (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') (ρ : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X),
    (∀ (a b : P.D.toPre.X) (x : (FractionRing R)ˣ) (x' : (FractionRing W)ˣ),
          GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P.D.toPre a b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P'.D.toPre (ρ a) (ρ b) x' →
          ∃ u : Wˣ, IsFractionRing.lift (A := R) (K := FractionRing R)
              (g := (algebraMap W (FractionRing W)).comp g) ((IsFractionRing.injective W (FractionRing W)).comp hg) (x : FractionRing R) =
            algebraMap W (FractionRing W) (u : W) * (x' : FractionRing W)) →
    ∀ (y : P.D.toPre.X) (r : R) (r' : W), PsiCoord P.D.toPre y r → PsiCoord P'.D.toPre (ρ y) r' → Associated (g r) r' := by
  first | exact @GlobalTheory.PsiFromTau.associated_of_tau | exact GlobalTheory.PsiFromTau.associated_of_tau | (intros; apply GlobalTheory.PsiFromTau.associated_of_tau <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplitAllStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.auxiliary_places_split_all : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ _ x => ∀ _ : LC hL x, ∀ v, v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  first | exact @GlobalTheory.SplitPrimeAuxiliary.auxiliary_primes_split | exact GlobalTheory.SplitPrimeAuxiliary.auxiliary_primes_split | (intros; apply GlobalTheory.SplitPrimeAuxiliary.auxiliary_primes_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplitStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.auxiliary_places_split : PrN → AllSt fun _ _ _ _ _ _ x => ∀ v : HeightOneSpectrum (𝓞 (Dof x).host.E), v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  first | exact @GlobalTheory.HeightCounting.Up.split_allSt | exact GlobalTheory.HeightCounting.Up.split_allSt | (intros; apply GlobalTheory.HeightCounting.Up.split_allSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedEntriesBoundedSiegelReducedStatement
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balanced_entries_bounded_siegelReduced : ∀ (n : ℕ) (K : ℝ), ∃ C : ℝ, ∀ (A A' : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u → (∀ i, 0 < d i) → (A.map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u * A'.map (Int.cast : ℤ → ℝ) → (((A' * A).trace : ℤ) : ℝ) ≤ K → ∀ i j, ((|A i j| : ℤ) : ℝ) ≤ C := by
  first | exact @GlobalTheory.RedTh.balanced_entries_bounded | exact GlobalTheory.RedTh.balanced_entries_bounded | (intros; apply GlobalTheory.RedTh.balanced_entries_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedFormCellMultiplicityPos
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem cellMult_pos {O : Type} [CommRing O] [Module.Finite ℤ O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} (δ : Fin m → balForms bar X) : 0 < cellMult bar δ := by
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  unfold cellMult
  set M := balForms bar X ⧸ Submodule.span ℤ (Set.range δ)
  set T := Submodule.torsion ℤ M
  haveI : IsNoetherian ℤ (LinearMap.BilinForm ℤ X) := inferInstance
  haveI : Module.Finite ℤ M := inferInstance
  haveI : IsNoetherian ℤ M := inferInstance
  haveI : Module.Finite ℤ T := inferInstance
  haveI : AddGroup.FG T := by
    rw [← Module.Finite.iff_addGroup_fg]; infer_instance
  haveI : Finite T := by
    apply AddCommGroup.finite_of_fg_torsion
    rintro ⟨x, hx⟩
    obtain ⟨⟨a, ha⟩, hax⟩ := hx
    refine (isOfFinAddOrder_iff_zsmul_eq_zero).2 ⟨a, nonZeroDivisors.ne_zero ha, ?_⟩
    ext
    exact hax
  exact Nat.card_pos

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeDefiniteUnitaryStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_definite_unitary : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → AllSt fun _ _ _ _ _ _ x => ∀ l : LC hL x, GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → SphericalInertData.Conclusion1 D' := by
  first | exact @GlobalTheory.HeightCounting.Up.conclusion1_thirdSt | exact GlobalTheory.HeightCounting.Up.conclusion1_thirdSt | (intros; apply GlobalTheory.HeightCounting.Up.conclusion1_thirdSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedDomainModelGramContDiffIsUnit
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.PointChern

open GlobalTheory.HermFrame Matrix
open scoped ComplexOrder

theorem mContDiffAt_coordOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {n : ℕ}
    (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (σ : GlobalTheory.AllWt.Psi H) (w : ReciprocityTheory.L2DbarEstimates.V n) :
    MContDiffAt 2 (fun u => coordOf ix u σ) w := fun a b => by
  have : (fun u : ReciprocityTheory.L2DbarEstimates.V n => coordOf ix u σ a b) =
      ((EuclideanSpace.proj (𝕜 := ℂ) (ix.symm (σ, a, b))).restrictScalars ℝ) := by
    funext u; rfl
  rw [this]
  exact ContinuousLinearMap.contDiff _ |>.contDiffAt

theorem one_sub_map_conj_mul_transpose {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) :
    (1 - z.map (starRingEnd ℂ) * zᵀ) = (1 - z * zᴴ)ᵀ := by
  ext a b
  simp [Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply, eq_comm, mul_comm]

theorem isUnit_det_one_sub_map_conj {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) (h : (1 - zᴴ * z).PosDef) :
    IsUnit (1 - z.map (starRingEnd ℂ) * zᵀ).det := by
  rw [one_sub_map_conj_mul_transpose, det_transpose, det_one_sub_mul_comm]
  exact (h.det_pos.ne').isUnit

theorem isUnit_det_one_sub_conjTranspose {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) (h : (1 - zᴴ * z).PosDef) :
    IsUnit (1 - zᴴ * z).det :=
  (h.det_pos.ne').isUnit

theorem MContDiffAt.map_conj {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {m n : Type*} {k : WithTop ℕ∞}
    {A : V → Matrix m n ℂ} {z : V} (h : MContDiffAt k A z) :
    MContDiffAt k (fun x => (A x).map (starRingEnd ℂ)) z :=
  fun a b => Complex.conjCLE.contDiff.contDiffAt.comp z (h a b)

end GlobalTheory.PointChern

namespace GlobalTheory.PointChern
open GlobalTheory.HermFrame Matrix
open scoped ComplexOrder

theorem modelGram_smooth_isUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n), InDom (coordOf ix w) → ∀ τ, MContDiffAt 2 (fun u => modelGram H Dw (coordOf ix u) τ) w ∧ IsUnit (modelGram H Dw (coordOf ix w) τ).det := by
  intro E _ _ _ H Dw n ix w hw τ
  by_cases h : τ (H.rt : E) = H.rt0
  · have hZ := mContDiffAt_coordOf ix ⟨τ, h⟩ w
    have hA : MContDiffAt 2 (fun u => 1 - (coordOf ix u ⟨τ, h⟩).map (starRingEnd ℂ) * (coordOf ix u ⟨τ, h⟩)ᵀ) w :=
      (mContDiffAt_const 1).sub ((GlobalTheory.PointChern.MContDiffAt.map_conj hZ).mul hZ.transpose)
    have hu := isUnit_det_one_sub_map_conj _ (hw ⟨τ, h⟩)
    simp only [modelGram, dif_pos h]
    refine ⟨?_, ?_⟩
    · simp only [reindex_apply]
      exact (hA.inv hu).submatrix _ _
    · rw [det_reindex_self]
      exact isUnit_nonsing_inv_det_iff.mpr hu
  · by_cases h' : conjEmb τ (H.rt : E) = H.rt0
    · have hZ := mContDiffAt_coordOf ix ⟨conjEmb τ, h'⟩ w
      have hA : MContDiffAt 2 (fun u => 1 - (coordOf ix u ⟨conjEmb τ, h'⟩)ᴴ * coordOf ix u ⟨conjEmb τ, h'⟩) w :=
        (mContDiffAt_const 1).sub (hZ.conjTranspose.mul hZ)
      have hu := isUnit_det_one_sub_conjTranspose _ (hw ⟨conjEmb τ, h'⟩)
      simp only [modelGram, dif_neg h, dif_pos h']
      refine ⟨?_, ?_⟩
      · simp only [reindex_apply]
        exact (hA.inv hu).submatrix _ _
      · rw [det_reindex_self]
        exact isUnit_nonsing_inv_det_iff.mpr hu
    · simp only [modelGram, dif_neg h, dif_neg h']
      exact ⟨mContDiffAt_const 1, by simp⟩

end GlobalTheory.PointChern
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalTrivialOfRelativeAmple
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.KTrivSpread

namespace GlobalTheory.KTrivGenericPt

theorem spMap_eq_lift_comp_jK {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] (ψ : R →+* F)
    (hψ : Function.Injective ψ) :
    spMap ψ = spMap (IsFractionRing.lift (K := FractionRing R) hψ) ≫ Out.jK R := by
  rw [Out.jK, spMap, spMap, ← Spec.map_comp]
  congr 1
  ext r
  simp

theorem trivAlong_field {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {R : Type} [CommRing R] [IsDomain R]
    {g : Sp R ⟶ S} (h : TrivAlong A L (Out.jK R ≫ g)) {F : Type} [Field F] (ψ : R →+* F)
    (hψ : Function.Injective ψ) : TrivAlong A L (spMap ψ ≫ g) := by
  rw [spMap_eq_lift_comp_jK ψ hψ, Category.assoc]
  exact h.comp _

end GlobalTheory.KTrivGenericPt

open GlobalTheory.KTrivGenericPt in

theorem GlobalTheory.KTrivGenericPt.kTriv_of_polAt_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (t : SAB H (Sp R)), IsProper t.G.hom → RelAmple t.G t.PP.L → GlobalTheory.LN.PolAt t (jK R) → KTriv t.G t.PP.L := by
  intro E _ _ _ H R _ _ _ _ t hP ha hpol
  haveI : IsProper t.G.hom := hP
  have hA : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have hgen : TrivAlong t.G t.PP.L (Out.jK R) :=
    trivAlong_of_kTriv (isGrpPullback_pullback t.G (Out.jK R)) t.PP.isLB hpol.2.2
  have hgen' : TrivAlong t.G t.PP.L (Out.jK R ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; exact hgen
  refine kTriv_of_primes hG R t.G hA t.PP.L t.PP.isLB ha fun p => ?_
  let O := Localization.AtPrime p.asIdeal
  have hO : Function.Injective (algebraMap R O) := IsLocalization.injective O p.asIdeal.primeCompl_le_nonZeroDivisors
  have hp : PrimeSpectrum.comap (algebraMap R O) (IsLocalRing.closedPoint O) = p :=
    PrimeSpectrum.ext Localization.AtPrime.under_maximalIdeal
  by_cases hf : IsField O
  · refine ⟨O, inferInstance, algebraMap R O, ⟨_, hp⟩, ?_⟩
    letI := hf.toField
    have := trivAlong_field hgen' (algebraMap R O) hO
    rwa [Category.comp_id] at this
  · obtain ⟨V, _, _, _, ρ, h1, h2⟩ := exists_dvr O hf
    have hρ : Function.Injective (ρ.comp (algebraMap R O)) := h1.comp hO
    have : CharZero V := charZero_of_injective_ringHom hρ
    refine ⟨V, inferInstance, ρ.comp (algebraMap R O), ⟨IsLocalRing.closedPoint V, ?_⟩, ?_⟩
    · rw [PrimeSpectrum.comap_comp_apply, IsLocalRing.comap_closedPoint, hp]
    · have key := trivAlong_dvr hG (𝟙 (Sp R)) hA t.PP t.cub ha V (spMap (ρ.comp (algebraMap R O))) ?_
      · rwa [Category.comp_id] at key
      · let F := AlgebraicClosure (FractionRing V)
        have H' := trivAlong_field hgen'
          ((algebraMap (FractionRing V) F).comp ((algebraMap V (FractionRing V)).comp (ρ.comp (algebraMap R O))))
          ((algebraMap (FractionRing V) F).injective.comp ((IsFractionRing.injective V (FractionRing V)).comp hρ))
        have e : (Out.TF (R := V) F).hom ≫ spMap (ρ.comp (algebraMap R O)) = spMap ((algebraMap (FractionRing V) F).comp
            ((algebraMap V (FractionRing V)).comp (ρ.comp (algebraMap R O)))) :=
          (congrArg (· ≫ _) (Spec.map_comp _ _).symm).trans (Spec.map_comp _ _).symm
        rw [← e, Category.assoc] at H'
        exact H'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardCmTypeEmbeddingsFixingRootEqHalfFinrankStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_cmTypeEmbeddingsFixingRoot_eq_half_finrank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), Fintype.card (GlobalTheory.AllWt.Psi H) = Module.finrank ℚ E / 2 := by
  first | exact @GlobalTheory.CMTypeCard.card_psi_eq_half | exact GlobalTheory.CMTypeCard.card_psi_eq_half | (intros; apply GlobalTheory.CMTypeCard.card_psi_eq_half <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardGLResidueTypePrimeDvdCardTypeGroup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.ZetaSer

theorem coeffRings_contain_rootsOfUnity_of_groupOrder (D : D7) (h : RootsLL D) : GlobalTheory.PendOf.CoeffRingsHaveRootsOfUnity D := by
  obtain ⟨ζ, hζ⟩ := h
  intro i
  have hpos := D.what₂.restRowsFiniteGroupCard_pos
  have hz : IsPrimitiveRoot (D.nd.embK i ζ) D.what₂.restRowsFiniteGroupCard := hζ.map_of_injective (D.nd.embK i).injective
  have hint : IsIntegral (D.nd.O i) (D.nd.embK i ζ) := ⟨Polynomial.X ^ D.what₂.restRowsFiniteGroupCard - Polynomial.C 1,
    Polynomial.monic_X_pow_sub_C 1 hpos.ne', by simp [hz.pow_eq_one]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, ?_⟩
  rw [← hy] at hz
  exact hz.of_map_of_injective (IsFractionRing.injective _ _)

theorem trace_mem_fieldRange {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {L : Type} [Field L] (e : L →+* ℂ) {n : ℕ} (hn : 0 < n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (f : Module.End ℂ V) (hf : f ^ n = 1) : LinearMap.trace ℂ V f ∈ e.fieldRange := by
  classical
  let b := Module.finBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace_eq_sum_roots_charpoly]
  refine multiset_sum_mem _ fun μ hμ => ?_
  have hroot : (LinearMap.charpoly f).IsRoot μ := by
    rw [← LinearMap.charpoly_toMatrix f b]
    exact (Polynomial.mem_roots'.mp hμ).2
  obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).2 hroot).exists_hasEigenvector
  have hpow : μ ^ n = 1 := by
    have h1 := hv.pow_apply n
    rw [hf, Module.End.one_apply] at h1
    have h2 : (μ ^ n - 1) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv.2)
  have hζc := hζ.map_of_injective e.injective
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨j, -, hj⟩ := hζc.eq_pow_of_pow_eq_one hpow
  exact ⟨ζ ^ j, by rw [map_pow, hj]⟩

end GlobalTheory.ZetaSer

namespace GlobalTheory.ZetaSer

theorem card_GL_residue_typePrime_dvd_card_typeGroup (D : D7) (k : Fin 2) :
    Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) ∣ D.what₂.restRowsFiniteGroupCard := by
  rw [D.nd.restN_card_levelGroup_eq]
  have hf : D.R.f ≠ 0 := by
    unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n
    positivity
  exact (dvd_pow_self _ hf).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))

theorem coeff_zIdem_mem {Γ : Type} [Group Γ] [Fintype Γ] {L : Type} [Field L] (e : L →+* ℂ) {n : ℕ} (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (hΓ : Nat.card Γ ∣ n) (τ : FDRep ℂ Γ) (γ : Γ) :
    (Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ).coeff γ ∈ e.fieldRange := by
  rw [Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff]
  refine mul_mem (div_mem (natCast_mem _ _) (natCast_mem _ _)) (trace_mem_fieldRange e hn hζ _ ?_)
  obtain ⟨c, hc⟩ := hΓ
  rw [← map_pow, hc, pow_mul, pow_card_eq_one', one_pow, map_one]

theorem serLL_of_rootsLL (D : D7) (h : RootsLL D) (G : GrpSide D) : GlobalTheory.PendOf.SerLL D := by
  obtain ⟨ζ, hζ⟩ := h
  intro k f γ
  apply RingHom.mem_fieldRange.mp
  rw [G.eSer_def k f]
  unfold eSerO
  refine finsum_induction (fun x : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) => x.coeff γ ∈ D.what₂.embLL.fieldRange) ?_ ?_ fun z => ?_
  · simp
  · intro x y hx hy
    simpa using add_mem hx hy
  · refine finsum_induction (fun x : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) => x.coeff γ ∈ D.what₂.embLL.fieldRange) ?_ ?_ fun hz => ?_
    · simp
    · intro x y hx hy
      simpa using add_mem hx hy
    · obtain ⟨τ, -, rfl, -⟩ := hz
      exact coeff_zIdem_mem _ D.what₂.restRowsFiniteGroupCard_pos hζ (card_GL_residue_typePrime_dvd_card_typeGroup D k) τ γ

theorem rootsOfUnity_and_seriesIdempotent_rational : ∀ D : D7, RootsLL D → GlobalTheory.PendOf.CoeffRingsHaveRootsOfUnity D ∧ (GrpSide D → GlobalTheory.PendOf.SerLL D) :=
  fun D h => ⟨coeffRings_contain_rootsOfUnity_of_groupOrder D h, serLL_of_rootsLL D h⟩

end GlobalTheory.ZetaSer
end

