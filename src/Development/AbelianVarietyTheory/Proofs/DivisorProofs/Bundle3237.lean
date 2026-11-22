import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3213
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3214
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2792
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2977
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3059
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3038
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2661
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2663
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedComplexFibreMarkedLatticeClass
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsMemNormalDomainStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSymmetricFunctions_mem_normalDomain : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ e : Fin N → R, SymAt G L ρ m x θ e := by
  first | exact @GlobalTheory.UMin.SymRing.sym_ring | exact GlobalTheory.UMin.SymRing.sym_ring | (intros; apply GlobalTheory.UMin.SymRing.sym_ring <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemRechartAffineOpenAtClassicalTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSystem_rechart_affineOpen_at_classicalTrait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁), ∃ (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)) (u' : Sp R' ⟶ F.X), Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X₁.ρ.i₀ ∧ R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧ IsDiagEnd F W ρ'.P u' ε' ∧ ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) ∧ spMap y₀ ≫ u' = spMap c.ι ≫ c.T.y ∧ ∀ a : X₁.o₁, ‖y₀ (algebraMap X₁.o₁ R' a)‖ ≤ 1 := by
  first | exact @GlobalTheory.Poinc.rechart_at_classical_trait | exact GlobalTheory.Poinc.rechart_at_classical_trait | (intros; apply GlobalTheory.Poinc.rechart_at_classical_trait <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopChernDensityHolomorphicChartEtaleStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_chern_density_holomorphic_chart_etale : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ (c : AlgChart X.str σ X.dim) {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → y ∈ e.source → y ∈ c.e.source → ∀ {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → (Real.pi ^ X.dim)⁻¹ * (mixTop fun _ => curvAt (fun v => H A (e.symm v) ()) (e y)).re = ‖transDet e c.e y‖ ^ 2 * topDens E H c y := by
  first | exact @GlobalTheory.GoodTop.topDens_holoChart | exact GlobalTheory.GoodTop.topDens_holoChart | (intros; apply GlobalTheory.GoodTop.topDens_holoChart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityBaseFormTimesFibreClassStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeDensity_base_form_times_fibre_class : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (a : V d → Alt d) (w : V n), (∀ τ, (G (bsL ε w) τ).PosDef) → (∀ τ, MContDiffAt 2 (fun v => G v τ) (bsL ε w)) → dens (cellForm ε G a w) = dens (a (bsL ε w)) * (fibDens (G (bsL ε w)) (fb ε w) : ℝ) := by
  first | exact @GlobalTheory.FlagCell2.CellDens.dens_cellForm | exact GlobalTheory.FlagCell2.CellDens.dens_cellForm | (intros; apply GlobalTheory.FlagCell2.CellDens.dens_cellForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTransportCmConjugation
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ConjHerm

theorem exists_conj_herm : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)), (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) →
          (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') →
          (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) →
          ∃ (u'' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E))) (h' : I → ℝ), u''.ex = u'.ex ∧
            (∃ χ, u''.IsAH (Matrix.diagonal fun j ↦ (h' (T.U.e j) : ℂ)) χ) ∧
            ∀ i, g ((T.U.h i : ℂ) * (Real.sqrt d : ℝ)) = ((modF t : ℝ) : ℂ) * ((h' i : ℂ) * (Real.sqrt d : ℝ)) := by
  intro hPC hADR hADC K _ _ d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E _ _ _ _ I _ φ hφ hres c y hc 𝔠 T X' p hp u' hΛ hdiff hex
  obtain ⟨u₀, Hm, χ, hex₀, hAH⟩ := GlobalTheory.RealMult.Obj.exists_isAH_diag (FR E) 𝔠 X' T.U.c T.U.pos u'
  obtain ⟨β, hβ⟩ := GlobalTheory.T.cm_point_hodge_period_formula E I φ hφ c y hc 𝔠 T
  have hE := GlobalTheory.T.torsion_transport_cm_period hPC hADR hADC K d δ io hK hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E I φ hφ hres c y hc 𝔠 T X' p hp u' hΛ hdiff hex
    u₀ Hm χ hex₀ hAH
  have hmem : ∀ w, w ∈ u₀.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ g (φ (T.U.e j) x) := by
    intro w
    rw [← u₀.ker, hex₀, u'.ker, hΛ]
    simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]
  have hN : 0 < modF t := by
    unfold modF
    refine finprod_induction (fun x => 0 < x) one_pos (fun _ _ => mul_pos) (fun v => ?_)
    have : (0:ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by
      exact_mod_cast Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
    exact zpow_pos this _
  obtain ⟨h', hHm, hid⟩ := GlobalTheory.T.cm_lattice_spans_real_space K d δ io hd hδ g hT.2.2.1 E I φ hφ hres _ T.U.e u₀.Λ _ u₀.full hmem T.U.h β hβ
    (modF t) hN Hm hAH.1 hE
  exact ⟨u₀, h', hex₀, ⟨χ, hHm ▸ hAH⟩, hid⟩

end GlobalTheory.ConjHerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTransportCmUniformizationStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_transport_cm_uniformization : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)),
 (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') → (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) := by
  first | exact @GlobalTheory.cmTorsionConj | exact GlobalTheory.cmTorsionConj | (intros; apply GlobalTheory.cmTorsionConj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorPointOverStrictHenselisationNoetherianNormStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsor_point_over_strictHenselisation_noetherianNormal : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra.EssFiniteType ℤ A]
      (i : A →+* T), Function.Injective i → IsLocalHom i → IsUnit (q : A) →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ σ : DA →+* GlobalTheory.LocAcyc.GenFib T O, σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = ψA := by
  first | (exact @GlobalTheory.KeyOriginNoeth.torsor_point_of_essFiniteType) | (exact GlobalTheory.KeyOriginNoeth.torsor_point_of_essFiniteType) | (intros; apply GlobalTheory.KeyOriginNoeth.torsor_point_of_essFiniteType  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinateUniformisationTranslateEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumCmp.TranslCoord

theorem coord_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)), wL.IsGen → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left), h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom → h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → ∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.val ((U.gt e).t (xe χ)) (r ≫ h) z J = (∏ k, Geo.Tor.gv w (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) z (fun i => J ((r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k)) ^ Oinvε k) * Geo.Tor.val ((U₂.gt e).t χ) r z J' * Geo.Tor.val (g.s (xe χ)) (r ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e) z J := by
  intro R _ _ _ hR D A G _ _ hG U g hg a ha hlev A₂ D₂ U₂ wL hwL β hβ hp w hw xe hker hc e h hh hfst χ Z r z J J' hJ hJ'
  have hpg := GlobalTheory.T.uniformisation_translate_lift_torus_image_eq_add R (maximalIdeal R) D D₂ A A₂ G U.toUnifPre U₂.toUnifPre g a β hβ e (hp e)
    (fun ae h1 h2 => (hlev e ae h1 h2).1) h hh hfst
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.exists_generator_corrected_torusCoordinate_ratio (U.gt e) (U₂.gt e) β.hom g w hw χ (xe χ) (hc χ) h hh hpg
  have hp' : (U₂.gt e).pG ≫ β.hom = (U.gt e).pG := Over.OverMorphism.ext (hp e)
  have := (U.gt e).q_flat
  have := (U.gt e).q_surj
  have := (U.gt e).q_affine
  obtain ⟨v, hv, hv'⟩ := GlobalTheory.CoordCompare.exists_gen_of_val_eq D.toPre.P.isLB _ _ (U.gt e).q.left u hu
    (fun Z r r' z J hJ hrr => by
      obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D₂.toPre.P.L D₂.toPre.P.isLB z
      rw [hu' Z r z J J' hJ hJ', hu' Z r' z J J' hJ hJ']
      exact GlobalTheory.T.twistedCoordinateRatio_fibre_invariant (U.gt e) (U₂.gt e) β.hom hp' g w χ (xe χ)
        (fun Z r z J J' hJ hJ' h1 h2 => hker e Z r z J J' hJ hJ' h1 h2 χ) a h hh hfst r r' z J J' hJ hJ' hrr)
  have h1 := GlobalTheory.CoordCompare.val_eq_one GlobalTheory.globalFns_holds (D.toPre.c (xe χ)) _ rfl v hv (fun y J hJ => by
      obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D₂.toPre.P.L D₂.toPre.P.isLB y
      have := (U.gt e).q_hom
      have k := hv' _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶ thickObj R (maximalIdeal R) e G).left y J hJ
      rw [← Over.comp_left, MonObj.one_comp] at k
      rw [k, hu' _ _ y J J' hJ hJ']
      exact GlobalTheory.T.twistedCoordinateRatio_eq_one_unitSection (U.gt e) (U₂.gt e) β.hom g w χ (xe χ) a h hh hfst (fun ae h1 h2 => (hlev e ae h1 h2).2 (xe χ)) y J J' hJ hJ')
    Z (r ≫ (U.gt e).q.left) z J hJ
  rw [hv' Z r z J hJ, hu' Z r z J J' hJ hJ', mul_inv_eq_one] at h1
  exact h1

end GlobalTheory.MumCmp.TranslCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusFormStatementHolds
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusFormPf

theorem embOfCM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (e₀ : Fin (Module.finrank ℚ (FR E)) ≃ I),
    ∃ e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ), ∀ j (x : FR E), (e j x : ℂ) = φ (e₀ j) (x : E) := GlobalTheory.T.exists_real_embedding_ordering

theorem realEmb_indep : ∀ (F : Type) [Field F] [NumberField F] (a : (F →+* ℝ) → ℝ),
    (∀ x : 𝓞 F, ∑ τ, a τ * τ (x : F) = 0) → a = 0 := GlobalTheory.T.real_embeddings_linearly_independent

theorem riemannForm_of_unif : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
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
      (∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 F) {t | ∃ l l' : u.Λ, t = P l l'}) := GlobalTheory.T.diagonal_appell_humbert_real_mult

theorem steinitz_sympl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ (𝔞 𝔟 : FracId (FR E)) (P : E → E → FR E),
    (∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P x x' = -P x' x) →
    (∀ x₁ ∈ lattice c y, ∀ x₂ ∈ lattice c y, ∀ x' ∈ lattice c y, P (x₁ + x₂) x' = P x₁ x' + P x₂ x') →
    (∀ (a : 𝓞 (FR E)), ∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P (((a : FR E) : E) * x) x' = (a : FR E) * P x x') →
    (∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P x x' ∈ dualLat (𝔞 * 𝔟⁻¹)) →
    (∀ t ∈ dualLat (𝔞 * 𝔟⁻¹), t ∈ Submodule.span (𝓞 (FR E)) {t | ∃ x ∈ lattice c y, ∃ x' ∈ lattice c y, t = P x x'}) →
    ∃ ω₁ ω₂ : E, (∀ x, x ∈ lattice c y ↔ ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt, x = (m : E) * ω₁ + (β : E) * ω₂) ∧
      ∀ m ∈ dualLat 𝔞, ∀ β ∈ 𝔟.elt, ∀ m' ∈ dualLat 𝔞, ∀ β' ∈ 𝔟.elt,
        P ((m : E) * ω₁ + (β : E) * ω₂) ((m' : E) * ω₁ + (β' : E) * ω₂) = β * m' - m * β' := GlobalTheory.T.alternating_pairing_on_lattice

theorem holUnif_rescale : ∀ (A : Over (Sp ℂ)) [GrpObj A] (Lb : LB A.left) (g : ℕ) (u : HolUnif A Lb g) (lam : Fin g → ℂ),
    (∀ j, lam j ≠ 0) → ∃ u' : HolUnif A Lb g, (∀ w, u'.ex w = u.ex (fun j ↦ lam j * w j)) ∧
      (∀ (d : Fin g → ℝ) χ, u.IsAH (Matrix.diagonal fun j ↦ (d j : ℂ)) χ →
        ∃ χ', u'.IsAH (Matrix.diagonal fun j ↦ ((d j * ‖lam j‖ ^ 2 : ℝ) : ℂ)) χ') ∧
      (∀ W v, u'.IsDiff W v ↔ u.IsDiff (fun j ↦ lam j * W j) v) := GlobalTheory.T.rescaled_uniformization

end GlobalTheory.TorusFormPf

namespace GlobalTheory.TorusFormPf

theorem lattice_add {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)} {y : (Af E)ˣ} {x x' : E}
    (hx : x ∈ lattice c y) (hx' : x' ∈ lattice c y) : x + x' ∈ lattice c y := by
  simp only [lattice, Set.mem_setOf_eq, map_add, add_mul] at *
  exact Subring.add_mem _ hx hx'

theorem lattice_smul {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)} {y : (Af E)ˣ} {x : E}
    (a : 𝓞 (FR E)) (hx : x ∈ lattice c y) : ((a : FR E) : E) * x ∈ lattice c y := by
  have := mul_mem_lattice (algebraMap_mem_orderC c a) hx
  convert this using 2
  first | rfl | simp [IsScalarTower.algebraMap_apply (OF E) (FR E) E] | exact (IsScalarTower.algebraMap_apply (OF E) (FR E) E a).symm

theorem torusForm : TorusForm := by
  intro E _ _ _ I _ 𝔞 𝔟 φ c y hCM hc z hz X U
  obtain ⟨e, he⟩ := embOfCM E I φ hCM U.e
  have hreal : ∀ j (x : FR E), starRingEnd ℂ (φ (U.e j) (x : E)) = φ (U.e j) (x : E) := by
    intro j x; rw [← he]; exact Complex.conj_ofReal _
  set D : E → Fin (Module.finrank ℚ (FR E)) → ℂ := fun x j ↦ defCoord φ z x (U.e j) with hD
  have hDadd : ∀ x x', D (x + x') = D x + D x' := by
    intro x x'; funext j; simp only [hD, defCoord, map_add, Pi.add_apply]; ring
  have hDsmul : ∀ (a : FR E) x, D ((a : E) * x) = fun j ↦ (e j a : ℂ) * D x j := by
    intro a x; funext j; simp only [hD, defCoord, map_mul]; rw [hreal j a, ← he]; ring
  have hact : ∀ (a : 𝓞 (FR E)) w, U.u.ex (fun j ↦ (e j (a : FR E) : ℂ) * w j) = U.u.ex w ≫ X.rm.act a := by
    intro a w; simpa only [he] using U.act a w
  obtain ⟨χ, hAH⟩ := U.ah
  obtain ⟨P, hPalt, hPadd, hPsmul, hPtr, hPmem, hPspan⟩ := riemannForm_of_unif (FR E) (𝔞 * 𝔟⁻¹) X U.c U.pos U.u e hact
    (fun j ↦ U.h (U.e j)) χ hAH
  have hDmem : ∀ x ∈ lattice c y, D x ∈ U.u.Λ := fun x hx ↦ (U.lat _).2 ⟨x, hx, rfl⟩
  classical
  let PL : E → E → FR E := fun x x' ↦
    if hx : x ∈ lattice c y ∧ x' ∈ lattice c y then P ⟨D x, hDmem x hx.1⟩ ⟨D x', hDmem x' hx.2⟩ else 0
  have hPL : ∀ x (hx : x ∈ lattice c y) x' (hx' : x' ∈ lattice c y),
      PL x x' = P ⟨D x, hDmem x hx⟩ ⟨D x', hDmem x' hx'⟩ := by
    intro x hx x' hx'; simp only [PL, dif_pos (And.intro hx hx')]
  obtain ⟨ω₁, ω₂, hL, hPω⟩ := steinitz_sympl E c y hc 𝔞 𝔟 PL
    (by intro x hx x' hx'; rw [hPL x hx x' hx', hPL x' hx' x hx]; exact hPalt _ _)
    (by
      intro x₁ h₁ x₂ h₂ x' h'
      rw [hPL _ (lattice_add h₁ h₂) x' h', hPL x₁ h₁ x' h', hPL x₂ h₂ x' h', ← hPadd]
      congr 1; exact Subtype.ext (hDadd x₁ x₂))
    (by
      intro a x hx x' hx'
      rw [hPL _ (lattice_smul a hx) x' hx', hPL x hx x' hx']
      exact hPsmul a _ _ _ (hDsmul (a : FR E) x))
    (by intro x hx x' hx'; rw [hPL x hx x' hx']; exact hPmem _ _)
    (by
      intro t ht
      have := hPspan t ht
      refine Submodule.span_mono ?_ this
      rintro s ⟨l, l', rfl⟩
      obtain ⟨x, hx, hxl⟩ := (U.lat l).1 l.2
      obtain ⟨x', hx', hxl'⟩ := (U.lat l').1 l'.2
      refine ⟨x, hx, x', hx', ?_⟩
      rw [hPL x hx x' hx']
      congr 1 <;> apply Subtype.ext <;> assumption)
  set A : Fin (Module.finrank ℚ (FR E)) → ℂ := D ω₁ with hA
  set B : Fin (Module.finrank ℚ (FR E)) → ℂ := D ω₂ with hB
  have hDlin : ∀ m β : FR E, D ((m : E) * ω₁ + (β : E) * ω₂) = fun j ↦ (e j m : ℂ) * A j + (e j β : ℂ) * B j := by
    intro m β; rw [hDadd, hDsmul, hDsmul]; rfl
  have hmemL : ∀ m ∈ dualLat 𝔞, ∀ β ∈ 𝔟.elt, (m : E) * ω₁ + (β : E) * ω₂ ∈ lattice c y :=
    fun m hm β hβ ↦ (hL _).2 ⟨m, hm, β, hβ, rfl⟩
  obtain ⟨β₀, hβ₀, hβ₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (fun h ↦ 𝔟.ne_zero (FractionalIdeal.coeToSubmodule_eq_bot.1 h))
  have hdual0 : dualLat 𝔞 ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ 𝔞.ne_zero
  obtain ⟨m₀, hm₀, hm₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (fun h ↦ hdual0 (FractionalIdeal.coeToSubmodule_eq_bot.1 h))
  have h0a : (0 : FR E) ∈ dualLat 𝔞 := (dualLat 𝔞 : Submodule (𝓞 (FR E)) (FR E)).zero_mem
  have h0b : (0 : FR E) ∈ 𝔟.elt := 𝔟.elt.zero_mem
  have hkey : ∀ x : 𝓞 (FR E), ∑ j, e j (x : FR E) * ((e j β₀ * e j m₀) *
      (U.h (U.e j) * (B j * starRingEnd ℂ (A j)).im - 2 * e j (U.c : FR E))) = 0 := by
    intro x
    have hxβ : (x : FR E) * β₀ ∈ 𝔟.elt := by
      have := 𝔟.elt.smul_mem x hβ₀; rwa [Algebra.smul_def] at this
    have m1 := hmemL 0 h0a _ hxβ
    have m2 := hmemL m₀ hm₀ 0 h0b
    have htr := hPtr ⟨_, hDmem _ m1⟩ ⟨_, hDmem _ m2⟩
    rw [← hPL _ m1 _ m2, hPω 0 h0a _ hxβ m₀ hm₀ 0 h0b, GlobalTheory.trace_eq_sum_realEmbeddings, ← e.sum_comp] at htr
    simp only [hDlin, Complex.im_sum] at htr
    have hl : ∀ j, ((U.h (U.e j) : ℂ) * ((((e j 0 : ℝ) : ℂ) * A j + ((e j ((x : FR E) * β₀) : ℝ) : ℂ) * B j) *
        starRingEnd ℂ (((e j m₀ : ℝ) : ℂ) * A j + ((e j 0 : ℝ) : ℂ) * B j))).im =
        e j (x : FR E) * (e j β₀ * e j m₀ * (U.h (U.e j) * (B j * starRingEnd ℂ (A j)).im)) := by
      intro j
      have : (U.h (U.e j) : ℂ) * ((((e j 0 : ℝ) : ℂ) * A j + ((e j ((x : FR E) * β₀) : ℝ) : ℂ) * B j) *
          starRingEnd ℂ (((e j m₀ : ℝ) : ℂ) * A j + ((e j 0 : ℝ) : ℂ) * B j)) =
          ((U.h (U.e j) * e j (x : FR E) * e j β₀ * e j m₀ : ℝ) : ℂ) * (B j * starRingEnd ℂ (A j)) := by
        simp only [map_zero, map_mul, map_add, Complex.ofReal_zero, Complex.conj_ofReal, zero_mul, zero_add, add_zero]
        push_cast; ring
      rw [this, Complex.im_ofReal_mul]; ring
    simp only [hl] at htr
    rw [← sub_eq_zero, Finset.mul_sum, ← Finset.sum_sub_distrib] at htr
    rw [← htr]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [map_mul, map_sub, map_zero, mul_zero, sub_zero]
    ring
  have hk : ∀ j, U.h (U.e j) * (B j * starRingEnd ℂ (A j)).im = 2 * e j (U.c : FR E) := by
    have hz := realEmb_indep (FR E) (fun σ ↦ (e (e.symm σ) β₀ * e (e.symm σ) m₀) *
      (U.h (U.e (e.symm σ)) * (B (e.symm σ) * starRingEnd ℂ (A (e.symm σ))).im - 2 * e (e.symm σ) (U.c : FR E))) (by
        intro x
        rw [← e.sum_comp]
        simp only [Equiv.symm_apply_apply]
        rw [← hkey x]
        exact Finset.sum_congr rfl fun j _ ↦ by ring)
    intro j
    have := congrFun hz (e j)
    simp only [Equiv.symm_apply_apply, Pi.zero_apply] at this
    have hne : e j β₀ * e j m₀ ≠ 0 := mul_ne_zero ((map_ne_zero _).2 hβ₀0) ((map_ne_zero _).2 hm₀0)
    have := (mul_eq_zero.1 this).resolve_left hne
    linarith
  have hhpos : ∀ j, 0 < U.h (U.e j) := by
    intro j
    have hne : (Pi.single j (1 : ℂ) : Fin (Module.finrank ℚ (FR E)) → ℂ) ≠ 0 := fun h ↦ by simpa using congrFun h j
    have := hAH.2.1 _ hne
    simpa [Matrix.mulVec_diagonal, dotProduct, Pi.single_apply] using this
  have hIm : ∀ j, 0 < (B j * starRingEnd ℂ (A j)).im := by
    intro j
    have hc := U.pos (e j)
    have : 0 < U.h (U.e j) * (B j * starRingEnd ℂ (A j)).im := by rw [hk j]; linarith
    exact pos_of_mul_pos_right this (le_of_lt (hhpos j))
  have hA0 : ∀ j, A j ≠ 0 := by
    intro j h; have := hIm j; rw [h] at this; simp at this
  set τ : (FR E →+* ℝ) → ℂ := fun σ ↦ B (e.symm σ) / A (e.symm σ) with hτdef
  set lam : Fin (Module.finrank ℚ (FR E)) → ℂ := fun j ↦ A j / (2 * Real.pi * Complex.I) with hlamdef
  have hτ : ∀ j, τ (e j) = B j / A j := by intro j; simp [hτdef]
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hlam : ∀ j, lam j ≠ 0 := fun j ↦ div_ne_zero (hA0 j) h2pi
  have hτim : ∀ j, (τ (e j)).im = (B j * starRingEnd ℂ (A j)).im / Complex.normSq (A j) := by
    intro j; rw [hτ, Complex.div_im]; simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
  obtain ⟨u', hex, hAH', hdiff⟩ := holUnif_rescale X.A (X.diag U.c) _ U.u lam hlam
  have hform : ∀ m β : FR E, (fun j ↦ lam j * (2 * Real.pi * Complex.I * ((e j m : ℂ) + (e j β : ℂ) * τ (e j)))) =
      D ((m : E) * ω₁ + (β : E) * ω₂) := by
    intro m β; rw [hDlin]; funext j; rw [hτ]; simp only [hlamdef]; have hAj := hA0 j; field_simp; try ring
  have hlat : ∀ w, w ∈ U.u.Λ ↔ ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt,
      w = fun j ↦ lam j * (2 * Real.pi * Complex.I * ((e j m : ℂ) + (e j β : ℂ) * τ (e j))) := by
    intro w
    rw [U.lat]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨m, hm, β, hβ, rfl⟩ := (hL x).1 hx
      exact ⟨m, hm, β, hβ, (hform m β).symm⟩
    · rintro ⟨m, hm, β, hβ, rfl⟩
      exact ⟨_, hmemL m hm β hβ, hform m β⟩
  refine ⟨e, τ, lam, he, fun σ ↦ ?_, hlam, hlat, ?_⟩
  · have := hτim (e.symm σ)
    simp only [Equiv.apply_symm_apply] at this
    rw [this]
    exact div_pos (hIm _) (Complex.normSq_pos.2 (hA0 _))
  · intro δ hδ
    refine ⟨U.c, u', U.pos, ?_, ?_, ?_, ?_⟩
    · intro w
      have hk' : w ∈ u'.Λ ↔ (fun j ↦ lam j * w j) ∈ U.u.Λ := by rw [← u'.ker, ← U.u.ker, hex]
      rw [hk', hlat]
      refine exists_congr fun m ↦ and_congr_right fun _ ↦ exists_congr fun β ↦ and_congr_right fun _ ↦ ?_
      constructor
      · intro h; funext j; exact mul_left_cancel₀ (hlam j) (congrFun h j)
      · intro h; rw [h]
    · intro a w
      rw [hex, hex, ← hact]
      congr 1; funext j; ring
    · obtain ⟨χ', h'⟩ := hAH' (fun j ↦ U.h (U.e j)) χ hAH
      refine ⟨χ', ?_⟩
      have hm : (fun i ↦ (((2 * e i (U.c : FR E) / (4 * Real.pi ^ 2 * (τ (e i)).im)) : ℝ) : ℂ)) =
          fun j ↦ ((U.h (U.e j) * ‖lam j‖ ^ 2 : ℝ) : ℂ) := by
        funext j
        congr 1
        have hn : ‖lam j‖ ^ 2 = Complex.normSq (A j) / (4 * Real.pi ^ 2) := by
          rw [hlamdef, norm_div, div_pow, Complex.sq_norm]
          congr 1
          simp [Complex.norm_mul, abs_of_pos Real.pi_pos]; ring
        rw [hn, hτim, ← hk j]
        have := hIm j
        have := Complex.normSq_pos.2 (hA0 j)
        field_simp
      rw [hm]; exact h'
    · intro v W hW
      have hW' : ∀ i, U.u.IsDiff (fun j ↦ lam j * W i j) (v i).hom := fun i ↦ (hdiff _ _).1 (hW i)
      rw [hδ v (Matrix.of fun i j ↦ lam j * W i j) hW']
      have hdet : (Matrix.of fun i j ↦ lam j * W i j).det = W.det * ∏ j, lam j := by
        have : (Matrix.of fun i j ↦ lam j * W i j) = W * Matrix.diagonal lam := by
          ext i j; simp [Matrix.mul_diagonal, mul_comm]
        rw [this, Matrix.det_mul, Matrix.det_diagonal]
      rw [hdet]
      have hprod : ∏ j, lam j ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ ↦ hlam j
      have hΩ : (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) = ((Real.sqrt |(discr (FR E) : ℝ)| *
          (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 (FR E))⁰ (FR E)) : ℝ) : ℝ) : ℂ) := by
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm, Real.sqrt_eq_rpow]
      rw [hΩ]; field_simp

end GlobalTheory.TorusFormPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionCorrectionIsTopDegreeFormStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transgression_correction_isTopDegreeForm : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → IsTopForm (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) := by
  first | exact @GlobalTheory.GoodTop.isTopForm_corrDens | exact GlobalTheory.GoodTop.isTopForm_corrDens | (intros; apply GlobalTheory.GoodTop.isTopForm_corrDens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateDualNumberPointInverseConstantTangentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_dual_number_point_inverse_constant_tangent : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (S : Type) [CommRing S] (A : Over (Sp S)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (c : epsR S ⟶ A) (p : Sp S ⟶ A.left), c.left = spMap (algebraMap S (DualNumber S)) ≫ p → ∀ y : epsR S ⟶ A, (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ y.left = spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ c.left ↔ IsTangent (y * c⁻¹)) ∧ ∀ f, tanVal y f = tanVal (y * c⁻¹) f := by
  first | exact @GlobalTheory.TanAdd.translate_const | exact GlobalTheory.TanAdd.translate_const | (intros; apply GlobalTheory.TanAdd.translate_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedComplexFibreMarkedLatticeClassStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_complex_fibre_marked_lattice_class : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL (D' : PLat D.O D.inv) t Q e, 0 < N → N.Coprime p → UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → ∃ t', D.Cls N D' t' ∧ ∀ a, ∃ x, t' a = t a + N • x := by
  first | exact @GlobalTheory.UPel.HT.unifAt_cls | exact GlobalTheory.UPel.HT.unifAt_cls | (intros; apply GlobalTheory.UPel.HT.unifAt_cls <;> assumption)
end

