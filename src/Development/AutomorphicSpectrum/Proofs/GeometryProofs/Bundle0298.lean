import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0296
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyHodgePrimeTotal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0081
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeLimit
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0150
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0194
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0069
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0280
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0005
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0297
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsChartOfLineBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0082
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0173
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0294
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0163
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0224
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistLatticeCompat
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptLabelBases
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0251
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0131
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0196
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0255
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0254
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0232
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0064
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0169
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0234
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0220

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeSpreadsOutFiniteTypeSubringStatement
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
theorem _root_.GlobalTheory.T.abelianScheme_spreads_out_finiteType_subring : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (F : Finset R), IsAbelianScheme A → ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.abelianScheme_descends_to_fg_subring | exact GlobalTheory.CompanionTheory.Ar.Approx.abelianScheme_descends_to_fg_subring | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.abelianScheme_descends_to_fg_subring <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyHodgePrimeTotalStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_hodge_prime_total : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (P : ∀ c' : ∀ k, J k, mseg y c' ≠ 0 → ChartPack G O c') (i : ∀ (c' : ∀ k, J k) (τ), (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), IsLatFamily O y (fun c' => (famD e b pq sc w P i c').M) ∧ ∀ τ : Sg, IsLatFamily O y (fun c' => (famD e b pq sc w P i c').Th τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over.funfam_holds | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over.funfam_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.Over.funfam_holds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyPrimeGlobalRelayStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_prime_global_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∃ (AA : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) RC (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)) (AW : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) RC (Fin (D.p + D.q) → F)), AA.carrier = (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) ∧ AW.carrier = (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC) ∧ AW.carrier.toAddSubgroup = ((chartD e b pq sc w P i).bc RC).M ∧ (∀ h ∈ AA.carrier, (fun x => h ((GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.toNAdd sc) ((GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.fromNAdd pq) x))) ∈ AA.carrier) ∧ GlobalTheory.CompanionTheory.Ar.GR.FStable F AW.carrier := by
  first | exact @GlobalTheory.CompanionTheory.Relay.arith_variety_prime_global_relay | exact GlobalTheory.CompanionTheory.Relay.arith_variety_prime_global_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.arith_variety_prime_global_relay <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartDThSqIdealMemAndSmulMemAndEigMemSqIdealStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartD_th_sqIdeal_mem_and_smul_mem_and_eig_mem_sqIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] (σ' : MulChar F RC) (ee : Sg → ℕ), (∀ τ a, χ τ a = ((σ' ^ p ^ ee τ) a : RC)) → ∀ τ, (∀ g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC)), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → ((fun x => g (a • x)), χ τ a • m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ ∀ g ∈ GlobalTheory.CompanionTheory.Ar.GR.eig (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC) (σ' ^ p ^ ee τ), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.chartD_th_sqIdeal_mem_and_smul_mem_and_eig_mem_sqIdeal | exact GlobalTheory.CompanionTheory.Relay.chartD_th_sqIdeal_mem_and_smul_mem_and_eig_mem_sqIdeal | (intros; apply GlobalTheory.CompanionTheory.Relay.chartD_th_sqIdeal_mem_and_smul_mem_and_eig_mem_sqIdeal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeLimitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_volume_limit : GlobalTheory.CompanionTheory.Ar.Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E (CMType H) Dc.j Dc.j' Dc.n g Λ) (V : Set (Fin Dc.n → ℂ)) (z : (Fin Dc.n → ℂ) → (Sp ℂ ⟶ Or.𝔐.X)) (gm : (Fin Dc.n → ℂ) → (Σ k, J k) → ℂ), IsOpen V → V ⊆ ballDom F.q → DifferentiableOn ℂ gm V → (∀ t ∈ V, CoordsAt Or.𝔐.ξ Dc.y (z t) (gm t) ∧ Or.𝔐.Interior (z t) ∧ Or.𝔐.LabVal (z t) Or.sm F.σ) → (∀ t₀ ∈ V, ∀ (m : ℕ) (s : Fin m → Or.𝔐.Li), (∀ a, ∃ v, Or.𝔐.M.ValAt (z t₀) (s a) v) → ∃ x : Fin m → (Fin Dc.n → ℂ) → Fin g → ℂ, (∀ a, AnalyticAt ℂ (x a) t₀) ∧ ∀ᶠ t in 𝓝 t₀, ∃ v : Fin m → (epsAt (z t) ⟶ Or.𝔐.t.G), (∀ a, Or.𝔐.M.ValAt (z t) (s a) (v a)) ∧ FibreLatVec Or.𝔐.t (z t) (F.R t) (fun a => x a t) v) → ∀ t ∈ V, ∃ G : (Fin Dc.n → ℂ) → ℂ, AnalyticAt ℂ G t ∧ ∀ᶠ t' in 𝓝 t, phMu Hd (gm t') = ballPot F.q t' / 2 + (G t').re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.phMu_eq_ballPot_half | exact GlobalTheory.CompanionTheory.Ar.Cusp.phMu_eq_ballPot_half | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.phMu_eq_ballPot_half <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeDedekindTwistStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_lattice_dedekind_twist : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (f : X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (cst : c.F →+* Ω) (S : Finset ℕ) (R : ℕ → ℕ) [IsLocallyNoetherian X], ξ ≫ f = y₀ ≫ Y.j → ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → M.IsActOf t.act.act ρ → IsCptGen ξ → Flat.NormalCpt ξ → (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, FullTorsion t.G ξ (p ^ R p)) → (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ R p)) → (∀ p ∈ S, ∀ s, ((M.htOm t.PP.L (p ^ R p)).map (eigSp ρ (cst.comp (labelEmb c s))).dualRestrict).IsVB (labelRk D s) ⊤) → ∀ s, (Lat.patch S (M.eigLat ρ (cst.comp (labelEmb c s))) fun p => htLabel M t.PP.L (p ^ R p) ρ (fun s' => cst.comp (labelEmb c s')) s).IsVB (labelRk D s) (eigSp ρ (cst.comp (labelEmb c s))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.hodgeLattices_isVB | exact GlobalTheory.CompanionTheory.Ar.hodgeLattices_isVB | (intros; apply GlobalTheory.CompanionTheory.Ar.hodgeLattices_isVB <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfParts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.TopA

theorem exists_padic_emb (F : IntermediateField ℚ ℂ) [NumberField F] (p : Nat.Primes) :
    Nonempty (F →+* ℂ_[p]) :=
  ⟨(IsAlgClosed.lift (M := ℂ_[p]) (R := ℚ) (S := F)).toRingHom⟩

theorem eq_of_clopen_irred {X : Type*} [TopologicalSpace X] {U U' : Set X} (hU : IsClopen U)
    (hUi : IsIrreducible U) (hU' : IsClopen U') (hUi' : IsIrreducible U') {u : X} (hu : u ∈ U) (hu' : u ∈ U') :
    U = U' :=
  (hUi.isConnected.isPreconnected.subset_isClopen hU' ⟨u, hu, hu'⟩).antisymm
    (hUi'.isConnected.isPreconnected.subset_isClopen hU ⟨u, hu', hu⟩)

theorem finite_primes_dvd {n : ℕ} (hn : n ≠ 0) : {p : Nat.Primes | (p : ℕ) ∣ n}.Finite :=
  ((Set.finite_Iic n).preimage Subtype.val_injective.injOn).subset fun p hp =>
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hp

theorem model_hyp {K : Type} [Field K] (V : ValuationSubring K) [IsDiscreteValuationRing V] :
    Function.Injective V.subtype ∧ IsNoetherianRing V ∧
      ∀ x : K, ∃ a b : V, V.subtype b ≠ 0 ∧ x * V.subtype b = V.subtype a := by
  refine ⟨Subtype.val_injective, inferInstance, fun x => ?_⟩
  rcases V.mem_or_inv_mem x with h | h
  · exact ⟨⟨x, h⟩, 1, by simp, by simp⟩
  · by_cases hx : x = 0
    · exact ⟨0, 1, by simp, by simp [hx]⟩
    · exact ⟨1, ⟨x⁻¹, h⟩, by simpa using hx, by simp [hx]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_place {l : Level H} (c : Coeff l) [NumberField c.F] (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) :
    ∃ W : ValuationSubring ℂ, ((p : ℕ) : ℂ) ∈ W.nonunits ∧ IsDiscreteValuationRing (c.V W) ∧
      ∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ c.V W := by
  obtain ⟨W, hp, hW⟩ := GlobalTheory.T.padic_embedding_valuation_subring c.F p κ
  obtain ⟨V, hV, hκ, -, -⟩ := GlobalTheory.T.padic_embedding_discrete_valuation_ring c.F p κ
  have hmem : ∀ x : c.F, x ∈ c.V W ↔ ‖κ x‖ ≤ 1 := fun x => (hW x).symm
  have heq : c.V W = V := by ext x; rw [hmem, hκ]
  refine ⟨W, hp, ?_, fun x => (hmem x).symm⟩
  rw [heq]; exact hV

theorem exists_cpt {D : Datum H} {l : Level H} (Xo : Moduli D l) (c : Coeff l) {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β)
    (hβ : Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    {U : Set (Xo.XF c)} (hU : IsClopen U) (hUi : IsIrreducible U) : Nonempty (CptOver Y U) := by
  obtain ⟨u, hu⟩ := hUi.nonempty
  obtain ⟨U', Z, hu', hc, hi⟩ := GlobalTheory.T.exists_clopen_irreducible_cpt E H D l Xo c O β Y u hβ
  rw [eq_of_clopen_irred hU hUi hc hi hu hu']
  exact ⟨Z⟩

theorem local_gen (hA0 : FlatLineGenerator) (hA1 : FlatLineGeneratorComponent) (hC : FinConstAll) {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} (U : Set (Xo.XF c)) (τ : E →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (hpq : 1 ≤ D.p + D.q)
    (hτ : τ (H.rt : E) = H.rt0) (hty : IsTypeFn H D.p D.q ty) (hU : IsClopen U) (hUi : IsIrreducible U)
    (hP : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
      (Set.range y ⊆ U ↔ ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P))
    (W : ValuationSubring ℂ) [IsDiscreteValuationRing (c.V W)] (Y : Model Xo c (c.V W).subtype)
    (hSF : Y.SplitFibres) (hN3 : Y.N3) (p : Nat.Primes) (κ : c.F →+* ℂ_[p])
    (hκ : ∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ c.V W) :
    ∃ φ : FrameFn Xo c, IsFlatGen U τ φ FU i ∧ (∀ s : c.F →+* ℂ, ∃ t, HasInfNorm U τ φ s t) ∧
      ∃ t, HasFinNorm U τ φ p κ t := by
  obtain ⟨Z⟩ := exists_cpt Xo c Y (model_hyp (c.V W)) hU hUi
  have hG : Z.IsGeom := GlobalTheory.T.generic_fibre_uniformised_frame E H D l Xo c _ _ Y U Z g ty FU i hty (fun y hy hr => (hP y hy).1 hr)
  obtain ⟨φ, hl, hf, -⟩ := hA0 E H D l Xo c _ _ Y U Z τ (model_hyp (c.V W)) hpq hτ hG
  obtain ⟨hinf, hfg⟩ := hA1 E H D l Xo c _ _ Y U Z τ φ (model_hyp (c.V W)) hpq hτ hG hl hf
  refine ⟨φ, hfg g ty FU i hty (fun P y hPer hu hy => (hP y hy).2 ⟨P, hPer, hu⟩), fun s => ?_, ?_⟩
  · obtain ⟨t, ht, -⟩ := hinf s
    exact ⟨t, ht⟩
  · refine hC E H D l Xo c _ _ Y U Z τ p κ φ hτ Subtype.val_injective (fun x => (hκ x).trans ?_) hSF hN3 hG hf hl
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩

theorem hasFinNorm_of_eq {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {U : Set (Xo.XF c)}
    {τ : E →+* ℂ} {φ φ' : FrameFn Xo c} (hl : IsLineFn U τ φ) {a : c.F} (ha : a ≠ 0)
    (he : ∀ (F : Type) [Field F] (β : c.F →+* F) y v w, IsFramed U τ β y v w → φ' F y v w = β a * φ F y v w)
    {p : Nat.Primes} {κ : c.F →+* ℂ_[p]} {t : ℝ} (ht : HasFinNorm U τ φ' p κ t) :
    HasFinNorm U τ φ p κ (t - Real.log ‖κ a‖) := by
  intro V K _ _ _ _ _ _ j β y v w T tK m m' hj hjβ hfr hv hw
  have h1 := ht V K j β y v w T tK m m' hj hjβ hfr hv hw
  have hja : j (β a) = κ a := by rw [← hjβ]; rfl
  have h2 : ‖κ a‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero κ).mpr ha)
  have h3 : ‖j (φ K y v w)‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero j).mpr (hl.ne K β y v w hfr))
  rw [he K β y v w hfr, map_mul, hja, norm_mul, Real.log_mul h2 h3] at h1
  linarith

end GlobalTheory.CompanionTheory.Ar.Flat.TopA

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.Flat.TopA in

theorem thmFlatA_of_parts : PartI → FlatLineGenerator → FlatLineGeneratorComponent → FinConst → ThmFlatA := by
  intro hI hA0 hA1 _ E _ _ _ H D Xo l c _ U τ g ty FU i hpq hτ hg hty hU hUi hP
  have hC : FinConstAll := GlobalTheory.T.finite_constant_all_holds
  obtain ⟨-, hI'⟩ := hI
  obtain ⟨Ys, hYs, -⟩ := hI' E H D hpq Xo
  have key : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ φ : FrameFn (Xo l) c, IsFlatGen U τ φ FU i ∧
      (∀ s : c.F →+* ℂ, ∃ t, HasInfNorm U τ φ s t) ∧ ∃ t, HasFinNorm U τ φ p κ t := by
    intro p κ
    obtain ⟨W, hpW, hdvr, hκ⟩ := exists_place c p κ
    haveI := hdvr
    obtain ⟨-, hYi⟩ := hYs p W p.2 hpW
    obtain ⟨hSF, hN3, -⟩ := hYi ⟨l, c, hg p p.2⟩
    exact local_gen hA0 hA1 hC U τ FU i hpq hτ hty hU hUi hP W (Ys p W p.2 hpW ⟨l, c, hg p p.2⟩) hSF hN3 p κ hκ
  obtain ⟨κ₀⟩ := exists_padic_emb c.F ⟨2, Nat.prime_two⟩
  obtain ⟨φ, hφ, hinf, -⟩ := key _ κ₀
  have hfin : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ φ p κ t := by
    intro p κ
    obtain ⟨φ', hφ', -, t, ht⟩ := key p κ
    obtain ⟨a, ha, he⟩ := GlobalTheory.T.flat_gen_frame_complex_compat E H D l (Xo l) c U τ φ' φ g ty FU i hty hφ' hφ
      (fun y hy hr => (hP y hy).1 hr)
    exact ⟨_, hasFinNorm_of_eq hφ.line ha he ht⟩
  let N : LogNorms c.F := ⟨fun s => (hinf s).choose, fun p κ => (hfin p κ).choose -
    D.q * (logIdeal (κ.comp (tauIn c τ)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((H.d : ℕ) : ℂ_[p])‖)⟩
  have hN : HasNorms U τ φ N := ⟨fun s => (hinf s).choose_spec, fun p κ => by
    simp only [N, sub_add_cancel]
    exact (hfin p κ).choose_spec⟩
  refine ⟨φ, N, hφ, hN, ?_⟩
  obtain ⟨n, hn, hn0⟩ := GlobalTheory.T.finite_norm_zero_outside_denom E H D l (Xo l) c U τ φ hτ hU.isOpen hUi.nonempty hφ.line
  have hS := GlobalTheory.T.logIdeal_support_finite E (differentIdeal ℤ (𝓞 E)) differentIdeal_ne_bot
  refine (((finite_primes_dvd hn.ne').union (finite_primes_dvd H.d_prime.ne_zero)).union hS).subset ?_
  rintro p ⟨ι₀, hι⟩
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_not] at hcon
  obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
  obtain ⟨-, -, -, -, hd⟩ := GlobalTheory.T.padic_embedding_discrete_valuation_ring c.F p ι₀
  have hd' : ‖((H.d : ℕ) : ℂ_[p])‖ = 1 := by simpa using hd H.d h2
  have h0 := hn0 p ι₀ _ h1 (hN.2 p ι₀)
  rw [h3 (ι₀.comp (tauIn c τ)), hd', Real.log_one] at h0
  simp only [sub_zero, mul_zero, add_zero] at h0
  exact hι h0

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompFieldExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_field_extension : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [CharZero Ω] [Field Ω'] [CharZero Ω'] (i : Ω →+* Ω') (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) [∀ k, Fintype (J k)] [∀ k, Fintype (J' k)] (y : (Σ k, J k) → Ω) (y' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S y) (A' : HodgeCpt Y S y') (g : A'.X ⟶ A.X) (m : SABMap A'.t A.t g) (j₁ : A.Li →+ A'.Li) (y₀ : Sp Ω ⟶ Xo.XF c) (p : ℕ), p ∈ S → GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ g i → A'.f = g ≫ A.f → A'.R = A.R → IsExtOver i j₁ → (∀ v, (A'.M.pt (j₁ v)).left ≫ m.φ = spMap (dualMap i) ≫ (A.M.pt v).left) → A.ξ ≫ A.f = y₀ ≫ Y.j → (∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ A.R p)) → (HT.omP A p).IsVBOn {q | InFibre A.ξ p q} (Module.finrank Ω A.Li) ⊤ → (HT.omP A' p).IsVBOn {q | InFibre A'.ξ p q} (Module.finrank Ω' A'.Li) ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HFlag.omP_ext | exact GlobalTheory.CompanionTheory.Ar.HFlag.omP_ext | (intros; apply GlobalTheory.CompanionTheory.Ar.HFlag.omP_ext <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistLatticeCompatStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_twist_lattice_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∀ (t : SAB H A'.X) (tΩ : SAB H (Sp Ω)) (k : SABMap t A.t e.hom) (m : SABMap tΩ t A'.ξ)
      (mA' : SABMap (twistSAB tΩ g) A'.t A'.ξ) (u : SABMap tΩ Y.oF.t x)
      (u' : SABMap (twistSAB tΩ g) Y'.oF.t x') (M₁ : LieModel t.G A'.ξ A.Li) (φ : A.Li ≃ₗ[Ω] A'.Li),
      m.φ ≫ k.φ ≫ A.m.φ = u.φ ≫ Y.m.φ → mA'.φ ≫ A'.m.φ = u'.φ ≫ Y'.m.φ →
      u'.φ ≫ Y'.m0.toSABMap.φ = u.φ ≫ Y.m0.toSABMap.φ ≫ n.φ →
      (∀ v, (M₁.pt v).left ≫ k.φ = (A.M.pt v).left) → (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M₁.pt v).left ∧ w.left ≫ mA'.φ = (A'.M.pt (φ v)).left) → (∀ N, FullTorsion A.t.G A.ξ N → FullTorsion t.G A'.ξ N) → (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), regAt A'.ξ q = regAt A.ξ ⟨e.hom q.1, h⟩ ∧
        (M₁.lat q : Set A.Li) = A.M.lat ⟨e.hom q.1, h⟩ ∧
        ∀ N, (M₁.htOm t.PP.L N q : Set (Module.Dual Ω A.Li)) = A.M.htOm A.t.PP.L N ⟨e.hom q.1, h⟩) →
      (∀ a v, φ (A.ρ (g.s a) v) = A'.ρ a (φ v)) →
      ∀ s s', A'.emb s' = (A.emb s).comp g.s.toRingHom → ∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1) (v : A.Li),
        v ∈ A.V s ⟨e.hom q.1, h⟩ ↔ φ v ∈ A'.V s' q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CmpBund.bund | exact GlobalTheory.CompanionTheory.Ar.CmpBund.bund | (intros; apply GlobalTheory.CompanionTheory.Ar.CmpBund.bund <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptGlobalNefBoundStatement
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_global_nef_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (Yl : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W), (∀ p W hp hW i, (Yl p W hp hW i).SplitFibres ∧ (Yl p W hp hW i).N3) → ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), (∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W), (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Dominates Y (Yl p W hp hW ⟨l, c, hg p hp⟩) b) → 1 ≤ D.p → 1 ≤ D.q → ∀ (S : Finset ℕ) [Fintype (CMType H)] (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω), Fl.RootLines M.xdeg e → ∀ p : ℕ, p.Prime → 2 < p → p ∉ S → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ mu : GlobalTheory.CompanionTheory.Ar.Top.Wt (CMType H) (D.p + D.q), GlobalTheory.CompanionTheory.Ar.Top.Dominant mu → GlobalTheory.CompanionTheory.Ar.Top.NefThreshold D.p p mu → M.NefAt p mu 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.hodge_cpt_global_nefness | exact GlobalTheory.CompanionTheory.Ar.Conj.hodge_cpt_global_nefness | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.hodge_cpt_global_nefness <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptLabelBasesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_cpt_label_bases : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c) (b : ∀ s, Fin (labelRk D s) → 𝔐.Li) (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module 𝔐.Ω₀ Li₀) (M₀ : LieModel Y.t.G 𝔐.ξ₀ Li₀) (j : Li₀ →+ 𝔐.Li) (V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀) (d : ℕ), 𝔐.ξ ≫ 𝔐.f = y₀ ≫ Y.j → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ 𝔐.R p)) → (∀ s, Submodule.span Ω (Set.range (b s)) = 𝔐.Vgen s) → (∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap 𝔐.fn) ≫ (M₀.pt e).left) → (∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s) → (letI := 𝔐.fn.toAlgebra; IsGenericFlag (Ω' := Ω) j V₀ b d) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (𝔐' : HodgeCpt Y S y') (g : 𝔐'.X ⟶ 𝔐.X) (Fl : 𝔐'.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K' → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐'.ξ 𝔐.ξ g (RingHom.id Ω) ∧ 𝔐'.f = g ≫ 𝔐.f ∧ 𝔐'.R = 𝔐.R ∧ 𝔐'.cst = 𝔐.cst ∧ (∀ p ∈ S, HT.HTFree 𝔐' p) ∧ Fl.deg = d ∧ (∀ s i, (𝔐'.M.pt (Fl.b s i)).left ≫ 𝔐'.m.φ = spMap (dualMap (RingHom.id Ω)) ≫ (𝔐.M.pt (b s i)).left ≫ 𝔐.m.φ) ∧ Fl.RootLines xdeg e ∧ (∀ s, (𝔐'.dR s).IsFlagVBOn Set.univ (Fl.b s)) ∧ ∀ q ∈ genFib 𝔐.ξ, (∀ s, (𝔐.V s).IsFlagVBOn {q} (b s)) → IsoAt 𝔐'.ξ g (RingHom.id Ω) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HFlag.exists_flag_model | exact GlobalTheory.CompanionTheory.Ar.HFlag.exists_flag_model | (intros; apply GlobalTheory.CompanionTheory.Ar.HFlag.exists_flag_model <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptLieMetricBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SlopeUnif

theorem isGrpPullback_iso {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom] :
    IsGrpPullback A B (𝟙 S) e.hom.left := by
  refine ⟨?_, fun T x y x₀ y₀ hx hy => ?_⟩
  · haveI : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · have e₁ : (x * y) ≫ e.hom = (x ≫ e.hom) * (y ≫ e.hom) := by
      first | exact Hom.mul_comp _ _ _ | exact MonObj.mul_comp _ _ _ | exact CategoryTheory.Hom.mul_comp _ _ _
    have : (x * y).left ≫ e.hom.left = ((x ≫ e.hom) * (y ≫ e.hom)).left := by
      rw [← e₁]; rfl
    rw [this]
    exact mul_left_congr (Category.comp_id _) _ _ _ _ hx hy

theorem exists_compare {S S₁ : Scheme.{0}} {f : S₁ ⟶ S} {A A' : Over S₁} {C : Over S} [GrpObj A] [GrpObj A'] [GrpObj C]
    {a : A.left ⟶ C.left} {a' : A'.left ⟶ C.left} (hA : IsGrpPullback A C f a) (hA' : IsGrpPullback A' C f a') :
    ∃ w : A.left ⟶ A'.left, w ≫ a' = a ∧ w ≫ A'.hom = A.hom ∧ IsGrpPullback A A' (𝟙 S₁) w := by
  refine ⟨hA'.1.lift a A.hom hA.1.w, hA'.1.lift_fst _ _ _, hA'.1.lift_snd _ _ _, ?_⟩
  refine IsGrpPullback.cancel hA' ?_ ?_
  · rw [hA'.1.lift_fst, Category.id_comp]; exact hA
  · rw [hA'.1.lift_snd, Category.comp_id]

theorem slope_unif : N1ab → PartI → Geo.ResK.ResKStatement → GlobalTheory.Published.SemiAbelianHomExtension → SlopeBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (h : LieMetric 𝔐.M y), 1 ≤ D.p + D.q → ∃ C : ℝ, 0 ≤ C ∧ ∀ (L₀ : Type) [Field L₀] [NumberField L₀] (z₀ : Sp (𝓞 L₀) ⟶ 𝔐.X), ∃ (L : Type) (_ : Field L) (_ : NumberField L) (e : L₀ →+* L), ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G (spMap (RingOfIntegers.mapRingHom e) ≫ z₀) B.carrier), IsFibre (fun z v w c => c = h.ip z v w) _ B MB → B.slopeMax ≤ ((C * Real.log (2 + C + max (-B.normDegree ⊤) 0) + C : ℝ) : EReal) := by
  intro hN hP hR hH hS E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 h hpq
  obtain ⟨K₀, hK₀, hQ⟩ := GlobalTheory.T.lie_metric_height_bound hR E H D l Xo c Y S Ω K J y 𝔐 h hpq
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  obtain ⟨C₁, hC₁, hT⟩ := GlobalTheory.T.semiabelian_lie_metric_height hH 𝔐.X Ω K J y 𝔐.ξ inferInstance 𝔐.all 𝔐.tie 𝔐.t.G 𝔐.t.semi 𝔐.Li 𝔐.M h
  obtain ⟨C₀, hC₀, hSl⟩ := hS
  obtain ⟨Cc, hCc1, hCcK, hCc₁, hCc₀⟩ : ∃ Cc : ℝ, 1 ≤ Cc ∧ K₀ ≤ Cc ∧ C₁ ≤ Cc ∧ C₀ ≤ Cc :=
    ⟨max (max K₀ C₁) (max C₀ 1), by simp, by simp, by simp, by simp⟩
  obtain ⟨C', hC', hPB⟩ := GlobalTheory.T.hermitian_bundle_quotient_degree_bound (Module.finrank Ω 𝔐.Li) Cc hCc1
  refine ⟨C', hC', fun L₀ _ _ z₀ => ?_⟩
  obtain ⟨L₁, _, _, e₁, ⟨P₁⟩⟩ := GlobalTheory.T.exists_abelian_part_extension E H 𝔐.X 𝔐.t L₀ (spMap (algebraMap (𝓞 L₀) L₀) ≫ z₀)
  obtain ⟨σ₁⟩ : Nonempty (L₁ →+* ℂ) := inferInstance
  obtain ⟨P₁c, _, mBc, _, _⟩ := GlobalTheory.T.abelian_part_base_change E H 𝔐.X 𝔐.t L₁ ℂ _ P₁ σ₁
  have hpr : IsPrincipal P₁.tB := (GlobalTheory.T.isPrincipal_base_change_iff E H L₁ ℂ σ₁ P₁.tB P₁c.tB mBc).1 (hQ _ P₁c).1
  obtain ⟨L, _, _, e₂, t', tK, ⟨m'⟩, ⟨mP⟩⟩ := GlobalTheory.T.lie_signature_number_field hN hP E H L₁ P₁.tB hpr
    (GlobalTheory.T.abelian_part_lie_signature E H D l Xo c Y S Ω K J y 𝔐 L₁ _ P₁)
  have hprK : IsPrincipal tK := (GlobalTheory.T.isPrincipal_base_change_iff E H L₁ L e₂ P₁.tB tK mP).2 hpr
  refine ⟨L, inferInstance, inferInstance, e₂.comp e₁, fun B MB hB => ?_⟩
  have hz : spMap (algebraMap (𝓞 L) L) ≫ (spMap (RingOfIntegers.mapRingHom (e₂.comp e₁)) ≫ z₀) =
      spMap e₂ ≫ (spMap e₁ ≫ spMap (algebraMap (𝓞 L₀) L₀) ≫ z₀) := by
    have e : spMap (algebraMap (𝓞 L) L) ≫ spMap (RingOfIntegers.mapRingHom (e₂.comp e₁)) =
        spMap e₂ ≫ spMap e₁ ≫ spMap (algebraMap (𝓞 L₀) L₀) := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
    rw [← Category.assoc, e]
    simp only [Category.assoc]
  obtain ⟨B', MB', hB'⟩ := GlobalTheory.T.principal_hermitian_fibre E H L t' tK m' hprK
  have hslope := hSl E H L t' tK m' hprK B' MB' hB'
  obtain ⟨P₂, mK2, mB2, c1, c2⟩ := GlobalTheory.T.abelian_part_base_change E H 𝔐.X 𝔐.t L₁ L _ P₁ e₂
  obtain ⟨w, hw, hw', hwp⟩ := exists_compare mB2.cart mP.cart
  letI := P₂.τ.addCommGroup
  letI := P₂.τ.grpB
  haveI := P₂.e_hom
  have hφ' : IsGrpPullback P₂.τ.B t'.G (spMap (algebraMap (𝓞 L) L)) (P₂.e.hom.left ≫ w ≫ m'.φ) := by
    have := (isGrpPullback_iso P₂.e).comp (hwp.comp m'.cart)
    simpa using this
  obtain ⟨MT, hMT⟩ := GlobalTheory.T.exists_cocharacter_lie_model (Sp L) P₂.τ.X L (𝟙 _)
  have hcart : IsGrpPullback P₂.tK.G 𝔐.t.G (spMap (algebraMap (𝓞 L) L) ≫ (spMap (RingOfIntegers.mapRingHom (e₂.comp e₁)) ≫ z₀)) P₂.m.φ := by
    rw [hz]; exact P₂.m.cart
  obtain ⟨r, bs, hbs⟩ := hT L _ P₂.tK.G P₂.m.φ P₂.τ hcart
  obtain ⟨ε, f, hε, hf, hli, hker, hsur⟩ := GlobalTheory.T.semi_abelian_pullback_torus_extension 𝔐.X 𝔐.t.G 𝔐.t.semi L _ P₂.tK.G P₂.m.φ P₂.τ t'.G _ t'.semi hcart hφ'
    MT hMT B.carrier B'.carrier MB MB' r bs
  have hbd := hbs MT hMT B MB hB ε hε
  have hnb := GlobalTheory.T.abelian_part_maps_compatible_right E H 𝔐.X 𝔐.t L₁ L e₂ _ _ hz P₁ P₂ mK2 mB2 c1 c2 t' tK m' mP w hw hw' Ω 𝔐.ξ 𝔐.Li 𝔐.M K J y h K₀
    (fun zc P v v₀ c => (hQ zc P).2 v v₀ c) B B' MB MB' hB hB' f hf
  haveI : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  have hrk := GlobalTheory.T.lie_model_rank_eq_generic 𝔐.X Ω 𝔐.ξ 𝔐.all 𝔐.t.G 𝔐.Li 𝔐.M L _ B.carrier MB
  have hC₁0 : (0 : ℝ) < C₁ := by linarith
  have hCc0 : (0 : ℝ) < Cc := by linarith
  refine hPB L B B' r ε f hrk hli hker hsur ?_ ?_ ?_
  · intro σ u
    have hs : 0 ≤ ∑ a, ‖u a‖ ^ 2 := Finset.sum_nonneg fun a _ => by positivity
    obtain ⟨h₁, h₂⟩ := hbd σ u
    refine ⟨le_trans (mul_le_mul_of_nonneg_right ?_ hs) h₁, h₂.trans (mul_le_mul_of_nonneg_right hCc₁ hs)⟩
    exact inv_anti₀ hC₁0 hCc₁
  · intro σ x
    have h0 : 0 ≤ sqAt B σ x := by
      have := (B.metric.form σ).re_inner_nonneg x
      simpa [sqAt] using this
    exact (hnb σ x).trans (mul_le_mul_of_nonneg_right hCcK h0)
  · refine hslope.trans (EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_right hCc₀ (Real.log_nonneg ?_)))
    have : (0 : ℝ) ≤ max (-B'.normDegree ⊤) 0 := le_max_right _ _
    have h' : (0 : ℝ) ≤ Module.finrank (𝓞 L) B'.carrier := Nat.cast_nonneg _
    linarith

end GlobalTheory.CompanionTheory.Ar.SlopeUnif
end
end

