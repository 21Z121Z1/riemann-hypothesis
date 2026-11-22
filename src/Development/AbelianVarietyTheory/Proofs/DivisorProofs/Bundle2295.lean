import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2246
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2247
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormUniformizerConstant
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.UnifNorm

theorem norm_le_one_of_mem (p : ℕ) [Fact p.Prime] (x : 𝓞_ℂ_[p]) : ‖(x : ℂ_[p])‖ ≤ 1 := by
  have hv : ((Valued.v (x : ℂ_[p]) : NNReal) : ℝ) = ‖(x : ℂ_[p])‖ := by
    rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, PadicComplex.RankOne.hom_eq_embedding,
      Valuation.embedding_restrict]
  rw [← hv]
  have : Valued.v (x : ℂ_[p]) ≤ 1 := x.2
  exact_mod_cast this

theorem norm_eq_one_of_isUnit (p : ℕ) [Fact p.Prime] {x : 𝓞_ℂ_[p]} (hx : IsUnit x) :
    ‖(x : ℂ_[p])‖ = 1 := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h1 : (x : ℂ_[p]) * (y : ℂ_[p]) = 1 := by
    have := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) hy
    simpa using this
  have h3 := congrArg norm h1
  rw [norm_mul, norm_one] at h3
  have ha := norm_le_one_of_mem p x
  have hb := norm_le_one_of_mem p y
  nlinarith [norm_nonneg (x : ℂ_[p]), norm_nonneg (y : ℂ_[p])]

theorem norm_pow_eq (p : ℕ) [Fact p.Prime] {V : Type} [CommRing V] {ϖ : V} {n : ℕ}
    (hn : Associated (p : V) (ϖ ^ n)) (φ : V →+* 𝓞_ℂ_[p]) :
    ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ ^ n = ‖(p : ℂ_[p])‖ := by
  obtain ⟨u, hu⟩ := hn
  have h1 := congrArg (fun z : V => ‖((φ z : 𝓞_ℂ_[p]) : ℂ_[p])‖) hu
  have hu1 : ‖((φ (u : V) : 𝓞_ℂ_[p]) : ℂ_[p])‖ = 1 :=
    norm_eq_one_of_isUnit p ((u.isUnit).map φ)
  simp only [map_mul, map_pow, map_natCast] at h1
  simp [norm_mul, norm_pow, hu1] at h1
  exact h1.symm

end GlobalTheory.UnifNorm

theorem GlobalTheory.unif_norm_indep : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ ϖ : V, Irreducible ϖ → ∃ r : ℝ, ∀ φ : V →+* 𝓞_ℂ_[p], ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ = r := by
  intro F _ _ V _ p _ hp ϖ hϖ
  classical
  have hp0 : (p : V) ≠ 0 := by
    intro h
    have h' := congrArg (fun z : V => (z : F)) h
    simp only [ZeroMemClass.coe_zero] at h'
    push_cast at h'
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h'
  have hpnu : ¬ IsUnit (p : V) := by
    intro hu
    rw [ValuationSubring.mem_nonunits_iff] at hp
    rw [ValuationSubring.valuation_eq_one_iff] at hu
    have : V.valuation ((p : V) : F) < 1 := by simpa using hp
    exact (ne_of_lt this) hu
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hpnu (associated_one_iff_isUnit.mp hn)
  by_cases hne : Nonempty (V →+* 𝓞_ℂ_[p])
  · obtain ⟨φ₀⟩ := hne
    refine ⟨‖((φ₀ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖, fun φ => ?_⟩
    have e1 := GlobalTheory.UnifNorm.norm_pow_eq p hn φ
    have e0 := GlobalTheory.UnifNorm.norm_pow_eq p hn φ₀
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hn0).mp (e1.trans e0.symm)
  · exact ⟨0, fun φ => (hne ⟨φ⟩).elim⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O

namespace GlobalTheory.CoverNorm

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def Norms (V : Cover Y) (L : HermLB V.p) (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ)
    (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) : Prop :=
  ∃ r : (L.B.pull V.j).ι → V.G.functionFieldˣ, IsRatSec (L.B.pull V.j) r ∧
    (∀ i, ∀ x ∈ (L.B.pull V.j).U i, UnitAt x (V.φ (f (V.π x)) * r i)) ∧
    (∀ (σ : F →+* ℂ) (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ) (y' : CxPts V.p (σ.comp (algebraMap (𝓞 F) F)))
      (i : (L.B.pull V.j).ι), y.1 = z.1 ≫ V.π → y'.1 = z.1 ≫ V.j → under z ∈ (L.B.pull V.j).U i →
      a σ y = Real.log ‖ratVal (V.φ (f (under y)) * (r i : V.G.functionField)) z‖ - (L.φ _).φ (i PUnit.unit) y' / 2) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X)
      (i : (L.B.pull V.j).ι), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ L.B.U (i PUnit.unit) →
      l v e y = Real.log (e.w (valAt z (V.φ (f (below y.1)) * (r i : V.G.functionField))))

theorem norms_of_induces {C : CxSt F} {V : Cover Y} {A : Adl C Y} {L : HermLB V.p} {k : ℕ} (h : V.Induces A L k) :
    Norms V L (fun x => genAt A.D x ^ k)
      (fun σ y => k * lnAdl A σ y)
      fun v e y => k * A.lg v e y := by
  obtain ⟨r, hr, hu, hc, hf⟩ := h
  refine ⟨r, hr, fun i x hx => by rw [map_pow]; exact hu i x hx, fun σ z y y' i e₁ e₂ hi => ?_,
    fun v e y z yt i e₁ e₂ hi => by rw [map_pow]; exact hf v e y z yt i e₁ e₂ hi⟩
  have H := hc σ z y y' i e₁ e₂ hi
  have hπ : V.π (under z) = under y := by
    show _ = y.1 _
    rw [e₁]
    rfl
  have hU := hu i _ hi
  rw [hπ] at hU
  have h0 := ratVal_ne_zero (y := z) hU
  have H' := congrArg Real.log H
  rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 h0)) (Real.exp_ne_zero _), Real.log_exp, Real.log_pow,
    Real.log_pow] at H'
  beta_reduce
  rw [map_pow]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, zero_mul, genAt] at H' ⊢
    simp only [Nat.cast_ofNat] at H'
    linarith
  have hp : C.pn Y σ A.D (A.m σ) (C.cx Y σ (genAt A.D (under y))) y ≠ 0 := fun h => by
    rw [h, mul_zero, zero_pow hk.ne'] at H
    exact (mul_pos (pow_pos (norm_pos_iff.2 h0) 2) (Real.exp_pos _)).ne H
  rw [Real.log_mul (Real.exp_ne_zero _) hp, Real.log_exp] at H'
  simp only [lnAdl, lnN, genAt] at H' ⊢
  simp only [Nat.cast_ofNat] at H'
  linarith

theorem Norms.congr {V : Cover Y} {L : HermLB V.p} {f f' : Y.X → Y.Fn} {a a' : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l l' : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : Norms V L f a l) (hf : ∀ x, f x = f' x)
    (ha : ∀ σ y, a σ y = a' σ y) (hl : ∀ v e y, l v e y = l' v e y) : Norms V L f' a' l' := by
  obtain rfl : f = f' := funext hf
  obtain rfl : a = a' := funext₂ ha
  obtain rfl : l = l' := funext₃ hl
  exact h

end GlobalTheory.CoverNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaStdAddNsmul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegCover

theorem unitOn_pow' {R : Type} [CommRing R] (u : Rˣ) (m : ℕ) : unitOn (u ^ m) = unitOn u ^ m := by
  unfold unitOn; exact map_pow _ u m

theorem unitOn_one' {R : Type} [CommRing R] : unitOn (1 : Rˣ) = 1 := by
  unfold unitOn; exact map_one _

theorem weilIs_congr_base {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {m : ℤ} {k : Type} [Field k]
    {y y' : Sp k ⟶ S} (e : y = y') {x₁ x₂ : Over.mk y ⟶ A} {x₁' x₂' : Over.mk y' ⟶ A}
    (h₁ : x₁.left = x₁'.left) (h₂ : x₂.left = x₂'.left) {c : Γ(Sp k, ⊤)ˣ} (H : Out.WeilIs A L m x₁ x₂ c) :
    Out.WeilIs A L m x₁' x₂' c := by
  subst e
  rwa [← Over.OverMorphism.ext h₁, ← Over.OverMorphism.ext h₂]

theorem weilTransport : ∀ (h N m : ℕ) (B B₁ : Type) [CommRing B] [CommRing B₁] (ζ : B) (ζ₁ : B₁) (S T : Scheme.{0}) (s : S ⟶ Sp B) (sT : T ⟶ Sp B₁) (c : SiegPre h m ζ s) (C' : SiegPre h N ζ₁ sT) (t : T ⟶ S) (φ : C'.A.left ⟶ c.A.left), IsGrpPullback C'.A c.A t φ → (∃ φ₂ : (G2 C'.A).left ⟶ (G2 c.A).left, IsSquare φ φ₂ ∧ LBIso C'.P (c.P.pull φ₂)) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T) (β : B₁ →+* k) (z : kˣ) (y : Sp k ⟶ S) (g g' : Over.mk y ⟶ c.A) (a a' : Fin h ⊕ Fin h → ℤ), x ≫ sT = spMap β → (z : k) = β ζ₁ → y = x ≫ t → g.left = x ≫ (C'.lev a).left ≫ φ → g'.left = x ≫ (C'.lev a').left ≫ φ → Out.WeilIs c.A c.diag N g g' (unitOn (z ^ (2 * omegaStd a a'))) := by
  intro h N m B B₁ _ _ ζ ζ₁ S T s sT c C' t φ pb hφ k _ _ x β z y g g' a a' hx hz hy hg hg'
  obtain ⟨φ₂, sq, iso⟩ := hφ
  subst hy
  obtain ⟨-, -, g₃⟩ := C'.geom k x β z hx hz
  exact (weilIs_grpPullback_of_comm S T c.A C'.A t φ _ _ (pull_isLB c.isLB _) (pull_isLB C'.isLB _) pb
    (SiegelPull.diag_iso sq iso) (Over.mk x) N _ _ g g' _
    (by rw [hg, Over.comp_left, Over.toUnit_left, Category.assoc]; rfl)
    (by rw [hg', Over.comp_left, Over.toUnit_left, Category.assoc]; rfl)).1 (g₃ a a')

theorem omegaStd_add_nsmul {h : ℕ} (N : ℕ) (a a' c₁ c₂ : Fin h ⊕ Fin h → ℤ) :
    omegaStd (a + N • c₁) (a' + N • c₂) =
      omegaStd a a' + N * (omegaStd c₁ a' + omegaStd a c₂ + N * omegaStd c₁ c₂) := by
  simp only [omegaStd, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, mul_add,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.SiegCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeIntersectionNumberSubvarietyThroughPositiveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_le_intersectionNumber_subvariety_through_positive : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N₁ N₂ : LB X) (hN : N.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a : ℕ) (x : X), IsNef k N → 0 < a → a • cls N hN = cls N₁ h₁ + cls N₂ h₂ → AmpleAt N₁ x → IsNef k N₂ → ∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e → topologicalKrullDim (Z : Set X) = e → 1 ≤ interNumRed k Z (fun _ : Fin e => N) := by
  first | exact @GlobalTheory.PosThrough.one_le_interNumRed | exact GlobalTheory.PosThrough.one_le_interNumRed | (intros; apply GlobalTheory.PosThrough.one_le_interNumRed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapRowAllTuplesOfCoreClauses
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapCore

theorem oneMapRowR_of_core : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ i, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → OneMapRowR T R κ v₀ O ph i := by
  intro hCI D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hR hoff hused hfw hio i hpins htie hspan
  have hin : TieIn T R κ v₀ := GlobalTheory.T.cuspFormsAgreement_contains_formIndependentFields D G Pl0 T0 A T R κ v₀ hfw
  refine GlobalTheory.T.oneMapRow_of_baseTuple_identityRow_span D G Pl0 T0 A T R κ v₀ O ph i hR.lev hR.grp.chiW hR.fam hR.models hpins htie
    (GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal hCI D G Pl0 T0 A T R F κ v₀ hR hin hio O i hpins) (fun hG => ?_)
    (GlobalTheory.T.thetaOneMap_identity_every_normalised_family hCI D G Pl0 T0 A T R F κ v₀ hR hin hio i) hspan
  obtain ⟨O', h1, h2, -⟩ := GlobalTheory.T.exists_normalisedData_allTuples_of_baseTuple D G Pl0 T0 A T R κ v₀ O hR.lev hR.grp.chiW hR.fam hR.models hR.thP.vP hoff hused
    hfw i hpins hG
  exact ⟨O', h1, h2⟩

end GlobalTheory.OneMapCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenImmersionRingFactor
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
namespace GlobalTheory.FlatModel

theorem chart_sections_factor : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) [IsOpenImmersion ξ],
    ∃ e : R →+* Γ(X, ξ.opensRange), ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (V : Y.Opens) (hV : IsAffineOpen V)
      (hVU : V ≤ f ⁻¹ᵁ ξ.opensRange), hV.fromSpec ≫ f = spMap ((f.appLE ξ.opensRange V hVU).hom.comp e) ≫ ξ := by
  intro X R _ ξ _
  have hU : IsAffineOpen ξ.opensRange := isAffineOpen_opensRange ξ
  have hr : Set.range hU.fromSpec.base ⊆ Set.range ξ.base := by
    rw [hU.range_fromSpec]; simp
  refine ⟨(Spec.preimage (IsOpenImmersion.lift ξ hU.fromSpec hr)).hom, ?_⟩
  intro Y f V hV hVU
  rw [← hU.SpecMap_appLE_fromSpec f hV hVU]
  conv_lhs => rw [← IsOpenImmersion.lift_fac ξ hU.fromSpec hr]
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom, Spec.map_preimage]

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFracFunctionFieldMapOfEssentiallyEtale
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open IsLocalRing

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EtaleKlt

theorem ord_functionFieldMap_of_formallyEtale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (E : DivOver p) (E' : DivOver (f ≫ p)) (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring), (∀ x, functionFieldMap f x ∈ E'.ring → x ∈ E.ring) → ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale → ((functionFieldMap f).restrict E.ring E'.ring h).EssFiniteType → ∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := by
  intro M W _ _ p f _ E E' h htr het hft g
  set φ := functionFieldMap f
  set ρ := φ.restrict E.ring E'.ring h
  letI := ρ.toAlgebra
  haveI : Algebra.FormallyEtale E.ring E'.ring := het
  haveI : Algebra.EssFiniteType E.ring E'.ring := hft
  haveI : IsLocalHom (algebraMap E.ring E'.ring) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    have e : φ (x : W.functionField) * (y : M.functionField) = 1 := congrArg Subtype.val hy
    have hx0 : (x : W.functionField) ≠ 0 := by
      rintro h0
      rw [h0, map_zero, zero_mul] at e
      exact zero_ne_one e
    have hinv : φ ((x : W.functionField)⁻¹) = y := by
      rw [map_inv₀]
      exact inv_eq_of_mul_eq_one_right e
    have hmem : (x : W.functionField)⁻¹ ∈ E.ring := htr _ (hinv ▸ y.2)
    exact IsUnit.of_mul_eq_one (b := (⟨_, hmem⟩ : E.ring)) (Subtype.ext (mul_inv_cancel₀ hx0))
  have hm := Algebra.FormallyUnramified.map_maximalIdeal (R := E.ring) (S := E'.ring)
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  have ht' : Irreducible (ρ t) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hm, (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht, Ideal.map_span,
      Set.image_singleton]
    rfl
  obtain ⟨m, u, e⟩ := exists_eq_unit_mul_zpow (F := W.functionField) ht g.ne_zero
  have h1 := ordTop_vw_unit_mul_zpow (F := W.functionField) ht u m
  have h2 := ordTop_vw_unit_mul_zpow (F := M.functionField) ht' (Units.map ρ.toMonoidHom u) m
  rw [← e, ordTop_vw_of_ne_zero _ g.ne_zero, WithTop.coe_inj] at h1
  have e2 : ((Units.map φ.toMonoidHom g : M.functionFieldˣ) : M.functionField) =
      algebraMap E'.ring M.functionField (Units.map ρ.toMonoidHom u) *
        algebraMap E'.ring M.functionField (ρ t) ^ m := by
    rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, e, map_mul, map_zpow₀]
    rfl
  rw [← e2, ordTop_vw_of_ne_zero _ (Units.ne_zero _), WithTop.coe_inj] at h2
  exact h2.trans h1.symm

end GlobalTheory.EtaleKlt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverInclusionBaseChangeModel
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem eigChar_model_eq_frPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (hle : c.F ≤ c'.F), OverIncl r hle → ∀ (σ : E →+* ℂ) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β → ∀ (K : Type) [CommRing K] (φ : A →+* K) (io : c.F →+* K) (y : letI := io.toAlgebra; FrPt Xo c K) (yy : Sp K ⟶ Xo'.XF c'), yy ≫ Y.j = spMap φ ≫ ξ → (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y = yy ≫ r) → ∀ a : 𝓞 E, φ (β (embV c' W σ a)) = io (embK c σ a) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r hle hOI σ A _ ξ β hξ K _ φ io y yy hyy hy a
  have e : ∀ {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T),
      spMap (g.comp f) = spMap g ≫ spMap f := by
    intro R S T _ _ _ f g
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]; rfl
  have inj : ∀ {R S : Type} [CommRing R] [CommRing S] (f g : R →+* S), spMap f = spMap g → f = g := by
    intro R S _ _ f g h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  have h1 : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (c'.V W).subtype := by
    show (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over]
  obtain ⟨ι', hι⟩ : ∃ ι' : c'.F →+* K, spMap ι' = yy ≫ pullback.snd _ _ :=
    ⟨(Spec.preimage (yy ≫ pullback.snd _ _)).hom, Spec.map_preimage _⟩
  have h2 : φ.comp β = ι'.comp (c'.V W).subtype := by
    apply inj
    rw [e, e, ← hξ, ← Category.assoc, ← hyy, Category.assoc, h1, ← Category.assoc, hι]
  have h3 : io = ι'.comp (IntermediateField.inclusion hle).toRingHom := by
    apply inj
    have h0 : (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y) ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
    rw [e, hι, ← h0, hy, Category.assoc, hOI, Category.assoc]
  have h4 : (IntermediateField.inclusion hle) (embK c σ a) = embK c' σ a := Subtype.ext rfl
  calc φ (β (embV c' W σ a)) = ι' ((c'.V W).subtype (embV c' W σ a)) := RingHom.congr_fun h2 _
    _ = ι' (embK c' σ a) := rfl
    _ = io (embK c σ a) := by rw [h3, RingHom.comp_apply]; exact congrArg ι' h4.symm

end GlobalTheory.FlatModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverTensorIsPullbackOfIsPullbackSquares
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem over_tensor_isPullback_of_isPullback {S S' : Scheme.{0}} (s : S' ⟶ S) (A B : Over S')
    (Y Z : Over S) (j : A.left ⟶ Y.left) (j' : B.left ⟶ Z.left)
    (h₁ : IsPullback j A.hom Y.hom s) (h₂ : IsPullback j' B.hom Z.hom s) :
    ∃ k : (A ⊗ B).left ⟶ (Y ⊗ Z).left, k ≫ (fst Y Z).left = (fst A B).left ≫ j ∧
      k ≫ (snd Y Z).left = (snd A B).left ≫ j' ∧ IsPullback k (A ⊗ B).hom (Y ⊗ Z).hom s := by
  let k : pullback A.hom B.hom ⟶ pullback Y.hom Z.hom :=
    pullback.map A.hom B.hom Y.hom Z.hom j j' s h₁.w.symm h₂.w.symm
  have kf : k ≫ pullback.fst Y.hom Z.hom = pullback.fst A.hom B.hom ≫ j := pullback.lift_fst _ _ _
  have ks : k ≫ pullback.snd Y.hom Z.hom = pullback.snd A.hom B.hom ≫ j' :=
    pullback.lift_snd _ _ _
  refine ⟨k, kf, ks, ?_⟩
  change IsPullback k (pullback.fst A.hom B.hom ≫ A.hom) (pullback.fst Y.hom Z.hom ≫ Y.hom) s
  have w : k ≫ pullback.fst Y.hom Z.hom ≫ Y.hom = (pullback.fst A.hom B.hom ≫ A.hom) ≫ s := by
    rw [← Category.assoc, kf, Category.assoc, h₁.w, Category.assoc]
  refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk w ?lift ?fl ?fr ?uniq)
  case lift =>
    intro c
    have e₁ : (c.fst ≫ pullback.fst Y.hom Z.hom) ≫ Y.hom = c.snd ≫ s := by
      simpa using c.condition
    have e₂ : (c.fst ≫ pullback.snd Y.hom Z.hom) ≫ Z.hom = c.snd ≫ s := by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc]; exact e₁
    exact pullback.lift (h₁.lift _ _ e₁) (h₂.lift _ _ e₂) (by simp)
  case fl =>
    intro c
    apply pullback.hom_ext
    · rw [Category.assoc, kf, pullback.lift_fst_assoc, h₁.lift_fst]
    · rw [Category.assoc, ks, pullback.lift_snd_assoc, h₂.lift_fst]
  case fr =>
    intro c
    rw [pullback.lift_fst_assoc, h₁.lift_snd]
  case uniq =>
    intro c m hm hm'
    have hA : m ≫ pullback.fst A.hom B.hom ≫ A.hom = c.snd := hm'
    have hB : m ≫ pullback.snd A.hom B.hom ≫ B.hom = c.snd := by
      rw [← pullback.condition]; exact hA
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      apply h₁.hom_ext
      · rw [h₁.lift_fst, Category.assoc, ← kf, ← Category.assoc, hm]
      · rw [h₁.lift_snd, Category.assoc, hA]
    · rw [pullback.lift_snd]
      apply h₂.hom_ext
      · rw [h₂.lift_fst, Category.assoc, ← ks, ← Category.assoc, hm]
      · rw [h₂.lift_snd, Category.assoc, hB]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicNormLeOneIffValuationStatement
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_norm_le_one_iff_valuation : ∀ {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : K →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (k : T.Fr →+* ℂ_[p]) (kO : T.V →+* 𝓞_ℂ_[p]), (∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a)) → ∀ a : K, ‖k (io a)‖ ≤ 1 ↔ la.valuation K a ≤ 1 := by
  first | exact @GlobalTheory.PlaceNorm.norm_le_one_iff_valuation_le_one | exact GlobalTheory.PlaceNorm.norm_le_one_iff_valuation_le_one | (intros; apply GlobalTheory.PlaceNorm.norm_le_one_iff_valuation_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPairingApproximationStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_pairing_approximation : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (n N g : ℕ) {J : Type}
    (ta : Fin N → P.T) (x : Fin g → LieG P.Gt) (h : Fin N → Fin g → 𝓞_ℂ_[p]) (Tc : J → Fin N → 𝓞_ℂ_[p])
    (U : Fin g → 𝓞_ℂ_[p]), (∀ m b, h m b - (P.al₀ (ta m)).1 (x b) ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}) → ∀ i : J,
    ‖(((∑ b, (∑ a, Tc i a * h a b) * U b : 𝓞_ℂ_[p]) : ℂ_[p]) -
      P.pairV (∑ b, (U b : ℂ_[p]) • P.bLie (x b)) (∑ m, (Tc i m : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))‖ ≤ (p : ℝ)⁻¹ ^ n := by
  first | exact @GlobalTheory.FlatModel.HTCong.pair_comb_congr | exact GlobalTheory.FlatModel.HTCong.pair_comb_congr | (intros; apply GlobalTheory.FlatModel.HTCong.pair_comb_congr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PackingStatementHoldsStatement
section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.packing_statement_holds : PackSt := by
  first | exact @GlobalTheory.FlatModel.packSt | exact GlobalTheory.FlatModel.packSt | (intros; apply GlobalTheory.FlatModel.packSt <;> assumption)
end

