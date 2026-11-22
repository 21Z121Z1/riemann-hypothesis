import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3314
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2342
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3273
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3300
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3253
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3302
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3311

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomOver
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et.CovChar

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

def constMor (Y : Scheme.{0}) (a : R) : (freeOn R).obj Y ⟶ coef R :=
  (sectionOf R Y (coef R)).symm
    ((toSheafify Scheme.proetaleTopology.{0} (coefPre R)).app (op Y) (ULift.up (ContinuousMap.const Y a)))

variable {R} {X Y : Scheme.{0}} (f : Y ⟶ X)

abbrev kerSc : ShortComplex (Shv R) :=
  ShortComplex.mk (kernel.ι ((freeOn R).map f)) ((freeOn R).map f) (kernel.condition _)

def CharRel {G : Type} (t : G → (Y ⟶ Y)) (x : H R 1 X) (c : G → R) : Prop :=
  ∃ (hS : (kerSc (R := R) f).ShortExact) (h : kernel ((freeOn R).map f) ⟶ coef R),
    (x : HS R (coef R) 1 X) = hS.extClass.comp (Abelian.Ext.mk₀ h) (add_zero 1) ∧
    ∀ (g : G) (k : (freeOn R).obj Y ⟶ kernel ((freeOn R).map f)),
      k ≫ kernel.ι _ = (freeOn R).map (t g) - 𝟙 _ → k ≫ h = constMor R Y (c g)

end GlobalTheory.Et.CovChar

namespace GlobalTheory.AV.AbVar

open ReciprocityTheory.ChartRestriction.G.Geo.Tor MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {K : Type} [Field K]

abbrev torsPts (A : AbVar K) (n : ℕ) : Subgroup A.Pt := (powMonoidHom n).ker

abbrev geomX (A : AbVar K) : Scheme.{0} := GlobalTheory.Et.geom (AlgebraicClosure K) A.X.hom

def mulGeom (A : AbVar K) (n : ℕ) : geomX A ⟶ geomX A :=
  GlobalTheory.Et.geomMap (AlgebraicClosure K) A.X.hom (n • 𝟙 A : A ⟶ A).hom.left (Over.w _)

abbrev geomOver (A : AbVar K) : Over (Sp K) :=
  Over.mk (pullback.fst A.X.hom (spMap (algebraMap K (AlgebraicClosure K))) ≫ A.X.hom)

def transl (A : AbVar K) (a : A.Pt) : geomX A ⟶ geomX A :=
  pullback.lift
    ((lift (Over.homMk (pullback.fst _ _) : geomOver A ⟶ A.X)
      (Over.homMk (pullback.snd _ _ ≫ a.left) (by
        rw [Category.assoc, Over.w a]; exact pullback.condition.symm) : geomOver A ⟶ A.X) ≫ μ[A.X]).left)
    (pullback.snd _ _) (by
      rw [Over.w]; exact pullback.condition)

def levT {l : ℕ} (A : AbVar K) (t : Tl l A) (m : ℕ) : torsPts A (l ^ m) :=
  ⟨t.lev m, (MonoidHom.mem_ker).2 (by rw [powMonoidHom_apply]; exact GlobalTheory.HTLat.Tate.lev_pow t m)⟩

end GlobalTheory.AV.AbVar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDeterminantWeightShiftAsymptoticLeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramDeterminant_weightShift_asymptotic_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ (u : SmFn p) (ε : ℝ), 0 < ε → ∀ᶠ m : ℕ in atTop, Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re ≤ (chInt P.L D u.u / D.factorial + ε) * (m : ℝ) ^ (D + 1) := by
  first | exact @GlobalTheory.HSAmp.gram_det_up_le | exact GlobalTheory.HSAmp.gram_det_up_le | (intros; apply GlobalTheory.HSAmp.gram_det_up_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasKernelOrderPPowerDegreeCompLeAdd
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory

namespace PDiv

theorem finrank_quot_kerIdeal_comp_le {k A B C : Type} [Field k] [CommRing A] [CommRing B]
    [CommRing C] [HopfAlgebra k A] [HopfAlgebra k B] [HopfAlgebra k C] [Module.Finite k A]
    [Module.Finite k B] (ψ : B →ₐc[k] A) (φ : C →ₐc[k] B) :
    Module.finrank k (A ⧸ kerIdeal (ψ.comp φ)) ≤
      Module.finrank k (A ⧸ kerIdeal ψ) * Module.finrank k (B ⧸ kerIdeal φ) := by
  haveI := isHopfIdeal_kerIdeal_of_bialgHom k A C (ψ.comp φ)
  haveI := isHopfIdeal_kerIdeal_of_bialgHom k B C φ
  let πA : A →ₐc[k] A ⧸ kerIdeal (ψ.comp φ) := Bialgebra.Quotient.mkBialgHom (kerIdeal (ψ.comp φ))
  let πB : B →ₐc[k] B ⧸ kerIdeal φ := Bialgebra.Quotient.mkBialgHom (kerIdeal φ)
  have hπA : Function.Surjective πA := Ideal.Quotient.mk_surjective
  have hπB : Function.Surjective πB := Ideal.Quotient.mk_surjective
  have hA : ∀ c, πA (ψ (φ c)) = algebraMap k _ (counit c) :=
    (kerIdeal_le_ker_iff (ψ.comp φ) (πA : A →ₐ[k] A ⧸ kerIdeal (ψ.comp φ))).1
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h1 : kerIdeal φ ≤ RingHom.ker (πA.comp ψ : B →ₐ[k] A ⧸ kerIdeal (ψ.comp φ)) :=
    (kerIdeal_le_ker_iff φ _).2 fun c => hA c
  let m' : (B ⧸ kerIdeal φ) →ₐc[k] A ⧸ kerIdeal (ψ.comp φ) :=
    liftSurj πB hπB (πA.comp ψ) fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)
  have hm' : ∀ b, m' (πB b) = πA (ψ b) := fun b =>
    liftSurj_apply πB hπB (πA.comp ψ) (fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)) b
  let q : A →ₐ[k] (A ⧸ kerIdeal (ψ.comp φ)) ⧸ kerIdeal m' :=
    (Ideal.Quotient.mkₐ k (kerIdeal m')).comp (πA : A →ₐ[k] A ⧸ kerIdeal (ψ.comp φ))
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective.comp hπA
  have h0 := (kerIdeal_le_ker_iff m' (Ideal.Quotient.mkₐ k (kerIdeal m'))).1
    fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h4 : kerIdeal ψ ≤ RingHom.ker q := (kerIdeal_le_ker_iff ψ q).2 fun b => by
    change Ideal.Quotient.mkₐ k (kerIdeal m') (πA (ψ b)) = _
    rw [← hm', h0, CoalgHomClass.counit_comp_apply]
  let q'' : (A ⧸ kerIdeal ψ) →ₐ[k] (A ⧸ kerIdeal (ψ.comp φ)) ⧸ kerIdeal m' :=
    Ideal.Quotient.liftₐ (kerIdeal ψ) q h4
  have hq'' : Function.Surjective q''.toLinearMap := fun x => by
    obtain ⟨a, rfl⟩ := hq x
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  rw [finrank_eq_ker_mul_range k _ _ m']
  exact Nat.mul_le_mul (LinearMap.finrank_le_finrank_of_surjective hq'')
    (LinearMap.finrank_range_le _)

end PDiv

namespace Dieu

theorem hasLogDeg_comp_le : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K) (a b c : ℕ),
    HasLogDeg f a → HasLogDeg g b → HasLogDeg (f ≫ g) c → c ≤ a + b := by
  intro p _ k _ _ G H K f g a b c ⟨N₁, h₁⟩ ⟨N₂, h₂⟩ ⟨N₃, h₃⟩
  let n := max N₁ (max N₂ N₃)
  have e₁ := h₁ n (le_max_left _ _)
  have e₂ := h₂ n (le_trans (le_max_left _ _) (le_max_right _ _))
  have e₃ := h₃ n (le_trans (le_max_right _ _) (le_max_right _ _))
  have hle := finrank_quot_kerIdeal_comp_le (f.app n) (g.app n)
  rw [← comp_app, e₃, e₁, e₂, ← pow_add] at hle
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hle

end Dieu

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeFieldPoint
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DualCon.FieldRep

theorem hasRep_field : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ g : ℕ,
    SmoothOfRelativeDimension g A.hom → ∀ (K : Type) [Field K] (s : Sp K ⟶ S), HasRep A g (Over.mk s) := by
  intro S A _ hA g hg K _ s
  have hA' : IsAbelianScheme ((Over.pullback s).obj A) := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  have hg' : SmoothOfRelativeDimension g ((Over.pullback s).obj A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  obtain ⟨L, hL, hamp⟩ := GlobalTheory.ProjFinite.exists_relAmple_of_isProjBy (GlobalTheory.T.abelianVariety_isProjectiveOverRingByCharts K _ hA')
  have hAF : HasRepAF ((Over.pullback s).obj A) g (𝟙_ _) := GlobalTheory.T.hasDualRepresentative_of_relAmple_noetherian K _ g hA' hg' L hL hamp
  have h := (GlobalTheory.DualCon.hasRep_baseChange_iff S (Sp K) s A ((Over.pullback s).obj A) (pullback.fst A.hom s)
    (isGrpPullback_pullback A s) g (𝟙_ _)).1.1
  obtain ⟨B, b, P, hR, hG, -⟩ := hAF
  have h2 := h ⟨B, b, P, hR, hG⟩
  have e : (𝟙_ (Over (Sp K))).hom ≫ s = s := Category.id_comp s
  rw [e] at h2
  exact h2

end GlobalTheory.DualCon.FieldRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceWeightFormsEqDimMulRationalClasses
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem trOn_forms_hop_eq_geom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → trOn (forms S lam K') (hop S K' f) = dimW lam * geomURat lam (fun γ => twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f)) := by
  intro E _ _ _ hU n hn S hS lam K' hK f hf hreg
  rw [GlobalTheory.T.heckeTrace_forms_eq_dim_mul_kernelSum E hU n hn S hS lam K' hK f hf, GlobalTheory.T.kernelSum_eq_finsum_regular_rationalClasses E hU n hn S hS lam K' hK f hf hreg]
  congr 1
  unfold geomURat
  refine finsum_congr fun c => ?_
  split_ifs with h
  · rw [GlobalTheory.T.classSum_eq_mass_mul_orbitalIntegral E hU n hn S hS lam K' hK f hf c.rep h]; ring
  · rfl

end GlobalTheory.BCT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolyEqIntersectionNumberStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_chernFormPoly_eq_intersectionNumber : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  first | exact @GlobalTheory.ChernLine.integral_evalF_c1W_eq_interPoly | exact GlobalTheory.ChernLine.integral_evalF_c1W_eq_interPoly | (intros; apply GlobalTheory.ChernLine.integral_evalF_c1W_eq_interPoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelOfAlgebraicModel
section
set_option autoImplicit false

open GlobalTheory.LatVal GlobalTheory.LatJet

namespace GlobalTheory.LatModel

theorem modelInt : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.SerreTateGoodReductionSt → GlobalTheory.Published.AbelianDeRham →
    GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.Statement → ModelAlg → ModelInt := by
  intro hPC hST hDR hDC hPM h31 _
  intro E _ _ _ _ I _ d φ _ hd _ _ _ 𝔣 Λ h𝔣 hΛ l _ Q hQ hQl y hy _ lam Ω hΩ
  exact GlobalTheory.T.cm_field_lattice_prime_condition hPC hDR hDC hPM h31 E I d φ hd 𝔣 Λ h𝔣 hΛ l Q hQ hQl y hy lam Ω hΩ
    (GlobalTheory.T.cm_field_lattice_base_condition hPC hST hDR hDC hPM E I d φ hd 𝔣 Λ h𝔣 hΛ l Q hQ hQl y hy lam Ω hΩ)

end GlobalTheory.LatModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDifferentialsConnectedPDivGroupCoordinaStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), (∀ w : Fin d → k, (fun n => ∑ i, w i • dUnit k (c.x n i)) ∈ G.omegaSub) ∧ ∀ u : G.omega, ∃! w : Fin d → k, ∀ n, u.1 n = ∑ i, w i • dUnit k (c.x n i) := by
  first | exact @GlobalTheory.OmegaCoord.omega_coord | exact GlobalTheory.OmegaCoord.omega_coord | (intros; apply GlobalTheory.OmegaCoord.omega_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageClosureCompleteDVRSpecialFibre
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.FibProperClosed

theorem isClosed_image_closure : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y P : Scheme.{0}) (q : Y ⟶ P)
    (s : P ⟶ Spec (CommRingCat.of O)) (C : Set Y), IsProper s → IsImmersion q →
    IsProper (pullback.snd (q ≫ s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) →
    IsIrreducible C → (∃ y ∈ closure C, (q ≫ s) y = IsLocalRing.closedPoint O) →
    IsClosed (q '' closure C) := by
  intro O _ _ _ hI Y P q s C hs hq hk hC hy
  set U : Set P := coborder (Set.range q) with hUdef
  have hUo : IsOpen U := q.isLocallyClosed_range.isOpen_coborder
  have hqU : Set.range q = U ∩ closure (Set.range q) := (coborder_inter_closure).symm
  have hZsub : closure (q '' C) ⊆ closure (Set.range q) := closure_mono (Set.image_subset_range _ _)
  have himg : q '' closure C = closure (q '' C) ∩ U := by
    rw [q.isEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_preimage_eq_inter_range, hqU]
    ext x
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, hZsub h1⟩
  have hZc : IsClosed (closure (q '' C)) := isClosed_closure
  have hZirr : IsIrreducible (closure (q '' C)) := (hC.image q q.continuous.continuousOn).closure

  have hZk : _root_.IsPreconnected (closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}) := by
    let I := Scheme.IdealSheafData.vanishingIdeal (⟨closure (q '' C), hZc⟩ : TopologicalSpace.Closeds P)
    have hrange : Set.range I.subschemeι = closure (q '' C) := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
    haveI : IsProper (I.subschemeι ≫ s) := inferInstance
    have hne : Nonempty I.subscheme := by
      obtain ⟨c, hc⟩ := hC.nonempty
      have : q c ∈ Set.range I.subschemeι := by rw [hrange]; exact subset_closure ⟨c, hc, rfl⟩
      obtain ⟨w, -⟩ := this
      exact ⟨w⟩
    have hpc : _root_.IsPreconnected (Set.univ : Set I.subscheme) := by
      rw [← I.subschemeι.isEmbedding.isInducing.isPreconnected_image, Set.image_univ, hrange]
      exact hZirr.2.isPreconnected
    haveI : ConnectedSpace I.subscheme := { toPreconnectedSpace := ⟨hpc⟩, toNonempty := hne }
    haveI hsp := GlobalTheory.AlgConn.connectedSpace_specialFibre_of_morphisms GlobalTheory.T.formalAlgebraisation_morphisms' O _
      (I.subschemeι ≫ s) inferInstance inferInstance
    have hT : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (I.subschemeι ≫ s)) =
        (I.subschemeι ≫ s) ⁻¹' {IsLocalRing.closedPoint O} := by
      have h := Scheme.Pullback.range_fst (I.subschemeι ≫ s)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
      rw [GlobalTheory.SpecialConn.range_residue] at h
      exact h
    have hR : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (I.subschemeι ≫ s) ≫ I.subschemeι) =
        closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O} := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hT, ← hrange, Set.inter_comm,
        ← Set.image_preimage_eq_inter_range]
      rfl
    rw [← hR]
    exact isPreconnected_range (Scheme.Hom.continuous _)

  have hkU : IsClosed ((closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}) ∩ U) := by
    let res := Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
    haveI : IsClosedImmersion res :=
      IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
    haveI : IsProper (pullback.snd (q ≫ s) res ≫ res) := inferInstance
    haveI : IsProper ((pullback.fst (q ≫ s) res ≫ q) ≫ s) := by
      rw [Category.assoc, pullback.condition]; infer_instance
    haveI : IsProper (pullback.fst (q ≫ s) res ≫ q) := IsProper.of_comp _ s
    have hF : Set.range (pullback.fst (q ≫ s) res) = (q ≫ s) ⁻¹' {IsLocalRing.closedPoint O} := by
      have h := Scheme.Pullback.range_fst (q ≫ s) res
      rw [GlobalTheory.SpecialConn.range_residue] at h
      exact h
    have hcl := (pullback.fst (q ≫ s) res ≫ q).isClosedMap _
      ((isClosed_closure (s := C)).preimage (pullback.fst (q ≫ s) res).continuous)
    have e : (pullback.fst (q ≫ s) res ≫ q) '' (pullback.fst (q ≫ s) res ⁻¹' closure C) =
        (closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}) ∩ U := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, Set.image_preimage_eq_inter_range, hF]
      change q '' (closure C ∩ q ⁻¹' (s ⁻¹' {IsLocalRing.closedPoint O})) = _
      rw [Set.image_inter_preimage, himg]
      ext x
      simp only [Set.mem_inter_iff]
      tauto
    rw [← e]; exact hcl
  have hne : ((closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}) ∩ U).Nonempty := by
    obtain ⟨y, hyC, hy⟩ := hy
    have h1 : q y ∈ closure (q '' C) ∩ U := himg ▸ ⟨y, hyC, rfl⟩
    exact ⟨q y, ⟨h1.1, hy⟩, h1.2⟩
  have hZkU : closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O} ⊆ U := by
    intro z hz
    by_contra hzU
    obtain ⟨w, hw, hw1, hw2⟩ := hZk U _ hUo hkU.isOpen_compl
        (fun x _ => by
          by_cases h : x ∈ U
          · exact Or.inl h
          · exact Or.inr fun h' => h h'.2)
        (by obtain ⟨x, hx1, hx2⟩ := hne; exact ⟨x, hx1, hx2⟩) ⟨z, hz, fun h => hzU h.2⟩
    exact hw2 ⟨hw, hw1⟩
  have hZU : closure (q '' C) ⊆ U := by
    intro z hz
    by_contra hzU
    have hcl : IsClosed (s '' (closure (q '' C) \ U)) := s.isClosedMap _ (hZc.sdiff hUo)
    have hsp : s z ⤳ IsLocalRing.closedPoint O :=
      (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal (s z).2.ne_top)
    obtain ⟨z', ⟨hz'Z, hz'U⟩, hz'⟩ := hsp.mem_closed hcl ⟨z, ⟨hz, hzU⟩, rfl⟩
    exact hz'U (hZkU ⟨hz'Z, hz'⟩)
  rw [himg, Set.inter_eq_left.2 hZU]
  exact hZc

end GlobalTheory.FibProperClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormEvalRealPolyChernFormsFlaggedMetric
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem isForm_evalF_chernF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ)
    (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H →
    ∀ R : MvPolynomial (ι × ℕ) ℝ, (atlas X σ).IsForm (evalF (atlas X σ) (chernF E H) R) := by
  intro F _ σ X ι _ m k E H h R
  exact ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (atlas X σ)).2.2.2.1 _ (chernF E H) R fun x =>
    (GlobalTheory.T.chernFormField_dbarCohomologous_two_connections _ _ (atlas X σ) _ _ _ (GlobalTheory.T.isGramConnectionPair_of_two_flagged_metrics F σ X ι m k E H H h h x.1) x.2).1).1

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenKawamataLogTerminalLocusLogCanonicalLocusStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_kawamataLogTerminalLocus_logCanonicalLocus : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsOpen {x : X | KltAt p n Δ x} ∧ IsOpen {x : X | LcAt p n Δ x} := by
  first | exact @GlobalTheory.Discrepancy.isOpen_kltLocus_lcLocus | exact GlobalTheory.Discrepancy.isOpen_kltLocus_lcLocus | (intros; apply GlobalTheory.Discrepancy.isOpen_kltLocus_lcLocus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyInducesPDivisibleGroupIsogenyPPartDegree
section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

open GlobalTheory.AV.KerPart in

theorem isIsog_hasLogDeg_map : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), IsIsogeny f → IsIsog (t.map t' f.hom) ∧ HasLogDeg (t.map t' f.hom) (padicValNat p (deg f)) := by
  intro p _ k _ A B G H t t' f hf
  have hp : p.Prime := Fact.out
  obtain ⟨N, g, hN, -, hfg, hgf⟩ := GlobalTheory.AV.AbVar.exists_quasiInverse_isogeny k A B f hf
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p hp.ne_one
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => hm (h0 ▸ dvd_zero p)
  have kill : ∀ {T : Over (Sp k)} (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ (p ^ a * m) = 1 :=
    fun x hx => pow_eq_one_of_comp hfg x hx
  refine ⟨?_, ?_⟩
  · have hu : IsUnit (m : ℤ_[p]) := by
      by_contra h
      have h1 : (m : ℤ_[p]) ∈ nonunits ℤ_[p] := h
      rw [PadicInt.mem_nonunits, PadicInt.norm_lt_one_iff_dvd] at h1
      obtain ⟨c, hc⟩ := h1
      have h2 := congrArg PadicInt.toZMod hc
      rw [map_natCast, map_mul, map_natCast, ZMod.natCast_self, zero_mul, ZMod.natCast_eq_zero_iff] at h2
      exact hm h2
    obtain ⟨u, hu⟩ := hu
    have hs : (↑u⁻¹ : ℤ_[p]) * ((p ^ a * m : ℕ) : ℤ_[p]) = (p : ℤ_[p]) ^ a := by
      push_cast
      rw [← hu, mul_left_comm, Units.inv_mul, mul_one]
    have eA : ((p ^ a * m) • 𝟙 A : A ⟶ A).hom = 𝟙 A.X ^ (p ^ a * m) := by simp
    have eB : ((p ^ a * m) • 𝟙 B : B ⟶ B).hom = 𝟙 B.X ^ (p ^ a * m) := by simp
    haveI : IsMonHom (𝟙 A.X ^ (p ^ a * m)) := eA ▸ inferInstance
    haveI : IsMonHom (𝟙 B.X ^ (p ^ a * m)) := eB ▸ inferInstance
    have h1 : t.map t' f.hom ≫ t'.map t g.hom = ((p ^ a * m : ℕ) : ℤ_[p]) • 𝟙 G := by
      rw [← TorsionTower.map_comp, ← t.map_pow_id]
      exact t.map_congr t (by rw [← comp_hom, hfg, eA])
    have h2 : t'.map t g.hom ≫ t.map t' f.hom = ((p ^ a * m : ℕ) : ℤ_[p]) • 𝟙 H := by
      rw [← TorsionTower.map_comp, ← t'.map_pow_id]
      exact t'.map_congr t' (by rw [← comp_hom, hgf, eB])
    refine ⟨a, (↑u⁻¹ : ℤ_[p]) • t'.map t g.hom, ?_, ?_⟩
    · rw [Linear.comp_smul, h1, smul_smul, hs]
    · rw [Linear.smul_comp, h2, smul_smul, hs]
  · obtain ⟨H₀, _, _, i₀, hK₀, hdeg⟩ := GlobalTheory.T.exists_isogeny_kernel_finite_algebra_finrank_eq_degree k A B f hf
    obtain ⟨Hm, _, _, im, hKm, hpm⟩ := GlobalTheory.T.exists_kernelPart_order_prime_to_p p k A B f m hm0 hm
    have hcop : (p ^ a).Coprime m := (Nat.Coprime.pow_left a ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)).symm))
    obtain ⟨H₁, _, _, i₁, hK₁, hrank⟩ := GlobalTheory.T.kernelPart_mul_of_coprime_abelianVariety k A B f (p ^ a) m hcop _ _ _ _ (kerPow_kerPt t t' f a) hKm
    have h01 : Module.finrank k H₁ = deg f := (finrank_eq_of_kerPow hK₁ hK₀ fun R _ _ x hx =>
      iff_of_true (kill x hx) (pow_zero x)).trans hdeg
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (finrank_quot_kerIdeal_dvd (t.map t' f.hom) a)
    have hv : padicValNat p (deg f) = j := by
      rw [← h01, hrank, hj, padicValNat.mul (pow_ne_zero _ hp.ne_zero) (fun h0 => hpm (by rw [h0]; exact dvd_zero p)),
        padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hpm, add_zero]
    refine ⟨a, fun n hn => ?_⟩
    rw [hv, ← hj]
    refine finrank_eq_of_kerPow (kerPow_kerPt t t' f n) (kerPow_kerPt t t' f a) fun R _ _ x hx => ?_
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h2 := pow_gcd_eq_one.2 ⟨h, kill x hx⟩
      have h3 : (p ^ n).gcd (p ^ a * m) = p ^ a := by
        obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hn
        rw [pow_add, Nat.gcd_mul_left, (Nat.Coprime.pow_left c ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)), mul_one]
      rwa [h3] at h2
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [pow_add, pow_mul, h, one_pow]

end GlobalTheory.Dieu
end
end

