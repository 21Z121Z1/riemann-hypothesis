import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegDefiniteHyperplaneOfSignatureOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSobolevInequalityAdelicUnitary
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelBasisEveryGeometricPointLocalRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelSpread

theorem eq_one_of_point (O : Type) [CommRing O] [IsLocalRing O] (A : Over (Sp O)) [GrpObj A]
    (hA : IsAbelianScheme A) (n : ℕ) (hn : IsUnit (n : O)) (s : 𝟙_ (Over (Sp O)) ⟶ A)
    (hs : s ^ n = 1) (k : Type) [Field k] (x : Sp k ⟶ Sp O) (hx : toUnit (Over.mk x) ≫ s = 1) :
    s = 1 := by
  haveI := GlobalTheory.AbelianDim.connectedSpace_spec_of_isLocalRing O
  have hn' : IsUnit (n : Γ(Sp O, ⊤)) := by
    have := hn.map (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
    simpa using this
  obtain ⟨⟨-, het⟩, -⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion (hG := hA) A hn'
  haveI := hA.proper
  haveI : IsSeparated ((mulN A n).left ≫ A.hom) := by
    rw [Over.w (mulN A n)]; infer_instance
  haveI : IsSeparated (mulN A n).left := IsSeparated.of_comp _ A.hom
  have hab : s ≫ mulN A n = (1 : 𝟙_ (Over (Sp O)) ⟶ A) ≫ mulN A n := by
    rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id,
      Category.comp_id, hs, one_pow]
  have hj : toUnit (Over.mk x) ≫ s = toUnit (Over.mk x) ≫ (1 : 𝟙_ (Over (Sp O)) ⟶ A) := by
    rw [hx, MonObj.comp_one]
  exact Over.OverMorphism.ext (GlobalTheory.eq_of_connected_of_unramified_of_point (T := Sp O) (mulN A n).left
    (congrArg (·.left) hab) x (congrArg (·.left) hj))

end GlobalTheory.LevelSpread

namespace GlobalTheory.LevelSpread

theorem card_of_basis {I G : Type} [Fintype I] [Group G] {n : ℕ} (hn : n ≠ 0) (f : (I → ℤ) → G)
    (add : ∀ a b, f (a + b) = f a * f b) (tors : ∀ a, f a ^ n = 1)
    (ker : ∀ a, f a = 1 ↔ ∃ b, a = n • b) (onto : ∀ u : G, u ^ n = 1 → ∃ a, f a = u) :
    Nat.card {u : G // u ^ n = 1} = n ^ Fintype.card I := by
  haveI : NeZero n := ⟨hn⟩
  let F : (I → ZMod n) → {u : G // u ^ n = 1} := fun c => ⟨f fun i => (c i).val, tors _⟩
  have hF : Function.Injective F := fun c c' e => by
    have e₁ : f (fun i => (c i).val) = f fun i => (c' i).val := congrArg Subtype.val e
    have e₂ := add ((fun i => ((c i).val : ℤ)) - fun i => ((c' i).val : ℤ)) fun i => (c' i).val
    rw [sub_add_cancel, e₁] at e₂
    obtain ⟨b, hb⟩ := (ker _).1 (mul_eq_right.1 e₂.symm)
    funext i
    have := congrArg (fun z : ℤ => (z : ZMod n)) (congrFun hb i)
    simpa [sub_eq_zero] using this
  have hS : Function.Surjective F := by
    rintro ⟨u, hu⟩
    obtain ⟨a, rfl⟩ := onto u hu
    refine ⟨fun i => (a i : ZMod n), Subtype.ext ?_⟩
    show f (fun i => ((a i : ZMod n).val : ℤ)) = f a
    have hd : ∃ b, (fun i => ((a i : ZMod n).val : ℤ)) - a = n • b := by
      have : ∀ i, (n : ℤ) ∣ ((a i : ZMod n).val : ℤ) - a i := fun i => by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, sub_self]
      choose b hb using this
      exact ⟨b, funext fun i => by simpa using hb i⟩
    have e := add ((fun i => ((a i : ZMod n).val : ℤ)) - a) a
    rw [sub_add_cancel, (ker _).2 hd, _root_.one_mul] at e
    exact e
  rw [← Nat.card_congr (Equiv.ofBijective F ⟨hF, hS⟩), Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card]

theorem basis_at_every_point : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (g n : ℕ), IsUnit (n : O) → ∀ (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp O)) ⟶ A)), (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ n = 1) → ∀ (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (x₀ : Sp k₀ ⟶ Sp O), (∀ a, (toUnit (Over.mk x₀) ≫ lev a = 1 ↔ ∃ b, a = n • b)) → (∀ u : Over.mk x₀ ⟶ A, u ^ n = 1 → ∃ a, toUnit _ ≫ lev a = u) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp O), (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = n • b)) ∧ (∀ u : Over.mk x ⟶ A, u ^ n = 1 → ∃ a, toUnit _ ≫ lev a = u) := by
  intro O _ _ _ A _ _ hA g n hn lev add tors k₀ _ _ x₀ ker₀ onto₀ k _ _ x
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (M₀ := O) (by simpa using hn)
  have lev0 : lev 0 = 1 := mul_eq_left.1 ((add 0 0).symm.trans (by rw [add_zero]))
  have pw : ∀ (b : Fin g ⊕ Fin g → ℤ) (m : ℕ), lev (m • b) = lev b ^ m := fun b m => by
    induction m with
    | zero => rw [zero_smul, pow_zero, lev0]
    | succ m ih => rw [succ_nsmul, add, ih, pow_succ]
  have hunit : ∀ (F : Type) [Field F] (p : Sp F ⟶ Sp O), (n : F) ≠ 0 := fun F _ p => by
    obtain ⟨φ, rfl⟩ := Spec.map_surjective p
    have := (hn.map φ.hom).ne_zero
    simpa using this
  have ker : ∀ a, toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = n • b := fun a => by
    refine ⟨fun h => (ker₀ a).1 ?_, ?_⟩
    · rw [GlobalTheory.LevelSpread.eq_one_of_point O A hA n hn (lev a) (tors a) k x h, MonObj.comp_one]
    · rintro ⟨b, rfl⟩
      rw [pw, tors, MonObj.comp_one]
  refine ⟨ker, fun u hu => ?_⟩
  haveI := hA.proper
  obtain ⟨d, hd⟩ := GlobalTheory.AbelianDim.exists_relDim O A hA
  have hsa := GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA
  have c₀ := GlobalTheory.FibreTorsion.card_torsion_of_proper_fibre (Sp O) A hsa d hd k₀ x₀ inferInstance n
    (hunit k₀ x₀)
  have c := GlobalTheory.FibreTorsion.card_torsion_of_proper_fibre (Sp O) A hsa d hd k x inferInstance n
    (hunit k x)
  have b₀ := card_of_basis hn0 (fun a => toUnit (Over.mk x₀) ≫ lev a)
    (fun a b => by rw [add, MonObj.comp_mul]) (fun a => by rw [← MonObj.comp_pow, tors, MonObj.comp_one])
    ker₀ onto₀
  exact GlobalTheory.SiegelOfPolarised.onto_torsion hn0 (fun a => toUnit (Over.mk x) ≫ lev a)
    (fun a b => by rw [add, MonObj.comp_mul]) (fun a => by rw [← MonObj.comp_pow, tors, MonObj.comp_one])
    (fun a => (ker a).1) (c.trans (c₀.symm.trans b₀)) u hu

end GlobalTheory.LevelSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointSmulIntegralOfFourierCoeffNeZeroStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPoint_smul_integral_of_fourierCoeff_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → ∀ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q ≠ 0 → ∀ s : 𝓞 D.host.E, (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → s ∈ PP.asIdeal) → ∀ b, ∃ z : Dw.La, s • (cSep l₂ • levRep (q b)) = l₂.M • z := by
  first | exact @GlobalTheory.HatInt.smul_eq_of_hatC_ne_zero | exact GlobalTheory.HatInt.smul_eq_of_hatC_ne_zero | (intros; apply GlobalTheory.HatInt.smul_eq_of_hatC_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEquivarianceWeilModelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_equivariance_weil_model : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), (∀ g, ∃ k, IsLiftW R i g k) ∧ ∀ (σ : D.what₂.LL →+* ℂ), (∀ g k, IsLiftW R i g k → ∀ y v h, (R.HW i σ).e (R.gW i σ g y) v h = (R.HW i σ).e y v (h * k)) ∧ ∀ y v, R.eWf i σ ((R.HW i σ).e y v) = (R.HW i σ).e (∑ g, RealDat.eC (A := A) σ g • R.gW i σ g y) v := by
  first | exact @GlobalTheory.GalLift.act_eq_translation | exact GlobalTheory.GalLift.act_eq_translation | (intros; apply GlobalTheory.GalLift.act_eq_translation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockRankThreeLtTopStatement
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_cutoffGramBoundMixedBlock_rankThree_lt_top : ∀ p0 : ℕ, (p0 = 1 ∨ p0 = 2) → ∫⁻ w : Low 3 → ℂ, hB p0 w < ⊤ := by
  first | exact @GlobalTheory.IntBall.Fin3.lintegral_hB_lt_top | exact GlobalTheory.IntBall.Fin3.lintegral_hB_lt_top | (intros; apply GlobalTheory.IntBall.Fin3.lintegral_hB_lt_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralProdChartCoordinatesEqProdStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_prod_chartCoordinates_eq_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (h : (Low r → ℂ) → ℝ≥0∞), Measurable h → ∫⁻ z, ∏ τ, h (zOf X z τ) = ∏ _τ : X.Ψ, ∫⁻ w, h w := by
  first | exact @GlobalTheory.IntBall.lintegral_prod_zOf | exact GlobalTheory.IntBall.lintegral_prod_zOf | (intros; apply GlobalTheory.IntBall.lintegral_prod_zOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPairValueLinear
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.PsiBound

theorem form_conj {n : ℕ} (Z M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    star x ⬝ᵥ ((Zᴴ * M * Z) *ᵥ y) = star (Z *ᵥ x) ⬝ᵥ (M *ᵥ (Z *ᵥ y)) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem form_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (x y : Fin n → ℂ) :
    star (t • x) ⬝ᵥ (M *ᵥ (t • y)) = ((t ^ 2 : ℝ) : ℂ) * (star x ⬝ᵥ (M *ᵥ y)) := by
  rw [← algebraMap_smul ℂ t x, ← algebraMap_smul ℂ t y, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct]
  simp only [smul_eq_mul, Complex.coe_algebraMap, Complex.star_def, Complex.conj_ofReal]
  push_cast; ring

theorem bound_of_form {n : ℕ} (f : (Fin n → ℂ) → ℝ) (hc : Continuous f)
    (hh : ∀ (t : ℝ) (x : Fin n → ℂ), f (t • x) = t ^ 2 * f x) (hp : ∀ x, x ≠ 0 → 0 < f x) :
    ∃ K : ℝ, ∀ (A : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 ≤ s → (∀ x, f (A *ᵥ x) = s * f x) →
      ∀ a b, ‖A a b‖ ≤ K * Real.sqrt s := by
  first
  | exact @_root_.GlobalTheory.LowerTriangularEntryBound.entry_bound
  | exact _root_.GlobalTheory.LowerTriangularEntryBound.entry_bound
  | (apply _root_.GlobalTheory.LowerTriangularEntryBound.entry_bound <;> assumption)
  | (intros; apply _root_.GlobalTheory.LowerTriangularEntryBound.entry_bound <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LowerTriangularEntryBound.entry_bound <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LowerTriangularEntryBound.entry_bound ..)

end GlobalTheory.LKCx.PsiBound

namespace GlobalTheory.LKCx

end GlobalTheory.LKCx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSobolevInequalityAdelicUnitaryStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_sobolev_inequality_adelic_unitary : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∀ μ : Measure (GA D V), μ.IsHaarMeasure → ∃ (S : List (List (D.what₂.Tau × Mt V.rank))) (Ω : Set (GA D V)) (C : ℝ), (∀ l ∈ S, ∀ p ∈ l, p.2 ∈ lieAt V p.1) ∧ IsCompact Ω ∧ ∀ ψ : GA D V → ℂ, Continuous ψ → (∀ k ∈ U, k ∈ GfC V → ∀ g, ψ (g * k) = ψ g) → (∀ l : List (D.what₂.Tau × Mt V.rank), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → Continuous (l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ)) → (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Mt V.rank), (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => ψ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) → ∀ y, ‖ψ y‖ ^ 2 ≤ C * (S.map fun l => ∫ x in Ω, ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ) (y * x)‖ ^ 2 ∂μ).sum := by
  first | exact @GlobalTheory.SobLoc.local_sobolev | exact GlobalTheory.SobLoc.local_sobolev | (intros; apply GlobalTheory.SobLoc.local_sobolev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTensorCenterInclusionInjectiveCentralFinran
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.OrbFinAf

theorem iotaF_props : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), Function.Injective (iotaF G v) ∧ (∀ z x, Commute (iotaF G v z) x) ∧ Module.finrank (Qv v) (Qv v ⊗[ℚ] G.C) = G.n ^ 2 * Module.finrank (Qv v) (Qv v ⊗[ℚ] G.F) := by
  intro p _ G v
  haveI : IsSimpleRing G.C := G.simpleC
  haveI : Nontrivial G.C := inferInstance
  haveI : Module.Finite ℚ G.C := Module.Finite.trans G.F G.C
  refine ⟨?_, ?_, ?_⟩
  · have hf : Function.Injective ((IsScalarTower.toAlgHom ℚ G.F G.C).toLinearMap) :=
      (algebraMap G.F G.C).injective
    have := Module.Flat.lTensor_preserves_injective_linearMap (M := Qv v) _ hf
    exact this
  · intro z x
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact ha.add_left hb
    | tmul a f =>
      induction x using TensorProduct.induction_on with
      | zero => exact Commute.zero_right _
      | add c d hc hd => exact hc.add_right hd
      | tmul b c =>
        rw [iotaF_tmul]
        show (a ⊗ₜ[ℚ] algebraMap G.F G.C f) * (b ⊗ₜ[ℚ] c) = (b ⊗ₜ[ℚ] c) * (a ⊗ₜ[ℚ] algebraMap G.F G.C f)
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm a b,
          Algebra.commutes]
  · rw [Module.finrank_baseChange, Module.finrank_baseChange, ← Module.finrank_mul_finrank ℚ G.F G.C,
      G.rankC, mul_comm]

end GlobalTheory.OrbFinAf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitsLocallyCompactStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_units_locally_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) (Qv v ⊗[ℚ] G.C); T2Space (Qv v ⊗[ℚ] G.C)ˣ ∧ LocallyCompactSpace (Qv v ⊗[ℚ] G.C)ˣ ∧ SigmaCompactSpace (Qv v ⊗[ℚ] G.C)ˣ := by
  first | (exact @GlobalTheory.OrbFinAf.topA) | (exact GlobalTheory.OrbFinAf.topA) | (intros; apply GlobalTheory.OrbFinAf.topA  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAtSmulMem
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

namespace GlobalTheory.LogDR

theorem logAt_smul_mem : ∀ (X : Scheme.{0}) [IsIntegral X] (Z : Set X) (G : CartierDiv X) (a : ℕ) (y : X)
    (f : X.functionField) (η : abelian₂ X.functionField), RegAt y f → η ∈ logAt Z G a y → f • η ∈ logAt Z G a y := by
  intro X _ Z G a y f η hf hη
  unfold logAt spanForms at hη ⊢
  induction hη using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    refine ⟨f * c, ?_, v, hv, ?_⟩
    · exact (show G.RegularAt y c from hc).regAt_mul hf
    · rw [smul_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

end GlobalTheory.LogDR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMulVecOfMemTD
section
noncomputable section

open scoped Matrix

namespace GlobalTheory.HaarLin

def TD (R : Type) [CommRing R] (κ : Type) [Fintype κ] [DecidableEq κ] : Submonoid (Matrix κ κ R) :=
  Submonoid.closure ({M | ∃ i j : κ, ∃ c : R, i ≠ j ∧ M = Matrix.transvection i j c} ∪
    {M | ∃ d : κ → Rˣ, M = Matrix.diagonal fun i => (d i : R)})

def HasStableRangeOne (R : Type) [CommRing R] : Prop := ∀ a b : R, IsCoprime a b → ∃ t : R, IsUnit (a + t * b)

end GlobalTheory.HaarLin

open NumberField MeasureTheory Matrix
open scoped NNReal ENNReal
namespace GlobalTheory.HaarLin

private lemma nnreal_eq_of_smul_addHaar_eq {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
    {a b : ℝ≥0} (h : a • μ = b • μ) : a = b := by
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : X)
  have h1 : μ K ≠ 0 := (μ.measure_pos_of_mem_nhds hK0).ne'
  have h2 : μ K ≠ ∞ := hK.measure_lt_top.ne
  have h3 : (a • μ) K = (b • μ) K := by rw [h]
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply] at h3
  exact_mod_cast (ENNReal.mul_left_inj h1 h2).1 h3

private lemma map_mul_lemma_2 {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {κ : Type} [Fintype κ] [MeasurableSpace (κ → R)] [BorelSpace (κ → R)]
    (A B : Matrix κ κ R) (μ : Measure (κ → R)) :
    μ.map (fun x => (A * B) *ᵥ x) = (μ.map (fun x => B *ᵥ x)).map (fun x => A *ᵥ x) := by
  have hA : Measurable (fun x : κ → R => A *ᵥ x) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hB : Measurable (fun x : κ → R => B *ᵥ x) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  rw [Measure.map_map hA hB]
  congr 1
  funext x
  simp [Function.comp, Matrix.mulVec_mulVec]

private lemma exists_map_mulVec_eq_smul_of_invertible {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (P Q : Matrix κ κ R) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    ∃ c : ℝ≥0, ∀ μ : Measure (κ → R), μ.IsAddHaarMeasure → μ.map (fun x => P *ᵥ x) = c • μ := by
  let e : (κ → R) ≃+ (κ → R) :=
    { toFun := fun x => P *ᵥ x
      invFun := fun x => Q *ᵥ x
      left_inv := fun x => by simp [Matrix.mulVec_mulVec, hQP]
      right_inv := fun x => by simp [Matrix.mulVec_mulVec, hPQ]
      map_add' := fun x y => Matrix.mulVec_add P x y }
  have he : Continuous (fun x : κ → R => P *ᵥ x) := Continuous.matrix_mulVec continuous_const continuous_id
  have he' : Continuous (fun x : κ → R => Q *ᵥ x) := Continuous.matrix_mulVec continuous_const continuous_id
  have key : ∀ μ : Measure (κ → R), μ.IsAddHaarMeasure → (μ.map (fun x => P *ᵥ x)).IsAddHaarMeasure :=
    fun μ _ => e.isAddHaarMeasure_map μ he he'
  let μ₀ : Measure (κ → R) := Measure.addHaar
  haveI := key μ₀ inferInstance
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, μ₀.map (fun x => P *ᵥ x) = c • μ₀ :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  refine ⟨c, fun μ hμ => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : ℝ≥0, μ = k • μ₀ := ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  rw [hk, Measure.map_smul, hc, smul_comm]

private lemma map_transvection_mulVec_addHaar_eq_self {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (i j : κ) (hij : i ≠ j) (c : R)
    (μ : Measure (κ → R)) [μ.IsAddHaarMeasure] :
    μ.map (fun x => transvection i j c *ᵥ x) = μ := by
  set D : Matrix κ κ R := diagonal (Function.update (1 : κ → R) i (-1)) with hD0
  have hD : D * D = 1 := by
    rw [hD0, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    by_cases hk : k = i <;> simp [Function.update_apply, hk]
  have hT : transvection i j c * transvection i j (-c) = 1 := by
    rw [transvection_mul_transvection_same (h := hij), add_neg_cancel, transvection_zero]
  have hT' : transvection i j (-c) * transvection i j c = 1 := by
    rw [transvection_mul_transvection_same (h := hij), neg_add_cancel, transvection_zero]
  have hconj : D * transvection i j c * D = transvection i j (-c) := by
    have hji : j ≠ i := Ne.symm hij
    clear hD hT hT'
    ext a b
    simp only [hD0, Matrix.mul_diagonal, Matrix.diagonal_mul, transvection, Matrix.add_apply,
      Matrix.one_apply, Matrix.single_apply, Function.update_apply, Pi.one_apply]
    clear hD0
    split_ifs <;> grind
  have hone : μ.map (fun x => (1 : Matrix κ κ R) *ᵥ x) = μ := by
    simp only [Matrix.one_mulVec, Measure.map_id']
  obtain ⟨a, ha⟩ := exists_map_mulVec_eq_smul_of_invertible D D hD hD
  obtain ⟨t, ht⟩ := exists_map_mulVec_eq_smul_of_invertible _ _ hT hT'
  obtain ⟨t', ht'⟩ := exists_map_mulVec_eq_smul_of_invertible _ _ hT' hT
  have haa : a * a = 1 := by
    have h := map_mul_lemma_2 D D μ
    rw [hD, hone, ha μ inferInstance, Measure.map_smul, ha μ inferInstance, smul_smul] at h
    exact nnreal_eq_of_smul_addHaar_eq μ (by rw [one_smul]; exact h.symm)
  have htt : t' * t = 1 := by
    have h := map_mul_lemma_2 (transvection i j c) (transvection i j (-c)) μ
    rw [hT, hone, ht' μ inferInstance, Measure.map_smul, ht μ inferInstance, smul_smul] at h
    exact nnreal_eq_of_smul_addHaar_eq μ (by rw [one_smul]; exact h.symm)
  have hcj : t' = a * t * a := by
    have h := map_mul_lemma_2 (D * transvection i j c) D μ
    rw [hconj, ht' μ inferInstance, ha μ inferInstance, Measure.map_smul, map_mul_lemma_2,
      ht μ inferInstance, Measure.map_smul, ha μ inferInstance, smul_smul, smul_smul] at h
    exact nnreal_eq_of_smul_addHaar_eq μ h
  have h2 : t * t = 1 := by
    rw [hcj] at htt
    calc t * t = t * t * (a * a) := by rw [haa, mul_one]
      _ = a * t * a * t := by ring
      _ = 1 := htt
  have h3 : t = 1 := by
    have h4 : (t : ℝ) * t = 1 := by exact_mod_cast h2
    apply NNReal.eq
    have h5 := t.coe_nonneg
    push_cast
    nlinarith
  rw [ht μ inferInstance, h3, one_smul]

private lemma map_diagonal_mulVec_eq_inv_prod_smul {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [inst : MeasurableSpace (κ → R)] [hb : BorelSpace (κ → R)] (d : κ → Rˣ)
    (μ : Measure (κ → R)) [μ.IsAddHaarMeasure] :
    μ.map (fun x => diagonal (fun i => (d i : R)) *ᵥ x) = (∏ i, distribHaarChar R (d i))⁻¹ • μ := by
  letI : MeasurableSpace R := borel R
  haveI : BorelSpace R := ⟨rfl⟩
  have e : inst = MeasurableSpace.pi :=
    (@BorelSpace.measurable_eq (κ → R) _ inst hb).trans
      (@BorelSpace.measurable_eq (κ → R) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst e
  have h1 : ∀ u : Rˣ, (Measure.addHaar : Measure R).map (fun y => (u : R) * y) =
      (distribHaarChar R u)⁻¹ • Measure.addHaar := by
    intro u
    have hu : (fun y : R => (u : R) * y) = fun y => (DomMulAct.mk.symm (DomMulAct.mk u⁻¹)⁻¹ : Rˣ) • y := by
      funext y
      simp [Units.smul_def]
    rw [hu]
    change DomMulAct.mk u⁻¹ • (Measure.addHaar : Measure R) = _
    rw [Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk u⁻¹ • (Measure.addHaar : Measure R)) Measure.addHaar,
      addHaarScalarFactor_smul_eq_distribHaarChar, map_inv]
  set ν : Measure (κ → R) := Measure.pi (fun _ => (Measure.addHaar : Measure R)) with hν0
  have hν : ν.map (fun x => diagonal (fun i => (d i : R)) *ᵥ x) = (∏ i, distribHaarChar R (d i))⁻¹ • ν := by
    have hf : (fun x : κ → R => diagonal (fun i => (d i : R)) *ᵥ x) = fun x i => (d i : R) * x i := by
      funext x i
      exact mulVec_diagonal _ _ _
    haveI : ∀ i, SigmaFinite ((Measure.addHaar : Measure R).map (fun y => (d i : R) * y)) := fun i => by
      rw [h1]; infer_instance
    rw [hf, hν0, Measure.pi_map_pi (f := fun i y => (d i : R) * y)
      (fun i => (continuous_mul_left (d i : R)).measurable.aemeasurable)]
    simp_rw [h1]
    refine Measure.pi_eq (fun s hs => ?_)
    rw [Measure.smul_apply, Measure.nnreal_smul_coe_apply, Measure.pi_pi]
    simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply, ← Finset.prod_inv_distrib,
      Finset.prod_mul_distrib, ENNReal.coe_finset_prod]
  obtain ⟨k, hk⟩ : ∃ k : ℝ≥0, μ = k • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  rw [hk, Measure.map_smul, hν, smul_comm]

private lemma exists_unit_det_map_mulVec_haar_eq_inv_smul {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] {κ : Type} [Fintype κ] [DecidableEq κ]
    [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (M : Matrix κ κ R) (hM : M ∈ TD R κ) :
    ∃ v : Rˣ, (v : R) = M.det ∧ ∀ μ : Measure (κ → R), μ.IsAddHaarMeasure →
      μ.map (fun x => M *ᵥ x) = (distribHaarChar R v)⁻¹ • μ := by
  induction hM using Submonoid.closure_induction with
  | mem M hM =>
    simp only [Set.mem_union, Set.mem_setOf_eq] at hM
    rcases hM with ⟨i, j, c, hij, rfl⟩ | ⟨d, rfl⟩
    · refine ⟨1, by rw [det_transvection_of_ne (h := hij), Units.val_one], fun μ hμ => ?_⟩
      rw [map_one, inv_one, one_smul]
      exact map_transvection_mulVec_addHaar_eq_self i j hij c μ
    · refine ⟨∏ i, d i, by simp [det_diagonal], fun μ hμ => ?_⟩
      rw [map_prod]
      exact map_diagonal_mulVec_eq_inv_prod_smul d μ
  | one => exact ⟨1, by simp, fun μ hμ => by simp [Measure.map_id']⟩
  | mul M N _ _ hM hN =>
    obtain ⟨v, hv, hvμ⟩ := hM
    obtain ⟨w, hw, hwμ⟩ := hN
    refine ⟨v * w, by simp [hv, hw, det_mul], fun μ hμ => ?_⟩
    rw [map_mul_lemma_2, hwμ μ hμ, Measure.map_smul, hvμ μ hμ, smul_smul, map_mul, mul_inv, mul_comm]

theorem map_mulVec_of_mem_TD : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] (κ : Type) [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ R), M ∈ TD R κ → ∀ u : Rˣ, u.1 = M.det → ∀ μ : @Measure (κ → R) (borel _),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    @Measure.map _ _ (borel _) (borel _) (fun x : κ → R => M *ᵥ x) μ = ((distribHaarChar R u)⁻¹ : ℝ≥0) • μ := by
  intro R _ _ _ _ _ _ κ _ _ M hM u hu μ hμ
  letI : MeasurableSpace (κ → R) := borel (κ → R)
  haveI : BorelSpace (κ → R) := ⟨rfl⟩
  obtain ⟨v, hv, hvμ⟩ := exists_unit_det_map_mulVec_haar_eq_inv_smul M hM
  have huv : u = v := Units.ext (hu.trans hv.symm)
  subst huv
  exact hvμ μ hμ

end GlobalTheory.HaarLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedSimilitudePairMinpolyRootsNormSqEqStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.marked_similitude_pair_minpoly_roots_normSq_eq : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ → ∀ (φ : G.F →+* ℂ) (z : ℂ), P.pol.eval₂ φ z = 0 → ‖z‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  first | (exact @GlobalTheory.LKMid.MarkEll.mark_ell) | (exact GlobalTheory.LKMid.MarkEll.mark_ell) | (intros; apply GlobalTheory.LKMid.MarkEll.mark_ell  <;> assumption)
end

