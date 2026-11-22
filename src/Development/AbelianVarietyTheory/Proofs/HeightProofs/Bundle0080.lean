import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryPolynomialSpectralGap
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0044
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfB
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0038
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0081
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0012
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0026
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0059
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0057
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingSmul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryPolynomialSpectralGapStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactUnitary_polynomial_spectral_gap : ∀ {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n), (∀ j, inK ε (X j)) → (∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j) → ∃ c α : ℝ, 0 < c ∧ 0 < α ∧ ∀ i : ℕ, 1 ≤ i → ∀ p ∈ polyV ε i, (∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0) → c * (i : ℝ) ^ α * ∫ k, ‖p k‖ ^ 2 ∂(muK ε) ≤ ∑ j, ∫ k, ‖rder ε [X j] p k‖ ^ 2 ∂(muK ε) := by
  first | exact @GlobalTheory.KFourier.spectral_gap_rder | exact GlobalTheory.KFourier.spectral_gap_rder | (intros; apply GlobalTheory.KFourier.spectral_gap_rder <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosLowerBoundSections
section
noncomputable section

namespace GlobalTheory.BignessCompare

open Formalism.L2.Pj NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.IndefiniteRowSideFullHecke.FullTranscendenceDegree (CuspAt XP Generates ptNorm l2Norm FullTrdeg SmallForm ExistsNonzeroCuspFormOfWeightPair CurveModelAt CurveModelExists
  ptNorm_nonneg)

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} [Fintype κ]

theorem bdd_of_mem_holSub (X : κ → Data E r) (la : ∀ c, Wt (X c).Ψ r) {P : FDSec X} (hP : P ∈ holSub X la) :
    ∃ M : ℝ, ∀ p : FPt X, (X p.1).pnorm (la p.1) (P p.1) p.2 ≤ M := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    choose C hC using fun c => (hP c).1.2
    refine ⟨∑ c, |C c|, fun p => (hC p.1 p.2 p.2.2).trans ((le_abs_self _).trans ?_)⟩
    exact Finset.single_le_sum (f := fun c => |C c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  | zero => exact ⟨0, fun p => (pnorm_zero _ _ _).le⟩
  | add P Q _ _ hP hQ =>
    obtain ⟨a, ha⟩ := hP
    obtain ⟨b, hb⟩ := hQ
    exact ⟨a + b, fun p => (pnorm_add_le _ _ _ _ _).trans (add_le_add (ha p) (hb p))⟩
  | smul a P _ hP =>
    obtain ⟨b, hb⟩ := hP
    exact ⟨‖a‖ * b, fun p => (pnorm_smul _ _ a _ _).le.trans (mul_le_mul_of_nonneg_left (hb p) (norm_nonneg _))⟩

end Model

section Weights

variable {D : D7} {j : ℕ}

theorem wt_ext {u v : WeightFamilies.Wt D j} (e1 : ∀ τ i, u.aP τ i = v.aP τ i) (e2 : ∀ τ i, u.aM τ i = v.aM τ i)
    (e3 : u.n = v.n) : u = v := by
  have e1' : u.aP = v.aP := funext fun τ => funext (e1 τ)
  have e2' : u.aM = v.aM := funext fun τ => funext (e2 τ)
  obtain ⟨⟩ := u
  obtain ⟨⟩ := v
  simp only at e1' e2' e3
  subst e1' e2' e3
  rfl

theorem wsmul_add_one (e : ℕ) (w : WeightFamilies.Wt D j) : wadd (wsmul e w) w = wsmul (e + 1) w :=
  wt_ext (fun _ _ => (add_one_mul _ _).symm) (fun _ _ => (add_one_mul _ _).symm) (add_one_mul _ _).symm

theorem wadd_assoc (u v w : WeightFamilies.Wt D j) : wadd u (wadd v w) = wadd (wadd u v) w :=
  wt_ext (fun _ _ => (add_assoc _ _ _).symm) (fun _ _ => (add_assoc _ _ _).symm) (add_assoc _ _ _).symm

end Weights

section Record

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)

theorem exists_nonZeroComp_mul {u v : WeightFamilies.Wt D j} {F : B.Cusp j u} {G : B.Cusp j v} (hF : X.NonZeroComp u F)
    (hG : X.NonZeroComp v G) : ∃ H : B.Cusp j (wadd u v), X.NonZeroComp (wadd u v) H := by
  obtain ⟨H, hH⟩ := X.inc_mul u v F G
  refine ⟨H, fun w' K hK => ?_⟩
  obtain ⟨H', hH'⟩ := X.inc_mul v w' G K
  have h0 : H' = 0 := hF _ H' (by rw [← hH', ← mul_assoc, hH, hK])
  exact hG w' K (by rw [hH', h0, map_zero])

variable {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
  (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ Z, gF Z (X.inc u F) = 0) → F = 0)

include hinj in

theorem nonZeroComp_iff_ev {wL : WeightFamilies.Wt D j}
    (hs : ∀ Z, ∃ g : B.Cusp j wL, gF Z (X.inc wL g) ≠ 0 ∧ ∀ Z', Z' ≠ Z → gF Z' (X.inc wL g) = 0)
    {u : WeightFamilies.Wt D j} (F : B.Cusp j u) : X.NonZeroComp u F ↔ ∀ Z, gF Z (X.inc u F) ≠ 0 := by
  refine ⟨fun hF Z h0 => ?_, fun hF w' G hG => hinj w' G fun Z => ?_⟩
  · obtain ⟨g, h1, h2⟩ := hs Z
    obtain ⟨H, hH⟩ := X.inc_mul u wL F g
    have hz : H = 0 := by
      refine hinj _ H fun Z' => ?_
      rw [← hH, map_mul]
      by_cases e : Z' = Z
      · subst e
        rw [h0, zero_mul]
      · rw [h2 Z' e, mul_zero]
    have hg0 : g = 0 := hF wL g (by rw [hH, hz, map_zero])
    exact h1 (by rw [hg0, map_zero, map_zero])
  · have := congrArg (gF Z) hG
    rw [map_mul, map_zero] at this
    exact (mul_eq_zero.1 this).resolve_left (hF Z)

theorem exists_ev_ne_zero [Finite ι] {wL : WeightFamilies.Wt D j}
    (hs : ∀ Z, ∃ g : B.Cusp j wL, gF Z (X.inc wL g) ≠ 0 ∧ ∀ Z', Z' ≠ Z → gF Z' (X.inc wL g) = 0) :
    ∃ g : B.Cusp j wL, ∀ Z, gF Z (X.inc wL g) ≠ 0 := by
  have := Fintype.ofFinite ι
  choose g h1 h2 using hs
  refine ⟨∑ Z, g Z, fun Z => ?_⟩
  rw [map_sum, map_sum, Finset.sum_eq_single Z (fun Z' _ e => h2 Z' Z e.symm) (fun h => absurd (Finset.mem_univ _) h)]
  exact h1 Z

end Record

section Inst

variable {D : D7} {T : Formalism.L2.Pj.Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  {ka wL wF : WeightFamilies.Wt D j}

def GenNeZero {u : WeightFamilies.Wt D j} (F : CuspAt h j u) : Prop :=
  ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z (F.1 : T.R j) ≠ 0

def HasForms (wL : WeightFamilies.Wt D j) : Prop :=
  ∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ g : CuspAt h j wL, evC hG Z (g.1 : T.R j) ≠ 0

include h hj in

theorem genFromTest : GenFromTest (T.Q.Xo j) T.Q.c hG := fun Z => h.allTest j hj (Om Z) (genFr hG Z)

theorem formsEv_inc (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (F : CuspAt h j u) :
    formsEvR j hG (genFromTest h j hj hG) Z ((XP h j hj).inc u F) = evC hG Z (F.1 : T.R j) :=
  formsEvR_single j hG _ Z _ _

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem separating (H : HasForms h j hG wL) (Z : Comp (T.Q.Xo j) T.Q.c) :
    ∃ g : CuspAt h j wL, formsEvR j hG (genFromTest h j hj hG) Z ((XP h j hj).inc wL g) ≠ 0 ∧
      ∀ Z', Z' ≠ Z → formsEvR j hG (genFromTest h j hj hG) Z' ((XP h j hj).inc wL g) = 0 := by
  obtain ⟨g, hg⟩ := H Z
  obtain ⟨g', e1, e2⟩ := (GlobalTheory.Reg.compSplit_and_genValInj D T h j hj hG).1 Z wL g
  exact ⟨g', fun h0 => hg (e1.symm.trans ((formsEv_inc h j hj hG Z wL g').symm.trans h0)),
    fun Z' hZ => (formsEv_inc h j hj hG Z' wL g').trans (e2 Z' hZ)⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem nonZeroComp_iff_genNeZero (H : HasForms h j hG wL) {u : WeightFamilies.Wt D j} (F : CuspAt h j u) :
    (XP h j hj).NonZeroComp u F ↔ GenNeZero h j hG F := by
  have hV := (GlobalTheory.Reg.compSplit_and_genValInj D T h j hj hG).2
  refine (nonZeroComp_iff_ev (XP h j hj) (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z)
    (fun Z => formsEvR j hG (genFromTest h j hj hG) Z)
    (fun u F hF => hV u F fun Z => (formsEv_inc h j hj hG Z u F).symm.trans (hF Z))
    (separating h j hj hG H) F).trans (forall_congr' fun Z => ?_)
  exact ⟨fun a b => a ((formsEv_inc h j hj hG Z u F).trans b), fun a b => a ((formsEv_inc h j hj hG Z u F).symm.trans b)⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_nonZeroComp (H : HasForms h j hG wL) : ∃ g : CuspAt h j wL, (XP h j hj).NonZeroComp wL g := by
  have := CompFin.finite_comp (T.Q.Xo j) T.Q.c
  obtain ⟨g, hg⟩ := exists_ev_ne_zero (XP h j hj) (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z)
    (fun Z => formsEvR j hG (genFromTest h j hj hG) Z) (separating h j hj hG H)
  exact ⟨g, (nonZeroComp_iff_genNeZero h j hj hG H g).2 fun Z b => hg Z ((formsEv_inc h j hj hG Z wL g).trans b)⟩

def Bounds (σ : T.Q.c.F →+* ℂ) {N : ℕ} (w : Fin N → CuspAt h j wL) (k m₀ : ℕ) (β : CuspAt h j (wsmul k wL))
    (C : ℝ) : Prop :=
  ∀ p : FPt (T.U j σ).X, ptNorm h j σ (wsmul k wL) β p ≤ C * l2Norm h j σ w p ^ k ∧
    ptNorm h j σ (wsmul k wL) β p ^ m₀ ≤ C * l2Norm h j σ w p ^ (k * m₀ + 1)

def SmallOne {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  ∃ (σ : T.Q.c.F →+* ℂ) (k m₀ : ℕ) (β : CuspAt h j (wsmul k wL)) (C : ℝ),
    GoodEmb T.Q.c σ ∧ 1 ≤ m₀ ∧ GenNeZero h j hG β ∧ Bounds h j σ w k m₀ β C

def SmallAll {N : ℕ} (w : Fin N → CuspAt h j wL) : Prop :=
  ∃ (k m₀ : ℕ) (β : CuspAt h j (wsmul k wL)) (C : ℝ),
    1 ≤ m₀ ∧ GenNeZero h j hG β ∧ ∀ σ, GoodEmb T.Q.c σ → Bounds h j σ w k m₀ β C

def IsHyperbolicFrameAt (e : ℕ) (wL wF : WeightFamilies.Wt D j) : Prop :=
  ∃ (w' : WeightFamilies.Wt D j) (θ : CuspAt h j w'), wadd wF w' = wsmul e wL ∧ GenNeZero h j hG θ

include hj in
theorem IsHyperbolicFrameAt.mono (H : HasForms h j hG wL) {e e' : ℕ} (he : e ≤ e') (hA : IsHyperbolicFrameAt h j hG e wL wF) :
    IsHyperbolicFrameAt h j hG e' wL wF := by
  induction he with
  | refl => exact hA
  | step _ ih =>
    obtain ⟨w', θ, h1, h2⟩ := ih
    obtain ⟨g, hg⟩ := exists_nonZeroComp h j hj hG H
    obtain ⟨θ', h3⟩ := exists_nonZeroComp_mul (XP h j hj) ((nonZeroComp_iff_genNeZero h j hj hG H θ).2 h2) hg
    exact ⟨wadd w' wL, θ', by rw [wadd_assoc, h1, wsmul_add_one], (nonZeroComp_iff_genNeZero h j hj hG H θ').1 h3⟩

def Extra (G : GlobalFamilyData (recPlus h j hj) ka wL wF) : Prop :=
  (j < D.R.m → SmallAll h j hG G.w) ∧ ∃ e ≤ WeightFamilies.dimY D j + 4, IsHyperbolicFrameAt h j hG e wL wF

def CurveOn (b : Bool) : Prop :=
  ∀ (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (S : Scal (recB h.toLawsCore))
    (g₀ : (recB h.toLawsCore).Cusp j wF), (Extra h j hj hG G ↔ b = true) →
    SpanW (recPlus h j hj) G.w S → Formalism.L2.Pj.BigAt h j hj hG G → ThAt h j hj hG G g₀ →
    (recPlus h j hj).NonZeroComp wF g₀ → Nonempty (CurveModel G la g₀)

def SecondAt : Prop :=
  ∀ (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (XP h j hj) ka wL wF)
    (S : Scal (recB h.toLawsCore)), CurveModelAt h j hj hG G S

end Inst

end GlobalTheory.BignessCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsEtaMeanOfIsKroneckerChar
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj UpperHalfPlane
open GlobalTheory.IndefiniteRowSideFullHecke.LegendreCharacterCMCurves

namespace GlobalTheory.CMCurveCompare

section Fibre

variable {R R' : Type} [CommRing R] [CommRing R']

def pullPol (P : Out.PolAV (Sp R)) (hg : P.g = 1) {s : R →+* R'} {A : Over (Sp R')} [GrpObj A]
    {φ : A.left ⟶ P.A.left} (h : IsGrpPullback A P.A (spMap s) φ) : Out.PolAV (Sp R') :=
  have hL := pull_isLB P.isLB φ
  have H := pol_pull _ _ P.A A _ φ P.L _ P.isLB hL P.isAb h (PolBaseChange.lbIso_refl hL)
  { A := A, isAb := H.1, g := 1
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 (hg ▸ P.smoothDim)
    L := P.L.pull φ, isLB := hL, rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym, ample := H.2.1 P.ample, ktriv := H.2.2 P.ktriv }

theorem exists_unif (P : Out.PolAV (Sp R)) (hg : P.g = 1) (s : R →+* ℂ) :
    ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.A.left) (u : HolUnif A (P.L.pull φ) 1)
      (Hm : Matrix (Fin 1) (Fin 1) ℂ) (χ : u.Λ → ℂ), IsGrpPullback A P.A (spMap s) φ ∧ u.IsAH Hm χ := by
  obtain ⟨Q, φ, -, h, -⟩ := exists_isPolFibre polBaseChange_holds s P
  obtain ⟨rig, hr⟩ := (pullPol P hg h).rigid
  obtain ⟨u, Hm, χ, -, hA, -⟩ := thetaUnifAV_all (pullPol P hg h) rig hr
  exact ⟨Q.A, inferInstance, φ, u, Hm, χ, h, hA⟩

theorem isLieComb_one_iff {G : Over (Sp R)} [GrpObj G] (c : R) (v w : epsR R ⟶ G) :
    IsLieComb ![c] ![v] w ↔ w.left = spMap (epsScaleR c) ≫ v.left := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy 0
  · intro h
    exact ⟨![w], fun i => by fin_cases i; exact h, by simp⟩

theorem isLieNormSq_unique {P : Out.PolAV (Sp R)} {v : epsR R ⟶ P.A} (hv : IsTangent v) {s : R →+* ℂ} {x y : ℝ}
    (hx : IsLieNormSq P v s x) (hy : IsLieNormSq P v s y) : y = x := by
  have h1 : IsLieComb ![(1 : R)] ![v] (v ≫ 𝟙 P.A) := by
    rw [isLieComb_one_iff, Category.comp_id]
    have e : epsScaleR (1 : R) = RingHom.id _ := by
      ext a <;> simp [epsScaleR]
    rw [e]
    exact ((congrArg (· ≫ v.left) (Spec.map_id (CommRingCat.of (DualNumber R)))).trans (Category.id_comp _)).symm
  have e := NormHom.lieNormSq_comp thetaUnifAV_all T.abelianScheme_laws_unconditional.1 R P P (𝟙 P.A) (𝟙 P.A) v 1 s x y inferInstance
    inferInstance (PolBaseChange.lbIso_refl (LB.isLB_linComb P.isLB _ _)) hv h1 hx (by rwa [Category.comp_id])
  simpa using e

variable {P : Out.PolAV (Sp R)} {s : R →+* ℂ} {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ P.A.left}

end Fibre

section Line

theorem exists_scaled {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L 1)
    {Hm : Matrix (Fin 1) (Fin 1) ℂ} {χ : u.Λ → ℂ} (hA : u.IsAH Hm χ) {c : ℂ} (hc : c ≠ 0) :
    ∃ (u' : HolUnif A L 1) (Hm' : Matrix (Fin 1) (Fin 1) ℂ) (χ' : u'.Λ → ℂ), u'.IsAH Hm' χ' ∧
      ∀ z, z ∈ u'.Λ ↔ c • z ∈ u.Λ := by
  have e : ∀ z w : Fin 1 → ℂ, z ⬝ᵥ ((c * starRingEnd ℂ c) • Hm).mulVec (star w) =
      (c • z) ⬝ᵥ Hm.mulVec (star (c • w)) := fun z w => by
    simp [Matrix.mulVec, dotProduct]
    ring
  refine ⟨holUnifReparam u (LinearEquiv.smulOfNeZero ℂ _ c hc) 1 (differentiable_const _) fun _ => one_ne_zero,
    (c * starRingEnd ℂ c) • Hm, fun l => χ ⟨c • l.1, l.2⟩, ⟨?_, fun z hz => ?_, fun l => hA.2.2.1 _,
      fun l i z hz => ?_⟩, fun _ => Iff.rfl⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hA.1.eq]
    simp [mul_comm]
  · rw [e]
    exact hA.2.1 _ (smul_ne_zero hc hz)
  · rw [e, e]
    change u.fr i (c • z) / 1 = _ * (u.fr i (c • (z + l.1)) / 1)
    rw [div_one, div_one, smul_add]
    exact hA.2.2.2 ⟨c • l.1, l.2⟩ i _ hz

end Line

theorem zpow_identity {A : Type*} [CommGroup A] (i w : A) (k m n m' n' : ℤ) :
    i ^ (m * m' + (-k) * n * n') * w ^ (m * n' + n * m' + n * n') =
      (i ^ m * w ^ n) ^ m' * (w ^ m * (w * i ^ (-k)) ^ n) ^ n' := by
  simp only [mul_zpow, ← zpow_mul, zpow_add]
  ac_rfl

theorem exists_oAct {O : Type} [CommRing O] {ω : O} {k : ℕ} (hsq : ω ^ 2 + k = ω)
    (hco : ∀ a : O, ∃! p : ℤ × ℤ, a = p.1 + p.2 * ω) {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    {W : G ⟶ G} (hW : IsMonHom W) (hEq : (W ≫ W) * (𝟙 G) ^ k = W) : ∃ a : OAct O G, a.act ω = W := by
  choose c hc hcu using hco
  have hcoord : ∀ m n : ℤ, c ((m : O) + (n : O) * ω) = (m, n) := fun m n => (hcu _ (m, n) rfl).symm
  have hWW : W ≫ W = W * (𝟙 G) ^ (-(k : ℤ)) := by
    rw [zpow_neg, zpow_natCast, eq_mul_inv_iff_mul_eq]
    exact hEq
  let F : O → (G ⟶ G) := fun a => (𝟙 G) ^ (c a).1 * W ^ (c a).2
  have hF : ∀ m n : ℤ, F ((m : O) + (n : O) * ω) = (𝟙 G) ^ m * W ^ n := fun m n => by
    simp only [F, hcoord]
  have hex : ∀ a : O, ∃ m n : ℤ, a = (m : O) + (n : O) * ω := fun a => ⟨_, _, hc a⟩
  refine ⟨⟨F, fun a => ?_, ?_, fun a b => ?_, fun a b => ?_⟩, ?_⟩
  · have h1 := Serre.isMonHom_zpow (𝟙 G) (c a).1
    have h2 := Serre.isMonHom_zpow W (c a).2
    exact Serre.isMonHom_mul _ _
  · simpa using hF 1 0
  · obtain ⟨m, n, rfl⟩ := hex a
    obtain ⟨m', n', rfl⟩ := hex b
    have e : ((m : O) + (n : O) * ω) * ((m' : O) + (n' : O) * ω) =
        ((m * m' + (-(k : ℤ)) * n * n' : ℤ) : O) + ((m * n' + n * m' + n * n' : ℤ) : O) * ω := by
      push_cast
      linear_combination ((n : O) * (n' : O)) * hsq
    rw [e, hF, hF, hF]
    simp only [MonObj.comp_mul, GrpObj.comp_zpow, MonObj.mul_comp, GrpObj.zpow_comp, Category.comp_id,
      Category.id_comp, hWW]
    exact zpow_identity _ _ _ _ _ _ _
  · obtain ⟨m, n, rfl⟩ := hex a
    obtain ⟨m', n', rfl⟩ := hex b
    have e : ((m : O) + (n : O) * ω) + ((m' : O) + (n' : O) * ω) =
        ((m + m' : ℤ) : O) + ((n + n' : ℤ) : O) * ω := by
      push_cast
      ring
    rw [e, hF, hF, hF, zpow_add, zpow_add]
    exact mul_mul_mul_comm _ _ _ _
  · simpa using hF 0 1

section Clauses

def IsEtaMean (K : Type) [Field K] [NumberField K] (x : ℝ) : Prop :=
  ∀ (σ : K →+* ℂ) (τ : ClassGroup (𝓞 K) → ℍ), (∀ C, IsIdealClassPoint σ C (τ C)) →
    (∑ C, Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K = x

def IsEtaCurve (d : ℕ) (K : Type) [Field K] [NumberField K] (M : IntermediateField ℚ ℂ) [NumberField M] (w : M)
    (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) : Prop :=
  (w : ℂ) = (1 + Complex.I * √d) / 2 ∧ P.g = 1 ∧ IsLieBasis ![v] ∧
    (∃ (P₀ : Out.PolAV (Sp M)) (φ : P₀.A.left ⟶ P.A.left) (v₀ : epsR M ⟶ P₀.A) (W : P₀.A ⟶ P₀.A),
      IsPolFibre (algebraMap (𝓞 M) M) P P₀ φ ∧ IsVecOver (algebraMap (𝓞 M) M) φ v v₀ ∧ IsLieBasis ![v₀] ∧
      IsMonHom W ∧ (W ≫ W) * (𝟙 P₀.A) ^ ((1 + d) / 4) = W ∧ IsLieComb ![w] ![v₀] (v₀ ≫ W)) ∧
    (∀ (P' : Out.PolAV (Sp ℂ)) (φ : P'.A.left ⟶ P.A.left),
      IsPolFibre ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) P P' φ → ∀ u : HolUnif P'.A P'.L P'.g,
      ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ u.Λ ↔ ∃ m n : ℤ, z = fun _ => c * (m + n * (w : ℂ))) ∧
    (∀ s : M →+* ℂ, ∃ r : ℝ, 0 < r ∧ ∀ r', IsLieNormSq P v (s.comp (algebraMap (𝓞 M) M)) r' ↔ r' = r) ∧
    ∀ n : (M →+* ℂ) → ℝ, (∀ s, IsLieNormSq P v (s.comp (algebraMap (𝓞 M) M)) (n s)) →
    ∀ (σ : K →+* ℂ) (τ : ClassGroup (𝓞 K) → ℍ), (∀ C, IsIdealClassPoint σ C (τ C)) →
      (∑ s, Real.log (n s)) / Module.finrank ℚ M =
        (∑ C, -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K

def EtaCurve (d : ℕ) (K : Type) [Field K] [NumberField K] : Prop :=
  ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (w : M) (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A),
    IsEtaCurve d K M w P v

def ActCurve (d : ℕ) {K : Type} [Field K] (τ : K →+* ℂ) (x : ℝ) : Prop :=
  ∃ (M : Type) (_ : Field M) (_ : NumberField M) (P : Out.PolAV (Sp (𝓞 M))) (act : OAct (𝓞 K) P.A)
    (ρ : 𝓞 K →+* 𝓞 M) (v : epsR (𝓞 M) ⟶ P.A), IsCMCurve d τ x M P act ρ v

end Clauses

section Compare

variable {d : ℕ} {K : Type} [Field K] [NumberField K]

theorem exists_generator (hs : Squarefree d) (h4 : d % 4 = 3) (h2 : Module.finrank ℚ K = 2) {rt : K}
    (hr : rt ^ 2 = -(d : K)) {τ : K →+* ℂ} (hτ : τ rt = Complex.I * (Real.sqrt d : ℝ)) :
    ∃ ω : 𝓞 K, τ (ω : K) = (1 + Complex.I * √d) / 2 ∧ ω ^ 2 + ((1 + d) / 4 : ℕ) = ω ∧
      (∀ a : 𝓞 K, ∃! p : ℤ × ℤ, a = p.1 + p.2 * ω) ∧ ∀ Λ : Submodule ℤ (Fin 1 → ℂ),
        PureType.IsQuadLattice Λ d 1 ↔ ∀ z : Fin 1 → ℂ, z ∈ Λ ↔ ∃ a : 𝓞 K, z 0 = τ (a : K) := by
  obtain ⟨ω, hω, hgen⟩ := exists_integer_generator_of_sq_eq_neg h2 hs h4 hr
  have h1 : τ (ω : K) = (1 + Complex.I * √d) / 2 := by
    have := congrArg τ hω
    rw [map_mul, map_add, map_one, map_ofNat, hτ] at this
    linear_combination this / 2
  have hd' : (0 : ℝ) < √d := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < d))
  have hc : ∀ m n : ℤ, τ (((m : 𝓞 K) + n * ω : 𝓞 K) : K) = m + n * ((1 + Complex.I * √d) / 2) := fun m n => by
    rw [← h1]
    simp
  refine ⟨ω, h1, ?_, fun a => ?_, fun Λ => forall_congr' fun z => iff_congr Iff.rfl ⟨?_, ?_⟩⟩
  · obtain ⟨k, rfl⟩ : ∃ k, d = 4 * k + 3 := ⟨d / 4, by omega⟩
    rw [show (1 + (4 * k + 3)) / 4 = k + 1 by omega]
    refine RingOfIntegers.coe_injective ?_
    simp only [map_add, map_pow, map_natCast]
    change (ω : K) ^ 2 + _ = (ω : K)
    push_cast at hr ⊢
    linear_combination (2 * (ω : K) - 1 + rt) / 4 * hω + hr / 4
  · obtain ⟨m, n, e⟩ := hgen a
    refine ⟨(m, n), e, ?_⟩
    rintro ⟨m', n'⟩ e'
    have e₁ := (hc m' n').symm.trans ((congrArg (fun b : 𝓞 K => τ (b : K)) (e'.symm.trans e)).trans (hc m n))
    have e₂ := congrArg Complex.im e₁
    simp [hd'.ne'] at e₂
    subst e₂
    have e₃ : m' = m := by exact_mod_cast add_right_cancel e₁
    rw [e₃]
  · rintro ⟨m, n, rfl⟩
    exact ⟨_, by rw [hc, _root_.one_mul]⟩
  · rintro ⟨a, ha⟩
    obtain ⟨m, n, rfl⟩ := hgen a
    refine ⟨m, n, funext fun i => ?_⟩
    rw [Subsingleton.elim i 0, ha, hc, _root_.one_mul]

end Compare

def ActCurveAll : Prop :=
  ∀ (d : ℕ) [NeZero d], 7 ≤ d → Squarefree d → d % 4 = 3 → ∀ χ : DirichletCharacter ℂ d, IsKroneckerChar χ →
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ rt : K, rt ^ 2 = -(d : K) →
    ∀ τ : K →+* ℂ, τ rt = Complex.I * (Real.sqrt d : ℝ) → ActCurve d τ (Real.eulerMascheroniConstant +
      Real.log (2 * Real.pi / √d) - (deriv χ.LFunction 1 / χ.LFunction 1).re)

def CMCurvePrime : Prop :=
  ∀ d : ℕ, d.Prime → d % 16 = 7 → ∀ (K : Type) [Field K] [NumberField K],
    Module.finrank ℚ K = 2 → (∃ r : K, r ^ 2 = -(d : K)) → EtaCurve d K

end GlobalTheory.CMCurveCompare
end
end

