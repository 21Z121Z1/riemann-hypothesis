import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0486
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0156
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0146
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0149
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0167
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0148
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0259
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0154
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0151
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0176
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0141
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0140
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0165
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0166
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0285
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0462
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0493
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedEvaluationEquivariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0474
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0364
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0490
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0489
import GroundTheory.PAdicHodge.FactorizationFactorialLe
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0487
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormConjugateInverse
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicSkewMatricesLocallyCompactGroupStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula PositivityTheory.FTA.FunctionalEquationHypotheses.B2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_skew_matrices_locally_compact_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ),
    (∀ β : Matrix (Fin n) (Fin n) (AE F E), β ∈ nA σ Y b ↔ βᵀ + ((ε : ℤ) : AE F E) • β.map (cA σ) = 0) →
    IsClosed (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) ∧ IsTopologicalAddGroup (nA σ Y b) ∧
    LocallyCompactSpace (nA σ Y b) ∧ SecondCountableTopology (nA σ Y b) ∧ T2Space (nA σ Y b) ∧ BorelSpace (nA σ Y b) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelRadTop.nA_top | exact GlobalTheory.CompanionTheory.SiegelRadTop.nA_top | (intros; apply GlobalTheory.CompanionTheory.SiegelRadTop.nA_top <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineGradedCohomologyVanishing
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

theorem capT_eq {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {ι : Type}
    (Q : ObjectProperty (Thick (LL q))) (U : ι → X.Opens) {n : ℕ} (i : Fin (n + 1) → ι) :
    capT (fun α => St Q {U α}) i = St Q {capO U i} := by
  funext T
  have h := GlobalTheory.T.inOpen_finite_inf_iff (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (U ∘ i) Finset.univ T
  have e : (⨅ α ∈ (Finset.univ : Finset (Fin (n + 1))), (U ∘ i) α) = capO U i := by simp [capO]
  rw [e] at h
  refine propext ⟨fun hT => ?_, fun hT a => ?_⟩
  · refine ⟨(hT 0).1, capO U i, rfl, h.2 fun a _ => ?_⟩
    obtain ⟨-, V, hV, hI⟩ := hT a
    rw [Set.mem_singleton_iff] at hV
    subst hV
    exact hI
  · obtain ⟨h1, V, hV, hI⟩ := hT
    rw [Set.mem_singleton_iff] at hV
    subst hV
    exact ⟨h1, _, rfl, h.1 hI a (Finset.mem_univ _)⟩

theorem dividedPowerFiltration_bot {K : Type} [CommRing K] {s : ℕ} (hs : 0 < s) : pdP (dividedPowersBot K) s = ⊥ := by
  refine le_bot_iff.1 (Ideal.span_le.2 ?_)
  rintro _ ⟨l, hl, hr, rfl⟩
  have : ∃ p ∈ l, p.1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    have : (l.map Prod.fst).sum = 0 := List.sum_eq_zero (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      exact hc p hp)
    omega
  obtain ⟨p, hp, hp0⟩ := this
  have h0 : (dividedPowersBot K).dpow p.1 p.2 = 0 := by
    have : p.2 = 0 := hl p hp
    rw [this]
    exact (dividedPowersBot K).dpow_eval_zero hp0
  simp only [SetLike.mem_coe]
  rw [List.prod_eq_zero (List.mem_map.2 ⟨p, hp, h0⟩)]
  exact Ideal.zero_mem _

theorem tfBase {K : Type} [Field K] [CharZero K] {s : ℕ} (hs : 0 < s) : TFBase (dividedPowersBot K) 1 s where
  nil := dividedPowerFiltration_bot hs
  tf r x h := by simpa using h
  dv n hn := ⟨0, (n : K)⁻¹, by simp; exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn)⟩

def zeroSerre (K : Type) [CommRing K] : Serre.{1} K where
  P M _ _ := Subsingleton M
  zero _ _ _ h := h
  mid M₁ M₂ M₃ _ _ _ _ _ _ f g hfg h₁ h₃ := ⟨fun a b => by
    have key : ∀ x : M₂, x = 0 := fun x => by
      obtain ⟨y, rfl⟩ := (hfg x).1 (Subsingleton.elim _ _)
      rw [Subsingleton.elim y 0, map_zero]
    rw [key a, key b]⟩

theorem subsingleton_H {K : Type} [CommRing K] (C : Cx.{1} K) (n : ℕ) (h : Subsingleton (C.X n)) : Subsingleton (C.H n) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [Subsingleton.elim a b]

theorem cech_van (hV : StVan) {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {ι : Type} (U : ι → X.Opens) (d : ι → ℕ)
    (c : ∀ α, Coord q (U α) (d α)) (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i)) (r b a : ℕ) (hr : r < s)
    (hbr : b ≠ r) : Subsingleton ((CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q l s (U α)) b).cx.H a) := by
  refine subsingleton_H _ a ?_
  refine ⟨fun x y => funext fun i => ?_⟩
  have e := capT_eq (q := q) (TF l s) U i
  obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (c (i 0)) (capO_le U i 0) (ha _ i)
  have : Subsingleton (HU (GF q r) (capT (fun α => SS q l s (U α)) i) b) := by
    rw [e]
    exact hV l s hb q c' r b hr hbr
  exact Subsingleton.elim _ _

theorem cech_pos (hB : StVB) {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {ι : Type} [Fintype ι] (U : ι → X.Opens) (d : ι → ℕ) (V : X.Opens) (hV : IsAffineOpen V)
    (hU : (⨆ α, U α) = V)
    (c : ∀ α, Coord q (U α) (d α)) (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i)) (r p : ℕ) (hr : r < s) :
    Subsingleton ((CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q l s (U α)) r).cx.H (p + 1)) := by
  obtain ⟨vb⟩ := hB l s hb q U d c ha r hr
  exact GlobalTheory.T.affine_cover_higher_cohomology_vanishes (strV q) V hV U hU ha (CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q l s (U α)) r) vb p

set_option maxHeartbeats 2000000 in
theorem main (hV : StVan) (hB : StVB) (hC : StCover) : KH.GlobSerreSt → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (V : X.Opens) (hV : IsAffineOpen V) (s r j : ℕ), r < s → j ≠ r → Subsingleton (HQ (KS q s {V}) r ((r : ℤ) + 1) j) := by
  intro hS K _ _ X q _ V hVa s r j hr hj
  have hs : 0 < s := by omega
  have hb : TFBase (dividedPowersBot K) 1 s := tfBase hs
  obtain ⟨ι, _, U, d, c, hU, ha⟩ := hC q V hVa
  have hle : ∀ α, U α ≤ V := fun α => hU ▸ le_iSup U α
  have hinc : St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) (Set.range U) ≤
      St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) {V} := by
    rintro T ⟨h1, W, ⟨α, rfl⟩, hI⟩
    exact ⟨h1, V, rfl, fun x hx => hle α (hI hx)⟩
  have hz := GlobalTheory.T.cech_refinement_cohomology_bijective (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) (Or.inl ⟨rfl, 1, s, rfl⟩) (Set.range U) {V} hinc
    (by
      rintro W rfl
      rw [← hU, sSup_range]) j
  have hcech : ∀ a b, a + b = j → (zeroSerre K).P ((CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q 1 s (U α)) b).cx.H a) := by
    intro a b hab
    by_cases hbr : b = r
    · subst hbr
      cases a with
      | zero => exact absurd (by omega) hj
      | succ p => exact cech_pos hB 1 s hb q U d V hVa hU c ha b p hr
    · exact cech_van hV 1 s hb q U d c ha r b a hr hbr
  have hG := hS (O := K) (R := K) (I := ⊥) (γ := dividedPowersBot K) (p := 0) (X := X) (q := q) (κ := Ideal.Quotient.mk ⊥) (Λ := K)
    (GF q r) (TF 1 s) U (zeroSerre K) j hcech
  exact @Function.Injective.subsingleton _ _ _ (hz.1 r ((r : ℤ) + 1)).1 hG

end GlobalTheory.CompanionTheory.GrForm

namespace GlobalTheory.CompanionTheory.GrForm

theorem gr_aff : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (V : X.Opens) (hV : IsAffineOpen V) (s r j : ℕ), r < s → j ≠ r → Subsingleton (HQ (KS q s {V}) r ((r : ℤ) + 1) j) := fun hL _ hP hS _ =>
  main (GlobalTheory.T.graded_form_vanish_of_frame GlobalTheory.T.graded_form_frame hL hP)
    (GlobalTheory.T.graded_form_vector_bundle (GlobalTheory.T.graded_form_exists_of_cocycle GlobalTheory.T.graded_form_cocycle) GlobalTheory.T.graded_form_add GlobalTheory.T.graded_form_smul GlobalTheory.T.graded_form_restrict GlobalTheory.T.graded_form_action (GlobalTheory.T.graded_form_local_of_frame GlobalTheory.T.graded_form_frame hL hP))
    GlobalTheory.T.graded_form_cover hS
end GlobalTheory.CompanionTheory.GrForm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMinorHeightBoundStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_minor_height_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (w : InfinitePlace F) (τ : EmbOver E w) (X : GL ι (AE F E)) (κ : Matrix ι ι (AE F E)),
    κ.map (piInf τ) * (κ.map (piInf τ))ᴴ = 1 → ∀ f e : Fin n → ι,
    ‖piInf τ ((X.1 * κ).submatrix f e).det‖₊ ≤ (n.factorial : ℝ≥0) * htInf F w (Formalism.UG.bc (compInf F E w) X) ^ n := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.MinInf.minor_le_htInf | exact GlobalTheory.CompanionTheory.GodementH.MinInf.minor_le_htInf | (intros; apply GlobalTheory.CompanionTheory.GodementH.MinInf.minor_le_htInf <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellOfPoissonSiegel
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WeilSiegel

theorem bigCell_of_poisson_siegel :
    (∀ (D : Formalism.BasicNotions.D7) (r : ℕ), ∃ (lam : Measure (PositivityTheory.GramSchwartzFunctions.BC.hermA D r)) (𝓖 : Set (PositivityTheory.GramSchwartzFunctions.BC.hermA D r)), PositivityTheory.GramSchwartzFunctions.BC.IsCovolOneH lam 𝓖) → PositivityTheory.GramSchwartzFunctions.BC.PoissonHerm → (∀ (D : Formalism.BasicNotions.D7) (r : ℕ) (V : Formalism.BasicNotions.TH.HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ → HasSum (fun β : PositivityTheory.GramSchwartzFunctions.HermE D r => PositivityTheory.GramSchwartzFunctions.BC.IfrB V ν φ β) (PositivityTheory.GramSchwartzFunctions.Ifr V ν φ)) → PositivityTheory.GramSchwartzFunctions.BC.SiegelND → PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg → PositivityTheory.GramSchwartzFunctions.BigCell := by
  intro hlam hP hG hND hDeg D r V h2r ψ hψ θ hθ μ 𝓕 h𝓕 ν hν φ hφ habs hsum
  obtain ⟨lam, 𝓖, hlg⟩ := hlam D r
  have hyp : Hyp D r V ψ θ μ lam ν φ :=
    ⟨h2r, hψ, hθ, ⟨𝓕, h𝓕⟩, ⟨𝓖, hlg⟩, hν, hφ, habs⟩
  have h1 := hP D r V ψ θ μ lam ν φ hyp hsum
  have h2 := hG D r V θ hθ ν hν φ hφ habs
  have h3 : (fun β : HermE D r => IfrB V ν φ β) = fun β : HermE D r => W ψ V μ lam φ β := by
    funext β
    by_cases hβ : β.1.det = 0
    · exact hDeg D r V ψ θ μ lam ν φ hyp β hβ
    · exact hND D r V ψ θ μ lam ν φ hyp β hβ
  rw [h3] at h2
  have h4 := h1.unique h2
  have h5 := hsum.hasSum
  rwa [h4] at h5

end GlobalTheory.CompanionTheory.WeilSiegel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasselmanFirstProperty
section
noncomputable section

open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Casselman

theorem hecke_dominant_mul_abstract (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    PositivityTheory.SphericalProduct.A1 G := by
  intro D V _ _ π hπ t t' ht _ U U' hU hU' v f hf
  obtain ⟨r, hr, x, hx, hcos⟩ := GlobalTheory.T.dominant_coset_reps_unipotent G D t' ‹_›
  have hform := GlobalTheory.T.hecke_operator_coset_formula G D.J D.isOpen_J D.isCompact_J V π hπ (t' : G) U' hU' r x hr
    (fun i => (hx i).1) hcos v
  have hfx : ∀ (x : G), x ∈ D.J → ∀ w : V, f (π x w) = f w := fun x hxJ w =>
    LinearMap.congr_fun (hf x hxJ) w
  have hterm : ∀ i, f (π (t : G) (π (x i * (t' : G)) (v : V))) = f (π ((t : G) * t') (v : V)) := by
    intro i
    have hconj : (t : G) * x i * (t : G)⁻¹ ∈ D.J := (ht.1 (x i) (hx i)).1
    have hmul : (t : G) * (x i * (t' : G)) = ((t : G) * x i * (t : G)⁻¹) * ((t : G) * t') := by group
    rw [← Module.End.mul_apply, ← map_mul, hmul, map_mul, Module.End.mul_apply]
    exact hfx _ hconj _
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hUU : ((((U * U') v : fixed π D.J)) : V) = ((U (U' v) : fixed π D.J) : V) := rfl
  rw [hUU, ← hU (U' v) f hf, hform, map_smul, map_smul, map_sum, map_sum, Finset.sum_congr rfl (fun i _ => hterm i)]
  simp [hr0]

end GlobalTheory.CompanionTheory.Casselman

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedEvaluationEquivariantStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_evaluation_equivariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (u : MirUin k ((i + 1) + t + 1)) (f : XS τ σ),
  eC ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (u : Mir k ((i + 1) + t + 1)) f) =
      ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) • eC ψ f := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.TwC.eC_tw | exact GlobalTheory.CompanionTheory.BZPhiPG.TwC.eC_tw | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.TwC.eC_tw <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofiniteCenterMonicAnnihilator
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin

theorem cofin_monic_on_killed : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ)
    (J : Set (Module.End ℂ (Sm E n))), Cofin J → ∀ z ∈ Zalg E n, ∃ p : Polynomial ℂ, p.Monic ∧
      ∀ φ : Sm E n, (∀ j ∈ J, j φ = 0) → Polynomial.aeval z p φ = 0 :=
  fun E _ _ _ n J hJ z hz => GlobalTheory.CompanionTheory.Affgl.minpoly_on_killed E n J hJ z hz

end GlobalTheory.CompanionTheory.CTFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinvariantLeviActionModulus
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.QLevi

theorem tmul_scalars {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (x : A) (y : B)
    (c d d' e f : ℂ) (hd : d * d' = 1) :
    (c * (e * f)) • (x ⊗ₜ[ℂ] y) = (d * e) • ((c • d' • x) ⊗ₜ[ℂ] (f • y)) := by
  rw [smul_smul, TensorProduct.smul_tmul_smul, smul_smul]
  congr 1
  linear_combination (-(c * e * f)) * hd

theorem qC_sigX : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (h : MirabolicParabolic k (i + 1) t) (η : HPG k (i + 1) (t + 1)) (hη : pgProj k (i + 1) (t + 1) η = (levi k (i + 1) (gpProj k (i + 1) t h).1, (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k))) (w : τ.V ⊗[ℂ] σ.V), qC τ σ (sigX τ σ η w) = ((dpow (i + 1) (1 / 2) (gpProj k (i + 1) t h).1 * dpow (t + 1) (-1 / 2) (((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k) : ℂˣ) : ℂ) • sigC τ σ h (qC τ σ w) := by
  intro k _ _ _ _ i t τ σ h η hη w
  generalize hgdef : (gpProj k (i + 1) t h).1 = g at *
  generalize hpdef : (gpProj k (i + 1) t h).2 = p at *
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul a b =>
    have hL : sigX τ σ η (a ⊗ₜ[ℂ] b) =
        (((dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2) (levi k (i + 1) g) : ℂˣ) : ℂ) • τ.ρ (levi k (i + 1) g) a) ⊗ₜ[ℂ]
        (((dpow (t + 1) (-((i + 1 + 1 : ℕ) : ℝ) / 2) (p : GL (Fin (t + 1)) k) : ℂˣ) : ℂ) • σ.ρ (p : GL (Fin (t + 1)) k) b) := by
      show extTensor _ _ (pgProj k (i + 1) (t + 1) η) _ = _
      rw [hη]
      exact extTensor_tmul (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ
        (levi k (i + 1) g, (p : GL (Fin (t + 1)) k)) a b
    have hR : sigC τ σ h (qC τ σ (a ⊗ₜ[ℂ] b)) =
        (((dpow (i + 1) (((t + 1 : ℕ) : ℝ) / 2) g : ℂˣ) : ℂ) • ((dpow (i + 1) (-1 / 2) g : ℂˣ) : ℂ) •
          ((twKer τ.ρ (MirUin k (i + 1)) 1).mkQ (τ.ρ (levi k (i + 1) g) a) : (psiN τ).V)) ⊗ₜ[ℂ]
        (((dpow (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) (p : GL (Fin (t + 1)) k) : ℂˣ) : ℂ) • σ.ρ (p : GL (Fin (t + 1)) k) b) := by
      show extTensor _ _ (gpProj k (i + 1) t h) (qC τ σ (a ⊗ₜ[ℂ] b)) = _
      have hq : qC τ σ (a ⊗ₜ[ℂ] b) = ((twKer τ.ρ (MirUin k (i + 1)) 1).mkQ a : (psiN τ).V) ⊗ₜ[ℂ] b := rfl
      have hgp : gpProj k (i + 1) t h = (g, p) := Prod.ext hgdef hpdef
      rw [hq, hgp]
      exact extTensor_tmul ((psiN τ).tw (((t + 1 : ℕ) : ℝ) / 2)).ρ (mtw (gres σ) (-((i + 1 : ℕ) : ℝ) / 2)).ρ (g, p)
        ((twKer τ.ρ (MirUin k (i + 1)) 1).mkQ a : (psiN τ).V) b
    have hg : dpow (i + 1) (1 / 2) g * dpow (i + 1) (-1 / 2) g = (1 : ℂˣ) := by
      have e := DFunLike.congr_fun (GlobalTheory.CompanionTheory.LeibOrd.DerivTw.dpow_add (k := k) (i + 1) (-1 / 2) (1 / 2)) g
      rw [MonoidHom.mul_apply] at e
      rw [← e, show (-1 / 2 + 1 / 2 : ℝ) = 0 by norm_num, GlobalTheory.CompanionTheory.LeibOrd.DerivTw.dpow_zero]
      rfl
    have hp : dpow (t + 1) (-((i + 1 + 1 : ℕ) : ℝ) / 2) (p : GL (Fin (t + 1)) k) =
        dpow (t + 1) (-1 / 2) (p : GL (Fin (t + 1)) k) * dpow (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) (p : GL (Fin (t + 1)) k) := by
      have e := DFunLike.congr_fun (GlobalTheory.CompanionTheory.LeibOrd.DerivTw.dpow_add (k := k) (t + 1) (-((i + 1 : ℕ) : ℝ) / 2) (-1 / 2))
        (p : GL (Fin (t + 1)) k)
      rw [MonoidHom.mul_apply] at e
      rw [← e]
      congr 2
      push_cast
      ring
    have hg' : ((dpow (i + 1) (1 / 2) g : ℂˣ) : ℂ) * ((dpow (i + 1) (-1 / 2) g : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, hg, Units.val_one]
    have hq : qC τ σ ((τ.ρ (levi k (i + 1) g) a) ⊗ₜ[ℂ] (σ.ρ (p : GL (Fin (t + 1)) k) b)) =
        ((twKer τ.ρ (MirUin k (i + 1)) 1).mkQ (τ.ρ (levi k (i + 1) g) a) : (psiN τ).V) ⊗ₜ[ℂ] (σ.ρ (p : GL (Fin (t + 1)) k) b) := rfl
    rw [hL, hR, GlobalTheory.CompanionTheory.LeibOrd.DerivTw.dpowM_levi, hp, TensorProduct.smul_tmul_smul, map_smul, hq]
    exact tmul_scalars _ _ _ _ _ _ _ hg'

end GlobalTheory.CompanionTheory.BZPhiPG.QLevi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFiniteAdelicDenominator
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.AdeleDenom

open IsDedekindDomain

theorem isIntegral_of_forall_mem_adicCompletionIntegers {F : Type} [Field F] [NumberField F] (f : F)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), (f : v.adicCompletion F) ∈ HeightOneSpectrum.adicCompletionIntegers F v) :
    IsIntegral ℤ f := by
  obtain ⟨r, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) (K := F) (x := f)
    (fun v => by
      have hv := h v
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.adicCompletion.valued_coe] at hv
      exact hv)
  exact NumberField.RingOfIntegers.isIntegral_coe r

theorem exists_nat_mul_isIntegral_of_isCompact (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (L : Set (Af F ⊗[F] E)) (hL : IsCompact L) :
    ∃ d : ℕ, 0 < d ∧ ∀ e : E, inclR (F := F) (Af F) e ∈ L → IsIntegral ℤ ((d : E) * e) := by
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have key : ∀ x : E, ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * x) := by
    intro x
    have halg : IsAlgebraic ℤ x :=
      (IsFractionRing.isAlgebraic_iff (A := ℤ) (K := ℚ) (C := E)).mpr (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)
    obtain ⟨y, hy, hyx⟩ := halg.exists_integral_multiple
    refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
    have hc : ((y.natAbs : ℕ) : E) = ((|y| : ℤ) : E) := by
      rw [← Int.cast_natCast, Int.natCast_natAbs]
    rcases abs_choice y with h | h
    · rw [hc, h, ← zsmul_eq_mul]
      exact hyx
    · rw [hc, h, Int.cast_neg, neg_mul, ← zsmul_eq_mul]
      exact hyx.neg
  let b := Module.finBasis F E
  choose mm hmm0 hmm using fun i => key (b i)
  obtain ⟨m, hm0, hmb⟩ : ∃ m : ℕ, 0 < m ∧ ∀ i, IsIntegral ℤ ((m : E) * b i) := by
    refine ⟨∏ i, mm i, Finset.prod_pos fun i _ => hmm0 i, fun i => ?_⟩
    have hsplit : ((∏ j, mm j : ℕ) : E) = ((∏ j ∈ Finset.univ.erase i, mm j : ℕ) : E) * (mm i : E) := by
      rw [← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    rw [hsplit, mul_assoc]
    refine IsIntegral.mul ?_ (hmm i)
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := ((∏ j ∈ Finset.univ.erase i, mm j : ℕ) : ℤ)))
  let B := Algebra.TensorProduct.basis (Af F) b
  let φ : (Af F ⊗[F] E) →ₗ[Af F] (Fin (Module.finrank F E) → Af F) := B.equivFun.toLinearMap
  have hφ : Continuous φ := IsModuleTopology.continuous_of_linearMap φ
  obtain ⟨N, hN, hNK⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F (hL.image hφ)
  refine ⟨N * m, Nat.mul_pos hN hm0, fun e he => ?_⟩
  have hx := hNK (φ (inclR (F := F) (Af F) e)) ⟨_, he, rfl⟩
  have hcoord : ∀ i, φ (inclR (F := F) (Af F) e) i = algebraMap F (Af F) (b.repr e i) := by
    intro i
    have hincl : inclR (F := F) (Af F) e = (1 : Af F) ⊗ₜ[F] e := rfl
    simp [φ, B, hincl, Algebra.TensorProduct.basis_repr_tmul]
  have hint : ∀ i, IsIntegral ℤ ((N : F) * b.repr e i) := by
    intro i
    refine isIntegral_of_forall_mem_adicCompletionIntegers _ fun v => ?_
    have h1 := hx i v
    rw [hcoord, ← map_natCast (algebraMap F (Af F)) N, ← map_mul] at h1
    exact h1
  have hsum : ((N * m : ℕ) : E) * e = ∑ i, algebraMap F E ((N : F) * b.repr e i) * ((m : E) * b i) := by
    conv_lhs => rw [← b.sum_repr e]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, map_natCast]
    push_cast
    ring
  rw [hsum]
  exact IsIntegral.sum _ fun i _ => (hint i).algebraMap.mul (hmb i)

end GlobalTheory.CompanionTheory.AdeleDenom
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactPartDiagonalMapStatement
section
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_part_diagonal_map : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (Z : Subgroup H), cptPart (Z.map ((MonoidHom.id H).prod (MonoidHom.id H))) = (cptPart Z).map ((MonoidHom.id H).prod (MonoidHom.id H)) := by
  first | exact @GlobalTheory.CompanionTheory.CptDiag.cptPart_diag | exact GlobalTheory.CompanionTheory.CptDiag.cptPart_diag | (intros; apply GlobalTheory.CompanionTheory.CptDiag.cptPart_diag <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjCompactOfAdmissible
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs
open GroundTheory.Automorphic.Reduction (adelicBorel posIdele diagUnits coe_diagUnits)
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.SiegelConj

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]

def scal (s : ℝ) : Ad E := 1 - GlobalTheory.CuspRep.sInf E 1 + GlobalTheory.CuspRep.sInf E (fun _ => (s : ℂ))

variable {E}

variable {n : ℕ}

def cell (S : Set (GA E n)) (R : ℝ) : Set (Matrix (Fin n) (Fin n) (Ad E)) :=
  (fun q : GA E n × (Fin n → Fin n → ℝ) =>
    Matrix.of fun i j => (q.1 : Matrix (Fin n) (Fin n) (Ad E)) i j * scal E (q.2 i j)) ''
    (S ×ˢ Set.univ.pi fun _ => Set.univ.pi fun _ => Set.Icc 0 R)

end GlobalTheory.CompanionTheory.SiegelConj

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspFormConjugateInverseStatement
section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_conjugate_inverse : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}, ∀ (φ : Sm E a) (hψ : (fun g => star (φ.1 (invA E a g))) ∈ Sm E a), IsCuspForm φ → IsCuspForm (⟨fun g => star (φ.1 (invA E a g)), hψ⟩ : Sm E a) := by
  first | exact @GlobalTheory.CompanionTheory.DualCusp.isCuspForm_conj_invA | exact GlobalTheory.CompanionTheory.DualCusp.isCuspForm_conj_invA | (intros; apply GlobalTheory.CompanionTheory.DualCusp.isCuspForm_conj_invA <;> assumption)
end

