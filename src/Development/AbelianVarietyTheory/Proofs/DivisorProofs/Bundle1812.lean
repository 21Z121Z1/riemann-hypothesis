import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1785
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0574
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharacterFockColumnSubstitutionEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0940
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0602
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0849
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0057
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1800
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPointIntegralFrameMemSpanEigenLattice
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

theorem GlobalTheory.PtDeg.intFrame_mem_span_eigLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (tt : 𝓞 E →+* 𝓞 K), (∀ a, ((tt a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ a)) → ∀ (u : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ u → ∀ (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → ∀ (ρV : 𝓞 K →+* T.V), (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∀ (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))), m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (a : T.Fr) (y' : FrPt Xo c T.Fr), FrChg C a yT y' → GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u → (∀ i, (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.eigLat B.t.act tt : Set (Fin F.P₀.g → K)))) := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ tt htt u hu 𝔓 T iK hiK ρV hρV
  letI := (iK.comp (algebraMap c.F K)).toAlgebra
  intro yT hyT G t' n n' m1' m2' h1 h2 C a y' hchg hint i
  obtain ⟨v', hv', hv'φ⟩ := GlobalTheory.T.exists_lieBasis_fibre_over_completion_fraction_field E H K B t₀ m2 F T iK t' n'
  obtain ⟨vV, hvV, hvVM⟩ := GlobalTheory.T.exists_lieBasis_completion_in_span_lieLattice E H K B F 𝔓 T iK hiK ρV hρV G n
  choose M w hMw hMn hMspan using hvVM
  obtain ⟨ub, hubT, -, -, hubu⟩ := hint
  obtain ⟨u', hu'1, hu'2⟩ := hubu ρ i
  obtain ⟨av, w₁, hw₁, hw₁c⟩ := GlobalTheory.T.genericFibre_integral_tangent_in_span_lieBasis E H K B t₀ m2 F T iK ρV hρV G t' n n' m2' h2 v' hv' hv'φ vV M hvV
    (fun k => ⟨w k, hMw k, hMn k⟩) (ub ρ i) u' (hubT ρ i) hu'2
  have hbase : u' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
    rw [← hw₁]; exact Over.w w₁
  obtain ⟨w₂, hw₂, hw₂c⟩ := GlobalTheory.T.framedPoint_genericFibre_coordinates_eq_frame E H Dw l Xo c K y B t₀ m1 m2 F ρ u hu T iK yT hyT t' n' m1' h1 v' hv'
    hv'φ C a y' hchg i u' hbase hu'1
  obtain rfl : w₁ = w₂ := Over.OverMorphism.ext (hw₁.trans hw₂.symm)
  have htan : IsTangent w₁ :=
    (GlobalTheory.LieComb.lieComb_algebra T.Fr t'.G _ v' hv'.1).2.1 _ _ hw₁c
  have heq := (hv'.2 w₁ htan).unique hw₁c hw₂c
  have hWlie : (∑ j, C ρ i j • fun k => iK (u j k)) ∈ Submodule.span T.V
      ((fun (v : Fin F.P₀.g → K) k => iK (v k)) '' (F.lieLat : Set (Fin F.P₀.g → K))) := by
    rw [← heq]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (hMspan k)
  obtain ⟨r', -, hr'⟩ := GlobalTheory.T.exists_lieRepresentation_eigenLattices K B.pol F (𝓞 E) B.t.act
  have hueig : ∀ j a, r' a (u j) = ((tt a : 𝓞 K) : K) • u j := by
    intro j a
    have := ((hr' tt (u j)).2).1 (GlobalTheory.T.framedPoint_coordinates_mem_span_eigenLattice E H Dw l Xo c K y B t₀ m1 m2 F ρ tt htt u hu j) a
    rw [this, ← algebraMap_smul K (tt a) (u j)]
  have hx := GlobalTheory.T.completed_span_eigen_vector_mem_eigen_sublattice K F.P₀.g F.lieLat (𝓞 E) (fun a => LinearMap.toMatrix' (r' a))
    (fun a => ((tt a : 𝓞 K) : K)) 𝔓 T iK hiK (GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K B.pol F).1 _ hWlie (fun a => by
      rw [Matrix.mulVec_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mulVec_smul, smul_comm]
      congr 1
      funext k
      rw [show (fun k => iK (u j k)) = iK ∘ u j from rfl, ← RingHom.map_mulVec, LinearMap.toMatrix'_mulVec, hueig j a]
      simp)
  refine Submodule.span_mono ?_ hx
  rintro _ ⟨c', ⟨hc1, hc2⟩, rfl⟩
  refine ⟨c', (hr' tt c').1.2 ⟨hc1, fun a => ?_⟩, rfl⟩
  have := hc2 a
  rw [LinearMap.toMatrix'_mulVec] at this
  rw [this, ← algebraMap_smul K (tt a) c']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnSubstitutionUnitaryOfKillsLieCoinvariants
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
noncomputable section

namespace GlobalTheory.LieInt

theorem exists_exp_unitary {a : ℕ} (u : Matrix.unitaryGroup (Fin a) ℂ) :
    ∃ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S ∧ NormedSpace.exp S = u := by
  have hJ : ReciprocityTheory.ChartRestriction.DS.Jm (fun _ : Fin a => true) = 1 := by
    simp [ReciprocityTheory.ChartRestriction.DS.Jm]
  obtain ⟨Z, ⟨hG, -⟩, hZ⟩ := ReciprocityTheory.ChartRestriction.DS.exists_exp_eq_of_mem_Kset (ε := fun _ : Fin a => true)
    (k := (u : Matrix (Fin a) (Fin a) ℂ)) ⟨u.2, by rw [hJ, Matrix.mul_one, Matrix.one_mul]⟩
  refine ⟨Z, ?_, hZ⟩
  unfold ReciprocityTheory.ChartRestriction.DS.inG at hG
  rw [hJ, Matrix.mul_one, Matrix.one_mul] at hG
  exact eq_neg_of_add_eq_zero_left hG

theorem colDer_neg {ι : Type} [DecidableEq ι] {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) :
    (GlobalTheory.ColLie.colDer (d := d) τ (-S)) = -GlobalTheory.ColLie.colDer τ S := by
  simp [GlobalTheory.ColLie.colDer, Finset.sum_neg_distrib, neg_smul]

theorem trace_map_conj {a : ℕ} (S : Matrix (Fin a) (Fin a) ℂ) (hS : S.conjTranspose = -S) :
    (S.map (starRingEnd ℂ)).trace = -S.trace := by
  have h : (S.map (starRingEnd ℂ)).trace = S.conjTranspose.trace := by
    simp [Matrix.trace, Matrix.diag, Matrix.conjTranspose_apply]
  rw [h, hS, Matrix.trace_neg]

theorem act_eq (D : D7) (ε : Bool) (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X)
    (eT : D.what₂.Tau → ℚ) (n₀ : D.what₂.Tau → ℕ) (hA : ∀ τ j, A.ε τ j = true) (hB : ∀ τ i, B.ε τ i = true)
    (hn : ∀ τ, (n₀ τ : ℚ) = (if ε then eT τ else -eT τ) - (X.rank : ℚ) / 2) (τ : D.what₂.Tau)
    (S : Matrix (Fin M.rank) (Fin M.rank) ℂ) (hS : S.conjTranspose = -S) :
    ∃ Z ∈ lieAt M τ, GlobalTheory.RealQuot.actS ε A B eT τ Z =
      GlobalTheory.ColLie.colDer τ S - (((n₀ τ : ℕ) : ℂ) * S.trace) • (1 : Module.End ℂ (PolF D X.rank M.rank)) := by
  classical
  set F := A.fr τ with hF
  have hFu : IsUnit F := A.fr_unit τ
  have hFd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).1 hFu
  have hFFi : F * F⁻¹ = 1 := Matrix.mul_nonsing_inv F hFd
  have hFiF : F⁻¹ * F = 1 := Matrix.nonsing_inv_mul F hFd
  have hJ : Formalism.REAL.Jm (A.ε τ) = 1 := by
    ext i j
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply, hA τ]
  have hG : gramAt D M τ = F.conjTranspose * F := by
    rw [← A.fr_gram τ, hJ, Matrix.mul_one]
  set Zf : Matrix (Fin M.rank) (Fin M.rank) ℂ := if ε then S else S.map (starRingEnd ℂ) with hZf
  have hZfs : Zf.conjTranspose = -Zf := by
    rcases ε with _ | _
    · simp only [hZf, if_false, Bool.false_eq_true]
      ext i j
      have := congrFun (congrFun hS j) i
      simp [Matrix.conjTranspose_apply] at this ⊢
      rw [this, neg_neg]
    · simpa [hZf] using hS
  refine ⟨F⁻¹ * Zf * F, ?_, ?_⟩
  · show (F⁻¹ * Zf * F).conjTranspose * gramAt D M τ + gramAt D M τ * (F⁻¹ * Zf * F) = 0
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hZfs]
    have h1 : (F⁻¹).conjTranspose * F.conjTranspose = 1 := by
      rw [← Matrix.conjTranspose_mul, hFFi, Matrix.conjTranspose_one]
    calc _ = F.conjTranspose * -Zf * ((F⁻¹).conjTranspose * F.conjTranspose) * F +
          F.conjTranspose * (F * F⁻¹) * Zf * F := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h1, hFFi]; simp [Matrix.mul_neg, Matrix.neg_mul]
  · have hconj : F * (F⁻¹ * Zf * F) * F⁻¹ = Zf := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hFFi, Matrix.one_mul, Matrix.mul_assoc, hFFi, Matrix.mul_one]
    have htr : (F⁻¹ * Zf * F).trace = Zf.trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hFFi, Matrix.one_mul]
    have hsg : (GlobalTheory.SquareComm.frSgn ε A).ε τ = fun _ => !ε := by
      funext j
      simp [GlobalTheory.SquareComm.frSgn, hA τ j]
    have hn' : ((n₀ τ : ℕ) : ℂ) = (((if ε then eT τ else -eT τ) : ℚ) : ℂ) - (X.rank : ℂ) / 2 := by
      have := congrArg (fun x : ℚ => (x : ℂ)) (hn τ)
      push_cast at this ⊢
      exact this
    unfold GlobalTheory.RealQuot.actS
    rw [hsg, hconj, htr]
    rcases ε with _ | _
    · have h2 := GlobalTheory.T.fockSourceGlActionSymmetrised_same_signs (D := D) τ (fun _ : Fin M.rank => !false) (B.ε τ) (Zf.map (starRingEnd ℂ))
        (fun i j => by simp [hB τ i])
      rw [h2]
      have hY : Zf.map (starRingEnd ℂ) = S := by
        ext i j
        simp [hZf]
      have hZt : Zf.trace = -S.trace := by
        simp only [hZf, Bool.false_eq_true, if_false]
        exact trace_map_conj S hS
      rw [hY, hZt, hn']
      simp only [Bool.false_eq_true, if_false]
      push_cast
      module
    · have h1 := GlobalTheory.T.fockSourceGlActionSymmetrised_opposite_signs (D := D) τ (fun _ : Fin M.rank => !true) (B.ε τ) (Zf.map (starRingEnd ℂ))
        (fun i j => by simp [hB τ i])
      rw [h1]
      have hY : (Zf.map (starRingEnd ℂ)).transpose = -S := by
        rw [← hS]
        ext i j
        simp [hZf, Matrix.conjTranspose_apply]
      have hYt : (Zf.map (starRingEnd ℂ)).trace = -S.trace := by
        simp only [hZf, if_true]
        exact trace_map_conj S hS
      have hZt : Zf.trace = S.trace := by simp [hZf]
      rw [hY, hYt, hZt, hn', colDer_neg]
      simp only [if_true]
      push_cast
      module

theorem colSub_unitary_of_coinv : ∀ (D : D7) (ε : Bool) (M X : HSp D) (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) (eT : D.what₂.Tau → ℚ)
    (n₀ : D.what₂.Tau → ℕ) (Q : Type) [AddCommGroup Q] [Module ℂ Q] (q : PolF D X.rank M.rank →ₗ[ℂ] Q),
    (∀ τ j, A.ε τ j = true) → (∀ τ i, B.ε τ i = true) →
    (∀ τ, (n₀ τ : ℚ) = (if ε then eT τ else -eT τ) - (X.rank : ℚ) / 2) →
    GlobalTheory.RealQuot.coinv ε A B eT ≤ LinearMap.ker q →
    ∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin M.rank) ℂ) (P : PolF D X.rank M.rank),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ)) • q P := by
  intro D ε M X A B eT n₀ Q _ _ q hA hB hn hker
  have hS : ∀ τ (S : Matrix (Fin M.rank) (Fin M.rank) ℂ), S.conjTranspose = -S → ∀ P : PolF D X.rank M.rank,
      q (GlobalTheory.ColLie.colDer τ S P) = (((n₀ τ : ℕ) : ℂ) * S.trace) • q P := by
    intro τ S hS P
    obtain ⟨Z, hZ, he⟩ := act_eq D ε M X A B eT n₀ hA hB hn τ S hS
    have hmem : GlobalTheory.RealQuot.actS ε A B eT τ Z P ∈ GlobalTheory.RealQuot.coinv ε A B eT :=
      Submodule.subset_span ⟨τ, Z, hZ, P, rfl⟩
    have h0 := hker hmem
    rw [LinearMap.mem_ker, he, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul,
      sub_eq_zero] at h0
    exact h0
  have h1 : ∀ τ (u : Matrix.unitaryGroup (Fin M.rank) ℂ) (P : PolF D X.rank M.rank),
      q (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (u : Matrix (Fin M.rank) (Fin M.rank) ℂ)) P) =
        ((u : Matrix (Fin M.rank) (Fin M.rank) ℂ).det ^ n₀ τ) • q P := by
    intro τ u P
    obtain ⟨S, hS', he⟩ := exists_exp_unitary u
    rw [← he]
    exact GlobalTheory.T.fockColumnSubstitution_exp_of_columnDerivation _ _ τ (n₀ τ) Q q (GlobalTheory.T.hasDerivAt_coeff_fockColumnSubstitution_exp _ _ τ) (hS τ) S hS' P
  intro g P
  have key : ∀ s : Finset D.what₂.Tau, ∀ P : PolF D X.rank M.rank,
      q (GlobalTheory.MinorFrame.colSub (fun τ => if τ ∈ s then (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ) else 1) P) =
        (∏ τ ∈ s, (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ).det ^ n₀ τ) • q P := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro P
      simp only [Finset.notMem_empty, if_false, Finset.prod_empty, one_smul]
      rw [GlobalTheory.MinorFrame.colSub_one, AlgHom.id_apply]
    | insert τ s hτ ih =>
      intro P
      have hsplit : (fun σ => if σ ∈ insert τ s then (g σ : Matrix (Fin M.rank) (Fin M.rank) ℂ) else 1) =
          fun σ => GlobalTheory.ColLie.atPl τ (g τ : Matrix (Fin M.rank) (Fin M.rank) ℂ) σ *
            (if σ ∈ s then (g σ : Matrix (Fin M.rank) (Fin M.rank) ℂ) else 1) := by
        funext σ
        by_cases h : σ = τ
        · subst h
          simp [GlobalTheory.ColLie.atPl, hτ]
        · simp [GlobalTheory.ColLie.atPl, h, Function.update_of_ne h]
      rw [hsplit, GlobalTheory.MinorFrame.colSub_mul, h1, ih, smul_smul, Finset.prod_insert hτ]
  have := key Finset.univ P
  simp only [Finset.mem_univ, if_true] at this
  rw [this]
  rfl

end GlobalTheory.LieInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjPlInvolutive
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat

namespace GlobalTheory.SumSize.OppConj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coef

variable {ι : Type} [Fintype ι] {n : ℕ}

def mapF {K L : Type} [Field K] [Field L] (φ : K →+* L) (lam : ι → DomWeight n) (x : VV K lam) : VV L lam :=
  ⟨MvPolynomial.map φ x.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ lam _ x.2⟩

theorem mapVV_mapF {K L : Type} [Field K] [Field L] (φ : K →+* L) (ψ : L →+* ℂ) (lam : ι → DomWeight n) (x : VV K lam) :
    GlobalTheory.CoefModel.mapVV ψ lam (mapF φ lam x) = GlobalTheory.CoefModel.mapVV (ψ.comp φ) lam x :=
  Subtype.ext (by
    change MvPolynomial.map ψ (MvPolynomial.map φ x.1) = MvPolynomial.map (ψ.comp φ) x.1
    rw [MvPolynomial.map_map])

theorem mapVV_mapVV {K : Type} [Field K] (φ : K →+* ℂ) (ψ : ℂ →+* ℂ) (lam : ι → DomWeight n) (x : VV K lam) :
    GlobalTheory.CoefModel.mapVV ψ lam (GlobalTheory.CoefModel.mapVV φ lam x) = GlobalTheory.CoefModel.mapVV (ψ.comp φ) lam x :=
  Subtype.ext (by
    change MvPolynomial.map ψ (MvPolynomial.map φ x.1) = MvPolynomial.map (ψ.comp φ) x.1
    rw [MvPolynomial.map_map])

theorem mapVV_id (lam : ι → DomWeight n) (v : VV ℂ lam) : GlobalTheory.CoefModel.mapVV (RingHom.id ℂ) lam v = v :=
  Subtype.ext (by
    change MvPolynomial.map (RingHom.id ℂ) v.1 = v.1
    rw [MvPolynomial.map_id])

theorem conj_comp_conj : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ :=
  RingHom.ext fun z => Complex.conj_conj z

theorem mapVV_conj_conj (lam : ι → DomWeight n) (v : VV ℂ lam) :
    GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam (GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam v) = v := by
  rw [mapVV_mapVV, conj_comp_conj, mapVV_id]

def conjMap {n' : ℕ} {lam : ι → DomWeight n} {lam' : ι → DomWeight n'} (K : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (v : VV ℂ lam) : VV ℂ lam' :=
  GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam' (K (GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam v))

end Coef

section Places

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def conjPl (q : InfinitePlace K) : InfinitePlace K := InfinitePlace.mk (q.embedding.comp (starRingEnd K))

variable {K}

theorem conjugate_comp (φ : K →+* ℂ) (f : K →+* K) :
    (ComplexEmbedding.conjugate φ).comp f = ComplexEmbedding.conjugate (φ.comp f) :=
  RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]

theorem conjPl_mk (φ : K →+* ℂ) : conjPl K (InfinitePlace.mk φ) = InfinitePlace.mk (φ.comp (starRingEnd K)) := by
  unfold conjPl
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h, conjugate_comp, InfinitePlace.mk_conjugate_eq]

theorem star_comp_star : (starRingEnd K).comp (starRingEnd K) = RingHom.id K :=
  RingHom.ext fun x => by simp

theorem conjPl_conjPl (q : InfinitePlace K) : conjPl K (conjPl K q) = q := by
  change conjPl K (InfinitePlace.mk (q.embedding.comp (starRingEnd K))) = q
  rw [conjPl_mk, RingHom.comp_assoc, star_comp_star, RingHom.comp_id, InfinitePlace.mk_embedding]

theorem conjPl_involutive : Function.Involutive (conjPl K) := conjPl_conjPl

theorem meanInf_conjPl (g : InfinitePlace K → ℝ) : Formalism.PairingDivisionLocalBalance.meanInf K (fun q => g (conjPl K q)) = Formalism.PairingDivisionLocalBalance.meanInf K g := by
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  congr 1
  exact Equiv.sum_comp (conjPl_involutive.toPerm _) g

end Places

section Nrm

variable {D : D7} {n : ℕ} (lam : D.what₂.Tau → DomWeight n)

theorem nrm_conj (v : VV ℂ lam) :
    nrm lam (fun _ => 1) (GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam v) = nrm lam (fun _ => 1) v := by
  have h := GlobalTheory.CoefModel.pairK_mapVV (starRingEnd ℂ) lam (fun _ => rfl) (fun _ : D.what₂.Tau => (1 : Matrix (Fin n) (Fin n) ℂ)) v v
  simp only [Matrix.map_one _ (map_zero _) (map_one _)] at h
  simp only [nrm, h, Complex.conj_re]

theorem nrmLe_conj_iff (σ : D.what₂.LL →+* ℂ) (v : VV ℂ lam) (B : ℝ) :
    NrmLe lam ((starRingEnd ℂ).comp σ) v B ↔ NrmLe lam σ v B := by
  constructor
  · rintro ⟨u, hu, hB⟩
    refine ⟨u, hu, ?_⟩
    rwa [← mapVV_mapVV, nrm_conj] at hB
  · rintro ⟨u, hu, hB⟩
    refine ⟨u, hu, ?_⟩
    rwa [← mapVV_mapVV, nrm_conj]

theorem nrmLe_mk_iff (φ : D.what₂.LL →+* ℂ) (v : VV ℂ lam) (B : ℝ) :
    NrmLe lam (InfinitePlace.mk φ).embedding v B ↔ NrmLe lam φ v B := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · have e : ComplexEmbedding.conjugate φ = (starRingEnd ℂ).comp φ :=
      RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
    rw [h, e, nrmLe_conj_iff]

end Nrm

section Transfer

variable {D : D7} {n n' : ℕ} {lam : D.what₂.Tau → DomWeight n} {lam' : D.what₂.Tau → DomWeight n'}

theorem embLL_comp_star : D.what₂.embLL.comp (starRingEnd D.what₂.LL) = (starRingEnd ℂ).comp D.what₂.embLL :=
  RingHom.ext fun x => D.starLL_cx x

theorem nrmLe_of_conjMap (σ : D.what₂.LL →+* ℂ) (K : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (c : ℝ)
    (h : ∀ B v, NrmLe lam (σ.comp (starRingEnd D.what₂.LL)) v B →
      NrmLe lam' (σ.comp (starRingEnd D.what₂.LL)) (conjMap K v) (c * B))
    (B : ℝ) (v : VV ℂ lam) (hv : NrmLe lam σ v B) : NrmLe lam' σ (K v) (c * B) := by
  obtain ⟨u, hu, hB⟩ := hv
  have h1 : NrmLe lam (σ.comp (starRingEnd D.what₂.LL)) (GlobalTheory.CoefModel.mapVV (starRingEnd ℂ) lam v) B := by
    refine ⟨mapF (starRingEnd D.what₂.LL) lam u, ?_, ?_⟩
    · rw [mapVV_mapF, embLL_comp_star, ← mapVV_mapVV, hu]
    · rwa [mapVV_mapF, RingHom.comp_assoc, star_comp_star, RingHom.comp_id]
  obtain ⟨u', hu', hB'⟩ := h B _ h1
  refine ⟨mapF (starRingEnd D.what₂.LL) lam' u', ?_, ?_⟩
  · rw [mapVV_mapF, embLL_comp_star, ← mapVV_mapVV, hu', conjMap, mapVV_conj_conj, mapVV_conj_conj]
  · rwa [mapVV_mapF]

end Transfer

section Std

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C b : ℝ)

def PairStdAt : Prop := ∃ g : InfinitePlace D.what₂.LL → ℝ, Formalism.PairingDivisionLocalBalance.meanInf _ g ≤ aOne ch.G C b ∧
  ∀ (p : InfinitePlace D.what₂.LL) Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β),
    (∀ (j : Fin D.R.m) B v, NrmLe _ p.embedding v B →
      NrmLe _ p.embedding (ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) v) (Real.exp (g p) * B)) ∧
    ∀ (i : Fin D.R.m) B v, NrmLe _ p.embedding v B →
      NrmLe _ p.embedding (conjMap (ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1))) v) (Real.exp (g p) * B)

theorem infRowAt_of (h : PairStdAt ch C b) : InfRowAt ch C b := by
  obtain ⟨g, hg, h⟩ := h
  refine ⟨fun p => g (conjPl _ p), by rwa [meanInf_conjPl], ?_⟩
  intro p Φ β d hO c i B v hv
  have key := (h (conjPl _ p) Φ β d hO c).2 i
  refine nrmLe_of_conjMap p.embedding _ _ (fun B' v' hv' => ?_) B v hv
  exact (nrmLe_mk_iff _ (p.embedding.comp (starRingEnd D.what₂.LL)) _ _).1
    (key B' v' ((nrmLe_mk_iff _ (p.embedding.comp (starRingEnd D.what₂.LL)) _ _).2 hv'))

end Std

def PairStdK : Prop := BigC fun _ ch C b => PairStdAt ch C b

theorem bigC_mono {Q Q' : ChQ} (h : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (F : Face D A) (ch : Choice R) (C b : ℝ),
    Q F ch C b → Q' F ch C b) : BigC Q → BigC Q' := by
  rintro ⟨CF0, h0⟩
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, h1⟩ := h0 CF hCF
  refine ⟨C0, fun ε C hC => ?_⟩
  obtain ⟨x0, h2⟩ := h1 ε C hC
  exact ⟨x0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h3 h4 h5 =>
    h F ch C large₂.sc.b (h2 D large₂ he hx Γ Pl0 T A Ks R F hS ch h3 h4 h5)⟩

theorem infRowK_of (h : PairStdK) : InfRowK := bigC_mono (fun _ ch C b => infRowAt_of ch C b) h

end GlobalTheory.SumSize.OppConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeilRepresentationThird
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

set_option maxHeartbeats 1000000 in

theorem integral_theta_chi {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (hL : ∀ k, k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β L ↔ k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β (Lev.flag1L L))
    (χ' : (levEnv S β L).J →* ℂˣ)
    {f : Bridge.Gf S → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J χ')
    (Λ : c.W →ₗ[ℂ] (WO S T → ℂ)) (hΛ : ∀ w, IsThetaFunO ψ S T (Λ w))
    (hΛa : ∀ a ∈ GinfC S, ∀ w, om (a, 1) (Λ w) = Λ (c.ρ a w))
    (hΛk : ∀ k ∈ GfC S, ∀ hk : fin S k ∈ (levEnv S β L).J, ∀ w,
      om (k, 1) (Λ w) = ((χ' ⟨fin S k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ w)
    {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : IsMeasDef S (Formalism.L2.DIV.lev D.sp.cm S.gram β L) ν 𝓕)
    (J' : Subgroup (Bridge.Gf S)) (Cl : Type) [Fintype Cl] (h : Cl → GA D S) (hle : J' ≤ (levEnv S β L).J)
    (hN : J'.relIndex (levEnv S β L).J ≠ 0) (hy : Bridge.IsReps (Bridge.ratF S) J' (fun k => fin S (h k)))
    (hh : ∀ k, h k ∈ GfC S) (g : GA D T) :
    ∫ x in 𝓕, thetaKO om x g (Λ (c.ext f x)) ∂ν = ∑ k, ((J'.relIndex (levEnv S β L).J : ℕ) : ℂ)⁻¹ *
      ((Nat.card (Bridge.stab (Bridge.ratF S) J' (fin S (h k))) : ℕ) : ℂ)⁻¹ * thetaKO om (h k) g (Λ (f (fin S (h k)))) := by
  rw [GlobalTheory.ClsInt.integral_eq_classSum_of_le D S β L ν 𝓕 hp hs hν hL J' Cl h hle hN hy hh
    (fun x => thetaKO om x g (Λ (c.ext f x))) ?_ ?_]
  · exact Finset.sum_congr rfl fun k _ => by rw [ext_fin c hc f (hh k)]
  · intro γ hγ x
    have e : (γ * x, g) = ((γ, 1) : GA D S × GA D T) * (x, g) := by rw [Prod.mk_mul_mk, one_mul]
    simp only [thetaKO]
    rw [GlobalTheory.ThetaIntegrand.ext_invariant c hf γ hγ, e, map_mul]
    exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ (hΛ _))
  · intro u hu x
    refine (GlobalTheory.LiftUnfold.exists_fin_mul_real S u).elim fun k hk0 => hk0.2.elim fun a ha0 => ?_
    have hk := hk0.1
    have ha := ha0.1
    have e := ha0.2.2
    have hk' : fin S k ∈ (levEnv S β L).J := by rw [e]; exact hu
    have h1 : c.ρ k⁻¹ = 1 := hc.1 _ (inv_mem hk)
    have h2 : (finHom S).rangeRestrict a = 1 := Subtype.ext (MonoidHom.mem_ker.1 ha)
    have h3 := GlobalTheory.LiftUnfold.form_right (Bridge.ratF S) c.coef.ρ hf ⟨fin S k, hk'⟩
    have h4 := GlobalTheory.LiftUnfold.integrand_right om c.ρ (finHom S).rangeRestrict Λ f u k a ha0.2.1 (χ' ⟨fin S k, hk'⟩)
      h1 h2 h3 (hΛk k hk hk') (hΛa a ha) x g
    exact congrFun h4 0

end GlobalTheory.GalOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormAdelicFunctionsEqModelValuesSemilinearStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormAdelicFunctions_eq_modelValues_semilinear : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → JEvExists T R κ v₀ := by
  first | exact @GlobalTheory.CuspFormValues.jEvExists | exact GlobalTheory.CuspFormValues.jEvExists | (intros; apply GlobalTheory.CuspFormValues.jEvExists <;> assumption)
end

