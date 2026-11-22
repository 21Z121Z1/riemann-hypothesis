import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0469
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0388
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0343
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0406
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0154
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0160
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0468
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0470
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0471
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0472
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0462
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0473
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0358

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitFramePrincipalLevelFiniteGroup
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
namespace GlobalTheory.TrPtFrame

theorem finLoc_locFin_ne {D : D7} (V : HSp D) {u v : HeightOneSpectrum (𝓞 D.host.F)} (h : u ≠ v) (x : Gv V v) :
    finLoc V u (locFin V v x) = 1 := by
  show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram u ((locFin V v x : GfC V) : GA D V) = 1
  rw [coe_locFin]
  exact GlobalTheory.AdelicU.proj_emb_ne _ _ h x

theorem mem_parLev {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    (L : LevDat D.host.E ℂ V.rank) (h : L.r = V.rank) (hQ : L.Q = ∅) {x : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    (hU : x ∈ UA D.sp.cm V.gram) (hS : x ∈ St β) : x ∈ parLev D.sp.cm V.gram β L := by
  rw [Formalism.L2.DIV.mem_parLev]
  refine ⟨hU, hS, fun PP _ => ?_, fun PP hP => ?_⟩
  · rw [Formalism.L2.DIV.mem_blockTri]
    intro i j hij
    exfalso
    simp [Formalism.L2.DIV.blkOf, h] at hij
  · exfalso
    simp [hQ] at hP

theorem upperLeftBlock_apply_of_eq {D : D7} {n r : ℕ} (hr : r ≤ n) (h : r = n) (PP : Pl D.host.E) (g : GL (Fin n) (kP PP)) (i j : Fin r) :
    ((upperLeftBlock hr g : GL (Fin r) (kP PP)) : Matrix (Fin r) (Fin r) (kP PP)) i j = (g : Matrix (Fin n) (Fin n) (kP PP)) (i.cast h) (j.cast h) := by
  subst h
  have hm : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
    rw [Formalism.L2.DIV.mem_blockTri]
    intro a b hab
    exfalso
    simp [Formalism.L2.DIV.blk2] at hab
  rw [Formalism.L2.DIV.upper_block_val_submatrix hr hm, Matrix.submatrix_apply]
  rfl

private theorem finLoc_locFin' {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (x : Gv V v) :
    finLoc V v (locFin V v x) = x := by
  show GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v ((locFin V v x : GfC V) : GA D V) = x
  rw [coe_locFin]
  exact GlobalTheory.AdelicU.proj_emb_self _ _ v x

private theorem upperLeftBlock_one {D : D7} {n r : ℕ} (hr : r ≤ n) (PP : Pl D.host.E) :
    (upperLeftBlock hr (1 : GL (Fin n) (kP PP)) : GL (Fin r) (kP PP)) = 1 :=
  Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one (Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) (Formalism.L2.DIV.blkR hr)

theorem exists_splitFrame_levG : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank) (h : L.r = V.rank), IsBaseFrame V β Λ N → L.Q = ∅ → (∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP') → ∃ (a : GfC V) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ L.Pg) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v) (ρ : ∀ v : S, ResF v.1 ≃+* kP (pl v).1), (∀ v ∉ S, ∀ k ∈ Kv V v, ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ levG V β (flag1L L)) ∧ ∀ (v : S) (k : Kv V v), ∃ g0 : G0 L.Pg L.r, IsLevelLift V β L g0 ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∧ (∀ PP, PP ≠ pl v → g0 PP = 1) ∧ ∀ i j : Fin L.r, (g0 (pl v)).1 i j = ρ v (((s v).red k).1 (i.cast h) (j.cast h)) := by
  intro D V β Λ N L h hB hQ hPg
  classical
  obtain ⟨a, hLat, hSt⟩ := GlobalTheory.FramePointMove.exists_point_carrying_frameLat D V β Λ N hB

  have hStk : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (k : Gv V v), k ∈ Kv V v →
      finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ St β := by
    intro v k hk
    refine (hSt (locFin V v k)).2 fun u => ?_
    by_cases huv : u = v
    · subst huv
      rw [finLoc_locFin']
      exact hk
    · rw [finLoc_locFin_ne V huv k]
      exact Subgroup.one_mem _

  have hinj : ∀ PP ∈ L.Pg, ∀ PP' ∈ L.Pg, PP.under (𝓞 D.host.F) = PP'.under (𝓞 D.host.F) → PP = PP' := by
    intro PP hP PP' hP' he
    by_contra hne
    exact hPg PP hP PP' hP' (GlobalTheory.UnderConj.isConjPl_of_under_eq_of_ne D PP PP' he hne)
  let S : Finset (HeightOneSpectrum (𝓞 D.host.F)) := L.Pg.image fun PP => PP.under (𝓞 D.host.F)
  let f : L.Pg → S := fun PP => ⟨PP.1.under (𝓞 D.host.F), Finset.mem_image_of_mem _ PP.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro PP PP' he
      exact Subtype.ext (hinj _ PP.2 _ PP'.2 (congrArg Subtype.val he))
    · intro v
      obtain ⟨PP, hP, he⟩ := Finset.mem_image.1 v.2
      exact ⟨⟨PP, hP⟩, Subtype.ext he⟩
  let pl : S ≃ L.Pg := (Equiv.ofBijective f hf).symm
  have hunder : ∀ v : S, (pl v).1.under (𝓞 D.host.F) = v.1 := fun v =>
    congrArg Subtype.val ((Equiv.ofBijective f hf).apply_symm_apply v)
  choose s ρ hsρ using fun v : S =>
    GlobalTheory.SplitPlaceRed.splitRed_frame D V β Λ N a hB hLat v.1 (pl v).1 (hunder v)
      (hPg _ (pl v).2 _ (pl v).2) (fun k => hStk v.1 k.1 k.2)
  refine ⟨a, S, pl, s, ρ, ?_, ?_⟩
  · intro v hv k hk
    have hx := hStk v k hk
    rw [Formalism.IndefR.Lev.levG, Formalism.IndefR.Lev.mem_levA]
    refine ⟨(a * locFin V v k * a⁻¹ : GfC V).2, ?_⟩
    rw [Formalism.L2.DIV.mem_lev]
    refine ⟨mem_parLev (flag1L L) h hQ (GlobalTheory.LevSplit.finE_mem_UA V _) hx, ?_⟩
    have hone : ∀ PP ∈ L.Pg, redFn β PP (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V)) = 1 := by
      intro PP hP
      refine GlobalTheory.PlaceAwayRed.redFn_conj_locFin_eq_one D V β a v PP (fun he => hv ?_) k hx
      rw [← he]
      exact Finset.mem_image_of_mem _ hP
    have hrt : rTup β (flag1L L) (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V)) = rTup β (flag1L L) 1 := by
      funext PP
      simp only [Formalism.L2.DIV.rTup]
      rw [hone PP.1 PP.2, Formalism.L2.DIV.redFn_one]
    rw [hrt, Formalism.L2.DIV.rTup_one]
    exact Subgroup.one_mem _
  · intro v k
    have hx := hStk v.1 k.1 k.2
    refine ⟨rTup β L (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V)),
      ⟨(a * locFin V v k * a⁻¹ : GfC V).2, mem_parLev L h hQ (GlobalTheory.LevSplit.finE_mem_UA V _) hx, rfl⟩, ?_, ?_⟩
    · intro PP hne
      have hu : PP.1.under (𝓞 D.host.F) ≠ v.1 := by
        intro he
        exact hne (Subtype.ext (hinj _ PP.2 _ (pl v).2 (he.trans (hunder v).symm)))
      show upperLeftBlock L.hr (redFn β PP.1 (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V))) = 1
      rw [GlobalTheory.PlaceAwayRed.redFn_conj_locFin_eq_one D V β a v.1 PP.1 hu k.1 hx]
      exact upperLeftBlock_one L.hr PP.1
    · intro i j
      show ((upperLeftBlock L.hr (redFn β (pl v).1 (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V))) :
        GL (Fin L.r) (kP (pl v).1)) : Matrix (Fin L.r) (Fin L.r) (kP (pl v).1)) i j = _
      rw [upperLeftBlock_apply_of_eq L.hr h]
      exact hsρ v k (i.cast h) (j.cast h)

end GlobalTheory.TrPtFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTestGridFromLevelChoiceGrid
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

section Cast

variable {D : D7}

def hermitianOrthogonalExtensionDataCast {A A' B B' : GlobalTheory.Grid.Node D} {c : ℕ} (hA : A = A') (hB : B = B') (d : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c) :
    GlobalTheory.Grid.HermitianOrthogonalExtensionData A' B' c := hA ▸ hB ▸ d

theorem gridDecompositionCast_is_iff {A A' B B' : GlobalTheory.Grid.Node D} {c : ℕ} (hA : A = A') (hB : B = B') (d : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c)
    (g : Fin c → Fin c → D.host.E) (𝔟 : Fin c → GlobalTheory.Grid.FrId D) : (hermitianOrthogonalExtensionDataCast hA hB d).Is g 𝔟 ↔ d.Is g 𝔟 := by
  subst hA hB; rfl

def hermitianOrthogonalExtensionDataZero (A B : GlobalTheory.Grid.Node D) (c : ℕ) : GlobalTheory.Grid.HermitianOrthogonalExtensionData A B c := ⟨0, 0⟩

theorem joinStair {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : GlobalTheory.ChiGrid.Consts) (c : ℕ) :
    GlobalTheory.ChiGrid.stairId (P.stA sc) (P.stAbar sc) c = GlobalTheory.Grid.staircaseExtensionIdeal (P.modul sc) c := by
  funext p
  simp only [GlobalTheory.ChiGrid.stairId, GlobalTheory.ChiGrid.Places.stA, GlobalTheory.ChiGrid.Places.stAbar, GlobalTheory.ChiGrid.Places.modulBar,
    GlobalTheory.Grid.staircaseExtensionIdeal, mul_pow, inv_pow, mul_inv, inv_inv]

theorem joinStair_top (c : ℕ) :
    GlobalTheory.ChiGrid.stairId D.host.AA D.host.AAbar c = GlobalTheory.Grid.staircaseExtensionIdeal (D := D) ⊤ c := by
  funext p
  simp [GlobalTheory.ChiGrid.stairId, GlobalTheory.Grid.staircaseExtensionIdeal, Ideal.pointwise_smul_def, Ideal.map_top, mul_pow, inv_pow]

theorem joinGram_one : (fun p q : Fin 1 => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix 1 (1 : D.host.E) p q) = fun _ _ => 1 := by
  funext p q
  fin_cases p; fin_cases q; simp [GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix]

theorem joinGram_neg (c : ℕ) : (fun p q : Fin c => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix c (-1 : D.host.E) p q) = GlobalTheory.Grid.antiDiagonalSignGramMatrix D.host.E c := by
  funext p q
  rfl

end Cast

theorem exists_gridPre_spaces : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesUpqExists → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → (∀ X : GlobalTheory.ChiGrid.Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → (G'.Λ X : Set _) = L0c D (G'.V X)) → (∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, PP.under (𝓞 D.host.F) = PP'.under (𝓞 D.host.F) → PP = PP') → Formalism.L2.Host.SplitsCompletely {G'.pl.w G'.pl.v0} → (∀ k, GlobalTheory.ChiGrid.q0 D ≠ D.host.g k) → (GlobalTheory.ChiGrid.q0 D ≠ D.sp.T ∧ ∀ u : D.what₂.Word, GlobalTheory.ChiGrid.q0 D ≠ (D.mem u).A.T) → (∀ i j, 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.grid i j)).rank → ℝ) (ε : Fin (G'.V (.grid i j)).rank → Bool), IsEnum (GlobalTheory.Grid.parV D i j τ) lam ε ∧ (W.onb (.grid i j) τ)ᴴ * gramAt D (G'.V (.grid i j)) τ * W.onb (.grid i j) τ = Formalism.REAL.Jm ε) → (∀ i, i ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.core i)).rank → ℝ) (ε : Fin (G'.V (.core i)).rank → Bool), IsEnum (GlobalTheory.Grid.parP D i τ) lam ε ∧ (W.onb (.core i) τ)ᴴ * gramAt D (G'.V (.core i)) τ * W.onb (.core i) τ = Formalism.REAL.Jm ε) → (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.top j)).rank → ℝ) (ε : Fin (G'.V (.top j)).rank → Bool), IsEnum (GlobalTheory.Grid.parXp D j τ) lam ε ∧ (W.onb (.top j) τ)ᴴ * gramAt D (G'.V (.top j)) τ * W.onb (.top j) τ = Formalism.REAL.Jm ε) → W.cart (.top 0) = W.cart (.core D.R.m) → W.onb (.top 0) = W.onb (.core D.R.m) → ∀ e : AE D, IsIdemSum e G'.pl.W0 → ∃ G : GlobalTheory.Grid.GridPre R, G.idem = e ∧ G.IsSpaces ∧ G.IsChars ∧ SpAgree G W := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDS hH F hR hsc G' W hW hL hPg hsplit hg hT hOV hOP hOX hcT hoT e he
  classical
  obtain ⟨Z, hZ, hq0, hw0, he0, hWZ, hlvl, hS0, hS1⟩ := GlobalTheory.T.testGridPlaceData_of_levelChoiceGrid hR hPg hsplit hg hT e he
  let Sx : GlobalTheory.ChiGrid.Node → D.what₂.Tau → SPar := fun X => match X with
    | .grid i j => GlobalTheory.Grid.parV D i j
    | .core i => GlobalTheory.Grid.parP D i
    | .top j => GlobalTheory.Grid.parXp D j
  let good : GlobalTheory.ChiGrid.Node → Prop := fun X => match X with
    | .grid i j => 1 ≤ i ∧ i ≤ D.R.m ∧ j ≤ D.R.m
    | .core i => i ≤ D.R.m
    | .top j => 1 ≤ j ∧ j ≤ D.R.m
  have hgood : ∀ X, good X → X.InRange D.R.m ∧ ∀ j, X ≠ .grid 0 j := by
    intro X hX
    rcases X with ⟨i, j⟩ | i | j
    · exact ⟨⟨hX.2.1, hX.2.2⟩, fun j' h => by cases h; exact absurd hX.1 (by omega)⟩
    · exact ⟨hX, fun j' h => GlobalTheory.ChiGrid.Node.noConfusion h⟩
    · exact ⟨hX.2, fun j' h => GlobalTheory.ChiGrid.Node.noConfusion h⟩
  have hMod : ∀ X, good X → ∃ M : DSModel (G'.V X) (Sx X), cart M = W.cart X ∧ onb M = W.onb X := by
    intro X hX
    have hv := G'.isV (hgood X hX).1 (hgood X hX).2
    refine GlobalTheory.T.exists_discreteSeriesModel_of_orthonormalBasis_cartan D hDS (G'.V X) (Sx X) (W.onb X) (W.cart X) ?_ (W.onb_is X (hgood X hX).1)
    intro τ
    rcases X with ⟨i, j⟩ | i | j
    · obtain ⟨lam, ε, h1, h2⟩ := hOV i j hX.1 hX.2.1 hX.2.2 τ
      exact ⟨lam, ε, h1, GlobalTheory.T.isHarishChandraParam_gridVertexRealParameter D hH i j hX.1 hX.2.1 hX.2.2 τ _ lam ε hv.rank h1, h2⟩
    · obtain ⟨lam, ε, h1, h2⟩ := hOP i hX τ
      exact ⟨lam, ε, h1, GlobalTheory.T.isHarishChandraParam_gridColumnRealParameter D hH i hX τ _ lam ε hv.rank h1, h2⟩
    · obtain ⟨lam, ε, h1, h2⟩ := hOX j hX.1 hX.2 τ
      exact ⟨lam, ε, h1, GlobalTheory.T.isHarishChandraParam_gridRowRealParameter D hH j hX.1 hX.2 τ _ lam ε hv.rank h1, h2⟩
  have hFr : ∀ X, good X → ∃ β, IsSDFrame (G'.V X) β (G'.Λ X) 1 := fun X hX =>
    GlobalTheory.T.exists_selfDual_frame_of_standard_selfDual_lattice D _ _ (hL X (hgood X hX).1 (hgood X hX).2) (G'.isV (hgood X hX).1 (hgood X hX).2).sd
  choose M hM using hMod
  choose β hβ using hFr
  let mk : ∀ X, good X → GlobalTheory.Grid.Node D := fun X h => ⟨G'.V X, Sx X, M X h, G'.Λ X, β X h⟩
  let node : GlobalTheory.ChiGrid.Node → GlobalTheory.Grid.Node D := fun X => if h : good X then mk X h else GlobalTheory.Grid.row0 R 0
  have node_pos : ∀ X (h : good X), node X = mk X h := fun X h => dif_pos h
  have mk_is : ∀ X (h : good X), (mk X h).Is (X.rank D) (X.neg D.R.m) (Sx X) := fun X h => by
    have hv := G'.isV (hgood X h).1 (hgood X h).2
    exact ⟨hv.rank, hv.sigOK, hv.sig, rfl, hβ X h⟩
  have mk_agree : ∀ X (h : good X), NodeAgree (mk X h) W X := fun X h =>
    ⟨rfl, HEq.rfl, heq_of_eq (hM X h).1, heq_of_eq (hM X h).2⟩
  let GS : GlobalTheory.Grid.GridSp D :=
    { toPlaceDat := Z, nV := fun i j => node (.grid (i + 1) j), P := fun i => node (.core i), nX := fun j => node (.top (j + 1)) }
  have vert_eq : ∀ n x, 1 ≤ n → GS.vert R n x = node (.grid n x) := by
    intro n x hn
    cases n with
    | zero => omega
    | succ n => rfl
  have Xp_eq : ∀ n, 1 ≤ n → GS.Xp n = node (.top n) := by
    intro n hn
    cases n with
    | zero => omega
    | succ n => rfl
  have gP : ∀ i, i ≤ D.R.m → good (.core i) := fun i h => h
  have gV : ∀ i j, 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → good (.grid i j) := fun i j h1 h2 h3 => ⟨h1, h2, h3⟩
  have gX : ∀ j, 1 ≤ j → j ≤ D.R.m → good (.top j) := fun j h1 h2 => ⟨h1, h2⟩
  have hm2 := D.R.two_le_m

  obtain ⟨dP, -, hdP⟩ := GlobalTheory.T.exists_extensionData_antiDiagonalSignGram_of_lat_eq (GlobalTheory.Grid.row0 R 0) (mk (.core 0) (gP 0 (by omega))) G'.sp.dec0 (fun _ => 1) (Or.inl rfl)
    G'.sp.lat0

  have exV : ∀ i (h : 1 ≤ i ∧ i ≤ D.R.m), ∃ d : GlobalTheory.Grid.HermitianOrthogonalExtensionData (mk (.core i) (gP i h.2)) (mk (.grid i 0) (gV i 0 h.1 h.2 (by omega))) (i - 1),
      d.Is (fun p q => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix (i - 1) (-1 : D.host.E) p q) (GlobalTheory.ChiGrid.stairId (G'.pl.stA sc) (G'.pl.stAbar sc) (i - 1)) :=
    fun i h => (GlobalTheory.T.exists_extensionData_antiDiagonalSignGram_of_lat_eq _ _ (G'.sp.colDec i h.1 h.2) _ (Or.inr rfl) (G'.sp.colLat i h.1 h.2)).imp fun _ h => h.2
  choose dV hdV using exV

  have exX : ∀ j (h : j + 1 < D.R.m), ∃ d : GlobalTheory.Grid.HermitianOrthogonalExtensionData (mk (.top (j + 1)) (gX (j + 1) (by omega) h.le))
      (mk (.grid D.R.m (j + 1)) (gV D.R.m (j + 1) (by omega) le_rfl h.le)) (D.R.m - 1 - (j + 1)),
      d.Is (fun p q => GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix (D.R.m - 1 - (j + 1)) (-1 : D.host.E) p q)
        (GlobalTheory.ChiGrid.stairId D.host.AA D.host.AAbar (D.R.m - 1 - (j + 1))) :=
    fun j h => (GlobalTheory.T.exists_extensionData_antiDiagonalSignGram_of_lat_eq _ _ (G'.sp.rowDecS j h) _ (Or.inr rfl) (G'.sp.rowLat j h)).imp fun _ h => h.2
  choose dX hdX using exX

  obtain ⟨dZ, -, hdZ⟩ := GlobalTheory.T.exists_extensionData_antiDiagonalSignGram_of_lat_eq (mk (.grid D.R.m D.R.m) (gV D.R.m D.R.m (by omega) le_rfl le_rfl))
    (mk (.top D.R.m) (gX D.R.m (by omega) le_rfl)) G'.sp.topDec (fun _ => 1) (Or.inl rfl) G'.sp.topLat
  let G : GlobalTheory.Grid.GridPre R :=
    { toGridSp := GS
      idem := e
      chiH := G'.ch.chiH
      chi := G'.ch.chi
      decP := hermitianOrthogonalExtensionDataCast rfl (node_pos (.core 0) (gP 0 (by omega))).symm dP
      decV := fun i => if h : 1 ≤ i ∧ i ≤ D.R.m then
        hermitianOrthogonalExtensionDataCast (node_pos (.core i) (gP i h.2)).symm ((vert_eq i 0 h.1).trans (node_pos (.grid i 0) (gV i 0 h.1 h.2 (by omega)))).symm (dV i h) else hermitianOrthogonalExtensionDataZero _ _ _
      decX := fun j => if h : j + 1 < D.R.m then
        hermitianOrthogonalExtensionDataCast (node_pos (.top (j + 1)) (gX (j + 1) (by omega) h.le)).symm ((vert_eq D.R.m (j + 1) (by omega)).trans (node_pos (.grid D.R.m (j + 1)) (gV D.R.m (j + 1) (by omega) le_rfl h.le))).symm (dX j h) else hermitianOrthogonalExtensionDataZero _ _ _
      decZ := hermitianOrthogonalExtensionDataCast ((vert_eq D.R.m D.R.m (by omega)).trans (node_pos (.grid D.R.m D.R.m) (gV D.R.m D.R.m (by omega) le_rfl le_rfl))).symm
        ((Xp_eq D.R.m (by omega)).trans (node_pos (.top D.R.m) (gX D.R.m (by omega) le_rfl))).symm dZ
      X := fun _ _ => ⟨1, 0, 0⟩
      ωT := fun _ _ _ => 1
      vacT := fun _ _ => 0
      ItT := fun _ _ => 0
      ωC := fun _ _ => 1
      vacC := fun _ => 0
      ItC := fun _ => 0
      dn := fun _ => ⟨1, 0, 0⟩
      ItU := fun _ => 0
      m00 := ⟨0, ∅⟩
      mV := fun _ _ => ⟨0, ∅⟩
      mP := fun _ => ⟨0, ∅⟩
      mX := fun _ => ⟨0, ∅⟩
      vC := fun _ _ => 0 }
  refine ⟨G, rfl, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hi hj
      show (node (.grid (i + 1) j)).Is _ _ _
      rw [node_pos (.grid (i + 1) j) (gV (i + 1) j (by omega) hi hj)]
      exact mk_is _ _
    · intro i hi
      show (node (.core i)).Is _ _ _
      rw [node_pos (.core i) (gP i hi)]
      exact mk_is _ _
    · intro j hj
      show (node (.top (j + 1))).Is _ _ _
      rw [node_pos (.top (j + 1)) (gX (j + 1) (by omega) hj)]
      exact mk_is _ _
    · dsimp only [G]
      rw [gridDecompositionCast_is_iff, ← joinGram_one]
      exact hdP
    · intro i hi1 hi2
      dsimp only [G]
      rw [dif_pos ⟨hi1, hi2⟩, gridDecompositionCast_is_iff]
      have hl' : Z.ideal R.Pg = G'.pl.modul sc := hlvl
      have := hdV i ⟨hi1, hi2⟩
      rw [joinGram_neg, joinStair, ← hl'] at this
      exact this
    · intro j hj
      dsimp only [G]
      rw [dif_pos hj, gridDecompositionCast_is_iff]
      have := hdX j hj
      rw [joinGram_neg, joinStair_top] at this
      exact this
    · dsimp only [G]
      rw [gridDecompositionCast_is_iff, ← joinGram_one]
      exact hdZ
  · exact ⟨hZ, fun i h1 h2 => GlobalTheory.T.heckeCharacterGrid_isAuxiliaryCharacter_testGrid (GlobalTheory.T.gridMinimalGap_eq_chiGridGapGamma_one D) hsc Z hS0 hS1 hZ.Wd_over hw0 i h1 h2, fun i h1 h2 => G'.ch.chi_eq i h1 h2⟩
  · refine ⟨?_, ?_, ?_, hq0, hw0, he0, hWZ, hlvl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    · intro i j hi hj
      cases i with
      | zero => exact GlobalTheory.T.testGridRowZero_vertices_agree_weilData W hW j hj
      | succ i =>
        show NodeAgree (node (.grid (i + 1) j)) W (.grid (i + 1) j)
        rw [node_pos (.grid (i + 1) j) (gV (i + 1) j (by omega) hi hj)]
        exact mk_agree _ _
    · intro i hi
      show NodeAgree (node (.core i)) W (.core i)
      rw [node_pos (.core i) (gP i hi)]
      exact mk_agree _ _
    · intro j hj
      cases j with
      | zero =>
        show NodeAgree (node (.core D.R.m)) W (.top 0)
        rw [node_pos (.core D.R.m) (gP D.R.m le_rfl)]
        exact ⟨rfl, HEq.rfl, heq_of_eq ((hM _ _).1.trans hcT.symm), heq_of_eq ((hM _ _).2.trans hoT.symm)⟩
      | succ j =>
        show NodeAgree (node (.top (j + 1))) W (.top (j + 1))
        rw [node_pos (.top (j + 1)) (gX (j + 1) (by omega) hj)]
        exact mk_agree _ _

end GlobalTheory.GridJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableIdempotentComponentNeOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagPairingTable_idempotentComponent_ne_one : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → GlobalTheory.StdFrames.cpt PP (ewT X h) ≠ 1 → PairTable (hY D) (SmallAt PP) (e0T X h) (f0T X h) (fun i => bwdT X h (Fin.rev i)) (fun i => bwT X h (Fin.rev i)) (z0T X h) := by
  first | exact @GlobalTheory.SeeConjRead.pairTable_rev | exact GlobalTheory.SeeConjRead.pairTable_rev | (intros; apply GlobalTheory.SeeConjRead.pairTable_rev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableIdempotentComponentOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagPairingTable_idempotentComponent_one : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 → PairTable (hY D) (SmallAt PP) (e0T X h) (f0T X h) (bwT X h) (bwdT X h) (z0T X h) := by
  first | exact @GlobalTheory.SeeConjRead.pairTable_of_cpt_one | exact GlobalTheory.SeeConjRead.pairTable_of_cpt_one | (intros; apply GlobalTheory.SeeConjRead.pairTable_of_cpt_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingVectorsIntegralInFrameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagPairingVectors_integral_inFrame : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β₀ : GL (Fin (Yc D 0).rank) (EAf D)), Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0 = GlobalTheory.NormSum.AdLattice.lat β₀ → ∀ (PP : Pl D.host.E) (i j : Fin (Yc D 0).rank), ((β₀⁻¹).val * colMat (flagAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ ((β₀⁻¹).val * colMat (pairAt X h PP)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.SeeConjRead.flag_pair_int | exact GlobalTheory.SeeConjRead.flag_pair_int | (intros; apply GlobalTheory.SeeConjRead.flag_pair_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuumMaximalCompactCharacterRealPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacuum_maximalCompact_character_realPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ τ : D.what₂.Tau, ∃ mS mT : ℤ, ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → ∀ κS κT, IsKMat (pS τ) κS → IsKMat (pT τ) κT → ∀ g h, IsAtTau θ S τ (BS τ * κS * (BS τ)⁻¹) g → IsAtTau θ T τ (BT τ * κT * (BT τ)⁻¹) h → om (g, h) f = (detPos (pS τ) κS ^ (mS + (T.rank - pT τ : ℕ)) * detNeg (pS τ) κS ^ (mS + pT τ) * (detPos (pT τ) κT ^ (mT + pS τ) * detNeg (pT τ) κT ^ (mT + (S.rank - pS τ : ℕ)))) • f := by
  first | exact @GlobalTheory.VacCharAtPlace.vacuum_char_at_place | exact GlobalTheory.VacCharAtPlace.vacuum_char_at_place | (intros; apply GlobalTheory.VacCharAtPlace.vacuum_char_at_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierUniquenessRealComponentsAdelicHomStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_uniqueness_realComponents_adelicHom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (Y : Type) [MeasurableSpace Y] (m : Measure Y) (F : Y → ℂ), Integrable F m → ∀ x : Y → Mx D W.rank ρ, Measurable x → (∀ c : Mx D W.rank ρ, c.map (finPart D) = 0 → ∫ y, ψ (symplO V W (d.extX W (x y)) (d.extY W c)) * F y ∂m = 0) → ∀ S : Set (Mx D W.rank ρ), MeasurableSet S → (∀ z z' : Mx D W.rank ρ, z.map (infPart D) = z'.map (infPart D) → (z ∈ S ↔ z' ∈ S)) → ∫ y in x ⁻¹' S, F y ∂m = 0 := by
  first | exact @GlobalTheory.FourierRealPart.integral_preimage_eq_zero | exact GlobalTheory.FourierRealPart.integral_preimage_eq_zero | (intros; apply GlobalTheory.FourierRealPart.integral_preimage_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialSuperdiagonalOffExceptionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericCharacter_trivial_superdiagonal_off_exceptional : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ i j : Fin ρ, j.1 = i.1 + 1 → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ G.pl.S0 → ∀ o ∈ intAt D (· = v), psiE W.ψ (o * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) = 1 := by
  first | exact @GlobalTheory.UniOff.uni_off | exact GlobalTheory.UniOff.uni_off | (intros; apply GlobalTheory.UniOff.uni_off <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedLatticePrescribedLocalComponentsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedLattice_prescribed_localComponents : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V) (f₀ : Pl D.host.E → Fin X.rank → EAf D), Submodule.IsLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) → (∀ w : Pl D.host.E, π ∈ w.asIdeal → idem w • f₀ w = f₀ w ∧ f₀ w - idem w • vA X x₀ ∈ hat L₀) → IsGlued Y X ι z u π L₀ f₀ (glueLat Y X ι z u L₀ x₀) := by
  first | exact @GlobalTheory.GluedCmp.isGlued_glueLat | exact GlobalTheory.GluedCmp.isGlued_glueLat | (intros; apply GlobalTheory.GluedCmp.isGlued_glueLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluedLatticeSelfDualPrimitiveMeetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedLattice_selfDual_primitive_meet : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) → IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) ∧ IsPrim Y z (glueLat Y X ι z u L₀ x₀) ∧ capX Y X ι (glueLat Y X ι z u L₀ x₀) = L₀ := by
  first | exact @GlobalTheory.GlueVecLattice.glueLat_selfDual_prim_cap | exact GlobalTheory.GlueVecLattice.glueLat_selfDual_prim_cap | (intros; apply GlobalTheory.GlueVecLattice.glueLat_selfDual_prim_cap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedPlaceOfUnramifiedOnePrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_unramified_place_of_unramified_one_prime : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → ResEta D ν 0 →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt ν w → GlobalTheory.WeilParts.UnramAt ε ν := by
  first | exact @GlobalTheory.UnramFromOnePrime.unramAt_of_unrAt_one | exact GlobalTheory.UnramFromOnePrime.unramAt_of_unrAt_one | (intros; apply GlobalTheory.UnramFromOnePrime.unramAt_of_unrAt_one <;> assumption)
end

