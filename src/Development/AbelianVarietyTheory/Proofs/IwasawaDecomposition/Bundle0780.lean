import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefDualPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulPrIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0761
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0760
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0400
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0468
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0736
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0766
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0277
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0759
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0729
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0733
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0762
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicReadingDecoratedLatticeForms
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.BrgRead

set_option maxHeartbeats 1000000

theorem embLL_labLL_eq {D : D7} (τ : D.what₂.Tau) (x : D.host.E) : D.what₂.embLL (labLL D τ x) = tauE D τ x :=
  DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)

theorem gram_V (X : Stages) (h : DiagSpaces X.toD7.sp) (i : Fin X.toD7.R.m) : (Vc X.toD7 i).gram = 1 := by
  obtain ⟨hs, -, -, -, -, hV⟩ := h
  have h1 := hV ((i : ℕ) + 1)
  have hn : X.toD7.sp.Vneg ((i : ℕ) + 1) = false := X.B.V_pos _ (by omega) i.2
  rw [hn] at h1
  change (X.toD7.sp.V ((i : ℕ) + 1)).gram = 1
  rw [h1]
  refine Matrix.ext fun a b => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ a b).trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

theorem isDualPair_smul {D : D7} {θ : InfFam D} {MX : DSModel D.sp.X' (parB (Ptw D) D.R.m)} {cX : CoefA D.sp.X'}
    {prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ} (h : IsDualPair θ MX cX prX) {c : ℂ} (hc : c ≠ 0) :
    IsDualPair θ MX cX (c • prX) := by
  refine ⟨smul_ne_zero hc h.1, fun τ g hg w v u hu => ?_⟩
  simp only [LinearMap.smul_apply]
  rw [h.2 τ g hg w v u hu]

theorem exists_coefData : ∀ (D : D7), Seed.VPos D → ∀ θ : InfFam D, IsInfFam θ → ∀ MX : DSModel D.sp.X' (parB (Ptw D) D.R.m),
  ∃ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ)
    (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] cX.W)
    (c0L : ∀ i : Fin D.R.m, VV D.what₂.LL (fun τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) →ₛₗ[D.what₂.embLL] (cV i).W),
    cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧
    (gramR = D.sp.X'.gram ∨ gramR = -D.sp.X'.gram) ∧
    Bridge.CoefMapTie D.sp.X' cX.coef c0R (rhoV (labLL D) _) ∧
    (∀ i, Bridge.CoefMapTie (Vc D i) (cV i).coef (c0L i) (rhoVr (labLL D) _)) ∧
    (∀ x y, inner ℂ (c0R x) (c0R y) = D.what₂.embLL (pairV (labLL D) _ gramR x y)) ∧
    ∀ i x y, inner ℂ (c0L i x) (c0L i y) = D.what₂.embLL (pairVr (labLL D) _
      (if D.sp.Vneg ((i : ℕ) + 1) then -(Vc D i).gram else (Vc D i).gram) x y) := by
  intro D hV θ hθ MX
  obtain ⟨cX, prX, c0R, gramR, hcX, hdual, hg, hmap, hin⟩ := GlobalTheory.CoefSpace.exists_coef_dualPair D θ MX hθ
  have hL := fun i => GlobalTheory.CoefModel.exists_coef_lift D i (hV i)
  choose cV c0L hcV hmapL hinL using hL
  obtain ⟨c, hc, hiso⟩ := GlobalTheory.PrIsoScale.exists_smul_prIso D θ MX cX prX hθ hcX hdual
  exact ⟨cX, cV, c • prX, gramR, c0R, c0L, hcX, hcV, isDualPair_smul hdual hc, hiso, hg, hmap, hmapL, hin, hinL⟩
theorem hecke_degrees : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px),
    (∀ t P, (famR X I hX U Xg tr).A.heckeR t (P, 0) = 1 ∧
      ∀ k, X.toD7.sp.X'.rank < k → (famR X I hX U Xg tr).A.heckeR t (P, k) = 0) ∧
    (∀ i t P, (famR X I hX U Xg tr).A.heckeL i t (P, 0) = 1 ∧
      ∀ k, (Vc X.toD7 i).rank < k → (famR X I hX U Xg tr).A.heckeL i t (P, k) = 0) := by
  intro X px I hX U Xg tr
  have hk3 := X.B.R.m_add_three_le_k
  refine ⟨fun t P => ⟨heckeCSD_zero _ _ _ _ _ _, fun k hk => ?_⟩, fun i t P => ⟨heckeCSD_zero _ _ _ _ _ _, fun k hk => ?_⟩⟩
  · refine (congrArg _ (Formalism.L2.Col.heckeFam_eq_zero_of_lt _ _ _ ?_)).trans (LinearEquiv.map_zero _)
    have e := X.toD7.sp.X'_rank
    change X.toD7.sp.X'.rank < k at hk
    rw [e] at hk
    change _ < k
    unfold Ranks.rankX' at hk
    unfold Ranks.N
    simp only [Ranks.r] at hk ⊢
    change X.B.R.k + X.B.R.m - 1 + X.B.R.m * X.B.R.t < k at hk
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · refine (congrArg _ (Formalism.L2.Col.heckeFam_eq_zero_of_lt _ _ _ ?_)).trans (LinearEquiv.map_zero _)
    have e := X.toD7.sp.V_rank _ (by omega) i.2
    change (X.toD7.sp.V ((i : ℕ) + 1)).rank < k at hk
    rw [e] at hk
    exact hk

theorem exists_brgL : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → (∀ i, L.βV i = 1) → Seed.FrmC.StdLat X.toD7.sp.X' → (∀ i, Seed.FrmC.StdLat (Vc X.toD7 i)) → ∀ θ : InfFam X.toD7, IsInfFam θ → ∀ MX : DSModel X.toD7.sp.X' (parB (Ptw X.toD7) X.toD7.R.m), ∃ (cX : CoefA X.toD7.sp.X') (cV : ∀ i, CoefA (Vc X.toD7 i)) (pl : PlS X.B px → Pl X.toD7.host.E) (Sb : Finset (Pl X.toD7.host.E)) (Bd : Seed.BType (famR X I hX U Xg tr) L cX cV pl) (plI : PlI X.B px → Pl X.toD7.host.E) (SF : Finset (HeightOneSpectrum (𝓞 X.toD7.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ), cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧ Seed.BrgL (famR X I hX U Xg tr) L eG cX cV pl Sb Bd plI SF ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => Bd.jR t φ) ∧ ∀ i, BrgStdV X I hX U Xg tr L i (cV i) fun t φ => Bd.jL i t φ := by
  intro X px I hX U Xg tr L eG hI hV hL hG hβX hβV hsX hsV θ hθ MX
  have hVP : Seed.VPos X.toD7 := fun i => X.B.V_posDef _ (by omega) i.2
  obtain ⟨cX, cV, prX, gramR, c0R, c0L, hcX, hcV, hdual, hiso, hgram, hmapR, hmapL, hinR, hinL⟩ :=
    exists_coefData X.toD7 hVP θ hθ MX
  have hR := GlobalTheory.T.exists_rowForms_adelic_decoratedLattices X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgram hmapR hinR hβX hsX
  have hLf := fun i => GlobalTheory.T.exists_liftForms_adelic_decoratedLattices X px I hX U Xg tr L eG hI hV hL hG cV i (c0L i) (hcV i) (hmapL i) (hinL i) (hβV i)
    (gram_V X hI.spaces i) (hsV i)
  obtain ⟨sR, hsR, hstR⟩ := hR
  choose sL hsL hstL using hLf
  obtain ⟨hok, hon, hit, hion⟩ := GlobalTheory.Mem.R3.famR_places X px I hX U Xg tr L eG hI hV hL hG
  obtain ⟨hmu, heta, hroots⟩ := GlobalTheory.Mem.R3.Brg.values X px I hX U Xg tr L eG hI hV hL hG
  obtain ⟨hdR, hdL⟩ := hecke_degrees X px I hX U Xg tr
  have hrk : X.toD7.sp.X'.rank = (famR X I hX U Xg tr).A.r + X.toD7.R.m * (famR X I hX U Xg tr).A.t := X.toD7.sp.X'_rank
  have hrkL : ∀ i : Fin X.toD7.R.m, (Vc X.toD7 i).rank = (famR X I hX U Xg tr).A.r + (famR X I hX U Xg tr).A.t :=
    fun i => X.toD7.sp.V_rank _ (by omega) i.2
  let B : Seed.BType (famR X I hX U Xg tr) L cX cV (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) :=
    { R := sR, L := fun i t => sL i t, rankR := hrk, rankL := hrkL }
  classical
  refine ⟨cX, cV, fun P => P.1, L.Pg, B, fun Q => Q.1, L.Pg.image (fun PP => PP.under (𝓞 X.toD7.host.F)), prX,
    hcX, hcV, hdual, hiso, ?_, hstR, hstL⟩
  exact
    { red_R := fun t q => (hsR t).1 q
      red_L := fun i t q => (hsL i t).1 q
      tie := ⟨gramR, c0R, c0L,
        { ranks := ⟨rfl, rfl, rfl⟩
          v0 := rfl
          tauL_ok := fun τ => RingHom.ext fun x => embLL_labLL_eq τ x
          pl_inj := fun a b h => Subtype.ext h
          q := fun P => rfl
          S_fin := Set.toFinite _
          ok := hok
          gramR_eq := hgram
          mapR := hmapR
          mapL := hmapL
          coefR := fun t => (hsR t).2.1
          coefL := fun i t => (hsL i t).2.1 }⟩
      sb := rfl
      roots := hroots
      pl_onto := hon
      degR := hdR
      degL := hdL
      muVal := hmu
      etaVal := heta
      in_tie := hit
      in_onto := hion
      in_R := fun t => (hsR t).2.2
      in_L := fun i t => (hsL i t).2.2
      in_SF := fun v => by
        simp only [Finset.mem_image]
        refine exists_congr fun PP => and_congr_right fun _ => ?_
        rw [HeightOneSpectrum.ext_iff, HeightOneSpectrum.under_asIdeal, Ideal.under_def] }

end GlobalTheory.Mem.R3.BrgRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjParahoricBlockLift
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.ParahLift

section Core

variable {K : Type} [CommRing K]

theorem pl_blkDiag_mem {m r : ℕ} {x : GL (Fin r) K} {M : GL (Fin m) K} (hM : GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity x M) :
    M ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  intro i j hij
  have hj : j.val < r := by
    unfold Formalism.L2.DIV.blk2 at hij; split_ifs at hij with h1 h2 <;> omega
  have hi : ¬ i.val < r := by
    unfold Formalism.L2.DIV.blk2 at hij; split_ifs at hij with h1 h2 <;> omega
  have hne : i ≠ j := fun h => hi (h ▸ hj)
  show M.val i j = 0
  rw [hM i j, dif_neg (fun h => hi h.1), if_neg hne]

theorem pl_blkOf_eq {m r t : ℕ} (hm : m = r + t) (a : Fin m) :
    Formalism.L2.DIV.blkOf r t a = Formalism.L2.DIV.blk2 r a := by
  have ha := a.2
  unfold Formalism.L2.DIV.blkOf Formalism.L2.DIV.blk2
  split_ifs with h
  · rfl
  · have : (a.val - r) / t = 0 := Nat.div_eq_of_lt (by omega)
    omega

theorem pl_blockTri_eq {m r t : ℕ} (hm : m = r + t) :
    Formalism.L2.DIV.blockTri (κ := K) (n := m) (Formalism.L2.DIV.blkOf r t) = Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  have : (Formalism.L2.DIV.blkOf r t : Fin m → ℕ) = Formalism.L2.DIV.blk2 r := funext (pl_blkOf_eq hm)
  rw [this]

theorem pl_core {m r t : ℕ} (hm : m = r + t) (hr : r ≤ m) {b M : GL (Fin m) K} {x : GL (Fin r) K}
    (hb : b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) (hM : GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity x M) :
    b * M * b⁻¹ ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧
    Formalism.L2.DIV.upperLeftBlock hr (b * M * b⁻¹) = Formalism.L2.DIV.upperLeftBlock hr b * x * (Formalism.L2.DIV.upperLeftBlock hr b)⁻¹ ∧
    Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 (b * M * b⁻¹) = 1 := by
  have hM2 := pl_blkDiag_mem hM
  have hbinv := (Formalism.L2.DIV.blockTri (κ := K) (Formalism.L2.DIV.blk2 r)).inv_mem hb
  have hbM := (Formalism.L2.DIV.blockTri (κ := K) (Formalism.L2.DIV.blk2 r)).mul_mem hb hM2
  have hall := (Formalism.L2.DIV.blockTri (κ := K) (Formalism.L2.DIV.blk2 r)).mul_mem hbM hbinv
  have hE := pl_blockTri_eq (K := K) hm
  refine ⟨hE ▸ hall, ?_, ?_⟩
  · have hMr : Formalism.L2.DIV.upperLeftBlock hr M = x := by
      apply Units.ext
      ext i j
      rw [Formalism.L2.DIV.upper_block_val_submatrix hr hM2, Matrix.submatrix_apply, hM, dif_pos ⟨i.2, j.2⟩]
      rfl
    unfold Formalism.L2.DIV.upperLeftBlock at hMr ⊢
    rw [Formalism.L2.DIV.extendMatrixByIdentityAlongIndices_mul _ hbM hbinv, Formalism.L2.DIV.extendMatrixByIdentityAlongIndices_mul _ hb hM2, Formalism.L2.DIV.extendOne_inv _ hb, hMr]
  · have hb' : b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := hE ▸ hb
    have hM' : M ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := hE ▸ hM2
    have hbinv' : b⁻¹ ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := hE ▸ hbinv
    have hbM' := (Formalism.L2.DIV.blockTri (κ := K) (Formalism.L2.DIV.blkOf r t)).mul_mem hb' hM'
    have hdM : Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 M = 1 := by
      apply Units.ext
      rw [Formalism.L2.DIV.diag_block_det_val 1 hM', Units.val_one]
      have hsub : (M.val.submatrix (Subtype.val : {a : Fin m // Formalism.L2.DIV.blkOf r t a = 1} → Fin m) (Subtype.val : {a : Fin m // Formalism.L2.DIV.blkOf r t a = 1} → Fin m)) = 1 := by
        ext a c
        have ha : ¬ a.1.val < r := fun h => by
          have h2 := a.2
          simp [Formalism.L2.DIV.blkOf, h] at h2
        rw [Matrix.submatrix_apply, hM, dif_neg (fun h => ha h.1), Matrix.one_apply]
        by_cases hac : a = c
        · subst hac; simp
        · rw [if_neg hac, if_neg (fun h => hac (Subtype.ext h))]
      show (M.val.submatrix (Subtype.val : {a : Fin m // Formalism.L2.DIV.blkOf r t a = 1} → Fin m) (Subtype.val : {a : Fin m // Formalism.L2.DIV.blkOf r t a = 1} → Fin m)).det = 1
      rw [hsub, Matrix.det_one]
    rw [Formalism.L2.DIV.diag_block_det_mul hbM' hbinv', Formalism.L2.DIV.diag_block_det_mul hb' hM', hdM, mul_one]
    unfold Formalism.L2.DIV.dBlk
    rw [Formalism.L2.DIV.extendOne_inv _ hb', mul_inv_cancel]

theorem pl_core_cast {n m r t : ℕ} (hn : n = m) (hm : m = r + t) (hr : r ≤ m) (hr' : r ≤ n) {b M : GL (Fin m) K}
    {X : GL (Fin n) K} {x : GL (Fin r) K}
    (hb : b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) (hM : GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity x M)
    (hX : ∀ a c : Fin m, X.val (Fin.cast hn.symm a) (Fin.cast hn.symm c) = (b * M * b⁻¹).val a c) :
    X ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧
    Formalism.L2.DIV.upperLeftBlock hr' X = Formalism.L2.DIV.upperLeftBlock hr b * x * (Formalism.L2.DIV.upperLeftBlock hr b)⁻¹ ∧
    Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 X = 1 := by
  subst hn
  have hXe : X = b * M * b⁻¹ := Units.ext (Matrix.ext fun a c => hX a c)
  subst hXe
  exact pl_core hm hr hb hM

theorem pl_one_cast {n m : ℕ} (hn : n = m) {b Y : GL (Fin m) K} {X : GL (Fin n) K} (hY : Y = 1)
    (hX : ∀ a c : Fin m, X.val (Fin.cast hn.symm a) (Fin.cast hn.symm c) = (b * Y * b⁻¹).val a c) : X = 1 := by
  subst hn; subst hY
  apply Units.ext
  ext a c
  have h := hX a c
  rw [mul_one, mul_inv_cancel] at h
  exact h

end Core

end GlobalTheory.ParahLift

namespace GlobalTheory.ParahLift

section LevFn

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
  {LL : Type} [CommRing LL]

theorem pl_levFn_eq_one (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Ld : Formalism.L2.DIV.LevDat E LL n)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hP : Ld.P.chi = 1)
    (hg : ∀ PP ∈ Ld.Pg, ∀ c ∈ Finset.range Ld.s,
      Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf Ld.r Ld.t) (c + 1) (Formalism.L2.DIV.redFn β PP x) = 1)
    (hq : ∀ PP ∈ Ld.Q, Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 Ld.r) 1 (Formalism.L2.DIV.redFn β PP x) = 1) :
    Formalism.L2.DIV.levFn β Ld x = 1 := by
  unfold Formalism.L2.DIV.levFn
  rw [Finset.prod_eq_one (fun PP hPP => Finset.prod_eq_one (fun c hc => by rw [hg PP hPP c hc, map_one])),
    Finset.prod_eq_one (fun PP hPP => by rw [hq PP hPP, map_one])]
  have h1 : Formalism.L2.DIV.ext1 Ld.P.H Ld.P.chi (Formalism.L2.DIV.rTup β Ld x) = 1 := by
    unfold Formalism.L2.DIV.ext1
    split_ifs
    · rw [hP]; rfl
    · rfl
  rw [h1, mul_one, mul_one]

end LevFn

theorem exists_conj_parahoric_lift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (k : Fin D.R.m) (s : T)
  (P : Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc D k) D.R.nV) (L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV),
  (∀ g, L g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) →
  (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ κ) ∈ Formalism.L2.DIV.St (R.βV k)) →
  (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q s → ∃ (s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin D.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w = PP ∧ GlobalTheory.CenFrame.IsResidue s' φ ∧
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV D k) P (R.βV k) s' φ b ∧ (PP ∈ R.Pg → b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 D.R.r))) →
  (∀ g (s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w), GlobalTheory.CenFrame.IsResidue s' φ →
      (s'.w ∈ R.Q s → ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧ Matrix.GeneralLinearGroup.map φ y = 1) ∧
      ∀ hP : s'.w ∈ R.Pg, ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧
        GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (R.eG ((R.eG.trans cG).symm g) ⟨s'.w, hP⟩) (Matrix.GeneralLinearGroup.map φ y)) →
  ∃ c : G, ∀ g : G,
    Formalism.IndefR.Lev.IsLevelLift (Formalism.IndefR.Links.Vc D k) (R.βV k) (R.datVt k s) (R.eG g) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) ∧
    Formalism.IndefR.Lev.levChi (Formalism.IndefR.Links.Vc D k) (R.βV k) (Formalism.IndefR.Lev.flagL (R.datVt k s)) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) = 1 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R cG k s P L H1 H2 H3 H4
  have hn : (Formalism.IndefR.Links.Vc D k).rank = D.R.nV := GlobalTheory.FrameBlockDiagonal.rankV D k
  have hm : D.R.nV = D.R.r + D.R.t := rfl
  have hr : D.R.r ≤ D.R.nV := Nat.le_add_right _ _
  have hr' : D.R.r ≤ (Formalism.IndefR.Links.Vc D k).rank := hn ▸ hr
  have hA : ∀ PP : ↥R.Pg, ∃ b : GL (Fin D.R.nV) (Formalism.L2.DIV.kP PP.1), b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 D.R.r) ∧
      ∀ h : G0g D.nd, ∃ M : GL (Fin D.R.nV) (Formalism.L2.DIV.kP PP.1),
        GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (R.eG ((R.eG.trans cG).symm h) PP) M ∧
        ∀ a c, (Formalism.L2.DIV.redFn (R.βV k) PP.1 (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h)))).val
          (Fin.cast hn.symm a) (Fin.cast hn.symm c) = (b * M * b⁻¹).val a c := by
    rintro ⟨PP, hPP⟩
    obtain ⟨s', φ, b, hw, hres, hfr, hb⟩ := H3 PP (Or.inl hPP)
    subst hw
    refine ⟨b, hb hPP, fun h => ?_⟩
    obtain ⟨y, hy, hbd⟩ := (H4 h s' φ hres).2 hPP
    exact ⟨_, hbd, hfr (L h) (H1 h) y hy⟩
  have hB : ∀ PP ∈ R.Q s, ∀ h : G0g D.nd,
      Formalism.L2.DIV.redFn (R.βV k) PP (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h))) = 1 := by
    intro PP hPP h
    obtain ⟨s', φ, b, hw, hres, hfr, -⟩ := H3 PP (Or.inr hPP)
    subst hw
    obtain ⟨y, hy, h1⟩ := (H4 h s' φ hres).1 hPP
    exact pl_one_cast hn h1 (hfr (L h) (H1 h) y hy)
  choose bf hbf Mf hMd hMe using hA
  refine ⟨R.eG.symm (fun PP => (Formalism.L2.DIV.upperLeftBlock hr (bf PP))⁻¹), fun g => ?_⟩
  set c := R.eG.symm (fun PP => (Formalism.L2.DIV.upperLeftBlock hr (bf PP))⁻¹) with hc
  set h := (R.eG.trans cG) (c * g * c⁻¹) with hh
  have hsymm : (R.eG.trans cG).symm h = c * g * c⁻¹ := MulEquiv.symm_apply_apply _ _
  have hx : ∀ PP : ↥R.Pg, R.eG ((R.eG.trans cG).symm h) PP =
      (Formalism.L2.DIV.upperLeftBlock hr (bf PP))⁻¹ * R.eG g PP * Formalism.L2.DIV.upperLeftBlock hr (bf PP) := by
    intro PP
    rw [hsymm, map_mul, map_mul, map_inv, hc, MulEquiv.apply_symm_apply]
    simp only [Pi.mul_apply, Pi.inv_apply, inv_inv]
  have hcore : ∀ PP : ↥R.Pg,
      Formalism.L2.DIV.redFn (R.βV k) PP.1 (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h))) ∈
        Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf D.R.r D.R.t) ∧
      Formalism.L2.DIV.upperLeftBlock hr' (Formalism.L2.DIV.redFn (R.βV k) PP.1 (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h)))) =
        R.eG g PP ∧
      Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf D.R.r D.R.t) 1
        (Formalism.L2.DIV.redFn (R.βV k) PP.1 (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h)))) = 1 := by
    intro PP
    obtain ⟨h1, h2, h3⟩ := pl_core_cast hn hm hr hr' (hbf PP) (hMd PP h) (hMe PP h)
    refine ⟨h1, ?_, h3⟩
    rw [h2, hx PP]
    group
  have hSt := H2 (L h) (H1 h)
  refine ⟨⟨P.into _, Formalism.L2.DIV.mem_parLev.2 ⟨GlobalTheory.LevFinCong.finE_mem_UA _ _, hSt, fun PP hPP => (hcore ⟨PP, hPP⟩).1,
    fun PP hPP => ?_⟩, ?_⟩, ?_⟩
  · rw [hB PP hPP h]; exact Subgroup.one_mem _
  · funext PP
    exact (hcore PP).2.1
  · unfold Formalism.IndefR.Lev.levChi
    rw [pl_levFn_eq_one _ _ _ rfl, Units.val_one]
    · intro PP hPP c' hc'
      have hc0 : c' = 0 := by
        have : c' < 1 := Finset.mem_range.1 hc'
        omega
      subst hc0
      exact (hcore ⟨PP, hPP⟩).2.2
    · intro PP hPP
      rw [hB PP hPP h]
      exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _

end GlobalTheory.ParahLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDescendedRaysMarkedFormPiecesStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descended_rays_marked_form_pieces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀]
  [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (hm : ∀ i, δ₀ i ∈ balForms H.bar X₀),
  (∀ i y, 0 ≤ δ₀ i y y) → LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, hm i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (β : LinearMap.BilinForm ℤ X) (τ : 𝓞 E ≃+* 𝓞 E)
    (f : X →+ X₀ ⧸ (CarDim.orad v : Submodule (𝓞 E) X₀)), τ H.w0 = H.w0 → Function.Surjective f →
    (∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) →
    (∀ (x y : X) (x₀ y₀ : X₀), Submodule.Quotient.mk x₀ = f x → Submodule.Quotient.mk y₀ = f y → β x y = v x₀ y₀) →
  ∃ u : Fin m₀ → LinearMap.BilinForm ℤ (X₀ ⧸ (CarDim.orad v : Submodule (𝓞 E) X₀)),
    toReal β = ∑ i, t i • toReal (pullAdd f (u i)) ∧
    LinearIndependent ℤ (fun i : {i // 0 < t i} => pullAdd f (u i)) ∧
    ∀ i, 0 < t i → pull (CarDim.orad v : Submodule (𝓞 E) X₀).mkQ (u i) = δ₀ i ∧ pullAdd f (u i) ∈ balForms H.bar X ∧
      (∀ y, 0 ≤ pullAdd f (u i) y y) ∧ (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = pullAdd f (u i) → k = 1) ∧
      ∀ lab : InvFun (𝓞 E), IsTwInv H lab → lab.evalZ (pullAdd f (u i)) = lab.evalZ (δ₀ i) := by
  first | exact @GlobalTheory.PolFan.OrbMark.exists_desc_rays_pullAdd | exact GlobalTheory.PolFan.OrbMark.exists_desc_rays_pullAdd | (intros; apply GlobalTheory.PolFan.OrbMark.exists_desc_rays_pullAdd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEigenIndexLabelingAtMemberStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigen_index_labeling_at_member : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ T w Z Wt _ t _ _ _ => ∃ (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd), Nonempty (E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) := by
  first | exact @GlobalTheory.HeightCounting.Up.IdxAt.exists_divX_eigIdx_lab | exact GlobalTheory.HeightCounting.Up.IdxAt.exists_divX_eigIdx_lab | (intros; apply GlobalTheory.HeightCounting.Up.IdxAt.exists_divX_eigIdx_lab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEigenReadThirdLocalStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigen_read_third_local : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → GlobalTheory.NRows.HypothesesX → AllSt fun _ _ _ T w P x => ∀ (l : LC hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), GlobalTheory.CoefDuty.Built l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → ∃ (Xd : DivX (withLoc L)) (E : EigIdx (withLoc L) Xd), Nonempty (E.Pi → (famR (w.st (GlobalTheory.HeightCounting.Fin3.oL x L).Z) w.I P.hX (usedOf w.I T P.Wt) m.z.Xg m.z.tr).A.fam.base.Ix) := by
  first | exact @GlobalTheory.HeightCounting.Up.ThirdIdx.exists_divX_eigIdx_third | exact GlobalTheory.HeightCounting.Up.ThirdIdx.exists_divX_eigIdx_third | (intros; apply GlobalTheory.HeightCounting.Up.ThirdIdx.exists_divX_eigIdx_third <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteRationalPolyhedralCellsUptoAutStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_rational_polyhedral_cells_upto_aut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g q : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], IsPolFan (id : ℤ → ℤ) g φs → Module.finrank ℚ E * q ≤ g → Module.finrank (𝓞 E) X ≤ q → HasRedCover H.bar X → ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone H.bar X, ∃ (e : X ≃ₗ[𝓞 E] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell H.bar (baseFun (𝓞 E) (fineDen g 𝓜) φs 𝓜) γ ∧ (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  first | exact @GlobalTheory.PolCell.exists_cells | exact GlobalTheory.PolCell.exists_cells | (intros; apply GlobalTheory.PolCell.exists_cells <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisCharacterOfFiniteOrderHeckeCharacterStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisCharacter_of_finiteOrder_heckeCharacter : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (χ : HChar D.host.E) (n : ℕ), 0 < n → χ.OrderDvd n → (∃ z : D.what₂.LL, IsPrimitiveRoot z n) → ∃ ψ₀, GalOf D χ ψ₀ ∧ ∀ g, ψ₀ g ^ n = 1 := by
  first | exact @GlobalTheory.LevCmp.galOf_of_orderDvd | exact GlobalTheory.LevCmp.galOf_of_orderDvd | (intros; apply GlobalTheory.LevCmp.galOf_of_orderDvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeDataSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hecke_data_split_place : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∀ (i : Fin (Dof x).R.m) (k : ℕ) (Pl : PlE (Dof x).host), 1 ≤ k → k ≤ (Dof x).R.r → IsSplitPl (Dof x).host Pl → Pl ∉ SbD (Dof x) → ∃ α Rr, HkDat x.m.z.R (SbD (Dof x)) i k Pl α Rr := by
  first | exact @GlobalTheory.HeckeDataAtState.exists_hkDat_at_state | exact GlobalTheory.HeckeDataAtState.exists_hkDat_at_state | (intros; apply GlobalTheory.HeckeDataAtState.exists_hkDat_at_state <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_invertible_frame_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ (k' : U.Comp) (s : ReciprocityTheory.L2DbarEstimates.V X.dim → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)), AnalyticAt ℂ s (c'.e y) → (∀ᶠ w in 𝓝 (c'.e y), ∃ hs : s w ∈ (U.X k').dom, cxPt T.Z (U.un k' ⟨s w, hs⟩) = cxOf e σ hj (c'.e.symm w)) → ∃ K : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ, (∀ τ a b, AnalyticAt ℂ (fun w => K w τ a b) (c'.e y)) ∧ (∀ τ, IsUnit (K (c'.e y) τ).det) ∧ ∀ᶠ w in 𝓝 (c'.e y), (∃ g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm w)).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (c'.e.symm w) g) ∧ ∀ (hs : s w ∈ (U.X k').dom) (g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm w)).1 ≫ genι T.Z)), FrameAt e f₀ A₀ A (c'.e.symm w) g → ∀ (M : EigMet T.Z σ) (τ : E →+* ℂ), M.gram (cxOf e σ hj (c'.e.symm w)) g τ = (K w τ)ᴴ * M.gram (cxPt T.Z (U.un k' ⟨s w, hs⟩)) (cxFrame T.Z (U.un k' ⟨s w, hs⟩)) τ * K w τ := by
  first | exact @GlobalTheory.FrameLift.exists_holomorphic_frame_coords | exact GlobalTheory.FrameLift.exists_holomorphic_frame_coords | (intros; apply GlobalTheory.FrameLift.exists_holomorphic_frame_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicLatticeBasisPunctPolydiscCoverPStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_latticeBasis_punctPolydiscCover_polyGrowth : ∀ (n a g r₀ : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (Pair : ℕ → (Fin n → ℂ) → (Fin g → ℂ) → (Fin g → ℂ) → ℂˣ → Prop), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∃ C : ℝ, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ‖ζ z‖ ≤ C) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → (∀ N z v w c c', Pair N z v w c → Pair N z v w c' → c = c') → (∀ (m N : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → Fin n → ℂ) (v w : (Fin m → ℂ) → Fin g → ℂ) (c : ℂˣ) (b₀ b₁ : Fin m → ℂ), 0 < N → IsOpen B → IsPreconnected B → DifferentiableOn ℂ φ B → Set.MapsTo φ B (Metric.ball 0 1) → DifferentiableOn ℂ v B → DifferentiableOn ℂ w B → (∀ b ∈ B, v b ∈ K (φ b) ∧ w b ∈ K (φ b)) → b₀ ∈ B → b₁ ∈ B → Pair N (φ b₀) (v b₀) (w b₀) c → Pair N (φ b₁) (v b₁) (w b₁) c) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ Submodule.span ℝ (K z) = ⊤ ∧ (∀ v ∈ K z, ∀ w ∈ K z, ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (N : ℕ) (v w : Fin g → ℂ), 0 < N → v ∈ K z → w ∈ K z → Pair N z v w (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / N)) (Complex.exp_ne_zero _))) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ a a' : Fin r₀ → ℤ, (fun j => (a j : ZMod N)) ∈ S → Pair N 0 (∑ j, a j • ζ 0 j) (∑ j, a' j • ζ 0 j) 1) → ∃ (r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (ρ : Fin g → Fin r → ℂ), ContinuousOn lam (logDom n a) ∧ (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ (∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) ∧ ∀ j, ∑ m, ρ j m • lam s m = Pi.single j 1) ∧ ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.Core.core | exact GlobalTheory.ShFam.Hor.LogCh.Core.core | (intros; apply GlobalTheory.ShFam.Hor.LogCh.Core.core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistRingMapLargeCoefficientRingsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twist_ring_map_large_coefficient_rings : ∀ (D : D7) (C : NChoice D) (F : TwFrameC D) (low : Finset ℕ) (E0 : PlEmb D.what₂), TwistFrameLowIndexCompatibility D F low → ChoiceC D C → ∀ w : D.what₂.places.Pl, ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ (X : CoefIn D.what₂) (j : ℕ), X.E = E0 → F0.1 ≤ (X.Kx j w).1 → ∃ f : D.ntw.O0 (C.twI w) →+* OcC X j w, TwAlgAt C X j w f ∧ TwRdAt C X j w f ∧ (TwistedAt D w → ∀ (x : D.LL0) (y : D.ntw.O0 (C.twI w)), algebraMap (D.ntw.O0 (C.twI w)) (FractionRing (D.ntw.O0 (C.twI w))) y = (if C.sd w then D.ntw.emb0 (C.twI w) else D.ntw.emb0b (C.twI w)) x → ecC X j w (x : D.what₂.LL) = algebraMap (OcC X j w) (FractionRing (OcC X j w)) (f y)) := by
  first | exact @GlobalTheory.HeckeLocN.exists_twRing_of_large | exact GlobalTheory.HeckeLocN.exists_twRing_of_large | (intros; apply GlobalTheory.HeckeLocN.exists_twRing_of_large <;> assumption)
end

