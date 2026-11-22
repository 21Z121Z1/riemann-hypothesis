import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddings
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0865
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0241
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqVolMulSum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0516
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0864
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDatumCharactersUnramifiedOffLevelsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBaseDataIsGoodTwist
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeriesTie.BaseGood

theorem base_good : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (F3 : Face3 D A3), Rl.Char3 F3 → ∀ (j : Fin D.R.m) (F : Frame (Vc D j) (Wc D j)) (hF : F.Good) (de : Twist D Circle), de.Good → PlacesOK Rl.Pg de.Q → ∃ (w : Weight D (Vc D j).rank) (mu : ResChars D Circle), (∀ τ, w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ) ∧ (∀ τ, w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ) ∧ ∀ P : LevelP Rl.Pg (Wc D j).rank ℂ, (⟨hF.rank_le, F, ⟨Rl.Pg, P, mu⟩, de, w, Rl.mu0 ((j : ℕ) + 1), Rl.eta⟩ : Base (Vc D j) (Wc D j)).Good := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl F3 hC j F hF de hde hpl
  have hL := hC.lev
  have hS : SplitSet Rl.Pg := by
    obtain ⟨P, h1, -, hP⟩ := hpl.split
    exact hP.mono h1
  have hr : Odd D.R.r := Formalism.L2.NTheta.odd_r D.R
  have rV : (Vc D j).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have rW : (Wc D j).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) j.2
  obtain ⟨Pa, hPa1, hPa2, hPa⟩ := hpl.split
  refine ⟨GlobalTheory.ConjTwist.liftWeight D j, fun PP => GlobalTheory.ConjTwist.toCircle (Rl.chi ((j : ℕ) + 1) PP)⁻¹,
    fun _ => rfl, fun _ => rfl, fun P => ?_⟩
  exact
    { even := rV ▸ hr.add_odd D.R.t_odd
      odd := rW ▸ hr
      frame := hF
      de := hde
      places := hpl
      wt := GlobalTheory.ConjTwist.liftWeight_good D j
      sig := fun _ => rfl
      sigOK := D.sp.W_sig _
      eta := GlobalTheory.EtaTildeOfComponents.isEtaTilde_of_chrEq D Rl.C Rl.eta hL.eta (GlobalTheory.HeckeCharacterRestriction.resEta_eta hL)
      hecke := (hL.mu0 j).1
      real := GlobalTheory.GridWeil.triv_base (hL.mu0 j) (Rl.C.isMu0 j).triv
      unram := GlobalTheory.T.levelChoice_mu_unramified_outside_type_places D _ _ _ hL hS j
      tame := fun PP hPP x hx hi u hu => by
        have e1 := GlobalTheory.ConjTwist.eq_res_of_chrEq (hL.mu0 j) (hS.isIdemAt hPP) ((Rl.C.isMu0 j).tame PP) (hL.chi j PP hPP) x hx hi u hu
        have e2 := GlobalTheory.T.tame_residue_char_trivial_split_place_off_unramified D Circle de.chi de.Q Pa hde.unram hPa hPa2 PP (hPa1 hPP)
          (Finset.disjoint_left.1 hpl.disj hPP) x hx hi u hu
        show Rl.mu0 ((j : ℕ) + 1) x * de.chi x = GlobalTheory.ConjTwist.toCircle (Rl.chi ((j : ℕ) + 1) PP)⁻¹ u
        rw [e2, MonoidHom.one_apply, mul_one]
        exact Circle.ext e1
      inf := fun τ => by
        have e : ((GlobalTheory.ConjTwist.liftWeight D j).c τ : ℚ) - (((GlobalTheory.ConjTwist.liftWeight D j).p τ : ℚ) -
            (GlobalTheory.ConjTwist.liftWeight D j).q τ) / 2 + 1 / 2 = -(D.hc τ).e j := by
          have h := GlobalTheory.ConjTwist.liftC_cast D j τ
          simp only [GlobalTheory.ConjTwist.liftWeight]
          linarith
        rw [e]
        exact GlobalTheory.ConjRefChar.reference_lift_character_exponent_neg_base hL j τ }

end GlobalTheory.SeriesTie.BaseGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLatticeIndexCartanDecompositionEqNormPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.LocKerMod.FrameIdx

variable {K : Type} [Field K] {n : ℕ}

def colHom : (Fin n → K) →+ Matrix (Fin n) (Fin 1) K where
  toFun y := fun i _ => y i
  map_zero' := rfl
  map_add' _ _ := rfl

theorem colHom_injective : Function.Injective (colHom (K := K) (n := n)) :=
  fun x y h => funext fun i => congrFun (congrFun h i) 0

@[simp] theorem colHom_apply (y : Fin n → K) (i : Fin n) (j : Fin 1) : colHom y i j = y i := rfl

theorem colHom_mulVec (P : Matrix (Fin n) (Fin n) K) (y : Fin n → K) :
    colHom (P *ᵥ y) = GlobalTheory.SplitIdx.mulL (n := 1) P (colHom y) := by
  ext i j
  simp only [GlobalTheory.SplitIdx.mulL, AddMonoidHom.mk'_apply, colHom_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem mulL_one : GlobalTheory.SplitIdx.mulL (n := 1) (1 : Matrix (Fin n) (Fin n) K) = AddMonoidHom.id _ := by
  ext y : 1
  simp [GlobalTheory.SplitIdx.mulL]

end GlobalTheory.LocKerMod.FrameIdx

open GlobalTheory.LocKerMod.FrameIdx in

theorem GlobalTheory.LocKerMod.FrameIdx.idxAt_eq_pow : ∀ (D : D7) (T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (a : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.LFun.IsFrameAt w (frameLat T) a → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w T.rank, ∀ k₂ ∈ KGL w T.rank, ∀ g : GlobalTheory.FinZeta.Gv T v, GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g = a * (k₁ * t * k₂) * a⁻¹ → GlobalTheory.LocKerMod.idxAt T w h g = qV D.host.E w ^ (∑ i, max (d i) 0).toNat := by
  intro D T v w h a ha ϖ hϖ d t ht k₁ hk₁ k₂ hk₂ g hg
  set k : GL (Fin T.rank) (w.adicCompletion D.host.E) := k₁ * t * k₂ with hk
  set Lw := (GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup with hLw
  set M := GlobalTheory.SplitIdx.intMat D.host.E w T.rank 1 with hM
  let Φ : (Fin T.rank → w.adicCompletion D.host.E) →+ Matrix (Fin T.rank) (Fin 1) (w.adicCompletion D.host.E) :=
    colHom.comp (a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1.mulVecLin.toAddMonoidHom
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    have h1 : (a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ x =
        (a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ y := colHom_injective hxy
    have e := congrArg (fun z => a.1 *ᵥ z) h1
    simp only [Matrix.mulVec_mulVec] at e
    rwa [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, Matrix.one_mulVec] at e
  have hA : Lw.map Φ = M := by
    ext Y
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩ i j
      have hx' : a.1 *ᵥ ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ x) ∈ GlobalTheory.LFun.latAt w (frameLat T) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]; exact hx
      exact (ha _).2 hx' i
    · intro hY
      refine ⟨a.1 *ᵥ (fun i => Y i 0), (ha _).1 (fun i => hY i 0), ?_⟩
      refine Matrix.ext fun i j => ?_
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      show colHom ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ (a.1 *ᵥ fun i => Y i 0)) i 0 = Y i 0
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rfl
  have hB : (Lw.map (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1.mulVecLin.toAddMonoidHom).map Φ =
      M.map (GlobalTheory.SplitIdx.mulL (n := 1) k.1) := by
    rw [← hA, AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    refine AddMonoidHom.ext fun x => ?_
    show colHom ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ
        ((GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1 *ᵥ x)) =
      GlobalTheory.SplitIdx.mulL (n := 1) k.1 (colHom ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ x))
    rw [← colHom_mulVec, hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  have step1 : GlobalTheory.LocKerMod.idxAt T w h g = (M.map (GlobalTheory.SplitIdx.mulL (n := 1) k.1)).relIndex M := by
    unfold GlobalTheory.LocKerMod.idxAt
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hΦ, hB, hA]
  have hinv : (M.map (GlobalTheory.SplitIdx.mulL (n := 1) k.1)).map (GlobalTheory.SplitIdx.mulL (n := 1) (k⁻¹).1) = M := by
    rw [AddSubgroup.map_map, ← GlobalTheory.SplitIdx.LocIndex.mulL_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      mulL_one, AddSubgroup.map_id]
  have hinj : Function.Injective (GlobalTheory.SplitIdx.mulL (n := 1) (k⁻¹).1) := by
    intro x y hxy
    have e := congrArg (GlobalTheory.SplitIdx.mulL (n := 1) k.1) hxy
    simpa [GlobalTheory.SplitIdx.mulL, ← Matrix.mul_assoc, ← Units.val_mul] using e
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    have hv : Valued.v (0 : w.adicCompletion D.host.E) = _ := hϖ
    rw [map_zero] at hv
    exact WithZero.coe_ne_zero hv.symm
  have ht' : (t⁻¹).1 = Matrix.diagonal (fun i => ϖ ^ (-d i)) := by
    have e1 : t.1 * Matrix.diagonal (fun i => ϖ ^ (-d i)) = 1 := by
      rw [ht, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext i
      rw [← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero]
    calc (t⁻¹).1 = (t⁻¹).1 * (t.1 * Matrix.diagonal (fun i => ϖ ^ (-d i))) := by rw [e1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have hkinv : k⁻¹ = k₂⁻¹ * t⁻¹ * k₁⁻¹ := by rw [hk]; group
  rw [step1, ← AddSubgroup.relIndex_map_map_of_injective _ _ hinj, hinv, hkinv,
    GlobalTheory.SplitIdx.LocIndex.relIndex_intMat w T.rank 1 ϖ hϖ (fun i => -d i) t⁻¹ ht' k₂⁻¹ (inv_mem hk₂)
      k₁⁻¹ (inv_mem hk₁)]
  simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LowerRightBlockMulBlockTriangular
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Matrix

namespace GlobalTheory.FirstBlocksReduction

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.ExportSeries GlobalTheory.FlatVecSum

variable {D : D7} {S T : HSp D}
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem exists_reps {G X : Type} [Group G] (J J' : Subgroup G) (φ : G → X) (A : Set X) (hA : A.Finite)
    (hφ : ∀ κ ∈ J, φ κ ∈ A) (h : ∀ u ∈ J, ∀ κ ∈ J, u⁻¹ * κ ∈ J' ↔ φ u = φ κ) :
    ∃ F : Finset G, (∀ u ∈ F, u ∈ J) ∧ ∀ κ ∈ J, ∃! u : G, u ∈ F ∧ u⁻¹ * κ ∈ J' := by
  classical
  have hfin : (φ '' (J : Set G)).Finite := hA.subset (by rintro _ ⟨κ, hκ, rfl⟩; exact hφ κ hκ)
  have hs : ∀ x : ↥(φ '' (J : Set G)), ∃ u, u ∈ J ∧ φ u = x.1 := fun x => x.2
  choose s hsJ hsφ using hs
  haveI := hfin.fintype
  refine ⟨Finset.univ.image s, fun u hu => ?_, fun κ hκ => ⟨s ⟨φ κ, κ, hκ, rfl⟩, ⟨?_, ?_⟩, ?_⟩⟩
  · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hu
    exact hsJ x
  · exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · exact (h _ (hsJ _) _ hκ).2 (hsφ _)
  · rintro u ⟨hu, hu'⟩
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hu
    congr 1
    exact Subtype.ext ((hsφ x).symm.trans ((h _ (hsJ x) _ hκ).1 hu'))

theorem extension_by_one_mul {G H : Type} [Group G] [Monoid H] (K : Subgroup G) (f : K →* H) {a b : G} (ha : a ∈ K) (hb : b ∈ K) :
    ext1 K f (a * b) = ext1 K f a * ext1 K f b := by
  unfold ext1
  rw [dif_pos ha, dif_pos hb, dif_pos (mul_mem ha hb), ← map_mul]
  rfl

theorem lowerRightBlock_mul_blockTriangular {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) {a b : GL (Fin n) κ} (ha : a ∈ blockTri (blk2 r))
    (hb : b ∈ blockTri (blk2 r)) : upperLeftBlock hr (a * b) = upperLeftBlock hr a * upperLeftBlock hr b :=
  extension_by_one_mul _ _ ha hb

def firstBlocks (B : Base S T) (ψ : Twist D Circle) (k : Bridge.Gf S) : G0 B.G.Pg T.rank :=
  rTup B.F.βS (B.levS ψ) (Formalism.UG.bc (Lev.swapAE D) k.1)

theorem firstBlocks_mul (B : Base S T) (ψ : Twist D Circle) {a b : Bridge.Gf S} (ha : a ∈ B.levJ ψ) (hb : b ∈ B.levJ ψ) :
    firstBlocks B ψ (a * b) = firstBlocks B ψ a * firstBlocks B ψ b := by
  have pa := lev_le_parLev ha
  have pb := lev_le_parLev hb
  funext PP
  show upperLeftBlock B.hr (redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) (a.1 * b.1))) =
    upperLeftBlock B.hr (redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) a.1)) * upperLeftBlock B.hr (redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) b.1))
  have e : redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) a.1 * Formalism.UG.bc (Lev.swapAE D) b.1) =
      redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) a.1) * redFn B.F.βS PP.1 (Formalism.UG.bc (Lev.swapAE D) b.1) :=
    extension_by_one_mul (St B.F.βS) (redAt B.F.βS PP.1) (Base.mem_St_of_mem_levJ ha) (Base.mem_St_of_mem_levJ hb)
  rw [map_mul, e]
  exact lowerRightBlock_mul_blockTriangular _ (blockTri_blkOf_le _ _ (parLev_g pa PP.2)) (blockTri_blkOf_le _ _ (parLev_g pb PP.2))

theorem mem_princ_iff (B : Base S T) (ψ : Twist D Circle) {k : Bridge.Gf S} (hk : k ∈ B.levJ ψ) :
    k ∈ (princ B).levJ ψ ↔ firstBlocks B ψ k = 1 :=
  ⟨fun h => Subgroup.mem_bot.1 h.2, fun h => ⟨mem_parLev.2 (by exact mem_parLev.1 hk.1), Subgroup.mem_bot.2 h⟩⟩

theorem exists_reps_levJ : ∀ {D : Formalism.BasicNotions.D7} {S T : Formalism.BasicNotions.TH.HSp D} (B : GlobalTheory.ExportSeries.Base S T), GlobalTheory.ExportSeries.Base.Good B → ∀ (ψ : GlobalTheory.ExportSeries.Twist D Circle), GlobalTheory.ExportSeries.Base.admitted B (GlobalTheory.ExportSeries.Twist.Q ψ) → ∃ (F : Finset ↥(Formalism.IndefR.Bridge.Gf S)), (∀ u ∈ F, u ∈ GlobalTheory.ExportSeries.Base.levJ B ψ) ∧ ∀ κ ∈ GlobalTheory.ExportSeries.Base.levJ B ψ, ∃! u : ↥(Formalism.IndefR.Bridge.Gf S), u ∈ F ∧ u⁻¹ * κ ∈ GlobalTheory.ExportSeries.Base.levJ (GlobalTheory.FlatVecSum.princ B) ψ := by
  intro D S T B _ ψ _
  refine exists_reps _ _ (firstBlocks B ψ) (B.G.P.H : Set _) (Set.finite_coe_iff.1 (finite_H B.G.P)) (fun κ hκ => hκ.2)
    fun u hu κ hκ => ?_
  have hm := mul_mem (inv_mem hu) hκ
  have e := firstBlocks_mul B ψ hu hm
  rw [mul_inv_cancel_left] at e
  rw [mem_princ_iff B ψ hm, e]
  exact left_eq_mul.symm

end GlobalTheory.FirstBlocksReduction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCoeffFinitePlaceOffLevelConstMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.GoodFactor

theorem mt_mul' {D : D7} (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_one' {D : D7} (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [map_one, Units.val_one]

theorem mt_inj {D : D7} (V : HSp D) {a b : GA D V} (h : mt V a = mt V b) : a = b :=
  Subtype.val_injective (Units.ext h)

theorem comm_of_supp_triv {D : D7} {V : HSp D} {f : AE D} {a b : GA D V} (ha : SuppF V f a) (hb : TrivAt V f b) :
    a * b = b * a := by
  apply mt_inj
  have hAB : (mt V a - 1) * (mt V b - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha i l, mul_assoc, mul_left_comm, hb l j, mul_zero]
  have hBA : (mt V b - 1) * (mt V a - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha l j, mul_left_comm, ← mul_assoc, hb i l, zero_mul]
  have e1 : mt V a * mt V b = (mt V a - 1) * (mt V b - 1) + mt V a + mt V b - 1 := by noncomm_ring
  have e2 : mt V b * mt V a = (mt V b - 1) * (mt V a - 1) + mt V b + mt V a - 1 := by noncomm_ring
  rw [mt_mul', mt_mul', e1, e2, hAB, hBA, zero_add, zero_add, add_comm (mt V a)]

theorem actO_one_of_trivAt {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f) {γ : GA D T} (hγ : TrivAt T f γ)
    {u : WO S T} (hu : u ∈ latO S T LS LT fun w => w = v) : actO S T 1 γ u = u := by
  obtain ⟨ε, hε, rfl⟩ := hf
  have hu' := GlobalTheory.VecInvInert.idem_smul_eq hε hu
  have hz : algebraMap (AF D.host.F) (AE D) ε • (mt T γ - 1) = 0 := by
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    exact hγ a b
  have h0 : HMul.hMul (mt T γ - 1) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = (0 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    rw [← hu', Matrix.mul_smul, ← Matrix.smul_mul, hz, Matrix.zero_mul]
  unfold actO
  rw [inv_one, mt_one', Matrix.mul_one]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h0
  exact h0

theorem vacFin_om_trivAt {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f) {γ : GA D T} (hγ : TrivAt T f γ)
    {x : WO S T → ℂ} (hx : GlobalTheory.FinZeta.VacFin ψ S T v x) : GlobalTheory.FinZeta.VacFin ψ S T v (om (1, γ) x) := by
  obtain ⟨hth, hl1, hl2⟩ := hx
  refine ⟨hW.om_pres _ _ hth, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · rw [← actO_one_of_trivAt hf hγ (nsmul_mem hu 2), ← hW.om_heis 1 γ _ x hth, hl1 u hu]
  · rw [← actO_one_of_trivAt hf hγ hu, ← hW.om_heis 1 γ _ x hth, hl2 e he u hu hh]

theorem thetaInner_eq_star_l2 {D : D7} {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (x y : WO S T' → ℂ) :
    thetaIP μ 𝓕 x y = star (GlobalTheory.AdelicScalar.l2 μ 𝓕 x y) := by
  unfold thetaIP GlobalTheory.AdelicScalar.l2 Formalism.IndefR.Lift.pet
  show _ = (starRingEnd ℂ) _
  rw [← integral_conj]
  congr 1; funext w
  simp [mul_comm]

theorem finmult_good : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v f, IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → ∀ k, SuppF (Wc D i) f k → ∃ c : ℂ, ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → thetaIP μ 𝓕 (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) = c * thetaIP μ 𝓕 (R.ωP i t (1, γ) (R.vP i t)) (R.vP i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t μ 𝓕 hμ v f hf hoff k hk
  obtain ⟨a, rfl⟩ := GlobalTheory.T.exists_local_preimage_of_supportedAtPlace D (Wc D i) v f hf k hk
  have hW := hL.thP.ωP i t
  have hvac := GlobalTheory.T.pairFixedVector_latticeVacuum_offLevels D G Pl0 T A Ks R F hL i t v f hf hoff
  have hunr := GlobalTheory.T.weilDatumCharacters_unramified_offLevels D G Pl0 T A Ks R F hL i t v f hf hoff
  obtain ⟨φ, -, hc⟩ := GlobalTheory.VacCoef.vac_coef D R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) hW μ 𝓕 hμ v hunr
  refine ⟨star (φ a), fun γ _ hγ => ?_⟩
  have hcomm := comm_of_supp_triv hk hγ
  have hv' := vacFin_om_trivAt hW hf hγ hvac
  have e : R.ωP i t (1, γ * GlobalTheory.FinZeta.embV (Wc D i) v a) (R.vP i t) =
      R.ωP i t (1, GlobalTheory.FinZeta.embV (Wc D i) v a) (R.ωP i t (1, γ) (R.vP i t)) := by
    rw [← hcomm]
    show _ = (R.ωP i t (1, _) * R.ωP i t (1, γ)) (R.vP i t)
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e, thetaInner_eq_star_l2, thetaInner_eq_star_l2 μ 𝓕 (R.ωP i t (1, γ) (R.vP i t)), hc a _ _ hv' hvac, star_mul']

end GlobalTheory.RawLift.GoodFactor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinTypeIntegralEntireOfRapidDecay
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.MellinEntire

lemma min_inv_pos {t : ℝ} (ht : 0 < t) : 0 < min t t⁻¹ := lt_min ht (inv_pos.mpr ht)

lemma min_inv_le_one {t : ℝ} (ht : 0 < t) : min t t⁻¹ ≤ 1 := by
  rcases le_total t 1 with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (inv_le_one_of_one_le₀ h)

lemma le_inv_of_le_one' {t : ℝ} (ht : 0 < t) (h : t ≤ 1) : t ≤ t⁻¹ :=
  h.trans ((one_le_inv₀ ht).mpr h)

lemma inv_le_of_one_le' {t : ℝ} (h : 1 ≤ t) : t⁻¹ ≤ t :=
  (inv_le_one_of_one_le₀ h).trans h

lemma rpow_mul_min_pow_le {t σ : ℝ} {K : ℕ} (ht : 0 < t) (hσ : |σ| ≤ K) :
    t ^ σ * (min t t⁻¹) ^ K ≤ 1 := by
  rcases le_total t 1 with h | h
  · rw [min_eq_left (le_inv_of_le_one' ht h)]
    have h1 : t ^ σ ≤ t ^ (-(K:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge ht h (by linarith [neg_abs_le σ])
    calc t ^ σ * t ^ K ≤ t ^ (-(K:ℝ)) * t ^ K := by gcongr
      _ = 1 := by
        rw [Real.rpow_neg ht.le, Real.rpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ ht.ne')]
  · rw [min_eq_right (inv_le_of_one_le' h)]
    have h1 : t ^ σ ≤ t ^ (K:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h (le_trans (le_abs_self σ) hσ)
    calc t ^ σ * t⁻¹ ^ K ≤ t ^ (K:ℝ) * t⁻¹ ^ K := by gcongr
      _ = 1 := by rw [Real.rpow_natCast, ← mul_pow, mul_inv_cancel₀ ht.ne', one_pow]

lemma min_mul_abs_log_le {t : ℝ} (ht : 0 < t) : min t t⁻¹ * |Real.log t| ≤ 1 := by
  rcases le_total t 1 with h | h
  · rw [min_eq_left (le_inv_of_le_one' ht h)]
    have := Real.abs_log_mul_self_lt t ht h
    rw [abs_mul, abs_of_pos ht] at this
    linarith
  · rw [min_eq_right (inv_le_of_one_le' h)]
    have := Real.abs_log_mul_self_lt t⁻¹ (inv_pos.mpr ht) (inv_le_one_of_one_le₀ h)
    rw [Real.log_inv, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr ht)] at this
    linarith

theorem integrable_and_differentiable {X : Type} [MeasurableSpace X] (ν : Measure X)
    (A : X → ℂ) (T : X → ℝ)
    (hA : AEStronglyMeasurable A ν) (hT : Measurable T) (hTpos : ∀ x, 0 < T x)
    (hw : Integrable (fun x => min (T x) (T x)⁻¹) ν)
    (hdec : ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C * (min (T x) (T x)⁻¹) ^ N) :
    (∀ s : ℂ, Integrable (fun x => A x * ((T x : ℝ) : ℂ) ^ s) ν) ∧
      Differentiable ℂ (fun s : ℂ => ∫ x, A x * ((T x : ℝ) : ℂ) ^ s ∂ν) := by
  have wpos : ∀ x, 0 < min (T x) (T x)⁻¹ := fun x => min_inv_pos (hTpos x)
  have wle : ∀ x, min (T x) (T x)⁻¹ ≤ 1 := fun x => min_inv_le_one (hTpos x)
  have hTc : Measurable fun x => ((T x : ℝ) : ℂ) := Complex.measurable_ofReal.comp hT
  have meas : ∀ s : ℂ, AEStronglyMeasurable (fun x => A x * ((T x : ℝ) : ℂ) ^ s) ν :=
    fun s => hA.mul (hTc.pow_const s).aestronglyMeasurable
  have bnd : ∀ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x (s : ℂ), |s.re| ≤ K →
      ‖A x * ((T x : ℝ) : ℂ) ^ s‖ ≤ C * (min (T x) (T x)⁻¹) ^ 2 := by
    intro K
    obtain ⟨C, hC⟩ := hdec (K + 2)
    refine ⟨|C|, abs_nonneg _, fun x s hs => ?_⟩
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hTpos x)]
    have hA' : ‖A x‖ ≤ |C| * (min (T x) (T x)⁻¹) ^ (K + 2) :=
      (hC x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (wpos x).le _))
    have h2 := rpow_mul_min_pow_le (hTpos x) hs
    have h0 : 0 ≤ T x ^ s.re := Real.rpow_nonneg (hTpos x).le _
    calc ‖A x‖ * T x ^ s.re ≤ |C| * (min (T x) (T x)⁻¹) ^ (K + 2) * T x ^ s.re :=
          mul_le_mul_of_nonneg_right hA' h0
      _ = |C| * (min (T x) (T x)⁻¹) ^ 2 * (T x ^ s.re * (min (T x) (T x)⁻¹) ^ K) := by ring
      _ ≤ |C| * (min (T x) (T x)⁻¹) ^ 2 * 1 := by
          gcongr
      _ = |C| * (min (T x) (T x)⁻¹) ^ 2 := mul_one _
  have sq_le : ∀ x, (min (T x) (T x)⁻¹) ^ 2 ≤ min (T x) (T x)⁻¹ := fun x => by
    nlinarith [wpos x, wle x]
  refine ⟨fun s => ?_, fun s₀ => ?_⟩
  · obtain ⟨C, hC0, hC⟩ := bnd ⌈|s.re|⌉₊
    refine Integrable.mono' (hw.const_mul C) (meas s) (ae_of_all _ fun x => ?_)
    exact (hC x s (Nat.le_ceil _)).trans (mul_le_mul_of_nonneg_left (sq_le x) hC0)
  · obtain ⟨C, hC0, hC⟩ := bnd (⌈|s₀.re|⌉₊ + 1)
    have hre : ∀ s ∈ Metric.ball s₀ 1, |s.re| ≤ ((⌈|s₀.re|⌉₊ + 1 : ℕ) : ℝ) := by
      intro s hs
      rw [Metric.mem_ball, dist_eq_norm] at hs
      have h1 : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
        rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
      have h2 : |s.re| ≤ |s₀.re| + |s.re - s₀.re| := by
        have := abs_add_le s₀.re (s.re - s₀.re); simpa using this
      have h3 := Nat.le_ceil |s₀.re|
      push_cast
      linarith
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
      (F := fun s x => A x * ((T x : ℝ) : ℂ) ^ s)
      (F' := fun s x => A x * (((T x : ℝ) : ℂ) ^ s * Complex.log ((T x : ℝ) : ℂ)))
      (x₀ := s₀) (bound := fun x => C * min (T x) (T x)⁻¹) (s := Metric.ball s₀ 1) (Metric.ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall fun s => meas s) ((fun s => ?_ : ∀ s : ℂ,
        Integrable (fun x => A x * ((T x : ℝ) : ℂ) ^ s) ν) s₀)
      (hA.mul ((hTc.pow_const s₀).mul (Complex.measurable_log.comp hTc)).aestronglyMeasurable)
      (ae_of_all _ fun x s hs => ?_) (hw.const_mul C)
      (ae_of_all _ fun x s _ => ?_)
    · exact key.2.differentiableAt
    · obtain ⟨C', hC0', hC'⟩ := bnd ⌈|s.re|⌉₊
      refine Integrable.mono' (hw.const_mul C') (meas s) (ae_of_all _ fun x => ?_)
      exact (hC' x s (Nat.le_ceil _)).trans (mul_le_mul_of_nonneg_left (sq_le x) hC0')
    · show ‖A x * (((T x : ℝ) : ℂ) ^ s * Complex.log ((T x : ℝ) : ℂ))‖ ≤ C * min (T x) (T x)⁻¹
      rw [← mul_assoc, norm_mul, ← Complex.ofReal_log (hTpos x).le, Complex.norm_real,
        Real.norm_eq_abs]
      have h1 := hC x s (hre s hs)
      have h2 := min_mul_abs_log_le (hTpos x)
      calc ‖A x * ((T x : ℝ) : ℂ) ^ s‖ * |Real.log (T x)|
          ≤ C * (min (T x) (T x)⁻¹) ^ 2 * |Real.log (T x)| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = C * min (T x) (T x)⁻¹ * (min (T x) (T x)⁻¹ * |Real.log (T x)|) := by ring
        _ ≤ C * min (T x) (T x)⁻¹ * 1 := by
            gcongr
            exact mul_nonneg hC0 (wpos x).le
        _ = C * min (T x) (T x)⁻¹ := mul_one _
    · have hne : ((T x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hTpos x).ne'
      exact (Complex.hasStrictDerivAt_const_cpow (Or.inl hne)).hasDerivAt.const_mul (A x)

end GlobalTheory.MellinEntire
end

