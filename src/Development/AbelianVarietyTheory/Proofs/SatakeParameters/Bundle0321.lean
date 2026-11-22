import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0007
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PNeatB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0314
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0315
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0308
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0040
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0095
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0184
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0310
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0226
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0196
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0198
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0234
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0252
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorEigenGoodPlaceSecond
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0312

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledLatticeVectorMemDualBaseLatticeCompletion
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col GlobalTheory.TwU Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.MemDual

theorem prV_inclE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e) = inclE (F := F) (v.adicCompletion F) e := by
  simp [prV, inclE]

theorem prV_sigR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    prV (E := E) v (sigR σ (FiniteAdeleRing (𝓞 F) F) x) = sigR σ (v.adicCompletion F) (prV (E := E) v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul a b => simp [prV, sigR]

theorem bc_prV_mem_UPts {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    {k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hk : k ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    bc (prV (E := E) v) k ∈ UPts σ J (v.adicCompletion F) := by
  have hg' : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (k : Matrix (Fin n) (Fin n) _) *
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * (k : Matrix (Fin n) (Fin n) _) =
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := hk
  change cT (sigR σ (v.adicCompletion F)) ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) *
      J.map (inclE (F := F) (v.adicCompletion F)) * ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) =
      J.map (inclE (F := F) (v.adicCompletion F))
  have h1 : cT (sigR σ (v.adicCompletion F)) ((k : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) =
      (cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (k : Matrix (Fin n) (Fin n) _)).map (prV (E := E) v) := by
    ext i j
    simp [cT, prV_sigR]
  have hJ' : (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).map (prV (E := E) v) =
      J.map (inclE (F := F) (v.adicCompletion F)) := by
    ext i j
    simp [prV_inclE]
  rw [h1, ← hJ', ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem pullV_ratA_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (c : GL (Fin N) E) (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (y : Fin N → E) :
    pullV (F := F) (ratA F c * x) ((c : Matrix (Fin N) (Fin N) E) *ᵥ y) =
      ((x⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) *ᵥ fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y i) := by
  unfold pullV
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  congr 1
  have hc : (((ratA F c)⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) =
      ((c⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) := by
    rw [← map_inv]; rfl
  rw [hc]
  ext i
  have := RingHom.map_mulVec (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))
    ((c⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) ((c : Matrix (Fin N) (Fin N) E) *ᵥ y) i
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  rw [this]; rfl

end GlobalTheory.MemDual

namespace GlobalTheory.MemDual

theorem mem_latS_dual_of_latCo : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), IsUnit J.det → ∀ (c : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F) →
    ∀ (Lb : Submodule (𝓞 E) (Fin N → E)), Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ →
    (∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb) → ∀ (v : HeightOneSpectrum (𝓞 F)) (y : Fin N → E),
    y ∈ latCo sp J c a x Lb →
    (fun l => prV (E := E) v (pullV (F := F) (ratA F c * x) y l)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)) := by
  intro R F E _ _ _ _ _ _ sp N J hJ c a x hx Lb hfin hspan hdual v y hy
  obtain ⟨y', hy', rfl⟩ := hy
  set σ : E →ₐ[F] E := sp.cm.sig with hσ
  set Λ := latAd x Lb with hΛ
  set xv := bc (prV (E := E) v) x with hxv
  have hLb : Submodule.IsLattice E Lb := ⟨Module.Finite.iff_fg.mp hfin, hspan⟩
  have hLam : Submodule.IsLattice E Λ := by
    have hlat : Formalism.L2.PairingIndexBounds.F.latAd x Lb = Formalism.UG.CS.globLat x Lb := Submodule.span_eq (Formalism.UG.CS.globLat x Lb)
    rw [hΛ, hlat]
    exact Formalism.UG.P.csGlob_lattice Lb hfin hspan x
  have hxU : xv ∈ UPts σ J (v.adicCompletion F) := bc_prV_mem_UPts σ J v hx
  have hcarry := GlobalTheory.LocCarry.mem_latS_latAd_iff x Lb hfin hspan v

  have hpull : (fun l => prV (E := E) v (pullV (F := F) (ratA F c * x) ((c : Matrix (Fin N) (Fin N) E) *ᵥ y') l)) =
      ((xv⁻¹ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) *ᵥ fun i => inclE (F := F) (v.adicCompletion F) (y' i) := by
    rw [pullV_ratA_mul, GlobalTheory.LocCarry.prV_mulVec, hxv, GlobalTheory.LocCarry.coe_bc_inv]
    congr 1
  show (fun l => prV (E := E) v (pullV (F := F) (ratA F c * x) ((c : Matrix (Fin N) (Fin N) E) *ᵥ y') l)) ∈ _
  rw [hpull]

  have hsub : compan (sp := sp) J a Λ ≤ Λ ⊔ dualL (σ : E →+* E) J Λ :=
    sup_le_sup_left (Submodule.smul_le_right) _
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp (hsub hy')
  have hadd : (fun i => inclE (F := F) (v.adicCompletion F) ((p + q) i)) =
      (fun i => inclE (F := F) (v.adicCompletion F) (p i)) + fun i => inclE (F := F) (v.adicCompletion F) (q i) := by
    ext i; simp
  rw [hadd, Matrix.mulVec_add]
  have hmono : latS (F := F) (v.adicCompletion F) (intV E v) Lb ≤
      latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J Lb) :=
    Submodule.span_mono (Set.image_mono fun z hz => Submodule.subset_span (hdual z hz))
  refine add_mem ?_ ?_
  · exact hmono ((hcarry _).1 (Submodule.subset_span ⟨p, hp, rfl⟩))
  · exact (GlobalTheory.DualCompletion.dual_move F E σ N J v Λ Lb xv hJ hLam hLb hxU hcarry _).1
      (Submodule.subset_span ⟨q, hq, rfl⟩)

end GlobalTheory.MemDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalMatrixEntriesCongruentOneOfAdelicCongrueStatement
section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalMatrix_entries_congruent_one_of_adelic_congruent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Q : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (g : GL (Fin N) E), GlobalTheory.TwU.CongAt (F := F) Q n (GlobalTheory.TwU.ratA F g) → ∀ a b : Fin N, Formalism.L2.Col.IntAt Q ((((Formalism.L2.Col.qOf Q : ℕ) : E) ^ n)⁻¹ * ((g : Matrix (Fin N) (Fin N) E) a b - (1 : Matrix (Fin N) (Fin N) E) a b)) := by
  first | exact @GlobalTheory.TwU.ratA_congAt_entry | exact GlobalTheory.TwU.ratA_congAt_entry | (intros; apply GlobalTheory.TwU.ratA_congAt_entry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueCardColumnFieldPrimeToHostPrimeEqStatement
section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueCard_columnFieldPrimeToHostPrime_eq : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.Col.Fields) (s : Formalism.L2.Ker.Seam D X) (P : HeightOneSpectrum (𝓞 X.E)), Formalism.L2.Col.qOf (GlobalTheory.TwU.seamP s P) = Formalism.L2.Col.qOf P := by
  first | exact @GlobalTheory.qOf_seamP | exact GlobalTheory.qOf_seamP | (intros; apply GlobalTheory.qOf_seamP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowFormsCoefficientFieldFormComplexPeriodRowsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowForms_coefficientField_form_complexPeriodRows : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : GlobalTheory.Mem.Col2.TC B X) (h : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι), (∀ s : Finset (Formalism.L2.Col.MtildeV (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps), LinearIndependent B.LL (fun x : s => x.1) → LinearIndependent ℂ (fun x : s => GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a x.1)) ∧ Submodule.span ℂ (Set.range (GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a)) = ⊤ := by
  first | exact @GlobalTheory.Mem.Col2.KerRat.rowForm_baseChange | exact GlobalTheory.Mem.Col2.KerRat.rowForm_baseChange | (intros; apply GlobalTheory.Mem.Col2.KerRat.rowForm_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsAOfJumpCount
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowsAClose

theorem main : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), JumpsCard D.nd D.naut → GlobalTheory.NRows.RowsA D := by
  intro hP hL D P hJ
  have hlab := GlobalTheory.TieLabAt.main hL D P
  have hrig : IsobaricRigid D.nd D.naut := GlobalTheory.NPin.isobaricRigid_of_pin hP.fin hP.js hL D P
  have han1 := GlobalTheory.RowClose.isobaricCuspidalMultiplicityOne_of_twisted _ _ _ D.nd D.naut hrig
  have han2 := GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne _ _ _ D.nd D.naut hrig
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hP.cheb D
  have ha5 : Formalism.MainNotions.SumRepresentations.adm5 D := (Formalism.MainNotions.SumRepresentations.condition_iff_additive_maps D).2 ⟨han1, han2, fun Sg hSg => by
    have hd := (hcheb hSg.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]⟩
  have haut := GlobalTheory.AutomorphismSplitting.tieAut_and_split hP.fin hL D P
  have htie0 : Formalism.MainNotions.SumRepresentations.tie0 D :=
    ⟨GlobalTheory.RowTieLP.main D P.T, haut.1, GlobalTheory.T.galois_compatibility_of_jumps hP.berger hL D P hJ⟩
  have ha2 : Formalism.MainNotions.SumRepresentations.adm2 D := GlobalTheory.GalClose.main hP hL D P
  have ha7 : Formalism.MainNotions.SumRepresentations.adm7 D := GlobalTheory.TempGal.main hP.fin hP.gal hL D P
  have heig := GlobalTheory.EigConcrete.main hP.berger hL D P
  refine ⟨hlab.1, GlobalTheory.RowClose.heckeSplitOne_of_charTied D P.cf P.C P.tp P.chr, htie0, ha2, han1, han2, ha5, ha7,
    GlobalTheory.LocalInvEta.noLocalInvariants_everywhere D P.T htie0 ha2 ha5 ha7
      (GlobalTheory.MuIntegral.muInt_of_charTied D P.cf P.C P.tp P.chr) (GlobalTheory.GoodCuspPoint.main D hlab.1) heig.1 heig.2,
    haut.2⟩

end GlobalTheory.RowsAClose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsCOfLocalLiftsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_c_of_local_lifts : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), Join P → GlobalTheory.NRows.RowsA D → GlobalTheory.NRows.RowsB D → Formalism.MainNotions.SumRepresentations.adm1 D → Formalism.MainNotions.SumRepresentations.adm8 D → Formalism.MainNotions.SumRepresentations.Conclusion1 D → (∀ i, PairLift D.nd D.naut i ∧ SplitBC D.nd D.naut i ∧ RepOfLoc D.nd D.naut i) → GlobalTheory.NRows.RowsC D := by
  first | exact @GlobalTheory.RowsCClose.main | exact GlobalTheory.RowsCClose.main | (intros; apply GlobalTheory.RowsCClose.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SameCouplingCosetInvariantFrameCongruentOneStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sameCouplingCoset_invariant_frame_congruent_one : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) {n : ℕ} (κ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (y0 : Sp X.E n), cst.Ok →
  κ ∈ GLint X.E n P.1 → (∀ w ∈ stdAt X.E n P.1, ((qOf P.1 : X.E) ^ cst.D P)⁻¹ • (κ w - w) ∈ stdAt X.E n P.1) →
  (P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) →
  (P.1 ∈ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) * y0 l)) → (P.1 ∉ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y0 l)) →
  ∀ w, SameCoset sel mu cst P (κ.symm w) y0 ↔ SameCoset sel mu cst P w y0 := by
  first | exact @GlobalTheory.CosetLoc.sameCoset_symm_iff | exact GlobalTheory.CosetLoc.sameCoset_symm_iff | (intros; apply GlobalTheory.CosetLoc.sameCoset_symm_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceHeckeSatakeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_hecke_satake : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (sp : SplitPlace D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) sp.w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (sp.w.under (𝓞 D.host.F)) → (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) sp.w d → ∃ Ds : Set (GAf D.host.E D.R.nV), (∀ x ∈ Ds, TrivOutside {sp.v} x) ∧ (∀ x ∈ Ds, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) ∧ {c : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J | ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c}.Finite ∧ ∀ (f : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) (c : ℂ), (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w d, X.fn hμ j f (g * γ) = c • X.fn hμ j f g) → NG.heckeD (P.M.loc i).J Ds ((P.M.loc i).real (hj ▸ f)) = c • (P.M.loc i).real (hj ▸ f) := by
  first | exact @GlobalTheory.LabelTransport.transport_label | exact GlobalTheory.LabelTransport.transport_label | (intros; apply GlobalTheory.LabelTransport.transport_label <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentComponentOneDeterminesPart
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.PlaceSupp

theorem finPart_surjective (D : D7) : Function.Surjective (Formalism.L2.Theta.finPart D) := by
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a x =>
    exact ⟨((0, a) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ⊗ₜ[D.host.F] x, rfl⟩
  | add y z hy hz =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    exact ⟨a + b, (Formalism.L2.Theta.finPart D).map_add a b⟩

theorem comp_idem : ∀ (D : D7) (sp : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E)
    (p : GlobalTheory.LocMod.Place D (sp.w.adicCompletion D.host.E))
    (c : sp.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* sp.w.adicCompletion D.host.E),
    (∀ a : Formalism.L2.Theta.AE D, p.π a = c (sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)))) →
    sp.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D p.e)) = 1 ∧
      ∀ x y, sp.proj (GlobalTheory.NJoin.tensCast hF x) = sp.proj (GlobalTheory.NJoin.tensCast hF y) →
        Formalism.L2.Theta.finPart D p.e * x = Formalism.L2.Theta.finPart D p.e * y := by
  intro D sp hF p c hπ
  have hι1 : p.ι 1 = p.e := by
    have := p.ι_π 1
    rwa [map_one, mul_one] at this
  have hπe : p.π p.e = 1 := by rw [← hι1, p.π_ι]
  refine ⟨?_, ?_⟩
  · apply c.injective
    rw [← hπ, hπe, map_one]
  · intro x y hxy
    obtain ⟨a, rfl⟩ := finPart_surjective D x
    obtain ⟨b, rfl⟩ := finPart_surjective D y
    have hab : p.π a = p.π b := by rw [hπ, hπ, hxy]
    have key : p.e * a = p.e * b := by rw [← p.ι_π, ← p.ι_π, hab]
    rw [← map_mul, ← map_mul, key]

end GlobalTheory.PlaceSupp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameConjGLintLeSelfDualLatticeStabilize
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.SplitFrameLattice

set_option maxHeartbeats 1000000 in

theorem glint_mul_frame_basis : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V V.rank) (sp : SplitPlace D.host.E)
    (β β' : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)),
    β * β' = 1 → β' * β = 1 →
    (∀ κ, Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (Ps.ψ κ) =
      β * ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map (GlobalTheory.NJoin.tensCast hF).symm) * β') →
    (∀ κ, κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank ↔ Ps.ψ κ ∈ Formalism.L2.Theta.KsphC V ∅) →
    ∀ (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
      (sec : sp.v.adicCompletion (maximalRealSubfield D.host.E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
      (B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)),
    (∀ t, sp.proj (GlobalTheory.NJoin.tensCast hF (sec t)) = t) →
    (∀ t ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E), sec t ∈ Formalism.L2.Theta.intAE D) →
    (∀ x ∈ Formalism.L2.Theta.intAE D,
      sp.proj (GlobalTheory.NJoin.tensCast hF x) ∈ sp.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) →
    sp.proj (GlobalTheory.NJoin.tensCast hF ε) = 1 →
    (∀ z, Formalism.IndefR.Mult.IntVec z → (fun a => ε * B.mulVec z a) ∈ Formalism.L2.NTheta.LamHat V) →
    (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z, Formalism.IndefR.Mult.IntVec z ∧ (fun a => ε * y a) = fun a => ε * B.mulVec z a) →
    ∀ g ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v),
    ∀ z : Fin V.rank → sp.v.adicCompletion (maximalRealSubfield D.host.E),
      (∀ i, z i ∈ Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) →
      ∃ z' : Fin V.rank → sp.v.adicCompletion (maximalRealSubfield D.host.E),
        (∀ i, z' i ∈ Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) ∧
        (g : Matrix (Fin V.rank) (Fin V.rank) _).mulVec
            ((β'.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) *
              B.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x))).mulVec z) =
          (β'.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) *
              B.map (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x))).mulVec z' := by
  intro D hF V Ps sp β β' hββ' hβ'β hfr hK ε sec B hsec hsecI hint hε b1 b2 g hg z hz
  let φ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+*
      sp.v.adicCompletion (maximalRealSubfield D.host.E) :=
    sp.proj.comp (GlobalTheory.NJoin.tensCast hF).toRingHom
  have hfun : (fun x => sp.proj (GlobalTheory.NJoin.tensCast hF x)) = ⇑φ := rfl
  have hφε : φ ε = 1 := hε
  rw [hfun]
  obtain ⟨emb, htriv, hloc⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc D.host.E V.rank sp
  have hκ : emb g ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank :=
    GlobalTheory.SplitHeckeComm.mem_Umax_of_loc sp (emb g) (htriv g) (by rw [hloc]; exact hg)
  have hKs := (hK (emb g)).1 hκ
  have hz0 : Formalism.IndefR.Mult.IntVec (sec ∘ z) := fun i => hsecI _ (hz i)
  have hy := b1 _ hz0
  have hy' := (hKs.2.1 _).1 hy
  obtain ⟨z'', hz'', e⟩ := b2 _ hy'
  refine ⟨φ ∘ z'', fun i => hint _ (hz'' i), ?_⟩
  have mv : ∀ (M : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) x,
      φ ∘ (M.mulVec x) = (M.map φ).mulVec (φ ∘ x) := fun M x => funext fun i => RingHom.map_mulVec φ M x i
  have hε' : ∀ w : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      φ ∘ (fun a => ε * w a) = φ ∘ w := fun w => funext fun a => by
    simp only [Function.comp_apply, map_mul, hφε, one_mul]
  have hg' : (((emb g).1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map
      (GlobalTheory.NJoin.tensCast hF).symm).map φ = (g : Matrix (Fin V.rank) (Fin V.rank) _) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    show sp.proj (GlobalTheory.NJoin.tensCast hF ((GlobalTheory.NJoin.tensCast hF).symm _)) = _
    rw [RingEquiv.apply_symm_apply]
    conv_rhs => rw [← hloc g]
    rfl
  have hM : (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (Ps.ψ (emb g))).map φ =
      β.map φ * (g : Matrix (Fin V.rank) (Fin V.rank) _) * β'.map φ := by
    rw [hfr (emb g), Matrix.map_mul, Matrix.map_mul, hg']
  have hzφ : φ ∘ (sec ∘ z) = z := funext fun i => hsec _
  have hβ : β'.map φ * β.map φ = 1 := by
    rw [← Matrix.map_mul, hβ'β, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have E := congrArg (fun w => φ ∘ w) e
  rw [hε', hε', mv, mv, hε', mv, hzφ, hM] at E
  have E2 := congrArg (fun w => (β'.map φ).mulVec w) E
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hβ, Matrix.one_mul] at E2
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
  exact E2

end GlobalTheory.SplitFrameLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameMemHyperspecialIffMaxCompactTrivOut
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.FrameHyp.mem_hyp_iff : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ}
    (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → ∀ (sp : SplitPlace D.host.E)
    (κ : Formalism.AUTREP.GAf D.host.E n), Ps.ψ κ ∈ GlobalTheory.Hk3.hyp V sp.w ↔ κ ∈ Umax D.host.E n ∧ TrivOutside {sp.v} κ := by
  intro D hF V n Ps hstd sp κ
  constructor
  · rintro ⟨hK, e, f, hef, hs⟩
    exact ⟨(hstd.2 κ).2 hK,
      (GlobalTheory.LabelTransport.suppF_iff_trivOutside D sp hF V n Ps hstd e f hef κ).1 hs⟩
  · rintro ⟨hU, hT⟩
    obtain ⟨-, e, f, hef, -⟩ := GlobalTheory.DefLiftHecke.one_mem_hyp V sp.w
    exact ⟨(hstd.2 κ).1 hU, e, f, hef,
      (GlobalTheory.LabelTransport.suppF_iff_trivOutside D sp hF V n Ps hstd e f hef κ).2 hT⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardFrameSphericalDoubleCosetRepsLocal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitFrameReps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pre_mul_eq {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (Ψ : Formalism.IndefR.principalLevelFrame.RowPsi V n) (x : Formalism.AUTREP.GAf D.host.E n) :
    Formalism.IndefR.principalLevelFrame.pre Ψ (Ψ.ψ x) = x :=
  Ψ.inj (Formalism.IndefR.principalLevelFrame.pre_spec Ψ (Ψ.into x))

theorem frame_reps : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (Ψ : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ψ → ∀ (Pp : HeightOneSpectrum (𝓞 D.host.E)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab V Pp d → ∃ (s : SplitPlace D.host.E) (α : Formalism.AUTREP.GAf D.host.E n), Formalism.L2.NG.OverPl Pp s.v ∧ TrivOutside {s.v} α ∧ (∀ γ ∈ GlobalTheory.Hk3.rep V Pp d, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, Formalism.IndefR.principalLevelFrame.pre Ψ γ = k₁ * α * k₂) ∧ ∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ GlobalTheory.Hk3.rep V Pp d ∧ (Formalism.IndefR.principalLevelFrame.pre Ψ γ)⁻¹ * x ∈ Umax D.host.E n := by
  intro D V n hF Ψ hΨ Pp hS d hd
  obtain ⟨s, hs⟩ := GlobalTheory.OffBad.splitPlace_of_isSplitPl D Pp (GlobalTheory.OffBad.isSplitPl_of_isSplit D Pp hS)
  have hv : Formalism.L2.NG.OverPl Pp s.v := by rw [← hs]; exact s.w_under
  have hrep : GlobalTheory.Hk3.rep V Pp d = hd.choose := by unfold GlobalTheory.Hk3.rep; rw [dif_pos hd]
  obtain ⟨e, f, ϖ, α, -, hP, -, -, -, -, -, hα, -, hRs, hR⟩ := hd.choose_spec
  rw [hrep]
  have hK : ∀ k, k ∈ GlobalTheory.HeckeScalarSph.locK n s.v ↔
      Ψ.ψ k ∈ {k | k ∈ Formalism.L2.Theta.KsphC V ∅ ∧ Formalism.IndefR.Mult.SuppF V f k} :=
    fun k => and_congr (hΨ.2 k) (GlobalTheory.InertTransport.suppF_iff hF Ψ hΨ hP hv k).symm
  have h1 : (1 : Formalism.L2.Theta.GA D V) ∈ {k | k ∈ Formalism.L2.Theta.KsphC V ∅ ∧ Formalism.IndefR.Mult.SuppF V f k} := by
    have := (hK 1).1 (one_mem _)
    rwa [map_one] at this
  have hαG : α ∈ Formalism.L2.Theta.GfC V := by
    obtain ⟨γ, ⟨hγ, hx⟩, -⟩ := hR.2 α ⟨1, h1, 1, h1, by rw [one_mul, mul_one]⟩
    have := mul_mem (hR.1 γ hγ).1 hx.1.1
    rwa [mul_inv_cancel_left] at this
  obtain ⟨a, rfl⟩ := Ψ.onto α hαG
  have hpull : ∀ k ∈ {k | k ∈ Formalism.L2.Theta.KsphC V ∅ ∧ Formalism.IndefR.Mult.SuppF V f k},
      ∃ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, Ψ.ψ κ = k := by
    intro k hk
    obtain ⟨κ, rfl⟩ := Ψ.onto k hk.1.1
    exact ⟨κ, (hK κ).2 hk, rfl⟩
  refine ⟨s, a, hv, (GlobalTheory.InertTransport.suppF_iff hF Ψ hΨ hP hv a).1 hα, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨-, k₁, hk₁, k₂, hk₂, eγ⟩ := hR.1 γ hγ
    obtain ⟨κ₁, hκ₁, rfl⟩ := hpull k₁ hk₁
    obtain ⟨κ₂, hκ₂, rfl⟩ := hpull k₂ hk₂
    refine ⟨κ₁, hκ₁, κ₂, hκ₂, ?_⟩
    rw [eγ, ← map_mul, ← map_mul, pre_mul_eq]
  · rintro x ⟨κ₁, hκ₁, κ₂, hκ₂, rfl⟩
    obtain ⟨γ, ⟨hγ, hγx⟩, hu⟩ := hR.2 (Ψ.ψ (κ₁ * a * κ₂)) ⟨Ψ.ψ κ₁, (hK _).1 hκ₁, Ψ.ψ κ₂, (hK _).1 hκ₂, by rw [map_mul, map_mul]⟩
    have hγG : γ ∈ Formalism.L2.Theta.GfC V := (hR.1 γ hγ).1
    have eγ : Ψ.ψ (Formalism.IndefR.principalLevelFrame.pre Ψ γ) = γ := Formalism.IndefR.principalLevelFrame.pre_spec Ψ hγG
    refine ⟨γ, ⟨hγ, ?_⟩, ?_⟩
    · have : Ψ.ψ ((Formalism.IndefR.principalLevelFrame.pre Ψ γ)⁻¹ * (κ₁ * a * κ₂)) ∈
          {k | k ∈ Formalism.L2.Theta.KsphC V ∅ ∧ Formalism.IndefR.Mult.SuppF V f k} := by
        rw [map_mul, map_inv, eγ]; exact hγx
      exact ((hK _).2 this).1
    · rintro δ ⟨hδ, hδx⟩
      refine hu δ ⟨hδ, ?_⟩
      have hδG : δ ∈ Formalism.L2.Theta.GfC V := (hR.1 δ hδ).1
      have eδ : Ψ.ψ (Formalism.IndefR.principalLevelFrame.pre Ψ δ) = δ := Formalism.IndefR.principalLevelFrame.pre_spec Ψ hδG
      have hδT : TrivOutside {s.v} (Formalism.IndefR.principalLevelFrame.pre Ψ δ) := by
        refine (GlobalTheory.InertTransport.suppF_iff hF Ψ hΨ hP hv _).1 ?_
        rw [eδ]; exact hRs δ hδ
      have hT : TrivOutside {s.v} ((Formalism.IndefR.principalLevelFrame.pre Ψ δ)⁻¹ * (κ₁ * a * κ₂)) :=
        GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv hδT)
          (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_mul hκ₁.2
            ((GlobalTheory.InertTransport.suppF_iff hF Ψ hΨ hP hv a).1 hα)) hκ₂.2)
      have := (hK _).1 ⟨hδx, hT⟩
      rwa [map_mul, map_inv, eδ] at this

end GlobalTheory.SplitFrameReps
end

