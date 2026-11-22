import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0893
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRepresentationSpectralProjectors
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleObstructionZeroOfRestriction
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchesParahoricLevels
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.LevTrans

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem frGL_conj {n : ℕ} (β β' : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (u y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    (β' * intGL F E n u * β⁻¹) * frGL β y * (β' * intGL F E n u * β⁻¹)⁻¹ = frGL β' (u * y * u⁻¹) := by
  simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
  group

theorem transport {n n' : ℕ} (h : n = n') (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (β' x' : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) (u : GL (Fin n') (Formalism.L2.Herm.intAf F E))
    (j : Matrix (Fin n') (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hc : HMul.hMul x'.val j = HMul.hMul j x.val)
    (hf : HMul.hMul j β.val = (β' * intGL F E n' u).val.submatrix id (Fin.cast h))
    (Pg : Finset (Pl E)) (hu : ∀ PP ∈ Pg, Formalism.UG.bc (resS F PP) u = 1) (r t : ℕ) (hr : r ≤ n) (hr' : r ≤ n') :
    (x ∈ St β ↔ x' ∈ St β') ∧ (x ∈ St β → ∀ PP ∈ Pg,
      (redFn β PP x ∈ blockTri (blkOf r t) ↔ redFn β' PP x' ∈ blockTri (blkOf r t)) ∧
        upperLeftBlock hr' (redFn β' PP x') = upperLeftBlock hr (redFn β PP x)) := by
  subst h
  have hf' : j * β.val = (β' * intGL F E n u).val := hf
  set J : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := β' * intGL F E n u * β⁻¹ with hJ
  have hj : j = J.val := by
    rw [hJ, Units.val_mul, ← hf', mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  have hx : x' = J * x * J⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    show x'.val * J.val = J.val * x.val
    rw [← hj]
    exact hc
  have key : ∀ y, J * frGL β y * J⁻¹ = frGL β' (u * y * u⁻¹) := frGL_conj β β' u
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨y, rfl⟩
    exact ⟨u * y * u⁻¹, by rw [hx, key]⟩
  · rintro ⟨y, hy⟩
    refine ⟨u⁻¹ * y * u, ?_⟩
    have h1 := key (u⁻¹ * y * u)
    rw [show u * (u⁻¹ * y * u) * u⁻¹ = y by group, hy, hx] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  · rintro ⟨y, rfl⟩ PP hP
    have h2 : redFn β' PP x' = redFn β PP (frGL β y) := by
      rw [hx, key, redFn_frGL, redFn_frGL, map_mul, map_mul, map_inv, hu PP hP]
      simp
    rw [h2]
    exact ⟨Iff.rfl, rfl⟩

end General

variable {D : D7}

theorem fin_cA (z : Formalism.L2.Theta.AE D) :
    ((swapAE D).comp (finPart D)) (cA D z) =
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (((swapAE D).comp (finPart D)) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb, RingHom.map_add, RingHom.map_add]

theorem finE_unitary (V : HSp D) (g : GA D V) : finE V g ∈ UA D.sp.cm V.gram := by
  have h : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g) * V.gram.map (incA D) * Formalism.L2.Theta.mt V g =
      V.gram.map (incA D) := (show HR (AF D.host.F) D.sp.cm.sig V.gram from g).2
  have h2 := congrArg (fun M => Matrix.map M ((swapAE D).comp (finPart D))) h
  simp only [Matrix.map_mul] at h2
  show Formalism.UG.cT _ (finE V g).1 * _ * (finE V g).1 = _
  rw [show (finE V g).1 = (Formalism.L2.Theta.mt V g).map ((swapAE D).comp (finPart D)) from rfl]
  have e1 : (Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt V g)).map ((swapAE D).comp (finPart D)) =
      Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
        ((Formalism.L2.Theta.mt V g).map ((swapAE D).comp (finPart D))) := by
    ext i j
    exact fin_cA _
  rw [e1] at h2
  exact h2

theorem levtrans : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (Φ : GfC V ≃ₜ* GfC V'), IsFinIso V V' β β' Pg j Φ → ∀ κ : GfC V, (finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔ finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ')) ∧ (finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) → (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) = (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r)) := by
  intro D V V' β β' r t hr hr' Pg χ χ' j Φ hI κ
  obtain ⟨h, u, hf, hu⟩ := hI.frame
  obtain ⟨h1, h2⟩ := transport h β (finE V (κ : GA D V)) β' (finE V' (Φ κ : GA D V')) u j (hI.conj κ) hf Pg hu r t hr hr'
  refine ⟨?_, fun hm => ?_⟩
  · rw [mem_parLev, mem_parLev]
    constructor
    · rintro ⟨-, a, b, -⟩
      exact ⟨finE_unitary _ _, h1.1 a, fun PP hP => ((h2 a PP hP).1).1 (b PP hP),
        fun PP hP => absurd hP (Finset.notMem_empty PP)⟩
    · rintro ⟨-, a, b, -⟩
      exact ⟨finE_unitary _ _, h1.2 a, fun PP hP => ((h2 (h1.2 a) PP hP).1).2 (b PP hP),
        fun PP hP => absurd hP (Finset.notMem_empty PP)⟩
  · funext PP
    exact (h2 (parLev_St hm) PP.1 PP.2).2

end GlobalTheory.LevTrans

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ExtensionLogCanonical
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem l2ExtensionLogCanonical' : GlobalTheory.Published.L2ExtensionLogCanonical := by
  intro n hn Y _ _ _ _ _ _ ι La _ A hH E L s hs hS hjac hle δ hδ hcurv f
  obtain ⟨Λ, τ, z, β, hdata⟩ := GlobalTheory.T.exists_etale_frame_off_finite_zeroSet n Y ι La A hn hH E L s hs hS
  exact GlobalTheory.T.l2_extension_etale_coordinates_finite_zeros n Y ι La A hn E L s hs hS hjac hle δ hδ hcurv Λ τ z β hdata f

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastMapHalfRecNumsOfLogLevelPrimeLeStatement
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastMapHalf_recNums_of_log_levelPrime_le : ∀ (CY CT : ℝ) (N : NumDatum) (X : Fields) (Pr : Primes X) (W : Wts X Pr.Word N.R) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)), WeightTie N W pl u δ → Sizes Pr W N.sc.a → GlobalTheory.Core.Ht2.SizeRowsS CY N δ → Real.log (Pr.T u : ℝ) ≤ CT * N.R.m * N.sc.L → 1 ≤ Pr.T u → Reads N eJ δ (Pr.T u) R → LastSide R CT (lastLog W u) := by
  first | exact @GlobalTheory.ColRows.LastSideProof.lastSide_of_logT_le | exact GlobalTheory.ColRows.LastSideProof.lastSide_of_logT_le | (intros; apply GlobalTheory.ColRows.LastSideProof.lastSide_of_logT_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoSpread
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegBundleSpread

theorem lbIso_spread : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → ∀ (j₂ : (G2 e.A).left ⟶ (G2 d₀.A).left) (φ₂ : (G2 e.A).left ⟶ (G2 u.A).left), IsPullback j e.A.hom d₀.A.hom (spMap R₀.subtype) → IsSquare j j₂ → LBIso e.P (d₀.P.pull j₂) → IsSquare (j ≫ ψ) φ₂ → LBIso e.P (u.P.pull φ₂) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁) (φ₁ : d₁.A.left ⟶ d₀.A.left) (φ₁₂ : (G2 d₁.A).left ⟶ (G2 d₀.A).left) (χ₂ : (G2 d₁.A).left ⟶ (G2 u.A).left), IsPullback φ₁ d₁.A.hom d₀.A.hom (spMap (Subring.inclusion hle)) → IsSquare φ₁ φ₁₂ → LBIso d₁.P (d₀.P.pull φ₁₂) → IsSquare (φ₁ ≫ ψ) χ₂ → LBIso d₁.P (u.P.pull χ₂) := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ ψ sE e j hψ j₂ φ₂ hj hj₂ hej hφ₂ heφ
  obtain ⟨ψ₂, hψ₂⟩ := GlobalTheory.SiegDesc.exists_isSquare hψ.w
  have hcomp : j₂ ≫ ψ₂ = φ₂ := GlobalTheory.SiegDesc.isSquare_comp rfl hj₂ hψ₂ hφ₂
  have hpb : IsPullback j₂ (G2 e.A).hom (G2 d₀.A).hom (spMap R₀.subtype) :=
    GlobalTheory.SiegDesc.isPullback_of_isSquare hj hj₂
  haveI : IsProper d₀.A.hom := d₀.ab.proper
  haveI : IsProper (G2 d₀.A).hom := by
    change IsProper (pullback.fst d₀.A.hom d₀.A.hom ≫ d₀.A.hom)
    infer_instance
  have hN : (u.P.pull ψ₂).IsLB := pull_isLB u.isLB ψ₂
  have H : LBIso (d₀.P.pull j₂) ((u.P.pull ψ₂).pull j₂) := by
    have a : LBIso (d₀.P.pull j₂) (u.P.pull φ₂) :=
      LBIso.trans (pull_isLB d₀.isLB _) e.isLB (pull_isLB u.isLB _) (LBIso.symm hej) heφ
    have b : LBIso (u.P.pull φ₂) ((u.P.pull ψ₂).pull j₂) := by
      rw [← hcomp]
      exact LBIso.symm (GlobalTheory.SiegelPullComp.iso_pull_pull u.isLB ψ₂ j₂)
    exact LBIso.trans (pull_isLB d₀.isLB _) (pull_isLB u.isLB _) (pull_isLB hN _) a b
  obtain ⟨F, hF⟩ := GlobalTheory.lbIso_descends_to_subring_containing_finset S R₀ (G2 e.A).left (G2 d₀.A).left
    (G2 e.A).hom (G2 d₀.A).hom j₂ d₀.P (u.P.pull ψ₂) hpb d₀.isLB hN H
  refine ⟨F, fun R₁ hle hFR s₁ d₁ φ₁ φ₁₂ χ₂ hφ₁ hφ₁₂ hd₁ hχ₂ => ?_⟩
  have hcomp₁ : φ₁₂ ≫ ψ₂ = χ₂ := GlobalTheory.SiegDesc.isSquare_comp rfl hφ₁₂ hψ₂ hχ₂
  have H₁ := hF R₁ hle hFR (G2 d₁.A).left (G2 d₁.A).hom φ₁₂
    (GlobalTheory.SiegDesc.isPullback_of_isSquare hφ₁ hφ₁₂)
  have c : LBIso ((u.P.pull ψ₂).pull φ₁₂) (u.P.pull χ₂) := by
    rw [← hcomp₁]
    exact GlobalTheory.SiegelPullComp.iso_pull_pull u.isLB ψ₂ φ₁₂
  exact LBIso.trans d₁.isLB (pull_isLB hN _) (pull_isLB u.isLB _)
    (LBIso.trans d₁.isLB (pull_isLB d₀.isLB _) (pull_isLB hN _) hd₁ H₁) c

end GlobalTheory.SiegBundleSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupMatrixIsomorphismStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_group_matrix_isomorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Pg : Finset (Formalism.L2.DIV.Pl E)), l.Mb = ∏ w ∈ Pg, w.asIdeal → ∀ (hle : ∀ w : ↥Pg, l.Mb ≤ w.1.asIdeal) (r : ℕ) (φ : LaMod Dw l ≃ₗ[𝓞 E] (Fin r → 𝓞 E ⧸ l.Mb)), ∃ ψ : Formalism.L2.DIV.G0 Pg r ≃* LevelLiftConditions.LevGrp Dw l, (∀ (g : Formalism.L2.DIV.G0 Pg r) (Y : Matrix (Fin r) (Fin r) (𝓞 E ⧸ l.Mb)), (∀ q, φ (ψ g q) = Y.mulVec (φ q)) ↔ ∀ w : ↥Pg, Y.map (Ideal.Quotient.factor (hle w)) = (g w).1) ∧ ∀ (g : Formalism.L2.DIV.G0 Pg r) (w : ↥Pg), Units.map (Ideal.Quotient.factor (hle w)).toMonoidHom (LevelLiftConditions.levDet Dw l (ψ g)) = Matrix.GeneralLinearGroup.det (g w) := by
  first | exact @GlobalTheory.GeoActCompare.exists_levGrp_equiv_pi | exact GlobalTheory.GeoActCompare.exists_levGrp_equiv_pi | (intros; apply GlobalTheory.GeoActCompare.exists_levGrp_equiv_pi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelTypeEigenfunctionOfLiftableElement
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

namespace GlobalTheory.LevelRows

variable {D : D7}

theorem levelType_eigenfunction_of_liftable_element {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {P : LevelP L.Pg L.r ℂ} {F : GA D V → ℂ} (hF : HasType V β (withP L P) F) (p : P.H)
    (hex : ∃ κ, IsLevelLift V β L p.1 κ) :
    actG0 V β L p.1 F = fun h => ((P.chi p : ℂˣ) : ℂ) * F h := by
  have hκ : IsLevelLift V β L p.1 hex.choose := hex.choose_spec
  have hp : rTup β L (finE V hex.choose) ∈ P.H := by rw [hκ.2.2]; exact p.2
  have hmem : hex.choose ∈ levG V β (withP L P) := ⟨hκ.1, hκ.2.1, hp⟩
  have hc : levChi V β (withP L P) hex.choose = ((P.chi p : ℂˣ) : ℂ) * levChi V β (flagL L) hex.choose := by
    unfold levChi
    rw [levFn_withP, extendOne_of_mem _ hp, Units.val_mul]
    congr 3
    exact Subtype.ext hκ.2.2
  have ha := levChi_ne_zero (β := β) (flagL L) hex.choose
  funext h
  unfold actG0
  rw [dif_pos hex, hF _ hmem h, hc]
  field_simp

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_lift_of_ne_zero (R : RealDat D A Ks) (hinj : Function.Injective R.HE.e) (hg : R.models_gE)
    {x : R.HE.H} (hx : x ≠ 0) (g : G) : ∃ κ, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) κ := by
  by_contra hk
  apply hx
  have h0 : R.gE g x = 0 := by
    apply hinj
    rw [hg g x, map_zero]
    ext v h
    show actG0 _ _ _ _ _ h = 0
    unfold actG0
    rw [dif_neg hk]
    rfl
  have : R.gE g⁻¹ (R.gE g x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, h0, map_zero]

theorem rowsOfLevel_of_models (R : RealDat D A Ks) (F : Face D A) (hE : R.models_HE) (hg : R.models_gE) :
    GlobalTheory.IndefiniteRowSideFullHecke.TypeCharacterLevelRows.RowsOfLevel R F := by
  intro b x
  have hx : R.HE.e x ∈ R.EEat R.triv := hE.2.1 ▸ LinearMap.mem_range_self _ x
  unfold RealDat.EEat at hx ⊢
  rw [mem_goodPart, GlobalTheory.MultMem.mem_mult_iff] at hx ⊢
  constructor
  · rintro ⟨h1, -⟩ g
    by_cases h0 : x = 0
    · simp [h0]
    apply hE.1
    rw [hg, map_smul]
    ext v h
    have hmem : R.eG g ∈ (R.levR F b).H := by
      show R.eG.symm (R.eG g) ∈ (F.lvl b).P
      rw [MulEquiv.symm_apply_apply]; exact g.2
    have h2 := levelType_eigenfunction_of_liftable_element (V := Yc D 0) (β := R.βY 0) (L := R.dat0 R.triv) (P := R.levR F b)
      (F := R.HE.e x v) (fun κ hκ h => h1.lev v κ hκ h) ⟨R.eG g, hmem⟩ (exists_lift_of_ne_zero R hE.1 hg h0 g)
    have h3 : (R.eG.symm.toMonoidHom.subgroupComap (F.lvl b).P) ⟨R.eG g, hmem⟩ = g :=
      Subtype.ext (R.eG.symm_apply_apply g)
    refine (congrFun h2 h).trans ?_
    show D.what₂.embLL (((F.lvl b).ψ ((R.eG.symm.toMonoidHom.subgroupComap (F.lvl b).P) ⟨R.eG g, hmem⟩) : D.what₂.LLˣ) : D.what₂.LL) * _ = _
    rw [h3]
    rfl
  · intro h
    refine ⟨⟨hx.1.aut, hx.1.cusp, fun v => ?_, hx.1.equiv, hx.1.cont⟩, hx.2⟩
    have hP : IsPLevel (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.levR F b) (R.HE.e x v) := by
      refine ⟨fun κ hκ y => hx.1.lev v κ hκ y, fun p => ?_⟩
      have h1 := congrArg (fun z => R.HE.e z v) (h ⟨R.eG.symm p.1, p.2⟩)
      simp only [hg _ x, map_smul] at h1
      have h2 : R.eG (R.eG.symm p.1) = p.1 := R.eG.apply_symm_apply p.1
      rw [h2] at h1
      exact h1
    exact fun κ hκ y => hP.hasType κ hκ y

end GlobalTheory.LevelRows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelTypeHeckeKilledCorrespondMatchingIso
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.CuspMult.EqTrans

theorem asAlg_comp {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H' X)
    (e : H ≃* H') (x : MonoidAlgebra ℂ H) :
    Representation.asAlgebraHom (ρ.comp e.toMonoidHom : Representation ℂ H X) x =
      ρ.asAlgebraHom (MonoidAlgebra.domCongr ℂ ℂ e x) := by
  have : Representation.asAlgebraHom (ρ.comp e.toMonoidHom : Representation ℂ H X) =
      ρ.asAlgebraHom.comp (MonoidAlgebra.domCongr ℂ ℂ e).toAlgHom := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      simp
    · exact Subsingleton.elim _ _
  rw [this]; rfl

theorem killed_comp {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H' X)
    (e : H ≃* H') (I : Set (MonoidAlgebra ℂ H)) (I' : Set (MonoidAlgebra ℂ H'))
    (h1 : ∀ x ∈ I, MonoidAlgebra.domCongr ℂ ℂ e x ∈ I')
    (h2 : ∀ x ∈ I', MonoidAlgebra.domCongr ℂ ℂ e.symm x ∈ I) :
    killed (ρ.comp e.toMonoidHom : Representation ℂ H X) I = killed ρ I' := by
  ext v
  rw [mem_killed, mem_killed]
  constructor
  · intro h x hx
    have := h _ (h2 x hx)
    rw [asAlg_comp, ← MonoidAlgebra.domCongr_symm, AlgEquiv.apply_symm_apply] at this
    exact this
  · intro h x hx
    rw [asAlg_comp]
    exact h _ (h1 x hx)

theorem isDC_map {H H' : Type} [Group H] [Group H'] (e : H ≃* H') (J : Subgroup H) (J' : Subgroup H')
    (hJ : ∀ g, g ∈ J ↔ e g ∈ J') (x : H) (R : Finset H) (h : Bridge.IsDC J x R) :
    Bridge.IsDC J' (e x) (R.map e.toEquiv.toEmbedding) := by
  have hJ' : ∀ g' : J', e.symm g' ∈ J := fun g' => (hJ _).2 (by simp)
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 ha
    obtain ⟨k₁, k₂, rfl⟩ := h.1 b hb
    exact ⟨⟨e k₁, (hJ _).1 k₁.2⟩, ⟨e k₂, (hJ _).1 k₂.2⟩, by simp⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a, ⟨ha, ha'⟩, hu⟩ := h.2 (e.symm k₁ * x * e.symm k₂) ⟨⟨_, hJ' k₁⟩, ⟨_, hJ' k₂⟩, rfl⟩
    refine ⟨e a, ⟨Finset.mem_map.2 ⟨a, ha, rfl⟩, ?_⟩, ?_⟩
    · have := (hJ _).1 ha'
      simpa using this
    · rintro b ⟨hb, hb'⟩
      obtain ⟨b, hbR, rfl⟩ := Finset.mem_map.1 hb
      have : b = a := hu b ⟨hbR, (hJ _).2 (by simpa using hb')⟩
      rw [this]; rfl

variable {D : D7}

theorem mem_levG (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (Pg : Finset (Pl D.host.E))
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (P : LevelP Pg r ℂ) (k : GfC V) :
    (k : GA D V) ∈ levG V β (withP (princDat V.rank r t hr Pg χ) P) ↔
      finE V (k : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ∧
        (rTup β (princDat V.rank r t hr Pg χ) (finE V (k : GA D V)) : G0 Pg r) ∈ P.H :=
  ⟨fun h => h.2, fun h => ⟨k.2, h⟩⟩

theorem levChi_eq (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (Pg : Finset (Pl D.host.E))
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (P : LevelP Pg r ℂ) (k : GA D V) :
    levChi V β (withP (princDat V.rank r t hr Pg χ) P) k =
      ((ext1 P.H P.chi (rTup β (princDat V.rank r t hr Pg χ) (finE V k) : G0 Pg r) : ℂˣ) : ℂ) := by
  unfold levChi levFn
  congr 1
  have h1 : (withP (princDat V.rank r t hr Pg χ) P).s = 0 := rfl
  have h2 : (withP (princDat V.rank r t hr Pg χ) P).Q = ∅ := rfl
  rw [h1, h2]
  simp only [Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
  rfl

theorem map_mem (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank)
    (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Φ : GfC V ≃* GfC V')
    {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 Pg r) (c : G → ℂ) (P : LevelP Pg r ℂ) {Pl0 : Type} (ok : Set Pl0)
    (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) (hrk : V.rank = V'.rank)
    (h1 : ∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔
      finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ'))
    (h2 : ∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) →
      (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) =
        (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r))
    (h3 : ∀ P0 ∈ ok, ∀ k (α : GfC V), IsHeckeAt V (pl P0) k α ↔ IsHeckeAt V' (pl P0) k (Φ α))
    (x : MonoidAlgebra ℂ (GfC V)) (hx : x ∈ eqSet V β (princDat V.rank r t hr Pg χ) eG c P ok pl q Sg) :
    MonoidAlgebra.domCongr ℂ ℂ Φ x ∈ eqSet V' β' (princDat V'.rank r t hr' Pg χ') eG c P ok pl q Sg := by
  have hlev : ∀ (P : LevelP Pg r ℂ) (k : GfC V), (k : GA D V) ∈ levG V β (withP (princDat V.rank r t hr Pg χ) P) ↔
      (Φ k : GA D V') ∈ levG V' β' (withP (princDat V'.rank r t hr' Pg χ') P) := by
    intro P k
    rw [mem_levG, mem_levG]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨(h1 k).1 a, by rw [h2 k a]; exact b⟩
    · rintro ⟨a, b⟩
      have a' := (h1 k).2 a
      exact ⟨a', by rw [← h2 k a']; exact b⟩
  rcases hx with (⟨k, hk, rfl⟩ | ⟨κ, hκ, rfl⟩) | ⟨P0, hP0, k, hk, α, R, hα, hR, rfl⟩
  · refine Or.inl (Or.inl ⟨Φ k, (hlev P k).1 hk, ?_⟩)
    rw [levChi_eq, levChi_eq, h2 k ((mem_levG V β r t hr Pg χ P k).1 hk).1, map_sub, MonoidAlgebra.domCongr_single,
      MonoidAlgebra.domCongr_single, map_one Φ]
  · refine Or.inl (Or.inr ⟨fun g => Φ (κ g), fun g => ⟨(Φ (κ g)).2, (h1 _).1 (hκ g).2.1, ?_⟩, ?_⟩)
    · exact (h2 _ (hκ g).2.1).trans (hκ g).2.2
    · rw [map_sub, map_sum, MonoidAlgebra.domCongr_single, map_one Φ]
      simp only [MonoidAlgebra.domCongr_single]
  · refine Or.inr ⟨P0, hP0, k, hrk ▸ hk, Φ α, R.map Φ.toEquiv.toEmbedding, (h3 P0 hP0 k α).1 hα, ?_, ?_⟩
    · rw [← map_inv Φ]
      exact isDC_map Φ _ _ (fun g => hlev (LevelP.triv Pg r ℂ) g) _ _ hR
    · rw [map_sub, map_sum, MonoidAlgebra.domCongr_single, map_one Φ, Finset.sum_map]
      simp only [MonoidAlgebra.domCongr_single]
      rfl

theorem killed_eqSet_comp : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Φ : GfC V ≃ₜ* GfC V') {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 Pg r) (c : G → ℂ) (P : LevelP Pg r ℂ) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GfC V') X), V.rank = V'.rank → (∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔ finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ')) → (∀ κ : GfC V, finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) → (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) = (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r)) → (∀ P0 ∈ ok, ∀ k (α : GfC V), IsHeckeAt V (pl P0) k α ↔ IsHeckeAt V' (pl P0) k (Φ α)) → killed (ρ.comp Φ.toMulEquiv.toMonoidHom : Representation ℂ (GfC V) X) (eqSet V β (princDat V.rank r t hr Pg χ) eG c P ok pl q Sg) = killed ρ (eqSet V' β' (princDat V'.rank r t hr' Pg χ') eG c P ok pl q Sg) := by
  intro D V V' β β' r t hr hr' Pg χ χ' Φ G _ _ eG c P Pl0 ok pl q Sg X _ _ ρ hrk h1 h2 h3
  refine killed_comp ρ Φ.toMulEquiv _ _
    (map_mem V V' β β' r t hr hr' Pg χ χ' Φ.toMulEquiv eG c P ok pl q Sg hrk h1 h2 h3) ?_
  have e : ∀ κ : GfC V', Φ (Φ.toMulEquiv.symm κ) = κ := fun κ => Φ.toMulEquiv.apply_symm_apply κ
  refine map_mem V' V β' β r t hr' hr Pg χ' χ Φ.toMulEquiv.symm eG c P ok pl q Sg hrk.symm ?_ ?_ ?_
  · intro κ
    rw [h1, e]
  · intro κ hκ
    have := h2 (Φ.toMulEquiv.symm κ) ((h1 _).2 (by rw [e]; exact hκ))
    rw [e] at this
    exact this.symm
  · intro P0 hP0 k α
    rw [h3 P0 hP0, e]

end GlobalTheory.CuspMult.EqTrans
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRepresentationSpectralProjectorsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_representation_spectral_projectors : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ), b.IsType σ ρ → ∃ E : Fin D.a → Matrix (Fin D.g) (Fin D.g) ℂ, (∀ i, E i * E i = E i) ∧ (∀ i, (E i).trace = (D.m : ℂ)) ∧ (∀ i c, ρ (algebraMap (𝓞 D.F) D.O c) * E i = σ (b.t i c) • E i) ∧ (∀ i c, E i * ρ (algebraMap (𝓞 D.F) D.O c) = σ (b.t i c) • E i) ∧ (2 * σ b.ρ - D.tr) • ∑ i, E i = ρ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : ℂ) - σ b.ρ) • (1 : Matrix (Fin D.g) (Fin D.g) ℂ) := by
  first | exact @GlobalTheory.UPel.HT.LieProj.lie_projectors | exact GlobalTheory.UPel.HT.LieProj.lie_projectors | (intros; apply GlobalTheory.UPel.HT.LieProj.lie_projectors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGlueOfOpenCoverCocycleStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_glue_of_openCover_cocycle : ∀ (X : Scheme.{0}) (Ix : Type) (W : Ix → X.Opens) (L : Ix → LB X) (w : ∀ i k, Cmp (W i ⊓ W k) (L i) (L k)), (∀ x, ∃ i, x ∈ W i) → (∀ i, IsOn (W i) (L i)) → (∀ i k, IsoOn (W i ⊓ W k) (L i) (L k) (w i k)) → (∀ (i j k : Ix) (x : X) (a : (L i).ι) (b : (L j).ι) (c : (L k).ι), x ∈ (L i).U a → x ∈ (L j).U b → x ∈ (L k).U c → gm (𝟙 X) x _ (w i j a b) * gm (𝟙 X) x _ (w j k b c) = gm (𝟙 X) x _ (w i k a c)) → ∃ N : LB X, N.IsLB ∧ ∀ i, ∃ v : Cmp (W i) N (L i), IsoOn (W i) N (L i) v := by
  first | exact @GlobalTheory.PicGlue.lb_glue | exact GlobalTheory.PicGlue.lb_glue | (intros; apply GlobalTheory.PicGlue.lb_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullOfIsLineBundleIsoOnOpenStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_pull_of_isLineBundleIsoOnOpen : ∀ (X Z : Scheme.{0}) (W : X.Opens) (L M : LB X) (w : Cmp W L M) (r : Z ⟶ X), IsoOn W L M w → (∀ z, r z ∈ W) → LBIso (L.pull r) (M.pull r) := by
  first | exact @GlobalTheory.PicGlue.lbIso_pull_of_isoOn | exact GlobalTheory.PicGlue.lbIso_pull_of_isoOn | (intros; apply GlobalTheory.PicGlue.lbIso_pull_of_isoOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleObstructionZeroOfRestrictionStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_obstruction_zero_of_restriction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i) (L : LB X), IsPullback i s₀ s (spMap π) → L.IsLB → IsObL S α (L.pull i) 0 := by
  first | exact @GlobalTheory.LBObs.isObL_pull_zero | exact GlobalTheory.LBObs.isObL_pull_zero | (intros; apply GlobalTheory.LBObs.isObL_pull_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormResidueSignMulStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localNormResidueSign_mul : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (s t : Fˣ), sgn E (s * t) = sgn E s * sgn E t := by
  first | exact @GlobalTheory.KSp.sgn_mul_of_isQuad | exact GlobalTheory.KSp.sgn_mul_of_isQuad | (intros; apply GlobalTheory.KSp.sgn_mul_of_isQuad <;> assumption)
end

