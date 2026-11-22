import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0847
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0851
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0487
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArcDataOfBadReductionFiniteExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0565
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelPointsTranslateMeanOfIntegralCombinat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0807
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0112
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0063
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0064
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0848
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockSubstitutionPreservesHarmonicLetterPolynomia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0844

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeOfPublishedStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_of_hypotheses : GlobalTheory.Published.BaseChangeDefiniteUnitary → GlobalTheory.Published.BernsteinUnitaryProductIrreducible → GlobalTheory.Published.DiscreteSpectrumGL → GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : AUSide D), CGTrue hL D T → AUTrue hL D T A → SphericalInertData.Conclusion1 D := by
  first | exact @GlobalTheory.BaseChangeClosing.conclusion1_of_baseChange | exact GlobalTheory.BaseChangeClosing.conclusion1_of_baseChange | (intros; apply GlobalTheory.BaseChangeClosing.conclusion1_of_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipSplitPlacesInvariantFormPhase
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

theorem cflip_flipElt_add {a b : AE D} (m : ℕ) (h1 : a * b = 0) (h2 : a * cA D b = 0) (h3 : cA D a * b = 0)
    (h4 : cA D a * cA D b = 0) : flipElt (a + b) m = flipElt a m * flipElt b m := by
  unfold flipElt
  rw [map_add]
  linear_combination (-((m : AE D) - 1) ^ 2) * h1 - ((m : AE D) - 1) * (incA D ((m : D.host.E)⁻¹) - 1) * h2
    - ((m : AE D) - 1) * (incA D ((m : D.host.E)⁻¹) - 1) * h3 - (incA D ((m : D.host.E)⁻¹) - 1) ^ 2 * h4

theorem cflip_sum_idem {S : Finset (Formalism.L2.DIV.Pl D.host.E)} {es : Formalism.L2.DIV.Pl D.host.E → AE D}
    (hes : ∀ PP ∈ S, Formalism.L2.NTheta.IsIdemAt (es PP) PP) : (∑ PP ∈ S, es PP) * (∑ PP ∈ S, es PP) = ∑ PP ∈ S, es PP := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun PP hPP => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single_of_mem PP hPP]
  · exact (hes PP hPP).1.1
  · intro Q hQ hne
    exact GlobalTheory.Tow.idemAt_orth (hes PP hPP) (hes Q hQ) (Ne.symm hne)

theorem cflip_mul_cA_eq_zero {e u v : AE D} (he : e * cA D e = 0) (hu : e * u = u) (hv : e * v = v) : u * cA D v = 0 := by
  rw [← hu, ← hv, map_mul]
  linear_combination (u * cA D v) * he

theorem cflip_isHalf_mono {m n : ℕ} {e u : AE D} (hu : e * u = u) {y : Mx D m n} (hy : Formalism.IndefR.Datum.IsHalf (cA D u) y) :
    Formalism.IndefR.Datum.IsHalf (cA D e) y := by
  intro i j
  rw [← hy i j, ← mul_assoc, ← map_mul, hu]

theorem cflip_det_split {R : Type*} [CommRing R] {a b t x : R} (hab : a * b = 0)
    (hx : x * ((a + b) * t + (1 - (a + b))) = 1) : x * ((a * t + (1 - a)) * (b * t + (1 - b))) = 1 := by
  linear_combination hx + (x * (t - 1) ^ 2) * hab

theorem cflip_smul_one_mul {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (c d : R)
    (X : Matrix n n R) : ((c * d) • (1 : Matrix n n R)) * X = c • ((d • (1 : Matrix n n R)) * X) := by
  rw [mul_smul, Matrix.smul_mul]

theorem cflip_unit_split {R : Type*} [CommRing R] {x u v : R} (h : x * (u * v) = 1) : x = x * v * (x * u) := by
  linear_combination (-x) * h

set_option maxHeartbeats 1000000 in
theorem centralFlip_phase : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (m : ℕ) (z : GA D V) (x : (AE D)ˣ) (ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ), IsIdemSum eT T → m ≠ 0 → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V eT m x → (∀ y : WO V W, IsHalf (cA D eT) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ) → ∃ r : ℝ, 0 < r ∧ ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ℓ (om (z⁻¹, 1) f) = (r : ℂ) * ((χW x : Circle) : ℂ)⁻¹ * ℓ f := by
  intro D ψ V W χV χW om hW T
  induction T using Finset.induction_on with
  | empty =>
    intro eT m z x ℓ hS hm hz hx hℓ
    obtain ⟨⟨es, -, he⟩, -⟩ := hS
    rw [Finset.sum_empty] at he
    subst he
    have h1 : flipElt (0 : AE D) m = 1 := by unfold flipElt; simp
    have hz1 : z = 1 := GlobalTheory.IdemSupport.mt_inj V (by rw [hz, h1, one_smul, GlobalTheory.IdemSupport.mt_one])
    have hx1 : x = 1 := by simpa [IsFlipDet] using hx
    subst hz1 hx1
    refine ⟨1, one_pos, fun f hf => ?_⟩
    simp only [inv_one, Circle.coe_one, map_one, inv_one, Complex.ofReal_one, one_mul]
    show ℓ ((om 1) f) = ℓ f
    rw [map_one]
    rfl
  | @insert P T' hP ih =>
    intro eT m z x ℓ hS hm hz hx hℓ
    obtain ⟨⟨es, hes, heT⟩, hT⟩ := hS
    have hesP := hes P (Finset.mem_insert_self P T')
    have hes' : ∀ Q ∈ T', Formalism.L2.NTheta.IsIdemAt (es Q) Q := fun Q hQ => hes Q (Finset.mem_insert_of_mem hQ)
    have heT' : eT = es P + ∑ Q ∈ T', es Q := by rw [heT, Finset.sum_insert hP]
    have hab : es P * ∑ Q ∈ T', es Q = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun Q hQ => GlobalTheory.Tow.idemAt_orth hesP (hes' Q hQ) (fun h => hP (h ▸ hQ))
    have hbb := cflip_sum_idem hes'
    have heA : eT * es P = es P := by
      rw [heT', add_mul, hesP.1.1, mul_comm, hab, add_zero]
    have heB : eT * ∑ Q ∈ T', es Q = ∑ Q ∈ T', es Q := by
      rw [heT', add_mul, hab, hbb, zero_add]
    have hSa : IsIdemSum (es P) {P} :=
      ⟨⟨es, by simpa using hesP, by simp⟩, cflip_mul_cA_eq_zero hT heA heA⟩
    have hSb : IsIdemSum (∑ Q ∈ T', es Q) T' := ⟨⟨es, hes', rfl⟩, cflip_mul_cA_eq_zero hT heB heB⟩
    have hflip : flipElt eT m = flipElt (es P) m * flipElt (∑ Q ∈ T', es Q) m := by
      rw [heT']
      refine cflip_flipElt_add m hab (cflip_mul_cA_eq_zero hT heA heB) ?_ (by rw [← map_mul, hab, map_zero])
      rw [mul_comm]
      exact cflip_mul_cA_eq_zero hT heB heA
    obtain ⟨zP, -, -, hzP⟩ := GlobalTheory.T.exists_central_conjugateFlipScalar_finiteAdelic D V {P} m (es P) hSa hm

    have h1 : Formalism.L2.Theta.mt V zP * Formalism.L2.Theta.mt V zP⁻¹ = 1 := by
      rw [← GlobalTheory.IdemSupport.mt_mul, mul_inv_cancel, GlobalTheory.IdemSupport.mt_one]
    have hz' : Formalism.L2.Theta.mt V (z * zP⁻¹) =
        flipElt (∑ Q ∈ T', es Q) m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
      rw [hzP] at h1
      calc Formalism.L2.Theta.mt V (z * zP⁻¹)
          = (flipElt (∑ Q ∈ T', es Q) m * flipElt (es P) m) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) *
              Formalism.L2.Theta.mt V zP⁻¹ := by
            rw [GlobalTheory.IdemSupport.mt_mul, hz, hflip, mul_comm (flipElt (es P) m)]
        _ = flipElt (∑ Q ∈ T', es Q) m • (flipElt (es P) m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) *
              Formalism.L2.Theta.mt V zP⁻¹) := cflip_smul_one_mul _ _ _
        _ = _ := by rw [h1]

    have hx0 : (x : AE D) * ((es P * (m : AE D) ^ V.rank + (1 - es P)) * ((∑ Q ∈ T', es Q) * (m : AE D) ^ V.rank + (1 - ∑ Q ∈ T', es Q))) = 1 := by
      rw [heT'] at hx
      exact cflip_det_split hab hx
    have hxa : (x : AE D) * ((∑ Q ∈ T', es Q) * (m : AE D) ^ V.rank + (1 - ∑ Q ∈ T', es Q)) * (es P * (m : AE D) ^ V.rank + (1 - es P)) = 1 := by
      rw [mul_assoc, mul_comm ((∑ Q ∈ T', es Q) * (m : AE D) ^ V.rank + _)]; exact hx0
    have hxb : (x : AE D) * (es P * (m : AE D) ^ V.rank + (1 - es P)) * ((∑ Q ∈ T', es Q) * (m : AE D) ^ V.rank + (1 - ∑ Q ∈ T', es Q)) = 1 := by
      rw [mul_assoc]; exact hx0
    let xa : (AE D)ˣ := ⟨_, _, hxa, by rw [mul_comm]; exact hxa⟩
    let xb : (AE D)ˣ := ⟨_, _, hxb, by rw [mul_comm]; exact hxb⟩
    have hxx : x = xa * xb := by
      apply Units.ext
      simp only [xa, xb, Units.val_mul]
      exact cflip_unit_split hx0
    have hxaD : IsFlipDet V (es P) m xa := hxa
    have hxbD : IsFlipDet V (∑ Q ∈ T', es Q) m xb := hxb
    obtain ⟨rP, hrP, hPstep⟩ := GlobalTheory.T.weilOperator_inv_centralFlip_invariantForm_eq D ψ V W χV χW om hW P (es P) m zP xa ℓ hesP hm hzP hxaD
      (fun y hy φ hφ => hℓ y (cflip_isHalf_mono heA hy) φ hφ)
    obtain ⟨r', hr', hrest⟩ := ih (∑ Q ∈ T', es Q) m (z * zP⁻¹) xb ℓ hSb hm hz' hxbD
      (fun y hy φ hφ => hℓ y (cflip_isHalf_mono heB hy) φ hφ)
    refine ⟨rP * r', mul_pos hrP hr', fun f hf => ?_⟩
    have hsplit : ((z⁻¹ : GA D V), (1 : GA D W)) = (zP⁻¹, 1) * ((z * zP⁻¹)⁻¹, 1) := by
      ext <;> simp
    rw [hsplit, map_mul, Module.End.mul_apply, hPstep _ (hW.om_pres _ _ hf), hrest f hf, hxx, map_mul]
    push_cast
    ring

end GlobalTheory.LevelSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterUnramifiedOffBadStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_unramified_off_bad : ∀ (D : D7) (V W : HSp D) (B : Base V W), B.Good → ∀ χ : Formalism.L2.Host.HChar D.host.E, ChrEq (B.mu * B.eta⁻¹) χ → ∀ bad : ℕ, (∀ PP, PP ∈ B.G.Pg ∨ PP ∈ B.de.Q → (bad : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (bad : 𝓞 D.host.E) ∉ Q.asIdeal → χ.UnrAt Q) ∧ ∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k, χ.resFin (Q.under (𝓞 D.host.F)) k = 1 := by
  first | exact @GlobalTheory.BasePairChar.base_pair_char | exact GlobalTheory.BasePairChar.base_pair_char | (intros; apply GlobalTheory.BasePairChar.base_pair_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmPlaceOperatorPreservesTypeAveragesShapeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmPlaceOperator_preserves_type_averages_shape : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (FinPl D)) (v : FinPl D), v ∈ Sb → ∀ (h : GA D (Wc D i)), (∀ a b, idem D (.inl v) * (Formalism.L2.Theta.mt (Wc D i) h - 1) a b = (Formalism.L2.Theta.mt (Wc D i) h - 1) a b) → ∀ (c : WO (Vc D i) (Wc D i) →₀ ℂ), (∀ y ∈ c.support, IsHalf (idem D (.inl v)) y) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → TypeIn R i t (dropPl Sb v) (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) ∧ CleanIn R i t (dropPl Sb v) (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) ∧ LikeOff R i t Sb (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) := by
  first | exact @GlobalTheory.DownLift.GenSplit.placeOp_keep | exact GlobalTheory.DownLift.GenSplit.placeOp_keep | (intros; apply GlobalTheory.DownLift.GenSplit.placeOp_keep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffSpaceLevelFixesFockVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.LevelFix

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem isLiftFiniteGroup_one_of_mem_coeffSpaceLevel (R : RealDat D A Ks) (i : Fin D.R.m) (k : GA D (Wc D i)) (hk : k ∈ levW R i) :
    IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 k := by
  refine ⟨hk.1, hk.2.1, ?_⟩
  have h2 := hk.2.2
  have e : (R.datWp i R.triv).P.H = ⊥ := rfl
  rw [e] at h2
  exact Subgroup.mem_bot.1 h2

theorem realDatum_identity_lifts_identity (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) 1 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact rTup_one⟩

theorem levChi_flag_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) 1 = 1 := by
  have := (levChar D.sp.cm (Vc D i).gram (R.βV i) (flagL (R.datVt i t))).map_one
  unfold levChi
  rw [map_one]
  exact congrArg Units.val this

theorem levW_fix_vP (R : RealDat D A Ks) (F : Face D A) (h : Laws R F) (i : Fin D.R.m) (t : T)
    (k : GA D (Wc D i)) (hk : k ∈ levW R i) : R.ωP i t (1, k) (R.vP i t) = R.vP i t := by
  have e := GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R h.lev h.models.inf h.thP.ωP h.thP.vP i t 1 1 k (realDatum_identity_lifts_identity R i t)
    (isLiftFiniteGroup_one_of_mem_coeffSpaceLevel R i k hk)
  rw [e, levChi_flag_one R i t, inv_one, one_smul]

theorem levFix : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    Laws R F → R.FullP → ∀ i t, LevFix R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F h _ i t k hk P
  have hv : R.ωP i t (1, k) (R.vP i t) = (1 : ℂ) • R.vP i t := by
    rw [one_smul]; exact levW_fix_vP R F h i t k hk
  have := GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) h.models.inf
    (h.thP.ωP i t) _ _ _ _ _ (h.thP.pt_theta i t) 1 (Subgroup.one_mem _) k hk.1 1 hv P
  exact this.trans (one_smul ℂ _)

end GlobalTheory.RawLift.LevelFix

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArcDataOfBadReductionFiniteExtensionStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arcData_of_badReduction_finiteExtension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype), Y.N3 → Y.SplitFibres → ∀ (T : CDVR) (io : c.F →+* T.Fr) (b : V →+* T.V) (y' : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c), (algebraMap T.V T.Fr).comp b = io.comp V.subtype → y' ≫ Y.s = spMap b → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y' → ¬ Set.range y' ⊆ abLocus Y.t.G → ∃ (T' : CDVR) (g : T.V →+* T'.V) (ϖ : T'.V) (a : ArcIn Dw l V.subtype T'.V (g.comp b)), Function.Injective g ∧ g.Finite ∧ Irreducible ϖ ∧ Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id T'.V) ϖ (spMap g ≫ y') := by
  first | exact @GlobalTheory.ArcOfPoint.exists_arcIn_of_bad_reduction | exact GlobalTheory.ArcOfPoint.exists_arcIn_of_bad_reduction | (intros; apply GlobalTheory.ArcOfPoint.exists_arcIn_of_bad_reduction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelPointsTranslateMeanOfIntegralCombinatStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelPointsTranslateMean_of_integral_combination : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), GlobalTheory.Member.IotaOK Dw W ι → ∀ (l₂ : Geo.Tor.Level H) (e : AE D), IsHalfIdem l₂ e → Nat.Coprime l₂.M (GlobalTheory.Tow.badN D) → ∀ (O : Subring ℂ), ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e l₂.M O, ∃ u : (Fin V.rank → LevQ Dw l₂) → ℂ, (∀ q, u q ∈ O) ∧ f = transSum ψ V W l₂ ι e f₀ u := by
  first | exact @GlobalTheory.LevelSeries.ToSum.exists_transSum_of_mem_trSp | exact GlobalTheory.LevelSeries.ToSum.exists_transSum_of_mem_trSp | (intros; apply GlobalTheory.LevelSeries.ToSum.exists_transSum_of_mem_trSp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSectionMulAdelicFunctionLevelCover
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.CompRat

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in

theorem exists_sec_mul_adelic_fun : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → IsUnf U → FnAlgClosed Xo c → ∀ w : GA D V → c.F, (∀ h h' : GA D V, finHom V h = finHom V h' → w h = w h') → (∀ γ ∈ GQ V, ∀ h, w (γ * h) = w h) → (∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, w (h * u) = w h) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∃ f' ∈ sec Xo c a n, (∀ h : GA D V, rdU U f' (dict h).1 (dict h).2 = σ (w h) * rdU U f (dict h).1 (dict h).2) ∧ (∀ la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (U.X k).Ψ r, rdU U f ∈ holSub0 U.X la → rdU U f' ∈ holSub0 U.X la) ∧ ∀ lam : HeightOneSpectrum (𝓞 c.F), (∀ h, lam.valuation c.F (w h) ≤ 1) → (∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f) → ∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f' := by
  intro D H Dw l Xo c σ V r hr U dict io g e F ik φ th x₀ hio hpq hA hσ hW hL hdom hU hF w hfin hQ hK a n f hf
  classical
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.T.exists_factor_components_of_adelic_invariant_function D H Dw l Xo c σ V r hr U dict io g e F ik φ th x₀ hio hpq hA hσ hW hL hdom
    w hfin hQ hK
  have hr1 : 1 ≤ r := hU.1 ▸ hpq
  obtain ⟨χ, hχ, hid, -, -, hrd⟩ := GlobalTheory.T.exists_orthogonal_idempotent_sections_indicating_components D.host.E H Dw l Xo c σ r U hr1 hσ hU hF
  let v : U.Comp → c.F := fun k => if ∃ h : GA D V, (dict h).1 = k then v₀ k else 0
  have hv : ∀ h : GA D V, v (dict h).1 = w h := fun h => by
    simp only [v]
    rw [if_pos ⟨h, rfl⟩, hv₀ h]
  have he : (∑ k, v k • χ k) ∈ sec Xo c 0 0 :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hχ k)
  have hval : ∀ k x, x ∈ (U.X k).dom → rdU U (∑ k, v k • χ k) k x = σ (v k) := by
    intro k x hx
    rw [map_sum, Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single k]
    · rw [LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, (hrd k k x hx).1 rfl, smul_eq_mul, mul_one]
    · intro k' _ hk
      rw [LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, (hrd k' k x hx).2 hk.symm, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hmul : rdU U ((∑ k, v k • χ k) * f) = fun k x => σ (v k) * rdU U f k x := by
    funext k x
    rw [GlobalTheory.rdU_mul_apply D.host.E H Dw l Xo c σ r U]
    by_cases hx : x ∈ (U.X k).dom
    · rw [hval k x hx]
    · rw [rdU_mem_offZero U f k x hx, mul_zero, mul_zero]
  refine ⟨(∑ k, v k • χ k) * f, ?_, fun h => ?_, fun la hla => ?_, fun lam hw hint => ?_⟩
  · have := sec_mul Xo c 0 a 0 n he hf
    simpa only [zero_add] using this
  · rw [hmul, ← hv h]
  · rw [hmul]
    exact (GlobalTheory.CompRat.holSub_compMul D.host.E r U.Comp U.X la (fun k => σ (v k)) (rdU U f)).2 hla
  · have hvi : ∀ k, lam.valuation c.F (v k) ≤ 1 := by
      intro k
      by_cases hk : ∃ h : GA D V, (dict h).1 = k
      · obtain ⟨h, rfl⟩ := hk
        rw [hv h]
        exact hw h
      · simp only [v]
        rw [if_neg hk, map_zero]
        exact zero_le_one
    let ε := (Fintype.equivFin U.Comp).symm
    rw [← ε.sum_comp (fun k => v k • χ k)]
    exact GlobalTheory.T.integralComb_idempotentSections_nonneg_over_place D.host.E H Dw l Xo c lam _ (fun i => χ (ε i)) (fun i => v (ε i))
      (fun i => ⟨hχ _, hid _⟩) (fun i => hvi _) f hint

end GlobalTheory.CompRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipScalarPrimePowIntegralAtLevelPlacesStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flipScalar_primePow_integral_at_levelPlaces : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l : ℕ), ChiData χW χ M₀ → l.Prime → M₀ ≠ 0 → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)), ∃ c : ℕ, ∀ (eT : AE D) (x : (AE D)ˣ), IsIdemSum eT T → (∀ PP ∈ T, ((M₀ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsFlipDet V eT M₀ x → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → Odd M₀ → Nat.Coprime M₀ (GlobalTheory.Tow.badN D) → (l : ℂ) ^ c * flipScal χW V W T M₀ x ∈ O := by
  first | exact @GlobalTheory.LevelSeries.flipScal_pow_mem | exact GlobalTheory.LevelSeries.flipScal_pow_mem | (intros; apply GlobalTheory.LevelSeries.flipScal_pow_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockSubstitutionHomogeneousCoeffMemAfterScalingStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSubstitution_homogeneous_coeff_mem_after_scaling : ∀ (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (u : GlobalTheory.ExportSeries.GLR D n) (O : Subring ℂ) (z : ℂ),
    (∀ τ x y, z * (((u τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) x y ∈ O ∧
      z * ((u τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) x y ∈ O) →
    ∀ (d : ℕ) (P : MvPolynomial (FVar D m n) ℂ), P.IsHomogeneous d → (∀ mo, P.coeff mo ∈ O) →
      ∀ mo, z ^ d * (GlobalTheory.ExportSeries.fockSubst p u P).coeff mo ∈ O := by
  first | exact @GlobalTheory.FockCoefInt.fockSubst_coeff_mem | exact GlobalTheory.FockCoefInt.fockSubst_coeff_mem | (intros; apply GlobalTheory.FockCoefInt.fockSubst_coeff_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockSubstitutionPreservesHarmonicLetterPolynomiaStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSubstitution_preserves_harmonicLetterPolynomials : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (m n : ℕ) (lt : LtN Dw n ≃ FVar D m n),
    m = Dw.p + Dw.q → (∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) → IsLetters Dw lt →
    ∀ (u : GlobalTheory.ExportSeries.GLR D n) (wa : (D.host.E →+* ℂ) × ℕ → ℕ) (Q : MvPolynomial (LtN Dw n) ℂ),
      Q ∈ HHa Dw.mult n ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)) →
      MvPolynomial.rename lt.symm (GlobalTheory.ExportSeries.fockSubst (m := m) (fun _ => Dw.p) u (MvPolynomial.rename lt Q)) ∈
        HHa Dw.mult n ℂ ComplexEmbedding.conjugate (InPsi H) (fun τ i => wa (τ, i)) := by
  first | exact @GlobalTheory.FockSubstHarm.rename_fockSubst_mem_HHa | exact GlobalTheory.FockSubstHarm.rename_fockSubst_mem_HHa | (intros; apply GlobalTheory.FockSubstHarm.rename_fockSubst_mem_HHa <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTwistDetCharEqOneOfSupportedTypePlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistTypeDet

open Classical in

theorem detChar_eq_one_of_suppAt : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ (A : Type) [CommGroup A] (t : Twist D A), t.Good → B.admitted t.Q → ∀ (u : G0 B.G.Pg T.rank) (κ : GA D T), Lev.IsLevelLift T B.F.βT B.G.levT u κ → SuppAt (idem B.G.Pg) T κ → detChar T t.chi κ = 1 := by
  intro D S T B hB _ A _ t ht hadm u κ hlift hsupp
  have hst : Lev.finE T κ ∈ St B.F.βT := Formalism.L2.DIV.parLev_St hlift.2.1
  rw [GlobalTheory.TwistDetStabAll.detChar_eq_prod_res B hB t ht hlift.1 hst]
  refine Finset.prod_eq_one fun PP hPP => ?_
  obtain ⟨P, hPg, hQ, hsplit⟩ := hadm.1.split
  have hnot : PP ∉ B.G.Pg := fun h => Finset.disjoint_left.mp hadm.1.disj h (Finset.mem_union_right _ hPP)
  rw [GlobalTheory.ExportSeries.redFn_eq_one_of_suppAt B.F.βT hsplit hPg (hQ (Finset.mem_union_right _ hPP)) hnot hst hsupp,
    map_one, map_one]

end GlobalTheory.TwistTypeDet
end

