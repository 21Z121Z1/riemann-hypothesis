import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0012
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSchwartzMemSpanDatumTranslates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0124
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0023
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0721
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0712
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0326
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0668
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0337
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0722

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLatOfIsIntMAdjConjHalf
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

noncomputable section

namespace GlobalTheory.ConjLatAdj

section General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
  IsDedekindDomain NumberField Matrix GlobalTheory.LatVac GlobalTheory.AdelicLatMove GlobalTheory.PlaceVec GlobalTheory.DatumFourier

variable {D : D7}

theorem tie_mul_inv_mem {Q : HeightOneSpectrum (𝓞 D.host.E)} {f : AE D} (hf : GlobalTheory.IdemSupport.Comparison₂ Q f)
    (hQ : FractionalIdeal.count D.host.E Q D.host.AA = 0) {c : D.host.E} (hc : c ∈ D.host.AA⁻¹) :
    toEAf D (f * incA D c) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have h0 : FractionalIdeal.count D.host.E Q D.host.AA⁻¹ = 0 := by
    rw [FractionalIdeal.count_inv, hQ, neg_zero]
  obtain ⟨b, t, ht, hbc⟩ := GlobalTheory.exists_den_not_mem_of_count_eq_zero Q _ h0 hc
  have ht0 : t ≠ 0 := fun h => ht (h ▸ Q.asIdeal.zero_mem)
  have ht0' : (t : D.host.E) ≠ 0 := by simpa using ht0
  have h1 : finPart D (f * incA D ((t : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h; exact ht ((hf t ht0).2 h)
  have h2 := mul_mem (GlobalTheory.IdemIntegral.toEAf_mem_of_finPart h1) (GlobalTheory.IdemIntegral.eToEAf_int D b)
  have e : c = (t : D.host.E)⁻¹ * (b : D.host.E) := by
    rw [eq_inv_mul_iff_mul_eq₀ ht0']
    exact hbc
  rw [e, map_mul (incA D), ← mul_assoc, map_mul (toEAf D)]
  exact h2

theorem toEAf_cA_idem_mul_inv_mem {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (hP : GlobalTheory.ExportSeries.PlacesOK Pg Q)
    {c : D.host.E} (hc : c ∈ D.host.AA⁻¹) :
    toEAf D (cA D (GlobalTheory.ExportSeries.idem Pg) * incA D c) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨P, h1, -, hsp⟩ := hP.split
  have hS : GlobalTheory.ExportSeries.SplitSet Pg := hsp.mono h1
  rw [GlobalTheory.ExportSeries.idem, map_sum, Finset.sum_mul, map_sum]
  refine sum_mem fun PP hPP => ?_
  have ht : GlobalTheory.IdemSupport.Comparison₂ PP (GlobalTheory.ExportSeries.idemAt PP) := (hS.isIdemAt hPP).2
  refine tie_mul_inv_mem ht.conj ?_ hc
  exact hP.prime PP (Or.inl hPP) _ (Or.inr ((GlobalTheory.IdemSupport.isConjPl_iff PP _).2 rfl))

set_option maxHeartbeats 4000000 in

theorem mem_latO_of_adj_int {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (hP : GlobalTheory.ExportSeries.PlacesOK Pg Q) {x : WO S T}
    (hx : IsHalf (cA D (GlobalTheory.ExportSeries.idem Pg)) x) (hi : IsIntM (frMapAdj S T βS βT x)) :
    x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  set e : AE D := GlobalTheory.ExportSeries.idem Pg with he_def
  have he : IsIdemSum e Pg := by
    obtain ⟨P, h1, -, hsp⟩ := hP.split
    exact (hsp.mono h1).isIdemSum
  obtain ⟨L, pa, pc, hpa, hpc, hac⟩ := GlobalTheory.HostAAPartition.host_AA_partition D
  have hpc' : ∀ l, pc l ∈ D.host.AA⁻¹ := fun l => by
    refine (FractionalIdeal.mem_inv_iff (GlobalTheory.HostAAPartition.host_AA_ne_zero D)).2 fun y hy => ?_
    obtain ⟨b, hb⟩ := hpc l y hy
    exact (FractionalIdeal.mem_one_iff _).2 ⟨b, hb⟩
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D S ΛS hS
  obtain ⟨m, t, t', ht, htt⟩ := GlobalTheory.LatVacDual.dualFamily D T ΛT hT
  obtain ⟨s₁, hs₁⟩ : ∃ A : Matrix (Fin S.rank) (Fin n) D.host.E, A = Matrix.of fun a k => s k a := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ A : Matrix (Fin S.rank) (Fin n) D.host.E, A = Matrix.of fun a k => s' k a := ⟨_, rfl⟩
  obtain ⟨t₁, ht₁⟩ : ∃ A : Matrix (Fin T.rank) (Fin m) D.host.E, A = Matrix.of fun a k => t k a := ⟨_, rfl⟩
  obtain ⟨t₂, ht₂⟩ : ∃ A : Matrix (Fin T.rank) (Fin m) D.host.E, A = Matrix.of fun a k => t' k a := ⟨_, rfl⟩
  have e1 : s₁ * (s₂ᴴ * S.gram) = 1 := by
    subst hs₁ hs₂
    exact Matrix.ext fun a j => (hss a j).trans (Matrix.one_apply).symm
  have e2 : t₁ * (t₂ᴴ * T.gram) = 1 := by
    subst ht₁ ht₂
    exact Matrix.ext fun a j => (htt a j).trans (Matrix.one_apply).symm
  obtain ⟨w, hw⟩ : ∃ w : Matrix (Fin m) (Fin n) (AE D), w = (t₂ᴴ * T.gram).map (incA D) * x * s₁.map (incA D) := ⟨_, rfl⟩
  have hx' : cA D e • x = x := Matrix.ext hx
  have hw1 : cA D e • w = w := by rw [hw, ← Matrix.smul_mul, ← Matrix.mul_smul, hx']
  have hG : T.gramᴴ = T.gram := Matrix.ext fun i j => gram_star T j i
  have hw2 : ((w.map (toEAf D)).map (cF D))ᵀ = (s₁ᴴ * S.gram).map (eToEAf D) * βS.val * frMapAdj S T βS βT x *
      ((βT⁻¹).val * t₂.map (eToEAf D)) := by
    rw [hw, Matrix.map_mul (f := toEAf D), Matrix.map_mul (f := toEAf D), Matrix.map_mul (f := cF D),
      Matrix.map_mul (f := cF D), Matrix.transpose_mul,
      Matrix.transpose_mul, conj_map, conj_map, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
      frMapAdj_eq, Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc βS.val, Units.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc βT.val, Units.mul_inv, Matrix.one_mul,
      ← Matrix.mul_assoc (S.gram.map (eToEAf D)), gram_map_mul_inv, Matrix.one_mul]
  have hcol : ∀ a, (fun k => βS.val k a) ∈ Formalism.L2.Herm.hatL (F := D.host.F) ΛS := fun a => by
    refine (fS _).2 fun i => ?_
    have e : ((βS⁻¹).val *ᵥ fun k => βS.val k a) i = ((βS⁻¹).val * βS.val) i a := rfl
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have i1 : IsIntM ((s₁ᴴ * S.gram).map (eToEAf D) * βS.val) := fun k a => by
    refine GlobalTheory.PairIntegral.sum_mem_intAf ΛS (fun j => (s₁ᴴ * S.gram) k j) (fun y hy => ?_) _ (hcol a)
    obtain ⟨b, hb⟩ := (hS.2 y).1 hy _ (hs k).1
    refine ⟨b, hb.trans ?_⟩
    rw [Finset.sum_comm, hs₁]
    exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
  have i2 : IsIntM ((βT⁻¹).val * t₂.map (eToEAf D)) := fun a k => by
    rw [ht₂]
    exact (fT _).1 (pure_mem_hatL ΛT 1 (one_mem _) _ (ht k).2) a
  have hwe : ∀ i k, cA D e * w i k = w i k := fun i k => congrFun (congrFun hw1 i) k
  have hw3 : ∀ i k l, toEAf D (w i k * incA D (pc l)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun i k l => by
    have h1 : cF D (toEAf D (w i k)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [show cF D (toEAf D (w i k)) = _ from congrFun (congrFun hw2 k) i, Matrix.mul_apply]
      refine sum_mem fun p _ => mul_mem ?_ (i2 p i)
      rw [Matrix.mul_apply]
      exact sum_mem fun q _ => mul_mem (i1 k q) (hi q p)
    have h2 : toEAf D (w i k) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      have := cF_mem_int h1
      rwa [cF_cF_toEAf] at this
    rw [← hwe i k, mul_comm (cA D e) (w i k), mul_assoc, RingHom.map_mul]
    exact mul_mem h2 (toEAf_cA_idem_mul_inv_mem hP (hpc' l))
  have hxw : x = t₁.map (incA D) * w * (s₂ᴴ * S.gram).map (incA D) := by
    rw [hw, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, e2, Matrix.mul_assoc, ← Matrix.map_mul, e1,
      Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _),
      Matrix.one_mul, Matrix.mul_one]
  have hsum : x = ∑ k, ∑ i, ∑ l, (w i k * incA D (pc l)) • finTens 1 (genMap S T (pa l) (s' k) (t i)) := by
    rw [hxw]
    ext a j
    simp only [Matrix.mul_apply (M := t₁.map (incA D) * w), Matrix.mul_apply (M := t₁.map (incA D)), Matrix.sum_apply,
      Finset.sum_mul, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    have h0 : infPart D (w i k) = 0 := by
      rw [← hwe i k, RingHom.map_mul, infPart_cA (idemSum_infPart he), zero_mul]
    have hterm : ∀ l, (w i k * incA D (pc l)) * finTens 1 (genMap S T (pa l) (s' k) (t i)) a j =
        w i k * incA D (pc l * pa l * (t₁ a i * (s₂ᴴ * S.gram) k j)) := fun l => by
      have h4 : finPart D (finTens 1 (genMap S T (pa l) (s' k) (t i)) a j) =
          finPart D (incA D (pa l * t₁ a i * (s₂ᴴ * S.gram) k j)) := by
        rw [ht₁, hs₂]; rfl
      refine GlobalTheory.SplitScalar.adele_ext (by simp only [RingHom.map_mul, h0, zero_mul]) ?_
      rw [RingHom.map_mul, RingHom.map_mul, h4, ← RingHom.map_mul, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul (incA D)]
      congr 3
      ring
    rw [Finset.sum_congr rfl fun l _ => hterm l, ← Finset.mul_sum, ← map_sum, ← Finset.sum_mul]
    have hac' : ∑ l, pc l * pa l = 1 := by rw [← hac]; exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [hac', one_mul, Matrix.map_apply, Matrix.map_apply, mul_comm (incA D (t₁ a i)), mul_assoc, ← RingHom.map_mul]
  rw [hsum]
  exact sum_mem fun k _ => sum_mem fun i _ => sum_mem fun l _ =>
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (finPart_mem_intAE (hw3 i k l)) _
      (finTens_mem_latO (one_mem_intAf _) (AddSubgroup.subset_closure ⟨_, hpa l, _, (hs k).2, _, (ht i).1, rfl⟩))

end General

end GlobalTheory.ConjLatAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicHyperplaneAverageSupportResidueGLStatement
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
theorem _root_.GlobalTheory.T.mirabolicHyperplaneAverage_support_residueGL : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (PP : Pl D.host.E) (hPP : PP ∈ R.Pg) (v : FinPl D) (ρk : IsLocalRing.ResidueField (OI v) ≃+* kP PP) (a : Fin D.R.r → IsLocalRing.ResidueField (OI v)) (F : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) → ℂ), (∑ᶠ g ∈ {g : G | mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0}, F (Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g ⟨PP, hPP⟩))) = ∑ᶠ g ∈ {g : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) | ∀ w, a ⬝ᵥ w = 0 → (g : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (OI v))).mulVec w = w}, F g := by
  first | exact @GlobalTheory.DownLift.GenSplit.mirC_hyperplane_reindex | exact GlobalTheory.DownLift.GenSplit.mirC_hyperplane_reindex | (intros; apply GlobalTheory.DownLift.GenSplit.mirC_hyperplane_reindex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModulusUnramifiedCharDetHeckeDoubleCosetSplitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_unramifiedChar_det_heckeDoubleCoset_split : ∀ (D : D7) (V : HSp D) (P : Pl D.host.E) (e : AE D), IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ x : (AE D)ˣ, (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → ∀ (k : ℕ) (α : GA D V), IsHeckeElt V e (ϖ : D.host.E) k α → ∀ k₁ ∈ Mult.locPart V (KsphC V ∅) e, ∀ k₂ ∈ Mult.locPart V (KsphC V ∅) e, ∀ z : (AE D)ˣ, IsDetAt e V (k₁ * α * k₂) z → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D z = (((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ k)⁻¹ ∧ ∀ (A : Type) [CommGroup A] (χ : (AE D)ˣ →* A), (∀ y : (AE D)ˣ, (1 - e) * (y : AE D) = 1 - e → finPart D (e * (y : AE D)) ∈ intAE D → finPart D (e * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D → χ y = 1) → χ z = χ x ^ k := by
  first | exact @GlobalTheory.SplitDetValue.det_modulus_chi | exact GlobalTheory.SplitDetValue.det_modulus_chi | (intros; apply GlobalTheory.SplitDetValue.det_modulus_chi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyIrreducibleElementaryWeightModificationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monodromy_irreducible_elementary_weightModification : ModStep := by
  first | exact @GlobalTheory.PMon.modStep_holds | exact GlobalTheory.PMon.modStep_holds | (intros; apply GlobalTheory.PMon.modStep_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParahoricSchwartzMemSpanDatumTranslatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoric_schwartz_mem_span_datum_translates_alt : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (n r : ℕ), r ≤ n → ∀ ϖ : O, Irreducible ϖ → ∀ ξ : (IsLocalRing.ResidueField O)ˣ →* ℂˣ, ξ ≠ 1 → ∀ Φ Φ₀ : Matrix (Fin n) (Fin r) K → ℂ, (∀ (z : Matrix (Fin n) (Fin r) O) (u : (IsLocalRing.ResidueField O)ˣ), LowZero r (z.map (IsLocalRing.residue O)) → (u : IsLocalRing.ResidueField O) = (topL r (z.map (IsLocalRing.residue O))).det → Φ₀ (z.map (algebraMap O K)) = ((ξ u : ℂˣ) : ℂ)⁻¹) → (∀ m, Φ₀ m ≠ 0 → ∃ z : Matrix (Fin n) (Fin r) O, m = z.map (algebraMap O K) ∧ LowZero r (z.map (IsLocalRing.residue O)) ∧ IsUnit (topL r (z.map (IsLocalRing.residue O))).det) → (∃ N : ℕ, (∀ m (z : Matrix (Fin n) (Fin r) O), Φ (m + (ϖ ^ N • z).map (algebraMap O K)) = Φ m) ∧ ∀ m, Φ m ≠ 0 → ∃ z : Matrix (Fin n) (Fin r) O, algebraMap O K (ϖ ^ N) • m = z.map (algebraMap O K)) → (∀ h : GL (Fin n) O, LowZero r (h.val.map (IsLocalRing.residue O)) → ∀ m m' : Matrix (Fin n) (Fin r) K, Φ (h.val.map (algebraMap O K) * m) * Φ₀ m' = Φ m * Φ₀ (h.val.map (algebraMap O K) * m')) → Φ ∈ Submodule.span ℂ {Ψ | ∃ γ : GL (Fin r) K, Ψ = fun m => Φ₀ (m * γ.val)} := by
  first | exact @GlobalTheory.parahoric_schwartz_mem_span_datum_translates | exact GlobalTheory.parahoric_schwartz_mem_span_datum_translates | (intros; apply GlobalTheory.parahoric_schwartz_mem_span_datum_translates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_over_transport_ring_iso : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∃ c : Weil h ≃* Weil h', (∀ σ σ', WeilRel φ σ σ' ↔ c σ = σ') ∧ (∀ σ, deg (c σ) = deg σ) ∧ normV w' = normV w ∧ ∀ (M : Type) [Monoid M] (f : Weil h' →* M), GlobalTheory.WeilDeligne.IsSmooth f ↔ GlobalTheory.WeilDeligne.IsSmooth (f.comp c.toMonoidHom) := by
  first | exact @GlobalTheory.WeilTransport.weil_equiv | exact GlobalTheory.WeilTransport.weil_equiv | (intros; apply GlobalTheory.WeilTransport.weil_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisNonGraphLagrangianSumEqZeroCuspidalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rallis_nonGraphLagrangian_sum_eq_zero_cuspidal : ∀ D : D7, EisAbs D → TermMove D → TermInv D → CuspKill D → (∀ ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr, SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ Y : Lag W, Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ → Continuous fun g : GA D W => lagTerm μ 𝓕 (fr Y) (om (1, g) f₁) f₂) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → ∑' Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥}, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = 0 := by
  first | exact @GlobalTheory.RallisCusp.nonGraph_sum_eq_zero | exact GlobalTheory.RallisCusp.nonGraph_sum_eq_zero | (intros; apply GlobalTheory.RallisCusp.nonGraph_sum_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergEpsilonTransportStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_selberg_epsilon_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (ψ : AddChar k Circle) (ψ' : AddChar k' Circle), (∀ x, ψ' (i x) = ψ x) → ∀ (m : ℕ) (π : IrrRep (GL (Fin (m + 1)) k)) (π' : IrrRep (GL (Fin (m + 1)) k')) (τ : IrrRep (GL (Fin m) k)) (τ' : IrrRep (GL (Fin m) k')) (c : ℂ), RepRel i (cls π) (cls π') → RepRel i (cls τ) (cls τ') → HasPairEps ψ π.ρ τ.ρ c → HasPairEps ψ' π'.ρ τ'.ρ c := by
  first | exact @GlobalTheory.LocLanglands.hasPairEps_transport | exact GlobalTheory.LocLanglands.hasPairEps_transport | (intros; apply GlobalTheory.LocLanglands.hasPairEps_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecUniqueOfLawsStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rec_unique_of_laws : LocalConverseGL → LanglandsExhaustionGL → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w.adicCompletion E) → WD h) (ψ : AddChar (w.adicCompletion E) Circle) (e' : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ), Continuous ψ → ψ ≠ 1 → e ψ = e' ψ → LawsMin a ha e rc → LawsMin a ha e' rc' → rc = rc' := by
  first | exact @GlobalTheory.LocLanglands.Unique.eq_of_lawsMin | exact GlobalTheory.LocLanglands.Unique.eq_of_lawsMin | (intros; apply GlobalTheory.LocLanglands.Unique.eq_of_lawsMin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableCocycleOfFrobeniusMonodromyPair
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

theorem GlobalTheory.semistable_class_of_pair : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ x ∈ Dst P ρ, ∀ y ∈ Dst P ρ, (l : ℚ_[l]) • phiV P ℚ_[l] V x - x = monV P ℚ_[l] V y → ∃ (z : V ⊗[ℚ_[l]] Bst P) (c : ↥(GK K) → V), c ∈ continuousCocycles ρ ∧ (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) ∧ monV P ℚ_[l] V z = x := by
  intro l _ P AI T K V _ _ _ _ _ _ _ ρ hρ x hx y hy hxy
  obtain ⟨ι, hιC, hιact⟩ := GlobalTheory.T.exists_equivariant_log_semistable_to_deRham l P AI T
  obtain ⟨hιst, -, -⟩ := GlobalTheory.T.lTensor_semistable_to_deRham_equivariant l P ι hιC hιact K V ρ
  obtain ⟨z, hNz, hφz, hFz⟩ := GlobalTheory.T.exists_monodromy_frobenius_solution_fil l P AI T ι hιC K V x y hxy
  have hx' := (mem_Dst P ρ).mp hx
  have hy' := (mem_Dst P ρ).mp hy
  have hw : ∀ g : ↥(GK K), ∃ v : V, stRep P ρ g z - z = v ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
    intro g
    refine GlobalTheory.T.exists_eq_tmul_one_of_monodromy_frobenius_filtration l P AI T ι hιC K V (stRep P ρ g z - z) ?_ ?_ ?_
    · rw [map_sub, ← Module.End.mul_apply, monV_stRep, Module.End.mul_apply, hNz, hx', sub_self]
    · have hφz' : phiV P ℚ_[l] V z = z + y := by rw [← hφz]; abel
      rw [map_sub, ← Module.End.mul_apply, phiV_stRep, Module.End.mul_apply, hφz', map_add, hy']
      abel
    · rw [map_sub, hιst]
      exact Submodule.sub_mem _ (GlobalTheory.T.actVdR_mem_tensorDeRhamFiltration l P K V ρ 0 g _ hFz) hFz
  choose c hc using hw
  have hc' : ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z := fun g => (hc g).symm
  exact ⟨z, c, GlobalTheory.T.continuousCocycle_of_semistable_coboundary l P AI T K V ρ hρ z c hc', hc', hNz⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.ChiExtend

theorem placesOver_finite' (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem maximalIdeal_le_comap {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) {O₀ O₁ : Type}
    [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra ℤ_[p] O₀] [Module.Finite ℤ_[p] O₀]
    [CommRing O₁] [IsDomain O₁] [IsDiscreteValuationRing O₁] [Algebra ℤ_[q] O₁] [Module.Finite ℤ_[q] O₁]
    (φ : O₀ →+* O₁) (hφ : ∀ (z : ℤ_[p]) (z' : ℤ_[q]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z') :
    IsLocalRing.maximalIdeal O₀ ≤ Ideal.comap φ (IsLocalRing.maximalIdeal O₁) := by
  subst h
  have hc : φ.comp (algebraMap ℤ_[p] O₀) = algebraMap ℤ_[p] O₁ := by
    ext z
    exact hφ z z HEq.rfl
  haveI : (Ideal.comap φ (IsLocalRing.maximalIdeal O₁)).IsPrime := Ideal.comap_isPrime _ _
  have h1 : (Ideal.comap (algebraMap ℤ_[p] O₀) (Ideal.comap φ (IsLocalRing.maximalIdeal O₁))).IsMaximal := by
    rw [Ideal.comap_comap, hc]
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
  have h2 := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ h1
  rw [IsLocalRing.eq_maximalIdeal h2]

theorem continuous_of_le_comap {O₀ O₁ : Type} [CommRing O₀] [IsLocalRing O₀] [TopologicalSpace O₀]
    [IsTopologicalRing O₀] [CommRing O₁] [IsLocalRing O₁] [TopologicalSpace O₁] [IsTopologicalRing O₁]
    (h₀ : IsAdic (IsLocalRing.maximalIdeal O₀)) (h₁ : IsAdic (IsLocalRing.maximalIdeal O₁))
    (φ : O₀ →+* O₁) (hφ : IsLocalRing.maximalIdeal O₀ ≤ Ideal.comap φ (IsLocalRing.maximalIdeal O₁)) :
    Continuous φ := by
  refine continuous_of_continuousAt_zero φ ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨n, hn⟩ := (isAdic_iff.1 h₁).2 s hs
  have ho := (isAdic_iff.1 h₀).1 n
  refine Filter.mem_map.2 <| Filter.mem_of_superset (ho.mem_nhds (Ideal.zero_mem _)) fun x hx => hn ?_
  exact (Ideal.pow_right_mono hφ n |>.trans (Ideal.le_comap_pow φ n)) hx

theorem cyc_heq (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q)
    (σ : G F Ω) : HEq ((cycZ F Ω p σ : ℤ_[p]ˣ) : ℤ_[p]) ((cycZ F Ω q σ : ℤ_[q]ˣ) : ℤ_[q]) := by
  subst h
  rfl

end GlobalTheory.ChiExtend

namespace GlobalTheory.ChiExtend

theorem iotaO_injective {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc) :
    Function.Injective (iotaO N A i) := by
  show Function.Injective (((A.iotaQC i).toRingHom.comp (A.iotaQ i)).comp (algebraMap (N.O i) (FractionRing (N.O i))))
  simp only [RingHom.coe_comp]
  exact (A.iotaQC i).injective.comp ((A.iotaQ i).injective.comp (IsFractionRing.injective _ _))

theorem eq_of_dense {X O : Type*} [TopologicalSpace X] [CommRing O] [IsLocalRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (h : IsAdic (IsLocalRing.maximalIdeal O)) (hH : IsHausdorff (IsLocalRing.maximalIdeal O) O)
    {f g : X → O} (hf : Continuous f) (hg : Continuous g) {s : Set X} (hs : Dense s) (he : ∀ x ∈ s, f x = g x) :
    f = g := by
  funext x
  rw [← sub_eq_zero]
  apply hH.haus' (f x - g x)
  intro n
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  have hcl : IsClosed ((fun y => f y - g y) ⁻¹' ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O)) := by
    refine IsClosed.preimage (hf.sub hg) ?_
    exact AddSubgroup.isClosed_of_isOpen (IsLocalRing.maximalIdeal O ^ n).toAddSubgroup
      ((isAdic_iff.1 h).1 n)
  have hsub : s ⊆ (fun y => f y - g y) ⁻¹' ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := by
    intro y hy
    simp only [Set.mem_preimage, he y hy, sub_self, SetLike.mem_coe]
    exact Ideal.zero_mem _
  have := closure_minimal hsub hcl
  rw [hs.closure_eq] at this
  exact this (Set.mem_univ x)

end GlobalTheory.ChiExtend

open GlobalTheory.ChiExtend in

theorem GlobalTheory.ChiExtend.chi_eq_of_ext : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ big₁ : D.what₂.places.Pl → Finset ℂ) (L₀ L₁ : LocAll (lay0 D)), Built A M C tp.tup big₀ L₀ → Built A M C tp.tup big₁ L₁ → ∀ (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc), L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ → L₀.lay.fixZ.nd.j i₀ = L₁.lay.fixZ.nd.j i₁ → ∀ φ : L₀.lay.fixZ.nd.O i₀ →+* L₁.lay.fixZ.nd.O i₁, (∀ z, iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ (φ z) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ z) → (∀ (z : ℤ_[L₀.lay.fixZ.nd.l i₀]) (z' : ℤ_[L₁.lay.fixZ.nd.l i₁]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z') → ∀ c, 1 ≤ c → c ≤ D.R.t → ∀ σ : GE L₁.lay.fixZ.nd, ((L₁.lay.fixZ.nd.chi i₁ c σ : (L₁.lay.fixZ.nd.O i₁)ˣ) : L₁.lay.fixZ.nd.O i₁) = φ ((L₀.lay.fixZ.nd.chi i₀ c σ : (L₀.lay.fixZ.nd.O i₀)ˣ) : L₀.lay.fixZ.nd.O i₀) := by
  intro _ D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ _ _ hCheb big₀ big₁ L₀ L₁ hB₀ hB₁ i₀ i₁ hw hj φ hφ hφalg c hc1 hct σ
  obtain ⟨Sp₀, ⟨AS₀⟩, -⟩ := hB₀
  obtain ⟨Sp₁, ⟨AS₁⟩, -⟩ := hB₁
  have hw' : L₀.X.nd.w i₀ = L₁.X.nd.w i₁ := hw
  have hj' : L₀.X.nd.j i₀ = L₁.X.nd.j i₁ := hj
  have hl : L₀.lay.fixZ.nd.l i₀ = L₁.lay.fixZ.nd.l i₁ := by
    rw [← L₀.lay.fixZ.nd.w_l i₀, ← L₁.lay.fixZ.nd.w_l i₁, hw]

  have hmu : L₀.Y.muC i₀ = L₁.Y.muC i₁ := by
    have hr := L₀.X.nd.j_range i₀
    let jj : Fin D.R.m := ⟨L₀.X.nd.j i₀ - 1, by omega⟩
    have e₀ := AS₀.muC i₀ jj (by show L₀.X.nd.j i₀ - 1 + 1 = L₀.X.nd.j i₀; omega)
    have e₁ := AS₁.muC i₁ jj (by show L₀.X.nd.j i₀ - 1 + 1 = L₁.X.nd.j i₁; omega)
    apply A.chr.e1.injective
    apply Subtype.ext
    have hm : L₀.X.nd.mu i₀ = L₁.X.nd.mu i₁ := by
      exact (L₀.X.mu_w i₀).trans ((congrArg D.what₂.muTw hw').trans (L₁.X.mu_w i₁).symm)
    exact e₀.trans ((congrArg (fun m => tp.tup m jj) hm).trans e₁.symm)
  have hl₀ := (L₀.lay.fixZ.nd.lPrime i₀).out.ne_zero
  have hfin : (placesOver D.host.E (L₀.lay.fixZ.nd.l i₀) ∪ ((L₀.lay.fixZ.nd.S i₀ : Set (PlE D.host)) ∪
      (L₀.lay.fixZ.nd.Q i₀ : Set (PlE D.host))) ∪ ((L₁.lay.fixZ.nd.S i₁ : Set (PlE D.host)) ∪
      (L₁.lay.fixZ.nd.Q i₁ : Set (PlE D.host)))).Finite :=
    ((placesOver_finite' _ _ hl₀).union ((Finset.finite_toSet _).union (Finset.finite_toSet _))).union
      ((Finset.finite_toSet _).union (Finset.finite_toSet _))
  have hout : ∀ w ∉ hfin.toFinset, IsSplitPl D.host w →
      SplitOut L₀.lay.fixZ.nd i₀ w ∧ SplitOut L₁.lay.fixZ.nd i₁ w := by
    intro w hwF hsp
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Finset.mem_coe, not_or] at hwF
    obtain ⟨⟨hpl, hS₀, hQ₀⟩, hS₁, hQ₁⟩ := hwF
    exact ⟨⟨hsp, hpl, hS₀, hQ₀⟩, ⟨hsp, hl ▸ hpl, hS₁, hQ₁⟩⟩
  have hone : (fun σ : GE L₁.lay.fixZ.nd => ((L₁.lay.fixZ.nd.chi i₁ 1 σ : (L₁.lay.fixZ.nd.O i₁)ˣ) :
      L₁.lay.fixZ.nd.O i₁)) = fun σ => φ ((L₀.lay.fixZ.nd.chi i₀ 1 σ : (L₀.lay.fixZ.nd.O i₀)ˣ) :
      L₀.lay.fixZ.nd.O i₀) := by
    haveI := L₁.lay.fixZ.nd.O_complete i₁
    refine eq_of_dense (L₁.lay.fixZ.nd.O_adic i₁) inferInstance (L₁.lay.fixZ.nd.chi_cont i₁ 1)
      ((continuous_of_le_comap (L₀.lay.fixZ.nd.O_adic i₀) (L₁.lay.fixZ.nd.O_adic i₁) φ
        (maximalIdeal_le_comap hl φ hφalg)).comp (L₀.lay.fixZ.nd.chi_cont i₀ 1)) (hCheb hfin.toFinset) ?_
    rintro σ ⟨w, hwF, hsp, B, hB, hσ⟩
    obtain ⟨ho₀, ho₁⟩ := hout w hwF hsp
    have e₀ := (L₀.lay.fixZ.naut.chi_mu i₀ w ho₀).2 B σ hB hσ
    have e₁ := (L₁.lay.fixZ.naut.chi_mu i₁ w ho₁).2 B σ hB hσ
    have em := congrArg (fun m => D.naut.frobEig (D.naut.lpTw (D.naut.locG (D.naut.tw m D.naut.etaTinv) w)
      (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2))) hmu
    have e := Multiset.singleton_inj.1 (e₀.symm.trans (em.trans e₁))
    apply iotaO_injective L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁
    rw [hφ]
    exact e.symm
  have hu1 : L₁.lay.fixZ.nd.chi i₁ 1 σ = Units.map (φ : L₀.lay.fixZ.nd.O i₀ →* L₁.lay.fixZ.nd.O i₁)
      (L₀.lay.fixZ.nd.chi i₀ 1 σ) := Units.ext (congrFun hone σ)
  have key : L₁.lay.fixZ.nd.chi i₁ c σ = Units.map (φ : L₀.lay.fixZ.nd.O i₀ →* L₁.lay.fixZ.nd.O i₁)
      (L₀.lay.fixZ.nd.chi i₀ c σ) := by
    rw [L₁.lay.fixZ.nd.chi_def i₁ c hc1 hct, L₀.lay.fixZ.nd.chi_def i₀ c hc1 hct]
    simp only [MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply, map_mul, map_zpow]
    erw [MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply, map_mul, map_zpow]
    rw [hu1]
    refine congrArg _ (congrArg (· ^ _) ?_)
    apply Units.ext
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    exact (hφalg _ _ (cyc_heq _ _ hl σ)).symm
  exact congrArg Units.val key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceUnitaryIntegralMatrixKeepsLatticeStatement
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
theorem _root_.GlobalTheory.T.splitPlaceUnitary_integralMatrix_keeps_lattice : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∀ (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsProjAt φ PP → IsIdemOf φ e → ∀ (red : OI v →+* kP PP), (∀ (a : Formalism.IndefR.Lev.EAf D) (ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∃ h : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a ∈ v.adicCompletionIntegers D.host.F, red ⟨GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a, h⟩ = resS D.host.F PP ⟨a, ha⟩) → ∀ (h : GL (Fin V.rank) (OI v)) (κ : GA D V), Formalism.L2.Theta.SuppAt e V κ → grpCo φ V (frCo φ β) κ = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h → κ ∈ GfC V ∧ finE V κ ∈ Formalism.L2.DIV.St β ∧ redFn β PP (finE V κ) = Matrix.GeneralLinearGroup.map red h ∧ ∀ PP', PP' ≠ PP → ¬ Formalism.IndefR.Lev.IsConjPl PP PP' → redFn β PP' (finE V κ) = 1 := by
  first | exact @GlobalTheory.DownLift.SplitIntLift.lift_of_integral | exact GlobalTheory.DownLift.SplitIntLift.lift_of_integral | (intros; apply GlobalTheory.DownLift.SplitIntLift.lift_of_integral <;> assumption)
end

