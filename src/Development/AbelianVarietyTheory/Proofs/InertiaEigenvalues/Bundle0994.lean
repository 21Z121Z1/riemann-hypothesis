import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0934
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0982
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0520
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0440
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0985
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0454
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0722
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0401
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0381
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0759
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0983
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0341
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0118
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousNormFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeHalfIffFrameMatrixIntegral
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.HalfOInt

open Formalism.IndefR.Fin.LevelGroupLemmas.Lat Matrix

theorem idem_mem_at (D : D7) (e : AE D) (PP : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E))
    (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (hP : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (a : D.host.E) (ha : a ∈ D.host.AA) :
    toEAf D e * eToEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  set n : ℕ := Ideal.absNorm D.host.𝔟 with hn
  have hnP : (n : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro h
    obtain ⟨p, hp, hpP⟩ := GlobalTheory.HalfCompare.exists_prime_under PP
    exact hP ((hpP _).2 (((GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hp).1 ((hpP _).1 h)).mul_right _))
  have hn0 : (n : 𝓞 D.host.E) ≠ 0 := fun h => hnP (h ▸ zero_mem _)
  have hn0' : (n : D.host.E) ≠ 0 := by
    intro h
    apply hn0
    have : n = 0 := by exact_mod_cast h
    rw [this, Nat.cast_zero]
  have h1 : finPart D (e * incA D (((n : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hnP ((he.2 _ hn0).2 h)
  have h2 := GlobalTheory.IdemIntegral.toEAf_mem_of_finPart h1
  obtain ⟨c, hc⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem D.host.𝔟) ha
  have h3 := mul_mem h2 (GlobalTheory.IdemIntegral.eToEAf_int D c)
  rw [map_mul, GlobalTheory.IdemIntegral.toEAf_incA, mul_assoc, ← map_mul] at h3
  convert h3 using 3
  have hc' : (c : D.host.E) = a * n := hc
  have hcast : ((n : 𝓞 D.host.E) : D.host.E) = n := map_natCast (algebraMap (𝓞 D.host.E) D.host.E) n
  rw [hc', hcast]
  field_simp

theorem idem_mem_intAf (D : D7) (e : AE D) (P : Finset (Pl D.host.E)) (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (a : D.host.E) (ha : a ∈ D.host.AA) :
    toEAf D e * eToEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [map_sum, Finset.sum_mul]
  exact sum_mem fun PP hPP => idem_mem_at D _ PP (hes PP hPP) (hP PP hPP) a ha

theorem smul_genE {D : D7} {S T : HSp D} (e : AE D) (c : EAf D) (τ : Fin T.rank → EAf D)
    (σ : Fin S.rank → EAf D) :
    e • genE (S := S) (T := T) c τ σ = genE (toEAf D e * c) τ σ := by
  ext i j
  simp only [genE, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_liftE, mul_assoc]

end GlobalTheory.HalfOInt

namespace GlobalTheory.HalfOInt
open Formalism.IndefR.Fin.LevelGroupLemmas.Lat Matrix

set_option maxHeartbeats 4000000 in

theorem frMapO_int_of_half {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    {u : WO S T} (hu : u ∈ latO S T ΛS ΛT (fun _ => True)) (hh : IsHalf e u) :
    IsIntM (frMapO S T βS βT u) := by
  have hx : e • u = u := Matrix.ext fun i j => hh i j
  rw [← hx]
  clear hx hh
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, _, a, ha, s, hs, t, ht, rfl⟩ := hw
    show IsIntM (frMapO S T βS βT (e • genL S T α a s t))
    rw [genL_eq_genE, smul_genE, genE, frMapO_mapLiftE, mul_vecMulVec_mul]
    intro i j
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    refine mul_mem ?_ (mul_mem ?_ ?_)
    · rw [← mul_assoc]
      exact mul_mem (idem_mem_intAf D e P he hP a ha)
        (Subring.subset_closure (Or.inr ⟨⟨α, fun v => hα v⟩, rfl⟩))
    · exact (fT _).1 (mem_hatL_of_mem ht) i
    · rw [Matrix.vecMul_vecMul]
      have e : (fun l => (S.gram.map (eToEAf D) * (βS : Matrix (Fin S.rank) (Fin S.rank) (EAf D))) l j) =
          S.gram.map (eToEAf D) *ᵥ (fun i => (βS : Matrix (Fin S.rank) (Fin S.rank) (EAf D)) i j) := by
        funext l; rw [Matrix.mul_apply]; rfl
      show (fun k => sR D (eToEAf D (s k))) ⬝ᵥ
        (fun l => (S.gram.map (eToEAf D) * (βS : Matrix (Fin S.rank) (Fin S.rank) (EAf D))) l j) ∈ _
      rw [e]
      exact hform_int hS hs (col_mem_hatL fS j)
  | zero =>
    rw [smul_zero, frMapO_zero]
    exact fun _ _ => zero_mem _
  | add x y _ _ hx hy =>
    rw [smul_add, frMapO_add]
    exact isIntM_add hx hy
  | neg x _ hx =>
    rw [smul_neg, frMapO_neg]
    exact fun i j => neg_mem (hx i j)

end GlobalTheory.HalfOInt

namespace GlobalTheory.HalfOInt
open Formalism.IndefR.Fin.LevelGroupLemmas.Lat Matrix

theorem sum_decomp {R : Type} [CommRing R] {m n N : ℕ} (M : Matrix (Fin m) (Fin n) R) (g Y : Fin N → Fin n → R)
    (hb : ∑ k, vecMulVec (g k) (Y k) = 1) (c z : R) (hM : (c * z) • M = M) :
    ∑ k, c • vecMulVec (z • (M *ᵥ g k)) (Y k) = M := by
  have h : ∀ k, c • vecMulVec (z • (M *ᵥ g k)) (Y k) = (c * z) • (M * vecMulVec (g k) (Y k)) := by
    intro k
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, mul_apply,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl fun k _ => h k, ← Finset.smul_sum, ← Matrix.mul_sum, hb, Matrix.mul_one, hM]

set_option maxHeartbeats 4000000 in

theorem mem_latO_of_int {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    {t : WO S T} (ht : IsHalf e t) (hN : IsIntM (frMapO S T βS βT t)) :
    t ∈ latO S T ΛS ΛT (fun _ => True) := by
  have ha := GlobalTheory.HalfAdjLattice.natCast_mem_AA (D := D) (D.host.QS * D.host.q)
  generalize D.host.QS * D.host.q * Ideal.absNorm D.host.ccK = n at hP ha
  obtain ⟨N, g, s, hg, hs, hb⟩ := GlobalTheory.HalfAdjLattice.exists_dual_families S hS
  have hz := GlobalTheory.HalfAdjLattice.toEAf_int (GlobalTheory.HalfAdjLattice.idem_div_int he hP)
  have hze := GlobalTheory.HalfAdjLattice.natCast_mul_idem_div he hP
  generalize e * incA D (n : D.host.E)⁻¹ = z at hz hze
  set M : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := Matrix.map t (toEAf D) with hMdef
  have hN' : IsIntM ((βT⁻¹).val * M * βS.val) := hN
  have hb' : ∑ k, vecMulVec (fun i => eToEAf D (g k i))
      (vecMul (fun a => sR D (eToEAf D (s k a))) (S.gram.map (eToEAf D))) = 1 := by
    ext i j
    have h1 := congrArg (eToEAf D) (congrFun (hb (Pi.single j 1)) i)
    rw [Finset.sum_apply, map_sum] at h1
    rw [Matrix.sum_apply]
    have h2 : eToEAf D ((Pi.single j 1 : Fin S.rank → D.host.E) i) = (1 : Matrix (Fin S.rank) (Fin S.rank) (EAf D)) i j := by
      rw [Pi.single_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [← h2, ← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mulVec_single_one]
    simp only [vecMulVec_apply, vecMul, dotProduct, map_apply, sR_eTo, Pi.smul_apply, smul_eq_mul, map_mul, map_sum,
      Matrix.col, transpose_apply]
    exact mul_comm _ _
  have hM : ((eToEAf D (n : D.host.E) * ((1 : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F))) * toEAf D z) • M = M := by
    have h1 : (eToEAf D (n : D.host.E) * ((1 : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F))) * toEAf D z = toEAf D e := by
      rw [← hze, map_mul, toEAf_incA, ← Algebra.TensorProduct.one_def, mul_one]
    rw [h1]
    ext i j
    simp only [hMdef, Matrix.smul_apply, map_apply, smul_eq_mul]
    rw [← map_mul, ht i j]
  have key := sum_decomp M (fun k i => eToEAf D (g k i))
    (fun k => vecMul (fun a => sR D (eToEAf D (s k a))) (S.gram.map (eToEAf D))) hb' _ _ hM
  have hdec : t = ∑ k, genE (S := S) (T := T)
      (eToEAf D (n : D.host.E) * ((1 : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)))
      (toEAf D z • (M *ᵥ fun i => eToEAf D (g k i))) (fun a => eToEAf D (s k a)) := by
    ext i j
    have h1 := congrFun (congrFun key i) j
    rw [Matrix.sum_apply] at h1
    rw [Matrix.sum_apply]
    unfold genE
    simp only [map_apply]
    rw [← liftE_sum, h1]
    have h0 : infPart D (t i j) = 0 := by rw [← ht i j, map_mul, infPart_of_idemSum he, zero_mul]
    exact (liftE_toEAf _ h0).symm
  rw [hdec]
  refine AddSubgroup.sum_mem _ fun k _ => genE_mem ?_ ha ?_ (mem_hatL_of_mem (hs k))
  · intro v; rw [map_one]; exact one_mem _
  · exact Submodule.smul_mem _ (⟨_, hz⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E)
      (GlobalTheory.HalfAdjLattice.mulVec_mem_hatL fT fS hN' (mem_hatL_of_mem (hg k)))

end GlobalTheory.HalfOInt

namespace GlobalTheory.HalfOInt

theorem mem_latO_iff_frMapO_int : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ w : WO S T, IsHalf e w → (w ∈ latO S T ΛS ΛT (fun _ => True) ↔ IsIntM (frMapO S T βS βT w)) := by
  intro D S T ΛS ΛT βS βT hS _ fS fT P e he hP w hw
  exact ⟨fun hu => frMapO_int_of_half hS fS fT he hP hu hw, fun hN => mem_latO_of_int hS fS fT he hP hw hN⟩

end GlobalTheory.HalfOInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualFrameConjugatePlaceIntegral
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
open Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult

namespace GlobalTheory.ConjInt
open GlobalTheory.StdFrames GlobalTheory.AdIsom GlobalTheory.IdemSupport

theorem frame_mat_le_one : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (g : GA D V) (Q : Formalism.L2.DIV.Pl D.host.E), (∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * (finE V g)⁻¹ * β).val a b)) ≤ 1) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP Q) ((β⁻¹ * finE V g * β).val a b)) ≤ 1 := by
  intro D V β Λ N hSD g Q h a b
  obtain ⟨hGi, U', hU'i, hU'⟩ := unimod_of_isSD hSD
  have hX : Formalism.UG.cT (sg D) (finE V g).val * GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM V.gram * (finE V g).val =
      GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM V.gram := GlobalTheory.LevSplit.finE_mem_UA V g
  have hYsub := GlobalTheory.ConjLt.conj_sub_one (sg D) β (finE V g) _ U' hX hU'
  have hY : (β⁻¹ * finE V g * β).val = U' * Formalism.UG.cT (sg D) (β⁻¹ * (finE V g)⁻¹ * β).val *
      (Formalism.UG.cT (sg D) β.val * GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM V.gram * β.val) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hU'] at hYsub
    exact sub_left_inj.1 hYsub
  have hM : ∀ i j, Valued.v (cpt (GlobalTheory.IdemSupport.cP Q)
      ((Formalism.UG.cT (sg D) (β⁻¹ * (finE V g)⁻¹ * β).val) i j)) ≤ 1 := by
    intro i j
    exact (cpt_cjA_le_iff Q _).2 (h j i)
  have hint : ∀ x ∈ GlobalTheory.StdFrames.OA D, Valued.v (cpt (GlobalTheory.IdemSupport.cP Q) x) ≤ 1 :=
    fun x hx => (mem_OA x).1 hx (GlobalTheory.IdemSupport.cP Q)
  rw [hY, Matrix.mul_apply, map_sum]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul, Valuation.map_mul, Matrix.mul_apply, map_sum]
  refine mul_le_one' ?_ (hint _ (hGi j b))
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [map_mul, Valuation.map_mul]
  exact mul_le_one' (hint _ (hU'i a i)) (hM i j)

end GlobalTheory.ConjInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesCharacterInverse
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.StateLevel

theorem level_char_allSt : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ _ w _ x => ∀ l : StrictHenselianAcyclic hL x, (∀ g : Gc B w.px, x.m.z.cG (x.m.z.R.eG g) ∈ (Dof x).nexp.U ↔ g ∈ x.m.z.F.P0) ∧
  ∀ i b (g : x.m.z.F.P0) (h : x.m.z.cG (x.m.z.R.eG g) ∈ (Dof x).nexp.U), l.b.ser.ex.ρ.e i b ((Dof x).nexp.psiU i b ⟨_, h⟩ : (FractionRing ((Dof x).ntw.O i))ˣ) = ((Dof x).what₂.embLL (x.m.z.F.ψ0 g : (Dof x).what₂.LLˣ))⁻¹ := by
  intro hL
  refine StepW.of_all fun _ _ _ _ _ _ _ _ _ x l => ?_
  have hU : (Dof x).nexp.U = Formalism.IndefR.NX.U (Dof x).nd := l.b.Bs.exp.U_eq
  refine ⟨fun g => ?_, fun i b g h => ?_⟩
  · rw [hU]
    exact (l.rat.rat.lvl g).symm
  · have hu' : (x.m.z.R.eG.trans x.m.z.cG) g ∈ Formalism.IndefR.NX.U (Dof x).nd := hU ▸ h
    have e := l.b.Bs.psiU i b _ h hu'
    have e2 := l.rat.rat.psi g hu'
    have h1 := l.b.ser.ex.good.e_LL0 i b (psiUOf (Dof x).nd (NX.xiRed (Dof x)) l.rat.In.θ ⟨_, hu'⟩)
    refine (congrArg (l.b.ser.ex.ρ.e i b) e).trans (h1.trans ?_)
    change (Dof x).what₂.embLL ((psiUOf (Dof x).nd (NX.xiRed (Dof x)) l.rat.In.θ ⟨_, hu'⟩ : (↥(Dof x).LL0)ˣ) : (Dof x).what₂.LL) = _
    rw [e2, Units.val_inv_eq_inv_val, map_inv₀]

end GlobalTheory.StateLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardFrameNonsplitMaxCompactInLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open scoped TensorProduct

noncomputable section
set_option maxHeartbeats 1000000

namespace GlobalTheory.NonSplitLevel

theorem comp_swapCast {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2) (Q : HeightOneSpectrum (𝓞 E))
    (x y : E ⊗[F2] FiniteAdeleRing (𝓞 F2) F2)
    (e : Algebra.TensorProduct.map (AlgHom.id F2 E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F2 (Q.under (𝓞 F2))) x =
      Algebra.TensorProduct.map (AlgHom.id F2 E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F2 (Q.under (𝓞 F2))) y) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F1 (Q.under (𝓞 F1))) (AlgHom.id F1 E) ((swapCast h).symm x) =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F1 (Q.under (𝓞 F1))) (AlgHom.id F1 E) ((swapCast h).symm y) := by
  subst h
  have key : ∀ z : E ⊗[F1] FiniteAdeleRing (𝓞 F1) F1,
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F1 (Q.under (𝓞 F1))) (AlgHom.id F1 E) ((swapCast (rfl : F1 = F1)).symm z) =
        Algebra.TensorProduct.comm F1 E _
          (Algebra.TensorProduct.map (AlgHom.id F1 E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F1 (Q.under (𝓞 F1))) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [key, key, e]

variable {D : D7}

theorem projV_eq_one {V : TH.HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : Formalism.IndefR.principalLevelFrame.RowPsi V n}
    (hP : StdFrame hF P) (κ : GAf D.host.E n) (Q : PlE D.host)
    (hκ : (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map
      (compAt D.host.E (HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) Q)) = 1) :
    GlobalTheory.FinZeta.projV V (Q.under (𝓞 D.host.F)) (P.ψ κ) = 1 := by
  classical
  obtain ⟨⟨β, β', h1, -, hβ⟩, -⟩ := hP
  let g := (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F (Q.under (𝓞 D.host.F))) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hK : ((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (swapCast hF).symm).map g = 1 := by
    ext i j
    have e2 := congrFun (congrFun hκ i) j
    rw [Matrix.map_apply] at e2
    rw [Matrix.map_apply, Matrix.map_apply]
    rw [Matrix.one_apply] at e2 ⊢
    split_ifs at e2 ⊢
    · exact (comp_swapCast hF Q _ 1 (e2.trans (map_one _).symm)).trans (by rw [map_one, map_one])
    · exact (comp_swapCast hF Q _ 0 (e2.trans (map_zero _).symm)).trans (by rw [map_zero, map_zero])
  refine GlobalTheory.AdelicU.matHom_injective _ D.sp.cm.sig V.gram (Units.ext ?_)
  rw [MonoidHom.map_one, Units.val_one]
  have e1 : (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.FinZeta.projV V (Q.under (𝓞 D.host.F)) (P.ψ κ))).1 =
      (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (P.ψ κ)).map g :=
    Matrix.ext fun i j => (GlobalTheory.FinZeta.LevelOff.evalV_finPart (Q.under (𝓞 D.host.F)) _).symm
  rw [e1, hβ κ, Matrix.map_mul, Matrix.map_mul, hK, Matrix.mul_one, ← Matrix.map_mul, h1,
    Matrix.map_one _ (map_zero g) (map_one g)]

theorem split_of_not_conj {Q : PlE D.host} (h : ¬ Formalism.IndefR.Lev.IsConjPl Q Q) : IsSplitPl D.host Q := by
  unfold Formalism.IndefR.Lev.IsConjPl at h
  push Not at h
  obtain ⟨c, hc, h⟩ := h
  have e : star (c : D.host.E) = D.host.conj c := by
    apply D.host.φ₀.injective
    have := D.host.isCMField_hostE
    exact (IsCMField.complexEmbedding_complexConj _ D.host.φ₀ _).trans
      (D.host.conjE_apply D.host.φ₀ _).symm
  exact ⟨c, hc, fun y hy hyQ => h y hyQ (hy.trans e.symm)⟩

theorem mem_level {V : TH.HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : Formalism.IndefR.principalLevelFrame.RowPsi V n}
    (hP : StdFrame hF P) {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hB : Formalism.IndefR.Lev.IsBaseFrame V β Λ 1) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (hL : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → IsSplitPl D.host PP) {w' : PlE D.host} (hw : ¬ IsSplitPl D.host w')
    {κ : GAf D.host.E n} (hU : κ ∈ Umax D.host.E n)
    (hT : TrivOutside {HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w'} κ) :
    P.ψ κ ∈ Formalism.IndefR.Links.levS V β L ∧ Formalism.IndefR.Lev.levChi V β L (P.ψ κ) = 1 := by
  have hS := (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hB (P.into κ)).2 ((hP.2 κ).1 hU)
  have hred : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V (P.ψ κ)) = 1 := by
    intro PP hPP
    refine GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {PP.under (𝓞 D.host.F)} hS (fun u hu => ?_) (Finset.mem_singleton_self _)
    rw [Finset.mem_singleton.1 hu]
    refine projV_eq_one hP κ PP (hT _ fun e => ?_)
    have e' : HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) PP =
        HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w' := e
    exact GlobalTheory.SphNonSplit.not_split_of_overPl D (w := w') (w' := PP)
      (v := HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w') rfl
      (congrArg HeightOneSpectrum.asIdeal e') hw (hL PP hPP)
  refine ⟨⟨P.into κ, GlobalTheory.LevSplit.mem_lev_of_red _ _ β L _ (GlobalTheory.LevSplit.finE_mem_UA V _) hS hred⟩, ?_⟩
  unfold Formalism.IndefR.Lev.levChi
  rw [GlobalTheory.LevSplit.levFn_eq_one β L _ hred, Units.val_one]

theorem lift_level : OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (i : Fin (w.st Z).toD7.R.m)
      (P : Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (w.st Z).toD7.R.nV), StdFrame Y.hF P →
      ∀ w' : PlE (w.st Z).toD7.host, ¬ IsSplitPl (w.st Z).toD7.host w' →
      ∀ κ ∈ Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
        TrivOutside {HeightOneSpectrum.under (𝓞 (maximalRealSubfield (w.st Z).toD7.host.E)) w'} κ →
        P.ψ κ ∈ Formalism.IndefR.Links.levS _ (z.R.toRealDat.βV i)
            (Formalism.IndefR.RecTie.datVP z.R.toRealDat i (Y.tupT (w.st Z).toD7.what₂.mu0) (z.R.toRealDat.levR z.F.lv2 false)) ∧
          Formalism.IndefR.Lev.levChi _ (z.R.toRealDat.βV i)
            (Formalism.IndefR.RecTie.datVP z.R.toRealDat i (Y.tupT (w.st Z).toD7.what₂.mu0) (z.R.toRealDat.levR z.F.lv2 false))
            (P.ψ κ) = 1 := by
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w _ Z Wt hX z p0 Y _ _ _ _ _ i P hP w' hw κ hU hT => ?_
  have hlev := z.pins.char.base.lev
  obtain ⟨c, hc⟩ := hlev.βV i
  rw [one_pow] at hc
  refine mem_level hP hc _ (fun PP hPP => ?_) hw hU hT
  rcases hPP with h | h
  · obtain ⟨k, hk⟩ := (hlev.Pg PP).1 h
    exact GlobalTheory.SphNonSplit.split_of_over_g _ k (GlobalTheory.Mem.TypePl.div_over _ hk)
  · exact split_of_not_conj ((hlev.Q_pl _ PP h).2 PP h)

end GlobalTheory.NonSplitLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterUnramifiedInf
section
noncomputable section

namespace GlobalTheory.LiftChar

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

theorem charAt (D : D7) (cf : CharFrame D) (C : CharSide D cf) (j : Fin D.R.m) :
    ∃ μ : D.naut.CG 1, (C.e1 μ).1 = cf.mu0 j ∧ D.naut.csd μ ∧
      (∀ w, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG μ w) ∧ D.naut.unr (D.naut.locG D.naut.etaTinv w)) ∧
      ∀ τ, D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {-(1 / 2 : ℂ)} ∧
        D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) = {(1 / 2 : ℂ)} := by
  have hm := cf.isMu0 j
  refine ⟨C.e1.symm ⟨cf.mu0 j, hm.unitary⟩, by simp, ?_, ?_, ?_⟩
  · rw [C.csd, Equiv.apply_symm_apply]
    exact GlobalTheory.CsdTriv.isCSD_of_trivOn _ _ _ hm.triv
  · intro w hw
    refine ⟨(C.unr_iff _ w).2 ?_, (C.unr_iff _ w).2 ?_⟩
    · rw [Equiv.apply_symm_apply]
      refine hm.unr w fun k hk => hw ?_
      exact (Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hk).2.2.1
    · rw [C.etaTinv]
      intro x hx
      have := cf.isEta.unr w x hx
      show ((cf.eta.loc w) x)⁻¹ = 1
      rw [this, inv_one]
  · have hinf : (C.e1 D.naut.etaTinv).1.HasInfQ (embPsi D.host) (fun _ => -(1/2 : ℚ)) := by
      rw [C.etaTinv]
      refine ⟨fun _ => -1, fun _ => by norm_num, fun k => ?_⟩
      have h := cf.isEta.inf k
      show (((cf.eta.inf k)⁻¹ : ℂˣ) : ℂ) = _
      rw [Units.val_inv_eq_inv_val, h]
      simp only [zpow_one, zpow_neg_one, Finset.prod_inv_distrib]
    intro τ
    obtain ⟨h1, h2⟩ := C.infG _ _ hinf (D.eTau τ)
    refine ⟨?_, ?_⟩
    · show D.naut.infG _ (embPsi D.host (D.eTau τ)) = _
      rw [h1]
      congr 1
      push_cast
      ring
    · show D.naut.infG _ ((starRingEnd ℂ).comp (embPsi D.host (D.eTau τ))) = _
      rw [h2]
      congr 1
      push_cast
      ring

theorem main : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.LiftRef.AtRows hL fun D cf _ _ a _ => ∀ j : Fin D.R.m, ∃ μ : D.naut.CG 1, (a.chr.e1 μ).1 = cf.mu0 j ∧ D.naut.csd μ ∧ (∀ w, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG μ w) ∧ D.naut.unr (D.naut.locG D.naut.etaTinv w)) ∧ ∀ τ, D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {-(1 / 2 : ℂ)} ∧ D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) = {(1 / 2 : ℂ)} := by
  intro _ hL
  unfold GlobalTheory.LiftRef.AtRows OverRows EvLgG
  refine evG_all fun K => lg_all K fun B f T _ => ?_
  intro _ w _ Z Wt hX z p0 Y _ _ _ _ _ Rw a M tup Q _ _
  exact charAt _ _ a.chr

end GlobalTheory.LiftChar

end
end

