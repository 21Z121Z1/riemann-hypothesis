import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepThetaDatumHalfEqSmul
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToEAfOrientedHermitianFormEqTraceFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.TraceFrames

theorem hO_eq_trace_mul {D : D7} (S T : HSp D) (k y : WO S T) :
    hO S T y k = Matrix.trace (HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D))
      ((k : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose) (T.gram.map (incA D))
      * (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))) := by
  simp only [hO, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [Finset.sum_comm]; enter [2, c]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem toEAf_hO_eq_trace_frames {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D))
    (βT : GL (Fin T.rank) (Datum.EAf D)) (k y : WO S T) :
    toEAf D (hO S T y k) = Matrix.trace (frMapAdj S T βS βT k * frMapO S T βS βT y) := by
  set X₀ : Matrix (Fin S.rank) (Fin T.rank) (AE D) := HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D))
      ((k : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose) (T.gram.map (incA D)) with hX
  set Y₀ : Matrix (Fin T.rank) (Fin S.rank) (AE D) := y with hY
  set A : Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D) := (βS⁻¹).val with hA
  set A' : Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D) := βS.val with hA'
  set B : Matrix (Fin T.rank) (Fin T.rank) (Datum.EAf D) := βT.val with hB
  set B' : Matrix (Fin T.rank) (Fin T.rank) (Datum.EAf D) := (βT⁻¹).val with hB'
  set Xf : Matrix (Fin S.rank) (Fin T.rank) (Datum.EAf D) := X₀.map (toEAf D) with hXf
  set Yf : Matrix (Fin T.rank) (Fin S.rank) (Datum.EAf D) := Y₀.map (toEAf D) with hYf
  have hBB : HMul.hMul B B' = (1 : Matrix (Fin T.rank) (Fin T.rank) (Datum.EAf D)) := Units.mul_inv βT
  have hAA : HMul.hMul A' A = (1 : Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D)) := Units.mul_inv βS
  have h1 : frMapAdj S T βS βT k = HMul.hMul (HMul.hMul A Xf) B := rfl
  have h2 : frMapO S T βS βT y = HMul.hMul (HMul.hMul B' Yf) A' := rfl
  have h4 : HMul.hMul Xf Yf = (HMul.hMul X₀ Y₀ : Matrix (Fin S.rank) (Fin S.rank) (AE D)).map (toEAf D) :=
    (Matrix.map_mul).symm
  have h3 : (HMul.hMul (HMul.hMul (HMul.hMul A Xf) B) (HMul.hMul (HMul.hMul B' Yf) A') :
      Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D)) = HMul.hMul A (HMul.hMul (HMul.hMul Xf Yf) A') := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B B', hBB, Matrix.one_mul]
  rw [h1, h2, h3, Matrix.trace_mul_comm, Matrix.mul_assoc, hAA, Matrix.mul_one, h4, hO_eq_trace_mul]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, map_sum]
  rfl

end GlobalTheory.TraceFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedStandardChainStabilizerRadical
section
open scoped Matrix

namespace GlobalTheory.StdChainStab

open Matrix

variable {K : Type} [Field K] {n m : ℕ}

def lowVec (b : Fin n → Fin m) (j : ℕ) (w : Fin n → K) : Prop :=
  ∀ i : Fin n, j ≤ ((b i : Fin m) : ℕ) → w i = 0

theorem lowVec_single (b : Fin n → Fin m) (c : Fin n) :
    lowVec b ((b c : ℕ) + 1) (Pi.single c (1 : K)) := by
  intro i hi
  have : i ≠ c := by rintro rfl; omega
  simp [Pi.single_apply, this]

theorem mulVec_single_apply (z : Matrix (Fin n) (Fin n) K) (i c : Fin n) :
    (z *ᵥ Pi.single c (1 : K)) i = z i c := by
  simp [Matrix.mulVec_single_one]

theorem stab_iff (b : Fin n → Fin m) (z : Matrix (Fin n) (Fin n) K) :
    (∀ j : Fin (m + 1), ∀ w, lowVec b j w → lowVec b j (z *ᵥ w)) ↔
      ∀ i c, b c < b i → z i c = 0 := by
  constructor
  · intro H i c hic
    have h1 := H ⟨(b c : ℕ) + 1, by omega⟩ _ (lowVec_single b c) i (by simp; exact hic)
    rwa [mulVec_single_apply] at h1
  · intro H j w hw i hi
    simp only [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : (j : ℕ) ≤ (b c : ℕ)
    · rw [hw c hc, mul_zero]
    · rw [H i c (by rw [Fin.lt_iff_val_lt_val]; omega), zero_mul]

theorem rad_iff (b : Fin n → Fin m) (z : Matrix (Fin n) (Fin n) K) :
    (∀ j : Fin m, ∀ w, lowVec b (j.succ : ℕ) w → lowVec b (j.castSucc : ℕ) (z *ᵥ w - w)) ↔
      ∀ i c, ¬ b i < b c → z i c = (1 : Matrix (Fin n) (Fin n) K) i c := by
  constructor
  · intro H i c hic
    have h1 := H (b c) _ (by simpa using lowVec_single (K := K) b c) i
      (by simp; exact (not_lt.1 hic))
    rw [Pi.sub_apply, mulVec_single_apply, sub_eq_zero] at h1
    rw [h1, Pi.single_apply, one_apply]
  · intro H j w hw i hi
    have e : z *ᵥ w - w = (z - 1) *ᵥ w := by rw [sub_mulVec, one_mulVec]
    rw [e]
    simp only [mulVec, dotProduct]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : (j : ℕ) + 1 ≤ (b c : ℕ)
    · rw [hw c (by simpa using hc), mul_zero]
    · simp only [Fin.coe_castSucc] at hi
      rw [Matrix.sub_apply, H i c (by rw [Fin.lt_iff_val_lt_val]; omega), sub_self, zero_mul]

theorem transport (Gm Gi X : Matrix (Fin n) (Fin n) K) (h1 : Gi * Gm = 1) (h2 : Gm * Gi = 1)
    (P : (Fin n → K) → Prop) (Q : (Fin n → K) → (Fin n → K) → Prop) :
    (∀ y, P (Gi *ᵥ y) → Q (Gi *ᵥ y) (Gi *ᵥ (X *ᵥ y))) ↔ ∀ w, P w → Q w ((Gi * X * Gm) *ᵥ w) := by
  constructor
  · intro H w hw
    have hw' : Gi *ᵥ (Gm *ᵥ w) = w := by rw [mulVec_mulVec, h1, one_mulVec]
    have := H (Gm *ᵥ w) (by rw [hw']; exact hw)
    rw [hw'] at this
    simpa [mulVec_mulVec, Matrix.mul_assoc] using this
  · intro H y hy
    have := H _ hy
    simpa [mulVec_mulVec, Matrix.mul_assoc, h2] using this

theorem stdChain_stab_rad : ∀ {K : Type} [Field K] {n m : ℕ} (Y : Fin (m + 1) → Submodule K (Fin n → K)) (d : Fin m → ℕ) (h : ∑ j, d j = n)
    (g : GL (Fin n) K), (∀ (j : Fin (m + 1)) (y : Fin n → K),
      y ∈ Y j ↔ ∀ i : Fin n, (j : ℕ) ≤ ((GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d h) i : Fin m) : ℕ) →
        (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y) i = 0) →
    (∀ x : GL (Fin n) K, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy g (GlobalTheory.SmGL.parab K (GlobalTheory.SmGL.stdBlocks d h)) ↔
        ∀ j, ∀ y ∈ Y j, (x : Matrix (Fin n) (Fin n) K) *ᵥ y ∈ Y j) ∧
    (∀ x : GL (Fin n) K, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy g (GlobalTheory.SmGL.unipRad K (GlobalTheory.SmGL.stdBlocks d h)) ↔
        ∀ j : Fin m, ∀ y ∈ Y j.succ, (x : Matrix (Fin n) (Fin n) K) *ᵥ y - y ∈ Y j.castSucc) := by
  intro K _ n m Y d h g hY
  set b := GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks d h) with hb
  have hGi : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hGm : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hz : ∀ x : GL (Fin n) K, (((g⁻¹ * x * g : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) =
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) *
        (g : Matrix (Fin n) (Fin n) K) := fun x => by simp only [Units.val_mul]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.mem_conjBy, GlobalTheory.SmGL.mem_parab, hz, ← stab_iff]
    refine forall_congr' fun j => ?_
    have := transport (g : Matrix (Fin n) (Fin n) K) ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      (x : Matrix (Fin n) (Fin n) K) hGi hGm (lowVec b j) (fun _ v => lowVec b j v)
    rw [← this]
    refine forall_congr' fun y => ?_
    rw [hY j y, hY j]
    rfl
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.mem_conjBy, GlobalTheory.RadRev.mem_unipRad_entries, hz, ← rad_iff]
    refine forall_congr' fun j => ?_
    have := transport (g : Matrix (Fin n) (Fin n) K) ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      (x : Matrix (Fin n) (Fin n) K) hGi hGm (lowVec b (j.succ : ℕ)) (fun w v => lowVec b (j.castSucc : ℕ) (v - w))
    rw [← this]
    refine forall_congr' fun y => ?_
    rw [hY j.succ y, hY j.castSucc, mulVec_sub]
    rfl

end GlobalTheory.StdChainStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesDisjointTwistPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.TwistPlaces

theorem typePlaces_disjoint_twistPlaces : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ t : T, Disjoint R.Pg (R.Q t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t
  have hL := hC.lev
  rw [Finset.disjoint_left]
  intro PP hPg hQ
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPg
  obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t PP hQ
  have hmemK : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.under (𝓞 D.host.K)).asIdeal := by
    have h := R.C.P.pb_over k
    have hk' : PP.under (𝓞 D.host.K) = R.C.P.pb k := hk
    rw [hk']; exact h
  have hmemE : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := hmemK
    simpa using h2
  haveI : Finite (kP PP) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
  have : PP.asIdeal.IsPrime := PP.isPrime
  haveI : Nontrivial (kP PP) := inferInstance
  haveI : Fintype (kP PP) := Fintype.ofFinite _
  have h0g : ((D.host.g k : ℕ) : kP PP) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem (I := PP.asIdeal)).2 hmemE
    simpa using this
  have h0q : ((q : ℕ) : kP PP) = 0 := by
    rw [← hcard, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero (kP PP)
  have hd1 : ringChar (kP PP) ∣ D.host.g k := ringChar.dvd h0g
  have hd2 : ringChar (kP PP) ∣ q := ringChar.dvd h0q
  have hcop : Nat.Coprime q (D.host.g k) := (Nat.coprime_primes hq (D.host.g_prime k)).2 (hne k)
  have h1 : ringChar (kP PP) = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hd1
  exact CharP.ringChar_ne_one h1

end GlobalTheory.TwistPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepSchrodingerModelHalfSubstitutionStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_schrodingerModel_half_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (a : AE D) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → a * a = a → infPart D a = 0 → IsThetaFunO ψ S T f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → ∀ (g : GA D S) (h : GA D T) (c : ℂ), (∀ u, u ∈ (latO S T ΛS ΛT fun _ => True) ↔ actO S T g h u ∈ (latO S T ΛS ΛT fun _ => True)) → om (g, h) f₀ = c • f₀ → ∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → om (g, h) (Tm Φ) = c • Tm fun x => Φ (actO S T g⁻¹ h⁻¹ x) := by
  first | exact @GlobalTheory.SchrodSubst.om_placeModel | exact GlobalTheory.SchrodSubst.om_placeModel | (intros; apply GlobalTheory.SchrodSubst.om_placeModel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepThetaDatumHalfEqSmulStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_theta_datum_half_eq_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ), (∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm → ∀ Ψ, IsSBHalf e Λ Ψ → IsThetaFunO ψ S T (Tm Ψ)) → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → ∀ (g : GA D S) (h : GA D T), (∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) → ∀ c c' : ℂ, c ≠ 0 → om (g, h) f₀ = c • f₀ → (∀ x, Φ (actO S T g⁻¹ h⁻¹ x) = c' * Φ x) → om (g, h) f = (c * c') • f := by
  first | exact @GlobalTheory.ThetaMove.om_theta_eq_smul | exact GlobalTheory.ThetaMove.om_theta_eq_smul | (intros; apply GlobalTheory.ThetaMove.om_theta_eq_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicGroupNormalizesFlagUnipotent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixPer

theorem witt_anisotropic_group_normalizes_flag_unipotent : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∀ n ∈ flagN d, ∀ h : GA D S₀,
    d.emb0 h * n * (d.emb0 h)⁻¹ ∈ flagN d := by
  intro D S S₀ ρ d n hn h
  have he : Formalism.L2.Theta.mt S (d.emb0 h) ⬝ d.e.map (incA D) = d.e.map (incA D) := d.wittDecomp_anisotropicEmbedding_inclX h
  have he' := GlobalTheory.BesselChar.inv_fix_cols (GlobalTheory.BesselChar.mt_inv_mul S (d.emb0 h)) he
  unfold flagN at hn ⊢
  rw [GlobalTheory.BesselChar.mem_NFlag_iff S d.e (isIsoSub_e d).1] at hn ⊢
  rw [GlobalTheory.BesselChar.mt_mul, GlobalTheory.BesselChar.mt_mul]
  exact hn.conj he he' (GlobalTheory.BesselChar.mt_mul_inv S _) (GlobalTheory.BesselChar.perp_fixed d.e _ he')

end GlobalTheory.MixPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicProjectionUnitaryInvEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JacProj

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem coords {m : ℕ} (v : Mx D S.rank m) :
    v = d.jX ⬝ (d.pX ⬝ v) + d.j0 ⬝ (d.p0 ⬝ v) + d.jY ⬝ (d.pY ⬝ v) := by
  conv_lhs => rw [← Matrix.one_mul v, ← d.sum_eq_one]
  simp only [Matrix.add_mul, Matrix.mul_assoc]

theorem pY_inv (g : GA D S) : d.pY ⬝ mt S g⁻¹ = adj (mt S g ⬝ d.jX) ⬝ gA S := by
  rw [mt_inv, d.pY_eq, adj_mul]
  simp only [Matrix.mul_assoc, gA_giA_cancel]

theorem witt_anisotropic_projection_unitary_inv_eq (g : GA D S) : d.p0 ⬝ mt S g⁻¹ = giA S₀ ⬝ (adj (mt S g ⬝ d.j0) ⬝ gA S) := by
  rw [mt_inv, d.p0_eq, adj_mul]
  simp only [Matrix.mul_assoc, gA_giA_cancel]

def Keeps (g : GA D S) : Prop :=
  d.p0 ⬝ (mt S g ⬝ d.jX) = 0 ∧ d.pY ⬝ (mt S g ⬝ d.jX) = 0 ∧ d.pY ⬝ (mt S g ⬝ d.j0) = 0

theorem expand {k m : ℕ} (Q : Mx D k S.rank) (A B : Mx D S.rank S.rank) (v : Mx D S.rank m) :
    Q ⬝ ((A * B) ⬝ v) = Q ⬝ (A ⬝ d.jX) ⬝ (d.pX ⬝ (B ⬝ v)) + Q ⬝ (A ⬝ d.j0) ⬝ (d.p0 ⬝ (B ⬝ v)) +
      Q ⬝ (A ⬝ d.jY) ⬝ (d.pY ⬝ (B ⬝ v)) := by
  conv_lhs => rw [← Matrix.mul_one A, ← d.sum_eq_one]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem keeps_jX {g : GA D S} (h : Keeps d g) : mt S g ⬝ d.jX = d.jX ⬝ (d.pX ⬝ (mt S g ⬝ d.jX)) := by
  have e := coords d (mt S g ⬝ d.jX)
  rw [h.1, h.2.1] at e
  simpa only [Matrix.mul_zero, add_zero] using e

theorem preserves_flag_anisotropic_action {g : GA D S} (h : Keeps d g) :
    mt S g ⬝ d.j0 = d.jX ⬝ (d.pX ⬝ (mt S g ⬝ d.j0)) + d.j0 ⬝ (d.p0 ⬝ (mt S g ⬝ d.j0)) := by
  have e := coords d (mt S g ⬝ d.j0)
  rw [h.2.2] at e
  simpa only [Matrix.mul_zero, add_zero] using e

theorem keeps_unitary {g : GA D S} (h : Keeps d g) :
    adj (d.p0 ⬝ (mt S g ⬝ d.j0)) ⬝ (gA S₀ ⬝ (d.p0 ⬝ (mt S g ⬝ d.j0))) = gA S₀ := by
  have hXX : ∀ {k : ℕ} (M : Mx D ρ k), adj d.jX ⬝ (gA S ⬝ (d.jX ⬝ M)) = 0 := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.gram_XX, Matrix.zero_mul]
  have hX0 : ∀ {k : ℕ} (M : Mx D S₀.rank k), adj d.jX ⬝ (gA S ⬝ (d.j0 ⬝ M)) = 0 := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.wittDecomp_gram_X_anisotropic, Matrix.zero_mul]
  have h0X : ∀ {k : ℕ} (M : Mx D ρ k), adj d.j0 ⬝ (gA S ⬝ (d.jX ⬝ M)) = 0 := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.gram_0X, Matrix.zero_mul]
  have h00 : ∀ {k : ℕ} (M : Mx D S₀.rank k), adj d.j0 ⬝ (gA S ⬝ (d.j0 ⬝ M)) = gA S₀ ⬝ M := fun M => by
    rw [← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc, d.gram_00]
  have hu : adj (mt S g ⬝ d.j0) ⬝ (gA S ⬝ (mt S g ⬝ d.j0)) = gA S₀ := by
    calc adj (mt S g ⬝ d.j0) ⬝ (gA S ⬝ (mt S g ⬝ d.j0))
        = adj d.j0 ⬝ ((adj (mt S g) * (gA S * mt S g)) ⬝ d.j0) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = gA S₀ := by rw [mt_unitary, d.gram_00]
  rw [preserves_flag_anisotropic_action d h] at hu
  generalize d.pX ⬝ (mt S g ⬝ d.j0) = P at hu
  generalize d.p0 ⬝ (mt S g ⬝ d.j0) = C at hu ⊢
  simpa only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hXX, hX0, h0X, h00,
    Matrix.mul_zero, zero_add, add_zero] using hu

theorem keeps_mul {g g' : GA D S} (h : Keeps d g) (h' : Keeps d g') : Keeps d (g * g') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mt_mul, expand, h.1, h'.1, h'.2.1]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  · rw [mt_mul, expand, h.2.1, h'.1, h'.2.1]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  · rw [mt_mul, expand, h.2.1, h.2.2, h'.2.2]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem keeps_inv {g : GA D S} (h : Keeps d g) : Keeps d g⁻¹ := by
  obtain ⟨P, hP⟩ : ∃ P : Mx D ρ ρ, mt S g ⬝ d.jX = d.jX ⬝ P := ⟨_, keeps_jX d h⟩
  obtain ⟨P', C, hC⟩ : ∃ (P' : Mx D ρ S₀.rank) (C : Mx D S₀.rank S₀.rank), mt S g ⬝ d.j0 = d.jX ⬝ P' + d.j0 ⬝ C := ⟨_, _, preserves_flag_anisotropic_action d h⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, witt_anisotropic_projection_unitary_inv_eq, hC]
    simp only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, d.gram_XX, d.gram_0X,
      Matrix.mul_zero, add_zero]
  · rw [← Matrix.mul_assoc, pY_inv, hP]
    simp only [adj_mul, Matrix.mul_assoc, d.gram_XX, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, pY_inv, hP]
    simp only [adj_mul, Matrix.mul_assoc, d.wittDecomp_gram_X_anisotropic, Matrix.mul_zero]

theorem preserves_flag_anisotropic_block_one_inv {g : GA D S} (h : Keeps d g) (h1 : d.p0 ⬝ (mt S g ⬝ d.j0) = 1) : d.p0 ⬝ (mt S g⁻¹ ⬝ d.j0) = 1 := by
  have e := preserves_flag_anisotropic_action d h
  rw [h1, Matrix.mul_one] at e
  obtain ⟨P, hP⟩ : ∃ P : Mx D ρ S₀.rank, mt S g ⬝ d.j0 = d.jX ⬝ P + d.j0 := ⟨_, e⟩
  rw [← Matrix.mul_assoc, witt_anisotropic_projection_unitary_inv_eq, hP]
  simp only [adj_add, adj_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, d.wittDecomp_gram_X_anisotropic, d.gram_00,
    Matrix.mul_zero, zero_add]
  exact giA_mul_gA S₀

theorem keeps_one : Keeps d 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [mt_one, Matrix.one_mul]
  · exact d.p0_jX
  · exact d.pY_jX
  · exact d.pY_j0

def keepSub : Subgroup (GA D S) where
  carrier := {g | Keeps d g}
  one_mem' := keeps_one d
  mul_mem' := keeps_mul d
  inv_mem' := keeps_inv d

def keepSub1 : Subgroup (GA D S) where
  carrier := {g | Keeps d g ∧ d.p0 ⬝ (mt S g ⬝ d.j0) = 1}
  one_mem' := ⟨keeps_one d, by rw [mt_one, Matrix.one_mul, HypDec.p0_j0]⟩
  mul_mem' := fun {a b} ha hb => ⟨keeps_mul d ha.1 hb.1, by
    rw [mt_mul, expand, ha.1.1, ha.2, hb.1.2.2, hb.2]
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Matrix.one_mul]⟩
  inv_mem' := fun {a} ha => ⟨keeps_inv d ha.1, preserves_flag_anisotropic_block_one_inv d ha.1 ha.2⟩

theorem flag_le : flagN d ≤ keepSub1 d := by
  intro n hn
  obtain ⟨T, b, -, hX, h0⟩ := exists_blocks d hn
  have eX : ∀ {k : ℕ} (Q : Mx D k S.rank), Q ⬝ (mt S n ⬝ d.jX) = Q ⬝ d.jX + Q ⬝ d.jX ⬝ T := fun Q => by
    rw [hX, Matrix.mul_add, Matrix.mul_assoc]
  have e0 : ∀ {k : ℕ} (Q : Mx D k S.rank), Q ⬝ (mt S n ⬝ d.j0) = Q ⬝ d.j0 + Q ⬝ d.jX ⬝ b := fun Q => by
    rw [h0, Matrix.mul_add, Matrix.mul_assoc]
  show (_ ∧ _ ∧ _) ∧ _
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [eX, d.p0_jX, Matrix.zero_mul, add_zero]
  · rw [eX, d.pY_jX, Matrix.zero_mul, add_zero]
  · rw [e0, d.pY_j0, d.pY_jX, Matrix.zero_mul, add_zero]
  · rw [e0, d.p0_j0, d.p0_jX, Matrix.zero_mul, add_zero]

theorem range_le : d.emb0.range ≤ keepSub d := by
  rintro _ ⟨h, rfl⟩
  show _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [d.wittDecomp_anisotropicEmbedding_inclX, d.p0_jX]
  · rw [d.wittDecomp_anisotropicEmbedding_inclX, d.pY_jX]
  · rw [d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, d.pY_j0, Matrix.zero_mul]

theorem jac_le : (flagN d ⊔ d.emb0.range : Subgroup (GA D S)) ≤ keepSub d :=
  sup_le (fun _ hg => (flag_le d hg).1) (range_le d)

theorem witt_anisotropic_block_flag_mul_embedded {n : GA D S} (hn : n ∈ flagN d) (h : GA D S₀) :
    d.p0 ⬝ (mt S (n * d.emb0 h) ⬝ d.j0) = mt S₀ h := by
  have h1 : d.p0 ⬝ (mt S n ⬝ d.j0) = 1 := (flag_le d hn).2
  rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc (mt S n), ← Matrix.mul_assoc d.p0, h1,
    Matrix.one_mul]

def proj (g : (flagN d ⊔ d.emb0.range : Subgroup (GA D S))) : GA D S₀ :=
  ofMat S₀ (d.p0 ⬝ (mt S g.1 ⬝ d.j0)) (keeps_unitary d (jac_le d g.2))

theorem continuous_proj : Continuous (proj d) := by
  apply continuous_of_mt
  simp only [proj, mt_ofMat]
  exact continuous_const.matrix_mul (((continuous_mt S).comp continuous_subtype_val).matrix_mul continuous_const)

theorem proj_mul (h : GA D S₀) (n : flagN d) :
    proj d ⟨n.1 * d.emb0 h, mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h := by
  apply mt_injective S₀
  simp only [proj, mt_ofMat]
  exact witt_anisotropic_block_flag_mul_embedded d n.2 h

theorem exists_continuous_proj : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ),
    ∃ p : (flagN d ⊔ d.emb0.range : Subgroup (GA D S)) → GA D S₀, Continuous p ∧
      ∀ (h : GA D S₀) (n : flagN d),
        p ⟨n.1 * d.emb0 h, mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)⟩ = h := by
  intro D S S₀ ρ d
  exact ⟨proj d, continuous_proj d, proj_mul d⟩

end GlobalTheory.JacProj
end
end

