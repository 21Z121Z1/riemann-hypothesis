import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasProdQuadExtLocalEulerFactorInvInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharValuesInNumberField
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0328
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1015
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0119
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1003
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HvMemOfInert
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.EtaValues

section General

variable {L : Type} [Field L] [NumberField L]

def hv (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : ℂ :=
  ((χ.val v : ℂˣ) : ℂ) * (((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ))⁻¹ : ℝ) : ℂ)

theorem absNorm_pos (v : HeightOneSpectrum (𝓞 L)) : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 v.ne_bot)

theorem hv_ne_zero (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : hv χ v ≠ 0 :=
  mul_ne_zero (Units.ne_zero _) (Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 (absNorm_pos v)).ne'))

theorem valTw_eq (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : χ.valTw (1 / 2) v = hv χ v := by
  unfold HChar.valTw hv
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg _), Complex.ofReal_cpow (Nat.cast_nonneg _),
    Complex.ofReal_natCast, Complex.ofReal_neg]

open Classical in

def cnt (a : 𝓞 L) (v : HeightOneSpectrum (𝓞 L)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a} : Ideal (𝓞 L))).factors

theorem intValuation_eq {a : 𝓞 L} (ha : a ≠ 0) (v : HeightOneSpectrum (𝓞 L)) :
    v.intValuation a = WithZero.exp (-(cnt a v : ℤ)) := by
  rw [HeightOneSpectrum.intValuation_if_neg _ ha]
  rfl

theorem ordF_eq {a : 𝓞 L} (ha : a ≠ 0) (v : HeightOneSpectrum (𝓞 L)) : ordF v (GlobalTheory.Mem.ValAlg.uOf a ha) = cnt a v := by
  show -WithZero.log (v.valuation L (algebraMap (𝓞 L) L a)) = _
  rw [HeightOneSpectrum.valuation_of_algebraMap, intValuation_eq ha]
  simp

theorem cnt_eq_zero {a : 𝓞 L} (ha : a ≠ 0) {v : HeightOneSpectrum (𝓞 L)} (h : a ∉ v.asIdeal) : cnt a v = 0 := by
  have h1 := intValuation_eq ha v
  rw [HeightOneSpectrum.intValuation_eq_one_iff.2 h, ← WithZero.exp_zero, WithZero.exp_inj] at h1
  omega

theorem prod_hv (hL : IsTotallyComplex L) {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar L) (hu : ∀ v, χ.UnrAt v)
    (hinf : χ.HasInf φ fun _ => 1) {a : 𝓞 L} (ha : a ≠ 0) (U : Finset (HeightOneSpectrum (𝓞 L)))
    (hU : ∀ v, a ∈ v.asIdeal → v ∈ U) :
    ∏ v ∈ U, hv χ v ^ cnt a v = (∏ i, φ i (algebraMap (𝓞 L) L a))⁻¹ := by
  classical
  have h0 : ∀ v, v ∉ U → cnt a v = 0 := fun v h => cnt_eq_zero ha (mt (hU v) h)
  have hp := GlobalTheory.TypeValues.productRule χ ∅ (fun v _ => hu v) (GlobalTheory.Mem.ValAlg.uOf a ha)
  have e1 : ∀ v, (∏ᶠ (_ : v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 L)))), χ.val v ^ ordF v (GlobalTheory.Mem.ValAlg.uOf a ha)) =
      χ.val v ^ cnt a v := fun v => by
    rw [finprod_eq_if, if_pos (Finset.notMem_empty v), ordF_eq, zpow_natCast]
  simp_rw [e1] at hp
  rw [Finset.prod_empty, mul_one, finprod_eq_prod_of_mulSupport_subset (s := U) _ (fun v hv' => by
    by_contra h
    exact hv' (by simp only [h0 v h, pow_zero]))] at hp
  have hp' := congrArg (Units.val : ℂˣ → ℂ) hp
  rw [Units.val_mul, hinf, Units.val_one, Units.coe_prod] at hp'
  have hf := Ideal.finprod_heightOneSpectrum_factorization (I := Ideal.span {a}) (by simpa using ha)
  rw [finprod_eq_prod_of_mulSupport_subset (s := U) _ (fun v hv' => by
    by_contra h
    refine hv' ?_
    show v.asIdeal ^ cnt a v = 1
    rw [h0 v h, pow_zero])] at hf
  have hN := GlobalTheory.Mem.ValAlg.absNorm_eq hL φ hφ a
  rw [← hf, map_prod, Nat.cast_prod] at hN
  have hN' : ∏ v ∈ U, Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) ^ cnt a v = ∏ i, ‖φ i (algebraMap (𝓞 L) L a)‖ := by
    refine (pow_left_inj₀ (Finset.prod_nonneg fun _ _ => by positivity) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      two_ne_zero).1 ?_
    rw [← hN, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
    show _ = ((Ideal.absNorm (v.asIdeal ^ cnt a v) : ℕ) : ℝ)
    rw [map_pow, Nat.cast_pow]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← hp']
  unfold hv
  simp_rw [mul_pow, Finset.prod_mul_distrib, zpow_one, Finset.prod_div_distrib, Units.val_pow_eq_pow_val,
    ← Complex.ofReal_pow, ← Complex.ofReal_prod, inv_pow, Finset.prod_inv_distrib, hN', Complex.ofReal_inv]
  show _ = (∏ i, φ i (algebraMap (𝓞 L) L a)) / ((∏ i, ‖φ i (algebraMap (𝓞 L) L a)‖ : ℝ) : ℂ) * _
  ring

theorem hv_mem (hL : IsTotallyComplex L) {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar L) (hu : ∀ v, χ.UnrAt v)
    (hinf : χ.HasInf φ fun _ => 1) (M : Subfield ℂ) (hM : ∀ i x, φ i x ∈ M) (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ v, v ∉ S → hv χ v ∈ M) (P : HeightOneSpectrum (𝓞 L)) : hv χ P ∈ M := by
  classical
  by_cases hP : P ∈ S
  swap
  · exact hS P hP
  obtain ⟨b, hb1, hb2⟩ : ∃ b ∈ P.asIdeal, b ∉ P.asIdeal ^ 2 := by
    have := Ideal.pow_succ_lt_pow P.ne_bot 1 (P := P.asIdeal)
    rw [pow_one] at this
    exact SetLike.exists_of_lt this
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) (fun _ => 2)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => if v.1 = P then b else 1)
  have haP := ha P hP
  rw [if_pos rfl] at haP
  have ha2 : a ∉ P.asIdeal ^ 2 := fun h => hb2 (by simpa using (P.asIdeal ^ 2).sub_mem h haP)
  have ha1 : a ∈ P.asIdeal := by simpa using P.asIdeal.add_mem (Ideal.pow_le_self two_ne_zero haP) hb1
  have ha0 : a ≠ 0 := by rintro rfl; exact ha2 (zero_mem _)
  have hc : cnt a P = 1 := by
    have h1 := intValuation_eq ha0 P
    rw [GlobalTheory.TypeValues.intValuation_eq_of_mem ha1 ha2, WithZero.exp_inj] at h1
    omega
  have hfin : {v : HeightOneSpectrum (𝓞 L) | v.asIdeal ∣ Ideal.span {a}}.Finite :=
    Ideal.finite_factors (by simpa using ha0)
  have hU : ∀ v, a ∈ v.asIdeal ↔ v ∈ hfin.toFinset := fun v => by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  have h := prod_hv hL φ hφ χ hu hinf ha0 hfin.toFinset fun v => (hU v).1
  rw [← Finset.mul_prod_erase _ _ ((hU P).1 ha1), hc, pow_one] at h
  rw [eq_div_of_mul_eq (Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hv_ne_zero χ v)) h]
  refine div_mem (inv_mem (prod_mem fun i _ => hM i _)) (prod_mem fun v hv' => pow_mem (hS v fun hvS => ?_) _)
  obtain ⟨hvP, hva⟩ := Finset.mem_erase.1 hv'
  have h1 := ha v hvS
  rw [if_neg hvP] at h1
  refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  simpa using v.asIdeal.sub_mem ((hU v).2 hva) (Ideal.pow_le_self two_ne_zero h1)

theorem hv_mem_of_inert {F : Type} [Field F] [NumberField F] [Algebra F L] (χ : HChar L) (hr : χ.ResEta F)
    {v : HeightOneSpectrum (𝓞 L)} (hu : χ.UnrAt v) (ho : ∀ k : Fˣ, ordF v (upF F k) = ordF (v.under (𝓞 F)) k)
    (h1 : ((v.under (𝓞 F)).asIdeal.primesOver (𝓞 L)).ncard = 1)
    (hN : Ideal.absNorm v.asIdeal = Ideal.absNorm (v.under (𝓞 F)).asIdeal ^ 2) (M : Subfield ℂ) : hv χ v ∈ M := by
  have hab : aboveF (L := L) F (v.under (𝓞 F)) = {v} := by
    obtain ⟨Q, hQ⟩ := Set.ncard_eq_one.1 h1
    have key : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v.under (𝓞 F) → w.asIdeal = Q := fun w hw => by
      have : w.asIdeal ∈ (v.under (𝓞 F)).asIdeal.primesOver (𝓞 L) := ⟨w.isPrime, ⟨by rw [← hw]; rfl⟩⟩
      rwa [hQ] at this
    ext P
    rw [aboveF, Set.Finite.mem_toFinset, Finset.mem_singleton]
    exact ⟨fun h => HeightOneSpectrum.ext ((key P h).trans (key v rfl).symm), fun h => by rw [h]; rfl⟩
  have hval : ∀ {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (k : Kˣ),
      IsUnifAt w (atFin w k) ↔ ordF w k = 1 := by
    intro K _ _ w k
    have h : Valued.v ((atFin w k : (w.adicCompletion K)ˣ) : w.adicCompletion K) = w.valuation K (k : K) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (k : K)
    have h0 : w.valuation K (k : K) ≠ 0 := (Valuation.ne_zero_iff _).2 k.ne_zero
    unfold IsUnifAt ordF
    rw [h, ← WithZero.exp_log h0, WithZero.exp_inj, WithZero.log_exp]
    omega
  have hk := (hval _ _).1 (unif_spec (v.under (𝓞 F)))
  have h := hr.1 (v.under (𝓞 F)) (unif (v.under (𝓞 F)))
  rw [HChar.resFin, etaFin, hab, Finset.prod_singleton, MonoidHom.comp_apply, if_pos (Finset.card_singleton _), hk, zpow_one] at h
  have h2 : χ.val v = -1 := (χ.val_eq hu _ ((hval _ _).2 ((ho _).trans hk))).symm.trans h
  unfold hv
  rw [h2, hN, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _), Complex.ofReal_inv, Complex.ofReal_natCast, Units.val_neg,
    Units.val_one]
  exact mul_mem (neg_mem (one_mem _)) (inv_mem (natCast_mem _ _))

end General

end GlobalTheory.EtaValues

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.EtaValues

open Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hv_mem_host (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (hχ : Formalism.L2.Host.IsEtaT D.host χ) (T : Finset (Pl D.host.E))
    (hT : ∀ v, Bridge.SplitOff v (T : Set (Pl D.host.E)) → hv χ v ∈ D.what₂.embLL.fieldRange) (P : Pl D.host.E) :
    hv χ P ∈ D.what₂.embLL.fieldRange := by
  classical
  obtain ⟨c, -, hcm, ho, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  refine hv_mem hcm.cplx _ hcm.bij χ hχ.unr hχ.inf D.what₂.embLL.fieldRange (fun g x => ⟨D.embE (D.host.sigmaOf g x),
    DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf g x)⟩) (T ∪ T.image conjPrime₂) (fun v hv' => ?_) P
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) v.asIdeal = v.asIdeal
  · have hm : v.asIdeal ∈ (v.under (𝓞 D.host.F)).asIdeal.primesOver (𝓞 D.host.E) := ⟨v.isPrime, ⟨rfl⟩⟩
    rcases GlobalTheory.EtaEulerProduct.inert_or_split (σ := D.sp.cm.sig)
      ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, fun τ x => D.sp.cm.cmUnram.2.1 τ x⟩ (fun _ => rfl)
      D.sp.cm.cmUnram (v.under (𝓞 D.host.F)) with ⟨-, h1, h2⟩ | ⟨-, -, h2⟩
    · exact hv_mem_of_inert χ hχ.res (hχ.unr v) (ho v) h1 (h2 _ hm).2 _
    · exact absurd hc (h2 _ hm).1
  · exact hT v ⟨hc, fun h => hv' (Finset.mem_union_left _ h), fun w hw h => hv' (Finset.mem_union_right _ (Finset.mem_image.2
      ⟨w, hw, by rw [show w = conjPrime₂ v from HeightOneSpectrum.ext (h.trans (conjIdeal_asIdeal v)),
        GlobalTheory.RationalValues.conjP_conjP]⟩))⟩

theorem splitOff_mono {D : D7} {v : Pl D.host.E} {S S' : Set (Pl D.host.E)} (h : Bridge.SplitOff v S) (hS : S' ⊆ S) :
    Bridge.SplitOff v S' :=
  ⟨h.1, fun h' => h.2.1 (hS h'), fun w hw => h.2.2 w (hS hw)⟩

theorem etaVals : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m), EtaVals R := by
  classical
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR _ P e he x hx
  have htie := hR.fam.tie
  obtain ⟨_, _, _, hT⟩ := htie
  have hok := hT.ok A.μ0
  have h := hv_mem_host D R.C.eta R.C.isEta (R.Sb ∪ R.Q A.μ0) (fun v hs => by
    rw [Finset.coe_union] at hs
    obtain ⟨Q, rfl⟩ := hR.fam.pl_onto v (splitOff_mono hs Set.subset_union_left)
    exact ⟨_, (hR.fam.etaVal Q ((hok Q).2 hs)).trans (valTw_eq _ _)⟩) P
  obtain ⟨y, hy⟩ := h
  refine ⟨y, hy.trans ?_⟩
  rw [hR.lev.eta.2 P e he _ x hx]
  rfl

end GlobalTheory.EtaValues

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentSupportHermitianDecomposition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FunObj.StdReps

section General

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_nat_smul_mem (L L' : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG)
    (hsp : Submodule.span E (L' : Set (Fin n → E)) = ⊤) :
    ∃ c : ℕ, 0 < c ∧ ∀ x ∈ L, (c : E) • x ∈ L' := by
  first
  | exact @_root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le
  | exact _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le
  | (apply _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMultipleIntegralSmulBound.exists_nat_smul_le ..)

theorem fg_colLat (B : GL (Fin n) E) : (colLat B).FG :=
  Submodule.fg_span (Set.finite_range _)

theorem span_colLat (B : GL (Fin n) E) : Submodule.span E (colLat B : Set (Fin n → E)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ j, ((B⁻¹).1 *ᵥ x) j • (fun a : Fin n => (B : Matrix (Fin n) (Fin n) E) a j) := by
    have e : x = B.1 *ᵥ ((B⁻¹).1 *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    conv_lhs => rw [e]
    funext a
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hx]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact Submodule.subset_span ⟨j, rfl⟩

end General

variable {D : D7}

def stabGL {R : Type} [CommRing R] {m : ℕ} (H : Set (Fin m → R)) : Subgroup (GL (Fin m) R) where
  carrier := {g | ∀ v, v ∈ H ↔ g.1 *ᵥ v ∈ H}
  one_mem' := fun v => by rw [Units.val_one, Matrix.one_mulVec]
  mul_mem' := fun {a b} ha hb v => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hb v).trans (ha _)
  inv_mem' := fun {a} ha v => by
    have := ha ((a⁻¹).1 *ᵥ v)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
    exact this.symm

def stabG (V : HSp D) (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Subgroup (GA D V) :=
  (stabGL (Formalism.L2.Herm.hatL (F := D.host.F) M : Set (Fin V.rank → Formalism.IndefR.Lev.EAf D))).comap (Formalism.IndefR.Lev.finE V)

set_option maxHeartbeats 1000000 in

theorem mulVec_mem_of_finCong (V : HSp D) (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (c : ℕ) (hc : 0 < c)
    (h1 : ∀ x ∈ M, (c : D.host.E) • x ∈ GlobalTheory.Member.latC V)
    (h2 : ∀ x ∈ GlobalTheory.Member.latC V, (c : D.host.E) • x ∈ M) (a : GA D V) (ha : GlobalTheory.Member.FinCong V (c * c) a) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) M,
      (Formalism.IndefR.Lev.finE V a).1 *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) M := by
  have hl := (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  have hcong : ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.Member.latC V),
      ∃ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.Member.latC V),
        (Formalism.IndefR.Lev.finE V a).1 *ᵥ z - z = (c * c) • y := by
    unfold GlobalTheory.Member.FinCong at ha
    rw [hl] at ha
    exact GlobalTheory.PrincInLevel.cong_swap _ _ _ ha
  intro z hz
  obtain ⟨y, hy, e⟩ := hcong _ (GlobalTheory.LevSplit.hatL_smul _ _ c h1 z hz)
  have hcE : IsUnit (c : D.host.E) := (Nat.cast_ne_zero.2 hc.ne').isUnit
  have hu : IsUnit (c : Formalism.IndefR.Lev.EAf D) := by
    have := hcE.map (eToEAf D)
    rwa [map_natCast] at this
  have e2 : (Formalism.IndefR.Lev.finE V a).1 *ᵥ z - z = (c : Formalism.IndefR.Lev.EAf D) • y := by
    refine (hu.smul_left_cancel).1 ?_
    rw [smul_sub, ← Matrix.mulVec_smul, e, ← Nat.cast_smul_eq_nsmul (Formalism.IndefR.Lev.EAf D), Nat.cast_mul, mul_smul]
  rw [sub_eq_iff_eq_add'] at e2
  rw [e2]
  exact Submodule.add_mem _ hz (GlobalTheory.LevSplit.hatL_smul _ _ c h2 y hy)

set_option maxHeartbeats 1000000 in

theorem mem_stabG_of_finCong (V : HSp D) (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (c : ℕ) (hc : 0 < c)
    (h1 : ∀ x ∈ M, (c : D.host.E) • x ∈ GlobalTheory.Member.latC V)
    (h2 : ∀ x ∈ GlobalTheory.Member.latC V, (c : D.host.E) • x ∈ M) (a : GA D V) (ha : GlobalTheory.Member.FinCong V (c * c) a) :
    a ∈ stabG V M := by
  intro v
  refine ⟨mulVec_mem_of_finCong V M c hc h1 h2 a ha v, fun hv => ?_⟩
  have := mulVec_mem_of_finCong V M c hc h1 h2 a⁻¹ (GlobalTheory.Member.PrincLevel.finCong_inv ha) _ hv
  rwa [map_inv, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

set_option maxHeartbeats 4000000 in

theorem exists_rep_std : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (S : Finset ℕ), (∀ q ∈ S, q.Prime) →
    ∀ x : GA D V, x ∈ GfC V →
    ∃ (γ : GL (Fin V.rank) D.host.E) (h k : GA D V),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram ∧ h ∈ GfC V ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V h ∧ ∀ w ∈ P, Off S w) ∧
      k ∈ GfC V ∧ (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) ∧
      (Formalism.IndefR.Lev.finE V x).1 = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 * (Formalism.IndefR.Lev.finE V k).1 := by
  intro D V fr S hS x hx
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨c1, hc1, h1⟩ := exists_nat_smul_mem (colLat fr) (GlobalTheory.Member.latC V) (fg_colLat fr) hsp
  obtain ⟨c2, hc2, h2⟩ := exists_nat_smul_mem (GlobalTheory.Member.latC V) (colLat fr) hfg (span_colLat fr)
  have h1' : ∀ y ∈ colLat fr, ((c1 * c2 : ℕ) : D.host.E) • y ∈ GlobalTheory.Member.latC V := fun y hy => by
    rw [Nat.cast_mul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul D.host.E c2]
    exact (GlobalTheory.Member.latC V).toAddSubmonoid.nsmul_mem (h1 y hy) c2
  have h2' : ∀ y ∈ GlobalTheory.Member.latC V, ((c1 * c2 : ℕ) : D.host.E) • y ∈ colLat fr := fun y hy => by
    rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul D.host.E c1]
    exact (colLat fr).toAddSubmonoid.nsmul_mem (h2 y hy) c1
  have hc : 0 < c1 * c2 := Nat.mul_pos hc1 hc2
  let J' : Subgroup (Formalism.IndefR.Bridge.Gf V) := (GfC V ⊓ stabG V (colLat fr)).map (finHom V).rangeRestrict
  have hK : ∀ k ∈ GfC V, GlobalTheory.Member.FinCong V ((c1 * c2) * (c1 * c2)) k → Formalism.IndefR.FWT.fin V k ∈ J' :=
    fun k hk hck => ⟨k, ⟨hk, mem_stabG_of_finCong V (colLat fr) _ hc h1' h2' k hck⟩, rfl⟩
  have hbad : 0 < ∏ q ∈ S, q := Finset.prod_pos fun q hq => (hS q hq).pos
  obtain ⟨h, ⟨hh, hs⟩, γ, k, e⟩ :=
    GlobalTheory.SplitReps.exists_split_rep V (Nat.mul_pos hc hc) hK hbad (Formalism.IndefR.FWT.fin V x)
  obtain ⟨k0, ⟨hk0, hk0s⟩, hk0e⟩ := Subgroup.mem_map.1 k.2
  obtain ⟨-, e0, P, he0, hP, hsupp⟩ := GlobalTheory.SplitReps.splitOffBad_of_suppSplit V _ h hh hs
  obtain ⟨γE, hU, hγ⟩ := γ.2
  have hm : matHom V γ.1 = Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γE := hγ.symm
  have hfγ : finHom V γ.1 = Formalism.UG.bc (inclR (F := D.host.F) (Af D.host.F)) γE := by
    rw [finHom, MonoidHom.comp_apply, hm]
    exact GlobalTheory.HLatMove.bc_map_bc_inclR _ _
  have ef : finHom V x = finHom V γ.1 * finHom V h * finHom V k0 := by
    have := congrArg Subtype.val e
    rw [← hk0e] at this
    exact this
  refine ⟨γE, h, k0, hU, hh, ⟨P, e0, he0, hsupp, fun w hw q hq hqw => hP w hw ?_⟩, hk0, hk0s, ?_⟩
  · obtain ⟨m, hm'⟩ := Finset.dvd_prod_of_mem (fun q : ℕ => q) hq
    rw [hm', Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hqw
  · have eE : Formalism.IndefR.Lev.finE V x = Formalism.IndefR.Lev.finE V γ.1 * Formalism.IndefR.Lev.finE V h * Formalism.IndefR.Lev.finE V k0 := by
      simp only [Formalism.IndefR.Lev.finE, MonoidHom.comp_apply, ef, map_mul]
    have eγ : (Formalism.IndefR.Lev.finE V γ.1).1 = γE.1.map (eToEAf D) := by
      simp only [Formalism.IndefR.Lev.finE, MonoidHom.comp_apply, hfγ]
      ext i j
      rfl
    rw [eE, Units.val_mul, Units.val_mul, eγ]

end GlobalTheory.FunObj.StdReps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerConjFormsEqCsumAt
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLower

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K] {M W' ι : Type} [AddCommGroup M] [Module K M]
  [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [Fintype ι]

omit [NumberField K] in

theorem inner_coef_of_rat (b : Module.Basis ι K M) (σ : K →+* ℂ) (c₁ : M →ₛₗ[σ] W') (pr : M →ₗ⋆[K] M →ₗ[K] K)
    (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pr (b a) (b a'))) (u v : M) (hu : ∀ a, b.repr u a ∈ cmMax K) :
    inner ℂ (c₁ u) (c₁ v) = σ (pr u v) := by
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
  conv_rhs => rw [← b.sum_repr u, ← b.sum_repr v]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_mul,
    RingHom.id_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [starRingEnd_apply (b.repr u a'), hu a' σ]

theorem inner_eq_csumAt (S : CSD K) (hb : S.HasRatBasis) (b : Module.Basis ι K M) (σ : K →+* ℂ) (c₁ : M →ₛₗ[σ] W')
    (pr : M →ₗ⋆[K] M →ₗ[K] K) (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pr (b a) (b a')))
    (e : S.V ≃ₗ[K] M) (hr : ∀ i a, b.repr (e (S.bV i)) a ∈ cmMax K) (he : ∀ x x', pr (e x) (e x') = S.pair x x')
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : S.Forms →ₛₗ[σ] H)
    (hj : ∀ x y : S.Forms, inner ℂ (j x) (j y) =
      ∑ c, ((S.wt c : ℂ))⁻¹ * inner ℂ (c₁ (e ((x : S.Cl → S.V) c))) (c₁ (e ((y : S.Cl → S.V) c)))) (x y : S.Forms) :
    inner ℂ (j x) (j y) = csumAt S σ x y := by
  have hrat : ∀ k c a, b.repr (e ((S.basis k : S.Cl → S.V) c)) a ∈ cmMax K := by
    intro k c a
    rw [← S.bV.sum_repr ((S.basis k : S.Cl → S.V) c)]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (S.basis_rat hb k c i) (hr i a)
  have hH : ∀ k l, inner ℂ (j (S.basis k)) (j (S.basis l)) = σ (S.H k l) := by
    intro k l
    rw [hj]
    unfold CSD.H CSD.csum
    rw [Matrix.of_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [inner_coef_of_rat b σ c₁ pr hp _ _ (hrat k c), he, map_mul, map_inv₀, map_natCast]
  conv_lhs => rw [← S.basis.sum_repr x, ← S.basis.sum_repr y]
  unfold csumAt
  simp only [map_sum, LinearMap.map_smulₛₗ, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hH,
    dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [starRingEnd_apply]
  ring

theorem inner_eq_csumAt_of_pres {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ι₀ : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι₀ S σ₀ ρ J χ) (b : Module.Basis ι K M) (c₀ : M →ₛₗ[σ₀] W) (pr : M →ₗ⋆[K] M →ₗ[K] K)
    {Q : (S.V ≃ₗ[K] M) → Prop}
    (hP : ∃ e : S.V ≃ₗ[K] M, (∀ i a, b.repr (e (S.bV i)) a ∈ cmMax K) ∧ (∀ x, P.coef x = c₀ (e x)) ∧
      (∀ x x', pr (e x) (e x') = S.pair x x') ∧ Q e)
    (hb : S.HasRatBasis) (σ : K →+* ℂ) (c₁ : M →ₛₗ[σ] W')
    (hp : ∀ a a', inner ℂ (c₁ (b a)) (c₁ (b a')) = σ (pr (b a) (b a')))
    (H : HMod (G → W')) (j : S.Forms →ₛₗ[σ] H.H)
    (hH : ∀ x y : H.H, inner ℂ x y = Bridge.adInner ι₀ J P.y (H.e x) (H.e y))
    (hj : ∀ (x : S.Forms) h, ∃ v, P.ext (x : S.Cl → S.V) h = c₀ v ∧ H.e (j x) h = c₁ v) (x y : S.Forms) :
    inner ℂ (j x) (j y) = csumAt S σ x y := by
  obtain ⟨e, hr, he, hpair, -⟩ := hP
  have hval : ∀ (z : S.Forms) cl, H.e (j z) (P.y cl) = c₁ (e (z.1 cl)) := by
    intro z cl
    obtain ⟨v, h0, h1⟩ := hj z (P.y cl)
    have h3 : P.coef (z.1 cl) = P.coef (e.symm v) := by
      rw [← GlobalTheory.PresBasic.ext_y P z cl, h0, he, e.apply_symm_apply]
    rw [h1, GlobalTheory.PresBasic.coef_injective _ h3, e.apply_symm_apply]
  refine inner_eq_csumAt S hb _ σ c₁ _ hp e hr hpair j (fun z w => ?_) x y
  rw [hH]
  unfold Bridge.adInner
  refine Finset.sum_congr rfl fun cl _ => ?_
  rw [hval, hval, CSD.wt, ← Nat.card_eq_fintype_card, Nat.card_congr (P.stabI cl).toEquiv]

end Generic

theorem inner_conjForms_eq_csumAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_jV → ∀ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) c c₁ H j, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ (c0L i) c c₁ H j → ∀ x y, ⟪j x, j y⟫_ℂ = csumAt (A.MtCSD i A.μ0) σ x y := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hjV gramR c0R c0L hT i σ c c₁ H j hC x y
  have hb : (A.MtCSD i A.μ0).HasRatBasis :=
    (GlobalTheory.HeckeRational.dcOp_matrix_mem_cmMax (Vc D i) (R.cV i).coef (R.βV i) (R.datVt i A.μ0) (R.B.L i A.μ0).pres
      (hT.coefL i A.μ0) (hT.mapL i)
      (fun g a k => (coefAction_repr_mem_subfield (labLL D) _ _ GlobalTheory.HeckeRational.labLL_mem_cmMax g a k).2) {1} 1
      (fun f => by funext h; simp [Bridge.dcOp])).1
  have h1 := hC.model.choose_spec.2.2.2
  have h2 : ∀ (z : A.fam.amb.FL i A.μ0) h, ∃ v, (R.B.L i A.μ0).pres.ext z.1 h = c0L i v ∧ H.e (j z) h = c₁ v :=
    fun z h => (hC.base z h).imp fun v hv => ⟨(congrFun (hjV i A.μ0 z) h).symm.trans hv.1, hv.2⟩
  exact inner_eq_csumAt_of_pres (R.B.L i A.μ0).pres _ (c0L i) _ (hT.coefL i A.μ0) hb σ c₁ hC.pair H j h1 h2 x y

end GlobalTheory.LiftLower

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousAndHilbertPolyEqOfPrimeInSaturationStatement
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHomogeneous_and_hilbertPoly_eq_of_prime_in_saturation : ∀ (K : Type) [Field K] (N : ℕ) (I Q : Ideal (MvPolynomial (Fin N) K)), (∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) → Q.IsPrime → I ≤ Q → (∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ I) → (∀ g ∈ Q, ∀ n : ℕ, homogeneousComponent n g ∈ Q) ∧ GlobalTheory.idealHilbertPoly Q = GlobalTheory.idealHilbertPoly I := by
  first | exact @GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq | exact GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq | (intros; apply GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq <;> assumption)
end

