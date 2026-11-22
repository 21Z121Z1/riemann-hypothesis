import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0052
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.InputsHecke
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterInfiniteOrderAtSplit
section
open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.SplitValue

open WithZero GlobalTheory.CharVal GlobalTheory.Formalism.L2.Col.HostOk

theorem val_map_eq_one {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) {w : HeightOneSpectrum (𝓞 E)}
    (hN : Ideal.absNorm w.asIdeal = p) (hsq : ((p : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2) {z : E}
    (hz : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ w → Q.valuation E z = 1) (φ : E →+* E) (hφ : φ ≠ RingHom.id E) :
    w.valuation E (φ z) = 1 := by
  obtain ⟨Q, hQ⟩ := exists_pull φ w
  refine val_emb_eq_one hQ (hz Q fun e => hφ ?_)
  subst e
  exact GlobalTheory.ringHom_eq_of_comap_eq_unramified_degree_one E E φ (RingHom.id E) Q Q p hp hN hsq hQ (fun r => Iff.rfl)

theorem not_isOfFinOrder_val : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (n : D.R.Psi → ℤ) (p : ℕ), (∀ v, χ.TameAt v) → χ.HasInf (Formalism.L2.Host.embPsi D.host) n → (∀ g, n g ≠ 0) → SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → ¬ IsOfFinOrder (χ.val w) := by
  intro D χ n p ht hinf hn hp w hw hfin
  classical
  obtain ⟨hN, hsq⟩ := hp.2 w hw
  obtain ⟨M, z, hM, h1, h2, h3⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf D.host.E χ
    (GlobalTheory.Mem.UnrAe.unr_ae_and_level _ χ).1.toFinset (GlobalTheory.HeckeProduct.hchar_productRule _ χ)
    (fun v hv => by simpa using hv) ht w (Formalism.L2.Host.unif w)
  obtain ⟨a, ha, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have h4 : χ.inf z ^ a = 1 := by
    have := congrArg (· ^ a) h3
    simp only [mul_pow, one_pow] at this
    rw [← pow_mul, mul_comm M a, pow_mul] at this
    change χ.val w ^ a = 1 at hpow
    unfold Formalism.L2.Host.HChar.val at hpow
    rwa [hpow, one_pow, one_mul] at this
  have h5 : ((χ.inf z : ℂˣ) : ℂ) ^ 2 =
      D.host.φ₀ (∏ g : D.R.Psi, (D.host.sigmaOf g z / D.host.sigmaOf g (D.host.conj z)) ^ n g) := by
    rw [hinf z, map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [map_zpow₀, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    congr 1
    have e : D.host.φ₀ (D.host.sigmaOf g (D.host.conj z)) = starRingEnd ℂ (D.host.φ₀ (D.host.sigmaOf g z)) := by
      rw [sigma_conj]
      exact D.host.conjE_apply D.host.φ₀ _
    have e' : Formalism.L2.Host.embPsi D.host g z = D.host.φ₀ (D.host.sigmaOf g z) := rfl
    have h0 : D.host.φ₀ (D.host.sigmaOf g z) ≠ 0 := by simp
    rw [map_div₀, e, e', div_pow, div_eq_div_iff (pow_ne_zero _ (by simpa using h0)) (by simpa using h0), sq, mul_assoc,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have h6 : (∏ g : D.R.Psi, (D.host.sigmaOf g z / D.host.sigmaOf g (D.host.conj z)) ^ n g) ^ a = 1 := by
    apply D.host.φ₀.injective
    rw [map_pow, ← h5, ← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, h4, map_one]
    simp
  have h7 := unit_of_pow (w := w) ha (by rw [h6, map_one])
  have hc : ∀ g : D.R.Psi, w.valuation _ (D.host.sigmaOf g (D.host.conj z)) = 1 := by
    intro g
    refine val_map_eq_one hp.1 hN hsq h2
      ((D.host.sigmaOf g : D.host.E →+* D.host.E).comp (D.host.conj : D.host.E →+* D.host.E)) fun e => ?_
    have := RingHom.congr_fun e D.host.sqrtMinusD
    change D.host.sigmaOf g (D.host.conj D.host.sqrtMinusD) = D.host.sqrtMinusD at this
    rw [conj_b, map_neg, sigmaOf_b] at this
    exact b_ne D.host this.symm
  have hone : D.host.sigmaOf ((1 : D.R.Psi) : D.R.GG) = 1 :=
    map_one (D.host.gal).symm
  have hg : ∀ g : D.R.Psi, g ≠ 1 → w.valuation _ (D.host.sigmaOf g z) = 1 := by
    intro g hg
    refine val_map_eq_one hp.1 hN hsq h2 (D.host.sigmaOf g : D.host.E →+* D.host.E) fun e => hg ?_
    have e1 : D.host.sigmaOf g = D.host.sigmaOf ((1 : D.R.Psi) : D.R.GG) := by
      rw [hone]
      exact AlgEquiv.ext fun x => RingHom.congr_fun e x
    exact Subtype.ext ((D.host.gal).symm.injective e1)
  rw [map_prod, Finset.prod_eq_single 1 (fun g _ h => by rw [map_zpow₀, map_div₀, hg g h, hc g, div_one, one_zpow])
    (by simp), map_zpow₀, map_div₀, hc, div_one, hone, AlgEquiv.one_apply, h1, val_unif, ← exp_nsmul, ← exp_zsmul,
    ← exp_zero, exp_inj] at h7
  simp only [nsmul_eq_mul, smul_eq_mul, mul_eq_zero] at h7
  rcases h7 with h | h | h
  · exact hn 1 h
  · omega
  · omega

end GlobalTheory.SplitValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeRatioPosOfPublished
section
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.HeckeRatio

section Standard

open HeckeCharacterZeroLocus.ThmBIn GlobalTheory.LFun GlobalTheory.HeckeOne GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.UnitaryHeckeBaseChange
open Formalism.L2.Host (HChar)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_conj_prime (hσ : IsCMExt F E σ) (χ : (AE F E)ˣ →* Circle)
    (hF : ∀ a : (AF F)ˣ, χ (idF F E a) = 1) :
    ∃ c : HeightOneSpectrum (𝓞 E) ≃ HeightOneSpectrum (𝓞 E), (∀ P, normP (c P) = normP P) ∧
      (∀ P, (c P).under (𝓞 F) = P.under (𝓞 F)) ∧ ∀ P, chiAt σ χ (c P) = starRingEnd ℂ (chiAt σ χ P) := by
  obtain ⟨c, hcc, hN, hmem, hund, hinv, hint, hidem⟩ := GlobalTheory.cmConjugation_on_primes_adeles_idempotents F E σ hσ
  have hsd := GlobalTheory.ideleChar_conj_eq_inv_of_trivial_on_base F E σ hσ χ hF
  have hun := GlobalTheory.HeckeUnif.unifIdele_exists_chiAt F E σ hσ χ
  have hram : ∀ P, IsUnramAt σ χ P → IsUnramAt σ χ (c P) := by
    rintro P ⟨e, f, he, hz⟩
    refine ⟨cA σ e, f, hidem P e f he, fun z h1 h2 h3 => ?_⟩
    have h4 : χ (Units.map (cA σ).toMonoidHom z) = 1 := by
      apply hz
      · change cA σ (z : AE F E) = e * cA σ (z : AE F E) + (1 - e)
        have := congrArg (cA σ) h1
        rwa [map_add, map_mul, map_sub, map_one, hinv] at this
      · exact (hint _).2 h2
      · exact (hint _).2 h3
    rw [hsd z (Units.map (cA σ).toMonoidHom z) rfl] at h4
    exact inv_eq_one.1 h4
  have hunif : ∀ P x, IsUnifIdele σ P x → IsUnifIdele σ (c P) (Units.map (cA σ).toMonoidHom x) := by
    rintro P x ⟨e, f, ϖ, he, h1, h2, h3⟩
    have hy : ((RingOfIntegers.mapRingHom σ.toRingHom ϖ : 𝓞 E) : E) = σ ϖ := rfl
    refine ⟨cA σ e, f, RingOfIntegers.mapRingHom σ.toRingHom ϖ, hidem P e f he,
      ((hmem P _ _ hy).1).2 h1, fun h => h2 (((hmem P _ _ hy).2).1 h), ?_⟩
    change cA σ (x : AE F E) = _
    rw [h3, map_add, map_mul, map_sub, map_one, GlobalTheory.cA_incA_apply, hy]
  refine ⟨c, hN, fun P => ((hund P (c P)).2 (Or.inr rfl)).symm, fun P => ?_⟩
  by_cases hP : IsUnramAt σ χ P
  · obtain ⟨x, hx⟩ := (hun P).1
    rw [(hun P).2.1 hP x hx, (hun (c P)).2.1 (hram P hP) _ (hunif P x hx),
      hsd x (Units.map (cA σ).toMonoidHom x) rfl, Circle.coe_inv_eq_conj]
  · have hP' : ¬ IsUnramAt σ χ (c P) := fun h => hP (by simpa [hcc] using hram _ h)
    simp [chiAt, hP, hP']

def toH (χ : UnitaryHeckeChar E) : HChar E := toHChar χ.toHom ⟨χ.continuous_toHom, χ.map_principal⟩

theorem unrAt_toH (χ : UnitaryHeckeChar E) (P : HeightOneSpectrum (𝓞 E)) :
    (toH χ).UnrAt P ↔ χ.IsUnramifiedAt P :=
  forall₂_congr fun _ _ => ⟨fun h => Circle.ext (congrArg Units.val h),
    fun h => (congrArg Circle.toUnits h).trans (map_one _)⟩

theorem val_toH (χ : UnitaryHeckeChar E) {P : HeightOneSpectrum (𝓞 E)} (h : χ.IsUnramifiedAt P) :
    (((toH χ).val P : ℂˣ) : ℂ) = χ.valueAt P :=
  (χ.valueAt_eq h (Formalism.L2.Host.unif_spec P)).symm

theorem eulerFactor_toH (χ : UnitaryHeckeChar E) (s : ℂ) (P : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.CMVal.eulerFactor (toH χ) s P = χ.eulerFactor P s := by
  unfold GlobalTheory.CMVal.eulerFactor UnitaryHeckeChar.eulerFactor
  split_ifs with h
  · rw [val_toH χ ((unrAt_toH χ P).1 h)]
  · rw [χ.valueAt_of_ramified fun h' => h ((unrAt_toH χ P).2 h'), zero_mul, sub_zero, inv_one]

theorem eq_zero_of_npow (H : GlobalTheory.Published.HeckeLPartialContinuation) {z : ℂ} (hz : z.re = 0)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), npow P (-z) = 1) : z = 0 := by
  obtain ⟨Z, hZ, h1, h2⟩ := (H E ∅ Set.finite_empty).2
  have e : ∀ s : ℂ, zetaOff (K := E) ∅ (s + z) = zetaOff (K := E) ∅ s := fun s => by
    simp only [zetaOff, eulerProd, locL, neg_add, LFun.npow_add, h, mul_one]
  have k := GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter.eq_of_eqOn_re (f := fun s => Z s * (s + z - 1)) (g := fun s => Z (s + z) * (s - 1))
    (hZ.mul (by fun_prop)) ((hZ.comp (by fun_prop)).mul (by fun_prop)) fun s hs => by
      rw [h1 s hs, h1 (s + z) (by simpa [hz] using hs), e]; ring
  have k1 := congrFun k 1
  simp only [sub_self, mul_zero, add_sub_cancel_left] at k1
  exact (mul_eq_zero.1 k1).resolve_left (h2 1 (by simp))

theorem exists_entire_pos (H : GlobalTheory.Published.HeckeLPartialContinuation) (hσ : IsCMExt F E σ)
    (χ : (AE F E)ˣ →* Circle) (hχ : IsHeckeChar F E χ) (hF : ∀ a : (AF F)ˣ, χ (idF F E a) = 1) (hne : χ ≠ 1)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 E) → Prop)
    (hp : ∀ P, p P ↔ P.under (𝓞 F) ∉ S) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      (∀ s : ℂ, 1 < s.re → HasProd (fun P : {P // p P} => lfac σ χ P.1 s) (Λ s)) ∧
      ∀ n : ℕ, 1 ≤ n → (Λ n).im = 0 ∧ 0 < (Λ n).re := by
  obtain ⟨c, hN, hU, hc⟩ := exists_conj_prime hσ χ hF
  obtain ⟨χ, rfl, -⟩ := (GlobalTheory.UnitaryHeckeBaseChange.isHeckeChar_iff hσ χ).1 hχ
  have hu : (toH χ).IsUnitary := isUnitary_toHChar _ _
  have hnp : ¬ ∃ t : ℝ, IsNormPow (toH χ) t := by
    rintro ⟨t, ht⟩
    rw [isNormPow_iff] at ht
    have hv : ∀ P, chiAt σ (pull F χ) P = npow P (-((t : ℂ) * Complex.I)) := fun P => by
      rw [chiAt_eq hσ, ← val_toH χ ((unrAt_toH χ P).1 (ht ▸ unrAt_normChar t P)), ht, val_normChar]
      rfl
    have h0 : (t : ℂ) * Complex.I + (t : ℂ) * Complex.I = 0 := eq_zero_of_npow (E := E) H (by simp) fun P => by
      have e1 : npow (c P) (-((t : ℂ) * Complex.I)) = npow P (-((t : ℂ) * Complex.I)) :=
        congrArg (fun n : ℕ => (n : ℂ) ^ (-((t : ℂ) * Complex.I))) (hN P)
      have e2 := hc P
      rw [hv, hv, e1] at e2
      rw [neg_add, LFun.npow_add]
      nth_rewrite 2 [e2]
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_npow]
      simp
    have ht0 : t = 0 := by simpa using congrArg Complex.im h0
    rw [ht0, normChar_zero] at ht
    refine hne ((pull_eq_one_iff hσ χ).2 (UnitaryHeckeChar.ext (MonoidHom.ext fun x => Circle.ext ?_)))
    exact congrArg (fun ψ : HChar E => ((ψ.1 x : ℂˣ) : ℂ)) ht
  obtain rfl : p = fun P => P ∉ {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ S} :=
    funext fun P => propext (hp P)
  have hT : {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ S}.Finite := by
    have := Filter.mem_cofinite.1 (tendsto_under F E S.finite_toSet.compl_mem_cofinite)
    exact this.subset fun P hP h => h hP
  obtain ⟨Λ, hΛ, h1, h2⟩ := (H E _ hT).1 _ hu hnp
  have hprod : ∀ s : ℂ, 1 < s.re → HasProd (fun P : {P // P ∉ {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ S}} =>
      lfac σ (pull F χ) P.1 s) (Λ s) := fun s hs => by
    have k := (converges_heckeFam {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ S} hu hs).hasProd
    simp only [locL_heckeFam, eulerFactor_toH, ← lfac_eq hσ] at k
    rw [h1 s hs]
    exact k
  obtain ⟨k1, k2⟩ := eulerProduct_eq_exp_and_pos {P // P ∉ {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ S}}
    (fun P => normP P.1) (fun P => chiAt σ (pull F χ) P.1) (fun P => GlobalTheory.LFun.one_lt_absNorm P.1)
    (fun P => (GlobalTheory.HeckeUnif.unifIdele_exists_chiAt F E σ hσ _ P.1).2.2)
    (fun t ht => (UnitaryHeckeChar.summable_absNorm_rpow ht).subtype _)
  have hpos : ∀ s : ℂ, 1 < s.re → s.im = 0 → (Λ s).im = 0 ∧ 0 < (Λ s).re := fun s hs hs0 => by
    rw [(hprod s hs).unique (k1 s hs).2]
    exact k2 (c.subtypeEquiv fun P => by simp only [Set.mem_ofPred_eq, hU]) (fun P => hN P.1) (fun P => hc P.1) s hs hs0
  refine ⟨Λ, hΛ, hprod, fun n hn => ?_⟩
  rcases hn.eq_or_lt with rfl | hlt
  · simpa using real_pos_at_one_of_right Λ hΛ.continuous.continuousAt (h2 1 (by simp)) hpos
  · exact hpos n (by simpa using hlt) (by simp)

end Standard

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult GlobalTheory.IndefiniteRowSideFullHecke.PartialLFunctionCharacter

variable {D : D7}

theorem offS_iff (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    OffS D S w ↔ w.under (𝓞 D.host.F) ∉ S := by
  constructor
  · intro h hw
    obtain ⟨x, hx, hy⟩ := h _ hw
    exact hy (algebraMap _ _ x) rfl hx
  · intro h u hu
    have : ¬ u.asIdeal ≤ (w.under (𝓞 D.host.F)).asIdeal := fun hle =>
      h (HeightOneSpectrum.ext (u.isMaximal.eq_of_le (w.under _).isPrime.ne_top hle) ▸ hu)
    obtain ⟨x, hx, hx'⟩ := SetLike.not_le_iff_exists.1 this
    refine ⟨x, hx, fun y hy hw => hx' ?_⟩
    obtain rfl : y = algebraMap _ _ x := RingOfIntegers.ext hy
    exact hw

theorem isPrimeIdem_eq : IsPrimeIdem (D := D) = HeckeCharacterZeroLocus.ThmBIn.IsPrimeIdem D.sp.cm.sig := rfl

theorem isUnifIdele_eq : Mi.IsUnifIdele (D := D) = HeckeCharacterZeroLocus.ThmBIn.IsUnifIdele D.sp.cm.sig := by
  funext P x
  unfold Mi.IsUnifIdele HeckeCharacterZeroLocus.ThmBIn.IsUnifIdele
  rw [isPrimeIdem_eq]
  rfl

theorem isUnramAt_eq : Mi.IsUnramAt (D := D) = HeckeCharacterZeroLocus.ThmBIn.IsUnramAt D.sp.cm.sig := by
  funext χ P
  unfold Mi.IsUnramAt HeckeCharacterZeroLocus.ThmBIn.IsUnramAt
  rw [isPrimeIdem_eq]
  rfl

theorem lfac_eq (χ : (AE D)ˣ →* Circle) : Mi.lfac χ = HeckeCharacterZeroLocus.ThmBIn.lfac D.sp.cm.sig χ := by
  funext P s
  have key : ∀ (A A' : Prop) (U U' : (AE D)ˣ → Prop), A = A' → U = U' →
      (open Classical in if h : A ∧ ∃ x, U x then ((χ h.2.choose : Circle) : ℂ) else 0) =
      (open Classical in if h : A' ∧ ∃ x, U' x then ((χ h.2.choose : Circle) : ℂ) else 0) := by
    rintro _ _ _ _ rfl rfl
    rfl
  have e0 := key (Mi.IsUnramAt χ P) (HeckeCharacterZeroLocus.ThmBIn.IsUnramAt D.sp.cm.sig χ P) (Mi.IsUnifIdele P)
    (HeckeCharacterZeroLocus.ThmBIn.IsUnifIdele D.sp.cm.sig P) (by rw [isUnramAt_eq]) (by rw [isUnifIdele_eq])
  have e : Mi.chiAt χ P = HeckeCharacterZeroLocus.ThmBIn.chiAt D.sp.cm.sig χ P := by
    unfold Mi.chiAt HeckeCharacterZeroLocus.ThmBIn.chiAt
    exact e0
  unfold Mi.lfac HeckeCharacterZeroLocus.ThmBIn.lfac
  rw [e]
  rfl

theorem heckeRatioPos_of_partialContinuation (H : GlobalTheory.Published.HeckeLPartialContinuation) (D : D7) : HeckeRatioPos D := by
  rintro μ μ' hμ hμ' hF hF' ⟨τ, e, e', h1, h2, hne⟩ t
  have hχ : IsHeckeChar D (μ * μ'⁻¹) := ⟨hμ.1.mul hμ'.1.inv, fun x => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hμ.2 x, hμ'.2 x, inv_one, mul_one]⟩
  have hχF : ∀ a, (μ * μ'⁻¹) (idF D a) = 1 := fun a => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hF a, hF' a, inv_one, mul_one]
  have hχ1 : μ * μ'⁻¹ ≠ 1 := fun h => by
    obtain rfl := mul_inv_eq_one.1 h
    exact hne (neg_injective (GlobalTheory.Mem.HeckeExp.hasInfExp_unique h1 h2))
  have key := exists_entire_pos H (Formalism.IndefR.ThmB.InputsHecke.isCMExt D) (μ * μ'⁻¹) hχ hχF hχ1
  refine ⟨?_, fun S => ?_⟩
  · obtain ⟨Λ, a1, a2, a3⟩ := key ∅ (fun _ => True) fun P => by simp
    refine ⟨Λ, ⟨a1, fun s hs => ?_⟩, fun n hn _ => a3 n hn⟩
    rw [lfac_eq]
    exact (Equiv.subtypeUnivEquiv (p := fun _ => True) fun _ => trivial).hasProd_iff.1 (a2 s hs)
  · obtain ⟨Λ, a1, a2, a3⟩ := key S (OffS D S) (offS_iff S)
    refine ⟨Λ, ⟨a1, fun s hs => ?_⟩, fun n hn _ => a3 n hn⟩
    rw [lfac_eq]
    exact a2 s hs

theorem heckeRatioPos (D : D7) : HeckeRatioPos D :=
  heckeRatioPos_of_partialContinuation GlobalTheory.Published.HeckeLPartialContinuation_holds D

end GlobalTheory.HeckeRatio

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ParahoricCompact

theorem exists_compact_entries {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) :
    ∃ C : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E), IsCompact C ∧ ∀ x : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E),
      Formalism.UG.bc (GlobalTheory.Mass.swapTens F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) : _ →+* _) x ∈ St β → ∀ i j, x.1 i j ∈ C := by
  classical
  haveI : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :=
    IsModuleTopology.isTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) _
  obtain ⟨-, C0, hC0, hC0m⟩ := GlobalTheory.Mass.intTens_open_compact F E
  let s := GlobalTheory.Mass.swapTens F E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)

  let b : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := (β : Matrix (Fin n) (Fin n) _).map s.symm
  let c : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :=
    ((β⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map s.symm

  let f : Fin n → Fin n → (Fin n → Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E :=
    fun i j a => ∑ l, (∑ k, b i k * a k l) * c l j
  have hf : ∀ i j, Continuous (f i j) := fun i j =>
    continuous_finsetSum _ fun l _ =>
      (continuous_finsetSum _ fun k _ =>
        continuous_const.mul ((continuous_apply l).comp (continuous_apply k))).mul continuous_const
  have hS : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => C0) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC0
  refine ⟨⋃ i, ⋃ j, f i j '' Set.univ.pi (fun _ : Fin n => Set.univ.pi fun _ : Fin n => C0),
    isCompact_iUnion fun i => isCompact_iUnion fun j => hS.image (hf i j), ?_⟩
  intro x hx i j
  obtain ⟨y, hy⟩ := hx
  refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j,
    ⟨fun k l => s.symm ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) k l), ?_, ?_⟩⟩⟩
  · intro k _ l _
    apply hC0m
    change (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E →+* E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) (s.symm _) ∈ Formalism.L2.Herm.intAf F E
    rw [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) k l).2
  · have hx' : (x : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) i j =
        s.symm (((Formalism.UG.bc (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E →+* E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) x :
          GL (Fin n) (E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) i j) := by
      rw [Formalism.UG.P.bc_coe]
      simp
    have hy' : Formalism.UG.bc (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E →+* E ⊗[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) x =
        β * Formalism.L2.DIV.intGL F E n y * β⁻¹ := by
      rw [← hy]
      rfl
    rw [hx', hy', Units.val_mul, Units.val_mul, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, Matrix.mul_apply, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, Formalism.L2.DIV.intGL, Formalism.UG.P.bc_coe]
    rfl

variable {D : D7}

theorem isOpen_comap_lev (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsOpen (((lev D.sp.cm V.gram β L).comap (finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
  classical
  haveI := (GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V).1
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β (L.Pg ∪ L.Q)] with κ hκ
  obtain ⟨hU, hS, hR⟩ := hκ
  show finE V κ ∈ lev D.sp.cm V.gram β L
  refine Formalism.L2.DIV.Kg_le_lev (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right ?_
  simp only [Formalism.L2.DIV.Kg, Subgroup.mem_inf, Subgroup.mem_iInf]
  exact ⟨⟨hU, hS⟩, fun PP hPP => Formalism.L2.DIV.mem_princAt.2 ⟨hS, hR PP hPP⟩⟩

theorem exists_compact (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) :
    ∃ C : Set (GA D V), IsCompact C ∧ ∀ k : GA D V, k ∈ GfC V → finE V k ∈ St β → k ∈ C := by
  obtain ⟨C1, hC1, hC1m⟩ := exists_compact_entries (F := D.host.F) (E := D.host.E) β
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨K, hK, hKm⟩ := GlobalTheory.StabCompact.exists_compact_adele D θ hθ 1 C1 hC1

  haveI : T2Space (InfiniteAdeleRing D.host.F) :=
    inferInstanceAs (T2Space ((v : InfinitePlace D.host.F) → v.Completion))
  haveI : T2Space (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    inferInstanceAs (T2Space (RestrictedProduct
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F) => v.adicCompletion D.host.F)
      (fun v => (v.adicCompletionIntegers D.host.F : Set (v.adicCompletion D.host.F))) Filter.cofinite))
  haveI : T2Space (AF D.host.F) :=
    inferInstanceAs (T2Space (InfiniteAdeleRing D.host.F × FiniteAdeleRing (𝓞 D.host.F) D.host.F))
  obtain ⟨K', hK', hK'm⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram
    (GlobalTheory.StabCompact.det_gram_ne_zero V) K hK
  refine ⟨K', hK', fun k hk hst => hK'm k fun i j => hKm _ ?_ ?_⟩
  ·
    have hsw : (GlobalTheory.Mass.swapTens D.host.F D.host.E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) : _ →+* _) = swapAE D :=
      RingHom.ext fun _ => rfl
    have hst' : Formalism.UG.bc (GlobalTheory.Mass.swapTens D.host.F D.host.E (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) : _ →+* _)
        (finHom V k) ∈ St β := by
      rw [hsw]
      exact hst
    have h := hC1m (finHom V k) hst' i j
    rw [finHom, MonoidHom.comp_apply, Formalism.UG.P.bc_coe] at h
    exact h
  ·
    intro ρ
    have h1 : infHom V k = 1 := hk
    have h2 : infPart D ((HA.mat (AF D.host.F) D.sp.cm.sig V.gram k : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) i j) =
        (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := by
      have h3 := congrArg (fun g : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) =>
        (g : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j) h1
      simp only [infHom, MonoidHom.comp_apply, Formalism.UG.P.bc_coe, Units.val_one] at h3
      exact h3
    rw [h2]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.one_apply_eq, map_one, norm_one, le_refl]
    · simp only [Matrix.one_apply_ne hij, map_zero, norm_zero, zero_le_one]

theorem isCompact_levG (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsCompact ((levG V β L : Subgroup (GA D V)) : Set (GA D V)) := by
  haveI := (GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V).1
  obtain ⟨C, hC, hCm⟩ := exists_compact V β
  refine hC.of_isClosed_subset ?_ ?_
  · rw [levG, levA, Subgroup.coe_inf]
    exact (GlobalTheory.Ker.CongTop.isClosed_GfC V).inter
      (Subgroup.isClosed_of_isOpen _ (isOpen_comap_lev V β L))
  · intro k hk
    rw [SetLike.mem_coe, levG, levA, Subgroup.mem_inf] at hk
    exact hCm k hk.1 (Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hk.2))

theorem isCompact_flag_and_lift : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank), IsCompact ((levG V β (flagL L) : Subgroup (GA D V)) : Set (GA D V)) ∧ ∀ g0 κ, IsLevelLift V β L g0 κ → κ ∈ levG V β (flagL L) := by
  intro D V β L
  refine ⟨isCompact_levG V β (flagL L), fun g0 κ hκ => ?_⟩
  obtain ⟨h1, h2, -⟩ := hκ
  rw [levG, levA, Subgroup.mem_inf]
  refine ⟨h1, ?_⟩
  show finE V κ ∈ lev D.sp.cm V.gram β (flagL L)
  rw [Formalism.L2.DIV.mem_lev]
  exact ⟨h2, Subgroup.mem_top _⟩

end GlobalTheory.ParahoricCompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHarishChandraParamGridColumnRealParameterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHarishChandraParam_gridColumnRealParameter : ∀ (D : D7), HostHyp D → ∀ (i : ℕ), i ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool), n = GlobalTheory.Grid.rkP D i → IsEnum (GlobalTheory.Grid.parP D i τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  first | exact @GlobalTheory.Grid.isHCParam_parP | exact GlobalTheory.Grid.isHCParam_parP | (intros; apply GlobalTheory.Grid.isHCParam_parP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHarishChandraParamGridRowRealParameterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHarishChandraParam_gridRowRealParameter : ∀ (D : D7), HostHyp D → ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ (τ : D.what₂.Tau) (n : ℕ) (lam : Fin n → ℝ) (ε : Fin n → Bool), n = GlobalTheory.Grid.rkX D j → IsEnum (GlobalTheory.Grid.parXp D j τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam := by
  first | exact @GlobalTheory.GridHC.isHCParam_parXp | exact GlobalTheory.GridHC.isHCParam_parXp | (intros; apply GlobalTheory.GridHC.isHCParam_parXp <;> assumption)
end

