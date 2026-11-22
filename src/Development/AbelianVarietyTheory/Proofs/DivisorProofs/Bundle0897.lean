import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0868
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.Columns.DecoFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0307
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0872
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformiserIdeleMultiplicativeOnIdeals
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.LatEnt UniqueFactorizationMonoid

namespace GlobalTheory.CMVal.IdealIdele

variable {E : Type} [Field E] [NumberField E]

open Classical in

def primeIdele (p : Ideal (𝓞 E)) : (Af E)ˣ :=
  if h : p.IsPrime ∧ p ≠ ⊥ then unifAt ⟨p, h.1, h.2⟩ else 1

def idl (I : Ideal (𝓞 E)) : (Af E)ˣ := ((normalizedFactors I).map primeIdele).prod

theorem idl_top : idl (⊤ : Ideal (𝓞 E)) = 1 := by
  rw [idl, ← Ideal.one_eq_top, normalizedFactors_one]; simp

theorem idl_mul {I J : Ideal (𝓞 E)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : idl (I * J) = idl I * idl J := by
  rw [idl, normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]; rfl

theorem nf_prime (v : HeightOneSpectrum (𝓞 E)) : normalizedFactors v.asIdeal = {v.asIdeal} := by
  rw [normalizedFactors_irreducible v.irreducible, normalize_eq]

theorem idl_prime (v : HeightOneSpectrum (𝓞 E)) : idl v.asIdeal = unifAt v := by
  rw [idl, nf_prime, Multiset.map_singleton, Multiset.prod_singleton, primeIdele,
    dif_pos ⟨v.isPrime, v.ne_bot⟩]

theorem ind {P : Ideal (𝓞 E) → Prop} (h1 : P ⊤)
    (h2 : ∀ (v : HeightOneSpectrum (𝓞 E)) (I : Ideal (𝓞 E)), I ≠ ⊥ → P I → P (v.asIdeal * I)) :
    ∀ I, I ≠ ⊥ → P I := fun I => by
  refine induction_on_prime (P := fun I => I ≠ ⊥ → P I) I (fun h => absurd rfl h) ?_ ?_
  · intro x hx _
    rw [Ideal.isUnit_iff.1 hx]; exact h1
  · intro a p ha hp h _
    exact h2 ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩ a ha (h ha)

theorem mul_apply' (a b : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    ((a * b : (Af E)ˣ) : Af E) w = (a : Af E) w * (b : Af E) w := rfl

theorem one_apply' (w : HeightOneSpectrum (𝓞 E)) : ((1 : (Af E)ˣ) : Af E) w = 1 := rfl

theorem modF_idl : ∀ I : Ideal (𝓞 E), I ≠ ⊥ → modF (idl I) = ((Ideal.absNorm I : ℕ) : ℝ)⁻¹ := by
  refine ind ?_ ?_
  · rw [idl_top, modF_eq_one fun w => by rw [one_apply', map_one]]
    simp
  · intro v I hI h
    rw [idl_mul v.ne_bot hI, ObjModel.modF_mul, h, idl_prime, modF_unifAt, map_mul]
    push_cast
    rw [mul_inv]

open Classical in
theorem val_idl (w : HeightOneSpectrum (𝓞 E)) : ∀ I : Ideal (𝓞 E), I ≠ ⊥ →
    Valued.v ((idl I : Af E) w) = WithZero.exp (-((normalizedFactors I).count w.asIdeal : ℤ)) := by
  refine ind ?_ ?_
  · rw [idl_top, one_apply', map_one, ← Ideal.one_eq_top, normalizedFactors_one]; simp
  · intro v I hI h
    rw [idl_mul v.ne_bot hI, mul_apply', map_mul, h, idl_prime, normalizedFactors_mul v.ne_bot hI, nf_prime,
      Multiset.count_add]
    by_cases hw : w = v
    · subst hw
      rw [(unifAt_spec w).2, ← WithZero.exp_add, Multiset.count_singleton_self]
      congr 1; push_cast; ring
    · have : w.asIdeal ≠ v.asIdeal := fun h => hw (HeightOneSpectrum.ext h)
      rw [(unifAt_spec v).1 w hw, map_one, one_mul, Multiset.count_singleton, if_neg this, zero_add]

theorem idl_eq_one (w : HeightOneSpectrum (𝓞 E)) : ∀ I : Ideal (𝓞 E), I ≠ ⊥ →
    ¬ w.asIdeal ∣ I → (idl I : Af E) w = 1 := by
  refine ind ?_ ?_
  · intro _; rw [idl_top, one_apply']
  · intro v I hI h hd
    have hw : w ≠ v := by
      rintro rfl
      exact hd (dvd_mul_right _ _)
    rw [idl_mul v.ne_bot hI, mul_apply', h fun h => hd (h.mul_left _), idl_prime, (unifAt_spec v).1 w hw, one_mul]

theorem mem_nf {w : HeightOneSpectrum (𝓞 E)} {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) (h : w.asIdeal ∣ I) :
    w.asIdeal ∈ normalizedFactors I :=
  (mem_normalizedFactors_iff hI).2 ⟨w.prime, h⟩

open Classical in
theorem exists_count (n : HeightOneSpectrum (𝓞 E) → ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ I : Ideal (𝓞 E), I ≠ ⊥ ∧ ∀ w : HeightOneSpectrum (𝓞 E),
      (normalizedFactors I).count w.asIdeal = if w ∈ S then n w else 0 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun w => by rw [normalizedFactors_one]; simp⟩
  | insert v S hv ih =>
    obtain ⟨I, hI, h⟩ := ih
    have h0 : v.asIdeal ^ n v ≠ 0 := pow_ne_zero _ v.ne_bot
    refine ⟨v.asIdeal ^ n v * I, mul_ne_zero h0 hI, fun w => ?_⟩
    rw [normalizedFactors_mul h0 hI, normalizedFactors_pow, nf_prime, Multiset.count_add, h, Multiset.count_nsmul,
      Multiset.count_singleton]
    by_cases hw : w = v
    · subst hw; simp [hv]
    · have : w.asIdeal ≠ v.asIdeal := fun h => hw (HeightOneSpectrum.ext h)
      simp [this, hw]

theorem finite_val_ne_one (z : (Af E)ˣ) : {w : HeightOneSpectrum (𝓞 E) | Valued.v ((z : Af E) w) ≠ 1}.Finite :=
  GlobalTheory.Mem.TupHecke.finite_nonunit z

theorem main : ∀ (E : Type) [Field E] [NumberField E], ∃ t : Ideal (𝓞 E) → (Af E)ˣ, t ⊤ = 1 ∧
    (∀ I J, I ≠ ⊥ → J ≠ ⊥ → t (I * J) = t I * t J) ∧ (∀ v : HeightOneSpectrum (𝓞 E), t v.asIdeal = unifAt v) ∧
    (∀ I, I ≠ ⊥ → modF (t I) = ((Ideal.absNorm I : ℕ) : ℝ)⁻¹) ∧
    (∀ I, I ≠ ⊥ → ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((t I : Af E) w) ≤ 1 ∧
      (w.asIdeal ∣ I → Valued.v ((t I : Af E) w) < 1) ∧ (¬ w.asIdeal ∣ I → (t I : Af E) w = 1)) ∧
    (∀ I J, I ≠ ⊥ → J ≠ ⊥ → (∀ w, Valued.v ((t I : Af E) w) = Valued.v ((t J : Af E) w)) → I = J) ∧
    ∀ z : (Af E)ˣ, (∀ w, Valued.v ((z : Af E) w) ≤ 1) →
      ∃ I, I ≠ ⊥ ∧ ∀ w, Valued.v ((t I : Af E) w) = Valued.v ((z : Af E) w) := by
  intro E _ _
  classical
  refine ⟨idl, idl_top, fun _ _ => idl_mul, idl_prime, modF_idl, fun I hI w => ⟨?_, fun hd => ?_, idl_eq_one w I hI⟩,
    fun I J hI hJ h => ?_, fun z hz => ?_⟩
  · rw [val_idl w I hI, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  · have := Multiset.count_pos.2 (mem_nf hI hd)
    rw [val_idl w I hI, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  · have e : normalizedFactors I = normalizedFactors J := by
      ext p
      by_cases hp : Prime p
      · have := h ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
        rw [val_idl _ I hI, val_idl _ J hJ, WithZero.exp_inj] at this
        simpa using this
      · rw [Multiset.count_eq_zero.2 fun h => hp (prime_of_normalized_factor _ h),
          Multiset.count_eq_zero.2 fun h => hp (prime_of_normalized_factor _ h)]
    rw [← Ideal.prod_normalizedFactors_eq_self hI, e, Ideal.prod_normalizedFactors_eq_self hJ]
  · obtain ⟨I, hI, h⟩ := exists_count (fun w => (-(Valued.v ((z : Af E) w)).log).toNat)
      (finite_val_ne_one z).toFinset
    refine ⟨I, hI, fun w => ?_⟩
    rw [val_idl w I hI, h]
    split_ifs with hw
    · have h0 := ObjModel.coord_ne z w
      have h1 : (Valued.v ((z : Af E) w)).log ≤ 0 := by
        rw [← WithZero.exp_le_exp, WithZero.exp_log h0]; exact hz w
      rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]
    · have : Valued.v ((z : Af E) w) = 1 := by simpa using hw
      rw [this]; simp

end GlobalTheory.CMVal.IdealIdele
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerBumpArchimedeanFactorOneNeZero
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

noncomputable section

namespace GlobalTheory.WhitBump

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]

theorem continuous_psiInf : Continuous (psiInf (E := E)) := by
  have hs : Continuous (fun z : Cinf E => sInf E z) :=
    ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact continuous_subtype_val.comp ((GroundTheory.Global.continuous_adelicChar (K := E)).comp hs)

theorem psiInf_zero : psiInf (0 : Cinf E) = 1 := by
  simp [psiInf, map_zero]

variable {E} {n : ℕ}

theorem continuous_sdM_of : Continuous fun x : Lie E n => sdM (Matrix.of x) := by
  unfold sdM
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (continuous_apply j).comp (continuous_apply i)

theorem sdM_one : sdM (1 : Matrix (Fin n) (Fin n) (Cinf E)) = 0 := by
  unfold sdM
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => ?_
  have hj' := (Finset.mem_filter.1 hj).2
  exact Matrix.one_apply_ne fun e => by subst e; omega

theorem continuous_toL_nu : Continuous fun t : Vp E n => toL (nu t) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  change Continuous fun t : Vp E n => nu t i j
  by_cases hij : i < j
  · simp only [nu, Matrix.of_apply, dif_pos hij]
    exact continuous_apply _
  · simp only [nu, Matrix.of_apply, dif_neg hij]
    exact continuous_const

theorem nu_zero : nu (0 : Vp E n) = 1 := by
  ext i j
  by_cases hij : i < j
  · simp [nu, hij, Matrix.one_apply, hij.ne]
  · simp [nu, hij, Matrix.one_apply]

theorem exists_bumpInf_oneL_ne_zero (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) :
    ∃ f : Lie E n → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ invSet E n ∧
      bumpInf f (oneL E n) ≠ 0 := by
  classical
  set h : Lie E n → ℝ := fun x => (psiInf (-sdM (Matrix.of x))).re with hh
  have hc : Continuous h :=
    Complex.continuous_re.comp ((continuous_psiInf E).comp continuous_sdM_of.neg)
  have hof : Matrix.of (oneL E n) = 1 := Matrix.of.apply_symm_apply _
  have h1 : h (oneL E n) = 1 := by
    simp only [hh, hof, sdM_one, neg_zero, psiInf_zero, Complex.one_re]
  have hU : {x | 0 < h x} ∩ invSet E n ∈ nhds (oneL E n) :=
    Filter.inter_mem ((isOpen_lt continuous_const hc).mem_nhds (by simp [h1]))
      (isOpen_invSet.mem_nhds (by change IsUnit (Matrix.of (oneL E n)); rw [hof]; exact isUnit_one))
  obtain ⟨f, hfs, hfc, hfd, hfr, hf1⟩ := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hU
  refine ⟨f, hfd, hfc, hfs.trans Set.inter_subset_right, ?_⟩
  set φ : Vp E n → Lie E n := fun t => toL (nu t) with hφ
  have hφc : Continuous φ := continuous_toL_nu
  set ψ : Lie E n → Vp E n := fun x p => x p.1.1 p.1.2 with hψ
  have hψc : Continuous ψ := continuous_pi fun p => (continuous_apply p.1.2).comp (continuous_apply p.1.1)
  have hψφ : ∀ t, ψ (φ t) = t := fun t => by
    funext p
    change nu t p.1.1 p.1.2 = t p
    simp [nu, p.2]
  have hfφ : HasCompactSupport (fun t => f (φ t)) := by
    refine HasCompactSupport.intro ((hfc.isCompact).image hψc) fun t ht => ?_
    by_contra hne
    exact ht ⟨φ t, subset_tsupport _ hne, hψφ t⟩
  have hsd : ∀ t, sdM (nu t) = sdM (Matrix.of (φ t)) := fun t => by
    rw [hφ]; simp only [toL, Equiv.apply_symm_apply]
  have hb : bumpInf f (oneL E n) = ∫ t : Vp E n, (f (φ t) : ℂ) * psiInf (-sdM (Matrix.of (φ t))) := by
    rw [bumpInf, hof]
    simp only [Matrix.mul_one, hsd]
    rfl
  set G : Vp E n → ℂ := fun t => (f (φ t) : ℂ) * psiInf (-sdM (Matrix.of (φ t))) with hG
  have hGc : Continuous G :=
    (Complex.continuous_ofReal.comp (hfd.continuous.comp hφc)).mul
      ((continuous_psiInf E).comp (continuous_sdM_of.neg.comp hφc))
  have hGs : HasCompactSupport G := (hfφ.comp_left Complex.ofReal_zero).mul_right
  have hint : Integrable G := hGc.integrable_of_hasCompactSupport hGs
  have hre : (∫ t, G t).re = ∫ t, f (φ t) * h (φ t) := by
    have := (Complex.reCLM.integral_comp_comm hint).symm
    simp only [Complex.reCLM_apply] at this
    rw [this]
    congr 1
    funext t
    simp [hG, hh, Complex.re_ofReal_mul]
  haveI : (volume : Measure (InfinitePlace E → ℂ)).IsOpenPosMeasure := Measure.pi.isOpenPosMeasure _
  haveI : (volume : Measure (Vp E n)).IsOpenPosMeasure := Measure.pi.isOpenPosMeasure _
  have hpos : 0 < ∫ t, f (φ t) * h (φ t) := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (0 : Vp E n))
      ((hfd.continuous.comp hφc).mul (hc.comp hφc)) hfφ.mul_right (fun t => ?_) ?_
    · have h0 : 0 ≤ f (φ t) := (hfr ⟨φ t, rfl⟩).1
      by_cases hz : f (φ t) = 0
      · simp [hz]
      · exact mul_nonneg h0 (hfs (subset_tsupport _ hz)).1.le
    · have : φ 0 = oneL E n := by rw [hφ]; simp only [nu_zero]
      simp [this, hf1, h1]
  intro h0
  rw [hb] at h0
  rw [h0, Complex.zero_re] at hre
  linarith

end GlobalTheory.WhitBump
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MovedIdem

open Formalism.L2.Col

variable {D : D7}

theorem sigR_mem_intAE {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig y ∈ intAE D := by
  induction hy using AddSubgroup.closure_induction with
  | mem y h =>
    obtain ⟨a, ha, x, rfl⟩ := h
    exact AddSubgroup.subset_closure ⟨a, ha, cO _ x, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem finPart_cA (z : Formalism.L2.Theta.AE D) :
    finPart D (cA D z) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, ha, hb]

theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (star x) := rfl

theorem cA_cA (z : Formalism.L2.Theta.AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun y : D.host.E => a ⊗ₜ[D.host.F] y) (star_star x)
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, ha, hb]

theorem finPart_conj_mem {e : Formalism.L2.Theta.AE D} {x : D.host.E}
    (h : finPart D (e * incA D x) ∈ intAE D) : finPart D (cA D e * incA D (star x)) ∈ intAE D := by
  have := sigR_mem_intAE h
  rwa [← finPart_cA, RingHom.map_mul, cA_incA] at this

theorem isIdemAt_conj {e : Formalism.L2.Theta.AE D} {P Q : HeightOneSpectrum (𝓞 D.host.E)} (he : IsIdemAt e Q)
    (h : ∀ x, x ∈ P.asIdeal ↔ cO _ x ∈ Q.asIdeal) : IsIdemAt (cA D e) P := by
  obtain ⟨⟨h1, h2, v, ε, h3, h4⟩, h5⟩ := he
  refine ⟨⟨by rw [← RingHom.map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, h3, by rw [cA_cA, add_comm, h4]⟩,
    fun x h0 => ?_⟩
  have h0' : cO _ x ≠ 0 := by
    intro h1
    apply h0
    rw [← cO_cO x, h1, map_zero]
  rw [h, h5 _ h0']
  refine not_congr ⟨fun hm => ?_, fun hm => ?_⟩
  · have := finPart_conj_mem hm
    rw [star_inv₀] at this
    have h6 : star ((cO _ x : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) := star_star (x : D.host.E)
    rwa [h6] at this
  · have := finPart_conj_mem hm
    rw [star_inv₀, cA_cA] at this
    exact this

theorem exists_isIdemAt : ∀ {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)),
    Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal → ∃ e : Formalism.L2.Theta.AE D, IsIdemAt e P := by
  intro D P hP
  have hex : ∃ a ∈ P.asIdeal, cO _ a ∉ P.asIdeal := by
    by_contra hn
    push Not at hn
    apply hP
    ext x
    rw [mem_conjIdeal]
    exact ⟨fun hx => by simpa only [cO_cO] using hn _ hx, hn x⟩
  obtain ⟨a, ha, ha'⟩ := hex
  let v : HeightOneSpectrum (𝓞 D.host.F) := P.under (𝓞 D.host.F)
  have hv : P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal := rfl
  obtain ⟨e, he⟩ := GlobalTheory.MovedSplit.exists_splitAt D v ⟨P.asIdeal, P.isPrime, hv, a, ha, cO _ a, rfl, ha'⟩
  obtain ⟨Q, hQ, hQv⟩ := GlobalTheory.IdemPrime.exists_isIdemAt D v e he
  have hsub : (P.asIdeal : Set (𝓞 D.host.E)) ⊆ Q.asIdeal ∪ (Q.asIdeal.comap (cO _) : Ideal (𝓞 D.host.E)) := by
    intro x hx
    obtain ⟨n, hn, -⟩ := GlobalTheory.MovedSplit.exists_int D (x * cO _ x) (by
      show star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E)
      rw [star_mul', star_star, mul_comm])
    have h1 : n ∈ v.asIdeal := by
      rw [← hv, Ideal.mem_comap, hn]
      exact Ideal.mul_mem_right _ _ hx
    rw [← hQv, Ideal.mem_comap, hn] at h1
    exact Q.isPrime.mem_or_mem h1
  rcases Ideal.subset_union.1 hsub with h | h
  · have : P = Q := HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h)
    exact ⟨e, this ▸ hQ⟩
  · have := Q.isPrime
    have h2 := P.isMaximal.eq_of_le (Ideal.comap_ne_top (cO _) Q.isPrime.ne_top) h
    exact ⟨_, isIdemAt_conj hQ fun x => by rw [h2, Ideal.mem_comap]⟩

end GlobalTheory.MovedIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspMult

section Abstract

variable {H S X : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X]

def homInto (σ : Representation ℂ H S) (ρ : Representation ℂ H X) (C : Submodule ℂ X) : Submodule ℂ (S →ₗ[ℂ] X) where
  carrier := {f | (∀ s, f s ∈ C) ∧ ∀ g s, f (σ g s) = ρ g (f s)}
  add_mem' := by
    intro f f' hf hf'
    exact ⟨fun s => C.add_mem (hf.1 s) (hf'.1 s), fun g s => by simp [hf.2 g s, hf'.2 g s]⟩
  zero_mem' := ⟨fun _ => C.zero_mem, fun g s => by simp⟩
  smul_mem' := by
    intro a f hf
    exact ⟨fun s => C.smul_mem a (hf.1 s), fun g s => by simp [hf.2 g s]⟩

def killed (ρ : Representation ℂ H X) (I : Set (MonoidAlgebra ℂ H)) : Submodule ℂ X :=
  ⨅ x ∈ I, LinearMap.ker (ρ.asAlgebraHom x)

theorem mem_killed {ρ : Representation ℂ H X} {I : Set (MonoidAlgebra ℂ H)} {v : X} :
    v ∈ killed ρ I ↔ ∀ x ∈ I, ρ.asAlgebraHom x v = 0 := by
  simp [killed]

def irrSum [TopologicalSpace H] (ρ : Representation ℂ H X) (C : Submodule ℂ X) : Submodule ℂ X :=
  ⨆ (U : Subrepresentation ρ) (_ : U.toSubmodule ≤ C ∧ U.toRepresentation.IsIrreducible ∧
    GlobalTheory.PRep.IsAdmissible U.toRepresentation), U.toSubmodule

def IsDecomp [TopologicalSpace H] (ρ : Representation ℂ H X) (C : Submodule ℂ X) : Prop :=
  ∀ x ∈ C, IsOpen {g : H | ρ g x = x} → x ∈ irrSum ρ C

end Abstract

variable {D : D7}

def finRep {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : Representation ℂ (GfC V) (MMap M) where
  toFun g := postOn M (LinearMap.funLeft ℂ ℂ fun x => x * (g : GA D V))
  map_one' := by
    ext T v x
    simp [postOn_apply, LinearMap.funLeft]
  map_mul' a b := by
    ext T v x
    simp [postOn_apply, LinearMap.funLeft, mul_assoc]

theorem finRep_apply {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (g : GfC V) (T : MMap M) (v : M.Vec) (x : GA D V) :
    finRep M g T v x = T v (x * (g : GA D V)) := rfl

abbrev allMaps (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) : Submodule ℂ (MMap M) := Mult θ M ∅ (fun _ => 1)

def cuspMult (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) : Cardinal :=
  Module.rank ℂ (homInto σ (finRep M) (allMaps θ M))

variable (D) in

def CuspDecomp : Prop :=
  ∀ (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsDecomp (finRep M) (allMaps θ M)

structure IsFinIso (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (Pg : Finset (Pl D.host.E))
    (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (Φ : GfC V ≃ₜ* GfC V') : Prop where
  isom : HMul.hMul (HMul.hMul (Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) j)
      (V'.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)))) j =
    V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))
  conj : ∀ g : GfC V, HMul.hMul (finE V' (Φ g : GA D V')).val j = HMul.hMul j (finE V (g : GA D V)).val
  frame : ∃ (h : V.rank = V'.rank) (u : GL (Fin V'.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)),
    HMul.hMul j β.val = (β' * intGL D.host.F D.host.E V'.rank u).val.submatrix id (Fin.cast h) ∧
      ∀ PP ∈ Pg, Formalism.UG.bc (resS D.host.F PP) u = 1

theorem IsFinIso.refl (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Pg : Finset (Pl D.host.E)) :
    IsFinIso V V β β Pg 1 (ContinuousMulEquiv.refl _) where
  isom := by rw [Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  conj g := by rw [Matrix.one_mul, Matrix.mul_one]; rfl
  frame := ⟨rfl, 1, by rw [map_one, mul_one, Matrix.one_mul]; rfl, fun _ _ => map_one _⟩

abbrev princDat (n r t : ℕ) (hr : r ≤ n) (Pg : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    LevDat D.host.E ℂ n :=
  datY n r t 0 hr Pg ∅ (LevelP.triv Pg r ℂ) χ (fun _ => 1) Frm.B

section Equations

variable (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G]
  (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)

def eqSet (P : LevelP L.Pg L.r ℂ) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) :
    Set (MonoidAlgebra ℂ (GfC V)) :=
  {x | ∃ k : GfC V, (k : GA D V) ∈ levG V β (withP L P) ∧
      x = MonoidAlgebra.single k 1 - MonoidAlgebra.single 1 (levChi V β (withP L P) k)} ∪
  {x | ∃ κ : G → GfC V, (∀ g, IsLevelLift V β L (eG g) (κ g)) ∧
      x = ∑ g, MonoidAlgebra.single (κ g) (c g) - MonoidAlgebra.single 1 1} ∪
  {x | ∃ P0 ∈ ok, ∃ k ≤ V.rank, ∃ (α : GfC V) (R : Finset (GfC V)), IsHeckeAt V (pl P0) k α ∧
      Bridge.IsDC ((levG V β (flag1L L)).subgroupOf (GfC V)) α⁻¹ R ∧
      x = ∑ γ ∈ R, MonoidAlgebra.single γ 1 -
        MonoidAlgebra.single 1 ((Sg P0).coeff k / ((-1) ^ k * (q P0 : ℂ) ^ (k * (k - 1) / 2)))}

def IsGoodRep {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) : Prop :=
  ∃ v : W, v ≠ 0 ∧ (∀ k : GfC V, (k : GA D V) ∈ levG V β (flag1L L) → σ k v = v) ∧
    ∃ κ : G → GfC V, (∀ g, IsLevelLift V β L (eG g) (κ g)) ∧ ∑ g, c g • σ (κ g) v = v

end Equations

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def MultEq (R : RealDat D A Ks) : Prop :=
  ∀ (i : Fin D.R.m) (M₀ : DSModel (Yc D 0) (parA (Ptw D) 0)) (j : Matrix (Fin (Wc D i).rank) (Fin (Yc D 0).rank) (EAf D))
    (Φ : GfC (Yc D 0) ≃ₜ* GfC (Wc D i)), IsFinIso (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) R.Pg j Φ →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC (Yc D 0)) W), σ.IsIrreducible →
      GlobalTheory.PRep.IsAdmissible σ →
      IsGoodRep (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (RealDat.eC (A := A) D.what₂.embLL) σ →
      cuspMult R.θ M₀ σ = cuspMult R.θ (R.MW i (sg0 D A)) (σ.comp Φ.symm.toMulEquiv.toMonoidHom)

end GlobalTheory.CuspMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleClearDenominatorStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adele_clear_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ a : Af E, ∃ m : E, m ≠ 0 ∧ algebraMap E (Af E) m * a ∈ hatO c := by
  first | exact @GlobalTheory.CMVal.IntMult.exists_mul_mem_hatO | exact GlobalTheory.CMVal.IntMult.exists_mul_mem_hatO | (intros; apply GlobalTheory.CMVal.IntMult.exists_mul_mem_hatO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorTranslateRatioGlobalUnitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT.Hecke.PullInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_translate_ratio_global_unit : ∀ (X X' : Scheme.{0}) (π : X ⟶ X') (Q₁ Q₂ : LB X'), Q₁.IsLB → Q₂.IsLB → ∀ (w : LB.Iso (Q₁.pull π) (Q₂.pull π)), w.IsGen → ∀ τ : X ⟶ X, τ ≫ π = π → ∃ f : Γ(X, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)), r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k → gm (r ≫ τ) z _ (w.s k) = gm r z ⊤ f * gm r z _ (w.s k) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.PullInj.gen_transl_ratio) | (exact GlobalTheory.UPel.HT.Hecke.PullInj.gen_transl_ratio) | (intros; apply GlobalTheory.UPel.HT.Hecke.PullInj.gen_transl_ratio  <;> assumption)
end

