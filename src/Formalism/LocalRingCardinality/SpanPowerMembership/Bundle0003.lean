import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocB
import Mathlib
import Formalism.CyclotomicNorms.Bundle0002
import Formalism.CyclotomicNorms.NonsquarefreeBounds.IrreducibilityOfRestriction

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.NDLocC
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.LB

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions.Loc

variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] [CharZero Ω]

omit hl in
variable (E Ω) in
include E in
theorem isAlgClosureQ : IsAlgClosure ℚ Ω := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  exact ⟨inferInstance, Algebra.IsAlgebraic.trans ℚ E Ω⟩

variable [IsAlgClosure ℚ Ω] (j : Ω →+* PadicAlgCl l)

omit [IsAlgClosure E Ω] [Algebra E Ω] [NumberField E] [Field E] in

def resQ (σ : GQ l) : Ω ≃ₐ[ℚ] Ω :=
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  haveI : IsScalarTower ℚ Ω (PadicAlgCl l) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  AlgHom.restrictNormal' ((σ.restrictScalars ℚ : PadicAlgCl l ≃ₐ[ℚ] PadicAlgCl l) :
    PadicAlgCl l →ₐ[ℚ] PadicAlgCl l) Ω

omit [IsAlgClosure E Ω] [Algebra E Ω] [NumberField E] [Field E] in
theorem j_resQ (σ : GQ l) (x : Ω) : j (resQ j σ x) = σ (j x) := by
  letI : Algebra Ω (PadicAlgCl l) := j.toAlgebra
  haveI : IsScalarTower ℚ Ω (PadicAlgCl l) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  exact AlgHom.restrictNormal_commutes _ Ω x

def resE (σ : GQ l) (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) : G E Ω :=
  AlgEquiv.ofRingEquiv (f := (resQ j σ).toRingEquiv) fun x => j.injective (by
    show j (resQ j σ (algebraMap E Ω x)) = _
    rw [j_resQ]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ (jE_mem j x))

theorem j_resE (σ : GQ l) (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) (x : Ω) :
    j (resE j σ hσ x) = σ (j x) := j_resQ j σ x

variable {j} {A : ValuationSubring Ω} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)

include hj in
theorem resE_mem (σ : GQ l) (hσ : σ ∈ (KwF (E := E) j).fixingSubgroup) :
    resE j σ hσ ∈ Dec (F := E) A := by
  have hiso : ∀ y : PadicAlgCl l, ‖σ y‖ = ‖y‖ := fun y => by
    rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
    first
      | (simp only [spectralNorm, minpoly.algEquiv_eq]; done)
      | exact (spectralNorm.aut_isom σ y).symm
      | (unfold spectralNorm; rw [minpoly.algEquiv_eq])
      | (unfold spectralNorm; congr 1; exact minpoly.algEquiv_eq σ y)
  have key : ∀ x, resE j σ hσ x ∈ A ↔ x ∈ A := fun x => by
    rw [hj, hj, j_resE, hiso]
  show resE j σ hσ ∈ MulAction.stabilizer _ A
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← key,
    ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

def rHom : ↥(KwF (E := E) j).fixingSubgroup →* ↥(Dec (F := E) A) where
  toFun σ := ⟨resE j σ.1 σ.2, resE_mem hj σ.1 σ.2⟩
  map_one' := Subtype.ext (AlgEquiv.ext fun x => j.injective
    ((j_resE j _ (1 : ↥(KwF (E := E) j).fixingSubgroup).2 x).trans rfl))
  map_mul' σ τ := Subtype.ext (AlgEquiv.ext fun x => j.injective ((j_resE j _ (σ * τ).2 x).trans
    ((congrArg (σ : GQ l) (j_resE j _ τ.2 x)).symm.trans (j_resE j _ σ.2 _).symm)))

theorem j_rHom (σ : ↥(KwF (E := E) j).fixingSubgroup) (x : Ω) :
    j ((rHom hj σ : G E Ω) x) = (σ : GQ l) (j x) := j_resE j σ.1 σ.2 x

theorem continuous_aut (σ : GQ l) : Continuous σ := by
  have hiso : ∀ y : PadicAlgCl l, ‖σ y‖ = ‖y‖ := fun y => by
    rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
    first
      | (simp only [spectralNorm, minpoly.algEquiv_eq]; done)
      | exact (spectralNorm.aut_isom σ y).symm
      | (unfold spectralNorm; rw [minpoly.algEquiv_eq])
      | (unfold spectralNorm; congr 1; exact minpoly.algEquiv_eq σ y)
  exact (AddMonoidHomClass.isometry_of_norm σ hiso).continuous

theorem rHom_injective : Function.Injective (rHom (E := E) hj) := by
  intro σ τ h
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hd := denseRange_emb l j
  have heq : ((σ : GQ l) : PadicAlgCl l → PadicAlgCl l) = (τ : GQ l) :=
    hd.equalizer (continuous_aut _) (continuous_aut _) (funext fun x => by
      simp only [Function.comp_apply]
      rw [← j_rHom hj σ x, ← j_rHom hj τ x, h])
  exact Subtype.ext (AlgEquiv.ext (congrFun heq))

include hj in
theorem norm_le_pow (g : G E Ω) (hg : g ∈ Dec (F := E) A) (z : Ω) (n : ℕ)
    (h : ‖j z‖ ≤ ‖((l : ℕ) : PadicAlgCl l)‖ ^ n) : ‖j (g z)‖ ≤ ‖((l : ℕ) : PadicAlgCl l)‖ ^ n := by
  have hl0 : ((l : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hl.out.ne_zero
  have hlpos : 0 < ‖((l : ℕ) : PadicAlgCl l)‖ := by
    rw [norm_pos_iff, ← map_natCast j]
    exact (map_ne_zero j).mpr hl0
  have h1 : z / ((l : ℕ) : Ω) ^ n ∈ A := by
    rw [hj, map_div₀, map_pow, map_natCast, norm_div, norm_pow]
    exact div_le_one_of_le₀ h (by positivity)
  have hg' : g • A = A := MulAction.mem_stabilizer_iff.mp hg
  have h2 : g (z / ((l : ℕ) : Ω) ^ n) ∈ A := by
    rw [← hg', ← AlgEquiv.smul_def]
    exact ValuationSubring.smul_mem_pointwise_smul g _ A h1
  rw [map_div₀, map_pow, map_natCast, hj, map_div₀, map_pow, map_natCast, norm_div, norm_pow] at h2
  exact (div_le_one (by positivity)).mp h2

include hj in

theorem exists_ext (g : G E Ω) (hg : g ∈ Dec (F := E) A) :
    ∃ σ : GQ l, ∀ x, σ (j x) = j (g x) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  let iC : Ω →+* ℂ_[l] := (algebraMap (PadicAlgCl l) ℂ_[l]).comp j
  letI : PseudoMetricSpace Ω := PseudoMetricSpace.induced iC inferInstance
  have ue : IsUniformInducing iC := ⟨rfl⟩
  have dr : DenseRange iC :=
    (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)).comp (denseRange_emb l j)
      (UniformSpace.Completion.continuous_coe _)
  let f : Ω →+* ℂ_[l] := iC.comp (g : Ω →+* Ω)
  have hn : ∀ z : Ω, ‖iC z‖ = ‖j z‖ := fun z => PadicComplex.norm_extends l (j z)
  have hl1 : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
    have h1 : ‖((l : ℕ) : PadicAlgCl l)‖ = ‖((l : ℕ) : ℚ_[l])‖ := by
      rw [← PadicAlgCl.norm_extends, map_natCast]
    rw [h1]
    exact Padic.norm_p_lt_one
  have hf : UniformContinuous f := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    obtain ⟨n, hn'⟩ := exists_pow_lt_of_lt_one hε hl1
    refine ⟨‖((l : ℕ) : PadicAlgCl l)‖ ^ n,
      pow_pos (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.out.ne_zero)) n, fun {a b} hab => ?_⟩
    have h1 : dist a b = ‖j (a - b)‖ := by
      show dist (iC a) (iC b) = _
      rw [dist_eq_norm, ← map_sub, hn]
    have h2 : dist (f a) (f b) = ‖j (g (a - b))‖ := by
      rw [dist_eq_norm, ← map_sub]
      exact hn _
    rw [h2]
    rw [h1] at hab
    exact lt_of_le_of_lt (norm_le_pow hj g hg _ n hab.le) hn'
  let gh : ℂ_[l] →+* ℂ_[l] := IsDenseInducing.extendRingHom ue dr hf
  have hgh : ∀ x, gh (iC x) = f x := fun x => (ue.isDenseInducing dr).extend_eq hf.continuous x
  have hcont : Continuous gh := (uniformContinuous_uniformly_extend ue dr hf).continuous
  have hQ : ∀ x : ℚ_[l], gh (algebraMap ℚ_[l] ℂ_[l] x) = algebraMap ℚ_[l] ℂ_[l] x := by
    have hc : Continuous (algebraMap ℚ_[l] ℂ_[l]) := continuous_algebraMap ℚ_[l] ℂ_[l]
    have e := (Padic.denseRange_ratCast l).equalizer (hcont.comp hc) hc (funext fun q => by
      show gh (algebraMap ℚ_[l] ℂ_[l] (q : ℚ_[l])) = algebraMap ℚ_[l] ℂ_[l] (q : ℚ_[l])
      rw [map_ratCast, map_ratCast])
    exact fun x => congrFun e x
  let gA : ℂ_[l] →ₐ[ℚ_[l]] ℂ_[l] := { gh with commutes' := hQ }
  refine ⟨gA.restrictNormal' (PadicAlgCl l), fun x => ?_⟩
  have h3 := AlgHom.restrictNormal_commutes gA (PadicAlgCl l) (j x)
  exact (algebraMap (PadicAlgCl l) ℂ_[l]).injective (h3.trans (hgh x))

theorem rHom_surjective : Function.Surjective (rHom (E := E) hj) := by
  rintro ⟨g, hg⟩
  obtain ⟨σ, hσ⟩ := exists_ext hj g hg
  have hfix : ∀ y ∈ Set.range fun i => jE (E := E) j (Module.finBasis ℚ E i), σ y = y := by
    rintro _ ⟨i, rfl⟩
    simp only [jE, RingHom.comp_apply]
    rw [hσ, AlgEquiv.commutes]
  have hmem : σ ∈ (KwF (E := E) j).fixingSubgroup := by
    have hz : Subgroup.zpowers σ ≤ (KwF (E := E) j).fixingSubgroup := by
      rw [← IntermediateField.le_iff_le]
      unfold KwF
      rw [IntermediateField.adjoin_le_iff]
      intro y hy
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      have hst : Subgroup.zpowers σ ≤ MulAction.stabilizer (GQ l) y := by
        rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
        exact hfix y hy
      have h2 := hst hτ
      rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at h2
    exact hz (Subgroup.mem_zpowers σ)
  refine ⟨⟨σ, hmem⟩, Subtype.ext (AlgEquiv.ext fun x => j.injective ?_)⟩
  rw [j_rHom]
  exact hσ x

end Formalism.BasicNotions.Examples₂.LB
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeA
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Polynomial Formalism.CyclotomicNorms

theorem pow_primeToPart {M : Type*} [Monoid M] {ℓ : ℕ} (hℓ : ℓ.Prime) (x : M) (hx : IsOfFinOrder x) :
    primeToPart ℓ x ^ (ℓ ^ (orderOf x).factorization ℓ) = x ^ (ℓ ^ (orderOf x).factorization ℓ) := by
  set n := orderOf x with hn
  have hn0 : n ≠ 0 := (orderOf_pos_iff.mpr hx).ne'
  set a := n.factorization ℓ
  set m := n / ℓ ^ a with hm
  have hnm : ℓ ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n ℓ
  have hc : Nat.Coprime (ℓ ^ a) m := (Nat.coprime_ordCompl hℓ hn0).pow_left a
  set u := (((ℓ ^ a : ℕ) : ZMod m)⁻¹).val
  have h1 : ((ℓ ^ a * u : ℕ) : ZMod m) = 1 := by
    have hm0 : NeZero m := ⟨fun h => hn0 (by rw [← hnm, h, mul_zero])⟩
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one _ hc
  have h2 : ℓ ^ a * u ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff, h1, Nat.cast_one]
  unfold primeToPart
  rw [← pow_mul]
  have h3 : ℓ ^ a * u * ℓ ^ a ≡ ℓ ^ a [MOD n] := by
    have := h2.mul_left' (ℓ ^ a)
    rw [mul_one, hnm] at this
    rwa [mul_comm (ℓ ^ a * u) (ℓ ^ a)]
  rw [← pow_mod_orderOf x (ℓ ^ a * u * ℓ ^ a), ← pow_mod_orderOf x (ℓ ^ a)]
  exact congrArg _ h3

theorem exists_pow_eq {M : Type*} [Monoid M] {ℓ : ℕ} (hℓ : ℓ.Prime) (x y : M) (hx : IsOfFinOrder x)
    (hy : IsOfFinOrder y) (h : primeToPart ℓ x = primeToPart ℓ y) : ∃ c : ℕ, x ^ ℓ ^ c = y ^ ℓ ^ c := by
  refine ⟨(orderOf x).factorization ℓ + (orderOf y).factorization ℓ, ?_⟩
  have h1 := pow_primeToPart hℓ x hx
  have h2 := pow_primeToPart hℓ y hy
  rw [pow_add, pow_mul, ← h1, h, ← pow_mul, mul_comm, pow_mul, h2, ← pow_mul]

theorem exc_of_dvd {g d e ℓ c : ℕ} (hg : 2 ≤ g) (hℓ : ℓ.Prime) (hd : 1 ≤ d) (he : 2 * Nat.gcd d e ≤ d)
    (h : g ^ d - 1 ∣ ℓ ^ c * (g ^ e - 1)) : Exc g d ℓ := by
  refine ⟨hℓ, ?_⟩
  set G := g ^ d with hG
  have hG3 : 3 ≤ G := by
    have h2 : 2 ≤ d := by
      have : 1 ≤ Nat.gcd d e := Nat.gcd_pos_of_pos_left e hd
      omega
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ g ^ 2 := Nat.pow_le_pow_left hg 2
      _ ≤ g ^ d := Nat.pow_le_pow_right (by omega) h2
  have hn0 : G - 1 ≠ 0 := by omega
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set v := padicValNat ℓ (G - 1) with hv
  have hfac : (G - 1).factorization ℓ = v := Nat.factorization_def _ hℓ
  set B := (G - 1) / ℓ ^ v with hB
  have hAB : ℓ ^ v * B = G - 1 := by
    have := Nat.ordProj_mul_ordCompl_eq_self (G - 1) ℓ
    rwa [hfac] at this
  have hcop : Nat.Coprime ℓ B := by
    have := Nat.coprime_ordCompl hℓ hn0
    rwa [hfac] at this
  have hB1 : B ∣ g ^ e - 1 :=
    (Nat.Coprime.pow_left c hcop).symm.dvd_of_dvd_mul_left ((Dvd.intro_left _ hAB).trans h)
  have hB2 : B ∣ g ^ Nat.gcd d e - 1 := by
    rw [← Nat.pow_sub_one_gcd_pow_sub_one]
    exact Nat.dvd_gcd (Dvd.intro_left _ hAB) hB1
  set s := Nat.gcd d e
  have hs1 : 1 ≤ s := Nat.gcd_pos_of_pos_left e hd
  have hgs : 2 ≤ g ^ s := le_trans hg (Nat.le_self_pow (by omega) g)
  have hBle : B ≤ g ^ s - 1 := Nat.le_of_dvd (by omega) hB2
  have hBsq : B * B ≤ G - 1 := by
    have h1 : g ^ s * g ^ s ≤ G := by
      rw [← pow_add, hG]; exact Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : B * B ≤ (g ^ s - 1) * (g ^ s - 1) := Nat.mul_le_mul hBle hBle
    have h3 : (g ^ s - 1) * (g ^ s - 1) + 1 ≤ g ^ s * g ^ s := by
      obtain ⟨t, ht⟩ : ∃ t, g ^ s = t + 2 := ⟨g ^ s - 2, by omega⟩
      rw [ht]; simp only [show t + 2 - 1 = t + 1 by omega]; nlinarith
    omega
  set A := ℓ ^ v
  have hA2 : G - 1 ≤ A * A := by
    have h1 : (A * A) * (B * B) = (G - 1) * (G - 1) := by rw [← hAB]; ring
    by_contra hlt
    push Not at hlt
    have hBpos : 0 < B * B := by
      rcases Nat.eq_zero_or_pos (B * B) with h0 | h0
      · rw [h0, mul_zero] at h1
        have : 0 < (G - 1) * (G - 1) := Nat.mul_pos (by omega) (by omega)
        omega
      · exact h0
    have : (A * A) * (B * B) < (G - 1) * (G - 1) :=
      calc (A * A) * (B * B) < (G - 1) * (B * B) := Nat.mul_lt_mul_of_pos_right hlt hBpos
        _ ≤ (G - 1) * (G - 1) := Nat.mul_le_mul_left _ hBsq
    omega
  have hA4 : ℓ ^ (4 * v) = (A * A) * (A * A) := by
    show ℓ ^ (4 * v) = (ℓ ^ v * ℓ ^ v) * (ℓ ^ v * ℓ ^ v)
    rw [← pow_add, ← pow_add]; congr 1; ring
  rw [hA4]
  have h5 : (G - 1) * (G - 1) ≤ (A * A) * (A * A) := Nat.mul_le_mul hA2 hA2
  have h6 : G < (G - 1) * (G - 1) := by
    obtain ⟨t, ht⟩ : ∃ t, G = t + 3 := ⟨G - 3, by omega⟩
    rw [ht]; simp only [show t + 3 - 1 = t + 2 by omega]; nlinarith
  omega

end Formalism.BasicNotions.Examples₂.NZ
end
end

