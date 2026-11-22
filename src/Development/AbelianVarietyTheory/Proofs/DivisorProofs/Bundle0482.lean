import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodNormIntegral
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

noncomputable section

namespace GlobalTheory.CMExtend

section Mult

variable {E : Type} [Field E] [NumberField E]

theorem exists_natMul_isIntegral (x : E) : ∃ m : ℕ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * x) := by
  obtain ⟨y, hy, hi⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ)
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x))
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · rw [h, zsmul_eq_mul] at hi
    simpa using hi
  · rw [h, zsmul_eq_mul] at hi
    have := hi.neg
    simpa using this

theorem exists_natMul_mem_orderC {c : Ideal (OF E)} (hc : c ≠ ⊥) (x : E) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : E) * x ∈ orderC c := by
  obtain ⟨m, hm, hint⟩ := exists_natMul_isIntegral x
  have hk0 : Ideal.absNorm c ≠ 0 := fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨y, hy⟩ : ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = (m : E) * x :=
    ⟨⟨(m : E) * x, (mem_integralClosure_iff ℤ E).2 hint⟩, rfl⟩
  refine ⟨Ideal.absNorm c * m, mul_ne_zero hk0 hm, ?_⟩
  refine mem_orderC.2 ⟨0, algebraMap (OF E) (𝓞 E) ((Ideal.absNorm c : ℕ) : OF E) * y,
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.absNorm_mem c)), ?_⟩
  rw [map_zero, zero_add, map_mul, hy, map_natCast, map_natCast, Nat.cast_mul, mul_assoc]

end Mult

section Ext

variable {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)}
variable {K A : Type} [Field K] [CharZero K] [Ring A] [Algebra K A]

def mulN (hc : c ≠ ⊥) (x : E) : ℕ := Classical.choose (exists_natMul_mem_orderC hc x)

theorem mulN_ne_zero (hc : c ≠ ⊥) (x : E) : mulN hc x ≠ 0 :=
  (Classical.choose_spec (exists_natMul_mem_orderC hc x)).1

theorem mulN_mem (hc : c ≠ ⊥) (x : E) : (mulN hc x : E) * x ∈ orderC c :=
  (Classical.choose_spec (exists_natMul_mem_orderC hc x)).2

variable (K) in

def extFun (hc : c ≠ ⊥) (g : orderC c →+* A) (x : E) : A :=
  ((mulN hc x : K))⁻¹ • g ⟨(mulN hc x : E) * x, mulN_mem hc x⟩

theorem map_natMul (g : orderC c →+* A) (n : ℕ) (z : orderC c) : g ((n : orderC c) * z) = (n : K) • g z := by
  rw [map_mul, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

theorem extFun_eq (hc : c ≠ ⊥) (g : orderC c →+* A) {x : E} {m : ℕ} (hm : m ≠ 0) (h : (m : E) * x ∈ orderC c) :
    extFun K hc g x = ((m : K))⁻¹ • g ⟨(m : E) * x, h⟩ := by
  have hm0 : (m : K) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hn0 : (mulN hc x : K) ≠ 0 := Nat.cast_ne_zero.2 (mulN_ne_zero hc x)
  have key : (m : K) • g ⟨(mulN hc x : E) * x, mulN_mem hc x⟩ = (mulN hc x : K) • g ⟨(m : E) * x, h⟩ := by
    rw [← map_natMul, ← map_natMul]
    congr 1
    apply Subtype.ext
    simp only [Subring.coe_mul, Subring.coe_natCast]
    ring
  calc extFun K hc g x = ((mulN hc x : K))⁻¹ • ((m : K)⁻¹ • ((m : K) • g ⟨(mulN hc x : E) * x, mulN_mem hc x⟩)) := by
        rw [inv_smul_smul₀ hm0]; rfl
    _ = ((mulN hc x : K))⁻¹ • ((m : K)⁻¹ • ((mulN hc x : K) • g ⟨(m : E) * x, h⟩)) := by rw [key]
    _ = ((m : K))⁻¹ • g ⟨(m : E) * x, h⟩ := by
        rw [smul_comm ((m : K)⁻¹) ((mulN hc x : K)), inv_smul_smul₀ hn0]

variable (K) in

def extHom (hc : c ≠ ⊥) (g : orderC c →+* A) : E →+* A where
  toFun := extFun K hc g
  map_one' := by
    rw [extFun_eq hc g one_ne_zero (by simpa using (orderC c).one_mem)]
    simp only [Nat.cast_one, inv_one, one_smul]
    convert g.map_one using 2
    apply Subtype.ext; simp
  map_mul' x y := by
    have hx := mulN_mem hc x
    have hy := mulN_mem hc y
    have hxy : ((mulN hc x * mulN hc y : ℕ) : E) * (x * y) ∈ orderC c := by
      convert mul_mem hx hy using 1; push_cast; ring
    rw [extFun_eq hc g (mul_ne_zero (mulN_ne_zero hc x) (mulN_ne_zero hc y)) hxy]
    have e : (⟨((mulN hc x * mulN hc y : ℕ) : E) * (x * y), hxy⟩ : orderC c) =
        ⟨(mulN hc x : E) * x, hx⟩ * ⟨(mulN hc y : E) * y, hy⟩ := by
      apply Subtype.ext; simp only [Subring.coe_mul]; push_cast; ring
    rw [e, map_mul]
    show _ = (((mulN hc x : K))⁻¹ • g ⟨(mulN hc x : E) * x, hx⟩) * (((mulN hc y : K))⁻¹ • g ⟨(mulN hc y : E) * y, hy⟩)
    rw [smul_mul_smul_comm]
    push_cast
    rw [mul_inv]
  map_zero' := by
    rw [extFun_eq hc g one_ne_zero (by simpa using (orderC c).zero_mem)]
    convert smul_zero _ using 2
    convert g.map_zero using 2
    apply Subtype.ext; simp
  map_add' x y := by
    have hx := mulN_mem hc x
    have hy := mulN_mem hc y
    have hx0 : (mulN hc x : K) ≠ 0 := Nat.cast_ne_zero.2 (mulN_ne_zero hc x)
    have hy0 : (mulN hc y : K) ≠ 0 := Nat.cast_ne_zero.2 (mulN_ne_zero hc y)
    have e : ((mulN hc x * mulN hc y : ℕ) : E) * (x + y) =
        (((mulN hc y : ℕ) : orderC c) * ⟨(mulN hc x : E) * x, hx⟩ + ((mulN hc x : ℕ) : orderC c) * ⟨(mulN hc y : E) * y, hy⟩ :
          orderC c) := by
      simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_natCast]; push_cast; ring
    have hxy : ((mulN hc x * mulN hc y : ℕ) : E) * (x + y) ∈ orderC c := by rw [e]; exact Subtype.property _
    rw [extFun_eq hc g (mul_ne_zero (mulN_ne_zero hc x) (mulN_ne_zero hc y)) hxy]
    have e' : (⟨((mulN hc x * mulN hc y : ℕ) : E) * (x + y), hxy⟩ : orderC c) =
        ((mulN hc y : ℕ) : orderC c) * ⟨(mulN hc x : E) * x, hx⟩ + ((mulN hc x : ℕ) : orderC c) * ⟨(mulN hc y : E) * y, hy⟩ :=
      Subtype.ext e
    rw [e', map_add, map_natMul (K := K), map_natMul (K := K)]
    show _ = ((mulN hc x : K))⁻¹ • g ⟨(mulN hc x : E) * x, hx⟩ + ((mulN hc y : K))⁻¹ • g ⟨(mulN hc y : E) * y, hy⟩
    rw [smul_add, smul_smul, smul_smul]
    congr 2
    · push_cast; field_simp
    · push_cast; field_simp

theorem extHom_apply (hc : c ≠ ⊥) (g : orderC c →+* A) (a : orderC c) : extHom K hc g a = g a := by
  show extFun K hc g a = g a
  rw [extFun_eq hc g one_ne_zero (by simpa using a.2)]
  simp only [Nat.cast_one, inv_one, one_smul]
  congr 1
  apply Subtype.ext; simp

theorem ringHom_ext_orderC (hc : c ≠ ⊥) {B : Type} [Ring B] (f₁ f₂ : E →+* B) (h : ∀ a : orderC c, f₁ a = f₂ a) :
    f₁ = f₂ := by
  ext x
  obtain ⟨n, hn, hnx⟩ := exists_natMul_mem_orderC hc x
  have hnE : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h1 : f₁ ((n : E)⁻¹) * (n : B) = 1 := by
    rw [← map_natCast f₁, ← map_mul, inv_mul_cancel₀ hnE, map_one]
  have h2 : (n : B) * f₂ ((n : E)⁻¹) = 1 := by
    rw [← map_natCast f₂, ← map_mul, mul_inv_cancel₀ hnE, map_one]
  have hinv : f₁ ((n : E)⁻¹) = f₂ ((n : E)⁻¹) := by
    calc f₁ ((n : E)⁻¹) = f₁ ((n : E)⁻¹) * ((n : B) * f₂ ((n : E)⁻¹)) := by rw [h2, mul_one]
      _ = f₂ ((n : E)⁻¹) := by rw [← mul_assoc, h1, one_mul]
  have hx : x = (n : E)⁻¹ * ((n : E) * x) := by rw [← mul_assoc, inv_mul_cancel₀ hnE, one_mul]
  have := h ⟨(n : E) * x, hnx⟩
  simp only at this
  calc f₁ x = f₁ ((n : E)⁻¹ * ((n : E) * x)) := congrArg f₁ hx
    _ = f₂ ((n : E)⁻¹ * ((n : E) * x)) := by rw [map_mul f₁, hinv, this, ← map_mul]
    _ = f₂ x := (congrArg f₂ hx).symm

end Ext

def baseChangeRingHom (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K] (H : Type) [AddCommGroup H] [Module O H] :
    Module.End O H →+* Module.End K (K ⊗[O] H) where
  toFun f := f.baseChange K
  map_one' := LinearMap.baseChange_one O H
  map_mul' f g := LinearMap.baseChange_mul f g
  map_zero' := LinearMap.baseChange_zero
  map_add' f g := LinearMap.baseChange_add f g

theorem exists_unique_extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → (∃! ρE : E →+* Module.End K (K ⊗[O] H), ∀ a : orderC c, ρE a = (ρ a).baseChange K) := by
  intro E _ _ _ c hc l hl O _ _ _ _ K _ _ _ hlm hcard D hD hcl I _ φ hφ H _ _ ρ Fil B hlat heig
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective O K)
  refine ⟨extHom K hc ((baseChangeRingHom O K H).comp ρ), fun a => extHom_apply hc _ a, ?_⟩
  intro f hf
  exact ringHom_ext_orderC hc f _ fun a => by rw [hf a, extHom_apply hc _ a]; rfl

end GlobalTheory.CMExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodProductIntegral
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.Div.eigen_line_bilinear

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}

theorem bar_bar (σ : E →+* K) : bar (bar σ) = σ := by
  ext x
  simp [bar, IsCMField.complexConj_apply_apply]

theorem inK_ne_zero (hfree : Module.Free O H) {h : H} (hh : h ≠ 0) : inK (O := O) K H h ≠ 0 := by
  have hloc : IsLocalizedModule (nonZeroDivisors O) (TensorProduct.mk O K H 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors O) K _).2 (TensorProduct.isBaseChange O H K)
  intro h0
  have h0' : TensorProduct.mk O K H 1 h = 0 := h0
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors O) _).1 h0'
  rw [Submonoid.smul_def] at ht
  exact hh ((smul_eq_zero.1 ht).resolve_left (nonZeroDivisors.ne_zero t.2))

theorem eq_smul_of_line {ρ : orderC c →+* Module.End O H} {τ : E →+* K} (hline : Module.finrank K (eigK ρ τ) = 1)
    {v : K ⊗[O] H} (hv : v ∈ eigK ρ τ) (hv0 : v ≠ 0) {x : K ⊗[O] H} (hx : x ∈ eigK ρ τ) : ∃ a : K, x = a • v := by
  have hne : (⟨v, hv⟩ : eigK ρ τ) ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).1 hline ⟨x, hx⟩
  exact ⟨a, (congrArg Subtype.val ha).symm⟩

theorem lower_apply {ρ : orderC c →+* Module.End O H} {τ : E →+* K} {e f : H} {N : Module.End K (K ⊗[O] H)}
    (hdir : DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ)) (hline : Module.finrank K (eigK ρ τ) = 1)
    (he : inK (O := O) K H e ∈ eigK ρ τ) (he0 : inK (O := O) K H e ≠ 0) (hN : IsLower ρ τ e f N) (x : K ⊗[O] H) :
    ∃ a : K, N x = a • inK (O := O) K H f := by
  have hx : x ∈ ⨆ σ : E →+* K, eigK ρ σ := by
    rw [hdir.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction (fun σ : E →+* K => eigK ρ σ) (motive := fun x => ∃ a : K, N x = a • inK (O := O) K H f) hx
    ?_ ⟨0, by simp⟩ ?_
  · intro σ y hy
    by_cases hσ : σ = τ
    · subst hσ
      obtain ⟨a, rfl⟩ := eq_smul_of_line hline he he0 hy
      exact ⟨a, by rw [map_smul, hN.1]⟩
    · exact ⟨0, by rw [hN.2 σ hσ y hy, zero_smul]⟩
  · rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [map_add, ha, hb, add_smul]⟩

theorem bilin_zero_of_eig {ρ : orderC c →+* Module.End O H}
    (hdir : DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ)) (S : LinearMap.BilinForm K (K ⊗[O] H))
    (h : ∀ σ σ' : E →+* K, ∀ x ∈ eigK ρ σ, ∀ y ∈ eigK ρ σ', S x y = 0) (x y : K ⊗[O] H) : S x y = 0 := by
  have hmem : ∀ z : K ⊗[O] H, z ∈ ⨆ σ : E →+* K, eigK ρ σ := fun z => by
    rw [hdir.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction (fun σ : E →+* K => eigK ρ σ) (motive := fun x => ∀ y, S x y = 0) (hmem x)
    ?_ (fun y => by simp) ?_ y
  · intro σ x hx y
    refine Submodule.iSup_induction (fun σ : E →+* K => eigK ρ σ) (motive := fun y => S x y = 0) (hmem y)
      (fun σ' y hy => h σ σ' x hx y hy) (by simp) ?_
    intro y y' h1 h2
    rw [map_add, h1, h2, add_zero]
  · intro x x' h1 h2 y
    rw [map_add, LinearMap.add_apply, h1, h2, add_zero]

end SlopeTestRemainingChoices

theorem lower_skew_orth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) → (∀ i x y, B.baseChange K (N i x) y + B.baseChange K x (N i y) = 0) ∧ ∀ i j x y, B.baseChange K (N i x) (N j y) = 0 := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ hCM H _ _ ρ Fil B hL hEC e f hG N hN
  obtain ⟨hfree, -, -, hlines, -, -, -, halt, -⟩ := hL
  obtain ⟨hdir, hlat, -, -, horth⟩ := hEC
  have he_mem : ∀ i, inK (O := O) K H (e i) ∈ eigK ρ (φ i) := fun i => by
    have hm : e i ∈ eigLat ρ (φ i) := by rw [(hG i).1]; exact Submodule.mem_span_singleton_self _
    exact hm
  have hf_mem : ∀ i, inK (O := O) K H (f i) ∈ eigK ρ (bar (φ i)) := fun i => by
    have hm : f i ∈ eigLat ρ (bar (φ i)) := by rw [(hG i).2]; exact Submodule.mem_span_singleton_self _
    exact hm
  have he0 : ∀ i, inK (O := O) K H (e i) ≠ 0 := fun i => by
    refine inK_ne_zero hfree fun he => ?_
    obtain ⟨-, ⟨g, hg0, hg⟩, -⟩ := hlat (φ i)
    have hgm : g ∈ O ∙ e i := by rw [← (hG i).1, hg]; exact Submodule.mem_span_singleton_self g
    rw [he, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at hgm
    exact hg0 hgm
  have hlow : ∀ i z, ∃ a : K, N i z = a • inK (O := O) K H (f i) := fun i z =>
    lower_apply hdir (hlines (φ i)) (he_mem i) (he0 i) (hN i) z
  have himg : ∀ i z, N i z ∈ eigK ρ (bar (φ i)) := fun i z => by
    obtain ⟨a, ha⟩ := hlow i z
    rw [ha]; exact Submodule.smul_mem _ a (hf_mem i)
  refine ⟨fun i x y => ?_, fun i j x y => ?_⟩
  · let S : LinearMap.BilinForm K (K ⊗[O] H) :=
      (B.baseChange K).compl₁₂ (N i) LinearMap.id + (B.baseChange K).compl₁₂ LinearMap.id (N i)
    have hS : ∀ x y, S x y = B.baseChange K (N i x) y + B.baseChange K x (N i y) := fun x y => rfl
    rw [← hS]
    refine bilin_zero_of_eig hdir S (fun σ σ' x hx y hy => ?_) x y
    rw [hS]
    have t1 : σ' ≠ φ i → B.baseChange K (N i x) y = 0 := fun h =>
      horth (bar (φ i)) σ' (by rwa [bar_bar]) _ (himg i x) y hy
    have t2 : σ ≠ φ i → B.baseChange K x (N i y) = 0 := fun h => by
      refine horth σ (bar (φ i)) (fun h' => h ?_) x hx _ (himg i y)
      have := congrArg bar h'
      rwa [bar_bar, bar_bar, eq_comm] at this
    by_cases h1 : σ = φ i
    · by_cases h2 : σ' = φ i
      · subst h1
        rw [h2] at hy
        obtain ⟨a, rfl⟩ := eq_smul_of_line (hlines _) (he_mem i) (he0 i) hx
        obtain ⟨b, rfl⟩ := eq_smul_of_line (hlines _) (he_mem i) (he0 i) hy
        have key : B.baseChange K (inK (O := O) K H (f i)) (inK (O := O) K H (e i)) +
            B.baseChange K (inK (O := O) K H (e i)) (inK (O := O) K H (f i)) = 0 := by
          simp only [inK, TensorProduct.mk_apply, LinearMap.BilinForm.baseChange_tmul, mul_one]
          rw [← add_smul, ← LinearMap.IsAlt.neg halt (e i) (f i), neg_add_cancel, zero_smul]
        simp only [map_smul, (hN i).1, LinearMap.smul_apply, smul_eq_mul]
        linear_combination (a * b) * key
      · rw [t1 h2, (hN i).2 σ' h2 y hy, map_zero, add_zero]
    · rw [t2 h1, (hN i).2 σ h1 x hx, map_zero, LinearMap.zero_apply, add_zero]
  · obtain ⟨a, ha⟩ := hlow i x
    obtain ⟨b, hb⟩ := hlow j y
    rw [ha, hb]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      have : B.baseChange K (inK (O := O) K H (f i)) (inK (O := O) K H (f i)) = 0 := by
        simp only [inK, TensorProduct.mk_apply, LinearMap.BilinForm.baseChange_tmul, halt (f i), zero_smul]
      rw [this, mul_zero, mul_zero]
    · have hne : bar (φ j) ≠ bar (bar (φ i)) := by
        rw [bar_bar]
        intro h
        obtain ⟨k, -, hk⟩ := hCM (φ i)
        exact hij ((hk i (Or.inl rfl)).trans (hk j (Or.inr h.symm)).symm)
      rw [horth (bar (φ i)) (bar (φ j)) hne _ (hf_mem i) _ (hf_mem j), mul_zero, mul_zero]

end GlobalTheory.Div.eigen_line_bilinear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodValuationBound
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory

theorem inK_injective_of_free {O : Type} [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K]
    [IsFractionRing O K] (H : Type) [AddCommGroup H] [Module O H] [Module.Free O H] :
    Function.Injective (inK K H : H →ₗ[O] K ⊗[O] H) := by
  have h1 : Function.Injective ((Algebra.linearMap O K).rTensor H) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective O K)
  intro x y hxy
  apply (TensorProduct.lid O H).symm.injective
  apply h1
  simpa [inK] using hxy

theorem existsUnique_endo_line {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    (W : ι → Submodule K V) (hW : DirectSum.IsInternal W) (τ : ι) (v w : V) (hv : v ∈ W τ) (hv0 : v ≠ 0)
    (h1 : Module.finrank K (W τ) = 1) :
    ∃! N : Module.End K V, N v = w ∧ ∀ σ, σ ≠ τ → ∀ x ∈ W σ, N x = 0 := by
  have hspan : ∀ x ∈ W τ, ∃ c : K, c • v = x := by
    intro x hx
    have hu : (⟨v, hv⟩ : W τ) ≠ 0 := by simpa using hv0
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : W τ) hu).1 h1 ⟨x, hx⟩
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩
  have hind := hW.submodule_iSupIndep
  have htop := hW.submodule_iSup_eq_top
  set C : Submodule K V := ⨆ j, ⨆ (_ : j ≠ τ), W j with hC
  have hmemC : ∀ σ, σ ≠ τ → ∀ x ∈ W σ, x ∈ C := fun σ hσ x hx =>
    (le_iSup₂_of_le σ hσ le_rfl : W σ ≤ C) hx
  have hc : IsCompl (W τ) C := by
    refine ⟨hind τ, codisjoint_iff.2 (eq_top_iff.2 ?_)⟩
    rw [← htop]
    refine iSup_le fun j => ?_
    by_cases hj : j = τ
    · subst hj; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le j hj le_rfl)
  have huniq : ∀ N₁ N₂ : Module.End K V, (N₁ v = w ∧ ∀ σ, σ ≠ τ → ∀ x ∈ W σ, N₁ x = 0) →
      (N₂ v = w ∧ ∀ σ, σ ≠ τ → ∀ x ∈ W σ, N₂ x = 0) → N₁ = N₂ := by
    intro N₁ N₂ h₁ h₂
    have hle : ∀ σ, W σ ≤ LinearMap.eqLocus N₁ N₂ := by
      intro σ x hx
      show N₁ x = N₂ x
      by_cases hσ : σ = τ
      · subst hσ
        obtain ⟨c, rfl⟩ := hspan x hx
        rw [map_smul, map_smul, h₁.1, h₂.1]
      · rw [h₁.2 σ hσ x hx, h₂.2 σ hσ x hx]
    have : (⊤ : Submodule K V) ≤ LinearMap.eqLocus N₁ N₂ := htop ▸ iSup_le hle
    exact LinearMap.ext fun x => this (Submodule.mem_top)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.toSpanSingleton K V v)
    (LinearMap.ker_toSpanSingleton K hv0)
  let p := Submodule.linearProjOfIsCompl (W τ) C hc
  have hN0 : ((LinearMap.toSpanSingleton K V w) ∘ₗ g ∘ₗ (W τ).subtype ∘ₗ p) v = w ∧
      ∀ σ, σ ≠ τ → ∀ x ∈ W σ, ((LinearMap.toSpanSingleton K V w) ∘ₗ g ∘ₗ (W τ).subtype ∘ₗ p) x = 0 := by
    constructor
    · have hpv : p v = ⟨v, hv⟩ := Submodule.linearProjOfIsCompl_apply_left hc ⟨v, hv⟩
      have hgv : g v = 1 := by simpa using LinearMap.congr_fun hg 1
      simp [hpv, hgv]
    · intro σ hσ x hx
      have : p x = 0 := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc).2 (hmemC σ hσ x hx)
      simp [this]
  exact ⟨_, hN0, fun N hN => huniq _ _ hN hN0⟩
end GlobalTheory

namespace GlobalTheory

theorem lowerOp_existsUnique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ i, ∃! N, IsLower ρ (φ i) (e i) (f i) N := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D _ _ I _ φ _ H _ _ ρ Fil B hLat hEig e f hGen i
  haveI : Module.Free O H := hLat.1
  have hmem : e i ∈ eigLat ρ (φ i) := by rw [(hGen i).1]; exact Submodule.mem_span_singleton_self _
  have hv : inK (O := O) K H (e i) ∈ eigK ρ (φ i) := hmem
  have he0 : e i ≠ 0 := by
    obtain ⟨g, hg0, hgs⟩ := (hEig.2.1 (φ i)).2.1
    intro h
    apply hg0
    have : g ∈ eigLat ρ (φ i) := hgs ▸ Submodule.mem_span_singleton_self g
    rw [(hGen i).1, h] at this
    simpa using this
  have hv0 : inK (O := O) K H (e i) ≠ 0 := fun h => he0 (inK_injective_of_free (O := O) K H (h.trans (map_zero (inK (O := O) K H)).symm))
  have key := existsUnique_endo_line (eigK ρ) hEig.1 (φ i) (inK K H (e i)) (inK K H (f i)) hv hv0 (hLat.2.2.2.1 (φ i))
  unfold IsLower
  exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassProperties
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SectionClass

variable (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})

theorem exists_cocycle (s : Sec F X) :
    ∃ α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0, ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s := by
  have hz : Sec.map ((res R F).d 0 1) (Sec.map (resι R F) s) = 0 :=
    ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).1 _).2 ⟨s, rfl⟩
  obtain ⟨α, h0, -⟩ := (GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (-1) 0 1 (by norm_num) (by norm_num)).1 _ hz
  refine ⟨α, (h0 X (𝟙 X)).trans ?_⟩
  simp [Sec.res]

theorem mk_eq_iff (α β : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0) :
    CohomologyClass.mk α = CohomologyClass.mk β ↔
      ev α.1 0 0 (by simp) X (𝟙 X) = ev β.1 0 0 (by simp) X (𝟙 X) := by
  have h2 := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (-1) 0 1 (by norm_num) (by norm_num)).2 (α - β)).2
  have hsub : ev (α - β).1 0 0 (by simp) X (𝟙 X) = ev α.1 0 0 (by simp) X (𝟙 X) - ev β.1 0 0 (by simp) X (𝟙 X) := by
    have := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).1 α.1 β.1 0 0 (by simp) X (𝟙 X)).2.1
    simpa using this
  have hss : Subsingleton (Sec ((res R F).X (-1)) X) := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).2.2.2 (-1) (by norm_num)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, h2, hsub]
  have hz : Sec.map ((res R F).d (-1) 0) (0 : Sec ((res R F).X (-1)) X) = 0 := map_zero _
  constructor
  · rintro ⟨y, hy⟩
    have hy' : (0 : Sec ((res R F).X 0) X) = ev α.1 0 0 (by simp) X (𝟙 X) - ev β.1 0 0 (by simp) X (𝟙 X) := by
      rw [← hz, ← Subsingleton.elim y 0]; exact hy
    exact (sub_eq_zero.1 hy'.symm)
  · intro h
    refine ⟨0, ?_⟩
    rw [hz, h, sub_self]

theorem secClass_spec (s : Sec F X) : ∃ α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0,
    CohomologyClass.mk α = secClass F s ∧ ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s := by
  obtain ⟨α, h⟩ := exists_cocycle R F X s
  exact pick_spec (P := fun c => ∃ α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0,
    CohomologyClass.mk α = c ∧ ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s) ⟨_, α, rfl, h⟩

theorem spec_iff (s : Sec F X) (α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0) :
    ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s ↔ CohomologyClass.mk α = secClass F s := by
  obtain ⟨α₀, h1, h2⟩ := secClass_spec R F X s
  rw [← h1, mk_eq_iff, h2]

end GlobalTheory.EtC.SectionClass

open GlobalTheory.EtC.SectionClass in

theorem GlobalTheory.EtC.secClass_props : ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}), (∀ (s : Sec F X) (α : Cocycle ((chains R).obj (sch.obj X)) (res R F) 0), ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s ↔ CohomologyClass.mk α = secClass F s) ∧ Function.Bijective (secClass F (X := X)) ∧ (∀ s t : Sec F X, secClass F (s + t) = secClass F s + secClass F t) ∧ (∀ {Y : Scheme.{0}} (f : Y ⟶ X) (s : Sec F X), pull R (sch.map f) F 0 (secClass F s) = secClass F (Sec.res f s)) ∧ ∀ {G : Shv R} (φ : F ⟶ G) (s : Sec F X), HK.post R _ φ 0 (secClass F s) = secClass G (Sec.map φ s) := by
  intro R _ F X
  refine ⟨spec_iff R F X, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro s t hst
    obtain ⟨α, h1, h2⟩ := secClass_spec R F X s
    have h3 := (spec_iff R F X t α).2 (h1.trans hst)
    exact (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).2.1 (h2.symm.trans h3)
  · intro c
    obtain ⟨α, rfl⟩ := c.mk_surjective
    have hd := ((GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X (res R F) (-1) 0 1 (by norm_num) (by norm_num)).2 α).1
    obtain ⟨a, ha⟩ := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F X).1 _).1 hd
    exact ⟨a, ((spec_iff R F X a α).1 ha.symm).symm⟩
  · intro s t
    obtain ⟨α, h1, h2⟩ := secClass_spec R F X s
    obtain ⟨β, h3, h4⟩ := secClass_spec R F X t
    rw [← h1, ← h3, ← CohomologyClass.mk_add]
    symm
    refine (spec_iff R F X (s + t) (α + β)).1 ?_
    have := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).1 α.1 β.1 0 0 (by simp) X (𝟙 X)).1
    simp only [Cocycle.coe_add] at this ⊢
    rw [this, h2, h4]
    exact (map_add ((resι R F).hom.app (op X)).hom s t).symm
  · intro Y f s
    obtain ⟨α, h1, h2⟩ := secClass_spec R F X s
    rw [← h1]
    refine (spec_iff R F Y _ _).1 ?_
    have e4 := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).2.2.2.1 (sch.map f) α.1 0 0 (by simp) Y (𝟙 Y)
    have e2 := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).2.1 α.1 0 0 (by simp) Y X f (𝟙 X)
    have hx1 : Sx.map (p := 0) (sch.map f) (𝟙 Y : Sx (sch.obj Y) 0 Y) = (show Sx (sch.obj X) 0 Y from f) := by
      simp [Sx.map, sch]
      exact Category.id_comp f
    have hx2 : Sx.res f (𝟙 X : Sx (sch.obj X) 0 X) = (show Sx (sch.obj X) 0 Y from f) := by
      simp [Sx.res, sch]
      exact Category.comp_id f
    change ev ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add 0)) 0 0 _ Y (𝟙 Y) = _
    rw [e4, hx1, ← hx2, ← e2, h2]
    exact (NatTrans.naturality_apply (resι R F).hom f.op s).symm
  · intro G φ s
    obtain ⟨α, h1, h2⟩ := secClass_spec R F X s
    rw [← h1]
    refine (spec_iff R G X _ _).1 ?_
    have e5 := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := res R F) (n := 0)).2.2.2.2 (resMap R φ) α.1 0 0 (by simp) X (𝟙 X)
    have hc := ((GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.2.2.2.2.2.2 G φ).2
    change ev (α.1.comp (Cochain.ofHom (resMap R φ)) (add_zero 0)) 0 0 _ X (𝟙 X) = _
    rw [e5, h2]
    change ((resι R F ≫ (resMap R φ).f 0).hom.app (op X)).hom s = _
    rw [hc]
    rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceDescentLocalEquivalenceStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpace_descent_local_equivalence : ∀ (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) [Cov.IsStableUnderComposition] (Φ Φ' : T ⥤ Spcᵒᵖ) (α : Φ' ⟶ Φ), Refines Cov (fun U X a => Hyp R Φ a ∧ Hyp R Φ' a) → (∀ (U : T) (n : ℤ) (x : H R (Φ.obj U).unop F n), ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : H R (Φ'.obj V).unop F n, pull R (α.app V).unop F n y = pull R (Φ.map g).unop F n x) → (∀ (U : T) (n : ℤ) (y : H R (Φ'.obj U).unop F n), pull R (α.app U).unop F n y = 0 → ∃ (V : T) (g : U ⟶ V), Cov g ∧ pull R (Φ'.map g).unop F n y = 0) → ∀ U, Eqv R (α.app U).unop F := by
  first | (exact @GlobalTheory.EtC.Descent.main) | (exact GlobalTheory.EtC.Descent.main) | (intros; apply GlobalTheory.EtC.Descent.main <;> assumption)
end

