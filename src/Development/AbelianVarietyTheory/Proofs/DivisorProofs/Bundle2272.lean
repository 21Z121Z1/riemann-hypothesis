import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelRefinementGenerating
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2232
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCycAwayHomComplex
section
open GlobalTheory.SiegelTor Polynomial

namespace GlobalTheory.SiegelTor

theorem isPrimitiveRoot_zetaAway {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (zetaAway N) N :=
  IsPrimitiveRoot.of_map_of_injective (f := (cycAway N).subtype) (Complex.isPrimitiveRoot_exp N hN) Subtype.val_injective

theorem cycAway_hom_ext {N : ℕ} (hN : N ≠ 0) {R : Type*} [CommRing R] {β β' : cycAway N →+* R}
    (h : β (zetaAway N) = β' (zetaAway N)) : β = β' := by
  ext ⟨x, hx⟩
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact h
    · have e : (N : cycAway N) * ⟨(N : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ = 1 :=
        Subtype.ext (by simpa using mul_inv_cancel₀ hN')
      have e₁ := congrArg β e
      have e₂ := congrArg β' e
      rw [map_mul, map_natCast, map_one] at e₁ e₂
      exact left_inv_eq_right_inv (by rw [mul_comm]; exact e₁) e₂
  | zero => exact (map_zero β).trans (map_zero β').symm
  | one => exact (map_one β).trans (map_one β').symm
  | add x y hx hy ihx ihy =>
    exact (map_add β ⟨x, hx⟩ ⟨y, hy⟩).trans ((congrArg₂ _ ihx ihy).trans (map_add β' ⟨x, hx⟩ ⟨y, hy⟩).symm)
  | neg x hx ih => exact (map_neg β ⟨x, hx⟩).trans ((congrArg _ ih).trans (map_neg β' ⟨x, hx⟩).symm)
  | mul x y hx hy ihx ihy =>
    exact (map_mul β ⟨x, hx⟩ ⟨y, hy⟩).trans ((congrArg₂ _ ihx ihy).trans (map_mul β' ⟨x, hx⟩ ⟨y, hy⟩).symm)

theorem exists_cycAway_hom_complex {N : ℕ} (hN : N ≠ 0) {μ : ℂ} (hμ : IsPrimitiveRoot μ N) :
    ∃ f : cycAway N →+* ℂ, f (zetaAway N) = μ := by
  have hp := Nat.pos_of_ne_zero hN
  have hz : IsPrimitiveRoot (zetaAway N : ℂ) N := Complex.isPrimitiveRoot_exp N hN
  have hi : IsIntegral ℚ (zetaAway N : ℂ) := (hz.isIntegral hp).tower_top
  let K := IntermediateField.adjoin ℚ {(zetaAway N : ℂ)}
  have hle : cycAway N ≤ K.toSubfield.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (rfl | rfl)
    · exact IntermediateField.mem_adjoin_simple_self ℚ _
    · exact K.inv_mem (natCast_mem K N)
  have hr : μ ∈ (minpoly ℚ (zetaAway N : ℂ)).aroots ℂ := by
    rw [← cyclotomic_eq_minpoly_rat hz hp, mem_aroots]
    refine ⟨cyclotomic_ne_zero N ℚ, ?_⟩
    rw [cyclotomic_eq_minpoly_rat hμ hp]
    exact minpoly.aeval ℚ μ
  let g : K →ₐ[ℚ] ℂ := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hi).symm ⟨μ, hr⟩
  have hg : g (IntermediateField.AdjoinSimple.gen ℚ (zetaAway N : ℂ)) = μ :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hi ⟨μ, hr⟩
  exact ⟨g.toRingHom.comp (Subring.inclusion hle), hg⟩

theorem exists_cycAway_end {N : ℕ} (hN : N ≠ 0) {m : ℕ} (hm : m.Coprime N) :
    ∃ f : cycAway N →+* cycAway N, f (zetaAway N) = zetaAway N ^ m := by
  have hz : IsPrimitiveRoot (zetaAway N : ℂ) N := Complex.isPrimitiveRoot_exp N hN
  obtain ⟨f, hf⟩ := exists_cycAway_hom_complex hN (hz.pow_of_coprime m hm)
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hmem : ∀ x, f x ∈ cycAway N := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hf ▸ pow_mem (zetaAway N).2 m
      · have e : (N : cycAway N) * ⟨(N : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ = 1 :=
          Subtype.ext (by simpa using mul_inv_cancel₀ hN')
        have e₁ := congrArg f e
        rw [map_mul, map_natCast, map_one] at e₁
        exact Set.mem_of_eq_of_mem (eq_inv_of_mul_eq_one_right e₁) (Subring.subset_closure (Or.inr rfl))
    | zero => exact Set.mem_of_eq_of_mem (map_zero f) (zero_mem (cycAway N))
    | one => exact Set.mem_of_eq_of_mem (map_one f) (one_mem (cycAway N))
    | add x y hx hy ihx ihy => exact (map_add f ⟨x, hx⟩ ⟨y, hy⟩) ▸ add_mem ihx ihy
    | neg x hx ih => exact (map_neg f ⟨x, hx⟩) ▸ neg_mem ih
    | mul x y hx hy ihx ihy => exact (map_mul f ⟨x, hx⟩ ⟨y, hy⟩) ▸ mul_mem ihx ihy
  exact ⟨f.codRestrict (cycAway N) hmem, Subtype.ext hf⟩

theorem exists_cycAway_aut {N : ℕ} (hN : N ≠ 0) {m : ℕ} (hm : m.Coprime N) :
    ∃ σ : cycAway N ≃+* cycAway N, σ (zetaAway N) = zetaAway N ^ m := by
  have hz := isPrimitiveRoot_zetaAway hN
  have : NeZero N := ⟨hN⟩
  obtain ⟨k, -, hk⟩ := (hz.pow_of_coprime m hm).eq_pow_of_pow_eq_one hz.pow_eq_one
  have hkc : k.Coprime N := by
    rw [← (hz.pow_of_coprime m hm).pow_iff_coprime (Nat.pos_of_ne_zero hN), hk]; exact hz
  obtain ⟨f, hf⟩ := exists_cycAway_end hN hm
  obtain ⟨g, hg⟩ := exists_cycAway_end hN hkc
  refine ⟨RingEquiv.ofRingHom f g (cycAway_hom_ext hN ?_) (cycAway_hom_ext hN ?_), hf⟩
  · rw [RingHom.comp_apply, hg, map_pow, hf, hk, RingHom.id_apply]
  · rw [RingHom.comp_apply, hf, map_pow, hg, ← pow_mul, mul_comm, pow_mul, hk, RingHom.id_apply]

theorem exists_pow_of_isLocalRing {N : ℕ} (hN : N ≠ 0) {R : Type} [CommRing R] [IsLocalRing R]
    (β β' : cycAway N →+* R) : ∃ m : ℕ, m.Coprime N ∧ β' (zetaAway N) = β (zetaAway N) ^ m := by
  classical
  have hp := Nat.pos_of_ne_zero hN
  have : NeZero N := ⟨hN⟩
  have hz := isPrimitiveRoot_zetaAway hN
  have h₁ := isPrimitiveRoot_map hN ((IsLocalRing.residue R).comp β)
  have h₂ := isPrimitiveRoot_map hN ((IsLocalRing.residue R).comp β')
  obtain ⟨i, hi, he⟩ := h₁.eq_pow_of_pow_eq_one h₂.pow_eq_one
  refine ⟨i, by rw [← h₁.pow_iff_coprime hp, he]; exact h₂, ?_⟩
  have hprod : ∏ k ∈ Finset.range N, (β' (zetaAway N) - β (zetaAway N) ^ k) = 0 := by
    have e := congrArg (fun p => (p.map β).eval (β' (zetaAway N))) (X_pow_sub_C_eq_prod hz hp (one_pow N))
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, Polynomial.map_prod, eval_prod, eval_sub, eval_pow,
      eval_X, eval_C, mul_one, map_one, map_pow, Polynomial.map_one, eval_one] at e
    rw [← e, ← map_pow, hz.pow_eq_one, map_one, sub_self]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hi)] at hprod
  have hu : IsUnit (∏ k ∈ (Finset.range N).erase i, (β' (zetaAway N) - β (zetaAway N) ^ k)) := by
    refine IsUnit.prod_iff.2 fun k hk => ?_
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, map_pow, sub_ne_zero]
    intro h
    obtain ⟨hki, hk⟩ := Finset.mem_erase.1 hk
    exact hki (h₁.pow_inj (Finset.mem_range.1 hk) hi (h.symm.trans he.symm))
  exact sub_eq_zero.1 (hu.mul_left_eq_zero.1 hprod)

theorem cycAway_galois : ∀ N : ℕ, N ≠ 0 → (∀ m : ℕ, m.Coprime N → ∃ σ : cycAway N ≃+* cycAway N, σ (zetaAway N) = zetaAway N ^ m) ∧ (∀ (R : Type) [CommRing R] (β β' : cycAway N →+* R), β (zetaAway N) = β' (zetaAway N) → β = β') ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (β β' : cycAway N →+* R), ∃ m : ℕ, m.Coprime N ∧ β' (zetaAway N) = β (zetaAway N) ^ m :=
  fun _ hN => ⟨fun _ hm => exists_cycAway_aut hN hm, fun _ _ _ _ h => cycAway_hom_ext hN h,
    fun _ _ _ β β' => exists_pow_of_isLocalRing hN β β'⟩

end GlobalTheory.SiegelTor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorIdealSheafPrincipalisingFamily
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier

namespace GlobalTheory.DenomIdeal

variable {X : Scheme.{0}} [IsIntegral X] {ι : Type} (w : ι → X.functionField)

def IsDen (V : X.Opens) (a : Γ(X, V)) : Prop :=
  ∀ h : genericPoint X ∈ V, ∀ j, ∀ y ∈ V, RegAt y (fnOf V h a * w j)

def gens (V : X.Opens) : Set Γ(X, V) :=
  {b | ∃ a, IsDen w V a ∧ ∃ j, ∀ h : genericPoint X ∈ V, fnOf V h b = fnOf V h a * w j}

def idealOn (V : X.Opens) : Ideal Γ(X, V) := Ideal.span (gens w V)

variable {w}

theorem IsDen.res {U V : X.Opens} (e : V ≤ U) {a : Γ(X, U)} (ha : IsDen w U a) :
    IsDen w V (resG X e a) := by
  intro h j y hy
  rw [fnOf_resG]
  exact ha (e h) j y (e hy)

theorem res_mem_gens {U V : X.Opens} (e : V ≤ U) {b : Γ(X, U)} (hb : b ∈ gens w U) :
    resG X e b ∈ gens w V := by
  obtain ⟨a, ha, j, hj⟩ := hb
  exact ⟨resG X e a, ha.res e, j, fun h => by rw [fnOf_resG, fnOf_resG, hj]⟩

theorem mem_map_of_mem_gens_basicOpen [Fintype ι] {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    {b : Γ(X, X.basicOpen f)} (hb : b ∈ gens w (X.basicOpen f)) :
    b ∈ (idealOn w U).map (resG X (X.basicOpen_le f)) := by
  by_cases hg : genericPoint X ∈ X.basicOpen f
  swap
  · have : b = 0 := Cartier.fn_ext fun h => (hg h).elim
    rw [this]; exact zero_mem _
  have hU' : genericPoint X ∈ U := X.basicOpen_le f hg
  have := hU.isLocalization_basicOpen f
  obtain ⟨a', ha', j, hj⟩ := hb
  obtain ⟨⟨a, _, n, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) a'
  have e' : fnOf _ hg a' * fnOf U hU' f ^ n = fnOf U hU' a := by
    have := congrArg (fnOf _ hg) e
    simp only [map_mul, map_pow] at this
    change fnOf _ hg a' * fnOf _ hg (resG X (X.basicOpen_le f) f) ^ n =
      fnOf _ hg (resG X (X.basicOpen_le f) a) at this
    rwa [fnOf_resG, fnOf_resG] at this
  have hreg : ∀ i, ∀ x ∈ X.basicOpen f, RegAt x (fnOf U hU' a * w i) := fun i x hx => by
    rw [← e', mul_right_comm]
    exact (ha' hg i x hx).mul (GlobalTheory.TrueGeo.SmallSec.regAt_pow (regAt_fnOf (X.basicOpen_le f hx) hU' f) n)
  have := fun i => GlobalTheory.InvertIdeal.exists_mul_pow hU hU' f hg (hreg i)
  choose m γ hγ using this
  set M := ∑ i, m i
  have hm : ∀ i, m i ≤ M := fun i => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have key : ∀ i, fnOf U hU' (γ i * f ^ (M - m i)) = fnOf U hU' (a * f ^ M) * w i := fun i => by
    rw [map_mul, map_mul, hγ, map_pow, map_pow, ← Nat.add_sub_cancel' (hm i), pow_add]
    simp only [Nat.add_sub_cancel_left]
    ring
  have hden : IsDen w U (a * f ^ M) := fun h i y hy => by
    rw [← key i]; exact regAt_fnOf hy _ _
  have hgen : γ j * f ^ (M - m j) ∈ gens w U := ⟨_, hden, j, fun h => key j⟩
  have hu : IsUnit (resG X (X.basicOpen_le f) f) := IsLocalization.Away.algebraMap_isUnit f
  have hb0 : resG X (X.basicOpen_le f) (γ j * f ^ (M - m j)) = b * resG X (X.basicOpen_le f) f ^ (n + M) :=
    Cartier.fn_ext fun h => by
      rw [fnOf_resG, key, map_mul (fnOf _ h), map_pow, fnOf_resG, hj, map_mul, map_pow, ← e']
      ring
  have hb : b = resG X (X.basicOpen_le f) (γ j * f ^ (M - m j)) * ((hu.unit⁻¹ : _) : Γ(X, X.basicOpen f)) ^ (n + M) := by
    rw [hb0, mul_assoc, ← mul_pow, hu.mul_val_inv, one_pow, mul_one]
  rw [hb]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span hgen))

variable (w) in

def idealSheaf [Fintype ι] : X.IdealSheafData where
  ideal U := idealOn w U.1
  map_ideal_basicOpen U f := by
    show Ideal.map (resG X (X.basicOpen_le f)) (idealOn w U.1) = idealOn w (X.basicOpen f)
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      refine Ideal.span_le.2 fun b hb => ?_
      exact Ideal.subset_span (res_mem_gens (X.basicOpen_le f) hb)
    · exact Ideal.span_le.2 fun b hb => mem_map_of_mem_gens_basicOpen U.2 f hb

theorem idealSheaf_ideal [Fintype ι] (U : X.affineOpens) : (idealSheaf w).ideal U = idealOn w U.1 := rfl

theorem idealSheaf_ne_bot [Fintype ι] (i₀ : ι) (h1 : w i₀ = 1) : idealSheaf w ≠ ⊥ := by
  classical
  obtain ⟨_, ⟨W, hW, rfl⟩, hηW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have hW' : IsAffineOpen W := hW
  choose β γ hβ hγ using fun j => GlobalTheory.InvertIdeal.exists_denom hW' hηW hηW (regAt_genericPoint (w j))
  have hβ0 : ∀ j, fnOf W hηW (β j) ≠ 0 := fun j => ((unitAt_fnOf_iff hηW hηW (β j)).2 (hβ j)).ne_zero
  set d := ∏ j, β j
  have hd : ∀ j, fnOf W hηW d * w j = fnOf W hηW (γ j) * fnOf W hηW (∏ i ∈ Finset.univ.erase j, β i) := fun j => by
    rw [hγ, show d = β j * ∏ i ∈ Finset.univ.erase j, β i from (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm,
      map_mul]
    ring
  have hden : IsDen w W d := fun h j y hy => by
    rw [hd j]; exact (regAt_fnOf hy _ _).mul (regAt_fnOf hy _ _)
  have hgen : d ∈ gens w W := ⟨d, hden, i₀, fun h => by rw [h1, mul_one]⟩
  have hd0 : fnOf W hηW d ≠ 0 := by
    rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun j _ => hβ0 j
  intro hbot
  have hmem : d ∈ (idealSheaf w).ideal ⟨W, hW⟩ := Ideal.subset_span hgen
  rw [hbot] at hmem
  exact hd0 (by rw [(Ideal.mem_bot).1 hmem, map_zero])

theorem notMem_support [Finite ι] [Fintype ι] (i₀ : ι) (h1 : w i₀ = 1) {y : X} {k : ι} (hk : w k ≠ 0)
    (hy : ∀ j, RegAt y (w j / w k)) : y ∉ (idealSheaf w).support := by
  obtain ⟨V, hyV, ha⟩ := GlobalTheory.InvertIdeal.exists_common_open hy
  choose a ha using ha
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hyV V.isOpen
  have e : W ≤ V := hWV
  have hηW : genericPoint X ∈ W := gen_mem hyW
  have hfa : ∀ j, fnOf W hηW (resG X e (a j)) = w j / w k := fun j => by rw [fnOf_resG, ha]
  have hden : IsDen w W (resG X e (a i₀)) := fun h j x hx => by
    rw [hfa, h1, one_div, inv_mul_eq_div, ← hfa j]; exact regAt_fnOf hx _ _
  have hgen : (1 : Γ(X, W)) ∈ gens w W :=
    ⟨_, hden, k, fun h => by rw [map_one, hfa, h1, one_div, inv_mul_cancel₀ hk]⟩
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨W, hW⟩) hyW, Scheme.mem_zeroLocus_iff]
  intro H
  exact H 1 (Ideal.subset_span hgen) (by rw [Scheme.basicOpen_one]; exact hyW)

theorem fnOf_appLE {Y' : Scheme.{0}} [IsIntegral Y'] (s : Y' ⟶ X)
    (hη : s (genericPoint Y') ⤳ genericPoint X) {W : X.Opens} {A : Y'.Opens} (hA : A ≤ s ⁻¹ᵁ W)
    (hA' : genericPoint Y' ∈ A) (hW : genericPoint X ∈ W) (c : Γ(X, W)) :
    fnOf A hA' ((s.appLE W A hA).hom c) = GlobalTheory.TrueGeo.SmallSec.fnMap s hη (fnOf W hW c) := by
  rw [GlobalTheory.TrueGeo.SmallSec.fnMap_fnOf s hη hW (hA hA'), ← fnOf_resG hA hA']
  rfl

theorem exists_dvd_of_effCartier [Fintype ι] {Y' : Scheme.{0}} [IsIntegral Y'] (s : Y' ⟶ X)
    (hη : s (genericPoint Y') ⤳ genericPoint X)
    (hE : ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier ((idealSheaf w).comap s)) (y' : Y') :
    ∃ k, GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w k) ≠ 0 ∧ ∀ j,
      RegAt y' (GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w k)) := by
  classical
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (s y')) isOpen_univ
  obtain ⟨U0, f0, sectionFrameQuotient, hf0, hI0⟩ := hE y'
  obtain ⟨t, htle, hyt⟩ := U0.2.exists_basicOpen_le (V := U0.1 ⊓ s ⁻¹ᵁ W) ⟨y', sectionFrameQuotient, hyW⟩ sectionFrameQuotient
  have hAW : Y'.basicOpen t ≤ s ⁻¹ᵁ W := fun x hx => (htle hx).2
  have hA' : genericPoint Y' ∈ Y'.basicOpen t := gen_mem hyt
  have hηW : genericPoint X ∈ W := gen_mem hyW
  set F := resG Y' (Y'.basicOpen_le t) f0 with hFdef
  have hIA : ((idealSheaf w).comap s).ideal (Y'.affineBasicOpen t) = Ideal.span {F} := by
    rw [← Scheme.IdealSheafData.map_ideal_basicOpen, hI0, Ideal.map_span, Set.image_singleton]
  have hmap : Ideal.map (s.appLE W (Y'.basicOpen t) hAW).hom (idealOn w W) = Ideal.span {F} := by
    rw [← hIA, GlobalTheory.Principalise.comapIdealAffine _ s ⟨W, hW⟩ (Y'.affineBasicOpen t) hAW]
    rfl
  set φ := fnOf (Y'.basicOpen t) hA'
  set w' := fun j => GlobalTheory.TrueGeo.SmallSec.fnMap s hη (w j) with hw'
  have hφ : ∀ c : Γ(X, W), φ ((s.appLE W (Y'.basicOpen t) hAW).hom c) =
      GlobalTheory.TrueGeo.SmallSec.fnMap s hη (fnOf W hηW c) := fun c => fnOf_appLE s hη hAW hA' hηW c
  have hF0 : φ F ≠ 0 := by
    have hU0 : genericPoint Y' ∈ U0.1 := Y'.basicOpen_le t hA'
    have : Nontrivial Γ(Y', U0.1) := (fnOf U0.1 hU0).domain_nontrivial
    rw [hFdef, fnOf_resG]
    intro h
    exact nonZeroDivisors.ne_zero hf0 (fnOf_injective _ hU0 (h.trans (map_zero _).symm))
  have key : ∀ x ∈ Ideal.map (s.appLE W (Y'.basicOpen t) hAW).hom (idealOn w W),
      ∃ C : ι → Y'.functionField, φ x = ∑ j, w' j * C j ∧ ∀ i j, ∃ r : Γ(Y', Y'.basicOpen t),
        w' i * C j = φ F * φ r := by
    intro x hx
    rw [idealOn, Ideal.map_span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, ⟨a, ha, j₀, hb⟩, rfl⟩ := hx
      refine ⟨Pi.single j₀ (GlobalTheory.TrueGeo.SmallSec.fnMap s hη (fnOf W hηW a)), ?_, fun i j => ?_⟩
      · rw [hφ, hb hηW, map_mul, Finset.sum_eq_single j₀ (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
          (by simp), Pi.single_eq_same, mul_comm]
      · by_cases hj : j = j₀
        · subst hj
          rw [Pi.single_eq_same]
          obtain ⟨bi, hbi⟩ := exists_fnOf_eq hηW fun y hy => ha hηW i y hy
          have hmem : (s.appLE W (Y'.basicOpen t) hAW).hom bi ∈ Ideal.span {F} :=
            hmap ▸ Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨a, ha, i, fun _ => hbi⟩)
          obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
          refine ⟨r, ?_⟩
          rw [hw', ← map_mul, mul_comm (w i), ← hbi, ← hφ, ← hr, map_mul, mul_comm]
        · rw [Pi.single_eq_of_ne hj, mul_zero]
          exact ⟨0, by rw [map_zero, mul_zero]⟩
    | zero => exact ⟨0, by simp, fun i j => ⟨0, by simp⟩⟩
    | add x y _ _ hx hy =>
      obtain ⟨C, hC, hC'⟩ := hx
      obtain ⟨D, hD, hD'⟩ := hy
      refine ⟨C + D, by rw [map_add, hC, hD, ← Finset.sum_add_distrib]; simp only [Pi.add_apply, mul_add],
        fun i j => ?_⟩
      obtain ⟨r, hr⟩ := hC' i j
      obtain ⟨r', hr'⟩ := hD' i j
      exact ⟨r + r', by simp only [Pi.add_apply, mul_add, hr, hr', map_add]⟩
    | smul c x _ hx =>
      obtain ⟨C, hC, hC'⟩ := hx
      refine ⟨fun j => φ c * C j, ?_, fun i j => ?_⟩
      · rw [smul_eq_mul, map_mul, hC, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      · obtain ⟨r, hr⟩ := hC' i j
        refine ⟨c * r, ?_⟩
        rw [map_mul, mul_left_comm, hr]
        ring
  obtain ⟨C, hC, hC'⟩ := key F (hmap ▸ Ideal.mem_span_singleton_self F)
  choose r hr using hC'
  have hreg : ∀ i j, RegAt y' (w' i * (C j / φ F)) := fun i j => by
    rw [mul_div_assoc', hr, mul_div_cancel_left₀ _ hF0]
    exact regAt_fnOf hyt _ _
  have he1 : ∑ j, (fun _ => (1 : Y'.functionField)) j * (w' j * (C j / φ F)) = 1 := by
    simp only [one_mul, mul_div_assoc']
    rw [← Finset.sum_div, ← hC, div_self hF0]
  obtain ⟨k, hk⟩ := GlobalTheory.InvertIdeal.exists_unitAt (x := y') (c := fun _ => 1)
    (g := fun j => w' j * (C j / φ F)) (fun _ => ⟨1, map_one _⟩) (fun j => hreg j j) he1
  have hk0 : w' k * (C k / φ F) ≠ 0 := hk.ne_zero
  refine ⟨k, left_ne_zero_of_mul hk0, fun j => ?_⟩
  have e : w' j / w' k = (w' j * (C k / φ F)) * (w' k * (C k / φ F))⁻¹ := by
    have h2 : C k / φ F ≠ 0 := right_ne_zero_of_mul hk0
    rw [← div_eq_mul_inv, mul_div_mul_right _ _ h2]
  change RegAt y' (w' j / w' k)
  rw [e]
  exact (hreg j k).mul hk.inv.regAt

theorem exists_idealSheaf : ∀ (Y : Scheme.{0}) [IsIntegral Y] (N : ℕ) (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)) (U : Y.Opens),
    w i₀ = 1 → (∀ y ∈ U, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) →
    ∃ I : Y.IdealSheafData, I ≠ ⊥ ∧ (∀ y ∈ U, y ∉ I.support) ∧
      ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (s : Y' ⟶ Y) (hη : s (genericPoint Y') = genericPoint Y),
        ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (I.comap s) → ∀ y' : Y', ∃ k,
          GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k) ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y'
            (GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k)) := by
  intro Y _ N w i₀ U h1 hU
  refine ⟨idealSheaf w, idealSheaf_ne_bot i₀ h1, fun y hy => ?_, fun Y' _ s hη hE y' =>
    exists_dvd_of_effCartier s (specializes_of_eq hη) hE y'⟩
  obtain ⟨k, hk, hreg⟩ := hU y hy
  exact notMem_support i₀ h1 hk hreg

end GlobalTheory.DenomIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivOfCenterHeightLeOne
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

open IsLocalRing in

theorem valuationRing_atPrime_of_minimal {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime]
    (hmin : ∀ p : Ideal A, p.IsPrime → p ≠ ⊥ → p ≤ q → p = q) :
    ValuationRing (Localization.AtPrime q) := by
  have hT := tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime q)
  have h1 : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have h2 : ∀ Q' : Ideal (Localization.AtPrime q), Q' ≠ ⊥ → Q'.IsPrime →
      Q' = maximalIdeal (Localization.AtPrime q) := by
    intro Q' hQ' hQ'p
    have hc : (Q'.comap (algebraMap A (Localization.AtPrime q))).IsPrime := Ideal.comap_isPrime _ _
    have hle : Q'.comap (algebraMap A (Localization.AtPrime q)) ≤ q := by
      intro x hx
      by_contra hxq
      exact hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
        (IsLocalization.map_units (Localization.AtPrime q) (⟨x, hxq⟩ : q.primeCompl)))
    have hne : Q'.comap (algebraMap A (Localization.AtPrime q)) ≠ ⊥ := by
      intro h0
      apply hQ'
      rw [← IsLocalization.map_under q.primeCompl (Localization.AtPrime q) Q']
      rw [Ideal.under, h0, Ideal.map_bot]
    have heq := hmin _ hc hne hle
    rw [← IsLocalization.map_under q.primeCompl (Localization.AtPrime q) Q']
    rw [Ideal.under, heq, Localization.AtPrime.map_eq_maximalIdeal]
  have h12 : IsIntegrallyClosed (Localization.AtPrime q) ∧ ∀ Q' : Ideal (Localization.AtPrime q),
      Q' ≠ ⊥ → Q'.IsPrime → Q' = maximalIdeal (Localization.AtPrime q) := ⟨h1, h2⟩
  exact (hT.out 3 1).mp h12

theorem mul_eq_mul_of_atPrime {A : Type} [CommRing A] [IsDomain A] (q : Ideal A) [q.IsPrime]
    (x y a : A) (s : q.primeCompl)
    (h : algebraMap A (Localization.AtPrime q) x * IsLocalization.mk' _ a s =
      algebraMap A (Localization.AtPrime q) y) : x * a = y * s := by
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul] at h
  exact IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors h

end GlobalTheory

namespace GlobalTheory

theorem exists_div_of_center_height_le_one : ∀ (K : Type) [Field K] (R : Subring K) [IsNoetherianRing R]
    [IsIntegrallyClosed R] [IsFractionRing R K] (E : ValuationSubring K), R ≤ E.toSubring →
    (∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → (∀ r ∈ p, (r : K) ∈ E.nonunits) →
      ∀ r : R, (r : K) ∈ E.nonunits → r ∈ p) →
    ∀ e ∈ E, ∃ a ∈ R, ∃ s ∈ R, s⁻¹ ∈ E ∧ e = a / s := by
  intro K _ R _ _ _ E hRE hyp e he
  classical
  let φ : R →+* E :=
    { toFun := fun r => ⟨r, hRE r.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let q : Ideal R := (IsLocalRing.maximalIdeal E).comap φ
  have hqmem : ∀ r : R, r ∈ q ↔ E.valuation (r : K) < 1 := fun r => E.valuation_lt_one_iff (φ r)
  have hRv : ∀ r : R, E.valuation (r : K) ≤ 1 := fun r => (E.valuation_le_one_iff _).2 (hRE r.2)
  have hv1 : ∀ s : R, s ∉ q → E.valuation (s : K) = 1 := fun s hs =>
    le_antisymm (hRv s) (not_lt.1 ((hqmem s).not.1 hs))
  have hinv : ∀ s : R, s ∉ q → (s : K)⁻¹ ∈ E := by
    intro s hs
    rw [← E.valuation_le_one_iff, map_inv₀, hv1 s hs, inv_one]
  have hne0 : ∀ s : R, s ∉ q → (s : K) ≠ 0 := by
    intro s hs h
    have := hv1 s hs
    rw [h, map_zero] at this
    exact zero_ne_one this
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.mk'_surjective (S := K) (nonZeroDivisors R) e
  dsimp only at hxy
  rw [IsFractionRing.mk'_eq_div] at hxy
  have hy0 : (algebraMap R K y) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors y.2
  change ((x : R) : K) / ((y : R) : K) = e at hxy
  change ((y : R) : K) ≠ 0 at hy0
  by_cases hq : q = ⊥
  · have hyq : (y : R) ∉ q := by
      rw [hq, Ideal.mem_bot]
      intro h; apply hy0; rw [h]; rfl
    exact ⟨x, (x : R).2, y, (y : R).2, hinv _ hyq, hxy.symm⟩
  · have hmin : ∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≤ q → p = q := by
      intro p hp hp0 hpq
      refine le_antisymm hpq ?_
      intro r hr
      refine hyp p hp hp0 (fun t ht => ?_) r ?_
      · exact E.mem_nonunits_iff.2 ((hqmem t).1 (hpq ht))
      · exact E.mem_nonunits_iff.2 ((hqmem r).1 hr)
    haveI : ValuationRing (Localization.AtPrime q) := valuationRing_atPrime_of_minimal q hmin
    obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap R (Localization.AtPrime q) x)
      (algebraMap R (Localization.AtPrime q) y)
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (S := Localization.AtPrime q) q.primeCompl c
    dsimp only at hc
    have hsq : (s : R) ∉ q := s.2
    rcases hc with hc | hc
    · have h := mul_eq_mul_of_atPrime q _ _ _ _ hc
      have hK : ((x : R) : K) * (a : K) = ((y : R) : K) * ((s : R) : K) := by
        have := congrArg (fun t : R => (t : K)) h
        simpa using this
      by_cases haq : a ∈ q
      · exfalso
        have hea : e * (a : K) = ((s : R) : K) := by
          rw [← hxy]
          field_simp
          linear_combination hK
        have h1 := hv1 _ hsq
        rw [← hea, map_mul] at h1
        have hle : E.valuation e * E.valuation (a : K) ≤ E.valuation (a : K) :=
          mul_le_of_le_one_left' ((E.valuation_le_one_iff e).2 he)
        have := (hqmem a).1 haq
        rw [h1] at hle
        exact absurd (lt_of_le_of_lt hle this) (lt_irrefl 1)
      · refine ⟨((s : R) : K), (s : R).2, (a : K), a.2, hinv a haq, ?_⟩
        rw [← hxy, div_eq_div_iff hy0 (hne0 a haq)]
        linear_combination hK
    · have h := mul_eq_mul_of_atPrime q _ _ _ _ hc
      have hK : ((y : R) : K) * (a : K) = ((x : R) : K) * ((s : R) : K) := by
        have := congrArg (fun t : R => (t : K)) h
        simpa using this
      refine ⟨(a : K), a.2, ((s : R) : K), (s : R).2, hinv _ hsq, ?_⟩
      rw [← hxy, div_eq_div_iff hy0 (hne0 _ hsq)]
      linear_combination -hK

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspSectionLargeEvenScalarWeightStatement
section
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_cuspSection_large_evenScalarWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → (∀ n : ℕ, Even n → ∀ γ ∈ X.Γ, X.χ (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) γ = 1) → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Even n ∧ ∃ P ∈ X.SS (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)), ∃ y ∈ X.dom, P y ≠ 0 := by
  first | exact @GlobalTheory.ScalarPoin.exists_cusp_ne_some | exact GlobalTheory.ScalarPoin.exists_cusp_ne_some | (intros; apply GlobalTheory.ScalarPoin.exists_cusp_ne_some <;> assumption)
end

