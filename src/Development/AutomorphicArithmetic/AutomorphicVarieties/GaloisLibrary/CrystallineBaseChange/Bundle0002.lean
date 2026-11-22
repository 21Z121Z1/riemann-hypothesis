import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.ExplicitConstants.SplitCharY
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExistsSqEqNegOfDiscr
import Mathlib.NumberTheory.LSeries.PrimesInAP

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.FrobEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open UpperTheory.V UpperTheory.V.Af
open scoped Pointwise

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

omit [NumberField F] in
private theorem val_smul_lt (g : G F Ω) (A : ValuationSubring Ω) (y : Ω) :
    (g • A).valuation (g y) < 1 ↔ A.valuation y < 1 := by
  have e : ∀ z : Ω, g z ∈ g • A ↔ z ∈ A := fun z => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, show g z = g • z from rfl, inv_smul_smul]
  rw [valuation_lt_one_iff', valuation_lt_one_iff', e, ← map_inv₀, e, map_eq_zero]

omit [NumberField F] in
private theorem val_smul_le (g : G F Ω) (A : ValuationSubring Ω) (y : Ω) :
    (g • A).valuation (g y) ≤ 1 ↔ A.valuation y ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, show g y = g • y from rfl, inv_smul_smul]

omit [NumberField F] in
private theorem conj_dec {g τ : G F Ω} {A : ValuationSubring Ω} (h : τ ∈ (g • A).decompositionSubgroup F) :
    g⁻¹ * τ * g ∈ A.decompositionSubgroup F := by
  have h1 : τ • g • A = g • A := h
  show (g⁻¹ * τ * g) • A = A
  rw [mul_smul, mul_smul, h1, inv_smul_smul]

omit [NumberField F] in
private theorem conj_apply (g τ : G F Ω) (x : Ω) : g ((g⁻¹ * τ * g) x) = τ (g x) := by
  change g • ((g⁻¹ * τ * g) • x) = τ • (g • x)
  rw [mul_smul, mul_smul, smul_inv_smul]

omit [NumberField F] in
private theorem conj_frob {g τ : G F Ω} {A : ValuationSubring Ω} {q : ℕ} (h : IsFrob (g • A) q τ) :
    IsFrob A q (g⁻¹ * τ * g) := by
  refine ⟨conj_dec h.1, fun x hx => ?_⟩
  have h1 := h.2 (g x) ((val_smul_le g A x).2 hx)
  rwa [← conj_apply, ← map_pow, ← map_sub, val_smul_lt] at h1

private theorem conj_ine {g τ : G F Ω} {A : ValuationSubring Ω} (h : τ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * τ * g ∈ Ine (F := F) A := by
  refine ⟨conj_dec h.1, fun x hx => ?_⟩
  have h1 := h.2 (g x) ((val_smul_le g A x).2 hx)
  rwa [← conj_apply, ← map_sub, val_smul_lt] at h1

private theorem ine_fix {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A w) {M : ℕ}
    (hM : ((M : ℕ) : 𝓞 F) ∉ w.asIdeal) {s : G F Ω} (hs : s ∈ Ine (F := F) A) (ζ : Ω) (hζ : ζ ^ M = 1) : s ζ = ζ := by
  set v := A.valuation with hvdef
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hM (by simp)
  have hvM : ¬ v (M : Ω) < 1 := by
    intro hlt
    apply hM
    rw [← hA]
    simpa using hlt
  have hζ1 : v ζ = 1 := by
    rcases lt_trichotomy (v ζ) 1 with h | h | h
    · have h2 := pow_lt_one' h hM0
      rw [← map_pow, hζ, map_one] at h2
      exact absurd h2 (lt_irrefl 1)
    · exact h
    · have h2 := one_lt_pow' h hM0
      rw [← map_pow, hζ, map_one] at h2
      exact absurd h2 (lt_irrefl 1)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ1
  have hsd : v (s ζ - ζ) < 1 := hs.2 ζ hζ1.le
  have hηM : (s ζ) ^ M = 1 := by rw [← map_pow, hζ, map_one]
  set η := s ζ with hη
  set u := η * ζ⁻¹ with hu
  have huM : u ^ M = 1 := by rw [hu, mul_pow, inv_pow, hηM, hζ, inv_one, mul_one]
  have hu1 : v (u - 1) < 1 := by
    have e : u - 1 = (η - ζ) * ζ⁻¹ := by rw [hu, sub_mul, mul_inv_cancel₀ hζ0]
    rw [e, map_mul, map_inv₀, hζ1, inv_one, mul_one]
    exact hsd
  have hule : v u ≤ 1 := by
    have e : u = (u - 1) + 1 := by ring
    rw [e]
    exact (v.map_add _ _).trans (max_le hu1.le (by rw [map_one]))
  by_contra hne
  have hu_ne : u ≠ 1 := by
    intro h1
    apply hne
    have e : η = u * ζ := by rw [hu, mul_assoc, inv_mul_cancel₀ hζ0, mul_one]
    rw [e, h1, one_mul]
  have hsum : ∑ i ∈ Finset.range M, u ^ i = 0 := by
    have h := geom_sum_mul u M
    rw [huM, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hu_ne)
  have hlt : v (∑ i ∈ Finset.range M, (u ^ i - 1)) < 1 := by
    apply Valuation.map_sum_lt v one_ne_zero
    intro i _
    rw [← geom_sum_mul u i, map_mul]
    have hs1 : v (∑ j ∈ Finset.range i, u ^ j) ≤ 1 :=
      Valuation.map_sum_le v (fun j _ => by rw [map_pow]; exact pow_le_one' hule j)
    calc v (∑ j ∈ Finset.range i, u ^ j) * v (u - 1) ≤ 1 * v (u - 1) := by gcongr
      _ = v (u - 1) := one_mul _
      _ < 1 := hu1
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, zero_sub, Valuation.map_neg] at hlt
  apply hvM
  simpa using hlt

end

theorem UpperTheory.V.Br.frobEx :
    UpperTheory.V.Br.FrobEx := by
  intro F Ω _ _ _ _ _ l _ ι n r w
  refine ⟨?_, ?_⟩
  · intro B B' hB hB'
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨σ, hσ⟩ := exists_isFrob hA
    have h1 := (hB A hA).2 σ hσ
    have h2 := (hB' A hA).2 σ hσ
    have h3 := congrArg Polynomial.roots (h1.symm.trans h2)
    simpa [Polynomial.roots_multiset_prod_X_sub_C] using h3
  · intro M hlev hl hM
    obtain ⟨A0, hA0, χ, hχ, P, hP⟩ := hlev w hl
    have hI0 : ∀ t ∈ Ine (F := F) A0, r t = 1 := by
      intro t ht
      have hd := hP t ht
      have hc : ∀ i, χ i t = 1 := fun i => hχ i t (fun ζ hζ => ine_fix hA0 hM ht ζ hζ)
      simp only [hc, Units.val_one, Matrix.diagonal_one] at hd
      have hq : P * r t * P⁻¹ = 1 := Units.ext hd
      calc r t = P⁻¹ * (P * r t * P⁻¹) * P := by group
        _ = 1 := by rw [hq]; group
    obtain ⟨σ0, hσ0⟩ := exists_isFrob hA0
    refine ⟨(Polynomial.map ι.toRingHom
      ((r σ0⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly).roots, ?_⟩
    intro A hA
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver hA0 hA
    subst hg
    refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
    · have ht := hI0 _ (conj_ine hs)
      calc r s = r g * r (g⁻¹ * s * g) * r g⁻¹ := by
            simp only [map_mul, map_inv]
            group
        _ = 1 := by rw [ht]; simp
    · have hc := inv_mul_mem_Ine_of_isFrob hσ0 (conj_frob hσ)
      have he : r (g⁻¹ * σ * g) = r σ0 := by
        have h4 := hI0 _ hc
        rw [map_mul, map_inv] at h4
        exact (inv_mul_eq_one.1 h4).symm
      have hu : r σ⁻¹ = r g * r σ0⁻¹ * (r g)⁻¹ := by
        rw [map_inv r σ0, ← he]
        simp only [map_mul, map_inv]
        group
      rw [hu, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
      exact Polynomial.Splits.eq_prod_roots_of_monic (IsAlgClosed.splits _)
        ((Matrix.charpoly_monic _).map _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.PotMove
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst UpperTheory.V UpperTheory.V.Af
open scoped Pointwise

theorem UpperTheory.V.Br.potMove :
    UpperTheory.V.Br.PotMove := by
  intro F Ω _ _ _ _ _ l _ n r A A' g hg hA
  obtain ⟨O, i1, i2, i3, Bw, hj, LL', r', ⟨hle, hmap⟩, K', hK', hcr⟩ := hA
  have hmem : ∀ s : G F Ω, s ∈ Dec (F := F) A' ↔ g * s * g⁻¹ ∈ Dec (F := F) A := fun s => by
    have hgA : g • A' = A := by
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hg]
      simp [AlgEquiv.smul_def]
    rw [mem_Dec, mem_Dec, ← hgA, mul_smul, inv_smul_smul, mul_smul, smul_left_cancel_iff]
  let φ : ↥(Dec (F := F) A') ≃* ↥(Dec (F := F) A) :=
    { toFun := fun s => ⟨g * s * g⁻¹, (hmem s).1 s.2⟩
      invFun := fun t => ⟨g⁻¹ * t * g, (hmem _).2 (by
        have e : g * (g⁻¹ * (t : G F Ω) * g) * g⁻¹ = t := by group
        rw [e]; exact t.2)⟩
      left_inv := fun s => Subtype.ext (by dsimp only; group)
      right_inv := fun t => Subtype.ext (by dsimp only; group)
      map_mul' := fun s t => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hφ : Continuous φ :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hφs : Continuous φ.symm :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hjE : ∀ x : F, Bw.j (g (algebraMap F Ω x)) = Bw.j (algebraMap F Ω x) := fun x => by
    rw [AlgEquiv.commutes]
  let Bw' : LocBridge l F Ω (Dec (F := F) A') O :=
    { Kw := Bw.Kw, j := Bw.j.comp (g : Ω →+* Ω)
      j_E := fun x => by
        change Bw.j (g (algebraMap F Ω x)) ∈ _
        rw [hjE]; exact Bw.j_E x
      j_dense := Bw.j_dense.trans (closure_mono (by
        rintro _ ⟨x, rfl⟩
        exact ⟨x, hjE x⟩))
      e := φ.trans Bw.e
      e_cont := Bw.e_cont.comp hφ, e_symm_cont := hφs.comp Bw.e_symm_cont
      e_comm := fun s x => by
        refine (Bw.e_comm (φ s) (g x)).trans ?_
        change Bw.j ((g * (s : G F Ω) * g⁻¹) (g x)) = Bw.j (g ((s : G F Ω) x))
        simp
      LL := Bw.LL, LL_split := Bw.LL_split, eO := Bw.eO, eO_alg := Bw.eO_alg
      eO_cont := Bw.eO_cont, eO_symm_cont := Bw.eO_symm_cont }
  have h1 : PotCrysAt (r.comp (MulAut.conj g).toMonoidHom) A' := by
    refine ⟨O, i1, i2, i3, Bw', fun x => (hg x).trans (hj (g x)), LL', r'.comp φ.toMonoidHom,
      ⟨hle, MonoidHom.ext fun s => DFunLike.congr_fun hmap (φ s)⟩, K', hK', ?_⟩
    have e : Bw'.repE LL' (r'.comp φ.toMonoidHom) = Bw.repE LL' r' := by
      refine MonoidHom.ext fun t => ?_
      simp [LocBridge.repE, Bw']
    rw [e]
    exact hcr
  refine h1.of_iso ⟨(r g)⁻¹, fun s => ?_⟩
  simp [mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.PotRes
section
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal UpperTheory.V.Loc UpperTheory.V.Af UpperTheory.V.Af.Bc NumberField

private theorem ex_bridge {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} (j : Ω →+* Om l) (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) :
    ∃ (L : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL L)), Bw.j = j := by
  let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap E Ω))⟩
  have := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := E) hj K rfl
  exact ⟨⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩,
    { Kw := K
      j := j
      j_E := fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
      j_dense := GlobalTheory.PlaceBridge.adjoin_range_subset_closure (j.comp (algebraMap E Ω))
      e := e
      e_cont := he
      e_symm_cont := he'
      e_comm := hec
      LL := ⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩
      LL_split := fun τ x => AlgHom.fieldRange_le_normalClosure τ ⟨x, rfl⟩
      eO := RingEquiv.refl _
      eO_alg := fun _ => rfl
      eO_cont := continuous_id
      eO_symm_cont := continuous_id }, rfl⟩

theorem UpperTheory.V.Br.potRes :
    UpperTheory.V.Br.PotRes := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ n r A hr
  obtain ⟨O, i1, i2, i3, Bw, hj, hp⟩ := hr
  obtain ⟨L, Bw', hBj⟩ := ex_bridge (E := K) (A := A) Bw.j hj
  refine ⟨↥(OL L), inferInstance, inferInstance, inferInstance, Bw', fun x => by rw [hBj]; exact hj x, ?_⟩
  obtain ⟨L₀, r₀, hm₀, -⟩ := id hp
  have hm₁ := hm₀.enlarge (L₂ := GlobalTheory.Pst.supExt L₀ Bw'.LL) le_sup_left
  have hL : Bw'.LL.1 ≤ (GlobalTheory.Pst.supExt L₀ Bw'.LL).1 := le_sup_right
  obtain ⟨r₁, hm, hc⟩ : ∃ r₁, GlobalTheory.Pst.IsModel Bw (r.comp (Dec (F := F) A).subtype) (GlobalTheory.Pst.supExt L₀ Bw'.LL) r₁ ∧
      Bw.IsPotCrysE (PP l) _ r₁ := ⟨_, hm₁, (hm₁.isPotCrysAt_iff (PP l)).1 hp⟩
  clear hm₁
  generalize GlobalTheory.Pst.supExt L₀ Bw'.LL = L₁ at hL r₁ hm hc
  obtain ⟨K₁, h₁, hc⟩ := hc
  have hmem : ∀ σ : G K Ω, σ ∈ Dec (F := K) A ↔ res F Ω K σ ∈ Dec (F := F) A := fun σ => by
    rw [mem_Dec, mem_Dec]
    exact Iff.rfl
  let f : ↥(Dec (F := K) A) →* ↥(Dec (F := F) A) :=
    ((res F Ω K).comp (Dec (F := K) A).subtype).codRestrict _ fun σ => (hmem σ).1 σ.2
  refine ⟨L₁, r₁.comp f, ⟨hL, MonoidHom.ext fun g => DFunLike.congr_fun hm.2 (f g)⟩, ?_⟩
  have h₂ : K₁.1 ≤ (GlobalTheory.Pst.supExt K₁ Bw'.Kw).1 := le_sup_left
  have h₃ : Bw'.Kw.1 ≤ (GlobalTheory.Pst.supExt K₁ Bw'.Kw).1 := le_sup_right
  refine ⟨_, h₃, ?_⟩
  obtain ⟨T⟩ := tiedP l
  have hres := (GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (PP l) (AIP l) T K₁ _ L₁ h₂ _ _).1 hc
  convert hres using 1
  refine MonoidHom.ext fun g => ?_
  have hg : f (Bw'.e.symm (Subgroup.inclusion (GK_le h₃) g)) =
      Bw.e.symm (Subgroup.inclusion (GK_le h₁) (Subgroup.inclusion (GK_le h₂) g)) := by
    refine Subtype.ext (AlgEquiv.ext fun x => Bw.j.injective ?_)
    have a1 := Bw'.e_comm (Bw'.e.symm (Subgroup.inclusion (GK_le h₃) g)) x
    have a2 := Bw.e_comm (Bw.e.symm (Subgroup.inclusion (GK_le h₁) (Subgroup.inclusion (GK_le h₂) g))) x
    rw [MulEquiv.apply_symm_apply] at a1 a2
    rw [hBj] at a1
    exact a1.symm.trans a2
  exact congrArg (fun s => Matrix.toLinAlgEquiv' (r₁ s : Matrix (Fin n) (Fin n) ↥L₁.1)) hg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadFam
section
open NumberField

private theorem quadFam_one (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 3) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K),
      Module.finrank ℚ K = 2 ∧ discr K = -(p : ℤ) := by
  obtain ⟨K, hF, hN, hr, hd⟩ := KStar.Consta.exists_quadField hp h4
  have hp0 : p ≠ 0 := hp.ne_zero
  have htc : IsTotallyComplex K :=
    (KStar.Choice.exists_sq_eq_neg_of_discr hr hp0 hd).2
  have hq : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := hr }
  exact ⟨K, hF, hN, IsCMField.ofCMExtension ℚ K, hr, hd⟩

theorem UpperTheory.V.Br.quadFam :
    UpperTheory.V.Br.QuadFam := by
  intro N
  have hS : {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro n
    obtain ⟨p, hpn, hpp, hmod⟩ :=
      Nat.forall_exists_prime_gt_and_modEq n (q := 4) (a := 3) (by norm_num) (by norm_num)
    exact ⟨p, ⟨hpp, hmod⟩, hpn⟩
  let e := hS.natEmbedding
  let q : Fin N → ℕ := fun i => (e i.val).1
  have hq : ∀ i, (q i).Prime ∧ q i % 4 = 3 := fun i => (e i.val).2
  have hinj : ∀ i j, q i = q j → i = j := fun i j h =>
    Fin.ext (e.injective (Subtype.ext h))
  choose K hF hN hC hr hd using fun i => quadFam_one (q i) (hq i).1 (hq i).2
  refine ⟨K, hF, hN, hC, hr, ?_⟩
  intro i j hij
  rw [hd i, hd j]
  have hne : q i ≠ q j := fun h => hij (hinj i j h)
  have hcop : Nat.Coprime (q i) (q j) := (Nat.coprime_primes (hq i).1 (hq j).1).2 hne
  exact (Nat.isCoprime_iff_coprime.2 hcop).neg_neg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ResTwo
section
open UpperTheory.V UpperTheory.V.Af

private theorem schur_scalar_of_commutes_irreducible {Γ k : Type} [Group Γ] [Field k] [IsAlgClosed k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (hirr : IsIrr r) (g : Matrix (Fin n) (Fin n) k)
    (hg : ∀ s, g * (r s : Matrix (Fin n) (Fin n) k) = (r s : Matrix (Fin n) (Fin n) k) * g) :
    ∃ c : k, g = c • (1 : Matrix (Fin n) (Fin n) k) := by
  obtain ⟨hne, -, hmin⟩ := hirr
  have hnt : Nontrivial (Fin n → k) := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact hne (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' g : Module.End k (Fin n → k))
  refine ⟨c, ?_⟩
  rcases hmin (Module.End.eigenspace (Matrix.toLin' g : Module.End k (Fin n → k)) c) le_top (by
      intro t v hv
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
      rw [Matrix.mulVec_mulVec, hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]) with h | h
  · exact absurd h hc
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ Module.End.eigenspace (Matrix.toLin' g : Module.End k (Fin n → k)) c := by
      rw [h]; trivial
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv]; simp

private theorem part_two {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] [IsAlgClosed k] {n : ℕ} (φ : Γ' →* Γ)
    (δ : Γ →* kˣ) (h1 : ∀ s, δ s = 1 ↔ s ∈ φ.range) (h2 : ∀ s, δ s = 1 ∨ δ s = -1) (r r' : Γ →* GL (Fin n) k)
    (hirr : IsIrr (r.comp φ)) (hiso : RepIso (r.comp φ) (r'.comp φ)) : RepIso r r' ∨ RepIso (tw r δ) r' := by
  obtain ⟨g, hg⟩ := hiso
  have hH : ∀ s, δ s = 1 → r' s = g * r s * g⁻¹ := by
    intro s hs
    obtain ⟨x, rfl⟩ := (h1 s).1 hs
    exact hg x
  by_cases hall : ∀ s, δ s = 1
  · exact Or.inl ⟨g, fun s => hH s (hall s)⟩
  push Not at hall
  obtain ⟨t, ht⟩ := hall
  have ht' : δ t = -1 := (h2 t).resolve_left ht
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin n) k, u = (r t)⁻¹ * g⁻¹ * r' t * g := ⟨_, rfl⟩
  have hrt : r' t = g * (r t * u) * g⁻¹ := by rw [hu]; group
  have hcomm : ∀ s, δ s = 1 → u * r s = r s * u := by
    intro s hs
    have e1 := hH s hs
    have e2 := hH (t * s * t⁻¹) (by simp [hs])
    simp only [map_mul, map_inv] at e2
    rw [e1, hrt] at e2
    have e3 : u * r s = (r t)⁻¹ * g⁻¹ * (g * (r t * u) * g⁻¹ * (g * r s * g⁻¹) * (g * (r t * u) * g⁻¹)⁻¹) * g * r t * u := by
      group
    rw [e3, e2]; group
  obtain ⟨c, hc⟩ := schur_scalar_of_commutes_irreducible (r.comp φ) hirr (u : Matrix (Fin n) (Fin n) k) (by
    intro x
    have := hcomm (φ x) ((h1 _).2 ⟨x, rfl⟩)
    simpa using congrArg Units.val this)
  have hcen : ∀ a : GL (Fin n) k, u * a = a * u := by
    intro a
    apply Units.ext
    simp [hc]
  have huu : u * u = 1 := by
    have e2 := hH (t * t) (by simp [ht'])
    simp only [map_mul] at e2
    rw [hrt] at e2
    have e3 : u * r t * u = (r t)⁻¹ * g⁻¹ * (g * (r t * u) * g⁻¹ * (g * (r t * u) * g⁻¹)) * g := by group
    rw [e2, hcen (r t)] at e3
    calc u * u = (r t)⁻¹ * (r t * u * u) := by group
      _ = 1 := by rw [e3]; group
  have hneg : ∀ s, δ s = -1 → r' s = g * (u * r s) * g⁻¹ := by
    intro s hs
    have e1 := hH (t⁻¹ * s) (by simp [hs, ht'])
    have e2 : r' s = r' t * r' (t⁻¹ * s) := by rw [← map_mul]; simp
    rw [e2, e1, hrt, ← hcen (r t), map_mul, map_inv]; group
  have hu2 : u = 1 ∨ u = -1 := by
    have e := congrArg Units.val huu
    rw [Units.val_mul, hc, Matrix.smul_mul, Matrix.one_mul, smul_smul, Units.val_one] at e
    have hn : Nonempty (Fin n) := by
      by_contra hc
      rw [not_nonempty_iff] at hc
      exact hirr.1 (Subsingleton.elim _ _)
    obtain ⟨i⟩ := hn
    have e' := congrFun (congrFun e i) i
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e'
    rcases mul_self_eq_one_iff.1 e' with h | h
    · left; apply Units.ext; simp [hc, h]
    · right; apply Units.ext; simp [hc, h]
  rcases hu2 with h | h
  · refine Or.inl ⟨g, fun s => ?_⟩
    rcases h2 s with hs | hs
    · exact hH s hs
    · rw [hneg s hs, h, one_mul]
  · refine Or.inr ⟨g, fun s => ?_⟩
    rcases h2 s with hs | hs
    · rw [hH s hs]; congr 2; apply Units.ext; simp [tw_val, hs]
    · rw [hneg s hs, h]; congr 2; apply Units.ext; simp [tw_val, hs]

private theorem part_one {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} (φ : Γ' →* Γ)
    (δ : Γ →* kˣ) (h1 : ∀ s, δ s = 1 ↔ s ∈ φ.range) (h2 : ∀ s, δ s = 1 ∨ δ s = -1) (r : Γ →* GL (Fin n) k)
    (hirr : IsIrr r) (hn : ¬ RepIso r (tw r δ)) : IsIrr (r.comp φ) := by
  refine ⟨hirr.1, fun _ _ _ => trivial, ?_⟩
  intro W _ hW
  by_contra hcon
  push Not at hcon
  obtain ⟨hW0, hW1⟩ := hcon
  apply hn
  by_cases hall : ∀ s, δ s = 1
  · refine ⟨1, fun s => ?_⟩
    apply Units.ext; simp [tw_val, hall s]
  push Not at hall
  obtain ⟨t, ht⟩ := hall
  have ht' : δ t = -1 := (h2 t).resolve_left ht
  let ρ : Γ → (Fin n → k) →ₗ[k] (Fin n → k) := fun s => Matrix.toLin' (r s : Matrix (Fin n) (Fin n) k)
  have hmul : ∀ a b v, ρ a (ρ b v) = ρ (a * b) v := by
    intro a b v
    simp [ρ, Matrix.toLin'_apply, Matrix.mulVec_mulVec]
  have a1 : ∀ s, δ s = 1 → ∀ v ∈ W, ρ s v ∈ W := by
    intro s hs v hv
    obtain ⟨x, rfl⟩ := (h1 s).1 hs
    exact hW x v hv
  have a2 : ∀ s, δ s = -1 → ∀ v ∈ W, ρ s v ∈ W.map (ρ t) := by
    intro s hs v hv
    refine ⟨ρ (t⁻¹ * s) v, a1 _ (by simp [hs, ht']) v hv, ?_⟩
    rw [hmul]; simp
  have a3 : ∀ s, δ s = 1 → ∀ v ∈ W.map (ρ t), ρ s v ∈ W.map (ρ t) := by
    rintro s hs _ ⟨v, hv, rfl⟩
    rw [hmul]; exact a2 _ (by simp [hs, ht']) v hv
  have a4 : ∀ s, δ s = -1 → ∀ v ∈ W.map (ρ t), ρ s v ∈ W := by
    rintro s hs _ ⟨v, hv, rfl⟩
    rw [hmul]; exact a1 _ (by simp [hs, ht']) v hv
  have hinf : W ⊓ W.map (ρ t) = ⊥ := by
    refine (hirr.2.2 _ le_top ?_).resolve_right (fun h => hW1 (top_le_iff.1 (h ▸ inf_le_left)))
    intro s v hv
    rcases h2 s with hs | hs
    · exact ⟨a1 s hs v hv.1, a3 s hs v hv.2⟩
    · exact ⟨a4 s hs v hv.2, a2 s hs v hv.1⟩
  have hsup : W ⊔ W.map (ρ t) = ⊤ := by
    refine (hirr.2.2 _ le_top ?_).resolve_left (fun h => hW0 (le_bot_iff.1 (h ▸ le_sup_left)))
    intro s v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    show ρ s (a + b) ∈ _
    rw [map_add]
    rcases h2 s with hs | hs
    · exact Submodule.add_mem_sup (a1 s hs a ha) (a3 s hs b hb)
    · rw [add_comm]; exact Submodule.add_mem_sup (a4 s hs b hb) (a2 s hs a ha)
  have hc : IsCompl W (W.map (ρ t)) := IsCompl.of_eq hinf hsup
  let P : (Fin n → k) →ₗ[k] (Fin n → k) := LinearMap.ofIsCompl hc W.subtype (-(W.map (ρ t)).subtype)
  have p1 : ∀ v ∈ W, P v = v := fun v hv => LinearMap.ofIsCompl_apply_left hc (u := ⟨v, hv⟩)
  have p2 : ∀ v ∈ W.map (ρ t), P v = -v := fun v hv => LinearMap.ofIsCompl_apply_right hc (v := ⟨v, hv⟩)
  have hdec : ∀ v : Fin n → k, ∃ a ∈ W, ∃ b ∈ W.map (ρ t), a + b = v := fun v =>
    Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top)
  have hPP : P ∘ₗ P = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
    simp [p1 a ha, p2 b hb]
  have hPr : ∀ s, (δ s : k) • (ρ s ∘ₗ P) = P ∘ₗ ρ s := by
    intro s
    refine LinearMap.ext fun v => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
    rcases h2 s with hs | hs
    · simp [p1 a ha, p2 b hb, hs, p1 _ (a1 s hs a ha), p2 _ (a3 s hs b hb)]
    · simp [p1 a ha, p2 b hb, hs, p2 _ (a2 s hs a ha), p1 _ (a4 s hs b hb), add_comm]
  have hM : LinearMap.toMatrix' P * LinearMap.toMatrix' P = 1 := by
    rw [← LinearMap.toMatrix'_comp, hPP, LinearMap.toMatrix'_id]
  refine ⟨⟨LinearMap.toMatrix' P, LinearMap.toMatrix' P, hM, hM⟩, fun s => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  have := congrArg LinearMap.toMatrix' (hPr s)
  simp only [map_smul, LinearMap.toMatrix'_comp, ρ, LinearMap.toMatrix'_toLin'] at this
  simp only [Units.val_mul, tw_val, Matrix.smul_mul]
  exact this

theorem UpperTheory.V.Br.resTwo :
    UpperTheory.V.Br.ResTwo := by
  intro Γ Γ' k _ _ _ _ _ n φ δ h1 h2 r
  exact ⟨part_one φ δ h1 h2 r, fun r' => part_two φ δ h1 h2 r r'⟩
end

