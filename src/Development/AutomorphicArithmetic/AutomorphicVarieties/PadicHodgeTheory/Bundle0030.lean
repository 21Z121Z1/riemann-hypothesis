import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaHecke
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

theorem UpperTheory.V.Loc.laHecke :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) (art : Neutral.B1.Ideles F →* Gab F Ω), IsGlobalArtin art → ∀ (ι : Qbar l ≃+* ℂ) (χ : Formalism.L2.Host.HChar F) (n : (F →+* ℂ) → ℤ) (μ : G F Ω →* (Qbar l)ˣ), IsLAdicOf art ι χ n μ → (∃ a, IsLocalArtin h a) → IsLocAlg h (μ.comp (Dec (F := F) A).subtype) fun τ => -n ((ι.toRingHom.comp τ.1).comp (algebraMap F (w.adicCompletion F))) := by
  intro F Ω _ _ _ _ _ l _ A w h art hart ι χ n μ hμ ⟨a0, ha0⟩
  have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' F Ω art hart w
  have hs : GlobalTheory.SmGL.IsSmoothChar (χ.loc w) := GlobalTheory.HeckeComp.smooth_loc χ w
  let φ : Ine (F := F) A →* ℂˣ := ((χ.loc w).comp a0).comp (ineIncl h)
  have hφ : IsOpen (φ.ker : Set (Ine (F := F) A)) := IsOpen.preimage ha0.cont hs
  refine ⟨((Units.map ι.symm.toRingHom.toMonoidHom).comp φ)⁻¹, ?_, fun a ha σ => ?_⟩
  · refine Subgroup.isOpen_mono (fun x hx => ?_) hφ
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [MonoidHom.inv_apply, MonoidHom.comp_apply, hx, map_one, inv_one]
  · have e : a (ineIncl h σ) = a0 (ineIncl h σ) :=
      hinj ((ha.glob art hart _).trans (ha0.glob art hart _).symm)
    have h1 := hμ.loc (a0 (ineIncl h σ)) _ (ha0.glob art hart _)
    have h0 : ι.symm ((χ.loc w (a0 (ineIncl h σ)) : ℂˣ) : ℂ) ≠ 0 := (map_ne_zero ι.symm).2 (Units.ne_zero _)
    rw [e, Units.val_mul, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    simp only [neg_neg]
    show ((μ (ineIncl h σ : Weil h) : (Qbar l)ˣ) : Qbar l) * (ι.symm ((χ.loc w (a0 (ineIncl h σ)) : ℂˣ) : ℂ))⁻¹ = locPow ι n w (a0 (ineIncl h σ))
    rw [h1, mul_comm, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaUnique
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

private theorem finite_emb {F : Type} [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (w : Plc F) :
    Finite (Emb l w) := by
  classical
  let φ : Emb l w → (F →+* Qbar l) := fun j =>
    (j.1).comp (algebraMap F (HeightOneSpectrum.adicCompletion F w))
  refine Finite.of_injective φ ?_
  intro i j hij
  apply Subtype.ext
  have hd := HeightOneSpectrum.denseRange_algebraMap (K := F) w
  have hfun : (i.1 : HeightOneSpectrum.adicCompletion F w → Qbar l) = j.1 :=
    hd.equalizer i.2 j.2 (funext fun x => DFunLike.congr_fun hij x)
  exact DFunLike.coe_injective hfun

private theorem lin_term {ι L : Type} [Fintype ι] [Field L] [CharZero L] (c : ι → L) (p q : ι → ℕ)
    (H : ∀ n : ℕ, ∏ i, (1 + c i * n) ^ p i = ∏ i, (1 + c i * n) ^ q i) :
    ∑ i, (p i : L) * c i = ∑ i, (q i : L) * c i := by
  classical
  open Polynomial in
  have hmul : ∀ f g : L[X], (f * g).coeff 1 = f.coeff 0 * g.coeff 1 + f.coeff 1 * g.coeff 0 := by
    intro f g
    rw [coeff_mul, Finset.Nat.antidiagonal_succ]
    simp [add_comm]
  have hlin : ∀ (a : L) (m : ℕ), ((1 + C a * X) ^ m).coeff 0 = 1 ∧ ((1 + C a * X) ^ m).coeff 1 = (m : L) * a := by
    intro a m
    induction m with
    | zero => simp [coeff_one]
    | succ m ih =>
      refine ⟨?_, ?_⟩
      · rw [pow_succ, mul_coeff_zero, ih.1]
        simp
      · rw [pow_succ, hmul, ih.1, ih.2]
        simp [coeff_one, coeff_C_mul_X]
        push_cast
        ring
  have hprod : ∀ (m : ι → ℕ) (s : Finset ι), (∏ i ∈ s, (1 + C (c i) * X) ^ m i).coeff 0 = 1 ∧
      (∏ i ∈ s, (1 + C (c i) * X) ^ m i).coeff 1 = ∑ i ∈ s, (m i : L) * c i := by
    intro m s
    induction s using Finset.induction_on with
    | empty => simp [coeff_one]
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj]
      refine ⟨?_, ?_⟩
      · rw [mul_coeff_zero, ih.1, (hlin (c j) (m j)).1, one_mul]
      · rw [hmul, ih.1, ih.2, (hlin (c j) (m j)).1, (hlin (c j) (m j)).2]
        ring
  have heq : (∏ i, (1 + C (c i) * X) ^ p i) = ∏ i, (1 + C (c i) * X) ^ q i := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := Set.range (fun n : ℕ => (n : L)))
    · rintro _ ⟨n, rfl⟩
      simp only [Set.mem_setOf_eq, eval_prod, eval_pow, eval_add, eval_one, eval_mul, eval_C, eval_X]
      exact H n
    · exact Set.infinite_range_of_injective Nat.cast_injective
  have h1 := congrArg (fun P : L[X] => P.coeff 1) heq
  rw [(hprod p Finset.univ).2, (hprod q Finset.univ).2] at h1
  exact h1

private theorem indep {ι k L Γ : Type} [Fintype ι] [Field k] [Field L] [CharZero L]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation k Γ) (π : k) (h0 : π ≠ 0) (h1 : v π < 1)
    (τ : ι → k →+* L) (hτ : Function.Injective τ) (e : ι → ℤ)
    (H : ∀ u : k, v u = 1 → ∏ i, τ i u ^ e i = 1) : e = 0 := by
  classical
  have hnat : ∀ n : ℕ, v (n : k) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      exact le_trans (v.map_add _ _) (max_le ih (by simp))
  have hS : ∀ y : k, v y < 1 → ∑ i, (e i : L) * τ i y = 0 := by
    intro y hy
    have key : ∀ n : ℕ, ∏ i, (1 + τ i y * n) ^ (e i).toNat = ∏ i, (1 + τ i y * n) ^ (-e i).toNat := by
      intro n
      have hlt : v ((n : k) * y) < 1 := by
        rw [v.map_mul]
        calc v (n : k) * v y ≤ 1 * v y := by gcongr; exact hnat n
          _ = v y := one_mul _
          _ < 1 := hy
      have hu : v (1 + (n : k) * y) = 1 := v.map_one_add_of_lt hlt
      have hu0 : (1 + (n : k) * y) ≠ 0 := by
        intro h0
        rw [h0, v.map_zero] at hu
        exact zero_ne_one hu
      have hx : ∀ i, τ i (1 + (n : k) * y) = 1 + τ i y * n := by
        intro i
        simp [map_add, map_mul, map_natCast, mul_comm]
      have hne : ∀ i, τ i (1 + (n : k) * y) ≠ 0 := fun i => (map_ne_zero (τ i)).2 hu0
      have h := H _ hu
      have hsplit : ∀ i, τ i (1 + (n : k) * y) ^ e i =
          τ i (1 + (n : k) * y) ^ (e i).toNat / τ i (1 + (n : k) * y) ^ (-e i).toNat := by
        intro i
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (hne i), Int.toNat_sub_toNat_neg]
      simp only [hsplit] at h
      rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hne i))] at h
      simpa only [hx] using h
    have h2 := lin_term (fun i => τ i y) (fun i => (e i).toNat) (fun i => (-e i).toNat) key
    have hcast : ∀ i, (e i : L) = ((e i).toNat : L) - ((-e i).toNat : L) := by
      intro i
      have := congrArg (fun z : ℤ => (z : L)) (Int.toNat_sub_toNat_neg (e i))
      push_cast at this
      exact this.symm
    simp only [hcast, sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.2 h2
  let R := v.integer
  let ρ : ι → (R →* L) := fun i => (τ i).toMonoidHom.comp R.subtype.toMonoidHom
  have hinj : Function.Injective ρ := by
    intro i j hij
    apply hτ
    ext x
    rcases le_or_gt (v x) 1 with hx | hx
    · have := DFunLike.congr_fun hij ⟨x, hx⟩
      simpa [ρ] using this
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      have hxi : v x⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact (inv_lt_one_of_one_lt₀ hx).le
      have := DFunLike.congr_fun hij ⟨x⁻¹, hxi⟩
      simp only [ρ, MonoidHom.coe_comp, Function.comp_apply] at this
      simpa [map_inv₀] using this
  have hli := (linearIndependent_monoidHom R L).comp ρ hinj
  rw [Fintype.linearIndependent_iff] at hli
  have hz := hli (fun i => (e i : L) * τ i π) (by
    funext a
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
    have ha : v (π * (a : k)) < 1 := by
      rw [v.map_mul]
      calc v π * v (a : k) ≤ v π * 1 := by gcongr; exact a.2
        _ = v π := mul_one _
        _ < 1 := h1
    have := hS _ ha
    simp only [map_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [ρ, mul_assoc])
  funext i
  have hi := hz i
  have hπ : τ i π ≠ 0 := (map_ne_zero (τ i)).2 h0
  have : (e i : L) = 0 := by
    rcases mul_eq_zero.1 hi with h | h
    · exact h
    · exact absurd h hπ
  simpa using this

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem UpperTheory.V.Loc.laUnique :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w), (∃ a, IsLocalArtin h a) → ∀ (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (wt wt' : Emb l w → ℤ), IsLocAlg h κ wt → IsLocAlg h κ wt' → wt = wt' := by
  intro F Ω _ _ _ _ _ l _ A w h ha0 κ wt wt' hw hw'
  classical
  obtain ⟨a, ha⟩ := ha0
  obtain ⟨ph, hph⟩ := hw
  obtain ⟨ph', hph'⟩ := hw'
  haveI : Finite (Emb l w) := finite_emb l w
  letI : Fintype (Emb l w) := Fintype.ofFinite _
  let K : Subgroup ↥(Ine (F := F) A) := ph.ker ⊓ ph'.ker
  haveI : CompactSpace ↥(Ine (F := F) A) :=
    isCompact_iff_compactSpace.mp (isClosed_Ine (F := F) A).isCompact
  have hKo : IsOpen (K : Set ↥(Ine (F := F) A)) := hph.1.inter hph'.1
  haveI : Finite (↥(Ine (F := F) A) ⧸ K) := Subgroup.quotient_finite_of_isOpen K hKo
  haveI : K.Normal := Subgroup.normal_inf_normal _ _
  have hm0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel : ∀ σ : ↥(Ine (F := F) A), ∏ τ : Emb l w,
      (τ.1 (a (ineIncl h σ) : HeightOneSpectrum.adicCompletion F w)) ^ ((K.index : ℤ) * (wt' τ - wt τ)) = 1 := by
    intro σ
    have hmem := K.pow_index_mem σ
    have hk1 : ph (σ ^ K.index) = 1 := hmem.1
    have hk2 : ph' (σ ^ K.index) = 1 := hmem.2
    have e1 := hph.2 a ha (σ ^ K.index)
    have e2 := hph'.2 a ha (σ ^ K.index)
    rw [hk1, mul_one] at e1
    rw [hk2, mul_one] at e2
    have e := e1.symm.trans e2
    rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype] at e
    simp only [map_pow, Units.val_pow_eq_pow_val] at e
    have hy : ((a (ineIncl h σ)) : HeightOneSpectrum.adicCompletion F w) ≠ 0 := Units.ne_zero _
    have hne : ∀ τ : Emb l w, τ.1 ((a (ineIncl h σ)) : HeightOneSpectrum.adicCompletion F w) ≠ 0 :=
      fun τ => (map_ne_zero τ.1).2 hy
    have hsp : ∀ τ : Emb l w, τ.1 ((a (ineIncl h σ)) : HeightOneSpectrum.adicCompletion F w) ^ ((K.index : ℤ) * (wt' τ - wt τ)) =
        (τ.1 ((a (ineIncl h σ)) : HeightOneSpectrum.adicCompletion F w) ^ K.index) ^ (-wt τ) /
        (τ.1 ((a (ineIncl h σ)) : HeightOneSpectrum.adicCompletion F w) ^ K.index) ^ (-wt' τ) := by
      intro τ
      rw [← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_sub₀ (hne τ)]
      congr 1
      ring
    simp only [hsp]
    rw [Finset.prod_div_distrib, e, div_self (Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (pow_ne_zero _ (hne τ)))]
  obtain ⟨γ, hγ0, hγ1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := HeightOneSpectrum.adicCompletion F w)
  obtain ⟨π, hπ⟩ := ValuativeRel.valuation_surjective γ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact hγ0.ne hπ
  have he := indep (ValuativeRel.valuation (HeightOneSpectrum.adicCompletion F w)) π hπ0 (hπ ▸ hγ1)
    (fun τ : Emb l w => τ.1) Subtype.val_injective (fun τ => (K.index : ℤ) * (wt' τ - wt τ)) (by
      intro u hu
      have hu0 : u ≠ 0 := by
        rintro rfl
        rw [map_zero] at hu
        exact zero_ne_one hu
      have hord : GlobalTheory.SmGL.ord _ (Units.mk0 u hu0) = 0 := GlobalTheory.SmGL.ord_eq_zero_iff.2 (by simpa using hu)
      obtain ⟨ρ, hρ⟩ := ha.surj (Units.mk0 u hu0)
      have hdeg : deg ρ = 0 := by
        have := ha.ord_eq ρ
        rw [hρ, hord] at this
        omega
      have hI : (ρ : G F Ω) ∈ Ine (F := F) A :=
        actsAs_zero_iff.1 (actsAs_of_deg (a := 0) (b := 0) (by simp [hdeg]))
      have hr : ineIncl h ⟨(ρ : G F Ω), hI⟩ = ρ := Subtype.ext rfl
      have := hrel ⟨(ρ : G F Ω), hI⟩
      rw [hr, hρ] at this
      simpa using this)
  funext τ
  have hτ := congrFun he τ
  simp only [Pi.zero_apply, mul_eq_zero, Nat.cast_eq_zero] at hτ
  rcases hτ with hτ | hτ
  · exact absurd hτ hm0
  · exact (sub_eq_zero.1 hτ).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaWDDefs
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

def UpperTheory.V.Loc.HasLT {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (ι : Qbar l ≃+* ℂ)
    (wt : Emb l w → ℤ) (a : Weil h →* (w.adicCompletion F)ˣ) : Prop :=
  ∃ (μ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (ξ : Weil h →* ℂˣ), Continuous μ ∧ IsSmooth ξ ∧
    GlobalTheory.Pst.IsPstAt (UpperTheory.V.Loc.PP l) Bw (GlobalTheory.TripleGal.rk1 μ) ∧
    (∀ σ, (ξ σ : ℂ) = ι ((μ (Subgroup.inclusion (Weil_le_Dec h) σ) : Qbar l) *
      ∏ᶠ τ : Emb l w, τ.1 (a σ : w.adicCompletion F) ^ wt τ)) ∧
    ∀ σ, (ξ σ : ℂ) ∈ (GlobalTheory.Pst.wdAt (UpperTheory.V.Loc.PP l) ι Bw h hj (GlobalTheory.TripleGal.rk1 μ)).eig σ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PotCrysOf
section
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

private theorem cr_transport {l : ℕ} [Fact l.Prime] {G G' A V : Type} [Group G] [Group G'] [CommRing A]
    [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]
    {φ : G →* GQ l} {ρ : Representation A G V} {φ' : G' →* GQ l} {ρ' : Representation A G' V}
    (e : G → G') (he : Function.Surjective e) (h1 : ∀ g, φ' (e g) = φ g)
    (h2 : ∀ g x, ρ' (e g) x = ρ g x) : IsCr φ ρ → IsCr φ' ρ' := by
  have hr : φ.range = φ'.range := by
    ext σ
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨e g, h1 g⟩
    · rintro ⟨g, rfl⟩
      obtain ⟨g, rfl⟩ := he g
      exact ⟨g, (h1 g).symm⟩
  have hρ : ∀ g, resCoef ℚ_[l] ρ' (e g) = resCoef ℚ_[l] ρ g := fun g => LinearMap.ext fun x => h2 g x
  have hc : Dcr φ (resCoef ℚ_[l] ρ) = Dcr φ' (resCoef ℚ_[l] ρ') := by
    unfold Dcr
    rw [he.iInf_comp (fun g => LinearMap.ker (actC φ' (resCoef ℚ_[l] ρ') g - LinearMap.id)) |>.symm]
    refine iInf_congr fun g => ?_
    unfold actC
    rw [hρ, h1]
  unfold IsCr
  rw [hr, hc]
  exact id

private theorem crys_of_isCr {l : ℕ} [Fact l.Prime] (K E' : FinExt l) {n : ℕ}
    (ρ : Representation ↥E'.1 ↥(GK K) (Fin n → ↥E'.1)) (h : IsCr (GK K).subtype ρ) :
    Formalism.WeaklyAdmissibleFiltrations.IsCrys ((PP l).PD K) ρ := by
  have := E'.2
  have : IsModuleTopology ℚ_[l] (Fin n → ↥E'.1) := isModuleTopologyOfFiniteDimensional
  exact (isCrField K ρ).1.1 ((isCrIff K ρ).1.1 h)

private theorem ex_bridge {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} (j : Ω →+* Om l) (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) :
    ∃ (L : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL L)), Bw.j = j ∧
      Bw.Kw.1 = IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)) := by
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
      eO_symm_cont := continuous_id }, rfl, rfl⟩

theorem UpperTheory.V.Loc.potCrysOf :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (j : Ω →+* Om l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : H →* GQ l) (ψ : H →* G F Ω), IsOpenEmbedding φ → (∀ h y, φ h (j y) = j (ψ h y)) → ∀ {n : ℕ} (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r → ∀ (E' : FinExt l) (r' : H →* GL (Fin n) ↥E'.1), (∀ h a b, (((r' h : Matrix (Fin n) (Fin n) ↥E'.1) a b : ↥E'.1) : Om l) = (r (ψ h) : Matrix (Fin n) (Fin n) (Qbar l)) a b) → IsCr φ (colRep r') → UpperTheory.V.Af.PotCrysAt r (placeJ j) := by
  intro F Ω _ _ _ _ _ _ l _ j H _ _ _ φ ψ hφ hφψ n r hr E' r' hr' hcr
  have hj : ∀ x, x ∈ placeJ j ↔ ‖j x‖ ≤ 1 := fun x => by
    change Valued.v (j x) ≤ 1 ↔ _
    rw [PadicAlgCl.valuation_def]
    exact Iff.rfl
  obtain ⟨L, Bw, hBj, hK⟩ := ex_bridge (E := F) j hj
  refine ⟨↥(OL L), inferInstance, inferInstance, inferInstance, Bw, fun x => by rw [hBj]; exact hj x, ?_⟩
  haveI : CompactSpace ↥(GK Bw.Kw) := by
    haveI := Bw.Kw.2
    exact isCompact_iff_compactSpace.1 Bw.Kw.1.fixingSubgroup_isClosed.isCompact
  haveI : CompactSpace ↥(Dec (F := F) (placeJ j)) :=
    Bw.e.symm.surjective.compactSpace Bw.e_symm_cont
  haveI : T2Space ↥(Dec (F := F) (placeJ j)) := inferInstance
  let r₀ := r.comp (Dec (F := F) (placeJ j)).subtype
  have hc0 : Continuous fun g => ((r₀ g : GL (Fin n) (Om l)) : Matrix (Fin n) (Fin n) (Om l)) :=
    Units.continuous_val.comp (hr.comp continuous_subtype_val)
  obtain ⟨LL, hL, hent⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l _ n r₀ hc0 (GlobalTheory.Pst.supExt Bw.LL E')
  obtain ⟨r₁, hr₁⟩ := GlobalTheory.CompactRepField.exists_hom_of_entries_mem r₀ LL.1 hent
  have l₁ : Bw.LL.1 ≤ LL.1 := le_trans le_sup_left hL
  have l₂ : E'.1 ≤ LL.1 := le_trans le_sup_right hL
  refine ⟨LL, r₁, ⟨l₁, ?_⟩, ?_⟩
  · ext g a b
    exact hr₁ g a b
  obtain ⟨K, e, -, -, he, hKr, -, -⟩ := openField φ hφ
  have he' : ∀ g, ((e g : ↥(GK K)) : GQ l) = φ g := fun g => DFunLike.congr_fun he g
  have hle : GK K ≤ GK Bw.Kw := by
    rw [← hKr]
    rintro _ ⟨g, rfl⟩
    rw [GlobalTheory.PlaceBridge.mem_GK_iff Bw.Kw hK]
    intro x
    rw [hφψ, AlgEquiv.commutes]
  have h : Bw.Kw.1 ≤ K.1 := by
    have : IsGalois ℚ_[l] (Om l) := inferInstance
    rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, ← InfiniteGalois.fixedField_fixingSubgroup Bw.Kw.1]
    exact IntermediateField.fixedField_le hle
  refine ⟨K, h, ?_⟩
  let ρK : Representation ↥E'.1 ↥(GK K) (Fin n → ↥E'.1) := (colRep r').comp e.symm.toMonoidHom
  have t1 : IsCr (GK K).subtype ρK := cr_transport e e.surjective he' (fun g x => by simp [ρK]) hcr
  have t2 := crys_of_isCr K E' ρK t1
  let _ : Algebra ↥E'.1 ↥LL.1 := (IntermediateField.inclusion l₂).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥E'.1 ↥LL.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := LL.2
  have : FiniteDimensional ↥E'.1 ↥LL.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  refine (GlobalTheory.Pst.isCrys_ext_iff _ (ρ := ρK) fun g => ⟨r' (e.symm g), fun _ => rfl, fun x => ?_⟩).2 t2
  have hg : ((Bw.e.symm (Subgroup.inclusion (GK_le h) g) : ↥(Dec (F := F) (placeJ j))) : G F Ω) = ψ (e.symm g) := by
    apply AlgEquiv.ext
    intro y
    apply j.injective
    have h1 := Bw.e_comm (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) y
    rw [hBj, MulEquiv.apply_symm_apply] at h1
    rw [← h1, ← hφψ, ← he', MulEquiv.apply_symm_apply]
    rfl
  have hM : (r₁ (Bw.e.symm (Subgroup.inclusion (GK_le h) g)) : Matrix (Fin n) (Fin n) ↥LL.1) =
      (r' (e.symm g) : Matrix (Fin n) (Fin n) ↥E'.1).map (algebraMap ↥E'.1 ↥LL.1) := by
    ext a b
    rw [hr₁]
    refine Eq.trans ?_ (hr' (e.symm g) a b).symm
    rw [← hg]
    rfl
  rw [← hM]
  rfl
end

