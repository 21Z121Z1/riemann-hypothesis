import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSplitPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzTypeCut
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def Narrow : Prop :=
  ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E'] [Algebra E Ω]
    [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 → normV w' = g ^ n →
    ∀ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' →
    ∀ (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K), Function.Surjective red →
      RingHom.ker red = w'.asIdeal →
    ∀ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ →
    ∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character →
      (∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
        τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) →
    ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
      ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        (rc (cls σ)).inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((θ (z ^ g ^ j) : ℂˣ) : ℂ))

theorem narrow_of_field (H : GlobalTheory.Published.DepthZeroTypeInertia) : Narrow :=
  fun E E' Ω _ _ _ _ _ _ _ _ _ _ _ g _ A w h w' h' rc hrc i hi n hn hg hN a' ha' K _ _ red hr hk θ hθ τ hτ hf σ hs =>
    (H E E' Ω g A w h w' h' rc hrc i hi n hn hg hN a' ha' K red hr hk θ hθ τ hτ hf σ hs).2

def LCusp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → ∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character →
    ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ → (cls σ).IsCusp

def LDepth : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime]
    (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, ∀ τ : FDRep ℂ (Gn g n),
    ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
      fixed (cls σ).rep (KOne (w.adicCompletion E) (Fin (cls σ).1)) ≠ ⊥

def LTame : Prop :=
  ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E'] [Algebra E Ω]
    [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 → normV w' = g ^ n →
    ∀ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' →
    ∀ (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K), Function.Surjective red →
      RingHom.ker red = w'.asIdeal →
    ∀ y : WD h, IsIrrWD y → IsTameWD y → y.lpDim = n →
    ∃ ξ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n ξ ∧
      ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        y.inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((ξ (z ^ g ^ j) : ℂˣ) : ℂ))

def LMatch : Prop :=
  ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E'] [Algebra E Ω]
    [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ n : ℕ, 0 < n → ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 → normV w' = g ^ n →
    ∀ a' : Weil h' →* (w'.adicCompletion E')ˣ, IsLocalArtin h' a' →
    ∀ (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K), Function.Surjective red →
      RingHom.ker red = w'.asIdeal →
    ∀ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ →
    ∀ τ : FDRep ℂ (Gn g n), IsCusp τ.character →
      (∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
        τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) →
    ∀ σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)),
      GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ →
    ∀ ξ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n ξ →
      (∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        (rc (cls σ)).inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((ξ (z ^ g ^ j) : ℂˣ) : ℂ))) →
      ∃ k : ℕ, ∀ z : Kˣ, ξ z = θ (z ^ g ^ k)

theorem prod_shift (f : ℕ → ℂ) (n : ℕ) (hf : ∀ j, f (j + n) = f j) (k : ℕ) :
    ∏ j ∈ Finset.range n, (X - C (f (j + k))) = ∏ j ∈ Finset.range n, (X - C (f j)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← ih]
    have h1 := Finset.prod_range_succ' (fun j => (X - C (f (j + k)) : ℂ[X])) n
    have h2 := Finset.prod_range_succ (fun j => (X - C (f (j + k)) : ℂ[X])) n
    have hper : f (n + k) = f (0 + k) := by rw [Nat.add_comm n k, hf, Nat.zero_add]
    rw [h2, hper] at h1
    have hne : (X - C (f (0 + k)) : ℂ[X]) ≠ 0 := X_sub_C_ne_zero _
    have h3 := mul_right_cancel₀ hne h1
    rw [h3]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Nat.add_right_comm, Nat.add_assoc]

theorem pow_card_units {E' : Type} [Field E'] [NumberField E'] (w' : HeightOneSpectrum (𝓞 E')) (g n : ℕ)
    (hN : normV w' = g ^ n) (K : Type) [Field K] (red : 𝓞 E' →+* K) (hr : Function.Surjective red)
    (hk : RingHom.ker red = w'.asIdeal) (hpos : 0 < g ^ n) (z : Kˣ) : z ^ g ^ n = z := by
  have e : (𝓞 E' ⧸ w'.asIdeal) ≃+* K :=
    (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hr)
  have hc : Nat.card K = g ^ n := by rw [← hN, normV, Nat.card_congr e.toEquiv]
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hc]; exact hpos.ne')
  letI := Fintype.ofFinite K
  have hcard : Fintype.card K = g ^ n := by rw [← Nat.card_eq_fintype_card, hc]
  ext
  rw [Units.val_pow_eq_pow_val, ← hcard, FiniteField.pow_card]

theorem narrow_of_leaves (H1 : LCusp) (H2 : LDepth) (H3 : LTame) (H4 : LMatch) : Narrow := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ _ _ g _ A w h w' h' rc hrc i hi n hn hg hN a' ha' K _ _ red hr hk θ hθ τ hτ hf σ hs
    t x z hxz hv
  obtain ⟨a, ha, ε, hε, hL⟩ := hrc
  have hrc' : IsRec h rc := ⟨a, ha, ε, hε, hL⟩
  have hc : IsIrrWD (rc (cls σ)) := (hL.cusp _).1 (H1 E w g i hi n hn τ hτ σ hs)
  have ht : IsTameWD (rc (cls σ)) := (hL.depth _).1 (H2 E w g i hi n τ σ hs)
  have hd : (rc (cls σ)).lpDim = n := hL.dim _
  obtain ⟨ξ, hξ, hξf⟩ := H3 E E' Ω g A w h w' h' i hi n hn hg hN a' ha' K red hr hk (rc (cls σ)) hc ht hd
  obtain ⟨k, hk'⟩ := H4 E E' Ω g A w h w' h' rc hrc' i hi n hn hg hN a' ha' K red hr hk θ hθ τ hτ hf σ hs ξ hξ hξf
  rw [hξf t x z hxz hv]
  have hpos : 0 < g ^ n := pow_pos (Fact.out : g.Prime).pos n
  have hz := pow_card_units w' g n hN K red hr hk hpos z
  have e1 : ∀ j, ((ξ (z ^ g ^ j) : ℂˣ) : ℂ) = ((θ (z ^ g ^ (j + k)) : ℂˣ) : ℂ) := fun j => by
    rw [hk', ← pow_mul, ← pow_add]
  simp_rw [e1]
  refine prod_shift (fun j => ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) n (fun j => ?_) k
  show ((θ (z ^ g ^ (j + n)) : ℂˣ) : ℂ) = ((θ (z ^ g ^ j) : ℂˣ) : ℂ)
  rw [pow_add, mul_comm, pow_mul, hz]

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.ExistsOfMemKOne
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Filter Topology GlobalTheory.GLp GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzIso

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}

theorem val_lt_iff (y : w.adicCompletion E) : valuation (w.adicCompletion E) y < 1 ↔ ‖y‖ < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.lt_one_iff_lt_one, Valued.toNormedField.norm_lt_one_iff]

theorem val_le_iff (y : w.adicCompletion E) : valuation (w.adicCompletion E) y ≤ 1 ↔ ‖y‖ ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.le_one_iff_le_one, Valued.toNormedField.norm_le_one_iff]

variable {g : ℕ} [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
include hi

theorem norm_lt_of_lt {x : ℚ_[g]} (hx : ‖x‖ < 1) : ‖i x‖ < 1 := by
  have h1 : Tendsto (fun k : ℕ => x ^ k) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx
  have h0 : Tendsto i (𝓝 0) (𝓝 0) := by simpa using hi.tendsto 0
  have h2 : Tendsto (fun k : ℕ => ‖i x‖ ^ k) atTop (𝓝 0) := by
    have := (h0.comp h1).norm
    simpa [Function.comp_def, map_pow, norm_pow] using this
  by_contra hc
  rw [not_lt] at hc
  obtain ⟨k, hk⟩ := (h2.eventually (gt_mem_nhds one_pos)).exists
  exact absurd hk (not_lt.2 (one_le_pow₀ hc))

theorem norm_le_of_le {x : ℚ_[g]} (hx : ‖x‖ ≤ 1) : ‖i x‖ ≤ 1 :=
  GlobalTheory.TypeRec.Model.emb_le w g i.toRingHom hi x hx

theorem norm_lt_iff (x : ℚ_[g]) : ‖i x‖ < 1 ↔ ‖x‖ < 1 := by
  refine ⟨fun h => ?_, norm_lt_of_lt i hi⟩
  by_contra hc
  rw [not_lt] at hc
  have hx0 : x ≠ 0 := fun e => by rw [e, norm_zero] at hc; exact absurd hc (by norm_num)
  have h1 : ‖x⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hc
  have h2 := norm_le_of_le i hi h1
  rw [map_inv₀, norm_inv] at h2
  have hpos : 0 < ‖i x‖ := norm_pos_iff.2 ((map_ne_zero i).2 hx0)
  have := (inv_le_one₀ hpos).1 h2
  exact absurd h (not_lt.2 this)

theorem norm_le_iff (x : ℚ_[g]) : ‖i x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  refine ⟨fun h => ?_, norm_le_of_le i hi⟩
  by_contra hc
  rw [not_le] at hc
  have hx0 : x ≠ 0 := fun e => by rw [e, norm_zero] at hc; exact absurd hc (by norm_num)
  have h1 : ‖x⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hc
  have h2 := norm_lt_of_lt i hi h1
  rw [map_inv₀, norm_inv] at h2
  have hpos : 0 < ‖i x‖ := norm_pos_iff.2 ((map_ne_zero i).2 hx0)
  have := (inv_lt_one₀ hpos).1 h2
  exact absurd h (not_le.2 this)

theorem valuation_lt_iff (x : ℚ_[g]) : valuation (w.adicCompletion E) (i x) < 1 ↔ ‖x‖ < 1 :=
  (val_lt_iff _).trans (norm_lt_iff i hi x)

theorem valuation_le_iff (x : ℚ_[g]) : valuation (w.adicCompletion E) (i x) ≤ 1 ↔ ‖x‖ ≤ 1 :=
  (val_le_iff _).trans (norm_le_iff i hi x)

theorem v_lt_iff (x : ℚ_[g]) : Valued.v (i x) < 1 ↔ ‖x‖ < 1 :=
  Valued.toNormedField.norm_lt_one_iff.symm.trans (norm_lt_iff i hi x)

theorem v_le_iff (x : ℚ_[g]) : Valued.v (i x) ≤ 1 ↔ ‖x‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.symm.trans (norm_le_iff i hi x)

omit hi in

theorem exists_ker_red {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ_[g])
    (h : ∀ a b, ‖M a b - (1 : Matrix (Fin n) (Fin n) ℚ_[g]) a b‖ < 1) :
    ∃ k : GL (Fin n) ℤ_[g], red g n k = 1 ∧ (inc g n k : Matrix (Fin n) (Fin n) ℚ_[g]) = M := by
  have hM : ∀ a b, ‖M a b‖ ≤ 1 := by
    intro a b
    have h1 := h a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.one_apply_eq] at h1
      have := IsUltrametricDist.norm_add_le_max (M a a - 1) (1 : ℚ_[g])
      rw [sub_add_cancel, norm_one] at this
      exact this.trans (max_le h1.le le_rfl)
    · rw [Matrix.one_apply_ne hab, sub_zero] at h1
      exact h1.le
  let A : Matrix (Fin n) (Fin n) ℤ_[g] := fun a b => ⟨M a b, hM a b⟩
  have hA : (PadicInt.toZMod (p := g)).mapMatrix A = 1 := by
    ext a b
    have hmem : A a b - (1 : Matrix (Fin n) (Fin n) ℤ_[g]) a b ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      have hc : ((A a b - (1 : Matrix (Fin n) (Fin n) ℤ_[g]) a b : ℤ_[g]) : ℚ_[g]) =
          M a b - (1 : Matrix (Fin n) (Fin n) ℚ_[g]) a b := by
        rw [PadicInt.coe_sub]
        by_cases hab : a = b
        · subst hab; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, PadicInt.coe_one]
        · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, PadicInt.coe_zero]
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def, hc]
      exact h a b
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hmem]
    by_cases hab : a = b <;> simp [hab, Matrix.one_apply]
  have hd : IsUnit A.det := by
    by_contra hn
    have hk : A.det ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
      exact mem_nonunits_iff.2 hn
    rw [RingHom.mem_ker, RingHom.map_det, hA, Matrix.det_one] at hk
    exact one_ne_zero hk
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det A).2 hd
  refine ⟨u, Units.ext ?_, ?_⟩
  · show (PadicInt.toZMod (p := g)).mapMatrix (u : Matrix (Fin n) (Fin n) ℤ_[g]) = 1
    rw [hu, hA]
  · show (algebraMap ℤ_[g] ℚ_[g]).mapMatrix (u : Matrix (Fin n) (Fin n) ℤ_[g]) = M
    rw [hu]
    ext a b
    rfl

theorem map_mem_KOne {n : ℕ} (k : GL (Fin n) ℤ_[g]) (hk : red g n k = 1) :
    Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k) ∈ KOne (w.adicCompletion E) (Fin n) := by
  rw [GlobalTheory.StepData.mem_KOne]
  intro a b
  have hk' : PadicInt.toZMod (k.val a b) = (1 : Matrix (Fin n) (Fin n) (ZMod g)) a b :=
    congrArg (fun x : GL (Fin n) (ZMod g) => (x : Matrix (Fin n) (Fin n) (ZMod g)) a b) hk
  have hn : ‖((k.val a b : ℤ_[g]) : ℚ_[g]) - (1 : Matrix (Fin n) (Fin n) ℚ_[g]) a b‖ < 1 := by
    have hmem : k.val a b - (1 : Matrix (Fin n) (Fin n) ℤ_[g]) a b ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [RingHom.mem_ker, map_sub, hk']
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    have hc : ((k.val a b - (1 : Matrix (Fin n) (Fin n) ℤ_[g]) a b : ℤ_[g]) : ℚ_[g]) =
        ((k.val a b : ℤ_[g]) : ℚ_[g]) - (1 : Matrix (Fin n) (Fin n) ℚ_[g]) a b := by
      rw [PadicInt.coe_sub]
      by_cases hab : a = b
      · subst hab; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, PadicInt.coe_one]
      · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, PadicInt.coe_zero]
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def, hc] at hmem
    exact hmem
  have hv := (valuation_lt_iff i hi _).2 hn
  have e : ((Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k)).val - 1) a b =
      i (((k.val a b : ℤ_[g]) : ℚ_[g]) - (1 : Matrix (Fin n) (Fin n) ℚ_[g]) a b) := by
    rw [Matrix.sub_apply, map_sub]
    refine congrArg₂ (· - ·) rfl ?_
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  rw [e]
  exact hv

theorem exists_of_mem_KOne {n : ℕ} {m : GL (Fin n) (w.adicCompletion E)}
    (hm : m ∈ KOne (w.adicCompletion E) (Fin n)) :
    ∃ k : GL (Fin n) ℤ_[g], red g n k = 1 ∧ Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k) = m := by
  have h1 := GlobalTheory.StepData.mem_KOne.1 hm
  obtain ⟨k, hk, hk'⟩ := exists_ker_red (i.symm.toRingHom.mapMatrix m.val) (fun a b => by
    have e : (i.symm.toRingHom.mapMatrix m.val) a b - (1 : Matrix (Fin n) (Fin n) ℚ_[g]) a b =
        i.symm ((m.val - 1) a b) := by
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab, map_sub]
    rw [e, ← valuation_lt_iff i hi, RingEquiv.apply_symm_apply]
    exact h1 a b)
  refine ⟨k, hk, Units.ext (Matrix.ext fun a b => ?_)⟩
  change i ((inc g n k : Matrix (Fin n) (Fin n) ℚ_[g]) a b) = m.val a b
  rw [hk']
  simp

theorem map_ker_red (n : ℕ) :
    ((red g n).ker.map (inc g n)).map (Matrix.GeneralLinearGroup.map i.toRingHom) =
      KOne (w.adicCompletion E) (Fin n) := by
  ext m
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact map_mem_KOne i hi k (MonoidHom.mem_ker.1 hk)
  · intro hm
    obtain ⟨k, hk, rfl⟩ := exists_of_mem_KOne i hi hm
    exact ⟨_, ⟨k, MonoidHom.mem_ker.2 hk, rfl⟩, rfl⟩

end DiscreteGroups.sglob.DzIso
end
end

