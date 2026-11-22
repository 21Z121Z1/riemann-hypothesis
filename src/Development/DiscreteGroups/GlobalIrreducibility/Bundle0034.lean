import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0169
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0726
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0009
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0030
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalCongruenceFixedVectorsLeSmoothVectors
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import GroundTheory.LocalFields.LocalFourierPadic

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzTameRec
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Neutral.B1
  GlobalTheory.HeckeGal

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Tame

variable {M Ω : Type} [Field M] [NumberField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 M)}

theorem normV_mem (v : HeightOneSpectrum (𝓞 M)) : ((normV v : ℕ) : 𝓞 M) ∈ v.asIdeal := by
  have : Finite (𝓞 M ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  let := Fintype.ofFinite (𝓞 M ⧸ v.asIdeal)
  have hc : ((Fintype.card (𝓞 M ⧸ v.asIdeal) : ℕ) : 𝓞 M ⧸ v.asIdeal) = 0 := Nat.cast_card_eq_zero _
  rw [← Nat.card_eq_fintype_card] at hc
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact hc

omit [IsAlgClosure M Ω] in

theorem weil_fix_root (h : IsPlaceOver A v) (s : Weil h) (ζ : Ω) (hζ : ζ ^ (normV v - 1) = 1) :
    (s : G M Ω) ζ = ζ := by
  have hq : 1 < normV v := one_lt_normV v
  have hζi : IsIntegral ℤ ζ := IsIntegral.of_pow (n := normV v - 1) (by omega) (by rw [hζ]; exact isIntegral_one)
  have hζA : A.valuation ζ ≤ 1 := (A.valuation_le_one_iff _).2 (ReciprocityTheory.Gal.mem_of_isIntegral_int A hζi)
  have hζ1 : ζ ^ normV v = ζ := by
    have : normV v = (normV v - 1) + 1 := by omega
    rw [this, pow_succ, hζ, one_mul]
  have hpow : ∀ (y : Ω), y ^ normV v = y → ∀ k : ℕ, y ^ (normV v ^ k) = y := by
    intro y hy k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, hy]
  have hsζ : ((s : G M Ω) ζ) ^ (normV v - 1) = 1 := by rw [← map_pow, hζ, map_one]
  have hsζ1 : ((s : G M Ω) ζ) ^ normV v = (s : G M Ω) ζ := by
    have : normV v = (normV v - 1) + 1 := by omega
    rw [this, pow_succ, hsζ, one_mul]
  obtain ⟨a, b, hab⟩ := s.2
  have hc := hab.2 ζ hζA
  rw [hpow _ hsζ1, hpow _ hζ1] at hc
  have hsA : A.valuation ((s : G M Ω) ζ) ≤ 1 := by
    rw [A.valuation_le_one_iff, ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hab.1, ← A.valuation_le_one_iff]
    exact hζA
  have hval1 : A.valuation ζ = 1 := by
    refine le_antisymm hζA (not_lt.1 fun hlt => ?_)
    have := pow_lt_one₀ zero_le hlt (show normV v - 1 ≠ 0 by omega)
    rw [← map_pow, hζ, map_one] at this
    exact lt_irrefl _ this
  have hqA : A.valuation ((normV v : ℕ) : Ω) < 1 := by
    have := (h ((normV v : ℕ) : 𝓞 M)).2 (normV_mem v)
    simpa using this
  have hd : ¬ A.valuation (aeval ζ (derivative (X ^ (normV v - 1) - 1 : ℤ[X]))) < 1 := by
    have e : aeval ζ (derivative (X ^ (normV v - 1) - 1 : ℤ[X])) =
        (((normV v - 1 : ℕ) : Ω)) * ζ ^ (normV v - 1 - 1) := by
      simp [derivative_X_pow]
    rw [e, map_mul, map_pow, hval1, one_pow, mul_one]
    have e2 : (((normV v - 1 : ℕ) : Ω)) = -1 + ((normV v : ℕ) : Ω) := by
      rw [Nat.cast_sub hq.le]; ring
    have h' : A.valuation ((normV v : ℕ) : Ω) < A.valuation (-1 : Ω) := by
      rw [Valuation.map_neg, map_one]; exact hqA
    rw [e2, Valuation.map_add_eq_of_lt_left _ h', Valuation.map_neg, map_one]
    exact lt_irrefl _
  exact (GlobalTheory.eq_of_root_congr_of_deriv_unit A (X ^ (normV v - 1) - 1) ζ ((s : G M Ω) ζ) hζA hsA
    (by simp [hζ]) (by simp [hsζ]) hd (by rw [Valuation.map_sub_swap]; exact hc)).symm

end Tame

theorem lTameRec : LTameRec := by
  intro hA hC M Ω _ _ _ _ _ _ g _ A v h hg1 hg2 a ha π hπ t x hx
  classical
  have hq : 1 < normV v := one_lt_normV v
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap M Ω).injective
  have : NeZero (normV v - 1) := ⟨by omega⟩
  have hg0 : ((g : ℕ) : Ω) ≠ 0 := by exact_mod_cast (Fact.out : g.Prime).ne_zero
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hπ
    exact hg0 hπ.symm

  let f : Weil h →* rootsOfUnity (normV v - 1) Ω :=
    { toFun := fun s => ⟨Units.mk0 ((s : G M Ω) π / π) (div_ne_zero ((_root_.map_ne_zero _).2 hπ0) hπ0), by
          rw [mem_rootsOfUnity]
          ext
          simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
          rw [div_pow, ← map_pow, hπ, map_natCast, div_self hg0]⟩
      map_one' := by
        ext
        simp [div_self hπ0]
      map_mul' := fun s s' => by
        ext
        simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul, Subgroup.coe_mul, AlgEquiv.mul_apply]
        have hr : (((s' : G M Ω) π / π)) ^ (normV v - 1) = 1 := by
          rw [div_pow, ← map_pow, hπ, map_natCast, div_self hg0]
        have hfix := weil_fix_root h s _ hr
        have e : (s : G M Ω) ((s' : G M Ω) π) = (s : G M Ω) (((s' : G M Ω) π / π) * π) := by
          rw [div_mul_cancel₀ _ hπ0]
        rw [e, map_mul, hfix]
        field_simp }
  have hf : ∀ s s' : Weil h, f s = f s' → (s : G M Ω) π = (s' : G M Ω) π := fun s s' hss => by
    have := congrArg (fun z : rootsOfUnity (normV v - 1) Ω => ((z : Ωˣ) : Ω)) hss
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0] at this
    exact (div_left_inj' hπ0).1 this
  let d := Nat.card (rootsOfUnity (normV v - 1) Ω)
  have hd : 0 < d := Nat.card_pos
  have : NeZero d := ⟨hd.ne'⟩
  let e : rootsOfUnity (normV v - 1) Ω ≃* rootsOfUnity d ℂ :=
    mulEquivOfCyclicCardEq (Complex.card_rootsOfUnity d).symm
  let η : Weil h →* ℂˣ := (rootsOfUnity d ℂ).subtype.comp (e.toMonoidHom.comp f)
  have hη : ∀ s s' : Weil h, η s = η s' → (s : G M Ω) π = (s' : G M Ω) π := fun s s' hss =>
    hf s s' (e.injective (Subtype.ext hss))

  have hπi : IsIntegral M π := Algebra.IsIntegral.isIntegral π
  have : FiniteDimensional M (IntermediateField.adjoin M ({π} : Set Ω)) :=
    IntermediateField.adjoin.finiteDimensional hπi
  have hηs : IsSmooth η := by
    let H1 : Subgroup (Ine (F := M) A) :=
      (IntermediateField.adjoin M ({π} : Set Ω)).fixingSubgroup.comap (Ine (F := M) A).subtype
    have hH1 : IsOpen (H1 : Set (Ine (F := M) A)) :=
      (IntermediateField.fixingSubgroup_isOpen _).preimage continuous_subtype_val
    have hle : H1 ≤ (η.comp (ineIncl h)).ker := fun σ hσ => by
      have hσπ : (σ : G M Ω) π = π :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ π (IntermediateField.mem_adjoin_simple_self _ _)
      have h1 : f (ineIncl h σ) = 1 := by
        ext
        simp [f, hσπ, div_self hπ0]
      show η (ineIncl h σ) = 1
      simp [η, h1]
    exact Subgroup.isOpen_mono hle hH1
  obtain ⟨χ, -, hχ⟩ := ha.factor η hηs

  obtain ⟨art, hart⟩ := hA M Ω
  have hπ' : π ^ (normV v - 1) = algebraMap M Ω (((g : ℕ) : 𝓞 M) : M) := by rw [hπ]; simp
  obtain ⟨σ, hσI, hσab, hσπ⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hA M Ω art hart v A h ((g : ℕ) : 𝓞 M) hg1 hg2 π
    hπ' (a (ineIncl h t)) x (GlobalTheory.ArtinInertia.isUnitAt_artin_ine h a ha t) hx
  let σ' : Ine (F := M) A := ⟨σ, hσI⟩
  have e1 : art (localIdele M v (a (ineIncl h σ'))) = art (localIdele M v (a (ineIncl h t))) := by
    rw [ha.glob art hart, ha.glob art hart]
    exact hσab.trans (ha.glob art hart (ineIncl h t))
  have e2 : a (ineIncl h σ') = a (ineIncl h t) := GlobalTheory.T.globalArtin_localIdele_injective hC M Ω art hart v e1
  have e3 : η (ineIncl h σ') = η (ineIncl h t) := by
    rw [hχ, MonoidHom.comp_apply, MonoidHom.comp_apply, e2]
  have e4 := hη _ _ e3
  have e5 : (t : G M Ω) π = σ π := e4.symm
  rw [e5]
  exact hσπ

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzTwChar
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzTw

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

include hi

def resMap : IsLocalRing.ResidueField 𝒪[w.adicCompletion E] →+* ZMod g :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal 𝒪[w.adicCompletion E]) (DzIso.redO i hi) fun a ha => by
    rw [← RingHom.mem_ker, DzIso.ker_redO i hi]
    exact ha

theorem norm_unit (u : ℤ_[g]ˣ) : ‖((u : ℤ_[g]) : ℚ_[g])‖ = 1 := by
  rw [← PadicInt.norm_def]
  exact PadicInt.isUnit_iff.1 u.isUnit

theorem exists_liftsChar (χ₀ : (ZMod g)ˣ →* ℂˣ) :
    ∃ χ : (w.adicCompletion E)ˣ →* ℂˣ, IsSmoothChar χ ∧ DiscreteGroups.sglob.DzType.LiftsChar i χ₀ χ := by
  have hne : ((g : ℕ) : w.adicCompletion E) ≠ 0 := fun h => by
    have := DzIso.valuation_natCast_eq_uniformizer i hi
    rw [h, map_zero] at this
    exact uniformizer_ne_zero this.symm
  have hϖ : valuation (w.adicCompletion E) ((Units.mk0 _ hne : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      uniformizer (w.adicCompletion E) := by
    rw [Units.val_mk0]
    exact DzIso.valuation_natCast_eq_uniformizer i hi
  obtain ⟨χ, hl, h1⟩ := GlobalTheory.LocGL.exists_isTameLift (k := w.adicCompletion E)
    (χ₀.comp (Units.map (resMap i hi).toMonoidHom)) hϖ 1
  refine ⟨χ, GlobalTheory.LocGL.isSmoothChar_of_isTame hl.isTame, fun u x hx => ?_, fun x hx => ?_⟩
  · have hv : valuation (w.adicCompletion E) (x : w.adicCompletion E) = 1 := by
      rw [hx]
      refine le_antisymm ((DzIso.valuation_le_iff i hi _).2 (norm_unit i hi u).le) (not_lt.1 fun hlt => ?_)
      have := (DzIso.valuation_lt_iff i hi _).1 hlt
      rw [norm_unit i hi u] at this
      exact lt_irrefl _ this
    obtain ⟨v, hv'⟩ := GlobalTheory.LocGL.valuation_eq_one_iff.1 hv
    have hx' : ((v : 𝒪[w.adicCompletion E]) : w.adicCompletion E) = (x : w.adicCompletion E) :=
      congrArg Units.val hv'
    rw [← hv', hl v]
    show χ₀ _ = χ₀ _
    refine congrArg χ₀ (Units.ext ?_)
    show PadicInt.toZMod (DzIso.toInt i hi (v : 𝒪[w.adicCompletion E])) = PadicInt.toZMod (u : ℤ_[g])
    congr 1
    apply PadicInt.ext
    rw [DzIso.coe_toInt, hx', hx, RingEquiv.symm_apply_apply]
  · have : x = Units.mk0 _ hne := Units.ext (by rw [hx, Units.val_mk0])
    rw [this, h1]

end DiscreteGroups.sglob.DzTw
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzTwFin
section
noncomputable section

open Polynomial GlobalTheory.GLq GlobalTheory.SmGL CategoryTheory

namespace DiscreteGroups.sglob.DzTw

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

def twFD (τ : FDRep ℂ (Gn g n)) (χ₀ : (ZMod g)ˣ →* ℂˣ) : FDRep ℂ (Gn g n) :=
  FDRep.of (twist τ.ρ (detChar (Fin n) χ₀))

theorem character_twFD (τ : FDRep ℂ (Gn g n)) (χ₀ : (ZMod g)ˣ →* ℂˣ) (y : Gn g n) :
    (twFD τ χ₀).character y = ((χ₀ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * τ.character y := by
  change LinearMap.trace ℂ τ (((detChar (Fin n) χ₀ y : ℂˣ) : ℂ) • τ.ρ y) =
    ((χ₀ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * LinearMap.trace ℂ τ (τ.ρ y)
  rw [map_smul, smul_eq_mul, detChar_apply]

theorem simple_of_char {G : Type} [Group G] [Fintype G] {V W : FDRep ℂ G} (hV : Simple V)
    (h : ∀ x, W.character x * W.character x⁻¹ = V.character x * V.character x⁻¹) : Simple W := by
  have hc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hc' : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_pos.ne'
  have := invertibleOfNonzero hc
  have := invertibleOfNonzero hc'
  rw [FDRep.simple_iff_char_is_norm_one] at hV ⊢
  simpa only [h] using hV

theorem char_twFD_mul (τ : FDRep ℂ (Gn g n)) (χ₀ : (ZMod g)ˣ →* ℂˣ) (x : Gn g n) :
    (twFD τ χ₀).character x * (twFD τ χ₀).character x⁻¹ = τ.character x * τ.character x⁻¹ := by
  have hu : ((χ₀ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * ((χ₀ (Matrix.GeneralLinearGroup.det x⁻¹) : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, Units.val_one]
  rw [character_twFD, character_twFD]
  calc _ = (((χ₀ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * ((χ₀ (Matrix.GeneralLinearGroup.det x⁻¹) : ℂˣ) : ℂ)) *
        (τ.character x * τ.character x⁻¹) := by ring
    _ = _ := by rw [hu, one_mul]

theorem det_eq_one_of_mem {N a : ℕ} {u : GL (Fin N) (ZMod g)}
    (hu : u ∈ GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks N a)) : Matrix.GeneralLinearGroup.det u = 1 := by
  have hu' := GlobalTheory.FiniteGL.mem_unipRadical.1 hu
  have hmono : ∀ i j : Fin N, j < i → GlobalTheory.FiniteGL.twoBlocks N a j ≤ GlobalTheory.FiniteGL.twoBlocks N a i := by
    intro i j hij
    have : (j : ℕ) < i := hij
    simp only [GlobalTheory.FiniteGL.twoBlocks]
    split_ifs <;> omega
  have hT : (u : Matrix (Fin N) (Fin N) (ZMod g)).BlockTriangular id := by
    intro i j hij
    have h := hu' i j (hmono i j hij)
    have hne : i ≠ j := fun e => by rw [e] at hij; exact lt_irrefl _ hij
    rwa [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at h
  have hd : ∀ i, (u : Matrix (Fin N) (Fin N) (ZMod g)) i i = 1 := by
    intro i
    have h := hu' i i le_rfl
    rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular hT]
  simp [hd]

theorem res_twFD (τ : FDRep ℂ (Gn g n)) (χ₀ : (ZMod g)ˣ →* ℂˣ) {a : ℕ} (ha : a < n) :
    res a (n - a) (twFD τ χ₀).character 1 1 = res a (n - a) τ.character 1 1 := by
  unfold res
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = ((1 : Gn g a) : Mt g a) ∧
      br a (n - a) (x : Mt g n) = ((1 : Gn g (n - a)) : Mt g (n - a))
  · rw [if_pos hx, if_pos hx, character_twFD,
      det_eq_one_of_mem ((GlobalTheory.SerSys.TameGen.mem_unipRadical_iff ha x).2 hx), map_one, Units.val_one, one_mul]
  · rw [if_neg hx, if_neg hx]

theorem isCusp_twFD (τ : FDRep ℂ (Gn g n)) (χ₀ : (ZMod g)ˣ →* ℂˣ) (hτ : IsCusp τ.character) :
    IsCusp (twFD τ χ₀).character := by
  obtain ⟨hn, ⟨V, hV, hVc⟩, hres⟩ := hτ
  have hsτ : Simple τ := simple_of_char hV (fun x => by rw [hVc, hVc])
  refine ⟨hn, ⟨twFD τ χ₀, simple_of_char hsτ (fun x => char_twFD_mul τ χ₀ x), fun _ => rfl⟩, fun a h0 ha => ?_⟩
  rw [res_twFD τ χ₀ ha]
  exact hres a h0 ha

theorem det_eq_norm (K : Type) [Field K] [Algebra (ZMod g) K] (hK : Nat.card K = g ^ n) (hn : 0 < n) (y : Gn g n)
    (hy : Irreducible (y : Mt g n).charpoly) (z : Kˣ) (hz : aeval (z : K) (y : Mt g n).charpoly = 0) :
    Matrix.GeneralLinearGroup.det y = Units.map (Algebra.norm (ZMod g) : K →* ZMod g) z := by
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (by omega))
  letI : Fintype K := Fintype.ofFinite K
  haveI : Module.Finite (ZMod g) K := by
    first
    | exact Module.finite_of_finite (ZMod g)
    | exact inferInstance
  have hfr : Module.finrank (ZMod g) K = n := by
    have h1 : Fintype.card K = Fintype.card (ZMod g) ^ Module.finrank (ZMod g) K := by
      first
      | exact Module.card_eq_pow_finrank
      | exact card_eq_pow_finrank
    rw [ZMod.card] at h1
    have h2 : Fintype.card K = g ^ n := by rw [← Nat.card_eq_fintype_card, hK]
    exact Nat.pow_right_injective hg (h1.symm.trans h2)
  have hmon : ((y : Mt g n).charpoly).Monic := Matrix.charpoly_monic _
  have hdeg : ((y : Mt g n).charpoly).natDegree = n := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hmin : (y : Mt g n).charpoly = minpoly (ZMod g) (z : K) := minpoly.eq_of_irreducible_of_monic hy hz hmon
  have hint : IsIntegral (ZMod g) (z : K) := Algebra.IsIntegral.isIntegral _
  have hfr2 : Module.finrank (IntermediateField.adjoin (ZMod g) {(z : K)}) K = 1 := by
    have h3 := IntermediateField.adjoin.finrank hint
    have h4 := Module.finrank_mul_finrank (ZMod g) (IntermediateField.adjoin (ZMod g) {(z : K)}) K
    rw [h3, ← hmin, hdeg, hfr] at h4
    exact Nat.eq_of_mul_eq_mul_left hn (h4.trans (mul_one n).symm)
  have hnorm : Algebra.norm (ZMod g) (z : K) = (-1) ^ n * ((y : Mt g n).charpoly).coeff 0 := by
    rw [Algebra.norm_eq_norm_adjoin (ZMod g) (z : K), hfr2, pow_one]
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hint)
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_dim,
      IntermediateField.minpoly_gen] at this
    rw [this, ← hmin, hdeg]
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin]
  exact hnorm.symm

theorem units_pow_card_pow (u : (ZMod g)ˣ) (j : ℕ) : u ^ g ^ j = u :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, ZMod.pow_card_pow])

theorem nmChar_pow (K : Type) [Field K] [Algebra (ZMod g) K] (χ₀ : (ZMod g)ˣ →* ℂˣ) (j : ℕ) :
    (DiscreteGroups.sglob.DzType.nmChar K χ₀) ^ g ^ j = DiscreteGroups.sglob.DzType.nmChar K χ₀ := by
  refine MonoidHom.ext fun z => ?_
  rw [MonoidHom.pow_apply]
  show (χ₀ (Units.map (Algebra.norm (ZMod g) : K →* ZMod g) z)) ^ g ^ j =
    χ₀ (Units.map (Algebra.norm (ZMod g) : K →* ZMod g) z)
  rw [← map_pow, units_pow_card_pow]

theorem isRegularChar_mul (K : Type) [Field K] [Algebra (ZMod g) K] (χ₀ : (ZMod g)ˣ →* ℂˣ) {θ : Kˣ →* ℂˣ}
    (hθ : GlobalTheory.Published.IsRegularChar g n θ) : GlobalTheory.Published.IsRegularChar g n (θ * DiscreteGroups.sglob.DzType.nmChar K χ₀) := by
  intro i j hi hj h
  apply hθ i j hi hj
  rw [mul_pow, mul_pow, nmChar_pow, nmChar_pow] at h
  exact mul_right_cancel h

theorem char_twFD (K : Type) [Field K] [Algebra (ZMod g) K] (hK : Nat.card K = g ^ n) (hn : 0 < n)
    (χ₀ : (ZMod g)ˣ →* ℂˣ) (θ : Kˣ →* ℂˣ) (τ : FDRep ℂ (Gn g n))
    (hτ : ∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
        τ.character y = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ)) :
    ∀ y : Gn g n, Irreducible (y : Mt g n).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g n).charpoly = 0 →
      (twFD τ χ₀).character y =
        (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, (((θ * DiscreteGroups.sglob.DzType.nmChar K χ₀) (z ^ g ^ j) : ℂˣ) : ℂ) := by
  intro y hy z hz
  have hN : ∀ j, DiscreteGroups.sglob.DzType.nmChar K χ₀ (z ^ g ^ j) = χ₀ (Matrix.GeneralLinearGroup.det y) := by
    intro j
    rw [det_eq_norm K hK hn y hy z hz, map_pow, ← MonoidHom.pow_apply, nmChar_pow]
    try rfl
  rw [character_twFD, hτ y hy z hz]
  simp only [MonoidHom.mul_apply, Units.val_mul, hN]
  rw [← Finset.sum_mul]
  ring

end DiscreteGroups.sglob.DzTw
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.ExistsEqMulShiftToCircle
section
noncomputable section

open NumberField IsDedekindDomain

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_eq_mulShift_toCircle (g : ℕ) [NeZero g] (l : AddChar (ZMod g) Circle) :
    ∃ s : ZMod g, l = (ZMod.toCircle : AddChar (ZMod g) Circle).mulShift s := by
  classical
  let e : AddChar (ZMod g) Circle → AddChar (ZMod g) ℂ := fun χ => Circle.coeHom.compAddChar χ
  have he : Function.Injective e :=
    MonoidHom.compAddChar_injective_right _ (fun a b h => Circle.coe_inj.mp h)
  have hp : (e ZMod.toCircle).IsPrimitive := ZMod.isPrimitive_stdAddChar g
  have hbij : Function.Bijective (e ZMod.toCircle).mulShift :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨AddChar.to_mulShift_inj_of_isPrimitive hp, AddChar.card_eq.symm⟩
  obtain ⟨s, hs⟩ := hbij.2 (e l)
  refine ⟨s, DFunLike.ext _ _ fun t => ?_⟩
  have := congrArg (fun χ : AddChar (ZMod g) ℂ => χ t) hs
  simp only [e, AddChar.mulShift_apply, MonoidHom.compAddChar_apply, Function.comp_apply] at this
  rw [AddChar.mulShift_apply]
  exact (Circle.coe_inj.mp this).symm

theorem stdChar_shift_intCast (g : ℕ) [Fact g.Prime] (s : ZMod g) (x : ℤ_[g]) :
    GroundTheory.LocalField.Padic.stdChar g (((s.val : ℚ_[g]) / g) * (x : ℚ_[g])) =
      ZMod.toCircle (s * PadicInt.toZMod x) := by
  have hg0 : (g : ℚ_[g]) ≠ 0 := by exact_mod_cast (Fact.out : g.Prime).ne_zero
  set j : ZMod g := s * PadicInt.toZMod x with hj
  have hmem : (s.val : ℤ_[g]) * x - (j.val : ℤ_[g]) ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_natCast, map_natCast, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val, hj, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc' : ((s.val : ℚ_[g]) / g) * (x : ℚ_[g]) - ((j.val : ℤ) : ℚ_[g]) / (g : ℚ_[g]) ^ 1 = (c : ℚ_[g]) := by
    have := congrArg (fun z : ℤ_[g] => (z : ℚ_[g])) hc
    simp only [PadicInt.coe_mul, PadicInt.coe_natCast, PadicInt.coe_sub] at this
    rw [pow_one]
    field_simp
    push_cast
    linear_combination (-1 : ℚ_[g]) * this
  rw [GroundTheory.LocalField.Padic.stdChar_apply g _ (j.val : ℤ) 1 (by rw [hc']; exact c.2),
    ZMod.toCircle_eq_circleExp, Real.fourierChar_apply']
  congr 1
  push_cast
  ring

theorem continuous_symm' {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ}
    [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) : Continuous i.symm := by
  have ho : IsOpenMap i :=
    AddMonoidHom.isOpenMap_of_sigmaCompact i.toRingHom.toAddMonoidHom i.surjective hi
  exact (i.toEquiv.toHomeomorphOfContinuousOpen hi ho).symm.continuous

theorem lPsi : LPsi := by
  intro E _ _ w g _ i hi ψ₀ h₀
  have : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  obtain ⟨s, hs⟩ := exists_eq_mulShift_toCircle g ψ₀
  let ψQ : AddChar ℚ_[g] Circle := (GroundTheory.LocalField.Padic.stdChar g).mulShift ((s.val : ℚ_[g]) / g)
  let ψ : AddChar (w.adicCompletion E) Circle := ψQ.compAddMonoidHom i.symm.toAddMonoidHom
  have key : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x) := fun x => by
    show GroundTheory.LocalField.Padic.stdChar g (((s.val : ℚ_[g]) / g) * i.symm (i (x : ℚ_[g]))) = ψ₀ _
    rw [RingEquiv.symm_apply_apply, stdChar_shift_intCast, hs, AddChar.mulShift_apply]
  refine ⟨ψ, ?_, ?_, key⟩
  · exact (GroundTheory.LocalField.Padic.continuous_stdChar g).comp (continuous_const.mul (continuous_symm' i hi))
  · intro h1
    apply h₀
    refine DFunLike.ext _ _ fun k => ?_
    obtain ⟨x, rfl⟩ := ZMod.ringHom_surjective (PadicInt.toZMod (p := g)) k
    rw [← key, h1, AddChar.one_apply, AddChar.one_apply]

end DiscreteGroups.sglob.DzType
end
end

