import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CardH2GaussianField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0150
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0097
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0123
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0104
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0158

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PoitouTateDualityOfNormalised
section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise

namespace GlobalTheory.PoitouTateConj

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

def conjBack (σ : Ω ≃+* Ω) (τ : F ≃+* F) (hστ : ∀ x, σ (algebraMap F Ω x) = algebraMap F Ω (τ x)) :
    G F Ω →* G F Ω where
  toFun g := AlgEquiv.ofRingEquiv (f := (σ.trans g.toRingEquiv).trans σ.symm) (fun x => by
    simp only [RingEquiv.trans_apply, hστ, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    rw [← hστ, RingEquiv.symm_apply_apply])
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

theorem conjBack_apply (σ : Ω ≃+* Ω) (τ : F ≃+* F) (hστ : ∀ x, σ (algebraMap F Ω x) = algebraMap F Ω (τ x))
    (g : G F Ω) (x : Ω) : conjBack σ τ hστ g x = σ.symm (g (σ x)) := rfl

theorem apply_conjBack (σ : Ω ≃+* Ω) (τ : F ≃+* F) (hστ : ∀ x, σ (algebraMap F Ω x) = algebraMap F Ω (τ x))
    (g : G F Ω) (x : Ω) : σ (conjBack σ τ hστ g x) = g (σ x) := by
  rw [conjBack_apply, RingEquiv.apply_symm_apply]

theorem mem_Dec_of_forall {A : ValuationSubring Ω} {g : G F Ω} (h : ∀ x, g x ∈ A ↔ x ∈ A) :
    g ∈ Dec (F := F) A := by
  show g • A = A
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← h, mul_inv_apply]

variable (σ : Ω ≃+* Ω) (τ : F ≃+* F) (hστ : ∀ x, σ (algebraMap F Ω x) = algebraMap F Ω (τ x))
  {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A)
include hA

theorem valuation_le_one_iff_of_map (x : Ω) :
    A'.valuation (σ x) ≤ 1 ↔ A.valuation x ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff, hA]

theorem valuation_lt_one_iff_of_map (x : Ω) :
    A'.valuation (σ x) < 1 ↔ A.valuation x < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', hA, ← map_inv₀, hA, map_eq_zero_iff _ σ.injective]

omit hA in
include hA in
theorem conjBack_mem_Dec {g : G F Ω} (hg : g ∈ Dec (F := F) A') :
    conjBack σ τ hστ g ∈ Dec (F := F) A :=
  mem_Dec_of_forall fun x => by
    rw [← hA, apply_conjBack, apply_mem_iff_of_mem_Dec hg, hA]

omit hA in
include hA in
theorem conjBack_mem_Ine {g : G F Ω} (hg : g ∈ Ine (F := F) A') :
    conjBack σ τ hστ g ∈ Ine (F := F) A := by
  refine ⟨conjBack_mem_Dec σ τ hστ hA hg.1, fun x hx => ?_⟩
  rw [← valuation_lt_one_iff_of_map σ hA, map_sub, apply_conjBack]
  exact hg.2 _ ((valuation_le_one_iff_of_map σ hA x).2 hx)

omit hA in
include hA in
theorem conjBack_isFrob {q : ℕ} {g : G F Ω} (hg : IsFrob A' q g) :
    IsFrob A q (conjBack σ τ hστ g) := by
  refine ⟨conjBack_mem_Dec σ τ hστ hA hg.1, fun x hx => ?_⟩
  rw [← valuation_lt_one_iff_of_map σ hA, map_sub, apply_conjBack, map_pow]
  exact hg.2 _ ((valuation_le_one_iff_of_map σ hA x).2 hx)

omit hA in
theorem cycMod_conjBack (l : ℕ) [Fact l.Prime] (r : ℕ) (g : G F Ω) :
    cycMod F Ω l r (conjBack σ τ hστ g) = cycMod F Ω l r g := by
  have e : MulSemiringAction.toRingAut (G F Ω) Ω (conjBack σ τ hστ g) =
      σ⁻¹ * MulSemiringAction.toRingAut (G F Ω) Ω g * σ := by
    ext x; rfl
  simp only [cycMod, cycZ, MonoidHom.comp_apply, e, map_mul, map_inv]
  rw [mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]

omit hA in

theorem continuous_conjBack [Algebra.IsAlgebraic F Ω] : Continuous (conjBack σ τ hστ) := by
  haveI : Algebra.IsIntegral F Ω := inferInstance
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  rw [Filter.mem_map]
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff F Ω s).1 hs
  let b := Module.finBasis F E
  have hU : IsOpen (⋂ i, (MulAction.stabilizer (G F Ω) (σ (b i : Ω)) : Set (G F Ω))) :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral _
  refine Filter.mem_of_superset (hU.mem_nhds (Set.mem_iInter.2 fun i => (MulAction.stabilizer (G F Ω) _).one_mem)) fun g hg => hEs ?_
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hb : ∀ i, conjBack σ τ hστ g (b i) = b i := fun i => by
    have := Set.mem_iInter.1 hg i
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
    rw [conjBack_apply, this, RingEquiv.symm_apply_apply]
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : Ω) := by
    have := congrArg E.val (b.sum_repr ⟨x, hx⟩)
    rw [map_sum] at this
    simp only [map_smul] at this
    exact this.symm
  rw [hx', map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hb]

omit hA in
include hA hστ in

theorem exists_place_map {v : HeightOneSpectrum (𝓞 F)} (hAv : IsPlaceOver A v) :
    ∃ v' : HeightOneSpectrum (𝓞 F), IsPlaceOver A' v' ∧ normV v' = normV v ∧
      ∀ ϖ : 𝓞 F, ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∃ ϖ' : 𝓞 F, ϖ' ∈ v'.asIdeal ∧
        ϖ' ∉ v'.asIdeal ^ 2 ∧ algebraMap F Ω (ϖ' : F) = σ (algebraMap F Ω (ϖ : F)) := by
  let e : 𝓞 F ≃+* 𝓞 F := RingOfIntegers.mapRingEquiv τ
  have he : ∀ x : 𝓞 F, ((e x : 𝓞 F) : F) = τ (x : F) := fun x => rfl
  let v' : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := v.asIdeal.map (e : 𝓞 F →+* 𝓞 F)
      isPrime := Ideal.map_isPrime_of_equiv e
      ne_bot := by
        rw [Ne, Ideal.map_eq_bot_iff_of_injective (f := (e : 𝓞 F →+* 𝓞 F)) e.injective]
        exact v.ne_bot }
  have hmem : ∀ x : 𝓞 F, x ∈ v'.asIdeal ↔ e.symm x ∈ v.asIdeal := fun x => by
    show x ∈ v.asIdeal.map (e : 𝓞 F →+* 𝓞 F) ↔ _
    rw [Ideal.map_comap_of_equiv, Ideal.mem_comap]
  refine ⟨v', fun x => ?_, ?_, fun ϖ h1 h2 => ⟨e ϖ, ?_, ?_, ?_⟩⟩
  · rw [hmem, ← hAv, ← valuation_lt_one_iff_of_map σ hA, hστ]
    congr 3
    rw [← he, RingEquiv.apply_symm_apply]
  · unfold normV
    exact Nat.card_congr (Ideal.quotientEquiv v.asIdeal v'.asIdeal e rfl).toEquiv.symm
  · rw [hmem, RingEquiv.symm_apply_apply]; exact h1
  · show e ϖ ∉ (v.asIdeal.map (e : 𝓞 F →+* 𝓞 F)) ^ 2
    rw [← Ideal.map_pow, Ideal.map_comap_of_equiv, Ideal.mem_comap, RingEquiv.symm_apply_apply]
    exact h2
  · rw [he, hστ]

end GlobalTheory.PoitouTateConj

namespace GlobalTheory.PoitouTateConj
open GlobalTheory.Published GlobalTheory.Published.PoitouTate

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [hl : Fact l.Prime] {r : ℕ}

theorem conjCompatible (hr : 0 < r) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (l ^ r)) {inv : InvFam F Ω l r}
    (h : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
      Function.Bijective (inv A) ∧ IsNormalised ζ A v (inv A)) :
    ConjCompatible ζ inv := by
  intro σ τ hστ c hc A A' v hAv hA z z' hz
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  let ψ : Dec (F := F) A' →* Dec (F := F) A :=
    ((conjBack σ τ hστ).comp (Dec (F := F) A').subtype).codRestrict (Dec (F := F) A)
      (fun g => conjBack_mem_Dec σ τ hστ hA g.2)
  have hψv : ∀ g : Dec (F := F) A', ((ψ g : Dec (F := F) A) : G F Ω) = conjBack σ τ hστ g := fun _ => rfl
  have hψc : Continuous ψ :=
    (((continuous_conjBack σ τ hστ).comp continuous_subtype_val)).subtype_mk _
  have hψ : ∀ (g' : Dec (F := F) A') x, (g' : G F Ω) (σ x) = σ (((ψ g' : Dec (F := F) A) : G F Ω) x) :=
    fun g' x => (apply_conjBack σ τ hστ g' x).symm
  have hcyc : ∀ g' : Dec (F := F) A',
      ((cycMod F Ω l r ((ψ g' : Dec (F := F) A) : G F Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) =
        ((cycMod F Ω l r (g' : G F Ω) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) := fun g' => by
    rw [hψv, cycMod_conjBack]
  have hz' : ∀ p, z'.1 p = c * z.1 (ψ p.1, ψ p.2) := fun p => hz _ _ p.1 p.2 (hψ p.1) (hψ p.2)

  have hTZ : ∀ w : Z2 (muLoc F l r A),
      (fun p : Dec (F := F) A' × Dec (F := F) A' => c * w.1 (ψ p.1, ψ p.2)) ∈ Z2 (muLoc F l r A') := by
    intro w
    refine ⟨continuous_const.mul (w.2.1.comp ((hψc.comp continuous_fst).prodMk (hψc.comp continuous_snd))),
      fun g h k => ?_⟩
    have e := w.2.2 (ψ g) (ψ h) (ψ k)
    simp only [charRep_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul] at e ⊢
    rw [← hcyc g]
    linear_combination c * e
  have hTB : ∀ f : Dec (F := F) A → ZMod (l ^ r), Continuous f →
      ∃ f' : Dec (F := F) A' → ZMod (l ^ r), Continuous f' ∧
        ∀ p, d1 (muLoc F l r A') f' p = c * d1 (muLoc F l r A) f (ψ p.1, ψ p.2) := by
    intro f hf
    refine ⟨fun g => c * f (ψ g), continuous_const.mul (hf.comp hψc), fun p => ?_⟩
    simp only [d1, LinearMap.coe_mk, AddHom.coe_mk, charRep_apply, MonoidHom.comp_apply,
      Subgroup.coe_subtype, map_mul]
    rw [← hcyc p.1]
    ring

  obtain ⟨χ, h1, h2, h3, h4⟩ := GlobalTheory.Published.PoitouTate.Model.exists_unramified hAv (n := l ^ r)
    (Nat.one_lt_pow hr.ne' hl.out.one_lt)
  obtain ⟨ϖ, y, κ, z0, ha, hb, hy, hκ, hz0e⟩ :=
    GlobalTheory.Published.PoitouTate.Model.exists_kummer hζ A v χ h1 h2
  have hz0 : inv A (Submodule.Quotient.mk z0) = 1 := (h A v hAv).2 ϖ y κ χ z0 ha hb hy hκ h1 h3 h4 hz0e
  set a := inv A (Submodule.Quotient.mk z) with ha_def
  have hzz : (Submodule.Quotient.mk z : H2 (muLoc F l r A)) = Submodule.Quotient.mk (a • z0) := by
    rw [Submodule.Quotient.mk_smul]
    exact (h A v hAv).1.1 (by rw [map_smul, hz0, smul_eq_mul, mul_one])
  rw [Submodule.Quotient.eq] at hzz
  obtain ⟨f, hf, hfe⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 hzz)
  obtain ⟨f', hf', hf'e⟩ := hTB f hf

  obtain ⟨v', hA'v', hN, hϖ⟩ := exists_place_map σ τ hστ hA hAv
  obtain ⟨ϖ', ha', hb', hϖe⟩ := hϖ ϖ ha hb
  let z0' : Z2 (muLoc F l r A') := ⟨_, hTZ z0⟩
  have hpow : ∀ s t : ZMod (l ^ r), ζ ^ (s * t).val = ζ ^ (s.val * t.val) := fun s t => by
    rw [ZMod.val_mul]
    conv_rhs => rw [← Nat.mod_add_div (s.val * t.val) (l ^ r), pow_add, pow_mul, hζ.pow_eq_one,
      one_pow, mul_one]
  have hz0' : inv A' (Submodule.Quotient.mk z0') = 1 := by
    refine (h A' v' hA'v').2 ϖ' (σ y) (fun g => c * κ (ψ g)) (fun g => χ (ψ g)) z0' ha' hb' ?_ ?_
      ?_ ?_ ?_ ?_
    · rw [← map_pow, hy, hϖe]
    · intro g
      rw [hψ, hκ, map_mul, map_pow, hc, ← pow_mul, hpow]
    · intro g h; rw [map_mul, h1]
    · intro g hg; exact h3 _ (by rw [hψv]; exact conjBack_mem_Ine σ τ hστ hA hg)
    · intro g hg; exact h4 _ (by rw [hψv]; rw [hN] at hg; exact conjBack_isFrob σ τ hστ hA hg)
    · intro g h; show c * z0.1 (ψ g, ψ h) = _; rw [hz0e]; ring
  have hzz' : (Submodule.Quotient.mk z' : H2 (muLoc F l r A')) = Submodule.Quotient.mk (a • z0') := by
    rw [Submodule.Quotient.eq]
    refine Submodule.mem_comap.2 (Submodule.mem_map.2 ⟨f', hf', ?_⟩)
    funext p
    rw [hf'e, hfe]
    show _ = z'.1 p - a * (c * z0.1 (ψ p.1, ψ p.2))
    rw [hz']
    show c * (z.1 _ - a * z0.1 _) = _
    ring
  rw [hzz', Submodule.Quotient.mk_smul, map_smul, hz0', smul_eq_mul, mul_one]

theorem poitouTateDuality_of_normalised (h : PoitouTateNormalised) : PoitouTateDuality := by
  intro F Ω _ _ _ _ _ l _ r hl hr ζ hζ
  obtain ⟨inv, h1, h2⟩ := h F Ω l r hl hr ζ hζ
  exact ⟨inv, ⟨h1, conjCompatible hr hζ h1⟩, h2⟩

end GlobalTheory.PoitouTateConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumStableLatticesProductEqQPowMul
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section

namespace GlobalTheory.UnitLemma.FibSum

theorem fib_card (K : UQ) (B₁ B₂ : InvAlg K) (hg₁ : B₁.σ B₁.g = B₁.g) (hg₂ : B₂.σ B₂.g = B₂.g)
    (hres : resultant B₁.P B₂.P ≠ 0)
    (M₁ : Submodule K.O B₁.A) (M₂ : Submodule K.O B₂.A) (h₁ : M₁ ∈ B₁.Lin) (h₂ : M₂ ∈ B₂.Lin) :
    (Nat.card {M : Submodule K.O (B₁.A × B₂.A) // M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} : ℚ) =
      (K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P) := by
  have hI := GlobalTheory.T.card_stable_lattices_alt K.O K.E B₁.A B₂.A B₁.g B₂.g hres M₁ M₂ h₁.1 h₂.1 h₁.2.1 h₂.2.1
  have hH := GlobalTheory.T.card_sigma_stable_prod_lattice_ext_sq K B₁ B₂ hg₁ hg₂ M₁ M₂ h₁ h₂
  have e : {M : Submodule K.O (B₁.A × B₂.A) // M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} ≃
      {M : Submodule K.O (B₁.A × B₂.A) // ((∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧
        ∀ y ∈ M, (B₁.σ y.1, B₂.σ y.2) ∈ M) ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} :=
    { toFun := fun M => ⟨M.1, ⟨M.2.1.2.1, M.2.1.2.2⟩, M.2.2⟩
      invFun := fun M => ⟨M.1, ⟨GlobalTheory.T.isFullLattice_prod_of_comap_inl_map_snd K B₁ B₂ M.1 (by rw [M.2.2.1]; exact h₁.1)
          (by rw [M.2.2.2]; exact h₂.1), M.2.1.1, M.2.1.2⟩, M.2.2⟩
      left_inv := fun M => rfl
      right_inv := fun M => rfl }
  rw [Nat.card_congr e]
  have hq2 : (Nat.card (IsLocalRing.ResidueField K.O) : ℚ) = (K.q : ℚ) ^ 2 := by
    rw [K.card_res]; push_cast; ring
  rw [hq2] at hI
  have hqpos : (0 : ℚ) < K.q := by
    have : 0 < Nat.card (IsLocalRing.ResidueField K.O) := Nat.card_pos
    rw [K.card_res] at this
    exact_mod_cast pos_of_ne_zero (fun h => by simp [h] at this)
  have hsq : ((Nat.card {M : Submodule K.O (B₁.A × B₂.A) // ((∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧
        ∀ y ∈ M, (B₁.σ y.1, B₂.σ y.2) ∈ M) ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} : ℚ)) ^ 2 =
      ((K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P)) ^ 2 := by
    have hpw : ((K.q : ℚ) ^ 2) ^ val K.O (resultant B₁.P B₂.P) = ((K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P)) ^ 2 := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    have hP₁ : (LinearMap.mulLeft K.E B₁.g).charpoly = B₁.P := rfl
    have hP₂ : (LinearMap.mulLeft K.E B₂.g).charpoly = B₂.P := rfl
    rw [hP₁, hP₂, hpw] at hI
    rw [← hI]
    exact_mod_cast hH
  exact (pow_left_inj₀ (by positivity) (zpow_pos hqpos _).le two_ne_zero).1 hsq

theorem fibsum : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g → (B₁.P * B₂.P).Separable → ∀ (φ₁ : Submodule K.O B₁.A → ℚ) (φ₂ : Submodule K.O B₂.A → ℚ), {M ∈ B₁.Lin | φ₁ M ≠ 0}.Finite → {M ∈ B₂.Lin | φ₂ M ≠ 0}.Finite → {M ∈ (B₁.prod B₂).Lin | φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) ≠ 0}.Finite ∧ ∑ᶠ M ∈ (B₁.prod B₂).Lin, φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) = (K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P) * ((∑ᶠ M ∈ B₁.Lin, φ₁ M) * ∑ᶠ M ∈ B₂.Lin, φ₂ M) := by
  intro K B₁ B₂ hg₁ hg₂ hsep φ₁ φ₂ hf₁ hf₂
  have hres : resultant B₁.P B₂.P ≠ 0 := resultant_ne_zero _ _ hsep.isCoprime
  set v := val K.O (resultant B₁.P B₂.P) with hv
  set π : Submodule K.O (B₁.prod B₂).A → Submodule K.O B₁.A × Submodule K.O B₂.A := fun M =>
    (M.comap (LinearMap.inl K.O B₁.A B₂.A), M.map (LinearMap.snd K.O B₁.A B₂.A)) with hπ
  suffices key : ∀ F : Submodule K.O (B₁.prod B₂).A → ℚ, (∀ M, F M =
      φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A))) →
      {M | M ∈ (B₁.prod B₂).Lin ∧ F M ≠ 0}.Finite ∧ ∑ᶠ M ∈ (B₁.prod B₂).Lin, F M =
        (K.q : ℚ) ^ v * ((∑ᶠ M ∈ B₁.Lin, φ₁ M) * ∑ᶠ M ∈ B₂.Lin, φ₂ M) from key _ (fun _ => rfl)
  intro F hF
  set s₁ := hf₁.toFinset
  set s₂ := hf₂.toFinset
  have hs₁ : ∀ M, M ∈ s₁ ↔ M ∈ B₁.Lin ∧ φ₁ M ≠ 0 := fun M => by simp [s₁]
  have hs₂ : ∀ M, M ∈ s₂ ↔ M ∈ B₂.Lin ∧ φ₂ M ≠ 0 := fun M => by simp [s₂]
  have hfibfin : ∀ p ∈ s₁ ×ˢ s₂, {M | M ∈ (B₁.prod B₂).Lin ∧ π M = p}.Finite := by
    intro p hp
    rw [Finset.mem_product, hs₁, hs₂] at hp
    have hc := fib_card K B₁ B₂ hg₁ hg₂ hres p.1 p.2 hp.1.1 hp.2.1
    have hqpos : (0 : ℚ) < K.q := by
      have : 0 < Nat.card (IsLocalRing.ResidueField K.O) := Nat.card_pos
      rw [K.card_res] at this
      exact_mod_cast pos_of_ne_zero (fun h => by simp [h] at this)
    have hne : Nat.card {M : Submodule K.O (B₁.A × B₂.A) // M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = p.1 ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = p.2} ≠ 0 := by
      intro h0
      rw [h0] at hc
      exact (zpow_pos hqpos v).ne' (by simpa using hc.symm)
    have := Nat.finite_of_card_ne_zero hne
    refine (Set.finite_coe_iff.1 ?_)
    have e : {M | M ∈ (B₁.prod B₂).Lin ∧ π M = p} = {M | M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = p.1 ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = p.2} := by
      ext M; simp only [Set.mem_setOf_eq, hπ, Prod.ext_iff]
    rw [e]; exact this
  set W := {M | M ∈ (B₁.prod B₂).Lin ∧ π M ∈ s₁ ×ˢ s₂} with hW
  have hWfin : W.Finite := by
    refine (Set.Finite.biUnion (t := fun p => {M | M ∈ (B₁.prod B₂).Lin ∧ π M = p})
      (s₁ ×ˢ s₂).finite_toSet hfibfin).subset ?_
    intro M hM
    exact Set.mem_biUnion (x := π M) hM.2 (show M ∈ {M' | M' ∈ (B₁.prod B₂).Lin ∧ π M' = π M} from ⟨hM.1, rfl⟩)
  have hsupp : ∀ M ∈ (B₁.prod B₂).Lin, F M ≠ 0 → M ∈ W := by
    intro M hM hFM
    have hl := GlobalTheory.T.lieLattice_prod_comap_inl_and_map_snd K B₁ B₂ M hM
    rw [hF M] at hFM
    refine ⟨hM, Finset.mem_product.2 ⟨(hs₁ _).2 ⟨hl.1, left_ne_zero_of_mul hFM⟩,
      (hs₂ _).2 ⟨hl.2, right_ne_zero_of_mul hFM⟩⟩⟩
  refine ⟨hWfin.subset fun M hM => hsupp M hM.1 hM.2, ?_⟩
  have hL : ∑ᶠ M ∈ (B₁.prod B₂).Lin, F M = ∑ M ∈ hWfin.toFinset, F M := by
    have hset : (B₁.prod B₂).Lin ∩ Function.support F = W ∩ Function.support F := by
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support]
      exact ⟨fun h => ⟨hsupp M h.1 h.2, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [← finsum_mem_eq_finite_toFinset_sum _ hWfin, ← finsum_mem_inter_support,
      ← finsum_mem_inter_support (s := W), hset]
  have h1 : ∑ᶠ M ∈ B₁.Lin, φ₁ M = ∑ M ∈ s₁, φ₁ M := by
    have hset : B₁.Lin ∩ Function.support φ₁ = {M | M ∈ B₁.Lin ∧ φ₁ M ≠ 0} ∩ Function.support φ₁ := by
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [← finsum_mem_eq_finite_toFinset_sum _ hf₁, ← finsum_mem_inter_support,
      ← finsum_mem_inter_support (s := {M | M ∈ B₁.Lin ∧ φ₁ M ≠ 0}), hset]
  have h2 : ∑ᶠ M ∈ B₂.Lin, φ₂ M = ∑ M ∈ s₂, φ₂ M := by
    have hset : B₂.Lin ∩ Function.support φ₂ = {M | M ∈ B₂.Lin ∧ φ₂ M ≠ 0} ∩ Function.support φ₂ := by
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [← finsum_mem_eq_finite_toFinset_sum _ hf₂, ← finsum_mem_inter_support,
      ← finsum_mem_inter_support (s := {M | M ∈ B₂.Lin ∧ φ₂ M ≠ 0}), hset]
  rw [hL, h1, h2, ← Finset.sum_fiberwise_of_maps_to (s := hWfin.toFinset) (t := s₁ ×ˢ s₂) (g := π)
    (fun M hM => ((Set.Finite.mem_toFinset hWfin).1 hM).2), Finset.sum_mul_sum, ← Finset.sum_product', Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hin : ∀ M ∈ hWfin.toFinset.filter (fun M => π M = p), F M = φ₁ p.1 * φ₂ p.2 := by
    intro M hM
    have hM' := (Finset.mem_filter.1 hM).2
    rw [hF, ← hM']
  rw [Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hp' := hp
  rw [Finset.mem_product, hs₁, hs₂] at hp'
  rw [← fib_card K B₁ B₂ hg₁ hg₂ hres p.1 p.2 hp'.1.1 hp'.2.1]
  congr 1
  rw [← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro M
  simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, hW, hπ, Prod.ext_iff]
  constructor
  · rintro ⟨⟨h, _⟩, h'⟩; exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩
    refine ⟨⟨h, ?_⟩, h'⟩
    rw [Finset.mem_product]; rw [h'.1, h'.2]; exact Finset.mem_product.1 hp

end GlobalTheory.UnitLemma.FibSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoUntiltFrobeniusSeriesTermNormsZero
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem psers_norm_natCast_self (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends' l (l : ℚ_[l])
  rw [Padic.norm_p] at h
  simpa using h

theorem psers_terms_tendsto_zero : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ), 1 ≤ h → 0 ≤ r → r < 1 → Filter.Tendsto (fun n : ℤ => ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))) Filter.cofinite (nhds 0) := by
  intro l _ h j r h1 hr0 hr1
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hlR : (1 : ℝ) < l := by exact_mod_cast hl
  have ha := psers_norm_natCast_self l
  set a := ‖(l : ℂ_[l])‖ with ha_def
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have ha1 : a < 1 := by rw [ha]; exact inv_lt_one_of_one_lt₀ hlR
  rw [Int.cofinite_eq, Filter.tendsto_sup]
  constructor
  · rw [← Filter.map_neg_atTop, Filter.tendsto_map'_iff, ← Nat.map_cast_int_atTop,
      Filter.tendsto_map'_iff]
    refine squeeze_zero (fun k => ?_) (fun k => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1)
    · simp only [Function.comp_apply, neg_neg, zpow_natCast]
      exact mul_nonneg (pow_nonneg ha0 _) (Real.rpow_nonneg hr0 _)
    · simp only [Function.comp_apply, neg_neg, zpow_natCast]
      have : r ^ ((l : ℝ) ^ (-(k : ℤ) * h + j : ℤ)) ≤ 1 :=
        Real.rpow_le_one hr0 hr1.le (zpow_nonneg (by positivity) _)
      calc a ^ k * r ^ ((l : ℝ) ^ (-(k : ℤ) * h + j : ℤ)) ≤ a ^ k * 1 :=
            mul_le_mul_of_nonneg_left this (pow_nonneg ha0 _)
        _ = a ^ k := mul_one _
  · rw [← Nat.map_cast_int_atTop, Filter.tendsto_map'_iff]
    have hN : Filter.Tendsto (fun k : ℕ => l ^ (k * h + j)) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_mono (fun k => ?_) Filter.tendsto_id
      calc k ≤ l ^ k := (Nat.lt_pow_self hl).le
        _ ≤ l ^ (k * h + j) := Nat.pow_le_pow_right (by omega) (by nlinarith)
    refine squeeze_zero (fun k => ?_) (fun k => ?_)
      ((tendsto_self_mul_const_pow_of_lt_one hr0 hr1).comp hN)
    · exact mul_nonneg (zpow_nonneg ha0 _) (Real.rpow_nonneg hr0 _)
    · have e1 : a ^ (-((k : ℕ) : ℤ)) = (l : ℝ) ^ k := by
        rw [zpow_neg, zpow_natCast, ha, inv_pow, inv_inv]
      have e2 : (l : ℝ) ^ (((k : ℕ) : ℤ) * h + j : ℤ) = ((l ^ (k * h + j) : ℕ) : ℝ) := by
        rw [show (((k : ℕ) : ℤ) * h + j : ℤ) = ((k * h + j : ℕ) : ℤ) by push_cast; ring,
          zpow_natCast]
        push_cast; ring
      simp only [Function.comp_apply]
      rw [e1, e2, Real.rpow_natCast]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0 _)
      have : l ^ k ≤ l ^ (k * h + j) := Nat.pow_le_pow_right (by omega) (by nlinarith)
      exact_mod_cast this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltFrobeniusIntegerPowerLaws
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer.PwLaws
variable {l : ℕ} [Fact l.Prime]
theorem pw_apply_eq (k : ℤ) (x : Fl l) :
    pw k x = ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ k : RingAut (Fl l)) x := rfl
theorem pw_zadd (a b : ℤ) (x : Fl l) : pw (a + b) x = pw a (pw b x) := by
  simp only [pw_apply_eq, zpow_add, RingAut.mul_apply]
theorem pw_one (x : Fl l) : pw 1 x = x ^ l := by
  rw [pw_apply_eq, zpow_one]
  show frobeniusEquiv (Fl l) l x = _
  rw [frobeniusEquiv_apply, frobenius_def]
theorem pw_nat (n : ℕ) (x : Fl l) : pw (n : ℤ) x = x ^ l ^ n := by
  induction n with
  | zero => simp [pw_apply_eq]
  | succ n ih =>
    have h : ((n + 1 : ℕ) : ℤ) = 1 + (n : ℤ) := by push_cast; ring
    rw [h, pw_zadd, ih, pw_one, ← pow_mul, pow_succ]

theorem pw_zero_int (x : Fl l) : pw 0 x = x := by
  simp [pw_apply_eq]
theorem sh_pow' (x : Fl l) (m : ℕ) : sh (x ^ m) = sh x ^ m := by
  simp only [sh, map_pow, SubmonoidClass.coe_pow]
theorem norm_sh_pw_nat (n : ℕ) (x : Fl l) : ‖sh (pw (n : ℤ) x)‖ = ‖sh x‖ ^ (l ^ n) := by
  rw [pw_nat, sh_pow', norm_pow]
theorem norm_sh_pw (k : ℤ) (x : Fl l) : ‖sh (pw k x)‖ = ‖sh x‖ ^ ((l : ℝ) ^ k) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [norm_sh_pw_nat, zpow_natCast, ← Real.rpow_natCast]
    push_cast
    rfl
  · set y := pw (-(n : ℤ)) x with hy
    have hx : x = pw (n : ℤ) y := by
      rw [hy, ← pw_zadd, add_neg_cancel, pw_zero_int]
    have hne : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    have e : ((l : ℝ) ^ (-(n : ℤ))) = (((l ^ n : ℕ) : ℝ))⁻¹ := by
      rw [zpow_neg, zpow_natCast]
      push_cast
      rfl
    conv_rhs => rw [hx, norm_sh_pw_nat, e]
    exact (Real.pow_rpow_inv_natCast (norm_nonneg _) hne).symm

theorem pw_laws : ∀ (l : ℕ) [Fact l.Prime], (∀ (k : ℤ) (x y : Fl l), pw k (x + y) = pw k x + pw k y) ∧ (∀ (k : ℤ) (x y : Fl l), pw k (x * y) = pw k x * pw k y) ∧ (∀ k : ℤ, pw k (0 : Fl l) = 0) ∧ (∀ (a b : ℤ) (x : Fl l), pw (a + b) x = pw a (pw b x)) ∧ (∀ (n : ℕ) (x : Fl l), pw n x = x ^ l ^ n) ∧ (∀ (k : ℤ) (n : ℕ) (x : Fl l), pw k (x ^ n) = pw k x ^ n) ∧ (∀ (k : ℤ) (x : Fl l), ‖sh (pw k x)‖ = ‖sh x‖ ^ ((l : ℝ) ^ k)) := by
  intro l _
  refine ⟨fun k x y => ?_, fun k x y => ?_, fun k => ?_, pw_zadd, pw_nat, fun k n x => ?_, norm_sh_pw⟩
  · simp only [pw_apply_eq, map_add]
  · simp only [pw_apply_eq, map_mul]
  · simp only [pw_apply_eq, map_zero]
  · simp only [pw_apply_eq, map_pow]

end GlobalTheory.PSer.PwLaws
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaSelfAdjointLieOfCountLimitDescentStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemmaSelfAdjointLie_of_count_limit_descent : CountIdentity → UnitaryLimit → LinearDescent → UnitLemmaLie := by
  first | exact @GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of | exact GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of | (intros; apply GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of <;> assumption)
end

