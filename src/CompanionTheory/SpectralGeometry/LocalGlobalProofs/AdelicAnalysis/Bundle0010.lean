import Mathlib
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GermConstantsEqAlongAffineSpaceSquare
section
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.QuasiRefl

open HeckeCharacterZeroLocus.SiegelWeilU

section Form

variable {A : Type} [CommRing A] {n : Type} [Fintype n] {σ : A →+* A} {J : Matrix n n A}

theorem hform_eq_dot (x y : n → A) : hform σ J x y = (σ ∘ x) ⬝ᵥ J *ᵥ y := by
  simp [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem comp_mulVec' (P : Matrix n n A) (x : n → A) : σ ∘ (P *ᵥ x) = P.map σ *ᵥ (σ ∘ x) := by
  funext i
  simp [mulVec, dotProduct]

theorem hform_mulVec' (P Q : Matrix n n A) (x y : n → A) :
    hform σ J (P *ᵥ x) (Q *ᵥ y) = hform σ (cT σ P * J * Q) x y := by
  rw [hform_eq_dot, hform_eq_dot, comp_mulVec', cT, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec _ (_ᵀ), vecMul_transpose]

theorem hform_sub_left (x d y : n → A) (c : A) :
    hform σ J (x - c • d) y = hform σ J x y - σ c * hform σ J d y := by
  simp [hform, Finset.mul_sum, sub_mul, mul_assoc]

theorem hform_sub_right (x d y : n → A) (c : A) :
    hform σ J x (y - c • d) = hform σ J x y - c * hform σ J x d := by
  simp [hform, Finset.mul_sum, mul_sub, mul_left_comm]

theorem hform_smul_right' (d y : n → A) (c : A) :
    hform σ J y (c • d) = c * hform σ J y d := by
  simp [hform, Finset.mul_sum, mul_left_comm]

theorem hform_conj_symm (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x y : n → A) :
    σ (hform σ J x y) = hform σ J y x := by
  simp only [hform, map_sum, map_mul, hσ, hJ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Form

section Refl

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {σ : A →+* A}
  {J : Matrix n n A}

def qrMat (σ : A →+* A) (J : Matrix n n A) (d : n → A) (c : A) : Matrix n n A :=
  1 - c • vecMulVec d ((σ ∘ d) ᵥ* J)

theorem qrMat_mulVec (d : n → A) (c : A) (z : n → A) :
    qrMat σ J d c *ᵥ z = z - (c * hform σ J d z) • d := by
  rw [qrMat, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, hform_eq_dot, dotProduct_mulVec]
  funext i
  simp [mul_comm, mul_left_comm]

theorem ext_mulVec' {P Q : Matrix n n A} (h : ∀ z, P *ᵥ z = Q *ᵥ z) : P = Q := by
  ext i j
  simpa using congrFun (h (Pi.single j 1)) i

theorem qrMat_mul (d : n → A) {c c' : A} (hc : c + c' = c * c' * hform σ J d d) :
    qrMat σ J d c * qrMat σ J d c' = 1 := ext_mulVec' fun z => by
  rw [← mulVec_mulVec, qrMat_mulVec, qrMat_mulVec, hform_sub_right, one_mulVec]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-hform σ J d z * d i) * hc

theorem hform_single' (i j : n) :
    hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have : σ ∘ (Pi.single i 1 : n → A) = Pi.single i 1 := by
    funext k
    by_cases h : k = i <;> simp [h]
  rw [hform_eq_dot, this]
  simp

theorem qrMat_isometry (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (d : n → A) (c : A)
    (hc : c + σ c = c * σ c * hform σ J d d) :
    cT σ (qrMat σ J d c) * J * qrMat σ J d c = J := by
  ext i j
  rw [← hform_single' (σ := σ) (J := _ * J * _) i j, ← hform_mulVec', qrMat_mulVec, qrMat_mulVec,
    hform_sub_left, hform_sub_right, hform_sub_right, map_mul, hform_conj_symm hσ hJ,
    hform_single']
  linear_combination
    (-hform σ J (Pi.single i 1) d * hform σ J d (Pi.single j 1)) * hc

def qr (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (d : n → A) (c : A)
    (hc : c + σ c = c * σ c * hform σ J d d) : UJ σ J :=
  ⟨⟨qrMat σ J d c, qrMat σ J d (σ c), qrMat_mul d hc,
    qrMat_mul d (by linear_combination hc)⟩, qrMat_isometry hσ hJ d c hc⟩

end Refl

theorem exists_unitary_carry (A : Type) [CommRing A] (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) A) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → A) (ε : A)
    (hxy : hform σ J x x = hform σ J y y) (hβ : IsUnit (hform σ J x x)) (hε : ε * σ ε = 1)
    (hu : IsUnit (hform σ J x x - σ ε * hform σ J y x)) :
    ∃ g ∈ UJ σ J, (g : Matrix (Fin M) (Fin M) A) *ᵥ x = y ∧
      ∀ z, hform σ J x z = 0 → hform σ J y z = 0 → (g : Matrix (Fin M) (Fin M) A) *ᵥ z = z := by
  obtain ⟨bi, hb⟩ := hβ.exists_right_inv
  obtain ⟨ui, hui⟩ := hu.exists_right_inv
  set β := hform σ J x x with hβdef
  set w := hform σ J y x with hw
  have hyy : hform σ J y y = β := hxy.symm
  have hxyw : hform σ J x y = σ w := by rw [hw, hform_conj_symm hσ hJ]
  have hσβ : σ β = β := hform_conj_symm hσ hJ x x
  have hσε : σ (σ ε) = ε := hσ ε
  have hσb : σ bi = bi := by
    have h1 : β * σ bi = 1 := by
      have := congrArg σ hb
      rwa [map_mul, hσβ, map_one] at this
    linear_combination bi * h1 - σ bi * hb
  have hσui : (β - ε * σ w) * σ ui = 1 := by
    have := congrArg σ hui
    rwa [map_mul, map_sub, map_mul, hσβ, hσε, map_one] at this
  set d : Fin M → A := x - ε • y with hd
  have hdx : hform σ J d x = β - σ ε * w := hform_sub_left x y x ε
  have hdy : hform σ J d y = σ w - σ ε * β := by
    rw [hd, hform_sub_left, hxyw, hyy]
  have hdd : hform σ J d d = (β - σ ε * w) + (β - ε * σ w) + (ε * σ ε - 1) * β := by
    rw [hform_sub_right, hdx, hdy]
    ring
  have hc₁ : (1 - σ ε) * bi + σ ((1 - σ ε) * bi)
      = (1 - σ ε) * bi * σ ((1 - σ ε) * bi) * hform σ J y y := by
    rw [map_mul, map_sub, map_one, hσε, hσb, hyy]
    linear_combination (-(1 - ε - σ ε + ε * σ ε) * bi) * hb + (-bi) * hε
  have hc₂ : ui + σ ui = ui * σ ui * hform σ J d d := by
    rw [hdd, hε]
    linear_combination (-σ ui) * hui + (-ui) * hσui
  refine ⟨((qr hσ hJ y _ hc₁ * qr hσ hJ d ui hc₂ : UJ σ J) : GL (Fin M) A), SetLike.coe_mem _, ?_, ?_⟩
  · have h2 : qrMat σ J d ui *ᵥ x = ε • y := by
      rw [qrMat_mulVec, hdx, mul_comm ui, hui, one_smul, hd]
      simp
    have h3 : qrMat σ J y ((1 - σ ε) * bi) *ᵥ (ε • y) = y := by
      rw [qrMat_mulVec, hform_smul_right', hyy]
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination ((1 - σ ε) * ε * y i) * (-hb) + (y i) * hε
    show (qrMat σ J y ((1 - σ ε) * bi) * qrMat σ J d ui) *ᵥ x = y
    rw [← mulVec_mulVec, h2, h3]
  · intro z hxz hyz
    have hdz : hform σ J d z = 0 := by
      rw [hd, hform_sub_left, hxz, hyz]
      simp
    show (qrMat σ J y ((1 - σ ε) * bi) * qrMat σ J d ui) *ᵥ z = z
    have h2 : qrMat σ J d ui *ᵥ z = z := by
      rw [qrMat_mulVec, hdz, mul_zero, zero_smul, sub_zero]
    rw [← mulVec_mulVec, h2, qrMat_mulVec, hyz, mul_zero, zero_smul, sub_zero]

end GlobalTheory.CompanionTheory.SW.QuasiRefl
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarInvariantUnderTransvection
section
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.Transv

theorem toMatrix_mulVec_apply {K ι : Type} [CommRing K] [Fintype ι] [DecidableEq ι]
    (t : Matrix.TransvectionStruct ι K) (x : ι → K) (k : ι) :
    (t.toMatrix *ᵥ x) k = if k = t.i then x k + t.c * x t.j else x k := by
  have h : t.toMatrix = 1 + Matrix.single t.i t.j t.c := rfl
  rw [h, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  by_cases hk : k = t.i
  · subst hk
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · have : ∀ l, (Matrix.single t.i t.j t.c) k l = 0 := by
      intro l
      simp [Matrix.single_apply, Ne.symm hk]
    simp [Matrix.mulVec, dotProduct, this, hk]

theorem measurePreserving_pi {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K]
    {ι : Type} [Fintype ι] [DecidableEq ι] (ν : Measure K) [SigmaFinite ν]
    [ν.IsAddLeftInvariant] (t : Matrix.TransvectionStruct ι K) :
    MeasurePreserving (fun x : ι → K => t.toMatrix *ᵥ x)
      (Measure.pi fun _ : ι => ν) (Measure.pi fun _ : ι => ν) := by
  classical
  have hj : t.j ≠ t.i := t.hij.symm
  let p : ι → Prop := fun k => k ≠ t.i
  let B : Measure ({k // p k} → K) := Measure.pi fun _ => ν
  let A : Measure ({k // ¬ p k} → K) := Measure.pi fun _ => ν
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => ν) p
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => K) p
  let g : ({k // p k} → K) → ({k // ¬ p k} → K) → ({k // ¬ p k} → K) :=
    fun b a => (fun _ => t.c * b ⟨t.j, hj⟩) + a
  have hgm : Measurable (Function.uncurry g) := by
    refine measurable_pi_iff.2 fun k => ?_
    have h1 : Measurable fun q : ({k // p k} → K) × ({k // ¬ p k} → K) =>
        q.1 ⟨t.j, hj⟩ := (measurable_pi_apply _).comp measurable_fst
    have h2 : Measurable fun q : ({k // p k} → K) × ({k // ¬ p k} → K) =>
        q.2 k := (measurable_pi_apply _).comp measurable_snd
    exact (h1.const_mul t.c).add h2
  have hsk : MeasurePreserving (fun q : ({k // p k} → K) × ({k // ¬ p k} → K) => (id q.1, g q.1 q.2))
      (B.prod A) (B.prod A) := by
    refine (MeasurePreserving.id B).skew_product hgm (Filter.Eventually.of_forall fun b => ?_)
    exact map_add_left_eq_self A _
  have hall := hmp.symm.comp (hsk.comp hmp)
  have hfun : (fun x : ι → K => t.toMatrix *ᵥ x) =
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => K) p).symm ∘
        (fun q : ({k // p k} → K) × ({k // ¬ p k} → K) => (id q.1, g q.1 q.2)) ∘
          (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => K) p) := by
    funext x k
    rw [toMatrix_mulVec_apply]
    by_cases hk : k = t.i
    · subst hk
      have hnp : ¬ p t.i := fun h => h rfl
      simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, g, hnp, add_comm]
    · have hp : p k := hk
      simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hp, hk]
  rw [hfun]
  exact hall

theorem map_toMatrix_mulVec (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K]
    [BorelSpace K] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → K))
    [μ.IsAddHaarMeasure] (t : Matrix.TransvectionStruct ι K) :
    μ.map (fun x => t.toMatrix *ᵥ x) = μ := by
  let ν : Measure K := Measure.addHaar
  let P : Measure (ι → K) := Measure.pi fun _ : ι => ν
  haveI : P.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hμ : μ = Measure.addHaarScalarFactor μ P • P := Measure.isAddLeftInvariant_eq_smul μ P
  have hP : P.map (fun x => t.toMatrix *ᵥ x) = P := (measurePreserving_pi ν t).map_eq
  generalize Measure.addHaarScalarFactor μ P = c at hμ
  rw [hμ, Measure.map_smul, hP]

end GlobalTheory.CompanionTheory.SW.Transv

theorem GlobalTheory.CompanionTheory.SW.transvection_map_addHaar : ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : Measure (ι → K)) [μ.IsAddHaarMeasure] (t : Matrix.TransvectionStruct ι K), μ.map (fun x => t.toMatrix *ᵥ x) = μ := by
  intro K _ _ _ _ _ _ _ _ ι _ _ μ _ t
  exact GlobalTheory.CompanionTheory.SW.Transv.map_toMatrix_mulVec K ι μ t
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarModularCharacterOfContinuousAction
section
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW

open scoped Pointwise in

theorem exists_continuous_modulus_of_continuous_action :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
      [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
      [IsTopologicalAddGroup V] (μ : Measure V) [μ.IsAddHaarMeasure] (Q : Type) [Group Q]
      [TopologicalSpace Q] [IsTopologicalGroup Q] [DistribMulAction Q V] [ContinuousSMul Q V],
      ∃ χ : Q →* ℝ≥0, Continuous χ ∧ ∀ q : Q, μ.map (fun v => q • v) = χ q • μ := by
  intro V _ _ _ _ _ _ _ _ μ _ Q _ _ _ _ _

  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : V)
  have hKint : (interior K).Nonempty := ⟨0, mem_interior_iff_mem_nhds.2 hK0⟩
  have hKtop : μ K ≠ ∞ := hK.measure_lt_top.ne
  have hKpos : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hK0).ne'
  have : μ.Regular := Measure.regular_of_isAddLeftInvariant hK hKint hKtop
  set Δ : Q →* ℝ≥0 := distribHaarChar V with hΔ
  have hmul : ∀ (g : Q) (s : Set V), (Δ g : ℝ≥0∞) * μ s = μ (g • s) := fun g s =>
    distribHaarChar_mul μ g s

  have hup : ∀ b : ℝ≥0, 1 < b → ∀ᶠ q in 𝓝 (1 : Q), Δ q < b := by
    intro b hb
    have hb' : (1 : ℝ≥0∞) < b := by exact_mod_cast hb
    have hlt : μ K < (b : ℝ≥0∞) * μ K := by
      calc μ K = 1 * μ K := (one_mul _).symm
        _ < b * μ K := (ENNReal.mul_lt_mul_iff_left hKpos hKtop).2 hb'
    obtain ⟨O, hKO, hO, hOμ⟩ := Set.exists_isOpen_lt_of_lt K _ hlt
    have hN : IsOpen {p : Q × V | p.1 • p.2 ∈ O} := hO.preimage continuous_smul
    obtain ⟨u, v, hu, -, h1u, hKv, huv⟩ :=
      generalized_tube_lemma (isCompact_singleton : IsCompact ({1} : Set Q)) hK hN (by
        rintro ⟨q, k⟩ ⟨hq, hk⟩
        simp only [Set.mem_singleton_iff] at hq
        subst hq
        simpa using hKO hk)
    filter_upwards [hu.mem_nhds (h1u (Set.mem_singleton 1))] with q hq
    have hsub : q • K ⊆ O := by
      rintro _ ⟨k, hk, rfl⟩
      exact huv (Set.mk_mem_prod hq (hKv hk))
    have h2 : (Δ q : ℝ≥0∞) * μ K < b * μ K := by
      rw [hmul]
      exact (measure_mono hsub).trans_lt hOμ
    exact_mod_cast (ENNReal.mul_lt_mul_iff_left hKpos hKtop).1 h2
  have hcont1 : ContinuousAt Δ 1 := by
    rw [ContinuousAt, map_one]
    refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => hup b hb⟩
    rcases eq_or_ne a 0 with rfl | ha0
    · exact Filter.Eventually.of_forall fun q => distribHaarChar_pos
    · have hb : 1 < a⁻¹ := (one_lt_inv₀ (pos_iff_ne_zero.2 ha0)).2 ha
      have ht : Filter.Tendsto (fun q : Q => q⁻¹) (𝓝 1) (𝓝 1) := by
        simpa using (continuous_inv.tendsto (1 : Q))
      filter_upwards [ht.eventually (hup _ hb)] with q hq
      rw [map_inv] at hq
      exact (inv_lt_inv₀ distribHaarChar_pos (pos_iff_ne_zero.2 ha0)).1 hq
  have hcont : Continuous Δ := continuous_of_continuousAt_one Δ hcont1
  refine ⟨⟨⟨fun q => Δ q⁻¹, by simp⟩, fun a b => by
    simp only [_root_.mul_inv_rev]
    rw [map_mul, mul_comm]⟩, hcont.comp continuous_inv, fun q => ?_⟩
  ext s hs
  rw [Measure.map_apply (continuous_const_smul q).measurable hs]
  show _ = ((Δ q⁻¹ : ℝ≥0) • μ) s
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Set.preimage_smul]
  exact (hmul q⁻¹ s).symm

end GlobalTheory.CompanionTheory.SW
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianUnitFormRepresentsUnit
section
open Matrix HeckeCharacterZeroLocus.SiegelWeilU

namespace GlobalTheory.CompanionTheory.SW.UnitRep

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem hform_add_left (σ : A →+* A) (J : Matrix n n A) (x x' y : n → A) :
    hform σ J (x + x') y = hform σ J x y + hform σ J x' y := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_add_right (σ : A →+* A) (J : Matrix n n A) (x y y' : n → A) :
    hform σ J x (y + y') = hform σ J x y + hform σ J x y' := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_left' (σ : A →+* A) (J : Matrix n n A) (a : A) (x y : n → A) :
    hform σ J (a • x) y = σ a * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem hform_smul_right' (σ : A →+* A) (J : Matrix n n A) (a : A) (x y : n → A) :
    hform σ J x (a • y) = a * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_single_single (σ : A →+* A) (J : Matrix n n A) (i j : n) :
    hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  rw [hform, Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · simp

theorem hform_self_fixed (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (J : Matrix n n A)
    (hJ : ∀ i j, σ (J j i) = J i j) (x : n → A) : σ (hform σ J x x) = hform σ J x x := by
  simp only [hform, map_sum, map_mul, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ i j]; ring

theorem hform_self_congr (σ : A →+* A) (J : Matrix n n A) (P : Ideal A) (x z : n → A)
    (h₁ : ∀ i, z i - x i ∈ P) (h₂ : ∀ i, σ (z i - x i) ∈ P) :
    hform σ J z z - hform σ J x x ∈ P := by
  have e₁ : ∀ i, Ideal.Quotient.mk P (z i) = Ideal.Quotient.mk P (x i) := fun i =>
    Ideal.Quotient.eq.2 (h₁ i)
  have e₂ : ∀ i, Ideal.Quotient.mk P (σ (z i)) = Ideal.Quotient.mk P (σ (x i)) := fun i =>
    Ideal.Quotient.eq.2 (by simpa only [map_sub] using h₂ i)
  refine Ideal.Quotient.eq.1 ?_
  simp only [hform, map_sum, map_mul, e₁, e₂]

theorem exists_hform_not_mem (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (h2 : IsUnit (2 : A))
    (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ) (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A)
    (hdet : IsUnit J.det) (P : Ideal A) (hP : P.IsMaximal) :
    ∃ y, hform σ J y y ∉ P := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨δ, hδu, hδσ⟩ := hδ
  have hpol : ∀ x y, hform σ J x y + hform σ J y x ∈ P := fun x y => by
    have h := hcon (x + y)
    rw [hform_add_left, hform_add_right, hform_add_right] at h
    have h' := P.sub_mem (P.sub_mem h (hcon x)) (hcon y)
    convert h' using 1
    ring
  have hpol' : ∀ x y, δ * (hform σ J x y - hform σ J y x) ∈ P := fun x y => by
    have h := hpol x (δ • y)
    rw [hform_smul_right', hform_smul_left', hδσ] at h
    convert h using 1
    ring
  have hall : ∀ x y, hform σ J x y ∈ P := fun x y => by
    have h₁ : hform σ J x y - hform σ J y x ∈ P :=
      (Ideal.unit_mul_mem_iff_mem P hδu).1 (hpol' x y)
    have h₂ : 2 * hform σ J x y ∈ P := by
      convert P.add_mem (hpol x y) h₁ using 1
      ring
    exact (Ideal.unit_mul_mem_iff_mem P h2).1 h₂
  have hJ0 : (Ideal.Quotient.mk P).mapMatrix J = 0 := by
    ext i j
    have h := hall (Pi.single i 1) (Pi.single j 1)
    rw [hform_single_single] at h
    simpa using Ideal.Quotient.eq_zero_iff_mem.2 h
  have hd : J.det ∈ P := by
    refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [RingHom.map_det, hJ0, Matrix.det_zero]
  exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P hd hdet)

theorem comap_isMaximal (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (P : Ideal A) (hP : P.IsMaximal) :
    (P.comap σ).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective σ (fun y => ⟨σ y, hσ y⟩)

theorem isCoprime_of_mem_not_mem {P Q : Ideal A} (hP : P.IsMaximal) (hQ : Q.IsMaximal) {a : A}
    (ha : a ∈ P) (ha' : a ∉ Q) : IsCoprime P Q := by
  rw [Ideal.isCoprime_iff_sup_eq]
  refine hP.coprime_of_ne hQ ?_
  rintro rfl
  exact ha' ha

theorem exists_good_on_finset [Finite (MaximalSpectrum A)] (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y)
    (h2 : IsUnit (2 : A)) (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ) (m : ℕ)
    (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (hJ : ∀ i j, σ (J j i) = J i j)
    (hdet : IsUnit J.det) (T : Finset (MaximalSpectrum A)) :
    ∃ x, ∀ p ∈ T, hform σ J x x ∉ p.asIdeal := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert q T _ ih =>
    obtain ⟨x, hx⟩ := ih
    by_cases hxq : hform σ J x x ∈ q.asIdeal
    swap
    · refine ⟨x, fun p hp => ?_⟩
      rcases Finset.mem_insert.1 hp with rfl | hp
      · exact hxq
      · exact hx p hp
    obtain ⟨y, hy⟩ := exists_hform_not_mem σ hσ h2 hδ m J hdet q.asIdeal q.isMaximal
    have hfix := hform_self_fixed σ hσ J hJ x
    have hmemc : ∀ {P : Ideal A}, hform σ J x x ∈ P → hform σ J x x ∈ P.comap σ := fun h => by
      rw [Ideal.mem_comap, hfix]; exact h
    have hnotc : ∀ {P : Ideal A}, hform σ J x x ∉ P → hform σ J x x ∉ P.comap σ := fun h h' => by
      rw [Ideal.mem_comap, hfix] at h'; exact h h'
    have hqm := q.isMaximal
    have hqc := comap_isMaximal σ hσ q.asIdeal q.isMaximal
    have hL : ∀ {Q : Ideal A}, Q.IsMaximal → hform σ J x x ∉ Q →
        IsCoprime (q.asIdeal * q.asIdeal.comap σ) Q := fun hQ hn =>
      IsCoprime.mul_left (isCoprime_of_mem_not_mem hqm hQ hxq hn)
        (isCoprime_of_mem_not_mem hqc hQ (hmemc hxq) hn)
    have hK₁ : IsCoprime (q.asIdeal * q.asIdeal.comap σ) (⨅ p ∈ T, p.asIdeal) :=
      Ideal.isCoprime_biInf fun p hp => hL p.isMaximal (hx p hp)
    have hK₂ : IsCoprime (q.asIdeal * q.asIdeal.comap σ) (⨅ p ∈ T, p.asIdeal.comap σ) :=
      Ideal.isCoprime_biInf fun p hp =>
        hL (comap_isMaximal σ hσ _ p.isMaximal) (hnotc (hx p hp))
    obtain ⟨u, hu, c, hc, huc⟩ := Ideal.isCoprime_iff_exists.1 (hK₁.mul_right hK₂)
    have hc₁ : ∀ p ∈ T, c ∈ p.asIdeal := fun p hp =>
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (Ideal.mul_le_left hc) p) hp
    have hc₂ : ∀ p ∈ T, σ c ∈ p.asIdeal := fun p hp =>
      Ideal.mem_comap.1 ((Submodule.mem_iInf _).1
        ((Submodule.mem_iInf _).1 (Ideal.mul_le_right hc) p) hp)
    have hu₁ : u ∈ q.asIdeal := Ideal.mul_le_right (I := q.asIdeal.comap σ) (by rwa [mul_comm] at hu)
    have hu₂ : σ u ∈ q.asIdeal := Ideal.mem_comap.1 (Ideal.mul_le_left (J := q.asIdeal) (by rwa [mul_comm] at hu))
    refine ⟨u • x + c • y, fun p hp => ?_⟩
    have hu' : u = 1 - c := by rw [← huc]; ring
    rcases Finset.mem_insert.1 hp with rfl | hp
    · intro hz
      refine hy ?_
      have h := hform_self_congr σ J p.asIdeal y (u • x + c • y)
        (fun i => ?_) (fun i => ?_)
      · simpa using p.asIdeal.sub_mem hz h
      · have : (u • x + c • y) i - y i = u * (x i - y i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this]
        exact p.asIdeal.mul_mem_right _ hu₁
      · have : (u • x + c • y) i - y i = u * (x i - y i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this, map_mul]
        exact p.asIdeal.mul_mem_right _ hu₂
    · intro hz
      refine hx p hp ?_
      have h := hform_self_congr σ J p.asIdeal x (u • x + c • y)
        (fun i => ?_) (fun i => ?_)
      · simpa using p.asIdeal.sub_mem hz h
      · have : (u • x + c • y) i - x i = c * (y i - x i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this]
        exact p.asIdeal.mul_mem_right _ (hc₁ p hp)
      · have : (u • x + c • y) i - x i = c * (y i - x i) := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu']; ring
        rw [this, map_mul]
        exact p.asIdeal.mul_mem_right _ (hc₂ p hp)

theorem exists_isUnit_hform : ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A),
    (∀ y, σ (σ y) = y) → IsUnit (2 : A) → (∃ δ : A, IsUnit δ ∧ σ δ = -δ) →
    ∀ (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A), (∀ i j, σ (J j i) = J i j) →
    IsUnit J.det → ∃ x, IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hform σ J x x) := by
  intro A _ _ σ hσ h2 hδ m J hJ hdet
  have := Fintype.ofFinite (MaximalSpectrum A)
  obtain ⟨x, hx⟩ := exists_good_on_finset σ hσ h2 hδ m J hJ hdet Finset.univ
  refine ⟨x, ?_⟩
  by_contra hnu
  obtain ⟨P, hP, hmem⟩ := exists_max_ideal_of_mem_nonunits hnu
  exact hx ⟨P, hP⟩ (Finset.mem_univ _) hmem

end GlobalTheory.CompanionTheory.SW.UnitRep
end

