import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import GroundTheory.GlobalFields.TateThesis.HeckeChar
import GroundTheory.LocalFields.LocalZetaEpsilon
import GroundTheory.LocalFields.LocalZetaGauss

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.ContinuousOfIsSmoothChar
section
noncomputable section

namespace PositivityTheory.Pf1.LocalLanglands.KernelCondition.G7

section Bridge

open ValuativeRel GroundTheory.LocalField

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ord_eq (x : kˣ) : GlobalTheory.SmGL.ord k x = ord (x : k) := by
  simp [GlobalTheory.SmGL.ord, ord, normalizedValuation_apply]

theorem val_le_iff_mem (y : k) (x : kˣ) : valuation k y ≤ valuation k (x : k) ↔ y ∈ valBall k (ord (x : k)) := by
  rw [mem_valBall, ← normalizedValuation_eq_exp_ord x.ne_zero, normalizedValuation_le_iff]

theorem mul_mem_valBall_iff (g : kˣ) (z : k) (j : ℤ) :
    (g : k) * z ∈ valBall k j ↔ z ∈ valBall k (j - ord (g : k)) := by
  by_cases hz : z = 0
  · subst hz; simp only [mul_zero]; exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  · rw [mem_valBall_iff_le_ord (mul_ne_zero g.ne_zero hz), mem_valBall_iff_le_ord hz, ord_mul g.ne_zero hz]
    omega

theorem continuous_of_isSmoothChar (χ : kˣ →* ℂˣ) (hχ : GlobalTheory.SmGL.IsSmoothChar χ) : Continuous χ := by
  refine continuous_of_continuousAt_one χ ?_
  have h : (χ.ker : Set kˣ) ∈ nhds (1 : kˣ) := hχ.mem_nhds χ.ker.one_mem
  refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
  filter_upwards [h] with x hx
  exact (MonoidHom.mem_ker.mp hx).symm

theorem hasConductor (ψ : AddChar k Circle) (hψ : Continuous ψ) (h1 : ψ ≠ 1) :
    GlobalTheory.SplitWeil.HasConductor ψ (unifUnit k ^ addCharConductor ψ) := by
  intro x
  rw [val_le_iff_mem x (unifUnit k ^ addCharConductor ψ), ord_unifUnit_zpow]
  constructor
  · intro h
    by_cases hx : x = 0
    · subst hx; exact zero_mem _
    · have htriv : IsTrivialOn ψ (ord x) := fun y hy => h y (by
        rw [← normalizedValuation_le_iff, normalizedValuation_eq_exp_ord hx]; exact hy)
      exact (mem_valBall_iff_le_ord hx).2 ((isTrivialOn_iff hψ h1 (ord x)).1 htriv)
  · intro hx y hy
    exact isTrivialOn_addCharConductor hψ h1 y ((normalizedValuation_le_iff.2 hy).trans hx)

theorem mem_unitFilt_iff (b : ℕ) (x : kˣ) :
    x ∈ GlobalTheory.LocLanglands.unitFilt k b ↔ x ∈ unitFiltrationUnits k b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [mem_unitFiltrationUnits_zero_iff]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    rw [pow_zero]
    exact (Valuation.map_sub _ _ _).trans (by simp [h])
  · rw [mem_unitFiltrationUnits_iff_valBall hb]
    obtain ⟨p, hp, hpo⟩ := GlobalTheory.LocLanglands.exists_unit_pow k b
    have hpo' : ord (p : k) = b := by rw [← ord_eq]; exact hpo
    constructor
    · intro h
      have := (val_le_iff_mem ((x : k) - 1) p).1 (h.2.trans_eq hp.symm)
      rwa [hpo'] at this
    · intro h
      refine ⟨mem_unitFiltrationUnits_zero_iff.1
        (unitFiltrationUnits_antitone (Nat.zero_le b) ((mem_unitFiltrationUnits_iff_valBall hb).2 h)), ?_⟩
      rw [← hp]
      exact (val_le_iff_mem ((x : k) - 1) p).2 (by rwa [hpo'])

theorem hasExponent (χ : kˣ →* ℂˣ) (hχ : Continuous χ) :
    GlobalTheory.LocLanglands.HasExponent χ (quasiCharConductor χ) := by
  refine ⟨fun x hx => unitFiltrationUnits_quasiCharConductor_le_ker hχ ((mem_unitFilt_iff _ x).1 hx), fun b hb => ?_⟩
  by_contra h
  push Not at h
  have hle : quasiCharConductor χ ≤ b :=
    Nat.sInf_le (fun x hx => MonoidHom.mem_ker.2 (h x ((mem_unitFilt_iff b x).2 hx)))
  omega

theorem isUnram_of (χ : kˣ →* ℂˣ) (hu : IsUnramifiedChar χ) : GlobalTheory.SplitWeil.IsUnram χ := fun x hx =>
  isUnramifiedChar_iff.1 hu x (by rw [← ord_eq]; exact GlobalTheory.SmGL.ord_eq_zero hx)

theorem nabs_unif (n : ℤ) : GlobalTheory.SplitWeil.nabs k (unifUnit k ^ n) = (residueCard k : ℝ) ^ (-n) := by
  rw [GlobalTheory.LGrp.nabs_eq_zpow, ord_eq, ord_unifUnit_zpow]
  rfl

end Bridge

end PositivityTheory.Pf1.LocalLanglands.KernelCondition.G7

end

noncomputable section

namespace PositivityTheory.Pf1.LocalLanglands.KernelCondition.G7

section Shell

open ValuativeRel GroundTheory.LocalField

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def shellPt (m : ℤ) {a : ℕ} (t : unitsModFiltration k a) : kˣ := unifUnit k ^ m * unitsModRep t

theorem ord_shellPt (m : ℤ) {a : ℕ} (t : unitsModFiltration k a) : ord ((shellPt m t : kˣ) : k) = m := by
  rw [shellPt, ord_units_mul, ord_unifUnit_zpow, mem_unitFiltrationUnits_zero_iff_ord.1 (unitsModRep_mem t), add_zero]

theorem shellPt_injective (m : ℤ) (a : ℕ) : Function.Injective (shellPt (k := k) m (a := a)) := by
  intro x y h
  have h2 : unitsModRep x = unitsModRep y := mul_left_cancel h
  exact Quotient.out_inj.1 (Subtype.ext h2)

theorem shell_val_le_iff {n : ℤ} {a : ℕ} (ha : 1 ≤ a) (y : kˣ)
    (t : unitsModFiltration k a) :
    valuation k ((y : k) - (shellPt (n - a) t : k)) ≤ valuation k ((unifUnit k ^ n : kˣ) : k) ↔
      unifUnit k ^ (-(n - a)) * y ∈ unitsModCoset t := by
  set m : ℤ := n - a
  set u : kˣ := unifUnit k ^ (-m) * y
  set w : kˣ := unitsModRep t
  have hy' : y = unifUnit k ^ m * u := by
    simp only [u, ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  have hw0 : ord (w : k) = 0 := mem_unitFiltrationUnits_zero_iff_ord.1 (unitsModRep_mem t)
  have hdiff : (y : k) - (shellPt m t : k) = ((unifUnit k ^ m * w : kˣ) : k) * (((w⁻¹ * u : kˣ) : k) - 1) := by
    have hw : (w : k) ≠ 0 := w.ne_zero
    rw [hy', shellPt]
    push_cast
    field_simp
    rfl
  rw [val_le_iff_mem, ord_unifUnit_zpow, hdiff, mul_mem_valBall_iff, ord_units_mul, ord_unifUnit_zpow, hw0,
    mem_unitsModCoset, mem_unitFiltrationUnits_iff_valBall ha]
  constructor <;> intro h <;> convert h using 2 <;> simp [m]

open Classical in

theorem isShellReps {n : ℤ} {a : ℕ} (ha : 1 ≤ a) :
    GlobalTheory.LocLanglands.IsShellReps (unifUnit k ^ n) a
      (Finset.univ.image (shellPt (k := k) (n - a) (a := a))) := by
  classical
  have hc : GlobalTheory.SmGL.ord k (unifUnit k ^ n) = n := by rw [ord_eq, ord_unifUnit_zpow]
  refine ⟨fun r hr => ?_, fun y hy => ?_⟩
  · obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hr
    rw [ord_eq, ord_shellPt, hc]
  · rw [hc, ord_eq] at hy
    set u : kˣ := unifUnit k ^ (-(n - a)) * y
    have hu0 : u ∈ unitFiltrationUnits k 0 := by
      rw [mem_unitFiltrationUnits_zero_iff_ord, ord_units_mul, ord_unifUnit_zpow, hy]
      ring
    refine ⟨shellPt (n - a) (QuotientGroup.mk ⟨u, hu0⟩ : unitsModFiltration k a),
      ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
        (shell_val_le_iff ha y _).2 (mem_unitsModCoset_mk hu0)⟩, ?_⟩
    rintro r ⟨hr, hv⟩
    obtain ⟨t', -, rfl⟩ := Finset.mem_image.1 hr
    rw [eq_of_mem_unitsModCoset ((shell_val_le_iff ha y t').1 hv) (mem_unitsModCoset_mk hu0)]

end Shell

end PositivityTheory.Pf1.LocalLanglands.KernelCondition.G7

end

noncomputable section

namespace PositivityTheory.Pf1.LocalLanglands.KernelCondition.G7

section Main

open ValuativeRel GroundTheory.LocalField

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

omit [MeasurableSpace k] [BorelSpace k] in

theorem real_factor (t : ℝ) (n : ℤ) :
    ((t / (residueCard k : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * (residueCard k : ℂ) ^ (-(n : ℂ) / 2) =
      ((t * (residueCard k : ℝ) ^ (-n) : ℝ) : ℂ) := by
  have hq : (0 : ℝ) < (residueCard k : ℝ) := residueCard_pos_real
  rw [show (residueCard k : ℂ) ^ (-(n : ℂ) / 2) = (((residueCard k : ℝ) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) by
    rw [Complex.ofReal_cpow hq.le]; push_cast; ring_nf]
  rw [← Complex.ofReal_mul]
  congr 1
  rw [div_eq_mul_inv, ← Real.rpow_neg hq.le, mul_assoc, ← Real.rpow_add hq, ← Real.rpow_intCast]
  congr 2
  push_cast
  ring

theorem main (ψ : AddChar k Circle) (hψ : Continuous ψ) (h1 : ψ ≠ 1) (χ : kˣ →* ℂˣ)
    (hχ : GlobalTheory.SmGL.IsSmoothChar χ) (t : ℝ) :
    GlobalTheory.LocLanglands.IsTateMeas ψ t χ (((t / (selfDualMeasure ψ (valBall k 0 : Set k)).toReal : ℝ) : ℂ) *
      localEpsilon χ ψ 0) := by
  classical
  have hχc := continuous_of_isSmoothChar χ hχ
  have hvol : (selfDualMeasure ψ (valBall k 0 : Set k)).toReal =
      (residueCard k : ℝ) ^ ((addCharConductor ψ : ℝ) / 2) := selfDualMeasure_real_valBall_zero ψ
  rw [hvol]
  have hc := hasConductor ψ hψ h1
  by_cases hu : IsUnramifiedChar χ
  · have := GlobalTheory.LocLanglands.MeasModel.isTateMeas_of_isUnram hc (isUnram_of χ hu) t
    convert this using 1
    rw [localEpsilon_of_isUnramified hu, nabs_unif, map_zpow, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
      ← zpow_neg]
    have e : (residueCard k : ℂ) ^ ((addCharConductor ψ : ℂ) * (0 - 1 / 2)) =
        (residueCard k : ℂ) ^ (-(addCharConductor ψ : ℂ) / 2) := by congr 1; ring
    rw [e, ← real_factor]
    ring
  · have ha := hasExponent χ hχc
    have ha1 := quasiCharConductor_pos hχc hu
    refine ⟨_, _, _, hc, ha, isShellReps (n := addCharConductor ψ) ha1, ?_⟩
    rw [Finset.sum_image (fun x _ y _ h => shellPt_injective _ _ h), localEpsilon_eq_gaussSum hψ h1 hχc hu 0,
      nabs_unif]
    have e : (residueCard k : ℂ) ^ (((addCharConductor ψ - quasiCharConductor χ : ℤ) : ℂ) * 0 -
        (addCharConductor ψ : ℂ) / 2) = (residueCard k : ℂ) ^ (-(addCharConductor ψ : ℂ) / 2) := by
      congr 1; ring
    rw [e, ← mul_assoc, real_factor, GroundTheory.LocalField.gaussSum]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Units.val_inv_eq_inv_val]
    rfl

end Main

end PositivityTheory.Pf1.LocalLanglands.KernelCondition.G7

end

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands.KernelCondition

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable [MeasurableSpace k] [BorelSpace k]

theorem isTateMeas_localEpsilon (ψ : AddChar k Circle) (hψ : Continuous ψ) (h1 : ψ ≠ 1) (χ : kˣ →* ℂˣ)
    (hχ : IsSmoothChar χ) (t : ℝ) (ht : 0 < t) :
    IsTateMeas ψ t χ (((t / (GroundTheory.LocalField.selfDualMeasure ψ (GroundTheory.LocalField.valBall k 0 : Set k)).toReal : ℝ) : ℂ) *
      GroundTheory.LocalField.localEpsilon χ ψ 0) :=
  G7.main ψ hψ h1 χ hχ t

end Local

end PositivityTheory.Pf1.LocalLanglands.KernelCondition
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.HasExponentMulOfIsUnram
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands

section Tate

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ψ : AddChar k Circle} {χ : kˣ →* ℂˣ} {t : ℝ} {e : ℂ}

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem val_mul_le_iff (b : kˣ) {x y : k} :
    valuation k ((b : k) * y) ≤ valuation k ((b : k) * x) ↔ valuation k y ≤ valuation k x := by
  constructor
  · intro h
    have := mul_le_mul' (le_refl (valuation k ((b⁻¹ : kˣ) : k))) h
    rwa [← map_mul, ← map_mul, ← mul_assoc, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul,
      one_mul] at this
  · intro h
    rw [map_mul, map_mul]
    exact mul_le_mul' le_rfl h

theorem IsShellReps.map_mul {c : kˣ} {a : ℕ} {R : Finset kˣ} (hR : IsShellReps c a R) (b : kˣ) :
    IsShellReps (b * c) a (R.map (mulLeftEmbedding b)) := by
  refine ⟨fun r hr => ?_, fun y hy => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_map.1 hr
    simp only [mulLeftEmbedding_apply, ord_mul, hR.1 s hs]
    ring
  · have h1 : ord k (b⁻¹ * y) = ord k c - a := by
      have := ord_mul k b (b⁻¹ * y)
      rw [mul_inv_cancel_left] at this
      rw [ord_mul] at hy
      omega
    have h2 : ∀ r : kˣ, valuation k ((y : k) - (b * r : kˣ)) ≤ valuation k ((b * c : kˣ) : k) ↔
        valuation k (((b⁻¹ * y : kˣ) : k) - r) ≤ valuation k (c : k) := fun r => by
      rw [← val_mul_le_iff b (x := (c : k)) (y := ((b⁻¹ * y : kˣ) : k) - r)]
      have e2 : (b : k) * (((b⁻¹ * y : kˣ) : k) - r) = (y : k) - (b * r : kˣ) := by
        simp [mul_sub]
      rw [e2]
      simp only [Units.val_mul]
    obtain ⟨r, hr, hr'⟩ := hR.2 _ h1
    refine ⟨b * r, ⟨Finset.mem_map_of_mem _ hr.1, (h2 r).2 hr.2⟩, ?_⟩
    rintro _ ⟨hm, hv⟩
    obtain ⟨r', hm', rfl⟩ := Finset.mem_map.1 hm
    rw [mulLeftEmbedding_apply, hr' r' ⟨hm', (h2 r').1 hv⟩]

theorem hasExponent_mul_of_isUnram {μ : kˣ →* ℂˣ} (hμ : IsUnram μ) {a : ℕ} :
    HasExponent (χ * μ) a ↔ HasExponent χ a := by
  have key : ∀ b, ∀ x ∈ unitFilt k b, (χ * μ) x = χ x := fun b x hx => by
    rw [MonoidHom.mul_apply, hμ x hx.1, mul_one]
  unfold HasExponent
  exact and_congr (forall₂_congr fun x hx => by rw [key _ x hx])
    (forall₂_congr fun b _ => exists_congr fun x => and_congr_right fun hx => by rw [key _ x hx])

theorem isTateMeas_mul_of_const {μ : kˣ →* ℂˣ} (hμ : IsUnram μ) {c : kˣ} {a : ℕ} (hc : HasConductor ψ c)
    (ha : HasExponent χ a) {m : ℂˣ} (hm : ∀ r : kˣ, ord k r = ord k c - a → μ r = m) (he : IsTateMeas ψ t χ e) :
    IsTateMeas ψ t (χ * μ) (((m⁻¹ : ℂˣ) : ℂ) * e) := by
  obtain ⟨c', a', R, hc', ha', hR, rfl⟩ := he
  obtain rfl := ha'.unique ha
  have hord : ord k c' = ord k c :=
    valuation_eq_iff_ord.1 (le_antisymm ((hc _).1 ((hc' _).2 le_rfl)) ((hc' _).1 ((hc _).2 le_rfl)))
  refine ⟨c', a', R, hc', (hasExponent_mul_of_isUnram hμ).2 ha', hR, ?_⟩
  have hs : ∑ r ∈ R, ((((χ * μ) r)⁻¹ : ℂˣ) : ℂ) * (ψ (r : k) : ℂ) =
      ((m⁻¹ : ℂˣ) : ℂ) * ∑ r ∈ R, (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (r : k) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [MonoidHom.mul_apply, hm r ((hR.1 r hr).trans (by rw [hord])), mul_inv, Units.val_mul]
    ring
  rw [hs]
  ring

theorem isTateMeas_mul_unrChar (α : ℂˣ) {c : kˣ} {a : ℕ} (hc : HasConductor ψ c) (ha : HasExponent χ a)
    (he : IsTateMeas ψ t χ e) :
    IsTateMeas ψ t (χ * GlobalTheory.SmGL.unrChar k α) (((α ^ ((a : ℤ) - ord k c) : ℂˣ) : ℂ) * e) := by
  have := isTateMeas_mul_of_const (isUnram_unrChar k α) hc ha (m := α ^ (ord k c - a))
    (fun r hr => by rw [GlobalTheory.SmGL.unrChar_apply, hr]) he
  rwa [← zpow_neg, neg_sub] at this

end Tate

section WDTwist

variable {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
  {E : Type} [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] {w : HeightOneSpectrum (𝓞 E)}
  {h : IsPlaceOver A w}

theorem lpTwist_lpOfChar_unr {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    {χ : (w.adicCompletion E)ˣ →* ℂˣ} (hχ : IsSmoothChar χ) (z : ℂˣ) :
    (WD.lpOfChar h (χ.comp a) (ha.smooth hχ)).lpTwist (GlobalTheory.WeilDeligne.unrChar h z) (isSmooth_unrChar h z) =
      WD.lpOfChar h ((χ * GlobalTheory.SmGL.unrChar _ z⁻¹).comp a)
        (ha.smooth (hχ.mul (isSmoothChar_of_isUnram (isUnram_unrChar _ _)))) := by
  rw [WD.lpOfChar, WD.lpOfChar, WD.lpTwist_mk]
  refine WD.sound ⟨.refl _ _, fun σ u => ?_, fun u => rfl⟩
  have key : GlobalTheory.SmGL.unrChar _ z⁻¹ (a σ) = GlobalTheory.WeilDeligne.unrChar h z σ := by
    rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.WeilDeligne.unrChar_apply, ha.ord_eq, inv_zpow', neg_neg]
  funext i
  simp [WDRep.twist, key, mul_comm, mul_left_comm]

end WDTwist

end PositivityTheory.Pf1.LocalLanglands

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.IsTateMeasMulHighlyRamified
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands.UnitFiltration

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_close {θ : kˣ →* ℂˣ} {m : ℕ} (hθ : ∀ x ∈ unitFilt k m, θ x = 1) {u s : kˣ}
    (hus : valuation k (u : k) = valuation k (s : k))
    (h : valuation k ((u : k) - s) ≤ uniformizer k ^ m * valuation k (s : k)) : θ u = θ s := by
  have hs0 : 0 < valuation k (s : k) := by simp [zero_lt_iff]
  have hmem : u * s⁻¹ ∈ unitFilt k m := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hus, mul_inv_cancel₀ hs0.ne']
    · have e : ((u * s⁻¹ : kˣ) : k) - 1 = ((u : k) - s) * (s : k)⁻¹ := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ s.ne_zero]
      rw [e, map_mul, map_inv₀, mul_inv_le_iff₀ hs0]
      exact h
  have := hθ _ hmem
  rwa [map_mul, map_inv, mul_inv_eq_one] at this

def ballSub (p : kˣ) : AddSubgroup k where
  carrier := cball p
  add_mem' := add_mem_cball
  zero_mem' := by simp [cball]
  neg_mem' := neg_mem_cball

theorem mem_ballSub {p : kˣ} {z : k} : z ∈ ballSub p ↔ valuation k z ≤ valuation k (p : k) := Iff.rfl

theorem val_one_add {p : kˣ} (hp : valuation k (p : k) < 1) (z : ballSub p) : valuation k (1 + (z : k)) = 1 :=
  Valuation.map_one_add_of_lt _ (lt_of_le_of_lt (mem_ballSub.1 z.2) hp)

def onePlus {p : kˣ} (hp : valuation k (p : k) < 1) (z : ballSub p) : kˣ :=
  Units.mk0 (1 + (z : k)) (fun h0 => by
    have := val_one_add hp z
    rw [h0, map_zero] at this
    exact zero_ne_one this)

@[simp] theorem val_onePlus {p : kˣ} (hp : valuation k (p : k) < 1) (z : ballSub p) :
    ((onePlus hp z : kˣ) : k) = 1 + (z : k) := rfl

def addCharOn (ψ : AddChar k Circle) (p : kˣ) (w : k) : Multiplicative (ballSub p) →* ℂ where
  toFun z := (ψ (w * ((Multiplicative.toAdd z : ballSub p) : k)) : ℂ)
  map_one' := by simp
  map_mul' x y := by simp [mul_add, AddChar.map_add_eq_mul]

@[simp] theorem addCharOn_apply (ψ : AddChar k Circle) (p : kˣ) (w : k) (z : Multiplicative (ballSub p)) :
    addCharOn ψ p w z = (ψ (w * ((Multiplicative.toAdd z : ballSub p) : k)) : ℂ) := rfl

def alphaChar (α : kˣ →* ℂˣ) {p : kˣ} (hp : valuation k (p : k) < 1) {m : ℕ} (hα : ∀ x ∈ unitFilt k m, α x = 1)
    (hpm : valuation k (p : k) * valuation k (p : k) ≤ uniformizer k ^ m) : Multiplicative (ballSub p) →* ℂ where
  toFun z := (α (onePlus hp (Multiplicative.toAdd z)) : ℂ)
  map_one' := by
    have : onePlus hp (Multiplicative.toAdd (1 : Multiplicative (ballSub p))) = 1 := Units.ext (by simp)
    rw [this, map_one, Units.val_one]
  map_mul' x y := by
    rw [← Units.val_mul, ← map_mul]
    congr 1
    refine (eq_of_close hα ?_ ?_).symm
    · rw [Units.val_mul, map_mul, val_onePlus, val_onePlus, val_onePlus, val_one_add hp, val_one_add hp, mul_one]
      have := val_one_add hp (Multiplicative.toAdd (x * y))
      simpa using this.symm
    · have e : ((onePlus hp (Multiplicative.toAdd x) * onePlus hp (Multiplicative.toAdd y) : kˣ) : k) -
          ((onePlus hp (Multiplicative.toAdd (x * y)) : kˣ) : k) =
          ((Multiplicative.toAdd x : ballSub p) : k) * ((Multiplicative.toAdd y : ballSub p) : k) := by
        simp only [Units.val_mul, val_onePlus, toAdd_mul, AddSubgroup.coe_add]
        ring
      have h1 := val_one_add hp (Multiplicative.toAdd (x * y))
      rw [e, map_mul, val_onePlus, h1, mul_one]
      exact (mul_le_mul' (mem_ballSub.1 (Multiplicative.toAdd x).2) (mem_ballSub.1 (Multiplicative.toAdd y).2)).trans hpm

@[simp] theorem alphaChar_apply (α : kˣ →* ℂˣ) {p : kˣ} (hp : valuation k (p : k) < 1) {m : ℕ}
    (hα : ∀ x ∈ unitFilt k m, α x = 1) (hpm : valuation k (p : k) * valuation k (p : k) ≤ uniformizer k ^ m)
    (z : Multiplicative (ballSub p)) :
    alphaChar α hp hα hpm z = (α (onePlus hp (Multiplicative.toAdd z)) : ℂ) := rfl

end Local

section Sums

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ψ : AddChar k Circle} {c : kˣ} {m : ℕ} {R : Finset kˣ} {θ : kˣ →* ℂˣ}

end Sums

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Local

end PositivityTheory.Pf1.LocalLanglands.UnitFiltration

end
end

