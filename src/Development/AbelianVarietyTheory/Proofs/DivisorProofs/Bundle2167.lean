import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfGrowthOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2158
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2112
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2154
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2152
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2135
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGrowthOnComponentNsmul
section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Filter
open scoped ENNReal NNReal

namespace GlobalTheory.GrowthMul

theorem limsup_le_iSup_classes {a : ℕ} (ha : 1 ≤ a) (f : ℕ → ℝ≥0∞) :
    limsup f atTop ≤ ⨆ j : Fin a, limsup (fun k => f (a * k + j)) atTop := by
  refine le_of_forall_gt_imp_ge_of_dense fun x hx => ?_
  have h1 : ∀ j : Fin a, ∀ᶠ k in atTop, f (a * k + j) < x := fun j =>
    eventually_lt_of_limsup_lt ((le_iSup (fun j : Fin a => limsup (fun k => f (a * k + j)) atTop) j).trans_lt hx)
  choose K hK using fun j => eventually_atTop.1 (h1 j)
  refine limsup_le_of_le (by isBoundedDefault) (eventually_atTop.2 ⟨a * Finset.univ.sup K, fun τ hτ => ?_⟩)
  have hm : τ % a < a := Nat.mod_lt _ (by omega)
  have hq : Finset.univ.sup K ≤ τ / a := (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact hτ)
  have := hK ⟨τ % a, hm⟩ (τ / a) ((Finset.le_sup (Finset.mem_univ _)).trans hq)
  rw [Nat.div_add_mod] at this
  exact this.le

theorem term_mul_eq (D : ℕ) {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℕ∞) {k : ℕ} (hk : 1 ≤ k) :
    (D.factorial : ℝ≥0∞) * (r (a * k) : ℝ≥0∞) / (k : ℝ≥0∞) ^ D =
      (a : ℝ≥0∞) ^ D * ((D.factorial : ℝ≥0∞) * (r (a * k) : ℝ≥0∞) / ((a * k : ℕ) : ℝ≥0∞) ^ D) := by
  have ha0 : (a : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hat : (a : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
  rw [Nat.cast_mul, mul_pow, ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ ha0 hat, mul_comm]

theorem growth_mul_le (D : ℕ) {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℕ∞) :
    growth D (fun k => r (a * k)) ≤ (a : ℝ≥0∞) ^ D * growth D r := by
  have hat : (a : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
  set g : ℕ → ℝ≥0∞ := fun τ => (D.factorial : ℝ≥0∞) * (r τ : ℝ≥0∞) / (τ : ℝ≥0∞) ^ D
  have h1 : growth D (fun k => r (a * k)) = limsup (fun k => (a : ℝ≥0∞) ^ D * g (a * k)) atTop :=
    limsup_congr ((eventually_ge_atTop 1).mono fun k hk => term_mul_eq D ha r hk)
  rw [h1, ENNReal.limsup_const_mul_of_ne_top hat, growth]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le)
  have ht : Tendsto (fun k : ℕ => a * k) atTop atTop :=
    tendsto_id.const_mul_atTop' (by omega)
  exact (limsup_comp g (fun k => a * k) atTop).le.trans (limsup_le_limsup_of_le ht)

theorem limsup_class_le (D : ℕ) {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℕ∞) (j c : ℕ)
    (h : ∀ k, r (a * k + j) ≤ r (a * (k + c))) :
    limsup (fun k => (D.factorial : ℝ≥0∞) * (r (a * k + j) : ℝ≥0∞) / ((a * k + j : ℕ) : ℝ≥0∞) ^ D) atTop ≤
      ((a : ℝ≥0∞) ^ D)⁻¹ * growth D (fun k => r (a * k)) := by
  have ha0 : (a : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hit : ((a : ℝ≥0∞) ^ D)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 ha0
  refine (limsup_le_limsup ((eventually_ge_atTop 1).mono fun k hk => ?_)).trans
    ((ENNReal.limsup_const_mul_of_ne_top hit).le.trans (by gcongr; exact GlobalTheory.GrowthShift.growth_shift_le D c _))
  show _ ≤ ((a : ℝ≥0∞) ^ D)⁻¹ * ((D.factorial : ℝ≥0∞) * (r (a * (k + c)) : ℝ≥0∞) / (k : ℝ≥0∞) ^ D)
  have hk0 : (k : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hkt : (k : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top k)
  have hat : (a : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
  have e : ((a : ℝ≥0∞) ^ D)⁻¹ * ((D.factorial : ℝ≥0∞) * (r (a * (k + c)) : ℝ≥0∞) / (k : ℝ≥0∞) ^ D) =
      (D.factorial : ℝ≥0∞) * (r (a * (k + c)) : ℝ≥0∞) / ((a : ℝ≥0∞) ^ D * (k : ℝ≥0∞) ^ D) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl ha0) (Or.inl hat)]
    ring
  rw [e]
  refine ENNReal.div_le_div (by gcongr; exact h k) ?_
  rw [← mul_pow]
  gcongr
  exact_mod_cast Nat.le_add_right _ _

theorem growth_mul_eq_of_classes (D : ℕ) {a : ℕ} (ha : 1 ≤ a) (r : ℕ → ℕ∞)
    (h : ∀ j, j < a → ∃ c, ∀ k, r (a * k + j) ≤ r (a * (k + c))) :
    growth D (fun k => r (a * k)) = (a : ℝ≥0∞) ^ D * growth D r := by
  refine le_antisymm (growth_mul_le D ha r) ?_
  have ha0 : (a : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hat : (a : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top a)
  have h1 : growth D r ≤ ((a : ℝ≥0∞) ^ D)⁻¹ * growth D (fun k => r (a * k)) := by
    refine (limsup_le_iSup_classes ha _).trans (iSup_le fun j => ?_)
    obtain ⟨c, hc⟩ := h j j.2
    exact limsup_class_le D ha r j c hc
  calc (a : ℝ≥0∞) ^ D * growth D r ≤ (a : ℝ≥0∞) ^ D * (((a : ℝ≥0∞) ^ D)⁻¹ * growth D (fun k => r (a * k))) :=
        mul_le_mul_of_nonneg_left h1 zero_le
    _ = growth D (fun k => r (a * k)) := by rw [← mul_assoc, ENNReal.mul_inv_cancel ha0 hat, one_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem pow_mul_mem_cuspOn {Z : Comp Xo c} {G : WTZ E} (hG : Even G.2) {τ₀ τ : ℕ} {g f : Rul Xo c}
    (hg : g ∈ cuspOn U Z (τ₀ • G)) (hf : f ∈ cuspOn U Z (τ • G)) (n : ℕ) :
    g ^ n * f ∈ cuspOn U Z ((τ + n * τ₀) • G) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    have e : (τ + (n + 1) * τ₀) • G = (τ + n * τ₀) • G + τ₀ • G := by rw [← add_nsmul]; ring_nf
    rw [e, pow_succ, mul_right_comm]
    exact GlobalTheory.DegTop.mul_mem_cuspOn (GlobalTheory.DegTop.even_nsmul hG _) (GlobalTheory.DegTop.even_nsmul hG _) ih hg.1

theorem rank_le_of_ne_zero {Z : Comp Xo c} {G : WTZ E} (hG : Even G.2) {τ₀ : ℕ} {g : Rul Xo c}
    (hg : g ∈ cuspOn U Z (τ₀ • G)) (hg0 : g ≠ 0) (τ n : ℕ) :
    Module.rank c.F (cuspOn U Z (τ • G)) ≤ Module.rank c.F (cuspOn U Z ((τ + n * τ₀) • G)) := by
  have hv : genVal Z g ≠ 0 := fun h0 => hg0 (GlobalTheory.DegTop.eq_zero_of_genVal hg h0)
  rw [← GlobalTheory.DegTop.rank_map_mul (U := U) (G := τ • G) (θ := g ^ n) (by rw [map_pow]; exact pow_ne_zero _ hv)]
  refine (Submodule.rank_mono ?_).trans (rank_map_le (genVal Z).toLinearMap _)
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨_, pow_mul_mem_cuspOn hG hg hf n, rfl⟩

theorem classes_bound (Z : Comp Xo c) {G : WTZ E} (hG : Even G.2) {a : ℕ} (ha : 1 ≤ a) (j : ℕ) :
    ∃ c' : ℕ, ∀ k, Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k + j) • G))) ≤
      Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * (k + c')) • G))) := by
  by_cases hex : ∃ q : ℕ, ∃ g ∈ cuspOn U Z ((a * q + j) • G), g ≠ 0
  · obtain ⟨q, g, hg, hg0⟩ := hex
    refine ⟨j + (a - 1) * q, fun k => ?_⟩
    have e : a * (k + (j + (a - 1) * q)) = (a * k + j) + (a - 1) * (a * q + j) := by
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [e]
    exact OrderHomClass.mono Cardinal.toENat (rank_le_of_ne_zero hG hg hg0 _ _)
  · push_neg at hex
    refine ⟨0, fun k => ?_⟩
    have h0 : cuspOn U Z ((a * k + j) • G) = ⊥ := (Submodule.eq_bot_iff _).2 (hex k)
    rw [h0, rank_bot, map_zero]
    exact zero_le

end GlobalTheory.GrowthMul

theorem GlobalTheory.GrowthMul.growthOn_nsmul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ (Z : Comp Xo c) (G : WTZ E), Even G.2 → ∀ a : ℕ, 1 ≤ a → growthOn U Z (a • G) = (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G := by
  intro E _ _ _ H Dw l Xo c r U _ Z G hG a ha
  rw [growthOn, growthOn]
  convert GlobalTheory.GrowthMul.growth_mul_eq_of_classes (dimFlag Dw) ha (fun τ => Cardinal.toENat (Module.rank c.F (cuspOn U Z (τ • G))))
    (fun j _ => GlobalTheory.GrowthMul.classes_bound (U := U) Z hG ha j) using 4 with τ
  rw [smul_smul, mul_comm]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsSupLatticeSplitOverComponents
section
noncomputable section

namespace GlobalTheory.CuspSplit

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 200000

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem idem_mul_mem_cuspOn (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (Z : Comp Xo c) {G : WTZ D.host.E}
    (F : cuspW Xo c U G) : idem Z * (F : Rul Xo c) ∈ cuspOn U Z G := by
  refine ⟨GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2, ?_⟩
  rw [mul_comm]
  exact mul_mem_suppOn _ (idem_mem_suppOn Z)

theorem idem_mul_of_mem_cuspOn {Z : Comp Xo c} {G : WTZ D.host.E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) :
    idem Z * f = f :=
  (mem_suppOn_iff_idem_mul (cuspW_le_secZ G hf.1) Z).1 hf.2

theorem idem_mul_eq_zero {Z Z' : Comp Xo c} (h : Z ≠ Z') {G : WTZ D.host.E} {f : Rul Xo c}
    (hf : f ∈ cuspOn U Z' G) : idem Z * f = 0 := by
  calc idem Z * f = idem Z * (idem Z' * f) := by rw [idem_mul_of_mem_cuspOn hf]
    _ = 0 := by rw [← mul_assoc, idem_mul_idem_of_ne h, zero_mul]

theorem finsum_parts (f : Rul Xo c) : ∑ᶠ Z : Comp Xo c, idem Z * f = f := by
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  rw [finsum_eq_sum_of_fintype, sum_idem_mul]

theorem mem_latOn_part (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G : WTZ D.host.E} (F : cuspW Xo c U G)
    (hF : F ∈ latW U G) (Z : Comp Xo c) :
    (⟨_, idem_mul_mem_cuspOn hU Z F⟩ : cuspOn U Z G) ∈ latOn U Z G := by
  rw [latOn, mem_supLat_iff (idem_mul_mem_cuspOn hU Z F).2]
  intro la v hv
  show 0 ≤ v (idem Z * (F : Rul Xo c))
  rw [(isVal_valOn hv).mul, val_idem hv, zero_add]
  exact (mem_supLat.1 hF) la v (valOn_subset Z la hv)

theorem mem_latW_of_parts (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G : WTZ D.host.E} (F : cuspW Xo c U G)
    (h : ∀ Z, (⟨_, idem_mul_mem_cuspOn hU Z F⟩ : cuspOn U Z G) ∈ latOn U Z G) : F ∈ latW U G := by
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  refine mem_supLat.2 ?_
  intro la v hv
  have hval := isVal_valSet la v hv
  rw [← sum_idem_mul (F : Rul Xo c)]
  refine Finset.sum_induction _ (fun x => 0 ≤ v x) (fun a b ha hb => (le_min ha hb).trans (hval.add a b))
    (by rw [hval.zero]; exact le_top) fun Z _ => ?_
  exact (mem_supLat.1 ((mem_latOn U).1 (h Z))) la v hv

theorem cuspOn_indep (G : WTZ D.host.E) : iSupIndep (fun Z : Comp Xo c => cuspOn U Z G) := fun Z => by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ Z), cuspOn U j G) ≤ LinearMap.ker (LinearMap.mulLeft c.F (idem Z)) :=
    iSup₂_le fun j hj y hy => by
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply]
      exact idem_mul_eq_zero (Ne.symm hj) hy
  have h0 : idem Z * x = 0 := by
    have := hle hx'
    rwa [LinearMap.mem_ker, LinearMap.mulLeft_apply] at this
  calc x = idem Z * x := (idem_mul_of_mem_cuspOn hx).symm
    _ = 0 := h0

theorem iSup_cuspOn (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (G : WTZ D.host.E) :
    ⨆ Z : Comp Xo c, cuspOn U Z G = cuspW Xo c U G := by
  refine le_antisymm (iSup_le fun Z => cuspOn_le U Z G) fun F hF => ?_
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  rw [← sum_idem_mul F]
  exact Submodule.sum_mem _ fun Z _ => Submodule.mem_iSup_of_mem Z (idem_mul_mem_cuspOn hU Z ⟨F, hF⟩)

theorem coe_mem_of_mem_partLat {Z : Comp Xo c} {G : WTZ D.host.E} {g : cuspW Xo c U G}
    (hg : g ∈ partLat U Z G) : (g : Rul Xo c) ∈ cuspOn U Z G := by
  obtain ⟨f, -, rfl⟩ := hg
  exact f.2

theorem partLat_indep (G : WTZ D.host.E) : iSupIndep (fun Z : Comp Xo c => partLat U Z G) := fun Z => by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ Z), partLat U j G) ≤
      (LinearMap.ker ((LinearMap.mulLeft c.F (idem Z)).comp (cuspW Xo c U G).subtype)).restrictScalars (𝓞 c.F) :=
    iSup₂_le fun j hj y hy => by
      rw [Submodule.restrictScalars_mem, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearMap.mulLeft_apply]
      exact idem_mul_eq_zero (Ne.symm hj) (coe_mem_of_mem_partLat hy)
  have h0 : idem Z * (x : Rul Xo c) = 0 := by
    have := hle hx'
    rwa [Submodule.restrictScalars_mem, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.mulLeft_apply] at this
  apply Subtype.ext
  calc (x : Rul Xo c) = idem Z * x := (idem_mul_of_mem_cuspOn (coe_mem_of_mem_partLat hx)).symm
    _ = 0 := h0

theorem iSup_partLat (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (G : WTZ D.host.E) :
    ⨆ Z : Comp Xo c, partLat U Z G = latW U G := by
  refine le_antisymm (iSup_le fun Z => partLat_le U Z G) fun F hF => ?_
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  have hF' : F = ∑ Z : Comp Xo c,
      (⟨idem Z * (F : Rul Xo c), GlobalTheory.CompRestr.idem_mul_mem_cuspW hU Z F.2⟩ : cuspW Xo c U G) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact (sum_idem_mul _).symm
  rw [hF']
  refine Submodule.sum_mem _ fun Z _ => Submodule.mem_iSup_of_mem Z ?_
  exact ⟨⟨_, idem_mul_mem_cuspOn hU Z F⟩, mem_latOn_part hU F hF Z, rfl⟩

theorem splits : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r),
    (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ G : WTZ D.host.E, Splits U G :=
  fun _ _ _ _ _ _ _ _ _ _ hU G =>
    ⟨fun F => ⟨(finsum_parts _).symm, fun Z => idem_mul_mem_cuspOn hU Z F,
        ⟨fun hF Z => mem_latOn_part hU F hF Z, mem_latW_of_parts hU F⟩⟩,
      ⟨cuspOn_indep G, iSup_cuspOn hU G⟩, partLat_indep G, iSup_partLat hU G⟩

end GlobalTheory.CuspSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseOpenEqTopOfSmoothOfRelativeDimensionZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory

theorem dense_open_eq_top_of_smoothOfRelativeDimension_zero : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k), SmoothOfRelativeDimension 0 p → ∀ (U : Y.Opens), Dense (U : Set Y) → U = ⊤ := by
  intro k _ Y p hp U hU
  have he : Etale p := (Etale.iff_smoothOfRelativeDimension_zero p).2 hp
  have hq : LocallyQuasiFinite p := by
    refine ⟨fun {V} hV {W} hW e ↦ ?_⟩
    have h := p.etale_appLE hV hW e
    letI := (p.appLE V W e).hom.toAlgebra
    have : Algebra.Etale Γ(Sp k, V) Γ(Y, W) := h
    exact (inferInstance : Algebra.QuasiFinite Γ(Sp k, V) Γ(Y, W))
  have hsub : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hopen : ∀ y : Y, IsOpen ({y} : Set Y) := by
    intro y
    have hd : _root_.IsDiscrete (p ⁻¹' {p y}) := p.isDiscrete_preimage_singleton (p y)
    have huniv : p ⁻¹' {p y} = Set.univ := by
      ext z; simp [Subsingleton.elim (p z) (p y)]
    rw [huniv] at hd
    have : DiscreteTopology Y := by
      have h2 := hd.to_subtype
      exact (Homeomorph.Set.univ Y).symm.isEmbedding.discreteTopology
    exact isOpen_discrete _
  refine eq_top_iff.2 fun y _ ↦ ?_
  obtain ⟨z, hz1, hz2⟩ := hU.inter_open_nonempty {y} (hopen y) ⟨y, rfl⟩
  rw [Set.mem_singleton_iff] at hz1
  subst hz1
  exact hz2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLargeInertPrime
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum.InertOsc

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig IsSmall IsSpread sumSmallSpread not_isBig_iff)

theorem card_filter_inPsi {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    [DecidablePred (fun τ : E →+* ℂ => InPsi H τ)] :
    (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = Module.finrank ℚ E / 2 := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact GlobalTheory.LamF.card_psiSet H

theorem nuBetween_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ} [Fact p.Prime] {la : PointsOfFlagModel.abelian₂ p c}
    {cx : Lt1 Dw → ℕ} {A B B' : ℝ} (h : NuBetween Xo la cx A B) (hB : B ≤ B') : NuBetween Xo la cx A B' :=
  fun T io e ho y => ⟨(h T io e ho y).1, fun ha => ((h T io e ho y).2 ha).trans (EReal.coe_le_coe_iff.2 hB)⟩

theorem big_arith {i q k m p : ℕ} (hi : i + 1 ≤ k + m) (hk : k ≤ m * p) (hq : q ≤ m) (hp : 2 ≤ p) :
    2 * i + 2 * q * p ≤ 5 * m * p := by
  have h1 : 2 * m ≤ m * p := by nlinarith
  have h2 : q * p ≤ m * p := Nat.mul_le_mul_right _ hq
  nlinarith

theorem big_bound {i q k m p c : ℕ} (hi : i + 1 ≤ k + m) (hk : k ≤ m * p) (hq : q ≤ m) (hp : 2 ≤ p) :
    boundInert p q i c ≤ 5 * (m : ℝ) * c / ((p : ℝ) - 1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hn : ((2 * i + 2 * q * p : ℕ) : ℝ) ≤ ((5 * m * p : ℕ) : ℝ) := by exact_mod_cast big_arith hi hk hq hp
  push_cast at hn
  unfold boundInert
  rw [div_add_div _ _ (by positivity) hp1.ne', div_le_div_iff₀ (by positivity) hp1]
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have : (2 * (i : ℝ) * c * ((p : ℝ) - 1) + (p * ((p : ℝ) - 1)) * (2 * q * c)) * ((p : ℝ) - 1)
      = ((2 * i + 2 * q * p) * c) * ((p : ℝ) - 1) ^ 2 := by ring
  rw [this]
  have : 5 * (m : ℝ) * c * (p * ((p : ℝ) - 1) * ((p : ℝ) - 1)) = ((5 * m * p) * c) * ((p : ℝ) - 1) ^ 2 := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hc) (sq_nonneg _)

theorem rk_add_one_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (f : Lt1 Dw) : rk f + 1 ≤ Dw.p + Dw.q + 1 := by
  have h := rk_le f
  unfold Datum.mult at h
  split_ifs at h <;> omega

theorem oscLe_inert_large : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], ¬ (p : ℤ) ∣ discr E → InertInK H p → k ≤ m * p → OscLe Xo c p cx ((6 * F * m * Mb + Sm) / ((p : ℝ) - 1) + 1) := by
  classical
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE p _ hdisc hin hkp
  obtain ⟨hS1, hSq, hmk, hm1, hk2, hF⟩ := hS
  obtain ⟨hMb, hbig, hsm, -⟩ := hE
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  intro la
  set w : Lt1 Dw → ℝ := fun f => if IsBig k f then 5 * (m : ℝ) * cx f / ((p : ℝ) - 1)
    else (rk f : ℝ) * cx f / ((p : ℝ) - 1) with hw
  have key : ∀ f, ∃ ab : ℝ × ℝ, FacBetween Xo la f (cx f) ab.1 ab.2 ∧ ab.2 - ab.1 ≤ w f := by
    intro f
    by_cases hb : IsBig k f
    · obtain ⟨A, B, hAB, hBA⟩ := GlobalTheory.T.factorDepth_bounds_inert_prime E H Dw l Xo c p la hdisc hin f (cx f) hb.1
      refine ⟨(A, B), hAB, ?_⟩
      simp only [hw, if_pos hb]
      exact hBA.trans (big_bound (by have := rk_add_one_le f; omega) hkp hSq hp2)
    · refine ⟨(0, boundAll p (rk f) (cx f)), (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1, ?_⟩
      simp only [hw, if_neg hb, boundAll, sub_zero, le_refl]
  choose g hg using key
  obtain ⟨n, hn⟩ := ((GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 (fun f => (g f).1) (fun f => (g f).2) fun f => (hg f).1).2
  refine ⟨n, nuBetween_mono hn ?_⟩
  have hsum : ∑ f, ((g f).2 - (g f).1) ≤ ∑ f, w f := Finset.sum_le_sum fun f _ => (hg f).2
  suffices hw2 : ∑ f, w f ≤ (6 * F * m * Mb + Sm) / ((p : ℝ) - 1) by linarith

  have hcard : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = F := by
    rw [card_filter_inPsi H, hF]; omega
  have hB : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f), (cx f : ℝ) ≤ F * Mb := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun f : Lt1 Dw => IsBig k f))
      (t := Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)) (g := fun f : Lt1 Dw => f.1)
      (fun f hf => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢; exact hf.1)]
    calc _ ≤ ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ), Mb := by
          refine Finset.sum_le_sum fun τ _ => ?_
          have h := hbig τ
          push_cast at h
          rw [Finset.filter_filter]
          convert h using 2
      _ = F * Mb := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hSS : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => ¬ IsBig k f), (rk f : ℝ) * cx f = (sumSmallSpread k cx : ℝ) := by
    unfold sumSmallSpread
    push_cast
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_isBig_iff]
  simp only [hw]
  rw [Finset.sum_ite, ← Finset.sum_div, ← Finset.sum_div, ← add_div, ← Finset.mul_sum, hSS]
  refine div_le_div_of_nonneg_right ?_ hp1.le
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have h5 : 5 * (m : ℝ) * ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f), (cx f : ℝ) ≤ 5 * m * (F * Mb) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have h6 : 5 * (m : ℝ) * (F * Mb) ≤ 6 * F * m * Mb := by
    have : (0 : ℝ) ≤ F * m * Mb := by positivity
    nlinarith
  linarith

end GlobalTheory.RefSum.InertOsc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledTargetWeilTransportRestrictFirstFactorStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.doubled_target_weil_transport_restrict_first_factor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
      ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E) (hA : JA = JTᵀ),
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
        GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
          Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
          Module.End ℂ ((κ ⊕ κ → AF F) → ℂ),
        GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) ωd omp →
      ∀ (g : UG (cA σ) (incM F JA)) (gd : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)),
        gd.1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1.1 0 0 1) →
        ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omp (gd, 1) (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂ := by
  first | exact @GlobalTheory.DblTargetRestrict.restrict_boxFun | exact GlobalTheory.DblTargetRestrict.restrict_boxFun | (intros; apply GlobalTheory.DblTargetRestrict.restrict_boxFun <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCurveMapToAbelianStatement
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_twist_function_decomposition : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → AtTw fun Fm x hx i p w j => ∀ τ : ℂ ≃+* ℂ,
  (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
  ∀ Φ Φ' : GA (Fm.D x i) (Wc (Fm.D x i) j) → ℂ, GlobalTheory.ConjTwist.ConjFun (p.O j) (p.κ j) τ 1 Φ Φ' →
    ∃ (n : ℕ) (b : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
      Φ = ∑ k, b k • evW p.nexp p.v₀ j (g k).val ∧ ∑ k, τ (b k) • evW p.nexp p.v₀ j (g k).val = Φ' := by
  first | exact @GlobalTheory.ConjExpandRational.conj_expansion_rational | exact GlobalTheory.ConjExpandRational.conj_expansion_rational | (intros; apply GlobalTheory.ConjExpandRational.conj_expansion_rational <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfOrthonormalConjBlockUpperTriangularStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_orthonormal_conj_block_upper_triangular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ γ ∈ X.Γ, (∀ τ, (KU.gm X x0 γ τ).toBlocks₁₂ = 0) → γ = 1 := by
  first | exact @GlobalTheory.ScalarPoin.BlockFree.eq_one_of_gm_toBlocks₁₂ | exact GlobalTheory.ScalarPoin.BlockFree.eq_one_of_gm_toBlocks₁₂ | (intros; apply GlobalTheory.ScalarPoin.BlockFree.eq_one_of_gm_toBlocks₁₂ <;> assumption)
end

