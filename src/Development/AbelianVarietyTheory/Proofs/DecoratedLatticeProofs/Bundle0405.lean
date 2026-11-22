import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0383
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0384
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0374
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0365
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0395
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsPrincipalIdealRingSemiLoc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0386
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0387
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0376
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0388

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteQuotientAnnihilatorStandardLatticeConjHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.AnnConjHalf

variable {D : D7}

theorem symplO_add_right' (S T : HSp D) (x u v : WO S T) :
    symplO S T x (u + v) = symplO S T x u + symplO S T x v := by
  simp only [symplO, hO, Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_neg_right' (S T : HSp D) (x u : WO S T) :
    symplO S T x (-u) = -symplO S T x u := by
  simp only [symplO, hO, Matrix.neg_apply, map_neg, mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem symplO_zero_right' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp only [symplO, hO, Matrix.zero_apply, map_zero, mul_zero, zero_mul, Finset.sum_const_zero]

def annHalf (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (E₂ : AE D) : AddSubgroup (WO S T) where
  carrier := {u | IsHalf (cA D E₂) u ∧ ∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x u) = 1}
  zero_mem' := ⟨fun i j => by simp, fun x _ _ => by rw [symplO_zero_right', AddChar.map_zero_eq_one]⟩
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    refine ⟨fun i j => by rw [Matrix.add_apply, mul_add, hu i j, hv i j], fun x hx hxh => ?_⟩
    rw [symplO_add_right', AddChar.map_add_eq_mul, hu' x hx hxh, hv' x hx hxh, mul_one]
  neg_mem' := by
    rintro u ⟨hu, hu'⟩
    refine ⟨fun i j => by rw [Matrix.neg_apply, mul_neg, hu i j], fun x hx hxh => ?_⟩
    rw [symplO_neg_right', AddChar.map_neg_eq_inv, hu' x hx hxh, inv_one]

def stdHalf (S T : HSp D) (f : AE D) : AddSubgroup (WO S T) where
  carrier := {u | u ∈ stdHom S T ∧ IsHalf f u}
  zero_mem' := ⟨zero_mem _, fun i j => by simp⟩
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    exact ⟨add_mem hu hv, fun i j => by rw [Matrix.add_apply, mul_add, hu' i j, hv' i j]⟩
  neg_mem' := by
    rintro u ⟨hu, hu'⟩
    exact ⟨neg_mem hu, fun i j => by rw [Matrix.neg_apply, mul_neg, hu' i j]⟩

theorem half_nsmul {m n : ℕ} {f : AE D} {u : Mx D m n} (hu : IsHalf f u) (N : ℕ) : IsHalf f (N • u) :=
  fun i j => by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu i j]

theorem nsmul_eq_zero_WO (S T : HSp D) {N : ℕ} (hN : 0 < N) (v : WO S T) (h : N • v = 0) : v = 0 := by
  ext i j
  have hij : N • v i j = 0 := by
    have := congrFun (congrFun h i) j
    rwa [Matrix.smul_apply] at this
  have hF : (N : D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hu : IsUnit ((N : ℕ) : AE D) := by
    have := (isUnit_iff_ne_zero.2 hF).map (algebraMap D.host.F (AE D))
    rwa [map_natCast] at this
  rw [nsmul_eq_mul] at hij
  rw [Matrix.zero_apply]
  exact (hu.mul_right_eq_zero).1 hij

theorem ann_conj_half_finite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u : WO S T, IsHalf (cA D E₂) u → (∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x u) = 1) → ∃ r ∈ R, ∃ v : WO S T, IsHalf (cA D E₂) v ∧ (∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x v) = 1) ∧ u = r + k • v := by
  intro D ψ hψ S T Q E₂ hE k hk
  obtain ⟨N, hN, hup⟩ := GlobalTheory.T.exists_nsmul_annihilator_half_mem_standardHom D ψ hψ S T Q E₂ hE
  obtain ⟨M, hM, hlow⟩ := GlobalTheory.StdHomOrth.exists_nsmul_orth D ψ hψ S T
  obtain ⟨Q', hQ'⟩ := GlobalTheory.T.exists_isIdemSum_conj_of_isIdemSum D Q E₂ hE
  have hAL : ∀ a ∈ annHalf ψ S T E₂, N • a ∈ stdHalf S T (cA D E₂) := fun a ha =>
    ⟨hup a ha.1 ha.2, half_nsmul ha.1 N⟩
  have hLA : ∀ l ∈ stdHalf S T (cA D E₂), M • l ∈ annHalf ψ S T E₂ := fun l hl =>
    ⟨half_nsmul hl.2 M, fun x hx _ => hlow x hx l hl.1⟩
  have hfin : ∀ j : ℕ, 0 < j → ∃ R : Finset (WO S T), ∀ u ∈ stdHalf S T (cA D E₂), ∃ r ∈ R,
      ∃ v ∈ stdHalf S T (cA D E₂), u = r + j • v := by
    intro j hj
    obtain ⟨R, hR⟩ := GlobalTheory.HalfStdFin.exists_reps_half_stdHom D S T Q' (cA D E₂) hQ' j hj
    refine ⟨R, fun u hu => ?_⟩
    obtain ⟨r, hr, v, hv, hvh, huv⟩ := hR u hu.1 hu.2
    exact ⟨r, hr, v, ⟨hv, hvh⟩, huv⟩
  obtain ⟨R, hR⟩ := GlobalTheory.addSubgroup_finite_quot_of_commensurable (WO S T) (annHalf ψ S T E₂) (stdHalf S T (cA D E₂))
    N M hN hM (nsmul_eq_zero_WO S T hN) hAL hLA hfin k hk
  refine ⟨R, fun u hu hann => ?_⟩
  obtain ⟨r, hr, v, hv, huv⟩ := hR u ⟨hu, hann⟩
  exact ⟨r, hr, v, hv.1, hv.2, huv⟩

end GlobalTheory.AnnConjHalf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.IdVGen

open GlobalTheory.SemiLocalFrame

theorem exists_gen_semiLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {𝔟 : FractionalIdeal (𝓞 E)⁰ E} (h𝔟 : 𝔟 ≠ 0) :
    ∃ b : E, b ≠ 0 ∧ ∀ z, (∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • z ∈ (𝔟 : Submodule (𝓞 E) E)) ↔
      b⁻¹ * z ∈ semiLoc E v := by
  have hfg : (Submodule.span (semiLoc E v) ((𝔟 : Submodule (𝓞 E) E) : Set E)).FG := by
    obtain ⟨s, hs⟩ := FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔟
    exact ⟨s, by rw [← hs, Submodule.span_span_of_tower]⟩
  obtain ⟨b, hb⟩ := (FractionalIdeal.isPrincipal
    (⟨_, FractionalIdeal.isFractional_of_fg hfg⟩ : FractionalIdeal (semiLoc E v)⁰ E)).principal
  have hb' : ∀ z, (∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • z ∈ (𝔟 : Submodule (𝓞 E) E)) ↔
      ∃ a : semiLoc E v, a • b = z := fun z => by
    rw [← Submodule.mem_span_singleton, ← hb]
    exact (mem_span_semiLoc_iff v (𝔟 : Submodule (𝓞 E) E) z).symm
  have hb0 : b ≠ 0 := by
    rintro rfl
    refine h𝔟 (FractionalIdeal.eq_zero_iff.2 fun z hz => ?_)
    obtain ⟨a, ha⟩ := (hb' z).1 ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, by simpa using hz⟩
    rw [← ha, smul_zero]
  refine ⟨b, hb0, fun z => (hb' z).trans ⟨?_, fun h => ⟨⟨_, h⟩, ?_⟩⟩⟩
  · rintro ⟨a, rfl⟩
    have : b⁻¹ * (a • b) = a := by
      change b⁻¹ * ((a : E) * b) = a
      field_simp
    rw [this]; exact a.2
  · change b⁻¹ * z * b = z
    field_simp

theorem exists_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) {𝔟 : FractionalIdeal (𝓞 E)⁰ E} (h𝔟 : 𝔟 ≠ 0) :
    ∃ b : E, b ≠ 0 ∧ (∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) * b ∈ 𝔟) ∧
      ∀ c ∈ 𝔟, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ ∃ o : 𝓞 E,
        algebraMap F E (t : F) * (b⁻¹ * c) = algebraMap (𝓞 E) E o := by
  obtain ⟨b, hb0, hb⟩ := exists_gen_semiLoc v h𝔟
  have hone : (1 : 𝓞 F) ∉ v.asIdeal := (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top
  refine ⟨b, hb0, ?_, fun c hc => ?_⟩
  · obtain ⟨t, ht, h⟩ := (hb b).2 (by rw [inv_mul_cancel₀ hb0]; exact one_mem _)
    exact ⟨t, ht, by rw [← smul_eq]; exact h⟩
  · have h1 := (hb c).1 ⟨1, hone, by rw [map_one, one_smul]; exact hc⟩
    obtain ⟨t, ht, h⟩ := exists_of_mem_semiLoc v h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 h
    exact ⟨t, ht, o, by rw [← smul_eq, ho]⟩

variable {D : D7}

theorem inv_mem_integers {v : Pl D} {t : 𝓞 D.host.F} (hv : t ∉ v.asIdeal) :
    algebraMap D.host.F (Fv D.host.F v) (t : D.host.F)⁻¹ ∈ v.adicCompletionIntegers D.host.F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation D.host.F (t : D.host.F) = 1 := by
    simpa using (v.valuation_eq_one_iff_notMem (K := D.host.F)).2 hv
  have h2 := v.valuedAdicCompletion_eq_valuation' ((t : D.host.F)⁻¹)
  have h3 : v.valuation D.host.F (t : D.host.F)⁻¹ = 1 := by rw [map_inv₀, h1, inv_one]
  exact (h2.trans h3).le

theorem smul_inv_mem {v : Pl D} {t : 𝓞 D.host.F} (hv : t ∉ v.asIdeal) {α : Af D.host.F}
    (hα : α ∈ intAf D.host.F) (h0 : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    (t : D.host.F)⁻¹ • α ∈ intAf D.host.F ∧ ∀ w, w ≠ v → evalV D.host.F w ((t : D.host.F)⁻¹ • α) = 0 := by
  refine ⟨fun w => ?_, fun w hw => by rw [map_smul, h0 w hw, smul_zero]⟩
  by_cases hw : w = v
  · subst hw
    rw [map_smul, Algebra.smul_def]
    exact mul_mem (inv_mem_integers hv) (hα w)
  · rw [map_smul, h0 w hw, smul_zero]
    exact zero_mem _

theorem pairA_smul {F : Type} [Field F] [NumberField F] (c : F) (α : Af F) :
    pairA F 0 (c • α) = c • pairA F 0 α := by
  have : c • pairA F 0 α = ((c • (0 : Ainf F), c • α) : Ainf F × Af F) := rfl
  rw [this, smul_zero]; rfl

theorem tmul_eq_of_ne {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (c : F) (hc : c ≠ 0)
    (α : Af F) (z : E) : pairA F 0 α ⊗ₜ[F] z = pairA F 0 (c⁻¹ • α) ⊗ₜ[F] (algebraMap F E c * z) := by
  rw [pairA_smul, TensorProduct.smul_tmul, ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem tmul_eq {v : Pl D} {t : 𝓞 D.host.F} (ht : t ∉ v.asIdeal) (α : Af D.host.F) (z : D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] z =
      pairA D.host.F 0 ((t : D.host.F)⁻¹ • α) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E (t : D.host.F) * z) := by
  have ht0 : t ≠ 0 := fun h => ht (h ▸ v.asIdeal.zero_mem)
  have hF : (t : D.host.F) ≠ 0 := by exact_mod_cast ht0
  exact tmul_eq_of_ne _ hF α z

theorem gen_mem_idAt {v : Pl D} {α : Af D.host.F} (h0 : ∀ w, w ≠ v → evalV D.host.F w α = 0) (z : D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] z ∈ idAt D (· = v) := by
  rw [idAt, Ideal.mem_inf, Ideal.mem_iInf]
  refine ⟨?_, fun w => ?_⟩
  · rw [RingHom.mem_ker]
    show (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] z = 0
    exact TensorProduct.zero_tmul _ _
  · rw [RingHom.mem_ker]
    show evalV D.host.F w.1 α ⊗ₜ[D.host.F] z = 0
    rw [h0 w.1 w.2, TensorProduct.zero_tmul]

theorem gen_mem_intAt {v : Pl D} {α : Af D.host.F} (hα : α ∈ intAf D.host.F)
    (h0 : ∀ w, w ≠ v → evalV D.host.F w α = 0) (o : 𝓞 D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] algebraMap (𝓞 D.host.E) D.host.E o ∈ intAt D (· = v) :=
  ⟨gen_mem_idAt h0 _, AddSubgroup.subset_closure ⟨α, hα, o, rfl⟩⟩

theorem intAt_zero' (v : Pl D) : (0 : AE D) ∈ intAt D (· = v) :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem intAt_add' {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a + b ∈ intAt D (· = v) :=
  ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (finPart D) a b]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg' {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) : -a ∈ intAt D (· = v) :=
  ⟨neg_mem ha.1, by rw [RingHom.map_neg (finPart D) a]; exact neg_mem ha.2⟩

theorem incA_mul_tmul (y : AF D.host.F) (e z : D.host.E) :
    incA D e * (y ⊗ₜ[D.host.F] z) = y ⊗ₜ[D.host.F] (e * z) := by
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) * (y ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem idV_gen : ∀ (D : D7) (v : Pl D) (𝔞 : FI D), 𝔞 ≠ 0 → ∃ x : D.host.E, x ≠ 0 ∧
    ∀ s, s ∈ idV 𝔞 v ↔ incA D x⁻¹ * s ∈ intAt D (· = v) ∧ s ∈ idAt D (· = v) := by
  intro D v 𝔞 h𝔞
  obtain ⟨x, hx0, ⟨t₀, ht₀, hx𝔞⟩, hc⟩ := exists_gen v h𝔞
  refine ⟨x, hx0, fun s => ⟨fun hs => ?_, fun ⟨h1, _⟩ => ?_⟩⟩
  · unfold idV at hs
    induction hs using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, h0, c, hc', rfl⟩ := hy
      obtain ⟨t, ht, o, ho⟩ := hc c hc'
      obtain ⟨h1, h2⟩ := smul_inv_mem ht hα h0
      refine ⟨?_, gen_mem_idAt h0 c⟩
      rw [incA_mul_tmul, tmul_eq ht α (x⁻¹ * c), ho]
      exact gen_mem_intAt h1 h2 o
    | zero => exact ⟨by rw [mul_zero]; exact intAt_zero' v, zero_mem _⟩
    | add a b _ _ ha hb => exact ⟨by rw [mul_add]; exact intAt_add' ha.1 hb.1, add_mem ha.2 hb.2⟩
    | neg a _ ha => exact ⟨by rw [mul_neg]; exact intAt_neg' ha.1, neg_mem ha.2⟩
  · have h3 : incA D x⁻¹ * s ∈ idV (1 : FI D) v := (GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).2 h1
    have key : ∀ y ∈ idV (1 : FI D) v, incA D x * y ∈ idV 𝔞 v := by
      intro y hy
      unfold idV at hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, h0, c, hc', rfl⟩ := hy
        obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hc'
        obtain ⟨h1', h2'⟩ := smul_inv_mem ht₀ hα h0
        apply AddSubgroup.subset_closure
        refine ⟨_, h1', h2', algebraMap D.host.F D.host.E (t₀ : D.host.F) * (x * algebraMap (𝓞 D.host.E) D.host.E o),
          ?_, ?_⟩
        · have := (𝔞 : Submodule (𝓞 D.host.E) D.host.E).smul_mem o hx𝔞
          rw [Algebra.smul_def] at this
          have e : algebraMap D.host.F D.host.E (t₀ : D.host.F) * (x * algebraMap (𝓞 D.host.E) D.host.E o) =
              algebraMap (𝓞 D.host.E) D.host.E o * (algebraMap D.host.F D.host.E (t₀ : D.host.F) * x) := by ring
          rw [e]; exact this
        · rw [incA_mul_tmul, tmul_eq ht₀ α]
      | zero => rw [mul_zero]; exact zero_mem _
      | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
      | neg a _ ha => rw [mul_neg]; exact neg_mem ha
    have := key _ h3
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ hx0, map_one, one_mul] at this

end GlobalTheory.IdVGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FunctionalValuesIntegralVectorsOfIntegerVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

noncomputable section

namespace GlobalTheory.FinPl.SplitPt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_max_iff_val_lt_one (x : 𝒪[k]) : x ∈ IsLocalRing.maximalIdeal 𝒪[k] ↔ valuation k (x : k) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem pr_incA_int_mem (q : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (x : 𝓞 D.host.E) : q.pr (incA D (x : D.host.E)) ∈ 𝒪[k] :=
  (q.pr_mem_iff _).2 (mul_mem (GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he).1
    (Formalism.L2.DIV.oToS D.host.F D.host.E x).2)

theorem exists_int_approx (q : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    {u : k} (hu : u ∈ 𝒪[k]) : ∃ z : 𝓞 D.host.E, valuation k (u - q.pr (incA D (z : D.host.E))) < 1 := by
  have h1 : toEAf D (q.e * q.sec u) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [map_mul]
    exact (q.pr_mem_iff (q.sec u)).1 (by rw [q.pr_sec]; exact hu)
  have h2 : q.pr (q.e * q.sec u) = u := by rw [← q.sec_pr, q.pr_sec, q.pr_sec]
  obtain ⟨a, ha0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx PP.ne_bot
    (⟨_, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E)
  have ha : (⟨_, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E a ∈
    Formalism.L2.DIV.idS D.host.F PP.asIdeal := ha0
  have h3 := q.val_lt_of_mem_idS he ha
  have e2 : (((⟨_, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E a :
      Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      toEAf D (q.e * q.sec u) - toEAf D (incA D (a : D.host.E)) := rfl
  rw [e2, RingHom.map_sub, prF_toEAf, prF_toEAf, h2] at h3
  exact ⟨a, h3⟩

theorem hasVal_of_int_vectors : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∀ (m : ℕ) (b b' : Matrix (Fin m) (Fin m) k), b * b' = 1 → b' * b = 1 →
    ∀ P : Pair k (Fin m), (∀ x, x ∈ P.lat ↔ ∀ r, (b *ᵥ x) r ∈ 𝒪[k]) → ∀ c₀ : 𝓞 D.host.E,
    (∀ z : Fin m → D.host.E, (∀ r, IsIntegral ℤ (z r)) → ∀ r : Fin m, r.1 + 1 = m →
      ∃ s : 𝒪[k], (s : k) = p.pr (incA D ((c₀ : D.host.E) * z r)) ∧
        P.HasVal (b' *ᵥ fun r' => p.pr (incA D (z r'))) (IsLocalRing.residue 𝒪[k] s)) →
    ∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) → ∀ r0 : Fin m, r0.1 + 1 = m →
      ∃ s : 𝒪[k], (s : k) = p.pr (incA D (c₀ : D.host.E)) * u r0 ∧ P.HasVal (b' *ᵥ u) (IsLocalRing.residue 𝒪[k] s) := by
  intro D k _ _ _ _ p PP he m b b' hb _ P hlat c₀ hval u hu r0 hr0
  classical
  choose z hz using fun r => p.exists_int_approx he (hu r)
  obtain ⟨s, hs, hv⟩ := hval (fun r => (z r : D.host.E)) (fun r => (z r).isIntegral_coe) r0 hr0
  have hw : ∀ r, p.pr (incA D (z r : D.host.E)) ∈ 𝒪[k] := fun r => p.pr_incA_int_mem he (z r)
  let d : Fin m → 𝒪[k] := fun r => ⟨u r - p.pr (incA D (z r : D.host.E)), sub_mem (hu r) (hw r)⟩
  have hd : ∀ r, d r ∈ maximalIdeal 𝒪[k] := fun r => (mem_max_iff_val_lt_one (d r)).2 (hz r)
  have hcol : ∀ r, b' *ᵥ (Pi.single r 1 : Fin m → k) ∈ P.lat := fun r => (hlat _).2 fun r' => by
    rw [Matrix.mulVec_mulVec, hb, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have hker : ∑ r, d r • (b' *ᵥ (Pi.single r 1 : Fin m → k)) ∈ P.ker :=
    Submodule.sum_mem _ fun r _ => Pair.smul_mem_ker (hd r) (hcol r)
  have hsum : b' *ᵥ u = (b' *ᵥ fun r' => p.pr (incA D (z r' : D.host.E))) +
      ∑ r, d r • (b' *ᵥ (Pi.single r 1 : Fin m → k)) := by
    have : ∀ r, d r • (b' *ᵥ (Pi.single r 1 : Fin m → k)) = b' *ᵥ (Pi.single r (d r : k) : Fin m → k) := fun r => by
      change (d r : k) • (b' *ᵥ (Pi.single r 1 : Fin m → k)) = _
      rw [← Matrix.mulVec_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl fun r _ => this r, ← Matrix.mulVec_sum, ← Matrix.mulVec_add, Finset.univ_sum_single]
    congr 1
    funext r
    simp [d]
  let c : 𝒪[k] := ⟨_, p.pr_incA_int_mem he c₀⟩
  refine ⟨s + c * d r0, ?_, ?_⟩
  · change (s : k) + p.pr (incA D (c₀ : D.host.E)) * (u r0 - p.pr (incA D (z r0 : D.host.E))) = _
    rw [hs, map_mul, map_mul]
    ring
  · rw [hsum, map_add, (IsLocalRing.residue_eq_zero_iff _).2 (Ideal.mul_mem_left _ c (hd r0))]
    exact hv.add (Pair.mem_ker.1 hker)

end GlobalTheory.FinPl.SplitPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasResOfValSubLt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseFn

open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2.DetSpec

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable [StarRing E] {n : ℕ}

variable {hc : Formalism.BasicNotions.CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem fn_eq {p : DecoF E n ST SG Q} {k : GL (Fin n) (AfE F E)} (h : IsPtOf hc k p) (hN : p.deco.1.N = Formalism.L2.Col.stdLat E n) (P : ST)
    (r : Fin n) (hr : r.1 + 1 = n) (c : 𝓞 E)
    (hrow : ∀ i, HasRes P.1 (adAt F P.1 ((k⁻¹ : GL (Fin n) (AfE F E)).1 r i)) (if i = r then Ideal.Quotient.mk P.1.asIdeal c else 0))
    (x : Fin n → 𝓞 E) : p.deco.1.f P (fun i => (x i : E)) = Ideal.Quotient.mk P.1.asIdeal (c * x r) := by
  refine HasRes.unique (h.f P _ (hN ▸ (Formalism.L2.Col.mem_stdLat _).2 fun i => ⟨x i, rfl⟩) r hr) ?_
  choose ρ hρ hv using hrow
  refine ⟨∑ i, ρ i * x i, ?_, ?_⟩
  · simp only [map_sum, map_mul, hρ, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · simp only [Col2.pullV, Matrix.mulVec, dotProduct, map_sum, map_mul, adAt_inclE]
    rw [← Finset.sum_sub_distrib]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
    show Valued.v (_ * algebraMap E (P.1.adicCompletion E) (algebraMap (𝓞 E) E (x i)) - _) < 1
    rw [← _root_.sub_mul, map_mul, valued_algebraMap]
    exact (mul_le_of_le_one_right' (P.1.valuation_le_one (x i))).trans_lt (hv i)

end Loc

end GlobalTheory.BaseFn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeInnerProductFormulaOfDoublingEulerStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeInnerProductFormula_of_doublingEuler : ∀ D : D7, GlobalForm D → EulerRight D → HeckeForm D := by
  first | exact @GlobalTheory.Core.Rk.IP.heckeForm_of_global_euler | exact GlobalTheory.Core.Rk.IP.heckeForm_of_global_euler | (intros; apply GlobalTheory.Core.Rk.IP.heckeForm_of_global_euler <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralEntriesOfCarriesStandardLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KJStdInt

theorem carries_std_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)), Formalism.L2.Herm.Carries k (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n) → (∀ i j, k.1 i j ∈ Formalism.L2.Herm.intAf F E) ∧ ∀ i j, (k⁻¹).1 i j ∈ Formalism.L2.Herm.intAf F E := by
  intro F E _ _ _ _ _ n k hk
  letI : StarRing E := starRingOfComm
  have hm : ∀ z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F,
      z ∈ Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E n) ↔ ∀ i, z i ∈ Formalism.L2.Herm.intAf F E :=
    fun z => Formalism.L2.Col.mem_latS_std z
  have hs : ∀ j : Fin n, (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E n) := by
    intro j
    refine (hm _).2 fun i => ?_
    by_cases h : i = j
    · subst h
      rw [Pi.single_eq_same]
      exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne h]
      exact Subring.zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have h1 : (k⁻¹).1 *ᵥ (k.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) ∈
        Formalism.L2.Herm.hatL (F := F) (Formalism.L2.Col.stdLat E n) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact hs j
    have h2 := (hm _).1 ((hk _).2 h1) i
    rwa [Matrix.mulVec_single_one] at h2
  · have h2 := (hm _).1 ((hk _).1 (hs j)) i
    rwa [Matrix.mulVec_single_one] at h2

end GlobalTheory.KJStdInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralMatrixSplitPlaceMemStdHomLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_matrix_split_place_mem_stdHomLattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (a₀ : D.host.E), a₀ ∈ (D.host.AA : Set D.host.E) → q.pr (incA D a₀) ≠ 0 → ∀ (FS : Frame k S.rank (Fin S.rank)) (FT : Frame k T.rank (Fin T.rank)), FT.β = 1 → FT.γ = 1 → FS.γ = q.pr (incA D a₀) • (HSpace.gram S).map (fun a => q.pr (incA D a)) → ∀ t : Matrix (Fin T.rank) (Fin S.rank) k, (∀ r s, t r s ∈ 𝒪[k]) → (Place.ofSplitPt q).up FS FT t ∈ stdHom S T := by
  first | exact @GlobalTheory.SplitUpStd.int_up_mem_stdHom | exact GlobalTheory.SplitUpStd.int_up_mem_stdHom | (intros; apply GlobalTheory.SplitUpStd.int_up_mem_stdHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentCompletionIffCharacterDualStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseDifferentCompletion_iff_characterDual : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (v : Pl D), ∀ s ∈ idAt D (· = v), s ∈ idV (dI D) v ↔ ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1 := by
  first | exact @GlobalTheory.SeeSaw.DiffDual.idV_dI_iff | exact GlobalTheory.SeeSaw.DiffDual.idV_dI_iff | (intros; apply GlobalTheory.SeeSaw.DiffDual.idV_dI_iff <;> assumption)
end

