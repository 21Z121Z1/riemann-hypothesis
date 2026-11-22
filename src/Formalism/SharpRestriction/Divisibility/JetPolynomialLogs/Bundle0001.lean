import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Formalism.DirichletDensity.HostDensityArith
import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts

-- bundled from Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.AnnihilatorMulRelativeDifferent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.placeRankTwoOne NumberField Formalism.FrobeniusOrbits
open scoped Pointwise

namespace Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent

theorem bb_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h1 := D.host.𝔟_spec.1
  rw [h, Ideal.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem annihilator_mul_relative_different (D : D7) : D.host.AA0 * ddEK D =
    ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have h0 : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (bb_ne_bot D)
  unfold Host.AA0 ddEK
  have h1 : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) = D.host.𝔟 * (D.host.conj • D.host.𝔟) := D.host.𝔟_spec.1
  rw [h1, FractionalIdeal.coeIdeal_mul, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]

theorem idOf_coe (D : D7) (τ : D.what₂.Tau) (I : Ideal (𝓞 D.host.E)) :
    idOf D τ (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) =
      IsLocalization.coeSubmodule D.what₂.LL (I.map (RingOfIntegers.mapRingHom (embTau D τ))) := by
  unfold idOf
  rw [Ideal.map, IsLocalization.coeSubmodule_span]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨x', hx', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hx
    exact ⟨_, ⟨x', hx', rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x', hx', rfl⟩, rfl⟩
    exact ⟨algebraMap _ _ x', (FractionalIdeal.mem_coeIdeal _).mpr ⟨x', hx', rfl⟩, rfl⟩

theorem absNorm_smul {K : Type} [Field K] [NumberField K] (σ : K ≃ₐ[ℚ] K) (I : Ideal (𝓞 K)) :
    Ideal.absNorm (σ • I) = Ideal.absNorm I := by
  have e : (𝓞 K ⧸ I) ≃+* (𝓞 K ⧸ (σ • I)) :=
    Ideal.quotientEquiv I (σ • I) (MulSemiringAction.toRingEquiv (K ≃ₐ[ℚ] K) (𝓞 K) σ) rfl
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr e.toEquiv).symm

theorem log_absNorm_map_gen {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (f : K →+* L)
    (I : Ideal (𝓞 K)) :
    Real.log (Ideal.absNorm (I.map (RingOfIntegers.mapRingHom f))) / (Module.finrank ℚ L : ℝ) =
      Real.log (Ideal.absNorm I) / (Module.finrank ℚ K : ℝ) := by
  let _ : Algebra K L := f.toAlgebra
  have h : Ideal.absNorm (I.map (algebraMap (𝓞 K) (𝓞 L))) = Ideal.absNorm I ^ Module.finrank (𝓞 K) (𝓞 L) :=
    by rw [Ideal.absNorm_algebraMap]
  have hf : Module.finrank K L = Module.finrank (𝓞 K) (𝓞 L) := IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L
  have ht : Module.finrank ℚ K * Module.finrank K L = Module.finrank ℚ L := Module.finrank_mul_finrank ℚ K L
  have hm : (RingOfIntegers.mapRingHom f) = algebraMap (𝓞 K) (𝓞 L) := rfl
  have hK : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hL : (0 : ℝ) < (Module.finrank ℚ L : ℝ) := by exact_mod_cast Module.finrank_pos
  rw [hm, h, ← hf, ← ht]
  push_cast
  rw [Real.log_pow]
  have hKL : (0 : ℝ) < (Module.finrank K L : ℝ) := by
    rw [← ht] at hL; push_cast at hL
    exact (pos_iff_pos_of_mul_pos hL).mp hK
  field_simp

theorem log_absNorm_map (D : D7) (τ : D.what₂.Tau) (I : Ideal (𝓞 D.host.E)) :
    Real.log (Ideal.absNorm (I.map (RingOfIntegers.mapRingHom (embTau D τ)))) / (Module.finrank ℚ D.what₂.LL : ℝ) =
      Real.log (Ideal.absNorm I) / (Module.finrank ℚ D.host.E : ℝ) :=
  log_absNorm_map_gen _ I

theorem discr_K (D : D7) : discr D.host.K = -(D.host.d : ℤ) := by
  have hb : D.host.sqd ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  let x : D.host.K := ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hx : x ^ 2 = ((-(D.host.d : ℤ) : ℤ) : D.host.K) := by
    apply Subtype.ext
    simpa [x] using hb
  have htop : IntermediateField.adjoin ℚ {x} = ⊤ := by
    apply Formalism.HF.P.adjoin_top_of_lift
    rw [Set.image_singleton]
    rfl
  exact Formalism.HF.Final.quadDiscr D.host.K _ x hx htop (Formalism.HF.P.sqf_neg _ D.host.hyp.2.1)
    (by have := D.host.hyp.2.2.2.1; omega)

theorem finrank_K (D : D7) : Module.finrank ℚ D.host.K = 2 :=
  SplitK.finrank_K (L := D.host.E) (b := D.host.sqd) (d := D.host.d) D.host.hyp.2.1.pos
    (D.host.sqd_sq)

theorem log_absNorm_bbar (D : D7) :
    Real.log (Ideal.absNorm (D.host.conj • D.host.𝔟)) / (Module.finrank ℚ D.host.E : ℝ) =
      (Real.log D.host.rdE - Real.log (D.host.d : ℝ) / 2) / 2 := by
  have h1 : differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) = D.host.𝔟 * (D.host.conj • D.host.𝔟) := D.host.𝔟_spec.1
  have h2 := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow D.host.K (𝓞 D.host.K) D.host.E (𝓞 D.host.E)
  rw [h1, map_mul, absNorm_smul, discr_K] at h2
  have ht : Module.finrank ℚ D.host.K * Module.finrank D.host.K D.host.E = Module.finrank ℚ D.host.E :=
    Module.finrank_mul_finrank ℚ D.host.K D.host.E
  rw [finrank_K] at ht
  have hE : (0 : ℝ) < (Module.finrank ℚ D.host.E : ℝ) := by exact_mod_cast Module.finrank_pos
  have hN : (0 : ℝ) < (Ideal.absNorm D.host.𝔟 : ℝ) := by
    have : Ideal.absNorm D.host.𝔟 ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact bb_ne_bot D
    exact_mod_cast Nat.pos_of_ne_zero this
  have hd : (0 : ℝ) < (D.host.d : ℝ) := by exact_mod_cast D.host.hyp.2.1.pos
  have h3 : |(discr D.host.E : ℝ)| = (Ideal.absNorm D.host.𝔟 : ℝ) * (Ideal.absNorm D.host.𝔟 : ℝ) *
      (D.host.d : ℝ) ^ Module.finrank D.host.K D.host.E := by
    have : ((discr D.host.E).natAbs : ℝ) = |(discr D.host.E : ℝ)| := by
      rw [Nat.cast_natAbs]; push_cast; rfl
    rw [← this, h2]
    simp
  rw [absNorm_smul]
  unfold Host.rdE
  rw [Real.log_rpow (by rw [h3]; positivity), h3, Real.log_mul (by positivity) (by positivity),
    Real.log_mul hN.ne' hN.ne', Real.log_pow, ← ht]
  push_cast
  have hKE : (0 : ℝ) < (Module.finrank D.host.K D.host.E : ℝ) := by
    rw [← ht] at hE; push_cast at hE; linarith
  field_simp
  ring

noncomputable def JJ (D : D7) (τ : D.what₂.Tau) : Ideal (𝓞 D.what₂.LL) :=
  (D.host.conj • D.host.𝔟).map (RingOfIntegers.mapRingHom (embTau D τ))

theorem idealOf_annihilator_mul_relativeDifferent (D : D7) (τ : D.what₂.Tau) :
    idOf D τ (D.host.AA0 * ddEK D) = IsLocalization.coeSubmodule D.what₂.LL (JJ D τ) := by
  rw [annihilator_mul_relative_different, idOf_coe]; rfl

theorem JJ_ne_bot (D : D7) (τ : D.what₂.Tau) : JJ D τ ≠ ⊥ := by
  unfold JJ
  have hinj : Function.Injective (RingOfIntegers.mapRingHom (embTau D τ)) := by
    intro x y h
    apply RingOfIntegers.ext
    apply (embTau D τ).injective
    have := congrArg (fun z : 𝓞 D.what₂.LL => (z : D.what₂.LL)) h
    simpa [RingOfIntegers.mapRingHom_apply] using this
  rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
  intro h
  have h1 : Ideal.absNorm (D.host.conj • D.host.𝔟) = 0 := by rw [h]; simp
  rw [absNorm_smul, Ideal.absNorm_eq_zero_iff] at h1
  exact bb_ne_bot D h1

theorem log_absNorm_JJ (D : D7) (τ : D.what₂.Tau) :
    2 / (Module.finrank ℚ D.what₂.LL : ℝ) * Real.log (Ideal.absNorm (JJ D τ)) =
      Real.log D.host.rdE - Real.log (D.host.d : ℝ) / 2 := by
  have h := log_absNorm_map D τ (D.host.conj • D.host.𝔟)
  rw [log_absNorm_bbar] at h
  unfold JJ
  have e : 2 / (Module.finrank ℚ D.what₂.LL : ℝ) *
      Real.log (Ideal.absNorm ((D.host.conj • D.host.𝔟).map (RingOfIntegers.mapRingHom (embTau D τ)))) =
      2 * (Real.log (Ideal.absNorm ((D.host.conj • D.host.𝔟).map (RingOfIntegers.mapRingHom (embTau D τ)))) /
        (Module.finrank ℚ D.what₂.LL : ℝ)) := by ring
  rw [e, h]; ring

end Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent
end

-- bundled from Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.LogbAddOneNonneg
section
noncomputable section

namespace Formalism.MainNotions.product_zeroth_first_parts

theorem kvalGe_anti {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime] (nu : Lt → YoungDiagram)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) {B B' : ℝ} (hB : B' ≤ B) (h : KvalGe N0 N1 l nu Th B) :
    KvalGe N0 N1 l nu Th B' := by
  intro I m
  have hl : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
  exact (h I m).trans (Real.rpow_le_rpow_of_exponent_le hl (neg_le_neg hB))

theorem logb_add_one_nonneg {l : ℕ} (hl : 1 < l) {a : ℝ} (ha : (l : ℝ) ≤ a) : 0 ≤ Real.logb l a + 1 := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl
  have h2 := Real.logb_nonneg h1 (le_trans h1.le ha)
  linarith

theorem uniform_bound_mono {C C' : ℝ} (hC : C ≤ C') (h : ExportAllConjugates C) : ExportAllConjugates C' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun L hL => ⟨?_, ?_⟩, fun L hL => ?_⟩
  · intro a ha
    refine kvalGe_anti _ _ _ _ _ ?_ ((h1 L hL).1 a ha)
    have hl : 1 < L.l := (Fact.out : L.l.Prime).one_lt
    have hX : 0 ≤ (L.d : ℝ) * L.N0 * L.N1 * (Real.logb L.l a + 1) :=
      mul_nonneg (by positivity) (logb_add_one_nonneg hl ha.1)
    have hCX := mul_le_mul_of_nonneg_right hC hX
    linarith
  · intro a ha k w E hk hw hE h1' h2'
    refine kvalGe_anti _ _ _ _ _ ?_ ((h1 L hL).2 a ha k w E hk hw hE h1' h2')
    have hl : 1 < L.l := (Fact.out : L.l.Prime).one_lt
    have hX : 0 ≤ (L.d : ℝ) * L.N0 * L.N1 * (Real.logb L.l a + 1) :=
      mul_nonneg (by positivity) (logb_add_one_nonneg hl ha.1)
    have hCX := mul_le_mul_of_nonneg_right hC hX
    have h3 : C * (∑ s, w s) / (L.l : ℝ) ≤ C' * (∑ s, w s) / (L.l : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC (Finset.sum_nonneg fun s _ => (hw s).le)) (Nat.cast_nonneg _)
    linarith
  · intro a ha
    refine kvalGe_anti _ _ _ _ _ ?_ (h2 L hL a ha)
    have hl : 1 < L.l := (Fact.out : L.l.Prime).one_lt
    have hX : 0 ≤ (L.N0 : ℝ) * L.N1 * (Real.logb L.l a + 1) :=
      mul_nonneg (by positivity) (logb_add_one_nonneg hl ha.1)
    have hCX := mul_le_mul_of_nonneg_right hC hX
    linarith

end Formalism.MainNotions.product_zeroth_first_parts

end
end

