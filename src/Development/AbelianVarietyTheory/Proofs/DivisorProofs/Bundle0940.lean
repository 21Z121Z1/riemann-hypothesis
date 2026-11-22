import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0914
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0025
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsTwistCharacterUnitsModSpecialIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0920
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0574
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0740
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0921
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0806

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerCutInductionStepOfOpenSubgroup
section
open Matrix Topology GlobalTheory.SmGL GlobalTheory.Whittaker

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin

theorem exists_mul_lr {F : Type} [NormedField F] [ProperSpace F] {ψ : AddChar F ℂ} (hψ : IsLocallyConstant ψ)
    (hψ1 : ψ ≠ 1) {m : ℕ} {L : Set (Fin (m + 1) → F)} (hL : L ∈ nhds (0 : Fin (m + 1) → F))
    (T' : GL (Fin (m + 1)) F →₀ ℂ) (κ : GL (Fin (m + 1)) F → GL (Fin (m + 1)) F) (Φ : (Fin (m + 1) → F) → ℂ)
    (hΦ : IsLocallyConstant Φ) :
    ∃ M₂ : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, Eqv ψ f →
      (∀ y ∈ L, ∀ g, f (g * mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F,
      act (comp M₂ (T'.sum fun k c => Finsupp.single (cor (κ k)) c)) f (cor h) =
        Φ (lr h) * act (T'.sum fun k c => Finsupp.single (cor (κ k)) c) f (cor h) := by
  classical
  have hK := GlobalTheory.JSW.isCompact_charAnnihilator_of_mem_nhds_zero ψ hψ hψ1 L hL
  set K := {r : Fin (m + 1) → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} with hKdef
  let K' : Set (Fin (m + 1) → F) := ⋃ k ∈ T'.support, (fun r => r ᵥ* ((κ k)⁻¹).val) '' K
  have hK' : IsCompact K' := T'.support.isCompact_biUnion fun k _ =>
    hK.image (continuous_id.matrix_vecMul continuous_const)
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_finite_characterSum_eq_locallyConstant_on_compact ψ hψ hψ1 K' hK' Φ hΦ
  set T₂ : GL (Fin (m + 2)) F →₀ ℂ := T'.sum fun k c => Finsupp.single (cor (κ k)) c with hT₂def
  let M₂ : GL (Fin (m + 2)) F →₀ ℂ := M.sum fun v c => Finsupp.single (mir 1 v) c
  refine ⟨M₂, fun f hf hfL h => ?_⟩
  have hT₂ : act T₂ f (cor h) = T'.sum fun k c => c * f (cor (h * κ k)) := by
    simp only [T₂, act_finsupp_sum, act_single, map_mul]
  rw [act_comp]
  simp only [M₂, act_finsupp_sum, act_single, eqv_cor_mul_col (eqv_act hf T₂), ← mul_assoc]
  rw [← Finsupp.sum_mul]
  by_cases h0 : act T₂ f (cor h) = 0
  · rw [h0, mul_zero, mul_zero]
  · rw [hM]
    rw [hT₂] at h0
    obtain ⟨k, hk, hk0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
    have hk1 := right_ne_zero_of_mul hk0
    refine Set.mem_iUnion₂.2 ⟨k, hk, lr (h * κ k), fun y hy => ?_, ?_⟩
    · have := hfL y hy (cor (h * κ k))
      rw [eqv_cor_mul_col hf] at this
      exact (mul_eq_right₀ hk1).1 this
    · simp only
      rw [← lr_mul, mul_inv_cancel_right]

theorem exists_cut_cor_of_sub : ∀ {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ m : ℕ, (∀ U : Subgroup (GL (Fin (m + 1)) F), IsCompact (U : Set (GL (Fin (m + 1)) F)) → IsOpen (U : Set (GL (Fin (m + 1)) F)) → ∀ z : GL (Fin (m + 1)) F, ∃ U₁ : Subgroup (GL (Fin (m + 1)) F), U₁ ≤ U ∧ IsOpen (U₁ : Set (GL (Fin (m + 1)) F)) ∧ GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 1)) F)) (GlobalTheory.JSW.Cut.cell z (U : Set (GL (Fin (m + 1)) F))) {g | ∃ p : GL (Fin (m + 1)) F, GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1 ∧ ∃ u ∈ U₁, g = p * u}) → ∀ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) → IsOpen (B : Set (GL (Fin (m + 1)) F)) → ∀ L : Set (Fin (m + 1) → F), L ∈ nhds (0 : Fin (m + 1) → F) → ∀ h₀ : GL (Fin (m + 1)) F, ∃ T : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, GlobalTheory.JSW.KirFin.Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * GlobalTheory.JSW.KirFin.cor b) = f g) → (∀ y ∈ L, ∀ g, f (g * GlobalTheory.JSW.KirFin.mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.Cut.act T f (GlobalTheory.JSW.KirFin.cor h) = (GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (GlobalTheory.JSW.KirFin.cor h)) h := by
  intro F _ _ _ ψ hψ hψ1 m H B hBc hBo L hL h₀
  classical
  let U : Subgroup (GL (Fin (m + 1)) F) := B.map (MulAut.conj h₀).toMonoidHom
  have hUe : (U : Set (GL (Fin (m + 1)) F)) = (fun b => h₀ * b * h₀⁻¹) '' B := by
    ext x; simp [U]
  have hUm : ∀ b ∈ B, h₀ * b * h₀⁻¹ ∈ U := fun b hb => ⟨b, hb, rfl⟩
  have hUB : ∀ u ∈ U, h₀⁻¹ * u * h₀ ∈ B := by
    rintro _ ⟨b, hb, rfl⟩
    simpa [mul_assoc] using hb
  have hUc : IsCompact (U : Set (GL (Fin (m + 1)) F)) := by
    rw [hUe]; exact hBc.image (by fun_prop)
  have hUo : IsOpen (U : Set (GL (Fin (m + 1)) F)) := by
    rw [hUe]; exact ((isOpenMap_mul_right h₀⁻¹).comp (isOpenMap_mul_left h₀)) _ hBo
  obtain ⟨U₁, hU₁U, hU₁o, T', hT'⟩ := H U hUc hUo 1
  have hU₁c : IsCompact (U₁ : Set (GL (Fin (m + 1)) F)) :=
    hUc.of_isClosed_subset (U₁.isClosed_of_isOpen hU₁o) hU₁U
  have hOe := GlobalTheory.T.isClopen_rowVector_orbit_compactOpen_GL U₁ hU₁c hU₁o (lr 1) (lr_ne_zero 1)
  let R : GL (Fin (m + 1)) F → Set (Fin (m + 1) → F) := fun a =>
    (fun r => r ᵥ* ((a * h₀)⁻¹).val) ⁻¹' {r | ∃ b ∈ U₁, r = lr 1 ᵥ* (b : Matrix (Fin (m + 1)) (Fin (m + 1)) F)}
  have hR : ∀ a, IsClopen (R a) := fun a => hOe.preimage (continuous_id.matrix_vecMul continuous_const)

  have hC : ∀ a ∈ U, ∀ f : GL (Fin (m + 2)) F → ℂ, Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * cor b) = f g) →
      ∀ h, lr h ∈ R a → act (T'.sum fun k c => Finsupp.single (cor (h₀⁻¹ * a⁻¹ * k * h₀)) c) f (cor h) =
        (cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (cor h)) h := by
    intro a ha f hf hfB h hRa
    obtain ⟨v, hv, e⟩ := hRa
    have e' : lr (h * h₀⁻¹ * a⁻¹) = lr (1 * v) := by
      rw [show h * h₀⁻¹ * a⁻¹ = h * (a * h₀)⁻¹ by group]
      exact e
    have hmem : h * h₀⁻¹ * a⁻¹ ∈ {g | ∃ p : GL (Fin (m + 1)) F, lr p = lr 1 ∧ ∃ u ∈ U₁, g = p * u} :=
      ⟨h * h₀⁻¹ * a⁻¹ * v⁻¹, by rw [lr_mul_congr e' v⁻¹, one_mul, mul_inv_cancel], v, hv, by group⟩
    have h2 := hT' (fun g => f (cor (g * h₀)))
      (fun u hu g => by simp only [mul_assoc]; exact hf.res u hu _)
      (fun u hu g => by
        rw [show g * u * h₀ = g * h₀ * (h₀⁻¹ * u * h₀) by group, map_mul]
        exact hfB _ (hUB u hu) _)
      (h * h₀⁻¹ * a⁻¹) hmem
    have hT₂ : act (T'.sum fun k c => Finsupp.single (cor (h₀⁻¹ * a⁻¹ * k * h₀)) c) f (cor h) =
        T'.sum fun k c => c * f (cor (h * (h₀⁻¹ * a⁻¹ * k * h₀))) := by
      simp only [act_finsupp_sum, act_single, map_mul]
    have h3 : act (T'.sum fun k c => Finsupp.single (cor (h₀⁻¹ * a⁻¹ * k * h₀)) c) f (cor h) =
        act T' (fun g => f (cor (g * h₀))) (h * h₀⁻¹ * a⁻¹) := by
      rw [hT₂]
      simp only [act, mul_assoc]
    rw [h3, h2]
    have h4 : h * h₀⁻¹ * a⁻¹ ∈ cell 1 (U : Set (GL (Fin (m + 1)) F)) ↔
        h ∈ cell h₀ (B : Set (GL (Fin (m + 1)) F)) := by
      constructor
      · rintro ⟨u, hu, c, hc, e⟩
        refine ⟨u, hu, h₀⁻¹ * (c * a) * h₀, hUB _ (U.mul_mem hc ha), ?_⟩
        rw [show h = h * h₀⁻¹ * a⁻¹ * (a * h₀) by group, e]
        group
      · rintro ⟨u, hu, c, hc, rfl⟩
        exact ⟨u, hu, h₀ * c * h₀⁻¹ * a⁻¹, U.mul_mem (hUm c hc) (U.inv_mem ha), by group⟩
    by_cases h5 : h ∈ cell h₀ (B : Set (GL (Fin (m + 1)) F))
    · rw [Set.indicator_of_mem h5, Set.indicator_of_mem (h4.2 h5)]
      rw [show h * h₀⁻¹ * a⁻¹ * h₀ = h * (h₀⁻¹ * a⁻¹ * h₀) by group, map_mul]
      exact hfB _ (by simpa using hUB _ (U.inv_mem ha)) _
    · rw [Set.indicator_of_notMem h5, Set.indicator_of_notMem (fun h6 => h5 (h4.1 h6))]

  have key : ∀ A : Finset (GL (Fin (m + 1)) F), (∀ a ∈ A, a ∈ U) → ∃ S : GL (Fin (m + 2)) F →₀ ℂ,
      ∀ f : GL (Fin (m + 2)) F → ℂ, Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * cor b) = f g) →
      (∀ y ∈ L, ∀ g, f (g * mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F,
      act S f (cor h) = (⋃ a ∈ A, R a).indicator 1 (lr h) *
        (cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (cor h)) h := by
    intro A
    induction A using Finset.induction_on with
    | empty => intro _; exact ⟨0, fun f _ _ _ h => by simp⟩
    | insert a A haA ih =>
      intro hA
      obtain ⟨S, hS⟩ := ih (fun b hb => hA b (Finset.mem_insert_of_mem hb))
      have ha : a ∈ U := hA a (Finset.mem_insert_self a A)
      have hcl : IsClopen (R a \ ⋃ b ∈ A, R b) := (hR a).diff (isClopen_biUnion_finset fun b _ => hR b)
      obtain ⟨M₂, hM₂⟩ := exists_mul_lr hψ hψ1 hL T' (fun k => h₀⁻¹ * a⁻¹ * k * h₀)
        ((R a \ ⋃ b ∈ A, R b).indicator 1) (LocallyConstant.charFn ℂ hcl).isLocallyConstant
      refine ⟨S + comp M₂ (T'.sum fun k c => Finsupp.single (cor (h₀⁻¹ * a⁻¹ * k * h₀)) c),
        fun f hf hfB hfL h => ?_⟩
      rw [act_add, hS f hf hfB hfL h, hM₂ f hf hfL h]
      by_cases h1 : lr h ∈ ⋃ b ∈ A, R b
      · have h2 : lr h ∈ ⋃ b ∈ insert a A, R b := by
          rw [Finset.set_biUnion_insert]; exact Or.inr h1
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
          Set.indicator_of_notMem (s := R a \ ⋃ b ∈ A, R b) (fun h3 => h3.2 h1)]
        simp
      · by_cases h3 : lr h ∈ R a
        · have h2 : lr h ∈ ⋃ b ∈ insert a A, R b := by
            rw [Finset.set_biUnion_insert]; exact Or.inl h3
          rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, Set.indicator_of_mem (s := R a \ ⋃ b ∈ A, R b) ⟨h3, h1⟩,
            hC a ha f hf hfB h h3]
          simp
        · have h2 : lr h ∉ ⋃ b ∈ insert a A, R b := by
            rw [Finset.set_biUnion_insert]; exact fun h4 => h4.elim h3 h1
          rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2,
            Set.indicator_of_notMem (s := R a \ ⋃ b ∈ A, R b) (fun h4 => h3 h4.1)]
          simp
  obtain ⟨t, ht⟩ := hUc.elim_finite_subcover
    (fun a : U => (fun x => x * (a : GL (Fin (m + 1)) F)⁻¹) ⁻¹' (U₁ : Set (GL (Fin (m + 1)) F)))
    (fun a => hU₁o.preimage (continuous_mul_right _))
    (fun u hu => Set.mem_iUnion.2 ⟨⟨u, hu⟩, by simp [U₁.one_mem]⟩)
  obtain ⟨S, hS⟩ := key (t.image Subtype.val) (fun a ha => by
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 ha
    exact b.2)
  refine ⟨S, fun f hf hfB hfL h => ?_⟩
  rw [hS f hf hfB hfL h]
  by_cases hh : h ∈ cell h₀ (B : Set (GL (Fin (m + 1)) F))
  · have hmem : lr h ∈ ⋃ a ∈ t.image Subtype.val, R a := by
      obtain ⟨u, hu, c, hc, rfl⟩ := hh
      obtain ⟨i, hi, hw⟩ := Set.mem_iUnion₂.1 (ht (hUm c hc))
      refine Set.mem_iUnion₂.2 ⟨i.1, Finset.mem_image_of_mem _ hi, h₀ * c * h₀⁻¹ * (i : GL (Fin (m + 1)) F)⁻¹, hw, ?_⟩
      show lr (u * h₀ * c) ᵥ* _ = _
      rw [← lr_mul, show u * h₀ * c * ((i : GL (Fin (m + 1)) F) * h₀)⁻¹ =
        u * (h₀ * c * h₀⁻¹ * (i : GL (Fin (m + 1)) F)⁻¹) by group, lr_mul_congr (lr_of_mem hu), one_mul, ← lr_mul, one_mul]
    rw [Set.indicator_of_mem hmem, Pi.one_apply, one_mul]
  · rw [Set.indicator_of_notMem hh, mul_zero]

end GlobalTheory.JSW.Cut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFieldCharacterLabelsCompatNormPowInv
section
open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.LabelNorm

variable {p : ℕ} [Fact p.Prime]

theorem sub_pos' {d : ℕ} (hd : 0 < d) : 0 < p ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)

theorem theta_gen_pow (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {x : Fbar p} (hx : x ^ (p ^ d - 1) = 1)
    (n : ℕ) : GlobalTheory.GLq.thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  have h : ∃ m : ℕ, L.gen d ^ n = L.gen d ^ m := ⟨n, rfl⟩
  unfold GlobalTheory.GLq.thetaOf
  rw [dif_pos h]
  have hp : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have hfin : IsOfFinOrder (L.gen d) := isOfFinOrder_iff_pow_eq_one.2 ⟨_, sub_pos' hd, hp.pow_eq_one⟩
  have hm : n ≡ h.choose [MOD p ^ d - 1] := by
    rw [← L.gen_order d hd]; exact hfin.pow_eq_pow_iff_modEq.1 h.choose_spec
  have h1 : L.teich x ^ (p ^ d - 1) = 1 := by rw [← map_pow, hx, map_one]
  rw [pow_eq_pow_mod h.choose h1, pow_eq_pow_mod n h1, hm]

theorem exists_pow (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) {z : Fbar p} (hz : z ^ (p ^ d - 1) = 1) :
    ∃ n : ℕ, z = L.gen d ^ n := by
  haveI : NeZero (p ^ d - 1) := ⟨(sub_pos' hd).ne'⟩
  have hprim : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hz
  exact ⟨n, hn.symm⟩

theorem tor_pow {d : ℕ} (u : Tor p d) : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ d - 1) = 1 := by
  rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]

theorem base_pow (c : (ZMod p)ˣ) : algebraMap (ZMod p) (Fbar p) c ^ (p ^ 1 - 1) = 1 :=
  tor_pow (toTorOne p c)

theorem labels_norm_pow (L : GlobalTheory.GLq.LabelDatum p) {N : ℕ} (hN : 0 < N) (d : ℕ) (h : d ∣ N) (θ : Tor p d →* ℂˣ)
    (x : Fbar p) (n : ℕ) (hθ : LabelsChar L θ x) : LabelsChar L ((θ.comp (torNorm p h)) ^ n) (x ^ n) := by
  have hd : 0 < d := Nat.pos_of_dvd_of_pos h hN
  have hx : (x ^ n) ^ (p ^ N - 1) = 1 := by
    obtain ⟨k, hk⟩ := Nat.pow_sub_one_dvd_pow_sub_one p h
    rw [hk, ← pow_mul, mul_comm n, pow_mul, pow_mul, hθ.1, one_pow, one_pow]
  refine ⟨hx, fun u => ?_⟩
  obtain ⟨k, hk⟩ := exists_pow L hN (tor_pow u)
  have hn : (((torNorm p h u : Tor p d) : (Fbar p)ˣ) : Fbar p) = L.gen d ^ k := by
    have e : (((torNorm p h u : Tor p d) : (Fbar p)ˣ) : Fbar p) =
        ((u : (Fbar p)ˣ) : Fbar p) ^ ((p ^ N - 1) / (p ^ d - 1)) := Units.val_pow_eq_pow_val _ _
    obtain ⟨e', rfl⟩ := h
    rw [e, hk, ← pow_mul, mul_comm k, pow_mul, L.gen_norm d e' hd (Nat.pos_of_mul_pos_left hN)]
  rw [hk, theta_gen_pow L hN hx, MonoidHom.pow_apply, MonoidHom.comp_apply, Units.val_pow_eq_pow_val, hθ.2, hn,
    theta_gen_pow L hd hθ.1, map_pow, ← pow_mul, ← pow_mul, mul_comm]

theorem labels_base (L : GlobalTheory.GLq.LabelDatum p) {N : ℕ} (hN : 0 < N) (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ)
    (h : LabelsTame L χ a) :
    LabelsChar L (χ.comp (baseNorm p N)) (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) := by
  have h1 : LabelsChar L (χ.comp ((MulEquiv.ofBijective (toTorOne p) (toTorOne_bijective p)).symm :
      Tor p 1 →* (ZMod p)ˣ)) (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) := by
    refine ⟨base_pow a, fun u => ?_⟩
    obtain ⟨v, rfl⟩ := (MulEquiv.ofBijective (toTorOne p) (toTorOne_bijective p)).surjective u
    rw [MonoidHom.comp_apply, MonoidHom.coe_coe, MulEquiv.symm_apply_apply, ← h v]
    rfl
  have h2 := labels_norm_pow L hN 1 (one_dvd N) _ _ 1 h1
  rw [pow_one, pow_one] at h2
  exact h2

theorem labels_inv (L : GlobalTheory.GLq.LabelDatum p) (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ)
    (h : LabelsTame L χ a) : LabelsTame L χ⁻¹ a⁻¹ := by
  intro u
  obtain ⟨k, hk⟩ := exists_pow L one_pos (base_pow u)
  have h1 := h u
  rw [hk, theta_gen_pow L one_pos (base_pow a)] at h1
  rw [hk, theta_gen_pow L one_pos (base_pow a⁻¹), MonoidHom.inv_apply, Units.val_inv_eq_inv_val (χ u), ← h1,
    ← inv_pow]
  congr 1
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (N : ℕ), 0 < N → (∀ (d : ℕ) (h : d ∣ N) (θ : Tor p d →* ℂˣ) (x : Fbar p) (n : ℕ), LabelsChar L θ x → LabelsChar L ((θ.comp (torNorm p h)) ^ n) (x ^ n)) ∧ ∀ (χ : (ZMod p)ˣ →* ℂˣ) (a : (ZMod p)ˣ), LabelsTame L χ a → LabelsChar L (χ.comp (baseNorm p N)) (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) ∧ LabelsTame L χ⁻¹ a⁻¹ :=
  fun _ _ L _ hN => ⟨labels_norm_pow L hN, fun χ a h => ⟨labels_base L hN χ a h, labels_inv L χ a h⟩⟩

end GlobalTheory.LabelNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitChineseRemainder
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitResidue

theorem exists_isUnit_map_eq {A B : Type} [CommRing A] [CommRing B] [IsArtinianRing A] (φ : A →+* B) (a : A)
    (ha : IsUnit (φ a)) : ∃ b b' : A, b * b' = 1 ∧ φ b = φ a := by
  obtain ⟨n, y, h⟩ := IsArtinian.exists_pow_succ_smul_dvd a (1 : A)
  simp only [smul_eq_mul, mul_one, Nat.succ_eq_add_one] at h
  have h1 : (a * y) ^ n * (a * y) = (a * y) ^ n := by
    rw [mul_pow]; linear_combination y ^ n * h
  have h2 : ∀ m : ℕ, (a * y) ^ n * (a * y) ^ m = (a * y) ^ n := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, ← mul_assoc, ih, h1]
  have h3 := h2 n
  have h4 : φ (a * y) = 1 := by
    have := congrArg φ h
    rw [map_mul, map_pow, map_pow, pow_succ, mul_assoc, ← map_mul] at this
    exact (ha.pow n).mul_left_cancel (this.trans (mul_one _).symm)
  have h5 : φ ((a * y) ^ n) = 1 := by rw [map_pow, h4, one_pow]
  generalize (a * y) ^ n = e at *
  refine ⟨a * e + (1 - e), y * e + (1 - e), ?_, by simp [h5]⟩
  linear_combination e * h1 + (2 - a - y) * h3

theorem exists_unit_mod {O : Type} [CommRing O] (I J : Ideal O) (hIJ : I ⊔ J = ⊤) (N : O) (hI : N ∈ I) (hJ : N ∈ J)
    [Finite (O ⧸ Ideal.span {N})] (u : O) (hu : IsUnit (Ideal.Quotient.mk I u)) :
    ∃ b b' k : O, b * b' = 1 + N * k ∧ b - u ∈ I ∧ b - 1 ∈ J := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hIJ)
  have hI' : Ideal.span {N} ≤ I := (Ideal.span_singleton_le_iff_mem _).2 hI
  have hJ' : Ideal.span {N} ≤ J := (Ideal.span_singleton_le_iff_mem _).2 hJ
  have e1 : Ideal.Quotient.mk I (u * j + i) = Ideal.Quotient.mk I u := by
    rw [Ideal.Quotient.eq, show u * j + i - u = (1 - u) * i by linear_combination u * hij]
    exact I.mul_mem_left _ hi
  have e2 : Ideal.Quotient.mk J (u * j + i) = Ideal.Quotient.mk J 1 := by
    rw [Ideal.Quotient.eq, show u * j + i - 1 = (u - 1) * j by linear_combination hij]
    exact J.mul_mem_left _ hj
  obtain ⟨b, b', h, hb⟩ := exists_isUnit_map_eq
    ((Ideal.Quotient.factor hI').prod (Ideal.Quotient.factor hJ')) (Ideal.Quotient.mk _ (u * j + i)) (by
      rw [Prod.isUnit_iff]
      refine ⟨?_, ?_⟩
      · change IsUnit (Ideal.Quotient.mk I (u * j + i))
        rw [e1]; exact hu
      · change IsUnit (Ideal.Quotient.mk J (u * j + i))
        rw [e2, map_one]; exact isUnit_one)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b'
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (Ideal.span {N})), Ideal.Quotient.eq,
    Ideal.mem_span_singleton] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨b, b', k, by linear_combination hk, ?_, ?_⟩
  · exact Ideal.Quotient.eq.1 ((congrArg Prod.fst hb).trans e1)
  · exact Ideal.Quotient.eq.1 ((congrArg Prod.snd hb).trans e2)

open GlobalTheory.AdLat GlobalTheory.AdLat.RootNear

theorem exists_unit_hat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ)
    (b b' k : 𝓞 E) (h : b * b' = 1 + N * k) :
    ∃ y ∈ intHat F E, ∃ y' ∈ intHat F E, ∃ w ∈ intHat F E, y * y' = 1 ∧
      y = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E) + (N : RA F E) * w := by
  obtain ⟨y, w, hy⟩ := GlobalTheory.TwistChar.exists_unit_lift F E N (ratHat F E b) (ratHat F E b')
    (ratHat F E k) (by rw [← RingHom.map_mul, h, RingHom.map_add, RingHom.map_one, RingHom.map_mul, map_natCast])
  refine ⟨_, (y : intHat F E).2, _, ((y⁻¹ : (intHat F E)ˣ) : intHat F E).2, _, w.2,
    congrArg Subtype.val y.mul_inv, ?_⟩
  rw [hy]
  push_cast
  rfl

theorem exists_idele (D : D7) (y y' : Af D.host.F ⊗[D.host.F] D.host.E) (h : y * y' = 1) :
    ∃ x : (AE D)ˣ, infPart D (x : AE D) = 1 ∧ finPart D (x : AE D) = y ∧
      finPart D ((x⁻¹ : (AE D)ˣ) : AE D) = y' := by
  obtain ⟨e, he, -, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hf : ∀ p, finPart D (e.symm p) = p.2 := fun p =>
    ((he (e.symm p)).2.symm).trans (by rw [e.apply_symm_apply])
  have hi : ∀ p, infPart D (e.symm p) = p.1 := fun p =>
    ((he (e.symm p)).1.symm).trans (by rw [e.apply_symm_apply])
  have hm : e.symm (1, y) * e.symm (1, y') = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, h, one_mul]
    exact map_one _
  exact ⟨⟨_, _, hm, (mul_comm _ _).trans hm⟩, hi _, hf _, hf _⟩

theorem add_mem_idealHat (D : D7) (I : Ideal (𝓞 D.host.E)) (N : ℕ) (hN : (N : 𝓞 D.host.E) ∈ I)
    (b u : 𝓞 D.host.E) (hb : b - u ∈ I) (w : Af D.host.F ⊗[D.host.F] D.host.E) (hw : w ∈ intAE D)
    (h1 : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D) :
    (1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E) + (N : Af D.host.F ⊗[D.host.F] D.host.E) * w -
      (1 : Af D.host.F) ⊗ₜ[D.host.F] (u : D.host.E) ∈ GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.idealHat D I := by
  have e : (1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E) + (N : Af D.host.F ⊗[D.host.F] D.host.E) * w -
      (1 : Af D.host.F) ⊗ₜ[D.host.F] (u : D.host.E) =
      (1 : Af D.host.F) ⊗ₜ[D.host.F] ((b - u : 𝓞 D.host.E) : D.host.E) * 1 +
      (1 : Af D.host.F) ⊗ₜ[D.host.F] ((N : 𝓞 D.host.E) : D.host.E) * w := by
    have e1 : ((b - u : 𝓞 D.host.E) : D.host.E) = (b : D.host.E) - u := rfl
    have e2 : (1 : Af D.host.F) ⊗ₜ[D.host.F] ((N : 𝓞 D.host.E) : D.host.E) =
        (N : Af D.host.F ⊗[D.host.F] D.host.E) :=
      map_natCast ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Af D.host.F)
        (B := D.host.E)).toRingHom.comp (algebraMap (𝓞 D.host.E) D.host.E)) N
    rw [e1, e2, TensorProduct.tmul_sub]
    ring
  rw [e]
  exact add_mem (AddSubgroup.subset_closure ⟨_, hb, 1, h1, rfl⟩) (AddSubgroup.subset_closure ⟨_, hN, w, hw, rfl⟩)

theorem exists_finUnit_congMod : ∀ (D : D7) (I J : Ideal (𝓞 D.host.E)), I ≠ ⊥ → J ≠ ⊥ → I ⊔ J = ⊤ → ∀ u : 𝓞 D.host.E, IsUnit (Ideal.Quotient.mk I u) → ∃ x : (AE D)ˣ, FinUnit x ∧ GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.CongMod I x u ∧ GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.CongMod J x 1 := by
  intro D I J hI hJ hIJ u hu
  have hS : ∀ w, w ∈ intAE D ↔ w ∈ intHat D.host.F D.host.E := fun w => by
    rw [GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers]; rfl
  obtain ⟨N, hN, hNI, hNJ⟩ : ∃ N : ℕ, N ≠ 0 ∧ (N : 𝓞 D.host.E) ∈ I ∧ (N : 𝓞 D.host.E) ∈ J := by
    refine ⟨Ideal.absNorm I * Ideal.absNorm J, mul_ne_zero ?_ ?_, ?_, ?_⟩
    · rwa [Ne, Ideal.absNorm_eq_zero_iff]
    · rwa [Ne, Ideal.absNorm_eq_zero_iff]
    · rw [Nat.cast_mul]; exact I.mul_mem_right _ I.absNorm_mem
    · rw [Nat.cast_mul]; exact J.mul_mem_left _ J.absNorm_mem
  haveI : Finite (𝓞 D.host.E ⧸ Ideal.span {(N : 𝓞 D.host.E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN)
  obtain ⟨b, b', k, h, hb, hb1⟩ := exists_unit_mod I J hIJ N hNI hNJ u hu
  obtain ⟨y, hy, y', hy', w, hw, hyy, e⟩ := exists_unit_hat D.host.F D.host.E N b b' k h
  obtain ⟨x, hx1, hx2, hx3⟩ := exists_idele D y y' hyy
  have h1 := (hS 1).2 (one_mem _)
  refine ⟨x, ⟨hx1, ?_, ?_⟩, ?_, ?_⟩
  · rw [hx2]; exact (hS _).2 hy
  · rw [hx3]; exact (hS _).2 hy'
  · unfold GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.CongMod
    rw [hx2, e]
    exact add_mem_idealHat D I N hNI b u hb w ((hS w).2 hw) h1
  · unfold GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions.CongMod
    rw [hx2, e]
    exact add_mem_idealHat D J N hNJ b 1 hb1 w ((hS w).2 hw) h1

end GlobalTheory.UnitResidue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumEqFinsumConjugacyClassesCentraliserCosetsStatement
section
open GlobalTheory.BCT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_eq_finsum_conjugacyClasses_centraliserCosets : ∀ {H : Type} [Group H] (a : H → ℂ), (Function.support a).Finite → ∑ᶠ γ, a γ = ∑ᶠ c : TwCl (MonoidHom.id H), ∑ᶠ δ : H ⧸ twCent (MonoidHom.id H) c.rep, a (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) := by
  first | exact @GlobalTheory.ConjRegroup.finsum_eq_finsum_classes | exact GlobalTheory.ConjRegroup.finsum_eq_finsum_classes | (intros; apply GlobalTheory.ConjRegroup.finsum_eq_finsum_classes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSourceGlActionSymmetrisedOppositeSignsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSourceGlActionSymmetrised_opposite_signs : ∀ {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (Y : Matrix (Fin a) (Fin a) ℂ),
    (∀ i j, ε' i ≠ ε j) →
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' Y = -(GlobalTheory.ColLie.colDer τ Y.transpose : Module.End ℂ (PolF D b a)) - (((b : ℂ) / 2) * Y.trace) • 1 := by
  first | exact @GlobalTheory.FockOpp.fockS_of_opposite | exact GlobalTheory.FockOpp.fockS_of_opposite | (intros; apply GlobalTheory.FockOpp.fockS_of_opposite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSourceGlActionSymmetrisedSameSignsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockSourceGlActionSymmetrised_same_signs : ∀ {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (Y : Matrix (Fin a) (Fin a) ℂ),
    (∀ i j, ε' i = ε j) →
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' Y = (GlobalTheory.ColLie.colDer τ Y : Module.End ℂ (PolF D b a)) + (((b : ℂ) / 2) * Y.trace) • 1 := by
  first | exact @GlobalTheory.ColLie.fockS_eq_colDer_of_same_signs | exact GlobalTheory.ColLie.fockS_eq_colDer_of_same_signs | (intros; apply GlobalTheory.ColLie.fockS_eq_colDer_of_same_signs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBasisChangeInvariaStatement
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupDeterminantPowDepth_basis_change_invariant : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C) (g : Matrix (Fin i) (Fin i) C), v g.det = 0 → detDepth G (fun a => ∑ a', g a a' • u a') c = detDepth G u c := by
  first | exact @GlobalTheory.DetDepthBasis.main | exact GlobalTheory.DetDepthBasis.main | (intros; apply GlobalTheory.DetDepthBasis.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDifferentialOperatorDepthEqIInfMonomiStatement
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupDifferentialOperatorDepth_eq_iInf_monomial : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (κ : Type) [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (G : ∀ b, LogFGL v (d b)) (ι : κ → Type) [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)] (u : ∀ b, ι b → Fin (d b) → C) (P : MvPolynomial (Σ b, ι b) C), depth G u P = ⨅ β ∈ {β : (Σ b, Fin (d b)) →₀ ℕ | β.degree ≤ P.totalDegree}, toE (v (derivAt0 P (subst (expAlong G u) (monomial β (1 : C))))) := by
  first | exact @GlobalTheory.DepthDegree.depth_eq_iInf_monomial_degree_le | exact GlobalTheory.DepthDegree.depth_eq_iInf_monomial_degree_le | (intros; apply GlobalTheory.DepthDegree.depth_eq_iInf_monomial_degree_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOrbitRootPolynomialFactorizationStatement
section
open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusOrbitRootPolynomial_factorization : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (b : Fin r → Fin r) (x : Cyc b → Fbar p) (f : (ZMod p)[X]), IsRootPoly x f → f.natDegree = r ∧ f.coeff 0 ≠ 0 ∧ (Squarefree f ↔ Function.Injective (rootElt x)) ∧ (Squarefree f → (∀ c, (minpoly (ZMod p) (x c)).natDegree = cycLen b c) ∧ Function.Injective (fun c => minpoly (ZMod p) (x c)) ∧ f = ∏ c, minpoly (ZMod p) (x c)) := by
  first | exact @GlobalTheory.ParamLabel.RootPolyFactor.rootPoly_factor | exact GlobalTheory.ParamLabel.RootPolyFactor.rootPoly_factor | (intros; apply GlobalTheory.ParamLabel.RootPolyFactor.rootPoly_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPreservesIntegerRing
section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

namespace GlobalTheory.LKLoc

theorem frobR_mem_intR (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) :
    ∀ x ∈ intR p K r, frobR p K r x ∈ intR p K r := by
  intro x hx
  have hx' : ((x : PadicAlgCl p)) ∈ Obar p := hx
  show ((frobR p K r x : Kn p K r) : PadicAlgCl p) ∈ Obar p
  have h : ((frobR p K r x : Kn p K r) : PadicAlgCl p) = frobK p K (x : PadicAlgCl p) := rfl
  rw [h, mem_Obar_iff, norm_map_GK]
  exact mem_Obar_iff.1 hx'

end GlobalTheory.LKLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebraStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodForms_eq_killed_by_groupAlgebra : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (P : LevelP L.Pg L.r ℂ) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]), L.s = 0 → L.Q = ∅ → LiftsExist V β L → goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) (gaL V β L eG c) ⊓ hPart M (levG V β (flag1L L)) ok pl q Sg = allMaps θ M ⊓ killed (finRep M) (eqSet V β L eG c P ok pl q Sg) := by
  first | exact @GlobalTheory.CuspMult.EqCut.good_hecke_eq_killed | exact GlobalTheory.CuspMult.EqCut.good_hecke_eq_killed | (intros; apply GlobalTheory.CuspMult.EqCut.good_hecke_eq_killed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCuspidalCharIsCuspidalOfMinpolyOfParamStatement
section
open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.greenCuspidalChar_isCuspidalOfMinpoly_of_param : GlobalTheory.GLq.Green → ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p), 5 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (θ : Tor p (Fintype.card ι) →* ℂˣ) (x : Fbar p), 0 < Fintype.card ι → LabelsChar L θ x → (minpoly (ZMod p) x).natDegree = Fintype.card ι → GlobalTheory.GLq.IsCuspOf L (minpoly (ZMod p) x) (cuspOn θ) := by
  first | exact @GlobalTheory.ParamLabel.isCuspOf_cuspOn_of_green | exact GlobalTheory.ParamLabel.isCuspOf_cuspOn_of_green | (intros; apply GlobalTheory.ParamLabel.isCuspOf_cuspOn_of_green <;> assumption)
end

