import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0015
import Mathlib.NumberTheory.ModularForms.NormTrace

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.CuspZero
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd
  UpperTheory.V.Br CongruenceSubgroup

private theorem cusp_zero (N : ℕ) [NeZero N] (f : CuspForm (Gamma1 N) ((0 : ℕ) : ℤ)) : f = 0 := by
  obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero (𝒢 := (Gamma1 N : Subgroup (GL (Fin 2) ℝ)))
    { toFun := f, holo' := f.holo', slash_action_eq' := f.slash_action_eq',
      bdd_at_cusps' := fun hc g hg => (f.zero_at_cusps' hc g hg).isBoundedAtImInfty }
  have hc' : (f : UpperHalfPlane → ℂ) = Function.const UpperHalfPlane c := hc
  have hz : UpperHalfPlane.IsZeroAtImInfty (f : UpperHalfPlane → ℂ) := CuspFormClass.zero_at_infty f
  rw [hc'] at hz
  have h0 : c = 0 := tendsto_nhds_unique tendsto_const_nhds hz
  ext z
  rw [hc', h0]
  rfl

theorem UpperTheory.V.Af.Rn.noLow :
    UpperTheory.V.Sd.Wc.CentChar → UpperTheory.V.Af.Rn.NoLow := by
  intro hC π hπ
  obtain ⟨N, ψ, ν, hN, hν, φ, hφ, h0, hlow, hfix⟩ := levelVec 0 π hπ
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨ω, hω, -⟩ := hC ℚ (π.twist ν)
  have hc := fun z g => hω z φ hφ g
  obtain ⟨χ, hχ⟩ := charOf N hN ω φ h0 hlow.one hfix hc
  have hcusp := (π.twist ν).cusp φ hφ
  obtain ⟨f, -, hL⟩ := deadel 0 N hN χ ω hχ φ hcusp hlow hfix hc
  obtain rfl := cusp_zero N f
  refine h0 (Subtype.ext (funext fun g => ?_))
  obtain ⟨γ, h, u, hu, rfl⟩ := decomp N hN g
  rw [hL γ h u hu]
  simp [nsl]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.EigOfLow
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd
  UpperTheory.V.Br CongruenceSubgroup

open private untwist eig_unique level_zero_eq_maximal_compact ev_not_dvd from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RepEig

theorem UpperTheory.V.Af.Rn.eigOfLow :
    UpperTheory.V.Sd.Wc.CentChar → UpperTheory.V.Af.Rn.EigOfLow := by
  intro hCC k hk1 π hlw
  obtain ⟨N, ψ, ν, hN, hν, φ, hφ, h0, hlow, hfix⟩ := levelVec k π hlw
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨ω, hω, -⟩ := hCC ℚ (π.twist ν)
  have hc := fun z g => hω z φ hφ g
  obtain ⟨χ, hχ⟩ := charOf N hN ω φ h0 hlow.one hfix hc
  have hcusp := (π.twist ν).cusp φ hφ
  obtain ⟨f, hf, hL⟩ := deadel k N hN χ ω hχ φ hcusp hlow hfix hc
  have hf0 : f ≠ 0 := by
    rintro rfl
    refine h0 (Subtype.ext (funext fun g => ?_))
    obtain ⟨γ, h, u, hu, rfl⟩ := decomp N hN g
    rw [hL γ h u hu]
    simp [nsl]
  have hhol : IsHol k (lev N) ω φ := ⟨hcusp.1, fun w u hu => hfix _ (kLocal N hN w u hu), hc, hlow.wt, hlow.low⟩
  obtain ⟨g, hg⟩ := eigEx N k hk1 χ f hf hf0 fun p => Classical.epsilon (IsEigAt k χ f p)
  obtain ⟨χ', g', hg'⟩ := untwist k N hk1 χ ψ g
  refine ⟨N * N, inferInstance, χ', g', ?_⟩
  filter_upwards [Gk.satAE ℚ 2 π, ev_not_dvd (NeZero.ne N),
    Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.unr_ae_and_level ℚ ν).1] with w ⟨B, hB⟩ hw hu
  obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 (TR.CuspSub.HasSat.card hB)
  refine ⟨α, β, hB, ?_⟩
  have hT := TR.CuspSub.HasSat.twist hB hu
  have hp := (places w).1
  have hv : GlobalTheory.LFun.IsSatVecGL w (locSm ℚ w) φ {α * ν.val w, β * ν.val w} :=
    (hT.2 ⟨φ, hφ⟩ (GlobalTheory.LGrp.mem_fixed.2 fun u hu => Subtype.ext (hfix _ (kLocal N hN w u (by
      rwa [(places w).2.2.2 N hN hw, level_zero_eq_maximal_compact])))) fun e => h0 (congrArg Subtype.val e)).map
      (π.twist ν).V.subtype (fun _ _ => rfl) h0
  obtain ⟨h1, h2⟩ := eigOf k N hk1 hN χ ω hχ f φ hL hhol w _ _ hw hv
  have h3 := Classical.epsilon_spec (p := IsEigAt k χ f (normV w)) ⟨_, h1⟩
  have h4 := (hg _ hp h3).trans (eig_unique hf0 h3 h1)
  obtain ⟨h5, h6⟩ := hg' _ hp hw
  have h7 := (charVal N hN ψ ν hν).2 w hw
  have h8 : ψ (normV w : ZMod N) ≠ 0 := h7 ▸ Units.ne_zero _
  simp only [Units.val_mul, h7] at h2 h4 ⊢
  constructor
  · refine mul_right_cancel₀ h8 ?_
    rw [h5, h4]; ring
  · refine mul_right_cancel₀ (pow_ne_zero 2 h8) ?_
    rw [h6, ← h2]; ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.EvPl
section
open private normV_inj normV_surj from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharEq

open Formalism.ConjugateSelfDual UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd UpperTheory.V.Br.CharacterEquality in
theorem UpperTheory.V.Af.Rn.evPl :
    UpperTheory.V.Af.Rn.EvPl := by
  refine ⟨fun P => ⟨fun h => ?_, fun h => ?_⟩, fun M hM => ?_⟩
  · refine Filter.eventually_cofinite.2
      (((Filter.eventually_cofinite.1 h).image fun w => normV w).subset fun p hp => ?_)
    obtain ⟨hp, hne⟩ := Classical.not_imp.1 hp
    obtain ⟨w, rfl⟩ := normV_surj hp
    exact ⟨w, hne, rfl⟩
  · filter_upwards [normV_inj.tendsto_cofinite.eventually h] with w hw
    exact hw (places w).1
  · filter_upwards [normV_inj.tendsto_cofinite.eventually (Set.finite_le_nat M).eventually_cofinite_notMem] with w hw
    exact fun h => hw (Nat.le_of_dvd hM h)
end

