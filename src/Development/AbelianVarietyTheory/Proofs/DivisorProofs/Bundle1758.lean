import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1723
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1632
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1642
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1729
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorSmallCosetHalfIsSchwartzBruhat
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.FunObj.CosSB

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV GlobalTheory.LatVac
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7}

section Small

variable {a b : ℕ}

theorem frAt_add (w : Pl D.host.E) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (x y : Mx D b a) :
    frAt w β' β (x + y) = frAt w β' β x + frAt w β' β y := by
  unfold frAt
  rw [Matrix.map_add _ (toEAf D).map_add, Comparison₂.fr_add, Matrix.map_add _ (cpt (D := D) w).map_add]

theorem frAt_sub (w : Pl D.host.E) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (x y : Mx D b a) :
    frAt w β' β (x - y) = frAt w β' β x - frAt w β' β y := by
  unfold frAt
  rw [Matrix.map_sub _ (toEAf D).map_sub, Comparison₂.fr_sub, Matrix.map_sub _ (cpt (D := D) w).map_sub]

theorem isSmall_add {P : Finset (Pl D.host.E)} {β' : GL (Fin b) (Lev.EAf D)} {β : GL (Fin a) (Lev.EAf D)} {n : ℤ}
    {x y : Mx D b a} (hx : IsSmall P β' β n x) (hy : IsSmall P β' β n y) : IsSmall P β' β n (x + y) :=
  fun w hw i j => by
    rw [frAt_add, Matrix.add_apply]
    exact Valuation.map_add_le _ (hx w hw i j) (hy w hw i j)

theorem isSmall_sub {P : Finset (Pl D.host.E)} {β' : GL (Fin b) (Lev.EAf D)} {β : GL (Fin a) (Lev.EAf D)} {n : ℤ}
    {x y : Mx D b a} (hx : IsSmall P β' β n x) (hy : IsSmall P β' β n y) : IsSmall P β' β n (x - y) :=
  fun w hw i j => by
    rw [frAt_sub, Matrix.sub_apply]
    exact Valuation.map_sub_le _ (hx w hw i j) (hy w hw i j)

theorem isHalf_add_nsmul {e : AE D} {t u : Mx D b a} (k : ℕ) (hu : IsHalf e u) : IsHalf e (t + k • u) ↔ IsHalf e t := by
  have h : ∀ i j, e * (t + k • u) i j = e * t i j + k • u i j := fun i j => by
    rw [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, mul_add, mul_left_comm, hu i j]
  unfold IsHalf
  refine forall₂_congr fun i j => ?_
  rw [h, Matrix.add_apply, Matrix.smul_apply, add_left_inj]

theorem v_unif_pow (w : Pl D.host.E) (n : ℕ) :
    Valued.v (((unifAt w ^ (n : ℤ) : (Kw w)ˣ)) : Kw w) = WithZero.exp (-(n : ℤ)) := by
  have h : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow, h, ← WithZero.exp_nsmul]
  simp

theorem val_le_unif_iff (w : Pl D.host.E) (n : ℕ) (x : Kw w) :
    valuation (Kw w) x ≤ valuation (Kw w) (((unifAt w ^ (n : ℤ) : (Kw w)ˣ)) : Kw w) ↔
      Valued.v x ≤ WithZero.exp (-(n : ℤ)) :=
  (Comparison₂.vEq w _ _).trans (by rw [v_unif_pow])

end Small

section Lat

variable {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem nsmul_mem_hatMx {b : ℕ} (h2 : ∀ x ∈ latRat S T ΛS ΛT, b • x ∈ homLat ΛS ΛT) (𝔪 : Ideal (𝓞 D.host.E))
    {u : WO S T} (hu : u ∈ latO S T ΛS ΛT fun _ => True) :
    (b * Ideal.absNorm 𝔪) • u ∈ hatMx (𝔪 • homLat ΛS ΛT) := by
  refine latO_induction (p := fun u => (b * Ideal.absNorm 𝔪) • u ∈ hatMx (𝔪 • homLat ΛS ΛT)) ?_ ?_ ?_ ?_ hu
  · intro α hα X hX
    rw [← WeilOver.finTens_nsmul]
    refine AddSubgroup.subset_closure ⟨α, hα, _, ?_, rfl⟩
    rw [mul_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 D.host.E)]
    exact Submodule.smul_mem_smul (Ideal.absNorm_mem _) (h2 X hX)
  · rw [nsmul_zero]; exact zero_mem _
  · intro x y hx hy; rw [nsmul_add]; exact add_mem hx hy
  · intro x hx; rw [neg_nsmul]; exact neg_mem hx

theorem nsmul_mem_latO {a : ℕ} (h1 : ∀ x ∈ homLat ΛS ΛT, a • x ∈ latRat S T ΛS ΛT) (𝔪 : Ideal (𝓞 D.host.E))
    {u : WO S T} (hu : u ∈ hatMx (𝔪 • homLat ΛS ΛT)) : a • u ∈ latO S T ΛS ΛT fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    exact WeilOver.finTens_nsmul α a x ▸ finTens_mem_latO hα (h1 x (Submodule.smul_le_right hx))
  | zero => rw [nsmul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [nsmul_add]; exact add_mem hx hy
  | neg x _ hx => rw [neg_nsmul]; exact neg_mem hx

theorem isSmall_of_mem_hatMx {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    (hS : IsFrame βS ΛS) (hT : IsFrame βT ΛT) (P : Finset (Pl D.host.E)) (n : ℕ) {u : WO S T}
    (hu : u ∈ hatMx ((∏ w ∈ P, w.asIdeal ^ n) • homLat ΛS ΛT)) : IsSmall P βT βS n u := by
  intro w hw i j
  obtain ⟨s, hs, h⟩ := ((Comparison₂.mem_hatMx_iff hS hT _ u).1 hu).2 i j
  have h3 := Comparison₂.v_le_of_mem_idS (Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Pl D.host.E => w.asIdeal ^ n) hw)) hs
  rw [val_le_unif_iff]
  change Valued.v (cpt w (Comparison₂.fr βT βS (u.map (toEAf D)) i j)) ≤ _
  rwa [← h]

end Lat

end GlobalTheory.FunObj.CosSB

namespace GlobalTheory.FunObj.CosSB

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV GlobalTheory.LatVac
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem prod_pow_ne_bot {D : D7} (P : Finset (Pl D.host.E)) (n : ℕ) : (∏ w ∈ P, w.asIdeal ^ n) ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
  exact fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in

theorem isSBHalf_cosLoc : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) (e : AE D) (n : ℕ) (r : WO S T),
    Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → IsFrame βS ΛS → IsFrame βT ΛT →
    IsIdemSum e P → IsHalf e r → IsSBHalf e (latO S T ΛS ΛT fun _ => True) (cosLoc P e βT βS n r) := by
  intro D S T ΛS ΛT βS βT P e n r hS hT hFS hFT he _
  classical
  obtain ⟨a, ha, h1⟩ := WeilOver.exists_hom_le hS hT
  obtain ⟨b, hb, h2⟩ := WeilOver.exists_le_hom hS hT
  obtain ⟨e0, e1, e2⟩ := Comparison₂.cpt_idemSum he
  have hM : 0 < Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ n) :=
    Nat.pos_of_ne_zero fun h => prod_pow_ne_bot P n (Ideal.absNorm_eq_zero_iff.1 h)

  set N : ℕ := Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ 1) with hNdef
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => prod_pow_ne_bot P 1 (Ideal.absNorm_eq_zero_iff.1 h)
  have hNmem : ∀ w ∈ P, (N : 𝓞 D.host.E) ∈ w.asIdeal := fun w hw => by
    have := Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Pl D.host.E => w.asIdeal ^ 1) hw)
      (Ideal.absNorm_mem (∏ w ∈ P, w.asIdeal ^ 1))
    rw [pow_one] at this
    exact this

  have hc1 : ∀ p : Fin T.rank × Fin S.rank, ∃ k : ℕ, ∀ l, k ≤ l →
      ((N ^ l : ℕ) : Lev.EAf D) * (toEAf D e * Comparison₂.fr βT βS (r.map (toEAf D)) p.1 p.2) ∈ OA D :=
    fun p => exists_pow_mul_mem _ fun Q hQ => by
      have hQP : Q ∉ P := fun h => hQ (hNmem Q h)
      rw [map_mul, e2 Q hQP, zero_mul]
      exact zero_mem _
  choose kk hkk using hc1
  set c : ℕ := N ^ (Finset.univ.sup kk) with hcdef
  have hc0 : 0 < c := pow_pos hN _
  have hc : ∀ i j, (c : Lev.EAf D) * (toEAf D e * Comparison₂.fr βT βS (r.map (toEAf D)) i j) ∈ OA D :=
    fun i j => hkk (i, j) _ (Finset.le_sup (f := kk) (Finset.mem_univ (i, j)))
  refine ⟨fun t ht => ?_, (a * c) * (b * Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ n)), by positivity,
    fun u hu hh t => ?_, fun t ht => ?_⟩
  · by_contra h
    exact ht (by unfold cosLoc; rw [if_neg fun H => h H.1])
  · have hk : IsSmall P βT βS n (((a * c) * (b * Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ n))) • u) := by
      refine isSmall_of_mem_hatMx hFS hFT P n ?_
      rw [mul_nsmul']
      exact nsmul_mem (nsmul_mem_hatMx h2 _ hu) _
    unfold cosLoc
    refine if_congr (and_congr (isHalf_add_nsmul _ hh) ?_) rfl rfl
    rw [add_sub_right_comm]
    exact ⟨fun h => by simpa using isSmall_sub h hk, fun h => isSmall_add h hk⟩
  · obtain ⟨hth, hts⟩ : IsHalf e t ∧ IsSmall P βT βS n (t - r) := by
      by_contra h
      exact ht (by unfold cosLoc; rw [if_neg h])
    set X := Comparison₂.fr βT βS (t.map (toEAf D))
    set R := Comparison₂.fr βT βS (r.map (toEAf D))
    have hX : Comparison₂.fr βT βS ((c • t).map (toEAf D)) = (c : Lev.EAf D) • (toEAf D e • X) := by
      have : (c • t).map (toEAf D) = (c : Lev.EAf D) • (toEAf D e • t.map (toEAf D)) := by
        ext i j
        rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, nsmul_eq_mul,
          map_mul, map_natCast, smul_eq_mul, smul_eq_mul]
        conv_lhs => rw [← hth i j]
        rw [map_mul]
      rw [this, Comparison₂.fr_smul, Comparison₂.fr_smul]
    have hsm : ∀ i j, toEAf D e * (X - R) i j ∈ OA D := fun i j => by
      refine (mem_OA_iff _).2 fun Q => ?_
      rw [map_mul]
      by_cases hQ : Q ∈ P
      · rw [e1 Q hQ, one_mul]
        have h3 := (val_le_unif_iff Q n _).1 (hts Q hQ i j)
        rw [frAt_sub, Matrix.sub_apply] at h3
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, Matrix.sub_apply, map_sub]
        refine h3.trans ?_
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]
        omega
      · rw [e2 Q hQ, zero_mul]
        exact zero_mem _
    have hint : ∀ i j, Comparison₂.fr βT βS ((c • t).map (toEAf D)) i j ∈ OA D := fun i j => by
      have : Comparison₂.fr βT βS ((c • t).map (toEAf D)) i j =
          (c : Lev.EAf D) * (toEAf D e * (X - R) i j) + (c : Lev.EAf D) * (toEAf D e * R i j) := by
        rw [hX, Matrix.smul_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, smul_eq_mul, ← mul_add, ← mul_add,
          sub_add_cancel]
      rw [this]
      exact add_mem (mul_mem (natCast_mem _ _) (hsm i j)) (hc i j)
    have hmem : c • t ∈ hatMx ((⊤ : Ideal (𝓞 D.host.E)) • homLat ΛS ΛT) := by
      refine (Comparison₂.mem_hatMx_iff hFS hFT ⊤ _).2 ⟨fun i j => ?_, fun i j => ⟨⟨_, hint i j⟩, ?_, rfl⟩⟩
      · rw [Matrix.smul_apply, map_nsmul, ← hth i j, map_mul, e0, zero_mul, smul_zero]
      · rw [idS, Ideal.map_top]
        exact Submodule.mem_top
    have := nsmul_mem (nsmul_mem_latO h1 ⊤ hmem) (b * Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ n))
    convert this using 1
    rw [mul_comm (a * c), ← smul_smul, ← smul_smul a c t]

end GlobalTheory.FunObj.CosSB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedFieldValuationRingStrictlyHenselian
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.InertiaFixedSH

theorem vs_inv_mem_of_not_mem_nonunits {F : Type} [Field F] (A : ValuationSubring F) {x : F} (hx : x ∈ A)
    (hn : x ∉ A.nonunits) : x ≠ 0 ∧ x⁻¹ ∈ A := by
  rw [ValuationSubring.mem_nonunits_iff, not_lt] at hn
  have h1 : A.valuation x = 1 := le_antisymm ((A.valuation_le_one_iff x).2 hx) hn
  refine ⟨fun h => by simp [h] at h1, ?_⟩
  rw [← A.valuation_le_one_iff, map_inv₀, h1, inv_one]

theorem inertiaFixed_strictlyHenselian : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → GlobalTheory.SS.SH (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) (IntermediateField.fixedField (inertia K V)) ∧ ∃ f : R →+* V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω), (∀ r : R, ((f r : IntermediateField.fixedField (inertia K V)) : Ω) = algebraMap K Ω (algebraMap R K r)) ∧ ∀ π : R, Irreducible π → Irreducible (f π) := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV
  have hc : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ V := fun r => by
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := hV ▸ ⟨r, rfl⟩
    exact this
  have hinv : ∀ π : R, Irreducible π → (algebraMap K Ω (algebraMap R K π))⁻¹ ∉ V := by
    intro π hπ h
    have h' : (algebraMap R K π)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
      change algebraMap K Ω _ ∈ V
      rwa [map_inv₀]
    rw [hV] at h'
    obtain ⟨s, hs⟩ := h'
    have hπ0 : algebraMap R K π ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hπ.ne_zero
    apply hπ.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨s, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hs, map_one, mul_inv_cancel₀ hπ0]
  have hc0 : ∀ π : R, Irreducible π → algebraMap K Ω (algebraMap R K π) ≠ 0 := by
    intro π hπ h
    apply hinv π hπ
    rw [h, inv_zero]; exact V.zero_mem
  set K' := IntermediateField.fixedField (inertia K V) with hK'
  set V' := V.comap (algebraMap K' Ω) with hV'
  have memV' : ∀ y : K', y ∈ V' ↔ (y : Ω) ∈ V := fun y => ValuationSubring.mem_comap
  let f : R →+* V' := ((algebraMap K K').comp (algebraMap R K)).codRestrict V' (fun r => by
      rw [memV']; simpa using hc r)
  have hf : ∀ r : R, ((f r : K') : Ω) = algebraMap K Ω (algebraMap R K r) := fun r => by simp [f]
  have unitV' : ∀ a : V', ((a : K') : Ω) ∉ V.nonunits → IsUnit a := by
    intro a ha
    obtain ⟨h0, hi⟩ := vs_inv_mem_of_not_mem_nonunits V ((memV' a).1 a.2) ha
    have hmem : (a : K')⁻¹ ∈ V' := by rw [memV']; simpa using hi
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_inv, OneMemClass.coe_one,
      IntermediateField.coe_one]
    exact mul_inv_cancel₀ h0
  have hfπ : ∀ π : R, Irreducible π → Irreducible (f π) := by
    intro π hπ
    refine irreducible_iff.2 ⟨fun hu => hinv π hπ ?_, fun a b hab => ?_⟩
    · obtain ⟨b, hb⟩ := hu.exists_right_inv
      have hb' : ((f π : K') : Ω) * ((b : K') : Ω) = 1 := by
        have := congrArg (fun z : V' => ((z : K') : Ω)) hb
        simpa using this
      rw [hf] at hb'
      rw [inv_eq_of_mul_eq_one_right hb']
      exact (memV' b).1 b.2
    · by_contra hne
      push_neg at hne
      have ha : ((a : K') : Ω) ∈ V.nonunits := by_contra fun h => hne.1 (unitV' a h)
      have hb : ((b : K') : Ω) ∈ V.nonunits := by_contra fun h => hne.2 (unitV' b h)
      have h1 := GlobalTheory.T.inertiaFixedField_maximalIdeal_dvd_uniformizer R K Ω V hV π hπ _ (a : K').2 ha
      have h2 := GlobalTheory.T.inertiaFixedField_maximalIdeal_dvd_uniformizer R K Ω V hV π hπ _ (b : K').2 hb
      have hab' : algebraMap K Ω (algebraMap R K π) = ((a : K') : Ω) * ((b : K') : Ω) := by
        rw [← hf, hab]; simp
      apply hinv π hπ
      have h0 := hc0 π hπ
      convert mul_mem h1 h2 using 1
      rw [div_mul_div_comm, ← hab']
      field_simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hdvr : IsDiscreteValuationRing V' := by
    refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨f π, hfπ π hπ, fun {x} hx => ?_⟩
    have hx0 : ((x : K') : Ω) ≠ 0 := by
      intro h; apply hx; apply Subtype.ext; apply Subtype.ext; simpa using h
    classical
    have hex := GlobalTheory.T.not_mem_div_uniformizer_pow_alt R K Ω V hV π hπ _ hx0
    have hn := Nat.find_spec hex
    have hn0 : Nat.find hex ≠ 0 := by
      intro h; rw [h] at hn; apply hn; simpa using (memV' x).1 x.2
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := Nat.exists_eq_succ_of_ne_zero hn0
    have hmin : ((x : K') : Ω) / algebraMap K Ω (algebraMap R K π) ^ m ∈ V := by
      have := Nat.find_min hex (show m < Nat.find hex by omega)
      simpa using this
    set y : K' := (x : K') / (algebraMap K K' (algebraMap R K π)) ^ m with hy
    have hyΩ : (y : Ω) = ((x : K') : Ω) / algebraMap K Ω (algebraMap R K π) ^ m := by simp [y]
    have hyV' : y ∈ V' := by rw [memV', hyΩ]; exact hmin
    have hyU : (y : Ω) ∉ V.nonunits := by
      intro hyn
      have := GlobalTheory.T.inertiaFixedField_maximalIdeal_dvd_uniformizer R K Ω V hV π hπ _ y.2 hyn
      apply hn
      rw [hm, hyΩ] at *
      convert this using 1
      rw [pow_succ, div_div]
    refine ⟨m, (unitV' ⟨y, hyV'⟩ hyU).unit, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    simp only [IsUnit.unit_spec, MulMemClass.coe_mul, IntermediateField.coe_mul, SubmonoidClass.coe_pow,
      IntermediateField.coe_pow]
    rw [hf, hyΩ]
    field_simp [pow_ne_zero m (hc0 π hπ)]
  exact ⟨⟨hdvr, GlobalTheory.T.henselianLocalRing_fixedField_inertia_alt R K Ω V hV, GlobalTheory.T.residueField_inertiaFixed_isAlgClosed_alt R K Ω V hV, inferInstance⟩, f, hf, hfπ⟩

end GlobalTheory.InertiaFixedSH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IoExtCore
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.IoExtCore
open GlobalTheory.AdTh.IoExtPf

theorem ioExt_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ i, VStd D i) → (∀ i, LowSm (R.MW i (sg0 D A)) ∧ ExtLine (R.MW i (sg0 D A))) → IoExt R := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR hV hM i
  obtain ⟨hs, hl⟩ := hM i
  obtain ⟨-, hK, v, w, hv1, hw1, hio⟩ := hR.thP.ioP i A.μ0
  obtain ⟨hth, hvac, hcW, hcV, hbW⟩ := GlobalTheory.AdTh.VecFockCore.vec_fock_core D G Pl0 T0 A Ks R F hR i A.μ0 (hV i)
  have hP := (GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A Ks R F hR i A.μ0 (hV i)).1
  have hinj := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hP.weil.std hP.inf (fun _ => 1) (R.BV i)
    (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) (fun τ => ((Wc D i).sig (tauE D τ)).1)
    hcV hcW (hR.models.BV i) hbW hP.sigV hP.sigW _ hth hvac
    (GlobalTheory.AdTh.VecNeCore.thetaVector_ne_zero_core D G Pl0 T0 A Ks R F hR i (hV i))
  let pt := pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
    (R.vP i A.μ0)
  let f : LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) := pt ∘ₗ (R.ioP i).flip w
  have hf : ∀ x, f x = R.ptP i A.μ0 (R.ioP i x w) := fun x => rfl
  have hv0 : f (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    rw [hf, hio]
    exact fun h => Delta_ne i (hinj (h.trans (map_zero pt).symm))
  refine ⟨fun ρ => v ρ, fun τ => ⟨hv1 τ, (v τ).2, fun a ha => ?_⟩, v, w, fun _ => rfl, hw1, hio⟩
  have hm := GlobalTheory.LowKProj.lowKSub_stable _ _ _ _ ha _ (v τ).2
  let u : lowT (R.MW i (sg0 D A)) τ := ⟨⟨_, hs τ hm⟩, hm⟩
  have h1 := hK τ _ ha v u rfl w
  rw [hio, GlobalTheory.T.minorProduct_fockVector_extremalTorusWeight D G Pl0 T0 A Ks R F hR i (hV i) τ a A.μ0, ← hio, ← hf, ← hf] at h1
  have h2 := inj_factor (R.MW i (sg0 D A)) hs hl τ f
    (fun k => R.ωP i A.μ0 (1, atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ)))
    (fun k hk v u hu => hK τ k hk v u hu w) v hv0
    (u - cexp (((∑ j, extWt (R.MW i (sg0 D A)) τ j * a j : ℝ) : ℂ) * I) • v τ) (by
      rw [MultilinearMap.map_update_sub, MultilinearMap.map_update_smul, Function.update_eq_self, map_sub, map_smul, ← h1,
        sub_self])
  exact congrArg (fun y : lowT (R.MW i (sg0 D A)) τ => ((y : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ))
    (sub_eq_zero.1 h2)

end GlobalTheory.AdTh.IoExtCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStandingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdmissibleCMBaseData_of_squareTupleStanding : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (W : G.Weil) (t : T),
    SquareStanding G t → ∀ B : Base D.host.F D.host.E, B.ψ = W.ψ →
      (∀ v ∈ B.P, ∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) → B.IsGood D.sp.cm.sig := by
  first | exact @GlobalTheory.FunObj.base_isGood_of_standing | exact GlobalTheory.FunObj.base_isGood_of_standing | (intros; apply GlobalTheory.FunObj.base_isGood_of_standing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCartanInvolutionHermitianSmulBlockDiagonalReinStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCartanInvolutionHermitian_smul_blockDiagonalReindexed : ∀ {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) (GA sA : Matrix (Fin a) (Fin a) ℂ) (GB sB : Matrix (Fin b) (Fin b) ℂ) {κ : ℝ},
    0 < κ → Formalism.IndefR.Datum.IsCartanInv GA sA → Formalism.IndefR.Datum.IsCartanInv GB sB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan ((κ : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e GA GB) ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e sA sB).map (starRingEnd ℂ)) := by
  first | exact @GlobalTheory.CartanBlocks.isCartan_blk | exact GlobalTheory.CartanBlocks.isCartan_blk | (intros; apply GlobalTheory.CartanBlocks.isCartan_blk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedHermN
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ResAniso

variable (D : D7) (n : ℕ)

def hermN : AddSubgroup (Mx D n n) where
  carrier := {b | adj b = b}
  add_mem' := by
    intro a b ha hb
    change adj _ = _ at ha hb ⊢
    ext i j
    have h1 := congrFun (congrFun ha i) j
    have h2 := congrFun (congrFun hb i) j
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply] at h1 h2 ⊢
    rw [map_add, h1, h2]
  zero_mem' := by simp [adj]
  neg_mem' := by
    intro a ha
    change adj _ = _ at ha ⊢
    ext i j
    have h1 := congrFun (congrFun ha i) j
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply] at h1 ⊢
    rw [map_neg, h1]

variable {D n}

def nElt (b : hermN D n) : StdUnn.G D n := ((StdUnn.Model.exists_unip b.1).2 b.2).choose

theorem mat_nElt (b : hermN D n) : StdUnn.mat (nElt b) = StdUnn.blk4 1 b.1 0 1 :=
  ((StdUnn.Model.exists_unip b.1).2 b.2).choose_spec

variable (D n)

def wElt : StdUnn.G D n := (StdUnn.Model.exists_weyl (D := D) (n := n)).choose

theorem mat_wElt : StdUnn.mat (wElt D n) = StdUnn.blk4 0 1 (-1) 0 :=
  (StdUnn.Model.exists_weyl (D := D) (n := n)).choose_spec

variable {D n}

def intw (db : Measure (hermN D n)) (f : ℂ → StdUnn.G D n → ℂ) (s : ℂ) (g : StdUnn.G D n) : ℂ :=
  ∫ b, f s (wElt D n * nElt b * g) ∂db

def eisOf (H : StdUnn.G D n → ℝ≥0) (s₁ : ℂ) (r : StdUnn.G D n → ℂ) (g : StdUnn.G D n) : ℂ → ℂ :=
  fun s => cosetSum (StdUnn.P D n) (StdUnn.GF D n) (fun x => npow (H x) (s - s₁) * r x) g

end GlobalTheory.ResAniso
end
end

