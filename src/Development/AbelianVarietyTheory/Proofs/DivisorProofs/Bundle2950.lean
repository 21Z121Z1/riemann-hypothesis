import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2839
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2851
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2849
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LbIsoOfAssociatedGermsFlat
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2682
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2547
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2661
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionRatioDetermined
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ConjArith

theorem int_of_coprime_denoms (x : ℝ)
    (h : ∀ k : ℕ, 0 < k → ∃ b : ℕ, 0 < b ∧ Nat.Coprime b k ∧ ∃ n : ℤ, (b : ℝ) * x = n) :
    ∃ n : ℤ, x = n := by
  obtain ⟨b₁, hb₁, -, n₁, h₁⟩ := h 1 one_pos
  obtain ⟨b, hb, hcop, n, hn⟩ := h b₁ hb₁
  have hb₁R : (b₁ : ℝ) ≠ 0 := by exact_mod_cast hb₁.ne'
  have key : (n₁ : ℤ) * b = n * b₁ := by
    have : (n₁ : ℝ) * b = n * b₁ := by rw [← h₁, ← hn]; ring
    exact_mod_cast this
  have hdvd : (b₁ : ℤ) ∣ n₁ * b := ⟨n, by rw [key]; ring⟩
  have hc : IsCoprime (b₁ : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
  obtain ⟨t, ht⟩ := hc.dvd_of_dvd_mul_right hdvd
  refine ⟨t, ?_⟩
  have : (b₁ : ℝ) * x = b₁ * t := by rw [h₁, ht]; push_cast; ring
  exact mul_left_cancel₀ hb₁R this

theorem int_core {S : Type} (m n : S → ℤ)
    (h : ∀ k : ℕ, 0 < k → ∃ a : ℤ, ∃ b : ℕ, Nat.Coprime b k ∧ IsCoprime a (k : ℤ) ∧
      ∀ s, (k : ℤ) ∣ n s - a * b * m s)
    (s₀ : S) (hm : m s₀ ≠ 0) (hpos : 0 < m s₀ * n s₀) : ∀ s, n s = m s := by
  have hn : n s₀ ≠ 0 := by
    rintro h0; rw [h0, mul_zero] at hpos; exact lt_irrefl _ hpos
  have h1 : m s₀ ∣ n s₀ := by
    obtain ⟨a, b, -, -, hk⟩ := h (m s₀).natAbs (Int.natAbs_pos.mpr hm)
    have h2 : ((m s₀).natAbs : ℤ) ∣ a * b * m s₀ :=
      Dvd.dvd.mul_left (Int.natAbs_dvd.mpr dvd_rfl) _
    have h3 := dvd_add (hk s₀) h2
    rw [sub_add_cancel] at h3
    exact Int.natAbs_dvd.mp h3
  have h2 : n s₀ ∣ m s₀ := by
    obtain ⟨a, b, hb, ha, hk⟩ := h (n s₀).natAbs (Int.natAbs_pos.mpr hn)
    have hself : ((n s₀).natAbs : ℤ) ∣ n s₀ := Int.natAbs_dvd.mpr dvd_rfl
    have h3 := dvd_sub hself (hk s₀)
    rw [sub_sub_cancel, _root_.mul_assoc] at h3
    have h4 : ((n s₀).natAbs : ℤ) ∣ b * m s₀ := ha.symm.dvd_of_dvd_mul_left h3
    have hbc : IsCoprime ((n s₀).natAbs : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hb.symm
    exact Int.natAbs_dvd.mp (hbc.dvd_of_dvd_mul_left h4)
  have heq : n s₀ = m s₀ := by
    have h5 := Int.natAbs_eq_of_dvd_dvd h1 h2
    rcases Int.natAbs_eq_natAbs_iff.mp h5 with h6 | h6
    · exact h6.symm
    · rw [h6] at hpos; nlinarith [mul_self_nonneg (m s₀)]
  intro s
  have hD : ∀ k : ℕ, 0 < k → (k : ℤ) ∣ n s * m s₀ - n s₀ * m s := by
    intro k hk
    obtain ⟨a, b, -, -, hks⟩ := h k hk
    have e : n s * m s₀ - n s₀ * m s
        = (n s - a * b * m s) * m s₀ - (n s₀ - a * b * m s₀) * m s := by ring
    rw [e]; exact dvd_sub ((hks s).mul_right _) ((hks s₀).mul_right _)
  have hD0 : n s * m s₀ - n s₀ * m s = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd (hD _ (Nat.succ_pos (n s * m s₀ - n s₀ * m s).natAbs))
    rw [Int.abs_eq_natAbs]; push_cast; omega
  rw [heq] at hD0
  have h7 : n s * m s₀ = m s * m s₀ := by linarith
  exact mul_right_cancel₀ hm h7

theorem form_eq_div : ∀ (S : Type) (f f' : S → ℝ) (A : ℝ), 0 < A → (∀ s, ∃ n : ℤ, f' s = n) →
    (∀ k : ℕ, 0 < k → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ Nat.Coprime b k ∧ IsCoprime a (k : ℤ) ∧
      ∀ s, (∃ n : ℤ, (b : ℝ) / A * f s = n) ∧ ∃ n : ℤ, f' s - a * ((b : ℝ) / A * f s) = k * n) →
    (∃ s, f s ≠ 0 ∧ 0 < f s * f' s) → ∀ s, f' s = f s / A := by
  intro S f f' A hA hint hk hex
  have hF : ∀ s, ∃ n : ℤ, f s / A = n := by
    intro s
    apply int_of_coprime_denoms
    intro k hk0
    obtain ⟨a, b, hb, hc, -, hs⟩ := hk k hk0
    obtain ⟨n, hn⟩ := (hs s).1
    exact ⟨b, hb, hc, n, by rw [← hn]; ring⟩
  choose m hm using hF
  choose n hn using hint
  have hcore : ∀ k : ℕ, 0 < k → ∃ a : ℤ, ∃ b : ℕ, Nat.Coprime b k ∧ IsCoprime a (k : ℤ) ∧
      ∀ s, (k : ℤ) ∣ n s - a * b * m s := by
    intro k hk0
    obtain ⟨a, b, -, hc, ha, hs⟩ := hk k hk0
    refine ⟨a, b, hc, ha, fun s => ?_⟩
    obtain ⟨t, ht⟩ := (hs s).2
    refine ⟨t, ?_⟩
    have : ((n s - a * b * m s : ℤ) : ℝ) = ((k * t : ℤ) : ℝ) := by
      push_cast
      rw [← hn s, ← ht, ← hm s]; ring
    exact_mod_cast this
  obtain ⟨s₀, hf0, hpos⟩ := hex
  have hmR : ((m s₀ : ℤ) : ℝ) * (n s₀ : ℝ) = f s₀ * f' s₀ / A := by
    rw [← hm s₀, ← hn s₀]; ring
  have hposZ : 0 < m s₀ * n s₀ := by
    have : (0 : ℝ) < ((m s₀ * n s₀ : ℤ) : ℝ) := by
      push_cast; rw [hmR]; exact div_pos hpos hA
    exact_mod_cast this
  have hm0 : m s₀ ≠ 0 := by
    rintro h0; rw [h0, zero_mul] at hposZ; exact lt_irrefl _ hposZ
  intro s
  rw [hn s, hm s]
  exact_mod_cast int_core m n hcore s₀ hm0 hposZ s

end GlobalTheory.ConjArith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.MultPull

open GlobalTheory.TrueGeo.SmallSec GlobalTheory.FrameGlue.Pull

theorem isRatSec_pull_map {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
    (hη : j (genericPoint Y) ⤳ genericPoint X) {L : LB X} {r : L.ι → X.functionFieldˣ}
    (hr : IsRatSec L r) :
    IsRatSec (L.pull j) fun c => Units.map (fnMap j hη).toMonoidHom (r (c PUnit.unit)) := by
  intro c c' h
  have l : (L.pull j).U c ⊓ (L.pull j).U c' ≤ j ⁻¹ᵁ (L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have h₁ : genericPoint Y ∈ j ⁻¹ᵁ (L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit)) := l h
  have h₀ : genericPoint X ∈ L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit) :=
    (genericPoint_specializes _).mem_open (L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit)).isOpen h₁
  have e : (L.pull j).g c c' = res l (pullU j _ (L.g (c PUnit.unit) (c' PUnit.unit))) := by
    change ∏ _k : PUnit, _ = _
    exact (Fintype.prod_unique _).trans (zpow_one _)
  change fnMap j hη (r (c PUnit.unit) : X.functionField) =
    fnOf _ h ((L.pull j).g c c' : Γ(Y, (L.pull j).U c ⊓ (L.pull j).U c')) *
      fnMap j hη (r (c' PUnit.unit) : X.functionField)
  rw [hr _ _ h₀, map_mul, fnMap_fnOf j hη h₀ h₁, e]
  first
    | exact congrArg (· * _) (fnOf_resG l h _)
    | exact congrArg (· * _) (fnOf_resG l h _).symm

theorem ord_fnMap {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (j : Y ⟶ X) (hη : j (genericPoint Y) ⤳ genericPoint X) (y : Y)
    [IsIso (j.stalkMap y)] (f : X.functionField) :
    Scheme.ord (fnMap j hη f) y = Scheme.ord f (j y) := by
  let e : X.presheaf.stalk (j y) ≃+* Y.presheaf.stalk y :=
    (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv
  have he (a : X.presheaf.stalk (j y)) : e a = j.stalkMap y a := rfl
  have hc : Order.coheight y = Order.coheight (j y) := by
    have := ringKrullDim_eq_of_ringEquiv e
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at this
    exact_mod_cast this.symm
  by_cases hz : Order.coheight (j y) = 1
  swap
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one (hc ▸ hz), Scheme.ord_eq_zero_of_coheight_neq_one hz]
  have hz' : Order.coheight y = 1 := hc.trans hz
  have key (a : X.presheaf.stalk (j y)) (ha : a ≠ 0) :
      Scheme.ord (fnMap j hη (algebraMap _ X.functionField a)) y =
        Scheme.ord (algebraMap _ X.functionField a) (j y) := by
    have ha' : j.stalkMap y a ≠ 0 := by rw [← he]; exact (map_ne_zero_iff _ e.injective).2 ha
    rw [fnMap_algebraMap, ord_algebraMap hz' ha', ord_algebraMap hz ha, ← he]
    exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) (ord_map_ringEquiv e a)
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (j y)) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap _ X.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hf (by rw [← hab, map_zero, zero_div])
  have hfb : f * algebraMap _ X.functionField b = algebraMap _ X.functionField a := by
    rw [← hab, div_mul_cancel₀ _ hb']
  have h₁ := Scheme.ord_mul (x := j y) hf hb'
  have hfm : fnMap j hη f ≠ 0 := (map_ne_zero_iff _ (fnMap j hη).injective).2 hf
  have hbm : fnMap j hη (algebraMap _ X.functionField b) ≠ 0 :=
    (map_ne_zero_iff _ (fnMap j hη).injective).2 hb'
  have h₂ := Scheme.ord_mul (x := y) hfm hbm
  rw [← map_mul, hfb] at h₂
  rw [hfb] at h₁
  rw [key a ha0, key b hb0] at h₂
  omega

end GlobalTheory.MultPull

open GlobalTheory.MultPull GlobalTheory.TrueGeo.SmallSec in

theorem GlobalTheory.MultPull.exists_isRatSec_pull_mult : ∀ (G Y : Scheme.{0}) [IsIntegral G] [IsIntegral Y] [IsLocallyNoetherian G] [IsLocallyNoetherian Y] (j : G ⟶ Y), j (genericPoint G) = genericPoint Y → (∀ x : G, IsIso (j.stalkMap x)) → ∀ (M : LB Y) (hM : M.IsLB) (r : M.ι → Y.functionFieldˣ) (hr : IsRatSec M r), ∃ (r' : (M.pull j).ι → G.functionFieldˣ) (hr' : IsRatSec (M.pull j) r'), ∀ x : G, (divOfRatSec (LB.isLB_pull hM j) hr').mult x = (divOfRatSec hM hr).mult (j x) := by
  intro G Y _ _ _ _ j hj hiso M hM r hr
  have hη : j (genericPoint G) ⤳ genericPoint Y := hj ▸ specializes_rfl
  refine ⟨_, isRatSec_pull_map j hη hr, fun x => ?_⟩
  obtain ⟨c, hc⟩ := exists_chart (LB.isLB_pull hM j) x
  have hc' : j x ∈ M.U (c PUnit.unit) := Set.mem_iInter.1 hc PUnit.unit
  rw [((presents_divOfRatSec _ _).isEqn c x hc).mult_eq,
    ((presents_divOfRatSec hM hr).isEqn _ _ hc').mult_eq]
  have := hiso x
  exact ord_fnMap j hη x _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationsSameGenericFibreAgreeAtPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisations_same_genericFibre_agree_at_points : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) →
  ∀ (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)), Same ρ' ε' ρ₂ ε₂ (fun a => D.lab a) (algebraMap X₁.Ω₁ D.X.Ω₁) → R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) → ∀ (y₂ : R₂ →+* PadicAlgCl p), (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) →
  ∀ (K : Type) [Field K] (j : K →+* PadicAlgCl p) (f' : R' →+* K), j.comp f' = y₀ → (∀ a ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))), D.X.M.val (gPt p ≫ y) a ∈ j.range) →
  ∀ (A₁ : PolAV (Sp K)) (a₁ : A₁.A.left ⟶ ρ'.P.A.left), IsGrpPullback A₁.A ρ'.P.A (spMap f') a₁ → LBIso A₁.L (ρ'.P.L.pull a₁) →
  ∃ (f₂ : R₂ →+* K) (φ₂ : A₁.A.left ⟶ ρ₂.P.A.left), j.comp f₂ = y₂ ∧ IsGrpPullback A₁.A ρ₂.P.A (spMap f₂) φ₂ ∧ LBIso A₁.L (ρ₂.P.L.pull φ₂) ∧
    (∀ (x : Sp (PadicAlgCl p) ⟶ A₁.A.left) (a : X₁.S.Gam), x ≫ A₁.A.hom = spMap j → (x ≫ φ₂ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ x ≫ a₁ = spMap y₀ ≫ (ρ'.pt a).left)) ∧
    (∀ (x x' : Sp (PadicAlgCl p) ⟶ A₁.A.left) (E : Matrix (Fin 8) (Fin 8) ℤ), x ≫ A₁.A.hom = spMap j → x' ≫ A₁.A.hom = spMap j → (x' ≫ φ₂ = x ≫ φ₂ ≫ (ε₂ E).left ↔ x' ≫ a₁ = x ≫ a₁ ≫ (ε' E).left)) := by
  first | exact @GlobalTheory.Poinc.special_transport | exact GlobalTheory.Poinc.special_transport | (intros; apply GlobalTheory.Poinc.special_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemSectionGeneratesFieldFibresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisedThetaSystem_section_generates_field_fibres : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K), IsGenSec ρ.P.A ρ.P.L _ (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) := by
  first | exact @GlobalTheory.UMin.isGenSec_real_pull | exact GlobalTheory.UMin.isGenSec_real_pull | (intros; apply GlobalTheory.UMin.isGenSec_real_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemThetaConstantNegEvenUpToRoot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.ThetaParity

theorem exists_rigPull_inv {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (hrig : rig.IsGen) :
    haveI := P.isAb.comm
    ∃ w : LB.Iso P.L (P.L.pull (ι[P.A]).left), GlobalTheory.OneBasis.RigPull P.A P.A (𝟙 S) (ι[P.A]).left w rig rig := by
  haveI := P.isAb.comm
  obtain ⟨u, hu⟩ := GlobalTheory.exists_gen_neg_of_sym GlobalTheory.globalFns_holds P.isAb P.isLB P.sym
  obtain ⟨s, hs, hr⟩ := GlobalTheory.AbPackage.exists_rigidified_sym P.isLB u hu
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨he, w, hw, hm⟩ := GlobalTheory.SymmetricBundle.isSymmetric_of_gen L s hs hr
  refine ⟨w, GlobalTheory.SabBaseChange.isGrpPullback_inv P.A, hw, hrig, ?_⟩
  exact (maps_iff w (K := PUnit) (fun _ => eSec P.A) (fun _ => eSec P.A) (fun _ => 1) rig rig (𝟙 _) _
    (fun j => rigPull_le _ (𝟙 _) he P.L j) (fun _ => rfl)).1 hm

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem pt_neg {S : ThetaSys o Ω} (ρ : S.Real) (a : S.Gam) : ρ.pt (-a) = (ρ.pt a)⁻¹ := by
  have h0 : ρ.pt 0 = 1 := by
    have h := ρ.pt_add 0 0
    rw [add_zero] at h
    have h' : ρ.pt 0 * ρ.pt 0 = ρ.pt 0 * 1 := by rw [_root_.mul_one]; exact h.symm
    exact mul_left_cancel h'
  have h := ρ.pt_add (-a) a
  rw [neg_add_cancel, h0] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem pt_neg_left {S : ThetaSys o Ω} (ρ : S.Real) (a : S.Gam) :
    haveI := ρ.P.isAb.comm
    (ρ.pt (-a)).left ≫ (ι[ρ.P.A]).left = 𝟙 _ ≫ (ρ.pt a).left := by
  rw [pt_neg, Category.id_comp, ← Over.comp_left]
  congr 1
  simp [Hom.inv_def]

theorem key_fn (S : ThetaSys o Ω) (ρ : S.Real) :
    ∃ c₀ : Γ((baseOver (Sp S.R)).left, ⊤), ∀ a, ∃ d : Γ((baseOver (Sp S.R)).left, ⊤),
      d ^ ((S.r * S.N) ^ 2) = 1 ∧ c₀ * fn (⟨S.th (-a), S.th_mem (-a)⟩ : S.R) = d * fn (⟨S.th a, S.th_mem a⟩ : S.R) := by
  haveI := ρ.P.isAb.comm
  obtain ⟨w, R⟩ := exists_rigPull_inv ρ.P ρ.rig ρ.rig_gen
  have hφ : (ι[ρ.P.A]).left ≫ ρ.P.A.hom = ρ.P.A.hom ≫ 𝟙 _ := by rw [Over.w, Category.comp_id]
  obtain ⟨s', hs', -⟩ := GlobalTheory.OneBasis.Calc.existsUnique_thru (k := 1) (T := baseOver (Sp S.R))
    (T' := baseOver (Sp S.R)) hφ R.2.1 ρ.P.isLB ρ.P.isLB (h := 𝟙 _) (by simp) ρ.th₁
  obtain ⟨c, hc, -⟩ := ρ.th₁_basis s'
  refine ⟨c 0, fun a => ?_⟩
  obtain ⟨e', he', He⟩ := GlobalTheory.OneBasis.TabMap.frame_move R (h := 𝟙 _) (pt_neg_left ρ a) (ρ.fr_tors a)
  have v₁ := He 1 ρ.th₁ s' (fn (⟨S.th a, S.th_mem a⟩ : S.R)) hs' (fun z J hJ => by
    have := GlobalTheory.FrameMove.sval_valueAt (ρ.th_val a) (𝟙 _) hJ
    rw [Category.id_comp] at this
    rw [GlobalTheory.FrameMove.val_powFrame]
    simpa using this)
  have v₂ := (GlobalTheory.OneBasis.Calc.cmb_iff ρ.P.isLB (k := 1) (fun _ => ρ.th₁) c s').1 hc
  obtain ⟨d, hd⟩ := GlobalTheory.AbPackage.exists_unit_ratio ρ.P.isLB he'.2.1 (ρ.fr_tors (-a)).2.1
  obtain ⟨α, hα⟩ := GlobalTheory.EmbLocal.exists_mulPull GlobalTheory.globalFns_holds ρ.P (S.r * S.N) (baseOver (Sp S.R))

  refine ⟨(d : Γ((baseOver (Sp S.R)).left, ⊤)), ?_, ?_⟩
  · have hu : d ^ ((S.r * S.N) ^ 2) = 1 := by
      apply Units.ext
      apply fn_ext
      intro z _
      obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' ρ.P.isLB z
      have t₁ := GlobalTheory.ThetaCompare.torsFrame_pow GlobalTheory.globalFns_holds ρ.P hα he' hJ
      have t₂ := GlobalTheory.ThetaCompare.torsFrame_pow GlobalTheory.globalFns_holds ρ.P hα (ρ.fr_tors (-a)) hJ
      have e := hd _ (𝟙 _) z J hJ
      rw [e, mul_pow, ← t₂, _root_.mul_assoc] at t₁
      have g := mul_eq_right.1 t₁
      rw [gs_unit (𝟙 _) z ⊤ trivial, gs_unit (𝟙 _) z ⊤ trivial, map_pow, g, map_one]
    rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  · apply fn_ext
    intro z _
    obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' ρ.P.isLB z
    have a₁ := v₁ z J hJ
    have a₂ := v₂ _ (ptSecT ρ.P.A (ρ.pt (-a))).left z J hJ
    have a₃ := GlobalTheory.FrameMove.sval_valueAt (ρ.th_val (-a)) (𝟙 _) hJ
    have a₄ := hd _ (𝟙 _) z J hJ
    rw [Category.id_comp] at a₃
    rw [gs_mul _ z ⊤ trivial, gs_mul _ z ⊤ trivial]

    simp only [GlobalTheory.FrameGen.sv, Fin.sum_univ_one] at a₂
    have f₁ : (ptSecT ρ.P.A (ρ.pt (-a))).left ≫ (fst (baseOver (Sp S.R)) ρ.P.A).left = 𝟙 _ := by
      rw [← Over.comp_left, ptSecT, lift_fst, Over.id_left]
    rw [f₁, ← GlobalTheory.FrameGen.gs_top, a₃] at a₂
    have hp : ∀ u : ((baseOver (Sp S.R)).left.presheaf.stalk z)ˣ, u ^ ((1 : ℕ) : ℤ) = u := fun u => by simp
    rw [GlobalTheory.FrameMove.val_powFrame, hp, a₄, Units.val_mul] at a₁
    have e := a₂.symm.trans a₁
    rw [← gs_unit (𝟙 _) z ⊤ trivial d] at e
    refine (Units.mul_left_inj (Geo.Tor.val (ρ.fr (-a)) (𝟙 _) z J)).1 ?_
    linear_combination e

theorem key (S : ThetaSys o Ω) (ρ : S.Real) :
    ∃ C : Ω, ∀ a, ∃ D : Ω, D ^ ((S.r * S.N) ^ 2) = 1 ∧ C * S.th (-a) = D * S.th a := by
  obtain ⟨c₀, h⟩ := key_fn S ρ
  let φ : Γ((baseOver (Sp S.R)).left, ⊤) →+* Ω :=
    S.R.val.toRingHom.comp (Scheme.ΓSpecIso (CommRingCat.of S.R)).hom.hom
  have hφ : ∀ x : S.R, φ (fn x) = x := fun x => by simp [φ, fn]
  refine ⟨φ c₀, fun a => ?_⟩
  obtain ⟨d, hd, e⟩ := h a
  refine ⟨φ d, by rw [← map_pow, hd, map_one], ?_⟩
  have := congrArg φ e
  rwa [map_mul, map_mul, hφ, hφ] at this

theorem odd_rN (S : ThetaSys o Ω) (ρ : S.Real) : Odd ((S.r * S.N) ^ 2) := by
  obtain ⟨j, -, hj⟩ := ρ.r_eq
  rw [hj, ρ.N_eq]
  exact ((ρ.n_odd.pow).mul ((ρ.n_odd.pow).pow)).pow

end GlobalTheory.ThetaParity

namespace GlobalTheory.ThetaParity

theorem theta_neg : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (ρ : S.Real) (a : S.Gam), ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a := by
  intro o Ω _ _ _ _ S ρ a
  obtain ⟨C, hC⟩ := key S ρ
  have hodd := odd_rN S ρ
  set m := (S.r * S.N) ^ 2 with hm
  obtain ⟨x, hx⟩ := S.th_ne
  obtain ⟨D₁, hD₁, e₁⟩ := hC x
  obtain ⟨D₂, hD₂, e₂⟩ := hC (-x)
  rw [neg_neg] at e₂
  have hm0 : m ≠ 0 := hodd.pos.ne'
  have nz : ∀ D : Ω, D ^ m = 1 → D ≠ 0 := fun D h h0 => by
    rw [h0, zero_pow hm0] at h; exact zero_ne_one h
  have hx' : S.th (-x) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at e₁; exact (mul_ne_zero (nz _ hD₁) hx) e₁.symm
  have hC0 : C ≠ 0 := by
    intro h0; rw [h0, zero_mul] at e₁; exact (mul_ne_zero (nz _ hD₁) hx) e₁.symm
  have hC2 : C ^ 2 = D₁ * D₂ := by
    have h2 : C ^ 2 * (S.th (-x) * S.th x) = D₁ * D₂ * (S.th (-x) * S.th x) := by
      linear_combination (C * S.th x) * e₁ + (D₁ * S.th x) * e₂
    exact mul_right_cancel₀ (mul_ne_zero hx' hx) h2
  have hCi : C⁻¹ ^ (2 * m) = 1 := by
    rw [inv_pow, pow_mul, hC2, mul_pow, hD₁, hD₂, _root_.one_mul, inv_one]
  obtain ⟨D, hD, e⟩ := hC a
  obtain ⟨k, hk⟩ := hodd
  refine ⟨C⁻¹ ^ m, C⁻¹ ^ (m + 1) * D, ?_, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, hCi]
  · rw [mul_pow, hD, _root_.mul_one, ← pow_mul, show (m + 1) * m = 2 * m * (k + 1) by rw [hk]; ring, pow_mul, hCi,
      one_pow]
  · have e' : S.th (-a) = C⁻¹ * D * S.th a := by
      rw [_root_.mul_assoc, ← e, ← _root_.mul_assoc, inv_mul_cancel₀ hC0, _root_.one_mul]
    rw [e', ← _root_.mul_assoc, ← pow_add, show m + (m + 1) = 2 * m + 1 by ring, pow_succ, hCi, _root_.one_mul]

end GlobalTheory.ThetaParity
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RechartingsThetaSetupSameGeometricFibreAtTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rechartings_thetaSetup_same_geometric_fibre_at_trait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) → R' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X.M.val (gPt p ≫ c.y) a) → ∀ (c₁ : X.Ω₁) (hc₁ : c₁ ≠ 0) (R'' : Subalgebra X.o₁ X.Ω₁) (fg₁ : R''.FG) (frac₁ : ∀ x : X.Ω₁, ∃ a ∈ R'', ∃ b ∈ R'', x = a / b) (hth₁ : ∀ x, c₁ * X.S.th x ∈ R'') (hev₁ : ∀ x k, c₁ * X.S.ev x k ∈ R'') (ρ'' : (X.S.rechart c₁ hc₁ R'' fg₁ frac₁ hth₁ hev₁).Real) (ε'' : Matrix (Fin 8) (Fin 8) ℤ → (ρ''.P.A ⟶ ρ''.P.A)), Same X.ρ ε ρ'' ε'' (fun x => x) (RingHom.id _) → R'' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₁ : R'' →+* PadicAlgCl p), (∀ a : R'', y₁ a = X.M.val (gPt p ≫ c.y) a) → ∀ (u : ρ'.UTest p y₀) (u' : ρ''.UTest p y₁), ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u'.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧ IsGrpPullback P₀.A u'.A.A (spMap (algebraMap (FractionRing u'.V) (PadicAlgCl p))) a' ∧ LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u'.A.L.pull a') ∧ (∀ b : X.S.Gam, ∃ (w : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u'.V) (PadicAlgCl p) ⟶ u'.A.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt b).left ∧ x'.left ≫ u'.φ = spMap y₁ ≫ (ρ''.pt b).left) ∧ ∀ (E : Matrix (Fin 8) (Fin 8) ℤ) (w w₂ : Sp (PadicAlgCl p) ⟶ P₀.A.left), w ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ a ≫ u.φ = w ≫ a ≫ u.φ ≫ (ε' E).left → w₂ ≫ a' ≫ u'.φ = w ≫ a' ≫ u'.φ ≫ (ε'' E).left := by
  first | exact @GlobalTheory.Poinc.Spread.main | exact GlobalTheory.Poinc.Spread.main | (intros; apply GlobalTheory.Poinc.Spread.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceCoreOfSumPoint
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.RefSum.primeSum_add_pair {S : Finset ℕ} {e : ℕ → ℝ} {s : ℝ} (h : PrimeSum S e s) (g : Fin 2 → ℕ)
    (hg : ∀ k, (g k).Prime) :
    PrimeSum (S ∪ Finset.univ.image g) (fun q => e q + if q ∈ Finset.univ.image g then 1 else 0)
      (s + (Real.log (g 0) + Real.log (g 1))) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun q hq => ?_, fun q => add_nonneg (h2 q) (by split_ifs <;> norm_num), fun q hq => ?_, ?_⟩
  · rcases Finset.mem_union.1 hq with hq | hq
    · exact h1 q hq
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hq
      exact hg k
  · rw [Finset.mem_union, not_or] at hq
    simp only [h3 q hq.1, if_neg hq.2, add_zero]
  · have a : ∑ q ∈ S ∪ Finset.univ.image g, e q * Real.log q = ∑ q ∈ S, e q * Real.log q :=
      (Finset.sum_subset Finset.subset_union_left fun q _ hq => by rw [h3 q hq, zero_mul]).symm
    have b : ∑ q ∈ S ∪ Finset.univ.image g, (if q ∈ Finset.univ.image g then (1 : ℝ) else 0) * Real.log q =
        ∑ q ∈ Finset.univ.image g, Real.log q := by
      rw [← Finset.sum_subset Finset.subset_union_right fun q _ hq => by rw [if_neg hq, zero_mul]]
      exact Finset.sum_congr rfl fun q hq => by rw [if_pos hq, one_mul]
    have c : ∑ q ∈ Finset.univ.image g, Real.log (q : ℕ) ≤ ∑ k : Fin 2, Real.log (g k) :=
      Finset.sum_image_le_of_nonneg (f := fun q : ℕ => Real.log q) fun q _ => Real.log_natCast_nonneg q
    rw [Fin.sum_univ_two] at c
    simp only [add_mul, Finset.sum_add_distrib]
    linarith

theorem GlobalTheory.RefSum.refCore_of_sumPt : Size → SumPt → RefCore := by
  intro hS hSum
  refine Closed.imp (Closed.and hSum (Closed.and (GlobalTheory.T.quotient_weight_gap_bounds hS) (GlobalTheory.T.jet_number_quotient_bounds hS))) ?_
  rintro eps Fm CH - ⟨⟨C1, hC1, h1⟩, ⟨C2, -, h2⟩, C3, hC3, h3⟩
  refine ⟨C1 + C3, add_nonneg hC1 hC3, (h1.and (h2.and h3)).imp fun x0 h x hx hle ι p hp i hi u1 hu => ?_⟩
  obtain ⟨k1, k2, k3⟩ := h x hx hle ι p hp
  obtain ⟨S, e, s, hP, hs, hO⟩ := k1 i hi u1 hu
  obtain ⟨-, -, -, -, -, -, hD, hL, -⟩ := k2 i hi u1 hu
  obtain ⟨hJ, hr, hg⟩ := k3 i hi u1 hu
  have hI : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨by omega, hi.le⟩
  refine ⟨_, _, _, primeSum_add_pair hP (Fm.D x ι).host.g (Fm.D x ι).host.g_prime, by rw [mul_add, add_mul]; exact add_le_add hs hg,
    fun q hq => ?_⟩
  by_cases hq' : q ∈ Finset.univ.image (Fm.D x ι).host.g
  · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hq'
    refine (GlobalTheory.T.supLatticeReferenceExponent_thetaWeight_level_le_one _ p.T.toCore p.fw.laws.toLawsM (Fm.ex x hx ι).errX _ hI _ _ _ hD hL sum_le_nCol hr hJ k).trans
      (EReal.coe_le_coe_iff.2 ?_)
    simp only [if_pos hq']
    linarith [hP.2.1 ((Fm.D x ι).host.g k)]
  · haveI := Fact.mk hq
    have hne : ∀ k, q ≠ (Fm.D x ι).host.g k := fun k h => hq' (Finset.mem_image.2 ⟨k, Finset.mem_univ _, h.symm⟩)
    refine (GlobalTheory.T.baseLocusExponent_le_oscillation_nonTypePrime _ p.T.toCore p.fw.laws.toLawsM (Fm.ex x hx ι).errX _ hI _ _ _ hD hL sum_le_nCol hr hJ q hne _
      (hO q hne)).trans (EReal.coe_le_coe_iff.2 ?_)
    simp only [if_neg hq', add_zero, le_refl]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatingConstantMemTraitFractionFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relatingConstant_mem_traitFractionField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (c : F), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → (∃ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (_ : p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α) (_ : p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _))) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J ∧ sval σ p z J ≠ 0) → ∃ x : FractionRing W, algebraMap (FractionRing W) F x = c := by
  first | exact @GlobalTheory.Mum.RatConst.main | exact GlobalTheory.Mum.RatConst.main | (intros; apply GlobalTheory.Mum.RatConst.main <;> assumption)
end

