import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ParabolicPointMembership
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0104
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0023
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0016
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0108
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0080
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0083
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0081
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0260

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTraceOne
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership GlobalTheory.QuadSubfield GlobalTheory.PlaceComponents

namespace GlobalTheory.ApproxIdem

theorem improve {O F : Type*} [CommRing O] [NormedField F] (f g : O →+* F) (hf : ∀ a, ‖f a‖ ≤ 1)
    (hg : ∀ a, ‖g a‖ ≤ 1) (r : ℝ) (e : O) (h1 : ‖f e - 1‖ ≤ r) (h2 : ‖g e‖ ≤ r) (m : ℕ) :
    ∃ ε : O, ‖f ε - 1‖ ≤ r ^ m ∧ ‖g ε‖ ≤ r ^ m := by
  refine ⟨1 - (1 - e ^ m) ^ m, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow 1 e m
    rw [one_pow] at hc
    rw [hc]
    have : f (1 - ((1 - e) * c) ^ m) - 1 = -((-(f e - 1)) * f c) ^ m := by
      simp only [map_sub, map_one, map_pow, map_mul]; ring
    rw [this, norm_neg, norm_pow, norm_mul, norm_neg]
    refine pow_le_pow_left₀ (by positivity) ?_ m
    exact (mul_le_of_le_one_right (norm_nonneg _) (hf c)).trans h1
  · obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow 1 (1 - e ^ m) m
    rw [one_pow, sub_sub_cancel] at hc
    rw [hc, map_mul, norm_mul, map_pow, norm_pow]
    exact (mul_le_of_le_one_right (by positivity) (hg c)).trans (pow_le_pow_left₀ (norm_nonneg _) h2 m)

theorem dichotomy {p : ℕ} [Fact p.Prime] (a b : ℂ_[p]) (k n : ℤ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hs : a + b = 1 + p * k) (hp : a * b = p * n) :
    (‖a - 1‖ ≤ (p : ℝ)⁻¹ ∧ ‖b‖ ≤ (p : ℝ)⁻¹) ∨ (‖b - 1‖ ≤ (p : ℝ)⁻¹ ∧ ‖a‖ ≤ (p : ℝ)⁻¹) := by
  have hpn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    have h : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
    rw [h, norm_algebraMap', Padic.norm_p]
  have hz : ∀ z : ℤ, ‖(p : ℂ_[p]) * z‖ ≤ (p : ℝ)⁻¹ := fun z => by
    rw [norm_mul, hpn]
    exact mul_le_of_le_one_right (by positivity) (IsUltrametricDist.norm_intCast_le_one _ z)
  have hlt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have key : ∀ a b : ℂ_[p], a + b = 1 + p * k → a * b = p * n → ‖a‖ = 1 →
      ‖a - 1‖ ≤ (p : ℝ)⁻¹ ∧ ‖b‖ ≤ (p : ℝ)⁻¹ := fun a b hs hp h => by
    have h2 : ‖b‖ ≤ (p : ℝ)⁻¹ := by
      have := hz n
      rwa [← hp, norm_mul, h, one_mul] at this
    refine ⟨?_, h2⟩
    have : a - 1 = (p : ℂ_[p]) * k + -b := by linear_combination hs
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hz k) (by rwa [norm_neg]))
  rcases ha.eq_or_lt with h | h
  · exact Or.inl (key a b hs hp h)
  rcases hb.eq_or_lt with h' | h'
  · exact Or.inr (key b a (by rw [add_comm, hs]) (by rw [mul_comm, hp]) h')
  exfalso
  have h1 : (1 : ℂ_[p]) = (a + b) + -((p : ℂ_[p]) * k) := by linear_combination -hs
  have h2 : ‖(1 : ℂ_[p])‖ < 1 := by
    rw [h1]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h h')
    · rw [norm_neg]; exact (hz k).trans_lt hlt
  simp at h2

theorem exists_trace_one (D : D7) (p : ℕ) [Fact p.Prime] (h : Formalism.L2.Ker.SplitK D p) :
    ∃ (e : 𝓞 D.host.K) (k n : ℤ), (e : D.host.K) + conjK D e = 1 + p * k ∧ (e : D.host.K) * conjK D e = p * n := by
  obtain ⟨-, σ, θ, hσ, hθ, hσθ, -, hint, -⟩ := quadratic_subfield D
  have e : conjK D θ = -θ := (Subtype.ext (hσ θ).symm : conjK D θ = σ θ).trans hσθ
  by_cases h2 : p = 2
  · subst h2
    have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
    obtain ⟨m, hm⟩ : ∃ m : ℕ, D.host.d + 1 = 8 * m := ⟨(D.host.d + 1) / 8, by omega⟩
    have hm' : (D.host.d : D.host.K) + 1 = 8 * (m : D.host.K) := by exact_mod_cast hm
    refine ⟨⟨(1 + θ) / 2, hint⟩, 0, m, ?_, ?_⟩
    · change (1 + θ) / 2 + conjK D ((1 + θ) / 2) = _
      rw [map_div₀, map_add, map_one, map_ofNat, e]
      push_cast; ring
    · change (1 + θ) / 2 * conjK D ((1 + θ) / 2) = _
      rw [map_div₀, map_add, map_one, map_ofNat, e]
      push_cast
      linear_combination (-1 / 4 : D.host.K) * hθ + (1 / 4 : D.host.K) * hm'
  · have hj : jacobiSym (-(D.host.d : ℤ)) p = 1 := h.resolve_left h2
    obtain ⟨a, ha⟩ := ZMod.isSquare_of_jacobiSym_eq_one hj
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [← jacobiSym.legendreSym.to_jacobiSym] at hj
      rw [(legendreSym.eq_zero_iff p _).2 (by simpa using ha)] at hj
      exact zero_ne_one hj
    have h20 : (2 : ZMod p) ≠ 0 := by
      intro h0
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
      rw [ZMod.natCast_eq_zero_iff] at this
      exact h2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
    obtain ⟨A, rfl⟩ := ZMod.intCast_surjective a
    obtain ⟨T, hT⟩ := ZMod.intCast_surjective (2 * (A : ZMod p))⁻¹
    obtain ⟨k, hk⟩ : (p : ℤ) ∣ T * (2 * A) - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hT, inv_mul_cancel₀ (mul_ne_zero h20 ha0), sub_self]
    obtain ⟨n, hn⟩ : (p : ℤ) ∣ A * A + D.host.d := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast at ha ⊢
      rw [← ha]; ring
    have hθi : IsIntegral ℤ θ := by
      have : θ = (1 + θ) / 2 + (1 + θ) / 2 - 1 := by ring
      rw [this]
      exact (hint.add hint).sub isIntegral_one
    have hk' : (T : D.host.K) * (2 * A) - 1 = p * k := by exact_mod_cast hk
    have hn' : (A : D.host.K) * A + D.host.d = p * n := by exact_mod_cast hn
    have hI : IsIntegral ℤ ((T : D.host.K) * (A + θ)) :=
      (isIntegral_algebraMap (R := ℤ) (x := T)).mul ((isIntegral_algebraMap (R := ℤ) (x := A)).add hθi)
    refine ⟨⟨(T : D.host.K) * (A + θ), hI⟩, k, T ^ 2 * n, ?_, ?_⟩
    · change (T : D.host.K) * (A + θ) + conjK D ((T : D.host.K) * (A + θ)) = _
      rw [map_mul, map_add, map_intCast, map_intCast, e]
      linear_combination hk'
    · change (T : D.host.K) * (A + θ) * conjK D ((T : D.host.K) * (A + θ)) = _
      rw [map_mul, map_add, map_intCast, map_intCast, e]
      push_cast
      linear_combination (T : D.host.K) ^ 2 * hn' - (T : D.host.K) ^ 2 * hθ

theorem exists_isIdem : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), Formalism.L2.Ker.SplitK D p →
    ∀ m : ℕ, ∃ ε : 𝓞 D.host.K, IsIdem D lam m ε := by
  intro D p _ lam h m
  obtain ⟨e, k, n, hs, hp⟩ := exists_trace_one D p h
  have hs' := congrArg (homP D lam) hs
  have hp' := congrArg (homP D lam) hp
  simp only [map_add, map_mul, map_one, map_natCast, map_intCast, homP_conjK] at hs' hp'
  have hex : ∃ e : 𝓞 D.host.K, ‖homP D lam e - 1‖ ≤ (p : ℝ)⁻¹ ∧ ‖homPbar D lam e‖ ≤ (p : ℝ)⁻¹ := by
    rcases dichotomy _ _ k n (norm_int_le D _ e) (norm_int_le D _ e) hs' hp' with h | h
    · exact ⟨e, h⟩
    · exact ⟨conjO D e, by rwa [coe_conjO, homP_conjK, homPbar_conjK]⟩
  obtain ⟨e₁, h1, h2⟩ := hex
  obtain ⟨ε, hε⟩ := improve ((homP D lam).comp (algebraMap (𝓞 D.host.K) D.host.K))
    ((homPbar D lam).comp (algebraMap (𝓞 D.host.K) D.host.K)) (norm_int_le D (homP D lam)) (norm_int_le D (homPbar D lam)) _ e₁ h1 h2 m
  refine ⟨ε, (isIdem_iff D lam m ε).2 ?_⟩
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  exact hε

end GlobalTheory.ApproxIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.JetsOnCopiesOfCompatibleFrames
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowJets

theorem exists_position_basis {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {n r : ℕ} (xe : X' ≃+ (Fin n → X))
    (b : Module.Basis (Fin r) ℤ X) :
    ∃ (r' : ℕ) (b' : Module.Basis (Fin r') ℤ X'), ∀ k, ∃ i j, xe (b' k) = Pi.single i (b j) := by
  classical
  let B : Module.Basis (Σ _ : Fin n, Fin r) ℤ (Fin n → X) := Pi.basis fun _ => b
  refine ⟨_, (B.map xe.toIntLinearEquiv.symm).reindex (Fintype.equivFin _), fun k => ?_⟩
  refine ⟨((Fintype.equivFin (Σ _ : Fin n, Fin r)).symm k).1, ((Fintype.equivFin (Σ _ : Fin n, Fin r)).symm k).2, ?_⟩
  simp [B, Pi.basis_apply]

theorem sum_single_add {X : Type} [AddCommGroup X] {n : ℕ} (Q : X → ℤ) (i : Fin n) (x : X) (w : Fin n → X) :
    ∑ k, Q ((Pi.single i x + w : Fin n → X) k) = ∑ k, Q (w k) + (Q (x + w i) - Q (w i)) := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ (fun k => Q (w k)) (Finset.mem_univ i),
    Finset.sum_congr rfl (g := fun k => Q (w k)) fun k hk => by
      rw [Pi.add_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hk), zero_add]]
  simp only [Pi.add_apply, Pi.single_eq_same]
  ring

theorem exists_basis_bounds {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {n r : ℕ} (xe : X' ≃+ (Fin n → X))
    (Q : X → ℤ) (h0 : Q 0 = 0) (hQ : ∀ x, 0 ≤ Q x) (Φ M0 : ℝ) (b : Module.Basis (Fin r) ℤ X)
    (hΦ : ∀ j, (Q (b j) : ℝ) ≤ Φ) (hM : ∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) :
    ∃ (r' : ℕ) (b' : Module.Basis (Fin r') ℤ X'), (∀ j, (sumQ xe Q (b' j) : ℝ) ≤ Φ) ∧
      ∀ j w, |((sumQ xe Q (b' j + w) - sumQ xe Q (b' j) - sumQ xe Q w : ℤ) : ℝ)| ≤ max M0 0 * sumQ xe Q w := by
  obtain ⟨r', b', hb⟩ := exists_position_basis xe b
  have e1 : ∀ k i j, xe (b' k) = Pi.single i (b j) → sumQ xe Q (b' k) = Q (b j) := fun k i j h => by
    have := sum_single_add Q i (b j) 0
    simpa [sumQ, h, h0] using this
  refine ⟨r', b', fun k => ?_, fun k w => ?_⟩
  · obtain ⟨i, j, h⟩ := hb k
    rw [e1 k i j h]
    exact hΦ j
  · obtain ⟨i, j, h⟩ := hb k
    have e2 : sumQ xe Q (b' k + w) = sumQ xe Q w + (Q (b j + xe w i) - Q (xe w i)) := by
      unfold sumQ
      rw [map_add, h]
      exact sum_single_add Q i (b j) (xe w)
    have e3 : sumQ xe Q (b' k + w) - sumQ xe Q (b' k) - sumQ xe Q w = Q (b j + xe w i) - Q (b j) - Q (xe w i) := by
      rw [e1 k i j h, e2]; ring
    have e4 : Q (xe w i) ≤ sumQ xe Q w :=
      Finset.single_le_sum (f := fun k => Q (xe w k)) (fun k _ => hQ _) (Finset.mem_univ i)
    rw [e3]
    refine (hM j _).trans (mul_le_mul (le_max_left _ _) (by exact_mod_cast e4) (by exact_mod_cast hQ _) (le_max_right _ _))

theorem jets_on_copies : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → JetsOnCopiesCompatibleFrames := by
  intro L1 L2 L4 TB E _ _ _ H Dw l Xo c inst hstar
  obtain rfl : inst = H.starRing := starSt E H inst hstar
  letI := H.starRing
  intro T io y _ C htr P ϖ hϖ Q hQ Φ M0 r b hΦ0 hΦ hM n _ D' A' G' _ _ pD pA pG U' PU F _ _ _ _ _ v hv q D hq hD f hf
  choose f₀ hf₀ using hf
  obtain ⟨τ, hτ, htrunc, hgerm⟩ := frameNSt_holds E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hu := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n (chD C.ch) pG C.xT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C)
  obtain ⟨r', b', h1, h2⟩ := exists_basis_bounds pD.xe Q (Q_zero hϖ P.D hQ) (RoundingSumAlt.Q_nonneg hϖ hQ) Φ M0 b hΦ hM
  have hD' : (D : ℝ) * max M0 0 < q := by
    rcases le_total M0 0 with h | h
    · rw [max_eq_right h, mul_zero]
      exact_mod_cast (by omega : 0 < q)
    · rwa [max_eq_left h]
  obtain ⟨s, σ', g, lam, a1, a2, a3, a4, a5, a6⟩ := GlobalTheory.UnifJets.jets L1 L2 L4 TB T.V ϖ hϖ D' A' G' U' (Fin n × Fin (chD C.ch))
    (zV pG C.xT) hu τ hτ (htrunc htr) (sumQ pD.xe Q) (GlobalTheory.QBox.main T.V ϖ hϖ n P.D D' pD Q hQ) Φ (max M0 0) r' b' hΦ0
    (le_max_right _ _) h1 h2 F v hv q D hq hD' (fun e => f₀ e)
  refine ⟨s, σ', g, lam, a1, a2, (hgerm F q σ' g).2 a3, a4, a5, fun e he => ?_⟩
  rw [a6 e he, map_smul, MvPowerSeries.coeff_map, ← hf₀ e, smul_eq_mul, ← IsScalarTower.algebraMap_apply]
  rfl

end GlobalTheory.PowJets
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormAdjointCompIsometryEquiv
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem norm_adjoint_comp_isometryEquiv {V₁ V₂ V₃ : Type} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
    [CompleteSpace V₁] [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] [CompleteSpace V₂]
    [NormedAddCommGroup V₃] [InnerProductSpace ℂ V₃] [CompleteSpace V₃]
    (A : V₂ →L[ℂ] V₁) (φ : V₃ ≃ₗᵢ[ℂ] V₂) (v : V₁) :
    ‖ContinuousLinearMap.adjoint (A.comp (φ : V₃ →L[ℂ] V₂)) v‖ = ‖ContinuousLinearMap.adjoint A v‖ := by
  rw [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm]
  simp

theorem exists_wigMap_pair_of_isType : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] (Vm : Type) [NormedAddCommGroup Vm] [InnerProductSpace ℂ Vm] [FiniteDimensional ℂ Vm] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (πp : Mx k r → (Vp →L[ℂ] Vp)) (πm : Mx k r → (Vm →L[ℂ] Vm)) (u up um : ℕ → ℝ) (l n₀ : ℕ) (b : ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → (∀ i ∈ Finset.Icc 1 (k - 1), ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1) → 1 ≤ l → l < k → 2 * (n₀ : ℝ) + 1 ≤ u l - u (l + 1) → (∀ i ∈ Finset.Icc 1 k, |u i| ≤ b) → (n₀ : ℝ) ≤ b → 1 ≤ b → IsType k r z πp up → IsType k r z πm um → (∀ i ∈ Finset.Icc 1 k, up i = if i = l + 1 then u i + (n₀ : ℝ) else u i) → (∀ i ∈ Finset.Icc 1 k, um i = if i = l then u i - (n₀ : ℝ) else u i) → ∃ (Ap : (Fin (2 * r + k + 1) → ℂ) → (Vp →L[ℂ] V)) (Am : (Fin (2 * r + k + 1) → ℂ) → (Vm →L[ℂ] V)), GlobalTheory.WigSh.WigMap k r z πp π n₀ Ap ∧ GlobalTheory.WigSh.WigMap k r z πm π n₀ Am ∧ ∀ ω, inWb k r ω → herm (Hpk k r) ω z = 0 → ∀ v : V, (herm (Hpk k r) ω ω).re ^ n₀ * ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (‖ContinuousLinearMap.adjoint (Ap ω) v‖ ^ 2 + ‖ContinuousLinearMap.adjoint (Am ω) v‖ ^ 2) := by
  intro V _ _ _ Vp _ _ _ Vm _ _ _ k r z π πp πm u up um l n₀ b hz hT hπ hgap hl hlk hn hb hnb h1b hp hm hup hum
  obtain ⟨Vp', _, _, _, Vm', _, _, _, πp', πm', Ap', Am', hp', hm', hAp, hAm, hlb⟩ :=
    GlobalTheory.T.exists_shifted_types_lower_bound_alt V k r z π u l n₀ b hz hT hπ hgap hl hlk hn hb hnb h1b
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨φp, hφp⟩ := GlobalTheory.exists_isometry_of_isType_of_param_eq Vp Vp' n r z πp πp' _ _ hz hT hp hp' (by
    intro i hi
    rw [hup i hi, Function.update_apply]
    split_ifs with h
    · rw [h]
    · rfl)
  obtain ⟨φm, hφm⟩ := GlobalTheory.exists_isometry_of_isType_of_param_eq Vm Vm' n r z πm πm' _ _ hz hT hm hm' (by
    intro i hi
    rw [hum i hi, Function.update_apply]
    split_ifs with h
    · rw [h]
    · rfl)
  refine ⟨fun ω => (Ap' ω).comp (φp : Vp →L[ℂ] Vp'), fun ω => (Am' ω).comp (φm : Vm →L[ℂ] Vm'), ?_, ?_, ?_⟩
  · exact wigMap_comp V Vp' Vp (n + 1) r z π πp' πp n₀ 0 Ap' (fun _ => (φp : Vp →L[ℂ] Vp')) hAp
      (wigMap_zero_of_contraction Vp' Vp (n + 1) r z πp' πp _ (fun v => by simp)
        (fun h hh v => by simpa using hφp h hh v))
  · exact wigMap_comp V Vm' Vm (n + 1) r z π πm' πm n₀ 0 Am' (fun _ => (φm : Vm →L[ℂ] Vm')) hAm
      (wigMap_zero_of_contraction Vm' Vm (n + 1) r z πm' πm _ (fun v => by simp)
        (fun h hh v => by simpa using hφm h hh v))
  · intro ω hω hωz v
    rw [norm_adjoint_comp_isometryEquiv, norm_adjoint_comp_isometryEquiv]
    exact hlb ω hω hωz v

end GlobalTheory.WigSh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WopAddLattice
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership

namespace GlobalTheory.ThetaShift

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

variable {D : D7} {N N' : ℕ}

theorem Hf_nsmul_left (T : Tor D) (n : ℕ) (x y : VC D N N') :
    Hf D T (n • x) y = (n : ℂ) * Hf D T x y := by
  induction n with
  | zero => simp [Hf]
  | succ n ih => rw [succ_nsmul, Hf_add_left, ih]; push_cast; ring

theorem Hf_nsmul_right (T : Tor D) (n : ℕ) (x y : VC D N N') :
    Hf D T x (n • y) = (n : ℂ) * Hf D T x y := by
  induction n with
  | zero => simp [Hf]
  | succ n ih => rw [succ_nsmul, Hf_add_right, ih]; push_cast; ring

theorem qH_nsmul (T : Tor D) (n : ℕ) (x : VC D N N') :
    qH D T (n • x) = (n : ℝ) ^ 2 * qH D T x := by
  unfold qH
  rw [Hf_nsmul_left, Hf_nsmul_right, ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul]
  ring

theorem qH_int (T : Tor D) {Λ : AddSubgroup (VC D N N')} (hI : HfInt T Λ) {w : VC D N N'} (hw : w ∈ Λ) :
    ∃ m : ℤ, qH D T w = m ∧ al D T w = (-1 : ℂ) ^ m := by
  obtain ⟨m, h1, h2⟩ := self_int T hI hw
  have hs := sqrt_d_pos D
  refine ⟨m, ?_, ?_⟩
  · unfold qH
    rw [h1]
    field_simp
  · unfold al
    rw [h2]

theorem qH_add (T : Tor D) (x w : VC D N N') :
    qH D T (x + w) = qH D T x + qH D T w + Real.sqrt D.host.d * (Hf D T x w).re := by
  unfold qH
  rw [Hf_add_left, Hf_add_right, Hf_add_right, Complex.add_re, Complex.add_re, Complex.add_re,
    Hf_re_swap T x w]
  ring

theorem wPh_shift (T : Tor D) {p : ℕ} (hp : p.Prime) {x y : VC D N N'} {k : ℕ} {M n : ℤ}
    (hM : (p : ℝ) ^ k * qH D T x = M) (hy : qH D T y = qH D T x + n) :
    wPh D T p y = wPh D T p x * (-1 : ℂ) ^ n := by
  by_cases h2 : p = 2
  · unfold wPh
    rw [if_pos h2, if_pos h2, hy, ← GlobalTheory.GalThetaSign.exp_int_pi, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · have hM' : (p : ℝ) ^ k * qH D T y = ((M + ((p ^ k : ℕ) : ℤ) * n : ℤ) : ℝ) := by
      rw [hy, mul_add, hM]
      push_cast
      ring
    rw [GlobalTheory.GalThetaSign.wPh_eq D T x hp h2 hM, GlobalTheory.GalThetaSign.wPh_eq D T y hp h2 hM',
      zpow_add₀ (by norm_num), zpow_mul, zpow_natCast,
      ((hp.odd_of_ne_two h2).pow : Odd (p ^ k)).neg_one_pow]

theorem Wop_add_lattice : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (Λ : AddSubgroup (VC D N N')) (p : ℕ), p.Prime → Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt T Λ → ∀ G ∈ ThSp D T Λ, ∀ x w : VC D N N', w ∈ Λ → (∃ k : ℕ, p ^ k • x ∈ Λ) → (∃ a b : ℤ, Even (a - b) ∧ Hf D T x w = (((a : ℝ) / Real.sqrt D.host.d : ℝ) : ℂ) + (b : ℂ) * Complex.I) → Wop D T p (x + w) G = Wop D T p x G := by
  intro D T N N' Λ p hp hI G hG x w hw ⟨k, hk⟩ ⟨a, b, hab, h⟩
  have hs := sqrt_d_pos D
  obtain ⟨m, hm, hal⟩ := qH_int T hI hw
  obtain ⟨M, hM, -⟩ := qH_int T hI hk
  have hM' : (p : ℝ) ^ (k * 2) * qH D T x = M := by
    rw [← hM, qH_nsmul, pow_mul]
    push_cast
    ring
  have hre : (Hf D T x w).re = a / Real.sqrt D.host.d := by rw [h]; simp
  have him : (Hf D T x w).im = b := by rw [h]; simp
  have hq : qH D T (x + w) = qH D T x + ((m + a : ℤ) : ℝ) := by
    rw [qH_add, hm, hre]
    push_cast
    field_simp
    ring
  have hph := wPh_shift T hp hM' hq
  funext z
  have hU : U D T x G z = al D T w * cf T x w * U D T (x + w) G z := by
    conv_lhs => rw [← fix_eq T hG hw]
    rw [U_smul, U_U]; ring
  have hsgn : (-1 : ℂ) ^ (m + a) = (-1 : ℂ) ^ m * (-1 : ℂ) ^ (-b) := by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    apply neg_one_zpow_congr
    have : m + a - (m + -b) = (a - b) + 2 * b := by ring
    rw [this]
    exact hab.add (even_two_mul b)
  unfold Wop
  rw [hU, hph, hal, cf_int T x w b him, hsgn]
  ring

end GlobalTheory.ThetaShift
end

