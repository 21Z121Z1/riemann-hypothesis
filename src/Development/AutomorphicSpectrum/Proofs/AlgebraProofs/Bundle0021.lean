import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0019
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0031
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0009
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0009
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0007

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationQuotientEquivLatticeStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.augmentation_quotient_equiv_lattice : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), Nonempty (AFQuot p AA.carrier ≃ₗ[R] ((ι → R) ⧸ afLat p AA.carrier)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.afQuot_equiv_coords | exact GlobalTheory.CompanionTheory.Ar.GR.afQuot_equiv_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.afQuot_equiv_coords <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtensionUnique
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.PullPreserve

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)

section Closure

variable {O Ω V : Type} [CommRing O] [Field Ω] [Algebra O Ω] [AddCommGroup V] [Module Ω V]

theorem const_smul_mem (R : Subalgebra O Ω) (A : AddSubgroup V) (c : O) {v : V}
    (hv : v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e}) :
    algebraMap O Ω c • v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e} := by
  induction hv using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, e, he, rfl⟩ := hw
    exact AddSubgroup.subset_closure
      ⟨algebraMap O Ω c * a, mul_mem (R.algebraMap_mem c) ha, e, he, by rw [mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add w₁ w₂ _ _ h₁ h₂ => rw [smul_add]; exact add_mem h₁ h₂
  | neg w _ h => rw [smul_neg]; exact neg_mem h

theorem exists_const_smul_mem [IsDomain O] (R : Subalgebra O Ω) (A B : AddSubgroup V)
    (h : ∀ v ∈ A, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ B) {v : V}
    (hv : v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e}) :
    ∃ c : O, c ≠ 0 ∧
      algebraMap O Ω c • v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ B, v = a • e} := by
  induction hv using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, e, he, rfl⟩ := hw
    obtain ⟨c, hc, hce⟩ := h e he
    exact ⟨c, hc, AddSubgroup.subset_closure ⟨a, ha, _, hce, smul_comm _ _ _⟩⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | add w₁ w₂ _ _ h₁ h₂ =>
    obtain ⟨c₁, hc₁, m₁⟩ := h₁
    obtain ⟨c₂, hc₂, m₂⟩ := h₂
    refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, ?_⟩
    have e : algebraMap O Ω (c₁ * c₂) • (w₁ + w₂) =
        algebraMap O Ω c₂ • (algebraMap O Ω c₁ • w₁) +
          algebraMap O Ω c₁ • (algebraMap O Ω c₂ • w₂) := by
      rw [map_mul, smul_add, smul_smul, smul_smul, mul_comm]
    rw [e]
    exact add_mem (const_smul_mem R B c₂ m₁) (const_smul_mem R B c₁ m₂)
  | neg w _ h =>
    obtain ⟨c, hc, m⟩ := h
    exact ⟨c, hc, by rw [smul_neg]; exact neg_mem m⟩

theorem mem_span_scaled (R : Subalgebra O Ω) (A B : AddSubgroup V) (c : Ω)
    (h : ∀ v, v ∈ B ↔ ∃ e ∈ A, v = c • e) (v : V) :
    v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ B, v = a • e} ↔
      ∃ e ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e}, v = c • e :=
  _root_.UpperTheory.Reformulated.B.Ydb6.main R A B c h v

end Closure

theorem pull_preserve : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → (LatLE O x E E' → LatLE O (joinCoord x z) EB E'B) ∧ (SameGeneric O x E E' → SameGeneric O (joinCoord x z) EB E'B) ∧ (∀ c : Ω, IsScaled x c E.lat E'.lat → IsScaled (joinCoord x z) c EB.lat E'B.lat) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ E E' K' _ _ ι' _ z EB E'B hE hE'
  have hx : ∀ s, mseg (joinCoord x z) s ≠ 0 → mseg x (restrictChart s) ≠ 0 := by
    intro s hs h
    apply hs
    have e : mseg (joinCoord x z) s =
        mseg x (restrictChart s) * mseg z (fun k => s (.inr k)) := by
      simp only [mseg, Fintype.prod_sum_type]
      rfl
    rw [e, h, zero_mul]
  refine ⟨fun h s hs => ?_, fun h s hs => ⟨fun v hv => ?_, fun v hv => ?_⟩,
    fun c h s hs v => ?_⟩
  · rw [hE s hs, hE' s hs]
    refine AddSubgroup.closure_mono ?_
    rintro _ ⟨a, ha, e, he, rfl⟩
    exact ⟨a, ha, e, h _ (hx s hs) he, rfl⟩
  · rw [hE s hs] at hv
    rw [hE' s hs]
    exact exists_const_smul_mem _ _ _ (h _ (hx s hs)).1 hv
  · rw [hE' s hs] at hv
    rw [hE s hs]
    exact exists_const_smul_mem _ _ _ (h _ (hx s hs)).2 hv
  · rw [hE s hs, hE' s hs]
    exact mem_span_scaled _ _ _ c (h _ (hx s hs)) v

end GlobalTheory.CompanionTheory.Ar.Num.PullPreserve
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleShortExact
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.PullSubQuot

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)
open ReciprocityTheory.ChartRestriction.G.Geo (div_mem_chartRing)

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}

def comb (t : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => t k
  | .inr k => s (.inr k)

theorem mseg_join (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord x z) s = mseg x (restrictChart s) * mseg z (fun k => s (.inr k)) := by
  simp only [mseg, Fintype.prod_sum_type]
  rfl

theorem chartRing_le (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (joinCoord x z) s ≠ 0) :
    chartRing O (mseg x) (restrictChart s) ≤ chartRing O (mseg (joinCoord x z)) s := by
  have hw : mseg z (fun k => s (.inr k)) ≠ 0 := by
    rw [mseg_join] at hs
    exact right_ne_zero_of_mul hs
  unfold chartRing
  apply Algebra.adjoin_le
  rintro _ ⟨t, rfl⟩
  have h : mseg x t / mseg x (restrictChart s) =
      mseg (joinCoord x z) (comb t s) / mseg (joinCoord x z) s := by
    rw [mseg_join x z (comb t s), mseg_join x z s]
    exact (mul_div_mul_right _ _ hw).symm
  have h2 := div_mem_chartRing (o := O) (mseg (joinCoord x z)) s (comb t s)
  rw [← h] at h2
  exact h2

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N N₁ N₂ : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (E : ChartBundle O (mseg x) N V) (i : V₁ →ₗ[Ω] V) (p : V →ₗ[Ω] V₂) (E₁ : ChartBundle O (mseg x) N₁ V₁) (E₂ : ChartBundle O (mseg x) N₂ V₂), IsSubQuot O x E i p E₁ E₂ → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB : ChartBundle O (mseg (joinCoord x z)) N V) (EB₁ : ChartBundle O (mseg (joinCoord x z)) N₁ V₁) (EB₂ : ChartBundle O (mseg (joinCoord x z)) N₂ V₂), IsPull O x z E EB → IsPull O x z E₁ EB₁ → IsPull O x z E₂ EB₂ → IsSubQuot O (joinCoord x z) EB i p EB₁ EB₂ := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N N₁ N₂ V _ _ V₁ _ _ V₂ _ _ E i p E₁ E₂ h K' _ _ ι' _ z EB EB₁ EB₂ hE hE₁ hE₂
  obtain ⟨hi, hp, hex, hc⟩ := h
  refine ⟨hi, hp, hex, fun s hs => ?_⟩
  have hx : mseg x (restrictChart s) ≠ 0 := by
    rw [mseg_join] at hs
    exact left_ne_zero_of_mul hs
  obtain ⟨h₁, h₂⟩ := hc _ hx
  have hF : LocFree (chartRing O (mseg x) (restrictChart s)) N₂
      ((E.lat (restrictChart s)).map p.toAddMonoidHom) := by
    rw [← h₂]
    exact ⟨fun a ha v hv => E₂.stable _ a ha v hv, E₂.frame _ hx⟩
  obtain ⟨c₁, c₂⟩ := SpanExact.span_comap_exact _ _ (chartRing_le x z s hs) i p hi hex
    (E.lat (restrictChart s)) N₂ (fun a ha v hv => E.stable _ a ha v hv) hF
  have e : EB.lat s = spanOver (chartRing O (mseg (joinCoord x z)) s)
      (E.lat (restrictChart s) : Set V) := hE s hs
  have e₁ : EB₁.lat s = spanOver (chartRing O (mseg (joinCoord x z)) s)
      (E₁.lat (restrictChart s) : Set V₁) := hE₁ s hs
  have e₂ : EB₂.lat s = spanOver (chartRing O (mseg (joinCoord x z)) s)
      (E₂.lat (restrictChart s) : Set V₂) := hE₂ s hs
  rw [e, e₁, e₂, h₁, h₂]
  exact ⟨c₁.symm, c₂.symm⟩

end GlobalTheory.CompanionTheory.Ar.Num.PullSubQuot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CmProjectiveModulePairingPStatement
section
open NumberField TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_projective_module_pairing_p : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ (p : ℕ) [Fact p.Prime] (L L' : Type) [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L'] [Module.Finite (𝓞 E) L'] [Module.Projective (𝓞 E) L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), Module.finrank (𝓞 E) L = Module.finrank (𝓞 E) L' → (∀ x, B x x = 0) → Function.Bijective B → (∀ (a : 𝓞 E) x y, B (a • x) y = B x (bar a • y)) → (∀ x, B' x x = 0) → Function.Bijective B' → (∀ (a : 𝓞 E) x y, B' (a • x) y = B' x (bar a • y)) → ∃ φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] L'), (∀ (a : 𝓞 E) (x : L), φ (1 ⊗ₜ (a • x)) = LinearMap.baseChange ℤ_[p] (LinearMap.lsmul (𝓞 E) L' a).toAddMonoidHom.toIntLinearMap (φ (1 ⊗ₜ x))) ∧ ∀ u v, B'.baseChange ℤ_[p] (φ u) (φ v) = B.baseChange ℤ_[p] u v := by
  first | exact @GlobalTheory.CompanionTheory.TwGenus.two_unimodular_isometric_padic | exact GlobalTheory.CompanionTheory.TwGenus.two_unimodular_isometric_padic | (intros; apply GlobalTheory.CompanionTheory.TwGenus.two_unimodular_isometric_padic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeAdditiveSubQuotientStatement
section
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_additive_sub_quotient : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (W : Submodule K V), IsBun C L → deg C L = subDeg C L W + deg C (quot C L W) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg.deg_eq_subDeg_add_deg_quot | exact GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg.deg_eq_subDeg_add_deg_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg.deg_eq_subDeg_add_deg_quot <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualEigenSubDegreeTranspose
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.EigDual

theorem eig_dual_deg : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Matrix (Fin d) (Fin d) K, IsBun C L → (∀ a, IsHom C L L (Matrix.toLin' (ρ a))) → ∀ s, subDeg C (dotDual C L) (eig (fun a => Matrix.toLin' (ρ a).transpose) (fun a => algebraMap k K (χ s a))) = - subDeg C L (eig (fun a => Matrix.toLin' (ρ a)) (fun a => algebraMap k K (χ s a))) :=
  PositivityTheory.HtPt.Ci.eig_dual

end GlobalTheory.CompanionTheory.Ar.Crv.EigDual
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeFlagFrame
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.FlagDual

section Linear

variable {O Ω : Type*} [CommRing O] [Field Ω] [Algebra O Ω]
variable {V V₁ : Type*} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁] {N : ℕ}

theorem form_eq_sum {W : Type*} [AddCommGroup W] [Module Ω W] (w : Module.Basis (Fin N) Ω W)
    (φ : W →ₗ[Ω] Ω) (v : W) : φ v = ∑ j, w.repr v j * φ (w j) := by
  conv_lhs => rw [← w.sum_repr v]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem exists_coeffs (R : Subalgebra O Ω) (L : AddSubgroup V)
    (hst : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) (w : Module.Basis (Fin N) Ω V) (m : Fin N → Ω)
    (hg : ∀ i s, (∃ v ∈ L, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = s) ↔ ∃ a ∈ R, s = a * m i)
    (e : Fin N → V) (heL : ∀ i, e i ∈ L) (hez : ∀ i j, i < j → w.repr (e i) j = 0)
    (hed : ∀ i, w.repr (e i) i = m i) (k : ℕ) :
    ∀ v ∈ L, (∀ j : Fin N, k ≤ j.val → w.repr v j = 0) →
      ∃ c : Fin N → Ω, (∀ i, c i ∈ R) ∧ v = ∑ i, c i • e i := by
  induction k with
  | zero =>
    intro v _ hv
    refine ⟨0, fun _ => zero_mem _, ?_⟩
    have : v = 0 := by
      apply w.repr.injective
      ext j
      simpa using hv j (Nat.zero_le _)
    simp [this]
  | succ k ih =>
    intro v hvL hv
    by_cases hk : k < N
    · set i : Fin N := ⟨k, hk⟩ with hi
      obtain ⟨a, haR, ha⟩ := (hg i (w.repr v i)).1
        ⟨v, hvL, fun j hj => hv j (by
          have : i.val < j.val := hj
          simpa [hi] using this), rfl⟩
      have hv' : v - a • e i ∈ L := sub_mem hvL (hst a haR _ (heL i))
      obtain ⟨c, hcR, hc⟩ := ih _ hv' (fun j hj => by
        rcases Nat.lt_or_eq_of_le hj with hlt | heq
        · have hij : i < j := by
            show i.val < j.val
            simpa [hi] using hlt
          have h1 : w.repr v j = 0 := hv j hlt
          simp [h1, hez i j hij]
        · have hij : j = i := Fin.ext (by simp [hi, heq])
          subst hij
          simp [hed, ha])
      refine ⟨fun l => c l + (if l = i then a else 0), fun l => ?_, ?_⟩
      · refine add_mem (hcR l) ?_
        split_ifs
        · exact haR
        · exact zero_mem _
      · have : v = (v - a • e i) + a • e i := by abel
        rw [this, hc]
        simp [add_smul, Finset.sum_add_distrib, ite_smul]
    · exact ih v hvL (fun j _ => hv j (by have := j.isLt; omega))

theorem exists_basis (w : Module.Basis (Fin N) Ω V) (m : Fin N → Ω) (hm : ∀ i, m i ≠ 0)
    (e : Fin N → V) (hez : ∀ i j, i < j → w.repr (e i) j = 0) (hed : ∀ i, w.repr (e i) i = m i) :
    ∃ e' : Module.Basis (Fin N) Ω V, ∀ i, e' i = e i := by
  have hdet : IsUnit (w.det e) := by
    rw [Module.Basis.det_apply, isUnit_iff_ne_zero,
      Matrix.det_of_upperTriangular (M := w.toMatrix e)]
    · refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      simpa [Module.Basis.toMatrix_apply, hed] using hm i
    · intro i j hij
      simpa [Module.Basis.toMatrix_apply] using hez j i hij
  obtain ⟨hli, hsp⟩ := (Module.Basis.is_basis_iff_det w).2 hdet
  exact ⟨Module.Basis.mk hli hsp.ge, fun i => by simp⟩

theorem coord_w (w e' : Module.Basis (Fin N) Ω V) (m : Fin N → Ω) (hm : ∀ i, m i ≠ 0)
    (hez : ∀ i j, i < j → w.repr (e' i) j = 0) (hed : ∀ i, w.repr (e' i) i = m i) (r : Fin N) :
    (∀ l, l < r → e'.repr (w l) r = 0) ∧ e'.repr (w r) r = (m r)⁻¹ := by
  have hexp : ∀ l, (∀ j, j < l → e'.repr (w j) r = 0) →
      e'.repr (e' l) r = m l * e'.repr (w l) r := by
    intro l hl
    have h0 : e'.repr (e' l) r = ∑ j, w.repr (e' l) j * e'.repr (w j) r :=
      form_eq_sum w (e'.coord r) (e' l)
    rw [h0, Finset.sum_eq_single l]
    · rw [hed]
    · intro j _ hjl
      rcases lt_or_gt_of_ne hjl with h | h
      · simp [hl j h]
      · simp [hez l j h]
    · simp
  have hlow : ∀ n : ℕ, ∀ l : Fin N, l.val = n → l < r → e'.repr (w l) r = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro l hln hlr
      have h1 := hexp l (fun j hj => ih j.val (by rw [← hln]; exact hj) j rfl (hj.trans hlr))
      have h2 : e'.repr (e' l) r = 0 := by
        simp [Module.Basis.repr_self, Finsupp.single_apply, hlr.ne]
      rw [h2] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left (hm l)
  have hlow' : ∀ l, l < r → e'.repr (w l) r = 0 := fun l hl => hlow _ l rfl hl
  refine ⟨hlow', ?_⟩
  have h1 := hexp r hlow'
  have h2 : e'.repr (e' r) r = 1 := by simp
  rw [h2] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

theorem dual_graded (R : Subalgebra O Ω) (L : AddSubgroup V) (L₁ : AddSubgroup V₁)
    (hst : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) (w : Module.Basis (Fin N) Ω V) (m : Fin N → Ω)
    (hm : ∀ i, m i ≠ 0)
    (hg : ∀ i s, (∃ v ∈ L, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = s) ↔ ∃ a ∈ R, s = a * m i)
    (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (hβ : Function.Surjective β.flip)
    (hL₁ : ∀ u, u ∈ L₁ ↔ ∀ v ∈ L, β v u ∈ R) (w₁ : Module.Basis (Fin N) Ω V₁)
    (hw : ∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0) (j : Fin N) (s : Ω) :
    (∃ u ∈ L₁, (∀ l, j < l → w₁.repr u l = 0) ∧ w₁.repr u j = s) ↔
      ∃ a ∈ R, s = a * (m j.rev)⁻¹ := by
  have hcoord : ∀ u l, w₁.repr u l = β (w l.rev) u := by
    intro u l
    rw [form_eq_sum w₁ (β (w l.rev)) u]
    simp [hw, Fin.rev_inj]
  have hex : ∀ i, ∃ v, v ∈ L ∧ (∀ l, i < l → w.repr v l = 0) ∧ w.repr v i = m i := by
    intro i
    obtain ⟨v, hv, h1, h2⟩ := (hg i (m i)).2 ⟨1, one_mem _, by simp⟩
    exact ⟨v, hv, h1, h2⟩
  choose e heL hez hed using hex
  obtain ⟨e', he'⟩ := exists_basis w m hm e hez hed
  have hez' : ∀ i l, i < l → w.repr (e' i) l = 0 := fun i l h => by rw [he']; exact hez i l h
  have hed' : ∀ i, w.repr (e' i) i = m i := fun i => by rw [he']; exact hed i
  set r := j.rev with hr
  obtain ⟨hlow, htop⟩ := coord_w w e' m hm hez' hed' r
  constructor
  · rintro ⟨u, hu, hz, rfl⟩
    refine ⟨m r * w₁.repr u j, ?_, ?_⟩
    · have hmem := (hL₁ u).1 hu _ (heL r)
      have hsum : β (e r) u = m r * w₁.repr u j := by
        have h0 : β (e r) u = ∑ l, w.repr (e r) l * β (w l) u :=
          form_eq_sum w (β.flip u) (e r)
        rw [h0, Finset.sum_eq_single r]
        · rw [hed, hcoord u j]
        · intro l _ hlr
          rcases lt_or_gt_of_ne hlr with h | h
          · have hl : j < l.rev := by
              rw [hr] at h
              have := Fin.rev_lt_rev.2 h
              simpa using this
            have h2 := hcoord u l.rev
            rw [Fin.rev_rev] at h2
            rw [← h2, hz _ hl, mul_zero]
          · simp [hez r l h]
        · simp
      rwa [hsum] at hmem
    · field_simp [hm r]
  · rintro ⟨a, haR, rfl⟩
    obtain ⟨u, hu⟩ := hβ (a • e'.coord r)
    have hβu : ∀ v, β v u = a * e'.repr v r := fun v => by
      have := LinearMap.congr_fun hu v
      simpa using this
    refine ⟨u, (hL₁ u).2 fun v hv => ?_, fun l hl => ?_, ?_⟩
    · obtain ⟨c, hcR, hc⟩ := exists_coeffs R L hst w m hg e heL hez hed N v hv
        (fun l hl => by have := l.isLt; omega)
      have hcoef : e'.repr v r = c r := by
        have : v = ∑ i, c i • e' i := by simpa [he'] using hc
        rw [this]
        simp [map_sum, Finsupp.finset_sum_apply, Finsupp.single_apply]
      rw [hβu, hcoef]
      exact mul_mem haR (hcR r)
    · rw [hcoord, hβu, hlow _ (by simpa [hr] using Fin.rev_lt_rev.2 hl), mul_zero]
    · rw [hcoord, hβu, ← hr, htop]

end Linear

theorem main : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N V₁) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω), IsDualLat O x β E.lat F.lat → ∀ (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ), IsFlagFrame x E w b → ∀ w₁ : Module.Basis (Fin N) Ω V₁, (∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0) → IsFlagFrame x F w₁ (fun j => -b j.rev) := by
  intro O _ Ω _ _ K _ _ ι _ x N V _ _ V₁ _ _ E F β hdual w b hE w₁ hw
  refine ⟨fun c hc i => ?_⟩
  have hc' : mseg x c ≠ 0 := hc
  have hx : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc' k (Finset.mem_univ k)
  have hm : ∀ l, (∏ k, x ⟨k, c k⟩ ^ b l k) ≠ 0 := fun l =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hx k)
  ext s
  have key := dual_graded (chartRing O (mseg x) c) (E.lat c) (F.lat c)
    (fun a ha v hv => E.stable c a ha v hv) w (fun l => ∏ k, x ⟨k, c k⟩ ^ b l k) hm
    (fun l s => by
      have := Set.ext_iff.1 (hE.graded c hc l) s
      exact this)
    β hdual.1.2 (hdual.2 c hc') w₁ hw i s
  have hinv : (∏ k, x ⟨k, c k⟩ ^ b i.rev k)⁻¹ = ∏ k, x ⟨k, c k⟩ ^ (-b i.rev) k := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun k _ => by simp [zpow_neg]
  rw [hinv] at key
  exact key

end GlobalTheory.CompanionTheory.Ar.Num.FlagDual
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenspaceFrobeniusTwist
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem eig_frobenius_twist : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) (ρ : O → Matrix (Fin d) (Fin d) K) (χ : O → K), eig (fun a => Matrix.toLin' ((ρ a).map (· ^ p))) (fun a => χ a ^ p) = frobSub p (eig (fun a => Matrix.toLin' (ρ a)) χ) :=
  PositivityTheory.HtPt.Ci.eig_frob

end GlobalTheory.CompanionTheory.Ar.Crv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsIntegralPosDefPerturbationStatement
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_posDef_perturbation : ∀ (E : Type) [Field E] [NumberField E] (Ψ : Set (E →+* ℂ)) (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (M : (E →+* ℂ) → Matrix J J ℂ) (C : (E →+* ℂ) → Matrix I J ℂ) (X₀ : Matrix I J (𝓞 E)) (n : ℕ), n ≠ 0 → (∀ τ ∈ Ψ, ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ ∈ Ψ, (M τ).IsHermitian ∧ (C τ * M τ * (C τ)ᴴ).PosDef) → ∃ Y : Matrix I J (𝓞 E), ∀ τ ∈ Ψ, (((X₀ + n • Y).map fun a => τ (a : E)) * M τ * ((X₀ + n • Y).map fun a => τ (a : E))ᴴ).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.frame_congr_posDef_on_places | exact GlobalTheory.CompanionTheory.Ar.Fl.frame_congr_posDef_on_places | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.frame_congr_posDef_on_places <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFlatSubgroupSchemeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_flat_subgroup_scheme : ∀ (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (B : Type) [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ A), IsFinFlatSub A B h → ∃ _ : GrpObj (sp (R₀ := R) B), IsMonHom h ∧ Mono h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.SubGrp.grpObj_of_isFinFlatSub | exact GlobalTheory.CompanionTheory.Ar.GR.SubGrp.grpObj_of_isFinFlatSub | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.SubGrp.grpObj_of_isFinFlatSub <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GenerationAlongInvariantsStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generation_along_invariants : ∀ (p : ℕ) (C : Type) [Field C] (R : Type) [CommRing R] [Algebra R C] (N N' : Type) [AddCommGroup N] [AddCommGroup N'] (M : Submodule R (N → C)) (M' : Submodule R (N' → C)) (j : N →+ N') (K : AddSubgroup N), M'.map (LinearMap.funLeft R C (j : N → N')) = invFun M K → GenAF p M' ⊥ → GenAF p M K := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.genAF_of_map_eq_invFun | exact GlobalTheory.CompanionTheory.Ar.GR.genAF_of_map_eq_invFun | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.genAF_of_map_eq_invFun <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeKernelImageLattice
section
open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

namespace GlobalTheory.CompanionTheory.Ar.PtSeq

theorem pt_seq_lin : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) (p : ℕ) {F : Type} [Zero F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (τ : Sg), w ≠ 0 → mulLat w (stdLat RC _) ≤ D.af RC p (χ τ) → D.af RC p (χ τ) ≤ stdLat RC _ → ∀ (ht : (Fin n → C) →ₗ[C] (Fin (s τ) → C)) (hb : (Fin (r τ) → C) →ₗ[C] (Fin n → C)), Function.Injective hb → LinearMap.range hb = LinearMap.ker ht → (stdLat RC _).map ht.toAddMonoidHom = D.omHT τ → (stdLat RC _).comap hb.toAddMonoidHom = D.W τ → (D.hh RC p (χ τ)).map ht.toAddMonoidHom = D.om τ → (D.hh RC p (χ τ)).comap hb.toAddMonoidHom = divLat w (D.lie τ) → (∀ b c, (b, c) ∈ D.Del τ ↔ w • b ∈ stdLat RC _ ∧ c - ht b ∈ D.omHT τ) → (∀ a b, (a, b) ∈ D.Gam τ ↔ w • a ∈ D.W τ ∧ b - hb a ∈ stdLat RC _) → D.imH RC p τ (χ τ) = D.om τ ∧ D.kerH RC p τ (χ τ) = divLat w (D.lie τ) :=
  @PositivityTheory.Xgn.t_pt_seq_lin

end GlobalTheory.CompanionTheory.Ar.PtSeq
end

