import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0025
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicDegreeTameRamification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0884
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormsEqOfKeyDataIsoComplex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0237
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2089
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0692
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0715
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0941
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2094
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0929
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2058

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatementOfDegreeTheorem
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM Matrix

namespace GlobalTheory.FlatDegreeCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Degree

variable {k : Type} [Field k] [NumberField k]

def ordOf (a : HeightOneSpectrum (𝓞 k) → k) (𝔭 : HeightOneSpectrum (𝓞 k)) : ℝ :=
  (WithZero.log (𝔭.valuation k (a 𝔭)) : ℤ)

theorem finite_support_ordTwist (τ : E →+* k) : (Function.support (EigenvectorLieDegree.ordTwist H τ)).Finite := by
  have f : ∀ 𝔞, {𝔭 | ¬ EigenvectorLieDegree.ordIdeal τ 𝔞 𝔭 = 0}.Finite := fun 𝔞 =>
    Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors _)
  refine ((f (differentIdeal ℤ (𝓞 E))).union (f (Ideal.span {H.rt}))).subset fun 𝔭 h => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  exact h (by rw [EigenvectorLieDegree.ordTwist, hc.1, hc.2]; rfl)

end Degree

section Lie

variable {k : Type} [Field k] [NumberField k] {t : SAB H (Sp k)} {m : ℕ} {x : Fin m → (epsR k ⟶ t.G)}

theorem isEigBasis_iff (τ : E →+* k) : EigenvectorLieDegree.IsEigBasis t.act (τ.comp (algebraMap (𝓞 E) E)) x ↔
    AdelicDegreeTameRamification.IsEigenBasis t (fun a => τ (a : E)) x := Iff.rfl

open GlobalTheory.KeyPow GlobalTheory.KeyKa GlobalTheory.KeyEq GlobalTheory.KeyIsoNormal in
theorem isArchSq_iff (σ : k →+* ℂ) (N : ℝ) : EigenvectorLieDegree.IsArchSq t.G t.PP.L x σ N ↔ AdelicDegreeTameRamification.IsArchNormSq t x σ N := by
  constructor
  · rintro ⟨A, _, φ, g, u', Hm, χ, v, W, hφ, hA, hv, h0, hN⟩
    obtain ⟨t', ⟨n⟩⟩ := exists_sab (spMap σ) t
    obtain ⟨e, he, hφ'⟩ := grpPullback_iso hφ n.cart
    have hL : LBIso t'.PP.L (t.PP.L.pull n.cm.F) := by
      obtain ⟨w, hw, -⟩ := n.lin
      exact ⟨w, hw⟩
    obtain ⟨w, hw⟩ : LBIso (t.PP.L.pull φ) (t'.PP.L.pull e.hom.left) := hφ' ▸ EllComp.lbIso_pull_comp hL.symm _
    have hL' := pull_isLB t.PP.isLB φ
    obtain ⟨u, hex, hΛ, hfr⟩ := exists_push t'.PP.isLB hL' e.hom (isGrpPullback_of_iso e) w ((isGen_iff w).1 hw) u'
    refine ⟨t', n, g, u, Hm, fun l => χ ⟨l.1, hΛ ▸ l.2⟩, fun i => v i ≫ e.hom, W,
      ⟨hA.1, hA.2.1, fun l => hA.2.2.1 _, fun l j z hz => ?_⟩, fun i => ?_, fun i U hU f => ?_, hN, h0⟩
    · rw [hex] at hz
      have hj : e.hom.left ((u'.ex z).left pt) ∈ t'.PP.L.U j := (top_le_preimage_iff_mem _ _).1 hz
      obtain ⟨c, hc⟩ := exists_chart hL' ((u'.ex z).left pt)
      have hl : u'.ex (z + l.1) = u'.ex z := by
        rw [u'.ex_add, (u'.ker l.1).2 (hΛ ▸ l.2), _root_.mul_one]
      have a := hA.2.2.2 ⟨l.1, hΛ ▸ l.2⟩ c z ((top_le_preimage_iff_mem _ _).2 hc)
      rw [hfr j c z hj hc, hfr j c (z + l.1) (hl ▸ hj) (hl ▸ hc), hl, a]
      ring
    · rw [Over.comp_left, Category.assoc]
      exact (congrArg _ hφ').trans (hv i).1
    · have := (hv i).2 (e.hom.left ⁻¹ᵁ U) hU ((e.hom.left.app U).hom f)
      simp only [valAt'_comp, ← hex] at this
      rw [← this]
      congr 2
  · rintro ⟨t', n, g, u, Hm, χ, v, W, hA, hv, hW, hN, h0⟩
    obtain ⟨w, hw, -⟩ := n.lin
    exact ⟨t'.G, inferInstance, n.φ, g, TorsionTauCompare.transport t'.PP.isLB (pull_isLB t.PP.isLB _) hw u, Hm, χ, v, W,
      n.cart, TorsionTauCompare.isAH_transport _ _ hw u hA, fun i => ⟨hv i, hW i⟩, h0, hN⟩

end Lie

section Point

variable {k : Type} [Field k] [NumberField k]

def IsEigData (t : SAB H (Sp k)) (τ : E →+* k) (m : ℕ) (r : HeightOneSpectrum (𝓞 k) → ℝ) (N : (k →+* ℂ) → ℝ) : Prop :=
  ∃ v : Fin m → (epsR k ⟶ t.G), EigenvectorLieDegree.IsEigBasis t.act (τ.comp (algebraMap (𝓞 E) E)) v ∧
    (∀ 𝔭, EigenvectorLieDegree.IsLocOrd t.G v 𝔭 (r 𝔭)) ∧ ∀ σ, EigenvectorLieDegree.IsArchSq t.G t.PP.L v σ (N σ)

def ClaimOrd (x : ℝ) (t : SAB H (Sp k)) (τ τ' : E →+* k) (p q : ℕ) : Prop :=
  ∀ r N r' N', IsEigData t τ p r N → IsEigData t τ' q r' N' →
    (Function.support r).Finite ∧ (Function.support r').Finite ∧
    EigenvectorLieDegree.adDeg r N - EigenvectorLieDegree.adDeg r' N' = ((p : ℝ) - q) / 2 * x ∧
    EigenvectorLieDegree.adDeg (fun 𝔭 => r 𝔭 - r' 𝔭 - q * (EigenvectorLieDegree.ordTwist H τ 𝔭 : ℝ)) (fun σ => N σ / N' σ) =
      -EigenvectorLieDegree.cOne H p q x ∧
    |EigenvectorLieDegree.cOne H p q x + ((p : ℝ) - q) * x / 2| ≤ q * Real.log (rootDiscr E)

def ClaimGen (t : SAB H (Sp k)) (τ τ' : E →+* k) (p q : ℕ) : Prop :=
  ∀ (x : Fin p → (epsR k ⟶ t.G)) (x' : Fin q → (epsR k ⟶ t.G)),
    AdelicDegreeTameRamification.IsEigenBasis t (fun a => τ (a : E)) x → AdelicDegreeTameRamification.IsEigenBasis t (fun a => τ' (a : E)) x' →
  ∀ (a a' : HeightOneSpectrum (𝓞 k) → k) (r r' : (k →+* ℂ) → ℝ),
    (∀ v, AdelicDegreeTameRamification.IsLocalGen t x v (a v)) → (∀ v, AdelicDegreeTameRamification.IsLocalGen t x' v (a' v)) →
    (∀ σ, AdelicDegreeTameRamification.IsArchNormSq t x σ (r σ)) → (∀ σ, AdelicDegreeTameRamification.IsArchNormSq t x' σ (r' σ)) →
    AdelicDegreeTameRamification.AlmostUnit k a ∧ AdelicDegreeTameRamification.AlmostUnit k a' ∧
    AdelicDegreeTameRamification.adelicDeg k a r - AdelicDegreeTameRamification.adelicDeg k a' r' = ((p : ℝ) - q) / 2 * AdelicDegreeTameRamification.logOmega H ∧
    ∀ b : HeightOneSpectrum (𝓞 k) → k, (∀ v, AdelicDegreeTameRamification.IsFlatFactor H (fun a => τ (a : E)) v (b v)) →
      AdelicDegreeTameRamification.AlmostUnit k b ∧
      ∀ c₁ : ℝ, c₁ = -AdelicDegreeTameRamification.adelicDeg k (fun v => b v ^ q * a v / a' v) (fun σ => r σ / r' σ) →
        -c₁ = ((p : ℝ) - q) / 2 * AdelicDegreeTameRamification.logOmega H +
          q * (2 * Real.log (rootDiscr (AdelicDegreeTameRamification.quadField H)) - Real.log (rootDiscr E)) ∧
        |c₁ + ((p : ℝ) - q) * AdelicDegreeTameRamification.logOmega H / 2| ≤ q * Real.log (rootDiscr E)

variable {t : SAB H (Sp k)} {τ τ' : E →+* k} {p q : ℕ}

end Point

def AtAllObjects (H : Host E)
    (Q : ∀ (L : Type) [Field L] [NumberField L], SAB H (Sp L) → (E →+* L) → (E →+* L) → ℕ → ℕ → Prop) : Prop :=
  ∀ (D : Datum H) (l : Level H) (c : Coeff l) (k : Type) [Field k] [NumberField k] (j : c.F →+* k)
    (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom))
    (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → Q k o.t (EigenvectorLieDegree.embIn c j τ) (EigenvectorLieDegree.embIn c j (conjEmb τ)) D.p D.q

def DegreeOnModels : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), EigenvectorLieDegree.IsHostField H →
    ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ →
      EigenvectorLieDegree.AtAllPoints H fun _ _ _ t τ τ' p q => (∀ 𝔭, HasModel t 𝔭) → ClaimOrd (logOm E χ).re t τ τ' p q

section Extension

variable {k k' : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] {i : k →+* k'}

structure IsUnder (i : k →+* k') (π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k))
    (ε : HeightOneSpectrum (𝓞 k') → ℕ) : Prop where
  val : ∀ 𝔓 (z : k), 𝔓.valuation k' (i z) = (π 𝔓).valuation k z ^ ε 𝔓
  sum : ∀ 𝔭, ∃ s : Finset (HeightOneSpectrum (𝓞 k')), (∀ 𝔓, 𝔓 ∈ s ↔ π 𝔓 = 𝔭) ∧ s.Nonempty ∧
    (Module.finrank ℚ k : ℝ) * ∑ 𝔓 ∈ s, (ε 𝔓 : ℝ) * Real.log (Ideal.absNorm 𝔓.asIdeal) =
      (Module.finrank ℚ k' : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal)

theorem exists_isUnder (i : k →+* k') : ∃ π ε, IsUnder i π ε :=
  let ⟨π, ε, a, b⟩ := GlobalTheory.T.ramification_weighted_log_norm_sum k k' i
  ⟨π, ε, a, b⟩

variable {π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)} {ε : HeightOneSpectrum (𝓞 k') → ℕ}

theorem IsUnder.pos (h : IsUnder i π ε) (𝔓 : HeightOneSpectrum (𝓞 k')) : 0 < ε 𝔓 :=
  Nat.pos_of_ne_zero fun e => by simpa [e] using h.val 𝔓 0

theorem IsUnder.surjective (h : IsUnder i π ε) : Function.Surjective π := fun 𝔭 =>
  let ⟨_, hs, ⟨𝔓, h𝔓⟩, _⟩ := h.sum 𝔭
  ⟨𝔓, (hs 𝔓).1 h𝔓⟩

def up (π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)) (ε : HeightOneSpectrum (𝓞 k') → ℕ)
    (r : HeightOneSpectrum (𝓞 k) → ℝ) (𝔓 : HeightOneSpectrum (𝓞 k')) : ℝ := ε 𝔓 * r (π 𝔓)

theorem IsUnder.finite_of_up (h : IsUnder i π ε) {r : HeightOneSpectrum (𝓞 k) → ℝ}
    (hr : (Function.support (up π ε r)).Finite) : (Function.support r).Finite :=
  (hr.image π).subset fun 𝔭 h𝔭 => by
    obtain ⟨𝔓, rfl⟩ := h.surjective 𝔭
    exact ⟨𝔓, mul_ne_zero (Nat.cast_ne_zero.2 (h.pos 𝔓).ne') h𝔭, rfl⟩

theorem IsUnder.adDeg_up (h : IsUnder i π ε) {r : HeightOneSpectrum (𝓞 k) → ℝ} (hr : (Function.support r).Finite)
    (N : (k →+* ℂ) → ℝ) : EigenvectorLieDegree.adDeg (up π ε r) (fun σ => N (σ.comp i)) = EigenvectorLieDegree.adDeg r N := by
  classical
  choose s hs _ hsum using h.sum
  have n0 : (Module.finrank ℚ k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have n0' : (Module.finrank ℚ k' : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have a := GlobalTheory.T.embedding_sum_degree_formula k k' i fun σ => Real.log (N σ)
  have b : (Module.finrank ℚ k : ℝ) * ∑ᶠ 𝔓, up π ε r 𝔓 * Real.log (Ideal.absNorm 𝔓.asIdeal) =
      (Module.finrank ℚ k' : ℝ) * ∑ᶠ 𝔭, r 𝔭 * Real.log (Ideal.absNorm 𝔭.asIdeal) := by
    rw [finsum_eq_sum_of_support_subset (s := hr.toFinset.biUnion s), finsum_eq_sum_of_support_subset (s := hr.toFinset),
      Finset.sum_biUnion, Finset.mul_sum, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun 𝔭 _ => ?_
      rw [mul_left_comm, ← hsum, mul_left_comm, Finset.mul_sum (s 𝔭) _ (r 𝔭)]
      congr 1
      refine Finset.sum_congr rfl fun 𝔓 h𝔓 => ?_
      rw [up, (hs _ _).1 h𝔓]; ring
    · intro 𝔭 _ 𝔮 _ e
      exact Finset.disjoint_left.2 fun 𝔓 u v => e (((hs _ _).1 u).symm.trans ((hs _ _).1 v))
    · intro 𝔭 h𝔭
      simpa using left_ne_zero_of_mul h𝔭
    · intro 𝔓 h𝔓
      have := right_ne_zero_of_mul (left_ne_zero_of_mul h𝔓)
      simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Set.Finite.mem_toFinset]
      exact ⟨π 𝔓, this, (hs _ _).2 rfl⟩
  rw [EigenvectorLieDegree.adDeg, EigenvectorLieDegree.adDeg, div_eq_div_iff n0' n0]
  linear_combination b - 1 / 2 * a

theorem IsUnder.ordTwist (h : IsUnder i π ε) (τ : E →+* k) (𝔓 : HeightOneSpectrum (𝓞 k')) :
    EigenvectorLieDegree.ordTwist H (i.comp τ) 𝔓 = ε 𝔓 * EigenvectorLieDegree.ordTwist H τ (π 𝔓) := by
  have e : ∀ 𝔞, EigenvectorLieDegree.ordIdeal (i.comp τ) 𝔞 𝔓 = ε 𝔓 * EigenvectorLieDegree.ordIdeal τ 𝔞 (π 𝔓) := fun 𝔞 =>
    GlobalTheory.T.ideal_count_under_extension E k k' i τ 𝔞 _ _ _ (h.val 𝔓)
  simp only [EigenvectorLieDegree.ordTwist, e]
  ring

variable {t : SAB H (Sp k)} {t' : SAB H (Sp k')}

theorem IsEigData.up (h : IsUnder i π ε) (n : SABMap t' t (spMap i)) {τ : E →+* k} {m : ℕ}
    {r : HeightOneSpectrum (𝓞 k) → ℝ} {N : (k →+* ℂ) → ℝ} (hd : IsEigData t τ m r N) :
    IsEigData t' (i.comp τ) m (up π ε r) fun σ => N (σ.comp i) := by
  obtain ⟨x, hx, hr, hN⟩ := hd
  choose x' hx' _ using fun a => existsUnique_isVecOver n.cart.1 (x a)
  have h₁ := GlobalTheory.T.eigenbasis_base_change E H k k' i t t' n m x x' _ hx' hx
  have h₂ := fun 𝔓 => GlobalTheory.T.nonarchimedean_norm_base_change E H k k' i t t' n m x x' (π 𝔓) 𝔓 (ε 𝔓) (r (π 𝔓)) (Indep.of_eigBasis hx) hx' (h.val 𝔓) (hr _)
  have h₃ := fun σ : k' →+* ℂ => (isArchSq_iff σ _).2
    (GlobalTheory.T.archimedean_norm_square_base_change E H k k' i t t' n m x x' σ (N (σ.comp i)) hx' ((isArchSq_iff (σ.comp i) _).1 (hN _)))
  exact ⟨x', h₁, h₂, h₃⟩

theorem ClaimOrd.down (n : SABMap t' t (spMap i)) {x : ℝ} {τ τ' : E →+* k} {p q : ℕ}
    (c : ClaimOrd x t' (i.comp τ) (i.comp τ') p q) : ClaimOrd x t τ τ' p q := by
  obtain ⟨π, ε, h⟩ := exists_isUnder i
  intro r N r' N' h₁ h₂
  obtain ⟨f₁, f₂, d₁, d₂, b⟩ := c _ _ _ _ (h₁.up h n) (h₂.up h n)
  have g₁ := h.finite_of_up f₁
  have g₂ := h.finite_of_up f₂
  rw [h.adDeg_up g₁, h.adDeg_up g₂] at d₁
  refine ⟨g₁, g₂, d₁, Eq.trans ?_ d₂, b⟩
  rw [← h.adDeg_up]
  · congr 1
    funext 𝔓
    simp only [FlatDegreeCompare.up, h.ordTwist]
    push_cast
    ring
  · refine ((g₁.union g₂).union (finite_support_ordTwist (H := H) τ)).subset fun 𝔭 h𝔭 => ?_
    by_contra hc
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc
    exact h𝔭 (by simp [hc.1.1, hc.1.2, hc.2])

end Extension

end GlobalTheory.FlatDegreeCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfAtSmallPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HalfLabels

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]

theorem cjE_cjE (φ : E →+* Formalism.ConjugateSelfDual.Qbar l) : ExpFrame.cj (cj φ) = φ := by
  ext x
  simp only [ExpFrame.cj, RingHom.comp_apply]
  exact congrArg φ (IsCMField.complexConj_apply_apply E x)

theorem isHalf_cj {ι : Type} {inc : ι → (E →+* Formalism.ConjugateSelfDual.Qbar l)} (h : IsHalf inc) : IsHalf fun τ => ExpFrame.cj (inc τ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a b hab => h1 ?_, fun τ τ' e => h2 τ' τ ?_, fun i => ?_⟩
  · have := congrArg ExpFrame.cj hab
    simpa only [cjE_cjE] using this
  · simp only [cjE_cjE] at e
    exact e.symm
  · obtain ⟨τ, hτ | hτ⟩ := h3 i
    · exact ⟨τ, Or.inr (by rw [cjE_cjE]; exact hτ)⟩
    · exact ⟨τ, Or.inl hτ⟩

end GlobalTheory.HalfLabels

namespace GlobalTheory.HalfLabels

theorem exists_aut {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [CharZero K] (ι i : E →+* K) :
    ∃ σ : E ≃ₐ[ℚ] E, i = ι.comp (σ : E →+* E) := by
  let _ : Algebra E K := ι.toAlgebra
  have : IsScalarTower ℚ E K := IsScalarTower.of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ K), eq_ratCast (algebraMap ℚ E), map_ratCast]
  let φ : E →ₐ[ℚ] K := i.toRatAlgHom
  refine ⟨AlgEquiv.ofBijective (φ.restrictNormal E) (AlgHom.normal_bijective ℚ E E _), ?_⟩
  ext x
  have h := AlgHom.restrictNormal_commutes φ E x
  exact h.symm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isHalf_lab (D : D7) {l : ℕ} [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) : IsHalf (incOf D e0 false) := by
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  set ι : D.host.E →+* PadicAlgCl l := e0.comp D.embE with hι
  have hinc : ∀ τ, incOf D e0 false τ = ι.comp (D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E) := fun τ => rfl
  have hcc : ∀ g, ExpFrame.cj (ι.comp (D.host.sigmaOf g : D.host.E →+* D.host.E)) =
      ι.comp (D.host.sigmaOf (g * D.R.cc) : D.host.E →+* D.host.E) := by
    intro g
    have hs : D.host.sigmaOf (g * D.R.cc) = D.host.sigmaOf g * D.host.conj :=
      map_mul (D.host.gal).symm g (D.R.cc)
    ext x
    rw [hs]
    show ι (D.host.sigmaOf g (IsCMField.complexConj D.host.E x)) = ι (D.host.sigmaOf g (D.host.conj x))
    congr 2
    exact Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hinj : ∀ g g', ι.comp (D.host.sigmaOf g : D.host.E →+* D.host.E) = ι.comp (D.host.sigmaOf g' : D.host.E →+* D.host.E) →
      g = g' := by
    intro g g' h
    have : D.host.sigmaOf g = D.host.sigmaOf g' := AlgEquiv.ext fun x => ι.injective (RingHom.congr_fun h x)
    exact (D.host.gal).symm.injective this
  refine ⟨fun τ τ' h => ?_, fun τ τ' h => ?_, fun i => ?_⟩
  · rw [hinc, hinc] at h
    exact D.eTau.injective (Subtype.ext (hinj _ _ h))
  · rw [hinc, hinc, hcc] at h
    have e := hinj _ _ h
    exact (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau τ).2 (e ▸ (D.eTau τ').2)
  · obtain ⟨σ, hσ⟩ := exists_aut ι i
    have hσg : D.host.sigmaOf (D.host.gal σ) = σ :=
      (D.host.gal).symm_apply_apply σ
    by_cases hg : D.host.gal σ ∈ D.R.Psi
    · refine ⟨D.eTau.symm ⟨_, hg⟩, Or.inl ?_⟩
      rw [hinc, Equiv.apply_symm_apply, hσ, hσg]
    · have hg' : D.host.gal σ * D.R.cc ∈ D.R.Psi := by
        by_contra h'
        exact hg ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h')
      refine ⟨D.eTau.symm ⟨_, hg'⟩, Or.inr ?_⟩
      rw [hinc, Equiv.apply_symm_apply, ← hcc, cjE_cjE, hσ, hσg]

theorem halfAt_all (D : D7) (l : ℕ) : HalfAt D l := by
  intro _ e0 b
  cases b
  · exact isHalf_lab D (l := l) e0
  · exact isHalf_cj (isHalf_lab D e0)

theorem halfAt_inRange : InRange fun Fm x _ i p j P _ w => SmallAt p j P w → HalfAt (Fm.D x i) (Formalism.EigenvalueLevelCeiling.plc w) := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  exact EvPt.of_forall fun x _ i _ _ _ _ _ _ _ _ w _ _ _ => halfAt_all (Fm.D x i) (Formalism.EigenvalueLevelCeiling.plc w)

end GlobalTheory.HalfLabels

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicPolynomialLattices
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain
open NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links (PolF labLL)
open Formalism.L2.Host (embLL0)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmallSpan

variable {D : D7} {m n : ℕ}

open GlobalTheory.ExportSeries.Onto in

theorem exists_harm (w : Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m) (F : VV ℂ w.lam) :
    ∃ P ∈ harm m w B, harmFn m w B P = coefFn (RingHom.id ℂ) w.lam (F : Pol ℂ D.what₂.Tau n) := by
  obtain ⟨s, hs⟩ := GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta D m n w B hw hm
  have hs0 : ((s : ℤ) : ℂ) ≠ 0 := by exact_mod_cast s.ne_zero
  have key : ∀ u : GLR D n, harmFn m w B (fockGL m w B u (w.delta m)) =
      ((s : ℤ) : ℂ) • coefLin w.lam (actP w.lam (invTrK (u * B)) (ten fun τ => extremal ℂ n (w.lam τ))) := fun u => by
    funext x
    rw [harmFn_fockGL, hs, Pi.smul_apply, smul_eq_mul]
    congr 1
    change _ = coefFn _ _ _ _
    rw [coefFn_actP, _root_.mul_inv_rev, mul_assoc]
  have hle : (VV ℂ w.lam).map (coefLin w.lam) ≤ (harm m w B).map (harmFn m w B) := by
    rw [GlobalTheory.OrbitSpan.VV_eq_span_orbit, harm, Submodule.map_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have h2 := key (invTrK g * B⁻¹)
    rw [inv_mul_cancel_right, invTrK_invTrK] at h2
    refine (Submodule.smul_mem_iff _ hs0).1 ?_
    beta_reduce
    rw [← h2]
    exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩
  exact hle (Submodule.mem_map_of_mem F.2)

open GlobalTheory.ExportSeries.HarmLattice in

theorem harmLat_le_span {K₀ K : Type} [Field K₀] [NumberField K₀] [Field K] [NumberField K] (f : K₀ →+* K) (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K₀)) (O O' : Subring ℂ) (hO' : ∀ a : 𝓞 K, σ a ∈ O') (w : Weight D n) (B : GLR D n)
    (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m) {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hM : Submodule.IsLattice D.host.E M) {P : PolF D m n} (hP : P ∈ harmLat σ (fun τ => f.comp (emb τ)) O' m w B M) :
    P ∈ Submodule.span O' (harmLat (σ.comp f) emb O m w B M : Set (PolF D m n)) := by
  set N := Submodule.span O' (harmLat (σ.comp f) emb O m w B M : Set (PolF D m n))
  have hN : N ≤ (harm m w B).restrictScalars O' := Submodule.span_le.2 fun Q hQ => hQ.1
  have hle : coefLatFn σ (fun τ => f.comp (emb τ)) O' w.lam M ≤ N.map ((harmFn m w B).restrictScalars O') := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨F, hF, rfl⟩
    have hF' := GlobalTheory.NabBC.nabBaseChange _ _ _ _ n f emb w.lam M hM hF
    rw [coefFn_eq, SetLike.mem_coe]
    clear hF
    induction hF' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, e⟩ := hy
      obtain ⟨Q, hQ, eQ⟩ := exists_harm w B hw hm (GlobalTheory.CoefModel.mapVV (σ.comp f) w.lam x)
      have e1 : harmFn m w B Q = coefFn (σ.comp f) w.lam (x : Pol K₀ D.what₂.Tau n) := eQ.trans (coefFn_eq _ _ x).symm
      refine ⟨Q, Submodule.subset_span ⟨hQ, ?_⟩, ?_⟩
      · exact Submodule.subset_span ⟨x, hx, e1⟩
      · refine eQ.trans (congrArg (cf w.lam) (Subtype.ext ?_))
        change MvPolynomial.map (σ.comp f) x.1 = MvPolynomial.map σ y.1
        rw [e, MvPolynomial.map_map]
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add, map_add]; exact add_mem h1 h2
    | smul a F _ h1 =>
      rw [← algebraMap_smul K a F, LinearMap.map_smulₛₗ, map_smul]
      exact Submodule.smul_mem _ (⟨σ a, hO' a⟩ : O') h1
  obtain ⟨Q, hQ, e⟩ := hle hP.2
  have h0 : P - Q = 0 := GlobalTheory.ExportSeries.HarmInj.harm_inj D m n w B hw hm _ (sub_mem hP.1 (hN hQ)) (by
    rw [map_sub, sub_eq_zero]
    exact e.symm)
  rw [sub_eq_zero.1 h0]
  exact hQ

theorem isLattice_latAt {S T : HSp D} {B : Base S T} (hF : B.F.Good) (h : Bridge.Gf S) :
    Submodule.IsLattice D.host.E (B.latAt h) :=
  Formalism.UG.P.global_lattice_isLattice_holds _ _ _ _ (Module.Finite.iff_fg.2 hF.sdS.1.fg) hF.sdS.1.span_eq_top _

theorem smallSt : GlobalTheory.BigOn.Exp.TupLe.SmallSt := by
  intro D _ _ _ _ _ _ _ _ _ p j _ _ B hB _ O O' _ hO' h P hP
  exact harmLat_le_span D.LL0.val.toRingHom D.what₂.embLL (labLL0 D) O O' hO'.int B.w B.F.BS hB.wt
    (GlobalTheory.CoefLatConj.pq_le hB) (isLattice_latAt hB.frame _) hP

end GlobalTheory.SmallSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterConjHalfIdeleEqProdLocalStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_conjHalfIdele_eq_prod_local : ∀ (D : D7) (Q : Finset (Pl D.host.E)) (eQ : AE D), IsIdemSum eQ Q → ∀ (k : D.host.Eˣ) (y : (AE D)ˣ), (y : AE D) = Formalism.L2.JoinChr.locE D (cA D eQ) (k : D.host.E) → ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ → ((c y : Circle) : ℂ) = ∏ P ∈ Q, ((ψ.locK (conjPl P) k : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.IdemSumChar.char_eq_prod | exact GlobalTheory.IdemSumChar.char_eq_prod | (intros; apply GlobalTheory.IdemSumChar.char_eq_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweFiniteLengthUniqueMaximalOfCyclicStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeAlg_of_cyclic_highest_weight : ∀ (T : Type) [Fintype T] [DecidableEq T] (R S : T → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ V), (∀ w, Good (a w)) → (∀ w w', w ≠ w' → ∀ Z Z' v, a w Z (a w' Z' v) = a w' Z' (a w Z v)) → ∀ (C : Submodule ℂ V) (α β α' β' : T → ℂ), (∀ w, QuadMod (a w) (α w) (β w) (α' w) (β' w) C ⊤) → (∀ B : ℚ, ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ ∀ μ : ∀ w, Ix (R w) (S w) → ℚ, (∀ w c, |μ w c| ≤ B) → (⨅ w, hwSub (a w) (μ w)) ≤ U ⊔ C) → (∃ (μ : ∀ w, Ix (R w) (S w) → ℚ) (v : V), (∀ w, v ∈ hwSub (a w) (μ w)) ∧ (∀ N : Submodule ℂ V, (∀ w, Stab (a w) N) → C ≤ N → v ∈ N → N = ⊤) ∧ (⨅ w, hwSub (a w) (μ w)) ≤ Submodule.span ℂ {v} ⊔ C) → HoweAlg a C := by
  first | exact @GlobalTheory.HoweR.howe_finiteLength_uniqueMaximal_of_cyclic | exact GlobalTheory.HoweR.howe_finiteLength_uniqueMaximal_of_cyclic | (intros; apply GlobalTheory.HoweR.howe_finiteLength_uniqueMaximal_of_cyclic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweQuotientFiniteLengthFockPolynomials
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem fock_pack : ∀ (P Q R S : ℕ) (x : ℂ), Pack (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro P Q R S x
  obtain ⟨-, hLie, -, hWt, -⟩ := GlobalTheory.T.fockActions_lie_rationalWeights_commute P Q R S
  obtain ⟨hStab, hAdm⟩ := GlobalTheory.T.fockCoinvariantKernel_stable_and_admissible P Q R S x
  obtain ⟨α, β, hq⟩ := GlobalTheory.T.fockSecondAction_quadraticIdentity_mod_coinvariants P Q R S x
  obtain ⟨α', β', hqt⟩ := GlobalTheory.T.negTranspose_fockSecondAction_quadratic_mod_coinvariants P Q R S x
  refine ⟨⟨hLie, hWt, GlobalTheory.T.fockAction_isLocallyBlockUnitary P Q R S⟩, hStab, ⟨α, β, α', β', fun a b v _ => ⟨hq a b v, hqt a b v⟩⟩, hAdm, GlobalTheory.T.fockCoinvariants_highestWeightCyclic_multiplicityOne P Q R S x⟩

end GlobalTheory.HoweR
end

