import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0035
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0006
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.WeilBound.CoreStatements.HodgeTatePoints.ChSplit
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import ReciprocityTheory.DualLattices.Bundle0005
import ReciprocityTheory.DualLattices.Bundle0018
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0006
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0013
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0036
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0031
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.DifferentIdealLogSumRootDiscriminantStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0004
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0005
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0006
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0020
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0029
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0028
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0033

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartRingsNoetherianFractionStatement
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_rings_noetherian_fraction : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), (∀ c, IsNoetherianRing (chartRing O (mseg x) c)) ∧ (fnField O x = ⊤ → ∀ c, mseg x c ≠ 0 → IsFractionRing (chartRing O (mseg x) c) Ω) ∧ ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), (fnField O x = ⊤ → fnField O (joinCoord x z) = ⊤) ∧ ∀ c, mseg (joinCoord x z) c ≠ 0 → mseg x (restrictChart c) ≠ 0 ∧ (chartRing O (mseg x) (restrictChart c)) ≤ (chartRing O (mseg (joinCoord x z)) c) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.ChartNoethFrac.main | exact GlobalTheory.CompanionTheory.Ar.Num.ChartNoethFrac.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.ChartNoethFrac.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeMonoLatticeLeStatement
section
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_mono_lattice_le : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L L' : C.I → AddSubgroup V), IsBun C L → IsBun C L' → (∀ i, L i ≤ L' i) → deg C L ≤ deg C L' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.deg_le_deg_of_le | exact GlobalTheory.CompanionTheory.Ar.Crv.deg_le_deg_of_le | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.deg_le_deg_of_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DegreeSumEigenSubDegrees
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem degree_eq_sum_eigen : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Module.End K V, IsBun C L → (∀ a, IsHom C L L (ρ a)) → deg C L = ∑ s, subDeg C L (eig (fun a => ρ a) (fun a => algebraMap k K (χ s a))) :=
  @PositivityTheory.HtPt.Ch.split_deg

end GlobalTheory.CompanionTheory.Ar.Crv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentIdealAutomorphismInvariantStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.different_ideal_automorphism_invariant : ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (d : 𝓞 E), s d ∈ differentIdeal ℤ (𝓞 E) ↔ d ∈ differentIdeal ℤ (𝓞 E) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.mem_differentIdeal_ringEquiv_iff | exact GlobalTheory.CompanionTheory.Ar.mem_differentIdeal_ringEquiv_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.mem_differentIdeal_ringEquiv_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DivisibleGroupTowerCompatibilityStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisible_group_tower_compatibility : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ), (∀ (φ : La →+ La) (dφ : L →ₗ[O] L), X.Acts φ dφ → ∃ f : G ⟶ G, (∀ a, tateMap G G O f (τ a) = τ (φ a)) ∧ ∀ n (g : G.A n) (a : La), (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a))) ∧ ∀ (H : PDivGroup p O) (f f' : G ⟶ H), (∀ a, tateMap G H O f (τ a) = tateMap G H O f' (τ a)) → f = f' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.tower_end_pdiv | exact GlobalTheory.CompanionTheory.Ar.HT.tower_end_pdiv | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.tower_end_pdiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DotDualSubDegreeAnnihilatorStatement
section
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dot_dual_sub_degree_annihilator : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W X : Submodule K (Fin d → K)), IsBun C L → (∀ u, u ∈ W ↔ ∀ φ ∈ X, u ⬝ᵥ φ = 0) → subDeg C (dotDual C L) X = deg C (dotDual C L) + subDeg C L W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.subDeg_dotDual_orth | exact GlobalTheory.CompanionTheory.Ar.Crv.subDeg_dotDual_orth | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.subDeg_dotDual_orth <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsSplitIdempotentConjugation
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem exists_addChar_ne_one (C F : Type) [Field C] [IsAlgClosed C] [CharZero C] [Field F]
    [Finite F] : ∃ ψ : AddChar F C, ψ ≠ 1 := by
  have hch : ringChar C ≠ ringChar F := by
    rw [ringChar.eq_zero]
    exact (CharP.char_ne_zero_of_finite F (ringChar F)).symm
  let P := AddChar.FiniteField.primitiveChar F C hch
  haveI : NeZero (P.n : ℕ) := ⟨P.n.ne_zero⟩
  haveI : Algebra.IsIntegral C (CyclotomicField P.n C) :=
    IsCyclotomicExtension.integral {(P.n : ℕ)} C _
  let j : CyclotomicField P.n C →ₐ[C] C := IsAlgClosed.lift
  let ψ : AddChar F C :=
    { toFun := fun a => j (P.char a)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a b => by simp [AddChar.map_add_eq_mul] }
  refine ⟨ψ, fun h => ?_⟩
  refine P.prim one_ne_zero ?_
  ext a
  have h1 : j (P.char a) = 1 := by
    have := congrArg (fun χ : AddChar F C => χ a) h
    simpa [ψ] using this
  have h2 : P.char a = 1 := j.toRingHom.injective (by simpa using h1)
  simpa [AddChar.mulShift_apply] using h2

theorem exists_shift_equiv {C F : Type} [Field C] [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F C) (hψ : ψ ≠ 1) :
    ∃ e : F ≃ AddChar F C, (∀ h h', e (h + h') = e h * e h') ∧ ∀ h a, e h a = ψ (h * a) :=
  _root_.UpperTheory.Reformulated.B.AddCharacterCount.main ψ hψ

theorem rank_one_sum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∃ AD : HopfOrder (C := C) R F, FStable F AD.carrier ∧ (∀ cN cD, HasColen R v AA.carrier cN → HasColen R v AD.carrier cD → (cN * cD) ^ 2 = v (p : C) ^ (f * p ^ f)) ∧ ∀ τ : MulChar F R, IsFund p τ → ∀ c cD : R, xIdeal AA.carrier τ = Ideal.span {c} → xIdeal AD.carrier τ = Ideal.span {cD} → (v (algebraMap R C c) * v (algebraMap R C cD)) ^ (p - 1) = v (p : C) := by
  intro p _ C _ _ _ v R _ _ hv hvp F _ _ _ _ f hcard AA hFS
  obtain ⟨ψ, hψ⟩ := exists_addChar_ne_one C F
  obtain ⟨e, he, heψ⟩ := exists_shift_equiv ψ hψ
  obtain ⟨AD, hAD, -, hcol⟩ := h1 C R v hv F F e he rfl AA
  have hfun : (fun (h a : F) => e h a) = fun (h a : F) => ψ (h * a) := by
    funext h a; exact heψ h a
  rw [hfun] at hAD
  obtain ⟨hFD, hdual⟩ := GlobalTheory.T.dual_hopf_order_gauss_sum p C v R hv hvp F f hcard AA hFS ψ hψ AD hAD
  refine ⟨AD, hFD, ?_, ?_⟩
  · intro cN cD hN hD
    rw [hcol cN cD hN hD, hcard, Nat.cast_pow, map_pow, ← pow_mul]
  · intro τ hτ c cD hc hcD
    have hord := (GlobalTheory.T.teichmuller_character_order_generates p C v R hv hvp F f hcard τ hτ).1
    by_cases h2 : Fintype.card F = 2
    · have hpf : p ^ f = 2 := hcard.symm.trans h2
      obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 hpf
      have ht : τ = 1 := orderOf_eq_one_iff.1 (by rw [hord]; norm_num)
      have hN := (GlobalTheory.T.fundamental_character_ideal_powers 2 C v R hv hvp F 1 hcard AA hFS τ hτ (fun _ => c)
        (fun m => by rw [ht, one_pow, ← ht]; exact hc)).2.2
      have hD := (GlobalTheory.T.fundamental_character_ideal_powers 2 C v R hv hvp F 1 hcard AD hFD τ hτ (fun _ => cD)
        (fun m => by rw [ht, one_pow, ← ht]; exact hcD)).2.2
      have hI : Finset.Icc 1 (2 ^ 1 - 1) = ({1} : Finset ℕ) := by decide
      rw [hI, Finset.prod_singleton] at hN hD
      have key := hcol _ _ hN hD
      rw [h2] at key
      have := (pow_left_inj₀ zero_le zero_le two_ne_zero).1 key
      simpa using this
    · have hne : τ ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hord
        apply h2
        rw [hcard]
        have : 1 ≤ p ^ f := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
        omega
      rw [hdual τ hne c cD hc hcD]
      exact GlobalTheory.T.gauss_sum_valuation_teichmuller p C v R hv hvp F f hcard h2 τ hτ ψ hψ

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HermitianLogNormLocalSum
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.LocalSum

theorem finsum_lin {α : Type} {f g : α → ℝ} (hf : {x | f x ≠ 0}.Finite)
    (hg : {x | g x ≠ 0}.Finite) (a b : ℝ) :
    (∑ᶠ x, (a * f x + b * g x)) = a * (∑ᶠ x, f x) + b * ∑ᶠ x, g x := by
  rw [mul_finsum, mul_finsum, finsum_add_distrib]
  · exact hf.subset fun x hx h => hx (by simp [h])
  · exact hg.subset fun x hx h => hx (by simp [h])

theorem finite_lin {α : Type} {f g : α → ℝ} (hf : {x | f x ≠ 0}.Finite)
    (hg : {x | g x ≠ 0}.Finite) (a b : ℝ) : {x | a * f x + b * g x ≠ 0}.Finite :=
  (hf.union hg).subset fun x hx => by
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hx (by simp [h.1, h.2])

theorem finsum_linear_combination_four {α : Type} {f g h i : α → ℝ} (hf : {x | f x ≠ 0}.Finite)
    (hg : {x | g x ≠ 0}.Finite) (hh : {x | h x ≠ 0}.Finite) (hi : {x | i x ≠ 0}.Finite)
    (a b c d : ℝ) :
    (∑ᶠ x, (a * f x + (b * g x + (c * h x + d * i x)))) =
      a * (∑ᶠ x, f x) + (b * (∑ᶠ x, g x) + (c * (∑ᶠ x, h x) + d * ∑ᶠ x, i x)) := by
  have sm : ∀ (c : ℝ) (u : α → ℝ), {x | u x ≠ 0}.Finite →
      (Function.support fun x => c * u x).Finite :=
    fun c u hu => hu.subset fun x hx h => hx (by simp [h])
  have sa : ∀ (u v : α → ℝ), (Function.support u).Finite → (Function.support v).Finite →
      (Function.support fun x => u x + v x).Finite :=
    fun u v hu hv => (hu.union hv).subset (Function.support_add u v)
  rw [finsum_add_distrib (sm a f hf) (sa _ _ (sm b g hg) (sa _ _ (sm c h hh) (sm d i hi))),
    finsum_add_distrib (sm b g hg) (sa _ _ (sm c h hh) (sm d i hi)),
    finsum_add_distrib (sm c h hh) (sm d i hi)]
  simp only [mul_finsum]

theorem two_log_norm {E A : Type} [Field E] [NormedField A] (j : E →+* A) {r : E} {d : ℕ}
    (hr : r ^ 2 = -(d : E)) : 2 * Real.log ‖j r‖ = Real.log ‖(d : A)‖ := by
  have h1 : (j r) ^ 2 = -(d : A) := by rw [← map_pow, hr]; simp
  have h2 : ‖j r‖ ^ 2 = ‖(d : A)‖ := by rw [← norm_pow, h1, norm_neg]
  rw [← h2, Real.log_pow]
  norm_num

theorem deg_of_local_formulas : ∀ (k E : Type) [Field k] [NumberField k] [Field E] [NumberField E] (τ : E →+* k) (N : LogNorms k) (ρ : k) (a r : E) (p q d : ℕ) (n : (k →+* ℂ) → ℝ) (x : ℝ) (t t' : Nat.Primes → E), ρ ≠ 0 → a ≠ 0 → 0 < d → r ^ 2 = -(d : E) → -(∑ s, Real.log (n s)) / Module.finrank ℚ k = x → (∀ s, N.inf s = Real.log ‖s ρ‖ + ((p : ℝ) - q) / 2 * (Real.log (n s) + Real.log d / 2) + Real.log ‖s (τ a)‖ / 2) → (∀ ℓ : Nat.Primes, ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t' ℓ)‖ = ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖) → (∀ (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]), Real.log ‖j (t ℓ)‖ + Real.log ‖j (t' ℓ)‖ + Real.log ‖j a‖ = -((p : ℝ) + q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → {ℓ : Nat.Primes | ∃ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ ≠ 0}.Finite → (∀ (ℓ : Nat.Primes) (j : k →+* ℂ_[ℓ]), N.fin ℓ j + q * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) = Real.log ‖j ρ‖ - Real.log ‖j (τ (t ℓ))‖ - q * logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((q : ℝ) - p) * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (τ r)‖)) → N.IsAdelic ∧ N.deg = ((p : ℝ) - q) / 2 * (x - Real.log (rootDiscr E) + Real.log (Real.sqrt d)) + q * (2 * Real.log (Real.sqrt d) - Real.log (rootDiscr E)) := by
  intro k E _ _ _ _ τ N ρ a r p q d n x t t' hρ ha hd hr hx hinf htt' htt hfin hN
  have hm : (Module.finrank ℚ k : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have he : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hdk : (d : k) ≠ 0 := by exact_mod_cast hd.ne'
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set m : ℝ := ((Module.finrank ℚ k : ℕ) : ℝ) with hmdef
  set e : ℝ := ((Module.finrank ℚ E : ℕ) : ℝ) with hedef

  have hloc : ∀ (ℓ : Nat.Primes) (j : k →+* ℂ_[ℓ]), N.fin ℓ j = Real.log ‖j ρ‖ - Real.log ‖j (τ (t ℓ))‖
      - ((p : ℝ) + q) * logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
      + ((p : ℝ) + q) / 2 * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ := by
    intro ℓ j
    have h1 := hN ℓ j
    have h2 : 2 * Real.log ‖j (τ r)‖ = Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ := two_log_norm (j.comp τ) hr
    linear_combination h1 + (((p : ℝ) - q) / 2) * h2
  constructor
  · have S1 := GlobalTheory.T.log_norms_of_nonzero_adelic k ρ hρ
    have S4 := GlobalTheory.T.log_norms_of_nonzero_adelic k (d : k) hdk
    have S3 := GlobalTheory.T.logIdeal_support_finite E (differentIdeal ℤ (𝓞 E)) differentIdeal_ne_bot
    refine (((S1.union S4).union S3).union hfin).subset ?_
    rintro ℓ ⟨j, hj⟩
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_not] at h
    obtain ⟨⟨⟨h1, h4⟩, h3⟩, h2⟩ := h
    apply hj
    have e1 : Real.log ‖j ρ‖ = 0 := h1 j
    have e2 : Real.log ‖j (τ (t ℓ))‖ = 0 := h2 (j.comp τ)
    have e3 := h3 ((j.comp τ).comp (algebraMap (𝓞 E) E))
    have e4 : Real.log ‖j (d : k)‖ = 0 := h4 j
    rw [map_natCast] at e4
    rw [hloc, e1, e2, e3, e4]
    simp
  ·
    have hcard : ∀ ℓ : Nat.Primes, ((Fintype.card (k →+* ℂ_[ℓ]) : ℕ) : ℝ) = m := fun ℓ => by
      rw [hmdef, Embeddings.card]
    have hcardC : ((Fintype.card (k →+* ℂ) : ℕ) : ℝ) = m := by rw [hmdef, Embeddings.card]
    have hDd : ∀ ℓ : Nat.Primes, (LogNorms.ofElt (d : k)).finSum ℓ = m * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ := by
      intro ℓ
      simp only [LogNorms.finSum, LogNorms.ofElt, map_natCast, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hcard]
    have hsum : ∀ ℓ : Nat.Primes, N.finSum ℓ = 1 * (LogNorms.ofElt ρ).finSum ℓ
        + (((m / e) * (1 / 2)) * (LogNorms.ofElt a).finSum ℓ
        + ((-(m / e) * (((p : ℝ) + q) / 2)) * (∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)))
        + (((p : ℝ) + q) / 2) * (LogNorms.ofElt (d : k)).finSum ℓ)) := by
      intro ℓ
      have f1 := GlobalTheory.T.sum_embeddings_base_change E k ℂ_[ℓ] τ (fun i => Real.log ‖i (t ℓ)‖)
      have f2 := GlobalTheory.T.sum_embeddings_base_change E k ℂ_[ℓ] τ
        (fun i => logIdeal (i.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)))
      have g1 : ∑ j : E →+* ℂ_[ℓ], (Real.log ‖j (t ℓ)‖ + Real.log ‖j (t' ℓ)‖ + Real.log ‖j a‖) =
          ∑ j : E →+* ℂ_[ℓ], -((p : ℝ) + q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) :=
        Finset.sum_congr rfl fun j _ => htt ℓ j
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, htt' ℓ, ← Finset.mul_sum] at g1
      have h0 : N.finSum ℓ = (LogNorms.ofElt ρ).finSum ℓ - ∑ j : k →+* ℂ_[ℓ], Real.log ‖(j.comp τ) (t ℓ)‖
          - ((p : ℝ) + q) * ∑ j : k →+* ℂ_[ℓ], logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))
          + ((p : ℝ) + q) / 2 * (m * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) := by
        have c1 : ∑ j : k →+* ℂ_[ℓ], ((p : ℝ) + q) / 2 * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖ =
            ((p : ℝ) + q) / 2 * (m * Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; ring
        rw [← c1, Finset.mul_sum]
        simp only [LogNorms.finSum, LogNorms.ofElt, hloc, RingHom.comp_apply,
          ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      have hT : ∑ j : k →+* ℂ_[ℓ], Real.log ‖(j.comp τ) (t ℓ)‖ =
          (m / e) * ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ := by
        rw [div_mul_eq_mul_div, eq_div_iff he, mul_comm]
        exact f1
      have hD : ∑ j : k →+* ℂ_[ℓ], logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) =
          (m / e) * ∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := by
        rw [div_mul_eq_mul_div, eq_div_iff he, mul_comm]
        exact f2
      have hae : (LogNorms.ofElt a).finSum ℓ = ∑ j : E →+* ℂ_[ℓ], Real.log ‖j a‖ := rfl
      rw [h0, hDd, hT, hD, hae]
      linear_combination (-(m / e) / 2) * g1
    have hA := GlobalTheory.T.product_formula_log_norms k ρ hρ
    have hE := GlobalTheory.T.product_formula_log_norms E a ha
    have hG := GlobalTheory.T.product_formula_log_norms k (d : k) hdk
    have hΔ := GlobalTheory.T.different_ideal_log_sum_root_discriminant E
    have hfs : ∑ᶠ ℓ, N.finSum ℓ = 1 * (∑ᶠ ℓ, (LogNorms.ofElt ρ).finSum ℓ)
        + (((m / e) * (1 / 2)) * (∑ᶠ ℓ, (LogNorms.ofElt a).finSum ℓ)
        + ((-(m / e) * (((p : ℝ) + q) / 2)) * (∑ᶠ ℓ : Nat.Primes, ∑ j : E →+* ℂ_[ℓ], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)))
        + (((p : ℝ) + q) / 2) * (∑ᶠ ℓ, (LogNorms.ofElt (d : k)).finSum ℓ))) := by
      rw [finsum_congr hsum]
      exact finsum_linear_combination_four hA.1 hE.1 hΔ.1 hG.1 _ _ _ _
    have hlogn : ∑ s, Real.log (n s) = -(m * x) := by
      rw [← hx]; field_simp
    have hI : ∑ s, N.inf s = (∑ s : k →+* ℂ, Real.log ‖s ρ‖)
        + ((p : ℝ) - q) / 2 * ((∑ s, Real.log (n s)) + m * (Real.log d / 2))
        + (∑ s : k →+* ℂ, Real.log ‖s (τ a)‖) / 2 := by
      simp only [hinf]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hcardC, ← Finset.sum_div]
    have hAτ : ∑ s : k →+* ℂ, Real.log ‖s (τ a)‖ = (m / e) * ∑ s : E →+* ℂ, Real.log ‖s a‖ := by
      rw [div_mul_eq_mul_div, eq_div_iff he, mul_comm]
      exact GlobalTheory.T.sum_embeddings_base_change E k ℂ τ (fun i => Real.log ‖i a‖)
    have hdinf : ∑ s : k →+* ℂ, Real.log ‖s (d : k)‖ = m * Real.log d := by
      simp only [map_natCast, Complex.norm_natCast, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hcardC]
    have h1 := hA.2
    have h2 := hE.2
    have h3 := hG.2
    have h4 := hΔ.2
    rw [hdinf] at h3
    have hme : m / e * e = m := div_mul_cancel₀ _ he
    have key : (∑ s, N.inf s) + ∑ᶠ ℓ, N.finSum ℓ =
        m * (((p : ℝ) - q) / 2 * (-x + Real.log d / 2) + ((p : ℝ) + q) / 2 * Real.log (rootDiscr E)
          - ((p : ℝ) + q) / 2 * Real.log d) := by
      rw [hI, hfs, hlogn, hAτ, h4]
      linear_combination h1 + (m / e / 2) * h2 + (((p : ℝ) + q) / 2) * h3
        + ((((p : ℝ) + q) / 2) * Real.log (rootDiscr E)) * hme
    have hdiv : ∀ Y : ℝ, -(m * Y) / m = -Y := fun Y => by field_simp
    rw [LogNorms.deg, key, hdiv, Real.log_sqrt hdR.le]
    ring

end GlobalTheory.CompanionTheory.Ar.Fl.LocalSum
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeDivisorIdealLatticeStatement
section
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_divisor_ideal_lattice : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ i, D.dId R p (χ τ) i = D.xId (χ τ) i) ∧ (∀ τ (i : Fin n), (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) = D.kk τ i) ∧ ∀ τ i, (D.stepGraph (φ τ) (χ (φ τ)) i).comap (AddMonoidHom.inl _ _) = powSpan R p (D.xId (χ τ) i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HaSteps.main | exact GlobalTheory.CompanionTheory.Ar.Num.HaSteps.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HaSteps.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeImageLattice
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_span {E : Type} [AddCommGroup E] [Module Ω E] (R : Subalgebra o Ω) {S : Set E} {e : E}
    (h : e ∈ S) : e ∈ spanOver R S :=
  AddSubgroup.subset_closure ⟨1, R.one_mem, e, h, (one_smul _ _).symm⟩

theorem bc_smul {C : Type} [Field C] [Algebra Ω C] {ι : Type} (w : Ω) (v : ι → Ω) :
    bcMap Ω C ι (w • v) = algebraMap Ω C w • bcMap Ω C ι v := by
  funext i
  show algebraMap Ω C (w * v i) = algebraMap Ω C w * algebraMap Ω C (v i)
  rw [map_mul]

theorem pow_one_smul_mem {E : Type} [AddCommGroup E] [Module Ω E] {R : Subalgebra o Ω} {N : ℕ}
    {L : AddSubgroup E} (hL : LocFree R N L) {p : ℕ} {w : Ω} (hw : ∃ c ∈ R, (p : Ω) = c * w) {v : E}
    (hv : w • v ∈ L) : ∃ m : ℕ, (p : Ω) ^ m • v ∈ L := by
  obtain ⟨c, hc, e⟩ := hw
  refine ⟨1, ?_⟩
  rw [pow_one, e, mul_smul]
  exact hL.1 c hc _ hv

end GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence

open GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence in

theorem GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence.main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → ∀ τ, D.imH R p τ (χ τ) = D.om τ ∧ D.kerH R p τ (χ τ) = divLat w (D.lie τ) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hb hp hN hF hI φ hT hG hG2 τ
  have hle := GlobalTheory.T.hodge_annihilator_lattice_holds D R p w χ hc hb hp hN hF hI φ hT hG
  have hbc1 := GlobalTheory.T.lattice_image_base_change D R p w χ hc hb hG hle
  obtain ⟨hf2, hbc2⟩ := GlobalTheory.T.lattice_second_goodness D R p w χ hc hb hG hG2 hle
  have hp0 := hc.1
  have hw := hc.2.2.1
  obtain ⟨flie, -, fom, -⟩ := hb.free τ
  obtain ⟨i1, i2, i3, i4⟩ := hb.incl τ
  refine ⟨le_antisymm (fun v hv => ?_) (fun v hv => ?_), le_antisymm (fun v hv => ?_) (fun v hv => ?_)⟩
  · refine GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ fom v (pow_one_smul_mem fom hw ?_) ?_
    · obtain ⟨⟨b, c⟩, ⟨h, -⟩, rfl⟩ := hv
      exact i3 (((hb.del τ).2.1 c).1 ⟨b, h⟩)
    · intro C _ _ _ _ RC hRC
      have h : bcMap Ω C _ v ∈ (D.bc RC).imH RC p τ (fun a => algebraMap Ω C (χ τ a)) := by
        rw [hbc1 C RC hRC.2.2.2 τ]
        exact mem_span RC ⟨v, hv, rfl⟩
      have e := (hT C RC hRC).im τ
      exact e.le h
  · refine GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ (hG2.im τ) v (pow_one_smul_mem (hG2.im τ) hw ?_) ?_
    · exact ⟨(0, w • v), ⟨((hb.del τ).2.2.1 _).2 (i4 hv), zero_mem _, trivial⟩, rfl⟩
    · intro C _ _ _ _ RC hRC
      rw [← hbc1 C RC hRC.2.2.2 τ]
      have e := (hT C RC hRC).im τ
      exact e.ge (mem_span RC ⟨v, hv, rfl⟩)
  · show w • v ∈ D.lie τ
    refine GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ flie _ (pow_one_smul_mem flie hw ?_) ?_
    · obtain ⟨⟨a, b⟩, ⟨h, -⟩, rfl⟩ := hv
      exact i2 (((hb.gam τ).1 a).1 ⟨b, h⟩)
    · intro C _ _ _ _ RC hRC
      have h : bcMap Ω C _ v ∈ (D.bc RC).kerH RC p τ (fun a => algebraMap Ω C (χ τ a)) := by
        rw [((hbc2 C RC hRC.2.2.2).2 τ).1]
        exact mem_span RC ⟨v, hv, rfl⟩
      have e := (hT C RC hRC).ker τ
      rw [bc_smul]
      exact e.le h
  · have hv' : w • v ∈ D.lie τ := hv
    refine GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ (hf2 τ).1 v (pow_one_smul_mem (hf2 τ).1 hw ?_) ?_
    · exact ⟨(w • v, 0), ⟨((hb.gam τ).2.2 _).2 (i1 hv'), trivial, zero_mem _⟩, rfl⟩
    · intro C _ _ _ _ RC hRC
      rw [← ((hbc2 C RC hRC.2.2.2).2 τ).1]
      have e := (hT C RC hRC).ker τ
      refine e.ge ?_
      show algebraMap Ω C w • bcMap Ω C _ v ∈ (D.bc RC).lie τ
      rw [← bc_smul]
      exact mem_span RC ⟨_, hv', rfl⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDualPairingStatement
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_chart_dual_pairing : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d d' : A) (m : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), κ * (p : A) ^ m ∣ (p : A) ^ R → GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' → (∀ x ∈ D.om, κ • x ∈ D.om') → Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → D.HasTestPoints κ → D.IsDualMap σ d m i → ∀ w, ∃ y ∈ D.omHT σ, D.q σ (i w) = ((p : A) ^ m) • y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.chart_comp_zero_mod | exact GlobalTheory.CompanionTheory.Ar.HT.chart_comp_zero_mod | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.chart_comp_zero_mod <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderRetractElementary
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hopf_order_retract_elementary : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → IsTight v p AA.carrier → IsTight v p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) := by
  first | exact @PositivityTheory.HtPt.Re.ret_tight | exact PositivityTheory.HtPt.Re.ret_tight
end

