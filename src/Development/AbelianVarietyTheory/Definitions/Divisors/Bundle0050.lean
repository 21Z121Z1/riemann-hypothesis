import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.SupTrace
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle0001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.Bundle0003
import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Statement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsPlacePlane
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

namespace GlobalTheory.FieldPair.Model

variable {k K : Type} [Field k] [Field K] {c : k →+* K} {n : ℕ}

theorem not_contains_top (E : Place c) : ¬ E.Contains ⊤ := fun h =>
  E.ring_ne_top (ValuationSubring.ext _ _ fun x => ⟨fun _ => trivial, fun _ => h x trivial⟩)

theorem klt_top_iff (η : Forms c n) (φ : K →₀ ℚ) : Klt c n ⊤ η φ ↔ η ≠ 0 ∧ φ 0 = 0 :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun E hE => (not_contains_top E hE).elim⟩⟩

theorem disc_smul [PerfectField k] {x : Fin n → K} (hx : TrBasis c x) (E : Place c)
    {η : Forms c n} (hη : η ≠ 0) {f : K} (hf : f ≠ 0) (φ : K →₀ ℚ) :
    E.disc (f • η) (φ + Finsupp.single f 1) = E.disc η φ := by
  rw [Place.disc, Place.disc, E.formOrd_smul hx hη hf, map_add, Place.ordQ_single]
  push_cast
  ring

theorem klt_smul_iff [PerfectField k] {x : Fin n → K} (hx : TrBasis c x) (R : Subring K)
    {η : Forms c n} {f : K} (hf : f ≠ 0) (φ : K →₀ ℚ) :
    Klt c n R (f • η) (φ + Finsupp.single f 1) ↔ Klt c n R η φ := by
  have h0 : (φ + Finsupp.single f 1 : K →₀ ℚ) 0 = φ 0 := by
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hf.symm, add_zero]
  constructor
  · intro h
    have hη : η ≠ 0 := fun e => h.1 (by rw [e, smul_zero])
    exact ⟨hη, h0 ▸ h.2.1, fun E hE => disc_smul hx E hη hf φ ▸ h.lt_disc hE⟩
  · intro h
    exact ⟨smul_ne_zero hf h.1, h0 ▸ h.2.1,
      fun E hE => (disc_smul hx E h.1 hf φ).symm ▸ h.lt_disc hE⟩

theorem disc_single_mul (E : Place c) (η : Forms c n) {f g : K} (hf : f ≠ 0) (hg : g ≠ 0)
    (s : ℚ) : E.disc η (Finsupp.single (f * g) s) =
      E.disc η (Finsupp.single f s + Finsupp.single g s) := by
  rw [Place.disc, Place.disc, map_add, Place.ordQ_single, Place.ordQ_single, Place.ordQ_single,
    E.ord_mul hf hg]
  push_cast
  ring

theorem simple_pole (E : Place c) {ω : Forms E.const n} (hω : IsFreeGen E.ring ω)
    {t : E.ring} (ht : Irreducible t) :
    ¬ Klt c n E.ring.toSubring ((t : K)⁻¹ • E.toRat n ω) 0 ∧
      EffAt c n E.ring.toSubring ((t : K)⁻¹ • E.toRat n ω) 0 := by
  have h0 : (t : K)⁻¹ ≠ 0 := inv_ne_zero fun h => ht.ne_zero (Subtype.ext h)
  have h1 := smul_ne_zero h0 (E.toRat_ne_zero hω)
  rw [klt_ring_iff E h1 rfl, effAt_ring_iff E h1 rfl, Place.disc, E.formOrd_smul_toRat hω h0,
    E.ord_inv, E.ord_irreducible ht]
  norm_num

theorem simple_zero (E : Place c) {ω : Forms E.const n} (hω : IsFreeGen E.ring ω)
    {t : E.ring} (ht : Irreducible t) :
    Klt c n E.ring.toSubring ((t : K) • E.toRat n ω) 0 ∧
      ¬ EffAt c n E.ring.toSubring ((t : K) • E.toRat n ω) 0 := by
  have h0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
  have h1 := smul_ne_zero h0 (E.toRat_ne_zero hω)
  rw [klt_ring_iff E h1 rfl, effAt_ring_iff E h1 rfl, Place.disc, E.formOrd_smul_toRat hω h0,
    E.ord_irreducible ht]
  norm_num

theorem isEmpty_place_self : IsEmpty (Place (RingHom.id k)) :=
  ⟨fun E => not_contains_top E fun f _ => E.const_mem f⟩

section Scheme

variable {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem isPrimeOf_of_isAt {E : DivOver p} {x z : X} (hE : E.IsAt z) (hz : z ⤳ x) :
    (placeEquiv p E).IsPrimeOf (locRing x) := by
  refine ⟨hE.through hz, fun f hf => ?_⟩
  obtain ⟨a, rfl⟩ := (hE f).1 hf
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have hzU : z ∈ U := hz.mem_open U.isOpen hx
  letI := X.presheaf.algebra_section_stalk (⟨z, hzU⟩ : U)
  haveI := hU.isLocalization_stalk ⟨z, hzU⟩
  obtain ⟨⟨r, s⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl
    (S := X.presheaf.stalk z) a
  have hs : IsUnit (X.presheaf.germ U z hzU s.1) :=
    IsLocalization.map_units (M := (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl)
      (X.presheaf.stalk z) s
  have hs' : IsUnit (hE.equiv (X.presheaf.germ U z hzU s.1)) := hs.map hE.equiv.toRingHom
  have ho : (placeEquiv p E).ord
      (algebraMap _ X.functionField (X.presheaf.germ U z hzU s.1)) = 0 :=
    Place.ord_eq_zero (placeEquiv p E) (u := hE.equiv (X.presheaf.germ U z hzU s.1)) hs'
  have h1 (r : Γ(X, U)) :
      algebraMap _ X.functionField (X.presheaf.germ U z hzU r) ∈ locRing x :=
    ⟨X.presheaf.germ U x hx r, (algebraMap_germ hx r).trans (algebraMap_germ hzU r).symm⟩
  have h2 : algebraMap _ X.functionField (X.presheaf.germ U z hzU s.1) ≠ 0 :=
    (hs.map (algebraMap (X.presheaf.stalk z) X.functionField)).ne_zero
  have e' : a * X.presheaf.germ U z hzU s.1 = X.presheaf.germ U z hzU r := e
  refine ⟨_, h1 r, _, h1 s.1, h2, ho, ?_⟩
  rw [← map_mul, e']

theorem nonneg_of_effAt {Δ : X → ℚ} {η : RatForms p n} {x z : X} {m : ℕ}
    {g : X.functionFieldˣ} (h : IsLogEqn p Δ η x m g) (hm : 0 < m)
    (he : EffAt (Cartier.constFn p) n (locRing x) η
      (Finsupp.single (g : X.functionField) (1 / (m : ℚ))))
    {E : DivOver p} (hE : E.IsAt z) (hz : z ⤳ x) : 0 ≤ Δ z := by
  have := he.disc_le (isPrimeOf_of_isAt hE hz)
  rw [disc_placeEquiv, h.discrep_eq_neg hm hz hE] at this
  linarith

theorem exists_klt_smooth [PerfectField k] [SmoothOfRelativeDimension n p]
    (hn : topologicalKrullDim X = n) (x : X) :
    IsLocModel (Cartier.constFn p) (locRing x) ∧
      ∃ η φ, Klt (Cartier.constFn p) n (locRing x) η φ := by
  haveI := SmoothOfRelativeDimension.smooth n p
  obtain ⟨η, m, g, -, -, h⟩ := (kltAt_iff_exists_klt (p := p) (n := n) 0 x).1
    (kltAt_zero_of_smooth hn x)
  exact ⟨isLocModel_locRing x, η, _, h⟩

end Scheme

theorem projectiveSpace (d : ℕ) (x : (ProjVar.proj ℂ d).X) :
    IsLocModel (Cartier.constFn (ProjVar.proj ℂ d).str) (locRing x) ∧
      ∃ η φ, Klt (Cartier.constFn (ProjVar.proj ℂ d).str) (ProjVar.proj ℂ d).dim (locRing x) η φ :=
  exists_klt_smooth (ProjVar.Var.topologicalKrullDim_eq _) x

theorem dForm_blowup (c : k →+* K) (t u : K) :
    dForm c ![t, t * u] = t • dForm c ![t, u] := by
  rw [dForm_eq, dForm_eq]
  letI := c.toAlgebra
  have e1 : (fun i => dFun c (![t, t * u] i)) =
      Function.update (fun i => dFun c (![t, u] i)) 1 (t • dFun c u + u • dFun c t) := by
    funext i
    fin_cases i
    · simp
    · simp [dFun, Derivation.leibniz]
  have e2 : Function.update (fun i => dFun c (![t, u] i)) 1 (dFun c u) =
      fun i => dFun c (![t, u] i) := by
    funext i
    fin_cases i <;> simp
  rw [e1, AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
    AlternatingMap.map_update_smul, e2,
    AlternatingMap.map_eq_zero_of_eq _ (Function.update _ 1 (dFun c t)) (i := 0) (j := 1)
      (by simp) (by decide), smul_zero, add_zero]

theorem exists_chart [PerfectField k] (E : Place c) {x : Fin 2 → K} (hx : TrBasis c x) :
    ∃ t u : E.ring, Irreducible t ∧ IsUnit u ∧ IsUnit (u - 1) ∧
      IsFreeGen E.ring (dForm E.const ![t, u]) := by
  letI := E.const.toAlgebra
  letI := c.toAlgebra
  haveI : IsScalarTower k E.ring K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType k E.ring := E.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField k E.ring
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨m, z, b, hz, hb⟩ := exists_basis_kaehler_uniformiser k ht
  have h1 := trdeg_eq_of_basis_kaehler k K b
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := k) hx
  rw [h1, Cardinal.mk_fin] at h2
  obtain rfl : m = 1 := by
    have : 2 = m + 1 := by exact_mod_cast h2
    omega
  have key (w : E.ring) (hw : KaehlerDifferential.D k E.ring w = b 1) : IsUnit w := by
    by_contra hu
    have hm : w ∈ Ideal.span {t} := by
      rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht]
      exact hu
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton.1 hm
    rw [Derivation.leibniz, ← hz, ← hb 0] at hw
    have := congrArg (fun η => b.repr η 1) hw
    simp at this
    exact ht.not_isUnit (IsUnit.of_mul_eq_one _ (hz ▸ this))
  have ez : z = ![t, z 1] := by
    funext i
    fin_cases i
    · exact hz
    · rfl
  refine ⟨t, z 1, ht, key _ (hb 1).symm, key _ (by simp [hb 1]), ?_⟩
  rw [← ez]
  exact isFreeGen_dForm z b hb

theorem three_lines [PerfectField k] (E : Place c) {x : Fin 2 → K} (hx : TrBasis c x) :
    ∃ a b : K, a ∈ E.ring ∧ b ∈ E.ring ∧ dForm c ![a, b] ≠ 0 ∧ ∀ s : ℚ,
      E.disc (dForm c ![a, b])
        (Finsupp.single a s + Finsupp.single b s + Finsupp.single (b - a) s) = 1 - 3 * s ∧
      ∀ R : Subring K, E.Contains R → 2 / 3 ≤ s → ¬ Klt c 2 R (dForm c ![a, b])
        (Finsupp.single a s + Finsupp.single b s + Finsupp.single (b - a) s) := by
  obtain ⟨t, u, ht, hu, hu', hω⟩ := exists_chart E hx
  have h0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
  have e : dForm c ![(t : K), t * u] = (t : K) • E.toRat 2 (dForm E.const ![t, u]) := by
    have e' : E.toRat 2 (dForm E.const ![t, u]) = dForm c fun i => E.ring.subtype (![t, u] i) :=
      formMap_dForm (β := c) E.ring.subtype rfl _
    rw [dForm_blowup, e']
    congr 2
    funext i
    fin_cases i <;> rfl
  have o1 : E.ord ((t : K) * u) = 1 := by
    rw [E.ord_mul (g := u) h0 (hu.map E.ring.subtype).ne_zero, E.ord_irreducible ht, E.ord_eq_zero hu]
    rfl
  have o2 : E.ord ((t : K) * u - t) = 1 := by
    have : (t : K) * u - t = t * ((u - 1 : E.ring) : K) := by push_cast; ring
    rw [this, E.ord_mul (g := (u - 1 : E.ring)) h0 (hu'.map E.ring.subtype).ne_zero,
      E.ord_irreducible ht,
      E.ord_eq_zero hu']
    rfl
  have hd (s : ℚ) : E.disc (dForm c ![(t : K), t * u]) (Finsupp.single (t : K) s +
      Finsupp.single ((t : K) * u) s + Finsupp.single ((t : K) * u - t) s) = 1 - 3 * s := by
    rw [Place.disc, e, E.formOrd_smul_toRat hω h0, map_add, map_add, Place.ordQ_single,
      Place.ordQ_single, Place.ordQ_single, o1, o2, E.ord_irreducible ht]
    push_cast
    ring
  refine ⟨t, t * u, t.2, mul_mem t.2 u.2, e ▸ smul_ne_zero h0 (E.toRat_ne_zero hω),
    fun s => ⟨hd s, fun R hR hs h => ?_⟩⟩
  have := h.lt_disc hR
  rw [hd] at this
  linarith

theorem exists_place_plane :
    Nonempty (Place (Cartier.constFn (spMap (algebraMap k (Polynomial (Polynomial k)))))) ∧
    ∃ x : Fin 2 → (Sp (Polynomial (Polynomial k))).functionField,
      TrBasis (Cartier.constFn (spMap (algebraMap k (Polynomial (Polynomial k))))) x := by
  let z : Sp (Polynomial (Polynomial k)) := ⟨Ideal.span {Polynomial.X},
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X⟩
  have hz : Order.coheight z = 1 := by
    rw [← idealHeight_eq_coheight]
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (R := Polynomial (Polynomial k))
      (mem_nonZeroDivisors_of_ne_zero Polynomial.X_ne_zero) Polynomial.prime_X.not_unit
  haveI : Algebra.FiniteType k (Polynomial (Polynomial k)) :=
    .trans (S := Polynomial k) inferInstance inferInstance
  haveI : LocallyOfFiniteType (spMap (algebraMap k (Polynomial (Polynomial k)))) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)
  have hn : topologicalKrullDim (Sp (Polynomial (Polynomial k))) = (2 : ℕ) := by
    change topologicalKrullDim (PrimeSpectrum (Polynomial (Polynomial k))) = _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      Polynomial.ringKrullDim_of_isNoetherianRing, Polynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field]
    norm_num
  obtain ⟨E, -⟩ := DivOver.exists_isAt_of_coheight_eq_one
    (p := spMap (algebraMap k (Polynomial (Polynomial k)))) hz
  exact ⟨⟨placeEquiv _ E⟩, (isLocModel_locRing_and_exists_trBasis _ _ 2 z hn).2⟩

end GlobalTheory.FieldPair.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsLocCompIffEquiv
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

def SoleTerm {ι : Type} (C : ι → ℂ) (p q : ι → Prop) : Prop :=
  ∃ i, C i ≠ 0 ∧ p i ∧ ∀ i', C i' ≠ 0 → q i' → i' = i

theorem SoleTerm.mono {ι : Type} {C : ι → ℂ} {p q p' q' : ι → Prop} (h : SoleTerm C p q) (hp : ∀ i, p i → p' i)
    (hq : ∀ i, q' i → q i) : SoleTerm C p' q' := by
  obtain ⟨i, h0, h1, hu⟩ := h
  exact ⟨i, h0, hp i h1, fun j hj hj' => hu j hj (hq j hj')⟩

example : ¬ SoleTerm (![1, -1] : Fin 2 → ℂ) (fun _ => True) (fun _ => True) := by
  rintro ⟨i, -, -, hu⟩
  exact absurd ((hu 0 (by simp) trivial).trans (hu 1 (by simp) trivial).symm) (by decide)

example : SoleTerm (![2, 0] : Fin 2 → ℂ) (fun _ => True) (fun _ => True) :=
  ⟨0, by simp, trivial, fun i hi _ => by fin_cases i <;> simp_all⟩

example : SoleTerm (![2, -2] : Fin 2 → ℂ) (· = 0) (· = 0) := ⟨0, by simp, rfl, fun _ _ h => h⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def TraceIdC (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (geo : Set (Pl E) → (InfinitePlace E → DomWeight n) → (∀ w : Pl E, GLw n w → ℂ) → ℂ) : Prop :=
  ∀ S : Set (Pl E), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (GLw n w)),
    IsLevelFam (thL n) (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' →
    ∃ (ι : Type) (_ : Fintype ι) (t : ι → Term E n) (C : ι → ℂ), (∀ i, (t i).HasWt lam) ∧
      (∀ φ, IsTest (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' φ → (∃ w ∈ S, RegAt n w (φ w)) → geo S lam φ = spec S t C K' φ) ∧
      (∀ ρc : CuspSub E n, ρc.IsCsd → (∀ v : InfinitePlace E, ρc.HasInfChar v.embedding (infOfWeight (lam v))) →
        (∀ w ∈ S, ∃ τ : SmIrr (GLw n w), ρc.IsLocComp w τ ∧ fixed τ.ρ (K' w) ≠ ⊥) →
        SoleTerm C (fun i => ∀ w, ρc.IsLocComp w ((t i).P w)) (fun i => ∀ w ∈ S, ρc.IsLocComp w ((t i).P w)))

def STFC : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n, TraceIdC E n geomSt

def MainIdC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ),
    IsMu μ e → ∀ S : Set (Pl E), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
      (K₁ : ∀ (w : Pl E) a, Subgroup (GLw a w)) (K₂ : ∀ (w : Pl E) a, Subgroup (GLw (n - a) w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
    (∀ a ≤ n, IsLevelFam (thL a) (fun w : Pl E => GlobalTheory.LFun.KGL w a) (K₁ · a) ∧
      IsLevelFam (thL (n - a)) (fun w : Pl E => GlobalTheory.LFun.KGL w (n - a)) (K₂ · a)) →
    ∃ (ι : Type) (_ : Fintype ι) (T : ι → PairTerm E n μ) (C : ι → ℂ), (∀ j, (T j).D.HasWt lam) ∧
      (∀ ρc : CuspSub E n, ρc.IsCsd → (∀ v : InfinitePlace E, ρc.HasInfChar v.embedding (infOfWeight (lam v))) →
        (∀ w ∈ S, IsSplitAt w → ∃ τ : SmIrr (GLw n w), ρc.IsLocComp w τ ∧ fixed (τ.ρ.comp (UL n w).subtype) (K' w) ≠ ⊥) →
        (∀ w ∈ S, ¬ IsSplitAt w → ∃ τ : SmIrr (GLw n w), ρc.IsLocComp w τ ∧ fixed τ.ρ (K₁ w n) ≠ ⊥) →
        SoleTerm C (fun j => (T j).a = n ∧ ∀ w, ρc.IsLocComp w ((T j).D.P w))
          (fun j => ∀ᶠ w in cofinite, w ∈ S → IsSplitAt w → ρc.IsLocComp w ((T j).D.P w))) ∧
      ∀ (f : ∀ w : Pl E, UL n w → ℂ) (φ : ∀ (w : Pl E) a, GLw a w × GLw (n - a) w → ℂ), IsTest (KL n) K' f →
        (∀ a ≤ n, (∀ w, ¬ IsSplitAt w → IsHecke ((K₁ w a).prod (K₂ w a)) (φ w a) ∧ Match n a (n - a) w 1 (f w) (φ w a)) ∧
          ∀ᶠ w in cofinite, ¬ IsSplitAt w →
            φ w a = (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a)) : Subgroup _) : Set _).indicator 1) →
        (∃ w ∈ S, (∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) ∧
          (¬ IsSplitAt w → ∀ a ≤ n, RegAt2 a (n - a) w (φ w a))) →
        geomU S lam f = ∑ j, C j * ∏ᶠ w ∈ S, (T j).fac w (K' w) (f w) (K₁ w) (K₂ w) (φ w)

theorem isLocComp_iff_equiv {ρc : CuspSub E n} {w : Pl E} {σ : SmIrr (GLw n w)} (h : ρc.IsLocComp w σ)
    (τ : SmIrr (GLw n w)) : ρc.IsLocComp w τ ↔ Nonempty (τ.ρ.Equiv σ.ρ) :=
  ⟨fun h' => GlobalTheory.CuspRep.LocUniq.isLocComp_unique ρc w τ σ h' h,
    fun ⟨e⟩ => h.congr ((CuspSub.setoid E n).iseqv.refl ρc) ⟨e.symm⟩⟩

end GlobalTheory.BCT
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit
section
noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev blockAlg detbP OmP dMode)
open GlobalTheory.HCChar (dsChar)
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.PcEG

open GlobalTheory.PsCo.PcEF

variable {n : ℕ}

def OmDet : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), ∃ Q : Poly n, ∀ k ∈ Formalism.REAL.Kset ε, ev k Q * ev k (OmP ε).det = physDet ε k

def ClassFn : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (k k' : KG ε), physDet ε (toMK (k'⁻¹ * k * k')) = physDet ε (toMK k) ∧
    ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
      (T : Mat n → (W →L[ℂ] W)), Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T →
      trK T (toMK (k'⁻¹ * k * k')) = trK T (toMK k)

def GaInt : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∃ Λ m : Fin n → ℤ, gaW ε lam = (fun a => (Λ a : ℝ)) ∧ (∀ a b, a < b → ε a = ε b → Λ b ≤ Λ a) ∧
      (∀ a, lam a + ((n : ℝ) - 1) / 2 = m a) ∧
      ∀ a, (Λ + ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε) a = m a - if ε a then 0 else (pOf ε : ℤ)

def ToKType : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (γ : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (T : Mat n → (W →L[ℂ] W)), IsKIrr ε γ T →
    (∀ v w : W, PolyOnK ε fun k => ⟪w, T k v⟫_ℂ) →
    ∃ T₀ : S7.KType ε γ, ∀ k : S7.KG ε, ReciprocityTheory.ChartRestriction.TR.Weyl.kChar T₀ k = trK T (S7.toMK k)

def VdmSplit : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (t : Fin n → ℂ),
    (∏ a, ∏ b ∈ Finset.Ioi a, (t a - t b)) = ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε t * ((-1) ^ sDeg ε *
      ∏ x : GlobalTheory.PsCo.Pc1.Mode ε, (t x.1.1 - t x.1.2))

def PhysTor : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (θ : Fin n → ℝ),
    physDet ε (Matrix.diagonal (tor θ)) = (-1) ^ (pOf ε * qOf ε) * (∏ x : GlobalTheory.PsCo.Pc1.Mode ε, (tor θ x.1.1 - tor θ x.1.2)) *
      ∏ a, tor θ a ^ (-(if ε a then 0 else (pOf ε : ℤ))) ∧
    physDet ε (Matrix.diagonal (tor θ)) * conj (physDet ε (Matrix.diagonal (tor θ))) = (dMode ε θ : ℂ)

def NumShift : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (m : Fin n → ℤ) (c : Bool → ℤ) (t : Fin n → ℂ), (∀ a, t a ≠ 0) →
    ReciprocityTheory.ChartRestriction.TR.Weyl.numK ε (fun a => m a - c (ε a)) t =
      (∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) => ε ∘ w = ε),
        ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ a, t a ^ m (w.symm a)) * ∏ a, t a ^ (-c (ε a))

def RangeFD : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)) (hσ : IsURepOn (UJset ε) σ), Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ → ∀ d : ℕ,
    ∃ L : Submodule ℂ (smD ε σ), FiniteDimensional ℂ L ∧
      (∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ x ∈ L, sigD (isDerivedOn_smE hσ) hk x ∈ L) ∧
      ∀ P : Poly n, P.totalDegree ≤ d → ∀ u : H,
        ∫ k : KG ε, ev (toMK k) P • σ (toMK k) u ∂(muK ε) ∈ L.map (smD ε σ).subtype

def BuildY : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (c : ℂ), (∀ v : D, casimir E v = c • v) →
    ∀ L : Submodule ℂ D, FiniteDimensional ℂ L → (∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ x ∈ L, sigD hD hk x ∈ L) →
    ∃ Y : Submodule ℂ (TensorProduct ℂ D (Fock n)), FiniteDimensional ℂ Y ∧ tensFock L ⊓ physicalSubspace ε ≤ Y ∧
      Y ≤ physicalSubspace ε ∧ (∀ y ∈ Y, dD ε E y ∈ Y) ∧ (∀ y ∈ Y, gradT y ∈ Y) ∧
      ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y

def StrKer : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (Y : Submodule ℂ (TensorProduct ℂ D (Fock n)))
      [FiniteDimensional ℂ Y], (∀ y ∈ Y, dD ε E y ∈ Y) → ∀ (hG : ∀ y ∈ Y, gradT y ∈ Y)
      (hK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y),
    ∃ (Z : Submodule ℂ (TensorProduct ℂ D (Fock n))) (_ : FiniteDimensional ℂ Z)
      (hZK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Z, wK hD hk y ∈ Z) (Γ : TSub Z →ₗ[ℂ] TSub Z),
      Z ≤ Y ∧ (∀ y ∈ Z, dD ε E y = 0) ∧ ∀ (k : Mat n) (hk : k ∈ Kset ε),
        LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD hk).restrict (fun y hy => hG _ (hK k hk y hy))) =
          LinearMap.trace ℂ (TSub Z) (Γ ∘ₗ (tOp hD hZK k : TSub Z →ₗ[ℂ] TSub Z))

def StrIdx : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P : Poly n), ∃ d : ℕ,
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (L : Submodule ℂ D) [FiniteDimensional ℂ L],
    (∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ x ∈ L, sigD hD hk x ∈ L) →
    (∀ Q : Poly n, Q.totalDegree ≤ d → ∀ u : H,
      ∫ k : KG ε, ev (toMK k) Q • σ (toMK k) u ∂(muK ε) ∈ L.map D.subtype) →
    ∀ (Y : Submodule ℂ (TensorProduct ℂ D (Fock n))) [FiniteDimensional ℂ Y], tensFock L ⊓ physicalSubspace ε ≤ Y →
      Y ≤ physicalSubspace ε → ∀ (hG : ∀ y ∈ Y, gradT y ∈ Y)
      (hK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Y, wK hD hk y ∈ Y) (B : H →L[ℂ] H),
      (∀ w, B w = ∫ k : KG ε, (ev (toMK k) P * physDet ε (toMK k)) • σ (toMK k) w ∂(muK ε)) →
      ∃ hB : ∀ x, (B : H →ₗ[ℂ] H) x ∈ L.map D.subtype,
        LinearMap.trace ℂ (L.map D.subtype) ((B : H →ₗ[ℂ] H).restrict fun x _ => hB x) =
          ∫ k : KG ε, ev (toMK k) P * LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD (k := toMK k) k.2).restrict
            (fun y hy => hG _ (hK _ k.2 y hy))) ∂(muK ε)

def HWVec : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D),
    IsURepOn (UJset ε) σ → ∀ (hD : IsDerivedOn ε σ D E) (Z : Submodule ℂ (TensorProduct ℂ D (Fock n)))
      [FiniteDimensional ℂ Z] (hZK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Z, wK hD hk y ∈ Z)
      (γ : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
      (T : Mat n → (W →L[ℂ] W)), IsKIrr ε γ T → ∀ Φ : W →ₗ[ℂ] TSub Z, Φ ≠ 0 →
      (∀ k ∈ Formalism.REAL.Kset ε, ∀ v, Φ (T k v) = tOp hD hZK k (Φ v)) →
      ∃ z ∈ Z, z ≠ 0 ∧ IsKHWVec ε (diagE ε (eT E) cpT cmT) γ z

def CoordFD : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (Z : Submodule ℂ (TensorProduct ℂ M (Fock n))), FiniteDimensional ℂ Z →
    IsKStableSub ε (diagE ε (eT E) cpT cmT) Z →
    FiniteDimensional ℂ (coordSpan Z) ∧ IsKStableSub ε E (coordSpan Z)

def CasCoord : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M), IsGlRep E → ∀ z : TensorProduct ℂ M (Fock n),
    IsKHWVec ε (diagE ε (eT E) cpT cmT) (gaW ε lam) z → dD ε E z = 0 →
    ∀ s, casimir E (tco s z) = (casVal lam : ℂ) • tco s z

def AlgDatum : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Gap3 ε lam →
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (E : Fin n → Fin n → Module.End ℂ M),
    IsGlRep E → IsInfUnitary ε E → ∀ z : TensorProduct ℂ M (Fock n), z ≠ 0 → z ∈ physicalSubspace ε →
    IsKHWVec ε (diagE ε (eT E) cpT cmT) (gaW ε lam) z →
    (∀ s, casimir E (tco s z) = (casVal lam : ℂ) • tco s z) →
    ∀ S : Submodule ℂ M, FiniteDimensional ℂ S → IsKStableSub ε E S → (∀ s, tco s z ∈ S) →
    ∃ V : Submodule ℂ M, IsKIrrHW ε E (lowK ε lam) V ∧ V ≠ ⊥ ∧ ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v

def CptCase : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), pOf ε = 0 ∨ qOf ε = 0 →
    (∀ k, physDet ε k = 1) ∧ sDeg ε = 0 ∧
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (D : Mat n → (X →L[ℂ] X)), Formalism.MainNotions.S.IsDS ε lam D →
      FiniteDimensional ℂ X ∧ IsKIrr ε (gaW ε lam) D

def GapNum : Prop :=
  ∀ (r : ℕ), Odd r → ∀ (ε : Fin r → Bool) (lam : Fin r → ℤ),
    (∀ i j : Fin r, (j : ℕ) = i + 1 → 100 * (r : ℤ) ^ 4 ≤ lam i - lam j) →
    Formalism.QuantumDeterminants.IsHCParam (fun a => (lam a : ℝ)) ∧ StdGap ε (fun a => (lam a : ℝ)) ∧ Gap3 ε (fun a => (lam a : ℝ)) ∧
      ∃ h : ℝ, GapAtLeast ε (fun a => (lam a : ℝ)) h ∧ thrStar ε < h

def TorusId : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (Λ m : Fin n → ℤ), (∀ a, lam a + ((n : ℝ) - 1) / 2 = m a) →
    (∀ a, (Λ + ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε) a = m a - if ε a then 0 else (pOf ε : ℤ)) →
    ∀ θ : Fin n → ℝ, Function.Injective (tor θ) → ∀ x : ℂ,
      ReciprocityTheory.ChartRestriction.TR.Weyl.wdenK ε (tor θ) * x = ReciprocityTheory.ChartRestriction.TR.Weyl.numK ε (Λ + ReciprocityTheory.ChartRestriction.TR.Weyl.rhoK ε) (tor θ) →
      (-1) ^ sDeg ε * x = dsChar ε lam θ * physDet ε (Matrix.diagonal (tor θ))

end GlobalTheory.PsCo.PcEG
end
end

