import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0700
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2484
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2503
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2479
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomCompleteDVRPrincipalMaximalIdeal
section
open IsLocalRing

namespace GlobalTheory.PrincDvr

def powInf {B : Type} [CommRing B] (ϖ : B) : Ideal B := ⨅ n : ℕ, Ideal.span {ϖ ^ n}

variable {B : Type} [CommRing B] [IsLocalRing B] {ϖ : B}

theorem pow_not_mem_span_succ (hm : maximalIdeal B = Ideal.span {ϖ}) (hϖ : ϖ ∈ nonZeroDivisors B) (n : ℕ) :
    ϖ ^ n ∉ Ideal.span {ϖ ^ (n + 1)} := by
  intro h
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h
  have hn : ϖ ^ n ∈ nonZeroDivisors B := pow_mem hϖ n
  have e : (b * ϖ - 1) * ϖ ^ n = 0 := by linear_combination hb
  have e1 : b * ϖ - 1 = 0 := (mem_nonZeroDivisors_iff.1 hn).2 _ e
  have hmem : ϖ ∈ maximalIdeal B := by rw [hm]; exact Ideal.mem_span_singleton_self ϖ
  exact (mem_maximalIdeal _).1 hmem (isUnit_iff_exists_inv.2 ⟨b, by rw [mul_comm]; exact sub_eq_zero.1 e1⟩)

theorem exists_unit_mul_pow (hm : maximalIdeal B = Ideal.span {ϖ}) (x : B) (hx : x ∉ powInf ϖ) :
    ∃ (n : ℕ) (u : Bˣ), x = u * ϖ ^ n := by
  classical
  have hex : ∃ n, ¬ ϖ ^ n ∣ x := by
    by_contra h
    push_neg at h
    exact hx (Ideal.mem_iInf.2 fun n => Ideal.mem_span_singleton.2 (h n))
  obtain ⟨N, hN, hmin⟩ : ∃ N, ¬ ϖ ^ N ∣ x ∧ ∀ m < N, ϖ ^ m ∣ x :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => not_not.1 (Nat.find_min hex hm)⟩
  clear hex
  have hN0 : N ≠ 0 := by
    intro h0; apply hN; rw [h0, pow_zero]; exact one_dvd x
  obtain ⟨u, hu⟩ : ϖ ^ (N - 1) ∣ x := hmin _ (Nat.sub_lt (Nat.pos_of_ne_zero hN0) one_pos)
  have hu' : IsUnit u := by
    by_contra hu'
    have hmem : u ∈ Ideal.span {ϖ} := by rw [← hm]; exact (mem_maximalIdeal u).2 hu'
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hmem
    apply hN
    refine ⟨c, ?_⟩
    rw [hu, hc, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hN0)]
  exact ⟨N - 1, hu'.unit, by rw [hu, IsUnit.unit_spec, mul_comm]⟩

theorem isPrime_powInf (hm : maximalIdeal B = Ideal.span {ϖ}) (hϖ : ϖ ∈ nonZeroDivisors B) :
    (powInf ϖ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    intro h
    exact pow_not_mem_span_succ hm hϖ 0 (by simpa using Ideal.mem_iInf.1 h 1)
  · intro a b hab
    by_contra h
    push_neg at h
    obtain ⟨m, u, rfl⟩ := exists_unit_mul_pow hm a h.1
    obtain ⟨k, v, rfl⟩ := exists_unit_mul_pow hm b h.2
    have hmem := Ideal.mem_iInf.1 hab (m + k + 1)
    apply pow_not_mem_span_succ hm hϖ (m + k)
    have e1 : (u : B) * ϖ ^ m * (v * ϖ ^ k) = ((u * v : Bˣ) : B) * ϖ ^ (m + k) := by push_cast; ring
    have e : ϖ ^ (m + k) = (((u * v)⁻¹ : Bˣ) : B) * ((u : B) * ϖ ^ m * (v * ϖ ^ k)) := by
      rw [e1, Units.inv_mul_cancel_left]
    rw [e]
    exact Ideal.mul_mem_left _ _ hmem

theorem exists_cDvr_localHom : ∀ (B : Type) [CommRing B] [IsLocalRing B] (ϖ : B), maximalIdeal B = Ideal.span {ϖ} →
    ϖ ∈ nonZeroDivisors B → CharZero (ResidueField B) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W)
    (_ : IsLocalRing W) (h : B →+* W), GlobalTheory.LN.CDvr W ∧ IsLocalHom h ∧ h ϖ ≠ 0 := by
  intro B _ _ ϖ hm hϖ h0
  haveI := isPrime_powInf hm hϖ
  have hp0 : Ideal.Quotient.mk (powInf ϖ) ϖ ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    intro h
    exact pow_not_mem_span_succ hm hϖ 1 (by simpa using Ideal.mem_iInf.1 h 2)
  have hnu : ∀ a : B, ¬ IsUnit a → ∃ c, Ideal.Quotient.mk (powInf ϖ) a =
      Ideal.Quotient.mk (powInf ϖ) ϖ * Ideal.Quotient.mk (powInf ϖ) c := by
    intro a ha
    have hmem : a ∈ Ideal.span {ϖ} := by rw [← hm]; exact (mem_maximalIdeal a).2 ha
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    exact ⟨c, by rw [← hc, map_mul, mul_comm]⟩
  have hpu : ¬ IsUnit (Ideal.Quotient.mk (powInf ϖ) ϖ) := by
    rintro ⟨w, hw⟩
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (w⁻¹ : (B ⧸ powInf ϖ)ˣ).val
    have e : Ideal.Quotient.mk (powInf ϖ) (ϖ * c) = Ideal.Quotient.mk (powInf ϖ) 1 := by
      rw [map_mul, hc, ← hw, Units.mul_inv, map_one]
    have h1 := Ideal.mem_iInf.1 (Ideal.Quotient.eq.1 e) 1
    rw [pow_one] at h1
    have h2 : (1 : B) ∈ Ideal.span {ϖ} := by
      have := Ideal.sub_mem _ (Ideal.mul_mem_right c _ (Ideal.mem_span_singleton_self ϖ)) h1
      simpa using this
    exact pow_not_mem_span_succ hm hϖ 0 (by simpa using h2)
  have hirr : Irreducible (Ideal.Quotient.mk (powInf ϖ) ϖ) := by
    refine irreducible_iff.2 ⟨hpu, fun a b hab => ?_⟩
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    by_cases ha : IsUnit a'
    · exact Or.inl (ha.map _)
    · obtain ⟨c, hc⟩ := hnu a' ha
      right
      rw [hc, mul_assoc] at hab
      have e := mul_left_cancel₀ hp0 ((mul_one _).trans hab)
      exact isUnit_iff_exists_inv.2 ⟨_, by rw [mul_comm]; exact e.symm⟩
  have hfac : ∀ {x : B ⧸ powInf ϖ}, x ≠ 0 → ∃ n, Associated (Ideal.Quotient.mk (powInf ϖ) ϖ ^ n) x := by
    intro x hx
    obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : x' ∉ powInf ϖ := fun h => hx (Ideal.Quotient.eq_zero_iff_mem.2 h)
    obtain ⟨n, u, rfl⟩ := exists_unit_mul_pow hm x' hx'
    refine ⟨n, Units.map (Ideal.Quotient.mk (powInf ϖ)).toMonoidHom u, ?_⟩
    simp only [map_mul, map_pow, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    ring
  haveI : IsDiscreteValuationRing (B ⧸ powInf ϖ) :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨_, hirr, hfac⟩
  have hle : powInf ϖ ≤ RingHom.ker (residue B) := by
    intro a ha
    rw [RingHom.mem_ker, residue_eq_zero_iff, hm]
    simpa using Ideal.mem_iInf.1 ha 1
  have hc0 : CharZero (B ⧸ powInf ϖ) := RingHom.charZero (Ideal.Quotient.lift (powInf ϖ) (residue B) hle)
  have hloc : IsLocalHom (Ideal.Quotient.mk (powInf ϖ)) := ⟨fun a ha => by
    by_contra h
    obtain ⟨c, hc⟩ := hnu a h
    rw [hc] at ha
    exact hpu (isUnit_of_mul_isUnit_left ha)⟩
  obtain ⟨W, _, _, _, g, hW, hinj, hg⟩ := GlobalTheory.LocalCompletion.exists_cDvr_embedding (B ⧸ powInf ϖ) inferInstance
    inferInstance (IsDiscreteValuationRing.ringKrullDim_eq_one _) hc0
  refine ⟨W, inferInstance, inferInstance, inferInstance, g.comp (Ideal.Quotient.mk (powInf ϖ)), hW, ?_, ?_⟩
  · haveI := hloc; haveI := hg; infer_instance
  · intro h
    exact hp0 (hinj (by rw [map_zero]; exact h))

end GlobalTheory.PrincDvr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLtBinomialBoundOfMulPowLtStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lt_binomial_bound_of_mul_pow_lt : ∀ (c k : ℕ) (h d : ℚ), 1 ≤ k → 0 < h → (c : ℚ) * (k : ℚ) ^ k < h ^ k * d →
  ∃ q : ℚ, q < d ∧ ∀ l₀ : ℕ, ∃ l M : ℕ, l₀ ≤ l ∧ 1 ≤ M ∧ (k : ℚ) * l < h * M ∧ h < l ∧
    ((c * (M + k - 1).choose k : ℕ) : ℚ) < q * (l : ℚ) ^ k / k.factorial := by
  first | exact @GlobalTheory.elementary_binom_bound | exact GlobalTheory.elementary_binom_bound | (intros; apply GlobalTheory.elementary_binom_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapIntegralSchemeToGradedProjModel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.ToModel

theorem sep (R : Type) [CommRing R] (P : Scheme.{0}) (p : P ⟶ Sp R) [IsSeparated p] : P.IsSeparated := by
  refine ⟨?_⟩
  rw [terminal.hom_ext (terminal.from P) (p ≫ terminal.from _)]
  infer_instance

theorem gp_dom (Y : Scheme.{0}) [IsIntegral Y] : IsDominant (gp Y) := by
  refine ⟨?_⟩
  have h : genericPoint Y ∈ Set.range (gp Y) := ⟨closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
  refine Dense.mono (Set.singleton_subset_iff.2 h) ?_
  rw [dense_iff_closure_eq, (genericPoint_spec Y).def]

theorem regAt_pow {Y : Scheme.{0}} [IsIntegral Y] {y : Y} {x : Y.functionField} (h : RegAt y x) (m : ℕ) :
    RegAt y (x ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact (unitAt_one y).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem reg_div (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y) (k m : ℕ) (u a : Y.functionField) (y : Y)
    (ha : a ∈ Sec D (k * m)) (hu : y ∈ locus D k u) : RegAt y (a / u ^ m) := by
  obtain ⟨g, hg⟩ := D.exists_isEqn y
  have h1 := ((hg.nsmul (k * m)).regularAt_iff).1 (ha y)
  have h2 := ((hg.nsmul k).generatesAt_iff).1 hu
  have e : a / u ^ m = (a * ((g ^ (k * m) : Y.functionFieldˣ) : Y.functionField)) *
      ((u * ((g ^ k : Y.functionFieldˣ) : Y.functionField))⁻¹) ^ m := by
    have hg0 : ((g : Y.functionFieldˣ) : Y.functionField) ≠ 0 := Units.ne_zero _
    push_cast
    rw [inv_pow, mul_pow, ← pow_mul]
    field_simp
  rw [e]
  exact h1.mul (regAt_pow h2.inv.regAt m)

theorem locus_open (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y) (k : ℕ) (u : Y.functionField) :
    IsOpen (locus D k u) := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨g, hg, hu⟩ := hy
  obtain ⟨U, hyU, hU⟩ := hg.exists_nhds
  obtain ⟨V, hyV, hV⟩ := hu.exists_nhds
  exact ⟨(U ⊓ V : Y.Opens), fun z hz => ⟨g, hU z hz.1, hV z hz.2⟩, (U ⊓ V).2, ⟨hyU, hyV⟩⟩

theorem unitAt_pow {Y : Scheme.{0}} [IsIntegral Y] {y : Y} {x : Y.functionField} (h : UnitAt y x) (m : ℕ) :
    UnitAt y (x ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact unitAt_one y
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem unitAt_of_pow {Y : Scheme.{0}} [IsIntegral Y] {y : Y} {x : Y.functionField} (h : RegAt y x) {n : ℕ}
    (hn : 1 ≤ n) (hu : UnitAt y (x ^ n)) : UnitAt y x := by
  have hx : x ≠ 0 := fun h0 => hu.ne_zero (by rw [h0, zero_pow (by omega)])
  refine (unitAt_iff hx).2 ⟨h, ?_⟩
  have e : x⁻¹ = x ^ (n - 1) * (x ^ n)⁻¹ := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    field_simp
  rw [e]
  exact (regAt_pow h _).mul hu.inv.regAt

theorem locus_iff {Y : Scheme.{0}} [IsIntegral Y] (D : CartierDiv Y) {k k' : ℕ} (hk : 1 ≤ k)
    {u u' : Y.functionField} {y : Y} (hu : y ∈ locus D k u) (hu' : u' ∈ Sec D k') :
    y ∈ locus D k' u' ↔ UnitAt y (u' ^ k / u ^ k') := by
  obtain ⟨g, hg⟩ := D.exists_isEqn y
  have h2 := ((hg.nsmul k).generatesAt_iff).1 hu
  have h1 := ((hg.nsmul k').regularAt_iff).1 (hu' y)
  have e : u' ^ k / u ^ k' = (u' * ((g ^ k' : Y.functionFieldˣ) : Y.functionField)) ^ k *
      ((u * ((g ^ k : Y.functionFieldˣ) : Y.functionField))⁻¹) ^ k' := by
    have hg0 : ((g : Y.functionFieldˣ) : Y.functionField) ≠ 0 := Units.ne_zero _
    push_cast
    rw [inv_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm k' k]
    field_simp
  show (k' • D).GeneratesAt y u' ↔ _
  rw [(hg.nsmul k').generatesAt_iff, e]
  constructor
  · intro h
    exact (unitAt_pow h k).mul (unitAt_pow h2.inv k')
  · intro h
    refine unitAt_of_pow h1 hk ?_
    have e2 : (u' * ((g ^ k' : Y.functionFieldˣ) : Y.functionField)) ^ k =
        ((u' * ((g ^ k' : Y.functionFieldˣ) : Y.functionField)) ^ k *
          ((u * ((g ^ k : Y.functionFieldˣ) : Y.functionField))⁻¹) ^ k') *
        (u * ((g ^ k : Y.functionFieldˣ) : Y.functionField)) ^ k' := by
      have h0 : (u * ((g ^ k : Y.functionFieldˣ) : Y.functionField)) ≠ 0 := h2.ne_zero
      rw [inv_pow, _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ h0), _root_.mul_one]
    rw [e2]
    exact h.mul (unitAt_pow h2 k')

theorem pow_mem {R F : Type} [CommRing R] [Field F] {c₀ : R →+* F} {N : ℕ → Set F} (hN : GradedFam c₀ N)
    {k : ℕ} {b : F} (hb : b ∈ N k) (n : ℕ) : b ^ n ∈ N (k * n) := by
  induction n with
  | zero => simpa using hN.one
  | succ n ih => rw [pow_succ, Nat.mul_succ]; exact hN.mul _ _ _ ih _ hb

theorem exists_map_to_model : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] (ρ : R →+* R₁) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → (∀ k, ∀ a ∈ N k, θ a ∈ Sec D₁ k) → (∀ y : Y, ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, y ∈ locus D₁ k (θ b)) → ∃ m : Y ⟶ P, m ≫ p = q ≫ spMap ρ ∧ PFF (𝟙 _) m (θ.comp ψ) ∧ ∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b) := by
  intro R F _ _ _ c₀ N hN P _ p ψ Dp hM R₁ _ ρ Y _ q θ D₁ hc hsec hcov
  haveI : IsSeparated p := hM.sep
  haveI : P.IsSeparated := sep R P p
  choose k hk b hb hy using hcov
  have hb0 : ∀ y, b y ≠ 0 := fun y h => (hy y).ne_zero (by rw [h, map_zero])
  let U : Y → Y.Opens := fun y => ⟨locus D₁ (k y) (θ (b y)), locus_open Y D₁ _ _⟩
  have hyU : ∀ y, y ∈ U y := hy
  have hgen : ∀ y, genericPoint Y ∈ U y := fun y => gen_mem (hyU y)
  have hPη : ∀ y, genericPoint P ∈ Dp (k y) (b y) := fun y => (hM.gen _ (hk y) _ (hb y)).2 (hb0 y)
  have hreg : ∀ y (s : Γ(P, Dp (k y) (b y))), ∀ z ∈ U y, RegAt z ((θ.comp ψ) (fnOf _ (hPη y) s)) := by
    intro y s z hz
    obtain ⟨m, a, ha, he⟩ := (hM.ring _ (hk y) _ (hb y) (hb0 y) (ψ (fnOf _ (hPη y) s))).1
      ⟨_, fun z' hz' => regAt_fnOf hz' _ s, rfl⟩
    show RegAt z (θ (ψ _))
    rw [he, map_div₀, map_pow]
    exact reg_div Y D₁ (k y) m (θ (b y)) (θ a) z (hsec _ a ha) hz
  choose f hfV hf using fun y => GlobalTheory.T.exists_hom_to_affineOpen_of_functionField_map_regular Y P (U y) (hgen y) (Dp (k y) (b y)) (hM.affine _ (hk y) _ (hb y)) (hPη y)
    (θ.comp ψ) (hreg y)
  obtain ⟨m, hmU, hmg⟩ := GlobalTheory.T.exists_glue_morphisms_integral_agree_at_genericPoint Y P U hyU f (spMap (θ.comp ψ) ≫ gp P) hf
  refine ⟨m, ?_, ⟨gp Y, Category.comp_id _, hmg⟩, ?_⟩
  · haveI := gp_dom Y
    refine ext_of_isDominant (gp Y) ?_
    rw [reassoc_of% hmg, GlobalTheory.T.genericPoint_comp_structure_eq_specMap_constants P R p, ← Category.assoc, GlobalTheory.T.genericPoint_comp_structure_eq_specMap_constants Y R₁ q, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    change θ (ψ (cst p x)) = cst q (ρ x)
    have h1 := congrArg (fun g => g x) hc
    have h2 := congrArg (fun g => g x) hM.const
    simp only [RingHom.comp_apply] at h1 h2
    rw [h2, h1]
  · intro k' hk' b' hb' y
    have hmy : m y ∈ Dp (k y) (b y) := by
      have h1 := hfV y ⟨y, hyU y⟩
      rw [← hmU y] at h1
      exact h1
    rw [hM.mem _ (hk y) _ (hb y) _ hmy k' hk' b' hb']
    obtain ⟨v₀, hv₀, hψ⟩ := (hM.ring _ (hk y) _ (hb y) (hb0 y) (b' ^ (k y) / b y ^ k')).2
      ⟨k', b' ^ (k y), by rw [mul_comm]; exact pow_mem hN hb' _, rfl⟩
    have hst := GlobalTheory.T.regular_and_unit_preserved_by_functionField_compatible Y P m (θ.comp ψ) hmg y v₀ (hv₀ _ hmy)
    have hl := locus_iff D₁ (hk y) (hy y) (hsec _ _ hb')
    have e : (θ.comp ψ) v₀ = θ b' ^ (k y) / θ (b y) ^ k' := by
      rw [RingHom.comp_apply, hψ, map_div₀, map_pow, map_pow]
    rw [hl, ← e]
    constructor
    · rintro ⟨v, hv, hvw⟩
      obtain rfl : v = v₀ := ψ.injective (hvw.trans hψ.symm)
      exact hst.2.2 hv
    · intro h
      exact ⟨v₀, hst.2.1 h, hψ⟩

end GlobalTheory.Desc.ToModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatchingLineBundleGeneratorsNearPinchingPo
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.PinchLift

theorem exists_affine_nbhd_of_closedImm {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] (V : Z.Opens)
    (z : Z) (hz : z ∈ V) : ∃ W : X.Opens, IsAffineOpen W ∧ i z ∈ W ∧ i ⁻¹ᵁ W ≤ V := by
  obtain ⟨O, hO, hOV⟩ : ∃ O : Set X, IsOpen O ∧ i ⁻¹' O = V :=
    (i.isClosedEmbedding.isInducing.isOpen_iff).1 V.isOpen
  obtain ⟨W, hW, hzW, hWO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show i z ∈ (⟨O, hO⟩ : X.Opens) by show i z ∈ O; rw [← Set.mem_preimage, hOV]; exact hz)
  refine ⟨W, hW, hzW, fun y hy => ?_⟩
  have : i y ∈ O := hWO hy
  rw [← Set.mem_preimage, hOV] at this
  exact this

theorem gm_idHom_val {Y : Scheme.{0}} (y : Y) (U : Y.Opens) (h : y ∈ U) (a : Γ(Y, U)ˣ) :
    (gm (𝟙 Y) y U a).val = Y.presheaf.germ U y h a.val := by
  rw [gm_val (𝟙 Y) y U h]
  rfl

end GlobalTheory.PinchLift

namespace GlobalTheory.PinchLift

theorem near_matched : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (L' : LB X') (LZ : LB Z), L'.IsLB → LZ.IsLB → ∀ w : LB.Iso (L'.pull i') (LZ.pull p'), w.IsGen → ∀ z : Z, ∃ (W : X.Opens) (s' : ∀ k, Γ(X', L'.U k ⊓ p ⁻¹ᵁ W)ˣ) (sZ : ∀ j, Γ(Z, LZ.U j ⊓ i ⁻¹ᵁ W)ˣ), i z ∈ W ∧ GlobalTheory.PinchLift.GenOn L' (p ⁻¹ᵁ W) s' ∧ GlobalTheory.PinchLift.GenOn LZ (i ⁻¹ᵁ W) sZ ∧ GlobalTheory.PinchLift.Matched i' p' L' LZ w (p ⁻¹ᵁ W) (i ⁻¹ᵁ W) s' sZ := by
  intro X X' Z Z' p i i' p' hpb hp hi hg L' LZ hL' hLZ w hw z
  haveI : IsClosedImmersion i' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) hpb.flip hi
  have hc : ∀ z' : Z', p (i' z') = i (p' z') := fun z' => by
    have := congrArg (fun f : Z' ⟶ X => f z') hpb.w
    simpa using this
  obtain ⟨j₀, hj₀⟩ := exists_chart hLZ z
  obtain ⟨W₀, hW₀, hzW₀, hW₀j⟩ := exists_affine_nbhd_of_closedImm i (LZ.U j₀) z hj₀
  have hY : IsAffineOpen (p ⁻¹ᵁ W₀) := hW₀.preimage p
  have hZj : ∀ z' : Z', i' z' ∈ p ⁻¹ᵁ W₀ → p' z' ∈ LZ.U j₀ := fun z' h =>
    hW₀j (show i (p' z') ∈ W₀ from (hc z') ▸ h)

  have hpl : ∀ (z' : Z') (k k' : L'.ι) (hk : i' z' ∈ L'.U k) (hk' : i' z' ∈ L'.U k'),
      gm (𝟙 Z') z' ((L'.pull i').U (fun _ => k) ⊓ (L'.pull i').U (fun _ => k'))
        ((L'.pull i').g (fun _ => k) (fun _ => k')) = gm i' z' _ (L'.g k k') := by
    intro z' k k' hk hk'
    have hp : (𝟙 Z' : Z' ⟶ Z') z' ∈ (L'.pull i').U (fun _ => k) ⊓ (L'.pull i').U (fun _ => k') :=
      ⟨mem_pull.2 hk, mem_pull.2 hk'⟩
    show gm (𝟙 Z') z' _ (∏ _k : PUnit, (res _ (pullU i' _ (L'.g k k'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res _ z' _ hp _).trans ((gm_pull (𝟙 Z') i' z' (L'.U k ⊓ L'.U k') ⟨hk, hk'⟩ _).trans
      (by rw [Category.id_comp]))

  have hwst : ∀ (z' : Z') (j j' : LZ.ι) (k k' : L'.ι), p' z' ∈ LZ.U j → p' z' ∈ LZ.U j' → i' z' ∈ L'.U k →
      i' z' ∈ L'.U k' →
      gm (𝟙 Z') z' _ (w.s (fun _ => j, fun _ => k)) =
        gm p' z' _ (LZ.g j j') * (gm i' z' _ (L'.g k k'))⁻¹ * gm (𝟙 Z') z' _ (w.s (fun _ => j', fun _ => k')) := by
    intro z' j j' k k' hj hj' hk hk'
    have hm : (𝟙 Z' : Z' ⟶ Z') z' ∈ (LZ.pull p').U (fun _ => j) ⊓ (L'.pull i').U (fun _ => k) ⊓
        ((LZ.pull p').U (fun _ => j') ⊓ (L'.pull i').U (fun _ => k')) :=
      ⟨⟨mem_pull.2 hj, mem_pull.2 hk⟩, mem_pull.2 hj', mem_pull.2 hk'⟩
    have e := congrArg (gm (𝟙 Z') z' _) (hw (fun _ => j, fun _ => k) (fun _ => j', fun _ => k'))
    have hd := gm_div_g (F := p') (L := LZ) (L' := L'.pull i') (𝟙 Z') z' j j' (fun _ => k) (fun _ => k') hj hj'
      (mem_pull.2 hk) (mem_pull.2 hk')
    rw [hpl z' k k' hk hk', Category.id_comp] at hd
    rw [← hd]
    exact (gm_res _ z' _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ z' _ hm _))))

  have hle : ∀ k, i' ⁻¹ᵁ (L'.U k ⊓ p ⁻¹ᵁ W₀) ≤ (LZ.pull p').U (fun _ => j₀) ⊓ (L'.pull i').U (fun _ => k) :=
    fun k z' hz' => ⟨mem_pull.2 (hZj z' hz'.2), mem_pull.2 hz'.1⟩
  let τu : ∀ k, Γ(Z', i' ⁻¹ᵁ (L'.U k ⊓ p ⁻¹ᵁ W₀))ˣ := fun k => res (hle k) (w.s (fun _ => j₀, fun _ => k))⁻¹
  have hτu : ∀ (z' : Z') (k : L'.ι) (h : z' ∈ i' ⁻¹ᵁ (L'.U k ⊓ p ⁻¹ᵁ W₀)),
      gm (𝟙 Z') z' _ (τu k) = (gm (𝟙 Z') z' _ (w.s (fun _ => j₀, fun _ => k)))⁻¹ := by
    intro z' k h
    show gm (𝟙 Z') z' _ (res (hle k) (w.s (fun _ => j₀, fun _ => k))⁻¹) = _
    rw [gm_res _ z' _ h]; exact map_inv _ _
  have hτ : ∀ (k l : L'.ι) (z' : Z') (hk : z' ∈ i' ⁻¹ᵁ (L'.U k ⊓ p ⁻¹ᵁ W₀))
      (hl : z' ∈ i' ⁻¹ᵁ (L'.U l ⊓ p ⁻¹ᵁ W₀)),
      Z'.presheaf.germ _ z' hk (τu k).val =
        Z'.presheaf.germ (i' ⁻¹ᵁ (L'.U k ⊓ L'.U l)) z' ⟨hk.1, hl.1⟩ ((i'.app _).hom (L'.g k l).val) *
          Z'.presheaf.germ _ z' hl (τu l).val := by
    intro k l z' hk hl
    have e : gm (𝟙 Z') z' _ (τu k) = gm i' z' (L'.U k ⊓ L'.U l) (L'.g k l) * gm (𝟙 Z') z' _ (τu l) := by
      rw [hτu z' k hk, hτu z' l hl, hwst z' j₀ j₀ k l (hZj z' hk.2) (hZj z' hk.2) hk.1 hl.1,
        gm_self hLZ p' z' (hZj z' hk.2), _root_.one_mul, _root_.mul_inv, inv_inv]
    have e' := congrArg Units.val e
    rw [Units.val_mul, gm_idHom_val z' _ hk, gm_idHom_val z' _ hl, gm_val i' z' (L'.U k ⊓ L'.U l) (show i' z' ∈ L'.U k ⊓ L'.U l from ⟨hk.1, hl.1⟩)] at e'
    exact e'
  obtain ⟨θ, hθc, hθi⟩ := GlobalTheory.T.lift_lineBundle_section_of_closedImmersion_affineOpen X' Z' i' L' hL' (p ⁻¹ᵁ W₀) hY (fun k => (τu k).val) hτ

  have hN : ∀ z' : Z', i' z' ∈ p ⁻¹ᵁ W₀ → i' z' ∈ ⨆ k, X'.basicOpen (θ k) := by
    intro z' h
    obtain ⟨k, hk⟩ := exists_chart hL' (i' z')
    have : z' ∈ i' ⁻¹ᵁ X'.basicOpen (θ k) := by
      rw [Scheme.preimage_basicOpen, hθi k, Scheme.basicOpen_of_isUnit _ (τu k).isUnit]
      exact ⟨hk, h⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, this⟩
  obtain ⟨b, hb1, hbN⟩ := GlobalTheory.T.exists_basicOpen_le_of_app_eq_one_of_isClosedImmersion' X' Z' i' (p ⁻¹ᵁ W₀) hY _ hN
  obtain ⟨s, ⟨hsp, hsi⟩, -⟩ := hg W₀ b 1 (by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, hb1, map_one, map_one])
  have hzW : i z ∈ X.basicOpen s := by
    show z ∈ i ⁻¹ᵁ X.basicOpen s
    rw [Scheme.preimage_basicOpen, hsi, Scheme.basicOpen_of_isUnit _ isUnit_one]
    exact hzW₀
  have hpW : p ⁻¹ᵁ X.basicOpen s = X'.basicOpen b := by rw [Scheme.preimage_basicOpen, hsp]
  have hWle : X.basicOpen s ≤ W₀ := X.basicOpen_le s
  have hbY : X'.basicOpen b ≤ p ⁻¹ᵁ W₀ := X'.basicOpen_le b

  have hunit : ∀ (k : L'.ι) (x : X'), x ∈ L'.U k → x ∈ X'.basicOpen b → x ∈ X'.basicOpen (θ k) := by
    intro k x hk hx
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (hbN hx)
    have hxY := hbY hx
    have hlU : x ∈ L'.U l ⊓ p ⁻¹ᵁ W₀ := X'.basicOpen_le (θ l) hl
    rw [Scheme.mem_basicOpen (X := X') (f := θ k) x ⟨hk, hxY⟩, hθc k l x ⟨hk, hxY⟩ hlU]
    refine IsUnit.mul ?_ ((Scheme.mem_basicOpen (X := X') (f := θ l) x hlU).1 hl)
    exact (L'.g k l).isUnit.map _
  have hle2 : ∀ k, L'.U k ⊓ p ⁻¹ᵁ X.basicOpen s ≤ L'.U k ⊓ p ⁻¹ᵁ W₀ :=
    fun k x hx => ⟨hx.1, hWle hx.2⟩
  have hle3 : ∀ k, L'.U k ⊓ p ⁻¹ᵁ X.basicOpen s ≤ X'.basicOpen (θ k) := fun k x hx =>
    hunit k x hx.1 (hpW ▸ hx.2)
  have hu : ∀ k, IsUnit ((X'.presheaf.map (homOfLE (hle2 k)).op).hom (θ k)) := by
    intro k
    have e := (RingedSpace.isUnit_res_basicOpen X'.toRingedSpace (θ k)).map
      (X'.presheaf.map (homOfLE (hle3 k)).op).hom
    have h2 : (homOfLE (hle2 k)).op = (homOfLE (X'.basicOpen_le (θ k))).op ≫ (homOfLE (hle3 k)).op :=
      Subsingleton.elim _ _
    rw [h2, Functor.map_comp, CommRingCat.comp_apply]
    exact e
  have hZle : ∀ j, LZ.U j ⊓ i ⁻¹ᵁ X.basicOpen s ≤ LZ.U j ⊓ LZ.U j₀ := fun j y hy => ⟨hy.1, hW₀j (hWle hy.2)⟩
  refine ⟨X.basicOpen s, fun k => (hu k).unit, fun j => res (hZle j) (LZ.g j j₀), hzW, ?_, ?_, ?_⟩
  · intro k l y hk hl hy
    apply Units.ext
    rw [Units.val_mul, gm_idHom_val y _ (show y ∈ L'.U k ⊓ p ⁻¹ᵁ X.basicOpen s from ⟨hk, hy⟩),
      gm_idHom_val y _ (show y ∈ L'.U k ⊓ L'.U l from ⟨hk, hl⟩),
      gm_idHom_val y _ (show y ∈ L'.U l ⊓ p ⁻¹ᵁ X.basicOpen s from ⟨hl, hy⟩),
      IsUnit.unit_spec, IsUnit.unit_spec, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact hθc k l y _ _
  · intro j l y hj hl hy
    have hy0 : y ∈ LZ.U j₀ := hW₀j (hWle hy)
    rw [gm_res _ y _ (show y ∈ LZ.U j ⊓ i ⁻¹ᵁ X.basicOpen s from ⟨hj, hy⟩),
      gm_res _ y _ (show y ∈ LZ.U l ⊓ i ⁻¹ᵁ X.basicOpen s from ⟨hl, hy⟩)]
    exact (gm_cocycle hLZ (𝟙 Z) y hj hl hy0).symm
  · intro z' j k hj hk hjW hkW
    have hkW' : i' z' ∈ X'.basicOpen b := hpW ▸ hkW
    have hY' : i' z' ∈ p ⁻¹ᵁ W₀ := hbY hkW'
    have h0 := hZj z' hY'
    have hs' : gm i' z' (L'.U k ⊓ p ⁻¹ᵁ X.basicOpen s) (hu k).unit = gm (𝟙 Z') z' _ (τu k) := by
      apply Units.ext
      rw [gm_val i' z' _ (show i' z' ∈ L'.U k ⊓ p ⁻¹ᵁ X.basicOpen s from ⟨hk, hkW⟩),
        gm_idHom_val z' _ (show z' ∈ i' ⁻¹ᵁ (L'.U k ⊓ p ⁻¹ᵁ W₀) from ⟨hk, hY'⟩), IsUnit.unit_spec]
      rw [← Scheme.Hom.germ_stalkMap_apply, TopCat.Presheaf.germ_res_apply, Scheme.Hom.germ_stalkMap_apply, hθi k]
    have e1 : gm (𝟙 Z') z' ((LZ.pull p').U (fun _ => j) ⊓ (L'.pull i').U (fun _ => k)) (w.s (fun _ => j, fun _ => k)) =
        gm p' z' _ (LZ.g j j₀) * (gm i' z' _ (L'.g k k))⁻¹ *
          gm (𝟙 Z') z' ((LZ.pull p').U (fun _ => j₀) ⊓ (L'.pull i').U (fun _ => k)) (w.s (fun _ => j₀, fun _ => k)) :=
      hwst z' j j₀ k k hj h0 hk hk
    have e2 : gm (𝟙 Z') z' _ (τu k) =
        (gm (𝟙 Z') z' ((LZ.pull p').U (fun _ => j₀) ⊓ (L'.pull i').U (fun _ => k)) (w.s (fun _ => j₀, fun _ => k)))⁻¹ :=
      hτu z' k ⟨hk, hY'⟩
    rw [gm_res _ z' _ (show p' z' ∈ LZ.U j ⊓ i ⁻¹ᵁ X.basicOpen s from ⟨hj, hjW⟩), hs', e2, e1,
      gm_self hL' i' z' hk, inv_one, _root_.mul_one, mul_inv_cancel_right]

end GlobalTheory.PinchLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNonzeroLocusOfWeightZeroExpansionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_nonzeroLocus_of_weightZero_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (τ : U.SecGT (𝟙_ _) 1) (g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α), U.ExpT (𝟙_ _) 1 τ g → GlobalTheory.PsiRing.FibNZ (𝟙_ _ ⊗ D.P.A).hom (g 0) → (∀ α, α ≠ 0 → ∃ a ∈ maximalIdeal R, ∃ h : GlobalTheory.UU.SecBT D (𝟙_ _) 1 α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom a (g α) h) → ∃ θ : LB.Sec U.P.L.L, ∃ x ∈ nonzeroLocus θ, G.hom x = closedPoint R := by
  first | exact @GlobalTheory.PreUTheta.exists_mem_nonzeroLocus | exact GlobalTheory.PreUTheta.exists_mem_nonzeroLocus | (intros; apply GlobalTheory.PreUTheta.exists_mem_nonzeroLocus <;> assumption)
end

