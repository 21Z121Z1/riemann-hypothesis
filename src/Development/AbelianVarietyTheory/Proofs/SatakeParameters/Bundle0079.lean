import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0076
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSplitProdRight
import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
import Formalism.GaussJetBounds.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0077
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvalueCoprimeConjugation
section
noncomputable section

namespace GlobalTheory.Proof.EigenvalueCoprimeConjugation

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual Formalism.CyclotomicNorms ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels GlobalTheory.WeilDeligne GlobalTheory.IndefiniteRowSideFullHecke.TameEigenvaluesTypePrimes

theorem conj_of_coprime {Γ : Type*} [Group Γ] (P : Subgroup Γ) [Finite P] (a b : Γ) (n : ℕ)
    (hP : ∀ x ∈ P, a * x * a⁻¹ ∈ P) (hn : (Nat.card P).Coprime n) (ha : a ^ n = 1) (hb : b ^ n = 1)
    (hab : b * a⁻¹ ∈ P) : ∃ u ∈ P, u * a * u⁻¹ = b := by
  obtain ⟨e, he0, he1⟩ := Nat.chineseRemainder hn 0 1
  have hpow : ∀ x : Γ, x ^ n = 1 → x ^ e = x := fun x hx => by
    have := pow_eq_pow_of_modEq he1 hx
    simpa using this
  have hc : ∀ c : P, (c : Γ) ^ e = 1 := fun c => by
    have h1 : c ^ e = 1 := by
      have := pow_eq_pow_of_modEq he0 (pow_card_eq_one' (x := c))
      simpa using this
    simpa using congrArg Subtype.val h1
  let C : Subgroup P := (Subgroup.centralizer {a}).subgroupOf P
  have hC : ∀ c : C, Commute a ((c : P) : Γ) := fun c => by
    have := Subgroup.mem_subgroupOf.1 c.2
    exact Subgroup.mem_centralizer_iff.1 this a rfl
  have key : ∀ (u : Γ) (c : C), (u * (a * ((c : P) : Γ)) * u⁻¹) ^ e = u * a * u⁻¹ := fun u c => by
    rw [conj_pow, (hC c).mul_pow, hpow a ha, hc, mul_one]
  let F : (P ⧸ C) × C → P := fun q => ⟨(q.1.out : Γ) * (a * ((q.2 : P) : Γ)) * (q.1.out : Γ)⁻¹ * a⁻¹, by
    have := P.mul_mem q.1.out.2 (hP _ (P.mul_mem (q.2 : P).2 (P.inv_mem q.1.out.2)))
    simpa [mul_assoc] using this⟩
  have hF : Function.Injective F := by
    rintro ⟨q, c⟩ ⟨q', c'⟩ h
    have h1 : (q.out : Γ) * (a * ((c : P) : Γ)) * (q.out : Γ)⁻¹ =
        (q'.out : Γ) * (a * ((c' : P) : Γ)) * (q'.out : Γ)⁻¹ :=
      mul_right_cancel (congrArg Subtype.val h)
    have h2 : (q.out : Γ) * a * (q.out : Γ)⁻¹ = (q'.out : Γ) * a * (q'.out : Γ)⁻¹ := by
      rw [← key _ c, h1, key]
    have h3 : q = q' := by
      rw [← q.out_eq, ← q'.out_eq]
      refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_centralizer_iff.2 ?_))
      intro z hz
      rw [Set.mem_singleton_iff.1 hz]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc _ = (q.out : Γ)⁻¹ * ((q.out : Γ) * a * (q.out : Γ)⁻¹) * q'.out := by group
        _ = _ := by rw [h2]; group
    subst h3
    have h4 : ((c : P) : Γ) = ((c' : P) : Γ) := mul_left_cancel (mul_left_cancel (mul_right_cancel h1))
    exact Prod.ext rfl (Subtype.ext (Subtype.ext h4))
  obtain ⟨⟨q, c⟩, hq⟩ := (Finite.injective_iff_surjective_of_equiv
    (Subgroup.groupEquivQuotientProdSubgroup (s := C)).symm).1 hF ⟨_, hab⟩
  refine ⟨q.out, q.out.2, ?_⟩
  have h5 : (q.out : Γ) * (a * ((c : P) : Γ)) * (q.out : Γ)⁻¹ = b := mul_right_cancel (congrArg Subtype.val hq)
  rw [← key _ c, h5, hpow b hb]

theorem exists_wild_conj {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (hA : IsPlaceOver A w) {Γ : Type} [Group Γ]
    (ρ : G E Ω →* Γ) (ho : IsOpen (ρ.ker : Set (G E Ω))) {t φ : G E Ω} {q : ℕ} (ht : t ∈ Ine (F := E) A)
    (hφ : IsFrob A q φ) {n : ℕ} (hn : (n : 𝓞 E) ∉ w.asIdeal) (hord : ρ t ^ n = 1) :
    ∃ u ∈ Wild E A, ρ ((u * φ) * t * (u * φ)⁻¹) = ρ t ^ q := by
  haveI : IsGalois E Ω := {}
  haveI := Subgroup.quotient_finite_of_isOpen ρ.ker ho
  haveI : Finite ρ.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ρ).toEquiv
  haveI : Finite ((Wild E A).map ρ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective ((Wild E A).map_le_range ρ))
  have htD : t ^ q ∈ Dec (F := E) A := Subgroup.pow_mem _ ht.1 _
  have hP : ∀ x ∈ (Wild E A).map ρ, ρ t ^ q * x * (ρ t ^ q)⁻¹ ∈ (Wild E A).map ρ := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨_, conj_mem_Wild htD hs, by simp⟩
  have hcop : (Nat.card ((Wild E A).map ρ)).Coprime n := by
    refine Nat.coprime_of_dvd fun p hp h1 h2 => ?_
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨⟨_, s, hs, rfl⟩, hx⟩ := exists_prime_orderOf_dvd_card' p h1
    have h3 : ρ s ^ n = 1 := by
      have := orderOf_dvd_iff_pow_eq_one.1 (hx ▸ h2)
      simpa using congrArg Subtype.val this
    have h4 : s ∈ ρ.ker := GlobalTheory.mem_of_wild_of_pow_mem_open_normal _ _ _ _ hA _ inferInstance ho s n hn hs
      (by rwa [MonoidHom.mem_ker, map_pow])
    have h5 : (⟨ρ s, s, hs, rfl⟩ : (Wild E A).map ρ) = 1 := Subtype.ext h4
    rw [h5, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hab : ρ (φ * t * φ⁻¹) * (ρ t ^ q)⁻¹ ∈ (Wild E A).map ρ := by
    have := hP _ ⟨_, (mem_Wild.2 (wild_of_frob ht hφ)), rfl⟩
    simpa [mul_assoc] using this
  obtain ⟨_, ⟨u, hu, rfl⟩, h⟩ := conj_of_coprime _ (ρ t ^ q) (ρ (φ * t * φ⁻¹)) n hP hcop
    (by rw [← pow_mul, mul_comm, pow_mul, hord, one_pow])
    (by rw [map_mul, map_mul, map_inv, conj_pow, hord]; simp) hab
  refine ⟨u⁻¹, inv_mem hu, ?_⟩
  have e : u⁻¹ * φ * t * (u⁻¹ * φ)⁻¹ = u⁻¹ * (φ * t * φ⁻¹) * u := by group
  rw [e, map_mul, map_mul, ← h, map_inv]; group

theorem isFrob_wild_mul {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {u φ : G E Ω} {q : ℕ} (hu : u ∈ Wild E A) (hφ : IsFrob A q φ) :
    IsFrob A q (u * φ) := by
  refine ⟨Subgroup.mul_mem _ (Wild_le_Ine hu).1 hφ.1, fun x hx => ?_⟩
  have h1 := hφ.2 x hx
  have h2 : A.valuation (φ x) ≤ 1 := by
    have := Valuation.map_add_le A.valuation h1.le (y := x ^ q) (by rw [map_pow]; exact pow_le_one' hx q)
    simpa using this
  have h3 : A.valuation (u (φ x) - φ x) < 1 := by
    by_cases h0 : φ x = 0
    · simp [h0]
    · have e : u (φ x) - φ x = φ x * (u (φ x) / φ x - 1) := by field_simp
      rw [e, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' h2) (mem_Wild.1 hu _ h0)
  have := Valuation.map_add_lt A.valuation h3 h1
  simpa using this

theorem exists_exponent {g : ℕ} [Fact g.Prime] (s : Multiset (Fbar g)) (hs : ∀ x ∈ s, x ≠ 0) :
    ∃ m : ℕ, g.Coprime m ∧ ∀ x ∈ s, x ^ m = 1 := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | cons a s ih =>
    obtain ⟨m, hm, h⟩ := ih fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    have ha := (isOfFinOrder_of_ne_zero (hs a (Multiset.mem_cons_self _ _))).orderOf_pos
    refine ⟨orderOf a * m, Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 ?_) hm, ?_⟩
    · rintro ⟨c, hc⟩
      have h1 : a ^ c = 1 := (frobenius (Fbar g) g).injective (by
        rw [frobenius_def, map_one, ← pow_mul, mul_comm, ← hc, pow_orderOf_eq_one])
      have h2 := orderOf_dvd_of_pow_eq_one h1
      have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; omega)
      have h3 := Nat.le_of_dvd hc0 h2
      have h4 := (Fact.out : g.Prime).two_le
      nlinarith
    · intro x hx
      rcases Multiset.mem_cons.1 hx with rfl | hx
      · rw [pow_mul, pow_orderOf_eq_one, one_pow]
      · rw [mul_comm, pow_mul, h x hx, one_pow]

theorem pow_eq_one_of_roots {K : Type} [Field K] {l N m : ℕ} [Fact l.Prime] [CharP K l]
    (M : Matrix (Fin N) (Fin N) K) (s : Multiset K) (hs : ∀ a ∈ s, a ^ m = 1)
    (hM : M.charpoly = (s.map fun a => X - C a).prod) : M ^ (m * l ^ s.card) = 1 := by
  have h1 : (s.map fun a => X - C a).prod ∣ (X ^ m - 1 : K[X]) ^ s.card := by
    have := Multiset.prod_dvd_prod_of_dvd (S := s) (fun a => X - C a) (fun _ => (X ^ m - 1 : K[X]))
      (fun a ha => by rw [dvd_iff_isRoot]; simp [hs a ha])
    simpa using this
  have h2 : (X ^ m - 1 : K[X]) ^ s.card ∣ X ^ (m * l ^ s.card) - 1 := by
    have : (X ^ (m * l ^ s.card) - 1 : K[X]) = (X ^ m - 1) ^ l ^ s.card := by
      rw [sub_pow_char_pow, one_pow, pow_mul]
    rw [this]
    exact pow_dvd_pow _ (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
  have h3 := aeval_eq_zero_of_dvd_aeval_eq_zero (hM ▸ h1.trans h2) (Matrix.aeval_self_charpoly M)
  simpa [sub_eq_zero] using h3

variable (D : D7)

def EigenClause (σ : D.what₂.FT) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
  Matrix.charpoly ((D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
      Matrix (Fin D.R.r) (Fin D.R.r) _) =
    ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x =>
      X - C (D.ntypes.iota k v (D.nd.w i) (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar (D.nd.w i)) x))).prod

theorem first_iff : GlobalTheory.RowCopy.JointOccurrenceCondition D ↔
    ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k), D.ntypes.cuspidal σ →
      TameGen D.nd (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) →
      ∀ i : D.nd.Loc, D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ →
        EigenClause D σ i k v ∧ ∃ φ : G D.host.E D.nd.Om, FrobConj D σ i k v φ := Iff.rfl

theorem hypotheses_iff (σ : D.what₂.FT) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) :
    (D.ntypes.cuspidal σ ∧ TameGen D.nd (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) ∧
      D.nd.l i ≠ D.host.g k ∧ D.what₂.isot (D.nd.j i) σ ≠ ⊥ ∧ D.nd.goodRow σ) ↔ Guard D σ i k :=
  ⟨fun ⟨hc, _, hl, ho, hg⟩ => ⟨hg, hc, ho, hl⟩,
    fun ⟨hg, hc, ho, hl⟩ => ⟨hc, (D.ntypes.tg_gen k v).2, hl, ho, hg⟩⟩

theorem eigenvalues_iff (σ : D.what₂.FT) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) :
    EigenClause D σ i k v ↔ TameEigenvalues D σ i k v := by
  unfold EigenClause TameEigenvalues
  rw [← D.nd.w_l i]

theorem normV_plGw (k : Fin 2) (v : D.nd.PlG k) : normV (D.naut.plGw k v) = D.host.g k :=
  normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) (D.naut.plGw_over k v)

theorem exists_frobConj_of_eigenvalues {σ : D.what₂.FT} {i : D.nd.Loc} {k : Fin 2} {v : D.nd.PlG k}
    (hg : D.nd.goodRow σ) (hl : D.nd.l i ≠ D.host.g k) (h1 : EigenClause D σ i k v) :
    ∃ φ : G D.host.E D.nd.Om, IsFrobAtType D k v φ ∧ FrobConj D σ i k v φ := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
  obtain ⟨m, hm, hx⟩ := exists_exponent (rootsBar (D.nd.lab k σ v)) (root_ne_zero D σ hg k v)
  have h2 := pow_eq_one_of_roots (l := D.what₂.places.resChar (D.nd.w i)) (m := m)
    ((D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) : GL (Fin D.R.r) _) : Matrix (Fin D.R.r) (Fin D.R.r) _)
    ((rootsBar (D.nd.lab k σ v)).map fun x =>
      D.ntypes.iota k v (D.nd.w i) (primeToPart (D.what₂.places.resChar (D.nd.w i)) x))
    (by
      intro a ha
      obtain ⟨x, hx', rfl⟩ := Multiset.mem_map.1 ha
      rw [map_primeToPart _ (isOfFinOrder_of_ne_zero (root_ne_zero D σ hg k v x hx')), ← map_pow, hx x hx',
        map_one])
    (by rw [Multiset.map_map]; exact h1)
  obtain ⟨φ, hφ⟩ := exists_isFrobAtType D k v
  unfold IsFrobAtType at hφ ⊢
  rw [normV_plGw] at hφ ⊢
  refine (exists_wild_conj (D.nd.plOm.2 (D.naut.plGw k v)) _ (D.ntypes.rbar_open σ (D.nd.w i))
    (D.ntypes.tg_mem k v) hφ (n := _) ?_ (Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h2))).elim
      fun u hu => ⟨_, isFrob_wild_mul hu.1 hφ, hu.2⟩
  intro hmem
  have hcop := Nat.Coprime.mul_right hm (Nat.Coprime.pow_right
    (Multiset.card ((rootsBar (D.nd.lab k σ v)).map fun x =>
      D.ntypes.iota k v (D.nd.w i) (primeToPart (D.what₂.places.resChar (D.nd.w i)) x)))
    ((Nat.coprime_primes (D.host.g_prime k) (D.what₂.places.resChar_prime (D.nd.w i))).2
      (by rw [D.nd.w_l i]; exact hl.symm)))
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 D.host.E))
  refine (D.naut.plGw k v).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (by simpa [placesOver] using D.naut.plGw_over k v))
    (Ideal.mul_mem_left _ _ (by simpa using hmem))

theorem conclusions_iff {σ : D.what₂.FT} {i : D.nd.Loc} {k : Fin 2} (v : D.nd.PlG k)
    (hg : D.nd.goodRow σ) (hl : D.nd.l i ≠ D.host.g k) :
    (EigenClause D σ i k v ∧ ∃ φ : G D.host.E D.nd.Om, FrobConj D σ i k v φ) ↔
      (TameEigenvalues D σ i k v ∧
        ∃ φ : G D.host.E D.nd.Om, IsFrobAtType D k v φ ∧ FrobConj D σ i k v φ) :=
  ⟨fun h => ⟨(eigenvalues_iff D σ i k v).1 h.1, exists_frobConj_of_eigenvalues D hg hl h.1⟩,
    fun ⟨h, φ, _, hφ⟩ => ⟨(eigenvalues_iff D σ i k v).2 h, φ, hφ⟩⟩

theorem tameGenerator_iff : GlobalTheory.RowCopy.JointOccurrenceCondition D ↔ TameGeneratorAtTypePrime D := by
  rw [first_iff]
  constructor
  · intro h σ i k hG v
    obtain ⟨hc, ht, hl, ho, hg⟩ := (hypotheses_iff D σ i k v).2 hG
    exact (conclusions_iff D v hg hl).1 (h σ k v hc ht i hl ho hg)
  · intro h σ k v hc ht i hl ho hg
    exact (conclusions_iff D v hg hl).2 (h σ i k ((hypotheses_iff D σ i k v).1 ⟨hc, ht, hl, ho, hg⟩) v)

theorem strong_iff : TameAtTypePrimeStrong D ↔ TameGeneratorAtTypePrime D ∧
    ∀ (σ : D.what₂.FT) (i : D.nd.Loc) (k : Fin 2), Guard D σ i k → ∀ (v : D.nd.PlG k)
      (s : G D.host.E D.nd.Om), IsWildAtType D k v s → D.ntypes.rbar σ (D.nd.w i) s = 1 := by
  refine ⟨fun h => ⟨tameGenerator_of_strong D h, fun σ i k hG v => (h σ i k hG v).1⟩,
    fun ⟨h, hw⟩ σ i k hG v => ⟨hw σ i k hG v, (h σ i k hG v).1, fun φ hφ => ?_⟩⟩
  unfold IsFrobAtType at hφ
  rw [normV_plGw] at hφ
  have h3 := hw σ i k hG v _ (wild_of_frob (D.ntypes.tg_mem k v) hφ)
  rw [map_mul, map_inv, inv_mul_eq_one, map_pow] at h3
  exact h3.symm

end GlobalTheory.Proof.EigenvalueCoprimeConjugation

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharTrivialAtPlaceOfDegOneCofiniteTrivialStatement
section
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_trivialAtPlace_of_degOne_cofinite_trivial : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ → (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → (∀ x : (InfiniteAdeleRing E)ˣ, χ (infIdele E x) = 1) → ∀ w, TrivAt χ w := by
  first | exact @GlobalTheory.HeckeFin.trivAt_of_degOne_cofinite | exact GlobalTheory.HeckeFin.trivAt_of_degOne_cofinite | (intros; apply GlobalTheory.HeckeFin.trivAt_of_degOne_cofinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostFieldPadicEmbeddingMemMaxUnramifiedStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hostField_padicEmbedding_mem_maxUnramified : ∀ {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime], l ∉ H.small → l ≠ H.q → l ≠ H.d → ∀ (c : H.E →+* PadicAlgCl l) (x : H.E), c x ∈ Loc.MaximalUnramifiedExtension l := by
  first | exact @GlobalTheory.HostKur.host_image_mem_Kur | exact GlobalTheory.HostKur.host_image_mem_Kur | (intros; apply GlobalTheory.HostKur.host_image_mem_Kur <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsDCOfMemDoubleCoset
section
namespace GlobalTheory.HkB

open Formalism.IndefR.Bridge

theorem isDC_of_mem_doubleCoset {G : Type} [Group G] {J : Subgroup G} {x x' : G} {A : Finset G}
    (hA : IsDC J x' A) (hx : ∃ k₁ k₂ : J, x' = (k₁ : G) * x * k₂) : IsDC J x A := by
  obtain ⟨k₁, k₂, rfl⟩ := hx
  constructor
  · intro a ha
    obtain ⟨u, v, rfl⟩ := hA.1 a ha
    exact ⟨u * k₁, k₂ * v, by simp [mul_assoc]⟩
  · rintro _ ⟨u, v, rfl⟩
    exact hA.2 _ ⟨u * k₁⁻¹, k₂⁻¹ * v, by simp [mul_assoc]⟩

theorem dcOp_eq_and_level {G W : Type} [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (J L : Subgroup G) (χ : J →* ℂˣ) (x x' : G) (A A' : Finset G) (F : G → W)
    (hs : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l)
    (hχ : ∀ k : J, (k : G) ∈ L → χ k = 1) (hAL : ∀ a ∈ A, a ∈ L) (hAL' : ∀ a ∈ A', a ∈ L)
    (hA : IsDC J x A) (hA' : IsDC J x' A') (hx : ∃ k₁ k₂ : J, x' = (k₁ : G) * x * k₂)
    (hF : ∀ (k : J) (h : G), F (h * k) = (χ k : ℂ) • F h) :
    dcOp A F = dcOp A' F ∧ (∀ (k : J) (h : G), (dcOp A F) (h * k) = (χ k : ℂ) • (dcOp A F) h) := by
  have hF' : F ∈ AdForms (1 : G →* G) (1 : G →* Module.End ℂ W) J χ := by
    intro γ h k
    simpa using hF k h
  refine ⟨dcOp_eq_of_isDC _ _ hχ hA (isDC_of_mem_doubleCoset hA' hx) hAL hAL' hF', fun k h => ?_⟩
  have h1 := LocSplit.dcOp_mem (1 : G →* G) (1 : G →* Module.End ℂ W) hs hχ hA hAL hF' 1 h k
  simpa using h1

end GlobalTheory.HkB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KvalGeZeroOfIntegralJetsStatement
section
open Formalism.MainNotions Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kvalGe_zero_of_integral_jets : ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime] (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]), Formalism.DworkPowerSeriesWeights.JetsIntegral Th → product_zeroth_first_parts.KvalGe N0 N1 l nu Th 0 := by
  first | exact @GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero | exact GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero | (intros; apply GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemCmComplexOfPow
section
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

noncomputable section

namespace GlobalTheory.PresRat

def conjAlg : algebraicClosure ℚ ℂ →+* algebraicClosure ℚ ℂ :=
  ((starRingEnd ℂ).comp (algebraicClosure ℚ ℂ).val.toRingHom).codRestrict (algebraicClosure ℚ ℂ) fun x => by
    have hx : IsAlgebraic ℚ (x : ℂ) := mem_algebraicClosure_iff.1 x.2
    exact mem_algebraicClosure_iff.2 (hx.algHom (starRingEnd ℂ).toRatAlgHom)

def cmComplex : Subfield ℂ :=
  (⨅ τ : algebraicClosure ℚ ℂ →+* ℂ, RingHom.eqLocusField (τ.comp conjAlg) ((starRingEnd ℂ).comp τ)).map
    (algebraicClosure ℚ ℂ).val.toRingHom

theorem mem_cmComplex {z : ℂ} : z ∈ cmComplex ↔ ∃ x : algebraicClosure ℚ ℂ, (x : ℂ) = z ∧
    ∀ τ : algebraicClosure ℚ ℂ →+* ℂ, τ (conjAlg x) = starRingEnd ℂ (τ x) := by
  unfold cmComplex
  rw [Subfield.mem_map]
  refine exists_congr fun x => ?_
  rw [Subfield.mem_iInf, and_comm]
  rfl

theorem conj_eq_inv_of_pow {z : ℂ} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) : starRingEnd ℂ z = z⁻¹ :=
  (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hz hn.ne')).symm

theorem mem_cmComplex_of_pow {z : ℂ} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) : z ∈ cmComplex := by
  have ha : IsAlgebraic ℚ z := IsAlgebraic.of_pow hn (by rw [hz]; exact isAlgebraic_one)
  refine mem_cmComplex.2 ⟨⟨z, mem_algebraicClosure_iff.2 ha⟩, rfl, fun τ => ?_⟩
  set x : algebraicClosure ℚ ℂ := ⟨z, mem_algebraicClosure_iff.2 ha⟩
  have hx : x ^ n = 1 := Subtype.ext hz
  have h1 : conjAlg x = x⁻¹ := Subtype.ext (conj_eq_inv_of_pow hn hz)
  rw [h1, map_inv₀, conj_eq_inv_of_pow hn (by rw [← map_pow, hx, map_one])]

theorem mem_cmComplex_iff {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ)
    (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (a : K) : σ a ∈ cmComplex ↔ a ∈ cmMax K := by
  let s : K →+* algebraicClosure ℚ ℂ := σ.codRestrict (algebraicClosure ℚ ℂ) fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom σ.toRatAlgHom)
  have hs : conjAlg (s a) = s (star a) := Subtype.ext (hσ a).symm
  rw [mem_cmComplex]
  constructor
  · rintro ⟨x, hx, h⟩ φ
    have hx' : x = s a := Subtype.ext hx
    let _ : Algebra K (algebraicClosure ℚ ℂ) := s.toAlgebra
    have : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := by
      convert algebraicClosure.isAlgebraic ℚ ℂ
      · rfl
      · exact Subsingleton.elim _ _
    have : Algebra.IsAlgebraic K (algebraicClosure ℚ ℂ) :=
      Algebra.IsAlgebraic.tower_top (K := ℚ) K
    have h1 := h (ComplexEmbedding.lift (algebraicClosure ℚ ℂ) φ)
    rw [hx', hs] at h1
    have e : ∀ b, ComplexEmbedding.lift (algebraicClosure ℚ ℂ) φ (s b) = φ b := fun b =>
      ComplexEmbedding.lift_algebraMap_apply _ φ b
    rw [e, e] at h1
    exact h1
  · intro h
    exact ⟨s a, rfl, fun τ => by rw [hs]; exact h (τ.comp s)⟩

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : ClassPres ι S σ ρ J χ)

theorem act_mem (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (hχ : ∀ k, ∃ n : ℕ, 0 < n ∧ χ k ^ n = 1)
    (hρ : ∀ γ j, ∃ c : S.ιV → K, (∀ i, c i ∈ cmMax K) ∧ ρ γ (P.coef (S.bV j)) = ∑ i, σ (c i) • P.coef (S.bV i))
    (k : J) (γ : Γ) (x : S.V) (hx : ∀ i, S.bV.repr x i ∈ cmMax K) (i : S.ιV) :
    (PresBasic.bW P).repr ((χ k : ℂ) • ρ γ (P.coef x)) i ∈ cmComplex := by
  obtain ⟨n, hn, hk⟩ := hχ k
  have h1 : (χ k : ℂ) ∈ cmComplex :=
    mem_cmComplex_of_pow hn (by rw [← Units.val_pow_eq_pow_val, hk, Units.val_one])
  have h2 : P.coef x = ∑ j, σ (S.bV.repr x j) • P.coef (S.bV j) := by
    conv_lhs => rw [← S.bV.sum_repr x]
    rw [map_sum]
    simp only [map_smulₛₗ]
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, h2]
  refine cmComplex.mul_mem h1 ?_
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine cmComplex.sum_mem fun j _ => cmComplex.mul_mem ((mem_cmComplex_iff σ hσ _).2 (hx j)) ?_
  obtain ⟨c, hc, e⟩ := hρ γ j
  rw [e]
  simp only [← PresBasic.bW_apply]
  rw [Module.Basis.repr_sum_self]
  exact (mem_cmComplex_iff σ hσ _).2 (hc i)

end GlobalTheory.PresRat

namespace GlobalTheory

theorem classPres_dcOp_rat : ∀ {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : ClassPres ι S σ ρ J χ) (A : Finset G) (T : Module.End K S.Forms), (∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) → (∀ k, ∃ n : ℕ, 0 < n ∧ χ k ^ n = 1) → (∀ γ j, ∃ c : S.ιV → K, (∀ i, c i ∈ cmMax K) ∧ ρ γ (P.coef (S.bV j)) = ∑ i, σ (c i) • P.coef (S.bV i)) → (∀ f : S.Forms, P.ext ((T f : S.Forms) : S.Cl → S.V) = dcOp A (P.ext (f : S.Cl → S.V))) → S.HasRatBasis ∧ ∀ a b, LinearMap.toMatrix S.basis S.basis T a b ∈ cmMax K := by
  intro G Γ W K _ _ _ _ _ _ _ ι S σ ρ J χ P A T hσ hχ hρ hT
  have hb : S.HasRatBasis := by
    refine (forms_rat S).1 fun c γ i j => ?_
    rw [← PresRat.mem_cmComplex_iff σ hσ, ← PresBasic.repr_coef P, P.coef_act]
    refine PresRat.act_mem P hσ hχ hρ _ _ _ (fun l => ?_) i
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨hb, (forms_rat S).2 T hb fun f hf c i => ?_⟩
  rw [← PresRat.mem_cmComplex_iff σ hσ, ← PresBasic.repr_coef P, ← PresBasic.ext_y P, hT]
  unfold dcOp
  rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  exact PresRat.cmComplex.sum_mem fun a _ => PresRat.act_mem P hσ hχ hρ _ _ _ (hf _) i

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OneLeScOfSizeData
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem one_le_Sc {D : D7} (L : SizeData₂ D) : (1 : ℝ) ≤ L.Sc := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  set τ := D.eTau.symm ⟨plc (1 : D.R.GG), plc_mem 1⟩
  set P := D.hc τ
  have h1 := P.u_gt_v ⟨1, by omega⟩
  have h2 := P.v_gt_u ⟨0, by omega⟩
  obtain ⟨z0, hz0⟩ := P.v_int ⟨0, by omega⟩
  obtain ⟨z1, hz1⟩ := P.v_int ⟨1, by omega⟩
  have c0 := (L.cloud_v τ ⟨0, by omega⟩).2
  have c1 := (L.cloud_v τ ⟨1, by omega⟩).1
  simp only at h1 h2
  have hlt : P.v ⟨1, by omega⟩ < P.v ⟨0, by omega⟩ := lt_trans h1 h2
  rw [hz0, hz1] at hlt
  have hz : z1 < z0 := by exact_mod_cast hlt
  have hz1' : (0 : ℝ) ≤ (z1 : ℝ) := by
    have : (((P.v ⟨1, by omega⟩ : ℚ) : ℝ)) = (z1 : ℝ) := by rw [hz1]; push_cast; rfl
    rw [← this]; exact c1
  have hz0' : (z0 : ℝ) ≤ L.Sc := by
    have : (((P.v ⟨0, by omega⟩ : ℚ) : ℝ)) = (z0 : ℝ) := by rw [hz0]; push_cast; rfl
    rw [← this]; exact c0
  have : (0 : ℤ) ≤ z1 := by exact_mod_cast hz1'
  have : (1 : ℝ) ≤ (z0 : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ z0 by omega)
  linarith

theorem recWord_small_pos : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ}
    (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ →
    Small (recWord L j ε g) ∧ 1 ≤ (recWord L j ε g).S ∧ 1 ≤ (recWord L j ε g).η := by
  intro D L C j ε n g ψ hR _
  have hB := GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε (1 : D.R.GG) (1 : D.R.GG) hR
  obtain ⟨b1, w1, bw, bη, bS, hsz⟩ := hB
  refine ⟨⟨b1, w1, bw, bη, bS, fun a => ?_⟩, ?_, ?_⟩
  · have hB' := GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε (g a) (1 : D.R.GG) hR
    have h := hB'.2.2.2.2.2 (0 : ZMod (orderOf (1 : D.R.GG)))
    simp only [pageWord, letter, one_pow, mul_one] at h
    show etaHat L < (szT (hcAt D (g a)) j (pos ε (g a))).toNat
    exact Int.lt_toNat.mpr h
  · show 1 ≤ sHat L
    unfold sHat
    exact Nat.le_floor (by exact_mod_cast one_le_Sc L)
  · show 1 ≤ etaHat L
    unfold etaHat; omega

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoThreeOfOfDeterminantCharacterFiniteOrderTypeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.Host GlobalTheory.KerJ NumberField Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rhoThreeOf_of_determinantCharacterFiniteOrderType : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ), MtType u mt → rhoThreeOf D C mt := by
  first | exact @GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType | exact GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType | (intros; apply GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType <;> assumption)
end

