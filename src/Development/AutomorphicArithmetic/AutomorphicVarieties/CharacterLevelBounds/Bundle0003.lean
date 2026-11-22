import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.AbLevel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem val_modEq {N : ℕ} [NeZero N] {x : ZMod N} {a : ℕ} (h : x = (a : ZMod N)) : x.val ≡ a [MOD N] := by
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, h]

private theorem unitsMap_val {g N : ℕ} [NeZero g] [NeZero N] (h : g ∣ N) (u : (ZMod N)ˣ) :
    ((ZMod.unitsMap h u : (ZMod g)ˣ) : ZMod g).val ≡ (u : ZMod N).val [MOD g] := by
  apply val_modEq
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val]

private theorem down (P : ℕ → Prop) (g : ℕ) [NeZero g] (hP : ∀ a b, a ≡ b [MOD g] → (P a ↔ P b))
    (K : Subgroup (ZMod g)ˣ) (hK : ∀ u, u ∈ K ↔ P (u : ZMod g).val)
    (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N] (h : g ∣ N)
    (j : E →ₐ[ℚ] CyclotomicField N ℚ) (ζ : CyclotomicField N ℚ) (hζ : IsPrimitiveRoot ζ N)
    (hj : ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (a : ℕ), τ ζ = ζ ^ a →
      ((∀ x : E, τ (j x) = j x) ↔ P a)) : HasLevel E g K := by
  refine ((levChange E N).2 g h K).2 ⟨j, ζ, hζ, fun τ u hu => ?_⟩
  rw [hj τ _ hu, Subgroup.mem_comap, hK]
  exact (hP _ _ (unitsMap_val h u)).symm

private theorem exists_sub (P : ℕ → Prop) (g : ℕ) [NeZero g] (hP : ∀ a b, a ≡ b [MOD g] → (P a ↔ P b))
    (h1 : P 1) (hm : ∀ a b, P a → P b → P (a * b)) :
    ∃ K : Subgroup (ZMod g)ˣ, ∀ u, u ∈ K ↔ P (u : ZMod g).val := by
  let S : Submonoid (ZMod g)ˣ :=
    { carrier := {u | P (u : ZMod g).val}
      one_mem' := (hP _ _ (val_modEq (a := 1) (by simp))).2 h1
      mul_mem' := fun {u v} hu hv =>
        (hP _ _ (val_modEq (a := (u : ZMod g).val * (v : ZMod g).val) (by simp))).2 (hm _ _ hu hv) }
  refine ⟨{ S with inv_mem' := fun {u} hu => ?_ }, fun u => Iff.rfl⟩
  have : u⁻¹ ∈ Submonoid.powers u := mem_powers_iff_mem_zpowers.2 (inv_mem (Subgroup.mem_zpowers u))
  exact (Submonoid.powers_le (P := S)).2 hu this

private theorem ker_congr (A : AbF) {a b : ℕ} (h : a ≡ b [MOD A.m]) : A.ker a ↔ A.ker b := by
  unfold AbF.ker
  rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 h]

private theorem pm_iff (n a : ℕ) : (a ≡ 1 [MOD n] ∨ a + 1 ≡ 0 [MOD n]) ↔ ((a : ZMod n) = 1 ∨ (a : ZMod n) = -1) := by
  rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  rw [add_eq_zero_iff_eq_neg]

private theorem jac_congr {a b q : ℕ} (h : a ≡ b [MOD q]) : jacobiSym (a : ℤ) q = jacobiSym (b : ℤ) q :=
  jacobiSym.mod_left' (Int.natCast_modEq_iff.2 h)

theorem UpperTheory.V.Chr.abLevel :
    (∀ (A : AbF) (E : Type) [Field E] [NumberField E], IsAbField A E → HasLevel E A.m A.H) ∧
          ∀ (A : AbF) (e q d : ℕ) (E : Type) [Field E] [NumberField E], IsCompField A e q d E → ∀ (N : ℕ) [NeZero N], 2 ^ (e + 2) ∣ N → A.m ∣ N → q ∣ N → d ∣ N →
            ∃ H : Subgroup (ZMod N)ˣ, HasLevel E N H ∧ ∀ (u : (ZMod N)ˣ) (a : ℕ), (u : ZMod N) = (a : ZMod N) →
              (u ∈ H ↔ (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ A.ker a ∧ jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1) := by
  refine ⟨?_, ?_⟩
  · rintro A E _ _ ⟨N, _, j, ζ, h, hζ, hj⟩
    refine down A.ker A.m (fun a b => ker_congr A) A.H (fun u => ?_) E N h j ζ hζ hj
    unfold AbF.ker
    rw [ZMod.natCast_zmod_val]
    exact ⟨fun hu => ⟨u, hu, rfl⟩, fun ⟨v, hv, e⟩ => Units.ext e ▸ hv⟩
  · rintro A e q d E _ _ ⟨M, _, j, ζ, a1, a2, a3, a4, hζ, hj⟩ N _ b1 b2 b3 b4
    haveI : NeZero (Nat.gcd M N) := ⟨(Nat.gcd_pos_of_pos_left _ (NeZero.pos M)).ne'⟩
    let P : ℕ → Prop := fun a => (a ≡ 1 [MOD 2 ^ (e + 2)] ∨ a + 1 ≡ 0 [MOD 2 ^ (e + 2)]) ∧ A.ker a ∧
      jacobiSym (a : ℤ) q = 1 ∧ jacobiSym (a : ℤ) d = 1
    have hP : ∀ a b, a ≡ b [MOD Nat.gcd M N] → (P a ↔ P b) := fun a b h => by
      simp only [P]
      rw [pm_iff, pm_iff, (ZMod.natCast_eq_natCast_iff _ _ _).2 (h.of_dvd (Nat.dvd_gcd a1 b1)),
        ker_congr A (h.of_dvd (Nat.dvd_gcd a2 b2)), jac_congr (h.of_dvd (Nat.dvd_gcd a3 b3)),
        jac_congr (h.of_dvd (Nat.dvd_gcd a4 b4))]
    have h1 : P 1 := ⟨Or.inl (Nat.ModEq.refl _), ⟨1, A.H.one_mem, by simp⟩, by simp, by simp⟩
    have hm : ∀ a b, P a → P b → P (a * b) := by
      rintro a b ⟨p1, ⟨u, hu, eu⟩, p3, p4⟩ ⟨r1, ⟨v, hv, ev⟩, r3, r4⟩
      refine ⟨?_, ⟨u * v, A.H.mul_mem hu hv, by rw [Units.val_mul, eu, ev, Nat.cast_mul]⟩, ?_, ?_⟩
      · rw [pm_iff] at p1 r1 ⊢
        rw [Nat.cast_mul]
        rcases p1 with p | p <;> rcases r1 with r | r <;> simp [p, r]
      · rw [Nat.cast_mul, jacobiSym.mul_left, p3, r3, mul_one]
      · rw [Nat.cast_mul, jacobiSym.mul_left, p4, r4, mul_one]
    obtain ⟨K, hK⟩ := exists_sub P _ hP h1 hm
    have hL := down P _ hP K hK E M (Nat.gcd_dvd_left M N) j ζ hζ hj
    refine ⟨_, ((levChange E N).2 _ (Nat.gcd_dvd_right M N) K).1 hL, fun u a hu => ?_⟩
    rw [Subgroup.mem_comap, hK]
    exact hP _ _ ((unitsMap_val _ u).trans ((val_modEq hu).of_dvd (Nat.gcd_dvd_right M N)))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.DecCyc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

namespace UpperTheory.V.Chr.DecompositionCyclotomic

variable (l : ℕ) [hl : Fact l.Prime]

private theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h := Nat.prime_iff_prime_int.mp hl.out
  have he : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
  rw [he, MulEquiv.prime_iff]
  exact h

private noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

private theorem normV_vQ : normV (vQ l) = l := by
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  unfold normV
  have hJ : Ideal.span {((l : ℕ) : ℤ)} = Ideal.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (vQ l).asIdeal := by
    show _ = Ideal.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (Ideal.span {((l : ℕ) : 𝓞 ℚ)})
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have e : (𝓞 ℚ ⧸ (vQ l).asIdeal) ≃+* ZMod l :=
    (Ideal.quotientEquiv _ _ Rat.ringOfIntegersEquiv hJ).trans (Int.quotientSpanNatEquivZMod l)
  rw [Nat.card_congr e.toEquiv, Nat.card_zmod]

variable {l} {Ω : Type} [Field Ω]

private theorem intCast_mem_vQ (n : ℤ) : ((n : ℤ) : 𝓞 ℚ) ∈ (vQ l).asIdeal ↔ ((l : ℕ) : ℤ) ∣ n := by
  show _ ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)} ↔ _
  rw [Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv, map_natCast, map_intCast]
  simp

private theorem val_intCast_le_one (A : ValuationSubring Ω) (n : ℤ) : A.valuation (n : Ω) ≤ 1 := by
  have h := A.valuation_le_one (n : A)
  simpa using h

private theorem val_intCast_lt_one_iff (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (n : ℤ) :
    A.valuation (n : Ω) < 1 ↔ ((l : ℕ) : ℤ) ∣ n := by
  have hlp : Prime ((l : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  constructor
  · intro h
    by_contra hnd
    obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hlp.irreducible).mpr hnd
    have h1 : A.valuation (((a * ((l : ℕ) : ℤ) + b * n : ℤ)) : Ω) < 1 := by
      push_cast
      apply Valuation.map_add_lt
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A a)) hA
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A b)) h
    rw [hab] at h1
    simp at h1
  · rintro ⟨k, rfl⟩
    push_cast
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_intCast_le_one A k)) hA

private theorem isPlaceOver_vQ [Algebra ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    IsPlaceOver (F := ℚ) A (vQ l) := by
  intro x
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, (m : 𝓞 ℚ) = x :=
    ⟨Rat.ringOfIntegersEquiv x,
      (eq_intCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm.trans
        (Rat.ringOfIntegersEquiv.symm_apply_apply x)⟩
  rw [intCast_mem_vQ, ← val_intCast_lt_one_iff A hA m]
  simp

end UpperTheory.V.Chr.DecompositionCyclotomic

private theorem decomposition_cyclotomic_of_mem_dec {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (τ : G ℚ Ω)
    (hτ : τ ∈ Dec (F := ℚ) A) (x : Ω) : A.valuation x ≤ 1 → A.valuation (τ x) ≤ 1 := by
  intro hx
  rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
  open scoped Pointwise in
    (have h1 := MulAction.mem_stabilizer_iff.mp hτ
     rw [← h1, ← SetLike.mem_coe, ValuationSubring.coe_pointwise_smul]
     exact Set.smul_mem_smul_set hx)

private theorem decomposition_cyclotomic_of_mem_dec_second {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (τ : G ℚ Ω)
    (hτ : τ ∈ Dec (F := ℚ) A) (x : Ω) : A.valuation (τ x) ≤ 1 ↔ A.valuation x ≤ 1 := by
  constructor
  · intro h
    have h' := decomposition_cyclotomic_of_mem_dec A τ⁻¹ ((Dec (F := ℚ) A).inv_mem hτ) _ h
    simpa [AlgEquiv.aut_inv] using h'
  · exact decomposition_cyclotomic_of_mem_dec A τ hτ x

private theorem decomposition_cyclotomic_of_mem_dec_third {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (τ : G ℚ Ω)
    (hτ : τ ∈ Dec (F := ℚ) A) (x : Ω) : A.valuation (τ x) < 1 ↔ A.valuation x < 1 := by
  have key : ∀ z : Ω, A.valuation z < 1 ↔ z = 0 ∨ (A.valuation z ≤ 1 ∧ ¬ A.valuation z⁻¹ ≤ 1) := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    · have hv0 : A.valuation z ≠ 0 := by simpa using hz
      rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hv0), ← lt_iff_le_not_ge]
      simp [hz]
  rw [key, key, ← map_inv₀ τ x, decomposition_cyclotomic_of_mem_dec_second A τ hτ, decomposition_cyclotomic_of_mem_dec_second A τ hτ, EmbeddingLike.map_eq_zero_iff]

open UpperTheory.V.Chr.DecompositionCyclotomic in
theorem UpperTheory.V.Chr.decCyc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (p : ℕ) (A : ValuationSubring Ω), p.Prime → A.valuation (p : Ω) < 1 →
          ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A)).Normal ∧ Ine (F := ℚ) A ≤ Dec (F := ℚ) A ∧
          ∃ γ ∈ Dec (F := ℚ) A, Dec (F := ℚ) A ≤ (Subgroup.zpowers γ ⊔ Ine (F := ℚ) A).topologicalClosure ∧
            ∀ (l : ℕ) [Fact l.Prime], l ≠ p → ((cycZ ℚ Ω l γ : ℤ_[l]ˣ) : ℤ_[l]) = (p : ℤ_[l]) := by
  intro Ω _ _ _ p A hp hA
  haveI : Fact p.Prime := ⟨hp⟩
  have hPO := isPlaceOver_vQ (l := p) A hA
  obtain ⟨σ, hσ⟩ := exists_isFrob hPO
  have hσD : σ ∈ Dec (F := ℚ) A := hσ.1
  refine ⟨?_, Ine_le_Dec A, σ, hσD, ?_, ?_⟩
  · constructor
    rintro ⟨i, hiD⟩ hi ⟨τ, hτ⟩
    rw [Subgroup.mem_subgroupOf] at hi ⊢
    have hi2 : ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (i x - x) < 1 := hi.2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨(Dec (F := ℚ) A).mul_mem ((Dec (F := ℚ) A).mul_mem hτ hiD) ((Dec (F := ℚ) A).inv_mem hτ), ?_⟩
    intro x hx
    have hτi : τ⁻¹ ∈ Dec (F := ℚ) A := (Dec (F := ℚ) A).inv_mem hτ
    have hy : A.valuation (τ⁻¹ x) ≤ 1 := decomposition_cyclotomic_of_mem_dec A τ⁻¹ hτi x hx
    have h3 := hi2 _ hy
    have heq : (τ * i * τ⁻¹) x - x = τ (i (τ⁻¹ x) - τ⁻¹ x) := by
      simp [AlgEquiv.mul_apply, map_sub, AlgEquiv.aut_inv]
    rw [heq, decomposition_cyclotomic_of_mem_dec_third A τ hτ]
    exact h3
  · set K := (Subgroup.zpowers σ ⊔ Ine (F := ℚ) A).topologicalClosure with hK
    have hKc : IsClosed (K : Set (G ℚ Ω)) := Subgroup.isClosed_topologicalClosure _
    have hcs := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G ℚ Ω) ⟨K, hKc⟩
    refine le_trans ?_ hcs.ge
    refine le_sInf fun N hN => ?_
    have hKN : K ≤ N := hN.2
    exact Kum.decGen ℚ Ω A (vQ p) σ N hPO hσ hN.1
      (le_trans (le_sup_right.trans (Subgroup.le_topologicalClosure _)) hKN)
      (hKN (Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers σ))))
  · intro l _ hlp
    have hnot : ((l : ℕ) : 𝓞 ℚ) ∉ (vQ p).asIdeal := by
      intro h
      have h' := (intCast_mem_vQ (l := p) (l : ℤ)).mp (by simpa using h)
      rw [Int.natCast_dvd_natCast] at h'
      exact hlp ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : l.Prime)).mp h').symm
    rw [cycZ_of_isFrob hnot hPO hσ, normV_vQ]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.FactorGS
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

theorem UpperTheory.V.Chr.factorGS :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N : ℕ) [NeZero N] (e : ℕ) (ψ : G k Ω →* Oˣ), (cls k Ω N).ker ≤ ψ.ker →
          ∀ S : Set (HeightOneSpectrum (𝓞 k)), S = Above k (l * N) →
          ∃ θ : GS Ω S →* Oˣ, θ.comp (toGS Ω S) = (Psi l e ψ)⁻¹ ∧ ContAction (twist₂ l θ) := by
  intro k Ω _ _ _ _ _ l _ O _ _ _ _ _ N _ e ψ hker S hS
  have hψopen : IsOpen (ψ.ker : Set (G k Ω)) := Subgroup.isOpen_mono hker (clsFacts k Ω N).1
  have hcyc : IsClosed ((cycZ k Ω l).ker : Set (G k Ω)) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage (contTw k Ω l).1
  have hNS : NS Ω S ≤ ψ.ker ⊓ (cycZ k Ω l).ker := by
    unfold NS
    refine Subgroup.topologicalClosure_minimal _ ?_ ((Subgroup.isClosed_of_isOpen _ hψopen).inter hcyc)
    refine Subgroup.normalClosure_le_normal ?_
    intro σ hσ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hσ
    obtain ⟨v, hv, A, hA, hσ⟩ := hσ
    have hvS : v ∉ Above k (l * N) := by
      rw [← hS]
      exact hv
    have hmem : ∀ m : ℕ, m ∣ l * N → ¬ A.valuation (m : Ω) < 1 := by
      intro m hm hlt
      apply hvS
      have hx := (hA (m : 𝓞 k)).1 (by simpa using hlt)
      obtain ⟨c, hc⟩ := hm
      show ((l * N : ℕ) : 𝓞 k) ∈ v.asIdeal
      rw [hc, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hx
    refine ⟨?_, ?_⟩
    · exact hker ((clsFacts k Ω N).2.2.2.2 A (hmem N (dvd_mul_left N l)) hσ)
    · exact (places k Ω l A).2.2.2 (hmem l (dvd_mul_right l N)) hσ
  have hP : NS Ω S ≤ (Psi l e ψ)⁻¹.ker := by
    intro σ hσ
    have h1 : ψ σ = 1 := (hNS hσ).1
    have h2 : cycZ k Ω l σ = 1 := (hNS hσ).2
    rw [MonoidHom.mem_ker]
    unfold Psi chiO
    simp [h1, h2]
  refine ⟨QuotientGroup.lift (NS Ω S) (Psi l e ψ)⁻¹ hP, MonoidHom.ext fun σ => rfl, ?_⟩
  have heq : (Psi l e ψ)⁻¹ = ψ⁻¹ * chiO k Ω l O ^ (-(e : ℤ)) := by
    unfold Psi
    rw [mul_inv, mul_comm, zpow_neg]
  have hopen : IsOpen ((ψ⁻¹).ker : Set (G k Ω)) := by
    convert hψopen using 2
    ext σ
    simp
  have hG := (contTw k Ω l).2.2 O ψ⁻¹ (-(e : ℤ)) hopen
  rw [← heq] at hG
  unfold ReciprocityTheory.Gal.ContAction at hG ⊢
  rw [← ((QuotientGroup.isOpenQuotientMap_mk (N := NS Ω S)).prodMap (IsOpenQuotientMap.id (X := QO l O))).continuous_comp_iff]
  exact hG
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.KerFin
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem kerFin_triv {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R G M)
    (U' U : Subgroup G) (h : U' ≤ U) (hρ : ∀ u ∈ U, ∀ m, ρ u m = m) (n : ℕ) (hn : ∀ u ∈ U, u ^ n ∈ U')
    [Fintype (U ⧸ U'.subgroupOf U)] :
    Module.length R (LinearMap.ker (resU ρ h)) ≤ (Fintype.card (U ⧸ U'.subgroupOf U) : ℕ∞) *
      Module.length R (LinearMap.ker ((n : R) • (LinearMap.id : M →ₗ[R] M))) := by
  classical
  set K : Subgroup U := U'.subgroupOf U with hK
  set N := LinearMap.ker ((n : R) • (LinearMap.id : M →ₗ[R] M)) with hN
  have hadd : ∀ z ∈ Z1U ρ U, ∀ a b : U, z (a * b) = z a + z b := by
    intro z hz a b
    have := ((mem_Z1_iff_cocycle (ρ.comp U.subtype) z).mp hz).2 a b
    rw [this, MonoidHom.comp_apply, Subgroup.coe_subtype, hρ a a.2]
  have hone : ∀ z ∈ Z1U ρ U, z 1 = 0 := by
    intro z hz
    have := hadd z hz 1 1
    rw [mul_one] at this
    exact left_eq_add.mp this
  have hinv : ∀ z ∈ Z1U ρ U, ∀ a : U, z a⁻¹ = - z a := by
    intro z hz a
    have := hadd z hz a a⁻¹
    rw [mul_inv_cancel, hone z hz] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have hpow : ∀ z ∈ Z1U ρ U, ∀ a : U, ∀ k : ℕ, z (a ^ k) = k • z a := by
    intro z hz a k
    induction k with
    | zero => rw [pow_zero, hone z hz, zero_smul]
    | succ k ih => rw [pow_succ, hadd z hz, ih, succ_nsmul]
  have hB : ∀ z ∈ Submodule.comap (Z1U ρ U).subtype (B1 (ρ.comp U.subtype)), (z : U → M) = 0 := by
    intro z hz
    rw [Submodule.mem_comap, B1, LinearMap.mem_range] at hz
    obtain ⟨m, hm⟩ := hz
    funext u
    rw [Submodule.coe_subtype] at hm
    rw [← hm, amitsur_d0_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, hρ u u.2, sub_self]
    rfl
  let ev : (Z1U ρ U) →ₗ[R] (U ⧸ K → M) :=
    LinearMap.pi (fun q => (LinearMap.proj (Quotient.out q) : (U → M) →ₗ[R] M) ∘ₗ (Z1U ρ U).subtype)
  have hev : ∀ z q, ev z q = (z : U → M) (Quotient.out q) := fun z q => rfl
  let Φ : H1U ρ U →ₗ[R] (U ⧸ K → M) :=
    (Submodule.comap (Z1U ρ U).subtype (B1 (ρ.comp U.subtype))).liftQ ev (by
      intro z hz
      rw [LinearMap.mem_ker]
      funext q
      rw [hev, hB z hz]
      rfl)
  have hΦ : ∀ z q, Φ (Submodule.Quotient.mk z) q = (z : U → M) (Quotient.out q) := fun z q => rfl
  have hvan : ∀ z : Z1U ρ U, resU ρ h (Submodule.Quotient.mk z) = 0 → ∀ u : U, (u : G) ∈ U' → (z : U → M) u = 0 := by
    intro z hz u hu
    obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ h z).mp hz
    have := hm ⟨(u : G), hu⟩
    rw [hρ _ (h hu), sub_self] at this
    exact this
  have key : ∀ x ∈ LinearMap.ker (resU ρ h), ∀ q, Φ x q ∈ N := by
    intro x hx q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker] at hx
    rw [hΦ, hN, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul,
      ← hpow z z.2]
    exact hvan z hx _ (hn _ (Quotient.out q).2)
  let Ψ : LinearMap.ker (resU ρ h) →ₗ[R] (U ⧸ K → N) :=
    LinearMap.pi (fun q => LinearMap.codRestrict N
      ((LinearMap.proj q : (U ⧸ K → M) →ₗ[R] M) ∘ₗ Φ ∘ₗ (LinearMap.ker (resU ρ h)).subtype)
      (fun x => key x.1 x.2 q))
  have hΨ : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, hxk⟩ hx0
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hq : ∀ q : U ⧸ K, (z : U → M) (Quotient.out q) = 0 := by
      intro q
      have := congrArg (fun f => ((f q : N) : M)) hx0
      exact this
    have hz : (z : U → M) = 0 := by
      funext u
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K u
      have hkU : ((k : U) : G) ∈ U' := Subgroup.mem_subgroupOf.mp k.2
      have hu : u = Quotient.out (QuotientGroup.mk u : U ⧸ K) * (k : U)⁻¹ := by
        rw [hk]; group
      rw [hu, hadd z z.2, hq, hinv z z.2, hvan z hxk _ hkU, neg_zero, add_zero]
      rfl
    have hz' : z = 0 := Subtype.ext hz
    subst hz'
    rfl
  calc Module.length R (LinearMap.ker (resU ρ h)) ≤ Module.length R (U ⧸ K → N) :=
        Module.length_le_of_injective Ψ hΨ
    _ = _ := by
      rw [Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]

private theorem exists_doubleCoset_section {G : Type} [Group G] (U' U : Subgroup G) (h0 : U'.relIndex U ≠ 0) :
    ∃ T : Finset G, (T : Set G) ⊆ U ∧ T.card ≤ U'.relIndex U ∧ U ≤ Subgroup.closure (T : Set G) ⊔ U' := by
  classical
  set K : Subgroup U := U'.subgroupOf U with hK
  have hfi : K.FiniteIndex := ⟨by rw [hK]; exact h0⟩
  haveI : Finite (U ⧸ K) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (U ⧸ K) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : U ⧸ K => ((Quotient.out q : U) : G)), ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨q, rfl⟩ := hx
    exact (Quotient.out q).2
  · refine (Finset.card_image_le).trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Subgroup.relIndex, ← hK, Subgroup.index]
  · intro u hu
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (⟨u, hu⟩ : U)
    have hkU' : ((k : U) : G) ∈ U' := Subgroup.mem_subgroupOf.mp k.2
    have hout : ((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) : U) : G) ∈ Subgroup.closure
        ((Finset.univ.image (fun q : U ⧸ K => ((Quotient.out q : U) : G)) : Finset G) : Set G) := by
      apply Subgroup.subset_closure
      simp
    have heq : u = ((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) : U) : G) * ((k : U) : G)⁻¹ := by
      have := congrArg (fun x : U => (x : G)) hk
      simp only [Subgroup.coe_mul] at this
      rw [this]; group
    rw [heq]
    exact Subgroup.mul_mem_sup hout (U'.inv_mem hkU')

theorem UpperTheory.V.Chr.kerFin :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* Oˣ), ContAction (twist₂ l θ) →
          ∀ (U' U : Subgroup G) (h : U' ≤ U), U' ≤ θ.ker → (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ U') → ∀ n : ℕ, n ≠ 0 → U'.relIndex U ∣ n →
          Module.length O (LinearMap.ker (resU (twist₂ l θ) h)) ≤ ((n * n.factorization l : ℕ) : ℕ∞) * eO l O := by
  intro l _ O _ _ _ _ _ G _ _ _ θ hc U' U h hker hcomm n hn hdiv
  classical
  have h0 : U'.relIndex U ≠ 0 := fun hz => hn (Nat.eq_zero_of_zero_dvd (hz ▸ hdiv))
  set K : Subgroup U := U'.subgroupOf U with hK
  have hfi : K.FiniteIndex := ⟨by rw [hK]; exact h0⟩
  haveI : Finite (U ⧸ K) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (U ⧸ K) := Fintype.ofFinite _
  have hnorm : K.Normal := by
    constructor
    intro k hk g
    rw [hK, Subgroup.mem_subgroupOf] at hk ⊢
    have hcm := hcomm g g.2 k k.2
    have : ((g * k * g⁻¹ : U) : G) = ((g : G) * k * (g : G)⁻¹ * (k : G)⁻¹) * k := by
      push_cast; group
    rw [this]
    exact U'.mul_mem hcm hk
  have hcardK : Nat.card (U ⧸ K) = U'.relIndex U := by
    rw [Subgroup.relIndex, ← hK, Subgroup.index]
  have hpowU : ∀ u ∈ U, u ^ n ∈ U' := by
    intro u hu
    obtain ⟨c, hc'⟩ := hdiv
    have h1 : (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) ^ (U'.relIndex U) = 1 := by
      rw [← hcardK]; exact pow_card_eq_one'
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hK, Subgroup.mem_subgroupOf] at h1
    rw [hc', pow_mul]
    have : ((⟨u, hu⟩ : U) ^ (U'.relIndex U) : U) = (u ^ (U'.relIndex U) : G) := by simp
    rw [this] at h1
    exact U'.pow_mem h1 c
  have hrel_le : U'.relIndex U ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv
  obtain ⟨_, hζ, heOtop, _⟩ := rootVal l O n hn
  have hact : ∀ g m, twist₂ l θ g m = ((θ g : Oˣ) : O) • m := fun g m => by
    rw [twist₂, scalRep_apply]
  by_cases htriv : U ≤ θ.ker
  · have hρ : ∀ u ∈ U, ∀ m, twist₂ l θ u m = m := by
      intro u hu m
      rw [hact, htriv hu, Units.val_one, one_smul]
    have := kerFin_triv (twist₂ l θ) U' U h hρ n hpowU
    refine this.trans ?_
    rw [(qoFacts l O).2.2.2, (rootVal l O n hn).1, Fintype.card_eq_nat_card, hcardK]
    push_cast
    rw [← mul_assoc]
    gcongr
  · obtain ⟨g, hg, hgk⟩ := SetLike.not_le_iff_exists.mp htriv
    set ζ : O := ((θ g : Oˣ) : O) with hζdef
    have hθn : (θ g) ^ n = 1 := by
      rw [← map_pow]
      exact hker (hpowU g hg)
    have hζn : ζ ^ n = 1 := by
      rw [hζdef, ← Units.val_pow_eq_pow_val, hθn, Units.val_one]
    have hζ1 : ζ ≠ 1 := by
      intro h1
      apply hgk
      rw [MonoidHom.mem_ker]
      exact Units.ext h1
    have hsub : H0U (twist₂ l θ) U ≤ ((ζ - 1) • LinearMap.id : QO l O →ₗ[O] QO l O).ker := by
      intro m hm
      rw [H0U, mem_riemannRochSpace_iff_regularAt_everywhere] at hm
      have h1 := hm ⟨g, hg⟩
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hact] at h1
      rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, sub_smul, one_smul, hζdef, h1, sub_self]
    have hbound : Module.length O (H0U (twist₂ l θ) U) ≤ (n.factorization l : ℕ∞) * eO l O := by
      refine (Module.length_le_of_injective (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)).trans ?_
      rw [(qoFacts l O).2.2.2]
      exact hζ ζ hζn hζ1
    obtain ⟨T, hTU, hTcard, hTcl⟩ := exists_doubleCoset_section U' U h0
    have key := kerResAb O G (QO l O) (twist₂ l θ) hc (qoFacts l O).1
      (fun g => ⟨(θ g : O), fun m => hact g m⟩) U' U h hcomm T hTU
      (hTcl.trans (Subgroup.le_topologicalClosure _))
    refine key.trans ?_
    have hle : T.card ≤ n := hTcard.trans hrel_le
    calc (T.card : ℕ∞) * Module.length O (H0U (twist₂ l θ) U) ≤ (n : ℕ∞) * ((n.factorization l : ℕ∞) * eO l O) := by
          gcongr
      _ = ((n * n.factorization l : ℕ) : ℕ∞) * eO l O := by
          push_cast
          rw [mul_assoc]
end

