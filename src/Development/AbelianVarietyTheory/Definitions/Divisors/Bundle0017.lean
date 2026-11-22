import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0042
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0572

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLevFnPow
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain TensorProduct Formalism.L2.DIV

namespace GlobalTheory.AdeleEv

variable {l : ℕ} [Fact l.Prime]

theorem norm_int_le {E : Type} [Field E] [NumberField E] (τ : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖τ x‖ ≤ 1 := by
  obtain ⟨v, hv⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding E l τ
  by_contra h
  have h0 : (x : E) ≠ 0 := by
    rintro h0
    rw [h0, map_zero, norm_zero] at h
    exact h zero_le_one
  have h1 : ‖τ (x : E)⁻¹‖ < 1 := by
    rw [map_inv₀, norm_inv]
    exact inv_lt_one_of_one_lt₀ (not_le.1 h)
  have h2 := (hv _).2 h1
  rw [map_inv₀] at h2
  have h3 : v.valuation E (x : E) ≤ 1 := v.valuation_le_one x
  have h4 : v.valuation E (x : E) ≠ 0 := (map_ne_zero _).2 h0
  exact absurd ((inv_lt_one₀ (zero_lt_iff.2 h4)).1 h2) (not_lt.2 h3)

theorem exists_adele (F : Type) [Field F] [NumberField F] (τ : F →+* PadicAlgCl l) (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    [FiniteDimensional ℚ_[l] K] (hK : ∀ x, τ x ∈ K) :
    ∃ ev : FiniteAdeleRing (𝓞 F) F →+* PadicAlgCl l, (∀ x, ev (algebraMap F _ x) = τ x) ∧ (∀ a, ev a ∈ K) ∧
      ∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) → ‖ev a‖ ≤ 1 := by
  obtain ⟨v, hv⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding F l τ
  obtain ⟨j, hj, e⟩ := GlobalTheory.exists_continuous_extension_adicCompletion F l τ v hv
  have e' : ∀ x, j (algebraMap F (v.adicCompletion F) x) = τ x := fun x => DFunLike.congr_fun e x
  have hd := HeightOneSpectrum.denseRange_algebraMap F v
  let pr : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
    { toFun := fun a => a v, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
  refine ⟨j.comp pr, fun x => e' x, fun a => ?_, fun a ha => ?_⟩
  · have hc : IsClosed (K : Set (PadicAlgCl l)) := K.toSubmodule.closed_of_finiteDimensional
    exact hd.induction_on (p := fun y => j y ∈ K) (a v) (hc.preimage hj) fun x => by rw [e']; exact hK x
  · have hc : IsClosed {y : v.adicCompletion F | ‖j y‖ ≤ 1} := isClosed_le hj.norm continuous_const
    have ho : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := Valued.isOpen_valuationSubring _
    refine hc.closure_subset_iff.2 ?_ (hd.open_subset_closure_inter ho (ha v))
    rintro _ ⟨h1, x, rfl⟩
    have h2 : v.valuation F x ≤ 1 := by
      have := (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) (K := F) v).1 h1
      rwa [show algebraMap F (v.adicCompletion F) x = (x : v.adicCompletion F) from rfl,
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
    show ‖j _‖ ≤ 1
    rw [e']
    by_contra h
    have h0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero, norm_zero] at h
      exact h zero_le_one
    have h3 : ‖τ x⁻¹‖ < 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_lt_one_of_one_lt₀ (not_le.1 h)
    have h4 := (hv _).2 h3
    rw [map_inv₀] at h4
    exact absurd ((inv_lt_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))).1 h4) (not_lt.2 h2)

theorem exists_ev (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (τ : E →+* PadicAlgCl l)
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (hK : ∀ x, τ x ∈ K) :
    ∃ ev : E ⊗[F] FiniteAdeleRing (𝓞 F) F →+* PadicAlgCl l, (∀ x, ev (x ⊗ₜ[F] 1) = τ x) ∧ (∀ z, ev z ∈ K) ∧
      ∀ z ∈ Formalism.L2.Herm.intAf F E, ‖ev z‖ ≤ 1 := by
  obtain ⟨ev, h1, h2, h3⟩ := exists_adele F (τ.comp (algebraMap F E)) K fun x => hK _
  letI : Algebra F (PadicAlgCl l) := (τ.comp (algebraMap F E)).toAlgebra
  let τ' : E →ₐ[F] PadicAlgCl l := { τ with commutes' := fun _ => rfl }
  let ev' : FiniteAdeleRing (𝓞 F) F →ₐ[F] PadicAlgCl l := { ev with commutes' := h1 }
  let φ := (Algebra.TensorProduct.productMap τ' ev').toRingHom
  have hφ : ∀ x a, φ (x ⊗ₜ[F] a) = τ x * ev a := fun x a => rfl
  refine ⟨φ, fun x => by rw [hφ, map_one, mul_one], fun z => ?_, fun z hz => ?_⟩
  · induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul x a => rw [hφ]; exact mul_mem (hK x) (h2 a)
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  · induction hz using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨⟨_, b, rfl⟩, rfl⟩ | ⟨y, rfl⟩
      · show ‖φ (_ ⊗ₜ[F] _)‖ ≤ 1
        rw [hφ, map_one, mul_one]
        exact norm_int_le τ b
      · show ‖φ (_ ⊗ₜ[F] _)‖ ≤ 1
        rw [hφ, map_one, one_mul]
        exact h3 _ y.2
    | zero => simp
    | one => simp
    | add x y _ _ hx hy => rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
    | neg x _ hx => rwa [map_neg, norm_neg]
    | mul x y _ _ hx hy => rw [map_mul, norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

theorem exists_levFn_pow {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {LL : Type} [CommRing LL]
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (D : LevDat E LL n) : ∃ M : ℕ, 0 < M ∧ ∀ x, levFn β D x ^ M = 1 := by
  classical
  haveI : ∀ PP : Pl E, Finite (kP PP) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot
  have key : ∀ {G : Type} [Group G] (f : G →* LLˣ) (g : G) (M : ℕ), Nat.card G ∣ M → f g ^ M = 1 := by
    rintro G _ f g _ ⟨c, rfl⟩
    rw [← map_pow, pow_mul, pow_card_eq_one', one_pow, map_one]
  have hP : ∀ PP ∈ D.Pg ∪ D.Q, Nat.card (kP PP)ˣ ∣ Nat.card D.P.H * ∏ PP ∈ D.Pg ∪ D.Q, Nat.card (kP PP)ˣ := fun PP h =>
    (Finset.dvd_prod_of_mem (fun PP : Pl E => Nat.card (kP PP)ˣ) h).mul_left _
  refine ⟨Nat.card D.P.H * ∏ PP ∈ D.Pg ∪ D.Q, Nat.card (kP PP)ˣ,
    Nat.mul_pos Nat.card_pos (Finset.prod_pos fun _ _ => Nat.card_pos), fun x => ?_⟩
  have hH : Nat.card D.P.H ∣ Nat.card D.P.H * ∏ PP ∈ D.Pg ∪ D.Q, Nat.card (kP PP)ˣ := dvd_mul_right _ _
  generalize Nat.card D.P.H * ∏ PP ∈ D.Pg ∪ D.Q, Nat.card (kP PP)ˣ = M at hP hH
  unfold levFn
  rw [mul_pow, mul_pow, ← Finset.prod_pow, ← Finset.prod_pow, Finset.prod_eq_one, Finset.prod_eq_one, mul_one, mul_one]
  · unfold ext1
    split_ifs
    · exact key _ _ _ hH
    · exact one_pow _
  · exact fun PP h => key _ _ _ (hP PP (Finset.mem_union_right _ h))
  · intro PP h
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun c _ => key _ _ _ (hP PP (Finset.mem_union_left _ h))

theorem exists_field (L : Type) [Field L] [NumberField L] (e : L →+* PadicAlgCl l) {M : ℕ} (hM : 0 < M) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ (∀ x, e x ∈ K) ∧ ∀ z, z ^ M = 1 → z ∈ K := by
  classical
  obtain ⟨K₁, h₁, h₂⟩ := GlobalTheory.exists_finite_intermediateField_range_le L l e
  let S : Set (PadicAlgCl l) := (Polynomial.nthRoots M (1 : PadicAlgCl l)).toFinset
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  refine ⟨K₁ ⊔ IntermediateField.adjoin ℚ_[l] S, inferInstance, fun x => (le_sup_left : K₁ ≤ _) (h₂ x), fun z hz => ?_⟩
  refine (le_sup_right : IntermediateField.adjoin ℚ_[l] S ≤ _) (IntermediateField.subset_adjoin _ _ ?_)
  exact Finset.mem_coe.2 (Multiset.mem_toFinset.2 ((Polynomial.mem_nthRoots hM).2 hz))

def embInt (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : integralClosure ℤ_[l] K →+* PadicAlgCl l :=
  K.val.toRingHom.comp (integralClosure ℤ_[l] K).val.toRingHom

theorem embInt_injective (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : Function.Injective (embInt K) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem range_embInt (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : Set.range (embInt K) = {x | x ∈ K ∧ ‖x‖ ≤ 1} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1.2, (GlobalTheory.mem_integralClosure_padicInt_iff K _).1 y.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨⟨x, h1⟩, (GlobalTheory.mem_integralClosure_padicInt_iff K _).2 h2⟩, rfl⟩

end GlobalTheory.AdeleEv

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (ValGe_vp IsFieldData IsIntLattice IsClassZetaVals betaBound_vp c_vp cE_vp a0)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt upIdele IsInvIdealOf IsLatOf)
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.LatVal

def Sz (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (r : ℝ) (x : ℂ) : Prop :=
  ∃ h : x ∈ algebraicClosure ℚ ℂ, ‖lam ⟨x, h⟩‖ ≤ (l : ℝ) ^ r

def OneOver {E : Type} [Field E] [NumberField E] (l : ℕ) (y : (Af E)ˣ) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → (y : Af E) w = 1

abbrev LP := ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] (_ : ℕ) (_ : I → E →+* ℂ) (_ : ℕ)
  (_ : ClassGroup (OF E) → ℚ) (_ : Ideal (OF E)) (_ : PeriodPair) (_ : ℕ) (_ : Set E), Prop

def AllLat (P : LP) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I]
    (d : ℕ) (φ : I → E →+* ℂ) (s : ℕ), IsFieldData d φ → 1 ≤ s → ∀ z : ClassGroup (OF E) → ℚ, IsClassZetaVals (2 * s) z →
    ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 → IsIntLattice d Λ → ∀ l : ℕ, l.Prime →
    ∀ Q : Finset (HeightOneSpectrum (OF E)), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → P E I d φ s z 𝔣 Λ l (lattice (condQ 𝔣 Q) y)

def LatIntRam : Prop := AllLat fun E _ _ I _ d φ s z 𝔣 Λ l L => c_vp 𝔣 l ≠ 0 → ∀ (κ : I → ℕ) (S : ℂ → ℂ),
  IsLatSum φ (2 * s) κ L S → ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (beta E d s κ Λ (S 0))

def LatIntUnr : Prop := AllLat fun E _ _ I _ d φ s z 𝔣 Λ l L => c_vp 𝔣 l = 0 → ∀ (κ : I → ℕ) (S : ℂ → ℂ),
  IsLatSum φ (2 * s) κ L S → ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (beta E d s κ Λ (S 0))

open Classical in

def Expansion : Prop := AllLat fun _ _ _ I _ d φ s z 𝔣 Λ l L => c_vp 𝔣 l ≠ 0 →
  ∀ [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
  ∃ a b : I → ℂ, (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ Sz l lam (a0 𝔣 l) (a i / Ω) ∧
      Sz l lam (c_vp 𝔣 l + if l = d then 1 / 2 else 0) (a i * b i * (Real.sqrt d : ℝ) / (2 * Real.pi))⁻¹) ∧
    ∀ (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I), IsDefSum φ (2 * s) L g → (∀ i, u.count i = κ i) →
      Sz l lam ((cE_vp l z : ℝ) + ((2 * s * Fintype.card I : ℕ) : ℝ) * c_vp 𝔣 l +
          ((∑ i, κ i : ℕ) : ℝ) * (c_vp 𝔣 l + 1 + if l = 2 then 1 else 0))
        (iterD u g 0 * ∏ i, ((b i / a i) ^ κ i / (a i ^ (2 * s) * ((κ i).factorial : ℂ))))

section Transport

variable {K : Type} [Field K] [NumberField K]

def TorsTransport (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) : Prop :=
  Ω₀ ≠ 0 ∧ Ω₁ ≠ 0 ∧ (∀ x, g (ι x) = ι x) ∧ IsLatOf ι 1 Λ₀ ∧ (∃ 𝔞, IsInvIdealOf t 𝔞 ∧ IsLatOf ι 𝔞 Λ₁) ∧
    g (Λ₀.g₂ / Ω₀ ^ 4) = Λ₁.g₂ / Ω₁ ^ 4 ∧ g (Λ₀.g₃ / Ω₀ ^ 6) = Λ₁.g₃ / Ω₁ ^ 6 ∧
    ∀ x x' : K, ι x ∉ Λ₀.lattice →
      (∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t : Af K) * algebraMap K (Af K) x' - algebraMap K (Af K) x) v) ≤ 1) →
      g (Λ₀.weierstrassP (ι x) / Ω₀ ^ 2) = Λ₁.weierstrassP (ι x') / Ω₁ ^ 2 ∧
        g (Λ₀.derivWeierstrassP (ι x) / Ω₀ ^ 3) = Λ₁.derivWeierstrassP (ι x') / Ω₁ ^ 3

def IsLatDatum {E : Type} [Field E] [NumberField E] [Algebra K E] {I : Type} [Fintype I] (ι : K →+* ℂ)
    (φ : I → E →+* ℂ) (s : ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) : Prop :=
  UnramFin E ∧ IsCMType φ ∧ (∀ i, (φ i).comp (algebraMap K E) = ι) ∧ 1 ≤ s ∧ IsBaseCond 𝔣 ∧ IsFinSetSplitPlacesCoprimeConductor 𝔣 Q

end Transport

def PeriodEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : K →+* ℂ), Module.finrank ℚ K = 2 →
    ∀ (Λ₀ : PeriodPair) (Ω₀ : ℂ), IsLatOf ι 1 Λ₀ → Ω₀ ≠ 0 →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (j : Ω →+* ℂ)
      (art : Ideles K →* Gab K Ω), j.comp (algebraMap K Ω) = ι → IsGlobalArtin art →
      ∀ (g : ℂ ≃+* ℂ) (σ : Formalism.ConjugateSelfDual.G K Ω) (t : (Af K)ˣ), (∀ x, j (σ x) = g (j x)) → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsSymbol art t σ →
      ∃ (Λ₁ : PeriodPair) (Ω₁ : ℂ), TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁

def LatAlg : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (Λ₀ : PeriodPair) (Ω₀ : ℂ), IsLatOf ι 1 Λ₀ → Ω₀ ^ 12 = latDisc Λ₀ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ)
      (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), IsLatDatum ι φ s 𝔣 Q →
      ∀ (κ : I → ℕ) (y : (Af E)ˣ) (S : ℂ → ℂ), IsLatSum φ (2 * s) κ (lattice (condQ 𝔣 Q) y) S →
        IsAlgebraic ℚ (coordIn E d s κ Ω₀ (S 0))

def LatConj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ)
      (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), IsLatDatum ι φ s 𝔣 Q →
      ∀ (κ κ' : I → ℕ), IsConjWt φ g κ κ' → ∀ (y : (Af E)ˣ) (S S' : ℂ → ℂ),
        IsLatSum φ (2 * s) κ (lattice (condQ 𝔣 Q) y) S →
        IsLatSum φ (2 * s) κ' (lattice (condQ 𝔣 Q) (y * (upIdele K E t)⁻¹)) S' →
        g (coordIn E d s κ Ω₀ (S 0)) = coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * S' 0)

def LatClaims : Prop := LatIntRam ∧ LatIntUnr ∧ Expansion ∧ PeriodEx ∧ LatAlg ∧ LatConj

end GlobalTheory.LatVal
end
end

