import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExponentStrictlyLeastWeight
section
open scoped BigOperators

namespace GlobalTheory

open scoped BigOperators in

theorem _root_.GlobalTheory.exists_exponent_strictly_least_weight :
    ∀ (ρ : ℕ) (S : Set (Fin ρ → ℕ)), S.Nonempty → ∃ m ∈ S, ∀ c : Fin ρ → ℕ,
      (∀ i, ∑ i' ∈ Finset.Iio i, m i' * c i' < c i) →
        ∀ a ∈ S, a ≠ m → ∑ i, m i * c i < ∑ i, a i * c i := by
  intro ρ S hS
  have hwf : WellFounded (Pi.Lex (fun i j : Fin ρ => j < i) (fun {_} (x y : ℕ) => x < y)) :=
    Pi.Lex.wellFounded _ (fun _ => wellFounded_lt)
  refine ⟨hwf.min S hS, hwf.min_mem S hS, ?_⟩
  set m := hwf.min S hS with hm
  intro c hc a ha hne
  have hnl := hwf.not_lt_min S ha
  have hd : (Finset.univ.filter fun i => a i ≠ m i).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    exact ⟨i, by simp [hi]⟩
  set k := (Finset.univ.filter fun i => a i ≠ m i).max' hd with hkdef
  have hk : a k ≠ m k := (Finset.mem_filter.1 (Finset.max'_mem _ hd)).2
  have hgt : ∀ j, k < j → a j = m j := fun j hj => by
    by_contra h
    exact absurd (Finset.le_max' _ j (by simp [h])) (not_le.2 hj)
  have hlt : m k < a k := by
    rcases lt_or_gt_of_ne hk with h | h
    · exact absurd ⟨k, fun j hj => hgt j hj, h⟩ hnl
    · exact h
  have key : ∀ i, m i * c i + (if i = k then c k else 0) ≤
      a i * c i + (if i < k then m i * c i else 0) := by
    intro i
    rcases lt_trichotomy i k with h | h | h
    · simp [h, h.ne]
    · subst h
      simp only [if_true, lt_irrefl, if_false, add_zero]
      nlinarith
    · simp [h.ne', not_lt.2 h.le, hgt i h]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.sum_filter] at hsum
  simp only [Finset.mem_univ, if_true] at hsum
  have hI : Finset.univ.filter (fun i => i < k) = Finset.Iio k := by ext; simp
  rw [hI] at hsum
  have := hc k
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExtendCharacterTrivialOnNormal
section
namespace GlobalTheory

private lemma char_eq_of_same_coset {G M : Type} [Group G] [CommGroup M]
    (Ik H : Subgroup G) (ψ : ↥Ik →* M) (hψ : ∀ s : ↥Ik, (s : G) ∈ H → ψ s = 1)
    (g s t : G) (hs : s ∈ Ik) (ht : t ∈ Ik) (h1 : s⁻¹ * g ∈ H) (h2 : t⁻¹ * g ∈ H) :
    ψ ⟨s, hs⟩ = ψ ⟨t, ht⟩ := by
  have hmem : ((⟨s, hs⟩⁻¹ * ⟨t, ht⟩ : ↥Ik) : G) ∈ H := by
    have h3 : s⁻¹ * t = (s⁻¹ * g) * (t⁻¹ * g)⁻¹ := by group
    have h5 : s⁻¹ * t ∈ H := by
      rw [h3]
      exact H.mul_mem h1 (H.inv_mem h2)
    exact h5
  have h4 := hψ _ hmem
  rw [map_mul, map_inv, inv_mul_eq_one] at h4
  exact h4

theorem exists_extend_character_trivial_on_normal {G M : Type} [Group G] [CommGroup M]
    (I Ik H : Subgroup G) (hH : H.Normal) (hdec : ∀ g ∈ I, ∃ s ∈ Ik, s⁻¹ * g ∈ H)
    (ψ : ↥Ik →* M) (hψ : ∀ s : ↥Ik, (s : G) ∈ H → ψ s = 1) :
    ∃ χ : ↥I →* M, ∀ (g : ↥I) (s : G) (hs : s ∈ Ik), s⁻¹ * (g : G) ∈ H → χ g = ψ ⟨s, hs⟩ := by
  classical
  choose f hfIk hfH using hdec
  have key := char_eq_of_same_coset Ik H ψ hψ
  refine ⟨{ toFun := fun g => ψ ⟨f g g.2, hfIk g g.2⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · show ψ ⟨f _ _, _⟩ = 1
    rw [key _ _ 1 _ Ik.one_mem (hfH _ _) (by simp)]
    exact map_one ψ
  · intro a b
    show ψ ⟨f _ _, _⟩ = ψ ⟨f _ _, _⟩ * ψ ⟨f _ _, _⟩
    have hab : (f a a.2 * f b b.2)⁻¹ * ((a * b : ↥I) : G) ∈ H := by
      show (f a a.2 * f b b.2)⁻¹ * ((a : G) * b) ∈ H
      have hc := hH.conj_mem _ (hfH a a.2) (f b b.2)⁻¹
      have he : (f a a.2 * f b b.2)⁻¹ * ((a : G) * b)
          = ((f b b.2)⁻¹ * ((f a a.2)⁻¹ * a) * (f b b.2)⁻¹⁻¹) * ((f b b.2)⁻¹ * b) := by group
      rw [he]
      exact H.mul_mem hc (hfH b b.2)
    rw [key ((a * b : ↥I) : G) _ (f a a.2 * f b b.2) _ (Ik.mul_mem (hfIk a a.2) (hfIk b b.2))
      (hfH _ _) hab]
    exact map_mul ψ ⟨f a a.2, hfIk a a.2⟩ ⟨f b b.2, hfIk b b.2⟩
  · intro g s hs hsg
    exact key g _ s _ hs (hfH g g.2) hsg

theorem extend_characters_and_generator : ∀ {G F LL : Type} [Group G] [Field F] [Field LL] (I Ik H : Subgroup G), H.Normal → Ik ≤ I → (∀ g ∈ I, ∃ s ∈ Ik, s⁻¹ * g ∈ H) → ∀ (n : ℕ), 0 < n → ∀ (Ψ : ↥(rootsOfUnity n F) →* (↥Ik →* LLˣ)) (Y : Set F), (∀ y ∈ Y, ∃ u : ↥(rootsOfUnity n F), ((u : Fˣ) : F) = y) → (∀ u : ↥(rootsOfUnity n F), ((u : Fˣ) : F) ∈ Y → ∀ s : ↥Ik, (s : G) ∈ H → Ψ u s = 1) → ∃ ch : F → (↥I →* LLˣ), (∀ u : ↥(rootsOfUnity n F), ((u : Fˣ) : F) ∈ Y → ∀ (g : ↥I) (s : G) (hs : s ∈ Ik), s⁻¹ * (g : G) ∈ H → ch ((u : Fˣ) : F) g = Ψ u ⟨s, hs⟩) ∧ ∃ c : ↥I →* LLˣ, (∀ g, c g ^ n = 1) ∧ ∀ y ∈ Y, ∃ k : ℕ, ∀ g, ch y g = c g ^ k := by
  intro G F LL _ _ _ I Ik H hH _ hdec n hn Ψ Y hY hΨ
  classical
  have : NeZero n := ⟨hn.ne'⟩
  let K : Subgroup ↥(rootsOfUnity n F) :=
    { carrier := {u | ∀ s : ↥Ik, (s : G) ∈ H → Ψ u s = 1}
      mul_mem' := fun {a b} ha hb s hs => by
        simp only [Set.mem_ofPred_eq] at ha hb
        rw [map_mul, MonoidHom.mul_apply, ha s hs, hb s hs, mul_one]
      one_mem' := fun s _ => by rw [map_one, MonoidHom.one_apply]
      inv_mem' := fun {a} ha s hs => by
        simp only [Set.mem_ofPred_eq] at ha
        rw [map_inv, MonoidHom.inv_apply, ha s hs, inv_one] }
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := ↥K)
  obtain ⟨c, hc⟩ := exists_extend_character_trivial_on_normal I Ik H hH hdec
    (Ψ (ζ : ↥(rootsOfUnity n F))) (fun s hs => ζ.2 s hs)
  have hk : ∀ y ∈ Y, ∃ k : ℕ, ∀ u : ↥(rootsOfUnity n F), ((u : Fˣ) : F) = y →
      (ζ : ↥(rootsOfUnity n F)) ^ k = u := by
    intro y hy
    obtain ⟨u₀, hu₀⟩ := hY y hy
    have hK : u₀ ∈ K := hΨ u₀ (hu₀ ▸ hy)
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (x := ζ) (y := ⟨u₀, hK⟩)).mpr (hζ _)
    refine ⟨k, fun u hu => ?_⟩
    have hu' : u = u₀ := Subtype.ext (Units.ext (hu.trans hu₀.symm))
    rw [hu']
    have := congrArg (fun v : ↥K => (v : ↥(rootsOfUnity n F))) hk
    simpa using this
  choose! kk hkk using hk
  have hpow : (ζ : ↥(rootsOfUnity n F)) ^ n = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    exact (mem_rootsOfUnity n _).mp (ζ : ↥(rootsOfUnity n F)).2
  refine ⟨fun y => c ^ kk y, ?_, c, ?_, ?_⟩
  · intro u hu g s hs hsg
    show (c ^ kk ((u : Fˣ) : F)) g = Ψ u ⟨s, hs⟩
    rw [MonoidHom.pow_apply, hc g s hs hsg, ← MonoidHom.pow_apply, ← map_pow,
      hkk _ hu u rfl]
  · intro g
    obtain ⟨s, hs, hsg⟩ := hdec g g.2
    rw [hc g s hs hsg, ← MonoidHom.pow_apply, ← map_pow, hpow, map_one, MonoidHom.one_apply]
  · intro y _
    exact ⟨kk y, fun g => MonoidHom.pow_apply c (kk y) g⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteGaloisContainsRootsOfUnits
section
open NumberField Polynomial

namespace GlobalTheory.KummerUnits

theorem exists_finite_galois_mem_of_pow_eq_unit : ∀ (E F Ω : Type) [Field E] [NumberField E] [Field F] [Field Ω] [IsAlgClosed Ω]
    [Algebra E F] [Algebra E Ω] [Algebra F Ω] [IsScalarTower E F Ω] (M : ℕ), 0 < M →
    (∃ ζ : F, IsPrimitiveRoot ζ M) → ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsGalois F L ∧
      ∀ (u : (𝓞 E)ˣ) (w : Ω), w ^ M = algebraMap E Ω ((u : 𝓞 E) : E) → w ∈ L := by
  intro E F Ω _ _ _ _ _ _ _ _ _ M hM ⟨ζ, hζ⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap E F).injective
  obtain ⟨S, hS⟩ := Monoid.fg_def.1 (inferInstance : Monoid.FG (𝓞 E)ˣ)
  let c : (𝓞 E)ˣ → F := fun u => algebraMap E F ((u : 𝓞 E) : E)
  let p : F[X] := ∏ s ∈ S, (X ^ M - C (c s))
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => X_pow_sub_C_ne_zero hM _
  let L := IntermediateField.adjoin F (p.rootSet Ω)
  have hsp : p.IsSplittingField F L :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI := Polynomial.IsSplittingField.finiteDimensional L p
  haveI := Normal.of_isSplittingField (F := F) (E := L) p
  refine ⟨L, inferInstance, ⟨⟩, ?_⟩
  have hζΩ : IsPrimitiveRoot (algebraMap F Ω ζ) M := hζ.map_of_injective (algebraMap F Ω).injective
  have hroot : ∀ ξ : Ω, ξ ^ M = 1 → ξ ∈ L := by
    intro ξ hξ
    obtain ⟨i, -, rfl⟩ := hζΩ.eq_pow_of_pow_eq_one hξ
    exact pow_mem (L.algebraMap_mem ζ) i
  let φ : (𝓞 E)ˣ →* Ω :=
    ((algebraMap E Ω).toMonoidHom.comp (algebraMap (𝓞 E) E).toMonoidHom).comp (Units.coeHom _)
  have hφ : ∀ u, φ u = algebraMap E Ω ((u : 𝓞 E) : E) := fun u => rfl
  have hφc : ∀ u, φ u = algebraMap F Ω (c u) := fun u => IsScalarTower.algebraMap_apply E F Ω _
  have hφ0 : ∀ u, φ u ≠ 0 := fun u => ((Group.isUnit u).map φ).ne_zero
  intro u
  simp only [← hφ]
  have hall : u ∈ Submonoid.closure (S : Set (𝓞 E)ˣ) := by rw [hS]; trivial
  induction hall using Submonoid.closure_induction with
  | mem s hs =>
    intro w hw
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet]
    refine ⟨hp, ?_⟩
    simp only [p, map_prod]
    refine Finset.prod_eq_zero hs ?_
    simp [hw, hφc]
  | one =>
    intro w hw
    exact hroot w (by rw [hw, map_one])
  | mul a b _ _ ha hb =>
    intro w hw
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (φ a) hM
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (φ b) hM
    have hxy : x * y ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · rintro rfl; exact hφ0 a (by rw [← hx, zero_pow hM.ne'])
      · rintro rfl; exact hφ0 b (by rw [← hy, zero_pow hM.ne'])
    rw [← div_mul_cancel₀ w hxy]
    refine mul_mem (hroot _ ?_) (mul_mem (ha x hx) (hb y hy))
    rw [div_pow, mul_pow, hx, hy, hw, map_mul, div_self (mul_ne_zero (hφ0 a) (hφ0 b))]

end GlobalTheory.KummerUnits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinitePlaceValuationCompRingEquiv
section
open NumberField IsDedekindDomain

namespace GlobalTheory.PlaceTransport

theorem eq_of_forall_le_exp_neg {a b : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hb : b ≠ 0) (ha1 : a ≤ 1)
    (hb1 : b ≤ 1) (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, WithZero.exp m = a := ⟨_, WithZero.exp_log ha⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, WithZero.exp k = b := ⟨_, WithZero.exp_log hb⟩
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1 hb1
  have key : ∀ n : ℕ, (m ≤ -(n : ℤ) ↔ k ≤ -(n : ℤ)) := fun n => by
    simpa only [WithZero.exp_le_exp] using h n
  have hkm : k ≤ m := by
    have := (key (-m).toNat).1 (by omega)
    omega
  have hmk : m ≤ k := by
    have := (key (-k).toNat).2 (by omega)
    omega
  rw [le_antisymm hmk hkm]

theorem intValuation_comap_equiv {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    (f : R ≃+* S) (w : HeightOneSpectrum S) (x : R) :
    (HeightOneSpectrum.comap (f : R →+* S) f.surjective w).intValuation x = w.intValuation (f x) := by
  by_cases hx : x = 0
  · simp [hx]
  have hfx : f x ≠ 0 := by simpa using hx
  refine eq_of_forall_le_exp_neg (HeightOneSpectrum.intValuation_ne_zero _ x hx)
    (w.intValuation_ne_zero _ hfx) (HeightOneSpectrum.intValuation_le_one _ x)
    (w.intValuation_le_one _) fun n => ?_
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem]
  change x ∈ (w.asIdeal.comap (f : R →+* S)) ^ n ↔ f x ∈ w.asIdeal ^ n
  have hJ : ∀ J : Ideal S, J.comap (f : R →+* S) = J.map (f.symm : S →+* R) := fun J =>
    (Ideal.map_comap_of_equiv f.symm).symm
  rw [hJ, ← Ideal.map_pow, ← hJ, Ideal.mem_comap]
  rfl

theorem exists_place_valuation_comp_equiv :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L)
      (la : HeightOneSpectrum (𝓞 L)), ∃ la' : HeightOneSpectrum (𝓞 K),
        ∀ y : K, la'.valuation K y = la.valuation L (e y) := by
  intro K L _ _ _ _ e la
  set g : 𝓞 K ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv e
  refine ⟨HeightOneSpectrum.comap (g : 𝓞 K →+* 𝓞 L) g.surjective la, fun y => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
  have hcast : ∀ c : 𝓞 K, e (algebraMap (𝓞 K) K c) = algebraMap (𝓞 L) L (g c) := fun _ => rfl
  rw [map_div₀, map_div₀, map_div₀, hcast, hcast, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_comap_equiv, intValuation_comap_equiv]

end GlobalTheory.PlaceTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGLOfSpanRangeEqLocalRing
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators Matrix

namespace GlobalTheory

theorem exists_det_add_mul_one_sub_mul_ne_zero {k : Type*} [Field k] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) k) :
    ∃ T : Matrix (Fin n) (Fin n) k, (A + T * (1 - B * A)).det ≠ 0 := by
  classical
  set LA := Matrix.toLin' A with hLA
  set K := LinearMap.ker LA
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl (LinearMap.range LA)
  obtain ⟨K', hK'⟩ := Submodule.exists_isCompl K
  have h1 : Module.finrank k (LinearMap.range LA) + Module.finrank k K = Module.finrank k (Fin n → k) :=
    LinearMap.finrank_range_add_finrank_ker LA
  have h2 := Submodule.finrank_add_eq_of_isCompl hU
  have hdim : Module.finrank k K = Module.finrank k U := by omega
  let e : K ≃ₗ[k] U := LinearEquiv.ofFinrankEq K U hdim
  let f : (Fin n → k) →ₗ[k] (Fin n → k) :=
    U.subtype ∘ₗ (e : K →ₗ[k] U) ∘ₗ Submodule.linearProjOfIsCompl K K' hK'
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  have hfw : ∀ w, LinearMap.toMatrix' f *ᵥ w = f w := by
    intro w
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have hfU : ∀ w, f w ∈ U := fun w => (e _).2
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hfw] at hv
  have hAv : A *ᵥ v = 0 := by
    have hr : A *ᵥ v ∈ LinearMap.range LA := ⟨v, by rw [hLA, Matrix.toLin'_apply]⟩
    have hu : A *ᵥ v ∈ U := by
      rw [eq_neg_of_add_eq_zero_left hv]
      exact U.neg_mem (hfU _)
    exact (Submodule.disjoint_def.mp hU.disjoint) _ hr hu
  rw [hAv, zero_add, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hAv,
    Matrix.mulVec_zero, sub_zero] at hv
  have hvK : v ∈ K := by
    show LA v = 0
    rw [hLA, Matrix.toLin'_apply, hAv]
  have hp : Submodule.linearProjOfIsCompl K K' hK' v = ⟨v, hvK⟩ :=
    Submodule.linearProjOfIsCompl_apply_left hK' ⟨v, hvK⟩
  have he : e ⟨v, hvK⟩ = 0 := by
    apply Subtype.ext
    have : f v = 0 := hv
    simpa [f, hp] using this
  have : (⟨v, hvK⟩ : K) = 0 := by simpa using he
  simpa using congrArg Subtype.val this

theorem exists_GL_of_span_range_eq : ∀ (O M : Type) [CommRing O] [IsLocalRing O] [AddCommGroup M]
    [Module O M] (n : ℕ) (x y : Fin n → M),
    Submodule.span O (Set.range x) = Submodule.span O (Set.range y) →
    ∃ h : GL (Fin n) O, ∀ i, y i = ∑ j, (h : Matrix (Fin n) (Fin n) O) i j • x j := by
  intro O M _ _ _ _ n x y hspan
  classical
  have hA : ∀ i, ∃ c : Fin n → O, ∑ j, c j • x j = y i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun O).mp (hspan ▸ Submodule.subset_span ⟨i, rfl⟩)
  have hB : ∀ i, ∃ c : Fin n → O, ∑ j, c j • y j = x i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun O).mp (hspan.symm ▸ Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) O, ∀ i, ∑ j, A i j • x j = y i :=
    ⟨fun i => (hA i).choose, fun i => (hA i).choose_spec⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) O, ∀ i, ∑ j, B i j • y j = x i :=
    ⟨fun i => (hB i).choose, fun i => (hB i).choose_spec⟩
  have hmul : ∀ (P Q : Matrix (Fin n) (Fin n) O) (z : Fin n → M) i,
      ∑ j, (P * Q) i j • z j = ∑ l, P i l • ∑ j, Q l j • z j := by
    intro P Q z i
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  have hC : ∀ l, ∑ j, ((1 : Matrix (Fin n) (Fin n) O) - B * A) l j • x j = 0 := by
    intro l
    simp only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, hmul, hA, hB]
    simp [Matrix.one_apply]
  let r := IsLocalRing.residue O
  obtain ⟨Tb, hTb⟩ := exists_det_add_mul_one_sub_mul_ne_zero (r.mapMatrix A) (r.mapMatrix B)
  obtain ⟨s, hs⟩ : ∃ s : IsLocalRing.ResidueField O → O, ∀ a, r (s a) = a :=
    ⟨Function.surjInv IsLocalRing.residue_surjective, Function.surjInv_eq _⟩
  let T : Matrix (Fin n) (Fin n) O := Tb.map s
  have hT : r.mapMatrix T = Tb := by ext i j; simp [T, hs]
  let H : Matrix (Fin n) (Fin n) O := A + T * (1 - B * A)
  have hdet : IsUnit H.det := by
    have hne : r H.det ≠ 0 := by
      rw [RingHom.map_det]
      simp only [H, map_add, map_mul, map_sub, map_one, hT]
      exact hTb
    by_contra hnu
    exact hne ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
  have hHu : IsUnit H := (Matrix.isUnit_iff_isUnit_det H).mpr hdet
  refine ⟨hHu.unit, fun i => ?_⟩
  rw [IsUnit.unit_spec]
  simp only [H, Matrix.add_apply, add_smul, Finset.sum_add_distrib, hA, hmul, hC, smul_zero,
    Finset.sum_const_zero, add_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeneratorsOfCardHomResidueFieldLe
section
open TensorProduct

namespace GlobalTheory

theorem exists_span_eq_top_of_card_hom_residueField_le
    (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Finite (IsLocalRing.ResidueField Λ)]
    (A : Type) [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] (a : ℕ)
    (h : Nat.card (A →ₗ[Λ] IsLocalRing.ResidueField Λ) ≤
      Nat.card (IsLocalRing.ResidueField Λ) ^ a) :
    ∃ v : Fin a → A, Submodule.span Λ (Set.range v) = ⊤ := by
  classical
  set k := IsLocalRing.ResidueField Λ
  let V := k ⊗[Λ] A
  let d := Module.finrank k V
  let b : Module.Basis (Fin d) k V := Module.finBasis k V

  have hsurj : Function.Surjective (TensorProduct.mk Λ k A 1) :=
    TensorProduct.mk_surjective Λ A k Ideal.Quotient.mk_surjective
  choose f hf using fun i => hsurj (b i)

  have hspan : Submodule.span Λ (Set.range f) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis f b (fun i => hf i)

  let Φ : (V →ₗ[k] k) → (A →ₗ[Λ] k) := fun g =>
    (g.restrictScalars Λ).comp (TensorProduct.mk Λ k A 1)
  have hΦ : Function.Injective Φ := by
    intro g₁ g₂ h
    apply TensorProduct.AlgebraTensorModule.ext
    intro x y
    have h' := LinearMap.congr_fun h y
    simp only [Φ, LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply] at h'
    have e : x ⊗ₜ[Λ] y = x • ((1 : k) ⊗ₜ[Λ] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul, map_smul]
    exact congrArg (x • ·) h'

  have : Finite (A →ₗ[Λ] k) := by
    refine Finite.of_injective (fun g : A →ₗ[Λ] k => fun i => g (f i)) ?_
    intro g₁ g₂ h
    exact LinearMap.ext_on_range hspan (fun i => congr_fun h i)
  have hcard : Nat.card (V →ₗ[k] k) = Nat.card k ^ d := by
    rw [← Nat.card_congr (b.constr k).toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin d),
      Fintype.card_fin]
  have hle : Nat.card k ^ d ≤ Nat.card k ^ a := by
    rw [← hcard]; exact (Nat.card_le_card_of_injective Φ hΦ).trans h
  have hk : 1 < Nat.card k := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hda : d ≤ a := (Nat.pow_le_pow_iff_right hk).mp hle

  refine ⟨fun i => if hi : (i : ℕ) < d then f ⟨i, hi⟩ else 0, ?_⟩
  rw [eq_top_iff, ← hspan]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i, i.2.trans_le hda⟩, by simp⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeightOneMem
section
namespace GlobalTheory.HeightOnePrimeMembership

open NumberField

theorem exists_heightOne_mem (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : Nat.Prime p) :
    ∃ w : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers E),
      (p : RingOfIntegers E) ∈ w.asIdeal := by
  have hnu : ¬ IsUnit (p : RingOfIntegers E) := by
    intro hu
    have h1 : IsUnit (Algebra.norm ℤ (p : RingOfIntegers E)) := hu.map _
    have h2 : (p : RingOfIntegers E) = algebraMap ℤ (RingOfIntegers E) (p : ℤ) := by simp
    rw [h2, Algebra.norm_algebraMap] at h1
    have hpos : Module.finrank ℤ (RingOfIntegers E) ≠ 0 := Module.finrank_pos.ne'
    have h3 : IsUnit (p : ℤ) := (isUnit_pow_iff hpos).1 h1
    exact (Nat.prime_iff_prime_int.1 hp).not_isUnit h3
  have hne : Ideal.span {(p : RingOfIntegers E)} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : (p : RingOfIntegers E) ∈ M := hle (Ideal.mem_span_singleton_self _)
  have hp0 : (p : RingOfIntegers E) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  intro hb
  rw [hb] at hmem
  exact hp0 (by simpa using hmem)

end GlobalTheory.HeightOnePrimeMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentSubMemOfPowSubMem
section
namespace GlobalTheory

private theorem isClosed_submodule_padicInt_finite (l : ℕ) [Fact l.Prime] {N : Type} [AddCommGroup N]
    [Module ℤ_[l] N] [Module.Finite ℤ_[l] N] [TopologicalSpace N] [IsModuleTopology ℤ_[l] N]
    (M : Submodule ℤ_[l] N) : IsClosed (M : Set N) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' ℤ_[l] N
  have hq := IsModuleTopology.isQuotientMap_of_surjective (R := ℤ_[l]) hπ
  rw [← hq.isClosed_preimage]
  obtain ⟨m, φ, hφ⟩ := Module.Finite.exists_fin' ℤ_[l] (M.comap π)
  have hc : Continuous (fun x => ((φ x : M.comap π) : Fin n → ℤ_[l])) :=
    IsModuleTopology.continuous_of_linearMap ((M.comap π).subtype ∘ₗ φ)
  have hrange : Set.range (fun x => ((φ x : M.comap π) : Fin n → ℤ_[l])) = π ⁻¹' (M : Set N) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (φ x).2
    · intro hy
      obtain ⟨x, hx⟩ := hφ ⟨y, hy⟩
      exact ⟨x, by simp [hx]⟩
  rw [← hrange]
  exact (isCompact_range hc).isClosed

theorem exists_idempotent_sub_mem_of_pow_sub_mem (l : ℕ) [Fact l.Prime] {R : Type} [Ring R]
    [Algebra ℤ_[l] R] [Module.Finite ℤ_[l] R] (b : R) :
    ∃ E : R, E * E = E ∧ ∀ (M : Submodule ℤ_[l] R) (c : R),
      (∀ n : ℕ, b ^ (n + 1) - c ∈ M) → E - c ∈ M := by
  letI : TopologicalSpace R := moduleTopology ℤ_[l] R
  haveI : IsModuleTopology ℤ_[l] R := ⟨rfl⟩
  haveI : IsTopologicalRing R := IsModuleTopology.isTopologicalRing ℤ_[l] R
  have hcl : ∀ M : Submodule ℤ_[l] R, IsClosed (M : Set R) := fun M => isClosed_submodule_padicInt_finite l M
  haveI : T2Space R := by
    rw [IsTopologicalAddGroup.t2Space_iff_zero_closed]
    simpa using hcl ⊥
  haveI : CompactSpace R := by
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' ℤ_[l] R
    have hc : Continuous π := IsModuleTopology.continuous_of_linearMap π
    exact ⟨by simpa [hπ.range_eq] using isCompact_range hc⟩
  obtain ⟨E, hES, hE⟩ := exists_idempotent_in_compact_subsemigroup (fun r => continuous_mul_right r)
    (closure (Set.range fun n : ℕ => b ^ (n + 1))) ⟨b ^ (0 + 1), subset_closure ⟨0, rfl⟩⟩
    isClosed_closure.isCompact (by
      intro x hx y hy
      refine map_mem_closure₂ (f := fun x y : R => x * y) continuous_mul hx hy ?_
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      refine ⟨i + j + 1, ?_⟩
      show b ^ (i + j + 1 + 1) = b ^ (i + 1) * b ^ (j + 1)
      rw [← pow_add]
      congr 1
      omega)
  refine ⟨E, hE, fun M c h => ?_⟩
  have hC : IsClosed {x : R | x - c ∈ M} := (hcl M).preimage (continuous_id.sub continuous_const)
  exact closure_minimal (by rintro _ ⟨n, rfl⟩; exact h n) hC hES

end GlobalTheory
end

