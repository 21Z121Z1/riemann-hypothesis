import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0002

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.EvIff
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem ev_iff {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n a : ℕ} {Z : Matrix (Fin n) (Fin n) R} :
    Z ∈ Ev A R n a ↔ ∀ i j : Fin n, ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j = 0 := by
  show (∀ i j : Fin n, ((((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j ∈ (⊤ : Submodule A R)) ∧
      (¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j ∈ (⊥ : Submodule A R))) ↔ _
  simp only [Submodule.mem_top, Submodule.mem_bot, implies_true, true_and]

private theorem od_iff {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n a : ℕ} {Z : Matrix (Fin n) (Fin n) R} :
    Z ∈ Od A R n a ↔ ∀ i j : Fin n, (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j = 0 := by
  show (∀ i j : Fin n, ((((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j ∈ (⊥ : Submodule A R)) ∧
      (¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j ∈ (⊤ : Submodule A R))) ↔ _
  simp only [Submodule.mem_top, Submodule.mem_bot, implies_true, and_true]

private theorem sandwich {R : Type} [CommRing R] {n a : ℕ} {P Q Z : Matrix (Fin n) (Fin n) R}
    (hP : ∀ i j : Fin n, ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → P i j = 0)
    (hQ : ∀ i j : Fin n, ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Q i j = 0) (i j : Fin n)
    (hZ : ∀ i' j' : Fin n, (((i : ℕ) < a) ↔ ((i' : ℕ) < a)) → (((j' : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i' j' = 0) :
    (P * Z * Q) i j = 0 := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun m _ => ?_
  by_cases h1 : (((i : ℕ) < a) ↔ ((m : ℕ) < a))
  · by_cases h2 : (((k : ℕ) < a) ↔ ((j : ℕ) < a))
    · rw [hZ m k h1 h2]
      ring
    · rw [hQ k j h2]
      ring
  · rw [hP i m h1]
    ring

theorem UpperTheory.V.Pa.okX :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] (χ : G.Γ →* x.A), AdOk G.frame (fun g => x.ρX X (h.p₀ g)) (fun g => algebraMap x.A X (χ g)) (Ev x.A X n x.a) ∧ AdOk G.frame (fun g => x.ρX X (h.p₀ g)) (fun g => algebraMap x.A X (χ g)) (Od x.A X n x.a) := by
  intro l _ L G G0 h n x X _ _ χ
  classical
  have hblk : ∀ g : G0.frame.G₀, ∀ i j : Fin n, ¬ (((i : ℕ) < x.a) ↔ ((j : ℕ) < x.a)) →
      x.ρX X g i j = 0 := by
    intro g i j hij
    have hz := ev_iff.mp (x.blk g) i j hij
    simp [NP.ρX, Matrix.map_apply, hz]
  have hconj : ∀ g : G.frame.G₀, h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g) := by
    intro g
    apply Subtype.ext
    simp [GFrame.conj, Glob.Hom.p₀, map_mul, map_inv, h.c]
  have key : ∀ (M : Matrix (Fin n) (Fin n) x.A) (E : (x.A)ˣ),
      M = (E : x.A) • (1 : Matrix (Fin n) (Fin n) x.A) →
        ∃ u : Xˣ, M.map (algebraMap x.A X) = (u : X) • (1 : Matrix (Fin n) (Fin n) X) := by
    rintro M E rfl
    refine ⟨Units.map (algebraMap x.A X).toMonoidHom E, ?_⟩
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hform : ∀ g : G.frame.G₀, ∃ u : Xˣ,
      (x.ρX X (h.p₀ g))ᵀ * x.ρX X (h.p₀ (G.frame.conj g)) =
        (u : X) • (1 : Matrix (Fin n) (Fin n) X) := by
    intro g
    have hf := x.form (h.p₀ g)
    simp only [Units.val_one, Matrix.mul_one] at hf
    obtain ⟨u, hu⟩ := key _ _ hf
    refine ⟨u, ?_⟩
    rw [← hu, hconj]
    simp only [NP.ρX, Matrix.transpose_map, Matrix.map_mul]
  refine ⟨⟨?_, ?_, hform, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, hform, ?_, ?_, ?_, ?_⟩⟩
  all_goals try (simp [NP.ρX, Matrix.map_mul]; done)
  · intro g Z hZ
    rw [ev_iff] at hZ ⊢
    intro i j hij
    rw [Matrix.smul_apply, sandwich (hblk _) (hblk _) i j
      (fun i' j' h1 h2 => hZ i' j' (fun h3 => hij (h1.trans (h3.trans h2)))), smul_zero]
  · intro Z hZ
    rw [ev_iff] at hZ ⊢
    intro i j hij
    rw [Matrix.smul_apply, Matrix.transpose_apply, hZ j i (fun h3 => hij h3.symm), smul_zero]
  · intro g Z hZ
    rw [od_iff] at hZ ⊢
    intro i j hij
    rw [Matrix.smul_apply, sandwich (hblk _) (hblk _) i j
      (fun i' j' h1 h2 => hZ i' j' (h1.symm.trans (hij.trans h2.symm))), smul_zero]
  · intro Z hZ
    rw [od_iff] at hZ ⊢
    intro i j hij
    rw [Matrix.smul_apply, Matrix.transpose_apply, hZ j i hij.symm, smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FiltCount
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.filtCount :
    ∀ (Z Y : Type) [AddCommGroup Z] [AddCommGroup Y] (r : ℕ) (f : Fin r → Z →+ Y) (P : Fin r → Set Y), (∀ z, (∀ i, f i z = 0) → z = 0) → (∀ i, (P i).Finite) → (∀ i z, (∀ j, j < i → f j z = 0) → f i z ∈ P i) → Finite Z ∧ Nat.card Z ≤ ∏ i, (P i).ncard := by
  intro Z Y _ _ r
  induction r generalizing Z with
  | zero =>
    intro f P hinj _ _
    have hsub : Subsingleton Z := ⟨fun a b => by
      rw [hinj a (fun i => i.elim0), hinj b (fun i => i.elim0)]⟩
    refine ⟨inferInstance, ?_⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    exact Finite.card_le_one_iff_subsingleton.2 hsub
  | succ r ih =>
    intro f P hinj hP hfilt
    obtain ⟨hKfin, hKcard⟩ := ih (f 0).ker (fun i => (f i.succ).comp (f 0).ker.subtype)
      (fun i => P i.succ)
      (by
        intro z hz
        have h0 : f 0 z.1 = 0 := AddMonoidHom.mem_ker.1 z.2
        apply Subtype.ext
        apply hinj
        intro i
        cases i using Fin.cases with
        | zero => exact h0
        | succ j => exact hz j)
      (fun i => hP i.succ)
      (by
        intro i z hz
        apply hfilt i.succ z.1
        intro j hj
        cases j using Fin.cases with
        | zero => exact AddMonoidHom.mem_ker.1 z.2
        | succ j' => exact hz j' (Fin.succ_lt_succ_iff.1 hj))
    have hrange : ((f 0).range : Set Y) ⊆ P 0 := by
      rintro _ ⟨z, rfl⟩
      exact hfilt 0 z (fun j hj => absurd hj (Fin.not_lt_zero j))
    haveI : Finite (f 0).range := ((hP 0).subset hrange).to_subtype
    have e := QuotientAddGroup.quotientKerEquivRange (f 0)
    haveI : Finite (Z ⧸ (f 0).ker) := Finite.of_equiv _ e.toEquiv.symm
    haveI : Finite Z := Finite.of_addSubgroup_quotient (f 0).ker
    refine ⟨inferInstance, ?_⟩
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (f 0).ker, Nat.card_congr e.toEquiv,
      Fin.prod_univ_succ]
    refine Nat.mul_le_mul ?_ hKcard
    calc Nat.card (f 0).range = ((f 0).range : Set Y).ncard := Nat.card_coe_set_eq _
      _ ≤ (P 0).ncard := Set.ncard_le_ncard hrange (hP 0)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FinAm
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.finAm :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (m g : ℕ), Finite (x.Am m) ∧ Nat.card (x.Am m) = Nat.card x.K ^ m ∧ Finite (DD (x.Am m) g) ∧ (∀ y : x.Am m, l • y = 0) ∧ (∀ y : DD (x.Am m) g, l • y = 0) ∧ (algebraMap x.A (x.Am m) x.t) ^ m = 0 ∧ (algebraMap x.A (DD (x.Am m) g) x.t) ^ m = 0 ∧ (l ≠ 2 → IsUnit (2 : x.A)) ∧ CharP x.K l := by
  intro l _ F n x m g
  obtain ⟨h1, h2, -, -, h5, -⟩ := UpperTheory.V.Pa.am_fin l F n x m g
  have hA : (l : x.A) = 0 := h5
  have e : (l : x.K) = 0 := by
    have := congrArg (PowerSeries.constantCoeff (R := x.K)) hA
    rwa [map_natCast, map_zero] at this
  have hc : CharP x.K l := (CharP.charP_iff_prime_eq_zero (Fact.out)).2 e
  have hAm : (l : x.Am m) = 0 := by
    rw [← map_natCast (algebraMap x.A (x.Am m)), hA, map_zero]
  have hDD : (l : DD (x.Am m) g) = 0 := by
    rw [← map_natCast (DD.C (X := x.Am m) (g := g)), hAm, map_zero]
  haveI := h1
  have ht : (algebraMap x.A (x.Am m) x.t) ^ m = 0 := by
    rw [← map_pow, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  refine ⟨h1, h2, Finite.of_equiv _ DD.equiv.symm, fun y => by rw [nsmul_eq_mul, hAm, zero_mul],
    fun y => by rw [nsmul_eq_mul, hDD, zero_mul], ht, ?_, ?_, hc⟩
  · show (DD.C (algebraMap x.A (x.Am m) x.t)) ^ m = 0
    rw [← map_pow, ht, map_zero]
  · intro hl
    show IsUnit (2 : PowerSeries x.K)
    rw [PowerSeries.isUnit_iff_constantCoeff, map_ofNat]
    apply Ne.isUnit
    intro h2
    have h2' : ((2 : ℕ) : x.K) = 0 := by exact_mod_cast h2
    rw [CharP.cast_eq_zero_iff x.K l] at h2'
    exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2')
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.LocBare
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem cardZ {k D M : Type} [CommRing k] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module k M]
    [Finite M] [TopologicalSpace M] [DiscreteTopology M] (σ : Representation k D M) (hσ : ContAction σ)
    [Finite (H1 σ)] : Finite (Z1 σ) ∧ Nat.card (Z1 σ) * Nat.card (H0 σ) = Nat.card (H1 σ) * Nat.card M := by
  classical
  have hB : B1 σ ≤ Z1 σ := by
    intro f hf
    obtain ⟨m, rfl⟩ := LinearMap.mem_range.mp hf
    show Continuous (d0 σ m) ∧ ∀ g h, d0 σ m (g * h) = d0 σ m g + σ g (d0 σ m h)
    refine ⟨?_, ?_⟩
    · have e : (d0 σ m) = fun g => σ g m - m := funext (fun g => amitsur_d0_apply σ m g)
      rw [e]
      exact (hσ.comp (continuous_id.prodMk continuous_const)).sub continuous_const
    · intro g h
      simp only [amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]
      abel
  have hker : LinearMap.ker (d0 σ) = H0 σ := by
    ext m
    rw [LinearMap.mem_ker, mem_riemannRochSpace_iff_regularAt_everywhere, funext_iff]
    simp only [amitsur_d0_apply, Pi.zero_apply, sub_eq_zero]
  have hM : Nat.card M = Nat.card (B1 σ) * Nat.card (H0 σ) := by
    rw [(LinearMap.ker (d0 σ)).card_eq_card_quotient_mul_card, mul_comm]
    congr 1
    · exact Nat.card_congr (d0 σ).quotKerEquivRange.toEquiv
    · rw [hker]
  have hS : Nat.card (Submodule.comap (Z1 σ).subtype (B1 σ)) = Nat.card (B1 σ) :=
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe hB).toEquiv
  have hZ : Nat.card (Z1 σ) =
      Nat.card (Submodule.comap (Z1 σ).subtype (B1 σ)) * Nat.card (H1 σ) :=
    Submodule.card_eq_card_quotient_mul_card _
  haveI hBfin : Finite (B1 σ) := Finite.of_surjective _ (d0 σ).surjective_rangeRestrict
  have hpos1 : 0 < Nat.card (B1 σ) := Nat.card_pos
  have hpos2 : 0 < Nat.card (H1 σ) := Nat.card_pos
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [hZ, hS]
    positivity
  · rw [hZ, hS, hM]
    ring

private theorem cardDual (k V : Type) [Field k] [AddCommGroup V] [Module k V] [Finite V] :
    Nat.card (Module.Dual k V) = Nat.card V := by
  haveI : Module.Finite k V := Module.Finite.of_finite
  exact Nat.card_congr (Module.Free.chooseBasis k V).toDualEquiv.symm.toEquiv

private theorem cardInv {n : ℕ} [Fact n.Prime] {D M M' : Type} [Group D] [AddCommGroup M] [Module (ZMod n) M]
    [AddCommGroup M'] [Module (ZMod n) M'] [Finite M] [Finite M'] (χ : D →* (ZMod n)ˣ)
    (σ : Representation (ZMod n) D M) (τ : D → M' → M') (b : M →+ M' →+ ZMod n)
    (hl : ∀ x, (∀ y, b x y = 0) → x = 0) (hr : ∀ y, (∀ x, b x y = 0) → y = 0)
    (he : ∀ g x y, b (σ g x) (τ g y) = χ g * b x y) :
    Nat.card (H0 ((twDual χ σ).comp (MonoidHom.id D))) = Nat.card {y : M' // ∀ g, τ g y = y} := by
  classical
  let Φ : M' → Module.Dual (ZMod n) M := fun y => (b.flip y).toZModLinearMap n
  have hΦ : ∀ y x, Φ y x = b x y := fun y x => rfl
  have hsep : ∀ y y' : M', (∀ x, b x y = b x y') → y = y' := by
    intro y y' h
    have := hr (y - y') (fun x => by rw [map_sub, h x, sub_self])
    exact sub_eq_zero.mp this
  have hΦi : Function.Injective Φ := by
    intro y y' h
    exact hsep y y' (fun x => by rw [← hΦ, ← hΦ, h])
  have hΨi : Function.Injective (fun x : M => (b x).toZModLinearMap n) := by
    intro x x' h
    have h' : ∀ y, b x y = b x' y := fun y => LinearMap.congr_fun h y
    have := hl (x - x') (fun y => by rw [map_sub, AddMonoidHom.sub_apply, h' y, sub_self])
    exact sub_eq_zero.mp this
  have c1 := cardDual (ZMod n) M
  have c2 := cardDual (ZMod n) M'
  haveI : Finite (Module.Dual (ZMod n) M) :=
    Nat.finite_of_card_ne_zero (by rw [c1]; exact Nat.card_pos.ne')
  haveI : Finite (Module.Dual (ZMod n) M') :=
    Nat.finite_of_card_ne_zero (by rw [c2]; exact Nat.card_pos.ne')
  have le1 : Nat.card M ≤ Nat.card M' := c2 ▸ Nat.card_le_card_of_injective _ hΨi
  have hΦb : Function.Bijective Φ := hΦi.bijective_of_nat_card_le (by rw [c1]; exact le1)
  have hinv : ∀ g (x : M), σ g (σ g⁻¹ x) = x := by
    intro g x
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have htw : ∀ g y x, ((twDual χ σ) g (Φ y)) x = b x (τ g y) := by
    intro g y x
    have e := he g (σ g⁻¹ x) y
    rw [hinv] at e
    rw [e]
    rfl
  have hmem : ∀ y, Φ y ∈ H0 ((twDual χ σ).comp (MonoidHom.id D)) ↔ ∀ g, τ g y = y := by
    intro y
    show (∀ g, ((twDual χ σ).comp (MonoidHom.id D)) g (Φ y) = Φ y) ↔ _
    constructor
    · intro h g
      apply hsep
      intro x
      rw [← htw g y x]
      exact DFunLike.congr_fun (h g) x
    · intro h g
      apply TDual.ext
      intro x
      show ((twDual χ σ) g (Φ y)) x = Φ y x
      rw [htw, h g]
      rfl
  refine (Nat.card_congr (Equiv.ofBijective
    (fun y : {y : M' // ∀ g, τ g y = y} =>
      (⟨Φ y.1, (hmem y.1).2 y.2⟩ : ↥(H0 ((twDual χ σ).comp (MonoidHom.id D))))) ⟨?_, ?_⟩)).symm
  · intro y y' h
    exact Subtype.ext (hΦi (congrArg Subtype.val h))
  · intro φ
    obtain ⟨y, hy⟩ := hΦb.2 φ.1
    have hy' : Φ y ∈ H0 ((twDual χ σ).comp (MonoidHom.id D)) := by
      rw [hy]
      exact φ.2
    exact ⟨⟨y, (hmem y).1 hy'⟩, Subtype.ext hy⟩

private def zRep (n : ℕ) {R D M : Type} [CommRing R] [Group D] [AddCommGroup M] [Module R M] [Module (ZMod n) M]
    (ρ : Representation R D M) : Representation (ZMod n) D M where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap n
  map_one' := LinearMap.ext fun m => by
    show ρ 1 m = m
    rw [map_one]; rfl
  map_mul' g h := LinearMap.ext fun m => by
    show ρ (g * h) m = ρ g (ρ h m)
    rw [map_mul]; rfl

private theorem cast_toZMod {l : ℕ} [Fact l.Prime] (h : l ^ 1 ∣ l) (x : ℤ_[l]) :
    ZMod.castHom h (ZMod (l ^ 1)) (PadicInt.toZMod x) = PadicInt.toZModPow 1 x := by
  have hinj : Function.Injective (ZMod.castHom h (ZMod (l ^ 1))) := by
    haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact (Fact.out : l.Prime).one_lt⟩
    exact (ZMod.castHom h (ZMod (l ^ 1))).injective
  have hspan : Ideal.span {((l : ℤ_[l])) ^ 1} = RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := by
    rw [pow_one, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]
  have key : (ZMod.castHom h (ZMod (l ^ 1))).comp PadicInt.toZMod = PadicInt.toZModPow 1 := by
    apply ZMod.ringHom_eq_of_ker_eq
    rw [PadicInt.ker_toZModPow, hspan]
    ext y
    simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]
    constructor
    · intro hy
      apply hinj
      rw [hy, map_zero]
    · intro hy
      rw [hy, map_zero]
  exact congrArg (fun f : ℤ_[l] →+* ZMod (l ^ 1) => f x) key

theorem UpperTheory.V.Pa.locBare :
    LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → (((l : ℕ) : 𝓞 F) ∈ v.asIdeal → LocCount (Dec (F := F) A) ((cycZ F Ω l).comp (Dec (F := F) A).subtype) (locDeg v)) ∧ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → LocCount (Dec (F := F) A) ((cycZ F Ω l).comp (Dec (F := F) A).subtype) 0) := by
  intro hF hT hE l _ F Ω _ _ _ _ _ A v hv
  haveI hl1 : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
  have hdvd : l ^ 1 ∣ l := by rw [pow_one]
  have tate : ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M]
      [TopologicalSpace M] [DiscreteTopology M]
      (σ : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M), ReciprocityTheory.Gal.ContAction σ →
      Nat.card ↥(H0 ((twDual ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype) σ).comp
        (MonoidHom.id (Dec (F := F) A)))) ≠ 0 →
      Nat.card (H2 σ) = Nat.card ↥(H0 ((twDual ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype) σ).comp
        (MonoidHom.id (Dec (F := F) A)))) := by
    intro M _ _ _ _ _ σ hσ hne
    haveI := Nat.finite_of_card_ne_zero hne
    obtain ⟨⟨eχ⟩, -, -, -, h20⟩ := hT F Ω l 1 M A σ v one_pos hv hσ
    have hχiso : Nonempty (H2 ((charRep ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype)).comp
        (MonoidHom.id (Dec (F := F) A))) ≃ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)) := by
      rw [MonoidHom.comp_id]
      exact ⟨eχ⟩
    obtain ⟨e2⟩ := hχiso
    have hc1 : Nat.card (H2 σ) = Nat.card (H2 (σ.comp (MonoidHom.id (Dec (F := F) A)))) := by
      rw [MonoidHom.comp_id]
    rw [hc1, Nat.card_congr (Equiv.ofBijective _ h20),
      Nat.card_congr (LinearEquiv.congrRight e2).toEquiv, cardDual]
  have core : ∀ d : ℕ, (∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M]
      [TopologicalSpace M] [DiscreteTopology M]
      (rho : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M), ReciprocityTheory.Gal.ContAction rho →
      Nat.card (H1 rho) = Nat.card (H0 rho) * Nat.card (H2 rho) * Nat.card M ^ d) →
      LocCount (Dec (F := F) A) ((cycZ F Ω l).comp (Dec (F := F) A).subtype) d := by
    intro d hEd R M M' _ _ _ _ _ _ _ ρ ρ' b hLC hD
    have hkill : ∀ x : M, (l ^ 1 : ℕ) • x = 0 := by
      intro x
      apply hD.left
      intro y
      simp [map_nsmul, nsmul_eq_mul]
    have hkill' : ∀ y : M', (l ^ 1 : ℕ) • y = 0 := by
      intro y
      apply hD.right
      intro x
      simp [map_nsmul, nsmul_eq_mul]
    letI : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule hkill
    letI : Module (ZMod (l ^ 1)) M' := AddCommGroup.zmodModule hkill'
    letI : TopologicalSpace M := ⊥
    haveI : DiscreteTopology M := ⟨rfl⟩
    let σ : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M := zRep (l ^ 1) ρ
    have hσ : ReciprocityTheory.Gal.ContAction σ := by
      show Continuous fun p : (Dec (F := F) A) × M => ρ p.1 p.2
      rw [continuous_prod_of_discrete_right]
      intro m
      exact (hLC m).continuous
    obtain ⟨hf0, hf1, hf2, -⟩ := hF F Ω l 1 M A σ v one_pos hv hσ
    haveI := hf0
    haveI := hf1
    haveI := hf2
    have hE1 := hEd M σ hσ
    obtain ⟨hZfin, hZc⟩ := cardZ σ hσ
    let τ : Dec (F := F) A → M' → M' := fun g y => ρ' g y
    let c : ZMod l →+* ZMod (l ^ 1) := ZMod.castHom hdvd (ZMod (l ^ 1))
    have cinj : Function.Injective c := c.injective
    let b' : M →+ M' →+ ZMod (l ^ 1) :=
      AddMonoidHom.mk' (fun x => c.toAddMonoidHom.comp (b x)) (fun x x' => by ext y; simp)
    have hb' : ∀ x y, b' x y = c (b x y) := fun x y => rfl
    have hl' : ∀ x, (∀ y, b' x y = 0) → x = 0 := by
      intro x h
      apply hD.left
      intro y
      apply cinj
      rw [← hb', h y, map_zero]
    have hr' : ∀ y, (∀ x, b' x y = 0) → y = 0 := by
      intro y h
      apply hD.right
      intro x
      apply cinj
      rw [← hb', h x, map_zero]
    have he' : ∀ (g : Dec (F := F) A) (x : M) (y : M'),
        b' (ρ g x) (τ g y) = (((cycMod F Ω l 1).comp (Dec (F := F) A).subtype) g : ZMod (l ^ 1)) * b' x y := by
      intro g x y
      show c (b (ρ g x) (ρ' g y)) = _ * c (b x y)
      rw [hD.equiv, map_mul]
      congr 1
      exact cast_toZMod hdvd _
    have hinvc := cardInv ((cycMod F Ω l 1).comp (Dec (F := F) A).subtype) σ τ b' hl' hr' he'
    haveI : Nonempty {y : M' // ∀ g, τ g y = y} := ⟨⟨0, fun g => map_zero (ρ' g)⟩⟩
    have hpos : Nat.card {y : M' // ∀ g, τ g y = y} ≠ 0 := Nat.card_pos.ne'
    rw [← hinvc] at hpos
    have hinv2 : Nat.card ↥ρ'.invariants = Nat.card {y : M' // ∀ g, τ g y = y} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun y => Iff.rfl))
    have hH2 : Nat.card (H2 σ) = Nat.card ↥ρ'.invariants := by
      rw [tate M σ hσ hpos, hinvc, hinv2]
    have hZeq : ↥(Zl ρ) ≃ ↥(Z1 σ) := Equiv.subtypeEquivRight (fun z => by
      show (IsLocallyConstant z ∧ _) ↔ (Continuous z ∧ _)
      rw [IsLocallyConstant.iff_continuous]
      rfl)
    refine ⟨Finite.of_equiv _ hZeq.symm, ?_⟩
    rw [Nat.card_congr hZeq]
    refine Nat.eq_of_mul_eq_mul_right ?_ (hZc.trans ?_)
    · exact Nat.card_pos_iff.2 ⟨⟨⟨0, Submodule.zero_mem _⟩⟩, hf0⟩
    · rw [hE1, ← hH2, add_comm 1 d, pow_succ (Nat.card M) d]
      ring
  refine ⟨fun hl => core (locDeg v) ?_, fun hl => core 0 ?_⟩
  · intro M _ _ _ _ _ rho hc
    exact (hE F Ω l 1 M A rho v one_pos hv hc).1 hl
  · intro M _ _ _ _ _ rho hc
    rw [pow_zero, mul_one]
    exact (hE F Ω l 1 M A rho v one_pos hv hc).2 hl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.LocCongr
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.locCongr :
    ∀ (l : ℕ) [Fact l.Prime] (D D' : Type) [Group D] [TopologicalSpace D] [Group D'] [TopologicalSpace D'] (α : D ≃ₜ* D') (ε : D →* ℤ_[l]ˣ) (ε' : D' →* ℤ_[l]ˣ) (d : ℕ), (∀ g, ε g = ε' (α g)) → LocCount D' ε' d → LocCount D ε d := by
  intro l _ D D' _ _ _ _ α ε ε' d hε h R M M' _ _ _ _ _ _ _ ρ ρ' b hLC hdual
  let σ : D' →* D := α.symm.toMulEquiv.toMonoidHom
  have hσ : ∀ g, σ g = α.symm g := fun g => rfl
  let ρ2 : Representation R D' M := ρ.comp σ
  let ρ2' : Representation R D' M' := ρ'.comp σ
  have heps : ∀ g : D', epsBar ε (α.symm g) = epsBar ε' g := by
    intro g
    simp only [epsBar, hε, ContinuousMulEquiv.apply_symm_apply]
  have hLC2 : LC ρ2 := fun m => (hLC m).comp_continuous α.symm.continuous
  have hdual2 : IsDualPair ε' ρ2 ρ2' b := by
    refine ⟨hdual.left, hdual.right, fun g x y => ?_⟩
    have := hdual.equiv (α.symm g) x y
    rw [← heps g, ← this]
    rfl
  obtain ⟨hfin, hcard⟩ := h R M M' ρ2 ρ2' b hLC2 hdual2
  let e : Zl ρ ≃ Zl ρ2 :=
    { toFun := fun z => ⟨fun g => z.1 (α.symm g), by
        obtain ⟨hz1, hz2⟩ := z.2
        refine ⟨hz1.comp_continuous α.symm.continuous, fun g k => ?_⟩
        show z.1 (α.symm (g * k)) = z.1 (α.symm g) + ρ (α.symm g) (z.1 (α.symm k))
        rw [map_mul]
        exact hz2 _ _⟩
      invFun := fun z => ⟨fun g => z.1 (α g), by
        obtain ⟨hz1, hz2⟩ := z.2
        refine ⟨hz1.comp_continuous α.continuous, fun g k => ?_⟩
        have := hz2 (α g) (α k)
        rw [← map_mul] at this
        show z.1 (α (g * k)) = z.1 (α g) + ρ g (z.1 (α k))
        rw [this]
        show z.1 (α g) + ρ (α.symm (α g)) (z.1 (α k)) = _
        rw [ContinuousMulEquiv.symm_apply_apply]⟩
      left_inv := fun z => by
        apply Subtype.ext
        funext g
        show z.1 (α.symm (α g)) = z.1 g
        rw [ContinuousMulEquiv.symm_apply_apply]
      right_inv := fun z => by
        apply Subtype.ext
        funext g
        show z.1 (α (α.symm g)) = z.1 g
        rw [ContinuousMulEquiv.apply_symm_apply] }
  have hinv : Nat.card ρ2'.invariants = Nat.card ρ'.invariants := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun v => ?_)
    simp only [Representation.mem_invariants]
    constructor
    · intro hv g
      have := hv (α g)
      simpa [ρ2', hσ] using this
    · intro hv g
      exact hv (α.symm g)
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, hcard, hinv]
end

