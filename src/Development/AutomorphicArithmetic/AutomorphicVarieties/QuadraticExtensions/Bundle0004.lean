import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ZmodToQZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.QzInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0002

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.AbBasic
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem ker_congr (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m n : ℕ) [NeZero m] [NeZero n]
    (h : m = n) : (galChar Ω m).ker = (galChar Ω n).ker := by
  subst h
  rfl

private theorem prim_lemma (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m] :
    ∃ ζ : Ω, IsPrimitiveRoot ζ m := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic m Ω)
    (Polynomial.degree_cyclotomic_pos m Ω (NeZero.pos m)).ne'
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

private theorem galChar_eq_of_apply_primitiveRoot_eq_pow (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m]
    (g : G ℚ Ω) (ζ : Ω) (hζ : IsPrimitiveRoot ζ m) (k : ℕ) (hk : g ζ = ζ ^ k) :
    (galChar Ω m g : ZMod m) = k := by
  have h1 := galChar_spec m g ζ hζ.pow_eq_one
  rw [hk] at h1
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨m, NeZero.pos m, hζ.pow_eq_one⟩
  have h2 := hfin.pow_eq_pow_iff_modEq.mp h1
  rw [← hζ.eq_orderOf] at h2
  rw [← ZMod.natCast_zmod_val (galChar Ω m g : ZMod m)]
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr h2).symm

private theorem galChar_val_cast_eq_galChar_of_dvd (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m N : ℕ) [NeZero m]
    [NeZero N] (h : m ∣ N) (g : G ℚ Ω) :
    (((galChar Ω N g : ZMod N).val : ℕ) : ZMod m) = (galChar Ω m g : ZMod m) := by
  obtain ⟨ζ, hζ⟩ := prim_lemma Ω N
  obtain ⟨d, hd⟩ := h
  have hμ : IsPrimitiveRoot (ζ ^ d) m := hζ.pow (NeZero.pos N) (by rw [hd, mul_comm])
  refine (galChar_eq_of_apply_primitiveRoot_eq_pow Ω m g (ζ ^ d) hμ _ ?_).symm
  rw [map_pow, galChar_spec N g ζ hζ.pow_eq_one, ← pow_mul, ← pow_mul, mul_comm]

private theorem unitsMap_galChar_eq_galChar_of_dvd (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m N : ℕ) [NeZero m]
    [NeZero N] (h : m ∣ N) (g : G ℚ Ω) :
    ZMod.unitsMap h (galChar Ω N g) = galChar Ω m g := by
  ext
  rw [← galChar_val_cast_eq_galChar_of_dvd Ω m N h g, ← ZMod.cast_eq_val]
  rfl

private theorem galChar_surjective (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m] :
    Function.Surjective (galChar Ω m) := by
  intro u
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain ⟨ζ, hζ⟩ := prim_lemma Ω m
  have hcop : Nat.Coprime (u : ZMod m).val m := ZMod.val_coe_unit_coprime u
  have hμ : IsPrimitiveRoot (ζ ^ (u : ZMod m).val) m := hζ.pow_of_coprime _ hcop
  have hmin : minpoly ℚ (ζ ^ (u : ZMod m).val) = minpoly ℚ ζ := by
    have e1 := Polynomial.cyclotomic_eq_minpoly_rat hμ (NeZero.pos m)
    have e2 := Polynomial.cyclotomic_eq_minpoly_rat hζ (NeZero.pos m)
    convert e1.symm.trans e2 <;> exact Subsingleton.elim _ _
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := Ω)).mp hmin
  have hg' : g ζ = ζ ^ (u : ZMod m).val := (AlgEquiv.smul_def g ζ).symm.trans hg
  refine ⟨g, ?_⟩
  ext
  rw [galChar_eq_of_apply_primitiveRoot_eq_pow Ω m g ζ hζ _ hg', ZMod.natCast_zmod_val]

private theorem isOpen_galChar_ker (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) [NeZero m] :
    IsOpen ((galChar Ω m).ker : Set (G ℚ Ω)) := by
  obtain ⟨ζ, hζ⟩ := prim_lemma Ω m
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    IntermediateField.adjoin.finiteDimensional (hζ.isIntegral (NeZero.pos m)).tower_top
  refine Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin ℚ {ζ}).fixingSubgroup) ?_
    (IntermediateField.fixingSubgroup_isOpen _)
  intro g hg
  have hfix : g ζ = ζ ^ 1 := by
    rw [pow_one]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg ζ
      (IntermediateField.subset_adjoin ℚ {ζ} (Set.mem_singleton ζ))
  rw [MonoidHom.mem_ker]
  ext
  rw [galChar_eq_of_apply_primitiveRoot_eq_pow Ω m g ζ hζ 1 hfix]
  simp

theorem UpperTheory.V.Two.abBasic :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω], (∀ A B : AbF, abU Ω (A.sup B) = abU Ω A ⊓ abU Ω B) ∧ (∀ A : AbF, (abU Ω A).index = A.deg ∧ A.deg ≠ 0 ∧ IsOpen (abU Ω A : Set (G ℚ Ω)) ∧ (galChar Ω A.m).ker ≤ abU Ω A) ∧
      (∀ (A : AbF) (N : ℕ) [NeZero N], A.m ∣ N → ∀ g, g ∈ abU Ω A ↔ A.ker (galChar Ω N g : ZMod N).val) ∧ ∀ (m : ℕ) [NeZero m], abU Ω (AbF.cyc m) = (galChar Ω m).ker := by
  intro Ω _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A B
    ext g
    rw [Subgroup.mem_inf]
    show ZMod.unitsMap (dvd_mul_right A.m B.m) (galChar Ω (A.m * B.m) g) ∈ A.H ∧
        ZMod.unitsMap (dvd_mul_left B.m A.m) (galChar Ω (A.m * B.m) g) ∈ B.H ↔
      galChar Ω A.m g ∈ A.H ∧ galChar Ω B.m g ∈ B.H
    rw [unitsMap_galChar_eq_galChar_of_dvd Ω A.m (A.m * B.m) (dvd_mul_right _ _) g,
      unitsMap_galChar_eq_galChar_of_dvd Ω B.m (A.m * B.m) (dvd_mul_left _ _) g]
  · intro A
    refine ⟨Subgroup.index_comap_of_surjective _ (galChar_surjective Ω A.m), Subgroup.index_ne_zero_of_finite, ?_, ?_⟩
    · refine Subgroup.isOpen_mono ?_ (isOpen_galChar_ker Ω A.m)
      intro g hg
      simp [abU, MonoidHom.mem_ker.mp hg, one_mem]
    · intro g hg
      simp [abU, MonoidHom.mem_ker.mp hg, one_mem]
  · intro A N _ hN g
    simp only [abU, Subgroup.mem_comap, AbF.ker]
    rw [galChar_val_cast_eq_galChar_of_dvd Ω A.m N hN g]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨u, hu, hEq⟩
      rwa [← Units.ext hEq]
  · intro m _
    have hm : (AbF.cyc m).m = m := max_eq_left NeZero.one_le
    show Subgroup.comap _ ⊥ = _
    rw [MonoidHom.comap_bot]
    exact ker_congr Ω _ _ hm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.DecIndex
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.decIndex :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p c : ℕ) (A₀ : ValuationSubring Ω), p.Prime → (p % 8 = 3 ∧ c = 2 ∨ p % 16 = 7 ∧ c = 4) → A₀.valuation (p : Ω) < 1 →
      ((cycZ ℚ Ω 2).ker ⊔ Dec (F := ℚ) A₀).index ≠ 0 ∧ ((cycZ ℚ Ω 2).ker ⊔ Dec (F := ℚ) A₀).index ≤ c := by
  intro Ω _ _ _ p c A₀ hp hc hA
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg, hgζ⟩ := decFrob Ω p A₀ hA
  have hodd : Nat.Coprime 2 p := by
    rw [Nat.coprime_two_left, Nat.odd_iff]; omega
  have hu : ((cycZ ℚ Ω 2 g : ℤ_[2]ˣ) : ℤ_[2]) = p := by
    refine PadicInt.ext_of_toZModPow.1 fun n => ?_
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (2 ^ n)
    have h1 : g ζ = ζ ^ (PadicInt.toZModPow n ((cycZ ℚ Ω 2 g : ℤ_[2]ˣ) : ℤ_[2])).val :=
      cyclotomicCharacter.spec 2 (n := n) (MulSemiringAction.toRingAut (G ℚ Ω) Ω g) ζ hζ.pow_eq_one
    have h2 := hgζ (2 ^ n) (Nat.Coprime.pow_left n hodd) ζ hζ.pow_eq_one
    rw [h2] at h1
    have h3 : p ≡ (PadicInt.toZModPow n ((cycZ ℚ Ω 2 g : ℤ_[2]ˣ) : ℤ_[2])).val [MOD 2 ^ n] := by
      have hfin : IsOfFinOrder ζ := hζ.isOfFinOrder (by positivity)
      rwa [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h1
    rw [map_natCast, (ZMod.natCast_eq_natCast_iff _ _ _).2 h3, ZMod.natCast_zmod_val]
  have hcl : IsClosed ((decImage ℚ 2 A₀ : Subgroup ℤ_[2]ˣ) : Set ℤ_[2]ˣ) :=
    ((isClosed_Dec (F := ℚ) A₀).isCompact.image (continuous_cycZ ℚ Ω 2)).isClosed
  obtain ⟨h0, hle⟩ := idxAdic (decImage ℚ 2 A₀) (cycZ ℚ Ω 2 g) p c hcl ⟨g, hg, rfl⟩ hu hc
  have e : (cycZ ℚ Ω 2).ker ⊔ Dec (F := ℚ) A₀ = (decImage ℚ 2 A₀).comap (cycZ ℚ Ω 2) := by
    rw [decImage, Subgroup.comap_map_eq, sup_comm]
  rw [e, Subgroup.index_comap]
  have hrel0 : (decImage ℚ 2 A₀).relIndex ⊤ ≠ 0 := by rwa [Subgroup.relIndex_top_right]
  refine ⟨fun h => hrel0 (Subgroup.relIndex_eq_zero_of_le_right le_top h), ?_⟩
  refine (Subgroup.relIndex_le_of_le_right le_top hrel0).trans ?_
  rwa [Subgroup.relIndex_top_right]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.EmbedQZ
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem embQ_smul (l : ℕ) [Fact l.Prime] {M : Type} [AddCommGroup M] [Module ℤ_[l] M] (z : ℤ_[l]) (x : M)
    (hx : (l : ℤ_[l]) • x = 0) : z • x = z.zmodRepr • x := by
  have hm := PadicInt.sub_zmodRepr_mem z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hm
  obtain ⟨b, hb⟩ := hm
  calc z • x = (z - (z.zmodRepr : ℤ_[l])) • x + (z.zmodRepr : ℤ_[l]) • x := by
        rw [sub_smul, sub_add_cancel]
    _ = z.zmodRepr • x := by
        rw [← hb, mul_smul, hx, smul_zero, zero_add, Nat.cast_smul_eq_nsmul]

private theorem embQ_fl (l : ℕ) [hl : Fact l.Prime] (T : Type) [AddCommGroup T] (r : ℕ) (hTn : ∀ x : T, l • x = 0)
    (hcard : CardLe T (l ^ r)) : ∃ g : T →+ (Fin r → ZMod l), Function.Injective g := by
  obtain ⟨hfin, hc⟩ := hcard
  letI : Module (ZMod l) T := AddCommGroup.zmodModule hTn
  haveI := Fintype.ofFinite T
  haveI hF : Module.Finite (ZMod l) T := Module.Finite.of_finite
  haveI hFr : Module.Free (ZMod l) T := Module.Free.of_divisionRing (ZMod l) T
  set d := Module.finrank (ZMod l) T with hd_def
  have hcardT : Fintype.card T = l ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod l) (V := T), ZMod.card]
  have hd : d ≤ r := by
    have : l ^ d ≤ l ^ r := by rw [← hcardT, ← Nat.card_eq_fintype_card]; exact hc
    exact (Nat.pow_le_pow_iff_right hl.out.one_lt).mp this
  let b := @Module.finBasis (ZMod l) T _ _ _ hFr _ hF
  let E := b.equivFun
  have hadd : ∀ s t : T, E.toFun (s + t) = E.toFun s + E.toFun t := E.map_add'
  have hzero : E.toFun 0 = 0 := by
    have := hadd 0 0
    simp only [add_zero] at this
    exact left_eq_add.mp this
  let g : T →+ (Fin r → ZMod l) :=
    { toFun := fun t i => if h : (i : ℕ) < d then E.toFun t ⟨i, h⟩ else 0
      map_zero' := by
        funext i
        by_cases h : (i : ℕ) < d
        · simp only [h, dif_pos, hzero, Pi.zero_apply]
        · simp only [h, dif_neg, not_false_eq_true, Pi.zero_apply]
      map_add' := by
        intro s t
        funext i
        by_cases h : (i : ℕ) < d
        · simp only [h, dif_pos, hadd, Pi.add_apply]
        · simp only [h, dif_neg, not_false_eq_true, Pi.add_apply, add_zero] }
  refine ⟨g, ?_⟩
  intro s t hst
  have key : E.toFun s = E.toFun t := by
    funext j
    have := congr_fun hst (Fin.castLE hd j)
    simp only [g, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fin.coe_castLE, Fin.eta] at this
    rwa [dif_pos j.isLt, dif_pos j.isLt] at this
  calc s = E.invFun (E.toFun s) := (E.left_inv s).symm
    _ = E.invFun (E.toFun t) := by rw [key]
    _ = t := E.left_inv t

theorem UpperTheory.V.Two.embedQZ :
    ∀ (l : ℕ) [Fact l.Prime] (D : Type) [AddCommGroup D] [Module ℤ_[l] D] (r : ℕ), (∀ x : D, ∃ k : ℕ, (l : ℤ_[l]) ^ k • x = 0) → CardLe (Submodule.torsionBy ℤ_[l] D (l : ℤ_[l])) (l ^ r) →
      ∃ f : D →ₗ[ℤ_[l]] (Fin r → QZ l), Function.Injective f := by
  intro l _ D _ _ r htors hcard
  set Tl := Submodule.torsionBy ℤ_[l] D (l : ℤ_[l]) with hTl
  have hTl' : ∀ t : Tl, (l : ℤ_[l]) • t = 0 := by
    intro t
    have h := t.2
    rw [Submodule.mem_torsionBy_iff] at h
    exact Subtype.ext h
  have hTn : ∀ t : Tl, l • t = 0 := by
    intro t
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]
    exact hTl' t
  obtain ⟨g, hg⟩ := embQ_fl l Tl r hTn hcard
  obtain ⟨ι, hιinj, hιrange, -⟩ := UpperTheory.V.Kum.zmodToQZ l 1
  let e : ZMod l ≃+* ZMod (l ^ 1) := ZMod.ringEquivCongr (pow_one l).symm
  have hιl : ∀ a, (l : ℤ_[l]) • ι a = 0 := by
    intro a
    have := (hιrange (ι a)).mp ⟨a, rfl⟩
    simpa using this
  let ψ : Fin r → Tl →+ QZ l := fun i =>
    ((ι : ZMod (l ^ 1) →+ QZ l).comp e.toAddMonoidHom).comp ((Pi.evalAddMonoidHom (fun _ => ZMod l) i).comp g)
  have hψl : ∀ i t, (l : ℤ_[l]) • ψ i t = 0 := fun i t => hιl _
  let ψL : Fin r → Tl →ₗ[ℤ_[l]] QZ l := fun i =>
    { toFun := ψ i
      map_add' := (ψ i).map_add
      map_smul' := by
        intro z t
        simp only [RingHom.id_apply]
        rw [embQ_smul l z t (hTl' t), map_nsmul, ← embQ_smul l z (ψ i t) (hψl i t)] }
  have hext := fun i => (UpperTheory.V.PropA.qzInj l).out Tl.subtype Subtype.val_injective (ψL i)
  choose y hy using hext
  refine ⟨LinearMap.pi y, ?_⟩
  have hzeroT : ∀ t : Tl, (∀ i, y i t = 0) → t = 0 := by
    intro t ht
    have hgt : g t = 0 := by
      funext i
      have h1 := hy i t
      rw [Submodule.coe_subtype, ht i] at h1
      have h2 : ι (e (g t i)) = ι 0 := by
        rw [map_zero]
        exact h1.symm
      have h3 := hιinj h2
      simpa using h3
    exact hg (by rw [hgt, map_zero])
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hxi : ∀ x : D, LinearMap.pi y x = 0 → ∀ i, y i x = 0 := by
    intro x hx i
    have := congr_fun hx i
    simpa using this
  obtain ⟨k, hk⟩ := htors x
  induction k generalizing x with
  | zero =>
    simpa using hk
  | succ k ih =>
    have hlx : (l : ℤ_[l]) • x = 0 := by
      apply ih ((l : ℤ_[l]) • x)
      · rw [map_smul, hx, smul_zero]
      · rw [← mul_smul, ← pow_succ]
        exact hk
    have hmem : x ∈ Tl := (Submodule.mem_torsionBy_iff _ _).mpr hlx
    have := hzeroT ⟨x, hmem⟩ (hxi x hx)
    simpa using congrArg Subtype.val this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneTwo
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem not_lt_one_of_coprime {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p m : ℕ} (h : p.Coprime m)
    (hp : A.valuation (p : Ω) < 1) : ¬ A.valuation (m : Ω) < 1 := by
  intro hm
  have hz : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => A.valuation_le_one ⟨(z : Ω), intCast_mem A z⟩
  have h1 : ((p : ℤ) * Nat.gcdA p m + (m : ℤ) * Nat.gcdB p m : ℤ) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one h]
    rfl
  have hcast : (p : Ω) * (Nat.gcdA p m : Ω) + (m : Ω) * (Nat.gcdB p m : Ω) = 1 := by
    have := congrArg (Int.cast : ℤ → Ω) h1
    push_cast at this
    exact this
  have ha : A.valuation ((p : Ω) * (Nat.gcdA p m : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hz _)) hp
  have hb : A.valuation ((m : Ω) * (Nat.gcdB p m : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hz _)) hm
  have := lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt ha hb)
  rw [hcast, map_one] at this
  exact lt_irrefl _ this

theorem UpperTheory.V.Two.ineTwo :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : AbF) (p : ℕ) (A : ValuationSubring Ω), p.Coprime (2 * M.m) → A.valuation (p : Ω) < 1 → Ine (F := ℚ) A ≤ cycU 2 (abU Ω (withI M)) := by
  intro Ω _ _ _ M p A hcop hp
  have h2 : p.Coprime 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 M.m) hcop
  have hM : p.Coprime M.m := Nat.Coprime.coprime_dvd_right (dvd_mul_left M.m 2) hcop
  have hW : p.Coprime (withI M).m := by
    show p.Coprime (M.m * max 4 1)
    exact Nat.Coprime.mul_right hM (by simpa using Nat.Coprime.pow_right 2 h2)
  intro g hg
  refine ⟨?_, ?_⟩
  · have := ineChar Ω (withI M).m A (not_lt_one_of_coprime A hW hp) hg
    rw [MonoidHom.mem_ker] at this
    show galChar Ω (withI M).m g ∈ (withI M).H
    rw [this]
    exact Subgroup.one_mem _
  · exact (places ℚ Ω 2 A).2.2.2 (not_lt_one_of_coprime A h2 hp) hg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.InvTwo
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem UpperTheory.V.Two.invTwo_sign (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (U V : Subgroup Γ) (S : Set Γ) (σ : Γ) (hσ : σ ∈ V) (ho : IsOpen (U.subgroupOf V : Set V)) (hi : U.relIndex V = 2)
    (hn : σ ∉ U) (hS : ∀ s ∈ S, s ∈ V → s ∈ U) :
    ∃ ε ∈ CharOff V S 2, ε ⟨σ, hσ⟩ = 1 ∧ ∀ v : V, v.1 ∈ U → ε v = 0 := by
  classical
  set H : Subgroup V := U.subgroupOf V with hH
  have hidx : H.index = 2 := hi
  have hσH : (⟨σ, hσ⟩ : V) ∉ H := by
    rw [hH, Subgroup.mem_subgroupOf]; exact hn
  have hcl : IsClosed (H : Set V) := H.isClosed_of_isOpen ho
  have h10 : (1 : ZMod 2) ≠ 0 := one_ne_zero
  let ε : V → ZMod 2 := fun v => if v ∈ H then 0 else 1
  have hmem : ε ∈ CharOff V S 2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [IsLocallyConstant.iff_isOpen_fiber_apply]
      intro x
      by_cases hx : x ∈ H
      · convert ho using 1
        ext v
        by_cases hv : v ∈ H <;> simp [ε, hv, hx, h10]
      · convert hcl.isOpen_compl using 1
        ext v
        by_cases hv : v ∈ H <;> simp [ε, hv, hx, h10, h10.symm]
    · intro a b
      have hab := Subgroup.mul_mem_iff_of_index_two hidx (a := a) (b := b)
      by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp [ε, ha, hb, hab] <;> decide
    · intro u hu
      have : u ∈ H := by
        rw [hH, Subgroup.mem_subgroupOf]; exact hS _ hu u.2
      simp [ε, this]
  refine ⟨ε, hmem, ?_, ?_⟩
  · simp [ε, hσH]
  · intro v hv
    have : v ∈ H := by
      rw [hH, Subgroup.mem_subgroupOf]; exact hv
    simp [ε, this]

theorem UpperTheory.V.Two.invTwo :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (U V : Subgroup Γ) (S : Set Γ) (σ : Γ) (n : ℕ), U ≤ V → σ ∈ V → IsOpen (U.subgroupOf V : Set V) → U.relIndex V = 2 → σ ∉ U → (∀ s ∈ S, s ∈ V → s ∈ U) →
      CardLe (CharOff V S 2) n → CardLe {φ : CharOff U S 2 // ∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → φ.1 u' = φ.1 u} n := by
  intro Γ _ _ _ U V S σ n hUV hσ ho hi hn hS hQ
  have two : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  classical
  obtain ⟨ε, hε, hεσ, hεU⟩ := UpperTheory.V.Two.invTwo_sign Γ U V S σ hσ ho hi hn hS
  have hσσ : σ * σ ∈ U := by
    have h2 : (U.subgroupOf V).index = 2 := hi
    have := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨σ, hσ⟩ : V)) (b := ⟨σ, hσ⟩)).mpr Iff.rfl
    rwa [Subgroup.mem_subgroupOf] at this
  set P := {φ : CharOff U S 2 // ∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → φ.1 u' = φ.1 u} with hP
  let val : P → ZMod 2 := fun φ => (φ.1 : U → ZMod 2) ⟨σ * σ, hσσ⟩
  obtain ⟨φ0, hφ0⟩ : ∃ φ0 : P, ∀ φ : P, val φ ≠ 0 → val φ0 = 1 := by
    by_cases hex : ∃ φ : P, val φ ≠ 0
    · obtain ⟨φ, hφ⟩ := hex
      exact ⟨φ, fun _ _ => (two _).resolve_left hφ⟩
    · push_neg at hex
      exact ⟨⟨0, fun _ _ _ => rfl⟩, fun φ h => absurd (hex φ) h⟩
  let χ : P → U → ZMod 2 := fun φ =>
    if val φ = 0 then (φ.1 : U → ZMod 2) else (φ.1 : U → ZMod 2) + (φ0.1 : U → ZMod 2)
  have hχmem : ∀ φ, χ φ ∈ CharOff U S 2 := by
    intro φ
    simp only [χ]
    split_ifs
    · exact φ.1.2
    · exact add_mem φ.1.2 φ0.1.2
  have hχinv : ∀ φ, ∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → χ φ u' = χ φ u := by
    intro φ u u' h
    simp only [χ]
    split_ifs
    · exact φ.2 u u' h
    · simp only [Pi.add_apply]
      rw [φ.2 u u' h, φ0.2 u u' h]
  have hχσ : ∀ φ, χ φ ⟨σ * σ, hσσ⟩ = 0 := by
    intro φ
    simp only [χ]
    split_ifs with h
    · exact h
    · have h1 : (φ.1 : U → ZMod 2) ⟨σ * σ, hσσ⟩ = 1 := (two _).resolve_left h
      have h2 : (φ0.1 : U → ZMod 2) ⟨σ * σ, hσσ⟩ = 1 := hφ0 φ h
      simp only [Pi.add_apply]
      rw [h1, h2]
      rfl
  have hext : ∀ φ, ∃ ψ ∈ CharOff V S 2, ψ ⟨σ, hσ⟩ = 0 ∧ ∀ u : U, ψ ⟨u, hUV u.2⟩ = χ φ u :=
    fun φ => UpperTheory.V.Two.extTwo Γ U V S hUV σ hσ hσσ ho hi hn hS (χ φ) (hχmem φ) (hχinv φ) (hχσ φ)
  choose ψ hψmem hψσ hψU using hext
  let f : P → CharOff V S 2 := fun φ =>
    ⟨ψ φ + (if val φ = 0 then 0 else ε), add_mem (hψmem φ) (by split_ifs; exact zero_mem _; exact hε)⟩
  refine UpperTheory.V.Two.CardLe.of_injective hQ f ?_
  intro φ φ' hff
  have hfun : ψ φ + (if val φ = 0 then 0 else ε) = ψ φ' + (if val φ' = 0 then 0 else ε) :=
    congrArg Subtype.val hff
  have hbranch : (val φ = 0 ↔ val φ' = 0) := by
    have := congrFun hfun ⟨σ, hσ⟩
    simp only [Pi.add_apply] at this
    rw [hψσ φ, hψσ φ'] at this
    by_cases h : val φ = 0 <;> by_cases h' : val φ' = 0 <;> simp [h, h', hεσ] at this ⊢
  have hχ : χ φ = χ φ' := by
    funext u
    have := congrFun hfun ⟨u, hUV u.2⟩
    simp only [Pi.add_apply] at this
    rw [hψU φ u, hψU φ' u] at this
    have hu : ε ⟨u, hUV u.2⟩ = 0 := hεU _ u.2
    split_ifs at this <;> simpa [hu] using this
  apply Subtype.ext
  apply Subtype.ext
  simp only [χ] at hχ
  by_cases h : val φ = 0
  · have h' := hbranch.mp h
    simpa [h, h'] using hχ
  · have h' : ¬ val φ' = 0 := fun h' => h (hbranch.mpr h')
    simp only [h, h', if_false] at hχ
    exact add_right_cancel hχ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.KerTwo
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem gen_of_dvd_two {Q : Type} [Group Q] (H : Subgroup Q) (h : H.index ∣ 2) :
    H.Normal ∧ ∃ γ : Q, ∀ u : Q, u ∈ H ∨ u * γ ∈ H := by
  rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h2
  · rw [Subgroup.index_eq_one] at h1
    subst h1
    exact ⟨inferInstance, 1, fun u => Or.inl trivial⟩
  · obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 h2
    exact ⟨Subgroup.normal_of_index_eq_two h2, a, fun u => (ha u).or.symm⟩

theorem UpperTheory.V.Two.kerTwo :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (ρ : Representation ℤ_[2] Γ (QZ 2)) (U' U : Subgroup Γ) (h : U' ≤ U), ContAction ρ → U'.relIndex U ∣ 2 → Module.length ℤ_[2] (LinearMap.ker (resU ρ h)) ≤ 1 := by
  intro Γ _ _ _ ρ U' U h hρ hd
  obtain ⟨hN, γ, hγ⟩ := gen_of_dvd_two (U'.subgroupOf U) hd
  have hcl : U ≤ (Subgroup.zpowers γ.1 ⊔ U').topologicalClosure := by
    refine le_trans (fun u hu => ?_) (Subgroup.le_topologicalClosure _)
    rcases hγ ⟨u, hu⟩ with h1 | h1
    · exact Subgroup.mem_sup_right h1
    · have h2 : u * γ.1 ∈ Subgroup.zpowers γ.1 ⊔ U' := Subgroup.mem_sup_right h1
      exact (Subgroup.mul_mem_cancel_right _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))).1 h2
  have hstab : ∀ m ∈ H0U ρ U', ρ γ m - m ∈ H0U ρ U' := by
    intro m hm
    refine Submodule.sub_mem _ ?_ hm
    intro u
    have h1 : γ⁻¹ * ⟨u.1, h u.2⟩ * γ⁻¹⁻¹ ∈ U'.subgroupOf U :=
      hN.conj_mem _ (by simp [Subgroup.mem_subgroupOf]) _
    have h2 : γ.1⁻¹ * u.1 * γ.1 ∈ U' := by simpa [Subgroup.mem_subgroupOf] using h1
    have h3 : ρ (γ.1⁻¹ * u.1 * γ.1) m = m := hm ⟨_, h2⟩
    show ρ u.1 (ρ γ m) = ρ γ m
    conv_rhs => rw [← h3]
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  let T : H0U ρ U' →ₗ[ℤ_[2]] H0U ρ U' := (ρ γ - LinearMap.id).restrict (p := H0U ρ U') (q := H0U ρ U') hstab
  obtain ⟨φ, hφ⟩ := kerResGen1 _ Γ _ ρ hρ U' U h γ γ.2 hcl T fun _ => rfl
  refine subqLen 2 (H0U ρ U') _ _ (LinearMap.range T).mkQ φ (Submodule.mkQ_surjective _) hφ fun x => ?_
  obtain ⟨k, hk⟩ := hd
  have h1 := kerResSmul _ Γ _ ρ U' U h x.1 x.2
  refine Subtype.ext ?_
  show ((2 : ℕ) : ℤ_[2]) • x.1 = 0
  have h2 : (U'.relIndex U * k) • x.1 = 0 := by rw [mul_comm, mul_smul, h1, smul_zero]
  rw [← hk] at h2
  rw [Nat.cast_smul_eq_nsmul]
  exact h2
end

