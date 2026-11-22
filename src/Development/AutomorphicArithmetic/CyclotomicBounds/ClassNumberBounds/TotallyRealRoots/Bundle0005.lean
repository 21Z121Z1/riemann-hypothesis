import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0002
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0003
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0004

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalAbelian
section
namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem ga_restrict {Ω : Type*} [Monoid Ω] {m M : ℕ} [NeZero m] [NeZero M] (hm : m ∣ M)
    (f : Ω → Ω) (a : (ZMod M)ˣ) (h : ∀ ζ : Ω, ζ ^ M = 1 → f ζ = ζ ^ (a : ZMod M).val)
    (ζ : Ω) (hζ : ζ ^ m = 1) :
    f ζ = ζ ^ ((ZMod.unitsMap hm a : (ZMod m)ˣ) : ZMod m).val := by
  have hM : ζ ^ M = 1 := by
    obtain ⟨c, rfl⟩ := hm
    rw [pow_mul, hζ, one_pow]
  rw [h ζ hM, ZMod.unitsMap_val, ← ZMod.natCast_val, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ]

private theorem ga_red {F : Type*} [Field F] [CharZero F] (g : Gal(AlgebraicClosure F/F)) (n : ℕ)
    (w : (ZMod (l ^ n))ˣ)
    (h : ∀ ζ : AlgebraicClosure F, ζ ^ l ^ n = 1 → g ζ = ζ ^ (w : ZMod (l ^ n)).val) :
    redPow l n (eps l F g) = w := by
  have hen : ∀ i, HasEnoughRootsOfUnity (AlgebraicClosure F) (l ^ i) := fun i => by
    have : NeZero (l ^ i) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have : NeZero ((l ^ i : ℕ) : AlgebraicClosure F) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩
    infer_instance
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure F) (l ^ n)
  have h1 : g ζ = ζ ^ (PadicInt.toZModPow n ((eps l F g : ℤ_[l]ˣ) : ℤ_[l])).val :=
    cyclotomicCharacter.spec l
      (MulSemiringAction.toRingAut Gal(AlgebraicClosure F/F) (AlgebraicClosure F) g) ζ
      hζ.pow_eq_one
  rw [h ζ hζ.pow_eq_one] at h1
  have hfin : IsOfFinOrder ζ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨l ^ n, Nat.pos_of_neZero _, hζ.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf, ← ZMod.natCast_eq_natCast_iff,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h1
  exact Units.ext h1.symm

private theorem ga_embed {K : Type*} [Field K] [NumberField K] (E : IntermediateField ℚ K) :
    ∃ φ : K →+* AlgebraicClosure E, ∀ x : E, φ (x : K) = algebraMap E (AlgebraicClosure E) x := by
  have : Algebra.IsAlgebraic E K := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  let φ : K →ₐ[E] AlgebraicClosure E := IsAlgClosed.lift
  exact ⟨φ.toRingHom, fun x => φ.commutes x⟩

variable {N : ℕ} [NeZero N] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]

theorem galImage_le_levelGroup (E : IntermediateField ℚ K) :
    galImage l E ≤ levelGroup l N (fieldSubgroup N K E) := by
  rintro _ ⟨g, rfl⟩
  obtain ⟨φ, hφ⟩ := ga_embed E
  obtain ⟨a, ha⟩ := exists_class_of_aut (N := N) g.toRingEquiv
  have : NeZero (l ^ N.factorization l) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine mem_levelGroup.2 ⟨a, ?_, ?_⟩
  · refine ⟨(IsCyclotomicExtension.Rat.galEquivZMod N K).symm a, ?_,
      MulEquiv.apply_symm_apply _ _⟩
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
    apply φ.injective
    rw [← aut_comp_embedding φ g.toRingEquiv.toRingHom a ha x]
    have := hφ ⟨x, hx⟩
    change φ x = _ at this
    rw [this]
    exact g.commutes _
  · exact (ga_red g _ _ (ga_restrict (Nat.ordProj_dvd N l) g a ha)).symm

theorem levelGroup_le_galImage (E : IntermediateField ℚ K) :
    levelGroup l N (fieldSubgroup N K E) ≤ galImage l E := by
  intro u hu
  obtain ⟨h, ⟨σ, hσ, rfl⟩, hu⟩ := mem_levelGroup.1 hu
  obtain ⟨φ, hφ⟩ := ga_embed E
  refine mem_of_isClosed isClosed_galImage fun b => ?_
  obtain ⟨a, ha1, ha2⟩ := exists_lift_level _ u hu b
  have : NeZero (l ^ b) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : NeZero (N * l ^ b) := ⟨mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure E) := Algebra.IsAlgebraic.trans ℚ E _
  obtain ⟨g, hg⟩ := exists_aut_pow_roots (AlgebraicClosure E) a
  have hN := ga_restrict (Nat.dvd_mul_right N (l ^ b)) g a hg
  have hb := ga_restrict (Nat.dvd_mul_left (l ^ b) N) g a hg
  rw [ha1] at hN
  rw [ha2] at hb
  have hfix : ∀ x : E, g.toRingEquiv (algebraMap E (AlgebraicClosure E) x) =
      algebraMap E (AlgebraicClosure E) x := fun x => by
    have h1 := aut_comp_embedding φ g.toRingEquiv.toRingHom _ hN (x : K)
    have h2 : (IsCyclotomicExtension.Rat.galEquivZMod N K).symm
        ((IsCyclotomicExtension.Rat.galEquivZMod N K).toMonoidHom σ) = σ :=
      MulEquiv.symm_apply_apply _ _
    rw [h2, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x x.2, hφ] at h1
    exact h1
  let g' : Gal(AlgebraicClosure E/E) := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) hfix
  exact ⟨eps l E g', ⟨g', rfl⟩, ga_red g' b _ hb⟩

theorem galImage_eq_levelGroup (E : IntermediateField ℚ K) :
    galImage l E = levelGroup l N (fieldSubgroup N K E) :=
  le_antisymm (galImage_le_levelGroup E) (levelGroup_le_galImage E)

end KStar.TotallyRealRoots
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalOpen
section
namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

variable {E : Type*} [Field E]

private theorem go_finiteDimensional_adjoinRoots {m : ℕ} (hm : 0 < m) :
    FiniteDimensional E (adjoinRoots E m) := by
  classical
  have hfin : {ζ : AlgebraicClosure E | ζ ^ m = 1}.Finite := by
    refine (Polynomial.nthRoots m (1 : AlgebraicClosure E)).toFinset.finite_toSet.subset ?_
    intro ζ hζ
    simpa [Polynomial.mem_nthRoots hm] using hζ
  have : Finite {ζ : AlgebraicClosure E | ζ ^ m = 1} := hfin.to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

theorem totient_le_finrank_mul [NumberField E] (n : ℕ) :
    (l ^ n).totient ≤ Module.finrank ℚ E * Module.finrank E (adjoinRoots E (l ^ n)) := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have : NeZero (l ^ n) := ⟨hpos.ne'⟩
  have : NeZero ((l ^ n : ℕ) : AlgebraicClosure E) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩
  have := go_finiteDimensional_adjoinRoots (E := E) hpos
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure E) (l ^ n)
  have hmem : ζ ∈ adjoinRoots E (l ^ n) := IntermediateField.subset_adjoin E _ hζ.pow_eq_one
  have hζ' : IsPrimitiveRoot (⟨ζ, hmem⟩ : adjoinRoots E (l ^ n)) (l ^ n) :=
    IsPrimitiveRoot.of_map_of_injective (f := (adjoinRoots E (l ^ n)).val) hζ Subtype.val_injective
  have : FiniteDimensional ℚ (adjoinRoots E (l ^ n)) := Module.Finite.trans E _
  rw [Module.finrank_mul_finrank, ← Polynomial.natDegree_cyclotomic (l ^ n) ℚ,
    Polynomial.cyclotomic_eq_minpoly_rat hζ' hpos]
  exact minpoly.natDegree_le _

theorem finiteIndex_of_index_map_le {U : Subgroup ℤ_[l]ˣ} (hU : IsClosed (U : Set ℤ_[l]ˣ)) {B : ℕ}
    (h : ∀ n, (U.map (redPow l n)).index ≤ B) : U.FiniteIndex := by
  have hl : l.Prime := Fact.out
  have hidx : ∀ n, (U ⊔ princ l n).index = (U.map (redPow l n)).index := by
    intro n
    show (U ⊔ (redPow l n).ker).index = _
    rw [Subgroup.index_map, MonoidHom.range_eq_top.mpr (redPow_surjective n), Subgroup.index_top,
      mul_one]
  have hne : ∀ n, (U ⊔ princ l n).index ≠ 0 := by
    intro n
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
    rw [hidx]
    exact Subgroup.index_ne_zero_of_finite
  have hbdd : BddAbove (Set.range fun n => (U ⊔ princ l n).index) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨n, rfl⟩
    show (U ⊔ princ l n).index ≤ B
    rw [hidx]
    exact h n
  obtain ⟨n₀, hn₀⟩ := Nat.sSup_mem (Set.range_nonempty _) hbdd
  have hmax : ∀ n, (U ⊔ princ l n).index ≤ (U ⊔ princ l n₀).index := by
    intro n
    have hc := le_csSup hbdd ⟨n, rfl⟩
    rw [← hn₀] at hc
    exact hc
  have hstab : ∀ n, n₀ ≤ n → U ⊔ princ l n₀ ≤ U ⊔ princ l n := by
    intro n hn
    have hle : U ⊔ princ l n ≤ U ⊔ princ l n₀ := sup_le_sup_left (princ_anti hn) U
    have hmul := Subgroup.relIndex_mul_index hle
    have h1 : (U ⊔ princ l n).relIndex (U ⊔ princ l n₀) = 1 := by
      have hpos : 0 < (U ⊔ princ l n₀).index := Nat.pos_of_ne_zero (hne n₀)
      have hm : (U ⊔ princ l n).relIndex (U ⊔ princ l n₀) * (U ⊔ princ l n₀).index
          ≤ 1 * (U ⊔ princ l n₀).index := by
        rw [hmul, one_mul]
        exact hmax n
      have h' := Nat.le_of_mul_le_mul_right hm hpos
      have h0 : (U ⊔ princ l n).relIndex (U ⊔ princ l n₀) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hmul
        exact hne n hmul.symm
      omega
    exact Subgroup.relIndex_eq_one.mp h1
  have hsub : U ⊔ princ l n₀ ≤ U := by
    intro x hx
    apply mem_of_isClosed hU
    intro b
    have hxm : x ∈ U ⊔ princ l (max b n₀) := hstab _ (le_max_right _ _) hx
    obtain ⟨u, hu, z, hz, rfl⟩ := Subgroup.mem_sup.mp hxm
    refine ⟨u, hu, ?_⟩
    have hz' : z ∈ princ l b := princ_anti (le_max_left b n₀) hz
    have hz1 : redPow l b z = 1 := MonoidHom.mem_ker.mp hz'
    rw [map_mul, hz1, mul_one]
  have hEq : U ⊔ princ l n₀ = U := le_antisymm hsub le_sup_left
  rw [← hEq]
  exact ⟨hne n₀⟩

theorem isOpen_galImage [NumberField E] : IsOpen (galImage l E : Set ℤ_[l]ˣ) := by
  rw [isOpen_iff_isClosed_finiteIndex]
  refine ⟨isClosed_galImage,
    finiteIndex_of_index_map_le isClosed_galImage (B := Module.finrank ℚ E) fun n => ?_⟩
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hN : 0 < l ^ n := pow_pos hl.pos n
  haveI : FiniteDimensional E (adjoinRoots E (l ^ n)) := go_finiteDimensional_adjoinRoots hN
  have hcard := Subgroup.index_mul_card ((galImage l E).map (redPow l n))
  rw [card_map_redPow_galImage, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at hcard
  have htot := totient_le_finrank_mul (l := l) (E := E) n
  have hpos : 0 < Module.finrank E (adjoinRoots E (l ^ n)) := Module.finrank_pos
  rw [← hcard] at htot
  exact Nat.le_of_mul_le_mul_right htot hpos

end KStar.TotallyRealRoots
end

